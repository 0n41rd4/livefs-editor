# Copyright 2021 Canonical Ltd.
#
# SPDX-License-Identifier: GPL-3.0
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License version 3, as
# published by the Free Software Foundation.
#
# This program is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranties of
# MERCHANTABILITY, SATISFACTORY QUALITY, or FITNESS FOR A PARTICULAR
# PURPOSE.  See the GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see
# <http://www.gnu.org/licenses/>.

import contextlib
import glob
import json
import os
import re
import shlex
import shutil
import subprocess
import tempfile
from debian import deb822


class _MountBase:

    def p(self, *args):
        for a in args:
            if a.startswith('/'):
                raise Exception('no absolute paths here please')
        return os.path.join(self.mountpoint, *args)

    def write(self, path, content):
        with open(self.p(path), 'w') as fp:
            fp.write(content)


class Mountpoint(_MountBase):
    def __init__(self, *, device, mountpoint):
        self.device = device
        self.mountpoint = mountpoint


class OverlayMountpoint(_MountBase):
    def __init__(self, *, lowers, upperdir, mountpoint):
        self.lowers = lowers
        self.upperdir = upperdir
        self.mountpoint = mountpoint

    def unchanged(self):
        return os.listdir(self.upperdir) == []


class EditContext:

    def __init__(self, source_path, *, debug=False):
        self.source_path = source_path
        self.debug = debug
        self._source_overlay = None
        self.dir = tempfile.mkdtemp()
        os.mkdir(self.p('.tmp'))
        self._cache = {}
        self._indent = ''
        self._pre_repack_hooks = []
        self._loops = []
        self._mounts = []
        self._squash_mounts = {}
        self._xorriso_extra_args = []
        self._xorriso_personality = "mkisofs"
        self._preserved_partitions = []
        self._new_partitions = []
        self._final_partitions = []

    def run(self, cmd, check=True, **kw):
        if self.debug:
            msg = []
            for arg in cmd:
                arg = shlex.quote(str(arg))
                arg = arg.replace(self.dir, '${BASE}')
                msg.append(arg)
            msg = ' '.join(msg)
            self.log(f"running with check={check}, kw={kw}\n{self._indent}    {msg}")
        cp = subprocess.run(cmd, check=check, **kw)
        if self.debug:
            msg = f"exit code {cp.returncode}"
            if cp.stdout is not None:
                msg += f" {len(cp.stdout)} bytes of output"
            if cp.stderr is not None:
                msg += f" {len(cp.stderr)} bytes of error"
            self.log(msg)
        return cp

    def run_capture(self, cmd, **kw):
        return self.run(
            cmd, encoding='utf-8', stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            **kw)

    def log(self, msg):
        print(self._indent + msg)

    @contextlib.contextmanager
    def logged(self, msg, done_msg=None):
        self.log(msg)
        self._indent += '  '
        try:
            yield
        finally:
            self._indent = self._indent[:-2]
        if done_msg is not None:
            self.log(done_msg)

    def tmpdir(self):
        d = tempfile.mkdtemp(dir=self.p('.tmp'))
        os.chmod(d, 0o755)
        return d

    def tmpfile(self):
        return tempfile.mktemp(dir=self.p('.tmp'))

    def p(self, *args):
        for a in args:
            if a.startswith('/'):
                raise Exception('no absolute paths here please')
        return os.path.join(self.dir, *args)

    def add_loop(self, file):
        cp = self.run_capture(['losetup', '--show', '--find', '--partscan', file])
        dev = cp.stdout.strip()
        self._loops.append(dev)
        self.run(['udevadm', 'settle'])
        self.log(f'set up loop device {dev} backing {file}')
        return dev

    def add_mount(self, typ, src, mountpoint, *, options=None):
        cmd = ['mount']
        if typ is not None:
            cmd.extend(['-t', typ])
        cmd.append(src)
        if options:
            cmd.extend(['-o', options])
        if mountpoint is None:
            mountpoint = self.tmpdir()
        cmd.append(mountpoint)
        if not os.path.isdir(mountpoint):
            os.makedirs(mountpoint)
        self.run_capture(cmd)
        self._mounts.append(mountpoint)
        return Mountpoint(device=src, mountpoint=mountpoint)

    def umount(self, mountpoint):
        self._mounts.remove(mountpoint)
        self.run(['umount', mountpoint])

    def get_sysfs_mounts(self):
        cp = self.run_capture(
            ['findmnt', '--submounts', '/sys', '--json', '--list'])
        return json.loads(cp.stdout)['filesystems']

    def add_sys_mounts(self, mountpoint):
        mnts = []
        for typ, relpath in [
                ('devtmpfs',   'dev'),
                ('devpts',     'dev/pts'),
                ('proc',       'proc'),
                ]:
            mnts.append(self.add_mount(typ, typ, f'{mountpoint}/{relpath}'))
        ro_targets = []
        for fs in self.get_sysfs_mounts():
            relpath = fs['target'].lstrip('/')
            target = f'{mountpoint}/{relpath}'
            options = fs['options'].split(',')
            if 'ro' in options:
                ro_targets.append(target)
                options.remove('ro')
            options = ','.join(options)
            mnts.append(self.add_mount(
                fs['fstype'], fs['fstype'], target,
                options=options))
        for ro_target in ro_targets:
            self.run(['mount', '-o', 'remount,ro', ro_target])
        resolv_conf = f'{mountpoint}/etc/resolv.conf'
        os.rename(resolv_conf, resolv_conf + '.tmp')
        shutil.copy('/etc/resolv.conf', resolv_conf)

        def _pre_repack():
            for mnt in reversed(mnts):
                self.umount(mnt.p())
            os.rename(resolv_conf + '.tmp', resolv_conf)

        self.add_pre_repack_hook(_pre_repack)

    def add_overlay(self, lowers, mountpoint=None):
        if not isinstance(lowers, list):
            lowers = [lowers]
        upperdir = self.tmpdir()
        workdir = self.tmpdir()

        def lowerdir_for(lower):
            if isinstance(lower, str):
                return lower
            if isinstance(lower, Mountpoint):
                return lower.p()
            if isinstance(lower, OverlayMountpoint):
                return lowerdir_for(lower.lowers + [lower.upperdir])
            if isinstance(lower, list):
                return ':'.join(reversed([lowerdir_for(ll) for ll in lower]))
            raise Exception(f'lowerdir_for({lower!r})')

        lowerdir = lowerdir_for(lowers)
        options = f'lowerdir={lowerdir},upperdir={upperdir},workdir={workdir}'
        return OverlayMountpoint(
            lowers=lowers,
            mountpoint=self.add_mount(
                'overlay', 'overlay', mountpoint, options=options).p(),
            upperdir=upperdir)

    def add_pre_repack_hook(self, hook):
        self._pre_repack_hooks.append(hook)

    def mount_squash(self, name):
        target = self.p('old/' + name)
        squash = self.p(f'old/iso/casper/{name}.squashfs')
        if name in self._squash_mounts:
            return self._squash_mounts[name]
        else:
            self._squash_mounts[name] = m = self.add_mount(
                'squashfs', squash, target, options='ro')
            return m

    def get_arch(self):
        # Is this really the best way??
        with open(self.p('new/iso/.disk/info')) as fp:
            return fp.read().strip().split()[-2]

    def get_suite(self):
        paths = glob.glob(self.p('old/iso/dists/*/Release'))
        with open(paths[0]) as fp:
            release = deb822.Deb822(fp)
        return release['Suite']

    def edit_squashfs(self, name, *, add_sys_mounts=True):
        if name and name.endswith('.squashfs'):
            name = name[:-len('.squashfs')]
        lower = self.mount_squash(name)
        reltarget = f'new/{name}'
        target = self.p(reltarget)
        if os.path.exists(target):
            return target
        overlay = self.add_overlay(lower, target)
        self.log(f"squashfs {name!r} now mounted at {reltarget!r}")
        new_squash = self.p(f'new/iso/casper/{name}.squashfs')

        def _pre_repack():
            try:
                os.unlink(f'{overlay.upperdir}/etc/resolv.conf')
                os.rmdir(f'{overlay.upperdir}/etc')
            except OSError:
                pass
            if overlay.unchanged():
                self.log(f"no changes found in squashfs {name!r}")
                return
            with self.logged(f"repacking squashfs {name!r}"):
                os.unlink(new_squash)
            self.run(['mksquashfs', target, new_squash])

        self.add_pre_repack_hook(_pre_repack)

        if add_sys_mounts:
            self.add_sys_mounts(target)

        return target

    def teardown(self):
        for mount in reversed(self._mounts):
            self.run(['mount', '--make-rprivate', mount])
            try:
                self.run(['umount', '-R', mount])
            except subprocess.CalledProcessError:
                self.run(['umount', '-l', mount])
        shutil.rmtree(self.dir)
        for loop in reversed(self._loops):
            self.run(['losetup', '--detach', loop])

    def find_livefs(self, device):
        for dev in glob.glob(f'{device}*'):
            try:
                try_mount = self.add_mount(None, dev, None, options='ro')
            except subprocess.CalledProcessError:
                continue
            try:
                if os.path.exists(try_mount.p('.disk/info')):
                    return dev
            finally:
                self.umount(try_mount.p())
        else:
            raise Exception("could not find live filesystem")

    def mount_source(self):
        source_loop = self.add_loop(self.source_path)
        live_dev = self.find_livefs(source_loop)
        source_mount = self.add_mount(
            None, live_dev, self.p('old/iso'), options='ro')
        cp = self.run_capture(['findmnt', '-no', 'fstype', source_mount.p()])
        self.source_fstype = cp.stdout.strip()
        self.log(
            f'found live {self.source_fstype} filesystem on {live_dev}')
        self._source_overlay = self.add_overlay(
            source_mount, self.p('new/iso'))

    def get_partition_info(self, sourcepath, partition_number):
        cp = self.run_capture(["sgdisk", "-i", str(partition_number), sourcepath])
        part_info = {}
        for line in cp.stdout.splitlines():
            if "Partition GUID" in line:
                part_info["type"] = line.split(":")[1].strip().split(" ")[0]
            elif "First sector" in line:
                part_info["source_start"] = int(line.split(":")[1].strip().split(" ")[0])
            elif "Last sector" in line:
                part_info["source_end"] = int(line.split(":")[1].strip().split(" ")[0])
            elif "Partition name" in line:
                part_info["name"] = line.split(":")[1].strip().split(" ")[0].strip("'")
        if part_info:
            return part_info
        else:
            raise Exception(f"Could not retrieve partition information for partition {partition_number} on {sourcepath}")

    def write_partition(self, part_info, source_path, destpath):
        start = part_info["source_start"]
        end = part_info["source_end"]
        size = end - start
        dd_command = [
            "dd",
            "if={}".format(source_path),
            "of={}".format(destpath),
            "bs=512",
            "skip={}".format(start),
            "seek={}".format(part_info["dest_start"]),
            "count={}".format(size),
            "conv=notrunc"
        ]
        self.log("running: " + ' '.join(map(shlex.quote, dd_command)))
        self.run(dd_command)

    def process_existing_partitions(self, destpath):
        cp = self.run_capture(["sgdisk", "-p", destpath])
        for line in cp.stdout.splitlines():
            match = re.match(r"\s*(\d+)\s+\d+\s+\d+\s+\S+\s+\S+\s+(\S+)\s+.*", line)
            if match:
                part_num, part_type = match.groups()
                if part_type == "EF00":
                    part_info = self.get_partition_info(destpath, part_num)
                    part_info["number"] = 0
                    part_info["dest_start"] = part_info["source_start"]
                    part_info["dest_end"] = part_info["source_end"]
                    self._final_partitions.append(part_info)
                remove_command = ["sgdisk", destpath]
                remove_command.append("-d {}".format(part_num))
                self.log("running: " + ' '.join(map(shlex.quote, remove_command)))
                self.run(remove_command)

    def add_preserved_partitions(self, destpath):
        for entry in self._preserved_partitions:
            part_info = self.get_partition_info(self.source_path, entry["number"])
            if entry.get("type"):
                part_info["type"] = entry["type"]
            if entry.get("start"):
                part_info["dest_start"] = entry["start"]
            else:
                part_info["dest_start"] = part_info["source_start"]
            if entry.get("name"):
                part_info["name"] = entry["name"]
            part_info["dest_end"] = part_info["dest_start"] + part_info["source_end"] - part_info["source_start"]
            part_info["number"] = entry["as"]
            self.write_partition(part_info, self.source_path, destpath)
            self._final_partitions.append(part_info)

    def add_new_partitions(self, destpath):
        for new_part in self._new_partitions:
            file_size = (os.path.getsize(new_part["sourcepath"]) + 511) // 512
            if new_part["size"] and new_part["size"] < file_size:
                raise Exception(f'Partition size is not big enough to contain {new_part["sourcepath"]}')
            part_size = new_part["size"] if new_part["size"] else file_size
            if new_part["size"]:
                zero_command = [
                    "dd", "if=/dev/null", f'of={destpath}', "bs=512",
                    f'seek={new_part["start"]}', f'count={part_size}', "conv=notrunc"
                ]
                self.log("running: " + ' '.join(map(shlex.quote, zero_command)))
                self.run(zero_command)
            part_info = {
                "number": new_part["number"],
                "type": new_part["type"],
                "source_start": 0,
                "source_end": file_size,
                "dest_start": new_part["start"],
                "dest_end": new_part["start"] + part_size,
                "name": new_part["name"],
            }
            self.write_partition(part_info, new_part["sourcepath"], destpath)
            self._final_partitions.append(part_info)

    def fix_partitions(self, destpath):
        self.add_preserved_partitions(destpath)
        self.add_new_partitions(destpath)
        self.process_existing_partitions(destpath)
        sgdisk_command = ["sgdisk", destpath, "--set-alignment=2"]
        for part_info in self._final_partitions:
            if part_info["number"] != 0:
                sgdisk_command.append("-n {}:{}:{}".format(part_info["number"], part_info["dest_start"], part_info["dest_end"]))
                sgdisk_command.append("-c {}:{}".format(part_info["number"], part_info["name"]))
                sgdisk_command.append("-t {}:{}".format(part_info["number"], part_info["type"]))
        for part_info in self._final_partitions:
            if part_info["number"] == 0:
                sgdisk_command.append("-n 0:{}:{}".format(part_info["dest_start"], part_info["dest_end"]))
                sgdisk_command.append("-c 0:{}".format( part_info["name"]))
                sgdisk_command.append("-t 0:{}".format(part_info["type"]))
        self.log("running: " + ' '.join(map(shlex.quote, sgdisk_command)))
        self.run(sgdisk_command)

    def repack(self, destpath):
        with self.logged("running repack hooks"):
            for hook in reversed(self._pre_repack_hooks):
                hook()
        if self._source_overlay.unchanged():
            self.log("no changes!")
            return False
        if self.source_fstype == 'iso9660':
            self.repack_iso(destpath)
        else:
            self.repack_generic(destpath)
        self.fix_partitions(destpath)
        return True

    def repack_iso(self, destpath):
        cp = self.run_capture([
            'xorriso',
            '-indev', self.source_path,
            '-report_el_torito', 'as_mkisofs' if self._xorriso_personality == "mkisofs" else 'cmd',
        ])
        opts = [arg.replace("imported_iso", "local_fs") for arg in shlex.split(cp.stdout)]
        with self.logged("recreating ISO"):
            if self._xorriso_personality == "mkisofs":
                cmd = ['xorriso', '-as', 'mkisofs'] + opts + \
                    ['-o', destpath, '-V', 'Ubuntu custom', self.p('new/iso')] + \
                    self._xorriso_extra_args
            else:
                cmd = ['xorriso', '-outdev', destpath] + opts + self._xorriso_extra_args + \
                    ['-volid', 'Ubuntu custom', '-fs', '64m', '-map', self.p('new/iso'), '/']

            self.log("running: " + ' '.join(map(shlex.quote, cmd)))
            self.run(cmd)

    def repack_generic(self, destpath):
        with self.logged(f"copying {self.source_path} to {destpath}"):
            self.run(['cp', self.source_path, destpath])
        destloop = self.add_loop(destpath)
        dest_dev = self.find_livefs(destloop)
        dest_mount = self.add_mount(None, dest_dev, None)
        with self.logged("copying live filesystem"):
            self.run(
                ['rsync', '-axXvHAS', self.p('new/iso/'), '.'],
                cwd=dest_mount.p())
