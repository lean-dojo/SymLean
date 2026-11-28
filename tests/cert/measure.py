#!/usr/bin/env python3
# Copyright (c) 2026 SymLean Team. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Measurements of the certificate framework (CAS/Cert) on invented data, three sizes per regime.

  one     one shard module that tests all cells of a stored mesh, in the kernel
  many    shard modules of 16,384 cells, eight at a time, in the kernel, and their aggregate;
          then the same shard modules with compiled code (cega.nativeCertificates), as rows
          `native`
  seed    tables recomputed from a seed (CAS.Examples.Cert.Seed), kernel and compiled code
  run     the run over files (CAS.Cert.Run), eight processes, interpreted

Usage, from the repository root after `lake build`:
    lake env python3 tests/cert/measure.py WORK OUT.tsv [REGIME ...] [--sizes N,N,N]

WORK is a scratch directory; the data of a size are deleted when it is measured. Every row of
OUT.tsv is one phase: regime, cells, bytes of data, phase, number of processes, processes at a
time, wall seconds, CPU seconds (user and system, summed over the processes), the largest
resident set of a process in MiB, and bytes of build products where that applies. The modules
are compiled by tests/cert/build.sh outside Lake, each `lean` under /usr/bin/time -v. Only the
standard library is used. This is a measurement and not a test: tests/cert/run.sh is the test.

tests/cert/measure.tsv keeps the rows of one run of all regimes, of 22 November 2026 on 8 cores
of a shared 96-core machine.
"""
import glob
import json
import os
import re
import shutil
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
JOBS = 8
SIZES = {
    'one': [4096, 16384, 65536],
    'many': [65536, 262144, 1048576],
    'seed': [1024, 4096, 16384],
    'run': [1048576, 4194304, 16777216],
}
SEED_UNFOLD = ['CAS.Examples.Cert.Seed.test', 'CAS.Examples.Cert.MeshSpec.cellCond',
               'CAS.Examples.Cert.MeshSpec.meshAt', 'CAS.Examples.Cert.MeshSpec.coefAt',
               'CAS.Examples.Cert.MeshSpec.boundAt', 'CAS.Examples.Cert.MeshSpec.local',
               'CAS.Examples.Cert.Seed.benv', 'CAS.Examples.Cert.Seed.genBenv',
               'CAS.Examples.Cert.Seed.taylor', 'CAS.Examples.Cert.Seed.seedBall',
               'CAS.Examples.Cert.Seed.center', 'CAS.Examples.Cert.Seed.meshBall',
               'CAS.Cert.gridBall']


def sh(cmd, env=None, check=True):
    """Runs a command in the repository root; returns its exit status."""
    full = dict(os.environ)
    full.update(env or {})
    done = subprocess.run(cmd, cwd=ROOT, env=full, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, text=True)
    if check and done.returncode != 0:
        sys.stderr.write(done.stdout[-3000:])
        raise SystemExit('failed: ' + ' '.join(cmd))
    return done.returncode


def times(directory):
    """CPU seconds and largest resident set (MiB) from the reports of /usr/bin/time -v."""
    cpu, rss, count = 0.0, 0, 0
    for path in glob.glob(os.path.join(directory, '*.time')):
        text = open(path).read()
        cpu += float(re.search(r'User time \(seconds\): ([\d.]+)', text).group(1))
        cpu += float(re.search(r'System time \(seconds\): ([\d.]+)', text).group(1))
        rss = max(rss, int(re.search(r'Maximum resident set size \(kbytes\): (\d+)', text).group(1)))
        count += 1
    return cpu, rss // 1024, count


class Bench:
    def __init__(self, work, out):
        self.work, self.out = work, out
        self.src = os.path.join(work, 'src')
        os.makedirs(self.src, exist_ok=True)

    def row(self, regime, cells, data, phase, count, jobs, wall, cpu, rss, products=''):
        line = '\t'.join(str(v) for v in [regime, cells, data, phase, count, jobs,
                                          '%.1f' % wall, '%.1f' % cpu, rss, products])
        with open(self.out, 'a') as f:
            f.write(line + '\n')
        print(line, flush=True)

    def build(self, regime, cells, data, phase, out, jobs, modules, opts=''):
        """Compiles the modules, each under /usr/bin/time -v, and writes one row."""
        tdir = os.path.join(self.work, 'times')
        shutil.rmtree(tdir, ignore_errors=True)
        os.makedirs(tdir)
        start = time.time()
        sh(['bash', 'tests/cert/build.sh', self.src, out, str(jobs)] + modules,
           env={'TIMES': tdir, 'LEAN_OPTS': opts})
        wall = time.time() - start
        cpu, rss, count = times(tdir)
        products = sum(os.path.getsize(p) for m in modules
                       for p in glob.glob(os.path.join(out, m.replace('.', '/') + '.olean*')))
        self.row(regime, cells, data, phase, count, jobs, wall, cpu, rss, products)

    def stored(self, name, cells, part, shard, batch):
        """Writes invented tables and the modules of their certificate; returns the manifest."""
        d = os.path.join(self.src, name)
        sh(['python3', 'scripts/cert_synthetic.py', d, '--cells', str(cells), '--per-part',
            str(part), '--shard', str(shard), '--batch', str(batch), '--prefix', name,
            '--dir', name])
        sh(['lean', '--run', 'scripts/CertStubs.lean', os.path.join(d, 'manifest.json'), self.src])
        return json.load(open(os.path.join(d, 'manifest.json')))

    def data_bytes(self, manifest):
        return sum(p['bytes'] for t in manifest['tables'] for p in t['parts'])

    def kernel(self, regime, cells, part, shard, batch, native):
        """A stored mesh: parts, tables, shards, aggregate; then the shards with compiled code."""
        name = 'M%d' % cells
        m = self.stored(name, cells, part, shard, batch)
        data = self.data_bytes(m)
        out = os.path.join(self.work, 'out')
        parts = max(len(t['parts']) for t in m['tables'])
        shards = (cells + shard - 1) // shard
        self.build(regime, cells, data, 'parts', out, JOBS, ['%s.Part%d' % (name, j) for j in range(parts)])
        self.build(regime, cells, data, 'tables', out, 1, [name + '.Tables'])
        mods = ['%s.Shard%d' % (name, j) for j in range(shards)]
        self.build(regime, cells, data, 'shards-kernel', out, JOBS, mods)
        self.build(regime, cells, data, 'aggregate', out, 1, [name + '.All'])
        if native:
            self.build('native', cells, data, 'shards-compiled', out, JOBS, mods,
                       '-Dweak.cega.nativeCertificates=true')
        shutil.rmtree(os.path.join(self.src, name))
        shutil.rmtree(out)

    def seed(self, cells):
        """Recomputed tables: 2^m cells of CAS.Examples.Cert.Seed, kernel and compiled code."""
        m = cells.bit_length() - 1
        name = 'S%d' % cells
        d = os.path.join(self.src, name)
        os.makedirs(d)
        shard = 2048
        manifest = {'prefix': name, 'dir': name, 'spec': 'CAS.Examples.Cert.Seed',
                    'family': '(CAS.Examples.Cert.Seed.test %d)' % m, 'count': cells,
                    'shard': shard, 'batch': 512, 'unfolding': SEED_UNFOLD, 'tables': []}
        json.dump(manifest, open(os.path.join(d, 'manifest.json'), 'w'))
        sh(['lean', '--run', 'scripts/CertStubs.lean', os.path.join(d, 'manifest.json'), self.src])
        out = os.path.join(self.work, 'out')
        mods = ['%s.Shard%d' % (name, j) for j in range((cells + shard - 1) // shard)]
        self.build('seed', cells, 0, 'shards-kernel', out, JOBS, mods)
        self.build('seed', cells, 0, 'aggregate', out, 1, [name + '.All'])
        self.build('seed', cells, 0, 'shards-compiled', out, JOBS, mods,
                   '-Dweak.cega.nativeCertificates=true')
        shutil.rmtree(d)
        shutil.rmtree(out)

    def run(self, cells):
        """The run over files: eight processes, each a range of shards, interpreted."""
        name = 'R%d' % cells
        part = 65536
        d = os.path.join(self.src, name)
        start = time.time()
        sh(['python3', 'scripts/cert_synthetic.py', d, '--cells', str(cells), '--per-part',
            str(part), '--prefix', name, '--dir', name])
        self.row('run', cells, '', 'write-data', 1, 1, time.time() - start, 0, 0)
        m = json.load(open(os.path.join(d, 'manifest.json')))
        data = self.data_bytes(m)
        sh(['lean', '--run', 'scripts/CertStubs.lean', os.path.join(d, 'manifest.json'),
            self.src, '--run'])
        out = os.path.join(self.work, 'out')
        self.build('run', cells, data, 'manifest', out, 1, [name + '.Manifest'])
        # The digests, by sha256sum.
        listing = os.path.join(self.work, 'sums')
        with open(listing, 'w') as f:
            for t in m['tables']:
                for p in t['parts']:
                    f.write('%s  %s\n' % (p['sha256'], p['file']))
        start = time.time()
        done = subprocess.run(['sha256sum', '--quiet', '-c', listing], cwd=d)
        if done.returncode != 0:
            raise SystemExit('sha256sum: a file differs')
        self.row('run', cells, data, 'sha256sum', 1, 1, time.time() - start, 0, 0)
        # The tests: ranges of shards, eight processes at a time.
        shards = (cells + part - 1) // part
        step = max(1, (shards + JOBS - 1) // JOBS)
        tdir = os.path.join(self.work, 'times')
        shutil.rmtree(tdir, ignore_errors=True)
        os.makedirs(tdir)
        env = dict(os.environ)
        env['LEAN_PATH'] = out + ':' + env['LEAN_PATH']
        main = os.path.join(d, 'RunMain.lean')
        start = time.time()
        procs = []
        for lo in range(0, shards, step):
            hi = min(shards, lo + step)
            procs.append(subprocess.Popen(
                ['/usr/bin/time', '-v', '-o', os.path.join(tdir, 'r%d.time' % lo), 'lean',
                 '--run', main, d, str(lo), str(hi), '--no-digest'],
                cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True))
        for p in procs:
            text = p.communicate()[0]
            if p.returncode != 0 or 'pass' not in text:
                raise SystemExit('run failed: ' + text[-500:])
        wall = time.time() - start
        cpu, rss, count = times(tdir)
        self.row('run', cells, data, 'tests-interpreted', count, JOBS, wall, cpu, rss)
        if cells == SIZES['run'][0]:
            # One shard with the digests computed by the Lean function, interpreted.
            shutil.rmtree(tdir)
            os.makedirs(tdir)
            start = time.time()
            done = subprocess.run(
                ['/usr/bin/time', '-v', '-o', os.path.join(tdir, 'd.time'), 'lean', '--run',
                 main, d, '0', '1'], cwd=ROOT, env=env, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, text=True)
            if done.returncode != 0:
                raise SystemExit('run with digests failed: ' + done.stdout[-500:])
            cpu, rss, count = times(tdir)
            window = sum(p['bytes'] for t in m['tables'] for p in t['parts'][:2])
            self.row('run', part, window, 'one-shard-with-lean-digests', 1, 1,
                     time.time() - start, cpu, rss)
        shutil.rmtree(d)
        shutil.rmtree(out)


def main():
    args = sys.argv[1:]
    sizes = None
    if '--sizes' in args:
        i = args.index('--sizes')
        sizes = [int(v) for v in args[i + 1].split(',')]
        del args[i:i + 2]
    work, out = args[0], args[1]
    regimes = args[2:] or ['one', 'many', 'seed', 'run']
    bench = Bench(work, out)
    for regime in regimes:
        for cells in sizes or SIZES[regime]:
            if regime == 'one':
                bench.kernel('one', cells, cells, cells, 4096, False)
            elif regime == 'many':
                bench.kernel('many', cells, 16384, 16384, 4096, True)
            elif regime == 'seed':
                bench.seed(cells)
            elif regime == 'run':
                bench.run(cells)
            else:
                raise SystemExit('unknown regime ' + regime)


if __name__ == '__main__':
    main()
