#!/usr/bin/env python3
# Copyright (c) 2026 SymLean Team. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Synthetic data for the certificate framework (CAS/Cert): a piecewise cubic on a stored mesh.

Writes three tables in parts, as hexadecimal text, and a manifest for scripts/CertStubs.lean.

  mesh   N + 1 mesh points x_0 < ... < x_N of [0, 1], not equally spaced, each rounded to the
         grid; they stay apart for N below 2^39
  coef   4 N numbers: on cell k the cubic c_0 + c_1 h + c_2 h^2 + c_3 h^3 in h = x - x_k,
         the Taylor polynomial at x_k of the global cubic p with each coefficient rounded to
         the grid, so the cubics of two cells need not be pieces of one cubic
  bound  N numbers: an upper bound of the cubic of cell k on the cell

Every entry is a 64-bit two's complement integer at the scale 2^-40, written as 16 hexadecimal
digits on a line of its own, entry 0 first. The data are invented: the cubic p and the mesh are
fixed formulas, and the bounds are computed with exact integer arithmetic so that the check of
CAS.Examples.Cert.MeshSpec passes. `--break K` spoils the bound of cell K, so that the check
must fail there.

Usage: cert_synthetic.py OUTDIR --cells N --per-part S --prefix M --dir D [--spec SPEC]
       [--shard C] [--batch B] [--halo H] [--block Q] [--break K]
S must be a multiple of the block length Q, the number of entries in one literal of a build
(by default 4096, or S if that is smaller). M is the module prefix and D the directory of the
modules that scripts/CertStubs.lean writes; the library embeds no data file, so they name a
scratch tree.
Only the standard library is used.
"""
import argparse
import hashlib
import json
import os

SCALE = 40
WIDTH = 64
ONE = 1 << SCALE

# The global cubic p(x) = (3 - 10 x + 28 x^2 - 18 x^3) / 8.
A8 = [3, -10, 28, -18]


def rdiv(num, den):
    """The integer nearest to num / den, for den > 0 (halves go up)."""
    return (2 * num + den) // (2 * den)


def mesh_point(k, n):
    """Mesh point k of n cells: the grid value of t + t (1 - t) / 4 at t = k / n."""
    return rdiv((4 * n * k + k * (n - k)) * ONE, 4 * n * n)


def taylor(x):
    """Taylor coefficients of p at the grid point x, each rounded to the grid."""
    a0, a1, a2, a3 = A8
    c0 = rdiv(a0 * ONE**3 + a1 * x * ONE**2 + a2 * x * x * ONE + a3 * x**3, 8 * ONE**2)
    c1 = rdiv(a1 * ONE**2 + 2 * a2 * x * ONE + 3 * a3 * x * x, 8 * ONE)
    c2 = rdiv(a2 * ONE + 3 * a3 * x, 8)
    c3 = rdiv(a3 * ONE, 8)
    return [c0, c1, c2, c3]


def cell_bound(c, w):
    """An upper bound of c0 + c1 h + c2 h^2 + c3 h^3 for 0 <= h <= w (grid integers in, grid
    integer out): the value at h = 0 plus the largest possible increase, plus a margin that
    covers the rounding of a check at 96 bits."""
    rise = abs(c[1]) * w * ONE**2 + abs(c[2]) * w * w * ONE + abs(c[3]) * w**3
    return c[0] + rdiv(rise, ONE**3) + 4


def hex_entry(v):
    return format(v & (2**WIDTH - 1), '0%dx' % (WIDTH // 4))


def write_parts(outdir, name, values, per_part):
    """Writes the entries in parts of per_part entries, one entry per line; returns the
    manifest rows."""
    rows = []
    for j in range(0, max(1, (len(values) + per_part - 1) // per_part)):
        chunk = values[j * per_part:(j + 1) * per_part]
        data = ''.join(hex_entry(v) + '\n' for v in chunk).encode()
        rel = 'data/%s-%d.hex' % (name, j)
        with open(os.path.join(outdir, rel), 'wb') as f:
            f.write(data)
        rows.append({'file': rel, 'bytes': len(data),
                     'sha256': hashlib.sha256(data).hexdigest(), 'entries': len(chunk)})
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('outdir')
    ap.add_argument('--cells', type=int, required=True)
    ap.add_argument('--per-part', type=int, required=True)
    ap.add_argument('--prefix', required=True)
    ap.add_argument('--dir', required=True)
    ap.add_argument('--spec', default='CAS.Examples.Cert.MeshSpec')
    ap.add_argument('--shard', type=int, default=None)
    ap.add_argument('--batch', type=int, default=None)
    ap.add_argument('--halo', type=int, default=1)
    ap.add_argument('--block', type=int, default=None)
    ap.add_argument('--break', dest='broken', type=int, default=None)
    args = ap.parse_args()
    n, s = args.cells, args.per_part
    os.makedirs(os.path.join(args.outdir, 'data'), exist_ok=True)
    mesh = [mesh_point(k, n) for k in range(n + 1)]
    coef, bound = [], []
    for k in range(n):
        c = taylor(mesh[k])
        coef += c
        b = cell_bound(c, mesh[k + 1] - mesh[k])
        if args.broken == k:
            b = c[0] - 2**20
        bound.append(b)
    tables = [
        {'name': 'mesh', 'width': WIDTH, 'perPart': s,
         'parts': write_parts(args.outdir, 'mesh', mesh, s)},
        {'name': 'coef', 'width': WIDTH, 'perPart': 4 * s,
         'parts': write_parts(args.outdir, 'coef', coef, 4 * s)},
        {'name': 'bound', 'width': WIDTH, 'perPart': s,
         'parts': write_parts(args.outdir, 'bound', bound, s)},
    ]
    manifest = {
        'prefix': args.prefix, 'dir': args.dir, 'spec': args.spec,
        'family': args.spec + '.test', 'count': n, 'shard': args.shard or s,
        'batch': args.batch or (args.shard or s), 'halo': args.halo,
        'block': args.block or min(4096, s),
        'unfolding': [args.spec + '.' + d for d in
                      ['test', 'cellCond', 'stored', 'local', 'coefAt', 'meshAt', 'boundAt']],
        'synthetic': True, 'tables': tables,
    }
    with open(os.path.join(args.outdir, 'manifest.json'), 'w') as f:
        json.dump(manifest, f, indent=1)
        f.write('\n')
    total = sum(p['bytes'] for t in tables for p in t['parts'])
    print('cells %d, parts of %d cells, %d data bytes in %d files' %
          (n, s, total, sum(len(t['parts']) for t in tables)))


if __name__ == '__main__':
    main()
