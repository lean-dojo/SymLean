#!/usr/bin/env python3
# Copyright (c) 2026 SymLean Team. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Kernel time of `cega` in exact arithmetic, in binary64 and in binary128, on a few goals.

  call    one theorem proved by one `cega` call, in each arithmetic. The call tries FloatLib's
          check of the stated bound first and then the box query. Two goals are out of reach of
          binary64, thirty digits of the square root of 2 and a product that overflows: there the
          call must fail with the message of that reason, and the row says `refused`.
  eval    200 evaluations of an expression by FloatLib's interval evaluation, one on each piece
          [k/200, (k+1)/200] of [0, 1], each compared with two bounds: the cost of the arithmetic
          alone, without the planner of the exact route. A polynomial is evaluated with exact
          rational intervals (`RationalInterval.evalPolynomial`, FloatLib's `Backend.rational`)
          and with float intervals (`CAS.CEGA.Check.enclose?` with `Check.Endpoints.binary` at the
          settings `floatConfig` of the format). An exponential is evaluated with rational
          intervals at the settings that the float backend uses for the format
          (`Check.Endpoints.rational` at `floatConfig`) and with float intervals, which are those
          enclosures rounded outward into the format. The float rows of the polynomial of degree 20
          are slow: one binary64 run takes more than ten minutes.
  base    a file with `import CAS` and a trivial theorem: what every row includes.

Usage, from the repository root after `lake build`:
    lake env python3 tests/floats/measure.py WORK OUT.tsv [--runs=N] [--only=call|eval|base]

WORK is a scratch directory for the generated files. Each case is one file, elaborated N times
(default 3) by `lean --profile` under /usr/bin/time -v, one process at a time. Every row of
OUT.tsv is one case: kind, goal, arithmetic, the call, `proved` or `refused`, the time that the
kernel spent checking declarations (the line `type checking` of Lean's profile, in milliseconds)
as the median, the smallest and the largest of the runs, and the medians of the wall time of the
process in seconds, which includes loading the library, and of its largest resident set in MiB.
A `cega` call hands its certificate to the kernel as a theorem, so the kernel time of a `call`
row is the evaluation of the check or the query and the comparison with the stated bound. Only
the standard library is used. This is a measurement and not a test: tests/floats/run.sh and
CAS/Examples/CEGA/Floats.lean are the tests.

tests/floats/measure.tsv keeps the rows of one run, without the float rows of the polynomial of
degree 20.
"""
import os
import re
import statistics
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

UNIT = '(x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1)'
EXACT, DOUBLE, QUAD = 'exact', 'binary64', 'binary128'
DEFAULT = {EXACT: 'cega', DOUBLE: 'cega [use_floats]', QUAD: 'cega (arith := binary128)'}


def deep(depth):
    """The calls of a goal whose float queries need `depth` bisections."""
    return {EXACT: 'cega', DOUBLE: f'cega [use_floats] (depth := {depth})',
            QUAD: f'cega (arith := binary128) (depth := {depth})'}


# goal, statement, the call of each arithmetic, and for a call that must fail a text of its message.
CALLS = [
    ('exp x ≤ 2.72 on [0, 1]', f'{UNIT} : Real.exp x ≤ 2.72', DEFAULT, {}),
    ('1 / (1 - x) ≤ 2 on [-1/2, 1/2]', '(x : ℝ) (hx : |x| ≤ 1 / 2) : 1 / (1 - x) ≤ 2', DEFAULT, {}),
    ('sqrt 2 ≤ 1.415', ': Real.sqrt 2 ≤ 1.415', DEFAULT, {}),
    ('exp (x * y) ≤ 21 on [0, 1] × [2, 3]',
     "(x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) (hy : 2 ≤ y) (hy' : y ≤ 3) : Real.exp (x * y) ≤ 21",
     DEFAULT, {}),
    ('x * (1 - x) ≤ 0.26 on [0, 1]', f'{UNIT} : x * (1 - x) ≤ 0.26', deep(6), {}),
    ('sin x ≤ 0.85 on [0, 1]', f'{UNIT} : Real.sin x ≤ 0.85', deep(5), {}),
    ('sqrt 2 to thirty digits', ': Real.sqrt 2 ≤ 1.41421356237309504880168872421',
     {EXACT: 'cega (prec := 110)', DOUBLE: DEFAULT[DOUBLE], QUAD: DEFAULT[QUAD]},
     {DOUBLE: 'the arithmetic is binary64. A wider format, as in `(arith := binary128)`'}),
    ('10 ^ 200 * 10 ^ 200 ≤ 10 ^ 401', ': (10 : ℝ) ^ 200 * 10 ^ 200 ≤ 10 ^ 401', DEFAULT,
     {DOUBLE: 'beyond the largest finite binary64 number (overflow)'}),
]


def horner(degree):
    """The polynomial with coefficients (k + 1) / 7 in Horner form, as a `Verified.Expr`."""
    term = f'.rat {degree + 1} 7'
    for k in range(degree, 0, -1):
        term = f'.add (.rat {k} 7) (.mul (.var 0) ({term}))'
    return term


# The number of pieces of [0, 1] on which an `eval` row evaluates its expression.
PIECES = 200
PIECE = f'.ofBounds (k / {PIECES}) ((k + 1) / {PIECES}) (by gcongr; linarith)'

# A query of `Check.enclose?` on piece `k` with the ends `{ends}` at the settings of the format
# `{fmt}`, read as its interval.
QUERY = '(Check.enclose? {ends} (floatConfig {fmt}) (piece k) expression).map (·.interval)'
FORMAT = {DOUBLE: 'FloatFormat.binary64', QUAD: 'FloatFormat.binary128'}
# The evaluators of a polynomial: exact rational intervals, and float intervals.
POLYNOMIAL = [('exact rationals', 'RationalInterval.evalPolynomial (piece k) expression')] + [
    (fmt, QUERY.format(ends=f'(.binary {FORMAT[fmt]})', fmt=FORMAT[fmt])) for fmt in (DOUBLE, QUAD)]
# The evaluators of an elementary function: for each format, rational intervals with the
# settings that the float backend uses for that format, and float intervals, which are those
# rational enclosures rounded outward into the format.
ELEMENTARY = [pair for fmt in (DOUBLE, QUAD) for pair in (
    (f'rationals at the settings of {fmt}', QUERY.format(ends='.rational', fmt=FORMAT[fmt])),
    (fmt, QUERY.format(ends=f'(.binary {FORMAT[fmt]})', fmt=FORMAT[fmt])))]

# goal, dimension, the box of piece `k`, expression, evaluators.
EVALS = [
    ('x * (1 - x)', 1, f'fun _ ↦ {PIECE}', '.mul (.var 0) (.sub (.nat 1) (.var 0))', POLYNOMIAL),
    ('a polynomial of degree 20 in Horner form', 1, f'fun _ ↦ {PIECE}', horner(20), POLYNOMIAL),
    ('exp (x * y) with y in [2, 3]', 2,
     f'fun i ↦ if i = 0 then {PIECE} else .ofBounds 2 3 (by norm_num)',
     '.exp (.mul (.var 0) (.var 1))', ELEMENTARY),
]
HEADER = ('import CAS\n\nopen CAS.CEGA CAS.Continuum CAS.Verified '
          'FloatLib.Floats.Formats.BinaryInterchange\n\n')


def eval_file(dimension, box, expression, value):
    """The kernel evaluations of `expression` on the pieces of its box by the evaluator `value`,
    each compared with two rational bounds that hold, as `cega` compares an enclosure with a
    stated bound; without the comparison the kernel, which is lazy, would not compute the ends
    of a rational interval. A float evaluation includes the rounding of the piece into the
    format and the reading of its two ends as rationals."""
    text = HEADER + (f'/-- Piece `k` of the box. -/\ndef piece (k : ℕ) : Fin {dimension} → '
                     f'RationalInterval :=\n  {box}\n\n'
                     f'/-- The expression. -/\ndef expression : Expr (Fin {dimension}) :=\n'
                     f'  {expression}\n\n')
    bounds = 'decide ((-1000000 : ℚ) ≤ I.lo) && decide (I.hi ≤ (1000000 : ℚ))'
    return text + (f'theorem evaluated :\n    ((List.range {PIECES}).all fun k ↦ ({value}).any '
                   f'fun I ↦\n      {bounds}) = true := by\n  decide +kernel\n')


def cases():
    yield ('base', 'import CAS', '', '', 'import CAS\n\ntheorem loaded : True :=\n  trivial\n', '')
    for goal, statement, calls, refusals in CALLS:
        for arithmetic in (EXACT, DOUBLE, QUAD):
            call = calls[arithmetic]
            text = f'import CAS\n\ntheorem bound {statement} := by\n  {call}\n'
            yield ('call', goal, arithmetic, call, text, refusals.get(arithmetic, ''))
    for goal, dimension, box, expression, evaluators in EVALS:
        for arithmetic, value in evaluators:
            yield ('eval', f'{PIECES} evaluations of {goal}', arithmetic, 'decide +kernel',
                   eval_file(dimension, box, expression, value), '')


def seconds(text):
    """A duration of Lean's profile, such as `162ms` or `1.2s`, in milliseconds."""
    value, unit = re.fullmatch(r'([\d.e+-]+)(ms|s)', text).groups()
    return float(value) * (1000.0 if unit == 's' else 1.0)


def run(path):
    """Elaborates `path` once; returns (status, output, kernel ms, wall s, resident MiB)."""
    done = subprocess.run(['/usr/bin/time', '-v', 'lean', '--profile', '-Dprofiler.threshold=20',
                           path], cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          text=True)
    out = done.stdout
    kernel = re.search(r'^\ttype checking (\S+)$', out, re.M)
    wall = re.search(r'Elapsed \(wall clock\) time.*: (?:(\d+):)?(\d+):([\d.]+)$', out, re.M)
    resident = re.search(r'Maximum resident set size \(kbytes\): (\d+)', out)
    hours, minutes, secs = wall.groups()
    return (done.returncode, out, seconds(kernel.group(1)) if kernel else float('nan'),
            int(hours or 0) * 3600 + int(minutes) * 60 + float(secs), int(resident.group(1)) / 1024)


def main():
    arguments = [a for a in sys.argv[1:] if not a.startswith('--')]
    if len(arguments) != 2:
        raise SystemExit(__doc__)
    work, out_path = arguments
    runs, only = 3, None
    for flag in sys.argv[1:]:
        if flag.startswith('--runs='):
            runs = int(flag.split('=')[1])
        if flag.startswith('--only='):
            only = flag.split('=')[1]
    os.makedirs(work, exist_ok=True)
    rows = []
    for number, (kind, goal, arithmetic, call, text, refusal) in enumerate(cases()):
        if only and kind != only:
            continue
        path = os.path.join(work, f'case{number:02d}.lean')
        with open(path, 'w', encoding='utf-8') as handle:
            handle.write(text)
        results = [run(path) for _ in range(runs)]
        for status, output, _, _, _ in results:
            if refusal:
                if status == 0 or refusal not in output:
                    sys.stderr.write(output[-3000:])
                    raise SystemExit(f'{goal} in {arithmetic}: expected a refusal with: {refusal}')
            elif status != 0:
                sys.stderr.write(output[-3000:])
                raise SystemExit(f'{goal} in {arithmetic}: `{call}` failed')
        kernel = statistics.median(r[2] for r in results)
        wall = statistics.median(r[3] for r in results)
        resident = statistics.median(r[4] for r in results)
        kernels = [r[2] for r in results]
        row = [kind, goal, arithmetic, call, 'refused' if refusal else 'proved',
               f'{kernel:.3g}', f'{min(kernels):.3g}', f'{max(kernels):.3g}', f'{wall:.1f}',
               f'{resident:.0f}']
        rows.append(row)
        print('\t'.join(row), flush=True)
    with open(out_path, 'w', encoding='utf-8') as handle:
        handle.write(''.join('\t'.join(row) + '\n' for row in rows))


if __name__ == '__main__':
    main()
