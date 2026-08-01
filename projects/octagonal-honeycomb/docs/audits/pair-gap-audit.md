# Audit of Lemma 4: the RR-HH pair-gap inequality

Date: 24 July 2026

## Bottom line

The pair-gap statement in the crystalline octagonal honeycomb note is correct,
and it admits a stronger exact form:

\[
  r_m(x)+h_f(x)>\frac{101}{1000}
\]

for every \(x>0\), \(f\ge A_8\), and \(m\in\{4,5\}\). The original note only
needed \(0.09\).

The original written proof had one minor logical omission: in the branch
\(x\le1/2\), it observed that \(r_m(x)>1\) but did not explicitly establish
that \(h_f(x)\ge0\). The missing fact is true and has the exact certificate

\[
(f+d^2)(x^2+4)-(dx+2\sqrt f)^2=(x\sqrt f-2d)^2.
\]

No change to the theorem is needed.

## Strengthened proof architecture

1. **Universal nonnegativity of the HH lower-bound excess.**
   The square identity above proves \(h_f(x)\ge0\).

2. **Small-edge branch.**
   For \(0<x\le1/2\),
   \[
   x(r_4(x)-1)=(2x-1)(x-2)\ge0.
   \]
   An exact rational estimate gives \(r_5(x)-r_4(x)>431/10000\).
   Hence the total pair gap is at least 1 in this branch.

3. **Reduction to the smallest fan area.**
   For \(x\ge1/2\), an algebraic difference-quotient argument proves
   \(h_f(x)\ge h_{A_8}(x)\) for all \(f\ge A_8\). No calculus is needed.

4. **A better tangent.**
   Instead of taking the tangent to \(\sqrt{x^2+4}\) at \(x=1\), take it at
   \(x=23/25\):
   \[
   \sqrt{x^2+4}\ge\frac{23x+100}{\sqrt{3029}}.
   \]
   The exact certificate is
   \[
   3029(x^2+4)-(23x+100)^2=4(25x-23)^2.
   \]

5. **AM-GM and rational square certificates.**
   The remaining constants are bounded using only rational comparisons of
   squares. The quadrilateral branch gives \(>101/1000\); the pentagonal
   branch gives \(>107/1000\).

## Exact certificate margins

- \(7071/5000<\sqrt2<70711/50000\)
- \(u:=\sqrt{(6\sqrt2-5)/3029}>106/3125\)
- \(p_8<3641/1000\)
- \(p_5<3914/1000\)
- quadrilateral AM-GM root term \(>87/20\)
- pentagonal AM-GM root term \(>427/100\)

The smallest rational margins in the chain are still strictly positive:

- tangent/AM-GM square margin for \(m=4\): \(251/200000\)
- tangent/AM-GM square margin for \(m=5\): \(419/200000\)
- lower square margin for \(u\): \(5249/118320312500\)

## Independent verification

Two independent executable checks were run:

### `verify_pair_gap_exact.py`

- dependency-free;
- uses `fractions.Fraction` only;
- checks every rational bracket and square comparison exactly;
- certifies final bounds \(101/1000\) and \(107/1000\).

### `verify_pair_gap_sympy.py`

- independently derives all universal identities from the definitions;
- verifies the nonnegativity square identity;
- verifies the algebraic monotonicity quotient;
- verifies the tangent sum-of-squares identity;
- locates the true minima at 80-digit working precision;
- performs a broad scan in both \(x\) and \(f\).

The true numerical minima, not used in the proof, are approximately

\[
0.1019913081771644\quad(m=4),
\qquad
0.1092001113238300\quad(m=5).
\]

## Downstream consequence

Replacing \(0.09\) by \(0.101\) in the discharging argument gives

\[
\sum_C\varepsilon_C>\frac{101}{8000}N=0.012625N
\]

for the remaining dangerous cells, versus structural debt below \(0.009N\).
The margin in that stage increases from \(0.00225N\) to \(0.003625N\).

## Remaining trust boundary

This audit proves the one-variable pair-gap inequality conditional on the RR
and HH edge estimates used to define \(r_m\) and \(h_f\). The RR estimate now
has the separate seven-case sum-of-squares proof. The HH edge lemma is the
next local geometric input upstream; it is elementary, but it should be the
next independent audit target if the entire restricted theorem is being
certified in dependency order.
