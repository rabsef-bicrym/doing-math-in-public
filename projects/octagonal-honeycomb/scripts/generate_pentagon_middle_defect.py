#!/usr/bin/env python3
"""Generate an exact Lean Bernstein certificate for the pentagon middle-turn gap.

The generated module proves that the first-sector phase defect is at least
7/1000 whenever 1/5 <= tan(beta) <= 7/8.  All coefficients are exact elements
of Q(sqrt 2); the script aborts unless every Bernstein coefficient is positive.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import comb, sqrt
from pathlib import Path


@dataclass(frozen=True)
class QS:
    a: Fraction = Fraction(0)
    b: Fraction = Fraction(0)

    def __add__(self, other: object) -> "QS":
        o = as_qs(other)
        return QS(self.a + o.a, self.b + o.b)

    __radd__ = __add__

    def __neg__(self) -> "QS":
        return QS(-self.a, -self.b)

    def __sub__(self, other: object) -> "QS":
        return self + (-as_qs(other))

    def __rsub__(self, other: object) -> "QS":
        return as_qs(other) - self

    def __mul__(self, other: object) -> "QS":
        o = as_qs(other)
        return QS(self.a * o.a + 2 * self.b * o.b,
                  self.a * o.b + self.b * o.a)

    __rmul__ = __mul__

    def __truediv__(self, other: object) -> "QS":
        o = as_qs(other)
        den = o.a * o.a - 2 * o.b * o.b
        if den == 0:
            raise ZeroDivisionError
        return QS((self.a * o.a - 2 * self.b * o.b) / den,
                  (self.b * o.a - self.a * o.b) / den)

    def value(self) -> float:
        return float(self.a) + float(self.b) * sqrt(2.0)


def as_qs(x: object) -> QS:
    if isinstance(x, QS):
        return x
    if isinstance(x, Fraction):
        return QS(x, Fraction(0))
    if isinstance(x, int):
        return QS(Fraction(x), Fraction(0))
    raise TypeError(type(x))


Poly = list[QS]  # ascending power basis


def trim(p: Poly) -> Poly:
    while len(p) > 1 and p[-1] == QS():
        p.pop()
    return p


def padd(p: Poly, q: Poly) -> Poly:
    n = max(len(p), len(q))
    return trim([(p[i] if i < len(p) else QS()) +
                 (q[i] if i < len(q) else QS()) for i in range(n)])


def pscale(p: Poly, c: object) -> Poly:
    z = as_qs(c)
    return trim([z * x for x in p])


def pmul(p: Poly, q: Poly) -> Poly:
    out = [QS() for _ in range(len(p) + len(q) - 1)]
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            out[i + j] = out[i + j] + x * y
    return trim(out)


def ppow(p: Poly, n: int) -> Poly:
    out: Poly = [QS(1)]
    base = p
    k = n
    while k:
        if k & 1:
            out = pmul(out, base)
        base = pmul(base, base)
        k >>= 1
    return out


def compose_affine(p: Poly, left: Fraction, right: Fraction) -> Poly:
    # p(left + (right-left) x)
    aff: Poly = [QS(left), QS(right - left)]
    out: Poly = [QS()]
    power: Poly = [QS(1)]
    for coeff in p:
        out = padd(out, pscale(power, coeff))
        power = pmul(power, aff)
    return trim(out)


def to_bernstein(power: Poly, degree: int) -> list[QS]:
    c = power + [QS()] * (degree + 1 - len(power))
    out: list[QS] = []
    for j in range(degree + 1):
        bj = QS()
        for k in range(j + 1):
            bj = bj + c[k] * Fraction(comb(j, k), comb(degree, k))
        out.append(bj)
    return out


def fmt_frac(q: Fraction) -> str:
    if q.denominator == 1:
        return str(q.numerator)
    return f"({q.numerator} : ℝ) / {q.denominator}"


def fmt_qs(z: QS) -> str:
    a, b = z.a, z.b
    if b == 0:
        return fmt_frac(a)
    a_txt = fmt_frac(a)
    b_abs = abs(b)
    b_txt = "s" if b_abs == 1 else f"({fmt_frac(b_abs)}) * s"
    if a == 0:
        return b_txt if b > 0 else f"- {b_txt}"
    return f"{a_txt} {'+' if b > 0 else '-'} {b_txt}"


def poly_lean(name: str, p: Poly) -> str:
    terms: list[str] = []
    for i, z in enumerate(p):
        if z == QS():
            continue
        coeff = f"({fmt_qs(z)})"
        term = coeff if i == 0 else (f"{coeff} * t" if i == 1 else f"{coeff} * t ^ {i}")
        terms.append(term)
    body = " +\n    ".join(terms) if terms else "0"
    return f"def {name} (t : ℝ) : ℝ :=\n  {body}\n"


def bernstein_expr(prefix: str, degree: int, xname: str) -> str:
    parts: list[str] = []
    for j in range(degree + 1):
        factors: list[str] = []
        binom = comb(degree, j)
        if binom != 1:
            factors.append(str(binom))
        factors.append(f"{prefix}{j}")
        if j == 1:
            factors.append(f"{xname} t")
        elif j > 1:
            factors.append(f"({xname} t) ^ {j}")
        rem = degree - j
        if rem == 1:
            factors.append(f"(1 - {xname} t)")
        elif rem > 1:
            factors.append(f"(1 - {xname} t) ^ {rem}")
        parts.append(" * ".join(factors))
    return " +\n      ".join(parts)


def emit_certificate(prefix: str, poly_name: str, x_name: str,
                     p: Poly, left: Fraction, right: Fraction) -> str:
    degree = len(p) - 1
    bern = to_bernstein(compose_affine(p, left, right), degree)
    for i, z in enumerate(bern):
        if not z.value() > 1e-12:
            raise RuntimeError(f"nonpositive {prefix}{i}: {z} = {z.value()}")

    lines: list[str] = []
    for i, z in enumerate(bern):
        lines.append(f"def {prefix}{i} : ℝ := {fmt_qs(z)}")
    lines.append("")
    for i, z in enumerate(bern):
        tactic = "norm_num" if z.b == 0 else (
            "nlinarith [s_upper_tight]" if z.b < 0 else "nlinarith [s_lower]")
        lines.append(f"lemma {prefix}{i}_pos : 0 < {prefix}{i} := by\n  dsimp [{prefix}{i}]\n  {tactic}")
    lines.append("")
    defs = ", ".join(f"{prefix}{i}" for i in range(degree + 1))
    lines.append(
        f"lemma {prefix}_bernstein_identity (t : ℝ) :\n"
        f"    {poly_name} t =\n      {bernstein_expr(prefix, degree, x_name)} := by\n"
        f"  dsimp [{poly_name}, {x_name}, {defs}]\n  ring")
    lines.append("")
    lines.append(
        f"theorem {poly_name}_nonneg (t : ℝ)\n"
        f"    (ht0 : ({fmt_frac(left)}) ≤ t) (ht1 : t ≤ ({fmt_frac(right)})) :\n"
        f"    0 ≤ {poly_name} t := by\n"
        f"  have hx0 : 0 ≤ {x_name} t := by dsimp [{x_name}]; nlinarith\n"
        f"  have hx1 : {x_name} t ≤ 1 := by dsimp [{x_name}]; nlinarith\n"
        f"  have hy0 : 0 ≤ 1 - {x_name} t := sub_nonneg.mpr hx1\n"
        f"  rw [{prefix}_bernstein_identity]\n" +
        "\n".join(
            f"  have h{i} : 0 ≤ {comb(degree, i)} * {prefix}{i} * " +
            ((f"({x_name} t) ^ {i} * " if i > 1 else (f"{x_name} t * " if i == 1 else ""))) +
            ((f"(1 - {x_name} t) ^ {degree-i}" if degree-i > 1 else
              (f"(1 - {x_name} t)" if degree-i == 1 else "1")) +
             " := by positivity")
            for i in range(degree + 1)) +
        "\n  nlinarith")
    return "\n".join(lines)


# Original polynomial data from FirstSectorAlgebra.
s = QS(0, 1)
low_poly: Poly = [
    QS(1155, -813),
    QS(-2142, 1542),
    QS(1555, -1013),
    QS(-800, 400),
    QS(160, -80),
    QS(160, -80),
    QS(-240, 120),
    QS(-240, 120),
]
high_poly: Poly = [
    QS(-58, 29),
    QS(713, -451),
    QS(73, -131),
    QS(335, -73),
    QS(-247, 218),
]
tpoly: Poly = [QS(), QS(1)]
one: Poly = [QS(1)]
Dlow = pmul(padd(one, tpoly), padd(one, ppow(tpoly, 2)))
Dhigh = pmul(ppow(padd(one, tpoly), 3), padd(one, ppow(tpoly, 2)))
low_margin = padd(pscale(pmul(tpoly, low_poly), 1000), pscale(Dlow, -3297))
high_margin = padd(pscale(pmul(padd(one, pscale(tpoly, -1)), high_poly), 1000),
                    pscale(Dhigh, -1323))

header = '''import FirstSectorScalar
import OctagonBenchmarkStandalone

/-!
# Generated exact classification certificate for the pentagon middle interval

This file is generated by `scripts/generate_pentagon_middle_defect.py`.
It proves that the first-sector phase defect is at least `7/1000` whenever
`1/5 <= tan beta <= 7/8`.  The only nontrivial positivity steps are exact
Bernstein decompositions over `Q(sqrt 2)`.
-/

namespace PentagonMiddleDefectGenerated

noncomputable section

open Real
open OctagonBase
open ArctanPolynomialBounds
open FirstSectorAlgebra
open FirstSectorScalar
open OctagonBenchmarkStandalone

'''

parts = [header]
parts.append(poly_lean("lowMarginPoly", low_margin))
parts.append("def lowClassX (t : ℝ) : ℝ := (5 * t - 1) / 2\n")
parts.append(emit_certificate("lm", "lowMarginPoly", "lowClassX", low_margin,
                              Fraction(1, 5), Fraction(3, 5)))
parts.append("\n")
parts.append(poly_lean("highMarginPoly", high_margin))
parts.append("def highClassX (t : ℝ) : ℝ := (40 * t - 24) / 11\n")
parts.append(emit_certificate("hm", "highMarginPoly", "highClassX", high_margin,
                              Fraction(3, 5), Fraction(7, 8)))
parts.append(r'''

lemma low_margin_identity (t : ℝ) (h1 : t + 1 ≠ 0) (h2 : t ^ 2 + 1 ≠ 0) :
    firstLhs t - lowK * quintic t - (7 : ℝ) / 1000 =
      lowMarginPoly t / (471000 * (t + 1) * (t ^ 2 + 1)) := by
  rw [low_gap_identity t h1 h2]
  dsimp [lowMarginPoly]
  field_simp [h1, h2]
  ring

lemma high_margin_identity (t : ℝ) (h1 : t + 1 ≠ 0) (h2 : t ^ 2 + 1 ≠ 0) :
    firstLhs t - c + highK * cubic (u t) - (7 : ℝ) / 1000 =
      highMarginPoly t / (189000 * (t + 1) ^ 3 * (t ^ 2 + 1)) := by
  rw [sub_sub, add_comm (firstLhs t - c), high_gap_identity t h1 h2]
  dsimp [highMarginPoly]
  field_simp [h1, h2]
  ring

lemma low_margin_lower (t : ℝ) (ht0 : (1 : ℝ) / 5 ≤ t)
    (ht1 : t ≤ (3 : ℝ) / 5) :
    (7 : ℝ) / 1000 ≤ firstLhs t - lowK * quintic t := by
  have h1 : t + 1 ≠ 0 := by positivity
  have h2 : t ^ 2 + 1 ≠ 0 := by positivity
  have hp := lowMarginPoly_nonneg t ht0 ht1
  have hd : 0 < 471000 * (t + 1) * (t ^ 2 + 1) := by positivity
  rw [← sub_nonneg, low_margin_identity t h1 h2]
  exact div_nonneg hp hd.le

lemma high_margin_lower (t : ℝ) (ht0 : (3 : ℝ) / 5 ≤ t)
    (ht1 : t ≤ (7 : ℝ) / 8) :
    (7 : ℝ) / 1000 ≤ firstLhs t - c + highK * cubic (u t) := by
  have h1 : t + 1 ≠ 0 := by positivity
  have h2 : t ^ 2 + 1 ≠ 0 := by positivity
  have hp := highMarginPoly_nonneg t ht0 ht1
  have hd : 0 < 189000 * (t + 1) ^ 3 * (t ^ 2 + 1) := by positivity
  rw [← sub_nonneg, high_margin_identity t h1 h2]
  exact div_nonneg hp hd.le

/-- Quantitative phase-defect gap between the low and high pentagonal windows. -/
theorem middle_phase_defect_lower (t : ℝ)
    (ht0 : (1 : ℝ) / 5 ≤ t) (ht1 : t ≤ (7 : ℝ) / 8) :
    (7 : ℝ) / 1000 ≤ firstLhs t - exactK * Real.arctan t := by
  by_cases hm : t ≤ (3 : ℝ) / 5
  · have ht_nonneg : 0 ≤ t := by nlinarith
    have hatan0 : 0 ≤ Real.arctan t := Real.arctan_nonneg.mpr ht_nonneg
    have hquint := arctan_le_quintic t ht_nonneg
    have hcoeff := exactK_le_lowK
    have hfirst : exactK * Real.arctan t ≤ lowK * Real.arctan t :=
      mul_le_mul_of_nonneg_right hcoeff hatan0
    have hsecond : lowK * Real.arctan t ≤ lowK * quintic t :=
      mul_le_mul_of_nonneg_left hquint lowK_nonneg
    have hmargin := low_margin_lower t ht0 hm
    linarith
  · have htmid : (3 : ℝ) / 5 ≤ t := le_of_not_ge hm
    have ht_nonneg : 0 ≤ t := by nlinarith
    have hcomp := arctan_complement t htmid (by nlinarith)
    have htm : -1 < t := by nlinarith
    have hu0 := u_nonneg t (by nlinarith) htm
    have hcubic := cubic_le_arctan (u t) hu0
    have hcubic0 := cubic_u_nonneg t htmid (by nlinarith)
    have hcoeff := mul_le_mul_of_nonneg_right highK_le_exactK hcubic0
    have hscaled := mul_le_mul_of_nonneg_left hcubic exactK_nonneg
    have hmargin := high_margin_lower t htmid ht1
    rw [hcomp, mul_sub, exactK_mul_pi_div_four]
    linarith

/-- A negative pentagonal owner cannot lie in the middle tangent interval. -/
theorem eta5_lt_middle_phase_defect (t : ℝ)
    (ht0 : (1 : ℝ) / 5 ≤ t) (ht1 : t ≤ (7 : ℝ) / 8) :
    eta5 < firstLhs t - exactK * Real.arctan t :=
  lt_of_lt_of_le eta5_lt_seven_thousandths
    (middle_phase_defect_lower t ht0 ht1)

end

end PentagonMiddleDefectGenerated
''')

out = Path("PentagonMiddleDefectGenerated.lean")
out.write_text("".join(parts), encoding="utf-8")
print(f"wrote {out} ({out.stat().st_size} bytes)")
