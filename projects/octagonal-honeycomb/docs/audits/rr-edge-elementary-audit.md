# Independent audit of Lemma 3: an elementary sum-of-squares proof

## Statement being audited

For a unit-area convex **crystalline** polygon `C`, suppose a distinguished
edge has Euclidean length `x` and has a 90-degree interior corner at each
endpoint (an `RR` edge). Let `f` be the area of the polygon circumscribed about
the Euclidean unit disk with the same normal fan as `C`. In the normalization
used in the octagonal honeycomb note, the anisotropic perimeter `P` of a
crystalline polygon equals the sum of its Euclidean edge lengths. Lemma 3 says

\[
4 \le 2Px-fx^2.
\]

The proof below does **not** use mixed area, Alexandrov--Fenchel, or the
null-Hodge assertion in the original note.

## 1. Coordinate normal form

Rotate and translate so that the distinguished edge runs from `(0,0)` to
`(x,0)` and the polygon lies above it. Because both endpoint turns are
90 degrees, the adjacent oriented edges point north and south. Convexity and
the crystalline-direction restriction imply that the boundary directions,
in counterclockwise order, are

\[
E,\;N,\;[NW],\;[W],\;[SW],\;S,
\]

where the three bracketed directions are optional, but cannot all be absent.
After merging collinear consecutive edges, no other direction can occur.

Write the corresponding lengths as

\[
x,\;r,\;a,\;b,\;c,\;d,
\]

where `a,b,c` are zero when their optional direction is absent. Put
`s = sqrt(2)`. Vector closure gives

\[
b=x-\frac{s}{2}(a+c),
\qquad
d=r+\frac{s}{2}(a-c).
\]

Consequently the perimeter is

\[
P=2x+2r+a+(1-s)c. \tag{1}
\]

A direct shoelace calculation gives the Euclidean area

\[
A=rx+\frac{s}{2}ax-\frac{a^2+c^2}{4}. \tag{2}
\]

Both identities are checked exactly by `verify_rr_lemma_exact.py`.

## 2. The deficit

Define the homogeneous deficit

\[
D:=2Px-fx^2-4A.
\]

Substituting (1) and (2) gives

\[
D=a^2+c^2-2(s-1)x(a+c)+(4-f)x^2. \tag{3}
\]

Thus the desired inequality is simply `D >= 0`.

## 3. Exhausting the seven direction patterns

For a tangent polygon about the unit circle, a turn through `j*45 degrees`
contributes `tan(j*pi/8)` to `f`. Hence

\[
\tan(\pi/8)=s-1,\qquad \tan(\pi/4)=1,\qquad
\tan(3\pi/8)=s+1.
\]

There are exactly seven nonempty subsets of `{NW,W,SW}`. In every case the
deficit is a manifest sum of squares.

| Optional directions present | Fan area `f` | Closure condition | Exact deficit |
|---|---:|---|---|
| `W` | `4` | `a=c=0` | `D=0` |
| `NW` | `2+2s` | `a=sx, c=0` | `D=0` |
| `SW` | `2+2s` | `a=0, c=sx` | `D=0` |
| `NW,W` | `1+2s` | `c=0` | `D=(a-(s-1)x)^2` |
| `W,SW` | `1+2s` | `a=0` | `D=(c-(s-1)x)^2` |
| `NW,SW` | `1+2s` | `a+c=sx` | `D=(a-c)^2/2` |
| `NW,W,SW` | `4s-2` | none beyond closure | `D=(a-(s-1)x)^2+(c-(s-1)x)^2` |

Every entry follows by expansion using only `s^2=2`. Therefore `D >= 0` in
all possible crystalline direction patterns. Returning to arbitrary area,

\[
4A\le 2Px-fx^2.
\]

For `A=1`, this is exactly Lemma 3.

## 4. What has and has not been formalized

The dependency-free Python checker verifies, in exact arithmetic over
`Q(sqrt(2))`:

1. vector closure;
2. the perimeter identity;
3. the shoelace-area identity;
4. all seven fan areas;
5. all seven sum-of-squares identities.

The accompanying Lean file formalizes the algebraic normal form, the seven
identities, their nonnegativity, and the unit-area conclusion. It still needs
to be run through a Lean 4 + Mathlib kernel in an external environment; no
Lean binary is installed in the execution container used to produce this
audit.

The only genuinely geometric bridge not encoded as a Lean datatype is:

> A convex crystalline polygon with an `RR` edge has, after rigid motion and
> merging collinear consecutive edges, one of the seven direction patterns
> above.

That bridge is a finite cyclic-order argument, not a mixed-volume theorem.
