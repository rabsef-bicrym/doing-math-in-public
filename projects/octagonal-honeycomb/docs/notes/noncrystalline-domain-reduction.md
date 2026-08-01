# Exhausting the interval verifier's root domains

## Purpose

The noncrystalline interval certificate checks the local charge inequality on the root boxes

\[
\theta/\pi\in[0,1/4],\qquad x\in[0,4.10],
\]

with owner turns

\[
[0.46,0.53]\quad(n_A=4),\qquad [0.47,0.52]\quad(n_A=5),
\]

opposite-cell turns in \([0,0.54]\), and neighbor side count \(4\le n_B\le9\).
This note explains why every clean trivalent local configuration that can carry negative net charge
is represented by those boxes. Angles below are divided by \(\pi\), so their total around one
convex cell is \(2\), and the three exterior turns at a trivalent vertex total \(1\).

## 1. Only four and five sides can be negative

Let \(p_n\) be the isolated unit-area lower perimeter for an \(n\)-sided cell, and let \(L(n)\)
be the affine line through \((6,p_6)\) and \((8,p_8)\). Chakerian's inequality gives
\(P_C\ge p_{n(C)}\). Exact rational brackets show

\[
p_3>L(3),\quad p_6=L(6),\quad p_7>L(7),\quad p_8\ge L(n)\ (n\ge8).
\]

Consequently

\[
P_C-L(n(C))<0\quad\Longrightarrow\quad n(C)\in\{4,5\}.
\]

The Lean module proves this as `negative_cell_has_four_or_five_sides`.

## 2. Selecting an owner edge inside the certified angle box

The phase-snapping stability theorem gives the broad windows:

- every negative quadrilateral turn lies in \((79^\circ,92^\circ)\);
- a negative pentagon has exactly three turns in \((87^\circ,91^\circ)\) and two in
  \((43^\circ,58^\circ)\).

### Quadrilateral

Put \(a_i=\alpha_i/\pi\). We need adjacent turns at least \(0.46\). If no adjacent pair had
both turns at least \(0.46\), then the high vertices would form an independent set on the
4-cycle. At most two could be high, and therefore

\[
\sum_i a_i<2(0.46)+2(92/180)=437/225<2,
\]

contrary to the full exterior-turn sum. Thus an adjacent pair lies in

\[
[0.46,0.53]^2,
\]

because \(92/180<0.53\).

### Pentagon

The three high corners contain an adjacent pair on a 5-cycle. Moreover

\[
87/180>0.47,\qquad 91/180<0.52.
\]

Thus one selected edge has both endpoint turns in \([0.47,0.52]\).

Lean checks these as `quadrilateral_has_root_edge` and `pentagon_has_root_edge`.

## 3. The opposite turns automatically lie in `[0,0.54]`

At a clean trivalent endpoint,

\[
\alpha+\beta+\gamma=1,
\]

where \(\alpha\) belongs to the owner, \(\beta\) to the cell across the selected edge, and
\(\gamma\ge0\) to the third cell. Since every selected owner turn is at least \(0.46\),

\[
0\le\beta\le1-0.46=0.54.
\]

This is `opposite_turn_in_root`.

## 4. The common length is automatically below `4.10`

For a closed polygonal chain, the remaining edge vectors sum to the negative of any chosen edge.
The triangle inequality therefore gives

\[
P_C\ge 2\lVert e\rVert_M.
\]

In the chosen normalization the octagonal support function is at least one, so the norm length of
an edge is at least its Euclidean length \(x\). Hence \(P_C\ge2x\).

A negative owner satisfies \(P_C<L(4)\) or \(P_C<L(5)\), and exact rational bounds give both
\(L(4),L(5)<8.2\). Therefore

\[
x<4.10.
\]

`negative_owner_edge_length_in_root` performs the final arithmetic. The generic closed-polygon
triangle inequality is formalized separately in `ClosedPolygonEdgeBound.lean`.

## 5. Why only neighbor side counts four through nine are certified

A triangular neighbor has such a large unavoidable positive net charge that its allocated side bank
already exceeds the worst owner debt. At the other end, if \(n\ge10\), then

\[
p_8-L(n)=\lambda(n-8),\qquad \lambda=(p_6-p_8)/2>0.09.
\]

After dividing the retained \(63/80\) side bank among \(n\) sides,

\[
\frac{63}{80n}\bigl(p_8-L(n)\bigr)
\ge \frac{63}{400}\,0.09
=0.014175
>0.009>\Delta_4.
\]

Thus triangles and all \(10+\)-sided neighbors pay immediately; only \(n_B=4,\ldots,9\) need the
interval certificate. Lean checks these as `triangular_neighbor_reserve_pays` and
`large_neighbor_reserve_pays`.

## Result and current caveat

Subject to the phase-snapping angle classification and the clean trivalent reduction, every local
configuration that can contribute negative charge is contained in one of the twelve certified
interval domains. The remaining proof interface is to identify the geometric local charge
expression exactly with the elementary function certified on those domains, then derive and sum
the role allocations globally.
