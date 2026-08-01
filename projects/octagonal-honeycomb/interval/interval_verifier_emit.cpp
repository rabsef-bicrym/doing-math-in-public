#pragma STDC FENV_ACCESS ON
#include <boost/numeric/interval.hpp>
#include <boost/numeric/interval/transc.hpp>
#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>

namespace bn = boost::numeric;
namespace il = boost::numeric::interval_lib;
using Rounding = il::save_state<il::rounded_transc_std<double>>;
using Checking = il::checking_base<double>;
using Policies = il::policies<Rounding, Checking>;
using I = bn::interval<double, Policies>;

static constexpr double PI_LO = 0x1.921fb54442d18p+1;
static constexpr double PI_HI = 0x1.921fb54442d19p+1;
static constexpr double SQRT2_LO = 0x1.6a09e667f3bccp+0;
static constexpr double SQRT2_HI = 0x1.6a09e667f3bcdp+0;
static const I PI_I(PI_LO, PI_HI);
static const I SQRT2_I(SQRT2_LO, SQRT2_HI);
static const I D_I = SQRT2_I - I(1.0);
static const I D2_I = D_I * D_I;
static const I R_I = I(1.0) / cos(PI_I / I(8.0));
static const I SLOPE_NORM_I = I(4.0) * (I(2.0) - SQRT2_I);
static const I A4_I(4.0);
static const I A5_I = I(1.0) + I(2.0) * SQRT2_I;
static const I A6_I = I(4.0) * SQRT2_I - I(2.0);
static const I A7_I = I(6.0) * SQRT2_I - I(5.0);
static const I A8_I = I(8.0) * D_I;
static const I P6_I = I(2.0) * sqrt(A6_I);
static const I P8_I = I(2.0) * sqrt(A8_I);
static const I LAMBDA_I = (P6_I - P8_I) / I(2.0);
static const I ONE_TENTH_I = I(1.0) / I(10.0);
static const I ONE_FIFTH_I = I(1.0) / I(5.0);
static const I THREE_FIFTH_I = I(3.0) / I(5.0);

static double down(double x) {
  return std::nextafter(x, -std::numeric_limits<double>::infinity());
}
static double up(double x) {
  return std::nextafter(x, std::numeric_limits<double>::infinity());
}
static double rat_down(double p, double q) { return down(p / q); }
static double rat_up(double p, double q) { return up(p / q); }

static I lineI(int n) { return P6_I - LAMBDA_I * I(double(n - 6)); }
static I aminI(int n) {
  switch (n) {
    case 4: return A4_I;
    case 5: return A5_I;
    case 6: return A6_I;
    case 7: return A7_I;
    default: return A8_I;
  }
}
static I etaI(int n) {
  if (n != 4 && n != 5) return I(0.0);
  I l = lineI(n);
  return (l / I(2.0)) * (l / I(2.0)) - aminI(n);
}

static I hullI(const I& a, const I& b) {
  return I(std::min(a.lower(), b.lower()), std::max(a.upper(), b.upper()));
}

static I support_oct_norm(const I& u) {
  constexpr double PERIOD = 0.25;
  constexpr double HALF_SECTOR = 0.125;
  double lo = u.lower(), hi = u.upper();
  if (!std::isfinite(lo) || !std::isfinite(hi) || hi - lo >= PERIOD)
    return I(1.0, R_I.upper());
  long k0 = static_cast<long>(std::floor(lo / PERIOD)) - 2;
  long k1 = static_cast<long>(std::floor(hi / PERIOD)) + 2;
  bool any = false;
  I out;
  for (long k = k0; k <= k1; ++k) {
    const double sl = double(k) * PERIOD;
    const double su = double(k + 1) * PERIOD;
    const double ilow = std::max(lo, sl);
    const double ihigh = std::min(hi, su);
    if (ilow <= ihigh) {
      I subu(ilow, ihigh);
      I phase = subu - I(double(k) * PERIOD) - I(HALF_SECTOR);
      I val = R_I * cos(PI_I * phase);
      out = any ? hullI(out, val) : val;
      any = true;
    }
  }
  if (!any) return I(1.0, R_I.upper());
  return intersect(out, I(1.0, R_I.upper()));
}

static I G(const I& u, const I& v, const I& alpha) {
  I ss = sin(alpha), cc = cos(alpha);
  return u * v / ss - (u * u + v * v) * cc / (I(2.0) * ss);
}

static double delta_point_lower_small(double u) {
  if (u <= 0.0) return D2_I.lower();
  I U(u), alpha = PI_I * U;
  I ss = sin(alpha), cc = cos(alpha);
  I m = D_I * ss * (cc + ss);
  I del = m - (SLOPE_NORM_I * U - D2_I);
  return std::max(0.0, del.lower());
}

static I delta_piece_large(const I& U) {
  I alpha = PI_I * U;
  I m = G(I(1.0), support_oct_norm(U), alpha);
  return m - (SLOPE_NORM_I * U - D2_I);
}

static double delta_point_lower_large(double u) {
  return std::max(0.0, delta_piece_large(I(u)).lower());
}

static double delta_lower_box(const I& U) {
  const double lo = std::max(0.0, U.lower());
  const double hi = std::max(lo, U.upper());
  double out = std::numeric_limits<double>::infinity();
  bool any = false;
  auto add_bound = [&](double z) {
    out = std::min(out, z);
    any = true;
  };

  if (lo < 0.25)
    add_bound(delta_point_lower_small(std::min(hi, 0.25)));

  const double a1 = std::max(lo, 0.25);
  const double b1 = std::min(hi, 0.5);
  if (a1 <= b1) {
    const double q5_lo = rat_down(4.0, 625.0);
    const double qlo = rat_up(58.0, 180.0);
    const double qhi = rat_down(87.0, 180.0);
    const double l0 = a1;
    const double l1 = std::min(b1, qlo);
    if (l0 <= l1) {
      I beta = PI_I * (I(l0, l1) - I(0.25));
      I tt = sin(beta) / cos(beta);
      if (tt.upper() <= 0.25)
        add_bound(delta_point_lower_large(l0));
      else
        add_bound(delta_piece_large(I(l0, l1)).lower());
    }
    if (std::max(a1, qlo) <= std::min(b1, qhi))
      add_bound(q5_lo);
    const double r0 = std::max(a1, qhi);
    const double r1 = b1;
    if (r0 <= r1) {
      I beta = PI_I * (I(r0, r1) - I(0.25));
      I tt = sin(beta) / cos(beta);
      if (tt.lower() >= rat_up(4.0, 5.0))
        add_bound(delta_point_lower_large(r1));
      else
        add_bound(delta_piece_large(I(r0, r1)).lower());
    }
  }

  const double a2 = std::max(lo, 0.5);
  const double b2 = std::min(hi, 0.75);
  if (a2 <= b2) {
    I lower = THREE_FIFTH_I * PI_I * (I(a2) - I(0.5));
    add_bound(lower.lower());
  }
  if (hi > 0.75)
    add_bound(D2_I.lower());
  return any ? std::max(0.0, out) : 0.0;
}

static double chi_lower(int n, const I& u) {
  const double capped = std::min(delta_lower_box(u), D2_I.lower());
  const double threshold = (n == 4 || n == 5) ? etaI(n).upper() : 0.0;
  const double raw = std::max(0.0, (I(capped) - I(threshold)).lower());
  return (ONE_TENTH_I * I(raw)).lower();
}
static double underchi_lower(const I& u) {
  const double capped = std::min(delta_lower_box(u), D2_I.lower());
  const double raw = std::max(0.0, (I(capped) - I(etaI(4).upper())).lower());
  return (ONE_TENTH_I * I(raw)).lower();
}

struct ProfileData { double f_lo; I q; I c; bool ok; };

static ProfileData profile_data(const I& theta_norm, const I& left_norm,
                                const I& right_norm, int n) {
  I al = PI_I * left_norm, ar = PI_I * right_norm;
  I h0 = support_oct_norm(theta_norm);
  I hl = support_oct_norm(theta_norm - left_norm);
  I hr = support_oct_norm(theta_norm + right_norm);
  I remainder = SLOPE_NORM_I * (I(2.0) - left_norm - right_norm)
    - I(double(n - 2)) * D2_I;
  I exact = G(hl, h0, al) + G(h0, hr, ar) + remainder;
  I universal(aminI(n).lower());
  if (n <= 8)
    universal = universal + I(delta_lower_box(left_norm))
      + I(delta_lower_box(right_norm));
  const double flo = std::max({aminI(n).lower(), exact.lower(), universal.lower()});
  I q = (hl - h0 * cos(al)) / sin(al) + (hr - h0 * cos(ar)) / sin(ar);
  I c = -cos(al) / sin(al) - cos(ar) / sin(ar);
  const bool ok = std::isfinite(flo) && flo > 0 && q.upper() > 0;
  return {flo, q, c, ok};
}

static double profile_lower(const ProfileData& pd, const I& x, bool allow_edge) {
  if (!pd.ok) return -std::numeric_limits<double>::infinity();
  I f(pd.f_lo), sf = sqrt(f);
  const double base = (I(2.0) * sf).lower();
  if (!allow_edge || x.upper() <= 0 || pd.q.lower() <= 0) return base;
  I U = pd.q / sf;
  I K = -I(2.0) * pd.c;
  I uRad = bn::square(U) + K, xRad = bn::square(x) + K;
  if (uRad.upper() <= 0 || xRad.upper() <= 0) return base;
  I uRad0(std::max(0.0, uRad.lower()), uRad.upper());
  I xRad0(std::max(0.0, xRad.lower()), xRad.upper());
  I denom = sqrt(uRad0 * xRad0) + U * x + K;
  if (denom.upper() <= 0) return base;
  I numer = I(2.0) * sf * bn::square(U - x);
  const double numer_lo = std::max(0.0, numer.lower());
  const double exc_lo = (I(numer_lo) / I(denom.upper())).lower();
  return (I(base) + I(exc_lo)).lower();
}

struct Box { std::array<double, 6> lo, hi; int depth = 0; };
struct Eval { double lb; int reason; bool feasible; };

static Eval evaluate(const Box& b, int nA, int nB) {
  I t(b.lo[0], b.hi[0]), aL(b.lo[1], b.hi[1]), aR(b.lo[2], b.hi[2]);
  I bL(b.lo[3], b.hi[3]), bR(b.lo[4], b.hi[4]), x(b.lo[5], b.hi[5]);
  I gL = I(1.0) - aL - bL, gR = I(1.0) - aR - bR;
  if (gL.upper() <= 0 || gR.upper() <= 0) return {1e9, 1, false};
  I gLc(std::max(0.0, gL.lower()), gL.upper());
  I gRc(std::max(0.0, gR.lower()), gR.upper());
  ProfileData A = profile_data(t, aL, aR, nA);
  if (!A.ok) return {-1e9, 9, true};
  const double threshold = (aminI(nA) + etaI(nA)).upper();
  if (A.f_lo >= threshold) return {1e9, 2, false};
  const double PA = profile_lower(A, x, true);
  if (!std::isfinite(PA)) return {-1e9, 9, true};
  const double rA = (I(PA) - I(lineI(nA).upper())).lower();
  if (rA >= 0) return {rA, 3, true};
  ProfileData B = profile_data(t + I(1.0), bL, bR, nB);
  if (!B.ok) return {-1e9, 9, true};
  const double bmin = rat_up(1.0, 360.0);
  const bool edge_ok = bL.lower() >= bmin && bR.lower() >= bmin;
  const double PB = profile_lower(B, x, edge_ok);
  const double rB = std::max(0.0, (I(PB) - I(lineI(nB).upper())).lower());
  const double creditB = (ONE_FIFTH_I *
    (I(chi_lower(nB, bL)) + I(chi_lower(nB, bR)))).lower();
  const double creditThird = (THREE_FIFTH_I *
    (I(underchi_lower(gLc)) + I(underchi_lower(gRc)))).lower();
  const I sideCoeff = I(63.0) / I(double(80 * nB));
  const double lb = (I(rA) + sideCoeff * I(rB)
    + I(creditB) + I(creditThird)).lower();
  return {lb, 4, true};
}

static int split_dim(const Box& b) {
  static const double target[6] = {
    1.0 / 8192, 1.0 / 8192, 1.0 / 8192,
    1.0 / 8192, 1.0 / 8192, 1.0 / 4096
  };
  int best = 0;
  double score = -1;
  for (int i = 0; i < 6; ++i) {
    const double s = (b.hi[i] - b.lo[i]) / target[i];
    if (s > score) { score = s; best = i; }
  }
  return best;
}

struct EmitStats {
  std::uint64_t nodes = 0, leaves = 0, positive = 0, infeasible = 0;
  int maxdepth = 0;
  double worst = std::numeric_limits<double>::infinity();
};
static void put8(std::ofstream& out, std::uint8_t x) {
  out.put(static_cast<char>(x));
  if (!out) throw std::runtime_error("write failure");
}
static void put64(std::ofstream& out, std::int64_t x) {
  std::uint64_t u = static_cast<std::uint64_t>(x);
  for (int k = 0; k < 8; ++k)
    put8(out, static_cast<std::uint8_t>(u >> (8 * k)));
}
static void emit_tree(std::ofstream& out, const Box& b, int nA, int nB,
                      EmitStats& st) {
  ++st.nodes;
  st.maxdepth = std::max(st.maxdepth, b.depth);
  Eval e = evaluate(b, nA, nB);
  if (!e.feasible) {
    put8(out, 7); ++st.leaves; ++st.infeasible; return;
  }
  if (e.lb > 0.0) {
    put8(out, 6); put64(out, 1); ++st.leaves; ++st.positive;
    st.worst = std::min(st.worst, e.lb); return;
  }
  const int dim = split_dim(b);
  const double mid = (b.lo[dim] + b.hi[dim]) * 0.5;
  if (mid == b.lo[dim] || mid == b.hi[dim])
    throw std::runtime_error("interval subdivision became stuck");
  put8(out, static_cast<std::uint8_t>(dim));
  Box l = b, r = b;
  l.hi[dim] = mid; r.lo[dim] = mid;
  l.depth = r.depth = b.depth + 1;
  emit_tree(out, l, nA, nB, st);
  emit_tree(out, r, nA, nB, st);
}

static Box root_box(int nA) {
  Box root;
  const double owner_lo = nA == 4 ? rat_down(46.0, 100.0)
                                  : rat_down(47.0, 100.0);
  const double owner_hi = nA == 4 ? rat_up(53.0, 100.0)
                                  : rat_up(52.0, 100.0);
  root.lo = {0.0, owner_lo, owner_lo, 0.0, 0.0, 0.0};
  root.hi = {0.25, owner_hi, owner_hi,
    rat_up(54.0, 100.0), rat_up(54.0, 100.0), rat_up(41.0, 10.0)};
  return root;
}

int main(int argc, char** argv) {
  if (argc != 2) {
    std::cerr << "usage: interval_verifier_emit OUTPUT.octv1\n";
    return 2;
  }
  std::ofstream out(argv[1], std::ios::binary);
  if (!out) return 2;
  out.write("OCTV1", 5);
  put8(out, 12);
  std::cout << std::setprecision(17);
  for (int nA : {4, 5}) {
    for (int nB = 4; nB <= 9; ++nB) {
      put8(out, static_cast<std::uint8_t>(nA));
      put8(out, static_cast<std::uint8_t>(nB));
      Box root = root_box(nA);
      EmitStats st;
      auto start = std::chrono::steady_clock::now();
      emit_tree(out, root, nA, nB, st);
      double sec = std::chrono::duration<double>(
        std::chrono::steady_clock::now() - start).count();
      std::cout << nA << '-' << nB
                << " nodes=" << st.nodes
                << " leaves=" << st.leaves
                << " positive=" << st.positive
                << " infeasible=" << st.infeasible
                << " maxdepth=" << st.maxdepth
                << " worst=" << st.worst
                << " seconds=" << sec << '\n';
    }
  }
  out.close();
  if (!out) return 2;
  std::cout << "CERTIFIED_AND_EMITTED\n";
  return 0;
}
