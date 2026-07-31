#include <mpfr.h>
#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <string>
#include <vector>

static constexpr mpfr_prec_t PREC = 192;

struct F {
  mpfr_t v;
  F() { mpfr_init2(v, PREC); mpfr_set_ui(v, 0, MPFR_RNDN); }
  explicit F(double x, mpfr_rnd_t r = MPFR_RNDN) {
    mpfr_init2(v, PREC); mpfr_set_d(v, x, r);
  }
  explicit F(long x) { mpfr_init2(v, PREC); mpfr_set_si(v, x, MPFR_RNDN); }
  F(const F& o) { mpfr_init2(v, PREC); mpfr_set(v, o.v, MPFR_RNDN); }
  F(F&& o) noexcept { mpfr_init2(v, PREC); mpfr_set(v, o.v, MPFR_RNDN); }
  F& operator=(const F& o) {
    if (this != &o) mpfr_set(v, o.v, MPFR_RNDN);
    return *this;
  }
  ~F() { mpfr_clear(v); }
  double down() const { return mpfr_get_d(v, MPFR_RNDD); }
  double up() const { return mpfr_get_d(v, MPFR_RNDU); }
};

static F fadd(const F& a, const F& b, mpfr_rnd_t r) { F z; mpfr_add(z.v,a.v,b.v,r); return z; }
static F fsub(const F& a, const F& b, mpfr_rnd_t r) { F z; mpfr_sub(z.v,a.v,b.v,r); return z; }
static F fmul(const F& a, const F& b, mpfr_rnd_t r) { F z; mpfr_mul(z.v,a.v,b.v,r); return z; }
static F fdiv(const F& a, const F& b, mpfr_rnd_t r) { F z; mpfr_div(z.v,a.v,b.v,r); return z; }
static F fsqrt(const F& a, mpfr_rnd_t r) { F z; mpfr_sqrt(z.v,a.v,r); return z; }
static F fsin(const F& a, mpfr_rnd_t r) { F z; mpfr_sin(z.v,a.v,r); return z; }
static F fcos(const F& a, mpfr_rnd_t r) { F z; mpfr_cos(z.v,a.v,r); return z; }
static F fneg(const F& a, mpfr_rnd_t r) { F z; F zero(0L); mpfr_sub(z.v,zero.v,a.v,r); return z; }
static F fmin(const F& a, const F& b) { return mpfr_cmp(a.v,b.v) <= 0 ? a : b; }
static F fmax(const F& a, const F& b) { return mpfr_cmp(a.v,b.v) >= 0 ? a : b; }

struct M {
  F lo, hi;
  M() : lo(0L), hi(0L) {}
  explicit M(double x) : lo(x), hi(x) {}
  explicit M(long x) : lo(x), hi(x) {}
  M(const F& l, const F& h) : lo(l), hi(h) {}
  M(double l, double h) : lo(l,MPFR_RNDD), hi(h,MPFR_RNDU) {}
  double lower() const { return lo.down(); }
  double upper() const { return hi.up(); }
};

static M add(const M& a, const M& b) { return M(fadd(a.lo,b.lo,MPFR_RNDD), fadd(a.hi,b.hi,MPFR_RNDU)); }
static M neg(const M& a) { return M(fneg(a.hi,MPFR_RNDD), fneg(a.lo,MPFR_RNDU)); }
static M sub(const M& a, const M& b) { return add(a,neg(b)); }
static M mul(const M& a, const M& b) {
  F p1d=fmul(a.lo,b.lo,MPFR_RNDD), p2d=fmul(a.lo,b.hi,MPFR_RNDD);
  F p3d=fmul(a.hi,b.lo,MPFR_RNDD), p4d=fmul(a.hi,b.hi,MPFR_RNDD);
  F p1u=fmul(a.lo,b.lo,MPFR_RNDU), p2u=fmul(a.lo,b.hi,MPFR_RNDU);
  F p3u=fmul(a.hi,b.lo,MPFR_RNDU), p4u=fmul(a.hi,b.hi,MPFR_RNDU);
  return M(fmin(fmin(p1d,p2d),fmin(p3d,p4d)),
           fmax(fmax(p1u,p2u),fmax(p3u,p4u)));
}
static bool pos(const M& a) { return mpfr_cmp_d(a.lo.v,0.0) > 0; }
static bool nonneg(const M& a) { return mpfr_cmp_d(a.lo.v,0.0) >= 0; }
static M invPos(const M& a) {
  assert(pos(a)); F one(1L);
  return M(fdiv(one,a.hi,MPFR_RNDD), fdiv(one,a.lo,MPFR_RNDU));
}
static M divPos(const M& a, const M& b) { return mul(a,invPos(b)); }
static M sqr(const M& a) {
  if (a.lower() <= 0 && a.upper() >= 0) {
    F z(0L), l2=fmul(a.lo,a.lo,MPFR_RNDU), h2=fmul(a.hi,a.hi,MPFR_RNDU);
    return M(z,fmax(l2,h2));
  }
  return mul(a,a);
}
static M sqrtM(const M& a) {
  assert(nonneg(a)); return M(fsqrt(a.lo,MPFR_RNDD),fsqrt(a.hi,MPFR_RNDU));
}
static M hull(const M& a, const M& b) { return M(fmin(a.lo,b.lo),fmax(a.hi,b.hi)); }
static M rational(long p, long q) { return divPos(M(p),M(q)); }

static double down(double x) { return std::nextafter(x,-std::numeric_limits<double>::infinity()); }
static double up(double x) { return std::nextafter(x,std::numeric_limits<double>::infinity()); }
static double ratDown(double p,double q) { return down(p/q); }
static double ratUp(double p,double q) { return up(p/q); }

static M PI_M=[](){F l,h;mpfr_const_pi(l.v,MPFR_RNDD);mpfr_const_pi(h.v,MPFR_RNDU);return M(l,h);}();
static M SQRT2_M=[](){return sqrtM(M(2L));}();
static M D_M=sub(SQRT2_M,M(1L));
static M D2_M=sqr(D_M);
static M R_M=divPos(M(1L),sqrtM(divPos(add(M(2L),SQRT2_M),M(4L))));
static M SLOPE_M=mul(M(4L),sub(M(2L),SQRT2_M));
static M A4_M(4L), A5_M=add(M(1L),mul(M(2L),SQRT2_M));
static M A6_M=sub(mul(M(4L),SQRT2_M),M(2L));
static M A7_M=sub(mul(M(6L),SQRT2_M),M(5L));
static M A8_M=mul(M(8L),D_M);
static M P6_M=mul(M(2L),sqrtM(A6_M)), P8_M=mul(M(2L),sqrtM(A8_M));
static M LAM_M=divPos(sub(P6_M,P8_M),M(2L));
static M ONE_TENTH_M=rational(1,10), ONE_FIFTH_M=rational(1,5), THREE_FIFTH_M=rational(3,5);

static M lineM(int n) { return sub(P6_M,mul(LAM_M,M(long(n-6)))); }
static M aminM(int n) {
  switch(n){case 4:return A4_M;case 5:return A5_M;case 6:return A6_M;case 7:return A7_M;default:return A8_M;}
}
static M etaM(int n) {
  if(n!=4&&n!=5)return M(0L);
  M z=divPos(lineM(n),M(2L)); return sub(sqr(z),aminM(n));
}

static M sinM(const M& a) {
  F sl=fsin(a.lo,MPFR_RNDD),su=fsin(a.lo,MPFR_RNDU);
  F tl=fsin(a.hi,MPFR_RNDD),tu=fsin(a.hi,MPFR_RNDU);
  F l=fmin(sl,tl),h=fmax(su,tu);
  double lo=a.lower(),hi=a.upper(),pilo=PI_M.lower(),pihi=PI_M.upper();
  long k0=(long)std::floor((lo-pihi/2)/(2*pihi))-2;
  long k1=(long)std::ceil((hi-pilo/2)/(2*pilo))+2;
  for(long k=k0;k<=k1;k++){
    double xlo=(.5+2*k)*pilo,xhi=(.5+2*k)*pihi;
    if(xlo<=hi&&xhi>=lo)h=F(1L);
    double ylo=(-.5+2*k)*pilo,yhi=(-.5+2*k)*pihi;
    if(ylo<=hi&&yhi>=lo)l=F(-1L);
  }
  return M(l,h);
}
static M cosM(const M& a) {
  F sl=fcos(a.lo,MPFR_RNDD),su=fcos(a.lo,MPFR_RNDU);
  F tl=fcos(a.hi,MPFR_RNDD),tu=fcos(a.hi,MPFR_RNDU);
  F l=fmin(sl,tl),h=fmax(su,tu);
  double lo=a.lower(),hi=a.upper(),pilo=PI_M.lower(),pihi=PI_M.upper();
  long k0=(long)std::floor(lo/pihi)-2,k1=(long)std::ceil(hi/pilo)+2;
  for(long k=k0;k<=k1;k++){
    double xlo=(2*k)*pilo,xhi=(2*k)*pihi;
    if(xlo<=hi&&xhi>=lo)h=F(1L);
    double ylo=(1+2*k)*pilo,yhi=(1+2*k)*pihi;
    if(ylo<=hi&&yhi>=lo)l=F(-1L);
  }
  return M(l,h);
}
static M sinpi(const M& u){return sinM(mul(PI_M,u));}
static M cospi(const M& u){return cosM(mul(PI_M,u));}

static M supportNorm(const M& u) {
  if(u.upper()-u.lower()>=.25)return M(1.0,R_M.upper());
  long k0=(long)std::floor(u.lower()/.25)-2;
  long k1=(long)std::floor(u.upper()/.25)+2;
  bool any=false;M out;
  for(long k=k0;k<=k1;k++){
    double l=std::max(u.lower(),k*.25),h=std::min(u.upper(),(k+1)*.25);
    if(l<=h){
      M subu(l,h);
      M phase=sub(sub(subu,M(k*.25)),M(.125));
      M val=mul(R_M,cospi(phase));
      out=any?hull(out,val):val;any=true;
    }
  }
  if(!any)return M(1.0,R_M.upper());
  return M(fmax(out.lo,F(1.0)),fmin(out.hi,R_M.hi));
}

static M Gnorm(const M& u,const M& v,const M& a) {
  M ss=sinpi(a),cc=cospi(a);assert(pos(ss));
  return sub(divPos(mul(u,v),ss),
    divPos(mul(add(sqr(u),sqr(v)),cc),mul(M(2L),ss)));
}
static M deltaPieceLarge(const M& U) {
  return sub(Gnorm(M(1L),supportNorm(U),U),sub(mul(SLOPE_M,U),D2_M));
}
static double deltaPointSmall(double u) {
  if(u<=0)return D2_M.lower();
  M U(u), ss=sinpi(U), cc=cospi(U);
  M m=mul(mul(D_M,ss),add(cc,ss));
  return std::max(0.0,sub(m,sub(mul(SLOPE_M,U),D2_M)).lower());
}
static double deltaPointLarge(double u) {
  return std::max(0.0,deltaPieceLarge(M(u)).lower());
}
static double deltaLowerBox(const M& U) {
  double lo=std::max(0.0,U.lower()),hi=std::max(lo,U.upper());
  double out=std::numeric_limits<double>::infinity();bool any=false;
  auto take=[&](double z){out=std::min(out,z);any=true;};
  if(lo<.25)take(deltaPointSmall(std::min(hi,.25)));
  double a1=std::max(lo,.25),b1=std::min(hi,.5);
  if(a1<=b1){
    double qlo=ratUp(58,180),qhi=ratDown(87,180);
    double l0=a1,l1=std::min(b1,qlo);
    if(l0<=l1){
      M beta=mul(PI_M,sub(M(l0,l1),M(.25)));
      M tt=divPos(sinM(beta),cosM(beta));
      if(tt.upper()<=.25)take(deltaPointLarge(l0));
      else take(deltaPieceLarge(M(l0,l1)).lower());
    }
    if(std::max(a1,qlo)<=std::min(b1,qhi))take(rational(4,625).lower());
    double r0=std::max(a1,qhi),r1=b1;
    if(r0<=r1){
      M beta=mul(PI_M,sub(M(r0,r1),M(.25)));
      M tt=divPos(sinM(beta),cosM(beta));
      if(tt.lower()>=ratUp(4,5))take(deltaPointLarge(r1));
      else take(deltaPieceLarge(M(r0,r1)).lower());
    }
  }
  double a2=std::max(lo,.5),b2=std::min(hi,.75);
  if(a2<=b2)take(mul(mul(THREE_FIFTH_M,PI_M),sub(M(a2),M(.5))).lower());
  if(hi>.75)take(D2_M.lower());
  return any?std::max(0.0,out):0.0;
}
static double chiLower(int n,const M& u) {
  double cap=std::min(deltaLowerBox(u),D2_M.lower());
  double threshold=(n==4||n==5)?etaM(n).upper():0.0;
  double raw=std::max(0.0,sub(M(cap),M(threshold)).lower());
  return mul(ONE_TENTH_M,M(raw)).lower();
}
static double underLower(const M& u) {
  double cap=std::min(deltaLowerBox(u),D2_M.lower());
  double raw=std::max(0.0,sub(M(cap),M(etaM(4).upper())).lower());
  return mul(ONE_TENTH_M,M(raw)).lower();
}

struct PD{M f,q,c;bool ok;};
static PD profileData(const M& t,const M& l,const M& r,int n) {
  M h0=supportNorm(t),hl=supportNorm(sub(t,l)),hr=supportNorm(add(t,r));
  M rem=sub(mul(SLOPE_M,sub(sub(M(2L),l),r)),mul(M(long(n-2)),D2_M));
  double exactLo=-std::numeric_limits<double>::infinity();
  bool angular=l.lower()>0&&r.lower()>0;
  if(angular)exactLo=add(add(Gnorm(hl,h0,l),Gnorm(h0,hr,r)),rem).lower();
  M universal(aminM(n).lower());
  if(n<=8)universal=add(add(universal,M(deltaLowerBox(l))),M(deltaLowerBox(r)));
  F flo(std::max({aminM(n).lower(),exactLo,universal.lower()}),MPFR_RNDD);M fp(flo,flo);
  if(!angular)return{fp,M(0L),M(0L),flo.down()>0};
  M q=add(divPos(sub(hl,mul(h0,cospi(l))),sinpi(l)),
          divPos(sub(hr,mul(h0,cospi(r))),sinpi(r)));
  M c=neg(add(divPos(cospi(l),sinpi(l)),divPos(cospi(r),sinpi(r))));
  return{fp,q,c,flo.down()>0&&q.upper()>0};
}
static double profileLower(const PD& p,const M& x,bool edge) {
  M sf=sqrtM(p.f);double base=mul(M(2L),sf).lower();
  if(!edge||x.upper()<=0||p.q.lower()<=0)return base;
  M U=divPos(p.q,sf),K=neg(mul(M(2L),p.c));
  M ur=add(sqr(U),K),xr=add(sqr(x),K);
  if(ur.upper()<=0||xr.upper()<=0)return base;
  M ur0(std::max(0.0,ur.lower()),ur.upper()),xr0(std::max(0.0,xr.lower()),xr.upper());
  M den=add(add(sqrtM(mul(ur0,xr0)),mul(U,x)),K);
  if(den.upper()<=0)return base;
  M numer=mul(mul(M(2L),sf),sqr(sub(U,x)));
  F nlo=mpfr_cmp_d(numer.lo.v,0.0)<0?F(0L):numer.lo;
  F elo=fdiv(nlo,den.hi,MPFR_RNDD);
  return add(M(base),M(elo,elo)).lower();
}

struct Box{std::array<double,6>lo,hi;int depth=0;};
struct E{double lb;bool feasible;};
static E evalMP(const Box& b,int nA,int nB) {
  M t(b.lo[0],b.hi[0]),aL(b.lo[1],b.hi[1]),aR(b.lo[2],b.hi[2]);
  M bL(b.lo[3],b.hi[3]),bR(b.lo[4],b.hi[4]),x(b.lo[5],b.hi[5]);
  M gL=sub(sub(M(1L),aL),bL),gR=sub(sub(M(1L),aR),bR);
  if(gL.upper()<=0||gR.upper()<=0)return{1e9,false};
  M gl(std::max(0.0,gL.lower()),gL.upper()),gr(std::max(0.0,gR.lower()),gR.upper());
  PD A=profileData(t,aL,aR,nA);if(!A.ok)return{-1e9,true};
  double thresh=add(aminM(nA),etaM(nA)).upper();if(A.f.lower()>=thresh)return{1e9,false};
  double PA=profileLower(A,x,true),rA=sub(M(PA),M(lineM(nA).upper())).lower();
  if(rA>=0)return{rA,true};
  PD B=profileData(add(t,M(1L)),bL,bR,nB);if(!B.ok)return{-1e9,true};
  bool edge=bL.lower()>=ratUp(1,360)&&bR.lower()>=ratUp(1,360);
  double PB=profileLower(B,x,edge);
  double rB=std::max(0.0,sub(M(PB),M(lineM(nB).upper())).lower());
  double creditB=mul(ONE_FIFTH_M,add(M(chiLower(nB,bL)),M(chiLower(nB,bR)))).lower();
  double creditThird=mul(THREE_FIFTH_M,add(M(underLower(gl)),M(underLower(gr)))).lower();
  M sideCoeff=divPos(M(63L),M(long(80*nB)));
  double lb=add(add(M(rA),mul(sideCoeff,M(rB))),add(M(creditB),M(creditThird))).lower();
  return{lb,true};
}
static int splitDim(const Box& b) {
  static const double tar[6]={1./8192,1./8192,1./8192,1./8192,1./8192,1./4096};
  int best=0;double sc=-1;
  for(int i=0;i<6;i++){double q=(b.hi[i]-b.lo[i])/tar[i];if(q>sc){sc=q;best=i;}}
  return best;
}
static Box rootBox(int nA) {
  Box root;
  double olo=nA==4?ratDown(46,100):ratDown(47,100);
  double ohi=nA==4?ratUp(53,100):ratUp(52,100);
  root.lo={0,olo,olo,0,0,0};
  root.hi={.25,ohi,ohi,ratUp(54,100),ratUp(54,100),ratUp(41,10)};
  return root;
}

static uint8_t get8(std::ifstream&i){char c;i.get(c);if(!i)std::exit(5);return(uint8_t)c;}
static int64_t get64(std::ifstream&i){uint64_t x=0;for(int k=0;k<8;k++)x|=(uint64_t)get8(i)<<(8*k);return(int64_t)x;}
static std::vector<uint8_t> OUTBUF;
static void put8(uint8_t x){OUTBUF.push_back(x);}
static void put64(int64_t x){for(int k=0;k<8;k++)OUTBUF.push_back((uint8_t)((uint64_t)x>>(8*k)));}
struct St{uint64_t input=0,output=0,refined=0,leaves=0;double min=1e100;};
static void process(std::ifstream& in,Box b,int nA,int nB,St& st,int forcedTag=-1) {
  uint8_t tag=forcedTag>=0?(uint8_t)forcedTag:get8(in);st.input++;
  if(tag<=5){
    put8(tag);st.output++;int d=tag;double m=(b.lo[d]+b.hi[d])*.5;
    Box l=b,r=b;l.hi[d]=m;r.lo[d]=m;l.depth=r.depth=b.depth+1;
    process(in,l,nA,nB,st);process(in,r,nA,nB,st);return;
  }
  if(tag==6)(void)get64(in);
  E e=evalMP(b,nA,nB);
  if(!e.feasible){put8(7);st.output++;st.leaves++;return;}
  if(e.lb>0){
    put8(6);
    long double raw=std::floor((long double)e.lb*(long double)(1ULL<<60));
    if(raw<1)raw=1;put64((int64_t)raw);st.output++;st.leaves++;
    st.min=std::min(st.min,e.lb);return;
  }
  st.refined++;int d=splitDim(b);put8((uint8_t)d);st.output++;
  double m=(b.lo[d]+b.hi[d])*.5;Box l=b,r=b;
  l.hi[d]=m;r.lo[d]=m;l.depth=r.depth=b.depth+1;
  process(in,l,nA,nB,st,6);process(in,r,nA,nB,st,6);
}

int main(int argc,char** argv) {
  if(argc<3){std::cerr<<"in out\n";return 1;}
  std::ifstream in(argv[1],std::ios::binary);OUTBUF.reserve(3000000);
  char magic[5];in.read(magic,5);if(std::string(magic,5)!="OCTV1")return 2;
  for(char c:std::string("OCTV2"))OUTBUF.push_back((uint8_t)c);
  uint8_t cases=get8(in);put8(cases);
  for(int z=0;z<cases;z++){
    int nA=get8(in),nB=get8(in);put8(nA);put8(nB);Box root=rootBox(nA);St st;
    auto t=std::chrono::steady_clock::now();process(in,root,nA,nB,st);
    double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-t).count();
    std::cerr<<nA<<"-"<<nB<<" input="<<st.input<<" out="<<st.output
      <<" refined="<<st.refined<<" leaves="<<st.leaves
      <<" min="<<std::setprecision(17)<<st.min<<" sec="<<sec<<"\n";
  }
  if(in.peek()!=EOF){std::cerr<<"trailing data\n";return 3;}
  std::ofstream fout(argv[2],std::ios::binary);
  fout.write((const char*)OUTBUF.data(),(std::streamsize)OUTBUF.size());fout.close();
  std::cerr<<"bytes="<<OUTBUF.size()<<"\n";return 0;
}
