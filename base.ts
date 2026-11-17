export let base = `t : Type = ( Type )
aro : Type = ( (x: Type) -> Type )
atf = ( (x: Type) : Type => x )
aff = ( (x: Type) => x )
aa = ( ( f: ((t:Type) -> Type), t: Type) => f(t) )
Prop = ( (-T: Type) : Type => ((x:T)->Type) )
EQ  = ( (-T: Type, -a: T, -b: T) : Type => (P: Prop(T), h: P(a) ) ->  P(b)  )
rfl = ( ((-T: Type, x:T ) : EQ(T, x, x) => (P:Prop(T), h:P(x)) => h ) )
NULL : Data = ( | ()  )
Null : NULL = ( #0()  )
BOOL : Data = ( | () | ()  )
True : BOOL = ( #1()  )
False : BOOL = ( #0()  )

TF = ( (x:BOOL) : Type => match x | => NULL | => BOOL )
SIG : Type = ( | (w: BOOL, y: TF(w)) )
_type_identity = ( (x:Type) : Type => x )
_bool_identity = ( (x:BOOL) : BOOL => match x | => x | => x )
_bool_rebuild = ( (x:BOOL) : BOOL => match x | => True | => False )
_tfm = ( (x:BOOL) : TF(x) => match x | => Null | => True )
_sig1 : SIG = ( #0(True, True) )

_sig_false_null : SIG = ( #0(False, Null))
_app2 = ( (f :((x: Type) -> (y: Type) -> Type)) : Type => f(Type)(Type))
WRP = ( (T: Type) : Type => | (x: T))
_wrp_bool : WRP(BOOL) = ( #0(True) )
Nat: Data = ( | () | (p: Nat)  )
Zero : Nat = ( #0()  )
S = ( (n: Nat) : Nat => #1(n) )
n0 : Nat = ( Zero )
n1 : Nat = ( S(Zero) )
n2 : Nat = ( S(S(Zero)) )
pred = ( (n: Nat) : Nat => match n | => Zero | p => p )
EQ.tran = ( (T: Type, a: T, b: T, c: T, e1: EQ(T, a, b), e2: EQ(T, b, c)) : EQ(T, a, c) => e2(((x: T) : Type => EQ(T, a, x)), e1) )
Empty : Type = ( | )


eqn = ( (n: Nat, m: Nat) : Type => EQ(Nat, n, m) )

EQ.symm = ( (-T: Type, a: T, b: T, e: EQ(T, a, b)) : EQ(T, b, a) => e(((x: T) => EQ(T, x, a)), rfl(T, a)) )
add = ( (n: Nat, m: Nat) : Nat => match n | => m | p => S(add(p, m)) )
  
congruence = ( ( T: Type, U: Type, a: T, b: T, f: ((x:T) -> U), e: EQ(T, a, b))
  : EQ(U, f(a), f(b)) =>
  e(((x: T) : Type => EQ(U, f(a), f(x))), rfl(U, f(a))) )
add.succ.0 = ( (n: Nat, k: Nat) : (eqn(add(S(n), k), S(add(n, k)))) => rfl(Nat, add(S(n), k)) )
add.0.step = ( (n: Nat, h: eqn(add(n, n0), n)) : (eqn(add(S(n), n0), S(n))) =>
  congruence(Nat, Nat, add(n, n0), n, S, h) )
add.0 = ( (n: Nat) : (eqn(add(n, n0), n)) =>
  match n | => rfl(Nat, n0) | p => add.0.step(p, add.0(p)) )
add.0.symm = ( (n: Nat) : (eqn(n, add(n, n0))) => EQ.symm(Nat, add(n, n0), n, add.0(n)) )
add.succ.p = ( (n: Nat) : (eqn(S(n), add(n, n1))) => match n
  | => rfl(Nat, n1)
  | p => congruence(Nat, Nat, S(p), add(p, n1), S, add.succ.p(p)) )
add.succ = ( (n: Nat, m: Nat) : (eqn(S(add(n, m)), add(n, S(m)))) =>
  match n
    | => rfl(Nat, S(m))
    | p => congruence(Nat, Nat, S(add(p, m)), add(p, S(m)), S, add.succ(p, m)) )
add.comm = ( (n: Nat, m: Nat) : (eqn(add(n, m), add(m, n))) =>
  match n
    | => add.0.symm(m)
    | p => EQ.tran(Nat, S(add(p, m)), S(add(m, p)), add(m, S(p)),
        congruence(Nat, Nat, add(p, m), add(m, p), S, add.comm(p, m)), add.succ(m, p)) )
add.assoc = ( (n: Nat, m: Nat, k: Nat) : (eqn(add(n, add(m, k)), add(add(n, m), k))) =>
  match n
    | => rfl(Nat, add(m, k))
    | p => congruence(Nat, Nat, add(p, add(m, k)), add(add(p, m), k), S, add.assoc(p, m, k)) )
assoc.symm = ( (n: Nat, m: Nat, k: Nat) : (eqn(add(add(n, m), k), add(n, add(m, k)))) =>
  EQ.symm(Nat, add(n, add(m, k)), add(add(n, m), k), add.assoc(n, m, k)) )
mul = ( (n: Nat, m: Nat) : Nat => match n | => Zero | p => add(m, mul(p, m)) )
mul.0 = ( (m: Nat) : (eqn(n0, mul(m, n0))) => match m | => rfl(Nat, n0) | p => mul.0(p) )

congn = ( (a:Nat, b: Nat, f: ((x: Nat) -> Nat), e: eqn(a, b)) : (eqn(f(a), f(b))) =>
congruence(Nat, Nat, a, b, f, e) )
add.swap = ( (a: Nat, b: Nat, c: Nat) : (eqn(add(a, add(b, c)), add(b, add(a, c)))) =>
EQ.tran(Nat, add(a, add(b, c)), add(add(a, b), c), add(b, add(a, c)),
  add.assoc(a, b, c),
  EQ.tran(Nat, add(add(a, b), c), add(add(b, a), c), add(b, add(a, c)),
    congn(add(a, b), add(b, a), ((x:Nat):Nat => add(x, c)), add.comm(a, b)),
    EQ.symm(Nat, add(b, add(a, c)), add(add(b, a), c), add.assoc(b, a, c)))) )
mul.succ = ( (n: Nat, m: Nat) : (eqn(add(n, mul(n, m)), mul(n, S(m)))) =>
match n
  | => rfl(Nat, Zero)
  | p => (pm : Nat = (mul(p, m))
    congn(add(p, add(m, pm)), add(m, mul(p, S(m))), S,
      EQ.tran(Nat, add(p, add(m, pm)), add(m, add(p, pm)), add(m, mul(p, S(m))),
        add.swap(p, m, pm),
        congn(add(p, pm), mul(p, S(m)), ((x:Nat):Nat => add(m, x)), mul.succ(p, m))))) )
mul.comm = ( (n:Nat, m: Nat) : (eqn(mul(n, m), mul(m, n))) =>
match n
  | => mul.0(m)
  | p => EQ.tran(Nat, add(m, mul(p, m)), add(m, mul(m, p)), mul(m, n),
      congn(mul(p, m), mul(m, p), ((x:Nat):Nat => add(m, x)), mul.comm(p, m)), mul.succ(m, p)) )
addswap2 = ( (a: Nat, b: Nat, c: Nat, d: Nat)
  : (eqn(add(add(a, b), add(c, d)), add(add(a, c), add(b, d)))) =>
P = ((x:Nat)=> eqn(add(add(a, b), add(c, d)) , x))
(add.assoc(a, c, add(b, d))(P,
  add.swap(b,c,d)(
    (x:Nat)=>P(add(a,x)),
    assoc.symm(a,b, add(c,d))
  )
)))
mul.dist = ( (a: Nat, b: Nat, c: Nat) : eqn(mul(a, add(b, c)), add(mul(a, b), mul(a, c))) =>
match a
  | => rfl(Nat, n0)
  | p =>
      P = ((x: Nat) => eqn( mul(a, add(b,c)), x))
      h : (P(add(add(b,c), add(mul(p, b), mul(p, c))))) =
        (mul.dist(p,b,c)((x:Nat)=> P(add(add(b,c), x)), rfl(Nat, mul(a,add(b,c)))))
      addswap2(b,c, mul(p,b), mul(p,c))(P,h)
  )
Not = ( (A: Type) => ((x:A) -> Empty) )
ExF = ( (e: Empty, T: Type) : T => match e )
NEQ = ( (A: Type, x: A, y: A) => Not(EQ(A, x, y)) )
DEC = ( (P: Type) => (| (p: P) | (n: Not(P)) ) )
DEC.EQ = ( (A: Type, x: A, y: A) => DEC(EQ(A, x, y)) )

Nat.NEQ.0 = ( (n: Nat) : NEQ(Nat, Zero, S(n)) => 
  P = ((x: Nat) : Type => match x | => NULL | => Empty )
  ((e: eqn(Zero, S(n))) => e(P, Null))
)

Nat.dec.step = ( (n: Nat, m: Nat, d: DEC.EQ(Nat, n, m) ) : DEC.EQ(Nat, S(n), S(m)) =>
  match d
    | e =>
      P = ((x:Nat) => EQ(Nat, S(n), S(x)))
      #0(e( P, rfl(Nat, S(n))))
    | ne => #1( (e: EQ(Nat, S(n), S(m))) =>  ne( congn(S(n), S(m), pred, e )) )  )

Nat.dec.eq = ( (n: Nat, m: Nat) : DEC(EQ(Nat, n, m)) =>
  match n
  | => ( match m
    | => #0(rfl(Nat, Zero))
    | q => #1(Nat.NEQ.0(q)) )
  | p => ( match m
    | => #1((e: EQ(Nat,n,m)) => Nat.NEQ.0(p)( EQ.symm(Nat,n,m,e) ) )
    | q => Nat.dec.step(p,q,Nat.dec.eq(p,q)) ) )
AND = ( (A: Type, B: Type) : Type => | (a: A, b: B) )
`