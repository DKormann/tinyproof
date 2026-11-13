export type Quant = 0 | 1
export type F        = {names: string[], f: (...t: Term[]) => Term}
export type Sign     = {name: string, live: boolean, f: (...t: Term[]) => Term }[]
export type Uni      = { ty: Term, $: "Uni",       Quant : Quant}
export type Arrow    = { ty: Term, $: "Arrow",     s: Sign }
export type ADT      = { ty: Term, $: "ADT",       variants:  Sign[]}
export type adt      = { ty: Term, $: "adt",       tag: number, srcs: Term[] }
export type match    = { ty?: Term, $: "match",    scr: Term, srcs: F[] }
export type APP      = { ty: Term, $: "APP",       fn: Term, args: Term[] }
export type Lam      = { ty: Term, $: "Lam",       fn: F}
export type SYM      = { ty: Term, $: "SYM",       name?: string, live: boolean }
export type Term = Uni | Arrow | ADT | adt | match | APP | Lam | SYM

export const Type : Uni = {$: "Uni", Quant: 0} as Uni
Type.ty = Type
const Data : Uni = {$: "Uni", Quant: 1, ty: Type}
let rfl = {} as Term
let sorry = {} as Term

export function raise(msg: string): never { throw new Error(msg) }

function zip<T,S,U>(ts: T[], s: S[], f: (t: T, s: S, i: number)=>U): U[] {
  if (ts.length !== s.length) throw new Error(`zip: arrays must have the same length, got ${ts.length} and ${s.length}`)
  return ts.map((t, i) => f(t, s[i], i))
}

let fillSign = ( s: Sign): SYM[] => {
  return s.reduce((acc: SYM[], c) => [...acc, {$:"SYM", name: c.name, live: c.live, ty: c.f(...acc)}  as SYM ], [] )
}

let fillArrow = (a: Arrow) => { 
  let vs = fillSign(a.s)
  return { args: vs.slice(0,-1), ret: vs[vs.length - 1].ty }
}

let book = new Map(Object.entries({Type, Data, rfl, sorry}))
let names = new Map(Array.from(book.entries()).map(([k, v]) => [v, k]))

export function fmt(t: Term, def?: boolean){
  function pln(t:Term, def? : boolean):string{
    if (names.has(t) && !def) return names.get(t)!
    if (t.$ == "Uni") return `type${t.Quant}`
    if (t.$ == "ADT") return  t.variants.map(v=> `\n  | {${ fillSign(v).map(v =>  (v.live ? "" : "-") + pln(v)+": "+ pln(v.ty)).join(', ')}}`).join('') 
    if (t.$ == "adt") return `(#${t.tag} ${t.srcs.map(x=> pln(x)).join(', ')})`
    if (t.$ == "APP") return `(${pln(t.fn)} ${ t.args.map(x => pln(x)).join(' ')})`
    if (t.$ == "Arrow"){
      let ff = fillArrow(t)
      return `(${ff.args.map(v => `${pln(v)} : ${pln(v.ty)}`).join(', ')}) -> ${pln(ff.ret)}`
    }

    if (t.$ == "SYM") return t.name ?? "?"
    if (t.$ == "match") return `match ${pln(t.scr)}:${t.srcs.map(f=> {
      let s = f .names.map(name => ({ $: "SYM", name, live: true } as SYM))
      return `\n  | ${s.map(v => pln(v)).join(', ')} => ${pln(f.f(...s))}`
    }).join('')}`

    if (t.$ == "Lam") {
      if (t.ty.$ == "Arrow"){
        let ars = fillArrow(t.ty)
        return `(${ars.args.map(v => `${(v.live ? "" : "-") +pln(v)} : ${pln(v.ty)}`).join(', ')}):${pln(ars.ret)} = ${pln(t.fn.f(...ars.args))}`
      }
      return `${t.fn.toString()}`
    }
    return t
  }
  return pln(t, def)
}

function run(t:Term): Term{
  if (t.$ == "APP"){
    let fn = run(t.fn)
    if (fn.$ == "Lam") return run(fn.fn.f(...t.args))
  }else if (t.$ == "match"){
    let arg = run(t.scr)
    if (arg.$ == "adt") return run(t.srcs[arg.tag].f(...arg.srcs))
  }
  return t
}

function checkEQ(a: Term, b: Term){
  function checkEqSign(a:Sign, b:Sign){
    let vs = fillSign(a);
    vs.map((v, i) => {
      if (v.live != b[i].live) raise(`Live missmatch: ${v.name} vs ${b[i].name}`)
      checkEQ(v.ty, b[i].f(...vs))
    })
  }

  if (a.$ == "APP" && b.$ == "APP" && a.fn == b.fn && a.args.length == b.args.length) {
    try {
      checkEQ(a.fn, b.fn)
      zip(a.args, b.args, (x, y) => checkEQ(x, y))
      return }
    catch (e) { if (!(e instanceof Error) || !e.message.startsWith("Structural mismatch:")) throw e }
  }

  [a,b] = [run(a), run(b)]
  if (a == b) return

  if (a.$ != b.$) {
    raise(`Structural mismatch: ${fmt(a)} vs ${fmt(b)}`)
  }
  if (a.$ == "SYM") if (a!=b) raise(`Structural mismatch: ${fmt(a)} vs ${fmt(b)}`)
  if (a.$ == "ADT"){
    b = b as ADT
    if (a.variants.length != b.variants.length) raise(`Structural mismatch: ${fmt(a)} vs ${fmt(b)}`)
    zip(a.variants, b.variants, checkEqSign)
  }
  if (a.$ == "adt"){
    if (a.tag != (b as adt).tag) raise(`Structural mismatch: ${fmt(a)} vs ${fmt(b)}`)
    zip(a.srcs, (b as adt).srcs, (x, y)=> checkEQ(x, y))
  }
  if (a.$ == "APP"){
    checkEQ(a.fn, (b as APP).fn)
    zip(a.args, (b as APP).args, (x, y)=> checkEQ(x, y))
  }

  if (a.$ == "match"){
    checkEQ(a.scr, (b as match).scr)
    zip(a.srcs, (b as match).srcs, (x, y)=> {
      let vs = x.names.map(name => ({ $: "SYM", name } as SYM))
      if (x.f != y.f) checkEQ(x.f(...vs), y.f(...vs))
    })
  }

  if (a.$ == "Arrow") checkEqSign(a.s, (b as Arrow).s)
  if (a.$ == "Uni"){ if (a.Quant != (b as Uni).Quant) raise(`Structural mismatch: ${fmt(a)} vs ${fmt(b)}`) }
  if (a.$ == "Lam" || a.$ == "SYM") raise(`Structural mismatch: ${fmt(a)} vs ${fmt(b)}`)
}

function asTag <$ extends Term["$"]>(t: Term | undefined, tag: $) : Term & {$: $}{
  if (!t) raise(`Expected tag ${tag}, got undefined`)
  t = run(t)
  if (t.$ != tag) raise(`Expected tag ${tag}, got ${t.$} in term ${fmt(t)}`)
  return t as Term & {$: $}
}

let checked = new Set<Term> ()
type CallStack = { f: Term, args: Term[]} []

function check(t:Term){

  function checkSig(args: Term[], sig: Sign, live: boolean, cs: CallStack, used: SYM[]) : SYM[]{
    if (args.length != sig.length) raise(`Arity mismatch: expected ${sig.length} arguments, got ${args.length}`)
    zip(args, sig, (arg, slot)=>{
      let nus = go(arg, cs, used, slot.f(...args), live && slot.live)
      if (live && slot.live) used = nus
    })
    return used
  }

  function go(t:Term, cs: CallStack, used: SYM[], ty:Term | undefined, live : boolean) : SYM[]{

    if (t == sorry) raise(`Sorry: ${ty}`)

    if (ty && t.ty) {
      if (ty.$ == "Uni" && ty.Quant == 0 && t.ty.$ == "Uni" && t.ty.Quant == 1) {}
      else checkEQ(t.ty, ty)
    }

    if (t == rfl) return used
    if (!t.$) raise(`Unexpected term with tag ${t}: ${fmt(t)}`)
    function searchStack(c: CallStack, t: Term){ return c.find(x=>x.f == t) }

    if (checked.has(t)) return used

    let type = t.ty ?? ty
    if (!type) { raise(`Cannot infer type for term ${fmt(t)}`) }
    type = run(type)
    if (!type.ty) raise(`Cannot infer type for term ${fmt(t)}`)

    if (t.$ == "Uni"){
      if (asTag(t.ty, "Uni").Quant != 0) raise(`Expected Uni Type, got ${fmt(t.ty)}`)
    } else if (t.$ == "match"){
      let arg = asTag(t.scr, "SYM")
      let T = asTag(arg.ty, "ADT")
      let old : SYM = {...arg}
      let newuses: SYM[] = go(arg, cs, used, arg.ty, live)
      zip(T.variants, t.srcs, (v, s, i)=>{
        let vs = fillSign( v)
        Object.assign(arg, adt(T, i, ...vs))
        newuses.push(... go(s.f(...vs), cs, used, type, live).filter(x=>![...newuses, ...vs].includes(x)))
      })
      Object.assign(arg, old)
      used = newuses

    } else if (t.$ == "SYM"){
      if (live && t.live) { if (type.ty != Data && used.includes(t)) raise(`Symbol ${fmt(t)} already used: ${fmt(t)}`) }
      else{ if (live) raise(`Symbol ${fmt(t)} is not live`) }
      if (live) used = [...used, t]

    } else if (t.$ == "adt"){
      let vari = asTag(type, "ADT").variants[t.tag]
      if (t.srcs.length != vari.length) raise(`invalid constructor args for ${fmt(type)}: [${t.srcs.map(x=>fmt(x))}]`)
      return checkSig(t.srcs, vari, live, cs, used)

    } else if (t.$ == "Lam"){
      if (searchStack(cs, t)) raise(`Non well-founded lambda detected`)
      let {args, ret} = fillArrow(asTag(t.ty, "Arrow"))
      return go(t.fn.f(...args), [...cs, { f: t, args }], used, ret, live).filter(x=> !args.includes(x))

    } else if (t.$ == "APP"){
      let REC = searchStack(cs, t.fn)
      let aro = asTag(t.fn.ty, "Arrow")
      used = checkSig(t.args, aro.s.slice(0, -1), live, cs, used)
      checkEQ(type, aro.s[aro.s.length - 1].f(...t.args))
      if (REC){
        for (let i = 0; i < REC.args.length; i++){
          let A = REC.args[i]
          let a = t.args[i]
          if (A.$ == "adt" && A.srcs.some(el => el == a)) break
          if (A != a || i == REC.args.length - 1) raise(`Non well-founded application detected: ${fmt(a)}\nrecursive arguments are checked from left and must match until some argument decreases`)
        }
      }
      else return go(t.fn, cs, used, aro, live)

    } else if (t.$ == "Arrow"){
      asTag(type, "Uni")
      if (type == Data) raise(`Cannot construct Arrow of type Data`)

    } else if (t.$ == "ADT"){
      asTag(type, "Uni")
      if (type == Data)
        for(let v of t.variants)
          for (let s of fillSign(v))
            if (s.ty.ty != Data) raise(`Cannot construct Data from non-Data type: ${fmt(s.ty)}`)
    }
    return used

  }
  go(t, [], [], undefined, true)
  checked.add(t)
}

function adt(ty: Term, tag: number, ...srcs: Term[]): adt{
  return { $: "adt", ty, tag, srcs }
}

function $(fn: Term, ...args: Term[]): APP{
  if (args.length != asTag(fn.ty, "Arrow").s.length - 1) raise(`Invalid number of arguments for function application: expected ${asTag(fn.ty, "Arrow").s.length - 1}, got ${args.length}`)
  return {$:"APP", fn, args, ty: asTag(fn.ty, "Arrow").s[args.length].f(...args)}
}

type syntax = string | syntax []

function compile(s: string) : Term{

  const toks = s.split("\n").map(l => l.trim()).filter(l => !l.startsWith("//"))
    .join("\n").match(/->|=>|[():,|+\-]|(?:=(?!>)|[^()\s:,|+\-=])+/g) ?? []
  let idx = 0

  function parse(): syntax {
    if (toks[idx] !== "(") return toks[idx++]
    idx++
    const res: syntax[] = []
    while (toks[idx] !== ")") {
      if (idx >= toks.length) raise(`unexpected end of input while parsing list`)
      res.push(parse())
    }
    idx++
    return res
  }
  let tr = parse()
  function asIden(tr: syntax): string{
    if (typeof tr != "string") raise(`expected an identifier, but got: ${JSON.stringify(tr)}`)
    return tr
  }

  type Ctx = string[]
  type annot = {name: string, ty: string, live: boolean}

  function asAnnot (tr: syntax, ctx: Ctx): annot{
    let live = tr[0] != "-"
    if (!live) tr = tr.slice(1)
    if (tr.length < 3 || tr[1] != ":") raise(`expected an annotation of the form [expr, ":", type], but got: ${JSON.stringify(tr)}`)
    return {name: asIden(tr[0]), ty: goTerm(tr[2], ctx), live}
  }

  function asSign(tr: syntax, ctx: Ctx): annot[]{
    return splitList(tr, ",").reduce((anns:annot[], x) =>
      anns.concat(asAnnot(x, ctx.concat(anns.map(a => a.name)))), [])
  }

  function splitList(tr: syntax, sep: string): syntax[]{
    let res: syntax[] = []
    let idx = 0
    while (idx < tr.length){
      let nextIdx = tr.indexOf(sep, idx)
      if (nextIdx == -1) nextIdx = tr.length
      res.push(tr.slice(idx, nextIdx))
      idx = nextIdx + 1
    }
    return res
  }

  function goTerm(tr: syntax, ctx: Ctx, ty?: string): string{
    if (typeof tr == "string") {
      if (!ctx.includes(tr)) {
        if (book.has(tr)) return `book("${tr}")`
        raise(`unbound identifier: ${tr}`)
      }
      return tr
    }

    if (Array.isArray(tr)) {
      if (tr[0] == "match") {
        return `({
          $: "match",
          scr: ${goTerm(tr[1], ctx)},
          ty: ${ty},
          srcs: [${splitList(tr, "|").slice(1).map(arm => {
            let [pat, expr] = splitList(arm, "=>")
            if (typeof pat == "string") pat = [pat]
            for (let p of pat) if (typeof p != "string") raise(`expected a string in the pattern, but got: ${JSON.stringify(p)}`)
            return `{length: ${pat.length}, names: [${pat.map(x=>`"${x}"`)}], f: (${pat.join(", ")})=>${goTerm(expr, [...ctx, ...pat as string[]])}}`
          }).join(", ")}]
        })`
      }

      if (tr[0] == "|") return `({$: "ADT", ty: Type, variants: [${splitList(tr.slice(1), "|").map(x=> asSign(x[0], ctx)).map(vr => mkSign(vr)).join(", ")}]})`

      if (tr[1] == "->") {
        let args = asSign(tr[0], ctx)
        return mkarrow(args, goTerm(tr.slice(2), ctx.concat(args.map(a => a.name))))
      }

      if (Array.isArray(tr[0]) && tr[0].includes("=")){
        let letr = tr[0]
        let vname = asIden(letr[0])
        if (letr[1] != ":") raise(`expected a ":" after the let binding, but got: ${JSON.stringify(tr[1])}`)
        let vtype = goTerm(letr[2], ctx)
        if (letr[3] != "=") raise(`expected a "=" after the type annotation in the let binding, but got: ${JSON.stringify(tr[3])}`)
        return `(${vname} => ${goTerm(tr.slice(1), ctx.concat([vname]))})(${ goTerm(letr[4], ctx, vtype)})`
      }

      if (tr.includes("=>")){
        if (tr[1]!=":") raise(`expected a ":" after the argument list in the lambda, but got: ${JSON.stringify(tr[1])}`)
        if (tr[3] != "=>") raise(`expected a "=>" after the return type in the lambda, but got: ${JSON.stringify(tr[3])}`)
        return mkLam(tr[0], tr[2], tr.slice(4), ctx)
      }

      if (typeof tr[0] == "string" && tr[0].startsWith("#")){
        let idx = parseInt(tr[0].slice(1))
        if (isNaN(idx)) raise(`expected a numeric index after "#", but got: ${tr[0].slice(1)}`)
        if (ty == undefined) raise(`expected a type for the contructor`)
        return `({$:"adt", tag: ${idx}, srcs: [${tr.slice(1).map(x=>goTerm(x, ctx))}], ty: ${ty}})`
      }

      if (tr.length == 1) return goTerm(tr[0], ctx, ty)
      return `$( ${tr.map(x=>goTerm(x, ctx)).join(", ")} )`
    }
    raise(`expected a term, but got: ${JSON.stringify(tr)}`)
  }

  function mkSign(args: annot[]): string{
    return `[${args.map((a,i)=> `{name: "${a.name}", live: ${a.live}, f: (${args.slice(0,i).map(x=>x.name)}) => ${a.ty}}`)}]`
  }

  function mkarrow(dom: annot[], cod: string): string{
    return `({ty: Type, $: "Arrow", s: ${mkSign(dom.concat([{name: "out", live: true, ty: cod}]))}})`
  }

  function mkLam(args: syntax, r: syntax, bod: syntax, ctx: Ctx) : string {
    let vars = asSign(args, ctx)
    let names = vars.map(a=>a.name)
    ctx = ctx.concat(names)
    let R = goTerm(r, ctx)
    return `({ $: "Lam", ty: ${mkarrow(vars, R)}, fn: { names: ${JSON.stringify(names)}, f: (${names})=> ${goTerm(bod, ctx, R)} } })`
  }

  let ctx :Ctx = []
  let obj = {} as Term
  if (typeof tr == "string") raise(`unexpected string term at top level: ${tr}`)

  let name = asIden(tr[0])
  if (book.has(name)) raise(`Name already defined: ${name}`)

  let code = ""
  if (Array.isArray(tr[1])){
    book.set(name, obj)
    if (tr[2] != ":") raise(`expected a ":" after the argument list, but got: ${JSON.stringify(tr[2])}`)
    if (tr[4] != "=") raise(`expected a "=" after the return type, but got: ${JSON.stringify(tr[4])}`)
    code = mkLam(tr[1], tr[3], tr.slice(5), ctx)
  } else if (tr[1] == ":"){
    let ty = goTerm(tr[2], ctx)
    if (tr[2] == "Type" || tr[2] == "Data") book.set(name,obj)
    code = `({...${goTerm(tr.slice(4), ctx, ty)}, ty: ${ty} })`
  }else raise(`unexpected syntactic form: ${JSON.stringify(tr)}`)

  let Ctx = { book: (s:string)=>book.get(s), $, obj, Type }
  Function(...Object.keys(Ctx),"check", `Object.assign(obj, ${code})`)(...Object.values(Ctx), check)
  book.set(name,obj)
  check(obj)
  names.set(obj, name)
  if (!name.startsWith("_")) console.info(`✓${name} ${fmt(obj, true)}`)
  return obj
}

function decline(s: string){
  try{ compile(s)}
  catch(e){return}
  raise(`expected compilation to fail for: ${s}`)
}

compile("(NULL : Data = | () )")
compile("(Null : NULL = (#0 ) )")

compile("(BOOL : Data = | () | () )")
compile("(True : BOOL = (#1 ) )")
compile("(False : BOOL = (#0 ) )")

compile("(_type_identity (x:Type) : Type = x)")
compile("(_bool_identity (x:BOOL) : BOOL = match x | => x | => x)")
compile("(_bool_rebuild (x:BOOL) : BOOL = match x | => True | => False)")
decline("(_bad_bool_branch_right (x:BOOL) : BOOL = match x | => True | => NULL)")
decline("(_bad_bool_branch_left (x:BOOL) : BOOL = match x | => NULL | => True)")

compile("(TF (x:BOOL) : Type = match x | => NULL | => BOOL)")
compile("(_tfm (x:BOOL) : (TF x) = match x | => Null | => True)")

compile("(SIG : Type = | (w: BOOL, y: (TF w) ) )")
compile("(_sig1 : SIG = (#0 True True) ) ")
decline("(_sig_missing_field : SIG = (#0 True) )")
decline("(_sig_bad_true_payload : SIG = (#0 True Null) )")
decline("(_sig_bad_false_payload : SIG = (#0 False True) )")
compile("(_sig_false_null : SIG = (#0 False Null) )")

compile("(WRP (T: Type): Type = | (x: T) )")
compile("(_wrp_bool : (WRP BOOL) = (#0 True) )")
decline("(_bad_wrp_null : (WRP NULL) = (#0 True) )")

compile("(Nat: Data = | () | (p: Nat) )")
compile("(Zero : Nat = (#0 ) )")
compile("(S (n: Nat) : Nat = (#1 n) )")
compile("(pred (n: Nat) : Nat = match n | => Zero | p => p )")

compile("(eater (n: Nat): Nat = match n | => Zero | p => (eater p) )")
compile("(n0 : Nat = Zero)")
compile("(n1 : Nat = (S Zero) )")
compile("(n2 : Nat = (S (S Zero ))  )")
compile("(aro : Type = (x: Nat) -> Nat )")

decline("(NDT : Nat = Type)")
decline("(_bad_data_type : Data = Type)")
compile("(TID : Data = Nat)")
compile("(DID : Type = Type)")
compile("(_uu : aro = pred )")

compile(`( _oneof_nat (n: Nat) : (| ( x : Nat )  | ( y : BOOL ) ) = (#0 n) ) ` )
decline(`( _bad_oneof_bool (n: Nat) : (| ( x : Nat )  | ( y : BOOL ) ) = (#1 n) ) ` )
compile(`( _typeid (T: Type) :Type = T)`)
compile(`( _dataid (T: Data) :Data = T)`)
decline(`( _typeup (T: Type) :Data = T)`)
compile(`( _dataup (T: Data) :Type = T)`)
compile(`( _intersection (t: Data, x: t) : (|(a: t, b: t)) = (#0 x x))`)
decline(`( _notaffine (t: Type, x: t) : (|(a: t, b: t)) = (#0 x x))`)


/**
 * Equality is defined as proof of (P a) -> (P b) for all P, a, b
 * transitivity and symmetry can be derived
 * rfl is an AXIOM, saying for all x : x == x
 */

let EQ  = compile("(EQ (-T: Type, -a: T, -b: T) : Type = (Pr: ( (x:T)->Type), h: (Pr a) ) ->  (Pr b) )")
let RFL = compile("(RFL: Type = (-T: Type, -x: T) -> (EQ T x x) )")
rfl.ty = RFL


compile("(_pp : (EQ  Nat (pred n1) Zero ) = (rfl Nat Zero) ) ")
compile("(_ppe : (EQ  Nat (eater n2) Zero ) = (rfl Nat Zero) ) ")
decline("(_ppne : (EQ  Nat (pred n2) Zero ) = (rfl Nat Zero) )")

compile(`(pr0 (n: Nat ) : (EQ Nat Zero Zero) =  match n | => (rfl Nat n) | p => (rfl Nat Zero) ) `)

compile (" (NPred : Type = (n: Nat) -> Type )")

compile(`(_apply_predicate (n: Nat, P:NPred, h: ((x: Nat) -> (P x))) : (P n) =  (h n) ) `)
decline(`(_bad_apply_zero (n: Nat, P:NPred, h: ((x: Nat) -> (P x))) : (P n) =  (h Zero) ) `)

compile(`(_apply_predicate_match (n: Nat, P:NPred, h: ((x: Nat) -> (P x))) : (P n) = match n | => (h n) | p => (h n) ) `)
decline(`(_bad_apply_predecessor (n: Nat, P:NPred, h: ((x: Nat) -> (P x))) : (P n) = match n | => (h n) | p => (h p) ) `)

compile(`(isZ (n: Nat) : Type = (EQ Nat Zero n))`)
compile("(_eater_is_zero_type (n: Nat) : Type = (isZ (eater n))) ")

compile("(eater_n_eq (n: Nat): (EQ Nat (eater n) (eater (S n)) ) = (rfl Nat (eater n)) )")

decline("(_bad_eater_proof (n: Nat): (EQ Nat (eater n) (eater (S n)) ) = (rfl Nat (pred n)) )")
decline("(_bad_zero_one_proof (n: Nat): (EQ Nat Zero n1) = (rfl Nat Zero)")
compile(`(_eater_proof (n: Nat ) : ( EQ Nat (eater n) (eater (S n) ) ) = ( eater_n_eq n ) )`)

compile(`(eater_0 (n: Nat) : (isZ (eater n)) =  match n | => (rfl Nat Zero) | p => ((eater_n_eq p) isZ (eater_0 p)) )`)

compile(`(_cloj (x: Nat) : Nat = (y : Nat = Zero) y)`)
compile(`(_cloj2 : ((x:Nat) -> Nat ) = (x: Nat): Nat => x)`)

compile(`( EQ.tran (T: Type, a: T, b: T, c: T, e1: (EQ T a b), e2: (EQ T b c)) : (EQ T a c) = (e2 ((x: T) : Type => (EQ T a x)) e1) )`)

compile(`(_type_arrow (T: Type) : Type = (x: T) -> T)`)

decline(`(_bad_duplicate_type (T: Type, P: ((a:Type, b: Type)-> Type ) ) : Type = (P T T))`)
decline(`(_bad_use_dead_type (-T: Type, P: ((a:Type, b: Type)-> Type ) ) : Type = (P T T))`)

compile(`(_use2Nat (x: Nat, P: ((a: Nat, b: Nat) -> Type)) : Type = (P x x))`)
decline(`( _death (-x:Nat) : Nat = x)`)

compile(`(N2N : Type = ((x:Nat) -> Nat))`)
decline(`(_aroData : Data = ((x:Nat) -> Nat))`)

decline(`(eAdt : Data = | (x: N2N))`)
compile(`(tAdt : Type = | (x: N2N))`)
compile(`(_gAdt : Data = | (x: Nat))`)

decline(`(_bad_duplicate_tadt (x: tAdt) : (| (x: tAdt, y: tAdt))  = (#0 x x))`)
compile(`(_use_tadt_once (x: tAdt) : (| (x: tAdt, y: Nat))  = (#0 x n0))`)

compile(`(_usedeadT (-T: Type, x: T) : T = x)`)

compile(`(_call_dead_type (x:Nat): Nat = (_usedeadT Nat x))`)
decline(`(_bad_call_dead_type (x:Nat): Nat = (_usedeadT BOOL x))`)


compile(`(_passDead(-T: Type, -x:T, f: ((-x:T)->T) ) : T = (f x) )`)

compile(`(_erlf (-T: Type, x: T) : (EQ T x x) = (rfl T  x))`)


compile(`( Empty : Type = | )`)
compile(`( K : Type = (-x: K) -> Empty)`)
compile(`( Kp (xt: K) : Empty = (xt xt) )`)

decline(`( ep: Empty = (Kp Kp) )`)
decline(`( _bad_Kp_dead (-xt: K) : Empty = (xt xt) )`)

compile(`( Kl  : Type = (x: Kl) -> Empty)`)
decline(`( _bad_Kl_self_apply (xt: Kl)  : Empty = (xt xt))`)
decline(`( _bad_Kl_dead_self_apply (-xt: Kl) : Empty = (xt xt))`)
compile(`( Kl_identity (xt: Kl) : Kl = xt)`)
compile(`( Kl_apply (xt: Kl, yt: Kl) : Empty = (xt yt))`)
decline(`( _bad_Kl_apply_dead (xt: Kl, -yt: Kl) : Empty = (xt yt))`)

compile(`( EQ.symm (-T: Type, a: T, b: T, e: (EQ T a b)) : (EQ T b a) =
  (e
    ((x: T) : Type => (EQ T x a))
    (rfl T a)
  )
)`)


compile(`( + (n: Nat, m: Nat) : Nat =
  match n
    | => m
    | p => (S (+ p m))
)`)


compile(`(== (n: Nat, m: Nat) : Type = (EQ Nat n m))`)

compile( `(
  congruence (
    T: Type,
    U : Type,
    a: T,
    b: T,
    f: ((x:T) -> U),
    e: (EQ T a b)
  ) : (EQ U (f a) (f b))
  =
  (e
    ((x: T) : Type => (EQ U (f a) (f x)))
    (rfl U (f a))
  )
)`)

compile(`( add.succ.0 (n: Nat, k: Nat) : (== (+ (S n) k) (S (+ n k) )) = (rfl Nat (+ (S n) k)) )`)
compile(`( add.0.step (n: Nat, h: (== (+ n n0) n) )
  : (==  (+ (S n) n0) (S n) )
  = (congruence Nat Nat (+ n n0) n S h)
)`)

compile(`( add.0 (n: Nat) : (== (+ n n0) n) =
  match n
    | => (rfl Nat n0)
    | p => (add.0.step p (add.0 p) )
)`)

compile(`( add.0.symm (n: Nat) : (== n (+ n n0)) = ( EQ.symm Nat (+ n n0) n (add.0 n) ) )`)
compile(`(add.succ.p (n: Nat) : (== (S n) (+ n n1)) = match n
  | => (rfl Nat n1)
  | p =>(congruence Nat Nat (S p) (+ p n1) S (add.succ.p p))  )`)

compile(`( add.succ (n: Nat, m: Nat) : (== (S (+ n m)) (+ n (S m)) ) =
  match n
    | => (rfl Nat (S m))
    | p => (congruence Nat Nat (S (+ p m)) (+ p (S m)) S (add.succ p m))
)`)

compile(`( add.comm (n: Nat, m: Nat) : (== (+ n m) (+ m n)) =
  match n
    | => (add.0.symm m)
    | p => (EQ.tran Nat
      (S (+ p m))
      (S (+ m p))
      (+ m (S p))
      (congruence Nat Nat (+ p m) (+ m p) S (add.comm p m))
      (add.succ m p))
)`)


compile(`( AND (A: Type, B: Type) : Type  = | (a: A, b: B))`)

compile(`( _f (T: Type, P: ((x:Type) -> Type), a: (P T) ) : (P T) = a )`)

compile(`(
  BadM (m: Nat) : Type =
    match m
      | => NULL
      | q => Empty
)`)

compile(`(
  BadTy (n: Nat, m: Nat) : Type =
    match n
      | => (BadM m)
      | p => Empty
)`)

decline(`(
  badRec (n: Nat, m: Nat) : (BadTy n m) =
    match n
      | => (
          match m
            | => Null
            | q => (badRec (S q) q)
        )
      | p => (
          match p
            | => (badRec p (S p))
            | r => (badRec p (S p))
        )
)`)

decline(`(_badbad : Empty = _badbad)`)

compile(`(Fam (n: Nat) : Type = NULL)`)

compile(`(
  witness (n: Nat) : (Fam n) =
    Null
)`)

decline(`(Fam (n: Nat) : Type = Empty)`)

decline(`(
  _bad_empty_rebind : Empty =
    (witness Zero)
)`)

compile(`( DeadBox (T: Type) : Type = | (-x: T) )`)
compile(`( LiveBox (T: Type) : Type = | (x: T) )`)
compile(`( mkDead (-T : Type, -x: T) : (DeadBox T) = (#0 x))`)
decline(`( castBox (-T: Type, b: (DeadBox T)) : (LiveBox T) = b )`)
decline(`( fromrfl : Empty = rfl )`)
decline(`( fromrfl (x:Nat): Empty = rfl )`)
decline(`(false_arrow : Empty = (x: NULL) -> NULL)`)
decline(`(false_adt : Empty = |)`)

decline(`(boom (n: Nat) : Empty = sorry)`)
compile(`(badID (n: Null) : Null = n)`)


