(Error as any).stackTraceLimit = Infinity

export type F        = {names: string[], f: (...t: Term[]) => Term}
type ArgT            = {name:string, live:boolean, f: (...x:Term[]) => Term } 

export type Sign     = ArgT[]
export type Type     = { ty: Type,  $: "Uni",       Quant : 0}
export type Arrow    = { ty: Type,  $: "Arrow",     s: Sign }
export type ADT      = { ty: Term,  $: "ADT",       variants: Sign[]}
export type adt      = { ty: Term,  $: "adt",       tag: number, srcs: Term[] }
export type match    = { ty: Term,  $: "match",     scr: Term, srcs: F[] }
export type APP      = { ty: Term,  $: "APP",       fn: Term, args: Term[] }
export type Lam      = { ty: Term,  $: "Lam",       fn: F}
export type SYM      = { ty: Term,  $: "SYM",       name?: string, live: boolean }

export type Term = Type | { ty: Type,  $: "Uni", Quant : 1} | Arrow | ADT | adt | match | APP | Lam | SYM

export const Type = {$: "Uni", Quant: 0} as Type
Type.ty = Type
export const Data : Term = {$: "Uni", Quant: 1, ty: Type}

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

let book = new Map(Object.entries({Type, Data, sorry}))
let names = new Map(Array.from(book.entries()).map(([k, v]) => [v, k]))

export function fmt(t: Term, def?: boolean){
  function pln(t:Term, def? : boolean):string{

    if (names.has(t) && !def) return names.get(t)!
    if (t.$ == "Uni") return `type${t.Quant}`
    if (t.$ == "ADT") return t.variants.map(v=> `\n  | (${ fillSign(v).map(v =>  (v.live ? "" : "-") + pln(v)+": "+ pln(v.ty)).join(', ')})`).join('')
    if (t.$ == "adt") return `#${t.tag}(${t.srcs.map(x=> pln(x)).join(', ')})`
    if (t.$ == "APP") return `${pln(t.fn)}(${ t.args.map(x => pln(x)).join(', ')})`
    if (t.$ == "Arrow"){
      let ff = fillArrow(t)
      return `(${ff.args.map(v => `${pln(v)} : ${pln(v.ty)}`).join(', ')}) -> ${pln(ff.ret)}`
    }
    if (t.$ == "SYM") return t.name ?? "?"
    if (t.$ == "match") {
      return `match ${pln(t.scr)}:${t.srcs.map((f,i)=> `\n | ${f.names} => ${pln(f.f(...fillSign(asTag(t.scr.ty, "ADT").variants[i])))}`
      ).join('')}`
    }
    if (t.$ == "Lam") {
      if (t.ty && t.ty.$ == "Arrow"){
        let ars = fillArrow(t.ty)
        return `(${ars.args.map(v => `${(v.live ? "" : "-") +pln(v)} : ${pln(v.ty)}`).join(', ')}):${pln(ars.ret)} => ${pln(t.fn.f(...ars.args))}`
      }
      return `<|${t.fn.toString()}|>`
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
    if(a.length != b.length) raise(`Structural mismatch: ${a.length} vs ${b.length}`)
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
  if (a.$ == "Uni"){ if (a.Quant != (b as Type).Quant) raise(`Structural mismatch: ${fmt(a)} vs ${fmt(b)}`) }
  if (a.$ == "Lam" || a.$ == "SYM") raise(`Structural mismatch: ${fmt(a)} vs ${fmt(b)}`)
}

function asTag <$ extends Term["$"]>(t: Term | undefined, tag: $) : Term & {$: $}{
  if (!t) raise(`Expected tag ${tag}, got undefined`)
  t = run(t)
  if (t.$ != tag) raise(`Expected tag ${tag}, got ${t.$} in term ${fmt(t)}`)
  return t as Term & {$: $}
}

let checked = new Set<Term> ([Type])
type CallStack = { f: Term, args: Term[]} []

function check(t:Term){

  function checkSig(args: Term[], sig: Sign, live: boolean, cs: CallStack, used: SYM[]) : SYM[]{
    if (args.length != sig.length) raise(`Arity mismatch: expected ${sig.length} arguments, got ${args.length}`)
    zip(args, sig, (arg, slot,i)=>{
      let nus = go(arg, cs, used, slot.f(...args.slice(0,i)), live && slot.live)
      if (live && slot.live) used = nus
    })
    return used
  }

  function go(t:Term, cs: CallStack, used: SYM[], ty:Term | undefined, live : boolean) : SYM[]{

    function raise(msg: string): never{ throw new Error(msg) }

    if (t == sorry) raise(`Sorry: ${fmt(ty ?? sorry)}`)

    if (ty && t.ty) {
      if (ty.$ == "Uni" && ty.Quant == 0 && t.ty.$ == "Uni" && t.ty.Quant == 1) {}
      else checkEQ(t.ty, ty)
    }
    if (!t.$) raise(`Unexpected term with tag ${t}: ${fmt(t)}`)
    if (checked.has(t)) return used
    let type = t.ty
    if (!type) { raise(`Cannot infer type for term ${fmt(t)}`) }

    go(type, cs, used, Type, false)
    if (!type.ty) raise(`Cannot infer type for term ${fmt(t)}`)

    if (t.$ == "Uni"){
      if (asTag(t.ty, "Uni").Quant != 0) raise(`Expected Uni Type, got ${fmt(t.ty)}`)
    } else if (t.$ == "match"){
      let arg = t.scr //asTag(t.scr, "SYM")
      let T = asTag(arg.ty, "ADT")
      let old : Term = {...arg}
      let newuses: SYM[] = go(arg, cs, used, arg.ty, live)
      zip(T.variants, t.srcs, (v, s, i)=>{
        let vs = fillSign( v)
        Object.assign(arg,{$:"adt", tag: i, ty: T, srcs: vs})
        newuses.push(... go(s.f(...vs), cs, used, type, live).filter(x=>![...newuses, ...vs].includes(x)))
      })
      Object.assign(arg, old)
      used = newuses
    } else if (t.$ == "SYM"){
      if (live && t.live) { if (type.ty != Data && used.includes(t)) raise(`Symbol ${fmt(t)} already used: ${fmt(t)} ty ty: ${fmt(type.ty)}`) }
      else{ if (live) raise(`Symbol ${fmt(t)} is not live`) }
      if (live) used = [...used, t]

    } else if (t.$ == "adt"){
      let vari = asTag(type, "ADT").variants[t.tag]
      if (t.srcs.length != vari.length) raise(`invalid constructor args for ${fmt(type)}: [${t.srcs.map(x=>fmt(x))}]`)
      return checkSig(t.srcs, vari, live, cs, used)

    } else if (t.$ == "Lam"){
      if (cs.find(x=>x.f == t)) raise(`Non well-founded lambda detected`)
      let {args, ret} = fillArrow(asTag(t.ty, "Arrow"))
      return go(t.fn.f(...args), [...cs, { f: t, args }], used, ret, true).filter(x=> !args.includes(x))

    } else if (t.$ == "APP"){
      let REC = cs.find(x=>x.f == t.fn)
      let aro = asTag(t.fn.ty, "Arrow")
      used = checkSig(t.args, aro.s.slice(0, -1), live, cs, used)
      checkEQ(type, aro.s[aro.s.length - 1].f(...t.args))
      if (REC){
        let pairs = zip(REC.args, t.args, (x,y)=>[x,y])
        let WF = pairs.findIndex(([A, a]) => (A.$ == "adt" && A.srcs.some(el => el == a)))
        if (WF == -1 || pairs .slice(0,WF).some(([A, a]) => A!=a)) raise(`Non well-founded application detected: ${fmt(t)}`)
      }
      else return go(t.fn, cs, used, aro, live)

    } else if (t.$ == "Arrow"){
      if (asTag(type, "Uni").Quant == 1) raise(`Cannot construct Arrow of a universally quantified type`)
      if (cs.every(x=>x.f != t)) fillSign(t.s).forEach(x=> go(x.ty, [...cs, {f: t, args: []}], used, Type, false))

    } else if (t.$ == "ADT"){
      if (cs.every(x=>x.f != t) && asTag(type, "Uni").Quant == 1)
        for(let v of t.variants)
          for (let s of fillSign(v)) go(s.ty, [...cs, {f: t, args: []}], used, Data, true)
    }
    return used
  }
  go(t, [], [], undefined, true)
  checked.add(t)
}

type syntax = string | syntax []

function compile(s: string) {

  const toks = `(${s})`.split("\n").map(l => l.trim()).filter(l => !l.startsWith("//"))
    .join("\n").match(/->|=>|[():;,|+\-]|(?:=(?!>)|[^()\s:,|+\-=])+/g) ?? []

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
  type Ctx = [string, Term][]

  function asIden(tr: syntax): string{
    if (typeof tr != "string") raise(`expected an identifier, but got: ${JSON.stringify(tr)}`)
    return tr
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

  function mkFunc(tr: syntax, ty: undefined |((...x:Term[])=>Term), args: string[], ctx: Ctx): (...x:Term[]) => Term{
    return (...x) => asTerm(tr, ty?.(...x), [...ctx, ...x.map((v,i)=>["$"+args[i], v]) as Ctx])
  }
  
  function asAnnot(tr: syntax, args: string[], ctx: Ctx): ArgT{
    let live = tr[0]!= "-"
    if (!live) tr = tr.slice(1)
    if (tr[1] != ":") raise(`expected a ":" in annotation, but got: ${JSON.stringify(tr[1])}`)
    let f = mkFunc(tr.slice(2), ()=>Type, args, ctx)
    return {name:asIden(tr[0]), live, f}
  }

  function asLet(tr: syntax, ty: Term| undefined, ctx: Ctx){
    let mkLet = (offs:number, type?: Term) =>({n: "$" + asIden(tr[0]), v: {...asTerm(tr[offs], type, ctx), ...(type?{ ty: type} : {})} as Term, r: tr.slice(1+offs) })
    if (tr[1] == "=") return mkLet(2)
    return mkLet(tr.indexOf("=")+1, asTerm(tr.slice(2, tr.indexOf("=")), Type, ctx))
  }

  function asTerm(tr: syntax, ty: Term | undefined, ctx: Ctx): Term{
    function asSign(tr: syntax[]): Sign{
      return tr.reduce((acc,x)=> acc.concat(asAnnot(x, acc.map(x=>x.name), ctx)) , [] as Sign)
    }
    if (typeof tr == "string") {
      for (let i = ctx.length - 1; i >= 0; i--) if (ctx[i][0] === "$"+tr) return ctx[i][1]
      raise(`identifier not found in context: ${tr}`)
    }
    if (tr[0] == "|" && tr.length == 1) return {$:"ADT", variants:[], ty: ty ?? Type}
    if (tr.length == 1) return asTerm(tr[0], ty, ctx)
    if (tr[0] == "match"){
      if (!ty) raise(`expected type annotation for match expression`)
      return {$:"match", scr: asTerm(tr[1], undefined, ctx), ty, srcs: splitList(tr.slice(3), "|").map(x=>{
        if (!Array.isArray(x) || !x.includes("=>")) raise(`expected "=>" in match branch, but got: ${JSON.stringify(x)}`)
        let names = x.slice(0, x.indexOf("=>")).map(x=>asIden(x))
        return {names, f: mkFunc(x.slice(x.indexOf("=>")+1), ()=>ty, names, ctx)} as F
      })}
    }

    if (typeof tr[0] == "string" && (tr[1] == "=" || tr[1] == ":")){
      let dat = asLet(tr, ty, ctx)
      return asTerm(dat.r, ty, [...ctx, [dat.n, dat.v]])
    }

    if (tr.includes("=>")){
      let args = asSign(splitList(tr[0], ","))
      let names = args.map(x=>x.name)
      let fnf = (f: (...xs:Term[]) => Term, R: ArgT) : Lam => ( {$:"Lam", fn: {names, f}, ty: {$:"Arrow", s: args.concat([R]), ty:Type}})
      if (tr[1] == ":"){
        let R = asAnnot(["_",":", tr.slice(2,tr.indexOf("=>"))],names, ctx)
        return fnf(mkFunc(tr.slice(tr.indexOf("=>")+1), R.f, names, ctx), R)
      }
      let f = mkFunc(tr.slice(2), undefined, names, ctx)
      return fnf(f, {name: "_", live: true, f: (...xs: Term[])=> f(...xs).ty})
    }

    if (tr.includes("->")){
      if (tr[1] != "->") raise(`expected "->" in function type, but got: ${JSON.stringify(tr[1])}`)
      return {$:"Arrow", s:asSign(splitList(tr[0], ",").concat([["_", ":", tr.slice(2)]])), ty: Type}
    }

    if (tr[0] == "|") return {$:"ADT", variants:splitList(tr.slice(1), "|").map(x=>asSign(splitList(x[0], ","))), ty : ty ?? Type }

    if (tr.length > 1 && Array.isArray(tr[tr.length - 1])){
      let parseArgs = (sig: Sign) => splitList(tr[tr.length - 1], ",").reduce((acc,x,i)=> acc.concat(asTerm(x, sig[i].f(...acc), ctx)) , [] as Term[])
      if (tr.length == 2 && typeof tr[0] == "string" && tr[0].startsWith("#")){
        if (!ty) raise(`expected type annotation for data constructor: ${tr[0]}`)
        let tag = parseInt((tr[0] as string).slice(1))
        if (Number.isNaN(tag)) raise(`invalid data constructor tag: ${tr[0]}`)
        return {$:"adt", tag, ty, srcs: parseArgs(asTag(ty, "ADT").variants[tag])}
      }
      let fn = asTerm(tr.slice(0,-1), undefined, ctx)
      let sig = asTag(run(fn.ty), "Arrow").s
      let args = parseArgs(sig)
      return {$:"APP", fn, args, ty: sig[args.length].f(...args)}
    }

    raise(`unexpected syntactic form: ${JSON.stringify(tr)}`)
  }

  let body = {} as Term
  let name = asIden(tr[0])
  names.set(body, name)
  let dat = asLet(tr, undefined, [...book.entries(), [name, body]].map(([k,v])=>["$"+k,v]) as Ctx)
  check(Object.assign(body, { ...dat.v, ty: dat.v.ty }))
  if (!name.startsWith("_")) console.log(name, "=", fmt(body, true))
  book.set(name, body)
}

function decline(s: string){
  try{ compile(s)}
  catch(e){return}
  raise(`expected compilation to fail for: ${s}`)
}

compile(`t : Type = ( Type )`)
compile(`aro : Type = ( (x: Type) -> Type )`)
compile(`atf = ( (x: Type) : Type => x )`)
compile(`aff = ( (x: Type) => x )`)
compile(`aa = ( ( f: ((t:Type) -> Type), t: Type) => f(t) )`)
compile(`Prop = ( (-T: Type) : Type => ((x:T)->Type) )`)
compile(`EQ  = ( (-T: Type, -a: T, -b: T) : Type => (P: Prop(T), h: P(a) ) ->  P(b)  )`)
compile(`rfl = ( ((-T: Type, x:T ) : EQ(T, x, x) => (P:Prop(T), h:P(x)) => h ) )`)
compile(`NULL : Data = ( | ()  )`)
compile(`Null : NULL = ( #0()  )`)
compile(`BOOL : Data = ( | () | ()  )`)
compile(`True : BOOL = ( #1()  )`)
compile(`False : BOOL = ( #0()  )`)
compile(`_type_identity = ( (x:Type) : Type => x )`)
compile(`_bool_identity = ( (x:BOOL) : BOOL => match x | => x | => x )`)
compile(`_bool_rebuild = ( (x:BOOL) : BOOL => match x | => True | => False )`)
decline(`_bad_bool_branch_right = ( (x:BOOL) : BOOL => match x | => True | => NULL )`)
decline(`_bad_bool_branch_left = ( (x:BOOL) : BOOL => match x | => NULL | => True )`)
compile(`TF = ( (x:BOOL) : Type => match x | => NULL | => BOOL )`)
compile(`_tfm = ( (x:BOOL) : TF(x) => match x | => Null | => True )`)
compile(`SIG : Type = ( | (w: BOOL, y: TF(w)) )`)
compile(`_sig1 : SIG = ( #0(True, True) )`)
decline(`_sig_missing_comma : SIG = ( #0(True True) )`)
decline(`_sig_missing_field : SIG = ( #0(True) )`)
decline(`_sig_bad_true_payload : SIG = ( #0(True, Null) )`)
decline(`_sig_bad_false_payload : SIG = ( #0(False, True) )`)
compile(`_sig_false_null : SIG = ( #0(False, Null) )`)
compile(`_app2 = ( (f :((x: Type) -> (y: Type) -> Type)) : Type => f(Type)(Type)  )`)
compile(`WRP = ( (T: Type) : Type => | (x: T) )`)
compile(`_wrp_bool : WRP(BOOL) = ( #0(True) )`)
decline(`_bad_wrp_null : WRP(NULL) = ( #0(True) )`)
compile(`Nat: Data = ( | () | (p: Nat)  )`)
compile(`Zero : Nat = ( #0()  )`)
compile(`letz = ( x = Zero x )`)
compile(`leta = ( x :Nat = Zero x )`)
compile(`S = ( (n: Nat) : Nat => #1(n) )`)
compile(`pred = ( (n: Nat) : Nat => match n | => Zero | p => p )`)
compile(`eater = ( (n: Nat) : Nat => match n | => Zero | p => eater(p) )`)
compile(`n0 : Nat = ( Zero )`)
compile(`n1 : Nat = ( S(Zero) )`)
compile(`n2 : Nat = ( S(S(Zero)) )`)
compile(`natArrow : Type = ( (x: Nat) -> Nat )`)
decline(`letNB = ( (a: NULL) : NULL => x : NULL = a match a | => Zero )`)
compile(`letNB = ( (a: NULL) : Nat => x : NULL = Null match a | => Zero )`)
decline(`NDT : Nat = ( Type )`)
decline(`_bad_data_type : Data = ( Type )`)
compile(`TID : Data = ( Nat )`)
compile(`DID : Type = ( Type )`)
compile(`_uu : natArrow = ( pred )`)
compile(`_oneof_nat = ( (n: Nat) : (| (x: Nat) | (y: BOOL)) => #0(n) )`)
decline(`_bad_oneof_bool = ( (n: Nat) : (| (x: Nat) | (y: BOOL)) => #1(n) )`)
compile(`_typeid = ( (T: Type) : Type => T )`)
compile(`_dataid = ( (T: Data) : Data => T )`)
decline(`_typeup = ( (T: Type) : Data => T )`)
compile(`_dataup = ( (T: Data) : Type => T )`)
compile(`_intersection = ( (t: Data, x: t) : (| (a: t, b: t)) => #0(x, x) )`)
decline(`_notaffine = ( (t: Type, x: t) : (| (a: t, b: t)) => #0(x, x) )`)
compile(`_inferLam : ((x: Nat) -> Nat) = ( (x: Nat) => x )`)
compile(`_pp : EQ(Nat, pred(n1), Zero) = ( rfl(Nat, Zero) )`)
compile(`_ppe : EQ(Nat, eater(n2), Zero) = ( rfl(Nat, Zero) )`)
decline(`_ppne : EQ(Nat, pred(n2), Zero) = ( rfl(Nat, Zero) )`)
compile(`pr0 = ( (n: Nat) : EQ(Nat, Zero, Zero) => match n | => rfl(Nat, n) | p => rfl(Nat, Zero) )`)
compile(`NPred : Type = ( (n: Nat) -> Type )`)
compile(`_apply_predicate = ( (n: Nat, P:NPred, h: ((x: Nat) -> P(x))) : P(n) => h(n) )`)
decline(`_bad_apply_zero = ( (n: Nat, P:NPred, h: ((x: Nat) -> P(x))) : P(n) => h(Zero) )`)
compile(`_apply_predicate_match = ( (n: Nat, P:NPred, h: ((x: Nat) -> P(x))) : P(n) => match n | => h(n) | p => h(n) )`)
decline(`_bad_apply_predecessor = ( (n: Nat, P:NPred, h: ((x: Nat) -> P(x))) : P(n) => match n | => h(n) | p => h(p) )`)
compile(`isZ = ( (n: Nat) : Type => EQ(Nat, Zero, n) )`)
compile(`_eater_is_zero_type = ( (n: Nat) : Type => isZ(eater(n)) )`)
compile(`eater_n_eq = ( (n: Nat) : EQ(Nat, eater(n), eater(S(n))) => rfl(Nat, eater(n)) )`)
decline(`_bad_eater_proof = ( (n: Nat) : EQ(Nat, eater(n), eater(S(n))) => rfl(Nat, pred(n)) )`)
decline(`_bad_zero_one_proof = ( (n: Nat) : EQ(Nat, Zero, n1) => rfl(Nat, Zero) )`)
compile(`_eater_proof = ( (n: Nat) : EQ(Nat, eater(n), eater(S(n))) => eater_n_eq(n) )`)
compile(`eater_0 = ( (n: Nat) : isZ(eater(n)) => match n | => rfl(Nat, Zero) | p => (eater_n_eq(p))(isZ, eater_0(p)) )`)
compile(`_cloj = ( (x: Nat) : Nat => (y : Nat = Zero y) )`)
compile(`_cloj2 : ((x:Nat) -> Nat) = ( (x: Nat): Nat => x )`)
compile(`EQ.tran = ( (T: Type, a: T, b: T, c: T, e1: EQ(T, a, b), e2: EQ(T, b, c)) : EQ(T, a, c) => e2(((x: T) : Type => EQ(T, a, x)), e1) )`)
compile(`_type_arrow = ( (T: Type) : Type => (x: T) -> T )`)
decline(`_bad_duplicate_type = ( (T: Type, P: ((a:Type, b: Type)-> Type)) : Type => P(T, T) )`)
decline(`_bad_use_dead_type = ( (-T: Type, P: ((a:Type, b: Type)-> Type)) : Type => P(T, T) )`)
compile(`_use2Nat = ( (x: Nat, P: ((a: Nat, b: Nat) -> Type)) : Type => P(x, x) )`)
decline(`_death = ( (-x:Nat) : Nat => x )`)
compile(`N2N : Type = ( (x:Nat) -> Nat )`)
decline(`_aroData : Data = ( (x:Nat) -> Nat )`)
decline(`eAdt : Data = ( | (x: N2N) )`)
compile(`tAdt : Type = ( | (x: N2N) )`)
compile(`_gAdt : Data = ( | (x: Nat) )`)
decline(`_bad_duplicate_tadt = ( (x: tAdt) : (| (x: tAdt, y: tAdt)) => #0(x, x) )`)
compile(`_use_tadt_once = ( (x: tAdt) : (| (x: tAdt, y: Nat)) => #0(x, n0) )`)
compile(`_usedeadT = ( (-T: Type, x: T) : T => x )`)
compile(`_call_dead_type = ( (x:Nat) : Nat => _usedeadT(Nat, x) )`)
decline(`_bad_call_dead_type = ( (x:Nat) : Nat => _usedeadT(BOOL, x) )`)
compile(`_passDead = ( (-T: Type, -x:T, f: ((-x:T)->T)) : T => f(x) )`)
compile(`_erlf = ( (-T: Type, x: T) : EQ(T, x, x) => rfl(T, x) )`)
compile(`Empty : Type = ( | )`)
compile(`K : Type = ( (-x: K) -> Empty )`)
compile(`Kp = ( (xt: K) : Empty => xt(xt) )`)
decline(`ep: Empty = ( Kp(Kp) )`)
decline(`_bad_Kp_dead = ( (-xt: K) : Empty => xt(xt) )`)
compile(`Kl : Type = ( (x: Kl) -> Empty )`)
decline(`_bad_Kl_self_apply = ( (xt: Kl) : Empty => xt(xt) )`)
decline(`_bad_Kl_dead_self_apply = ( (-xt: Kl) : Empty => xt(xt) )`)
compile(`Kl_identity = ( (xt: Kl) : Kl => xt )`)
compile(`Kl_apply = ( (xt: Kl, yt: Kl) : Empty => xt(yt) )`)
decline(`_bad_Kl_apply_dead = ( (xt: Kl, -yt: Kl) : Empty => xt(yt) )`)
decline(`emptyLoop = ( (): Empty => emptyLoop() )`)
compile(`EQ.symm = ( (-T: Type, a: T, b: T, e: EQ(T, a, b)) : EQ(T, b, a) => e(((x: T) => EQ(T, x, a)), rfl(T, a)) )`)
compile(`Empty3 : Type = ( | )`)
compile(`Unit3 : Data = ( | () )`)
compile(`unit3 : Unit3 = ( #0() )`)
compile(`undefined : Type = ( Empty3 )`)
compile(`bad3 = ( (x: undefined, T:Type) : Empty3 => x )`)
decline(`contradiction3 : Empty3 = ( bad3(unit3, Unit3) )`)
compile(`add = ( (n: Nat, m: Nat) : Nat => match n | => m | p => S(add(p, m)) )`)
decline(`_add_missing_comma = ( (n: Nat, m: Nat) : Nat => add(n m) )`)
compile(`eqn = ( (n: Nat, m: Nat) : Type => EQ(Nat, n, m) )`)
compile(`congruence = ( ( T: Type, U: Type, a: T, b: T, f: ((x:T) -> U), e: EQ(T, a, b))
  : EQ(U, f(a), f(b)) =>
  e(((x: T) : Type => EQ(U, f(a), f(x))), rfl(U, f(a))) )`)
compile(`add.succ.0 = ( (n: Nat, k: Nat) : (eqn(add(S(n), k), S(add(n, k)))) => rfl(Nat, add(S(n), k)) )`)
compile(`add.0.step = ( (n: Nat, h: eqn(add(n, n0), n)) : (eqn(add(S(n), n0), S(n))) =>
  congruence(Nat, Nat, add(n, n0), n, S, h) )`)
compile(`add.0 = ( (n: Nat) : (eqn(add(n, n0), n)) =>
  match n | => rfl(Nat, n0) | p => add.0.step(p, add.0(p)) )`)
compile(`add.0.symm = ( (n: Nat) : (eqn(n, add(n, n0))) => EQ.symm(Nat, add(n, n0), n, add.0(n)) )`)
compile(`add.succ.p = ( (n: Nat) : (eqn(S(n), add(n, n1))) => match n
  | => rfl(Nat, n1)
  | p => congruence(Nat, Nat, S(p), add(p, n1), S, add.succ.p(p)) )`)
compile(`add.succ = ( (n: Nat, m: Nat) : (eqn(S(add(n, m)), add(n, S(m)))) =>
  match n
    | => rfl(Nat, S(m))
    | p => congruence(Nat, Nat, S(add(p, m)), add(p, S(m)), S, add.succ(p, m)) )`)
compile(`add.comm = ( (n: Nat, m: Nat) : (eqn(add(n, m), add(m, n))) =>
  match n
    | => add.0.symm(m)
    | p => EQ.tran(Nat, S(add(p, m)), S(add(m, p)), add(m, S(p)),
        congruence(Nat, Nat, add(p, m), add(m, p), S, add.comm(p, m)), add.succ(m, p)) )`)
compile(`add.assoc = ( (n: Nat, m: Nat, k: Nat) : (eqn(add(n, add(m, k)), add(add(n, m), k))) =>
  match n
    | => rfl(Nat, add(m, k))
    | p => congruence(Nat, Nat, add(p, add(m, k)), add(add(p, m), k), S, add.assoc(p, m, k)) )`)
compile(`assoc.symm = ( (n: Nat, m: Nat, k: Nat) : (eqn(add(add(n, m), k), add(n, add(m, k)))) =>
  EQ.symm(Nat, add(n, add(m, k)), add(add(n, m), k), add.assoc(n, m, k)) )`)
compile(`mul = ( (n: Nat, m: Nat) : Nat => match n | => Zero | p => add(m, mul(p, m)) )`)
compile(`mul.0 = ( (m: Nat) : (eqn(n0, mul(m, n0))) => match m | => rfl(Nat, n0) | p => mul.0(p) )`)
compile(`congn = ( (a:Nat, b: Nat, f: ((x: Nat) -> Nat), e: eqn(a, b)) : (eqn(f(a), f(b))) =>
  congruence(Nat, Nat, a, b, f, e) )`)
compile(`add.swap = ( (a: Nat, b: Nat, c: Nat) : (eqn(add(a, add(b, c)), add(b, add(a, c)))) =>
  EQ.tran(Nat, add(a, add(b, c)), add(add(a, b), c), add(b, add(a, c)),
    add.assoc(a, b, c),
    EQ.tran(Nat, add(add(a, b), c), add(add(b, a), c), add(b, add(a, c)),
      congn(add(a, b), add(b, a), ((x:Nat):Nat => add(x, c)), add.comm(a, b)),
      EQ.symm(Nat, add(b, add(a, c)), add(add(b, a), c), add.assoc(b, a, c)))) )`)
compile(`mul.succ = ( (n: Nat, m: Nat) : (eqn(add(n, mul(n, m)), mul(n, S(m)))) =>
  match n
    | => rfl(Nat, Zero)
    | p => (pm : Nat = (mul(p, m))
      congn(add(p, add(m, pm)), add(m, mul(p, S(m))), S,
        EQ.tran(Nat, add(p, add(m, pm)), add(m, add(p, pm)), add(m, mul(p, S(m))),
          add.swap(p, m, pm),
          congn(add(p, pm), mul(p, S(m)), ((x:Nat):Nat => add(m, x)), mul.succ(p, m))))) )`)
compile(`mul.comm = ( (n:Nat, m: Nat) : (eqn(mul(n, m), mul(m, n))) =>
  match n
    | => mul.0(m)
    | p => EQ.tran(Nat, add(m, mul(p, m)), add(m, mul(m, p)), mul(m, n),
        congn(mul(p, m), mul(m, p), ((x:Nat):Nat => add(m, x)), mul.comm(p, m)), mul.succ(m, p)) )`)
compile(`addswap2 = ( (a: Nat, b: Nat, c: Nat, d: Nat)
  : (eqn(add(add(a, b), add(c, d)), add(add(a, c), add(b, d)))) =>
  P = ((x:Nat)=> eqn(add(add(a, b), add(c, d)) , x))
  (add.assoc(a, c, add(b, d))(P,
    add.swap(b,c,d)(
      (x:Nat)=>P(add(a,x)),
      assoc.symm(a,b, add(c,d))
    )
  )))`)
compile(`mul.dist = ( (a: Nat, b: Nat, c: Nat) : eqn(mul(a, add(b, c)), add(mul(a, b), mul(a, c))) =>
  match a
    | => rfl(Nat, n0)
    | p =>
        P = ((x: Nat) => eqn( mul(a, add(b,c)), x))
        h : (P(add(add(b,c), add(mul(p, b), mul(p, c))))) =
          (mul.dist(p,b,c)((x:Nat)=> P(add(add(b,c), x)), rfl(Nat, mul(a,add(b,c)))))
        addswap2(b,c, mul(p,b), mul(p,c))(P,h)
   )`)
compile(`Not = ( (A: Type) => ((x:A) -> Empty) )`)
compile(`ExF = ( (e: Empty, T: Type) : T => match e )`)
compile(`NEQ = ( (A: Type, x: A, y: A) => Not(EQ(A, x, y)) )`)
compile(`DEC = ( (P: Type) => (| (p: P) | (n: Not(P)) ) )`)
compile(`DEC.EQ = ( (A: Type, x: A, y: A) => DEC(EQ(A, x, y)) )`)
compile(`Nat.NEQ.0 = ( (n:Nat ) : NEQ(Nat, Zero, S(n)) =>
  P = ((x: Nat): Type => match x | => NULL | => Empty )
  ((e: eqn(Zero, S(n))) => e(P, Null))
) )`)
compile(`Nat.dec.step = ( (n: Nat, m: Nat, d: DEC.EQ(Nat, n, m) ) : DEC.EQ(Nat, S(n), S(m)) =>
  match d
    | e =>
      P = ((x:Nat) => EQ(Nat, S(n), S(x)))
      #0(e( P, rfl(Nat, S(n))))
    | ne => #1( (e: EQ(Nat, S(n), S(m))) =>  ne( congn(S(n), S(m), pred, e )) )  )`)
compile(`Nat.dec.eq = ( (n: Nat, m: Nat) : DEC(EQ(Nat, n, m)) =>
    match n
    | => ( match m
      | => #0(rfl(Nat, Zero))
      | q => #1(Nat.NEQ.0(q)) )
    | p => ( match m
        | => #1((e: EQ(Nat,n,m)) => Nat.NEQ.0(p)( EQ.symm(Nat,n,m,e) ) )
        | q => Nat.dec.step(p,q,Nat.dec.eq(p,q)) ) )`)
compile(`AND = ( (A: Type, B: Type) : Type => | (a: A, b: B) )`)
compile(`_f = ( (T: Type, P: (x:Type) -> Type, a: P(T)) : P(T)=> a )`)
compile(`BadM = ( (m: Nat) : Type => match m | => NULL | q => Empty )`)
compile(`BadTy = ( (n: Nat, m: Nat) : Type => match n | => BadM(m) | p => Empty )`)
decline(`badRec = ( (n: Nat, m: Nat) : BadTy(n, m) =>
  match n
    | => (match m | => Null | q => badRec(S(q), q))
    | p => (match p | => badRec(p, S(p)) | r => badRec(p, S(p))) )`)
decline(`_badbad : Empty = ( _badbad )`)
compile(`Fam = ( (n: Nat) : Type => NULL )`)
compile(`_weakening = ( (A:Type, B: Type, x: AND(A,B)): B => match x | a b => b )`)
compile(`_weakening = ( (A:Type, B: Type, x: |(_:A, _:B) ): B => match x | a b => b )`)
compile(`witness = ( (n: Nat) : (Fam(n)) => Null )`)
decline(`_bad_empty_rebind : Empty = ( witness(Zero) )`)
compile(`DeadBox = ( (T: Type) : Type => | (-x: T) )`)
compile(`LiveBox = ( (T: Type) : Type => | (x: T) )`)
compile(`mkDead = ( (-T: Type, -x: T) : (DeadBox(T)) => #0(x) )`)
decline(`castBox = ( (-T: Type, b: DeadBox(T)) : (LiveBox(T)) => b )`)
decline(`fromrfl : Empty = ( rfl )`)
decline(`fromrfl = ( (x:Nat) : Empty => rfl )`)
decline(`_false_arrow : Empty = ( (x: NULL) -> NULL )`)
decline(`_false_adt : Empty = ( | )`)
decline(`_boom = ( (n: Nat) : Empty => sorry )`)
compile(`_castNull = ( (x: NULL) : | () => x )`)
decline(`_castBad = ( (x: NULL) : | (x:Nat) => x )`)
decline(`_badTF = ( (x: NULL) : Data => (x:NULL) -> NULL )`)
decline(`D : Data = ( | (f: ((z: NULL): Data => (x: D) -> Empty)(Null)) )`)
compile(`Empty2 : Type = ( | )`)
compile(`R2 : Type = ( (x: R2) -> Empty2 )`)
compile(`Box2 : Type = ( | (-e: Empty2) )`)
decline(`badBox2 : Box2 = ( #0(d = ((x: R2): Empty2 => x(x)) d(d)) )`)
decline(`packBad = ( (f: Kl) : (((Type: Type): Type => | (f: Kl)))(Data) => #0(f) )`)
decline(`unpackBad = ( (b: ((Type: Type): Type => | (f: Kl)) (Data)) : Kl => match b | f => f )`)