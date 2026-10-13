/-
File: translator/Lean2Agda/Core/Print.lean
-/
import Lean2Agda.Core.Naming
import Lean2Agda.Core.InductiveShape
import Lean.Environment
import Lean.LocalContext

/-!
# The expression printer

Kernel expressions to Agda text under profile U, in two pure stages.  The
printer turns an `Expr` into a small Agda syntax tree, `AgdaTerm`, deciding
names, visibilities and projections; `AgdaTerm.render` lays the tree out as
text by a precedence table.  The rules and their reasons are in
`docs/translator/printing.md`.

A kernel application does not record the visibility of its arguments, so
the printer reads it from the type of the application's head.  When that
type is not syntactically a Pi type, the kernel's own `whnf` exposes one,
and when the head is neither a constant nor a bound variable, the kernel's
`check` infers its type.  Both are pure functions of the environment.  To
give them closed terms, the printer replaces each bound variable by a free
variable of its own, entered in a local context with the binder's type.
-/

namespace Lean2Agda

open Lean

/-! ## Agda terms and their layout -/

/-- Agda's three argument visibilities. -/
inductive Visibility where
  | explicit | implicit | instance
  deriving BEq, Repr, Inhabited

/-- Lean's strict implicit binders have no Agda counterpart; Agda's
implicit binders are the nearest.  Instance arguments stay instance
arguments, and the printer always passes them explicitly. -/
def Visibility.ofBinderInfo : BinderInfo → Visibility
  | .default => .explicit
  | .implicit | .strictImplicit => .implicit
  | .instImplicit => .instance

def Visibility.opening : Visibility → String
  | .explicit => "("
  | .implicit => "{"
  | .instance => "⦃ "

def Visibility.closing : Visibility → String
  | .explicit => ")"
  | .implicit => "}"
  | .instance => " ⦄"

/-- The Agda terms the printer produces.  `sort` is `Set`, the only sort
under profile U; a Pi type without a name is non-dependent; `field r f`
is Agda's projection `r.f` of field `f` from record `r`. -/
inductive AgdaTerm where
  | var (name : String)
  | const (name : String)
  | field (record name : String)
  | sort
  | nat (value : Nat)
  | str (value : String)
  | app (fn : AgdaTerm) (visibility : Visibility) (arg : AgdaTerm)
  | lam (visibility : Visibility) (name : String) (type body : AgdaTerm)
  | pi (visibility : Visibility) (name : Option String) (type body : AgdaTerm)
  | letE (name : String) (type value body : AgdaTerm)
  deriving BEq, Repr, Inhabited

/-- The precedence table: a binding form (`λ`, a Pi type, an arrow, `let`)
extends as far right as it can, so it binds loosest; application binds
tighter and associates to the left; atoms bind tightest.  A position asks
for a minimum, and a term below it is parenthesized: an application's head
asks for 1, an explicit argument for 2, an arrow's domain for 1, and every
position inside delimiters or to the right of an arrow asks for 0. -/
def AgdaTerm.prec : AgdaTerm → Nat
  | .lam .. | .pi .. | .letE .. => 0
  | .app .. => 1
  | _ => 2

/-- Agda's string literals take Haskell's escapes.  Everything outside
printable ASCII is written as a decimal escape closed by `\&`, so the
output does not depend on how a reader decodes Unicode. -/
def agdaStringLiteral (s : String) : String :=
  s.foldl (init := "\"") (fun out c =>
    if c == '"' then out ++ "\\\""
    else if c == '\\' then out ++ "\\\\"
    else if c.toNat < 0x20 || c.toNat > 0x7e then out ++ s!"\\{c.toNat}\\&"
    else out.push c) ++ "\""

/-- Append `t` to `out`, parenthesized when its precedence is below
`min`.  Threading one accumulator keeps the layout linear in its size. -/
def AgdaTerm.renderTo (out : String) (min : Nat) (t : AgdaTerm) : String :=
  let paren := t.prec < min
  let out := if paren then out ++ "(" else out
  let out := match t with
    | .var n | .const n => out ++ n
    | .field r f => out ++ r ++ "." ++ f
    | .sort => out ++ "Set"
    | .nat n => out ++ toString n
    | .str s => out ++ agdaStringLiteral s
    | .app f v a =>
      let out := f.renderTo out 1 ++ " "
      match v with
      | .explicit => a.renderTo out 2
      -- `{{` is Agda's ASCII instance brace, so an implicit argument that
      -- is itself an implicit Pi type, the one term that renders starting
      -- with `{`, is spaced away from the brace around it.
      | .implicit => match a with
        | .pi .implicit .. => a.renderTo (out ++ "{ ") 0 ++ " }"
        | _ => a.renderTo (out ++ "{") 0 ++ "}"
      | .instance => a.renderTo (out ++ "⦃ ") 0 ++ " ⦄"
    | .lam v x ty b =>
      b.renderTo (ty.renderTo (out ++ "λ " ++ v.opening ++ x ++ " : ") 0 ++ v.closing ++ " → ") 0
    | .pi .explicit none ty b => b.renderTo (ty.renderTo out 1 ++ " → ") 0
    | .pi v x ty b =>
      b.renderTo (ty.renderTo (out ++ v.opening ++ x.getD "_" ++ " : ") 0 ++ v.closing ++ " → ") 0
    | .letE x ty v b =>
      b.renderTo (v.renderTo (ty.renderTo (out ++ "let " ++ x ++ " : ") 0 ++ "; " ++ x ++ " = ") 0
        ++ " in ") 0
  if paren then out ++ ")" else out

def AgdaTerm.render (t : AgdaTerm) : String := t.renderTo "" 0

/-- The constants a printed term refers to, in order of first occurrence;
a field projection refers to its record. -/
def AgdaTerm.constants (t : AgdaTerm) : Array String :=
  go t #[]
where
  go : AgdaTerm → Array String → Array String
    | .const n, acc | .field n _, acc => if acc.contains n then acc else acc.push n
    | .app f _ a, acc => go a (go f acc)
    | .lam _ _ ty b, acc | .pi _ _ ty b, acc => go b (go ty acc)
    | .letE _ ty v b, acc => go b (go v (go ty acc))
    | _, acc => acc

/-! ## Names -/

/-- How constant references print.  Within one module every constant is
its `agdaIdent`; `Naming.qualified` prefixes the owner's module path to a
constant owned by another module, as `docs/translator/naming.md` says. -/
structure Naming where
  constant : Name → String

def Naming.unqualified : Naming := ⟨agdaIdent⟩

/-- `owner` gives the source module of a constant that another module
owns, and `none` for a constant of the module being printed. -/
def Naming.qualified (root : Root) (owner : Name → Option ModuleName) : Naming :=
  ⟨fun n => match owner n with
    | some m => ".".intercalate (agdaModule root m) ++ "." ++ agdaIdent n
    | none => agdaIdent n⟩

/-- Subscript decimal digits, `₀` to `₉`. -/
def subscript (n : Nat) : String :=
  (toString n).map fun d => Char.ofNat (0x2080 + (d.toNat - '0'.toNat))

/-- Greek letters other than `λ`, which Agda reserves. -/
def isGreekLetter (c : Char) : Bool :=
  let n := c.toNat
  ((0x391 ≤ n && n ≤ 0x3a9 && n != 0x3a2) || (0x3b1 ≤ n && n ≤ 0x3c9)) && c != 'λ'

/-- Agda reads each of these followed by subscript digits as a sort. -/
def sortBases : List String := ["Set", "Prop", "SSet", "Setω", "Propω", "SSetω"]

/-- The readable part of a binder name: the last string component of the
name with its macro scopes erased, keeping ASCII letters, digits and Greek
letters.  Kernel binder names are often hygienic, and Lean's own display
names carry marks such as `✝`; neither survives. -/
def binderBase (n : Name) : String :=
  let raw := match n.eraseMacroScopes with
    | .str _ s => s
    | _ => ""
  let kept := String.ofList (raw.toList.filter fun c =>
    isAsciiLetter c || c.isDigit || isGreekLetter c)
  if kept.isEmpty || kept.front.isDigit || sortBases.contains kept then "x" else kept

/-- A binder's Agda name is its base followed by the subscript decimal of
its depth, the number of binders enclosing it.  Binders in scope at once
have distinct depths, so their names differ; every binder name contains a
subscript digit and every constant identifier is ASCII, so no binder can
shadow a constant; and no keyword ends in a subscript digit, nor does a
sort name once the bases of `sortBases` are excluded. -/
def binderName (n : Name) (depth : Nat) : String := binderBase n ++ subscript depth

/-! ## Expressions to terms -/

/-- What the printer counts.  A repair is a lambda whose binder visibility
differs from the expected Pi type's, which Lean accepts and Agda refuses;
the printer prints the expected visibility.  At the top level the lambdas
are the leading ones of a definition's value, matched against its type;
deeper, they are lambdas checked against any other expected type: an
argument's binder type, a `let`'s type, or a lambda's codomain below the
top.  A projection prints as a record's field projection, or, from a
structure-like type that is not a record, through its recursor. -/
structure PrintCounts where
  topRepairs : Nat := 0
  deepRepairs : Nat := 0
  projections : Nat := 0
  fieldProjections : Nat := 0
  deriving BEq, Repr, Inhabited

def PrintCounts.add (a b : PrintCounts) : PrintCounts :=
  { topRepairs := a.topRepairs + b.topRepairs, deepRepairs := a.deepRepairs + b.deepRepairs,
    projections := a.projections + b.projections,
    fieldProjections := a.fieldProjections + b.fieldProjections }

structure Printer where
  env : Environment
  naming : Naming := .unqualified

abbrev PrintM := ReaderT Printer (StateT PrintCounts (Except String))

/-- The printer's local context: one free variable per enclosing binder,
whose user name is the binder's printed name. -/
structure Scope where
  lctx : LocalContext := {}
  depth : Nat := 0

def Scope.fvarId (depth : Nat) : FVarId := ⟨.num `_lean2agda depth⟩

def Scope.enter (s : Scope) (n : Name) (type : Expr) (bi : BinderInfo) : Scope × String × Expr :=
  let x := binderName n s.depth
  let id := Scope.fvarId s.depth
  ({ lctx := s.lctx.mkLocalDecl id (.mkSimple x) type bi, depth := s.depth + 1 }, x, .fvar id)

def Scope.enterLet (s : Scope) (n : Name) (type value : Expr) : Scope × String × Expr :=
  let x := binderName n s.depth
  let id := Scope.fvarId s.depth
  ({ lctx := s.lctx.mkLetDecl id (.mkSimple x) type value, depth := s.depth + 1 }, x, .fvar id)

def Scope.nameOf (s : Scope) (id : FVarId) : Except String String :=
  match s.lctx.find? id with
  | some decl => match decl.userName with
    | .str .anonymous x => .ok x
    | _ => .error "a free variable the printer did not create"
  | none => .error "a free variable, which never occurs in a compiled constant"

def describe (e : Expr) : String :=
  let text := toString e
  if text.length ≤ 200 then text else String.ofList (text.toList.take 200) ++ "…"

def kernelWhnf (s : Scope) (e : Expr) : PrintM Expr := do
  match Kernel.whnf (← read).env s.lctx e with
  | .ok r => return r
  | .error _ => throw s!"the kernel could not reduce {describe e}"

def kernelType (s : Scope) (e : Expr) : PrintM Expr := do
  match Kernel.check (← read).env s.lctx e with
  | .ok r => return r
  | .error _ => throw s!"the kernel could not infer the type of {describe e}"

/-- A type as a Pi type, unfolding it to weak head normal form only when
it is not one syntactically. -/
def asPi (s : Scope) (type : Expr) : PrintM (Option Expr) := do
  let type := type.consumeMData
  if type.isForall then return some type
  let type ← kernelWhnf s type
  return if type.isForall then some type else none

def headType (s : Scope) (f : Expr) : PrintM Expr := do
  match f with
  | .const n us =>
    let some info := (← read).env.find? n | throw s!"unknown constant {n}"
    return info.instantiateTypeLevelParams us
  | .fvar id =>
    let some decl := s.lctx.find? id | throw "a free variable the printer did not create"
    return decl.type
  | _ => kernelType s f

/-- The visibility and binder type of each argument of an application,
read from the type of its head. -/
def argumentBinders (s : Scope) (f : Expr) (args : Array Expr) :
    PrintM (Array (Visibility × Expr)) := do
  let mut type ← headType s f
  let mut binders := #[]
  for a in args do
    let some (.forallE _ d b bi) ← asPi s type
      | throw s!"an application of {describe f}, whose type has too few binders"
    binders := binders.push (Visibility.ofBinderInfo bi, d)
    type := b.instantiate1 a
  return binders

/-- The fields of a constructor's type, after its parameters, as lambdas
returning field `i` of `n`. -/
def fieldsAsLambdas (fields : Expr) (n i : Nat) : Expr :=
  go fields n
where
  go : Expr → Nat → Expr
    | .forallE x t b bi, k + 1 => .lam x t (go b k) bi
    | _, _ => .bvar (n - 1 - i)

/-- `Expr.proj S i t` for a structure-like `S` that is not an Agda record
(`String`, which stays a postulate for `BUILTIN STRING`, or a type whose
constructor binds a parameter explicitly), as an application of `S`'s
recursor:
`S.rec {params} {λ self → Tᵢ} (λ f₀ … fₙ₋₁ → fᵢ) t`, where `Tᵢ` is the
field's type with each earlier field `fⱼ` replaced by `proj S j self`,
exactly as the kernel types a projection.  The motive's universe is not
printed under U, so the level it is given here is zero.  It checks
against a postulated recursor for a field whose type mentions no earlier
field, and needs the recursor to compute (issue M2-5) for the others. -/
def projectionAsRecursor (s : Scope) (S : Name) (i : Nat) (t : Expr) : PrintM Expr := do
  let env := (← read).env
  let some (.inductInfo ind) := env.find? S
    | throw s!"a projection from {S}, which is not an inductive type"
  let [ctor] := ind.ctors | throw s!"a projection from {S}, which has more than one constructor"
  unless ind.numIndices == 0 do throw s!"a projection from {S}, which has indices"
  -- A recursive type's minor premise also takes the fields' induction
  -- hypotheses, which this minor premise lacks.
  if ind.isRec then throw s!"a projection from {S}, which is recursive and not a record"
  let some (.ctorInfo c) := env.find? ctor | throw s!"unknown constructor {ctor}"
  let some (.recInfo r) := env.find? (mkRecName S) | throw s!"unknown recursor of {S}"
  unless i < c.numFields do throw s!"a projection of field {i} from {S}"
  let structType ← kernelWhnf s (← kernelType s t)
  let .const _ us := structType.getAppFn | throw s!"a projection from {describe structType}"
  let params := structType.getAppArgs
  unless params.size == ind.numParams do throw s!"a projection from {describe structType}"
  let mut fields := (ConstantInfo.ctorInfo c).instantiateTypeLevelParams us
  for p in params do
    let .forallE _ _ b _ := fields | throw s!"the constructor {ctor} has too few parameters"
    fields := b.instantiate1 p
  let self : FVarId := ⟨.num `_lean2agda.self s.depth⟩
  let mut field := fields
  for j in [:i] do
    let .forallE _ _ b _ := field | throw s!"the constructor {ctor} has too few fields"
    field := b.instantiate1 (.proj S j (.fvar self))
  let .forallE _ fieldType _ _ := field | throw s!"the constructor {ctor} has too few fields"
  let motive := Expr.lam `self structType (fieldType.abstract #[.fvar self]) .default
  let minor := fieldsAsLambdas fields c.numFields i
  let levels := if r.levelParams.length == us.length + 1 then Level.zero :: us else us
  return mkAppN (.const r.name levels) (params ++ #[motive, minor, t])

mutual

partial def printExpr (s : Scope) (e : Expr) : PrintM AgdaTerm := do
  match e with
  | .bvar i => throw s!"a loose bound variable #{i}"
  | .fvar id => return .var (← s.nameOf id)
  | .mvar _ => throw "a metavariable, which never occurs in a compiled constant"
  | .sort _ => return .sort
  | .const n _ => return .const ((← read).naming.constant n)
  | .lit (.natVal n) => return .nat n
  | .lit (.strVal v) => return .str v
  | .mdata _ b => printExpr s b
  | .proj S i t =>
    if isAgdaRecordName (← read).env S then printFieldProjection s S i t
    else
      modify fun c => { c with projections := c.projections + 1 }
      printExpr s (← projectionAsRecursor s S i t)
  | .app .. => printApp s e
  | .lam .. => printLambda s e none false
  | .forallE n t b bi =>
    let dom ← printExpr s t
    let v := Visibility.ofBinderInfo bi
    -- The printer keeps every expression free of loose bound variables, so
    -- the body's only possible one is the binder's own.
    if b.hasLooseBVars then
      let (s', x, fv) := s.enter n t bi
      return .pi v (some x) dom (← printExpr s' (b.instantiate1 fv))
    else
      return .pi v none dom (← printExpr s b)
  | .letE n t v b _ => printLet s n t v b none

/-- Print `e` where Agda will check it against `expected`, so that a
lambda takes the visibility of the expected Pi type. -/
partial def printAgainst (s : Scope) (e expected : Expr) (top : Bool) : PrintM AgdaTerm := do
  match e with
  | .mdata _ b => printAgainst s b expected top
  | .lam .. => printLambda s e (some expected) top
  | .letE n t v b _ => printLet s n t v b (some expected)
  | _ => printExpr s e

partial def printLambda (s : Scope) (e : Expr) (expected : Option Expr) (top : Bool) :
    PrintM AgdaTerm := do
  let .lam n t b bi := e | throw "internal error: printLambda on a non-lambda"
  let pi ← match expected with
    | some type => asPi s type
    | none => pure none
  let own := Visibility.ofBinderInfo bi
  let (v, codomain) := match pi with
    | some (.forallE _ _ cb cbi) => (Visibility.ofBinderInfo cbi, some cb)
    | _ => (own, none)
  if v != own then
    modify fun c => if top then { c with topRepairs := c.topRepairs + 1 }
      else { c with deepRepairs := c.deepRepairs + 1 }
  let dom ← printExpr s t
  let (s', x, fv) := s.enter n t bi
  let body := b.instantiate1 fv
  let bodyTerm ← match codomain with
    | some cb => printAgainst s' body (cb.instantiate1 fv) top
    | none => printExpr s' body
  return .lam v x dom bodyTerm

partial def printLet (s : Scope) (n : Name) (t v b : Expr) (expected : Option Expr) :
    PrintM AgdaTerm := do
  let ty ← printExpr s t
  let value ← printAgainst s v t false
  let (s', x, fv) := s.enterLet n t v
  let body := b.instantiate1 fv
  let bodyTerm ← match expected with
    | some type => printAgainst s' body type false
    | none => printExpr s' body
  return .letE x ty value bodyTerm

partial def printApp (s : Scope) (e : Expr) : PrintM AgdaTerm := do
  let f := e.getAppFn
  let args := e.getAppArgs
  let binders ← argumentBinders s f args
  let mut out ← match f with
    | .lam .. => printLambda s f none false
    | _ => printExpr s f
  for h : i in [:args.size] do
    let (v, dom) := binders[i]!
    out := .app out v (← printAgainst s args[i] dom false)
  return out

/-- `Expr.proj S i t` for a record `S`: Agda's projection `S.fᵢ` of the
field, applied to `S`'s parameters as Agda's projections take them
(instance arguments for the parameters declared as instances, implicit
ones for the rest), then to `t`.  The parameters are read from the type
of `t`, as the kernel types a projection. -/
partial def printFieldProjection (s : Scope) (S : Name) (i : Nat) (t : Expr) : PrintM AgdaTerm := do
  let env := (← read).env
  let some (.inductInfo ind) := env.find? S | throw s!"a projection from {S}, which is not an inductive type"
  let [ctor] := ind.ctors | throw s!"a projection from {S}, which has more than one constructor"
  let some (.ctorInfo c) := env.find? ctor | throw s!"unknown constructor {ctor}"
  let some (x, depth) := recordFieldBinder c.type ind.numParams i
    | throw s!"a projection of field {i} from {S}"
  let structType ← kernelWhnf s (← kernelType s t)
  let head := structType.getAppFn
  let params := structType.getAppArgs
  unless head.isConstOf S && params.size == ind.numParams do
    throw s!"a projection from {describe structType}"
  modify fun c => { c with fieldProjections := c.fieldProjections + 1 }
  let binders ← argumentBinders s head params
  let mut out := AgdaTerm.field ((← read).naming.constant S) (binderName x depth)
  for h : j in [:params.size] do
    let (v, dom) := binders[j]!
    out := .app out (if v == .instance then .instance else .implicit) (← printAgainst s params[j] dom false)
  return .app out .explicit (← printExpr s t)

end

/-- Enter the first `n` binders of a type: their printed binders, the
scope inside them, and the rest of the type with their free variables in
place, for the caller to print in that scope.  Every binder is entered,
used or not, as a declaration's telescope names each one. -/
partial def enterTelescope (s : Scope) (type : Expr) :
    Nat → PrintM (Array (Visibility × String × AgdaTerm) × Scope × Expr)
  | 0 => return (#[], s, type)
  | k + 1 => do
    let some (.forallE n t b bi) ← asPi s type | throw "a telescope longer than its type"
    let dom ← printExpr s t
    let (s', x, fv) := s.enter n t bi
    let (rest, inner, body) ← enterTelescope s' (b.instantiate1 fv) k
    return (#[(Visibility.ofBinderInfo bi, x, dom)] ++ rest, inner, body)

/-- The first `n` binders of a type as a telescope, and the rest of the
type in their scope, as a `data` type's parameters and its sort. -/
partial def printTelescope (s : Scope) (type : Expr) (n : Nat) :
    PrintM (Array (Visibility × String × AgdaTerm) × AgdaTerm) := do
  let (binders, inner, rest) ← enterTelescope s type n
  return (binders, ← printExpr inner rest)

def renderTelescope (binders : Array (Visibility × String × AgdaTerm)) : String :=
  " ".intercalate (binders.toList.map fun (v, x, t) => v.opening ++ x ++ " : " ++ t.render ++ v.closing)

/-- A definition's clause: the leading lambdas of its value become
left-hand-side patterns, because Agda inserts a definition's leading
implicit and instance patterns itself and would then refuse an implicit
lambda on the right. -/
structure Clause where
  patterns : Array (Visibility × String)
  body : AgdaTerm
  deriving BEq, Repr, Inhabited

def Clause.render (c : Clause) (name : String) : String :=
  c.patterns.foldl (fun out (v, x) => match v with
    | .explicit => out ++ " " ++ x
    | .implicit => out ++ " {" ++ x ++ "}"
    | .instance => out ++ " ⦃ " ++ x ++ " ⦄") name ++ " = " ++ c.body.render

def Clause.ofTerm : AgdaTerm → Clause
  | .lam v x _ b => let c := Clause.ofTerm b; { c with patterns := #[(v, x)] ++ c.patterns }
  | t => { patterns := #[], body := t }

def runPrint {α : Type} (p : Printer) (m : PrintM α) : Except String (α × PrintCounts) :=
  (m.run p).run {}

/-- Print a closed type. -/
def Printer.type (p : Printer) (type : Expr) : Except String (AgdaTerm × PrintCounts) :=
  runPrint p (printExpr {} type)

/-- Print a closed value as the clause of a definition of the given type. -/
def Printer.clause (p : Printer) (type value : Expr) : Except String (Clause × PrintCounts) := do
  let (t, counts) ← runPrint p (printAgainst {} value type true)
  return (Clause.ofTerm t, counts)

/-- Print the first `n` binders of a closed type as a telescope, and the
rest of the type. -/
def Printer.telescope (p : Printer) (type : Expr) (n : Nat) :
    Except String ((Array (Visibility × String × AgdaTerm) × AgdaTerm) × PrintCounts) :=
  runPrint p (printTelescope {} type n)

/-- Print a closed term with no expected type. -/
def Printer.term (p : Printer) (e : Expr) : Except String (AgdaTerm × PrintCounts) :=
  runPrint p (printExpr {} e)

end Lean2Agda
