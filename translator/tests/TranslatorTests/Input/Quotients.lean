/-
File: translator/tests/TranslatorTests/Input/Quotients.lean
-/

/-!
Quotients for the computation rules of the profile U scaffold
(`tests/Scaffold.lean`, and the golden scaffold `quotients` of
`tests/run.sh`).  Each theorem holds by `rfl` because Lean's kernel
reduces a quotient primitive applied to `Quot.mk`, and Agda checks it only
with the rewrite rule the scaffold states for that primitive: `succ_mk`,
`Quot.lift` itself; `over_mk`, a lift into a function type applied once
more; `eta_mk`, a lift under a binder whose result is a function only by
eta, the shape of `funext`'s proof; `ind_mk`, `Quot.ind`, which Lean's
kernel accepts by proof irrelevance and Agda, whose `Eq` is not
proof irrelevant under profile U, only by the rule.  The quotient is by
equality, so that each respect proof is `congrArg`.
-/

namespace QuotFixtures

def succ (q : Quot (@Eq Nat)) : Nat :=
  Quot.lift Nat.succ (fun _ _ h => congrArg Nat.succ h) q

theorem succ_mk (n : Nat) : succ (Quot.mk _ n) = Nat.succ n := rfl

theorem over_mk (n m : Nat) :
    Quot.lift (β := Nat → Nat) (fun a _ => a) (fun _ _ h => congrArg (fun a (_ : Nat) => a) h)
      (Quot.mk (@Eq Nat) n) m = n := rfl

theorem eta_mk (f : Nat → Nat) :
    (fun x => Quot.lift (fun g : Nat → Nat => g x) (fun _ _ h => congrArg (fun g : Nat → Nat => g x) h)
      (Quot.mk (@Eq (Nat → Nat)) f)) = f := rfl

theorem ind_mk (n : Nat) :
    (Quot.ind (β := fun _ => n = n) (fun _ => rfl) (Quot.mk (@Eq Nat) n) : n = n) = rfl := rfl

end QuotFixtures
