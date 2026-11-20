import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.PiBallFromAlt

noncomputable section

namespace PI.PoleLengthCount

open Module

/- English proof (translation)
Introduce `R M ι _ _ _ _ P Q _`. Use `set PP := Submodule.pi Set.univ fun _ : ι => P`. Use `set QQ := Submodule.pi Set.univ fun _ : ι => Q`. Set `q : Submodule R ↥P` to `Q.comap P.subtype`. Set `g : ι → (↥PP →ₗ[R] ↥P)` to `fun i => ((LinearMap.proj i).comp PP.subtype).codRestrict P (fun x => x.2 i (Set.mem_univ i))`.

Set `f : ↥PP →ₗ[R] (ι → ↥P ⧸ q)` to `LinearMap.pi fun i => q.mkQ.comp (g i)`. Establish `hker : QQ.comap PP.subtype = LinearMap.ker f`. Use extensionality with `x`. Simplify using `only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_ker, f, QQ, Submodule.mem_pi, Set.mem_univ, true_implies]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use function extensionality and compare the values at `i`. Simplify using `only [LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `h i`. Introduce `h i`.

Use `congrFun h i` as an intermediate fact. Simplify using `only [LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply, Submodule.Quotient.mk_eq_zero] at this`. Conclude with `this`. Establish `hsurj : Function.Surjective f`. Introduce `y`.

Use `choose p hp using fun i => Submodule.Quotient.mk_surjective q (y i)`. Use `⟨⟨fun i => (p i : M), fun i _ => (p i).2⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `only [f, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply]`. Rewrite using `[← hp i]`.

Both sides reduce to the same expression. Establish `e1` using `(Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective f hsurj)`. Rewrite using `[e1.length_eq, Module.length_pi, ENat.card_eq_coe_fintype_card]`.
-/
theorem piLen_holds : PiLen := by
  intro R M ι _ _ _ _ P Q _
  classical
  set PP := Submodule.pi Set.univ fun _ : ι => P
  set QQ := Submodule.pi Set.univ fun _ : ι => Q
  let q : Submodule R ↥P := Q.comap P.subtype
  let g : ι → (↥PP →ₗ[R] ↥P) := fun i =>
    ((LinearMap.proj i).comp PP.subtype).codRestrict P (fun x => x.2 i (Set.mem_univ i))
  let f : ↥PP →ₗ[R] (ι → ↥P ⧸ q) := LinearMap.pi fun i => q.mkQ.comp (g i)
  have hker : QQ.comap PP.subtype = LinearMap.ker f := by
    ext x
    simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_ker, f, QQ,
      Submodule.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h
      funext i
      simp only [LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply,
        Submodule.Quotient.mk_eq_zero]
      exact h i
    · intro h i
      have := congrFun h i
      simp only [LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply,
        Submodule.Quotient.mk_eq_zero] at this
      exact this
  have hsurj : Function.Surjective f := by
    intro y
    choose p hp using fun i => Submodule.Quotient.mk_surjective q (y i)
    refine ⟨⟨fun i => (p i : M), fun i _ => (p i).2⟩, ?_⟩
    funext i
    simp only [f, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [← hp i]
    rfl
  have e1 := (Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective f hsurj)
  rw [e1.length_eq, Module.length_pi, ENat.card_eq_coe_fintype_card]

end PI.PoleLengthCount
