import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BarKHomSurjective
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
open NumberField GlobalTheory.CuspRep GlobalTheory.Published GlobalTheory.IdemAdj

namespace GlobalTheory.IdemAdj

/- English proof (translation)
Introduce `E _ _ _ a π W _ _ ρ₀ U hU hst f hf u hu hcoef g`. Use `haveI := hU`. Set `w : Kinf E a → U` to `fun k => ⟨cptOn π k u, hst k u hu⟩`. Set `A : (U →ₗ[ℂ] ℂ) →ₗ[ℂ] (Kinf E a → ℂ)` to `{ toFun := fun ℓ k => ℓ (w k), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Set `ev : GA E a → (U →ₗ[ℂ] ℂ)` to `fun h => (LinearMap.proj h).comp ((Sm E a).subtype.comp (π.V.subtype.comp U.subtype))`.

Establish `hspan : Submodule.span ℂ (Set.range ev) = ⊤` using `by haveI hfr : Module.Free ℂ ((U →ₗ[ℂ] ℂ) ⧸ Submodule.span ℂ (Set.range ev)) := Module.Free.of_divisionRing ℂ _ haveI : Module.Projective ℂ ((U →ₗ[ℂ] ℂ) ⧸ Submodule.span ℂ (Set.range ev)) := @Module.Projective.of_free _ _ _ _ _ hfr`. Use `Submodule.span_eq_top_of_ne_zero fun z hz => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hz (Subtype.ext (Subtype.ext (Subtype.ext (funext fun h => hc _ ⟨h, rfl⟩))))`.

Set `L : U →ₗ[ℂ] ℂ` to `(LinearMap.proj g).comp ((Sm E a).subtype.comp (π.V.subtype.comp (f.comp U.subtype)))`. Establish `hL : L ∈ (AutFin.coeffSpan ρ₀).comap A`. Establish `hmem : L ∈ Submodule.span ℂ (Set.range ev)` using `hspan ▸ Submodule.mem_top`. Use `(Submodule.span_le.2 ?_) hmem` and prove the remaining obligations. Introduce and unpack `_ ⟨h, rfl⟩`.

Conclude with `hcoef h`. Establish `key : (fun k : Kinf E a => (cptRep E a k (f u).1).1 g) = A L`. Use function extensionality and compare the values at `k`. Use `show _ = (f (cptOn π k u)).1.1 g`. Rewrite using `[hf k u hu, cptOn_val]`.

Rewrite using `[key]`. Conclude with `hL`.
-/
theorem typeClosure_of_intertwine : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ₀ : Representation ℂ (Kinf E a) W) (U : Submodule ℂ π.V), FiniteDimensional ℂ U → (∀ k, ∀ u ∈ U, cptOn π k u ∈ U) → ∀ f : π.V →ₗ[ℂ] π.V, (∀ k, ∀ u ∈ U, f (cptOn π k u) = cptOn π k (f u)) → ∀ u ∈ U, (∀ g, (fun k : Kinf E a => (cptRep E a k u.1).1 g) ∈ AutFin.coeffSpan ρ₀) → ∀ g, (fun k : Kinf E a => (cptRep E a k (f u).1).1 g) ∈ AutFin.coeffSpan ρ₀ := by
  intro E _ _ _ a π W _ _ ρ₀ U hU hst f hf u hu hcoef g
  haveI := hU
  let w : Kinf E a → U := fun k => ⟨cptOn π k u, hst k u hu⟩
  let A : (U →ₗ[ℂ] ℂ) →ₗ[ℂ] (Kinf E a → ℂ) :=
    { toFun := fun ℓ k => ℓ (w k), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let ev : GA E a → (U →ₗ[ℂ] ℂ) := fun h =>
    (LinearMap.proj h).comp ((Sm E a).subtype.comp (π.V.subtype.comp U.subtype))
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    haveI hfr : Module.Free ℂ ((U →ₗ[ℂ] ℂ) ⧸ Submodule.span ℂ (Set.range ev)) :=
      Module.Free.of_divisionRing ℂ _
    haveI : Module.Projective ℂ ((U →ₗ[ℂ] ℂ) ⧸ Submodule.span ℂ (Set.range ev)) :=
      @Module.Projective.of_free _ _ _ _ _ hfr
    refine Submodule.span_eq_top_of_ne_zero fun z hz => ?_
    by_contra hc
    push_neg at hc
    exact hz (Subtype.ext (Subtype.ext (Subtype.ext (funext fun h => hc _ ⟨h, rfl⟩))))
  let L : U →ₗ[ℂ] ℂ :=
    (LinearMap.proj g).comp ((Sm E a).subtype.comp (π.V.subtype.comp (f.comp U.subtype)))
  have hL : L ∈ (AutFin.coeffSpan ρ₀).comap A := by
    have hmem : L ∈ Submodule.span ℂ (Set.range ev) := hspan ▸ Submodule.mem_top
    refine (Submodule.span_le.2 ?_) hmem
    rintro _ ⟨h, rfl⟩
    exact hcoef h
  have key : (fun k : Kinf E a => (cptRep E a k (f u).1).1 g) = A L := by
    funext k
    show _ = (f (cptOn π k u)).1.1 g
    rw [hf k u hu, cptOn_val]
  rw [key]
  exact hL

end GlobalTheory.IdemAdj
