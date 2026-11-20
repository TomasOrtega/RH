import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QzTorsionZmodEmbeddingStatement

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

/- English proof (translation)
Introduce `l _ Γ _ _ ψ hψ`. Use `haveI hd : DiscreteTopology (QZ l) := ⟨rfl⟩`. Unfold `ReciprocityTheory.Gal.ContAction`. Apply `continuous_prod_of_discrete_right.mpr` to reduce the goal to its premises. Introduce `a`.

Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective (ZlSub l) a`. Set `q : ℚ_[l] → QZ l` to `fun z => Submodule.Quotient.mk z`. Establish `hmk : Continuous q`. Use `(continuous_discrete_rng (β := QZ l)).mpr ?_` and prove the remaining obligations. Introduce `b`.

Take `⟨y, rfl⟩ : ∃ y, q y = b` from `Submodule.Quotient.mk_surjective (ZlSub l) b`. Establish `e : q ⁻¹' {q y} = Metric.closedBall y 1`. Use extensionality with `z`. Establish `h1 : q z = q y ↔ z - y ∈ ZlSub l` using `Submodule.Quotient.eq (ZlSub l)`. Rewrite using `[Set.mem_preimage, Set.mem_singleton_iff, h1, LinearMap.mem_range, Metric.mem_closedBall, dist_eq_norm]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw⟩`. Rewrite using `[← hw]`. Conclude with `w.norm_le_one`. Introduce `h`.

Conclude with `⟨⟨z - y, h⟩, rfl⟩`. Rewrite using `[e]`. Conclude with `IsUltrametricDist.isOpen_closedBall y one_ne_zero`. Establish `hc : Continuous fun g : Γ => ((ψ g : ℤ_[l]) : ℚ_[l]) * x` using `(continuous_subtype_val.comp hψ).mul continuous_const`. Use `(hmk.comp hc).congr ?_` and prove the remaining obligations.

Introduce `g`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.LDataCardLeFinrank.contScal :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ψ : Γ →* ℤ_[l]ˣ), (Continuous fun g => ((ψ g : ℤ_[l]ˣ) : ℤ_[l])) → ContAction (scalRep (QZ l) ψ) := by
  intro l _ Γ _ _ ψ hψ
  haveI hd : DiscreteTopology (QZ l) := ⟨rfl⟩
  unfold ReciprocityTheory.Gal.ContAction
  apply continuous_prod_of_discrete_right.mpr
  intro a
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) a
  let q : ℚ_[l] → QZ l := fun z => Submodule.Quotient.mk z
  have hmk : Continuous q := by
    refine (continuous_discrete_rng (β := QZ l)).mpr ?_
    intro b
    obtain ⟨y, rfl⟩ : ∃ y, q y = b := Submodule.Quotient.mk_surjective (ZlSub l) b
    have e : q ⁻¹' {q y} = Metric.closedBall y 1 := by
      ext z
      have h1 : q z = q y ↔ z - y ∈ ZlSub l := Submodule.Quotient.eq (ZlSub l)
      rw [Set.mem_preimage, Set.mem_singleton_iff, h1, LinearMap.mem_range,
        Metric.mem_closedBall, dist_eq_norm]
      constructor
      · rintro ⟨w, hw⟩
        rw [← hw]
        exact w.norm_le_one
      · intro h
        exact ⟨⟨z - y, h⟩, rfl⟩
    rw [e]
    exact IsUltrametricDist.isOpen_closedBall y one_ne_zero
  have hc : Continuous fun g : Γ => ((ψ g : ℤ_[l]) : ℚ_[l]) * x :=
    (continuous_subtype_val.comp hψ).mul continuous_const
  refine (hmk.comp hc).congr ?_
  intro g
  rfl
