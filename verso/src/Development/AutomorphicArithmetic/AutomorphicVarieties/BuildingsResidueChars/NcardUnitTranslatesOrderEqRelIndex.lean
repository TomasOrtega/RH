import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.Cond

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem UpperTheory.ncard_unit_translates_order_eq_relIndex :
    ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (τ : K) (a : (Etau K τ)ˣ) (y : Etau K τ), {S : Set (Etau K τ) | ∃ u ∈ Gu O τ, S = PS.ml (a * u) (Ord O y)}.ncard = (Hu O y).relIndex (Gu O τ) := by
  intro O K _ _ _ τ a y
  set G := Gu O τ
  set H := (Hu O y).subgroupOf G
  have key : ∀ g₁ g₂ : G, PS.ml (a * (g₁ : (Etau K τ)ˣ)) (PK.Ord O y) =
      PS.ml (a * (g₂ : (Etau K τ)ˣ)) (PK.Ord O y) ↔ g₁⁻¹ * g₂ ∈ H := by
    intro g₁ g₂
    rw [Subgroup.mem_subgroupOf]
    show _ ↔ PS.ml (((g₁⁻¹ * g₂ : G)) : (Etau K τ)ˣ) (PK.Ord O y) = PK.Ord O y
    rw [PS.ml_mul, PS.ml_mul, (PS.ml_inj a).eq_iff, Subgroup.coe_mul, Subgroup.coe_inv, PS.ml_mul]
    constructor
    · intro h
      rw [← h, ← PS.ml_mul, inv_mul_cancel, PS.ml_one]
    · intro h
      conv_lhs => rw [← h]
      rw [← PS.ml_mul, mul_inv_cancel, PS.ml_one]
  let f : G ⧸ H → Set (Etau K τ) :=
    Quotient.lift (fun g : G => PS.ml (a * (g : (Etau K τ)ˣ)) (PK.Ord O y))
      (fun g₁ g₂ hg => (key g₁ g₂).2 (QuotientGroup.leftRel_apply.1 hg))
  have hf : Function.Injective f := by
    intro q₁ q₂ hq
    obtain ⟨g₁, rfl⟩ := QuotientGroup.mk_surjective q₁
    obtain ⟨g₂, rfl⟩ := QuotientGroup.mk_surjective q₂
    exact QuotientGroup.eq.2 ((key _ _).1 hq)
  have hrange : {S : Set (Etau K τ) | ∃ u ∈ G, S = PS.ml (a * u) (PK.Ord O y)} = Set.range f := by
    ext S
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨((⟨u, hu⟩ : G) : G ⧸ H), rfl⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨g, g.2, rfl⟩
  rw [hrange, Set.ncard_range_of_injective hf]
  rfl
