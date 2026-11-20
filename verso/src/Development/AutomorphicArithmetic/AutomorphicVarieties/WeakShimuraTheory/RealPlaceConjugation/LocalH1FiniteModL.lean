import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

/- English proof (translation)
Use `haveI : Module.Finite K V := Module.Finite.of_finite`. Rewrite using `[Module.natCard_eq_pow_finrank (K := K) (V := Module.Dual K V), Module.natCard_eq_pow_finrank (K := K) (V := V), Subspace.dual_finrank_eq]`.
-/
private theorem natCard_dual_eq_natCard_of_finite (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V] [Finite V] :
    Nat.card (Module.Dual K V) = Nat.card V := by
  haveI : Module.Finite K V := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := K) (V := Module.Dual K V),
    Module.natCard_eq_pow_finrank (K := K) (V := V), Subspace.dual_finrank_eq]

/- English proof (translation)
Introduce `hF hT hE F Ω _ _ _ _ _ l _ M _ _ _ _ _ A v ρ hv hρ`. Use `haveI : Fact (Nat.Prime (l ^ 1)) := ⟨by rw [pow_one]; exact Fact.out⟩`. Take `⟨_, hf1, _, _⟩` from `hF F Ω l 1 M A ρ v one_pos hv hρ`. Take `⟨⟨e2⟩, _, _, _, hbij⟩` from `hT F Ω l 1 M A ρ v one_pos hv hρ`. Take `⟨hEram, hEun⟩` from `hE F Ω l 1 M A ρ v one_pos hv hρ`.

Take `⟨e2'⟩ : Nonempty (H2 ((charRep ((cycMod F Ω l 1).comp (Dec (F` from `F) A).subtype)).comp (MonoidHom.id _)) ≃ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)) := by`. Rewrite using `[MonoidHom.comp_id]`. Conclude with `⟨e2⟩`. Use `haveI hfinD : Finite (Module.Dual (ZMod (l ^ 1)) M) := Finite.of_injective (fun f : Module.Dual (ZMod (l ^ 1)) M => (f : M → ZMod (l ^ 1))) DFunLike.coe_injective`. Use `haveI hfinT : Finite (TDual (ZMod (l ^ 1)) M) := hfinD`.

Establish `hH2 : Nat.card (H2 ρ) ≤ Nat.card M`. Combine the equalities or inequalities in the displayed calculation. Use `⟨hf1, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hl : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal`. Rewrite using `[if_pos hl, hEram hl, pow_add, pow_one (Nat.card M), ← mul_assoc]`.

Conclude with `Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hH2)`. Rewrite using `[if_neg hl, hEun hl, add_zero, pow_one (Nat.card M)]`. Conclude with `Nat.mul_le_mul_left _ hH2`.
-/
theorem UpperTheory.V.Ws.local_h1_finite_mod_l :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (ρ : Representation (ZMod (l ^ 1)) (Dec (F := F) A) M), IsPlaceOver A v → ContAction ρ → Finite (H1 ρ) ∧ Nat.card (H1 ρ) ≤ Nat.card (H0 ρ) * Nat.card M ^ (1 + if ((l : ℕ) : 𝓞 F) ∈ v.asIdeal then locDeg v else 0) := by
  intro hF hT hE F Ω _ _ _ _ _ l _ M _ _ _ _ _ A v ρ hv hρ
  haveI : Fact (Nat.Prime (l ^ 1)) := ⟨by rw [pow_one]; exact Fact.out⟩
  obtain ⟨_, hf1, _, _⟩ := hF F Ω l 1 M A ρ v one_pos hv hρ
  obtain ⟨⟨e2⟩, _, _, _, hbij⟩ := hT F Ω l 1 M A ρ v one_pos hv hρ
  obtain ⟨hEram, hEun⟩ := hE F Ω l 1 M A ρ v one_pos hv hρ
  obtain ⟨e2'⟩ : Nonempty (H2 ((charRep ((cycMod F Ω l 1).comp (Dec (F := F) A).subtype)).comp
      (MonoidHom.id _)) ≃ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)) := by
    rw [MonoidHom.comp_id]
    exact ⟨e2⟩
  haveI hfinD : Finite (Module.Dual (ZMod (l ^ 1)) M) :=
    Finite.of_injective (fun f : Module.Dual (ZMod (l ^ 1)) M => (f : M → ZMod (l ^ 1))) DFunLike.coe_injective
  haveI hfinT : Finite (TDual (ZMod (l ^ 1)) M) := hfinD
  have hH2 : Nat.card (H2 ρ) ≤ Nat.card M := by
    calc Nat.card (H2 ρ) = Nat.card (H2 (ρ.comp (MonoidHom.id _))) := by rw [MonoidHom.comp_id]
      _ = _ := Nat.card_eq_of_bijective _ hbij
      _ = Nat.card (Module.Dual (ZMod (l ^ 1)) ↥(H0 ((twDual ((cycMod F Ω l 1).comp (Dec (F := F) A).subtype) ρ).comp
            (MonoidHom.id _)))) := Nat.card_congr (LinearEquiv.congrRight e2').toEquiv
      _ = Nat.card ↥(H0 ((twDual ((cycMod F Ω l 1).comp (Dec (F := F) A).subtype) ρ).comp
            (MonoidHom.id _))) := natCard_dual_eq_natCard_of_finite _ _
      _ ≤ Nat.card (TDual (ZMod (l ^ 1)) M) := Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = Nat.card M := natCard_dual_eq_natCard_of_finite _ _
  refine ⟨hf1, ?_⟩
  by_cases hl : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal
  · rw [if_pos hl, hEram hl, pow_add, pow_one (Nat.card M), ← mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hH2)
  · rw [if_neg hl, hEun hl, add_zero, pow_one (Nat.card M)]
    exact Nat.mul_le_mul_left _ hH2
