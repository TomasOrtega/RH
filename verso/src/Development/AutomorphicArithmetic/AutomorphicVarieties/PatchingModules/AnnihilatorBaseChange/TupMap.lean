import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem mem_map {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {y : R} (hy : y ∈ maximalIdeal R) :
    f y ∈ maximalIdeal R' := by
  rw [← res_eq_zero_iff O R'] at *
  rw [res_map]
  exact (res_eq_zero_iff O R y).mpr hy

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
private theorem adic_map {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {Γ : Type} [TopologicalSpace Γ] {a : Γ → R}
    (ha : AdicCont (maximalIdeal R) a) : AdicCont (maximalIdeal R') fun g => f (a g) := by
  intro N
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap f.toRingHom := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    apply Ideal.pow_right_mono
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact mem_map f hx
  have key := (ha N).comp (Ideal.quotientMap (maximalIdeal R' ^ N) f.toRingHom hle)
  convert key using 1
  funext g
  simp [Ideal.quotientMap_mk]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Pa.Core.tupMap :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (R R' : Type) [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (t : Tup Λ A R) (f : R →ₐ[O] R'), ∃ t' : Tup Λ A R', t.Maps f.toRingHom t'.D t'.ψ t'.s t'.U t'.y := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A R R' _ _ _ _ _ _ t f
  refine ⟨⟨t.D.map f.toRingHom, ?_, ?_, fun v i => pushCh f.toRingHom (t.ψ v i), ?_, f t.s, mem_map f t.s_mem,
    fun j i => f (t.U j i), ?_, fun j i => f (t.y j i), fun j i => mem_map f (t.y_mem j i)⟩,
    rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro i
    have h := adic_map f (t.cont i)
    convert h using 2 with g
    have := ((UpperTheory.V.CA.d_gmap t.D).2.2.1 f.toRingHom (MonoidAlgebra.single g 1)).2 i
    simpa using this
  · rw [(UpperTheory.V.CA.d_gmap t.D).2.1]
    have : (res O R' : R' →+* ResidueField O).comp f.toRingHom = (res O R : R →+* ResidueField O) := by
      ext x
      exact res_map f x
    rw [this]
    exact t.red
  · intro v i
    have hp := t.psi v i
    refine ⟨?_, ?_, ?_⟩
    · exact adic_map f hp.cont
    · intro g
      simpa [res_map] using hp.red g
    · intro g
      simpa using congrArg f (hp.mu g)
  · intro j i
    have h := mem_map f (t.U_mem j i)
    simpa using h
