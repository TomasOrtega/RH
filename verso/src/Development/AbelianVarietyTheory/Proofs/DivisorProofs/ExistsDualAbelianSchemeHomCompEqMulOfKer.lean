import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuotientIsAbelianSchemeOfQuotientScheme
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfDualHomomorphismKernelKilledStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfDualHomomorphismKernelKilledStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualFactor

/- English proof (translation)
Take `⟨mu, hmu⟩` from `GlobalTheory.AbelianQuotient.exists_desc la (𝟙 A ^ d) (by`. Introduce `W a b h`. Rewrite using `[comp_pow, comp_pow, Category.comp_id, Category.comp_id]`. Establish `h1 : (a / b) ≫ la = 1`. Rewrite using `[GrpObj.div_comp, h, div_self']`.

Establish `h2` using `hk W _ h1`. Rewrite using `[div_pow, div_eq_one] at h2)` and apply the resulting hypothesis. Use `FlatQuotient.epi_of_flat_surjective la` as an intermediate fact. Use `FlatQuotient.epi_tensorHom la la` as an intermediate fact. Use `⟨mu, ⟨?_, ?_⟩, hmu, ?_⟩` and prove the remaining obligations.

Establish `e : (η[A] : 𝟙_ (Over S) ⟶ A) = 1`. Rewrite using `[Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]`. Rewrite using `[← IsMonHom.one_hom la, Category.assoc, hmu, comp_pow, Category.comp_id, e, one_pow]`. Rewrite using `[← cancel_epi (la ⊗ₘ la), ← IsMonHom.mul_hom_assoc, hmu, tensorHom_comp_tensorHom_assoc, hmu, comp_pow, Category.comp_id]`. Establish `hμ : (μ[A] : A ⊗ A ⟶ A) = fst A A * snd A A`.

Rewrite using `[Hom.mul_def, lift_fst_snd, Category.id_comp]`. Rewrite using `[hμ, comp_mul, tensorHom_fst, tensorHom_snd, comp_pow, comp_pow, Category.comp_id, Category.comp_id, mul_pow]`. Rewrite using `[← cancel_epi la, reassoc_of% hmu, comp_pow, Category.comp_id, pow_comp, Category.id_comp]`.
-/
theorem factor_of_flat {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A]
    [IsCommMonObj B] (la : A ⟶ B) [IsMonHom la] [Flat la.left] [Surjective la.left]
    [QuasiCompact la.left] (d : ℕ)
    (hk : ∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) :
    ∃ mu : B ⟶ A, IsMonHom mu ∧ la ≫ mu = 𝟙 A ^ d ∧ mu ≫ la = 𝟙 B ^ d := by
  obtain ⟨mu, hmu⟩ := GlobalTheory.AbelianQuotient.exists_desc la (𝟙 A ^ d) (by
    intro W a b h
    rw [comp_pow, comp_pow, Category.comp_id, Category.comp_id]
    have h1 : (a / b) ≫ la = 1 := by
      rw [GrpObj.div_comp, h, div_self']
    have h2 := hk W _ h1
    rwa [div_pow, div_eq_one] at h2)
  have := FlatQuotient.epi_of_flat_surjective la
  have := FlatQuotient.epi_tensorHom la la
  refine ⟨mu, ⟨?_, ?_⟩, hmu, ?_⟩
  · have e : (η[A] : 𝟙_ (Over S) ⟶ A) = 1 := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [← IsMonHom.one_hom la, Category.assoc, hmu, comp_pow, Category.comp_id, e, one_pow]
  · rw [← cancel_epi (la ⊗ₘ la), ← IsMonHom.mul_hom_assoc, hmu, tensorHom_comp_tensorHom_assoc, hmu,
      comp_pow, Category.comp_id]
    have hμ : (μ[A] : A ⊗ A ⟶ A) = fst A A * snd A A := by
      rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    rw [hμ, comp_mul, tensorHom_fst, tensorHom_snd, comp_pow, comp_pow, Category.comp_id,
      Category.comp_id, mul_pow]
  · rw [← cancel_epi la, reassoc_of% hmu, comp_pow, Category.comp_id, pow_comp, Category.id_comp]

/- English proof (translation)
Introduce `S A B _ _ Q la d hA hB hAB hBA hla hd hk`. Use `hA.comm` as an intermediate fact. Use `hB.comm` as an intermediate fact. Use `hA.proper` as an intermediate fact. Use `hB.proper` as an intermediate fact.

Establish `: Surjective la.left` using `GlobalTheory.T.surjective_of_dual_homomorphism_kernel_killed S A B Q la d hA hB hAB hBA hla hd hk`. Establish `: Flat la.left` using `GlobalTheory.T.flat_of_dual_homomorphism_kernel_killed S A B Q la d hA hB hAB hBA hla hd hk`. Establish `: QuasiCompact la.left`. Establish `: QuasiCompact (la.left ≫ B.hom)` using `by rw [Over.w]; infer_instance`. Conclude with `QuasiCompact.of_comp la.left B.hom`.

Conclude with `factor_of_flat A B la d hk`.
-/
theorem main : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → ∃ mu : B ⟶ A, IsMonHom mu ∧ la ≫ mu = 𝟙 A ^ d ∧ mu ≫ la = 𝟙 B ^ d := by
  intro S A B _ _ Q la d hA hB hAB hBA hla hd hk
  have := hA.comm
  have := hB.comm
  have := hA.proper
  have := hB.proper
  have : Surjective la.left := GlobalTheory.T.surjective_of_dual_homomorphism_kernel_killed S A B Q la d hA hB hAB hBA hla hd hk
  have : Flat la.left := GlobalTheory.T.flat_of_dual_homomorphism_kernel_killed S A B Q la d hA hB hAB hBA hla hd hk
  have : QuasiCompact la.left := by
    have : QuasiCompact (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
    exact QuasiCompact.of_comp la.left B.hom
  exact factor_of_flat A B la d hk

end GlobalTheory.DualFactor
