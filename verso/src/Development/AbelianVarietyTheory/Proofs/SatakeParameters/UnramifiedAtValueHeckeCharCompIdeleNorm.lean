import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.NormValGen

/- English proof (translation)
Establish `hf' : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ f` using `hf`. Establish `hy : Valued.v (y : v.adicCompletion K) ≠ 0` using `(Valuation.ne_zero_iff _).2 y.ne_zero`. Establish `hx : Valued.v (x : w.adicCompletion L) ≠ 0` using `(Valuation.ne_zero_iff _).2 x.ne_zero`. Rewrite `h` using `[FinitePlace.norm_def, FinitePlace.norm_def]`. Rewrite `h` using `[WithZeroMulInt.toNNReal_neg_apply _ hy, WithZeroMulInt.toNNReal_neg_apply _ hx, NNReal.coe_inj, hf', Nat.cast_pow, ← zpow_natCast, ← zpow_mul]`.

Establish `h1` using `HeightOneSpectrum.one_lt_absNorm_nnreal v`. Establish `h2` using `zpow_right_injective₀ (zero_lt_one.trans h1) h1.ne' h`. Rewrite using `[← WithZero.coe_unzero hy, ← WithZero.coe_unzero hx, ← WithZero.coe_pow]`. Use `congrArg _ (Multiplicative.toAdd.injective ?_)` and prove the remaining obligations. Rewrite using `[h2, toAdd_pow, nsmul_eq_mul]`.
-/
theorem valuation_eq_pow_of_norm_eq {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) (y : (v.adicCompletion K)ˣ) (x : (w.adicCompletion L)ˣ)
    (h : ‖(y : v.adicCompletion K)‖ = ‖(x : w.adicCompletion L)‖) (f : ℕ) (hf : normV w = normV v ^ f) :
    Valued.v (y : v.adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ f := by
  have hf' : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ f := hf
  have hy : Valued.v (y : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 y.ne_zero
  have hx : Valued.v (x : w.adicCompletion L) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  rw [FinitePlace.norm_def, FinitePlace.norm_def] at h
  rw [WithZeroMulInt.toNNReal_neg_apply _ hy, WithZeroMulInt.toNNReal_neg_apply _ hx, NNReal.coe_inj, hf',
    Nat.cast_pow, ← zpow_natCast, ← zpow_mul] at h
  have h1 := HeightOneSpectrum.one_lt_absNorm_nnreal v
  have h2 := zpow_right_injective₀ (zero_lt_one.trans h1) h1.ne' h
  rw [← WithZero.coe_unzero hy, ← WithZero.coe_unzero hx, ← WithZero.coe_pow]
  refine congrArg _ (Multiplicative.toAdd.injective ?_)
  rw [h2, toAdd_pow, nsmul_eq_mul]

/- English proof (translation)
Establish `h` using `GroundTheory.Global.ideleNorm_finiteEmbedding (K := K) w x`. Establish `hm` using `GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := K) (GroundTheory.Global.IdeleGroup.finiteEmbedding w x)`. Rewrite `hm` using `[h]`. Establish `hm'` using `congrArg Subtype.val hm`. Rewrite `hm'` using `[GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding]`.

Conclude with `⟨_, (hψ _).trans (congrArg ψ.1 h), valuation_eq_pow_of_norm_eq _ w _ x hm' f hf⟩`.
-/
theorem loc_eq_of_comp_norm {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (ψ : HChar K) (ψ' : HChar M) (hψ : ∀ x : Ideles M, ψ'.1 x = ψ.1 (GroundTheory.Global.ideleNorm K M x))
    (w : HeightOneSpectrum (𝓞 M)) (f : ℕ) (hf : normV w = normV (w.under (𝓞 K)) ^ f)
    (x : (w.adicCompletion M)ˣ) : ∃ y : ((w.under (𝓞 K)).adicCompletion K)ˣ,
      ψ'.loc w x = ψ.loc (w.under (𝓞 K)) y ∧
      Valued.v (y : (w.under (𝓞 K)).adicCompletion K) = Valued.v (x : w.adicCompletion M) ^ f := by
  have h := GroundTheory.Global.ideleNorm_finiteEmbedding (K := K) w x
  have hm := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := K)
    (GroundTheory.Global.IdeleGroup.finiteEmbedding w x)
  rw [h] at hm
  have hm' := congrArg Subtype.val hm
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding] at hm'
  exact ⟨_, (hψ _).trans (congrArg ψ.1 h), valuation_eq_pow_of_norm_eq _ w _ x hm' f hf⟩

/- English proof (translation)
Introduce `K M _ _ _ _ _ ψ ψ' hψ w f hf hu`. Use `⟨fun x hx => ?_, ?_⟩` and prove the remaining obligations. Take `⟨y, hy, hv⟩` from `loc_eq_of_comp_norm ψ ψ' hψ w f hf x`. Rewrite using `[hy]`. Apply `hu` to reduce the goal to its premises.

Unfold `IsUnitAt at *`. Rewrite using `[hv, hx, one_pow]`. Take `⟨y, hy, hv⟩` from `loc_eq_of_comp_norm ψ ψ' hψ w f hf (atFin w (unif w))`. Establish `h1` using `unif_spec w`. Establish `h2` using `unif_spec (w.under (𝓞 K))`.

Establish `hunit : IsUnitAt (w.under (𝓞 K)) (y * ((atFin _ (unif (w.under (𝓞 K)))) ^ f)⁻¹)`. Unfold `IsUnitAt IsUnifAt at *`. Rewrite using `[Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, map_pow, hv, h1, h2]`. Conclude with `mul_inv_cancel₀ (pow_ne_zero _ WithZero.exp_ne_zero)`. Establish `h3` using `hu _ hunit`.

Rewrite `h3` using `[map_mul, map_inv, mul_inv_eq_one, map_pow]`. Conclude with `hy.trans h3`.
-/
theorem unrAt_val_of_comp_norm : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (ψ : HChar K) (ψ' : HChar M), (∀ x : Ideles M, ψ'.1 x = ψ.1 (GroundTheory.Global.ideleNorm K M x)) → ∀ (w : HeightOneSpectrum (𝓞 M)) (f : ℕ), normV w = normV (w.under (𝓞 K)) ^ f → ψ.UnrAt (w.under (𝓞 K)) → ψ'.UnrAt w ∧ ψ'.val w = ψ.val (w.under (𝓞 K)) ^ f := by
  intro K M _ _ _ _ _ ψ ψ' hψ w f hf hu
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, hv⟩ := loc_eq_of_comp_norm ψ ψ' hψ w f hf x
    rw [hy]
    apply hu
    unfold IsUnitAt at *
    rw [hv, hx, one_pow]
  · obtain ⟨y, hy, hv⟩ := loc_eq_of_comp_norm ψ ψ' hψ w f hf (atFin w (unif w))
    have h1 := unif_spec w
    have h2 := unif_spec (w.under (𝓞 K))
    have hunit : IsUnitAt (w.under (𝓞 K)) (y * ((atFin _ (unif (w.under (𝓞 K)))) ^ f)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, map_pow, hv, h1, h2]
      exact mul_inv_cancel₀ (pow_ne_zero _ WithZero.exp_ne_zero)
    have h3 := hu _ hunit
    rw [map_mul, map_inv, mul_inv_eq_one, map_pow] at h3
    exact hy.trans h3

end GlobalTheory.NormValGen

end
