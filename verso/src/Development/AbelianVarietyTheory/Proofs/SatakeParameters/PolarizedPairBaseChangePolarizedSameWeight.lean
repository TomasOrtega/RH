import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairSatakeParameterConjugatePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatake
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PolOfSatOfThetaSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ThetaSatakeParametersInverse
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IdeleNormValuationOfLocalCompatibility
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IdeleNormLocalCompatibility
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialInfinite
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.LiftPolar

/- English proof (translation)
Take `⟨j⟩ : Nonempty (M →+* ℂ)` from `inferInstance`. Apply `j.injective` to reduce the goal to its premises. Rewrite using `[IsCMField.complexEmbedding_complexConj M j]`. Conclude with `(IsCMField.complexEmbedding_complexConj E (j.comp (algebraMap E M)) x).symm`.
-/
theorem conj_algebraMap {E M : Type} [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] (x : E) :
    IsCMField.complexConj M (algebraMap E M x) = algebraMap E M (IsCMField.complexConj E x) := by
  obtain ⟨j⟩ : Nonempty (M →+* ℂ) := inferInstance
  apply j.injective
  rw [IsCMField.complexEmbedding_complexConj M j]
  exact (IsCMField.complexEmbedding_complexConj E (j.comp (algebraMap E M)) x).symm

/- English proof (translation)
The claim follows from `(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)`.
-/
theorem cPl_asIdeal {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    (UpperTheory.V.Af.Bc.cPl w).asIdeal =
      w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E →+* 𝓞 E) :=
  (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)

/- English proof (translation)
Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Rewrite using `[cPl_asIdeal]`. Express the relevant statement in the definitionally equal form `(UpperTheory.V.Af.Bc.cPl w).asIdeal.comap (algebraMap (𝓞 E) (𝓞 M)) = (w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 M))).comap _`. Rewrite using `[cPl_asIdeal, Ideal.comap_comap, Ideal.comap_comap]`. Use `congr 1`.

Use extensionality with `x`. Conclude with `conj_algebraMap (x : E)`.
-/
theorem cPl_under {E M : Type} [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] (w : HeightOneSpectrum (𝓞 M)) :
    (UpperTheory.V.Af.Bc.cPl w).under (𝓞 E) = UpperTheory.V.Af.Bc.cPl (w.under (𝓞 E)) := by
  apply HeightOneSpectrum.ext
  rw [cPl_asIdeal]
  change (UpperTheory.V.Af.Bc.cPl w).asIdeal.comap (algebraMap (𝓞 E) (𝓞 M)) = (w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 M))).comap _
  rw [cPl_asIdeal, Ideal.comap_comap, Ideal.comap_comap]
  congr 1
  ext x
  exact conj_algebraMap (x : E)

/- English proof (translation)
Use `show Nat.card (𝓞 E ⧸ (UpperTheory.V.Af.Bc.cPl w).asIdeal) = Nat.card (𝓞 E ⧸ w.asIdeal)`. Use `Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv) ?_).toEquiv` and prove the remaining obligations. Rewrite using `[cPl_asIdeal]`. Conclude with `(Ideal.map_comap_of_surjective (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E →+* 𝓞 E) (RingOfIntegers.mapRingEquiv _).surjective w.asIdeal).symm`.
-/
theorem normV_cPl {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    normV (UpperTheory.V.Af.Bc.cPl w) = normV w := by
  show Nat.card (𝓞 E ⧸ (UpperTheory.V.Af.Bc.cPl w).asIdeal) = Nat.card (𝓞 E ⧸ w.asIdeal)
  refine Nat.card_congr (Ideal.quotientEquiv _ _
    (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv) ?_).toEquiv
  rw [cPl_asIdeal]
  exact (Ideal.map_comap_of_surjective
    (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E →+* 𝓞 E)
    (RingOfIntegers.mapRingEquiv _).surjective w.asIdeal).symm

/- English proof (translation)
Use `Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_` and prove the remaining obligations. Establish `h0 : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal ≠ 0` using `fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)`. Use `(Ideal.finite_factors h0).subset fun w hw => ?_` and prove the remaining obligations. Establish `e : w.under (𝓞 K) = v` using `hw`. Use `show w.asIdeal ∣ _`.

Rewrite using `[Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]`. Conclude with `le_rfl`.
-/
theorem tendsto_under {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 L) => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have h0 : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  have e : w.under (𝓞 K) = v := hw
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]
  exact le_rfl

/- English proof (translation)
Establish `: w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal` using `⟨rfl⟩`. Use `w.isMaximal` as an intermediate fact. Use `(w.under (𝓞 K)).isMaximal` as an intermediate fact. Use `show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)`. Rewrite using `[← Ideal.absNorm_relNorm (𝓞 K) (𝓞 L) w.asIdeal, Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]`.
-/
theorem normV_under {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 L) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

/- English proof (translation)
Establish `hf' : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ f` using `hf`. Establish `hy : Valued.v (y : v.adicCompletion K) ≠ 0` using `(Valuation.ne_zero_iff _).2 y.ne_zero`. Establish `hx : Valued.v (x : w.adicCompletion L) ≠ 0` using `(Valuation.ne_zero_iff _).2 x.ne_zero`. Rewrite `h` using `[FinitePlace.norm_def, FinitePlace.norm_def]`. Rewrite `h` using `[WithZeroMulInt.toNNReal_neg_apply _ hy, WithZeroMulInt.toNNReal_neg_apply _ hx, NNReal.coe_inj, hf', Nat.cast_pow, ← zpow_natCast, ← zpow_mul]`.

Establish `h1` using `HeightOneSpectrum.one_lt_absNorm_nnreal v`. Establish `h2` using `zpow_right_injective₀ (zero_lt_one.trans h1) h1.ne' h`. Rewrite using `[← WithZero.coe_unzero hy, ← WithZero.coe_unzero hx, ← WithZero.coe_pow]`. Use `congrArg _ (Multiplicative.toAdd.injective ?_)` and prove the remaining obligations. Rewrite using `[h2, toAdd_pow, nsmul_eq_mul]`.
-/
theorem val_of_norm {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
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

def normChar {K : Type} (L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (χ : HChar K) :
    HChar L :=
  ⟨χ.1.comp (GroundTheory.Global.ideleNorm K L), χ.2.1.comp GroundTheory.Global.continuous_ideleNorm, fun k =>
    (congrArg χ.1 (GroundTheory.Global.ideleNorm_diagonal (K := K) k)).trans (χ.2.2 _)⟩

/- English proof (translation)
Establish `h` using `GroundTheory.Global.ideleNorm_finiteEmbedding (K := K) w x`. Establish `hm` using `GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := K) (GroundTheory.Global.IdeleGroup.finiteEmbedding w x)`. Rewrite `hm` using `[h]`. Establish `hm'` using `congrArg Subtype.val hm`. Rewrite `hm'` using `[GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding]`.

Conclude with `⟨_, congrArg χ.1 h, val_of_norm _ w _ x hm' f hf⟩`.
-/
theorem normChar_loc {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (χ : HChar K) (w : HeightOneSpectrum (𝓞 L)) (f : ℕ) (hf : normV w = normV (w.under (𝓞 K)) ^ f)
    (x : (w.adicCompletion L)ˣ) : ∃ y : ((w.under (𝓞 K)).adicCompletion K)ˣ,
      (normChar L χ).loc w x = χ.loc (w.under (𝓞 K)) y ∧
      Valued.v (y : (w.under (𝓞 K)).adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ f := by
  have h := GroundTheory.Global.ideleNorm_finiteEmbedding (K := K) w x
  have hm := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := K)
    (GroundTheory.Global.IdeleGroup.finiteEmbedding w x)
  rw [h] at hm
  have hm' := congrArg Subtype.val hm
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding] at hm'
  exact ⟨_, congrArg χ.1 h, val_of_norm _ w _ x hm' f hf⟩

/- English proof (translation)
Use `⟨fun x hx => ?_, ?_⟩` and prove the remaining obligations. Take `⟨y, hy, hv⟩` from `normChar_loc χ w f hf x`. Rewrite using `[hy]`. Apply `hχ` to reduce the goal to its premises. Unfold `IsUnitAt at *`.

Rewrite using `[hv, hx, one_pow]`. Take `⟨y, hy, hv⟩` from `normChar_loc χ w f hf (atFin w (unif w))`. Establish `h1` using `unif_spec w`. Establish `h2` using `unif_spec (w.under (𝓞 K))`. Establish `hu : IsUnitAt (w.under (𝓞 K)) (y * ((atFin _ (unif (w.under (𝓞 K)))) ^ f)⁻¹)`.

Unfold `IsUnitAt IsUnifAt at *`. Rewrite using `[Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, map_pow, hv, h1, h2]`. Conclude with `mul_inv_cancel₀ (pow_ne_zero _ WithZero.exp_ne_zero)`. Establish `h3` using `hχ _ hu`. Rewrite `h3` using `[map_mul, map_inv, mul_inv_eq_one, map_pow]`.

Conclude with `hy.trans h3`.
-/
theorem normChar_val {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (χ : HChar K) (w : HeightOneSpectrum (𝓞 L)) (f : ℕ) (hf : normV w = normV (w.under (𝓞 K)) ^ f)
    (hχ : χ.UnrAt (w.under (𝓞 K))) : (normChar L χ).UnrAt w ∧ (normChar L χ).val w = χ.val (w.under (𝓞 K)) ^ f := by
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, hv⟩ := normChar_loc χ w f hf x
    rw [hy]
    apply hχ
    unfold IsUnitAt at *
    rw [hv, hx, one_pow]
  · obtain ⟨y, hy, hv⟩ := normChar_loc χ w f hf (atFin w (unif w))
    have h1 := unif_spec w
    have h2 := unif_spec (w.under (𝓞 K))
    have hu : IsUnitAt (w.under (𝓞 K)) (y * ((atFin _ (unif (w.under (𝓞 K)))) ^ f)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, map_pow, hv, h1, h2]
      exact mul_inv_cancel₀ (pow_ne_zero _ WithZero.exp_ne_zero)
    have h3 := hχ _ hu
    rw [map_mul, map_inv, mul_inv_eq_one, map_pow] at h3
    exact hy.trans h3

/- English proof (translation)
Use `Units.ext (Prod.ext (funext fun u => ?_) rfl)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Pi.mulSingle w (x : w.Completion) u = GroundTheory.Global.IdeleGroup.infiniteAdeleSingle w (x : w.Completion) u`. Rewrite using `[GroundTheory.Global.IdeleGroup.infiniteAdeleSingle_apply]`.
-/
theorem infIdele_eq {K : Type} [Field K] [NumberField K] (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    ReciprocityTheory.Neutral.Bridge.HCFR.infIdele K w x = GroundTheory.Global.IdeleGroup.infiniteEmbedding w x := by
  classical
  refine Units.ext (Prod.ext (funext fun u => ?_) rfl)
  change Pi.mulSingle w (x : w.Completion) u = GroundTheory.Global.IdeleGroup.infiniteAdeleSingle w (x : w.Completion) u
  rw [GroundTheory.Global.IdeleGroup.infiniteAdeleSingle_apply]

/- English proof (translation)
Establish `hv` using `hu.comap (algebraMap K L)`. Use `show χ.1 (GroundTheory.Global.ideleNorm K L (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L u (-1))) = χ.1 (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele K (u.comap (algebraMap K L)) (-1))`. Rewrite using `[infIdele_eq, infIdele_eq, GroundTheory.Global.ideleNorm_infiniteEmbedding]`. Use `congr 2`. Apply `Units.ext` to reduce the goal to its premises.

Apply `(InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).injective` to reduce the goal to its premises. Use `GroundTheory.Global.extensionEmbeddingOfIsReal_normUnits (K := K) u hu (-1)` as an intermediate fact. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem normChar_locInf {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (χ : HChar K) (u : InfinitePlace L) (hu : u.IsReal) :
    (normChar L χ).locInf u (-1) = χ.locInf (u.comap (algebraMap K L)) (-1) := by
  have hv := hu.comap (algebraMap K L)
  show χ.1 (GroundTheory.Global.ideleNorm K L (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L u (-1))) =
    χ.1 (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele K (u.comap (algebraMap K L)) (-1))
  rw [infIdele_eq, infIdele_eq, GroundTheory.Global.ideleNorm_infiniteEmbedding]
  congr 2
  apply Units.ext
  apply (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).injective
  have := GroundTheory.Global.extensionEmbeddingOfIsReal_normUnits (K := K) u hu (-1)
  rw [this]
  simp

/- English proof (translation)
Introduce `K L _ _ _ _ _ χ s hs`. Use `⟨normChar L χ, fun u hu => (normChar_locInf χ u hu).trans (hs _ (hu.comap _)), fun u hu => ?_⟩` and prove the remaining obligations. Use `⟨(normChar_val χ u _ (normV_under u) hu).1, fun f hf => (normChar_val χ u f hf hu).2⟩` and prove the remaining obligations.
-/
theorem normCharGen : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (χ : HChar K) (s : ℂˣ), (∀ v : InfinitePlace K, v.IsReal → χ.locInf v (-1) = s) → ∃ χ' : HChar L, (∀ u : InfinitePlace L, u.IsReal → χ'.locInf u (-1) = s) ∧ ∀ u : HeightOneSpectrum (𝓞 L), χ.UnrAt (u.under (𝓞 K)) → χ'.UnrAt u ∧ ∀ f : ℕ, normV u = normV (u.under (𝓞 K)) ^ f → χ'.val u = χ.val (u.under (𝓞 K)) ^ f := by
  intro K L _ _ _ _ _ χ s hs
  refine ⟨normChar L χ, fun u hu => (normChar_locInf χ u hu).trans (hs _ (hu.comap _)), fun u hu => ?_⟩
  refine ⟨(normChar_val χ u _ (normV_under u) hu).1, fun f hf => (normChar_val χ u f hf hu).2⟩

/- English proof (translation)
Establish `h` using `HeightOneSpectrum.one_lt_absNorm_nnreal v`. Use `show 1 < Ideal.absNorm v.asIdeal`. Conclude with `h` after adjusting the coercions.
-/
theorem one_lt_normV {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : 1 < normV v := by
  have h := HeightOneSpectrum.one_lt_absNorm_nnreal v
  show 1 < Ideal.absNorm v.asIdeal
  exact_mod_cast h

/- English proof (translation)
Use `(IsCMField.complexConj_eq_self_iff M _).1 ?_` and prove the remaining obligations. Rewrite using `[conj_algebraMap, (IsCMField.complexConj_eq_self_iff E _).2 x.2]`.
-/
theorem algebraMap_mem_real {E M : Type} [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] (x : maximalRealSubfield E) : algebraMap E M x ∈ maximalRealSubfield M := by
  refine (IsCMField.complexConj_eq_self_iff M _).1 ?_
  rw [conj_algebraMap, (IsCMField.complexConj_eq_self_iff E _).2 x.2]

def realHom (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] : maximalRealSubfield E →+* maximalRealSubfield M :=
  ((algebraMap E M).comp (maximalRealSubfield E).subtype).codRestrict _ algebraMap_mem_real

/- English proof (translation)
Introduce `E M _ _ _ _ _ _ _ a χ hsign`. Use `letI : Algebra (maximalRealSubfield E) (maximalRealSubfield M) := (realHom E M).toAlgebra`. Take `⟨χ', hs, hv⟩` from `normCharGen (maximalRealSubfield E) (maximalRealSubfield M) χ ((-1) ^ a) (fun v _ => hsign v)`. Use `⟨χ', fun u => hs u (IsTotallyReal.isReal u), ?_⟩` and prove the remaining obligations. Establish `hNV` using `UpperTheory.ideleNorm_valuation_of_local_compatibility UpperTheory.ideleNorm_local_compatibility`.

Establish `hfin : ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, χ.UnrAt ((w.under (𝓞 E)).under (𝓞 (maximalRealSubfield E)))` using `(tendsto_under (K := E) (L := M)).eventually ((tendsto_under (K := maximalRealSubfield E) (L := E)).eventually (Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified χ)))`. Use `filter_upwards [hfin] with w hw`. Establish `key : (w.under (𝓞 (maximalRealSubfield M))).under (𝓞 (maximalRealSubfield E)) = (w.under (𝓞 E)).under (𝓞 (maximalRealSubfield E))`. Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(w.asIdeal.comap _).comap _ = (w.asIdeal.comap _).comap _`.

Rewrite using `[Ideal.comap_comap, Ideal.comap_comap]`. Use `congr 1`. Take `⟨hu1, hu2⟩` from `hv (w.under (𝓞 (maximalRealSubfield M))) (by rw [key]; exact hw)`. Take `⟨hw1, hw2⟩` from `hNV M χ' w _ (normV_under w) hu1`. Take `⟨-, hv2⟩` from `hNV E χ (w.under (𝓞 E)) _ (normV_under _) hw`.

Use `⟨hw1, fun f hf => ?_⟩` and prove the remaining obligations. Rewrite using `[hw2, hu2 _ (normV_under _), hv2, key, ← pow_mul, ← pow_mul]`. Use `congr 1`. Use `Nat.pow_right_injective (one_lt_normV ((w.under (𝓞 E)).under (𝓞 (maximalRealSubfield E)))) ?_` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[pow_mul, pow_mul, ← key, ← normV_under, ← normV_under, key, ← normV_under, ← hf]`.
-/
theorem charLift : ∀ (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M] [Algebra E M] (a : ℕ) (χ : HChar (maximalRealSubfield E)), (∀ v : InfinitePlace (maximalRealSubfield E), χ.locInf v (-1) = (-1) ^ a) → ∃ χ' : HChar (maximalRealSubfield M), (∀ u : InfinitePlace (maximalRealSubfield M), χ'.locInf u (-1) = (-1) ^ a) ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, (compNorm M χ').UnrAt w ∧ ∀ f : ℕ, normV w = normV (w.under (𝓞 E)) ^ f → (compNorm M χ').val w = (compNorm E χ).val (w.under (𝓞 E)) ^ f := by
  intro E M _ _ _ _ _ _ _ a χ hsign
  letI : Algebra (maximalRealSubfield E) (maximalRealSubfield M) := (realHom E M).toAlgebra
  obtain ⟨χ', hs, hv⟩ := normCharGen (maximalRealSubfield E) (maximalRealSubfield M) χ ((-1) ^ a) (fun v _ => hsign v)
  refine ⟨χ', fun u => hs u (IsTotallyReal.isReal u), ?_⟩
  have hNV := UpperTheory.ideleNorm_valuation_of_local_compatibility UpperTheory.ideleNorm_local_compatibility
  have hfin : ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite,
      χ.UnrAt ((w.under (𝓞 E)).under (𝓞 (maximalRealSubfield E))) :=
    (tendsto_under (K := E) (L := M)).eventually ((tendsto_under (K := maximalRealSubfield E) (L := E)).eventually
      (Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified χ)))
  filter_upwards [hfin] with w hw
  have key : (w.under (𝓞 (maximalRealSubfield M))).under (𝓞 (maximalRealSubfield E)) =
      (w.under (𝓞 E)).under (𝓞 (maximalRealSubfield E)) := by
    apply HeightOneSpectrum.ext
    change (w.asIdeal.comap _).comap _ = (w.asIdeal.comap _).comap _
    rw [Ideal.comap_comap, Ideal.comap_comap]
    congr 1
  obtain ⟨hu1, hu2⟩ := hv (w.under (𝓞 (maximalRealSubfield M))) (by rw [key]; exact hw)
  obtain ⟨hw1, hw2⟩ := hNV M χ' w _ (normV_under w) hu1
  obtain ⟨-, hv2⟩ := hNV E χ (w.under (𝓞 E)) _ (normV_under _) hw
  refine ⟨hw1, fun f hf => ?_⟩
  rw [hw2, hu2 _ (normV_under _), hv2, key, ← pow_mul, ← pow_mul]
  congr 1
  refine Nat.pow_right_injective (one_lt_normV ((w.under (𝓞 E)).under (𝓞 (maximalRealSubfield E)))) ?_
  simp only
  rw [pow_mul, pow_mul, ← key, ← normV_under, ← normV_under, key, ← normV_under, ← hf]

/- English proof (translation)
Introduce `hF hJ hG E M _ _ _ _ _ _ _ l a ha π χ P hL hS`. Take `⟨hreg, hpol, -⟩` from `hS`. Use `⟨?_, fun wt hw τ => ?_⟩` and prove the remaining obligations. Take `⟨χ', hsign, hev⟩` from `charLift E M a χ hpol.sign`. Use `⟨χ', (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, ⟨hsign, ?_⟩, trivial⟩` and prove the remaining obligations.

Rewrite using `[hL.inf τ]`. Conclude with `(GlobalTheory.CuspRep.CG.isRegAlg_iff _).1 hreg _`. Use `UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse hJ hG M a ha P (compNorm M χ') ?_` and prove the remaining obligations. Establish `hsd` using `GlobalTheory.T.polarizedPair_satakeParameter_conjugatePlace hF E a π χ hpol`. Establish `hun` using `GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hF E a π`.

Use `filter_upwards [hev, (tendsto_under (K := E) (L := M)).eventually (hsd.and hun)] with w ⟨hu, hval⟩ ⟨hs, B, hB⟩`. Establish `e1` using `cPl_under (E := E) w`. Establish `e2` using `normV_cPl w`. Establish `e3` using `normV_cPl (w.under (𝓞 E))`. Establish `hf` using `normV_under (K := E) w`.

Use `set f := w.asIdeal.inertiaDeg (𝓞 E)`. Establish `hB0 : (CG.mk π).HasSat (w.under (𝓞 E)) B` using `(CG.hasSat_mk _ _ _).2 hB`. Establish `h1` using `hL.sat w f B hf hB0`. Establish `h2` using `hL.sat (UpperTheory.V.Af.Bc.cPl w) f _ (by rw [e1, e2, e3]; exact hf) (e1 ▸ hs B hB0)`. Use `⟨hu, _, _, h1, h2, ?_⟩` and prove the remaining obligations.

Rewrite using `[hval f hf]`. Simplify using `only [Multiset.map_map, Function.comp_def, mul_pow, inv_pow, mul_inv, inv_inv]`. Rewrite using `[hL.inf, hL.inf]`. Establish `e : (τ.comp (IsCMField.complexConj M).toRingEquiv.toRingHom).comp (algebraMap E M) = (τ.comp (algebraMap E M)).comp (IsCMField.complexConj E).toRingEquiv.toRingHom` using `RingHom.ext fun x => congrArg τ (conj_algebraMap x)`. Rewrite using `[e]`.

Conclude with `hw _`.
-/
theorem main : AutomorphicFormsFiniteGL → JacquetShalikaRigidity → GelfandKazhdanDual → ∀ (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M] [Algebra E M] (l a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)) (P : CuspSub M a), IsLift π P → InScope .all l π χ → (∃ χ' : HChar (maximalRealSubfield M), InScope .all l P χ') ∧ ∀ wt : ℤ, IsWeight π wt → IsWeight P wt := by
  intro hF hJ hG E M _ _ _ _ _ _ _ l a ha π χ P hL hS
  obtain ⟨hreg, hpol, -⟩ := hS
  refine ⟨?_, fun wt hw τ => ?_⟩
  · obtain ⟨χ', hsign, hev⟩ := charLift E M a χ hpol.sign
    refine ⟨χ', (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, ⟨hsign, ?_⟩, trivial⟩
    · rw [hL.inf τ]
      exact (GlobalTheory.CuspRep.CG.isRegAlg_iff _).1 hreg _
    refine UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse hJ hG M a ha P (compNorm M χ') ?_
    have hsd := GlobalTheory.T.polarizedPair_satakeParameter_conjugatePlace hF E a π χ hpol
    have hun := GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hF E a π
    filter_upwards [hev, (tendsto_under (K := E) (L := M)).eventually (hsd.and hun)] with w ⟨hu, hval⟩ ⟨hs, B, hB⟩
    have e1 := cPl_under (E := E) w
    have e2 := normV_cPl w
    have e3 := normV_cPl (w.under (𝓞 E))
    have hf := normV_under (K := E) w
    set f := w.asIdeal.inertiaDeg (𝓞 E)
    have hB0 : (CG.mk π).HasSat (w.under (𝓞 E)) B := (CG.hasSat_mk _ _ _).2 hB
    have h1 := hL.sat w f B hf hB0
    have h2 := hL.sat (UpperTheory.V.Af.Bc.cPl w) f _ (by rw [e1, e2, e3]; exact hf) (e1 ▸ hs B hB0)
    refine ⟨hu, _, _, h1, h2, ?_⟩
    rw [hval f hf]
    simp only [Multiset.map_map, Function.comp_def, mul_pow, inv_pow, mul_inv, inv_inv]
  · rw [hL.inf, hL.inf]
    have e : (τ.comp (IsCMField.complexConj M).toRingEquiv.toRingHom).comp (algebraMap E M) =
        (τ.comp (algebraMap E M)).comp (IsCMField.complexConj E).toRingEquiv.toRingHom :=
      RingHom.ext fun x => congrArg τ (conj_algebraMap x)
    rw [e]
    exact hw _

end GlobalTheory.LiftPolar

end
