import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Discrepancy

/- English proof (translation)
Introduce `X _ _ p hp y hy f hf`. Use `haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1`. Take `⟨U, hU, hx, -⟩` from `exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial`. Use `haveI : Nonempty U := ⟨⟨y, hx⟩⟩`. Use `letI := X.presheaf.algebra_section_stalk (⟨y, hx⟩ : U)`.

Use `haveI := hU.isLocalization_stalk ⟨y, hx⟩`. Use `(mem_range_algebraMap_iff_forall_height_eq_one (A := X.presheaf.stalk y) f).2 fun q hq h1 => ?_` and prove the remaining obligations. Set `P : PrimeSpectrum Γ(X, U)` to `⟨q.comap (algebraMap _ (X.presheaf.stalk y)), inferInstance⟩`. Establish `hP1 : P.asIdeal.height = 1` using `(IsLocalization.height_comap (hU.primeIdealOf ⟨y, hx⟩).asIdeal.primeCompl q).trans h1`. Establish `hPQ : P ≤ hU.primeIdealOf ⟨y, hx⟩` using `fun s hs => by_contra fun hs' => hq.ne_top (q.eq_top_of_isUnit_mem hs (IsLocalization.map_units (X.presheaf.stalk y) (⟨s, hs'⟩ : (hU.primeIdealOf ⟨y, hx⟩).asIdeal.primeCompl)))`.

Establish `hz : hU.fromSpec P ∈ U`. Establish `: hU.fromSpec P ∈ Set.range hU.fromSpec` using `⟨P, rfl⟩`. Rewrite `this` using `[hU.range_fromSpec]`. Then use the resulting hypothesis. Set `z : U` to `⟨hU.fromSpec P, hz⟩`. Establish `hP : hU.primeIdealOf z = P` using `hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)`.

Establish `hzx : (z : X) ⤳ y`. Establish `h` using `((PrimeSpectrum.le_iff_specializes P (hU.primeIdealOf ⟨y, hx⟩)).mp hPQ).map hU.fromSpec.continuous`. Rewrite `h` using `[hU.fromSpec_primeIdealOf ⟨y, hx⟩]`. Then use the resulting hypothesis. Use `clear_value z`. Use `haveI := hU.isLocalization_stalk z`.

Establish `hc : Order.coheight (z : X) = 1`. Use `IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf z).asIdeal (X.presheaf.stalk (z : X))` as an intermediate fact. Rewrite `this` using `[ringKrullDim_stalk_eq_coheight, hP, hP1]`. Conclude with `this` after adjusting the coercions. Use `haveI hT : IsLocalization.AtPrime (Localization.AtPrime q) P.asIdeal := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (hU.primeIdealOf ⟨y, hx⟩).asIdeal.primeCompl (Localization.AtPrime q) q`.

Use `haveI : IsIntegrallyClosed (Localization.AtPrime q) := isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors`. Establish `hs : (hU.primeIdealOf z).asIdeal.primeCompl = P.asIdeal.primeCompl`. Use extensionality with `s`. Rewrite using `[Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hP]`. Use `haveI hZ : IsLocalization P.asIdeal.primeCompl (X.presheaf.stalk (z : X)) := by`.

Rewrite using `[← hs]`. Conclude with `hU.isLocalization_stalk z`. Set `e : X.presheaf.stalk (z : X) ≃+* Localization.AtPrime q` to `(IsLocalization.algEquiv P.asIdeal.primeCompl (X.presheaf.stalk (z : X)) (Localization.AtPrime q)).toRingEquiv`. Use `haveI : IsIntegrallyClosed (X.presheaf.stalk (z : X)) := ((IsNormalScheme.isDomain_and_isIntegrallyClosed_iff_of_ringEquiv e).2 ⟨inferInstance, inferInstance⟩).2`. Use `haveI : IsDiscreteValuationRing (X.presheaf.stalk (z : X)) := by`.

Establish `h1 : Ring.KrullDimLE 1 (X.presheaf.stalk (z : X))` using `krullDimLE_of_coheight_le hc.le`. Establish `hf : ¬ IsField (X.presheaf.stalk (z : X))` using `fun h => by`. Use `ringKrullDim_eq_zero_of_isField h` as an intermediate fact. Rewrite `this` using `[ringKrullDim_stalk_eq_coheight, hc]`. Simplify using `at this`.

Establish `hm` using `IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hf`. Establish `h3 : IsIntegrallyClosed (X.presheaf.stalk (z : X)) ∧ ∃! P : Ideal (X.presheaf.stalk (z : X)), P ≠ ⊥ ∧ P.IsPrime` using `⟨inferInstance, _, ⟨hm, inferInstance⟩, fun P hP => IsLocalRing.eq_maximalIdeal (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h1 P hP.1 hP.2)⟩`. Conclude with `((IsDiscreteValuationRing.TFAE (X.presheaf.stalk (z : X)) hf).out 0 3).mpr h3`. Take `⟨E, hE⟩` from `DivOver.exists_isAt p (z : X)`. Take `⟨a, rfl⟩` from `(hE f).1 (hf z hzx E hE)`.

Take `⟨⟨c, s⟩, e⟩` from `IsLocalization.surj (hU.primeIdealOf z).asIdeal.primeCompl a`. Use `(mem_primeLocalSubalgebra_iff q _).2 ⟨algebraMap _ _ s.1, ?_, algebraMap _ _ c, ?_⟩` and prove the remaining obligations. Use `s.2` as an intermediate fact. Rewrite `this` using `[Ideal.mem_primeCompl_iff]`. Establish `h' : s.1 ∉ P.asIdeal` using `by simpa only [hP] using this`.

Conclude with `h'`. Establish `e'` using `congrArg (algebraMap _ X.functionField) e`. Rewrite `e'` using `[map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`. Rewrite using `[Algebra.smul_def, mul_comm]`. Conclude with `((algebraMap_germ hx c).trans e'.symm).trans (congrArg _ (algebraMap_germ hx s.1).symm)`.
-/
theorem regAt_of_isIntegrallyClosed_stalk : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y) → ∀ f : X.functionField, (∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z → f ∈ E.ring) → RegAt y f := by
  intro X _ _ p hp y hy f hf
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨y, hx⟩⟩
  letI := X.presheaf.algebra_section_stalk (⟨y, hx⟩ : U)
  haveI := hU.isLocalization_stalk ⟨y, hx⟩
  refine (mem_range_algebraMap_iff_forall_height_eq_one (A := X.presheaf.stalk y) f).2
    fun q hq h1 => ?_
  let P : PrimeSpectrum Γ(X, U) := ⟨q.comap (algebraMap _ (X.presheaf.stalk y)), inferInstance⟩
  have hP1 : P.asIdeal.height = 1 :=
    (IsLocalization.height_comap (hU.primeIdealOf ⟨y, hx⟩).asIdeal.primeCompl q).trans h1
  have hPQ : P ≤ hU.primeIdealOf ⟨y, hx⟩ := fun s hs => by_contra fun hs' =>
    hq.ne_top (q.eq_top_of_isUnit_mem hs (IsLocalization.map_units (X.presheaf.stalk y)
      (⟨s, hs'⟩ : (hU.primeIdealOf ⟨y, hx⟩).asIdeal.primeCompl)))
  have hz : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  let z : U := ⟨hU.fromSpec P, hz⟩
  have hP : hU.primeIdealOf z = P :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)
  have hzx : (z : X) ⤳ y := by
    have h := ((PrimeSpectrum.le_iff_specializes P (hU.primeIdealOf ⟨y, hx⟩)).mp hPQ).map
      hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf ⟨y, hx⟩] at h
  clear_value z
  haveI := hU.isLocalization_stalk z
  have hc : Order.coheight (z : X) = 1 := by
    have := IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf z).asIdeal
      (X.presheaf.stalk (z : X))
    rw [ringKrullDim_stalk_eq_coheight, hP, hP1] at this
    exact_mod_cast this

  haveI hT : IsLocalization.AtPrime (Localization.AtPrime q) P.asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (hU.primeIdealOf ⟨y, hx⟩).asIdeal.primeCompl (Localization.AtPrime q) q
  haveI : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
  have hs : (hU.primeIdealOf z).asIdeal.primeCompl = P.asIdeal.primeCompl := by
    ext s; rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hP]
  haveI hZ : IsLocalization P.asIdeal.primeCompl (X.presheaf.stalk (z : X)) := by
    rw [← hs]; exact hU.isLocalization_stalk z
  let e : X.presheaf.stalk (z : X) ≃+* Localization.AtPrime q :=
    (IsLocalization.algEquiv P.asIdeal.primeCompl (X.presheaf.stalk (z : X))
      (Localization.AtPrime q)).toRingEquiv
  haveI : IsIntegrallyClosed (X.presheaf.stalk (z : X)) :=
    ((IsNormalScheme.isDomain_and_isIntegrallyClosed_iff_of_ringEquiv e).2
      ⟨inferInstance, inferInstance⟩).2
  haveI : IsDiscreteValuationRing (X.presheaf.stalk (z : X)) := by
    have h1 : Ring.KrullDimLE 1 (X.presheaf.stalk (z : X)) := krullDimLE_of_coheight_le hc.le
    have hf : ¬ IsField (X.presheaf.stalk (z : X)) := fun h => by
      have := ringKrullDim_eq_zero_of_isField h
      rw [ringKrullDim_stalk_eq_coheight, hc] at this
      simp at this
    have hm := IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hf
    have h3 : IsIntegrallyClosed (X.presheaf.stalk (z : X)) ∧
        ∃! P : Ideal (X.presheaf.stalk (z : X)), P ≠ ⊥ ∧ P.IsPrime :=
      ⟨inferInstance, _, ⟨hm, inferInstance⟩, fun P hP => IsLocalRing.eq_maximalIdeal
        (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h1 P hP.1 hP.2)⟩
    exact ((IsDiscreteValuationRing.TFAE (X.presheaf.stalk (z : X)) hf).out 0 3).mpr h3
  obtain ⟨E, hE⟩ := DivOver.exists_isAt p (z : X)
  obtain ⟨a, rfl⟩ := (hE f).1 (hf z hzx E hE)
  obtain ⟨⟨c, s⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf z).asIdeal.primeCompl a
  refine (mem_primeLocalSubalgebra_iff q _).2 ⟨algebraMap _ _ s.1, ?_, algebraMap _ _ c, ?_⟩
  · have := s.2
    rw [Ideal.mem_primeCompl_iff] at this
    have h' : s.1 ∉ P.asIdeal := by simpa only [hP] using this
    exact h'
  · have e' := congrArg (algebraMap _ X.functionField) e
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at e'
    rw [Algebra.smul_def, mul_comm]
    exact ((algebraMap_germ hx c).trans e'.symm).trans (congrArg _ (algebraMap_germ hx s.1).symm)

end GlobalTheory.Discrepancy
