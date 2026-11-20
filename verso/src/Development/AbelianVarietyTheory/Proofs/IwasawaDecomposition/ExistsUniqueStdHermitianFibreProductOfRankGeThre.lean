import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyLocalDensityStandardLatticeBoundStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreFamilyHermitianQuadraticFormAtUnitProps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFibreFamilyHermitianLengthInfiniteAdelesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNiceLocalFieldProductRingInfiniteAdelesComplet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductMeasureBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsRestrictedProductTupleMeasureStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSelfDualLatticeIff
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CountableIdealSummableAbsNormRpow

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

/- English proof (translation)
Unfold `tupMeas`. Use `haveI : (Measure.pi fun _ : Fin M => lam).IsAddHaarMeasure := inferInstance`. Use `infer_instance`.
-/
theorem isAddHaarMeasure_tupMeas_of_lc {S : Type} [AddCommGroup S] [TopologicalSpace S]
    [IsTopologicalAddGroup S] [LocallyCompactSpace S] [SecondCountableTopology S]
    [MeasurableSpace S] [BorelSpace S] (lam : Measure S) (h : lam.IsAddHaarMeasure) (n M : ℕ) :
    (tupMeas lam n M).IsAddHaarMeasure := by
  unfold tupMeas
  haveI : (Measure.pi fun _ : Fin M => lam).IsAddHaarMeasure := inferInstance
  infer_instance

/- English proof (translation)
Use extensionality with `c`. Simplify using `only [Set.mem_setOf_eq]`. Use `(Pi.isUnit_iff (x := c)).trans (forall_congr' fun w => isUnit_iff_ne_zero)` and prove the remaining obligations.
-/
theorem setOf_isUnit_ainf (F : Type) [Field F] [NumberField F] :
    {c : Ainf F | IsUnit c} = {c : Ainf F | ∀ w, c w ≠ 0} := by
  ext c
  simp only [Set.mem_setOf_eq]
  refine (Pi.isUnit_iff (x := c)).trans (forall_congr' fun w => isUnit_iff_ne_zero)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ d b s M J β hM hJ hβ`. Establish `hM1 : 1 ≤ M` using `by omega`. Take `⟨nI, nV⟩` from `GlobalTheory.GaugeEx.nice_ainf_fv F`. Establish `uI : IsUnit (algebraMap F (Ainf F) β)` using `(isUnit_iff_ne_zero.2 hβ).map _`. Establish `uV : ∀ v, IsUnit (algebraMap F (Fv F v) β)` using `fun v => (isUnit_iff_ne_zero.2 hβ).map _`.

Establish `bI` using `fun m => GlobalTheory.GaugeEx.FibBasic.fibAt_basic F E σ (Ainf F) nI M J (tupMeas s.lamI 1 M) s.nuI _ m s.haar_nuI uI`. Establish `bV` using `fun v m => GlobalTheory.GaugeEx.FibBasic.fibAt_basic F E σ (Fv F v) (nV v) M J (tupMeas (s.lamV v) 1 M) (s.nuV v) _ m (s.haar_nuV v) (uV v)`. Choose the witnesses or unpack the hypotheses as in `⟨mi, hmi⟩ : ∃ mi, FibAt (Ainf F) σ J (tupMeas s.lamI 1 M) s.nuI (algebraMap F _ β) mi := by`. Take `⟨fib, hfib⟩` from `GlobalTheory.T.exists_fibreFamily_hermitianLength_infiniteAdeles F E σ hσ M J (tupMeas s.lamI 1 M) s.nuI hM1 hJ (isAddHaarMeasure_tupMeas_of_lc _ s.haar_lamI 1 M) s.haar_nuI`. Conclude with `⟨_, fib, by rw [setOf_isUnit_ainf]; exact hfib, rfl⟩`.

Establish `hex : ∀ v, ∃ m, FibAt (Fv F v) σ J (tupMeas (s.lamV v) 1 M) (s.nuV v) (algebraMap F _ β) m`. Introduce `v`. Take `⟨-, fib, hfib⟩` from `GlobalTheory.LocalDensityCompare.null_and_exists v σ J hσ hM1 hJ (tupMeas (s.lamV v) 1 M) (isAddHaarMeasure_tupMeas_of_lc _ (s.haar_lamV v) 1 M) (s.nuV v) (s.haar_nuV v)`. Use `⟨_, fib, ?_, rfl⟩` and prove the remaining obligations. Simplify using `only [isUnit_iff_ne_zero]`.

Conclude with `hfib`. Use `choose mv hmv using hex`. Establish `hconv : Conv b mi mv`. Use `⟨(bI mi hmi).2.1, fun v => (bV v _ (hmv v)).2.1, ?_⟩` and prove the remaining obligations. Establish `hs` using `((GlobalTheory.countable_ideal_and_summable_absNorm_rpow F).2 2 (by norm_num)).2`.

Use `Summable.of_norm_bounded_eventually hs ?_` and prove the remaining obligations. Use `filter_upwards [GlobalTheory.T.eventually_localDensity_standardLattice_bound F E σ hσ d b s M J β hM1 hJ hβ] with v hv`. Establish `h` using `hv _ (hmv v)`. Establish `hq : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ)`. Establish `: Ideal.absNorm v.asIdeal ≠ 0`.

Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`. Conclude with `Nat.one_le_iff_ne_zero.2 this` after adjusting the coercions. Use `set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ)`. Use `set a : ℝ := |(mv v (latV b v)).toReal - 1|`.

Establish `ha : 0 ≤ a` using `abs_nonneg _`. Establish `hq0 : 0 < q` using `by linarith`. Establish `h3 : a * q ^ 3 ≤ q` using `(mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq hM) ha).trans h`. Establish `h2 : a * q ^ 2 ≤ 1`. Use `le_of_mul_le_mul_right ?_ hq0` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.norm_of_nonneg ha, Real.rpow_neg hq0.le, Real.rpow_two, ← one_div, le_div_iff₀ (by positivity)]`. Conclude with `h2`. Take `⟨ν, hν⟩` from `GlobalTheory.T.exists_isRestrictedProductTupleMeasure F E d b 1 M mi mv hconv`. Use `⟨ν, ⟨mi, mv, hmi, hmv, hν⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `ν' ⟨mi', mv', hmi', hmv', hν'⟩`. Take `rfl : mi' = mi` from `(bI mi hmi).2.2 _ hmi'`. Take `rfl : mv' = mv` from `funext fun v => (bV v _ (hmv v)).2.2 _ (hmv' v)`. Conclude with `(GlobalTheory.T.restrictedProductMeasure_basic_properties F E d b 1 M ν _ _ hν).2.2.1 _ hν'`.
-/
theorem existsUnique_isStdX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (β : F), 3 ≤ M → IsHermND σ J → β ≠ 0 → ∃! ν, IsStdX s σ J β ν := by
  intro F E _ _ _ _ _ σ hσ d b s M J β hM hJ hβ
  have hM1 : 1 ≤ M := by omega
  obtain ⟨nI, nV⟩ := GlobalTheory.GaugeEx.nice_ainf_fv F
  have uI : IsUnit (algebraMap F (Ainf F) β) := (isUnit_iff_ne_zero.2 hβ).map _
  have uV : ∀ v, IsUnit (algebraMap F (Fv F v) β) := fun v => (isUnit_iff_ne_zero.2 hβ).map _
  have bI := fun m => GlobalTheory.GaugeEx.FibBasic.fibAt_basic F E σ (Ainf F) nI M J (tupMeas s.lamI 1 M) s.nuI _ m s.haar_nuI uI
  have bV := fun v m => GlobalTheory.GaugeEx.FibBasic.fibAt_basic F E σ (Fv F v) (nV v) M J (tupMeas (s.lamV v) 1 M) (s.nuV v) _ m
    (s.haar_nuV v) (uV v)
  obtain ⟨mi, hmi⟩ : ∃ mi, FibAt (Ainf F) σ J (tupMeas s.lamI 1 M) s.nuI (algebraMap F _ β) mi := by
    obtain ⟨fib, hfib⟩ := GlobalTheory.T.exists_fibreFamily_hermitianLength_infiniteAdeles F E σ hσ M J (tupMeas s.lamI 1 M) s.nuI hM1 hJ
      (isAddHaarMeasure_tupMeas_of_lc _ s.haar_lamI 1 M) s.haar_nuI
    exact ⟨_, fib, by rw [setOf_isUnit_ainf]; exact hfib, rfl⟩
  have hex : ∀ v, ∃ m, FibAt (Fv F v) σ J (tupMeas (s.lamV v) 1 M) (s.nuV v) (algebraMap F _ β) m := by
    intro v
    obtain ⟨-, fib, hfib⟩ := GlobalTheory.LocalDensityCompare.null_and_exists v σ J hσ hM1 hJ
      (tupMeas (s.lamV v) 1 M) (isAddHaarMeasure_tupMeas_of_lc _ (s.haar_lamV v) 1 M) (s.nuV v)
      (s.haar_nuV v)
    refine ⟨_, fib, ?_, rfl⟩
    simp only [isUnit_iff_ne_zero]
    exact hfib
  choose mv hmv using hex
  have hconv : Conv b mi mv := by
    refine ⟨(bI mi hmi).2.1, fun v => (bV v _ (hmv v)).2.1, ?_⟩
    have hs := ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow F).2 2 (by norm_num)).2
    refine Summable.of_norm_bounded_eventually hs ?_
    filter_upwards [GlobalTheory.T.eventually_localDensity_standardLattice_bound F E σ hσ d b s M J β hM1 hJ hβ] with v hv
    have h := hv _ (hmv v)
    have hq : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
      have : Ideal.absNorm v.asIdeal ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
      exact_mod_cast Nat.one_le_iff_ne_zero.2 this
    set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ)
    set a : ℝ := |(mv v (latV b v)).toReal - 1|
    have ha : 0 ≤ a := abs_nonneg _
    have hq0 : 0 < q := by linarith
    have h3 : a * q ^ 3 ≤ q := (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq hM) ha).trans h
    have h2 : a * q ^ 2 ≤ 1 := by
      refine le_of_mul_le_mul_right ?_ hq0
      calc a * q ^ 2 * q = a * q ^ 3 := by ring
        _ ≤ 1 * q := by rw [one_mul]; exact h3
    rw [Real.norm_of_nonneg ha, Real.rpow_neg hq0.le, Real.rpow_two, ← one_div,
      le_div_iff₀ (by positivity)]
    exact h2
  obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_isRestrictedProductTupleMeasure F E d b 1 M mi mv hconv
  refine ⟨ν, ⟨mi, mv, hmi, hmv, hν⟩, ?_⟩
  rintro ν' ⟨mi', mv', hmi', hmv', hν'⟩
  obtain rfl : mi' = mi := (bI mi hmi).2.2 _ hmi'
  obtain rfl : mv' = mv := funext fun v => (bV v _ (hmv v)).2.2 _ (hmv' v)
  exact (GlobalTheory.T.restrictedProductMeasure_basic_properties F E d b 1 M ν _ _ hν).2.2.1 _ hν'

end GlobalTheory.GaugeEx
