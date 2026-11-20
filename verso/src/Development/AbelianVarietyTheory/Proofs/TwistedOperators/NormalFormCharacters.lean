import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.AlgValsFinMain
import Formalism.LocalToGlobal.UnitaryNorms.CharHost
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUniformiserValueIsAlgebraicStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharLocalValueDivUniformiserPowStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNumberFieldValuesInEtaCharHalfTwistStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.RowExNF

open Formalism.L2.Host

/- English proof (translation)
Use `Finset.induction_on s (by simp) ?_` and prove the remaining obligations. Introduce `j s hj ih`. Rewrite using `[Finset.sum_insert hj, Finset.prod_insert hj, zpow_add₀ hz, ih]`.
-/
theorem zpow_sum_ne {ι : Type} {z : ℂ} (hz : z ≠ 0) (s : Finset ι) (f : ι → ℤ) :
    z ^ (∑ i ∈ s, f i) = ∏ i ∈ s, z ^ f i := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro j s hj ih
  rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add₀ hz, ih]

/- English proof (translation)
Establish `h1 : starRingEnd ℂ z ≠ 0` using `by simpa using hz`. Establish `h2 : ((‖z‖ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast norm_ne_zero_iff.2 hz`. Establish `h3 : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * starRingEnd ℂ z`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[zpow_two, div_mul_div_comm, ← pow_two, ← pow_two, h3]`. Clear the denominators using the available nonvanishing facts.
-/
theorem sq_div_norm {z : ℂ} (hz : z ≠ 0) : (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 : ℤ) = z / starRingEnd ℂ z := by
  have h1 : starRingEnd ℂ z ≠ 0 := by simpa using hz
  have h2 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  have h3 : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * starRingEnd ℂ z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [zpow_two, div_mul_div_comm, ← pow_two, ← pow_two, h3]
  field_simp

/- English proof (translation)
Use `⟨fun ψ => ∑ i, ((if φ i = ψ then a i else 0) - (if (starRingEnd ℂ).comp (φ i) = ψ then a i else 0)), fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[h k]`. Repeatedly rewrite using `[hn]`. Establish `hne : ∀ ψ : L →+* ℂ, ψ (k : L) ≠ 0` using `fun ψ => by simp`. Establish `e1 : ∀ ψ : L →+* ℂ, ψ (k : L) ^ (∑ i, ((if φ i = ψ then a i else 0) - (if (starRingEnd ℂ).comp (φ i) = ψ then a i else 0))) = ∏ i, (ψ (k : L) ^ (if φ i = ψ then a i else 0) * (ψ (k : L) ^ (if (starRingEnd ℂ).comp (φ i) = ψ then a i else 0))⁻¹)`.

Introduce `ψ`. Rewrite using `[zpow_sum_ne (hne ψ)]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[zpow_sub₀ (hne ψ), div_eq_mul_inv]`. Repeatedly rewrite using `[e1]`.

Rewrite using `[Finset.prod_comm]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_inv_distrib]`. Establish `p1 : ∏ ψ : L →+* ℂ, ψ (k : L) ^ (if φ i = ψ then a i else 0) = φ i (k : L) ^ a i`. Rewrite using `[Finset.prod_eq_single (φ i) (fun b _ hb => by rw [if_neg (Ne.symm hb), zpow_zero]) (by simp), if_pos rfl]`.

Establish `p2 : ∏ ψ : L →+* ℂ, ψ (k : L) ^ (if (starRingEnd ℂ).comp (φ i) = ψ then a i else 0) = (starRingEnd ℂ (φ i (k : L))) ^ a i`. Rewrite using `[Finset.prod_eq_single ((starRingEnd ℂ).comp (φ i)) (fun b _ hb => by rw [if_neg (Ne.symm hb), zpow_zero]) (by simp), if_pos rfl, RingHom.comp_apply]`. Rewrite using `[p1, p2, zpow_mul, sq_div_norm (hne _), div_zpow, div_eq_mul_inv]`.
-/
theorem algType_of_hasInf {L : Type} [Field L] [NumberField L] {I : Type} [Fintype I] (φ : I → L →+* ℂ) (a : I → ℤ)
    (χ : HChar L) {n : I → ℤ} (h : χ.HasInf φ n) (hn : ∀ i, n i = 2 * a i) :
    ∃ m : (L →+* ℂ) → ℤ, ∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ ψ : L →+* ℂ, ψ (k : L) ^ m ψ := by
  classical
  refine ⟨fun ψ => ∑ i, ((if φ i = ψ then a i else 0) - (if (starRingEnd ℂ).comp (φ i) = ψ then a i else 0)), fun k => ?_⟩
  rw [h k]
  simp_rw [hn]
  have hne : ∀ ψ : L →+* ℂ, ψ (k : L) ≠ 0 := fun ψ => by simp
  have e1 : ∀ ψ : L →+* ℂ, ψ (k : L) ^ (∑ i, ((if φ i = ψ then a i else 0) - (if (starRingEnd ℂ).comp (φ i) = ψ then a i else 0))) =
      ∏ i, (ψ (k : L) ^ (if φ i = ψ then a i else 0) * (ψ (k : L) ^ (if (starRingEnd ℂ).comp (φ i) = ψ then a i else 0))⁻¹) := by
    intro ψ
    rw [zpow_sum_ne (hne ψ)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [zpow_sub₀ (hne ψ), div_eq_mul_inv]
  simp_rw [e1]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have p1 : ∏ ψ : L →+* ℂ, ψ (k : L) ^ (if φ i = ψ then a i else 0) = φ i (k : L) ^ a i := by
    rw [Finset.prod_eq_single (φ i) (fun b _ hb => by rw [if_neg (Ne.symm hb), zpow_zero]) (by simp), if_pos rfl]
  have p2 : ∏ ψ : L →+* ℂ, ψ (k : L) ^ (if (starRingEnd ℂ).comp (φ i) = ψ then a i else 0) =
      (starRingEnd ℂ (φ i (k : L))) ^ a i := by
    rw [Finset.prod_eq_single ((starRingEnd ℂ).comp (φ i)) (fun b _ hb => by rw [if_neg (Ne.symm hb), zpow_zero]) (by simp),
      if_pos rfl, RingHom.comp_apply]
  rw [p1, p2, zpow_mul, sq_div_norm (hne _), div_zpow, div_eq_mul_inv]

end GlobalTheory.RowExNF

namespace GlobalTheory.RowExNF

open Formalism.L2.Host

/- English proof (translation)
Set `S : Finset ℂ` to `(Polynomial.nthRoots n (1 : ℂ)).toFinset`. Establish `hint : ∀ z ∈ (S : Set ℂ), IsIntegral ℚ z` using `fun z hz => by`. Establish `hz' : z ^ n = 1`. Simplify `hz` using `[S, Polynomial.mem_nthRoots hn]`. Use `⟨Polynomial.X ^ n - 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', ?_⟩` and prove the remaining obligations.

Simplify using `[hz']`. Use `haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (S : Set ℂ)) := IntermediateField.finiteDimensional_adjoin hint`. Use `⟨IntermediateField.adjoin ℚ (S : Set ℂ), inferInstance, fun w x => IntermediateField.subset_adjoin _ _ ?_⟩` and prove the remaining obligations. Establish `e : ((χ ^ n).loc w x) = (χ.loc w x) ^ n`. Simplify using `[HChar.loc, MonoidHom.pow_apply]`.

Establish `e1 : ((χ.loc w x : ℂˣ) : ℂ) ^ n = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, ← e, show χ ^ n = 1 from h]`. Both sides reduce to the same expression. Simplify `e1` using `[S, Polynomial.mem_nthRoots hn]`.
-/
theorem locIn_fin {L : Type} [Field L] [NumberField L] (χ : HChar L) (n : ℕ) (hn : 0 < n) (h : χ.OrderDvd n) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ w x, ((χ.loc w x : ℂˣ) : ℂ) ∈ M := by
  classical
  let S : Finset ℂ := (Polynomial.nthRoots n (1 : ℂ)).toFinset
  have hint : ∀ z ∈ (S : Set ℂ), IsIntegral ℚ z := fun z hz => by
    have hz' : z ^ n = 1 := by
      simpa [S, Polynomial.mem_nthRoots hn] using hz
    refine ⟨Polynomial.X ^ n - 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', ?_⟩
    simp [hz']
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (S : Set ℂ)) :=
    IntermediateField.finiteDimensional_adjoin hint
  refine ⟨IntermediateField.adjoin ℚ (S : Set ℂ), inferInstance, fun w x => IntermediateField.subset_adjoin _ _ ?_⟩
  have e : ((χ ^ n).loc w x) = (χ.loc w x) ^ n := by
    simp [HChar.loc, MonoidHom.pow_apply]
  have e1 : ((χ.loc w x : ℂˣ) : ℂ) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← e, show χ ^ n = 1 from h]; rfl
  simpa [S, Polynomial.mem_nthRoots hn] using e1

end GlobalTheory.RowExNF

namespace GlobalTheory.RowExNF
open Formalism.L2.Host

/- English proof (translation)
Take `⟨C, hC, hv⟩` from `PI.AlgValsFin.W.algValsFin_main L χ 0 m (fun k => by simp [hm k])`. Set `M : IntermediateField ℚ ℂ` to `C.toIntermediateField fun x => by simp`. Set `e : C ≃+ M` to `{ toFun := fun x => ⟨x, x.2⟩ invFun := fun x => ⟨x, x.2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl map_add' := fun _ _ => rfl }`. Use `haveI := hC`. Use `⟨M, LinearEquiv.finiteDimensional { e.toAddMonoidHom.toRatLinearMap with invFun := e.symm, left_inv := e.left_inv, right_inv := e.right_inv }, fun v hu => ?_⟩` and prove the remaining obligations.

Take `⟨y, hy⟩` from `hv v hu`. Establish `: ((χ.val v : ℂˣ) : ℂ) = y`. Establish `hy' : (y : ℂ) = χ.valTw 0 v` using `hy`. Rewrite using `[hy']`. Simplify using `[HChar.valTw]`.

Rewrite using `[this]`. Conclude with `y.2`.
-/
theorem unr_vals' (L : Type) [Field L] [NumberField L] (χ : HChar L) (m : (L →+* ℂ) → ℤ)
    (hm : ∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ φ : L →+* ℂ, φ (k : L) ^ m φ) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ v, χ.UnrAt v → ((χ.val v : ℂˣ) : ℂ) ∈ M := by
  obtain ⟨C, hC, hv⟩ := PI.AlgValsFin.W.algValsFin_main L χ 0 m (fun k => by simp [hm k])
  let M : IntermediateField ℚ ℂ := C.toIntermediateField fun x => by simp
  let e : C ≃+ M :=
    { toFun := fun x => ⟨x, x.2⟩
      invFun := fun x => ⟨x, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  haveI := hC
  refine ⟨M, LinearEquiv.finiteDimensional { e.toAddMonoidHom.toRatLinearMap with invFun := e.symm, left_inv := e.left_inv, right_inv := e.right_inv }, fun v hu => ?_⟩
  obtain ⟨y, hy⟩ := hv v hu
  have : ((χ.val v : ℂˣ) : ℂ) = y := by
    have hy' : (y : ℂ) = χ.valTw 0 v := hy
    rw [hy']; simp [HChar.valTw]
  rw [this]
  exact y.2

end GlobalTheory.RowExNF

namespace GlobalTheory.RowExNF

open Formalism.L2.Host

/- English proof (translation)
Take `⟨N, hN, hdec⟩` from `GlobalTheory.T.heckeChar_local_value_div_uniformiser_pow L χ`. Take `⟨M0, hM0, hval⟩` from `unr_vals' L χ m hm`. Set `Z : Finset ℂ` to `S.image (fun w => ((χ.val w : ℂˣ) : ℂ)) ∪ (Polynomial.nthRoots N (1 : ℂ)).toFinset`. Establish `hint : ∀ z ∈ (Z : Set ℂ), IsIntegral ℚ z` using `fun z hz => by`. Rewrite `hz` using `[Finset.coe_union, Set.mem_union]`.

Break down `hz with hz | hz` into its components or cases. Take `⟨w, -, rfl⟩` from `Finset.mem_image.1 hz`. Conclude with `(GlobalTheory.T.heckeChar_uniformiser_value_isAlgebraic L χ m hm w).isIntegral`. Establish `hz' : z ^ N = 1` using `by simpa [Polynomial.mem_nthRoots hN] using hz`. Conclude with `⟨Polynomial.X ^ N - 1, Polynomial.monic_X_pow_sub_C 1 hN.ne', by simp [hz']⟩`.

Use `haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Z : Set ℂ)) := IntermediateField.finiteDimensional_adjoin hint`. Use `haveI := hM0`. Use `⟨M0 ⊔ IntermediateField.adjoin ℚ (Z : Set ℂ), inferInstance, fun w x => ?_⟩` and prove the remaining obligations. Establish `hZ : ∀ z ∈ Z, z ∈ M0 ⊔ IntermediateField.adjoin ℚ (Z : Set ℂ)` using `fun z hz => le_sup_right (a := M0) (IntermediateField.subset_adjoin ℚ _ hz)`. Take `⟨a, ha⟩` from `hdec w x`.

Establish `hv : ((χ.val w : ℂˣ) : ℂ) ∈ M0 ⊔ IntermediateField.adjoin ℚ (Z : Set ℂ)`. Distinguish the cases in `hw : w ∈ S`. Conclude with `hZ _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hw))`. Conclude with `le_sup_left (b := IntermediateField.adjoin ℚ (Z : Set ℂ)) (hval w (hS w hw))`. Establish `hr : ((χ.loc w x / χ.val w ^ a : ℂˣ) : ℂ) ∈ M0 ⊔ IntermediateField.adjoin ℚ (Z : Set ℂ)` using `hZ _ (Finset.mem_union_right _ (by simpa [Polynomial.mem_nthRoots hN] using ha))`.

Establish `e : ((χ.loc w x : ℂˣ) : ℂ) = ((χ.loc w x / χ.val w ^ a : ℂˣ) : ℂ) * ((χ.val w : ℂˣ) : ℂ) ^ a`. Rewrite using `[← Units.val_zpow_eq_zpow_val, ← Units.val_mul, div_mul_cancel]`. Rewrite using `[e]`. Conclude with `mul_mem hr (zpow_mem hv a)`.
-/
theorem locIn_alg (L : Type) [Field L] [NumberField L] (χ : HChar L) (m : (L →+* ℂ) → ℤ)
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hm : ∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ φ : L →+* ℂ, φ (k : L) ^ m φ)
    (hS : ∀ v, v ∉ S → χ.UnrAt v) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ w x, ((χ.loc w x : ℂˣ) : ℂ) ∈ M := by
  classical
  obtain ⟨N, hN, hdec⟩ := GlobalTheory.T.heckeChar_local_value_div_uniformiser_pow L χ
  obtain ⟨M0, hM0, hval⟩ := unr_vals' L χ m hm
  let Z : Finset ℂ := S.image (fun w => ((χ.val w : ℂˣ) : ℂ)) ∪ (Polynomial.nthRoots N (1 : ℂ)).toFinset
  have hint : ∀ z ∈ (Z : Set ℂ), IsIntegral ℚ z := fun z hz => by
    rw [Finset.coe_union, Set.mem_union] at hz
    rcases hz with hz | hz
    · obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hz
      exact (GlobalTheory.T.heckeChar_uniformiser_value_isAlgebraic L χ m hm w).isIntegral
    · have hz' : z ^ N = 1 := by simpa [Polynomial.mem_nthRoots hN] using hz
      exact ⟨Polynomial.X ^ N - 1, Polynomial.monic_X_pow_sub_C 1 hN.ne', by simp [hz']⟩
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Z : Set ℂ)) := IntermediateField.finiteDimensional_adjoin hint
  haveI := hM0
  refine ⟨M0 ⊔ IntermediateField.adjoin ℚ (Z : Set ℂ), inferInstance, fun w x => ?_⟩
  have hZ : ∀ z ∈ Z, z ∈ M0 ⊔ IntermediateField.adjoin ℚ (Z : Set ℂ) := fun z hz =>
    le_sup_right (a := M0) (IntermediateField.subset_adjoin ℚ _ hz)
  obtain ⟨a, ha⟩ := hdec w x
  have hv : ((χ.val w : ℂˣ) : ℂ) ∈ M0 ⊔ IntermediateField.adjoin ℚ (Z : Set ℂ) := by
    by_cases hw : w ∈ S
    · exact hZ _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hw))
    · exact le_sup_left (b := IntermediateField.adjoin ℚ (Z : Set ℂ)) (hval w (hS w hw))
  have hr : ((χ.loc w x / χ.val w ^ a : ℂˣ) : ℂ) ∈ M0 ⊔ IntermediateField.adjoin ℚ (Z : Set ℂ) :=
    hZ _ (Finset.mem_union_right _ (by simpa [Polynomial.mem_nthRoots hN] using ha))
  have e : ((χ.loc w x : ℂˣ) : ℂ) = ((χ.loc w x / χ.val w ^ a : ℂˣ) : ℂ) * ((χ.val w : ℂˣ) : ℂ) ^ a := by
    rw [← Units.val_zpow_eq_zpow_val, ← Units.val_mul, div_mul_cancel]
  rw [e]
  exact mul_mem hr (zpow_mem hv a)

end GlobalTheory.RowExNF

namespace GlobalTheory.RowExNF

open Formalism.L2.Host

/- English proof (translation)
Establish `hI : Ideal.span {((n : ℕ) : 𝓞 L)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hn` after adjusting the coercions. Establish `hf` using `Ideal.finite_factors hI`. Use `⟨hf.toFinset, fun v hv hmem => hv ?_⟩` and prove the remaining obligations.

Rewrite using `[Set.Finite.mem_toFinset]`. Conclude with `Ideal.dvd_span_singleton.2 hmem`.
-/
theorem exists_finset_over {L : Type} [Field L] [NumberField L] (n : ℕ) (hn : n ≠ 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 L)), ∀ v, v ∉ S → ((n : ℕ) : 𝓞 L) ∉ v.asIdeal := by
  have hI : Ideal.span {((n : ℕ) : 𝓞 L)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  have hf := Ideal.finite_factors hI
  refine ⟨hf.toFinset, fun v hv hmem => hv ?_⟩
  rw [Set.Finite.mem_toFinset]
  exact Ideal.dvd_span_singleton.2 hmem

/- English proof (translation)
Introduce `w x` and use `⟨⟨_, hle (h w x)⟩, rfl⟩`.
-/
theorem locIn_of_mem {D : D7} {M M' : IntermediateField ℚ ℂ} {χ : HChar D.host.E}
    (h : ∀ w x, ((χ.loc w x : ℂˣ) : ℂ) ∈ M) (hle : M ≤ M') : LocIn (algebraMap M' ℂ) χ :=
  fun w x => ⟨⟨_, hle (h w x)⟩, rfl⟩

/- English proof (translation)
Introduce `v hv` and use `by obtain ⟨y, hy⟩ := h v hv exact ⟨⟨y, hle y.2⟩, hy⟩`.
-/
theorem valuesIn_mono {L : Type} [Field L] [NumberField L] {M M' : IntermediateField ℚ ℂ} {χ : HChar L} {s : ℝ}
    (h : χ.ValuesIn s (algebraMap M ℂ)) (hle : M ≤ M') : χ.ValuesIn s (algebraMap M' ℂ) := fun v hv => by
  obtain ⟨y, hy⟩ := h v hv
  exact ⟨⟨y, hle y.2⟩, hy⟩

/- English proof (translation)
Establish `hmu : ∀ j : Fin D.R.m, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ w x, (((L.C.mu0 j).loc w x : ℂˣ) : ℂ) ∈ M`. Introduce `j`. Establish `hC` using `L.C.isMu0 j`. Take `⟨n, hn, hinf⟩` from `hC.inf`. Use `choose z hz using fun g : D.R.Psi => (D.hc (D.eTau.symm g)).e_int j`.

Establish `hn' : ∀ g, n g = 2 * (-(z g))` using `fun g => by`. Establish `h1` using `hn g`. Simplify using `only [eExp, hz] at h1`. Conclude with `h1` after adjusting the coercions. Take `⟨m, hm⟩` from `algType_of_hasInf _ _ _ hinf hn'`.

Take `⟨S0, hS0⟩` from `exists_finset_over (L := D.host.E) (D.host.g 0) (D.host.g_prime 0).ne_zero`. Take `⟨S1, hS1⟩` from `exists_finset_over (L := D.host.E) (D.host.g 1) (D.host.g_prime 1).ne_zero`. Use `locIn_alg _ _ m (S0 ∪ S1) hm fun v hv => hC.unr v fun k => ?_` and prove the remaining obligations. Rewrite `hv` using `[Finset.mem_union, not_or]`. Use `fin_cases k`.

Conclude with `hS0 v hv.1`. Conclude with `hS1 v hv.2`. Establish `hxi : ∀ t : T, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ w x, (((L.xiH t).loc w x : ℂˣ) : ℂ) ∈ M` using `fun t => by`. Take `⟨n, hn, h⟩` from `hL.xi_fin t`. Conclude with `locIn_fin _ n hn h`.

Establish `hchi : ∀ i : Fin D.R.m, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ w x, (((G.ch.chiH (i + 1)).loc w x : ℂˣ) : ℂ) ∈ M`. Introduce `i`. Establish `h1 : 1 ≤ (i : ℕ) + 1` using `by omega`. Establish `h2 : (i : ℕ) + 1 ≤ D.R.m` using `i.2`. Take `⟨m, hm⟩` from `algType_of_hasInf _ _ _ (G.ch.inf _ h1 h2) fun _ => rfl`.

Use `locIn_alg _ _ m (G.pl.S0.biUnion (aboveF (L := D.host.E) D.host.F)) hm fun v hv => G.ch.unr _ h1 h2 v fun hu => hv ?_` and prove the remaining obligations. Rewrite using `[Finset.mem_biUnion]`. Conclude with `⟨_, hu, (finite_aboveF (L := D.host.E) D.host.F _).mem_toFinset.2 rfl⟩`. Establish `hpsi : ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ w x, ((L.C.chiPsi.loc w x : ℂˣ) : ℂ) ∈ M`. Take `⟨m, hm⟩` from `algType_of_hasInf _ (fun _ => (1 : ℤ)) _ L.C.isChi.inf fun _ => rfl`.

Conclude with `locIn_alg _ _ m ∅ hm fun v _ => L.C.isChi.unr v`. Establish `hdel : ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ w x, ((L.C.del.loc w x : ℂˣ) : ℂ) ∈ M`. Take `⟨n, hn, h⟩` from `L.C.isDel.fin`. Conclude with `locIn_fin _ n hn h`. Establish `hdel' : ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ w x, ((L.C.del'.loc w x : ℂˣ) : ℂ) ∈ M`.

Take `⟨n, hn, h⟩` from `L.C.isDel'.fin`. Conclude with `locIn_fin _ n hn h`. Take `⟨Me, hMe, he⟩` from `GlobalTheory.T.exists_numberField_valuesIn_etaChar_halfTwist D.host L.C.eta L.C.isEta`. Use `choose Mmu hMmu hmu using hmu`. Use `choose Mxi hMxi hxi using hxi`.

Use `choose Mchi hMchi hchi using hchi`. Take `⟨Mp, hMp, hp⟩` from `hpsi`. Take `⟨Md, hMd, hd⟩` from `hdel`. Take `⟨Md', hMd', hd'⟩` from `hdel'`. Use `haveI := hMe`.

Use `haveI := hMp`. Use `haveI := hMd`. Use `haveI := hMd'`. Use `haveI := fun j => hMmu j`. Use `haveI := fun t => hMxi t`.

Use `haveI := fun i => hMchi i`. Use `⟨(⨆ j, Mmu j) ⊔ (⨆ t, Mxi t) ⊔ (⨆ i, Mchi i) ⊔ Me ⊔ Mp ⊔ Md ⊔ Md', inferInstance, ?_⟩` and prove the remaining obligations. Use `⟨fun j => locIn_of_mem (hmu j) ?_, fun t => locIn_of_mem (hxi t) ?_, fun i h1 h2 => ?_, valuesIn_mono he ?_, (locIn_of_mem hp ?_).valuesIn, (locIn_of_mem hd ?_).valuesIn, (locIn_of_mem hd' ?_).valuesIn⟩` and prove the remaining obligations. Conclude with `(le_iSup Mmu j).trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))))`. Conclude with `(le_iSup Mxi t).trans (le_sup_right.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))))`.

Take `⟨k, rfl⟩ : ∃ k, i = k + 1` from `⟨i - 1, by omega⟩`. Conclude with `locIn_of_mem (hchi ⟨k, by omega⟩) ((le_iSup Mchi ⟨k, by omega⟩).trans (le_sup_right.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))))`. Conclude with `le_sup_right.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))`. Conclude with `le_sup_right.trans (le_sup_left.trans le_sup_left)`. Conclude with `le_sup_right.trans le_sup_left`.

Conclude with `le_sup_right`.
-/
theorem charsIn_nf {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) {sc : Consts}
    (G : GridData L sc) : ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ CharsIn G (algebraMap M ℂ) := by
  classical
  have hmu : ∀ j : Fin D.R.m, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
      ∀ w x, (((L.C.mu0 j).loc w x : ℂˣ) : ℂ) ∈ M := by
    intro j
    have hC := L.C.isMu0 j
    obtain ⟨n, hn, hinf⟩ := hC.inf
    choose z hz using fun g : D.R.Psi => (D.hc (D.eTau.symm g)).e_int j
    have hn' : ∀ g, n g = 2 * (-(z g)) := fun g => by
      have h1 := hn g
      simp only [eExp, hz] at h1
      exact_mod_cast h1
    obtain ⟨m, hm⟩ := algType_of_hasInf _ _ _ hinf hn'
    obtain ⟨S0, hS0⟩ := exists_finset_over (L := D.host.E) (D.host.g 0) (D.host.g_prime 0).ne_zero
    obtain ⟨S1, hS1⟩ := exists_finset_over (L := D.host.E) (D.host.g 1) (D.host.g_prime 1).ne_zero
    refine locIn_alg _ _ m (S0 ∪ S1) hm fun v hv => hC.unr v fun k => ?_
    rw [Finset.mem_union, not_or] at hv
    fin_cases k
    · exact hS0 v hv.1
    · exact hS1 v hv.2
  have hxi : ∀ t : T, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
      ∀ w x, (((L.xiH t).loc w x : ℂˣ) : ℂ) ∈ M := fun t => by
    obtain ⟨n, hn, h⟩ := hL.xi_fin t
    exact locIn_fin _ n hn h
  have hchi : ∀ i : Fin D.R.m, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
      ∀ w x, (((G.ch.chiH (i + 1)).loc w x : ℂˣ) : ℂ) ∈ M := by
    intro i
    have h1 : 1 ≤ (i : ℕ) + 1 := by omega
    have h2 : (i : ℕ) + 1 ≤ D.R.m := i.2
    obtain ⟨m, hm⟩ := algType_of_hasInf _ _ _ (G.ch.inf _ h1 h2) fun _ => rfl
    refine locIn_alg _ _ m (G.pl.S0.biUnion (aboveF (L := D.host.E) D.host.F)) hm fun v hv => G.ch.unr _ h1 h2 v fun hu => hv ?_
    rw [Finset.mem_biUnion]
    exact ⟨_, hu, (finite_aboveF (L := D.host.E) D.host.F _).mem_toFinset.2 rfl⟩
  have hpsi : ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
      ∀ w x, ((L.C.chiPsi.loc w x : ℂˣ) : ℂ) ∈ M := by
    obtain ⟨m, hm⟩ := algType_of_hasInf _ (fun _ => (1 : ℤ)) _ L.C.isChi.inf fun _ => rfl
    exact locIn_alg _ _ m ∅ hm fun v _ => L.C.isChi.unr v
  have hdel : ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
      ∀ w x, ((L.C.del.loc w x : ℂˣ) : ℂ) ∈ M := by
    obtain ⟨n, hn, h⟩ := L.C.isDel.fin
    exact locIn_fin _ n hn h
  have hdel' : ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
      ∀ w x, ((L.C.del'.loc w x : ℂˣ) : ℂ) ∈ M := by
    obtain ⟨n, hn, h⟩ := L.C.isDel'.fin
    exact locIn_fin _ n hn h
  obtain ⟨Me, hMe, he⟩ := GlobalTheory.T.exists_numberField_valuesIn_etaChar_halfTwist D.host L.C.eta L.C.isEta
  choose Mmu hMmu hmu using hmu
  choose Mxi hMxi hxi using hxi
  choose Mchi hMchi hchi using hchi
  obtain ⟨Mp, hMp, hp⟩ := hpsi
  obtain ⟨Md, hMd, hd⟩ := hdel
  obtain ⟨Md', hMd', hd'⟩ := hdel'
  haveI := hMe; haveI := hMp; haveI := hMd; haveI := hMd'
  haveI := fun j => hMmu j; haveI := fun t => hMxi t; haveI := fun i => hMchi i
  refine ⟨(⨆ j, Mmu j) ⊔ (⨆ t, Mxi t) ⊔ (⨆ i, Mchi i) ⊔ Me ⊔ Mp ⊔ Md ⊔ Md', inferInstance, ?_⟩
  refine ⟨fun j => locIn_of_mem (hmu j) ?_, fun t => locIn_of_mem (hxi t) ?_, fun i h1 h2 => ?_,
    valuesIn_mono he ?_, (locIn_of_mem hp ?_).valuesIn, (locIn_of_mem hd ?_).valuesIn, (locIn_of_mem hd' ?_).valuesIn⟩
  · exact (le_iSup Mmu j).trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans
      (le_sup_left.trans le_sup_left)))))
  · exact (le_iSup Mxi t).trans (le_sup_right.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans
      (le_sup_left.trans le_sup_left)))))
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    exact locIn_of_mem (hchi ⟨k, by omega⟩) ((le_iSup Mchi ⟨k, by omega⟩).trans (le_sup_right.trans
      (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))))
  · exact le_sup_right.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
  · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

end GlobalTheory.RowExNF

open GlobalTheory.RowExNF in

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hS ch _ _ => by haveI := hS.fin exact charsIn_nf hS.core.lev ch.G⟩⟩`.
-/
theorem GlobalTheory.RowEx.nfChars : NFChars :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hS ch _ _ => by
    haveI := hS.fin
    exact charsIn_nf hS.core.lev ch.G⟩⟩

end
