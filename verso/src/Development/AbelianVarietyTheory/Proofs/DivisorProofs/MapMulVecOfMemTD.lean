import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoRows
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMapLinearScalingByDeterminant
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

open scoped Matrix

namespace GlobalTheory.HaarLin

def TD (R : Type) [CommRing R] (κ : Type) [Fintype κ] [DecidableEq κ] : Submonoid (Matrix κ κ R) :=
  Submonoid.closure ({M | ∃ i j : κ, ∃ c : R, i ≠ j ∧ M = Matrix.transvection i j c} ∪
    {M | ∃ d : κ → Rˣ, M = Matrix.diagonal fun i => (d i : R)})

def HasStableRangeOne (R : Type) [CommRing R] : Prop := ∀ a b : R, IsCoprime a b → ∃ t : R, IsUnit (a + t * b)

end GlobalTheory.HaarLin

open NumberField MeasureTheory Matrix
open scoped NNReal ENNReal
namespace GlobalTheory.HaarLin

/- English proof (translation)
Take `⟨K, hK, hK0⟩` from `exists_compact_mem_nhds (0 : X)`. Establish `h1 : μ K ≠ 0` using `(μ.measure_pos_of_mem_nhds hK0).ne'`. Establish `h2 : μ K ≠ ∞` using `hK.measure_lt_top.ne`. Establish `h3 : (a • μ) K = (b • μ) K` using `by rw [h]`. Simplify using `only [Measure.smul_apply, Measure.nnreal_smul_coe_apply] at h3`.

Conclude with `(ENNReal.mul_left_inj h1 h2).1 h3` after adjusting the coercions.
-/
private lemma nnreal_eq_of_smul_addHaar_eq {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]
    {a b : ℝ≥0} (h : a • μ = b • μ) : a = b := by
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : X)
  have h1 : μ K ≠ 0 := (μ.measure_pos_of_mem_nhds hK0).ne'
  have h2 : μ K ≠ ∞ := hK.measure_lt_top.ne
  have h3 : (a • μ) K = (b • μ) K := by rw [h]
  simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply] at h3
  exact_mod_cast (ENNReal.mul_left_inj h1 h2).1 h3

/- English proof (translation)
Establish `hA : Measurable (fun x : κ → R => A *ᵥ x)` using `(Continuous.matrix_mulVec continuous_const continuous_id).measurable`. Establish `hB : Measurable (fun x : κ → R => B *ᵥ x)` using `(Continuous.matrix_mulVec continuous_const continuous_id).measurable`. Rewrite using `[Measure.map_map hA hB]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Simplify using `[Function.comp, Matrix.mulVec_mulVec]`.
-/
private lemma map_mul_lemma_2 {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {κ : Type} [Fintype κ] [MeasurableSpace (κ → R)] [BorelSpace (κ → R)]
    (A B : Matrix κ κ R) (μ : Measure (κ → R)) :
    μ.map (fun x => (A * B) *ᵥ x) = (μ.map (fun x => B *ᵥ x)).map (fun x => A *ᵥ x) := by
  have hA : Measurable (fun x : κ → R => A *ᵥ x) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have hB : Measurable (fun x : κ → R => B *ᵥ x) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  rw [Measure.map_map hA hB]
  congr 1
  funext x
  simp [Function.comp, Matrix.mulVec_mulVec]

/- English proof (translation)
Set `e : (κ → R) ≃+ (κ → R)` to `{ toFun := fun x => P *ᵥ x invFun := fun x => Q *ᵥ x left_inv := fun x => by simp [Matrix.mulVec_mulVec, hQP] right_inv := fun x => by simp [Matrix.mulVec_mulVec, hPQ] map_add' := fun x y => Matrix.mulVec_add P x y }`. Establish `he : Continuous (fun x : κ → R => P *ᵥ x)` using `Continuous.matrix_mulVec continuous_const continuous_id`. Establish `he' : Continuous (fun x : κ → R => Q *ᵥ x)` using `Continuous.matrix_mulVec continuous_const continuous_id`. Establish `key : ∀ μ : Measure (κ → R), μ.IsAddHaarMeasure → (μ.map (fun x => P *ᵥ x)).IsAddHaarMeasure` using `fun μ _ => e.isAddHaarMeasure_map μ he he'`. Set `μ₀ : Measure (κ → R)` to `Measure.addHaar`.

Use `haveI := key μ₀ inferInstance`. Take `⟨c, hc⟩ : ∃ c : ℝ≥0, μ₀.map (fun x => P *ᵥ x) = c • μ₀` from `⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩`. Use `⟨c, fun μ hμ => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩ : ∃ k : ℝ≥0, μ = k • μ₀` from `⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩`. Rewrite using `[hk, Measure.map_smul, hc, smul_comm]`.
-/
private lemma exists_map_mulVec_eq_smul_of_invertible {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] {κ : Type} [Fintype κ] [DecidableEq κ]
    [MeasurableSpace (κ → R)] [BorelSpace (κ → R)] (P Q : Matrix κ κ R) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    ∃ c : ℝ≥0, ∀ μ : Measure (κ → R), μ.IsAddHaarMeasure → μ.map (fun x => P *ᵥ x) = c • μ := by
  let e : (κ → R) ≃+ (κ → R) :=
    { toFun := fun x => P *ᵥ x
      invFun := fun x => Q *ᵥ x
      left_inv := fun x => by simp [Matrix.mulVec_mulVec, hQP]
      right_inv := fun x => by simp [Matrix.mulVec_mulVec, hPQ]
      map_add' := fun x y => Matrix.mulVec_add P x y }
  have he : Continuous (fun x : κ → R => P *ᵥ x) := Continuous.matrix_mulVec continuous_const continuous_id
  have he' : Continuous (fun x : κ → R => Q *ᵥ x) := Continuous.matrix_mulVec continuous_const continuous_id
  have key : ∀ μ : Measure (κ → R), μ.IsAddHaarMeasure → (μ.map (fun x => P *ᵥ x)).IsAddHaarMeasure :=
    fun μ _ => e.isAddHaarMeasure_map μ he he'
  let μ₀ : Measure (κ → R) := Measure.addHaar
  haveI := key μ₀ inferInstance
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, μ₀.map (fun x => P *ᵥ x) = c • μ₀ :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  refine ⟨c, fun μ hμ => ?_⟩
  obtain ⟨k, hk⟩ : ∃ k : ℝ≥0, μ = k • μ₀ := ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  rw [hk, Measure.map_smul, hc, smul_comm]

/- English proof (translation)
Use `set D : Matrix κ κ R := diagonal (Function.update (1 : κ → R) i (-1)) with hD0`. Establish `hD : D * D = 1`. Rewrite using `[hD0, diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Apply the tactic sequence `by_cases hk : k = i <;> simp [Function.update_apply, hk]`. Establish `hT : transvection i j c * transvection i j (-c) = 1`. Rewrite using `[transvection_mul_transvection_same (h := hij), add_neg_cancel, transvection_zero]`. Establish `hT' : transvection i j (-c) * transvection i j c = 1`. Rewrite using `[transvection_mul_transvection_same (h := hij), neg_add_cancel, transvection_zero]`.

Establish `hconj : D * transvection i j c * D = transvection i j (-c)`. Establish `hji : j ≠ i` using `Ne.symm hij`. Use `clear hD hT hT'`. Use extensionality with `a b`. Simplify using `only [hD0, Matrix.mul_diagonal, Matrix.diagonal_mul, transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Function.update_apply, Pi.one_apply]`.

Use `clear hD0`. Apply the tactic sequence `split_ifs <;> grind`. Establish `hone : μ.map (fun x => (1 : Matrix κ κ R) *ᵥ x) = μ`. Simplify using `only [Matrix.one_mulVec, Measure.map_id']`. Take `⟨a, ha⟩` from `exists_map_mulVec_eq_smul_of_invertible D D hD hD`.

Take `⟨t, ht⟩` from `exists_map_mulVec_eq_smul_of_invertible _ _ hT hT'`. Take `⟨t', ht'⟩` from `exists_map_mulVec_eq_smul_of_invertible _ _ hT' hT`. Establish `haa : a * a = 1`. Establish `h` using `map_mul_lemma_2 D D μ`. Rewrite `h` using `[hD, hone, ha μ inferInstance, Measure.map_smul, ha μ inferInstance, smul_smul]`.

Conclude with `nnreal_eq_of_smul_addHaar_eq μ (by rw [one_smul]; exact h.symm)`. Establish `htt : t' * t = 1`. Establish `h` using `map_mul_lemma_2 (transvection i j c) (transvection i j (-c)) μ`. Rewrite `h` using `[hT, hone, ht' μ inferInstance, Measure.map_smul, ht μ inferInstance, smul_smul]`. Conclude with `nnreal_eq_of_smul_addHaar_eq μ (by rw [one_smul]; exact h.symm)`.

Establish `hcj : t' = a * t * a`. Establish `h` using `map_mul_lemma_2 (D * transvection i j c) D μ`. Rewrite `h` using `[hconj, ht' μ inferInstance, ha μ inferInstance, Measure.map_smul, map_mul_lemma_2, ht μ inferInstance, Measure.map_smul, ha μ inferInstance, smul_smul, smul_smul]`. Conclude with `nnreal_eq_of_smul_addHaar_eq μ h`. Establish `h2 : t * t = 1`.

Rewrite `htt` using `[hcj]`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : t = 1`. Establish `h4 : (t : ℝ) * t = 1` using `by exact_mod_cast h2`. Apply `NNReal.eq` to reduce the goal to its premises.

Establish `h5` using `t.coe_nonneg`. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[ht μ inferInstance, h3, one_smul]`.
-/
private lemma map_transvection_mulVec_addHaar_eq_self {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] {κ : Type} [Fintype κ] [DecidableEq κ]
    [MeasurableSpace (κ → R)] [BorelSpace (κ → R)] (i j : κ) (hij : i ≠ j) (c : R)
    (μ : Measure (κ → R)) [μ.IsAddHaarMeasure] :
    μ.map (fun x => transvection i j c *ᵥ x) = μ := by
  set D : Matrix κ κ R := diagonal (Function.update (1 : κ → R) i (-1)) with hD0
  have hD : D * D = 1 := by
    rw [hD0, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    by_cases hk : k = i <;> simp [Function.update_apply, hk]
  have hT : transvection i j c * transvection i j (-c) = 1 := by
    rw [transvection_mul_transvection_same (h := hij), add_neg_cancel, transvection_zero]
  have hT' : transvection i j (-c) * transvection i j c = 1 := by
    rw [transvection_mul_transvection_same (h := hij), neg_add_cancel, transvection_zero]
  have hconj : D * transvection i j c * D = transvection i j (-c) := by
    have hji : j ≠ i := Ne.symm hij
    clear hD hT hT'
    ext a b
    simp only [hD0, Matrix.mul_diagonal, Matrix.diagonal_mul, transvection, Matrix.add_apply,
      Matrix.one_apply, Matrix.single_apply, Function.update_apply, Pi.one_apply]
    clear hD0
    split_ifs <;> grind
  have hone : μ.map (fun x => (1 : Matrix κ κ R) *ᵥ x) = μ := by
    simp only [Matrix.one_mulVec, Measure.map_id']
  obtain ⟨a, ha⟩ := exists_map_mulVec_eq_smul_of_invertible D D hD hD
  obtain ⟨t, ht⟩ := exists_map_mulVec_eq_smul_of_invertible _ _ hT hT'
  obtain ⟨t', ht'⟩ := exists_map_mulVec_eq_smul_of_invertible _ _ hT' hT
  have haa : a * a = 1 := by
    have h := map_mul_lemma_2 D D μ
    rw [hD, hone, ha μ inferInstance, Measure.map_smul, ha μ inferInstance, smul_smul] at h
    exact nnreal_eq_of_smul_addHaar_eq μ (by rw [one_smul]; exact h.symm)
  have htt : t' * t = 1 := by
    have h := map_mul_lemma_2 (transvection i j c) (transvection i j (-c)) μ
    rw [hT, hone, ht' μ inferInstance, Measure.map_smul, ht μ inferInstance, smul_smul] at h
    exact nnreal_eq_of_smul_addHaar_eq μ (by rw [one_smul]; exact h.symm)
  have hcj : t' = a * t * a := by
    have h := map_mul_lemma_2 (D * transvection i j c) D μ
    rw [hconj, ht' μ inferInstance, ha μ inferInstance, Measure.map_smul, map_mul_lemma_2,
      ht μ inferInstance, Measure.map_smul, ha μ inferInstance, smul_smul, smul_smul] at h
    exact nnreal_eq_of_smul_addHaar_eq μ h
  have h2 : t * t = 1 := by
    rw [hcj] at htt
    calc t * t = t * t * (a * a) := by rw [haa, mul_one]
      _ = a * t * a * t := by ring
      _ = 1 := htt
  have h3 : t = 1 := by
    have h4 : (t : ℝ) * t = 1 := by exact_mod_cast h2
    apply NNReal.eq
    have h5 := t.coe_nonneg
    push_cast
    nlinarith
  rw [ht μ inferInstance, h3, one_smul]

/- English proof (translation)
Use `letI : MeasurableSpace R := borel R`. Use `haveI : BorelSpace R := ⟨rfl⟩`. Establish `e : inst = MeasurableSpace.pi` using `(@BorelSpace.measurable_eq (κ → R) _ inst hb).trans (@BorelSpace.measurable_eq (κ → R) _ MeasurableSpace.pi Pi.borelSpace).symm`. Substitute `e` using the available equality. Establish `h1 : ∀ u : Rˣ, (Measure.addHaar : Measure R).map (fun y => (u : R) * y) = (distribHaarChar R u)⁻¹ • Measure.addHaar`.

Introduce `u`. Establish `hu : (fun y : R => (u : R) * y) = fun y => (DomMulAct.mk.symm (DomMulAct.mk u⁻¹)⁻¹ : Rˣ) • y`. Use function extensionality and compare the values at `y`. Simplify using `[Units.smul_def]`. Rewrite using `[hu]`.

Express the relevant statement in the definitionally equal form `DomMulAct.mk u⁻¹ • (Measure.addHaar : Measure R) = _`. Rewrite using `[Measure.isAddLeftInvariant_eq_smul (DomMulAct.mk u⁻¹ • (Measure.addHaar : Measure R)) Measure.addHaar, addHaarScalarFactor_smul_eq_distribHaarChar, map_inv]`. Use `set ν : Measure (κ → R) := Measure.pi (fun _ => (Measure.addHaar : Measure R)) with hν0`. Establish `hν : ν.map (fun x => diagonal (fun i => (d i : R)) *ᵥ x) = (∏ i, distribHaarChar R (d i))⁻¹ • ν`. Establish `hf : (fun x : κ → R => diagonal (fun i => (d i : R)) *ᵥ x) = fun x i => (d i : R) * x i`.

Use function extensionality and compare the values at `x i`. Conclude with `mulVec_diagonal _ _ _`. Use `haveI : ∀ i, SigmaFinite ((Measure.addHaar : Measure R).map (fun y => (d i : R) * y)) := fun i => by`. Rewrite using `[h1]`. Use `infer_instance`.

Rewrite using `[hf, hν0, Measure.pi_map_pi (f := fun i y => (d i : R) * y) (fun i => (continuous_mul_left (d i : R)).measurable.aemeasurable)]`. Repeatedly rewrite using `[h1]`. Use `Measure.pi_eq (fun s hs => ?_)` and prove the remaining obligations. Rewrite using `[Measure.smul_apply, Measure.nnreal_smul_coe_apply, Measure.pi_pi]`. Simplify using `only [Measure.smul_apply, Measure.nnreal_smul_coe_apply, ← Finset.prod_inv_distrib, Finset.prod_mul_distrib, ENNReal.coe_finset_prod]`.

Take `⟨k, hk⟩ : ∃ k : ℝ≥0, μ = k • ν` from `⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩`. Rewrite using `[hk, Measure.map_smul, hν, smul_comm]`.
-/
private lemma map_diagonal_mulVec_eq_inv_prod_smul {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] {κ : Type} [Fintype κ] [DecidableEq κ]
    [inst : MeasurableSpace (κ → R)] [hb : BorelSpace (κ → R)] (d : κ → Rˣ)
    (μ : Measure (κ → R)) [μ.IsAddHaarMeasure] :
    μ.map (fun x => diagonal (fun i => (d i : R)) *ᵥ x) = (∏ i, distribHaarChar R (d i))⁻¹ • μ := by
  letI : MeasurableSpace R := borel R
  haveI : BorelSpace R := ⟨rfl⟩
  have e : inst = MeasurableSpace.pi :=
    (@BorelSpace.measurable_eq (κ → R) _ inst hb).trans
      (@BorelSpace.measurable_eq (κ → R) _ MeasurableSpace.pi Pi.borelSpace).symm
  subst e
  have h1 : ∀ u : Rˣ, (Measure.addHaar : Measure R).map (fun y => (u : R) * y) =
      (distribHaarChar R u)⁻¹ • Measure.addHaar := by
    intro u
    have hu : (fun y : R => (u : R) * y) = fun y => (DomMulAct.mk.symm (DomMulAct.mk u⁻¹)⁻¹ : Rˣ) • y := by
      funext y
      simp [Units.smul_def]
    rw [hu]
    change DomMulAct.mk u⁻¹ • (Measure.addHaar : Measure R) = _
    rw [Measure.isAddLeftInvariant_eq_smul (DomMulAct.mk u⁻¹ • (Measure.addHaar : Measure R)) Measure.addHaar,
      addHaarScalarFactor_smul_eq_distribHaarChar, map_inv]
  set ν : Measure (κ → R) := Measure.pi (fun _ => (Measure.addHaar : Measure R)) with hν0
  have hν : ν.map (fun x => diagonal (fun i => (d i : R)) *ᵥ x) = (∏ i, distribHaarChar R (d i))⁻¹ • ν := by
    have hf : (fun x : κ → R => diagonal (fun i => (d i : R)) *ᵥ x) = fun x i => (d i : R) * x i := by
      funext x i
      exact mulVec_diagonal _ _ _
    haveI : ∀ i, SigmaFinite ((Measure.addHaar : Measure R).map (fun y => (d i : R) * y)) := fun i => by
      rw [h1]; infer_instance
    rw [hf, hν0, Measure.pi_map_pi (f := fun i y => (d i : R) * y)
      (fun i => (continuous_mul_left (d i : R)).measurable.aemeasurable)]
    simp_rw [h1]
    refine Measure.pi_eq (fun s hs => ?_)
    rw [Measure.smul_apply, Measure.nnreal_smul_coe_apply, Measure.pi_pi]
    simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply, ← Finset.prod_inv_distrib,
      Finset.prod_mul_distrib, ENNReal.coe_finset_prod]
  obtain ⟨k, hk⟩ : ∃ k : ℝ≥0, μ = k • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  rw [hk, Measure.map_smul, hν, smul_comm]

/- English proof (translation)
Proceed by induction on `hM using Submonoid.closure_induction with`. Consider the case `mem M hM`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq] at hM`. Break down `hM with ⟨i, j, c, hij, rfl⟩ | ⟨d, rfl⟩` into its components or cases. Use `⟨1, by rw [det_transvection_of_ne (h := hij), Units.val_one], fun μ hμ => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_one, inv_one, one_smul]`. Conclude with `map_transvection_mulVec_addHaar_eq_self i j hij c μ`. Use `⟨∏ i, d i, by simp [det_diagonal], fun μ hμ => ?_⟩` and prove the remaining obligations. Rewrite using `[map_prod]`. Conclude with `map_diagonal_mulVec_eq_inv_prod_smul d μ`.

Consider the case `one => exact ⟨1, by simp, fun μ hμ => by simp [Measure.map_id']⟩`. Consider the case `mul M N _ _ hM hN`. Take `⟨v, hv, hvμ⟩` from `hM`. Take `⟨w, hw, hwμ⟩` from `hN`. Use `⟨v * w, by simp [hv, hw, det_mul], fun μ hμ => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul_lemma_2, hwμ μ hμ, Measure.map_smul, hvμ μ hμ, smul_smul, map_mul, mul_inv, mul_comm]`.
-/
private lemma exists_unit_det_map_mulVec_haar_eq_inv_smul {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] {κ : Type} [Fintype κ] [DecidableEq κ]
    [MeasurableSpace (κ → R)] [BorelSpace (κ → R)] (M : Matrix κ κ R) (hM : M ∈ TD R κ) :
    ∃ v : Rˣ, (v : R) = M.det ∧ ∀ μ : Measure (κ → R), μ.IsAddHaarMeasure →
      μ.map (fun x => M *ᵥ x) = (distribHaarChar R v)⁻¹ • μ := by
  induction hM using Submonoid.closure_induction with
  | mem M hM =>
    simp only [Set.mem_union, Set.mem_setOf_eq] at hM
    rcases hM with ⟨i, j, c, hij, rfl⟩ | ⟨d, rfl⟩
    · refine ⟨1, by rw [det_transvection_of_ne (h := hij), Units.val_one], fun μ hμ => ?_⟩
      rw [map_one, inv_one, one_smul]
      exact map_transvection_mulVec_addHaar_eq_self i j hij c μ
    · refine ⟨∏ i, d i, by simp [det_diagonal], fun μ hμ => ?_⟩
      rw [map_prod]
      exact map_diagonal_mulVec_eq_inv_prod_smul d μ
  | one => exact ⟨1, by simp, fun μ hμ => by simp [Measure.map_id']⟩
  | mul M N _ _ hM hN =>
    obtain ⟨v, hv, hvμ⟩ := hM
    obtain ⟨w, hw, hwμ⟩ := hN
    refine ⟨v * w, by simp [hv, hw, det_mul], fun μ hμ => ?_⟩
    rw [map_mul_lemma_2, hwμ μ hμ, Measure.map_smul, hvμ μ hμ, smul_smul, map_mul, mul_inv, mul_comm]

/- English proof (translation)
Introduce `R _ _ _ _ _ _ κ _ _ M hM u hu μ hμ`. Use `letI : MeasurableSpace (κ → R) := borel (κ → R)`. Use `haveI : BorelSpace (κ → R) := ⟨rfl⟩`. Take `⟨v, hv, hvμ⟩` from `exists_unit_det_map_mulVec_haar_eq_inv_smul M hM`. Establish `huv : u = v` using `Units.ext (hu.trans hv.symm)`.

Substitute `huv` using the available equality. Conclude with `hvμ μ hμ`.
-/
theorem map_mulVec_of_mem_TD : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] (κ : Type) [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ R), M ∈ TD R κ → ∀ u : Rˣ, u.1 = M.det → ∀ μ : @Measure (κ → R) (borel _),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    @Measure.map _ _ (borel _) (borel _) (fun x : κ → R => M *ᵥ x) μ = ((distribHaarChar R u)⁻¹ : ℝ≥0) • μ := by
  intro R _ _ _ _ _ _ κ _ _ M hM u hu μ hμ
  letI : MeasurableSpace (κ → R) := borel (κ → R)
  haveI : BorelSpace (κ → R) := ⟨rfl⟩
  obtain ⟨v, hv, hvμ⟩ := exists_unit_det_map_mulVec_haar_eq_inv_smul M hM
  have huv : u = v := Units.ext (hu.trans hv.symm)
  subst huv
  exact hvμ μ hμ

end GlobalTheory.HaarLin
