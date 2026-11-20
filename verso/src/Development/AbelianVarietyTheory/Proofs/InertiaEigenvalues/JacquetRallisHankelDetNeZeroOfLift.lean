import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisBorderedMatrixNormalFormInvariantsStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.DeltaLift

variable {k : Type} [Field k] {r : ℕ}

/- English proof (translation)
Simplify using `[full]`.
-/
theorem full_cc (Z : Gl r k) (i j : Fin r) : full Z (Fin.castSucc i) (Fin.castSucc j) = Z.1 i j := by
  simp [full]

/- English proof (translation)
Simplify using `[full]`.
-/
theorem full_cl (Z : Gl r k) (i : Fin r) : full Z (Fin.castSucc i) (Fin.last r) = Z.2.1 i := by
  simp [full]

/- English proof (translation)
Simplify using `[full]`.
-/
theorem full_lc (Z : Gl r k) (j : Fin r) : full Z (Fin.last r) (Fin.castSucc j) = Z.2.2.1 j := by
  simp [full]

/- English proof (translation)
Simplify using `only [mulVec, dotProduct, Fin.sum_univ_castSucc, full_cc, full_cl]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem full_mulVec_cs (Z : Gl r k) (V : Fin (r + 1) → k) (i : Fin r) :
    (full Z *ᵥ V) (Fin.castSucc i) = (Z.1 *ᵥ (fun j => V (Fin.castSucc j))) i + V (Fin.last r) * Z.2.1 i := by
  simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, full_cc, full_cl]
  ring

/- English proof (translation)
Simplify using `only [vecMul, dotProduct, Fin.sum_univ_castSucc, full_cc, full_lc]`.
-/
theorem vecMul_full_cs (Z : Gl r k) (V : Fin (r + 1) → k) (j : Fin r) :
    (V ᵥ* full Z) (Fin.castSucc j) = ((fun i => V (Fin.castSucc i)) ᵥ* Z.1) j + V (Fin.last r) * Z.2.2.1 j := by
  simp only [vecMul, dotProduct, Fin.sum_univ_castSucc, full_cc, full_lc]

/- English proof (translation)
Simplify using `only [dotProduct, Fin.sum_univ_castSucc]`.
-/
theorem dot_split (W V : Fin (r + 1) → k) :
    W ⬝ᵥ V = (fun i => W (Fin.castSucc i)) ⬝ᵥ (fun i => V (Fin.castSucc i)) + W (Fin.last r) * V (Fin.last r) := by
  simp only [dotProduct, Fin.sum_univ_castSucc]

/- English proof (translation)
Break down `Nat.eq_zero_or_pos r with rfl | hr` into its components or cases. Simplify using `[dotProduct]`. Establish `hP : A.charpoly.Monic` using `Matrix.charpoly_monic A`. Establish `hdeg : A.charpoly.natDegree = r` using `by simpa using Matrix.charpoly_natDegree_eq_dim A`. Establish `hne : A.charpoly ≠ 1`.

Introduce `h1`. Rewrite `hdeg` using `[h1, Polynomial.natDegree_one]`. Use linear arithmetic over natural numbers and integers. Establish `hlt : (Polynomial.X ^ m %ₘ A.charpoly).natDegree < r`. Simplify `Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ m) hP hne` using `[hdeg]`.

Rewrite using `[Matrix.pow_eq_aeval_mod_charpoly, Polynomial.aeval_eq_sum_range' hlt]`. Establish `key : ∀ (s : Finset ℕ), (∀ i ∈ s, i < r) → ∀ c : ℕ → k, w ⬝ᵥ ((∑ i ∈ s, c i • A ^ i) *ᵥ b) = 0`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro _ c`.

Simplify using the standard rewrite rules. Consider the case `insert a s ha ih`. Introduce `hs c`. Rewrite using `[Finset.sum_insert ha, add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, h a (hs a (Finset.mem_insert_self a s)), ih (fun i hi => hs i (Finset.mem_insert_of_mem hi)) c]`. Simplify using the standard rewrite rules.

Conclude with `key _ (fun i hi => Finset.mem_range.mp hi) _`.
-/
theorem dot_pow_all (A : Matrix (Fin r) (Fin r) k) (w b : Fin r → k)
    (h : ∀ i < r, w ⬝ᵥ (A ^ i *ᵥ b) = 0) (m : ℕ) : w ⬝ᵥ (A ^ m *ᵥ b) = 0 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [dotProduct]
  have hP : A.charpoly.Monic := Matrix.charpoly_monic A
  have hdeg : A.charpoly.natDegree = r := by simpa using Matrix.charpoly_natDegree_eq_dim A
  have hne : A.charpoly ≠ 1 := by
    intro h1; rw [h1, Polynomial.natDegree_one] at hdeg; omega
  have hlt : (Polynomial.X ^ m %ₘ A.charpoly).natDegree < r := by
    simpa [hdeg] using Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ m) hP hne
  rw [Matrix.pow_eq_aeval_mod_charpoly, Polynomial.aeval_eq_sum_range' hlt]
  have key : ∀ (s : Finset ℕ), (∀ i ∈ s, i < r) → ∀ c : ℕ → k,
      w ⬝ᵥ ((∑ i ∈ s, c i • A ^ i) *ᵥ b) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _ c; simp
    | insert a s ha ih =>
      intro hs c
      rw [Finset.sum_insert ha, add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul,
        h a (hs a (Finset.mem_insert_self a s)), ih (fun i hi => hs i (Finset.mem_insert_of_mem hi)) c]
      simp
  exact key _ (fun i hi => Finset.mem_range.mp hi) _

/- English proof (translation)
Take `⟨w, hw0, hw⟩` from `(Matrix.exists_vecMul_eq_zero_iff (M := Bm Z)).mpr h`. Establish `hw' : ∀ m, w ⬝ᵥ (Z.1 ^ m *ᵥ Z.2.1) = 0`. Apply `dot_pow_all` to reduce the goal to its premises. Introduce `i hi`. Use `congrFun hw ⟨i, hi⟩` as an intermediate fact.

Simplify `this` using `[vecMul, Bm, dotProduct]`. Use `set A' := full Z`. Set `x : ℕ → Fin r → k` to `fun j i => (A' ^ j *ᵥ GlobalTheory.JR.Step.eL r k) (Fin.castSucc i)`. Establish `hx : ∀ j m, w ⬝ᵥ (Z.1 ^ m *ᵥ x j) = 0`. Introduce `j`.

Proceed by induction on `j with`. Consider the case `zero`. Introduce `m`. Establish `h0 : x 0 = 0`. Use function extensionality and compare the values at `i`.

Simplify using `[x, GlobalTheory.JR.Step.eL, Pi.single_apply, Fin.castSucc_ne_last]`. Rewrite using `[h0, mulVec_zero, dotProduct_zero]`. Consider the case `succ j ih`. Introduce `m`. Establish `hxs : x (j + 1) = Z.1 *ᵥ x j + (A' ^ j *ᵥ GlobalTheory.JR.Step.eL r k) (Fin.last r) • Z.2.1`.

Use function extensionality and compare the values at `i`. Simplify using `only [x, pow_succ', ← mulVec_mulVec]`. Rewrite using `[full_mulVec_cs]`. Simplify using `[mul_comm]`. Rewrite using `[hxs, mulVec_add, dotProduct_add, mulVec_mulVec, ← pow_succ, ih, mulVec_smul, dotProduct_smul, hw']`.

Simplify using the standard rewrite rules. Use `(Matrix.exists_vecMul_eq_zero_iff (M := Bm (GlobalTheory.JR.Step.lift Z μ l))).mp ?_` and prove the remaining obligations. Use `⟨fun i => Fin.lastCases 0 w i, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Apply `hw0` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Simplify using `using congrFun h0 (Fin.castSucc i)`. Establish `e : (fun i => Fin.lastCases 0 w i : Fin (r + 1) → k) ᵥ* Bm (GlobalTheory.JR.Step.lift Z μ l) = fun j : Fin (r + 1) => μ * (w ⬝ᵥ x (j : ℕ))`. Use function extensionality and compare the values at `j`. Use `show (fun i => Fin.lastCases 0 w i : Fin (r + 1) → k) ⬝ᵥ (A' ^ (j : ℕ) *ᵥ (μ • GlobalTheory.JR.Step.eL r k)) = _`.

Rewrite using `[mulVec_smul, dotProduct_smul, dot_split]`. Simplify using `[x, smul_eq_mul]`. Rewrite using `[e]`. Use function extensionality and compare the values at `j`. Simplify using `using congrArg (μ * ·) (hx j 0)`.
-/
theorem det_Bm_lift (Z : Gl r k) (μ l : k) (h : (Bm Z).det = 0) :
    (Bm (GlobalTheory.JR.Step.lift Z μ l)).det = 0 := by
  obtain ⟨w, hw0, hw⟩ := (Matrix.exists_vecMul_eq_zero_iff (M := Bm Z)).mpr h
  have hw' : ∀ m, w ⬝ᵥ (Z.1 ^ m *ᵥ Z.2.1) = 0 := by
    apply dot_pow_all
    intro i hi
    have := congrFun hw ⟨i, hi⟩
    simpa [vecMul, Bm, dotProduct] using this
  set A' := full Z
  let x : ℕ → Fin r → k := fun j i => (A' ^ j *ᵥ GlobalTheory.JR.Step.eL r k) (Fin.castSucc i)
  have hx : ∀ j m, w ⬝ᵥ (Z.1 ^ m *ᵥ x j) = 0 := by
    intro j
    induction j with
    | zero =>
      intro m
      have h0 : x 0 = 0 := by
        funext i; simp [x, GlobalTheory.JR.Step.eL, Pi.single_apply, Fin.castSucc_ne_last]
      rw [h0, mulVec_zero, dotProduct_zero]
    | succ j ih =>
      intro m
      have hxs : x (j + 1) = Z.1 *ᵥ x j + (A' ^ j *ᵥ GlobalTheory.JR.Step.eL r k) (Fin.last r) • Z.2.1 := by
        funext i
        simp only [x, pow_succ', ← mulVec_mulVec]
        rw [full_mulVec_cs]
        simp [mul_comm]
      rw [hxs, mulVec_add, dotProduct_add, mulVec_mulVec, ← pow_succ, ih, mulVec_smul, dotProduct_smul, hw']
      simp
  refine (Matrix.exists_vecMul_eq_zero_iff (M := Bm (GlobalTheory.JR.Step.lift Z μ l))).mp ?_
  refine ⟨fun i => Fin.lastCases 0 w i, ?_, ?_⟩
  · intro h0
    apply hw0
    funext i
    simpa using congrFun h0 (Fin.castSucc i)
  · have e : (fun i => Fin.lastCases 0 w i : Fin (r + 1) → k) ᵥ* Bm (GlobalTheory.JR.Step.lift Z μ l)
        = fun j : Fin (r + 1) => μ * (w ⬝ᵥ x (j : ℕ)) := by
      funext j
      show (fun i => Fin.lastCases 0 w i : Fin (r + 1) → k) ⬝ᵥ (A' ^ (j : ℕ) *ᵥ (μ • GlobalTheory.JR.Step.eL r k)) = _
      rw [mulVec_smul, dotProduct_smul, dot_split]
      simp [x, smul_eq_mul]
    rw [e]
    funext j
    simpa using congrArg (μ * ·) (hx j 0)

/- English proof (translation)
Take `⟨v, hv0, hv⟩` from `(Matrix.exists_mulVec_eq_zero_iff (M := Cm Z)).mpr h`. Establish `hv' : ∀ m, Z.2.2.1 ⬝ᵥ (Z.1 ^ m *ᵥ v) = 0`. Apply `dot_pow_all` to reduce the goal to its premises. Introduce `i hi`. Use `congrFun hv ⟨i, hi⟩` as an intermediate fact.

Rewrite using `[dotProduct_mulVec]`. Simplify `this` using `[mulVec, Cm, dotProduct]`. Use `set A' := full Z`. Set `u : ℕ → Fin r → k` to `fun j i => (GlobalTheory.JR.Step.eL r k ᵥ* A' ^ j) (Fin.castSucc i)`. Establish `hu : ∀ j m, u j ⬝ᵥ (Z.1 ^ m *ᵥ v) = 0`.

Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `m`. Establish `h0 : u 0 = 0`.

Use function extensionality and compare the values at `i`. Simplify using `only [u, pow_zero, vecMul_one, GlobalTheory.JR.Step.eL]`. Simplify using `[Pi.single_apply, Fin.castSucc_ne_last]`. Rewrite using `[h0, zero_dotProduct]`. Consider the case `succ j ih`.

Introduce `m`. Establish `hus : u (j + 1) = u j ᵥ* Z.1 + (GlobalTheory.JR.Step.eL r k ᵥ* A' ^ j) (Fin.last r) • Z.2.2.1`. Use function extensionality and compare the values at `i`. Simplify using `only [u, pow_succ, ← vecMul_vecMul]`. Rewrite using `[vecMul_full_cs]`.

Simplify using `[mul_comm]`. Rewrite using `[hus, add_dotProduct, ← dotProduct_mulVec, mulVec_mulVec, ← pow_succ', ih, smul_dotProduct, hv']`. Simplify using the standard rewrite rules. Use `(Matrix.exists_mulVec_eq_zero_iff (M := Cm (GlobalTheory.JR.Step.lift Z μ l))).mp ?_` and prove the remaining obligations. Use `⟨fun i => Fin.lastCases 0 v i, ?_, ?_⟩` and prove the remaining obligations.

Introduce `h0`. Apply `hv0` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Simplify using `using congrFun h0 (Fin.castSucc i)`. Use function extensionality and compare the values at `j`.

Simplify using `only [mulVec, Cm, GlobalTheory.JR.Step.lift, Matrix.of_apply]`. Rewrite using `[dot_split]`. Simplify `hu j 0` using `[u, A']`.
-/
theorem det_Cm_lift (Z : Gl r k) (μ l : k) (h : (Cm Z).det = 0) :
    (Cm (GlobalTheory.JR.Step.lift Z μ l)).det = 0 := by
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := Cm Z)).mpr h
  have hv' : ∀ m, Z.2.2.1 ⬝ᵥ (Z.1 ^ m *ᵥ v) = 0 := by
    apply dot_pow_all
    intro i hi
    have := congrFun hv ⟨i, hi⟩
    rw [dotProduct_mulVec]
    simpa [mulVec, Cm, dotProduct] using this
  set A' := full Z
  let u : ℕ → Fin r → k := fun j i => (GlobalTheory.JR.Step.eL r k ᵥ* A' ^ j) (Fin.castSucc i)
  have hu : ∀ j m, u j ⬝ᵥ (Z.1 ^ m *ᵥ v) = 0 := by
    intro j
    induction j with
    | zero =>
      intro m
      have h0 : u 0 = 0 := by
        funext i
        simp only [u, pow_zero, vecMul_one, GlobalTheory.JR.Step.eL]
        simp [Pi.single_apply, Fin.castSucc_ne_last]
      rw [h0, zero_dotProduct]
    | succ j ih =>
      intro m
      have hus : u (j + 1) = u j ᵥ* Z.1 + (GlobalTheory.JR.Step.eL r k ᵥ* A' ^ j) (Fin.last r) • Z.2.2.1 := by
        funext i
        simp only [u, pow_succ, ← vecMul_vecMul]
        rw [vecMul_full_cs]
        simp [mul_comm]
      rw [hus, add_dotProduct, ← dotProduct_mulVec, mulVec_mulVec, ← pow_succ', ih, smul_dotProduct, hv']
      simp
  refine (Matrix.exists_mulVec_eq_zero_iff (M := Cm (GlobalTheory.JR.Step.lift Z μ l))).mp ?_
  refine ⟨fun i => Fin.lastCases 0 v i, ?_, ?_⟩
  · intro h0
    apply hv0
    funext i
    simpa using congrFun h0 (Fin.castSucc i)
  · funext j
    simp only [mulVec, Cm, GlobalTheory.JR.Step.lift, Matrix.of_apply]
    rw [dot_split]
    simpa [u, A'] using hu j 0

end GlobalTheory.JR.DeltaLift

open GlobalTheory.JR.DeltaLift in

/- English proof (translation)
Introduce `k _ r Z μ l h`. Establish `e1` using `(GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants k (r + 1)).2.2.1 (GlobalTheory.JR.Step.lift Z μ l)`. Establish `e0` using `(GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants k r).2.2.1 Z`. Unfold `Delta at h ⊢`. Rewrite `h` using `[← e1, det_mul]`.

Rewrite using `[← e0, det_mul]`. Establish `hC : (Cm (GlobalTheory.JR.Step.lift Z μ l)).det ≠ 0` using `left_ne_zero_of_mul h`. Establish `hB : (Bm (GlobalTheory.JR.Step.lift Z μ l)).det ≠ 0` using `right_ne_zero_of_mul h`. Conclude with `mul_ne_zero (fun hc => hC (det_Cm_lift Z μ l hc)) (fun hb => hB (det_Bm_lift Z μ l hb))`.
-/
theorem GlobalTheory.JR.Step.delta_lift_ne : ∀ (k : Type) [Field k] (r : ℕ) (Z : Gl r k) (μ l : k),
    Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → Delta (inv Z) ≠ 0 := by
  intro k _ r Z μ l h
  have e1 := (GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants k (r + 1)).2.2.1 (GlobalTheory.JR.Step.lift Z μ l)
  have e0 := (GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants k r).2.2.1 Z
  unfold Delta at h ⊢
  rw [← e1, det_mul] at h
  rw [← e0, det_mul]
  have hC : (Cm (GlobalTheory.JR.Step.lift Z μ l)).det ≠ 0 := left_ne_zero_of_mul h
  have hB : (Bm (GlobalTheory.JR.Step.lift Z μ l)).det ≠ 0 := right_ne_zero_of_mul h
  exact mul_ne_zero (fun hc => hC (det_Cm_lift Z μ l hc)) (fun hb => hB (det_Bm_lift Z μ l hb))
