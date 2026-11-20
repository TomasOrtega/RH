import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceOrderCalculusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceIsDVRAndResidueEqGroundStatement

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

namespace GlobalTheory.Nef.LocalIndex

open GlobalTheory.Nef.OrdCalc

variable {k F : Type} [Field k] [Field F] [Algebra k F]

/- English proof (translation)
Distinguish the cases in `hc : c = 0`. Simplify using `[hc]`. Conclude with `(v.2.2 c hc).le`.
-/
theorem const_le_one (v : Place k F) (c : k) : v.1 (algebraMap k F c) ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · exact (v.2.2 c hc).le

/- English proof (translation)
Distinguish the cases in `h0 : y = 0`. Simplify using `[h0]`. Establish `h2` using `(le_one_iff v y h0).1 hy.le`. Establish `h3 : ord v y ≠ 0` using `fun h => hy.ne ((eq_one_iff v y h0).2 h)`. Establish `h4 : ord v π⁻¹ = -1`.

Use `ord_zpow v π (-1)` as an intermediate fact. Rewrite `this` using `[zpow_neg_one, h1]`. Simplify using `using this`. Rewrite using `[le_one_iff v _ (mul_ne_zero (inv_ne_zero hπ) h0), ord_mul v _ _ (inv_ne_zero hπ) h0, h4]`. Use linear arithmetic over natural numbers and integers.
-/
theorem div_unif (v : Place k F) {π : F} (hπ : π ≠ 0) (h1 : ord v π = 1) {y : F}
    (hy : v.1 y < 1) : v.1 (π⁻¹ * y) ≤ 1 := by
  by_cases h0 : y = 0
  · simp [h0]
  have h2 := (le_one_iff v y h0).1 hy.le
  have h3 : ord v y ≠ 0 := fun h => hy.ne ((eq_one_iff v y h0).2 h)
  have h4 : ord v π⁻¹ = -1 := by
    have := ord_zpow v π (-1)
    rw [zpow_neg_one, h1] at this; simpa using this
  rw [le_one_iff v _ (mul_ne_zero (inv_ne_zero hπ) h0), ord_mul v _ _ (inv_ne_zero hπ) h0, h4]
  omega

/- English proof (translation)
Set `m : Submodule k F` to `{ carrier := {y | v.1 y < 1} add_mem' := fun {a b} ha hb => v.1.map_add_lt ha hb zero_mem' := by simp smul_mem' := fun c y hy => by show v.1 (c • y) < 1`. Rewrite using `[Algebra.smul_def, map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (const_le_one v c)) hy }`. Establish `h1 : (1 : F) ∉ m` using `by show ¬ v.1 1 < 1`. Simplify using the standard rewrite rules.

Take `⟨f, hf, hk⟩` from `Submodule.exists_le_ker_of_notMem h1`. Use `⟨f, fun y hy h0 => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `hres y hy`. Establish `h2 : f (y - algebraMap k F c) = 0` using `hk hc`. Rewrite `h2` using `[map_sub, h0, Algebra.algebraMap_eq_smul_one, map_smul, zero_sub, neg_eq_zero, smul_eq_mul, mul_eq_zero]`.

Break down `h2 with h2 | h2` into its components or cases. Simplify `hc` using `[h2]`. Conclude with `absurd h2 hf`.
-/
theorem exists_residue (v : Place k F)
    (hres : ∀ x : F, v.1 x ≤ 1 → ∃ c : k, v.1 (x - algebraMap k F c) < 1) :
    ∃ f : F →ₗ[k] k, ∀ y, v.1 y ≤ 1 → f y = 0 → v.1 y < 1 := by
  let m : Submodule k F :=
    { carrier := {y | v.1 y < 1}
      add_mem' := fun {a b} ha hb => v.1.map_add_lt ha hb
      zero_mem' := by simp
      smul_mem' := fun c y hy => by
        show v.1 (c • y) < 1
        rw [Algebra.smul_def, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (const_le_one v c)) hy }
  have h1 : (1 : F) ∉ m := by
    show ¬ v.1 1 < 1
    simp
  obtain ⟨f, hf, hk⟩ := Submodule.exists_le_ker_of_notMem h1
  refine ⟨f, fun y hy h0 => ?_⟩
  obtain ⟨c, hc⟩ := hres y hy
  have h2 : f (y - algebraMap k F c) = 0 := hk hc
  rw [map_sub, h0, Algebra.algebraMap_eq_smul_one, map_smul, zero_sub, neg_eq_zero, smul_eq_mul,
    mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · simpa [h2] using hc
  · exact absurd h2 hf

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Apply `Valuation.map_sum_le` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[map_mul]`. Conclude with `mul_le_one' (hu i j) (hx j)`.
-/
theorem mulVec_int (v : Place k F) {n : ℕ} (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F)
    (hu : ∀ i j, v.1 (u i j) ≤ 1) (hx : ∀ i, v.1 (x i) ≤ 1) (i : Fin n) :
    v.1 (u.mulVec x i) ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  apply Valuation.map_sum_le
  intro j _
  rw [map_mul]
  exact mul_le_one' (hu i j) (hx j)

/- English proof (translation)
Establish `hn : ¬ ∀ i j, v.1 (a⁻¹ i j) ≤ 1`. Introduce `h`. Establish `h1` using `(det_adj_int v n _ h).1`. Establish `h2 : v.1 (a.det * a⁻¹.det) < 1`. Rewrite using `[map_mul]`.

Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' h1) hlt`. Rewrite `h2` using `[← Matrix.det_mul, Matrix.mul_nonsing_inv a (isUnit_iff_ne_zero.2 hd)]`. Simplify using `at h2`. Use `push Not at hn`. Take `⟨i0, j, hj⟩` from `hn`.

Establish `hb : (fun l => a⁻¹ l j) ≠ 0`. Introduce `h`. Use `congrFun h i0` as an intermediate fact. Simplify using `only [Pi.zero_apply] at this`. Rewrite `hj` using `[this]`.

Simplify using `at hj`. Take `⟨i, hi, -, -, hmax⟩` from `nrm_max v n _ hb`. Establish `hvi : 1 < v.1 (a⁻¹ i j)` using `lt_of_lt_of_le hj (hmax i0)`. Establish `hpos : 0 < v.1 (a⁻¹ i j)` using `lt_trans zero_lt_one hvi`. Use `⟨(a⁻¹ i j)⁻¹ • fun l => a⁻¹ l j, i, ?_, fun l => ?_, fun l => ?_⟩` and prove the remaining obligations.

Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Conclude with `inv_mul_cancel₀ hi`. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]`. Rewrite using `[inv_mul_le_iff₀ hpos, mul_one]`. Conclude with `hmax l`.

Rewrite using `[Matrix.mulVec_smul]`. Establish `e : a.mulVec (fun l => a⁻¹ l j) l = (1 : Matrix (Fin n) (Fin n) F) l j`. Rewrite using `[← Matrix.mul_nonsing_inv a (isUnit_iff_ne_zero.2 hd)]`. Both sides reduce to the same expression. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀, e]`.

Rewrite using `[inv_mul_lt_iff₀ hpos, mul_one]`. Use `lt_of_le_of_lt ?_ hvi` and prove the remaining obligations. Apply the tactic sequence `by_cases h : l = j <;> simp [Matrix.one_apply, h]`.
-/
theorem exists_primitive (v : Place k F) {n : ℕ} (a : Matrix (Fin n) (Fin n) F) (hd : a.det ≠ 0)
    (hlt : v.1 a.det < 1) :
    ∃ (c : Fin n → F) (i : Fin n), c i = 1 ∧ (∀ l, v.1 (c l) ≤ 1) ∧ ∀ l, v.1 (a.mulVec c l) < 1 := by
  have hn : ¬ ∀ i j, v.1 (a⁻¹ i j) ≤ 1 := by
    intro h
    have h1 := (det_adj_int v n _ h).1
    have h2 : v.1 (a.det * a⁻¹.det) < 1 := by
      rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right' h1) hlt
    rw [← Matrix.det_mul, Matrix.mul_nonsing_inv a (isUnit_iff_ne_zero.2 hd)] at h2
    simp at h2
  push Not at hn
  obtain ⟨i0, j, hj⟩ := hn
  have hb : (fun l => a⁻¹ l j) ≠ 0 := by
    intro h
    have := congrFun h i0
    simp only [Pi.zero_apply] at this
    rw [this] at hj
    simp at hj
  obtain ⟨i, hi, -, -, hmax⟩ := nrm_max v n _ hb
  have hvi : 1 < v.1 (a⁻¹ i j) := lt_of_lt_of_le hj (hmax i0)
  have hpos : 0 < v.1 (a⁻¹ i j) := lt_trans zero_lt_one hvi
  refine ⟨(a⁻¹ i j)⁻¹ • fun l => a⁻¹ l j, i, ?_, fun l => ?_, fun l => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]; exact inv_mul_cancel₀ hi
  · simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    rw [inv_mul_le_iff₀ hpos, mul_one]; exact hmax l
  · rw [Matrix.mulVec_smul]
    have e : a.mulVec (fun l => a⁻¹ l j) l = (1 : Matrix (Fin n) (Fin n) F) l j := by
      rw [← Matrix.mul_nonsing_inv a (isUnit_iff_ne_zero.2 hd)]; rfl
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀, e]
    rw [inv_mul_lt_iff₀ hpos, mul_one]
    refine lt_of_le_of_lt ?_ hvi
    by_cases h : l = j <;> simp [Matrix.one_apply, h]

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero`. Introduce `a hd ha hN`. Establish `hu : Unimod v a` using `⟨ha, (eq_one_iff v _ hd).2 (by simpa using hN)⟩`. Conclude with `⟨0, fun x hx _ i => mulVec_int v _ x (unimod_mul_inv v n a a hu hu).2.1 hx i⟩`.

Consider the case `succ N ih`. Introduce `a hd ha hN`. Take `⟨π, hπ, hπ1⟩` from `exists_unif v`. Take `⟨f, hf⟩` from `exists_residue v hres`. Establish `hlt : v.1 a.det < 1` using `lt_of_le_of_ne (det_adj_int v n a ha).1 (fun h => by`.

Use `(eq_one_iff v _ hd).1 h` as an intermediate fact. Use the proof step `omega)`. Take `⟨c, i, hci, hc, hac⟩` from `exists_primitive v a hd hlt`. Use `set T : Matrix (Fin n) (Fin n) F := (1 : Matrix (Fin n) (Fin n) F).updateCol i (π⁻¹ • c) with hT`. Establish `hTd : T.det = π⁻¹`.

Rewrite using `[hT, ← Matrix.cramer_apply, Matrix.cramer_one]`. Simplify using `[hci]`. Establish `h4 : ord v π⁻¹ = -1`. Use `ord_zpow v π (-1)` as an intermediate fact. Rewrite `this` using `[zpow_neg_one, hπ1]`.

Simplify using `using this`. Establish `hd' : (a * T).det ≠ 0`. Rewrite using `[Matrix.det_mul, hTd]`. Conclude with `mul_ne_zero hd (inv_ne_zero hπ)`. Establish `ha' : ∀ l j, v.1 ((a * T) l j) ≤ 1`.

Introduce `l j`. Distinguish the cases in `h : j = i`. Establish `e : (a * T) l j = π⁻¹ * a.mulVec c l`. Substitute `h` using the available equality. Simplify using `only [hT, Matrix.mul_apply, Matrix.updateCol_self, Matrix.mulVec, dotProduct, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]`.

Conclude with `Finset.sum_congr rfl fun _ _ => by ring`. Rewrite using `[e]`. Conclude with `div_unif v hπ hπ1 (hac l)`. Establish `e : (a * T) l j = a l j` using `by conv_rhs => rw [← Matrix.mul_one a]`. Simplify using `only [hT, Matrix.mul_apply, Matrix.updateCol_ne h]`.

Rewrite using `[e]`. Conclude with `ha l j`. Establish `hN' : ord v (a * T).det = N`. Rewrite using `[Matrix.det_mul, hTd, ord_mul v _ _ hd (inv_ne_zero hπ), hN, h4]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨φ, hφ⟩` from `ih (a * T) hd' ha' hN'`. Set `ψ : (Fin n → F) →ₗ[k] k` to `f ∘ₗ (LinearMap.proj i) ∘ₗ ((Matrix.mulVecLin (a * T)⁻¹).restrictScalars k)`. Use `⟨LinearMap.pi fun j => Fin.cases ψ (fun j => (LinearMap.proj j) ∘ₗ φ) j, fun x hx h0 l => ?_⟩` and prove the remaining obligations. Establish `h1 : φ x = 0` using `funext fun j => by simpa using congrFun h0 j.succ`.

Establish `h2 : f ((a * T)⁻¹.mulVec x i) = 0` using `by simpa [ψ] using congrFun h0 0`. Establish `hy` using `hφ x hx h1`. Establish `hyi` using `div_unif v hπ hπ1 (hf _ (hy i) h2)`. Establish `e : a⁻¹ = T * (a * T)⁻¹`. Rewrite using `[Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv T (isUnit_iff_ne_zero.2 (hTd ▸ inv_ne_zero hπ)), Matrix.one_mul]`.

Rewrite using `[e, ← Matrix.mulVec_mulVec]`. Generalize the expression as in `(a * T)⁻¹.mulVec x = y at hy hyi`. Simplify using `only [Matrix.mulVec, dotProduct]`. Apply `Valuation.map_sum_le` to reduce the goal to its premises. Introduce `j _`.

Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Establish `e2 : T l j * y j = c l * (π⁻¹ * y j)`. Simplify using `only [hT, Matrix.updateCol_self, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e2, map_mul]`. Conclude with `mul_le_one' (hc l) hyi`. Rewrite using `[map_mul]`. Use `mul_le_one' ?_ (hy j)` and prove the remaining obligations. Simplify using `only [hT, Matrix.updateCol_ne h]`.

Apply the tactic sequence `by_cases h' : l = j <;> simp [Matrix.one_apply, h']`.
-/
theorem exists_functional_inv_mulVec_integral_of_order (v : Place k F)
    (hres : ∀ x : F, v.1 x ≤ 1 → ∃ c : k, v.1 (x - algebraMap k F c) < 1) (n N : ℕ) :
    ∀ a : Matrix (Fin n) (Fin n) F, a.det ≠ 0 → (∀ i j, v.1 (a i j) ≤ 1) → ord v a.det = N →
      ∃ φ : (Fin n → F) →ₗ[k] (Fin N → k), ∀ x : Fin n → F, (∀ i, v.1 (x i) ≤ 1) → φ x = 0 →
        ∀ i, v.1 (a⁻¹.mulVec x i) ≤ 1 := by
  induction N with
  | zero =>
    intro a hd ha hN
    have hu : Unimod v a := ⟨ha, (eq_one_iff v _ hd).2 (by simpa using hN)⟩
    exact ⟨0, fun x hx _ i => mulVec_int v _ x (unimod_mul_inv v n a a hu hu).2.1 hx i⟩
  | succ N ih =>
    intro a hd ha hN
    obtain ⟨π, hπ, hπ1⟩ := exists_unif v
    obtain ⟨f, hf⟩ := exists_residue v hres
    have hlt : v.1 a.det < 1 := lt_of_le_of_ne (det_adj_int v n a ha).1 (fun h => by
      have := (eq_one_iff v _ hd).1 h
      omega)
    obtain ⟨c, i, hci, hc, hac⟩ := exists_primitive v a hd hlt
    set T : Matrix (Fin n) (Fin n) F := (1 : Matrix (Fin n) (Fin n) F).updateCol i (π⁻¹ • c) with hT
    have hTd : T.det = π⁻¹ := by
      rw [hT, ← Matrix.cramer_apply, Matrix.cramer_one]; simp [hci]
    have h4 : ord v π⁻¹ = -1 := by
      have := ord_zpow v π (-1)
      rw [zpow_neg_one, hπ1] at this; simpa using this
    have hd' : (a * T).det ≠ 0 := by
      rw [Matrix.det_mul, hTd]; exact mul_ne_zero hd (inv_ne_zero hπ)
    have ha' : ∀ l j, v.1 ((a * T) l j) ≤ 1 := by
      intro l j
      by_cases h : j = i
      · have e : (a * T) l j = π⁻¹ * a.mulVec c l := by
          subst h
          simp only [hT, Matrix.mul_apply, Matrix.updateCol_self, Matrix.mulVec, dotProduct,
            Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
          exact Finset.sum_congr rfl fun _ _ => by ring
        rw [e]; exact div_unif v hπ hπ1 (hac l)
      · have e : (a * T) l j = a l j := by
          conv_rhs => rw [← Matrix.mul_one a]
          simp only [hT, Matrix.mul_apply, Matrix.updateCol_ne h]
        rw [e]; exact ha l j
    have hN' : ord v (a * T).det = N := by
      rw [Matrix.det_mul, hTd, ord_mul v _ _ hd (inv_ne_zero hπ), hN, h4]; push_cast; ring
    obtain ⟨φ, hφ⟩ := ih (a * T) hd' ha' hN'
    let ψ : (Fin n → F) →ₗ[k] k :=
      f ∘ₗ (LinearMap.proj i) ∘ₗ ((Matrix.mulVecLin (a * T)⁻¹).restrictScalars k)
    refine ⟨LinearMap.pi fun j => Fin.cases ψ (fun j => (LinearMap.proj j) ∘ₗ φ) j,
      fun x hx h0 l => ?_⟩
    have h1 : φ x = 0 := funext fun j => by simpa using congrFun h0 j.succ
    have h2 : f ((a * T)⁻¹.mulVec x i) = 0 := by simpa [ψ] using congrFun h0 0
    have hy := hφ x hx h1
    have hyi := div_unif v hπ hπ1 (hf _ (hy i) h2)
    have e : a⁻¹ = T * (a * T)⁻¹ := by
      rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv T (isUnit_iff_ne_zero.2 (hTd ▸ inv_ne_zero hπ)), Matrix.one_mul]
    rw [e, ← Matrix.mulVec_mulVec]
    generalize (a * T)⁻¹.mulVec x = y at hy hyi
    simp only [Matrix.mulVec, dotProduct]
    apply Valuation.map_sum_le
    intro j _
    by_cases h : j = i
    · subst h
      have e2 : T l j * y j = c l * (π⁻¹ * y j) := by
        simp only [hT, Matrix.updateCol_self, Pi.smul_apply, smul_eq_mul]; ring
      rw [e2, map_mul]
      exact mul_le_one' (hc l) hyi
    · rw [map_mul]
      refine mul_le_one' ?_ (hy j)
      simp only [hT, Matrix.updateCol_ne h]
      by_cases h' : l = j <;> simp [Matrix.one_apply, h']

end GlobalTheory.Nef.LocalIndex

open GlobalTheory.Nef.OrdCalc GlobalTheory.Nef.LocalIndex in

/- English proof (translation)
Introduce `k F _ _ _ _ _ hF v n h hd hi`. Establish `e : h⁻¹.det = h.det⁻¹` using `by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`. Establish `hd' : h⁻¹.det ≠ 0` using `e ▸ inv_ne_zero hd`. Establish `h0` using `(le_one_iff v _ hd').1 (det_adj_int v n _ hi).1`. Establish `h1 : ord v h⁻¹.det = -ord v h.det`.

Use `ord_zpow v h.det (-1)` as an intermediate fact. Rewrite `this` using `[zpow_neg_one]`. Rewrite using `[e, this]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨N, hN⟩` from `Int.eq_ofNat_of_zero_le h0`.

Take `⟨φ, hφ⟩` from `exists_functional_inv_mulVec_integral_of_order v (GlobalTheory.T.functionFieldPlace_isDVR_and_residue_eq_ground k F hF v).2 n N h⁻¹ hd' hi hN`. Rewrite `hφ` using `[Matrix.nonsing_inv_nonsing_inv h (isUnit_iff_ne_zero.2 hd)]`. Conclude with `⟨N, φ, by rw [← hN, h1], hφ⟩`.
-/
theorem GlobalTheory.Nef.local_index : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (v : Place k F) (n : ℕ) (h : Matrix (Fin n) (Fin n) F), h.det ≠ 0 → (∀ i j, v.1 (h⁻¹ i j) ≤ 1) → ∃ (N : ℕ) (φ : (Fin n → F) →ₗ[k] (Fin N → k)), (N : ℤ) = -ord v h.det ∧ ∀ x : Fin n → F, (∀ i, v.1 (x i) ≤ 1) → φ x = 0 → ∀ i, v.1 (h.mulVec x i) ≤ 1 := by
  intro k F _ _ _ _ _ hF v n h hd hi
  have e : h⁻¹.det = h.det⁻¹ := by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hd' : h⁻¹.det ≠ 0 := e ▸ inv_ne_zero hd
  have h0 := (le_one_iff v _ hd').1 (det_adj_int v n _ hi).1
  have h1 : ord v h⁻¹.det = -ord v h.det := by
    have := ord_zpow v h.det (-1)
    rw [zpow_neg_one] at this; rw [e, this]; ring
  obtain ⟨N, hN⟩ := Int.eq_ofNat_of_zero_le h0
  obtain ⟨φ, hφ⟩ := exists_functional_inv_mulVec_integral_of_order v (GlobalTheory.T.functionFieldPlace_isDVR_and_residue_eq_ground k F hF v).2 n N h⁻¹ hd' hi hN
  rw [Matrix.nonsing_inv_nonsing_inv h (isUnit_iff_ne_zero.2 hd)] at hφ
  exact ⟨N, φ, by rw [← hN, h1], hφ⟩
