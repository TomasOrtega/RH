import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.NChart
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.OneParameterSubgroups.ExistsCyclic

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base
open ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
open Matrix Formalism.QuantumDeterminants Finset
open scoped Matrix.Norms.Operator

variable {k r : ℕ}

def nxt (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) :=
  if a.val + 1 < r then ⟨a.val + 1, by omega⟩ else ⟨r + k, by omega⟩

/- English proof (translation)
Unfold `Formalism.MainNotions.S.ellA nxt`. Use `split_ifs with h`. Both sides reduce to the same expression. Simplify using `[z0, bvec, wI]`.
-/
theorem ellA_eq (g : Mat k r) (a : Fin r) :
    Formalism.MainNotions.S.ellA k r (z0 k r) g a = g (eI k r a) (nxt k r a) := by
  unfold Formalism.MainNotions.S.ellA nxt
  split_ifs with h
  · rfl
  · simp [z0, bvec, wI]

/- English proof (translation)
Use `a.isLt` as an intermediate fact. Unfold `levB nxt eI`. Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `split_ifs <;> simp_all <;> omega`. Simplify using the standard rewrite rules.
-/
theorem lev_nxt (a : Fin r) : levB k r (nxt k r a) = a.val + 1 ∧ levB k r (eI k r a) = a.val := by
  have := a.isLt
  unfold levB nxt eI
  constructor
  · split_ifs <;> simp_all <;> omega
  · simp

/- English proof (translation)
Take `⟨hY1, hY2⟩` from `mem_lieN.mp hY`. Establish `hY2' : Hpk k r * Yᴴ * Hpk k r = -Y` using `hY2`. Set `A : Mat k r` to `∑ a : Fin r, Matrix.single (nxt k r a) (eI k r a) 1`. Establish `hA : ∀ i j, A i j = ∑ a : Fin r, if nxt k r a = i ∧ eI k r a = j then 1 else 0`. Introduce `i j`.

Simplify using `[A, Matrix.sum_apply, Matrix.single_apply]`. Establish `hAe : ∀ (a : Fin r) i, A i (eI k r a) = if i = nxt k r a then 1 else 0`. Introduce `a i`. Rewrite using `[hA, Finset.sum_eq_single a]`. Simplify using `[eq_comm]`.

Introduce `b _ hb`. Rewrite using `[if_neg]; rintro ⟨_, h⟩; exact hb (Fin.ext (by have := congrArg Fin.val h; exact this))`. Simplify using the standard rewrite rules. Establish `hA0 : ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → A i j = 0`. Introduce `i j hj`.

Rewrite using `[hA]`. Use `Finset.sum_eq_zero fun a _ => if_neg ?_` and prove the remaining obligations. Introduce and unpack `⟨_, rfl⟩`. Use `a.isLt` as an intermediate fact. Simplify using `[eI] at hj`.

Use linear arithmetic over natural numbers and integers. Establish `hA1 : ∀ i j : Fin (2 * r + k + 1), r ≤ i.val → i.val ≠ r + k → A i j = 0`. Introduce `i j h1 h2`. Rewrite using `[hA]`. Use `Finset.sum_eq_zero fun a _ => if_neg ?_` and prove the remaining obligations.

Introduce and unpack `⟨rfl, _⟩`. Apply the tactic sequence `unfold nxt at h1 h2; split_ifs at h1 h2 <;> simp at h1 h2; omega`. Use `set R : Mat k r := Ξ - A - Hpk k r * Aᴴ * Hpk k r with hR`. Establish `hH2 : ∀ X : Mat k r, Hpk k r * (Hpk k r * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, Hpk_sq, Matrix.one_mul]`.

Establish `hRsa : Hpk k r * Rᴴ * Hpk k r = R`. Rewrite using `[hR, conjTranspose_sub, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, Hpk_herm, Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, hsa, hH2, Matrix.mul_assoc A, Hpk_sq, Matrix.mul_one]`. Normalize the expressions using the abelian group laws. Establish `hRcol : ∀ i j : Fin (2 * r + k + 1), j.val < r + k → R i j = 0`. Introduce `i j hj`.

Establish `h3 : (Hpk k r * Aᴴ * Hpk k r) i j = 0`. Rewrite using `[mul_Hpk_apply, Hpk_mul_apply, conjTranspose_apply, hA1, star_zero, mul_zero, zero_mul]`. Apply the tactic sequence `rw [flipB_val]; split_ifs <;> omega`. Apply the tactic sequence `rw [flipB_val]; split_ifs <;> omega`. Rewrite using `[hR, Matrix.sub_apply, Matrix.sub_apply, h3, sub_zero]`.

Distinguish the cases in `h : j.val < r`. Establish `e : j = eI k r ⟨j.val, h⟩` using `rfl`. Rewrite using `[e, he, hAe, sub_self]`. Rewrite using `[hw i j (by omega) hj, hA0 i j (by omega), sub_self]`. Establish `hRY : trace (R * Y) = 0`.

Rewrite using `[Matrix.trace]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.diag_apply, Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Establish `hi` using `i.isLt`.

Distinguish the cases in `hj : j.val < r + k`. Rewrite using `[hRcol i j hj, zero_mul]`. Distinguish the cases in `hi2 : r + k < i.val`. Rewrite using `[← hRsa, mul_Hpk_apply, Hpk_mul_apply, conjTranspose_apply, hRcol, star_zero, mul_zero, zero_mul, zero_mul]`. Apply the tactic sequence `rw [flipB_val]; split_ifs <;> omega`.

Rewrite using `[hY1 j i, mul_zero]`. Apply the tactic sequence `unfold levB; split_ifs <;> omega`. Establish `hAY : trace (A * Y) = ∑ a, Y (eI k r a) (nxt k r a)`. Simplify using `only [A, Matrix.sum_mul, Matrix.trace_sum, Matrix.trace_single_mul, smul_eq_mul, one_mul]`. Establish `hHY : Hpk k r * Y * Hpk k r = -Yᴴ`.

Use `congrArg conjTranspose hY2'` as an intermediate fact. Rewrite `this` using `[conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, Hpk_herm, ← Matrix.mul_assoc, conjTranspose_neg]`. Then use the resulting hypothesis. Establish `hA2 : trace (Hpk k r * Aᴴ * Hpk k r * Y) = -star (trace (A * Y))`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hHY, Matrix.mul_neg, Matrix.trace_neg, ← conjTranspose_mul, Matrix.trace_conjTranspose, Matrix.trace_mul_comm]`. Establish `: Ξ = R + A + Hpk k r * Aᴴ * Hpk k r` using `by rw [hR]; abel`.

Rewrite using `[this, Matrix.add_mul, Matrix.add_mul, Matrix.trace_add, Matrix.trace_add, hRY, hA2, hAY, zero_add, Finset.sum_sub_distrib, star_sum, sub_eq_add_neg]`. Both sides reduce to the same expression.
-/
theorem trace_shift (Ξ Y : Mat k r) (hsa : Hpk k r * Ξᴴ * Hpk k r = Ξ)
    (he : ∀ (a : Fin r) i, Ξ i (eI k r a) = if i = nxt k r a then 1 else 0)
    (hw : ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val < r + k → Ξ i j = 0)
    (hY : Y ∈ lieN (levF (levB k r)) (adjH (Hpk k r))) :
    trace (Ξ * Y) = ∑ a, (Y (eI k r a) (nxt k r a) - starRingEnd ℂ (Y (eI k r a) (nxt k r a))) := by
  obtain ⟨hY1, hY2⟩ := mem_lieN.mp hY
  have hY2' : Hpk k r * Yᴴ * Hpk k r = -Y := hY2
  let A : Mat k r := ∑ a : Fin r, Matrix.single (nxt k r a) (eI k r a) 1
  have hA : ∀ i j, A i j = ∑ a : Fin r, if nxt k r a = i ∧ eI k r a = j then 1 else 0 := by
    intro i j; simp [A, Matrix.sum_apply, Matrix.single_apply]
  have hAe : ∀ (a : Fin r) i, A i (eI k r a) = if i = nxt k r a then 1 else 0 := by
    intro a i
    rw [hA, Finset.sum_eq_single a]
    · simp [eq_comm]
    · intro b _ hb
      rw [if_neg]; rintro ⟨_, h⟩; exact hb (Fin.ext (by have := congrArg Fin.val h; exact this))
    · simp
  have hA0 : ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → A i j = 0 := by
    intro i j hj
    rw [hA]; refine Finset.sum_eq_zero fun a _ => if_neg ?_
    rintro ⟨_, rfl⟩; have := a.isLt; simp [eI] at hj; omega
  have hA1 : ∀ i j : Fin (2 * r + k + 1), r ≤ i.val → i.val ≠ r + k → A i j = 0 := by
    intro i j h1 h2
    rw [hA]; refine Finset.sum_eq_zero fun a _ => if_neg ?_
    rintro ⟨rfl, _⟩
    unfold nxt at h1 h2; split_ifs at h1 h2 <;> simp at h1 h2; omega
  set R : Mat k r := Ξ - A - Hpk k r * Aᴴ * Hpk k r with hR
  have hH2 : ∀ X : Mat k r, Hpk k r * (Hpk k r * X) = X := fun X => by
    rw [← Matrix.mul_assoc, Hpk_sq, Matrix.one_mul]
  have hRsa : Hpk k r * Rᴴ * Hpk k r = R := by
    rw [hR, conjTranspose_sub, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, Hpk_herm, Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.sub_mul, hsa, hH2, Matrix.mul_assoc A, Hpk_sq, Matrix.mul_one]
    abel
  have hRcol : ∀ i j : Fin (2 * r + k + 1), j.val < r + k → R i j = 0 := by
    intro i j hj
    have h3 : (Hpk k r * Aᴴ * Hpk k r) i j = 0 := by
      rw [mul_Hpk_apply, Hpk_mul_apply, conjTranspose_apply, hA1, star_zero, mul_zero, zero_mul]
      · rw [flipB_val]; split_ifs <;> omega
      · rw [flipB_val]; split_ifs <;> omega
    rw [hR, Matrix.sub_apply, Matrix.sub_apply, h3, sub_zero]
    by_cases h : j.val < r
    · have e : j = eI k r ⟨j.val, h⟩ := rfl
      rw [e, he, hAe, sub_self]
    · rw [hw i j (by omega) hj, hA0 i j (by omega), sub_self]
  have hRY : trace (R * Y) = 0 := by
    rw [Matrix.trace]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hi := i.isLt
    by_cases hj : j.val < r + k
    · rw [hRcol i j hj, zero_mul]
    · by_cases hi2 : r + k < i.val
      · rw [← hRsa, mul_Hpk_apply, Hpk_mul_apply, conjTranspose_apply, hRcol, star_zero, mul_zero,
          zero_mul, zero_mul]
        rw [flipB_val]; split_ifs <;> omega
      · rw [hY1 j i, mul_zero]
        unfold levB; split_ifs <;> omega
  have hAY : trace (A * Y) = ∑ a, Y (eI k r a) (nxt k r a) := by
    simp only [A, Matrix.sum_mul, Matrix.trace_sum, Matrix.trace_single_mul, smul_eq_mul,
      one_mul]
  have hHY : Hpk k r * Y * Hpk k r = -Yᴴ := by
    have := congrArg conjTranspose hY2'
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, Hpk_herm,
      ← Matrix.mul_assoc, conjTranspose_neg] at this
  have hA2 : trace (Hpk k r * Aᴴ * Hpk k r * Y) = -star (trace (A * Y)) := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hHY,
      Matrix.mul_neg, Matrix.trace_neg, ← conjTranspose_mul, Matrix.trace_conjTranspose,
      Matrix.trace_mul_comm]
  have : Ξ = R + A + Hpk k r * Aᴴ * Hpk k r := by rw [hR]; abel
  rw [this, Matrix.add_mul, Matrix.add_mul, Matrix.trace_add, Matrix.trace_add, hRY, hA2, hAY,
    zero_add, Finset.sum_sub_distrib, star_sum, sub_eq_add_neg]
  rfl

/- English proof (translation)
Establish `h` using `isFilB.exp_shear.2 0 Y hY 0 (Submodule.zero_mem _) (by simpa using hY)`. Establish `h2` using `h (eI k r a) (nxt k r a) (by rw [(lev_nxt a).1, (lev_nxt a).2]; omega)`. Establish `hne : eI k r a ≠ nxt k r a` using `fun e => by`. Use `(lev_nxt (k := k) a).1` as an intermediate fact. Rewrite `this` using `[← e, (lev_nxt a).2]`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [NormedSpace.exp_zero, sub_self, sub_zero, Matrix.sub_apply, Matrix.one_apply_ne hne] at h2`. Conclude with `sub_eq_zero.mp h2`.
-/
theorem exp_entry (Y : Mat k r) (hY : Y ∈ levF (levB k r) 0) (a : Fin r) :
    NormedSpace.exp Y (eI k r a) (nxt k r a) = Y (eI k r a) (nxt k r a) := by
  have h := isFilB.exp_shear.2 0 Y hY 0 (Submodule.zero_mem _) (by simpa using hY)
  have h2 := h (eI k r a) (nxt k r a) (by rw [(lev_nxt a).1, (lev_nxt a).2]; omega)
  have hne : eI k r a ≠ nxt k r a := fun e => by
    have := (lev_nxt (k := k) a).1; rw [← e, (lev_nxt a).2] at this; omega
  simp only [NormedSpace.exp_zero, sub_self, sub_zero, Matrix.sub_apply, Matrix.one_apply_ne hne]
    at h2
  exact sub_eq_zero.mp h2

def emb (k : ℕ) (v : Fin (2 * r + 1) → ℝ) : Fin (2 * r + k + 1) → ℂ :=
  fun i => if h : k ≤ i.val then ((v ⟨i.val - k, by omega⟩ : ℝ) : ℂ) else 0

/- English proof (translation)
Rewrite using `[← Equiv.sum_comp (finCongr (show k + (2 * r + 1) = 2 * r + k + 1 by omega)), Fin.sum_univ_add]`. Both sides reduce to the same expression.
-/
theorem sum_split (f : Fin (2 * r + k + 1) → ℂ) :
    ∑ i, f i = ∑ j : Fin k, f ⟨j.val, by omega⟩ + ∑ s : Fin (2 * r + 1), f ⟨k + s.val, by omega⟩ := by
  rw [← Equiv.sum_comp (finCongr (show k + (2 * r + 1) = 2 * r + k + 1 by omega)), Fin.sum_univ_add]
  rfl

def formJ (k r : ℕ) (x y : Fin (2 * r + k + 1) → ℂ) : ℂ :=
  ∑ s, star (x s) * (if parEps k r s then 1 else -1) * y s

/- English proof (translation)
Rewrite using `[formJ, sum_split, Finset.sum_eq_zero, zero_add, formV]`. Use `push_cast`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Establish `e : (if parEps k r ⟨k + s.val, by omega⟩ then (1 : ℂ) else -1) = (-1) ^ (s.val + 1)`. Establish `e1 : k + s.val - (k - 1) = s.val + 1` using `by omega`.

Simplify using `only [parEps, show ¬ (k + s.val < k - 1) by omega, if_false, e1, decide_eq_true_eq]`. Use `split_ifs with h`. Rewrite using `[Even.neg_one_pow (Nat.even_iff.mpr h)]`. Rewrite using `[Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))]`. Rewrite using `[e]`.

Simplify using `only [emb, show k ≤ k + s.val by omega, dif_pos, Nat.add_sub_cancel_left, Fin.eta, Complex.star_def, Complex.conj_ofReal]`. Expand and normalize the polynomial expressions, which then agree. Introduce `j _`. Simplify using `[emb, j.isLt]`.
-/
theorem formJ_emb (hk : 1 ≤ k) (u v : Fin (2 * r + 1) → ℝ) :
    formJ k r (emb k u) (emb k v) = (formV u v : ℝ) := by
  rw [formJ, sum_split, Finset.sum_eq_zero, zero_add, formV]
  · push_cast
    refine Finset.sum_congr rfl fun s _ => ?_
    have e : (if parEps k r ⟨k + s.val, by omega⟩ then (1 : ℂ) else -1) = (-1) ^ (s.val + 1) := by
      have e1 : k + s.val - (k - 1) = s.val + 1 := by omega
      simp only [parEps, show ¬ (k + s.val < k - 1) by omega, if_false, e1, decide_eq_true_eq]
      split_ifs with h
      · rw [Even.neg_one_pow (Nat.even_iff.mpr h)]
      · rw [Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))]
    rw [e]
    simp only [emb, show k ≤ k + s.val by omega, dif_pos, Nat.add_sub_cancel_left, Fin.eta,
      Complex.star_def, Complex.conj_ofReal]
    ring
  · intro j _
    simp [emb, j.isLt]

/- English proof (translation)
Rewrite using `[formJ, Finset.sum_eq_single j]`. Establish `: parEps k r j = true`. Unfold `parEps`. Use `split_ifs`. Both sides reduce to the same expression.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Simplify using `[bvec, this]`. Introduce `s _ hs`. Simplify using `[bvec, hs]`.

Simplify using the standard rewrite rules.
-/
theorem formJ_bvec_left (j : Fin (2 * r + k + 1)) (hj : j.val < k) (y : Fin (2 * r + k + 1) → ℂ) :
    formJ k r (bvec j) y = y j := by
  rw [formJ, Finset.sum_eq_single j]
  · have : parEps k r j = true := by
      unfold parEps; split_ifs
      · rfl
      · simp; omega
    simp [bvec, this]
  · intro s _ hs; simp [bvec, hs]
  · simp

/- English proof (translation)
Rewrite using `[formJ, Finset.sum_eq_single j]`. Establish `: parEps k r j = true`. Unfold `parEps`. Use `split_ifs`. Both sides reduce to the same expression.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Simplify using `[bvec, this]`. Introduce `s _ hs`. Simplify using `[bvec, hs]`.

Simplify using the standard rewrite rules.
-/
theorem formJ_bvec_right (j : Fin (2 * r + k + 1)) (hj : j.val < k) (x : Fin (2 * r + k + 1) → ℂ) :
    formJ k r x (bvec j) = star (x j) := by
  rw [formJ, Finset.sum_eq_single j]
  · have : parEps k r j = true := by
      unfold parEps; split_ifs
      · rfl
      · simp; omega
    simp [bvec, this]
  · intro s _ hs; simp [bvec, hs]
  · simp

/- English proof (translation)
Simplify using `[emb, hj]`.
-/
theorem emb_lt (v : Fin (2 * r + 1) → ℝ) (j : Fin (2 * r + k + 1)) (hj : j.val < k) :
    emb k v j = 0 := by simp [emb, hj]

/- English proof (translation)
Take `⟨e, f, z, hee, hff, hfe, hez, hfz, hzz, hx⟩` from `frame r (fun s => -((s.val : ℝ) + 1)) (fun a b hab => by`. Establish `: (a.val : ℝ) < b.val` using `by exact_mod_cast hab`. Simplify using `only`. Use the proof step `linarith)`. Set `col : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ` to `fun j => if h : j.val < r then emb k (e ⟨j.val, h⟩) else if h2 : j.val < r + k then bvec ⟨j.val - r, by omega⟩ else if h3 : j.val = r + k then emb k z else emb k (f ⟨2 * r + k - j.val, by omega⟩)`.

Set `P : Mat k r` to `Matrix.of fun i j => col j i`. Establish `hG : Pᴴ * Formalism.REAL.Jm (parEps k r) * P = Hpk k r`. Use extensionality with `i j`. Establish `h0 : (Pᴴ * Formalism.REAL.Jm (parEps k r) * P) i j = formJ k r (col i) (col j)`. Simplify using `[Matrix.mul_apply, Formalism.REAL.Jm, Matrix.diagonal_apply, formJ, P]`.

Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`. Rewrite using `[h0, Hpk_apply]`. Simplify using `only [col, Fin.ext_iff, flipB_val, sgnB]`. Apply the tactic sequence `split_ifs <;> first`.

Consider the case `omega`. Consider the case `(rw [formJ_emb hk]`. Simplify using `only [hee, hff, hfe, hez, hfz, hzz, formV_symm (e _) (f _), formV_symm z (e _), formV_symm z (f _), Fin.ext_iff]`. Apply the tactic sequence `first | (push_cast; rfl) | (split_ifs <;> first | omega | simp))`. Consider the case `(rw [formJ_bvec_left _ (by simp only; omega), emb_lt _ _ (by simp only; omega)])`.

Consider the case `(rw [formJ_bvec_right _ (by simp only; omega), emb_lt _ _ (by simp only; omega), star_zero])`. Consider the case `(rw [formJ_bvec_left _ (by simp only; omega)]`. Simplify using `only [bvec, Pi.single_apply, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | omega | rfl)`. Establish `hL : (Hpk k r * Pᴴ * Formalism.REAL.Jm (parEps k r)) * P = 1`.

Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Pᴴ, hG, Hpk_sq]`. Establish `hdet : IsUnit P.det` using `Matrix.isUnit_det_of_left_inverse hL`. Establish `hinv : P⁻¹ = Hpk k r * Pᴴ * Formalism.REAL.Jm (parEps k r)` using `Matrix.inv_eq_left_inv hL`. Establish `hPP : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul _ hdet`. Use `⟨P, ⟨(Matrix.isUnit_iff_isUnit_det _).mpr hdet, hG⟩, fun j => ?_, fun Y hY => ?_⟩` and prove the remaining obligations.

Use `j.isLt` as an intermediate fact. Use function extensionality and compare the values at `i`. Simplify using `only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, P, Matrix.of_apply, col, wI, Fin.val_castSucc, show ¬ (r + j.val < r) by omega, show r + j.val < r + k by omega, dif_pos, dif_neg, not_false_eq_true, Nat.add_sub_cancel_left]`. Use `set D := dMat (dNode k r) with hD`. Establish `hDP : ∀ i j, (D * P) i j = (dNode k r i : ℂ) * col j i` using `fun i j => by`.

Simplify using `[hD, dMat, Matrix.diagonal_mul, P]`. Establish `hcol : ∀ j j' : Fin (2 * r + k + 1), (∀ i, (D * P) i j = P i j') → ∀ i, (P⁻¹ * (D * P)) i j = if i = j' then 1 else 0`. Introduce `j j' h i`. Rewrite using `[← Matrix.one_apply, ← hPP, Matrix.mul_apply, Matrix.mul_apply]`. Simplify using `only [h]`.

Rewrite using `[← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc D, ← Matrix.mul_assoc]`. Use `trace_shift _ Y ?_ (fun a => hcol _ _ fun i => ?_) (fun i j h1 h2 => ?_) hY` and prove the remaining obligations. Establish `hJ : (Formalism.REAL.Jm (parEps k r))ᴴ = Formalism.REAL.Jm (parEps k r)`. Rewrite using `[Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Apply the tactic sequence `simp only [Pi.star_apply]; split_ifs <;> simp`. Establish `hDh : Dᴴ = D`. Rewrite using `[hD, dMat, Matrix.diagonal_conjTranspose]`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Simplify using the standard rewrite rules. Establish `hDJ : D * Formalism.REAL.Jm (parEps k r) = Formalism.REAL.Jm (parEps k r) * D`. Rewrite using `[hD, dMat, Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hinv]`. Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose, Hpk_herm, hJ, hDh, Matrix.mul_assoc, Hpk_sq, Matrix.mul_one]`. Rewrite using `[← Matrix.mul_assoc D, hDJ, Matrix.mul_assoc]`.

Establish `ha` using `a.isLt`. Rewrite using `[hDP]`. Establish `e1 : col (eI k r a) = emb k (e a)` using `by simp [col, eI]`. Establish `e2 : col (nxt k r a) = emb k (fun s => -((s.val : ℝ) + 1) * e a s)`. Simplify using `only [hx]`.

Unfold `nxt`. Use `split_ifs with h`. Simplify using `[col, h]`. Simplify using `[col]`. Rewrite using `[e1]`.

Use `show _ = col (nxt k r a) i`. Rewrite using `[e2]`. Unfold `emb dNode`. Use `split_ifs with h1 h2 h2`. Use linear arithmetic over natural numbers and integers.

Simplify using the standard rewrite rules. Establish `: i.val + 1 - k = (i.val - k) + 1` using `by omega`. Rewrite using `[this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Rewrite using `[hDP]`. Establish `: col j = bvec ⟨j.val - r, by omega⟩` using `by simp [col, show ¬ j.val < r by omega, h2]`.

Rewrite using `[this]`. Distinguish the cases in `hc : c.val < k`. Simplify using `[dNode, hc]`. Establish `: c ≠ ⟨j.val - r, by omega⟩` using `fun h => hc (by rw [h]; simp only; omega)`. Simplify using `[bvec, this]`.
-/
theorem exists_frame (hk : 1 ≤ k) : ∃ P : Mat k r, Formalism.MainNotions.S.IsCayley k r (parEps k r) P ∧
    WCols k r P ∧ ∀ Y ∈ lieN (levF (levB k r)) (adjH (Hpk k r)),
      trace (dMat (dNode k r) * (P * Y * P⁻¹)) =
        ∑ a, (Y (eI k r a) (nxt k r a) - starRingEnd ℂ (Y (eI k r a) (nxt k r a))) := by
  obtain ⟨e, f, z, hee, hff, hfe, hez, hfz, hzz, hx⟩ :=
    frame r (fun s => -((s.val : ℝ) + 1)) (fun a b hab => by
      have : (a.val : ℝ) < b.val := by exact_mod_cast hab
      simp only; linarith)
  let col : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ := fun j =>
    if h : j.val < r then emb k (e ⟨j.val, h⟩)
    else if h2 : j.val < r + k then bvec ⟨j.val - r, by omega⟩
    else if h3 : j.val = r + k then emb k z else emb k (f ⟨2 * r + k - j.val, by omega⟩)
  let P : Mat k r := Matrix.of fun i j => col j i
  have hG : Pᴴ * Formalism.REAL.Jm (parEps k r) * P = Hpk k r := by
    ext i j
    have h0 : (Pᴴ * Formalism.REAL.Jm (parEps k r) * P) i j = formJ k r (col i) (col j) := by
      simp [Matrix.mul_apply, Formalism.REAL.Jm, Matrix.diagonal_apply, formJ, P]
    have hi := i.isLt
    have hj := j.isLt
    rw [h0, Hpk_apply]
    simp only [col, Fin.ext_iff, flipB_val, sgnB]
    split_ifs <;>
      first
      | omega
      | (rw [formJ_emb hk]
         simp only [hee, hff, hfe, hez, hfz, hzz, formV_symm (e _) (f _), formV_symm z (e _),
           formV_symm z (f _), Fin.ext_iff]
         first | (push_cast; rfl) | (split_ifs <;> first | omega | simp))
      | (rw [formJ_bvec_left _ (by simp only; omega), emb_lt _ _ (by simp only; omega)])
      | (rw [formJ_bvec_right _ (by simp only; omega), emb_lt _ _ (by simp only; omega), star_zero])
      | (rw [formJ_bvec_left _ (by simp only; omega)]
         simp only [bvec, Pi.single_apply, Fin.ext_iff]
         split_ifs <;> first | omega | rfl)
  have hL : (Hpk k r * Pᴴ * Formalism.REAL.Jm (parEps k r)) * P = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Pᴴ, hG, Hpk_sq]
  have hdet : IsUnit P.det := Matrix.isUnit_det_of_left_inverse hL
  have hinv : P⁻¹ = Hpk k r * Pᴴ * Formalism.REAL.Jm (parEps k r) := Matrix.inv_eq_left_inv hL
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hdet
  refine ⟨P, ⟨(Matrix.isUnit_iff_isUnit_det _).mpr hdet, hG⟩, fun j => ?_, fun Y hY => ?_⟩
  · have := j.isLt
    funext i
    simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, P, Matrix.of_apply, col, wI,
      Fin.val_castSucc, show ¬ (r + j.val < r) by omega, show r + j.val < r + k by omega,
      dif_pos, dif_neg, not_false_eq_true, Nat.add_sub_cancel_left]
  · set D := dMat (dNode k r) with hD
    have hDP : ∀ i j, (D * P) i j = (dNode k r i : ℂ) * col j i := fun i j => by
      simp [hD, dMat, Matrix.diagonal_mul, P]
    have hcol : ∀ j j' : Fin (2 * r + k + 1), (∀ i, (D * P) i j = P i j') →
        ∀ i, (P⁻¹ * (D * P)) i j = if i = j' then 1 else 0 := by
      intro j j' h i
      rw [← Matrix.one_apply, ← hPP, Matrix.mul_apply, Matrix.mul_apply]
      simp only [h]
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc D, ← Matrix.mul_assoc]
    refine trace_shift _ Y ?_ (fun a => hcol _ _ fun i => ?_) (fun i j h1 h2 => ?_) hY
    · have hJ : (Formalism.REAL.Jm (parEps k r))ᴴ = Formalism.REAL.Jm (parEps k r) := by
        rw [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]; congr 1; funext a
        simp only [Pi.star_apply]; split_ifs <;> simp
      have hDh : Dᴴ = D := by
        rw [hD, dMat, Matrix.diagonal_conjTranspose]; congr 1; funext a; simp
      have hDJ : D * Formalism.REAL.Jm (parEps k r) = Formalism.REAL.Jm (parEps k r) * D := by
        rw [hD, dMat, Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
        congr 1; funext a; ring
      rw [hinv]
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, Hpk_herm, hJ, hDh, Matrix.mul_assoc,
        Hpk_sq, Matrix.mul_one]
      rw [← Matrix.mul_assoc D, hDJ, Matrix.mul_assoc]
    · have ha := a.isLt
      rw [hDP]
      have e1 : col (eI k r a) = emb k (e a) := by simp [col, eI]
      have e2 : col (nxt k r a) = emb k (fun s => -((s.val : ℝ) + 1) * e a s) := by
        simp only [hx]
        unfold nxt
        split_ifs with h
        · simp [col, h]
        · simp [col]
      rw [e1]
      show _ = col (nxt k r a) i
      rw [e2]
      unfold emb dNode
      split_ifs with h1 h2 h2
      · omega
      · simp
      · have : i.val + 1 - k = (i.val - k) + 1 := by omega
        rw [this]; push_cast; ring
      · simp
    · rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [hDP]
      have : col j = bvec ⟨j.val - r, by omega⟩ := by simp [col, show ¬ j.val < r by omega, h2]
      rw [this]
      by_cases hc : c.val < k
      · simp [dNode, hc]
      · have : c ≠ ⟨j.val - r, by omega⟩ := fun h => hc (by rw [h]; simp only; omega)
        simp [bvec, this]

/- English proof (translation)
Take `⟨P, h1, h2, h3⟩` from `exists_frame (r := r) hk`. Rewrite using `[lieOf_Nset_eq]`. Use `⟨P, h1, h2, fun Y hY => by simp only [ellA_eq]; exact h3 Y hY, fun Y hY t => ?_⟩` and prove the remaining obligations. Rewrite using `[h3 Y hY, Formalism.MainNotions.S.psiGen]`. Apply the tactic sequence `simp only [ellA_eq, exp_entry Y (mem_lieN.mp hY).1, cBase, Complex.re_sum]`.

Use `congr 1`. Use `push_cast`. Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Apply the tactic sequence `apply Complex.ext <;> simp <;> ring`.
-/
theorem base_point_psi_exp_formula (hk : 1 ≤ k) : ∃ P : Mat k r, Formalism.MainNotions.S.IsCayley k r (parEps k r) P ∧ WCols k r P ∧
    (∀ Y ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r),
      trace (dMat (dNode k r) * (P * Y * P⁻¹)) =
        ∑ a, (Formalism.MainNotions.S.ellA k r (z0 k r) Y a - starRingEnd ℂ (Formalism.MainNotions.S.ellA k r (z0 k r) Y a))) ∧
    ∀ Y ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r), ∀ t : ℝ,
      Formalism.MainNotions.S.psiGen k r (z0 k r) (cBase r t) (NormedSpace.exp Y) =
        Complex.exp ((t : ℂ) * trace (dMat (dNode k r) * (P * Y * P⁻¹))) := by
  obtain ⟨P, h1, h2, h3⟩ := exists_frame (r := r) hk
  rw [lieOf_Nset_eq]
  refine ⟨P, h1, h2, fun Y hY => by simp only [ellA_eq]; exact h3 Y hY, fun Y hY t => ?_⟩
  rw [h3 Y hY, Formalism.MainNotions.S.psiGen]
  simp only [ellA_eq, exp_entry Y (mem_lieN.mp hY).1, cBase, Complex.re_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  apply Complex.ext <;> simp <;> ring

/- English proof (translation)
Introduce `_ _ hk` and use `base_point_psi_exp_formula hk`.
-/
theorem b1 : PairingPropertiesStatement := fun _ _ hk => base_point_psi_exp_formula hk

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
