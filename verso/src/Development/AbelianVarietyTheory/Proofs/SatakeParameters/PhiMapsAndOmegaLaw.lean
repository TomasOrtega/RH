import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsRowFrame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaCharSymMulInvEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.TwU

noncomputable section

namespace GlobalTheory.DatumLaw

open Loc LocE

section Comb

variable {κ : Type} [CommRing κ]

def dT (A : ℕ → ℕ → κ) (a : ℕ) : κ := Matrix.det (Matrix.of fun s s' : Fin a => A s.1 s'.1)

def dB (A : ℕ → ℕ → κ) (a t : ℕ) : κ := Matrix.det (Matrix.of fun s s' : Fin t => A (a + s.1) (a + s'.1))

/- English proof (translation)
Unfold `dB`. Rewrite using `[← Matrix.det_mul]`. Use `congr 1`. Use extensionality with `s s'`. Establish `hs` using `s.2`.

Establish `hs'` using `s'.2`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun l => A (a + s.1) (a + l) * B (a + l) (a + s'.1)) t, hC _ _ hs hs']`. Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le hn`.

Rewrite using `[Finset.sum_range_add, Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range a), Finset.sum_eq_zero (s := Finset.range m), zero_add, add_zero]`. Introduce `l hl`. Rewrite `hl` using `[Finset.mem_range]`. Rewrite using `[hB _ _ hs' (by omega) (by omega), mul_zero]`. Introduce `l hl`.

Rewrite `hl` using `[Finset.mem_range]`. Rewrite using `[hA _ _ hs hl, zero_mul]`.
-/
theorem dB_mul {n a t : ℕ} (hn : a + t ≤ n) {A B C : ℕ → ℕ → κ}
    (hA : ∀ u l, u < t → l < a → A (a + u) l = 0)
    (hB : ∀ u l, u < t → a + t ≤ l → l < n → B l (a + u) = 0)
    (hC : ∀ u u', u < t → u' < t → C (a + u) (a + u') = ∑ l ∈ Finset.range n, A (a + u) l * B l (a + u')) :
    dB C a t = dB A a t * dB B a t := by
  unfold dB
  rw [← Matrix.det_mul]
  congr 1
  ext s s'
  have hs := s.2
  have hs' := s'.2
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun l => A (a + s.1) (a + l) * B (a + l) (a + s'.1)) t, hC _ _ hs hs']
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Finset.sum_range_add, Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range a),
    Finset.sum_eq_zero (s := Finset.range m), zero_add, add_zero]
  · intro l hl
    rw [Finset.mem_range] at hl
    rw [hB _ _ hs' (by omega) (by omega), mul_zero]
  · intro l hl
    rw [Finset.mem_range] at hl
    rw [hA _ _ hs hl, zero_mul]

/- English proof (translation)
Unfold `dT dB`. Simplify using `only [zero_add]`.
-/
theorem dT_eq (A : ℕ → ℕ → κ) (a : ℕ) : dT A a = dB A 0 a := by
  unfold dT dB
  simp only [zero_add]

/- English proof (translation)
Rewrite using `[dT_eq, dT_eq, dT_eq]`. Use `dB_mul (n := n) (by omega) (fun _ _ _ h => absurd h (by omega)) ?_ ?_` and prove the remaining obligations. Simplify `hB` using `only [zero_add]`. Simplify `hC` using `only [zero_add]`.
-/
theorem dT_mul {n t : ℕ} (hn : t ≤ n) {A B C : ℕ → ℕ → κ}
    (hB : ∀ u l, u < t → t ≤ l → l < n → B l u = 0)
    (hC : ∀ u u', u < t → u' < t → C u u' = ∑ l ∈ Finset.range n, A u l * B l u') :
    dT C t = dT A t * dT B t := by
  rw [dT_eq, dT_eq, dT_eq]
  refine dB_mul (n := n) (by omega) (fun _ _ _ h => absurd h (by omega)) ?_ ?_
  · simpa only [zero_add] using hB
  · simpa only [zero_add] using hC

/- English proof (translation)
Unfold `dT dB`. Rewrite using `[← Matrix.det_fromBlocks_zero₂₁ _ (Matrix.of fun (s : Fin a) (s' : Fin t) => A s.1 (a + s'.1)), ← Matrix.det_submatrix_equiv_self finSumFinEquiv]`. Use `congr 1`. Use extensionality with `(s | s) (s' | s')`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Simplify using `using hA _ _ s.2 s'.2`. Simplify using the standard rewrite rules.
-/
theorem dT_split {a t : ℕ} {A : ℕ → ℕ → κ} (hA : ∀ u l, u < t → l < a → A (a + u) l = 0) :
    dT A (a + t) = dT A a * dB A a t := by
  unfold dT dB
  rw [← Matrix.det_fromBlocks_zero₂₁ _ (Matrix.of fun (s : Fin a) (s' : Fin t) => A s.1 (a + s'.1)),
    ← Matrix.det_submatrix_equiv_self finSumFinEquiv]
  congr 1
  ext (s | s) (s' | s')
  · simp
  · simp
  · simpa using hA _ _ s.2 s'.2
  · simp

def Zs (k rS r p p' : ℕ) : Prop := r ≤ p ∨ symIdx k rS p' < symIdx k rS p ∨ (p' = k + rS ∧ p < k)

def Pat (k rS r t a : ℕ) (A : ℕ → ℕ → κ) : Prop :=
  (∀ p', p' < r → A p' p' = 1 ∧ ∀ p, p < a → p ≠ p' → Zs k rS r p p' → A p p' = 0) ∧
    (∀ p p', r ≤ p' → p' < a → p < a → (p' - r) / t < (p - r) / t → A p p' = 0)

/- English proof (translation)
Establish `e1` using `SymLevelInv.symIdx_cases k rS p`. Establish `e2` using `SymLevelInv.symIdx_cases k rS s`. Establish `e3` using `SymLevelInv.symIdx_cases k rS p'`. Unfold `Zs at *`. Apply the tactic sequence `constructor <;> omega`.
-/
theorem zs_trans {k rS r p s p' : ℕ} (hr : k + rS ≤ r) (h1 : s ≠ p') (h2 : ¬ Zs k rS r s p') (h3 : p ≠ s)
    (h4 : ¬ Zs k rS r p s) : p ≠ p' ∧ ¬ Zs k rS r p p' := by
  have e1 := SymLevelInv.symIdx_cases k rS p
  have e2 := SymLevelInv.symIdx_cases k rS s
  have e3 := SymLevelInv.symIdx_cases k rS p'
  unfold Zs at *
  constructor <;> omega

/- English proof (translation)
Establish `e1` using `SymLevelInv.symIdx_cases k rS p`. Establish `e2` using `SymLevelInv.symIdx_cases k rS s`. Establish `e3` using `SymLevelInv.symIdx_cases k rS (p + 1)`. Unfold `Zs at *`. Use linear arithmetic over natural numbers and integers.
-/
theorem zs_adj {k rS r p s : ℕ} (hp : p + 1 ≠ k) (h1 : s ≠ p + 1) (h2 : ¬ Zs k rS r s (p + 1)) (h3 : p ≠ s) :
    Zs k rS r p s := by
  have e1 := SymLevelInv.symIdx_cases k rS p
  have e2 := SymLevelInv.symIdx_cases k rS s
  have e3 := SymLevelInv.symIdx_cases k rS (p + 1)
  unfold Zs at *
  omega

variable {k rS r t a : ℕ} {A B C : ℕ → ℕ → κ}

/- English proof (translation)
Distinguish the cases in `hz : Zs k rS r s p'`. Rewrite using `[(hB.1 p' hp').2 s hs h1 hz, mul_zero]`. Establish `hsr : s < r`. Assume the negation of the conclusion as `hh`. Conclude with `hz (Or.inl (by omega))`.

Rewrite using `[(hA.1 s hsr).2 p hp (h hz).1 (h hz).2, zero_mul]`.
-/
theorem Pat.term (hA : Pat k rS r t a A) (hB : Pat k rS r t a B) {p s p' : ℕ} (hp : p < a) (hs : s < a) (hp' : p' < r)
    (h1 : s ≠ p') (h : ¬ Zs k rS r s p' → p ≠ s ∧ Zs k rS r p s) : A p s * B s p' = 0 := by
  by_cases hz : Zs k rS r s p'
  · rw [(hB.1 p' hp').2 s hs h1 hz, mul_zero]
  · have hsr : s < r := by
      by_contra hh
      exact hz (Or.inl (by omega))
    rw [(hA.1 s hsr).2 p hp (h hz).1 (h hz).2, zero_mul]

/- English proof (translation)
Use `⟨fun p' hp' => ⟨?_, fun p hp hne hz => ?_⟩, fun p p' h1 h2 h3 h4 => ?_⟩` and prove the remaining obligations. Rewrite using `[hC _ _ (by omega) (by omega), Finset.sum_eq_single p', (hA.1 p' hp').1, (hB.1 p' hp').1, one_mul]`. Introduce `s hs hne`. Use `hA.term hB (by omega) (Finset.mem_range.1 hs) hp' hne fun hz => ⟨hne.symm, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h4`.

Conclude with `(zs_trans hr hne hz hne.symm h4).1 rfl`. Introduce `h`. Conclude with `absurd (Finset.mem_range.2 (by omega)) h`. Rewrite using `[hC _ _ hp (by omega)]`. Use `Finset.sum_eq_zero fun s hs => ?_` and prove the remaining obligations.

Distinguish the cases in `h1 : s = p'`. Rewrite using `[h1, (hA.1 p' hp').2 p hp hne hz, zero_mul]`. Use `hA.term hB hp (Finset.mem_range.1 hs) hp' h1 fun hz' => ?_` and prove the remaining obligations. Establish `h3 : p ≠ s` using `fun h => hz' (h ▸ hz)`. Use `⟨h3, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `h4`. Conclude with `(zs_trans hr h1 hz' h3 h4).2 hz`. Rewrite using `[hC _ _ h3 h2]`. Establish `hpr : r ≤ p`. Assume the negation of the conclusion as `hh`.

Rewrite `h4` using `[show p - r = 0 by omega, Nat.zero_div]`. Conclude with `absurd h4 (Nat.not_lt_zero _)`. Use `Finset.sum_eq_zero fun s hs => ?_` and prove the remaining obligations. Rewrite `hs` using `[Finset.mem_range]`. Distinguish the cases in `hsr : s < r`.

Rewrite using `[(hA.1 s hsr).2 p h3 (by omega) (Or.inl hpr), zero_mul]`. Distinguish the cases in `h5 : (s - r) / t < (p - r) / t`. Rewrite using `[hA.2 p s (by omega) hs h3 h5, zero_mul]`. Rewrite using `[hB.2 s p' h1 h2 hs (by omega), mul_zero]`.
-/
theorem Pat.mul (hr : k + rS ≤ r) (ha : r ≤ a) (hA : Pat k rS r t a A) (hB : Pat k rS r t a B)
    (hC : ∀ p p', p < a → p' < a → C p p' = ∑ l ∈ Finset.range a, A p l * B l p') : Pat k rS r t a C := by
  refine ⟨fun p' hp' => ⟨?_, fun p hp hne hz => ?_⟩, fun p p' h1 h2 h3 h4 => ?_⟩
  · rw [hC _ _ (by omega) (by omega), Finset.sum_eq_single p', (hA.1 p' hp').1, (hB.1 p' hp').1, one_mul]
    · intro s hs hne
      refine hA.term hB (by omega) (Finset.mem_range.1 hs) hp' hne fun hz => ⟨hne.symm, ?_⟩
      by_contra h4
      exact (zs_trans hr hne hz hne.symm h4).1 rfl
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  · rw [hC _ _ hp (by omega)]
    refine Finset.sum_eq_zero fun s hs => ?_
    by_cases h1 : s = p'
    · rw [h1, (hA.1 p' hp').2 p hp hne hz, zero_mul]
    · refine hA.term hB hp (Finset.mem_range.1 hs) hp' h1 fun hz' => ?_
      have h3 : p ≠ s := fun h => hz' (h ▸ hz)
      refine ⟨h3, ?_⟩
      by_contra h4
      exact (zs_trans hr h1 hz' h3 h4).2 hz
  · rw [hC _ _ h3 h2]
    have hpr : r ≤ p := by
      by_contra hh
      rw [show p - r = 0 by omega, Nat.zero_div] at h4
      exact absurd h4 (Nat.not_lt_zero _)
    refine Finset.sum_eq_zero fun s hs => ?_
    rw [Finset.mem_range] at hs
    by_cases hsr : s < r
    · rw [(hA.1 s hsr).2 p h3 (by omega) (Or.inl hpr), zero_mul]
    · by_cases h5 : (s - r) / t < (p - r) / t
      · rw [hA.2 p s (by omega) hs h3 h5, zero_mul]
      · rw [hB.2 s p' h1 h2 hs (by omega), mul_zero]

/- English proof (translation)
Rewrite using `[hC _ _ (by omega) (by omega), Finset.sum_eq_add_of_mem p (p + 1) (by simp; omega) (by simp; omega) (by omega), (hA.1 p (by omega)).1, (hB.1 (p + 1) hp).1, one_mul, mul_one, add_comm]`. Introduce and unpack `s hs ⟨h1, h2⟩`. Conclude with `hA.term hB (by omega) (Finset.mem_range.1 hs) hp h2 fun hz => ⟨h1.symm, zs_adj hk h2 hz h1.symm⟩`.
-/
theorem Pat.superdiag (ha : r ≤ a) (hA : Pat k rS r t a A) (hB : Pat k rS r t a B)
    (hC : ∀ p p', p < a → p' < a → C p p' = ∑ l ∈ Finset.range a, A p l * B l p') {p : ℕ} (hp : p + 1 < r)
    (hk : p + 1 ≠ k) : C p (p + 1) = A p (p + 1) + B p (p + 1) := by
  rw [hC _ _ (by omega) (by omega), Finset.sum_eq_add_of_mem p (p + 1) (by simp; omega) (by simp; omega) (by omega),
    (hA.1 p (by omega)).1, (hB.1 (p + 1) hp).1, one_mul, mul_one, add_comm]
  rintro s hs ⟨h1, h2⟩
  exact hA.term hB (by omega) (Finset.mem_range.1 hs) hp h2 fun hz => ⟨h1.symm, zs_adj hk h2 hz h1.symm⟩

/- English proof (translation)
Establish `hd : ∀ u, u < t → (r + i * t + u - r) / t = i` using `fun u hu => by`. Rewrite using `[show r + i * t + u - r = u + i * t by omega, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hu, zero_add]`. Use `dB_mul hi (fun u l hu hl => ?_) (fun u l hu h1 h2 => ?_) fun u u' hu hu' => hC _ _ (by omega) (by omega)` and prove the remaining obligations. Distinguish the cases in `hlr : l < r`. Conclude with `(hA.1 l hlr).2 _ (by omega) (by omega) (Or.inl (by omega))`.

Use `hA.2 _ _ (by omega) (by omega) (by omega) ?_` and prove the remaining obligations. Rewrite using `[hd u hu, Nat.div_lt_iff_lt_mul (by omega)]`. Use linear arithmetic over natural numbers and integers. Use `hB.2 _ _ (by omega) (by omega) h2 ?_` and prove the remaining obligations. Rewrite using `[hd u hu, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by omega), add_mul]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem Pat.block (hA : Pat k rS r t a A) (hB : Pat k rS r t a B)
    (hC : ∀ p p', p < a → p' < a → C p p' = ∑ l ∈ Finset.range a, A p l * B l p') {i : ℕ} (hi : r + i * t + t ≤ a) :
    dB C (r + i * t) t = dB A (r + i * t) t * dB B (r + i * t) t := by
  have hd : ∀ u, u < t → (r + i * t + u - r) / t = i := fun u hu => by
    rw [show r + i * t + u - r = u + i * t by omega, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hu, zero_add]
  refine dB_mul hi (fun u l hu hl => ?_) (fun u l hu h1 h2 => ?_) fun u u' hu hu' => hC _ _ (by omega) (by omega)
  · by_cases hlr : l < r
    · exact (hA.1 l hlr).2 _ (by omega) (by omega) (Or.inl (by omega))
    · refine hA.2 _ _ (by omega) (by omega) (by omega) ?_
      rw [hd u hu, Nat.div_lt_iff_lt_mul (by omega)]
      omega
  · refine hB.2 _ _ (by omega) (by omega) h2 ?_
    rw [hd u hu, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by omega), add_mul]
    omega

variable {K : Type} [Field K]

open Classical in

def ext0 (χ : κˣ →* Kˣ) (a : κ) : K := if h : IsUnit a then ((χ h.unit : Kˣ) : K) else 0

/- English proof (translation)
Unfold `ext0`. Distinguish the cases in `ha : IsUnit a`. Distinguish the cases in `hb : IsUnit b`. Rewrite using `[dif_pos ha, dif_pos hb, dif_pos (ha.mul hb), ← Units.val_mul, ← map_mul]`. Use `congr 2`.

Conclude with `Units.ext (by simp)`. Rewrite using `[dif_neg hb, dif_neg fun h => hb (isUnit_of_mul_isUnit_right h), mul_zero]`. Rewrite using `[dif_neg ha, dif_neg fun h => ha (isUnit_of_mul_isUnit_left h), zero_mul]`.
-/
theorem matrixExtendByZero_mul (χ : κˣ →* Kˣ) (a b : κ) : ext0 χ (a * b) = ext0 χ a * ext0 χ b := by
  unfold ext0
  by_cases ha : IsUnit a
  · by_cases hb : IsUnit b
    · rw [dif_pos ha, dif_pos hb, dif_pos (ha.mul hb), ← Units.val_mul, ← map_mul]
      congr 2
      exact Units.ext (by simp)
    · rw [dif_neg hb, dif_neg fun h => hb (isUnit_of_mul_isUnit_right h), mul_zero]
  · rw [dif_neg ha, dif_neg fun h => ha (isUnit_of_mul_isUnit_left h), zero_mul]

/- English proof (translation)
Unfold `ext0`. Rewrite using `[dif_pos h]`. Conclude with `Units.ne_zero _`.
-/
theorem unitCharacterExtendByZero_ne_zero_of_isUnit (χ : κˣ →* Kˣ) {a : κ} (h : IsUnit a) : ext0 χ a ≠ 0 := by
  unfold ext0
  rw [dif_pos h]
  exact Units.ne_zero _

/- English proof (translation)
Unfold `ext0`. Use `split_ifs`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem extendByZeroOffSubset_mul_left_of_mem_lattice (χ : κˣ →* Kˣ) (a : κ) : ext0 χ⁻¹ a = (ext0 χ a)⁻¹ := by
  unfold ext0
  split_ifs
  · simp
  · simp

def lamF (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (k r t j : ℕ) (A : ℕ → ℕ → κ) : K :=
  ψ (∑ i ∈ Finset.range (k - 1), A i (i + 1) + ∑ i ∈ Finset.range (r - k - 1), A (k + i) (k + i + 1)) *
    ∏ i ∈ Finset.range j, ext0 (χ i) (dB A (r + i * t) t)

/- English proof (translation)
Unfold `lamF`. Rewrite using `[Finset.prod_range_succ, mul_assoc]`.
-/
theorem lamF_succ (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (j : ℕ) (A : ℕ → ℕ → κ) :
    lamF ψ χ k r t (j + 1) A = lamF ψ χ k r t j A * ext0 (χ j) (dB A (r + j * t) t) := by
  unfold lamF
  rw [Finset.prod_range_succ, mul_assoc]

/- English proof (translation)
Establish `: (i + 1) * t ≤ j * t` using `Nat.mul_le_mul_right t hi`. Rewrite `this` using `[add_mul, one_mul]`. Use linear arithmetic over natural numbers and integers.
-/
theorem blk_le {r i j t a : ℕ} (hi : i < j) (h : r + j * t ≤ a) : r + i * t + t ≤ a := by
  have : (i + 1) * t ≤ j * t := Nat.mul_le_mul_right t hi
  rw [add_mul, one_mul] at this
  omega

/- English proof (translation)
Establish `hra : r ≤ a` using `le_trans (Nat.le_add_right _ _) ha`. Unfold `lamF`. Rewrite using `[mul_mul_mul_comm, ← AddChar.map_add_eq_mul, ← Finset.prod_mul_distrib, add_add_add_comm, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Use `congr 1`. Use `congr 2`.

Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite `hi` using `[Finset.mem_range]`. Conclude with `hA.superdiag hra hB hC (by omega) (by omega)`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite `hi` using `[Finset.mem_range]`.

Conclude with `hA.superdiag hra hB hC (by omega) (by omega)`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[hA.block hB hC (blk_le (Finset.mem_range.1 hi) ha), matrixExtendByZero_mul]`.
-/
theorem Pat.lamF_mul (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (hk : k ≤ r) {j : ℕ} (ha : r + j * t ≤ a)
    (hA : Pat k rS r t a A) (hB : Pat k rS r t a B)
    (hC : ∀ p p', p < a → p' < a → C p p' = ∑ l ∈ Finset.range a, A p l * B l p') :
    lamF ψ χ k r t j C = lamF ψ χ k r t j A * lamF ψ χ k r t j B := by
  have hra : r ≤ a := le_trans (Nat.le_add_right _ _) ha
  unfold lamF
  rw [mul_mul_mul_comm, ← AddChar.map_add_eq_mul, ← Finset.prod_mul_distrib, add_add_add_comm,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  · congr 2
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      exact hA.superdiag hra hB hC (by omega) (by omega)
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      exact hA.superdiag hra hB hC (by omega) (by omega)
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [hA.block hB hC (blk_le (Finset.mem_range.1 hi) ha), matrixExtendByZero_mul]

end Comb

section Mat

variable {E K : Type} [Field E] [NumberField E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

/- English proof (translation)
Rewrite using `[Nat.cast_ne_zero]`. Conclude with `fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)`.
-/
theorem q_ne : (qOf P : E) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  exact fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)

/- English proof (translation)
Use `SymLevelInv.of_inv_mul P (q := qOf P) (Nat.cast_ne_zero.1 (q_ne (E := E) (P := P))) (Ideal.absNorm_mem P.asIdeal) ?_` and prove the remaining obligations. Rewrite using `[mul_comm, ← div_eq_mul_inv]` and apply the resulting hypothesis.
-/
theorem of_div {a : E} (h : IntAt P (a / (qOf P : E))) : IntAt P a ∧ redP P a = 0 := by
  refine SymLevelInv.of_inv_mul P (q := qOf P) (Nat.cast_ne_zero.1 (q_ne (E := E) (P := P)))
    (Ideal.absNorm_mem P.asIdeal) ?_
  rwa [mul_comm, ← div_eq_mul_inv]

variable (P) in

def red (M : ℕ → ℕ → E) : ℕ → ℕ → 𝓞 E ⧸ P.asIdeal := fun p p' => redP P (M p p')

variable (P) in

def IntM (b a : ℕ) (M : ℕ → ℕ → E) : Prop := ∀ p p', p < b → p' < a → IntAt P (M p p')

def IsMul (n : ℕ) (A B C : ℕ → ℕ → E) : Prop := ∀ p p', C p p' = ∑ l ∈ Finset.range n, A p l * B l p'

variable {a b n : ℕ} {A B C : ℕ → ℕ → E}

/- English proof (translation)
Introduce `p p' hp hp'` and use `by rw [h] exact SymLevelInv.intAt_sum P _ _ fun l hl => (hA p l hp (Finset.mem_range.1 hl)).mul (hB l p' (Finset.mem_range.1 hl) hp')`.
-/
theorem IsMul.int (h : IsMul n A B C) (hA : IntM P b n A) (hB : IntM P n a B) : IntM P b a C := fun p p' hp hp' => by
  rw [h]
  exact SymLevelInv.intAt_sum P _ _ fun l hl =>
    (hA p l hp (Finset.mem_range.1 hl)).mul (hB l p' (Finset.mem_range.1 hl) hp')

/- English proof (translation)
Unfold `DatumLaw.red`. Rewrite using `[h, SymLevelInv.reduction_sum₂ P _ _ fun l hl => (hA p l hp (Finset.mem_range.1 hl)).mul (hB l p' (Finset.mem_range.1 hl) hp')]`. Conclude with `Finset.sum_congr rfl fun l hl => reduction_mul (hA p l hp (Finset.mem_range.1 hl)) (hB l p' (Finset.mem_range.1 hl) hp')`.
-/
theorem IsMul.red (h : IsMul n A B C) (hA : IntM P b n A) (hB : IntM P n a B) {p p' : ℕ} (hp : p < b) (hp' : p' < a) :
    red P C p p' = ∑ l ∈ Finset.range n, red P A p l * red P B l p' := by
  unfold DatumLaw.red
  rw [h, SymLevelInv.reduction_sum₂ P _ _ fun l hl =>
    (hA p l hp (Finset.mem_range.1 hl)).mul (hB l p' (Finset.mem_range.1 hl) hp')]
  exact Finset.sum_congr rfl fun l hl =>
    reduction_mul (hA p l hp (Finset.mem_range.1 hl)) (hB l p' (Finset.mem_range.1 hl) hp')

/- English proof (translation)
Rewrite using `[h, Finset.sum_div]`. Use `SymLevelInv.intAt_sum P _ _ fun l hl => ?_` and prove the remaining obligations. Rewrite `hl` using `[Finset.mem_range]`. Break down `hd l hl with h1 | h1` into its components or cases. Rewrite using `[← div_mul_eq_mul_div]`.

Conclude with `h1.mul (hB l p' hl hp')`. Rewrite using `[mul_div_assoc]`. Conclude with `(hA p l hp hl).mul h1`.
-/
theorem IsMul.div (h : IsMul n A B C) (hA : IntM P b n A) (hB : IntM P n a B) {p p' : ℕ} (hp : p < b) (hp' : p' < a)
    (hd : ∀ l, l < n → IntAt P (A p l / (qOf P : E)) ∨ IntAt P (B l p' / (qOf P : E))) :
    IntAt P (C p p' / (qOf P : E)) := by
  rw [h, Finset.sum_div]
  refine SymLevelInv.intAt_sum P _ _ fun l hl => ?_
  rw [Finset.mem_range] at hl
  rcases hd l hl with h1 | h1
  · rw [← div_mul_eq_mul_div]
    exact h1.mul (hB l p' hl hp')
  · rw [mul_div_assoc]
    exact (hA p l hp hl).mul h1

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem unitV_eq (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (x : E) : unitV χ x = ext0 χ (redP P x) := rfl

/- English proof (translation)
The claim follows from `SymLevelInv.reduction_det P _ fun u u' => hA _ _ (by have := u.2; omega) (by have := u'.2; omega)`.
-/
theorem redP_dB {s t : ℕ} (hA : IntM P b a A) (h1 : s + t ≤ b) (h2 : s + t ≤ a) : redP P (dB A s t) = dB (red P A) s t :=
  SymLevelInv.reduction_det P _ fun u u' => hA _ _ (by have := u.2; omega) (by have := u'.2; omega)

/- English proof (translation)
The claim follows from `SymLevelInv.reduction_det P _ fun u u' => hA _ _ (by have := u.2; omega) (by have := u'.2; omega)`.
-/
theorem reduction_leadingMinor {t : ℕ} (hA : IntM P b a A) (h1 : t ≤ b) (h2 : t ≤ a) : redP P (dT A t) = dT (red P A) t :=
  SymLevelInv.reduction_det P _ fun u u' => hA _ _ (by have := u.2; omega) (by have := u'.2; omega)

variable (P) in

def SuppQ (r b a : ℕ) (M : ℕ → ℕ → E) : Prop :=
  IntM P b a M ∧ ∀ p p', r ≤ p → p < b → p' < r → IntAt P (M p p' / (qOf P : E))

/- English proof (translation)
Use `⟨⟨h.int hA.1 hB.1, fun p p' h1 h2 h3 => h.div hA.1 hB.1 h2 (by omega) fun l hl => ?_⟩, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hlr : l < r`. Conclude with `Or.inl (hA.2 p l h1 h2 hlr)`. Conclude with `Or.inr (hB.2 l p' (by omega) hl h3)`. Conclude with `dT_mul hn (fun u l hu h1 h2 => (of_div (hB.2 l u h1 h2 hu)).2) fun u u' hu hu' => h.red hA.1 hB.1 (by omega) (by omega)`.
-/
theorem SuppQ.mul {r : ℕ} (h : IsMul n A B C) (hb : r ≤ b) (hn : r ≤ n) (ha : r ≤ a) (hA : SuppQ P r b n A)
    (hB : SuppQ P r n a B) : SuppQ P r b a C ∧ dT (red P C) r = dT (red P A) r * dT (red P B) r := by
  refine ⟨⟨h.int hA.1 hB.1, fun p p' h1 h2 h3 => h.div hA.1 hB.1 h2 (by omega) fun l hl => ?_⟩, ?_⟩
  · by_cases hlr : l < r
    · exact Or.inl (hA.2 p l h1 h2 hlr)
    · exact Or.inr (hB.2 l p' (by omega) hl h3)
  · exact dT_mul hn (fun u l hu h1 h2 => (of_div (hB.2 l u h1 h2 hu)).2)
      fun u u' hu hu' => h.red hA.1 hB.1 (by omega) (by omega)

/- English proof (translation)
Rewrite using `[reduction_leadingMinor hA.1 le_rfl le_rfl]`. Conclude with `dT_split fun u l hu hl => (of_div (hA.2 _ _ (by omega) (by omega) hl)).2`.
-/
theorem SuppQ.det {r t : ℕ} (hA : SuppQ P r (r + t) (r + t) A) :
    redP P (dT A (r + t)) = dT (red P A) r * dB (red P A) r t := by
  rw [reduction_leadingMinor hA.1 le_rfl le_rfl]
  exact dT_split fun u l hu hl => (of_div (hA.2 _ _ (by omega) (by omega) hl)).2

variable (P) in

def SuppG (k rS r t b a : ℕ) (M : ℕ → ℕ → E) : Prop :=
  IntM P b a M ∧ (∀ p p', a ≤ p → p < b → p' < a → IntAt P (M p p' / (qOf P : E))) ∧ Pat k rS r t a (red P M)

variable (P) in

def LevG (k rS r t n : ℕ) (M : ℕ → ℕ → E) : Prop :=
  IntM P n n M ∧
    (∀ p', p' < r → redP P (M p' p') = 1 ∧ ∀ p, p < n → p ≠ p' → Zs k rS r p p' → redP P (M p p') = 0) ∧
    ∀ i p p', r + i * t ≤ p → p < n → p' < r + i * t → IntAt P (M p p' / (qOf P : E))

variable {k rS r t : ℕ}

/- English proof (translation)
Use `⟨fun p' hp' => ⟨(h.2.1 p' hp').1, fun p hp => (h.2.1 p' hp').2 p (by omega)⟩, fun p p' h1 h2 h3 h4 => ?_⟩` and prove the remaining obligations. Establish `ht : 0 < t`. Break down `Nat.eq_zero_or_pos t with rfl | ht` into its components or cases. Simplify using `at h4`. Conclude with `ht`.

Establish `hpr : r ≤ p`. Assume the negation of the conclusion as `hh`. Rewrite `h4` using `[show p - r = 0 by omega, Nat.zero_div]`. Conclude with `absurd h4 (Nat.not_lt_zero _)`. Establish `h5` using `Nat.div_mul_le_self (p - r) t`.

Rewrite `h4` using `[Nat.div_lt_iff_lt_mul ht]`. Conclude with `(of_div (h.2.2 ((p - r) / t) p p' (by omega) (by omega) (by omega))).2`.
-/
theorem LevG.pat (h : LevG P k rS r t n A) (ha : a ≤ n) : Pat k rS r t a (red P A) := by
  refine ⟨fun p' hp' => ⟨(h.2.1 p' hp').1, fun p hp => (h.2.1 p' hp').2 p (by omega)⟩, fun p p' h1 h2 h3 h4 => ?_⟩
  have ht : 0 < t := by
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp at h4
    · exact ht
  have hpr : r ≤ p := by
    by_contra hh
    rw [show p - r = 0 by omega, Nat.zero_div] at h4
    exact absurd h4 (Nat.not_lt_zero _)
  have h5 := Nat.div_mul_le_self (p - r) t
  rw [Nat.div_lt_iff_lt_mul ht] at h4
  exact (of_div (h.2.2 ((p - r) / t) p p' (by omega) (by omega) (by omega))).2

variable (ψ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)

/- English proof (translation)
Establish `i1 : ∀ i ∈ Finset.range (k - 1), IntAt P (A i (i + 1))` using `fun i hi => by`. Rewrite `hi` using `[Finset.mem_range]`. Conclude with `hA _ _ (by omega) (by omega)`. Establish `i2 : ∀ i ∈ Finset.range (r - k - 1), IntAt P (A (k + i) (k + i + 1))` using `fun i hi => by`. Rewrite `hi` using `[Finset.mem_range]`.

Conclude with `hA _ _ (by omega) (by omega)`. Unfold `lamGvS lamF`. Rewrite using `[reduction_add (SymLevelInv.intAt_sum P _ _ i1) (SymLevelInv.intAt_sum P _ _ i2), SymLevelInv.reduction_sum₂ P _ _ i1, SymLevelInv.reduction_sum₂ P _ _ i2]`. Use `congr 1`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations.

Rewrite `hi` using `[Finset.mem_range]`. Rewrite using `[unitV_eq, ← redP_dB hA (blk_le hi hb) (blk_le hi ha)]`. Both sides reduce to the same expression.
-/
theorem lamGvS_eq {j : ℕ} (hk : k ≤ r) (hA : IntM P b a A) (hb : r + j * t ≤ b) (ha : r + j * t ≤ a) :
    lamGvS ψ χ k r t j A = lamF ψ χ k r t j (red P A) := by
  have i1 : ∀ i ∈ Finset.range (k - 1), IntAt P (A i (i + 1)) := fun i hi => by
    rw [Finset.mem_range] at hi
    exact hA _ _ (by omega) (by omega)
  have i2 : ∀ i ∈ Finset.range (r - k - 1), IntAt P (A (k + i) (k + i + 1)) := fun i hi => by
    rw [Finset.mem_range] at hi
    exact hA _ _ (by omega) (by omega)
  unfold lamGvS lamF
  rw [reduction_add (SymLevelInv.intAt_sum P _ _ i1) (SymLevelInv.intAt_sum P _ _ i2), SymLevelInv.reduction_sum₂ P _ _ i1,
    SymLevelInv.reduction_sum₂ P _ _ i2]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [unitV_eq, ← redP_dB hA (blk_le hi hb) (blk_le hi ha)]
  rfl

def valG (k r t i : ℕ) (M : ℕ → ℕ → E) : K := lamGvS ψ χ k r t i M * (unitV (χ i) (dT M (r + i * t)))⁻¹

/- English proof (translation)
Establish `hC` using `h.int hA.1 hB.1`. Establish `hm : ∀ p p', p < r + i * t → p' < r + i * t → red P C p p' = ∑ l ∈ Finset.range (r + i * t), red P A p l * red P B l p'` using `fun p p' hp hp' => h.red hA.1 hB.1 (by omega) hp'`. Use `⟨⟨hC, fun p p' h1 h2 h3 => h.div hA.1 hB.1 h2 h3 fun l hl => Or.inl (hA.2.1 p l h1 h2 hl), hA.2.2.mul hr (Nat.le_add_right _ _) (hB.pat le_rfl) hm⟩, ?_⟩` and prove the remaining obligations. Establish `hne` using `unitCharacterExtendByZero_ne_zero_of_isUnit (χ i) hu`. Unfold `valG`.

Simplify using `only [unitV_eq]`. Rewrite using `[lamGvS_eq ψ χ (by omega) hC hb le_rfl, lamGvS_eq ψ χ (by omega) hA.1 hb le_rfl, lamGvS_eq ψ χ (by omega) hB.1 le_rfl le_rfl, hA.2.2.lamF_mul ψ χ (by omega) le_rfl (hB.pat le_rfl) hm, reduction_leadingMinor hC hb le_rfl, dT_mul le_rfl (fun _ _ _ _ _ => by omega) hm, matrixExtendB …`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem SuppG.source {i : ℕ} (hr : k + rS ≤ r) (hb : r + i * t ≤ b) (h : IsMul (r + i * t) A B C)
    (hA : SuppG P k rS r t b (r + i * t) A) (hB : LevG P k rS r t (r + i * t) B) (hu : IsUnit (redP P (dT B (r + i * t)))) :
    SuppG P k rS r t b (r + i * t) C ∧
      valG ψ χ k r t i C * unitV (χ i) (dT B (r + i * t)) = lamGvS ψ χ k r t i B * valG ψ χ k r t i A := by
  have hC := h.int hA.1 hB.1
  have hm : ∀ p p', p < r + i * t → p' < r + i * t →
      red P C p p' = ∑ l ∈ Finset.range (r + i * t), red P A p l * red P B l p' :=
    fun p p' hp hp' => h.red hA.1 hB.1 (by omega) hp'
  refine ⟨⟨hC, fun p p' h1 h2 h3 => h.div hA.1 hB.1 h2 h3 fun l hl => Or.inl (hA.2.1 p l h1 h2 hl),
    hA.2.2.mul hr (Nat.le_add_right _ _) (hB.pat le_rfl) hm⟩, ?_⟩
  have hne := unitCharacterExtendByZero_ne_zero_of_isUnit (χ i) hu
  unfold valG
  simp only [unitV_eq]
  rw [lamGvS_eq ψ χ (by omega) hC hb le_rfl, lamGvS_eq ψ χ (by omega) hA.1 hb le_rfl,
    lamGvS_eq ψ χ (by omega) hB.1 le_rfl le_rfl, hA.2.2.lamF_mul ψ χ (by omega) le_rfl (hB.pat le_rfl) hm,
    reduction_leadingMinor hC hb le_rfl, dT_mul le_rfl (fun _ _ _ _ _ => by omega) hm, matrixExtendByZero_mul, ← reduction_leadingMinor hB.1 le_rfl le_rfl,
    ← reduction_leadingMinor hA.1 hb le_rfl, mul_inv, mul_assoc, mul_assoc _ _ (ext0 _ _), inv_mul_cancel₀ hne]
  ring

/- English proof (translation)
Establish `hC` using `h.int hB.1 hA.1`. Establish `hb : r + i * t ≤ r + i * t + t` using `Nat.le_add_right _ _`. Establish `hm : ∀ p p', p < r + i * t → p' < r + i * t → red P C p p' = ∑ l ∈ Finset.range (r + i * t), red P B p l * red P A l p'` using `fun p p' hp hp' => by`. Rewrite using `[h.red hB.1 hA.1 (by omega) hp', Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range t), add_zero]`. Introduce `l hl`.

Rewrite `hl` using `[Finset.mem_range]`. Rewrite using `[show red P A (r + i * t + l) p' = 0 from (of_div (hA.2.1 _ _ (by omega) (by omega) hp')).2, mul_zero]`. Use `⟨⟨hC, fun p p' h1 h2 h3 => h.div hB.1 hA.1 h2 h3 fun l hl => ?_, (hB.pat hb).mul hr (Nat.le_add_right _ _) hA.2.2 hm⟩, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hl' : l < r + i * t`. Conclude with `Or.inl (hB.2.2 i p l h1 h2 hl')`.

Conclude with `Or.inr (hA.2.1 l p' (by omega) hl h3)`. Establish `hs : redP P (dT B (r + i * t + t)) = dT (red P B) (r + i * t) * dB (red P B) (r + i * t) t`. Rewrite using `[reduction_leadingMinor hB.1 le_rfl le_rfl]`. Conclude with `dT_split fun u l hu hl => (of_div (hB.2.2 i _ _ (by omega) (by omega) hl)).2`. Rewrite `hu` using `[hs]`.

Establish `hne` using `unitCharacterExtendByZero_ne_zero_of_isUnit (χ i) (isUnit_of_mul_isUnit_left hu)`. Establish `hb' : r + (i + 1) * t ≤ r + i * t + t` using `by rw [add_mul, one_mul, add_assoc]`. Unfold `valG`. Simplify using `only [unitV_eq]`. Rewrite using `[lamGvS_eq ψ χ (by omega) hC hb le_rfl, lamGvS_eq ψ χ (by omega) hA.1 hb le_rfl, lamGvS_eq ψ χ (by omega) hB.1 hb' hb', (hB.pat hb).lamF_mul ψ χ (by omega) le_rfl hA.2.2 hm, lamF_succ, reduction_leadingMinor hC hb le_rfl, dT_mul le_rfl (fun _ _ _ _ _ => by omega) hm, matrixExtend …`.

Clear the denominators using the available nonvanishing facts.
-/
theorem SuppG.target {i : ℕ} (hr : k + rS ≤ r) (h : IsMul (r + i * t + t) B A C)
    (hA : SuppG P k rS r t (r + i * t + t) (r + i * t) A) (hB : LevG P k rS r t (r + i * t + t) B)
    (hu : IsUnit (redP P (dT B (r + i * t + t)))) :
    SuppG P k rS r t (r + i * t + t) (r + i * t) C ∧
      valG ψ χ k r t i C * unitV (χ i) (dT B (r + i * t + t)) = lamGvS ψ χ k r t (i + 1) B * valG ψ χ k r t i A := by
  have hC := h.int hB.1 hA.1
  have hb : r + i * t ≤ r + i * t + t := Nat.le_add_right _ _
  have hm : ∀ p p', p < r + i * t → p' < r + i * t →
      red P C p p' = ∑ l ∈ Finset.range (r + i * t), red P B p l * red P A l p' := fun p p' hp hp' => by
    rw [h.red hB.1 hA.1 (by omega) hp', Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range t), add_zero]
    intro l hl
    rw [Finset.mem_range] at hl
    rw [show red P A (r + i * t + l) p' = 0 from (of_div (hA.2.1 _ _ (by omega) (by omega) hp')).2, mul_zero]
  refine ⟨⟨hC, fun p p' h1 h2 h3 => h.div hB.1 hA.1 h2 h3 fun l hl => ?_,
    (hB.pat hb).mul hr (Nat.le_add_right _ _) hA.2.2 hm⟩, ?_⟩
  · by_cases hl' : l < r + i * t
    · exact Or.inl (hB.2.2 i p l h1 h2 hl')
    · exact Or.inr (hA.2.1 l p' (by omega) hl h3)
  have hs : redP P (dT B (r + i * t + t)) = dT (red P B) (r + i * t) * dB (red P B) (r + i * t) t := by
    rw [reduction_leadingMinor hB.1 le_rfl le_rfl]
    exact dT_split fun u l hu hl => (of_div (hB.2.2 i _ _ (by omega) (by omega) hl)).2
  rw [hs] at hu
  have hne := unitCharacterExtendByZero_ne_zero_of_isUnit (χ i) (isUnit_of_mul_isUnit_left hu)
  have hb' : r + (i + 1) * t ≤ r + i * t + t := by rw [add_mul, one_mul, add_assoc]
  unfold valG
  simp only [unitV_eq]
  rw [lamGvS_eq ψ χ (by omega) hC hb le_rfl, lamGvS_eq ψ χ (by omega) hA.1 hb le_rfl,
    lamGvS_eq ψ χ (by omega) hB.1 hb' hb', (hB.pat hb).lamF_mul ψ χ (by omega) le_rfl hA.2.2 hm, lamF_succ,
    reduction_leadingMinor hC hb le_rfl, dT_mul le_rfl (fun _ _ _ _ _ => by omega) hm, matrixExtendByZero_mul, hs, matrixExtendByZero_mul,
    reduction_leadingMinor hA.1 hb le_rfl, mul_inv]
  field_simp

end Mat

section Ent

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

/- English proof (translation)
Unfold `fIdx fPos`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem fIdx_lt {k₀ c n p : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) : fIdx k₀ c n p < n + c ∧ fPos k₀ c n (fIdx k₀ c n p) = p := by
  unfold fIdx fPos
  split_ifs <;> omega

def fPerm {k₀ n : ℕ} (c : ℕ) (hk : k₀ ≤ n) : Equiv.Perm (Fin (n + c)) where
  toFun p := ⟨fIdx k₀ c n p.1, (fIdx_lt hk p.2).1⟩
  invFun l := ⟨fPos k₀ c n l.1, (LastSteps.fIdx_fPos hk l.2).1⟩
  left_inv p := Fin.ext (fIdx_lt hk p.2).2
  right_inv l := Fin.ext (LastSteps.fIdx_fPos hk l.2).2

omit [StarRing E] in
/- English proof (translation)
Introduce `p p'`. Establish `hq : (qOf P : E) ≠ 0` using `q_ne`. Rewrite using `[← Fin.sum_univ_eq_sum_range (fun l => entB (qOf P) k₀ c' n' c n ex' ex x p l * entB (qOf P) k₀ c'' n'' c' n' ex'' ex' y l p') (n' + c')]`. Unfold `entB`. Rewrite using `[LinearMap.comp_apply]`.

Use `set v := y (eN E N'' (fIdx k₀ c'' n'' p')) with hv`. Establish `h2 : v = ∑ l : Fin (n' + c'), v (fPerm c' hk l) • eN E (n' + c') (fPerm c' hk l).1`. Rewrite using `[Equiv.sum_comp (fPerm c' hk) (fun l => v l • eN E (n' + c') l.1)]`. Use function extensionality and compare the values at `i`. Simplify using `[Finset.sum_apply, eN, Fin.val_inj]`.

Establish `h3 : atN (x v) (fIdx k₀ c n p) = ∑ l : Fin (n' + c'), v (fPerm c' hk l) * atN (x (eN E (n' + c') (fPerm c' hk l).1)) (fIdx k₀ c n p)` using `by conv_lhs => rw [h2, map_sum]`. Unfold `atN`. Use `split_ifs`. Simplify using `[Finset.sum_apply]`. Simplify using the standard rewrite rules.

Rewrite using `[h3, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Establish `h4 : atN v (fIdx k₀ c' n' l.1) = v (fPerm c' hk l)` using `dif_pos (fIdx_lt hk l.2).1`. Rewrite using `[h4]`. Use `show _ * atN (x (eN E (n' + c') (fIdx k₀ c' n' l.1))) _ * _ = _`.

Rewrite using `[zpow_sub₀ hq, zpow_sub₀ hq, zpow_sub₀ hq]`. Use `zpow_ne_zero (scE n' ex' (fIdx k₀ c' n' l.1)) hq` as an intermediate fact. Clear the denominators using the available nonvanishing facts.
-/
theorem entB_comp {N'' N k₀ c'' n'' c' n' c n : ℕ} (hk : k₀ ≤ n') (ex'' ex' ex : ℕ → ℕ) (x : HomE E (n' + c') N)
    (y : HomE E N'' (n' + c')) :
    IsMul (n' + c') (entB (qOf P) k₀ c' n' c n ex' ex x) (entB (qOf P) k₀ c'' n'' c' n' ex'' ex' y)
      (entB (qOf P) k₀ c'' n'' c n ex'' ex (x ∘ₗ y)) := by
  intro p p'
  have hq : (qOf P : E) ≠ 0 := q_ne
  rw [← Fin.sum_univ_eq_sum_range (fun l => entB (qOf P) k₀ c' n' c n ex' ex x p l *
    entB (qOf P) k₀ c'' n'' c' n' ex'' ex' y l p') (n' + c')]
  unfold entB
  rw [LinearMap.comp_apply]
  set v := y (eN E N'' (fIdx k₀ c'' n'' p')) with hv
  have h2 : v = ∑ l : Fin (n' + c'), v (fPerm c' hk l) • eN E (n' + c') (fPerm c' hk l).1 := by
    rw [Equiv.sum_comp (fPerm c' hk) (fun l => v l • eN E (n' + c') l.1)]
    funext i
    simp [Finset.sum_apply, eN, Fin.val_inj]
  have h3 : atN (x v) (fIdx k₀ c n p) =
      ∑ l : Fin (n' + c'), v (fPerm c' hk l) * atN (x (eN E (n' + c') (fPerm c' hk l).1)) (fIdx k₀ c n p) := by
    conv_lhs => rw [h2, map_sum]
    unfold atN
    split_ifs
    · simp [Finset.sum_apply]
    · simp
  rw [h3, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h4 : atN v (fIdx k₀ c' n' l.1) = v (fPerm c' hk l) := dif_pos (fIdx_lt hk l.2).1
  rw [h4]
  show _ * atN (x (eN E (n' + c') (fIdx k₀ c' n' l.1))) _ * _ = _
  rw [zpow_sub₀ hq, zpow_sub₀ hq, zpow_sub₀ hq]
  have := zpow_ne_zero (scE n' ex' (fIdx k₀ c' n' l.1)) hq
  field_simp

omit [StarRing E] in
/- English proof (translation)
Establish `hq : (qOf P : E) ≠ 0` using `q_ne`. Establish `h1 : (Matrix.of fun s s' : Fin (n + c) => entB (qOf P) k₀ c n c n ex ex g.toLinearMap s.1 s'.1) = Matrix.of fun l l' : Fin (n + c) => ((qOf P : E) ^ scE n ex (fIdx k₀ c n l.1))⁻¹ * (Matrix.of fun l l' : Fin (n + c) => (qOf P : E) ^ scE n ex (fIdx k₀ c n l'.1) * ((LinearMap.toMatr …`. Use extensionality with `l l'`. Simplify using `only [Matrix.of_apply, Matrix.submatrix_apply, LinearMap.toMatrix'_apply]`. Unfold `entB atN`.

Rewrite using `[dif_pos (fIdx_lt hk l.2).1, LastSteps.eN_eq (fIdx_lt hk l'.2).1, zpow_sub₀ hq]`. Use `show _ = _ * (_ * g.toLinearMap (Pi.single ⟨_, (fIdx_lt hk l'.2).1⟩ 1) ⟨_, (fIdx_lt hk l.2).1⟩)`. Expand and normalize the polynomial expressions, which then agree. Unfold `dT`. Rewrite using `[h1, Matrix.det_mul_column, Matrix.det_mul_row, Finset.prod_inv_distrib, ← mul_assoc, inv_mul_cancel₀ (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ hq), one_mul, Matrix.det_submatrix_equiv_self, LinearMap.det_toMatrix', LinearEquiv.coe_det]`.
-/
theorem entB_det {k₀ c n : ℕ} (hk : k₀ ≤ n) (ex : ℕ → ℕ) (g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :
    ((LinearEquiv.det g : Eˣ) : E) = dT (entB (qOf P) k₀ c n c n ex ex g.toLinearMap) (n + c) := by
  have hq : (qOf P : E) ≠ 0 := q_ne
  have h1 : (Matrix.of fun s s' : Fin (n + c) => entB (qOf P) k₀ c n c n ex ex g.toLinearMap s.1 s'.1) =
      Matrix.of fun l l' : Fin (n + c) => ((qOf P : E) ^ scE n ex (fIdx k₀ c n l.1))⁻¹ *
        (Matrix.of fun l l' : Fin (n + c) => (qOf P : E) ^ scE n ex (fIdx k₀ c n l'.1) *
          ((LinearMap.toMatrix' g.toLinearMap).submatrix (fPerm c hk) (fPerm c hk)) l l') l l' := by
    ext l l'
    simp only [Matrix.of_apply, Matrix.submatrix_apply, LinearMap.toMatrix'_apply]
    unfold entB atN
    rw [dif_pos (fIdx_lt hk l.2).1, LastSteps.eN_eq (fIdx_lt hk l'.2).1, zpow_sub₀ hq]
    show _ = _ * (_ * g.toLinearMap (Pi.single ⟨_, (fIdx_lt hk l'.2).1⟩ 1) ⟨_, (fIdx_lt hk l.2).1⟩)
    ring
  unfold dT
  rw [h1, Matrix.det_mul_column, Matrix.det_mul_row, Finset.prod_inv_distrib, ← mul_assoc,
    inv_mul_cancel₀ (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ hq), one_mul,
    Matrix.det_submatrix_equiv_self, LinearMap.det_toMatrix', LinearEquiv.coe_det]

variable (E) in

def bv (q k₀ n c : ℕ) (ex : ℕ → ℕ) (s : ℕ) : Sp E (n + c) :=
  ((q : E) ^ scE n ex (fIdx k₀ c n s)) • eN E (n + c) (fIdx k₀ c n s)

def co (q k₀ n c : ℕ) (ex : ℕ → ℕ) (v : Sp E (n + c)) (p : ℕ) : E :=
  ((q : E) ^ scE n ex (fIdx k₀ c n p))⁻¹ * atN v (fIdx k₀ c n p)

variable (P) in

def midL (k₀ n c : ℕ) (ex : ℕ → ℕ) (D : ℕ → Prop) [DecidablePred D] : Submodule (𝓞 E) (Sp E (n + c)) :=
  sclLat P (qOf P) (n + c) fun l => scE n ex l + if D (fPos k₀ c n l) then 1 else 0

variable {k₀ n c : ℕ} {ex : ℕ → ℕ}

omit [StarRing E] in
/- English proof (translation)
Establish `hq : (qOf P : E) ≠ 0` using `q_ne`. Unfold `entB co bv atN`. Rewrite using `[zpow_sub₀ hq, map_smul]`. Use `split_ifs`. Rewrite using `[Pi.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem entB_eq_co (g : HomE E (n + c) (n + c)) (p p' : ℕ) :
    entB (qOf P) k₀ c n c n ex ex g p p' = co (qOf P) k₀ n c ex (g (bv E (qOf P) k₀ n c ex p')) p := by
  have hq : (qOf P : E) ≠ 0 := q_ne
  unfold entB co bv atN
  rw [zpow_sub₀ hq, map_smul]
  split_ifs
  · rw [Pi.smul_apply, smul_eq_mul]
    ring
  · simp

omit [StarRing E] in
/- English proof (translation)
Unfold `co atN`. Use `split_ifs`. Rewrite using `[Pi.sub_apply, mul_sub]`. Simplify using the standard rewrite rules.
-/
theorem co_sub (v w : Sp E (n + c)) (p : ℕ) :
    co (qOf P) k₀ n c ex (v - w) p = co (qOf P) k₀ n c ex v p - co (qOf P) k₀ n c ex w p := by
  unfold co atN
  split_ifs
  · rw [Pi.sub_apply, mul_sub]
  · simp

omit [StarRing E] in
/- English proof (translation)
Establish `hq : (qOf P : E) ≠ 0` using `q_ne`. Unfold `co bv atN eN`. Rewrite using `[dif_pos (fIdx_lt hk hp).1, Pi.smul_apply, smul_eq_mul]`. Distinguish the cases in `h : p = p'`. Substitute `h` using the available equality.

Simplify using `[inv_mul_cancel₀ (zpow_ne_zero _ hq)]`. Rewrite using `[if_neg h, if_neg, mul_zero, mul_zero]`. Introduce `h1`. Apply `h` to reduce the goal to its premises. Rewrite using `[← (fIdx_lt hk hp).2, ← (fIdx_lt hk hp').2]`.

Conclude with `congrArg _ h1`.
-/
theorem co_bv (hk : k₀ ≤ n) {p p' : ℕ} (hp : p < n + c) (hp' : p' < n + c) :
    co (qOf P) k₀ n c ex (bv E (qOf P) k₀ n c ex p') p = if p = p' then 1 else 0 := by
  have hq : (qOf P : E) ≠ 0 := q_ne
  unfold co bv atN eN
  rw [dif_pos (fIdx_lt hk hp).1, Pi.smul_apply, smul_eq_mul]
  by_cases h : p = p'
  · subst h
    simp [inv_mul_cancel₀ (zpow_ne_zero _ hq)]
  · rw [if_neg h, if_neg, mul_zero, mul_zero]
    intro h1
    apply h
    rw [← (fIdx_lt hk hp).2, ← (fIdx_lt hk hp').2]
    exact congrArg _ h1

/- English proof (translation)
Establish `hq : (qOf P : E) ≠ 0` using `q_ne`. Establish `h` using `LastSteps.mem_sclLat.1 hv ⟨_, (fIdx_lt hk hp).1⟩`. Simplify using `only [(fIdx_lt hk hp).2, if_pos hD] at h`. Unfold `co atN`. Rewrite using `[dif_pos (fIdx_lt hk hp).1]`.

Use `h using 1` and compare the differences between its conclusion and the goal. Rewrite using `[zpow_add₀ hq, zpow_one]`. Use `zpow_ne_zero (scE n ex (fIdx k₀ c n p)) hq` as an intermediate fact. Clear the denominators using the available nonvanishing facts.
-/
theorem co_mid (hk : k₀ ≤ n) {D : ℕ → Prop} [DecidablePred D] {v : Sp E (n + c)} (hv : v ∈ midL P k₀ n c ex D) {p : ℕ}
    (hp : p < n + c) (hD : D p) : IntAt P (co (qOf P) k₀ n c ex v p / (qOf P : E)) := by
  have hq : (qOf P : E) ≠ 0 := q_ne
  have h := LastSteps.mem_sclLat.1 hv ⟨_, (fIdx_lt hk hp).1⟩
  simp only [(fIdx_lt hk hp).2, if_pos hD] at h
  unfold co atN
  rw [dif_pos (fIdx_lt hk hp).1]
  convert h using 1
  rw [zpow_add₀ hq, zpow_one]
  have := zpow_ne_zero (scE n ex (fIdx k₀ c n p)) hq
  field_simp

/- English proof (translation)
Establish `hq : (qOf P : E) ≠ 0` using `q_ne`. Use `LastSteps.mem_sclLat.2 fun l => ?_` and prove the remaining obligations. Unfold `bv eN`. Rewrite using `[Pi.smul_apply, smul_eq_mul]`. Distinguish the cases in `h : l.1 = fIdx k₀ c n p`.

Simplify using `only [h, (fIdx_lt hk hp).2, if_neg hD, add_zero, if_true, mul_one]`. Rewrite using `[inv_mul_cancel₀ (zpow_ne_zero _ hq)]`. Conclude with `SymLevelInv.intAt_one P`. Rewrite using `[if_neg h, mul_zero, mul_zero]`. Conclude with `SymLevelInv.intAt_zero P`.
-/
theorem bv_mid (hk : k₀ ≤ n) {D : ℕ → Prop} [DecidablePred D] {p : ℕ} (hp : p < n + c) (hD : ¬ D p) :
    bv E (qOf P) k₀ n c ex p ∈ midL P k₀ n c ex D := by
  have hq : (qOf P : E) ≠ 0 := q_ne
  refine LastSteps.mem_sclLat.2 fun l => ?_
  unfold bv eN
  rw [Pi.smul_apply, smul_eq_mul]
  by_cases h : l.1 = fIdx k₀ c n p
  · simp only [h, (fIdx_lt hk hp).2, if_neg hD, add_zero, if_true, mul_one]
    rw [inv_mul_cancel₀ (zpow_ne_zero _ hq)]
    exact SymLevelInv.intAt_one P
  · rw [if_neg h, mul_zero, mul_zero]
    exact SymLevelInv.intAt_zero P

/- English proof (translation)
Rewrite using `[entB_eq_co]`. Conclude with `co_mid hk ((hg _).2 (bv_mid hk hp' hD')) hp hD`.
-/
theorem ent_div (hk : k₀ ≤ n) {D : ℕ → Prop} [DecidablePred D] {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hg : g ∈ stabL E (n + c) (midL P k₀ n c ex D)) {p p' : ℕ} (hp : p < n + c) (hp' : p' < n + c) (hD : D p) (hD' : ¬ D p') :
    IntAt P (entB (qOf P) k₀ c n c n ex ex g.toLinearMap p p' / (qOf P : E)) := by
  rw [entB_eq_co]
  exact co_mid hk ((hg _).2 (bv_mid hk hp' hD')) hp hD

/- English proof (translation)
Take `⟨h1, h2⟩` from `of_div (co_mid hk hg hp hD)`. Establish `e : entB (qOf P) k₀ c n c n ex ex g.toLinearMap p p' = co (qOf P) k₀ n c ex (g (bv E (qOf P) k₀ n c ex p') - bv E (qOf P) k₀ n c ex p') p + if p = p' then 1 else 0`. Rewrite using `[co_sub, co_bv hk hp hp', sub_add_cancel, entB_eq_co]`. Both sides reduce to the same expression. Rewrite using `[e, reduction_add h1 (SymLevelInv.intAt_ite _), h2, zero_add]`.

Use `split_ifs`. Conclude with `SymLevelInv.reduction_one' P`. Conclude with `SymLevelInv.redP_zero' P`.
-/
theorem ent_col (hk : k₀ ≤ n) {D : ℕ → Prop} [DecidablePred D] {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} {p p' : ℕ}
    (hg : g (bv E (qOf P) k₀ n c ex p') - bv E (qOf P) k₀ n c ex p' ∈ midL P k₀ n c ex D) (hp : p < n + c) (hp' : p' < n + c)
    (hD : D p) : redP P (entB (qOf P) k₀ c n c n ex ex g.toLinearMap p p') = if p = p' then 1 else 0 := by
  obtain ⟨h1, h2⟩ := of_div (co_mid hk hg hp hD)
  have e : entB (qOf P) k₀ c n c n ex ex g.toLinearMap p p' =
      co (qOf P) k₀ n c ex (g (bv E (qOf P) k₀ n c ex p') - bv E (qOf P) k₀ n c ex p') p + if p = p' then 1 else 0 := by
    rw [co_sub, co_bv hk hp hp', sub_add_cancel, entB_eq_co]
    rfl
  rw [e, reduction_add h1 (SymLevelInv.intAt_ite _), h2, zero_add]
  split_ifs
  · exact SymLevelInv.reduction_one' P
  · exact SymLevelInv.redP_zero' P

/- English proof (translation)
Introduce `p p' _ _` and use `LastSteps.entB_int k₀ (fun y hy => (hg y).2 hy) p p'`.
-/
theorem ent_int {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ stabL E (n + c) (lamY P (qOf P) n c ex)) :
    IntM P (n + c) (n + c) (entB (qOf P) k₀ c n c n ex ex g.toLinearMap) := fun p p' _ _ =>
  LastSteps.entB_int k₀ (fun y hy => (hg y).2 hy) p p'

/- English proof (translation)
Use `⟨ent_int hg.1, fun p' hp' => ?_, fun i p p' h1 h2 h3 => ?_⟩` and prove the remaining obligations. Establish `h` using `fun p hp hD => ent_col (p := p) (D := fun l => p' ≤ l) hk (hg.2.2 p' hp').2 hp (by omega) hD`. Use `⟨(h p' (by omega) le_rfl).trans (if_pos rfl), fun p hp hne hz => (h p hp ?_).trans (if_neg hne)⟩` and prove the remaining obligations. Establish `e1` using `SymLevelInv.symIdx_cases r 0 p`. Establish `e2` using `SymLevelInv.symIdx_cases r 0 p'`.

Unfold `Zs at hz`. Use linear arithmetic over natural numbers and integers. Conclude with `ent_div (D := fun l => r + i * t ≤ l) hk (hg.2.1 _ ⟨i, rfl⟩) h2 (by omega) h1 (by omega)`.
-/
theorem levG_of_JG {r t : ℕ} (hk : k₀ ≤ n) (hr : r ≤ n + c) {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hg : g ∈ JG P (qOf P) k₀ r t n c) :
    LevG P r 0 r t (n + c) (entB (qOf P) k₀ c n c n (fun i => i + 1) (fun i => i + 1) g.toLinearMap) := by
  refine ⟨ent_int hg.1, fun p' hp' => ?_, fun i p p' h1 h2 h3 => ?_⟩
  · have h := fun p hp hD => ent_col (p := p) (D := fun l => p' ≤ l) hk (hg.2.2 p' hp').2 hp (by omega) hD
    refine ⟨(h p' (by omega) le_rfl).trans (if_pos rfl), fun p hp hne hz => (h p hp ?_).trans (if_neg hne)⟩
    have e1 := SymLevelInv.symIdx_cases r 0 p
    have e2 := SymLevelInv.symIdx_cases r 0 p'
    unfold Zs at hz
    omega
  · exact ent_div (D := fun l => r + i * t ≤ l) hk (hg.2.1 _ ⟨i, rfl⟩) h2 (by omega) h1 (by omega)

/- English proof (translation)
Use `⟨ent_int hg.1, fun p' hp' => ?_, fun i p p' h1 h2 h3 => ?_⟩` and prove the remaining obligations. Establish `h0` using `(hg.2.2 (symIdx k₀ rS p') (symIdx_lt hS.le hp')).2`. Unfold `bvecS at h0`. Rewrite `h0` using `[symIdxInv_symIdx]`. Establish `h` using `fun p hp hD => ent_col (p := p) (D := fun l => bd5 k₀ rS (symIdx k₀ rS p') ≤ symIdx k₀ rS l) hk h0 hp (by omega) hD`.

Establish `e2` using `SymLevelInv.symIdx_cases k₀ rS p'`. Establish `e3` using `SymLevelInv.symmetricBlockBoundary_cases k₀ rS (symIdx k₀ rS p')`. Use `⟨(h p' (by omega) (by omega)).trans (if_pos rfl), fun p hp hne hz => (h p hp ?_).trans (if_neg hne)⟩` and prove the remaining obligations. Establish `e1` using `SymLevelInv.symIdx_cases k₀ rS p`. Unfold `Zs at hz`.

Use linear arithmetic over natural numbers and integers. Establish `e1` using `SymLevelInv.symIdx_cases k₀ rS p`. Establish `e2` using `SymLevelInv.symIdx_cases k₀ rS p'`. Establish `e3` using `SymLevelInv.symmetricBlockBoundary_cases k₀ rS (r + i * t)`. Conclude with `ent_div (D := fun l => bd5 k₀ rS (r + i * t) ≤ symIdx k₀ rS l) hk (hg.2.1 _ ⟨i, rfl⟩) h2 (by omega) (by omega) (by omega)`.
-/
theorem levG_of_JGsym {rS r t : ℕ} (hk : k₀ ≤ n) (hS : k₀ + rS < r) (hr : r ≤ n + c) {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hg : g ∈ JGsym P (qOf P) k₀ rS r t n c) :
    LevG P k₀ rS r t (n + c) (entB (qOf P) k₀ c n c n (fun i => i + 1) (fun i => i + 1) g.toLinearMap) := by
  refine ⟨ent_int hg.1, fun p' hp' => ?_, fun i p p' h1 h2 h3 => ?_⟩
  · have h0 := (hg.2.2 (symIdx k₀ rS p') (symIdx_lt hS.le hp')).2
    unfold bvecS at h0
    rw [symIdxInv_symIdx] at h0
    have h := fun p hp hD => ent_col (p := p) (D := fun l => bd5 k₀ rS (symIdx k₀ rS p') ≤ symIdx k₀ rS l) hk h0 hp (by omega) hD
    have e2 := SymLevelInv.symIdx_cases k₀ rS p'
    have e3 := SymLevelInv.symmetricBlockBoundary_cases k₀ rS (symIdx k₀ rS p')
    refine ⟨(h p' (by omega) (by omega)).trans (if_pos rfl), fun p hp hne hz => (h p hp ?_).trans (if_neg hne)⟩
    have e1 := SymLevelInv.symIdx_cases k₀ rS p
    unfold Zs at hz
    omega
  · have e1 := SymLevelInv.symIdx_cases k₀ rS p
    have e2 := SymLevelInv.symIdx_cases k₀ rS p'
    have e3 := SymLevelInv.symmetricBlockBoundary_cases k₀ rS (r + i * t)
    exact ent_div (D := fun l => bd5 k₀ rS (r + i * t) ≤ symIdx k₀ rS l) hk (hg.2.1 _ ⟨i, rfl⟩) h2 (by omega)
      (by omega) (by omega)

/- English proof (translation)
Unfold `scE`. Simplify using the standard rewrite rules.
-/
theorem scE_zero (n l : ℕ) : scE n 0 l = 0 := by
  unfold scE
  simp

/- English proof (translation)
Use extensionality with `v`. Unfold `lamY`. Rewrite using `[LastSteps.mem_sclLat]`. Unfold `stdAt`. Rewrite using `[mem_localization_standardLattice]`.

Simplify using `[scE_zero]`.
-/
theorem stdAt_eq : stdAt E (n + c) P = lamY P (qOf P) n c 0 := by
  ext v
  unfold lamY
  rw [LastSteps.mem_sclLat]
  unfold stdAt
  rw [mem_localization_standardLattice]
  simp [scE_zero]

/- English proof (translation)
Use `⟨ent_int (stdAt_eq (E := E) (P := P) (n := n) (c := c) ▸ hg.1), fun p p' h1 h2 h3 => ?_⟩` and prove the remaining obligations. Establish `e : parL P (qOf P) kj n c = midL P k₀ n c 0 fun l => kj + c ≤ l`. Use extensionality with `v`. Unfold `parL midL`. Rewrite using `[LastSteps.mem_sclLat, LastSteps.mem_sclLat]`.

Use `forall_congr' fun l => ?_` and prove the remaining obligations. Use `l.2` as an intermediate fact. Rewrite using `[scE_zero, zero_add, if_congr (show (kj ≤ l.1 ∧ l.1 < n) ↔ kj + c ≤ fPos k₀ c n l.1 by`. Apply the tactic sequence `unfold fPos; split_ifs <;> omega) rfl rfl]`. Conclude with `ent_div (D := fun l => kj + c ≤ l) (by omega) (e ▸ hg.2) h2 (by omega) h1 (by omega)`.
-/
theorem suppQ_of_JQ {kj : ℕ} (hk : k₀ ≤ kj) (hn : kj ≤ n) {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hg : g ∈ JQ P (qOf P) kj n c) :
    SuppQ P (kj + c) (n + c) (n + c) (entB (qOf P) k₀ c n c n 0 0 g.toLinearMap) := by
  refine ⟨ent_int (stdAt_eq (E := E) (P := P) (n := n) (c := c) ▸ hg.1), fun p p' h1 h2 h3 => ?_⟩
  have e : parL P (qOf P) kj n c = midL P k₀ n c 0 fun l => kj + c ≤ l := by
    ext v
    unfold parL midL
    rw [LastSteps.mem_sclLat, LastSteps.mem_sclLat]
    refine forall_congr' fun l => ?_
    have := l.2
    rw [scE_zero, zero_add, if_congr (show (kj ≤ l.1 ∧ l.1 < n) ↔ kj + c ≤ fPos k₀ c n l.1 by
      unfold fPos; split_ifs <;> omega) rfl rfl]
  exact ent_div (D := fun l => kj + c ≤ l) (by omega) (e ▸ hg.2) h2 (by omega) h1 (by omega)

omit [StarRing E] in
/- English proof (translation)
Establish `e : ∀ s, fIdx k₀ c n (kj + c + s) = kj + s` using `fun s => by`. Unfold `fIdx`. Apply the tactic sequence `split_ifs <;> omega`. Unfold `lamQB dB entB`. Simplify using `only [e, scE_zero, sub_zero, zpow_zero, mul_one]`.
-/
theorem lamQB_eq (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {kj : ℕ} (hk : k₀ ≤ kj) (g : HomE E (n + c) (n + c)) :
    lamQB ξ kj n g = (unitV ξ (dB (entB (qOf P) k₀ c n c n 0 0 g) (kj + c) (n - kj)))⁻¹ := by
  have e : ∀ s, fIdx k₀ c n (kj + c + s) = kj + s := fun s => by
    unfold fIdx
    split_ifs <;> omega
  unfold lamQB dB entB
  simp only [e, scE_zero, sub_zero, zpow_zero, mul_one]

end Ent

section Laws

open Classical in
/- English proof (translation)
Distinguish the cases in `hx : S x`. Rewrite using `[if_pos hx, if_pos (h g hg x hx).1, (h g hg x hx).2]`. Rewrite using `[if_neg hx, if_neg fun h' => hx (hact g x ▸ (h g⁻¹ (inv_mem hg) _ h').1), zero_mul, mul_zero]`.
-/
theorem ite_law {G Y K : Type} [Group G] [Field K] (J : Subgroup G) (act : G → Y → Y) (hact : ∀ g x, act g⁻¹ (act g x) = x)
    (S : Y → Prop) (val : Y → K) (μ lam : G → K)
    (h : ∀ g ∈ J, ∀ x, S x → S (act g x) ∧ val (act g x) * μ g = lam g * val x) {g : G} (hg : g ∈ J) (x : Y) :
    (if S (act g x) then val (act g x) else 0) * μ g = lam g * if S x then val x else 0 := by
  by_cases hx : S x
  · rw [if_pos hx, if_pos (h g hg x hx).1, (h g hg x hx).2]
  · rw [if_neg hx, if_neg fun h' => hx (hact g x ▸ (h g⁻¹ (inv_mem hg) _ h').1), zero_mul, mul_zero]

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

omit [NumberField E] [StarRing E] in
/- English proof (translation)
The claim follows from `LinearMap.ext fun v => congrArg x (g.apply_symm_apply v)`.
-/
theorem comp_inv {a b : ℕ} (g : Sp E a ≃ₗ[E] Sp E a) (x : HomE E a b) :
    (x ∘ₗ g.toLinearMap) ∘ₗ (g⁻¹ : Sp E a ≃ₗ[E] Sp E a).toLinearMap = x :=
  LinearMap.ext fun v => congrArg x (g.apply_symm_apply v)

omit [NumberField E] [StarRing E] in
/- English proof (translation)
The claim follows from `LinearMap.ext fun v => g.symm_apply_apply (x v)`.
-/
theorem inv_comp {a b : ℕ} (g : Sp E b ≃ₗ[E] Sp E b) (x : HomE E a b) :
    (g⁻¹ : Sp E b ≃ₗ[E] Sp E b).toLinearMap ∘ₗ (g.toLinearMap ∘ₗ x) = x :=
  LinearMap.ext fun v => g.symm_apply_apply (x v)

variable (ψ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
  {k₀ k₁ rS r t i c' n' c n : ℕ}

open Classical in

def PhiM (k₀ k₁ rS r t i c' n' c n : ℕ) : SF E K (n' + c') (n + c) := fun x =>
  if SuppG P k₁ rS r t (n + c) (r + i * t) (entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x) then
    valG ψ χ k₁ r t i (entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x) else 0

omit [StarRing E] in
/- English proof (translation)
Use function extensionality and compare the values at `x`. Conclude with `LastSteps.ite_eq_ite_zero Iff.rfl fun _ => rfl`.
-/
theorem phiGS_eq : PhiGS (qOf P) ψ χ k₀ rS r t (i + 1) c' n' c n = PhiM ψ χ k₀ k₀ rS r t i c' n' c n := by
  funext x
  exact LastSteps.ite_eq_ite_zero Iff.rfl fun _ => rfl

omit [StarRing E] in
/- English proof (translation)
Unfold `lamGv lamGvS`. Simplify using the standard rewrite rules.
-/
theorem lamGv_eq (j : ℕ) (M : ℕ → ℕ → E) : lamGv ψ χ r t j M = lamGvS ψ χ r r t j M := by
  unfold lamGv lamGvS
  simp

omit [StarRing E] in
/- English proof (translation)
Use function extensionality and compare the values at `x`. Use `LastSteps.ite_eq_ite_zero ?_ fun _ => ?_` and prove the remaining obligations. Establish `hz : ∀ p p', p' < r → (p' < p ↔ p ≠ p' ∧ Zs r 0 r p p')` using `fun p p' hp' => by`. Establish `e1` using `SymLevelInv.symIdx_cases r 0 p`. Establish `e2` using `SymLevelInv.symIdx_cases r 0 p'`.

Unfold `Zs`. Use linear arithmetic over natural numbers and integers. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3, h4, -⟩`. Conclude with `⟨h1, h2, fun p' hp' => ⟨(h3 p' hp').1, fun p hp hne hz' => (h3 p' hp').2 p ((hz p p' hp').2 ⟨hne, hz'⟩) hp⟩, h4⟩`.

Introduce and unpack `⟨h1, h2, h3, h4⟩`. Conclude with `⟨h1, h2, fun p' hp' => ⟨(h3 p' hp').1, fun p hlt hp => (h3 p' hp').2 p hp ((hz p p' hp').1 hlt).1 ((hz p p' hp').1 hlt).2⟩, h4, fun h => absurd h (by simp)⟩`. Rewrite using `[lamGv_eq]`. Both sides reduce to the same expression.
-/
theorem phiG_eq : PhiG (qOf P) ψ χ false k₀ r t (i + 1) c' n' c n = PhiM ψ χ k₀ r 0 r t i c' n' c n := by
  funext x
  refine LastSteps.ite_eq_ite_zero ?_ fun _ => ?_
  · have hz : ∀ p p', p' < r → (p' < p ↔ p ≠ p' ∧ Zs r 0 r p p') := fun p p' hp' => by
      have e1 := SymLevelInv.symIdx_cases r 0 p
      have e2 := SymLevelInv.symIdx_cases r 0 p'
      unfold Zs
      omega
    constructor
    · rintro ⟨h1, h2, h3, h4, -⟩
      exact ⟨h1, h2, fun p' hp' => ⟨(h3 p' hp').1, fun p hp hne hz' => (h3 p' hp').2 p ((hz p p' hp').2 ⟨hne, hz'⟩) hp⟩, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, fun p' hp' => ⟨(h3 p' hp').1, fun p hlt hp =>
        (h3 p' hp').2 p hp ((hz p p' hp').1 hlt).1 ((hz p p' hp').1 hlt).2⟩, h4, fun h => absurd h (by simp)⟩
  · rw [lamGv_eq]
    rfl

/- English proof (translation)
Use `ite_law J (fun g (x : HomE E (n' + c') (n + c)) => x ∘ₗ g.toLinearMap) comp_inv (fun x => SuppG P k₁ rS r t (n + c) (r + i * t) (entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x)) (fun x => valG ψ χ k₁ r t i (entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1 …` and prove the remaining obligations. Establish `hu` using `LastSteps.isUnit_det_of_stab (hJ hg)`. Establish `hm` using `entB_comp (P := P) (c := c) (n := n) (c'' := c') (n'' := n') hk (fun i => i + 1) (fun i => i + 1) (fun i => i + 1) x g.toLinearMap`. Establish `hl` using `hL g hg`. Rewrite `hu`, the goal using `[entB_det (P := P) hk (fun i => i + 1)]`.

Generalize the expression as in `entB (qOf P) k₀ c' n' c' n' (fun i => i + 1) (fun i => i + 1) g.toLinearMap = B at *`. Generalize the expression as in `entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) (x ∘ₗ g.toLinearMap) = C at *`. Generalize the expression as in `entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x = A at *`. Rewrite `hu`, `hm`, `hl`, the goal using `[ha]`. Conclude with `SuppG.source ψ χ hr hb hm hx hl hu`.
-/
theorem phiM_source (hk : k₀ ≤ n') (hr : k₁ + rS ≤ r) (ha : n' + c' = r + i * t) (hb : r + i * t ≤ n + c)
    (J : Subgroup (Sp E (n' + c') ≃ₗ[E] Sp E (n' + c'))) (hJ : J ≤ stabL E _ (lamY P (qOf P) n' c' fun i => i + 1))
    (hL : ∀ g ∈ J, LevG P k₁ rS r t (n' + c') (entB (qOf P) k₀ c' n' c' n' (fun i => i + 1) (fun i => i + 1) g.toLinearMap))
    {g : Sp E (n' + c') ≃ₗ[E] Sp E (n' + c')} (hg : g ∈ J) (x : HomE E (n' + c') (n + c)) :
    PhiM ψ χ k₀ k₁ rS r t i c' n' c n (x ∘ₗ g.toLinearMap) * unitV (χ i) ((LinearEquiv.det g : Eˣ) : E) =
      lamGvS ψ χ k₁ r t i (entB (qOf P) k₀ c' n' c' n' (fun i => i + 1) (fun i => i + 1) g.toLinearMap) *
        PhiM ψ χ k₀ k₁ rS r t i c' n' c n x := by
  refine ite_law J (fun g (x : HomE E (n' + c') (n + c)) => x ∘ₗ g.toLinearMap) comp_inv
    (fun x => SuppG P k₁ rS r t (n + c) (r + i * t) (entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x))
    (fun x => valG ψ χ k₁ r t i (entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x))
    (fun g => unitV (χ i) ((LinearEquiv.det g : Eˣ) : E))
    (fun g => lamGvS ψ χ k₁ r t i (entB (qOf P) k₀ c' n' c' n' (fun i => i + 1) (fun i => i + 1) g.toLinearMap))
    (fun g hg x hx => ?_) hg x
  have hu := LastSteps.isUnit_det_of_stab (hJ hg)
  have hm := entB_comp (P := P) (c := c) (n := n) (c'' := c') (n'' := n') hk (fun i => i + 1) (fun i => i + 1)
    (fun i => i + 1) x g.toLinearMap
  have hl := hL g hg
  rw [entB_det (P := P) hk (fun i => i + 1)] at hu ⊢
  generalize entB (qOf P) k₀ c' n' c' n' (fun i => i + 1) (fun i => i + 1) g.toLinearMap = B at *
  generalize entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) (x ∘ₗ g.toLinearMap) = C at *
  generalize entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x = A at *
  rw [ha] at hu hm hl ⊢
  exact SuppG.source ψ χ hr hb hm hx hl hu

/- English proof (translation)
Use `ite_law J (fun g (x : HomE E (n' + c') (n + c)) => g.toLinearMap ∘ₗ x) inv_comp (fun x => SuppG P k₁ rS r t (n + c) (r + i * t) (entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x)) (fun x => valG ψ χ k₁ r t i (entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1 …` and prove the remaining obligations. Establish `hu` using `LastSteps.isUnit_det_of_stab (hJ hg)`. Establish `hm` using `entB_comp (P := P) (c := c) (n := n) (c'' := c') (n'' := n') hk (fun i => i + 1) (fun i => i + 1) (fun i => i + 1) g.toLinearMap x`. Establish `hl` using `hL g hg`. Rewrite `hu`, the goal using `[entB_det (P := P) hk (fun i => i + 1)]`.

Generalize the expression as in `entB (qOf P) k₀ c n c n (fun i => i + 1) (fun i => i + 1) g.toLinearMap = B at *`. Generalize the expression as in `entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) (g.toLinearMap ∘ₗ x) = C at *`. Generalize the expression as in `entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x = A at *`. Rewrite `hu`, `hm`, `hl`, `hx`, the goal using `[hb]`. Conclude with `SuppG.target ψ χ hr hm hx hl hu`.
-/
theorem phiM_target (hk : k₀ ≤ n) (hr : k₁ + rS ≤ r) (hb : n + c = r + i * t + t)
    (J : Subgroup (Sp E (n + c) ≃ₗ[E] Sp E (n + c))) (hJ : J ≤ stabL E _ (lamY P (qOf P) n c fun i => i + 1))
    (hL : ∀ g ∈ J, LevG P k₁ rS r t (n + c) (entB (qOf P) k₀ c n c n (fun i => i + 1) (fun i => i + 1) g.toLinearMap))
    {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ J) (x : HomE E (n' + c') (n + c)) :
    PhiM ψ χ k₀ k₁ rS r t i c' n' c n (g.toLinearMap ∘ₗ x) * unitV (χ i) ((LinearEquiv.det g : Eˣ) : E) =
      lamGvS ψ χ k₁ r t (i + 1) (entB (qOf P) k₀ c n c n (fun i => i + 1) (fun i => i + 1) g.toLinearMap) *
        PhiM ψ χ k₀ k₁ rS r t i c' n' c n x := by
  refine ite_law J (fun g (x : HomE E (n' + c') (n + c)) => g.toLinearMap ∘ₗ x) inv_comp
    (fun x => SuppG P k₁ rS r t (n + c) (r + i * t) (entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x))
    (fun x => valG ψ χ k₁ r t i (entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x))
    (fun g => unitV (χ i) ((LinearEquiv.det g : Eˣ) : E))
    (fun g => lamGvS ψ χ k₁ r t (i + 1) (entB (qOf P) k₀ c n c n (fun i => i + 1) (fun i => i + 1) g.toLinearMap))
    (fun g hg x hx => ?_) hg x
  have hu := LastSteps.isUnit_det_of_stab (hJ hg)
  have hm := entB_comp (P := P) (c := c) (n := n) (c'' := c') (n'' := n') hk (fun i => i + 1) (fun i => i + 1)
    (fun i => i + 1) g.toLinearMap x
  have hl := hL g hg
  rw [entB_det (P := P) hk (fun i => i + 1)] at hu ⊢
  generalize entB (qOf P) k₀ c n c n (fun i => i + 1) (fun i => i + 1) g.toLinearMap = B at *
  generalize entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) (g.toLinearMap ∘ₗ x) = C at *
  generalize entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x = A at *
  rw [hb] at hu hm hl hx ⊢
  exact SuppG.target ψ χ hr hm hx hl hu

/- English proof (translation)
Establish `hu` using `LastSteps.isUnit_det_of_stab (stdAt_eq (E := E) (P := P) (n := n) (c := c) ▸ hg.1)`. Establish `hS` using `suppQ_of_JQ hk hn hg`. Rewrite using `[lamQB_eq ξ hk]`. Rewrite `hu`, the goal using `[entB_det (P := P) (k₀ := k₀) (by omega) 0]`. Generalize the expression as in `entB (qOf P) k₀ c n c n 0 0 g.toLinearMap = B at *`.

Establish `e : n + c = kj + c + (n - kj)` using `by omega`. Rewrite `hu`, `hS`, the goal using `[e]`. Rewrite `hu` using `[hS.det]`. Rewrite using `[unitV_eq, unitV_eq, hS.det, redP_dB hS.1 le_rfl le_rfl, extendByZeroOffSubset_mul_left_of_mem_lattice, matrixExtendByZero_mul, mul_inv, mul_inv_cancel_left₀ (unitCharacterExtendByZero_ne_zero_of_isUnit ξ (isUnit_of_mul_isUnit_left hu))]`.
-/
theorem detQ {kj : ℕ} (hk : k₀ ≤ kj) (hn : kj ≤ n) {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ JQ P (qOf P) kj n c) :
    ext0 ξ (dT (red P (entB (qOf P) k₀ c n c n 0 0 g.toLinearMap)) (kj + c)) * unitV ξ⁻¹ ((LinearEquiv.det g : Eˣ) : E) =
      lamQB ξ kj n g.toLinearMap := by
  have hu := LastSteps.isUnit_det_of_stab (stdAt_eq (E := E) (P := P) (n := n) (c := c) ▸ hg.1)
  have hS := suppQ_of_JQ hk hn hg
  rw [lamQB_eq ξ hk]
  rw [entB_det (P := P) (k₀ := k₀) (by omega) 0] at hu ⊢
  generalize entB (qOf P) k₀ c n c n 0 0 g.toLinearMap = B at *
  have e : n + c = kj + c + (n - kj) := by omega
  rw [e] at hu hS ⊢
  rw [hS.det] at hu
  rw [unitV_eq, unitV_eq, hS.det, redP_dB hS.1 le_rfl le_rfl, extendByZeroOffSubset_mul_left_of_mem_lattice, matrixExtendByZero_mul, mul_inv,
    mul_inv_cancel_left₀ (unitCharacterExtendByZero_ne_zero_of_isUnit ξ (isUnit_of_mul_isUnit_left hu))]

/- English proof (translation)
Substitute `hr` using the available equality. Establish `h` using `ite_law (JQ P (qOf P) kj n' c') (fun g (x : HomE E (n' + c') (n + c)) => x ∘ₗ g.toLinearMap) comp_inv (fun x => SuppQ P (kj + c') (n + c) (n' + c') (entB (qOf P) k₀ c' n' c n 0 0 x)) (fun x => unitV ξ (dT (entB (qOf P) k₀ c' n' c n 0 0 x) (kj + c'))) (fun g => unitV ξ⁻¹ ((LinearE …`. Take `⟨h1, h2⟩` from `SuppQ.mul (entB_comp (P := P) (c := c) (n := n) (c'' := c') (n'' := n') (hk.trans hn) 0 0 0 x g.toLinearMap) hb (by omega) (by omega) hx (suppQ_of_JQ hk hn hg)`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Rewrite using `[← detQ ξ hk hn hg, unitV_eq ξ, unitV_eq ξ, reduction_leadingMinor h1.1 hb (by omega), reduction_leadingMinor hx.1 hb (by omega), h2, matrixExtendByZero_mul]`.

Use the proof step `ring) hg x`. Use `Eq.trans ?_ (h.trans ?_)` and prove the remaining obligations. Use `congr 1`. Conclude with `LastSteps.ite_eq_ite_zero Iff.rfl fun _ => rfl`. Use `congr 1`.

Conclude with `LastSteps.ite_eq_ite_zero Iff.rfl fun _ => rfl`.
-/
theorem phiQ_source {kj : ℕ} (hk : k₀ ≤ kj) (hn : kj ≤ n') (hr : r = kj + c') (hb : r ≤ n + c)
    {g : Sp E (n' + c') ≃ₗ[E] Sp E (n' + c')} (hg : g ∈ JQ P (qOf P) kj n' c') (x : HomE E (n' + c') (n + c)) :
    PhiQ (qOf P) ξ k₀ r c' n' c n (x ∘ₗ g.toLinearMap) * unitV ξ⁻¹ ((LinearEquiv.det g : Eˣ) : E) =
      lamQB ξ kj n' g.toLinearMap * PhiQ (qOf P) ξ k₀ r c' n' c n x := by
  subst hr
  have h := ite_law (JQ P (qOf P) kj n' c') (fun g (x : HomE E (n' + c') (n + c)) => x ∘ₗ g.toLinearMap) comp_inv
    (fun x => SuppQ P (kj + c') (n + c) (n' + c') (entB (qOf P) k₀ c' n' c n 0 0 x))
    (fun x => unitV ξ (dT (entB (qOf P) k₀ c' n' c n 0 0 x) (kj + c')))
    (fun g => unitV ξ⁻¹ ((LinearEquiv.det g : Eˣ) : E)) (fun g => lamQB ξ kj n' g.toLinearMap)
    (fun g hg x hx => by
      obtain ⟨h1, h2⟩ := SuppQ.mul (entB_comp (P := P) (c := c) (n := n) (c'' := c') (n'' := n') (hk.trans hn) 0 0 0 x
        g.toLinearMap) hb (by omega) (by omega) hx (suppQ_of_JQ hk hn hg)
      refine ⟨h1, ?_⟩
      rw [← detQ ξ hk hn hg, unitV_eq ξ, unitV_eq ξ, reduction_leadingMinor h1.1 hb (by omega), reduction_leadingMinor hx.1 hb (by omega), h2, matrixExtendByZero_mul]
      ring) hg x
  refine Eq.trans ?_ (h.trans ?_)
  · congr 1
    exact LastSteps.ite_eq_ite_zero Iff.rfl fun _ => rfl
  · congr 1
    exact LastSteps.ite_eq_ite_zero Iff.rfl fun _ => rfl

/- English proof (translation)
Substitute `hr` using the available equality. Establish `h` using `ite_law (JQ P (qOf P) kj n c) (fun g (x : HomE E (n' + c') (n + c)) => g.toLinearMap ∘ₗ x) inv_comp (fun x => SuppQ P (kj + c) (n + c) (n' + c') (entB (qOf P) k₀ c' n' c n 0 0 x)) (fun x => unitV ξ (dT (entB (qOf P) k₀ c' n' c n 0 0 x) (kj + c))) (fun g => unitV ξ⁻¹ ((LinearEquiv …`. Take `⟨h1, h2⟩` from `SuppQ.mul (entB_comp (P := P) (c := c) (n := n) (c'' := c') (n'' := n') (hk.trans hn) 0 0 0 g.toLinearMap x) (by omega) (by omega) ha (suppQ_of_JQ hk hn hg) hx`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Rewrite using `[← detQ ξ hk hn hg, unitV_eq ξ, unitV_eq ξ, reduction_leadingMinor h1.1 (by omega) ha, reduction_leadingMinor hx.1 (by omega) ha, h2, matrixExtendByZero_mul]`.

Use the proof step `ring) hg x`. Use `Eq.trans ?_ (h.trans ?_)` and prove the remaining obligations. Use `congr 1`. Conclude with `LastSteps.ite_eq_ite_zero Iff.rfl fun _ => rfl`. Use `congr 1`.

Conclude with `LastSteps.ite_eq_ite_zero Iff.rfl fun _ => rfl`.
-/
theorem phiQ_target {kj : ℕ} (hk : k₀ ≤ kj) (hn : kj ≤ n) (hr : r = kj + c) (ha : r ≤ n' + c')
    {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ JQ P (qOf P) kj n c) (x : HomE E (n' + c') (n + c)) :
    PhiQ (qOf P) ξ k₀ r c' n' c n (g.toLinearMap ∘ₗ x) * unitV ξ⁻¹ ((LinearEquiv.det g : Eˣ) : E) =
      lamQB ξ kj n g.toLinearMap * PhiQ (qOf P) ξ k₀ r c' n' c n x := by
  subst hr
  have h := ite_law (JQ P (qOf P) kj n c) (fun g (x : HomE E (n' + c') (n + c)) => g.toLinearMap ∘ₗ x) inv_comp
    (fun x => SuppQ P (kj + c) (n + c) (n' + c') (entB (qOf P) k₀ c' n' c n 0 0 x))
    (fun x => unitV ξ (dT (entB (qOf P) k₀ c' n' c n 0 0 x) (kj + c)))
    (fun g => unitV ξ⁻¹ ((LinearEquiv.det g : Eˣ) : E)) (fun g => lamQB ξ kj n g.toLinearMap)
    (fun g hg x hx => by
      obtain ⟨h1, h2⟩ := SuppQ.mul (entB_comp (P := P) (c := c) (n := n) (c'' := c') (n'' := n') (hk.trans hn) 0 0 0
        g.toLinearMap x) (by omega) (by omega) ha (suppQ_of_JQ hk hn hg) hx
      refine ⟨h1, ?_⟩
      rw [← detQ ξ hk hn hg, unitV_eq ξ, unitV_eq ξ, reduction_leadingMinor h1.1 (by omega) ha, reduction_leadingMinor hx.1 (by omega) ha, h2, matrixExtendByZero_mul]
      ring) hg x
  refine Eq.trans ?_ (h.trans ?_)
  · congr 1
    exact LastSteps.ite_eq_ite_zero Iff.rfl fun _ => rfl
  · congr 1
    exact LastSteps.ite_eq_ite_zero Iff.rfl fun _ => rfl

end Laws

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu))

/- English proof (translation)
Use `R.two_le_m` as an intermediate fact. Unfold `Ranks.N Ranks.r Ranks.rS cOf`. Rewrite using `[mul_add, mul_one]`. Use linear arithmetic over natural numbers and integers.
-/
theorem ranks (R : Ranks) {j : ℕ} (hj : j + 1 ≤ R.m) :
    R.N j + cOf R j = R.r + j * R.t ∧ R.k + j ≤ R.N j ∧ R.r = R.k + j + cOf R j ∧ R.k + R.rS < R.r := by
  have := R.two_le_m
  unfold Ranks.N Ranks.r Ranks.rS cOf
  rw [mul_add, mul_one]
  omega

/- English proof (translation)
Unfold `Jat at hg`. Use `split_ifs at hg`. Conclude with `LastSteps.isUnit_det_of_stab hg.1`. Conclude with `LastSteps.isUnit_det_of_stab hg.1`. Conclude with `LastSteps.isUnit_det_of_stab (stdAt_eq (E := X.E) (P := P) (n := R.N j) (c := cOf R j) ▸ hg.1)`.
-/
theorem isUnit_det {sharp : Bool} {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} {g : AutY X R j} (hg : g ∈ Jat (Pr := Pr) sharp j P) :
    IsUnit (redP P ((LinearEquiv.det g : X.Eˣ) : X.E)) := by
  unfold Jat at hg
  split_ifs at hg
  · exact LastSteps.isUnit_det_of_stab hg.1
  · exact LastSteps.isUnit_det_of_stab hg.1
  · exact LastSteps.isUnit_det_of_stab (stdAt_eq (E := X.E) (P := P) (n := R.N j) (c := cOf R j) ▸ hg.1)

/- English proof (translation)
Take `⟨a1, a2, a3, a4⟩` from `ranks R (j := i) (by omega)`. Take `⟨b1, b2, b3, -⟩` from `ranks R (j := i + 1) (by omega)`. Rewrite `b1` using `[add_mul, one_mul]`. Unfold `muAt`. Rewrite using `[LastSteps.locChar_unit _ _ (isUnit_det hg)]`.

Unfold `Jat at hg`. Unfold `PhiAt lamRow`. Use `split_ifs at hg ⊢`. Rewrite using `[phiGS_eq]`. Conclude with `phiM_source _ _ (by omega) (by omega) a1 (by omega) _ inf_le_left (fun g hg => levG_of_JGsym (by omega) a4 (by omega) hg) hg x`.

Rewrite using `[phiG_eq, lamGB, lamGv_eq]`. Conclude with `phiM_source _ _ (by omega) (by omega) a1 (by omega) _ inf_le_left (fun g hg => levG_of_JG (by omega) (by omega) hg) hg x`. Conclude with `phiQ_source _ (by omega) a2 a3 (by omega) hg x`.
-/
theorem phiAt_source (sharp : Bool) {i : ℕ} (hi : i + 2 ≤ R.m) (P : rowSG Pr sel mu) {g : AutY X R i}
    (hg : g ∈ Jat (Pr := Pr) sharp i P.1) (x : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))) :
    PhiAt Ch mu sharp i P.1 (x ∘ₗ g.toLinearMap) * muAt Ch sel mu cst i P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      lamRow Ch mu sharp i P.1 g.toLinearMap * PhiAt Ch mu sharp i P.1 x := by
  obtain ⟨a1, a2, a3, a4⟩ := ranks R (j := i) (by omega)
  obtain ⟨b1, b2, b3, -⟩ := ranks R (j := i + 1) (by omega)
  rw [add_mul, one_mul] at b1
  unfold muAt
  rw [LastSteps.locChar_unit _ _ (isUnit_det hg)]
  unfold Jat at hg
  unfold PhiAt lamRow
  split_ifs at hg ⊢
  · rw [phiGS_eq]
    exact phiM_source _ _ (by omega) (by omega) a1 (by omega) _ inf_le_left
      (fun g hg => levG_of_JGsym (by omega) a4 (by omega) hg) hg x
  · rw [phiG_eq, lamGB, lamGv_eq]
    exact phiM_source _ _ (by omega) (by omega) a1 (by omega) _ inf_le_left
      (fun g hg => levG_of_JG (by omega) (by omega) hg) hg x
  · exact phiQ_source _ (by omega) a2 a3 (by omega) hg x

/- English proof (translation)
Take `⟨a1, a2, a3, a4⟩` from `ranks R (j := i) (by omega)`. Take `⟨b1, b2, b3, -⟩` from `ranks R (j := i + 1) (by omega)`. Rewrite `b1` using `[add_mul, one_mul, ← add_assoc]`. Unfold `muAt`. Rewrite using `[LastSteps.locChar_unit _ _ (isUnit_det hg)]`.

Unfold `Jat at hg`. Unfold `PhiAt lamRow`. Use `split_ifs at hg ⊢`. Rewrite using `[phiGS_eq]`. Conclude with `phiM_target _ _ (by omega) (by omega) b1 _ inf_le_left (fun g hg => levG_of_JGsym (by omega) a4 (by omega) hg) hg x`.

Rewrite using `[phiG_eq, lamGB, lamGv_eq]`. Conclude with `phiM_target _ _ (by omega) (by omega) b1 _ inf_le_left (fun g hg => levG_of_JG (by omega) (by omega) hg) hg x`. Conclude with `phiQ_target _ (by omega) b2 b3 (by omega) hg x`.
-/
theorem phiAt_target (sharp : Bool) {i : ℕ} (hi : i + 2 ≤ R.m) (P : rowSG Pr sel mu) {g : AutY X R (i + 1)}
    (hg : g ∈ Jat (Pr := Pr) sharp (i + 1) P.1) (x : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))) :
    PhiAt Ch mu sharp i P.1 (g.toLinearMap ∘ₗ x) * muAt Ch sel mu cst i P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      lamRow Ch mu sharp (i + 1) P.1 g.toLinearMap * PhiAt Ch mu sharp i P.1 x := by
  obtain ⟨a1, a2, a3, a4⟩ := ranks R (j := i) (by omega)
  obtain ⟨b1, b2, b3, -⟩ := ranks R (j := i + 1) (by omega)
  rw [add_mul, one_mul, ← add_assoc] at b1
  unfold muAt
  rw [LastSteps.locChar_unit _ _ (isUnit_det hg)]
  unfold Jat at hg
  unfold PhiAt lamRow
  split_ifs at hg ⊢
  · rw [phiGS_eq]
    exact phiM_target _ _ (by omega) (by omega) b1 _ inf_le_left
      (fun g hg => levG_of_JGsym (by omega) a4 (by omega) hg) hg x
  · rw [phiG_eq, lamGB, lamGv_eq]
    exact phiM_target _ _ (by omega) (by omega) b1 _ inf_le_left
      (fun g hg => levG_of_JG (by omega) (by omega) hg) hg x
  · exact phiQ_target _ (by omega) b2 b3 (by omega) hg x

end Chain

end GlobalTheory.DatumLaw

end
