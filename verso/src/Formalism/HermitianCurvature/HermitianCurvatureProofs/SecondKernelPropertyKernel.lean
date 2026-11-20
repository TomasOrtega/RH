import Formalism.HermitianCurvature.StatementA

namespace Formalism.FourierDecayAlt.P.LastBlockReversal

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp [Formalism.DoubleCosetMeasures.blk]`. Consider the case `cons a l ih`. Simplify using `only [List.cons_append, List.sum_cons, List.length_cons, Formalism.DoubleCosetMeasures.blk]`. Rewrite using `[if_neg (by omega), Nat.add_sub_cancel_left, ih]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem blk_last (l : List ℕ) : Formalism.DoubleCosetMeasures.blk (l ++ [1]) l.sum = l.length := by
  induction l with
  | nil => simp [Formalism.DoubleCosetMeasures.blk]
  | cons a l ih =>
    simp only [List.cons_append, List.sum_cons, List.length_cons, Formalism.DoubleCosetMeasures.blk]
    rw [if_neg (by omega), Nat.add_sub_cancel_left, ih]
    omega

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp [Formalism.DoubleCosetMeasures.revIn]`. Consider the case `cons a l ih`. Simplify using `only [List.cons_append, List.sum_cons, Formalism.DoubleCosetMeasures.revIn]`. Rewrite using `[if_neg (by omega), Nat.add_sub_cancel_left, ih]`.
-/
theorem revIn_last (l : List ℕ) : Formalism.DoubleCosetMeasures.revIn (l ++ [1]) l.sum = l.sum := by
  induction l with
  | nil => simp [Formalism.DoubleCosetMeasures.revIn]
  | cons a l ih =>
    simp only [List.cons_append, List.sum_cons, Formalism.DoubleCosetMeasures.revIn]
    rw [if_neg (by omega), Nat.add_sub_cancel_left, ih]

end Formalism.FourierDecayAlt.P.LastBlockReversal

namespace Formalism.FourierDecayAlt.P.LastBlockReversalIndices

open Formalism.DoubleCosetMeasures MeasureTheory

/- English proof (translation)
Establish `hU'` using `isUpUni_inv K hU`. Establish `hV'` using `isLowUni_inv K hV`. Establish `hlast : ∀ i : Fin n, i ≤ N` using `fun i => by`. Use `i.2` as an intermediate fact. Rewrite using `[Fin.le_def]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_apply, Finset.sum_eq_single N]`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single N]`. Rewrite using `[hU'.2 N, hV'.2 N, one_mul, mul_one]`. Introduce `j _ hj`.

Rewrite using `[hV'.1 (show OrderDual.toDual N < OrderDual.toDual j from (lt_of_le_of_ne (hlast j) hj : j < N)), mul_zero]`. Simplify using the standard rewrite rules. Introduce `i _ hi`. Rewrite using `[hU'.1 (lt_of_le_of_ne (hlast i) hi), zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem entry {K : Type} [CommRing K] {n : ℕ} (N : Fin n) (hN : N.val + 1 = n)
    (V W U : Matrix (Fin n) (Fin n) K) (hV : IsLowUni V) (hU : IsUpUni U) :
    (V * W * U)⁻¹ N N = W⁻¹ N N := by
  have hU' := isUpUni_inv K hU
  have hV' := isLowUni_inv K hV
  have hlast : ∀ i : Fin n, i ≤ N := fun i => by
    have := i.2
    rw [Fin.le_def]
    omega
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_apply, Finset.sum_eq_single N]
  · rw [Matrix.mul_apply, Finset.sum_eq_single N]
    · rw [hU'.2 N, hV'.2 N, one_mul, mul_one]
    · intro j _ hj
      rw [hV'.1 (show OrderDual.toDual N < OrderDual.toDual j from (lt_of_le_of_ne (hlast j) hj : j < N)),
        mul_zero]
    · simp
  · intro i _ hi
    rw [hU'.1 (lt_of_le_of_ne (hlast i) hi), zero_mul]
  · simp

/- English proof (translation)
Establish `hv : coeLin R (eLast R) = Pi.single N (1 : K)`. Use extensionality with `j`. Simplify using `only [coeLin, eLast, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Algebra.linearMap_apply, Pi.single_apply]`. Distinguish the cases in `h : j = N`. Substitute `h` using the available equality.

Simplify using `[hN]`. Establish `h' : ¬ (j.val + 1 = n)` using `fun e => h (Fin.ext (by omega))`. Simplify using `[h', h]`. Establish `hlc : ∀ v : Fin n → K, lastCoord R v = v N`. Introduce `v`.

Simplify using `only [lastCoord, LinearMap.sum_apply]`. Rewrite using `[Finset.sum_eq_single N]`. Simplify using `[hN]`. Introduce `j _ hj`. Establish `h' : ¬ (j.val + 1 = n)` using `fun e => hj (Fin.ext (by omega))`.

Simplify using `[h']`. Simplify using the standard rewrite rules. Simplify using `only [lamLin, LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, hv, hlc]`. Use `congr 1`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
theorem lam_last {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (N : Fin n) (hN : N.val + 1 = n)
    (Z : Matrix (Fin n) (Fin n) K) :
    lamLin R Z (eLast R) = Submodule.Quotient.mk (Z⁻¹ N N) := by
  have hv : coeLin R (eLast R) = Pi.single N (1 : K) := by
    ext j
    simp only [coeLin, eLast, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Algebra.linearMap_apply, Pi.single_apply]
    by_cases h : j = N
    · subst h
      simp [hN]
    · have h' : ¬ (j.val + 1 = n) := fun e => h (Fin.ext (by omega))
      simp [h', h]
  have hlc : ∀ v : Fin n → K, lastCoord R v = v N := by
    intro v
    simp only [lastCoord, LinearMap.sum_apply]
    rw [Finset.sum_eq_single N]
    · simp [hN]
    · intro j _ hj
      have h' : ¬ (j.val + 1 = n) := fun e => hj (Fin.ext (by omega))
      simp [h']
    · simp
  simp only [lamLin, LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.restrictScalars_apply,
    Matrix.mulVecLin_apply, hv, hlc]
  congr 1
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/- English proof (translation)
Introduce `K _ _ _ R l t ψ C _ _ e lam μ₁ μ₂ hB`. Choose the witnesses or unpack the hypotheses as in `⟨p, hp⟩ : ∃ p, phi R (l ++ [1]) t ψ C e lam p ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hB` to reduce the goal to its premises.

Unfold `BB`. Rewrite using `[show phi R (l ++ [1]) t ψ C e lam = fun _ => 0 from funext hcon]`. Simplify using the standard rewrite rules. Unfold `phi at hp`. Establish `h1` using `left_ne_zero_of_mul hp`.

Use `split_ifs at h1 with hI`. Establish `h2 : Nat.card (isoSet R ((((p.1 : GL (Fin (l ++ [1]).sum) K)) : Matrix (Fin (l ++ [1]).sum) (Fin (l ++ [1]).sum) K) * pt (l ++ [1]) t * ((p.2 : GL (Fin (l ++ [1]).sum) K) : Matrix (Fin (l ++ [1]).sum) (Fin (l ++ [1]).sum) K)) C e lam) ≠ 0` using `by exact_mod_cast h1`. Take `⟨⟨φ, hφ1, hφ2⟩⟩` from `(Nat.card_ne_zero.mp h2).1`. Establish `hN : ((⟨l.sum, by simp⟩ : Fin (l ++ [1]).sum) : ℕ) + 1 = (l ++ [1]).sum` using `by simp`. Apply the tactic sequence `rw [← hφ1, eZ, hφ2, lam_last R ⟨l.sum, by simp⟩ hN, entry _ hN _ _ _ p.1.2.1 p.2.2, hW K l t _ hN]`.

Conclude with `absurd rfl h1`.
-/
theorem a2one_of
    (hW : ∀ (K : Type) [CommRing K] (l : List ℕ) (t : ℕ → Kˣ) (N : Fin (l ++ [1]).sum),
      N.val + 1 = (l ++ [1]).sum → (pt (l ++ [1]) t)⁻¹ N N = (((t l.length)⁻¹ : Kˣ) : K)) :
    Formalism.FourierDecayAlt.A.LevelOneKernelPoint := by
  intro K _ _ _ R l t ψ C _ _ e lam μ₁ μ₂ hB
  obtain ⟨p, hp⟩ : ∃ p, phi R (l ++ [1]) t ψ C e lam p ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hB
    unfold BB
    rw [show phi R (l ++ [1]) t ψ C e lam = fun _ => 0 from funext hcon]
    simp
  unfold phi at hp
  have h1 := left_ne_zero_of_mul hp
  split_ifs at h1 with hI
  · have h2 : Nat.card (isoSet R ((((p.1 : GL (Fin (l ++ [1]).sum) K)) :
        Matrix (Fin (l ++ [1]).sum) (Fin (l ++ [1]).sum) K) * pt (l ++ [1]) t *
        ((p.2 : GL (Fin (l ++ [1]).sum) K) : Matrix (Fin (l ++ [1]).sum) (Fin (l ++ [1]).sum) K))
        C e lam) ≠ 0 := by exact_mod_cast h1
    obtain ⟨⟨φ, hφ1, hφ2⟩⟩ := (Nat.card_ne_zero.mp h2).1
    have hN : ((⟨l.sum, by simp⟩ : Fin (l ++ [1]).sum) : ℕ) + 1 = (l ++ [1]).sum := by simp
    rw [← hφ1, eZ, hφ2, lam_last R ⟨l.sum, by simp⟩ hN, entry _ hN _ _ _ p.1.2.1 p.2.2,
      hW K l t _ hN]
  · exact absurd rfl h1

end Formalism.FourierDecayAlt.P.LastBlockReversalIndices

namespace Formalism.FourierDecayAlt.P.ReversedIndexLastBlock

open Formalism.DoubleCosetMeasures

/- English proof (translation)
The claim follows from `| [], j, h => by simp at h | a :: s, j, h => by simp only [revIn] split_ifs with hj · simp; omega · have := revIn_lt s (j - a) (by simp at h; omega) simp; omega`.
-/
theorem revIn_lt : ∀ (s : List ℕ) (j : ℕ), j < s.sum → revIn s j < s.sum
  | [], j, h => by simp at h
  | a :: s, j, h => by
    simp only [revIn]
    split_ifs with hj
    · simp; omega
    · have := revIn_lt s (j - a) (by simp at h; omega)
      simp; omega

/- English proof (translation)
The claim follows from `| [], j, h => by simp at h | a :: s, j, h => by by_cases hj : j < a · have h2 : a - 1 - j < a := by omega simp only [revIn, hj, if_true, h2]; omega · have h2 : ¬ (a + revIn s (j - a) < a) := by omega simp only [revIn, hj, if_false, h2] rw [Nat.add_sub_cancel_left, revIn_revIn s ( …`.
-/
theorem revIn_revIn : ∀ (s : List ℕ) (j : ℕ), j < s.sum → revIn s (revIn s j) = j
  | [], j, h => by simp at h
  | a :: s, j, h => by
    by_cases hj : j < a
    · have h2 : a - 1 - j < a := by omega
      simp only [revIn, hj, if_true, h2]; omega
    · have h2 : ¬ (a + revIn s (j - a) < a) := by omega
      simp only [revIn, hj, if_false, h2]
      rw [Nat.add_sub_cancel_left, revIn_revIn s (j - a) (by simp at h; omega)]; omega

/- English proof (translation)
The claim follows from `| [], j, h => by simp at h | a :: s, j, h => by by_cases hj : j < a · have h2 : a - 1 - j < a := by omega simp only [revIn, blk, hj, if_true, h2] · have h2 : ¬ (a + revIn s (j - a) < a) := by omega simp only [revIn, blk, hj, if_false, h2] rw [Nat.add_sub_cancel_left, blk_revIn s …`.
-/
theorem blk_revIn : ∀ (s : List ℕ) (j : ℕ), j < s.sum → blk s (revIn s j) = blk s j
  | [], j, h => by simp at h
  | a :: s, j, h => by
    by_cases hj : j < a
    · have h2 : a - 1 - j < a := by omega
      simp only [revIn, blk, hj, if_true, h2]
    · have h2 : ¬ (a + revIn s (j - a) < a) := by omega
      simp only [revIn, blk, hj, if_false, h2]
      rw [Nat.add_sub_cancel_left, blk_revIn s (j - a) (by simp at h; omega)]

/- English proof (translation)
Use extensionality with `a c`. Simplify using `only [Matrix.mul_apply, pt]`. Rewrite using `[Finset.sum_eq_single ⟨revIn s a, revIn_lt s a a.2⟩]`. Rewrite using `[if_pos rfl]`. Simplify using `only [Fin.val_mk]`.

Rewrite using `[revIn_revIn s a a.2, blk_revIn s a a.2, Matrix.one_apply]`. Distinguish the cases in `h : c = a`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Establish `h' : (c : ℕ) ≠ a` using `fun e => h (Fin.ext e)`.

Simplify using `[h', Ne.symm h]`. Introduce `b _ hb`. Rewrite using `[if_neg, zero_mul]`. Introduce `e`. Conclude with `hb (Fin.ext e)`.

Simplify using the standard rewrite rules.
-/
theorem pt_mul {K : Type} [CommRing K] (s : List ℕ) (t : ℕ → Kˣ) :
    pt s t * pt s (fun b => (t b)⁻¹) = (1 : Matrix (Fin s.sum) (Fin s.sum) K) := by
  ext a c
  simp only [Matrix.mul_apply, pt]
  rw [Finset.sum_eq_single ⟨revIn s a, revIn_lt s a a.2⟩]
  · rw [if_pos rfl]
    simp only [Fin.val_mk]
    rw [revIn_revIn s a a.2, blk_revIn s a a.2, Matrix.one_apply]
    by_cases h : c = a
    · subst h
      simp
    · have h' : (c : ℕ) ≠ a := fun e => h (Fin.ext e)
      simp [h', Ne.symm h]
  · intro b _ hb
    rw [if_neg, zero_mul]
    intro e
    exact hb (Fin.ext e)
  · simp

/- English proof (translation)
Rewrite using `[Matrix.inv_eq_right_inv (pt_mul _ t)]`. Establish `hN' : (N : ℕ) = l.sum`. Simplify using `at hN`. Use linear arithmetic over natural numbers and integers. Simplify using `only [pt]`.

Rewrite using `[hN', Formalism.FourierDecayAlt.P.LastBlockReversal.revIn_last, if_pos rfl, Formalism.FourierDecayAlt.P.LastBlockReversal.blk_last]`.
-/
theorem pt_inv_last {K : Type} [CommRing K] (l : List ℕ) (t : ℕ → Kˣ) (N : Fin (l ++ [1]).sum)
    (hN : N.val + 1 = (l ++ [1]).sum) : (pt (l ++ [1]) t)⁻¹ N N = (((t l.length)⁻¹ : Kˣ) : K) := by
  rw [Matrix.inv_eq_right_inv (pt_mul _ t)]
  have hN' : (N : ℕ) = l.sum := by
    simp at hN
    omega
  simp only [pt]
  rw [hN', Formalism.FourierDecayAlt.P.LastBlockReversal.revIn_last, if_pos rfl, Formalism.FourierDecayAlt.P.LastBlockReversal.blk_last]

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.LastBlockReversalIndices.a2one_of (fun _ _ l t N hN => pt_inv_last l t N hN)`.
-/
theorem a2one : Formalism.FourierDecayAlt.A.LevelOneKernelPoint :=
  Formalism.FourierDecayAlt.P.LastBlockReversalIndices.a2one_of (fun _ _ l t N hN => pt_inv_last l t N hN)

/- English proof (translation)
Introduce `K _ _ _ R l l' t t' ψ C _ _ e lam m1 m2 m3 m4 h1 h2`. Establish `e1` using `a2one K R l t ψ C e lam m1 m2 h1`. Establish `e2` using `a2one K R l' t' ψ C e lam m3 m4 h2`. Establish `h3` using `e1.symm.trans e2`. Rewrite `h3` using `[Submodule.Quotient.eq]`.

Take `⟨r, hr⟩` from `LinearMap.mem_range.mp h3`. Rewrite using `[← hr]`. Conclude with `r.2`.
-/
theorem a2oneKernel : Formalism.FourierDecayAlt.A.LevelOneKernelPair := by
  intro K _ _ _ R l l' t t' ψ C _ _ e lam m1 m2 m3 m4 h1 h2
  have e1 := a2one K R l t ψ C e lam m1 m2 h1
  have e2 := a2one K R l' t' ψ C e lam m3 m4 h2
  have h3 := e1.symm.trans e2
  rw [Submodule.Quotient.eq] at h3
  obtain ⟨r, hr⟩ := LinearMap.mem_range.mp h3
  rw [← hr]
  exact r.2

end Formalism.FourierDecayAlt.P.ReversedIndexLastBlock

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.ReversedIndexLastBlock.a2one`.
-/
theorem Formalism.FourierDecayAlt.P.second_kernel_property_one : Formalism.FourierDecayAlt.A.LevelOneKernelPoint := Formalism.FourierDecayAlt.P.ReversedIndexLastBlock.a2one
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.ReversedIndexLastBlock.a2oneKernel`.
-/
theorem Formalism.FourierDecayAlt.P.second_kernel_property_kernel : Formalism.FourierDecayAlt.A.LevelOneKernelPair :=
  Formalism.FourierDecayAlt.P.ReversedIndexLastBlock.a2oneKernel
