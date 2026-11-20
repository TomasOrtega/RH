import Mathlib
import Formalism.PeriodIntegrals.RowWtSpan

open MvPolynomial

noncomputable section

namespace PI.RWS

open PI.RW

def rowW {k : ℕ} (a : Fin k) : Fin k × Fin k → ℕ := fun v => if v.1 = a then 1 else 0

/- English proof (translation)
Establish `h'` using `h.sum_weight_X_mul_pderiv`. Unfold `RE`. Rewrite using `[Nat.cast_smul_eq_nsmul K d f, ← h']`. Use `symm`. Rewrite using `[Fintype.sum_prod_type, Finset.sum_eq_single a (fun x _ hx => by simp [rowW, hx]) (fun h => absurd (Finset.mem_univ a) h)]`.

Simplify using `[rowW]`.
-/
theorem RE_eq_of_hom {K : Type} [CommRing K] {k : ℕ} (a : Fin k)
    (f : MvPolynomial (Fin k × Fin k) K) (d : ℕ)
    (h : IsWeightedHomogeneous (rowW a) f d) : RE K k a a f = (d : K) • f := by
  have h' := h.sum_weight_X_mul_pderiv
  unfold RE
  rw [Nat.cast_smul_eq_nsmul K d f, ← h']
  symm
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a (fun x _ hx => by simp [rowW, hx])
    (fun h => absurd (Finset.mem_univ a) h)]
  simp [rowW]

/- English proof (translation)
Unfold `initMinor`. Rewrite using `[Matrix.det_apply]`. Use `IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_` and prove the remaining obligations. Establish `hp` using `IsWeightedHomogeneous.prod Finset.univ (fun i => (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin k × Fin k) K)) (fun i => rowW a (I (σ i), Fin.castLE hs i)) (w := rowW a) (fun i _ => isWeightedHomogeneous_X K (rowW a) _)`. Establish `hdeg : ∑ i, rowW a (I (σ i), Fin.castLE hs i) = (Finset.univ.filter fun p => I p = a).card`.

Simplify using `only [rowW]`. Rewrite using `[Finset.card_filter]`. Conclude with `Equiv.sum_comp σ (fun p => if I p = a then 1 else 0)`. Rewrite `hp` using `[hdeg]`. Rewrite `*` using `[Units.smul_def, ← mem_weightedHomogeneousSubmodule]`.

Conclude with `zsmul_mem hp _`.
-/
theorem minor_hom {K : Type} [CommRing K] {k s : ℕ} (a : Fin k) (I : Fin s → Fin k) (hs : s ≤ k) :
    IsWeightedHomogeneous (rowW a) (initMinor K I hs)
      (Finset.univ.filter fun p => I p = a).card := by
  unfold initMinor
  rw [Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  have hp := IsWeightedHomogeneous.prod Finset.univ
    (fun i => (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin k × Fin k) K))
    (fun i => rowW a (I (σ i), Fin.castLE hs i)) (w := rowW a)
    (fun i _ => isWeightedHomogeneous_X K (rowW a) _)
  have hdeg : ∑ i, rowW a (I (σ i), Fin.castLE hs i) =
      (Finset.univ.filter fun p => I p = a).card := by
    simp only [rowW]
    rw [Finset.card_filter]
    exact Equiv.sum_comp σ (fun p => if I p = a then 1 else 0)
  rw [hdeg] at hp
  rw [Units.smul_def, ← mem_weightedHomogeneousSubmodule] at *
  exact zsmul_mem hp _

/- English proof (translation)
Unfold `bideterminant`. Conclude with `IsWeightedHomogeneous.prod _ _ _ fun j _ => minor_hom a (I j) (hsz j)`.
-/
theorem bidet_hom {K : Type} [CommRing K] {k N : ℕ} (a : Fin k) (sz : Fin N → ℕ)
    (hsz : ∀ j, sz j ≤ k) (I : ∀ j, Fin (sz j) → Fin k) :
    IsWeightedHomogeneous (rowW a) (bideterminant K sz hsz I)
      (∑ j, (Finset.univ.filter fun p => I j p = a).card) := by
  unfold bideterminant
  exact IsWeightedHomogeneous.prod _ _ _ fun j _ => minor_hom a (I j) (hsz j)

/- English proof (translation)
Unfold `shapeDeg`. Rewrite using `[ht0, Finset.card_filter]`. Use `Finset.sum_le_sum fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : 0 < sz j`. Rewrite using `[if_pos hj]`.

Use `Finset.card_le_one.2 fun p hp q hq => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq`. Conclude with `(hI j).injective (hp.trans hq.symm)`. Rewrite using `[if_neg hj]`. Establish `hem : (Finset.univ : Finset (Fin (sz j))) = ∅` using `Finset.univ_eq_empty_iff.2 ⟨fun p => hj (lt_of_le_of_lt (Nat.zero_le _) p.2)⟩`.

Rewrite using `[hem]`. Simplify using the standard rewrite rules.
-/
theorem wt_le {k N : ℕ} (sz : Fin N → ℕ) (I : ∀ j, Fin (sz j) → Fin k)
    (hI : ∀ j, StrictMono (I j)) (a t0 : Fin k) (ht0 : t0.val = 0) :
    ∑ j, (Finset.univ.filter fun p => I j p = a).card ≤ shapeDeg sz t0 := by
  unfold shapeDeg
  rw [ht0, Finset.card_filter]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : 0 < sz j
  · rw [if_pos hj]
    refine Finset.card_le_one.2 fun p hp q hq => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    exact (hI j).injective (hp.trans hq.symm)
  · rw [if_neg hj]
    have hem : (Finset.univ : Finset (Fin (sz j))) = ∅ :=
      Finset.univ_eq_empty_iff.2 ⟨fun p => hj (lt_of_le_of_lt (Nat.zero_le _) p.2)⟩
    rw [hem]
    simp

def Data (m : ℕ) (ν : Fin (m + 1) → ℕ) : Type :=
  {d : Σ N : ℕ, Σ sz : Fin N → ℕ, ∀ j, Fin (sz j) → Fin (m + 1) //
    (∀ j, d.2.1 j ≤ m + 1) ∧ shapeDeg d.2.1 = ν ∧ ∀ j, StrictMono (d.2.2 j)}

/- English proof (translation)
Introduce `K _ m ν _`. Use `⟨{d : Σ N : ℕ, Σ sz : Fin N → ℕ, ∀ j, Fin (sz j) → Fin (m + 1) // (∀ j, d.2.1 j ≤ m + 1) ∧ shapeDeg d.2.1 = ν ∧ ∀ j, StrictMono (d.2.2 j)}, fun d => bideterminant K d.1.2.1 d.2.1 d.1.2.2, fun d a => ∑ j, (Finset.univ.filter fun p => d.1.2.2 j p = a).card, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨⟨⟨N, sz, I⟩, hsz, hsh, hmono⟩, rfl⟩`.

Substitute `hsh` using the available equality. Conclude with `h1 K (m + 1) (m + 1) N sz hsz I`. Use `le_trans (h2 K (m + 1) (m + 1) ν) (Submodule.span_mono ?_)` and prove the remaining obligations. Introduce and unpack `f ⟨N, sz, hsz, I, hsh, hmono, rfl⟩`. Conclude with `⟨⟨⟨N, sz, I⟩, hsz, hsh, hmono⟩, rfl⟩`.

Introduce and unpack `⟨⟨N, sz, I⟩, hsz, hsh, hmono⟩ a`. Conclude with `RE_eq_of_hom a _ _ (bidet_hom a sz hsz I)`. Introduce and unpack `⟨⟨N, sz, I⟩, hsz, hsh, hmono⟩ a`. Establish `hw` using `wt_le sz I hmono a 0 rfl`. Rewrite `hw` using `[hsh]`.

Conclude with `hw`.
-/
theorem rowWtSpan_of_bideterminant (h1 : BideterminantMem) (h2 : BideterminantSpan) : PI.RowWtSpan := by
  intro K _ m ν _
  refine ⟨{d : Σ N : ℕ, Σ sz : Fin N → ℕ, ∀ j, Fin (sz j) → Fin (m + 1) //
      (∀ j, d.2.1 j ≤ m + 1) ∧ shapeDeg d.2.1 = ν ∧ ∀ j, StrictMono (d.2.2 j)},
    fun d => bideterminant K d.1.2.1 d.2.1 d.1.2.2,
    fun d a => ∑ j, (Finset.univ.filter fun p => d.1.2.2 j p = a).card, ?_, ?_, ?_⟩
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨⟨⟨N, sz, I⟩, hsz, hsh, hmono⟩, rfl⟩
      subst hsh
      exact h1 K (m + 1) (m + 1) N sz hsz I
    · refine le_trans (h2 K (m + 1) (m + 1) ν) (Submodule.span_mono ?_)
      rintro f ⟨N, sz, hsz, I, hsh, hmono, rfl⟩
      exact ⟨⟨⟨N, sz, I⟩, hsz, hsh, hmono⟩, rfl⟩
  · rintro ⟨⟨N, sz, I⟩, hsz, hsh, hmono⟩ a
    exact RE_eq_of_hom a _ _ (bidet_hom a sz hsz I)
  · rintro ⟨⟨N, sz, I⟩, hsz, hsh, hmono⟩ a
    have hw := wt_le sz I hmono a 0 rfl
    rw [hsh] at hw
    exact hw

end PI.RWS
