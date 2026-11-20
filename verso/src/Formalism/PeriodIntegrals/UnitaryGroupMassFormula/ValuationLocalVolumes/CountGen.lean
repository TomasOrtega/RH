import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.CardAndAdd

noncomputable section

namespace PI.OmVe

open PI.VolStabSW Matrix

section gen

variable {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)

/- English proof (translation)
Establish `: Fintype K` using `Fintype.ofFinite K`. Establish `: Fintype k` using `Fintype.ofFinite k`. Use `set T0 := T.submatrix i₀.succAbove i₀.succAbove with hT0`. Establish `hu0 : IsUnit T0.det`. Establish `h1` using `det_corOne T i₀ hr (1 : K)`.

Rewrite `h1` using `[one_mul]`. Rewrite using `[← h1]`. Conclude with `hu`. Set `A : {Y : Fin a' → Fin M → K // ffGram σ J Y = T0} → k → ℕ` to `fun Y c => Nat.card {x : Fin M → K // (∀ j, ffH σ J (Y.1 j) x = 0) ∧ ffH σ J x x = ι c}`. Establish `hperp : ∀ Y : {Y : Fin a' → Fin M → K // ffGram σ J Y = T0}, Nat.card {x : Fin M → K // ∀ j, ffH σ J (Y.1 j) x = 0} = Nat.card K ^ (M - a')`.

Introduce `Y`. Establish `h1` using `card_perp σ J T0 hu0 Y.1 Y.2`. Establish `hK : 0 < Nat.card K` using `Nat.card_pos`. Establish `h2 : Nat.card K ^ M = Nat.card K ^ (M - a') * Nat.card K ^ a'`. Rewrite using `[← pow_add, Nat.sub_add_cancel haM]`.

Rewrite `h1` using `[h2]`. Conclude with `Nat.eq_of_mul_eq_mul_right (pow_pos hK _) h1`. Establish `hfib : ∀ Y : {Y : Fin a' → Fin M → K // ffGram σ J Y = T0}, Nat.card {x : Fin M → K // ∀ j, ffH σ J (Y.1 j) x = 0} = ∑ c, A Y c`. Introduce `Y`. Simplify using `only [A, Nat.card_eq_fintype_card, Fintype.card_subtype]`.

Rewrite using `[Finset.card_eq_sum_card_fiberwise (f := fun x => ffH σ J x x) (t := Finset.univ.image ι) (fun x _ => by`. Take `⟨c, hc'⟩` from `hrange x`. Conclude with `Finset.mem_image.2 ⟨c, Finset.mem_univ _, hc'.symm⟩)]`. Rewrite using `[Finset.sum_image (fun a _ b _ h => hι h)]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.filter_filter]`. Establish `htot : Nat.card {Y : Fin a' → Fin M → K // ffGram σ J Y = T0} * Nat.card K ^ (M - a') = ∑ c, ∑ Y, A Y c`. Rewrite using `[Finset.sum_comm, Nat.card_eq_fintype_card, ← smul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]`. Use `Finset.sum_congr rfl fun Y _ => ?_` and prove the remaining obligations. Rewrite using `[← hperp Y, hfib Y]`.

Establish `hcN : ∀ c, c ≠ 0 → ∑ Y, A Y c = N`. Introduce `c hc0`. Rewrite using `[← hN c hc0]`. Establish `h1` using `card_split σ J hσ hJ T i₀ hr hc (ι c) (fun _ => True)`. Simplify using `only [and_true] at h1`.

Rewrite using `[h1, Nat.card_sigma]`. Establish `h0 : ∑ Y, A Y 0 = Nat.card {X : Fin (a' + 1) → Fin M → K // ffGram σ J X = T ∧ LinearIndependent K X} + Nat.card {Y : Fin a' → Fin M → K // ffGram σ J Y = T0} * D`. Establish `hR` using `card_split σ J hσ hJ T i₀ hr hc 0 (fun x => ∀ c : K, c • x = 0 → c = 0)`. Simplify using `only [Matrix.single_zero, add_zero] at hR`. Establish `hLI : Nat.card {X : Fin (a' + 1) → Fin M → K // ffGram σ J X = T ∧ LinearIndependent K X} = Nat.card {X : Fin (a' + 1) → Fin M → K // ffGram σ J X = T ∧ ∀ c : K, c • X i₀ = 0 → c = 0}` using `Nat.card_congr (Equiv.subtypeEquivRight fun X => ⟨fun h => ⟨h.1, (indep_iff σ J i₀ hc hu X h.1).1 h.2⟩, fun h => ⟨h.1, (indep_iff σ J i₀ hc hu X h.1).2 h.2⟩⟩)`.

Establish `hD' : ∑ Y : {Y : Fin a' → Fin M → K // ffGram σ J Y = T0}, Nat.card {x : Fin M → K // (∀ j, ffH σ J (Y.1 j) x = 0) ∧ ffH σ J x x = 0 ∧ ¬ ∀ c : K, c • x = 0 → c = 0} = Nat.card {Y : Fin a' → Fin M → K // ffGram σ J Y = T0} * D`. Rewrite using `[Finset.sum_congr rfl (fun Y _ => hD Y.1 Y.2), Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]`. Rewrite using `[hLI, hR, Nat.card_sigma, ← hD', ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun Y _ => ?_` and prove the remaining obligations. Simplify using `only [A, hι0]`.

Establish `h2` using `card_and_add (fun x : Fin M → K => (∀ j, ffH σ J (Y.1 j) x = 0) ∧ ffH σ J x x = 0) (fun x => ∀ c : K, c • x = 0 → c = 0)`. Simplify using `only [and_assoc] at h2`. Conclude with `h2.symm`. Rewrite `htot` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : k)), Finset.sum_congr rfl (fun c hc0 => hcN c (Finset.ne_of_mem_erase hc0)), Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, smul_eq_mul, h0]`. Rewrite using `[htot, Nat.card_eq_fintype_card (α := k)]`.
-/
theorem count_gen [Finite K] (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) {a' : ℕ}
    (T : Matrix (Fin (a' + 1)) (Fin (a' + 1)) K) (i₀ : Fin (a' + 1)) (hr : ∀ j, T i₀ j = 0)
    (hc : ∀ j, T j i₀ = 0) (hu : IsUnit (T + Matrix.single i₀ i₀ 1).det) (haM : a' ≤ M)
    {k : Type} [Finite k] [Zero k] (ι : k → K) (hι : Function.Injective ι) (hι0 : ι 0 = 0)
    (hrange : ∀ x : Fin M → K, ∃ c, ffH σ J x x = ι c) (N D : ℕ)
    (hN : ∀ c, c ≠ 0 → Nat.card {X : Fin (a' + 1) → Fin M → K //
      ffGram σ J X = T + Matrix.single i₀ i₀ (ι c)} = N)
    (hD : ∀ Y : Fin a' → Fin M → K, ffGram σ J Y = T.submatrix i₀.succAbove i₀.succAbove →
      Nat.card {x : Fin M → K // (∀ j, ffH σ J (Y j) x = 0) ∧ ffH σ J x x = 0 ∧
        ¬ ∀ c : K, c • x = 0 → c = 0} = D) :
    Nat.card {X : Fin (a' + 1) → Fin M → K // ffGram σ J X = T ∧ LinearIndependent K X} +
      Nat.card {Y : Fin a' → Fin M → K // ffGram σ J Y = T.submatrix i₀.succAbove i₀.succAbove} * D +
      (Nat.card k - 1) * N =
    Nat.card {Y : Fin a' → Fin M → K // ffGram σ J Y = T.submatrix i₀.succAbove i₀.succAbove} *
      Nat.card K ^ (M - a') := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fintype k := Fintype.ofFinite k
  set T0 := T.submatrix i₀.succAbove i₀.succAbove with hT0
  have hu0 : IsUnit T0.det := by
    have h1 := det_corOne T i₀ hr (1 : K)
    rw [one_mul] at h1
    rw [← h1]
    exact hu
  let A : {Y : Fin a' → Fin M → K // ffGram σ J Y = T0} → k → ℕ := fun Y c =>
    Nat.card {x : Fin M → K // (∀ j, ffH σ J (Y.1 j) x = 0) ∧ ffH σ J x x = ι c}
  have hperp : ∀ Y : {Y : Fin a' → Fin M → K // ffGram σ J Y = T0},
      Nat.card {x : Fin M → K // ∀ j, ffH σ J (Y.1 j) x = 0} = Nat.card K ^ (M - a') := by
    intro Y
    have h1 := card_perp σ J T0 hu0 Y.1 Y.2
    have hK : 0 < Nat.card K := Nat.card_pos
    have h2 : Nat.card K ^ M = Nat.card K ^ (M - a') * Nat.card K ^ a' := by
      rw [← pow_add, Nat.sub_add_cancel haM]
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hK _) h1
  have hfib : ∀ Y : {Y : Fin a' → Fin M → K // ffGram σ J Y = T0},
      Nat.card {x : Fin M → K // ∀ j, ffH σ J (Y.1 j) x = 0} = ∑ c, A Y c := by
    intro Y
    simp only [A, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x => ffH σ J x x) (t := Finset.univ.image ι)
      (fun x _ => by
        obtain ⟨c, hc'⟩ := hrange x
        exact Finset.mem_image.2 ⟨c, Finset.mem_univ _, hc'.symm⟩)]
    rw [Finset.sum_image (fun a _ b _ h => hι h)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.filter_filter]
  have htot : Nat.card {Y : Fin a' → Fin M → K // ffGram σ J Y = T0} * Nat.card K ^ (M - a') =
      ∑ c, ∑ Y, A Y c := by
    rw [Finset.sum_comm, Nat.card_eq_fintype_card, ← smul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [← hperp Y, hfib Y]
  have hcN : ∀ c, c ≠ 0 → ∑ Y, A Y c = N := by
    intro c hc0
    rw [← hN c hc0]
    have h1 := card_split σ J hσ hJ T i₀ hr hc (ι c) (fun _ => True)
    simp only [and_true] at h1
    rw [h1, Nat.card_sigma]
  have h0 : ∑ Y, A Y 0 = Nat.card {X : Fin (a' + 1) → Fin M → K // ffGram σ J X = T ∧ LinearIndependent K X} +
      Nat.card {Y : Fin a' → Fin M → K // ffGram σ J Y = T0} * D := by
    have hR := card_split σ J hσ hJ T i₀ hr hc 0 (fun x => ∀ c : K, c • x = 0 → c = 0)
    simp only [Matrix.single_zero, add_zero] at hR
    have hLI : Nat.card {X : Fin (a' + 1) → Fin M → K // ffGram σ J X = T ∧ LinearIndependent K X} =
        Nat.card {X : Fin (a' + 1) → Fin M → K // ffGram σ J X = T ∧ ∀ c : K, c • X i₀ = 0 → c = 0} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun X =>
        ⟨fun h => ⟨h.1, (indep_iff σ J i₀ hc hu X h.1).1 h.2⟩,
          fun h => ⟨h.1, (indep_iff σ J i₀ hc hu X h.1).2 h.2⟩⟩)
    have hD' : ∑ Y : {Y : Fin a' → Fin M → K // ffGram σ J Y = T0},
        Nat.card {x : Fin M → K // (∀ j, ffH σ J (Y.1 j) x = 0) ∧ ffH σ J x x = 0 ∧
          ¬ ∀ c : K, c • x = 0 → c = 0} =
        Nat.card {Y : Fin a' → Fin M → K // ffGram σ J Y = T0} * D := by
      rw [Finset.sum_congr rfl (fun Y _ => hD Y.1 Y.2), Finset.sum_const, Finset.card_univ,
        smul_eq_mul, Nat.card_eq_fintype_card]
    rw [hLI, hR, Nat.card_sigma, ← hD', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun Y _ => ?_
    simp only [A, hι0]
    have h2 := card_and_add (fun x : Fin M → K => (∀ j, ffH σ J (Y.1 j) x = 0) ∧ ffH σ J x x = 0)
      (fun x => ∀ c : K, c • x = 0 → c = 0)
    simp only [and_assoc] at h2
    exact h2.symm
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : k)),
    Finset.sum_congr rfl (fun c hc0 => hcN c (Finset.ne_of_mem_erase hc0)), Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, smul_eq_mul, h0] at htot
  rw [htot, Nat.card_eq_fintype_card (α := k)]

end gen

end PI.OmVe
