import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IterateOnePlusCasOfEq
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.TypeSum

open GlobalTheory.LowTypeDetermined

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil`. Use `⟨(smooth (Jm ε) σ).zero_mem, ?_⟩` and prove the remaining obligations. Establish `h` using `Dw_smul hσ hl (0 : ℂ) hv`. Simplify using `using h`.

Consider the case `cons u L ih`. Establish `hu : Sm ε σ (Dw σ u.2 v)` using `hv.word hσ (hL u List.mem_cons_self)`. Take `⟨ih1, ih2⟩` from `ih fun w hw => hL w (List.mem_cons_of_mem _ hw)`. Establish `hs : Sm ε σ (u.1 • Dw σ u.2 v)` using `(smooth (Jm ε) σ).smul_mem u.1 hu`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [List.map_cons, List.sum_cons]`. Conclude with `(smooth (Jm ε) σ).add_mem hs ih1`. Simplify using `only [List.map_cons, List.sum_cons]`. Rewrite using `[Dw_add hσ hl hs ih1, Dw_smul hσ hl u.1 hu, ← Dw_append, ih2]`.
-/
theorem Dw_comb (hσ : IsURepOn (UJset ε) σ) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) {v : H}
    (hv : Sm ε σ v) (L : List (ℂ × List (Mx n))) (hL : ∀ u ∈ L, ∀ Y ∈ u.2, Y ∈ lieSet ε) :
    Sm ε σ ((L.map fun u => u.1 • Dw σ u.2 v).sum) ∧
      Dw σ l ((L.map fun u => u.1 • Dw σ u.2 v).sum) = (L.map fun u => u.1 • Dw σ (l ++ u.2) v).sum := by
  induction L with
  | nil =>
    refine ⟨(smooth (Jm ε) σ).zero_mem, ?_⟩
    have h := Dw_smul hσ hl (0 : ℂ) hv
    simpa using h
  | cons u L ih =>
    have hu : Sm ε σ (Dw σ u.2 v) := hv.word hσ (hL u List.mem_cons_self)
    obtain ⟨ih1, ih2⟩ := ih fun w hw => hL w (List.mem_cons_of_mem _ hw)
    have hs : Sm ε σ (u.1 • Dw σ u.2 v) := (smooth (Jm ε) σ).smul_mem u.1 hu
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons]
      exact (smooth (Jm ε) σ).add_mem hs ih1
    · simp only [List.map_cons, List.sum_cons]
      rw [Dw_add hσ hl hs ih1, Dw_smul hσ hl u.1 hu, ← Dw_append, ih2]

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simp`. Consider the case `cons u L ih`. Simplify using `only [List.map_cons, List.sum_cons, neg_smul, neg_add] at *`. Rewrite using `[ih]`.
-/
theorem sum_neg_comb (L : List (ℂ × List (Mx n))) (f : List (Mx n) → H) :
    (L.map fun u => (-u.1) • f u.2).sum = -(L.map fun u => u.1 • f u.2).sum := by
  induction L with
  | nil => simp
  | cons u L ih =>
    simp only [List.map_cons, List.sum_cons, neg_smul, neg_add] at *
    rw [ih]

/- English proof (translation)
Simplify using `[List.map_map, Function.comp_def]`.
-/
theorem sum_norm_neg (L : List (ℂ × List (Mx n))) (f : List (Mx n) → List (Mx n)) :
    ((L.map fun u => ((-u.1, f u.2) : ℂ × List (Mx n))).map fun u => ‖u.1‖).sum = (L.map fun u => ‖u.1‖).sum := by
  simp [List.map_map, Function.comp_def]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons a l ih => simp [List.flatMap_cons, ih]`.
-/
theorem sum_flatMap' {α M : Type} [AddCommMonoid M] (l : List α) (f : α → List M) :
    (l.flatMap f).sum = (l.map fun i => (f i).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

/- English proof (translation)
Introduce `n ε H _ _ σ hσ d X hX r`. Proceed by induction on `r with`. Consider the case `zero`. Use `⟨[(1, [])], ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Introduce `v _`. Simplify using the standard rewrite rules. Consider the case `succ r ih`. Take `⟨L, hL1, hL2, hL3⟩` from `ih`.

Establish `hLie : ∀ u ∈ L, ∀ Y ∈ u.2, Y ∈ lieSet ε` using `fun u hu Y hY => by`. Take `⟨i, rfl⟩` from `(hL1 u hu).2 Y hY`. Conclude with `hX i`. Set `M : Fin d → List (ℂ × List (Mx n))` to `fun i => L.map fun u => (-u.1, X i :: X i :: u.2)`. Use `⟨L ++ (List.finRange d).flatMap M, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `u hu`. Break down `List.mem_append.1 hu with hu | hu` into its components or cases. Conclude with `⟨(hL1 u hu).1.trans (by omega), (hL1 u hu).2⟩`. Take `⟨i, -, hu⟩` from `List.mem_flatMap.1 hu`. Take `⟨w, hw, rfl⟩` from `List.mem_map.1 hu`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [List.length_cons]`. Use `(hL1 w hw).1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce `Y hY`.

Simplify using `only [List.mem_cons] at hY`. Break down `hY with rfl | rfl | hY` into its components or cases. Conclude with `⟨i, rfl⟩`. Conclude with `⟨i, rfl⟩`. Conclude with `(hL1 w hw).2 Y hY`.

Establish `hM : ∀ i, ((M i).map fun u => ‖u.1‖).sum = (L.map fun u => ‖u.1‖).sum` using `fun i => sum_norm_neg L (fun l => X i :: X i :: l)`. Rewrite using `[List.map_append, List.sum_append, List.map_flatMap, sum_flatMap']`. Simplify using `only [hM, List.map_const', List.sum_replicate, List.length_finRange, nsmul_eq_mul]`. Establish `h0 : 0 ≤ (L.map fun u => ‖u.1‖).sum` using `List.sum_nonneg fun x hx => by`. Take `⟨u, -, rfl⟩` from `List.mem_map.1 hx`.

Conclude with `norm_nonneg _`. Rewrite using `[pow_succ]`. Use polynomial arithmetic with `[pow_nonneg (by positivity : (0:ℝ) ≤ 1 + d) r]`. Introduce `v hv`. Establish `hi : ∀ i, dRep σ (X i) (dRep σ (X i) (L.map fun u => u.1 • Dw σ u.2 v).sum) = (L.map fun u => u.1 • Dw σ (X i :: X i :: u.2) v).sum` using `fun i => (Dw_comb hσ (l := [X i, X i]) (by simp [hX i]) hv L hLie).2`.

Establish `hMi : ∀ i, ((M i).map fun u => u.1 • Dw σ u.2 v).sum = -(L.map fun u => u.1 • Dw σ (X i :: X i :: u.2) v).sum` using `fun i => by`. Rewrite using `[← sum_neg_comb L (fun l => Dw σ (X i :: X i :: l) v)]`. Simplify using `[M, List.map_map, Function.comp_def]`. Rewrite using `[Function.iterate_succ_apply', hL3 v hv, onePlusCas]`. Simplify using `only [hi]`.

Rewrite using `[List.map_append, List.sum_append, List.map_flatMap, sum_flatMap', ← Fin.sum_univ_def]`. Simplify using `only [hMi, Finset.sum_neg_distrib, sub_eq_add_neg]`.
-/
theorem caspow_expand : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → ∀ (d : ℕ) (X : Fin d → Mx n), (∀ i, X i ∈ lieSet ε) →
    ∀ r : ℕ, ∃ L : List (ℂ × List (Mx n)), (∀ u ∈ L, u.2.length ≤ 2 * r ∧ ∀ Y ∈ u.2, ∃ i, X i = Y) ∧
      (L.map fun u => ‖u.1‖).sum ≤ (1 + (d : ℝ)) ^ r ∧
      ∀ v, Sm ε σ v → (onePlusCas σ X)^[r] v = (L.map fun u => u.1 • Dw σ u.2 v).sum := by
  intro n ε H _ _ σ hσ d X hX r
  induction r with
  | zero =>
    refine ⟨[(1, [])], ?_, ?_, ?_⟩
    · simp
    · simp
    · intro v _; simp
  | succ r ih =>
    obtain ⟨L, hL1, hL2, hL3⟩ := ih
    have hLie : ∀ u ∈ L, ∀ Y ∈ u.2, Y ∈ lieSet ε := fun u hu Y hY => by
      obtain ⟨i, rfl⟩ := (hL1 u hu).2 Y hY
      exact hX i
    let M : Fin d → List (ℂ × List (Mx n)) := fun i => L.map fun u => (-u.1, X i :: X i :: u.2)
    refine ⟨L ++ (List.finRange d).flatMap M, ?_, ?_, ?_⟩
    · intro u hu
      rcases List.mem_append.1 hu with hu | hu
      · exact ⟨(hL1 u hu).1.trans (by omega), (hL1 u hu).2⟩
      · obtain ⟨i, -, hu⟩ := List.mem_flatMap.1 hu
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hu
        refine ⟨?_, ?_⟩
        · simp only [List.length_cons]; have := (hL1 w hw).1; omega
        · intro Y hY
          simp only [List.mem_cons] at hY
          rcases hY with rfl | rfl | hY
          · exact ⟨i, rfl⟩
          · exact ⟨i, rfl⟩
          · exact (hL1 w hw).2 Y hY
    · have hM : ∀ i, ((M i).map fun u => ‖u.1‖).sum = (L.map fun u => ‖u.1‖).sum := fun i => sum_norm_neg L (fun l => X i :: X i :: l)
      rw [List.map_append, List.sum_append, List.map_flatMap, sum_flatMap']
      simp only [hM, List.map_const', List.sum_replicate, List.length_finRange, nsmul_eq_mul]
      have h0 : 0 ≤ (L.map fun u => ‖u.1‖).sum := List.sum_nonneg fun x hx => by
        obtain ⟨u, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
      rw [pow_succ]
      nlinarith [pow_nonneg (by positivity : (0:ℝ) ≤ 1 + d) r]
    · intro v hv
      have hi : ∀ i, dRep σ (X i) (dRep σ (X i) (L.map fun u => u.1 • Dw σ u.2 v).sum) =
          (L.map fun u => u.1 • Dw σ (X i :: X i :: u.2) v).sum := fun i =>
        (Dw_comb hσ (l := [X i, X i]) (by simp [hX i]) hv L hLie).2
      have hMi : ∀ i, ((M i).map fun u => u.1 • Dw σ u.2 v).sum =
          -(L.map fun u => u.1 • Dw σ (X i :: X i :: u.2) v).sum := fun i => by
        rw [← sum_neg_comb L (fun l => Dw σ (X i :: X i :: l) v)]
        simp [M, List.map_map, Function.comp_def]
      rw [Function.iterate_succ_apply', hL3 v hv, onePlusCas]
      simp only [hi]
      rw [List.map_append, List.sum_append, List.map_flatMap, sum_flatMap', ← Fin.sum_univ_def]
      simp only [hMi, Finset.sum_neg_distrib, sub_eq_add_neg]

end GlobalTheory.TypeSum
