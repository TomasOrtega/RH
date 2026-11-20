import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesHasSumBoundFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomTiltMapTiltFrobeniusIntegerPowerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUntiltExtensionFinsetSumSubLeStatement

noncomputable section

open Formalism.Per GlobalTheory.PSer Finset
open scoped Formalism.Per

namespace GlobalTheory.PSer

/- English proof (translation)
Introduce `l _ F _ _ _ _ ι tsh hn hs hsurj h m x ϖ K τ r hh hϖ hx hT`. Establish `hid : ∀ j n, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) = sh (m j) * ((l : ℂ_[l]) ^ (-n) * sh (pw (n * h + ((r : ℕ) : ℤ)) (x j)))`. Introduce `j n`. Simplify using `only [GlobalTheory.PMonE.term, map_mul, map_zpow₀, hϖ, hs]`. Rewrite using `[← GlobalTheory.T.ringHom_tilt_map_tiltFrobeniusIntegerPower l F ι, hs]`.

Rewrite using `[show ((r : ℤ) + n * h) = n * h + ((r : ℕ) : ℤ) by push_cast; ring]`. Expand and normalize the polynomial expressions, which then agree. Establish `hR : 0 ≤ τ r` using `(norm_nonneg _).trans (hT r 0).1`. Establish `hR' : 0 ≤ ‖(l : ℂ_[l])‖ * τ r` using `mul_nonneg (norm_nonneg _) hR`. Establish `hlb : τ r / l = ‖(l : ℂ_[l])‖ * τ r` using `by rw [Laws.norm_l, div_eq_inv_mul]`.

Establish `htail : ∀ j, ‖sh (m j) * lam h r (x j) - ∑ n ∈ Icc (-(K : ℤ)) K, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n)‖ ≤ ‖(l : ℂ_[l])‖ * τ r`. Introduce `j`. Establish `hsum : Summable (fun n => tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n))`. Simplify using `only [hid]`. Conclude with `(Laws.summable_lam hh r (hx j)).mul_left _`.

Establish `hlam : sh (m j) * lam h r (x j) = ∑' n, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n)`. Simplify using `only [hid, lam]`. Rewrite using `[tsum_mul_left]`. Rewrite using `[hlam, ← hsum.sum_add_tsum_compl (s := Icc (-(K : ℤ)) K), add_sub_cancel_left]`. Use `IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hR' fun ⟨n, hmem⟩ => ?_` and prove the remaining obligations.

Rewrite using `[← hlb]`. Use `show ‖tsh _‖ ≤ _`. Rewrite using `[hn]`. Apply `(hT j n).2` to reduce the goal to its premises. Simplify using `only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] at hmem`.

Rewrite using `[lt_abs]`. Use linear arithmetic over natural numbers and integers. Establish `hfin : ‖∑ j, ∑ n ∈ Icc (-(K : ℤ)) K, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) - tsh (GlobalTheory.PMonE.rowT l ϖ (fun j => ι (m j)) K (fun j => ι (x j)) r)‖ ≤ ‖(l : ℂ_[l])‖ * τ r`. Use `GlobalTheory.T.norm_untilt_extension_finset_sum_sub_le l F ι tsh hn hs hsurj (Fin h × ℤ) (univ ×ˢ Icc (-(K : ℤ)) K) (fun a => GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r a.1 a.2) (τ r) hR (fun a _ => (hT a.1 a.2).1)` as an intermediate fact. Simplify using `only [Finset.sum_product] at this`.

Rewrite using `[norm_sub_rev]`. Simplify `this` using `[GlobalTheory.PMonE.rowT]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_sub_distrib]`. Use `congr 1`.

Normalize the expressions using the abelian group laws. Use `_ ≤ max _ _ := IsUltrametricDist.norm_add_le_max _ _`. Use `_ ≤ _ := max_le (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR' fun j _ => htail j) hfin`.
-/
theorem row_lam_sub_untilt_rowT : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CharP F l]
    [PerfectRing F l] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ (h : ℕ) (m x : Fin h → Fl l) (ϖ : F) (K : ℕ) (τ : Fin h → ℝ) (r : Fin h), 1 ≤ h → tsh ϖ = l →
      (∀ j, ‖sh (x j)‖ < 1) →
      (∀ (j : Fin h) (n : ℤ), ‖GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n‖ ≤ τ r ∧
        ((K : ℤ) < |n| → ‖GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n‖ ≤ τ r / l)) →
      ‖∑ j, sh (m j) * lam h r (x j) - tsh (GlobalTheory.PMonE.rowT l ϖ (fun j => ι (m j)) K (fun j => ι (x j)) r)‖
        ≤ ‖(l : ℂ_[l])‖ * τ r := by
  intro l _ F _ _ _ _ ι tsh hn hs hsurj h m x ϖ K τ r hh hϖ hx hT
  have hid : ∀ j n, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) =
      sh (m j) * ((l : ℂ_[l]) ^ (-n) * sh (pw (n * h + ((r : ℕ) : ℤ)) (x j))) := by
    intro j n
    simp only [GlobalTheory.PMonE.term, map_mul, map_zpow₀, hϖ, hs]
    rw [← GlobalTheory.T.ringHom_tilt_map_tiltFrobeniusIntegerPower l F ι, hs]
    rw [show ((r : ℤ) + n * h) = n * h + ((r : ℕ) : ℤ) by push_cast; ring]
    ring
  have hR : 0 ≤ τ r := (norm_nonneg _).trans (hT r 0).1
  have hR' : 0 ≤ ‖(l : ℂ_[l])‖ * τ r := mul_nonneg (norm_nonneg _) hR
  have hlb : τ r / l = ‖(l : ℂ_[l])‖ * τ r := by rw [Laws.norm_l, div_eq_inv_mul]
  have htail : ∀ j, ‖sh (m j) * lam h r (x j) -
      ∑ n ∈ Icc (-(K : ℤ)) K, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n)‖
        ≤ ‖(l : ℂ_[l])‖ * τ r := by
    intro j
    have hsum : Summable (fun n => tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n)) := by
      simp only [hid]; exact (Laws.summable_lam hh r (hx j)).mul_left _
    have hlam : sh (m j) * lam h r (x j) =
        ∑' n, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) := by
      simp only [hid, lam]; rw [tsum_mul_left]
    rw [hlam, ← hsum.sum_add_tsum_compl (s := Icc (-(K : ℤ)) K), add_sub_cancel_left]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hR' fun ⟨n, hmem⟩ => ?_
    rw [← hlb]
    show ‖tsh _‖ ≤ _
    rw [hn]
    apply (hT j n).2
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] at hmem
    rw [lt_abs]; omega
  have hfin : ‖∑ j, ∑ n ∈ Icc (-(K : ℤ)) K,
      tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) -
        tsh (GlobalTheory.PMonE.rowT l ϖ (fun j => ι (m j)) K (fun j => ι (x j)) r)‖ ≤ ‖(l : ℂ_[l])‖ * τ r := by
    have := GlobalTheory.T.norm_untilt_extension_finset_sum_sub_le l F ι tsh hn hs hsurj (Fin h × ℤ) (univ ×ˢ Icc (-(K : ℤ)) K)
      (fun a => GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r a.1 a.2) (τ r) hR
      (fun a _ => (hT a.1 a.2).1)
    simp only [Finset.sum_product] at this
    rw [norm_sub_rev]
    simpa [GlobalTheory.PMonE.rowT] using this
  calc _ = ‖∑ j, (sh (m j) * lam h r (x j) -
        ∑ n ∈ Icc (-(K : ℤ)) K, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n)) +
      (∑ j, ∑ n ∈ Icc (-(K : ℤ)) K,
        tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) -
        tsh (GlobalTheory.PMonE.rowT l ϖ (fun j => ι (m j)) K (fun j => ι (x j)) r))‖ := by
        rw [Finset.sum_sub_distrib]; congr 1; abel
    _ ≤ max _ _ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ _ := max_le (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR' fun j _ => htail j) hfin

end GlobalTheory.PSer

end
