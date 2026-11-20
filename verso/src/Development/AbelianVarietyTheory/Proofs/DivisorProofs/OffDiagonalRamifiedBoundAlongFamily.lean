import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamifiedTau1NeRamifiedTau2

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.RamifiedOffD

open Formalism.MainNotions.G GlobalTheory.HCEntries GlobalTheory.FockDegreeGap GlobalTheory.RamifiedLoss

variable {D : D7} {L : SizeData₂ D}

/- English proof (translation)
Introduce `j hj`. Establish `hp : D.host.d.Prime` using `D.host.hyp.2.1`. Establish `hb` using `one_le_b L`. Establish `hL` using `one_le_scL L`. Establish `hn` using `one_le_n D`.

Establish `hf : (1 : ℝ) ≤ D.R.f` using `by linarith [f_eq D, one_le_n D]`. Establish `hm : (1 : ℝ) ≤ D.R.m` using `by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)`. Establish `hE` using `abs_EatD_le h P hx j hj`. Establish `hlog : Real.log D.host.d ≤ L.sc.L`. Take `⟨-, -, -, -, -, -, hQ, -⟩` from `h`.

Use `hQ.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le ?_)` and prove the remaining obligations. Unfold `szTh`. Combine the linear relations using `[L.sc.eps_pos]`. Establish `hlog0 : 0 ≤ Real.log (D.host.d : ℝ)` using `Real.log_natCast_nonneg _`. Establish `hE2 : |EatD D j| ≤ 2 * ((D.R.f : ℝ) * L.sc.b)`.

Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hS, -⟩` from `h`. Establish `a1 : (D.host.TT.card : ℝ) ≤ D.R.n`. Rewrite using `[← card_HH]`. Conclude with `Finset.card_le_univ _` after adjusting the coercions. Establish `a2 : (D.host.TT.card : ℝ) * L.sc.b ≤ D.R.f * L.sc.b` using `mul_le_mul_of_nonneg_right (by linarith [f_eq D]) (by linarith)`.

Establish `a3 : (D.R.f : ℝ) * (D.R.k * L.sc.b') ≤ D.R.f * L.sc.b` using `mul_le_mul_of_nonneg_left (k_b'_le hS) (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hB : L.B0 = D.R.f * D.R.m * L.sc.b * L.sc.L` using `rfl`. Establish `hB1 : D.R.f * L.sc.b * L.sc.L ≤ L.B0`. Rewrite using `[hB, show (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L = D.R.m * (D.R.f * L.sc.b * L.sc.L) by ring]`.

Conclude with `le_mul_of_one_le_left (by positivity) hm`. Establish `h1 : Real.log (D.host.d : ℝ) * |EatD D j| ≤ L.sc.L * (2 * ((D.R.f : ℝ) * L.sc.b))` using `mul_le_mul hlog hE2 (abs_nonneg _) (by linarith)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem offDiagonalRamified_bound_const_four (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) : Formalism.MainNotions.WeightDegreeSizes.DiscriminantOffsetBound D L 4 := by
  intro j hj
  have hp : D.host.d.Prime := D.host.hyp.2.1
  have hb := one_le_b L
  have hL := one_le_scL L
  have hn := one_le_n D
  have hf : (1 : ℝ) ≤ D.R.f := by linarith [f_eq D, one_le_n D]
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have hE := abs_EatD_le h P hx j hj
  have hlog : Real.log D.host.d ≤ L.sc.L := by
    obtain ⟨-, -, -, -, -, -, hQ, -⟩ := h
    refine hQ.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le ?_)
    unfold szTh
    linarith [L.sc.eps_pos]
  have hlog0 : 0 ≤ Real.log (D.host.d : ℝ) := Real.log_natCast_nonneg _
  have hE2 : |EatD D j| ≤ 2 * ((D.R.f : ℝ) * L.sc.b) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hS, -⟩ := h
    have a1 : (D.host.TT.card : ℝ) ≤ D.R.n := by
      rw [← card_HH]
      exact_mod_cast Finset.card_le_univ _
    have a2 : (D.host.TT.card : ℝ) * L.sc.b ≤ D.R.f * L.sc.b :=
      mul_le_mul_of_nonneg_right (by linarith [f_eq D]) (by linarith)
    have a3 : (D.R.f : ℝ) * (D.R.k * L.sc.b') ≤ D.R.f * L.sc.b :=
      mul_le_mul_of_nonneg_left (k_b'_le hS) (by linarith)
    linarith
  have hB : L.B0 = D.R.f * D.R.m * L.sc.b * L.sc.L := rfl
  have hB1 : D.R.f * L.sc.b * L.sc.L ≤ L.B0 := by
    rw [hB, show (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L = D.R.m * (D.R.f * L.sc.b * L.sc.L) by ring]
    exact le_mul_of_one_le_left (by positivity) hm
  have h1 : Real.log (D.host.d : ℝ) * |EatD D j| ≤ L.sc.L * (2 * ((D.R.f : ℝ) * L.sc.b)) :=
    mul_le_mul hlog hE2 (abs_nonneg _) (by linarith)
  nlinarith

/- English proof (translation)
Introduce `eps Fm _ _`. Use `⟨4, 2, by norm_num, fun x hx0 hx i => ?_⟩` and prove the remaining obligations. Conclude with `offDiagonalRamified_bound_const_four (Fm.sizes x hx i) (Fm.params x hx i) (by rw [Fm.L_x x i hx]; exact hx0)`.
-/
theorem offDiagonalRamified_bound_along_family : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.DiscriminantOffsetBound (Fm.D x i) (Fm.L x i) C := by
  intro eps Fm _ _
  refine ⟨4, 2, by norm_num, fun x hx0 hx i => ?_⟩
  exact offDiagonalRamified_bound_const_four (Fm.sizes x hx i) (Fm.params x hx i) (by rw [Fm.L_x x i hx]; exact hx0)

end GlobalTheory.RamifiedOffD

end
