import Mathlib
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

noncomputable section

namespace GlobalTheory.TwU

/- English proof (translation)
Assume the negation of the conclusion as `hk`. Establish `hk : D.R.k < 2 * Formalism.MainNotions.G.rG L.sc` using `not_le.1 hk`. Establish `hx` using `L.sc.one_lt_alt`. Establish `he` using `L.sc.eps_pos`. Establish `he2` using `L.sc.eps_lt`.

Establish `hK` using `hS.2.2.1.1`. Establish `h1 : L.sc.x ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps - Formalism.MainNotions.szTh L)` using `Real.self_le_rpow_of_one_le hx.le (by unfold Formalism.MainNotions.szTh; linarith)`. Establish `h2 : (D.R.k : ℝ) ≤ 2 * (Formalism.MainNotions.G.rG L.sc : ℝ)` using `by exact_mod_cast hk.le`. Establish `h3 : (Formalism.MainNotions.G.rG L.sc : ℝ) ≤ 8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps + 2`. Unfold `Formalism.MainNotions.G.rG Formalism.MainNotions.G.KG`.

Use `Nat.ceil_lt_add_one (a := 8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps) (div_nonneg (by unfold Formalism.MainNotions.G.hG; linarith) he.le)` as an intermediate fact. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h5 : L.sc.x ≤ 2 * (8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps + 2)` using `by linarith`. Establish `h6` using `mul_le_mul_of_nonneg_right h5 he.le`.

Establish `h7 : 2 * (8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps + 2) * L.sc.eps = 2 * (8 * (Formalism.MainNotions.G.hG L.sc + 2) + 2 * L.sc.eps)`. Clear the denominators using the available nonvanishing facts. Rewrite `h6` using `[h7]`. Unfold `Formalism.MainNotions.G.hG at h6`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem two_rG_le_k_of_size {D : Formalism.BasicNotions.D7} {L : SizeData₂ D} (hS : Formalism.MainNotions.SizesAt L)
    (h : 70 < L.sc.x * L.sc.eps) : 2 * Formalism.MainNotions.G.rG L.sc ≤ D.R.k := by
  by_contra hk
  have hk : D.R.k < 2 * Formalism.MainNotions.G.rG L.sc := not_le.1 hk
  have hx := L.sc.one_lt_alt
  have he := L.sc.eps_pos
  have he2 := L.sc.eps_lt
  have hK := hS.2.2.1.1
  have h1 : L.sc.x ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps - Formalism.MainNotions.szTh L) :=
    Real.self_le_rpow_of_one_le hx.le (by unfold Formalism.MainNotions.szTh; linarith)
  have h2 : (D.R.k : ℝ) ≤ 2 * (Formalism.MainNotions.G.rG L.sc : ℝ) := by exact_mod_cast hk.le
  have h3 : (Formalism.MainNotions.G.rG L.sc : ℝ) ≤ 8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps + 2 := by
    unfold Formalism.MainNotions.G.rG Formalism.MainNotions.G.KG
    have := Nat.ceil_lt_add_one (a := 8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps)
      (div_nonneg (by unfold Formalism.MainNotions.G.hG; linarith) he.le)
    push_cast
    linarith
  have h5 : L.sc.x ≤ 2 * (8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps + 2) := by linarith
  have h6 := mul_le_mul_of_nonneg_right h5 he.le
  have h7 : 2 * (8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps + 2) * L.sc.eps =
      2 * (8 * (Formalism.MainNotions.G.hG L.sc + 2) + 2 * L.sc.eps) := by
    field_simp
  rw [h7] at h6
  unfold Formalism.MainNotions.G.hG at h6
  linarith

/- English proof (translation)
Use `⟨71 / eps, fun x hx hx1 i => two_rG_le_k_of_size (Fm.sizes x hx1 i) ?_⟩` and prove the remaining obligations. Establish `hs : (Fm.L x i).sc.x = x` using `Fm.L_x x i hx1`. Establish `he : (Fm.L x i).sc.eps = eps` using `Fm.L_eps x i`. Establish `hp : 0 < eps` using `he ▸ (Fm.L x i).sc.eps_pos`. Rewrite using `[hs, he]`.

Establish `: 71 ≤ x * eps` using `(div_le_iff₀ hp).1 hx`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem two_rG_le_k_large {eps : ℝ} (Fm : FamP eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, 2 * rG (Fm.L x i).sc ≤ (Fm.D x i).R.k := by
  refine ⟨71 / eps, fun x hx hx1 i => two_rG_le_k_of_size (Fm.sizes x hx1 i) ?_⟩
  have hs : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have he : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hp : 0 < eps := he ▸ (Fm.L x i).sc.eps_pos
  rw [hs, he]
  have : 71 ≤ x * eps := (div_le_iff₀ hp).1 hx
  linarith

end GlobalTheory.TwU
