import Mathlib
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RpowLeExpRpowEventually
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Use `haveI : NeZero g := ⟨hg.ne'⟩`. Establish `h1 : Nat.card (GL (Fin r) (ZMod g)) ≤ Nat.card (Matrix (Fin r) (Fin r) (ZMod g))` using `Nat.card_le_card_of_injective _ Units.val_injective`. Establish `h2 : Nat.card (Matrix (Fin r) (Fin r) (ZMod g)) = g ^ (r * r)` using `by show Nat.card (Fin r → Fin r → ZMod g) = _`. Simplify using `[Nat.card_fun, pow_mul]`. Conclude with `h2 ▸ h1`.
-/
theorem natCard_GL_zmod_le (r g : ℕ) (hg : 0 < g) :
    Nat.card (GL (Fin r) (ZMod g)) ≤ g ^ (r * r) := by
  haveI : NeZero g := ⟨hg.ne'⟩
  have h1 : Nat.card (GL (Fin r) (ZMod g)) ≤ Nat.card (Matrix (Fin r) (Fin r) (ZMod g)) :=
    Nat.card_le_card_of_injective _ Units.val_injective
  have h2 : Nat.card (Matrix (Fin r) (Fin r) (ZMod g)) = g ^ (r * r) := by
    show Nat.card (Fin r → Fin r → ZMod g) = _
    simp [Nat.card_fun, pow_mul]
  exact h2 ▸ h1

/- English proof (translation)
Introduce `eps Fm`. Take `⟨x0, hx0⟩` from `poly_sizes_ranks_weights eps Fm`. Use `⟨max x0 8, fun x hx hx1 i => ?_⟩` and prove the remaining obligations. Take `⟨hCt, hf, hm, hk, -, -, -, hLx, -, hL1, hL2, hb, -⟩` from `hx0 x (le_trans (le_max_left _ _) hx) hx1 i`. Establish `hx8 : 8 ≤ x` using `le_trans (le_max_right _ _) hx`.

Establish `hS` using `Fm.sizes x hx1 i`. Establish `hLe` using `Fm.L_eps x i`. Generalize the expression as in `Fm.L x i = L at *`. Generalize the expression as in `Fm.D x i = D at *`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -⟩` from `hS`.

Establish `hlt : eps < 1 / 52` using `hLe ▸ L.sc.eps_lt`. Establish `h1x : (1 : ℝ) ≤ x` using `by linarith`. Establish `h0x : (0 : ℝ) < x` using `by linarith`. Establish `hb1 : 1 ≤ L.sc.b` using `le_trans (Real.one_le_rpow h1x (by linarith)) hb`. Establish `h2m` using `D.R.two_le_m`.

Establish `hk3` using `D.R.m_add_three_le_k`. Establish `hfk : D.R.f ≤ D.R.k` using `D.R.f_le_k`. Establish `hrk : D.R.r ≤ 2 * D.R.k` using `by unfold Ranks.r; omega`. Establish `hk5 : (5 : ℝ) ≤ D.R.k`. Establish `: 5 ≤ D.R.k` using `by omega`.

Conclude with `this` after adjusting the coercions. Establish `hfk' : (D.R.f : ℝ) ≤ D.R.k` using `by exact_mod_cast hfk`. Establish `hrk' : (D.R.r : ℝ) ≤ 2 * D.R.k` using `by exact_mod_cast hrk`. Establish `hg8 : ∀ j, (D.R.k : ℝ) ^ 8 ≤ (D.host.g j : ℝ)` using `fun j => le_trans (pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_right (by linarith) hb1) 8) (hG j j).1`. Establish `hkpos : (0 : ℝ) < (D.R.k : ℝ) ^ 8` using `by positivity`.

Establish `hgpos : ∀ j, 0 < D.host.g j` using `fun j => by`. Use `lt_of_lt_of_le hkpos (hg8 j)` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hlog : ∀ j, Real.log (D.host.g j : ℝ) ≤ x` using `fun j => by`. Use `(hG j j).2.2.trans ?_` and prove the remaining obligations.

Unfold `szTh Scale.L`. Rewrite using `[hLx, hLe, ← Real.rpow_add h0x]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨?_, ?_, hb1⟩` and prove the remaining obligations. Establish `hc : D.what₂.restRowsFiniteGroupCard ≤ (D.host.g 0 * D.host.g 1) ^ (D.R.r * D.R.r * D.R.f)`.

Rewrite using `[D.nd.restN_card_levelGroup_eq, Fin.prod_univ_two, mul_pow, pow_mul _ (D.R.r * D.R.r), pow_mul _ (D.R.r * D.R.r)]`. Conclude with `Nat.mul_le_mul (Nat.pow_le_pow_left (natCard_GL_zmod_le _ _ (hgpos 0)) _) (Nat.pow_le_pow_left (natCard_GL_zmod_le _ _ (hgpos 1)) _)`. Establish `hc' : (D.what₂.restRowsFiniteGroupCard : ℝ) ≤ ((D.host.g 0 : ℝ) * D.host.g 1) ^ (D.R.r * D.R.r * D.R.f)` using `by exact_mod_cast hc`. Establish `hp : (0 : ℝ) < D.what₂.restRowsFiniteGroupCard` using `by exact_mod_cast D.what₂.restRowsFiniteGroupCard_pos`. Establish `hg0 : (0 : ℝ) < D.host.g 0` using `by exact_mod_cast hgpos 0`.

Establish `hg1 : (0 : ℝ) < D.host.g 1` using `by exact_mod_cast hgpos 1`. Establish `hr5 : (D.R.r : ℝ) ≤ 2 * x ^ (5 : ℝ)` using `by linarith`. Unfold `lam0`. Use `(Real.log_le_log hp hc').trans ?_` and prove the remaining obligations. Rewrite using `[Real.log_pow, Real.log_mul hg0.ne' hg1.ne']`.

Use `push_cast`. Establish `hl0 : 0 ≤ Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ)` using `add_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)`. Establish `hl2 : Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ) ≤ 2 * x`. Combine the linear relations using `[hlog 0, hlog 1]`. Establish `e5 : x ^ (5 : ℝ) = x ^ 5` using `by exact_mod_cast Real.rpow_natCast x 5`.

Establish `e3 : x ^ (3 : ℝ) = x ^ 3` using `by exact_mod_cast Real.rpow_natCast x 3`. Establish `e15 : x ^ (15 : ℝ) = x ^ 15` using `by exact_mod_cast Real.rpow_natCast x 15`. Rewrite `hr5` using `[e5]`. Rewrite `hf` using `[e3]`. Rewrite using `[e15]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hmin : (D.R.k : ℝ) ^ 8 ≤ ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ)`. Use `push_cast`. Conclude with `le_min (hg8 0) (hg8 1)`. Rewrite using `[div_le_iff₀ (lt_of_lt_of_le hkpos hmin)]`.

Establish `h1 : 8 * (D.R.f : ℝ) * D.R.r ≤ 8 * (D.R.k : ℝ) * (2 * D.R.k)` using `by gcongr`. Establish `h2 : (5 : ℝ) ^ 6 ≤ (D.R.k : ℝ) ^ 6` using `by gcongr`. Establish `h3 : (D.R.k : ℝ) ^ 8 = (D.R.k : ℝ) ^ 6 * (D.R.k : ℝ) ^ 2` using `by ring`. Establish `h4 : (5 : ℝ) ^ 6 * (D.R.k : ℝ) ^ 2 ≤ (D.R.k : ℝ) ^ 6 * (D.R.k : ℝ) ^ 2` using `by gcongr`. Use polynomial arithmetic with `[sq_nonneg (D.R.k : ℝ)]`.
-/
theorem log_levelGroup_le_and_level_large : ∀ (eps : ℝ) (Fm : FamP eps), (∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, lam0 (Fm.D x i) ≤ x ^ (15 : ℝ) ∧ 8 * ((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.r : ℝ) / ((min ((Fm.D x i).host.g 0) ((Fm.D x i).host.g 1) : ℕ) : ℝ) ≤ 1 / 3 ∧ 1 ≤ (Fm.L x i).sc.b) := by
  intro eps Fm
  obtain ⟨x0, hx0⟩ := poly_sizes_ranks_weights eps Fm
  refine ⟨max x0 8, fun x hx hx1 i => ?_⟩
  obtain ⟨hCt, hf, hm, hk, -, -, -, hLx, -, hL1, hL2, hb, -⟩ :=
    hx0 x (le_trans (le_max_left _ _) hx) hx1 i
  have hx8 : 8 ≤ x := le_trans (le_max_right _ _) hx
  have hS := Fm.sizes x hx1 i
  have hLe := Fm.L_eps x i
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -⟩ := hS
  have hlt : eps < 1 / 52 := hLe ▸ L.sc.eps_lt
  have h1x : (1 : ℝ) ≤ x := by linarith
  have h0x : (0 : ℝ) < x := by linarith
  have hb1 : 1 ≤ L.sc.b := le_trans (Real.one_le_rpow h1x (by linarith)) hb
  have h2m := D.R.two_le_m
  have hk3 := D.R.m_add_three_le_k
  have hfk : D.R.f ≤ D.R.k := D.R.f_le_k
  have hrk : D.R.r ≤ 2 * D.R.k := by unfold Ranks.r; omega
  have hk5 : (5 : ℝ) ≤ D.R.k := by
    have : 5 ≤ D.R.k := by omega
    exact_mod_cast this
  have hfk' : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have hrk' : (D.R.r : ℝ) ≤ 2 * D.R.k := by exact_mod_cast hrk
  have hg8 : ∀ j, (D.R.k : ℝ) ^ 8 ≤ (D.host.g j : ℝ) := fun j =>
    le_trans (pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_right (by linarith) hb1) 8) (hG j j).1
  have hkpos : (0 : ℝ) < (D.R.k : ℝ) ^ 8 := by positivity
  have hgpos : ∀ j, 0 < D.host.g j := fun j => by
    have := lt_of_lt_of_le hkpos (hg8 j)
    exact_mod_cast this
  have hlog : ∀ j, Real.log (D.host.g j : ℝ) ≤ x := fun j => by
    refine (hG j j).2.2.trans ?_
    unfold szTh Scale.L
    rw [hLx, hLe, ← Real.rpow_add h0x]
    calc x ^ (eps / 100 + eps) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1x (by linarith)
      _ = x := Real.rpow_one x
  refine ⟨?_, ?_, hb1⟩
  · have hc : D.what₂.restRowsFiniteGroupCard ≤ (D.host.g 0 * D.host.g 1) ^ (D.R.r * D.R.r * D.R.f) := by
      rw [D.nd.restN_card_levelGroup_eq, Fin.prod_univ_two, mul_pow, pow_mul _ (D.R.r * D.R.r),
        pow_mul _ (D.R.r * D.R.r)]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (natCard_GL_zmod_le _ _ (hgpos 0)) _)
        (Nat.pow_le_pow_left (natCard_GL_zmod_le _ _ (hgpos 1)) _)
    have hc' : (D.what₂.restRowsFiniteGroupCard : ℝ) ≤
        ((D.host.g 0 : ℝ) * D.host.g 1) ^ (D.R.r * D.R.r * D.R.f) := by exact_mod_cast hc
    have hp : (0 : ℝ) < D.what₂.restRowsFiniteGroupCard := by exact_mod_cast D.what₂.restRowsFiniteGroupCard_pos
    have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast hgpos 0
    have hg1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast hgpos 1
    have hr5 : (D.R.r : ℝ) ≤ 2 * x ^ (5 : ℝ) := by linarith
    unfold lam0
    refine (Real.log_le_log hp hc').trans ?_
    rw [Real.log_pow, Real.log_mul hg0.ne' hg1.ne']
    push_cast
    have hl0 : 0 ≤ Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ) :=
      add_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
    have hl2 : Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ) ≤ 2 * x := by
      linarith [hlog 0, hlog 1]
    have e5 : x ^ (5 : ℝ) = x ^ 5 := by exact_mod_cast Real.rpow_natCast x 5
    have e3 : x ^ (3 : ℝ) = x ^ 3 := by exact_mod_cast Real.rpow_natCast x 3
    have e15 : x ^ (15 : ℝ) = x ^ 15 := by exact_mod_cast Real.rpow_natCast x 15
    rw [e5] at hr5
    rw [e3] at hf
    rw [e15]
    calc (D.R.r : ℝ) * D.R.r * D.R.f * (Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ))
        ≤ (2 * x ^ 5) * (2 * x ^ 5) * x ^ 3 * (2 * x) := by gcongr
      _ = 8 * x ^ 14 := by ring
      _ ≤ x * x ^ 14 := by gcongr
      _ = x ^ 15 := by ring
  · have hmin : (D.R.k : ℝ) ^ 8 ≤ ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ) := by
      push_cast
      exact le_min (hg8 0) (hg8 1)
    rw [div_le_iff₀ (lt_of_lt_of_le hkpos hmin)]
    have h1 : 8 * (D.R.f : ℝ) * D.R.r ≤ 8 * (D.R.k : ℝ) * (2 * D.R.k) := by gcongr
    have h2 : (5 : ℝ) ^ 6 ≤ (D.R.k : ℝ) ^ 6 := by gcongr
    have h3 : (D.R.k : ℝ) ^ 8 = (D.R.k : ℝ) ^ 6 * (D.R.k : ℝ) ^ 2 := by ring
    have h4 : (5 : ℝ) ^ 6 * (D.R.k : ℝ) ^ 2 ≤ (D.R.k : ℝ) ^ 6 * (D.R.k : ℝ) ^ 2 := by gcongr
    nlinarith [sq_nonneg (D.R.k : ℝ)]

end GlobalTheory
