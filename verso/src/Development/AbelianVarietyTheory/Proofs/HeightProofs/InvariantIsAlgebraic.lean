import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FinalJoin GlobalTheory.CompRat Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.WeberField

/- English proof (translation)
Establish `hD` using `g₂_cube_sub_g₃_sq_ne_zero L`. Take `⟨m, hm⟩` from `IsAlgClosed.exists_pow_nat_eq (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) (n := 12) (by norm_num)`. Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Conclude with `hD (by simpa using hm.symm)`.

Establish `H` using `isHomothetic_scalePeriods L m hm0`. Use `set L' := scalePeriods L m hm0`. Establish `e2 : L'.g₂ ^ 3 = L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)`. Rewrite using `[H.g₂_eq, ← hm]`. Clear the denominators using the available nonvanishing facts.

Establish `e3 : L'.g₃ ^ 2 = (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) - 1) / 27`. Rewrite using `[H.g₃_eq, mul_pow, inv_pow, ← pow_mul, hm]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hjm` using `mem_algebraicClosure_iff.mpr hj`.

Establish `h2 : L'.g₂ ∈ algebraicClosure ℚ ℂ` using `mem_algebraicClosure_iff.mpr (IsAlgebraic.of_pow three_pos (e2 ▸ hj))`. Establish `h3 : L'.g₃ ∈ algebraicClosure ℚ ℂ`. Use `mem_algebraicClosure_iff.mpr (IsAlgebraic.of_pow two_pos ?_)` and prove the remaining obligations. Rewrite using `[← mem_algebraicClosure_iff, e3]`. Conclude with `div_mem (sub_mem hjm (one_mem _)) (ofNat_mem _ 27)`.

Establish `hp` using `(GlobalTheory.CurveAlgebraic.weierstrassP_mem L' h2 h3 hn (t := m * t) (fun h => ht ((H t).1 h)) (by rw [mul_left_comm]; exact (H _).2 hnt)).1`. Establish `e : L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t = L'.g₂ * L'.g₃ * L'.weierstrassP (m * t)`. Rewrite using `[H.g₂_eq, H.g₃_eq, H.weierstrassP_mul, ← hm]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`.

Conclude with `mem_algebraicClosure_iff.mp (mul_mem (mul_mem h2 h3) hp)`.
-/
theorem weber_isAlgebraic (L : PeriodPair) (hj : IsAlgebraic ℚ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)))
    {n : ℕ} (hn : 0 < n) {t : ℂ} (ht : t ∉ L.lattice) (hnt : (n : ℂ) * t ∈ L.lattice) :
    IsAlgebraic ℚ (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) := by
  have hD := g₂_cube_sub_g₃_sq_ne_zero L
  obtain ⟨m, hm⟩ := IsAlgClosed.exists_pow_nat_eq (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) (n := 12) (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hD (by simpa using hm.symm)
  have H := isHomothetic_scalePeriods L m hm0
  set L' := scalePeriods L m hm0
  have e2 : L'.g₂ ^ 3 = L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
    rw [H.g₂_eq, ← hm]; field_simp
  have e3 : L'.g₃ ^ 2 = (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) - 1) / 27 := by
    rw [H.g₃_eq, mul_pow, inv_pow, ← pow_mul, hm]; field_simp; ring
  have hjm := mem_algebraicClosure_iff.mpr hj
  have h2 : L'.g₂ ∈ algebraicClosure ℚ ℂ :=
    mem_algebraicClosure_iff.mpr (IsAlgebraic.of_pow three_pos (e2 ▸ hj))
  have h3 : L'.g₃ ∈ algebraicClosure ℚ ℂ := by
    refine mem_algebraicClosure_iff.mpr (IsAlgebraic.of_pow two_pos ?_)
    rw [← mem_algebraicClosure_iff, e3]
    exact div_mem (sub_mem hjm (one_mem _)) (ofNat_mem _ 27)
  have hp := (GlobalTheory.CurveAlgebraic.weierstrassP_mem L' h2 h3 hn (t := m * t) (fun h => ht ((H t).1 h))
    (by rw [mul_left_comm]; exact (H _).2 hnt)).1
  have e : L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t =
      L'.g₂ * L'.g₃ * L'.weierstrassP (m * t) := by
    rw [H.g₂_eq, H.g₃_eq, H.weierstrassP_mul, ← hm]; field_simp
  rw [e]
  exact mem_algebraicClosure_iff.mp (mul_mem (mul_mem h2 h3) hp)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Take `⟨a, τ, ha, h⟩` from `exists_lattice_eq_mul_tau L`. Establish `key : ∀ y : ℂ, y ∈ Submodule.span ℤ {(τ : ℂ), 1} ↔ a * y ∈ L.lattice` using `fun y ↦ by`. Rewrite using `[h, Submodule.mem_span_pair]`. Simplify using `[mul_right_inj' ha]`. Establish `hi : IsIntegral ℤ (modularJ τ)`.

Use `isIntegral_modularJ_of_mul_mem (α := wC H (0, 1)) (fun m hm => ?_) fun x hx => ?_` and prove the remaining obligations. Establish `e : H.rt0 = ((2 * m - 1 : ℤ) : ℂ)`. Simplify using `only [wC] at hm`. Move the coercions through the operations in `at hm ⊢`. Take the linear combination `2 * hm`.

Establish `e'` using `H.sqrt_neg_disc_sq`. Rewrite `e'` using `[e]`. Establish `e'' : (2 * m - 1) ^ 2 = -(H.d : ℤ)` using `by exact_mod_cast e'`. Use `H.d_prime.pos` as an intermediate fact. Use polynomial arithmetic with `[sq_nonneg (2 * m - 1)]`.

Rewrite `hx`, the goal using `[key]`. Take `⟨s, hs⟩` from `(hL _).1 hx`. Take `⟨b, hb⟩` from `Weber.wC_mul H (0, 1) s`. Rewrite using `[mul_left_comm, hs, hb]`. Conclude with `(hL _).2 ⟨b, rfl⟩`.

Rewrite `hi` using `[← g₂_cube_div_eq_modularJ ha h]`. Use `div_mem (mem_algebraicClosure_iff.mpr (hi.tower_top (A := ℚ)).isAlgebraic) (ofNat_mem (algebraicClosure ℚ ℂ) 1728)` as an intermediate fact. Rewrite `this` using `[mul_div_assoc, mul_div_cancel_left₀ _ (by norm_num)]`. Conclude with `mem_algebraicClosure_iff.mp this`.
-/
theorem invariant_isAlgebraic (H : Host E) (L : PeriodPair) (hL : ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s) :
    IsAlgebraic ℚ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) := by
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  have key : ∀ y : ℂ, y ∈ Submodule.span ℤ {(τ : ℂ), 1} ↔ a * y ∈ L.lattice := fun y ↦ by
    rw [h, Submodule.mem_span_pair]
    simp [mul_right_inj' ha]
  have hi : IsIntegral ℤ (modularJ τ) := by
    refine isIntegral_modularJ_of_mul_mem (α := wC H (0, 1)) (fun m hm => ?_) fun x hx => ?_
    · have e : H.rt0 = ((2 * m - 1 : ℤ) : ℂ) := by
        simp only [wC] at hm
        push_cast at hm ⊢
        linear_combination 2 * hm
      have e' := H.sqrt_neg_disc_sq
      rw [e] at e'
      have e'' : (2 * m - 1) ^ 2 = -(H.d : ℤ) := by exact_mod_cast e'
      have := H.d_prime.pos
      nlinarith [sq_nonneg (2 * m - 1)]
    · rw [key] at hx ⊢
      obtain ⟨s, hs⟩ := (hL _).1 hx
      obtain ⟨b, hb⟩ := Weber.wC_mul H (0, 1) s
      rw [mul_left_comm, hs, hb]
      exact (hL _).2 ⟨b, rfl⟩
  rw [← g₂_cube_div_eq_modularJ ha h] at hi
  have := div_mem (mem_algebraicClosure_iff.mpr (hi.tower_top (A := ℚ)).isAlgebraic)
    (ofNat_mem (algebraicClosure ℚ ℂ) 1728)
  rw [mul_div_assoc, mul_div_cancel_left₀ _ (by norm_num)] at this
  exact mem_algebraicClosure_iff.mp this

end GlobalTheory.WeberField
