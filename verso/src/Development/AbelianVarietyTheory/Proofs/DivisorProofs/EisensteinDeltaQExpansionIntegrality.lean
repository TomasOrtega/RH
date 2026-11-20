import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalMF

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

/- English proof (translation)
Unfold `HasQ at h ⊢`. Introduce `τ`. Establish `hg : Function.Injective (fun n : ℕ => N * n)` using `fun x y hxy => Nat.eq_of_mul_eq_mul_left hN hxy`. Establish `hN' : (N : ℂ) ≠ 0` using `by exact_mod_cast hN.ne'`. Rewrite using `[← hg.hasSum_iff]`.

Use `h τ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `n`. Simplify using `only [Function.comp_apply, spread, dvd_mul_right, if_true, Nat.mul_div_cancel_left n hN]`. Use `congr 2`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Introduce `m hm`. Simplify using `only [spread]`. Rewrite using `[if_neg, zero_mul]`. Introduce and unpack `⟨k, rfl⟩`.

Conclude with `hm ⟨k, rfl⟩`.
-/
private theorem eis_spread (N : ℕ) (hN : 0 < N) (f : ℍ → ℂ) (a : ℕ → ℂ) (h : HasQ 1 f a) :
    HasQ N f (spread N a) := by
  unfold HasQ at h ⊢
  intro τ
  have hg : Function.Injective (fun n : ℕ => N * n) := fun x y hxy => Nat.eq_of_mul_eq_mul_left hN hxy
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [← hg.hasSum_iff]
  · convert h τ using 1
    funext n
    simp only [Function.comp_apply, spread, dvd_mul_right, if_true, Nat.mul_div_cancel_left n hN]
    congr 2
    push_cast
    field_simp
  · intro m hm
    simp only [spread]
    rw [if_neg, zero_mul]
    rintro ⟨k, rfl⟩
    exact hm ⟨k, rfl⟩

/- English proof (translation)
Unfold `HasQ`. Introduce `τ`. Establish `hs` using `hf.hasSum τ`. Rewrite `hs` using `[← hp]`. Use `hs using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `n`. Rewrite using `[PowerSeries.coeff_map, eq_intCast, ReciprocityTheory.ChartRestriction.L1.qm, ← Complex.exp_nat_mul]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem eis_one {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) (p : PowerSeries ℤ)
    (hp : p.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 f) :
    HasQ 1 f fun n => ((PowerSeries.coeff n p : ℤ) : ℂ) := by
  unfold HasQ
  intro τ
  have hs := hf.hasSum τ
  rw [← hp] at hs
  convert hs using 1
  funext n
  rw [PowerSeries.coeff_map, eq_intCast, ReciprocityTheory.ChartRestriction.L1.qm, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨k, hk, p, hp⟩ : ∃ k : ℤ, IsMF k F ∧ ∃ p : PowerSeries ℤ, p.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 F := by`. Break down `hF with rfl | rfl | rfl` into its components or cases. Conclude with `⟨4, ⟨E₄, fun _ => rfl⟩, _, ReciprocityTheory.ChartRestriction.L1.map_eisensteinFourInt⟩`. Conclude with `⟨6, ⟨E₆, fun _ => rfl⟩, _, ReciprocityTheory.ChartRestriction.L1.map_eisensteinSixInt⟩`. Conclude with `⟨12, ReciprocityTheory.ChartRestriction.L1.isMF_DD, _, ReciprocityTheory.ChartRestriction.L1.dC_eq⟩`.

Use `⟨fun n => if N ∣ n then PowerSeries.coeff (n / N) p else 0, ?_⟩` and prove the remaining obligations. Use `eis_spread N hN F _ (eis_one hk p hp) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `n`. Simplify using `only [spread]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem eis_hasQ_int (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ) (hF : F = ⇑E₄ ∨ F = ⇑E₆ ∨ F = DD) :
    ∃ a : ℕ → ℤ, HasQ N F fun n => (a n : ℂ) := by
  obtain ⟨k, hk, p, hp⟩ : ∃ k : ℤ, IsMF k F ∧ ∃ p : PowerSeries ℤ,
      p.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 F := by
    rcases hF with rfl | rfl | rfl
    · exact ⟨4, ⟨E₄, fun _ => rfl⟩, _, ReciprocityTheory.ChartRestriction.L1.map_eisensteinFourInt⟩
    · exact ⟨6, ⟨E₆, fun _ => rfl⟩, _, ReciprocityTheory.ChartRestriction.L1.map_eisensteinSixInt⟩
    · exact ⟨12, ReciprocityTheory.ChartRestriction.L1.isMF_DD, _, ReciprocityTheory.ChartRestriction.L1.dC_eq⟩
  refine ⟨fun n => if N ∣ n then PowerSeries.coeff (n / N) p else 0, ?_⟩
  convert eis_spread N hN F _ (eis_one hk p hp) using 1
  funext n
  simp only [spread]
  split_ifs <;> simp

/- English proof (translation)
Take `⟨a, ha⟩` from `eis_hasQ_int N hN F hF`. Conclude with `⟨_, ha, fun n => intCast_mem R (a n)⟩`.
-/
theorem eis_qAll (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ) (hF : F = ⇑E₄ ∨ F = ⇑E₆ ∨ F = DD)
    (R : Subring ℂ) : QAll (· ∈ R) N F := by
  obtain ⟨a, ha⟩ := eis_hasQ_int N hN F hF
  exact ⟨_, ha, fun n => intCast_mem R (a n)⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `eis_hasQ_int N hN F hF`. Use `⟨_, ha, ?_⟩` and prove the remaining obligations. Simplify `ha` using `only [map_intCast]`.
-/
theorem eis_qConj (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ) (hF : F = ⇑E₄ ∨ F = ⇑E₆ ∨ F = DD)
    (g : ℂ ≃+* ℂ) : QConj g N F F := by
  obtain ⟨a, ha⟩ := eis_hasQ_int N hN F hF
  refine ⟨_, ha, ?_⟩
  simpa only [map_intCast] using ha

/- English proof (translation)
Introduce `N hN F hF`. Conclude with `⟨eis_hasQ_int N hN F hF, fun R => eis_qAll N hN F hF R, fun g => eis_qConj N hN F hF g⟩`.
-/
theorem eis_q : ∀ (N : ℕ), 0 < N → ∀ F : ℍ → ℂ, (F = ⇑E₄ ∨ F = ⇑E₆ ∨ F = DD) →
    (∃ a : ℕ → ℤ, HasQ N F fun n => (a n : ℂ)) ∧ (∀ R : Subring ℂ, QAll (· ∈ R) N F) ∧
      ∀ g : ℂ ≃+* ℂ, QConj g N F F := by
  intro N hN F hF
  exact ⟨eis_hasQ_int N hN F hF, fun R => eis_qAll N hN F hF R, fun g => eis_qConj N hN F hF g⟩

end GlobalTheory.QFam
