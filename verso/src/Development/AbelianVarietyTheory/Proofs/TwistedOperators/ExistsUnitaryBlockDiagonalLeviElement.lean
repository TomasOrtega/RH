import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallerUnitaryGroupEmbedding

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

/- English proof (translation)
Introduce `L _ _ ϖ σ q N hq a g₀`. Take `⟨-, -, hσϖ, hv, -⟩` from `hq`. Establish `hϖ : ϖ ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hv`.

Take `⟨ι, hι⟩` from `_root_.GlobalTheory.SatakeWeyl.embExists L σ (N + 2) N _root_.GlobalTheory.InertZeta.mid _root_.GlobalTheory.InertZeta.mid_injective _root_.GlobalTheory.InertZeta.mid_rev`. Take `⟨h1, h2⟩` from `hι g₀`. Use `set d : Fin (N + 2) → L := fun i => if i = 0 then ϖ ^ a else if i = Fin.last (N + 1) then ϖ ^ (-a) else 1`. Establish `hd : ∀ i, σ (d i) * d i.rev = 1`. Introduce `i`.

Break down `_root_.GlobalTheory.InertZeta.idx_cases i with rfl | ⟨k, rfl⟩ | rfl` into its components or cases. Simplify using `[d, _root_.GlobalTheory.InertZeta.last_ne_zero, map_zpow₀, hσϖ, mul_inv_cancel₀ (zpow_ne_zero a hϖ)]`. Simplify using `[d, ← _root_.GlobalTheory.InertZeta.mid_rev, _root_.GlobalTheory.InertZeta.mid_ne_zero, _root_.GlobalTheory.InertZeta.mid_ne_last]`. Simplify using `[d, _root_.GlobalTheory.InertZeta.last_ne_zero, map_zpow₀, hσϖ, inv_mul_cancel₀ (zpow_ne_zero a hϖ)]`. Take `⟨D, hD⟩` from `_root_.GlobalTheory.SatakeWeyl.exists_mat (σ := σ) (Matrix.diagonal d) (by`.

Use extensionality with `i j`. Unfold `_root_.Formalism.UG.cT`. Rewrite using `[Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul, _root_.Formalism.UG.P.fIwasawa_antiJ]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Simplify using `using hd i`. Use the proof step `simp)`. Establish `h0 : (0 : Fin (N + 2)) ∉ Set.range _root_.GlobalTheory.InertZeta.mid` using `fun ⟨k, hk⟩ => _root_.GlobalTheory.InertZeta.mid_ne_zero k hk`. Establish `hl : Fin.last (N + 1) ∉ Set.range _root_.GlobalTheory.InertZeta.mid` using `fun ⟨k, hk⟩ => _root_.GlobalTheory.InertZeta.mid_ne_last k hk`. Establish `hm : _root_.GlobalTheory.SatakeWeyl.mat (D * ι g₀) = Matrix.diagonal d * _root_.GlobalTheory.SatakeWeyl.mat (ι g₀)`.

Rewrite using `[← hD]`. Both sides reduce to the same expression. Use `⟨D * ι g₀, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Rewrite using `[hm, Matrix.diagonal_mul]`.

Establish `hne : i ≠ j` using `fun h => hij (h ▸ rfl)`. Distinguish the cases in `hi : i ∈ Set.range _root_.GlobalTheory.InertZeta.mid`. Distinguish the cases in `hj : j ∈ Set.range _root_.GlobalTheory.InertZeta.mid`. Take `⟨k, rfl⟩` from `hi`. Take `⟨l, rfl⟩` from `hj`.

Simplify using `[_root_.GlobalTheory.InertZeta.blk_mid] at hij`. Rewrite using `[h2 i j (Or.inr hj), Matrix.one_apply_ne hne, mul_zero]`. Rewrite using `[h2 i j (Or.inl hi), Matrix.one_apply_ne hne, mul_zero]`. Rewrite using `[hm, Matrix.diagonal_mul, h2 0 0 (Or.inl h0), Matrix.one_apply_eq, mul_one]`. Simplify using `[d]`.

Rewrite using `[hm, Matrix.diagonal_mul, h2 _ _ (Or.inl hl), Matrix.one_apply_eq, mul_one]`. Simplify using `[d, _root_.GlobalTheory.InertZeta.last_ne_zero]`. Introduce `i j`. Rewrite using `[hm, Matrix.diagonal_mul, h1]`. Simplify using `[d, _root_.GlobalTheory.InertZeta.mid_ne_zero, _root_.GlobalTheory.InertZeta.mid_ne_last]`.
-/
theorem _root_.GlobalTheory.InertZeta.leviExists : _root_.GlobalTheory.InertZeta.LeviExists := by
  intro L _ _ ϖ σ q N hq a g₀
  obtain ⟨-, -, hσϖ, hv, -⟩ := hq
  have hϖ : ϖ ≠ 0 := by
    rintro rfl
    simp at hv
  obtain ⟨ι, hι⟩ := _root_.GlobalTheory.SatakeWeyl.embExists L σ (N + 2) N _root_.GlobalTheory.InertZeta.mid
    _root_.GlobalTheory.InertZeta.mid_injective _root_.GlobalTheory.InertZeta.mid_rev
  obtain ⟨h1, h2⟩ := hι g₀
  set d : Fin (N + 2) → L := fun i => if i = 0 then ϖ ^ a else if i = Fin.last (N + 1) then ϖ ^ (-a) else 1
  have hd : ∀ i, σ (d i) * d i.rev = 1 := by
    intro i
    rcases _root_.GlobalTheory.InertZeta.idx_cases i with rfl | ⟨k, rfl⟩ | rfl
    · simp [d, _root_.GlobalTheory.InertZeta.last_ne_zero, map_zpow₀, hσϖ, mul_inv_cancel₀ (zpow_ne_zero a hϖ)]
    · simp [d, ← _root_.GlobalTheory.InertZeta.mid_rev, _root_.GlobalTheory.InertZeta.mid_ne_zero,
        _root_.GlobalTheory.InertZeta.mid_ne_last]
    · simp [d, _root_.GlobalTheory.InertZeta.last_ne_zero, map_zpow₀, hσϖ, inv_mul_cancel₀ (zpow_ne_zero a hϖ)]
  obtain ⟨D, hD⟩ := _root_.GlobalTheory.SatakeWeyl.exists_mat (σ := σ) (Matrix.diagonal d) (by
    ext i j
    unfold _root_.Formalism.UG.cT
    rw [Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.mul_diagonal,
      Matrix.diagonal_mul, _root_.Formalism.UG.P.fIwasawa_antiJ]
    split_ifs with h
    · subst h
      simpa using hd i
    · simp)
  have h0 : (0 : Fin (N + 2)) ∉ Set.range _root_.GlobalTheory.InertZeta.mid :=
    fun ⟨k, hk⟩ => _root_.GlobalTheory.InertZeta.mid_ne_zero k hk
  have hl : Fin.last (N + 1) ∉ Set.range _root_.GlobalTheory.InertZeta.mid :=
    fun ⟨k, hk⟩ => _root_.GlobalTheory.InertZeta.mid_ne_last k hk
  have hm : _root_.GlobalTheory.SatakeWeyl.mat (D * ι g₀) =
      Matrix.diagonal d * _root_.GlobalTheory.SatakeWeyl.mat (ι g₀) := by
    rw [← hD]
    rfl
  refine ⟨D * ι g₀, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    rw [hm, Matrix.diagonal_mul]
    have hne : i ≠ j := fun h => hij (h ▸ rfl)
    by_cases hi : i ∈ Set.range _root_.GlobalTheory.InertZeta.mid
    · by_cases hj : j ∈ Set.range _root_.GlobalTheory.InertZeta.mid
      · obtain ⟨k, rfl⟩ := hi
        obtain ⟨l, rfl⟩ := hj
        simp [_root_.GlobalTheory.InertZeta.blk_mid] at hij
      · rw [h2 i j (Or.inr hj), Matrix.one_apply_ne hne, mul_zero]
    · rw [h2 i j (Or.inl hi), Matrix.one_apply_ne hne, mul_zero]
  · rw [hm, Matrix.diagonal_mul, h2 0 0 (Or.inl h0), Matrix.one_apply_eq, mul_one]
    simp [d]
  · rw [hm, Matrix.diagonal_mul, h2 _ _ (Or.inl hl), Matrix.one_apply_eq, mul_one]
    simp [d, _root_.GlobalTheory.InertZeta.last_ne_zero]
  · intro i j
    rw [hm, Matrix.diagonal_mul, h1]
    simp [d, _root_.GlobalTheory.InertZeta.mid_ne_zero, _root_.GlobalTheory.InertZeta.mid_ne_last]

end GlobalTheory.InertZeta
