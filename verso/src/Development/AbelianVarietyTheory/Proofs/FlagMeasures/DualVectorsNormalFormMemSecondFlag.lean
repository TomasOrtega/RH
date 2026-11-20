import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Formalism.FormalDegreeBessel.StatementG
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
open Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `K V _ _ _ _ H r j hj e e' s hdet he' hz hs he's hss`. Use `set P : Matrix (Fin j) (Fin j) K := Matrix.of fun a b : Fin j => H.B (e (Fin.castLE hj a)) (e' (Fin.castLE hj b)) with hPdef`. Establish `hu : IsUnit P.det` using `isUnit_iff_ne_zero.mpr hdet`. Establish `hPQ : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv P hu`. Establish `hQP : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul P hu`.

Establish `hR : ∀ (x : V) (g : Fin j → K), H.B x (∑ c, g c • e' (Fin.castLE hj c)) = ∑ c, star (g c) * H.B x (e' (Fin.castLE hj c))`. Introduce `x g`. Simplify using `[map_sum, map_smulₛₗ, starRingEnd_apply]`. Establish `hL : ∀ (y : V) (g : Fin j → K), H.B (∑ c, g c • e' (Fin.castLE hj c)) y = ∑ c, g c * H.B (e' (Fin.castLE hj c)) y`. Introduce `y g`.

Simplify using `[map_sum, LinearMap.sum_apply]`. Set `f : Fin r → V` to `fun b => if h : b.val < j then ∑ c : Fin j, star (P⁻¹ c ⟨b.val, h⟩) • e' (Fin.castLE hj c) else s b`. Establish `hf : ∀ b : Fin j, f (Fin.castLE hj b) = ∑ c, star (P⁻¹ c b) • e' (Fin.castLE hj c)` using `fun b => by`. Simplify using `[f]`. Use `⟨f, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `a ha`. Simplify using `[f, Nat.not_lt.mpr ha]`. Introduce `a ha`. Simplify using `only [f, dif_pos ha]`. Conclude with `Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.castLE hj c, c.isLt, rfl⟩)`.

Introduce `a b`. Distinguish the cases in `hb : b.val < j`. Simplify using `only [f, dif_pos hb, hR, star_star]`. Distinguish the cases in `ha : a.val < j`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Both sides reduce to the same expression. Use `_ = (P * P⁻¹) ⟨a.val, ha⟩ ⟨b.val, hb⟩ := by rw [Matrix.mul_apply]`. Use `_ = if a = b then 1 else 0 := by rw [hPQ, Matrix.one_apply]; simp [Fin.ext_iff]`.

Rewrite using `[Finset.sum_eq_zero]`. Establish `: a ≠ b` using `fun h => ha (h ▸ hb)`. Simplify using `[this]`. Introduce `c _`. Rewrite using `[hz a (Fin.castLE hj c) (Nat.not_lt.mp ha) (by simp), mul_zero]`.

Simplify using `only [f, dif_neg hb]`. Conclude with `hs a b (Nat.not_lt.mp hb)`. Introduce `a b`. Apply the tactic sequence `by_cases ha : a.val < j <;> by_cases hb : b.val < j`. Simplify using `only [f, dif_pos ha, dif_pos hb, hL, hR, he', mul_zero, Finset.sum_const_zero]`.

Simplify using `only [f, dif_pos ha, dif_neg hb, hL]`. Conclude with `Finset.sum_eq_zero fun c _ => by rw [he's _ _ (by simp) (Nat.not_lt.mp hb), mul_zero]`. Simplify using `only [f, dif_neg ha, dif_pos hb, hR]`. Conclude with `Finset.sum_eq_zero fun c _ => by rw [← H.herm, he's _ _ (by simp) (Nat.not_lt.mp ha), star_zero, mul_zero]`. Simplify using `only [f, dif_neg ha, dif_neg hb]`.

Conclude with `hss a b (Nat.not_lt.mp ha) (Nat.not_lt.mp hb)`. Introduce `a ha`. Establish `key : e' a = ∑ b : Fin j, star (P b ⟨a.val, ha⟩) • f (Fin.castLE hj b)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[Matrix.one_apply, apply_ite star]`.

Use `_ = ∑ c, star ((P⁻¹ * P) c ⟨a.val, ha⟩) • e' (Fin.castLE hj c) := by rw [hQP]`. Use `_ = ∑ b, star (P b ⟨a.val, ha⟩) • ∑ c, star (P⁻¹ c b) • e' (Fin.castLE hj c) := by`. Repeatedly rewrite using `[Matrix.mul_apply, star_sum, Finset.sum_smul, Finset.smul_sum, smul_smul, star_mul]`. Rewrite using `[Finset.sum_comm]`. Use `_ = ∑ b, star (P b ⟨a.val, ha⟩) • f (Fin.castLE hj b) := by simp_rw [hf]`.

Rewrite using `[key]`. Conclude with `Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.castLE hj b, b.isLt, rfl⟩)`.
-/
theorem dual_vectors_in_second_flag : ∀ {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) {r j : ℕ} (hj : j ≤ r) (e e' s : Fin r → V),
    (Matrix.of fun a b : Fin j => H.B (e (Fin.castLE hj a)) (e' (Fin.castLE hj b))).det ≠ 0 →
    (∀ a b, H.B (e' a) (e' b) = 0) →
    (∀ a b : Fin r, j ≤ a.val → b.val < j → H.B (e a) (e' b) = 0) →
    (∀ a b : Fin r, j ≤ b.val → H.B (e a) (s b) = if a = b then 1 else 0) →
    (∀ a b : Fin r, a.val < j → j ≤ b.val → H.B (e' a) (s b) = 0) →
    (∀ a b : Fin r, j ≤ a.val → j ≤ b.val → H.B (s a) (s b) = 0) →
    ∃ f : Fin r → V, (∀ a, j ≤ a.val → f a = s a) ∧
      (∀ a, a.val < j → f a ∈ Submodule.span K (e' '' {b | b.val < j})) ∧
      (∀ a b, H.B (e a) (f b) = if a = b then 1 else 0) ∧ (∀ a b, H.B (f a) (f b) = 0) ∧
      (∀ a, a.val < j → e' a ∈ Submodule.span K (f '' {b | b.val < j})) := by
  intro K V _ _ _ _ H r j hj e e' s hdet he' hz hs he's hss
  set P : Matrix (Fin j) (Fin j) K := Matrix.of fun a b : Fin j => H.B (e (Fin.castLE hj a)) (e' (Fin.castLE hj b)) with hPdef
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hdet
  have hPQ : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hu
  have hQP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hu
  have hR : ∀ (x : V) (g : Fin j → K), H.B x (∑ c, g c • e' (Fin.castLE hj c)) = ∑ c, star (g c) * H.B x (e' (Fin.castLE hj c)) := by
    intro x g; simp [map_sum, map_smulₛₗ, starRingEnd_apply]
  have hL : ∀ (y : V) (g : Fin j → K), H.B (∑ c, g c • e' (Fin.castLE hj c)) y = ∑ c, g c * H.B (e' (Fin.castLE hj c)) y := by
    intro y g; simp [map_sum, LinearMap.sum_apply]
  let f : Fin r → V := fun b => if h : b.val < j then ∑ c : Fin j, star (P⁻¹ c ⟨b.val, h⟩) • e' (Fin.castLE hj c) else s b
  have hf : ∀ b : Fin j, f (Fin.castLE hj b) = ∑ c, star (P⁻¹ c b) • e' (Fin.castLE hj c) := fun b => by
    simp [f]
  refine ⟨f, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha; simp [f, Nat.not_lt.mpr ha]
  · intro a ha
    simp only [f, dif_pos ha]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.castLE hj c, c.isLt, rfl⟩)
  · intro a b
    by_cases hb : b.val < j
    · simp only [f, dif_pos hb, hR, star_star]
      by_cases ha : a.val < j
      · calc ∑ c, P⁻¹ c ⟨b.val, hb⟩ * H.B (e a) (e' (Fin.castLE hj c))
            = ∑ c, P ⟨a.val, ha⟩ c * P⁻¹ c ⟨b.val, hb⟩ := by
              refine Finset.sum_congr rfl fun c _ => ?_
              rw [mul_comm]; rfl
          _ = (P * P⁻¹) ⟨a.val, ha⟩ ⟨b.val, hb⟩ := by rw [Matrix.mul_apply]
          _ = if a = b then 1 else 0 := by rw [hPQ, Matrix.one_apply]; simp [Fin.ext_iff]
      · rw [Finset.sum_eq_zero]
        · have : a ≠ b := fun h => ha (h ▸ hb)
          simp [this]
        intro c _
        rw [hz a (Fin.castLE hj c) (Nat.not_lt.mp ha) (by simp), mul_zero]
    · simp only [f, dif_neg hb]; exact hs a b (Nat.not_lt.mp hb)
  · intro a b
    by_cases ha : a.val < j <;> by_cases hb : b.val < j
    · simp only [f, dif_pos ha, dif_pos hb, hL, hR, he', mul_zero, Finset.sum_const_zero]
    · simp only [f, dif_pos ha, dif_neg hb, hL]
      exact Finset.sum_eq_zero fun c _ => by rw [he's _ _ (by simp) (Nat.not_lt.mp hb), mul_zero]
    · simp only [f, dif_neg ha, dif_pos hb, hR]
      exact Finset.sum_eq_zero fun c _ => by rw [← H.herm, he's _ _ (by simp) (Nat.not_lt.mp ha), star_zero, mul_zero]
    · simp only [f, dif_neg ha, dif_neg hb]; exact hss a b (Nat.not_lt.mp ha) (Nat.not_lt.mp hb)
  · intro a ha
    have key : e' a = ∑ b : Fin j, star (P b ⟨a.val, ha⟩) • f (Fin.castLE hj b) := by
      calc e' a = ∑ c, star ((1 : Matrix (Fin j) (Fin j) K) c ⟨a.val, ha⟩) • e' (Fin.castLE hj c) := by
              simp [Matrix.one_apply, apply_ite star]
        _ = ∑ c, star ((P⁻¹ * P) c ⟨a.val, ha⟩) • e' (Fin.castLE hj c) := by rw [hQP]
        _ = ∑ b, star (P b ⟨a.val, ha⟩) • ∑ c, star (P⁻¹ c b) • e' (Fin.castLE hj c) := by
              simp_rw [Matrix.mul_apply, star_sum, Finset.sum_smul, Finset.smul_sum, smul_smul, star_mul]
              rw [Finset.sum_comm]
        _ = ∑ b, star (P b ⟨a.val, ha⟩) • f (Fin.castLE hj b) := by simp_rw [hf]
    rw [key]
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.castLE hj b, b.isLt, rfl⟩)

end GlobalTheory
