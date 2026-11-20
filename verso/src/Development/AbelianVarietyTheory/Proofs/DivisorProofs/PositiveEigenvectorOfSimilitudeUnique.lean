import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormNegOnOrthogonalOfPositiveIndexOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

/- English proof (translation)
Use `set f := Matrix.toLin' g`. Establish `hc : f.charpoly = g.charpoly` using `Matrix.charpoly_toLin' g`. Establish `h1 : Module.finrank ℂ (Module.End.maxGenEigenspace f μ) ≤ 1`. Rewrite using `[LinearMap.finrank_maxGenEigenspace_eq, hc]`. Conclude with `Polynomial.rootMultiplicity_le_one_of_separable hg μ`.

Establish `mem : ∀ v : Fin n → ℂ, g *ᵥ v = μ • v → v ∈ Module.End.maxGenEigenspace f μ` using `fun v hv => by`. Rewrite using `[Module.End.mem_maxGenEigenspace]`. Conclude with `⟨1, by simp [f, hv]⟩`. Establish `h2 : Module.finrank ℂ (Module.End.maxGenEigenspace f μ) = 1` using `le_antisymm h1 (Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨x, mem x hx⟩, fun h => hx0 (congrArg Subtype.val h)⟩)`. Take `⟨c, hc⟩` from `(finrank_eq_one_iff_of_nonzero' (⟨x, mem x hx⟩ : Module.End.maxGenEigenspace f μ) fun h => hx0 (congrArg Subtype.val h)).1 h2 ⟨y, mem y hy⟩`.

Conclude with `⟨c, (congrArg Subtype.val hc).symm⟩`.
-/
theorem exists_smul_eq_of_eigvec_of_charpoly_separable {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g.charpoly.Separable) {μ : ℂ} {x y : Fin n → ℂ} (hx0 : x ≠ 0)
    (hx : g *ᵥ x = μ • x) (hy : g *ᵥ y = μ • y) : ∃ c : ℂ, y = c • x := by
  set f := Matrix.toLin' g
  have hc : f.charpoly = g.charpoly := Matrix.charpoly_toLin' g
  have h1 : Module.finrank ℂ (Module.End.maxGenEigenspace f μ) ≤ 1 := by
    rw [LinearMap.finrank_maxGenEigenspace_eq, hc]
    exact Polynomial.rootMultiplicity_le_one_of_separable hg μ
  have mem : ∀ v : Fin n → ℂ, g *ᵥ v = μ • v → v ∈ Module.End.maxGenEigenspace f μ := fun v hv => by
    rw [Module.End.mem_maxGenEigenspace]
    exact ⟨1, by simp [f, hv]⟩
  have h2 : Module.finrank ℂ (Module.End.maxGenEigenspace f μ) = 1 := le_antisymm h1
    (Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨x, mem x hx⟩, fun h => hx0 (congrArg Subtype.val h)⟩)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨x, mem x hx⟩ : Module.End.maxGenEigenspace f μ)
    fun h => hx0 (congrArg Subtype.val h)).1 h2 ⟨y, mem y hy⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

/- English proof (translation)
Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]`.
-/
theorem form_conjTranspose_mul_mul {n : ℕ} (A g : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    star u ⬝ᵥ (gᴴ * A * g) *ᵥ v = star (g *ᵥ u) ⬝ᵥ A *ᵥ (g *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

/- English proof (translation)
Introduce `n A hA hdet hsig g s hs hsim hsep x y hxp hyp ⟨μ, hμ⟩ ⟨ν, hν⟩`. Establish `hx0 : x ≠ 0` using `by rintro rfl; simp at hxp`. Establish `hy0 : y ≠ 0` using `by rintro rfl; simp at hyp`. Establish `Q : ∀ u v : Fin n → ℂ, star (g *ᵥ u) ⬝ᵥ A *ᵥ (g *ᵥ v) = (s : ℂ) * (star u ⬝ᵥ A *ᵥ v)`. Introduce `u v`.

Rewrite using `[← form_conjTranspose_mul_mul, hsim]`. Establish `e : ((s : ℂ) • A) *ᵥ v = (s : ℂ) • (A *ᵥ v)`. Conclude with `Matrix.smul_mulVec (s : ℂ) A v`. Rewrite using `[e, dotProduct_smul, smul_eq_mul]`. Establish `scal : ∀ (a b : ℂ) (u v : Fin n → ℂ), star (a • u) ⬝ᵥ A *ᵥ (b • v) = star a * b * (star u ⬝ᵥ A *ᵥ v)`.

Introduce `a b u v`. Rewrite using `[star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hQx : star x ⬝ᵥ A *ᵥ x ≠ 0` using `fun h => by rw [h] at hxp; simp at hxp`. Establish `hQy : star y ⬝ᵥ A *ᵥ y ≠ 0` using `fun h => by rw [h] at hyp; simp at hyp`.

Establish `eμ : star μ * μ = (s : ℂ)`. Use `Q x x` as an intermediate fact. Rewrite `this` using `[hμ, scal]`. Conclude with `mul_right_cancel₀ hQx this`. Establish `eν : star ν * ν = (s : ℂ)`.

Use `Q y y` as an intermediate fact. Rewrite `this` using `[hν, scal]`. Conclude with `mul_right_cancel₀ hQy this`. Establish `exy : (star μ * ν - s) * (star x ⬝ᵥ A *ᵥ y) = 0`. Use `Q x y` as an intermediate fact.

Rewrite `this` using `[hμ, hν, scal]`. Rewrite using `[sub_mul, this, sub_self]`. Distinguish the cases in `hμν : μ = ν`. Substitute `hμν` using the available equality. Conclude with `exists_smul_eq_of_eigvec_of_charpoly_separable hsep hx0 hμ hν`.

It suffices to derive a contradiction. Establish `hs0 : (s : ℂ) ≠ 0` using `by exact_mod_cast hs.ne'`. Establish `hμ0 : star μ ≠ 0` using `fun h => hs0 (by rw [← eμ, h, zero_mul])`. Establish `hne : star μ * ν - s ≠ 0`. Introduce `h`.

Apply `hμν` to reduce the goal to its premises. Establish `: star μ * ν = star μ * μ` using `by rw [eμ]; exact sub_eq_zero.1 h`. Conclude with `(mul_left_cancel₀ hμ0 this).symm`. Establish `horth : star x ⬝ᵥ A *ᵥ y = 0` using `(mul_eq_zero.1 exy).resolve_left hne`. Use `GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one A hA hdet hsig x y hxp horth hy0` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eigvec_pos_unique_of_similitude : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian),
    A.det ≠ 0 → sigPosH hA = 1 → ∀ (g : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 < s →
    gᴴ * A * g = (s : ℂ) • A → g.charpoly.Separable → ∀ x y : Fin n → ℂ,
    0 < (star x ⬝ᵥ A *ᵥ x).re → 0 < (star y ⬝ᵥ A *ᵥ y).re →
    (∃ μ : ℂ, g *ᵥ x = μ • x) → (∃ ν : ℂ, g *ᵥ y = ν • y) → ∃ c : ℂ, y = c • x := by
  intro n A hA hdet hsig g s hs hsim hsep x y hxp hyp ⟨μ, hμ⟩ ⟨ν, hν⟩
  have hx0 : x ≠ 0 := by rintro rfl; simp at hxp
  have hy0 : y ≠ 0 := by rintro rfl; simp at hyp
  have Q : ∀ u v : Fin n → ℂ, star (g *ᵥ u) ⬝ᵥ A *ᵥ (g *ᵥ v) = (s : ℂ) * (star u ⬝ᵥ A *ᵥ v) := by
    intro u v
    rw [← form_conjTranspose_mul_mul, hsim]
    have e : ((s : ℂ) • A) *ᵥ v = (s : ℂ) • (A *ᵥ v) := by
      exact Matrix.smul_mulVec (s : ℂ) A v
    rw [e, dotProduct_smul, smul_eq_mul]
  have scal : ∀ (a b : ℂ) (u v : Fin n → ℂ), star (a • u) ⬝ᵥ A *ᵥ (b • v) = star a * b * (star u ⬝ᵥ A *ᵥ v) := by
    intro a b u v
    rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]; ring
  have hQx : star x ⬝ᵥ A *ᵥ x ≠ 0 := fun h => by rw [h] at hxp; simp at hxp
  have hQy : star y ⬝ᵥ A *ᵥ y ≠ 0 := fun h => by rw [h] at hyp; simp at hyp
  have eμ : star μ * μ = (s : ℂ) := by
    have := Q x x; rw [hμ, scal] at this; exact mul_right_cancel₀ hQx this
  have eν : star ν * ν = (s : ℂ) := by
    have := Q y y; rw [hν, scal] at this; exact mul_right_cancel₀ hQy this
  have exy : (star μ * ν - s) * (star x ⬝ᵥ A *ᵥ y) = 0 := by
    have := Q x y; rw [hμ, hν, scal] at this; rw [sub_mul, this, sub_self]
  by_cases hμν : μ = ν
  · subst hμν
    exact exists_smul_eq_of_eigvec_of_charpoly_separable hsep hx0 hμ hν
  · exfalso
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hμ0 : star μ ≠ 0 := fun h => hs0 (by rw [← eμ, h, zero_mul])
    have hne : star μ * ν - s ≠ 0 := by
      intro h
      apply hμν
      have : star μ * ν = star μ * μ := by rw [eμ]; exact sub_eq_zero.1 h
      exact (mul_left_cancel₀ hμ0 this).symm
    have horth : star x ⬝ᵥ A *ᵥ y = 0 := (mul_eq_zero.1 exy).resolve_left hne
    have := GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one A hA hdet hsig x y hxp horth hy0
    linarith

end GlobalTheory
