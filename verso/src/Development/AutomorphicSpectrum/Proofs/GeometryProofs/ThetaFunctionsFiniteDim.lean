import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ReFormPosOfThetaNeZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HodgeFormAna

/- English proof (translation)
Introduce `g Λ hΛ hspan Hm χ N J Θ hH hχ hN hΘ htr hne hinv z hz`. Use `haveI : IsZLattice ℝ Λ := ⟨hspan⟩`. Establish `hNr : (0 : ℝ) < N` using `by exact_mod_cast hN`. Take `⟨H', hH'⟩ : ∃ H' : Matrix (Fin g) (Fin g) ℂ, H' = (N : ℂ) • Hm` from `⟨_, rfl⟩`. Establish `hH'h : H'.IsHermitian`.

Unfold `Matrix.IsHermitian`. Rewrite using `[hH', Matrix.conjTranspose_smul, hH.eq]`. Simplify using the standard rewrite rules. Establish `hform : ∀ u v : Fin g → ℂ, u ⬝ᵥ H'.mulVec v = (N : ℂ) * (u ⬝ᵥ Hm.mulVec v)`. Introduce `u v`.

Rewrite using `[hH', Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]`. Establish `hre : ∀ u : Fin g → ℂ, (u ⬝ᵥ H'.mulVec (star u)).re = N * (u ⬝ᵥ Hm.mulVec (star u)).re`. Introduce `u`. Rewrite using `[hform]`. Simplify using the standard rewrite rules.

Establish `htr' : ∀ i (l : Λ) z, Θ i (z + l) = ((χ l) ^ N * Complex.exp (Real.pi * (z ⬝ᵥ H'.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ H'.mulVec (star (l : Fin g → ℂ))))) * Θ i z`. Introduce `i l z`. Rewrite using `[htr i l z, mul_pow, ← Complex.exp_nat_mul, hform, hform]`. Use `congr 3`. Expand and normalize the polynomial expressions, which then agree.

Establish `hχ' : ∀ l, ‖(χ l) ^ N‖ = 1` using `fun l => by rw [norm_pow, hχ, one_pow]`. Establish `hbd : ∀ i, ∃ C : ℝ, ∀ z, ‖Θ i z‖ ≤ C * Real.exp (Real.pi / 2 * (z ⬝ᵥ H'.mulVec (star z)).re)` using `fun i => GlobalTheory.ThetaPositivity.exists_norm_le Λ hH'h (fun l => χ l ^ N) hχ' (hΘ i).continuous (htr' i)`. Take `⟨i0, hi0⟩` from `hne`. Take `⟨C0, hC0⟩` from `hbd i0`. Establish `hnn : ∀ w : Fin g → ℂ, 0 ≤ (w ⬝ᵥ Hm.mulVec (star w)).re` using `fun w => not_lt.mp fun hw => hi0 (GlobalTheory.ThetaPositivity.eq_zero_of_neg hH'h (hΘ i0) hC0 (w := w) (by rw [hre]; exact mul_neg_of_pos_of_neg hNr hw))`.

Establish `him : ∀ w : Fin g → ℂ, (w ⬝ᵥ Hm.mulVec (star w)).im = 0` using `fun w => by`. Establish `h` using `congrArg Complex.im (GlobalTheory.ThetaPositivity.form_conj hH w w)`. Simplify using `only [Complex.star_def, Complex.conj_im] at h`. Combine the linear equalities and inequalities to obtain the conclusion. Use `lt_of_le_of_ne (hnn z) fun h0 => ?_` and prove the remaining obligations.

Use `open scoped ComplexOrder in`. Establish `hpsd : Hm.PosSemidef`. Use `Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hH, fun x => ?_⟩` and prove the remaining obligations. Establish `h1` using `hnn (star x)`. Establish `h2` using `him (star x)`.

Rewrite `h1`, `h2` using `[star_star]`. Conclude with `Complex.le_def.mpr ⟨h1, h2.symm⟩`. Establish `hker : Hm.mulVec (star z) = 0` using `(hpsd.dotProduct_mulVec_zero_iff (star z)).mp (by`. Rewrite using `[star_star]`. Conclude with `Complex.ext h0.symm (him z))`.

Establish `hker' : ∀ t : ℂ, H'.mulVec (star (t • z)) = 0`. Introduce `t`. Rewrite using `[star_smul, Matrix.mulVec_smul, hH', Matrix.smul_mulVec, hker]`. Simplify using the standard rewrite rules. Use `hinv z hz fun i t y => ?_` and prove the remaining obligations.

Take `⟨C, hC⟩` from `hbd i`. Establish `hd : Differentiable ℂ fun t : ℂ => Θ i (y + t • z)` using `(hΘ i).comp ((differentiable_const _).add (differentiable_id.smul_const z))`. Establish `hq : ∀ t : ℂ, ((y + t • z) ⬝ᵥ H'.mulVec (star (y + t • z))).re = (y ⬝ᵥ H'.mulVec (star y)).re`. Introduce `t`. Rewrite using `[GlobalTheory.ThetaPositivity.form_add_self hH'h, hker' t]`.

Simplify using the standard rewrite rules. Establish `hb : Bornology.IsBounded (Set.range fun t : ℂ => Θ i (y + t • z))`. Use `isBounded_iff_forall_norm_le.2 ⟨C * Real.exp (Real.pi / 2 * (y ⬝ᵥ H'.mulVec (star y)).re), ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨t, rfl⟩`. Establish `h` using `hC (y + t • z)`.

Rewrite `h` using `[hq t]`. Then use the resulting hypothesis. Establish `h` using `hd.apply_eq_apply_of_bounded hb t 0`. Simplify using `using h`.
-/
theorem pos_of_theta_power : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (N : ℕ) (J : Type) (Θ : J → (Fin g → ℂ) → ℂ), Hm.IsHermitian → (∀ l, ‖χ l‖ = 1) → 0 < N → (∀ i, Differentiable ℂ (Θ i)) → (∀ i (l : Λ) z, Θ i (z + l) = (χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) ^ N * Θ i z) → (∃ i, Θ i ≠ 0) → (∀ w : Fin g → ℂ, w ≠ 0 → ¬ ∀ i (t : ℂ) z, Θ i (z + t • w) = Θ i z) → ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re := by
  intro g Λ hΛ hspan Hm χ N J Θ hH hχ hN hΘ htr hne hinv z hz
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨H', hH'⟩ : ∃ H' : Matrix (Fin g) (Fin g) ℂ, H' = (N : ℂ) • Hm := ⟨_, rfl⟩
  have hH'h : H'.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [hH', Matrix.conjTranspose_smul, hH.eq]
    simp
  have hform : ∀ u v : Fin g → ℂ, u ⬝ᵥ H'.mulVec v = (N : ℂ) * (u ⬝ᵥ Hm.mulVec v) := by
    intro u v
    rw [hH', Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hre : ∀ u : Fin g → ℂ,
      (u ⬝ᵥ H'.mulVec (star u)).re = N * (u ⬝ᵥ Hm.mulVec (star u)).re := by
    intro u
    rw [hform]
    simp
  have htr' : ∀ i (l : Λ) z, Θ i (z + l) =
      ((χ l) ^ N * Complex.exp (Real.pi * (z ⬝ᵥ H'.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ H'.mulVec (star (l : Fin g → ℂ))))) * Θ i z := by
    intro i l z
    rw [htr i l z, mul_pow, ← Complex.exp_nat_mul, hform, hform]
    congr 3
    ring
  have hχ' : ∀ l, ‖(χ l) ^ N‖ = 1 := fun l => by rw [norm_pow, hχ, one_pow]
  have hbd : ∀ i, ∃ C : ℝ, ∀ z, ‖Θ i z‖ ≤
      C * Real.exp (Real.pi / 2 * (z ⬝ᵥ H'.mulVec (star z)).re) := fun i =>
    GlobalTheory.ThetaPositivity.exists_norm_le Λ hH'h (fun l => χ l ^ N) hχ' (hΘ i).continuous (htr' i)
  obtain ⟨i0, hi0⟩ := hne
  obtain ⟨C0, hC0⟩ := hbd i0
  have hnn : ∀ w : Fin g → ℂ, 0 ≤ (w ⬝ᵥ Hm.mulVec (star w)).re := fun w =>
    not_lt.mp fun hw => hi0 (GlobalTheory.ThetaPositivity.eq_zero_of_neg hH'h (hΘ i0) hC0 (w := w)
      (by rw [hre]; exact mul_neg_of_pos_of_neg hNr hw))
  have him : ∀ w : Fin g → ℂ, (w ⬝ᵥ Hm.mulVec (star w)).im = 0 := fun w => by
    have h := congrArg Complex.im (GlobalTheory.ThetaPositivity.form_conj hH w w)
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  refine lt_of_le_of_ne (hnn z) fun h0 => ?_
  open scoped ComplexOrder in
  have hpsd : Hm.PosSemidef := by
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hH, fun x => ?_⟩
    have h1 := hnn (star x)
    have h2 := him (star x)
    rw [star_star] at h1 h2
    exact Complex.le_def.mpr ⟨h1, h2.symm⟩
  have hker : Hm.mulVec (star z) = 0 :=
    (hpsd.dotProduct_mulVec_zero_iff (star z)).mp (by
      rw [star_star]
      exact Complex.ext h0.symm (him z))
  have hker' : ∀ t : ℂ, H'.mulVec (star (t • z)) = 0 := by
    intro t
    rw [star_smul, Matrix.mulVec_smul, hH', Matrix.smul_mulVec, hker]
    simp
  refine hinv z hz fun i t y => ?_
  obtain ⟨C, hC⟩ := hbd i
  have hd : Differentiable ℂ fun t : ℂ => Θ i (y + t • z) :=
    (hΘ i).comp ((differentiable_const _).add (differentiable_id.smul_const z))
  have hq : ∀ t : ℂ, ((y + t • z) ⬝ᵥ H'.mulVec (star (y + t • z))).re =
      (y ⬝ᵥ H'.mulVec (star y)).re := by
    intro t
    rw [GlobalTheory.ThetaPositivity.form_add_self hH'h, hker' t]
    simp
  have hb : Bornology.IsBounded (Set.range fun t : ℂ => Θ i (y + t • z)) := by
    refine isBounded_iff_forall_norm_le.2
      ⟨C * Real.exp (Real.pi / 2 * (y ⬝ᵥ H'.mulVec (star y)).re), ?_⟩
    rintro _ ⟨t, rfl⟩
    have h := hC (y + t • z)
    rwa [hq t] at h
  have h := hd.apply_eq_apply_of_bounded hb t 0
  simpa using h

end GlobalTheory.CompanionTheory.Ar.HodgeFormAna
