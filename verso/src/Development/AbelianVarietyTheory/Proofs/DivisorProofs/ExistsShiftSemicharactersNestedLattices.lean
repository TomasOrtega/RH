import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemicharShift

def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun y w => (hermForm Hm y w).im)
    (fun a b w => by simp [hermForm, add_dotProduct])
    (fun c a w => by simp [hermForm, smul_dotProduct, Complex.smul_im])
    (fun y a b => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c y a => by
      simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem imForm_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (y w : Fin g → ℂ) :
    imForm Hm y w = (hermForm Hm y w).im := rfl

/- English proof (translation)
Establish `hinj : Function.Injective (imForm Hm)`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `z hz`. Assume the negation of the conclusion as `hz0`. Establish `h1 : imForm Hm z (Complex.I • z) = 0` using `by rw [hz]; rfl`.

Establish `h2 : imForm Hm z (Complex.I • z) = -(hermForm Hm z z).re`. Rewrite using `[imForm_apply]`. Simplify using `[hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Matrix.mulVec_neg, dotProduct_neg, smul_eq_mul, Complex.mul_im]`. Use `hpos z hz0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hdim : Module.finrank ℝ (Fin g → ℂ) = Module.finrank ℝ ((Fin g → ℂ) →ₗ[ℝ] ℝ)` using `(Subspace.dual_finrank_eq).symm`. Conclude with `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj`.
-/
theorem imForm_surjective {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) :
    Function.Surjective (imForm Hm) := by
  have hinj : Function.Injective (imForm Hm) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    by_contra hz0
    have h1 : imForm Hm z (Complex.I • z) = 0 := by rw [hz]; rfl
    have h2 : imForm Hm z (Complex.I • z) = -(hermForm Hm z z).re := by
      rw [imForm_apply]
      simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Matrix.mulVec_neg,
        dotProduct_neg, smul_eq_mul, Complex.mul_im]
    have := hpos z hz0
    linarith
  have hdim : Module.finrank ℝ (Fin g → ℂ) = Module.finrank ℝ ((Fin g → ℂ) →ₗ[ℝ] ℝ) :=
    (Subspace.dual_finrank_eq).symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj

end GlobalTheory.SemicharShift

namespace GlobalTheory.SemicharShift

/- English proof (translation)
Use `haveI : IsZLattice ℝ Λ := ⟨hsp⟩`. Set `b` to `Module.Free.chooseBasis ℤ Λ`. Set `B` to `b.ofZLatticeBasis ℝ Λ`. Set `φ : (Fin g → ℂ) →ₗ[ℝ] ℝ` to `B.constr ℝ (fun j => Complex.arg (ρ (b j)) / (2 * Real.pi))`. Use `⟨φ, ?_⟩` and prove the remaining obligations.

Establish `hφb : ∀ j, φ (b j : Fin g → ℂ) = Complex.arg (ρ (b j)) / (2 * Real.pi)`. Introduce `j`. Establish `: (b j : Fin g → ℂ) = B j` using `by simp [B, Module.Basis.ofZLatticeBasis_apply]`. Rewrite using `[this]`. Conclude with `B.constr_basis ℝ _ j`.

Establish `hne : ∀ l, ρ l ≠ 0` using `fun l h => by simpa [h] using hn l`. Establish `h0 : ρ 0 = 1`. Use `hmul 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Establish `h` using `hne 0`.

Clear denominators, using `at this` for the nonvanishing conditions. Conclude with `this.symm`. Set `S : AddSubgroup Λ` to `{ carrier := {l | ρ l = Complex.exp (2 * Real.pi * Complex.I * (φ (l : Fin g → ℂ) : ℂ))} add_mem' := by`. Introduce `l m hl hm`. Simplify using `only [Set.mem_setOf_eq] at hl hm ⊢`.

Rewrite using `[hmul, hl, hm, ← Complex.exp_add]`. Use `congr 1`. Simplify using `only [Submodule.coe_add, map_add]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use the proof step `zero_mem' := by`. Simplify using `only [Set.mem_setOf_eq, ZeroMemClass.coe_zero, map_zero]`. Simplify using `[h0]`. Use the proof step `neg_mem' := by`. Introduce `l hl`.

Simplify using `only [Set.mem_setOf_eq] at hl ⊢`. Establish `h1 : ρ (-l) * ρ l = 1` using `by rw [← hmul, neg_add_cancel, h0]`. Establish `h2 : ρ (-l) = (ρ l)⁻¹` using `eq_inv_of_mul_eq_one_left h1`. Rewrite using `[h2, hl, ← Complex.exp_neg]`. Use `congr 1`.

Simplify using `only [Submodule.coe_neg, map_neg]`. Use `push_cast`. Use `ring }`. Establish `htop : (⊤ : Submodule ℤ Λ) ≤ S.toIntSubmodule`. Rewrite using `[← b.span_eq, Submodule.span_le]`.

Introduce and unpack `_ ⟨j, rfl⟩`. Use `show ρ (b j) = Complex.exp (2 * Real.pi * Complex.I * (φ (b j : Fin g → ℂ) : ℂ))`. Rewrite using `[hφb]`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `: 2 * (Real.pi : ℂ) * Complex.I * ((Complex.arg (ρ (b j)) / (2 * Real.pi) : ℝ) : ℂ) = (Complex.arg (ρ (b j)) : ℂ) * Complex.I` using `by push_cast; field_simp`.

Rewrite using `[this]`. Establish `h` using `Complex.norm_mul_exp_arg_mul_I (ρ (b j))`. Rewrite `h` using `[hn, Complex.ofReal_one, _root_.one_mul]`. Conclude with `h.symm`. Introduce `l`.

Conclude with `htop (Submodule.mem_top : l ∈ ⊤)`.
-/
theorem exists_linear_of_char {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hsp : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (ρ : Λ → ℂ) (hn : ∀ l, ‖ρ l‖ = 1)
    (hmul : ∀ l m, ρ (l + m) = ρ l * ρ m) :
    ∃ φ : (Fin g → ℂ) →ₗ[ℝ] ℝ, ∀ l : Λ,
      ρ l = Complex.exp (2 * Real.pi * Complex.I * (φ (l : Fin g → ℂ) : ℂ)) := by
  haveI : IsZLattice ℝ Λ := ⟨hsp⟩
  let b := Module.Free.chooseBasis ℤ Λ
  let B := b.ofZLatticeBasis ℝ Λ
  let φ : (Fin g → ℂ) →ₗ[ℝ] ℝ := B.constr ℝ (fun j => Complex.arg (ρ (b j)) / (2 * Real.pi))
  refine ⟨φ, ?_⟩
  have hφb : ∀ j, φ (b j : Fin g → ℂ) = Complex.arg (ρ (b j)) / (2 * Real.pi) := by
    intro j
    have : (b j : Fin g → ℂ) = B j := by simp [B, Module.Basis.ofZLatticeBasis_apply]
    rw [this]
    exact B.constr_basis ℝ _ j
  have hne : ∀ l, ρ l ≠ 0 := fun l h => by simpa [h] using hn l
  have h0 : ρ 0 = 1 := by
    have := hmul 0 0
    rw [add_zero] at this
    have h := hne 0
    field_simp at this
    exact this.symm
  let S : AddSubgroup Λ :=
    { carrier := {l | ρ l = Complex.exp (2 * Real.pi * Complex.I * (φ (l : Fin g → ℂ) : ℂ))}
      add_mem' := by
        intro l m hl hm
        simp only [Set.mem_setOf_eq] at hl hm ⊢
        rw [hmul, hl, hm, ← Complex.exp_add]
        congr 1
        simp only [Submodule.coe_add, map_add]
        push_cast; ring
      zero_mem' := by
        simp only [Set.mem_setOf_eq, ZeroMemClass.coe_zero, map_zero]
        simp [h0]
      neg_mem' := by
        intro l hl
        simp only [Set.mem_setOf_eq] at hl ⊢
        have h1 : ρ (-l) * ρ l = 1 := by rw [← hmul, neg_add_cancel, h0]
        have h2 : ρ (-l) = (ρ l)⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [h2, hl, ← Complex.exp_neg]
        congr 1
        simp only [Submodule.coe_neg, map_neg]
        push_cast; ring }
  have htop : (⊤ : Submodule ℤ Λ) ≤ S.toIntSubmodule := by
    rw [← b.span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show ρ (b j) = Complex.exp (2 * Real.pi * Complex.I * (φ (b j : Fin g → ℂ) : ℂ))
    rw [hφb]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have : 2 * (Real.pi : ℂ) * Complex.I * ((Complex.arg (ρ (b j)) / (2 * Real.pi) : ℝ) : ℂ)
        = (Complex.arg (ρ (b j)) : ℂ) * Complex.I := by
      push_cast; field_simp
    rw [this]
    have h := Complex.norm_mul_exp_arg_mul_I (ρ (b j))
    rw [hn, Complex.ofReal_one, _root_.one_mul] at h
    exact h.symm
  intro l
  exact htop (Submodule.mem_top : l ∈ ⊤)

end GlobalTheory.SemicharShift

namespace GlobalTheory.SemicharShift

/- English proof (translation)
Introduce `g Λ Λ₁ Hm χ χ₁ h hdisc hsp _hH hpos hχ hχ₁ hc hc₁`. Use `haveI := hdisc`. Establish `hne : ∀ l, χ₁ l ≠ 0` using `fun l e => by simpa [e] using hχ₁ l`. Establish `hne' : ∀ l, χ l ≠ 0` using `fun l e => by simpa [e] using hχ l`. Set `ρ : Λ → ℂ` to `fun l => χ l / χ₁ (Submodule.inclusion h l)`.

Establish `hn : ∀ l, ‖ρ l‖ = 1` using `fun l => by simp [ρ, norm_div, hχ, hχ₁]`. Establish `hmul : ∀ l m, ρ (l + m) = ρ l * ρ m`. Introduce `l m`. Simplify using `only [ρ]`. Rewrite using `[map_add, hc, hc₁]`.

Simplify using `only [Submodule.coe_inclusion]`. Establish `e1` using `hne (Submodule.inclusion h l)`. Establish `e2` using `hne (Submodule.inclusion h m)`. Establish `e3 : Complex.exp (Real.pi * Complex.I * (hermForm Hm l m).im) ≠ 0` using `Complex.exp_ne_zero _`. Clear the denominators using the available nonvanishing facts.

Take `⟨φ, hφ⟩` from `exists_linear_of_char Λ hsp ρ hn hmul`. Take `⟨a, ha⟩` from `imForm_surjective Hm hpos φ`. Use `⟨a, fun l => ?_⟩` and prove the remaining obligations. Establish `h1` using `hφ l`. Rewrite `h1` using `[← ha, imForm_apply]`.

Rewrite using `[← h1]`. Simplify using `only [ρ]`. Clear denominators, using `[hne (Submodule.inclusion h l)]` for the nonvanishing conditions.
-/
theorem exists_shift_of_semichar : ∀ (g : ℕ) (Λ Λ₁ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (χ₁ : Λ₁ → ℂ)
    (h : Λ ≤ Λ₁), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ l, ‖χ l‖ = 1) → (∀ l, ‖χ₁ l‖ = 1) →
    (∀ l m : Λ, χ (l + m) = χ l * χ m * Complex.exp (Real.pi * Complex.I * (hermForm Hm l m).im)) →
    (∀ l m : Λ₁, χ₁ (l + m) = χ₁ l * χ₁ m * Complex.exp (Real.pi * Complex.I * (hermForm Hm l m).im)) →
    ∃ a : Fin g → ℂ, ∀ l : Λ,
      χ l = χ₁ (Submodule.inclusion h l) * Complex.exp (2 * Real.pi * Complex.I * (hermForm Hm a l).im) := by
  intro g Λ Λ₁ Hm χ χ₁ h hdisc hsp _hH hpos hχ hχ₁ hc hc₁
  haveI := hdisc
  have hne : ∀ l, χ₁ l ≠ 0 := fun l e => by simpa [e] using hχ₁ l
  have hne' : ∀ l, χ l ≠ 0 := fun l e => by simpa [e] using hχ l
  let ρ : Λ → ℂ := fun l => χ l / χ₁ (Submodule.inclusion h l)
  have hn : ∀ l, ‖ρ l‖ = 1 := fun l => by simp [ρ, norm_div, hχ, hχ₁]
  have hmul : ∀ l m, ρ (l + m) = ρ l * ρ m := by
    intro l m
    simp only [ρ]
    rw [map_add, hc, hc₁]
    simp only [Submodule.coe_inclusion]
    have e1 := hne (Submodule.inclusion h l)
    have e2 := hne (Submodule.inclusion h m)
    have e3 : Complex.exp (Real.pi * Complex.I * (hermForm Hm l m).im) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  obtain ⟨φ, hφ⟩ := exists_linear_of_char Λ hsp ρ hn hmul
  obtain ⟨a, ha⟩ := imForm_surjective Hm hpos φ
  refine ⟨a, fun l => ?_⟩
  have h1 := hφ l
  rw [← ha, imForm_apply] at h1
  rw [← h1]
  simp only [ρ]
  field_simp [hne (Submodule.inclusion h l)]

end GlobalTheory.SemicharShift
