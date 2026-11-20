import Mathlib
import Formalism.PeriodIntegrals.UMultOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralSpanAlgebra.Burnside

noncomputable section

namespace PI.UMultOne.GelfSpanWork

open MeasureTheory Matrix ComplexConjugate

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ μ _ N ρ hC hI T`. Establish `hE : ∀ i j, Continuous (fun g => ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j)` using `fun i j => (continuous_apply j).comp ((continuous_apply i).comp hC)`. Establish `hInt : ∀ f : G → ℂ, Continuous f → Integrable f μ` using `fun f hf => hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)`. Establish `hIntP : ∀ f : G → ℂ, Continuous f → ∀ i j, Integrable (fun g => f g * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j) μ` using `fun f hf i j => hInt _ (hf.mul (hE i j))`. Set `S : Submodule ℂ (Matrix (Fin N) (Fin N) ℂ)` to `{ carrier := {T | ∃ f : G → ℂ, Continuous f ∧ ∀ i j, T i j = ∫ g, f g * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ} add_mem' := by`.

Introduce and unpack `A B ⟨f₁, hf₁, h₁⟩ ⟨f₂, hf₂, h₂⟩`. Use `⟨f₁ + f₂, hf₁.add hf₂, fun i j => ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.add_apply, Pi.add_apply, add_mul]`. Rewrite using `[integral_add (hIntP f₁ hf₁ i j) (hIntP f₂ hf₂ i j), h₁, h₂]`. Use the proof step `zero_mem' := ⟨0, continuous_const, fun i j => by simp⟩`.

Use the proof step `smul_mem' := by`. Introduce and unpack `c A ⟨f, hf, h⟩`. Use `⟨fun g => c * f g, continuous_const.mul hf, fun i j => ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.smul_apply, smul_eq_mul, mul_assoc]`. Rewrite using `[integral_const_mul, h] }`.

It suffices to establish `hS : S = ⊤ by`. Establish `: T ∈ S` using `hS ▸ Submodule.mem_top`. Conclude with `this`. Assume the negation of the conclusion as `hne`. Take `⟨ℓ, hℓ0, hℓS⟩` from `S.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hne)`.

Apply `hℓ0` to reduce the goal to its premises. Apply `functional_eq_zero ρ hI ℓ` to reduce the goal to its premises. Use `set h : G → ℂ := fun g => ℓ ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) with hh`. Establish `hhc : Continuous h` using `(LinearMap.continuous_of_finiteDimensional ℓ).comp hC`. Establish `hcoef : ∀ A : Matrix (Fin N) (Fin N) ℂ, ℓ A = ∑ i, ∑ j, A i j * ℓ (Matrix.single i j 1)`.

Introduce `A`. Use `conv_lhs => rw [Matrix.matrix_eq_sum_single A]`. Simplify using `only [map_sum]`. Use `Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))` and prove the remaining obligations. Rewrite using `[show Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℂ) by`.

Rewrite using `[Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]`. Set `M : Matrix (Fin N) (Fin N) ℂ` to `fun i j => ∫ g, conj (h g) * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ`. Establish `hM : M ∈ S` using `⟨fun g => conj (h g), Complex.continuous_conj.comp hhc, fun i j => rfl⟩`. Establish `hℓM : ℓ M = 0` using `hℓS hM`. Establish `hℓM' : ℓ M = ∫ g, ((Complex.normSq (h g) : ℝ) : ℂ) ∂μ`.

Rewrite using `[hcoef M]`. Simplify using `only [M]`. Establish `: ∀ g, ((Complex.normSq (h g) : ℝ) : ℂ) = ∑ i, ∑ j, conj (h g) * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j * ℓ (Matrix.single i j 1)`. Introduce `g`. Rewrite using `[Complex.normSq_eq_conj_mul_self, hh]`.

Simplify using `only`. Rewrite using `[hcoef ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ), Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[this]`. Establish `hcj : Continuous (fun g => conj (h g))` using `Complex.continuous_conj.comp hhc`. Use `symm`. Rewrite using `[integral_finsetSum _ (fun i _ => ?_)]`.

Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[integral_finsetSum _ (fun j _ => ?_)]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[integral_mul_const]`. Conclude with `(hIntP (fun g => conj (h g)) hcj i j).mul_const _`.

Conclude with `integrable_finsetSum _ (fun j _ => (hIntP (fun g => conj (h g)) hcj i j).mul_const _)`. Rewrite `hℓM'` using `[hℓM, integral_complex_ofReal]`. Establish `hR : ∫ g, Complex.normSq (h g) ∂μ = 0` using `by exact_mod_cast hℓM'.symm`. Introduce `g`. Assume the negation of the conclusion as `hg`.

Establish `hpos : 0 < ∫ x, Complex.normSq (h x) ∂μ` using `Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := g) (Complex.continuous_normSq.comp hhc) (HasCompactSupport.of_compactSpace _) (fun x => Complex.normSq_nonneg _) (by simpa [Complex.normSq_eq_zero] using hg)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem intSpan' : IntSpan := by
  intro G _ _ _ _ _ _ _ _ μ _ N ρ hC hI T

  have hE : ∀ i j, Continuous (fun g => ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j) :=
    fun i j => (continuous_apply j).comp ((continuous_apply i).comp hC)
  have hInt : ∀ f : G → ℂ, Continuous f → Integrable f μ := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hIntP : ∀ f : G → ℂ, Continuous f → ∀ i j,
      Integrable (fun g => f g * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j) μ :=
    fun f hf i j => hInt _ (hf.mul (hE i j))

  let S : Submodule ℂ (Matrix (Fin N) (Fin N) ℂ) :=
    { carrier := {T | ∃ f : G → ℂ, Continuous f ∧
        ∀ i j, T i j = ∫ g, f g * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ}
      add_mem' := by
        rintro A B ⟨f₁, hf₁, h₁⟩ ⟨f₂, hf₂, h₂⟩
        refine ⟨f₁ + f₂, hf₁.add hf₂, fun i j => ?_⟩
        simp only [Matrix.add_apply, Pi.add_apply, add_mul]
        rw [integral_add (hIntP f₁ hf₁ i j) (hIntP f₂ hf₂ i j), h₁, h₂]
      zero_mem' := ⟨0, continuous_const, fun i j => by simp⟩
      smul_mem' := by
        rintro c A ⟨f, hf, h⟩
        refine ⟨fun g => c * f g, continuous_const.mul hf, fun i j => ?_⟩
        simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc]
        rw [integral_const_mul, h] }
  suffices hS : S = ⊤ by
    have : T ∈ S := hS ▸ Submodule.mem_top
    exact this
  by_contra hne
  obtain ⟨ℓ, hℓ0, hℓS⟩ := S.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hne)
  apply hℓ0
  apply functional_eq_zero ρ hI ℓ

  set h : G → ℂ := fun g => ℓ ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) with hh
  have hhc : Continuous h := (LinearMap.continuous_of_finiteDimensional ℓ).comp hC
  have hcoef : ∀ A : Matrix (Fin N) (Fin N) ℂ,
      ℓ A = ∑ i, ∑ j, A i j * ℓ (Matrix.single i j 1) := by
    intro A
    conv_lhs => rw [Matrix.matrix_eq_sum_single A]
    simp only [map_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [show Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℂ) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
  let M : Matrix (Fin N) (Fin N) ℂ := fun i j =>
    ∫ g, conj (h g) * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ
  have hM : M ∈ S := ⟨fun g => conj (h g), Complex.continuous_conj.comp hhc, fun i j => rfl⟩
  have hℓM : ℓ M = 0 := hℓS hM
  have hℓM' : ℓ M = ∫ g, ((Complex.normSq (h g) : ℝ) : ℂ) ∂μ := by
    rw [hcoef M]
    simp only [M]
    have : ∀ g, ((Complex.normSq (h g) : ℝ) : ℂ) = ∑ i, ∑ j,
        conj (h g) * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j *
          ℓ (Matrix.single i j 1) := by
      intro g
      rw [Complex.normSq_eq_conj_mul_self, hh]
      simp only
      rw [hcoef ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    simp_rw [this]
    have hcj : Continuous (fun g => conj (h g)) := Complex.continuous_conj.comp hhc
    symm
    rw [integral_finsetSum _ (fun i _ => ?_)]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_finsetSum _ (fun j _ => ?_)]
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [integral_mul_const]
      · exact (hIntP (fun g => conj (h g)) hcj i j).mul_const _
    · exact integrable_finsetSum _ (fun j _ => (hIntP (fun g => conj (h g)) hcj i j).mul_const _)
  rw [hℓM, integral_complex_ofReal] at hℓM'
  have hR : ∫ g, Complex.normSq (h g) ∂μ = 0 := by exact_mod_cast hℓM'.symm
  intro g
  by_contra hg
  have hpos : 0 < ∫ x, Complex.normSq (h x) ∂μ :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := g)
      (Complex.continuous_normSq.comp hhc) (HasCompactSupport.of_compactSpace _)
      (fun x => Complex.normSq_nonneg _) (by simpa [Complex.normSq_eq_zero] using hg)
  linarith

end PI.UMultOne.GelfSpanWork
