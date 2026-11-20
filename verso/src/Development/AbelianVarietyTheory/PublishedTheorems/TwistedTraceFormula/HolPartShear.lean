import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation

noncomputable section

open MeasureTheory Matrix Complex
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory.Published.Metaplectic.Model

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Rewrite using `[SymplecticGroup.mem_iff]`. Simplify using `[Matrix.J, fromBlocks_transpose, fromBlocks_multiply, hC]`.
-/
theorem shear_mem (C : Matrix ι ι ℝ) (hC : Cᵀ = C) : fromBlocks 1 0 C 1 ∈ symplecticGroup ι ℝ := by
  rw [SymplecticGroup.mem_iff]
  simp [Matrix.J, fromBlocks_transpose, fromBlocks_multiply, hC]

def chirp (C : Matrix ι ι ℝ) (f : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  fun x => cexp (-π * I * ((x ⬝ᵥ C *ᵥ x : ℝ) : ℂ)) * f x

/- English proof (translation)
Use function extensionality and compare the values at `x`. Establish `hs : p ⬝ᵥ C *ᵥ x = x ⬝ᵥ C *ᵥ p`. Rewrite using `[dotProduct_mulVec, ← hC, vecMul_transpose, hC, dotProduct_comm]`. Rewrite using `[act_fromBlocks, rho_apply, h]`. Simplify using `only [chirp, rho_apply, one_mulVec, zero_mulVec, add_zero, mulVec_add, dotProduct_add, add_dotProduct, hs]`.

Rewrite using `[← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chirp_rho (C : Matrix ι ι ℝ) (hC : Cᵀ = C) (p q : ι → ℝ) (φ ψ : 𝓢(ι → ℝ, ℂ)) (h : ⇑ψ = chirp C φ) :
    chirp C (rho (p, q) φ) = rho (act (fromBlocks 1 0 C 1) (p, q)) ψ := by
  funext x
  have hs : p ⬝ᵥ C *ᵥ x = x ⬝ᵥ C *ᵥ p := by
    rw [dotProduct_mulVec, ← hC, vecMul_transpose, hC, dotProduct_comm]
  rw [act_fromBlocks, rho_apply, h]
  simp only [chirp, rho_apply, one_mulVec, zero_mulVec, add_zero, mulVec_add, dotProduct_add, add_dotProduct, hs]
  rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  push_cast
  ring

omit [Fintype ι] in
/- English proof (translation)
Simplify using `[holPart]`. Evaluate the numerical expressions.
-/
theorem holPart_shear (C : Matrix ι ι ℝ) (i : ι) : holPart (fromBlocks 1 0 C 1) i i = (2 + I * C i i) / 2 := by
  simp [holPart]; norm_num

/- English proof (translation)
Establish `hc : ∀ x : ℝ, conj (cexp (-π * x ^ 2)) = cexp (-π * x ^ 2)`. Introduce `x`. Rewrite using `[← Complex.exp_conj]`. Simplify using the standard rewrite rules. Establish `e1 : ∀ x : ℝ, cexp (-π * I * (c * x ^ 2)) * cexp (-π * x ^ 2) * conj (cexp (-π * x ^ 2)) = cexp (-(π * (2 + I * c)) * x ^ 2)`.

Introduce `x`. Rewrite using `[hc, ← Complex.exp_add, ← Complex.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ∀ x : ℝ, cexp (-π * x ^ 2) * conj (cexp (-π * x ^ 2)) = cexp (-(π * 2) * x ^ 2)`.

Introduce `x`. Rewrite using `[hc, ← Complex.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[e1, e2]`.

Establish `hp` using `Real.pi_pos`. Rewrite using `[integral_gaussian_complex (by simp; positivity), integral_gaussian_complex (by simp; positivity)]`. Establish `h2 : ∀ z : ℂ, (z ^ (1 / 2 : ℂ)) ^ 2 = z` using `fun z => by`. Use `Complex.cpow_nat_inv_pow z (n := 2) two_ne_zero` as an intermediate fact. Simplify using `using this`.

Rewrite using `[h2, h2]`. Establish `h3 : (2 + I * c : ℂ) ≠ 0`. Introduce `h`. Use `congrArg Complex.re h` as an intermediate fact. Simplify using `at this`.

Establish `h4 : (π : ℂ) ≠ 0` using `by exact_mod_cast hp.ne'`. Clear the denominators using the available nonvanishing facts.
-/
theorem shear_coeff (c : ℝ) :
    (∫ x : ℝ, cexp (-π * I * (c * x ^ 2)) * cexp (-π * x ^ 2) * conj (cexp (-π * x ^ 2))) ^ 2 * ((2 + I * c) / 2) =
      (∫ x : ℝ, cexp (-π * x ^ 2) * conj (cexp (-π * x ^ 2))) ^ 2 := by
  have hc : ∀ x : ℝ, conj (cexp (-π * x ^ 2)) = cexp (-π * x ^ 2) := by
    intro x; rw [← Complex.exp_conj]; simp
  have e1 : ∀ x : ℝ, cexp (-π * I * (c * x ^ 2)) * cexp (-π * x ^ 2) * conj (cexp (-π * x ^ 2)) =
      cexp (-(π * (2 + I * c)) * x ^ 2) := by
    intro x; rw [hc, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  have e2 : ∀ x : ℝ, cexp (-π * x ^ 2) * conj (cexp (-π * x ^ 2)) = cexp (-(π * 2) * x ^ 2) := by
    intro x; rw [hc, ← Complex.exp_add]; congr 1; ring
  simp_rw [e1, e2]
  have hp := Real.pi_pos
  rw [integral_gaussian_complex (by simp; positivity), integral_gaussian_complex (by simp; positivity)]
  have h2 : ∀ z : ℂ, (z ^ (1 / 2 : ℂ)) ^ 2 = z := fun z => by
    have := Complex.cpow_nat_inv_pow z (n := 2) two_ne_zero
    simpa using this
  rw [h2, h2]
  have h3 : (2 + I * c : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h4 : (π : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp

def sgnRep (E : Type) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [ContinuousConstSMul ℂ E] :
    ℤˣ →* (E →L[ℂ] E) where
  toFun g := (((g : ℤ) : ℂ)) • (1 : E →L[ℂ] E)
  map_one' := by simp
  map_mul' g h := by ext; simp [smul_smul, mul_comm]

/- English proof (translation)
Establish `hs : Subsingleton (symplecticGroup ι ℝ)` using `⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩`. Establish `hsq : ∀ g : ℤˣ, (((g : ℤ) : ℂ)) ^ 2 = 1`. Apply the tactic sequence `intro g; rcases Int.units_eq_one_or g with rfl | rfl <;> simp`. Set `φ₀ : 𝓢(ι → ℝ, ℂ)` to `(HasCompactSupport.of_compactSpace (fun _ : ι → ℝ => (1 : ℂ))).toSchwartzMap contDiff_const`. Use `⟨ℤˣ, inferInstance, inferInstance, inferInstance, 1, sgnRep _, sgnRep _, φ₀, fun a => ⟨1, Subsingleton.elim _ _⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x`. Use `⟨inferInstance, Set.univ, trivial, isOpen_univ, isOpen_discrete _, ?_⟩` and prove the remaining obligations. Establish `: Finite ((1 : ℤˣ →* symplecticGroup ι ℝ) ⁻¹' {x})` using `inferInstance`. Use `⟨Equiv.toHomeomorphOfDiscrete { toFun := fun g => (⟨x, trivial⟩, ⟨g.1, Subsingleton.elim _ _⟩) invFun := fun y => ⟨y.2.1, trivial⟩ left_inv := fun _ => rfl right_inv := fun y => Prod.ext (Subtype.ext (Subsingleton.elim _ _)) rfl }, fun _ => Subsingleton.elim _ _⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.

Introduce `g f`. Apply the tactic sequence `rcases Int.units_eq_one_or g with rfl | rfl <;> simp [sgnRep]`. Introduce `f`. Conclude with `continuous_of_discreteTopology`. Introduce `g φ`.

Express the relevant statement in the definitionally equal form `((g : ℤ) : ℂ) • SchwartzMap.toLpCLM ℂ ℂ 2 volume φ = SchwartzMap.toLpCLM ℂ ℂ 2 volume (((g : ℤ) : ℂ) • φ)`. Rewrite using `[map_smul]`. Express the relevant statement in the definitionally equal form `Continuous fun x : ℤˣ × 𝓢(ι → ℝ, ℂ) => (((x.1 : ℤ) : ℂ)) • x.2`. Conclude with `((continuous_of_discreteTopology (f := fun g : ℤˣ => ((g : ℤ) : ℂ))).comp continuous_fst).smul continuous_snd`. Introduce `g w φ`.

Rewrite using `[Subsingleton.elim (act _ w) w]`. Simplify using `[sgnRep]`. Introduce `g _ hg φ`. Break down `Int.units_eq_one_or g with rfl | rfl` into its components or cases. Conclude with `absurd rfl hg`.

Simplify using `[sgnRep]`. Introduce `x`. Simplify using `[φ₀, dotProduct]`. Introduce `g`. Apply the tactic sequence `rcases Int.units_eq_one_or g with rfl | rfl <;> simp [sgnRep, integral_neg]`.

Introduce `g _`. Conclude with `⟨_, by simp [hsq g], rfl⟩`.
-/
theorem empty_case (ι : Type) [Fintype ι] [DecidableEq ι] [IsEmpty ι] :
    ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G)
      (pr : G →* symplecticGroup ι ℝ)
      (Ω : G →* (Lp ℂ 2 (volume : Measure (ι → ℝ)) →L[ℂ] Lp ℂ 2 (volume : Measure (ι → ℝ))))
      (ω : G →* (𝓢(ι → ℝ, ℂ) →L[ℂ] 𝓢(ι → ℝ, ℂ))) (φ₀ : 𝓢(ι → ℝ, ℂ)),
      Function.Surjective pr ∧ IsCoveringMap pr ∧ Nat.card pr.ker = 2 ∧
      (∀ g f, ‖Ω g f‖ = ‖f‖) ∧ (∀ f, Continuous fun g => Ω g f) ∧
      (∀ g (φ : 𝓢(ι → ℝ, ℂ)), Ω g (φ.toLp 2) = (ω g φ).toLp 2) ∧
      (Continuous fun x : G × 𝓢(ι → ℝ, ℂ) => ω x.1 x.2) ∧
      (∀ g w φ, ω g (rho w φ) = rho (act (pr g).1 w) (ω g φ)) ∧
      (∀ g, pr g = 1 → g ≠ 1 → ∀ φ, ω g φ = -φ) ∧
      (∀ x, φ₀ x = cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ))) ∧
      (∀ g, (∫ x, ω g φ₀ x * conj (φ₀ x)) ^ 2 * (holPart (pr g).1).det = (∫ x, φ₀ x * conj (φ₀ x)) ^ 2) ∧
      (∀ g, (pr g).1ᵀ * (pr g).1 = 1 → ∃ c : ℂ, c ^ 2 * (holPart (pr g).1).det = 1 ∧ ω g φ₀ = c • φ₀) := by
  have hs : Subsingleton (symplecticGroup ι ℝ) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  have hsq : ∀ g : ℤˣ, (((g : ℤ) : ℂ)) ^ 2 = 1 := by
    intro g; rcases Int.units_eq_one_or g with rfl | rfl <;> simp
  let φ₀ : 𝓢(ι → ℝ, ℂ) := (HasCompactSupport.of_compactSpace (fun _ : ι → ℝ => (1 : ℂ))).toSchwartzMap contDiff_const
  refine ⟨ℤˣ, inferInstance, inferInstance, inferInstance, 1, sgnRep _, sgnRep _, φ₀, fun a => ⟨1, Subsingleton.elim _ _⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    refine ⟨inferInstance, Set.univ, trivial, isOpen_univ, isOpen_discrete _, ?_⟩
    have : Finite ((1 : ℤˣ →* symplecticGroup ι ℝ) ⁻¹' {x}) := inferInstance
    refine ⟨Equiv.toHomeomorphOfDiscrete
      { toFun := fun g => (⟨x, trivial⟩, ⟨g.1, Subsingleton.elim _ _⟩)
        invFun := fun y => ⟨y.2.1, trivial⟩
        left_inv := fun _ => rfl
        right_inv := fun y => Prod.ext (Subtype.ext (Subsingleton.elim _ _)) rfl }, fun _ => Subsingleton.elim _ _⟩
  · simp
  · intro g f
    rcases Int.units_eq_one_or g with rfl | rfl <;> simp [sgnRep]
  · intro f; exact continuous_of_discreteTopology
  · intro g φ
    change ((g : ℤ) : ℂ) • SchwartzMap.toLpCLM ℂ ℂ 2 volume φ = SchwartzMap.toLpCLM ℂ ℂ 2 volume (((g : ℤ) : ℂ) • φ)
    rw [map_smul]
  · change Continuous fun x : ℤˣ × 𝓢(ι → ℝ, ℂ) => (((x.1 : ℤ) : ℂ)) • x.2
    exact ((continuous_of_discreteTopology (f := fun g : ℤˣ => ((g : ℤ) : ℂ))).comp continuous_fst).smul continuous_snd
  · intro g w φ
    rw [Subsingleton.elim (act _ w) w]
    simp [sgnRep]
  · intro g _ hg φ
    rcases Int.units_eq_one_or g with rfl | rfl
    · exact absurd rfl hg
    · simp [sgnRep]
  · intro x; simp [φ₀, dotProduct]
  · intro g
    rcases Int.units_eq_one_or g with rfl | rfl <;> simp [sgnRep, integral_neg]
  · intro g _
    exact ⟨_, by simp [hsq g], rfl⟩

end GlobalTheory.Published.Metaplectic.Model

end
