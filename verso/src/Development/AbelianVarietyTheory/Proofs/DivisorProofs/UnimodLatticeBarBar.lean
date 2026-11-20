import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularPosDefAdjointActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmFieldTraceFormGramMatrixPosDefStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]`.
-/
theorem unimodLattice_bar_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (a : 𝓞 E) :
    H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[H.bar_eq]`. Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[IsCMField.complexEmbedding_complexConj]`.

Establish `hsq : φ (H.rt : E) ^ 2 = -(H.d : ℂ)`. Use `congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq` as an intermediate fact. Simplify using `using this`. Establish `hd : (7 : ℝ) ≤ H.d`. Use `H.d_mod` as an intermediate fact.

Establish `: 7 ≤ H.d` using `by omega`. Conclude with `this` after adjusting the coercions. Use `set z := φ (H.rt : E) with hz`. Establish `hre` using `congrArg Complex.re hsq`. Establish `him` using `congrArg Complex.im hsq`.

Simplify using `[pow_two] at hre him`. Establish `hx : z.re = 0`. Establish `hm : z.re * z.im = 0` using `by linarith`. Break down `mul_eq_zero.1 hm with h | h` into its components or cases. Conclude with `h`.

Rewrite `hre` using `[h]`. Use polynomial arithmetic with `[sq_nonneg z.re]`. Apply the tactic sequence `have key : starRingEnd ℂ z = -z := by apply Complex.ext <;> simp [hx]`. Rewrite `key` using `[hz]`. Simplify using `using key`.
-/
theorem unimodLattice_bar_rt {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.bar H.rt = -H.rt := by
  apply RingOfIntegers.ext
  rw [H.bar_eq]
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj]
  have hsq : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
    simpa using this
  have hd : (7 : ℝ) ≤ H.d := by
    have := H.d_mod
    have : 7 ≤ H.d := by omega
    exact_mod_cast this
  set z := φ (H.rt : E) with hz
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im hsq
  simp [pow_two] at hre him
  have hx : z.re = 0 := by
    have hm : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.1 hm with h | h
    · exact h
    · rw [h] at hre; nlinarith [sq_nonneg z.re]
  have key : starRingEnd ℂ z = -z := by apply Complex.ext <;> simp [hx]
  rw [hz] at key
  simpa using key

/- English proof (translation)
Establish `h1` using `H.two_weight_eq_one_add_root`. Establish `h2 : 2 * H.bar H.w0 = 1 - H.rt`. Use `congrArg H.bar h1` as an intermediate fact. Rewrite `this` using `[map_mul, map_add, map_one, unimodLattice_bar_rt, map_ofNat]`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h3 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1`. Rewrite using `[mul_add, h1, h2]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `mul_left_cancel₀ two_ne_zero h3`.
-/
theorem unimodLattice_w0_add {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 + H.bar H.w0 = 1 := by
  have h1 := H.two_weight_eq_one_add_root
  have h2 : 2 * H.bar H.w0 = 1 - H.rt := by
    have := congrArg H.bar h1
    rw [map_mul, map_add, map_one, unimodLattice_bar_rt, map_ofNat] at this
    rw [this]; ring
  have h3 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by
    rw [mul_add, h1, h2]; ring
  exact mul_left_cancel₀ two_ne_zero h3

/- English proof (translation)
Introduce `E _ _ _ H`. Take `⟨m, B0, ρ0, hm, hsym, hpd, hadj⟩` from `GlobalTheory.T.exists_cmField_traceForm_gram_matrix_posDef E H`. Take `⟨r, b, ρ, hr, hbs, hbpd, hbu, hbadj⟩` from `GlobalTheory.T.exists_unimodular_posDef_form_adjoint_rep_of_posDef (𝓞 E) (H.bar : 𝓞 E →+* 𝓞 E) (unimodLattice_bar_bar H) m B0 ρ0 hm hsym hpd hadj`. Establish `hW : b * ρ H.w0 + (b * ρ H.w0).transpose = b`. Rewrite using `[Matrix.transpose_mul, hbs, hbadj, ← Matrix.mul_add, ← map_add]`.

Use `erw [unimodLattice_w0_add H]`. Rewrite using `[map_one, Matrix.mul_one]`. Use `⟨r, b * ρ H.w0, ρ, hr, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hW]`. Conclude with `hbpd`.

Rewrite using `[hW]`. Conclude with `hbu`. Introduce `a`. Rewrite using `[hW]`. Conclude with `hbadj a`.

Rewrite using `[hW]`.
-/
theorem unimodLattice :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∃ (r : ℕ) (W : Matrix (Fin r) (Fin r) ℤ) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), 1 ≤ r ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ IsUnit (W + W.transpose).det ∧ (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) ∧ W = (W + W.transpose) * ρ H.w0 := by
  intro E _ _ _ H
  obtain ⟨m, B0, ρ0, hm, hsym, hpd, hadj⟩ := GlobalTheory.T.exists_cmField_traceForm_gram_matrix_posDef E H
  obtain ⟨r, b, ρ, hr, hbs, hbpd, hbu, hbadj⟩ :=
    GlobalTheory.T.exists_unimodular_posDef_form_adjoint_rep_of_posDef (𝓞 E) (H.bar : 𝓞 E →+* 𝓞 E) (unimodLattice_bar_bar H) m B0 ρ0 hm hsym hpd hadj
  have hW : b * ρ H.w0 + (b * ρ H.w0).transpose = b := by
    rw [Matrix.transpose_mul, hbs, hbadj, ← Matrix.mul_add, ← map_add]
    erw [unimodLattice_w0_add H]
    rw [map_one, Matrix.mul_one]
  refine ⟨r, b * ρ H.w0, ρ, hr, ?_, ?_, ?_, ?_⟩
  · rw [hW]; exact hbpd
  · rw [hW]; exact hbu
  · intro a; rw [hW]; exact hbadj a
  · rw [hW]

end GlobalTheory.Mum
