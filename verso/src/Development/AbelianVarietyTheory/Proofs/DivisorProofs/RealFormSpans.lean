import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.RealFormSpan

/- English proof (translation)
Unfold `Jm`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem jm_sq (n : ℕ) (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

/- English proof (translation)
Unfold `Jm`. Rewrite using `[Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `by_cases h : ε a = true <;> simp [h]`.
-/
theorem jm_ct (n : ℕ) (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]

/- English proof (translation)
Unfold `inG`. Establish `h1` using `jm_sq n ε`. Establish `h2` using `jm_ct n ε`. Establish `h1' : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, h1, Matrix.one_mul]`.

Simplify using `only [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, h2]`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub]`. Simplify using `only [Matrix.mul_assoc, h1, h1', Matrix.mul_one]`. Establish `hs : star (1/2 : ℂ) = 1/2` using `by simp`. Rewrite using `[hs]`.

Use `module`.
-/
theorem inG_re (n : ℕ) (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inG ε ((1/2 : ℂ) • (Z - Jm ε * Zᴴ * Jm ε)) := by
  unfold inG
  have h1 := jm_sq n ε
  have h2 := jm_ct n ε
  have h1' : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  simp only [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, h2]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub]
  simp only [Matrix.mul_assoc, h1, h1', Matrix.mul_one]
  have hs : star (1/2 : ℂ) = 1/2 := by simp
  rw [hs]
  module

/- English proof (translation)
Unfold `inG`. Establish `h1` using `jm_sq n ε`. Establish `h2` using `jm_ct n ε`. Establish `h1' : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, h1, Matrix.one_mul]`.

Simplify using `only [conjTranspose_smul, conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose, h2]`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add]`. Simplify using `only [Matrix.mul_assoc, h1, h1', Matrix.mul_one]`. Establish `hs : star (-Complex.I / 2) = Complex.I / 2` using `by simp [Complex.conj_I]`. Rewrite using `[hs]`.

Use `module`.
-/
theorem inG_im (n : ℕ) (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inG ε ((-Complex.I/2 : ℂ) • (Z + Jm ε * Zᴴ * Jm ε)) := by
  unfold inG
  have h1 := jm_sq n ε
  have h2 := jm_ct n ε
  have h1' : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose, h2]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add]
  simp only [Matrix.mul_assoc, h1, h1', Matrix.mul_one]
  have hs : star (-Complex.I / 2) = Complex.I / 2 := by simp [Complex.conj_I]
  rw [hs]
  module

end GlobalTheory.RealFormSpan

open GlobalTheory.RealFormSpan in
/- English proof (translation)
Introduce `n ε W _ _ u h a b`. Set `f : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] W` to `{ toFun := fun X => ∑ a, ∑ b, X a b • u a b map_add' := by intro X Y; simp [add_smul, Finset.sum_add_distrib] map_smul' := by intro c X; simp [Finset.smul_sum, smul_smul] }`. Establish `hZ : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Z = (1/2 : ℂ) • (Z - Jm ε * Zᴴ * Jm ε) + Complex.I • ((-Complex.I/2 : ℂ) • (Z + Jm ε * Zᴴ * Jm ε))`. Introduce `Z`. Rewrite using `[smul_smul]`.

Establish `: Complex.I * (-Complex.I / 2) = (1/2 : ℂ)`. Use `Complex.I_mul_I` as an intermediate fact. Take the linear combination `(-1/2:ℂ) * this`. Rewrite using `[this, smul_sub, smul_add]`. Rewrite using `[show ((1/2 : ℂ) • Z - (1/2:ℂ) • (Jm ε * Zᴴ * Jm ε) + ((1/2:ℂ) • Z + (1/2:ℂ) • (Jm ε * Zᴴ * Jm ε))) = ((1/2 : ℂ) + 1/2) • Z by rw [add_smul]; abel]`.

Evaluate the numerical expressions. Establish `hf : ∀ Z, f Z = 0`. Introduce `Z`. Establish `e1` using `h _ (inG_re n ε Z)`. Establish `e2` using `h _ (inG_im n ε Z)`.

Express the relevant statement in the definitionally equal form `f _ = 0 at e1 e2`. Rewrite using `[hZ Z, map_add, e1, map_smul, e2, smul_zero, add_zero]`. Use `hf (Matrix.single a b 1)` as an intermediate fact. Simplify `this` using `[f, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']`.
-/
theorem GlobalTheory.realForm_spans : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [AddCommGroup W] [Module ℂ W] (u : Fin n → Fin n → W), (∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → ∑ a, ∑ b, X a b • u a b = 0) → ∀ a b, u a b = 0 := by
  intro n ε W _ _ u h a b
  let f : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] W :=
    { toFun := fun X => ∑ a, ∑ b, X a b • u a b
      map_add' := by intro X Y; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro c X; simp [Finset.smul_sum, smul_smul] }
  have hZ : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Z = (1/2 : ℂ) • (Z - Jm ε * Zᴴ * Jm ε)
      + Complex.I • ((-Complex.I/2 : ℂ) • (Z + Jm ε * Zᴴ * Jm ε)) := by
    intro Z
    rw [smul_smul]
    have : Complex.I * (-Complex.I / 2) = (1/2 : ℂ) := by
      have := Complex.I_mul_I; linear_combination (-1/2:ℂ) * this
    rw [this, smul_sub, smul_add]
    rw [show ((1/2 : ℂ) • Z - (1/2:ℂ) • (Jm ε * Zᴴ * Jm ε) + ((1/2:ℂ) • Z + (1/2:ℂ) • (Jm ε * Zᴴ * Jm ε)))
      = ((1/2 : ℂ) + 1/2) • Z by rw [add_smul]; abel]
    norm_num
  have hf : ∀ Z, f Z = 0 := by
    intro Z
    have e1 := h _ (inG_re n ε Z)
    have e2 := h _ (inG_im n ε Z)
    change f _ = 0 at e1 e2
    rw [hZ Z, map_add, e1, map_smul, e2, smul_zero, add_zero]
  have := hf (Matrix.single a b 1)
  simpa [f, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq'] using this
