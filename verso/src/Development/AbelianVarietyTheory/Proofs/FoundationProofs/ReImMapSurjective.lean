import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqEqOfOmegaDensity

open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open scoped NNReal

noncomputable section

namespace GlobalTheory.CompactDualOmega

/- English proof (translation)
Simplify using `[Formalism.UG.Jpq, Matrix.fromBlocks_multiply]`.
-/
theorem Jpq_mul_self (P Q : ℕ) : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

/- English proof (translation)
Simplify using `[Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]`.
-/
theorem Jpq_conjTranspose (P Q : ℕ) : (Formalism.UG.Jpq P Q)ᴴ = Formalism.UG.Jpq P Q := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_lieU {P Q : ℕ} (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    X ∈ lieU P Q ↔ Xᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X = 0 := Iff.rfl

def reImMap (P Q : ℕ) :
    (lieU P Q × lieU P Q) →ₗ[ℝ] ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ) where
  toFun ab := entries ((ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))
  map_add' x y := by
    funext ij
    simp [entries]
    ring
  map_smul' c x := by
    funext ij
    simp [entries]
    ring

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce and unpack `⟨⟨a, ha⟩, ⟨b, hb⟩⟩ h`. Establish `h1 : a + Complex.I • b = 0`. Use extensionality with `i j`. Conclude with `congrFun h (i, j)`.

Establish `h2 : a = -(Complex.I • b)` using `eq_neg_of_add_eq_zero_left h1`. Establish `ha'` using `(mem_lieU a).1 ha`. Establish `hb'` using `(mem_lieU b).1 hb`. Establish `h3 : bᴴ * Formalism.UG.Jpq P Q = -(Formalism.UG.Jpq P Q * b)` using `eq_neg_of_add_eq_zero_left hb'`. Establish `h4 : (-(2 * Complex.I)) • (Formalism.UG.Jpq P Q * b) = 0`.

Rewrite using `[← ha', h2]`. Simplify using `only [conjTranspose_neg, conjTranspose_smul, Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, h3, Complex.star_def, Complex.conj_I]`. Use `module`. Establish `h5 : Formalism.UG.Jpq P Q * b = 0` using `(smul_eq_zero.1 h4).resolve_left (by simp)`. Establish `h6 : b = 0`.

Use `congrArg (Formalism.UG.Jpq P Q * ·) h5` as an intermediate fact. Simplify `this` using `[← Matrix.mul_assoc, Jpq_mul_self]`. Establish `h7 : a = 0` using `by rw [h2, h6]; simp`. Substitute `h6` using the available equality. Substitute `h7` using the available equality.

Both sides reduce to the same expression.
-/
theorem reImMap_injective (P Q : ℕ) : Function.Injective (reImMap P Q) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ h
  have h1 : a + Complex.I • b = 0 := by
    ext i j
    exact congrFun h (i, j)
  have h2 : a = -(Complex.I • b) := eq_neg_of_add_eq_zero_left h1
  have ha' := (mem_lieU a).1 ha
  have hb' := (mem_lieU b).1 hb
  have h3 : bᴴ * Formalism.UG.Jpq P Q = -(Formalism.UG.Jpq P Q * b) := eq_neg_of_add_eq_zero_left hb'
  have h4 : (-(2 * Complex.I)) • (Formalism.UG.Jpq P Q * b) = 0 := by
    rw [← ha', h2]
    simp only [conjTranspose_neg, conjTranspose_smul, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.smul_mul, Matrix.mul_smul, h3, Complex.star_def, Complex.conj_I]
    module
  have h5 : Formalism.UG.Jpq P Q * b = 0 :=
    (smul_eq_zero.1 h4).resolve_left (by simp)
  have h6 : b = 0 := by
    have := congrArg (Formalism.UG.Jpq P Q * ·) h5
    simpa [← Matrix.mul_assoc, Jpq_mul_self] using this
  have h7 : a = 0 := by rw [h2, h6]; simp
  subst h6
  subst h7
  rfl

/- English proof (translation)
Introduce `f`. Set `Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ` to `Matrix.of fun i j => f (i, j)`. Establish `hJ` using `Jpq_mul_self P Q`. Establish `hH` using `Jpq_conjTranspose P Q`. Establish `hl : ∀ X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ, Formalism.UG.Jpq P Q * (Formalism.UG.Jpq P Q * X) = X` using `fun X => by`.

Rewrite using `[← Matrix.mul_assoc, hJ, Matrix.one_mul]`. Use `⟨(⟨(1 / 2 : ℂ) • (Z - Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q), ?_⟩, ⟨(-(Complex.I / 2)) • (Z + Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q), ?_⟩), ?_⟩` and prove the remaining obligations. Rewrite using `[mem_lieU]`. Establish `: star (1 / 2 : ℂ) = 1 / 2` using `by simp`. Simplify using `only [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, hH, conjTranspose_conjTranspose, this, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hJ, hl, Matrix.mul_one]`.

Use `module`. Rewrite using `[mem_lieU]`. Establish `: star (-(Complex.I / 2)) = Complex.I / 2` using `by simp [neg_div]`. Simplify using `only [conjTranspose_smul, conjTranspose_add, conjTranspose_mul, hH, conjTranspose_conjTranspose, this, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hJ, hl, Matrix.mul_one]`. Use `module`.

Establish `h1 : Complex.I * (-(Complex.I / 2)) = 1 / 2`. Use `Complex.I_mul_I` as an intermediate fact. Take the linear combination `(-1 / 2 : ℂ) * this`. Establish `h2 : (1 / 2 : ℂ) • (Z - Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q) + Complex.I • (-(Complex.I / 2)) • (Z + Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q) = Z`. Rewrite using `[smul_smul, h1]`.

Use `module`. Conclude with `(congrArg entries h2).trans rfl`.
-/
theorem reImMap_surjective (P Q : ℕ) : Function.Surjective (reImMap P Q) := by
  intro f
  let Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := Matrix.of fun i j => f (i, j)
  have hJ := Jpq_mul_self P Q
  have hH := Jpq_conjTranspose P Q
  have hl : ∀ X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ,
      Formalism.UG.Jpq P Q * (Formalism.UG.Jpq P Q * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  refine ⟨(⟨(1 / 2 : ℂ) • (Z - Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q), ?_⟩,
    ⟨(-(Complex.I / 2)) • (Z + Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q), ?_⟩), ?_⟩
  · rw [mem_lieU]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    simp only [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, hH,
      conjTranspose_conjTranspose, this, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_assoc, hJ, hl, Matrix.mul_one]
    module
  · rw [mem_lieU]
    have : star (-(Complex.I / 2)) = Complex.I / 2 := by simp [neg_div]
    simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_mul, hH,
      conjTranspose_conjTranspose, this, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
      Matrix.mul_add, Matrix.mul_assoc, hJ, hl, Matrix.mul_one]
    module
  · have h1 : Complex.I * (-(Complex.I / 2)) = 1 / 2 := by
      have := Complex.I_mul_I
      linear_combination (-1 / 2 : ℂ) * this
    have h2 : (1 / 2 : ℂ) • (Z - Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q) +
        Complex.I • (-(Complex.I / 2)) • (Z + Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q) = Z := by
      rw [smul_smul, h1]
      module
    exact (congrArg entries h2).trans rfl

/- English proof (translation)
Introduce `P Q`. Establish `: BorelSpace (lieU P Q)` using `⟨rfl⟩`. Establish `: LocallyCompactSpace (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)` using `inferInstanceAs (LocallyCompactSpace ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))`. Establish `: SecondCountableTopology (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)` using `inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))`. Establish `: LocallyCompactSpace (lieU P Q)` using `(Submodule.closed_of_finiteDimensional (lieU P Q)).isClosedEmbedding_subtypeVal.locallyCompactSpace`.

Establish `: SecondCountableTopology (lieU P Q)` using `TopologicalSpace.Subtype.secondCountableTopology _`. Establish `: FiniteDimensional ℝ (lieU P Q × lieU P Q)` using `FiniteDimensional.of_injective (reImMap P Q) (reImMap_injective P Q)`. Set `e : (lieU P Q × lieU P Q) ≃L[ℝ] ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ)` to `(LinearEquiv.ofBijective (reImMap P Q) ⟨reImMap_injective P Q, reImMap_surjective P Q⟩).toContinuousLinearEquiv`. Set `l : Measure (lieU P Q)` to `Measure.addHaar`. Establish `: ((l.prod l).map e).IsAddHaarMeasure` using `e.isAddHaarMeasure_map _`.

Set `t : ℝ≥0` to `Measure.addHaarScalarFactor volume ((l.prod l).map e)`. Establish `ht : volume = t • (l.prod l).map e` using `Measure.isAddLeftInvariant_eq_smul _ _`. Establish `ht0 : 0 < t` using `Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _`. Establish `hs : NNReal.sqrt t ≠ 0` using `by simpa using ht0.ne'`. Use `⟨NNReal.sqrt t • l, Measure.IsAddHaarMeasure.nnreal_smul l hs, ?_⟩` and prove the remaining obligations.

Rewrite using `[Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, NNReal.mul_self_sqrt, Measure.map_smul]`. Conclude with `ht.symm`.
-/
theorem exists_isOmegaLeb : ∀ P Q : ℕ, ∃ lam : Measure (lieU P Q), IsOmegaLeb lam := by
  intro P Q
  have : BorelSpace (lieU P Q) := ⟨rfl⟩
  have : LocallyCompactSpace (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (LocallyCompactSpace ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  have : SecondCountableTopology (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  have : LocallyCompactSpace (lieU P Q) :=
    (Submodule.closed_of_finiteDimensional (lieU P Q)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (lieU P Q) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have : FiniteDimensional ℝ (lieU P Q × lieU P Q) :=
    FiniteDimensional.of_injective (reImMap P Q) (reImMap_injective P Q)
  let e : (lieU P Q × lieU P Q) ≃L[ℝ] ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ) :=
    (LinearEquiv.ofBijective (reImMap P Q)
      ⟨reImMap_injective P Q, reImMap_surjective P Q⟩).toContinuousLinearEquiv
  let l : Measure (lieU P Q) := Measure.addHaar
  have : ((l.prod l).map e).IsAddHaarMeasure := e.isAddHaarMeasure_map _
  let t : ℝ≥0 := Measure.addHaarScalarFactor volume ((l.prod l).map e)
  have ht : volume = t • (l.prod l).map e := Measure.isAddLeftInvariant_eq_smul _ _
  have ht0 : 0 < t := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hs : NNReal.sqrt t ≠ 0 := by simpa using ht0.ne'
  refine ⟨NNReal.sqrt t • l, Measure.IsAddHaarMeasure.nnreal_smul l hs, ?_⟩
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, NNReal.mul_self_sqrt,
    Measure.map_smul]
  exact ht.symm

end GlobalTheory.CompactDualOmega
