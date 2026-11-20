import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WittIndexAddOfIsWittLower
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LowerLiftsZeroOfWittIdxEqZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulVecMapResolution
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RegSch.EmbLevel

open Formalism.UG

section Ring

variable {A B : Type} [CommRing A] [CommRing B] {σ : A →+* A} {τ : B →+* B} {φ : A →+* B}

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Conclude with `hφ (M j i)`.
-/
theorem cT_map (hφ : ∀ x, φ (σ x) = τ (φ x)) {m p : Type} (M : Matrix m p A) :
    (cT σ M).map φ = cT τ (M.map φ) := by
  funext i j
  exact hφ (M j i)

/- English proof (translation)
Establish `h1 : b.1 * (b⁻¹).1 = 1` using `b.mul_inv`. Establish `h2 : (b⁻¹).1 * b.1 = 1` using `b.inv_mul`. Establish `h3 : cT τ (b⁻¹).1 * cT τ b.1 = 1` using `by rw [← cT_mul, h1, cT_one]`. Establish `h4 : cT τ b.1 * cT τ (b⁻¹).1 = 1` using `by rw [← cT_mul, h2, cT_one]`. Express the relevant statement in the definitionally equal form `cT τ ((b⁻¹).1 * g.1 * b.1) * 1 * ((b⁻¹).1 * g.1 * b.1) = 1 ↔ _`.

Establish `e : cT τ ((b⁻¹).1 * g.1 * b.1) * 1 * ((b⁻¹).1 * g.1 * b.1) = cT τ b.1 * (cT τ g.1 * (cT τ (b⁻¹).1 * (b⁻¹).1) * g.1) * b.1`. Simplify using `only [cT_mul, Matrix.mul_one, Matrix.mul_assoc]`. Rewrite using `[e]`. Generalize the expression as in `cT τ g.1 * (cT τ (b⁻¹).1 * (b⁻¹).1) * g.1 = X`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `rfl`. Rewrite using `[← Matrix.mul_assoc, h4, Matrix.one_mul, h2]`.
-/
theorem conj_mem_iff {n : ℕ} (b g : GL (Fin n) B) :
    b⁻¹ * g * b ∈ UJ τ (1 : Matrix (Fin n) (Fin n) B) ↔
      cT τ g.1 * (cT τ (b⁻¹).1 * (b⁻¹).1) * g.1 = cT τ (b⁻¹).1 * (b⁻¹).1 := by
  have h1 : b.1 * (b⁻¹).1 = 1 := b.mul_inv
  have h2 : (b⁻¹).1 * b.1 = 1 := b.inv_mul
  have h3 : cT τ (b⁻¹).1 * cT τ b.1 = 1 := by rw [← cT_mul, h1, cT_one]
  have h4 : cT τ b.1 * cT τ (b⁻¹).1 = 1 := by rw [← cT_mul, h2, cT_one]
  change cT τ ((b⁻¹).1 * g.1 * b.1) * 1 * ((b⁻¹).1 * g.1 * b.1) = 1 ↔ _
  have e : cT τ ((b⁻¹).1 * g.1 * b.1) * 1 * ((b⁻¹).1 * g.1 * b.1) =
      cT τ b.1 * (cT τ g.1 * (cT τ (b⁻¹).1 * (b⁻¹).1) * g.1) * b.1 := by
    simp only [cT_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [e]
  generalize cT τ g.1 * (cT τ (b⁻¹).1 * (b⁻¹).1) * g.1 = X
  constructor
  · intro h
    calc X = (cT τ (b⁻¹).1 * cT τ b.1) * X * (b.1 * (b⁻¹).1) := by rw [h1, h3, Matrix.one_mul, Matrix.mul_one]
      _ = cT τ (b⁻¹).1 * (cT τ b.1 * X * b.1) * (b⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Matrix.mul_one]
  · rintro rfl
    rw [← Matrix.mul_assoc, h4, Matrix.one_mul, h2]

/- English proof (translation)
Rewrite using `[conj_mem_iff, ← map_inv]`. Simplify using `only [Matrix.map_mul, cT_map hφ]`. Both sides reduce to the same expression.
-/
theorem conj_bc_mem_iff (hφ : ∀ x, φ (σ x) = τ (φ x)) {n : ℕ} (c g : GL (Fin n) A) :
    (bc φ c)⁻¹ * bc φ g * bc φ c ∈ UJ τ (1 : Matrix (Fin n) (Fin n) B) ↔
      (cT σ g.1 * (cT σ (c⁻¹).1 * (c⁻¹).1) * g.1).map φ = (cT σ (c⁻¹).1 * (c⁻¹).1).map φ := by
  rw [conj_mem_iff, ← map_inv]
  simp only [Matrix.map_mul, cT_map hφ]
  rfl

end Ring

section Lattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul a e => rfl`.
-/
theorem compInf_sigR (σ : E →ₐ[F] E) (w : InfinitePlace F) (x : AF F ⊗[F] E) :
    compInf F E w (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (compInf F E w x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => rfl

omit [NumberField E] in
/- English proof (translation)
Use `mem_levelAll.trans (and_congr Iff.rfl (forall_congr' fun w => ?_))` and prove the remaining obligations. Rewrite using `[mem_stabArch, matHom_projArch]`. Conclude with `conj_bc_mem_iff (compInf_sigR σ w) c _`.
-/
theorem mem_levelAll_iff (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (c : GL (Fin n) (AF F ⊗[F] E)) (g : GAd σ J) : g ∈ levelAll σ J L c ↔
    (∀ v y, y ∈ latLoc F L v ↔ (GlobalTheory.AdelicU.matHom _ σ J g).1.map (compFin F E v) *ᵥ y ∈ latLoc F L v) ∧
      ∀ w, (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) (GlobalTheory.AdelicU.matHom _ σ J g).1 *
          (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) (c⁻¹).1 * (c⁻¹).1) * (GlobalTheory.AdelicU.matHom _ σ J g).1).map (compInf F E w) =
        (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) (c⁻¹).1 * (c⁻¹).1).map (compInf F E w) := by
  refine mem_levelAll.trans (and_congr Iff.rfl (forall_congr' fun w => ?_))
  rw [mem_stabArch, matHom_projArch]
  exact conj_bc_mem_iff (compInf_sigR σ w) c _

end Lattice

variable {D : D7}

end GlobalTheory.RegSch.EmbLevel

end
