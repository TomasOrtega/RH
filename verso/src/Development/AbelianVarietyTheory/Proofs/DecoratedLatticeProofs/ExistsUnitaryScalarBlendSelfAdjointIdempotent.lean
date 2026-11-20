import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKuProj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnsCharacterEqLinkedFrameCharacter
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntAfApproxInterUnitConj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalWIdent
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnitTorus

/- English proof (translation)
Establish `e : ∀ (N : Matrix n n A) (u v : n → A), Formalism.UG.hform σ N u v = (σ ∘ u) ⬝ᵥ (N *ᵥ v)`. Introduce `N u v`. Simplify using `only [Formalism.UG.hform, dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]`. Establish `hσ : σ ∘ (M *ᵥ x) = M.map σ *ᵥ (σ ∘ x)`. Use function extensionality and compare the values at `i`.

Conclude with `RingHom.map_mulVec σ M x i`. Rewrite using `[e, e, hσ, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Formalism.UG.cT, Matrix.mul_assoc]`.
-/
theorem hform_mulVec_two {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J M M' : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M' *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M') x y := by
  have e : ∀ (N : Matrix n n A) (u v : n → A), Formalism.UG.hform σ N u v = (σ ∘ u) ⬝ᵥ (N *ᵥ v) := by
    intro N u v
    simp only [Formalism.UG.hform, dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]
  have hσ : σ ∘ (M *ᵥ x) = M.map σ *ᵥ (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ M x i
  rw [e, e, hσ, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec,
    mulVec_mulVec, Formalism.UG.cT, Matrix.mul_assoc]

/- English proof (translation)
Simplify using `[Formalism.UG.hform, Pi.single_apply]`.
-/
theorem hform_single {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (N : Matrix n n A) (i j : n) :
    Formalism.UG.hform σ N (Pi.single i 1) (Pi.single j 1) = N i j := by
  simp [Formalism.UG.hform, Pi.single_apply]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[← hform_single σ N i j, ← hform_single σ N' i j, h]`.
-/
theorem matrix_eq_of_hform {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (N N' : Matrix n n A) (h : ∀ x y, Formalism.UG.hform σ N x y = Formalism.UG.hform σ N' x y) : N = N' := by
  ext i j
  rw [← hform_single σ N i j, ← hform_single σ N' i j, h]

/- English proof (translation)
Establish `hcT : Formalism.UG.cT σ (c • (1 : Matrix n n A) + (1 - c) • P) = σ c • 1 + (1 - σ c) • Formalism.UG.cT σ P`. Use extensionality with `i j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[Formalism.UG.cT]`.

Simplify using `[Formalism.UG.cT, Matrix.one_apply, h, Ne.symm h]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hPP, smul_smul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hPP, smul_smul]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hcT]`. Simplify using `only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hSA, Matrix.mul_assoc, hPP, smul_smul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem unit_of_proj {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (J P : Matrix n n A) (c : A) (hPP : P * P = P) (hSA : Formalism.UG.cT σ P * J = J * P) (hc : c * σ c = 1) :
    (c • 1 + (1 - c) • P) * (σ c • 1 + (1 - σ c) • P) = 1 ∧
    (σ c • 1 + (1 - σ c) • P) * (c • 1 + (1 - c) • P) = 1 ∧
    Formalism.UG.cT σ (c • 1 + (1 - c) • P) * J * (c • 1 + (1 - c) • P) = J := by
  have hcT : Formalism.UG.cT σ (c • (1 : Matrix n n A) + (1 - c) • P) = σ c • 1 + (1 - σ c) • Formalism.UG.cT σ P := by
    ext i j
    by_cases h : j = i
    · subst h; simp [Formalism.UG.cT]
    · simp [Formalism.UG.cT, Matrix.one_apply, h, Ne.symm h]
  refine ⟨?_, ?_, ?_⟩
  · simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hPP, smul_smul]
    calc _ = (c * σ c) • (1 : Matrix n n A) + (1 - c * σ c) • P := by module
      _ = 1 := by rw [hc, sub_self, zero_smul, add_zero, one_smul]
  · simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hPP, smul_smul]
    calc _ = (c * σ c) • (1 : Matrix n n A) + (1 - c * σ c) • P := by module
      _ = 1 := by rw [hc, sub_self, zero_smul, add_zero, one_smul]
  · rw [hcT]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hSA,
      Matrix.mul_assoc, hPP, smul_smul]
    calc _ = (c * σ c) • J + (1 - c * σ c) • (J * P) := by module
      _ = J := by rw [hc, sub_self, zero_smul, add_zero, one_smul]

end GlobalTheory.UnitTorus

open GlobalTheory.UnitTorus in
/- English proof (translation)
Introduce `I P c hP hSA hc`. Establish `hPP : P * P = P`. Use extensionality with `i j`. Use `congrFun (hP (Pi.single j 1)) i` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec]`.

Simplify using `using this`. Establish `hSA' : Formalism.UG.cT (sigA I) P * I.J.map (Formalism.UG.inclE (F` using `I.F) (Af I.F)) = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * P := by`. Use `matrix_eq_of_hform (sigA I) (Formalism.UG.cT (sigA I) P * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * 1) (Formalism.UG.cT (sigA I) 1 * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * P) (fun x y => by` as an intermediate fact. Rewrite using `[← hform_mulVec_two, ← hform_mulVec_two, one_mulVec, one_mulVec]`. Conclude with `hSA x y)`.

Simplify `this` using `[Formalism.UG.cT_one]`. Take `⟨h1, h2, h3⟩` from `unit_of_proj (sigA I) _ P c hPP hSA' hc`. Conclude with `⟨⟨⟨_, _, h1, h2⟩, h3⟩, rfl, rfl⟩`.
-/
theorem GlobalTheory.unitTorus_unit : ∀ (I : AutInst) (P : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (c : I.E ⊗[I.F] Af I.F), (∀ y, P *ᵥ (P *ᵥ y) = P *ᵥ y) → (∀ x y, hA I (P *ᵥ x) y = hA I x (P *ᵥ y)) → c * sigA I c = 1 → ∃ h : I.Gf, I.fmat h = c • 1 + (1 - c) • P ∧ I.fmat h⁻¹ = sigA I c • 1 + (1 - sigA I c) • P := by
  intro I P c hP hSA hc
  have hPP : P * P = P := by
    ext i j
    have := congrFun (hP (Pi.single j 1)) i
    rw [Matrix.mulVec_mulVec] at this
    simpa using this
  have hSA' : Formalism.UG.cT (sigA I) P * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) =
      I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * P := by
    have := matrix_eq_of_hform (sigA I) (Formalism.UG.cT (sigA I) P * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * 1)
      (Formalism.UG.cT (sigA I) 1 * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * P) (fun x y => by
        rw [← hform_mulVec_two, ← hform_mulVec_two, one_mulVec, one_mulVec]
        exact hSA x y)
    simpa [Formalism.UG.cT_one] using this
  obtain ⟨h1, h2, h3⟩ := unit_of_proj (sigA I) _ P c hPP hSA' hc
  exact ⟨⟨⟨_, _, h1, h2⟩, h3⟩, rfl, rfl⟩
