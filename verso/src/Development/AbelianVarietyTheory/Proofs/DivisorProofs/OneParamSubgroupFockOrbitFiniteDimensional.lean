import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsItWOfGlobIt
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.MassFormulaPositivity
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubstitutionTotalDegreeLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexOrder Matrix

namespace GlobalTheory.OneParamOrbit

/- English proof (translation)
Establish `hu : IsUnit (B.fr τ).det` using `(Matrix.isUnit_iff_isUnit_det _).mp (B.fr_unit τ)`. Establish `hinj : Function.Injective ((B.fr τ)⁻¹).mulVec` using `Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_nonsing_inv_iff).mpr (B.fr_unit τ))`. Establish `hJ : ((B.fr τ)⁻¹)ᴴ * gramAt D X τ * (B.fr τ)⁻¹ = Formalism.REAL.Jm (B.ε τ)`. Rewrite using `[← B.fr_gram τ]`. Establish `h1 : ((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ = 1`.

Rewrite using `[← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Formalism.REAL.Jm (B.ε τ) := by rw [h1, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_one]`. Establish `hpos` using `(hG.conjTranspose_mul_mul_same hinj).diag_pos (i := i)`.

Rewrite `hpos` using `[hJ]`. Assume the negation of the conclusion as `hne`. Simplify using `only [Formalism.REAL.Jm, Matrix.diagonal_apply_eq, hne] at hpos`. Evaluate the numerical expressions using `at hpos`.
-/
theorem eps_true_of_posDef {D : D7} {X : HSp D} (B : GlobalTheory.ChainFr.Fr X) (τ : D.what₂.Tau)
    (hG : (gramAt D X τ).PosDef) (i : Fin X.rank) : B.ε τ i = true := by
  have hu : IsUnit (B.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (B.fr_unit τ)
  have hinj : Function.Injective ((B.fr τ)⁻¹).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_nonsing_inv_iff).mpr (B.fr_unit τ))
  have hJ : ((B.fr τ)⁻¹)ᴴ * gramAt D X τ * (B.fr τ)⁻¹ = Formalism.REAL.Jm (B.ε τ) := by
    rw [← B.fr_gram τ]
    have h1 : ((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one]
    calc ((B.fr τ)⁻¹)ᴴ * ((B.fr τ)ᴴ * Formalism.REAL.Jm (B.ε τ) * B.fr τ) * (B.fr τ)⁻¹
        = (((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ) * Formalism.REAL.Jm (B.ε τ) * (B.fr τ * (B.fr τ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (B.ε τ) := by rw [h1, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_one]
  have hpos := (hG.conjTranspose_mul_mul_same hinj).diag_pos (i := i)
  rw [hJ] at hpos
  by_contra hne
  simp only [Formalism.REAL.Jm, Matrix.diagonal_apply_eq, hne] at hpos
  norm_num at hpos

/- English proof (translation)
Establish `hu : IsUnit (B.fr τ).det` using `(Matrix.isUnit_iff_isUnit_det _).mp (B.fr_unit τ)`. Establish `hJ1 : Formalism.REAL.Jm (B.ε τ) = 1`. Establish `: B.ε τ = fun _ => true` using `funext (eps_true_of_posDef B τ hG)`. Rewrite using `[this]`. Simplify using `[Formalism.REAL.Jm]`.

Establish `hgram : (B.fr τ)ᴴ * B.fr τ = gramAt D X τ`. Rewrite using `[← B.fr_gram τ, hJ1, Matrix.mul_one]`. Use `⟨?_, by rw [hJ1, Matrix.mul_one, Matrix.one_mul]⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]`. Establish `h1 : ((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ = 1`.

Rewrite using `[← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = ((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ * (B.fr τ * (B.fr τ)⁻¹) := by`. Rewrite using `[hgram, hE, ← hgram]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [h1, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]`.
-/
theorem conj_mem_Kset {D : D7} {X : HSp D} (B : GlobalTheory.ChainFr.Fr X) (τ : D.what₂.Tau)
    (hG : (gramAt D X τ).PosDef) {E : Matrix (Fin X.rank) (Fin X.rank) ℂ}
    (hE : Eᴴ * gramAt D X τ * E = gramAt D X τ) :
    B.fr τ * E * (B.fr τ)⁻¹ ∈ Formalism.REAL.Kset (B.ε τ) := by
  have hu : IsUnit (B.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (B.fr_unit τ)
  have hJ1 : Formalism.REAL.Jm (B.ε τ) = 1 := by
    have : B.ε τ = fun _ => true := funext (eps_true_of_posDef B τ hG)
    rw [this]; simp [Formalism.REAL.Jm]
  have hgram : (B.fr τ)ᴴ * B.fr τ = gramAt D X τ := by
    rw [← B.fr_gram τ, hJ1, Matrix.mul_one]
  refine ⟨?_, by rw [hJ1, Matrix.mul_one, Matrix.one_mul]⟩
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  have h1 : ((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one]
  calc (B.fr τ * E * (B.fr τ)⁻¹)ᴴ * (B.fr τ * E * (B.fr τ)⁻¹)
      = ((B.fr τ)⁻¹)ᴴ * (Eᴴ * ((B.fr τ)ᴴ * B.fr τ) * E) * (B.fr τ)⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ * (B.fr τ * (B.fr τ)⁻¹) := by
        rw [hgram, hE, ← hgram]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

/- English proof (translation)
Introduce `D ψ θ _hψ hθ M X A B χ χ' ω hω hexp hsig τ Y hY Φ hΦ`. Establish `hG : (gramAt D X τ).PosDef` using `GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity.posDef_of_hasSignature (hsig τ)`. Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, P, hf, rfl⟩` from `hx`.

Distinguish the cases in `hf0 : f = 0`. Substitute `hf0` using the available equality. Establish `h0 : fockF ψ θ false A B 0 P = 0`. Use `GlobalTheory.FiniteFock.pureTensorO_smul ψ θ (GlobalTheory.Grid.sgn false M) X (frSgn false A).cart B.cart A.onb B.onb 0 0 P` as an intermediate fact. Rewrite `this` using `[zero_smul, zero_smul]`. Then use the resulting hypothesis.

Use `⟨⊥, inferInstance, fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[h0, map_zero]`. Conclude with `zero_mem _`. Take `⟨a, b, ha, hb⟩` from `hexp τ`. Take `⟨x, y, -, -, hK⟩` from `GlobalTheory.CompactFockAction.compactFockAll D (GlobalTheory.Grid.sgn false M) X (frSgn false A) B θ ψ χ χ' (ω.toSgn false) f τ a b hθ hω ha hb hf hf0`.

Use `⟨(MvPolynomial.restrictTotalDegree _ ℂ P.totalDegree).map (fockF ψ θ false A B f), inferInstance, fun t => ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit (B.fr τ).det` using `(Matrix.isUnit_iff_isUnit_det _).mp (B.fr_unit τ)`. Establish `hE : (NormedSpace.exp (t • Y))ᴴ * gramAt D X τ * NormedSpace.exp (t • Y) = gramAt D X τ` using `GlobalTheory.SmoothAutCheck.exp_mem_UH (Matrix.isUnit_iff_isUnit_det _ |>.mp hG.isUnit) hY t`. Establish `hk` using `conj_mem_Kset B τ hG hE`. Establish `hA1 : (frSgn false A).elt θ τ 1 = 1`.

Establish `hAu : IsUnit (A.fr τ).det` using `(Matrix.isUnit_iff_isUnit_det _).mp (A.fr_unit τ)`. Use `show atTau θ _ τ ((A.fr τ)⁻¹ * 1 * A.fr τ) = 1`. Rewrite using `[Matrix.mul_one, Matrix.nonsing_inv_mul _ hAu]`. Conclude with `GlobalTheory.PointAtPlaceHom.atTau_one hθ _ τ`. Establish `hBk : B.elt θ τ (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹) = oneP θ X τ Y t` using `by show atTau θ X τ ((B.fr τ)⁻¹ * (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹) * B.fr τ) = _`.

Rewrite using `[show (B.fr τ)⁻¹ * (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹) * B.fr τ = ((B.fr τ)⁻¹ * B.fr τ) * NormedSpace.exp (t • Y) * ((B.fr τ)⁻¹ * B.fr τ) by`. Simplify using `only [Matrix.mul_assoc],`. Use the proof step `Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_one]`. Both sides reduce to the same expression. Establish `hω1 : ω (1, oneP θ X τ Y t) = (ω.toSgn false) ((frSgn false A).elt θ τ 1, B.elt θ τ (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹))`.

Rewrite using `[hA1, hBk]`. Use `show ω (1, _) = ω ((GlobalTheory.Grid.ofSgn false M) 1, _)`. Rewrite using `[map_one]`. Establish `key` using `hK 1 (GlobalTheory.Chain.RealIt.one_mem_Kset _) _ hk P`. Establish `hfock : fockF ψ θ false A B f P = GlobalTheory.ChainFr.ptF ψ θ (frSgn false A) B f P` using `rfl`.

Rewrite using `[hfock, hω1, key]`. Use `Submodule.smul_mem _ _ ⟨_, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 (GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _), rfl⟩` and prove the remaining obligations. Consider the case `zero => exact ⟨⊥, inferInstance, fun t => by rw [map_zero]; exact zero_mem _⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨V₁, h₁, hV₁⟩` from `hx`.

Take `⟨V₂, h₂, hV₂⟩` from `hy`. Conclude with `⟨V₁ ⊔ V₂, Submodule.finiteDimensional_sup V₁ V₂, fun t => by`. Rewrite using `[map_add]`. Conclude with `add_mem (Submodule.mem_sup_left (hV₁ t)) (Submodule.mem_sup_right (hV₂ t))⟩`. Consider the case `smul c x _ hx`.

Take `⟨V, h, hV⟩` from `hx`. Conclude with `⟨V, h, fun t => by rw [map_smul]; exact Submodule.smul_mem _ _ (hV t)⟩`.
-/
theorem orbit_finiteDimensional : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (χ χ' : (AE D)ˣ →* Circle) (ω : GlobalTheory.Grid.WRep M X),
    GlobalTheory.Grid.IsWeil ψ false M X χ χ' ω → (∀ τ, ∃ a b : ℚ, HasInfExp D χ τ a ∧ HasInfExp D χ' τ b) →
    (∀ τ, Formalism.UG.HasSignature (gramAt D X τ) X.rank 0) →
    ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ algF ψ θ false A B,
      ∃ V : Submodule ℂ (WO M X → ℂ), FiniteDimensional ℂ V ∧ ∀ t : ℝ, ω (1, oneP θ X τ Y t) Φ ∈ V := by
  intro D ψ θ _hψ hθ M X A B χ χ' ω hω hexp hsig τ Y hY Φ hΦ
  have hG : (gramAt D X τ).PosDef := GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity.posDef_of_hasSignature (hsig τ)
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, P, hf, rfl⟩ := hx
    by_cases hf0 : f = 0
    · subst hf0
      have h0 : fockF ψ θ false A B 0 P = 0 := by
        have := GlobalTheory.FiniteFock.pureTensorO_smul ψ θ (GlobalTheory.Grid.sgn false M) X (frSgn false A).cart B.cart
          A.onb B.onb 0 0 P
        rwa [zero_smul, zero_smul] at this
      refine ⟨⊥, inferInstance, fun t => ?_⟩
      rw [h0, map_zero]; exact zero_mem _
    · obtain ⟨a, b, ha, hb⟩ := hexp τ
      obtain ⟨x, y, -, -, hK⟩ := GlobalTheory.CompactFockAction.compactFockAll D (GlobalTheory.Grid.sgn false M) X
        (frSgn false A) B θ ψ χ χ' (ω.toSgn false) f τ a b hθ hω ha hb hf hf0
      refine ⟨(MvPolynomial.restrictTotalDegree _ ℂ P.totalDegree).map (fockF ψ θ false A B f),
        inferInstance, fun t => ?_⟩
      have hu : IsUnit (B.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (B.fr_unit τ)
      have hE : (NormedSpace.exp (t • Y))ᴴ * gramAt D X τ * NormedSpace.exp (t • Y) = gramAt D X τ :=
        GlobalTheory.SmoothAutCheck.exp_mem_UH (Matrix.isUnit_iff_isUnit_det _ |>.mp hG.isUnit) hY t
      have hk := conj_mem_Kset B τ hG hE
      have hA1 : (frSgn false A).elt θ τ 1 = 1 := by
        have hAu : IsUnit (A.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (A.fr_unit τ)
        show atTau θ _ τ ((A.fr τ)⁻¹ * 1 * A.fr τ) = 1
        rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ hAu]
        exact GlobalTheory.PointAtPlaceHom.atTau_one hθ _ τ
      have hBk : B.elt θ τ (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹) = oneP θ X τ Y t := by
        show atTau θ X τ ((B.fr τ)⁻¹ * (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹) * B.fr τ) = _
        rw [show (B.fr τ)⁻¹ * (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹) * B.fr τ
            = ((B.fr τ)⁻¹ * B.fr τ) * NormedSpace.exp (t • Y) * ((B.fr τ)⁻¹ * B.fr τ) by
              simp only [Matrix.mul_assoc],
          Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_one]
        rfl
      have hω1 : ω (1, oneP θ X τ Y t)
          = (ω.toSgn false) ((frSgn false A).elt θ τ 1, B.elt θ τ (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹)) := by
        rw [hA1, hBk]
        show ω (1, _) = ω ((GlobalTheory.Grid.ofSgn false M) 1, _)
        rw [map_one]
      have key := hK 1 (GlobalTheory.Chain.RealIt.one_mem_Kset _) _ hk P
      have hfock : fockF ψ θ false A B f P = GlobalTheory.ChainFr.ptF ψ θ (frSgn false A) B f P := rfl
      rw [hfock, hω1, key]
      refine Submodule.smul_mem _ _ ⟨_, (MvPolynomial.mem_restrictTotalDegree _ _ _).2
        (GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _), rfl⟩
  | zero => exact ⟨⊥, inferInstance, fun t => by rw [map_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨V₁, h₁, hV₁⟩ := hx
    obtain ⟨V₂, h₂, hV₂⟩ := hy
    exact ⟨V₁ ⊔ V₂, Submodule.finiteDimensional_sup V₁ V₂, fun t => by
      rw [map_add]; exact add_mem (Submodule.mem_sup_left (hV₁ t)) (Submodule.mem_sup_right (hV₂ t))⟩
  | smul c x _ hx =>
    obtain ⟨V, h, hV⟩ := hx
    exact ⟨V, h, fun t => by rw [map_smul]; exact Submodule.smul_mem _ _ (hV t)⟩

end GlobalTheory.OneParamOrbit
