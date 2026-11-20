import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCharEntireNeZeroAutomorphyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCharBlockPeriodMatrixFourierJacobiExpansionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierJacobiExpansionFderivTermwiseStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

/- English proof (translation)
Establish `h1 : HasFDerivAt (fun Z : Fin g → ℂ => c • Z + p) (c • ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0` using `((hasFDerivAt_id (0 : Fin g → ℂ)).const_smul c).add_const p`. Establish `h2 : HasFDerivAt F (fderiv ℂ F p) (c • (0 : Fin g → ℂ) + p)`. Rewrite using `[smul_zero, zero_add]`. Conclude with `(hF p).hasFDerivAt`. Establish `h3 : HasFDerivAt (fun Z => F (c • Z + p)) _ 0` using `h2.comp (0 : Fin g → ℂ) h1`.

Establish `h4 : HasFDerivAt (fun Z => f Z * F (c • Z + p)) _ 0` using `(hf 0).hasFDerivAt.mul h3`. Rewrite using `[h4.fderiv]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem termsum_fderiv_mul_affine {g : ℕ} (f F : (Fin g → ℂ) → ℂ) (hf : Differentiable ℂ f) (hF : Differentiable ℂ F)
    (c : ℂ) (p W : Fin g → ℂ) :
    fderiv ℂ (fun Z => f Z * F (c • Z + p)) 0 W = fderiv ℂ f 0 W * F p + f 0 * fderiv ℂ F p (c • W) := by
  have h1 : HasFDerivAt (fun Z : Fin g → ℂ => c • Z + p) (c • ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 :=
    ((hasFDerivAt_id (0 : Fin g → ℂ)).const_smul c).add_const p
  have h2 : HasFDerivAt F (fderiv ℂ F p) (c • (0 : Fin g → ℂ) + p) := by
    rw [smul_zero, zero_add]; exact (hF p).hasFDerivAt
  have h3 : HasFDerivAt (fun Z => F (c • Z + p)) _ 0 := h2.comp (0 : Fin g → ℂ) h1
  have h4 : HasFDerivAt (fun Z => f Z * F (c • Z + p)) _ 0 := (hf 0).hasFDerivAt.mul h3
  rw [h4.fderiv]
  simp
  ring

/- English proof (translation)
Unfold `trFac`. Simplify using `only [dotProduct]`. Use `fun_prop`.
-/
theorem termsum_trFac_differentiable {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (m : ℕ)
    (M N : Fin g → ℤ) : Differentiable ℂ (trFac τ a b m M N) := by
  unfold trFac
  simp only [dotProduct]
  fun_prop

/- English proof (translation)
Unfold `CD.full`. Apply `Matrix.IsSymm.submatrix` to reduce the goal to its premises. Conclude with `Matrix.IsSymm.fromBlocks d.symm rfl (d.toricPeriodBlock_isSymm.add hS)`.
-/
theorem termsum_full_isSymm {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX)
    (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (hS : S.IsSymm) : (d.full σ S).IsSymm := by
  unfold CD.full
  apply Matrix.IsSymm.submatrix
  exact Matrix.IsSymm.fromBlocks d.symm rfl (d.toricPeriodBlock_isSymm.add hS)

/- English proof (translation)
Introduce `j`. Unfold `CD.aF`. Break down `σ j with i | l` into its components or cases. Conclude with `d.ha i`. Conclude with `Or.inl rfl`.
-/
theorem termsum_half_aF {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX)
    (σ : Fin g ≃ Fin g' ⊕ Fin r) : Half (d.aF σ) := by
  intro j
  unfold CD.aF
  rcases σ j with i | l
  · exact d.ha i
  · exact Or.inl rfl

/- English proof (translation)
Introduce `j`. Unfold `CD.bF`. Break down `σ j with i | l` into its components or cases. Conclude with `d.hb i`. Conclude with `d.hb2 l`.
-/
theorem termsum_half_bF {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX)
    (σ : Fin g ≃ Fin g' ⊕ Fin r) : Half (d.bF σ) := by
  intro j
  unfold CD.bF
  rcases σ j with i | l
  · exact d.hb i
  · exact d.hb2 l

/- English proof (translation)
Introduce `N g' r g bX d σ S hS hpos m M Nn W`. Establish `hθ` using `(GlobalTheory.T.thetaChar_differentiable_ne_zero_automorphy g _ _ _ (termsum_full_isSymm d σ S hS) hpos (termsum_half_aF d σ) (termsum_half_bF d σ)).1`. Use `set p := (m : ℂ)⁻¹ • perV (d.full σ S) M Nn with hp`. Take `⟨hs, he⟩` from `GlobalTheory.T.thetaChar_blockPeriodMatrix_fourierJacobiExpansion N g' r g bX d σ S hS hpos p`. Take `⟨hd, hD⟩` from `GlobalTheory.T.fourierJacobiExpansion_fderiv_termwise N g' r g bX d σ S hS hpos`.

Take `⟨hs', he'⟩` from `hD p ((m : ℂ) • W)`. Establish `hf` using `termsum_trFac_differentiable (d.full σ S) (d.aF σ) (d.bF σ) m M Nn`. Use `set f := trFac (d.full σ S) (d.aF σ) (d.bF σ) m M Nn with hfdef`. Establish `e0 : ∀ χ, d.term σ S m M Nn χ 0 = f 0 * d.fj σ S χ p` using `fun χ => by`. Simplify using `only [CD.term, smul_zero, zero_add, hfdef, hp]`.

Establish `e1 : ∀ χ, fderiv ℂ (d.term σ S m M Nn χ) 0 W = fderiv ℂ f 0 W * d.fj σ S χ p + f 0 * fderiv ℂ (d.fj σ S χ) p ((m : ℂ) • W)` using `fun χ => termsum_fderiv_mul_affine f (d.fj σ S χ) hf (hd χ) m p W`. Establish `e2 : fderiv ℂ (trF (d.full σ S) (d.aF σ) (d.bF σ) m M Nn) 0 W = _` using `termsum_fderiv_mul_affine f _ hf hθ m p W`. Establish `s1` using `hs.of_norm`. Establish `s2` using `hs'.of_norm`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [e0]`. Conclude with `(s1.mul_left _).norm`. Simplify using `only [e1]`. Conclude with `((s1.mul_left _).add (s2.mul_left _)).norm`. Simplify using `only [e0]`.

Rewrite using `[tsum_mul_left, he]`. Simplify using `only [trF, smul_zero, zero_add, hfdef, hp]`. Simplify using `only [e1]`. Rewrite using `[(s1.mul_left _).tsum_add (s2.mul_left _), tsum_mul_left, tsum_mul_left, he, he', e2]`.
-/
theorem term_sum_and_fderiv : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ S : Matrix (Fin r) (Fin r) ℂ, S.IsSymm → ((d.full σ S).map Complex.im).PosDef → ∀ (m : ℕ) (M Nn : Fin g → ℤ) (W : Fin g → ℂ), (Summable fun χ => ‖d.term σ S m M Nn χ 0‖) ∧ (Summable fun χ => ‖fderiv ℂ (d.term σ S m M Nn χ) 0 W‖) ∧ ∑' χ, d.term σ S m M Nn χ 0 = trF (d.full σ S) (d.aF σ) (d.bF σ) m M Nn 0 ∧ ∑' χ, fderiv ℂ (d.term σ S m M Nn χ) 0 W = fderiv ℂ (trF (d.full σ S) (d.aF σ) (d.bF σ) m M Nn) 0 W := by
  intro N g' r g bX d σ S hS hpos m M Nn W
  have hθ := (GlobalTheory.T.thetaChar_differentiable_ne_zero_automorphy g _ _ _ (termsum_full_isSymm d σ S hS) hpos (termsum_half_aF d σ) (termsum_half_bF d σ)).1
  set p := (m : ℂ)⁻¹ • perV (d.full σ S) M Nn with hp
  obtain ⟨hs, he⟩ := GlobalTheory.T.thetaChar_blockPeriodMatrix_fourierJacobiExpansion N g' r g bX d σ S hS hpos p
  obtain ⟨hd, hD⟩ := GlobalTheory.T.fourierJacobiExpansion_fderiv_termwise N g' r g bX d σ S hS hpos
  obtain ⟨hs', he'⟩ := hD p ((m : ℂ) • W)
  have hf := termsum_trFac_differentiable (d.full σ S) (d.aF σ) (d.bF σ) m M Nn
  set f := trFac (d.full σ S) (d.aF σ) (d.bF σ) m M Nn with hfdef
  have e0 : ∀ χ, d.term σ S m M Nn χ 0 = f 0 * d.fj σ S χ p := fun χ => by
    simp only [CD.term, smul_zero, zero_add, hfdef, hp]
  have e1 : ∀ χ, fderiv ℂ (d.term σ S m M Nn χ) 0 W =
      fderiv ℂ f 0 W * d.fj σ S χ p + f 0 * fderiv ℂ (d.fj σ S χ) p ((m : ℂ) • W) := fun χ =>
    termsum_fderiv_mul_affine f (d.fj σ S χ) hf (hd χ) m p W
  have e2 : fderiv ℂ (trF (d.full σ S) (d.aF σ) (d.bF σ) m M Nn) 0 W = _ :=
    termsum_fderiv_mul_affine f _ hf hθ m p W
  have s1 := hs.of_norm
  have s2 := hs'.of_norm
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [e0]
    exact (s1.mul_left _).norm
  · simp only [e1]
    exact ((s1.mul_left _).add (s2.mul_left _)).norm
  · simp only [e0]
    rw [tsum_mul_left, he]
    simp only [trF, smul_zero, zero_add, hfdef, hp]
  · simp only [e1]
    rw [(s1.mul_left _).tsum_add (s2.mul_left _), tsum_mul_left, tsum_mul_left, he, he', e2]

end GlobalTheory.MBLow.Cl
