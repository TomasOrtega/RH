import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IntFrames
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.EigenLatticeFrames
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsTriangularReframeExistsAndUnique
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IntFramesCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFrames GlobalTheory.Reg

open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Linear

variable {S : Type} [Field S] {x : Sp S ⟶ Xo.X} {m : ℕ} {u v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}

/- English proof (translation)
Establish `h1` using `(ReframeEx.comb_iff hu (N i) _).2 rfl`. Establish `h2` using `GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S x v hv u M.transpose (N i) _ h h1`. Establish `e : M.transpose.mulVec (N i) = Pi.single i 1`. Use function extensionality and compare the values at `j`. Use `congrFun (congrFun hNM i) j` as an intermediate fact.

Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.single_apply]`. Rewrite using `[Finset.sum_congr rfl fun k _ => _root_.mul_comm (M k j) (N i k), this]`. Simplify using `only [eq_comm]`. Rewrite `h2` using `[e]`.

Rewrite using `[← ReframeEx.comb_unique hv h2 (ReframeEx.comb_single hv i)]`. Conclude with `h1`.
-/
theorem comb_inv (hu : ∀ i, IsTanAt x (u i)) (hv : ∀ i, IsTanAt x (v i)) (M N : Matrix (Fin m) (Fin m) S)
    (hNM : N * M = 1) (h : ∀ i, IsCombAt x v (M i) (u i)) (i : Fin m) : IsCombAt x u (N i) (v i) := by
  have h1 := (ReframeEx.comb_iff hu (N i) _).2 rfl
  have h2 := GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S x v hv u M.transpose (N i) _ h h1
  have e : M.transpose.mulVec (N i) = Pi.single i 1 := by
    funext j
    have := congrFun (congrFun hNM i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.single_apply]
    rw [Finset.sum_congr rfl fun k _ => _root_.mul_comm (M k j) (N i k), this]
    simp only [eq_comm]
  rw [e] at h2
  rw [← ReframeEx.comb_unique hv h2 (ReframeEx.comb_single hv i)]
  exact h1

/- English proof (translation)
Use `choose M hd hz hc using h`. Set `M' : Matrix (Fin m) (Fin m) S` to `Matrix.of M`. Establish `hdet : IsUnit M'.det`. Rewrite using `[Matrix.det_of_lowerTriangular M' (fun i j hij => hz i j hij), isUnit_iff_ne_zero]`. Conclude with `Finset.prod_ne_zero_iff.2 fun i _ => hd i`.

Establish `hNM : M'⁻¹ * M' = 1` using `Matrix.nonsing_inv_mul _ hdet`. Establish `hz'` using `BorelGroupoid.lower_of_mul_eq_one M' M'⁻¹ hz hNM`. Use `⟨M'⁻¹, Matrix.isUnit_det_of_right_inverse hNM, fun i => ⟨fun h0 => ?_, hz' i, comb_inv hu hv M' _ hNM hc i⟩⟩` and prove the remaining obligations. Establish `h2` using `BorelGroupoid.lower_mul_diag M'⁻¹ M' hz' hz i`. Rewrite `h2` using `[hNM, Matrix.one_apply_eq, h0, zero_mul]`.

Conclude with `one_ne_zero h2`.
-/
theorem tri_inv (hu : ∀ i, IsTanAt x (u i)) (hv : ∀ i, IsTanAt x (v i))
    (h : ∀ i, ∃ cf : Fin m → S, cf i ≠ 0 ∧ (∀ j, i < j → cf j = 0) ∧ IsCombAt x v cf (u i)) :
    ∃ N : Matrix (Fin m) (Fin m) S, IsUnit N.det ∧
      ∀ i, N i i ≠ 0 ∧ (∀ j, i < j → N i j = 0) ∧ IsCombAt x u (N i) (v i) := by
  choose M hd hz hc using h
  let M' : Matrix (Fin m) (Fin m) S := Matrix.of M
  have hdet : IsUnit M'.det := by
    rw [Matrix.det_of_lowerTriangular M' (fun i j hij => hz i j hij), isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hd i
  have hNM : M'⁻¹ * M' = 1 := Matrix.nonsing_inv_mul _ hdet
  have hz' := BorelGroupoid.lower_of_mul_eq_one M' M'⁻¹ hz hNM
  refine ⟨M'⁻¹, Matrix.isUnit_det_of_right_inverse hNM, fun i => ⟨fun h0 => ?_, hz' i, comb_inv hu hv M' _ hNM hc i⟩⟩
  have h2 := BorelGroupoid.lower_mul_diag M'⁻¹ M' hz' hz i
  rw [hNM, Matrix.one_apply_eq, h0, zero_mul] at h2
  exact one_ne_zero h2

end Linear

section Basis

variable {S : Type} [Field S] [Algebra c.F S] {x : Sp S ⟶ Xo.X} {τ : E →+* ℂ}
  {u v : Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}

/- English proof (translation)
Take `⟨n, xc, hx⟩` from `ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback x).obj Xo.univ.t.G)`. Set `B : Module.Basis (Fin (Dw.mult τ)) S (gfpEig (c` to `c) hx τ) := Module.finBasisOfFinrankEq S _ (gfp_finrank hx0 hx τ)`. Establish `hd : LinearIndependent S ((gfpEig (c` using `c) hx τ).subtype ∘ B) := B.linearIndependent.map' (gfpEig (c := c) hx τ).subtype (Submodule.ker_subtype _)`. Establish `hW : ∀ i, ((gfpEig (c` using `c) hx τ).subtype ∘ B) i ∈ gfpEig (c := c) hx τ := fun i => (B i).2`. Conclude with `⟨fun i => gfpVec x xc (((gfpEig (c := c) hx τ).subtype ∘ B) i), fun i => gfp_tan hx _, fun i => (gfp_eig_iff hx τ _).2 (hW i), fun w hw he => gfp_basis hx0 hx τ _ hd hW w hw he⟩`.
-/
theorem exists_eigenBasisAt (hx0 : x ≫ Xo.s = sOf c S) (τ : E →+* ℂ) : ∃ u, IsEigenBasisAt Xo c x τ u := by
  obtain ⟨n, xc, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback x).obj Xo.univ.t.G)
  let B : Module.Basis (Fin (Dw.mult τ)) S (gfpEig (c := c) hx τ) :=
    Module.finBasisOfFinrankEq S _ (gfp_finrank hx0 hx τ)
  have hd : LinearIndependent S ((gfpEig (c := c) hx τ).subtype ∘ B) :=
    B.linearIndependent.map' (gfpEig (c := c) hx τ).subtype (Submodule.ker_subtype _)
  have hW : ∀ i, ((gfpEig (c := c) hx τ).subtype ∘ B) i ∈ gfpEig (c := c) hx τ := fun i => (B i).2
  exact ⟨fun i => gfpVec x xc (((gfpEig (c := c) hx τ).subtype ∘ B) i), fun i => gfp_tan hx _,
    fun i => (gfp_eig_iff hx τ _).2 (hW i), fun w hw he => gfp_basis hx0 hx τ _ hd hW w hw he⟩

end Basis

section Generic

end Generic

variable (Xo c)

end GlobalTheory.IntFramesCompare
