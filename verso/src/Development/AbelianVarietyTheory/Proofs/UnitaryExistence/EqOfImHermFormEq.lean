import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmTypeLetterFrameColumnDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramePeriodsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TriangularFrameMovesPeriodBlockTriangularStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameEqOrthonormalMulTriangularStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemIffConjugateNotMem

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.UnitDet

/- English proof (translation)
Establish `h1 : ∀ z, ∀ w ∈ S, (hermForm A z w).im = (hermForm B z w).im`. Introduce `z w hw`. Establish `hz : z ∈ Submodule.span ℝ S` using `hS ▸ Submodule.mem_top`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx => exact h x hx w hw`.

Consider the case `zero => simp [hermForm]`. Consider the case `add x y _ _ hx hy`. Simplify using `only [hermForm, add_dotProduct, Complex.add_im] at hx hy ⊢`. Rewrite using `[hx, hy]`. Consider the case `smul a x _ hx`.

Simplify using `only [hermForm, smul_dotProduct, Complex.smul_im] at hx ⊢`. Rewrite using `[hx]`. Establish `h2 : ∀ z w, (hermForm A z w).im = (hermForm B z w).im`. Introduce `z w`. Establish `hw : w ∈ Submodule.span ℝ S` using `hS ▸ Submodule.mem_top`.

Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact h1 z x hx`. Consider the case `zero => simp [hermForm]`. Consider the case `add x y _ _ hx hy`. Simplify using `only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im] at hx hy ⊢`.

Rewrite using `[hx, hy]`. Consider the case `smul a x _ hx`. Simplify using `only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im] at hx ⊢`. Rewrite using `[hx]`. Use extensionality with `i j`.

Establish `e1` using `h2 (Pi.single i 1) (Pi.single j 1)`. Establish `e2` using `h2 (Pi.single i Complex.I) (Pi.single j 1)`. Simplify using `[hermForm] at e1 e2`. Conclude with `Complex.ext e2 e1`.
-/
theorem eq_of_im_hermForm_eq {g : ℕ} (S : Set (Fin g → ℂ)) (hS : Submodule.span ℝ S = ⊤)
    (A B : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ z ∈ S, ∀ w ∈ S, (hermForm A z w).im = (hermForm B z w).im) : A = B := by
  have h1 : ∀ z, ∀ w ∈ S, (hermForm A z w).im = (hermForm B z w).im := by
    intro z w hw
    have hz : z ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx => exact h x hx w hw
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, add_dotProduct, Complex.add_im] at hx hy ⊢
      rw [hx, hy]
    | smul a x _ hx =>
      simp only [hermForm, smul_dotProduct, Complex.smul_im] at hx ⊢
      rw [hx]
  have h2 : ∀ z w, (hermForm A z w).im = (hermForm B z w).im := by
    intro z w
    have hw : w ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem x hx => exact h1 z x hx
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im] at hx hy ⊢
      rw [hx, hy]
    | smul a x _ hx =>
      simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im] at hx ⊢
      rw [hx]
  ext i j
  have e1 := h2 (Pi.single i 1) (Pi.single j 1)
  have e2 := h2 (Pi.single i Complex.I) (Pi.single j 1)
  simp [hermForm] at e1 e2
  exact Complex.ext e2 e1

/- English proof (translation)
Establish `: star (h *ᵥ w) = h.map (starRingEnd ℂ) *ᵥ star w`. Use extensionality with `a`. Simplify using `[Matrix.mulVec, dotProduct]`. Rewrite using `[hermForm, hermForm, this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec z, Matrix.vecMul_transpose]`.
-/
theorem hermForm_mulVec {g : ℕ} (A h : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm A (h *ᵥ z) (h *ᵥ w) = hermForm (hᵀ * (A * h.map (starRingEnd ℂ))) z w := by
  have : star (h *ᵥ w) = h.map (starRingEnd ℂ) *ᵥ star w := by
    ext a; simp [Matrix.mulVec, dotProduct]
  rw [hermForm, hermForm, this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec z, Matrix.vecMul_transpose]

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c σ g e F r M hG hB hN k Pf hPf x hx hu Hm hHm`. Take `⟨hl1, hl2, -⟩` from `GlobalTheory.T.unitFrame_eq_orthonormal_mul_triangular E r (M.X k).p0 (M.X k).Ψ (M.X k).Gm (M.X k).Gm_herm`. Take `⟨x₀, b, hb, hgr, hb1, rfl⟩` from `hl1 x hx hu`. Establish `hx₀ : x₀ ∈ (M.X k).dom` using `(hl2 x₀ hgr).1`. Take `⟨h₀, -, hh, -, -, hdet, -⟩` from `GlobalTheory.T.triangularFrame_moves_period_blockTriangular E H Dw l Xo c σ g e F r M hG hB hN k Pf hPf x₀ hx₀ b hb`.

Use `replace hdet := hdet hb1`. Take `⟨Pf', -, huniq, hper, -⟩` from `GlobalTheory.T.exists_framePeriods_alt E H Dw l Xo c σ g e F r M hG hB hN k`. Take `rfl` from `huniq Pf hPf`. Establish `hspan` using `(hper x₀ hx₀).2.2.2.1`. Take `⟨⟨idx, hty, -, hfr⟩, hp, -, hξ, hpos, hφ⟩` from `GlobalTheory.T.cmType_letter_frame_column_dictionary E H Dw l Xo c σ g e F r M hG hB hN k`.

Set `φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E)` to `(M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap`. Establish `hD` using `GlobalTheory.UnitFrame.im_hermForm_eq E H (F.Di k) r (-(M.X k).ξ0) (M.X k).Gm φ (M.X k).Ψ (hB.type k).2 g idx (fun j => relab c σ (e j).1) hty hξ hpos (hφ φ fun _ => rfl).2 x₀ (Pf x₀) (fun v j => by rw [hPf, hfr]; rfl) (fun τ => by rw [← hp]; exact hgr τ)`. Establish `key : h₀ᵀ * (Hm * h₀.map (starRingEnd ℂ)) = Matrix.diagonal fun j => ((2 * ‖(idx j).1.1 (-(M.X k).ξ0)‖ : ℝ) : ℂ)`. Use `eq_of_im_hermForm_eq _ hspan _ _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩ _ ⟨a', rfl⟩`.

Rewrite using `[hD, ← hermForm_mulVec, ← hh, ← hh, hHm]`. Establish `h1` using `congrArg Matrix.det key`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Establish `h2 : h₀.det * starRingEnd ℂ h₀.det = 1`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, hdet]`.

Simplify using the standard rewrite rules. Establish `h3 : Hm.det = h₀.det * (Hm.det * starRingEnd ℂ h₀.det)`. Take the linear combination `(-Hm.det) * h2`. Rewrite using `[h3, h1, Complex.ofReal_prod]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[hty j, map_neg, norm_neg]`. Use `split_ifs`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]`. Both sides reduce to the same expression.
-/
theorem det_eq_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k Pf, IsPerFr e F M k Pf → ∀ x ∈ (M.X k).dom, (∀ τ i, ‖dmin (M.X k).Gm x τ i‖ = 1) → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ a b, (hermForm Hm (Pf x a) (Pf x b)).im = (F.Di k).EF a b) → Hm.det = ((∏ j, (2 * ‖relab c σ (e j).1 (M.X k).ξ0‖) : ℝ) : ℂ) := by
  intro E _ _ _ H Dw l Xo c σ g e F r M hG hB hN k Pf hPf x hx hu Hm hHm
  obtain ⟨hl1, hl2, -⟩ := GlobalTheory.T.unitFrame_eq_orthonormal_mul_triangular E r (M.X k).p0 (M.X k).Ψ (M.X k).Gm (M.X k).Gm_herm
  obtain ⟨x₀, b, hb, hgr, hb1, rfl⟩ := hl1 x hx hu
  have hx₀ : x₀ ∈ (M.X k).dom := (hl2 x₀ hgr).1
  obtain ⟨h₀, -, hh, -, -, hdet, -⟩ :=
    GlobalTheory.T.triangularFrame_moves_period_blockTriangular E H Dw l Xo c σ g e F r M hG hB hN k Pf hPf x₀ hx₀ b hb
  replace hdet := hdet hb1
  obtain ⟨Pf', -, huniq, hper, -⟩ := GlobalTheory.T.exists_framePeriods_alt E H Dw l Xo c σ g e F r M hG hB hN k
  obtain rfl := huniq Pf hPf
  have hspan := (hper x₀ hx₀).2.2.2.1
  obtain ⟨⟨idx, hty, -, hfr⟩, hp, -, hξ, hpos, hφ⟩ := GlobalTheory.T.cmType_letter_frame_column_dictionary E H Dw l Xo c σ g e F r M hG hB hN k
  let φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E) := (M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap
  have hD := GlobalTheory.UnitFrame.im_hermForm_eq E H (F.Di k) r (-(M.X k).ξ0) (M.X k).Gm φ (M.X k).Ψ
    (hB.type k).2 g idx (fun j => relab c σ (e j).1) hty hξ hpos (hφ φ fun _ => rfl).2 x₀ (Pf x₀)
    (fun v j => by rw [hPf, hfr]; rfl) (fun τ => by rw [← hp]; exact hgr τ)
  have key : h₀ᵀ * (Hm * h₀.map (starRingEnd ℂ)) =
      Matrix.diagonal fun j => ((2 * ‖(idx j).1.1 (-(M.X k).ξ0)‖ : ℝ) : ℂ) := by
    refine eq_of_im_hermForm_eq _ hspan _ _ ?_
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    rw [hD, ← hermForm_mulVec, ← hh, ← hh, hHm]
  have h1 := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h1
  have h2 : h₀.det * starRingEnd ℂ h₀.det = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hdet]; simp
  have h3 : Hm.det = h₀.det * (Hm.det * starRingEnd ℂ h₀.det) := by
    linear_combination (-Hm.det) * h2
  rw [h3, h1, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hty j, map_neg, norm_neg]
  split_ifs
  · rw [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]
  · rfl

end GlobalTheory.UnitDet
