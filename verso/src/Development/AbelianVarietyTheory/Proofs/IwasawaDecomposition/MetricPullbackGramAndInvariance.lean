import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramTransformOfCoordinateChangeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramInvariantUnderGroupActionStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.MetLaws

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up Formalism.UG

/- English proof (translation)
Rewrite using `[toUpq_val]`. Simplify using `only [frameCo, reindex_apply, submatrix_mul_equiv]`. Use `congr 1`. Use `show _ * (γ.1.map (ι t).1 * mat x (ι t)) = _ * (γ.1.map (ι t).1 * mat (x0F X) (ι t)) * _`. Simplify using `only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ (det_x0F X (ι t)).isUnit]`.
-/
theorem frameCo_lact {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ} (hj : j ≤ r)
    {Tau : Type} (ι : Tau → X.Ψ) (γ : GL (Fin r) E) (x : Frame X.Ψ r) (t : Tau) :
    frameCo X hj (lact γ x) (ι t) = (toUpq X hj ι γ t).1 * frameCo X hj x (ι t) := by
  rw [toUpq_val]
  simp only [frameCo, reindex_apply, submatrix_mul_equiv]
  congr 1
  show _ * (γ.1.map (ι t).1 * mat x (ι t)) = _ * (γ.1.map (ι t).1 * mat (x0F X) (ι t)) * _
  simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ (det_x0F X (ι t)).isUnit]

/- English proof (translation)
Use `set G : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := g.1 with hG`. Establish `h0` using `moeb_mul_kapQ hg hz`. Rewrite `h0` using `[← hG]`. Rewrite using `[hw]`. Use `set z := moeb F 0 with hzdef`.

Use `set w := moeb G z with hwdef`. Establish `b11 : (G * F).toBlocks₁₁ = G.toBlocks₁₁ * F.toBlocks₁₁ + G.toBlocks₁₂ * F.toBlocks₂₁` using `by conv_lhs => rw [← fromBlocks_toBlocks G, ← fromBlocks_toBlocks F, fromBlocks_multiply]`. Simplify using the standard rewrite rules. Establish `b21 : (G * F).toBlocks₂₁ = G.toBlocks₂₁ * F.toBlocks₁₁ + G.toBlocks₂₂ * F.toBlocks₂₁` using `by conv_lhs => rw [← fromBlocks_toBlocks G, ← fromBlocks_toBlocks F, fromBlocks_multiply]`. Simplify using the standard rewrite rules.

Establish `b22 : (G * F).toBlocks₂₂ = G.toBlocks₂₁ * F.toBlocks₁₂ + G.toBlocks₂₂ * F.toBlocks₂₂` using `by conv_lhs => rw [← fromBlocks_toBlocks G, ← fromBlocks_toBlocks F, fromBlocks_multiply]`. Simplify using the standard rewrite rules. Establish `hkap : kapQ g z = G.toBlocks₂₁ * z + G.toBlocks₂₂` using `rfl`. Establish `hjW : jW g z = G.toBlocks₁₁ - w * G.toBlocks₂₁` using `rfl`. Rewrite `h0` using `[hkap]`.

Establish `e12 : G.toBlocks₁₂ = w * (G.toBlocks₂₁ * z + G.toBlocks₂₂) - G.toBlocks₁₁ * z` using `eq_sub_of_add_eq' h0.symm`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[b11, b21, hjW, e12]`. Simplify using `only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws.

Rewrite using `[b22, hkap, hzdef, moeb_zero, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul _ hF, Matrix.mul_one]`.
-/
theorem co_mul {p q : ℕ} {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q)
    (F : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (hF : IsUnit F.toBlocks₂₂.det) (hz : moeb F 0 ∈ hcDom p q)
    (hw : moeb ((g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * F) 0 =
      moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (moeb F 0)) :
    ((g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * F).toBlocks₁₁ -
        moeb ((g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * F) 0 *
          ((g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * F).toBlocks₂₁ =
        jW g (moeb F 0) * (F.toBlocks₁₁ - moeb F 0 * F.toBlocks₂₁) ∧
      ((g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * F).toBlocks₂₂ = kapQ g (moeb F 0) * F.toBlocks₂₂ := by
  set G : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := g.1 with hG
  have h0 := moeb_mul_kapQ hg hz
  rw [← hG] at h0
  rw [hw]
  set z := moeb F 0 with hzdef
  set w := moeb G z with hwdef
  have b11 : (G * F).toBlocks₁₁ = G.toBlocks₁₁ * F.toBlocks₁₁ + G.toBlocks₁₂ * F.toBlocks₂₁ := by
    conv_lhs => rw [← fromBlocks_toBlocks G, ← fromBlocks_toBlocks F, fromBlocks_multiply]
    simp
  have b21 : (G * F).toBlocks₂₁ = G.toBlocks₂₁ * F.toBlocks₁₁ + G.toBlocks₂₂ * F.toBlocks₂₁ := by
    conv_lhs => rw [← fromBlocks_toBlocks G, ← fromBlocks_toBlocks F, fromBlocks_multiply]
    simp
  have b22 : (G * F).toBlocks₂₂ = G.toBlocks₂₁ * F.toBlocks₁₂ + G.toBlocks₂₂ * F.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks G, ← fromBlocks_toBlocks F, fromBlocks_multiply]
    simp
  have hkap : kapQ g z = G.toBlocks₂₁ * z + G.toBlocks₂₂ := rfl
  have hjW : jW g z = G.toBlocks₁₁ - w * G.toBlocks₂₁ := rfl
  rw [hkap] at h0
  have e12 : G.toBlocks₁₂ = w * (G.toBlocks₂₁ * z + G.toBlocks₂₂) - G.toBlocks₁₁ * z := eq_sub_of_add_eq' h0.symm
  refine ⟨?_, ?_⟩
  · rw [b11, b21, hjW, e12]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    abel
  · rw [b22, hkap, hzdef, moeb_zero, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      nonsing_inv_mul _ hF, Matrix.mul_one]

/- English proof (translation)
Establish `hT' : IsUnit Tᴴ.det` using `by rw [det_conjTranspose]; exact hT.star`. Establish `e : ∀ M : Matrix n n ℂ, M = (Tᴴ)⁻¹ * (Tᴴ * M * T * T⁻¹)` using `fun M => by`. Rewrite using `[mul_nonsing_inv_cancel_right _ _ hT, nonsing_inv_mul_cancel_left _ _ hT']`. Rewrite using `[e A, e B, h]`.
-/
theorem conj_cancel {n : Type} [Fintype n] [DecidableEq n] {T A B : Matrix n n ℂ} (hT : IsUnit T.det)
    (h : Tᴴ * A * T = Tᴴ * B * T) : A = B := by
  have hT' : IsUnit Tᴴ.det := by rw [det_conjTranspose]; exact hT.star
  have e : ∀ M : Matrix n n ℂ, M = (Tᴴ)⁻¹ * (Tᴴ * M * T * T⁻¹) := fun M => by
    rw [mul_nonsing_inv_cancel_right _ _ hT, nonsing_inv_mul_cancel_left _ _ hT']
  rw [e A, e B, h]

end GlobalTheory.ShFam.MetLaws

namespace GlobalTheory.ShFam.MetLaws

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up Formalism.UG

/- English proof (translation)
Introduce `D A N j S κ s L k x`. Establish `P1 : ∀ (f : (s.fd k).dom) t, (coW (s.fd k) s.j_le f.1 (s.lab L k t))ᴴ * x.metW L k (s.zOf L k f) t * coW (s.fd k) s.j_le f.1 (s.lab L k t) = x.gramW L k f t ∧ (coOm (s.fd k) s.j_le f.1 (s.lab L k t))ᴴ * x.metOm L k (s.zOf L k f) t * coOm (s.fd k) s.j_le f.1 (s.lab L k t) = x.gram …`. Introduce `f t`. Establish `hz0 : s.zOf L k (s.frameOver L k (s.zOf L k f)) = s.zOf L k f` using `s.zOf_frameOver L k (s.zOf_mem L k f)`. Establish `H` using `GlobalTheory.T.gram_transform_of_coordinate_change D A N j S κ s L k x f (s.frameOver L k (s.zOf L k f)) hz0.symm t`.

Establish `hW` using `isUnit_coW (s.fd k) s.j_le (s.p0_eq k) (s.frameOver L k (s.zOf L k f)).2 (s.lab L k t)`. Establish `hO` using `isUnit_coOm (s.fd k) s.j_le (s.p0_eq k) (s.frameOver L k (s.zOf L k f)).2 (s.lab L k t)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[H.1 _ (mul_nonsing_inv_cancel_left _ _ hW), ToroidalCompactificationData.metW, conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[H.2 _ (mul_nonsing_inv_cancel_left _ _ hO), ToroidalCompactificationData.metOm, conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `⟨P1, ?_⟩` and prove the remaining obligations. Introduce `g hg z hz t`. Establish `hU : g t ∈ Upq j (N - j)` using `gammaU_le _ _ _ (s.p0_eq k) hg t trivial`.

Take `⟨g₀, hg₀, rfl⟩` from `hg`. Use `set f := s.frameOver L k z with hfdef`. Establish `hf : s.zOf L k f = z` using `s.zOf_frameOver L k hz`. Set `f' : (s.fd k).dom` to `⟨lact g₀ f.1, (PairUnfoldPf.lact_mem_dom_iff _ hg₀ f.1).2 f.2⟩`. Establish `hf' : s.zOf L k f' = moebI (toUpq (s.fd k) s.j_le (s.lab L k) g₀) z`.

Rewrite using `[← hf]`. Conclude with `domPt_lact (s.fd k) s.j_le (s.lab L k) (s.p0_eq k) g₀ f.2`. Establish `hG` using `GlobalTheory.T.gram_invariant_under_group_action D A N j S κ s L k x g₀ hg₀ f f' rfl t`. Establish `A1` using `P1 f' t`. Establish `A0` using `P1 f t`.

Rewrite `A1` using `[hf']`. Rewrite `A0` using `[hf]`. Establish `hFr` using `frameCo_lact (s.fd k) s.j_le (s.lab L k) g₀ f.1 t`. Establish `hzt : moeb (frameCo (s.fd k) s.j_le f.1 (s.lab L k t)) 0 = z t` using `congrFun hf t`. Establish `hw : moeb ((toUpq (s.fd k) s.j_le (s.lab L k) g₀ t : Matrix _ _ ℂ) * frameCo (s.fd k) s.j_le f.1 (s.lab L k t)) 0 = moeb (toUpq (s.fd k) s.j_le (s.lab L k) g₀ t : Matrix _ _ ℂ) (moeb (frameCo (s.fd k) s.j_le f.1 (s.lab L k t)) 0)`.

Rewrite using `[← hFr]`. Conclude with `congrFun (domPt_lact (s.fd k) s.j_le (s.lab L k) (s.p0_eq k) g₀ f.2) t`. Establish `hC` using `co_mul hU (frameCo (s.fd k) s.j_le f.1 (s.lab L k t)) (frameCo_isUnit₂₂ (s.fd k) s.j_le (s.p0_eq k) f.2 _) (hzt ▸ hz t) hw`. Establish `eW : coW (s.fd k) s.j_le f'.1 (s.lab L k t) = jW (toUpq (s.fd k) s.j_le (s.lab L k) g₀ t) (z t) * coW (s.fd k) s.j_le f.1 (s.lab L k t)` using `by show coW (s.fd k) s.j_le (lact g₀ f.1) (s.lab L k t) = _`. Simplify using `only [coW]`.

Rewrite using `[hFr, hC.1, hzt]`. Establish `eO : coOm (s.fd k) s.j_le f'.1 (s.lab L k t) = kapQ (toUpq (s.fd k) s.j_le (s.lab L k) g₀ t) (z t) * coOm (s.fd k) s.j_le f.1 (s.lab L k t)` using `by show coOm (s.fd k) s.j_le (lact g₀ f.1) (s.lab L k t) = _`. Simplify using `only [coOm]`. Rewrite using `[hFr, hC.2, hzt]`. Use `⟨conj_cancel (isUnit_coW (s.fd k) s.j_le (s.p0_eq k) f.2 (s.lab L k t)) ?_, conj_cancel (isUnit_coOm (s.fd k) s.j_le (s.p0_eq k) f.2 (s.lab L k t)) ?_⟩` and prove the remaining obligations.

Rewrite using `[A0.1, ← hG.1, ← A1.1, eW, conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[A0.2, ← hG.2, ← A1.2, eO, conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem metLaws : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp) (x : ToroidalCompactificationData s), (∀ (f : (s.fd k).dom) t, (coW (s.fd k) s.j_le f.1 (s.lab L k t))ᴴ * x.metW L k (s.zOf L k f) t * coW (s.fd k) s.j_le f.1 (s.lab L k t) = x.gramW L k f t ∧ (coOm (s.fd k) s.j_le f.1 (s.lab L k t))ᴴ * x.metOm L k (s.zOf L k f) t * coOm (s.fd k) s.j_le f.1 (s.lab L k t) = x.gramOm L k f t) ∧ ∀ g ∈ gammaU (s.fd k) s.j_le (s.lab L k), ∀ z ∈ DomI D.what₂.Tau j (N - j), ∀ t, (jW (g t) (z t))ᴴ * x.metW L k (moebI g z) t * jW (g t) (z t) = x.metW L k z t ∧ (kapQ (g t) (z t))ᴴ * x.metOm L k (moebI g z) t * kapQ (g t) (z t) = x.metOm L k z t := by
  intro D A N j S κ s L k x
  have P1 : ∀ (f : (s.fd k).dom) t, (coW (s.fd k) s.j_le f.1 (s.lab L k t))ᴴ * x.metW L k (s.zOf L k f) t * coW (s.fd k) s.j_le f.1 (s.lab L k t) = x.gramW L k f t ∧ (coOm (s.fd k) s.j_le f.1 (s.lab L k t))ᴴ * x.metOm L k (s.zOf L k f) t * coOm (s.fd k) s.j_le f.1 (s.lab L k t) = x.gramOm L k f t := by
    intro f t
    have hz0 : s.zOf L k (s.frameOver L k (s.zOf L k f)) = s.zOf L k f := s.zOf_frameOver L k (s.zOf_mem L k f)
    have H := GlobalTheory.T.gram_transform_of_coordinate_change D A N j S κ s L k x f (s.frameOver L k (s.zOf L k f)) hz0.symm t
    have hW := isUnit_coW (s.fd k) s.j_le (s.p0_eq k) (s.frameOver L k (s.zOf L k f)).2 (s.lab L k t)
    have hO := isUnit_coOm (s.fd k) s.j_le (s.p0_eq k) (s.frameOver L k (s.zOf L k f)).2 (s.lab L k t)
    refine ⟨?_, ?_⟩
    · rw [H.1 _ (mul_nonsing_inv_cancel_left _ _ hW), ToroidalCompactificationData.metW, conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    · rw [H.2 _ (mul_nonsing_inv_cancel_left _ _ hO), ToroidalCompactificationData.metOm, conjTranspose_mul]
      simp only [Matrix.mul_assoc]
  refine ⟨P1, ?_⟩
  intro g hg z hz t
  have hU : g t ∈ Upq j (N - j) := gammaU_le _ _ _ (s.p0_eq k) hg t trivial
  obtain ⟨g₀, hg₀, rfl⟩ := hg
  set f := s.frameOver L k z with hfdef
  have hf : s.zOf L k f = z := s.zOf_frameOver L k hz
  let f' : (s.fd k).dom := ⟨lact g₀ f.1, (PairUnfoldPf.lact_mem_dom_iff _ hg₀ f.1).2 f.2⟩
  have hf' : s.zOf L k f' = moebI (toUpq (s.fd k) s.j_le (s.lab L k) g₀) z := by
    rw [← hf]
    exact domPt_lact (s.fd k) s.j_le (s.lab L k) (s.p0_eq k) g₀ f.2
  have hG := GlobalTheory.T.gram_invariant_under_group_action D A N j S κ s L k x g₀ hg₀ f f' rfl t
  have A1 := P1 f' t
  have A0 := P1 f t
  rw [hf'] at A1
  rw [hf] at A0
  have hFr := frameCo_lact (s.fd k) s.j_le (s.lab L k) g₀ f.1 t
  have hzt : moeb (frameCo (s.fd k) s.j_le f.1 (s.lab L k t)) 0 = z t := congrFun hf t
  have hw : moeb ((toUpq (s.fd k) s.j_le (s.lab L k) g₀ t : Matrix _ _ ℂ) * frameCo (s.fd k) s.j_le f.1 (s.lab L k t)) 0 =
      moeb (toUpq (s.fd k) s.j_le (s.lab L k) g₀ t : Matrix _ _ ℂ) (moeb (frameCo (s.fd k) s.j_le f.1 (s.lab L k t)) 0) := by
    rw [← hFr]
    exact congrFun (domPt_lact (s.fd k) s.j_le (s.lab L k) (s.p0_eq k) g₀ f.2) t
  have hC := co_mul hU (frameCo (s.fd k) s.j_le f.1 (s.lab L k t))
    (frameCo_isUnit₂₂ (s.fd k) s.j_le (s.p0_eq k) f.2 _) (hzt ▸ hz t) hw
  have eW : coW (s.fd k) s.j_le f'.1 (s.lab L k t) =
      jW (toUpq (s.fd k) s.j_le (s.lab L k) g₀ t) (z t) * coW (s.fd k) s.j_le f.1 (s.lab L k t) := by
    show coW (s.fd k) s.j_le (lact g₀ f.1) (s.lab L k t) = _
    simp only [coW]
    rw [hFr, hC.1, hzt]
  have eO : coOm (s.fd k) s.j_le f'.1 (s.lab L k t) =
      kapQ (toUpq (s.fd k) s.j_le (s.lab L k) g₀ t) (z t) * coOm (s.fd k) s.j_le f.1 (s.lab L k t) := by
    show coOm (s.fd k) s.j_le (lact g₀ f.1) (s.lab L k t) = _
    simp only [coOm]
    rw [hFr, hC.2, hzt]
  refine ⟨conj_cancel (isUnit_coW (s.fd k) s.j_le (s.p0_eq k) f.2 (s.lab L k t)) ?_,
    conj_cancel (isUnit_coOm (s.fd k) s.j_le (s.p0_eq k) f.2 (s.lab L k t)) ?_⟩
  · rw [A0.1, ← hG.1, ← A1.1, eW, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  · rw [A0.2, ← hG.2, ← A1.2, eO, conjTranspose_mul]
    simp only [Matrix.mul_assoc]

end GlobalTheory.ShFam.MetLaws
