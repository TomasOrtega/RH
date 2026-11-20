import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open Matrix

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c Y p A b S₀ _ _ P₀ h σ`. Establish `hM : ⊤ ≤ (frX P₀ ≫ Y.j) ⁻¹ᵁ (A.k b).M.U` using `le_preimage_mono (A.k b).le h`. Use `set U := ((A.k b).u σ).map (ev (frX P₀ ≫ Y.j) _ h) with hUdef`. Use `set W := ((A.k b).w σ).map (ev (frX P₀ ≫ Y.j) _ h) with hWdef`. Establish `hWU : W * U = 1`.

Rewrite using `[hUdef, hWdef, ← Matrix.map_mul, (A.k b).wu, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hfix : ∀ v : Fin (A.k b).M.n → S₀, vec (A.k b).M.toMChart _ hM v ∈ eigLie c (frX P₀ ≫ Y.j) σ → U *ᵥ (W *ᵥ v) = v`. Introduce `v hv`. Take `⟨a, ha⟩` from `((A.k b).fix_iff σ _ h hM v).1 (((LowRank.pm_gen p (A.k b).M.toMChart σ (frX_snd P₀) hM).1 v).1 ((vec_mem_eigLie _ _ hM σ v).1 hv))`. Rewrite using `[← ha, Matrix.mulVec_mulVec (M := W) (N := U), hWU, Matrix.one_mulVec]`.

Establish `hspan` using `LowRank.initSpan_frVec_top P₀ (A.k b).M.toMChart hM σ`. Establish `hmem : ∀ j, frVec Y P₀ rfl σ j ∈ eigLie c (frX P₀ ≫ Y.j) σ` using `fun j => by`. Rewrite using `[← hspan]`. Conclude with `Submodule.subset_span ⟨j, j.isLt, rfl⟩`. Set `cv : Fin (Dw.mult σ) → Fin (A.k b).M.n → S₀` to `fun j => (vec (A.k b).M.toMChart _ hM).symm (frVec Y P₀ rfl σ j)`.

Establish `hcvv : ∀ j, vec (A.k b).M.toMChart _ hM (cv j) = frVec Y P₀ rfl σ j` using `fun j => LinearEquiv.apply_symm_apply _ _`. Establish `hcv : ∀ j, U *ᵥ (W *ᵥ cv j) = cv j` using `fun j => hfix _ (by rw [hcvv]; exact hmem j)`. Set `C : Matrix (Fin (A.k b).M.n) (Fin (Dw.mult σ)) S₀` to `Matrix.of fun i j => cv j i`. Establish `hUT : U * (W * C) = C`. Use extensionality with `i j`.

Use `congrFun (hcv j) i` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct] at this`. Simplify using `only [Matrix.mul_apply, C, Matrix.of_apply]`. Conclude with `this`. Use `⟨W * C, ?_, ?_⟩` and prove the remaining obligations.

Establish `hcol : ∀ r, vec (A.k b).M.toMChart _ hM (U *ᵥ Pi.single r 1) ∈ eigLie c (frX P₀ ≫ Y.j) σ` using `fun r => (vec_mem_eigLie _ _ hM σ _).2 (((LowRank.pm_gen p (A.k b).M.toMChart σ (frX_snd P₀) hM).1 _).2 (((A.k b).fix_iff σ _ h hM _).2 ⟨_, rfl⟩))`. Establish `hc : ∀ r, ∃ a : Fin (Dw.mult σ) → S₀, ∑ j, a j • cv j = U *ᵥ Pi.single r 1` using `fun r => by`. Use `hcol r` as an intermediate fact. Rewrite `this` using `[← hspan, mem_initSpan]`. Take `⟨a, -, ha⟩` from `this`.

Use `⟨a, (vec (A.k b).M.toMChart _ hM).injective ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum, ← ha]`. Simplify using `only [map_smul, hcvv]`. Use `choose a ha using hc`. Establish `hCT : C * Matrix.of (fun j r => a r j) = U`.

Use extensionality with `i r`. Use `congrFun (ha r) i` as an intermediate fact. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single_one] at this`. Simplify using `only [Matrix.mul_apply, C, Matrix.of_apply]`. Rewrite `this` using `[Matrix.col_apply]`.

Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Establish `h1 : W * C * Matrix.of (fun j r => a r j) = 1` using `by rw [Matrix.mul_assoc, hCT, hWU]`. Establish `h2` using `congrArg Matrix.det h1`. Rewrite `h2` using `[Matrix.det_mul, Matrix.det_one]`.

Conclude with `IsUnit.of_mul_eq_one _ h2`. Introduce `S' _ _ ψ P' hP h' hM' j`. Establish `e : spMap ψ.toRingHom ≫ (frX P₀ ≫ Y.j) = frX P' ≫ Y.j` using `by rw [← Category.assoc, frX_frMap hP]`. Rewrite using `[← tanPull_frVec hP rfl rfl e σ j, ← hcvv j, tanPull_vec (A.k b).M.toMChart ψ.toRingHom e hM hM']`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Establish `hev : ((A.k b).u σ).map (ev (frX P' ≫ Y.j) _ h') = U.map ψ`. Use extensionality with `r s`. Simplify using `only [Matrix.map_apply, hUdef]`. Rewrite using `[ev_congr e.symm _ h' (e ▸ h'), ev_spMap ψ.toRingHom _ _ h]`.

Both sides reduce to the same expression. Establish `hm : U.map ψ * (W * C).map ψ = (U * (W * C)).map ψ` using `(Matrix.map_mul (f := (ψ : S₀ →+* S'))).symm`. Rewrite using `[hev, hm, hUT]`. Both sides reduce to the same expression.
-/
theorem frVec_eq_eigFrame_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (b : A.B) (S₀ : Type) [CommRing S₀] [Algebra c.F S₀] (P₀ : FrPt Xo c S₀), ⊤ ≤ (frX P₀ ≫ Y.j) ⁻¹ᵁ (A.k b).V → ∀ σ : E →+* ℂ, ∃ T : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S₀, IsUnit T.det ∧ ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (ψ : S₀ →ₐ[c.F] S') (P' : FrPt Xo c S'), FrMap ψ P₀ P' → ∀ (h' : ⊤ ≤ (frX P' ≫ Y.j) ⁻¹ᵁ (A.k b).V) (hM' : ⊤ ≤ (frX P' ≫ Y.j) ⁻¹ᵁ (A.k b).M.U) (j : Fin (Dw.mult σ)), frVec Y P' rfl σ j = vec (A.k b).M.toMChart _ hM' (fun r => ((((A.k b).u σ).map (ev _ _ h')) * T.map ψ) r j) := by
  intro E _ _ _ H Dw l Xo c Y p A b S₀ _ _ P₀ h σ
  have hM : ⊤ ≤ (frX P₀ ≫ Y.j) ⁻¹ᵁ (A.k b).M.U := le_preimage_mono (A.k b).le h
  set U := ((A.k b).u σ).map (ev (frX P₀ ≫ Y.j) _ h) with hUdef
  set W := ((A.k b).w σ).map (ev (frX P₀ ≫ Y.j) _ h) with hWdef
  have hWU : W * U = 1 := by
    rw [hUdef, hWdef, ← Matrix.map_mul, (A.k b).wu, Matrix.map_one _ (map_zero _) (map_one _)]
  have hfix : ∀ v : Fin (A.k b).M.n → S₀, vec (A.k b).M.toMChart _ hM v ∈ eigLie c (frX P₀ ≫ Y.j) σ →
      U *ᵥ (W *ᵥ v) = v := by
    intro v hv
    obtain ⟨a, ha⟩ := ((A.k b).fix_iff σ _ h hM v).1
      (((LowRank.pm_gen p (A.k b).M.toMChart σ (frX_snd P₀) hM).1 v).1 ((vec_mem_eigLie _ _ hM σ v).1 hv))
    rw [← ha, Matrix.mulVec_mulVec (M := W) (N := U), hWU, Matrix.one_mulVec]
  have hspan := LowRank.initSpan_frVec_top P₀ (A.k b).M.toMChart hM σ
  have hmem : ∀ j, frVec Y P₀ rfl σ j ∈ eigLie c (frX P₀ ≫ Y.j) σ := fun j => by
    rw [← hspan]
    exact Submodule.subset_span ⟨j, j.isLt, rfl⟩
  let cv : Fin (Dw.mult σ) → Fin (A.k b).M.n → S₀ := fun j => (vec (A.k b).M.toMChart _ hM).symm (frVec Y P₀ rfl σ j)
  have hcvv : ∀ j, vec (A.k b).M.toMChart _ hM (cv j) = frVec Y P₀ rfl σ j := fun j =>
    LinearEquiv.apply_symm_apply _ _
  have hcv : ∀ j, U *ᵥ (W *ᵥ cv j) = cv j := fun j => hfix _ (by rw [hcvv]; exact hmem j)
  let C : Matrix (Fin (A.k b).M.n) (Fin (Dw.mult σ)) S₀ := Matrix.of fun i j => cv j i
  have hUT : U * (W * C) = C := by
    ext i j
    have := congrFun (hcv j) i
    simp only [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, C, Matrix.of_apply]
    exact this
  refine ⟨W * C, ?_, ?_⟩
  · have hcol : ∀ r, vec (A.k b).M.toMChart _ hM (U *ᵥ Pi.single r 1) ∈ eigLie c (frX P₀ ≫ Y.j) σ := fun r =>
      (vec_mem_eigLie _ _ hM σ _).2 (((LowRank.pm_gen p (A.k b).M.toMChart σ (frX_snd P₀) hM).1 _).2
        (((A.k b).fix_iff σ _ h hM _).2 ⟨_, rfl⟩))
    have hc : ∀ r, ∃ a : Fin (Dw.mult σ) → S₀, ∑ j, a j • cv j = U *ᵥ Pi.single r 1 := fun r => by
      have := hcol r
      rw [← hspan, mem_initSpan] at this
      obtain ⟨a, -, ha⟩ := this
      refine ⟨a, (vec (A.k b).M.toMChart _ hM).injective ?_⟩
      rw [map_sum, ← ha]
      simp only [map_smul, hcvv]
    choose a ha using hc
    have hCT : C * Matrix.of (fun j r => a r j) = U := by
      ext i r
      have := congrFun (ha r) i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single_one] at this
      simp only [Matrix.mul_apply, C, Matrix.of_apply]
      rw [Matrix.col_apply] at this
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have h1 : W * C * Matrix.of (fun j r => a r j) = 1 := by rw [Matrix.mul_assoc, hCT, hWU]
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_one] at h2
    exact IsUnit.of_mul_eq_one _ h2
  · intro S' _ _ ψ P' hP h' hM' j
    have e : spMap ψ.toRingHom ≫ (frX P₀ ≫ Y.j) = frX P' ≫ Y.j := by rw [← Category.assoc, frX_frMap hP]
    rw [← tanPull_frVec hP rfl rfl e σ j, ← hcvv j, tanPull_vec (A.k b).M.toMChart ψ.toRingHom e hM hM']
    congr 1
    funext i
    have hev : ((A.k b).u σ).map (ev (frX P' ≫ Y.j) _ h') = U.map ψ := by
      ext r s
      simp only [Matrix.map_apply, hUdef]
      rw [ev_congr e.symm _ h' (e ▸ h'), ev_spMap ψ.toRingHom _ _ h]
      rfl
    have hm : U.map ψ * (W * C).map ψ = (U * (W * C)).map ψ := (Matrix.map_mul (f := (ψ : S₀ →+* S'))).symm
    rw [hev, hm, hUT]
    rfl

end GlobalTheory.FlagMod.FieldFlag
