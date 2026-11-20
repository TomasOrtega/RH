import Mathlib
import Formalism.HermitianCurvature.StatementQ
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.VectorComplexifiedDerivativeCommutator

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.EabGlW

open Formalism.REAL Formalism.QuantumDeterminants

set_option backward.isDefEq.respectTransparency false in
open scoped Norms.Operator in

/- English proof (translation)
Establish `hs` using `NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y`. Establish `h2` using `hs.map (Matrix.mulVec.addMonoidHomLeft v) (Continuous.matrix_mulVec continuous_id continuous_const)`. Establish `e : ((Matrix.mulVec.addMonoidHomLeft v) ∘ fun m : ℕ => ((m.factorial : ℂ)⁻¹) • Y ^ m) = fun m => if m = 0 then v else 0`. Use function extensionality and compare the values at `m`. Use `show (((m.factorial : ℂ)⁻¹) • Y ^ m) *ᵥ v = _`.

Break down `m with _ | m` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[Matrix.smul_mulVec, pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero, smul_zero]`. Simplify using the standard rewrite rules. Rewrite `h2` using `[e]`.

Conclude with `h2.unique (hasSum_ite_eq 0 v)`.
-/
theorem exp_mulVec_fix {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (h : Y *ᵥ v = 0) :
    NormedSpace.exp Y *ᵥ v = v := by
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y
  have h2 := hs.map (Matrix.mulVec.addMonoidHomLeft v)
    (Continuous.matrix_mulVec continuous_id continuous_const)
  have e : ((Matrix.mulVec.addMonoidHomLeft v) ∘ fun m : ℕ => ((m.factorial : ℂ)⁻¹) • Y ^ m) =
      fun m => if m = 0 then v else 0 := by
    funext m
    show (((m.factorial : ℂ)⁻¹) • Y ^ m) *ᵥ v = _
    rcases m with _ | m
    · simp
    · rw [Matrix.smul_mulVec, pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero, smul_zero]
      simp
  rw [e] at h2
  exact h2.unique (hasSum_ite_eq 0 v)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Flow (G : Set (Matrix (Fin n) (Fin n) ℂ)) (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G

def LocExt (G : Set (Matrix (Fin n) (Fin n) ℂ)) (f F : Matrix (Fin n) (Fin n) ℂ → E)
    (U : Set (Matrix (Fin n) (Fin n) ℂ)) : Prop :=
  IsOpen U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ h ∈ U, h ∈ G → f h = F h

/- English proof (translation)
Take `⟨hU, hF, hfF⟩` from `hL`. Unfold `RdV`. Establish `hγ` using `hasDerivAt_mul_exp_smul_zero g X`. Establish `hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g`. Simplify using `[NormedSpace.exp_zero]`.

Establish `hFd : DifferentiableAt ℝ F g` using `(hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)`. Establish `hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0` using `hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm`. Establish `hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0] (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)))`. Establish `hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U` using `hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)`. Use `filter_upwards [hmem] with t ht`.

Conclude with `hfF _ ht (hX g hgG t)`. Rewrite using `[hev.deriv_eq]`. Conclude with `hcomp.deriv`.
-/
theorem loc_ext {G : Set (Matrix (Fin n) (Fin n) ℂ)} {X : Matrix (Fin n) (Fin n) ℂ} (hX : Flow G X)
    {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hL : LocExt G f F U)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ U) (hgG : g ∈ G) :
    RdV X f g = fderiv ℝ F g (g * X) := by
  obtain ⟨hU, hF, hfF⟩ := hL
  unfold RdV
  have hγ := hasDerivAt_mul_exp_smul_zero g X
  have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by
    simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F g (g * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)
    filter_upwards [hmem] with t ht
    exact hfF _ ht (hX g hgG t)
  rw [hev.deriv_eq]
  exact hcomp.deriv

/- English proof (translation)
The claim follows from `(hF.fderiv_of_isOpen hU withTop_enat_infty_add_one_le_infty).clm_apply (mulRightRealCLM Z).contDiff.contDiffOn`.
-/
theorem loc_smooth {F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (Z : Matrix (Fin n) (Fin n) ℂ) :
    ContDiffOn ℝ ∞ (fun k => fderiv ℝ F k (k * Z)) U :=
  (hF.fderiv_of_isOpen hU withTop_enat_infty_add_one_le_infty).clm_apply (mulRightRealCLM Z).contDiff.contDiffOn

/- English proof (translation)
Assemble the required witnesses or components as `⟨hL.1, loc_smooth hL.1 hL.2.1 X, fun _ hh hhG => loc_ext hX hL hh hhG⟩`.
-/
theorem loc_rd_ext {G : Set (Matrix (Fin n) (Fin n) ℂ)} {X : Matrix (Fin n) (Fin n) ℂ} (hX : Flow G X)
    {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hL : LocExt G f F U) :
    LocExt G (RdV X f) (fun k => fderiv ℝ F k (k * X)) U :=
  ⟨hL.1, loc_smooth hL.1 hL.2.1 X, fun _ hh hhG => loc_ext hX hL hh hhG⟩

/- English proof (translation)
Rewrite using `[loc_ext hXY hL hg hgG, loc_ext hX hL hg hgG, loc_ext hY hL hg hgG, Matrix.mul_add, map_add]`.
-/
theorem loc_add {G : Set (Matrix (Fin n) (Fin n) ℂ)} {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : Flow G X) (hY : Flow G Y) (hXY : Flow G (X + Y))
    {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hL : LocExt G f F U)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ U) (hgG : g ∈ G) :
    RdV (X + Y) f g = RdV X f g + RdV Y f g := by
  rw [loc_ext hXY hL hg hgG, loc_ext hX hL hg hgG, loc_ext hY hL hg hgG, Matrix.mul_add, map_add]

/- English proof (translation)
Rewrite using `[loc_ext hXY hL hg hgG, loc_ext hX hL hg hgG, loc_ext hY hL hg hgG, Matrix.mul_sub, map_sub]`.
-/
theorem loc_sub {G : Set (Matrix (Fin n) (Fin n) ℂ)} {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : Flow G X) (hY : Flow G Y) (hXY : Flow G (X - Y))
    {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hL : LocExt G f F U)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ U) (hgG : g ∈ G) :
    RdV (X - Y) f g = RdV X f g - RdV Y f g := by
  rw [loc_ext hXY hL hg hgG, loc_ext hX hL hg hgG, loc_ext hY hL hg hgG, Matrix.mul_sub, map_sub]

/- English proof (translation)
Establish `hU` using `hL.1`. Establish `hF` using `hL.2.1`. Establish `hsA` using `loc_smooth hU hF A`. Establish `hsB` using `loc_smooth hU hF B`. Establish `hLc : LocExt G (fun h => RdV A f h + c • RdV B f h) (fun k => fderiv ℝ F k (k * A) + c • fderiv ℝ F k (k * B)) U` using `⟨hU, hsA.add (hsB.const_smul c), fun h hh hhG => by show RdV A f h + c • RdV B f h = fderiv ℝ F h (h * A) + c • fderiv ℝ F h (h * B)`.

Rewrite using `[loc_ext hA hL hh hhG, loc_ext hB hL hh hhG]⟩`. Rewrite using `[loc_ext hV hLc hg hgG, loc_ext hV (loc_rd_ext hA hL) hg hgG, loc_ext hV (loc_rd_ext hB hL) hg hgG]`. Establish `dA : DifferentiableAt ℝ (fun k => fderiv ℝ F k (k * A)) g` using `(hsA.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)`. Establish `dB : DifferentiableAt ℝ (fun k => fderiv ℝ F k (k * B)) g` using `(hsB.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)`. Establish `hD : HasFDerivAt (fun k => fderiv ℝ F k (k * A) + c • fderiv ℝ F k (k * B)) (fderiv ℝ (fun k => fderiv ℝ F k (k * A)) g + c • fderiv ℝ (fun k => fderiv ℝ F k (k * B)) g) g` using `dA.hasFDerivAt.add (dB.hasFDerivAt.const_smul c)`.

Rewrite using `[hD.fderiv]`. Simplify using the standard rewrite rules.
-/
theorem loc_comb {G : Set (Matrix (Fin n) (Fin n) ℂ)} {V A B : Matrix (Fin n) (Fin n) ℂ}
    (hV : Flow G V) (hA : Flow G A) (hB : Flow G B)
    {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hL : LocExt G f F U)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ U) (hgG : g ∈ G) (c : ℂ) :
    RdV V (fun h => RdV A f h + c • RdV B f h) g = RdV V (RdV A f) g + c • RdV V (RdV B f) g := by
  have hU := hL.1
  have hF := hL.2.1
  have hsA := loc_smooth hU hF A
  have hsB := loc_smooth hU hF B
  have hLc : LocExt G (fun h => RdV A f h + c • RdV B f h)
      (fun k => fderiv ℝ F k (k * A) + c • fderiv ℝ F k (k * B)) U :=
    ⟨hU, hsA.add (hsB.const_smul c), fun h hh hhG => by
      show RdV A f h + c • RdV B f h = fderiv ℝ F h (h * A) + c • fderiv ℝ F h (h * B)
      rw [loc_ext hA hL hh hhG, loc_ext hB hL hh hhG]⟩
  rw [loc_ext hV hLc hg hgG, loc_ext hV (loc_rd_ext hA hL) hg hgG,
    loc_ext hV (loc_rd_ext hB hL) hg hgG]
  have dA : DifferentiableAt ℝ (fun k => fderiv ℝ F k (k * A)) g :=
    (hsA.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have dB : DifferentiableAt ℝ (fun k => fderiv ℝ F k (k * B)) g :=
    (hsB.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hD : HasFDerivAt (fun k => fderiv ℝ F k (k * A) + c • fderiv ℝ F k (k * B))
      (fderiv ℝ (fun k => fderiv ℝ F k (k * A)) g + c • fderiv ℝ (fun k => fderiv ℝ F k (k * B)) g) g :=
    dA.hasFDerivAt.add (dB.hasFDerivAt.const_smul c)
  rw [hD.fderiv]
  simp

/- English proof (translation)
Establish `hU` using `hL.1`. Establish `hF` using `hL.2.1`. Establish `hFa : ContDiffAt ℝ ∞ F g` using `hF.contDiffAt (hU.mem_nhds hg)`. Establish `hc : DifferentiableAt ℝ (fderiv ℝ F) g` using `(hFa.fderiv_right (m := ∞) withTop_enat_infty_add_one_le_infty).differentiableAt (by simp)`. Establish `hd : ∀ Z W : Matrix (Fin n) (Fin n) ℂ, fderiv ℝ (fun k => fderiv ℝ F k (k * Z)) g W = fderiv ℝ (fderiv ℝ F) g W (g * Z) + fderiv ℝ F g (W * Z)`.

Introduce `Z W`. Establish `H` using `(hc.hasFDerivAt.clm_apply (mulRightRealCLM Z).hasFDerivAt).fderiv`. Use `erw [H]`. Conclude with `add_comm _ _`. Establish `e1` using `loc_ext hX (loc_rd_ext hY hL) hg hgG`.

Establish `e2` using `loc_ext hY (loc_rd_ext hX hL) hg hgG`. Establish `e3` using `loc_ext hXY hL hg hgG`. Establish `hsym : IsSymmSndFDerivAt ℝ F g` using `hFa.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)`. Establish `hs2` using `hsym (g * X) (g * Y)`. Rewrite using `[e1, e2, e3, hd, hd]`.

Simplify using `only [Matrix.mul_sub, Matrix.mul_assoc, map_sub]`. Use `erw [hs2]`. Conclude with `add_sub_add_left_eq_sub _ _ _`.
-/
theorem loc_bracket {G : Set (Matrix (Fin n) (Fin n) ℂ)} {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : Flow G X) (hY : Flow G Y) (hXY : Flow G (X * Y - Y * X))
    {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hL : LocExt G f F U)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ U) (hgG : g ∈ G) :
    RdV X (RdV Y f) g - RdV Y (RdV X f) g = RdV (X * Y - Y * X) f g := by
  have hU := hL.1
  have hF := hL.2.1
  have hFa : ContDiffAt ℝ ∞ F g := hF.contDiffAt (hU.mem_nhds hg)
  have hc : DifferentiableAt ℝ (fderiv ℝ F) g :=
    (hFa.fderiv_right (m := ∞) withTop_enat_infty_add_one_le_infty).differentiableAt (by simp)
  have hd : ∀ Z W : Matrix (Fin n) (Fin n) ℂ, fderiv ℝ (fun k => fderiv ℝ F k (k * Z)) g W
      = fderiv ℝ (fderiv ℝ F) g W (g * Z) + fderiv ℝ F g (W * Z) := by
    intro Z W
    have H := (hc.hasFDerivAt.clm_apply (mulRightRealCLM Z).hasFDerivAt).fderiv
    erw [H]
    exact add_comm _ _
  have e1 := loc_ext hX (loc_rd_ext hY hL) hg hgG
  have e2 := loc_ext hY (loc_rd_ext hX hL) hg hgG
  have e3 := loc_ext hXY hL hg hgG
  have hsym : IsSymmSndFDerivAt ℝ F g :=
    hFa.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  have hs2 := hsym (g * X) (g * Y)
  rw [e1, e2, e3, hd, hd]
  simp only [Matrix.mul_sub, Matrix.mul_assoc, map_sub]
  erw [hs2]
  exact add_sub_add_left_eq_sub _ _ _

end Formalism.FourierDecayAlt.Q.EabGlW
