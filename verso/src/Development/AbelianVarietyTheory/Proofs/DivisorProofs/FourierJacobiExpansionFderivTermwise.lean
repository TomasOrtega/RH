import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCharBlockPeriodMatrixFourierJacobiExpansion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCharEntireNeZeroAutomorphy
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.FJD

open GlobalTheory.MBLow.Cl.FJ

/- English proof (translation)
Establish `h1 : HasDerivAt (fun s : ℂ => Z + s • W) W 0`. Simplify using `using ((hasDerivAt_id (0 : ℂ)).smul_const W).const_add Z`. Establish `h2 : HasFDerivAt f (fderiv ℂ f Z) (Z + (0 : ℂ) • W)`. Simplify using `using (hf Z).hasFDerivAt`. Conclude with `(h2.comp_hasDerivAt (0 : ℂ) h1).deriv`.
-/
theorem deriv_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ} (hf : Differentiable ℂ f) (Z W : E) :
    deriv (fun s : ℂ => f (Z + s • W)) 0 = fderiv ℂ f Z W := by
  have h1 : HasDerivAt (fun s : ℂ => Z + s • W) W 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const W).const_add Z
  have h2 : HasFDerivAt f (fderiv ℂ f Z) (Z + (0 : ℂ) • W) := by
    simpa using (hf Z).hasFDerivAt
  exact (h2.comp_hasDerivAt (0 : ℂ) h1).deriv

/- English proof (translation)
Establish `hl : Differentiable ℂ (fun s : ℂ => Z + s • W)` using `by fun_prop`. Establish `hd : ∀ i, Differentiable ℂ (fun s : ℂ => f i (Z + s • W))` using `fun i => (hf i).comp hl`. Use `⟨hu.of_nonneg_of_le (fun _ => norm_nonneg _) fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← deriv_line (hf i)]`. Use `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := 0) (R := 1) (C := u i) one_pos (hd i).diffContOnCl (fun s hs => hb i s (by` as an intermediate fact.

Establish `: ‖s‖ = 1` using `by simpa using hs`. Use the proof step `linarith))`. Simplify using `using this`. Establish `h` using `Complex.hasSum_deriv_of_summable_norm (U := Metric.ball (0 : ℂ) 2) (z := 0) (F := fun i s => f i (Z + s • W)) hu (fun i => (hd i).differentiableOn) Metric.isOpen_ball (fun i s hs => hb i s (le_of_lt (by simpa using hs))) (by simp)`. Simplify using `only [hs] at h`.

Rewrite `h` using `[deriv_line hF]`. Simplify using `only [deriv_line (hf _)] at h`. Conclude with `h.tsum_eq`.
-/
theorem termwise {J E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : J → E → ℂ} {F : E → ℂ}
    (hf : ∀ i, Differentiable ℂ (f i)) (hF : Differentiable ℂ F) (hs : ∀ Z, ∑' i, f i Z = F Z) (Z W : E)
    {u : J → ℝ} (hu : Summable u) (hb : ∀ i (s : ℂ), ‖s‖ ≤ 2 → ‖f i (Z + s • W)‖ ≤ u i) :
    (Summable fun i => ‖fderiv ℂ (f i) Z W‖) ∧ ∑' i, fderiv ℂ (f i) Z W = fderiv ℂ F Z W := by
  have hl : Differentiable ℂ (fun s : ℂ => Z + s • W) := by fun_prop
  have hd : ∀ i, Differentiable ℂ (fun s : ℂ => f i (Z + s • W)) := fun i => (hf i).comp hl
  refine ⟨hu.of_nonneg_of_le (fun _ => norm_nonneg _) fun i => ?_, ?_⟩
  · rw [← deriv_line (hf i)]
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := 0) (R := 1) (C := u i) one_pos
      (hd i).diffContOnCl (fun s hs => hb i s (by
        have : ‖s‖ = 1 := by simpa using hs
        linarith))
    simpa using this
  · have h := Complex.hasSum_deriv_of_summable_norm (U := Metric.ball (0 : ℂ) 2) (z := 0)
      (F := fun i s => f i (Z + s • W)) hu (fun i => (hd i).differentiableOn) Metric.isOpen_ball
      (fun i s hs => hb i s (le_of_lt (by simpa using hs))) (by simp)
    simp only [hs] at h
    rw [deriv_line hF] at h
    simp only [deriv_line (hf _)] at h
    exact h.tsum_eq

/- English proof (translation)
Establish `h1` using `abs_le.mp ((Complex.abs_re_le_norm s).trans hs)`. Establish `h2` using `abs_le.mp ((Complex.abs_im_le_norm s).trans hs)`. Simplify using `only [Complex.norm_exp]`. Establish `p1` using `Real.exp_pos (α + (2 + 2 * Complex.I) * c).re`. Establish `p2` using `Real.exp_pos (α + (2 - 2 * Complex.I) * c).re`.

Establish `p3` using `Real.exp_pos (α + (-2 + 2 * Complex.I) * c).re`. Establish `p4` using `Real.exp_pos (α + (-2 - 2 * Complex.I) * c).re`. Apply the tactic sequence `rcases le_total 0 c.re with hr | hr <;> rcases le_total 0 c.im with hi | hi`. Establish `: Real.exp (α + s * c).re ≤ Real.exp (α + (2 - 2 * Complex.I) * c).re` using `Real.exp_le_exp.mpr (by simp; nlinarith)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `: Real.exp (α + s * c).re ≤ Real.exp (α + (2 + 2 * Complex.I) * c).re` using `Real.exp_le_exp.mpr (by simp; nlinarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: Real.exp (α + s * c).re ≤ Real.exp (α + (-2 - 2 * Complex.I) * c).re` using `Real.exp_le_exp.mpr (by simp; nlinarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: Real.exp (α + s * c).re ≤ Real.exp (α + (-2 + 2 * Complex.I) * c).re` using `Real.exp_le_exp.mpr (by simp; nlinarith)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_exp_le_corners (α c s : ℂ) (hs : ‖s‖ ≤ 2) :
    ‖Complex.exp (α + s * c)‖ ≤ ‖Complex.exp (α + (2 + 2 * Complex.I) * c)‖ + ‖Complex.exp (α + (2 - 2 * Complex.I) * c)‖ +
      ‖Complex.exp (α + (-2 + 2 * Complex.I) * c)‖ + ‖Complex.exp (α + (-2 - 2 * Complex.I) * c)‖ := by
  have h1 := abs_le.mp ((Complex.abs_re_le_norm s).trans hs)
  have h2 := abs_le.mp ((Complex.abs_im_le_norm s).trans hs)
  simp only [Complex.norm_exp]
  have p1 := Real.exp_pos (α + (2 + 2 * Complex.I) * c).re
  have p2 := Real.exp_pos (α + (2 - 2 * Complex.I) * c).re
  have p3 := Real.exp_pos (α + (-2 + 2 * Complex.I) * c).re
  have p4 := Real.exp_pos (α + (-2 - 2 * Complex.I) * c).re
  rcases le_total 0 c.re with hr | hr <;> rcases le_total 0 c.im with hi | hi
  · have : Real.exp (α + s * c).re ≤ Real.exp (α + (2 - 2 * Complex.I) * c).re :=
      Real.exp_le_exp.mpr (by simp; nlinarith)
    linarith
  · have : Real.exp (α + s * c).re ≤ Real.exp (α + (2 + 2 * Complex.I) * c).re :=
      Real.exp_le_exp.mpr (by simp; nlinarith)
    linarith
  · have : Real.exp (α + s * c).re ≤ Real.exp (α + (-2 - 2 * Complex.I) * c).re :=
      Real.exp_le_exp.mpr (by simp; nlinarith)
    linarith
  · have : Real.exp (α + s * c).re ≤ Real.exp (α + (-2 + 2 * Complex.I) * c).re :=
      Real.exp_le_exp.mpr (by simp; nlinarith)
    linarith

/- English proof (translation)
Establish `key : ∀ t : ℂ, thT τ a b (Z + t • W) n = Complex.exp ((Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ τ.mulVec ((fun i => (n i : ℂ)) + a)) + 2 * Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ (Z + b))) + t * (2 * Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ W) …`. Introduce `t`. Unfold `thT`. Use `congr 1`. Generalize the expression as in `((fun i => (n i : ℂ)) + a) = v`.

Simplify using `only [dotProduct_add, dotProduct_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [key]`. Conclude with `norm_exp_le_corners _ _ s hs`.
-/
theorem norm_thT_le_corners {k : ℕ} (τ : Matrix (Fin k) (Fin k) ℂ) (a b Z W : Fin k → ℂ) (n : Fin k → ℤ) (s : ℂ)
    (hs : ‖s‖ ≤ 2) :
    ‖thT τ a b (Z + s • W) n‖ ≤ ‖thT τ a b (Z + (2 + 2 * Complex.I) • W) n‖ + ‖thT τ a b (Z + (2 - 2 * Complex.I) • W) n‖ +
      ‖thT τ a b (Z + (-2 + 2 * Complex.I) • W) n‖ + ‖thT τ a b (Z + (-2 - 2 * Complex.I) • W) n‖ := by
  have key : ∀ t : ℂ, thT τ a b (Z + t • W) n =
      Complex.exp ((Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ τ.mulVec ((fun i => (n i : ℂ)) + a)) +
        2 * Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ (Z + b))) +
        t * (2 * Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ W))) := by
    intro t
    unfold thT
    congr 1
    generalize ((fun i => (n i : ℂ)) + a) = v
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    ring
  simp only [key]
  exact norm_exp_le_corners _ _ s hs

def splitE {g g' r : ℕ} (σ : Fin g ≃ Fin g' ⊕ Fin r) : (Fin g → ℤ) ≃ (Fin r → ℤ) × (Fin g' → ℤ) where
  toFun := fun n => (tP σ n, zP σ n)
  invFun := fun p j => Sum.elim p.2 p.1 (σ j)
  left_inv := fun n => by
    funext j
    rcases h : σ j with i | l
    · simp only [h, Sum.elim_inl, zP]; rw [σ.symm_apply_eq.mpr h.symm]
    · simp only [h, Sum.elim_inr, tP]; rw [σ.symm_apply_eq.mpr h.symm]
  right_inv := fun p => by ext <;> simp [zP, tP]

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r)

/- English proof (translation)
Establish `hcv : cv (bX.equivFun χ) = co bX χ`. Use function extensionality and compare the values at `l`. Simplify using `[cv, co, Module.Basis.equivFun_apply]`. Establish `hsymm : ∀ p, splitE σ ((splitE σ).symm p) = p` using `(splitE σ).apply_symm_apply`. Simplify using `only [CD.fj, thetaChar_eq_tsum, ← tsum_mul_left]`.

Use `congr 1`. Use function extensionality and compare the values at `m`. Establish `h1 : tP σ ((splitE σ).symm (bX.equivFun χ, m)) = bX.equivFun χ` using `congrArg Prod.fst (hsymm (bX.equivFun χ, m))`. Establish `h2 : zP σ ((splitE σ).symm (bX.equivFun χ, m)) = m` using `congrArg Prod.snd (hsymm (bX.equivFun χ, m))`. Rewrite using `[thT_full, h1, h2, hcv]`.
-/
theorem fj_eq_tsum (S : Matrix (Fin r) (Fin r) ℂ) (χ : N.X) (Z : Fin g → ℂ) :
    d.fj σ S χ Z = ∑' m, thT (d.full σ S) (d.aF σ) (d.bF σ) Z ((splitE σ).symm (bX.equivFun χ, m)) := by
  have hcv : cv (bX.equivFun χ) = co bX χ := by
    funext l; simp [cv, co, Module.Basis.equivFun_apply]
  have hsymm : ∀ p, splitE σ ((splitE σ).symm p) = p := (splitE σ).apply_symm_apply
  simp only [CD.fj, thetaChar_eq_tsum, ← tsum_mul_left]
  congr 1
  funext m
  have h1 : tP σ ((splitE σ).symm (bX.equivFun χ, m)) = bX.equivFun χ := congrArg Prod.fst (hsymm (bX.equivFun χ, m))
  have h2 : zP σ ((splitE σ).symm (bX.equivFun χ, m)) = m := congrArg Prod.snd (hsymm (bX.equivFun χ, m))
  rw [thT_full, h1, h2, hcv]

/- English proof (translation)
Introduce `j`. Simplify using `only [CD.aF]`. Break down `σ j with i | l` into its components or cases. Conclude with `d.ha i`. Simplify using the standard rewrite rules.
-/
theorem half_aF : Half (d.aF σ) := by
  intro j
  simp only [CD.aF]
  rcases σ j with i | l
  · exact d.ha i
  · simp

/- English proof (translation)
Introduce `j`. Simplify using `only [CD.bF]`. Break down `σ j with i | l` into its components or cases. Conclude with `d.hb i`. Conclude with `d.hb2 l`.
-/
theorem half_bF : Half (d.bF σ) := by
  intro j
  simp only [CD.bF]
  rcases σ j with i | l
  · exact d.hb i
  · exact d.hb2 l

/- English proof (translation)
The claim follows from `(Matrix.IsSymm.fromBlocks d.symm rfl (d.toricPeriodBlock_isSymm.add hS)).submatrix σ`.
-/
theorem full_isSymm {S : Matrix (Fin r) (Fin r) ℂ} (hS : S.IsSymm) : (d.full σ S).IsSymm :=
  (Matrix.IsSymm.fromBlocks d.symm rfl (d.toricPeriodBlock_isSymm.add hS)).submatrix σ

/- English proof (translation)
Establish `h` using `(thetaChar_entire_ne_zero_automorphy g' d.τ d.a d.b d.symm d.pos d.ha d.hb).1`. Establish `hz : Differentiable ℂ (fun Z : Fin g → ℂ => zP σ Z + d.t12 *ᵥ co bX χ)`. Use `Differentiable.add_const _ ?_` and prove the remaining obligations. Unfold `zP`. Use `fun_prop`.

Establish `ht : Differentiable ℂ (fun Z : Fin g → ℂ => co bX χ ⬝ᵥ (tP σ Z + d.b2))`. Simplify using `only [dotProduct, tP, Pi.add_apply]`. Use `fun_prop`. Unfold `CD.fj`. Conclude with `(((ht.const_mul _).const_add _).cexp).mul (h.comp hz)`.
-/
theorem differentiable_fj (S : Matrix (Fin r) (Fin r) ℂ) (χ : N.X) : Differentiable ℂ (d.fj σ S χ) := by
  have h := (thetaChar_entire_ne_zero_automorphy g' d.τ d.a d.b d.symm d.pos d.ha d.hb).1
  have hz : Differentiable ℂ (fun Z : Fin g → ℂ => zP σ Z + d.t12 *ᵥ co bX χ) := by
    refine Differentiable.add_const _ ?_
    unfold zP
    fun_prop
  have ht : Differentiable ℂ (fun Z : Fin g → ℂ => co bX χ ⬝ᵥ (tP σ Z + d.b2)) := by
    simp only [dotProduct, tP, Pi.add_apply]
    fun_prop
  unfold CD.fj
  exact (((ht.const_mul _).const_add _).cexp).mul (h.comp hz)

/- English proof (translation)
Establish `haF : ∀ j, ((d.aF σ j).re : ℂ) = d.aF σ j`. Introduce `j`. Apply the tactic sequence `rcases half_aF d σ j with h | h <;> simp [h]`. Establish `hF : ∀ t : ℂ, Summable fun p => ‖thT (d.full σ S) (d.aF σ) (d.bF σ) (Z + t • W) ((splitE σ).symm p)‖` using `fun t => ((splitE σ).symm.summable_iff (f := fun n => ‖thT (d.full σ S) (d.aF σ) (d.bF σ) (Z + t • W) n‖)).mpr (summable_thT hpos haF (d.bF σ) _)`. Establish `hG` using `(((hF (2 + 2 * Complex.I)).add (hF (2 - 2 * Complex.I))).add (hF (-2 + 2 * Complex.I))).add (hF (-2 - 2 * Complex.I))`.

Use `⟨_, hG.prod.comp_injective bX.equivFun.injective, fun χ s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[fj_eq_tsum]`. Use `(norm_tsum_le_tsum_norm ((hF s).prod_factor _)).trans ?_` and prove the remaining obligations. Conclude with `Summable.tsum_le_tsum (fun m => norm_thT_le_corners _ _ _ Z W _ s hs) ((hF s).prod_factor _) (hG.prod_factor _)`.
-/
theorem exists_bound {S : Matrix (Fin r) (Fin r) ℂ} (hpos : ((d.full σ S).map Complex.im).PosDef) (Z W : Fin g → ℂ) :
    ∃ u : N.X → ℝ, Summable u ∧ ∀ χ (s : ℂ), ‖s‖ ≤ 2 → ‖d.fj σ S χ (Z + s • W)‖ ≤ u χ := by
  have haF : ∀ j, ((d.aF σ j).re : ℂ) = d.aF σ j := by
    intro j
    rcases half_aF d σ j with h | h <;> simp [h]
  have hF : ∀ t : ℂ, Summable fun p => ‖thT (d.full σ S) (d.aF σ) (d.bF σ) (Z + t • W) ((splitE σ).symm p)‖ := fun t =>
    ((splitE σ).symm.summable_iff (f := fun n => ‖thT (d.full σ S) (d.aF σ) (d.bF σ) (Z + t • W) n‖)).mpr
      (summable_thT hpos haF (d.bF σ) _)
  have hG := (((hF (2 + 2 * Complex.I)).add (hF (2 - 2 * Complex.I))).add (hF (-2 + 2 * Complex.I))).add
    (hF (-2 - 2 * Complex.I))
  refine ⟨_, hG.prod.comp_injective bX.equivFun.injective, fun χ s hs => ?_⟩
  rw [fj_eq_tsum]
  refine (norm_tsum_le_tsum_norm ((hF s).prod_factor _)).trans ?_
  exact Summable.tsum_le_tsum (fun m => norm_thT_le_corners _ _ _ Z W _ s hs) ((hF s).prod_factor _) (hG.prod_factor _)

end GlobalTheory.MBLow.Cl.FJD

open GlobalTheory.MBLow.Cl.FJD in

/- English proof (translation)
Introduce `N g' r g bX d σ S hS hpos`. Use `⟨differentiable_fj d σ S, fun Z W => ?_⟩` and prove the remaining obligations. Take `⟨u, hu, hb⟩` from `exists_bound d σ hpos Z W`. Conclude with `termwise (differentiable_fj d σ S) (thetaChar_entire_ne_zero_automorphy g _ _ _ (full_isSymm d σ hS) hpos (half_aF d σ) (half_bF d σ)).1 (fun Z => (fj_expansion N g' r g bX d σ S hS hpos Z).2) Z W hu hb`.
-/
theorem GlobalTheory.MBLow.Cl.fj_expansion_fderiv : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ S : Matrix (Fin r) (Fin r) ℂ, S.IsSymm → ((d.full σ S).map Complex.im).PosDef → (∀ χ, Differentiable ℂ (d.fj σ S χ)) ∧ ∀ Z W, (Summable fun χ => ‖fderiv ℂ (d.fj σ S χ) Z W‖) ∧ ∑' χ, fderiv ℂ (d.fj σ S χ) Z W = fderiv ℂ (thetaChar (d.full σ S) (d.aF σ) (d.bF σ)) Z W := by
  intro N g' r g bX d σ S hS hpos
  refine ⟨differentiable_fj d σ S, fun Z W => ?_⟩
  obtain ⟨u, hu, hb⟩ := exists_bound d σ hpos Z W
  exact termwise (differentiable_fj d σ S)
    (thetaChar_entire_ne_zero_automorphy g _ _ _ (full_isSymm d σ hS) hpos (half_aF d σ) (half_bF d σ)).1
    (fun Z => (fj_expansion N g' r g bX d σ S hS hpos Z).2) Z W hu hb

end
