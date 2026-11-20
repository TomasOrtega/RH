import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.DiagInvVal
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.AbLower
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ContinuousPrN

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical Pointwise

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.MZ

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
The claim follows from `Matrix.SpecialLinearGroup.continuous_toGL`.
-/
private theorem cont_gl : Continuous (gl : G1 E → GL (Fin 2) (A E)) := Matrix.SpecialLinearGroup.continuous_toGL

/- English proof (translation)
Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Both sides reduce to the same expression.
-/
private theorem gl_rat (γ : Matrix.SpecialLinearGroup (Fin 2) E) : gl (ratS E γ) = ratGL E 2 (Matrix.SpecialLinearGroup.toGL γ) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rfl

/- English proof (translation)
Take `⟨c, C₀, hc, hC₀, hred⟩` from `hR E`. Take `⟨hL, -, hdec⟩` from `hD E P φ hφ`. Take `⟨B, hB⟩` from `hdec ((gl '' C₀) * C) ((hC₀.image cont_gl).mul hC) c hc 0`. Use `⟨B, fun h k hk => ?_⟩` and prove the remaining obligations. Take `⟨γ, u, b, k₀, hk₀, he, hb⟩` from `hred h`.

Establish `h1 : φ.1 (gl h * k) = φ.1 (gl (nU u * mD b) * (gl k₀ * k))`. Rewrite using `[← hL.2 (Matrix.SpecialLinearGroup.toGL γ) (gl h * k), ← gl_rat, ← mul_assoc, ← mul_assoc, ← map_mul, he, map_mul]`. Rewrite using `[h1]`. Simplify using `using hB u b _ (Set.mul_mem_mul ⟨k₀, hk₀, rfl⟩ hk) hb`.
-/
private theorem bdd (hD : DecE) (hR : RedE) (P : CuspSub E 2) {φ : Sm E 2} (hφ : φ ∈ P.V) {C : Set (GL (Fin 2) (A E))} (hC : IsCompact C) :
    ∃ B : ℝ, ∀ h : G1 E, ∀ k ∈ C, ‖φ.1 (gl h * k)‖ ≤ B := by
  obtain ⟨c, C₀, hc, hC₀, hred⟩ := hR E
  obtain ⟨hL, -, hdec⟩ := hD E P φ hφ
  obtain ⟨B, hB⟩ := hdec ((gl '' C₀) * C) ((hC₀.image cont_gl).mul hC) c hc 0
  refine ⟨B, fun h k hk => ?_⟩
  obtain ⟨γ, u, b, k₀, hk₀, he, hb⟩ := hred h
  have h1 : φ.1 (gl h * k) = φ.1 (gl (nU u * mD b) * (gl k₀ * k)) := by
    rw [← hL.2 (Matrix.SpecialLinearGroup.toGL γ) (gl h * k), ← gl_rat, ← mul_assoc, ← mul_assoc, ← map_mul, he, map_mul]
  rw [h1]
  simpa using hB u b _ (Set.mul_mem_mul ⟨k₀, hk₀, rfl⟩ hk) hb

/- English proof (translation)
Use `set h := GroundTheory.Automorphic.AutomorphicForm.isExpLieAlgebra E 2`. Use `set Y := h.ofLie (Cm.lieEq E 2 X)`. Establish `h3 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • (Y : GroundTheory.Automorphic.AutomorphicForm.ArchMatrix E 2))) (Y : GroundTheory.Automorphic.AutomorphicForm.ArchMatrix E 2) 0`. Simplify using `using hasDerivAt_exp_smul_const (𝕂 := ℝ) (Y : GroundTheory.Automorphic.AutomorphicForm.ArchMatrix E 2) 0`. Establish `h4` using `(Cm.archEq E 2).symm.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3`.

Establish `e : (Cm.archEq E 2).symm Y = X` using `(Cm.archEq E 2).symm_apply_apply X`. Use `⟨fun t => (Cm.grpEq E 2).symm (h.expG (t • Y)), ?_, fun s t => ?_, ?_, h4.congr_deriv e⟩` and prove the remaining obligations. Simplify using `only [zero_smul, h.expG_zero, map_one]`. Establish `e2 : h.expG ((s + t) • Y) = h.expG (s • Y) * h.expG (t • Y)`. Use `Subtype.ext (Units.ext ?_)` and prove the remaining obligations.

Establish `e3 : (((s + t) • Y : GroundTheory.Automorphic.AutomorphicForm.archLie E 2) : GroundTheory.Automorphic.AutomorphicForm.ArchMatrix E 2) = s • (Y : GroundTheory.Automorphic.AutomorphicForm.ArchMatrix E 2) + t • (Y : GroundTheory.Automorphic.AutomorphicForm.ArchMatrix E 2)` using `add_smul s t (Y : GroundTheory.Automorphic.AutomorphicForm.ArchMatrix E 2)`. Conclude with `(congrArg NormedSpace.exp e3).trans (NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) (((Commute.refl _).smul_left s).smul_right t) ((NormedSpace.expSeries_radius_eq_top ℝ (GroundTheory.Automorphic.AutomorphicForm.ArchMatrix E 2)).symm ▸ edist_lt_top _ _) ((NormedSpace.expSeri …`. Conclude with `(congrArg _ e2).trans (map_mul _ _ _)`. Simplify using `only [← Cm.infEmb_grpEq, MulEquiv.apply_symm_apply]`. Conclude with `GroundTheory.Automorphic.AutomorphicForm.continuous_infEmb.comp (h.continuous_expG.comp (continuous_id.smul continuous_const))`.
-/
private theorem curve (X : Lie E 2) : ∃ c : ℝ → GL (Fin 2) (Cinf E), c 0 = 1 ∧ (∀ s t, c (s + t) = c s * c t) ∧
    Continuous (fun t => infGL E 2 (c t)) ∧ HasDerivAt (fun t => toL (c t).val) X 0 := by
  set h := GroundTheory.Automorphic.AutomorphicForm.isExpLieAlgebra E 2
  set Y := h.ofLie (Cm.lieEq E 2 X)
  have h3 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • (Y : GroundTheory.Automorphic.AutomorphicForm.ArchMatrix E 2)))
      (Y : GroundTheory.Automorphic.AutomorphicForm.ArchMatrix E 2) 0 := by
    simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) (Y : GroundTheory.Automorphic.AutomorphicForm.ArchMatrix E 2) 0
  have h4 := (Cm.archEq E 2).symm.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3
  have e : (Cm.archEq E 2).symm Y = X := (Cm.archEq E 2).symm_apply_apply X
  refine ⟨fun t => (Cm.grpEq E 2).symm (h.expG (t • Y)), ?_, fun s t => ?_, ?_, h4.congr_deriv e⟩
  · simp only [zero_smul, h.expG_zero, map_one]
  · have e2 : h.expG ((s + t) • Y) = h.expG (s • Y) * h.expG (t • Y) := by
      refine Subtype.ext (Units.ext ?_)
      have e3 : (((s + t) • Y : GroundTheory.Automorphic.AutomorphicForm.archLie E 2) : GroundTheory.Automorphic.AutomorphicForm.ArchMatrix E 2) =
          s • (Y : GroundTheory.Automorphic.AutomorphicForm.ArchMatrix E 2) + t • (Y : GroundTheory.Automorphic.AutomorphicForm.ArchMatrix E 2) :=
        add_smul s t (Y : GroundTheory.Automorphic.AutomorphicForm.ArchMatrix E 2)
      exact (congrArg NormedSpace.exp e3).trans (NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) (((Commute.refl _).smul_left s).smul_right t)
        ((NormedSpace.expSeries_radius_eq_top ℝ (GroundTheory.Automorphic.AutomorphicForm.ArchMatrix E 2)).symm ▸ edist_lt_top _ _)
        ((NormedSpace.expSeries_radius_eq_top ℝ (GroundTheory.Automorphic.AutomorphicForm.ArchMatrix E 2)).symm ▸ edist_lt_top _ _))
    exact (congrArg _ e2).trans (map_mul _ _ _)
  · simp only [← Cm.infEmb_grpEq, MulEquiv.apply_symm_apply]
    exact GroundTheory.Automorphic.AutomorphicForm.continuous_infEmb.comp (h.continuous_expG.comp (continuous_id.smul continuous_const))

/- English proof (translation)
The claim follows from `Measure.integrableOn_of_bounded hfin.ne hf.aestronglyMeasurable (Eventually.of_forall hB)`.
-/
private theorem integ (N : MeasE E) (hfin : N.μ N.D < ⊤) {f : G1 E → ℂ} (hf : Continuous f) {B : ℝ} (hB : ∀ h, ‖f h‖ ≤ B) :
    IntegrableOn f N.D N.μ :=
  Measure.integrableOn_of_bounded hfin.ne hf.aestronglyMeasurable (Eventually.of_forall hB)

/- English proof (translation)
Establish `h1` using `hasDerivAt_curve φ (g * infGL E 2 (c t)) c X c0 cd`. Establish `h2 : HasDerivAt (fun s => φ.1 (g * infGL E 2 (c t) * infGL E 2 (c (s - t)))) (lieD X φ.1 (g * infGL E 2 (c t))) t` using `HasDerivAt.comp_sub_const t t (by simpa using h1)`. Use `h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ.1 (g * infGL E 2 (c s)) = φ.1 (g * infGL E 2 (c t) * infGL E 2 (c (s - t)))`. Rewrite using `[mul_assoc, ← map_mul, ← cadd, add_sub_cancel]`.
-/
private theorem deriv_curve (φ : Sm E 2) (X : Lie E 2) {c : ℝ → GL (Fin 2) (Cinf E)} (c0 : c 0 = 1) (cadd : ∀ s t, c (s + t) = c s * c t)
    (cd : HasDerivAt (fun t => toL (c t).val) X 0) (g : GL (Fin 2) (A E)) (t : ℝ) :
    HasDerivAt (fun s => φ.1 (g * infGL E 2 (c s))) ((lie E 2 X φ).1 (g * infGL E 2 (c t))) t := by
  have h1 := hasDerivAt_curve φ (g * infGL E 2 (c t)) c X c0 cd
  have h2 : HasDerivAt (fun s => φ.1 (g * infGL E 2 (c t) * infGL E 2 (c (s - t)))) (lieD X φ.1 (g * infGL E 2 (c t))) t :=
    HasDerivAt.comp_sub_const t t (by simpa using h1)
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  change φ.1 (g * infGL E 2 (c s)) = φ.1 (g * infGL E 2 (c t) * infGL E 2 (c (s - t)))
  rw [mul_assoc, ← map_mul, ← cadd, add_sub_cancel]

/- English proof (translation)
Take `⟨c, c0, cadd, ccont, cd⟩` from `curve X`. Establish `hψ : lie E 2 X φ ∈ P.V` using `P.stable (.lie X) φ hφ`. Establish `hCc : IsCompact ((fun t : ℝ => y * infGL E 2 (c t)) '' Set.Icc (-1) 1)` using `isCompact_Icc.image (continuous_const.mul ccont)`. Take `⟨B, hB⟩` from `bdd hD hR P hψ hCc`. Take `⟨B', hB'⟩` from `bdd hD hR P hφ hCc`.

Establish `cφ : ∀ z, Continuous fun h : G1 E => φ.1 (gl h * z)` using `fun z => (hD E P φ hφ).1.1.comp (cont_gl.mul continuous_const)`. Establish `cψ : ∀ z, Continuous fun h : G1 E => (lie E 2 X φ).1 (gl h * z)` using `fun z => (hD E P _ hψ).1.1.comp (cont_gl.mul continuous_const)`. Establish `hz : y * infGL E 2 (c 0) = y` using `by rw [c0, map_one, mul_one]`. Establish `h0m : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1` using `by norm_num`. Use `haveI : IsFiniteMeasure (N.μ.restrict N.D) := ⟨by simpa using hfin⟩`.

Establish `hb` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := N.μ.restrict N.D) (F := fun t h => φ.1 (gl h * (y * infGL E 2 (c t)))) (F' := fun t h => (lie E 2 X φ).1 (gl h * (y * infGL E 2 (c t)))) (x₀ := (0 : ℝ)) (bound := fun _ => B) (s := Set.Ioo (-1) 1) (Ioo_mem_nhds (by norm_num) …`. Simplify `deriv_curve φ X c0 cadd cd (gl h * y) t)` using `only [mul_assoc]`. Establish `e : (fun t : ℝ => ∫ h in N.D, φ.1 (gl h * (y * infGL E 2 (c t))) ∂N.μ) = fun _ => 0` using `funext fun t => h0 _`. Use `hb.2` as an intermediate fact. Rewrite `this` using `[e, hz]`.

Conclude with `this.unique (hasDerivAt_const _ _)`.
-/
private theorem lie_zero (hD : DecE) (hR : RedE) (N : MeasE E) (hfin : N.μ N.D < ⊤) (P : CuspSub E 2) {φ : Sm E 2} (hφ : φ ∈ P.V)
    (h0 : ∀ y, ∫ h in N.D, φ.1 (gl h * y) ∂N.μ = 0) (X : Lie E 2) (y : GL (Fin 2) (A E)) :
    ∫ h in N.D, (lie E 2 X φ).1 (gl h * y) ∂N.μ = 0 := by
  obtain ⟨c, c0, cadd, ccont, cd⟩ := curve X
  have hψ : lie E 2 X φ ∈ P.V := P.stable (.lie X) φ hφ
  have hCc : IsCompact ((fun t : ℝ => y * infGL E 2 (c t)) '' Set.Icc (-1) 1) := isCompact_Icc.image (continuous_const.mul ccont)
  obtain ⟨B, hB⟩ := bdd hD hR P hψ hCc
  obtain ⟨B', hB'⟩ := bdd hD hR P hφ hCc
  have cφ : ∀ z, Continuous fun h : G1 E => φ.1 (gl h * z) := fun z => (hD E P φ hφ).1.1.comp (cont_gl.mul continuous_const)
  have cψ : ∀ z, Continuous fun h : G1 E => (lie E 2 X φ).1 (gl h * z) := fun z => (hD E P _ hψ).1.1.comp (cont_gl.mul continuous_const)
  have hz : y * infGL E 2 (c 0) = y := by rw [c0, map_one, mul_one]
  have h0m : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
  haveI : IsFiniteMeasure (N.μ.restrict N.D) := ⟨by simpa using hfin⟩
  have hb := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := N.μ.restrict N.D)
    (F := fun t h => φ.1 (gl h * (y * infGL E 2 (c t)))) (F' := fun t h => (lie E 2 X φ).1 (gl h * (y * infGL E 2 (c t))))
    (x₀ := (0 : ℝ)) (bound := fun _ => B) (s := Set.Ioo (-1) 1) (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun t => (cφ _).aestronglyMeasurable)
    (integ N hfin (cφ _) fun h => hB' h _ ⟨0, h0m, rfl⟩)
    (cψ _).aestronglyMeasurable
    (Eventually.of_forall fun h t ht => hB h _ ⟨t, Set.Ioo_subset_Icc_self ht, rfl⟩)
    (integrable_const _)
    (Eventually.of_forall fun h t _ => by
      simpa only [mul_assoc] using deriv_curve φ X c0 cadd cd (gl h * y) t)
  have e : (fun t : ℝ => ∫ h in N.D, φ.1 (gl h * (y * infGL E 2 (c t))) ∂N.μ) = fun _ => 0 := funext fun t => h0 _
  have := hb.2
  rw [e, hz] at this
  exact this.unique (hasDerivAt_const _ _)

private def Ker (N : MeasE E) (P : CuspSub E 2) (hI : ∀ φ ∈ P.V, ∀ y, IntegrableOn (fun h : G1 E => φ.1 (gl h * y)) N.D N.μ) :
    Submodule ℂ (Sm E 2) where
  carrier := {φ | φ ∈ P.V ∧ ∀ y, ∫ h in N.D, φ.1 (gl h * y) ∂N.μ = 0}
  add_mem' := fun {a b} ha hb => ⟨P.V.add_mem ha.1 hb.1, fun y => by
    change ∫ h in N.D, (a.1 (gl h * y) + b.1 (gl h * y)) ∂N.μ = 0
    rw [integral_add (hI a ha.1 y) (hI b hb.1 y), ha.2, hb.2, add_zero]⟩
  zero_mem' := ⟨P.V.zero_mem, fun y => by
    change ∫ h in N.D, (0 : ℂ) ∂N.μ = 0
    simp⟩
  smul_mem' := fun c a ha => ⟨P.V.smul_mem c ha.1, fun y => by
    change ∫ h in N.D, c * a.1 (gl h * y) ∂N.μ = 0
    rw [integral_const_mul, ha.2, mul_zero]⟩

/- English proof (translation)
Introduce `o φ hφ`. Use `⟨P.stable o φ hφ.1, fun y => ?_⟩` and prove the remaining obligations. Consider the cases of `o with`. Consider the case `fin k`. Express the relevant statement in the definitionally equal form `∫ h in N.D, φ.1 (gl h * y * finGL E 2 k) ∂N.μ = 0`.

Simplify `hφ.2 (y * finGL E 2 k)` using `only [mul_assoc]`. Consider the case `cpt k`. Express the relevant statement in the definitionally equal form `∫ h in N.D, φ.1 (gl h * y * infGL E 2 (Unitary.toUnits k)) ∂N.μ = 0`. Simplify `hφ.2 (y * infGL E 2 (Unitary.toUnits k))` using `only [mul_assoc]`. Consider the case `lie X => exact lie_zero hD hR N hfin P hφ.1 hφ.2 X y`.
-/
private theorem ker_stable (hD : DecE) (hR : RedE) (N : MeasE E) (hfin : N.μ N.D < ⊤) (P : CuspSub E 2) (hI) :
    IsStable (Ker N P hI) := by
  intro o φ hφ
  refine ⟨P.stable o φ hφ.1, fun y => ?_⟩
  cases o with
  | fin k =>
    change ∫ h in N.D, φ.1 (gl h * y * finGL E 2 k) ∂N.μ = 0
    simpa only [mul_assoc] using hφ.2 (y * finGL E 2 k)
  | cpt k =>
    change ∫ h in N.D, φ.1 (gl h * y * infGL E 2 (Unitary.toUnits k)) ∂N.μ = 0
    simpa only [mul_assoc] using hφ.2 (y * infGL E 2 (Unitary.toUnits k))
  | lie X => exact lie_zero hD hR N hfin P hφ.1 hφ.2 X y

/- English proof (translation)
Establish `hd : w.val.det = 1` using `congrArg Units.val hw`. Establish `e : gl (⟨w.val, hd⟩ : G1 E) = w` using `Units.ext rfl`. Establish `hLR : LRat fun x => φ.1 (x * y)` using `fun γ g => by`. Express the relevant statement in the definitionally equal form `φ.1 (ratGL E 2 γ * g * y) = φ.1 (g * y)`. Rewrite using `[mul_assoc, hL.2]`.

Use `((hV E N).2 _ hLR).1 ⟨w.val, hd⟩` as an intermediate fact. Rewrite `this` using `[e]`. Simplify `this` using `only [mean, mul_assoc]`.
-/
private theorem mean_det (hV : InvE) (N : MeasE E) {φ : Sm E 2} (hL : Pp.Lf φ.1) (y w : GL (Fin 2) (A E))
    (hw : Matrix.GeneralLinearGroup.det w = 1) :
    ∫ h in N.D, φ.1 (gl h * (w * y)) ∂N.μ = ∫ h in N.D, φ.1 (gl h * y) ∂N.μ := by
  have hd : w.val.det = 1 := congrArg Units.val hw
  have e : gl (⟨w.val, hd⟩ : G1 E) = w := Units.ext rfl
  have hLR : LRat fun x => φ.1 (x * y) := fun γ g => by
    change φ.1 (ratGL E 2 γ * g * y) = φ.1 (g * y)
    rw [mul_assoc, hL.2]
  have := ((hV E N).2 _ hLR).1 ⟨w.val, hd⟩
  rw [e] at this
  simpa only [mean, mul_assoc] using this

/- English proof (translation)
Establish `hm : finRep E 2 k φ ∈ P.V` using `P.stable (.fin k) φ hφ`. Establish `hmem : finRep E 2 k φ - φ ∈ Ker N P hI`. Use `⟨P.V.sub_mem hm hφ, fun y => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `∫ h in N.D, (φ.1 (gl h * y * finGL E 2 k) - φ.1 (gl h * y)) ∂N.μ = 0`. Establish `e : ∀ h : G1 E, gl h * y * finGL E 2 k = gl h * ((y * finGL E 2 k * y⁻¹) * y)` using `fun h => by group`.

Establish `hw : Matrix.GeneralLinearGroup.det (y * finGL E 2 k * y⁻¹) = 1`. Rewrite using `[map_mul, map_mul, hk, mul_one, map_inv, mul_inv_cancel]`. Rewrite using `[integral_sub (by simp only [e]; exact hI _ hφ ((y * finGL E 2 k * y⁻¹) * y)) (hI φ hφ y)]`. Simplify using `only [e]`. Rewrite using `[mean_det hV N (hL φ hφ) y _ hw, sub_self]`.

Rewrite `hmem` using `[hK, Submodule.mem_bot]`. Use `congrFun (congrArg Subtype.val hmem) g` as an intermediate fact. Conclude with `sub_eq_zero.1 this`.
-/
private theorem fixed (hV : InvE) (N : MeasE E) (P : CuspSub E 2) (hI) (hL : ∀ φ ∈ P.V, Pp.Lf φ.1) (hK : Ker N P hI = ⊥) {φ : Sm E 2} (hφ : φ ∈ P.V)
    (k : GL (Fin 2) (Af E)) (hk : Matrix.GeneralLinearGroup.det (finGL E 2 k) = 1) (g : GL (Fin 2) (A E)) :
    φ.1 (g * finGL E 2 k) = φ.1 g := by
  have hm : finRep E 2 k φ ∈ P.V := P.stable (.fin k) φ hφ
  have hmem : finRep E 2 k φ - φ ∈ Ker N P hI := by
    refine ⟨P.V.sub_mem hm hφ, fun y => ?_⟩
    change ∫ h in N.D, (φ.1 (gl h * y * finGL E 2 k) - φ.1 (gl h * y)) ∂N.μ = 0
    have e : ∀ h : G1 E, gl h * y * finGL E 2 k = gl h * ((y * finGL E 2 k * y⁻¹) * y) := fun h => by group
    have hw : Matrix.GeneralLinearGroup.det (y * finGL E 2 k * y⁻¹) = 1 := by
      rw [map_mul, map_mul, hk, mul_one, map_inv, mul_inv_cancel]
    rw [integral_sub (by simp only [e]; exact hI _ hφ ((y * finGL E 2 k * y⁻¹) * y)) (hI φ hφ y)]
    simp only [e]
    rw [mean_det hV N (hL φ hφ) y _ hw, sub_self]
  rw [hK, Submodule.mem_bot] at hmem
  have := congrFun (congrArg Subtype.val hmem) g
  exact sub_eq_zero.1 this

/- English proof (translation)
The claim follows from `map_mul _ x y`.
-/
private theorem gl_mul (x y : G1 E) : gl (x * y) = gl x * gl y := map_mul _ x y
/- English proof (translation)
The claim follows from `map_one _`.
-/
private theorem gl_one : gl (1 : G1 E) = 1 := map_one _

/- English proof (translation)
Use `⟨_, (congrArg gl (?_ : nU (rt q) = ratS E (⟨!![1, q; 0, 1], by simp [Matrix.det_fin_two]⟩ : Matrix.SpecialLinearGroup (Fin 2) E))).trans (gl_rat _)⟩` and prove the remaining obligations. Use `Subtype.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(!![1, rt q; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) i j = ((!![1, q; 0, 1] : Matrix (Fin 2) (Fin 2) E).map (algebraMap E (A E))) i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`.
-/
private theorem gl_nU_rat (q : E) : ∃ γ : GL (Fin 2) E, gl (nU (rt q)) = ratGL E 2 γ := by
  refine ⟨_, (congrArg gl (?_ : nU (rt q) = ratS E (⟨!![1, q; 0, 1], by simp [Matrix.det_fin_two]⟩ : Matrix.SpecialLinearGroup (Fin 2) E))).trans (gl_rat _)⟩
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  change (!![1, rt q; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) i j = ((!![1, q; 0, 1] : Matrix (Fin 2) (Fin 2) E).map (algebraMap E (A E))) i j
  fin_cases i <;> fin_cases j <;> simp

private noncomputable def iI (x : InfiniteAdeleRing E) : A E := (x, 0)

/- English proof (translation)
The claim follows from `(continuous_id.prodMk continuous_const : Continuous fun x : InfiniteAdeleRing E => ((x, 0) : InfiniteAdeleRing E × Af E))`.
-/
private theorem cont_iI : Continuous (iI : InfiniteAdeleRing E → A E) :=
  (continuous_id.prodMk continuous_const : Continuous fun x : InfiniteAdeleRing E => ((x, 0) : InfiniteAdeleRing E × Af E))

/- English proof (translation)
Use `⟨Matrix.GeneralLinearGroup.map (pFin E) (gl (nU (sFin E a))), ?_⟩` and prove the remaining obligations. Establish `h1 : Matrix.GeneralLinearGroup.map (pInf E) (gl (nU (sFin E a))) = 1`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Establish `h0 : pInf E (sFin E a) = 0` using `map_zero (infEq E).symm`. Express the relevant statement in the definitionally equal form `pInf E ((gl (nU (sFin E a))).val i j) = (1 : Matrix (Fin 2) (Fin 2) (Cinf E)) i j`.

Rewrite using `[show (gl (nU (sFin E a))).val i j = (!![1, sFin E a; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) i j from rfl]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [h0]`. Use `infGL_mul_finGL (gl (nU (sFin E a)))` as an intermediate fact. Rewrite `this` using `[h1, map_one, one_mul]`. Conclude with `this.symm`.
-/
private theorem gl_nU_fin (a : Af E) : ∃ k, gl (nU (sFin E a)) = finGL E 2 k := by
  refine ⟨Matrix.GeneralLinearGroup.map (pFin E) (gl (nU (sFin E a))), ?_⟩
  have h1 : Matrix.GeneralLinearGroup.map (pInf E) (gl (nU (sFin E a))) = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    have h0 : pInf E (sFin E a) = 0 := map_zero (infEq E).symm
    change pInf E ((gl (nU (sFin E a))).val i j) = (1 : Matrix (Fin 2) (Fin 2) (Cinf E)) i j
    rw [show (gl (nU (sFin E a))).val i j = (!![1, sFin E a; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) i j from rfl]
    fin_cases i <;> fin_cases j <;> simp [h0]
  have := infGL_mul_finGL (gl (nU (sFin E a)))
  rw [h1, map_one, one_mul] at this
  exact this.symm

/- English proof (translation)
Use `set S : AddSubgroup (A E) := { carrier := {b | ∀ g, φ.1 (gl (nU b) * g) = φ.1 g} add_mem' := fun {x y} hx hy g => by rw [M.nU_add, gl_mul, mul_assoc, hx, hy] zero_mem' := fun g => by rw [M.nU_zero, gl_one, one_mul] neg_mem' := fun {x} hx g => by`. Use `hx (gl (nU (-x)) * g)` as an intermediate fact. Rewrite `this` using `[← mul_assoc, ← gl_mul, ← M.nU_add, add_neg_cancel, M.nU_zero, gl_one, one_mul]`. Conclude with `this.symm } with hS`. Establish `hq : ∀ q : E, rt q ∈ S` using `fun q g => by`.

Take `⟨γ, e⟩` from `gl_nU_rat q`. Rewrite using `[e]`. Conclude with `hL.2 γ g`. Establish `hf : ∀ a : Af E, sFin E a ∈ S` using `fun a g => by`. Take `⟨k₀, e⟩` from `gl_nU_fin a`.

Use `set u := Matrix.GeneralLinearGroup.map (pFin E) g`. Use `set y := Matrix.GeneralLinearGroup.map (pInf E) g`. Establish `hg : infGL E 2 y * finGL E 2 u = g` using `infGL_mul_finGL g`. Establish `e1 : g * finGL E 2 (u⁻¹ * k₀ * u) = finGL E 2 k₀ * g`. Rewrite using `[map_mul, map_mul, map_inv]`.

Use `nth_rw 1 [← hg]`. Rewrite using `[← mul_assoc, ← mul_assoc, mul_assoc (infGL E 2 y), mul_inv_cancel, mul_one, infGL_comm, mul_assoc, hg]`. Establish `hd : Matrix.GeneralLinearGroup.det (finGL E 2 k₀) = 1`. Rewrite using `[← e]`. Conclude with `Units.ext (nU (sFin E a)).2`.

Establish `hd' : Matrix.GeneralLinearGroup.det (finGL E 2 (u⁻¹ * k₀ * u)) = 1`. Simplify using `only [map_mul, map_inv, hd, mul_one, inv_mul_cancel]`. Rewrite using `[e, ← e1]`. Conclude with `hfix _ hd' g`. Establish `hinf : ∀ x : InfiniteAdeleRing E, iI x ∈ S`.

Introduce `x`. Use `(InfiniteAdeleRing.denseRange_algebraMap E).induction_on (p := fun x => iI x ∈ S) x ?_ ?_` and prove the remaining obligations. Establish `: {x : InfiniteAdeleRing E | iI x ∈ S} = ⋂ g, {x | φ.1 (gl (nU (iI x)) * g) = φ.1 g}` using `Set.ext fun x => ⟨fun h => Set.mem_iInter.2 h, fun h => Set.mem_iInter.1 h⟩`. Rewrite using `[this]`. Conclude with `isClosed_iInter fun g => isClosed_eq (hL.1.comp ((cont_gl.comp (M.continuous_nU.comp cont_iI)).mul continuous_const)) continuous_const`.

Introduce `q`. Establish `e : rt q = iI (algebraMap E (InfiniteAdeleRing E) q) + sFin E (algebraMap E (Af E) q)` using `Prod.ext (add_zero _).symm (zero_add _).symm`. Rewrite using `[eq_sub_of_add_eq e.symm]`. Conclude with `S.sub_mem (hq q) (hf _)`. Establish `e : b = iI b.1 + sFin E b.2` using `Prod.ext (add_zero _).symm (zero_add _).symm`.

Establish `: b ∈ S`. Rewrite using `[e]`. Conclude with `S.add_mem (hinf _) (hf _)`. Conclude with `this g`.
-/
private theorem left_inv {φ : Sm E 2} (hL : Pp.Lf φ.1)
    (hfix : ∀ k, Matrix.GeneralLinearGroup.det (finGL E 2 k) = 1 → ∀ g, φ.1 (g * finGL E 2 k) = φ.1 g) (b : A E) (g : GL (Fin 2) (A E)) :
    φ.1 (gl (nU b) * g) = φ.1 g := by
  set S : AddSubgroup (A E) :=
    { carrier := {b | ∀ g, φ.1 (gl (nU b) * g) = φ.1 g}
      add_mem' := fun {x y} hx hy g => by rw [M.nU_add, gl_mul, mul_assoc, hx, hy]
      zero_mem' := fun g => by rw [M.nU_zero, gl_one, one_mul]
      neg_mem' := fun {x} hx g => by
        have := hx (gl (nU (-x)) * g)
        rw [← mul_assoc, ← gl_mul, ← M.nU_add, add_neg_cancel, M.nU_zero, gl_one, one_mul] at this
        exact this.symm } with hS
  have hq : ∀ q : E, rt q ∈ S := fun q g => by
    obtain ⟨γ, e⟩ := gl_nU_rat q
    rw [e]
    exact hL.2 γ g
  have hf : ∀ a : Af E, sFin E a ∈ S := fun a g => by
    obtain ⟨k₀, e⟩ := gl_nU_fin a
    set u := Matrix.GeneralLinearGroup.map (pFin E) g
    set y := Matrix.GeneralLinearGroup.map (pInf E) g
    have hg : infGL E 2 y * finGL E 2 u = g := infGL_mul_finGL g
    have e1 : g * finGL E 2 (u⁻¹ * k₀ * u) = finGL E 2 k₀ * g := by
      rw [map_mul, map_mul, map_inv]
      nth_rw 1 [← hg]
      rw [← mul_assoc, ← mul_assoc, mul_assoc (infGL E 2 y), mul_inv_cancel, mul_one, infGL_comm, mul_assoc, hg]
    have hd : Matrix.GeneralLinearGroup.det (finGL E 2 k₀) = 1 := by
      rw [← e]
      exact Units.ext (nU (sFin E a)).2
    have hd' : Matrix.GeneralLinearGroup.det (finGL E 2 (u⁻¹ * k₀ * u)) = 1 := by
      simp only [map_mul, map_inv, hd, mul_one, inv_mul_cancel]
    rw [e, ← e1]
    exact hfix _ hd' g
  have hinf : ∀ x : InfiniteAdeleRing E, iI x ∈ S := by
    intro x
    refine (InfiniteAdeleRing.denseRange_algebraMap E).induction_on (p := fun x => iI x ∈ S) x ?_ ?_
    · have : {x : InfiniteAdeleRing E | iI x ∈ S} = ⋂ g, {x | φ.1 (gl (nU (iI x)) * g) = φ.1 g} :=
        Set.ext fun x => ⟨fun h => Set.mem_iInter.2 h, fun h => Set.mem_iInter.1 h⟩
      rw [this]
      exact isClosed_iInter fun g => isClosed_eq (hL.1.comp ((cont_gl.comp (M.continuous_nU.comp cont_iI)).mul continuous_const)) continuous_const
    · intro q
      have e : rt q = iI (algebraMap E (InfiniteAdeleRing E) q) + sFin E (algebraMap E (Af E) q) :=
        Prod.ext (add_zero _).symm (zero_add _).symm
      rw [eq_sub_of_add_eq e.symm]
      exact S.sub_mem (hq q) (hf _)
  have e : b = iI b.1 + sFin E b.2 := Prod.ext (add_zero _).symm (zero_add _).symm
  have : b ∈ S := by
    rw [e]
    exact S.add_mem (hinf _) (hf _)
  exact this g

/- English proof (translation)
Establish `hfin` using `hV E N`. Establish `hL : ∀ φ ∈ P.V, Pp.Lf φ.1` using `fun φ hφ => (hD E P φ hφ).1`. Establish `hI : ∀ φ ∈ P.V, ∀ y, IntegrableOn (fun h : G1 E => φ.1 (gl h * y)) N.D N.μ` using `fun φ hφ y => by`. Take `⟨B, hB⟩` from `bdd hD hR P hφ (isCompact_singleton (x := y))`. Conclude with `integ N hfin ((hL φ hφ).1.comp (cont_gl.mul continuous_const)) fun h => hB h y rfl`.

Break down `P.irred (Ker N P hI) (fun φ h => h.1) (ker_stable hD hR N hfin P hI) with hK | hK` into its components or cases. Establish `hz : φ = 0`. Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations. Establish `h1` using `(hD E P φ hφ).2.1 g`. Simplify using `only [left_inv (hL φ hφ) (fun k hk g => fixed hIv N P hI hL hK hφ k hk g)] at h1`.

Simplify `h1` using `[Measure.real, adeleMeasure_fundamentalSet]`. Rewrite using `[hz]`. Simplify using the standard rewrite rules. Establish `: φ ∈ Ker N P hI` using `hK ▸ hφ`. Conclude with `this.2 y`.
-/
private theorem main (hD : DecE) (hR : RedE) (hV : VolE) (hIv : InvE) (N : MeasE E) (P : CuspSub E 2) {φ : Sm E 2} (hφ : φ ∈ P.V)
    (y : GL (Fin 2) (A E)) : ∫ h in N.D, φ.1 (gl h * y) ∂N.μ = 0 := by
  have hfin := hV E N
  have hL : ∀ φ ∈ P.V, Pp.Lf φ.1 := fun φ hφ => (hD E P φ hφ).1
  have hI : ∀ φ ∈ P.V, ∀ y, IntegrableOn (fun h : G1 E => φ.1 (gl h * y)) N.D N.μ := fun φ hφ y => by
    obtain ⟨B, hB⟩ := bdd hD hR P hφ (isCompact_singleton (x := y))
    exact integ N hfin ((hL φ hφ).1.comp (cont_gl.mul continuous_const)) fun h => hB h y rfl
  rcases P.irred (Ker N P hI) (fun φ h => h.1) (ker_stable hD hR N hfin P hI) with hK | hK
  · have hz : φ = 0 := by
      refine Subtype.ext (funext fun g => ?_)
      have h1 := (hD E P φ hφ).2.1 g
      simp only [left_inv (hL φ hφ) (fun k hk g => fixed hIv N P hI hL hK hφ k hk g)] at h1
      simpa [Measure.real, adeleMeasure_fundamentalSet] using h1
    rw [hz]
    simp
  · have : φ ∈ Ker N P hI := hK ▸ hφ
    exact this.2 y

end UpperTheory.ConvolutionTheory.RankTwoDescent.MZ

/- English proof (translation)
Introduce `hD E _ _ _ _ _ _ N P φ hφ y`. Conclude with `MZ.main hD redE volE invE N P hφ y`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.meanZero :
    DecE → MeanZero := by
  intro hD E _ _ _ _ _ _ N P φ hφ y
  exact MZ.main hD redE volE invE N P hφ y
