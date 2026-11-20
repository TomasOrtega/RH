import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashEvalSmoothWeightLowering
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.RationalGL2InfiniteFiniteFactor
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashUnnormalizedConstMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertHolomorphicUnnormalizedSlashOfPos
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.LiftSmooth

open Matrix

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def PSet (F : Type) [Field F] : Set (TR.Lie F 2) := {x | ∀ v, 0 < (Matrix.of x).det v}

/- English proof (translation)
Establish `: PSet F = ⋂ v : InfinitePlace F, (fun x : TR.Lie F 2 => (Matrix.of x).det v) ⁻¹' Set.Ioi 0`. Use extensionality with `x`. Simplify using `[PSet]`. Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun v => isOpen_Ioi.preimage ((continuous_apply v).comp TR.contDiff_det.continuous)`.
-/
theorem isOpen_PSet : IsOpen (PSet F) := by
  have : PSet F = ⋂ v : InfinitePlace F, (fun x : TR.Lie F 2 => (Matrix.of x).det v) ⁻¹' Set.Ioi 0 := by
    ext x; simp [PSet]
  rw [this]
  exact isOpen_iInter_of_finite fun v =>
    isOpen_Ioi.preimage ((continuous_apply v).comp TR.contDiff_det.continuous)

/- English proof (translation)
The claim follows from `(Matrix.isUnit_iff_isUnit_det _).2 (Pi.isUnit_iff.2 fun v => (hx v).ne'.isUnit)`.
-/
theorem isUnit_of_mem_PSet {x : TR.Lie F 2} (hx : x ∈ PSet F) : IsUnit (Matrix.of x) :=
  (Matrix.isUnit_iff_isUnit_det _).2 (Pi.isUnit_iff.2 fun v => (hx v).ne'.isUnit)

/- English proof (translation)
Introduce `v` and use `by simp`.
-/
theorem pos_one : Pos (1 : GL (Fin 2) (InfinitePlace F → ℝ)) := fun v => by simp

/- English proof (translation)
Use `set gi := Matrix.GeneralLinearGroup.map (TR.pInf F) g`. Use `set gf := Matrix.GeneralLinearGroup.map (pFin F) g`. Take `⟨τ, hτ⟩` from `(GlobalTheory.T.rational_GL2_infinite_finite_factor F 1).2 gi`. Establish `hdec` using `(GlobalTheory.T.rational_GL2_infinite_finite_factor F τ).1`. Use `set M := toInf τ * gi`.

Use `set f := sl k M (Ψ (toFin τ * gf))`. Establish `hf : Hol f` using `((GlobalTheory.HilbertThetaSeries.HolKeep.main F k (Ψ (toFin τ * gf)) (Ψ (toFin τ * gf)) 1 (hΨ _) (hΨ _)).2.2.2.2.2 M hτ).2`. Establish `hmain : ∀ u : GL (Fin 2) (InfinitePlace F → ℝ), Pos u → φ (g * TR.infGL F 2 u) = sl k u f fun _ => UpperHalfPlane.I`. Introduce `u hu`. Establish `hc` using `GlobalTheory.HilbertThetaSeries.SlashCocycle.slash_cocycle F k M u (Ψ (toFin τ * gf)) hτ hu`.

Establish `e : ratGL F 2 τ * (g * TR.infGL F 2 u) = TR.infGL F 2 (M * u) * finGL F 2 (toFin τ * gf)`. Rewrite using `[hdec]`. Apply the tactic sequence `refine TR.ga_ext ?_ ?_ <;> simp [map_mul, gi, gf, M, mul_assoc]`. Rewrite using `[← hL.1 τ, e, hL.2 _ hc.1, hc.2.2.2.1]`. Use `⟨f, hf, ?_, hmain⟩` and prove the remaining obligations.

Establish `h1` using `hmain 1 pos_one`. Rewrite `h1` using `[map_one, mul_one]`. Rewrite using `[h1, (GlobalTheory.HilbertThetaSeries.SlashCocycle.slash_cocycle F k 1 1 f pos_one pos_one).2.2.2.2.2]`.
-/
theorem key (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : GA F 2 → ℂ) (hΨ : ∀ g, Hol (Ψ g))
    (hL : IsLift k Ψ φ) (g : GA F 2) :
    ∃ f : Hn F → ℂ, Hol f ∧ f (fun _ => UpperHalfPlane.I) = φ g ∧
      ∀ u : GL (Fin 2) (InfinitePlace F → ℝ), Pos u →
        φ (g * TR.infGL F 2 u) = sl k u f fun _ => UpperHalfPlane.I := by
  set gi := Matrix.GeneralLinearGroup.map (TR.pInf F) g
  set gf := Matrix.GeneralLinearGroup.map (pFin F) g
  obtain ⟨τ, hτ⟩ := (GlobalTheory.T.rational_GL2_infinite_finite_factor F 1).2 gi
  have hdec := (GlobalTheory.T.rational_GL2_infinite_finite_factor F τ).1
  set M := toInf τ * gi
  set f := sl k M (Ψ (toFin τ * gf))
  have hf : Hol f := ((GlobalTheory.HilbertThetaSeries.HolKeep.main F k (Ψ (toFin τ * gf)) (Ψ (toFin τ * gf)) 1 (hΨ _) (hΨ _)).2.2.2.2.2 M hτ).2
  have hmain : ∀ u : GL (Fin 2) (InfinitePlace F → ℝ), Pos u →
      φ (g * TR.infGL F 2 u) = sl k u f fun _ => UpperHalfPlane.I := by
    intro u hu
    have hc := GlobalTheory.HilbertThetaSeries.SlashCocycle.slash_cocycle F k M u (Ψ (toFin τ * gf)) hτ hu
    have e : ratGL F 2 τ * (g * TR.infGL F 2 u) = TR.infGL F 2 (M * u) * finGL F 2 (toFin τ * gf) := by
      rw [hdec]
      refine TR.ga_ext ?_ ?_ <;> simp [map_mul, gi, gf, M, mul_assoc]
    rw [← hL.1 τ, e, hL.2 _ hc.1, hc.2.2.2.1]
  refine ⟨f, hf, ?_, hmain⟩
  have h1 := hmain 1 pos_one
  rw [map_one, mul_one] at h1
  rw [h1, (GlobalTheory.HilbertThetaSeries.SlashCocycle.slash_cocycle F k 1 1 f pos_one pos_one).2.2.2.2.2]

/- English proof (translation)
Take `⟨w, hw⟩` from `isUnit_of_mem_PSet hy`. Establish `e : y = TR.toL w.val` using `hw.symm`. Substitute `e` using the available equality. Establish `hpw : Pos w` using `hy`. Rewrite using `[TR.chart_val, hfe w hpw, hA w hpw]`.
-/
theorem chart_eq (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : GA F 2 → ℂ) (hΨ : ∀ g, Hol (Ψ g))
    (hL : IsLift k Ψ φ) (g : GA F 2) (f : Hn F → ℂ)
    (hfe : ∀ u : GL (Fin 2) (InfinitePlace F → ℝ), Pos u →
        φ (g * TR.infGL F 2 u) = sl k u f fun _ => UpperHalfPlane.I)
    (A : (Fin 2 → Fin 2 → InfinitePlace F → ℝ) → ℂ)
    (hA : ∀ h : GL (Fin 2) (InfinitePlace F → ℝ), Pos h → A (Matrix.of.symm h.val) = sl k h f fun _ => UpperHalfPlane.I)
    {y : TR.Lie F 2} (hy : y ∈ PSet F) : TR.chart φ g y = A y := by
  obtain ⟨w, hw⟩ := isUnit_of_mem_PSet hy
  have e : y = TR.toL w.val := hw.symm
  subst e
  have hpw : Pos w := hy
  rw [TR.chart_val, hfe w hpw, hA w hpw]

end GlobalTheory.HilbertThetaSeries.LiftSmooth

open GlobalTheory.HilbertThetaSeries.LiftSmooth in
/- English proof (translation)
Introduce `F _ _ _ k Ψ φ hΨ hL`. Establish `hsm : φ ∈ TR.Sm F 2`. Introduce `g`. Apply `contDiffOn_of_locally_contDiffOn` to reduce the goal to its premises. Introduce `x hx`.

Take `⟨u, hu⟩` from `id hx`. Establish `ex : x = TR.toL u.val` using `hu.symm`. Take `⟨f, hf, -, hfe⟩` from `key k Ψ φ hΨ hL (g * TR.infGL F 2 u)`. Take `⟨A, hA1, hA2, -⟩` from `GlobalTheory.T.hilbert_slash_eval_smooth_weight_lowering F k f hf`. Use `set L := TR.lmul (TR.toL (u⁻¹).val)`.

Use `⟨L ⁻¹' PSet F, isOpen_PSet.preimage L.continuous, ?_, ?_⟩` and prove the remaining obligations. Use `show ∀ v, 0 < (Matrix.of (L x)).det v`. Introduce `v`. Establish `: Matrix.of (L x) = 1`. Substitute `ex` using the available equality.

Use `show ((u⁻¹ : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix _ _ _) * u.val = 1`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Simplify using the standard rewrite rules. Use `(hA2.comp L.contDiff.contDiffOn fun y hy => hy.2).congr ?_` and prove the remaining obligations.

Introduce `y hy`. Establish `hy1 : IsUnit (Matrix.of y)` using `hy.1`. Take `⟨w, hw⟩` from `hy1`. Establish `ey : y = TR.toL w.val` using `hw.symm`. Establish `hLy : L y = TR.toL (u⁻¹ * w).val` using `by subst ey; rfl`.

Establish `hpos : Pos (u⁻¹ * w)`. Introduce `v`. Use `hy.2 v` as an intermediate fact. Rewrite `this` using `[hLy]`. Conclude with `this`.

Simplify using `only [Function.comp_apply]`. Rewrite using `[hLy, hA1 _ hpos, ← hfe _ hpos, ey, TR.chart_val, mul_assoc, ← map_mul, mul_inv_cancel_left]`. Use `⟨hsm, fun v => ?_⟩` and prove the remaining obligations. Establish `hD : ∀ g, ∃ A : (Fin 2 → Fin 2 → InfinitePlace F → ℝ) → ℂ, TR.chart φ g =ᶠ[nhds (TR.oneL F 2)] A ∧ fderiv ℝ A (Matrix.of.symm 1) (Matrix.of.symm (Matrix.single 0 1 (Pi.single v 1))) - fderiv ℝ A (Matrix.of.symm 1) (Matrix.of.symm (Matrix.single 1 0 (Pi.single v 1))) = Complex.I * …`. Introduce `g`.

Take `⟨f, hf, hfg, hfe⟩` from `key k Ψ φ hΨ hL g`. Take `⟨A, hA1, -, hA3⟩` from `GlobalTheory.T.hilbert_slash_eval_smooth_weight_lowering F k f hf`. Take `⟨h1, h2⟩` from `hA3 v _ fun _ _ => rfl`. Use `⟨A, ?_, ?_, h2⟩` and prove the remaining obligations. Establish `hmem : TR.oneL F 2 ∈ PSet F` using `fun w => by simp`.

Conclude with `Filter.eventually_of_mem (isOpen_PSet.mem_nhds hmem) fun y hy => chart_eq k Ψ φ hΨ hL g f hfe A hA1 hy`. Rewrite using `[h1, hfg]`. Prove the components needed by the constructor for the conclusion. Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations. Take `⟨A, hA, h1, -⟩` from `hD g`.

Use `show TR.lieD _ φ g - TR.lieD _ φ g = (Complex.I * k) * φ g`. Rewrite using `[TR.lieD, TR.lieD, hA.fderiv_eq, h1]`. Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations. Take `⟨A, hA, -, h2⟩` from `hD g`. Use `show TR.lieD _ φ g - TR.lieD _ φ g = Complex.I * (TR.lieD _ φ g + TR.lieD _ φ g)`.

Rewrite using `[TR.lieD, TR.lieD, TR.lieD, TR.lieD, hA.fderiv_eq, h2]`.
-/
theorem GlobalTheory.HilbertThetaSeries.lift_smooth_lowering : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : GA F 2 → ℂ), (∀ g, Hol (Ψ g)) → IsLift k Ψ φ → ∃ h : φ ∈ TR.Sm F 2, ∀ v, TR.Eop v 0 1 ⟨φ, h⟩ - TR.Eop v 1 0 ⟨φ, h⟩ = (Complex.I * k) • (⟨φ, h⟩ : TR.Sm F 2) ∧ TR.Eop v 0 0 ⟨φ, h⟩ - TR.Eop v 1 1 ⟨φ, h⟩ = Complex.I • (TR.Eop v 0 1 ⟨φ, h⟩ + TR.Eop v 1 0 ⟨φ, h⟩) := by
  intro F _ _ _ k Ψ φ hΨ hL
  classical
  have hsm : φ ∈ TR.Sm F 2 := by
    intro g
    apply contDiffOn_of_locally_contDiffOn
    intro x hx
    obtain ⟨u, hu⟩ := id hx
    have ex : x = TR.toL u.val := hu.symm
    obtain ⟨f, hf, -, hfe⟩ := key k Ψ φ hΨ hL (g * TR.infGL F 2 u)
    obtain ⟨A, hA1, hA2, -⟩ := GlobalTheory.T.hilbert_slash_eval_smooth_weight_lowering F k f hf
    set L := TR.lmul (TR.toL (u⁻¹).val)
    refine ⟨L ⁻¹' PSet F, isOpen_PSet.preimage L.continuous, ?_, ?_⟩
    · show ∀ v, 0 < (Matrix.of (L x)).det v
      intro v
      have : Matrix.of (L x) = 1 := by
        subst ex
        show ((u⁻¹ : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix _ _ _) * u.val = 1
        simp
      rw [this]; simp
    · refine (hA2.comp L.contDiff.contDiffOn fun y hy => hy.2).congr ?_
      intro y hy
      have hy1 : IsUnit (Matrix.of y) := hy.1
      obtain ⟨w, hw⟩ := hy1
      have ey : y = TR.toL w.val := hw.symm
      have hLy : L y = TR.toL (u⁻¹ * w).val := by subst ey; rfl
      have hpos : Pos (u⁻¹ * w) := by
        intro v; have := hy.2 v; rw [hLy] at this; exact this
      simp only [Function.comp_apply]
      rw [hLy, hA1 _ hpos, ← hfe _ hpos, ey, TR.chart_val, mul_assoc, ← map_mul, mul_inv_cancel_left]
  refine ⟨hsm, fun v => ?_⟩
  have hD : ∀ g, ∃ A : (Fin 2 → Fin 2 → InfinitePlace F → ℝ) → ℂ,
      TR.chart φ g =ᶠ[nhds (TR.oneL F 2)] A ∧
      fderiv ℝ A (Matrix.of.symm 1) (Matrix.of.symm (Matrix.single 0 1 (Pi.single v 1))) -
          fderiv ℝ A (Matrix.of.symm 1) (Matrix.of.symm (Matrix.single 1 0 (Pi.single v 1))) =
        Complex.I * k * φ g ∧
      fderiv ℝ A (Matrix.of.symm 1) (Matrix.of.symm (Matrix.single 0 0 (Pi.single v 1))) -
          fderiv ℝ A (Matrix.of.symm 1) (Matrix.of.symm (Matrix.single 1 1 (Pi.single v 1))) =
        Complex.I * (fderiv ℝ A (Matrix.of.symm 1) (Matrix.of.symm (Matrix.single 0 1 (Pi.single v 1))) +
          fderiv ℝ A (Matrix.of.symm 1) (Matrix.of.symm (Matrix.single 1 0 (Pi.single v 1)))) := by
    intro g
    obtain ⟨f, hf, hfg, hfe⟩ := key k Ψ φ hΨ hL g
    obtain ⟨A, hA1, -, hA3⟩ := GlobalTheory.T.hilbert_slash_eval_smooth_weight_lowering F k f hf
    obtain ⟨h1, h2⟩ := hA3 v _ fun _ _ => rfl
    refine ⟨A, ?_, ?_, h2⟩
    · have hmem : TR.oneL F 2 ∈ PSet F := fun w => by simp
      exact Filter.eventually_of_mem (isOpen_PSet.mem_nhds hmem) fun y hy => chart_eq k Ψ φ hΨ hL g f hfe A hA1 hy
    · rw [h1, hfg]
  constructor
  · refine Subtype.ext (funext fun g => ?_)
    obtain ⟨A, hA, h1, -⟩ := hD g
    show TR.lieD _ φ g - TR.lieD _ φ g = (Complex.I * k) * φ g
    rw [TR.lieD, TR.lieD, hA.fderiv_eq, h1]
  · refine Subtype.ext (funext fun g => ?_)
    obtain ⟨A, hA, -, h2⟩ := hD g
    show TR.lieD _ φ g - TR.lieD _ φ g = Complex.I * (TR.lieD _ φ g + TR.lieD _ φ g)
    rw [TR.lieD, TR.lieD, TR.lieD, TR.lieD, hA.fderiv_eq, h2]

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.HilbertThetaSeries.lift_smooth_lowering | exact GlobalTheory.HilbertThetaSeries.lift_smooth_lowering | (intros; apply GlobalTheory.HilbertThetaSeries.lift_smooth_lowering <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.adelic_lift_mem_smooth_killed_by_lowering : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : GA F 2 → ℂ), (∀ g, Hol (Ψ g)) → IsLift k Ψ φ → ∃ h : φ ∈ TR.Sm F 2, ∀ v, TR.Eop v 0 1 ⟨φ, h⟩ - TR.Eop v 1 0 ⟨φ, h⟩ = (Complex.I * k) • (⟨φ, h⟩ : TR.Sm F 2) ∧ TR.Eop v 0 0 ⟨φ, h⟩ - TR.Eop v 1 1 ⟨φ, h⟩ = Complex.I • (TR.Eop v 0 1 ⟨φ, h⟩ + TR.Eop v 1 0 ⟨φ, h⟩) := by
  first | exact @GlobalTheory.HilbertThetaSeries.lift_smooth_lowering | exact GlobalTheory.HilbertThetaSeries.lift_smooth_lowering | (intros; apply GlobalTheory.HilbertThetaSeries.lift_smooth_lowering <;> assumption)
