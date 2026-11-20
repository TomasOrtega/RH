import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBlocks
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialBlockDecomposition
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SamePotBlock
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FA.Flat

/- English proof (translation)
Establish `h1 : AnalyticAt ℂ (fun y => Complex.log (G y / G u)) u` using `(hG.div_const (c := G u)).clog (by simp [div_self h0])`. Establish `h2 : (fun y => Real.log ‖G y‖) =ᶠ[𝓝 u] fun y => (Complex.log (G y / G u)).re + Real.log ‖G u‖ * (fun _ => (1 : ℝ)) y` using `by filter_upwards [hG.continuousAt.eventually_ne h0] with y hy`. Rewrite using `[Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.2 hy) (norm_ne_zero_iff.2 h0)]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : ContDiffAt ℝ 2 (fun y => (Complex.log (G y / G u)).re) u` using `Complex.reCLM.contDiff.contDiffAt.comp u (h1.restrictScalars (𝕜 := ℝ)).contDiffAt`.

Rewrite using `[levi_congr h2, levi_add_smul _ h3 contDiffAt_const, levi_re_analytic h1]`. Simplify using `[levi]`.
-/
theorem levi_log_norm {e : ℕ} {G : (Fin e → ℂ) → ℂ} {u : Fin e → ℂ} (hG : AnalyticAt ℂ G u) (h0 : G u ≠ 0)
    (w : Fin e → ℂ) : levi (fun y => Real.log ‖G y‖) u w = 0 := by
  have h1 : AnalyticAt ℂ (fun y => Complex.log (G y / G u)) u :=
    (hG.div_const (c := G u)).clog (by simp [div_self h0])
  have h2 : (fun y => Real.log ‖G y‖) =ᶠ[𝓝 u]
      fun y => (Complex.log (G y / G u)).re + Real.log ‖G u‖ * (fun _ => (1 : ℝ)) y := by
    filter_upwards [hG.continuousAt.eventually_ne h0] with y hy
    rw [Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.2 hy) (norm_ne_zero_iff.2 h0)]
    ring
  have h3 : ContDiffAt ℝ 2 (fun y => (Complex.log (G y / G u)).re) u :=
    Complex.reCLM.contDiff.contDiffAt.comp u (h1.restrictScalars (𝕜 := ℝ)).contDiffAt
  rw [levi_congr h2, levi_add_smul _ h3 contDiffAt_const, levi_re_analytic h1]
  simp [levi]

/- English proof (translation)
The claim follows from `(M.blk_none p).2 fun hq => hq.2 h`.
-/
theorem blk_none_of_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
    {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j) {p : Ψ × Fin N} (h : (p.2 : ℕ) + 1 = N) :
    M.blk p = none := (M.blk_none p).2 fun hq => hq.2 h

/- English proof (translation)
Unfold `FlagModel.dy`. Rewrite using `[dif_neg hk, blk_none_of_top M h]`. Simplify using the standard rewrite rules.
-/
theorem dy_eq_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
    {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j) {p : Ψ × Fin N} (h : (p.2 : ℕ) + 1 = N)
    {k : K} (hk : ¬ ∀ p', M.blk p' ≠ some k) : M.dy p k = 0 := by
  unfold FlagModel.dy
  rw [dif_neg hk, blk_none_of_top M h]
  simp

/- English proof (translation)
Establish `e : (gramHead (sigForm N j) N g).det = (gramOf (sigForm N j) g).det`. Unfold `gramHead`. Conclude with `Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (p := fun a : Fin N => (a : ℕ) < N) fun a => a.2) _`. Establish `hd : ‖(Matrix.diagonal fun i => ((sigForm N j i : ℝ) : ℂ)).det‖ = 1`. Rewrite using `[Matrix.det_diagonal, norm_prod]`.

Use `Finset.prod_eq_one fun a _ => ?_` and prove the remaining obligations. Unfold `sigForm`. Apply the tactic sequence `split_ifs <;> simp`. Unfold `gramLog`. Rewrite using `[e, gramOf, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul, hd, Matrix.det_conjTranspose, norm_star, mul_one, ← pow_two, Real.log_pow]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gramLog_top {N : ℕ} (j : ℕ) (g : Matrix (Fin N) (Fin N) ℂ) :
    gramLog (sigForm N j) N g = Real.log ‖g.det‖ := by
  have e : (gramHead (sigForm N j) N g).det = (gramOf (sigForm N j) g).det := by
    unfold gramHead
    exact Matrix.det_submatrix_equiv_self
      (Equiv.subtypeUnivEquiv (p := fun a : Fin N => (a : ℕ) < N) fun a => a.2) _
  have hd : ‖(Matrix.diagonal fun i => ((sigForm N j i : ℝ) : ℂ)).det‖ = 1 := by
    rw [Matrix.det_diagonal, norm_prod]
    refine Finset.prod_eq_one fun a _ => ?_
    unfold sigForm
    split_ifs <;> simp
  unfold gramLog
  rw [e, gramOf, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul, hd, Matrix.det_conjTranspose, norm_star,
    mul_one, ← pow_two, Real.log_pow]
  push_cast
  ring

/- English proof (translation)
Unfold `stepPot`. Use `split_ifs with h1`. Establish `e1 : N - j + ((i : ℕ) + 1) = N` using `by omega`. Establish `e2 : N - j = 0` using `by omega`. Rewrite using `[e1, gramLog_top, e2]`.

Establish `: gramLog (sigForm N j) 0 g = 0`. Unfold `gramLog`. Use `haveI : IsEmpty {a : Fin N // (a : ℕ) < 0} := ⟨fun a => by have := a.2; omega⟩`. Simplify using the standard rewrite rules. Rewrite using `[this, sub_zero]`.

Establish `e1 : (i : ℕ) + 1 - j = N - j` using `by omega`. Rewrite using `[e1, gramLog_top]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem stepPot_top {N : ℕ} {j : ℕ} (hj : j ≤ N) (i : Fin N) (h : (i : ℕ) + 1 = N)
    (g : Matrix (Fin N) (Fin N) ℂ) : stepPot N j i g = Real.log ‖g.det‖ := by
  unfold stepPot
  split_ifs with h1
  · have e1 : N - j + ((i : ℕ) + 1) = N := by omega
    have e2 : N - j = 0 := by omega
    rw [e1, gramLog_top, e2]
    have : gramLog (sigForm N j) 0 g = 0 := by
      unfold gramLog
      haveI : IsEmpty {a : Fin N // (a : ℕ) < 0} := ⟨fun a => by have := a.2; omega⟩
      simp
    rw [this, sub_zero]
  · have e1 : (i : ℕ) + 1 - j = N - j := by omega
    rw [e1, gramLog_top]
    ring

/- English proof (translation)
Unfold `minorIJ`. Rewrite using `[dif_pos rfl, Matrix.submatrix_one _ (S.orderEmbOfFin rfl).injective, Matrix.det_one]`.
-/
theorem minorIJ_one_self {N : ℕ} (S : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) S S = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.submatrix_one _ (S.orderEmbOfFin rfl).injective, Matrix.det_one]

/- English proof (translation)
Unfold `detFac`. Simplify using `only [minorIJ_one_self]`. Simplify using the standard rewrite rules.
-/
theorem detFac_one {N : ℕ} (j : ℕ) (i : Fin N) : detFac j i (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
  unfold detFac
  simp only [minorIJ_one_self]
  simp

/- English proof (translation)
Use `(stepPot_mul_eq_blockPot N j i Pi G 1 hj hP hG hG' isBlockDiag_one (by simp)).2` as an intermediate fact. Rewrite `this` using `[mul_one, stepPot_top hj i h, detFac_one, norm_one, Real.log_one, add_zero]`. Conclude with `this.symm`.
-/
theorem blockPot_top {N j : ℕ} (hj : j ≤ N) (i : Fin N) (h : (i : ℕ) + 1 = N) {Pi G : Matrix (Fin N) (Fin N) ℂ}
    (hP : IsPeriodGram j Pi G) (hG : IsBlockDiag j G) (hG' : G.PosDef) :
    blockPot j i G 1 = Real.log ‖Pi.det‖ := by
  have := (stepPot_mul_eq_blockPot N j i Pi G 1 hj hP hG hG' isBlockDiag_one (by simp)).2
  rw [mul_one, stepPot_top hj i h, detFac_one, norm_one, Real.log_one, add_zero] at this
  exact this.symm

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `h`. Use `⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), funext fun q => ?_⟩` and prove the remaining obligations. Simplify using `only [inv_mul_cancel_left₀ (hc q.1)]`.
-/
theorem sameOrbit_symm {K : Type} {ι : K → Type} {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), funext fun q => ?_⟩
  simp only [inv_mul_cancel_left₀ (hc q.1)]

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `h`. Take `⟨d, hd, rfl⟩` from `h'`. Conclude with `⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), funext fun q => by simp only [mul_assoc]⟩`.
-/
theorem sameOrbit_trans {K : Type} {ι : K → Type} {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z')
    (h' : SameOrbit z' z'') : SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨d, hd, rfl⟩ := h'
  exact ⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), funext fun q => by simp only [mul_assoc]⟩

section Val

variable {Kb : Type} [Fintype Kb] {ιb : Kb → Type} [∀ k, Fintype (ιb k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Introduce `e` and use `hq (mem_mCoordIdeal_of_aeval_eq_zero z hh (by have : aeval z h = eval z (map (Int.castRingHom ℂ) h) := by rw [eval_map, aeval_def] exact congrArg (fun f => eval₂ f z h) (Subsingleton.elim _ _) rw [this, e]))`.
-/
theorem eval_ne_zero_of_not_mem {z : (Σ k, ιb k) → ℂ} {h : MRing ιb} {d : Kb → ℕ} (hh : IsMultiHomog h d)
    (hq : h ∉ mCoordIdeal z) : eval z (map (Int.castRingHom ℂ) h) ≠ 0 := fun e => hq
  (mem_mCoordIdeal_of_aeval_eq_zero z hh (by
    have : aeval z h = eval z (map (Int.castRingHom ℂ) h) := by
      rw [eval_map, aeval_def]
      exact congrArg (fun f => eval₂ f z h) (Subsingleton.elim _ _)
    rw [this, e]))

/- English proof (translation)
Introduce `e` and use `hne (eval_eq_zero_of_mem_mcPts hz (mem_mCoordIdeal_of_aeval_eq_zero x hh e))`.
-/
theorem aeval_ne_zero_of_eval {x : (Σ k, ιb k) → Ω} {z : (Σ k, ιb k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x))
    {h : MRing ιb} {d : Kb → ℕ} (hh : IsMultiHomog h d) (hne : eval z (map (Int.castRingHom ℂ) h) ≠ 0) :
    aeval x h ≠ 0 := fun e => hne (eval_eq_zero_of_mem_mcPts hz (mem_mCoordIdeal_of_aeval_eq_zero x hh e))

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `ho`. Establish `hp : (∏ k, c k ^ d k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)`. Use `⟨d, g, h, hg, hh, a, he, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[eval_smul_of_isMultiHomog hh]`. Conclude with `mul_ne_zero hp hne`.

Rewrite using `[eval_smul_of_isMultiHomog hg, eval_smul_of_isMultiHomog hh, mul_div_mul_left _ _ hp]`.
-/
theorem isValueAt_of_orbit {x : (Σ k, ιb k) → Ω} {s : Ω} {d : Kb → ℕ} {g h : MRing ιb} (hg : IsMultiHomog g d)
    (hh : IsMultiHomog h d) (a : aeval x h ≠ 0) (he : aeval x g = s * aeval x h) {z z' : (Σ k, ιb k) → ℂ}
    (ho : SameOrbit z z') (hne : eval z' (map (Int.castRingHom ℂ) h) ≠ 0) :
    IsValueAt x s z (eval z' (map (Int.castRingHom ℂ) g) / eval z' (map (Int.castRingHom ℂ) h)) := by
  obtain ⟨c, hc, rfl⟩ := ho
  have hp : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  refine ⟨d, g, h, hg, hh, a, he, ?_, ?_⟩
  · rw [eval_smul_of_isMultiHomog hh]
    exact mul_ne_zero hp hne
  · rw [eval_smul_of_isMultiHomog hg, eval_smul_of_isMultiHomog hh, mul_div_mul_left _ _ hp]

/- English proof (translation)
Take `⟨d, g, h, hg, hh, hQ, he⟩` from `hs`. Take `⟨d', g', h', hg', hh', hQ', he'⟩` from `hs'`. Establish `hz₀ : Rb.lift b₀ b₀ ∈ mcPts (mCoordIdeal x)` using `Rb.mem b₀ b₀ (Rb.mem_U b₀)`. Establish `n1` using `eval_ne_zero_of_not_mem hh hQ`. Establish `n2` using `eval_ne_zero_of_not_mem hh' hQ'`.

Establish `a1` using `aeval_ne_zero_of_eval hz₀ hh n1`. Establish `a2` using `aeval_ne_zero_of_eval hz₀ hh' n2`. Set `E : MRing ιb → Rb.X → ℂ` to `fun f b => eval (Rb.lift b₀ b) (map (Int.castRingHom ℂ) f)`. Establish `hE : ∀ f, Rb.A.HoloOn (Rb.U b₀) (E f)` using `holoOn_eval_lift Rb b₀`. Establish `hC : ∀ f, ContinuousOn (E f) (Rb.U b₀)` using `fun f b hb => (BlockPot.continuousAt_of_holoOn (hE f) hb).continuousWithinAt`.

Establish `hO : ∀ f, IsOpen (Rb.U b₀ ∩ E f ⁻¹' {0}ᶜ)` using `fun f => (hC f).isOpen_inter_preimage (Rb.isOpen_U b₀) isOpen_compl_singleton`. Use `⟨(Rb.U b₀ ∩ E h ⁻¹' {0}ᶜ) ∩ (Rb.U b₀ ∩ E h' ⁻¹' {0}ᶜ), fun b => E g b / E h b, (hO h).inter (hO h'), ⟨⟨Rb.mem_U b₀, n1⟩, ⟨Rb.mem_U b₀, n2⟩⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `c u hu`. Conclude with `(hE g c u ⟨hu.1, hu.2.1.1⟩).div (hE h c u ⟨hu.1, hu.2.1.1⟩) hu.2.1.2`. Introduce and unpack `b ⟨⟨hb, hb1⟩, -, hb2⟩ e`.

Establish `hm` using `Rb.mem b₀ b hb`. Establish `v1 : IsValueAt x s (Rb.lift b₀ b) (E g b / E h b)` using `isValueAt_of_orbit hg hh a1 he ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩ hb1`. Establish `v2 : IsValueAt x s⁻¹ (Rb.lift b₀ b) (E g' b / E h' b)` using `isValueAt_of_orbit hg' hh' a2 he' ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩ hb2`. Establish `v3` using `isValueAt_mul v1 v2`. Rewrite `v3` using `[mul_inv_cancel₀ hs0]`.

Establish `v4 : IsValueAt x 1 (Rb.lift b₀ b) 1` using `⟨d, h, h, hh, hh, a1, by rw [one_mul], hb1, (div_self hb1).symm⟩`. Use `isValueAt_unique hm v3 v4` as an intermediate fact. Simplify using `only at e`. Rewrite `this` using `[e, zero_mul]`. Conclude with `zero_ne_one this`.

Introduce and unpack `b ⟨⟨hb, hb1⟩, -⟩ z hz`. Establish `ho : SameOrbit z (Rb.lift b₀ b)` using `sameOrbit_trans hz (sameOrbit_symm (Rb.compat b₀ b b ⟨hb, Rb.mem_U b⟩))`. Conclude with `valAt_eq (mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal x) ho (Rb.mem b₀ b hb)) (isValueAt_of_orbit hg hh a1 he ho hb1)`.
-/
theorem val_local {n : ℕ} {x : (Σ k, ιb k) → Ω} (Rb : AnLogRes (mCoordIdeal x) ⊤ n) (b₀ : Rb.X) {s : Ω}
    (hs0 : s ≠ 0) (hs : RegAt x (mCoordIdeal (Rb.lift b₀ b₀)) s)
    (hs' : RegAt x (mCoordIdeal (Rb.lift b₀ b₀)) s⁻¹) :
    ∃ (V : Set Rb.X) (f : Rb.X → ℂ), IsOpen V ∧ b₀ ∈ V ∧ Rb.A.HoloOn V f ∧ (∀ b ∈ V, f b ≠ 0) ∧
      ∀ b ∈ V, ∀ z, SameOrbit z (Rb.lift b b) → valAt x s z = f b := by
  obtain ⟨d, g, h, hg, hh, hQ, he⟩ := hs
  obtain ⟨d', g', h', hg', hh', hQ', he'⟩ := hs'
  have hz₀ : Rb.lift b₀ b₀ ∈ mcPts (mCoordIdeal x) := Rb.mem b₀ b₀ (Rb.mem_U b₀)
  have n1 := eval_ne_zero_of_not_mem hh hQ
  have n2 := eval_ne_zero_of_not_mem hh' hQ'
  have a1 := aeval_ne_zero_of_eval hz₀ hh n1
  have a2 := aeval_ne_zero_of_eval hz₀ hh' n2
  let E : MRing ιb → Rb.X → ℂ := fun f b => eval (Rb.lift b₀ b) (map (Int.castRingHom ℂ) f)
  have hE : ∀ f, Rb.A.HoloOn (Rb.U b₀) (E f) := holoOn_eval_lift Rb b₀
  have hC : ∀ f, ContinuousOn (E f) (Rb.U b₀) := fun f b hb =>
    (BlockPot.continuousAt_of_holoOn (hE f) hb).continuousWithinAt
  have hO : ∀ f, IsOpen (Rb.U b₀ ∩ E f ⁻¹' {0}ᶜ) := fun f =>
    (hC f).isOpen_inter_preimage (Rb.isOpen_U b₀) isOpen_compl_singleton
  refine ⟨(Rb.U b₀ ∩ E h ⁻¹' {0}ᶜ) ∩ (Rb.U b₀ ∩ E h' ⁻¹' {0}ᶜ), fun b => E g b / E h b, (hO h).inter (hO h'),
    ⟨⟨Rb.mem_U b₀, n1⟩, ⟨Rb.mem_U b₀, n2⟩⟩, ?_, ?_, ?_⟩
  · intro c u hu
    exact (hE g c u ⟨hu.1, hu.2.1.1⟩).div (hE h c u ⟨hu.1, hu.2.1.1⟩) hu.2.1.2
  · rintro b ⟨⟨hb, hb1⟩, -, hb2⟩ e
    have hm := Rb.mem b₀ b hb
    have v1 : IsValueAt x s (Rb.lift b₀ b) (E g b / E h b) :=
      isValueAt_of_orbit hg hh a1 he ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩ hb1
    have v2 : IsValueAt x s⁻¹ (Rb.lift b₀ b) (E g' b / E h' b) :=
      isValueAt_of_orbit hg' hh' a2 he' ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩ hb2
    have v3 := isValueAt_mul v1 v2
    rw [mul_inv_cancel₀ hs0] at v3
    have v4 : IsValueAt x 1 (Rb.lift b₀ b) 1 :=
      ⟨d, h, h, hh, hh, a1, by rw [one_mul], hb1, (div_self hb1).symm⟩
    have := isValueAt_unique hm v3 v4
    simp only at e
    rw [e, zero_mul] at this
    exact zero_ne_one this
  · rintro b ⟨⟨hb, hb1⟩, -⟩ z hz
    have ho : SameOrbit z (Rb.lift b₀ b) :=
      sameOrbit_trans hz (sameOrbit_symm (Rb.compat b₀ b b ⟨hb, Rb.mem_U b⟩))
    exact valAt_eq (mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal x) ho (Rb.mem b₀ b hb))
      (isValueAt_of_orbit hg hh a1 he ho hb1)

end Val

/- English proof (translation)
Establish `hc : ContinuousOn (s b₀) (L.U b₀)` using `fun b hb => (BlockPot.continuousAt_of_holoOn (hsec.1 b₀) hb).continuousWithinAt`. Use `⟨_, hc.isOpen_inter_preimage (L.isOpen_U b₀) isOpen_compl_singleton, ⟨L.mem_U b₀, h⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `b ⟨hb, hb'⟩ (e : s b b = 0)`. Establish `h1` using `hsec.2 b₀ b b ⟨hb, L.mem_U b⟩`. Rewrite `h1` using `[e, norm_zero, zero_mul]`.

Conclude with `hb' (norm_eq_zero.1 ((mul_eq_zero.1 h1).resolve_right (Real.exp_pos _).ne'))`.
-/
theorem exists_nhd_off_bdry {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {L : LocPot X}
    {s : X → X → ℂ} (hsec : IsSection A L s) {b₀ : X} (h : b₀ ∉ bdry s) :
    ∃ V : Set X, IsOpen V ∧ b₀ ∈ V ∧ V ⊆ (bdry s)ᶜ := by
  have hc : ContinuousOn (s b₀) (L.U b₀) := fun b hb =>
    (BlockPot.continuousAt_of_holoOn (hsec.1 b₀) hb).continuousWithinAt
  refine ⟨_, hc.isOpen_inter_preimage (L.isOpen_U b₀) isOpen_compl_singleton, ⟨L.mem_U b₀, h⟩, ?_⟩
  rintro b ⟨hb, hb'⟩ (e : s b b = 0)
  have h1 := hsec.2 b₀ b b ⟨hb, L.mem_U b⟩
  rw [e, norm_zero, zero_mul] at h1
  exact hb' (norm_eq_zero.1 ((mul_eq_zero.1 h1).resolve_right (Real.exp_pos _).ne'))

/- English proof (translation)
Introduce `c u hu`. Establish `e1 : ((fun x => (P x).det) ∘ (A.chart c).symm) = fun t => ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, P ((A.chart c).symm t) (σ i) i`. Use function extensionality and compare the values at `t`. Simplify using `only [Function.comp_apply, Matrix.det_apply', Int.cast_inj]`. Rewrite using `[e1]`.

Use `Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul ?_` and prove the remaining obligations. Conclude with `Finset.analyticAt_fun_prod _ fun i _ => h (σ i) i c u hu`.
-/
theorem holoOn_det {e N : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {V : Set X}
    {P : X → Matrix (Fin N) (Fin N) ℂ} (h : ∀ a b, A.HoloOn V fun x => P x a b) :
    A.HoloOn V fun x => (P x).det := by
  intro c u hu
  have e1 : ((fun x => (P x).det) ∘ (A.chart c).symm) = fun t =>
      ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, P ((A.chart c).symm t) (σ i) i := by
    funext t
    simp only [Function.comp_apply, Matrix.det_apply', Int.cast_inj]
  rw [e1]
  refine Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul ?_
  exact Finset.analyticAt_fun_prod _ fun i _ => h (σ i) i c u hu

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ}

/- English proof (translation)
Take `⟨l, hl⟩` from `BM.O_cover b₀`. Establish `hbl : b₀ ∈ BM.O l \ bdry BM.s` using `⟨hl, hb₀⟩`. Establish `hnone` using `blk_none_of_top M hN`. Take `⟨h0, h1, h2⟩` from `(BM.good l b₀ hl).2.2 p hnone`. Take `⟨V₁, f₁, o₁, m₁, H₁, n₁, e₁⟩` from `val_local BM.Rb b₀ h0 h1 h2`.

Take `⟨V₂, Pi, m₂, o₂, H₂, P₂⟩` from `BM.period l b₀ hbl`. Take `⟨V₃, o₃, m₃, s₃⟩` from `exists_nhd_off_bdry BM.sec hb₀`. Establish `hsub : V₁ ∩ V₂ ∩ V₃ ∩ BM.O l ⊆ BM.O l \ bdry BM.s` using `fun b hb => ⟨hb.2, s₃ hb.1.2⟩`. Establish `hdet` using `holoOn_det (H₂ p.1)`. Use `⟨l, V₁ ∩ V₂ ∩ V₃ ∩ BM.O l, fun b => (Pi p.1 b).det / f₁ b, ((o₁.inter o₂).inter o₃).inter (BM.O_open l), ⟨⟨⟨m₁, m₂⟩, m₃⟩, hl⟩, hsub, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `c u hu`. Establish `hu₁ : (BM.Rb.A.chart c).symm u ∈ V₁` using `hu.2.1.1.1`. Establish `hu₂ : (BM.Rb.A.chart c).symm u ∈ V₂` using `hu.2.1.1.2`. Conclude with `(hdet c u ⟨hu.1, hu₂⟩).div (H₁ c u ⟨hu.1, hu₁⟩) (n₁ _ hu₁)`. Introduce `b hb`.

Conclude with `div_ne_zero (P₂ p.1 b hb.1.1.2).1.1.ne_zero (n₁ b hb.1.1.1)`. Introduce `b hb z hz`. Establish `hbG` using `BM.G_pos l p.1 b (hsub hb)`. Rewrite using `[blockPot_top M.j_le p.2 hN (P₂ p.1 b hb.1.1.2) hbG.1 hbG.2, e₁ b hb.1.1.1 z hz, norm_div, Real.log_div (norm_ne_zero_iff.2 (P₂ p.1 b hb.1.1.2).1.1.ne_zero) (norm_ne_zero_iff.2 (n₁ b hb.1.1.1))]`.
-/
theorem base_flat {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) {p : Ψ × Fin N} (hN : (p.2 : ℕ) + 1 = N)
    {b₀ : BM.Rb.X} (hb₀ : b₀ ∉ bdry BM.s) :
    ∃ (l : Fin BM.q) (V : Set BM.Rb.X) (f : BM.Rb.X → ℂ), IsOpen V ∧ b₀ ∈ V ∧ V ⊆ BM.O l \ bdry BM.s ∧
      BM.Rb.A.HoloOn V f ∧ (∀ b ∈ V, f b ≠ 0) ∧ ∀ b ∈ V, ∀ z, SameOrbit z (BM.Rb.lift b b) →
        blockPot j p.2 (BM.G l p.1 b) 1 - Real.log ‖valAt M.x ((BM.F l).υ p) z‖ = Real.log ‖f b‖ := by
  obtain ⟨l, hl⟩ := BM.O_cover b₀
  have hbl : b₀ ∈ BM.O l \ bdry BM.s := ⟨hl, hb₀⟩
  have hnone := blk_none_of_top M hN
  obtain ⟨h0, h1, h2⟩ := (BM.good l b₀ hl).2.2 p hnone
  obtain ⟨V₁, f₁, o₁, m₁, H₁, n₁, e₁⟩ := val_local BM.Rb b₀ h0 h1 h2
  obtain ⟨V₂, Pi, m₂, o₂, H₂, P₂⟩ := BM.period l b₀ hbl
  obtain ⟨V₃, o₃, m₃, s₃⟩ := exists_nhd_off_bdry BM.sec hb₀
  have hsub : V₁ ∩ V₂ ∩ V₃ ∩ BM.O l ⊆ BM.O l \ bdry BM.s := fun b hb => ⟨hb.2, s₃ hb.1.2⟩
  have hdet := holoOn_det (H₂ p.1)
  refine ⟨l, V₁ ∩ V₂ ∩ V₃ ∩ BM.O l, fun b => (Pi p.1 b).det / f₁ b, ((o₁.inter o₂).inter o₃).inter (BM.O_open l),
    ⟨⟨⟨m₁, m₂⟩, m₃⟩, hl⟩, hsub, ?_, ?_, ?_⟩
  · intro c u hu
    have hu₁ : (BM.Rb.A.chart c).symm u ∈ V₁ := hu.2.1.1.1
    have hu₂ : (BM.Rb.A.chart c).symm u ∈ V₂ := hu.2.1.1.2
    exact (hdet c u ⟨hu.1, hu₂⟩).div (H₁ c u ⟨hu.1, hu₁⟩) (n₁ _ hu₁)
  · intro b hb
    exact div_ne_zero (P₂ p.1 b hb.1.1.2).1.1.ne_zero (n₁ b hb.1.1.1)
  · intro b hb z hz
    have hbG := BM.G_pos l p.1 b (hsub hb)
    rw [blockPot_top M.j_le p.2 hN (P₂ p.1 b hb.1.1.2) hbG.1 hbG.2, e₁ b hb.1.1.1 z hz, norm_div,
      Real.log_div (norm_ne_zero_iff.2 (P₂ p.1 b hb.1.1.2).1.1.ne_zero) (norm_ne_zero_iff.2 (n₁ b hb.1.1.1))]

def cz (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι k) → ℂ) (k : K) : ℂ :=
  if h : ∀ p', M.blk p' ≠ some k then z ⟨k, F.c ⟨k, h⟩⟩ else 1

/- English proof (translation)
Take `⟨t, ht, e⟩` from `ho`. Establish `h1 : BM.Rb.lift b b ⟨k, (BM.F l).c k⟩ ≠ 0` using `fun h => (BM.good l b hb).1 k (by show mConeMap _ (X ⟨k, (BM.F l).c k⟩) = 0`. Rewrite using `[mConeMap, aeval_X, h, map_zero, zero_mul])`. Establish `h2` using `congrFun e ⟨k, (BM.F l).c k⟩`. Simplify using `only [basePart] at h2`.

Rewrite using `[h2]`. Conclude with `mul_ne_zero (ht k) h1`.
-/
theorem coord_ne {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) {l : Fin BM.q} {b : BM.Rb.X}
    (hb : b ∈ BM.O l) {z : (Σ k, ι k) → ℂ} (ho : SameOrbit (basePart M.blk z) (BM.Rb.lift b b))
    (k : NonPluckerBlocks M.blk) : z ⟨k.1, (BM.F l).c k⟩ ≠ 0 := by
  obtain ⟨t, ht, e⟩ := ho
  have h1 : BM.Rb.lift b b ⟨k, (BM.F l).c k⟩ ≠ 0 := fun h => (BM.good l b hb).1 k (by
    show mConeMap _ (X ⟨k, (BM.F l).c k⟩) = 0
    rw [mConeMap, aeval_X, h, map_zero, zero_mul])
  have h2 := congrFun e ⟨k, (BM.F l).c k⟩
  simp only [basePart] at h2
  rw [h2]
  exact mul_ne_zero (ht k) h1

/- English proof (translation)
Establish `hc : ∀ k, cz M (BM.F l) z k ≠ 0`. Introduce `k`. Unfold `cz`. Use `split_ifs with h`. Conclude with `coord_ne BM hb.1 ho ⟨k, h⟩`.

Conclude with `one_ne_zero`. Use `set t : K → ℂ := fun k => (cz M (BM.F l) z k)⁻¹ with ht`. Establish `ht0 : ∀ k, t k ≠ 0` using `fun k => inv_ne_zero (hc k)`. Use `set z' : (Σ k, ι k) → ℂ := fun q => t q.1 * z q with hz'`. Establish `hm : z' ∈ mcPts (mCoordIdeal y)` using `mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal y) ⟨t, ht0, rfl⟩ hz`.

Establish `ho' : SameOrbit (basePart M.blk z') (BM.Rb.lift b b)`. Use `sameOrbit_trans ⟨fun k => t k.1, fun k => ht0 _, rfl⟩ ho` and prove the remaining obligations. Establish `hone : ∀ k, basePart M.blk z' ⟨k, (BM.F l).c k⟩ = 1`. Introduce `k`. Establish `e : cz M (BM.F l) z k.1 = z ⟨k.1, (BM.F l).c k⟩` using `dif_pos k.2`.

Use `show t k.1 * z ⟨k.1, (BM.F l).c k⟩ = 1`. Rewrite using `[ht]`. Simplify using `only`. Rewrite using `[e]`. Conclude with `inv_mul_cancel₀ (coord_ne BM hb.1 ho k)`.

Establish `h1` using `(BM.induced l b hb p z' hm ho' hone 1 isBlockDiag_one (by simp)).2 (blk_none_of_top M hN)`. Establish `h2` using `(BM.hom p).smul t z ht0`. Establish `hpos` using `(BM.hom p).pos z hz.1`. Use `⟨_, ho', ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`.

Establish `h3 : Real.log ((BM.hom p).h z') = ∑ k, (M.dy p k : ℝ) * Real.log ‖t k‖ + Real.log ((BM.hom p).h z)` using `by show Real.log ((BM.hom p).h fun q => t q.1 * z q) = _`. Rewrite using `[h2, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (ht0 k))) hpos.ne', Real.log_prod fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (ht0 k))]`. Simplify using `only [Real.log_zpow, BM.hom_deg]`. Establish `h4 : ∑ k, (M.dy p k : ℝ) * Real.log ‖t k‖ = - ∑ k, (M.dy p k : ℝ) * Real.log ‖cz M (BM.F l) z k‖`. Rewrite using `[← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [ht, norm_inv, Real.log_inv]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[h3, h4]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_hom_eq {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) {p : Ψ × Fin N} (hN : (p.2 : ℕ) + 1 = N)
    {l : Fin BM.q} {b : BM.Rb.X} (hb : b ∈ BM.O l \ bdry BM.s) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) (ho : SameOrbit (basePart M.blk z) (BM.Rb.lift b b)) :
    ∃ zb, SameOrbit zb (BM.Rb.lift b b) ∧ Real.log ((BM.hom p).h z) =
      ∑ k, (M.dy p k : ℝ) * Real.log ‖cz M (BM.F l) z k‖ + blockPot j p.2 (BM.G l p.1 b) 1 -
        Real.log ‖valAt M.x ((BM.F l).υ p) zb‖ := by
  have hc : ∀ k, cz M (BM.F l) z k ≠ 0 := by
    intro k
    unfold cz
    split_ifs with h
    · exact coord_ne BM hb.1 ho ⟨k, h⟩
    · exact one_ne_zero
  set t : K → ℂ := fun k => (cz M (BM.F l) z k)⁻¹ with ht
  have ht0 : ∀ k, t k ≠ 0 := fun k => inv_ne_zero (hc k)
  set z' : (Σ k, ι k) → ℂ := fun q => t q.1 * z q with hz'
  have hm : z' ∈ mcPts (mCoordIdeal y) :=
    mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal y) ⟨t, ht0, rfl⟩ hz
  have ho' : SameOrbit (basePart M.blk z') (BM.Rb.lift b b) := by
    refine sameOrbit_trans ⟨fun k => t k.1, fun k => ht0 _, rfl⟩ ho
  have hone : ∀ k, basePart M.blk z' ⟨k, (BM.F l).c k⟩ = 1 := by
    intro k
    have e : cz M (BM.F l) z k.1 = z ⟨k.1, (BM.F l).c k⟩ := dif_pos k.2
    show t k.1 * z ⟨k.1, (BM.F l).c k⟩ = 1
    rw [ht]
    simp only
    rw [e]
    exact inv_mul_cancel₀ (coord_ne BM hb.1 ho k)
  have h1 := (BM.induced l b hb p z' hm ho' hone 1 isBlockDiag_one (by simp)).2 (blk_none_of_top M hN)
  have h2 := (BM.hom p).smul t z ht0
  have hpos := (BM.hom p).pos z hz.1
  refine ⟨_, ho', ?_⟩
  rw [← sub_eq_zero]
  have h3 : Real.log ((BM.hom p).h z') = ∑ k, (M.dy p k : ℝ) * Real.log ‖t k‖ + Real.log ((BM.hom p).h z) := by
    show Real.log ((BM.hom p).h fun q => t q.1 * z q) = _
    rw [h2, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (ht0 k))) hpos.ne',
      Real.log_prod fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (ht0 k))]
    simp only [Real.log_zpow, BM.hom_deg]
  have h4 : ∑ k, (M.dy p k : ℝ) * Real.log ‖t k‖ = - ∑ k, (M.dy p k : ℝ) * Real.log ‖cz M (BM.F l) z k‖ := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [ht, norm_inv, Real.log_inv]
    ring
  rw [h3, h4] at h1
  linarith

/- English proof (translation)
Take `⟨z, hz, hzv, ho⟩` from `H1 t`. Take `⟨c, hc, ec⟩` from `R.compat x₀ t t ⟨ht, R.mem_U t⟩`. Use `set ct : K → ℂ := Function.extend κ c 1 with hct`. Establish `hκ : ∀ k, ct (κ k) = c k` using `fun k => hb.1.extend_apply _ _ _`. Establish `hct0 : ∀ k, ct k ≠ 0`.

Introduce `k`. Distinguish the cases in `hk : ∃ k', κ k' = k`. Take `⟨k', rfl⟩` from `hk`. Rewrite using `[hκ]`. Conclude with `hc k'`.

Rewrite using `[hct, Function.extend_apply' _ _ _ hk]`. Conclude with `one_ne_zero`. Establish `hm : (fun q => ct q.1 * z q) ∈ mcPts (mCoordIdeal y)` using `mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal y) ⟨ct, hct0, rfl⟩ hz`. Establish `hv : (fun q => ct q.1 * z q) ∘ v = R.lift x₀ t`. Use function extensionality and compare the values at `q`.

Establish `e1` using `congrFun ec q`. Establish `e2` using `congrFun hzv q`. Simplify using `only [Function.comp_apply] at e2 ⊢`. Rewrite using `[e1, hb.2.2.1 q, hκ, e2]`. Establish `ha : ∀ k, k ∉ Set.range κ → M.dy p k = 0` using `fun k hk => dy_eq_zero M hN fun h => hk (hr k h)`.

Use `⟨fun q => ct q.1 * z q, hm, hv, sameOrbit_trans ⟨fun k => ct k.1, fun k => hct0 _, rfl⟩ ho, ?_⟩` and prove the remaining obligations. Establish `e1 : refNorm (fun k => M.dy p (κ k)) (R.lift x₀ t) = refNorm (M.dy p) fun q => ct q.1 * z q`. Rewrite using `[← hv]`. Conclude with `(BlockPot.refNorm_block hb ha _).symm`. Establish `e2 : refNorm (M.dy p) (fun q => ct q.1 * z q) = (∏ k, ‖ct k‖ ^ M.dy p k) * refNorm (M.dy p) z` using `refNorm_smul _ ct z`.

Establish `e3` using `(BM.hom p).smul ct z hct0`. Rewrite `e3` using `[BM.hom_deg]`. Establish `hP : (∏ k, ‖ct k‖ ^ M.dy p k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hct0 k))`. Rewrite using `[e1, e2, e3, Real.log_mul hP (refNorm_pos _ hz.1).ne', Real.log_mul hP ((BM.hom p).pos z hz.1).ne', H2 t hbd z hz hzv, fsHerm_h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem torus_move {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) {p : Ψ × Fin N} (hN : (p.2 : ℕ) + 1 = N)
    {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)] {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)}
    (hb : IsBlockMap κ v) (hr : ∀ k, (∀ p', M.blk p' ≠ some k) → k ∈ Set.range κ) {e : ℕ}
    (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (ph : R.X → ℝ)
    (H1 : ∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧
      SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x)))
    (H2 : ∀ x, pr x ∉ bdry BM.s → ∀ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x →
      Real.log ((BM.hom p).h z) = Real.log ((fsHerm ι (M.dy p)).h z) + ph x)
    {x₀ t : R.X} (ht : t ∈ R.U x₀) (hbd : pr t ∉ bdry BM.s) :
    ∃ z₁ ∈ mcPts (mCoordIdeal y), z₁ ∘ v = R.lift x₀ t ∧ SameOrbit (basePart M.blk z₁) (BM.Rb.lift (pr t) (pr t)) ∧
      Real.log (refNorm (fun k => M.dy p (κ k)) (R.lift x₀ t)) + ph t = Real.log ((BM.hom p).h z₁) := by
  obtain ⟨z, hz, hzv, ho⟩ := H1 t
  obtain ⟨c, hc, ec⟩ := R.compat x₀ t t ⟨ht, R.mem_U t⟩
  set ct : K → ℂ := Function.extend κ c 1 with hct
  have hκ : ∀ k, ct (κ k) = c k := fun k => hb.1.extend_apply _ _ _
  have hct0 : ∀ k, ct k ≠ 0 := by
    intro k
    by_cases hk : ∃ k', κ k' = k
    · obtain ⟨k', rfl⟩ := hk
      rw [hκ]
      exact hc k'
    · rw [hct, Function.extend_apply' _ _ _ hk]
      exact one_ne_zero
  have hm : (fun q => ct q.1 * z q) ∈ mcPts (mCoordIdeal y) :=
    mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal y) ⟨ct, hct0, rfl⟩ hz
  have hv : (fun q => ct q.1 * z q) ∘ v = R.lift x₀ t := by
    funext q
    have e1 := congrFun ec q
    have e2 := congrFun hzv q
    simp only [Function.comp_apply] at e2 ⊢
    rw [e1, hb.2.2.1 q, hκ, e2]
  have ha : ∀ k, k ∉ Set.range κ → M.dy p k = 0 := fun k hk => dy_eq_zero M hN fun h => hk (hr k h)
  refine ⟨fun q => ct q.1 * z q, hm, hv, sameOrbit_trans ⟨fun k => ct k.1, fun k => hct0 _, rfl⟩ ho, ?_⟩
  have e1 : refNorm (fun k => M.dy p (κ k)) (R.lift x₀ t) = refNorm (M.dy p) fun q => ct q.1 * z q := by
    rw [← hv]
    exact (BlockPot.refNorm_block hb ha _).symm
  have e2 : refNorm (M.dy p) (fun q => ct q.1 * z q) = (∏ k, ‖ct k‖ ^ M.dy p k) * refNorm (M.dy p) z :=
    refNorm_smul _ ct z
  have e3 := (BM.hom p).smul ct z hct0
  rw [BM.hom_deg] at e3
  have hP : (∏ k, ‖ct k‖ ^ M.dy p k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hct0 k))
  rw [e1, e2, e3, Real.log_mul hP (refNorm_pos _ hz.1).ne', Real.log_mul hP ((BM.hom p).pos z hz.1).ne',
    H2 t hbd z hz hzv, fsHerm_h]
  ring

end Flag

section Main

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ}

/- English proof (translation)
Take `⟨l, V, f, oV, mV, sV, HV, nV, eV⟩` from `base_flat BM hN hbd`. Establish `hw : ∀ k : NonPluckerBlocks M.blk, ∃ q, v q = ⟨k.1, (BM.F l).c k⟩` using `fun k => hb.2.2.2 _ (hr k.1 k.2)`. Use `choose w hw using hw`. Establish `hE : ∀ k, R.A.HoloOn (R.U x₀) fun t => R.lift x₀ t (w k)` using `fun k => R.holo x₀ (w k)`. Establish `hO : ∀ k, IsOpen (R.U x₀ ∩ (fun t => R.lift x₀ t (w k)) ⁻¹' {0}ᶜ)` using `fun k => ContinuousOn.isOpen_inter_preimage (fun t ht => (BlockPot.continuousAt_of_holoOn (hE k) ht).continuousWithinAt) (R.isOpen_U x₀) isOpen_compl_singleton`.

Use `set W₀ : Set R.X := R.U x₀ ∩ pr ⁻¹' V with hW₀`. Use `set W : Set R.X := W₀ ∩ ⋂ k, (R.U x₀ ∩ (fun t => R.lift x₀ t (w k)) ⁻¹' {0}ᶜ) with hW`. Establish `oW : IsOpen W` using `((R.isOpen_U x₀).inter (oV.preimage hp.1)).inter (isOpen_iInter_of_finite hO)`. Establish `hbase : ∀ t ∈ W, ∃ z₁ ∈ mcPts (mCoordIdeal y), z₁ ∘ v = R.lift x₀ t ∧ SameOrbit (basePart M.blk z₁) (BM.Rb.lift (pr t) (pr t)) ∧ Real.log (refNorm (fun k => M.dy p (κ k)) (R.lift x₀ t)) + ph t = Real.log ((BM.hom p).h z₁)` using `fun t ht => torus_move BM hN hb hr R pr ph H1 H2 ht.1.1 (sV ht.1.2).2`. Set `ℓ : K → R.X → ℂ` to `fun k t => if h : ∀ p', M.blk p' ≠ some k then R.lift x₀ t (w ⟨k, h⟩) else 1`.

Establish `hℓ0 : ∀ t ∈ W, ∀ k, ℓ k t ≠ 0`. Introduce `t ht k`. Simplify using `only [ℓ]`. Use `split_ifs with h`. Conclude with `(Set.mem_iInter.1 ht.2 ⟨k, h⟩).2`.

Conclude with `one_ne_zero`. Establish `hℓH : ∀ k, R.A.HoloOn W (ℓ k)`. Introduce `k c u hu`. Distinguish the cases in `h : ∀ p', M.blk p' ≠ some k`. Establish `e : ℓ k ∘ (R.A.chart c).symm = (fun t => R.lift x₀ t (w ⟨k, h⟩)) ∘ (R.A.chart c).symm`.

Use function extensionality and compare the values at `t`. Simplify using `only [ℓ, Function.comp_apply, dif_pos h]`. Rewrite using `[e]`. Conclude with `hE ⟨k, h⟩ c u ⟨hu.1, hu.2.1.1⟩`. Establish `e : ℓ k ∘ (R.A.chart c).symm = fun _ => 1`.

Use function extensionality and compare the values at `t`. Simplify using `only [ℓ, Function.comp_apply, dif_neg h]`. Rewrite using `[e]`. Conclude with `analyticAt_const`. Establish `hfH : R.A.HoloOn W fun t => f (pr t)` using `fun c u hu => BlockPot.holoOn_comp hp HV c u ⟨hu.1, hu.2.1.2⟩`.

Establish `hcz : ∀ z₁, ∀ t, z₁ ∘ v = R.lift x₀ t → ∀ k, cz M (BM.F l) z₁ k = ℓ k t`. Introduce `z₁ t hz k`. Simplify using `only [cz, ℓ]`. Use `split_ifs with h`. Rewrite using `[← hz, Function.comp_apply, hw]`.

Both sides reduce to the same expression. Establish `mW : t₀ ∈ W`. Use `⟨⟨ht₀, mV⟩, Set.mem_iInter.2 fun k => ⟨ht₀, ?_⟩⟩` and prove the remaining obligations. Take `⟨z₁, -, hz, ho, -⟩` from `torus_move BM hN hb hr R pr ph H1 H2 ht₀ hbd`. Use `coord_ne BM (sV mV).1 ho k` as an intermediate fact.

Simplify using `only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]`. Rewrite using `[← hz, Function.comp_apply, hw]`. Conclude with `this`. Use `⟨W, fun t => (∏ k, ℓ k t ^ M.dy p k) * f (pr t), oW, mW, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `c u hu`.

Use `AnalyticAt.mul (Finset.analyticAt_fun_prod _ fun k _ => ?_) (hfH c u hu)` and prove the remaining obligations. Conclude with `(hℓH k c u hu).zpow (hℓ0 _ hu.2 k)`. Introduce `t ht`. Conclude with `mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hℓ0 t ht k)) (nV _ ht.1.2)`. Introduce `t ht`.

Take `⟨z₁, hz₁, hv, ho, he⟩` from `hbase t ht`. Take `⟨zb, hzb, hf⟩` from `log_hom_eq BM hN (sV ht.1.2) hz₁ ho`. Establish `hb'` using `eV _ ht.1.2 zb hzb`. Rewrite using `[he, hf, norm_mul, norm_prod, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => norm_ne_zero_iff.2 (zpow_ne_zero _ (hℓ0 t ht k))) (norm_ne_zero_iff.2 (nV _ ht.1.2)), Real.log_prod fun k _ => norm_ne_zero_iff.2 (zpow_ne_zero _ (hℓ0 t ht k)), ← hb']`. Simplify using `only [norm_zpow, Real.log_zpow, hcz z₁ t hv]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem local_log_norm {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) {p : Ψ × Fin N}
    (hN : (p.2 : ℕ) + 1 = N) {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)] {κ : Kk → K}
    {v : (Σ k, ιk k) → (Σ k, ι k)} (hb : IsBlockMap κ v) (hr : ∀ k, (∀ p', M.blk p' ≠ some k) → k ∈ Set.range κ)
    {e : ℕ} (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr)
    (ph : R.X → ℝ)
    (H1 : ∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧
      SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x)))
    (H2 : ∀ x, pr x ∉ bdry BM.s → ∀ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x →
      Real.log ((BM.hom p).h z) = Real.log ((fsHerm ι (M.dy p)).h z) + ph x)
    {x₀ t₀ : R.X} (ht₀ : t₀ ∈ R.U x₀) (hbd : pr t₀ ∉ bdry BM.s) :
    ∃ (W : Set R.X) (H : R.X → ℂ), IsOpen W ∧ t₀ ∈ W ∧ R.A.HoloOn W H ∧ (∀ t ∈ W, H t ≠ 0) ∧
      ∀ t ∈ W, Real.log (refNorm (fun k => M.dy p (κ k)) (R.lift x₀ t)) + ph t = Real.log ‖H t‖ := by
  obtain ⟨l, V, f, oV, mV, sV, HV, nV, eV⟩ := base_flat BM hN hbd

  have hw : ∀ k : NonPluckerBlocks M.blk, ∃ q, v q = ⟨k.1, (BM.F l).c k⟩ := fun k => hb.2.2.2 _ (hr k.1 k.2)
  choose w hw using hw
  have hE : ∀ k, R.A.HoloOn (R.U x₀) fun t => R.lift x₀ t (w k) := fun k => R.holo x₀ (w k)
  have hO : ∀ k, IsOpen (R.U x₀ ∩ (fun t => R.lift x₀ t (w k)) ⁻¹' {0}ᶜ) := fun k =>
    ContinuousOn.isOpen_inter_preimage (fun t ht => (BlockPot.continuousAt_of_holoOn (hE k) ht).continuousWithinAt)
      (R.isOpen_U x₀) isOpen_compl_singleton
  set W₀ : Set R.X := R.U x₀ ∩ pr ⁻¹' V with hW₀
  set W : Set R.X := W₀ ∩ ⋂ k, (R.U x₀ ∩ (fun t => R.lift x₀ t (w k)) ⁻¹' {0}ᶜ) with hW
  have oW : IsOpen W := ((R.isOpen_U x₀).inter (oV.preimage hp.1)).inter (isOpen_iInter_of_finite hO)
  have hbase : ∀ t ∈ W, ∃ z₁ ∈ mcPts (mCoordIdeal y), z₁ ∘ v = R.lift x₀ t ∧
      SameOrbit (basePart M.blk z₁) (BM.Rb.lift (pr t) (pr t)) ∧
      Real.log (refNorm (fun k => M.dy p (κ k)) (R.lift x₀ t)) + ph t = Real.log ((BM.hom p).h z₁) :=
    fun t ht => torus_move BM hN hb hr R pr ph H1 H2 ht.1.1 (sV ht.1.2).2
  let ℓ : K → R.X → ℂ := fun k t => if h : ∀ p', M.blk p' ≠ some k then R.lift x₀ t (w ⟨k, h⟩) else 1
  have hℓ0 : ∀ t ∈ W, ∀ k, ℓ k t ≠ 0 := by
    intro t ht k
    simp only [ℓ]
    split_ifs with h
    · exact (Set.mem_iInter.1 ht.2 ⟨k, h⟩).2
    · exact one_ne_zero
  have hℓH : ∀ k, R.A.HoloOn W (ℓ k) := by
    intro k c u hu
    by_cases h : ∀ p', M.blk p' ≠ some k
    · have e : ℓ k ∘ (R.A.chart c).symm = (fun t => R.lift x₀ t (w ⟨k, h⟩)) ∘ (R.A.chart c).symm := by
        funext t
        simp only [ℓ, Function.comp_apply, dif_pos h]
      rw [e]
      exact hE ⟨k, h⟩ c u ⟨hu.1, hu.2.1.1⟩
    · have e : ℓ k ∘ (R.A.chart c).symm = fun _ => 1 := by
        funext t
        simp only [ℓ, Function.comp_apply, dif_neg h]
      rw [e]
      exact analyticAt_const
  have hfH : R.A.HoloOn W fun t => f (pr t) :=
    fun c u hu => BlockPot.holoOn_comp hp HV c u ⟨hu.1, hu.2.1.2⟩
  have hcz : ∀ z₁, ∀ t, z₁ ∘ v = R.lift x₀ t → ∀ k, cz M (BM.F l) z₁ k = ℓ k t := by
    intro z₁ t hz k
    simp only [cz, ℓ]
    split_ifs with h
    · rw [← hz, Function.comp_apply, hw]
    · rfl
  have mW : t₀ ∈ W := by
    refine ⟨⟨ht₀, mV⟩, Set.mem_iInter.2 fun k => ⟨ht₀, ?_⟩⟩
    obtain ⟨z₁, -, hz, ho, -⟩ := torus_move BM hN hb hr R pr ph H1 H2 ht₀ hbd
    have := coord_ne BM (sV mV).1 ho k
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [← hz, Function.comp_apply, hw]
    exact this
  refine ⟨W, fun t => (∏ k, ℓ k t ^ M.dy p k) * f (pr t), oW, mW, ?_, ?_, ?_⟩
  · intro c u hu
    refine AnalyticAt.mul (Finset.analyticAt_fun_prod _ fun k _ => ?_) (hfH c u hu)
    exact (hℓH k c u hu).zpow (hℓ0 _ hu.2 k)
  · intro t ht
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hℓ0 t ht k)) (nV _ ht.1.2)
  · intro t ht
    obtain ⟨z₁, hz₁, hv, ho, he⟩ := hbase t ht
    obtain ⟨zb, hzb, hf⟩ := log_hom_eq BM hN (sV ht.1.2) hz₁ ho
    have hb' := eV _ ht.1.2 zb hzb
    rw [he, hf, norm_mul, norm_prod,
      Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => norm_ne_zero_iff.2 (zpow_ne_zero _ (hℓ0 t ht k)))
        (norm_ne_zero_iff.2 (nV _ ht.1.2)),
      Real.log_prod fun k _ => norm_ne_zero_iff.2 (zpow_ne_zero _ (hℓ0 t ht k)), ← hb']
    simp only [norm_zpow, Real.log_zpow, hcz z₁ t hv]
    ring

end Main

/- English proof (translation)
Introduce `K _ ι _ Φ _ y Ψ _ _ N j M n BM p hN Kk _ ιk _ κ v hb hr e R pr hp ph H1 H2`. Establish `key : ∀ (x₀ : R.X) (c : Fin R.A.n) (u : Fin e → ℂ), u ∈ (R.A.chart c).target → (R.A.chart c).symm u ∈ R.U x₀ → (R.A.chart c).symm u ∉ bdry (fun x y => BM.s (pr x) (pr y)) → ∃ G : (Fin e → ℂ) → ℂ, AnalyticAt ℂ G u ∧ G u ≠ 0 ∧ (fun t => Real.log (refNorm (fun k => M.dy p (κ k)) (R. …`. Introduce `x₀ c u hu h1 h2`. Take `⟨W, H, oW, mW, HW, nW, eW⟩` from `local_log_norm BM hN hb hr R pr hp ph H1 H2 h1 h2`. Use `⟨H ∘ (R.A.chart c).symm, HW c u ⟨hu, mW⟩, nW _ mW, ?_⟩` and prove the remaining obligations.

Use `filter_upwards [((R.A.chart c).isOpen_inter_preimage_symm oW).mem_nhds ⟨hu, mW⟩] with t ht`. Conclude with `eW _ ht.2`. Prove the components needed by the constructor for the conclusion. Introduce `x₀ c u hu w`. Take `⟨G, hG, hG0, hE⟩` from `key x₀ c u hu.1 hu.2.1.1 hu.2.2`.

Use `(levi_congr (φ := (potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun ph).φ x₀ ∘ (R.A.chart c).symm) hE w).trans_ge ?_` and prove the remaining obligations. Rewrite using `[levi_log_norm hG hG0]`. Introduce `x₀ c u hu w`. Take `⟨G, hG, hG0, hE⟩` from `key x₀ c u hu.1 hu.2.1.1 hu.2.2`. Establish `hE' : ((potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun ph).rsmul (-1)).φ x₀ ∘ (R.A.chart c).symm =ᶠ[𝓝 u] fun t => Real.log ‖(G t)⁻¹‖` using `by filter_upwards [hE] with t ht`.

Establish `ht' : ((potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun ph).rsmul (-1)).φ x₀ ((R.A.chart c).symm t) = -1 * (Real.log (refNorm (fun k => M.dy p (κ k)) (R.lift x₀ ((R.A.chart c).symm t))) + ph ((R.A.chart c).symm t))` using `rfl`. Rewrite using `[Function.comp_apply, ht', ht, norm_inv, Real.log_inv]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[levi_congr hE' w, levi_log_norm (G := fun t => (G t)⁻¹) (hG.inv hG0) (inv_ne_zero hG0)]`.
-/
theorem flat_off_boundary : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ)
    (BM : BaseMetric M n) (p : Ψ × Fin N), (p.2 : ℕ) + 1 = N → ∀ (Kk : Type) [Fintype Kk] (ιk : Kk → Type)
    [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v →
    (∀ k, (∀ p', M.blk p' ≠ some k) → k ∈ Set.range κ) →
    ∀ (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr)
      (ph : R.X → ℝ),
    (∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧ SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x))) →
    (∀ x, pr x ∉ bdry BM.s → ∀ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x →
      Real.log ((BM.hom p).h z) = Real.log ((fsHerm ι (M.dy p)).h z) + ph x) →
    IsPshOn R.A (bdry fun x y => BM.s (pr x) (pr y))ᶜ
        (potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun ph) ∧
      IsPshOn R.A (bdry fun x y => BM.s (pr x) (pr y))ᶜ
        ((potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun ph).rsmul (-1)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p hN Kk _ ιk _ κ v hb hr e R pr hp ph H1 H2
  have key : ∀ (x₀ : R.X) (c : Fin R.A.n) (u : Fin e → ℂ), u ∈ (R.A.chart c).target →
      (R.A.chart c).symm u ∈ R.U x₀ → (R.A.chart c).symm u ∉ bdry (fun x y => BM.s (pr x) (pr y)) →
      ∃ G : (Fin e → ℂ) → ℂ, AnalyticAt ℂ G u ∧ G u ≠ 0 ∧
        (fun t => Real.log (refNorm (fun k => M.dy p (κ k)) (R.lift x₀ ((R.A.chart c).symm t))) +
          ph ((R.A.chart c).symm t)) =ᶠ[𝓝 u] fun t => Real.log ‖G t‖ := by
    intro x₀ c u hu h1 h2
    obtain ⟨W, H, oW, mW, HW, nW, eW⟩ := local_log_norm BM hN hb hr R pr hp ph H1 H2 h1 h2
    refine ⟨H ∘ (R.A.chart c).symm, HW c u ⟨hu, mW⟩, nW _ mW, ?_⟩
    filter_upwards [((R.A.chart c).isOpen_inter_preimage_symm oW).mem_nhds ⟨hu, mW⟩] with t ht
    exact eW _ ht.2
  constructor
  · intro x₀ c u hu w
    obtain ⟨G, hG, hG0, hE⟩ := key x₀ c u hu.1 hu.2.1.1 hu.2.2
    refine (levi_congr (φ := (potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun ph).φ x₀ ∘
      (R.A.chart c).symm) hE w).trans_ge ?_
    rw [levi_log_norm hG hG0]
  · intro x₀ c u hu w
    obtain ⟨G, hG, hG0, hE⟩ := key x₀ c u hu.1 hu.2.1.1 hu.2.2
    have hE' : ((potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun ph).rsmul (-1)).φ x₀ ∘
        (R.A.chart c).symm =ᶠ[𝓝 u] fun t => Real.log ‖(G t)⁻¹‖ := by
      filter_upwards [hE] with t ht
      have ht' : ((potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun ph).rsmul (-1)).φ x₀
          ((R.A.chart c).symm t) = -1 * (Real.log (refNorm (fun k => M.dy p (κ k)) (R.lift x₀ ((R.A.chart c).symm t))) +
            ph ((R.A.chart c).symm t)) := rfl
      rw [Function.comp_apply, ht', ht, norm_inv, Real.log_inv]
      ring
    rw [levi_congr hE' w, levi_log_norm (G := fun t => (G t)⁻¹) (hG.inv hG0) (inv_ne_zero hG0)]

end GlobalTheory.CompanionTheory.Ar.PB.FA.Flat
