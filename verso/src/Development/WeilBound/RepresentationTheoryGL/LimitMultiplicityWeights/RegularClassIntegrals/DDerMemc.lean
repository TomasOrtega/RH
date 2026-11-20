import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.Variation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapInfFinEquivEqProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodFunctionLineDerivative

open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open scoped ContDiff ComplexConjugate Topology

noncomputable section

namespace MainStatements.WeightKernel.Dec.DDerMemc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
Use `open scoped Matrix.Norms.Operator in`. Establish `h1 : ContDiff ℝ ∞ fun t : ℝ => (NormedSpace.exp (t • Z) : Matrix (Fin n) (Fin n) ℂ)`. Establish `: ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)` using `contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt`. Conclude with `this.comp (contDiff_id.smul contDiff_const)`. Use `open scoped Matrix.Norms.Operator in`.

Conclude with `(LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).contDiff.comp h1`.
-/
theorem exp_entry (Z : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ContDiff ℝ ∞ fun t : ℝ => (NormedSpace.exp (t • Z)) i j := by
  open scoped Matrix.Norms.Operator in
  have h1 : ContDiff ℝ ∞ fun t : ℝ => (NormedSpace.exp (t • Z) : Matrix (Fin n) (Fin n) ℂ) := by
    have : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) :=
      contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
    exact this.comp (contDiff_id.smul contDiff_const)
  open scoped Matrix.Norms.Operator in
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).contDiff.comp h1

/- English proof (translation)
Take `⟨w, τ, Z, -, hZ⟩` from `hb`. Use `choose y hy hyZ using hZ`. Use `contDiff_pi.2 fun u => contDiff_pi.2 fun τ' => contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_` and prove the remaining obligations. Establish `e0 : ∀ t, infCoord σ J (projInf σ J (b t)) u τ' i j = archMat σ J τ' (projArch σ J u (embArch σ J w (y t))) i j` using `fun t => by rw [← hy t, ← projInfArch_projInf]; rfl`. Simplify using `only [e0]`.

Distinguish the cases in `hu : u = w`. Substitute `hu` using the available equality. Simplify using `only [projArch_embArch_self]`. Establish `e1 : ∀ t, infEmb τ ((matHom _ σ J (y t)).1 i j) = (NormedSpace.exp (t • Z)) i j` using `fun t => by`. Rewrite using `[← hyZ t]`.

Both sides reduce to the same expression. Break down `infEmb_eq_or_conj h τ τ' with e | e` into its components or cases. Establish `: ∀ t, archMat σ J τ' (y t) i j = (NormedSpace.exp (t • Z)) i j` using `fun t => by`. Rewrite using `[← e1 t, ← e]`. Both sides reduce to the same expression.

Simplify using `only [this]`. Apply the tactic sequence `exact exp_entry Z i j`. Establish `: ∀ t, archMat σ J τ' (y t) i j = conj ((NormedSpace.exp (t • Z)) i j)` using `fun t => by`. Rewrite using `[← e1 t]`. Express the relevant statement in the definitionally equal form `infEmb τ' _ = _`.

Rewrite using `[e]`. Both sides reduce to the same expression. Simplify using `only [this]`. Apply the tactic sequence `exact Complex.conjCLE.contDiff.comp (exp_entry Z i j)`. Simplify using `only [projArch_embArch_ne σ J hu]`.

Conclude with `contDiff_const`.
-/
theorem lineSm (h : IsCMExt F E σ) {b : ℝ → GAd σ J} (hb : IsRealLine σ J b) :
    ContDiff ℝ ∞ fun t => infCoord σ J (projInf σ J (b t)) := by
  classical
  obtain ⟨w, τ, Z, -, hZ⟩ := hb
  choose y hy hyZ using hZ
  refine contDiff_pi.2 fun u => contDiff_pi.2 fun τ' => contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  have e0 : ∀ t, infCoord σ J (projInf σ J (b t)) u τ' i j = archMat σ J τ' (projArch σ J u (embArch σ J w (y t))) i j :=
    fun t => by rw [← hy t, ← projInfArch_projInf]; rfl
  simp only [e0]
  by_cases hu : u = w
  · subst hu
    simp only [projArch_embArch_self]
    have e1 : ∀ t, infEmb τ ((matHom _ σ J (y t)).1 i j) = (NormedSpace.exp (t • Z)) i j := fun t => by
      rw [← hyZ t]; rfl
    rcases infEmb_eq_or_conj h τ τ' with e | e
    · have : ∀ t, archMat σ J τ' (y t) i j = (NormedSpace.exp (t • Z)) i j := fun t => by
        rw [← e1 t, ← e]; rfl
      simp only [this]; exact exp_entry Z i j
    · have : ∀ t, archMat σ J τ' (y t) i j = conj ((NormedSpace.exp (t • Z)) i j) := fun t => by
        rw [← e1 t]
        change infEmb τ' _ = _
        rw [e]; rfl
      simp only [this]; exact Complex.conjCLE.contDiff.comp (exp_entry Z i j)
  · simp only [projArch_embArch_ne σ J hu]
    exact contDiff_const

/- English proof (translation)
Establish `hβ` using `lineSm h hb`. Establish `hfin : ∀ t, projFin σ J (b t) = 1` using `fun t => mem_infPts.1 (GlobalTheory.RealLineInf.realLine_mem_infPts F E σ n J b hb t)`. Establish `hbc : Continuous b` using `GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J b hb`. Establish `hb0 : b 0 = 1` using `GlobalTheory.UAut.ConstAut.realLine_zero h hb`. Take `⟨-, ⟨m, hm, em⟩, -⟩` from `isGroupCoord_infCoord σ J`.

Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem f hf`. Take `⟨a, ⟨hac, Φ, hΦ, ea⟩, c, hc, rfl⟩` from `hf`. Use `set G := fun p : _ × ℝ => Φ (m (p.1, infCoord σ J (projInf σ J (b p.2)))) with hG`. Establish `hGs : ContDiff ℝ ∞ G` using `hΦ.comp (hm.comp (contDiff_fst.prodMk (hβ.comp contDiff_snd)))`.

Establish `hd : ∀ x, HasDerivAt (fun t : ℝ => G (x, t)) (fderiv ℝ G (x, 0) (0, 1)) 0` using `fun x => ((hGs.differentiable (by simp)) (x, (0 : ℝ))).hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id (0 : ℝ)))`. Establish `ea' : ∀ (g : GInf σ J) t, a (g * projInf σ J (b t)) = G (infCoord σ J g, t)` using `fun g t => by`. Rewrite using `[ea, em]`. Establish `e1 : ∀ g, (fun t => infFin σ J a c (g * b t)) = fun t => G (infCoord σ J (projInf σ J g), t) * c (projFin σ J g)` using `fun g => funext fun t => by`. Simplify using `only [infFin, map_mul, hfin, mul_one, ea']`.

Use `⟨fun g => by rw [e1]; exact ((hd _).mul_const _).differentiableAt, ?_⟩` and prove the remaining obligations. Establish `e2 : lineDer b (infFin σ J a c) = infFin σ J (fun g => fderiv ℝ G (infCoord σ J g, 0) (0, 1)) c` using `funext fun g => by`. Rewrite using `[lineDer, e1, ((hd _).mul_const _).deriv]`. Both sides reduce to the same expression. Rewrite using `[e2]`.

Use `infFin_mem_ccAd ⟨HasCompactSupport.intro hac.isCompact fun g hg => ?_, fun x => fderiv ℝ G (x, 0) (0, 1), ?_, fun _ => rfl⟩ hc` and prove the remaining obligations. Rewrite using `[← (hd _).deriv]`. Establish `hc1 : Continuous fun t => g * projInf σ J (b t)` using `continuous_const.mul ((continuous_projInf σ J).comp hbc)`. Establish `: ∀ᶠ t in 𝓝 (0 : ℝ), g * projInf σ J (b t) ∈ (tsupport a)ᶜ` using `hc1.continuousAt.eventually_mem ((isClosed_tsupport a).isOpen_compl.mem_nhds (by simpa [hb0] using hg))`. Establish `e3 : (fun t : ℝ => G (infCoord σ J g, t)) =ᶠ[𝓝 0] fun _ => 0` using `this.mono fun t ht => (ea' g t).symm.trans (image_eq_zero_of_notMem_tsupport ht)`.

Rewrite using `[e3.deriv_eq, deriv_const]`. Conclude with `((hGs.fderiv_right (m := ∞) (by simp)).comp (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const`. Consider the case `zero => exact ⟨fun g => differentiableAt_const _, by`. Establish `: lineDer b (0 : GAd σ J → ℂ) = 0` using `funext fun g => by simp [lineDer]`. Rewrite using `[this]`.

Conclude with `zero_mem _⟩`. Consider the case `add f f' _ _ h1 h2`. Use `⟨fun g => (h1.1 g).add (h2.1 g), ?_⟩` and prove the remaining obligations. Establish `: lineDer b (f + f') = lineDer b f + lineDer b f'` using `funext fun g => deriv_add (h1.1 g) (h2.1 g)`. Rewrite using `[this]`.

Conclude with `add_mem h1.2 h2.2`. Consider the case `smul a f _ h1`. Use `⟨fun g => (h1.1 g).const_smul a, ?_⟩` and prove the remaining obligations. Establish `: lineDer b (a • f) = a • lineDer b f` using `funext fun g => deriv_const_smul a (h1.1 g)`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ a h1.2`.
-/
theorem main (h : IsCMExt F E σ) {b : ℝ → GAd σ J} (hb : IsRealLine σ J b) {f : GAd σ J → ℂ} (hf : f ∈ CcAd σ J) :
    (∀ g, DifferentiableAt ℝ (fun t => f (g * b t)) 0) ∧ lineDer b f ∈ CcAd σ J := by
  have hβ := lineSm h hb
  have hfin : ∀ t, projFin σ J (b t) = 1 := fun t =>
    mem_infPts.1 (GlobalTheory.RealLineInf.realLine_mem_infPts F E σ n J b hb t)
  have hbc : Continuous b := GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J b hb
  have hb0 : b 0 = 1 := GlobalTheory.UAut.ConstAut.realLine_zero h hb
  obtain ⟨-, ⟨m, hm, em⟩, -⟩ := isGroupCoord_infCoord σ J
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ⟨hac, Φ, hΦ, ea⟩, c, hc, rfl⟩ := hf
    set G := fun p : _ × ℝ => Φ (m (p.1, infCoord σ J (projInf σ J (b p.2)))) with hG
    have hGs : ContDiff ℝ ∞ G := hΦ.comp (hm.comp (contDiff_fst.prodMk (hβ.comp contDiff_snd)))
    have hd : ∀ x, HasDerivAt (fun t : ℝ => G (x, t)) (fderiv ℝ G (x, 0) (0, 1)) 0 := fun x =>
      ((hGs.differentiable (by simp)) (x, (0 : ℝ))).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        ((hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id (0 : ℝ)))
    have ea' : ∀ (g : GInf σ J) t, a (g * projInf σ J (b t)) = G (infCoord σ J g, t) := fun g t => by
      rw [ea, em]
    have e1 : ∀ g, (fun t => infFin σ J a c (g * b t)) =
        fun t => G (infCoord σ J (projInf σ J g), t) * c (projFin σ J g) := fun g => funext fun t => by
      simp only [infFin, map_mul, hfin, mul_one, ea']
    refine ⟨fun g => by rw [e1]; exact ((hd _).mul_const _).differentiableAt, ?_⟩
    have e2 : lineDer b (infFin σ J a c) =
        infFin σ J (fun g => fderiv ℝ G (infCoord σ J g, 0) (0, 1)) c := funext fun g => by
      rw [lineDer, e1, ((hd _).mul_const _).deriv]; rfl
    rw [e2]
    refine infFin_mem_ccAd ⟨HasCompactSupport.intro hac.isCompact fun g hg => ?_,
      fun x => fderiv ℝ G (x, 0) (0, 1), ?_, fun _ => rfl⟩ hc
    · rw [← (hd _).deriv]
      have hc1 : Continuous fun t => g * projInf σ J (b t) :=
        continuous_const.mul ((continuous_projInf σ J).comp hbc)
      have : ∀ᶠ t in 𝓝 (0 : ℝ), g * projInf σ J (b t) ∈ (tsupport a)ᶜ :=
        hc1.continuousAt.eventually_mem ((isClosed_tsupport a).isOpen_compl.mem_nhds (by simpa [hb0] using hg))
      have e3 : (fun t : ℝ => G (infCoord σ J g, t)) =ᶠ[𝓝 0] fun _ => 0 :=
        this.mono fun t ht => (ea' g t).symm.trans (image_eq_zero_of_notMem_tsupport ht)
      rw [e3.deriv_eq, deriv_const]
    · exact ((hGs.fderiv_right (m := ∞) (by simp)).comp (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const
  | zero => exact ⟨fun g => differentiableAt_const _, by
      have : lineDer b (0 : GAd σ J → ℂ) = 0 := funext fun g => by simp [lineDer]
      rw [this]; exact zero_mem _⟩
  | add f f' _ _ h1 h2 =>
    refine ⟨fun g => (h1.1 g).add (h2.1 g), ?_⟩
    have : lineDer b (f + f') = lineDer b f + lineDer b f' := funext fun g => deriv_add (h1.1 g) (h2.1 g)
    rw [this]; exact add_mem h1.2 h2.2
  | smul a f _ h1 =>
    refine ⟨fun g => (h1.1 g).const_smul a, ?_⟩
    have : lineDer b (a • f) = a • lineDer b f := funext fun g => deriv_const_smul a (h1.1 g)
    rw [this]; exact Submodule.smul_mem _ a h1.2

end MainStatements.WeightKernel.Dec.DDerMemc

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ h _ _ _ _ hf _ hb` and use `(MainStatements.WeightKernel.Dec.DDerMemc.main h hb hf).2`.
-/
theorem MainStatements.WeightKernel.Dec.derMem : MainStatements.WeightKernel.Dec.DerMem :=
  fun _ _ _ _ _ _ _ _ h _ _ _ _ hf _ hb => (MainStatements.WeightKernel.Dec.DDerMemc.main h hb hf).2
