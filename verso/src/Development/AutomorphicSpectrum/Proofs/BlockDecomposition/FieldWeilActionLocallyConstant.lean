import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnstatedLocalWeilLemma
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RWConstMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NsgDivNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationHypothesisStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilInducedRepresentationHypothesisStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilInducedRepresentationHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilSmoothnessHypothesis

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open scoped Topology
open Filter Matrix Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.WeilSmooth GlobalTheory.CompanionTheory.WeilPiRep

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilLocConst

/- English proof (translation)
Introduce `F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη c Φ hΦ g h hg hh`. Establish `wdg` using `GlobalTheory.CompanionTheory.WeilDilation.wDiagT F χ hχ hχ1 E hfr hcont σ hσ η hη`. Establish `wsb` using `GlobalTheory.CompanionTheory.WeilSB.wsb F χ hχ hχ1 E hfr hcont σ hσ η hη`. Establish `wrp` using `GlobalTheory.T.weil_representation_hypothesis F χ hχ hχ1 E hfr hcont σ hσ η hη`. Use `beta_reduce at wdg wsb wrp`.

Establish `hdet : ∀ x : GL (Fin 2) F, (x.val).det ≠ 0` using `fun x => ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).ne_zero`. Take `⟨tg, htg⟩` from `hg`. Take `⟨t, hnt⟩` from `hh`. Establish `hiso` using `hΦ.2.2`. Establish `hpi : piE E χ σ η c h Φ = fun x => (((c t : ℂˣ) : ℂ) * (((modulus (h.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ))) * rWE E χ σ η (red h.val) (fun y => Φ (y * (t : E))) x`.

Use function extensionality and compare the values at `fun x => piG_choice χ σ (muE E χ) (lamE E χ η) c hiso h t hnt x`. Use `set k : ℂ := ((c t : ℂˣ) : ℂ) * (((modulus (h.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) with hk`. Use `set Ψ : E → ℂ := fun y => Φ (y * (t : E)) with hΨdef`. Establish `hΨ : Ψ ∈ SBc F E c` using `dil_mem hΦ t`. Establish `hΨE : Ψ ∈ SBE E` using `⟨hΨ.1, hΨ.2.1⟩`.

Establish `hd1 : (red h.val).det = 1` using `det_red (hdet h)`. Establish `hmem : piE E χ σ η c h Φ ∈ SBc F E c`. Rewrite using `[hpi]`. Conclude with `const_mul_mem ((wsb _ hd1 Ψ hΨE).2 c hΨ) k`. Establish `hdg` using `hdet g`.

Establish `hgh : Algebra.norm F ((tg * t : Eˣ) : E) = ((g * h).val).det`. Rewrite using `[Units.val_mul, map_mul, htg, hnt, Units.val_mul, Matrix.det_mul]`. Use function extensionality and compare the values at `x`. Establish `lhs` using `piG_choice χ σ (muE E χ) (lamE E χ η) c hiso (g * h) (tg * t) hgh x`. Establish `rhs` using `piG_choice χ σ (muE E χ) (lamE E χ η) c hmem.2.2 g tg htg x`.

Use `lhs.trans (Eq.trans ?_ rhs.symm)` and prove the remaining obligations. Use `set f : E → ℂ := fun y => Ψ (y * (tg : E)) with hfdef`. Establish `hfE : f ∈ SBE E`. Use `dil_mem hΨ tg` as an intermediate fact. Conclude with `⟨this.1, this.2.1⟩`.

Establish `hcj : (cjA (g.val).det (red h.val)).det = 1` using `by rw [det_cjA hdg, hd1]`. Establish `hgd : (red g.val).det = 1` using `det_red hdg`. Establish `hL : (fun y => Φ (y * ((tg * t : Eˣ) : E))) = f`. Use function extensionality and compare the values at `y`. Simplify using `only [hfdef, hΨdef, Units.val_mul, mul_assoc]`.

Establish `hR : (fun y => piE E χ σ η c h Φ (y * (tg : E))) = fun y => k * rWE E χ σ η (cjA (g.val).det (red h.val)) f y`. Use function extensionality and compare the values at `y`. Use `congrFun (wdg (red h.val) hd1 tg Ψ hΨE) y` as an intermediate fact. Rewrite `this` using `[htg]`. Rewrite using `[hpi]`.

Simplify using `only []`. Rewrite using `[this]`. Establish `e1 : rW χ σ (muE E χ) (lamE E χ η) (((g * h).val) 0 0 / ((g * h).val).det) (((g * h).val) 0 1) (((g * h).val) 1 0 / ((g * h).val).det) (((g * h).val) 1 1) f x = rWE E χ σ η (red (g * h).val) f x` using `rfl`. Establish `e2 : rW χ σ (muE E χ) (lamE E χ η) ((g.val) 0 0 / (g.val).det) ((g.val) 0 1) ((g.val) 1 0 / (g.val).det) ((g.val) 1 1) (fun y => k * rWE E χ σ η (cjA (g.val).det (red h.val)) f y) x = k * rWE E χ σ η (red g.val) (rWE E χ σ η (cjA (g.val).det (red h.val)) f) x` using `GlobalTheory.CompanionTheory.WeilChoice.rW_const_mul _ _ _ _ _ _ _ _ _ _ _`. Rewrite using `[hL, hR, e1, e2, Units.val_mul, red_mul hdg (hdet h), wrp _ _ hgd hcj f hfE]`.

Establish `e3 : (((modulus ((g.val * h.val).det) : ℝ) : ℂ) ^ (1 / 2 : ℂ)) = (((modulus (g.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) * (((modulus (h.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ))`. Rewrite using `[Matrix.det_mul, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]`. Rewrite using `[e3, map_mul, Units.val_mul, hk]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem piE_mul : GL2LocalData.ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η =>
    ∀ c : Eˣ →* ℂˣ, ∀ Φ ∈ GL2LocalData.SBc F E c, ∀ g h : GL (Fin 2) F,
      (∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det) →
      (∃ t : Eˣ, Algebra.norm F (t : E) = (h.val).det) →
      GL2LocalData.piE E χ σ η c (g * h) Φ = GL2LocalData.piE E χ σ η c g (GL2LocalData.piE E χ σ η c h Φ) := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη c Φ hΦ g h hg hh
  have wdg := GlobalTheory.CompanionTheory.WeilDilation.wDiagT F χ hχ hχ1 E hfr hcont σ hσ η hη
  have wsb := GlobalTheory.CompanionTheory.WeilSB.wsb F χ hχ hχ1 E hfr hcont σ hσ η hη
  have wrp := GlobalTheory.T.weil_representation_hypothesis F χ hχ hχ1 E hfr hcont σ hσ η hη
  beta_reduce at wdg wsb wrp
  have hdet : ∀ x : GL (Fin 2) F, (x.val).det ≠ 0 := fun x =>
    ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).ne_zero
  obtain ⟨tg, htg⟩ := hg
  obtain ⟨t, hnt⟩ := hh
  have hiso := hΦ.2.2
  have hpi : piE E χ σ η c h Φ = fun x => (((c t : ℂˣ) : ℂ) * (((modulus (h.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ))) *
      rWE E χ σ η (red h.val) (fun y => Φ (y * (t : E))) x :=
    funext fun x => piG_choice χ σ (muE E χ) (lamE E χ η) c hiso h t hnt x
  set k : ℂ := ((c t : ℂˣ) : ℂ) * (((modulus (h.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) with hk
  set Ψ : E → ℂ := fun y => Φ (y * (t : E)) with hΨdef
  have hΨ : Ψ ∈ SBc F E c := dil_mem hΦ t
  have hΨE : Ψ ∈ SBE E := ⟨hΨ.1, hΨ.2.1⟩
  have hd1 : (red h.val).det = 1 := det_red (hdet h)
  have hmem : piE E χ σ η c h Φ ∈ SBc F E c := by
    rw [hpi]
    exact const_mul_mem ((wsb _ hd1 Ψ hΨE).2 c hΨ) k
  have hdg := hdet g
  have hgh : Algebra.norm F ((tg * t : Eˣ) : E) = ((g * h).val).det := by
    rw [Units.val_mul, map_mul, htg, hnt, Units.val_mul, Matrix.det_mul]
  funext x
  have lhs := piG_choice χ σ (muE E χ) (lamE E χ η) c hiso (g * h) (tg * t) hgh x
  have rhs := piG_choice χ σ (muE E χ) (lamE E χ η) c hmem.2.2 g tg htg x
  refine lhs.trans (Eq.trans ?_ rhs.symm)
  set f : E → ℂ := fun y => Ψ (y * (tg : E)) with hfdef
  have hfE : f ∈ SBE E := by
    have := dil_mem hΨ tg
    exact ⟨this.1, this.2.1⟩
  have hcj : (cjA (g.val).det (red h.val)).det = 1 := by rw [det_cjA hdg, hd1]
  have hgd : (red g.val).det = 1 := det_red hdg
  have hL : (fun y => Φ (y * ((tg * t : Eˣ) : E))) = f := by
    funext y
    simp only [hfdef, hΨdef, Units.val_mul, mul_assoc]
  have hR : (fun y => piE E χ σ η c h Φ (y * (tg : E))) =
      fun y => k * rWE E χ σ η (cjA (g.val).det (red h.val)) f y := by
    funext y
    have := congrFun (wdg (red h.val) hd1 tg Ψ hΨE) y
    rw [htg] at this
    rw [hpi]
    simp only []
    rw [this]
  have e1 : rW χ σ (muE E χ) (lamE E χ η) (((g * h).val) 0 0 / ((g * h).val).det) (((g * h).val) 0 1)
      (((g * h).val) 1 0 / ((g * h).val).det) (((g * h).val) 1 1) f x =
      rWE E χ σ η (red (g * h).val) f x := rfl
  have e2 : rW χ σ (muE E χ) (lamE E χ η) ((g.val) 0 0 / (g.val).det) ((g.val) 0 1)
      ((g.val) 1 0 / (g.val).det) ((g.val) 1 1)
      (fun y => k * rWE E χ σ η (cjA (g.val).det (red h.val)) f y) x =
      k * rWE E χ σ η (red g.val) (rWE E χ σ η (cjA (g.val).det (red h.val)) f) x :=
    GlobalTheory.CompanionTheory.WeilChoice.rW_const_mul _ _ _ _ _ _ _ _ _ _ _
  rw [hL, hR, e1, e2, Units.val_mul, red_mul hdg (hdet h), wrp _ _ hgd hcj f hfE]
  have e3 : (((modulus ((g.val * h.val).det) : ℝ) : ℂ) ^ (1 / 2 : ℂ)) =
      (((modulus (g.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) * (((modulus (h.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) := by
    rw [Matrix.det_mul, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
  rw [e3, map_mul, Units.val_mul, hk]
  ring

/- English proof (translation)
Introduce `F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη c hc Φ hΦ g₀ hg₀`. Use `haveI : Fact (Module.finrank F E = 2) := ⟨hfr⟩`. Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)`. Use `haveI : ValuativeExtension F E := GlobalTheory.CompanionTheory.WeilSB.valuativeExtension_of_continuous hcont`. Use `haveI : Algebra.IsSeparable F E := inferInstance`.

Establish `hNc` using `GlobalTheory.CompanionTheory.WeilSB.continuous_norm_of (F := F) (E := E) hcont`. Establish `hlc` using `GlobalTheory.CompanionTheory.WeilSB.isLocallyConstant_char hχ hχ1`. Establish `hSB : Φ ∈ SBE E` using `⟨hΦ.1, hΦ.2.1⟩`. Establish `hiso` using `hΦ.2.2`. Establish `hmul : ∀ g h : GL (Fin 2) F, (∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det) → (∃ t : Eˣ, Algebra.norm F (t : E) = (h.val).det) → piE E χ σ η c (g * h) Φ = piE E χ σ η c g (piE E χ σ η c h Φ)` using `piE_mul F χ hχ hχ1 E hfr hcont σ hσ η hη c Φ hΦ`.

Establish `hrep : ∀ g h : Matrix (Fin 2) (Fin 2) F, g.det = 1 → h.det = 1 → ∀ Ψ ∈ SBE E, rWE E χ σ η (g * h) Ψ = rWE E χ σ η g (rWE E χ σ η h Ψ)` using `GlobalTheory.T.weil_representation_hypothesis F χ hχ hχ1 E hfr hcont σ hσ η hη`. Establish `hsb : ∀ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 → ∀ Ψ ∈ SBE E, rWE E χ σ η g Ψ ∈ SBE E` using `fun g hg Ψ hΨ => (GlobalTheory.CompanionTheory.WeilSB.wsb F χ hχ hχ1 E hfr hcont σ hσ η hη g hg Ψ hΨ).1`. Establish `hone : piE E χ σ η c 1 Φ = Φ` using `(piG_det_one χ σ (muE E χ) (lamE E χ η) c hiso 1 (by simp)).trans (rWm_one χ σ (muE E χ) (lamE E χ η) Φ)`. Choose the witnesses or unpack the hypotheses as in `⟨H, hH⟩ : ∃ H : Subgroup (GL (Fin 2) F), ∀ h, h ∈ H ↔ (∃ t : Eˣ, Algebra.norm F (t : E) = (h.val).det) ∧ piE E χ σ η c h Φ = Φ := by`. Use `⟨{ carrier := {h | (∃ t : Eˣ, Algebra.norm F (t : E) = (h.val).det) ∧ piE E χ σ η c h Φ = Φ} mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun h => Iff.rfl⟩` and prove the remaining obligations.

Introduce and unpack `a b ⟨⟨s, hs⟩, ha⟩ ⟨⟨t, ht⟩, hb⟩`. Use `⟨⟨s * t, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, map_mul, hs, ht, Units.val_mul, Matrix.det_mul]`. Rewrite using `[hmul a b ⟨s, hs⟩ ⟨t, ht⟩, hb, ha]`. Conclude with `⟨⟨1, by simp⟩, hone⟩`.

Introduce and unpack `a ⟨⟨t, ht⟩, ha⟩`. Establish `h1 : ((a⁻¹ : GL (Fin 2) F).val).det * (a.val).det = 1`. Rewrite using `[← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel]`. Simplify using the standard rewrite rules. Establish `h2 : Algebra.norm F ((t⁻¹ : Eˣ) : E) * (a.val).det = 1`.

Rewrite using `[← ht, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]`. Establish `hd : Algebra.norm F ((t⁻¹ : Eˣ) : E) = ((a⁻¹ : GL (Fin 2) F).val).det` using `mul_right_cancel₀ (show (a.val).det ≠ 0 from fun h0 => by simp [h0] at h1) (h2.trans h1.symm)`. Use `⟨⟨t⁻¹, hd⟩, ?_⟩` and prove the remaining obligations. Use `hmul a⁻¹ a ⟨t⁻¹, hd⟩ ⟨t, ht⟩` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel, hone, ha]`.

Conclude with `this.symm`. Establish `key : ∀ h : GL (Fin 2) F, (∃ t : Eˣ, Algebra.norm F (t : E) = (h.val).det) → piE E χ σ η c h Φ = Φ → h ∈ H` using `fun h hx he => (hH h).2 ⟨hx, he⟩`. Establish `hdet1 : ∀ h : GL (Fin 2) F, (h.val).det = 1 → rWE E χ σ η h.val Φ = Φ → h ∈ H`. Introduce `h hd he`. Use `key h ⟨1, by simp [hd]⟩ ?_` and prove the remaining obligations.

Conclude with `(piG_det_one χ σ (muE E χ) (lamE E χ η) c hiso h hd).trans he`. Establish `hUp : ∀ᶠ x in 𝓝 (0 : F), uni2 x ∈ H` using `by filter_upwards [ev_chirp hlc hNc hΦ.2.1] with x hx`. Use `hdet1 _ (by simp [uni2, Matrix.det_fin_two]) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Conclude with `(rWm_upper χ σ (muE E χ) (lamE E χ η) x Φ z).trans (hx z)`.

Establish `hLow : ∀ᶠ y in 𝓝 (0 : F), low y ∈ H`. Establish `hwm : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F).det = 1` using `by simp [Matrix.det_fin_two]`. Establish `hwi : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F).det = 1` using `by simp [Matrix.det_fin_two]`. Establish `hΦ'` using `hsb _ hwi Φ hSB`. Establish `ht : Tendsto (fun y : F => -y) (𝓝 0) (𝓝 0)`.

Establish `: ContinuousAt (fun y : F => -y) 0` using `continuous_neg.continuousAt`. Simplify `this` using `[ContinuousAt]`. Use `filter_upwards [ht.eventually (ev_chirp hlc hNc hΦ'.2)] with y hy`. Establish `hnd : (!![1, -y; 0, 1] : Matrix (Fin 2) (Fin 2) F).det = 1` using `by simp [Matrix.det_fin_two]`. Establish `hn : rWE E χ σ η !![1, -y; 0, 1] (rWE E χ σ η !![0, -1; 1, 0] Φ) = rWE E χ σ η !![0, -1; 1, 0] Φ`.

Use function extensionality and compare the values at `fun z => (rWm_upper χ σ (muE E χ) (lamE E χ η) (-y) _ z).trans (hy z)`. Establish `e : (low y).val = !![0, 1; -1, 0] * (!![1, -y; 0, 1] * !![0, -1; 1, 0])`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [low, Matrix.mul_apply, Fin.sum_univ_two]`. Establish `e1 : (!![0, 1; -1, 0] * !![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) = 1`.

Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]`. Use `hdet1 _ (by simp [low, Matrix.det_fin_two]) ?_` and prove the remaining obligations. Rewrite using `[e, hrep _ _ hwm (by rw [Matrix.det_mul, hnd, hwi, one_mul]) Φ hSB, hrep _ _ hnd hwi Φ hSB, hn, ← hrep _ _ hwm hwi Φ hSB, e1]`. Conclude with `rWm_one χ σ (muE E χ) (lamE E χ η) Φ`.

Establish `tE : Tendsto (algebraMap F E) (𝓝 1) (𝓝 1)`. Use `hcont.tendsto 1` as an intermediate fact. Rewrite `this` using `[map_one]`. Then use the resulting hypothesis. Establish `hGood : ∀ᶠ r in 𝓝 (1 : F), r ≠ 0 ∧ GroundTheory.LocalField.modulus r = 1 ∧ (∀ x, Φ (x * algebraMap F E r) = Φ x) ∧ ∀ u : Eˣ, (u : E) = algebraMap F E r → c u = 1` using `by filter_upwards [eventually_ne_nhds (one_ne_zero (α := F)), ev_modulus, tE.eventually (ev_dil hSB), tE.eventually (ev_char c hc.1)] with r h1 h2 h3 h4`. Conclude with `⟨h1, h2, h3, h4⟩`.

Establish `hS` using `ev_sq hGood`. Establish `hD : ∀ᶠ a in 𝓝 (1 : F), ∀ s : Fˣ, (s : F) = a → dg2 s 1 ∈ H` using `by filter_upwards [hS] with a ha s hs`. Take `⟨r, ⟨hr0, hrm, hrd, hrc⟩, hra⟩` from `ha`. Set `t : Eˣ` to `Units.mk0 (algebraMap F E r) ((map_ne_zero _).2 hr0)`. Establish `hNt : Algebra.norm F (t : E) = a`.

Simplify using `[t, Algebra.norm_algebraMap, hfr, sq, hra]`. Establish `hdet : ((dg2 s 1 : GL (Fin 2) F).val).det = a`. Simplify using `[dg2, Matrix.det_fin_two, hs]`. Establish `ha0 : a ≠ 0` using `hs ▸ s.ne_zero`. Establish `hma : GroundTheory.LocalField.modulus a = 1`.

Rewrite using `[← hra, GroundTheory.LocalField.modulus_mul, hrm, one_mul]`. Use `key _ ⟨t, by rw [hNt, hdet]⟩ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Establish `e00 : (dg2 s 1 : GL (Fin 2) F).val 0 0 = a` using `by simp [dg2, hs]`. Establish `e01 : (dg2 s 1 : GL (Fin 2) F).val 0 1 = 0` using `by simp [dg2]`.

Establish `e10 : (dg2 s 1 : GL (Fin 2) F).val 1 0 = 0` using `by simp [dg2]`. Establish `e11 : (dg2 s 1 : GL (Fin 2) F).val 1 1 = 1` using `by simp [dg2]`. Use `(piG_choice χ σ (muE E χ) (lamE E χ η) c hiso _ t (by rw [hNt, hdet]) x).trans ?_` and prove the remaining obligations. Rewrite using `[hdet, e00, e01, e10, e11, div_self ha0, zero_div, rW_zero, hrc t rfl, hma]`. Simplify using `[nsg_one, t, hrd]`.

Establish `hM : ∀ᶠ a in 𝓝 (1 : F), ∀ s : Fˣ, (s : F) = a → dg2 s s⁻¹ ∈ H` using `by filter_upwards [hS] with a ha s hs`. Take `⟨r, ⟨hr0, hrm, hrd, hrc⟩, hra⟩` from `ha`. Set `t : Eˣ` to `Units.mk0 (algebraMap F E r) ((map_ne_zero _).2 hr0)`. Establish `hNt : Algebra.norm F (t : E) = a`. Simplify using `[t, Algebra.norm_algebraMap, hfr, sq, hra]`.

Establish `hma : GroundTheory.LocalField.modulus a = 1`. Rewrite using `[← hra, GroundTheory.LocalField.modulus_mul, hrm, one_mul]`. Use `hdet1 _ (by simp [dg2, Matrix.det_fin_two]) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Use `show rW χ σ (muE E χ) (lamE E χ η) ((dg2 s s⁻¹ : GL (Fin 2) F).val 0 0) ((dg2 s s⁻¹ : GL (Fin 2) F).val 0 1) ((dg2 s s⁻¹ : GL (Fin 2) F).val 1 0) ((dg2 s s⁻¹ : GL (Fin 2) F).val 1 1) Φ z = Φ z`.

Establish `e00 : (dg2 s s⁻¹ : GL (Fin 2) F).val 0 0 = a` using `by simp [dg2, hs]`. Establish `e01 : (dg2 s s⁻¹ : GL (Fin 2) F).val 0 1 = 0` using `by simp [dg2]`. Establish `e10 : (dg2 s s⁻¹ : GL (Fin 2) F).val 1 0 = 0` using `by simp [dg2]`. Rewrite using `[e00, e01, e10, rW_zero, hma, ← hNt, nsg_norm, hNt]`. Establish `: Φ (algebraMap F E a * z) = Φ z`.

Rewrite using `[← hra, map_mul, mul_comm, ← mul_assoc, hrd, hrd]`. Simplify using `[this]`. Establish `hmem` using `mem_nhds_of_factors H hUp hLow hD hM`. Establish `hcont' : ContinuousAt (fun g : GL (Fin 2) F => g₀⁻¹ * g) g₀` using `(continuous_const.mul continuous_id).continuousAt`. Use `⟨(fun g : GL (Fin 2) F => g₀⁻¹ * g) ⁻¹' (H : Set (GL (Fin 2) F)), hcont'.preimage_mem_nhds (by simpa using hmem), fun g hg => ?_⟩` and prove the remaining obligations.

Take `⟨hx, he⟩` from `(hH _).1 hg`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem piE_locConst : GL2LocalData.ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η =>
  ∀ c : Eˣ →* ℂˣ, IsUnit1 c → ∀ Φ ∈ GL2LocalData.SBc F E c, ∀ g₀ : GL (Fin 2) F,
    (∃ t : Eˣ, Algebra.norm F (t : E) = (g₀.val).det) →
    ∃ U ∈ nhds g₀, ∀ g ∈ U, GL2LocalData.piE E χ σ η c g Φ = GL2LocalData.piE E χ σ η c g₀ Φ := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη c hc Φ hΦ g₀ hg₀
  haveI : Fact (Module.finrank F E = 2) := ⟨hfr⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : ValuativeExtension F E := GlobalTheory.CompanionTheory.WeilSB.valuativeExtension_of_continuous hcont
  haveI : Algebra.IsSeparable F E := inferInstance
  have hNc := GlobalTheory.CompanionTheory.WeilSB.continuous_norm_of (F := F) (E := E) hcont
  have hlc := GlobalTheory.CompanionTheory.WeilSB.isLocallyConstant_char hχ hχ1
  have hSB : Φ ∈ SBE E := ⟨hΦ.1, hΦ.2.1⟩
  have hiso := hΦ.2.2
  have hmul : ∀ g h : GL (Fin 2) F, (∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det) →
      (∃ t : Eˣ, Algebra.norm F (t : E) = (h.val).det) →
      piE E χ σ η c (g * h) Φ = piE E χ σ η c g (piE E χ σ η c h Φ) :=
    piE_mul F χ hχ hχ1 E hfr hcont σ hσ η hη c Φ hΦ
  have hrep : ∀ g h : Matrix (Fin 2) (Fin 2) F, g.det = 1 → h.det = 1 → ∀ Ψ ∈ SBE E,
      rWE E χ σ η (g * h) Ψ = rWE E χ σ η g (rWE E χ σ η h Ψ) :=
    GlobalTheory.T.weil_representation_hypothesis F χ hχ hχ1 E hfr hcont σ hσ η hη
  have hsb : ∀ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 → ∀ Ψ ∈ SBE E, rWE E χ σ η g Ψ ∈ SBE E :=
    fun g hg Ψ hΨ => (GlobalTheory.CompanionTheory.WeilSB.wsb F χ hχ hχ1 E hfr hcont σ hσ η hη g hg Ψ hΨ).1
  have hone : piE E χ σ η c 1 Φ = Φ :=
    (piG_det_one χ σ (muE E χ) (lamE E χ η) c hiso 1 (by simp)).trans
      (rWm_one χ σ (muE E χ) (lamE E χ η) Φ)
  obtain ⟨H, hH⟩ : ∃ H : Subgroup (GL (Fin 2) F), ∀ h, h ∈ H ↔
      (∃ t : Eˣ, Algebra.norm F (t : E) = (h.val).det) ∧ piE E χ σ η c h Φ = Φ := by
    refine ⟨{ carrier := {h | (∃ t : Eˣ, Algebra.norm F (t : E) = (h.val).det) ∧ piE E χ σ η c h Φ = Φ}
              mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun h => Iff.rfl⟩
    · rintro a b ⟨⟨s, hs⟩, ha⟩ ⟨⟨t, ht⟩, hb⟩
      refine ⟨⟨s * t, ?_⟩, ?_⟩
      · rw [Units.val_mul, map_mul, hs, ht, Units.val_mul, Matrix.det_mul]
      · rw [hmul a b ⟨s, hs⟩ ⟨t, ht⟩, hb, ha]
    · exact ⟨⟨1, by simp⟩, hone⟩
    · rintro a ⟨⟨t, ht⟩, ha⟩
      have h1 : ((a⁻¹ : GL (Fin 2) F).val).det * (a.val).det = 1 := by
        rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel]
        simp
      have h2 : Algebra.norm F ((t⁻¹ : Eˣ) : E) * (a.val).det = 1 := by
        rw [← ht, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
      have hd : Algebra.norm F ((t⁻¹ : Eˣ) : E) = ((a⁻¹ : GL (Fin 2) F).val).det :=
        mul_right_cancel₀ (show (a.val).det ≠ 0 from fun h0 => by simp [h0] at h1) (h2.trans h1.symm)
      refine ⟨⟨t⁻¹, hd⟩, ?_⟩
      have := hmul a⁻¹ a ⟨t⁻¹, hd⟩ ⟨t, ht⟩
      rw [inv_mul_cancel, hone, ha] at this
      exact this.symm
  have key : ∀ h : GL (Fin 2) F, (∃ t : Eˣ, Algebra.norm F (t : E) = (h.val).det) →
      piE E χ σ η c h Φ = Φ → h ∈ H := fun h hx he => (hH h).2 ⟨hx, he⟩
  have hdet1 : ∀ h : GL (Fin 2) F, (h.val).det = 1 → rWE E χ σ η h.val Φ = Φ → h ∈ H := by
    intro h hd he
    refine key h ⟨1, by simp [hd]⟩ ?_
    exact (piG_det_one χ σ (muE E χ) (lamE E χ η) c hiso h hd).trans he
  have hUp : ∀ᶠ x in 𝓝 (0 : F), uni2 x ∈ H := by
    filter_upwards [ev_chirp hlc hNc hΦ.2.1] with x hx
    refine hdet1 _ (by simp [uni2, Matrix.det_fin_two]) ?_
    funext z
    exact (rWm_upper χ σ (muE E χ) (lamE E χ η) x Φ z).trans (hx z)
  have hLow : ∀ᶠ y in 𝓝 (0 : F), low y ∈ H := by
    have hwm : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F).det = 1 := by simp [Matrix.det_fin_two]
    have hwi : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F).det = 1 := by simp [Matrix.det_fin_two]
    have hΦ' := hsb _ hwi Φ hSB
    have ht : Tendsto (fun y : F => -y) (𝓝 0) (𝓝 0) := by
      have : ContinuousAt (fun y : F => -y) 0 := continuous_neg.continuousAt
      simpa [ContinuousAt] using this
    filter_upwards [ht.eventually (ev_chirp hlc hNc hΦ'.2)] with y hy
    have hnd : (!![1, -y; 0, 1] : Matrix (Fin 2) (Fin 2) F).det = 1 := by simp [Matrix.det_fin_two]
    have hn : rWE E χ σ η !![1, -y; 0, 1] (rWE E χ σ η !![0, -1; 1, 0] Φ) = rWE E χ σ η !![0, -1; 1, 0] Φ :=
      funext fun z => (rWm_upper χ σ (muE E χ) (lamE E χ η) (-y) _ z).trans (hy z)
    have e : (low y).val = !![0, 1; -1, 0] * (!![1, -y; 0, 1] * !![0, -1; 1, 0]) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [low, Matrix.mul_apply, Fin.sum_univ_two]
    have e1 : (!![0, 1; -1, 0] * !![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    refine hdet1 _ (by simp [low, Matrix.det_fin_two]) ?_
    rw [e, hrep _ _ hwm (by rw [Matrix.det_mul, hnd, hwi, one_mul]) Φ hSB, hrep _ _ hnd hwi Φ hSB, hn,
      ← hrep _ _ hwm hwi Φ hSB, e1]
    exact rWm_one χ σ (muE E χ) (lamE E χ η) Φ
  have tE : Tendsto (algebraMap F E) (𝓝 1) (𝓝 1) := by
    have := hcont.tendsto 1
    rwa [map_one] at this
  have hGood : ∀ᶠ r in 𝓝 (1 : F), r ≠ 0 ∧ GroundTheory.LocalField.modulus r = 1 ∧
      (∀ x, Φ (x * algebraMap F E r) = Φ x) ∧ ∀ u : Eˣ, (u : E) = algebraMap F E r → c u = 1 := by
    filter_upwards [eventually_ne_nhds (one_ne_zero (α := F)), ev_modulus, tE.eventually (ev_dil hSB),
      tE.eventually (ev_char c hc.1)] with r h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hS := ev_sq hGood
  have hD : ∀ᶠ a in 𝓝 (1 : F), ∀ s : Fˣ, (s : F) = a → dg2 s 1 ∈ H := by
    filter_upwards [hS] with a ha s hs
    obtain ⟨r, ⟨hr0, hrm, hrd, hrc⟩, hra⟩ := ha
    let t : Eˣ := Units.mk0 (algebraMap F E r) ((map_ne_zero _).2 hr0)
    have hNt : Algebra.norm F (t : E) = a := by
      simp [t, Algebra.norm_algebraMap, hfr, sq, hra]
    have hdet : ((dg2 s 1 : GL (Fin 2) F).val).det = a := by
      simp [dg2, Matrix.det_fin_two, hs]
    have ha0 : a ≠ 0 := hs ▸ s.ne_zero
    have hma : GroundTheory.LocalField.modulus a = 1 := by
      rw [← hra, GroundTheory.LocalField.modulus_mul, hrm, one_mul]
    refine key _ ⟨t, by rw [hNt, hdet]⟩ ?_
    funext x
    have e00 : (dg2 s 1 : GL (Fin 2) F).val 0 0 = a := by simp [dg2, hs]
    have e01 : (dg2 s 1 : GL (Fin 2) F).val 0 1 = 0 := by simp [dg2]
    have e10 : (dg2 s 1 : GL (Fin 2) F).val 1 0 = 0 := by simp [dg2]
    have e11 : (dg2 s 1 : GL (Fin 2) F).val 1 1 = 1 := by simp [dg2]
    refine (piG_choice χ σ (muE E χ) (lamE E χ η) c hiso _ t (by rw [hNt, hdet]) x).trans ?_
    rw [hdet, e00, e01, e10, e11, div_self ha0, zero_div, rW_zero, hrc t rfl, hma]
    simp [nsg_one, t, hrd]
  have hM : ∀ᶠ a in 𝓝 (1 : F), ∀ s : Fˣ, (s : F) = a → dg2 s s⁻¹ ∈ H := by
    filter_upwards [hS] with a ha s hs
    obtain ⟨r, ⟨hr0, hrm, hrd, hrc⟩, hra⟩ := ha
    let t : Eˣ := Units.mk0 (algebraMap F E r) ((map_ne_zero _).2 hr0)
    have hNt : Algebra.norm F (t : E) = a := by
      simp [t, Algebra.norm_algebraMap, hfr, sq, hra]
    have hma : GroundTheory.LocalField.modulus a = 1 := by
      rw [← hra, GroundTheory.LocalField.modulus_mul, hrm, one_mul]
    refine hdet1 _ (by simp [dg2, Matrix.det_fin_two]) ?_
    funext z
    show rW χ σ (muE E χ) (lamE E χ η) ((dg2 s s⁻¹ : GL (Fin 2) F).val 0 0) ((dg2 s s⁻¹ : GL (Fin 2) F).val 0 1)
      ((dg2 s s⁻¹ : GL (Fin 2) F).val 1 0) ((dg2 s s⁻¹ : GL (Fin 2) F).val 1 1) Φ z = Φ z
    have e00 : (dg2 s s⁻¹ : GL (Fin 2) F).val 0 0 = a := by simp [dg2, hs]
    have e01 : (dg2 s s⁻¹ : GL (Fin 2) F).val 0 1 = 0 := by simp [dg2]
    have e10 : (dg2 s s⁻¹ : GL (Fin 2) F).val 1 0 = 0 := by simp [dg2]
    rw [e00, e01, e10, rW_zero, hma, ← hNt, nsg_norm, hNt]
    have : Φ (algebraMap F E a * z) = Φ z := by
      rw [← hra, map_mul, mul_comm, ← mul_assoc, hrd, hrd]
    simp [this]
  have hmem := mem_nhds_of_factors H hUp hLow hD hM
  have hcont' : ContinuousAt (fun g : GL (Fin 2) F => g₀⁻¹ * g) g₀ :=
    (continuous_const.mul continuous_id).continuousAt
  refine ⟨(fun g : GL (Fin 2) F => g₀⁻¹ * g) ⁻¹' (H : Set (GL (Fin 2) F)),
    hcont'.preimage_mem_nhds (by simpa using hmem), fun g hg => ?_⟩
  obtain ⟨hx, he⟩ := (hH _).1 hg
  calc piE E χ σ η c g Φ = piE E χ σ η c (g₀ * (g₀⁻¹ * g)) Φ := by rw [mul_inv_cancel_left]
    _ = piE E χ σ η c g₀ (piE E χ σ η c (g₀⁻¹ * g) Φ) := hmul _ _ hg₀ hx
    _ = piE E χ σ η c g₀ Φ := by rw [he]

end GlobalTheory.CompanionTheory.WeilLocConst
