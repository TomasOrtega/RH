import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairRApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTranslationSeminormBound

noncomputable section

open Filter Topology
open scoped SchwartzMap

namespace GlobalTheory.SchrPairing

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def pairCLM {P : V → V → ℝ} (hP : GlobalTheory.ArchUniq.IsPairing P) : V →L[ℝ] (V →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := pairR hP
      map_add' := fun b b' => by ext y; simp [pairR_apply, hP.addR]
      map_smul' := fun c b => by ext y; simp [pairR_apply, hP.smulR] }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pairCLM_apply {P : V → V → ℝ} (hP : GlobalTheory.ArchUniq.IsPairing P) (b : V) : pairCLM hP b = pairR hP b := rfl

/- English proof (translation)
The claim follows from `((pairCLM hP).continuous.comp continuous_snd).clm_apply continuous_fst`.
-/
theorem continuous_pair {P : V → V → ℝ} (hP : GlobalTheory.ArchUniq.IsPairing P) :
    Continuous fun x : V × V => P x.1 x.2 :=
  ((pairCLM hP).continuous.comp continuous_snd).clm_apply continuous_fst

/- English proof (translation)
Rewrite using `[(schwartz_withSeminorms ℂ V ℂ).tendsto_nhds _ g]`. Introduce `i ε hε`. Take `⟨q₁, M₁, hq₁, hb₁⟩` from `GlobalTheory.PhaseLipschitz.seminorm_smulLeft_eChar_sub_le V (schwartzSeminormFamily ℂ V ℂ i) ((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i)`. Take `⟨q₂, M₂, -, hb₂⟩` from `GlobalTheory.SchwartzTranslateLip.translate_sub_le V (schwartzSeminormFamily ℂ V ℂ i) ((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i)`. Take `⟨q₃, M₃, -, hb₃⟩` from `GlobalTheory.SchwartzTranslateLip.translate_sub_le V q₁ hq₁`.

Use `set p := schwartzSeminormFamily ℂ V ℂ i with hp`. Establish `key : ∀ u : V × V, p (schrSch hP u g - g) ≤ (‖pairR hP u.2‖ + |P u.1 u.2 / 2|) * (1 + ‖pairR hP u.2‖) ^ M₁ * (‖u.1‖ * (1 + ‖u.1‖) ^ M₃ * q₃ g + q₁ g) + ‖u.1‖ * (1 + ‖u.1‖) ^ M₂ * q₂ g`. Introduce `u`. Use `set T := SchwartzMap.compSubConstCLM ℂ (-u.1) g with hT`. Establish `h1` using `map_add_le_add p (SchwartzMap.smulLeftCLM ℂ (fun y => GlobalTheory.Published.Metaplectic.eChar ((-pairR hP u.2) y + -(P u.1 u.2 / 2))) T - T) (T - g)`.

Rewrite `h1` using `[sub_add_sub_cancel]`. Establish `e : schrSch hP u g = SchwartzMap.smulLeftCLM ℂ (fun y => GlobalTheory.Published.Metaplectic.eChar ((-pairR hP u.2) y + -(P u.1 u.2 / 2))) T` using `rfl`. Rewrite using `[e]`. Use `le_trans h1 (add_le_add ((hb₁ _ _ T).trans ?_) (hb₂ _ g))` and prove the remaining obligations. Rewrite using `[norm_neg, abs_neg]`.

Establish `h2` using `map_add_le_add q₁ (T - g) g`. Rewrite `h2` using `[sub_add_cancel]`. Establish `h3` using `hb₃ u.1 g`. Use `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1c : Tendsto (fun u : V × V => u.1) (𝓝 0) (𝓝 0)` using `continuous_fst.tendsto' _ _ rfl`. Establish `h1n : Tendsto (fun u : V × V => ‖u.1‖) (𝓝 0) (𝓝 0)` using `by simpa using h1c.norm`. Establish `hLc : Tendsto (fun u : V × V => pairCLM hP u.2) (𝓝 0) (𝓝 0)` using `((pairCLM hP).continuous.comp continuous_snd).tendsto' _ _ (by simp)`. Establish `hLn : Tendsto (fun u : V × V => ‖pairR hP u.2‖) (𝓝 0) (𝓝 0)` using `by simpa [pairCLM_apply] using hLc.norm`. Establish `hk : Tendsto (fun u : V × V => |P u.1 u.2 / 2|) (𝓝 0) (𝓝 0)`.

Establish `h0 : P 0 0 = 0` using `hP.zero_left 0`. Use `(((continuous_pair hP).tendsto (0 : V × V)).div_const 2).abs` as an intermediate fact. Simplify `this` using `[h0]`. Establish `lim : Tendsto (fun u : V × V => (‖pairR hP u.2‖ + |P u.1 u.2 / 2|) * (1 + ‖pairR hP u.2‖) ^ M₁ * (‖u.1‖ * (1 + ‖u.1‖) ^ M₃ * q₃ g + q₁ g) + ‖u.1‖ * (1 + ‖u.1‖) ^ M₂ * q₂ g) (𝓝 0) (𝓝 0)`. Use `(((hLn.add hk).mul ((hLn.const_add 1).pow M₁)).mul (((h1n.mul ((h1n.const_add 1).pow M₃)).mul_const (q₃ g)).add_const (q₁ g))).add ((h1n.mul ((h1n.const_add 1).pow M₂)).mul_const (q₂ g))` as an intermediate fact.

Simplify using `using this`. Use `filter_upwards [lim.eventually (gt_mem_nhds hε)] with u hu`. Conclude with `(key u).trans_lt hu`.
-/
theorem tendsto_schrSch_zero {P : V → V → ℝ} (hP : GlobalTheory.ArchUniq.IsPairing P) (g : 𝓢(V, ℂ)) :
    Tendsto (fun u : V × V => schrSch hP u g) (𝓝 0) (𝓝 g) := by
  rw [(schwartz_withSeminorms ℂ V ℂ).tendsto_nhds _ g]
  intro i ε hε
  obtain ⟨q₁, M₁, hq₁, hb₁⟩ := GlobalTheory.PhaseLipschitz.seminorm_smulLeft_eChar_sub_le V
    (schwartzSeminormFamily ℂ V ℂ i) ((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i)
  obtain ⟨q₂, M₂, -, hb₂⟩ := GlobalTheory.SchwartzTranslateLip.translate_sub_le V
    (schwartzSeminormFamily ℂ V ℂ i) ((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i)
  obtain ⟨q₃, M₃, -, hb₃⟩ := GlobalTheory.SchwartzTranslateLip.translate_sub_le V q₁ hq₁
  set p := schwartzSeminormFamily ℂ V ℂ i with hp
  have key : ∀ u : V × V, p (schrSch hP u g - g) ≤
      (‖pairR hP u.2‖ + |P u.1 u.2 / 2|) * (1 + ‖pairR hP u.2‖) ^ M₁ *
          (‖u.1‖ * (1 + ‖u.1‖) ^ M₃ * q₃ g + q₁ g) + ‖u.1‖ * (1 + ‖u.1‖) ^ M₂ * q₂ g := by
    intro u
    set T := SchwartzMap.compSubConstCLM ℂ (-u.1) g with hT
    have h1 := map_add_le_add p (SchwartzMap.smulLeftCLM ℂ
      (fun y => GlobalTheory.Published.Metaplectic.eChar ((-pairR hP u.2) y + -(P u.1 u.2 / 2))) T - T) (T - g)
    rw [sub_add_sub_cancel] at h1
    have e : schrSch hP u g = SchwartzMap.smulLeftCLM ℂ
      (fun y => GlobalTheory.Published.Metaplectic.eChar ((-pairR hP u.2) y + -(P u.1 u.2 / 2))) T := rfl
    rw [e]
    refine le_trans h1 (add_le_add ((hb₁ _ _ T).trans ?_) (hb₂ _ g))
    rw [norm_neg, abs_neg]
    have h2 := map_add_le_add q₁ (T - g) g
    rw [sub_add_cancel] at h2
    have h3 := hb₃ u.1 g
    gcongr
    linarith
  have h1c : Tendsto (fun u : V × V => u.1) (𝓝 0) (𝓝 0) := continuous_fst.tendsto' _ _ rfl
  have h1n : Tendsto (fun u : V × V => ‖u.1‖) (𝓝 0) (𝓝 0) := by simpa using h1c.norm
  have hLc : Tendsto (fun u : V × V => pairCLM hP u.2) (𝓝 0) (𝓝 0) :=
    ((pairCLM hP).continuous.comp continuous_snd).tendsto' _ _ (by simp)
  have hLn : Tendsto (fun u : V × V => ‖pairR hP u.2‖) (𝓝 0) (𝓝 0) := by simpa [pairCLM_apply] using hLc.norm
  have hk : Tendsto (fun u : V × V => |P u.1 u.2 / 2|) (𝓝 0) (𝓝 0) := by
    have h0 : P 0 0 = 0 := hP.zero_left 0
    have := (((continuous_pair hP).tendsto (0 : V × V)).div_const 2).abs
    simpa [h0] using this
  have lim : Tendsto (fun u : V × V => (‖pairR hP u.2‖ + |P u.1 u.2 / 2|) * (1 + ‖pairR hP u.2‖) ^ M₁ *
          (‖u.1‖ * (1 + ‖u.1‖) ^ M₃ * q₃ g + q₁ g) + ‖u.1‖ * (1 + ‖u.1‖) ^ M₂ * q₂ g)
      (𝓝 0) (𝓝 0) := by
    have := (((hLn.add hk).mul ((hLn.const_add 1).pow M₁)).mul
      (((h1n.mul ((h1n.const_add 1).pow M₃)).mul_const (q₃ g)).add_const (q₁ g))).add
      ((h1n.mul ((h1n.const_add 1).pow M₂)).mul_const (q₂ g))
    simpa using this
  filter_upwards [lim.eventually (gt_mem_nhds hε)] with u hu
  exact (key u).trans_lt hu

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[SchwartzMap.smul_apply, coe_schrSch, coe_schrSch, coe_schrSch]`. Simplify using `only [GlobalTheory.ArchUniq.schrF, Prod.fst_add, Prod.snd_add, hP.addL, hP.addR, smul_eq_mul, add_assoc]`. Rewrite using `[← mul_assoc, ← Complex.exp_add, ← mul_assoc, ← Complex.exp_add]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem schrSch_schrSch {P : V → V → ℝ} (hP : GlobalTheory.ArchUniq.IsPairing P) (w₀ u : V × V) (g : 𝓢(V, ℂ)) :
    schrSch hP w₀ (schrSch hP u g) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (((P w₀.1 u.2 - P u.1 w₀.2) / 2 : ℝ) : ℂ)) •
        schrSch hP (w₀ + u) g := by
  ext y
  rw [SchwartzMap.smul_apply, coe_schrSch, coe_schrSch, coe_schrSch]
  simp only [GlobalTheory.ArchUniq.schrF, Prod.fst_add, Prod.snd_add, hP.addL, hP.addR, smul_eq_mul, add_assoc]
  rw [← mul_assoc, ← Complex.exp_add, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/- English proof (translation)
Introduce `V _ _ _ P hP f`. Use `continuous_iff_continuousAt.2 fun w₀ => ?_` and prove the remaining obligations. Use `set c : V × V → ℂ := fun u => Complex.exp (-(2 * Real.pi * Complex.I) * (((P w₀.1 u.2 - P u.1 w₀.2) / 2 : ℝ) : ℂ)) with hcdef`. Establish `hs : Continuous fun u : V × V => P w₀.1 u.2 - P u.1 w₀.2` using `((continuous_pair hP).comp (continuous_const.prodMk continuous_snd)).sub ((continuous_pair hP).comp (continuous_fst.prodMk continuous_const))`. Establish `hc : Continuous c`.

Rewrite using `[hcdef]`. Use `fun_prop`. Establish `h1 : Tendsto (fun u => (c u)⁻¹ • schrSch hP w₀ (schrSch hP u f)) (𝓝 0) (𝓝 ((c 0)⁻¹ • schrSch hP w₀ f))` using `((hc.tendsto 0).inv₀ (Complex.exp_ne_zero _)).smul (((schrSch hP w₀).continuous.tendsto f).comp (tendsto_schrSch_zero hP f))`. Establish `hc0 : c 0 = 1`. Simplify using `[hcdef, GlobalTheory.ArchUniq.IsPairing.zero_left hP, GlobalTheory.ArchUniq.IsPairing.zero_right hP]`.

Establish `e : ∀ u, (c u)⁻¹ • schrSch hP w₀ (schrSch hP u f) = schrSch hP (w₀ + u) f` using `fun u => by`. Rewrite using `[schrSch_schrSch, inv_smul_smul₀ (Complex.exp_ne_zero _)]`. Simplify using `only [e, hc0, inv_one, one_smul] at h1`. Establish `h3 : Tendsto (fun w => w - w₀) (𝓝 w₀) (𝓝 0)` using `(continuous_sub_right w₀).tendsto' _ _ (sub_self _)`. Use `(h1.comp h3).congr fun w => ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules.
-/
theorem continuous_schrSch : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {P : V → V → ℝ} (hP : GlobalTheory.ArchUniq.IsPairing P) (f : 𝓢(V, ℂ)),
    Continuous fun w : V × V => GlobalTheory.SchrPairing.schrSch hP w f := by
  intro V _ _ _ P hP f
  refine continuous_iff_continuousAt.2 fun w₀ => ?_
  set c : V × V → ℂ := fun u =>
    Complex.exp (-(2 * Real.pi * Complex.I) * (((P w₀.1 u.2 - P u.1 w₀.2) / 2 : ℝ) : ℂ)) with hcdef
  have hs : Continuous fun u : V × V => P w₀.1 u.2 - P u.1 w₀.2 :=
    ((continuous_pair hP).comp (continuous_const.prodMk continuous_snd)).sub
      ((continuous_pair hP).comp (continuous_fst.prodMk continuous_const))
  have hc : Continuous c := by
    rw [hcdef]
    fun_prop
  have h1 : Tendsto (fun u => (c u)⁻¹ • schrSch hP w₀ (schrSch hP u f)) (𝓝 0)
      (𝓝 ((c 0)⁻¹ • schrSch hP w₀ f)) :=
    ((hc.tendsto 0).inv₀ (Complex.exp_ne_zero _)).smul
      (((schrSch hP w₀).continuous.tendsto f).comp (tendsto_schrSch_zero hP f))
  have hc0 : c 0 = 1 := by
    simp [hcdef, GlobalTheory.ArchUniq.IsPairing.zero_left hP, GlobalTheory.ArchUniq.IsPairing.zero_right hP]
  have e : ∀ u, (c u)⁻¹ • schrSch hP w₀ (schrSch hP u f) = schrSch hP (w₀ + u) f := fun u => by
    rw [schrSch_schrSch, inv_smul_smul₀ (Complex.exp_ne_zero _)]
  simp only [e, hc0, inv_one, one_smul] at h1
  have h3 : Tendsto (fun w => w - w₀) (𝓝 w₀) (𝓝 0) := (continuous_sub_right w₀).tendsto' _ _ (sub_self _)
  refine (h1.comp h3).congr fun w => ?_
  simp

end GlobalTheory.SchrPairing
