import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix MeasureTheory
open scoped ComplexOrder Pointwise

namespace Formalism.IndefR.Fock.Skew

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ.1.2.1 a]`. Simplify using the standard rewrite rules.
-/
theorem psi_mul_conj {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) :
    ψ a * starRingEnd ℂ (ψ a) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ.1.2.1 a]
  simp

/- English proof (translation)
Take `⟨e, he⟩` from `γ.2`. Establish `hγ : γ +ᵥ w = ratW T S e + w` using `by show (γ : WO S T) + w = _`. Rewrite using `[← he]`. Both sides reduce to the same expression. Rewrite using `[hγ, hf.quasi, hg.quasi, map_mul]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem prod_inv {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) (γ : ratL T S) (w : WO S T) :
    f (γ +ᵥ w) * starRingEnd ℂ (g (γ +ᵥ w)) = f w * starRingEnd ℂ (g w) := by
  obtain ⟨e, he⟩ := γ.2
  have hγ : γ +ᵥ w = ratW T S e + w := by
    show (γ : WO S T) + w = _
    rw [← he]
    rfl
  rw [hγ, hf.quasi, hg.quasi, map_mul]
  calc _ = (ψ (-(symplOH S T (ratW T S e) w)) * starRingEnd ℂ (ψ (-(symplOH S T (ratW T S e) w)))) *
        (f w * starRingEnd ℂ (g w)) := by ring
    _ = _ := by rw [psi_mul_conj hψ]; ring

/- English proof (translation)
Take `⟨K, hK, hsub⟩` from `Formalism.IndefR.PHeisFC.FD_sub_compact T S`. Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn hc.continuousOn`. Use `⟨C, fun x => ?_⟩` and prove the remaining obligations. Take `⟨γ, hγ, -⟩` from `Formalism.IndefR.PHeisFC.exU T S x`. Rewrite using `[← hinv γ x]`.

Conclude with `hC _ (hsub hγ)`.
-/
theorem bdd_of_inv {S T : HSp D} (F : WO S T → ℂ) (hc : Continuous F) (hinv : ∀ (γ : ratL T S) w, F (γ +ᵥ w) = F w) :
    ∃ C, ∀ x, ‖F x‖ ≤ C := by
  obtain ⟨K, hK, hsub⟩ := Formalism.IndefR.PHeisFC.FD_sub_compact T S
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun x => ?_⟩
  obtain ⟨γ, hγ, -⟩ := Formalism.IndefR.PHeisFC.exU T S x
  rw [← hinv γ x]
  exact hC _ (hsub hγ)

/- English proof (translation)
Use `Formalism.IndefR.PHeisFC.countable_ratL T S` as an intermediate fact. Establish `: MeasurableConstVAdd (ratL T S) (WO S T)` using `⟨fun c => (continuous_const.add continuous_id).measurable⟩`. Establish `: VAddInvariantMeasure (ratL T S) (WO S T) μ` using `⟨fun c s _ => measure_preimage_add μ (c : WO S T) s⟩`. Establish `: MeasurableConstVAdd (WO S T) (WO S T)` using `⟨fun c => (continuous_const.add continuous_id).measurable⟩`. Establish `: VAddInvariantMeasure (WO S T) (WO S T) μ` using `⟨fun c s _ => measure_preimage_add μ c s⟩`.

Establish `: VAddCommClass (WO S T) (ratL T S) (WO S T)` using `⟨fun a γ x => by show a + ((γ : WO S T) + x) = (γ : WO S T) + (a + x) abel⟩`. Establish `h𝓕' : IsAddFundamentalDomain (ratL T S) (v +ᵥ 𝓕) μ` using `h𝓕.vadd_of_comm v`. Establish `hemb : MeasurableEmbedding (fun w : WO S T => v + w)` using `(Homeomorph.addLeft v).measurableEmbedding`. Establish `hpre : (fun w : WO S T => v + w) ⁻¹' (v +ᵥ 𝓕) = 𝓕`. Use extensionality with `w`.

Simplify using `[Set.mem_vadd_set_iff_neg_vadd_mem]`. Establish `key` using `(measurePreserving_add_left μ v).setIntegral_preimage_emb hemb F (v +ᵥ 𝓕)`. Rewrite `key` using `[hpre]`. Rewrite using `[key]`. Conclude with `h𝓕'.setIntegral_eq h𝓕 hinv`.
-/
theorem integral_translate {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) [μ.IsAddHaarMeasure]
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) (F : WO S T → ℂ)
    (hinv : ∀ (γ : ratL T S) w, F (γ +ᵥ w) = F w) (v : WO S T) :
    ∫ w in 𝓕, F (v + w) ∂μ = ∫ w in 𝓕, F w ∂μ := by
  have := Formalism.IndefR.PHeisFC.countable_ratL T S
  have : MeasurableConstVAdd (ratL T S) (WO S T) :=
    ⟨fun c => (continuous_const.add continuous_id).measurable⟩
  have : VAddInvariantMeasure (ratL T S) (WO S T) μ :=
    ⟨fun c s _ => measure_preimage_add μ (c : WO S T) s⟩
  have : MeasurableConstVAdd (WO S T) (WO S T) :=
    ⟨fun c => (continuous_const.add continuous_id).measurable⟩
  have : VAddInvariantMeasure (WO S T) (WO S T) μ :=
    ⟨fun c s _ => measure_preimage_add μ c s⟩
  have : VAddCommClass (WO S T) (ratL T S) (WO S T) :=
    ⟨fun a γ x => by
      show a + ((γ : WO S T) + x) = (γ : WO S T) + (a + x)
      abel⟩
  have h𝓕' : IsAddFundamentalDomain (ratL T S) (v +ᵥ 𝓕) μ := h𝓕.vadd_of_comm v
  have hemb : MeasurableEmbedding (fun w : WO S T => v + w) := (Homeomorph.addLeft v).measurableEmbedding
  have hpre : (fun w : WO S T => v + w) ⁻¹' (v +ᵥ 𝓕) = 𝓕 := by
    ext w
    simp [Set.mem_vadd_set_iff_neg_vadd_mem]
  have key := (measurePreserving_add_left μ v).setIntegral_preimage_emb hemb F (v +ᵥ 𝓕)
  rw [hpre] at key
  rw [key]
  exact h𝓕'.setIntegral_eq h𝓕 hinv

/- English proof (translation)
Unfold `heisO`. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [psi_mul_conj hψ]; ring`.
-/
theorem heis_mul_conj {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} (f g : WO S T → ℂ)
    (v w : WO S T) :
    heisO ψ S T v f w * starRingEnd ℂ (heisO ψ S T v g w) = f (w + v) * starRingEnd ℂ (g (w + v)) := by
  unfold heisO
  rw [map_mul]
  calc _ = (ψ (symplOH S T w v) * starRingEnd ℂ (ψ (symplOH S T w v))) * (f (w + v) * starRingEnd ℂ (g (w + v))) := by
        ring
    _ = _ := by rw [psi_mul_conj hψ]; ring

/- English proof (translation)
Unfold `heisO symplOH symplO hO`. Simplify using the standard rewrite rules.
-/
theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (f : WO S T → ℂ) (w : WO S T) :
    heisO ψ S T 0 f w = f w := by
  unfold heisO symplOH symplO hO
  simp

/- English proof (translation)
Take `⟨G, hG⟩ : ∃ G : WO S T → ℂ, G = fun w => f w * starRingEnd ℂ (g w)` from `⟨_, rfl⟩`. Take `⟨H, hH⟩ : ∃ H : WO S T → ℂ, H = fun w => df w * starRingEnd ℂ (g w) + f w * starRingEnd ℂ (dg w)` from `⟨_, rfl⟩`. Establish `hcc : Continuous (starRingEnd ℂ)` using `Complex.continuous_conj`. Establish `hGc : Continuous G` using `by rw [hG]; exact hf.cont.mul (hcc.comp hg.cont)`. Establish `hH1c : Continuous fun w => df w * starRingEnd ℂ (g w)` using `hdf.cont.mul (hcc.comp hg.cont)`.

Establish `hH2c : Continuous fun w => f w * starRingEnd ℂ (dg w)` using `hf.cont.mul (hcc.comp hdg.cont)`. Establish `hHc : Continuous H` using `by rw [hH]; exact hH1c.add hH2c`. Establish `hGi : ∀ (γ : ratL T S) w, G (γ +ᵥ w) = G w` using `by rw [hG]; exact prod_inv hstd hf hg`. Establish `hH1i : ∀ (γ : ratL T S) w, df (γ +ᵥ w) * starRingEnd ℂ (g (γ +ᵥ w)) = df w * starRingEnd ℂ (g w)` using `prod_inv hstd hdf hg`. Establish `hH2i : ∀ (γ : ratL T S) w, f (γ +ᵥ w) * starRingEnd ℂ (dg (γ +ᵥ w)) = f w * starRingEnd ℂ (dg w)` using `prod_inv hstd hf hdg`.

Establish `hHi : ∀ (γ : ratL T S) w, H (γ +ᵥ w) = H w` using `fun γ w => by`. Rewrite using `[hH]`. Simplify using `only`. Rewrite using `[hH1i, hH2i]`. Take `⟨CG, hCG⟩` from `bdd_of_inv G hGc hGi`.

Take `⟨CH, hCH⟩` from `bdd_of_inv H hHc hHi`. Take `⟨C1, hC1⟩` from `bdd_of_inv _ hH1c hH1i`. Take `⟨C2, hC2⟩` from `bdd_of_inv _ hH2c hH2i`. Establish `hd0 : ∀ w, HasDerivAt (fun t : ℝ => G (w + L t)) (H w) 0`. Introduce `w`.

Establish `hp : HasDerivAt (fun t : ℝ => heisO ψ S T (L t) f w * star (heisO ψ S T (L t) g w)) (df w * star (heisO ψ S T (L 0) g w) + heisO ψ S T (L 0) f w * star (dg w)) 0` using `(hderf w).mul (hderg w).star`. Establish `e1 : (fun t : ℝ => heisO ψ S T (L t) f w * star (heisO ψ S T (L t) g w)) = fun t => G (w + L t)`. Use function extensionality and compare the values at `t`. Rewrite using `[← starRingEnd_apply, heis_mul_conj hstd, hG]`. Establish `e2 : df w * star (heisO ψ S T (L 0) g w) + heisO ψ S T (L 0) f w * star (dg w) = H w`.

Rewrite using `[map_zero, heisO_zero, heisO_zero, hH, ← starRingEnd_apply, ← starRingEnd_apply]`. Rewrite `hp` using `[e1, e2]`. Conclude with `hp`. Establish `hdt : ∀ w (t : ℝ), HasDerivAt (fun s : ℝ => G (w + L s)) (H (w + L t)) t`. Introduce `w t`.

Establish `h0 : HasDerivAt (fun s : ℝ => G (w + L t + L s)) (H (w + L t)) (t - t)`. Rewrite using `[sub_self]`. Conclude with `hd0 (w + L t)`. Establish `h2` using `h0.comp_sub_const t t`. Establish `e : (fun s : ℝ => G (w + L s)) = fun s => G (w + L t + L (s - t))`.

Use function extensionality and compare the values at `s`. Rewrite using `[add_assoc, ← map_add, add_sub_cancel]`. Rewrite using `[e]`. Conclude with `h2`. Establish `hfin : IsFiniteMeasure (μ.restrict 𝓕)` using `isFiniteMeasure_restrict.2 (by rw [h1]; simp)`.

Establish `hint : ∀ (F : WO S T → ℂ) (C : ℝ), Continuous F → (∀ x, ‖F x‖ ≤ C) → Integrable F (μ.restrict 𝓕)` using `fun F C hc hb => Integrable.of_bound hc.aestronglyMeasurable C (ae_of_all _ hb)`. Establish `hsh : ∀ t : ℝ, Continuous fun w : WO S T => w + L t` using `fun t => continuous_id.add continuous_const`. Establish `hmain` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (x₀ := (0 : ℝ)) (F := fun (t : ℝ) w => G (w + L t)) (F' := fun (t : ℝ) w => H (w + L t)) (bound := fun _ => CH) (s := Set.univ) Filter.univ_mem (Filter.Eventually.of_forall fun t => (hGc.comp (hsh t)).aestrongly …`. Establish `hconst : (fun t : ℝ => ∫ w in 𝓕, G (w + L t) ∂μ) = fun _ => ∫ w in 𝓕, G w ∂μ`. Use function extensionality and compare the values at `t`.

Rewrite using `[← integral_translate μ 𝓕 h𝓕 G hGi (L t)]`. Use `congr 1`. Use function extensionality and compare the values at `w`. Rewrite using `[add_comm]`. Establish `hzero : ∫ w in 𝓕, H (w + L 0) ∂μ = 0`.

Establish `h` using `hmain.2`. Rewrite `h` using `[hconst]`. Conclude with `h.unique (hasDerivAt_const _ _)`. Rewrite `hzero` using `[map_zero]`. Simplify using `only [add_zero] at hzero`.

Rewrite `hzero` using `[hH]`. Rewrite `hzero` using `[integral_add (hint _ C1 hH1c hC1) (hint _ C2 hH2c hC2)]`. Conclude with `eq_neg_of_add_eq_zero_left hzero`.
-/
theorem skew_core {ψ : AddChar (AF D.host.F) ℂ} (hstd : IsStdChar D ψ (-1)) {S T : HSp D} (μ : Measure (WO S T))
    (𝓕 : Set (WO S T)) [μ.IsAddHaarMeasure] (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) (h1 : μ 𝓕 = 1)
    (L : ℝ →+ WO S T) (f g df dg : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g)
    (hdf : IsThetaFunO ψ S T df) (hdg : IsThetaFunO ψ S T dg)
    (hderf : ∀ x, HasDerivAt (fun t : ℝ => heisO ψ S T (L t) f x) (df x) 0)
    (hderg : ∀ x, HasDerivAt (fun t : ℝ => heisO ψ S T (L t) g x) (dg x) 0) :
    ∫ w in 𝓕, df w * starRingEnd ℂ (g w) ∂μ = -∫ w in 𝓕, f w * starRingEnd ℂ (dg w) ∂μ := by
  obtain ⟨G, hG⟩ : ∃ G : WO S T → ℂ, G = fun w => f w * starRingEnd ℂ (g w) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : WO S T → ℂ, H = fun w => df w * starRingEnd ℂ (g w) + f w * starRingEnd ℂ (dg w) :=
    ⟨_, rfl⟩
  have hcc : Continuous (starRingEnd ℂ) := Complex.continuous_conj
  have hGc : Continuous G := by rw [hG]; exact hf.cont.mul (hcc.comp hg.cont)
  have hH1c : Continuous fun w => df w * starRingEnd ℂ (g w) := hdf.cont.mul (hcc.comp hg.cont)
  have hH2c : Continuous fun w => f w * starRingEnd ℂ (dg w) := hf.cont.mul (hcc.comp hdg.cont)
  have hHc : Continuous H := by rw [hH]; exact hH1c.add hH2c
  have hGi : ∀ (γ : ratL T S) w, G (γ +ᵥ w) = G w := by rw [hG]; exact prod_inv hstd hf hg
  have hH1i : ∀ (γ : ratL T S) w, df (γ +ᵥ w) * starRingEnd ℂ (g (γ +ᵥ w)) = df w * starRingEnd ℂ (g w) :=
    prod_inv hstd hdf hg
  have hH2i : ∀ (γ : ratL T S) w, f (γ +ᵥ w) * starRingEnd ℂ (dg (γ +ᵥ w)) = f w * starRingEnd ℂ (dg w) :=
    prod_inv hstd hf hdg
  have hHi : ∀ (γ : ratL T S) w, H (γ +ᵥ w) = H w := fun γ w => by
    rw [hH]; simp only; rw [hH1i, hH2i]
  obtain ⟨CG, hCG⟩ := bdd_of_inv G hGc hGi
  obtain ⟨CH, hCH⟩ := bdd_of_inv H hHc hHi
  obtain ⟨C1, hC1⟩ := bdd_of_inv _ hH1c hH1i
  obtain ⟨C2, hC2⟩ := bdd_of_inv _ hH2c hH2i

  have hd0 : ∀ w, HasDerivAt (fun t : ℝ => G (w + L t)) (H w) 0 := by
    intro w
    have hp : HasDerivAt (fun t : ℝ => heisO ψ S T (L t) f w * star (heisO ψ S T (L t) g w))
        (df w * star (heisO ψ S T (L 0) g w) + heisO ψ S T (L 0) f w * star (dg w)) 0 :=
      (hderf w).mul (hderg w).star
    have e1 : (fun t : ℝ => heisO ψ S T (L t) f w * star (heisO ψ S T (L t) g w)) = fun t => G (w + L t) := by
      funext t
      rw [← starRingEnd_apply, heis_mul_conj hstd, hG]
    have e2 : df w * star (heisO ψ S T (L 0) g w) + heisO ψ S T (L 0) f w * star (dg w) = H w := by
      rw [map_zero, heisO_zero, heisO_zero, hH, ← starRingEnd_apply, ← starRingEnd_apply]
    rw [e1, e2] at hp
    exact hp
  have hdt : ∀ w (t : ℝ), HasDerivAt (fun s : ℝ => G (w + L s)) (H (w + L t)) t := by
    intro w t
    have h0 : HasDerivAt (fun s : ℝ => G (w + L t + L s)) (H (w + L t)) (t - t) := by
      rw [sub_self]; exact hd0 (w + L t)
    have h2 := h0.comp_sub_const t t
    have e : (fun s : ℝ => G (w + L s)) = fun s => G (w + L t + L (s - t)) := by
      funext s
      rw [add_assoc, ← map_add, add_sub_cancel]
    rw [e]
    exact h2

  have hfin : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (by rw [h1]; simp)
  have hint : ∀ (F : WO S T → ℂ) (C : ℝ), Continuous F → (∀ x, ‖F x‖ ≤ C) → Integrable F (μ.restrict 𝓕) :=
    fun F C hc hb => Integrable.of_bound hc.aestronglyMeasurable C (ae_of_all _ hb)
  have hsh : ∀ t : ℝ, Continuous fun w : WO S T => w + L t := fun t => continuous_id.add continuous_const

  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (x₀ := (0 : ℝ))
    (F := fun (t : ℝ) w => G (w + L t)) (F' := fun (t : ℝ) w => H (w + L t)) (bound := fun _ => CH)
    (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => (hGc.comp (hsh t)).aestronglyMeasurable)
    (hint _ CG (hGc.comp (hsh 0)) fun x => hCG _)
    ((hHc.comp (hsh 0)).aestronglyMeasurable)
    (ae_of_all _ fun w t _ => hCH _) (integrable_const CH)
    (ae_of_all _ fun w t _ => hdt w t)
  have hconst : (fun t : ℝ => ∫ w in 𝓕, G (w + L t) ∂μ) = fun _ => ∫ w in 𝓕, G w ∂μ := by
    funext t
    rw [← integral_translate μ 𝓕 h𝓕 G hGi (L t)]
    congr 1
    funext w
    rw [add_comm]
  have hzero : ∫ w in 𝓕, H (w + L 0) ∂μ = 0 := by
    have h := hmain.2
    rw [hconst] at h
    exact h.unique (hasDerivAt_const _ _)
  rw [map_zero] at hzero
  simp only [add_zero] at hzero
  rw [hH] at hzero
  rw [integral_add (hint _ C1 hH1c hC1) (hint _ C2 hH2c hC2)] at hzero
  exact eq_neg_of_add_eq_zero_left hzero

/- English proof (translation)
Introduce `ψ θ hstd hinf hline S T τ z μ 𝓕 hcov f g hf hg`. Take `⟨hdf, hderf⟩` from `hT ψ θ hstd hinf hline S T τ z f hf`. Take `⟨hdg, hderg⟩` from `hT ψ θ hstd hinf hline S T τ z g hg`. Take `⟨hHaar, h𝓕, h1⟩` from `hcov`. Conclude with `skew_core hstd μ 𝓕 h𝓕 h1 (lineAt θ τ z) f g _ _ hf hg hdf hdg hderf hderg`.
-/
theorem dRhoSkew_of (D : D7) (hT : Formalism.IndefR.Fock.Sk.ThetaDRho D) : Formalism.IndefR.Fock.Sk.DRhoSkew D := by
  intro ψ θ hstd hinf hline S T τ z μ 𝓕 hcov f g hf hg
  obtain ⟨hdf, hderf⟩ := hT ψ θ hstd hinf hline S T τ z f hf
  obtain ⟨hdg, hderg⟩ := hT ψ θ hstd hinf hline S T τ z g hg
  obtain ⟨hHaar, h𝓕, h1⟩ := hcov
  exact skew_core hstd μ 𝓕 h𝓕 h1 (lineAt θ τ z) f g _ _ hf hg hdf hdg hderf hderg

/- English proof (translation)
Introduce `ψ hstd S T μ 𝓕 hcov f g hf hg`. Take `⟨hHaar, h𝓕, h1⟩` from `hcov`. Establish `hc : Continuous fun w => f w * starRingEnd ℂ (g w)` using `hf.cont.mul (Complex.continuous_conj.comp hg.cont)`. Take `⟨C, hC⟩` from `bdd_of_inv _ hc (prod_inv hstd hf hg)`. Establish `hfin : IsFiniteMeasure (μ.restrict 𝓕)` using `isFiniteMeasure_restrict.2 (by rw [h1]; simp)`.

Conclude with `Integrable.of_bound hc.aestronglyMeasurable C (ae_of_all _ hC)`.
-/
theorem thetaIntO (D : D7) : Formalism.IndefR.Fock.Sk.ThetaIntO D := by
  intro ψ hstd S T μ 𝓕 hcov f g hf hg
  obtain ⟨hHaar, h𝓕, h1⟩ := hcov
  have hc : Continuous fun w => f w * starRingEnd ℂ (g w) := hf.cont.mul (Complex.continuous_conj.comp hg.cont)
  obtain ⟨C, hC⟩ := bdd_of_inv _ hc (prod_inv hstd hf hg)
  have hfin : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (by rw [h1]; simp)
  exact Integrable.of_bound hc.aestronglyMeasurable C (ae_of_all _ hC)

end Formalism.IndefR.Fock.Skew

end
