import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SzLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLContinuousStatement
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Iwa
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ContinuousPrN

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

/- English proof (translation)
Use `set R : Set (Fin 4 → ℚ) := {ξ | ξ ≠ 0 ∧ qr δ ξ = 0}`. Use `set Q : Set (Fin 4 → ℚ) := {ξ | qr δ ξ ≠ 0}`. Establish `h0 : qr δ 0 = 0` using `by simp [qr]`. Establish `hpt : ∀ ξ, f ξ = (({0} : Set (Fin 4 → ℚ)).indicator f ξ + R.indicator f ξ) + Q.indicator f ξ`. Introduce `ξ`.

Distinguish the cases in `hq : qr δ ξ = 0`. Distinguish the cases in `hξ : ξ = 0`. Substitute `hξ` using the available equality. Simplify using `[R, Q, h0]`. Simplify using `[R, Q, hξ, hq]`.

Establish `hξ : ξ ≠ 0` using `fun e => hq (e ▸ h0)`. Simplify using `[R, Q, hξ, hq]`. Establish `s0` using `hf.indicator ({0} : Set (Fin 4 → ℚ))`. Establish `sR` using `hf.indicator R`. Establish `sQ` using `hf.indicator Q`.

Rewrite using `[tsum_subtype R f, tsum_subtype Q f]`. Establish `e0 : ∑' ξ, ({0} : Set (Fin 4 → ℚ)).indicator f ξ = f 0`. Rewrite using `[← tsum_subtype]`. Simplify using the standard rewrite rules. Rewrite using `[← e0, ← (s0.tsum_add sR), ← ((s0.add sR).tsum_add sQ)]`.

Conclude with `tsum_congr hpt`.
-/
private theorem tsum_split (δ : ℚ) (f : (Fin 4 → ℚ) → ℂ) (hf : Summable f) :
    ∑' ξ, f ξ = f 0 + (∑' ξ : ({ξ | ξ ≠ 0 ∧ qr δ ξ = 0} : Set (Fin 4 → ℚ)), f ξ) +
      ∑' ξ : ({ξ | qr δ ξ ≠ 0} : Set (Fin 4 → ℚ)), f ξ := by
  set R : Set (Fin 4 → ℚ) := {ξ | ξ ≠ 0 ∧ qr δ ξ = 0}
  set Q : Set (Fin 4 → ℚ) := {ξ | qr δ ξ ≠ 0}
  have h0 : qr δ 0 = 0 := by simp [qr]
  have hpt : ∀ ξ, f ξ = (({0} : Set (Fin 4 → ℚ)).indicator f ξ + R.indicator f ξ) + Q.indicator f ξ := by
    intro ξ
    by_cases hq : qr δ ξ = 0
    · by_cases hξ : ξ = 0
      · subst hξ
        simp [R, Q, h0]
      · simp [R, Q, hξ, hq]
    · have hξ : ξ ≠ 0 := fun e => hq (e ▸ h0)
      simp [R, Q, hξ, hq]
  have s0 := hf.indicator ({0} : Set (Fin 4 → ℚ))
  have sR := hf.indicator R
  have sQ := hf.indicator Q
  rw [tsum_subtype R f, tsum_subtype Q f]
  have e0 : ∑' ξ, ({0} : Set (Fin 4 → ℚ)).indicator f ξ = f 0 := by
    rw [← tsum_subtype]; simp
  rw [← e0, ← (s0.tsum_add sR), ← ((s0.add sR).tsum_add sQ)]
  exact tsum_congr hpt

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [cD]`.
-/
private theorem cD_one (g : G1 ℚ) : cD 1 g = g := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cD]

/- English proof (translation)
Simplify using `[ab]`.
-/
private theorem ab_one' : ab (1 : (A ℚ)ˣ) = 1 := by
  simp [ab]

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {D : Dat ℚ E}

/- English proof (translation)
Establish `e : D.herm (0 : V4 ℚ) = 0`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Dat.herm, Dat.mkE]`. Establish `e2 : D.unherm (0 : Matrix (Fin 2) (Fin 2) (A E)) = 0`. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `fin_cases i <;> simp [Dat.unherm, Dat.co]`. Simplify using `[Dat.act, e, e2]`.
-/
private theorem act_zero (h : GL (Fin 2) (A E)) : D.act h (0 : V4 ℚ) = 0 := by
  have e : D.herm (0 : V4 ℚ) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Dat.herm, Dat.mkE]
  have e2 : D.unherm (0 : Matrix (Fin 2) (Fin 2) (A E)) = 0 := by
    funext i
    fin_cases i <;> simp [Dat.unherm, Dat.co]
  simp [Dat.act, e, e2]

/- English proof (translation)
Establish `h1` using `W.comm x g`. Rewrite `h1` using `[hx, cD_one]`. Establish `h2 : W.Om g (W.L x ph) = W.L x (W.Om g ph)`. Use `congrArg (fun T : Module.End ℂ (S4 ℚ) => T ph) h1` as an intermediate fact. Simplify `this.symm` using `[Module.End.mul_apply]`.

Establish `hz : rp (0 : Fin 4 → ℚ) = (0 : V4 ℚ)`. Use function extensionality and compare the values at `i`. Simplify using `[rp]`. Rewrite using `[h2, W.L_apply, hx, ab_one', hz, act_zero]`. Simplify using the standard rewrite rules.
-/
private theorem om_zero (W : Weil D) (g : G1 ℚ) (ph : S4 ℚ) (x : GL (Fin 2) (A E)) (hx : nu ℚ x = 1) :
    (W.Om g (W.L x ph)).1 (rp 0) = (W.Om g ph).1 (rp 0) := by
  have h1 := W.comm x g
  rw [hx, cD_one] at h1
  have h2 : W.Om g (W.L x ph) = W.L x (W.Om g ph) := by
    have := congrArg (fun T : Module.End ℂ (S4 ℚ) => T ph) h1
    simpa [Module.End.mul_apply] using this.symm
  have hz : rp (0 : Fin 4 → ℚ) = (0 : V4 ℚ) := by
    funext i; simp [rp]
  rw [h2, W.L_apply, hx, ab_one', hz, act_zero]
  simp

/- English proof (translation)
Take `⟨b, a, k', hk', hg⟩` from `UpperTheory.ConvolutionTheory.R2.M.iwa ℚ g`. Establish `hapos : 0 < ab a` using `(IdeleGroup.ideleModule ℚ a).2`. Take `⟨B, hB⟩` from `hMaj E D W M N P ph hph φ hφ {y} isCompact_singleton (by rintro k rfl; exact hy) (ab a) hapos 0`. Establish `hB' : ∀ h : G1 E, (Summable fun ξ : Fin 4 → ℚ => ‖(W.Om g (W.L (gl h * y) ph)).1 (rp ξ)‖) ∧ (∑' ξ : Fin 4 → ℚ, ‖(W.Om g (W.L (gl h * y) ph)).1 (rp ξ)‖) * ‖φ.1 (gl h * y)‖ ≤ B * ab a ^ 2`. Introduce `h`.

Use `hB b a k' hk' le_rfl h y rfl` as an intermediate fact. Rewrite `this` using `[← hg]`. Conclude with `⟨this.1, this.2.1⟩`. Establish `hnu : ∀ h : G1 E, nu ℚ (gl h * y) = 1` using `fun h => by rw [nu_mul, hgl, hy, one_mul]`. Establish `hcφ : Continuous φ.1` using `GlobalTheory.T.automorphicForm_GL_continuous E 2 φ (P.cusp φ hφ).1`.

Establish `hcg : Continuous fun h : G1 E => gl h` using `by fun_prop`. Establish `hcx : Continuous fun h : G1 E => gl h * y` using `hcg.mul continuous_const`. Use `haveI : IsFiniteMeasure (N.μ.restrict N.D) := ⟨by simpa using hV⟩`. Establish `hint : ∀ S : Set (Fin 4 → ℚ), IntegrableOn (fun h : G1 E => ThOn S (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y)) N.D N.μ`. Introduce `S`.

Establish `hc1 : Continuous fun h : G1 E => ThOn S (W.Om g (W.L (gl h * y) ph)).1` using `(hTh E D W M N P ph hph S).comp_continuous (f := fun h : G1 E => (g, gl h * y)) (continuous_const.prodMk hcx) (fun h => hnu h)`. Establish `hc : Continuous fun h : G1 E => ThOn S (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y)` using `hc1.mul (hcφ.comp hcx)`. Use `Integrable.of_bound hc.aestronglyMeasurable (B * ab a ^ 2) (Eventually.of_forall fun h => ?_)` and prove the remaining obligations. Take `⟨hs, hb⟩` from `hB' h`. Establish `hle : ‖ThOn S (W.Om g (W.L (gl h * y) ph)).1‖ ≤ ∑' ξ : Fin 4 → ℚ, ‖(W.Om g (W.L (gl h * y) ph)).1 (rp ξ)‖`.

Establish `hsS` using `hs.subtype S`. Use `(norm_tsum_le_tsum_norm hsS).trans ?_` and prove the remaining obligations. Conclude with `tsum_comp_le_tsum_of_inj hs (fun _ => norm_nonneg _) Subtype.val_injective`. Rewrite using `[norm_mul]`. Conclude with `(mul_le_mul_of_nonneg_right hle (norm_nonneg _)).trans hb`.

Use `set c : ℂ := (W.Om g ph).1 (rp 0)`. Establish `hz : ∀ h : G1 E, ThOn {0} (W.Om g (W.L (gl h * y) ph)).1 = c`. Introduce `h`. Establish `e : ThOn {0} (W.Om g (W.L (gl h * y) ph)).1 = (W.Om g (W.L (gl h * y) ph)).1 (rp 0)`. Simplify using `[ThOn]`.

Rewrite using `[e]`. Conclude with `om_zero W g ph _ (hnu h)`. Establish `hφi : IntegrableOn (fun h : G1 E => c * φ.1 (gl h * y)) N.D N.μ`. Use `(hint {0}).congr (Eventually.of_forall fun h => ?_)` and prove the remaining obligations. Simplify using `only [hz]`.

Establish `hpt : ∀ h : G1 E, Th (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) = c * φ.1 (gl h * y) + ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) + ThOn {ξ | qr D.δ ξ ≠ 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y)`. Introduce `h`. Establish `hsp` using `tsum_split D.δ (fun ξ => (W.Om g (W.L (gl h * y) ph)).1 (rp ξ)) (hB' h).1.of_norm`. Establish `e0 : (W.Om g (W.L (gl h * y) ph)).1 (rp 0) = c` using `om_zero W g ph _ (hnu h)`. Establish `: Th (W.Om g (W.L (gl h * y) ph)).1 = c + ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 + ThOn {ξ | qr D.δ ξ ≠ 0} (W.Om g (W.L (gl h * y) ph)).1`.

Rewrite using `[← e0]`. Conclude with `hsp`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Establish `z1 : ∫ h in N.D, φ.1 (gl h * y) ∂N.μ = 0` using `hMean E D W M N P φ hφ y`.

Establish `z2 : ∫ h in N.D, ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) ∂N.μ = 0` using `hR1 E D W M N P ph hph φ hφ g y hy`. Simplify using `only [mean]`. Simplify using `only [hpt]`. Establish `i1 : IntegrableOn (fun h : G1 E => c * φ.1 (gl h * y) + ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y)) N.D N.μ` using `hφi.add (hint _)`. Rewrite using `[integral_add i1 (hint _), integral_add hφi (hint _), integral_const_mul, z1, z2]`.

Simplify using the standard rewrite rules.
-/
private theorem core (hMaj : Maj) (hTh : ThCont) (hMean : MeanZero) (hR1 : Rank1)
    (W : Weil D) (M : Meas ℚ) (N : MeasE E) (P : CuspSub E 2) (hV : N.μ N.D < ⊤)
    (ph : S4 ℚ) (hph : ph ∈ Fock D.δ) (φ : Sm E 2) (hφ : φ ∈ P.V) (g : G1 ℚ)
    (y : GL (Fin 2) (A E)) (hy : nu ℚ y = 1) (hgl : ∀ h : G1 E, nu ℚ (gl h) = 1) :
    (mean N fun x => Th (W.Om g (W.L (x * y) ph)).1 * φ.1 (x * y)) =
      mean N fun x => ThOn {ξ | qr D.δ ξ ≠ 0} (W.Om g (W.L (x * y) ph)).1 * φ.1 (x * y) := by
  obtain ⟨b, a, k', hk', hg⟩ := UpperTheory.ConvolutionTheory.R2.M.iwa ℚ g
  have hapos : 0 < ab a := (IdeleGroup.ideleModule ℚ a).2
  obtain ⟨B, hB⟩ := hMaj E D W M N P ph hph φ hφ {y} isCompact_singleton
    (by rintro k rfl; exact hy) (ab a) hapos 0
  have hB' : ∀ h : G1 E, (Summable fun ξ : Fin 4 → ℚ => ‖(W.Om g (W.L (gl h * y) ph)).1 (rp ξ)‖) ∧
      (∑' ξ : Fin 4 → ℚ, ‖(W.Om g (W.L (gl h * y) ph)).1 (rp ξ)‖) * ‖φ.1 (gl h * y)‖ ≤ B * ab a ^ 2 := by
    intro h
    have := hB b a k' hk' le_rfl h y rfl
    rw [← hg] at this
    exact ⟨this.1, this.2.1⟩
  have hnu : ∀ h : G1 E, nu ℚ (gl h * y) = 1 := fun h => by rw [nu_mul, hgl, hy, one_mul]
  have hcφ : Continuous φ.1 := GlobalTheory.T.automorphicForm_GL_continuous E 2 φ (P.cusp φ hφ).1
  have hcg : Continuous fun h : G1 E => gl h := by fun_prop
  have hcx : Continuous fun h : G1 E => gl h * y := hcg.mul continuous_const
  haveI : IsFiniteMeasure (N.μ.restrict N.D) := ⟨by simpa using hV⟩
  have hint : ∀ S : Set (Fin 4 → ℚ), IntegrableOn
      (fun h : G1 E => ThOn S (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y)) N.D N.μ := by
    intro S
    have hc1 : Continuous fun h : G1 E => ThOn S (W.Om g (W.L (gl h * y) ph)).1 :=
      (hTh E D W M N P ph hph S).comp_continuous (f := fun h : G1 E => (g, gl h * y))
        (continuous_const.prodMk hcx) (fun h => hnu h)
    have hc : Continuous fun h : G1 E => ThOn S (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) :=
      hc1.mul (hcφ.comp hcx)
    refine Integrable.of_bound hc.aestronglyMeasurable (B * ab a ^ 2) (Eventually.of_forall fun h => ?_)
    obtain ⟨hs, hb⟩ := hB' h
    have hle : ‖ThOn S (W.Om g (W.L (gl h * y) ph)).1‖ ≤
        ∑' ξ : Fin 4 → ℚ, ‖(W.Om g (W.L (gl h * y) ph)).1 (rp ξ)‖ := by
      have hsS := hs.subtype S
      refine (norm_tsum_le_tsum_norm hsS).trans ?_
      exact tsum_comp_le_tsum_of_inj hs (fun _ => norm_nonneg _) Subtype.val_injective
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hle (norm_nonneg _)).trans hb
  set c : ℂ := (W.Om g ph).1 (rp 0)
  have hz : ∀ h : G1 E, ThOn {0} (W.Om g (W.L (gl h * y) ph)).1 = c := by
    intro h
    have e : ThOn {0} (W.Om g (W.L (gl h * y) ph)).1 = (W.Om g (W.L (gl h * y) ph)).1 (rp 0) := by
      simp [ThOn]
    rw [e]
    exact om_zero W g ph _ (hnu h)
  have hφi : IntegrableOn (fun h : G1 E => c * φ.1 (gl h * y)) N.D N.μ := by
    refine (hint {0}).congr (Eventually.of_forall fun h => ?_)
    simp only [hz]
  have hpt : ∀ h : G1 E, Th (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) =
      c * φ.1 (gl h * y) +
        ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) +
        ThOn {ξ | qr D.δ ξ ≠ 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) := by
    intro h
    have hsp := tsum_split D.δ (fun ξ => (W.Om g (W.L (gl h * y) ph)).1 (rp ξ)) (hB' h).1.of_norm
    have e0 : (W.Om g (W.L (gl h * y) ph)).1 (rp 0) = c := om_zero W g ph _ (hnu h)
    have : Th (W.Om g (W.L (gl h * y) ph)).1 = c + ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 +
        ThOn {ξ | qr D.δ ξ ≠ 0} (W.Om g (W.L (gl h * y) ph)).1 := by
      rw [← e0]
      exact hsp
    rw [this]
    ring
  have z1 : ∫ h in N.D, φ.1 (gl h * y) ∂N.μ = 0 := hMean E D W M N P φ hφ y
  have z2 : ∫ h in N.D, ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) ∂N.μ = 0 :=
    hR1 E D W M N P ph hph φ hφ g y hy
  simp only [mean]
  simp only [hpt]
  have i1 : IntegrableOn (fun h : G1 E => c * φ.1 (gl h * y) +
      ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y)) N.D N.μ := hφi.add (hint _)
  rw [integral_add i1 (hint _), integral_add hφi (hint _), integral_const_mul, z1, z2]
  simp

end UpperTheory.ConvolutionTheory.RankTwoDescent

/- English proof (translation)
Introduce `hMaj hTh hMean hR1 E _ _ _ D W M N P ph hph φ hφ`. Use function extensionality and compare the values at `g`. Establish `hS` using `szLaws E D`. Simplify using `only [f0, fOn, J1]`. Use `congrArg (UI (E := E)) (funext fun z => ?_)` and prove the remaining obligations.

Conclude with `core hMaj hTh hMean hR1 W M N P (UpperTheory.ConvolutionTheory.RankTwoDescent.volE E N) ph hph φ hφ g (sZ D z) (hS.2.2.1 z) hS.2.2.2.1`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.f0Eq :
    Maj → ThCont → MeanZero → Rank1 → ThetaLiftEqAnisotropicPart := by
  intro hMaj hTh hMean hR1 E _ _ _ D W M N P ph hph φ hφ
  funext g
  have hS := szLaws E D
  simp only [f0, fOn, J1]
  refine congrArg (UI (E := E)) (funext fun z => ?_)
  exact core hMaj hTh hMean hR1 W M N P (UpperTheory.ConvolutionTheory.RankTwoDescent.volE E N) ph hph φ hφ g (sZ D z) (hS.2.2.1 z) hS.2.2.2.1
