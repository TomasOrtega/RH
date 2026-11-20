import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousOnHolomorphicFramedFamilyStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsHolomorphicFamilyStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.FrameNorm

/- English proof (translation)
Introduce `x₀ hx₀`. Set `ρ : X → (A →+* ℂ)` to `fun x => (φ x).toRingHom`. Establish `hρ : ∀ x, (ρ x).comp (algebraMap c.F A) = σ` using `fun x => RingHom.ext fun a => (φ x).commutes a`. Establish `hρc : ∀ a, ContinuousOn (fun x => ρ x a) W` using `hφ`. Take `⟨m, s, B, ψ, S, ε, hB, hε, hψ, hd, hnear⟩` from `GlobalTheory.T.exists_holomorphic_family_of_ringHom_near c.F A σ (ρ x₀) (hρ x₀)`.

Set `ψ' : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)` to `fun b => if h : b ∈ B then { (show A →+* CAt σ from ψ b) with commutes' := fun a => RingHom.congr_fun (hψ b h).1 a } else φ x₀`. Establish `hψ' : ∀ b ∈ B, ∀ a, Formalism.L2.PjFree.toC (ψ' b a) = ψ b a`. Introduce `b hb a`. Simplify using `only [ψ', dif_pos hb]`. Both sides reduce to the same expression.

Use `choose z hz using fun b => GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c A (CAt σ) (ψ' b) yA`. Establish `hcont` using `GlobalTheory.T.frameNorms_continuousOn_holomorphic_framedFamily E H Dw l Xo c r U hU xR fn hx hfn σ hσ A yA m B ψ' z hB (fun a => (hd a).congr fun b hb => hψ' b hb a) (fun b _ => hz b) i`. Set `p : X → (Fin m → ℂ)` to `fun x j => ρ x (s j)`. Establish `hp : ContinuousWithinAt p W x₀` using `continuousWithinAt_pi.2 fun j => hρc (s j) x₀ hx₀`. Establish `hev : ∀ᶠ x in nhdsWithin x₀ W, ∀ a ∈ S, ‖ρ x a - ρ x₀ a‖ < ε`.

Rewrite using `[Filter.eventually_all_finset]`. Introduce `a _`. Use `Metric.tendsto_nhds.1 (hρc a x₀ hx₀) ε hε` as an intermediate fact. Simplify `this` using `only [dist_eq_norm]`. Establish `key : ∀ x ∈ W, (∀ a ∈ S, ‖ρ x a - ρ x₀ a‖ < ε) → p x ∈ B ∧ y x = z (p x)`.

Introduce `x hxW h`. Take `⟨h1, h2⟩` from `hnear (ρ x) (hρ x) h`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `e : ψ' (p x) = φ x`. Use `AlgHom.ext fun a => ?_` and prove the remaining obligations.

Use `hψ' (p x) h1 a` as an intermediate fact. Rewrite `this` using `[show ψ (p x) = ρ x from h2]`. Conclude with `this`. Establish `h3` using `hz (p x)`. Rewrite `h3` using `[e]`.

Conclude with `(GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c A (CAt σ) (φ x) yA).1 _ _ (hy x hxW) h3`. Establish `h0` using `key x₀ hx₀ (fun a _ => by simpa using hε)`. Establish `hc : ContinuousWithinAt (fun x => |fn σ (z (p x)) i|) W x₀` using `ContinuousAt.comp_continuousWithinAt (f := p) (g := fun b => |fn σ (z b) i|) (hcont.continuousAt (hB.mem_nhds h0.1)) hp`. Use `hc.congr_of_eventuallyEq ?_ (by rw [h0.2])` and prove the remaining obligations. Use `filter_upwards [hev, self_mem_nhdsWithin] with x h hxW`.

Rewrite using `[(key x hxW h).2]`.
-/
theorem fn_continuousOn_good {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r)
    (hU : ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) (xR : ℝ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) (hx : 0 < xR) (hfn : FnPin U xR fn)
    (σ : c.F →+* ℂ) (hσ : Formalism.L2.PjFree.GoodEmb c σ) (A : Type) [CommRing A] [Algebra c.F A] [Algebra.Smooth c.F A]
    (yA : FrPt Xo c A) (X : Type) [TopologicalSpace X] (W : Set X) (φ : X → (A →ₐ[c.F] CAt σ))
    (y : X → FrPt Xo c (CAt σ)) (hφ : ∀ a, ContinuousOn (fun x => Formalism.L2.PjFree.toC (φ x a)) W)
    (hy : ∀ x ∈ W, FrMap (φ x) yA (y x)) (i : Ix Dw) : ContinuousOn (fun x => |fn σ (y x) i|) W := by
  classical
  intro x₀ hx₀
  let ρ : X → (A →+* ℂ) := fun x => (φ x).toRingHom
  have hρ : ∀ x, (ρ x).comp (algebraMap c.F A) = σ := fun x => RingHom.ext fun a => (φ x).commutes a
  have hρc : ∀ a, ContinuousOn (fun x => ρ x a) W := hφ
  obtain ⟨m, s, B, ψ, S, ε, hB, hε, hψ, hd, hnear⟩ := GlobalTheory.T.exists_holomorphic_family_of_ringHom_near c.F A σ (ρ x₀) (hρ x₀)
  let ψ' : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ) := fun b =>
    if h : b ∈ B then
      { (show A →+* CAt σ from ψ b) with commutes' := fun a => RingHom.congr_fun (hψ b h).1 a }
    else φ x₀
  have hψ' : ∀ b ∈ B, ∀ a, Formalism.L2.PjFree.toC (ψ' b a) = ψ b a := by
    intro b hb a
    simp only [ψ', dif_pos hb]
    rfl
  choose z hz using fun b => GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c A (CAt σ) (ψ' b) yA
  have hcont := GlobalTheory.T.frameNorms_continuousOn_holomorphic_framedFamily E H Dw l Xo c r U hU xR fn hx hfn σ hσ A yA m B ψ' z hB
    (fun a => (hd a).congr fun b hb => hψ' b hb a) (fun b _ => hz b) i
  let p : X → (Fin m → ℂ) := fun x j => ρ x (s j)
  have hp : ContinuousWithinAt p W x₀ := continuousWithinAt_pi.2 fun j => hρc (s j) x₀ hx₀
  have hev : ∀ᶠ x in nhdsWithin x₀ W, ∀ a ∈ S, ‖ρ x a - ρ x₀ a‖ < ε := by
    rw [Filter.eventually_all_finset]
    intro a _
    have := Metric.tendsto_nhds.1 (hρc a x₀ hx₀) ε hε
    simpa only [dist_eq_norm] using this
  have key : ∀ x ∈ W, (∀ a ∈ S, ‖ρ x a - ρ x₀ a‖ < ε) → p x ∈ B ∧ y x = z (p x) := by
    intro x hxW h
    obtain ⟨h1, h2⟩ := hnear (ρ x) (hρ x) h
    refine ⟨h1, ?_⟩
    have e : ψ' (p x) = φ x := by
      refine AlgHom.ext fun a => ?_
      have := hψ' (p x) h1 a
      rw [show ψ (p x) = ρ x from h2] at this
      exact this
    have h3 := hz (p x)
    rw [e] at h3
    exact (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c A (CAt σ) (φ x) yA).1 _ _ (hy x hxW) h3
  have h0 := key x₀ hx₀ (fun a _ => by simpa using hε)
  have hc : ContinuousWithinAt (fun x => |fn σ (z (p x)) i|) W x₀ :=
    ContinuousAt.comp_continuousWithinAt (f := p) (g := fun b => |fn σ (z b) i|)
      (hcont.continuousAt (hB.mem_nhds h0.1)) hp
  refine hc.congr_of_eventuallyEq ?_ (by rw [h0.2])
  filter_upwards [hev, self_mem_nhdsWithin] with x h hxW
  rw [(key x hxW h).2]

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c r U hU xR fn hx hfn σ A _ _ _ yA X _ W φ y hφ hy i`. Distinguish the cases in `hσ : Formalism.L2.PjFree.GoodEmb c σ`. Conclude with `fn_continuousOn_good U hU xR fn hx hfn σ hσ A yA X W φ y hφ hy i`. Establish `hσ' : Formalism.L2.PjFree.GoodEmb c ((starRingEnd ℂ).comp σ)`. Use `Formalism.L2.PjFree.goodEmb_goodOf c σ` as an intermediate fact.

Unfold `Formalism.L2.PjFree.goodOf at this`. Rewrite `this` using `[if_neg hσ]`. Then use the resulting hypothesis. Use `choose z hz using fun x => GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c (CAt σ) (CAt ((starRingEnd ℂ).comp σ)) (conjAlg σ) (y x)`. Establish `h` using `fn_continuousOn_good U hU xR fn hx hfn _ hσ' A yA X W (fun x => (conjAlg σ).comp (φ x)) z (fun a => Complex.continuous_conj.comp_continuousOn (hφ a)) (fun x hxW => frMap_trans (Xo := Xo) (c := c) _ _ _ (φ x) (conjAlg σ) yA (y x) (z x) (hy x hxW) (hz x)) i`. Conclude with `h.congr fun x _ => (hfn.2 σ (y x) (z x) (hz x) i).symm`.
-/
theorem fn_continuousOn_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ (σ : c.F →+* ℂ) (A : Type) [CommRing A] [Algebra c.F A] [Algebra.Smooth c.F A] (yA : FrPt Xo c A) (X : Type) [TopologicalSpace X] (W : Set X) (φ : X → (A →ₐ[c.F] CAt σ)) (y : X → FrPt Xo c (CAt σ)), (∀ a, ContinuousOn (fun x => Formalism.L2.PjFree.toC (φ x a)) W) → (∀ x ∈ W, FrMap (φ x) yA (y x)) → ∀ i, ContinuousOn (fun x => |fn σ (y x) i|) W := by
  intro E _ _ _ H Dw l Xo c r U hU xR fn hx hfn σ A _ _ _ yA X _ W φ y hφ hy i
  by_cases hσ : Formalism.L2.PjFree.GoodEmb c σ
  · exact fn_continuousOn_good U hU xR fn hx hfn σ hσ A yA X W φ y hφ hy i
  · have hσ' : Formalism.L2.PjFree.GoodEmb c ((starRingEnd ℂ).comp σ) := by
      have := Formalism.L2.PjFree.goodEmb_goodOf c σ
      unfold Formalism.L2.PjFree.goodOf at this
      rwa [if_neg hσ] at this
    choose z hz using fun x => GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c (CAt σ)
      (CAt ((starRingEnd ℂ).comp σ)) (conjAlg σ) (y x)
    have h := fn_continuousOn_good U hU xR fn hx hfn _ hσ' A yA X W (fun x => (conjAlg σ).comp (φ x)) z
      (fun a => Complex.continuous_conj.comp_continuousOn (hφ a))
      (fun x hxW => frMap_trans (Xo := Xo) (c := c) _ _ _ (φ x) (conjAlg σ) yA (y x) (z x) (hy x hxW) (hz x)) i
    exact h.congr fun x _ => (hfn.2 σ (y x) (z x) (hz x) i).symm

end GlobalTheory.FrameNorm
