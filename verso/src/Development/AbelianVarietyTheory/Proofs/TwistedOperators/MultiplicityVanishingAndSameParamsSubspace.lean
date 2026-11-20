import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainHeckeParamAddSmulOfAgreeOffSet
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOnto

/- English proof (translation)
Introduce `hM c hc j hj s hs x w hw hx`. Take `⟨ipD, ip, hm⟩` from `hM c hc j hj s hs`. Establish `h1` using `hm.schur x x w w`. Establish `h0 : Lift.pet s.ν s.fd ((x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w) ((x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w) = 0`. Establish `hx' : (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w = 0` using `hx`.

Rewrite using `[hx']`. Simplify using `[Lift.pet]`. Rewrite `h1` using `[h0]`. Establish `hD : ipD w w ≠ 0`. Introduce `h`.

Use `hm.posD w hw` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `at this`. Establish `hip : ip x x = 0`. Break down `mul_eq_zero.mp h1.symm with h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd h hD`. Assume the negation of the conclusion as `hne`. Use `hm.pos x hne` as an intermediate fact. Rewrite `this` using `[hip]`.

Simplify using `at this`.
-/
theorem val_eq_zero_imp (D : D7) : MetEx D → ForStage D fun c _ s => ∀ (x : s.CC c) w, w ≠ 0 → PiLocalization₂.val x w = 0 → x = 0 := by
  intro hM c hc j hj s hs x w hw hx
  obtain ⟨ipD, ip, hm⟩ := hM c hc j hj s hs
  have h1 := hm.schur x x w w
  have h0 : Lift.pet s.ν s.fd ((x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w) ((x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w) = 0 := by
    have hx' : (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w = 0 := hx
    rw [hx']
    simp [Lift.pet]
  rw [h0] at h1
  have hD : ipD w w ≠ 0 := by
    intro h
    have := hm.posD w hw
    rw [h] at this
    simp at this
  have hip : ip x x = 0 := by
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact h
    · exact absurd h hD
  by_contra hne
  have := hm.pos x hne
  rw [hip] at this
  simp at this

open GlobalTheory.LFun.ParLin in

/- English proof (translation)
Introduce `D c s`. Establish `cne : ∀ f : GA D s.V → ℂ, f ≠ 0 → (fun g => conj (f g)) ≠ 0` using `fun f hf h0 => hf (funext fun g => by simpa using congrFun h0 g)`. Use `⟨fun u u' B B' a hu hu' hB h0 => ⟨h0, fun v hv => ?_⟩, fun u B a hu ha => ⟨smul_ne_zero ha hu.1, fun v hv => ?_⟩⟩` and prove the remaining obligations. Establish `hval : PiLocalization₂.val (u + a • u') v = PiLocalization₂.val u v + a • PiLocalization₂.val u' v` using `by simp [PiLocalization₂.val]`. Establish `hc : (fun g => conj (PiLocalization₂.val (u + a • u') v g)) = (fun g => conj (PiLocalization₂.val u v g)) + (conj a) • (fun g => conj (PiLocalization₂.val u' v g))`.

Use function extensionality and compare the values at `g`. Simplify using `[hval]`. Unfold `ParFun`. Rewrite using `[hc]`. Distinguish the cases in `h1 : PiLocalization₂.val u v = 0`.

Establish `h2 : a • PiLocalization₂.val u' v ≠ 0` using `by rw [hval, h1, zero_add] at hv; exact hv`. Establish `ha : a ≠ 0` using `fun e => h2 (by simp [e])`. Establish `hu'v : PiLocalization₂.val u' v ≠ 0` using `fun e => h2 (by simp [e])`. Establish `hz : (fun g => conj (PiLocalization₂.val u v g)) = 0` using `by funext g; simp [h1]`. Rewrite using `[hz, zero_add]`.

Conclude with `paramFun_smul (paramFun_of_agree (hu'.2 v hu'v) hB) (by simpa using ha)`. Distinguish the cases in `h2 : a • PiLocalization₂.val u' v = 0`. Establish `hz : (conj a) • (fun g => conj (PiLocalization₂.val u' v g)) = 0`. Use function extensionality and compare the values at `g`. Use `congrFun h2 g` as an intermediate fact.

Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢`. Rewrite using `[← map_mul, this, map_zero]`. Rewrite using `[hz, add_zero]`. Conclude with `hu.2 v h1`. Establish `ha : a ≠ 0` using `fun e => h2 (by simp [e])`.

Establish `hu'v : PiLocalization₂.val u' v ≠ 0` using `fun e => h2 (by simp [e])`. Use `paramFun_add (hu.2 v h1) (paramFun_smul (paramFun_of_agree (hu'.2 v hu'v) hB) (by simpa using ha)) ?_` and prove the remaining obligations. Rewrite using `[← hc]`. Conclude with `cne _ hv`. Establish `hval : PiLocalization₂.val (a • u) v = a • PiLocalization₂.val u v` using `by simp [PiLocalization₂.val]`.

Establish `hu0 : PiLocalization₂.val u v ≠ 0` using `fun e => hv (by rw [hval, e, smul_zero])`. Establish `hc : (fun g => conj (PiLocalization₂.val (a • u) v g)) = (conj a) • (fun g => conj (PiLocalization₂.val u v g))`. Use function extensionality and compare the values at `g`. Simplify using `[hval]`. Unfold `ParFun`.

Rewrite using `[hc]`. Conclude with `paramFun_smul (hu.2 v hu0) (by simpa using ha)`.
-/
theorem isPar_add_smul : ∀ (D : D7) (c : Com D) (s : PiLocalization₂ D), (∀ (u u' : s.CC c) B B' (a : ℂ), IsPar u B → IsPar u' B' →
    (∀ w ∉ (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))), B w = B' w) →
    u + a • u' ≠ 0 → IsPar (u + a • u') B) ∧ ∀ (u : s.CC c) B (a : ℂ), IsPar u B → a ≠ 0 → IsPar (a • u) B := by
  intro D c s
  have cne : ∀ f : GA D s.V → ℂ, f ≠ 0 → (fun g => conj (f g)) ≠ 0 := fun f hf h0 =>
    hf (funext fun g => by simpa using congrFun h0 g)
  refine ⟨fun u u' B B' a hu hu' hB h0 => ⟨h0, fun v hv => ?_⟩, fun u B a hu ha => ⟨smul_ne_zero ha hu.1, fun v hv => ?_⟩⟩
  · have hval : PiLocalization₂.val (u + a • u') v = PiLocalization₂.val u v + a • PiLocalization₂.val u' v := by simp [PiLocalization₂.val]
    have hc : (fun g => conj (PiLocalization₂.val (u + a • u') v g)) =
        (fun g => conj (PiLocalization₂.val u v g)) + (conj a) • (fun g => conj (PiLocalization₂.val u' v g)) := by
      funext g; simp [hval]
    unfold ParFun
    rw [hc]
    by_cases h1 : PiLocalization₂.val u v = 0
    · have h2 : a • PiLocalization₂.val u' v ≠ 0 := by rw [hval, h1, zero_add] at hv; exact hv
      have ha : a ≠ 0 := fun e => h2 (by simp [e])
      have hu'v : PiLocalization₂.val u' v ≠ 0 := fun e => h2 (by simp [e])
      have hz : (fun g => conj (PiLocalization₂.val u v g)) = 0 := by funext g; simp [h1]
      rw [hz, zero_add]
      exact paramFun_smul (paramFun_of_agree (hu'.2 v hu'v) hB) (by simpa using ha)
    · by_cases h2 : a • PiLocalization₂.val u' v = 0
      · have hz : (conj a) • (fun g => conj (PiLocalization₂.val u' v g)) = 0 := by
          funext g
          have := congrFun h2 g
          simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
          rw [← map_mul, this, map_zero]
        rw [hz, add_zero]
        exact hu.2 v h1
      · have ha : a ≠ 0 := fun e => h2 (by simp [e])
        have hu'v : PiLocalization₂.val u' v ≠ 0 := fun e => h2 (by simp [e])
        refine paramFun_add (hu.2 v h1) (paramFun_smul (paramFun_of_agree (hu'.2 v hu'v) hB) (by simpa using ha)) ?_
        rw [← hc]
        exact cne _ hv
  · have hval : PiLocalization₂.val (a • u) v = a • PiLocalization₂.val u v := by simp [PiLocalization₂.val]
    have hu0 : PiLocalization₂.val u v ≠ 0 := fun e => hv (by rw [hval, e, smul_zero])
    have hc : (fun g => conj (PiLocalization₂.val (a • u) v g)) = (conj a) • (fun g => conj (PiLocalization₂.val u v g)) := by
      funext g; simp [hval]
    unfold ParFun
    rw [hc]
    exact paramFun_smul (hu.2 v hu0) (by simpa using ha)

/- English proof (translation)
Introduce `D hM` and use `⟨val_eq_zero_imp D hM, isPar_add_smul D⟩`.
-/
theorem vanish_and_parLin : ∀ D : D7, MetEx D → (ForStage D fun c _ s => ∀ (x : s.CC c) w, w ≠ 0 → PiLocalization₂.val x w = 0 → x = 0) ∧ ∀ (c : Com D) (s : PiLocalization₂ D), (∀ (u u' : s.CC c) B B' (a : ℂ), IsPar u B → IsPar u' B' → (∀ w ∉ (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))), B w = B' w) → u + a • u' ≠ 0 → IsPar (u + a • u') B) ∧ ∀ (u : s.CC c) B (a : ℂ), IsPar u B → a ≠ 0 → IsPar (a • u) B :=
  fun D hM => ⟨val_eq_zero_imp D hM, isPar_add_smul D⟩

end GlobalTheory.EvenOnto
