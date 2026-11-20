import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValQOfValQr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFirstStepFlatMapSupportAll
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.QVal

/- English proof (translation)
Use `haveI : IsProbabilityMeasure μR := ⟨hR⟩`. Use `haveI : IsProbabilityMeasure μG := ⟨hG⟩`. Establish `hc : ∀ x, f x = f 1` using `fun x => by rw [Subsingleton.elim x 1]`. Establish `hf : f = fun _ => f 1` using `funext hc`. Use `⟨fun _ => f 1, integrable_const _, fun _ => integrable_const _, fun h => ?_, ?_⟩` and prove the remaining obligations.

Simplify using `[hc h]`. Simplify using the standard rewrite rules.
-/
theorem quotient_integral_of_subsingleton {G : Type} [Group G] [MeasurableSpace G] [Subsingleton G] {R : Subgroup G}
    (μR : Measure R) (μG : Measure G) (hR : μR Set.univ = 1) (hG : μG Set.univ = 1) (f : G → ℂ) :
    IsQuotIntL1 μR μG f (f 1) := by
  haveI : IsProbabilityMeasure μR := ⟨hR⟩
  haveI : IsProbabilityMeasure μG := ⟨hG⟩
  have hc : ∀ x, f x = f 1 := fun x => by rw [Subsingleton.elim x 1]
  have hf : f = fun _ => f 1 := funext hc
  refine ⟨fun _ => f 1, integrable_const _, fun _ => integrable_const _, fun h => ?_, ?_⟩
  · simp [hc h]
  · simp

section
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conv_nil' {G : Type} [Monoid G] : conv ([] : List (G →₀ ℂ)) = Finsupp.single 1 1 := rfl

/- English proof (translation)
Simplify using `only [aconv, List.foldr_cons, List.foldr_nil]`. Use `conv_rhs => rw [← Finsupp.sum_single c]`. Use `Finsupp.sum_congr fun g _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.sum_single_index (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem aconv_singleton' {G : Type} [AddMonoid G] (c : G →₀ ℂ) : aconv [c] = c := by
  simp only [aconv, List.foldr_cons, List.foldr_nil]
  conv_rhs => rw [← Finsupp.sum_single c]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [Finsupp.sum_single_index (by simp)]
  simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem aconv_nil' {G : Type} [AddMonoid G] : aconv ([] : List (G →₀ ℂ)) = Finsupp.single 0 1 := rfl

/- English proof (translation)
Simplify using `[comb, Finsupp.support_single_ne_zero _ one_ne_zero, heisO_zero_eq]`.
-/
theorem comb_single_zero' (S' T : HSp D) (u : WO S' T → ℂ) :
    comb ψ S' T (Finsupp.single 0 1) u = u := by
  simp [comb, Finsupp.support_single_ne_zero _ one_ne_zero, heisO_zero_eq]

/- English proof (translation)
Simplify using `only [trc, Finsupp.support_single_ne_zero (1 : GA D V) (one_ne_zero (α := ℂ)), Finset.sum_singleton, Finsupp.single_eq_same, one_smul]`. Use function extensionality and compare the values at `x`. Use `show u (x * 1) = u x`. Rewrite using `[mul_one]`.
-/
theorem trc_single_one' {V : HSp D} (u : GA D V → ℂ) : trc (Finsupp.single 1 1) u = u := by
  simp only [trc, Finsupp.support_single_ne_zero (1 : GA D V) (one_ne_zero (α := ℂ)), Finset.sum_singleton, Finsupp.single_eq_same, one_smul]
  funext x
  show u (x * 1) = u x
  rw [mul_one]

/- English proof (translation)
Simplify using `only [value, integrand, List.ofFn_zero, conv_nil', aconv_singleton', trc_single_one']`. Rewrite using `[GlobalTheory.PosOne.comb, Finsupp.sum_single_index (by simp)]`. Simplify using `[aconv_nil', comb_single_zero']`.
-/
theorem value_zero_eq (Q : Fin 0 → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) :
    value Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ = integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ 1 1 := by
  simp only [value, integrand, List.ofFn_zero, conv_nil', aconv_singleton', trc_single_one']
  rw [GlobalTheory.PosOne.comb, Finsupp.sum_single_index (by simp)]
  simp [aconv_nil', comb_single_zero']
end

end GlobalTheory.QVal

namespace GlobalTheory.QVal

/- English proof (translation)
Introduce `D ψ _ σ S Q _ μ₁ ρ₁ μ₂ ρ₂ hN c₁ c₂ f₁ f₂ φ f g h₁ h₂ _`. Take `⟨-, -, -, -, e1, e2, e3, e4⟩` from `hN`. Establish `hP : ¬ ∃ v, places Q v` using `fun ⟨_, i, _⟩ => i.elim0`. Use `haveI : Subsingleton (GlobalTheory.FinPl.grpAt S.J.W (places Q)) := by`. Rewrite using `[grpAt_eq_bot S.J.W hP]`.

Use `infer_instance`. Use `haveI : Subsingleton (GlobalTheory.FinPl.grpAt S.B'.V (places Q)) := by`. Rewrite using `[grpAt_eq_bot S.B'.V hP]`. Use `infer_instance`. Simplify using `only [IsEmpty.forall_iff, Set.setOf_true] at e1 e2 e3 e4`.

Use `⟨fun x => integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x.1 1, ?_, fun q => ?_⟩` and prove the remaining obligations. Use `quotient_integral_of_subsingleton ρ₁ μ₁ e2 e1 (fun x => integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x.1 1)` as an intermediate fact. Simplify `this` using `[value_zero_eq]`. Use `quotient_integral_of_subsingleton ρ₂ μ₂ e4 e3 (fun y => integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ q.1 y.1)` as an intermediate fact. Simplify using `using this`.
-/
theorem valQr_zero : ∀ D : D7, ValQr D 0 := by
  intro D ψ _ σ S Q _ μ₁ ρ₁ μ₂ ρ₂ hN c₁ c₂ f₁ f₂ φ f g h₁ h₂ _
  obtain ⟨-, -, -, -, e1, e2, e3, e4⟩ := hN
  have hP : ¬ ∃ v, places Q v := fun ⟨_, i, _⟩ => i.elim0
  haveI : Subsingleton (GlobalTheory.FinPl.grpAt S.J.W (places Q)) := by
    rw [grpAt_eq_bot S.J.W hP]; infer_instance
  haveI : Subsingleton (GlobalTheory.FinPl.grpAt S.B'.V (places Q)) := by
    rw [grpAt_eq_bot S.B'.V hP]; infer_instance
  simp only [IsEmpty.forall_iff, Set.setOf_true] at e1 e2 e3 e4
  refine ⟨fun x => integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x.1 1, ?_, fun q => ?_⟩
  · have := quotient_integral_of_subsingleton ρ₁ μ₁ e2 e1 (fun x => integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x.1 1)
    simpa [value_zero_eq] using this
  · have := quotient_integral_of_subsingleton ρ₂ μ₂ e4 e3 (fun y => integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ q.1 y.1)
    simpa using this

end GlobalTheory.QVal
