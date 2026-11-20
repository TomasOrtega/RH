import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiltZerosUntiltFrobeniusDoubleSeriesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisPlusSeriesWithThetaResiduesStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PSer TensorProduct
open scoped Formalism.Per
/- English proof (translation)
Introduce `l _ P AI T h hh μ hμ hne`. Take `⟨S, θ, hS, hker, hq, hb⟩` from `hser l P AI T`. Set `μ' : Fin h → ℂ_[l]` to `fun i => θ ⟨μ i, (hS _).2 (hμ i)⟩`. Establish `hμ' : μ' ≠ 0`. Take `⟨i, hi⟩` from `hne`.

Introduce `h0`. Conclude with `hi ((hker ⟨μ i, (hS _).2 (hμ i)⟩).1 (congrFun h0 i))`. Take `⟨y, hy, hz, hind⟩` from `hcore l h μ' hh hμ'`. Use `choose b hplus hφ hev using fun a => hb h _ (y a) hh GlobalTheory.RingBasics.norm_p_lt (hy a)`. Use `choose hm hev using hev`.

Use `choose hq0 hq using hq`. Use `⟨b, hplus, hφ, ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc`. Establish `: c = 0`.

Use `hind c fun j _ => ?_` and prove the remaining obligations. Establish `e : ∀ x : P.R.B, ev P j x = P.ιB ((P.φB ^ j) x)` using `fun x => by`. Simplify using `only [ev, AlgHom.coe_pow]`. Establish `h1 : (∑ a, (⟨_, hq0 (c a)⟩ : S) * ⟨_, hm a j⟩) = 0`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `congrArg (fun x => P.ιB ((P.φB ^ j) x)) hc` as an intermediate fact. Simplify using `only [map_sum, map_smul, map_zero] at this`. Simplify using `only [AddSubmonoidClass.coe_finset_sum, Subring.coe_mul, e, ZeroMemClass.coe_zero]`. Simplify `this` using `only [Algebra.smul_def]`. Establish `h2` using `congrArg θ h1`.

Rewrite `h2` using `[map_sum, map_zero]`. Simplify `h2` using `only [map_mul, hq, hev]`. Conclude with `fun i => congrFun this i`. Establish `h2 : θ (∑ i : Fin h, (⟨μ i, (hS _).2 (hμ i)⟩ : S) * ⟨_, hm a i⟩) = 0`. Rewrite using `[map_sum]`.

Simplify `hz a` using `only [map_mul, hev]`. Use `(hker _).1 h2` as an intermediate fact. Simplify `this` using `only [AddSubmonoidClass.coe_finset_sum, Subring.coe_mul]`.
-/
theorem GlobalTheory.PMon.exI_of_ser_core (hser : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI), ∃ (S : Subring P.R.BdR) (θ : ↥S →+* ℂ_[l]), (∀ x, x ∈ S ↔ x ∈ Fil P 0) ∧ (∀ x : ↥S, θ x = 0 ↔ (x : P.R.BdR) ∈ Fil P 1) ∧ (∀ c : ℚ_[l], ∃ hm, θ ⟨algebraMap ℚ_[l] P.R.BdR c, hm⟩ = algebraMap ℚ_[l] ℂ_[l] c) ∧ ∀ (h : ℕ) (r : ℝ) (y : ℕ → Formalism.Per.Fl l), 2 ≤ h → r < 1 → (∀ k, ‖sh (y k)‖ ≤ r) → ∃ b : P.R.B, Plus T b ∧ P.φB^[h] b = (l : P.R.B) * b ∧ ∀ j : ℕ, ∃ hm, θ ⟨ev P j b, hm⟩ = abelian₂ h j y) (hcore : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 2 ≤ h → μ ≠ 0 → ∃ y : Fin h → ℕ → Formalism.Per.Fl l, (∀ a k, ‖sh (y a k)‖ ≤ ‖(l : ℂ_[l])‖) ∧ (∀ a, ∑ i : Fin h, μ i * abelian₂ h i (y a) = 0) ∧ ∀ c : Fin h → ℚ_[l], (∀ j : ℕ, j < 2 → ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * abelian₂ h j (y a) = 0) → c = 0) : ExI := by
  intro l _ P AI T h hh μ hμ hne
  obtain ⟨S, θ, hS, hker, hq, hb⟩ := hser l P AI T
  let μ' : Fin h → ℂ_[l] := fun i => θ ⟨μ i, (hS _).2 (hμ i)⟩
  have hμ' : μ' ≠ 0 := by
    obtain ⟨i, hi⟩ := hne
    intro h0
    exact hi ((hker ⟨μ i, (hS _).2 (hμ i)⟩).1 (congrFun h0 i))
  obtain ⟨y, hy, hz, hind⟩ := hcore l h μ' hh hμ'
  choose b hplus hφ hev using fun a => hb h _ (y a) hh GlobalTheory.RingBasics.norm_p_lt (hy a)
  choose hm hev using hev
  choose hq0 hq using hq
  refine ⟨b, hplus, hφ, ?_, fun a => ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    have : c = 0 := by
      refine hind c fun j _ => ?_
      have e : ∀ x : P.R.B, ev P j x = P.ιB ((P.φB ^ j) x) := fun x => by
        simp only [ev, AlgHom.coe_pow]
      have h1 : (∑ a, (⟨_, hq0 (c a)⟩ : S) * ⟨_, hm a j⟩) = 0 := by
        apply Subtype.ext
        have := congrArg (fun x => P.ιB ((P.φB ^ j) x)) hc
        simp only [map_sum, map_smul, map_zero] at this
        simp only [AddSubmonoidClass.coe_finset_sum, Subring.coe_mul, e, ZeroMemClass.coe_zero]
        simpa only [Algebra.smul_def] using this
      have h2 := congrArg θ h1
      rw [map_sum, map_zero] at h2
      simpa only [map_mul, hq, hev] using h2
    exact fun i => congrFun this i
  · have h2 : θ (∑ i : Fin h, (⟨μ i, (hS _).2 (hμ i)⟩ : S) * ⟨_, hm a i⟩) = 0 := by
      rw [map_sum]
      simpa only [map_mul, hev] using hz a
    have := (hker _).1 h2
    simpa only [AddSubmonoidClass.coe_finset_sum, Subring.coe_mul] using this

/- English proof (translation)
The claim follows from `GlobalTheory.PMon.exI_of_ser_core GlobalTheory.T.exists_BcrisPlus_series_with_theta_residues GlobalTheory.T.exists_tilt_zeros_untiltFrobeniusDoubleSeries`.
-/
theorem GlobalTheory.PMon.exI_main : ExI := GlobalTheory.PMon.exI_of_ser_core GlobalTheory.T.exists_BcrisPlus_series_with_theta_residues GlobalTheory.T.exists_tilt_zeros_untiltFrobeniusDoubleSeries
