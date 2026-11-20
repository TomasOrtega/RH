import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTranslate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqOneOfNormPowTwoPowSubOneLt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TriStepMem

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt`. Consider the case `exact _root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt`. Consider the case `(apply _root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt ..)`.
-/
theorem eq_one_of_pow_two_pow (z : ℂ) (h : ∀ m : ℕ, ‖z ^ (2 ^ m) - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt
  | exact _root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt
  | (apply _root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt ..)

end GlobalTheory.TriStepMem

namespace GlobalTheory.TriStep

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

/- English proof (translation)
Introduce `D ψ σ S Q f hf hT`. Establish `hgl : Continuous Q.gl₂` using `(GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q.k Q.q S.B'.V _ Q.F.G₂ Q.gl₂ Q.loc₂).1.continuous`. Use `⟨fun y => ⟨fun γ hγ x => ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [rTrans]`. Rewrite using `[mul_assoc, hf.1 γ hγ]`.

Conclude with `hf.2.comp (continuous_id.mul continuous_const)`. Distinguish the cases in `h0 : ∃ x, f x ≠ 0`. Take `⟨x, hx⟩` from `h0`. Establish `hval : ∀ j : Q.L₂.J, f (x * Q.gl₂ j.1) = (Q.L₂.lam j : ℂ) * f x` using `fun j => by`. Use `congrFun (hT j) x` as an intermediate fact.

Simplify `this` using `[rTrans]`. Set `φ : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k → ℂ` to `fun g => f (x * Q.gl₂ g) / f x`. Establish `hφc : Continuous φ` using `(hf.2.comp (continuous_const.mul hgl)).div_const _`. Establish `hφ : ∀ j : Q.L₂.J, φ j.1 = (Q.L₂.lam j : ℂ)` using `fun j => by`. Simplify using `only [φ, hval j]`.

Clear the denominators using the available nonvanishing facts. Set `U : Set (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k)` to `(Q.L₂.J : Set _) ∩ φ ⁻¹' Metric.ball 1 (1 / 2)`. Establish `hU : U ∈ nhds (1 : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k)`. Use `(Q.co₂.1.inter (Metric.isOpen_ball.preimage hφc)).mem_nhds ⟨Q.L₂.J.one_mem, ?_⟩` and prove the remaining obligations. Use `hφ 1` as an intermediate fact.

Simplify using `only [OneMemClass.coe_one, map_one, Units.val_one] at this`. Simplify using `[this]`. Take `⟨K, hKo, hKU, -, -⟩` from `GlobalTheory.SmGL.exists_open_normalised_subgroup_subset Q.k (Q.n₂ ⊕ Fin (Q.c + 1)) U hU`. Use `⟨K, hKo, fun u hu => ?_⟩` and prove the remaining obligations. Establish `huJ : u ∈ Q.L₂.J` using `(hKU hu).1`.

Establish `hlam : (Q.L₂.lam ⟨u, huJ⟩ : ℂ) = 1`. Apply `GlobalTheory.TriStepMem.eq_one_of_pow_two_pow` to reduce the goal to its premises. Introduce `m`. Establish `hm : u ^ (2 ^ m) ∈ K` using `K.pow_mem hu _`. Establish `hmU` using `hKU hm`.

Establish `hmJ : u ^ (2 ^ m) ∈ Q.L₂.J` using `hmU.1`. Establish `e : (⟨u ^ (2 ^ m), hmJ⟩ : Q.L₂.J) = (⟨u, huJ⟩ : Q.L₂.J) ^ (2 ^ m)` using `rfl`. Establish `h2 : φ (u ^ (2 ^ m)) ∈ Metric.ball (1 : ℂ) (1 / 2)` using `hmU.2`. Rewrite `h2` using `[show u ^ (2 ^ m) = ((⟨u ^ (2 ^ m), hmJ⟩ : Q.L₂.J) : GL _ _) from rfl, hφ, e, map_pow, Units.val_pow_eq_pow_val, Metric.mem_ball, dist_eq_norm]`. Conclude with `h2`.

Use `hT ⟨u, huJ⟩` as an intermediate fact. Rewrite `this` using `[hlam, one_smul]`. Conclude with `this`. Use `push_neg at h0`. Use `⟨⊤, isOpen_univ, fun u _ => ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `g`. Simplify using `[rTrans, h0]`.
-/
theorem mem_space_of_typed : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S)
    (f : GA D S.B'.V → ℂ), IsContAut S.B'.V f → Q.Typed f → f ∈ GlobalTheory.TriStep.space Q := by
  intro D ψ σ S Q f hf hT
  have hgl : Continuous Q.gl₂ := (GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q.k Q.q S.B'.V _ Q.F.G₂ Q.gl₂ Q.loc₂).1.continuous
  refine ⟨fun y => ⟨fun γ hγ x => ?_, ?_⟩, ?_⟩
  · simp only [rTrans]
    rw [mul_assoc, hf.1 γ hγ]
  · exact hf.2.comp (continuous_id.mul continuous_const)
  · by_cases h0 : ∃ x, f x ≠ 0
    · obtain ⟨x, hx⟩ := h0
      have hval : ∀ j : Q.L₂.J, f (x * Q.gl₂ j.1) = (Q.L₂.lam j : ℂ) * f x := fun j => by
        have := congrFun (hT j) x
        simpa [rTrans] using this
      let φ : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k → ℂ := fun g => f (x * Q.gl₂ g) / f x
      have hφc : Continuous φ := (hf.2.comp (continuous_const.mul hgl)).div_const _
      have hφ : ∀ j : Q.L₂.J, φ j.1 = (Q.L₂.lam j : ℂ) := fun j => by
        simp only [φ, hval j]; field_simp
      let U : Set (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) := (Q.L₂.J : Set _) ∩ φ ⁻¹' Metric.ball 1 (1 / 2)
      have hU : U ∈ nhds (1 : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) := by
        refine (Q.co₂.1.inter (Metric.isOpen_ball.preimage hφc)).mem_nhds ⟨Q.L₂.J.one_mem, ?_⟩
        have := hφ 1
        simp only [OneMemClass.coe_one, map_one, Units.val_one] at this
        simp [this]
      obtain ⟨K, hKo, hKU, -, -⟩ := GlobalTheory.SmGL.exists_open_normalised_subgroup_subset Q.k (Q.n₂ ⊕ Fin (Q.c + 1)) U hU
      refine ⟨K, hKo, fun u hu => ?_⟩
      have huJ : u ∈ Q.L₂.J := (hKU hu).1
      have hlam : (Q.L₂.lam ⟨u, huJ⟩ : ℂ) = 1 := by
        apply GlobalTheory.TriStepMem.eq_one_of_pow_two_pow
        intro m
        have hm : u ^ (2 ^ m) ∈ K := K.pow_mem hu _
        have hmU := hKU hm
        have hmJ : u ^ (2 ^ m) ∈ Q.L₂.J := hmU.1
        have e : (⟨u ^ (2 ^ m), hmJ⟩ : Q.L₂.J) = (⟨u, huJ⟩ : Q.L₂.J) ^ (2 ^ m) := rfl
        have h2 : φ (u ^ (2 ^ m)) ∈ Metric.ball (1 : ℂ) (1 / 2) := hmU.2
        rw [show u ^ (2 ^ m) = ((⟨u ^ (2 ^ m), hmJ⟩ : Q.L₂.J) : GL _ _) from rfl, hφ, e, map_pow,
          Units.val_pow_eq_pow_val, Metric.mem_ball, dist_eq_norm] at h2
        exact h2
      have := hT ⟨u, huJ⟩
      rw [hlam, one_smul] at this
      exact this
    · push_neg at h0
      refine ⟨⊤, isOpen_univ, fun u _ => ?_⟩
      funext g
      simp [rTrans, h0]

end GlobalTheory.TriStep
end
