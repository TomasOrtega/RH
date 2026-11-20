import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearIndependentOfIsParamFunVStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageLatticeStabilizerParamsOffSetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

/- English proof (translation)
Introduce `D c hc j hj s hs ι x B hpar hB`. Establish `hlat` using `(GlobalTheory.T.thetaChainStage_lattice_stabilizer_params_off_set D c hc j hj s hs).2`. Rewrite using `[linearIndependent_iff']`. Introduce `t a hsum i₀ hi₀`. Take `⟨hne0, _⟩` from `hpar i₀`.

Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, PiLocalization₂.val (x i₀) v ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hne0` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `w`. Simplify `h w` using `[PiLocalization₂.val]`. Set `p : ι → Prop` to `fun i => PiLocalization₂.val (x i) v ≠ 0`. Set `f : {i // p i} → (GA D s.V → ℂ)` to `fun i g => conj (PiLocalization₂.val (x i.1) v g)`.

Establish `hli : LinearIndependent ℂ f`. Use `GlobalTheory.T.linearIndependent_of_ne_zero_of_isParamFunV_of_separated D s.V c.S {i // p i} f (fun i => B i.1) ?_ ?_ ?_` and prove the remaining obligations. Introduce `i h0`. Apply `i.2` to reduce the goal to its premises. Use function extensionality and compare the values at `g`.

Use `congrFun h0 g` as an intermediate fact. Simplify `this` using `[f]`. Introduce `i`. Establish `h1` using `(hpar i.1).2 v i.2`. Unfold `ParFun at h1`.

Conclude with `(hlat _ _).1 h1`. Introduce `i i' hii'`. Conclude with `hB i.1 i'.1 (fun h => hii' (Subtype.ext h))`. Rewrite `hli` using `[linearIndependent_iff']`. Establish `hsum' : ∀ g, ∑ i ∈ t, a i * PiLocalization₂.val (x i) v g = 0`.

Introduce `g`. Use `congrArg (fun y : s.CC c => PiLocalization₂.val y v g) hsum` as an intermediate fact. Simplify `this` using `[PiLocalization₂.val, Finset.sum_apply]`. Establish `key` using `hli (t.subtype p) (fun i => conj (a i.1)) ?_ ⟨i₀, hv⟩ (by simp [Finset.mem_subtype, hi₀])`. Simplify using `using key`.

Use function extensionality and compare the values at `g`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, f, Pi.zero_apply]`. Rewrite using `[Finset.sum_subtype_eq_sum_filter (f := fun i => conj (a i) * conj (PiLocalization₂.val (x i) v g)) (p := p)]`. Rewrite using `[Finset.sum_filter_of_ne]`.

Rewrite using `[← map_zero (starRingEnd ℂ), ← hsum' g, map_sum]`. Simplify using `[map_mul]`. Introduce `i _ hne h0`. Apply `hne` to reduce the goal to its premises. Simplify using `[h0]`.
-/
theorem parIndep : ∀ D : D7, ParIndep D := by
  intro D c hc j hj s hs ι x B hpar hB
  classical
  have hlat := (GlobalTheory.T.thetaChainStage_lattice_stabilizer_params_off_set D c hc j hj s hs).2
  rw [linearIndependent_iff']
  intro t a hsum i₀ hi₀
  obtain ⟨hne0, _⟩ := hpar i₀
  obtain ⟨v, hv⟩ : ∃ v, PiLocalization₂.val (x i₀) v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne0
    apply Subtype.ext
    apply LinearMap.ext
    intro w
    simpa [PiLocalization₂.val] using h w
  let p : ι → Prop := fun i => PiLocalization₂.val (x i) v ≠ 0
  let f : {i // p i} → (GA D s.V → ℂ) := fun i g => conj (PiLocalization₂.val (x i.1) v g)
  have hli : LinearIndependent ℂ f := by
    refine GlobalTheory.T.linearIndependent_of_ne_zero_of_isParamFunV_of_separated D s.V c.S {i // p i} f (fun i => B i.1) ?_ ?_ ?_
    · intro i h0
      apply i.2
      funext g
      have := congrFun h0 g
      simpa [f] using this
    · intro i
      have h1 := (hpar i.1).2 v i.2
      unfold ParFun at h1
      exact (hlat _ _).1 h1
    · intro i i' hii'
      exact hB i.1 i'.1 (fun h => hii' (Subtype.ext h))
  rw [linearIndependent_iff'] at hli
  have hsum' : ∀ g, ∑ i ∈ t, a i * PiLocalization₂.val (x i) v g = 0 := by
    intro g
    have := congrArg (fun y : s.CC c => PiLocalization₂.val y v g) hsum
    simpa [PiLocalization₂.val, Finset.sum_apply] using this
  have key := hli (t.subtype p) (fun i => conj (a i.1)) ?_ ⟨i₀, hv⟩ (by simp [Finset.mem_subtype, hi₀])
  · simpa using key
  · funext g
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, f, Pi.zero_apply]
    rw [Finset.sum_subtype_eq_sum_filter (f := fun i => conj (a i) * conj (PiLocalization₂.val (x i) v g)) (p := p)]
    rw [Finset.sum_filter_of_ne]
    · rw [← map_zero (starRingEnd ℂ), ← hsum' g, map_sum]
      simp [map_mul]
    · intro i _ hne h0
      apply hne
      simp [h0]

end GlobalTheory.ChainOnto
