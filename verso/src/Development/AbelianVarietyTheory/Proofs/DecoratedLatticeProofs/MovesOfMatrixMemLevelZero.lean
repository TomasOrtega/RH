import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabilizesSelfDualIffFrameMatrixStabilizesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticePrescribedSplitPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

open GlobalTheory.StepData GlobalTheory.RootEx GlobalTheory.SymChain

namespace GlobalTheory.LevX

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

open MeasureTheory IsDedekindDomain NumberField Matrix ValuativeRel in
open scoped TensorProduct nonZeroDivisors in
open scoped Pointwise in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ} in

/- English proof (translation)
Simplify using `[_root_.GlobalTheory.StepData.typeFrame, _root_.GlobalTheory.StepData.LatFrame.bas, _root_.GlobalTheory.RootEx.embA, _root_.GlobalTheory.RootEx.embX, Matrix.fromBlocks_multiply]`.
-/
theorem _root_.GlobalTheory.LevX.conj_embX_val (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) (g : GL n k) :
    ((_root_.GlobalTheory.StepData.typeFrame ϖ ord).bas⁻¹ *
        _root_.GlobalTheory.RootEx.embX c g *
        (_root_.GlobalTheory.StepData.typeFrame ϖ ord).bas).val.toBlocks₁₁ = g.val := by
  simp [_root_.GlobalTheory.StepData.typeFrame, _root_.GlobalTheory.StepData.LatFrame.bas,
    _root_.GlobalTheory.RootEx.embA, _root_.GlobalTheory.RootEx.embX, Matrix.fromBlocks_multiply]

open MeasureTheory IsDedekindDomain NumberField Matrix ValuativeRel in
open scoped TensorProduct nonZeroDivisors in
open scoped Pointwise in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ} in

/- English proof (translation)
Use `set b := (_root_.GlobalTheory.StepData.typeFrame ϖ ord).bas with hb`. Establish `hconj : b⁻¹ * _root_.GlobalTheory.RootEx.embX c g * b ∈ _root_.GlobalTheory.SplitWeil.KO k (n ⊕ Fin c)`. Unfold `_root_.GlobalTheory.StepData.stabLat at h`. Simplify `Subgroup.mem_comap.1 h` using `[MulAut.conj_apply]`. Take `⟨h₁, h₂⟩` from `(_root_.GlobalTheory.SplitFlip.mem_KO_iff _).1 hconj`.

Establish `hinv : (b⁻¹ * _root_.GlobalTheory.RootEx.embX c g * b)⁻¹ = b⁻¹ * _root_.GlobalTheory.RootEx.embX c g⁻¹ * b`. Simplify using `[_root_.mul_inv_rev, mul_assoc]`. Rewrite using `[_root_.GlobalTheory.SplitFlip.mem_KO_iff]`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Establish `e` using `congrFun (congrFun (_root_.GlobalTheory.LevX.conj_embX_val ϖ ord g) i) j`.

Rewrite using `[← e]`. Conclude with `h₁ (Sum.inl i) (Sum.inl j)`. Establish `e` using `congrFun (congrFun (_root_.GlobalTheory.LevX.conj_embX_val ϖ ord g⁻¹) i) j`. Rewrite using `[← e]`. Use `h₂ (Sum.inl i) (Sum.inl j)` as an intermediate fact.

Rewrite `this` using `[hinv]`. Conclude with `this`.
-/
theorem _root_.GlobalTheory.LevX.mem_KO_of_embX_mem_stabLat (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) {g : GL n k}
    (h : _root_.GlobalTheory.RootEx.embX c g ∈
      _root_.GlobalTheory.StepData.stabLat (_root_.GlobalTheory.StepData.typeFrame ϖ ord).bas) :
    g ∈ _root_.GlobalTheory.SplitWeil.KO k n := by
  set b := (_root_.GlobalTheory.StepData.typeFrame ϖ ord).bas with hb
  have hconj : b⁻¹ * _root_.GlobalTheory.RootEx.embX c g * b ∈
      _root_.GlobalTheory.SplitWeil.KO k (n ⊕ Fin c) := by
    unfold _root_.GlobalTheory.StepData.stabLat at h
    simpa [MulAut.conj_apply] using Subgroup.mem_comap.1 h
  obtain ⟨h₁, h₂⟩ := (_root_.GlobalTheory.SplitFlip.mem_KO_iff _).1 hconj
  have hinv : (b⁻¹ * _root_.GlobalTheory.RootEx.embX c g * b)⁻¹ =
      b⁻¹ * _root_.GlobalTheory.RootEx.embX c g⁻¹ * b := by
    simp [_root_.mul_inv_rev, mul_assoc]
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have e := congrFun (congrFun (_root_.GlobalTheory.LevX.conj_embX_val ϖ ord g) i) j
    rw [← e]
    exact h₁ (Sum.inl i) (Sum.inl j)
  · have e := congrFun (congrFun (_root_.GlobalTheory.LevX.conj_embX_val ϖ ord g⁻¹) i) j
    rw [← e]
    have := h₂ (Sum.inl i) (Sum.inl j)
    rw [hinv] at this
    exact this

open MeasureTheory IsDedekindDomain NumberField Matrix ValuativeRel in
open scoped TensorProduct nonZeroDivisors in
open scoped Pointwise in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ} in
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hM i j) (hy j)`.
-/
private lemma mulVec_apply_mem_integer_of_entries_mem_integer {M : Matrix n n k}
    (hM : ∀ i j, M i j ∈ (ValuativeRel.valuation k).integer) {y : n → k}
    (hy : ∀ j, y j ∈ (ValuativeRel.valuation k).integer) (i : n) :
    (M *ᵥ y) i ∈ (ValuativeRel.valuation k).integer := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hM i j) (hy j)

open MeasureTheory IsDedekindDomain NumberField Matrix ValuativeRel in
open scoped TensorProduct nonZeroDivisors in
open scoped Pointwise in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ} in

/- English proof (translation)
Take `⟨h₁, h₂⟩` from `(_root_.GlobalTheory.SplitFlip.mem_KO_iff _).1 h`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `x ∈ (g : Matrix n n k) • _root_.GlobalTheory.SplitLat.stdLat k n ↔ _`. Rewrite using `[Submodule.mem_smul_pointwise_iff_exists]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩`. Rewrite `hy`, the goal using `[_root_.GlobalTheory.SplitLat.mem_std]`. Introduce `i`. Rewrite using `[Matrix.smul_eq_mulVec]`. Conclude with `mulVec_apply_mem_integer_of_entries_mem_integer h₁ hy i`.

Introduce `hx`. Use `⟨((g⁻¹ : GL n k) : Matrix n n k) • x, ?_, ?_⟩` and prove the remaining obligations. Rewrite `hx`, the goal using `[_root_.GlobalTheory.SplitLat.mem_std]`. Introduce `i`. Rewrite using `[Matrix.smul_eq_mulVec]`.

Conclude with `mulVec_apply_mem_integer_of_entries_mem_integer h₂ hx i`. Rewrite using `[smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]`.
-/
theorem _root_.GlobalTheory.LevX.smul_stdLat_of_mem_KO {g : GL n k} (h : g ∈ _root_.GlobalTheory.SplitWeil.KO k n) :
    g • _root_.GlobalTheory.SplitLat.stdLat k n = _root_.GlobalTheory.SplitLat.stdLat k n := by
  obtain ⟨h₁, h₂⟩ := (_root_.GlobalTheory.SplitFlip.mem_KO_iff _).1 h
  ext x
  change x ∈ (g : Matrix n n k) • _root_.GlobalTheory.SplitLat.stdLat k n ↔ _
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [_root_.GlobalTheory.SplitLat.mem_std] at hy ⊢
    intro i
    rw [Matrix.smul_eq_mulVec]
    exact mulVec_apply_mem_integer_of_entries_mem_integer h₁ hy i
  · intro hx
    refine ⟨((g⁻¹ : GL n k) : Matrix n n k) • x, ?_, ?_⟩
    · rw [_root_.GlobalTheory.SplitLat.mem_std] at hx ⊢
      intro i
      rw [Matrix.smul_eq_mulVec]
      exact mulVec_apply_mem_integer_of_entries_mem_integer h₂ hx i
    · rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

end GlobalTheory.LevX
