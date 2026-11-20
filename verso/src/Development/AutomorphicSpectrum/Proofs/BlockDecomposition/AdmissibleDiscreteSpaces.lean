import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TreeParts

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.AdmDiscFin

section Dual

variable {K : Type} [Group K]

def shiftL (Y : Submodule ℂ (K → ℂ)) (hY : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y) (k : K) : Y →ₗ[ℂ] Y where
  toFun f := ⟨fun x => f.1 (k * x), hY f.1 f.2 k⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def dualRep (Y : Submodule ℂ (K → ℂ)) (hY : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y) :
    Representation ℂ K (Module.Dual ℂ Y) where
  toFun k := (shiftL Y hY k).dualMap
  map_one' := by
    refine LinearMap.ext fun ξ => LinearMap.ext fun f => ?_
    change ξ (shiftL Y hY 1 f) = ξ f
    congr 1
    exact Subtype.ext (funext fun x => by simp [shiftL])
  map_mul' k l := by
    refine LinearMap.ext fun ξ => LinearMap.ext fun f => ?_
    change ξ (shiftL Y hY (k * l) f) = ξ (shiftL Y hY l (shiftL Y hY k f))
    congr 1
    exact Subtype.ext (funext fun x => by simp [shiftL, mul_assoc])

/- English proof (translation)
Introduce `f hf`. Set `ev : Module.Dual ℂ Y` to `(LinearMap.proj (1 : K)).comp Y.subtype`. Use `Submodule.subset_span ⟨Module.Dual.eval ℂ Y ⟨f, hf⟩, ev, funext fun k => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f k = f (k * 1)`. Rewrite using `[mul_one]`.
-/
theorem le_coeffSpan_dualRep (Y : Submodule ℂ (K → ℂ)) (hY : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y) :
    Y ≤ GlobalTheory.Published.AutFin.coeffSpan (dualRep Y hY) := by
  intro f hf
  let ev : Module.Dual ℂ Y := (LinearMap.proj (1 : K)).comp Y.subtype
  refine Submodule.subset_span ⟨Module.Dual.eval ℂ Y ⟨f, hf⟩, ev, funext fun k => ?_⟩
  change f k = f (k * 1)
  rw [mul_one]

/- English proof (translation)
Introduce `ℓ ξ`. Set `ev : K → Module.Dual ℂ Y` to `fun x => (LinearMap.proj x).comp Y.subtype`. Establish `hspan : Submodule.span ℂ (Set.range ev) = ⊤`. Establish `h0 : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥`. Rewrite using `[eq_bot_iff]`.

Introduce `v hv`. Rewrite `hv` using `[Submodule.mem_dualCoannihilator]`. Establish `h2 : ∀ x, v.1 x = 0` using `fun x => hv _ (Submodule.subset_span ⟨x, rfl⟩)`. Rewrite using `[Submodule.mem_bot]`. Conclude with `Subtype.ext (funext h2)`.

Rewrite using `[← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), h0, Submodule.dualAnnihilator_bot]`. Take `⟨f, rfl⟩` from `(Module.evalEquiv ℂ Y).surjective ℓ`. Establish `key : ∀ ξ ∈ Submodule.span ℂ (Set.range ev), Continuous fun k => ξ (shiftL Y hY k f)`. Introduce `ξ hl`. Proceed by induction on `hl using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨x, rfl⟩` from `hx`. Conclude with `(hc f.1 f.2).comp (continuous_id.mul continuous_const)`. Consider the case `zero => exact continuous_const`. Consider the case `add x y _ _ hx hy => exact hx.add hy`.

Consider the case `smul r x _ hx => exact hx.const_smul r`. Conclude with `key ξ (hspan ▸ Submodule.mem_top)`.
-/
theorem isContRep_dualRep [TopologicalSpace K] [ContinuousMul K] (Y : Submodule ℂ (K → ℂ))
    (hY : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y) [FiniteDimensional ℂ Y] (hc : ∀ f ∈ Y, Continuous f) :
    GlobalTheory.Published.AutFin.IsContRep (dualRep Y hY) := by
  intro ℓ ξ
  let ev : K → Module.Dual ℂ Y := fun x => (LinearMap.proj x).comp Y.subtype
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    have h0 : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      have h2 : ∀ x, v.1 x = 0 := fun x => hv _ (Submodule.subset_span ⟨x, rfl⟩)
      rw [Submodule.mem_bot]
      exact Subtype.ext (funext h2)
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), h0,
      Submodule.dualAnnihilator_bot]
  obtain ⟨f, rfl⟩ := (Module.evalEquiv ℂ Y).surjective ℓ
  have key : ∀ ξ ∈ Submodule.span ℂ (Set.range ev), Continuous fun k => ξ (shiftL Y hY k f) := by
    intro ξ hl
    induction hl using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, rfl⟩ := hx
      exact (hc f.1 f.2).comp (continuous_id.mul continuous_const)
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul r x _ hx => exact hx.const_smul r
  exact key ξ (hspan ▸ Submodule.mem_top)

end Dual

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {M : ℕ}

/- English proof (translation)
Establish `h1 : Continuous fun k : Kinf E M => (Unitary.toUnits k : GL (Fin M) (Cinf E))` using `Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_subtype_val.star⟩`. Establish `e : (fun k : Kinf E M => φ.1 (g * infGL E M (Unitary.toUnits k))) = fun k => chart φ.1 g (toL (Unitary.toUnits k : GL (Fin M) (Cinf E)).val)`. Use function extensionality and compare the values at `k`. Rewrite using `[chart_val]`. Rewrite using `[e]`.

Establish `hc : ContinuousOn (chart φ.1 g) (invSet E M)` using `(φ.2 g).continuousOn`. Establish `h3' : Continuous fun k : Kinf E M => ((Unitary.toUnits k : GL (Fin M) (Cinf E)) : Matrix (Fin M) (Fin M) (Cinf E))` using `(Units.continuous_val (M := Matrix (Fin M) (Fin M) (Cinf E))).comp h1`. Establish `h3 : Continuous fun k : Kinf E M => toL ((Unitary.toUnits k : GL (Fin M) (Cinf E)) : Matrix (Fin M) (Fin M) (Cinf E))` using `h3'`. Conclude with `hc.comp_continuous h3 fun k => val_mem_invSet _`.
-/
theorem continuous_slice (φ : Sm E M) (g : GA E M) :
    Continuous fun k : Kinf E M => φ.1 (g * infGL E M (Unitary.toUnits k)) := by
  have h1 : Continuous fun k : Kinf E M => (Unitary.toUnits k : GL (Fin M) (Cinf E)) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_subtype_val.star⟩
  have e : (fun k : Kinf E M => φ.1 (g * infGL E M (Unitary.toUnits k))) =
      fun k => chart φ.1 g (toL (Unitary.toUnits k : GL (Fin M) (Cinf E)).val) := by
    funext k
    rw [chart_val]
  rw [e]
  have hc : ContinuousOn (chart φ.1 g) (invSet E M) := (φ.2 g).continuousOn
  have h3' : Continuous fun k : Kinf E M =>
      ((Unitary.toUnits k : GL (Fin M) (Cinf E)) : Matrix (Fin M) (Fin M) (Cinf E)) :=
    (Units.continuous_val (M := Matrix (Fin M) (Fin M) (Cinf E))).comp h1
  have h3 : Continuous fun k : Kinf E M =>
      toL ((Unitary.toUnits k : GL (Fin M) (Cinf E)) : Matrix (Fin M) (Fin M) (Cinf E)) := h3'
  exact hc.comp_continuous h3 fun k => val_mem_invSet _

/- English proof (translation)
Introduce `E _ _ _ M K' W' hK' hW' V hV`. Use `haveI := hW'`. Establish `hsc : ∀ (τ : E →+* ℂ) (u : ℂ), ∃ c : ℂ, ∀ ψ ∈ V, cap τ u ψ = c • ψ` using `fun τ u => GlobalTheory.DiscLocEx.exists_scalarD hV (Algebra.subset_adjoin ⟨τ, u, rfl⟩) (GlobalTheory.SpehInfChar.cap_commute_act τ u)`. Use `choose c hc using hsc`. Set `Y : Submodule ℂ (Kinf E M → ℂ)` to `Submodule.span ℂ {f | ∃ φ : Sm E M, φ ∈ V ∧ TypeB K' W' φ ∧ ∃ g : GA E M, f = fun k => φ.1 (g * infGL E M (Unitary.toUnits k))}`.

Establish `hYW : Y ≤ W'`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨φ, -, hφ, g, rfl⟩`. Conclude with `hφ.2 g`. Use `haveI : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le hYW`.

Establish `hYl : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y`. Introduce `f hf k`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem f hf`. Take `⟨φ, hφV, hφ, g, rfl⟩` from `hf`.

Use `Submodule.subset_span ⟨φ, hφV, hφ, g * infGL E M (Unitary.toUnits k), funext fun x => ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, mul_assoc]`. Consider the case `zero => exact Y.zero_mem`. Consider the case `add x y _ _ hx hy => exact Y.add_mem hx hy`. Consider the case `smul r x _ hx => exact Y.smul_mem r hx`.

Establish `hYc : ∀ f ∈ Y, Continuous f`. Introduce `f hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem f hf`. Take `⟨φ, -, -, g, rfl⟩` from `hf`.

Conclude with `continuous_slice φ g`. Consider the case `zero => exact continuous_const`. Consider the case `add x y _ _ hx hy => exact hx.add hy`. Consider the case `smul r x _ hx => exact hx.const_smul r`. Use `haveI hF := PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E M K' hK' (Module.Dual ℂ Y) (dualRep Y hYl) (isContRep_dualRep Y hYl hYc) c`.

Establish `hle : {φ | φ ∈ V ∧ TypeB K' W' φ} ⊆ GlobalTheory.Published.AutFinGL.forms K' (dualRep Y hYl) c`. Introduce and unpack `φ ⟨hφV, hφ⟩`. Use `⟨hV.aut φ hφV, fun k hk => Subtype.ext (funext fun g => hφ.1 k hk g), fun g => ?_, fun τ u => hc τ u φ hφV⟩` and prove the remaining obligations. Conclude with `le_coeffSpan_dualRep Y hYl (Submodule.subset_span ⟨φ, hφV, hφ, g, rfl⟩)`. Conclude with `Submodule.finiteDimensional_of_le (Submodule.span_mono hle)`.
-/
theorem admissible_discrete_spaces : PositivityTheory.Rg.BcB.SpectralAccumulation.AdmDisc := by
  intro E _ _ _ M K' W' hK' hW' V hV
  haveI := hW'
  have hsc : ∀ (τ : E →+* ℂ) (u : ℂ), ∃ c : ℂ, ∀ ψ ∈ V, cap τ u ψ = c • ψ := fun τ u =>
    GlobalTheory.DiscLocEx.exists_scalarD hV (Algebra.subset_adjoin ⟨τ, u, rfl⟩) (GlobalTheory.SpehInfChar.cap_commute_act τ u)
  choose c hc using hsc
  let Y : Submodule ℂ (Kinf E M → ℂ) := Submodule.span ℂ
    {f | ∃ φ : Sm E M, φ ∈ V ∧ TypeB K' W' φ ∧ ∃ g : GA E M, f = fun k => φ.1 (g * infGL E M (Unitary.toUnits k))}
  have hYW : Y ≤ W' := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ, -, hφ, g, rfl⟩
    exact hφ.2 g
  haveI : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le hYW
  have hYl : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y := by
    intro f hf k
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨φ, hφV, hφ, g, rfl⟩ := hf
      refine Submodule.subset_span ⟨φ, hφV, hφ, g * infGL E M (Unitary.toUnits k), funext fun x => ?_⟩
      simp only [map_mul, mul_assoc]
    | zero => exact Y.zero_mem
    | add x y _ _ hx hy => exact Y.add_mem hx hy
    | smul r x _ hx => exact Y.smul_mem r hx
  have hYc : ∀ f ∈ Y, Continuous f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨φ, -, -, g, rfl⟩ := hf
      exact continuous_slice φ g
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul r x _ hx => exact hx.const_smul r
  haveI hF := PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E M K' hK' (Module.Dual ℂ Y) (dualRep Y hYl)
    (isContRep_dualRep Y hYl hYc) c
  have hle : {φ | φ ∈ V ∧ TypeB K' W' φ} ⊆ GlobalTheory.Published.AutFinGL.forms K' (dualRep Y hYl) c := by
    rintro φ ⟨hφV, hφ⟩
    refine ⟨hV.aut φ hφV, fun k hk => Subtype.ext (funext fun g => hφ.1 k hk g), fun g => ?_,
      fun τ u => hc τ u φ hφV⟩
    exact le_coeffSpan_dualRep Y hYl (Submodule.subset_span ⟨φ, hφV, hφ, g, rfl⟩)
  exact Submodule.finiteDimensional_of_le (Submodule.span_mono hle)

end GlobalTheory.CompanionTheory.AdmDiscFin

end
