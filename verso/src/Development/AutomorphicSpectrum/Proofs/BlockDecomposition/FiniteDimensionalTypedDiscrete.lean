import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleDiscreteSpaces

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.FdV

open GlobalTheory.CompanionTheory.AdmDiscFin GlobalTheory.LevelTypeProj

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

/- English proof (translation)
Establish `h1 : Continuous fun k : Kinf E N => (Unitary.toUnits k : GL (Fin N) (Cinf E))` using `Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_subtype_val.star⟩`. Establish `e : (fun k : Kinf E N => φ.1 (g * infGL E N (Unitary.toUnits k))) = fun k => chart φ.1 g (toL (Unitary.toUnits k : GL (Fin N) (Cinf E)).val)`. Use function extensionality and compare the values at `k`. Rewrite using `[chart_val]`. Rewrite using `[e]`.

Establish `hc : ContinuousOn (chart φ.1 g) (invSet E N)` using `(φ.2 g).continuousOn`. Establish `h3' : Continuous fun k : Kinf E N => ((Unitary.toUnits k : GL (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E))` using `(Units.continuous_val (M := Matrix (Fin N) (Fin N) (Cinf E))).comp h1`. Establish `h3 : Continuous fun k : Kinf E N => toL ((Unitary.toUnits k : GL (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E))` using `h3'`. Conclude with `hc.comp_continuous h3 fun k => val_mem_invSet _`.
-/
theorem continuous_sliceTC (φ : Sm E N) (g : GA E N) :
    Continuous fun k : Kinf E N => φ.1 (g * infGL E N (Unitary.toUnits k)) := by
  have h1 : Continuous fun k : Kinf E N => (Unitary.toUnits k : GL (Fin N) (Cinf E)) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_subtype_val.star⟩
  have e : (fun k : Kinf E N => φ.1 (g * infGL E N (Unitary.toUnits k))) =
      fun k => chart φ.1 g (toL (Unitary.toUnits k : GL (Fin N) (Cinf E)).val) := by
    funext k
    rw [chart_val]
  rw [e]
  have hc : ContinuousOn (chart φ.1 g) (invSet E N) := (φ.2 g).continuousOn
  have h3' : Continuous fun k : Kinf E N =>
      ((Unitary.toUnits k : GL (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E)) :=
    (Units.continuous_val (M := Matrix (Fin N) (Fin N) (Cinf E))).comp h1
  have h3 : Continuous fun k : Kinf E N =>
      toL ((Unitary.toUnits k : GL (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E)) := h3'
  exact hc.comp_continuous h3 fun k => val_mem_invSet _

/- English proof (translation)
Use `haveI := hW`. Take `⟨ψ, hψV, hψ0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hV.ne_bot`. Establish `hadm : PrAdm.SupSpansPsiPart V ψ = V` using `(hV.irred _ (PrAdm.admissible_span_le V ψ) (PrAdm.isStable_admissible_span hV.stable ψ)).resolve_left fun h => hψ0 (by`. Establish `h2` using `PrAdm.mem_admissible_span_self hψV`. Rewrite `h2` using `[h]`.

Simplify using `using h2)`. Set `Y : Submodule ℂ (Kinf E N → ℂ)` to `Submodule.span ℂ {f | ∃ φ : Sm E N, φ ∈ typed V K W ∧ ∃ g : GA E N, f = fun k => φ.1 (g * infGL E N (Unitary.toUnits k))}`. Establish `hYW : Y ≤ W`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨φ, hφ, g, rfl⟩`.

Conclude with `hφ.2.2 g`. Use `haveI : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le hYW`. Establish `hYl : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y`. Introduce `f hf k`. Proceed by induction on `hf using Submodule.span_induction with`.

Consider the case `mem f hf`. Take `⟨φ, hφ, g, rfl⟩` from `hf`. Use `Submodule.subset_span ⟨φ, hφ, g * infGL E N (Unitary.toUnits k), funext fun x => ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, mul_assoc]`. Consider the case `zero => exact Y.zero_mem`.

Consider the case `add x y _ _ hx hy => exact Y.add_mem hx hy`. Consider the case `smul r x _ hx => exact Y.smul_mem r hx`. Establish `hYc : ∀ f ∈ Y, Continuous f`. Introduce `f hf`. Proceed by induction on `hf using Submodule.span_induction with`.

Consider the case `mem f hf`. Take `⟨φ, -, g, rfl⟩` from `hf`. Conclude with `continuous_sliceTC φ g`. Consider the case `zero => exact continuous_const`. Consider the case `add x y _ _ hx hy => exact hx.add hy`.

Consider the case `smul r x _ hx => exact hx.const_smul r`. Establish `hF` using `PrAdm.finiteDimensional_admissible_isotypic hV.aut (hV.aut ψ hψV) hK (dualRep Y hYl) (isContRep_dualRep Y hYl hYc)`. Rewrite `hF` using `[hadm]`. Use `Submodule.finiteDimensional_of_le (S₂ := V ⊓ typePart K (dualRep Y hYl)) ?_` and prove the remaining obligations. Introduce `φ hφ`.

Use `⟨hφ.1, fun k hk => Subtype.ext (funext fun g => hφ.2.1 k hk g), fun g => ?_⟩` and prove the remaining obligations. Conclude with `le_coeffSpan_dualRep Y hYl (Submodule.subset_span ⟨φ, hφ, g, rfl⟩)`.
-/
theorem fd_typed {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ} (V : Submodule ℂ (Sm E N))
    (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) (hV : IsDiscrete V)
    (hK : IsOpen (K : Set (GL (Fin N) (Af E)))) (hW : FiniteDimensional ℂ W) :
    FiniteDimensional ℂ (typed V K W) := by
  haveI := hW
  obtain ⟨ψ, hψV, hψ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV.ne_bot
  have hadm : PrAdm.SupSpansPsiPart V ψ = V :=
    (hV.irred _ (PrAdm.admissible_span_le V ψ) (PrAdm.isStable_admissible_span hV.stable ψ)).resolve_left fun h => hψ0 (by
      have h2 := PrAdm.mem_admissible_span_self hψV
      rw [h] at h2
      simpa using h2)
  let Y : Submodule ℂ (Kinf E N → ℂ) := Submodule.span ℂ
    {f | ∃ φ : Sm E N, φ ∈ typed V K W ∧ ∃ g : GA E N, f = fun k => φ.1 (g * infGL E N (Unitary.toUnits k))}
  have hYW : Y ≤ W := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ, hφ, g, rfl⟩
    exact hφ.2.2 g
  haveI : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le hYW
  have hYl : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y := by
    intro f hf k
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨φ, hφ, g, rfl⟩ := hf
      refine Submodule.subset_span ⟨φ, hφ, g * infGL E N (Unitary.toUnits k), funext fun x => ?_⟩
      simp only [map_mul, mul_assoc]
    | zero => exact Y.zero_mem
    | add x y _ _ hx hy => exact Y.add_mem hx hy
    | smul r x _ hx => exact Y.smul_mem r hx
  have hYc : ∀ f ∈ Y, Continuous f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨φ, -, g, rfl⟩ := hf
      exact continuous_sliceTC φ g
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul r x _ hx => exact hx.const_smul r
  have hF := PrAdm.finiteDimensional_admissible_isotypic hV.aut (hV.aut ψ hψV) hK (dualRep Y hYl) (isContRep_dualRep Y hYl hYc)
  rw [hadm] at hF
  refine Submodule.finiteDimensional_of_le (S₂ := V ⊓ typePart K (dualRep Y hYl)) ?_
  intro φ hφ
  refine ⟨hφ.1, fun k hk => Subtype.ext (funext fun g => hφ.2.1 k hk g), fun g => ?_⟩
  exact le_coeffSpan_dualRep Y hYl (Submodule.subset_span ⟨φ, hφ, g, rfl⟩)

end GlobalTheory.CompanionTheory.LimV.FdV

end
