import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceTensA

open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace GlobalTheory.CompanionTheory.PairSpProof

/- English proof (translation)
Introduce `E _ _ _ a b F U₁ U₂ h₁ h₂ hfd`. Use `set A : Submodule ℂ (GA E a → ℂ) := Submodule.span ℂ (Set.range fun y x => F (x, y)) with hA`. Establish `: FiniteDimensional ℂ A` using `hfd`. Take `⟨S, c, hc⟩` from `PositivityTheory.Rg.Rs.SliceTensor.interp A`. Set `V : Submodule ℂ (GA E a → ℂ)` to `(U₁.map (Submodule.subtype _))`.

Establish `hAV : A ≤ V`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, rfl⟩`. Take `⟨φ, hφ, e⟩` from `h₁ y`. Conclude with `⟨φ, hφ, e⟩`.

Establish `hF : F = ∑ κ : S, fun x : GA E a × GA E b => (c κ : GA E a → ℂ) x.1 * F (κ.1, x.2)`. Use function extensionality and compare the values at `⟨x, y⟩`. Establish `hy : (fun x => F (x, y)) ∈ A` using `Submodule.subset_span ⟨y, rfl⟩`. Use `congrFun (hc _ hy) x` as an intermediate fact. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢`.

Rewrite using `[this]`. Conclude with `Finset.sum_congr rfl fun κ _ => mul_comm _ _`. Rewrite using `[hF]`. Use `Submodule.sum_mem _ fun κ _ => Submodule.subset_span ?_` and prove the remaining obligations. Take `⟨φ, hφ, e⟩` from `hAV (c κ).2`.

Take `⟨ψ, hψ, e'⟩` from `h₂ κ.1`. Use `⟨φ, hφ, ψ, hψ, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Establish `e1 : φ.1 = (c κ : GA E a → ℂ)` using `e`. Rewrite using `[e1, e']`.
-/
theorem pairSp : PositivityTheory.Rg.BcB.E.E3.PairSp := by
  intro E _ _ _ a b F U₁ U₂ h₁ h₂ hfd
  classical
  set A : Submodule ℂ (GA E a → ℂ) := Submodule.span ℂ (Set.range fun y x => F (x, y)) with hA
  have : FiniteDimensional ℂ A := hfd
  obtain ⟨S, c, hc⟩ := PositivityTheory.Rg.Rs.SliceTensor.interp A

  let V : Submodule ℂ (GA E a → ℂ) := (U₁.map (Submodule.subtype _))
  have hAV : A ≤ V := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, rfl⟩
    obtain ⟨φ, hφ, e⟩ := h₁ y
    exact ⟨φ, hφ, e⟩
  have hF : F = ∑ κ : S, fun x : GA E a × GA E b => (c κ : GA E a → ℂ) x.1 * F (κ.1, x.2) := by
    funext ⟨x, y⟩
    have hy : (fun x => F (x, y)) ∈ A := Submodule.subset_span ⟨y, rfl⟩
    have := congrFun (hc _ hy) x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [this]
    exact Finset.sum_congr rfl fun κ _ => mul_comm _ _
  rw [hF]
  refine Submodule.sum_mem _ fun κ _ => Submodule.subset_span ?_
  obtain ⟨φ, hφ, e⟩ := hAV (c κ).2
  obtain ⟨ψ, hψ, e'⟩ := h₂ κ.1
  refine ⟨φ, hφ, ψ, hψ, ?_⟩
  funext x
  have e1 : φ.1 = (c κ : GA E a → ℂ) := e
  rw [e1, e']

end GlobalTheory.CompanionTheory.PairSpProof
