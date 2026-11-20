import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabiliserFixesVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

namespace GlobalTheory.HeisTranslateSB

/- English proof (translation)
Introduce `F _ _ v _ χ κ _ hcond w f hf`. Establish `hO : ∀ y ∈ v.adicCompletionIntegers F, χ y = 1`. Introduce `y hy`. Use `(hcond 1).2 (one_mem _) y hy` as an intermediate fact. Simplify using `using this`.

Establish `hOopen : IsOpen (v.adicCompletionIntegers F : Set (Fv F v))` using `Valued.isOpen_valuationSubring _`. Establish `hχ : IsLocallyConstant (fun s : Fv F v => χ s)`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `s`. Establish `hmem : ∀ᶠ y in nhds s, y - s ∈ v.adicCompletionIntegers F`.

Establish `h0 : (fun y => y - s) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) ∈ nhds s`. Apply `(hOopen.preimage (continuous_id.sub continuous_const)).mem_nhds` to reduce the goal to its premises. Simplify using the standard rewrite rules. Conclude with `h0`. Use `filter_upwards [hmem] with y hy`.

Establish `: y = s + (y - s)` using `by ring`. Rewrite using `[this, AddChar.map_add_eq_mul, hO _ hy, mul_one]`. Establish `hcont : Continuous (fun x : κ → Fv F v => x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2))`. Use `Continuous.add ?_ continuous_const` and prove the remaining obligations. Unfold `dotProduct`.

Conclude with `continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const`. Establish `h1 : IsLocallyConstant (fun x : κ → Fv F v => χ (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)))` using `hχ.comp_continuous hcont`. Establish `h2 : IsLocallyConstant (fun x : κ → Fv F v => f (x + w.1))` using `hf.1.comp_continuous (continuous_id.add continuous_const)`. Establish `h3 : HasCompactSupport (fun x : κ → Fv F v => f (x + w.1))` using `hf.2.comp_homeomorph (Homeomorph.addRight w.1)`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Conclude with `h1.mul h2`. Conclude with `h3.mul_left`.
-/
theorem main : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) [Invertible (2 : Fv F v)] (χ : AddChar (Fv F v) ℂ) (κ : Type) [Fintype κ], (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, χ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) →
    ∀ (w : (κ → Fv F v) × (κ → Fv F v)) (f : (κ → Fv F v) → ℂ), f ∈ SB (κ → Fv F v) → schr χ w f ∈ SB (κ → Fv F v) := by
  intro F _ _ v _ χ κ _ hcond w f hf
  have hO : ∀ y ∈ v.adicCompletionIntegers F, χ y = 1 := by
    intro y hy
    have := (hcond 1).2 (one_mem _) y hy
    simpa using this
  have hOopen : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hχ : IsLocallyConstant (fun s : Fv F v => χ s) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro s
    have hmem : ∀ᶠ y in nhds s, y - s ∈ v.adicCompletionIntegers F := by
      have h0 : (fun y => y - s) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) ∈ nhds s := by
        apply (hOopen.preimage (continuous_id.sub continuous_const)).mem_nhds
        simp
      exact h0
    filter_upwards [hmem] with y hy
    have : y = s + (y - s) := by ring
    rw [this, AddChar.map_add_eq_mul, hO _ hy, mul_one]
  have hcont : Continuous (fun x : κ → Fv F v => x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) := by
    refine Continuous.add ?_ continuous_const
    unfold dotProduct
    exact continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const
  have h1 : IsLocallyConstant (fun x : κ → Fv F v => χ (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2))) :=
    hχ.comp_continuous hcont
  have h2 : IsLocallyConstant (fun x : κ → Fv F v => f (x + w.1)) :=
    hf.1.comp_continuous (continuous_id.add continuous_const)
  have h3 : HasCompactSupport (fun x : κ → Fv F v => f (x + w.1)) :=
    hf.2.comp_homeomorph (Homeomorph.addRight w.1)
  refine ⟨?_, ?_⟩
  · exact h1.mul h2
  · exact h3.mul_left

end GlobalTheory.HeisTranslateSB
