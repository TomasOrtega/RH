import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CoreFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerpEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalTypes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteCapOfCommuteEop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteCompactRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanEvalEqTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommuteCap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommuteOfMemZalg

noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.CuspRep

namespace GlobalTheory.LeviGL.ZGood

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg`. Consider the case `exact _root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg`. Consider the case `(apply _root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg ..)`.
-/
theorem zalg_commute {z z' : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (hz' : z' ∈ Zalg E a) : Commute z z' := by
  first
  | exact @_root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg
  | exact _root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg
  | (apply _root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg ..)

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [chart, mul_assoc]`.
-/
theorem chart_left (φ : GA E a → ℂ) (h g : GA E a) :
    chart (fun x => φ (h * x)) g = chart φ (h * g) := by
  funext x
  simp only [chart, mul_assoc]

def leftRat (γ : GL (Fin a) E) : Module.End ℂ (Sm E a) where
  toFun φ := ⟨fun g => φ.1 (ratGL E a γ * g), fun g => by
    rw [chart_left]
    exact φ.2 _⟩
  map_add' φ ψ := rfl
  map_smul' c φ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem leftRat_apply (γ : GL (Fin a) E) (φ : Sm E a) (g : GA E a) :
    (leftRat γ φ).1 g = φ.1 (ratGL E a γ * g) := rfl

end GlobalTheory.LeviGL.ZGood

end
