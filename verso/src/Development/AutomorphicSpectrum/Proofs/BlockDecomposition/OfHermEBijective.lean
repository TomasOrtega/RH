import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermPoisson

variable {D : D7} {r : ℕ}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem rat_mem_hermA (β : HermE D r) : rat β.1 ∈ hermA D r := by
  show adj (rat β.1) = rat β.1
  rw [← rat_conjTranspose]
  congr 1
  exact β.2

def ofHermE (β : HermE D r) : ratHerm D r :=
  ⟨⟨rat β.1, rat_mem_hermA β⟩, ⟨β.1, rfl⟩⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ofHermE_val (β : HermE D r) : (ofHermE β).1.1 = β.1.map (incA D) := rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem ofHermE_bijective : Function.Bijective (ofHermE (D := D) (r := r)) := by
  refine ⟨fun a b h => Subtype.ext (rat_injective (congrArg (fun c : ratHerm D r => c.1.1) h)), ?_⟩
  rintro ⟨⟨x, hx⟩, hr⟩
  obtain ⟨γ, hγ⟩ := (mem_ratMx).1 (AddSubgroup.mem_comap.1 hr)
  have hγ' : rat γ = x := hγ
  refine ⟨⟨γ, rat_injective ?_⟩, Subtype.ext (Subtype.ext hγ')⟩
  have hx' : adj x = x := hx
  have : rat γᴴ = rat γ := by rw [rat_conjTranspose, hγ', hx']
  exact this

def hermEquiv : HermE D r ≃ ratHerm D r := Equiv.ofBijective _ ofHermE_bijective

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hermEquiv_apply (β : HermE D r) : (hermEquiv (D := D) (r := r)) β = ofHermE β := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem J_eq_Jt (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (μ : Measure (Mx D V.rank r)) (φ : Mx D V.rank r → ℂ)
    (β : HermE D r) : J ψ V μ φ β = Jt ψ V μ φ (ofHermE β).1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem W_eq (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r))
    (φ : Mx D V.rank r → ℂ) (β : HermE D r) :
    W ψ V μ lam φ β = ∫ b, Jt ψ V μ φ b *
      ψ (-halfTr (Matrix.trace (HMul.hMul (ofHermE β).1.1 b.1 : Mx D r r))) ∂lam := rfl

end GlobalTheory.CompanionTheory.HermPoisson
