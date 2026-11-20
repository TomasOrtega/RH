import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ParabolicLowerBlockZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.VacCut

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Avac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open GlobalTheory.Doubling (absE)

def I0 {n : ℕ} (i₀ : Fin n) : Set (Fin n ⊕ Fin n) := {Sum.inl i₀, Sum.inr i₀}

variable (F E) in

structure IsQ {n : ℕ} (i₀ : Fin n) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (lam : (AE F E)ˣ) : Prop where
  off : ∀ a b, a ∉ I0 i₀ → b ∉ I0 i₀ → M a b = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) a b
  col : ∀ a, M a (Sum.inl i₀) = if a = Sum.inl i₀ then (lam : AE F E) else 0
  row : ∀ b, b ≠ Sum.inr i₀ → M (Sum.inr i₀) b = 0

/- English proof (translation)
Establish `h : absE F E u * absE F E u⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel, map_one]`. Establish `: absE F E u ≠ 0` using `fun h0 => by rw [h0, zero_mul] at h; exact zero_ne_one h`. Conclude with `pos_iff_ne_zero.2 this` after adjusting the coercions.
-/
theorem absE_pos (u : (AE F E)ˣ) : 0 < (absE F E u : ℝ) := by
  have h : absE F E u * absE F E u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have : absE F E u ≠ 0 := fun h0 => by rw [h0, zero_mul] at h; exact zero_ne_one h
  exact_mod_cast pos_iff_ne_zero.2 this

/- English proof (translation)
Use function extensionality and compare the values at `X`. Simplify using `only [SD.T, Pi.zero_apply]`. Establish `: d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) 0 = 0` using `funext fun z => mul_zero _`. Rewrite using `[this, map_zero]`.
-/
theorem T_zero (d : SD σ) : d.T 0 = 0 := by
  funext X
  simp only [SD.T, Pi.zero_apply]
  have : d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) 0 = 0 := funext fun z => mul_zero _
  rw [this, map_zero]

end PositivityTheory.SiegelWeilFormula.Avac

end
