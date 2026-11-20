import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorBranches
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelExists
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorRegularGeneric
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalDivisorChartGeneric
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalDoublePointsGeneric
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorGoodPointBranches
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

noncomputable section

namespace DivisorBranches

/- English proof (translation)
Rewrite `h₁`, `h₂`, the goal using `[ringKrullDim_quotient]`. Rewrite `h₁`, `h₂`, the goal using `[Order.krullDim_lt_coe_iff]`. Introduce `l`. Establish `hhead : l.head.1 ∈ PrimeSpectrum.zeroLocus (I₁ : Set R) ∪ PrimeSpectrum.zeroLocus (I₂ : Set R)`. Rewrite using `[← PrimeSpectrum.zeroLocus_inf]`.

Conclude with `l.head.2`. Establish `hup : ∀ (I : Ideal R), l.head.1 ∈ PrimeSpectrum.zeroLocus (I : Set R) → ∀ i, (l i).1 ∈ PrimeSpectrum.zeroLocus (I : Set R)` using `fun I hI i => (PrimeSpectrum.mem_zeroLocus _ _).2 (((PrimeSpectrum.mem_zeroLocus _ _).1 hI).trans (show l.head.1.asIdeal ≤ (l i).1.asIdeal from l.head_le i))`. Break down `hhead with h | h` into its components or cases. Conclude with `h₁ { length := l.length, toFun := fun i => ⟨(l i).1, hup I₁ h i⟩, step := fun i => l.step i }`. Conclude with `h₂ { length := l.length, toFun := fun i => ⟨(l i).1, hup I₂ h i⟩, step := fun i => l.step i }`.
-/
theorem quotient_inf_dim_lt {R : Type*} [CommRing R] {I₁ I₂ : Ideal R} {d : ℕ}
    (h₁ : ringKrullDim (R ⧸ I₁) < (d : ℕ)) (h₂ : ringKrullDim (R ⧸ I₂) < (d : ℕ)) :
    ringKrullDim (R ⧸ (I₁ ⊓ I₂)) < (d : ℕ) := by
  rw [ringKrullDim_quotient] at h₁ h₂ ⊢
  rw [Order.krullDim_lt_coe_iff] at h₁ h₂ ⊢
  intro l
  have hhead : l.head.1 ∈ PrimeSpectrum.zeroLocus (I₁ : Set R) ∪ PrimeSpectrum.zeroLocus (I₂ : Set R) := by
    rw [← PrimeSpectrum.zeroLocus_inf]
    exact l.head.2
  have hup : ∀ (I : Ideal R), l.head.1 ∈ PrimeSpectrum.zeroLocus (I : Set R) →
      ∀ i, (l i).1 ∈ PrimeSpectrum.zeroLocus (I : Set R) := fun I hI i =>
    (PrimeSpectrum.mem_zeroLocus _ _).2
      (((PrimeSpectrum.mem_zeroLocus _ _).1 hI).trans (show l.head.1.asIdeal ≤ (l i).1.asIdeal from l.head_le i))
  rcases hhead with h | h
  · exact h₁ { length := l.length, toFun := fun i => ⟨(l i).1, hup I₁ h i⟩, step := fun i => l.step i }
  · exact h₂ { length := l.length, toFun := fun i => ⟨(l i).1, hup I₂ h i⟩, step := fun i => l.step i }

/- English proof (translation)
Introduce `h` and use `hq fun f hf => h f (hle hf)`.
-/
theorem not_mem_zeroSet_of_le {n : ℕ} {I I' : Ideal (MvPolynomial (Fin n) ℂ)} (hle : I ≤ I')
    {q : Fin n → ℂ} (hq : q ∉ zeroSet I) : q ∉ zeroSet I' :=
  fun h => hq fun f hf => h f (hle hf)

/- English proof (translation)
Introduce `n d J u hJ hdim hu`. Take `⟨M⟩` from `hModel n J hJ`. Take `⟨I₁, hle₁, hdim₁, hI₁⟩` from `hReg n d J u hJ hdim hu`. Take `⟨I₂, hle₂, hdim₂, hI₂⟩` from `hChart n d J u M hJ hdim hu`. Take `⟨I₃, hle₃, hdim₃, hI₃⟩` from `hDouble n d J u M hJ hdim hu`.

Use `⟨I₁ ⊓ I₂ ⊓ I₃, le_inf (le_inf hle₁ hle₂) hle₃, quotient_inf_dim_lt (quotient_inf_dim_lt hdim₁ hdim₂) hdim₃, ?_⟩` and prove the remaining obligations. Introduce `q hqJ hqu hqI`. Conclude with `hGood n d J u M q hJ hdim hu hqJ hqu (hI₁ q hqJ hqu (not_mem_zeroSet_of_le (inf_le_left.trans inf_le_left) hqI)) (hI₂ q hqJ hqu (not_mem_zeroSet_of_le (inf_le_left.trans inf_le_right) hqI)) (hI₃ q hqJ hqu (not_mem_zeroSet_of_le inf_le_right hqI))`.
-/
theorem proof (hModel : IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.Statement)
    (hReg : DivisorRegularGeneric.Statement) (hChart : NormalDivisorChartGeneric.Statement)
    (hDouble : NormalDoublePointsGeneric.Statement) (hGood : DivisorGoodPointBranches.Statement) :
    DivisorBranches.Statement := by
  intro n d J u hJ hdim hu
  obtain ⟨M⟩ := hModel n J hJ
  obtain ⟨I₁, hle₁, hdim₁, hI₁⟩ := hReg n d J u hJ hdim hu
  obtain ⟨I₂, hle₂, hdim₂, hI₂⟩ := hChart n d J u M hJ hdim hu
  obtain ⟨I₃, hle₃, hdim₃, hI₃⟩ := hDouble n d J u M hJ hdim hu
  refine ⟨I₁ ⊓ I₂ ⊓ I₃, le_inf (le_inf hle₁ hle₂) hle₃,
    quotient_inf_dim_lt (quotient_inf_dim_lt hdim₁ hdim₂) hdim₃, ?_⟩
  intro q hqJ hqu hqI
  exact hGood n d J u M q hJ hdim hu hqJ hqu
    (hI₁ q hqJ hqu (not_mem_zeroSet_of_le (inf_le_left.trans inf_le_left) hqI))
    (hI₂ q hqJ hqu (not_mem_zeroSet_of_le (inf_le_left.trans inf_le_right) hqI))
    (hI₃ q hqJ hqu (not_mem_zeroSet_of_le inf_le_right hqI))

end DivisorBranches

end

end GroundTheory.Heights₂.Heights
