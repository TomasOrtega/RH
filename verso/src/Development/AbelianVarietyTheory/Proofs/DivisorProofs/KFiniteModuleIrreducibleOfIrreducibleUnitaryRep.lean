import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroup
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.SubquotientNontrivial
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.KFinIrr

/- English proof (translation)
Establish `hσ' : ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.UJset ε) σ` using `hσ`. Establish `key : ∀ X, ReciprocityTheory.ChartRestriction.DS.inG ε X → ReciprocityTheory.ChartRestriction.DS.dS σ X (v : H) = ∑ c, ∑ d, X c d • ((E c d v : D) : H)` using `fun X hX => (hK.real X hX v).deriv`. Rewrite using `[ReciprocityTheory.ChartRestriction.DS.smE_apply hσ']`. Express the relevant statement in the definitionally equal form `ReciprocityTheory.ChartRestriction.DS.dS σ _ (v : H) + Complex.I • ReciprocityTheory.ChartRestriction.DS.dS σ _ (v : H) = _`. Rewrite using `[key _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart1 ε _), key _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart2 ε _)]`.

Establish `hz : ∀ c d, ReciprocityTheory.ChartRestriction.DS.S7.cpart1 ε (Matrix.single a b 1) c d + Complex.I * ReciprocityTheory.ChartRestriction.DS.S7.cpart2 ε (Matrix.single a b 1) c d = Matrix.single a b (1 : ℂ) c d`. Introduce `c d`. Use `congrFun (congrFun (ReciprocityTheory.ChartRestriction.DS.SmDerA.cpart_decomp ε (Matrix.single a b 1)) c) d` as an intermediate fact. Rewrite using `[this]`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.smul_sum, add_smul, Finset.sum_add_distrib, smul_smul]`. Use `_ = ∑ c, ∑ d, Matrix.single a b (1 : ℂ) c d • ((E c d v : D) : H) := by simp only [hz]`. Use `_ = ((E a b v : D) : H) := by`. Simplify using `[Matrix.single_apply, ite_smul, ite_and]`.
-/
theorem smE_eq {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hK : IsKMod ε σ D E) (v : D) (hv : (v : H) ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ)
    (a b : Fin n) :
    ((ReciprocityTheory.ChartRestriction.DS.smE ε σ a b ⟨v, hv⟩ : ReciprocityTheory.ChartRestriction.DS.smD ε σ) : H) = ((E a b v : D) : H) := by
  have hσ' : ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.UJset ε) σ := hσ
  have key : ∀ X, ReciprocityTheory.ChartRestriction.DS.inG ε X →
      ReciprocityTheory.ChartRestriction.DS.dS σ X (v : H) = ∑ c, ∑ d, X c d • ((E c d v : D) : H) := fun X hX =>
    (hK.real X hX v).deriv
  rw [ReciprocityTheory.ChartRestriction.DS.smE_apply hσ']
  change ReciprocityTheory.ChartRestriction.DS.dS σ _ (v : H) + Complex.I • ReciprocityTheory.ChartRestriction.DS.dS σ _ (v : H) = _
  rw [key _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart1 ε _), key _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart2 ε _)]
  have hz : ∀ c d, ReciprocityTheory.ChartRestriction.DS.S7.cpart1 ε (Matrix.single a b 1) c d +
      Complex.I * ReciprocityTheory.ChartRestriction.DS.S7.cpart2 ε (Matrix.single a b 1) c d = Matrix.single a b (1 : ℂ) c d := by
    intro c d
    have := congrFun (congrFun (ReciprocityTheory.ChartRestriction.DS.SmDerA.cpart_decomp ε (Matrix.single a b 1)) c) d
    rw [this]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  calc _ = ∑ c, ∑ d, (ReciprocityTheory.ChartRestriction.DS.S7.cpart1 ε (Matrix.single a b 1) c d +
        Complex.I * ReciprocityTheory.ChartRestriction.DS.S7.cpart2 ε (Matrix.single a b 1) c d) • ((E c d v : D) : H) := by
          simp only [Finset.smul_sum, add_smul, Finset.sum_add_distrib, smul_smul]
    _ = ∑ c, ∑ d, Matrix.single a b (1 : ℂ) c d • ((E c d v : D) : H) := by simp only [hz]
    _ = ((E a b v : D) : H) := by
          simp [Matrix.single_apply, ite_smul, ite_and]

/- English proof (translation)
Introduce `n ε H _ _ σ D E hc hσ hirr hK N hN`. Use `haveI := hc`. Establish `hle : D ≤ ReciprocityTheory.ChartRestriction.DS.smD ε σ` using `fun v hv => (CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr).1 v ((hK.mem v).1 hv)`. Set `ι : D →ₗ[ℂ] ReciprocityTheory.ChartRestriction.DS.smD ε σ` to `Submodule.inclusion hle`. Establish `hι : Function.Injective ι` using `Submodule.inclusion_injective hle`.

Establish `hcomm : ∀ a b (x : D), ReciprocityTheory.ChartRestriction.DS.smE ε σ a b (ι x) = ι (E a b x)` using `fun a b x => Subtype.ext (smE_eq hσ hK x (hle x.2) a b)`. Set `N' : Submodule ℂ (ReciprocityTheory.ChartRestriction.DS.smD ε σ)` to `N.map ι`. Establish `hN'K : (N' : Set (ReciprocityTheory.ChartRestriction.DS.smD ε σ)) ⊆ CompanionTheory.D.gk.HC.KF ε σ`. Introduce and unpack `_ ⟨x, -, rfl⟩`. Conclude with `(hK.mem x).1 x.2`.

Establish `hN'st : ∀ a b, ∀ v ∈ N', ReciprocityTheory.ChartRestriction.DS.smE ε σ a b v ∈ N'`. Introduce and unpack `a b _ ⟨x, hx, rfl⟩`. Rewrite using `[hcomm]`. Conclude with `⟨_, hN a b x hx, rfl⟩`. Break down `GlobalTheory.HcPort.uIrr n ε H σ hσ hirr N' hN'K hN'st with h | h` into its components or cases.

Use `left`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Establish `hx' : ι x ∈ N'` using `⟨x, hx, rfl⟩`. Rewrite `hx'` using `[h, Submodule.mem_bot]`.

Rewrite using `[Submodule.mem_bot]`. Conclude with `hι (by rw [hx', map_zero])`. Use `right`. Rewrite using `[eq_top_iff]`. Introduce `x _`.

Establish `hx' : ι x ∈ (N' : Set (ReciprocityTheory.ChartRestriction.DS.smD ε σ))`. Rewrite using `[h]`. Conclude with `(hK.mem x).1 x.2`. Take `⟨y, hy, hyx⟩` from `hx'`. Rewrite `hy` using `[hι hyx]`.

Conclude with `hy`.
-/
theorem kMod_irred : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), CompleteSpace H → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsKMod ε σ D E → ∀ N : Submodule ℂ D, (∀ a b, ∀ x ∈ N, E a b x ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro n ε H _ _ σ D E hc hσ hirr hK N hN
  haveI := hc
  have hle : D ≤ ReciprocityTheory.ChartRestriction.DS.smD ε σ := fun v hv =>
    (CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr).1 v ((hK.mem v).1 hv)
  let ι : D →ₗ[ℂ] ReciprocityTheory.ChartRestriction.DS.smD ε σ := Submodule.inclusion hle
  have hι : Function.Injective ι := Submodule.inclusion_injective hle
  have hcomm : ∀ a b (x : D), ReciprocityTheory.ChartRestriction.DS.smE ε σ a b (ι x) = ι (E a b x) := fun a b x =>
    Subtype.ext (smE_eq hσ hK x (hle x.2) a b)
  let N' : Submodule ℂ (ReciprocityTheory.ChartRestriction.DS.smD ε σ) := N.map ι
  have hN'K : (N' : Set (ReciprocityTheory.ChartRestriction.DS.smD ε σ)) ⊆ CompanionTheory.D.gk.HC.KF ε σ := by
    rintro _ ⟨x, -, rfl⟩
    exact (hK.mem x).1 x.2
  have hN'st : ∀ a b, ∀ v ∈ N', ReciprocityTheory.ChartRestriction.DS.smE ε σ a b v ∈ N' := by
    rintro a b _ ⟨x, hx, rfl⟩
    rw [hcomm]
    exact ⟨_, hN a b x hx, rfl⟩
  rcases GlobalTheory.HcPort.uIrr n ε H σ hσ hirr N' hN'K hN'st with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have hx' : ι x ∈ N' := ⟨x, hx, rfl⟩
    rw [h, Submodule.mem_bot] at hx'
    rw [Submodule.mem_bot]
    exact hι (by rw [hx', map_zero])
  · right
    rw [eq_top_iff]
    intro x _
    have hx' : ι x ∈ (N' : Set (ReciprocityTheory.ChartRestriction.DS.smD ε σ)) := by
      rw [h]
      exact (hK.mem x).1 x.2
    obtain ⟨y, hy, hyx⟩ := hx'
    rw [hι hyx] at hy
    exact hy

end GlobalTheory.KFinIrr
