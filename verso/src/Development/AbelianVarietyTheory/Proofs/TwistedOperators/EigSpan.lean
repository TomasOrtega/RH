import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoSidedHeckePartnerInertPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdjoinSplitHeckeGeneratorsDualsSpherical
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeConjPlaceEqDualLabelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvectorAdjointIntertwinerNormalOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftIntegOfCuspRapidDecay
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EigSpan

/- English proof (translation)
Introduce `D G _ _ Pl0 T A Ks _ _ _ R F hC t h hh P hP a w s hs c hc`. Establish `inj : Function.Injective R.HE.e` using `hC.models.HE.1`. Establish `hkAdd : ∀ c c' : List ℤ →₀ ℂ, GlobalTheory.Hk3.hk (Yc D 0) P (c + c') = GlobalTheory.Hk3.hk (Yc D 0) P c + GlobalTheory.Hk3.hk (Yc D 0) P c'` using `fun c c' => by`. Unfold `GlobalTheory.Hk3.hk`. Conclude with `Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)`.

Establish `hkSmul : ∀ (z : ℂ) (c : List ℤ →₀ ℂ), GlobalTheory.Hk3.hk (Yc D 0) P (z • c) = z • GlobalTheory.Hk3.hk (Yc D 0) P c` using `fun z c => by`. Unfold `GlobalTheory.Hk3.hk`. Rewrite using `[Finsupp.sum_smul_index', Finsupp.smul_sum]`. Simplify using `only [smul_eq_mul, mul_smul]`. Use `intro`.

Conclude with `zero_smul _ _`. Establish `hkZero : GlobalTheory.Hk3.hk (Yc D 0) P 0 = 0`. Unfold `GlobalTheory.Hk3.hk`. Conclude with `Finsupp.sum_zero_index`. Establish `evAdd : ∀ c c' : List ℤ →₀ ℂ, GlobalTheory.Hk3.evC (Yc D 0) P a (c + c') = GlobalTheory.Hk3.evC (Yc D 0) P a c + GlobalTheory.Hk3.evC (Yc D 0) P a c'` using `fun c c' => by`.

Unfold `GlobalTheory.Hk3.evC`. Apply the tactic sequence `exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by split_ifs <;> ring)`. Establish `evSmul : ∀ (z : ℂ) (c : List ℤ →₀ ℂ), GlobalTheory.Hk3.evC (Yc D 0) P a (z • c) = z * GlobalTheory.Hk3.evC (Yc D 0) P a c` using `fun z c => by`. Unfold `GlobalTheory.Hk3.evC`. Rewrite using `[Finsupp.sum_smul_index', Finsupp.mul_sum]`.

Apply the tactic sequence `exact Finsupp.sum_congr fun d _ => by split_ifs <;> simp [mul_assoc]`. Use `intro`. Simplify using the standard rewrite rules. Establish `evZero : GlobalTheory.Hk3.evC (Yc D 0) P a 0 = 0`. Unfold `GlobalTheory.Hk3.evC`.

Conclude with `Finsupp.sum_zero_index`. Establish `pAdd : ∀ L L' x, postOn (R.MY 0) (L + L') x = postOn (R.MY 0) L x + postOn (R.MY 0) L' x`. Introduce `L L' x`. Use extensionality with `v`. Simplify using `[postOn]`.

Establish `pSmul : ∀ (z : ℂ) L x, postOn (R.MY 0) (z • L) x = z • postOn (R.MY 0) L x`. Introduce `z L x`. Use extensionality with `v`. Simplify using `[postOn]`. Establish `pZero : ∀ x, postOn (R.MY 0) 0 x = 0`.

Introduce `x`. Use extensionality with `v`. Simplify using `[postOn]`. Establish `hAdd : ∀ c c', h P (c + c') w = h P c w + h P c' w` using `fun c c' => inj (by rw [hh P hP, map_add, hh P hP, hh P hP, hkAdd, pAdd])`. Establish `hSmul : ∀ (z : ℂ) c, h P (z • c) w = z • h P c w` using `fun z c => inj (by rw [hh P hP, map_smul, hh P hP, hkSmul, pSmul])`.

Establish `hZero : h P 0 w = 0` using `inj (by rw [hh P hP, hkZero, pZero, map_zero])`. Proceed by induction on `hc using Submodule.span_induction with`. Consider the case `mem x hx => exact hs x hx`. Consider the case `zero => rw [hZero, evZero, zero_smul]`. Consider the case `add x y _ _ hx hy => rw [hAdd, hx, hy, evAdd, add_smul]`.

Consider the case `smul z x _ hx => rw [hSmul, hx, evSmul, mul_smul]`.
-/
theorem eig_span : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H), (∀ P, GlobalTheory.Hk3.Good R t P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (GlobalTheory.Hk3.hk (Yc D 0) P c) (R.HE.e x)) → ∀ P, GlobalTheory.Hk3.Good R t P → ∀ (a : List ℤ → ℂ) (w : R.HE.H) (s : Set (List ℤ →₀ ℂ)), (∀ c ∈ s, h P c w = GlobalTheory.Hk3.evC (Yc D 0) P a c • w) → ∀ c ∈ Submodule.span ℂ s, h P c w = GlobalTheory.Hk3.evC (Yc D 0) P a c • w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t h hh P hP a w s hs c hc
  have inj : Function.Injective R.HE.e := hC.models.HE.1
  have hkAdd : ∀ c c' : List ℤ →₀ ℂ, GlobalTheory.Hk3.hk (Yc D 0) P (c + c') = GlobalTheory.Hk3.hk (Yc D 0) P c + GlobalTheory.Hk3.hk (Yc D 0) P c' :=
    fun c c' => by
      unfold GlobalTheory.Hk3.hk
      exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)
  have hkSmul : ∀ (z : ℂ) (c : List ℤ →₀ ℂ), GlobalTheory.Hk3.hk (Yc D 0) P (z • c) = z • GlobalTheory.Hk3.hk (Yc D 0) P c :=
    fun z c => by
      unfold GlobalTheory.Hk3.hk
      rw [Finsupp.sum_smul_index', Finsupp.smul_sum]
      · simp only [smul_eq_mul, mul_smul]
      · intro; exact zero_smul _ _
  have hkZero : GlobalTheory.Hk3.hk (Yc D 0) P 0 = 0 := by
    unfold GlobalTheory.Hk3.hk; exact Finsupp.sum_zero_index
  have evAdd : ∀ c c' : List ℤ →₀ ℂ, GlobalTheory.Hk3.evC (Yc D 0) P a (c + c') = GlobalTheory.Hk3.evC (Yc D 0) P a c + GlobalTheory.Hk3.evC (Yc D 0) P a c' :=
    fun c c' => by
      unfold GlobalTheory.Hk3.evC
      exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by split_ifs <;> ring)
  have evSmul : ∀ (z : ℂ) (c : List ℤ →₀ ℂ), GlobalTheory.Hk3.evC (Yc D 0) P a (z • c) = z * GlobalTheory.Hk3.evC (Yc D 0) P a c :=
    fun z c => by
      unfold GlobalTheory.Hk3.evC
      rw [Finsupp.sum_smul_index', Finsupp.mul_sum]
      · exact Finsupp.sum_congr fun d _ => by split_ifs <;> simp [mul_assoc]
      · intro; simp
  have evZero : GlobalTheory.Hk3.evC (Yc D 0) P a 0 = 0 := by
    unfold GlobalTheory.Hk3.evC; exact Finsupp.sum_zero_index
  have pAdd : ∀ L L' x, postOn (R.MY 0) (L + L') x = postOn (R.MY 0) L x + postOn (R.MY 0) L' x := by
    intro L L' x; ext v; simp [postOn]
  have pSmul : ∀ (z : ℂ) L x, postOn (R.MY 0) (z • L) x = z • postOn (R.MY 0) L x := by
    intro z L x; ext v; simp [postOn]
  have pZero : ∀ x, postOn (R.MY 0) 0 x = 0 := by
    intro x; ext v; simp [postOn]
  have hAdd : ∀ c c', h P (c + c') w = h P c w + h P c' w := fun c c' =>
    inj (by rw [hh P hP, map_add, hh P hP, hh P hP, hkAdd, pAdd])
  have hSmul : ∀ (z : ℂ) c, h P (z • c) w = z • h P c w := fun z c =>
    inj (by rw [hh P hP, map_smul, hh P hP, hkSmul, pSmul])
  have hZero : h P 0 w = 0 := inj (by rw [hh P hP, hkZero, pZero, map_zero])
  induction hc using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => rw [hZero, evZero, zero_smul]
  | add x y _ _ hx hy => rw [hAdd, hx, hy, evAdd, add_smul]
  | smul z x _ hx => rw [hSmul, hx, evSmul, mul_smul]

end GlobalTheory.EigSpan
