import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.Twist.RatLatO

variable {D : D7}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem incA_eq_tmul (e : D.host.E) : incA D e = ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) := rfl

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨α, hαi, hα, a, ha, s, hs, rfl⟩` from `hy`. Use `AddSubgroup.subset_closure ⟨α, hαi, hα, a, ha, M *ᵥ s, hM s hs, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Simplify using `only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, incA_eq_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_sum]`. Use `congr 1`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun l _ => by ring`. Consider the case `zero => rw [Matrix.mulVec_zero]`.

Conclude with `zero_mem _`. Consider the case `add z z' _ _ hz hz' => rw [Matrix.mulVec_add]`. Conclude with `add_mem hz hz'`. Consider the case `neg z _ hz => rw [Matrix.mulVec_neg]`. Conclude with `neg_mem hz`.
-/
theorem rat_mulVec_mem_latMul {S T : HSp D} (𝔞 : Set D.host.E) {L : Lat S} {L' : Lat T} {P : GlobalTheory.FinPl.Pl D → Prop}
    (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (hM : ∀ t ∈ L, M *ᵥ t ∈ L')
    {z : Fin S.rank → AE D} (hz : z ∈ GlobalTheory.FinPl.latMul S 𝔞 L P) : rat M *ᵥ z ∈ GlobalTheory.FinPl.latMul T 𝔞 L' P := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hαi, hα, a, ha, s, hs, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨α, hαi, hα, a, ha, M *ᵥ s, hM s hs, ?_⟩
    funext i
    simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, incA_eq_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, ← TensorProduct.tmul_sum]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

/- English proof (translation)
Introduce `D S S' T T' LS LS' LT LT' hS hS' hT' j q hj hq x hx`. Rewrite using `[GlobalTheory.FinPl.LatMem.mem_latO_iff D S' T' LS' LT' hS' hT']`. Use `⟨fun i k => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hxM` using `GlobalTheory.FinPl.LatMem.latO_mxAt hx`. Simplify using `only [Matrix.mul_apply]`.

Conclude with `Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ (hxM m l))`. Use `show (rat q * x * rat j) *ᵥ y ∈ _`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Establish `h1 : rat j *ᵥ y ∈ latV S LS (fun _ => True)` using `rat_mulVec_mem_latMul (L := LS') (L' := LS) (P := fun _ => True) {1} j hj hy`. Establish `h2 : x *ᵥ (rat j *ᵥ y) ∈ latA T LT (fun _ => True)` using `GlobalTheory.FinPl.LatMem.latO_maps hS hx h1`.

Conclude with `rat_mulVec_mem_latMul (L := LT) (L' := LT') (P := fun _ => True) {a | a ∈ D.host.AA} q hq h2`.
-/
theorem rat_mul_mem_latO : ∀ {D : D7} {S S' T T' : HSp D} {LS : Lat S} {LS' : Lat S'} {LT : Lat T} {LT' : Lat T'}, IsSelfDualC S LS → IsSelfDualC S' LS' → IsSelfDualC T' LT' → ∀ (j : Matrix (Fin S.rank) (Fin S'.rank) D.host.E) (q : Matrix (Fin T'.rank) (Fin T.rank) D.host.E), (∀ y ∈ LS', j *ᵥ y ∈ LS) → (∀ t ∈ LT, q *ᵥ t ∈ LT') → ∀ x : WO S T, x ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True) → (rat q * x * rat j : WO S' T') ∈ latO S' T' (LS' : Set _) (LT' : Set _) (fun _ => True) := by
  intro D S S' T T' LS LS' LT LT' hS hS' hT' j q hj hq x hx
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S' T' LS' LT' hS' hT']
  refine ⟨fun i k => ?_, fun y hy => ?_⟩
  · have hxM := GlobalTheory.FinPl.LatMem.latO_mxAt hx
    simp only [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _
      (Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ (hxM m l))
  · show (rat q * x * rat j) *ᵥ y ∈ _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 : rat j *ᵥ y ∈ latV S LS (fun _ => True) :=
      rat_mulVec_mem_latMul (L := LS') (L' := LS) (P := fun _ => True) {1} j hj hy
    have h2 : x *ᵥ (rat j *ᵥ y) ∈ latA T LT (fun _ => True) := GlobalTheory.FinPl.LatMem.latO_maps hS hx h1
    exact rat_mulVec_mem_latMul (L := LT) (L' := LT') (P := fun _ => True) {a | a ∈ D.host.AA} q hq h2

end GlobalTheory.Twist.RatLatO
