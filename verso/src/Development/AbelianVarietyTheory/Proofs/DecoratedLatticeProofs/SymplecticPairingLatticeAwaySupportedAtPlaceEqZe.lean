import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.OffSympl

/- English proof (translation)
Take `⟨β, rfl, h1, h0⟩` from `hε`. Introduce `u hu`. Proceed by induction on `hu using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩` from `hw`.

Establish `hβα : β * α = 0` using `FiniteAdeleRing.ext _ fun w => by`. Express the relevant statement in the definitionally equal form `evalV D.host.F w (β * α) = evalV D.host.F w 0`. Rewrite using `[map_mul, map_zero]`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality.

Rewrite using `[hP w hv, mul_zero]`. Rewrite using `[h0 w hw, zero_mul]`. Use extensionality with `i j`. Rewrite using `[Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]`. Express the relevant statement in the definitionally equal form `(pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = 0`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Establish `: pairA D.host.F 0 β * pairA D.host.F 0 α = 0` using `Prod.ext (mul_zero _) hβα`. Rewrite using `[this, TensorProduct.zero_tmul]`. Consider the case `zero => exact smul_zero _`. Consider the case `add x x' _ _ h h' => rw [smul_add, h, h', add_zero]`.

Consider the case `neg x _ h => rw [smul_neg, h, neg_zero]`.
-/
theorem placeIdem_smul_latO {D : D7} {S T : HSp D} {MS : Set (Fin S.rank → D.host.E)}
    {MT : Set (Fin T.rank → D.host.E)} {P : Pl D → Prop} {v : Pl D} (hv : ¬ P v) {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) : ∀ u ∈ latO S T MS MT P, algebraMap (AF D.host.F) (AE D) ε • u = 0 := by
  obtain ⟨β, rfl, h1, h0⟩ := hε
  intro u hu
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    have hβα : β * α = 0 := FiniteAdeleRing.ext _ fun w => by
      change evalV D.host.F w (β * α) = evalV D.host.F w 0
      rw [map_mul, map_zero]
      by_cases hw : w = v
      · subst hw; rw [hP w hv, mul_zero]
      · rw [h0 w hw, zero_mul]
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = 0
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have : pairA D.host.F 0 β * pairA D.host.F 0 α = 0 := Prod.ext (mul_zero _) hβα
    rw [this, TensorProduct.zero_tmul]
  | zero => exact smul_zero _
  | add x x' _ _ h h' => rw [smul_add, h, h', add_zero]
  | neg x _ h => rw [smul_neg, h, neg_zero]

/- English proof (translation)
Introduce `hv u hu x hx`. Take `⟨ε, hε, he⟩` from `p.above`. Establish `hx' : (p.e + cA D p.e) • x = x` using `Matrix.ext fun i j => by rw [Matrix.smul_apply, smul_eq_mul, hx]`. Establish `hc : cA D (p.e + cA D p.e) = p.e + cA D p.e` using `by rw [map_add, cA_cA, add_comm]`. Rewrite using `[← hx', ← hc, ← GlobalTheory.PlaceModel.symplO_smul, he, placeIdem_smul_latO hv hε u hu, GlobalTheory.PlaceModel.symplO_zero_left]`.
-/
theorem symplO_off_eq_zero (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S T : HSp D) (MS : Set (Fin S.rank → D.host.E))
    (MT : Set (Fin T.rank → D.host.E)) (P : Pl D → Prop) : ¬ P p.v → ∀ u ∈ latO S T MS MT P, ∀ x : WO S T,
    (∀ i j, (p.e + cA D p.e) * x i j = x i j) → symplO S T u x = 0 := by
  intro hv u hu x hx
  obtain ⟨ε, hε, he⟩ := p.above
  have hx' : (p.e + cA D p.e) • x = x := Matrix.ext fun i j => by rw [Matrix.smul_apply, smul_eq_mul, hx]
  have hc : cA D (p.e + cA D p.e) = p.e + cA D p.e := by rw [map_add, cA_cA, add_comm]
  rw [← hx', ← hc, ← GlobalTheory.PlaceModel.symplO_smul, he, placeIdem_smul_latO hv hε u hu,
    GlobalTheory.PlaceModel.symplO_zero_left]

end GlobalTheory.FinPl.OffSympl
