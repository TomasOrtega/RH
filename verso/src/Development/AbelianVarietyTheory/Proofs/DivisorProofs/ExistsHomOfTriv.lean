import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsAmpleClass
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BirigidHom

/- English proof (translation)
Introduce `k _ A B _ _ _ hA hB P₀ hd P hP h₁ h₂`. Take `⟨g, hg⟩` from `GlobalTheory.AbelianDim.exists_relDim k A hA`. Set `AV : GlobalTheory.AV.AbVar k` to `{ X := A, ab := hA, dim := g, smooth := hg }`. Take `⟨c, L, hL, hamp, -⟩` from `GlobalTheory.AV.exists_isAmpleCls k AV`. Take `⟨H, hH, aH⟩` from `GlobalTheory.BirigidLift.exists_relAmple_prod (A := A) (B := A) hA hA hL hamp hL hamp`.

Take `⟨a₁, -⟩` from `GlobalTheory.BirigidLift.additive_of_triv hA hA hH aH hP h₁ h₂`. Take `⟨x, hx, -⟩` from `hd.univ A P hP a₁`. Establish `hE : (ev P₀ (fst A A) (snd A A ≫ x)).IsLB` using `pull_isLB hd.isLB _`. Establish `e : cls P hP = evc hd.isLB (fst A A) (snd A A ≫ x)` using `(cls_eq_iff hP hE).2 hx`. Use `⟨x, GlobalTheory.rigidity_holds (Sp k) A B hA hB x ?_, hx⟩` and prove the remaining obligations.

Apply `hd.eq_one` to reduce the goal to its premises. Rewrite using `[triv_ev_iff hd.isLB, ← Category.assoc, ← GlobalTheory.BirigidLift.evc_of_cls hd.isLB hP e]`. Establish `u1 : snd A (𝟙_ (Over (Sp k))) ≫ (η : 𝟙_ (Over (Sp k)) ⟶ A) = 1` using `by show _ = toUnit _ ≫ η`. Rewrite using `[toUnit_unique (snd A (𝟙_ (Over (Sp k)))) (toUnit _)]`. Rewrite using `[u1]`.

Conclude with `evc_one_right hP h₂ _`.
-/
theorem exists_hom_of_triv : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [IsCommMonObj A] [GrpObj B],
    IsAbelianScheme A → IsAbelianScheme B → ∀ (P₀ : LB (A ⊗ B).left), GlobalTheory.AbDual.IsDual A B P₀ →
    ∀ (P : LB (A ⊗ A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    ∃ l : A ⟶ B, IsMonHom l ∧ LBIso P (GlobalTheory.AbDual.ev P₀ (fst A A) (snd A A ≫ l)) := by
  intro k _ A B _ _ _ hA hB P₀ hd P hP h₁ h₂
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim k A hA
  let AV : GlobalTheory.AV.AbVar k := { X := A, ab := hA, dim := g, smooth := hg }
  obtain ⟨c, L, hL, hamp, -⟩ := GlobalTheory.AV.exists_isAmpleCls k AV
  obtain ⟨H, hH, aH⟩ := GlobalTheory.BirigidLift.exists_relAmple_prod (A := A) (B := A) hA hA hL hamp hL hamp
  obtain ⟨a₁, -⟩ := GlobalTheory.BirigidLift.additive_of_triv hA hA hH aH hP h₁ h₂
  obtain ⟨x, hx, -⟩ := hd.univ A P hP a₁
  have hE : (ev P₀ (fst A A) (snd A A ≫ x)).IsLB := pull_isLB hd.isLB _
  have e : cls P hP = evc hd.isLB (fst A A) (snd A A ≫ x) := (cls_eq_iff hP hE).2 hx
  refine ⟨x, GlobalTheory.rigidity_holds (Sp k) A B hA hB x ?_, hx⟩
  apply hd.eq_one
  rw [triv_ev_iff hd.isLB, ← Category.assoc, ← GlobalTheory.BirigidLift.evc_of_cls hd.isLB hP e]
  have u1 : snd A (𝟙_ (Over (Sp k))) ≫ (η : 𝟙_ (Over (Sp k)) ⟶ A) = 1 := by
    show _ = toUnit _ ≫ η
    rw [toUnit_unique (snd A (𝟙_ (Over (Sp k)))) (toUnit _)]
  rw [u1]
  exact evc_one_right hP h₂ _

end GlobalTheory.BirigidHom
