import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.IsFirstChernThickening
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.SiteCup

/- English proof (translation)
Unfold `CH.Mor.pull CH.oneH`. Use `generalize_proofs p1 p2`. Rewrite using `[CrystallineSemistableComparison.P.mapH_cls]`. Use `congr 1`. Use function extensionality and compare the values at `s`.

Conclude with `h _`. Use `p2 using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `s`. Conclude with `h _`.
-/
theorem pull_unit_class {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {σ : R →+* R'} (A : C ⥤ CommAlgCat.{0} R) (A' : C' ⥤ CommAlgCat.{0} R')
    (m : CH.Mor (CH.modF A) (CH.modF A') σ)
    (h : ∀ T : C', m.τ T (1 : A.obj (m.G.obj T)) = (1 : A'.obj T)) :
    m.pull 0 (CH.oneH A) = CH.oneH A' := by
  unfold CH.Mor.pull CH.oneH
  generalize_proofs p1 p2
  rw [CrystallineSemistableComparison.P.mapH_cls]
  · congr 1
    funext s
    exact h _
  · convert p2 using 2
    funext s
    exact h _

/- English proof (translation)
Introduce `R R' _ _ C C' _ _ Φ Φ' σ m`. Use `⟨?_, pull_unit_class _ _ m.o (fun T => RingHom.map_one (m.ρ T))⟩` and prove the remaining obligations. Introduce `i j k h x y`. Establish `hz : ∀ n (c : (CH.cx (CH.modF Φ.A)).X n), c ∈ (CH.cx (CH.modF Φ.A)).Z n → m.o.hom.f n c ∈ (CH.cx (CH.modF Φ'.A)).Z n`. Introduce `n c hc`.

Use `LinearMap.mem_ker.mpr ?_` and prove the remaining obligations. Rewrite using `[m.o.hom.comm, LinearMap.mem_ker.mp hc, map_zero]`. Establish `ex` using `CrystallineSemistableComparison.Auxff.cls_out _ x`. Generalize the expression as in `Quotient.out x = z at ex`. Substitute `ex` using the available equality.

Establish `ey` using `CrystallineSemistableComparison.Auxff.cls_out _ y`. Generalize the expression as in `Quotient.out y = w at ey`. Substitute `ey` using the available equality. Take `⟨a, ha⟩` from `z`. Take `⟨b, hb⟩` from `w`.

Take `⟨hc, e⟩` from `CrystallineSemistableComparison.P.cup_cls (CH.mulP Φ.A) h a b ha hb`. Take `⟨hc', e'⟩` from `CrystallineSemistableComparison.P.cup_cls (CH.mulP Φ'.A) h _ _ (hz _ _ ha) (hz _ _ hb)`. Rewrite using `[e]`. Unfold `CH.Mor.pull`. Rewrite using `[CrystallineSemistableComparison.P.mapH_cls _ _ _ _ (hz _ _ ha), CrystallineSemistableComparison.P.mapH_cls _ _ _ _ (hz _ _ hb), e', CrystallineSemistableComparison.P.mapH_cls _ _ _ _ (hz _ _ hc)]`.

Use `congr 1`. Use function extensionality and compare the values at `s`. Simplify using `[CH.Mor.hom, CH.Mor.pullC, CH.mulP, CH.Pairing.cupC, SMor.o, CH.term, CH.modF]`. Apply the tactic sequence `congr 1 <;> exact m.nat _ _`.
-/
theorem smor_cup : ∀ {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {Φ : PDF R C}
    {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ), (∀ {i j k : ℕ} (h : i + j = k) x y,
      m.o.pull k ((CH.mulP Φ.A).cup h x y) = (CH.mulP Φ'.A).cup h (m.o.pull i x) (m.o.pull j y)) ∧
    m.o.pull 0 (CH.oneH Φ.A) = CH.oneH Φ'.A := by
  intro R R' _ _ C C' _ _ Φ Φ' σ m
  refine ⟨?_, pull_unit_class _ _ m.o (fun T => RingHom.map_one (m.ρ T))⟩
  intro i j k h x y
  have hz : ∀ n (c : (CH.cx (CH.modF Φ.A)).X n), c ∈ (CH.cx (CH.modF Φ.A)).Z n →
      m.o.hom.f n c ∈ (CH.cx (CH.modF Φ'.A)).Z n := by
    intro n c hc
    refine LinearMap.mem_ker.mpr ?_
    rw [m.o.hom.comm, LinearMap.mem_ker.mp hc, map_zero]
  have ex := CrystallineSemistableComparison.Auxff.cls_out _ x
  generalize Quotient.out x = z at ex
  subst ex
  have ey := CrystallineSemistableComparison.Auxff.cls_out _ y
  generalize Quotient.out y = w at ey
  subst ey
  obtain ⟨a, ha⟩ := z
  obtain ⟨b, hb⟩ := w
  obtain ⟨hc, e⟩ := CrystallineSemistableComparison.P.cup_cls (CH.mulP Φ.A) h a b ha hb
  obtain ⟨hc', e'⟩ := CrystallineSemistableComparison.P.cup_cls (CH.mulP Φ'.A) h _ _ (hz _ _ ha) (hz _ _ hb)
  rw [e]
  unfold CH.Mor.pull
  rw [CrystallineSemistableComparison.P.mapH_cls _ _ _ _ (hz _ _ ha), CrystallineSemistableComparison.P.mapH_cls _ _ _ _ (hz _ _ hb), e',
    CrystallineSemistableComparison.P.mapH_cls _ _ _ _ (hz _ _ hc)]
  congr 1
  funext s
  simp [CH.Mor.hom, CH.Mor.pullC, CH.mulP, CH.Pairing.cupC, SMor.o, CH.term, CH.modF]
  congr 1 <;> exact m.nat _ _

end GlobalTheory.CompanionTheory.SiteCup
