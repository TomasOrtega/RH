import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Simplify using `only [pow_zero, Hom.one_def]`. Rewrite using `[← Category.assoc, toUnit_unique (f ≫ toUnit Y) (toUnit X)]`. Consider the case `succ n ih`.

Rewrite using `[pow_succ, pow_succ, ← ih, Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]`.
-/
private theorem comp_pow' {C : Type*} [Category C] [CartesianMonoidalCategory C] {X Y Z : C} [MonObj Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) : f ≫ (g ^ n) = (f ≫ g) ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero, Hom.one_def]
    rw [← Category.assoc, toUnit_unique (f ≫ toUnit Y) (toUnit X)]
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih, Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

/- English proof (translation)
Conclude with `map_pow (IsMonHom.monoidHom g X) f n`.
-/
private theorem pow_comp' {C : Type*} [Category C] [CartesianMonoidalCategory C] {X Y Z : C} [MonObj Y] [MonObj Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsMonHom g] (n : ℕ) : (f ^ n) ≫ g = (f ≫ g) ^ n := by
  exact map_pow (IsMonHom.monoidHom g X) f n

/- English proof (translation)
Introduce `hP p _ D R _ b N S s c c' o o₁ o₂ ψ χ h1 h2`. Take `⟨⟨k, rfl⟩, hψ, ha, he, hL, ψ', hψ', hψ1, hψ2⟩` from `h1`. Take `⟨⟨k', rfl⟩, hχ, ha', he', hL', χ', hχ', hχ1, hχ2⟩` from `h2`. Use `haveI := hψ`. Use `haveI := hχ`.

Use `haveI := hψ'`. Use `haveI := hχ'`. Use `⟨⟨k + k', (pow_add p k k').symm⟩, inferInstance, ?_, ?_, ?_, ⟨χ' ≫ ψ', inferInstance, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `a`. Rewrite using `[← Category.assoc, ha, Category.assoc, ha', Category.assoc]`.

Introduce `x`. Rewrite using `[he', he, Category.assoc]`. Rewrite using `[(hP p D R b N S s o).2.2.2.2 o₂ (ψ ≫ χ) (p ^ k * p ^ k')]`. Introduce `T x y`. Establish `e1` using `((hP p D R b N S s o).2.2.2.2 o₁ ψ (p ^ k)).1 hL`.

Establish `e2` using `((hP p D R b N S s o₁).2.2.2.2 o₂ χ (p ^ k')).1 hL'`. Rewrite using `[← Category.assoc, ← Category.assoc, e2, e1, mul_comm, mul_smul]`. Rewrite using `[Category.assoc, ← Category.assoc χ, hχ1, pow_comp', Category.id_comp, comp_pow', hψ1, ← pow_mul]`. Rewrite using `[Category.assoc, ← Category.assoc ψ', hψ2, pow_comp', Category.id_comp, comp_pow', hχ2, ← pow_mul, mul_comm]`.
-/
theorem UpperTheory.Gal.crystallineComparison.Mod.isogComp_of :
    PairCalc → IsogComp := by
  intro hP p _ D R _ b N S s c c' o o₁ o₂ ψ χ h1 h2
  obtain ⟨⟨k, rfl⟩, hψ, ha, he, hL, ψ', hψ', hψ1, hψ2⟩ := h1
  obtain ⟨⟨k', rfl⟩, hχ, ha', he', hL', χ', hχ', hχ1, hχ2⟩ := h2
  haveI := hψ
  haveI := hχ
  haveI := hψ'
  haveI := hχ'
  refine ⟨⟨k + k', (pow_add p k k').symm⟩, inferInstance, ?_, ?_, ?_, ⟨χ' ≫ ψ', inferInstance, ?_, ?_⟩⟩
  · intro a
    rw [← Category.assoc, ha, Category.assoc, ha', Category.assoc]
  · intro x
    rw [he', he, Category.assoc]
  · rw [(hP p D R b N S s o).2.2.2.2 o₂ (ψ ≫ χ) (p ^ k * p ^ k')]
    intro T x y
    have e1 := ((hP p D R b N S s o).2.2.2.2 o₁ ψ (p ^ k)).1 hL
    have e2 := ((hP p D R b N S s o₁).2.2.2.2 o₂ χ (p ^ k')).1 hL'
    rw [← Category.assoc, ← Category.assoc, e2, e1, mul_comm, mul_smul]
  · rw [Category.assoc, ← Category.assoc χ, hχ1, pow_comp', Category.id_comp, comp_pow', hψ1,
      ← pow_mul]
  · rw [Category.assoc, ← Category.assoc ψ', hψ2, pow_comp', Category.id_comp, comp_pow', hχ2,
      ← pow_mul, mul_comm]
