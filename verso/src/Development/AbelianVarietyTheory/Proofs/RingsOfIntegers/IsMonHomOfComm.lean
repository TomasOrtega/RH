import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem

namespace GlobalTheory.PowMap

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

variable {S : Scheme.{0}}

noncomputable def powHom {G B : Over S} (q : G ⟶ B) : ∀ n : ℕ, powObj G n ⟶ powObj B n
  | 0 => 𝟙 (𝟙_ (Over S))
  | n + 1 => (q ⊗ₘ powHom q n : G ⊗ powObj G n ⟶ B ⊗ powObj B n)

/- English proof (translation)
The claim follows from `| 0, i => i.elim0 | n + 1, i => by refine Fin.cases ?_ (fun i => ?_) i · exact tensorHom_fst q (powHom q n) · show (q ⊗ₘ powHom q n) ≫ snd _ _ ≫ powPr B i = (snd _ _ ≫ powPr G i) ≫ q rw [tensorHom_snd_assoc, powHom_pr q n i, Category.assoc]`.
-/
theorem powHom_pr {G B : Over S} (q : G ⟶ B) :
    ∀ (n : ℕ) (i : Fin n), powHom q n ≫ powPr B i = powPr G i ≫ q
  | 0, i => i.elim0
  | n + 1, i => by
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tensorHom_fst q (powHom q n)
    · show (q ⊗ₘ powHom q n) ≫ snd _ _ ≫ powPr B i = (snd _ _ ≫ powPr G i) ≫ q
      rw [tensorHom_snd_assoc, powHom_pr q n i, Category.assoc]

/- English proof (translation)
The claim follows from `| 0 => P.id_mem S | n + 1 => by have ih := prop_powHom P q hq n show P (q ⊗ₘ powHom q n).left rw [Over.tensorHom_left] exact MorphismProperty.pullbackMap (P := P) hq ih (Over.w q).symm (Over.w (powHom q n)).symm`.
-/
theorem prop_powHom (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {G B : Over S} (q : G ⟶ B) (hq : P q.left) : ∀ n : ℕ, P (powHom q n).left
  | 0 => P.id_mem S
  | n + 1 => by
    have ih := prop_powHom P q hq n
    show P (q ⊗ₘ powHom q n).left
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := P) hq ih (Over.w q).symm (Over.w (powHom q n)).symm

/- English proof (translation)
Set `e : G' ≅ powObj G j` to `p.lim.conePointUniqueUpToIso (powIsLimit G j)`. Set `f : B' ≅ powObj B j` to `pB.lim.conePointUniqueUpToIso (powIsLimit B j)`. Establish `he : ∀ i, e.hom ≫ powPr G i = p.pr i` using `fun i => p.lim.conePointUniqueUpToIso_hom_comp (powIsLimit G j) ⟨i⟩`. Establish `hf : ∀ i, f.inv ≫ pB.pr i = powPr B i` using `fun i => pB.lim.conePointUniqueUpToIso_inv_comp (powIsLimit B j) ⟨i⟩`. Establish `hq' : q' = e.hom ≫ powHom q j ≫ f.inv`.

Use `pB.lim.hom_ext fun ⟨i⟩ => ?_` and prove the remaining obligations. Use `show q' ≫ pB.pr i = (e.hom ≫ powHom q j ≫ f.inv) ≫ pB.pr i`. Rewrite using `[h, Category.assoc, Category.assoc, hf, powHom_pr, ← Category.assoc, he]`. Establish `i1 : IsIso e.hom.left` using `inferInstanceAs (IsIso ((Over.forget _).map e.hom))`. Establish `i2 : IsIso f.inv.left` using `inferInstanceAs (IsIso ((Over.forget _).map f.inv))`.

Rewrite using `[hq', Over.comp_left, Over.comp_left, P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]`. Conclude with `prop_powHom P q hq j`.
-/
theorem prop_of_comm (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {G' G B' B : Over S} [GrpObj G'] [GrpObj G] [GrpObj B'] [GrpObj B] {j : ℕ} (p : IsPowGrp G' G j)
    (pB : IsPowGrp B' B j) (q : G ⟶ B) (q' : G' ⟶ B') (h : ∀ i, q' ≫ pB.pr i = p.pr i ≫ q)
    (hq : P q.left) : P q'.left := by
  let e : G' ≅ powObj G j := p.lim.conePointUniqueUpToIso (powIsLimit G j)
  let f : B' ≅ powObj B j := pB.lim.conePointUniqueUpToIso (powIsLimit B j)
  have he : ∀ i, e.hom ≫ powPr G i = p.pr i := fun i =>
    p.lim.conePointUniqueUpToIso_hom_comp (powIsLimit G j) ⟨i⟩
  have hf : ∀ i, f.inv ≫ pB.pr i = powPr B i := fun i =>
    pB.lim.conePointUniqueUpToIso_inv_comp (powIsLimit B j) ⟨i⟩
  have hq' : q' = e.hom ≫ powHom q j ≫ f.inv := by
    refine pB.lim.hom_ext fun ⟨i⟩ => ?_
    show q' ≫ pB.pr i = (e.hom ≫ powHom q j ≫ f.inv) ≫ pB.pr i
    rw [h, Category.assoc, Category.assoc, hf, powHom_pr, ← Category.assoc, he]
  have i1 : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have i2 : IsIso f.inv.left := inferInstanceAs (IsIso ((Over.forget _).map f.inv))
  rw [hq', Over.comp_left, Over.comp_left, P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
  exact prop_powHom P q hq j

/- English proof (translation)
Use `⟨pB.lim.hom_ext fun ⟨i⟩ => ?_, pB.lim.hom_ext fun ⟨i⟩ => ?_⟩` and prove the remaining obligations. Use `p.hom i` as an intermediate fact. Use `pB.hom i` as an intermediate fact. Use `show (η ≫ q') ≫ pB.pr i = η ≫ pB.pr i`. Rewrite using `[Category.assoc, h, IsMonHom.one_hom, IsMonHom.one_hom]`.

Use `p.hom i` as an intermediate fact. Use `pB.hom i` as an intermediate fact. Use `show (μ ≫ q') ≫ pB.pr i = ((q' ⊗ₘ q') ≫ μ) ≫ pB.pr i`. Rewrite using `[Category.assoc, Category.assoc, h, IsMonHom.mul_hom, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, h]`.
-/
theorem isMonHom_of_comm {G' G B' B : Over S} [GrpObj G'] [GrpObj G] [GrpObj B'] [GrpObj B] {j : ℕ}
    (p : IsPowGrp G' G j) (pB : IsPowGrp B' B j) (q : G ⟶ B) (q' : G' ⟶ B')
    (h : ∀ i, q' ≫ pB.pr i = p.pr i ≫ q) (hq : IsMonHom q) : IsMonHom q' := by
  refine ⟨pB.lim.hom_ext fun ⟨i⟩ => ?_, pB.lim.hom_ext fun ⟨i⟩ => ?_⟩
  · have := p.hom i
    have := pB.hom i
    show (η ≫ q') ≫ pB.pr i = η ≫ pB.pr i
    rw [Category.assoc, h, IsMonHom.one_hom, IsMonHom.one_hom]
  · have := p.hom i
    have := pB.hom i
    show (μ ≫ q') ≫ pB.pr i = ((q' ⊗ₘ q') ≫ μ) ≫ pB.pr i
    rw [Category.assoc, Category.assoc, h, IsMonHom.mul_hom, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, h]

/- English proof (translation)
Introduce `S G' G B' B _ _ _ _ j p pB q`. Establish `h : ∀ i, pB.lim.lift (Fan.mk G' fun i => p.pr i ≫ q) ≫ pB.pr i = p.pr i ≫ q` using `fun i => pB.lim.fac (Fan.mk G' fun i => p.pr i ≫ q) ⟨i⟩`. Conclude with `⟨_, h, isMonHom_of_comm p pB q _ h, prop_of_comm @Flat p pB q _ h, prop_of_comm @Surjective p pB q _ h, prop_of_comm @QuasiCompact p pB q _ h, prop_of_comm @IsAffineHom p pB q _ h⟩`.
-/
theorem main : ∀ (S : Scheme.{0}) (G' G B' B : Over S) [GrpObj G'] [GrpObj G] [GrpObj B'] [GrpObj B] (j : ℕ) (p : IsPowGrp G' G j) (pB : IsPowGrp B' B j) (q : G ⟶ B), ∃ q' : G' ⟶ B', (∀ i, q' ≫ pB.pr i = p.pr i ≫ q) ∧ (IsMonHom q → IsMonHom q') ∧ (Flat q.left → Flat q'.left) ∧ (Surjective q.left → Surjective q'.left) ∧ (QuasiCompact q.left → QuasiCompact q'.left) ∧ (IsAffineHom q.left → IsAffineHom q'.left) := by
  intro S G' G B' B _ _ _ _ j p pB q
  have h : ∀ i, pB.lim.lift (Fan.mk G' fun i => p.pr i ≫ q) ≫ pB.pr i = p.pr i ≫ q := fun i =>
    pB.lim.fac (Fan.mk G' fun i => p.pr i ≫ q) ⟨i⟩
  exact ⟨_, h, isMonHom_of_comm p pB q _ h, prop_of_comm @Flat p pB q _ h,
    prop_of_comm @Surjective p pB q _ h, prop_of_comm @QuasiCompact p pB q _ h,
    prop_of_comm @IsAffineHom p pB q _ h⟩

end GlobalTheory.PowMap
