import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LatticeTorsion

variable {S : Scheme.{0}}

/- English proof (translation)
The claim follows from `| 0 => P.id_mem S | k + 1 => by change P (pullback.fst X.hom (Out.powObj X k).hom ≫ X.hom) exact P.comp_mem _ _ (P.pullback_fst _ _ (prop_powObj P X hX k)) hX`.
-/
theorem prop_powObj (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] (X : Over S) (hX : P X.hom) : ∀ k, P (Out.powObj X k).hom
  | 0 => P.id_mem S
  | k + 1 => by
    change P (pullback.fst X.hom (Out.powObj X k).hom ≫ X.hom)
    exact P.comp_mem _ _ (P.pullback_fst _ _ (prop_powObj P X hX k)) hX

/- English proof (translation)
Use `⟨pullback.lift x (toUnit T) ((GrpTangent.comp_mulN x n).trans hx), pullback.lift_fst _ _ _, fun y hy => ?_⟩` and prove the remaining obligations. Conclude with `pullback.hom_ext (hy.trans (pullback.lift_fst _ _ _).symm) (toUnit_unique _ _)`.
-/
theorem existsUnique_torsion (G : Over S) [GrpObj G] (n : ℕ) {T : Over S} (x : T ⟶ G)
    (hx : x ^ n = 1) : ∃! y : T ⟶ torsion G n, y ≫ torsion.ι G n = x := by
  refine ⟨pullback.lift x (toUnit T) ((GrpTangent.comp_mulN x n).trans hx),
    pullback.lift_fst _ _ _, fun y hy => ?_⟩
  exact pullback.hom_ext (hy.trans (pullback.lift_fst _ _ _).symm) (toUnit_unique _ _)

/- English proof (translation)
Rewrite using `[← GrpTangent.comp_mulN]`. Use `pullback.condition.trans ?_` and prove the remaining obligations. Rewrite using `[toUnit_unique (pullback.snd _ _) (toUnit _)]`. Both sides reduce to the same expression.
-/
theorem torsionι_pow_eq_one (G : Over S) [GrpObj G] (n : ℕ) : torsion.ι G n ^ n = 1 := by
  rw [← GrpTangent.comp_mulN]
  refine pullback.condition.trans ?_
  rw [toUnit_unique (pullback.snd _ _) (toUnit _)]
  rfl

/- English proof (translation)
Set `φ : Multiplicative La →* A` to `MonoidHom.mk' (fun x => f x.toAdd) fun x y => hf _ _`. Establish `h : ∀ x, f x = φ (Multiplicative.ofAdd x)` using `fun _ => rfl`. Use `conv_lhs => rw [← b.sum_repr a]`. Simplify using `only [h, ofAdd_sum, ofAdd_zsmul, map_prod, map_zpow]`.
-/
theorem eq_prod_zpow {La I A : Type} [AddCommGroup La] [Fintype I] [CommGroup A]
    (b : Module.Basis I ℤ La) (f : La → A) (hf : ∀ a c, f (a + c) = f a * f c) (a : La) :
    f a = ∏ i, f (b i) ^ (b.repr a i) := by
  let φ : Multiplicative La →* A := MonoidHom.mk' (fun x => f x.toAdd) fun x y => hf _ _
  have h : ∀ x, f x = φ (Multiplicative.ofAdd x) := fun _ => rfl
  conv_lhs => rw [← b.sum_repr a]
  simp only [h, ofAdd_sum, ofAdd_zsmul, map_prod, map_zpow]

end GlobalTheory.LatticeTorsion

namespace GlobalTheory

open LatticeTorsion in

/- English proof (translation)
Introduce `S G _ _ n La _ _ _ hG hn`. Take `⟨-, hfin, het⟩` from `GrpTangent.finiteEtale_mulN_torsion G hn`. Set `b` to `Module.finBasis ℤ La`. Set `r` to `Module.finrank ℤ La`. Set `Z` to `Out.powObj (torsion G n) r`.

Set `x : Fin r → (Z ⟶ G)` to `fun i => Out.powPr (torsion G n) i ≫ torsion.ι G n`. Establish `hx : ∀ i, x i ^ n = 1` using `fun i => by`. Rewrite using `[← MonObj.comp_pow, torsionι_pow_eq_one, MonObj.comp_one]`. Set `et : La → (Z ⟶ G)` to `fun a => ∏ i, x i ^ (b.repr a i)`. Establish `hadd : ∀ a c, et (a + c) = et a * et c` using `fun a c => by`.

Simplify using `only [et, map_add, Finsupp.add_apply, zpow_add, Finset.prod_mul_distrib]`. Establish `hb : ∀ i, et (b i) = x i` using `fun i => by`. Simplify using `only [et, Module.Basis.repr_self]`. Rewrite using `[Finset.prod_eq_single i (fun j _ hj => by simp [Finsupp.single_eq_of_ne hj]) (by simp)]`. Simplify using the standard rewrite rules.

Use `⟨Z, et, prop_powObj @IsFinite _ hfin r, prop_powObj @Etale _ het r, hadd, fun a => ?_, fun T et' hadd' hpow' => ?_⟩` and prove the remaining obligations. Simplify using `only [et, ← Finset.prod_pow]`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]`. Use `choose y hy hyu using fun i : Fin r => existsUnique_torsion G n (et' (b i)) (hpow' _)`.

Set `h : T ⟶ Z` to `(Out.powIsLimit (torsion G n) r).lift (Fan.mk T y)`. Establish `hh : ∀ i, h ≫ Out.powPr (torsion G n) i = y i` using `fun i => (Out.powIsLimit (torsion G n) r).fac (Fan.mk T y) ⟨i⟩`. Use `⟨h, fun a => ?_, fun h' hh' => ?_⟩` and prove the remaining obligations. Rewrite using `[eq_prod_zpow b (fun a => h ≫ et a) (fun a c => by rw [hadd, MonObj.comp_mul]) a, eq_prod_zpow b et' hadd' a]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hb, ← hy i, ← hh i, Category.assoc]`. Use `(Out.powIsLimit (torsion G n) r).hom_ext fun ⟨i⟩ => ?_` and prove the remaining obligations. Use `(hyu i _ ?_).trans (hh i).symm` and prove the remaining obligations. Use `hh' (b i)` as an intermediate fact. Rewrite `this` using `[hb]`.

Conclude with `(Category.assoc _ _ _).trans this`.
-/
theorem exists_finiteEtale_latticeTorsionHom :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La], IsAbelianScheme G → IsUnit (n : Γ(S, ⊤)) → ∃ (Z : Over S) (et : La → (Z ⟶ G)), IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ a c, et (a + c) = et a * et c) ∧ (∀ a, et a ^ n = 1) ∧ ∀ (T : Over S) (et' : La → (T ⟶ G)), (∀ a c, et' (a + c) = et' a * et' c) → (∀ a, et' a ^ n = 1) → ∃! h : T ⟶ Z, ∀ a, h ≫ et a = et' a := by
  intro S G _ _ n La _ _ _ hG hn
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion G hn
  let b := Module.finBasis ℤ La
  let r := Module.finrank ℤ La
  let Z := Out.powObj (torsion G n) r
  let x : Fin r → (Z ⟶ G) := fun i => Out.powPr (torsion G n) i ≫ torsion.ι G n
  have hx : ∀ i, x i ^ n = 1 := fun i => by
    rw [← MonObj.comp_pow, torsionι_pow_eq_one, MonObj.comp_one]
  let et : La → (Z ⟶ G) := fun a => ∏ i, x i ^ (b.repr a i)
  have hadd : ∀ a c, et (a + c) = et a * et c := fun a c => by
    simp only [et, map_add, Finsupp.add_apply, zpow_add, Finset.prod_mul_distrib]
  have hb : ∀ i, et (b i) = x i := fun i => by
    simp only [et, Module.Basis.repr_self]
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [Finsupp.single_eq_of_ne hj]) (by simp)]
    simp
  refine ⟨Z, et, prop_powObj @IsFinite _ hfin r, prop_powObj @Etale _ het r, hadd, fun a => ?_,
    fun T et' hadd' hpow' => ?_⟩
  · simp only [et, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  · choose y hy hyu using fun i : Fin r => existsUnique_torsion G n (et' (b i)) (hpow' _)
    let h : T ⟶ Z := (Out.powIsLimit (torsion G n) r).lift (Fan.mk T y)
    have hh : ∀ i, h ≫ Out.powPr (torsion G n) i = y i := fun i =>
      (Out.powIsLimit (torsion G n) r).fac (Fan.mk T y) ⟨i⟩
    refine ⟨h, fun a => ?_, fun h' hh' => ?_⟩
    · rw [eq_prod_zpow b (fun a => h ≫ et a) (fun a c => by rw [hadd, MonObj.comp_mul]) a,
        eq_prod_zpow b et' hadd' a]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hb, ← hy i, ← hh i, Category.assoc]
    · refine (Out.powIsLimit (torsion G n) r).hom_ext fun ⟨i⟩ => ?_
      refine (hyu i _ ?_).trans (hh i).symm
      have := hh' (b i)
      rw [hb] at this
      exact (Category.assoc _ _ _).trans this

end GlobalTheory
