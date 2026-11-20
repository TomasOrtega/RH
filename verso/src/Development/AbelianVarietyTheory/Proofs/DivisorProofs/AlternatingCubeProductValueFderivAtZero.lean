import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.AltJet

def thI (s : Finset (Fin 3)) : thK.{0} := ULift.up s

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem thI_down (s : Finset (Fin 3)) : (thI s).down = s := rfl

/- English proof (translation)
Use `(Fintype.prod_equiv (Equiv.ulift.symm : Finset (Fin 3) ≃ thK.{0}) (fun I => f (thI I)) f (fun _ => rfl)).symm.trans ?_` and prove the remaining obligations. Establish `hu : (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}}` using `by decide`. Rewrite using `[hu]`. Simplify using `(config := {decide := true}) [Finset.prod_insert]`.
-/
theorem prod_thK {M : Type*} [CommMonoid M] (f : thK.{0} → M) :
    ∏ I : thK.{0}, f I = f (thI ∅) * (f (thI {0}) * (f (thI {1}) * (f (thI {2}) *
      (f (thI {0, 1}) * (f (thI {0, 2}) * (f (thI {1, 2}) * f (thI {0, 1, 2}))))))) := by
  refine (Fintype.prod_equiv (Equiv.ulift.symm : Finset (Fin 3) ≃ thK.{0}) (fun I => f (thI I)) f
    (fun _ => rfl)).symm.trans ?_
  have hu : (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  rw [hu]
  simp (config := {decide := true}) [Finset.prod_insert]

/- English proof (translation)
Use `(Fintype.sum_equiv (Equiv.ulift.symm : Finset (Fin 3) ≃ thK.{0}) (fun I => f (thI I)) f (fun _ => rfl)).symm.trans ?_` and prove the remaining obligations. Establish `hu : (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}}` using `by decide`. Rewrite using `[hu]`. Simplify using `(config := {decide := true}) [Finset.sum_insert]`.
-/
theorem sum_thK {M : Type*} [AddCommMonoid M] (f : thK.{0} → M) :
    ∑ I : thK.{0}, f I = f (thI ∅) + (f (thI {0}) + (f (thI {1}) + (f (thI {2}) +
      (f (thI {0, 1}) + (f (thI {0, 2}) + (f (thI {1, 2}) + f (thI {0, 1, 2}))))))) := by
  refine (Fintype.sum_equiv (Equiv.ulift.symm : Finset (Fin 3) ≃ thK.{0}) (fun I => f (thI I)) f
    (fun _ => rfl)).symm.trans ?_
  have hu : (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  rw [hu]
  simp (config := {decide := true}) [Finset.sum_insert]

/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem thε_thI_empty : thε (thI ∅) = -1 := by decide
/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem thε_thI_0 : thε (thI {0}) = 1 := by decide
/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem thε_thI_1 : thε (thI {1}) = 1 := by decide
/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem thε_thI_2 : thε (thI {2}) = 1 := by decide
/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem thε_thI_01 : thε (thI {0, 1}) = -1 := by decide
/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem thε_thI_02 : thε (thI {0, 2}) = -1 := by decide
/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem thε_thI_12 : thε (thI {1, 2}) = -1 := by decide
/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem thetaCubeSign_full : thε (thI {0, 1, 2}) = 1 := by decide

/- English proof (translation)
Establish `hz : ∀ i ∈ s, HasFDerivAt (fun z => h i z ^ n i) (((n i : ℂ) * h i x ^ (n i - 1)) • h' i) x`. Introduce `i hi`. Conclude with `(hasDerivAt_zpow (n i) (h i x) (Or.inl (hn i hi))).comp_hasFDerivAt x (hd i hi)`. Use `HasFDerivAt.finsetProd (g := fun i z => h i z ^ n i) hz` as an intermediate fact. Use `this.congr_fderiv (Finset.sum_congr rfl fun i hi => ?_)` and prove the remaining obligations.

Establish `hm` using `Finset.mul_prod_erase s (fun j => h j x ^ n j) hi`. Rewrite `hm` using `[h1]`. Establish `hne : h i x ^ n i ≠ 0` using `zpow_ne_zero _ (hn i hi)`. Establish `he : ∏ j ∈ s.erase i, h j x ^ n j = (h i x ^ n i)⁻¹`. Conclude with `eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hm)`.

Rewrite using `[he, smul_smul, zpow_sub_one₀ (hn i hi)]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.
-/
theorem hasFDerivAt_prod_zpow_of_eq_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {κ : Type*} [DecidableEq κ] (s : Finset κ) (h : κ → E → ℂ) (h' : κ → E →L[ℂ] ℂ) (n : κ → ℤ) (x : E)
    (hd : ∀ i ∈ s, HasFDerivAt (h i) (h' i) x) (hn : ∀ i ∈ s, h i x ≠ 0)
    (h1 : ∏ i ∈ s, h i x ^ n i = 1) :
    HasFDerivAt (fun z => ∏ i ∈ s, h i z ^ n i) (∑ i ∈ s, ((n i : ℂ) / h i x) • h' i) x := by
  have hz : ∀ i ∈ s, HasFDerivAt (fun z => h i z ^ n i)
      (((n i : ℂ) * h i x ^ (n i - 1)) • h' i) x := by
    intro i hi
    exact (hasDerivAt_zpow (n i) (h i x) (Or.inl (hn i hi))).comp_hasFDerivAt x (hd i hi)
  have := HasFDerivAt.finsetProd (g := fun i z => h i z ^ n i) hz
  refine this.congr_fderiv (Finset.sum_congr rfl fun i hi => ?_)
  have hm := Finset.mul_prod_erase s (fun j => h j x ^ n j) hi
  rw [h1] at hm
  have hne : h i x ^ n i ≠ 0 := zpow_ne_zero _ (hn i hi)
  have he : ∏ j ∈ s.erase i, h j x ^ n j = (h i x ^ n i)⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hm)
  rw [he, smul_smul, zpow_sub_one₀ (hn i hi)]
  congr 1
  field_simp

section
variable {E : Type*} [AddCommMonoid E] (a b c : E)
/- English proof (translation)
The claim follows from `Finset.sum_empty`.
-/
@[simp] theorem vsum_empty : ∑ i ∈ (∅ : Finset (Fin 3)), ![a, b, c] i = 0 := Finset.sum_empty
/- English proof (translation)
The claim follows from `Finset.sum_singleton _ _`.
-/
@[simp] theorem vsum_0 : ∑ i ∈ ({0} : Finset (Fin 3)), ![a, b, c] i = a := Finset.sum_singleton _ _
/- English proof (translation)
The claim follows from `Finset.sum_singleton _ _`.
-/
@[simp] theorem vsum_1 : ∑ i ∈ ({1} : Finset (Fin 3)), ![a, b, c] i = b := Finset.sum_singleton _ _
/- English proof (translation)
The claim follows from `Finset.sum_singleton _ _`.
-/
@[simp] theorem vsum_2 : ∑ i ∈ ({2} : Finset (Fin 3)), ![a, b, c] i = c := Finset.sum_singleton _ _
/- English proof (translation)
The claim follows from `Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1)`.
-/
@[simp] theorem vsum_01 : ∑ i ∈ ({0, 1} : Finset (Fin 3)), ![a, b, c] i = a + b :=
  Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1)
/- English proof (translation)
The claim follows from `Finset.sum_pair (by decide : (0 : Fin 3) ≠ 2)`.
-/
@[simp] theorem vsum_02 : ∑ i ∈ ({0, 2} : Finset (Fin 3)), ![a, b, c] i = a + c :=
  Finset.sum_pair (by decide : (0 : Fin 3) ≠ 2)
/- English proof (translation)
The claim follows from `Finset.sum_pair (by decide : (1 : Fin 3) ≠ 2)`.
-/
@[simp] theorem vsum_12 : ∑ i ∈ ({1, 2} : Finset (Fin 3)), ![a, b, c] i = b + c :=
  Finset.sum_pair (by decide : (1 : Fin 3) ≠ 2)
/- English proof (translation)
Rewrite using `[Finset.sum_insert (by decide : (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3))), vsum_12]`. Both sides reduce to the same expression.
-/
@[simp] theorem sum_univ_finThree_vecThree : ∑ i ∈ ({0, 1, 2} : Finset (Fin 3)), ![a, b, c] i = a + (b + c) := by
  rw [Finset.sum_insert (by decide : (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3))), vsum_12]
  rfl
end

/- English proof (translation)
Introduce `g x y W fr F hF hd hn hpair`. Use `show F 0 = 1 ∧ fderiv ℂ F 0 W = fderiv ℂ (fr (thI {0, 1, 2})) (x + y) W / fr (thI {0, 1, 2}) (x + y) + fderiv ℂ (fr (thI {2})) 0 W / fr (thI {2}) 0 - fderiv ℂ (fr (thI {0, 2})) x W / fr (thI {0, 2}) x - fderiv ℂ (fr (thI {1, 2})) y W / fr (thI {1, 2}) y`. Establish `hw : ∀ I : thK.{0}, HasFDerivAt (fun z : Fin g → ℂ => ∑ i ∈ I.down, ![x, y, z] i) (∑ i ∈ I.down, ![0, 0, ContinuousLinearMap.id ℂ (Fin g → ℂ)] i) 0`. Introduce `I`. Use `HasFDerivAt.fun_sum (A := fun i (z : Fin g → ℂ) => ![x, y, z] i) (fun i _ => ?_)` and prove the remaining obligations.

Use `fin_cases i`. Conclude with `hasFDerivAt_const x (0 : Fin g → ℂ)`. Conclude with `hasFDerivAt_const y (0 : Fin g → ℂ)`. Conclude with `hasFDerivAt_id (0 : Fin g → ℂ)`. Establish `hc : ∀ I : thK.{0}, HasFDerivAt (fun z : Fin g → ℂ => fr I (∑ i ∈ I.down, ![x, y, z] i)) ((fderiv ℂ (fr I) (∑ i ∈ I.down, ![x, y, 0] i)).comp (∑ i ∈ I.down, ![0, 0, ContinuousLinearMap.id ℂ (Fin g → ℂ)] i)) 0` using `fun I => (hd I).hasFDerivAt.comp (0 : Fin g → ℂ) (hw I)`.

Establish `p0 : fr (thI {2}) = fr (thI ∅)` using `hpair (thI ∅) (by decide)`. Establish `p1 : fr (thI {0, 2}) = fr (thI {0})` using `(congrArg (fun s => fr (thI s)) (by decide : ({0, 2} : Finset (Fin 3)) = insert 2 {0})).trans (hpair (thI {0}) (by decide))`. Establish `p2 : fr (thI {1, 2}) = fr (thI {1})` using `(congrArg (fun s => fr (thI s)) (by decide : ({1, 2} : Finset (Fin 3)) = insert 2 {1})).trans (hpair (thI {1}) (by decide))`. Establish `p3 : fr (thI {0, 1, 2}) = fr (thI {0, 1})` using `(congrArg (fun s => fr (thI s)) (by decide : ({0, 1, 2} : Finset (Fin 3)) = insert 2 {0, 1})).trans (hpair (thI {0, 1}) (by decide))`. Establish `n0` using `hn (thI ∅)`.

Establish `n1` using `hn (thI {0})`. Establish `n2` using `hn (thI {1})`. Establish `n3` using `hn (thI {0, 1})`. Simplify using `only [thI_down, vsum_empty, vsum_0, vsum_1, vsum_01] at n0 n1 n2 n3`. Establish `hP0 : ∏ I : thK.{0}, fr I (∑ i ∈ I.down, ![x, y, 0] i) ^ thε I = 1`.

Rewrite using `[prod_thK]`. Simplify using `only [thI_down, vsum_empty, vsum_0, vsum_1, vsum_2, vsum_01, vsum_02, vsum_12, sum_univ_finThree_vecThree, thε_thI_empty, thε_thI_0, thε_thI_1, thε_thI_2, thε_thI_01, thε_thI_02, thε_thI_12, thetaCubeSign_full, p0, p1, p2, p3, add_zero, zpow_one, _root_.zpow_neg, zpow_one]`. Clear the denominators using the available nonvanishing facts. Use `⟨by rw [hF.eq_of_nhds]; exact hP0, ?_⟩` and prove the remaining obligations. Establish `hPd` using `hasFDerivAt_prod_zpow_of_eq_one (Finset.univ : Finset thK.{0}) (fun (I : thK.{0}) (z : Fin g → ℂ) => fr I (∑ i ∈ I.down, ![x, y, z] i)) _ thε 0 (fun I _ => hc I) (fun I _ => hn I) hP0`.

Rewrite using `[hF.fderiv_eq (𝕜 := ℂ), hPd.fderiv]`. Rewrite using `[ContinuousLinearMap.sum_apply, sum_thK]`. Simplify using `only [thI_down, vsum_empty, vsum_0, vsum_1, vsum_2, vsum_01, vsum_02, vsum_12, sum_univ_finThree_vecThree, thε_thI_empty, thε_thI_0, thε_thI_1, thε_thI_2, thε_thI_01, thε_thI_02, thε_thI_12, thetaCubeSign_full, add_zero, zero_add, ContinuousLinearMap.smul_apply, ContinuousLinearM …`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem value_and_fderiv_at_zero : ∀ {g : ℕ} (x y W : Fin g → ℂ) (fr : thK.{0} → (Fin g → ℂ) → ℂ) (F : (Fin g → ℂ) → ℂ),
    F =ᶠ[nhds 0] (fun z => ∏ I : thK.{0}, fr I (∑ i ∈ I.down, ![x, y, z] i) ^ thε I) →
    (∀ I : thK.{0}, DifferentiableAt ℂ (fr I) (∑ i ∈ I.down, ![x, y, 0] i)) →
    (∀ I : thK.{0}, fr I (∑ i ∈ I.down, ![x, y, 0] i) ≠ 0) →
    (∀ I : thK.{0}, 2 ∉ I.down → fr (ULift.up (insert 2 I.down)) = fr I) →
    F 0 = 1 ∧ fderiv ℂ F 0 W =
      fderiv ℂ (fr (ULift.up {0, 1, 2})) (x + y) W / fr (ULift.up {0, 1, 2}) (x + y) +
        fderiv ℂ (fr (ULift.up {2})) 0 W / fr (ULift.up {2}) 0 -
        fderiv ℂ (fr (ULift.up {0, 2})) x W / fr (ULift.up {0, 2}) x -
        fderiv ℂ (fr (ULift.up {1, 2})) y W / fr (ULift.up {1, 2}) y := by
  intro g x y W fr F hF hd hn hpair
  show F 0 = 1 ∧ fderiv ℂ F 0 W =
      fderiv ℂ (fr (thI {0, 1, 2})) (x + y) W / fr (thI {0, 1, 2}) (x + y) +
        fderiv ℂ (fr (thI {2})) 0 W / fr (thI {2}) 0 -
        fderiv ℂ (fr (thI {0, 2})) x W / fr (thI {0, 2}) x -
        fderiv ℂ (fr (thI {1, 2})) y W / fr (thI {1, 2}) y
  have hw : ∀ I : thK.{0}, HasFDerivAt (fun z : Fin g → ℂ => ∑ i ∈ I.down, ![x, y, z] i)
      (∑ i ∈ I.down, ![0, 0, ContinuousLinearMap.id ℂ (Fin g → ℂ)] i) 0 := by
    intro I
    refine HasFDerivAt.fun_sum (A := fun i (z : Fin g → ℂ) => ![x, y, z] i) (fun i _ => ?_)
    fin_cases i
    · exact hasFDerivAt_const x (0 : Fin g → ℂ)
    · exact hasFDerivAt_const y (0 : Fin g → ℂ)
    · exact hasFDerivAt_id (0 : Fin g → ℂ)
  have hc : ∀ I : thK.{0}, HasFDerivAt (fun z : Fin g → ℂ => fr I (∑ i ∈ I.down, ![x, y, z] i))
      ((fderiv ℂ (fr I) (∑ i ∈ I.down, ![x, y, 0] i)).comp
        (∑ i ∈ I.down, ![0, 0, ContinuousLinearMap.id ℂ (Fin g → ℂ)] i)) 0 :=
    fun I => (hd I).hasFDerivAt.comp (0 : Fin g → ℂ) (hw I)
  have p0 : fr (thI {2}) = fr (thI ∅) := hpair (thI ∅) (by decide)
  have p1 : fr (thI {0, 2}) = fr (thI {0}) :=
    (congrArg (fun s => fr (thI s)) (by decide : ({0, 2} : Finset (Fin 3)) = insert 2 {0})).trans
      (hpair (thI {0}) (by decide))
  have p2 : fr (thI {1, 2}) = fr (thI {1}) :=
    (congrArg (fun s => fr (thI s)) (by decide : ({1, 2} : Finset (Fin 3)) = insert 2 {1})).trans
      (hpair (thI {1}) (by decide))
  have p3 : fr (thI {0, 1, 2}) = fr (thI {0, 1}) :=
    (congrArg (fun s => fr (thI s)) (by decide : ({0, 1, 2} : Finset (Fin 3)) = insert 2 {0, 1})).trans
      (hpair (thI {0, 1}) (by decide))
  have n0 := hn (thI ∅)
  have n1 := hn (thI {0})
  have n2 := hn (thI {1})
  have n3 := hn (thI {0, 1})
  simp only [thI_down, vsum_empty, vsum_0, vsum_1, vsum_01] at n0 n1 n2 n3
  have hP0 : ∏ I : thK.{0}, fr I (∑ i ∈ I.down, ![x, y, 0] i) ^ thε I = 1 := by
    rw [prod_thK]
    simp only [thI_down, vsum_empty, vsum_0, vsum_1, vsum_2, vsum_01, vsum_02, vsum_12, sum_univ_finThree_vecThree,
      thε_thI_empty, thε_thI_0, thε_thI_1, thε_thI_2, thε_thI_01, thε_thI_02, thε_thI_12,
      thetaCubeSign_full, p0, p1, p2, p3, add_zero, zpow_one, _root_.zpow_neg, zpow_one]
    field_simp
  refine ⟨by rw [hF.eq_of_nhds]; exact hP0, ?_⟩
  classical
  have hPd := hasFDerivAt_prod_zpow_of_eq_one (Finset.univ : Finset thK.{0})
    (fun (I : thK.{0}) (z : Fin g → ℂ) => fr I (∑ i ∈ I.down, ![x, y, z] i)) _ thε 0
    (fun I _ => hc I) (fun I _ => hn I) hP0
  rw [hF.fderiv_eq (𝕜 := ℂ), hPd.fderiv]
  rw [ContinuousLinearMap.sum_apply, sum_thK]
  simp only [thI_down, vsum_empty, vsum_0, vsum_1, vsum_2, vsum_01, vsum_02, vsum_12, sum_univ_finThree_vecThree,
      thε_thI_empty, thε_thI_0, thε_thI_1, thε_thI_2, thε_thI_01, thε_thI_02, thε_thI_12,
      thetaCubeSign_full, add_zero, zero_add, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply, map_zero, smul_zero,
      smul_eq_mul, Int.cast_one, Int.cast_neg]
  ring

end GlobalTheory.AltJet
