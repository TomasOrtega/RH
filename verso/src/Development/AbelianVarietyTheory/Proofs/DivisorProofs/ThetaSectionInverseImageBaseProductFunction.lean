import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl

/- English proof (translation)
The claim follows from `LB.wchart_le P.L (fun _ : Fin 1 => (snd T P.A).left) j 0`.
-/
theorem lpow_le {S : Scheme.{0}} (P : PolAV S) (T : Over S) (k : ℤ) (j : Fin 1 → P.L.ι) :
    (LPow P.A P.L k T).U j ≤ (snd T P.A).left ⁻¹ᵁ P.L.U (j 0) :=
  LB.wchart_le P.L (fun _ : Fin 1 => (snd T P.A).left) j 0

/- English proof (translation)
Rewrite using `[← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]`.
-/
theorem appLE_swap {X Y : Scheme.{0}} (φ : Y ⟶ X) {U U' : X.Opens} {V V' : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (h' : V' ≤ φ ⁻¹ᵁ U')
    (a : V' ≤ V) (b : U' ≤ U) (f : Γ(X, U)) :
    (Y.presheaf.map (homOfLE a).op).hom ((φ.appLE U V h).hom f) =
      (φ.appLE U' V' h').hom ((X.presheaf.map (homOfLE b).op).hom f) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

/- English proof (translation)
Unfold `LB.LinComb`. Simplify using `only`. Rewrite using `[Fin.prod_univ_one, Nat.cast_one, zpow_one]`. Both sides reduce to the same expression.
-/
theorem linComb_g_one {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (i j : Fin 1 → L.ι) :
    ((LB.LinComb L (fun _ : Fin 1 => φ) (fun _ => ((1 : ℕ) : ℤ))).g i j).val =
      (φ.appLE (L.U (i 0) ⊓ L.U (j 0)) (LB.wchart L (fun _ : Fin 1 => φ) i ⊓ LB.wchart L (fun _ : Fin 1 => φ) j)
        (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : Fin 1 => φ) i 0))
          (inf_le_right.trans (LB.wchart_le L (fun _ : Fin 1 => φ) j 0)))).hom (L.g (i 0) (j 0)).val := by
  unfold LB.LinComb
  dsimp only
  rw [Fin.prod_univ_one, Nat.cast_one, zpow_one]
  rfl

def pullSec1 {S : Scheme.{0}} (P : PolAV S) (T : Over S) (s : P.L.Sec) :
    LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T) where
  f j := ((snd T P.A).left.appLE _ _ (lpow_le P T _ j)).hom (s.f (j 0))
  compat i j := by
    have h := congrArg ((snd T P.A).left.appLE (P.L.U (i 0) ⊓ P.L.U (j 0))
      ((LPow P.A P.L ((1 : ℕ) : ℤ) T).U i ⊓ (LPow P.A P.L ((1 : ℕ) : ℤ) T).U j)
      (le_inf (inf_le_left.trans (lpow_le P T _ i)) (inf_le_right.trans (lpow_le P T _ j)))).hom (s.compat (i 0) (j 0))
    rw [map_mul] at h
    refine (appLE_swap _ _ _ _ _ _).trans (h.trans (congrArg₂ (· * ·) ?_ (appLE_swap _ _ _ _ _ _).symm))
    exact (linComb_g_one P.L (snd T P.A).left i j).symm

/- English proof (translation)
Introduce `_ _` and use `rfl`.
-/
theorem pullbackSectionToBaseChangedAbelian_isInverseImage {S : Scheme.{0}} (P : PolAV S) (T : Over S) (s : P.L.Sec) : IsPolAVSectionInverseImage P T s (pullSec1 P T s) :=
  fun _ _ => rfl

/- English proof (translation)
Rewrite using `[← Over.comp_left, ptSecT, lift_snd]`.
-/
theorem ptSecT_snd' {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} (z : T ⟶ A) :
    (ptSecT A z).left ≫ (snd T A).left = z.left := by
  rw [← Over.comp_left, ptSecT, lift_snd]

/- English proof (translation)
Establish `h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U` using `fun p hp => h (hx hp)`. Rewrite using `[valR, valR, dif_pos hx, dif_pos h', ← CommRingCat.comp_apply (φ.appLE U V h), Scheme.Hom.appLE_comp_appLE]`.
-/
theorem valR_appLE' {R : Type} [CommRing R] {X Y : Scheme.{0}} (x : Sp R ⟶ Y) (φ : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (h : V ≤ φ ⁻¹ᵁ U) (hx : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    valR x V ((φ.appLE U V h).hom f) = valR (x ≫ φ) U f := by
  have h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := fun p hp => h (hx hp)
  rw [valR, valR, dif_pos hx, dif_pos h', ← CommRingCat.comp_apply (φ.appLE U V h), Scheme.Hom.appLE_comp_appLE]

/- English proof (translation)
Unfold `valR valAt' valAt`. Reduce the equality to equality of the corresponding arguments.
-/
theorem valR_eq_valAt' {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : valR x U f = valAt' x U f := by
  unfold valR valAt' valAt
  congr

/- English proof (translation)
Introduce `i z hz`. Establish `e` using `ptSecT_snd' P.A (T := baseOver (Sp ℂ)) (u.ex z)`. Establish `hx : ⊤ ≤ (ptSecT P.A (T` using `baseOver (Sp ℂ)) (u.ex z)).left ⁻¹ᵁ (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver (Sp ℂ))).U (fun _ => i) := fun p hp => val_le P.A P.L (T := baseOver (Sp ℂ)) (u.ex z) (fun _ => i) (Set.mem_iInter.2 fun _ => hz hp)`. Rewrite using `[H i (lpow_le P _ _ fun _ => i), pow_one, ← h i z hz, ← valR_eq_valAt']`. Use `(valR_appLE' _ _ _ _ _ hx _).trans ?_` and prove the remaining obligations.

Conclude with `congrArg (fun y => valR y (P.L.U i) (s.f i)) e`.
-/
theorem powerSectionFunctionInFrame_of_inverseImage {P : PolAV (Sp ℂ)} {g : ℕ} (u : HolUnif P.A P.L g) (s : P.L.Sec) (θ) (h : u.IsFn s θ)
    (th) (H : IsPolAVSectionInverseImage P (baseOver (Sp ℂ)) s th) : FnT u 1 th θ := by
  intro i z hz
  have e := ptSecT_snd' P.A (T := baseOver (Sp ℂ)) (u.ex z)
  have hx : ⊤ ≤ (ptSecT P.A (T := baseOver (Sp ℂ)) (u.ex z)).left ⁻¹ᵁ
      (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver (Sp ℂ))).U (fun _ => i) := fun p hp =>
    val_le P.A P.L (T := baseOver (Sp ℂ)) (u.ex z) (fun _ => i) (Set.mem_iInter.2 fun _ => hz hp)
  rw [H i (lpow_le P _ _ fun _ => i), pow_one, ← h i z hz, ← valR_eq_valAt']
  refine (valR_appLE' _ _ _ _ _ hx _).trans ?_
  exact congrArg (fun y => valR y (P.L.U i) (s.f i)) e

/- English proof (translation)
Take `⟨i, rfl⟩ : ∃ i : P.L.ι, j = fun _ => i` from `⟨j 0, funext fun a => congrArg j (Subsingleton.elim _ _)⟩`. Establish `hp : (baseOver (Sp ℂ) ⊗ P.A).hom = pullback.fst (𝟙 (Sp ℂ)) P.A.hom` using `Category.comp_id _`. Use `P.isAb.smooth` as an intermediate fact. Establish `: Smooth (baseOver (Sp ℂ) ⊗ P.A).hom` using `by rw [hp]; infer_instance`. Use `isReduced_of_smooth_complex _ (baseOver (Sp ℂ) ⊗ P.A).hom inferInstance` as an intermediate fact.

Use `ComplexPoints.eq_of_valAt'_eq (baseOver (Sp ℂ) ⊗ P.A).hom _ _ _ fun x hx hi => ?_` and prove the remaining obligations. Set `x' : baseOver (Sp ℂ) ⟶ baseOver (Sp ℂ) ⊗ P.A` to `Over.homMk x hx`. Take `⟨z, hz⟩` from `u.ex_onto (x' ≫ snd _ _)`. Establish `e : ptSecT P.A (T` using `baseOver (Sp ℂ)) (u.ex z) = x' := by`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises.

Rewrite using `[ptSecT, lift_fst]`. Use `Over.OverMorphism.ext ?_` and prove the remaining obligations. Conclude with `((Category.comp_id _).symm.trans (Over.w (x' ≫ fst _ _))).symm`. Rewrite using `[ptSecT, lift_snd]`. Conclude with `hz`.

Take `rfl : (ptSecT P.A (T` from `baseOver (Sp ℂ)) (u.ex z)).left = x := congrArg (·.left) e`. Establish `hz' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i`. Introduce `p hp`. Use `lpow_le P _ (k : ℤ) (fun _ => i) (hi hp)` as an intermediate fact. Rewrite using `[← ptSecT_snd' P.A (T := baseOver (Sp ℂ)) (u.ex z)]`.

Conclude with `this`. Rewrite using `[← valR_eq_valAt', ← valR_eq_valAt']`. Conclude with `(h i z hz').trans (h' i z hz').symm`.
-/
theorem eq_of_fnT {P : PolAV (Sp ℂ)} {g : ℕ} (u : HolUnif P.A P.L g) (k : ℕ)
    (t t' : LB.Sec (LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ)))) (f) (h : FnT u k t f) (h' : FnT u k t' f) (j) :
    t.f j = t'.f j := by
  obtain ⟨i, rfl⟩ : ∃ i : P.L.ι, j = fun _ => i := ⟨j 0, funext fun a => congrArg j (Subsingleton.elim _ _)⟩
  have hp : (baseOver (Sp ℂ) ⊗ P.A).hom = pullback.fst (𝟙 (Sp ℂ)) P.A.hom := Category.comp_id _
  have := P.isAb.smooth
  have : Smooth (baseOver (Sp ℂ) ⊗ P.A).hom := by rw [hp]; infer_instance
  have := isReduced_of_smooth_complex _ (baseOver (Sp ℂ) ⊗ P.A).hom inferInstance
  refine ComplexPoints.eq_of_valAt'_eq (baseOver (Sp ℂ) ⊗ P.A).hom _ _ _ fun x hx hi => ?_
  let x' : baseOver (Sp ℂ) ⟶ baseOver (Sp ℂ) ⊗ P.A := Over.homMk x hx
  obtain ⟨z, hz⟩ := u.ex_onto (x' ≫ snd _ _)
  have e : ptSecT P.A (T := baseOver (Sp ℂ)) (u.ex z) = x' := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [ptSecT, lift_fst]
      refine Over.OverMorphism.ext ?_
      exact ((Category.comp_id _).symm.trans (Over.w (x' ≫ fst _ _))).symm
    · rw [ptSecT, lift_snd]; exact hz
  obtain rfl : (ptSecT P.A (T := baseOver (Sp ℂ)) (u.ex z)).left = x := congrArg (·.left) e
  have hz' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i := by
    intro p hp
    have := lpow_le P _ (k : ℤ) (fun _ => i) (hi hp)
    rw [← ptSecT_snd' P.A (T := baseOver (Sp ℂ)) (u.ex z)]
    exact this
  rw [← valR_eq_valAt', ← valR_eq_valAt']
  exact (h i z hz').trans (h' i z hz').symm

/- English proof (translation)
Introduce `_ x _ u _ _ _ _ _ h` and use `⟨⟨_, pullbackSectionToBaseChangedAbelian_isInverseImage x.P _ x.th⟩, powerSectionFunctionInFrame_of_inverseImage u x.th _ h.2.2.2.2.2.2.2.1, fun k t t' f => eq_of_fnT u k t t' f⟩`.
-/
theorem thetaSection_fnT_thetaChar_and_unique : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → (∃ th, IsPolAVSectionInverseImage x.P (baseOver (Sp ℂ)) x.th th) ∧ (∀ th, IsPolAVSectionInverseImage x.P (baseOver (Sp ℂ)) x.th th → FnT u 1 th fun z => c * thetaChar τ a b z) ∧ ∀ (k : ℕ) (t t' : LB.Sec (LPow x.P.A x.P.L (k : ℤ) (baseOver (Sp ℂ)))) f, FnT u k t f → FnT u k t' f → ∀ j, t.f j = t'.f j :=
  fun _ x _ u _ _ _ _ _ h => ⟨⟨_, pullbackSectionToBaseChangedAbelian_isInverseImage x.P _ x.th⟩, powerSectionFunctionInFrame_of_inverseImage u x.th _ h.2.2.2.2.2.2.2.1,
    fun k t t' f => eq_of_fnT u k t t' f⟩

end GlobalTheory.MBLow.Cl

end
