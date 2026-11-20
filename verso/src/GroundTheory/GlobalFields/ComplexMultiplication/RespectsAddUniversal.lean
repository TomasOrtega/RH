import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualIsogeny
import GroundTheory.ArithmeticGeometry.AbelianVarieties.ReductionTorsion

namespace GroundTheory.Global

noncomputable section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine GroundTheory.Arith.Abelian IntermediateField

universe u

variable {F : Type u} [Field F]

section AlgPts

variable (E : WeierstrassCurve F) (L : Type*) {M : Type*} [Field L] [Algebra F L] [Field M]
  [Algebra F M] [Algebra L M] [IsScalarTower F L M] [DecidableEq M]

def TransOver : (E.baseChange M).toAffine.Point → Prop
  | .zero => False
  | .some x _ _ => Transcendental L x

def algPts : AddSubgroup (E.baseChange M).toAffine.Point :=
  (Point.map (W' := E) ((algebraicClosure L M).val.restrictScalars F)).range

omit [DecidableEq M] in

/- English proof (translation)
Use `set S := algebraicClosure L M`. Establish `e` using `(equation_iff _ _).mp h`. Simplify using `only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e`. Establish `hc : ∀ c : F, algebraMap F M c ∈ S` using `fun c => by`. Rewrite using `[IsScalarTower.algebraMap_apply F L M]`.

Conclude with `S.algebraMap_mem _`. Take `⟨c₁, hc₁⟩ : ∃ c₁ : S, (c₁ : M) = algebraMap F M E.a₁ * x + algebraMap F M E.a₃` from `⟨⟨_, S.add_mem (S.mul_mem (hc _) hx) (hc _)⟩, rfl⟩`. Take `⟨c₀, hc₀⟩ : ∃ c₀ : S, (c₀ : M) = x ^ 3 + algebraMap F M E.a₂ * x ^ 2 + algebraMap F M E.a₄ * x + algebraMap F M E.a₆` from `⟨⟨_, S.add_mem (S.add_mem (S.add_mem (pow_mem hx 3) (S.mul_mem (hc _) (pow_mem hx 2))) (S.mul_mem (hc _) hx)) (hc _)⟩, rfl⟩`. Establish `hy : IsIntegral S y`. Use `⟨X ^ 2 + C c₁ * X - C c₀, ?_, ?_⟩` and prove the remaining obligations.

Establish `: (X ^ 2 + C c₁ * X - C c₀ : S[X]) = X ^ 2 + (C c₁ * X - C c₀)` using `by ring`. Rewrite using `[this]`. Conclude with `monic_X_pow_add (by compute_degree!)`. Establish `key : y ^ 2 + (algebraMap F M E.a₁ * x + algebraMap F M E.a₃) * y - (x ^ 3 + algebraMap F M E.a₂ * x ^ 2 + algebraMap F M E.a₄ * x + algebraMap F M E.a₆) = 0` using `by linear_combination e`. Simplify using `only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, IntermediateField.algebraMap_apply, hc₁, hc₀]`.

Conclude with `key`. Conclude with `mem_algebraicClosure_iff'.2 (isIntegral_trans (R := L) (A := S) y hy)`.
-/
theorem isIntegral_y {x y : M} (h : (E.baseChange M).toAffine.Equation x y)
    (hx : x ∈ algebraicClosure L M) : y ∈ algebraicClosure L M := by
  set S := algebraicClosure L M
  have e := (equation_iff _ _).mp h
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e
  have hc : ∀ c : F, algebraMap F M c ∈ S := fun c => by
    rw [IsScalarTower.algebraMap_apply F L M]; exact S.algebraMap_mem _
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : S, (c₁ : M) = algebraMap F M E.a₁ * x + algebraMap F M E.a₃ :=
    ⟨⟨_, S.add_mem (S.mul_mem (hc _) hx) (hc _)⟩, rfl⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : S, (c₀ : M) = x ^ 3 + algebraMap F M E.a₂ * x ^ 2 +
      algebraMap F M E.a₄ * x + algebraMap F M E.a₆ :=
    ⟨⟨_, S.add_mem (S.add_mem (S.add_mem (pow_mem hx 3)
      (S.mul_mem (hc _) (pow_mem hx 2))) (S.mul_mem (hc _) hx)) (hc _)⟩, rfl⟩
  have hy : IsIntegral S y := by
    refine ⟨X ^ 2 + C c₁ * X - C c₀, ?_, ?_⟩
    · have : (X ^ 2 + C c₁ * X - C c₀ : S[X]) = X ^ 2 + (C c₁ * X - C c₀) := by ring
      rw [this]
      exact monic_X_pow_add (by compute_degree!)
    · have key : y ^ 2 + (algebraMap F M E.a₁ * x + algebraMap F M E.a₃) * y -
          (x ^ 3 + algebraMap F M E.a₂ * x ^ 2 + algebraMap F M E.a₄ * x + algebraMap F M E.a₆) =
            0 := by linear_combination e
      simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
        IntermediateField.algebraMap_apply, hc₁, hc₀]
      exact key
  exact mem_algebraicClosure_iff'.2 (isIntegral_trans (R := L) (A := S) y hy)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨P, hP⟩`. Consider the cases of `P with`. Consider the case `zero => exact absurd hP (Point.some_ne_zero h).symm`. Consider the case `some u v h'`.

Rewrite `hP` using `[Point.map_some, Point.some.injEq]`. Rewrite using `[← hP.1]`. Conclude with `mem_algebraicClosure_iff.1 u.2`. Introduce `hx`. Establish `hx'` using `mem_algebraicClosure_iff.2 hx`.

Establish `hy` using `isIntegral_y E L h.1 hx'`. Establish `h' : (E.baseChange (algebraicClosure L M)).toAffine.Nonsingular ⟨x, hx'⟩ ⟨y, hy⟩` using `(E.toAffine.baseChange_nonsingular (f := (algebraicClosure L M).val.restrictScalars F) (algebraicClosure L M).val.injective _ _).mp h`. Conclude with `⟨.some _ _ h', by rw [Point.map_some]; rfl⟩`.
-/
theorem mem_algPts_iff_of_ne_zero {x y : M} (h : (E.baseChange M).toAffine.Nonsingular x y) :
    (Point.some x y h) ∈ algPts E L ↔ IsAlgebraic L x := by
  constructor
  · rintro ⟨P, hP⟩
    cases P with
    | zero => exact absurd hP (Point.some_ne_zero h).symm
    | some u v h' =>
      rw [Point.map_some, Point.some.injEq] at hP
      rw [← hP.1]
      exact mem_algebraicClosure_iff.1 u.2
  · intro hx
    have hx' := mem_algebraicClosure_iff.2 hx
    have hy := isIntegral_y E L h.1 hx'
    have h' : (E.baseChange (algebraicClosure L M)).toAffine.Nonsingular ⟨x, hx'⟩ ⟨y, hy⟩ :=
      (E.toAffine.baseChange_nonsingular (f := (algebraicClosure L M).val.restrictScalars F)
        (algebraicClosure L M).val.injective _ _).mp h
    exact ⟨.some _ _ h', by rw [Point.map_some]; rfl⟩

end AlgPts

section Trans

variable (E : WeierstrassCurve F) {L M : Type*} [Field L] [Algebra F L] [Field M]
  [Algebra F M] [Algebra L M] [IsScalarTower F L M] [DecidableEq L] [DecidableEq M]

variable {E} in
/- English proof (translation)
Consider the cases of `P with`. Consider the case `zero => exact h.elim`. Consider the case `some x y _ => exact Transcendental.of_tower_top F h`.
-/
theorem TransOver.isGenPt {P : (E.baseChange M).toAffine.Point} (h : TransOver E L P) :
    IsGenPt E P := by
  cases P with
  | zero => exact h.elim
  | some x y _ => exact Transcendental.of_tower_top F h

/- English proof (translation)
Consider the cases of `P with`. Consider the case `zero => exact h (zero_mem _)`. Consider the case `some x y hxy => exact fun hx => h ((mem_algPts_iff_of_ne_zero E L hxy).2 hx)`.
-/
theorem transOver_of_notMem {P : (E.baseChange M).toAffine.Point} (h : P ∉ algPts E L) :
    TransOver E L P := by
  cases P with
  | zero => exact h (zero_mem _)
  | some x y hxy => exact fun hx => h ((mem_algPts_iff_of_ne_zero E L hxy).2 hx)

/- English proof (translation)
Consider the cases of `P with`. Consider the case `zero => exact h.elim`. Consider the case `some x y hxy => exact fun hm => h ((mem_algPts_iff_of_ne_zero E L hxy).1 hm)`.
-/
theorem notMem_of_transOver {P : (E.baseChange M).toAffine.Point} (h : TransOver E L P) :
    P ∉ algPts E L := by
  cases P with
  | zero => exact h.elim
  | some x y hxy => exact fun hm => h ((mem_algPts_iff_of_ne_zero E L hxy).1 hm)

/- English proof (translation)
Use `⟨Point.map ((IsScalarTower.toAlgHom L L (algebraicClosure L M)).restrictScalars F) A, ?_⟩` and prove the remaining obligations. Rewrite using `[Point.map_map]`. Use `congr 1`.
-/
theorem map_mem_algPts (A : (E.baseChange L).toAffine.Point) :
    Point.map (IsScalarTower.toAlgHom F L M) A ∈ algPts E L := by
  refine ⟨Point.map ((IsScalarTower.toAlgHom L L (algebraicClosure L M)).restrictScalars F) A, ?_⟩
  rw [Point.map_map]
  congr 1

variable {E} in
/- English proof (translation)
Use `transOver_of_notMem E fun hm => notMem_of_transOver E hB ?_` and prove the remaining obligations. Use `sub_mem hm (map_mem_algPts E A)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel_left]`. Then use the resulting hypothesis.
-/
theorem TransOver.add_left {B : (E.baseChange M).toAffine.Point} (hB : TransOver E L B)
    (A : (E.baseChange L).toAffine.Point) :
    TransOver E L (Point.map (IsScalarTower.toAlgHom F L M) A + B) := by
  refine transOver_of_notMem E fun hm => notMem_of_transOver E hB ?_
  have := sub_mem hm (map_mem_algPts E A)
  rwa [add_sub_cancel_left] at this

variable {E} in
/- English proof (translation)
Consider the cases of `B with`. Consider the case `zero => exact hB.elim`. Consider the case `some x y h => exact hB`.
-/
theorem TransOver.neg {B : (E.baseChange M).toAffine.Point} (hB : TransOver E L B) :
    TransOver E L (-B) := by
  cases B with
  | zero => exact hB.elim
  | some x y h => exact hB

end Trans

section BaseChange

omit [Field F] in
/- English proof (translation)
Use `show E.map ((algebraMap A B).comp (algebraMap F A)) = E.map (algebraMap F B)`. Rewrite using `[← IsScalarTower.algebraMap_eq]`.
-/
theorem baseChange_baseChange {F : Type*} [CommRing F] (E : WeierstrassCurve F) (A B : Type*)
    [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] [Algebra A B] [IsScalarTower F A B] :
    (E.baseChange A).baseChange B = E.baseChange B := by
  show E.map ((algebraMap A B).comp (algebraMap F A)) = E.map (algebraMap F B)
  rw [← IsScalarTower.algebraMap_eq]

end BaseChange

section Universal

variable (E : WeierstrassCurve F) [E.IsElliptic]

abbrev univField : Type u := (E.baseChange E.toAffine.FunctionField).toAffine.FunctionField

def univPt₁ : (E.baseChange (univField E)).toAffine.Point :=
  Point.map (IsScalarTower.toAlgHom F E.toAffine.FunctionField (univField E)) (genericPoint E)

def univPt₂ : (E.baseChange (univField E)).toAffine.Point :=
  pointCongr (baseChange_baseChange E _ _) (genericPoint (E.baseChange E.toAffine.FunctionField))

/- English proof (translation)
The claim follows from `isGenPt_map E _ (transcendental_genX E)`.
-/
theorem isGenPt_univPt₁ : IsGenPt E (univPt₁ E) :=
  isGenPt_map E _ (transcendental_genX E)

/- English proof (translation)
Rewrite using `[univPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some]`. Conclude with `transcendental_genX _`.
-/
theorem transOver_univPt₂ : TransOver E E.toAffine.FunctionField (univPt₂ E) := by
  rw [univPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some]
  exact transcendental_genX _

/- English proof (translation)
The claim follows from `(transOver_univPt₂ E).isGenPt`.
-/
theorem isGenPt_univPt₂ : IsGenPt E (univPt₂ E) := (transOver_univPt₂ E).isGenPt

/- English proof (translation)
Use `(transOver_univPt₂ E).add_left (genericPoint E)` as an intermediate fact. Conclude with `this.isGenPt`.
-/
theorem isGenPt_univPt₁₂ : IsGenPt E (univPt₁ E + univPt₂ E) := by
  have := (transOver_univPt₂ E).add_left (genericPoint E)
  exact this.isGenPt

variable {E} {E' : WeierstrassCurve F} [E'.IsElliptic]
  (Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point)

def UnivAdd : Prop :=
  Point.map (genEval E (univPt₁ E + univPt₂ E) (isGenPt_univPt₁₂ E)) Q =
    Point.map (genEval E (univPt₁ E) (isGenPt_univPt₁ E)) Q +
      Point.map (genEval E (univPt₂ E) (isGenPt_univPt₂ E)) Q

/- English proof (translation)
Rewrite using `[Point.map_map, ← genEval_map E τ hP]`.
-/
theorem map_genEval_map {L M : Type*} [Field L] [Algebra F L] [Field M] [Algebra F M]
    [DecidableEq L] [DecidableEq M] (τ : L →ₐ[F] M) {P : (E.baseChange L).toAffine.Point}
    (hP : IsGenPt E P) (hP' : IsGenPt E (Point.map τ P)) :
    Point.map (genEval E (Point.map τ P) hP') Q = Point.map τ (Point.map (genEval E P hP) Q) := by
  rw [Point.map_map, ← genEval_map E τ hP]

/- English proof (translation)
Use `set Fv := E.toAffine.FunctionField`. Use `set σA := genEval E A hA`. Use `letI : Algebra Fv L := σA.toRingHom.toAlgebra`. Use `letI : Algebra Fv M := ((algebraMap L M).comp σA.toRingHom).toAlgebra`. Use `haveI : IsScalarTower Fv L M := IsScalarTower.of_algebraMap_eq fun _ => rfl`.

Use `haveI : IsScalarTower F Fv M := IsScalarTower.of_algebraMap_eq fun c => by show algebraMap F M c = algebraMap L M (σA (algebraMap F Fv c))`. Rewrite using `[σA.commutes, ← IsScalarTower.algebraMap_apply]`. Consider the cases of `B with`. Consider the case `zero => exact hB.elim`. Consider the case `some x y h`.

Establish `h' : ((E.baseChange Fv).baseChange M).toAffine.Nonsingular x y`. Rewrite using `[baseChange_baseChange]`. Conclude with `h`. Establish `hB' : IsGenPt (E.baseChange Fv) (Point.some x y h')` using `Transcendental.restrictScalars (R := Fv) (S := L) σA.toRingHom.injective hB`. Use `set τ₀ := genEval (E.baseChange Fv) _ hB'`.

Use `set τ : univField E →ₐ[F] M := τ₀.restrictScalars F`. Establish `c₂ : Point.map τ (univPt₂ E) = Point.some x y h`. Rewrite using `[univPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some, Point.map_some, Point.some.injEq]`. Conclude with `⟨genEval_genX (E.baseChange Fv) _ hB', genEval_genY (E.baseChange Fv) _ hB'⟩`. Establish `hcomp : τ.comp (IsScalarTower.toAlgHom F Fv (univField E)) = (IsScalarTower.toAlgHom F L M).comp σA`.

Conclude with `AlgHom.ext fun f => τ₀.commutes f`. Establish `c₁ : Point.map τ (univPt₁ E) = Point.map (IsScalarTower.toAlgHom F L M) A`. Rewrite using `[univPt₁, Point.map_map, hcomp, ← Point.map_map, map_genEval_genericPoint]`. Establish `e` using `congrArg (Point.map τ) hQ`. Rewrite `e` using `[map_add, ← map_genEval_map Q τ _ (isGenPt_map E τ (isGenPt_univPt₁₂ E)), ← map_genEval_map Q τ _ (isGenPt_map E τ (isGenPt_univPt₁ E)), ← map_genEval_map Q τ _ (isGenPt_map E τ (isGenPt_univPt₂ E))]`.

Rewrite `e` using `[genEval_congr E (by rw [map_add, c₁, c₂]) _ (hB.add_left A).isGenPt, genEval_congr E c₁ _ (isGenPt_map E (IsScalarTower.toAlgHom F L M) hA), genEval_congr E c₂ _ hB.isGenPt]`. Conclude with `e`.
-/
theorem halfUniversal (hQ : UnivAdd Q) {L M : Type*} [Field L] [Algebra F L] [Field M]
    [Algebra F M] [Algebra L M] [IsScalarTower F L M] [DecidableEq L] [DecidableEq M]
    (A : (E.baseChange L).toAffine.Point) (hA : IsGenPt E A) (B : (E.baseChange M).toAffine.Point)
    (hB : TransOver E L B) :
    Point.map (genEval E _ (hB.add_left A).isGenPt) Q =
      Point.map (genEval E _ (isGenPt_map E (IsScalarTower.toAlgHom F L M) hA)) Q +
        Point.map (genEval E B hB.isGenPt) Q := by
  set Fv := E.toAffine.FunctionField
  set σA := genEval E A hA
  letI : Algebra Fv L := σA.toRingHom.toAlgebra
  letI : Algebra Fv M := ((algebraMap L M).comp σA.toRingHom).toAlgebra
  haveI : IsScalarTower Fv L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower F Fv M := IsScalarTower.of_algebraMap_eq fun c => by
    show algebraMap F M c = algebraMap L M (σA (algebraMap F Fv c))
    rw [σA.commutes, ← IsScalarTower.algebraMap_apply]
  cases B with
  | zero => exact hB.elim
  | some x y h =>
  have h' : ((E.baseChange Fv).baseChange M).toAffine.Nonsingular x y := by
    rw [baseChange_baseChange]; exact h
  have hB' : IsGenPt (E.baseChange Fv) (Point.some x y h') :=
    Transcendental.restrictScalars (R := Fv) (S := L) σA.toRingHom.injective hB
  set τ₀ := genEval (E.baseChange Fv) _ hB'
  set τ : univField E →ₐ[F] M := τ₀.restrictScalars F
  have c₂ : Point.map τ (univPt₂ E) = Point.some x y h := by
    rw [univPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some, Point.map_some, Point.some.injEq]
    exact ⟨genEval_genX (E.baseChange Fv) _ hB', genEval_genY (E.baseChange Fv) _ hB'⟩
  have hcomp : τ.comp (IsScalarTower.toAlgHom F Fv (univField E)) =
      (IsScalarTower.toAlgHom F L M).comp σA := by
    exact AlgHom.ext fun f => τ₀.commutes f
  have c₁ : Point.map τ (univPt₁ E) = Point.map (IsScalarTower.toAlgHom F L M) A := by
    rw [univPt₁, Point.map_map, hcomp, ← Point.map_map, map_genEval_genericPoint]
  have e := congrArg (Point.map τ) hQ
  rw [map_add, ← map_genEval_map Q τ _ (isGenPt_map E τ (isGenPt_univPt₁₂ E)),
    ← map_genEval_map Q τ _ (isGenPt_map E τ (isGenPt_univPt₁ E)),
    ← map_genEval_map Q τ _ (isGenPt_map E τ (isGenPt_univPt₂ E))] at e
  rw [genEval_congr E (by rw [map_add, c₁, c₂]) _ (hB.add_left A).isGenPt,
    genEval_congr E c₁ _ (isGenPt_map E (IsScalarTower.toAlgHom F L M) hA),
    genEval_congr E c₂ _ hB.isGenPt] at e
  exact e

end Universal

section Criterion

variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]
  (Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point)

/- English proof (translation)
Rewrite using `[respectsAdd_iff]`. Introduce `L _ _ _ P₁ P₂ h₁ h₂ h₃`. Use `set M := (E.baseChange L).toAffine.FunctionField`. Use `set ι := IsScalarTower.toAlgHom F L M`. Use `set T : (E.baseChange M).toAffine.Point := pointCongr (baseChange_baseChange E L M) (genericPoint (E.baseChange L))`.

Establish `hT : TransOver E L T`. Simplify using `only [T, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some]`. Conclude with `transcendental_genX _`. Establish `hnT` using `hT.neg`. Establish `hU` using `hnT.add_left P₂`.

Establish `e₁` using `halfUniversal Q hQ P₁ h₁ _ hU`. Establish `e₂` using `halfUniversal Q hQ P₂ h₂ _ hnT`. Establish `e₃` using `halfUniversal Q hQ (P₁ + P₂) h₃ _ hnT`. Establish `hsum : Point.map ι P₁ + (Point.map ι P₂ + -T) = Point.map ι (P₁ + P₂) + -T`. Rewrite using `[map_add, add_assoc]`.

Rewrite `e₁` using `[genEval_congr E hsum _ (hnT.add_left (P₁ + P₂)).isGenPt, e₃, e₂]`. Establish `key : Point.map (genEval E _ (isGenPt_map E ι h₃)) Q = Point.map (genEval E _ (isGenPt_map E ι h₁)) Q + Point.map (genEval E _ (isGenPt_map E ι h₂)) Q`. Use `congrArg (· - Point.map (genEval E (-T) hnT.isGenPt) Q) e₁` as an intermediate fact. Simplify using `only [add_sub_cancel_right] at this`. Rewrite using `[this]`.

Normalize the expressions using the abelian group laws. Rewrite `key` using `[map_genEval_map Q ι h₃, map_genEval_map Q ι h₁, map_genEval_map Q ι h₂, ← map_add]`. Conclude with `Point.map_injective ι key`.
-/
theorem respectsAdd_of_univAdd (hQ : UnivAdd Q) : RespectsAdd E E' Q := by
  rw [respectsAdd_iff]
  intro L _ _ _ P₁ P₂ h₁ h₂ h₃
  set M := (E.baseChange L).toAffine.FunctionField
  set ι := IsScalarTower.toAlgHom F L M
  set T : (E.baseChange M).toAffine.Point :=
    pointCongr (baseChange_baseChange E L M) (genericPoint (E.baseChange L))
  have hT : TransOver E L T := by
    simp only [T, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some]
    exact transcendental_genX _
  have hnT := hT.neg
  have hU := hnT.add_left P₂
  have e₁ := halfUniversal Q hQ P₁ h₁ _ hU
  have e₂ := halfUniversal Q hQ P₂ h₂ _ hnT
  have e₃ := halfUniversal Q hQ (P₁ + P₂) h₃ _ hnT
  have hsum : Point.map ι P₁ + (Point.map ι P₂ + -T) = Point.map ι (P₁ + P₂) + -T := by
    rw [map_add, add_assoc]
  rw [genEval_congr E hsum _ (hnT.add_left (P₁ + P₂)).isGenPt, e₃, e₂] at e₁
  have key : Point.map (genEval E _ (isGenPt_map E ι h₃)) Q =
      Point.map (genEval E _ (isGenPt_map E ι h₁)) Q +
        Point.map (genEval E _ (isGenPt_map E ι h₂)) Q := by
    have := congrArg (· - Point.map (genEval E (-T) hnT.isGenPt) Q) e₁
    simp only [add_sub_cancel_right] at this
    rw [this]
    abel
  rw [map_genEval_map Q ι h₃, map_genEval_map Q ι h₁, map_genEval_map Q ι h₂, ← map_add] at key
  exact Point.map_injective ι key

end Criterion

end

end GroundTheory.Global
