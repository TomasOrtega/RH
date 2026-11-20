import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.RespectsAddUniversal

open Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian

noncomputable section

namespace GroundTheory.Global

universe u

variable {F : Type u} [Field F] {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

omit [E.IsElliptic] in

/- English proof (translation)
Set `_ : Algebra E.toAffine.FunctionField M` to `σ.toRingHom.toAlgebra`. Establish `hc : ∀ a : F, algebraMap E.toAffine.FunctionField M (algebraMap F E.toAffine.FunctionField a) = algebraMap F M a` using `fun a ↦ σ.commutes a`. Establish `hEq : ((E.baseChange E.toAffine.FunctionField).baseChange M).toAffine.Equation u v`. Establish `e` using `(equation_iff _ _).1 h.1`. Rewrite using `[equation_iff]`.

Simplify using `only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e ⊢`. Rewrite using `[hc, hc, hc, hc, hc]`. Conclude with `e`. Establish `htr : Transcendental E.toAffine.FunctionField u`. Introduce and unpack `⟨p, hp0, hp⟩`.

Apply `hu p hp0` to reduce the goal to its premises. Rewrite using `[eval_map]`. Conclude with `hp`. Set `τ` to `liftPoint (E.baseChange E.toAffine.FunctionField) hEq htr`. Establish `_ : IsScalarTower F E.toAffine.FunctionField M` using `IsScalarTower.of_algebraMap_eq fun c ↦ (σ.commutes c).symm`.

Use `⟨τ.restrictScalars F, AlgHom.ext fun a ↦ ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[AlgHom.comp_apply, AlgHom.restrictScalars_apply, IsScalarTower.coe_toAlgHom']`. Conclude with `τ.commutes a`. Rewrite using `[AlgHom.restrictScalars_apply]`. Conclude with `liftPoint_genX _ _ _`.

Rewrite using `[AlgHom.restrictScalars_apply]`. Conclude with `liftPoint_genY _ _ _`.
-/
theorem exists_univField_algHom {M : Type*} [Field M] [Algebra F M] [DecidableEq M]
    (σ : E.toAffine.FunctionField →ₐ[F] M) {u v : M}
    (h : (E.baseChange M).toAffine.Nonsingular u v)
    (hu : ∀ p : E.toAffine.FunctionField[X], p ≠ 0 → (p.map σ.toRingHom).eval u ≠ 0) :
    ∃ τ : univField E →ₐ[F] M,
      τ.comp (IsScalarTower.toAlgHom F E.toAffine.FunctionField (univField E)) = σ ∧
        τ (genX (E.baseChange E.toAffine.FunctionField)) = u ∧
          τ (genY (E.baseChange E.toAffine.FunctionField)) = v := by
  let _ : Algebra E.toAffine.FunctionField M := σ.toRingHom.toAlgebra
  have hc : ∀ a : F, algebraMap E.toAffine.FunctionField M (algebraMap F E.toAffine.FunctionField a) =
      algebraMap F M a := fun a ↦ σ.commutes a
  have hEq : ((E.baseChange E.toAffine.FunctionField).baseChange M).toAffine.Equation u v := by
    have e := (equation_iff _ _).1 h.1
    rw [equation_iff]
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e ⊢
    rw [hc, hc, hc, hc, hc]
    exact e
  have htr : Transcendental E.toAffine.FunctionField u := by
    rintro ⟨p, hp0, hp⟩
    apply hu p hp0
    rw [eval_map]
    exact hp
  let τ := liftPoint (E.baseChange E.toAffine.FunctionField) hEq htr
  have _ : IsScalarTower F E.toAffine.FunctionField M :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (σ.commutes c).symm
  refine ⟨τ.restrictScalars F, AlgHom.ext fun a ↦ ?_, ?_, ?_⟩
  · rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply, IsScalarTower.coe_toAlgHom']
    exact τ.commutes a
  · rw [AlgHom.restrictScalars_apply]
    exact liftPoint_genX _ _ _
  · rw [AlgHom.restrictScalars_apply]
    exact liftPoint_genY _ _ _

/- English proof (translation)
Take `⟨τ, hτ, hu', hv'⟩` from `exists_univField_algHom σ h hu`. Establish `c₁ : Point.map τ (univPt₁ E) = Point.map σ (genericPoint E)`. Rewrite using `[univPt₁, Point.map_map, hτ]`. Establish `c₂ : Point.map τ (univPt₂ E) = Point.some u v h`. Rewrite using `[univPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some, Point.map_some, Point.some.injEq]`.

Conclude with `⟨hu', hv'⟩`. Apply `Point.map_injective τ` to reduce the goal to its premises. Rewrite using `[map_add, ← map_genEval_map Q τ _ (isGenPt_map E τ (isGenPt_univPt₁₂ E)), ← map_genEval_map Q τ _ (isGenPt_map E τ (isGenPt_univPt₁ E)), ← map_genEval_map Q τ _ (isGenPt_map E τ (isGenPt_univPt₂ E)), genEval_congr E (by rw [map_add, c₁, c₂]) _ hAB, genEval_congr E c₁ _ hA, genEva …`. Conclude with `hQ`.
-/
theorem univAdd_of_pair (Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point)
    {M : Type*} [Field M] [Algebra F M] [DecidableEq M] (σ : E.toAffine.FunctionField →ₐ[F] M)
    {u v : M} (h : (E.baseChange M).toAffine.Nonsingular u v)
    (hu : ∀ p : E.toAffine.FunctionField[X], p ≠ 0 → (p.map σ.toRingHom).eval u ≠ 0)
    (hA : IsGenPt E (Point.map σ (genericPoint E))) (hB : IsGenPt E (Point.some u v h))
    (hAB : IsGenPt E (Point.map σ (genericPoint E) + Point.some u v h))
    (hQ : Point.map (genEval E _ hAB) Q =
      Point.map (genEval E _ hA) Q + Point.map (genEval E _ hB) Q) : UnivAdd Q := by
  obtain ⟨τ, hτ, hu', hv'⟩ := exists_univField_algHom σ h hu
  have c₁ : Point.map τ (univPt₁ E) = Point.map σ (genericPoint E) := by
    rw [univPt₁, Point.map_map, hτ]
  have c₂ : Point.map τ (univPt₂ E) = Point.some u v h := by
    rw [univPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some, Point.map_some, Point.some.injEq]
    exact ⟨hu', hv'⟩
  apply Point.map_injective τ
  rw [map_add, ← map_genEval_map Q τ _ (isGenPt_map E τ (isGenPt_univPt₁₂ E)),
    ← map_genEval_map Q τ _ (isGenPt_map E τ (isGenPt_univPt₁ E)),
    ← map_genEval_map Q τ _ (isGenPt_map E τ (isGenPt_univPt₂ E)),
    genEval_congr E (by rw [map_add, c₁, c₂]) _ hAB, genEval_congr E c₁ _ hA,
    genEval_congr E c₂ _ hB]
  exact hQ

end GroundTheory.Global
