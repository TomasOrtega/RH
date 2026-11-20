import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.AnalyticAlgebraicIsogeny
import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenySeparable

open Filter Topology Set Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian KaehlerDifferential
open scoped PeriodPair

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

variable {L₁ L₂ : PeriodPair}

/- English proof (translation)
Use `set φ := isogOfHom Q hQ`. Establish `hsep : φ.IsSeparable`. Use `φ.finiteDimensional` as an intermediate fact. Conclude with `Algebra.IsSeparable.of_integral _ _`. Establish `h1` using `(isSeparable_iff_isogConst_ne_zero φ).1 hsep`.

Establish `h2 : isogConst φ = homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q`. Apply `(algebraMap ℂ (weierstrassCurve L₁).toAffine.FunctionField).injective` to reduce the goal to its premises. Rewrite using `[algebraMap_isogConst, algebraMap_homConst]`. Both sides reduce to the same expression. Rewrite using `[← h2]` and apply the resulting hypothesis.
-/
theorem homConst_ne_zero {Q : isogHom (weierstrassCurve L₁) (weierstrassCurve L₂)} (hQ : Q ≠ 0) :
    homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q ≠ 0 := by
  set φ := isogOfHom Q hQ
  have hsep : φ.IsSeparable := by
    have := φ.finiteDimensional
    exact Algebra.IsSeparable.of_integral _ _
  have h1 := (isSeparable_iff_isogConst_ne_zero φ).1 hsep
  have h2 : isogConst φ = homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q := by
    apply (algebraMap ℂ (weierstrassCurve L₁).toAffine.FunctionField).injective
    rw [algebraMap_isogConst, algebraMap_homConst]
    rfl
  rwa [← h2]

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `Q h`. Assume the negation of the conclusion as `hQ`. Conclude with `homConst_ne_zero hQ h`.
-/
theorem homConst_injective :
    Function.Injective (homConst (weierstrassCurve L₁) (weierstrassCurve L₂)) := by
  rw [injective_iff_map_eq_zero]
  intro Q h
  by_contra hQ
  exact homConst_ne_zero hQ h

/- English proof (translation)
Break down `P with _ | ⟨u, v, hP⟩` into its components or cases. Conclude with `⟨0, (map_zero _).symm⟩`. Take `⟨s₁, s₂⟩` from `omegaAt_some_spec W hP`. Establish `e₁` using `congrArg omegaDeriv s₁`. Establish `e₂` using `congrArg omegaDeriv s₂`.

Rewrite `e₁`, `e₂` using `[LinearMap.map_smul, h, smul_eq_mul, mul_zero, omegaDeriv_D, eq_comm]`. Take `⟨c, rfl⟩` from `exists_eq_algebraMap_of_germDeriv_eq_zero e₁`. Take `⟨d, rfl⟩` from `exists_eq_algebraMap_of_germDeriv_eq_zero e₂`. Establish `hcd : W.toAffine.Nonsingular c d` using `(W.toAffine.baseChange_nonsingular (f := Algebra.ofId ℂ MeroField) (algebraMap ℂ MeroField).injective c d).1 hP`. Conclude with `⟨.some c d hcd, rfl⟩`.
-/
theorem exists_eq_constMap_of_omegaDeriv {W : WeierstrassCurve ℂ}
    (P : (W.baseChange MeroField).toAffine.Point) (h : omegaDeriv (omegaAt W P) = 0) :
    ∃ R : W.toAffine.Point, P = constMap W MeroField R := by
  rcases P with _ | ⟨u, v, hP⟩
  · exact ⟨0, (map_zero _).symm⟩
  obtain ⟨s₁, s₂⟩ := omegaAt_some_spec W hP
  have e₁ := congrArg omegaDeriv s₁
  have e₂ := congrArg omegaDeriv s₂
  rw [LinearMap.map_smul, h, smul_eq_mul, mul_zero, omegaDeriv_D, eq_comm] at e₁ e₂
  obtain ⟨c, rfl⟩ := exists_eq_algebraMap_of_germDeriv_eq_zero e₁
  obtain ⟨d, rfl⟩ := exists_eq_algebraMap_of_germDeriv_eq_zero e₂
  have hcd : W.toAffine.Nonsingular c d :=
    (W.toAffine.baseChange_nonsingular (f := Algebra.ofId ℂ MeroField)
      (algebraMap ℂ MeroField).injective c d).1 hP
  exact ⟨.some c d hcd, rfl⟩

/- English proof (translation)
Use `set α := homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q`. Establish `h0 : α ≠ 0` using `homConst_ne_zero hQ`. Establish `e` using `omegaAt_eq_homConst_smul Q`. Establish `e'` using `congrArg (kpush (ellEval L₁)) e`. Rewrite `e'` using `[kpush_omegaAt, kpush_const_smul, invariantDifferential, kpush_omegaAt, map_ellEval_genericPoint, basePoint_eq]`.

Establish `hω : omegaDeriv (omegaAt (weierstrassCurve L₂) (Point.map (ellEval L₁) Q.1)) = algebraMap ℂ MeroField α`. Rewrite using `[e', ← algebraMap_smul MeroField, LinearMap.map_smul, omegaDeriv_affinePoint, smul_eq_mul, map_one, mul_one]`. Establish `hD : omegaDeriv (omegaAt (weierstrassCurve L₂) (Point.map (ellEval L₁) Q.1 - affinePoint L₂ α 0 h0)) = 0`. Establish `h1 : omegaAt (weierstrassCurve L₂) (Point.map (ellEval L₁) Q.1 - affinePoint L₂ α 0 h0) = omegaAt (weierstrassCurve L₂) (Point.map (ellEval L₁) Q.1) - omegaAt (weierstrassCurve L₂) (affinePoint L₂ α 0 h0)` using `map_sub (omegaHom (weierstrassCurve L₂)) _ _`. Rewrite using `[h1, map_sub, hω, omegaDeriv_affinePoint, sub_self]`.

Take `⟨R, hR⟩` from `exists_eq_constMap_of_omegaDeriv _ hD`. Take `⟨c, rfl⟩` from `toPoint_surjective (L := L₂) R`. Use `⟨0 + c, ?_⟩` and prove the remaining obligations. Rewrite using `[← affinePoint_add_constMap, ← hR]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_map_ellEval_eq {Q : isogHom (weierstrassCurve L₁) (weierstrassCurve L₂)}
    (hQ : Q ≠ 0) :
    ∃ c : ℂ, Point.map (ellEval L₁) Q.1 =
      affinePoint L₂ (homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q) c
        (homConst_ne_zero hQ) := by
  set α := homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q
  have h0 : α ≠ 0 := homConst_ne_zero hQ
  have e := omegaAt_eq_homConst_smul Q
  have e' := congrArg (kpush (ellEval L₁)) e
  rw [kpush_omegaAt, kpush_const_smul, invariantDifferential, kpush_omegaAt,
    map_ellEval_genericPoint, basePoint_eq] at e'
  have hω : omegaDeriv (omegaAt (weierstrassCurve L₂) (Point.map (ellEval L₁) Q.1)) =
      algebraMap ℂ MeroField α := by
    rw [e', ← algebraMap_smul MeroField, LinearMap.map_smul, omegaDeriv_affinePoint, smul_eq_mul,
      map_one, mul_one]
  have hD : omegaDeriv (omegaAt (weierstrassCurve L₂)
      (Point.map (ellEval L₁) Q.1 - affinePoint L₂ α 0 h0)) = 0 := by
    have h1 : omegaAt (weierstrassCurve L₂) (Point.map (ellEval L₁) Q.1 - affinePoint L₂ α 0 h0) =
        omegaAt (weierstrassCurve L₂) (Point.map (ellEval L₁) Q.1) -
          omegaAt (weierstrassCurve L₂) (affinePoint L₂ α 0 h0) :=
      map_sub (omegaHom (weierstrassCurve L₂)) _ _
    rw [h1, map_sub, hω, omegaDeriv_affinePoint, sub_self]
  obtain ⟨R, hR⟩ := exists_eq_constMap_of_omegaDeriv _ hD
  obtain ⟨c, rfl⟩ := toPoint_surjective (L := L₂) R
  refine ⟨0 + c, ?_⟩
  rw [← affinePoint_add_constMap, ← hR]
  abel

/- English proof (translation)
Distinguish the cases in `hQ : Q = 0`. Rewrite using `[hQ, map_zero]`. Conclude with `zero_mem _`. Use `set α := homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q`. Establish `h0 : α ≠ 0` using `homConst_ne_zero hQ`.

Take `⟨c, hc⟩` from `exists_map_ellEval_eq hQ`. Establish `hg : IsGenPt (weierstrassCurve L₂) Q.1` using `isGenPt_of_mem_isogHom Q.2 (fun h ↦ hQ (Subtype.ext h))`. Take `⟨hne, hQs⟩` from `eq_some_xOf_yOf _ (isGenPt_ne_zero _ hg)`. Rewrite `hc` using `[hQs, Point.map_some, affinePoint, Point.some.injEq]`. Take `⟨f, hf, hfe⟩` from `exists_isEllipticFunction_ellEval_eq L₁ (xOf _ Q.1)`.

Take `⟨g, hg', hge⟩` from `exists_isEllipticFunction_ellEval_eq L₁ (yOf _ Q.1)`. Rewrite `hc` using `[hfe, germ_eq_germ_iff hf.1 (meromorphic_weierstrassP_affine L₂ α c)]`. Rewrite `hc` using `[hge, germ_eq_germ_iff hg'.1 (meromorphic_derivWeierstrassP_half_affine L₂ α c)]`. Take `⟨hcx, hcy⟩` from `hc`. Introduce `l hl`.

Take `⟨z, h1, h2, h3, h4, h5, h6⟩` from `nonempty_of_mem_codiscrete (hcx.and (hcy.and ((eventually_affine hcx one_ne_zero l).and ((eventually_affine hcy one_ne_zero l).and ((eventually_affine (eventually_notMem_lattice L₂) h0 c).and (eventually_affine (eventually_notMem_lattice L₂) h0 (α * l + c)))))))`. Use `beta_reduce at h1 h2`. Simplify using `only [one_mul] at h3 h4`. Rewrite `h3` using `[hf.2 z l hl]`. Rewrite `h4` using `[hg'.2 z l hl]`.

Establish `e₁ : ℘[L₂] (α * z + (α * l + c)) = ℘[L₂] (α * z + c)`. Rewrite using `[← h1, h3, show α * (z + l) + c = α * z + (α * l + c) by ring]`. Establish `e₂ : ℘'[L₂] (α * z + (α * l + c)) = ℘'[L₂] (α * z + c)`. Use `h2.symm.trans h4` as an intermediate fact. Rewrite `this` using `[show α * (z + l) + c = α * z + (α * l + c) by ring]`.

Take the linear combination `2 * this.symm`. Establish `hpt : toPoint L₂ (α * z + (α * l + c)) = toPoint L₂ (α * z + c)`. Rewrite using `[toPoint_of_notMem h6, toPoint_of_notMem h5]`. Conclude with `point_some_congr e₁ (by rw [e₂])`. Use `torusToPoint_injective (L := L₂) (a₁ := Torus.mk L₂ _) (a₂ := Torus.mk L₂ _) hpt` as an intermediate fact.

Rewrite `this` using `[Torus.mk_eq_mk_iff]`. Simplify using `using this`.
-/
theorem homConst_mem_latticeHom (Q : isogHom (weierstrassCurve L₁) (weierstrassCurve L₂)) :
    homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q ∈ latticeHom L₁ L₂ := by
  by_cases hQ : Q = 0
  · rw [hQ, map_zero]
    exact zero_mem _
  set α := homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q
  have h0 : α ≠ 0 := homConst_ne_zero hQ
  obtain ⟨c, hc⟩ := exists_map_ellEval_eq hQ
  have hg : IsGenPt (weierstrassCurve L₂) Q.1 := isGenPt_of_mem_isogHom Q.2 (fun h ↦ hQ (Subtype.ext h))
  obtain ⟨hne, hQs⟩ := eq_some_xOf_yOf _ (isGenPt_ne_zero _ hg)
  rw [hQs, Point.map_some, affinePoint, Point.some.injEq] at hc
  obtain ⟨f, hf, hfe⟩ := exists_isEllipticFunction_ellEval_eq L₁ (xOf _ Q.1)
  obtain ⟨g, hg', hge⟩ := exists_isEllipticFunction_ellEval_eq L₁ (yOf _ Q.1)
  rw [hfe, germ_eq_germ_iff hf.1 (meromorphic_weierstrassP_affine L₂ α c)] at hc
  rw [hge, germ_eq_germ_iff hg'.1 (meromorphic_derivWeierstrassP_half_affine L₂ α c)] at hc
  obtain ⟨hcx, hcy⟩ := hc
  intro l hl
  obtain ⟨z, h1, h2, h3, h4, h5, h6⟩ := nonempty_of_mem_codiscrete (hcx.and (hcy.and
    ((eventually_affine hcx one_ne_zero l).and ((eventually_affine hcy one_ne_zero l).and
    ((eventually_affine (eventually_notMem_lattice L₂) h0 c).and
    (eventually_affine (eventually_notMem_lattice L₂) h0 (α * l + c)))))))
  beta_reduce at h1 h2
  simp only [one_mul] at h3 h4
  rw [hf.2 z l hl] at h3
  rw [hg'.2 z l hl] at h4
  have e₁ : ℘[L₂] (α * z + (α * l + c)) = ℘[L₂] (α * z + c) := by
    rw [← h1, h3, show α * (z + l) + c = α * z + (α * l + c) by ring]
  have e₂ : ℘'[L₂] (α * z + (α * l + c)) = ℘'[L₂] (α * z + c) := by
    have := h2.symm.trans h4
    rw [show α * (z + l) + c = α * z + (α * l + c) by ring] at this
    linear_combination 2 * this.symm
  have hpt : toPoint L₂ (α * z + (α * l + c)) = toPoint L₂ (α * z + c) := by
    rw [toPoint_of_notMem h6, toPoint_of_notMem h5]
    exact point_some_congr e₁ (by rw [e₂])
  have := torusToPoint_injective (L := L₂) (a₁ := Torus.mk L₂ _) (a₂ := Torus.mk L₂ _) hpt
  rw [Torus.mk_eq_mk_iff] at this
  simpa using this

/- English proof (translation)
The claim follows from `homConst_injective (by rw [homConst_latticeToHom])`.
-/
theorem latticeToHom_homConst (Q : isogHom (weierstrassCurve L₁) (weierstrassCurve L₂)) :
    latticeToHom ⟨_, homConst_mem_latticeHom Q⟩ = Q :=
  homConst_injective (by rw [homConst_latticeToHom])

/- English proof (translation)
The claim follows from `homConst_injective (by rw [map_add, homConst_latticeToHom, homConst_latticeToHom, homConst_latticeToHom] rfl)`.
-/
theorem latticeToHom_add (α β : latticeHom L₁ L₂) :
    latticeToHom (α + β) = latticeToHom α + latticeToHom β :=
  homConst_injective (by
    rw [map_add, homConst_latticeToHom, homConst_latticeToHom, homConst_latticeToHom]
    rfl)

/- English proof (translation)
Apply `algHom_eq_of_map_genericPoint' (E := weierstrassCurve L)` to reduce the goal to its premises. Rewrite using `[← Point.map_map, map_translate_genericPoint, map_add, map_ellEval_genericPoint, show constPoint (weierstrassCurve L) (toPoint L z) = constMap (weierstrassCurve L) _ (toPoint L z) from rfl, map_constMap, basePoint_eq, affinePoint_add_constMap, ← Point.map_map, map_ellEval_generic …`. Conclude with `affinePoint_congr L _ _ (by ring) (by ring)`.
-/
theorem ellEval_comp_translate (L : PeriodPair) (z : ℂ) :
    (ellEval L).comp (translate (weierstrassCurve L) (toPoint L z)) =
      (affineComp 1 z one_ne_zero).comp (ellEval L) := by
  apply algHom_eq_of_map_genericPoint' (E := weierstrassCurve L)
  rw [← Point.map_map, map_translate_genericPoint, map_add, map_ellEval_genericPoint,
    show constPoint (weierstrassCurve L) (toPoint L z) =
      constMap (weierstrassCurve L) _ (toPoint L z) from rfl, map_constMap, basePoint_eq,
    affinePoint_add_constMap, ← Point.map_map, map_ellEval_genericPoint, basePoint_eq,
    map_affineComp_affinePoint]
  exact affinePoint_congr L _ _ (by ring) (by ring)

/- English proof (translation)
Distinguish the cases in `h0 : (α : ℂ) = 0`. Rewrite using `[latticeToHom_of_eq_zero α h0, homPt_zero, AddMonoidHom.zero_apply, h0, zero_mul, toPoint_zero]`. Apply `homPt_eq_of` to reduce the goal to its premises. Apply `Point.map_injective (ellEval L₁)` to reduce the goal to its premises. Rewrite using `[Point.map_map, ellEval_comp_translate, ← Point.map_map, latticeToHom_of_ne_zero α h0, map_ellEval_isogPt, map_affineComp_affinePoint, map_add, map_ellEval_isogPt, map_constMap, affinePoint_add_constMap]`.

Conclude with `affinePoint_congr L₂ _ _ (by ring) (by ring)`.
-/
theorem homPt_latticeToHom (α : latticeHom L₁ L₂) (z : ℂ) :
    homPt (latticeToHom α) (toPoint L₁ z) = toPoint L₂ (α * z) := by
  by_cases h0 : (α : ℂ) = 0
  · rw [latticeToHom_of_eq_zero α h0, homPt_zero, AddMonoidHom.zero_apply, h0, zero_mul,
      toPoint_zero]
  apply homPt_eq_of
  apply Point.map_injective (ellEval L₁)
  rw [Point.map_map, ellEval_comp_translate, ← Point.map_map, latticeToHom_of_ne_zero α h0,
    map_ellEval_isogPt, map_affineComp_affinePoint, map_add, map_ellEval_isogPt, map_constMap,
    affinePoint_add_constMap]
  exact affinePoint_congr L₂ _ _ (by ring) (by ring)

section End

variable {L : PeriodPair}

/- English proof (translation)
Distinguish the cases in `hα : (α : ℂ) = 0`. Rewrite using `[latticeToHom_of_eq_zero α hα, zero_mul, latticeToHom_of_eq_zero _ (by simp [hα])]`. Distinguish the cases in `hβ : (β : ℂ) = 0`. Rewrite using `[latticeToHom_of_eq_zero β hβ, mul_zero, latticeToHom_of_eq_zero _ (by simp [hβ])]`. Establish `hg : IsGenPt (weierstrassCurve L) (latticeToHom β).1`.

Rewrite using `[latticeToHom_of_ne_zero β hβ]`. Conclude with `isGenPt_isogPt _ _`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Point.map_injective (ellEval L)` to reduce the goal to its premises. Establish `e : Point.map (ellEval L) (latticeToHom β).1 = affinePoint L β 0 hβ`.

Rewrite using `[latticeToHom_of_ne_zero β hβ, map_ellEval_isogPt]`. Rewrite using `[isogEnd_mul_def, homComp_of_isGenPt _ _ hg, Point.map_map, ← genEval_map _ (ellEval L) hg, genEval_congr _ e _ (isGenPt_affinePoint L β 0 hβ), genEval_affinePoint, ← Point.map_map, latticeToHom_of_ne_zero α hα, map_ellEval_isogPt, map_affineComp_affinePoint, latticeToHom_of_ne_z …`. Conclude with `affinePoint_congr L _ _ rfl (by ring)`.
-/
theorem latticeToHom_mul (α β : latticeHom L L) (h : (α : ℂ) * β ∈ latticeHom L L) :
    latticeToHom ⟨_, h⟩ = latticeToHom α * latticeToHom β := by
  by_cases hα : (α : ℂ) = 0
  · rw [latticeToHom_of_eq_zero α hα, zero_mul, latticeToHom_of_eq_zero _ (by simp [hα])]
  by_cases hβ : (β : ℂ) = 0
  · rw [latticeToHom_of_eq_zero β hβ, mul_zero, latticeToHom_of_eq_zero _ (by simp [hβ])]
  have hg : IsGenPt (weierstrassCurve L) (latticeToHom β).1 := by
    rw [latticeToHom_of_ne_zero β hβ]
    exact isGenPt_isogPt _ _
  apply Subtype.ext
  apply Point.map_injective (ellEval L)
  have e : Point.map (ellEval L) (latticeToHom β).1 = affinePoint L β 0 hβ := by
    rw [latticeToHom_of_ne_zero β hβ, map_ellEval_isogPt]
  rw [isogEnd_mul_def, homComp_of_isGenPt _ _ hg, Point.map_map, ← genEval_map _ (ellEval L) hg,
    genEval_congr _ e _ (isGenPt_affinePoint L β 0 hβ), genEval_affinePoint, ← Point.map_map,
    latticeToHom_of_ne_zero α hα, map_ellEval_isogPt, map_affineComp_affinePoint,
    latticeToHom_of_ne_zero _ (mul_ne_zero hα hβ), map_ellEval_isogPt]
  exact affinePoint_congr L _ _ rfl (by ring)

end End

end Elliptic
end GroundTheory.Global
