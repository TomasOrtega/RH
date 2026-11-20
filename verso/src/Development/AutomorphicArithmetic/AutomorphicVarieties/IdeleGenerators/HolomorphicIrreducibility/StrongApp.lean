import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import GroundTheory.AutomorphicForms.StrongApproximationSLDense

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix Topology

namespace UpperTheory.V.Sd

/- English proof (translation)
Use `ext`. Simplify using `[aff, Matrix.det_fin_two]`.
-/
private theorem det_aff {R : Type} [CommRing R] (y : Rˣ) (x : R) : GeneralLinearGroup.det (aff y x) = y := by
  ext
  simp [aff, Matrix.det_fin_two]

/- English proof (translation)
Establish `hc : Continuous (TR.infEq F).symm` using `continuous_pi fun w => (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp (continuous_apply w)`. Establish `hd : DenseRange ((TR.pInf F).comp (algebraMap F (Ad F)))` using `(TR.infEq F).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap F) hc`. Establish `ho : IsOpen {x : TR.Rinf F | ∀ v, 0 < x v * (d : TR.Rinf F) v}`. Rewrite using `[Set.setOf_forall]`. Conclude with `isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (by fun_prop)`.

Establish `hne : ∀ v, (d : TR.Rinf F) v ≠ 0` using `fun v h => by`. Use `congrFun d.mul_inv v` as an intermediate fact. Simplify using `[h] at this`. Take `⟨a, ha⟩` from `hd.exists_mem_open ho ⟨d, fun v => mul_self_pos.2 (hne v)⟩`. Use `⟨Units.mk0 a ?_, ha⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Take `⟨v⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Simplify using `using ha v`.
-/
private theorem exists_sign (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (d : (TR.Rinf F)ˣ) :
    ∃ a : Fˣ, ∀ v, 0 < ((TR.pInf F).comp (algebraMap F (Ad F)) (a : F)) v * (d : TR.Rinf F) v := by
  have hc : Continuous (TR.infEq F).symm :=
    continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp (continuous_apply w)
  have hd : DenseRange ((TR.pInf F).comp (algebraMap F (Ad F))) :=
    (TR.infEq F).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap F) hc
  have ho : IsOpen {x : TR.Rinf F | ∀ v, 0 < x v * (d : TR.Rinf F) v} := by
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (by fun_prop)
  have hne : ∀ v, (d : TR.Rinf F) v ≠ 0 := fun v h => by
    have := congrFun d.mul_inv v
    simp [h] at this
  obtain ⟨a, ha⟩ := hd.exists_mem_open ho ⟨d, fun v => mul_self_pos.2 (hne v)⟩
  refine ⟨Units.mk0 a ?_, ha⟩
  rintro rfl
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  simpa using ha v

/- English proof (translation)
Use `set y := GeneralLinearGroup.det g with hy`. Establish `hs : g * (aff y 0)⁻¹ ∈ GroundTheory.Automorphic.AdelicGLn.finiteSL F 2`. Rewrite using `[GroundTheory.Automorphic.AdelicGLn.mem_finiteSL, map_mul, map_inv, det_aff, hy, mul_inv_cancel]`. Establish `hcl` using `GroundTheory.Automorphic.AdelicGLn.finiteSL_le_topologicalClosure F 2 hs`. Rewrite `hcl` using `[← SetLike.mem_coe, Subgroup.topologicalClosure_coe]`.

Establish `ho : IsOpen {s : GL (Fin 2) (Af F) | (aff y 0)⁻¹ * s⁻¹ * g ∈ K}` using `hK.preimage (f := fun s : GL (Fin 2) (Af F) => (aff y 0)⁻¹ * s⁻¹ * g) ((continuous_const.mul continuous_inv).mul continuous_const)`. Take `⟨_, hu, σ, hσ, rfl⟩` from `mem_closure_iff.1 hcl _ ho (by`. Rewrite using `[Set.mem_setOf_eq, _root_.mul_inv_rev, inv_inv, inv_mul_cancel_left, inv_mul_cancel]`. Conclude with `one_mem K)`. Use `⟨σ, y, _, hu, hσ, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_assoc, mul_inv_cancel_left]`. Conclude with `(mul_inv_cancel_left _ g).symm`.
-/
private theorem exists_sl (F : Type) [Field F] [NumberField F] (K : Subgroup (GL (Fin 2) (Af F)))
    (hK : IsOpen (K : Set (GL (Fin 2) (Af F)))) (g : GL (Fin 2) (Af F)) :
    ∃ (σ : GL (Fin 2) F) (y : (Af F)ˣ) (u : GL (Fin 2) (Af F)), u ∈ K ∧ GeneralLinearGroup.det σ = 1 ∧
      g = GeneralLinearGroup.map (algebraMap F (Af F)) σ * (aff y 0 * u) := by
  set y := GeneralLinearGroup.det g with hy
  have hs : g * (aff y 0)⁻¹ ∈ GroundTheory.Automorphic.AdelicGLn.finiteSL F 2 := by
    rw [GroundTheory.Automorphic.AdelicGLn.mem_finiteSL, map_mul, map_inv, det_aff, hy, mul_inv_cancel]
  have hcl := GroundTheory.Automorphic.AdelicGLn.finiteSL_le_topologicalClosure F 2 hs
  rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at hcl
  have ho : IsOpen {s : GL (Fin 2) (Af F) | (aff y 0)⁻¹ * s⁻¹ * g ∈ K} :=
    hK.preimage (f := fun s : GL (Fin 2) (Af F) => (aff y 0)⁻¹ * s⁻¹ * g) ((continuous_const.mul continuous_inv).mul continuous_const)
  obtain ⟨_, hu, σ, hσ, rfl⟩ := mem_closure_iff.1 hcl _ ho (by
    rw [Set.mem_setOf_eq, _root_.mul_inv_rev, inv_inv, inv_mul_cancel_left, inv_mul_cancel]; exact one_mem K)
  refine ⟨σ, y, _, hu, hσ, ?_⟩
  rw [mul_assoc, mul_inv_cancel_left]
  exact (mul_inv_cancel_left _ g).symm

end UpperTheory.V.Sd

open UpperTheory.V UpperTheory.V.Sd in
/- English proof (translation)
Introduce `F _ _ _ K hK g`. Use `set j := (TR.pInf F).comp (algebraMap F (Ad F)) with hj`. Use `set gi := GeneralLinearGroup.map (TR.pInf F) g with hgi`. Take `⟨a, ha⟩` from `exists_sign F (GeneralLinearGroup.det gi)`. Take `⟨σ, y, u, hu, hσ, e⟩` from `exists_sl F K hK ((GeneralLinearGroup.map (algebraMap F (Af F)) (aff a 0))⁻¹ * GeneralLinearGroup.map (pFin F) g)`.

Establish `hγ : GeneralLinearGroup.det (aff a 0 * σ) = a` using `by rw [map_mul, det_aff, hσ, mul_one]`. Use `set h := (GeneralLinearGroup.map j (aff a 0 * σ))⁻¹ * gi with hh`. Establish `hh' : GeneralLinearGroup.map j (aff a 0 * σ) * h = gi` using `by rw [hh, mul_inv_cancel_left]`. Establish `e' : GeneralLinearGroup.map (algebraMap F (Af F)) (aff a 0 * σ) * (aff y 0 * u) = GeneralLinearGroup.map (pFin F) g`. Rewrite using `[inv_mul_eq_iff_eq_mul.1 e, map_mul, mul_assoc]`.

Generalize the expression as in `aff a 0 * σ = γ at *`. Use `⟨γ, h, y, u, hu, fun v => ?_, TR.ga_ext ?_ ?_⟩` and prove the remaining obligations. Establish `h1` using `ha v`. Rewrite `h1` using `[← hh', map_mul, Units.val_mul, GlobalTheory.CuspRep.det_map, hγ, Pi.mul_apply, ← hj, ← mul_assoc]`. Conclude with `(pos_iff_pos_of_mul_pos h1).1 (lt_of_le_of_ne (mul_self_nonneg _) fun h0 => by simp [← h0] at h1)`.

Rewrite using `[map_mul, map_mul, TR.pInf_infGL, TR.pInf_finGL, mul_one, ← hgi, ← hh']`. Both sides reduce to the same expression. Rewrite using `[map_mul, map_mul, TR.pFin_infGL, one_mul, ← e']`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.Sd.strongApp :
    UpperTheory.V.Sd.StrongApp := by
  intro F _ _ _ K hK g
  set j := (TR.pInf F).comp (algebraMap F (Ad F)) with hj
  set gi := GeneralLinearGroup.map (TR.pInf F) g with hgi
  obtain ⟨a, ha⟩ := exists_sign F (GeneralLinearGroup.det gi)
  obtain ⟨σ, y, u, hu, hσ, e⟩ := exists_sl F K hK
    ((GeneralLinearGroup.map (algebraMap F (Af F)) (aff a 0))⁻¹ * GeneralLinearGroup.map (pFin F) g)
  have hγ : GeneralLinearGroup.det (aff a 0 * σ) = a := by rw [map_mul, det_aff, hσ, mul_one]
  set h := (GeneralLinearGroup.map j (aff a 0 * σ))⁻¹ * gi with hh
  have hh' : GeneralLinearGroup.map j (aff a 0 * σ) * h = gi := by rw [hh, mul_inv_cancel_left]
  have e' : GeneralLinearGroup.map (algebraMap F (Af F)) (aff a 0 * σ) * (aff y 0 * u) =
      GeneralLinearGroup.map (pFin F) g := by
    rw [inv_mul_eq_iff_eq_mul.1 e, map_mul, mul_assoc]
  generalize aff a 0 * σ = γ at *
  refine ⟨γ, h, y, u, hu, fun v => ?_, TR.ga_ext ?_ ?_⟩
  · have h1 := ha v
    rw [← hh', map_mul, Units.val_mul, GlobalTheory.CuspRep.det_map, hγ, Pi.mul_apply, ← hj, ← mul_assoc] at h1
    exact (pos_iff_pos_of_mul_pos h1).1 (lt_of_le_of_ne (mul_self_nonneg _) fun h0 => by simp [← h0] at h1)
  · rw [map_mul, map_mul, TR.pInf_infGL, TR.pInf_finGL, mul_one, ← hgi, ← hh']
    rfl
  · rw [map_mul, map_mul, TR.pFin_infGL, one_mul, ← e']
    congr 1
    simp
