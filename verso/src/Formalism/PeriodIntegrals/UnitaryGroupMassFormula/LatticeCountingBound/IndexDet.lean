import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.IndexDefs

noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

namespace DetIdxW

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

def ιc (K : Type) [Field K] [NumberField K] (k : ℕ) : (Fin k → 𝓞 K) →+ (Fin k → K) :=
  (LinearMap.compLeft (Algebra.linearMap (𝓞 K) K) (Fin k)).toAddMonoidHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma ιc_apply (t : Fin k → 𝓞 K) (i : Fin k) : ιc K k t i = algebraMap (𝓞 K) K (t i) := rfl

/- English proof (translation)
Introduce `x y h` and use `funext fun c => IsFractionRing.injective (𝓞 K) K (by have := congrFun h c; rwa [ιc_apply, ιc_apply] at this)`.
-/
lemma ιc_inj : Function.Injective (ιc K k) := fun x y h => funext fun c =>
  IsFractionRing.injective (𝓞 K) K (by have := congrFun h c; rwa [ιc_apply, ιc_apply] at this)

/- English proof (translation)
Use extensionality with `x`. Simplify using `[oLat, ιc, AddSubgroup.mem_map, LinearMap.mem_range]`.
-/
lemma oLat_eq : (oLat K k).toAddSubgroup = (⊤ : AddSubgroup (Fin k → 𝓞 K)).map (ιc K k) := by
  ext x
  simp [oLat, ιc, AddSubgroup.mem_map, LinearMap.mem_range]

def vm (M : Matrix (Fin k) (Fin k) K) : (Fin k → K) →+ (Fin k → K) where
  toFun s := s ᵥ* M
  map_zero' := Matrix.zero_vecMul M
  map_add' a b := by simp [Matrix.add_vecMul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma vm_apply (M : Matrix (Fin k) (Fin k) K) (s : Fin k → K) : vm M s = s ᵥ* M := rfl

/- English proof (translation)
Establish `hGinj : Function.Injective γᵀ.mulVecLin`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `t ht`. Assume the negation of the conclusion as `hne`. Conclude with `hγ (Matrix.det_transpose γ ▸ Matrix.exists_mulVec_eq_zero_iff.1 ⟨t, hne, ht⟩)`.

Set `Gz : (Fin k → 𝓞 K) →ₗ[ℤ] (Fin k → 𝓞 K)` to `γᵀ.mulVecLin.restrictScalars ℤ`. Establish `hGz : Function.Injective Gz` using `hGinj`. Set `e` to `LinearEquiv.ofInjective Gz hGz`. Establish `hcard` using `Submodule.natAbs_det_equiv (LinearMap.range Gz) e`. Establish `hcomp : (LinearMap.range Gz).subtype ∘ₗ (e : (Fin k → 𝓞 K) →+ LinearMap.range Gz).toIntLinearMap = Gz`.

Use extensionality with `x`. Both sides reduce to the same expression. Establish `hdetG : LinearMap.det γᵀ.mulVecLin = γ.det`. Rewrite using `[← Matrix.det_transpose γ]`. Conclude with `LinearMap.det_toLin' γᵀ`.

Rewrite `hcard` using `[hcomp, LinearMap.det_restrictScalars, hdetG]`. Establish `hcomm : (vm (γ.map (algebraMap (𝓞 K) K))).comp (ιc K k) = (ιc K k).comp Gz.toAddMonoidHom`. Use `AddMonoidHom.ext fun t => funext fun j => ?_` and prove the remaining obligations. Simplify using `only [AddMonoidHom.comp_apply, vm_apply, ιc_apply, LinearMap.toAddMonoidHom_coe]`. Simplify using `[Gz, Matrix.vecMul, dotProduct, ιc_apply, map_sum, map_mul, mul_comm]`.

Establish `hr : (⊤ : AddSubgroup (Fin k → 𝓞 K)).map Gz.toAddMonoidHom = (LinearMap.range Gz).toAddSubgroup`. Use extensionality with `x`. Simplify using `[LinearMap.mem_range]`. Rewrite using `[oLat_eq, AddSubgroup.map_map, hcomm, ← AddSubgroup.map_map, AddSubgroup.relIndex_map_map_of_injective _ _ ιc_inj, AddSubgroup.relIndex_top_right, hr, hcard, AddSubgroup.index_eq_card]`. Both sides reduce to the same expression.
-/
lemma idx_int (γ : Matrix (Fin k) (Fin k) (𝓞 K)) (hγ : γ.det ≠ 0) :
    ((oLat K k).toAddSubgroup.map (vm (γ.map (algebraMap (𝓞 K) K)))).relIndex (oLat K k).toAddSubgroup =
      (Algebra.norm ℤ γ.det).natAbs := by
  classical
  have hGinj : Function.Injective γᵀ.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    by_contra hne
    exact hγ (Matrix.det_transpose γ ▸ Matrix.exists_mulVec_eq_zero_iff.1 ⟨t, hne, ht⟩)
  let Gz : (Fin k → 𝓞 K) →ₗ[ℤ] (Fin k → 𝓞 K) := γᵀ.mulVecLin.restrictScalars ℤ
  have hGz : Function.Injective Gz := hGinj
  let e := LinearEquiv.ofInjective Gz hGz
  have hcard := Submodule.natAbs_det_equiv (LinearMap.range Gz) e
  have hcomp : (LinearMap.range Gz).subtype ∘ₗ
      (e : (Fin k → 𝓞 K) →+ LinearMap.range Gz).toIntLinearMap = Gz := by
    ext x
    rfl
  have hdetG : LinearMap.det γᵀ.mulVecLin = γ.det := by
    rw [← Matrix.det_transpose γ]
    exact LinearMap.det_toLin' γᵀ
  rw [hcomp, LinearMap.det_restrictScalars, hdetG] at hcard
  have hcomm : (vm (γ.map (algebraMap (𝓞 K) K))).comp (ιc K k) = (ιc K k).comp Gz.toAddMonoidHom := by
    refine AddMonoidHom.ext fun t => funext fun j => ?_
    simp only [AddMonoidHom.comp_apply, vm_apply, ιc_apply, LinearMap.toAddMonoidHom_coe]
    simp [Gz, Matrix.vecMul, dotProduct, ιc_apply, map_sum, map_mul, mul_comm]
  have hr : (⊤ : AddSubgroup (Fin k → 𝓞 K)).map Gz.toAddMonoidHom = (LinearMap.range Gz).toAddSubgroup := by
    ext x
    simp [LinearMap.mem_range]
  rw [oLat_eq, AddSubgroup.map_map, hcomm, ← AddSubgroup.map_map,
    AddSubgroup.relIndex_map_map_of_injective _ _ ιc_inj, AddSubgroup.relIndex_top_right, hr, hcard,
    AddSubgroup.index_eq_card]
  rfl

/- English proof (translation)
Establish `h1 : ((Algebra.norm ℤ x : ℤ) : ℚ) = Algebra.norm ℚ (algebraMap (𝓞 K) K x)` using `Algebra.coe_norm_int x`. Rewrite using `[Nat.cast_natAbs, Int.cast_abs, ← h1, Rat.cast_intCast]`.
-/
lemma natAbs_norm_real (x : 𝓞 K) :
    ((Algebra.norm ℤ x).natAbs : ℝ) = |((Algebra.norm ℚ (algebraMap (𝓞 K) K x) : ℚ) : ℝ)| := by
  have h1 : ((Algebra.norm ℤ x : ℤ) : ℚ) = Algebra.norm ℚ (algebraMap (𝓞 K) K x) := Algebra.coe_norm_int x
  rw [Nat.cast_natAbs, Int.cast_abs, ← h1, Rat.cast_intCast]

/- English proof (translation)
Establish `hu : IsUnit N.det` using `isUnit_iff_ne_zero.mpr hN`. Use `congrArg (fun v => v ᵥ* N⁻¹) h` as an intermediate fact. Simplify `this` using `only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one]`.
-/
lemma vecMul_inj (N : Matrix (Fin k) (Fin k) K) (hN : N.det ≠ 0) {s s' : Fin k → K}
    (h : s ᵥ* N = s' ᵥ* N) : s = s' := by
  have hu : IsUnit N.det := isUnit_iff_ne_zero.mpr hN
  have := congrArg (fun v => v ᵥ* N⁻¹) h
  simpa only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one] using this

end DetIdxW

open DetIdxW in
/- English proof (translation)
Introduce `K _ _ k N Q D hOQ hOQ0 hDO hDO0 hDQ`. Distinguish the cases in `hN : N.det = 0`. Rewrite using `[hN, Algebra.norm_zero, Rat.cast_zero, abs_zero]`. Check the signs of the components of the expression. Use `set O := (oLat K k).toAddSubgroup with hOdef`.

Take `⟨⟨d, hd⟩, hdT⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K)) (Finset.univ.image fun p : Fin k × Fin k => N p.1 p.2)`. Establish `hd0 : d ≠ 0` using `nonZeroDivisors.ne_zero hd`. Use `set dK := algebraMap (𝓞 K) K d with hdKdef`. Establish `hdK : dK ≠ 0`. Rewrite using `[hdKdef, Ne, ← map_zero (algebraMap (𝓞 K) K)]`.

Conclude with `fun h => hd0 (IsFractionRing.injective (𝓞 K) K h)`. Establish `hG : ∀ i j, ∃ x : 𝓞 K, algebraMap (𝓞 K) K x = dK * N i j`. Introduce `i j`. Take `⟨x, hx⟩` from `hdT (N i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)`. Conclude with `⟨x, by rw [hx, Algebra.smul_def]⟩`.

Use `choose G hGe using hG`. Set `Gm : Matrix (Fin k) (Fin k) (𝓞 K)` to `Matrix.of G`. Establish `hGmap : Gm.map (algebraMap (𝓞 K) K) = dK • N`. Use extensionality with `i j`. Simplify using `[Gm, hGe]`.

Establish `hdetG : algebraMap (𝓞 K) K Gm.det = dK ^ k * N.det`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, hGmap, Matrix.det_smul, Fintype.card_fin]`. Establish `hGdet0 : Gm.det ≠ 0`. Introduce `h`. Establish `h2` using `hdetG`.

Rewrite `h2` using `[h, map_zero]`. Conclude with `(mul_ne_zero (pow_ne_zero _ hdK) hN) h2.symm`. Set `Dm : Matrix (Fin k) (Fin k) (𝓞 K)` to `d • (1 : Matrix (Fin k) (Fin k) (𝓞 K))`. Establish `hDmap : Dm.map (algebraMap (𝓞 K) K) = dK • (1 : Matrix (Fin k) (Fin k) K)`. Use extensionality with `i j`.

Apply the tactic sequence `by_cases h : i = j <;> simp [Dm, h, hdKdef]`. Establish `hDdet : Dm.det = d ^ k` using `by simp [Dm]`. Establish `hDdet0 : Dm.det ≠ 0` using `by rw [hDdet]; exact pow_ne_zero _ hd0`. Use `set T := vm (Gm.map (algebraMap (𝓞 K) K)) with hTdef`. Use `set S := vm (Dm.map (algebraMap (𝓞 K) K)) with hSdef`.

Establish `hT : ∀ s, T s = dK • (s ᵥ* N)`. Introduce `s`. Rewrite using `[hTdef, vm_apply, hGmap, Matrix.vecMul_smul]`. Establish `hS : ∀ s, S s = dK • s`. Introduce `s`.

Rewrite using `[hSdef, vm_apply, hDmap, Matrix.vecMul_smul, Matrix.vecMul_one]`. Establish `hTinj : Function.Injective T`. Introduce `s s' h`. Rewrite `h` using `[hT, hT]`. Conclude with `vecMul_inj N hN (smul_right_injective _ hdK h)`.

Establish `hSinj : Function.Injective S`. Introduce `s s' h`. Rewrite `h` using `[hS, hS]`. Conclude with `smul_right_injective _ hdK h`. Use `set X := O.map T with hX`.

Use `set Y := Q.map T with hY`. Use `set Z := D.map S with hZ`. Use `set dO := O.map S with hdO`. Establish `hXO : X.relIndex O = (Algebra.norm ℤ Gm.det).natAbs` using `idx_int Gm hGdet0`. Establish `hdOO : dO.relIndex O = (Algebra.norm ℤ Dm.det).natAbs` using `idx_int Dm hDdet0`.

Establish `hXY : X.relIndex Y = O.relIndex Q` using `AddSubgroup.relIndex_map_map_of_injective _ _ hTinj`. Establish `hZdO : Z.relIndex dO = D.relIndex O` using `AddSubgroup.relIndex_map_map_of_injective _ _ hSinj`. Establish `hZle_dO : Z ≤ dO` using `AddSubgroup.map_mono hDO`. Establish `hdO_le : dO ≤ O`. Introduce and unpack `_ ⟨s, hs, rfl⟩`.

Rewrite using `[hS]`. Use `(oLat K k).smul_mem d hs` as an intermediate fact. Rewrite `this` using `[← algebraMap_smul K d s]`. Then use the resulting hypothesis. Establish `hZO_le : Z ≤ O` using `hZle_dO.trans hdO_le`. Establish `hZY : Z ≤ Y`.

Introduce and unpack `_ ⟨r, hr, rfl⟩`. Take `⟨s, hs, hsr⟩` from `hDQ r hr`. Conclude with `⟨s, hs, by rw [hT, hS, hsr]⟩`. Establish `hZO : Z.relIndex O = D.relIndex O * (Algebra.norm ℤ Dm.det).natAbs`. Rewrite using `[← AddSubgroup.relIndex_mul_relIndex (hHK := hZle_dO) (hKL := hdO_le), hZdO, hdOO]`.

Establish `hXY0 : X.relIndex Y ≠ 0` using `hXY ▸ hOQ0`. Establish `hXZ0 : X.relIndex Z ≠ 0` using `mt (AddSubgroup.relIndex_eq_zero_of_le_right (hKL := hZY)) hXY0`. Establish `hZO0 : Z.relIndex O ≠ 0`. Rewrite using `[hZO]`. Conclude with `mul_ne_zero hDO0 (Int.natAbs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hDdet0))`.

Establish `hmul : (X ⊓ Z).relIndex O = X.relIndex Z * Z.relIndex O`. Rewrite using `[← AddSubgroup.relIndex_mul_relIndex (hHK := (inf_le_right : X ⊓ Z ≤ Z)) (hKL := hZO_le), AddSubgroup.inf_relIndex_right]`. Establish `h1 : X.relIndex O ≤ (X ⊓ Z).relIndex O` using `AddSubgroup.relIndex_le_of_le_left (hHK := (inf_le_left : X ⊓ Z ≤ X)) (hHL := by rw [hmul]; exact mul_ne_zero hXZ0 hZO0)`. Establish `h2 : X.relIndex Z ≤ X.relIndex Y` using `AddSubgroup.relIndex_le_of_le_right (hKL := hZY) (hHL := hXY0)`. Establish `key : X.relIndex O ≤ X.relIndex Y * Z.relIndex O`.

Rewrite `h1` using `[hmul]`. Conclude with `h1.trans (Nat.mul_le_mul_right _ h2)`. Rewrite `key` using `[hXO, hXY, hZO]`. Establish `keyR : ((Algebra.norm ℤ Gm.det).natAbs : ℝ) ≤ (O.relIndex Q : ℝ) * ((D.relIndex O : ℝ) * ((Algebra.norm ℤ Dm.det).natAbs : ℝ))`. Conclude with `key` after adjusting the coercions.

Rewrite `keyR` using `[natAbs_norm_real, natAbs_norm_real, hdetG, hDdet, map_pow, map_mul, map_pow]`. Simplify using `only [Rat.cast_mul, Rat.cast_pow, abs_mul, abs_pow] at keyR`. Establish `ha : 0 < |((Algebra.norm ℚ dK : ℚ) : ℝ)| ^ k`. Apply `pow_pos` to reduce the goal to its premises. Rewrite using `[abs_pos, Rat.cast_ne_zero]`.

Conclude with `Algebra.norm_ne_zero_iff.mpr hdK`. Establish `: |((Algebra.norm ℚ dK : ℚ) : ℝ)| ^ k * |((Algebra.norm ℚ N.det : ℚ) : ℝ)| ≤ |((Algebra.norm ℚ dK : ℚ) : ℝ)| ^ k * ((O.relIndex Q : ℝ) * (D.relIndex O : ℝ))`. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_of_mul_le_mul_left this ha`.
-/
theorem determinant_index_formula : DetIdx := by
  intro K _ _ k N Q D hOQ hOQ0 hDO hDO0 hDQ
  classical
  by_cases hN : N.det = 0
  · rw [hN, Algebra.norm_zero, Rat.cast_zero, abs_zero]
    positivity
  set O := (oLat K k).toAddSubgroup with hOdef

  obtain ⟨⟨d, hd⟩, hdT⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (Finset.univ.image fun p : Fin k × Fin k => N p.1 p.2)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  set dK := algebraMap (𝓞 K) K d with hdKdef
  have hdK : dK ≠ 0 := by
    rw [hdKdef, Ne, ← map_zero (algebraMap (𝓞 K) K)]
    exact fun h => hd0 (IsFractionRing.injective (𝓞 K) K h)
  have hG : ∀ i j, ∃ x : 𝓞 K, algebraMap (𝓞 K) K x = dK * N i j := by
    intro i j
    obtain ⟨x, hx⟩ := hdT (N i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
    exact ⟨x, by rw [hx, Algebra.smul_def]⟩
  choose G hGe using hG
  let Gm : Matrix (Fin k) (Fin k) (𝓞 K) := Matrix.of G
  have hGmap : Gm.map (algebraMap (𝓞 K) K) = dK • N := by
    ext i j
    simp [Gm, hGe]
  have hdetG : algebraMap (𝓞 K) K Gm.det = dK ^ k * N.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hGmap, Matrix.det_smul, Fintype.card_fin]
  have hGdet0 : Gm.det ≠ 0 := by
    intro h
    have h2 := hdetG
    rw [h, map_zero] at h2
    exact (mul_ne_zero (pow_ne_zero _ hdK) hN) h2.symm
  let Dm : Matrix (Fin k) (Fin k) (𝓞 K) := d • (1 : Matrix (Fin k) (Fin k) (𝓞 K))
  have hDmap : Dm.map (algebraMap (𝓞 K) K) = dK • (1 : Matrix (Fin k) (Fin k) K) := by
    ext i j
    by_cases h : i = j <;> simp [Dm, h, hdKdef]
  have hDdet : Dm.det = d ^ k := by simp [Dm]
  have hDdet0 : Dm.det ≠ 0 := by rw [hDdet]; exact pow_ne_zero _ hd0
  set T := vm (Gm.map (algebraMap (𝓞 K) K)) with hTdef
  set S := vm (Dm.map (algebraMap (𝓞 K) K)) with hSdef
  have hT : ∀ s, T s = dK • (s ᵥ* N) := by
    intro s; rw [hTdef, vm_apply, hGmap, Matrix.vecMul_smul]
  have hS : ∀ s, S s = dK • s := by
    intro s; rw [hSdef, vm_apply, hDmap, Matrix.vecMul_smul, Matrix.vecMul_one]
  have hTinj : Function.Injective T := by
    intro s s' h
    rw [hT, hT] at h
    exact vecMul_inj N hN (smul_right_injective _ hdK h)
  have hSinj : Function.Injective S := by
    intro s s' h
    rw [hS, hS] at h
    exact smul_right_injective _ hdK h
  set X := O.map T with hX
  set Y := Q.map T with hY
  set Z := D.map S with hZ
  set dO := O.map S with hdO
  have hXO : X.relIndex O = (Algebra.norm ℤ Gm.det).natAbs := idx_int Gm hGdet0
  have hdOO : dO.relIndex O = (Algebra.norm ℤ Dm.det).natAbs := idx_int Dm hDdet0
  have hXY : X.relIndex Y = O.relIndex Q := AddSubgroup.relIndex_map_map_of_injective _ _ hTinj
  have hZdO : Z.relIndex dO = D.relIndex O := AddSubgroup.relIndex_map_map_of_injective _ _ hSinj
  have hZle_dO : Z ≤ dO := AddSubgroup.map_mono hDO
  have hdO_le : dO ≤ O := by
    rintro _ ⟨s, hs, rfl⟩
    rw [hS]
    have := (oLat K k).smul_mem d hs
    rwa [← algebraMap_smul K d s] at this
  have hZO_le : Z ≤ O := hZle_dO.trans hdO_le
  have hZY : Z ≤ Y := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨s, hs, hsr⟩ := hDQ r hr
    exact ⟨s, hs, by rw [hT, hS, hsr]⟩
  have hZO : Z.relIndex O = D.relIndex O * (Algebra.norm ℤ Dm.det).natAbs := by
    rw [← AddSubgroup.relIndex_mul_relIndex (hHK := hZle_dO) (hKL := hdO_le), hZdO, hdOO]
  have hXY0 : X.relIndex Y ≠ 0 := hXY ▸ hOQ0
  have hXZ0 : X.relIndex Z ≠ 0 := mt (AddSubgroup.relIndex_eq_zero_of_le_right (hKL := hZY)) hXY0
  have hZO0 : Z.relIndex O ≠ 0 := by
    rw [hZO]
    exact mul_ne_zero hDO0 (Int.natAbs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hDdet0))
  have hmul : (X ⊓ Z).relIndex O = X.relIndex Z * Z.relIndex O := by
    rw [← AddSubgroup.relIndex_mul_relIndex (hHK := (inf_le_right : X ⊓ Z ≤ Z)) (hKL := hZO_le),
      AddSubgroup.inf_relIndex_right]
  have h1 : X.relIndex O ≤ (X ⊓ Z).relIndex O :=
    AddSubgroup.relIndex_le_of_le_left (hHK := (inf_le_left : X ⊓ Z ≤ X)) (hHL := by rw [hmul]; exact mul_ne_zero hXZ0 hZO0)
  have h2 : X.relIndex Z ≤ X.relIndex Y := AddSubgroup.relIndex_le_of_le_right (hKL := hZY) (hHL := hXY0)
  have key : X.relIndex O ≤ X.relIndex Y * Z.relIndex O := by
    rw [hmul] at h1
    exact h1.trans (Nat.mul_le_mul_right _ h2)
  rw [hXO, hXY, hZO] at key
  have keyR : ((Algebra.norm ℤ Gm.det).natAbs : ℝ) ≤
      (O.relIndex Q : ℝ) * ((D.relIndex O : ℝ) * ((Algebra.norm ℤ Dm.det).natAbs : ℝ)) := by
    exact_mod_cast key
  rw [natAbs_norm_real, natAbs_norm_real, hdetG, hDdet, map_pow, map_mul, map_pow] at keyR
  simp only [Rat.cast_mul, Rat.cast_pow, abs_mul, abs_pow] at keyR
  have ha : 0 < |((Algebra.norm ℚ dK : ℚ) : ℝ)| ^ k := by
    apply pow_pos
    rw [abs_pos, Rat.cast_ne_zero]
    exact Algebra.norm_ne_zero_iff.mpr hdK
  have : |((Algebra.norm ℚ dK : ℚ) : ℝ)| ^ k * |((Algebra.norm ℚ N.det : ℚ) : ℝ)| ≤
      |((Algebra.norm ℚ dK : ℚ) : ℝ)| ^ k * ((O.relIndex Q : ℝ) * (D.relIndex O : ℝ)) := by
    calc _ ≤ _ := keyR
      _ = _ := by ring
  exact le_of_mul_le_mul_left this ha

end PI.UnitaryGroupMassFormula.LCG
