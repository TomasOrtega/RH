import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMulEqMulDiagonal

noncomputable section

open Matrix

namespace GlobalTheory.IndexTranspose

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ}

abbrev stdLat (O K : Type) [CommRing O] [Field K] [Algebra O K] (r : ℕ) : Submodule O (Fin r → K) :=
  Submodule.span O (Set.range (Pi.basisFun K (Fin r)))

/- English proof (translation)
Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩`. Use `⟨c, funext fun i => ?_⟩` and prove the remaining obligations. Simplify using `[Finset.sum_apply, Pi.single_apply, Algebra.smul_def]`.

Introduce and unpack `⟨w, rfl⟩`. Use `⟨w, funext fun i => ?_⟩` and prove the remaining obligations. Simplify using `[Finset.sum_apply, Pi.single_apply, Algebra.smul_def]`.
-/
theorem mem_stdLat {v : Fin r → K} :
    v ∈ stdLat O K r ↔ ∃ w : Fin r → O, v = fun i => algebraMap O K (w i) := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c, funext fun i => ?_⟩
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  · rintro ⟨w, rfl⟩
    refine ⟨w, funext fun i => ?_⟩
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]

def latOf (O : Type) [CommRing O] [Algebra O K] (A : Matrix (Fin r) (Fin r) K) : Submodule O (Fin r → K) :=
  (stdLat O K r).map ((A.mulVecLin).restrictScalars O)

/- English proof (translation)
Simplify using `[latOf, Submodule.mem_map]`.
-/
theorem mem_latOf {A : Matrix (Fin r) (Fin r) K} {v : Fin r → K} :
    v ∈ latOf O A ↔ ∃ w ∈ stdLat O K r, A *ᵥ w = v := by
  simp [latOf, Submodule.mem_map]

/- English proof (translation)
Use extensionality with `v`. Rewrite using `[Submodule.mem_map, mem_latOf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Conclude with `⟨B *ᵥ w, mem_latOf.2 ⟨w, hw, rfl⟩, by simp [Matrix.mulVec_mulVec]⟩`.

Introduce and unpack `⟨u, hu, rfl⟩`. Take `⟨w, hw, rfl⟩` from `mem_latOf.1 hu`. Conclude with `⟨w, hw, by simp [Matrix.mulVec_mulVec]⟩`.
-/
theorem latOf_mul (A B : Matrix (Fin r) (Fin r) K) :
    latOf O (A * B) = (latOf O B).map ((A.mulVecLin).restrictScalars O) := by
  ext v
  rw [Submodule.mem_map, mem_latOf]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨B *ᵥ w, mem_latOf.2 ⟨w, hw, rfl⟩, by simp [Matrix.mulVec_mulVec]⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨w, hw, rfl⟩ := mem_latOf.1 hu
    exact ⟨w, hw, by simp [Matrix.mulVec_mulVec]⟩

/- English proof (translation)
Use extensionality with `v`. Rewrite using `[mem_latOf]`. Simplify using the standard rewrite rules.
-/
theorem latOf_one : latOf O (1 : Matrix (Fin r) (Fin r) K) = stdLat O K r := by
  ext v
  rw [mem_latOf]
  simp

/- English proof (translation)
Take `⟨w, rfl⟩` from `mem_stdLat.1 hv`. Use `mem_stdLat.2 ⟨N *ᵥ w, funext fun i => ?_⟩` and prove the remaining obligations. Conclude with `(RingHom.map_mulVec (algebraMap O K) N w i).symm`.
-/
theorem map_mulVec_mem (N : Matrix (Fin r) (Fin r) O) {v : Fin r → K} (hv : v ∈ stdLat O K r) :
    (N.map (algebraMap O K)) *ᵥ v ∈ stdLat O K r := by
  obtain ⟨w, rfl⟩ := mem_stdLat.1 hv
  refine mem_stdLat.2 ⟨N *ᵥ w, funext fun i => ?_⟩
  exact (RingHom.map_mulVec (algebraMap O K) N w i).symm

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `v hv`. Take `⟨w, hw, rfl⟩` from `mem_latOf.1 hv`. Conclude with `map_mulVec_mem N hw`. Introduce `v hv`.

Use `mem_latOf.2 ⟨(N⁻¹).map (algebraMap O K) *ᵥ v, map_mulVec_mem _ hv, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hN, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]`.
-/
theorem latOf_unimod (N : Matrix (Fin r) (Fin r) O) (hN : IsUnit N.det) :
    latOf O (N.map (algebraMap O K)) = stdLat O K r := by
  apply le_antisymm
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_latOf.1 hv
    exact map_mulVec_mem N hw
  · intro v hv
    refine mem_latOf.2 ⟨(N⁻¹).map (algebraMap O K) *ᵥ v, map_mulVec_mem _ hv, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hN,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

/- English proof (translation)
Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `(hN.map _).ne_zero`.
-/
theorem det_map_ne_zero (N : Matrix (Fin r) (Fin r) O) (hN : IsUnit N.det) :
    (N.map (algebraMap O K)).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (hN.map _).ne_zero

/- English proof (translation)
Use extensionality with `v`. Simplify using `[Submodule.mem_map, AddSubgroup.mem_map]`.
-/
theorem toAddSubgroup_map (A : Matrix (Fin r) (Fin r) K) (p : Submodule O (Fin r → K)) :
    (p.map ((A.mulVecLin).restrictScalars O)).toAddSubgroup =
      p.toAddSubgroup.map A.mulVecLin.toAddMonoidHom := by
  ext v
  simp [Submodule.mem_map, AddSubgroup.mem_map]

def idx (O : Type) [CommRing O] [Algebra O K] (A : Matrix (Fin r) (Fin r) K) : ℕ :=
  (latOf O A).toAddSubgroup.relIndex (stdLat O K r).toAddSubgroup

/- English proof (translation)
Unfold `idx`. Rewrite using `[latOf_mul, hU]`. Both sides reduce to the same expression.
-/
theorem idx_mul_right (A U : Matrix (Fin r) (Fin r) K) (hU : latOf O U = stdLat O K r) :
    idx O (A * U) = idx O A := by
  unfold idx
  rw [latOf_mul, hU]
  rfl

/- English proof (translation)
Establish `hinj : Function.Injective U.mulVecLin.toAddMonoidHom` using `fun a b hab => Matrix.mulVec_injective_of_det_ne_zero hd hab`. Establish `e : (stdLat O K r).toAddSubgroup = (stdLat O K r).toAddSubgroup.map U.mulVecLin.toAddMonoidHom`. Rewrite using `[← toAddSubgroup_map]`. Conclude with `congrArg Submodule.toAddSubgroup hU.symm`. Unfold `idx`.

Rewrite using `[latOf_mul, toAddSubgroup_map]`. Use `conv_lhs => rw [e]`. Conclude with `AddSubgroup.relIndex_map_map_of_injective _ _ hinj`.
-/
theorem idx_mul_left (U A : Matrix (Fin r) (Fin r) K) (hU : latOf O U = stdLat O K r) (hd : U.det ≠ 0) :
    idx O (U * A) = idx O A := by
  have hinj : Function.Injective U.mulVecLin.toAddMonoidHom :=
    fun a b hab => Matrix.mulVec_injective_of_det_ne_zero hd hab
  have e : (stdLat O K r).toAddSubgroup = (stdLat O K r).toAddSubgroup.map U.mulVecLin.toAddMonoidHom := by
    rw [← toAddSubgroup_map]
    exact congrArg Submodule.toAddSubgroup hU.symm
  unfold idx
  rw [latOf_mul, toAddSubgroup_map]
  conv_lhs => rw [e]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj

/- English proof (translation)
Take `⟨c, hc⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors O) (Finset.univ : Finset (Fin r × Fin r)) (fun ij => g ij.1 ij.2)`. Establish `hc'` using `fun ij : Fin r × Fin r => RingHom.mem_rangeS.1 (hc ij (Finset.mem_univ ij))`. Use `choose N0 hN0 using hc'`. Use `set a : K := algebraMap O K (c : O) with ha_def`. Establish `ha : a ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors c.2`.

Set `N : Matrix (Fin r) (Fin r) O` to `Matrix.of fun i j => N0 (i, j)`. Establish `hNmap : N.map (algebraMap O K) = a • g`. Use extensionality with `i j`. Simplify using `only [N, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, hN0 (i, j), ha_def, smul_eq_mul, Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]`. Establish `hNdet : N.det ≠ 0`.

Introduce `h0`. Establish `e` using `RingHom.map_det (algebraMap O K) N`. Rewrite `e` using `[h0, map_zero, RingHom.mapMatrix_apply, hNmap, Matrix.det_smul]`. Conclude with `mul_ne_zero (pow_ne_zero _ ha) hg e.symm`. Take `⟨P, Q, hP, hQ, d, hPQ⟩` from `GlobalTheory.SmithBetween.exists_mul_eq_mul_diagonal N hNdet`.

Use `set D : Matrix (Fin r) (Fin r) K := a⁻¹ • Matrix.diagonal (fun i => algebraMap O K (d i)) with hD`. Establish `hmap` using `congrArg (fun M : Matrix (Fin r) (Fin r) O => M.map (algebraMap O K)) hPQ`. Simplify using `only [Matrix.map_mul, hNmap, Matrix.diagonal_map (map_zero _)] at hmap`. Establish `key : g * Q.map (algebraMap O K) = P.map (algebraMap O K) * D`. Rewrite using `[hD, Matrix.mul_smul, ← hmap, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ ha, one_smul]`.

Establish `hDT : Dᵀ = D`. Rewrite using `[hD, Matrix.transpose_smul, Matrix.diagonal_transpose]`. Establish `hQT : IsUnit Qᵀ.det` using `by rwa [Matrix.det_transpose]`. Establish `hPT : IsUnit Pᵀ.det` using `by rwa [Matrix.det_transpose]`. Establish `e1 : idx O g = idx O D`.

Rewrite using `[← idx_mul_right g _ (latOf_unimod Q hQ), key, idx_mul_left _ _ (latOf_unimod P hP) (det_map_ne_zero P hP)]`. Establish `e2 : idx O gᵀ = idx O D`. Establish `hQ'` using `latOf_unimod (K := K) Qᵀ hQT`. Rewrite `hQ'` using `[Matrix.transpose_map]`. Establish `hP'` using `latOf_unimod (K := K) Pᵀ hPT`.

Rewrite `hP'` using `[Matrix.transpose_map]`. Establish `hQd` using `det_map_ne_zero (K := K) Qᵀ hQT`. Rewrite `hQd` using `[Matrix.transpose_map]`. Rewrite using `[← idx_mul_left _ gᵀ hQ' hQd, ← Matrix.transpose_mul, key, Matrix.transpose_mul, hDT, idx_mul_right _ _ hP']`. Rewrite using `[e1, e2]`.
-/
theorem idx_transpose [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K]
    (g : Matrix (Fin r) (Fin r) K) (hg : g.det ≠ 0) : idx O gᵀ = idx O g := by
  classical
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    (Finset.univ : Finset (Fin r × Fin r)) (fun ij => g ij.1 ij.2)
  have hc' := fun ij : Fin r × Fin r => RingHom.mem_rangeS.1 (hc ij (Finset.mem_univ ij))
  choose N0 hN0 using hc'
  set a : K := algebraMap O K (c : O) with ha_def
  have ha : a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors c.2
  let N : Matrix (Fin r) (Fin r) O := Matrix.of fun i j => N0 (i, j)
  have hNmap : N.map (algebraMap O K) = a • g := by
    ext i j
    simp only [N, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, hN0 (i, j), ha_def, smul_eq_mul, Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]
  have hNdet : N.det ≠ 0 := by
    intro h0
    have e := RingHom.map_det (algebraMap O K) N
    rw [h0, map_zero, RingHom.mapMatrix_apply, hNmap, Matrix.det_smul] at e
    exact mul_ne_zero (pow_ne_zero _ ha) hg e.symm
  obtain ⟨P, Q, hP, hQ, d, hPQ⟩ := GlobalTheory.SmithBetween.exists_mul_eq_mul_diagonal N hNdet
  set D : Matrix (Fin r) (Fin r) K := a⁻¹ • Matrix.diagonal (fun i => algebraMap O K (d i)) with hD
  have hmap := congrArg (fun M : Matrix (Fin r) (Fin r) O => M.map (algebraMap O K)) hPQ
  simp only [Matrix.map_mul, hNmap, Matrix.diagonal_map (map_zero _)] at hmap
  have key : g * Q.map (algebraMap O K) = P.map (algebraMap O K) * D := by
    rw [hD, Matrix.mul_smul, ← hmap, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have hDT : Dᵀ = D := by
    rw [hD, Matrix.transpose_smul, Matrix.diagonal_transpose]
  have hQT : IsUnit Qᵀ.det := by rwa [Matrix.det_transpose]
  have hPT : IsUnit Pᵀ.det := by rwa [Matrix.det_transpose]
  have e1 : idx O g = idx O D := by
    rw [← idx_mul_right g _ (latOf_unimod Q hQ), key,
      idx_mul_left _ _ (latOf_unimod P hP) (det_map_ne_zero P hP)]
  have e2 : idx O gᵀ = idx O D := by
    have hQ' := latOf_unimod (K := K) Qᵀ hQT
    rw [Matrix.transpose_map] at hQ'
    have hP' := latOf_unimod (K := K) Pᵀ hPT
    rw [Matrix.transpose_map] at hP'
    have hQd := det_map_ne_zero (K := K) Qᵀ hQT
    rw [Matrix.transpose_map] at hQd
    rw [← idx_mul_left _ gᵀ hQ' hQd, ← Matrix.transpose_mul, key, Matrix.transpose_mul, hDT,
      idx_mul_right _ _ hP']
  rw [e1, e2]

/- English proof (translation)
Introduce `O K _ _ _ _ _ _ _ r h`. Use `set g : Matrix (Fin r) (Fin r) K := ((h⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) with hg_def`. Use `set hM : Matrix (Fin r) (Fin r) K := (h : Matrix (Fin r) (Fin r) K) with hM_def`. Establish `hgh : g * hM = 1` using `Units.inv_mul h`. Establish `hg : g.det ≠ 0`.

Introduce `h0`. Establish `e` using `congrArg Matrix.det hgh`. Rewrite `e` using `[Matrix.det_mul, h0, zero_mul, Matrix.det_one]`. Conclude with `zero_ne_one e`. Establish `hginj : Function.Injective g.mulVecLin.toAddMonoidHom` using `fun a b hab => Matrix.mulVec_injective_of_det_ne_zero hg hab`.

Express the relevant statement in the definitionally equal form `idx O gᵀ = (stdLat O K r).toAddSubgroup.relIndex (latOf O hM).toAddSubgroup`. Establish `e1 : (latOf O g).toAddSubgroup = (stdLat O K r).toAddSubgroup.map g.mulVecLin.toAddMonoidHom` using `toAddSubgroup_map g _`. Establish `e2 : (stdLat O K r).toAddSubgroup = (latOf O hM).toAddSubgroup.map g.mulVecLin.toAddMonoidHom`. Rewrite using `[← toAddSubgroup_map, ← latOf_mul, hgh, latOf_one]`. Rewrite using `[idx_transpose g hg, ← AddSubgroup.relIndex_map_map_of_injective _ _ hginj, ← e1, ← e2]`.

Both sides reduce to the same expression.
-/
theorem relIndex_transpose_inv : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (h : GL (Fin r) K), ((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map ((((h⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ.mulVecLin).restrictScalars O)).toAddSubgroup.relIndex (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup = (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup.relIndex ((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((h : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)).toAddSubgroup := by
  intro O K _ _ _ _ _ _ _ r h
  set g : Matrix (Fin r) (Fin r) K := ((h⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) with hg_def
  set hM : Matrix (Fin r) (Fin r) K := (h : Matrix (Fin r) (Fin r) K) with hM_def
  have hgh : g * hM = 1 := Units.inv_mul h
  have hg : g.det ≠ 0 := by
    intro h0
    have e := congrArg Matrix.det hgh
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at e
    exact zero_ne_one e
  have hginj : Function.Injective g.mulVecLin.toAddMonoidHom :=
    fun a b hab => Matrix.mulVec_injective_of_det_ne_zero hg hab
  change idx O gᵀ = (stdLat O K r).toAddSubgroup.relIndex (latOf O hM).toAddSubgroup
  have e1 : (latOf O g).toAddSubgroup = (stdLat O K r).toAddSubgroup.map g.mulVecLin.toAddMonoidHom :=
    toAddSubgroup_map g _
  have e2 : (stdLat O K r).toAddSubgroup = (latOf O hM).toAddSubgroup.map g.mulVecLin.toAddMonoidHom := by
    rw [← toAddSubgroup_map, ← latOf_mul, hgh, latOf_one]
  rw [idx_transpose g hg, ← AddSubgroup.relIndex_map_map_of_injective _ _ hginj, ← e1, ← e2]
  rfl

end GlobalTheory.IndexTranspose
