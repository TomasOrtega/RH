import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianOpenChartDiagonalUnipotentStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalHermitianDiagonalizationUnitsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightActionIdentitiesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Tri

variable {R K : Type} [CommRing R] [CommRing K] {n : ℕ}

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Apply `Finset.sum_eq_single i` to reduce the goal to its premises. Introduce `j _ hj`. Break down `lt_or_gt_of_ne hj with h | h` into its components or cases. Rewrite using `[hA h, zero_mul]`.

Rewrite using `[hB h, mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem tri_mul_diag {A B : Matrix (Fin n) (Fin n) K} (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

def triSub (ι : R →+* K) (U : Subgroup Rˣ) (n : ℕ) : Subgroup (GL (Fin n) K) where
  carrier := {x | (x : Matrix (Fin n) (Fin n) K).BlockTriangular id ∧
    ∀ i, ∃ u ∈ U, (x : Matrix (Fin n) (Fin n) K) i i = ι (u : Rˣ)}
  one_mem' := by
    refine ⟨?_, fun i => ⟨1, U.one_mem, by simp⟩⟩
    simpa using Matrix.blockTriangular_one (b := (id : Fin n → Fin n))
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by simpa using ha.mul hb, fun i => ?_⟩
    obtain ⟨u, hu, e⟩ := ha' i
    obtain ⟨v, hv, f⟩ := hb' i
    refine ⟨u * v, U.mul_mem hu hv, ?_⟩
    rw [Units.val_mul, tri_mul_diag ha hb, e, f]
    simp
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    have hinv : ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        = (x : Matrix (Fin n) (Fin n) K)⁻¹ := Matrix.coe_units_inv x
    have ht : ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).BlockTriangular id := by
      rw [hinv]
      let : Invertible (x : Matrix (Fin n) (Fin n) K) := x.invertible
      exact Matrix.blockTriangular_inv_of_blockTriangular hx
    refine ⟨ht, fun i => ?_⟩
    obtain ⟨u, hu, e⟩ := hx' i
    refine ⟨u⁻¹, U.inv_mem hu, ?_⟩
    have h1 : (x : Matrix (Fin n) (Fin n) K) i i * ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i = 1 := by
      rw [← tri_mul_diag hx ht, ← Units.val_mul, mul_inv_cancel]
      simp
    rw [e] at h1
    have h2 : ι ((u⁻¹ : Rˣ) : R) * ι (u : Rˣ) = 1 := by
      rw [← map_mul]; simp
    calc _ = ι ((u⁻¹ : Rˣ) : R) * ι (u : Rˣ) * ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i := by
          rw [h2, one_mul]
      _ = ι ((u⁻¹ : Rˣ) : R) := by rw [mul_assoc, h1, mul_one]

def nMat (m : {p : Fin n × Fin n // p.1 < p.2} → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => if i = j then 1 else if h : i < j then m ⟨(i, j), h⟩ else 0

/- English proof (translation)
Introduce `i j h`. Establish `h' : j < i` using `h`. Simplify using `[nMat, h'.ne', h'.not_gt]`.
-/
theorem nMat_tri (m : {p : Fin n × Fin n // p.1 < p.2} → K) : (nMat m).BlockTriangular id := by
  intro i j h
  have h' : j < i := h
  simp [nMat, h'.ne', h'.not_gt]

/- English proof (translation)
Rewrite using `[Matrix.det_of_isUpperTriangular (nMat_tri m)]`. Simplify using `[nMat]`.
-/
theorem nMat_det (m : {p : Fin n × Fin n // p.1 < p.2} → K) : (nMat m).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (nMat_tri m)]
  simp [nMat]

def aMat (ι : R →+* K) {U : Subgroup Rˣ} (u : Fin n → U) (m : {p : Fin n × Fin n // p.1 < p.2} → K) :
    Matrix (Fin n) (Fin n) K :=
  Matrix.diagonal (fun i => ι ((u i : Rˣ) : R)) * nMat m

/- English proof (translation)
Simplify using `[aMat, Matrix.diagonal_mul]`.
-/
theorem aMat_apply (ι : R →+* K) {U : Subgroup Rˣ} (u : Fin n → U)
    (m : {p : Fin n × Fin n // p.1 < p.2} → K) (i j : Fin n) :
    aMat ι u m i j = ι ((u i : Rˣ) : R) * nMat m i j := by
  simp [aMat, Matrix.diagonal_mul]

/- English proof (translation)
Introduce `i j h`. Rewrite using `[aMat_apply, nMat_tri m h, mul_zero]`.
-/
theorem aMat_tri (ι : R →+* K) {U : Subgroup Rˣ} (u : Fin n → U)
    (m : {p : Fin n × Fin n // p.1 < p.2} → K) : (aMat ι u m).BlockTriangular id := by
  intro i j h
  rw [aMat_apply, nMat_tri m h, mul_zero]

/- English proof (translation)
Simplify using `[aMat, Matrix.det_mul, nMat_det, Matrix.det_diagonal, map_prod]`.
-/
theorem aMat_det (ι : R →+* K) {U : Subgroup Rˣ} (u : Fin n → U)
    (m : {p : Fin n × Fin n // p.1 < p.2} → K) :
    (aMat ι u m).det = ι ((∏ i, (u i : Rˣ) : Rˣ) : R) := by
  simp [aMat, Matrix.det_mul, nMat_det, Matrix.det_diagonal, map_prod]

def cInv (ι : R →+* K) {U : Subgroup Rˣ} (u : Fin n → U) : K :=
  ι (((∏ i, (u i : Rˣ) : Rˣ)⁻¹ : Rˣ) : R)

/- English proof (translation)
Rewrite using `[aMat_det, cInv, ← map_mul, Units.inv_mul, map_one]`.
-/
theorem cInv_mul (ι : R →+* K) {U : Subgroup Rˣ} (u : Fin n → U)
    (m : {p : Fin n × Fin n // p.1 < p.2} → K) : cInv ι u * (aMat ι u m).det = 1 := by
  rw [aMat_det, cInv, ← map_mul, Units.inv_mul, map_one]

def aGL (ι : R →+* K) {U : Subgroup Rˣ} (u : Fin n → U)
    (m : {p : Fin n × Fin n // p.1 < p.2} → K) : GL (Fin n) K where
  val := aMat ι u m
  inv := cInv ι u • (aMat ι u m).adjugate
  val_inv := by
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, cInv_mul, one_smul]
  inv_val := by
    rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, cInv_mul, one_smul]

/- English proof (translation)
Use `⟨aMat_tri ι u m, fun i => ⟨u i, (u i).2, ?_⟩⟩` and prove the remaining obligations. Use `show aMat ι u m i i = _`. Rewrite using `[aMat_apply]`. Simplify using `[nMat]`.
-/
theorem aGL_mem (ι : R →+* K) {U : Subgroup Rˣ} (u : Fin n → U)
    (m : {p : Fin n × Fin n // p.1 < p.2} → K) : aGL ι u m ∈ triSub ι U n := by
  refine ⟨aMat_tri ι u m, fun i => ⟨u i, (u i).2, ?_⟩⟩
  show aMat ι u m i i = _
  rw [aMat_apply]
  simp [nMat]

def uOf (ι : R →+* K) {U : Subgroup Rˣ} (x : triSub ι U n) (i : Fin n) : U :=
  ⟨(x.2.2 i).choose, (x.2.2 i).choose_spec.1⟩

/- English proof (translation)
The claim follows from `(x.2.2 i).choose_spec.2`.
-/
theorem uOf_spec (ι : R →+* K) {U : Subgroup Rˣ} (x : triSub ι U n) (i : Fin n) :
    ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i = ι ((uOf ι x i : Rˣ) : R) :=
  (x.2.2 i).choose_spec.2

def mOf (ι : R →+* K) {U : Subgroup Rˣ} (x : triSub ι U n) :
    {p : Fin n × Fin n // p.1 < p.2} → K :=
  fun p => ι (((uOf ι x p.1.1 : Rˣ)⁻¹ : Rˣ) : R) * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) p.1.1 p.1.2

/- English proof (translation)
Rewrite using `[← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]`.
-/
theorem unit_cancel (ι : R →+* K) (u : Rˣ) (a : K) : ι ((u⁻¹ : Rˣ) : R) * (ι (u : R) * a) = a := by
  rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

/- English proof (translation)
Rewrite using `[← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]`.
-/
theorem unit_cancel' (ι : R →+* K) (u : Rˣ) (a : K) : ι (u : R) * (ι ((u⁻¹ : Rˣ) : R) * a) = a := by
  rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Use `show aMat ι (uOf ι x) (mOf ι x) i j = _`. Rewrite using `[aMat_apply]`. Break down `lt_trichotomy i j with h | h | h` into its components or cases.

Simplify using `only [nMat, Matrix.of_apply, h.ne, if_false, h, dif_pos, mOf]`. Conclude with `unit_cancel' ι _ _`. Substitute `h` using the available equality. Simplify using `[nMat, uOf_spec]`. Establish `: ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = 0` using `x.2.1 h`.

Rewrite using `[this]`. Simplify using `[nMat, h.ne', h.not_gt]`.
-/
theorem aGL_coords (ι : R →+* K) {U : Subgroup Rˣ} (x : triSub ι U n) :
    aGL ι (uOf ι x) (mOf ι x) = (x : GL (Fin n) K) := by
  apply Units.ext
  ext i j
  show aMat ι (uOf ι x) (mOf ι x) i j = _
  rw [aMat_apply]
  rcases lt_trichotomy i j with h | h | h
  · simp only [nMat, Matrix.of_apply, h.ne, if_false, h, dif_pos, mOf]
    exact unit_cancel' ι _ _
  · subst h
    simp [nMat, uOf_spec]
  · have : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = 0 := x.2.1 h
    rw [this]
    simp [nMat, h.ne', h.not_gt]

/- English proof (translation)
Establish `h1 : uOf ι ⟨aGL ι u m, aGL_mem ι u m⟩ = u`. Use function extensionality and compare the values at `i`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Apply `hι` to reduce the goal to its premises.

Rewrite using `[← uOf_spec]`. Use `show aMat ι u m i i = _`. Rewrite using `[aMat_apply]`. Simplify using `[nMat]`. Use `⟨h1, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `p`. Take `⟨⟨i, j⟩, h⟩` from `p`. Establish `h' : i < j` using `h`. Simplify using `only [mOf, h1]`. Use `show _ * aMat ι u m i j = _`.

Rewrite using `[aMat_apply]`. Simplify using `only [nMat, Matrix.of_apply, h'.ne, if_false, h', dif_pos]`. Conclude with `unit_cancel ι _ _`.
-/
theorem coords_aGL (ι : R →+* K) (hι : Function.Injective ι) {U : Subgroup Rˣ} (u : Fin n → U)
    (m : {p : Fin n × Fin n // p.1 < p.2} → K) :
    uOf ι ⟨aGL ι u m, aGL_mem ι u m⟩ = u ∧ mOf ι ⟨aGL ι u m, aGL_mem ι u m⟩ = m := by
  have h1 : uOf ι ⟨aGL ι u m, aGL_mem ι u m⟩ = u := by
    funext i
    apply Subtype.ext
    apply Units.ext
    apply hι
    rw [← uOf_spec]
    show aMat ι u m i i = _
    rw [aMat_apply]
    simp [nMat]
  refine ⟨h1, ?_⟩
  funext p
  obtain ⟨⟨i, j⟩, h⟩ := p
  have h' : i < j := h
  simp only [mOf, h1]
  show _ * aMat ι u m i j = _
  rw [aMat_apply]
  simp only [nMat, Matrix.of_apply, h'.ne, if_false, h', dif_pos]
  exact unit_cancel ι _ _

/- English proof (translation)
Establish `hd : cT sig (Matrix.diagonal (fun i => ι ((u i : Rˣ) : R))) = Matrix.diagonal (fun i => ι ((u i : Rˣ) : R))`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[cT, hs]`.

Simplify using `[cT, Matrix.diagonal, h, Ne.symm h]`. Establish `hm : Matrix.diagonal (fun i => ι ((u i : Rˣ) : R)) * Matrix.diagonal (fun i => ι (d i : R)) * Matrix.diagonal (fun i => ι ((u i : Rˣ) : R)) = Matrix.diagonal (fun i => ι ((((u i : Rˣ) ^ 2 * d i : Rˣ)) : R))`. Simplify using `only [Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[aMat, cT_mul, hd, ← hm]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem aMat_gram (ι : R →+* K) (sig : K →+* K) (hs : ∀ r, sig (ι r) = ι r) {U : Subgroup Rˣ}
    (u : Fin n → U) (m : {p : Fin n × Fin n // p.1 < p.2} → K) (d : Fin n → Rˣ) :
    cT sig (aMat ι u m) * Matrix.diagonal (fun i => ι (d i : R)) * aMat ι u m
      = cT sig (nMat m) * Matrix.diagonal (fun i => ι ((((u i : Rˣ) ^ 2 * d i : Rˣ)) : R)) * nMat m := by
  have hd : cT sig (Matrix.diagonal (fun i => ι ((u i : Rˣ) : R))) = Matrix.diagonal (fun i => ι ((u i : Rˣ) : R)) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [cT, hs]
    · simp [cT, Matrix.diagonal, h, Ne.symm h]
  have hm : Matrix.diagonal (fun i => ι ((u i : Rˣ) : R)) * Matrix.diagonal (fun i => ι (d i : R)) *
      Matrix.diagonal (fun i => ι ((u i : Rˣ) : R))
      = Matrix.diagonal (fun i => ι ((((u i : Rˣ) ^ 2 * d i : Rˣ)) : R)) := by
    simp only [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
    ring
  rw [aMat, cT_mul, hd, ← hm]
  simp only [Matrix.mul_assoc]

section Top

variable [TopologicalSpace R] [TopologicalSpace K] [IsTopologicalRing R] [IsTopologicalRing K]

/- English proof (translation)
Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Simplify using `only [nMat, Matrix.of_apply]`. Use `split_ifs`. Conclude with `continuous_const`. Conclude with `continuous_apply _`.

Conclude with `continuous_const`.
-/
theorem nMat_cont : Continuous (nMat : ({p : Fin n × Fin n // p.1 < p.2} → K) → _) := by
  refine continuous_matrix fun i j => ?_
  simp only [nMat, Matrix.of_apply]
  split_ifs
  · exact continuous_const
  · exact continuous_apply _
  · exact continuous_const

/- English proof (translation)
Use `Continuous.matrix_mul (Continuous.matrix_diagonal ?_) (nMat_cont.comp continuous_snd)` and prove the remaining obligations. Use `continuous_pi fun i => hι.comp (Units.continuous_val.comp ?_)` and prove the remaining obligations. Conclude with `continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)`.
-/
theorem aMat_cont (ι : R →+* K) (hι : Continuous ι) (U : Subgroup Rˣ) :
    Continuous fun p : (Fin n → U) × ({p : Fin n × Fin n // p.1 < p.2} → K) => aMat ι p.1 p.2 := by
  refine Continuous.matrix_mul (Continuous.matrix_diagonal ?_) (nMat_cont.comp continuous_snd)
  refine continuous_pi fun i => hι.comp (Units.continuous_val.comp ?_)
  exact continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨aMat_cont ι hι U, ?_⟩` and prove the remaining obligations. Establish `hc : Continuous fun p : (Fin n → U) × ({p : Fin n × Fin n // p.1 < p.2} → K) => cInv ι p.1`. Use `hι.comp (Units.continuous_val.comp (Continuous.inv ?_))` and prove the remaining obligations. Use `continuous_finsetProd _ fun i _ => ?_` and prove the remaining obligations. Conclude with `continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)`.

Conclude with `hc.smul (aMat_cont ι hι U).matrix_adjugate`.
-/
theorem aGL_cont (ι : R →+* K) (hι : Continuous ι) (U : Subgroup Rˣ) :
    Continuous fun p : (Fin n → U) × ({p : Fin n × Fin n // p.1 < p.2} → K) => aGL ι p.1 p.2 := by
  refine Units.continuous_iff.2 ⟨aMat_cont ι hι U, ?_⟩
  have hc : Continuous fun p : (Fin n → U) × ({p : Fin n × Fin n // p.1 < p.2} → K) => cInv ι p.1 := by
    refine hι.comp (Units.continuous_val.comp (Continuous.inv ?_))
    refine continuous_finsetProd _ fun i _ => ?_
    exact continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)
  exact hc.smul (aMat_cont ι hι U).matrix_adjugate

/- English proof (translation)
The claim follows from `(continuous_id.matrix_elem i j).comp (Units.continuous_val.comp continuous_subtype_val)`.
-/
theorem entry_cont (ι : R →+* K) (U : Subgroup Rˣ) (i j : Fin n) :
    Continuous fun x : triSub ι U n => ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j :=
  (continuous_id.matrix_elem i j).comp (Units.continuous_val.comp continuous_subtype_val)

/- English proof (translation)
Use `hv.continuous_iff.2 ?_` and prove the remaining obligations. Establish `: (Units.val ∘ fun x : triSub ι U n => (uOf ι x i : Rˣ)) = fun x : triSub ι U n => π (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i)`. Use function extensionality and compare the values at `x`. Simplify using `[uOf_spec, hπι]`. Rewrite using `[this]`.

Conclude with `hπ.comp (entry_cont ι U i i)`.
-/
theorem uOf_cont (ι : R →+* K) (π : K → R) (hπ : Continuous π) (hπι : ∀ r, π (ι r) = r)
    (hv : IsInducing (Units.val : Rˣ → R)) (U : Subgroup Rˣ) (i : Fin n) :
    Continuous fun x : triSub ι U n => (uOf ι x i : Rˣ) := by
  refine hv.continuous_iff.2 ?_
  have : (Units.val ∘ fun x : triSub ι U n => (uOf ι x i : Rˣ))
      = fun x : triSub ι U n => π (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i) := by
    funext x
    simp [uOf_spec, hπι]
  rw [this]
  exact hπ.comp (entry_cont ι U i i)

def triHomeo (ι : R →+* K) (hι : Continuous ι) (π : K → R) (hπ : Continuous π)
    (hπι : ∀ r, π (ι r) = r) (hv : IsInducing (Units.val : Rˣ → R)) (U : Subgroup Rˣ) :
    ((Fin n → U) × ({p : Fin n × Fin n // p.1 < p.2} → K)) ≃ₜ triSub ι U n where
  toFun p := ⟨aGL ι p.1 p.2, aGL_mem ι p.1 p.2⟩
  invFun x := (uOf ι x, mOf ι x)
  left_inv p := by
    have hinj : Function.Injective ι := Function.LeftInverse.injective hπι
    exact Prod.ext (coords_aGL ι hinj p.1 p.2).1 (coords_aGL ι hinj p.1 p.2).2
  right_inv x := Subtype.ext (aGL_coords ι x)
  continuous_toFun := (aGL_cont ι hι U).subtype_mk _
  continuous_invFun := by
    refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun p => ?_)
    · exact (uOf_cont ι π hπ hπι hv U i).subtype_mk _
    · refine Continuous.mul ?_ (entry_cont ι U _ _)
      exact hι.comp (Units.continuous_val.comp (uOf_cont ι π hπ hπι hv U p.1.1).inv)

/- English proof (translation)
The claim follows from `(IsOpenEmbedding.piMap fun i => (Homeomorph.mulRight (d i)).isOpenEmbedding.comp hU).prodMap IsOpenEmbedding.id`.
-/
theorem sq_open (U : Subgroup Rˣ) (hU : IsOpenEmbedding (fun u : U => ((u : Rˣ) ^ 2 : Rˣ)))
    (d : Fin n → Rˣ) :
    IsOpenEmbedding (fun p : (Fin n → U) × ({p : Fin n × Fin n // p.1 < p.2} → K) =>
      ((fun i => (p.1 i : Rˣ) ^ 2 * d i : Fin n → Rˣ), p.2)) :=
  (IsOpenEmbedding.piMap fun i => (Homeomorph.mulRight (d i)).isOpenEmbedding.comp hU).prodMap
    IsOpenEmbedding.id

/- English proof (translation)
Use `set g : Matrix (Fin n) (Fin n) K := (G : Matrix (Fin n) (Fin n) K) with hgdef`. Use `set g' : Matrix (Fin n) (Fin n) K := ((G⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hg'def`. Establish `h1 : g * g' = 1` using `by rw [hgdef, hg'def, ← Units.val_mul, mul_inv_cancel]; rfl`. Establish `h2 : g' * g = 1` using `by rw [hgdef, hg'def, ← Units.val_mul, inv_mul_cancel]; rfl`. Set `h : GL (Fin n) K ≃ₜ GL (Fin n) K` to `(Homeomorph.mulLeft G).trans (Homeomorph.mulRight G⁻¹)`.

Set `Q : Subgroup (GL (Fin n) K)` to `Q₀.comap (MulAut.conj G).toMonoidHom`. Set `e : Q ≃ₜ Q₀` to `h.subtype (fun y => Iff.rfl)`. Establish `hcT : ∀ (a b : Matrix (Fin n) (Fin n) K), a * b = 1 → ∀ S : Matrix (Fin n) (Fin n) K, cT sig b * (cT sig a * S * a) * b = S`. Introduce `a b hab S`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[cT_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = S := by rw [hab, cT_one]; simp`. Set `T : Hm ≃ₜ Hm` to `{ toFun := fun S => ⟨cT sig g * S * g, hH _ S.2 _⟩ invFun := fun S => ⟨cT sig g' * S * g', hH _ S.2 _⟩ left_inv := fun S => Subtype.ext (hcT g g' h1 _) right_inv := fun S => Subtype.ext (hcT g' g h2 _) continuous_toFun := Continuous.subtype_mk ((continuous_const.matrix_mul contin …`. Use `⟨Q, e, fun y => T (o₀ (e y)), T.isOpenEmbedding.comp (ho₀.comp e.isOpenEmbedding), ?_⟩` and prove the remaining obligations.

Introduce `y`. Use `set Y : Matrix (Fin n) (Fin n) K := ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hY`. Establish `hx : (((e y : Q₀) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = g * Y * g'` using `rfl`. Use `show cT sig g * ((o₀ (e y) : Hm) : Matrix (Fin n) (Fin n) K) * g = _`. Rewrite using `[hf, hx]`.

Establish `hxg : g * Y * g' * g = g * Y` using `by rw [Matrix.mul_assoc, h2, Matrix.mul_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[cT_mul sig (g * Y * g') g]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = cT sig (g * Y) * D * (g * Y) := by rw [hxg]`.

Use `_ = cT sig Y * (cT sig g * D * g) * Y := by`. Rewrite using `[cT_mul]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem conj_case (sig : K →+* K) (Hm : AddSubgroup (Matrix (Fin n) (Fin n) K))
    (hH : ∀ S ∈ Hm, ∀ g : Matrix (Fin n) (Fin n) K, cT sig g * S * g ∈ Hm)
    (G : GL (Fin n) K) (Q₀ : Subgroup (GL (Fin n) K)) (o₀ : Q₀ → Hm) (ho₀ : IsOpenEmbedding o₀)
    (D : Matrix (Fin n) (Fin n) K)
    (hf : ∀ x : Q₀, (o₀ x : Matrix (Fin n) (Fin n) K) =
      cT sig ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * D * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ∃ (Q : Subgroup (GL (Fin n) K)) (_ : Q ≃ₜ Q₀) (o : Q → Hm), IsOpenEmbedding o ∧
      ∀ x : Q, (o x : Matrix (Fin n) (Fin n) K) =
        cT sig ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (cT sig (G : Matrix (Fin n) (Fin n) K) * D * (G : Matrix (Fin n) (Fin n) K)) *
          ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  set g : Matrix (Fin n) (Fin n) K := (G : Matrix (Fin n) (Fin n) K) with hgdef
  set g' : Matrix (Fin n) (Fin n) K := ((G⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hg'def
  have h1 : g * g' = 1 := by rw [hgdef, hg'def, ← Units.val_mul, mul_inv_cancel]; rfl
  have h2 : g' * g = 1 := by rw [hgdef, hg'def, ← Units.val_mul, inv_mul_cancel]; rfl
  let h : GL (Fin n) K ≃ₜ GL (Fin n) K := (Homeomorph.mulLeft G).trans (Homeomorph.mulRight G⁻¹)
  let Q : Subgroup (GL (Fin n) K) := Q₀.comap (MulAut.conj G).toMonoidHom
  let e : Q ≃ₜ Q₀ := h.subtype (fun y => Iff.rfl)
  have hcT : ∀ (a b : Matrix (Fin n) (Fin n) K), a * b = 1 → ∀ S : Matrix (Fin n) (Fin n) K,
      cT sig b * (cT sig a * S * a) * b = S := by
    intro a b hab S
    calc cT sig b * (cT sig a * S * a) * b = cT sig (a * b) * S * (a * b) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = S := by rw [hab, cT_one]; simp
  let T : Hm ≃ₜ Hm :=
    { toFun := fun S => ⟨cT sig g * S * g, hH _ S.2 _⟩
      invFun := fun S => ⟨cT sig g' * S * g', hH _ S.2 _⟩
      left_inv := fun S => Subtype.ext (hcT g g' h1 _)
      right_inv := fun S => Subtype.ext (hcT g' g h2 _)
      continuous_toFun := Continuous.subtype_mk
        ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _
      continuous_invFun := Continuous.subtype_mk
        ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _ }
  refine ⟨Q, e, fun y => T (o₀ (e y)), T.isOpenEmbedding.comp (ho₀.comp e.isOpenEmbedding), ?_⟩
  intro y
  set Y : Matrix (Fin n) (Fin n) K := ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hY
  have hx : (((e y : Q₀) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = g * Y * g' := rfl
  show cT sig g * ((o₀ (e y) : Hm) : Matrix (Fin n) (Fin n) K) * g = _
  rw [hf, hx]
  have hxg : g * Y * g' * g = g * Y := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  calc cT sig g * (cT sig (g * Y * g') * D * (g * Y * g')) * g
      = cT sig (g * Y * g' * g) * D * (g * Y * g' * g) := by
        rw [cT_mul sig (g * Y * g') g]; simp only [Matrix.mul_assoc]
    _ = cT sig (g * Y) * D * (g * Y) := by rw [hxg]
    _ = cT sig Y * (cT sig g * D * g) * Y := by
        rw [cT_mul]; simp only [Matrix.mul_assoc]

end Top

end GlobalTheory.CompanionTheory.SW.Tri

namespace GlobalTheory.CompanionTheory.SW

open GlobalTheory.CompanionTheory.SW.Tri

/- English proof (translation)
Use `haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)`. Establish `hb` using `Algebra.TensorProduct.basis R (Module.finBasis F E)`. Establish `h1 : (r ⊗ₜ[F] (1 : E) : R ⊗[F] E) = algebraMap R (R ⊗[F] E) r`. Simplify using `[Algebra.TensorProduct.algebraMap_apply]`. Rewrite using `[h1, Algebra.trace_algebraMap_of_basis hb]`.

Simplify using `only [Fintype.card_fin, h2]`. Rewrite using `[nsmul_eq_mul, ← mul_assoc]`. Establish `: algebraMap F R (1 / 2) * ((2 : ℕ) : R) = 1`. Establish `: ((2 : ℕ) : R) = algebraMap F R 2` using `by rw [map_ofNat, Nat.cast_ofNat]`. Rewrite using `[this, ← map_mul]`.

Simplify using the standard rewrite rules. Rewrite using `[this, one_mul]`.
-/
theorem half_trace_tmul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (R : Type) [CommRing R] [Algebra F R] (r : R) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] (1 : E)) = r := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hb := Algebra.TensorProduct.basis R (Module.finBasis F E)
  have h1 : (r ⊗ₜ[F] (1 : E) : R ⊗[F] E) = algebraMap R (R ⊗[F] E) r := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [h1, Algebra.trace_algebraMap_of_basis hb]
  simp only [Fintype.card_fin, h2]
  rw [nsmul_eq_mul, ← mul_assoc]
  have : algebraMap F R (1 / 2) * ((2 : ℕ) : R) = 1 := by
    have : ((2 : ℕ) : R) = algebraMap F R 2 := by rw [map_ofNat, Nat.cast_ofNat]
    rw [this, ← map_mul]
    simp
  rw [this, one_mul]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM R _ _ _ _ _ hR n S hS`. Establish `hR'` using `hR`. Take `⟨i1, i2, i3, i4, i5, i6, hval, U, -, hU⟩` from `hR'`. Use `haveI := i1`. Use `haveI := i2`.

Use `haveI := i3`. Use `haveI := i4`. Use `haveI := i5`. Use `haveI := i6`. Take `⟨k1, k2, k3, k4, -, htr, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R`.

Use `haveI := k1`. Use `haveI := k2`. Use `haveI := k3`. Use `haveI := k4`. Take `⟨o, ho, hof⟩` from `GlobalTheory.T.hermitian_open_chart_diagonal_unipotent F E σ hCM R hR n`.

Take `⟨g, d, hg, hSg⟩` from `GlobalTheory.T.local_hermitian_diagonalization_units F E σ hCM R n S hS`. Establish `hH : ∀ S' ∈ HermR R σ n, ∀ g' : Matrix (Fin n) (Fin n) (R ⊗[F] E), cT (sigR R σ) g' * S' * g' ∈ HermR R σ n` using `fun S' hS' g' => (GlobalTheory.T.gram_right_action_identities F E σ hCM 0 0 ⟨fun i => i.elim0, by simp⟩ R n).2.2.2.1 ⟨S', hS'⟩ g'`. Set `ι : R →+* R ⊗[F] E` to `Algebra.TensorProduct.includeLeftRingHom`. Establish `hιa : ∀ r, ι r = r ⊗ₜ[F] (1 : E)` using `fun r => rfl`. Use `haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩`.

Use `haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)`. Establish `hι : Continuous ι`. Establish `: (ι : R → R ⊗[F] E) = fun r => r • (1 : R ⊗[F] E)`. Use function extensionality and compare the values at `r`. Rewrite using `[hιa, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.

Rewrite using `[this]`. Conclude with `(continuous_id : Continuous fun r : R => r).smul (continuous_const : Continuous fun _ : R => (1 : R ⊗[F] E))`. Set `π : R ⊗[F] E → R` to `fun k => algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) k`. Establish `hπ : Continuous π` using `continuous_const.mul htr`. Establish `hπι : ∀ r, π (ι r) = r` using `fun r => half_trace_tmul hCM.2.2.1 R r`.

Establish `hs : ∀ r, sigR R σ (ι r) = ι r` using `fun r => by simp [hιa, sigR]`. Set `Ψ` to `triHomeo (n := n) ι hι π hπ hπι hval.isInducing U`. Establish `hP` using `sq_open (K := R ⊗[F] E) U hU d`. Set `Φ : triSub ι U n → (Fin n → Rˣ) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E)` to `fun x => (fun i => (uOf ι x i : Rˣ) ^ 2 * d i, mOf ι x)`. Establish `hΦ : IsOpenEmbedding Φ` using `hP.comp Ψ.symm.isOpenEmbedding`.

Use `haveI : LocallyCompactSpace Rˣ := hval.locallyCompactSpace`. Use `haveI : SecondCountableTopology Rˣ := hval.isEmbedding.secondCountableTopology`. Establish `lc₀ : LocallyCompactSpace (triSub ι U n)` using `hΦ.locallyCompactSpace`. Establish `sc₀ : SecondCountableTopology (triSub ι U n)` using `hΦ.isEmbedding.secondCountableTopology`. Set `D : Matrix (Fin n) (Fin n) (R ⊗[F] E)` to `Matrix.diagonal (fun i => ((d i : R) ⊗ₜ[F] (1 : E) : R ⊗[F] E))`.

Establish `hf : ∀ x : triSub ι U n, (o (Φ x) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) ((x : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * D * ((x : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))`. Introduce `x`. Establish `hxa : ((x : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = aMat ι (uOf ι x) (mOf ι x)` using `by conv_lhs => rw [← aGL_coords ι x]`. Both sides reduce to the same expression. Rewrite using `[hxa]`.

Use `aMat_gram ι (sigR R σ) hs (uOf ι x) (mOf ι x) d` as an intermediate fact. Conclude with `(hof _ _ (nMat (mOf ι x)) rfl).trans this.symm`. Establish `hgu : IsUnit g` using `(Matrix.isUnit_iff_isUnit_det g).2 hg`. Take `⟨Q, e, o', ho', hform⟩` from `conj_case (sigR R σ) (HermR R σ n) hH hgu.unit (triSub ι U n) (fun x => o (Φ x)) (ho.comp hΦ) D hf`. Use `⟨Q, o', e.isOpenEmbedding.locallyCompactSpace, e.isEmbedding.secondCountableTopology, ho', ?_⟩` and prove the remaining obligations.

Introduce `x`. Rewrite using `[hform x, hSg]`. Both sides reduce to the same expression.
-/
theorem tri_slice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (S : HermR R σ n), IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det → ∃ (Q : Subgroup (GL (Fin n) (R ⊗[F] E))) (o : Q → HermR R σ n), LocallyCompactSpace Q ∧ SecondCountableTopology Q ∧ IsOpenEmbedding o ∧ ∀ x : Q, (o x : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) ((x : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * ((x : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hCM R _ _ _ _ _ hR n S hS
  have hR' := hR
  obtain ⟨i1, i2, i3, i4, i5, i6, hval, U, -, hU⟩ := hR'
  haveI := i1
  haveI := i2
  haveI := i3
  haveI := i4
  haveI := i5
  haveI := i6
  obtain ⟨k1, k2, k3, k4, -, htr, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  haveI := k1
  haveI := k2
  haveI := k3
  haveI := k4
  obtain ⟨o, ho, hof⟩ := GlobalTheory.T.hermitian_open_chart_diagonal_unipotent F E σ hCM R hR n
  obtain ⟨g, d, hg, hSg⟩ := GlobalTheory.T.local_hermitian_diagonalization_units F E σ hCM R n S hS
  have hH : ∀ S' ∈ HermR R σ n, ∀ g' : Matrix (Fin n) (Fin n) (R ⊗[F] E),
      cT (sigR R σ) g' * S' * g' ∈ HermR R σ n := fun S' hS' g' =>
    (GlobalTheory.T.gram_right_action_identities F E σ hCM 0 0 ⟨fun i => i.elim0, by simp⟩ R n).2.2.2.1 ⟨S', hS'⟩ g'
  let ι : R →+* R ⊗[F] E := Algebra.TensorProduct.includeLeftRingHom
  have hιa : ∀ r, ι r = r ⊗ₜ[F] (1 : E) := fun r => rfl
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)
  have hι : Continuous ι := by
    have : (ι : R → R ⊗[F] E) = fun r => r • (1 : R ⊗[F] E) := by
      funext r
      rw [hιa, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact (continuous_id : Continuous fun r : R => r).smul (continuous_const : Continuous fun _ : R => (1 : R ⊗[F] E))
  let π : R ⊗[F] E → R := fun k => algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) k
  have hπ : Continuous π := continuous_const.mul htr
  have hπι : ∀ r, π (ι r) = r := fun r => half_trace_tmul hCM.2.2.1 R r
  have hs : ∀ r, sigR R σ (ι r) = ι r := fun r => by simp [hιa, sigR]
  let Ψ := triHomeo (n := n) ι hι π hπ hπι hval.isInducing U
  have hP := sq_open (K := R ⊗[F] E) U hU d
  let Φ : triSub ι U n → (Fin n → Rˣ) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) :=
    fun x => (fun i => (uOf ι x i : Rˣ) ^ 2 * d i, mOf ι x)
  have hΦ : IsOpenEmbedding Φ := hP.comp Ψ.symm.isOpenEmbedding
  haveI : LocallyCompactSpace Rˣ := hval.locallyCompactSpace
  haveI : SecondCountableTopology Rˣ := hval.isEmbedding.secondCountableTopology
  have lc₀ : LocallyCompactSpace (triSub ι U n) := hΦ.locallyCompactSpace
  have sc₀ : SecondCountableTopology (triSub ι U n) := hΦ.isEmbedding.secondCountableTopology
  let D : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
    Matrix.diagonal (fun i => ((d i : R) ⊗ₜ[F] (1 : E) : R ⊗[F] E))
  have hf : ∀ x : triSub ι U n, (o (Φ x) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      cT (sigR R σ) ((x : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * D *
        ((x : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
    intro x
    have hxa : ((x : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))
        = aMat ι (uOf ι x) (mOf ι x) := by
      conv_lhs => rw [← aGL_coords ι x]
      rfl
    rw [hxa]
    have := aMat_gram ι (sigR R σ) hs (uOf ι x) (mOf ι x) d
    exact (hof _ _ (nMat (mOf ι x)) rfl).trans this.symm
  have hgu : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 hg
  obtain ⟨Q, e, o', ho', hform⟩ := conj_case (sigR R σ) (HermR R σ n) hH hgu.unit (triSub ι U n)
    (fun x => o (Φ x)) (ho.comp hΦ) D hf
  refine ⟨Q, o', e.isOpenEmbedding.locallyCompactSpace, e.isEmbedding.secondCountableTopology, ho', ?_⟩
  intro x
  rw [hform x, hSg]
  rfl

end GlobalTheory.CompanionTheory.SW
