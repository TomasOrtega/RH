import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.AdPhysDiagSingle

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

/- English proof (translation)
Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Establish `hv : v = ∑ x, v x • Pi.single x (1 : ℂ)`. Use function extensionality and compare the values at `z`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `conv_lhs => rw [hv]`.

Simplify using `[cpV, cpFock, LinearMap.sum_apply, Finset.sum_mul]`.
-/
theorem cpV_eq_sum (v : Fin n × Fin n → ℂ) : cpV v = ∑ x, v x • cpFock (n := n) x.1 x.2 := by
  refine LinearMap.ext fun y => ?_
  have hv : v = ∑ x, v x • Pi.single x (1 : ℂ) := by
    funext z
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [cpV, cpFock, LinearMap.sum_apply, Finset.sum_mul]

/- English proof (translation)
Rewrite using `[cmV, dualV, map_sum]`. Simplify using `only [map_smul]`. Both sides reduce to the same expression.
-/
theorem cmV_eq_sum (v : Fin n × Fin n → ℂ) : cmV v = ∑ x, star (v x) • cmFock (n := n) x.1 x.2 := by
  rw [cmV, dualV, map_sum]
  simp only [map_smul]
  rfl

/- English proof (translation)
Rewrite using `[cmV_eq_sum, cpV_eq_sum, map_sum, map_sum, Matrix.conjTranspose_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, Matrix.conjTranspose_smul, lf_toMatrix_cm, lf_toMatrix_cp, fockMatrix_conjTranspose_eq_transpose]`.
-/
theorem toMatrix_cmV (v : Fin n × Fin n → ℂ) :
    LinearMap.toMatrix (fockBasis n) (fockBasis n) (cmV v) =
      (LinearMap.toMatrix (fockBasis n) (fockBasis n) (cpV v))ᴴ := by
  rw [cmV_eq_sum, cpV_eq_sum, map_sum, map_sum, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, map_smul, Matrix.conjTranspose_smul, lf_toMatrix_cm, lf_toMatrix_cp, fockMatrix_conjTranspose_eq_transpose]

/- English proof (translation)
Establish `hkk : k * kᴴ = 1`. Use `hk.1` as an intermediate fact. Rewrite `this` using `[Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose]`. Conclude with `this`. Rewrite using `[← LinearMap.comp_apply, ← adPhys_mul hk (kset_conjTranspose hk), hkk]`.

Simplify using `[adPhys, adMat_one]`.
-/
theorem adPhys_kkH {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (w : Fin n × Fin n → ℂ) :
    adPhys ε k (adPhys ε kᴴ w) = w := by
  have hkk : k * kᴴ = 1 := by
    have := hk.1
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose] at this
    exact this
  rw [← LinearMap.comp_apply, ← adPhys_mul hk (kset_conjTranspose hk), hkk]
  simp [adPhys, adMat_one]

/- English proof (translation)
Establish `h` using `congrArg (LinearMap.toMatrix (fockBasis n) (fockBasis n)) (ff_cmV hk (adPhys ε kᴴ w))`. Rewrite `h` using `[LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, adPhys_kkH hk, toMatrix_cmV, toMatrix_cmV]`. Establish `h2` using `congrArg Matrix.conjTranspose h`. Rewrite `h2` using `[conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_conjTranspose]`. Conclude with `h2`.
-/
theorem ffMat_H_cp {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (w : Fin n × Fin n → ℂ) :
    LinearMap.toMatrix (fockBasis n) (fockBasis n) (cpV (adPhys ε kᴴ w)) * (ffMat ε k)ᴴ =
      (ffMat ε k)ᴴ * LinearMap.toMatrix (fockBasis n) (fockBasis n) (cpV w) := by
  have h := congrArg (LinearMap.toMatrix (fockBasis n) (fockBasis n)) (ff_cmV hk (adPhys ε kᴴ w))
  rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, adPhys_kkH hk, toMatrix_cmV, toMatrix_cmV] at h
  have h2 := congrArg Matrix.conjTranspose h
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_conjTranspose] at h2
  exact h2

/- English proof (translation)
Establish `h` using `congrArg (Matrix.toLin (fockBasis n) (fockBasis n)) (ffMat_H_cp hk w)`. Rewrite `h` using `[Matrix.toLin_mul (v₁ := fockBasis n) (v₂ := fockBasis n) (v₃ := fockBasis n), Matrix.toLin_mul (v₁ := fockBasis n) (v₂ := fockBasis n) (v₃ := fockBasis n), Matrix.toLin_toMatrix, Matrix.toLin_toMatrix]`. Establish `h3` using `LinearMap.congr_fun h z`. Simplify using `only [LinearMap.comp_apply] at h3`. Conclude with `h3.symm`.
-/
theorem nH_cpV {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (w : Fin n × Fin n → ℂ) (z : Fock n) :
    Matrix.toLin (fockBasis n) (fockBasis n) (ffMat ε k)ᴴ (cpV w z) =
      cpV (adPhys ε kᴴ w) (Matrix.toLin (fockBasis n) (fockBasis n) (ffMat ε k)ᴴ z) := by
  have h := congrArg (Matrix.toLin (fockBasis n) (fockBasis n)) (ffMat_H_cp hk w)
  rw [Matrix.toLin_mul (v₁ := fockBasis n) (v₂ := fockBasis n) (v₃ := fockBasis n),
    Matrix.toLin_mul (v₁ := fockBasis n) (v₂ := fockBasis n) (v₃ := fockBasis n),
    Matrix.toLin_toMatrix, Matrix.toLin_toMatrix] at h
  have h3 := LinearMap.congr_fun h z
  simp only [LinearMap.comp_apply] at h3
  exact h3.symm

/- English proof (translation)
Establish `: (ExteriorAlgebra.algebraMapInv (R` using `ℂ) (M := Fin n × Fin n → ℂ)).comp (ff ε k) = ExteriorAlgebra.algebraMapInv := by`. Apply `ExteriorAlgebra.hom_ext` to reduce the goal to its premises. Use `LinearMap.ext fun m => ?_` and prove the remaining obligations. Simplify using `[ff, ExteriorAlgebra.algebraMapInv]`. Conclude with `AlgHom.congr_fun this x`.
-/
theorem algebraMapInv_ff (k : Matrix (Fin n) (Fin n) ℂ) (x : Fock n) :
    ExteriorAlgebra.algebraMapInv (ff ε k x) = ExteriorAlgebra.algebraMapInv x := by
  have : (ExteriorAlgebra.algebraMapInv (R := ℂ) (M := Fin n × Fin n → ℂ)).comp (ff ε k) =
      ExteriorAlgebra.algebraMapInv := by
    apply ExteriorAlgebra.hom_ext
    refine LinearMap.ext fun m => ?_
    simp [ff, ExteriorAlgebra.algebraMapInv]
  exact AlgHom.congr_fun this x

/- English proof (translation)
Substitute `hp` using the available equality. Conclude with `ExteriorAlgebra.ιMulti_zero_apply v`.
-/
theorem ιMulti_card_zero (p : ℕ) (v : Fin p → (Fin n × Fin n → ℂ)) (hp : p = 0) :
    ExteriorAlgebra.ιMulti ℂ p v = 1 := by
  subst hp
  exact ExteriorAlgebra.ιMulti_zero_apply v

/- English proof (translation)
Consider the cases of `p with`. Consider the case `zero => omega`. Consider the case `succ p`. Rewrite using `[ExteriorAlgebra.ιMulti_succ_apply, map_mul]`. Simplify using `[ExteriorAlgebra.algebraMapInv]`.
-/
theorem algebraMapInv_ιMulti_pos (p : ℕ) (v : Fin p → (Fin n × Fin n → ℂ)) (hp : 0 < p) :
    ExteriorAlgebra.algebraMapInv (ExteriorAlgebra.ιMulti ℂ p v) = 0 := by
  cases p with
  | zero => omega
  | succ p =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul]
    simp [ExteriorAlgebra.algebraMapInv]

/- English proof (translation)
Establish `: Finsupp.lapply ∅ ∘ₗ (fockBasis n).repr.toLinearMap = (ExteriorAlgebra.algebraMapInv (R` using `ℂ) (M := Fin n × Fin n → ℂ)).toLinearMap := by`. Use `(fockBasis n).ext fun T => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply, AlgHom.toLinearMap_apply]`. Rewrite using `[fockBasis_eq]`. Break down `Nat.eq_zero_or_pos T.card with h | h` into its components or cases.

Establish `hT : T = ∅` using `Finset.card_eq_zero.mp h`. Rewrite using `[ιMulti_card_zero _ _ h, map_one, hT, Finsupp.single_eq_same]`. Establish `hT : T ≠ ∅` using `Finset.nonempty_iff_ne_empty.mp (Finset.card_pos.mp h)`. Rewrite using `[algebraMapInv_ιMulti_pos _ _ h]`. Simplify using `[hT]`.

Conclude with `LinearMap.congr_fun this x`.
-/
theorem repr_empty (x : Fock n) : (fockBasis n).repr x ∅ = ExteriorAlgebra.algebraMapInv x := by
  have : Finsupp.lapply ∅ ∘ₗ (fockBasis n).repr.toLinearMap =
      (ExteriorAlgebra.algebraMapInv (R := ℂ) (M := Fin n × Fin n → ℂ)).toLinearMap := by
    refine (fockBasis n).ext fun T => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply,
      AlgHom.toLinearMap_apply]
    rw [fockBasis_eq]
    rcases Nat.eq_zero_or_pos T.card with h | h
    · have hT : T = ∅ := Finset.card_eq_zero.mp h
      rw [ιMulti_card_zero _ _ h, map_one, hT, Finsupp.single_eq_same]
    · have hT : T ≠ ∅ := Finset.nonempty_iff_ne_empty.mp (Finset.card_pos.mp h)
      rw [algebraMapInv_ιMulti_pos _ _ h]
      simp [hT]
  exact LinearMap.congr_fun this x

/- English proof (translation)
Rewrite using `[ffMat, LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply, repr_empty, algebraMapInv_ff, ← repr_empty, Module.Basis.repr_self, Finsupp.single_apply]`.
-/
theorem ffMat_empty_row (k : Matrix (Fin n) (Fin n) ℂ) (T : Finset (Fin (n * n))) :
    ffMat ε k ∅ T = if T = ∅ then 1 else 0 := by
  rw [ffMat, LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply, repr_empty, algebraMapInv_ff, ← repr_empty,
    Module.Basis.repr_self, Finsupp.single_apply]

/- English proof (translation)
Establish `h1 : (1 : Fock n) = fockBasis n ∅`. Rewrite using `[fockBasis_eq, ιMulti_card_zero _ _ Finset.card_empty]`. Rewrite using `[h1, Matrix.toLin_self, Finset.sum_eq_single ∅]`. Simplify using `[conjTranspose_apply, ffMat_empty_row]`. Introduce `T _ hT`.

Simplify using `[conjTranspose_apply, ffMat_empty_row, hT]`. Simplify using the standard rewrite rules.
-/
theorem nH_one (k : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.toLin (fockBasis n) (fockBasis n) (ffMat ε k)ᴴ 1 = 1 := by
  have h1 : (1 : Fock n) = fockBasis n ∅ := by
    rw [fockBasis_eq, ιMulti_card_zero _ _ Finset.card_empty]
  rw [h1, Matrix.toLin_self, Finset.sum_eq_single ∅]
  · simp [conjTranspose_apply, ffMat_empty_row]
  · intro T _ hT
    simp [conjTranspose_apply, ffMat_empty_row, hT]
  · simp

/- English proof (translation)
Proceed by induction on `x using CliffordAlgebra.left_induction with`. Consider the case `algebraMap r`. Introduce `y`. Simplify using `[Algebra.algebraMap_eq_smul_one]`. Consider the case `add x x' hx hx'`.

Introduce `y`. Rewrite using `[add_mul, map_add, hx, hx', map_add, add_mul]`. Consider the case `ι_mul x m hx`. Introduce `y`. Establish `h` using `nH_cpV hk m (x * y)`.

Simplify using `only [cpV, LinearMap.mulLeft_apply] at h`. Rewrite using `[mul_assoc, h, hx, map_mul, ff, ExteriorAlgebra.map_apply_ι, mul_assoc]`.
-/
theorem nH_mul {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (x : Fock n) :
    ∀ y : Fock n, Matrix.toLin (fockBasis n) (fockBasis n) (ffMat ε k)ᴴ (x * y) =
      ff ε kᴴ x * Matrix.toLin (fockBasis n) (fockBasis n) (ffMat ε k)ᴴ y := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    intro y
    simp [Algebra.algebraMap_eq_smul_one]
  | add x x' hx hx' =>
    intro y
    rw [add_mul, map_add, hx, hx', map_add, add_mul]
  | ι_mul x m hx =>
    intro y
    have h := nH_cpV hk m (x * y)
    simp only [cpV, LinearMap.mulLeft_apply] at h
    rw [mul_assoc, h, hx, map_mul, ff, ExteriorAlgebra.map_apply_ι, mul_assoc]

/- English proof (translation)
Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Establish `h` using `nH_mul hk x 1`. Rewrite `h` using `[mul_one, nH_one, mul_one]`. Conclude with `h`.
-/
theorem nH_eq {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    Matrix.toLin (fockBasis n) (fockBasis n) (ffMat ε k)ᴴ = (ff ε kᴴ).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  have h := nH_mul hk x 1
  rw [mul_one, nH_one, mul_one] at h
  exact h

/- English proof (translation)
Rewrite using `[Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]`. Establish `h1 : (ffMat ε k)ᴴ = LinearMap.toMatrix (fockBasis n) (fockBasis n) (ff ε kᴴ).toLinearMap`. Rewrite using `[← nH_eq hk, LinearMap.toMatrix_toLin]`. Establish `hkk : kᴴ * k = 1`. Use `hk.1` as an intermediate fact.

Rewrite `this` using `[Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]`. Conclude with `this`. Establish `h2 : (ff ε kᴴ).toLinearMap * (ff ε k).toLinearMap = 1`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[Module.End.mul_apply, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, ← AlgHom.comp_apply, ← ff_mul (kset_conjTranspose hk) hk, hkk, ff_one]`.

Both sides reduce to the same expression. Rewrite using `[h1, ffMat, ← LinearMap.toMatrix_mul, h2, LinearMap.toMatrix_one]`.
-/
theorem ffMat_unitary {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    ffMat ε k ∈ Matrix.unitaryGroup (Finset (Fin (n * n))) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
  have h1 : (ffMat ε k)ᴴ = LinearMap.toMatrix (fockBasis n) (fockBasis n) (ff ε kᴴ).toLinearMap := by
    rw [← nH_eq hk, LinearMap.toMatrix_toLin]
  have hkk : kᴴ * k = 1 := by
    have := hk.1
    rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose] at this
    exact this
  have h2 : (ff ε kᴴ).toLinearMap * (ff ε k).toLinearMap = 1 := by
    refine LinearMap.ext fun x => ?_
    rw [Module.End.mul_apply, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, ← AlgHom.comp_apply,
      ← ff_mul (kset_conjTranspose hk) hk, hkk, ff_one]
    rfl
  rw [h1, ffMat, ← LinearMap.toMatrix_mul, h2, LinearMap.toMatrix_one]

end ReciprocityTheory.ChartRestriction.DS.TRGap
