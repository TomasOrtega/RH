import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnitsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MooreDeterminantEqUnramifiedMulPeriodStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIndependentFrobSolutionsCrisProofStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSecondKindMatrixMooreDetNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MooreDeterminantCrisPlusNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisPlusFrobeniusStableSubringInFilZeroStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.FLOne

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Establish `e : M = (Matrix.of fun i j => (⟨M i j, hM i j⟩ : S0 P)).map (S0 P).subtype` using `by ext; rfl`. Rewrite using `[e, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `Subtype.prop _`.
-/
theorem det_mem (M : Matrix n n P.R.BdR) (hM : ∀ i j, M i j ∈ Fil P 0) : M.det ∈ Fil P 0 := by
  have e : M = (Matrix.of fun i j => (⟨M i j, hM i j⟩ : S0 P)).map (S0 P).subtype := by ext; rfl
  rw [e, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact Subtype.prop _

/- English proof (translation)
Establish `e : M = (Matrix.of fun i j => (⟨M i j, hM i j⟩ : S0 P)).map (S0 P).subtype` using `by ext; rfl`. Rewrite using `[e, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]`. Conclude with `Subtype.prop _`.
-/
theorem adj_mem (M : Matrix n n P.R.BdR) (hM : ∀ i j, M i j ∈ Fil P 0) (i j : n) : M.adjugate i j ∈ Fil P 0 := by
  have e : M = (Matrix.of fun i j => (⟨M i j, hM i j⟩ : S0 P)).map (S0 P).subtype := by ext; rfl
  rw [e, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]
  exact Subtype.prop _

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Conclude with `Fil_sum fun k _ => Fil_mul_left (hA i k) (hB k j)`.
-/
theorem mul_mem (A B : Matrix n n P.R.BdR) (hA : ∀ i j, A i j ∈ Fil P 0) (hB : ∀ i j, B i j ∈ Fil P 0) (i j : n) :
    (A * B) i j ∈ Fil P 0 := by
  rw [Matrix.mul_apply]
  exact Fil_sum fun k _ => Fil_mul_left (hA i k) (hB k j)

/- English proof (translation)
Introduce `h`. Establish `h1 : (P.PD (botExt l)).ι (P.PD (botExt l)).t ∈ Fil P 1` using `(P.PD (botExt l)).mem_filtration_one`. Establish `h2` using `Fil_mul h1 h`. Rewrite `h2` using `[mul_one]`. Conclude with `(P.PD (botExt l)).not_mem_filtration_two h2`.
-/
theorem one_not_mem : (1 : P.R.BdR) ∉ Fil P 1 := by
  intro h
  have h1 : (P.PD (botExt l)).ι (P.PD (botExt l)).t ∈ Fil P 1 := (P.PD (botExt l)).mem_filtration_one
  have h2 := Fil_mul h1 h
  rw [mul_one] at h2
  exact (P.PD (botExt l)).not_mem_filtration_two h2

/- English proof (translation)
Establish `hu : IsUnit M.det` using `(Units.mkOfMulEqOne _ _ h).isUnit`. Use `⟨Matrix.nonsingInvUnit M hu, rfl, hM, fun i j => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(M⁻¹ : Matrix n n P.R.BdR) i j ∈ Fil P 0`. Establish `hi : Ring.inverse M.det = y`. Rewrite using `[← mul_one (Ring.inverse _), ← h, ← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]`.

Rewrite using `[Matrix.inv_def, hi, Matrix.smul_apply, smul_eq_mul]`. Conclude with `Fil_mul_left hy (adj_mem M hM i j)`.
-/
theorem unitM_of (M : Matrix n n P.R.BdR) (hM : ∀ i j, M i j ∈ Fil P 0) (y : P.R.BdR) (hy : y ∈ Fil P 0)
    (h : M.det * y = 1) : ∃ W : GL n P.R.BdR, (W : Matrix n n P.R.BdR) = M ∧ UnitM P W := by
  have hu : IsUnit M.det := (Units.mkOfMulEqOne _ _ h).isUnit
  refine ⟨Matrix.nonsingInvUnit M hu, rfl, hM, fun i j => ?_⟩
  change (M⁻¹ : Matrix n n P.R.BdR) i j ∈ Fil P 0
  have hi : Ring.inverse M.det = y := by
    rw [← mul_one (Ring.inverse _), ← h, ← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]
  rw [Matrix.inv_def, hi, Matrix.smul_apply, smul_eq_mul]
  exact Fil_mul_left hy (adj_mem M hM i j)

end GlobalTheory.PMon.FLOne

namespace GlobalTheory.PMon.FLOne

open Matrix

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Take `⟨y, hy, hky⟩` from `(GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T).2.2.2.1 (v k) (hv k) hk`. Establish `e : (M.adjugate *ᵥ (M *ᵥ v)) k = M.det * v k`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.adjugate_mul]`. Simplify using `[Matrix.smul_mulVec]`. Establish `h3 : (M.adjugate *ᵥ (M *ᵥ v)) k ∈ Fil P 1` using `by show ∑ j, M.adjugate k j * (M *ᵥ v) j ∈ Fil P 1`.

Conclude with `Fil_sum fun j _ => Fil_mul_left (adj_mem M hM k j) (h j)`. Establish `e2 : M.det = M.det * v k * y` using `by rw [mul_assoc, hky, mul_one]`. Rewrite using `[e2, ← e]`. Conclude with `Fil_mul_right h3 hy`.
-/
theorem det_mem_one {AI : LocAinf l P} (T : LocTied l P AI) (M : Matrix n n P.R.BdR) (v : n → P.R.BdR)
    (hM : ∀ i j, M i j ∈ Fil P 0) (hv : ∀ j, v j ∈ Fil P 0) (k : n) (hk : v k ∉ Fil P 1)
    (h : ∀ i, (M *ᵥ v) i ∈ Fil P 1) : M.det ∈ Fil P 1 := by
  obtain ⟨y, hy, hky⟩ := (GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T).2.2.2.1 (v k) (hv k) hk
  have e : (M.adjugate *ᵥ (M *ᵥ v)) k = M.det * v k := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul]
    simp [Matrix.smul_mulVec]
  have h3 : (M.adjugate *ᵥ (M *ᵥ v)) k ∈ Fil P 1 := by
    show ∑ j, M.adjugate k j * (M *ᵥ v) j ∈ Fil P 1
    exact Fil_sum fun j _ => Fil_mul_left (adj_mem M hM k j) (h j)
  have e2 : M.det = M.det * v k * y := by rw [mul_assoc, hky, mul_one]
  rw [e2, ← e]
  exact Fil_mul_right h3 hy

/- English proof (translation)
Rewrite using `[← Matrix.det_transpose]`. Use `det_mem_one T Mᵀ v (fun i j => hM j i) hv k hk fun i => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_transpose]`. Conclude with `h i`.
-/
theorem det_mem_one' {AI : LocAinf l P} (T : LocTied l P AI) (M : Matrix n n P.R.BdR) (v : n → P.R.BdR)
    (hM : ∀ i j, M i j ∈ Fil P 0) (hv : ∀ j, v j ∈ Fil P 0) (k : n) (hk : v k ∉ Fil P 1)
    (h : ∀ j, (v ᵥ* M) j ∈ Fil P 1) : M.det ∈ Fil P 1 := by
  rw [← Matrix.det_transpose]
  refine det_mem_one T Mᵀ v (fun i j => hM j i) hv k hk fun i => ?_
  rw [Matrix.mulVec_transpose]
  exact h i

end GlobalTheory.PMon.FLOne

namespace GlobalTheory.PMon.FLOne

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Establish `hφA : IsUnit (A.map φ).det`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `hA.map φ`. Establish `e1 : (A⁻¹).map φ = (A.map φ)⁻¹`. Use `(Matrix.inv_eq_left_inv ?_).symm` and prove the remaining obligations.

Rewrite using `[← Matrix.map_mul, Matrix.nonsing_inv_mul _ hA, Matrix.map_one _ (map_zero φ) (map_one φ)]`. Establish `e2 : C * B = A.map φ * (A⁻¹ * B)`. Rewrite using `[hA', Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hA]`. Rewrite using `[Matrix.map_mul, e1, hB, e2, Matrix.nonsing_inv_mul_cancel_left _ _ hφA]`.
-/
theorem inv_mul_fixed {R : Type} [CommRing R] (φ : R →+* R) (A B C : Matrix n n R)
    (hA : IsUnit A.det) (hA' : A.map φ = C * A) (hB : B.map φ = C * B) : (A⁻¹ * B).map φ = A⁻¹ * B := by
  have hφA : IsUnit (A.map φ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hA.map φ
  have e1 : (A⁻¹).map φ = (A.map φ)⁻¹ := by
    refine (Matrix.inv_eq_left_inv ?_).symm
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hA, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have e2 : C * B = A.map φ * (A⁻¹ * B) := by
    rw [hA', Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  rw [Matrix.map_mul, e1, hB, e2, Matrix.nonsing_inv_mul_cancel_left _ _ hφA]

def comp (R : Type) [CommRing R] (c : R) (h : ℕ) : Matrix (Fin h) (Fin h) R :=
  Matrix.of fun i k => if (i : ℕ) + 1 = k then 1 else if (i : ℕ) + 1 = h ∧ (k : ℕ) = 0 then c else 0

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, ← Function.iterate_succ_apply' φ]`. Distinguish the cases in `hi : (i : ℕ) + 1 < h`. Rewrite using `[Finset.sum_eq_single ⟨(i : ℕ) + 1, hi⟩]`. Simplify using `[comp]`.

Introduce `k _ hk`. Establish `: (i : ℕ) + 1 ≠ k` using `fun e => hk (Fin.ext e.symm)`. Simplify using `[comp, this]`. Introduce `_ h0`. Use linear arithmetic over natural numbers and integers.

Simplify using the standard rewrite rules. Establish `hi' : (i : ℕ) + 1 = h` using `by omega`. Rewrite using `[Finset.sum_eq_single ⟨0, by omega⟩]`. Simplify using `[comp, hi', ha]`. Introduce `h0`.

Use linear arithmetic over natural numbers and integers. Introduce `k _ hk`. Establish `h1 : (i : ℕ) + 1 ≠ k` using `by omega`. Establish `h2 : (k : ℕ) ≠ 0` using `fun e => hk (Fin.ext e)`. Simplify using `[comp, h1, h2]`.

Simplify using the standard rewrite rules.
-/
theorem moore_map {R : Type} [CommRing R] (φ : R →+* R) (c : R) (h : ℕ) (a : Fin h → R)
    (ha : ∀ j, φ^[h] (a j) = c * a j) :
    (Matrix.of fun i j : Fin h => φ^[i] (a j)).map φ = comp R c h * Matrix.of fun i j : Fin h => φ^[i] (a j) := by
  ext i j
  rw [Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, ← Function.iterate_succ_apply' φ]
  by_cases hi : (i : ℕ) + 1 < h
  · rw [Finset.sum_eq_single ⟨(i : ℕ) + 1, hi⟩]
    · simp [comp]
    · intro k _ hk
      have : (i : ℕ) + 1 ≠ k := fun e => hk (Fin.ext e.symm)
      simp [comp, this]
      intro _ h0
      omega
    · simp
  · have hi' : (i : ℕ) + 1 = h := by omega
    rw [Finset.sum_eq_single ⟨0, by omega⟩]
    · simp [comp, hi', ha]
      intro h0
      omega
    · intro k _ hk
      have h1 : (i : ℕ) + 1 ≠ k := by omega
      have h2 : (k : ℕ) ≠ 0 := fun e => hk (Fin.ext e)
      simp [comp, h1, h2]
    · simp
end GlobalTheory.PMon.FLOne

namespace GlobalTheory.PMon.FLOne

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Use `(Matrix.inv_eq_left_inv ?_).symm` and prove the remaining obligations. Rewrite using `[← Matrix.map_mul, Matrix.nonsing_inv_mul _ hA, Matrix.map_one _ (map_zero f) (map_one f)]`.
-/
theorem map_inv' {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (A : Matrix n n R) (hA : IsUnit A.det) :
    (A⁻¹).map f = (A.map f)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hA, Matrix.map_one _ (map_zero f) (map_one f)]

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

/- English proof (translation)
Use `((GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T).2.2.1 1 (-1) x).1 hx` as an intermediate fact. Simplify using `using this`.
-/
theorem tz_inv_mem {AI : LocAinf l P} (T : LocTied l P AI) {x : P.R.BdR} (hx : x ∈ Fil P 1) :
    tz P (-1) * x ∈ Fil P 0 := by
  have := ((GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T).2.2.1 1 (-1) x).1 hx
  simpa using this

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR]`. Both sides reduce to the same expression.
-/
theorem kd_alg' (q : ℚ_[l]) : kd P (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q) = algebraMap ℚ_[l] P.R.BdR q := by
  rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR]; rfl

/- English proof (translation)
Rewrite using `[← map_mul, mul_inv_cancel₀ hκ, map_one]`.
-/
theorem kd_mul_inv {κ : ↥(MaximalUnramifiedExtension l)} (hκ : κ ≠ 0) : kd P κ * kd P κ⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel₀ hκ, map_one]

/- English proof (translation)
The claim follows from `((Ne.isUnit hκ).map _).mul (isUnit_tB P)`.
-/
theorem isUnit_algebraMap_unramified_mul_period {κ : ↥(MaximalUnramifiedExtension l)} (hκ : κ ≠ 0) : IsUnit (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B κ * P.tB) :=
  ((Ne.isUnit hκ).map _).mul (isUnit_tB P)

end GlobalTheory.PMon.FLOne

namespace GlobalTheory.PMon.FLOne

open Matrix

/- English proof (translation)
Introduce `l _ P AI T n _ _ U x y hxy hU hc`. Take `⟨x1, x2⟩` from `x`. Take `⟨y1, y2⟩` from `y`. Take `rfl : x1 = 0` from `Subsingleton.elim _ _`. Take `rfl : y1 = 0` from `Subsingleton.elim _ _`.

Establish `h2 : x2 ≠ y2` using `fun e => hxy (by rw [e])`. Use `set h := Fintype.card n with hhdef`. Establish `hh : 2 ≤ h` using `Fintype.one_lt_card_iff.2 ⟨x2, y2, h2⟩`. Set `e : n ≃ Fin h` to `Fintype.equivFin n`. Use `set U0 : Matrix n n P.R.BdR := (U 0 : Matrix n n P.R.BdR) with hU0`.

Establish `hI` using `GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T`. Set `lam : Fin h → P.R.BdR` to `fun k => U0 (e.symm k) x2`. Establish `hlam0 : ∀ k, lam k ∈ Fil P 0` using `fun k => (hU 0).1 _ _`. Establish `hind : ∀ c : Fin h → ℚ_[l], ∑ j, c j • lam j ∈ Fil P 1 → c = 0`. Introduce `c hcs`.

Establish `hc'` using `hc (fun i => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c (e i))) (fun i => fr_q 1 _) (by`. Establish `: ∑ i, kd P (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c (e i))) * (U (0 : Fin 1) : Matrix n n P.R.BdR) i x2 = ∑ j, c j • lam j`. Use `Fintype.sum_equiv e _ _ fun i => ?_` and prove the remaining obligations. Simplify using `[lam, kd_alg', Algebra.smul_def, hU0]`. Rewrite using `[this]`.

Conclude with `hcs)`. Use function extensionality and compare the values at `k`. Use `congrFun hc' (e.symm k)` as an intermediate fact. Simplify using `using this`. Establish `hunit : ∃ k, lam k ∉ Fil P 1`.

Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Use `hind (Pi.single ⟨0, by omega⟩ 1) (Fil_sum fun j _ => by` as an intermediate fact. Rewrite using `[Algebra.smul_def]`. Conclude with `Fil_mul_left (q_mem_Fil P _) (hne j))`.

Simplify using `using congrFun this ⟨0, by omega⟩`. Take `⟨a, ha_phi, ha_fil, ha_sum, ha_det⟩` from `GlobalTheory.T.exists_secondKind_matrix_moore_det_ne_zero l P AI T h hh lam hlam0 hind`. Establish `hdetι : P.ιB (Matrix.of fun i j : Fin h => P.φB^[i] (a j)).det ∈ Fil P 1`. Take `⟨k, hk⟩` from `hunit`. Express the relevant statement in the definitionally equal form `(P.ιB : P.R.B →+* P.R.BdR) _ ∈ _`.

Rewrite using `[RingHom.map_det]`. Use `det_mem_one T _ lam (fun i j => ha_fil i j) hlam0 k hk fun i => ?_` and prove the remaining obligations. Use `ha_sum i` as an intermediate fact. Simplify using `only [mulVec, dotProduct]`. Use `this using 2 with j` and compare the differences between its conclusion and the goal.

Rewrite using `[mul_comm]`. Both sides reduce to the same expression. Take `⟨κ, hκ, hdetA⟩` from `GlobalTheory.T.mooreDeterminant_eq_unramified_mul_period l P AI T h (by omega) a ha_phi ha_fil ha_det hdetι`. Use `set Ma : Matrix (Fin h) (Fin h) P.R.B := Matrix.of fun i j : Fin h => P.φB^[i] (a j) with hMa`. Use `set A : Matrix n n P.R.B := Ma.submatrix e e with hA`.

Establish `hAdet : A.det = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B κ * P.tB` using `by rw [hA, Matrix.det_submatrix_equiv_self, hdetA]`. Establish `hAu : IsUnit A.det` using `by rw [hAdet]; exact isUnit_algebraMap_unramified_mul_period hκ`. Use `set Dx : Matrix n n P.R.BdR := diagonal fun j => if j = x2 then tz P (-1) else 1 with hDx`. Use `set Um : Matrix n n P.R.BdR := A.map P.ιB * U0 * Dx with hUm`. Establish `hAU0 : ∀ i j, (A.map P.ιB * U0) i j ∈ Fil P 0` using `mul_mem _ _ (fun i j => ha_fil _ _) (hU 0).1`.

Establish `hAU1 : ∀ i, (A.map P.ιB * U0) i x2 ∈ Fil P 1`. Introduce `i`. Use `ha_sum (e i)` as an intermediate fact. Rewrite using `[Matrix.mul_apply]`. Use `this using 1` and compare the differences between its conclusion and the goal.

Use `Fintype.sum_equiv e _ _ fun j => ?_` and prove the remaining obligations. Simplify using `[lam, hA, hMa, ev, mul_comm]`. Establish `hUm0 : ∀ i j, Um i j ∈ Fil P 0`. Introduce `i j`. Rewrite using `[hUm, Matrix.mul_diagonal]`.

Distinguish the cases in `hj : j = x2`. Substitute `hj` using the available equality. Rewrite using `[if_pos rfl, mul_comm]`. Conclude with `tz_inv_mem T (hAU1 i)`. Rewrite using `[if_neg hj, mul_one]`.

Conclude with `hAU0 i j`. Establish `hUmdet : Um.det = kd P κ * U0.det`. Establish `hdι : (A.map P.ιB).det = P.ιB A.det` using `((P.ιB : P.R.B →+* P.R.BdR).map_det A).symm`. Establish `hDxd : Dx.det = tz P (-1)`. Rewrite using `[hDx, det_diagonal, Finset.prod_ite_eq']`.

Simplify using the standard rewrite rules. Establish `ht : tz P 1 * tz P (-1) = 1` using `by rw [← tz_add]; simp [tz_zero]`. Rewrite using `[hUm, det_mul, det_mul, hdι, hDxd, hAdet, map_mul, iota_kur, ← tz_one]`. Take the linear combination `(kd P κ * U0.det) * ht`. Establish `hU0inv : U0 * ((U 0)⁻¹ : GL n P.R.BdR) = 1` using `by rw [hU0, ← Units.val_mul, mul_inv_cancel, Units.val_one]`.

Take `⟨U', hU'eq, hU'u⟩` from `unitM_of Um hUm0 (kd P κ⁻¹ * Matrix.det (((U 0)⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR)) (Fil_mul_left (kd_mem_Fil P _) (det_mem _ (hU 0).2)) (by`. Rewrite using `[hUmdet]`. Establish `h1` using `kd_mul_inv (P := P) hκ`. Establish `h2 : U0.det * (((U 0)⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR).det = 1` using `by rw [← det_mul, hU0inv, det_one]`. Take the linear combination `(U0.det * (((U 0)⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR).det) * h1 + h2)`.

Use `set V : Matrix n n P.R.BdR := ((U'⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR) with hV`. Establish `hVU : V * Um = 1` using `by rw [hV, ← hU'eq, ← Units.val_mul, inv_mul_cancel, Units.val_one]`. Set `μ : Fin h → P.R.BdR` to `fun k => V y2 (e.symm k)`. Establish `hμ0 : ∀ k, μ k ∈ Fil P 0` using `fun k => hU'u.2 _ _`. Establish `hμu : ∃ k, μ k ∉ Fil P 1`.

Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `h1 : (V * Um) y2 y2 ∈ Fil P 1`. Rewrite using `[Matrix.mul_apply]`. Conclude with `Fil_sum fun j _ => Fil_mul_right (by simpa [μ] using hne (e j)) (hUm0 j y2)`.

Rewrite `h1` using `[hVU, Matrix.one_apply_eq]`. Conclude with `one_not_mem h1`. Take `⟨b, hb_plus, hb_phi, hb_ind, hb_sum⟩` from `GlobalTheory.T.existsIndependentFrobSolutionsCris_proof l P AI T h hh μ hμ0 hμu`. Establish `hb_det` using `GlobalTheory.T.mooreDeterminant_crisPlus_ne_zero l P AI T h h le_rfl b hb_plus hb_phi hb_ind`. Establish `hb_fil : ∀ (i : ℕ) j, ev P i (b j) ∈ Fil P 0` using `fun i j => (GlobalTheory.T.bcrisPlus_frobeniusStable_subring_in_filZero l P AI T).2.1 _ (hb_plus j) i`.

Establish `hdetιb : P.ιB (Matrix.of fun i j : Fin h => P.φB^[i] (b j)).det ∈ Fil P 1`. Take `⟨k, hk⟩` from `hμu`. Express the relevant statement in the definitionally equal form `(P.ιB : P.R.B →+* P.R.BdR) _ ∈ _`. Rewrite using `[RingHom.map_det]`. Use `det_mem_one' T _ μ (fun i j => hb_fil i j) hμ0 k hk fun j => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `∑ i, μ i * ev P i (b j) ∈ Fil P 1`. Conclude with `hb_sum j`. Take `⟨κ', hκ', hdetB⟩` from `GlobalTheory.T.mooreDeterminant_eq_unramified_mul_period l P AI T h (by omega) b hb_phi hb_fil hb_det hdetιb`. Use `set Mb : Matrix (Fin h) (Fin h) P.R.B := Matrix.of fun i j : Fin h => P.φB^[i] (b j) with hMb`. Use `set Bm : Matrix n n P.R.B := Mb.submatrix e e with hBm`.

Establish `hBdet : Bm.det = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B κ' * P.tB` using `by rw [hBm, Matrix.det_submatrix_equiv_self, hdetB]`. Establish `hBu : IsUnit Bm.det` using `by rw [hBdet]; exact isUnit_algebraMap_unramified_mul_period hκ'`. Use `set Dy : Matrix n n P.R.BdR := diagonal fun j => if j = y2 then tz P (-1) else 1 with hDy`. Use `set X : Matrix n n P.R.BdR := V * Bm.map P.ιB with hX`. Establish `hX0 : ∀ i j, X i j ∈ Fil P 0` using `mul_mem _ _ hU'u.2 (fun i j => hb_fil _ _)`.

Establish `hX1 : ∀ j, X y2 j ∈ Fil P 1`. Introduce `j`. Use `hb_sum (e j)` as an intermediate fact. Rewrite using `[hX, Matrix.mul_apply]`. Use `this using 1` and compare the differences between its conclusion and the goal.

Use `Fintype.sum_equiv e _ _ fun i => ?_` and prove the remaining obligations. Simplify using `[μ, hBm, hMb, ev]`. Use `set Wm : Matrix n n P.R.BdR := Dy * X with hWm`. Establish `hWm0 : ∀ i j, Wm i j ∈ Fil P 0`. Introduce `i j`.

Rewrite using `[hWm, Matrix.diagonal_mul]`. Distinguish the cases in `hi : i = y2`. Substitute `hi` using the available equality. Rewrite using `[if_pos rfl]`. Conclude with `tz_inv_mem T (hX1 j)`.

Rewrite using `[if_neg hi, one_mul]`. Conclude with `hX0 i j`. Establish `hVUm : V.det * Um.det = 1` using `by rw [← det_mul, hVU, det_one]`. Establish `ht : tz P (-1) * tz P 1 = 1` using `by rw [← tz_add]; simp [tz_zero]`. Establish `hWmdet : Wm.det = kd P κ' * V.det`.

Establish `hdι : (Bm.map P.ιB).det = P.ιB Bm.det` using `((P.ιB : P.R.B →+* P.R.BdR).map_det Bm).symm`. Establish `hDyd : Dy.det = tz P (-1)`. Rewrite using `[hDy, det_diagonal, Finset.prod_ite_eq']`. Simplify using the standard rewrite rules. Rewrite using `[hWm, hX, det_mul, det_mul, hdι, hDyd, hBdet, map_mul, iota_kur, ← tz_one]`.

Take the linear combination `(kd P κ' * V.det) * ht`. Take `⟨W, hWeq, hWu⟩` from `unitM_of Wm hWm0 (kd P κ'⁻¹ * Um.det) (Fil_mul_left (kd_mem_Fil P _) (det_mem _ hUm0)) (by`. Rewrite using `[hWmdet]`. Establish `h1` using `kd_mul_inv (P := P) hκ'`. Take the linear combination `(V.det * Um.det) * h1 + hVUm)`.

Establish `hRu : IsUnit (A⁻¹ * Bm).det` using `by rw [det_mul]; exact (isUnit_nonsing_inv_det A hAu).mul hBu`. Use `⟨Matrix.nonsingInvUnit (A⁻¹ * Bm) hRu, fun i j => ?_, fun m => ?_⟩` and prove the remaining obligations. Use `set C : Matrix n n P.R.B := (comp P.R.B (l : P.R.B) h).submatrix e e`. Establish `hMa'` using `moore_map (P.φB : P.R.B →+* P.R.B) (l : P.R.B) h a ha_phi`. Establish `hMb'` using `moore_map (P.φB : P.R.B →+* P.R.B) (l : P.R.B) h b hb_phi`.

Establish `hA' : A.map (P.φB : P.R.B →+* P.R.B) = C * A`. Rewrite using `[hA, ← Matrix.submatrix_map]`. Conclude with `(congrArg (fun M => Matrix.submatrix M e e) hMa').trans (Matrix.submatrix_mul_equiv _ _ _ e _).symm`. Establish `hB' : Bm.map (P.φB : P.R.B →+* P.R.B) = C * Bm`. Rewrite using `[hBm, ← Matrix.submatrix_map]`.

Conclude with `(congrArg (fun M => Matrix.submatrix M e e) hMb').trans (Matrix.submatrix_mul_equiv _ _ _ e _).symm`. Use `congrFun (congrFun (inv_mul_fixed (P.φB : P.R.B →+* P.R.B) A Bm C hAu hA' hB') i) j` as an intermediate fact. Conclude with `this`. Take `rfl : m = 0` from `Subsingleton.elim _ _`. Use `⟨W, hWu, ?_⟩` and prove the remaining obligations.

Establish `hev : ev P ((0 : Fin 1) : ℕ) = P.ιB` using `funext fun _ => rfl`. Establish `hιAu : IsUnit (A.map P.ιB).det`. Establish `h` using `hAu.map (P.ιB : P.R.B →+* P.R.BdR)`. Rewrite `h` using `[RingHom.map_det]`. Conclude with `h`.

Establish `hDε : diagonal (fun j => tz P (eps ((0 : Fin 1), x2) ((0 : Fin 1), y2) ((0 : Fin 1), j))) * Dy = Dx`. Rewrite using `[hDy, hDx, diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hjx : j = x2`.

Substitute `hjx` using the available equality. Simplify using `[eps, h2]`. Distinguish the cases in `hjy : j = y2`. Substitute `hjy` using the available equality. Simplify using `[eps, hjx, Ne.symm hjx]`.

Rewrite using `[mul_comm]`. Conclude with `ht`. Simplify using `[eps, hjx, hjy, tz_zero]`. Establish `hUmV : Um * V = 1` using `mul_eq_one_comm.1 hVU`. Express the relevant statement in the definitionally equal form `(A⁻¹ * Bm).map (ev P ((0 : Fin 1) : ℕ)) = U0 * _ * (W : Matrix n n P.R.BdR)`.

Establish `hinv : (A⁻¹).map P.ιB = (A.map P.ιB)⁻¹` using `map_inv' (P.ιB : P.R.B →+* P.R.BdR) A hAu`. Rewrite using `[hev, hWeq, Matrix.map_mul, hinv]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hUmV, Matrix.mul_one]`. Use `_ = U0 * Dx * V * Bm.map P.ιB := by`.

Rewrite using `[hUm, Matrix.mul_assoc (A.map P.ιB), Matrix.mul_assoc (A.map P.ιB), ← Matrix.mul_assoc (A.map P.ιB)⁻¹, Matrix.nonsing_inv_mul _ hιAu, Matrix.one_mul]`. Use `_ = _ := by`. Rewrite using `[hWm, hX, ← hDε]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem flAt_one : FLAt 1 := by
  intro l _ P AI T n _ _ U x y hxy hU hc
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  obtain rfl : x1 = 0 := Subsingleton.elim _ _
  obtain rfl : y1 = 0 := Subsingleton.elim _ _
  have h2 : x2 ≠ y2 := fun e => hxy (by rw [e])
  set h := Fintype.card n with hhdef
  have hh : 2 ≤ h := Fintype.one_lt_card_iff.2 ⟨x2, y2, h2⟩
  let e : n ≃ Fin h := Fintype.equivFin n
  set U0 : Matrix n n P.R.BdR := (U 0 : Matrix n n P.R.BdR) with hU0
  have hI := GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T

  let lam : Fin h → P.R.BdR := fun k => U0 (e.symm k) x2
  have hlam0 : ∀ k, lam k ∈ Fil P 0 := fun k => (hU 0).1 _ _
  have hind : ∀ c : Fin h → ℚ_[l], ∑ j, c j • lam j ∈ Fil P 1 → c = 0 := by
    intro c hcs
    have hc' := hc (fun i => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c (e i))) (fun i => fr_q 1 _) (by
      have : ∑ i, kd P (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c (e i))) * (U (0 : Fin 1) : Matrix n n P.R.BdR) i x2 =
          ∑ j, c j • lam j := by
        refine Fintype.sum_equiv e _ _ fun i => ?_
        simp [lam, kd_alg', Algebra.smul_def, hU0]
      rw [this]; exact hcs)
    funext k
    have := congrFun hc' (e.symm k)
    simpa using this
  have hunit : ∃ k, lam k ∉ Fil P 1 := by
    by_contra hne
    push_neg at hne
    have := hind (Pi.single ⟨0, by omega⟩ 1) (Fil_sum fun j _ => by
      rw [Algebra.smul_def]; exact Fil_mul_left (q_mem_Fil P _) (hne j))
    simpa using congrFun this ⟨0, by omega⟩
  obtain ⟨a, ha_phi, ha_fil, ha_sum, ha_det⟩ := GlobalTheory.T.exists_secondKind_matrix_moore_det_ne_zero l P AI T h hh lam hlam0 hind
  have hdetι : P.ιB (Matrix.of fun i j : Fin h => P.φB^[i] (a j)).det ∈ Fil P 1 := by
    obtain ⟨k, hk⟩ := hunit
    change (P.ιB : P.R.B →+* P.R.BdR) _ ∈ _
    rw [RingHom.map_det]
    refine det_mem_one T _ lam (fun i j => ha_fil i j) hlam0 k hk fun i => ?_
    have := ha_sum i
    simp only [mulVec, dotProduct]
    convert this using 2 with j
    rw [mul_comm]; rfl
  obtain ⟨κ, hκ, hdetA⟩ := GlobalTheory.T.mooreDeterminant_eq_unramified_mul_period l P AI T h (by omega) a ha_phi ha_fil ha_det hdetι

  set Ma : Matrix (Fin h) (Fin h) P.R.B := Matrix.of fun i j : Fin h => P.φB^[i] (a j) with hMa
  set A : Matrix n n P.R.B := Ma.submatrix e e with hA
  have hAdet : A.det = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B κ * P.tB := by rw [hA, Matrix.det_submatrix_equiv_self, hdetA]
  have hAu : IsUnit A.det := by rw [hAdet]; exact isUnit_algebraMap_unramified_mul_period hκ
  set Dx : Matrix n n P.R.BdR := diagonal fun j => if j = x2 then tz P (-1) else 1 with hDx
  set Um : Matrix n n P.R.BdR := A.map P.ιB * U0 * Dx with hUm
  have hAU0 : ∀ i j, (A.map P.ιB * U0) i j ∈ Fil P 0 := mul_mem _ _ (fun i j => ha_fil _ _) (hU 0).1
  have hAU1 : ∀ i, (A.map P.ιB * U0) i x2 ∈ Fil P 1 := by
    intro i
    have := ha_sum (e i)
    rw [Matrix.mul_apply]
    convert this using 1
    refine Fintype.sum_equiv e _ _ fun j => ?_
    simp [lam, hA, hMa, ev, mul_comm]
  have hUm0 : ∀ i j, Um i j ∈ Fil P 0 := by
    intro i j
    rw [hUm, Matrix.mul_diagonal]
    by_cases hj : j = x2
    · subst hj; rw [if_pos rfl, mul_comm]; exact tz_inv_mem T (hAU1 i)
    · rw [if_neg hj, mul_one]; exact hAU0 i j
  have hUmdet : Um.det = kd P κ * U0.det := by
    have hdι : (A.map P.ιB).det = P.ιB A.det := ((P.ιB : P.R.B →+* P.R.BdR).map_det A).symm
    have hDxd : Dx.det = tz P (-1) := by
      rw [hDx, det_diagonal, Finset.prod_ite_eq']; simp
    have ht : tz P 1 * tz P (-1) = 1 := by rw [← tz_add]; simp [tz_zero]
    rw [hUm, det_mul, det_mul, hdι, hDxd, hAdet, map_mul, iota_kur, ← tz_one]
    linear_combination (kd P κ * U0.det) * ht
  have hU0inv : U0 * ((U 0)⁻¹ : GL n P.R.BdR) = 1 := by rw [hU0, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨U', hU'eq, hU'u⟩ := unitM_of Um hUm0 (kd P κ⁻¹ * Matrix.det (((U 0)⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR))
    (Fil_mul_left (kd_mem_Fil P _) (det_mem _ (hU 0).2)) (by
      rw [hUmdet]
      have h1 := kd_mul_inv (P := P) hκ
      have h2 : U0.det * (((U 0)⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR).det = 1 := by rw [← det_mul, hU0inv, det_one]
      linear_combination (U0.det * (((U 0)⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR).det) * h1 + h2)

  set V : Matrix n n P.R.BdR := ((U'⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR) with hV
  have hVU : V * Um = 1 := by rw [hV, ← hU'eq, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  let μ : Fin h → P.R.BdR := fun k => V y2 (e.symm k)
  have hμ0 : ∀ k, μ k ∈ Fil P 0 := fun k => hU'u.2 _ _
  have hμu : ∃ k, μ k ∉ Fil P 1 := by
    by_contra hne
    push_neg at hne
    have h1 : (V * Um) y2 y2 ∈ Fil P 1 := by
      rw [Matrix.mul_apply]
      exact Fil_sum fun j _ => Fil_mul_right (by simpa [μ] using hne (e j)) (hUm0 j y2)
    rw [hVU, Matrix.one_apply_eq] at h1
    exact one_not_mem h1
  obtain ⟨b, hb_plus, hb_phi, hb_ind, hb_sum⟩ := GlobalTheory.T.existsIndependentFrobSolutionsCris_proof l P AI T h hh μ hμ0 hμu
  have hb_det := GlobalTheory.T.mooreDeterminant_crisPlus_ne_zero l P AI T h h le_rfl b hb_plus hb_phi hb_ind
  have hb_fil : ∀ (i : ℕ) j, ev P i (b j) ∈ Fil P 0 := fun i j => (GlobalTheory.T.bcrisPlus_frobeniusStable_subring_in_filZero l P AI T).2.1 _ (hb_plus j) i
  have hdetιb : P.ιB (Matrix.of fun i j : Fin h => P.φB^[i] (b j)).det ∈ Fil P 1 := by
    obtain ⟨k, hk⟩ := hμu
    change (P.ιB : P.R.B →+* P.R.BdR) _ ∈ _
    rw [RingHom.map_det]
    refine det_mem_one' T _ μ (fun i j => hb_fil i j) hμ0 k hk fun j => ?_
    change ∑ i, μ i * ev P i (b j) ∈ Fil P 1
    exact hb_sum j
  obtain ⟨κ', hκ', hdetB⟩ := GlobalTheory.T.mooreDeterminant_eq_unramified_mul_period l P AI T h (by omega) b hb_phi hb_fil hb_det hdetιb

  set Mb : Matrix (Fin h) (Fin h) P.R.B := Matrix.of fun i j : Fin h => P.φB^[i] (b j) with hMb
  set Bm : Matrix n n P.R.B := Mb.submatrix e e with hBm
  have hBdet : Bm.det = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B κ' * P.tB := by rw [hBm, Matrix.det_submatrix_equiv_self, hdetB]
  have hBu : IsUnit Bm.det := by rw [hBdet]; exact isUnit_algebraMap_unramified_mul_period hκ'
  set Dy : Matrix n n P.R.BdR := diagonal fun j => if j = y2 then tz P (-1) else 1 with hDy
  set X : Matrix n n P.R.BdR := V * Bm.map P.ιB with hX
  have hX0 : ∀ i j, X i j ∈ Fil P 0 := mul_mem _ _ hU'u.2 (fun i j => hb_fil _ _)
  have hX1 : ∀ j, X y2 j ∈ Fil P 1 := by
    intro j
    have := hb_sum (e j)
    rw [hX, Matrix.mul_apply]
    convert this using 1
    refine Fintype.sum_equiv e _ _ fun i => ?_
    simp [μ, hBm, hMb, ev]
  set Wm : Matrix n n P.R.BdR := Dy * X with hWm
  have hWm0 : ∀ i j, Wm i j ∈ Fil P 0 := by
    intro i j
    rw [hWm, Matrix.diagonal_mul]
    by_cases hi : i = y2
    · subst hi; rw [if_pos rfl]; exact tz_inv_mem T (hX1 j)
    · rw [if_neg hi, one_mul]; exact hX0 i j
  have hVUm : V.det * Um.det = 1 := by rw [← det_mul, hVU, det_one]
  have ht : tz P (-1) * tz P 1 = 1 := by rw [← tz_add]; simp [tz_zero]
  have hWmdet : Wm.det = kd P κ' * V.det := by
    have hdι : (Bm.map P.ιB).det = P.ιB Bm.det := ((P.ιB : P.R.B →+* P.R.BdR).map_det Bm).symm
    have hDyd : Dy.det = tz P (-1) := by
      rw [hDy, det_diagonal, Finset.prod_ite_eq']; simp
    rw [hWm, hX, det_mul, det_mul, hdι, hDyd, hBdet, map_mul, iota_kur, ← tz_one]
    linear_combination (kd P κ' * V.det) * ht
  obtain ⟨W, hWeq, hWu⟩ := unitM_of Wm hWm0 (kd P κ'⁻¹ * Um.det)
    (Fil_mul_left (kd_mem_Fil P _) (det_mem _ hUm0)) (by
      rw [hWmdet]
      have h1 := kd_mul_inv (P := P) hκ'
      linear_combination (V.det * Um.det) * h1 + hVUm)

  have hRu : IsUnit (A⁻¹ * Bm).det := by rw [det_mul]; exact (isUnit_nonsing_inv_det A hAu).mul hBu
  refine ⟨Matrix.nonsingInvUnit (A⁻¹ * Bm) hRu, fun i j => ?_, fun m => ?_⟩
  · set C : Matrix n n P.R.B := (comp P.R.B (l : P.R.B) h).submatrix e e
    have hMa' := moore_map (P.φB : P.R.B →+* P.R.B) (l : P.R.B) h a ha_phi
    have hMb' := moore_map (P.φB : P.R.B →+* P.R.B) (l : P.R.B) h b hb_phi
    have hA' : A.map (P.φB : P.R.B →+* P.R.B) = C * A := by
      rw [hA, ← Matrix.submatrix_map]
      exact (congrArg (fun M => Matrix.submatrix M e e) hMa').trans (Matrix.submatrix_mul_equiv _ _ _ e _).symm
    have hB' : Bm.map (P.φB : P.R.B →+* P.R.B) = C * Bm := by
      rw [hBm, ← Matrix.submatrix_map]
      exact (congrArg (fun M => Matrix.submatrix M e e) hMb').trans (Matrix.submatrix_mul_equiv _ _ _ e _).symm
    have := congrFun (congrFun (inv_mul_fixed (P.φB : P.R.B →+* P.R.B) A Bm C hAu hA' hB') i) j
    exact this
  · obtain rfl : m = 0 := Subsingleton.elim _ _
    refine ⟨W, hWu, ?_⟩
    have hev : ev P ((0 : Fin 1) : ℕ) = P.ιB := funext fun _ => rfl
    have hιAu : IsUnit (A.map P.ιB).det := by
      have h := hAu.map (P.ιB : P.R.B →+* P.R.BdR)
      rw [RingHom.map_det] at h
      exact h
    have hDε : diagonal (fun j => tz P (eps ((0 : Fin 1), x2) ((0 : Fin 1), y2) ((0 : Fin 1), j))) * Dy = Dx := by
      rw [hDy, hDx, diagonal_mul_diagonal]
      congr 1
      funext j
      by_cases hjx : j = x2
      · subst hjx; simp [eps, h2]
      · by_cases hjy : j = y2
        · subst hjy; simp [eps, hjx, Ne.symm hjx]; rw [mul_comm]; exact ht
        · simp [eps, hjx, hjy, tz_zero]
    have hUmV : Um * V = 1 := mul_eq_one_comm.1 hVU
    change (A⁻¹ * Bm).map (ev P ((0 : Fin 1) : ℕ)) = U0 * _ * (W : Matrix n n P.R.BdR)
    have hinv : (A⁻¹).map P.ιB = (A.map P.ιB)⁻¹ := map_inv' (P.ιB : P.R.B →+* P.R.BdR) A hAu
    rw [hev, hWeq, Matrix.map_mul, hinv]
    calc (A.map P.ιB)⁻¹ * Bm.map P.ιB = (A.map P.ιB)⁻¹ * (Um * V) * Bm.map P.ιB := by
          rw [hUmV, Matrix.mul_one]
      _ = U0 * Dx * V * Bm.map P.ιB := by
          rw [hUm, Matrix.mul_assoc (A.map P.ιB), Matrix.mul_assoc (A.map P.ιB), ← Matrix.mul_assoc (A.map P.ιB)⁻¹,
            Matrix.nonsing_inv_mul _ hιAu, Matrix.one_mul]
      _ = _ := by
          rw [hWm, hX, ← hDε]
          simp only [Matrix.mul_assoc]

end GlobalTheory.PMon.FLOne
