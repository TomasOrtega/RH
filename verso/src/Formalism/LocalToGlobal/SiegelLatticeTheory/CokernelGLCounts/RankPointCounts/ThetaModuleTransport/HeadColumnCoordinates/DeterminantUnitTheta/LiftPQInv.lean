import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.FirstQuotientEqZeroIff

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {r : ℕ}

/- English proof (translation)
Establish `hsurj : ∀ j : Fin (r + 1), ∃ w : Fin (r + 1) → M.R, Submodule.Quotient.mk (p` using `headCols Z₂.Z) w = γ.1 (Submodule.Quotient.mk (Pi.single j 1)) ∧ (j = Fin.last r → w = Pi.single (Fin.last r) 1) := by`. Introduce `j`. Distinguish the cases in `hj : j = Fin.last r`. Substitute `hj` using the available equality. Use `⟨Pi.single (Fin.last r) 1, ?_, fun _ => rfl⟩` and prove the remaining obligations.

Conclude with `γ.2.2.symm`. Take `⟨w, hw⟩` from `Submodule.Quotient.mk_surjective _ (γ.1 (Submodule.Quotient.mk (Pi.single j 1)))`. Conclude with `⟨w, hw, fun h => absurd h hj⟩`. Use `choose p hp hpl using hsurj`. Set `P : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R` to `Matrix.of fun i j => p j i`.

Establish `hP : ∀ v, γ.1 (Submodule.Quotient.mk v) = Submodule.Quotient.mk (P.mulVec v)`. Establish `key : γ.1.toLinearMap ∘ₗ (headCols Z₁.Z).mkQ = (headCols Z₂.Z).mkQ ∘ₗ P.mulVecLin`. Apply `LinearMap.pi_ext` to reduce the goal to its premises. Introduce `j x`. Establish `h1 : (Pi.single j x : Fin (r + 1) → M.R) = x • Pi.single j 1`.

Apply the tactic sequence `ext k; by_cases hk : k = j <;> simp [Pi.single_apply, hk]`. Establish `h2 : P.mulVec (Pi.single j x) = x • p j`. Use extensionality with `i`. Simplify using `[P, Matrix.mulVec_single, mul_comm]`. Simplify using `only [LinearMap.comp_apply, Submodule.mkQ_apply, Matrix.mulVecLin_apply, LinearEquiv.coe_coe]`.

Rewrite using `[h2, h1, Submodule.Quotient.mk_smul, map_smul, Submodule.Quotient.mk_smul, hp j]`. Introduce `v`. Conclude with `LinearMap.congr_fun key v`. Establish `ht : ∀ j, P.mulVec (fun i => Z₁.Z i j) - (if j = Fin.last r then (fun i => Z₂.Z i (Fin.last r)) else 0) ∈ headCols Z₂.Z`. Introduce `j`.

Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, ← hP]`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last`. Establish `h` using `γ.2.1`. Unfold `bCls at h`.

Rewrite using `[if_pos rfl, h, sub_self]`. Consider the case `cast a`. Establish `hmem : (fun i => Z₁.Z i a.castSucc) ∈ headCols Z₁.Z` using `Submodule.subset_span ⟨a, rfl⟩`. Rewrite using `[(Submodule.Quotient.mk_eq_zero _).2 hmem, map_zero, if_neg (Fin.castSucc_ne_last a), Submodule.Quotient.mk_zero, sub_zero]`. Establish `hc : ∀ j, ∃ c : Fin r → M.R, ∑ a, c a • (fun i => Z₂.Z i a.castSucc) = P.mulVec (fun i => Z₁.Z i j) - (if j = Fin.last r then (fun i => Z₂.Z i (Fin.last r)) else 0)` using `fun j => (Submodule.mem_span_range_iff_exists_fun _).1 (ht j)`.

Use `choose c hc using hc`. Use `⟨P, Matrix.of fun k j => Fin.lastCases (if j = Fin.last r then (1 : M.R) else 0) (fun b => c j b) k, hP, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Establish `h` using `congrFun (hc j) i`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h`.

Rewrite using `[Matrix.mul_apply, Matrix.mul_apply]`. Rewrite using `[show ∑ k, P i k * Z₁.Z k j = P.mulVec (fun i => Z₁.Z i j) i from rfl]`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `only [Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]`. Establish `hcomm : ∑ x : Fin r, Z₂.Z i x.castSucc * c j x = ∑ x : Fin r, c j x * Z₂.Z i x.castSucc` using `Finset.sum_congr rfl (fun _ _ => mul_comm _ _)`.

Rewrite using `[hcomm, h]`. Distinguish the cases in `hj : j = Fin.last r`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `only [if_neg hj, Pi.zero_apply]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `i`. Simplify using `[P, hpl _ rfl, Pi.single_apply]`. Introduce `j`. Simplify using the standard rewrite rules.
-/
theorem liftPQ (Z₁ Z₂ : M.Mat (r + 1)) (γ : IsoMbe Z₁.Z Z₂.Z) :
    ∃ P Q : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R,
      (∀ v, γ.1 (Submodule.Quotient.mk v) = Submodule.Quotient.mk (P.mulVec v)) ∧ P * Z₁.Z = Z₂.Z * Q ∧
      (∀ i, P i (Fin.last r) = if i = Fin.last r then 1 else 0) ∧
      (∀ j, Q (Fin.last r) j = if j = Fin.last r then 1 else 0) := by
  classical
  have hsurj : ∀ j : Fin (r + 1), ∃ w : Fin (r + 1) → M.R,
      Submodule.Quotient.mk (p := headCols Z₂.Z) w = γ.1 (Submodule.Quotient.mk (Pi.single j 1)) ∧
      (j = Fin.last r → w = Pi.single (Fin.last r) 1) := by
    intro j
    by_cases hj : j = Fin.last r
    · subst hj
      refine ⟨Pi.single (Fin.last r) 1, ?_, fun _ => rfl⟩
      exact γ.2.2.symm
    · obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (γ.1 (Submodule.Quotient.mk (Pi.single j 1)))
      exact ⟨w, hw, fun h => absurd h hj⟩
  choose p hp hpl using hsurj
  let P : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R := Matrix.of fun i j => p j i
  have hP : ∀ v, γ.1 (Submodule.Quotient.mk v) = Submodule.Quotient.mk (P.mulVec v) := by
    have key : γ.1.toLinearMap ∘ₗ (headCols Z₁.Z).mkQ = (headCols Z₂.Z).mkQ ∘ₗ P.mulVecLin := by
      apply LinearMap.pi_ext
      intro j x
      have h1 : (Pi.single j x : Fin (r + 1) → M.R) = x • Pi.single j 1 := by
        ext k; by_cases hk : k = j <;> simp [Pi.single_apply, hk]
      have h2 : P.mulVec (Pi.single j x) = x • p j := by
        ext i; simp [P, Matrix.mulVec_single, mul_comm]
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Matrix.mulVecLin_apply, LinearEquiv.coe_coe]
      rw [h2, h1, Submodule.Quotient.mk_smul, map_smul, Submodule.Quotient.mk_smul, hp j]
    intro v
    exact LinearMap.congr_fun key v
  have ht : ∀ j, P.mulVec (fun i => Z₁.Z i j) -
      (if j = Fin.last r then (fun i => Z₂.Z i (Fin.last r)) else 0) ∈ headCols Z₂.Z := by
    intro j
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, ← hP]
    induction j using Fin.lastCases with
    | last =>
      have h := γ.2.1
      unfold bCls at h
      rw [if_pos rfl, h, sub_self]
    | cast a =>
      have hmem : (fun i => Z₁.Z i a.castSucc) ∈ headCols Z₁.Z := Submodule.subset_span ⟨a, rfl⟩
      rw [(Submodule.Quotient.mk_eq_zero _).2 hmem, map_zero, if_neg (Fin.castSucc_ne_last a),
        Submodule.Quotient.mk_zero, sub_zero]
  have hc : ∀ j, ∃ c : Fin r → M.R, ∑ a, c a • (fun i => Z₂.Z i a.castSucc) =
      P.mulVec (fun i => Z₁.Z i j) - (if j = Fin.last r then (fun i => Z₂.Z i (Fin.last r)) else 0) :=
    fun j => (Submodule.mem_span_range_iff_exists_fun _).1 (ht j)
  choose c hc using hc
  refine ⟨P, Matrix.of fun k j => Fin.lastCases (if j = Fin.last r then (1 : M.R) else 0) (fun b => c j b) k,
    hP, ?_, ?_, ?_⟩
  · refine Matrix.ext fun i j => ?_
    have h := congrFun (hc j) i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h
    rw [Matrix.mul_apply, Matrix.mul_apply]
    rw [show ∑ k, P i k * Z₁.Z k j = P.mulVec (fun i => Z₁.Z i j) i from rfl]
    rw [Fin.sum_univ_castSucc]
    simp only [Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]
    have hcomm : ∑ x : Fin r, Z₂.Z i x.castSucc * c j x = ∑ x : Fin r, c j x * Z₂.Z i x.castSucc :=
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    rw [hcomm, h]
    by_cases hj : j = Fin.last r
    · subst hj
      simp
    · simp only [if_neg hj, Pi.zero_apply]
      ring
  · intro i
    simp [P, hpl _ rfl, Pi.single_apply]
  · intro j
    simp

/- English proof (translation)
Establish `hid : ∀ w : Fin (r + 1) → M.R, (P' * P).mulVec w - w ∈ headCols Z₁.Z`. Introduce `w`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero, ← Matrix.mulVec_mulVec, ← hP', ← hP, LinearEquiv.symm_apply_apply]`. Establish `hc : ∀ j, ∃ c : Fin r → M.R, ∑ a, c a • (fun i => Z₁.Z i a.castSucc) = (P' * P).mulVec (Pi.single j 1) - Pi.single j 1` using `fun j => (Submodule.mem_span_range_iff_exists_fun _).1 (hid _)`. Use `choose c hc using hc`.

Use `⟨Matrix.of fun k j => Fin.lastCases 0 (fun b => if j = Fin.last r then 0 else c j b) k, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j`. Simplify using the standard rewrite rules. Introduce `i`. Proceed by induction on `i using Fin.lastCases with`.

Consider the case `last => simp`. Consider the case `cast b => simp`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Rewrite using `[Matrix.add_apply, Matrix.mul_apply (M := Z₁.Z), Fin.sum_univ_castSucc]`. Simplify using `only [Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last, mul_zero, add_zero]`.

Distinguish the cases in `hj : j = Fin.last r`. Substitute `hj` using the available equality. Simplify using `only [if_pos rfl, mul_zero, Finset.sum_const_zero, add_zero]`. Rewrite using `[Matrix.mul_apply]`. Simplify using `[hPe, hP'e, Matrix.one_apply]`.

Simplify using `only [if_neg hj]`. Establish `h` using `congrFun (hc j) i`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Matrix.mulVec_single, mul_one] at h`. Establish `hcomm : ∑ x : Fin r, Z₁.Z i x.castSucc * c j x = ∑ x : Fin r, c j x * Z₁.Z i x.castSucc` using `Finset.sum_congr rfl (fun _ _ => mul_comm _ _)`. Rewrite using `[hcomm, h, Matrix.one_apply, Pi.single_apply]`.

Simplify using `[Matrix.col_apply]`.
-/
theorem liftPQ_inv (Z₁ Z₂ : M.Mat (r + 1)) (γ : IsoMbe Z₁.Z Z₂.Z) (P P' : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R)
    (hP : ∀ v, γ.1 (Submodule.Quotient.mk v) = Submodule.Quotient.mk (P.mulVec v))
    (hP' : ∀ v, γ.1.symm (Submodule.Quotient.mk v) = Submodule.Quotient.mk (P'.mulVec v))
    (hPe : ∀ i, P i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hP'e : ∀ i, P' i (Fin.last r) = if i = Fin.last r then 1 else 0) :
    ∃ K : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R, (∀ j, K (Fin.last r) j = 0) ∧ (∀ i, K i (Fin.last r) = 0) ∧
      P' * P = 1 + Z₁.Z * K := by
  classical
  have hid : ∀ w : Fin (r + 1) → M.R, (P' * P).mulVec w - w ∈ headCols Z₁.Z := by
    intro w
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero,
      ← Matrix.mulVec_mulVec, ← hP', ← hP, LinearEquiv.symm_apply_apply]
  have hc : ∀ j, ∃ c : Fin r → M.R, ∑ a, c a • (fun i => Z₁.Z i a.castSucc) =
      (P' * P).mulVec (Pi.single j 1) - Pi.single j 1 :=
    fun j => (Submodule.mem_span_range_iff_exists_fun _).1 (hid _)
  choose c hc using hc
  refine ⟨Matrix.of fun k j => Fin.lastCases 0 (fun b => if j = Fin.last r then 0 else c j b) k, ?_, ?_, ?_⟩
  · intro j
    simp
  · intro i
    induction i using Fin.lastCases with
    | last => simp
    | cast b => simp
  · refine Matrix.ext fun i j => ?_
    rw [Matrix.add_apply, Matrix.mul_apply (M := Z₁.Z), Fin.sum_univ_castSucc]
    simp only [Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last, mul_zero, add_zero]
    by_cases hj : j = Fin.last r
    · subst hj
      simp only [if_pos rfl, mul_zero, Finset.sum_const_zero, add_zero]
      rw [Matrix.mul_apply]
      simp [hPe, hP'e, Matrix.one_apply]
    · simp only [if_neg hj]
      have h := congrFun (hc j) i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Matrix.mulVec_single,
        mul_one] at h
      have hcomm : ∑ x : Fin r, Z₁.Z i x.castSucc * c j x = ∑ x : Fin r, c j x * Z₁.Z i x.castSucc :=
        Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
      rw [hcomm, h, Matrix.one_apply, Pi.single_apply]
      simp [Matrix.col_apply]

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
