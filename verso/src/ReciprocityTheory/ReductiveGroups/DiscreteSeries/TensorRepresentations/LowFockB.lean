import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockA
import Formalism.RealPlaceAnalysis.StatementKT

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def lfPhysModes (ε : Fin n → Bool) : Finset (Fin (n * n)) :=
  univ.filter fun m => ε (finProdFinEquiv.symm m).1 = true ∧ ε (finProdFinEquiv.symm m).2 = false

abbrev LfIdx (ε : Fin n → Bool) : Type := {S : Finset (Fin (n * n)) // S ⊆ lfPhysModes ε}

def lfMatFull (ε : Fin n → Bool) (a b : Fin n) : Matrix (Finset (Fin (n * n))) (Finset (Fin (n * n))) ℂ :=
  LinearMap.toMatrix (fockBasis n) (fockBasis n) (sgE ε cpFock cmFock a b)

def lfMat (ε : Fin n → Bool) (a b : Fin n) : Matrix (LfIdx ε) (LfIdx ε) ℂ :=
  (lfMatFull ε a b).submatrix Subtype.val Subtype.val

def lfP (i a : Fin n) : Matrix (Finset (Fin (n * n))) (Finset (Fin (n * n))) ℂ :=
  LinearMap.toMatrix (fockBasis n) (fockBasis n) (cpFock i a)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lf_toMatrix_cp (i a : Fin n) :
    LinearMap.toMatrix (fockBasis n) (fockBasis n) (cpFock i a) = lfP i a := rfl

/- English proof (translation)
Use extensionality with `T S`. Simplify using `only [LinearMap.toMatrix_apply, lfP, transpose_apply]`. Conclude with `lf_repr_cm_eq (i, a) S T`.
-/
theorem lf_toMatrix_cm (i a : Fin n) :
    LinearMap.toMatrix (fockBasis n) (fockBasis n) (cmFock i a) = (lfP i a)ᵀ := by
  ext T S
  simp only [LinearMap.toMatrix_apply, lfP, transpose_apply]
  exact lf_repr_cm_eq (i, a) S T

/- English proof (translation)
Use extensionality with `T S`. Simplify using `only [conjTranspose_apply, transpose_apply, lfP, LinearMap.toMatrix_apply]`. Conclude with `lf_repr_cp_star (i, a) T S`.
-/
theorem fockMatrix_conjTranspose_eq_transpose (i a : Fin n) : (lfP i a)ᴴ = (lfP i a)ᵀ := by
  ext T S
  simp only [conjTranspose_apply, transpose_apply, lfP, LinearMap.toMatrix_apply]
  exact lf_repr_cp_star (i, a) T S

/- English proof (translation)
Rewrite using `[← fockMatrix_conjTranspose_eq_transpose, Matrix.conjTranspose_conjTranspose]`.
-/
theorem fockMatrix_transpose_conjTranspose (i a : Fin n) : (lfP i a)ᵀᴴ = lfP i a := by
  rw [← fockMatrix_conjTranspose_eq_transpose, Matrix.conjTranspose_conjTranspose]

/- English proof (translation)
Unfold `lfMatFull sgE`. Apply the tactic sequence `split_ifs <;> simp only [map_sum, map_neg, map_zero, LinearMap.toMatrix_mul, lf_toMatrix_cp, lf_toMatrix_cm]`.
-/
theorem lfMatFull_eq (ε : Fin n → Bool) (a b : Fin n) : lfMatFull ε a b =
    if ε a = true ∧ ε b = true then ∑ x ∈ minusIdx ε, lfP a x * (lfP b x)ᵀ
    else if ε a = false ∧ ε b = false then -∑ i ∈ plusIdx ε, lfP i b * (lfP i a)ᵀ
    else 0 := by
  unfold lfMatFull sgE
  split_ifs <;> simp only [map_sum, map_neg, map_zero, LinearMap.toMatrix_mul, lf_toMatrix_cp, lf_toMatrix_cm]

/- English proof (translation)
Introduce `a b c d hab hcd`. Establish `h` using `congrArg (LinearMap.toMatrix (fockBasis n) (fockBasis n)) (sgE_comm isCAR_fock ε a b c d hab hcd)`. Apply the tactic sequence `split_ifs at h ⊢ <;> simpa only [lfMatFull, map_sub, map_zero, LinearMap.toMatrix_mul] using h`.
-/
theorem lfMatFull_kRel (ε : Fin n → Bool) : Formalism.REAL.KRel ε (lfMatFull ε) := by
  intro a b c d hab hcd
  have h := congrArg (LinearMap.toMatrix (fockBasis n) (fockBasis n))
    (sgE_comm isCAR_fock ε a b c d hab hcd)
  split_ifs at h ⊢ <;> simpa only [lfMatFull, map_sub, map_zero, LinearMap.toMatrix_mul] using h

/- English proof (translation)
Rewrite using `[lfMatFull_eq, lfMatFull_eq]`. Simplify using `only [h]`. Apply the tactic sequence `split_ifs <;> simp [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, fockMatrix_conjTranspose_eq_transpose, fockMatrix_transpose_conjTranspose, Matrix.conjTranspose_neg]`.
-/
theorem lfMatFull_conjTranspose (ε : Fin n → Bool) {a b : Fin n} (h : ε a = ε b) :
    lfMatFull ε b a = (lfMatFull ε a b)ᴴ := by
  rw [lfMatFull_eq, lfMatFull_eq]
  simp only [h]
  split_ifs <;> simp [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, fockMatrix_conjTranspose_eq_transpose,
    fockMatrix_transpose_conjTranspose, Matrix.conjTranspose_neg]

/- English proof (translation)
Simplify using `only [lfPhysModes, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]`.
-/
theorem lf_mem_phys (ε : Fin n → Bool) (i a : Fin n) :
    finProdFinEquiv (i, a) ∈ lfPhysModes ε ↔ ε i = true ∧ ε a = false := by
  simp only [lfPhysModes, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]

/- English proof (translation)
Distinguish the cases in `hx : finProdFinEquiv (i, a) ∈ S`. Take `⟨σ, -, h1, -⟩` from `lf_cm_basis_of_mem (x := (i, a)) hx`. Conclude with `⟨σ, S.erase (finProdFinEquiv (i, a)), (Finset.erase_subset _ _).trans hS, h1⟩`. Conclude with `⟨0, S, hS, by rw [zero_smul]; exact lf_cm_basis_of_not_mem (x := (i, a)) hx⟩`.
-/
theorem lf_cm_phys {ε : Fin n → Bool} (i a : Fin n) {S : Finset (Fin (n * n))} (hS : S ⊆ lfPhysModes ε) :
    ∃ c : ℂ, ∃ U, U ⊆ lfPhysModes ε ∧ cmFock i a (fockBasis n S) = c • fockBasis n U := by
  by_cases hx : finProdFinEquiv (i, a) ∈ S
  · obtain ⟨σ, -, h1, -⟩ := lf_cm_basis_of_mem (x := (i, a)) hx
    exact ⟨σ, S.erase (finProdFinEquiv (i, a)), (Finset.erase_subset _ _).trans hS, h1⟩
  · exact ⟨0, S, hS, by rw [zero_smul]; exact lf_cm_basis_of_not_mem (x := (i, a)) hx⟩

/- English proof (translation)
Distinguish the cases in `hx : finProdFinEquiv (i, a) ∈ S`. Conclude with `⟨0, S, hS, by rw [zero_smul]; exact lf_cp_basis_of_mem (x := (i, a)) hx⟩`. Take `⟨σ, -, h1, -⟩` from `lf_cp_cm_basis (x := (i, a)) hx`. Conclude with `⟨σ, insert (finProdFinEquiv (i, a)) S, Finset.insert_subset ((lf_mem_phys ε i a).2 hia) hS, h1⟩`.
-/
theorem lf_cp_phys {ε : Fin n → Bool} {i a : Fin n} (hia : ε i = true ∧ ε a = false)
    {S : Finset (Fin (n * n))} (hS : S ⊆ lfPhysModes ε) :
    ∃ c : ℂ, ∃ U, U ⊆ lfPhysModes ε ∧ cpFock i a (fockBasis n S) = c • fockBasis n U := by
  by_cases hx : finProdFinEquiv (i, a) ∈ S
  · exact ⟨0, S, hS, by rw [zero_smul]; exact lf_cp_basis_of_mem (x := (i, a)) hx⟩
  · obtain ⟨σ, -, h1, -⟩ := lf_cp_cm_basis (x := (i, a)) hx
    exact ⟨σ, insert (finProdFinEquiv (i, a)) S, Finset.insert_subset ((lf_mem_phys ε i a).2 hia) hS, h1⟩

/- English proof (translation)
Take `⟨c, U, hU, hcm⟩` from `lf_cm_phys (ε := ε) j b hS`. Take `⟨c', U', hU', hcp⟩` from `lf_cp_phys hia hU`. Establish `e : (cpFock i a * cmFock j b) (fockBasis n S) = (c * c') • fockBasis n U'` using `by show cpFock i a (cmFock j b (fockBasis n S)) = _`. Rewrite using `[hcm, map_smul, hcp, smul_smul]`. Rewrite using `[e, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero]`.

Introduce and unpack `rfl`. Conclude with `hT hU'`.
-/
theorem lf_cpcm_repr {ε : Fin n → Bool} {i a : Fin n} (j b : Fin n) (hia : ε i = true ∧ ε a = false)
    {S T : Finset (Fin (n * n))} (hS : S ⊆ lfPhysModes ε) (hT : ¬ T ⊆ lfPhysModes ε) :
    (fockBasis n).repr ((cpFock i a * cmFock j b) (fockBasis n S)) T = 0 := by
  obtain ⟨c, U, hU, hcm⟩ := lf_cm_phys (ε := ε) j b hS
  obtain ⟨c', U', hU', hcp⟩ := lf_cp_phys hia hU
  have e : (cpFock i a * cmFock j b) (fockBasis n S) = (c * c') • fockBasis n U' := by
    show cpFock i a (cmFock j b (fockBasis n S)) = _
    rw [hcm, map_smul, hcp, smul_smul]
  rw [e, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero]
  rintro rfl
  exact hT hU'

/- English proof (translation)
Rewrite using `[lfMatFull, LinearMap.toMatrix_apply]`. Unfold `sgE`. Use `split_ifs with h1 h2`. Simplify using `only [LinearMap.sum_apply, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]`. Use `Finset.sum_eq_zero fun x hx => ?_` and prove the remaining obligations.

Conclude with `lf_cpcm_repr b x ⟨h1.1, by simpa [minusIdx] using hx⟩ hS hT`. Simplify using `only [LinearMap.neg_apply, LinearMap.sum_apply, map_neg, map_sum, Finsupp.coe_neg, Pi.neg_apply, Finsupp.coe_finset_sum, Finset.sum_apply, neg_eq_zero]`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Conclude with `lf_cpcm_repr i a ⟨by simpa [plusIdx] using hi, h2.2⟩ hS hT`. Simplify using the standard rewrite rules.
-/
theorem lfMatFull_eq_zero (ε : Fin n → Bool) (a b : Fin n) {S T : Finset (Fin (n * n))}
    (hS : S ⊆ lfPhysModes ε) (hT : ¬ T ⊆ lfPhysModes ε) : lfMatFull ε a b T S = 0 := by
  rw [lfMatFull, LinearMap.toMatrix_apply]
  unfold sgE
  split_ifs with h1 h2
  · simp only [LinearMap.sum_apply, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun x hx => ?_
    exact lf_cpcm_repr b x ⟨h1.1, by simpa [minusIdx] using hx⟩ hS hT
  · simp only [LinearMap.neg_apply, LinearMap.sum_apply, map_neg, map_sum, Finsupp.coe_neg, Pi.neg_apply,
      Finsupp.coe_finset_sum, Finset.sum_apply, neg_eq_zero]
    refine Finset.sum_eq_zero fun i hi => ?_
    exact lf_cpcm_repr i a ⟨by simpa [plusIdx] using hi, h2.2⟩ hS hT
  · simp

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, lfMat, Matrix.submatrix_apply]`. Establish `key : ∑ U : Finset (Fin (n * n)), lfMatFull ε a b T.1 U * lfMatFull ε c d U S.1 = ∑ U ∈ Finset.univ.filter (fun U : Finset (Fin (n * n)) => U ⊆ lfPhysModes ε), lfMatFull ε a b T.1 U * lfMatFull ε c d U S.1`. Use `symm`. Apply `Finset.sum_subset (Finset.filter_subset _ _)` to reduce the goal to its premises. Introduce `U _ hU`.

Establish `hU' : ¬ U ⊆ lfPhysModes ε` using `by simpa using hU`. Rewrite using `[lfMatFull_eq_zero ε c d S.2 hU', mul_zero]`. Rewrite using `[key, Finset.sum_subtype (p := fun U : Finset (Fin (n * n)) => U ⊆ lfPhysModes ε) _ (fun U => by simp)]`.
-/
theorem lfMat_mul_apply (ε : Fin n → Bool) (a b c d : Fin n) (T S : LfIdx ε) :
    (lfMat ε a b * lfMat ε c d) T S = (lfMatFull ε a b * lfMatFull ε c d) T.1 S.1 := by
  simp only [Matrix.mul_apply, lfMat, Matrix.submatrix_apply]
  have key : ∑ U : Finset (Fin (n * n)), lfMatFull ε a b T.1 U * lfMatFull ε c d U S.1 =
      ∑ U ∈ Finset.univ.filter (fun U : Finset (Fin (n * n)) => U ⊆ lfPhysModes ε),
        lfMatFull ε a b T.1 U * lfMatFull ε c d U S.1 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro U _ hU
    have hU' : ¬ U ⊆ lfPhysModes ε := by simpa using hU
    rw [lfMatFull_eq_zero ε c d S.2 hU', mul_zero]
  rw [key, Finset.sum_subtype (p := fun U : Finset (Fin (n * n)) => U ⊆ lfPhysModes ε) _ (fun U => by simp)]

/- English proof (translation)
Introduce `a b c d hab hcd`. Use extensionality with `T S`. Establish `h` using `congrFun (congrFun (lfMatFull_kRel ε a b c d hab hcd) T.1) S.1`. Simplify using `only [Matrix.sub_apply, lfMat_mul_apply] at h ⊢`. Apply the tactic sequence `split_ifs at h ⊢ <;> simpa only [lfMat, Matrix.submatrix_apply, Matrix.zero_apply] using h`.
-/
theorem lfMat_kRel (ε : Fin n → Bool) : Formalism.REAL.KRel ε (lfMat ε) := by
  intro a b c d hab hcd
  ext T S
  have h := congrFun (congrFun (lfMatFull_kRel ε a b c d hab hcd) T.1) S.1
  simp only [Matrix.sub_apply, lfMat_mul_apply] at h ⊢
  split_ifs at h ⊢ <;> simpa only [lfMat, Matrix.submatrix_apply, Matrix.zero_apply] using h

/- English proof (translation)
Use extensionality with `T S`. Simplify using `only [lfMat, Matrix.submatrix_apply, Matrix.conjTranspose_apply]`. Rewrite using `[lfMatFull_conjTranspose ε h, Matrix.conjTranspose_apply]`.
-/
theorem lfMat_conjTranspose (ε : Fin n → Bool) {a b : Fin n} (h : ε a = ε b) :
    lfMat ε b a = (lfMat ε a b)ᴴ := by
  ext T S
  simp only [lfMat, Matrix.submatrix_apply, Matrix.conjTranspose_apply]
  rw [lfMatFull_conjTranspose ε h, Matrix.conjTranspose_apply]

/- English proof (translation)
Establish `key : sgE ε cpFock cmFock a b (fockBasis n S.1) = ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin (n * n)) => T ⊆ lfPhysModes ε), (fockBasis n).repr (sgE ε cpFock cmFock a b (fockBasis n S.1)) T • fockBasis n T` using `by conv_lhs => rw [← (fockBasis n).sum_repr (sgE ε cpFock cmFock a b (fockBasis n S.1))]`. Use `symm`. Apply `Finset.sum_subset (Finset.filter_subset _ _)` to reduce the goal to its premises. Introduce `T _ hT`. Establish `hT' : ¬ T ⊆ lfPhysModes ε` using `by simpa using hT`.

Establish `h0` using `lfMatFull_eq_zero ε a b S.2 hT'`. Rewrite `h0` using `[lfMatFull, LinearMap.toMatrix_apply]`. Rewrite using `[h0, zero_smul]`. Rewrite using `[key, Finset.sum_subtype (p := fun T : Finset (Fin (n * n)) => T ⊆ lfPhysModes ε) _ (fun T => by simp)]`. Use `Finset.sum_congr rfl fun T _ => ?_` and prove the remaining obligations.

Simplify using `only [lfMat, lfMatFull, Matrix.submatrix_apply, LinearMap.toMatrix_apply]`.
-/
theorem lfMat_basis (ε : Fin n → Bool) (a b : Fin n) (S : LfIdx ε) :
    sgE ε cpFock cmFock a b (fockBasis n S.1) = ∑ T : LfIdx ε, lfMat ε a b T S • fockBasis n T.1 := by
  have key : sgE ε cpFock cmFock a b (fockBasis n S.1) =
      ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin (n * n)) => T ⊆ lfPhysModes ε),
        (fockBasis n).repr (sgE ε cpFock cmFock a b (fockBasis n S.1)) T • fockBasis n T := by
    conv_lhs => rw [← (fockBasis n).sum_repr (sgE ε cpFock cmFock a b (fockBasis n S.1))]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro T _ hT
    have hT' : ¬ T ⊆ lfPhysModes ε := by simpa using hT
    have h0 := lfMatFull_eq_zero ε a b S.2 hT'
    rw [lfMatFull, LinearMap.toMatrix_apply] at h0
    rw [h0, zero_smul]
  rw [key, Finset.sum_subtype (p := fun T : Finset (Fin (n * n)) => T ⊆ lfPhysModes ε) _ (fun T => by simp)]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [lfMat, lfMatFull, Matrix.submatrix_apply, LinearMap.toMatrix_apply]

/- English proof (translation)
Use extensionality with `T`. Rewrite using `[Matrix.mulVec_single_one, Matrix.col_apply]`. Simplify using `only [lfMat, Matrix.submatrix_apply, lfMatFull, LinearMap.toMatrix_apply]`. Rewrite using `[h, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Pi.smul_apply, Finsupp.single_apply, Pi.single_apply]`. Distinguish the cases in `hTS : T = S`.

Substitute `hTS` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg (fun h' => hTS (Subtype.ext h'.symm)), if_neg hTS]`.
-/
theorem lfMat_mulVec_single (ε : Fin n → Bool) (a b : Fin n) (S : LfIdx ε) (c : ℂ)
    (h : sgE ε cpFock cmFock a b (fockBasis n S.1) = c • fockBasis n S.1) :
    lfMat ε a b *ᵥ Pi.single S 1 = c • Pi.single S 1 := by
  ext T
  rw [Matrix.mulVec_single_one, Matrix.col_apply]
  simp only [lfMat, Matrix.submatrix_apply, lfMatFull, LinearMap.toMatrix_apply]
  rw [h, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Pi.smul_apply, Finsupp.single_apply,
    Pi.single_apply]
  by_cases hTS : T = S
  · subst hTS
    simp
  · rw [if_neg (fun h' => hTS (Subtype.ext h'.symm)), if_neg hTS]

end ReciprocityTheory.ChartRestriction.DS
