import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosOkId
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

noncomputable section

namespace GlobalTheory.ValCmp.Invol

/- English proof (translation)
Use `conv_lhs => rw [f.as_sum]`. Use `conv_rhs => rw [f.as_sum]`. Rewrite using `[map_sum, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hw : Finsupp.weight (colW r n) d = ν` using `hf (mem_support_iff.mp hd)`.

Establish `hs : ∑ i, ν i = ∑ v, d v`. Rewrite using `[← hw, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]`. Simplify using `only [Finset.sum_apply, colW, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.mul_sum]`. Simplify using `[Pi.single_apply]`. Rewrite using `[aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), hs]`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_scale {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {r n : ℕ} (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous (colW r n) f ν) (c : S)
    (x : Fin r × Fin n → S) :
    aeval (fun v => c * x v) f = c ^ (∑ i, ν i) * aeval x f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : Finsupp.weight (colW r n) d = ν := hf (mem_support_iff.mp hd)
  have hs : ∑ i, ν i = ∑ v, d v := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp only [Finset.sum_apply, colW, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.mul_sum]
    simp [Pi.single_apply]
  rw [aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), hs]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

def cofM (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (MP R n) :=
  (genM R n).adjugate.transpose.submatrix id Fin.revPerm

/- English proof (translation)
Use `ext1 a s`. Simplify using `[cofAct, genM, cofM]`.
-/
theorem map_genM (R : Type) [CommRing R] (n : ℕ) :
    (cofAct R n).mapMatrix (genM R n) = cofM R n := by
  ext1 a s
  simp [cofAct, genM, cofM]

/- English proof (translation)
Rewrite using `[cofM, Matrix.det_permute', Matrix.det_transpose, Matrix.det_adjugate]`. Simplify using the standard rewrite rules.
-/
theorem det_cofM (R : Type) [CommRing R] (m : ℕ) :
    (cofM R (m + 1)).det = ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1))) : ℤ) : MP R (m + 1)) *
      (genM R (m + 1)).det ^ m := by
  rw [cofM, Matrix.det_permute', Matrix.det_transpose, Matrix.det_adjugate]
  simp

/- English proof (translation)
Rewrite using `[AlgHom.map_det, map_genM]`.
-/
theorem cofAct_det (R : Type) [CommRing R] (n : ℕ) :
    cofAct R n (genM R n).det = (cofM R n).det := by
  rw [AlgHom.map_det, map_genM]

/- English proof (translation)
Establish `h1 : cofM R n * (genM R n).transpose.submatrix Fin.revPerm id = (genM R n).det • (1 : Matrix _ _ _)`. Rewrite using `[cofM, Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, Matrix.mul_adjugate]`. Simplify using the standard rewrite rules. Establish `h2 : (cofM R n).det • (genM R n).transpose.submatrix Fin.revPerm id = (genM R n).det • (cofM R n).adjugate`. Use `congrArg (fun M => (cofM R n).adjugate * M) h1` as an intermediate fact.

Simplify `this` using `[← Matrix.mul_assoc, Matrix.adjugate_mul]`. Establish `h3 : cofAct R n (cofAct R n (X v)) = (cofM R n).adjugate v.2.rev v.1`. Rewrite using `[← map_genM, ← AlgHom.map_adjugate]`. Simplify using `[cofAct]`. Establish `h4` using `congrFun (congrFun h2 v.2.rev) v.1`.

Rewrite using `[h3]`. Simplify `h4.symm` using `[genM]`.
-/
theorem det_mul_cofAct_cofAct_X (R : Type) [CommRing R] (n : ℕ) (v : Fin n × Fin n) :
    (genM R n).det * cofAct R n (cofAct R n (X v)) = (cofM R n).det * X v := by
  have h1 : cofM R n * (genM R n).transpose.submatrix Fin.revPerm id = (genM R n).det • (1 : Matrix _ _ _) := by
    rw [cofM, Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, Matrix.mul_adjugate]
    simp
  have h2 : (cofM R n).det • (genM R n).transpose.submatrix Fin.revPerm id =
      (genM R n).det • (cofM R n).adjugate := by
    have := congrArg (fun M => (cofM R n).adjugate * M) h1
    simpa [← Matrix.mul_assoc, Matrix.adjugate_mul] using this
  have h3 : cofAct R n (cofAct R n (X v)) = (cofM R n).adjugate v.2.rev v.1 := by
    rw [← map_genM, ← AlgHom.map_adjugate]
    simp [cofAct]
  have h4 := congrFun (congrFun h2 v.2.rev) v.1
  rw [h3]
  simpa [genM] using h4.symm

/- English proof (translation)
Establish `h1 : cofAct R n (cofAct R n f) = aeval (fun v => cofAct R n (cofAct R n (X v))) f`. Establish `: (cofAct R n).comp (cofAct R n) = aeval (fun v => cofAct R n (cofAct R n (X v)))` using `by ext1 v; simp`. Conclude with `DFunLike.congr_fun this f`. Rewrite using `[h1, ← aeval_scale ν f hf]`. Simplify using `only [det_mul_cofAct_cofAct_X]`.

Rewrite using `[aeval_scale ν f hf, aeval_X_left_apply]`.
-/
theorem cofAct_cofAct (R : Type) [CommRing R] (n : ℕ) (ν : Fin n → ℕ) (f : MP R n)
    (hf : IsWeightedHomogeneous (colW n n) f ν) :
    (genM R n).det ^ (∑ i, ν i) * cofAct R n (cofAct R n f) = (cofM R n).det ^ (∑ i, ν i) * f := by
  have h1 : cofAct R n (cofAct R n f) = aeval (fun v => cofAct R n (cofAct R n (X v))) f := by
    have : (cofAct R n).comp (cofAct R n) = aeval (fun v => cofAct R n (cofAct R n (X v))) := by
      ext1 v; simp
    exact DFunLike.congr_fun this f
  rw [h1, ← aeval_scale ν f hf]
  simp only [det_mul_cofAct_cofAct_X]
  rw [aeval_scale ν f hf, aeval_X_left_apply]

/- English proof (translation)
Use `⟨Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1))) ^ ν 0, fun f hf g hg => ?_⟩` and prove the remaining obligations. Establish `hD : (genM R (m + 1)).det ≠ 0` using `Matrix.det_mvPolynomialX_ne_zero (Fin (m + 1)) R`. Establish `hδ : ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1))) : ℤ) : MP R (m + 1)) ≠ 0`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1)))) with h | h <;> simp [h]`. Establish `hC : (cofM R (m + 1)).det ≠ 0`.

Rewrite using `[det_cofM]`. Conclude with `mul_ne_zero hδ (pow_ne_zero _ hD)`. Establish `hle : ν 0 ≤ ∑ i, ν i` using `Finset.single_le_sum (fun i _ => Nat.zero_le (ν i)) (Finset.mem_univ _)`. Establish `hd0 : nuDual ν 0 = ν 0` using `by simp [nuDual, h0]`. Establish `hle' : nuDual ν 0 ≤ ∑ i, nuDual ν i` using `Finset.single_le_sum (fun i _ => Nat.zero_le (nuDual ν i)) (Finset.mem_univ _)`.

Establish `hsum : ∑ i, nuDual ν i + ∑ i, ν i = (m + 1) * ν 0`. Rewrite using `[← Equiv.sum_comp Fin.revPerm ν, ← Finset.sum_add_distrib]`. Establish `: ∀ i : Fin (m + 1), nuDual ν i + ν (Fin.revPerm i) = ν 0` using `fun i => Nat.sub_add_cancel (hν (Fin.zero_le i.rev))`. Simplify using `only [this]`. Simplify using the standard rewrite rules.

Establish `hexp : ∑ i, ν i + (∑ i, nuDual ν i - nuDual ν 0) = m * ν 0`. Rewrite `hsum` using `[add_mul]`. Use linear arithmetic over natural numbers and integers. Establish `h1` using `cofAct_cofAct R (m + 1) ν f hf.1`. Unfold `CofRel at hg ⊢`.

Rewrite `h1` using `[← hg, map_mul, map_pow, cofAct_det]`. Take `⟨e, he⟩` from `Nat.exists_eq_add_of_le hle`. Establish `he' : ∑ i, ν i - ν 0 = e` using `by omega`. Rewrite `h1` using `[he']`. Establish `h2 : (genM R (m + 1)).det ^ (∑ i, ν i) * cofAct R (m + 1) g = (cofM R (m + 1)).det ^ ν 0 * f`.

Apply `mul_left_cancel₀ (pow_ne_zero e hC)` to reduce the goal to its premises. Rewrite using `[mul_left_comm, h1, he]`. Expand and normalize the polynomial expressions, which then agree. Apply `mul_left_cancel₀ (pow_ne_zero (∑ i, ν i) hD)` to reduce the goal to its premises. Rewrite using `[h2, ← mul_assoc, ← pow_add, hexp, det_cofM, mul_pow, pow_mul]`.

Simplify using `only [Units.val_pow_eq_pow_val, zsmul_eq_mul, Int.cast_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cofRel_invol (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (hν : Antitone ν)
    (h0 : ν (Fin.last m) = 0) :
    ∃ ε : ℤˣ, ∀ f ∈ dualWeyl R (m + 1) (m + 1) ν, ∀ g : MP R (m + 1),
      CofRel R m ν f g → CofRel R m (nuDual ν) g ((ε : ℤ) • f) := by
  refine ⟨Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1))) ^ ν 0, fun f hf g hg => ?_⟩
  have hD : (genM R (m + 1)).det ≠ 0 := Matrix.det_mvPolynomialX_ne_zero (Fin (m + 1)) R
  have hδ : ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1))) : ℤ) : MP R (m + 1)) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1)))) with h | h <;> simp [h]
  have hC : (cofM R (m + 1)).det ≠ 0 := by
    rw [det_cofM]; exact mul_ne_zero hδ (pow_ne_zero _ hD)
  have hle : ν 0 ≤ ∑ i, ν i := Finset.single_le_sum (fun i _ => Nat.zero_le (ν i)) (Finset.mem_univ _)
  have hd0 : nuDual ν 0 = ν 0 := by simp [nuDual, h0]
  have hle' : nuDual ν 0 ≤ ∑ i, nuDual ν i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (nuDual ν i)) (Finset.mem_univ _)
  have hsum : ∑ i, nuDual ν i + ∑ i, ν i = (m + 1) * ν 0 := by
    rw [← Equiv.sum_comp Fin.revPerm ν, ← Finset.sum_add_distrib]
    have : ∀ i : Fin (m + 1), nuDual ν i + ν (Fin.revPerm i) = ν 0 :=
      fun i => Nat.sub_add_cancel (hν (Fin.zero_le i.rev))
    simp only [this]
    simp
  have hexp : ∑ i, ν i + (∑ i, nuDual ν i - nuDual ν 0) = m * ν 0 := by
    rw [add_mul] at hsum; omega
  have h1 := cofAct_cofAct R (m + 1) ν f hf.1
  unfold CofRel at hg ⊢
  rw [← hg, map_mul, map_pow, cofAct_det] at h1
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
  have he' : ∑ i, ν i - ν 0 = e := by omega
  rw [he'] at h1
  have h2 : (genM R (m + 1)).det ^ (∑ i, ν i) * cofAct R (m + 1) g = (cofM R (m + 1)).det ^ ν 0 * f := by
    apply mul_left_cancel₀ (pow_ne_zero e hC)
    rw [mul_left_comm, h1, he]
    ring
  apply mul_left_cancel₀ (pow_ne_zero (∑ i, ν i) hD)
  rw [h2, ← mul_assoc, ← pow_add, hexp, det_cofM, mul_pow, pow_mul]
  simp only [Units.val_pow_eq_pow_val, zsmul_eq_mul, Int.cast_pow]
  ring

end GlobalTheory.ValCmp.Invol
