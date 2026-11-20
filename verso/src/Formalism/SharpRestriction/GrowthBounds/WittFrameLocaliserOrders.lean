import Formalism.SharpRestriction.GrowthBounds.SourceCleaning
import Formalism.PolynomialDimension.DetMulEqSumAdjugate
import Formalism.SubspaceCounting.ChoiceOfTopsRefined
import Formalism.GrowthSums.LemmaATwoFactList
import Formalism.PolynomialDimension.FinalNum

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.G.WittFrameLocaliserOrders

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning

section InWj

variable {O : Type*} [CommRing O] [IsDomain O] {σ : Type*} {w : O}

/- English proof (translation)
Introduce `m` and use `⟨0, by simp⟩`.
-/
theorem inWj_zero (j : ℕ) : InWj w (0 : MvPolynomial σ (KK O)) j := fun m => ⟨0, by simp⟩

/- English proof (translation)
Introduce `m` and use `by obtain ⟨a, ha⟩ := hP m obtain ⟨b, hb⟩ := hQ m exact ⟨a + b, by rw [coeff_add, ha, hb, ← map_add]; ring_nf⟩`.
-/
theorem inWj_add {P Q : MvPolynomial σ (KK O)} {j : ℕ} (hP : InWj w P j) (hQ : InWj w Q j) :
    InWj w (P + Q) j := fun m => by
  obtain ⟨a, ha⟩ := hP m
  obtain ⟨b, hb⟩ := hQ m
  exact ⟨a + b, by rw [coeff_add, ha, hb, ← map_add]; ring_nf⟩

/- English proof (translation)
Introduce `m` and use `by obtain ⟨a, ha⟩ := hP m exact ⟨-a, by rw [coeff_neg, ha, ← map_neg]; ring_nf⟩`.
-/
theorem inWj_neg {P : MvPolynomial σ (KK O)} {j : ℕ} (hP : InWj w P j) : InWj w (-P) j := fun m => by
  obtain ⟨a, ha⟩ := hP m
  exact ⟨-a, by rw [coeff_neg, ha, ← map_neg]; ring_nf⟩

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `inWj_add hP (inWj_neg hQ)`.
-/
theorem inWj_sub {P Q : MvPolynomial σ (KK O)} {j : ℕ} (hP : InWj w P j) (hQ : InWj w Q j) :
    InWj w (P - Q) j := by
  rw [sub_eq_add_neg]; exact inWj_add hP (inWj_neg hQ)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using inWj_zero j`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `inWj_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem inWj_sum {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial σ (KK O)) {j : ℕ}
    (h : ∀ i ∈ s, InWj w (P i) j) : InWj w (∑ i ∈ s, P i) j := by
  induction s using Finset.induction_on with
  | empty => simpa using inWj_zero j
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact inWj_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Introduce `m` and use `by obtain ⟨a, ha⟩ := hP m refine ⟨w ^ (i - j) * a, ?_⟩ rw [ha, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hij]`.
-/
theorem inWj_mono {P : MvPolynomial σ (KK O)} {i j : ℕ} (hij : j ≤ i) (hP : InWj w P i) : InWj w P j := fun m => by
  obtain ⟨a, ha⟩ := hP m
  refine ⟨w ^ (i - j) * a, ?_⟩
  rw [ha, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hij]

/- English proof (translation)
Introduce `m` and use `by choose a ha using hP choose b hb using hQ refine ⟨∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, a x.1 * b x.2, ?_⟩ rw [coeff_mul, Finset.mul_sum, map_sum] refine Finset.sum_congr rfl fun x _ => ?_ rw [ha, hb, ← map_mul] congr 1 ring`.
-/
theorem inWj_mul {P Q : MvPolynomial σ (KK O)} {i j : ℕ} (hP : InWj w P i) (hQ : InWj w Q j) :
    InWj w (P * Q) (i + j) := fun m => by
  choose a ha using hP
  choose b hb using hQ
  refine ⟨∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, a x.1 * b x.2, ?_⟩
  rw [coeff_mul, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ha, hb, ← map_mul]
  congr 1
  ring

/- English proof (translation)
Introduce `m` and use `by by_cases h : 0 = m · exact ⟨1, by simp [coeff_one, h]⟩ · exact ⟨0, by simp [coeff_one, h]⟩`.
-/
theorem inWj_one : InWj w (1 : MvPolynomial σ (KK O)) 0 := fun m => by
  by_cases h : 0 = m
  · exact ⟨1, by simp [coeff_one, h]⟩
  · exact ⟨0, by simp [coeff_one, h]⟩

/- English proof (translation)
Introduce `m` and use `by by_cases h : 0 = m · exact ⟨c, by rw [coeff_C, if_pos h]⟩ · exact ⟨0, by rw [coeff_C, if_neg h]; simp⟩`.
-/
theorem inWj_C (j : ℕ) (c : O) : InWj w (C (algebraMap O (KK O) (w ^ j * c)) : MvPolynomial σ (KK O)) j := fun m => by
  by_cases h : 0 = m
  · exact ⟨c, by rw [coeff_C, if_pos h]⟩
  · exact ⟨0, by rw [coeff_C, if_neg h]; simp⟩

/- English proof (translation)
Use `inWj_C (σ := σ) (w := w) 1 1` as an intermediate fact. Simplify using `using this`.
-/
theorem inWj_Cw : InWj w (C (algebraMap O (KK O) w) : MvPolynomial σ (KK O)) 1 := by
  have := inWj_C (σ := σ) (w := w) 1 1
  simpa using this

/- English proof (translation)
Use `inWj_C (σ := σ) (w := w) j 1` as an intermediate fact. Simplify using `using this`.
-/
theorem inWj_Cpow (j : ℕ) : InWj w (C (algebraMap O (KK O) (w ^ j)) : MvPolynomial σ (KK O)) j := by
  have := inWj_C (σ := σ) (w := w) j 1
  simpa using this

/- English proof (translation)
Use `inWj_C (σ := σ) (w := w) 0 c` as an intermediate fact. Simplify using `using this`.
-/
theorem integral_constant_mem_order_zero (c : O) : InWj w (C (algebraMap O (KK O) c) : MvPolynomial σ (KK O)) 0 := by
  have := inWj_C (σ := σ) (w := w) 0 c
  simpa using this

/- English proof (translation)
Introduce `m` and use `by by_cases h : Finsupp.single v 1 = m · exact ⟨1, by simp [coeff_X, h]⟩ · exact ⟨0, by simp [coeff_X, h]⟩`.
-/
theorem inWj_X (v : σ) : InWj w (X v : MvPolynomial σ (KK O)) 0 := fun m => by
  by_cases h : Finsupp.single v 1 = m
  · exact ⟨1, by simp [coeff_X, h]⟩
  · exact ⟨0, by simp [coeff_X, h]⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using inWj_one`. Consider the case `succ n ih`. Rewrite using `[pow_succ, Nat.succ_mul]`. Conclude with `inWj_mul ih hP`.
-/
theorem inWj_pow {P : MvPolynomial σ (KK O)} {i : ℕ} (hP : InWj w P i) (n : ℕ) : InWj w (P ^ n) (n * i) := by
  induction n with
  | zero => simpa using inWj_one
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact inWj_mul ih hP

/- English proof (translation)
Simplify using `using inWj_pow hP n`.
-/
theorem inWPow_zero_pow {P : MvPolynomial σ (KK O)} (hP : InWj w P 0) (n : ℕ) : InWj w (P ^ n) 0 := by
  simpa using inWj_pow hP n

/- English proof (translation)
Simplify using `using inWj_mul hP hQ`.
-/
theorem inWPow_zero_mul {P Q : MvPolynomial σ (KK O)} (hP : InWj w P 0) (hQ : InWj w Q 0) : InWj w (P * Q) 0 := by
  simpa using inWj_mul hP hQ

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using inWj_one`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `inWj_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem inWj_prod {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial σ (KK O)) (e : ι → ℕ)
    (h : ∀ i ∈ s, InWj w (P i) (e i)) : InWj w (∏ i ∈ s, P i) (∑ i ∈ s, e i) := by
  induction s using Finset.induction_on with
  | empty => simpa using inWj_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact inWj_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Simplify using `using inWj_prod s P (fun _ => 0) h`.
-/
theorem inWj_prod0 {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial σ (KK O))
    (h : ∀ i ∈ s, InWj w (P i) 0) : InWj w (∏ i ∈ s, P i) 0 := by
  simpa using inWj_prod s P (fun _ => 0) h

/- English proof (translation)
Introduce `m` and use `⟨h.coeff m, by simp [coeff_map]⟩`.
-/
theorem inWj_map (h : MvPolynomial σ O) : InWj w (MvPolynomial.map (algebraMap O (KK O)) h) 0 := fun m =>
  ⟨h.coeff m, by simp [coeff_map]⟩

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `inWj_sum _ _ fun s _ => ?_` and prove the remaining obligations. Break down `Int.units_eq_one_or (Equiv.Perm.sign s) with hs | hs` into its components or cases. Rewrite using `[hs, one_smul]`. Conclude with `inWj_prod0 _ _ fun i _ => h _ _`.

Rewrite using `[hs, Units.neg_smul, one_smul]`. Conclude with `inWj_neg (inWj_prod0 _ _ fun i _ => h _ _)`.
-/
theorem inWj_det {n : ℕ} (M : Matrix (Fin n) (Fin n) (MvPolynomial σ (KK O))) (h : ∀ i j, InWj w (M i j) 0) :
    InWj w M.det 0 := by
  rw [Matrix.det_apply]
  refine inWj_sum _ _ fun s _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign s) with hs | hs
  · rw [hs, one_smul]; exact inWj_prod0 _ _ fun i _ => h _ _
  · rw [hs, Units.neg_smul, one_smul]; exact inWj_neg (inWj_prod0 _ _ fun i _ => h _ _)

/- English proof (translation)
Unfold `InA InWj`. Simplify using the standard rewrite rules.
-/
theorem inA_iff_inWj0 (P : MvPolynomial σ (KK O)) : InA P ↔ InWj w P 0 := by
  unfold InA InWj
  simp

/- English proof (translation)
Use `choose a ha using hP`. Use `⟨∑ m ∈ P.support, monomial m (a m), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum] conv_rhs => rw [P.as_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[map_monomial, ha]`.

Simplify using the standard rewrite rules. Introduce `v hv`. Use `vars_sum_subset P.support (fun m => monomial m (a m)) hv` as an intermediate fact. Rewrite `this` using `[Finset.mem_biUnion]`. Take `⟨m, hm, hvm⟩` from `this`.

Take `⟨d, hd, hvd⟩` from `(mem_vars v).1 hvm`. Establish `hdm : d = m` using `Finset.mem_singleton.1 (support_monomial_subset hd)`. Substitute `hdm` using the available equality. Conclude with `(mem_vars v).2 ⟨d, hm, hvd⟩`.
-/
theorem exists_map_of_inWj0 {P : MvPolynomial σ (KK O)} (hP : InWj w P 0) :
    ∃ h : MvPolynomial σ O, MvPolynomial.map (algebraMap O (KK O)) h = P ∧ h.vars ⊆ P.vars := by
  choose a ha using hP
  refine ⟨∑ m ∈ P.support, monomial m (a m), ?_, ?_⟩
  · rw [map_sum]
    conv_rhs => rw [P.as_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_monomial, ha]; simp
  · intro v hv
    have := vars_sum_subset P.support (fun m => monomial m (a m)) hv
    rw [Finset.mem_biUnion] at this
    obtain ⟨m, hm, hvm⟩ := this
    obtain ⟨d, hd, hvd⟩ := (mem_vars v).1 hvm
    have hdm : d = m := Finset.mem_singleton.1 (support_monomial_subset hd)
    subst hdm
    exact (mem_vars v).2 ⟨d, hm, hvd⟩

end InWj

section Sig

variable {p : ℕ} [Fact p.Prime] {O : Type*} [CommRing O] [IsDomain O]

/- English proof (translation)
Use extensionality with `a b`. Both sides reduce to the same expression.
-/
theorem sigMat_eq_map {f : ℕ} [Algebra (WF p f) O] {k : ℕ} (g : Matrix (Fin k) (Fin k) (WF p f)) (s : ℤ) :
    sigMat p f O g s =
      g.map (((algebraMap O (KK O)).comp (algebraMap (WF p f) O)).comp (sigPow p f s)) := by
  ext a b; rfl

/- English proof (translation)
Rewrite using `[sigMat_eq_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `hg.map _`.
-/
theorem sigMat_det_isUnit {f : ℕ} [Algebra (WF p f) O] {k : ℕ} {g : Matrix (Fin k) (Fin k) (WF p f)}
    (hg : IsGLW g) (s : ℤ) : IsUnit (sigMat p f O g s).det := by
  rw [sigMat_eq_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact hg.map _

/- English proof (translation)
Establish `hn : (0 : ℤ) < n'` using `by exact_mod_cast NeZero.pos n'`. Establish `h0 : 0 ≤ a % (n' : ℤ)` using `Int.emod_nonneg _ hn.ne'`. Establish `h1 : a % (n' : ℤ) < n'` using `Int.emod_lt_of_pos _ hn`. Unfold `posOf`. Simplify using `only`.

Establish `: (a % (n' : ℤ)).toNat < n'` using `by omega`. Rewrite using `[Nat.mod_eq_of_lt this]`. Use linear arithmetic over natural numbers and integers.
-/
theorem posOf_val (n' : ℕ) [NeZero n'] (a : ℤ) : ((posOf n' a).val : ℤ) = a % (n' : ℤ) := by
  have hn : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
  have h0 : 0 ≤ a % (n' : ℤ) := Int.emod_nonneg _ hn.ne'
  have h1 : a % (n' : ℤ) < n' := Int.emod_lt_of_pos _ hn
  unfold posOf
  simp only
  have : (a % (n' : ℤ)).toNat < n' := by omega
  rw [Nat.mod_eq_of_lt this]
  omega

/- English proof (translation)
Use extensionality with `i j`. Unfold `sigMat sigPow`. Rewrite using `[posOf_val, Int.emod_emod_of_dvd _ (dvd_refl _)]`.
-/
theorem sigMat_posOf {n' : ℕ} [NeZero n'] [Algebra (WF p n') O] {k : ℕ} (g : Matrix (Fin k) (Fin k) (WF p n'))
    (a : ℤ) : sigMat p n' O g ((posOf n' a).val : ℤ) = sigMat p n' O g a := by
  ext i j
  unfold sigMat sigPow
  rw [posOf_val, Int.emod_emod_of_dvd _ (dvd_refl _)]

/- English proof (translation)
Establish `h` using `posOf_val n' a`. Establish `h2 : Even ((posOf n' a).val : ℤ) ↔ Even a`. Rewrite using `[h]`. Take `⟨m, hm⟩` from `hn`. Establish `: (n' : ℤ) = 2 * m` using `by push_cast [hm]; ring`.

Rewrite using `[Int.even_iff, Int.even_iff, this, Int.emod_emod_of_dvd _ (Dvd.intro _ rfl)]`. Rewrite using `[← h2]`. Conclude with `(Int.even_coe_nat _).symm`.
-/
theorem posOf_even {n' : ℕ} [NeZero n'] (hn : Even n') (a : ℤ) : Even (posOf n' a).val ↔ Even a := by
  have h := posOf_val n' a
  have h2 : Even ((posOf n' a).val : ℤ) ↔ Even a := by
    rw [h]
    obtain ⟨m, hm⟩ := hn
    have : (n' : ℤ) = 2 * m := by push_cast [hm]; ring
    rw [Int.even_iff, Int.even_iff, this, Int.emod_emod_of_dvd _ (Dvd.intro _ rfl)]
  rw [← h2]
  exact (Int.even_coe_nat _).symm

variable {n' : ℕ} [NeZero n'] [Algebra (WF p n') O] {k : ℕ}

def newVar (w : O) (r : ℕ) (v : TV n' k) : MvPolynomial (TV n' k) (KK O) :=
  if IsNormal r v then C (algebraMap O (KK O) w) * X v else X v

/- English proof (translation)
Unfold `subst liftSubst`. Rewrite using `[aeval_X]`. Simplify using `only [LLT, hs, decide_true, if_true]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [newVar, IsNormal, hs, if_true]`.
-/
theorem subst_X_even (w : O) (r : ℕ) (g : Matrix (Fin k) (Fin k) (WF p n')) (s : Fin n') (hs : Even s.val)
    (c : Fin k) : subst p n' O w n' r g (X (s, c)) =
      ∑ b : Fin k, newVar w r (s, b) * C ((sigMat p n' O g (s.val : ℤ))⁻¹ b c) := by
  unfold subst liftSubst
  rw [aeval_X]
  simp only [LLT, hs, decide_true, if_true]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [newVar, IsNormal, hs, if_true]

/- English proof (translation)
Unfold `subst liftSubst`. Rewrite using `[aeval_X]`. Simplify using `only [LLT, hs, decide_false, Bool.false_eq_true, if_false]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [newVar, IsNormal, hs, if_false]`.
-/
theorem subst_X_odd (w : O) (r : ℕ) (g : Matrix (Fin k) (Fin k) (WF p n')) (s : Fin n') (hs : ¬ Even s.val)
    (c : Fin k) : subst p n' O w n' r g (X (s, c)) =
      ∑ b : Fin k, newVar w r (s, b) * C (sigMat p n' O g (s.val : ℤ) c b) := by
  unfold subst liftSubst
  rw [aeval_X]
  simp only [LLT, hs, decide_false, Bool.false_eq_true, if_false]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [newVar, IsNormal, hs, if_false]

/- English proof (translation)
Establish `hs : Even (posOf n' a).val` using `(posOf_even hn a).2 ha`. Unfold `xg`. Rewrite using `[map_sum]`. Simplify using `only [map_mul, subst_X_even w r g _ hs, sigMat_posOf]`. Establish `hC : ∀ x : KK O, subst p n' O w n' r g (C x) = C x` using `fun x => by`.

Unfold `subst`. Conclude with `(liftSubst p n' O w r (LLT n') g).commutes x`. Simplify using `only [hC, Finset.sum_mul, mul_assoc, ← C_mul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.mul_sum, ← map_sum]`.

Establish `hinv : ∀ b' : Fin k, ∑ c : Fin k, (sigMat p n' O g a)⁻¹ b' c * sigMat p n' O g a c b = (1 : Matrix (Fin k) (Fin k) (KK O)) b' b` using `fun b' => by`. Rewrite using `[← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (sigMat_det_isUnit hg a)]`. Simplify using `only [hinv, Matrix.one_apply]`. Rewrite using `[Finset.sum_eq_single b]`. Simplify using the standard rewrite rules.

Introduce `b' _ hb'`. Simplify using `[hb']`. Introduce `h`. Conclude with `absurd (Finset.mem_univ b) h`.
-/
theorem subst_xg (w : O) (r : ℕ) {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (hn : Even n') (a : ℤ)
    (ha : Even a) (b : Fin k) :
    subst p n' O w n' r g (xg p n' O n' g a b) = newVar w r (posOf n' a, b) := by
  have hs : Even (posOf n' a).val := (posOf_even hn a).2 ha
  unfold xg
  rw [map_sum]
  simp only [map_mul, subst_X_even w r g _ hs, sigMat_posOf]
  have hC : ∀ x : KK O, subst p n' O w n' r g (C x) = C x := fun x => by
    unfold subst; exact (liftSubst p n' O w r (LLT n') g).commutes x
  simp only [hC, Finset.sum_mul, mul_assoc, ← C_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, ← map_sum]
  have hinv : ∀ b' : Fin k, ∑ c : Fin k, (sigMat p n' O g a)⁻¹ b' c * sigMat p n' O g a c b =
      (1 : Matrix (Fin k) (Fin k) (KK O)) b' b := fun b' => by
    rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (sigMat_det_isUnit hg a)]
  simp only [hinv, Matrix.one_apply]
  rw [Finset.sum_eq_single b]
  · simp
  · intro b' _ hb'; simp [hb']
  · intro h; exact absurd (Finset.mem_univ b) h

/- English proof (translation)
Establish `hs : ¬ Even (posOf n' a).val` using `fun h => ha ((posOf_even hn a).1 h)`. Unfold `yg`. Rewrite using `[map_sum]`. Simplify using `only [map_mul, subst_X_odd w r g _ hs, sigMat_posOf]`. Establish `hC : ∀ x : KK O, subst p n' O w n' r g (C x) = C x` using `fun x => by`.

Unfold `subst`. Conclude with `(liftSubst p n' O w r (LLT n') g).commutes x`. Simplify using `only [hC, Finset.sum_mul, mul_assoc, ← C_mul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.mul_sum, ← map_sum]`.

Establish `hinv : ∀ b' : Fin k, ∑ c : Fin k, sigMat p n' O g a c b' * (sigMat p n' O g a)⁻¹ b c = (1 : Matrix (Fin k) (Fin k) (KK O)) b b'` using `fun b' => by`. Rewrite using `[← Matrix.nonsing_inv_mul _ (sigMat_det_isUnit hg a), Matrix.mul_apply]`. Conclude with `Finset.sum_congr rfl fun c _ => mul_comm _ _`. Simplify using `only [hinv, Matrix.one_apply]`. Rewrite using `[Finset.sum_eq_single b]`.

Simplify using the standard rewrite rules. Introduce `b' _ hb'`. Simplify using `[Ne.symm hb']`. Introduce `h`. Conclude with `absurd (Finset.mem_univ b) h`.
-/
theorem subst_yg (w : O) (r : ℕ) {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (hn : Even n') (a : ℤ)
    (ha : ¬ Even a) (b : Fin k) :
    subst p n' O w n' r g (yg p n' O n' g a b) = newVar w r (posOf n' a, b) := by
  have hs : ¬ Even (posOf n' a).val := fun h => ha ((posOf_even hn a).1 h)
  unfold yg
  rw [map_sum]
  simp only [map_mul, subst_X_odd w r g _ hs, sigMat_posOf]
  have hC : ∀ x : KK O, subst p n' O w n' r g (C x) = C x := fun x => by
    unfold subst; exact (liftSubst p n' O w r (LLT n') g).commutes x
  simp only [hC, Finset.sum_mul, mul_assoc, ← C_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, ← map_sum]
  have hinv : ∀ b' : Fin k, ∑ c : Fin k, sigMat p n' O g a c b' * (sigMat p n' O g a)⁻¹ b c =
      (1 : Matrix (Fin k) (Fin k) (KK O)) b b' := fun b' => by
    rw [← Matrix.nonsing_inv_mul _ (sigMat_det_isUnit hg a), Matrix.mul_apply]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  simp only [hinv, Matrix.one_apply]
  rw [Finset.sum_eq_single b]
  · simp
  · intro b' _ hb'; simp [Ne.symm hb']
  · intro h; exact absurd (Finset.mem_univ b) h

end Sig

end Formalism.MainNotions.G.WittFrameLocaliserOrders

end

noncomputable section
open MvPolynomial Finset Classical
namespace Formalism.MainNotions.G.WittFrameLocaliserOrders
open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning

def entrywisePowerMinor {R : Type} [CommRing R] {r k : ℕ} (x : Fin r → Fin k → R) (e : Fin r → ℕ) (cols : Fin r → Fin k) : R :=
  (Matrix.of fun l i : Fin r => x l (cols i) ^ e l).det

def columnSetMinor {R : Type} [CommRing R] {r k : ℕ} (x : Fin r → Fin k → R) (e : Fin r → ℕ) (I : Finset (Fin k)) : R :=
  if h : I.card = r then entrywisePowerMinor x e (I.orderEmbOfFin h) else 0

def localiserExpression {R : Type} [CommRing R] {r k : ℕ} (x : ℕ → Fin r → Fin k → R) (e : ℕ → Fin r → ℕ) (Q : ℕ → ℕ)
    (J : ℕ) : R :=
  columnSetMinor (x 0) (e 0) (Ifirst r k) * ∏ I ∈ II r k,
    (∏ j ∈ Finset.range J, columnSetMinor (x j) (e j) (Ifirst r k) ^ (Q j - 1) -
      ∏ j ∈ Finset.range J, columnSetMinor (x j) (e j) I ^ (Q j - 1))

/- English proof (translation)
Unfold `entrywisePowerMinor`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `l i`. Simplify using the standard rewrite rules.
-/
theorem ring_hom_map_generalized_minor {R R' : Type} [CommRing R] [CommRing R'] (Ψ : R →+* R') {r k : ℕ} (x : Fin r → Fin k → R)
    (e : Fin r → ℕ) (cols : Fin r → Fin k) :
    Ψ (entrywisePowerMinor x e cols) = entrywisePowerMinor (fun l b => Ψ (x l b)) e cols := by
  unfold entrywisePowerMinor
  rw [RingHom.map_det]
  congr 1
  ext l i
  simp

/- English proof (translation)
Unfold `columnSetMinor`. Use `split_ifs with h`. Conclude with `ring_hom_map_generalized_minor Ψ x e _`. Simplify using the standard rewrite rules.
-/
theorem columnSetMinor_map {R R' : Type} [CommRing R] [CommRing R'] (Ψ : R →+* R') {r k : ℕ} (x : Fin r → Fin k → R)
    (e : Fin r → ℕ) (I : Finset (Fin k)) :
    Ψ (columnSetMinor x e I) = columnSetMinor (fun l b => Ψ (x l b)) e I := by
  unfold columnSetMinor
  split_ifs with h
  · exact ring_hom_map_generalized_minor Ψ x e _
  · simp

/- English proof (translation)
Simplify using `only [localiserExpression, map_mul, map_prod, map_sub, map_pow, columnSetMinor_map]`.
-/
theorem localiserExpression_map {R R' : Type} [CommRing R] [CommRing R'] (Ψ : R →+* R') {r k : ℕ}
    (x : ℕ → Fin r → Fin k → R) (e : ℕ → Fin r → ℕ) (Q : ℕ → ℕ) (J : ℕ) :
    Ψ (localiserExpression x e Q J) = localiserExpression (fun j l b => Ψ (x j l b)) e Q J := by
  simp only [localiserExpression, map_mul, map_prod, map_sub, map_pow, columnSetMinor_map]

/- English proof (translation)
Establish `hcard : (univ.image c).card = r`. Rewrite using `[card_image_of_injective _ hc, card_univ, Fintype.card_fin]`. Establish `hex : ∀ y : Fin r, ∃ y', c y' = (univ.image c).orderEmbOfFin hcard y`. Introduce `y`. Take `⟨a, -, ha⟩` from `Finset.mem_image.mp (Finset.orderEmbOfFin_mem (univ.image c) hcard y)`.

Conclude with `⟨a, ha⟩`. Use `choose f hf using hex`. Establish `hinj : Function.Injective f`. Introduce `a b hab`. Establish `: (univ.image c).orderEmbOfFin hcard a = (univ.image c).orderEmbOfFin hcard b`.

Rewrite using `[← hf, ← hf, hab]`. Conclude with `((univ.image c).orderEmbOfFin hcard).injective this`. Use `⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun R _ x e => ?_⟩` and prove the remaining obligations. Unfold `columnSetMinor`. Rewrite using `[dif_pos hcard]`.

Unfold `entrywisePowerMinor`. Use `Matrix.det_permute' (Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)) (Matrix.of fun l i : Fin r => x l (c i) ^ e l)` as an intermediate fact. Rewrite using `[← this]`. Use `congr 1`. Use extensionality with `l i`.

Simplify using `[hf]`.
-/
theorem columnSetMinor_image_eq_sign {r k : ℕ} (c : Fin r → Fin k) (hc : Function.Injective c) :
    ∃ σ : Equiv.Perm (Fin r), ∀ (R : Type) [CommRing R] (x : Fin r → Fin k → R) (e : Fin r → ℕ),
      columnSetMinor x e (univ.image c) = ((Equiv.Perm.sign σ : ℤˣ) : ℤ) * entrywisePowerMinor x e c := by
  have hcard : (univ.image c).card = r := by
    rw [card_image_of_injective _ hc, card_univ, Fintype.card_fin]
  have hex : ∀ y : Fin r, ∃ y', c y' = (univ.image c).orderEmbOfFin hcard y := by
    intro y
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp (Finset.orderEmbOfFin_mem (univ.image c) hcard y)
    exact ⟨a, ha⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro a b hab
    have : (univ.image c).orderEmbOfFin hcard a = (univ.image c).orderEmbOfFin hcard b := by
      rw [← hf, ← hf, hab]
    exact ((univ.image c).orderEmbOfFin hcard).injective this
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun R _ x e => ?_⟩
  unfold columnSetMinor
  rw [dif_pos hcard]
  unfold entrywisePowerMinor
  have := Matrix.det_permute' (Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj))
    (Matrix.of fun l i : Fin r => x l (c i) ^ e l)
  rw [← this]
  congr 1
  ext l i
  simp [hf]

/- English proof (translation)
Use extensionality with `b`. Simplify using `only [Ifirst, mem_filter, mem_univ, true_and, mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨⟨b.val, h⟩, by ext; simp⟩`.

Introduce and unpack `⟨a, rfl⟩`. Simplify using the standard rewrite rules.
-/
theorem first_columns_eq_image {r k : ℕ} (hrk : r ≤ k) : Ifirst r k = univ.image (Fin.castLE hrk) := by
  ext b
  simp only [Ifirst, mem_filter, mem_univ, true_and, mem_image]
  constructor
  · intro h
    exact ⟨⟨b.val, h⟩, by ext; simp⟩
  · rintro ⟨a, rfl⟩
    simp

/- English proof (translation)
Introduce `a b hab`. Unfold `Formalism.CountingSumsFrames.swapCol at hab`. Apply the tactic sequence `by_cases ha : a = i <;> by_cases hb : b = i`. Rewrite using `[ha, hb]`. It suffices to derive a contradiction.

Rewrite `hab` using `[ha, Function.update_self, Function.update_of_ne hb]`. Use `congrArg Fin.val hab` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers. It suffices to derive a contradiction.

Rewrite `hab` using `[hb, Function.update_self, Function.update_of_ne ha]`. Use `congrArg Fin.val hab` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Rewrite `hab` using `[Function.update_of_ne ha, Function.update_of_ne hb]`.

Conclude with `Fin.castLE_injective hrk hab`.
-/
theorem column_swap_injective {r k : ℕ} (hrk : r ≤ k) (i : Fin r) (c : Fin k) (hc : r ≤ c.val) :
    Function.Injective (Formalism.CountingSumsFrames.swapCol r k hrk i c) := by
  intro a b hab
  unfold Formalism.CountingSumsFrames.swapCol at hab
  by_cases ha : a = i <;> by_cases hb : b = i
  · rw [ha, hb]
  · exfalso
    rw [ha, Function.update_self, Function.update_of_ne hb] at hab
    have := congrArg Fin.val hab
    simp at this
    omega
  · exfalso
    rw [hb, Function.update_self, Function.update_of_ne ha] at hab
    have := congrArg Fin.val hab
    simp at this
    omega
  · rw [Function.update_of_ne ha, Function.update_of_ne hb] at hab
    exact Fin.castLE_injective hrk hab

/- English proof (translation)
Simplify using `only [II, mem_filter, mem_univ, true_and]`. Use `⟨by rw [card_image_of_injective _ (column_swap_injective hrk i c hc), card_univ, Fintype.card_fin], ?_⟩` and prove the remaining obligations. Establish `: univ.image (Formalism.CountingSumsFrames.swapCol r k hrk i c) ∩ Ifirst r k = (univ.erase i).image (Fin.castLE hrk)`. Use extensionality with `b`. Simplify using `only [mem_inter, mem_image, mem_univ, true_and, Ifirst, mem_filter, mem_erase, ne_eq, and_true]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨a, rfl⟩, hb⟩`. Distinguish the cases in `ha : a = i`. It suffices to derive a contradiction. Rewrite `hb` using `[ha]`.

Simplify using `[Formalism.CountingSumsFrames.swapCol] at hb`. Use linear arithmetic over natural numbers and integers. Conclude with `⟨a, ha, by simp [Formalism.CountingSumsFrames.swapCol, Function.update_of_ne ha]⟩`. Introduce and unpack `⟨a, ha, rfl⟩`. Conclude with `⟨⟨a, by simp [Formalism.CountingSumsFrames.swapCol, Function.update_of_ne ha]⟩, by simp⟩`.

Rewrite using `[this, card_image_of_injective _ (Fin.castLE_injective hrk), card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]`.
-/
theorem swapColumn_image_mem {r k : ℕ} (hrk : r ≤ k) (i : Fin r) (c : Fin k) (hc : r ≤ c.val) :
    univ.image (Formalism.CountingSumsFrames.swapCol r k hrk i c) ∈ II r k := by
  simp only [II, mem_filter, mem_univ, true_and]
  refine ⟨by rw [card_image_of_injective _ (column_swap_injective hrk i c hc), card_univ, Fintype.card_fin], ?_⟩
  have : univ.image (Formalism.CountingSumsFrames.swapCol r k hrk i c) ∩ Ifirst r k = (univ.erase i).image (Fin.castLE hrk) := by
    ext b
    simp only [mem_inter, mem_image, mem_univ, true_and, Ifirst, mem_filter, mem_erase, ne_eq, and_true]
    constructor
    · rintro ⟨⟨a, rfl⟩, hb⟩
      by_cases ha : a = i
      · exfalso
        rw [ha] at hb
        simp [Formalism.CountingSumsFrames.swapCol] at hb
        omega
      · exact ⟨a, ha, by simp [Formalism.CountingSumsFrames.swapCol, Function.update_of_ne ha]⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, by simp [Formalism.CountingSumsFrames.swapCol, Function.update_of_ne ha]⟩, by simp⟩
  rw [this, card_image_of_injective _ (Fin.castLE_injective hrk), card_erase_of_mem (mem_univ _), card_univ,
    Fintype.card_fin]

/- English proof (translation)
Break down `Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h` into its components or cases. Simplify using `[h]`. Simplify using `[h, hn.neg_pow]`.
-/
theorem signed_pow_even {A : Type} [CommRing A] {r : ℕ} (σ : Equiv.Perm (Fin r)) (a : A) (n : ℕ) (hn : Even n) :
    ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) * a) ^ n = a ^ n := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simp [h]
  · simp [h, hn.neg_pow]

/- English proof (translation)
Take `⟨σ0, h0⟩` from `columnSetMinor_image_eq_sign (Fin.castLE hrk) (Fin.castLE_injective hrk)`. Unfold `localiserExpression`. Rewrite using `[first_columns_eq_image hrk]`. Break down `mul_eq_zero.mp h with h1 | h1` into its components or cases. Rewrite using `[h0, h1]`.

Simplify using the standard rewrite rules. Take `⟨I, -, hI⟩` from `Finset.prod_eq_zero_iff.mp h1`. Take `⟨σ1, h2⟩` from `columnSetMinor_image_eq_sign _ (column_swap_injective hrk I.1 I.2.1 I.2.2)`. Apply `mul_eq_zero_of_right` to reduce the goal to its premises. Apply `Finset.prod_eq_zero (swapColumn_image_mem hrk I.1 I.2.1 I.2.2)` to reduce the goal to its premises.

Rewrite using `[← hI]`. Use `congr 1`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[h0, signed_pow_even _ _ _ (hQ j)]`.

Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[h2, signed_pow_even _ _ _ (hQ j)]`.
-/
theorem localiserExpression_eq_zero {A : Type} [CommRing A] [IsDomain A] {r k : ℕ} (hrk : r ≤ k) (x : ℕ → Fin r → Fin k → A)
    (e : ℕ → Fin r → ℕ) (Q : ℕ → ℕ) (J : ℕ) (hQ : ∀ j, Even (Q j - 1))
    (h : entrywisePowerMinor (x 0) (e 0) (Fin.castLE hrk) * ∏ I : Formalism.CountingSumsFrames.IIdx r k,
      (∏ j ∈ Finset.range J, entrywisePowerMinor (x j) (e j) (Fin.castLE hrk) ^ (Q j - 1) -
        ∏ j ∈ Finset.range J, entrywisePowerMinor (x j) (e j) (Formalism.CountingSumsFrames.swapCol r k hrk I.1 I.2.1) ^ (Q j - 1)) = 0) :
    localiserExpression x e Q J = 0 := by
  obtain ⟨σ0, h0⟩ := columnSetMinor_image_eq_sign (Fin.castLE hrk) (Fin.castLE_injective hrk)
  unfold localiserExpression
  rw [first_columns_eq_image hrk]
  rcases mul_eq_zero.mp h with h1 | h1
  · rw [h0, h1]; simp
  · obtain ⟨I, -, hI⟩ := Finset.prod_eq_zero_iff.mp h1
    obtain ⟨σ1, h2⟩ := columnSetMinor_image_eq_sign _ (column_swap_injective hrk I.1 I.2.1 I.2.2)
    apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (swapColumn_image_mem hrk I.1 I.2.1 I.2.2)
    rw [← hI]
    congr 1
    · apply Finset.prod_congr rfl
      intro j _
      rw [h0, signed_pow_even _ _ _ (hQ j)]
    · apply Finset.prod_congr rfl
      intro j _
      rw [h2, signed_pow_even _ _ _ (hQ j)]

/- English proof (translation)
Distinguish the cases in `h0 : x = 0`. Conclude with `⟨0, by simp [h0]⟩`. Take `⟨m, b, hb, hxb⟩` from `WittVector.exists_eq_pow_p_mul x h0`. Consider the cases of `m with`. Consider the case `zero`.

It suffices to derive a contradiction. Simplify using `only [pow_zero, one_mul] at hxb`. Substitute `hxb` using the available equality. Conclude with `hb hx`. Consider the case `succ m => exact ⟨(p : WF p f) ^ m * b, by rw [hxb]; ring⟩`.
-/
theorem witt_vector_constant_zero_dvd_p {p f : ℕ} [Fact p.Prime] (x : WF p f) (hx : WittVector.constantCoeff x = 0) :
    ∃ y, x = (p : WF p f) * y := by
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨m, b, hb, hxb⟩ := WittVector.exists_eq_pow_p_mul x h0
  cases m with
  | zero =>
    exfalso
    simp only [pow_zero, one_mul] at hxb
    subst hxb
    exact hb hx
  | succ m => exact ⟨(p : WF p f) ^ m * b, by rw [hxb]; ring⟩

/- English proof (translation)
Establish `hk : RingHom.ker (WittVector.constantCoeff : WF p f →+* GaloisField p f) ≤ RingHom.ker φ`. Introduce `x hx`. Take `⟨y, rfl⟩` from `witt_vector_constant_zero_dvd_p x hx`. Rewrite using `[RingHom.mem_ker, map_mul, hφ, zero_mul]`. Use `⟨(WittVector.constantCoeff : WF p f →+* GaloisField p f).liftOfRightInverse (WittVector.teichmuller p) (fun x => WittVector.teichmuller_coeff_zero p x) ⟨φ, hk⟩, fun x => ?_⟩` and prove the remaining obligations.

Conclude with `RingHom.liftOfRightInverse_comp_apply _ _ _ ⟨φ, hk⟩ x`.
-/
theorem exists_residue_field_factor {p f : ℕ} [Fact p.Prime] {L : Type} [CommRing L] (φ : WF p f →+* L) (hφ : φ (p : WF p f) = 0) :
    ∃ ι : GaloisField p f →+* L, ∀ x, ι (WittVector.constantCoeff x) = φ x := by
  have hk : RingHom.ker (WittVector.constantCoeff : WF p f →+* GaloisField p f) ≤ RingHom.ker φ := by
    intro x hx
    obtain ⟨y, rfl⟩ := witt_vector_constant_zero_dvd_p x hx
    rw [RingHom.mem_ker, map_mul, hφ, zero_mul]
  refine ⟨(WittVector.constantCoeff : WF p f →+* GaloisField p f).liftOfRightInverse (WittVector.teichmuller p)
    (fun x => WittVector.teichmuller_coeff_zero p x) ⟨φ, hk⟩, fun x => ?_⟩
  exact RingHom.liftOfRightInverse_comp_apply _ _ _ ⟨φ, hk⟩ x

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[pow_succ', RingHom.mul_def, RingHom.comp_apply]`. Establish `: WittVector.constantCoeff (WittVector.frobenius (((WittVector.frobenius : WF p f →+* WF p f) ^ m) x)) = (WittVector.constantCoeff (((WittVector.frobenius : WF p f →+* WF p f) ^ m) x)) ^ p` using `WittVector.coeff_frobenius_charP p _ 0`.

Rewrite using `[this, ih, ← pow_mul, pow_succ]`.
-/
theorem constant_coeff_frobenius_pow {p f : ℕ} [Fact p.Prime] (x : WF p f) (m : ℕ) :
    WittVector.constantCoeff (((WittVector.frobenius : WF p f →+* WF p f) ^ m) x) =
      (WittVector.constantCoeff x) ^ p ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply]
    have : WittVector.constantCoeff (WittVector.frobenius (((WittVector.frobenius : WF p f →+* WF p f) ^ m) x)) =
        (WittVector.constantCoeff (((WittVector.frobenius : WF p f →+* WF p f) ^ m) x)) ^ p :=
      WittVector.coeff_frobenius_charP p _ 0
    rw [this, ih, ← pow_mul, pow_succ]

/- English proof (translation)
Establish `hy : y ^ p ^ f = y`. Establish `: Fintype (GaloisField p f)` using `Fintype.ofFinite _`. Use `FiniteField.pow_card y` as an intermediate fact. Rewrite `this` using `[← Nat.card_eq_fintype_card, GaloisField.card p f hf]`. Then use the resulting hypothesis. Proceed by induction on `t with`.

Consider the case `zero => simp`. Consider the case `succ t ih`. Rewrite using `[show m + f * (t + 1) = f + (m + f * t) by ring, pow_add, pow_mul, hy, ih]`.
-/
theorem galois_field_frobenius_period {p f : ℕ} [Fact p.Prime] (hf : f ≠ 0) (y : GaloisField p f) (m t : ℕ) :
    y ^ p ^ (m + f * t) = y ^ p ^ m := by
  have hy : y ^ p ^ f = y := by
    have : Fintype (GaloisField p f) := Fintype.ofFinite _
    have := FiniteField.pow_card y
    rwa [← Nat.card_eq_fintype_card, GaloisField.card p f hf] at this
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show m + f * (t + 1) = f + (m + f * t) by ring, pow_add, pow_mul, hy, ih]

/- English proof (translation)
Introduce `m`. Establish `h1 : IsLocalRing.residue O (P.coeff m) = 0`. Use `congrArg (MvPolynomial.coeff m) hP` as an intermediate fact. Simplify `this` using `[MvPolynomial.coeff_map]`. Establish `h2 : P.coeff m ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.residue_eq_zero_iff _).mp h1`.

Rewrite `h2` using `[S.w_irr.maximalIdeal_eq, Ideal.mem_span_singleton]`. Take `⟨c, hc⟩` from `h2`. Conclude with `⟨c, by rw [MvPolynomial.coeff_map, hc, pow_one]⟩`.
-/
theorem residue_zero_mem_order_one {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) {σ : Type} (P : MvPolynomial σ O) (hP : MvPolynomial.map (IsLocalRing.residue O) P = 0) :
    InWj S.w (MvPolynomial.map (algebraMap O (KK O)) P) 1 := by
  intro m
  have h1 : IsLocalRing.residue O (P.coeff m) = 0 := by
    have := congrArg (MvPolynomial.coeff m) hP
    simpa [MvPolynomial.coeff_map] using this
  have h2 : P.coeff m ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.residue_eq_zero_iff _).mp h1
  rw [S.w_irr.maximalIdeal_eq, Ideal.mem_span_singleton] at h2
  obtain ⟨c, hc⟩ := h2
  exact ⟨c, by rw [MvPolynomial.coeff_map, hc, pow_one]⟩

/- English proof (translation)
Rewrite using `[← Finset.sum_image (f := F) (g := Fin.castLE hrk) (s := univ) (fun a _ b _ hab => Fin.castLE_injective hrk hab), ← first_columns_eq_image hrk, Ifirst, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun b' _ => ?_` and prove the remaining obligations. Distinguish the cases in `hb : r ≤ b'.val`. Rewrite using `[if_pos hb, if_neg (by omega)]`. Rewrite using `[if_neg hb, if_pos (by omega)]`.
-/
theorem sum_ite_first_columns {M : Type} [AddCommMonoid M] {r k : ℕ} (hrk : r ≤ k) (F : Fin k → M) :
    ∑ b' : Fin k, (if r ≤ b'.val then 0 else F b') = ∑ i : Fin r, F (Fin.castLE hrk i) := by
  rw [← Finset.sum_image (f := F) (g := Fin.castLE hrk) (s := univ)
    (fun a _ b _ hab => Fin.castLE_injective hrk hab), ← first_columns_eq_image hrk, Ifirst, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b' _ => ?_
  by_cases hb : r ≤ b'.val
  · rw [if_pos hb, if_neg (by omega)]
  · rw [if_neg hb, if_pos (by omega)]

def integralPrimalRow (p n' : ℕ) [Fact p.Prime] [NeZero n'] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF p n') O]
    (w : O) (r : ℕ) {k : ℕ} (h : Matrix (Fin k) (Fin k) (WF p n')) (a : ℤ) (b : Fin k) :
    MvPolynomial (TV n' k) O :=
  ∑ b' : Fin k, (if r ≤ b'.val then C w * X (posOf n' a, b') else X (posOf n' a, b')) *
    C (algebraMap (WF p n') O (sigPow p n' a (h b' b)))

section Entries

variable {p n' : ℕ} [Fact p.Prime] [NeZero n'] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p n') O] {k : ℕ}

/- English proof (translation)
Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[sigMat_eq_map, sigMat_eq_map, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hg', Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem sigmaMatrix_inv_twisted {g' : Matrix (Fin k) (Fin k) (WF p n')} (hg' : IsGLW g') (s : ℤ) :
    (sigMat p n' O g' s)⁻¹ = sigMat p n' O g'⁻¹ s := by
  apply Matrix.inv_eq_left_inv
  rw [sigMat_eq_map, sigMat_eq_map, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hg',
    Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
Establish `hs : Even (posOf n' a).val` using `(posOf_even hn a).mpr ha`. Establish `hmul : sigMat p n' O (g'⁻¹ * g) a = sigMat p n' O g'⁻¹ a * sigMat p n' O g a`. Simplify using `only [sigMat_eq_map, Matrix.map_mul]`. Unfold `xg integralPrimalRow`. Simplify using `only [map_sum, map_mul, subst_X_even w r g' _ hs, sigMat_posOf, sigmaMatrix_inv_twisted hg', MvPolynomial.algHom_C, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b' _ => ?_` and prove the remaining obligations. Establish `hN : MvPolynomial.map (algebraMap O (KK O)) (if r ≤ b'.val then C w * X (posOf n' a, b') else X (posOf n' a, b')) = newVar w r (posOf n' a, b')`. Unfold `newVar IsNormal`. Simplify using `only [hs, if_true]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hC : MvPolynomial.map (algebraMap O (KK O)) (C (algebraMap (WF p n') O (sigPow p n' a ((g'⁻¹ * g) b' b)))) = (C (sigMat p n' O (g'⁻¹ * g) a b' b) : MvPolynomial (TV n' k) (KK O))`. Rewrite using `[MvPolynomial.map_C]`. Both sides reduce to the same expression. Rewrite using `[hN, hC, hmul, Matrix.mul_apply, map_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, mul_assoc]`. Both sides reduce to the same expression.
-/
theorem subst_twisted_row_even (w : O) (r : ℕ) (g : Matrix (Fin k) (Fin k) (WF p n')) {g' : Matrix (Fin k) (Fin k) (WF p n')}
    (hg' : IsGLW g') (hn : Even n') (a : ℤ) (ha : Even a) (b : Fin k) :
    subst p n' O w n' r g' (xg p n' O n' g a b) =
      MvPolynomial.map (algebraMap O (KK O)) (integralPrimalRow p n' O w r (g'⁻¹ * g) a b) := by
  have hs : Even (posOf n' a).val := (posOf_even hn a).mpr ha
  have hmul : sigMat p n' O (g'⁻¹ * g) a = sigMat p n' O g'⁻¹ a * sigMat p n' O g a := by
    simp only [sigMat_eq_map, Matrix.map_mul]
  unfold xg integralPrimalRow
  simp only [map_sum, map_mul, subst_X_even w r g' _ hs, sigMat_posOf, sigmaMatrix_inv_twisted hg', MvPolynomial.algHom_C,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  have hN : MvPolynomial.map (algebraMap O (KK O))
      (if r ≤ b'.val then C w * X (posOf n' a, b') else X (posOf n' a, b')) = newVar w r (posOf n' a, b') := by
    unfold newVar IsNormal
    simp only [hs, if_true]
    split_ifs <;> simp
  have hC : MvPolynomial.map (algebraMap O (KK O)) (C (algebraMap (WF p n') O (sigPow p n' a ((g'⁻¹ * g) b' b)))) =
      (C (sigMat p n' O (g'⁻¹ * g) a b' b) : MvPolynomial (TV n' k) (KK O)) := by
    rw [MvPolynomial.map_C]; rfl
  rw [hN, hC, hmul, Matrix.mul_apply, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, mul_assoc]
  rfl

/- English proof (translation)
Establish `hw : IsLocalRing.residue O S.w = 0`. Rewrite using `[IsLocalRing.residue_eq_zero_iff, S.w_irr.maximalIdeal_eq]`. Conclude with `Ideal.mem_span_singleton_self _`. Rewrite using `[← sum_ite_first_columns hrk (fun b' => X (posOf n' a, b') * (C (ι (WittVector.constantCoeff (h b' b)))) ^ p ^ m)]`. Unfold `integralPrimalRow`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun b' _ => ?_` and prove the remaining obligations. Establish `hF : IsLocalRing.residue O (algebraMap (WF p n') O (sigPow p n' a (h b' b))) = (ι (WittVector.constantCoeff (h b' b))) ^ p ^ m`. Establish `h1 : WittVector.constantCoeff (sigPow p n' a (h b' b)) = (WittVector.constantCoeff (h b' b)) ^ p ^ m`. Rewrite using `[sigPow, constant_coeff_frobenius_pow, hm, galois_field_frobenius_period (NeZero.ne n')]`.

Rewrite using `[← hι, h1, map_pow]`. Rewrite using `[map_mul, MvPolynomial.map_C, hF]`. Use `split_ifs with hb`. Simplify using `[hw]`. Simplify using the standard rewrite rules.
-/
theorem residue_integral_primal_row [IsDiscreteValuationRing O] (S : UniformizedDVR p O) {r : ℕ} (hrk : r ≤ k)
    (h : Matrix (Fin k) (Fin k) (WF p n')) (a : ℤ) (b : Fin k) (ι : GaloisField p n' →+* FF O)
    (hι : ∀ x, ι (WittVector.constantCoeff x) = IsLocalRing.residue O (algebraMap (WF p n') O x))
    (m t : ℕ) (hm : m = (a % (n' : ℤ)).toNat + n' * t) :
    MvPolynomial.map (IsLocalRing.residue O) (integralPrimalRow p n' O S.w r h a b) =
      ∑ i : Fin r, X (posOf n' a, Fin.castLE hrk i) *
        (C (ι (WittVector.constantCoeff (h (Fin.castLE hrk i) b)))) ^ p ^ m := by
  have hw : IsLocalRing.residue O S.w = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, S.w_irr.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self _
  rw [← sum_ite_first_columns hrk (fun b' => X (posOf n' a, b') *
        (C (ι (WittVector.constantCoeff (h b' b)))) ^ p ^ m)]
  unfold integralPrimalRow
  rw [map_sum]
  refine Finset.sum_congr rfl fun b' _ => ?_
  have hF : IsLocalRing.residue O (algebraMap (WF p n') O (sigPow p n' a (h b' b))) =
      (ι (WittVector.constantCoeff (h b' b))) ^ p ^ m := by
    have h1 : WittVector.constantCoeff (sigPow p n' a (h b' b)) = (WittVector.constantCoeff (h b' b)) ^ p ^ m := by
      rw [sigPow, constant_coeff_frobenius_pow, hm, galois_field_frobenius_period (NeZero.ne n')]
    rw [← hι, h1, map_pow]
  rw [map_mul, MvPolynomial.map_C, hF]
  split_ifs with hb
  · simp [hw]
  · simp

end Entries

section FramesLemmas

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ}

/- English proof (translation)
Introduce `i' hii'`. Proceed by induction on `i', hii' using Nat.le_induction with`. Consider the case `base => intro _`. Conclude with `le_refl _`. Consider the case `succ m _ ih`.

Introduce `hm`. Conclude with `le_trans (ih (by omega)) (le_of_lt (hV.2.2.1 j m hm))`.
-/
theorem frame_entries_monotone (hV : Fr.Valid L₁ N₁) (j : ℤ) (i : ℕ) : ∀ i' : ℕ, i ≤ i' → i' < r → Fr.fr j i ≤ Fr.fr j i' := by
  intro i' hii'
  induction i', hii' using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ m _ ih =>
    intro hm
    exact le_trans (ih (by omega)) (le_of_lt (hV.2.2.1 j m hm))

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Establish `h1` using `frame_entries_monotone hV (j : ℤ) 0 (r - 1) (Nat.zero_le _) (by omega)`.

Establish `h2` using `hV.2.2.2.1 (j : ℤ)`. Use `push_cast`. Use linear arithmetic over natural numbers and integers.
-/
theorem frame_first_entry_monotone (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) : ∀ j : ℕ, Fr.fr 0 0 ≤ Fr.fr (j : ℤ) 0 := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 := frame_entries_monotone hV (j : ℤ) 0 (r - 1) (Nat.zero_le _) (by omega)
    have h2 := hV.2.2.2.1 (j : ℤ)
    push_cast
    omega

end FramesLemmas

/- English proof (translation)
Simplify using `only [Rloc, Del, minorI, twRow, localiserExpression, columnSetMinor, entrywisePowerMinor, Nat.cast_zero]`.
-/
theorem localiser_eq_expression (p f : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF p f) O] {n' r : ℕ}
    [NeZero n'] (Fr : Frames n' r) {k : ℕ} (g : Matrix (Fin k) (Fin k) (WF p f)) :
    Rloc p f O Fr g = localiserExpression (fun (j : ℕ) (l : Fin r) (b : Fin k) => xg p f O n' g (Fr.fr (j : ℤ) l.val) b)
      (fun (j : ℕ) (l : Fin r) => p ^ (zF Fr (j : ℤ) - Fr.fr (j : ℤ) l.val).toNat) (fun j : ℕ => Qj Fr p (j : ℤ)) Fr.J := by
  simp only [Rloc, Del, minorI, twRow, localiserExpression, columnSetMinor, entrywisePowerMinor, Nat.cast_zero]

def LocaliserNonzeroOffPlane : Prop :=
  ∀ (p n' r k : ℕ) [Fact p.Prime], r ≤ k → ∀ g g' : Matrix (Fin k) (Fin k) (WF p n'), IsGLW g → IsGLW g' →
    ratPlane p n' r g' ≠ ratPlane p n' r g →
    ∃ i c : Fin k, i.val < r ∧ r ≤ c.val ∧ WittVector.constantCoeff ((g'⁻¹ * g) i c) ≠ 0

/- English proof (translation)
Introduce `p n' r k _ _ O _ _ _ _ S hO hH Fr L₁ N₁ hV g g' hg hg' hne`. Take `⟨hp13, hr2, hrk, hn2, hnE⟩` from `hH`. Establish `hφ : ((IsLocalRing.residue O).comp (algebraMap (WF p n') O)) (p : WF p n') = 0`. Rewrite using `[RingHom.comp_apply, map_natCast, IsLocalRing.residue_eq_zero_iff]`. Conclude with `S.p_mem`.

Take `⟨ι, hι⟩` from `exists_residue_field_factor _ hφ`. Establish `hι' : ∀ x, ι (WittVector.constantCoeff x) = IsLocalRing.residue O (algebraMap (WF p n') O x)` using `hι`. Take `⟨i0, c0, hi0, hc0, hne0⟩` from `hPl p n' r k hrk g g' hg hg' hne`. Establish `hn0 : (0 : ℤ) < n'` using `by exact_mod_cast NeZero.pos n'`. Take `⟨s0, q0, hs0, hs0le⟩ : ∃ s0 q0 : ℤ, s0 = n' * q0 ∧ s0 ≤ Fr.fr 0 0` from `⟨n' * (Fr.fr 0 0 / n'), Fr.fr 0 0 / n', rfl, Int.mul_ediv_self_le hn0.ne'⟩`.

Establish `hge : ∀ (j : ℕ) (l : Fin r), s0 ≤ Fr.fr (j : ℤ) l.val` using `fun j l => le_trans hs0le (le_trans (frame_first_entry_monotone hV (by omega) j) (frame_entries_monotone hV j 0 l.val (Nat.zero_le _) l.2))`. Establish `hlez : ∀ (j : ℕ) (l : Fin r), Fr.fr (j : ℤ) l.val ≤ zF Fr (j : ℤ)` using `fun j l => frame_entries_monotone hV j l.val (r - 1) (by have := l.2; omega) (by omega)`. Establish `hzz : ∀ j : ℕ, zF Fr (j : ℤ) ≤ zF Fr ((j : ℤ) + 1)` using `fun j => by`. Establish `h1` using `hV.2.2.2.1 (j : ℤ)`. Establish `h2` using `frame_entries_monotone hV ((j : ℤ) + 1) 0 (r - 1) (Nat.zero_le _) (by omega)`.

Unfold `zF`. Use linear arithmetic over natural numbers and integers. Establish `hzge : ∀ j : ℕ, s0 ≤ zF Fr (j : ℤ)` using `fun j => le_trans (hge j ⟨0, by omega⟩) (hlez j ⟨0, by omega⟩)`. Set `pos : ℕ → Fin r → ℕ` to `fun j l => (Fr.fr (j : ℤ) l.val - s0).toNat`. Set `z : ℕ → ℕ` to `fun j => (zF Fr (j : ℤ) - s0).toNat`.

Set `H : Matrix (Fin r) (Fin k) (GaloisField p n')` to `fun i c => WittVector.constantCoeff ((g'⁻¹ * g) (Fin.castLE hrk i) c)`. Set `t : ℕ → Fin r → Fin r → MvPolynomial (TV n' k) (FF O)` to `fun j l i => X (posOf n' (Fr.fr (j : ℤ) l.val), Fin.castLE hrk i)`. Set `_ : Algebra (GaloisField p n') (MvPolynomial (TV n' k) (FF O))` to `(C.comp ι).toAlgebra`. Establish `: Fintype (GaloisField p n')` using `Fintype.ofFinite _`. Establish `hcard : Fintype.card (GaloisField p n') = p ^ n'`.

Rewrite using `[← Nat.card_eq_fintype_card, GaloisField.card p n' (NeZero.ne n')]`. Establish `core` using `Formalism.CountingSumsFrames.Top.localizerVanishes p (GaloisField p n') n' r k Fr.J hrk hcard z (fun j _ => by`. Establish `h1` using `hzz j`. Establish `h2` using `hzge j`. Use `show (zF Fr (j : ℤ) - s0).toNat ≤ (zF Fr ((j + 1 : ℕ) : ℤ) - s0).toNat`.

Use `push_cast`. Use the proof step `omega)`. Use the proof step `(by`. Establish `h1` using `hV.2.1 0 (r - 1)`. Establish `h2` using `hzge 0`.

Use `show (zF Fr (Fr.J : ℤ) - s0).toNat = (zF Fr ((0 : ℕ) : ℤ) - s0).toNat + n'`. Unfold `zF at h2 ⊢`. Simplify using `only [zero_add, Nat.cast_zero] at h1 h2 ⊢`. Use the proof step `omega)`. Use `pos`.

Use the proof step `(fun j _ l => by`. Establish `h1` using `hlez j l`. Use `show (Fr.fr (j : ℤ) l.val - s0).toNat ≤ (zF Fr (j : ℤ) - s0).toNat`. Use the proof step `omega)`. Use `H ⟨⟨i0.val, hi0⟩, c0, hc0, hne0⟩ (MvPolynomial (TV n' k) (FF O)) t`.

Use `show InWj S.w ((subst p n' O S.w n' r g').toRingHom (Rloc p n' O Fr g)) 1`. Rewrite using `[localiser_eq_expression, localiserExpression_map]`. Establish `e1 : (fun (j : ℕ) (l : Fin r) (b : Fin k) => (subst p n' O S.w n' r g').toRingHom (xg p n' O n' g (Fr.fr (j : ℤ) l.val) b)) = fun (j : ℕ) (l : Fin r) (b : Fin k) => (MvPolynomial.map (algebraMap O (KK O))) (integralPrimalRow p n' O S.w r (g'⁻¹ * g) (Fr.fr (j : ℤ) l.val) b)`. Use function extensionality and compare the values at `j l b`. Conclude with `subst_twisted_row_even S.w r g hg' hnE _ (hV.2.2.2.2.1 j l.val l.2).2 b`.

Rewrite using `[e1, ← localiserExpression_map (MvPolynomial.map (algebraMap O (KK O)))]`. Apply `residue_zero_mem_order_one S` to reduce the goal to its premises. Rewrite using `[localiserExpression_map]`. Establish `hodd : Odd p` using `(Fact.out : p.Prime).odd_of_ne_two (by omega)`. Establish `ex : (fun (j : ℕ) (l : Fin r) (b : Fin k) => (MvPolynomial.map (IsLocalRing.residue O)) (integralPrimalRow p n' O S.w r (g'⁻¹ * g) (Fr.fr (j : ℤ) l.val) b)) = fun (j : ℕ) (l : Fin r) (b : Fin k) => Formalism.CountingSumsFrames.frameRow p r k (H.map (algebraMap (GaloisField p n') …`.

Use function extensionality and compare the values at `j l b`. Establish `hmod : ∃ u : ℕ, pos j l = (Fr.fr (j : ℤ) l.val % (n' : ℤ)).toNat + n' * u`. Establish `h1` using `hge j l`. Establish `h2 : 0 ≤ Fr.fr (j : ℤ) l.val / (n' : ℤ) - q0`. Establish `: q0 ≤ Fr.fr (j : ℤ) l.val / (n' : ℤ)`.

Rewrite using `[Int.le_ediv_iff_mul_le hn0]`. Rewrite `h1` using `[hs0]`. Combine the linear relations using `[mul_comm (n' : ℤ) q0]`. Use linear arithmetic over natural numbers and integers. Use `⟨(Fr.fr (j : ℤ) l.val / (n' : ℤ) - q0).toNat, ?_⟩` and prove the remaining obligations.

Establish `h3` using `Int.emod_add_mul_ediv (Fr.fr (j : ℤ) l.val) (n' : ℤ)`. Establish `h4` using `Int.emod_nonneg (Fr.fr (j : ℤ) l.val) hn0.ne'`. Establish `h5 : ((pos j l : ℕ) : ℤ) = Fr.fr (j : ℤ) l.val - s0` using `Int.toNat_of_nonneg (by omega)`. Establish `h6 : (((Fr.fr (j : ℤ) l.val % (n' : ℤ)).toNat + n' * (Fr.fr (j : ℤ) l.val / (n' : ℤ) - q0).toNat : ℕ) : ℤ) = Fr.fr (j : ℤ) l.val % (n' : ℤ) + n' * (Fr.fr (j : ℤ) l.val / (n' : ℤ) - q0)`. Use `push_cast`.

Rewrite using `[Int.toNat_of_nonneg h4, Int.toNat_of_nonneg h2]`. Establish `: ((pos j l : ℕ) : ℤ) = (((Fr.fr (j : ℤ) l.val % (n' : ℤ)).toNat + n' * (Fr.fr (j : ℤ) l.val / (n' : ℤ) - q0).toNat : ℕ) : ℤ)`. Rewrite using `[h5, h6, hs0]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `this` after adjusting the coercions.

Take `⟨u, hu⟩` from `hmod`. Rewrite using `[residue_integral_primal_row S hrk _ _ _ ι hι' (pos j l) u hu]`. Simplify using `only [Formalism.CountingSumsFrames.frameRow, Matrix.vecMul, dotProduct, Matrix.map_apply]`. Both sides reduce to the same expression. Establish `ee : (fun (j : ℕ) (l : Fin r) => p ^ (zF Fr (j : ℤ) - Fr.fr (j : ℤ) l.val).toNat) = fun (j : ℕ) (l : Fin r) => p ^ (z j - pos j l)`.

Use function extensionality and compare the values at `j l`. Establish `h1` using `hge j l`. Establish `h2` using `hlez j l`. Use `congr 1`. Use `show (zF Fr (j : ℤ) - Fr.fr (j : ℤ) l.val).toNat = (zF Fr (j : ℤ) - s0).toNat - (Fr.fr (j : ℤ) l.val - s0).toNat`.

Use linear arithmetic over natural numbers and integers. Establish `eQ : (fun j : ℕ => Qj Fr p (j : ℤ)) = fun j : ℕ => p ^ (z (j + 1) - z j)`. Use function extensionality and compare the values at `j`. Establish `h1` using `hzge j`. Establish `h2` using `hzz j`.

Unfold `Qj`. Use `congr 1`. Use `show (zF Fr ((j : ℤ) + 1) - zF Fr (j : ℤ)).toNat = (zF Fr ((j + 1 : ℕ) : ℤ) - s0).toNat - (zF Fr (j : ℤ) - s0).toNat`. Use `push_cast`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[ex, ee, eQ]`. Apply `localiserExpression_eq_zero hrk _ _ _ _ (fun j => by` to reduce the goal to its premises. Take `⟨u, hu⟩` from `(hodd.pow : Odd (p ^ (z (j + 1) - z j)))`. Conclude with `⟨u, by omega⟩)`. Conclude with `core`.
-/
theorem localiser_vanishing_of_distinct_planes (D : Formalism.BasicNotions.D7) (hPl : LocaliserNonzeroOffPlane) : Conclusion1 D := by
  intro p n' r k _ _ O _ _ _ _ S hO hH Fr L₁ N₁ hV g g' hg hg' hne
  obtain ⟨hp13, hr2, hrk, hn2, hnE⟩ := hH
  have hφ : ((IsLocalRing.residue O).comp (algebraMap (WF p n') O)) (p : WF p n') = 0 := by
    rw [RingHom.comp_apply, map_natCast, IsLocalRing.residue_eq_zero_iff]
    exact S.p_mem
  obtain ⟨ι, hι⟩ := exists_residue_field_factor _ hφ
  have hι' : ∀ x, ι (WittVector.constantCoeff x) = IsLocalRing.residue O (algebraMap (WF p n') O x) := hι
  obtain ⟨i0, c0, hi0, hc0, hne0⟩ := hPl p n' r k hrk g g' hg hg' hne
  have hn0 : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
  obtain ⟨s0, q0, hs0, hs0le⟩ : ∃ s0 q0 : ℤ, s0 = n' * q0 ∧ s0 ≤ Fr.fr 0 0 :=
    ⟨n' * (Fr.fr 0 0 / n'), Fr.fr 0 0 / n', rfl, Int.mul_ediv_self_le hn0.ne'⟩
  have hge : ∀ (j : ℕ) (l : Fin r), s0 ≤ Fr.fr (j : ℤ) l.val := fun j l =>
    le_trans hs0le (le_trans (frame_first_entry_monotone hV (by omega) j) (frame_entries_monotone hV j 0 l.val (Nat.zero_le _) l.2))
  have hlez : ∀ (j : ℕ) (l : Fin r), Fr.fr (j : ℤ) l.val ≤ zF Fr (j : ℤ) := fun j l =>
    frame_entries_monotone hV j l.val (r - 1) (by have := l.2; omega) (by omega)
  have hzz : ∀ j : ℕ, zF Fr (j : ℤ) ≤ zF Fr ((j : ℤ) + 1) := fun j => by
    have h1 := hV.2.2.2.1 (j : ℤ)
    have h2 := frame_entries_monotone hV ((j : ℤ) + 1) 0 (r - 1) (Nat.zero_le _) (by omega)
    unfold zF
    omega
  have hzge : ∀ j : ℕ, s0 ≤ zF Fr (j : ℤ) := fun j => le_trans (hge j ⟨0, by omega⟩) (hlez j ⟨0, by omega⟩)
  let pos : ℕ → Fin r → ℕ := fun j l => (Fr.fr (j : ℤ) l.val - s0).toNat
  let z : ℕ → ℕ := fun j => (zF Fr (j : ℤ) - s0).toNat
  let H : Matrix (Fin r) (Fin k) (GaloisField p n') :=
    fun i c => WittVector.constantCoeff ((g'⁻¹ * g) (Fin.castLE hrk i) c)
  let t : ℕ → Fin r → Fin r → MvPolynomial (TV n' k) (FF O) :=
    fun j l i => X (posOf n' (Fr.fr (j : ℤ) l.val), Fin.castLE hrk i)
  let _ : Algebra (GaloisField p n') (MvPolynomial (TV n' k) (FF O)) := (C.comp ι).toAlgebra
  have : Fintype (GaloisField p n') := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p n') = p ^ n' := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p n' (NeZero.ne n')]
  have core := Formalism.CountingSumsFrames.Top.localizerVanishes p (GaloisField p n') n' r k Fr.J hrk hcard z
    (fun j _ => by
      have h1 := hzz j
      have h2 := hzge j
      show (zF Fr (j : ℤ) - s0).toNat ≤ (zF Fr ((j + 1 : ℕ) : ℤ) - s0).toNat
      push_cast
      omega)
    (by
      have h1 := hV.2.1 0 (r - 1)
      have h2 := hzge 0
      show (zF Fr (Fr.J : ℤ) - s0).toNat = (zF Fr ((0 : ℕ) : ℤ) - s0).toNat + n'
      unfold zF at h2 ⊢
      simp only [zero_add, Nat.cast_zero] at h1 h2 ⊢
      omega)
    pos
    (fun j _ l => by
      have h1 := hlez j l
      show (Fr.fr (j : ℤ) l.val - s0).toNat ≤ (zF Fr (j : ℤ) - s0).toNat
      omega)
    H ⟨⟨i0.val, hi0⟩, c0, hc0, hne0⟩ (MvPolynomial (TV n' k) (FF O)) t
  show InWj S.w ((subst p n' O S.w n' r g').toRingHom (Rloc p n' O Fr g)) 1
  rw [localiser_eq_expression, localiserExpression_map]
  have e1 : (fun (j : ℕ) (l : Fin r) (b : Fin k) =>
      (subst p n' O S.w n' r g').toRingHom (xg p n' O n' g (Fr.fr (j : ℤ) l.val) b)) =
      fun (j : ℕ) (l : Fin r) (b : Fin k) => (MvPolynomial.map (algebraMap O (KK O)))
        (integralPrimalRow p n' O S.w r (g'⁻¹ * g) (Fr.fr (j : ℤ) l.val) b) := by
    funext j l b
    exact subst_twisted_row_even S.w r g hg' hnE _ (hV.2.2.2.2.1 j l.val l.2).2 b
  rw [e1, ← localiserExpression_map (MvPolynomial.map (algebraMap O (KK O)))]
  apply residue_zero_mem_order_one S
  rw [localiserExpression_map]
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have ex : (fun (j : ℕ) (l : Fin r) (b : Fin k) => (MvPolynomial.map (IsLocalRing.residue O))
        (integralPrimalRow p n' O S.w r (g'⁻¹ * g) (Fr.fr (j : ℤ) l.val) b)) =
      fun (j : ℕ) (l : Fin r) (b : Fin k) => Formalism.CountingSumsFrames.frameRow p r k
        (H.map (algebraMap (GaloisField p n') (MvPolynomial (TV n' k) (FF O)))) (pos j l) (t j l) b := by
    funext j l b
    have hmod : ∃ u : ℕ, pos j l = (Fr.fr (j : ℤ) l.val % (n' : ℤ)).toNat + n' * u := by
      have h1 := hge j l
      have h2 : 0 ≤ Fr.fr (j : ℤ) l.val / (n' : ℤ) - q0 := by
        have : q0 ≤ Fr.fr (j : ℤ) l.val / (n' : ℤ) := by
          rw [Int.le_ediv_iff_mul_le hn0]
          rw [hs0] at h1
          linarith [mul_comm (n' : ℤ) q0]
        omega
      refine ⟨(Fr.fr (j : ℤ) l.val / (n' : ℤ) - q0).toNat, ?_⟩
      have h3 := Int.emod_add_mul_ediv (Fr.fr (j : ℤ) l.val) (n' : ℤ)
      have h4 := Int.emod_nonneg (Fr.fr (j : ℤ) l.val) hn0.ne'
      have h5 : ((pos j l : ℕ) : ℤ) = Fr.fr (j : ℤ) l.val - s0 := Int.toNat_of_nonneg (by omega)
      have h6 : (((Fr.fr (j : ℤ) l.val % (n' : ℤ)).toNat + n' * (Fr.fr (j : ℤ) l.val / (n' : ℤ) - q0).toNat : ℕ) : ℤ) =
          Fr.fr (j : ℤ) l.val % (n' : ℤ) + n' * (Fr.fr (j : ℤ) l.val / (n' : ℤ) - q0) := by
        push_cast
        rw [Int.toNat_of_nonneg h4, Int.toNat_of_nonneg h2]
      have : ((pos j l : ℕ) : ℤ) = (((Fr.fr (j : ℤ) l.val % (n' : ℤ)).toNat +
          n' * (Fr.fr (j : ℤ) l.val / (n' : ℤ) - q0).toNat : ℕ) : ℤ) := by
        rw [h5, h6, hs0]
        linarith
      exact_mod_cast this
    obtain ⟨u, hu⟩ := hmod
    rw [residue_integral_primal_row S hrk _ _ _ ι hι' (pos j l) u hu]
    simp only [Formalism.CountingSumsFrames.frameRow, Matrix.vecMul, dotProduct, Matrix.map_apply]
    rfl
  have ee : (fun (j : ℕ) (l : Fin r) => p ^ (zF Fr (j : ℤ) - Fr.fr (j : ℤ) l.val).toNat) =
      fun (j : ℕ) (l : Fin r) => p ^ (z j - pos j l) := by
    funext j l
    have h1 := hge j l
    have h2 := hlez j l
    congr 1
    show (zF Fr (j : ℤ) - Fr.fr (j : ℤ) l.val).toNat = (zF Fr (j : ℤ) - s0).toNat - (Fr.fr (j : ℤ) l.val - s0).toNat
    omega
  have eQ : (fun j : ℕ => Qj Fr p (j : ℤ)) = fun j : ℕ => p ^ (z (j + 1) - z j) := by
    funext j
    have h1 := hzge j
    have h2 := hzz j
    unfold Qj
    congr 1
    show (zF Fr ((j : ℤ) + 1) - zF Fr (j : ℤ)).toNat = (zF Fr ((j + 1 : ℕ) : ℤ) - s0).toNat - (zF Fr (j : ℤ) - s0).toNat
    push_cast
    omega
  rw [ex, ee, eQ]
  apply localiserExpression_eq_zero hrk _ _ _ _ (fun j => by
    obtain ⟨u, hu⟩ := (hodd.pow : Odd (p ^ (z (j + 1) - z j)))
    exact ⟨u, by omega⟩)
  exact core

section Planes

variable {p f r k : ℕ} [Fact p.Prime]

/- English proof (translation)
Unfold `ratPlane`. Use `congr 1`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, hi, rfl⟩`.

Conclude with `⟨⟨i.val, hi⟩, rfl⟩`. Introduce and unpack `⟨i, rfl⟩`. Conclude with `⟨Fin.castLE hrk i, i.2, rfl⟩`.
-/
theorem rational_plane_eq_span (hrk : r ≤ k) (g : Matrix (Fin k) (Fin k) (WF p f)) :
    ratPlane p f r g = Submodule.span (GaloisField p f)
      (Set.range fun i : Fin r => fun c => WittVector.constantCoeff (g⁻¹ (Fin.castLE hrk i) c)) := by
  unfold ratPlane
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i.val, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.castLE hrk i, i.2, rfl⟩

/- English proof (translation)
Rewrite using `[rational_plane_eq_span hrk]`. Establish `hgi : IsUnit g⁻¹` using `(Matrix.isUnit_nonsing_inv_iff).mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hg)`. Establish `hu : IsUnit ((WittVector.constantCoeff : WF p f →+* GaloisField p f).mapMatrix g⁻¹)` using `hgi.map _`. Establish `hli` using `Matrix.linearIndependent_rows_of_isUnit hu`. Establish `h2` using `hli.comp (Fin.castLE hrk) (Fin.castLE_injective hrk)`.

Establish `h3` using `finrank_span_eq_card h2`. Rewrite `h3` using `[Fintype.card_fin]`. Conclude with `h3`.
-/
theorem rational_plane_finrank (hrk : r ≤ k) {g : Matrix (Fin k) (Fin k) (WF p f)} (hg : IsGLW g) :
    Module.finrank (GaloisField p f) (ratPlane p f r g) = r := by
  rw [rational_plane_eq_span hrk]
  have hgi : IsUnit g⁻¹ := (Matrix.isUnit_nonsing_inv_iff).mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hg)
  have hu : IsUnit ((WittVector.constantCoeff : WF p f →+* GaloisField p f).mapMatrix g⁻¹) := hgi.map _
  have hli := Matrix.linearIndependent_rows_of_isUnit hu
  have h2 := hli.comp (Fin.castLE hrk) (Fin.castLE_injective hrk)
  have h3 := finrank_span_eq_card h2
  rw [Fintype.card_fin] at h3
  exact h3

/- English proof (translation)
Introduce `p n' r k _ hrk g g' hg hg' hne`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `hne` to reduce the goal to its premises. Apply `Submodule.eq_of_le_of_finrank_eq` to reduce the goal to its premises.

Rewrite using `[rational_plane_eq_span hrk g', Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `hdec : g'⁻¹ = (g'⁻¹ * g) * g⁻¹`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.mul_one]`. Establish `e : (fun c => WittVector.constantCoeff (g'⁻¹ (Fin.castLE hrk i) c)) = ∑ d : Fin k, WittVector.constantCoeff ((g'⁻¹ * g) (Fin.castLE hrk i) d) • (fun c => WittVector.constantCoeff (g⁻¹ d c))`.

Use function extensionality and compare the values at `c`. Use `conv_lhs => rw [hdec]`. Rewrite using `[Matrix.mul_apply, map_sum]`. Simplify using `[Finset.sum_apply, map_mul]`. Use `show (fun c => WittVector.constantCoeff (g'⁻¹ (Fin.castLE hrk i) c)) ∈ ratPlane p n' r g`.

Rewrite using `[e]`. Apply `Submodule.sum_mem` to reduce the goal to its premises. Introduce `d _`. Distinguish the cases in `hd : d.val < r`. Apply `Submodule.smul_mem` to reduce the goal to its premises.

Conclude with `Submodule.subset_span ⟨d, hd, rfl⟩`. Rewrite using `[hcon (Fin.castLE hrk i) d i.2 (not_lt.mp hd), zero_smul]`. Conclude with `Submodule.zero_mem _`. Rewrite using `[rational_plane_finrank hrk hg, rational_plane_finrank hrk hg']`.
-/
theorem localiser_nonzero_off_plane : LocaliserNonzeroOffPlane := by
  intro p n' r k _ hrk g g' hg hg' hne
  by_contra hcon
  push Not at hcon
  apply hne
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [rational_plane_eq_span hrk g', Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hdec : g'⁻¹ = (g'⁻¹ * g) * g⁻¹ := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.mul_one]
    have e : (fun c => WittVector.constantCoeff (g'⁻¹ (Fin.castLE hrk i) c)) =
        ∑ d : Fin k, WittVector.constantCoeff ((g'⁻¹ * g) (Fin.castLE hrk i) d) •
          (fun c => WittVector.constantCoeff (g⁻¹ d c)) := by
      funext c
      conv_lhs => rw [hdec]
      rw [Matrix.mul_apply, map_sum]
      simp [Finset.sum_apply, map_mul]
    show (fun c => WittVector.constantCoeff (g'⁻¹ (Fin.castLE hrk i) c)) ∈ ratPlane p n' r g
    rw [e]
    apply Submodule.sum_mem
    intro d _
    by_cases hd : d.val < r
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨d, hd, rfl⟩
    · rw [hcon (Fin.castLE hrk i) d i.2 (not_lt.mp hd), zero_smul]
      exact Submodule.zero_mem _
  · rw [rational_plane_finrank hrk hg, rational_plane_finrank hrk hg']

end Planes

/- English proof (translation)
The claim follows from `localiser_vanishing_of_distinct_planes D localiser_nonzero_off_plane`.
-/
theorem localiser_vanishing_off_plane (D : Formalism.BasicNotions.D7) : Conclusion1 D := localiser_vanishing_of_distinct_planes D localiser_nonzero_off_plane

end Formalism.MainNotions.G.WittFrameLocaliserOrders

end

noncomputable section

open MvPolynomial Finset Classical Pointwise

namespace Formalism.MainNotions.G.WittFrameLocaliserOrders

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning

/- English proof (translation)
Establish `: Ifirst r k = (Finset.univ : Finset (Fin r)).image (Fin.castLE h)`. Use extensionality with `b`. Simplify using `only [Ifirst, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce `hb`.

Conclude with `⟨⟨b.val, hb⟩, rfl⟩`. Introduce and unpack `⟨a, rfl⟩`. Conclude with `a.2`. Rewrite using `[this, Finset.card_image_of_injective _ (Fin.castLE_injective h), Finset.card_univ, Fintype.card_fin]`.
-/
theorem first_columns_card {r k : ℕ} (h : r ≤ k) : (Ifirst r k).card = r := by
  have : Ifirst r k = (Finset.univ : Finset (Fin r)).image (Fin.castLE h) := by
    ext b
    simp only [Ifirst, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hb; exact ⟨⟨b.val, hb⟩, rfl⟩
    · rintro ⟨a, rfl⟩; exact a.2
  rw [this, Finset.card_image_of_injective _ (Fin.castLE_injective h), Finset.card_univ, Fintype.card_fin]

/- English proof (translation)
Establish `hAc : (Ifirst r k).card = r` using `first_columns_card h`. Establish `hbij : (II r k).card = ((powersetCard (r - 1) (Ifirst r k)) ×ˢ (powersetCard 1 (Ifirst r k)ᶜ)).card`. Use `Finset.card_nbij' (fun I => (I ∩ Ifirst r k, I \ Ifirst r k)) (fun ST => ST.1 ∪ ST.2) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `I hI`. Establish `hI'` using `Finset.mem_coe.1 hI`.

Rewrite `hI'` using `[II, Finset.mem_filter]`. Use `Finset.mem_coe.2 (Finset.mem_product.2 ⟨Finset.mem_powersetCard.2 ⟨Finset.inter_subset_right, hI'.2.2⟩, Finset.mem_powersetCard.2 ⟨?_, ?_⟩⟩)` and prove the remaining obligations. Introduce `x hx`. Conclude with `Finset.mem_compl.2 (Finset.mem_sdiff.1 hx).2`. Use `Finset.card_inter_add_card_sdiff I (Ifirst r k) show (I \ Ifirst r k).card = 1` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Introduce `ST hST`. Establish `hST'` using `Finset.mem_product.1 (Finset.mem_coe.1 hST)`. Take `⟨h1, h2⟩` from `Finset.mem_powersetCard.1 hST'.1`. Take `⟨h3, h4⟩` from `Finset.mem_powersetCard.1 hST'.2`.

Establish `hdisj : Disjoint ST.1 ST.2`. Rewrite using `[Finset.disjoint_left]`. Introduce `x hx hx2`. Conclude with `(Finset.mem_compl.1 (h3 hx2)) (h1 hx)`. Establish `hint : (ST.1 ∪ ST.2) ∩ Ifirst r k = ST.1`.

Use extensionality with `x`. Simplify using `only [Finset.mem_inter, Finset.mem_union]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx | hx, hxA⟩`. Conclude with `hx`.

Conclude with `absurd hxA (Finset.mem_compl.1 (h3 hx))`. Introduce `hx`. Conclude with `⟨Or.inl hx, h1 hx⟩`. Use `Finset.mem_coe.2 ?_` and prove the remaining obligations. Rewrite using `[II, Finset.mem_filter]`.

Use `⟨Finset.mem_univ _, ?_, ?_⟩` and prove the remaining obligations. Use `show (ST.1 ∪ ST.2).card = r`. Rewrite using `[Finset.card_union_of_disjoint hdisj]`. Use linear arithmetic over natural numbers and integers. Use `show ((ST.1 ∪ ST.2) ∩ Ifirst r k).card = r - 1`.

Rewrite using `[hint, h2]`. Introduce `I _ show (I ∩ Ifirst r k) ∪ (I \ Ifirst r k) = I`. Use extensionality with `x`. Simplify using `only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]`. The claim follows by propositional logic.

Introduce `ST hST`. Establish `hST'` using `Finset.mem_product.1 (Finset.mem_coe.1 hST)`. Take `⟨h1, h2⟩` from `Finset.mem_powersetCard.1 hST'.1`. Take `⟨h3, h4⟩` from `Finset.mem_powersetCard.1 hST'.2`. Use `show ((ST.1 ∪ ST.2) ∩ Ifirst r k, (ST.1 ∪ ST.2) \ Ifirst r k) = ST`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use extensionality with `x`. Simplify using `only [Finset.mem_inter, Finset.mem_union]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx | hx, hxA⟩`.

Conclude with `hx`. Conclude with `absurd hxA (Finset.mem_compl.1 (h3 hx))`. Introduce `hx`. Conclude with `⟨Or.inl hx, h1 hx⟩`. Use extensionality with `x`.

Simplify using `only [Finset.mem_sdiff, Finset.mem_union]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx | hx, hxA⟩`. Conclude with `absurd (h1 hx) hxA`. Conclude with `hx`.

Introduce `hx`. Conclude with `⟨Or.inr hx, Finset.mem_compl.1 (h3 hx)⟩`. Rewrite using `[hbij, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard, hAc, Finset.card_compl, Fintype.card_fin, hAc, Nat.choose_one_right]`. Use `congr 1`. Take `⟨m, rfl⟩ : ∃ m, r = m + 1` from `⟨r - 1, by omega⟩`.

Simplify using `[Nat.choose_succ_self_right]`.
-/
theorem card_complement_index_set {r k : ℕ} (h : r ≤ k) (hr : 1 ≤ r) : (II r k).card = r * (k - r) := by
  have hAc : (Ifirst r k).card = r := first_columns_card h
  have hbij : (II r k).card =
      ((powersetCard (r - 1) (Ifirst r k)) ×ˢ (powersetCard 1 (Ifirst r k)ᶜ)).card := by
    refine Finset.card_nbij' (fun I => (I ∩ Ifirst r k, I \ Ifirst r k)) (fun ST => ST.1 ∪ ST.2) ?_ ?_ ?_ ?_
    · intro I hI
      have hI' := Finset.mem_coe.1 hI
      rw [II, Finset.mem_filter] at hI'
      refine Finset.mem_coe.2 (Finset.mem_product.2 ⟨Finset.mem_powersetCard.2 ⟨Finset.inter_subset_right, hI'.2.2⟩,
        Finset.mem_powersetCard.2 ⟨?_, ?_⟩⟩)
      · intro x hx
        exact Finset.mem_compl.2 (Finset.mem_sdiff.1 hx).2
      · have := Finset.card_inter_add_card_sdiff I (Ifirst r k)
        show (I \ Ifirst r k).card = 1
        omega
    · intro ST hST
      have hST' := Finset.mem_product.1 (Finset.mem_coe.1 hST)
      obtain ⟨h1, h2⟩ := Finset.mem_powersetCard.1 hST'.1
      obtain ⟨h3, h4⟩ := Finset.mem_powersetCard.1 hST'.2
      have hdisj : Disjoint ST.1 ST.2 := by
        rw [Finset.disjoint_left]
        intro x hx hx2
        exact (Finset.mem_compl.1 (h3 hx2)) (h1 hx)
      have hint : (ST.1 ∪ ST.2) ∩ Ifirst r k = ST.1 := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hx | hx, hxA⟩
          · exact hx
          · exact absurd hxA (Finset.mem_compl.1 (h3 hx))
        · intro hx; exact ⟨Or.inl hx, h1 hx⟩
      refine Finset.mem_coe.2 ?_
      rw [II, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · show (ST.1 ∪ ST.2).card = r
        rw [Finset.card_union_of_disjoint hdisj]; omega
      · show ((ST.1 ∪ ST.2) ∩ Ifirst r k).card = r - 1
        rw [hint, h2]
    · intro I _
      show (I ∩ Ifirst r k) ∪ (I \ Ifirst r k) = I
      ext x
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      tauto
    · intro ST hST
      have hST' := Finset.mem_product.1 (Finset.mem_coe.1 hST)
      obtain ⟨h1, h2⟩ := Finset.mem_powersetCard.1 hST'.1
      obtain ⟨h3, h4⟩ := Finset.mem_powersetCard.1 hST'.2
      show ((ST.1 ∪ ST.2) ∩ Ifirst r k, (ST.1 ∪ ST.2) \ Ifirst r k) = ST
      refine Prod.ext ?_ ?_
      · ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hx | hx, hxA⟩
          · exact hx
          · exact absurd hxA (Finset.mem_compl.1 (h3 hx))
        · intro hx; exact ⟨Or.inl hx, h1 hx⟩
      · ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hx | hx, hxA⟩
          · exact absurd (h1 hx) hxA
          · exact hx
        · intro hx; exact ⟨Or.inr hx, Finset.mem_compl.1 (h3 hx)⟩
  rw [hbij, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard, hAc, Finset.card_compl,
    Fintype.card_fin, hAc, Nat.choose_one_right]
  congr 1
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  simp [Nat.choose_succ_self_right]

section Graded

variable {O : Type} [CommRing O] [IsDomain O] {n' r k : ℕ} (w : O) (Fr : Frames n' r)

def uniformiserMonomialTerms (E : ℕ) : Set (MvPolynomial (TV n' k) (KK O)) :=
  {T | ∃ (e : ℕ) (nu : TV n' k →₀ ℕ) (H : MvPolynomial (TV n' k) O), E ≤ e ∧
    (∀ v ∈ nu.support, IsNormal r v ∧ v.1 ∈ Fr.TT) ∧ nu.sum (fun _ m => m) ≤ e ∧ InT r H ∧ OnTops Fr H ∧
    T = C (algebraMap O (KK O) (w ^ e)) * monomial nu 1 * MvPolynomial.map (algebraMap O (KK O)) H}

def uniformiserOrderFiltration (E : ℕ) : AddSubmonoid (MvPolynomial (TV n' k) (KK O)) := AddSubmonoid.closure (uniformiserMonomialTerms w Fr E)

/- English proof (translation)
Take `⟨e1, nu1, H1, hE1, hn1, hs1, ht1, ho1, rfl⟩` from `h1`. Take `⟨e2, nu2, H2, hE2, hn2, hs2, ht2, ho2, rfl⟩` from `h2`. Use `⟨e1 + e2, nu1 + nu2, H1 * H2, by omega, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `v hv`. Break down `Finset.mem_union.1 (Finsupp.support_add hv) with h | h` into its components or cases.

Conclude with `hn1 v h`. Conclude with `hn2 v h`. Rewrite using `[Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]`. Use linear arithmetic over natural numbers and integers. Introduce `v hv`.

Break down `Finset.mem_union.1 (vars_mul H1 H2 hv) with h | h` into its components or cases. Conclude with `ht1 v h`. Conclude with `ht2 v h`. Introduce `v hv`. Break down `Finset.mem_union.1 (vars_mul H1 H2 hv) with h | h` into its components or cases.

Conclude with `ho1 v h`. Conclude with `ho2 v h`. Establish `hm : monomial (nu1 + nu2) (1 : KK O) = monomial nu1 1 * monomial nu2 1`. Rewrite using `[monomial_mul, one_mul]`. Simplify using `only [pow_add, map_mul, hm]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem graded_order_mul_mem {E1 E2 : ℕ} {T1 T2 : MvPolynomial (TV n' k) (KK O)} (h1 : T1 ∈ uniformiserMonomialTerms w Fr E1)
    (h2 : T2 ∈ uniformiserMonomialTerms w Fr E2) : T1 * T2 ∈ uniformiserMonomialTerms w Fr (E1 + E2) := by
  obtain ⟨e1, nu1, H1, hE1, hn1, hs1, ht1, ho1, rfl⟩ := h1
  obtain ⟨e2, nu2, H2, hE2, hn2, hs2, ht2, ho2, rfl⟩ := h2
  refine ⟨e1 + e2, nu1 + nu2, H1 * H2, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_union.1 (Finsupp.support_add hv) with h | h
    · exact hn1 v h
    · exact hn2 v h
  · rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]; omega
  · intro v hv
    rcases Finset.mem_union.1 (vars_mul H1 H2 hv) with h | h
    · exact ht1 v h
    · exact ht2 v h
  · intro v hv
    rcases Finset.mem_union.1 (vars_mul H1 H2 hv) with h | h
    · exact ho1 v h
    · exact ho2 v h
  · have hm : monomial (nu1 + nu2) (1 : KK O) = monomial nu1 1 * monomial nu2 1 := by
      rw [monomial_mul, one_mul]
    simp only [pow_add, map_mul, hm]
    ring

/- English proof (translation)
Establish `h` using `AddSubmonoid.mul_mem_mul h1 h2`. Unfold `uniformiserOrderFiltration at h`. Rewrite `h` using `[AddSubmonoid.closure_mul_closure]`. Use `AddSubmonoid.closure_mono ?_ h` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, b, hb, rfl⟩`.

Conclude with `graded_order_mul_mem w Fr ha hb`.
-/
theorem order_filtration_mul {E1 E2 : ℕ} {P1 P2 : MvPolynomial (TV n' k) (KK O)} (h1 : P1 ∈ uniformiserOrderFiltration w Fr E1)
    (h2 : P2 ∈ uniformiserOrderFiltration w Fr E2) : P1 * P2 ∈ uniformiserOrderFiltration w Fr (E1 + E2) := by
  have h := AddSubmonoid.mul_mem_mul h1 h2
  unfold uniformiserOrderFiltration at h
  rw [AddSubmonoid.closure_mul_closure] at h
  refine AddSubmonoid.closure_mono ?_ h
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact graded_order_mul_mem w Fr ha hb

/- English proof (translation)
Use `AddSubmonoid.closure_induction (motive := fun x _ => -x ∈ uniformiserOrderFiltration w Fr E) ?_ ?_ ?_ h` and prove the remaining obligations. Introduce `x hx`. Take `⟨e, nu, H, hE, hn, hs, ht, ho, rfl⟩` from `hx`. Use `AddSubmonoid.subset_closure ⟨e, nu, -H, hE, hn, hs, ?_, ?_, by rw [map_neg]; ring⟩` and prove the remaining obligations. Introduce `v hv`.

Rewrite `hv` using `[vars_neg]`. Conclude with `ht v hv`. Introduce `v hv`. Rewrite `hv` using `[vars_neg]`. Conclude with `ho v hv`.

Simplify using the standard rewrite rules. Introduce `x y _ _ hx hy`. Rewrite using `[neg_add]`. Conclude with `add_mem hx hy`.
-/
theorem order_filtration_neg {E : ℕ} {P : MvPolynomial (TV n' k) (KK O)} (h : P ∈ uniformiserOrderFiltration w Fr E) : -P ∈ uniformiserOrderFiltration w Fr E := by
  refine AddSubmonoid.closure_induction (motive := fun x _ => -x ∈ uniformiserOrderFiltration w Fr E) ?_ ?_ ?_ h
  · intro x hx
    obtain ⟨e, nu, H, hE, hn, hs, ht, ho, rfl⟩ := hx
    refine AddSubmonoid.subset_closure ⟨e, nu, -H, hE, hn, hs, ?_, ?_, by rw [map_neg]; ring⟩
    · intro v hv; rw [vars_neg] at hv; exact ht v hv
    · intro v hv; rw [vars_neg] at hv; exact ho v hv
  · simp
  · intro x y _ _ hx hy
    rw [neg_add]; exact add_mem hx hy

/- English proof (translation)
Use `AddSubmonoid.closure_mono ?_ hP` and prove the remaining obligations. Introduce and unpack `_ ⟨e, nu, H, hE, hr⟩`. Conclude with `⟨e, nu, H, le_trans h hE, hr⟩`.
-/
theorem order_filtration_antitone {E E' : ℕ} (h : E' ≤ E) {P : MvPolynomial (TV n' k) (KK O)} (hP : P ∈ uniformiserOrderFiltration w Fr E) :
    P ∈ uniformiserOrderFiltration w Fr E' := by
  refine AddSubmonoid.closure_mono ?_ hP
  rintro _ ⟨e, nu, H, hE, hr⟩
  exact ⟨e, nu, H, le_trans h hE, hr⟩

/- English proof (translation)
Use `AddSubmonoid.subset_closure ⟨0, 0, 1, le_rfl, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `v hv`. Simplify using `at hv`. Simplify using the standard rewrite rules. Introduce `v hv`.

Simplify using `at hv`. Introduce `v hv`. Simplify using `at hv`. Simplify using the standard rewrite rules.
-/
theorem one_mem_graded_zero : (1 : MvPolynomial (TV n' k) (KK O)) ∈ uniformiserOrderFiltration w Fr 0 := by
  refine AddSubmonoid.subset_closure ⟨0, 0, 1, le_rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv; simp at hv
  · simp
  · intro v hv; simp at hv
  · intro v hv; simp at hv
  · simp

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using one_mem_graded_zero w Fr`. Consider the case `succ n ih`. Rewrite using `[pow_succ, Nat.succ_mul]`. Conclude with `order_filtration_mul w Fr ih h`.
-/
theorem order_filtration_pow {E : ℕ} {P : MvPolynomial (TV n' k) (KK O)} (h : P ∈ uniformiserOrderFiltration w Fr E) (n : ℕ) :
    P ^ n ∈ uniformiserOrderFiltration w Fr (n * E) := by
  induction n with
  | zero => simpa using one_mem_graded_zero w Fr
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact order_filtration_mul w Fr ih h

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using one_mem_graded_zero w Fr`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `order_filtration_mul w Fr (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem order_filtration_prod {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial (TV n' k) (KK O)) (E : ι → ℕ)
    (h : ∀ i ∈ s, P i ∈ uniformiserOrderFiltration w Fr (E i)) : ∏ i ∈ s, P i ∈ uniformiserOrderFiltration w Fr (∑ i ∈ s, E i) := by
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_graded_zero w Fr
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact order_filtration_mul w Fr (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Distinguish the cases in `hb : r ≤ v.2.val`. Establish `hN : IsNormal r v` using `by simp only [IsNormal, he, if_true]; exact hb`. Rewrite using `[if_pos hb]`. Use `order_filtration_antitone w Fr hP (AddSubmonoid.subset_closure ⟨P, Finsupp.single v P, 1, le_rfl, ?_, ?_, ?_, ?_, ?_⟩)` and prove the remaining obligations. Introduce `v' hv'`.

Use `Finset.mem_singleton.1 (Finsupp.support_single_subset hv')` as an intermediate fact. Substitute `this` using the available equality. Conclude with `⟨hN, hv⟩`. Rewrite using `[Finsupp.sum_single_index rfl]`. Introduce `v' hv'`.

Simplify using `at hv'`. Introduce `v' hv'`. Simplify using `at hv'`. Simplify using `only [newVar, hN, if_true]`. Rewrite using `[mul_pow, X_pow_eq_monomial, map_pow, map_pow, (MvPolynomial.map (algebraMap O (KK O))).map_one, mul_one]`.

Establish `hN : ¬ IsNormal r v` using `by simp only [IsNormal, he, if_true]; exact hb`. Rewrite using `[if_neg hb]`. Use `AddSubmonoid.subset_closure ⟨0, 0, X v ^ P, le_rfl, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `v' hv'`. Simplify using `at hv'`.

Simplify using the standard rewrite rules. Introduce `v' hv'`. Establish `h1` using `vars_pow (X v : MvPolynomial (TV n' k) O) P hv'`. Rewrite `h1` using `[vars_X, Finset.mem_singleton]`. Substitute `h1` using the available equality.

Conclude with `⟨he, not_le.1 hb⟩`. Introduce `v' hv'`. Establish `h1` using `vars_pow (X v : MvPolynomial (TV n' k) O) P hv'`. Rewrite `h1` using `[vars_X, Finset.mem_singleton]`. Substitute `h1` using the available equality.

Conclude with `hv`. Simplify using `only [newVar, hN, if_false]`. Simplify using the standard rewrite rules.
-/
theorem newVar_pow_mem_even_top (v : TV n' k) (hv : v.1 ∈ Fr.TT) (he : Even v.1.val) (P : ℕ) (hP : 1 ≤ P) :
    newVar w r v ^ P ∈ uniformiserOrderFiltration w Fr (if r ≤ v.2.val then 1 else 0) := by
  by_cases hb : r ≤ v.2.val
  · have hN : IsNormal r v := by simp only [IsNormal, he, if_true]; exact hb
    rw [if_pos hb]
    refine order_filtration_antitone w Fr hP (AddSubmonoid.subset_closure ⟨P, Finsupp.single v P, 1, le_rfl, ?_, ?_, ?_, ?_, ?_⟩)
    · intro v' hv'
      have := Finset.mem_singleton.1 (Finsupp.support_single_subset hv')
      subst this
      exact ⟨hN, hv⟩
    · rw [Finsupp.sum_single_index rfl]
    · intro v' hv'; simp at hv'
    · intro v' hv'; simp at hv'
    · simp only [newVar, hN, if_true]
      rw [mul_pow, X_pow_eq_monomial, map_pow, map_pow, (MvPolynomial.map (algebraMap O (KK O))).map_one, mul_one]
  · have hN : ¬ IsNormal r v := by simp only [IsNormal, he, if_true]; exact hb
    rw [if_neg hb]
    refine AddSubmonoid.subset_closure ⟨0, 0, X v ^ P, le_rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro v' hv'; simp at hv'
    · simp
    · intro v' hv'
      have h1 := vars_pow (X v : MvPolynomial (TV n' k) O) P hv'
      rw [vars_X, Finset.mem_singleton] at h1
      subst h1
      exact ⟨he, not_le.1 hb⟩
    · intro v' hv'
      have h1 := vars_pow (X v : MvPolynomial (TV n' k) O) P hv'
      rw [vars_X, Finset.mem_singleton] at h1
      subst h1
      exact hv
    · simp only [newVar, hN, if_false]
      simp

end Graded

section Frames2

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ}

/- English proof (translation)
Take `⟨_, _, hstep, _⟩` from `hV`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro _`. Conclude with `le_rfl`.

Consider the case `succ i ih => intro hi; exact le_trans (ih (by omega)) (le_of_lt (hstep j i hi))`.
-/
theorem frame_first_entry_le (hV : Fr.Valid L₁ N₁) (j : ℤ) : ∀ i, i < r → Fr.fr j 0 ≤ Fr.fr j i := by
  obtain ⟨_, _, hstep, _⟩ := hV
  intro i
  induction i with
  | zero => intro _; exact le_rfl
  | succ i ih => intro hi; exact le_trans (ih (by omega)) (le_of_lt (hstep j i hi))

/- English proof (translation)
Establish `h1` using `frame_first_entry_le hV (j + 1) (r - 1) (by omega)`. Take `⟨_, _, _, hnext, _⟩` from `hV`. Establish `h2` using `hnext j`. Establish `h3 : (zF Fr (j + 1) - zF Fr j).toNat ≠ 0`. Unfold `zF`.

Use linear arithmetic over natural numbers and integers. Unfold `Qj`. Conclude with `le_trans hp (Nat.le_self_pow h3 p)`.
-/
theorem two_le_frame_exponent (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) {p : ℕ} (hp : 2 ≤ p) (j : ℤ) : 2 ≤ Qj Fr p j := by
  have h1 := frame_first_entry_le hV (j + 1) (r - 1) (by omega)
  obtain ⟨_, _, _, hnext, _⟩ := hV
  have h2 := hnext j
  have h3 : (zF Fr (j + 1) - zF Fr j).toNat ≠ 0 := by
    unfold zF; omega
  unfold Qj
  exact le_trans hp (Nat.le_self_pow h3 p)

end Frames2

section Main

variable {p n' r k : ℕ} [Fact p.Prime] [NeZero n'] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p n') O]
  (w : O) {Fr : Frames n' r} {L₁ N₁ : ℕ}

/- English proof (translation)
Rewrite `hI` using `[II, Finset.mem_filter]`. Take `⟨_, hIc, hIi⟩` from `hI`. Establish `hfr` using `hV.2.2.2.2.1`. Choose the witnesses or unpack the hypotheses as in `⟨c, hcI, hc⟩ : ∃ c ∈ I, c ∉ Ifirst r k := by`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Establish `: I ∩ Ifirst r k = I` using `Finset.inter_eq_left.2 hcon`. Rewrite `hIi` using `[this]`. Use linear arithmetic over natural numbers and integers. Establish `hc' : r ≤ c.val`.

Simplify `hc` using `[Ifirst]`. Choose the witnesses or unpack the hypotheses as in `⟨i0, hi0⟩ : ∃ i0 : Fin r, I.orderEmbOfFin hIc i0 = c := by`. Establish `: c ∈ Set.range (I.orderEmbOfFin hIc)` using `by rw [Finset.range_orderEmbOfFin]; exact hcI`. Conclude with `this`. Apply the tactic sequence `have hentry : ∀ (l i : Fin r), subst p n' O w n' r g (twRow p n' O Fr g j l.val (I.orderEmbOfFin hIc i)) ∈ uniformiserOrderFiltration (k := k) w Fr (if r ≤ (I.orderEmbOfFin hIc i).val then 1 else 0) := by`.

Introduce `l i`. Unfold `twRow`. Rewrite using `[map_pow, subst_xg w r hg hn _ (hfr j l.val l.2).2]`. Conclude with `newVar_pow_mem_even_top w Fr (posOf n' (Fr.fr j l.val), I.orderEmbOfFin hIc i) (hfr j l.val l.2).1 ((posOf_even hn _).2 (hfr j l.val l.2).2) _ (pow_pos (Fact.out : p.Prime).pos _)`. Establish `hprod : ∀ s : Equiv.Perm (Fin r), ∏ i : Fin r, subst p n' O w n' r g (twRow p n' O Fr g j (s i).val (I.orderEmbOfFin hIc i)) ∈ uniformiserOrderFiltration (k` using `k) w Fr 1 := by`.

Introduce `s`. Apply the tactic sequence `refine order_filtration_antitone w Fr ?_ (order_filtration_prod w Fr Finset.univ _ _ fun i _ => hentry (s i) i)`. Use `Finset.single_le_sum (f := fun i : Fin r => if r ≤ (I.orderEmbOfFin hIc i).val then 1 else 0) (fun i _ => Nat.zero_le _) (Finset.mem_univ i0)` as an intermediate fact. Simplify using `only [hi0, hc', if_true] at this`. Conclude with `this`.

Rewrite using `[minorI, dif_pos hIc, Matrix.det_apply, map_sum]`. Use `sum_mem fun s _ => ?_` and prove the remaining obligations. Break down `Int.units_eq_one_or (Equiv.Perm.sign s) with hs | hs` into its components or cases. Rewrite using `[hs, one_smul, map_prod]`. Conclude with `hprod s`.

Rewrite using `[hs, Units.neg_smul, one_smul, map_neg, map_prod]`. Conclude with `order_filtration_neg w Fr (hprod s)`.
-/
theorem complement_minor_order_pos (hV : Fr.Valid L₁ N₁) (hn : Even n') (hr : 1 ≤ r)
    {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (j : ℤ) {I : Finset (Fin k)} (hI : I ∈ II r k) :
    subst p n' O w n' r g (minorI p n' O Fr g j I) ∈ uniformiserOrderFiltration (k := k) w Fr 1 := by
  rw [II, Finset.mem_filter] at hI
  obtain ⟨_, hIc, hIi⟩ := hI
  have hfr := hV.2.2.2.2.1

  obtain ⟨c, hcI, hc⟩ : ∃ c ∈ I, c ∉ Ifirst r k := by
    by_contra hcon
    push_neg at hcon
    have : I ∩ Ifirst r k = I := Finset.inter_eq_left.2 hcon
    rw [this] at hIi
    omega
  have hc' : r ≤ c.val := by
    simpa [Ifirst] using hc
  obtain ⟨i0, hi0⟩ : ∃ i0 : Fin r, I.orderEmbOfFin hIc i0 = c := by
    have : c ∈ Set.range (I.orderEmbOfFin hIc) := by rw [Finset.range_orderEmbOfFin]; exact hcI
    exact this
  have hentry : ∀ (l i : Fin r), subst p n' O w n' r g (twRow p n' O Fr g j l.val (I.orderEmbOfFin hIc i)) ∈
      uniformiserOrderFiltration (k := k) w Fr (if r ≤ (I.orderEmbOfFin hIc i).val then 1 else 0) := by
    intro l i
    unfold twRow
    rw [map_pow, subst_xg w r hg hn _ (hfr j l.val l.2).2]
    exact newVar_pow_mem_even_top w Fr (posOf n' (Fr.fr j l.val), I.orderEmbOfFin hIc i) (hfr j l.val l.2).1
      ((posOf_even hn _).2 (hfr j l.val l.2).2) _ (pow_pos (Fact.out : p.Prime).pos _)
  have hprod : ∀ s : Equiv.Perm (Fin r),
      ∏ i : Fin r, subst p n' O w n' r g (twRow p n' O Fr g j (s i).val (I.orderEmbOfFin hIc i)) ∈
        uniformiserOrderFiltration (k := k) w Fr 1 := by
    intro s
    refine order_filtration_antitone w Fr ?_ (order_filtration_prod w Fr Finset.univ _ _ fun i _ => hentry (s i) i)
    have := Finset.single_le_sum (f := fun i : Fin r => if r ≤ (I.orderEmbOfFin hIc i).val then 1 else 0)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ i0)
    simp only [hi0, hc', if_true] at this
    exact this
  rw [minorI, dif_pos hIc, Matrix.det_apply, map_sum]
  refine sum_mem fun s _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign s) with hs | hs
  · rw [hs, one_smul, map_prod]
    exact hprod s
  · rw [hs, Units.neg_smul, one_smul, map_neg, map_prod]
    exact order_filtration_neg w Fr (hprod s)

def lemmaOneTerms (p : ℕ) (w : O) (Fr : Frames n' r) (Dl : ℕ → MvPolynomial (TV n' k) (KK O)) :
    Set (MvPolynomial (TV n' k) (KK O)) :=
  {T | ∃ (e : ℕ) (ex : ℕ → ℕ) (nu : TV n' k →₀ ℕ) (H : MvPolynomial (TV n' k) O),
    (1 ≤ e ∧ (∀ v ∈ nu.support, IsNormal r v ∧ v.1 ∈ Fr.TT) ∧ nu.sum (fun _ m => m) ≤ e ∧
      InT r H ∧ OnTops Fr H ∧ ∀ j < Fr.J, (alpha p Fr k j : ℤ) - e ≤ ex j) ∧
    T = C (algebraMap O (KK O) (w ^ e)) * monomial nu 1 * (∏ j ∈ Finset.range Fr.J, Dl j ^ ex j) *
      MvPolynomial.map (algebraMap O (KK O)) H}

/- English proof (translation)
Use `AddSubmonoid.closure_induction (motive := fun x _ => (∏ j ∈ Finset.range Fr.J, Dl j ^ ex j) * x ∈ AddSubmonoid.closure (lemmaOneTerms p w Fr Dl)) ?_ ?_ ?_ hx` and prove the remaining obligations. Introduce `y hy`. Take `⟨e, nu, H, hEe, hn, hs, ht, ho, rfl⟩` from `hy`. Use `AddSubmonoid.subset_closure ⟨e, ex, nu, H, ⟨le_trans hE hEe, hn, hs, ht, ho, ?_⟩, by ring⟩` and prove the remaining obligations. Introduce `j hj`.

Use `hex j hj` as an intermediate fact. Establish `h2 : (E : ℤ) ≤ e` using `by exact_mod_cast hEe`. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Introduce `a b _ _ ha hb`.

Rewrite using `[mul_add]`. Conclude with `add_mem ha hb`.
-/
theorem determinant_powers_lift_into_terms (Dl : ℕ → MvPolynomial (TV n' k) (KK O)) (E : ℕ) (ex : ℕ → ℕ) (hE : 1 ≤ E)
    (hex : ∀ j < Fr.J, (alpha p Fr k j : ℤ) - E ≤ ex j) {x : MvPolynomial (TV n' k) (KK O)}
    (hx : x ∈ uniformiserOrderFiltration w Fr E) :
    (∏ j ∈ Finset.range Fr.J, Dl j ^ ex j) * x ∈ AddSubmonoid.closure (lemmaOneTerms p w Fr Dl) := by
  refine AddSubmonoid.closure_induction
    (motive := fun x _ => (∏ j ∈ Finset.range Fr.J, Dl j ^ ex j) * x ∈ AddSubmonoid.closure (lemmaOneTerms p w Fr Dl))
    ?_ ?_ ?_ hx
  · intro y hy
    obtain ⟨e, nu, H, hEe, hn, hs, ht, ho, rfl⟩ := hy
    refine AddSubmonoid.subset_closure ⟨e, ex, nu, H, ⟨le_trans hE hEe, hn, hs, ht, ho, ?_⟩, by ring⟩
    intro j hj
    have := hex j hj
    have h2 : (E : ℤ) ≤ e := by exact_mod_cast hEe
    omega
  · simp
  · intro a b _ _ ha hb
    rw [mul_add]; exact add_mem ha hb

end Main

/- English proof (translation)
Introduce `p n' r k _ _ O _ _ _ _ S hO hH Fr L₁ N₁ hV g hg`. Take `⟨hp13, hr2, hrk, hn2, hnE⟩` from `hH`. Establish `hJ : 1 ≤ Fr.J` using `hV.1`. Establish `hexp` using `Formalism.CountingSumsFrames.Top.locExpand (MvPolynomial (TV n' k) (KK O)) (↥(II r k)) Fr.J (fun j => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ))) (fun I j => subst p n' O S.w n' r g (minorI p n' O Fr g (j : ℤ) I.1)) (fun j => Qj Fr p (j : ℤ)) hJ`. Establish `hcard : Fintype.card (↥(II r k)) = r * (k - r)`.

Rewrite using `[Fintype.card_coe]; exact card_complement_index_set hrk (by omega)`. Establish `halpha : ∀ j : ℕ, alpha p Fr k (j : ℤ) = (if j = 0 then 1 else 0) + Fintype.card (↥(II r k)) * (Qj Fr p (j : ℤ) - 1)`. Introduce `j`. Rewrite using `[hcard]`. Simplify using `[alpha]`.

Establish `hR : subst p n' O S.w n' r g (Rloc p n' O Fr g) =`. Substitute `p n' O S.w n' r g (Del p n' O Fr g ((0 : ℕ) : ℤ)) * ∏ I : ↥(II r k), (∏ j ∈ Finset.range Fr.J, subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ)) ^ (Qj Fr p (j : ℤ) - 1) - ∏ j ∈ Finset.range Fr.J, subst p n' O S.w n' r g (minorI p n' O Fr g (j : ℤ) I.1) ^ (Qj Fr p (j : ℤ) - 1)) := …` using the available equality. Rewrite using `[Finset.prod_coe_sort (II r k) (fun I => (∏ j ∈ Finset.range Fr.J, subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ)) ^ (Qj Fr p (j : ℤ) - 1) - ∏ j ∈ Finset.range Fr.J, subst p n' O S.w n' r g (minorI p n' O Fr g (j : ℤ) I) ^ (Qj Fr p (j : ℤ) - 1)))]`. Simplify using `only [Rloc, map_mul, map_prod, map_sub, map_pow, Nat.cast_zero]`. Establish `hR0 : subst p n' O S.w n' r g (R0 p n' O Fr g) = (fun T : Finset (↥(II r k)) => (-1) ^ T.card * (∏ j ∈ Finset.range Fr.J, subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ)) ^ ((if j = 0 then 1 else 0) + Fintype.card (↥(II r k)) * (Qj Fr p (j : ℤ) - 1) - T.card * (Qj Fr p (j : ℤ) - …`.

Substitute `p n' O S.w n' r g (minorI p n' O Fr g (j : ℤ) I.1) ^ (Qj Fr p (j : ℤ) - 1)) ∅ := by` using the available equality. Simplify using `only [R0, map_prod, map_pow, Finset.card_empty, pow_zero, one_mul, zero_mul, Nat.sub_zero, Finset.prod_empty, mul_one, halpha]`. Establish `hmem : subst p n' O S.w n' r g (Rloc p n' O Fr g - R0 p n' O Fr g) ∈ AddSubmonoid.closure (lemmaOneTerms p S.w Fr (fun j => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ))))`. Rewrite using `[map_sub, hR, hexp, hR0, ← Finset.sum_erase_eq_sub (Finset.mem_univ ∅)]`. Use `sum_mem fun T hT => ?_` and prove the remaining obligations.

Establish `hTne : T ≠ ∅` using `(Finset.mem_erase.1 hT).1`. Establish `hTc : 1 ≤ T.card` using `Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hTne)`. Establish `hW : (-1) ^ T.card * ∏ I ∈ T, ∏ j ∈ Finset.range Fr.J,`. Substitute `p n' O S.w n' r g (minorI p n' O Fr g (j : ℤ) I.1) ^ (Qj Fr p (j : ℤ) - 1) ∈` using the available equality. Use `uniformiserOrderFiltration (k := k) S.w Fr (∑ _I ∈ T, ∑ j ∈ Finset.range Fr.J, (Qj Fr p (j : ℤ) - 1) * 1) := by`.

Establish `h0 : ∏ I ∈ T, ∏ j ∈ Finset.range Fr.J,`. Substitute `p n' O S.w n' r g (minorI p n' O Fr g (j : ℤ) I.1) ^ (Qj Fr p (j : ℤ) - 1) ∈` using the available equality. Use `uniformiserOrderFiltration (k := k) S.w Fr (∑ _I ∈ T, ∑ j ∈ Finset.range Fr.J, (Qj Fr p (j : ℤ) - 1) * 1) :=`. Use `order_filtration_prod S.w Fr T _ _ fun I _ => order_filtration_prod S.w Fr _ _ _ fun j _ => order_filtration_pow S.w Fr (complement_minor_order_pos S.w hV hnE (by omega) hg (j : ℤ) I.2) _`. Break down `neg_one_pow_eq_or (MvPolynomial (TV n' k) (KK O)) T.card with h | h` into its components or cases.

Rewrite using `[h, one_mul]`. Conclude with `h0`. Rewrite using `[h, neg_one_mul]`. Conclude with `order_filtration_neg S.w Fr h0`. Establish `hEq : ∑ _I ∈ T, ∑ j ∈ Finset.range Fr.J, (Qj Fr p (j : ℤ) - 1) * 1 = T.card * ∑ j ∈ Finset.range Fr.J, (Qj Fr p (j : ℤ) - 1)`.

Simplify using `[Finset.sum_const]`. Establish `hge : ∀ j < Fr.J, T.card * (Qj Fr p (j : ℤ) - 1) ≤ ∑ _I ∈ T, ∑ j ∈ Finset.range Fr.J, (Qj Fr p (j : ℤ) - 1) * 1`. Introduce `j hj`. Rewrite using `[hEq]`. Conclude with `Nat.mul_le_mul_left _ (Finset.single_le_sum (f := fun j : ℕ => Qj Fr p (j : ℤ) - 1) (fun i _ => Nat.zero_le _) (Finset.mem_range.2 hj))`.

Establish `hl` using `determinant_powers_lift_into_terms (p := p) S.w (fun j => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ))) (∑ _I ∈ T, ∑ j ∈ Finset.range Fr.J, (Qj Fr p (j : ℤ) - 1) * 1) (fun j => (if j = 0 then 1 else 0) + Fintype.card (↥(II r k)) * (Qj Fr p (j : ℤ) - 1) - T.card * (Qj Fr p (j …`. Use `hl using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `h0` using `hge 0 (by omega)`. Establish `hq` using `two_le_frame_exponent hV (by omega : 1 ≤ r) (by omega : 2 ≤ p) ((0 : ℕ) : ℤ)`.

Establish `: 1 ≤ T.card * (Qj Fr p ((0 : ℕ) : ℤ) - 1)` using `Nat.mul_pos hTc (by omega)`. Use linear arithmetic over natural numbers and integers. Introduce `j hj`. Establish `h0` using `hge j hj`. Rewrite using `[halpha j]`.

Use linear arithmetic over natural numbers and integers. Take `⟨l, hl, hsum⟩` from `AddSubmonoid.exists_list_of_mem_closure hmem`. Establish `h' : ∀ i : Fin l.length, l[i.1] ∈ lemmaOneTerms p S.w Fr (fun j => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ)))` using `fun i => hl _ (List.getElem_mem i.2)`. Use `choose e ex nu H hc using h'`. Use `⟨l.length, e, ex, nu, H, fun i => (hc i).1, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hsum, ← Fin.sum_univ_getElem]`. Conclude with `Finset.sum_congr rfl fun i _ => (hc i).2`.
-/
theorem localiser_expansion_lemma (D : Formalism.BasicNotions.D7) : Conclusion2 D := by
  intro p n' r k _ _ O _ _ _ _ S hO hH Fr L₁ N₁ hV g hg
  obtain ⟨hp13, hr2, hrk, hn2, hnE⟩ := hH
  have hJ : 1 ≤ Fr.J := hV.1
  have hexp := Formalism.CountingSumsFrames.Top.locExpand (MvPolynomial (TV n' k) (KK O)) (↥(II r k)) Fr.J
    (fun j => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ)))
    (fun I j => subst p n' O S.w n' r g (minorI p n' O Fr g (j : ℤ) I.1)) (fun j => Qj Fr p (j : ℤ)) hJ
  have hcard : Fintype.card (↥(II r k)) = r * (k - r) := by
    rw [Fintype.card_coe]; exact card_complement_index_set hrk (by omega)
  have halpha : ∀ j : ℕ, alpha p Fr k (j : ℤ) =
      (if j = 0 then 1 else 0) + Fintype.card (↥(II r k)) * (Qj Fr p (j : ℤ) - 1) := by
    intro j
    rw [hcard]
    simp [alpha]
  have hR : subst p n' O S.w n' r g (Rloc p n' O Fr g) =
      subst p n' O S.w n' r g (Del p n' O Fr g ((0 : ℕ) : ℤ)) * ∏ I : ↥(II r k),
        (∏ j ∈ Finset.range Fr.J, subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ)) ^ (Qj Fr p (j : ℤ) - 1) -
          ∏ j ∈ Finset.range Fr.J, subst p n' O S.w n' r g (minorI p n' O Fr g (j : ℤ) I.1) ^ (Qj Fr p (j : ℤ) - 1)) := by
    rw [Finset.prod_coe_sort (II r k) (fun I =>
        (∏ j ∈ Finset.range Fr.J, subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ)) ^ (Qj Fr p (j : ℤ) - 1) -
          ∏ j ∈ Finset.range Fr.J, subst p n' O S.w n' r g (minorI p n' O Fr g (j : ℤ) I) ^ (Qj Fr p (j : ℤ) - 1)))]
    simp only [Rloc, map_mul, map_prod, map_sub, map_pow, Nat.cast_zero]
  have hR0 : subst p n' O S.w n' r g (R0 p n' O Fr g) =
      (fun T : Finset (↥(II r k)) => (-1) ^ T.card *
        (∏ j ∈ Finset.range Fr.J, subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ)) ^
          ((if j = 0 then 1 else 0) + Fintype.card (↥(II r k)) * (Qj Fr p (j : ℤ) - 1) - T.card * (Qj Fr p (j : ℤ) - 1))) *
          ∏ I ∈ T, ∏ j ∈ Finset.range Fr.J,
            subst p n' O S.w n' r g (minorI p n' O Fr g (j : ℤ) I.1) ^ (Qj Fr p (j : ℤ) - 1)) ∅ := by
    simp only [R0, map_prod, map_pow, Finset.card_empty, pow_zero, one_mul, zero_mul, Nat.sub_zero,
      Finset.prod_empty, mul_one, halpha]
  have hmem : subst p n' O S.w n' r g (Rloc p n' O Fr g - R0 p n' O Fr g) ∈
      AddSubmonoid.closure (lemmaOneTerms p S.w Fr (fun j => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ)))) := by
    rw [map_sub, hR, hexp, hR0, ← Finset.sum_erase_eq_sub (Finset.mem_univ ∅)]
    refine sum_mem fun T hT => ?_
    have hTne : T ≠ ∅ := (Finset.mem_erase.1 hT).1
    have hTc : 1 ≤ T.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hTne)
    have hW : (-1) ^ T.card * ∏ I ∈ T, ∏ j ∈ Finset.range Fr.J,
        subst p n' O S.w n' r g (minorI p n' O Fr g (j : ℤ) I.1) ^ (Qj Fr p (j : ℤ) - 1) ∈
        uniformiserOrderFiltration (k := k) S.w Fr (∑ _I ∈ T, ∑ j ∈ Finset.range Fr.J, (Qj Fr p (j : ℤ) - 1) * 1) := by
      have h0 : ∏ I ∈ T, ∏ j ∈ Finset.range Fr.J,
          subst p n' O S.w n' r g (minorI p n' O Fr g (j : ℤ) I.1) ^ (Qj Fr p (j : ℤ) - 1) ∈
          uniformiserOrderFiltration (k := k) S.w Fr (∑ _I ∈ T, ∑ j ∈ Finset.range Fr.J, (Qj Fr p (j : ℤ) - 1) * 1) :=
        order_filtration_prod S.w Fr T _ _ fun I _ => order_filtration_prod S.w Fr _ _ _ fun j _ =>
          order_filtration_pow S.w Fr (complement_minor_order_pos S.w hV hnE (by omega) hg (j : ℤ) I.2) _
      rcases neg_one_pow_eq_or (MvPolynomial (TV n' k) (KK O)) T.card with h | h
      · rw [h, one_mul]; exact h0
      · rw [h, neg_one_mul]; exact order_filtration_neg S.w Fr h0
    have hEq : ∑ _I ∈ T, ∑ j ∈ Finset.range Fr.J, (Qj Fr p (j : ℤ) - 1) * 1 =
        T.card * ∑ j ∈ Finset.range Fr.J, (Qj Fr p (j : ℤ) - 1) := by
      simp [Finset.sum_const]
    have hge : ∀ j < Fr.J, T.card * (Qj Fr p (j : ℤ) - 1) ≤
        ∑ _I ∈ T, ∑ j ∈ Finset.range Fr.J, (Qj Fr p (j : ℤ) - 1) * 1 := by
      intro j hj
      rw [hEq]
      exact Nat.mul_le_mul_left _ (Finset.single_le_sum (f := fun j : ℕ => Qj Fr p (j : ℤ) - 1)
        (fun i _ => Nat.zero_le _) (Finset.mem_range.2 hj))
    have hl := determinant_powers_lift_into_terms (p := p) S.w (fun j => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ)))
      (∑ _I ∈ T, ∑ j ∈ Finset.range Fr.J, (Qj Fr p (j : ℤ) - 1) * 1)
      (fun j => (if j = 0 then 1 else 0) + Fintype.card (↥(II r k)) * (Qj Fr p (j : ℤ) - 1) -
        T.card * (Qj Fr p (j : ℤ) - 1)) ?_ ?_ hW
    · convert hl using 1
      ring
    · have h0 := hge 0 (by omega)
      have hq := two_le_frame_exponent hV (by omega : 1 ≤ r) (by omega : 2 ≤ p) ((0 : ℕ) : ℤ)
      have : 1 ≤ T.card * (Qj Fr p ((0 : ℕ) : ℤ) - 1) := Nat.mul_pos hTc (by omega)
      omega
    · intro j hj
      have h0 := hge j hj
      rw [halpha j]
      omega
  obtain ⟨l, hl, hsum⟩ := AddSubmonoid.exists_list_of_mem_closure hmem
  have h' : ∀ i : Fin l.length, l[i.1] ∈
      lemmaOneTerms p S.w Fr (fun j => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ))) :=
    fun i => hl _ (List.getElem_mem i.2)
  choose e ex nu H hc using h'
  refine ⟨l.length, e, ex, nu, H, fun i => (hc i).1, ?_⟩
  rw [← hsum, ← Fin.sum_univ_getElem]
  exact Finset.sum_congr rfl fun i _ => (hc i).2

end Formalism.MainNotions.G.WittFrameLocaliserOrders

end

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.G.WittFrameLocaliserOrders

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning

section MaximumPrincipleVar

variable {O : Type} [CommRing O] [IsDomain O] {σ : Type}

/- English proof (translation)
Introduce `m` and use `⟨0, by simp⟩`.
-/
theorem inWPow_zero_zero (w : O) (j : ℕ) : InWj w (0 : MvPolynomial σ (KK O)) j := fun m => ⟨0, by simp⟩

/- English proof (translation)
Introduce `m` and use `by obtain ⟨a, ha⟩ := hP m obtain ⟨b, hb⟩ := hQ m exact ⟨a + b, by rw [coeff_add, ha, hb, ← map_add, mul_add]⟩`.
-/
theorem order_mem_add {w : O} {P Q : MvPolynomial σ (KK O)} {j : ℕ} (hP : InWj w P j) (hQ : InWj w Q j) :
    InWj w (P + Q) j := fun m => by
  obtain ⟨a, ha⟩ := hP m
  obtain ⟨b, hb⟩ := hQ m
  exact ⟨a + b, by rw [coeff_add, ha, hb, ← map_add, mul_add]⟩

/- English proof (translation)
Introduce `m` and use `by obtain ⟨a, ha⟩ := hP m exact ⟨-a, by rw [coeff_neg, ha, ← map_neg, mul_neg]⟩`.
-/
theorem inWPow_neg {w : O} {P : MvPolynomial σ (KK O)} {j : ℕ} (hP : InWj w P j) : InWj w (-P) j := fun m => by
  obtain ⟨a, ha⟩ := hP m
  exact ⟨-a, by rw [coeff_neg, ha, ← map_neg, mul_neg]⟩

/- English proof (translation)
Introduce `m` and use `by obtain ⟨a, ha⟩ := hP m exact ⟨w ^ (j - i) * a, by rw [ha, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]⟩`.
-/
theorem inWPow_antitone {w : O} {P : MvPolynomial σ (KK O)} {i j : ℕ} (h : i ≤ j) (hP : InWj w P j) :
    InWj w P i := fun m => by
  obtain ⟨a, ha⟩ := hP m
  exact ⟨w ^ (j - i) * a, by rw [ha, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]⟩

/- English proof (translation)
Unfold `InA InWj`. Simplify using the standard rewrite rules.
-/
theorem integral_iff_order_zero (w : O) (P : MvPolynomial σ (KK O)) : InA P ↔ InWj w P 0 := by
  unfold InA InWj
  simp

def wPowerSubgroup (w : O) (j : ℕ) : AddSubgroup (MvPolynomial σ (KK O)) where
  carrier := {P | InWj w P j}
  zero_mem' := inWPow_zero_zero w j
  add_mem' := order_mem_add
  neg_mem' := inWPow_neg

end MaximumPrincipleVar

section SumSquaresSecondDerivative

variable (p n' : ℕ) [Fact p.Prime] [NeZero n'] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p n') O]

def highOrderTopsSubgroup (w : O) {r k : ℕ} (Fr : Frames n' r) (g : Matrix (Fin k) (Fin k) (WF p n')) (j : ℕ) :
    AddSubgroup (MvPolynomial (TV n' k) (KK O)) where
  carrier := {F | InA F ∧ OnTops Fr F ∧ ∀ g' : Matrix (Fin k) (Fin k) (WF p n'), IsGLW g' →
    ratPlane p n' r g' ≠ ratPlane p n' r g → ordGe p n' O w n' r g' F j}
  zero_mem' := by
    refine ⟨(integral_iff_order_zero w _).2 (inWPow_zero_zero w 0), ?_, ?_⟩
    · intro v hv; simp at hv
    · intro g' _ _
      unfold ordGe InWjRg
      rw [map_zero]; exact inWPow_zero_zero w j
  add_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    refine ⟨(integral_iff_order_zero w _).2 (order_mem_add ((integral_iff_order_zero w _).1 ha1) ((integral_iff_order_zero w _).1 hb1)), ?_, ?_⟩
    · intro v hv
      rcases Finset.mem_union.1 (MvPolynomial.vars_add_subset a b hv) with h | h
      · exact ha2 v h
      · exact hb2 v h
    · intro g' h1 h2
      have := order_mem_add (ha3 g' h1 h2) (hb3 g' h1 h2)
      unfold ordGe InWjRg at *
      rwa [map_add]
  neg_mem' := by
    rintro a ⟨ha1, ha2, ha3⟩
    refine ⟨(integral_iff_order_zero w _).2 (inWPow_neg ((integral_iff_order_zero w _).1 ha1)), ?_, ?_⟩
    · intro v hv
      rw [MvPolynomial.vars_neg] at hv
      exact ha2 v hv
    · intro g' h1 h2
      have := inWPow_neg (ha3 g' h1 h2)
      unfold ordGe InWjRg at *
      rwa [map_neg]

end SumSquaresSecondDerivative

def SymbolOrderGeLevel (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p n' r k : ℕ) [Fact p.Prime] [NeZero n'] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF p n') O] (S : UniformizedDVR p O), OHyp p n' O S → ∀ hH : CommonHypotheses p n' r k,
  ∀ (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ → ∀ Q : ℕ, TwistBound p Fr Q →
  ∀ g : Matrix (Fin k) (Fin k) (WF p n'), IsGLW g →
  ∀ (c' mu la : ℕ) (τ : Term n' k O), τ.Valid p n' S.w n' r Q g → τ.InTops Fr →
    InWj S.w (τ.sym p n' S.w Fr hH.2.2.1 g c' mu la) τ.level

def RawSymbolOrderRemaining (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p n' r k : ℕ) [Fact p.Prime] [NeZero n'] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF p n') O] (S : UniformizedDVR p O), OHyp p n' O S → ∀ hH : CommonHypotheses p n' r k,
  ∀ (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ → ∀ Q : ℕ, TwistBound p Fr Q →
  ∀ g : Matrix (Fin k) (Fin k) (WF p n'), IsGLW g →
  ∀ (c' mu la : ℕ) (τ : Term n' k O), τ.Valid p n' S.w n' r Q g → τ.InTops Fr →
    InA (τ.raw p n' S.w Fr hH.2.2.1 g c' mu la) ∧ OnTops Fr (τ.raw p n' S.w Fr hH.2.2.1 g c' mu la) ∧
    ∀ g' : Matrix (Fin k) (Fin k) (WF p n'), IsGLW g' → ratPlane p n' r g' ≠ ratPlane p n' r g →
      ordGe p n' O S.w n' r g' (τ.raw p n' S.w Fr hH.2.2.1 g c' mu la) (τ.level + c')

def OrderClaimRemaining (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p n' r k : ℕ) [Fact p.Prime] [NeZero n'] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF p n') O] (S : UniformizedDVR p O), OHyp p n' O S → ∀ hH : CommonHypotheses p n' r k,
  ∀ (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ → ∀ Q : ℕ, TwistBound p Fr Q →
  ∀ g : Matrix (Fin k) (Fin k) (WF p n'), IsGLW g →
  ∀ (c' o mu la : ℕ) (τ : Term n' k O), τ.Valid p n' S.w n' r Q g → τ.InTops Fr → τ.level < o + c' →
    (2 * (Q : ℤ) + 1) * ((o : ℤ) + c' - 1 - τ.level) ≤ mu → ((o : ℤ) + c' - 1 - τ.level) ≤ la →
    ∃ (m : ℕ) (τ' : Fin m → Term n' k O) (mu' la' : Fin m → ℕ) (ρ : MvPolynomial (TV n' k) (KK O)),
      InWj S.w ρ (o + c') ∧
      subst p n' O S.w n' r g (τ.raw p n' S.w Fr hH.2.2.1 g c' mu la) - τ.sym p n' S.w Fr hH.2.2.1 g c' mu la =
        ∑ i, (τ' i).sym p n' S.w Fr hH.2.2.1 g c' (mu' i) (la' i) + ρ ∧
      ∀ i, (τ' i).Valid p n' S.w n' r Q g ∧ (τ' i).InTops Fr ∧ τ.level < (τ' i).level ∧ (τ' i).level < o + c' ∧
        (mu' i : ℤ) = (mu : ℤ) - (2 * (Q : ℤ) + 1) * (((τ' i).level : ℤ) - τ.level) ∧
        (la' i : ℤ) = (la : ℤ) - (((τ' i).level : ℤ) - τ.level)

/- English proof (translation)
Set `T` to `{x : ℕ × Term n' k O × ℕ × ℕ // x.2.1.Valid p n' S.w n' r Q g ∧ x.2.1.InTops Fr}`. Set `sb` to `(subst p n' O S.w n' r g).toRingHom.toAddMonoidHom`. Establish `key` using `Formalism.CountingSumsFrames.Top.cleanInduction (MvPolynomial (TV n' k) (KK O)) ⊤ (fun j => wPowerSubgroup S.w j) (fun j => (highOrderTopsSubgroup p n' S.w Fr g j).map sb) (fun i j hij P hP => inWPow_antitone hij hP) (fun i j hij P hP => by`. Take `⟨F, ⟨hF1, hF2, hF3⟩, rfl⟩` from `hP`. Conclude with `⟨F, ⟨hF1, hF2, fun g' a b => inWPow_antitone hij (hF3 g' a b)⟩, rfl⟩)`.

Use `T (fun x => x.1.2.1.level) (fun x => ((x.1.2.2.1 : ℤ), (x.1.2.2.2 : ℤ)))`. Use the proof step `(fun x => x.1.2.1.sym p n' S.w Fr hH.2.2.1 g c' x.1.2.2.1 x.1.2.2.2)`. Use the proof step `(fun x => subst p n' O S.w n' r g (x.1.2.1.raw p n' S.w Fr hH.2.2.1 g c' x.1.2.2.1 x.1.2.2.2))`. Use `o c' Q`. Use the proof step `(fun x => ⟨AddSubgroup.mem_top _, AddSubgroup.mem_top _⟩)`.

Use the proof step `(fun x => h1 p n' r k O S hO hH Fr L₁ N₁ hV Q hQ g hg c' _ _ x.1.2.1 x.2.1 x.2.2)`. Use the proof step `(fun x => ⟨_, h2 p n' r k O S hO hH Fr L₁ N₁ hV Q hQ g hg c' _ _ x.1.2.1 x.2.1 x.2.2, rfl⟩)`. Use the proof step `(by`. Introduce `x hx hmu hla`. Take `⟨m, τ', mu', la', ρ, hρ, heq, hch⟩` from `h3 p n' r k O S hO hH Fr L₁ N₁ hV Q hQ g hg c' o _ _ x.1.2.1 x.2.1 x.2.2 hx hmu hla`.

Set `e : Fin m → T` to `fun i => ⟨(i.val, τ' i, mu' i, la' i), (hch i).1, (hch i).2.1⟩`. Establish `he : Function.Injective e`. Introduce `i j hij`. Use `congrArg (fun y : T => y.1.1) hij` as an intermediate fact. Conclude with `Fin.ext this`.

Use `⟨Finset.univ.image e, ρ, hρ, AddSubgroup.mem_top _, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_image (fun i _ j _ h => he h)]`. Conclude with `heq`. Introduce `y hy`. Take `⟨i, _, rfl⟩` from `Finset.mem_image.1 hy`.

Conclude with `⟨(hch i).2.2.1, (hch i).2.2.2.1, Prod.ext (hch i).2.2.2.2.1 (hch i).2.2.2.2.2⟩)`. Set `e : Fin n → T` to `fun i => ⟨(i.val, τ i, (2 * Q + 3) * c', c'), (hτ i).1, (hτ i).2.1⟩`. Establish `he : Function.Injective e`. Introduce `i j hij`. Use `congrArg (fun y : T => y.1.1) hij` as an intermediate fact.

Conclude with `Fin.ext this`. Take `⟨f, -, hf1, F, ⟨hF1, hF2, hF3⟩, rfl⟩` from `key (Finset.univ.image e) (by`. Introduce `y hy`. Take `⟨i, _, rfl⟩` from `Finset.mem_image.1 hy`. Conclude with `⟨(hτ i).2.2, rfl⟩)`.

Rewrite `hf1` using `[Finset.sum_image (fun i _ j _ h => he h)]`. Conclude with `⟨F, hF1, hF2, hf1, hF3⟩`.
-/
theorem clean_symbol_order (D : Formalism.BasicNotions.D7) (h1 : SymbolOrderGeLevel D) (h2 : RawSymbolOrderRemaining D) (h3 : OrderClaimRemaining D)
    (p n' r k : ℕ) [Fact p.Prime] [NeZero n'] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF p n') O] (S : UniformizedDVR p O) (hO : OHyp p n' O S) (hH : CommonHypotheses p n' r k)
    (Fr : Frames n' r) (L₁ N₁ : ℕ) (hV : Fr.Valid L₁ N₁) (Q : ℕ) (hQ : TwistBound p Fr Q)
    (g : Matrix (Fin k) (Fin k) (WF p n')) (hg : IsGLW g)
    (c' o : ℕ) (n : ℕ) (τ : Fin n → Term n' k O)
    (hτ : ∀ i, (τ i).Valid p n' S.w n' r Q g ∧ (τ i).InTops Fr ∧ o ≤ (τ i).level) :
    ∃ F : MvPolynomial (TV n' k) (KK O), InA F ∧ OnTops Fr F ∧
      InWj S.w (subst p n' O S.w n' r g F - ∑ i, (τ i).sym p n' S.w Fr hH.2.2.1 g c' ((2 * Q + 3) * c') c')
        (o + c') ∧
      ∀ g' : Matrix (Fin k) (Fin k) (WF p n'), IsGLW g' → ratPlane p n' r g' ≠ ratPlane p n' r g →
        ordGe p n' O S.w n' r g' F (o + c') := by
  let T := {x : ℕ × Term n' k O × ℕ × ℕ // x.2.1.Valid p n' S.w n' r Q g ∧ x.2.1.InTops Fr}
  let sb := (subst p n' O S.w n' r g).toRingHom.toAddMonoidHom
  have key := Formalism.CountingSumsFrames.Top.cleanInduction (MvPolynomial (TV n' k) (KK O)) ⊤ (fun j => wPowerSubgroup S.w j)
    (fun j => (highOrderTopsSubgroup p n' S.w Fr g j).map sb)
    (fun i j hij P hP => inWPow_antitone hij hP)
    (fun i j hij P hP => by
      obtain ⟨F, ⟨hF1, hF2, hF3⟩, rfl⟩ := hP
      exact ⟨F, ⟨hF1, hF2, fun g' a b => inWPow_antitone hij (hF3 g' a b)⟩, rfl⟩)
    T (fun x => x.1.2.1.level) (fun x => ((x.1.2.2.1 : ℤ), (x.1.2.2.2 : ℤ)))
    (fun x => x.1.2.1.sym p n' S.w Fr hH.2.2.1 g c' x.1.2.2.1 x.1.2.2.2)
    (fun x => subst p n' O S.w n' r g (x.1.2.1.raw p n' S.w Fr hH.2.2.1 g c' x.1.2.2.1 x.1.2.2.2))
    o c' Q
    (fun x => ⟨AddSubgroup.mem_top _, AddSubgroup.mem_top _⟩)
    (fun x => h1 p n' r k O S hO hH Fr L₁ N₁ hV Q hQ g hg c' _ _ x.1.2.1 x.2.1 x.2.2)
    (fun x => ⟨_, h2 p n' r k O S hO hH Fr L₁ N₁ hV Q hQ g hg c' _ _ x.1.2.1 x.2.1 x.2.2, rfl⟩)
    (by
      intro x hx hmu hla
      obtain ⟨m, τ', mu', la', ρ, hρ, heq, hch⟩ :=
        h3 p n' r k O S hO hH Fr L₁ N₁ hV Q hQ g hg c' o _ _ x.1.2.1 x.2.1 x.2.2 hx hmu hla
      let e : Fin m → T := fun i => ⟨(i.val, τ' i, mu' i, la' i), (hch i).1, (hch i).2.1⟩
      have he : Function.Injective e := by
        intro i j hij
        have := congrArg (fun y : T => y.1.1) hij
        exact Fin.ext this
      refine ⟨Finset.univ.image e, ρ, hρ, AddSubgroup.mem_top _, ?_, ?_⟩
      · rw [Finset.sum_image (fun i _ j _ h => he h)]
        exact heq
      · intro y hy
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hy
        exact ⟨(hch i).2.2.1, (hch i).2.2.2.1, Prod.ext (hch i).2.2.2.2.1 (hch i).2.2.2.2.2⟩)
  let e : Fin n → T := fun i => ⟨(i.val, τ i, (2 * Q + 3) * c', c'), (hτ i).1, (hτ i).2.1⟩
  have he : Function.Injective e := by
    intro i j hij
    have := congrArg (fun y : T => y.1.1) hij
    exact Fin.ext this
  obtain ⟨f, -, hf1, F, ⟨hF1, hF2, hF3⟩, rfl⟩ := key (Finset.univ.image e) (by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨(hτ i).2.2, rfl⟩)
  rw [Finset.sum_image (fun i _ j _ h => he h)] at hf1
  exact ⟨F, hF1, hF2, hf1, hF3⟩

section B4c

variable {n' k : ℕ}

def coordinatePositionWeight (n' k : ℕ) : TV n' k → (Fin n' → ℕ) := fun v => Pi.single v.1 1

/- English proof (translation)
Rewrite using `[Finsupp.weight_eq_sum, Finset.sum_apply, Fintype.sum_prod_type]`. Unfold `multideg coordinatePositionWeight`. Simplify using `only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[Ne.symm hb]`. Simplify using the standard rewrite rules.
-/
theorem weight_eq_multidegree (m : TV n' k →₀ ℕ) (i : Fin n') : Finsupp.weight (coordinatePositionWeight n' k) m i = multideg m i := by
  rw [Finsupp.weight_eq_sum, Finset.sum_apply, Fintype.sum_prod_type]
  unfold multideg coordinatePositionWeight
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

/- English proof (translation)
Unfold `HasMultideg Pol`. Rewrite using `[mem_restrictSupport_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h m hm`. Establish `h' : ∀ i, multideg m i = d i` using `h (Finset.mem_coe.2 (mem_support_iff.2 hm))`.

Use function extensionality and compare the values at `i`. Rewrite using `[weight_eq_multidegree]`. Conclude with `h' i`. Introduce `h m hm show ∀ i, multideg m i = d i`. Introduce `i`.

Use `h (mem_support_iff.1 (Finset.mem_coe.1 hm))` as an intermediate fact. Rewrite using `[← weight_eq_multidegree, this]`.
-/
theorem hasMultideg_iff_weighted_homog {R : Type*} [CommRing R] (F : MvPolynomial (TV n' k) R) (d : Fin n' → ℕ) :
    HasMultideg F d ↔ IsWeightedHomogeneous (coordinatePositionWeight n' k) F d := by
  unfold HasMultideg Pol
  rw [mem_restrictSupport_iff]
  constructor
  · intro h m hm
    have h' : ∀ i, multideg m i = d i := h (Finset.mem_coe.2 (mem_support_iff.2 hm))
    funext i; rw [weight_eq_multidegree]; exact h' i
  · intro h m hm
    show ∀ i, multideg m i = d i
    intro i
    have := h (mem_support_iff.1 (Finset.mem_coe.1 hm))
    rw [← weight_eq_multidegree, this]

variable {O : Type} [CommRing O] [IsDomain O]

/- English proof (translation)
Introduce `m` and use `by rw [coeff_weightedHomogeneousComponent] split_ifs · exact hP m · exact ⟨0, by simp⟩`.
-/
theorem inWPow_weighted_component {w : O} (d : Fin n' → ℕ) {P : MvPolynomial (TV n' k) (KK O)} {j : ℕ} (hP : InWj w P j) :
    InWj w (weightedHomogeneousComponent (coordinatePositionWeight n' k) d P) j := fun m => by
  rw [coeff_weightedHomogeneousComponent]
  split_ifs
  · exact hP m
  · exact ⟨0, by simp⟩

/- English proof (translation)
Introduce `v hv`. Take `⟨m, hm, hvm⟩` from `(mem_vars v).1 hv`. Use `hP v ((mem_vars v).2 ⟨m, ?_, hvm⟩)` and prove the remaining obligations. Rewrite `hm`, the goal using `[mem_support_iff]`. Rewrite `hm` using `[coeff_weightedHomogeneousComponent]`.

Use `split_ifs at hm`. Conclude with `hm`. Conclude with `absurd rfl hm`.
-/
theorem onTops_weighted_component {r : ℕ} (Fr : Frames n' r) (d : Fin n' → ℕ) {P : MvPolynomial (TV n' k) (KK O)}
    (hP : OnTops Fr P) : OnTops Fr (weightedHomogeneousComponent (coordinatePositionWeight n' k) d P) := by
  intro v hv
  obtain ⟨m, hm, hvm⟩ := (mem_vars v).1 hv
  refine hP v ((mem_vars v).2 ⟨m, ?_, hvm⟩)
  rw [mem_support_iff] at hm ⊢
  rw [coeff_weightedHomogeneousComponent] at hm
  split_ifs at hm
  · exact hm
  · exact absurd rfl hm

variable {p : ℕ} [Fact p.Prime] [NeZero n'] [Algebra (WF p n') O]

/- English proof (translation)
Establish `hX : IsWeightedHomogeneous (coordinatePositionWeight n' k) (X (s, b) : MvPolynomial (TV n' k) (KK O)) (coordinatePositionWeight n' k (s, c))` using `isWeightedHomogeneous_X (R := KK O) (coordinatePositionWeight n' k) (s, b)`. Unfold `newVar`. Use `split_ifs`. Conclude with `hX.C_mul _`. Conclude with `hX`.
-/
theorem new_variable_weighted_homogeneous (w : O) (r : ℕ) (s : Fin n') (b c : Fin k) :
    IsWeightedHomogeneous (coordinatePositionWeight n' k) (newVar w r (s, b)) (coordinatePositionWeight n' k (s, c)) := by
  have hX : IsWeightedHomogeneous (coordinatePositionWeight n' k) (X (s, b) : MvPolynomial (TV n' k) (KK O)) (coordinatePositionWeight n' k (s, c)) :=
    isWeightedHomogeneous_X (R := KK O) (coordinatePositionWeight n' k) (s, b)
  unfold newVar
  split_ifs
  · exact hX.C_mul _
  · exact hX

/- English proof (translation)
Take `⟨s, c⟩` from `v`. Distinguish the cases in `hs : Even s.val`. Rewrite using `[subst_X_even w r g s hs c]`. Use `IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`.

Conclude with `(new_variable_weighted_homogeneous w r s b c).C_mul _`. Rewrite using `[subst_X_odd w r g s hs c]`. Use `IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Conclude with `(new_variable_weighted_homogeneous w r s b c).C_mul _`.
-/
theorem substitute_variable_weighted_homogeneous (w : O) (r : ℕ) (g : Matrix (Fin k) (Fin k) (WF p n')) (v : TV n' k) :
    IsWeightedHomogeneous (coordinatePositionWeight n' k) (subst p n' O w n' r g (X v)) (coordinatePositionWeight n' k v) := by
  obtain ⟨s, c⟩ := v
  by_cases hs : Even s.val
  · rw [subst_X_even w r g s hs c]
    refine IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
    rw [mul_comm]
    exact (new_variable_weighted_homogeneous w r s b c).C_mul _
  · rw [subst_X_odd w r g s hs c]
    refine IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
    rw [mul_comm]
    exact (new_variable_weighted_homogeneous w r s b c).C_mul _

/- English proof (translation)
Unfold `subst`. Conclude with `(liftSubst p n' O w r (LLT n') g).commutes a`.
-/
theorem subst_C_alt (w : O) (r : ℕ) (g : Matrix (Fin k) (Fin k) (WF p n')) (a : KK O) :
    subst p n' O w n' r g (C a) = C a := by
  unfold subst; exact (liftSubst p n' O w r (LLT n') g).commutes a

/- English proof (translation)
Rewrite using `[monomial_eq, map_mul, Finsupp.prod, map_prod, subst_C_alt]`. Apply `IsWeightedHomogeneous.C_mul` to reduce the goal to its premises. Rewrite using `[Finsupp.weight_apply, Finsupp.sum]`. Apply `IsWeightedHomogeneous.prod` to reduce the goal to its premises. Introduce `v _`.

Rewrite using `[map_pow]`. Conclude with `(substitute_variable_weighted_homogeneous w r g v).pow _`.
-/
theorem substitute_monomial_weighted_homogeneous (w : O) (r : ℕ) (g : Matrix (Fin k) (Fin k) (WF p n')) (m : TV n' k →₀ ℕ)
    (a : KK O) :
    IsWeightedHomogeneous (coordinatePositionWeight n' k) (subst p n' O w n' r g (monomial m a)) (Finsupp.weight (coordinatePositionWeight n' k) m) := by
  rw [monomial_eq, map_mul, Finsupp.prod, map_prod, subst_C_alt]
  apply IsWeightedHomogeneous.C_mul
  rw [Finsupp.weight_apply, Finsupp.sum]
  apply IsWeightedHomogeneous.prod
  intro v _
  rw [map_pow]
  exact (substitute_variable_weighted_homogeneous w r g v).pow _

/- English proof (translation)
Use `MvPolynomial.induction_on' F ?_ ?_` and prove the remaining obligations. Introduce `m a`. Establish `h1` using `substitute_monomial_weighted_homogeneous w r g m a`. Establish `h2 : IsWeightedHomogeneous (coordinatePositionWeight n' k) (monomial m a) (Finsupp.weight (coordinatePositionWeight n' k) m)` using `isWeightedHomogeneous_monomial _ m a rfl`. Distinguish the cases in `h : d = Finsupp.weight (coordinatePositionWeight n' k) m`.

Rewrite using `[h, h1.weightedHomogeneousComponent_same, h2.weightedHomogeneousComponent_same]`. Rewrite using `[h1.weightedHomogeneousComponent_ne d h, h2.weightedHomogeneousComponent_ne d h, map_zero]`. Introduce `P Q hP hQ`. Simplify using `only [map_add, hP, hQ]`.
-/
theorem weighted_component_substitute_comm (w : O) (r : ℕ) (g : Matrix (Fin k) (Fin k) (WF p n')) (d : Fin n' → ℕ)
    (F : MvPolynomial (TV n' k) (KK O)) :
    weightedHomogeneousComponent (coordinatePositionWeight n' k) d (subst p n' O w n' r g F) =
      subst p n' O w n' r g (weightedHomogeneousComponent (coordinatePositionWeight n' k) d F) := by
  refine MvPolynomial.induction_on' F ?_ ?_
  · intro m a
    have h1 := substitute_monomial_weighted_homogeneous w r g m a
    have h2 : IsWeightedHomogeneous (coordinatePositionWeight n' k) (monomial m a) (Finsupp.weight (coordinatePositionWeight n' k) m) :=
      isWeightedHomogeneous_monomial _ m a rfl
    by_cases h : d = Finsupp.weight (coordinatePositionWeight n' k) m
    · rw [h, h1.weightedHomogeneousComponent_same, h2.weightedHomogeneousComponent_same]
    · rw [h1.weightedHomogeneousComponent_ne d h, h2.weightedHomogeneousComponent_ne d h, map_zero]
  · intro P Q hP hQ
    simp only [map_add, hP, hQ]

end B4c

/- English proof (translation)
Introduce `p n' r k _ _ O _ _ _ _ S hO hH Fr L₁ N₁ hV Q hQ g hg c' o d n τ hτ`. Take `⟨F0, hA, hT, hW, hG⟩` from `clean_symbol_order D h1 h2 h3 p n' r k O S hO hH Fr L₁ N₁ hV Q hQ g hg c' o n τ (fun i => ⟨(hτ i).1, (hτ i).2.1, (hτ i).2.2.1⟩)`. Use `⟨weightedHomogeneousComponent (coordinatePositionWeight n' k) d F0, (integral_iff_order_zero S.w _).2 (inWPow_weighted_component d ((integral_iff_order_zero S.w _).1 hA)), onTops_weighted_component Fr d hT, (hasMultideg_iff_weighted_homog _ _).2 (weightedHomogeneousComponent_isWe …` and prove the remaining obligations. Establish `hs : HasMultideg (∑ i, (τ i).sym p n' S.w Fr hH.2.2.1 g c' ((2 * Q + 3) * c') c') d` using `Submodule.sum_mem _ (fun i _ => (hτ i).2.2.2.1)`. Establish `hs'` using `((hasMultideg_iff_weighted_homog _ _).1 hs).weightedHomogeneousComponent_same`.

Use `inWPow_weighted_component d hW` as an intermediate fact. Rewrite `this` using `[map_sub, weighted_component_substitute_comm, hs']`. Conclude with `this`. Introduce `g' hg' hne`. Use `inWPow_weighted_component d (hG g' hg' hne)` as an intermediate fact.

Use `show InWj S.w (subst p n' O S.w n' r g' _) _`. Rewrite using `[← weighted_component_substitute_comm]`. Conclude with `this`.
-/
theorem divisibility_lemma_of_three_orders (D : Formalism.BasicNotions.D7) (h1 : SymbolOrderGeLevel D) (h2 : RawSymbolOrderRemaining D) (h3 : OrderClaimRemaining D) :
    Conclusion4 D := by
  intro p n' r k _ _ O _ _ _ _ S hO hH Fr L₁ N₁ hV Q hQ g hg c' o d n τ hτ
  obtain ⟨F0, hA, hT, hW, hG⟩ := clean_symbol_order D h1 h2 h3 p n' r k O S hO hH Fr L₁ N₁ hV Q hQ g hg c' o n τ
    (fun i => ⟨(hτ i).1, (hτ i).2.1, (hτ i).2.2.1⟩)
  refine ⟨weightedHomogeneousComponent (coordinatePositionWeight n' k) d F0,
    (integral_iff_order_zero S.w _).2 (inWPow_weighted_component d ((integral_iff_order_zero S.w _).1 hA)), onTops_weighted_component Fr d hT,
    (hasMultideg_iff_weighted_homog _ _).2 (weightedHomogeneousComponent_isWeightedHomogeneous _ _), ?_, ?_⟩
  · have hs : HasMultideg (∑ i, (τ i).sym p n' S.w Fr hH.2.2.1 g c' ((2 * Q + 3) * c') c') d :=
      Submodule.sum_mem _ (fun i _ => (hτ i).2.2.2.1)
    have hs' := ((hasMultideg_iff_weighted_homog _ _).1 hs).weightedHomogeneousComponent_same
    have := inWPow_weighted_component d hW
    rw [map_sub, weighted_component_substitute_comm, hs'] at this
    exact this
  · intro g' hg' hne
    have := inWPow_weighted_component d (hG g' hg' hne)
    show InWj S.w (subst p n' O S.w n' r g' _) _
    rw [← weighted_component_substitute_comm]
    exact this

section B4d

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]

/- English proof (translation)
Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[sigMat_eq_map, sigMat_eq_map, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hg, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem sigmaMatrix_inv_general {f : ℕ} [Algebra (WF p f) O] {k : ℕ} {g : Matrix (Fin k) (Fin k) (WF p f)}
    (hg : IsGLW g) (s : ℤ) : (sigMat p f O g s)⁻¹ = sigMat p f O g⁻¹ s := by
  apply Matrix.inv_eq_left_inv
  rw [sigMat_eq_map, sigMat_eq_map, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hg,
    Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
Unfold `sigMat`. Simplify using `only [Matrix.of_apply]`. Conclude with `integral_constant_mem_order_zero _`.
-/
theorem sigmaMatrix_entry_integral {f : ℕ} [Algebra (WF p f) O] {k : ℕ} (w : O) {σ : Type} (g : Matrix (Fin k) (Fin k) (WF p f))
    (s : ℤ) (a b : Fin k) : InWj w (C (sigMat p f O g s a b) : MvPolynomial σ (KK O)) 0 := by
  unfold sigMat
  simp only [Matrix.of_apply]
  exact integral_constant_mem_order_zero _

variable {n' : ℕ} [NeZero n'] [Algebra (WF p n') O] {k : ℕ}

/- English proof (translation)
Unfold `newVar`. Use `split_ifs`. Conclude with `inWPow_zero_mul (integral_constant_mem_order_zero w) (inWj_X v)`. Conclude with `inWj_X v`.
-/
theorem new_variable_integral (w : O) (r : ℕ) (v : TV n' k) : InWj w (newVar w r v) 0 := by
  unfold newVar
  split_ifs
  · exact inWPow_zero_mul (integral_constant_mem_order_zero w) (inWj_X v)
  · exact inWj_X v

/- English proof (translation)
Take `⟨s, c⟩` from `v`. Distinguish the cases in `hs : Even s.val`. Rewrite using `[subst_X_even w r g s hs c, sigmaMatrix_inv_general hg]`. Conclude with `inWj_sum _ _ fun b _ => inWPow_zero_mul (new_variable_integral w r _) (sigmaMatrix_entry_integral w _ _ _ _)`. Rewrite using `[subst_X_odd w r g s hs c]`.

Conclude with `inWj_sum _ _ fun b _ => inWPow_zero_mul (new_variable_integral w r _) (sigmaMatrix_entry_integral w _ _ _ _)`.
-/
theorem subst_X_integral (w : O) (r : ℕ) {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (v : TV n' k) :
    InWj w (subst p n' O w n' r g (X v)) 0 := by
  obtain ⟨s, c⟩ := v
  by_cases hs : Even s.val
  · rw [subst_X_even w r g s hs c, sigmaMatrix_inv_general hg]
    exact inWj_sum _ _ fun b _ => inWPow_zero_mul (new_variable_integral w r _) (sigmaMatrix_entry_integral w _ _ _ _)
  · rw [subst_X_odd w r g s hs c]
    exact inWj_sum _ _ fun b _ => inWPow_zero_mul (new_variable_integral w r _) (sigmaMatrix_entry_integral w _ _ _ _)

/- English proof (translation)
Establish `h : subst p n' O w n' r g F = ∑ d ∈ F.support, C (F.coeff d) * ∏ i ∈ d.support, (subst p n' O w n' r g (X i)) ^ d i` using `by conv_lhs => rw [F.as_sum]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[monomial_eq, map_mul, subst_C_alt, Finsupp.prod, map_prod]`. Simplify using `only [map_pow]`.

Rewrite using `[h]`. Use `inWj_sum _ _ fun d _ => inWPow_zero_mul ?_ (inWj_prod0 _ _ fun i _ => inWPow_zero_pow (subst_X_integral w r hg i) _)` and prove the remaining obligations. Take `⟨c, hc⟩` from `((inA_iff_inWj0 (w := w) F).2 hF) d`. Rewrite using `[hc]`. Conclude with `integral_constant_mem_order_zero c`.
-/
theorem subst_integral (w : O) (r : ℕ) {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g)
    {F : MvPolynomial (TV n' k) (KK O)} (hF : InWj w F 0) : InWj w (subst p n' O w n' r g F) 0 := by
  have h : subst p n' O w n' r g F =
      ∑ d ∈ F.support, C (F.coeff d) * ∏ i ∈ d.support, (subst p n' O w n' r g (X i)) ^ d i := by
    conv_lhs => rw [F.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [monomial_eq, map_mul, subst_C_alt, Finsupp.prod, map_prod]
    simp only [map_pow]
  rw [h]
  refine inWj_sum _ _ fun d _ => inWPow_zero_mul ?_ (inWj_prod0 _ _ fun i _ => inWPow_zero_pow (subst_X_integral w r hg i) _)
  obtain ⟨c, hc⟩ := ((inA_iff_inWj0 (w := w) F).2 hF) d
  rw [hc]; exact integral_constant_mem_order_zero c

/- English proof (translation)
Unfold `xg`. Conclude with `inWj_sum _ _ fun c _ => inWPow_zero_mul (inWj_X _) (sigmaMatrix_entry_integral w _ _ _ _)`.
-/
theorem twisted_row_integral (w : O) (g : Matrix (Fin k) (Fin k) (WF p n')) (a : ℤ) (b : Fin k) :
    InWj w (xg p n' O n' g a b) 0 := by
  unfold xg
  exact inWj_sum _ _ fun c _ => inWPow_zero_mul (inWj_X _) (sigmaMatrix_entry_integral w _ _ _ _)

/- English proof (translation)
Unfold `yg`. Rewrite using `[sigmaMatrix_inv_general hg]`. Conclude with `inWj_sum _ _ fun c _ => inWPow_zero_mul (inWj_X _) (sigmaMatrix_entry_integral w _ _ _ _)`.
-/
theorem twisted_inverse_row_integral (w : O) {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (a : ℤ) (b : Fin k) :
    InWj w (yg p n' O n' g a b) 0 := by
  unfold yg
  rw [sigmaMatrix_inv_general hg]
  exact inWj_sum _ _ fun c _ => inWPow_zero_mul (inWj_X _) (sigmaMatrix_entry_integral w _ _ _ _)

/- English proof (translation)
Unfold `newCoord`. Use `split_ifs`. Conclude with `twisted_row_integral w g _ _`. Conclude with `twisted_inverse_row_integral w hg _ _`.
-/
theorem new_coordinate_integral (w : O) {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (v : TV n' k) :
    InWj w (newCoord p n' O n' g v) 0 := by
  unfold newCoord
  split_ifs
  · exact twisted_row_integral w g _ _
  · exact twisted_inverse_row_integral w hg _ _

/- English proof (translation)
Unfold `hTrue`. Rewrite using `[aeval_def, eval₂_eq]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_map]`. Both sides reduce to the same expression.
-/
theorem true_coordinates_eq_sum (g : Matrix (Fin k) (Fin k) (WF p n')) (h : MvPolynomial (TV n' k) O) :
    hTrue p n' O n' g h = ∑ d ∈ (MvPolynomial.map (algebraMap O (KK O)) h).support,
      C (algebraMap O (KK O) (h.coeff d)) * ∏ i ∈ d.support, (newCoord p n' O n' g i) ^ d i := by
  unfold hTrue
  rw [aeval_def, eval₂_eq]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [coeff_map]; rfl

/- English proof (translation)
Rewrite using `[true_coordinates_eq_sum]`. Conclude with `inWj_sum _ _ fun d _ => inWPow_zero_mul (integral_constant_mem_order_zero _) (inWj_prod0 _ _ fun i _ => inWPow_zero_pow (new_coordinate_integral w hg i) _)`.
-/
theorem true_coordinates_integral (w : O) {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (h : MvPolynomial (TV n' k) O) :
    InWj w (hTrue p n' O n' g h) 0 := by
  rw [true_coordinates_eq_sum]
  exact inWj_sum _ _ fun d _ => inWPow_zero_mul (integral_constant_mem_order_zero _) (inWj_prod0 _ _ fun i _ => inWPow_zero_pow (new_coordinate_integral w hg i) _)

variable {r : ℕ} (Fr : Frames n' r)

/- English proof (translation)
Unfold `minorI`. Use `split_ifs`. Use `inWj_det _ fun l i => ?_` and prove the remaining obligations. Simplify using `only [Matrix.of_apply, twRow]`. Conclude with `inWPow_zero_pow (twisted_row_integral w g _ _) _`.

Conclude with `inWj_zero 0`.
-/
theorem column_minor_integral (w : O) (g : Matrix (Fin k) (Fin k) (WF p n')) (j : ℤ) (I : Finset (Fin k)) :
    InWj w (minorI p n' O Fr g j I) 0 := by
  unfold minorI
  split_ifs
  · refine inWj_det _ fun l i => ?_
    simp only [Matrix.of_apply, twRow]
    exact inWPow_zero_pow (twisted_row_integral w g _ _) _
  · exact inWj_zero 0

/- English proof (translation)
The claim follows from `column_minor_integral Fr w g j _`.
-/
theorem frame_determinant_integral (w : O) (g : Matrix (Fin k) (Fin k) (WF p n')) (j : ℤ) : InWj w (Del p n' O Fr g j) 0 :=
  column_minor_integral Fr w g j _

/- English proof (translation)
Unfold `R0`. Conclude with `inWj_prod0 _ _ fun j _ => inWPow_zero_pow (frame_determinant_integral Fr w g j) _`.
-/
theorem base_localiser_integral (w : O) (g : Matrix (Fin k) (Fin k) (WF p n')) : InWj w (R0 p n' O Fr g) 0 := by
  unfold R0
  exact inWj_prod0 _ _ fun j _ => inWPow_zero_pow (frame_determinant_integral Fr w g j) _

/- English proof (translation)
Unfold `Rloc`. Conclude with `inWPow_zero_mul (frame_determinant_integral Fr w g 0) (inWj_prod0 _ _ fun I _ => inWj_sub (inWj_prod0 _ _ fun j _ => inWPow_zero_pow (frame_determinant_integral Fr w g j) _) (inWj_prod0 _ _ fun j _ => inWPow_zero_pow (column_minor_integral Fr w g j I) _))`.
-/
theorem local_relation_integral (w : O) (g : Matrix (Fin k) (Fin k) (WF p n')) : InWj w (Rloc p n' O Fr g) 0 := by
  unfold Rloc
  exact inWPow_zero_mul (frame_determinant_integral Fr w g 0) (inWj_prod0 _ _ fun I _ =>
    inWj_sub (inWj_prod0 _ _ fun j _ => inWPow_zero_pow (frame_determinant_integral Fr w g j) _)
      (inWj_prod0 _ _ fun j _ => inWPow_zero_pow (column_minor_integral Fr w g j I) _))

/- English proof (translation)
Unfold `DtopProd Dtop`. Use `inWj_prod0 _ _ fun s _ => inWPow_zero_pow (inWj_det _ fun l b => ?_) _` and prove the remaining obligations. Simplify using `only [Matrix.of_apply]`. Conclude with `inWPow_zero_pow (twisted_row_integral w g _ _) _`.
-/
theorem top_product_determinant_integral (w : O) (hrk : r ≤ k) (g : Matrix (Fin k) (Fin k) (WF p n')) (mu : ℕ) :
    InWj w (DtopProd p n' O Fr hrk g mu) 0 := by
  unfold DtopProd Dtop
  refine inWj_prod0 _ _ fun s _ => inWPow_zero_pow (inWj_det _ fun l b => ?_) _
  simp only [Matrix.of_apply]
  exact inWPow_zero_pow (twisted_row_integral w g _ _) _

end B4d

/- English proof (translation)
Introduce `p n' r k _ _ O _ _ _ _ S hO hH Fr L₁ N₁ hV Q hQ g hg c' mu la τ hτ _`. Unfold `Term.sym`. Establish `e1 : InWj S.w (C (algebraMap O (KK O) (S.w ^ τ.i)) * ∏ l, τ.ka0 l) (τ.i + ∑ l, τ.o l)` using `inWj_mul (inWj_Cpow _) (inWj_prod Finset.univ _ _ (fun l _ => (hτ.1 l).2.2.2.1))`. Establish `e2` using `inWj_mul (inWj_mul (inWj_mul (inWj_mul e1 (inWPow_zero_pow (subst_integral S.w r hg (base_localiser_integral Fr S.w g)) c')) (inWj_prod0 (Finset.range Fr.J) _ fun j _ => inWPow_zero_pow (subst_integral S.w r hg (frame_determinant_integral Fr S.w g j)) la)) (subst_integral S.w r h …`. Establish `hl : τ.level = τ.i + ∑ l, τ.o l + 0 + 0 + 0 + 0` using `by simp [Term.level]`.

Rewrite using `[hl]`. Conclude with `e2`.
-/
theorem symbol_order_ge_level (D : Formalism.BasicNotions.D7) : SymbolOrderGeLevel D := by
  intro p n' r k _ _ O _ _ _ _ S hO hH Fr L₁ N₁ hV Q hQ g hg c' mu la τ hτ _
  unfold Term.sym
  have e1 : InWj S.w (C (algebraMap O (KK O) (S.w ^ τ.i)) * ∏ l, τ.ka0 l) (τ.i + ∑ l, τ.o l) :=
    inWj_mul (inWj_Cpow _) (inWj_prod Finset.univ _ _ (fun l _ => (hτ.1 l).2.2.2.1))
  have e2 := inWj_mul (inWj_mul (inWj_mul (inWj_mul e1
    (inWPow_zero_pow (subst_integral S.w r hg (base_localiser_integral Fr S.w g)) c'))
    (inWj_prod0 (Finset.range Fr.J) _ fun j _ => inWPow_zero_pow (subst_integral S.w r hg (frame_determinant_integral Fr S.w g j)) la))
    (subst_integral S.w r hg (top_product_determinant_integral Fr S.w hH.2.2.1 g mu))) (inWj_map τ.h)
  have hl : τ.level = τ.i + ∑ l, τ.o l + 0 + 0 + 0 + 0 := by simp [Term.level]
  rw [hl]
  exact e2

/- English proof (translation)
Rewrite using `[inA_iff_inWj0 (w := w)]`. Unfold `Term.raw`. Conclude with `inWPow_zero_mul (inWPow_zero_mul (inWPow_zero_mul (inWPow_zero_mul (inWPow_zero_mul (integral_constant_mem_order_zero _) (inWj_prod0 _ _ fun l _ => (inA_iff_inWj0 _).1 (hτ.1 l).1)) (inWPow_zero_pow (local_relation_integral Fr w g) c')) (inWj_prod0 _ _ fun j _ => inWPow_zero_pow ( …`.
-/
theorem raw_symbol_integral {p n' r k : ℕ} [Fact p.Prime] [NeZero n'] {O : Type} [CommRing O] [IsDomain O]
    [Algebra (WF p n') O] (w : O) (Fr : Frames n' r) (hrk : r ≤ k) (Q : ℕ)
    {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (c' mu la : ℕ) (τ : Term n' k O)
    (hτ : τ.Valid p n' w n' r Q g) : InA (τ.raw p n' w Fr hrk g c' mu la) := by
  rw [inA_iff_inWj0 (w := w)]
  unfold Term.raw
  exact inWPow_zero_mul (inWPow_zero_mul (inWPow_zero_mul (inWPow_zero_mul (inWPow_zero_mul (integral_constant_mem_order_zero _)
    (inWj_prod0 _ _ fun l _ => (inA_iff_inWj0 _).1 (hτ.1 l).1))
    (inWPow_zero_pow (local_relation_integral Fr w g) c'))
    (inWj_prod0 _ _ fun j _ => inWPow_zero_pow (frame_determinant_integral Fr w g j) la))
    (top_product_determinant_integral Fr w hrk g mu)) (true_coordinates_integral w hg τ.h)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem orderGe_iff_inWPow_subst {p n' r k : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [Algebra (WF p n') O] (w : O) (g' : Matrix (Fin k) (Fin k) (WF p n')) (F : MvPolynomial (TV n' k) (KK O)) (j : ℕ) :
    ordGe p n' O w n' r g' F j ↔ InWj w (subst p n' O w n' r g' F) j := Iff.rfl

/- English proof (translation)
Establish `hk : ∀ l, InWj w (subst p n' O w n' r g' (τ.ka l)) (τ.o l)` using `fun l => (orderGe_iff_inWPow_subst w g' _ _).1 ((hτ.1 l).2.2.2.2.2 g' hg')`. Establish `e1 : InWj w (subst p n' O w n' r g' (C (algebraMap O (KK O) (w ^ τ.i)) * ∏ l, τ.ka l)) (τ.i + ∑ l, τ.o l)`. Rewrite using `[map_mul, map_prod, subst_C_alt]`. Conclude with `inWj_mul (inWj_Cpow _) (inWj_prod Finset.univ _ _ (fun l _ => hk l))`. Establish `e2 : InWj w (subst p n' O w n' r g' (Rloc p n' O Fr g ^ c')) (c' * 1)`.

Rewrite using `[map_pow]`. Conclude with `inWj_pow eR c'`. Establish `e3 : InWj w (subst p n' O w n' r g' (∏ j ∈ Finset.range Fr.J, (Del p n' O Fr g j) ^ la)) 0` using `subst_integral w r hg' (inWj_prod0 _ _ fun j _ => inWPow_zero_pow (frame_determinant_integral Fr w g j) la)`. Establish `e4` using `subst_integral w r hg' (top_product_determinant_integral Fr w hrk g mu)`. Establish `e5` using `subst_integral w r hg' (true_coordinates_integral w hg τ.h)`.

Establish `hl : τ.level + c' = τ.i + ∑ l, τ.o l + c' * 1 + 0 + 0 + 0` using `by simp [Term.level]`. Rewrite using `[hl]`. Unfold `Term.raw`. Rewrite using `[map_mul, map_mul, map_mul, map_mul]`. Conclude with `inWj_mul (inWj_mul (inWj_mul (inWj_mul e1 e2) e3) e4) e5`.
-/
theorem raw_symbol_order_other_planes {p n' r k : ℕ} [Fact p.Prime] [NeZero n'] {O : Type} [CommRing O] [IsDomain O]
    [Algebra (WF p n') O] (w : O) (Fr : Frames n' r) (hrk : r ≤ k) (Q : ℕ)
    {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (c' mu la : ℕ) (τ : Term n' k O)
    (hτ : τ.Valid p n' w n' r Q g) {g' : Matrix (Fin k) (Fin k) (WF p n')} (hg' : IsGLW g')
    (eR : InWj w (subst p n' O w n' r g' (Rloc p n' O Fr g)) 1) :
    InWj w (subst p n' O w n' r g' (τ.raw p n' w Fr hrk g c' mu la)) (τ.level + c') := by
  have hk : ∀ l, InWj w (subst p n' O w n' r g' (τ.ka l)) (τ.o l) := fun l =>
    (orderGe_iff_inWPow_subst w g' _ _).1 ((hτ.1 l).2.2.2.2.2 g' hg')
  have e1 : InWj w (subst p n' O w n' r g' (C (algebraMap O (KK O) (w ^ τ.i)) * ∏ l, τ.ka l))
      (τ.i + ∑ l, τ.o l) := by
    rw [map_mul, map_prod, subst_C_alt]
    exact inWj_mul (inWj_Cpow _) (inWj_prod Finset.univ _ _ (fun l _ => hk l))
  have e2 : InWj w (subst p n' O w n' r g' (Rloc p n' O Fr g ^ c')) (c' * 1) := by
    rw [map_pow]; exact inWj_pow eR c'
  have e3 : InWj w (subst p n' O w n' r g' (∏ j ∈ Finset.range Fr.J, (Del p n' O Fr g j) ^ la)) 0 :=
    subst_integral w r hg' (inWj_prod0 _ _ fun j _ => inWPow_zero_pow (frame_determinant_integral Fr w g j) la)
  have e4 := subst_integral w r hg' (top_product_determinant_integral Fr w hrk g mu)
  have e5 := subst_integral w r hg' (true_coordinates_integral w hg τ.h)
  have hl : τ.level + c' = τ.i + ∑ l, τ.o l + c' * 1 + 0 + 0 + 0 := by simp [Term.level]
  rw [hl]
  unfold Term.raw
  rw [map_mul, map_mul, map_mul, map_mul]
  exact inWj_mul (inWj_mul (inWj_mul (inWj_mul e1 e2) e3) e4) e5

def RawTermOnTops (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p n' r k : ℕ) [Fact p.Prime] [NeZero n'] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF p n') O] (S : UniformizedDVR p O), OHyp p n' O S → ∀ hH : CommonHypotheses p n' r k,
  ∀ (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ → ∀ Q : ℕ, TwistBound p Fr Q →
  ∀ g : Matrix (Fin k) (Fin k) (WF p n'), IsGLW g →
  ∀ (c' mu la : ℕ) (τ : Term n' k O), τ.Valid p n' S.w n' r Q g → τ.InTops Fr →
    OnTops Fr (τ.raw p n' S.w Fr hH.2.2.1 g c' mu la)

/- English proof (translation)
Introduce `p n' r k _ _ O _ _ _ _ S hO hH Fr L₁ N₁ hV Q hQ g hg c' mu la τ hτ hτ'`. Use `⟨raw_symbol_integral S.w Fr hH.2.2.1 Q hg c' mu la τ hτ, hT p n' r k O S hO hH Fr L₁ N₁ hV Q hQ g hg c' mu la τ hτ hτ', fun g' hg' hne => ?_⟩` and prove the remaining obligations. Rewrite using `[orderGe_iff_inWPow_subst]`. Conclude with `raw_symbol_order_other_planes S.w Fr hH.2.2.1 Q hg c' mu la τ hτ hg' ((orderGe_iff_inWPow_subst _ _ _ _).1 (hL1 p n' r k O S hO hH Fr L₁ N₁ hV g g' hg hg' hne))`.
-/
theorem raw_term_order_ge_off_plane (D : Formalism.BasicNotions.D7) (hL1 : Conclusion1 D) (hT : RawTermOnTops D) : RawSymbolOrderRemaining D := by
  intro p n' r k _ _ O _ _ _ _ S hO hH Fr L₁ N₁ hV Q hQ g hg c' mu la τ hτ hτ'
  refine ⟨raw_symbol_integral S.w Fr hH.2.2.1 Q hg c' mu la τ hτ,
    hT p n' r k O S hO hH Fr L₁ N₁ hV Q hQ g hg c' mu la τ hτ hτ', fun g' hg' hne => ?_⟩
  rw [orderGe_iff_inWPow_subst]
  exact raw_symbol_order_other_planes S.w Fr hH.2.2.1 Q hg c' mu la τ hτ hg'
    ((orderGe_iff_inWPow_subst _ _ _ _).1 (hL1 p n' r k O S hO hH Fr L₁ N₁ hV g g' hg hg' hne))

section B4e

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
variable {n' : ℕ} [NeZero n'] [Algebra (WF p n') O] {k : ℕ}

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Establish `h` using `posOf_val n' (s.val : ℤ)`. Establish `h2 : ((s.val : ℤ)) % (n' : ℤ) = s.val` using `Int.emod_eq_of_lt (by positivity) (by exact_mod_cast s.isLt)`. Rewrite `h` using `[h2]`. Conclude with `h` after adjusting the coercions.
-/
theorem posOf_natCast_self (s : Fin n') : posOf n' (s.val : ℤ) = s := by
  apply Fin.ext
  have h := posOf_val n' (s.val : ℤ)
  have h2 : ((s.val : ℤ)) % (n' : ℤ) = s.val :=
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast s.isLt)
  rw [h2] at h
  exact_mod_cast h

/- English proof (translation)
Unfold `newCoord`. Use `split_ifs with h`. Rewrite using `[subst_xg w r hg hn _ ((Int.even_coe_nat _).2 h), posOf_natCast_self]`. Rewrite using `[subst_yg w r hg hn _ (fun h' => h ((Int.even_coe_nat _).1 h')), posOf_natCast_self]`.
-/
theorem substitute_new_coordinate (w : O) (r : ℕ) {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (hn : Even n')
    (v : TV n' k) : subst p n' O w n' r g (newCoord p n' O n' g v) = newVar w r v := by
  unfold newCoord
  split_ifs with h
  · rw [subst_xg w r hg hn _ ((Int.even_coe_nat _).2 h), posOf_natCast_self]
  · rw [subst_yg w r hg hn _ (fun h' => h ((Int.even_coe_nat _).1 h')), posOf_natCast_self]

/- English proof (translation)
Rewrite using `[true_coordinates_eq_sum, map_sum]`. Use `conv_rhs => rw [(MvPolynomial.map (algebraMap O (KK O)) h).as_sum]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Rewrite using `[map_mul, subst_C_alt, map_prod, monomial_eq, coeff_map, Finsupp.prod]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[map_pow, substitute_new_coordinate w r hg hn, newVar, if_neg]`. Conclude with `hh i (vars_map _ _ ((mem_vars i).2 ⟨d, hd, hi⟩))`.
-/
theorem subst_true_coordinates (w : O) (r : ℕ) {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (hn : Even n')
    (h : MvPolynomial (TV n' k) O) (hh : InTV r h) :
    subst p n' O w n' r g (hTrue p n' O n' g h) = MvPolynomial.map (algebraMap O (KK O)) h := by
  rw [true_coordinates_eq_sum, map_sum]
  conv_rhs => rw [(MvPolynomial.map (algebraMap O (KK O)) h).as_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [map_mul, subst_C_alt, map_prod, monomial_eq, coeff_map, Finsupp.prod]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [map_pow, substitute_new_coordinate w r hg hn, newVar, if_neg]
  exact hh i (vars_map _ _ ((mem_vars i).2 ⟨d, hd, hi⟩))

end B4e

def DifferenceClaimInCoordinates (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p n' r k : ℕ) [Fact p.Prime] [NeZero n'] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF p n') O] (S : UniformizedDVR p O), OHyp p n' O S → ∀ hH : CommonHypotheses p n' r k,
  ∀ (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ → ∀ Q : ℕ, TwistBound p Fr Q →
  ∀ g : Matrix (Fin k) (Fin k) (WF p n'), IsGLW g →
  ∀ (c' o mu la : ℕ) (τ : Term n' k O), τ.Valid p n' S.w n' r Q g → τ.InTops Fr → τ.level < o + c' →
    (2 * (Q : ℤ) + 1) * ((o : ℤ) + c' - 1 - τ.level) ≤ mu → ((o : ℤ) + c' - 1 - τ.level) ≤ la →
    ∃ (m : ℕ) (τ' : Fin m → Term n' k O) (mu' la' : Fin m → ℕ) (ρ : MvPolynomial (TV n' k) (KK O)),
      InWj S.w ρ (o + c') ∧
      C (algebraMap O (KK O) (S.w ^ τ.i)) *
          ((∏ l, subst p n' O S.w n' r g (τ.ka l)) * (subst p n' O S.w n' r g (Rloc p n' O Fr g)) ^ c' -
            (∏ l, τ.ka0 l) * (subst p n' O S.w n' r g (R0 p n' O Fr g)) ^ c') *
          (∏ j ∈ Finset.range Fr.J, (subst p n' O S.w n' r g (Del p n' O Fr g j)) ^ la) *
          subst p n' O S.w n' r g (DtopProd p n' O Fr hH.2.2.1 g mu) * MvPolynomial.map (algebraMap O (KK O)) τ.h =
        ∑ i, (τ' i).sym p n' S.w Fr hH.2.2.1 g c' (mu' i) (la' i) + ρ ∧
      ∀ i, (τ' i).Valid p n' S.w n' r Q g ∧ (τ' i).InTops Fr ∧ τ.level < (τ' i).level ∧ (τ' i).level < o + c' ∧
        (mu' i : ℤ) = (mu : ℤ) - (2 * (Q : ℤ) + 1) * (((τ' i).level : ℤ) - τ.level) ∧
        (la' i : ℤ) = (la : ℤ) - (((τ' i).level : ℤ) - τ.level)

/- English proof (translation)
Introduce `p n' r k _ _ O _ _ _ _ S hO hH Fr L₁ N₁ hV Q hQ g hg c' o mu la τ hτ hτ' hl hmu hla`. Take `⟨m, τ', mu', la', ρ, h1, h2, h3⟩` from `h p n' r k O S hO hH Fr L₁ N₁ hV Q hQ g hg c' o mu la τ hτ hτ' hl hmu hla`. Use `⟨m, τ', mu', la', ρ, h1, ?_, h3⟩` and prove the remaining obligations. Rewrite using `[← h2]`. Unfold `Term.raw Term.sym`.

Rewrite using `[map_mul, map_mul, map_mul, map_mul, map_mul, subst_C_alt, map_prod, map_pow, map_prod, subst_true_coordinates S.w r hg hH.2.2.2.2 τ.h hτ.2]`. Simplify using `only [map_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem order_claim_of_residue_form (D : Formalism.BasicNotions.D7) (h : DifferenceClaimInCoordinates D) : OrderClaimRemaining D := by
  intro p n' r k _ _ O _ _ _ _ S hO hH Fr L₁ N₁ hV Q hQ g hg c' o mu la τ hτ hτ' hl hmu hla
  obtain ⟨m, τ', mu', la', ρ, h1, h2, h3⟩ :=
    h p n' r k O S hO hH Fr L₁ N₁ hV Q hQ g hg c' o mu la τ hτ hτ' hl hmu hla
  refine ⟨m, τ', mu', la', ρ, h1, ?_, h3⟩
  rw [← h2]
  unfold Term.raw Term.sym
  rw [map_mul, map_mul, map_mul, map_mul, map_mul, subst_C_alt, map_prod, map_pow, map_prod,
    subst_true_coordinates S.w r hg hH.2.2.2.2 τ.h hτ.2]
  simp only [map_pow]
  ring

/- English proof (translation)
The claim follows from `divisibility_lemma_of_three_orders D (symbol_order_ge_level D) (raw_term_order_ge_off_plane D hL1 hT) (order_claim_of_residue_form D hC)`.
-/
theorem order_lemma_of_plane_coordinates (D : Formalism.BasicNotions.D7) (hL1 : Conclusion1 D) (hT : RawTermOnTops D) (hC : DifferenceClaimInCoordinates D) : Conclusion4 D :=
  divisibility_lemma_of_three_orders D (symbol_order_ge_level D) (raw_term_order_ge_off_plane D hL1 hT) (order_claim_of_residue_form D hC)

end Formalism.MainNotions.G.WittFrameLocaliserOrders

end

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.G.WittFrameLocaliserOrders

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `sum_mem fun s _ => ?_` and prove the remaining obligations. Break down `Int.units_eq_one_or (Equiv.Perm.sign s) with hs | hs` into its components or cases. Rewrite using `[hs, one_smul]`. Conclude with `prod_mem fun i _ => h _ _`.

Rewrite using `[hs, Units.neg_smul, one_smul]`. Conclude with `neg_mem (prod_mem fun i _ => h _ _)`.
-/
theorem bs_det_mem {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply]
  refine sum_mem fun s _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign s) with hs | hs
  · rw [hs, one_smul]; exact prod_mem fun i _ => h _ _
  · rw [hs, Units.neg_smul, one_smul]; exact neg_mem (prod_mem fun i _ => h _ _)

/- English proof (translation)
Rewrite using `[mem_supported]`. Prove the components needed by the constructor for the conclusion. Introduce `H v hv`. Conclude with `H v (Finset.mem_coe.1 hv)`. Introduce `H v hv`.

Conclude with `H (Finset.mem_coe.2 hv)`.
-/
theorem bs_onTops_iff {R : Type*} [CommRing R] {n' r k : ℕ} (Fr : Frames n' r) (h : MvPolynomial (TV n' k) R) :
    OnTops Fr h ↔ h ∈ supported R {v : TV n' k | v.1 ∈ Fr.TT} := by
  rw [mem_supported]
  constructor
  · intro H v hv; exact H v (Finset.mem_coe.1 hv)
  · intro H v hv; exact H (Finset.mem_coe.2 hv)

section S1

variable {p n' : ℕ} [Fact p.Prime] [NeZero n'] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p n') O] {k : ℕ}

/- English proof (translation)
Unfold `hTrue`. Rewrite using `[aeval_def, eval₂_eq]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_map, algebraMap_eq]`.
-/
theorem bs_hTrue_eq (g : Matrix (Fin k) (Fin k) (WF p n')) (h : MvPolynomial (TV n' k) O) :
    hTrue p n' O n' g h = ∑ d ∈ (MvPolynomial.map (algebraMap O (KK O)) h).support,
      C (algebraMap O (KK O) (h.coeff d)) * ∏ i ∈ d.support, newCoord p n' O n' g i ^ d i := by
  unfold hTrue
  rw [aeval_def, eval₂_eq]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [coeff_map, algebraMap_eq]

variable {r : ℕ} (Fr : Frames n' r)

/- English proof (translation)
The claim follows from `sum_mem fun c _ => mul_mem (X_mem_supported.2 ha) (Subalgebra.algebraMap_mem _ _)`.
-/
theorem bs_top_xg (g : Matrix (Fin k) (Fin k) (WF p n')) (a : ℤ) (ha : posOf n' a ∈ Fr.TT) (b : Fin k) :
    xg p n' O n' g a b ∈ supported (KK O) {v : TV n' k | v.1 ∈ Fr.TT} :=
  sum_mem fun c _ => mul_mem (X_mem_supported.2 ha) (Subalgebra.algebraMap_mem _ _)

/- English proof (translation)
The claim follows from `sum_mem fun c _ => mul_mem (X_mem_supported.2 ha) (Subalgebra.algebraMap_mem _ _)`.
-/
theorem bs_top_yg (g : Matrix (Fin k) (Fin k) (WF p n')) (a : ℤ) (ha : posOf n' a ∈ Fr.TT) (b : Fin k) :
    yg p n' O n' g a b ∈ supported (KK O) {v : TV n' k | v.1 ∈ Fr.TT} :=
  sum_mem fun c _ => mul_mem (X_mem_supported.2 ha) (Subalgebra.algebraMap_mem _ _)

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Establish `h` using `posOf_val n' (s.val : ℤ)`. Establish `h2 : ((s.val : ℤ)) % (n' : ℤ) = s.val` using `Int.emod_eq_of_lt (by positivity) (by exact_mod_cast s.2)`. Rewrite `h` using `[h2]`. Conclude with `h` after adjusting the coercions.
-/
theorem bs_posOf_self (s : Fin n') : posOf n' (s.val : ℤ) = s := by
  apply Fin.ext
  have h := posOf_val n' (s.val : ℤ)
  have h2 : ((s.val : ℤ)) % (n' : ℤ) = s.val := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast s.2)
  rw [h2] at h
  exact_mod_cast h

/- English proof (translation)
Unfold `newCoord`. Use `split_ifs`. Conclude with `bs_top_xg Fr g _ (by rw [bs_posOf_self]; exact hv) _`. Conclude with `bs_top_yg Fr g _ (by rw [bs_posOf_self]; exact hv) _`.
-/
theorem bs_top_newCoord (g : Matrix (Fin k) (Fin k) (WF p n')) (v : TV n' k) (hv : v.1 ∈ Fr.TT) :
    newCoord p n' O n' g v ∈ supported (KK O) {v : TV n' k | v.1 ∈ Fr.TT} := by
  unfold newCoord
  split_ifs
  · exact bs_top_xg Fr g _ (by rw [bs_posOf_self]; exact hv) _
  · exact bs_top_yg Fr g _ (by rw [bs_posOf_self]; exact hv) _

/- English proof (translation)
Rewrite using `[bs_hTrue_eq]`. Use `sum_mem fun d hd => mul_mem (Subalgebra.algebraMap_mem _ _) (prod_mem fun i hi => pow_mem ?_ _)` and prove the remaining obligations. Use `bs_top_newCoord Fr g i (hh i ?_)` and prove the remaining obligations. Rewrite using `[mem_vars]`. Conclude with `⟨d, support_map_subset _ _ hd, hi⟩`.
-/
theorem bs_top_hTrue (g : Matrix (Fin k) (Fin k) (WF p n')) (h : MvPolynomial (TV n' k) O) (hh : OnTops Fr h) :
    hTrue p n' O n' g h ∈ supported (KK O) {v : TV n' k | v.1 ∈ Fr.TT} := by
  rw [bs_hTrue_eq]
  refine sum_mem fun d hd => mul_mem (Subalgebra.algebraMap_mem _ _) (prod_mem fun i hi => pow_mem ?_ _)
  refine bs_top_newCoord Fr g i (hh i ?_)
  rw [mem_vars]
  exact ⟨d, support_map_subset _ _ hd, hi⟩

/- English proof (translation)
Unfold `minorI`. Use `split_ifs with h`. Conclude with `bs_det_mem _ _ fun l i => pow_mem (bs_top_xg Fr g _ (hV.2.2.2.2.1 j l.val l.2).1 _) _`. Conclude with `zero_mem _`.
-/
theorem bs_top_minorI {L₁ N₁ : ℕ} (hV : Fr.Valid L₁ N₁) (g : Matrix (Fin k) (Fin k) (WF p n')) (j : ℤ)
    (I : Finset (Fin k)) : minorI p n' O Fr g j I ∈ supported (KK O) {v : TV n' k | v.1 ∈ Fr.TT} := by
  unfold minorI
  split_ifs with h
  · exact bs_det_mem _ _ fun l i => pow_mem (bs_top_xg Fr g _ (hV.2.2.2.2.1 j l.val l.2).1 _) _
  · exact zero_mem _

/- English proof (translation)
Unfold `Arow`. Distinguish the cases in `h : l < (evensBefore Fr (s.val : ℤ)).length`. Rewrite using `[List.getD_eq_getElem _ _ h]`. Establish `hm` using `List.getElem_mem h`. Unfold `evensBefore at hm`.

Rewrite `hm` using `[List.mem_reverse, Finset.mem_sort, Finset.mem_filter]`. Conclude with `hm.2.1`. Rewrite using `[List.getD_eq_default _ _ (not_lt.1 h), bs_posOf_self]`. Conclude with `hs`.
-/
theorem bs_top_Arow (s : Fin n') (hs : s ∈ Fr.TT) (l : ℕ) : posOf n' (Arow Fr (s.val : ℤ) l) ∈ Fr.TT := by
  unfold Arow
  by_cases h : l < (evensBefore Fr (s.val : ℤ)).length
  · rw [List.getD_eq_getElem _ _ h]
    have hm := List.getElem_mem h
    unfold evensBefore at hm
    rw [List.mem_reverse, Finset.mem_sort, Finset.mem_filter] at hm
    exact hm.2.1
  · rw [List.getD_eq_default _ _ (not_lt.1 h), bs_posOf_self]
    exact hs

/- English proof (translation)
The claim follows from `prod_mem fun s hs => pow_mem (bs_det_mem _ _ fun l b => pow_mem (bs_top_xg Fr g _ (bs_top_Arow Fr s hs _) _) _) _`.
-/
theorem bs_top_DtopProd (hrk : r ≤ k) (g : Matrix (Fin k) (Fin k) (WF p n')) (mu : ℕ) :
    DtopProd p n' O Fr hrk g mu ∈ supported (KK O) {v : TV n' k | v.1 ∈ Fr.TT} :=
  prod_mem fun s hs => pow_mem (bs_det_mem _ _ fun l b => pow_mem (bs_top_xg Fr g _ (bs_top_Arow Fr s hs _) _) _) _

/- English proof (translation)
The claim follows from `mul_mem (bs_top_minorI Fr hV g _ _) (prod_mem fun I _ => sub_mem (prod_mem fun j _ => pow_mem (bs_top_minorI Fr hV g _ _) _) (prod_mem fun j _ => pow_mem (bs_top_minorI Fr hV g _ _) _))`.
-/
theorem bs_top_Rloc {L₁ N₁ : ℕ} (hV : Fr.Valid L₁ N₁) (g : Matrix (Fin k) (Fin k) (WF p n')) :
    Rloc p n' O Fr g ∈ supported (KK O) {v : TV n' k | v.1 ∈ Fr.TT} :=
  mul_mem (bs_top_minorI Fr hV g _ _) (prod_mem fun I _ =>
    sub_mem (prod_mem fun j _ => pow_mem (bs_top_minorI Fr hV g _ _) _)
      (prod_mem fun j _ => pow_mem (bs_top_minorI Fr hV g _ _) _))

end S1

/- English proof (translation)
Introduce `p n' r k _ _ O _ _ _ _ S hO hH Fr L₁ N₁ hV Q hQ g hg c' mu la τ hτ hτT`. Rewrite using `[bs_onTops_iff]`. Conclude with `mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (prod_mem fun l _ => (bs_onTops_iff Fr _).1 (hτT.1 l).1)) (pow_mem (bs_top_Rloc Fr hV g) _)) (prod_mem fun j _ => pow_mem (bs_top_minorI Fr hV g _ _) _)) (bs_top_DtopProd Fr hH.2.2.1 g mu)) (bs_top_hTrue …`.
-/
theorem bs_restRawTops (D : Formalism.BasicNotions.D7) : RawTermOnTops D := by
  intro p n' r k _ _ O _ _ _ _ S hO hH Fr L₁ N₁ hV Q hQ g hg c' mu la τ hτ hτT
  rw [bs_onTops_iff]
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (Subalgebra.algebraMap_mem _ _)
    (prod_mem fun l _ => (bs_onTops_iff Fr _).1 (hτT.1 l).1))
    (pow_mem (bs_top_Rloc Fr hV g) _)) (prod_mem fun j _ => pow_mem (bs_top_minorI Fr hV g _ _) _))
    (bs_top_DtopProd Fr hH.2.2.1 g mu)) (bs_top_hTrue Fr g τ.h hτT.2)

/- English proof (translation)
The claim follows from `divisibility_lemma_of_three_orders D (symbol_order_ge_level D) (raw_term_order_ge_off_plane D hL1 (bs_restRawTops D)) hC`.
-/
theorem divisibility_lemma_of_order_claim (D : Formalism.BasicNotions.D7) (hL1 : Conclusion1 D) (hC : OrderClaimRemaining D) : Conclusion4 D :=
  divisibility_lemma_of_three_orders D (symbol_order_ge_level D) (raw_term_order_ge_off_plane D hL1 (bs_restRawTops D)) hC

end Formalism.MainNotions.G.WittFrameLocaliserOrders

end

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.G.WittFrameLocaliserOrders

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning

def bd_RestCritModW (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O)
    (n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K]
    (Fr : Frames n' r) (j : ℤ) (m : ℤ → ℤ) (th o : ℤ → ℝ),
  (∀ (A : MvPolynomial (ℤ × Fin r) (FF O)) (G : MvPolynomial (ℤ × Fin K) (FF O)) (M : ℤ → ℤ),
    A ∈ supported (FF O) {v : ℤ × Fin r | v.1 ∈ Fr.letters j} →
    G ∈ supported (FF O) {v : ℤ × Fin K | v.1 ∈ Fr.letters j ∧ ¬ Fr.IsW j v.1} →
    (∀ x ∈ Fr.letters j, ¬ Fr.IsW j x →
      (Even x → lam1S LZ {y | y ≤ x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
          ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} A) ∧
      (¬ Even x → lam1S LZ {y | y < x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
          ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} A) ∧
      geR (valS LZ {y | y < x} A) (th x)) →
    (∀ mm ∈ (plEmb (FF O) r K A * nmEmb (FF O) r K G).support, ∀ x ∈ Fr.letters j, ¬ Fr.IsW j x →
      (ordDeg mm x : ℝ) ≤ o x) →
    ∃ P ∈ XX' O r K Fr j m th o,
      MvPolynomial.map (IsLocalRing.residue O) P = plEmb (FF O) r K A * nmEmb (FF O) r K G)

/- English proof (translation)
Introduce `p _ O _ _ _ S n' r K _ _ _ Fr j m th o`. Use `⟨?_, h p O S n' r K Fr j m th o⟩` and prove the remaining obligations. Introduce `A G M hA hG hc ho`. Use `Submodule.mem_inf.mpr ⟨Submodule.subset_span ⟨A, G, M, hA, hG, hc, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.mem_restrictSupport_iff]`.

Introduce `mm hmm x hx hw`. Conclude with `ho mm (by simpa using hmm) x hx hw`.
-/
theorem criterion_of_mod_w_clause (D : Formalism.BasicNotions.D7) (h : bd_RestCritModW D) : SpaceCriterionModuloUniformiser D := by
  intro p _ O _ _ _ S n' r K _ _ _ Fr j m th o
  refine ⟨?_, h p O S n' r K Fr j m th o⟩
  intro A G M hA hG hc ho
  refine Submodule.mem_inf.mpr ⟨Submodule.subset_span ⟨A, G, M, hA, hG, hc, rfl⟩, ?_⟩
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro mm hmm x hx hw
  exact ho mm (by simpa using hmm) x hx hw

/- English proof (translation)
Introduce `p _ O _ _ _ S n' r K _ _ _ Fr j m th o`. Conclude with `(h p O S n' r K Fr j m th o).2`.
-/
theorem mod_w_clause_of_criterion (D : Formalism.BasicNotions.D7) (h : SpaceCriterionModuloUniformiser D) : bd_RestCritModW D := by
  intro p _ O _ _ _ S n' r K _ _ _ Fr j m th o
  exact (h p O S n' r K Fr j m th o).2

/- English proof (translation)
Unfold `HypII at h ⊢`. Take `⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩` from `h`. Establish `hla : 0 ≤ Real.log (a : ℝ)` using `Real.log_natCast_nonneg a`. Establish `hlb : 0 ≤ Real.logb (p : ℝ) (a : ℝ)`. Unfold `Real.logb`.

Conclude with `div_nonneg hla (Real.log_natCast_nonneg p)`. Establish `hY : 0 ≤ Y` using `le_trans (Nat.cast_nonneg r) h4`. Use `⟨h1, h2, h3, h4, le_trans ?_ h5, h6, h7, le_trans ?_ h8, h9, le_trans ?_ h10⟩` and prove the remaining obligations. Use `gcongr`. Use `gcongr`.

Use `gcongr`.
-/
theorem bd_hypII_mono {n' r : ℕ} [NeZero n'] {A B C A' B' C' : ℝ} (hA : A ≤ A') (hB : B ≤ B') (hC : C ≤ C')
    (p : ℕ) (hp : 1 < p) (Fr : Frames n' r) (k L₁ N₁ G' : ℕ) (deg : Fin n' → ℕ) (a : ℕ) (Y : ℝ) (c0 c'' cStar : ℕ)
    (Dd : ℝ) (h : HypII A' B' C' p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd) :
    HypII A B C p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd := by
  unfold HypII at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  have hla : 0 ≤ Real.log (a : ℝ) := Real.log_natCast_nonneg a
  have hlb : 0 ≤ Real.logb (p : ℝ) (a : ℝ) := by
    unfold Real.logb
    exact div_nonneg hla (Real.log_natCast_nonneg p)
  have hY : 0 ≤ Y := le_trans (Nat.cast_nonneg r) h4
  refine ⟨h1, h2, h3, h4, le_trans ?_ h5, h6, h7, le_trans ?_ h8, h9, le_trans ?_ h10⟩
  · gcongr
  · gcongr
  · gcongr

/- English proof (translation)
Introduce `p n' r K _ _ _ _ O _ _ _ _ S hO hH Fr L₁ N₁ G' hV hT deg a Y c0 c'' cStar Dd hII`. Conclude with `h p n' r K O S hO hH Fr L₁ N₁ G' hV hT deg a Y c0 c'' cStar Dd (bd_hypII_mono hA hB hC p (by have := hH.1; omega) Fr _ L₁ N₁ G' deg a Y c0 c'' cStar Dd hII)`.
-/
theorem real_bound_monotone_constants (D : Formalism.BasicNotions.D7) {A B C A' B' C' : ℝ} (hA : A ≤ A') (hB : B ≤ B') (hC : C ≤ C')
    (h : Conclusion6 D A B C) : Conclusion6 D A' B' C' := by
  intro p n' r K _ _ _ _ O _ _ _ _ S hO hH Fr L₁ N₁ G' hV hT deg a Y c0 c'' cStar Dd hII
  exact h p n' r K O S hO hH Fr L₁ N₁ G' hV hT deg a Y c0 c'' cStar Dd
    (bd_hypII_mono hA hB hC p (by have := hH.1; omega) Fr _ L₁ N₁ G' deg a Y c0 c'' cStar Dd hII)

/- English proof (translation)
Unfold `goodU`. Conclude with `Nat.one_le_iff_ne_zero.mpr (by`. Establish `: 0 < 1 / de` using `by positivity`. Conclude with `(Nat.ceil_pos.mpr this).ne')`.
-/
theorem bd_goodU_pos {de : ℝ} (h : 0 < de) : 1 ≤ goodU de := by
  unfold goodU
  exact Nat.one_le_iff_ne_zero.mpr (by
    have : 0 < 1 / de := by positivity
    exact (Nat.ceil_pos.mpr this).ne')

/- English proof (translation)
Establish `hn : (0 : ℤ) < n'` using `by exact_mod_cast NeZero.pos n'`. Apply `Finset.card_le_card_of_injOn (fun t => (posOf n' t).val)` to reduce the goal to its premises. Introduce `t ht`. Simplify using `only [Finset.coe_filter, Finset.mem_Ico, Set.mem_ofPred_eq] at ht`. Take `⟨⟨h1, h2⟩, h3⟩` from `ht`.

Simplify using `only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe]`. Use `⟨Finset.mem_map.mpr ⟨_, h3, rfl⟩, ?_⟩` and prove the remaining obligations. Unfold `Formalism.G0.window`. Use `Finset.mem_image.mpr ⟨(t - y).toNat, Finset.mem_range.mpr (by omega), ?_⟩` and prove the remaining obligations. Unfold `posOf`.

Simplify using `only`. Establish `e1 : (((y % (n' : ℤ)).toNat + (t - y).toNat : ℕ) : ℤ) = y % n' + (t - y)`. Use `Int.emod_nonneg y hn.ne'` as an intermediate fact. Use `push_cast`. Rewrite using `[Int.toNat_of_nonneg this, Int.toNat_of_nonneg (by omega)]`.

Establish `e2 : ((((y % (n' : ℤ)).toNat + (t - y).toNat) % n' : ℕ) : ℤ) = t % n'`. Move the coercions through the operations in `[e1] at e1 ⊢`. Rewrite using `[e1]`. Establish `: y % (n' : ℤ) + (t - y) = t - (n' : ℤ) * (y / n')`. Use `Int.emod_add_mul_ediv y n'` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[this, Int.sub_mul_emod_self_left]`. Establish `e3 : (((t % (n' : ℤ)).toNat % n' : ℕ) : ℤ) = t % n'`. Establish `h0` using `Int.emod_nonneg t hn.ne'`. Establish `h1` using `Int.emod_lt_of_pos t hn`.

Use `push_cast`. Rewrite using `[Int.toNat_of_nonneg h0, Int.emod_emod_of_dvd _ (dvd_refl _)]`. Conclude with `e2.trans e3.symm` after adjusting the coercions. Introduce `a ha b hb hab`. Simplify using `only [Finset.coe_filter, Finset.mem_Ico, Set.mem_ofPred_eq] at ha hb`.

Unfold `posOf at hab`. Simplify using `only at hab`. Establish `ea : (((a % (n' : ℤ)).toNat % n' : ℕ) : ℤ) = a % n'`. Establish `h0` using `Int.emod_nonneg a hn.ne'`. Use `push_cast`.

Rewrite using `[Int.toNat_of_nonneg h0, Int.emod_emod_of_dvd _ (dvd_refl _)]`. Establish `eb : (((b % (n' : ℤ)).toNat % n' : ℕ) : ℤ) = b % n'`. Establish `h0` using `Int.emod_nonneg b hn.ne'`. Use `push_cast`. Rewrite using `[Int.toNat_of_nonneg h0, Int.emod_emod_of_dvd _ (dvd_refl _)]`.

Establish `hm : a % (n' : ℤ) = b % n'` using `by rw [← ea, ← eb, hab]`. Establish `hd : (n' : ℤ) ∣ a - b` using `Int.ModEq.dvd (show b ≡ a [ZMOD (n' : ℤ)] from hm.symm)`. Take `⟨c, hc⟩` from `hd`. Establish `hLz : (L : ℤ) ≤ n'` using `by exact_mod_cast hL`. Establish `: c = 0`.

Assume the negation of the conclusion as `hc0`. Break down `lt_or_gt_of_ne hc0 with h | h` into its components or cases. Establish `: (n' : ℤ) * c ≤ -(n' : ℤ)` using `by nlinarith`. Use linear arithmetic over natural numbers and integers. Establish `: (n' : ℤ) ≤ (n' : ℤ) * c` using `by nlinarith`.

Use linear arithmetic over natural numbers and integers. Substitute `this` using the available equality. Use linear arithmetic over natural numbers and integers.
-/
theorem bd_unfold_card {n' : ℕ} [NeZero n'] (TT : Finset (Fin n')) (y : ℤ) (L : ℕ) (hL : L ≤ n') :
    ((Finset.Ico y (y + L)).filter fun t => posOf n' t ∈ TT).card ≤
      (TT.map Fin.valEmbedding ∩ Formalism.G0.window n' (y % (n' : ℤ)).toNat L).card := by
  have hn : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
  apply Finset.card_le_card_of_injOn (fun t => (posOf n' t).val)
  · intro t ht
    simp only [Finset.coe_filter, Finset.mem_Ico, Set.mem_ofPred_eq] at ht
    obtain ⟨⟨h1, h2⟩, h3⟩ := ht
    simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe]
    refine ⟨Finset.mem_map.mpr ⟨_, h3, rfl⟩, ?_⟩
    unfold Formalism.G0.window
    refine Finset.mem_image.mpr ⟨(t - y).toNat, Finset.mem_range.mpr (by omega), ?_⟩
    unfold posOf
    simp only
    have e1 : (((y % (n' : ℤ)).toNat + (t - y).toNat : ℕ) : ℤ) = y % n' + (t - y) := by
      have := Int.emod_nonneg y hn.ne'
      push_cast
      rw [Int.toNat_of_nonneg this, Int.toNat_of_nonneg (by omega)]
    have e2 : ((((y % (n' : ℤ)).toNat + (t - y).toNat) % n' : ℕ) : ℤ) = t % n' := by
      push_cast [e1] at e1 ⊢
      rw [e1]
      have : y % (n' : ℤ) + (t - y) = t - (n' : ℤ) * (y / n') := by
        have := Int.emod_add_mul_ediv y n'
        linarith
      rw [this, Int.sub_mul_emod_self_left]
    have e3 : (((t % (n' : ℤ)).toNat % n' : ℕ) : ℤ) = t % n' := by
      have h0 := Int.emod_nonneg t hn.ne'
      have h1 := Int.emod_lt_of_pos t hn
      push_cast
      rw [Int.toNat_of_nonneg h0, Int.emod_emod_of_dvd _ (dvd_refl _)]
    exact_mod_cast e2.trans e3.symm
  · intro a ha b hb hab
    simp only [Finset.coe_filter, Finset.mem_Ico, Set.mem_ofPred_eq] at ha hb
    unfold posOf at hab
    simp only at hab
    have ea : (((a % (n' : ℤ)).toNat % n' : ℕ) : ℤ) = a % n' := by
      have h0 := Int.emod_nonneg a hn.ne'
      push_cast
      rw [Int.toNat_of_nonneg h0, Int.emod_emod_of_dvd _ (dvd_refl _)]
    have eb : (((b % (n' : ℤ)).toNat % n' : ℕ) : ℤ) = b % n' := by
      have h0 := Int.emod_nonneg b hn.ne'
      push_cast
      rw [Int.toNat_of_nonneg h0, Int.emod_emod_of_dvd _ (dvd_refl _)]
    have hm : a % (n' : ℤ) = b % n' := by rw [← ea, ← eb, hab]
    have hd : (n' : ℤ) ∣ a - b := Int.ModEq.dvd (show b ≡ a [ZMOD (n' : ℤ)] from hm.symm)
    obtain ⟨c, hc⟩ := hd
    have hLz : (L : ℤ) ≤ n' := by exact_mod_cast hL
    have : c = 0 := by
      by_contra hc0
      rcases lt_or_gt_of_ne hc0 with h | h
      · have : (n' : ℤ) * c ≤ -(n' : ℤ) := by nlinarith
        omega
      · have : (n' : ℤ) ≤ (n' : ℤ) * c := by nlinarith
        omega
    subst this
    omega

/- English proof (translation)
Use `⟨?_, le_refl _, ?_⟩` and prove the remaining obligations. Establish `: (orbitSmallMultiplicity r h x + 1) * ((6 * r + 1) * goodU de) ≤ goodG' r de h x`. Unfold `goodG' goodEll`. Conclude with `Nat.mul_le_mul_right _ (by omega)`. Use linear arithmetic over natural numbers and integers.

Introduce `a ha`. Take `⟨b, _, rfl⟩` from `Finset.mem_map.mp ha`. Conclude with `Finset.mem_range.mpr b.isLt`.
-/
theorem bd_core_hyps {n' : ℕ} (TT : Finset (Fin n')) (r : ℕ) (de h x : ℝ) (h3 : 3 * goodG' r de h x ≤ n') :
    (orbitSmallMultiplicity r h x + 1) * ((6 * r + 1) * goodU de) ≤ n' ∧
      (orbitSmallMultiplicity r h x + 5) * ((6 * r + 1) * goodU de) ≤ goodG' r de h x ∧
      TT.map Fin.valEmbedding ⊆ Finset.range n' := by
  refine ⟨?_, le_refl _, ?_⟩
  · have : (orbitSmallMultiplicity r h x + 1) * ((6 * r + 1) * goodU de) ≤ goodG' r de h x := by
      unfold goodG' goodEll
      exact Nat.mul_le_mul_right _ (by omega)
    omega
  · intro a ha
    obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
    exact Finset.mem_range.mpr b.isLt

/- English proof (translation)
Establish `hn : (0 : ℤ) < n'` using `by exact_mod_cast NeZero.pos n'`. Establish `h0` using `Int.emod_nonneg y hn.ne'`. Establish `h1` using `Int.emod_lt_of_pos y hn`. Use linear arithmetic over natural numbers and integers.
-/
theorem bd_toNat_lt {n' : ℕ} [NeZero n'] (y : ℤ) : (y % (n' : ℤ)).toNat < n' := by
  have hn : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
  have h0 := Int.emod_nonneg y hn.ne'
  have h1 := Int.emod_lt_of_pos y hn
  omega

/- English proof (translation)
Unfold `goodG' goodEll`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem bd_U_le_G' (r : ℕ) (de h x : ℝ) : goodU de ≤ goodG' r de h x := by
  unfold goodG' goodEll
  calc goodU de = 1 * (1 * goodU de) := by ring
    _ ≤ (orbitSmallMultiplicity r h x + 5) * ((6 * r + 1) * goodU de) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul_right _ (by omega))

/- English proof (translation)
The claim follows from `le_trans (bd_unfold_card TT y L₂ hL) (hg.1 _ (bd_toNat_lt y))`.
-/
theorem bd_orbit_interval {n' : ℕ} [NeZero n'] (TT : Finset (Fin n')) (L₂ K r : ℕ) (de h x : ℝ) (hL : L₂ ≤ n')
    (hg : IsGoodOrbit n' TT L₂ K r de h x) (y : ℤ) :
    ((Finset.Ico y (y + L₂)).filter fun t => posOf n' t ∈ TT).card ≤ K :=
  le_trans (bd_unfold_card TT y L₂ hL) (hg.1 _ (bd_toNat_lt y))

/- English proof (translation)
Take `⟨c1, c2, c3⟩` from `bd_core_hyps TT r de h x h3`. Take `⟨Dd, hD, hT, hE⟩` from `Formalism.GrowthSums.Top.nextEvenTop n' (TT.map Fin.valEmbedding) L₂ K r (goodU de) (orbitSmallMultiplicity r h x) (goodG' r de h x) (orbitWindowCount r de h x) hr (bd_goodU_pos hde) c1 c2 c3 hg (posOf n' y).val (posOf n' y).isLt`. Take `⟨hD1, hD2⟩` from `Finset.mem_Icc.mp hD`. Establish `hval : (posOf n' (y + Dd)).val = ((posOf n' y).val + Dd) % n'`. Establish `e1` using `posOf_val n' (y + Dd)`.

Establish `e2` using `posOf_val n' y`. Establish `: (((posOf n' y).val + Dd) % n' : ℕ) = ((y + Dd) % (n' : ℤ))`. Use `push_cast`. Rewrite using `[e2, Int.emod_add_emod]`. Conclude with `e1.trans this.symm` after adjusting the coercions.

Establish `hle : z ≤ y + Dd`. Assume the negation of the conclusion as `hlt`. Use `hno (y + Dd) (by omega) (by omega) ⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨b, hb, hbe⟩` from `Finset.mem_map.mp hT`. Establish `: b = posOf n' (y + Dd)` using `Fin.ext (by rw [hval]; exact hbe)`.

Conclude with `this ▸ hb`. Rewrite using `[← posOf_even hn, hval]`. Conclude with `hE`. Establish `hG : z - y ≤ goodG' r de h x`. Establish `: (Dd : ℤ) ≤ goodG' r de h x` using `by exact_mod_cast hD2`.

Use linear arithmetic over natural numbers and integers. Use `⟨hG, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.card_le_card` to reduce the goal to its premises. Apply `Finset.filter_subset_filter` to reduce the goal to its premises.

Introduce `t ht`. Rewrite `ht` using `[Finset.mem_Ioo]`. Rewrite using `[Finset.mem_Ico]`. Use linear arithmetic over natural numbers and integers. Use `_ ≤ _ := bd_unfold_card TT (y + 1) _ (by omega)`.

Use `_ ≤ orbitWindowCount r de h x := hg.2.2 _ (bd_toNat_lt (y + 1))`.
-/
theorem bd_orbit_next {n' : ℕ} [NeZero n'] (TT : Finset (Fin n')) (L₂ K r : ℕ) (de h x : ℝ) (hn : Even n')
    (hr : 1 ≤ r) (hde : 0 < de) (h3 : 3 * goodG' r de h x ≤ n') (hg : IsGoodOrbit n' TT L₂ K r de h x)
    (y z : ℤ) (_hyz : y < z) (_hy : posOf n' y ∈ TT) (_hye : Even y) (_hz : posOf n' z ∈ TT) (_hze : Even z)
    (hno : ∀ t : ℤ, y < t → t < z → ¬ (posOf n' t ∈ TT ∧ Even t)) :
    z - y ≤ goodG' r de h x ∧ ((Finset.Ioo y z).filter fun t => posOf n' t ∈ TT).card ≤ orbitWindowCount r de h x := by
  obtain ⟨c1, c2, c3⟩ := bd_core_hyps TT r de h x h3
  obtain ⟨Dd, hD, hT, hE⟩ := Formalism.GrowthSums.Top.nextEvenTop n' (TT.map Fin.valEmbedding) L₂ K r (goodU de) (orbitSmallMultiplicity r h x)
    (goodG' r de h x) (orbitWindowCount r de h x) hr (bd_goodU_pos hde) c1 c2 c3 hg (posOf n' y).val (posOf n' y).isLt
  obtain ⟨hD1, hD2⟩ := Finset.mem_Icc.mp hD
  have hval : (posOf n' (y + Dd)).val = ((posOf n' y).val + Dd) % n' := by
    have e1 := posOf_val n' (y + Dd)
    have e2 := posOf_val n' y
    have : (((posOf n' y).val + Dd) % n' : ℕ) = ((y + Dd) % (n' : ℤ)) := by
      push_cast
      rw [e2, Int.emod_add_emod]
    exact_mod_cast e1.trans this.symm
  have hle : z ≤ y + Dd := by
    by_contra hlt
    refine hno (y + Dd) (by omega) (by omega) ⟨?_, ?_⟩
    · obtain ⟨b, hb, hbe⟩ := Finset.mem_map.mp hT
      have : b = posOf n' (y + Dd) := Fin.ext (by rw [hval]; exact hbe)
      exact this ▸ hb
    · rw [← posOf_even hn, hval]; exact hE
  have hG : z - y ≤ goodG' r de h x := by
    have : (Dd : ℤ) ≤ goodG' r de h x := by exact_mod_cast hD2
    omega
  refine ⟨hG, ?_⟩
  calc ((Finset.Ioo y z).filter fun t => posOf n' t ∈ TT).card
      ≤ ((Finset.Ico (y + 1) (y + 1 + (goodG' r de h x : ℕ))).filter fun t => posOf n' t ∈ TT).card := by
        apply Finset.card_le_card
        apply Finset.filter_subset_filter
        intro t ht
        rw [Finset.mem_Ioo] at ht
        rw [Finset.mem_Ico]
        omega
    _ ≤ _ := bd_unfold_card TT (y + 1) _ (by omega)
    _ ≤ orbitWindowCount r de h x := hg.2.2 _ (bd_toNat_lt (y + 1))

/- English proof (translation)
Establish `hh3 : 0 ≤ (h + 3) * lx` using `by positivity`. Establish `hq : 0 ≤ (h + 3) * lx / P` using `by positivity`. Establish `hq1 : (h + 3) * lx ≤ (h + 3) * lx / P`. Rewrite using `[le_div_iff₀ hP0]`. Conclude with `mul_le_of_le_one_right hh3 hP1`.

Establish `hM0 : 0 ≤ M` using `le_trans hq hM1`. Establish `hGde : G * de = (M + 5) * R * (u * de)` using `by rw [hG]; ring`. Establish `hMR : 0 ≤ (M + 5) * R` using `by positivity`. Establish `hup : G * de ≤ (M + 5) * R * 2` using `by rw [hGde]; exact mul_le_mul_of_nonneg_left hud2 hMR`. Establish `hlo : (M + 5) * R ≤ G * de` using `by rw [hGde]; exact le_mul_of_one_le_right hMR hud1`.

Establish `hc0 : 0 ≤ (h + 3) / P` using `by positivity`. Establish `hM5 : M + 5 ≤ ((h + 3) / P + 6) * lx`. Establish `e : (h + 3) * lx / P = (h + 3) / P * lx` using `by ring`. Rewrite `hM2` using `[e]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hR0 : 0 ≤ R` using `by linarith`. Establish `hCe : G * de ≤ (((h + 3) / P + 6) * R * 2) * lx`. Combine the equalities or inequalities in the displayed calculation. Establish `hMR5 : M + 5 ≤ (M + 5) * R` using `le_mul_of_one_le_right (by linarith) (by linarith)`. Establish `hG5 : 5 ≤ G * de` using `by linarith`.

Establish `hGpos : 0 < G`. Assume the negation of the conclusion as `hneg`. Establish `: G * de ≤ 0` using `mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) hde.le`. Combine the linear equalities and inequalities to obtain the conclusion. Prove the components needed by the constructor for the conclusion.

Rewrite using `[div_le_iff₀ (by positivity)]`. Combine the equalities or inequalities in the displayed calculation. Establish `he1 : 1 ≤ Real.exp 1` using `by have := Real.add_one_le_exp (1 : ℝ); linarith`. Establish `he2` using `Real.exp_one_lt_d9`. Establish `hA : B ≤ 6 * Real.exp 1 * G * de`.

Establish `: 6 * (G * de) ≤ 6 * Real.exp 1 * G * de` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hN1` using `[max_eq_left hA]`. Establish `hN1' : N1 ≤ 16.8 * (G * de)` using `by nlinarith`. Establish `hnG : n + G ≤ 4 / 3 * n` using `by linarith`.

Establish `hfin : N * G ≤ (22.4 * de * n) * G`. Combine the equalities or inequalities in the displayed calculation. Use `le_of_mul_le_mul_right hfin hGpos` as an intermediate fact. Establish `hnd : 0 ≤ n * de` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bd_count_real (n N G N1 u M P de h lx R B : ℝ)
    (hR : 13 ≤ R) (hh : 0 ≤ h) (hde : 0 < de) (hlx : 1 ≤ lx) (hP0 : 0 < P) (hP1 : P ≤ 1)
    (hud1 : 1 ≤ u * de) (hud2 : u * de ≤ 2) (hM1 : (h + 3) * lx / P ≤ M) (hM2 : M ≤ (h + 3) * lx / P + 1)
    (hG : G = (M + 5) * (R * u)) (hB : B ≤ 2 * ((h + 3) * lx))
    (hN1 : N1 ≤ max (6 * Real.exp 1 * G * de) B + 2)
    (hn0 : 0 ≤ n) (hN0 : 0 ≤ N) (h3 : 3 * G ≤ n) (h1 : n ≤ N * G) (h2 : N * G ≤ N1 * (n + G)) :
    n * de / ((((h + 3) / P + 6) * R * 2) * lx) ≤ N ∧ N ≤ 40 * n * de := by
  have hh3 : 0 ≤ (h + 3) * lx := by positivity
  have hq : 0 ≤ (h + 3) * lx / P := by positivity
  have hq1 : (h + 3) * lx ≤ (h + 3) * lx / P := by
    rw [le_div_iff₀ hP0]
    exact mul_le_of_le_one_right hh3 hP1
  have hM0 : 0 ≤ M := le_trans hq hM1
  have hGde : G * de = (M + 5) * R * (u * de) := by rw [hG]; ring
  have hMR : 0 ≤ (M + 5) * R := by positivity
  have hup : G * de ≤ (M + 5) * R * 2 := by rw [hGde]; exact mul_le_mul_of_nonneg_left hud2 hMR
  have hlo : (M + 5) * R ≤ G * de := by rw [hGde]; exact le_mul_of_one_le_right hMR hud1
  have hc0 : 0 ≤ (h + 3) / P := by positivity
  have hM5 : M + 5 ≤ ((h + 3) / P + 6) * lx := by
    have e : (h + 3) * lx / P = (h + 3) / P * lx := by ring
    rw [e] at hM2
    nlinarith
  have hR0 : 0 ≤ R := by linarith
  have hCe : G * de ≤ (((h + 3) / P + 6) * R * 2) * lx := by
    calc G * de ≤ (M + 5) * R * 2 := hup
      _ ≤ (((h + 3) / P + 6) * lx) * R * 2 := by gcongr
      _ = _ := by ring
  have hMR5 : M + 5 ≤ (M + 5) * R := le_mul_of_one_le_right (by linarith) (by linarith)
  have hG5 : 5 ≤ G * de := by linarith
  have hGpos : 0 < G := by
    by_contra hneg
    have : G * de ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) hde.le
    linarith
  constructor
  · rw [div_le_iff₀ (by positivity)]
    calc n * de ≤ N * G * de := by gcongr
      _ = N * (G * de) := by ring
      _ ≤ N * ((((h + 3) / P + 6) * R * 2) * lx) := by gcongr
  · have he1 : 1 ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    have he2 := Real.exp_one_lt_d9
    have hA : B ≤ 6 * Real.exp 1 * G * de := by
      have : 6 * (G * de) ≤ 6 * Real.exp 1 * G * de := by nlinarith
      linarith
    rw [max_eq_left hA] at hN1
    have hN1' : N1 ≤ 16.8 * (G * de) := by nlinarith
    have hnG : n + G ≤ 4 / 3 * n := by linarith
    have hfin : N * G ≤ (22.4 * de * n) * G := by
      calc N * G ≤ N1 * (n + G) := h2
        _ ≤ (16.8 * (G * de)) * (n + G) := by gcongr
        _ ≤ (16.8 * (G * de)) * (4 / 3 * n) := by gcongr
        _ = (22.4 * de * n) * G := by ring
    have := le_of_mul_le_mul_right hfin hGpos
    have hnd : 0 ≤ n * de := by positivity
    linarith

def bd_Ce (r : ℕ) (h : ℝ) : ℝ := ((h + 3) / (10 : ℝ) ^ (-((6 * r + 1 : ℕ) : ℤ)) + 6) * (6 * (r : ℝ) + 1) * 2

/- English proof (translation)
Unfold `bd_Ce`. Check the signs of the components of the expression.
-/
theorem bd_Ce_pos (r : ℕ) (h : ℝ) (hh : 0 ≤ h) : 0 < bd_Ce r h := by unfold bd_Ce; positivity

/- English proof (translation)
Take `⟨c1, c2, c3⟩` from `bd_core_hyps TT r de h x h3`. Take `⟨t1, t2⟩` from `Formalism.GrowthSums.Top.topCount n' (TT.map Fin.valEmbedding) L₂ K r (goodU de) (orbitSmallMultiplicity r h x) (goodG' r de h x) (orbitWindowCount r de h x) (by omega) (bd_goodU_pos hde) c1 c2 c3 hg`. Rewrite `t1`, `t2` using `[Finset.card_map]`. Establish `hlx : 1 ≤ Real.log x`. Rewrite using `[Real.le_log_iff_exp_le (by linarith)]`.

Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hP0 : 0 < (10 : ℝ) ^ (-((6 * r + 1 : ℕ) : ℤ))` using `by positivity`. Establish `hP1 : (10 : ℝ) ^ (-((6 * r + 1 : ℕ) : ℤ)) ≤ 1`. Rewrite using `[zpow_neg]`.

Conclude with `inv_le_one_of_one_le₀ (one_le_zpow₀ (by norm_num) (by positivity))`. Establish `hu1 : 1 / de ≤ (goodU de : ℝ)` using `Nat.le_ceil _`. Establish `hu2 : (goodU de : ℝ) < 1 / de + 1` using `Nat.ceil_lt_add_one (by positivity)`. Establish `hud1 : 1 ≤ (goodU de : ℝ) * de` using `by rwa [div_le_iff₀ hde] at hu1`. Establish `hud2 : (goodU de : ℝ) * de ≤ 2`.

Establish `h' : (goodU de : ℝ) * de < (1 / de + 1) * de` using `mul_lt_mul_of_pos_right hu2 hde`. Establish `e : (1 / de + 1) * de = 1 + de` using `by field_simp`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hM1 : (h + 3) * Real.log x / (10 : ℝ) ^ (-((6 * r + 1 : ℕ) : ℤ)) ≤ (orbitSmallMultiplicity r h x : ℝ)` using `Nat.le_ceil _`. Establish `hM2 : (orbitSmallMultiplicity r h x : ℝ) < (h + 3) * Real.log x / (10 : ℝ) ^ (-((6 * r + 1 : ℕ) : ℤ)) + 1` using `Nat.ceil_lt_add_one (by positivity)`.

Establish `hG : (goodG' r de h x : ℝ) = ((orbitSmallMultiplicity r h x : ℝ) + 5) * ((6 * (r : ℝ) + 1) * (goodU de : ℝ))`. Unfold `goodG' goodEll`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hB : (h + 3) * Real.logb 2 x ≤ 2 * ((h + 3) * Real.log x)`.

Establish `hl2` using `Real.log_two_gt_d9`. Establish `: Real.logb 2 x ≤ 2 * Real.log x`. Unfold `Real.logb`. Rewrite using `[div_le_iff₀ (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities.

Use the polynomial consequences of the given equalities and inequalities. Establish `hN1 : (orbitWindowCount r de h x : ℝ) ≤ max (6 * Real.exp 1 * (goodG' r de h x : ℝ) * de) ((h + 3) * Real.logb 2 x) + 2`. Unfold `orbitWindowCount`. Use `push_cast`. Use `Nat.ceil_lt_add_one (a := max (6 * Real.exp 1 * (goodG' r de h x : ℝ) * de) ((h + 3) * Real.logb 2 x)) (le_max_of_le_left (by positivity))` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hR : (13 : ℝ) ≤ 6 * (r : ℝ) + 1`. Establish `: (2 : ℝ) ≤ r` using `by exact_mod_cast hr`. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `bd_Ce`.

Conclude with `bd_count_real n' TT.card (goodG' r de h x) (orbitWindowCount r de h x) (goodU de) (orbitSmallMultiplicity r h x) _ de h (Real.log x) (6 * (r : ℝ) + 1) _ hR hh hde hlx hP0 hP1 hud1 hud2 hM1 hM2.le hG hB hN1 (by positivity) (by positivity) (by exact_mod_cast h3) (by exact_mod_cast …`.
-/
theorem bd_orbit_count {n' : ℕ} [NeZero n'] (TT : Finset (Fin n')) (L₂ K r : ℕ) (de h x : ℝ)
    (hr : 2 ≤ r) (hh : 0 ≤ h) (hde : 0 < de) (hde1 : de ≤ 1) (hx : 3 ≤ x)
    (h3 : 3 * goodG' r de h x ≤ n') (hg : IsGoodOrbit n' TT L₂ K r de h x) :
    (n' : ℝ) * de / (bd_Ce r h * Real.log x) ≤ TT.card ∧ (TT.card : ℝ) ≤ 40 * n' * de := by
  obtain ⟨c1, c2, c3⟩ := bd_core_hyps TT r de h x h3
  obtain ⟨t1, t2⟩ := Formalism.GrowthSums.Top.topCount n' (TT.map Fin.valEmbedding) L₂ K r (goodU de) (orbitSmallMultiplicity r h x)
    (goodG' r de h x) (orbitWindowCount r de h x) (by omega) (bd_goodU_pos hde) c1 c2 c3 hg
  rw [Finset.card_map] at t1 t2
  have hlx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hP0 : 0 < (10 : ℝ) ^ (-((6 * r + 1 : ℕ) : ℤ)) := by positivity
  have hP1 : (10 : ℝ) ^ (-((6 * r + 1 : ℕ) : ℤ)) ≤ 1 := by
    rw [zpow_neg]
    exact inv_le_one_of_one_le₀ (one_le_zpow₀ (by norm_num) (by positivity))
  have hu1 : 1 / de ≤ (goodU de : ℝ) := Nat.le_ceil _
  have hu2 : (goodU de : ℝ) < 1 / de + 1 := Nat.ceil_lt_add_one (by positivity)
  have hud1 : 1 ≤ (goodU de : ℝ) * de := by rwa [div_le_iff₀ hde] at hu1
  have hud2 : (goodU de : ℝ) * de ≤ 2 := by
    have h' : (goodU de : ℝ) * de < (1 / de + 1) * de := mul_lt_mul_of_pos_right hu2 hde
    have e : (1 / de + 1) * de = 1 + de := by field_simp
    linarith
  have hM1 : (h + 3) * Real.log x / (10 : ℝ) ^ (-((6 * r + 1 : ℕ) : ℤ)) ≤ (orbitSmallMultiplicity r h x : ℝ) := Nat.le_ceil _
  have hM2 : (orbitSmallMultiplicity r h x : ℝ) < (h + 3) * Real.log x / (10 : ℝ) ^ (-((6 * r + 1 : ℕ) : ℤ)) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hG : (goodG' r de h x : ℝ) = ((orbitSmallMultiplicity r h x : ℝ) + 5) * ((6 * (r : ℝ) + 1) * (goodU de : ℝ)) := by
    unfold goodG' goodEll
    push_cast
    ring
  have hB : (h + 3) * Real.logb 2 x ≤ 2 * ((h + 3) * Real.log x) := by
    have hl2 := Real.log_two_gt_d9
    have : Real.logb 2 x ≤ 2 * Real.log x := by
      unfold Real.logb
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    nlinarith
  have hN1 : (orbitWindowCount r de h x : ℝ) ≤
      max (6 * Real.exp 1 * (goodG' r de h x : ℝ) * de) ((h + 3) * Real.logb 2 x) + 2 := by
    unfold orbitWindowCount
    push_cast
    have := Nat.ceil_lt_add_one (a := max (6 * Real.exp 1 * (goodG' r de h x : ℝ) * de) ((h + 3) * Real.logb 2 x))
      (le_max_of_le_left (by positivity))
    linarith
  have hR : (13 : ℝ) ≤ 6 * (r : ℝ) + 1 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  unfold bd_Ce
  exact bd_count_real n' TT.card (goodG' r de h x) (orbitWindowCount r de h x) (goodU de) (orbitSmallMultiplicity r h x) _ de h (Real.log x)
    (6 * (r : ℝ) + 1) _ hR hh hde hlx hP0 hP1 hud1 hud2 hM1 hM2.le hG hB hN1 (by positivity) (by positivity)
    (by exact_mod_cast h3) (by exact_mod_cast t1) (by exact_mod_cast t2)

def bd_RestOrbit (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (r : ℕ) (h : ℝ), 2 ≤ r → 0 ≤ h →
  ∀ (n' : ℕ) [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de x : ℝ),
    Even n' → 1 ≤ L₁ → 2 * L₁ ≤ L₂ → 0 < de → de ≤ 1 → 3 ≤ x → L₂ < goodU de →
    3 * goodG' r de h x ≤ n' → IsGoodOrbit n' TT L₂ (r - 1) r de h x →
    let u := goodU de
    let G' := goodG' r de h x
    let N₁ := orbitWindowCount r de h x
    let T := TT.map Fin.valEmbedding
    let ell := (6 * r + 1) * u
    (∃ F : Frames n' r, F.TT = TT ∧ F.Valid L₁ N₁ ∧
      (∀ j : ℤ, ∀ i < r, ∃ s < n' / ell, Formalism.G0.Marked T r u s ∧
        (F.fr j i % (n' : ℤ)).toNat ∈ Formalism.G0.cell r u s (2 * r + 2 + 2 * i)) ∧
      (∀ s < n' / ell, Formalism.G0.Marked T r u s → ∃ j : ℤ, (F.fr j 0 % (n' : ℤ)).toNat ∈ Formalism.G0.cell r u s (2 * r + 2)) ∧
      (∀ j : ℤ, F.fr j (r - 1) - F.fr (j - 1) 0 ≤ G' ∧ (F.letters j).card ≤ N₁) ∧
      (∀ j : ℤ, ∀ x ∈ F.LLset j, (((F.LLset j).filter (· ≤ x)).card ≤ r ∨
          (F.LLset j).card < ((F.LLset j).filter (· ≤ x)).card + r) → F.GapGt L₂ j x) ∧
      (∀ j : ℤ, F.GapGt L₂ j (F.fr j 0)))

/- English proof (translation)
Introduce `r h hr hh`. Use `⟨bd_Ce r h, bd_Ce_pos r h hh, ?_⟩` and prove the remaining obligations. Introduce `n' _ TT L₁ L₂ de x hn hL1 hL12 hde hde1 hx hLu h3 hg`. Establish `hL2n : L₂ ≤ n'` using `by have := bd_U_le_G' r de h x; omega`. Establish `hcnt` using `bd_orbit_count TT L₂ (r - 1) r de h x hr hh hde hde1 hx h3 hg`.

Introduce `u G' N₁ T ell`. Conclude with `⟨fun s _ hm => Formalism.G0.Top.markedRun _ r _ s (bd_goodU_pos hde) hm, hR r h hr hh n' TT L₁ L₂ de x hn hL1 hL12 hde hde1 hx hLu h3 hg, fun y z hyz a b c d e => bd_orbit_next TT L₂ (r - 1) r de h x hn (by omega) hde h3 hg y z hyz a b c d e, hcnt.1, hcnt.2, fun y => bd_orbit_int …`.
-/
theorem good_orbits_of_frames (D : Formalism.BasicNotions.D7) (hR : bd_RestOrbit D) : GoodOrbitPositions D := by
  intro r h hr hh
  refine ⟨bd_Ce r h, bd_Ce_pos r h hh, ?_⟩
  intro n' _ TT L₁ L₂ de x hn hL1 hL12 hde hde1 hx hLu h3 hg
  have hL2n : L₂ ≤ n' := by have := bd_U_le_G' r de h x; omega
  have hcnt := bd_orbit_count TT L₂ (r - 1) r de h x hr hh hde hde1 hx h3 hg
  intro u G' N₁ T ell
  exact ⟨fun s _ hm => Formalism.G0.Top.markedRun _ r _ s (bd_goodU_pos hde) hm,
    hR r h hr hh n' TT L₁ L₂ de x hn hL1 hL12 hde hde1 hx hLu h3 hg,
    fun y z hyz a b c d e => bd_orbit_next TT L₂ (r - 1) r de h x hn (by omega) hde h3 hg y z hyz a b c d e,
    hcnt.1, hcnt.2, fun y => bd_orbit_interval TT L₂ (r - 1) r de h x hL2n hg y⟩

/- English proof (translation)
Introduce `r h hr hh n' _ TT L₁ L₂ de x hn hL1 hL12 hde hde1 hx hLu h3 hg`. Take `⟨Ce, _, hC⟩` from `hA r h hr hh`. Conclude with `(hC n' TT L₁ L₂ de x hn hL1 hL12 hde hde1 hx hLu h3 hg).2.1`.
-/
theorem orbit_clauses_of_lemma (D : Formalism.BasicNotions.D7) (hA : GoodOrbitPositions D) : bd_RestOrbit D := by
  intro r h hr hh n' _ TT L₁ L₂ de x hn hL1 hL12 hde hde1 hx hLu h3 hg
  obtain ⟨Ce, _, hC⟩ := hA r h hr hh
  exact (hC n' TT L₁ L₂ de x hn hL1 hL12 hde hde1 hx hLu h3 hg).2.1

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `t ht`. Unfold `Frames.letters at ht`. Simplify using `only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico] at ht ⊢`.

Conclude with `⟨⟨ht.1.1, by omega⟩, ht.2⟩`. Use `_ ≤ _ := bd_unfold_card F.TT _ _ hGn`. Use `_ ≤ _ := hg.2.2 _ (bd_toNat_lt _)`.
-/
theorem bd_letters_card {n' r : ℕ} [NeZero n'] (F : Frames n' r) (L₂ K r' : ℕ) (de h x : ℝ)
    (hGn : goodG' r' de h x ≤ n') (hg : IsGoodOrbit n' F.TT L₂ K r' de h x) (j : ℤ)
    (hlen : F.fr j (r - 1) - F.fr (j - 1) 0 < goodG' r' de h x) : (F.letters j).card ≤ orbitWindowCount r' de h x := by
  calc (F.letters j).card
      ≤ ((Finset.Ico (F.fr (j - 1) 0) (F.fr (j - 1) 0 + (goodG' r' de h x : ℕ))).filter
          fun t => posOf n' t ∈ F.TT).card := by
        apply Finset.card_le_card
        intro t ht
        unfold Frames.letters at ht
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico] at ht ⊢
        exact ⟨⟨ht.1.1, by omega⟩, ht.2⟩
    _ ≤ _ := bd_unfold_card F.TT _ _ hGn
    _ ≤ _ := hg.2.2 _ (bd_toNat_lt _)

/- English proof (translation)
Take `⟨E, hEdef⟩ : ∃ E, E = (F.letters j).filter fun z => Even z ∧ z < x` from `⟨_, rfl⟩`. Rewrite `hE` using `[← hEdef]`. Establish `hidx : E.card - r < E.card` using `by omega`. Establish `ho : F.oldest j x = E.orderEmbOfFin rfl ⟨E.card - r, hidx⟩`. Unfold `Frames.oldest`.

Simplify using `only`. Rewrite using `[← hEdef, Finset.length_sort, List.getD_eq_getElem _ _ (by rw [Finset.length_sort]; exact hidx), Finset.orderEmbOfFin_apply]`. Both sides reduce to the same expression. Assume the negation of the conclusion as `hcon`. Establish `hcon' : x - F.oldest j x ≤ L₁` using `not_lt.mp hcon`.

Establish `hcard : (Finset.univ : Finset (Fin r)).card ≤ ((Finset.Ico (F.oldest j x) (F.oldest j x + L₂)).filter fun t => posOf n' t ∈ F.TT).card`. Apply `Finset.card_le_card_of_injOn (fun i : Fin r => E.orderEmbOfFin rfl ⟨E.card - r + i.val, by omega⟩)` to reduce the goal to its premises. Introduce `i _`. Establish `hmem : E.orderEmbOfFin rfl ⟨E.card - r + i.val, by omega⟩ ∈ E` using `Finset.orderEmbOfFin_mem E rfl _`. Establish `hge : F.oldest j x ≤ E.orderEmbOfFin rfl ⟨E.card - r + i.val, by omega⟩`.

Rewrite using `[ho]`. Conclude with `(E.orderEmbOfFin rfl).monotone (by rw [Fin.le_def]; simp)`. Use `replace hmem := (Finset.ext_iff.mp hEdef _).mp hmem`. Unfold `Frames.letters at hmem`. Simplify using `only [Finset.mem_filter, Finset.mem_Icc] at hmem`.

Simplify using `only [Finset.coe_filter, Finset.mem_Ico, Set.mem_ofPred_eq]`. Establish `hLz : (L₁ : ℤ) + 1 ≤ L₂` using `by exact_mod_cast hL`. Conclude with `⟨⟨hge, by omega⟩, hmem.1.2⟩`. Introduce `a _ b _ hab`. Use `(E.orderEmbOfFin rfl).injective hab` as an intermediate fact.

Establish `h2` using `Fin.mk.inj this`. Conclude with `Fin.ext (by omega)`. Use `hI (F.oldest j x)` as an intermediate fact. Rewrite `hcard` using `[Finset.card_univ, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers.
-/
theorem bd_oldest_far {n' r : ℕ} [NeZero n'] (F : Frames n' r) (L₁ L₂ : ℕ) (hr : 1 ≤ r) (hL : L₁ + 1 ≤ L₂)
    (hI : ∀ y : ℤ, ((Finset.Ico y (y + L₂)).filter fun t => posOf n' t ∈ F.TT).card ≤ r - 1)
    (j x : ℤ) (hE : r ≤ ((F.letters j).filter fun z => Even z ∧ z < x).card) :
    (L₁ : ℤ) < x - F.oldest j x := by
  obtain ⟨E, hEdef⟩ : ∃ E, E = (F.letters j).filter fun z => Even z ∧ z < x := ⟨_, rfl⟩
  rw [← hEdef] at hE
  have hidx : E.card - r < E.card := by omega
  have ho : F.oldest j x = E.orderEmbOfFin rfl ⟨E.card - r, hidx⟩ := by
    unfold Frames.oldest
    simp only
    rw [← hEdef, Finset.length_sort, List.getD_eq_getElem _ _ (by rw [Finset.length_sort]; exact hidx),
      Finset.orderEmbOfFin_apply]
    rfl
  by_contra hcon
  have hcon' : x - F.oldest j x ≤ L₁ := not_lt.mp hcon
  have hcard : (Finset.univ : Finset (Fin r)).card ≤
      ((Finset.Ico (F.oldest j x) (F.oldest j x + L₂)).filter fun t => posOf n' t ∈ F.TT).card := by
    apply Finset.card_le_card_of_injOn (fun i : Fin r => E.orderEmbOfFin rfl ⟨E.card - r + i.val, by omega⟩)
    · intro i _
      have hmem : E.orderEmbOfFin rfl ⟨E.card - r + i.val, by omega⟩ ∈ E := Finset.orderEmbOfFin_mem E rfl _
      have hge : F.oldest j x ≤ E.orderEmbOfFin rfl ⟨E.card - r + i.val, by omega⟩ := by
        rw [ho]
        exact (E.orderEmbOfFin rfl).monotone (by rw [Fin.le_def]; simp)
      replace hmem := (Finset.ext_iff.mp hEdef _).mp hmem
      unfold Frames.letters at hmem
      simp only [Finset.mem_filter, Finset.mem_Icc] at hmem
      simp only [Finset.coe_filter, Finset.mem_Ico, Set.mem_ofPred_eq]
      have hLz : (L₁ : ℤ) + 1 ≤ L₂ := by exact_mod_cast hL
      exact ⟨⟨hge, by omega⟩, hmem.1.2⟩
    · intro a _ b _ hab
      have := (E.orderEmbOfFin rfl).injective hab
      have h2 := Fin.mk.inj this
      exact Fin.ext (by omega)
  have := hI (F.oldest j x)
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  omega

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro i hi`. Conclude with `hs j i hi`. Consider the case `succ d ih`.

Introduce `i hi`. Conclude with `lt_trans (ih i (by omega)) (hs j (i + (d + 1)) hi)`.
-/
theorem bd_fr_strict {n' r : ℕ} (F : Frames n' r) (hs : ∀ j : ℤ, ∀ i, i + 1 < r → F.fr j i < F.fr j (i + 1)) (j : ℤ) :
    ∀ d i, i + (d + 1) < r → F.fr j i < F.fr j (i + (d + 1)) := by
  intro d
  induction d with
  | zero => intro i hi; exact hs j i hi
  | succ d ih =>
    intro i hi
    exact lt_trans (ih i (by omega)) (hs j (i + (d + 1)) hi)

/- English proof (translation)
Take `⟨d, rfl⟩ : ∃ d, k = i + (d + 1)` from `⟨k - i - 1, by omega⟩`. Conclude with `bd_fr_strict F hs j d i hk`.
-/
theorem bd_fr_lt {n' r : ℕ} (F : Frames n' r) (hs : ∀ j : ℤ, ∀ i, i + 1 < r → F.fr j i < F.fr j (i + 1)) (j : ℤ)
    {i k : ℕ} (hik : i < k) (hk : k < r) : F.fr j i < F.fr j k := by
  obtain ⟨d, rfl⟩ : ∃ d, k = i + (d + 1) := ⟨k - i - 1, by omega⟩
  exact bd_fr_strict F hs j d i hk

/- English proof (translation)
Establish `hle : ∀ (j : ℤ) (i k : ℕ), i ≤ k → k < r → F.fr j i ≤ F.fr j k`. Introduce `j i k hik hk`. Break down `Nat.lt_or_ge i k with h | h` into its components or cases. Conclude with `(bd_fr_lt F hs j h hk).le`. Establish `: i = k` using `by omega`.

Rewrite using `[this]`. Establish `hcard : (Finset.univ : Finset (Fin r)).card ≤ ((F.letters j).filter fun z => Even z ∧ z < x).card`. Apply `Finset.card_le_card_of_injOn (fun i : Fin r => F.fr (j - 1) i.val)` to reduce the goal to its premises. Introduce `i _`. Unfold `Frames.IsW at hx`.

Establish `h1` using `hle (j - 1) 0 i.val (by omega) i.isLt`. Establish `h2` using `hle (j - 1) i.val (r - 1) (by omega) (by omega)`. Establish `h3` using `hn (j - 1)`. Establish `h4` using `hle j 0 (r - 1) (by omega) (by omega)`. Rewrite `h3` using `[sub_add_cancel]`.

Unfold `Frames.letters`. Simplify using `only [Finset.coe_filter, Finset.mem_filter, Finset.mem_Icc, Set.mem_ofPred_eq]`. Conclude with `⟨⟨⟨h1, by omega⟩, (ht (j - 1) i.val i.isLt).1⟩, (ht (j - 1) i.val i.isLt).2, by omega⟩`. Introduce `a _ b _ hab`. Assume the negation of the conclusion as `hne`.

Break down `Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h` into its components or cases. Conclude with `absurd hab (bd_fr_lt F hs (j - 1) h b.isLt).ne`. Conclude with `absurd hab (bd_fr_lt F hs (j - 1) h a.isLt).ne'`. Rewrite `hcard` using `[Finset.card_univ, Fintype.card_fin]`. Then use the resulting hypothesis.
-/
theorem bd_vectors_before {n' r : ℕ} [NeZero n'] (F : Frames n' r) (hr : 1 ≤ r)
    (hs : ∀ j : ℤ, ∀ i, i + 1 < r → F.fr j i < F.fr j (i + 1))
    (hn : ∀ j : ℤ, F.fr j (r - 1) < F.fr (j + 1) 0)
    (ht : ∀ j : ℤ, ∀ i, i < r → posOf n' (F.fr j i) ∈ F.TT ∧ Even (F.fr j i))
    (j x : ℤ) (hx : ¬ F.IsW j x) : r ≤ ((F.letters j).filter fun z => Even z ∧ z < x).card := by
  have hle : ∀ (j : ℤ) (i k : ℕ), i ≤ k → k < r → F.fr j i ≤ F.fr j k := by
    intro j i k hik hk
    rcases Nat.lt_or_ge i k with h | h
    · exact (bd_fr_lt F hs j h hk).le
    · have : i = k := by omega
      rw [this]
  have hcard : (Finset.univ : Finset (Fin r)).card ≤ ((F.letters j).filter fun z => Even z ∧ z < x).card := by
    apply Finset.card_le_card_of_injOn (fun i : Fin r => F.fr (j - 1) i.val)
    · intro i _
      unfold Frames.IsW at hx
      have h1 := hle (j - 1) 0 i.val (by omega) i.isLt
      have h2 := hle (j - 1) i.val (r - 1) (by omega) (by omega)
      have h3 := hn (j - 1)
      have h4 := hle j 0 (r - 1) (by omega) (by omega)
      rw [sub_add_cancel] at h3
      unfold Frames.letters
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_Icc, Set.mem_ofPred_eq]
      exact ⟨⟨⟨h1, by omega⟩, (ht (j - 1) i.val i.isLt).1⟩, (ht (j - 1) i.val i.isLt).2, by omega⟩
    · intro a _ b _ hab
      by_contra hne
      rcases Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
      · exact absurd hab (bd_fr_lt F hs (j - 1) h b.isLt).ne
      · exact absurd hab (bd_fr_lt F hs (j - 1) h a.isLt).ne'
  rwa [Finset.card_univ, Fintype.card_fin] at hcard

/- English proof (translation)
Introduce `y hy hlt hmax`. Establish `h1` using `h y hy hlt hmax`. Establish `h2 : (L : ℤ) ≤ L'` using `by exact_mod_cast hL`. Use linear arithmetic over natural numbers and integers.
-/
theorem bd_gap_mono {n' r : ℕ} [NeZero n'] (F : Frames n' r) {L L' : ℕ} (hL : L ≤ L') {j x : ℤ}
    (h : F.GapGt L' j x) : F.GapGt L j x := by
  intro y hy hlt hmax
  have h1 := h y hy hlt hmax
  have h2 : (L : ℤ) ≤ L' := by exact_mod_cast hL
  omega

def bd_RestFrames (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (r : ℕ) (h : ℝ), 2 ≤ r → 0 ≤ h →
  ∀ (n' : ℕ) [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de x : ℝ),
    Even n' → 1 ≤ L₁ → 2 * L₁ ≤ L₂ → 0 < de → de ≤ 1 → 3 ≤ x → L₂ < goodU de →
    3 * goodG' r de h x ≤ n' → IsGoodOrbit n' TT L₂ (r - 1) r de h x →
    let u := goodU de
    let G' := goodG' r de h x
    let T := TT.map Fin.valEmbedding
    let ell := (6 * r + 1) * u
    (∃ F : Frames n' r, F.TT = TT ∧
      1 ≤ F.J ∧
      (∀ j : ℤ, ∀ i, F.fr (j + F.J) i = F.fr j i + n') ∧
      (∀ j : ℤ, ∀ i, i + 1 < r → F.fr j i < F.fr j (i + 1)) ∧
      (∀ j : ℤ, F.fr j (r - 1) < F.fr (j + 1) 0) ∧
      (∀ j : ℤ, ∀ i, i < r → posOf n' (F.fr j i) ∈ F.TT ∧ Even (F.fr j i)) ∧
      (∀ j : ℤ, ∀ i, ∀ x : ℤ, i + 1 < r → F.fr j i < x → x < F.fr j (i + 1) → posOf n' x ∉ F.TT) ∧
      (∀ j : ℤ, r ≤ (F.LLset j).card ∧
        ∀ x ∈ F.LLset j, (((F.LLset j).filter (· ≤ x)).card ≤ r ∨
          (F.LLset j).card < ((F.LLset j).filter (· ≤ x)).card + r) → Even x) ∧
      (∀ j : ℤ, ∀ i < r, ∃ s < n' / ell, Formalism.G0.Marked T r u s ∧
        (F.fr j i % (n' : ℤ)).toNat ∈ Formalism.G0.cell r u s (2 * r + 2 + 2 * i)) ∧
      (∀ s < n' / ell, Formalism.G0.Marked T r u s → ∃ j : ℤ, (F.fr j 0 % (n' : ℤ)).toNat ∈ Formalism.G0.cell r u s (2 * r + 2)) ∧
      (∀ j : ℤ, F.fr j (r - 1) - F.fr (j - 1) 0 < G') ∧
      (∀ j : ℤ, ∀ x ∈ F.LLset j, (((F.LLset j).filter (· ≤ x)).card ≤ r ∨
          (F.LLset j).card < ((F.LLset j).filter (· ≤ x)).card + r) → F.GapGt L₂ j x) ∧
      (∀ j : ℤ, F.GapGt L₂ j (F.fr j 0)))

/- English proof (translation)
Introduce `r h hr hh n' _ TT L₁ L₂ de x hn hL1 hL12 hde hde1 hx hLu h3 hg u G' N₁ T ell`. Take `⟨F, hTT, v1, v2, v3, v4, v5, v6, v7, c1, c2, c3, c4, c5⟩` from `hR r h hr hh n' TT L₁ L₂ de x hn hL1 hL12 hde hde1 hx hLu h3 hg`. Substitute `hTT` using the available equality. Establish `hL2n : L₂ ≤ n'` using `by have := bd_U_le_G' r de h x; omega`. Establish `hI` using `fun y => bd_orbit_interval F.TT L₂ (r - 1) r de h x hL2n hg y`.

Establish `hcardL` using `fun j => bd_letters_card F L₂ (r - 1) r de h x (by omega) hg j (c3 j)`. Establish `hLL : L₁ ≤ L₂` using `by omega`. Conclude with `⟨F, rfl, ⟨v1, v2, v3, v4, v5, v6, fun j => ⟨(v7 j).1, fun x hx hc => ⟨(v7 j).2 x hx hc, bd_gap_mono F hLL (c4 j x hx hc)⟩, bd_gap_mono F hLL (c5 j)⟩, hcardL, fun j x _ hw => bd_oldest_far F L₁ L₂ (by omega) (by omega) hI j x (bd_vectors_before F (by omega) v3 v4 v5 j x hw)⟩, c1, …`.
-/
theorem bd_restOrbit_of_frames (D : Formalism.BasicNotions.D7) (hR : bd_RestFrames D) : bd_RestOrbit D := by
  intro r h hr hh n' _ TT L₁ L₂ de x hn hL1 hL12 hde hde1 hx hLu h3 hg u G' N₁ T ell
  obtain ⟨F, hTT, v1, v2, v3, v4, v5, v6, v7, c1, c2, c3, c4, c5⟩ :=
    hR r h hr hh n' TT L₁ L₂ de x hn hL1 hL12 hde hde1 hx hLu h3 hg
  subst hTT
  have hL2n : L₂ ≤ n' := by have := bd_U_le_G' r de h x; omega
  have hI := fun y => bd_orbit_interval F.TT L₂ (r - 1) r de h x hL2n hg y
  have hcardL := fun j => bd_letters_card F L₂ (r - 1) r de h x (by omega) hg j (c3 j)
  have hLL : L₁ ≤ L₂ := by omega
  exact ⟨F, rfl, ⟨v1, v2, v3, v4, v5, v6,
      fun j => ⟨(v7 j).1, fun x hx hc => ⟨(v7 j).2 x hx hc, bd_gap_mono F hLL (c4 j x hx hc)⟩,
        bd_gap_mono F hLL (c5 j)⟩,
      hcardL,
      fun j x _ hw => bd_oldest_far F L₁ L₂ (by omega) (by omega) hI j x
        (bd_vectors_before F (by omega) v3 v4 v5 j x hw)⟩,
    c1, c2, fun j => ⟨(c3 j).le, hcardL j⟩, c4, c5⟩

/- English proof (translation)
The claim follows from `good_orbits_of_frames D (bd_restOrbit_of_frames D hR)`.
-/
theorem orbit_lemma_of_frame_construction (D : Formalism.BasicNotions.D7) (hR : bd_RestFrames D) : GoodOrbitPositions D :=
  good_orbits_of_frames D (bd_restOrbit_of_frames D hR)

end Formalism.MainNotions.G.WittFrameLocaliserOrders

end

noncomputable section

open Finset Classical

namespace Formalism.MainNotions.G.WittFrameLocaliserOrders

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning

section Tiles

variable {n' : ℕ} [NeZero n'] (TT : Finset (Fin n')) (r u : ℕ)

def bf_MT (b : ℤ) : Prop :=
  ∀ c : ℕ, 1 ≤ c → c ≤ 6 * r + 1 →
    (Odd c → ∀ y : ℤ, b + (c : ℤ) * u - u ≤ y → y < b + (c : ℤ) * u → posOf n' y ∉ TT) ∧
    (Even c → ∃ x : ℤ, (b + (c : ℤ) * u - u ≤ x ∧ x < b + (c : ℤ) * u ∧ posOf n' x ∈ TT ∧ Even x) ∧
      ∀ y : ℤ, b + (c : ℤ) * u - u ≤ y → y < b + (c : ℤ) * u → posOf n' y ∈ TT → y = x)

def bf_tp (b : ℤ) (c : ℕ) : ℤ :=
  if h : ∃ x : ℤ, (b + (c : ℤ) * u - u ≤ x ∧ x < b + (c : ℤ) * u ∧ posOf n' x ∈ TT ∧ Even x) ∧
      ∀ y : ℤ, b + (c : ℤ) * u - u ≤ y → y < b + (c : ℤ) * u → posOf n' y ∈ TT → y = x
  then Classical.choose h else 0

/- English proof (translation)
Establish `hx` using `(h c h1 h2).2 he`. Unfold `bf_tp`. Rewrite using `[dif_pos hx]`. Conclude with `Classical.choose_spec hx`.
-/
theorem bf_tp_spec {b : ℤ} (h : bf_MT TT r u b) {c : ℕ} (h1 : 1 ≤ c) (h2 : c ≤ 6 * r + 1) (he : Even c) :
    (b + (c : ℤ) * u - u ≤ bf_tp TT u b c ∧ bf_tp TT u b c < b + (c : ℤ) * u ∧ posOf n' (bf_tp TT u b c) ∈ TT ∧
      Even (bf_tp TT u b c)) ∧
      ∀ y : ℤ, b + (c : ℤ) * u - u ≤ y → y < b + (c : ℤ) * u → posOf n' y ∈ TT → y = bf_tp TT u b c := by
  have hx := (h c h1 h2).2 he
  unfold bf_tp
  rw [dif_pos hx]
  exact Classical.choose_spec hx

/- English proof (translation)
The claim follows from `mul_le_mul_of_nonneg_right (by exact_mod_cast h) (by positivity)`.
-/
theorem bf_cu {c c' : ℕ} (h : c ≤ c') (u : ℕ) : (c : ℤ) * u ≤ (c' : ℤ) * u :=
  mul_le_mul_of_nonneg_right (by exact_mod_cast h) (by positivity)

/- English proof (translation)
Use `bf_cu h u` as an intermediate fact. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem mul_add_le_of_succ_le {c c' : ℕ} (h : c + 1 ≤ c') (u : ℕ) : (c : ℤ) * u + u ≤ (c' : ℤ) * u := by
  have := bf_cu h u
  push_cast at this
  linarith

/- English proof (translation)
Establish `a` using `(bf_tp_spec TT r u h h1 (by omega) he).1.2.1`. Establish `a'` using `(bf_tp_spec TT r u h (by omega) h2 he').1.1`. Use `mul_add_le_of_succ_le (show c + 1 ≤ c' from hlt) u` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bf_tp_lt {b : ℤ} (h : bf_MT TT r u b) {c c' : ℕ} (h1 : 1 ≤ c) (h2 : c' ≤ 6 * r + 1) (he : Even c)
    (he' : Even c') (hlt : c < c') : bf_tp TT u b c < bf_tp TT u b c' := by
  have a := (bf_tp_spec TT r u h h1 (by omega) he).1.2.1
  have a' := (bf_tp_spec TT r u h (by omega) h2 he').1.1
  have := mul_add_le_of_succ_le (show c + 1 ≤ c' from hlt) u
  linarith

/- English proof (translation)
Establish `hU : (0 : ℤ) < u` using `by exact_mod_cast hu`. Establish `hd0 : 0 ≤ (y - b) / (u : ℤ)` using `Int.ediv_nonneg (by linarith) hU.le`. Establish `hd1 : (y - b) / (u : ℤ) * u ≤ y - b` using `Int.ediv_mul_le _ hU.ne'`. Establish `hd2 : y - b < ((y - b) / (u : ℤ) + 1) * u` using `Int.lt_ediv_add_one_mul_self _ hU`. Take `⟨c0, hc0⟩` from `Int.eq_ofNat_of_zero_le hd0`.

Rewrite `hd1`, `hd2` using `[hc0]`. Establish `hcast : ((c0 + 1 : ℕ) : ℤ) * u = (c0 : ℤ) * u + u` using `by push_cast; ring`. Establish `hle : c0 + 1 ≤ 6 * r + 1`. Assume the negation of the conclusion as `hcon`. Use `bf_cu (show 6 * r + 1 ≤ c0 by omega) u` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `lo : b + ((c0 + 1 : ℕ) : ℤ) * u - u ≤ y` using `by rw [hcast]; linarith`. Establish `hi : y < b + ((c0 + 1 : ℕ) : ℤ) * u` using `by rw [hcast]; linarith`. Break down `Nat.even_or_odd (c0 + 1) with he | ho` into its components or cases. Conclude with `⟨c0 + 1, he, by omega, hle, (bf_tp_spec TT r u h (by omega) hle he).2 y lo hi hy⟩`.

Conclude with `absurd hy ((h (c0 + 1) (by omega) hle).1 ho y lo hi)`.
-/
theorem bf_class {b : ℤ} (h : bf_MT TT r u b) (hu : 1 ≤ u) {y : ℤ} (hy : posOf n' y ∈ TT) (h1 : b ≤ y)
    (h2 : y < b + ((6 * r + 1 : ℕ) : ℤ) * u) :
    ∃ c, Even c ∧ 1 ≤ c ∧ c ≤ 6 * r + 1 ∧ y = bf_tp TT u b c := by
  have hU : (0 : ℤ) < u := by exact_mod_cast hu
  have hd0 : 0 ≤ (y - b) / (u : ℤ) := Int.ediv_nonneg (by linarith) hU.le
  have hd1 : (y - b) / (u : ℤ) * u ≤ y - b := Int.ediv_mul_le _ hU.ne'
  have hd2 : y - b < ((y - b) / (u : ℤ) + 1) * u := Int.lt_ediv_add_one_mul_self _ hU
  obtain ⟨c0, hc0⟩ := Int.eq_ofNat_of_zero_le hd0
  rw [hc0] at hd1 hd2
  have hcast : ((c0 + 1 : ℕ) : ℤ) * u = (c0 : ℤ) * u + u := by push_cast; ring
  have hle : c0 + 1 ≤ 6 * r + 1 := by
    by_contra hcon
    have := bf_cu (show 6 * r + 1 ≤ c0 by omega) u
    linarith
  have lo : b + ((c0 + 1 : ℕ) : ℤ) * u - u ≤ y := by rw [hcast]; linarith
  have hi : y < b + ((c0 + 1 : ℕ) : ℤ) * u := by rw [hcast]; linarith
  rcases Nat.even_or_odd (c0 + 1) with he | ho
  · exact ⟨c0 + 1, he, by omega, hle, (bf_tp_spec TT r u h (by omega) hle he).2 y lo hi hy⟩
  · exact absurd hy ((h (c0 + 1) (by omega) hle).1 ho y lo hi)

/- English proof (translation)
Take `⟨c0, rfl⟩ : ∃ c0, c = c0 + 1` from `⟨c - 1, by omega⟩`. Take `⟨⟨lo, hi, _, _⟩, uniq⟩` from `bf_tp_spec TT r u h h1 h2 he`. Assume the negation of the conclusion as `hcon`. Establish `hcon' : bf_tp TT u b (c0 + 1) ≤ y + u` using `not_lt.1 hcon`. Establish `ho : Odd c0` using `Nat.not_even_iff_odd.1 (Nat.even_add_one.1 he)`.

Establish `hc0 : 1 ≤ c0` using `ho.pos`. Establish `hcast : ((c0 + 1 : ℕ) : ℤ) * u = (c0 : ℤ) * u + u` using `by push_cast; ring`. Rewrite `lo`, `hi` using `[hcast]`. Distinguish the cases in `hy2 : y < b + (c0 : ℤ) * u`. Conclude with `(h c0 hc0 (by omega)).1 ho y (by linarith) hy2 hy`.

Use `uniq y (by rw [hcast]; linarith) (by rw [hcast]; linarith) hy` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bf_gap {b : ℤ} (h : bf_MT TT r u b) {c : ℕ} (h1 : 1 ≤ c) (h2 : c ≤ 6 * r + 1) (he : Even c) {y : ℤ}
    (hy : posOf n' y ∈ TT) (hlt : y < bf_tp TT u b c) : y + u < bf_tp TT u b c := by
  obtain ⟨c0, rfl⟩ : ∃ c0, c = c0 + 1 := ⟨c - 1, by omega⟩
  obtain ⟨⟨lo, hi, _, _⟩, uniq⟩ := bf_tp_spec TT r u h h1 h2 he
  by_contra hcon
  have hcon' : bf_tp TT u b (c0 + 1) ≤ y + u := not_lt.1 hcon
  have ho : Odd c0 := Nat.not_even_iff_odd.1 (Nat.even_add_one.1 he)
  have hc0 : 1 ≤ c0 := ho.pos
  have hcast : ((c0 + 1 : ℕ) : ℤ) * u = (c0 : ℤ) * u + u := by push_cast; ring
  rw [hcast] at lo hi
  by_cases hy2 : y < b + (c0 : ℤ) * u
  · exact (h c0 hc0 (by omega)).1 ho y (by linarith) hy2 hy
  · have := uniq y (by rw [hcast]; linarith) (by rw [hcast]; linarith) hy
    linarith

/- English proof (translation)
Rewrite using `[card_image_of_injOn, card_range]`. Introduce `k hk k' hk' hkk`. Establish `hk1` using `mem_range.1 (mem_coe.1 hk)`. Establish `hk2` using `mem_range.1 (mem_coe.1 hk')`. Establish `hkk' : bf_tp TT u b (c0 + 2 * k) = bf_tp TT u b (c0 + 2 * k')` using `hkk`.

Assume the negation of the conclusion as `hne`. Break down `lt_or_gt_of_ne hne with hl | hl` into its components or cases. Use `bf_tp_lt TT r u h (c := c0 + 2 * k) (c' := c0 + 2 * k') (by omega) (hm k' hk2) (he.add (even_two_mul k)) (he.add (even_two_mul k')) (by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `bf_tp_lt TT r u h (c := c0 + 2 * k') (c' := c0 + 2 * k) (by omega) (hm k hk1) (he.add (even_two_mul k')) (he.add (even_two_mul k)) (by omega)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem bf_card_image {b : ℤ} (h : bf_MT TT r u b) (c0 m : ℕ) (he : Even c0) (h1 : 1 ≤ c0)
    (hm : ∀ k < m, c0 + 2 * k ≤ 6 * r + 1) :
    ((range m).image fun k => bf_tp TT u b (c0 + 2 * k)).card = m := by
  rw [card_image_of_injOn, card_range]
  intro k hk k' hk' hkk
  have hk1 := mem_range.1 (mem_coe.1 hk)
  have hk2 := mem_range.1 (mem_coe.1 hk')
  have hkk' : bf_tp TT u b (c0 + 2 * k) = bf_tp TT u b (c0 + 2 * k') := hkk
  by_contra hne
  rcases lt_or_gt_of_ne hne with hl | hl
  · have := bf_tp_lt TT r u h (c := c0 + 2 * k) (c' := c0 + 2 * k') (by omega) (hm k' hk2)
      (he.add (even_two_mul k)) (he.add (even_two_mul k')) (by omega)
    omega
  · have := bf_tp_lt TT r u h (c := c0 + 2 * k') (c' := c0 + 2 * k) (by omega) (hm k hk1)
      (he.add (even_two_mul k')) (he.add (even_two_mul k)) (by omega)
    omega

end Tiles

section Fr

variable {n' : ℕ} [NeZero n'] (TT : Finset (Fin n')) (r u : ℕ)

/- English proof (translation)
Use `bf_cu h u` as an intermediate fact. Simplify using `using this`.
-/
theorem bf_u_le {c : ℕ} (h : 1 ≤ c) (u : ℕ) : (u : ℤ) ≤ (c : ℤ) * u := by
  have := bf_cu h u
  simpa using this

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Establish `h1` using `posOf_val n' (y + n')`. Establish `h2` using `posOf_val n' y`. Rewrite `h1` using `[Int.add_emod_right]`. Establish `: ((posOf n' (y + n')).val : ℤ) = ((posOf n' y).val : ℤ)` using `by rw [h1, h2]`.

Conclude with `this` after adjusting the coercions.
-/
theorem bf_posOf_add (y : ℤ) : posOf n' (y + n') = posOf n' y := by
  apply Fin.ext
  have h1 := posOf_val n' (y + n')
  have h2 := posOf_val n' y
  rw [Int.add_emod_right] at h1
  have : ((posOf n' (y + n')).val : ℤ) = ((posOf n' y).val : ℤ) := by rw [h1, h2]
  exact_mod_cast this

/- English proof (translation)
Take `⟨⟨lo, hi, ht, _⟩, _⟩` from `bf_tp_spec TT r u h h1 h2 he`. Conclude with `((bf_tp_spec TT r u h' h1 h2 he).2 (bf_tp TT u b c + n') (by linarith) (by linarith) (by rw [bf_posOf_add]; exact ht)).symm`.
-/
theorem bf_tp_shift {b : ℤ} (h : bf_MT TT r u b) (h' : bf_MT TT r u (b + n')) {c : ℕ} (h1 : 1 ≤ c)
    (h2 : c ≤ 6 * r + 1) (he : Even c) : bf_tp TT u (b + n') c = bf_tp TT u b c + n' := by
  obtain ⟨⟨lo, hi, ht, _⟩, _⟩ := bf_tp_spec TT r u h h1 h2 he
  exact ((bf_tp_spec TT r u h' h1 h2 he).2 (bf_tp TT u b c + n') (by linarith) (by linarith)
    (by rw [bf_posOf_add]; exact ht)).symm

def bf_F (J : ℕ) (B : ℤ → ℤ) : Frames n' r :=
  ⟨TT, J, fun j i => if i < r then bf_tp TT u (B j) (2 * r + 2 + 2 * i) else B j⟩

/- English proof (translation)
The claim follows from `if_pos hi`.
-/
theorem bf_F_fr (J : ℕ) (B : ℤ → ℤ) (j : ℤ) {i : ℕ} (hi : i < r) :
    (bf_F TT r u J B).fr j i = bf_tp TT u (B j) (2 * r + 2 + 2 * i) := if_pos hi

variable {TT r u} {J : ℕ} {B : ℤ → ℤ} (hr : 2 ≤ r) (hu : 1 ≤ u) (hMT : ∀ j, bf_MT TT r u (B j))
  (hstep : ∀ j, B j + ((6 * r + 1 : ℕ) : ℤ) * u ≤ B (j + 1))

include hr in
/- English proof (translation)
Unfold `Frames.LLset`. Rewrite using `[mem_filter, mem_Ioo, bf_F_fr TT r u J B (j - 1) (show r - 1 < r by omega), bf_F_fr TT r u J B j (show 0 < r by omega), show 2 * r + 2 + 2 * (r - 1) = 4 * r by omega, show 2 * r + 2 + 2 * 0 = 2 * r + 2 by omega]`. Conclude with `Iff.rfl`.
-/
theorem bf_LL_mem (j x : ℤ) : x ∈ (bf_F TT r u J B).LLset j ↔
    (bf_tp TT u (B (j - 1)) (4 * r) < x ∧ x < bf_tp TT u (B j) (2 * r + 2)) ∧ posOf n' x ∈ TT := by
  unfold Frames.LLset
  rw [mem_filter, mem_Ioo, bf_F_fr TT r u J B (j - 1) (show r - 1 < r by omega),
    bf_F_fr TT r u J B j (show 0 < r by omega), show 2 * r + 2 + 2 * (r - 1) = 4 * r by omega,
    show 2 * r + 2 + 2 * 0 = 2 * r + 2 by omega]
  exact Iff.rfl

include hr hMT hstep in
/- English proof (translation)
Rewrite using `[bf_LL_mem hr]`. Establish `hs` using `hstep (j - 1)`. Rewrite `hs` using `[sub_add_cancel]`. Establish `A` using `bf_tp_spec TT r u (hMT (j - 1)) (c := 4 * r + 2 + 2 * k) (by omega) (by omega) ⟨2 * r + 1 + k, by ring⟩`. Establish `Bq` using `bf_tp_spec TT r u (hMT j) (c := 2 * r + 2) (by omega) (by omega) ⟨r + 1, by ring⟩`.

Use `⟨⟨bf_tp_lt TT r u (hMT (j - 1)) (by omega) (by omega) ⟨2 * r, by ring⟩ ⟨2 * r + 1 + k, by ring⟩ (by omega), ?_⟩, A.1.2.2.1⟩` and prove the remaining obligations. Establish `h1` using `bf_cu (show 4 * r + 2 + 2 * k ≤ 6 * r + 1 by omega) u`. Establish `h2` using `bf_u_le (show 1 ≤ 2 * r + 2 by omega) u`. Combine the linear relations using `[A.1.2.1, Bq.1.1]`.
-/
theorem bf_LL_first (j : ℤ) {k : ℕ} (hk : k < r) :
    bf_tp TT u (B (j - 1)) (4 * r + 2 + 2 * k) ∈ (bf_F TT r u J B).LLset j := by
  rw [bf_LL_mem hr]
  have hs := hstep (j - 1)
  rw [sub_add_cancel] at hs
  have A := bf_tp_spec TT r u (hMT (j - 1)) (c := 4 * r + 2 + 2 * k) (by omega) (by omega) ⟨2 * r + 1 + k, by ring⟩
  have Bq := bf_tp_spec TT r u (hMT j) (c := 2 * r + 2) (by omega) (by omega) ⟨r + 1, by ring⟩
  refine ⟨⟨bf_tp_lt TT r u (hMT (j - 1)) (by omega) (by omega) ⟨2 * r, by ring⟩ ⟨2 * r + 1 + k, by ring⟩ (by omega),
    ?_⟩, A.1.2.2.1⟩
  have h1 := bf_cu (show 4 * r + 2 + 2 * k ≤ 6 * r + 1 by omega) u
  have h2 := bf_u_le (show 1 ≤ 2 * r + 2 by omega) u
  linarith [A.1.2.1, Bq.1.1]

include hr hMT hstep in
/- English proof (translation)
Rewrite using `[bf_LL_mem hr]`. Establish `hs` using `hstep (j - 1)`. Rewrite `hs` using `[sub_add_cancel]`. Establish `A` using `bf_tp_spec TT r u (hMT (j - 1)) (c := 4 * r) (by omega) (by omega) ⟨2 * r, by ring⟩`. Establish `Bq` using `bf_tp_spec TT r u (hMT j) (c := 2 + 2 * k) (by omega) (by omega) ⟨1 + k, by ring⟩`.

Use `⟨⟨?_, bf_tp_lt TT r u (hMT j) (by omega) (by omega) ⟨1 + k, by ring⟩ ⟨r + 1, by ring⟩ (by omega)⟩, Bq.1.2.2.1⟩` and prove the remaining obligations. Establish `h1` using `bf_cu (show 4 * r ≤ 6 * r + 1 by omega) u`. Establish `h2` using `bf_u_le (show 1 ≤ 2 + 2 * k by omega) u`. Combine the linear relations using `[A.1.2.1, Bq.1.1]`.
-/
theorem bf_LL_last (j : ℤ) {k : ℕ} (hk : k < r) :
    bf_tp TT u (B j) (2 + 2 * k) ∈ (bf_F TT r u J B).LLset j := by
  rw [bf_LL_mem hr]
  have hs := hstep (j - 1)
  rw [sub_add_cancel] at hs
  have A := bf_tp_spec TT r u (hMT (j - 1)) (c := 4 * r) (by omega) (by omega) ⟨2 * r, by ring⟩
  have Bq := bf_tp_spec TT r u (hMT j) (c := 2 + 2 * k) (by omega) (by omega) ⟨1 + k, by ring⟩
  refine ⟨⟨?_, bf_tp_lt TT r u (hMT j) (by omega) (by omega) ⟨1 + k, by ring⟩ ⟨r + 1, by ring⟩ (by omega)⟩,
    Bq.1.2.2.1⟩
  have h1 := bf_cu (show 4 * r ≤ 6 * r + 1 by omega) u
  have h2 := bf_u_le (show 1 ≤ 2 + 2 * k by omega) u
  linarith [A.1.2.1, Bq.1.1]

include hr hu hMT hstep in

/- English proof (translation)
Establish `hx'` using `(bf_LL_mem hr j x).1 hx`. Establish `hs` using `hstep (j - 1)`. Rewrite `hs` using `[sub_add_cancel]`. Break down `hc with hc | hc` into its components or cases. Establish `hlt : x < B (j - 1) + ((6 * r + 1 : ℕ) : ℤ) * u`.

Assume the negation of the conclusion as `hcon`. Establish `hcon'` using `not_lt.1 hcon`. Establish `hS1` using `bf_card_image TT r u (hMT (j - 1)) (4 * r + 2) r ⟨2 * r + 1, by ring⟩ (by omega) (fun k hk => by omega)`. Establish `hlt1 : ∀ y ∈ (range r).image (fun k => bf_tp TT u (B (j - 1)) (4 * r + 2 + 2 * k)), y < x`. Introduce `y hy`.

Take `⟨k, hk, rfl⟩` from `mem_image.1 hy`. Establish `hk'` using `mem_range.1 hk`. Establish `A` using `bf_tp_spec TT r u (hMT (j - 1)) (c := 4 * r + 2 + 2 * k) (by omega) (by omega) ⟨2 * r + 1 + k, by ring⟩`. Establish `h1` using `bf_cu (show 4 * r + 2 + 2 * k ≤ 6 * r + 1 by omega) u`. Combine the linear relations using `[A.1.2.1]`.

Establish `hsub : insert x ((range r).image (fun k => bf_tp TT u (B (j - 1)) (4 * r + 2 + 2 * k))) ⊆ ((bf_F TT r u J B).LLset j).filter (· ≤ x)`. Introduce `y hy`. Break down `mem_insert.1 hy with h | h` into its components or cases. Rewrite using `[h]`. Conclude with `mem_filter.2 ⟨hx, le_rfl⟩`.

Establish `hl` using `hlt1 y h`. Take `⟨k, hk, rfl⟩` from `mem_image.1 h`. Conclude with `mem_filter.2 ⟨bf_LL_first hr hMT hstep j (mem_range.1 hk), le_of_lt hl⟩`. Establish `hnot : x ∉ (range r).image (fun k => bf_tp TT u (B (j - 1)) (4 * r + 2 + 2 * k))` using `fun h => lt_irrefl _ (hlt1 x h)`. Use `card_le_card hsub` as an intermediate fact.

Rewrite `this` using `[card_insert_of_notMem hnot, hS1]`. Use linear arithmetic over natural numbers and integers. Establish `A` using `bf_tp_spec TT r u (hMT (j - 1)) (c := 4 * r) (by omega) (by omega) ⟨2 * r, by ring⟩`. Establish `h2` using `bf_u_le (show 1 ≤ 4 * r by omega) u`. Take `⟨c, h1, h2, h3, h4⟩` from `bf_class TT r u (hMT (j - 1)) hu hx'.2 (by linarith [A.1.1, hx'.1.1]) hlt`.

Conclude with `⟨B (j - 1), c, hMT _, h1, h2, h3, h4⟩`. Establish `hge : B j ≤ x`. Assume the negation of the conclusion as `hcon`. Establish `hcon'` using `not_le.1 hcon`. Establish `hS2` using `bf_card_image TT r u (hMT j) 2 r ⟨1, by ring⟩ (by omega) (fun k hk => by omega)`.

Establish `hgt : ∀ y ∈ (range r).image (fun k => bf_tp TT u (B j) (2 + 2 * k)), x < y`. Introduce `y hy`. Take `⟨k, hk, rfl⟩` from `mem_image.1 hy`. Establish `hk'` using `mem_range.1 hk`. Establish `A` using `bf_tp_spec TT r u (hMT j) (c := 2 + 2 * k) (by omega) (by omega) ⟨1 + k, by ring⟩`.

Establish `h1` using `bf_u_le (show 1 ≤ 2 + 2 * k by omega) u`. Combine the linear relations using `[A.1.1]`. Establish `hsub : (range r).image (fun k => bf_tp TT u (B j) (2 + 2 * k)) ∪ ((bf_F TT r u J B).LLset j).filter (· ≤ x) ⊆ (bf_F TT r u J B).LLset j`. Introduce `y hy`. Break down `mem_union.1 hy with h | h` into its components or cases.

Take `⟨k, hk, rfl⟩` from `mem_image.1 h`. Conclude with `bf_LL_last hr hMT hstep j (mem_range.1 hk)`. Conclude with `(mem_filter.1 h).1`. Establish `hdis : Disjoint ((range r).image (fun k => bf_tp TT u (B j) (2 + 2 * k))) (((bf_F TT r u J B).LLset j).filter (· ≤ x))`. Rewrite using `[disjoint_left]`.

Introduce `y hy hy2`. Use `hgt y hy` as an intermediate fact. Use `(mem_filter.1 hy2).2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `card_le_card hsub` as an intermediate fact.

Rewrite `this` using `[card_union_of_disjoint hdis, hS2]`. Use linear arithmetic over natural numbers and integers. Establish `Bq` using `bf_tp_spec TT r u (hMT j) (c := 2 * r + 2) (by omega) (by omega) ⟨r + 1, by ring⟩`. Establish `h1` using `bf_cu (show 2 * r + 2 ≤ 6 * r + 1 by omega) u`. Take `⟨c, h1, h2, h3, h4⟩` from `bf_class TT r u (hMT j) hu hx'.2 hge (by linarith [Bq.1.2.1, hx'.1.2])`.

Conclude with `⟨B j, c, hMT _, h1, h2, h3, h4⟩`.
-/
theorem bf_LL_key (j x : ℤ) (hx : x ∈ (bf_F TT r u J B).LLset j)
    (hc : (((bf_F TT r u J B).LLset j).filter (· ≤ x)).card ≤ r ∨
      ((bf_F TT r u J B).LLset j).card < (((bf_F TT r u J B).LLset j).filter (· ≤ x)).card + r) :
    ∃ (b : ℤ) (c : ℕ), bf_MT TT r u b ∧ Even c ∧ 1 ≤ c ∧ c ≤ 6 * r + 1 ∧ x = bf_tp TT u b c := by
  have hx' := (bf_LL_mem hr j x).1 hx
  have hs := hstep (j - 1)
  rw [sub_add_cancel] at hs
  rcases hc with hc | hc
  · have hlt : x < B (j - 1) + ((6 * r + 1 : ℕ) : ℤ) * u := by
      by_contra hcon
      have hcon' := not_lt.1 hcon
      have hS1 := bf_card_image TT r u (hMT (j - 1)) (4 * r + 2) r ⟨2 * r + 1, by ring⟩ (by omega)
        (fun k hk => by omega)
      have hlt1 : ∀ y ∈ (range r).image (fun k => bf_tp TT u (B (j - 1)) (4 * r + 2 + 2 * k)), y < x := by
        intro y hy
        obtain ⟨k, hk, rfl⟩ := mem_image.1 hy
        have hk' := mem_range.1 hk
        have A := bf_tp_spec TT r u (hMT (j - 1)) (c := 4 * r + 2 + 2 * k) (by omega) (by omega)
          ⟨2 * r + 1 + k, by ring⟩
        have h1 := bf_cu (show 4 * r + 2 + 2 * k ≤ 6 * r + 1 by omega) u
        linarith [A.1.2.1]
      have hsub : insert x ((range r).image (fun k => bf_tp TT u (B (j - 1)) (4 * r + 2 + 2 * k))) ⊆
          ((bf_F TT r u J B).LLset j).filter (· ≤ x) := by
        intro y hy
        rcases mem_insert.1 hy with h | h
        · rw [h]; exact mem_filter.2 ⟨hx, le_rfl⟩
        · have hl := hlt1 y h
          obtain ⟨k, hk, rfl⟩ := mem_image.1 h
          exact mem_filter.2 ⟨bf_LL_first hr hMT hstep j (mem_range.1 hk), le_of_lt hl⟩
      have hnot : x ∉ (range r).image (fun k => bf_tp TT u (B (j - 1)) (4 * r + 2 + 2 * k)) :=
        fun h => lt_irrefl _ (hlt1 x h)
      have := card_le_card hsub
      rw [card_insert_of_notMem hnot, hS1] at this
      omega
    have A := bf_tp_spec TT r u (hMT (j - 1)) (c := 4 * r) (by omega) (by omega) ⟨2 * r, by ring⟩
    have h2 := bf_u_le (show 1 ≤ 4 * r by omega) u
    obtain ⟨c, h1, h2, h3, h4⟩ := bf_class TT r u (hMT (j - 1)) hu hx'.2 (by linarith [A.1.1, hx'.1.1]) hlt
    exact ⟨B (j - 1), c, hMT _, h1, h2, h3, h4⟩
  · have hge : B j ≤ x := by
      by_contra hcon
      have hcon' := not_le.1 hcon
      have hS2 := bf_card_image TT r u (hMT j) 2 r ⟨1, by ring⟩ (by omega) (fun k hk => by omega)
      have hgt : ∀ y ∈ (range r).image (fun k => bf_tp TT u (B j) (2 + 2 * k)), x < y := by
        intro y hy
        obtain ⟨k, hk, rfl⟩ := mem_image.1 hy
        have hk' := mem_range.1 hk
        have A := bf_tp_spec TT r u (hMT j) (c := 2 + 2 * k) (by omega) (by omega) ⟨1 + k, by ring⟩
        have h1 := bf_u_le (show 1 ≤ 2 + 2 * k by omega) u
        linarith [A.1.1]
      have hsub : (range r).image (fun k => bf_tp TT u (B j) (2 + 2 * k)) ∪
          ((bf_F TT r u J B).LLset j).filter (· ≤ x) ⊆ (bf_F TT r u J B).LLset j := by
        intro y hy
        rcases mem_union.1 hy with h | h
        · obtain ⟨k, hk, rfl⟩ := mem_image.1 h
          exact bf_LL_last hr hMT hstep j (mem_range.1 hk)
        · exact (mem_filter.1 h).1
      have hdis : Disjoint ((range r).image (fun k => bf_tp TT u (B j) (2 + 2 * k)))
          (((bf_F TT r u J B).LLset j).filter (· ≤ x)) := by
        rw [disjoint_left]
        intro y hy hy2
        have := hgt y hy
        have := (mem_filter.1 hy2).2
        omega
      have := card_le_card hsub
      rw [card_union_of_disjoint hdis, hS2] at this
      omega
    have Bq := bf_tp_spec TT r u (hMT j) (c := 2 * r + 2) (by omega) (by omega) ⟨r + 1, by ring⟩
    have h1 := bf_cu (show 2 * r + 2 ≤ 6 * r + 1 by omega) u
    obtain ⟨c, h1, h2, h3, h4⟩ := bf_class TT r u (hMT j) hu hx'.2 hge (by linarith [Bq.1.2.1, hx'.1.2])
    exact ⟨B j, c, hMT _, h1, h2, h3, h4⟩

/- English proof (translation)
Introduce `y hy hlt _`. Establish `hy' : posOf n' y ∈ TT` using `(mem_filter.1 hy).2`. Use `bf_gap TT r u h h1 h2 he hy' hlt` as an intermediate fact. Establish `hL' : (L₂ : ℤ) < u` using `by exact_mod_cast hL`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bf_gapGt {L₂ : ℕ} (hL : L₂ < u) (j : ℤ) {b : ℤ} (h : bf_MT TT r u b) {c : ℕ} (h1 : 1 ≤ c)
    (h2 : c ≤ 6 * r + 1) (he : Even c) : (bf_F TT r u J B).GapGt L₂ j (bf_tp TT u b c) := by
  intro y hy hlt _
  have hy' : posOf n' y ∈ TT := (mem_filter.1 hy).2
  have := bf_gap TT r u h h1 h2 he hy' hlt
  have hL' : (L₂ : ℤ) < u := by exact_mod_cast hL
  linarith

/- English proof (translation)
Take `⟨c0, rfl⟩ : ∃ c0, c = c0 + 1` from `⟨c - 1, by omega⟩`. Take `⟨⟨lo, hi, _, _⟩, _⟩` from `bf_tp_spec TT r u h h1 h2 he`. Establish `hsn : (s + 1) * ((6 * r + 1) * u) ≤ n'` using `le_trans (Nat.mul_le_mul_right _ hs) (Nat.div_mul_le_self _ _)`. Establish `hsn' : (s : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u) + ((6 * r + 1 : ℕ) : ℤ) * u ≤ n'`. Use `(Nat.cast_le (α := ℤ)).2 hsn` as an intermediate fact.

Move the coercions through the operations in `at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcu` using `bf_cu h2 u`. Establish `hcast : ((c0 + 1 : ℕ) : ℤ) * u = (c0 : ℤ) * u + u` using `by push_cast; ring`. Establish `hs0 : (0 : ℤ) ≤ (s : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u)` using `by positivity`.

Establish `hc0 : (0 : ℤ) ≤ (c0 : ℤ) * u` using `by positivity`. Establish `hz0 : 0 ≤ bf_tp TT u b (c0 + 1) - (n' : ℤ) * q` using `by rw [hcast] at lo; linarith`. Establish `hz1 : bf_tp TT u b (c0 + 1) - (n' : ℤ) * q < n'` using `by linarith`. Establish `hmod : bf_tp TT u b (c0 + 1) % (n' : ℤ) = bf_tp TT u b (c0 + 1) - (n' : ℤ) * q`. Establish `h3 : bf_tp TT u b (c0 + 1) = (bf_tp TT u b (c0 + 1) - (n' : ℤ) * q) + (n' : ℤ) * q` using `by ring`.

Use `conv_lhs => rw [h3]`. Rewrite using `[Int.add_mul_emod_self_left]`. Conclude with `Int.emod_eq_of_lt hz0 hz1`. Rewrite using `[hmod]`. Unfold `Formalism.G0.cell`.

Rewrite using `[mem_Ico, Nat.add_sub_cancel, Int.le_toNat hz0, Int.toNat_lt hz0]`. Prove the components needed by the constructor for the conclusion. Use `push_cast`. Rewrite `lo` using `[hcast]`. Move the coercions through the operations in `at lo hb`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `push_cast`. Move the coercions through the operations in `at hi hb`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bf_cell {b : ℤ} (h : bf_MT TT r u b) (s : ℕ) (q : ℤ)
    (hb : b = (n' : ℤ) * q + (s : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u)) (hs : s < n' / ((6 * r + 1) * u)) {c : ℕ}
    (h1 : 1 ≤ c) (h2 : c ≤ 6 * r + 1) (he : Even c) :
    (bf_tp TT u b c % (n' : ℤ)).toNat ∈ Formalism.G0.cell r u s c := by
  obtain ⟨c0, rfl⟩ : ∃ c0, c = c0 + 1 := ⟨c - 1, by omega⟩
  obtain ⟨⟨lo, hi, _, _⟩, _⟩ := bf_tp_spec TT r u h h1 h2 he
  have hsn : (s + 1) * ((6 * r + 1) * u) ≤ n' :=
    le_trans (Nat.mul_le_mul_right _ hs) (Nat.div_mul_le_self _ _)
  have hsn' : (s : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u) + ((6 * r + 1 : ℕ) : ℤ) * u ≤ n' := by
    have := (Nat.cast_le (α := ℤ)).2 hsn
    push_cast at this ⊢
    linarith
  have hcu := bf_cu h2 u
  have hcast : ((c0 + 1 : ℕ) : ℤ) * u = (c0 : ℤ) * u + u := by push_cast; ring
  have hs0 : (0 : ℤ) ≤ (s : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u) := by positivity
  have hc0 : (0 : ℤ) ≤ (c0 : ℤ) * u := by positivity
  have hz0 : 0 ≤ bf_tp TT u b (c0 + 1) - (n' : ℤ) * q := by rw [hcast] at lo; linarith
  have hz1 : bf_tp TT u b (c0 + 1) - (n' : ℤ) * q < n' := by linarith
  have hmod : bf_tp TT u b (c0 + 1) % (n' : ℤ) = bf_tp TT u b (c0 + 1) - (n' : ℤ) * q := by
    have h3 : bf_tp TT u b (c0 + 1) = (bf_tp TT u b (c0 + 1) - (n' : ℤ) * q) + (n' : ℤ) * q := by ring
    conv_lhs => rw [h3]
    rw [Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt hz0 hz1
  rw [hmod]
  unfold Formalism.G0.cell
  rw [mem_Ico, Nat.add_sub_cancel, Int.le_toNat hz0, Int.toNat_lt hz0]
  constructor
  · push_cast
    rw [hcast] at lo
    push_cast at lo hb
    linarith
  · push_cast
    push_cast at hi hb
    linarith

end Fr

section Asm

variable {n' : ℕ} [NeZero n']

def bf_Seq (TT : Finset (Fin n')) (r u M J : ℕ) (B : ℤ → ℤ) (sidx : ℤ → ℕ) : Prop :=
  1 ≤ J ∧ (∀ j, B (j + J) = B j + n') ∧ (∀ j, bf_MT TT r u (B j)) ∧
  (∀ j, B j + ((6 * r + 1 : ℕ) : ℤ) * u ≤ B (j + 1)) ∧
  (∀ j, B (j + 1) - B j < ((M + 2 : ℕ) : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u)) ∧
  (∀ j, sidx j < n' / ((6 * r + 1) * u) ∧ Formalism.G0.Marked (TT.map Fin.valEmbedding) r u (sidx j) ∧
    ∃ q : ℤ, B j = (n' : ℤ) * q + (sidx j : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u)) ∧
  (∀ s < n' / ((6 * r + 1) * u), Formalism.G0.Marked (TT.map Fin.valEmbedding) r u s → ∃ j, sidx j = s)

/- English proof (translation)
Take `⟨hJ, hper, hMT, hstep, hbd, hidx, hall⟩` from `hS`. Establish `hev : ∀ i, Even (2 * r + 2 + 2 * i)` using `fun i => ⟨r + 1 + i, by ring⟩`. Use `⟨bf_F TT r u J B, rfl, hJ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j i`. Distinguish the cases in `hi : i < r`.

Use `show (bf_F TT r u J B).fr (j + (J : ℤ)) i = _`. Rewrite using `[bf_F_fr TT r u J B _ hi, bf_F_fr TT r u J B _ hi, hper]`. Conclude with `bf_tp_shift TT r u (hMT j) (by rw [← hper]; exact hMT _) (by omega) (by omega) (hev i)`. Use `show (if i < r then _ else B (j + (J : ℤ))) = (if i < r then _ else B j) + (n' : ℤ)`. Rewrite using `[if_neg hi, if_neg hi]`.

Conclude with `hper j`. Introduce `j i hi`. Rewrite using `[bf_F_fr TT r u J B _ (show i < r by omega), bf_F_fr TT r u J B _ hi]`. Conclude with `bf_tp_lt TT r u (hMT j) (by omega) (by omega) (hev i) (hev (i + 1)) (by omega)`. Introduce `j`.

Rewrite using `[bf_F_fr TT r u J B _ (show r - 1 < r by omega), bf_F_fr TT r u J B _ (show 0 < r by omega)]`. Establish `A` using `bf_tp_spec TT r u (hMT j) (c := 2 * r + 2 + 2 * (r - 1)) (by omega) (by omega) (hev _)`. Establish `Bq` using `bf_tp_spec TT r u (hMT (j + 1)) (c := 2 * r + 2 + 2 * 0) (by omega) (by omega) (hev _)`. Establish `h1` using `bf_cu (show 2 * r + 2 + 2 * (r - 1) ≤ 6 * r + 1 by omega) u`. Establish `h2` using `bf_u_le (show 1 ≤ 2 * r + 2 + 2 * 0 by omega) u`.

Combine the linear relations using `[A.1.2.1, Bq.1.1, hstep j]`. Introduce `j i hi`. Rewrite using `[bf_F_fr TT r u J B _ hi]`. Establish `A` using `bf_tp_spec TT r u (hMT j) (c := 2 * r + 2 + 2 * i) (by omega) (by omega) (hev _)`. Conclude with `⟨A.1.2.2.1, A.1.2.2.2⟩`.

Introduce `j i x hi h1 h2 hx`. Rewrite `h1` using `[bf_F_fr TT r u J B _ (show i < r by omega)]`. Rewrite `h2` using `[bf_F_fr TT r u J B _ hi]`. Establish `A` using `bf_tp_spec TT r u (hMT j) (c := 2 * r + 2 + 2 * i) (by omega) (by omega) (hev _)`. Establish `A2` using `bf_tp_spec TT r u (hMT j) (c := 2 * r + 2 + 2 * (i + 1)) (by omega) (by omega) (hev _)`.

Establish `g1` using `bf_u_le (show 1 ≤ 2 * r + 2 + 2 * i by omega) u`. Establish `g2` using `bf_cu (show 2 * r + 2 + 2 * (i + 1) ≤ 6 * r + 1 by omega) u`. Take `⟨c, hce, hc1, hc2, hxc⟩` from `bf_class TT r u (hMT j) hu hx (by linarith [A.1.1]) (by linarith [A2.1.2.1])`. Take `⟨m, hm⟩` from `hce`. Break down `Nat.lt_trichotomy c (2 * r + 2 + 2 * i) with h | h | h` into its components or cases.

Use `bf_tp_lt TT r u (hMT j) hc1 (by omega) ⟨m, hm⟩ (hev i) h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite `hxc` using `[h]`. Use linear arithmetic over natural numbers and integers. Break down `Nat.lt_trichotomy c (2 * r + 2 + 2 * (i + 1)) with h' | h' | h'` into its components or cases.

Use linear arithmetic over natural numbers and integers. Rewrite `hxc` using `[h']`. Use linear arithmetic over natural numbers and integers. Use `bf_tp_lt TT r u (hMT j) (by omega) hc2 (hev (i + 1)) ⟨m, hm⟩ h'` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Introduce `j`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hS1` using `bf_card_image TT r u (hMT (j - 1)) (4 * r + 2) r ⟨2 * r + 1, by ring⟩ (by omega) (fun k hk => by omega)`. Use `le_trans (le_of_eq hS1.symm) (card_le_card fun y hy => ?_)` and prove the remaining obligations. Take `⟨k, hk, rfl⟩` from `mem_image.1 hy`.

Conclude with `bf_LL_first hr hMT hstep j (mem_range.1 hk)`. Introduce `x hx hc`. Take `⟨b, c, hb, he, h1, h2, rfl⟩` from `bf_LL_key hr hu hMT hstep j x hx hc`. Conclude with `(bf_tp_spec TT r u hb h1 h2 he).1.2.2.2`. Introduce `j i hi`.

Take `⟨h1, h2, q, hq⟩` from `hidx j`. Use `⟨sidx j, h1, h2, ?_⟩` and prove the remaining obligations. Rewrite using `[bf_F_fr TT r u J B _ hi]`. Conclude with `bf_cell (hMT j) (sidx j) q hq h1 (by omega) (by omega) (hev i)`. Introduce `s hs hM`.

Take `⟨j, rfl⟩` from `hall s hs hM`. Take `⟨h1, h2, q, hq⟩` from `hidx j`. Use `⟨j, ?_⟩` and prove the remaining obligations. Rewrite using `[bf_F_fr TT r u J B _ (show 0 < r by omega)]`. Conclude with `bf_cell (hMT j) (sidx j) q hq h1 (by omega) (by omega) (hev 0)`.

Introduce `j`. Rewrite using `[bf_F_fr TT r u J B _ (show r - 1 < r by omega), bf_F_fr TT r u J B _ (show 0 < r by omega)]`. Establish `A` using `bf_tp_spec TT r u (hMT j) (c := 2 * r + 2 + 2 * (r - 1)) (by omega) (by omega) (hev _)`. Establish `Bq` using `bf_tp_spec TT r u (hMT (j - 1)) (c := 2 * r + 2 + 2 * 0) (by omega) (by omega) (hev _)`. Establish `h1` using `bf_cu (show 2 * r + 2 + 2 * (r - 1) ≤ 6 * r + 1 by omega) u`.

Establish `h2` using `bf_u_le (show 1 ≤ 2 * r + 2 + 2 * 0 by omega) u`. Establish `h3` using `hbd (j - 1)`. Rewrite `h3` using `[sub_add_cancel]`. Establish `h4 : ((M + 3 : ℕ) : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u) ≤ Gp` using `by exact_mod_cast hG`. Establish `h5 : ((M + 3 : ℕ) : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u) = ((M + 2 : ℕ) : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u) + ((6 * r + 1 : ℕ) : ℤ) * u` using `by push_cast; ring`.

Combine the linear relations using `[A.1.2.1, Bq.1.1]`. Introduce `j x hx hc`. Take `⟨b, c, hb, he, h1, h2, rfl⟩` from `bf_LL_key hr hu hMT hstep j x hx hc`. Conclude with `bf_gapGt hL j hb h1 h2 he`. Introduce `j`.

Rewrite using `[bf_F_fr TT r u J B _ (show 0 < r by omega)]`. Conclude with `bf_gapGt hL j (hMT j) (by omega) (by omega) (hev 0)`.
-/
theorem bf_frames (TT : Finset (Fin n')) (r u L₂ Gp M J : ℕ) (B : ℤ → ℤ) (sidx : ℤ → ℕ) (hr : 2 ≤ r) (hu : 1 ≤ u)
    (hL : L₂ < u) (hG : (M + 3) * ((6 * r + 1) * u) ≤ Gp) (hS : bf_Seq TT r u M J B sidx) :
    ∃ F : Frames n' r, F.TT = TT ∧
      1 ≤ F.J ∧
      (∀ j : ℤ, ∀ i, F.fr (j + F.J) i = F.fr j i + n') ∧
      (∀ j : ℤ, ∀ i, i + 1 < r → F.fr j i < F.fr j (i + 1)) ∧
      (∀ j : ℤ, F.fr j (r - 1) < F.fr (j + 1) 0) ∧
      (∀ j : ℤ, ∀ i, i < r → posOf n' (F.fr j i) ∈ F.TT ∧ Even (F.fr j i)) ∧
      (∀ j : ℤ, ∀ i, ∀ x : ℤ, i + 1 < r → F.fr j i < x → x < F.fr j (i + 1) → posOf n' x ∉ F.TT) ∧
      (∀ j : ℤ, r ≤ (F.LLset j).card ∧
        ∀ x ∈ F.LLset j, (((F.LLset j).filter (· ≤ x)).card ≤ r ∨
          (F.LLset j).card < ((F.LLset j).filter (· ≤ x)).card + r) → Even x) ∧
      (∀ j : ℤ, ∀ i < r, ∃ s < n' / ((6 * r + 1) * u), Formalism.G0.Marked (TT.map Fin.valEmbedding) r u s ∧
        (F.fr j i % (n' : ℤ)).toNat ∈ Formalism.G0.cell r u s (2 * r + 2 + 2 * i)) ∧
      (∀ s < n' / ((6 * r + 1) * u), Formalism.G0.Marked (TT.map Fin.valEmbedding) r u s →
        ∃ j : ℤ, (F.fr j 0 % (n' : ℤ)).toNat ∈ Formalism.G0.cell r u s (2 * r + 2)) ∧
      (∀ j : ℤ, F.fr j (r - 1) - F.fr (j - 1) 0 < Gp) ∧
      (∀ j : ℤ, ∀ x ∈ F.LLset j, (((F.LLset j).filter (· ≤ x)).card ≤ r ∨
          (F.LLset j).card < ((F.LLset j).filter (· ≤ x)).card + r) → F.GapGt L₂ j x) ∧
      (∀ j : ℤ, F.GapGt L₂ j (F.fr j 0)) := by
  obtain ⟨hJ, hper, hMT, hstep, hbd, hidx, hall⟩ := hS
  have hev : ∀ i, Even (2 * r + 2 + 2 * i) := fun i => ⟨r + 1 + i, by ring⟩
  refine ⟨bf_F TT r u J B, rfl, hJ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j i
    by_cases hi : i < r
    · show (bf_F TT r u J B).fr (j + (J : ℤ)) i = _
      rw [bf_F_fr TT r u J B _ hi, bf_F_fr TT r u J B _ hi, hper]
      exact bf_tp_shift TT r u (hMT j) (by rw [← hper]; exact hMT _) (by omega) (by omega) (hev i)
    · show (if i < r then _ else B (j + (J : ℤ))) = (if i < r then _ else B j) + (n' : ℤ)
      rw [if_neg hi, if_neg hi]
      exact hper j
  · intro j i hi
    rw [bf_F_fr TT r u J B _ (show i < r by omega), bf_F_fr TT r u J B _ hi]
    exact bf_tp_lt TT r u (hMT j) (by omega) (by omega) (hev i) (hev (i + 1)) (by omega)
  · intro j
    rw [bf_F_fr TT r u J B _ (show r - 1 < r by omega), bf_F_fr TT r u J B _ (show 0 < r by omega)]
    have A := bf_tp_spec TT r u (hMT j) (c := 2 * r + 2 + 2 * (r - 1)) (by omega) (by omega) (hev _)
    have Bq := bf_tp_spec TT r u (hMT (j + 1)) (c := 2 * r + 2 + 2 * 0) (by omega) (by omega) (hev _)
    have h1 := bf_cu (show 2 * r + 2 + 2 * (r - 1) ≤ 6 * r + 1 by omega) u
    have h2 := bf_u_le (show 1 ≤ 2 * r + 2 + 2 * 0 by omega) u
    linarith [A.1.2.1, Bq.1.1, hstep j]
  · intro j i hi
    rw [bf_F_fr TT r u J B _ hi]
    have A := bf_tp_spec TT r u (hMT j) (c := 2 * r + 2 + 2 * i) (by omega) (by omega) (hev _)
    exact ⟨A.1.2.2.1, A.1.2.2.2⟩
  · intro j i x hi h1 h2 hx
    rw [bf_F_fr TT r u J B _ (show i < r by omega)] at h1
    rw [bf_F_fr TT r u J B _ hi] at h2
    have A := bf_tp_spec TT r u (hMT j) (c := 2 * r + 2 + 2 * i) (by omega) (by omega) (hev _)
    have A2 := bf_tp_spec TT r u (hMT j) (c := 2 * r + 2 + 2 * (i + 1)) (by omega) (by omega) (hev _)
    have g1 := bf_u_le (show 1 ≤ 2 * r + 2 + 2 * i by omega) u
    have g2 := bf_cu (show 2 * r + 2 + 2 * (i + 1) ≤ 6 * r + 1 by omega) u
    obtain ⟨c, hce, hc1, hc2, hxc⟩ := bf_class TT r u (hMT j) hu hx (by linarith [A.1.1]) (by linarith [A2.1.2.1])
    obtain ⟨m, hm⟩ := hce
    rcases Nat.lt_trichotomy c (2 * r + 2 + 2 * i) with h | h | h
    · have := bf_tp_lt TT r u (hMT j) hc1 (by omega) ⟨m, hm⟩ (hev i) h
      omega
    · rw [h] at hxc; omega
    · rcases Nat.lt_trichotomy c (2 * r + 2 + 2 * (i + 1)) with h' | h' | h'
      · omega
      · rw [h'] at hxc; omega
      · have := bf_tp_lt TT r u (hMT j) (by omega) hc2 (hev (i + 1)) ⟨m, hm⟩ h'
        omega
  · intro j
    refine ⟨?_, ?_⟩
    · have hS1 := bf_card_image TT r u (hMT (j - 1)) (4 * r + 2) r ⟨2 * r + 1, by ring⟩ (by omega)
        (fun k hk => by omega)
      refine le_trans (le_of_eq hS1.symm) (card_le_card fun y hy => ?_)
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hy
      exact bf_LL_first hr hMT hstep j (mem_range.1 hk)
    · intro x hx hc
      obtain ⟨b, c, hb, he, h1, h2, rfl⟩ := bf_LL_key hr hu hMT hstep j x hx hc
      exact (bf_tp_spec TT r u hb h1 h2 he).1.2.2.2
  · intro j i hi
    obtain ⟨h1, h2, q, hq⟩ := hidx j
    refine ⟨sidx j, h1, h2, ?_⟩
    rw [bf_F_fr TT r u J B _ hi]
    exact bf_cell (hMT j) (sidx j) q hq h1 (by omega) (by omega) (hev i)
  · intro s hs hM
    obtain ⟨j, rfl⟩ := hall s hs hM
    obtain ⟨h1, h2, q, hq⟩ := hidx j
    refine ⟨j, ?_⟩
    rw [bf_F_fr TT r u J B _ (show 0 < r by omega)]
    exact bf_cell (hMT j) (sidx j) q hq h1 (by omega) (by omega) (hev 0)
  · intro j
    rw [bf_F_fr TT r u J B _ (show r - 1 < r by omega), bf_F_fr TT r u J B _ (show 0 < r by omega)]
    have A := bf_tp_spec TT r u (hMT j) (c := 2 * r + 2 + 2 * (r - 1)) (by omega) (by omega) (hev _)
    have Bq := bf_tp_spec TT r u (hMT (j - 1)) (c := 2 * r + 2 + 2 * 0) (by omega) (by omega) (hev _)
    have h1 := bf_cu (show 2 * r + 2 + 2 * (r - 1) ≤ 6 * r + 1 by omega) u
    have h2 := bf_u_le (show 1 ≤ 2 * r + 2 + 2 * 0 by omega) u
    have h3 := hbd (j - 1)
    rw [sub_add_cancel] at h3
    have h4 : ((M + 3 : ℕ) : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u) ≤ Gp := by exact_mod_cast hG
    have h5 : ((M + 3 : ℕ) : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u) =
        ((M + 2 : ℕ) : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u) + ((6 * r + 1 : ℕ) : ℤ) * u := by push_cast; ring
    linarith [A.1.2.1, Bq.1.1]
  · intro j x hx hc
    obtain ⟨b, c, hb, he, h1, h2, rfl⟩ := bf_LL_key hr hu hMT hstep j x hx hc
    exact bf_gapGt hL j hb h1 h2 he
  · intro j
    rw [bf_F_fr TT r u J B _ (show 0 < r by omega)]
    exact bf_gapGt hL j (hMT j) (by omega) (by omega) (hev 0)

end Asm

section Enum

variable {n' : ℕ} [NeZero n']

/- English proof (translation)
Establish `hv : (posOf n' y).val = z`. Establish `h1` using `posOf_val n' y`. Rewrite `h1` using `[hy, add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hz)]`. Rewrite using `[hy, add_comm]`. Conclude with `h1` after adjusting the coercions.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `mem_map.2 ⟨posOf n' y, h, hv⟩`. Introduce `h`. Take `⟨a, ha, hav⟩` from `mem_map.1 h`.

Establish `: a = posOf n' y` using `Fin.ext (by rw [hv]; exact hav)`. Rewrite using `[← this]`. Conclude with `ha`.
-/
theorem bf_top_iff (TT : Finset (Fin n')) (y q : ℤ) (z : ℕ) (hy : y = (n' : ℤ) * q + z) (hz : z < n') :
    posOf n' y ∈ TT ↔ z ∈ TT.map Fin.valEmbedding := by
  have hv : (posOf n' y).val = z := by
    have h1 := posOf_val n' y
    rw [hy, add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hz)] at h1
    rw [hy, add_comm]
    exact_mod_cast h1
  constructor
  · intro h
    exact mem_map.2 ⟨posOf n' y, h, hv⟩
  · intro h
    obtain ⟨a, ha, hav⟩ := mem_map.1 h
    have : a = posOf n' y := Fin.ext (by rw [hv]; exact hav)
    rw [← this]; exact ha

/- English proof (translation)
Introduce `c h1 h2`. Take `⟨c0, rfl⟩ : ∃ c0, c = c0 + 1` from `⟨c - 1, by omega⟩`. Establish `hsn : (s + 1) * ((6 * r + 1) * u) ≤ n'` using `le_trans (Nat.mul_le_mul_right _ hs) (Nat.div_mul_le_self _ _)`. Establish `hsn' : (s : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u) + ((6 * r + 1 : ℕ) : ℤ) * u ≤ n'`. Use `(Nat.cast_le (α := ℤ)).2 hsn` as an intermediate fact.

Move the coercions through the operations in `at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcu` using `bf_cu h2 u`. Establish `hcast : ((c0 + 1 : ℕ) : ℤ) * u = (c0 : ℤ) * u + u` using `by push_cast; ring`. Establish `hs0 : (0 : ℤ) ≤ (s : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u)` using `by positivity`.

Establish `hc0 : (0 : ℤ) ≤ (c0 : ℤ) * u` using `by positivity`. Establish `hfold : ∀ y : ℤ, (n' : ℤ) * q + (s : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u) + ((c0 + 1 : ℕ) : ℤ) * u - u ≤ y → y < (n' : ℤ) * q + (s : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u) + ((c0 + 1 : ℕ) : ℤ) * u → ∃ z : ℕ, y = (n' : ℤ) * q + z ∧ z < n' ∧ z ∈ Formalism.G0.cell r u s (c0 + 1)`. Introduce `y lo hi`. Rewrite `lo` using `[hcast]`. Establish `hz0 : 0 ≤ y - (n' : ℤ) * q` using `by linarith`.

Take `⟨z, hz⟩` from `Int.eq_ofNat_of_zero_le hz0`. Use `⟨z, by linarith, ?_, ?_⟩` and prove the remaining obligations. Establish `: (z : ℤ) < n'` using `by linarith`. Conclude with `this` after adjusting the coercions. Unfold `Formalism.G0.cell`.

Rewrite using `[mem_Ico, Nat.add_sub_cancel]`. Prove the components needed by the constructor for the conclusion. Establish `: ((s * ((6 * r + 1) * u) + c0 * u : ℕ) : ℤ) ≤ (z : ℤ)`. Use `push_cast`. Move the coercions through the operations in `at lo`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `this` after adjusting the coercions. Establish `: (z : ℤ) < ((s * ((6 * r + 1) * u) + (c0 + 1) * u : ℕ) : ℤ)`. Use `push_cast`. Move the coercions through the operations in `at hi`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `this` after adjusting the coercions. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `ho y lo hi hy`. Take `⟨z, hyz, hzn, hzc⟩` from `hfold y lo hi`.

Establish `hzT` using `(bf_top_iff TT y q z hyz hzn).1 hy`. Establish `hemp` using `(hM (c0 + 1) h1 h2).1 ho`. Establish `: z ∈ TT.map Fin.valEmbedding ∩ Formalism.G0.cell r u s (c0 + 1)` using `mem_inter.2 ⟨hzT, hzc⟩`. Rewrite `this` using `[hemp]`. Conclude with `absurd this (notMem_empty _)`.

Introduce `he`. Take `⟨x, hx, hxe⟩` from `(hM (c0 + 1) h1 h2).2 he`. Establish `hxm : x ∈ TT.map Fin.valEmbedding ∩ Formalism.G0.cell r u s (c0 + 1)` using `by rw [hx]; exact mem_singleton_self x`. Take `⟨hxT, hxc⟩` from `mem_inter.1 hxm`. Unfold `Formalism.G0.cell at hxc`.

Rewrite `hxc` using `[mem_Ico, Nat.add_sub_cancel]`. Establish `hlo : ((s * ((6 * r + 1) * u) + c0 * u : ℕ) : ℤ) ≤ (x : ℤ)` using `by exact_mod_cast hxc.1`. Establish `hhi : (x : ℤ) < ((s * ((6 * r + 1) * u) + (c0 + 1) * u : ℕ) : ℤ)` using `by exact_mod_cast hxc.2`. Establish `hxn : x < n'`. Take `⟨a, _, hav⟩` from `mem_map.1 hxT`.

Rewrite using `[← hav]`. Conclude with `a.2`. Use `⟨(n' : ℤ) * q + x, ⟨?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hcast]`. Move the coercions through the operations in `at hlo ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion. Move the coercions through the operations in `at hhi ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(bf_top_iff TT _ q x rfl hxn).2 hxT`. Conclude with `Even.add (Even.mul_right ((Int.even_coe_nat n').2 hn) q) ((Int.even_coe_nat x).2 hxe)`.

Introduce `y lo hi hy`. Take `⟨z, hyz, hzn, hzc⟩` from `hfold y lo hi`. Establish `hzT` using `(bf_top_iff TT y q z hyz hzn).1 hy`. Establish `: z ∈ TT.map Fin.valEmbedding ∩ Formalism.G0.cell r u s (c0 + 1)` using `mem_inter.2 ⟨hzT, hzc⟩`. Rewrite `this` using `[hx, mem_singleton]`.

Rewrite using `[hyz, this]`.
-/
theorem bf_MT_of_marked (TT : Finset (Fin n')) (r u : ℕ) (hn : Even n') (s : ℕ) (hs : s < n' / ((6 * r + 1) * u))
    (hM : Formalism.G0.Marked (TT.map Fin.valEmbedding) r u s) (q : ℤ) :
    bf_MT TT r u ((n' : ℤ) * q + (s : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u)) := by
  intro c h1 h2
  obtain ⟨c0, rfl⟩ : ∃ c0, c = c0 + 1 := ⟨c - 1, by omega⟩
  have hsn : (s + 1) * ((6 * r + 1) * u) ≤ n' :=
    le_trans (Nat.mul_le_mul_right _ hs) (Nat.div_mul_le_self _ _)
  have hsn' : (s : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u) + ((6 * r + 1 : ℕ) : ℤ) * u ≤ n' := by
    have := (Nat.cast_le (α := ℤ)).2 hsn
    push_cast at this ⊢
    linarith
  have hcu := bf_cu h2 u
  have hcast : ((c0 + 1 : ℕ) : ℤ) * u = (c0 : ℤ) * u + u := by push_cast; ring
  have hs0 : (0 : ℤ) ≤ (s : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u) := by positivity
  have hc0 : (0 : ℤ) ≤ (c0 : ℤ) * u := by positivity

  have hfold : ∀ y : ℤ, (n' : ℤ) * q + (s : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u) + ((c0 + 1 : ℕ) : ℤ) * u - u ≤ y →
      y < (n' : ℤ) * q + (s : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u) + ((c0 + 1 : ℕ) : ℤ) * u →
      ∃ z : ℕ, y = (n' : ℤ) * q + z ∧ z < n' ∧ z ∈ Formalism.G0.cell r u s (c0 + 1) := by
    intro y lo hi
    rw [hcast] at lo
    have hz0 : 0 ≤ y - (n' : ℤ) * q := by linarith
    obtain ⟨z, hz⟩ := Int.eq_ofNat_of_zero_le hz0
    refine ⟨z, by linarith, ?_, ?_⟩
    · have : (z : ℤ) < n' := by linarith
      exact_mod_cast this
    · unfold Formalism.G0.cell
      rw [mem_Ico, Nat.add_sub_cancel]
      constructor
      · have : ((s * ((6 * r + 1) * u) + c0 * u : ℕ) : ℤ) ≤ (z : ℤ) := by
          push_cast
          push_cast at lo
          linarith
        exact_mod_cast this
      · have : (z : ℤ) < ((s * ((6 * r + 1) * u) + (c0 + 1) * u : ℕ) : ℤ) := by
          push_cast
          push_cast at hi
          linarith
        exact_mod_cast this
  refine ⟨?_, ?_⟩
  · intro ho y lo hi hy
    obtain ⟨z, hyz, hzn, hzc⟩ := hfold y lo hi
    have hzT := (bf_top_iff TT y q z hyz hzn).1 hy
    have hemp := (hM (c0 + 1) h1 h2).1 ho
    have : z ∈ TT.map Fin.valEmbedding ∩ Formalism.G0.cell r u s (c0 + 1) := mem_inter.2 ⟨hzT, hzc⟩
    rw [hemp] at this
    exact absurd this (notMem_empty _)
  · intro he
    obtain ⟨x, hx, hxe⟩ := (hM (c0 + 1) h1 h2).2 he
    have hxm : x ∈ TT.map Fin.valEmbedding ∩ Formalism.G0.cell r u s (c0 + 1) := by rw [hx]; exact mem_singleton_self x
    obtain ⟨hxT, hxc⟩ := mem_inter.1 hxm
    unfold Formalism.G0.cell at hxc
    rw [mem_Ico, Nat.add_sub_cancel] at hxc
    have hlo : ((s * ((6 * r + 1) * u) + c0 * u : ℕ) : ℤ) ≤ (x : ℤ) := by exact_mod_cast hxc.1
    have hhi : (x : ℤ) < ((s * ((6 * r + 1) * u) + (c0 + 1) * u : ℕ) : ℤ) := by exact_mod_cast hxc.2
    have hxn : x < n' := by
      obtain ⟨a, _, hav⟩ := mem_map.1 hxT
      rw [← hav]; exact a.2
    refine ⟨(n' : ℤ) * q + x, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hcast]
      push_cast at hlo ⊢
      linarith
    · push_cast at hhi ⊢
      linarith
    · exact (bf_top_iff TT _ q x rfl hxn).2 hxT
    · exact Even.add (Even.mul_right ((Int.even_coe_nat n').2 hn) q) ((Int.even_coe_nat x).2 hxe)
    · intro y lo hi hy
      obtain ⟨z, hyz, hzn, hzc⟩ := hfold y lo hi
      have hzT := (bf_top_iff TT y q z hyz hzn).1 hy
      have : z ∈ TT.map Fin.valEmbedding ∩ Formalism.G0.cell r u s (c0 + 1) := mem_inter.2 ⟨hzT, hzc⟩
      rw [hx, mem_singleton] at this
      rw [hyz, this]

end Enum

section Enum2

variable (T : Finset ℕ) (r u t : ℕ)

def bf_MS : Finset ℕ := (range t).filter (Formalism.G0.Marked T r u)

def bf_ms (a : ℕ) : ℕ :=
  if h : a < (bf_MS T r u t).card then (bf_MS T r u t).orderEmbOfFin rfl ⟨a, h⟩ else 0

variable {T r u t}

/- English proof (translation)
Unfold `bf_ms`. Rewrite using `[dif_pos h]`. Conclude with `orderEmbOfFin_mem _ _ _`.
-/
theorem bf_ms_mem {a : ℕ} (h : a < (bf_MS T r u t).card) : bf_ms T r u t a ∈ bf_MS T r u t := by
  unfold bf_ms; rw [dif_pos h]; exact orderEmbOfFin_mem _ _ _

/- English proof (translation)
Unfold `bf_ms`. Rewrite using `[dif_pos (lt_trans h h'), dif_pos h']`. Conclude with `((bf_MS T r u t).orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.2 h)`.
-/
theorem bf_ms_lt {a a' : ℕ} (h : a < a') (h' : a' < (bf_MS T r u t).card) :
    bf_ms T r u t a < bf_ms T r u t a' := by
  unfold bf_ms; rw [dif_pos (lt_trans h h'), dif_pos h']
  exact ((bf_MS T r u t).orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.2 h)

/- English proof (translation)
Break down `Nat.eq_or_lt_of_le h with h1 | h1` into its components or cases. Rewrite using `[h1]`. Conclude with `le_of_lt (bf_ms_lt h1 h')`.
-/
theorem bf_ms_le {a a' : ℕ} (h : a ≤ a') (h' : a' < (bf_MS T r u t).card) :
    bf_ms T r u t a ≤ bf_ms T r u t a' := by
  rcases Nat.eq_or_lt_of_le h with h1 | h1
  · rw [h1]
  · exact le_of_lt (bf_ms_lt h1 h')

/- English proof (translation)
Establish `: s ∈ Set.range ((bf_MS T r u t).orderEmbOfFin rfl)` using `by rw [range_orderEmbOfFin]; exact hs`. Take `⟨a, ha⟩` from `this`. Conclude with `⟨a.val, a.2, by unfold bf_ms; rw [dif_pos a.2]; exact ha⟩`.
-/
theorem bf_ms_surj {s : ℕ} (hs : s ∈ bf_MS T r u t) : ∃ a, a < (bf_MS T r u t).card ∧ bf_ms T r u t a = s := by
  have : s ∈ Set.range ((bf_MS T r u t).orderEmbOfFin rfl) := by rw [range_orderEmbOfFin]; exact hs
  obtain ⟨a, ha⟩ := this
  exact ⟨a.val, a.2, by unfold bf_ms; rw [dif_pos a.2]; exact ha⟩

/- English proof (translation)
Take `⟨a'', h1, rfl⟩` from `bf_ms_surj hs`. Establish `h2 : a < a''`. Assume the negation of the conclusion as `hc`. Use `bf_ms_le (not_lt.1 hc) ha` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Conclude with `⟨by omega, bf_ms_le (by omega) h1⟩`.
-/
theorem bf_ms_next {a s : ℕ} (ha : a < (bf_MS T r u t).card) (hs : s ∈ bf_MS T r u t)
    (hlt : bf_ms T r u t a < s) : a + 1 < (bf_MS T r u t).card ∧ bf_ms T r u t (a + 1) ≤ s := by
  obtain ⟨a'', h1, rfl⟩ := bf_ms_surj hs
  have h2 : a < a'' := by
    by_contra hc
    have := bf_ms_le (not_lt.1 hc) ha
    omega
  exact ⟨by omega, bf_ms_le (by omega) h1⟩

/- English proof (translation)
Establish `hs` using `mem_range.1 (mem_filter.1 (bf_ms_mem ha)).1`. Establish `ht : 0 < t` using `by omega`. Take `⟨j', hj', hM⟩` from `hcond ((bf_ms T r u t a + 1) % t) (Nat.mod_lt _ ht)`. Rewrite `hM` using `[Nat.mod_add_mod]`. Distinguish the cases in `hv : bf_ms T r u t a + 1 + j' < t`.

Rewrite `hM` using `[Nat.mod_eq_of_lt hv]`. Establish `hmem : bf_ms T r u t a + 1 + j' ∈ bf_MS T r u t` using `mem_filter.2 ⟨mem_range.2 hv, hM⟩`. Take `⟨h1, h2⟩` from `bf_ms_next ha hmem (by omega)`. Conclude with `⟨fun _ => by omega, fun h => by omega⟩`. Establish `hv' : (bf_ms T r u t a + 1 + j') % t = bf_ms T r u t a + 1 + j' - t`.

Rewrite using `[Nat.mod_eq_sub_mod (not_lt.1 hv), Nat.mod_eq_of_lt (by omega)]`. Rewrite `hM` using `[hv']`. Establish `hmem : bf_ms T r u t a + 1 + j' - t ∈ bf_MS T r u t` using `mem_filter.2 ⟨mem_range.2 (by omega), hM⟩`. Use `⟨fun h => ?_, fun _ => ?_⟩` and prove the remaining obligations. Use `mem_range.1 (mem_filter.1 (bf_ms_mem h)).1` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Take `⟨a'', h1, h2⟩` from `bf_ms_surj hmem`. Use `bf_ms_le (Nat.zero_le a'') h1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem bf_next {M : ℕ} (hcond : ∀ s₀ < t, ∃ j ≤ M, Formalism.G0.Marked T r u ((s₀ + j) % t)) (hMt : M + 1 < t) {a : ℕ}
    (ha : a < (bf_MS T r u t).card) :
    (a + 1 < (bf_MS T r u t).card → bf_ms T r u t (a + 1) ≤ bf_ms T r u t a + M + 1) ∧
    (a + 1 = (bf_MS T r u t).card → bf_ms T r u t 0 + t ≤ bf_ms T r u t a + M + 1) := by
  have hs := mem_range.1 (mem_filter.1 (bf_ms_mem ha)).1
  have ht : 0 < t := by omega
  obtain ⟨j', hj', hM⟩ := hcond ((bf_ms T r u t a + 1) % t) (Nat.mod_lt _ ht)
  rw [Nat.mod_add_mod] at hM
  by_cases hv : bf_ms T r u t a + 1 + j' < t
  · rw [Nat.mod_eq_of_lt hv] at hM
    have hmem : bf_ms T r u t a + 1 + j' ∈ bf_MS T r u t := mem_filter.2 ⟨mem_range.2 hv, hM⟩
    obtain ⟨h1, h2⟩ := bf_ms_next ha hmem (by omega)
    exact ⟨fun _ => by omega, fun h => by omega⟩
  · have hv' : (bf_ms T r u t a + 1 + j') % t = bf_ms T r u t a + 1 + j' - t := by
      rw [Nat.mod_eq_sub_mod (not_lt.1 hv), Nat.mod_eq_of_lt (by omega)]
    rw [hv'] at hM
    have hmem : bf_ms T r u t a + 1 + j' - t ∈ bf_MS T r u t := mem_filter.2 ⟨mem_range.2 (by omega), hM⟩
    refine ⟨fun h => ?_, fun _ => ?_⟩
    · have := mem_range.1 (mem_filter.1 (bf_ms_mem h)).1
      omega
    · obtain ⟨a'', h1, h2⟩ := bf_ms_surj hmem
      have := bf_ms_le (Nat.zero_le a'') h1
      omega

/- English proof (translation)
Establish `hJ' : (0 : ℤ) < J` using `by exact_mod_cast hJ`. Take `⟨h1, h2, h3⟩` from `(Int.ediv_emod_unique (a := j) hJ').1 ⟨rfl, rfl⟩`. Distinguish the cases in `h : j % (J : ℤ) + 1 < J`. Use `left`. Take `⟨e1, e2⟩` from `(Int.ediv_emod_unique (a := j + 1) (q := j / J) (r := j % J + 1) hJ').2 ⟨by linarith, by linarith, h⟩`.

Conclude with `⟨e1, by rw [e2]; omega, by omega⟩`. Use `right`. Establish `h5 : j % (J : ℤ) + 1 = J` using `by omega`. Take `⟨e1, e2⟩` from `(Int.ediv_emod_unique (a := j + 1) (q := j / J + 1) (r := 0) hJ').2 ⟨by linarith, le_rfl, hJ'⟩`. Conclude with `⟨e1, by rw [e2]; rfl, by omega⟩`.
-/
theorem bf_succ (J : ℕ) (hJ : 1 ≤ J) (j : ℤ) :
    ((j + 1) / (J : ℤ) = j / J ∧ ((j + 1) % (J : ℤ)).toNat = (j % (J : ℤ)).toNat + 1 ∧
      (j % (J : ℤ)).toNat + 1 < J) ∨
    ((j + 1) / (J : ℤ) = j / J + 1 ∧ ((j + 1) % (J : ℤ)).toNat = 0 ∧ (j % (J : ℤ)).toNat + 1 = J) := by
  have hJ' : (0 : ℤ) < J := by exact_mod_cast hJ
  obtain ⟨h1, h2, h3⟩ := (Int.ediv_emod_unique (a := j) hJ').1 ⟨rfl, rfl⟩
  by_cases h : j % (J : ℤ) + 1 < J
  · left
    obtain ⟨e1, e2⟩ := (Int.ediv_emod_unique (a := j + 1) (q := j / J) (r := j % J + 1) hJ').2
      ⟨by linarith, by linarith, h⟩
    exact ⟨e1, by rw [e2]; omega, by omega⟩
  · right
    have h5 : j % (J : ℤ) + 1 = J := by omega
    obtain ⟨e1, e2⟩ := (Int.ediv_emod_unique (a := j + 1) (q := j / J + 1) (r := 0) hJ').2
      ⟨by linarith, le_rfl, hJ'⟩
    exact ⟨e1, by rw [e2]; rfl, by omega⟩

end Enum2

section Enum3

variable {n' : ℕ} [NeZero n']

/- English proof (translation)
Establish `hJ : 1 ≤ (bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card`. Take `⟨j', _, hM⟩` from `hcond 0 (by omega)`. Conclude with `card_pos.2 ⟨_, mem_filter.2 ⟨mem_range.2 (Nat.mod_lt _ (by omega)), hM⟩⟩`. Establish `hJ' : (0 : ℤ) < ((bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card : ℤ)`. Conclude with `hJ` after adjusting the coercions.

Establish `ha : ∀ j : ℤ, (j % ((bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card : ℤ)).toNat < (bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card`. Introduce `j`. Establish `h1` using `Int.emod_nonneg j hJ'.ne'`. Establish `h2` using `Int.emod_lt_of_pos j hJ'`. Use linear arithmetic over natural numbers and integers.

Establish `hE0 : (0 : ℤ) < ((6 * r + 1 : ℕ) : ℤ) * u`. Establish `: 0 < (6 * r + 1) * u` using `Nat.mul_pos (by omega) hu`. Conclude with `this` after adjusting the coercions. Establish `hsn : ∀ s : ℕ, s < n' / ((6 * r + 1) * u) → (s : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u) + ((6 * r + 1 : ℕ) : ℤ) * u ≤ n'`. Introduce `s hs`.

Establish `h1 : (s + 1) * ((6 * r + 1) * u) ≤ n'` using `le_trans (Nat.mul_le_mul_right _ hs) (Nat.div_mul_le_self _ _)`. Use `(Nat.cast_le (α := ℤ)).2 h1` as an intermediate fact. Move the coercions through the operations in `at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnlt : (n' : ℤ) < ((n' / ((6 * r + 1) * u) : ℕ) : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u) + ((6 * r + 1 : ℕ) : ℤ) * u`.

Establish `h1` using `Nat.lt_mul_div_succ n' (Nat.mul_pos (show 0 < 6 * r + 1 by omega) hu)`. Use `(Nat.cast_lt (α := ℤ)).2 h1` as an intermediate fact. Move the coercions through the operations in `at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨(bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card, fun j => (n' : ℤ) * (j / ((bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card : ℤ)) + (bf_ms (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u)) (j % ((bf_MS (TT.map Fin.valEmbedding) r u (n' …` and prove the remaining obligations.

Introduce `j`. Take `⟨h1, h2, h3⟩` from `(Int.ediv_emod_unique (a := j) hJ').1 ⟨rfl, rfl⟩`. Take `⟨e1, e2⟩` from `(Int.ediv_emod_unique (a := j + ((bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card : ℤ)) (q := j / ((bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card : ℤ) + 1) (r := j % ((bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card : ℤ)) …`. Simplify using `only [e1, e2]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `j`. Establish `hm` using `mem_filter.1 (bf_ms_mem (ha j))`. Conclude with `bf_MT_of_marked TT r u hn _ (mem_range.1 hm.1) hm.2 _`. Introduce `j`. Establish `hm` using `mem_range.1 (mem_filter.1 (bf_ms_mem (ha j))).1`.

Break down `bf_succ _ hJ j with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩` into its components or cases. Simplify using `only [e1, e2]`. Establish `h1` using `bf_ms_lt (Nat.lt_succ_self _) e3`. Establish `h2 : ((bf_ms (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u)) (j % ((bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card : ℤ)).toNat : ℤ) + 1) ≤ (bf_ms (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u)) ((j % ((bf_MS (TT.map Fin.valEmbedding) r u (n' / (( …`. Conclude with `h1` after adjusting the coercions.

Establish `h3` using `mul_le_mul_of_nonneg_right h2 hE0.le`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [e1, e2]`. Establish `h1` using `hsn _ hm`. Establish `h2 : (0 : ℤ) ≤ (bf_ms (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u)) 0 : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u)` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `j`. Take `⟨n1, n2⟩` from `bf_next hcond hMt (ha j)`. Break down `bf_succ _ hJ j with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩` into its components or cases. Simplify using `only [e1, e2]`.

Establish `h1` using `n1 e3`. Establish `h2 : (bf_ms (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u)) ((j % ((bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card : ℤ)).toNat + 1) : ℤ) ≤ (bf_ms (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u)) (j % ((bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 …`. Conclude with `h1` after adjusting the coercions. Establish `h3` using `mul_le_mul_of_nonneg_right h2 hE0.le`. Use `push_cast`.

Move the coercions through the operations in `at h3 hE0`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [e1, e2]`. Establish `h1` using `n2 e3`. Establish `h2 : (bf_ms (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u)) 0 : ℤ) + ((n' / ((6 * r + 1) * u) : ℕ) : ℤ) ≤ (bf_ms (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u)) (j % ((bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card : ℤ)).toNat : ℤ) + M + 1`.

Conclude with `h1` after adjusting the coercions. Establish `h3` using `mul_le_mul_of_nonneg_right h2 hE0.le`. Establish `h4 : ((M + 2 : ℕ) : ℤ) = (M : ℤ) + 2` using `by push_cast; ring`. Rewrite using `[h4]`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `j`. Establish `hm` using `mem_filter.1 (bf_ms_mem (ha j))`. Conclude with `⟨mem_range.1 hm.1, hm.2, _, rfl⟩`. Introduce `s hs hM`. Take `⟨a, ha1, ha2⟩` from `bf_ms_surj (mem_filter.2 ⟨mem_range.2 hs, hM⟩)`.

Use `⟨(a : ℤ), ?_⟩` and prove the remaining obligations. Establish `: ((a : ℤ) % ((bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card : ℤ)).toNat = a`. Rewrite using `[Int.emod_eq_of_lt (by positivity) (by exact_mod_cast ha1)]`. Both sides reduce to the same expression. Simplify using `only [this]`.

Conclude with `ha2`.
-/
theorem bf_seq (TT : Finset (Fin n')) (r u M : ℕ) (hn : Even n') (hu : 1 ≤ u)
    (hcond : Formalism.G0.CondTiles n' (TT.map Fin.valEmbedding) r u M) (hMt : M + 1 < n' / ((6 * r + 1) * u)) :
    ∃ (J : ℕ) (B : ℤ → ℤ) (sidx : ℤ → ℕ), bf_Seq TT r u M J B sidx := by
  have hJ : 1 ≤ (bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card := by
    obtain ⟨j', _, hM⟩ := hcond 0 (by omega)
    exact card_pos.2 ⟨_, mem_filter.2 ⟨mem_range.2 (Nat.mod_lt _ (by omega)), hM⟩⟩
  have hJ' : (0 : ℤ) < ((bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card : ℤ) := by
    exact_mod_cast hJ
  have ha : ∀ j : ℤ, (j % ((bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card : ℤ)).toNat <
      (bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card := by
    intro j
    have h1 := Int.emod_nonneg j hJ'.ne'
    have h2 := Int.emod_lt_of_pos j hJ'
    omega
  have hE0 : (0 : ℤ) < ((6 * r + 1 : ℕ) : ℤ) * u := by
    have : 0 < (6 * r + 1) * u := Nat.mul_pos (by omega) hu
    exact_mod_cast this
  have hsn : ∀ s : ℕ, s < n' / ((6 * r + 1) * u) →
      (s : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u) + ((6 * r + 1 : ℕ) : ℤ) * u ≤ n' := by
    intro s hs
    have h1 : (s + 1) * ((6 * r + 1) * u) ≤ n' :=
      le_trans (Nat.mul_le_mul_right _ hs) (Nat.div_mul_le_self _ _)
    have := (Nat.cast_le (α := ℤ)).2 h1
    push_cast at this ⊢
    linarith
  have hnlt : (n' : ℤ) < ((n' / ((6 * r + 1) * u) : ℕ) : ℤ) * (((6 * r + 1 : ℕ) : ℤ) * u) +
      ((6 * r + 1 : ℕ) : ℤ) * u := by
    have h1 := Nat.lt_mul_div_succ n' (Nat.mul_pos (show 0 < 6 * r + 1 by omega) hu)
    have := (Nat.cast_lt (α := ℤ)).2 h1
    push_cast at this ⊢
    linarith
  refine ⟨(bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card,
    fun j => (n' : ℤ) * (j / ((bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card : ℤ)) +
      (bf_ms (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))
        (j % ((bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card : ℤ)).toNat : ℤ) *
        (((6 * r + 1 : ℕ) : ℤ) * u),
    fun j => bf_ms (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))
        (j % ((bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card : ℤ)).toNat,
    hJ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    obtain ⟨h1, h2, h3⟩ := (Int.ediv_emod_unique (a := j) hJ').1 ⟨rfl, rfl⟩
    obtain ⟨e1, e2⟩ := (Int.ediv_emod_unique
      (a := j + ((bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card : ℤ))
      (q := j / ((bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card : ℤ) + 1)
      (r := j % ((bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card : ℤ)) hJ').2
      ⟨by linarith, h2, h3⟩
    simp only [e1, e2]
    ring
  · intro j
    have hm := mem_filter.1 (bf_ms_mem (ha j))
    exact bf_MT_of_marked TT r u hn _ (mem_range.1 hm.1) hm.2 _
  · intro j
    have hm := mem_range.1 (mem_filter.1 (bf_ms_mem (ha j))).1
    rcases bf_succ _ hJ j with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
    · simp only [e1, e2]
      have h1 := bf_ms_lt (Nat.lt_succ_self _) e3
      have h2 : ((bf_ms (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))
          (j % ((bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card : ℤ)).toNat : ℤ) + 1) ≤
          (bf_ms (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))
          ((j % ((bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card : ℤ)).toNat + 1) : ℤ) := by
        exact_mod_cast h1
      have h3 := mul_le_mul_of_nonneg_right h2 hE0.le
      linarith
    · simp only [e1, e2]
      have h1 := hsn _ hm
      have h2 : (0 : ℤ) ≤ (bf_ms (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u)) 0 : ℤ) *
          (((6 * r + 1 : ℕ) : ℤ) * u) := by positivity
      linarith
  · intro j
    obtain ⟨n1, n2⟩ := bf_next hcond hMt (ha j)
    rcases bf_succ _ hJ j with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
    · simp only [e1, e2]
      have h1 := n1 e3
      have h2 : (bf_ms (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))
          ((j % ((bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card : ℤ)).toNat + 1) : ℤ) ≤
          (bf_ms (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))
          (j % ((bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card : ℤ)).toNat : ℤ) + M + 1 := by
        exact_mod_cast h1
      have h3 := mul_le_mul_of_nonneg_right h2 hE0.le
      push_cast
      push_cast at h3 hE0
      linarith
    · simp only [e1, e2]
      have h1 := n2 e3
      have h2 : (bf_ms (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u)) 0 : ℤ) +
          ((n' / ((6 * r + 1) * u) : ℕ) : ℤ) ≤
          (bf_ms (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))
          (j % ((bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card : ℤ)).toNat : ℤ) + M + 1 := by
        exact_mod_cast h1
      have h3 := mul_le_mul_of_nonneg_right h2 hE0.le
      have h4 : ((M + 2 : ℕ) : ℤ) = (M : ℤ) + 2 := by push_cast; ring
      rw [h4]
      linarith
  · intro j
    have hm := mem_filter.1 (bf_ms_mem (ha j))
    exact ⟨mem_range.1 hm.1, hm.2, _, rfl⟩
  · intro s hs hM
    obtain ⟨a, ha1, ha2⟩ := bf_ms_surj (mem_filter.2 ⟨mem_range.2 hs, hM⟩)
    refine ⟨(a : ℤ), ?_⟩
    have : ((a : ℤ) % ((bf_MS (TT.map Fin.valEmbedding) r u (n' / ((6 * r + 1) * u))).card : ℤ)).toNat = a := by
      rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast ha1)]
      rfl
    simp only [this]
    exact ha2

end Enum3

/- English proof (translation)
Introduce `r h hr hh n' _ TT L₁ L₂ de x hn hL1 hL12 hde hde1 hx hLu h3G hgood`. Introduce `u G' T ell`. Take `⟨_, hTiles, _⟩` from `hgood`. Establish `hu : 1 ≤ goodU de` using `bd_goodU_pos hde`. Establish `hell : 0 < (6 * r + 1) * goodU de` using `Nat.mul_pos (by omega) hu`.

Establish `hGdef : goodG' r de h x = (orbitSmallMultiplicity r h x + 5) * ((6 * r + 1) * goodU de)` using `rfl`. Establish `hMt : orbitSmallMultiplicity r h x + 1 < n' / ((6 * r + 1) * goodU de)`. Establish `h1 : (orbitSmallMultiplicity r h x + 2) * ((6 * r + 1) * goodU de) ≤ n'`. Establish `h2 : (orbitSmallMultiplicity r h x + 2) * ((6 * r + 1) * goodU de) ≤ (orbitSmallMultiplicity r h x + 5) * ((6 * r + 1) * goodU de)` using `Nat.mul_le_mul_right _ (by omega)`. Rewrite `h3G` using `[hGdef]`.

Use linear arithmetic over natural numbers and integers. Conclude with `(Nat.le_div_iff_mul_le hell).2 h1`. Take `⟨J, B, sidx, hS⟩` from `bf_seq TT r (goodU de) (orbitSmallMultiplicity r h x) hn hu hTiles hMt`. Conclude with `bf_frames TT r (goodU de) L₂ (goodG' r de h x) (orbitSmallMultiplicity r h x) J B sidx hr hu hLu (by rw [hGdef]; exact Nat.mul_le_mul_right _ (by omega)) hS`.
-/
theorem bf_restFrames (D : Formalism.BasicNotions.D7) : bd_RestFrames D := by
  intro r h hr hh n' _ TT L₁ L₂ de x hn hL1 hL12 hde hde1 hx hLu h3G hgood
  intro u G' T ell
  obtain ⟨_, hTiles, _⟩ := hgood
  have hu : 1 ≤ goodU de := bd_goodU_pos hde
  have hell : 0 < (6 * r + 1) * goodU de := Nat.mul_pos (by omega) hu
  have hGdef : goodG' r de h x = (orbitSmallMultiplicity r h x + 5) * ((6 * r + 1) * goodU de) := rfl
  have hMt : orbitSmallMultiplicity r h x + 1 < n' / ((6 * r + 1) * goodU de) := by
    have h1 : (orbitSmallMultiplicity r h x + 2) * ((6 * r + 1) * goodU de) ≤ n' := by
      have h2 : (orbitSmallMultiplicity r h x + 2) * ((6 * r + 1) * goodU de) ≤ (orbitSmallMultiplicity r h x + 5) * ((6 * r + 1) * goodU de) :=
        Nat.mul_le_mul_right _ (by omega)
      rw [hGdef] at h3G
      omega
    exact (Nat.le_div_iff_mul_le hell).2 h1
  obtain ⟨J, B, sidx, hS⟩ := bf_seq TT r (goodU de) (orbitSmallMultiplicity r h x) hn hu hTiles hMt
  exact bf_frames TT r (goodU de) L₂ (goodG' r de h x) (orbitSmallMultiplicity r h x) J B sidx hr hu hLu
    (by rw [hGdef]; exact Nat.mul_le_mul_right _ (by omega)) hS

/- English proof (translation)
The claim follows from `orbit_lemma_of_frame_construction D (bf_restFrames D)`.
-/
theorem good_orbits_lemma (D : Formalism.BasicNotions.D7) : GoodOrbitPositions D := orbit_lemma_of_frame_construction D (bf_restFrames D)

end Formalism.MainNotions.G.WittFrameLocaliserOrders

end

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.G.WittFrameLocaliserOrders

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning

section B3gen

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Conclude with `S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)`.
-/
theorem det_mem_subalgebra_alt {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  exact S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)

/- English proof (translation)
Rewrite using `[Matrix.adjugate_apply]`. Apply `det_mem_subalgebra_alt` to reduce the goal to its premises. Introduce `a b`. Distinguish the cases in `ha : a = j`. Substitute `ha` using the available equality.

Rewrite using `[Matrix.updateRow_self]`. Distinguish the cases in `hb : b = i`. Substitute `hb` using the available equality. Simplify using `[S.one_mem]`. Simplify using `[hb, S.zero_mem]`.

Rewrite using `[Matrix.updateRow_ne ha]`. Conclude with `h _ _`.
-/
theorem adjugate_mem_subalgebra {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (h : ∀ i j, M i j ∈ S) (i j : Fin n) : M.adjugate i j ∈ S := by
  rw [Matrix.adjugate_apply]
  apply det_mem_subalgebra_alt
  intro a b
  by_cases ha : a = j
  · subst ha
    rw [Matrix.updateRow_self]
    by_cases hb : b = i
    · subst hb; simp [S.one_mem]
    · simp [hb, S.zero_mem]
  · rw [Matrix.updateRow_ne ha]; exact h _ _

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [Formalism.CountingSumsFrames.borderedMatrix]`.
-/
theorem minor_matrix_ring_hom_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (r : ℕ) (ts : Fin r → R) (u : R)
    (T : Matrix (Fin r) (Fin r) R) (b : Fin r → R) :
    (Formalism.CountingSumsFrames.borderedMatrix r ts u T b).map f =
      Formalism.CountingSumsFrames.borderedMatrix r (fun i => f (ts i)) (f u) (T.map f) (fun l => f (b l)) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [Formalism.CountingSumsFrames.borderedMatrix]

/- English proof (translation)
Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, minor_matrix_ring_hom_map]`.
-/
theorem keyMatrix_det_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (r : ℕ) (ts : Fin r → R) (u : R)
    (T : Matrix (Fin r) (Fin r) R) (b : Fin r → R) :
    f (Formalism.CountingSumsFrames.borderedMatrix r ts u T b).det =
      (Formalism.CountingSumsFrames.borderedMatrix r (fun i => f (ts i)) (f u) (T.map f) (fun l => f (b l))).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, minor_matrix_ring_hom_map]

/- English proof (translation)
Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>`. Simplify using `[Formalism.CountingSumsFrames.borderedMatrix, h1, h2, h3, h4]`.
-/
theorem keyMatrix_mem_subalgebra {R : Type} {A : Type} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) (r : ℕ)
    (ts : Fin r → A) (u : A) (T : Matrix (Fin r) (Fin r) A) (b : Fin r → A) (h1 : ∀ i, ts i ∈ S) (h2 : u ∈ S)
    (h3 : ∀ i j, T i j ∈ S) (h4 : ∀ l, b l ∈ S) (i j : Fin (r + 1)) : Formalism.CountingSumsFrames.borderedMatrix r ts u T b i j ∈ S := by
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [Formalism.CountingSumsFrames.borderedMatrix, h1, h2, h3, h4]

/- English proof (translation)
Take `⟨K, rfl⟩` from `Nat.exists_eq_add_of_le h`. Rewrite using `[Fin.sum_univ_add]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem sum_ite_lt_castLE {M : Type*} [AddCommMonoid M] (r k : ℕ) (h : r ≤ k) (f : Fin k → M) :
    ∑ c, (if c.val < r then f c else 0) = ∑ a : Fin r, f (Fin.castLE h a) := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Fin.sum_univ_add]
  simp
  rfl

end B3gen

section B3pos

variable {n' : ℕ} [NeZero n']

/- English proof (translation)
Establish `hn : (0:ℤ) < (n' : ℤ)` using `by exact_mod_cast NeZero.pos n'`. Establish `h0` using `Int.emod_nonneg a hn.ne'`. Establish `h1` using `Int.emod_lt_of_pos a hn`. Establish `h2 : (a % (n':ℤ)).toNat < n'` using `(Int.toNat_lt h0).mpr h1`. Use `show (((a % (n' : ℤ)).toNat % n' : ℕ) : ℤ) = _`.

Rewrite using `[Nat.mod_eq_of_lt h2, Int.toNat_of_nonneg h0]`.
-/
theorem residue_position_val (a : ℤ) : ((posOf n' a).val : ℤ) = a % (n' : ℤ) := by
  have hn : (0:ℤ) < (n' : ℤ) := by exact_mod_cast NeZero.pos n'
  have h0 := Int.emod_nonneg a hn.ne'
  have h1 := Int.emod_lt_of_pos a hn
  have h2 : (a % (n':ℤ)).toNat < n' := (Int.toNat_lt h0).mpr h1
  show (((a % (n' : ℤ)).toNat % n' : ℕ) : ℤ) = _
  rw [Nat.mod_eq_of_lt h2, Int.toNat_of_nonneg h0]

/- English proof (translation)
Establish `h : Even ((posOf n' a).val : ℤ)`. Rewrite using `[residue_position_val, Int.emod_def]`. Conclude with `ha.sub (((Int.even_coe_nat n').mpr hn).mul_right _)`. Conclude with `(Int.even_coe_nat _).mp h`.
-/
theorem position_of_even_is_even (hn : Even n') {a : ℤ} (ha : Even a) : Even (posOf n' a).val := by
  have h : Even ((posOf n' a).val : ℤ) := by
    rw [residue_position_val, Int.emod_def]
    exact ha.sub (((Int.even_coe_nat n').mpr hn).mul_right _)
  exact (Int.even_coe_nat _).mp h

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Establish `h` using `residue_position_val (n' := n') (s.val : ℤ)`. Rewrite `h` using `[Int.emod_eq_of_lt (by positivity) (by exact_mod_cast s.isLt)]`. Conclude with `h` after adjusting the coercions.
-/
theorem residue_position_of_nat (s : Fin n') : posOf n' (s.val : ℤ) = s := by
  apply Fin.ext
  have h := residue_position_val (n' := n') (s.val : ℤ)
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast s.isLt)] at h
  exact_mod_cast h

end B3pos

section B3norm

variable {n' k : ℕ}

def normalVariableWeight (n' k r : ℕ) : TV n' k → ℕ := fun v => if IsNormal r v then 1 else 0

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply]`. Unfold `normDeg Finsupp.sum normalVariableWeight`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases h : IsNormal r v <;> simp [h]`.
-/
theorem weight_eq_normal_degree (r : ℕ) (m : TV n' k →₀ ℕ) : Finsupp.weight (normalVariableWeight n' k r) m = normDeg r m := by
  rw [Finsupp.weight_apply]
  unfold normDeg Finsupp.sum normalVariableWeight
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : IsNormal r v <;> simp [h]

/- English proof (translation)
Introduce `d hd`. Rewrite using `[weight_eq_normal_degree]`. Unfold `normDeg`. Use `Finset.sum_eq_zero fun v hv => ?_` and prove the remaining obligations. Establish `hv' : v ∈ h.vars` using `(mem_vars_iff_mem_support v).mpr ⟨d, mem_support_iff.mpr hd, hv⟩`.

Establish `hT : IsT r v` using `(mem_supported.mp hh) (Finset.mem_coe.mpr hv')`. Establish `: ¬ IsNormal r v`. Unfold `IsNormal`. Rewrite using `[if_pos hT.1]`. Conclude with `Nat.not_le.mpr hT.2`.

Rewrite using `[if_neg this]`.
-/
theorem weighted_homog_zero_of_inT {R : Type*} [CommRing R] (r : ℕ) (h : MvPolynomial (TV n' k) R)
    (hh : h ∈ supported R {v : TV n' k | IsT r v}) : IsWeightedHomogeneous (normalVariableWeight n' k r) h 0 := by
  intro d hd
  rw [weight_eq_normal_degree]
  unfold normDeg
  refine Finset.sum_eq_zero fun v hv => ?_
  have hv' : v ∈ h.vars := (mem_vars_iff_mem_support v).mpr ⟨d, mem_support_iff.mpr hd, hv⟩
  have hT : IsT r v := (mem_supported.mp hh) (Finset.mem_coe.mpr hv')
  have : ¬ IsNormal r v := by
    unfold IsNormal
    rw [if_pos hT.1]
    exact Nat.not_le.mpr hT.2
  rw [if_neg this]

/- English proof (translation)
Introduce `m hm`. Rewrite using `[← weight_eq_normal_degree]`. Apply `hP` to reduce the goal to its premises. Introduce `h0`. Apply `mem_support_iff.mp hm` to reduce the goal to its premises.

Rewrite using `[coeff_C_mul, coeff_map, h0, map_zero, mul_zero]`.
-/
theorem leading_part_normal_degree {O : Type} [CommRing O] [IsDomain O] (r o : ℕ) (a : KK O) (P : MvPolynomial (TV n' k) O)
    (hP : IsWeightedHomogeneous (normalVariableWeight n' k r) P o) :
    ∀ m ∈ (C a * MvPolynomial.map (algebraMap O (KK O)) P).support, normDeg r m = o := by
  intro m hm
  rw [← weight_eq_normal_degree]
  apply hP
  intro h0
  apply mem_support_iff.mp hm
  rw [coeff_C_mul, coeff_map, h0, map_zero, mul_zero]

/- English proof (translation)
Introduce `m` and use `⟨coeff m P, by rw [coeff_map, coeff_C_mul]⟩`.
-/
theorem uniformiser_power_leading_mem_order {O : Type} [CommRing O] [IsDomain O] (w : O) (j : ℕ) (P : MvPolynomial (TV n' k) O) :
    InWj w (MvPolynomial.map (algebraMap O (KK O)) (C (w ^ j) * P)) j := fun m =>
  ⟨coeff m P, by rw [coeff_map, coeff_C_mul]⟩

/- English proof (translation)
Introduce `m` and use `⟨coeff m P, by rw [coeff_map]⟩`.
-/
theorem integral_map_mem_integral {O : Type} [CommRing O] [IsDomain O] (P : MvPolynomial (TV n' k) O) :
    InA (MvPolynomial.map (algebraMap O (KK O)) P) := fun m => ⟨coeff m P, by rw [coeff_map]⟩

/- English proof (translation)
The claim follows from `mem_supported.mpr (subset_trans (Finset.coe_subset.mpr (vars_map _ _)) (mem_supported.mp h))`.
-/
theorem map_supported_fraction_field {O : Type} [CommRing O] [IsDomain O] (s : Set (TV n' k)) (P : MvPolynomial (TV n' k) O)
    (h : P ∈ supported O s) : MvPolynomial.map (algebraMap O (KK O)) P ∈ supported (KK O) s :=
  mem_supported.mpr (subset_trans (Finset.coe_subset.mpr (vars_map _ _)) (mem_supported.mp h))

end B3norm

section B3main

variable {p n' r k : ℕ} [Fact p.Prime] [NeZero n'] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p n') O]

/- English proof (translation)
Unfold `IsNormal`. Simplify using `only [hE, if_true]`.
-/
theorem normal_variable_iff_even_index {s' : Fin n'} (hE : Even s'.val) (c : Fin k) : IsNormal r ((s', c) : TV n' k) ↔ r ≤ c.val := by
  unfold IsNormal
  simp only [hE, if_true]

/- English proof (translation)
Unfold `IsNormal`. Simplify using `only [hE, if_false]`.
-/
theorem normal_variable_iff_odd_index {s' : Fin n'} (hE : ¬ Even s'.val) (c : Fin k) :
    IsNormal r ((s', c) : TV n' k) ↔ c.val < r := by
  unfold IsNormal
  simp only [hE, if_false]

def rowPowerExponent (p : ℕ) (Fr : Frames n' r) (s : ℤ) (l : ℕ) : ℕ := p ^ (s - Arow Fr s l).toNat

def RowsEvenTopsBefore (Fr : Frames n' r) (s : ℤ) : Prop :=
  ∀ l < r, Even (Arow Fr s l) ∧ posOf n' (Arow Fr s l) ∈ Fr.TT ∧ Arow Fr s l < s

/- English proof (translation)
Unfold `rowPowerExponent`. Establish `h1 : 1 ≤ (s - Arow Fr s l).toNat` using `by omega`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem two_le_rowPowerExponent (hp : 2 ≤ p) (Fr : Frames n' r) (s : ℤ) (l : ℕ) (h : Arow Fr s l < s) : 2 ≤ rowPowerExponent p Fr s l := by
  unfold rowPowerExponent
  have h1 : 1 ≤ (s - Arow Fr s l).toNat := by omega
  calc 2 ≤ p := hp
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) h1

def firstKeyMinor (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF p n') O] (Fr : Frames n' r)
    (hrk : r ≤ k) (g : Matrix (Fin k) (Fin k) (WF p n')) (s : ℤ) (c : Fin k) : MvPolynomial (TV n' k) (KK O) :=
  (Formalism.CountingSumsFrames.borderedMatrix r (fun i => xg p n' O n' g s (Fin.castLE hrk i)) (xg p n' O n' g s c)
    (Matrix.of fun l i : Fin r => xg p n' O n' g (Arow Fr s l.val) (Fin.castLE hrk i) ^ rowPowerExponent p Fr s l.val)
    (fun l => xg p n' O n' g (Arow Fr s l.val) c ^ rowPowerExponent p Fr s l.val)).det

def pairingKey (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF p n') O] (Fr : Frames n' r)
    (g : Matrix (Fin k) (Fin k) (WF p n')) (s : ℤ) (l : Fin r) : MvPolynomial (TV n' k) (KK O) :=
  ∑ c : Fin k, xg p n' O n' g (Arow Fr s l.val) c ^ rowPowerExponent p Fr s l.val * yg p n' O n' g s c

def topPairingMatrix (p : ℕ) (O : Type) [CommRing O] (Fr : Frames n' r) (hrk : r ≤ k) (s : ℤ) :
    Matrix (Fin r) (Fin r) (MvPolynomial (TV n' k) O) :=
  Matrix.of fun l i : Fin r => X (posOf n' (Arow Fr s l.val), Fin.castLE hrk i) ^ rowPowerExponent p Fr s l.val

def firstKeyLeading (p : ℕ) (w : O) (Fr : Frames n' r) (hrk : r ≤ k) (s : ℤ) (c : Fin k) :
    MvPolynomial (TV n' k) (KK O) :=
  C (algebraMap O (KK O) w) *
    MvPolynomial.map (algebraMap O (KK O)) ((-1) ^ r * X (posOf n' s, c) * (topPairingMatrix p O Fr hrk s).det)

def pairingKeyLeadingPart (p : ℕ) (w : O) (Fr : Frames n' r) (hrk : r ≤ k) (s : ℤ) (l : Fin r) :
    MvPolynomial (TV n' k) (KK O) :=
  C (algebraMap O (KK O) w) * MvPolynomial.map (algebraMap O (KK O))
    (Matrix.mulVec (topPairingMatrix p O Fr hrk s) (fun a : Fin r => X (posOf n' s, Fin.castLE hrk a)) l)

/- English proof (translation)
Rewrite using `[subst_xg w r hg hn a ha]`. Unfold `newVar`. Rewrite using `[if_neg ((normal_variable_iff_even_index ((posOf_even hn a).2 ha) (Fin.castLE hrk i)).not.mpr (Nat.not_le.mpr i.isLt))]`.
-/
theorem substitute_primal_top_variable (w : O) (hrk : r ≤ k) {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (hn : Even n') (a : ℤ)
    (ha : Even a) (i : Fin r) : subst p n' O w n' r g (xg p n' O n' g a (Fin.castLE hrk i)) =
      X (posOf n' a, Fin.castLE hrk i) := by
  rw [subst_xg w r hg hn a ha]
  unfold newVar
  rw [if_neg ((normal_variable_iff_even_index ((posOf_even hn a).2 ha) (Fin.castLE hrk i)).not.mpr (Nat.not_le.mpr i.isLt))]

/- English proof (translation)
Rewrite using `[subst_xg w r hg hn a ha]`. Unfold `newVar`. Rewrite using `[if_pos ((normal_variable_iff_even_index ((posOf_even hn a).2 ha) _).mpr hc)]`.
-/
theorem substitute_even_normal_variable (w : O) {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (hn : Even n') (a : ℤ)
    (ha : Even a) (c : Fin k) (hc : r ≤ c.val) : subst p n' O w n' r g (xg p n' O n' g a c) =
      C (algebraMap O (KK O) w) * X (posOf n' a, c) := by
  rw [subst_xg w r hg hn a ha]
  unfold newVar
  rw [if_pos ((normal_variable_iff_even_index ((posOf_even hn a).2 ha) _).mpr hc)]

/- English proof (translation)
Rewrite using `[subst_yg w r hg hn a ha]`. Unfold `newVar`. Rewrite using `[if_pos ((normal_variable_iff_odd_index (fun h => ha ((posOf_even hn a).1 h)) _).mpr hc)]`.
-/
theorem subst_odd_row_eq (w : O) {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (hn : Even n') (a : ℤ)
    (ha : ¬ Even a) (c : Fin k) (hc : c.val < r) : subst p n' O w n' r g (yg p n' O n' g a c) =
      C (algebraMap O (KK O) w) * X (posOf n' a, c) := by
  rw [subst_yg w r hg hn a ha]
  unfold newVar
  rw [if_pos ((normal_variable_iff_odd_index (fun h => ha ((posOf_even hn a).1 h)) _).mpr hc)]

/- English proof (translation)
Rewrite using `[subst_yg w r hg hn a ha]`. Unfold `newVar`. Rewrite using `[if_neg ((normal_variable_iff_odd_index (fun h => ha ((posOf_even hn a).1 h)) _).not.mpr hc)]`.
-/
theorem substitute_dual_odd_variable (w : O) {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (hn : Even n') (a : ℤ)
    (ha : ¬ Even a) (c : Fin k) (hc : ¬ c.val < r) : subst p n' O w n' r g (yg p n' O n' g a c) =
      X (posOf n' a, c) := by
  rw [subst_yg w r hg hn a ha]
  unfold newVar
  rw [if_neg ((normal_variable_iff_odd_index (fun h => ha ((posOf_even hn a).1 h)) _).not.mpr hc)]

/- English proof (translation)
Substitute `h1 h2 h3 h4` using the available equality. Both sides reduce to the same expression.
-/
theorem keyMatrix_congr {R : Type} [CommRing R] {r : ℕ} {ts ts' : Fin r → R} {u u' : R}
    {T T' : Matrix (Fin r) (Fin r) R} {b b' : Fin r → R} (h1 : ts = ts') (h2 : u = u') (h3 : T = T') (h4 : b = b') :
    Formalism.CountingSumsFrames.borderedMatrix r ts u T b = Formalism.CountingSumsFrames.borderedMatrix r ts' u' T' b' := by
  subst h1 h2 h3 h4; rfl

/- English proof (translation)
The claim follows from `keyMatrix_det_map (f : R →+* R') r ts u T b`.
-/
theorem alg_hom_minor_matrix_det {K R R' : Type} [CommRing K] [CommRing R] [CommRing R'] [Algebra K R] [Algebra K R']
    (f : R →ₐ[K] R') (r : ℕ) (ts : Fin r → R) (u : R) (T : Matrix (Fin r) (Fin r) R) (b : Fin r → R) :
    f (Formalism.CountingSumsFrames.borderedMatrix r ts u T b).det =
      (Formalism.CountingSumsFrames.borderedMatrix r (fun i => f (ts i)) (f u) (T.map f) (fun l => f (b l))).det :=
  keyMatrix_det_map (f : R →+* R') r ts u T b

/- English proof (translation)
Unfold `Dtop`. Rewrite using `[AlgHom.map_det, RingHom.map_det]`. Use `congrArg Matrix.det (Matrix.ext fun l i => ?_)` and prove the remaining obligations. Use `show subst p n' O w n' r g (xg p n' O n' g (Arow Fr s l.val) (Fin.castLE hrk i) ^ rowPowerExponent p Fr s l.val) = MvPolynomial.map (algebraMap O (KK O)) (X (posOf n' (Arow Fr s l.val), Fin.castLE hrk i) ^ rowPowerExponent p Fr s l.val)`. Rewrite using `[map_pow, map_pow, substitute_primal_top_variable w hrk hg hn _ (hA l.val l.isLt).1, MvPolynomial.map_X]`.
-/
theorem subst_top_determinant (w : O) (Fr : Frames n' r) (hrk : r ≤ k) {g : Matrix (Fin k) (Fin k) (WF p n')}
    (hg : IsGLW g) (hn : Even n') (s : ℤ) (hA : RowsEvenTopsBefore Fr s) :
    subst p n' O w n' r g (Dtop p n' O Fr hrk g s) =
      MvPolynomial.map (algebraMap O (KK O)) (topPairingMatrix p O Fr hrk s).det := by
  unfold Dtop
  rw [AlgHom.map_det, RingHom.map_det]
  refine congrArg Matrix.det (Matrix.ext fun l i => ?_)
  show subst p n' O w n' r g (xg p n' O n' g (Arow Fr s l.val) (Fin.castLE hrk i) ^ rowPowerExponent p Fr s l.val) =
    MvPolynomial.map (algebraMap O (KK O)) (X (posOf n' (Arow Fr s l.val), Fin.castLE hrk i) ^ rowPowerExponent p Fr s l.val)
  rw [map_pow, map_pow, substitute_primal_top_variable w hrk hg hn _ (hA l.val l.isLt).1, MvPolynomial.map_X]

/- English proof (translation)
Unfold `firstKeyMinor`. Rewrite using `[alg_hom_minor_matrix_det, keyMatrix_det_map]`. Use `congrArg Matrix.det (keyMatrix_congr (funext fun i => ?_) ?_ (Matrix.ext fun l i => ?_) (funext fun l => ?_))` and prove the remaining obligations. Rewrite using `[substitute_primal_top_variable w hrk hg hn s hs, MvPolynomial.map_X]`. Rewrite using `[substitute_even_normal_variable w hg hn s hs c hc, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]`.

Use `show subst p n' O w n' r g (xg p n' O n' g (Arow Fr s l.val) (Fin.castLE hrk i) ^ rowPowerExponent p Fr s l.val) = MvPolynomial.map (algebraMap O (KK O)) (X (posOf n' (Arow Fr s l.val), Fin.castLE hrk i) ^ rowPowerExponent p Fr s l.val)`. Rewrite using `[map_pow, map_pow, substitute_primal_top_variable w hrk hg hn _ (hA l.val l.isLt).1, MvPolynomial.map_X]`. Rewrite using `[map_pow, map_pow, substitute_even_normal_variable w hg hn _ (hA l.val l.isLt).1 c hc, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]`.
-/
theorem subst_first_key_eq (w : O) (Fr : Frames n' r) (hrk : r ≤ k) {g : Matrix (Fin k) (Fin k) (WF p n')}
    (hg : IsGLW g) (hn : Even n') (s : ℤ) (hs : Even s) (hA : RowsEvenTopsBefore Fr s) (c : Fin k) (hc : r ≤ c.val) :
    subst p n' O w n' r g (firstKeyMinor p O Fr hrk g s c) = MvPolynomial.map (algebraMap O (KK O))
      (Formalism.CountingSumsFrames.borderedMatrix r (fun i => X (posOf n' s, Fin.castLE hrk i)) (C w * X (posOf n' s, c)) (topPairingMatrix p O Fr hrk s)
        (fun l => (C w * X (posOf n' (Arow Fr s l.val), c)) ^ rowPowerExponent p Fr s l.val)).det := by
  unfold firstKeyMinor
  rw [alg_hom_minor_matrix_det, keyMatrix_det_map]
  refine congrArg Matrix.det (keyMatrix_congr (funext fun i => ?_) ?_ (Matrix.ext fun l i => ?_) (funext fun l => ?_))
  · rw [substitute_primal_top_variable w hrk hg hn s hs, MvPolynomial.map_X]
  · rw [substitute_even_normal_variable w hg hn s hs c hc, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
  · show subst p n' O w n' r g (xg p n' O n' g (Arow Fr s l.val) (Fin.castLE hrk i) ^ rowPowerExponent p Fr s l.val) =
      MvPolynomial.map (algebraMap O (KK O)) (X (posOf n' (Arow Fr s l.val), Fin.castLE hrk i) ^ rowPowerExponent p Fr s l.val)
    rw [map_pow, map_pow, substitute_primal_top_variable w hrk hg hn _ (hA l.val l.isLt).1, MvPolynomial.map_X]
  · rw [map_pow, map_pow, substitute_even_normal_variable w hg hn _ (hA l.val l.isLt).1 c hc, map_mul, MvPolynomial.map_C,
      MvPolynomial.map_X]

def twistedRowIntegral (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF p n') O]
    (g : Matrix (Fin k) (Fin k) (WF p n')) (a : ℤ) (b : Fin k) : MvPolynomial (TV n' k) O :=
  ∑ c : Fin k, X (posOf n' a, c) * C (algebraMap (WF p n') O (sigPow p n' a (g c b)))

/- English proof (translation)
Unfold `twistedRowIntegral xg`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, MvPolynomial.map_X, MvPolynomial.map_C]`. Both sides reduce to the same expression.
-/
theorem map_integral_primal_variable (g : Matrix (Fin k) (Fin k) (WF p n')) (a : ℤ) (b : Fin k) :
    MvPolynomial.map (algebraMap O (KK O)) (twistedRowIntegral p O g a b) = xg p n' O n' g a b := by
  unfold twistedRowIntegral xg
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, MvPolynomial.map_X, MvPolynomial.map_C]
  rfl

/- English proof (translation)
Rewrite using `[sigMat_eq_map, sigMat_eq_map]`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[← Matrix.map_mul, Matrix.nonsing_inv_mul _ hg, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem sigmaMatrix_inv_at_shift {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (a : ℤ) :
    (sigMat p n' O g a)⁻¹ = sigMat p n' O g⁻¹ a := by
  rw [sigMat_eq_map, sigMat_eq_map]
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hg, Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
Unfold `yg`. Rewrite using `[map_sum, sigmaMatrix_inv_at_shift hg]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, MvPolynomial.map_X, MvPolynomial.map_C]`. Both sides reduce to the same expression.
-/
theorem map_twisted_inverse_row {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (a : ℤ) (b : Fin k) :
    MvPolynomial.map (algebraMap O (KK O))
      (∑ c : Fin k, X (posOf n' a, c) * C (algebraMap (WF p n') O (sigPow p n' a (g⁻¹ b c)))) =
      yg p n' O n' g a b := by
  unfold yg
  rw [map_sum, sigmaMatrix_inv_at_shift hg]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, MvPolynomial.map_X, MvPolynomial.map_C]
  rfl

/- English proof (translation)
Establish `h : firstKeyMinor p O Fr hrk g s c = MvPolynomial.map (algebraMap O (KK O)) (Formalism.CountingSumsFrames.borderedMatrix r (fun i => twistedRowIntegral p O g s (Fin.castLE hrk i)) (twistedRowIntegral p O g s c) (Matrix.of fun l i : Fin r => twistedRowIntegral p O g (Arow Fr s l.v …`. Rewrite using `[keyMatrix_det_map]`. Unfold `firstKeyMinor`. Use `congrArg Matrix.det (keyMatrix_congr (funext fun i => (map_integral_primal_variable g s _).symm) (map_integral_primal_variable g s c).symm (Matrix.ext fun l i => ?_) (funext fun l => ?_))` and prove the remaining obligations. Use `show _ = MvPolynomial.map (algebraMap O (KK O)) (twistedRowIntegral p O g (Arow Fr s l.val) (Fin.castLE hrk i) ^ rowPowerExponent p Fr s l.val)`.

Rewrite using `[map_pow, map_integral_primal_variable]`. Both sides reduce to the same expression. Rewrite using `[map_pow, map_integral_primal_variable]`. Rewrite using `[h]`. Conclude with `integral_map_mem_integral _`.
-/
theorem first_key_integral (Fr : Frames n' r) (hrk : r ≤ k) (g : Matrix (Fin k) (Fin k) (WF p n')) (s : ℤ) (c : Fin k) :
    InA (firstKeyMinor p O Fr hrk g s c) := by
  have h : firstKeyMinor p O Fr hrk g s c = MvPolynomial.map (algebraMap O (KK O))
      (Formalism.CountingSumsFrames.borderedMatrix r (fun i => twistedRowIntegral p O g s (Fin.castLE hrk i)) (twistedRowIntegral p O g s c)
        (Matrix.of fun l i : Fin r => twistedRowIntegral p O g (Arow Fr s l.val) (Fin.castLE hrk i) ^ rowPowerExponent p Fr s l.val)
        (fun l => twistedRowIntegral p O g (Arow Fr s l.val) c ^ rowPowerExponent p Fr s l.val)).det := by
    rw [keyMatrix_det_map]
    unfold firstKeyMinor
    refine congrArg Matrix.det (keyMatrix_congr (funext fun i => (map_integral_primal_variable g s _).symm) (map_integral_primal_variable g s c).symm
      (Matrix.ext fun l i => ?_) (funext fun l => ?_))
    · show _ = MvPolynomial.map (algebraMap O (KK O))
        (twistedRowIntegral p O g (Arow Fr s l.val) (Fin.castLE hrk i) ^ rowPowerExponent p Fr s l.val)
      rw [map_pow, map_integral_primal_variable]
      rfl
    · rw [map_pow, map_integral_primal_variable]
  rw [h]
  exact integral_map_mem_integral _

/- English proof (translation)
Establish `h : pairingKey p O Fr g s l = MvPolynomial.map (algebraMap O (KK O)) (∑ c : Fin k, twistedRowIntegral p O g (Arow Fr s l.val) c ^ rowPowerExponent p Fr s l.val * (∑ c' : Fin k, X (posOf n' s, c') * C (algebraMap (WF p n') O (sigPow p n' s (g⁻¹ c c')))))`. Unfold `pairingKey`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, map_integral_primal_variable, map_twisted_inverse_row hg]`.

Rewrite using `[h]`. Conclude with `integral_map_mem_integral _`.
-/
theorem third_key_integral (Fr : Frames n' r) {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (s : ℤ) (l : Fin r) :
    InA (pairingKey p O Fr g s l) := by
  have h : pairingKey p O Fr g s l = MvPolynomial.map (algebraMap O (KK O))
      (∑ c : Fin k, twistedRowIntegral p O g (Arow Fr s l.val) c ^ rowPowerExponent p Fr s l.val *
        (∑ c' : Fin k, X (posOf n' s, c') * C (algebraMap (WF p n') O (sigPow p n' s (g⁻¹ c c'))))) := by
    unfold pairingKey
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, map_pow, map_integral_primal_variable, map_twisted_inverse_row hg]
  rw [h]
  exact integral_map_mem_integral _

/- English proof (translation)
The claim follows from `(supported O St).pow_mem (X_mem_supported.mpr (h l i)) _`.
-/
theorem row_power_mem_supported (Fr : Frames n' r) (hrk : r ≤ k) (s : ℤ) (St : Set (TV n' k))
    (h : ∀ (l i : Fin r), (posOf n' (Arow Fr s l.val), Fin.castLE hrk i) ∈ St) (l i : Fin r) :
    topPairingMatrix p O Fr hrk s l i ∈ supported O St :=
  (supported O St).pow_mem (X_mem_supported.mpr (h l i)) _

/- English proof (translation)
Introduce `m` and use `⟨coeff m P, by rw [coeff_C_mul, coeff_map, pow_one, map_mul]⟩`.
-/
theorem inWPow_one_of_C_w_mul (w : O) (P : MvPolynomial (TV n' k) O) :
    InWj w (C (algebraMap O (KK O) w) * MvPolynomial.map (algebraMap O (KK O)) P) 1 := fun m =>
  ⟨coeff m P, by rw [coeff_C_mul, coeff_map, pow_one, map_mul]⟩

/- English proof (translation)
Rewrite using `[mul_pow, ← C_pow, ← mul_assoc, ← C_mul, ← pow_add, Nat.add_sub_cancel' hP]`.
-/
theorem uniformiser_variable_pow_split (w : O) (v : TV n' k) (P : ℕ) (hP : 2 ≤ P) :
    (C w * X v : MvPolynomial (TV n' k) O) ^ P = C (w ^ 2) * (C (w ^ (P - 2)) * X v ^ P) := by
  rw [mul_pow, ← C_pow, ← mul_assoc, ← C_mul, ← pow_add, Nat.add_sub_cancel' hP]

/- English proof (translation)
Take `⟨cc, hcc⟩` from `Formalism.CountingSumsFrames.Top.borderedDetLinear (MvPolynomial (TV n' k) O) r (fun i => X (posOf n' s, Fin.castLE hrk i)) (topPairingMatrix p O Fr hrk s)`. Rewrite using `[subst_first_key_eq w Fr hrk hg hn s hs hA c hc, hcc, map_add]`. Establish `e1 : MvPolynomial.map (algebraMap O (KK O)) ((-1) ^ r * (C w * X (posOf n' s, c)) * (topPairingMatrix p O Fr hrk s).det) = firstKeyLeading p w Fr hrk s c`. Unfold `firstKeyLeading`. Simplify using `only [map_mul, MvPolynomial.map_C]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, add_sub_cancel_left]`. Establish `e2 : ∑ l : Fin r, (C w * X (posOf n' (Arow Fr s l.val), c)) ^ rowPowerExponent p Fr s l.val * cc l = C (w ^ 2) * ∑ l : Fin r, C (w ^ (rowPowerExponent p Fr s l.val - 2)) * X (posOf n' (Arow Fr s l.val), c) ^ rowPowerExponent p Fr s l.val * cc l`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[uniformiser_variable_pow_split w _ _ (two_le_rowPowerExponent hp Fr s l.val (hA l.val l.isLt).2.2)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Conclude with `uniformiser_power_leading_mem_order w 2 _`.
-/
theorem minor_tail_mem_order_two (hp : 2 ≤ p) (w : O) (Fr : Frames n' r) (hrk : r ≤ k) {g : Matrix (Fin k) (Fin k) (WF p n')}
    (hg : IsGLW g) (hn : Even n') (s : ℤ) (hs : Even s) (hA : RowsEvenTopsBefore Fr s) (c : Fin k) (hc : r ≤ c.val) :
    InWj w (subst p n' O w n' r g (firstKeyMinor p O Fr hrk g s c) - firstKeyLeading p w Fr hrk s c) 2 := by
  obtain ⟨cc, hcc⟩ := Formalism.CountingSumsFrames.Top.borderedDetLinear (MvPolynomial (TV n' k) O) r
    (fun i => X (posOf n' s, Fin.castLE hrk i)) (topPairingMatrix p O Fr hrk s)
  rw [subst_first_key_eq w Fr hrk hg hn s hs hA c hc, hcc, map_add]
  have e1 : MvPolynomial.map (algebraMap O (KK O))
      ((-1) ^ r * (C w * X (posOf n' s, c)) * (topPairingMatrix p O Fr hrk s).det) = firstKeyLeading p w Fr hrk s c := by
    unfold firstKeyLeading
    simp only [map_mul, MvPolynomial.map_C]
    ring
  rw [e1, add_sub_cancel_left]
  have e2 : ∑ l : Fin r, (C w * X (posOf n' (Arow Fr s l.val), c)) ^ rowPowerExponent p Fr s l.val * cc l =
      C (w ^ 2) * ∑ l : Fin r, C (w ^ (rowPowerExponent p Fr s l.val - 2)) *
        X (posOf n' (Arow Fr s l.val), c) ^ rowPowerExponent p Fr s l.val * cc l := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [uniformiser_variable_pow_split w _ _ (two_le_rowPowerExponent hp Fr s l.val (hA l.val l.isLt).2.2)]
    ring
  rw [e2]
  exact uniformiser_power_leading_mem_order w 2 _

/- English proof (translation)
Establish `e0 : pairingKeyLeadingPart p w Fr hrk s l = MvPolynomial.map (algebraMap O (KK O)) (∑ c : Fin k, if c.val < r then C w * (X (posOf n' (Arow Fr s l.val), c) ^ rowPowerExponent p Fr s l.val * X (posOf n' s, c)) else 0)`. Rewrite using `[sum_ite_lt_castLE r k hrk (fun c => C w * (X (posOf n' (Arow Fr s l.val), c) ^ rowPowerExponent p Fr s l.val * X (posOf n' s, c))), ← Finset.mul_sum, map_mul, MvPolynomial.map_C]`. Both sides reduce to the same expression. Rewrite using `[e0, ← map_add, Finset.mul_sum, ← Finset.sum_add_distrib, map_sum]`. Unfold `pairingKey`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow]`. Distinguish the cases in `hc : c.val < r`. Establish `hc' : c = Fin.castLE hrk ⟨c.val, hc⟩` using `rfl`.

Rewrite using `[if_pos hc, if_pos hc, mul_zero, add_zero, subst_odd_row_eq w hg hn s hs c hc]`. Use `conv_lhs => rw [hc', substitute_primal_top_variable w hrk hg hn _ (hA l.val l.isLt).1]`. Simplify using `only [map_mul, map_pow, MvPolynomial.map_C, MvPolynomial.map_X]`. Rewrite using `[← hc']`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[if_neg hc, if_neg hc, zero_add, substitute_dual_odd_variable w hg hn s hs c hc, substitute_even_normal_variable w hg hn _ (hA l.val l.isLt).1 c (Nat.le_of_not_lt hc)]`. Establish `e3 : (C (w ^ 2) * (C (w ^ (rowPowerExponent p Fr s l.val - 2)) * X (posOf n' (Arow Fr s l.val), c) ^ rowPowerExponent p Fr s l.val * X (posOf n' s, c)) : MvPolynomial (TV n' k) O) = (C w * X (posOf n' (Arow Fr s l.val), c)) ^ rowPowerExponent p Fr s l.val * X (posOf n' s, c)`. Rewrite using `[uniformiser_variable_pow_split w _ _ (two_le_rowPowerExponent hp Fr s l.val (hA l.val l.isLt).2.2)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e3]`.

Simplify using `only [map_mul, map_pow, MvPolynomial.map_C, MvPolynomial.map_X]`.
-/
theorem substitute_pairing_key_leading_part (hp : 2 ≤ p) (w : O) (Fr : Frames n' r) (hrk : r ≤ k) {g : Matrix (Fin k) (Fin k) (WF p n')}
    (hg : IsGLW g) (hn : Even n') (s : ℤ) (hs : ¬ Even s) (hA : RowsEvenTopsBefore Fr s) (l : Fin r) :
    subst p n' O w n' r g (pairingKey p O Fr g s l) = pairingKeyLeadingPart p w Fr hrk s l +
      MvPolynomial.map (algebraMap O (KK O)) (C (w ^ 2) * ∑ c : Fin k, if c.val < r then 0 else
        C (w ^ (rowPowerExponent p Fr s l.val - 2)) * X (posOf n' (Arow Fr s l.val), c) ^ rowPowerExponent p Fr s l.val *
          X (posOf n' s, c)) := by
  have e0 : pairingKeyLeadingPart p w Fr hrk s l = MvPolynomial.map (algebraMap O (KK O)) (∑ c : Fin k, if c.val < r then
      C w * (X (posOf n' (Arow Fr s l.val), c) ^ rowPowerExponent p Fr s l.val * X (posOf n' s, c)) else 0) := by
    rw [sum_ite_lt_castLE r k hrk (fun c => C w * (X (posOf n' (Arow Fr s l.val), c) ^ rowPowerExponent p Fr s l.val *
      X (posOf n' s, c))), ← Finset.mul_sum, map_mul, MvPolynomial.map_C]
    rfl
  rw [e0, ← map_add, Finset.mul_sum, ← Finset.sum_add_distrib, map_sum]
  unfold pairingKey
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, map_pow]
  by_cases hc : c.val < r
  · have hc' : c = Fin.castLE hrk ⟨c.val, hc⟩ := rfl
    rw [if_pos hc, if_pos hc, mul_zero, add_zero, subst_odd_row_eq w hg hn s hs c hc]
    conv_lhs => rw [hc', substitute_primal_top_variable w hrk hg hn _ (hA l.val l.isLt).1]
    simp only [map_mul, map_pow, MvPolynomial.map_C, MvPolynomial.map_X]
    rw [← hc']
    ring
  · rw [if_neg hc, if_neg hc, zero_add, substitute_dual_odd_variable w hg hn s hs c hc,
      substitute_even_normal_variable w hg hn _ (hA l.val l.isLt).1 c (Nat.le_of_not_lt hc)]
    have e3 : (C (w ^ 2) * (C (w ^ (rowPowerExponent p Fr s l.val - 2)) * X (posOf n' (Arow Fr s l.val), c) ^ rowPowerExponent p Fr s l.val *
        X (posOf n' s, c)) : MvPolynomial (TV n' k) O) =
        (C w * X (posOf n' (Arow Fr s l.val), c)) ^ rowPowerExponent p Fr s l.val * X (posOf n' s, c) := by
      rw [uniformiser_variable_pow_split w _ _ (two_le_rowPowerExponent hp Fr s l.val (hA l.val l.isLt).2.2)]
      ring
    rw [e3]
    simp only [map_mul, map_pow, MvPolynomial.map_C, MvPolynomial.map_X]

end B3main

section B3keys

variable {p n' r k : ℕ} [Fact p.Prime] [NeZero n'] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p n') O]

/- English proof (translation)
Introduce `_ hv` and use `(mem_supported.mp hh) (Finset.mem_coe.mpr hv)`.
-/
theorem inT_of_mem_supported {h : MvPolynomial (TV n' k) O} (hh : h ∈ supported O {v : TV n' k | IsT r v}) : InT r h :=
  fun _ hv => (mem_supported.mp hh) (Finset.mem_coe.mpr hv)

/- English proof (translation)
Introduce `_ hv` and use `(mem_supported.mp hh) (Finset.mem_coe.mpr hv)`.
-/
theorem onTops_of_supported {R : Type} [CommRing R] (Fr : Frames n' r) {h : MvPolynomial (TV n' k) R}
    (hh : h ∈ supported R {v : TV n' k | v.1 ∈ Fr.TT}) : OnTops Fr h :=
  fun _ hv => (mem_supported.mp hh) (Finset.mem_coe.mpr hv)

/- English proof (translation)
The claim follows from `row_power_mem_supported Fr hrk s {v : TV n' k | IsT r v} (fun l i => (show IsT r (posOf n' (Arow Fr s l.val), Fin.castLE hrk i) from ⟨(posOf_even hn _).2 (hA l.val l.isLt).1, i.isLt⟩)) l i`.
-/
theorem pairing_matrix_supported_tops (Fr : Frames n' r) (hrk : r ≤ k) (hn : Even n') (s : ℤ) (hA : RowsEvenTopsBefore Fr s) (l i : Fin r) :
    topPairingMatrix p O Fr hrk s l i ∈ supported O {v : TV n' k | IsT r v} :=
  row_power_mem_supported Fr hrk s {v : TV n' k | IsT r v} (fun l i => (show IsT r (posOf n' (Arow Fr s l.val), Fin.castLE hrk i) from
    ⟨(posOf_even hn _).2 (hA l.val l.isLt).1, i.isLt⟩)) l i

/- English proof (translation)
The claim follows from `row_power_mem_supported Fr hrk s {v : TV n' k | v.1 ∈ Fr.TT} (fun l _ => (hA l.val l.isLt).2.1) l i`.
-/
theorem row_power_supported_on_tops (Fr : Frames n' r) (hrk : r ≤ k) (s : ℤ) (hA : RowsEvenTopsBefore Fr s) (l i : Fin r) :
    topPairingMatrix p O Fr hrk s l i ∈ supported O {v : TV n' k | v.1 ∈ Fr.TT} :=
  row_power_mem_supported Fr hrk s {v : TV n' k | v.1 ∈ Fr.TT} (fun l _ => (hA l.val l.isLt).2.1) l i

/- English proof (translation)
The claim follows from `Subalgebra.sum_mem _ fun _ _ => Subalgebra.mul_mem _ (X_mem_supported.mpr ha) (Subalgebra.algebraMap_mem _ _)`.
-/
theorem twisted_row_supported_on_tops (Fr : Frames n' r) (g : Matrix (Fin k) (Fin k) (WF p n')) (a : ℤ) (ha : posOf n' a ∈ Fr.TT)
    (b : Fin k) : xg p n' O n' g a b ∈ supported (KK O) {v : TV n' k | v.1 ∈ Fr.TT} :=
  Subalgebra.sum_mem _ fun _ _ => Subalgebra.mul_mem _ (X_mem_supported.mpr ha) (Subalgebra.algebraMap_mem _ _)

/- English proof (translation)
The claim follows from `Subalgebra.sum_mem _ fun _ _ => Subalgebra.mul_mem _ (X_mem_supported.mpr ha) (Subalgebra.algebraMap_mem _ _)`.
-/
theorem twisted_inverse_row_supported_on_tops (Fr : Frames n' r) (g : Matrix (Fin k) (Fin k) (WF p n')) (a : ℤ) (ha : posOf n' a ∈ Fr.TT)
    (b : Fin k) : yg p n' O n' g a b ∈ supported (KK O) {v : TV n' k | v.1 ∈ Fr.TT} :=
  Subalgebra.sum_mem _ fun _ _ => Subalgebra.mul_mem _ (X_mem_supported.mpr ha) (Subalgebra.algebraMap_mem _ _)

/- English proof (translation)
The claim follows from `onTops_of_supported Fr (det_mem_subalgebra_alt _ _ (keyMatrix_mem_subalgebra _ r _ _ _ _ (fun _ => twisted_row_supported_on_tops Fr g s hs _) (twisted_row_supported_on_tops Fr g s hs _) (fun l _ => Subalgebra.pow_mem _ (twisted_row_supported_on_tops Fr g _ (hA l.val l.isLt).2.1 _ …`.
-/
theorem first_key_supported_on_tops (Fr : Frames n' r) (hrk : r ≤ k) (g : Matrix (Fin k) (Fin k) (WF p n')) (s : ℤ)
    (hs : posOf n' s ∈ Fr.TT) (hA : RowsEvenTopsBefore Fr s) (c : Fin k) : OnTops Fr (firstKeyMinor p O Fr hrk g s c) :=
  onTops_of_supported Fr (det_mem_subalgebra_alt _ _ (keyMatrix_mem_subalgebra _ r _ _ _ _ (fun _ => twisted_row_supported_on_tops Fr g s hs _) (twisted_row_supported_on_tops Fr g s hs _)
    (fun l _ => Subalgebra.pow_mem _ (twisted_row_supported_on_tops Fr g _ (hA l.val l.isLt).2.1 _) _)
    (fun l => Subalgebra.pow_mem _ (twisted_row_supported_on_tops Fr g _ (hA l.val l.isLt).2.1 _) _)))

/- English proof (translation)
The claim follows from `onTops_of_supported Fr (Subalgebra.sum_mem _ fun _ _ => Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (twisted_row_supported_on_tops Fr g _ (hA l.val l.isLt).2.1 _) _) (twisted_inverse_row_supported_on_tops Fr g s hs _))`.
-/
theorem pairingKey_on_tops (Fr : Frames n' r) (g : Matrix (Fin k) (Fin k) (WF p n')) (s : ℤ)
    (hs : posOf n' s ∈ Fr.TT) (hA : RowsEvenTopsBefore Fr s) (l : Fin r) : OnTops Fr (pairingKey p O Fr g s l) :=
  onTops_of_supported Fr (Subalgebra.sum_mem _ fun _ _ => Subalgebra.mul_mem _
    (Subalgebra.pow_mem _ (twisted_row_supported_on_tops Fr g _ (hA l.val l.isLt).2.1 _) _) (twisted_inverse_row_supported_on_tops Fr g s hs _))

/- English proof (translation)
The claim follows from `onTops_of_supported Fr (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (map_supported_fraction_field _ _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _) (X_mem_supported.mpr hs)) (det_mem_subalgebra_alt _ _ …`.
-/
theorem first_key_leading_supported_on_tops (w : O) (Fr : Frames n' r) (hrk : r ≤ k) (s : ℤ)
    (hs : posOf n' s ∈ Fr.TT) (hA : RowsEvenTopsBefore Fr s) (c : Fin k) : OnTops Fr (firstKeyLeading p w Fr hrk s c) :=
  onTops_of_supported Fr (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (map_supported_fraction_field _ _
    (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _)
      (X_mem_supported.mpr hs)) (det_mem_subalgebra_alt _ _ (row_power_supported_on_tops Fr hrk s hA)))))

/- English proof (translation)
The claim follows from `onTops_of_supported Fr (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (map_supported_fraction_field _ _ (show (∑ a : Fin r, topPairingMatrix p O Fr hrk s l a * X (posOf n' s, Fin.castLE hrk a)) ∈ supported O {v : TV n' k | v.1 ∈ Fr.TT} from Subalgebra.sum_mem _ fun a _ => …`.
-/
theorem third_key_leading_supported_on_tops (w : O) (Fr : Frames n' r) (hrk : r ≤ k) (s : ℤ)
    (hs : posOf n' s ∈ Fr.TT) (hA : RowsEvenTopsBefore Fr s) (l : Fin r) : OnTops Fr (pairingKeyLeadingPart p w Fr hrk s l) :=
  onTops_of_supported Fr (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (map_supported_fraction_field _ _
    (show (∑ a : Fin r, topPairingMatrix p O Fr hrk s l a * X (posOf n' s, Fin.castLE hrk a)) ∈
        supported O {v : TV n' k | v.1 ∈ Fr.TT} from
      Subalgebra.sum_mem _ fun a _ => Subalgebra.mul_mem _ (row_power_supported_on_tops Fr hrk s hA l a) (X_mem_supported.mpr hs))))

/- English proof (translation)
Use `leading_part_normal_degree r 1 _ _ ?_` and prove the remaining obligations. Establish `hv : normalVariableWeight n' k r (posOf n' s, c) = 1` using `if_pos ((normal_variable_iff_even_index ((posOf_even hn s).2 hs) c).mpr hc)`. Establish `h1 : IsWeightedHomogeneous (normalVariableWeight n' k r) ((-1 : MvPolynomial (TV n' k) O) ^ r) 0`. Establish `: ((-1 : MvPolynomial (TV n' k) O) ^ r) = C ((-1) ^ r)` using `by simp`. Rewrite using `[this]`.

Conclude with `isWeightedHomogeneous_C _ _`. Establish `h2` using `(h1.mul (isWeightedHomogeneous_X O (normalVariableWeight n' k r) (posOf n' s, c))).mul (weighted_homog_zero_of_inT r _ (det_mem_subalgebra_alt _ _ (pairing_matrix_supported_tops (p := p) (O := O) Fr hrk hn s hA)))`. Rewrite `h2` using `[hv]`. Conclude with `h2`.
-/
theorem minor_leading_part_normal_degree (w : O) (Fr : Frames n' r) (hrk : r ≤ k) (hn : Even n') (s : ℤ) (hs : Even s)
    (hA : RowsEvenTopsBefore Fr s) (c : Fin k) (hc : r ≤ c.val) :
    ∀ m ∈ (firstKeyLeading p w Fr hrk s c).support, normDeg r m = 1 := by
  refine leading_part_normal_degree r 1 _ _ ?_
  have hv : normalVariableWeight n' k r (posOf n' s, c) = 1 := if_pos ((normal_variable_iff_even_index ((posOf_even hn s).2 hs) c).mpr hc)
  have h1 : IsWeightedHomogeneous (normalVariableWeight n' k r) ((-1 : MvPolynomial (TV n' k) O) ^ r) 0 := by
    have : ((-1 : MvPolynomial (TV n' k) O) ^ r) = C ((-1) ^ r) := by simp
    rw [this]
    exact isWeightedHomogeneous_C _ _
  have h2 := (h1.mul (isWeightedHomogeneous_X O (normalVariableWeight n' k r) (posOf n' s, c))).mul
    (weighted_homog_zero_of_inT r _ (det_mem_subalgebra_alt _ _ (pairing_matrix_supported_tops (p := p) (O := O) Fr hrk hn s hA)))
  rw [hv] at h2
  exact h2

/- English proof (translation)
Use `leading_part_normal_degree r 1 _ _ ?_` and prove the remaining obligations. Use `IsWeightedHomogeneous.sum _ _ _ fun a _ => ?_` and prove the remaining obligations. Establish `hv : normalVariableWeight n' k r (posOf n' s, Fin.castLE hrk a) = 1` using `if_pos ((normal_variable_iff_odd_index (fun h => hs ((posOf_even hn s).1 h)) (Fin.castLE hrk a)).mpr a.isLt)`. Establish `h2` using `(weighted_homog_zero_of_inT r _ (pairing_matrix_supported_tops (p := p) (O := O) Fr hrk hn s hA l a)).mul (isWeightedHomogeneous_X O (normalVariableWeight n' k r) (posOf n' s, Fin.castLE hrk a))`. Rewrite `h2` using `[hv]`.

Conclude with `h2`.
-/
theorem k3_leading_support_normDeg_eq_one (w : O) (Fr : Frames n' r) (hrk : r ≤ k) (hn : Even n') (s : ℤ) (hs : ¬ Even s)
    (hA : RowsEvenTopsBefore Fr s) (l : Fin r) :
    ∀ m ∈ (pairingKeyLeadingPart p w Fr hrk s l).support, normDeg r m = 1 := by
  refine leading_part_normal_degree r 1 _ _ ?_
  refine IsWeightedHomogeneous.sum _ _ _ fun a _ => ?_
  have hv : normalVariableWeight n' k r (posOf n' s, Fin.castLE hrk a) = 1 :=
    if_pos ((normal_variable_iff_odd_index (fun h => hs ((posOf_even hn s).1 h)) (Fin.castLE hrk a)).mpr a.isLt)
  have h2 := (weighted_homog_zero_of_inT r _ (pairing_matrix_supported_tops (p := p) (O := O) Fr hrk hn s hA l a)).mul
    (isWeightedHomogeneous_X O (normalVariableWeight n' k r) (posOf n' s, Fin.castLE hrk a))
  rw [hv] at h2
  exact h2

/- English proof (translation)
Take the linear combination `(-(x * d * e * e)) * hab + (-(x * d)) * he`.
-/
theorem unit_conjugation_identity {R : Type*} [CommRing R] (a b e x d : R) (hab : a * b = 1) (he : e * e = 1) :
    x * d = e * (a * (b * (e * x * d))) := by
  linear_combination (-(x * d * e * e)) * hab + (-(x * d)) * he

/- English proof (translation)
Take the linear combination `(-(M * A)) * hab`.
-/
theorem mul_eq_of_mul_eq_one_cancel {R : Type*} [CommRing R] (a b M A : R) (hab : a * b = 1) : M * A = A * (a * (b * M)) := by
  linear_combination (-(M * A)) * hab

end B3keys

def RowsEvenTopsInWindow : Prop :=
  ∀ (n' r : ℕ) [NeZero n'] (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ → Even n' → 1 ≤ r →
    ∀ s : ℤ, RowsEvenTopsBefore Fr s

def RowsPairOnPlanes : Prop :=
  ∀ (p n' r k : ℕ) [Fact p.Prime] [NeZero n'] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF p n') O] (S : UniformizedDVR p O), OHyp p n' O S → ∀ hH : CommonHypotheses p n' r k,
  ∀ (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ →
  ∀ g g' : Matrix (Fin k) (Fin k) (WF p n'), IsGLW g → IsGLW g' →
  ∀ s ∈ Fr.TT,
    (Even s.val → ∀ c : Fin k, r ≤ c.val → ordGe p n' O S.w n' r g' (firstKeyMinor p O Fr hH.2.2.1 g (s.val : ℤ) c) 1) ∧
    (¬ Even s.val → ∀ l : Fin r, ordGe p n' O S.w n' r g' (pairingKey p O Fr g (s.val : ℤ) l) 1)

/- English proof (translation)
Introduce `p n' r k _ _ O _ _ _ _ S hO hH Fr L₁ N₁ hV Q hQ g hg s hs b hb`. Establish `hn : Even n'` using `hH.2.2.2.2`. Establish `hrk : r ≤ k` using `hH.2.2.1`. Establish `hp : 2 ≤ p` using `by have := hH.1; omega`. Establish `hA : RowsEvenTopsBefore Fr (s.val : ℤ)` using `h2 n' r Fr L₁ N₁ hV hn (by have := hH.2.1; omega) (s.val : ℤ)`.

Establish `hQ1 : 1 ≤ 2 * Q`. Establish `h3 : 1 ≤ Qj Fr p 0` using `Nat.one_le_pow _ _ (by omega)`. Establish `h4` using `hQ.1 0`. Use linear arithmetic over natural numbers and integers. Establish `hw : algebraMap O (KK O) S.w ≠ 0`.

Introduce `h`. Conclude with `S.w_irr.ne_zero ((IsFractionRing.injective O (KK O)) (by rw [h, map_zero]))`. Establish `hab : (C (wInv S.w) * C (algebraMap O (KK O) S.w) : MvPolynomial (TV n' k) (KK O)) = 1`. Rewrite using `[← C_mul, wInv, inv_mul_cancel₀ hw, C_1]`. Establish `hsT : posOf n' (s.val : ℤ) ∈ Fr.TT` using `by rw [residue_position_of_nat]; exact hs`.

Distinguish the cases in `hE : Even s.val`. Establish `hc : r ≤ b.val` using `(normal_variable_iff_even_index hE b).mp hb`. Establish `hEz : Even (s.val : ℤ)` using `(Int.even_coe_nat _).mpr hE`. Use `⟨1, fun _ => firstKeyMinor p O Fr hrk g (s.val : ℤ) b, fun _ => firstKeyLeading p S.w Fr hrk (s.val : ℤ) b, fun _ => (-1) ^ r, fun _ => ⟨⟨first_key_integral Fr hrk g _ b, hQ1, minor_leading_part_normal_degree S.w Fr hrk hn _ hEz hA b hc, inWPow_one_of_C_w_mul S.w _, minor_tail_me …` and prove the remaining obligations. Rewrite using `[subst_top_determinant S.w Fr hrk hg hn _ hA, Fin.sum_univ_one]`.

Unfold `firstKeyLeading`. Rewrite using `[residue_position_of_nat, map_mul, map_mul, MvPolynomial.map_X]`. Use `unit_conjugation_identity _ _ _ _ _ hab ?_` and prove the remaining obligations. Rewrite using `[← map_mul, ← mul_pow]`. Simplify using the standard rewrite rules.

Establish `hc : b.val < r` using `(normal_variable_iff_odd_index hE b).mp hb`. Establish `hEz : ¬ Even (s.val : ℤ)` using `fun h => hE ((Int.even_coe_nat _).mp h)`. Use `⟨r, fun l => pairingKey p O Fr g (s.val : ℤ) l, fun l => pairingKeyLeadingPart p S.w Fr hrk (s.val : ℤ) l, fun l => (topPairingMatrix p O Fr hrk (s.val : ℤ)).adjugate ⟨b.val, hc⟩ l, fun l => ⟨⟨third_key_integral Fr hg _ l, hQ1, k3_leading_support_normDeg_eq_one S.w Fr hrk hn _ hE …` and prove the remaining obligations. Rewrite using `[substitute_pairing_key_leading_part hp S.w Fr hrk hg hn _ hEz hA l, add_sub_cancel_left]`. Conclude with `uniformiser_power_leading_mem_order S.w 2 _`.

Establish `e` using `congrArg (MvPolynomial.map (algebraMap O (KK O))) (Formalism.CountingSumsFrames.Top.detMulEqSumAdjugate (MvPolynomial (TV n' k) O) r (topPairingMatrix p O Fr hrk (s.val : ℤ)) (fun a : Fin r => X (posOf n' (s.val : ℤ), Fin.castLE hrk a)) ⟨b.val, hc⟩) beta_reduce at e`. Rewrite `e` using `[map_mul, map_sum, MvPolynomial.map_X]`. Establish `hX : (X (s, b) : MvPolynomial (TV n' k) (KK O)) = X (posOf n' (s.val : ℤ), Fin.castLE hrk ⟨b.val, hc⟩)`. Rewrite using `[residue_position_of_nat]`. Both sides reduce to the same expression.

Rewrite using `[subst_top_determinant S.w Fr hrk hg hn _ hA, hX, mul_comm]`. Use `e.trans (Finset.sum_congr rfl fun l _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul]`. Unfold `pairingKeyLeadingPart`. Conclude with `mul_eq_of_mul_eq_one_cancel _ _ _ _ hab`.
-/
theorem pairing_order_of_planes_and_rows (D : Formalism.BasicNotions.D7) (h1 : RowsPairOnPlanes) (h2 : RowsEvenTopsInWindow) : PointsLemma D := by
  intro p n' r k _ _ O _ _ _ _ S hO hH Fr L₁ N₁ hV Q hQ g hg s hs b hb
  have hn : Even n' := hH.2.2.2.2
  have hrk : r ≤ k := hH.2.2.1
  have hp : 2 ≤ p := by have := hH.1; omega
  have hA : RowsEvenTopsBefore Fr (s.val : ℤ) := h2 n' r Fr L₁ N₁ hV hn (by have := hH.2.1; omega) (s.val : ℤ)
  have hQ1 : 1 ≤ 2 * Q := by
    have h3 : 1 ≤ Qj Fr p 0 := Nat.one_le_pow _ _ (by omega)
    have h4 := hQ.1 0
    omega
  have hw : algebraMap O (KK O) S.w ≠ 0 := by
    intro h
    exact S.w_irr.ne_zero ((IsFractionRing.injective O (KK O)) (by rw [h, map_zero]))
  have hab : (C (wInv S.w) * C (algebraMap O (KK O) S.w) : MvPolynomial (TV n' k) (KK O)) = 1 := by
    rw [← C_mul, wInv, inv_mul_cancel₀ hw, C_1]
  have hsT : posOf n' (s.val : ℤ) ∈ Fr.TT := by rw [residue_position_of_nat]; exact hs
  by_cases hE : Even s.val
  · have hc : r ≤ b.val := (normal_variable_iff_even_index hE b).mp hb
    have hEz : Even (s.val : ℤ) := (Int.even_coe_nat _).mpr hE
    refine ⟨1, fun _ => firstKeyMinor p O Fr hrk g (s.val : ℤ) b, fun _ => firstKeyLeading p S.w Fr hrk (s.val : ℤ) b,
      fun _ => (-1) ^ r, fun _ => ⟨⟨first_key_integral Fr hrk g _ b, hQ1, minor_leading_part_normal_degree S.w Fr hrk hn _ hEz hA b hc,
        inWPow_one_of_C_w_mul S.w _, minor_tail_mem_order_two hp S.w Fr hrk hg hn _ hEz hA b hc,
        fun g' hg' => (h1 p n' r k O S hO hH Fr L₁ N₁ hV g g' hg hg' s hs).1 hE b hc⟩,
        inT_of_mem_supported (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _),
        first_key_supported_on_tops Fr hrk g _ hsT hA b, first_key_leading_supported_on_tops S.w Fr hrk _ hsT hA b,
        onTops_of_supported Fr (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _)⟩, ?_⟩
    rw [subst_top_determinant S.w Fr hrk hg hn _ hA, Fin.sum_univ_one]
    unfold firstKeyLeading
    rw [residue_position_of_nat, map_mul, map_mul, MvPolynomial.map_X]
    refine unit_conjugation_identity _ _ _ _ _ hab ?_
    rw [← map_mul, ← mul_pow]
    simp
  · have hc : b.val < r := (normal_variable_iff_odd_index hE b).mp hb
    have hEz : ¬ Even (s.val : ℤ) := fun h => hE ((Int.even_coe_nat _).mp h)
    refine ⟨r, fun l => pairingKey p O Fr g (s.val : ℤ) l, fun l => pairingKeyLeadingPart p S.w Fr hrk (s.val : ℤ) l,
      fun l => (topPairingMatrix p O Fr hrk (s.val : ℤ)).adjugate ⟨b.val, hc⟩ l,
      fun l => ⟨⟨third_key_integral Fr hg _ l, hQ1, k3_leading_support_normDeg_eq_one S.w Fr hrk hn _ hEz hA l,
        inWPow_one_of_C_w_mul S.w _, ?_,
        fun g' hg' => (h1 p n' r k O S hO hH Fr L₁ N₁ hV g g' hg hg' s hs).2 hE l⟩,
        inT_of_mem_supported (adjugate_mem_subalgebra _ _ (pairing_matrix_supported_tops Fr hrk hn _ hA) _ _),
        pairingKey_on_tops Fr g _ hsT hA l, third_key_leading_supported_on_tops S.w Fr hrk _ hsT hA l,
        onTops_of_supported Fr (adjugate_mem_subalgebra _ _ (row_power_supported_on_tops Fr hrk _ hA) _ _)⟩, ?_⟩
    · rw [substitute_pairing_key_leading_part hp S.w Fr hrk hg hn _ hEz hA l, add_sub_cancel_left]
      exact uniformiser_power_leading_mem_order S.w 2 _
    · have e := congrArg (MvPolynomial.map (algebraMap O (KK O)))
        (Formalism.CountingSumsFrames.Top.detMulEqSumAdjugate (MvPolynomial (TV n' k) O) r (topPairingMatrix p O Fr hrk (s.val : ℤ))
          (fun a : Fin r => X (posOf n' (s.val : ℤ), Fin.castLE hrk a)) ⟨b.val, hc⟩)
      beta_reduce at e
      rw [map_mul, map_sum, MvPolynomial.map_X] at e
      have hX : (X (s, b) : MvPolynomial (TV n' k) (KK O)) =
          X (posOf n' (s.val : ℤ), Fin.castLE hrk ⟨b.val, hc⟩) := by
        rw [residue_position_of_nat]; rfl
      rw [subst_top_determinant S.w Fr hrk hg hn _ hA, hX, mul_comm]
      refine e.trans (Finset.sum_congr rfl fun l _ => ?_)
      rw [map_mul]
      unfold pairingKeyLeadingPart
      exact mul_eq_of_mul_eq_one_cancel _ _ _ _ hab

/- English proof (translation)
Unfold `posOf`. Simplify using `only [Int.add_mul_emod_self_left]`.
-/
theorem posOf_add_mul_alt {n' : ℕ} [NeZero n'] (x t : ℤ) : posOf n' (x + n' * t) = posOf n' x := by
  unfold posOf
  simp only [Int.add_mul_emod_self_left]

/- English proof (translation)
Introduce `n' r _ Fr L₁ N₁ hV hn hr s l hl`. Establish `hall : ∀ y ∈ evensBefore Fr s, (s - (r : ℤ) * n' ≤ y ∧ y < s) ∧ posOf n' y ∈ Fr.TT ∧ Even y`. Introduce `y hy`. Unfold `evensBefore at hy`. Rewrite `hy` using `[List.mem_reverse, Finset.mem_sort, Finset.mem_filter, Finset.mem_Ico]`.

Conclude with `hy`. Take `⟨heT, heE⟩` from `hV.2.2.2.2.1 0 0 (by omega)`. Establish `hn0 : (0 : ℤ) < (n' : ℤ)` using `by exact_mod_cast NeZero.pos n'`. Establish `hnE : Even (n' : ℤ)` using `(Int.even_coe_nat n').mpr hn`. Establish `hd` using `Int.emod_def (Fr.fr 0 0 - (s - (r : ℤ) * n')) (n' : ℤ)`.

Establish `h0` using `Int.emod_nonneg (Fr.fr 0 0 - (s - (r : ℤ) * n')) hn0.ne'`. Establish `h1` using `Int.emod_lt_of_pos (Fr.fr 0 0 - (s - (r : ℤ) * n')) hn0`. Rewrite `h0`, `h1` using `[hd]`. Generalize the expression as in `(Fr.fr 0 0 - (s - (r : ℤ) * n')) / (n' : ℤ) = q at h0 h1`. Establish `hlen : l < (evensBefore Fr s).length`.

Unfold `evensBefore`. Rewrite using `[List.length_reverse, Finset.length_sort]`. Use `lt_of_lt_of_le hl ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Introduce `i hi`.

Establish `hi' : i < r` using `by simpa using hi`. Establish `hi0 : (0 : ℤ) ≤ (n' : ℤ) * (i : ℤ)` using `by positivity`. Establish `hi1 : (n' : ℤ) * ((i : ℤ) + 1) ≤ (n' : ℤ) * (r : ℤ)` using `mul_le_mul_of_nonneg_left (by exact_mod_cast hi') hn0.le`. Simplify using `only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ico]`. Use `⟨⟨by linarith, by linarith⟩, ?_, heE.add (hnE.mul_right _)⟩` and prove the remaining obligations.

Rewrite using `[posOf_add_mul_alt]`. Conclude with `heT`. Introduce `i _ j _ hij`. Establish `h2 : (n' : ℤ) * ((i : ℤ) - q) = (n' : ℤ) * ((j : ℤ) - q)`. Establish `h3 : Fr.fr 0 0 + (n' : ℤ) * ((i : ℤ) - q) = Fr.fr 0 0 + (n' : ℤ) * ((j : ℤ) - q)` using `hij`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4` using `mul_left_cancel₀ hn0.ne' h2`. Establish `h5 : (i : ℤ) = j` using `by linarith`. Conclude with `h5` after adjusting the coercions. Establish `hmem : Arow Fr s l ∈ evensBefore Fr s`.

Unfold `Arow`. Rewrite using `[List.getD_eq_getElem _ _ hlen]`. Conclude with `List.getElem_mem hlen`. Take `⟨⟨_, h6⟩, h7, h8⟩` from `hall _ hmem`. Conclude with `⟨h8, h7, h6⟩`.
-/
theorem window_holds_even_tops : RowsEvenTopsInWindow := by
  intro n' r _ Fr L₁ N₁ hV hn hr s l hl
  have hall : ∀ y ∈ evensBefore Fr s, (s - (r : ℤ) * n' ≤ y ∧ y < s) ∧ posOf n' y ∈ Fr.TT ∧ Even y := by
    intro y hy
    unfold evensBefore at hy
    rw [List.mem_reverse, Finset.mem_sort, Finset.mem_filter, Finset.mem_Ico] at hy
    exact hy
  obtain ⟨heT, heE⟩ := hV.2.2.2.2.1 0 0 (by omega)
  have hn0 : (0 : ℤ) < (n' : ℤ) := by exact_mod_cast NeZero.pos n'
  have hnE : Even (n' : ℤ) := (Int.even_coe_nat n').mpr hn
  have hd := Int.emod_def (Fr.fr 0 0 - (s - (r : ℤ) * n')) (n' : ℤ)
  have h0 := Int.emod_nonneg (Fr.fr 0 0 - (s - (r : ℤ) * n')) hn0.ne'
  have h1 := Int.emod_lt_of_pos (Fr.fr 0 0 - (s - (r : ℤ) * n')) hn0
  rw [hd] at h0 h1
  generalize (Fr.fr 0 0 - (s - (r : ℤ) * n')) / (n' : ℤ) = q at h0 h1
  have hlen : l < (evensBefore Fr s).length := by
    unfold evensBefore
    rw [List.length_reverse, Finset.length_sort]
    refine lt_of_lt_of_le hl ?_
    calc r = (Finset.range r).card := (Finset.card_range r).symm
      _ ≤ _ := Finset.card_le_card_of_injOn (fun i : ℕ => Fr.fr 0 0 + (n' : ℤ) * ((i : ℤ) - q)) ?_ ?_
    · intro i hi
      have hi' : i < r := by simpa using hi
      have hi0 : (0 : ℤ) ≤ (n' : ℤ) * (i : ℤ) := by positivity
      have hi1 : (n' : ℤ) * ((i : ℤ) + 1) ≤ (n' : ℤ) * (r : ℤ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hi') hn0.le
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ico]
      refine ⟨⟨by linarith, by linarith⟩, ?_, heE.add (hnE.mul_right _)⟩
      rw [posOf_add_mul_alt]
      exact heT
    · intro i _ j _ hij
      have h2 : (n' : ℤ) * ((i : ℤ) - q) = (n' : ℤ) * ((j : ℤ) - q) := by
        have h3 : Fr.fr 0 0 + (n' : ℤ) * ((i : ℤ) - q) = Fr.fr 0 0 + (n' : ℤ) * ((j : ℤ) - q) := hij
        linarith
      have h4 := mul_left_cancel₀ hn0.ne' h2
      have h5 : (i : ℤ) = j := by linarith
      exact_mod_cast h5
  have hmem : Arow Fr s l ∈ evensBefore Fr s := by
    unfold Arow
    rw [List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem hlen
  obtain ⟨⟨_, h6⟩, h7, h8⟩ := hall _ hmem
  exact ⟨h8, h7, h6⟩

/- English proof (translation)
The claim follows from `pairing_order_of_planes_and_rows D h1 window_holds_even_tops`.
-/
theorem keys_of_rational_planes (D : Formalism.BasicNotions.D7) (h1 : RowsPairOnPlanes) : PointsLemma D := pairing_order_of_planes_and_rows D h1 window_holds_even_tops

section B3modw

variable {p n' r k : ℕ} [Fact p.Prime] [NeZero n'] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p n') O]

def newVariableIntegral (w : O) (r : ℕ) (v : TV n' k) : MvPolynomial (TV n' k) O := if IsNormal r v then C w * X v else X v

/- English proof (translation)
Apply the tactic sequence `by_cases h : IsNormal r v <;> simp [newVariableIntegral, newVar, h]`.
-/
theorem map_newVariableIntegral (w : O) (r : ℕ) (v : TV n' k) :
    MvPolynomial.map (algebraMap O (KK O)) (newVariableIntegral w r v) = newVar w r v := by
  by_cases h : IsNormal r v <;> simp [newVariableIntegral, newVar, h]

/- English proof (translation)
Rewrite using `[sigMat_eq_map, sigMat_eq_map, sigMat_eq_map, Matrix.map_mul]`.
-/
theorem frobenius_twisted_matrix_mul (A B : Matrix (Fin k) (Fin k) (WF p n')) (a : ℤ) :
    sigMat p n' O (A * B) a = sigMat p n' O A a * sigMat p n' O B a := by
  rw [sigMat_eq_map, sigMat_eq_map, sigMat_eq_map, Matrix.map_mul]

def dualRowIntegral (w : O) (r : ℕ) (g' g : Matrix (Fin k) (Fin k) (WF p n')) (a : ℤ) (b : Fin k) :
    MvPolynomial (TV n' k) O :=
  ∑ b' : Fin k, newVariableIntegral w r (posOf n' a, b') * C (algebraMap (WF p n') O (sigPow p n' a ((g⁻¹ * g') b b')))

/- English proof (translation)
Establish `hs : ¬ Even (posOf n' a).val` using `fun h => ha ((posOf_even hn a).1 h)`. Unfold `yg`. Rewrite using `[map_sum]`. Simplify using `only [map_mul, subst_X_odd w r g' _ hs, sigMat_posOf]`. Establish `hC : ∀ x : KK O, subst p n' O w n' r g' (C x) = C x` using `fun x => by`.

Unfold `subst`. Conclude with `(liftSubst p n' O w r (LLT n') g').commutes x`. Simplify using `only [hC, Finset.sum_mul, mul_assoc, ← C_mul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.mul_sum, ← map_sum]`.

Unfold `dualRowIntegral`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun b' _ => ?_` and prove the remaining obligations. Establish `e : ∑ c : Fin k, sigMat p n' O g' a c b' * (sigMat p n' O g a)⁻¹ b c = sigMat p n' O (g⁻¹ * g') a b b'`. Rewrite using `[frobenius_twisted_matrix_mul, ← sigmaMatrix_inv_at_shift hg, Matrix.mul_apply]`.

Conclude with `Finset.sum_congr rfl fun c _ => mul_comm _ _`. Rewrite using `[map_mul, map_newVariableIntegral, MvPolynomial.map_C, e]`. Both sides reduce to the same expression.
-/
theorem substitute_dual_row (w : O) (r : ℕ) (g' : Matrix (Fin k) (Fin k) (WF p n'))
    {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (hn : Even n') (a : ℤ) (ha : ¬ Even a) (b : Fin k) :
    subst p n' O w n' r g' (yg p n' O n' g a b) =
      MvPolynomial.map (algebraMap O (KK O)) (dualRowIntegral w r g' g a b) := by
  have hs : ¬ Even (posOf n' a).val := fun h => ha ((posOf_even hn a).1 h)
  unfold yg
  rw [map_sum]
  simp only [map_mul, subst_X_odd w r g' _ hs, sigMat_posOf]
  have hC : ∀ x : KK O, subst p n' O w n' r g' (C x) = C x := fun x => by
    unfold subst; exact (liftSubst p n' O w r (LLT n') g').commutes x
  simp only [hC, Finset.sum_mul, mul_assoc, ← C_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, ← map_sum]
  unfold dualRowIntegral
  rw [map_sum]
  refine Finset.sum_congr rfl fun b' _ => ?_
  have e : ∑ c : Fin k, sigMat p n' O g' a c b' * (sigMat p n' O g a)⁻¹ b c = sigMat p n' O (g⁻¹ * g') a b b' := by
    rw [frobenius_twisted_matrix_mul, ← sigmaMatrix_inv_at_shift hg, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  rw [map_mul, map_newVariableIntegral, MvPolynomial.map_C, e]
  rfl

/- English proof (translation)
Establish `hsum : ∀ (n N : ℕ) (f : Fin N → R), (∑ i, f i) ^ p ^ n = ∑ i, f i ^ p ^ n`. Introduce `n N f`. Use `map_sum (iterateFrobenius R p n) f Finset.univ` as an intermediate fact. Simplify using `only [iterateFrobenius_def] at this`. Conclude with `this`.

Establish `h1 : ∀ c, (∑ i : Fin r, x i * α (Fin.castLE hrk i) c ^ p ^ m) ^ p ^ e = ∑ i : Fin r, x i ^ p ^ e * α (Fin.castLE hrk i) c ^ p ^ (m + e)`. Introduce `c`. Rewrite using `[hsum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_pow, ← pow_mul, ← pow_add]`.

Simplify using `only [h1, Finset.sum_mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun b' _ => ?_` and prove the remaining obligations.

Establish `h2 : ∑ c, x i ^ p ^ e * α (Fin.castLE hrk i) c ^ p ^ (m + e) * (y b' * β c b' ^ p ^ (m + e)) = x i ^ p ^ e * y b' * (∑ c, α (Fin.castLE hrk i) c * β c b') ^ p ^ (m + e)`. Rewrite using `[hsum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[mul_pow]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h2, hαβ]`. Distinguish the cases in `hb : b'.val < r`. Rewrite using `[hy b' hb]`. Expand and normalize the polynomial expressions, which then agree. Establish `hne : Fin.castLE hrk i ≠ b'`.

Introduce `h`. Apply `hb` to reduce the goal to its premises. Rewrite using `[← h]`. Conclude with `i.isLt`. Rewrite using `[if_neg hne, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), mul_zero]`.
-/
theorem twisted_pairing_eq_zero {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] {r k : ℕ} (hrk : r ≤ k)
    (x : Fin r → R) (y : Fin k → R) (α β : Fin k → Fin k → R) (m e : ℕ)
    (hαβ : ∀ i b', ∑ c, α i c * β c b' = if i = b' then 1 else 0) (hy : ∀ b' : Fin k, b'.val < r → y b' = 0) :
    ∑ c, (∑ i : Fin r, x i * α (Fin.castLE hrk i) c ^ p ^ m) ^ p ^ e * ∑ b', y b' * β c b' ^ p ^ (m + e) = 0 := by
  have hsum : ∀ (n N : ℕ) (f : Fin N → R), (∑ i, f i) ^ p ^ n = ∑ i, f i ^ p ^ n := by
    intro n N f
    have := map_sum (iterateFrobenius R p n) f Finset.univ
    simp only [iterateFrobenius_def] at this
    exact this
  have h1 : ∀ c, (∑ i : Fin r, x i * α (Fin.castLE hrk i) c ^ p ^ m) ^ p ^ e =
      ∑ i : Fin r, x i ^ p ^ e * α (Fin.castLE hrk i) c ^ p ^ (m + e) := by
    intro c
    rw [hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, ← pow_mul, ← pow_add]
  simp only [h1, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun b' _ => ?_
  have h2 : ∑ c, x i ^ p ^ e * α (Fin.castLE hrk i) c ^ p ^ (m + e) * (y b' * β c b' ^ p ^ (m + e)) =
      x i ^ p ^ e * y b' * (∑ c, α (Fin.castLE hrk i) c * β c b') ^ p ^ (m + e) := by
    rw [hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_pow]
    ring
  rw [h2, hαβ]
  by_cases hb : b'.val < r
  · rw [hy b' hb]; ring
  · have hne : Fin.castLE hrk i ≠ b' := by
      intro h
      apply hb
      rw [← h]
      exact i.isLt
    rw [if_neg hne, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), mul_zero]

/- English proof (translation)
Establish `hn0 : (0 : ℤ) < (n' : ℤ)` using `by exact_mod_cast NeZero.pos n'`. Establish `h0` using `Int.emod_nonneg A hn0.ne'`. Establish `hN : (((A % (n' : ℤ)).toNat + (s - A).toNat : ℕ) : ℤ) = A % (n' : ℤ) + (s - A)`. Rewrite using `[Nat.cast_add, Int.toNat_of_nonneg h0, Int.toNat_of_nonneg (by omega)]`. Establish `hmod : ((((A % (n' : ℤ)).toNat + (s - A).toNat) % n' : ℕ) : ℤ) = s % (n' : ℤ)`.

Rewrite using `[Int.natCast_mod, hN, Int.emod_add_emod]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `⟨((A % (n' : ℤ)).toNat + (s - A).toNat) / n', ?_⟩` and prove the remaining obligations. Rewrite using `[← hmod, Int.toNat_natCast]`.

Conclude with `(Nat.mod_add_div _ _).symm`.
-/
theorem residue_exponent_shift (n' : ℕ) [NeZero n'] (A s : ℤ) (h : A < s) :
    ∃ t : ℕ, (A % (n' : ℤ)).toNat + (s - A).toNat = (s % (n' : ℤ)).toNat + n' * t := by
  have hn0 : (0 : ℤ) < (n' : ℤ) := by exact_mod_cast NeZero.pos n'
  have h0 := Int.emod_nonneg A hn0.ne'
  have hN : (((A % (n' : ℤ)).toNat + (s - A).toNat : ℕ) : ℤ) = A % (n' : ℤ) + (s - A) := by
    rw [Nat.cast_add, Int.toNat_of_nonneg h0, Int.toNat_of_nonneg (by omega)]
  have hmod : ((((A % (n' : ℤ)).toNat + (s - A).toNat) % n' : ℕ) : ℤ) = s % (n' : ℤ) := by
    rw [Int.natCast_mod, hN, Int.emod_add_emod]
    congr 1
    ring
  refine ⟨((A % (n' : ℤ)).toNat + (s - A).toNat) / n', ?_⟩
  rw [← hmod, Int.toNat_natCast]
  exact (Nat.mod_add_div _ _).symm

/- English proof (translation)
Establish `hs : ¬ Even (posOf n' a).val` using `fun h => ha ((posOf_even hn a).1 h)`. Establish `hw : IsLocalRing.residue O S.w = 0`. Rewrite using `[IsLocalRing.residue_eq_zero_iff, S.w_irr.maximalIdeal_eq]`. Conclude with `Ideal.mem_span_singleton_self _`. Unfold `dualRowIntegral`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun b' _ => ?_` and prove the remaining obligations. Establish `hF : IsLocalRing.residue O (algebraMap (WF p n') O (sigPow p n' a ((g⁻¹ * g') b b'))) = (ι (WittVector.constantCoeff ((g⁻¹ * g') b b'))) ^ p ^ m`. Establish `h1 : WittVector.constantCoeff (sigPow p n' a ((g⁻¹ * g') b b')) = (WittVector.constantCoeff ((g⁻¹ * g') b b')) ^ p ^ m`. Rewrite using `[sigPow, constant_coeff_frobenius_pow, hm, galois_field_frobenius_period (NeZero.ne n')]`.

Rewrite using `[← hι, h1, map_pow]`. Rewrite using `[map_mul, MvPolynomial.map_C, hF]`. Unfold `newVariableIntegral`. Distinguish the cases in `hb : b'.val < r`. Rewrite using `[if_pos ((normal_variable_iff_odd_index hs b').mpr hb), if_pos hb]`.

Simplify using `[hw]`. Rewrite using `[if_neg ((normal_variable_iff_odd_index hs b').not.mpr hb), if_neg hb]`. Simplify using the standard rewrite rules.
-/
theorem residue_twisted_row_eq [IsDiscreteValuationRing O] (S : UniformizedDVR p O) (r : ℕ)
    (g' g : Matrix (Fin k) (Fin k) (WF p n')) (hn : Even n') (a : ℤ) (ha : ¬ Even a) (b : Fin k)
    (ι : GaloisField p n' →+* FF O)
    (hι : ∀ x, ι (WittVector.constantCoeff x) = IsLocalRing.residue O (algebraMap (WF p n') O x))
    (m t : ℕ) (hm : m = (a % (n' : ℤ)).toNat + n' * t) :
    MvPolynomial.map (IsLocalRing.residue O) (dualRowIntegral S.w r g' g a b) =
      ∑ b' : Fin k, (if b'.val < r then 0 else X (posOf n' a, b')) *
        (C (ι (WittVector.constantCoeff ((g⁻¹ * g') b b')))) ^ p ^ m := by
  have hs : ¬ Even (posOf n' a).val := fun h => ha ((posOf_even hn a).1 h)
  have hw : IsLocalRing.residue O S.w = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, S.w_irr.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self _
  unfold dualRowIntegral
  rw [map_sum]
  refine Finset.sum_congr rfl fun b' _ => ?_
  have hF : IsLocalRing.residue O (algebraMap (WF p n') O (sigPow p n' a ((g⁻¹ * g') b b'))) =
      (ι (WittVector.constantCoeff ((g⁻¹ * g') b b'))) ^ p ^ m := by
    have h1 : WittVector.constantCoeff (sigPow p n' a ((g⁻¹ * g') b b')) =
        (WittVector.constantCoeff ((g⁻¹ * g') b b')) ^ p ^ m := by
      rw [sigPow, constant_coeff_frobenius_pow, hm, galois_field_frobenius_period (NeZero.ne n')]
    rw [← hι, h1, map_pow]
  rw [map_mul, MvPolynomial.map_C, hF]
  unfold newVariableIntegral
  by_cases hb : b'.val < r
  · rw [if_pos ((normal_variable_iff_odd_index hs b').mpr hb), if_pos hb]
    simp [hw]
  · rw [if_neg ((normal_variable_iff_odd_index hs b').not.mpr hb), if_neg hb]
    simp

/- English proof (translation)
Establish `hφ : ((IsLocalRing.residue O).comp (algebraMap (WF p n') O)) (p : WF p n') = 0`. Rewrite using `[RingHom.comp_apply, map_natCast, IsLocalRing.residue_eq_zero_iff]`. Conclude with `S.p_mem`. Take `⟨ι, hι⟩` from `exists_residue_field_factor _ hφ`. Establish `hι' : ∀ x, ι (WittVector.constantCoeff x) = IsLocalRing.residue O (algebraMap (WF p n') O x)` using `hι`.

Establish `: CharP (FF O) p` using `(CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by`. Establish `h` using `(IsLocalRing.residue_eq_zero_iff (p : O)).mpr S.p_mem`. Rewrite using `[map_natCast] at h)` and apply the resulting hypothesis. Take `⟨t, ht⟩` from `residue_exponent_shift n' (Arow Fr s l.val) s (hA l.val l.isLt).2.2`. Establish `hh : (g'⁻¹ * g) * (g⁻¹ * g') = 1`.

Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc g, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul, Matrix.nonsing_inv_mul _ hg']`. Establish `hαβ : ∀ i b' : Fin k, ∑ c : Fin k, (C (ι (WittVector.constantCoeff ((g'⁻¹ * g) i c))) : MvPolynomial (TV n' k) (FF O)) * C (ι (WittVector.constantCoeff ((g⁻¹ * g') c b'))) = if i = b' then 1 else 0`. Introduce `i b'`. Establish `h3 : (C (ι (WittVector.constantCoeff (((g'⁻¹ * g) * (g⁻¹ * g')) i b'))) : MvPolynomial (TV n' k) (FF O)) = ∑ c : Fin k, C (ι (WittVector.constantCoeff ((g'⁻¹ * g) i c))) * C (ι (WittVector.constantCoeff ((g⁻¹ * g') c b')))`. Rewrite using `[Matrix.mul_apply, map_sum, map_sum, map_sum]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_mul]`. Rewrite using `[← h3, hh, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Unfold `rowPowerExponent`.

Rewrite using `[map_sum]`. Use `(Finset.sum_congr rfl fun c _ => ?_).trans (twisted_pairing_eq_zero p hrk (fun i : Fin r => (X (posOf n' (Arow Fr s l.val), Fin.castLE hrk i) : MvPolynomial (TV n' k) (FF O))) (fun b' : Fin k => if b'.val < r then 0 else X (posOf n' s, b')) (fun i c => C (ι (WittVector.constantCo …` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, residue_integral_primal_row S hrk _ _ c ι hι' ((Arow Fr s l.val) % (n' : ℤ)).toNat 0 (by simp), residue_twisted_row_eq S r g' g hn s hs c ι hι' _ t ht]`.
-/
theorem third_key_residue_eq_zero [IsDiscreteValuationRing O] (S : UniformizedDVR p O) (Fr : Frames n' r) (hrk : r ≤ k)
    {g g' : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (hg' : IsGLW g') (hn : Even n') (s : ℤ)
    (hs : ¬ Even s) (hA : RowsEvenTopsBefore Fr s) (l : Fin r) :
    MvPolynomial.map (IsLocalRing.residue O)
      (∑ c : Fin k, integralPrimalRow p n' O S.w r (g'⁻¹ * g) (Arow Fr s l.val) c ^ rowPowerExponent p Fr s l.val *
        dualRowIntegral S.w r g' g s c) = 0 := by
  have hφ : ((IsLocalRing.residue O).comp (algebraMap (WF p n') O)) (p : WF p n') = 0 := by
    rw [RingHom.comp_apply, map_natCast, IsLocalRing.residue_eq_zero_iff]
    exact S.p_mem
  obtain ⟨ι, hι⟩ := exists_residue_field_factor _ hφ
  have hι' : ∀ x, ι (WittVector.constantCoeff x) = IsLocalRing.residue O (algebraMap (WF p n') O x) := hι
  have : CharP (FF O) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
    have h := (IsLocalRing.residue_eq_zero_iff (p : O)).mpr S.p_mem
    rwa [map_natCast] at h)
  obtain ⟨t, ht⟩ := residue_exponent_shift n' (Arow Fr s l.val) s (hA l.val l.isLt).2.2
  have hh : (g'⁻¹ * g) * (g⁻¹ * g') = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc g, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul,
      Matrix.nonsing_inv_mul _ hg']
  have hαβ : ∀ i b' : Fin k, ∑ c : Fin k,
      (C (ι (WittVector.constantCoeff ((g'⁻¹ * g) i c))) : MvPolynomial (TV n' k) (FF O)) *
        C (ι (WittVector.constantCoeff ((g⁻¹ * g') c b'))) = if i = b' then 1 else 0 := by
    intro i b'
    have h3 : (C (ι (WittVector.constantCoeff (((g'⁻¹ * g) * (g⁻¹ * g')) i b'))) :
        MvPolynomial (TV n' k) (FF O)) = ∑ c : Fin k, C (ι (WittVector.constantCoeff ((g'⁻¹ * g) i c))) *
          C (ι (WittVector.constantCoeff ((g⁻¹ * g') c b'))) := by
      rw [Matrix.mul_apply, map_sum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_mul, map_mul, map_mul]
    rw [← h3, hh, Matrix.one_apply]
    split_ifs <;> simp
  unfold rowPowerExponent
  rw [map_sum]
  refine (Finset.sum_congr rfl fun c _ => ?_).trans (twisted_pairing_eq_zero p hrk
    (fun i : Fin r => (X (posOf n' (Arow Fr s l.val), Fin.castLE hrk i) : MvPolynomial (TV n' k) (FF O)))
    (fun b' : Fin k => if b'.val < r then 0 else X (posOf n' s, b'))
    (fun i c => C (ι (WittVector.constantCoeff ((g'⁻¹ * g) i c))))
    (fun c b' => C (ι (WittVector.constantCoeff ((g⁻¹ * g') c b'))))
    ((Arow Fr s l.val) % (n' : ℤ)).toNat (s - Arow Fr s l.val).toNat hαβ (fun b' hb => if_pos hb))
  rw [map_mul, map_pow, residue_integral_primal_row S hrk _ _ c ι hι' ((Arow Fr s l.val) % (n' : ℤ)).toNat 0 (by simp),
    residue_twisted_row_eq S r g' g hn s hs c ι hι' _ t ht]

end B3modw

def ExplicitMinorsOrderRemaining : Prop :=
  ∀ (p n' r k : ℕ) [Fact p.Prime] [NeZero n'] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF p n') O] (S : UniformizedDVR p O), OHyp p n' O S → ∀ hH : CommonHypotheses p n' r k,
  ∀ (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ →
  ∀ g g' : Matrix (Fin k) (Fin k) (WF p n'), IsGLW g → IsGLW g' →
  ∀ s ∈ Fr.TT, Even s.val → ∀ c : Fin k, r ≤ c.val →
    ordGe p n' O S.w n' r g' (firstKeyMinor p O Fr hH.2.2.1 g (s.val : ℤ) c) 1

/- English proof (translation)
Introduce `p n' r k _ _ O _ _ _ _ S hO hH Fr L₁ N₁ hV g g' hg hg' s hs`. Establish `hn : Even n'` using `hH.2.2.2.2`. Establish `hA : RowsEvenTopsBefore Fr (s.val : ℤ)` using `window_holds_even_tops n' r Fr L₁ N₁ hV hn (by have := hH.2.1; omega) (s.val : ℤ)`. Use `⟨fun hE c hc => h p n' r k O S hO hH Fr L₁ N₁ hV g g' hg hg' s hs hE c hc, fun hE l => ?_⟩` and prove the remaining obligations. Establish `hEz : ¬ Even (s.val : ℤ)` using `fun h => hE ((Int.even_coe_nat _).mp h)`.

Establish `e` using `residue_zero_mem_order_one S _ (third_key_residue_eq_zero S Fr hH.2.2.1 hg hg' hn _ hEz hA l)`. Establish `e2 : subst p n' O S.w n' r g' (pairingKey p O Fr g (s.val : ℤ) l) = MvPolynomial.map (algebraMap O (KK O)) (∑ c : Fin k, integralPrimalRow p n' O S.w r (g'⁻¹ * g) (Arow Fr (s.val : ℤ) l.val) c ^ rowPowerExponent p Fr (s.val : ℤ) l.val * dualRowIntegral S.w r g' g (s.val : ℤ) c)`. Unfold `pairingKey`. Rewrite using `[map_sum, map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_mul, map_pow, map_pow, subst_twisted_row_even S.w r g hg' hn _ (hA l.val l.isLt).1, substitute_dual_row S.w r g' hg hn _ hEz]`. Rewrite `e` using `[← e2]`. Conclude with `e`.
-/
theorem plane_pairings_of_first_key (h : ExplicitMinorsOrderRemaining) : RowsPairOnPlanes := by
  intro p n' r k _ _ O _ _ _ _ S hO hH Fr L₁ N₁ hV g g' hg hg' s hs
  have hn : Even n' := hH.2.2.2.2
  have hA : RowsEvenTopsBefore Fr (s.val : ℤ) := window_holds_even_tops n' r Fr L₁ N₁ hV hn (by have := hH.2.1; omega) (s.val : ℤ)
  refine ⟨fun hE c hc => h p n' r k O S hO hH Fr L₁ N₁ hV g g' hg hg' s hs hE c hc, fun hE l => ?_⟩
  have hEz : ¬ Even (s.val : ℤ) := fun h => hE ((Int.even_coe_nat _).mp h)
  have e := residue_zero_mem_order_one S _ (third_key_residue_eq_zero S Fr hH.2.2.1 hg hg' hn _ hEz hA l)
  have e2 : subst p n' O S.w n' r g' (pairingKey p O Fr g (s.val : ℤ) l) = MvPolynomial.map (algebraMap O (KK O))
      (∑ c : Fin k, integralPrimalRow p n' O S.w r (g'⁻¹ * g) (Arow Fr (s.val : ℤ) l.val) c ^ rowPowerExponent p Fr (s.val : ℤ) l.val *
        dualRowIntegral S.w r g' g (s.val : ℤ) c) := by
    unfold pairingKey
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, map_mul, map_pow, map_pow, subst_twisted_row_even S.w r g hg' hn _ (hA l.val l.isLt).1,
      substitute_dual_row S.w r g' hg hn _ hEz]
  rw [← e2] at e
  exact e

/- English proof (translation)
The claim follows from `keys_of_rational_planes D (plane_pairings_of_first_key h)`.
-/
theorem keys_of_explicit_minors (D : Formalism.BasicNotions.D7) (h : ExplicitMinorsOrderRemaining) : PointsLemma D :=
  keys_of_rational_planes D (plane_pairings_of_first_key h)

end Formalism.MainNotions.G.WittFrameLocaliserOrders

end

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.G.WittFrameLocaliserOrders

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning

/- English proof (translation)
Establish `hn : (0 : ℤ) < n'` using `by exact_mod_cast NeZero.pos n'`. Establish `h1 : (a + (n' : ℤ) * R) % (n' : ℤ) = a % (n' : ℤ)` using `Int.add_mul_emod_self_left a n' R`. Establish `h2` using `Int.emod_def (a + (n' : ℤ) * R) (n' : ℤ)`. Establish `h3 : 0 ≤ (a + (n' : ℤ) * R) / (n' : ℤ)` using `Int.ediv_nonneg h hn.le`. Establish `h4 : 0 ≤ a % (n' : ℤ)` using `Int.emod_nonneg _ hn.ne'`.

Use `⟨((a + (n' : ℤ) * R) / (n' : ℤ)).toNat, ?_⟩` and prove the remaining obligations. Use `zify`. Rewrite using `[Int.toNat_of_nonneg h, Int.toNat_of_nonneg h4, Int.toNat_of_nonneg h3]`. Rewrite `h2` using `[h1]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bk_shift (n' : ℕ) [NeZero n'] (a : ℤ) (R : ℕ) (h : 0 ≤ a + (n' : ℤ) * R) :
    ∃ t : ℕ, (a + (n' : ℤ) * R).toNat = (a % (n' : ℤ)).toNat + n' * t := by
  have hn : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
  have h1 : (a + (n' : ℤ) * R) % (n' : ℤ) = a % (n' : ℤ) := Int.add_mul_emod_self_left a n' R
  have h2 := Int.emod_def (a + (n' : ℤ) * R) (n' : ℤ)
  have h3 : 0 ≤ (a + (n' : ℤ) * R) / (n' : ℤ) := Int.ediv_nonneg h hn.le
  have h4 : 0 ≤ a % (n' : ℤ) := Int.emod_nonneg _ hn.ne'
  refine ⟨((a + (n' : ℤ) * R) / (n' : ℤ)).toNat, ?_⟩
  zify
  rw [Int.toNat_of_nonneg h, Int.toNat_of_nonneg h4, Int.toNat_of_nonneg h3]
  rw [h1] at h2
  linarith

section V

variable {p n' : ℕ} [Fact p.Prime] [NeZero n'] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF p n') O] {k r : ℕ}

/- English proof (translation)
Establish `hφ : ((IsLocalRing.residue O).comp (algebraMap (WF p n') O)) (p : WF p n') = 0`. Rewrite using `[RingHom.comp_apply, map_natCast, IsLocalRing.residue_eq_zero_iff]`. Conclude with `S.p_mem`. Take `⟨ι, hι⟩` from `exists_residue_field_factor _ hφ`. Establish `hι' : ∀ x, ι (WittVector.constantCoeff x) = IsLocalRing.residue O (algebraMap (WF p n') O x)` using `hι`.

Establish `h1 : subst p n' O S.w n' r g' (Matrix.of fun l c' : Fin (r + 1) => xg p n' O n' g (aZ l) (cols c') ^ p ^ (Sn - An l)).det = MvPolynomial.map (algebraMap O (KK O)) (Matrix.of fun l c' : Fin (r + 1) => integralPrimalRow p n' O S.w r (g'⁻¹ * g) (aZ l) (cols c') ^ p ^ (Sn - An l)).de …`. Rewrite using `[AlgHom.map_det, RingHom.map_det]`. Use `congrArg Matrix.det (Matrix.ext fun l c' => ?_)` and prove the remaining obligations. Use `show subst p n' O S.w n' r g' (xg p n' O n' g (aZ l) (cols c') ^ p ^ (Sn - An l)) = MvPolynomial.map (algebraMap O (KK O)) (integralPrimalRow p n' O S.w r (g'⁻¹ * g) (aZ l) (cols c') ^ p ^ (Sn - An l))`. Rewrite using `[map_pow, map_pow, subst_twisted_row_even S.w r g hg' hn _ (hev l)]`.

Rewrite using `[h1]`. Apply `residue_zero_mem_order_one` to reduce the goal to its premises. Establish `: CharP (FF O) p` using `charP_of_injective_ringHom ι.injective p`. Apply `IsFractionRing.injective (MvPolynomial (TV n' k) (FF O)) (FractionRing (MvPolynomial (TV n' k) (FF O)))` to reduce the goal to its premises. Rewrite using `[map_zero, RingHom.map_det, RingHom.map_det]`.

Establish `hunit : IsUnit ((g'⁻¹ * g).map ((algebraMap (MvPolynomial (TV n' k) (FF O)) (FractionRing (MvPolynomial (TV n' k) (FF O)))).comp ((C : FF O →+* MvPolynomial (TV n' k) (FF O)).comp (ι.comp (WittVector.constantCoeff : WF p n' →+* GaloisField p n'))))).det`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Use `IsUnit.map _ ?_` and prove the remaining obligations. Rewrite using `[Matrix.det_mul]`. Conclude with `IsUnit.mul (Matrix.isUnit_nonsing_inv_det _ hg') hg`.

Establish `key` using `((Formalism.CountingSumsFrames.Top.keyVanish p (FractionRing (MvPolynomial (TV n' k) (FF O))) r k _ hunit Sn).1 An (fun l i => if r ≤ i.val then 0 else algebraMap (MvPolynomial (TV n' k) (FF O)) (FractionRing (MvPolynomial (TV n' k) (FF O))) (X (posOf n' (aZ l), i))) cols hle (fu …`. Rewrite using `[← key]`. Use `congrArg Matrix.det (Matrix.ext fun l c' => ?_)` and prove the remaining obligations. Take `⟨t, ht⟩` from `hAn l`. Use `show algebraMap (MvPolynomial (TV n' k) (FF O)) (FractionRing (MvPolynomial (TV n' k) (FF O))) (MvPolynomial.map (IsLocalRing.residue O) (integralPrimalRow p n' O S.w r (g'⁻¹ * g) (aZ l) (cols c') ^ p ^ (Sn - An l))) = _`.

Rewrite using `[map_pow, map_pow, residue_integral_primal_row S hrk (g'⁻¹ * g) (aZ l) (cols c') ι hι' (An l) t ht, Matrix.of_apply]`. Use `congr 1`. Rewrite using `[Matrix.vecMul, dotProduct, map_sum, ← sum_ite_first_columns hrk (fun b' : Fin k => algebraMap (MvPolynomial (TV n' k) (FF O)) (FractionRing (MvPolynomial (TV n' k) (FF O))) (X (posOf n' (aZ l), b') * C (ι (WittVector.constantCoeff ((g'⁻¹ * g) b' (cols c')))) ^ p ^ An l))]`. Use `Finset.sum_congr rfl fun b' _ => ?_` and prove the remaining obligations. Use `split_ifs with hb`.

Rewrite using `[zero_mul]`. Rewrite using `[map_mul, map_pow]`. Both sides reduce to the same expression.
-/
theorem bk_vanish1 (S : UniformizedDVR p O) (hrk : r ≤ k) (hn : Even n') (g : Matrix (Fin k) (Fin k) (WF p n'))
    {g' : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (hg' : IsGLW g') (aZ : Fin (r + 1) → ℤ)
    (hev : ∀ l, Even (aZ l)) (An : Fin (r + 1) → ℕ)
    (hAn : ∀ l, ∃ t : ℕ, An l = (aZ l % (n' : ℤ)).toNat + n' * t) (Sn : ℕ) (hle : ∀ l, An l ≤ Sn)
    (cols : Fin (r + 1) → Fin k) :
    InWj S.w (subst p n' O S.w n' r g'
      (Matrix.of fun l c' : Fin (r + 1) => xg p n' O n' g (aZ l) (cols c') ^ p ^ (Sn - An l)).det) 1 := by
  have hφ : ((IsLocalRing.residue O).comp (algebraMap (WF p n') O)) (p : WF p n') = 0 := by
    rw [RingHom.comp_apply, map_natCast, IsLocalRing.residue_eq_zero_iff]
    exact S.p_mem
  obtain ⟨ι, hι⟩ := exists_residue_field_factor _ hφ
  have hι' : ∀ x, ι (WittVector.constantCoeff x) = IsLocalRing.residue O (algebraMap (WF p n') O x) := hι
  have h1 : subst p n' O S.w n' r g'
      (Matrix.of fun l c' : Fin (r + 1) => xg p n' O n' g (aZ l) (cols c') ^ p ^ (Sn - An l)).det =
      MvPolynomial.map (algebraMap O (KK O))
        (Matrix.of fun l c' : Fin (r + 1) => integralPrimalRow p n' O S.w r (g'⁻¹ * g) (aZ l) (cols c') ^ p ^ (Sn - An l)).det := by
    rw [AlgHom.map_det, RingHom.map_det]
    refine congrArg Matrix.det (Matrix.ext fun l c' => ?_)
    show subst p n' O S.w n' r g' (xg p n' O n' g (aZ l) (cols c') ^ p ^ (Sn - An l)) =
      MvPolynomial.map (algebraMap O (KK O)) (integralPrimalRow p n' O S.w r (g'⁻¹ * g) (aZ l) (cols c') ^ p ^ (Sn - An l))
    rw [map_pow, map_pow, subst_twisted_row_even S.w r g hg' hn _ (hev l)]
  rw [h1]
  apply residue_zero_mem_order_one
  have : CharP (FF O) p := charP_of_injective_ringHom ι.injective p
  apply IsFractionRing.injective (MvPolynomial (TV n' k) (FF O)) (FractionRing (MvPolynomial (TV n' k) (FF O)))
  rw [map_zero, RingHom.map_det, RingHom.map_det]
  have hunit : IsUnit ((g'⁻¹ * g).map ((algebraMap (MvPolynomial (TV n' k) (FF O))
      (FractionRing (MvPolynomial (TV n' k) (FF O)))).comp ((C : FF O →+* MvPolynomial (TV n' k) (FF O)).comp
        (ι.comp (WittVector.constantCoeff : WF p n' →+* GaloisField p n'))))).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    refine IsUnit.map _ ?_
    rw [Matrix.det_mul]
    exact IsUnit.mul (Matrix.isUnit_nonsing_inv_det _ hg') hg
  have key := ((Formalism.CountingSumsFrames.Top.keyVanish p (FractionRing (MvPolynomial (TV n' k) (FF O))) r k _ hunit Sn).1 An
    (fun l i => if r ≤ i.val then 0 else algebraMap (MvPolynomial (TV n' k) (FF O))
      (FractionRing (MvPolynomial (TV n' k) (FF O))) (X (posOf n' (aZ l), i))) cols hle
    (fun l i hi => if_pos hi))
  rw [← key]
  refine congrArg Matrix.det (Matrix.ext fun l c' => ?_)
  obtain ⟨t, ht⟩ := hAn l
  show algebraMap (MvPolynomial (TV n' k) (FF O)) (FractionRing (MvPolynomial (TV n' k) (FF O)))
      (MvPolynomial.map (IsLocalRing.residue O)
        (integralPrimalRow p n' O S.w r (g'⁻¹ * g) (aZ l) (cols c') ^ p ^ (Sn - An l))) = _
  rw [map_pow, map_pow, residue_integral_primal_row S hrk (g'⁻¹ * g) (aZ l) (cols c') ι hι' (An l) t ht, Matrix.of_apply]
  congr 1
  rw [Matrix.vecMul, dotProduct, map_sum, ← sum_ite_first_columns hrk (fun b' : Fin k =>
    algebraMap (MvPolynomial (TV n' k) (FF O)) (FractionRing (MvPolynomial (TV n' k) (FF O)))
      (X (posOf n' (aZ l), b') * C (ι (WittVector.constantCoeff ((g'⁻¹ * g) b' (cols c')))) ^ p ^ An l))]
  refine Finset.sum_congr rfl fun b' _ => ?_
  split_ifs with hb
  · rw [zero_mul]
  · rw [map_mul, map_pow]
    rfl

/- English proof (translation)
Establish `hn : (0 : ℤ) ≤ (r : ℤ) * n'` using `by positivity`. Unfold `Arow`. Distinguish the cases in `h : l < (evensBefore Fr s).length`. Rewrite using `[List.getD_eq_getElem _ _ h]`. Establish `hm` using `List.getElem_mem h`.

Unfold `evensBefore at hm`. Rewrite `hm` using `[List.mem_reverse, Finset.mem_sort, Finset.mem_filter, Finset.mem_Ico]`. Conclude with `hm.1.1`. Rewrite using `[List.getD_eq_default _ _ (not_lt.1 h)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem bk_Arow_low (Fr : Frames n' r) (s : ℤ) (l : ℕ) : s - (r : ℤ) * n' ≤ Arow Fr s l := by
  have hn : (0 : ℤ) ≤ (r : ℤ) * n' := by positivity
  unfold Arow
  by_cases h : l < (evensBefore Fr s).length
  · rw [List.getD_eq_getElem _ _ h]
    have hm := List.getElem_mem h
    unfold evensBefore at hm
    rw [List.mem_reverse, Finset.mem_sort, Finset.mem_filter, Finset.mem_Ico] at hm
    exact hm.1.1
  · rw [List.getD_eq_default _ _ (not_lt.1 h)]
    omega

/- English proof (translation)
Establish `hlow : ∀ l : ℕ, 0 ≤ Arow Fr (s.val : ℤ) l + (n' : ℤ) * r` using `fun l => by`. Establish `h1` using `bk_Arow_low Fr (s.val : ℤ) l`. Establish `h2 : (r : ℤ) * n' = (n' : ℤ) * r` using `mul_comm _ _`. Establish `h3 : (0 : ℤ) ≤ s.val` using `by positivity`. Use linear arithmetic over natural numbers and integers.

Establish `hs0 : 0 ≤ (s.val : ℤ) + (n' : ℤ) * r` using `by positivity`. Establish `hK : firstKeyMinor p O Fr hrk g (s.val : ℤ) c = (Matrix.of fun l c' : Fin (r + 1) => xg p n' O n' g ((Fin.cons (s.val : ℤ) (fun l : Fin r => Arow Fr (s.val : ℤ) l.val) : Fin (r + 1) → ℤ) l) ((Fin.snoc (Fin.castLE hrk) c : Fin (r + 1) → Fin k) c') ^ p ^ (((s.val : ℤ) + (n' : ℤ) * …`. Unfold `firstKeyMinor`. Use `congrArg Matrix.det (Matrix.ext fun l c' => ?_)` and prove the remaining obligations. Establish `hexp : ∀ l : Fin r, rowPowerExponent p Fr (s.val : ℤ) l.val = p ^ (((s.val : ℤ) + (n' : ℤ) * r).toNat - (Arow Fr (s.val : ℤ) l.val + (n' : ℤ) * r).toNat)` using `fun l => by`.

Unfold `rowPowerExponent`. Use `congr 1`. Establish `h1` using `hlow l.val`. Establish `h2` using `(hA l.val l.2).2.2`. Use linear arithmetic over natural numbers and integers.

Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) l <;> refine Fin.lastCases ?_ (fun j => ?_) c' <;>`. Simplify using `[Formalism.CountingSumsFrames.borderedMatrix, hexp]`. Use `show InWj S.w (subst p n' O S.w n' r g' (firstKeyMinor p O Fr hrk g (s.val : ℤ) c)) 1`. Rewrite using `[hK]`. Use `bk_vanish1 S hrk hn g hg hg' _ ?_ (fun l => (((Fin.cons (s.val : ℤ) (fun l : Fin r => Arow Fr (s.val : ℤ) l.val) : Fin (r + 1) → ℤ) l) + (n' : ℤ) * r).toNat) ?_ _ ?_ _` and prove the remaining obligations.

Introduce `l`. Use `Fin.cases ?_ (fun i => ?_) l` and prove the remaining obligations. Simplify using `using (Int.even_coe_nat _).2 hs`. Simplify using `using (hA i.val i.2).1`. Introduce `l`.

Use `Fin.cases ?_ (fun i => ?_) l` and prove the remaining obligations. Simplify using `using bk_shift n' (s.val : ℤ) r hs0`. Simplify using `using bk_shift n' (Arow Fr (s.val : ℤ) i.val) r (hlow i.val)`. Introduce `l`. Use `Fin.cases ?_ (fun i => ?_) l` and prove the remaining obligations.

Simplify using the standard rewrite rules. Establish `h1` using `hlow i.val`. Establish `h2` using `(hA i.val i.2).2.2`. Simplify using `only [Fin.cons_succ]`. Use linear arithmetic over natural numbers and integers.
-/
theorem explicit_minor_order_positive (S : UniformizedDVR p O) (hrk : r ≤ k) (hn : Even n') (Fr : Frames n' r)
    (g : Matrix (Fin k) (Fin k) (WF p n')) {g' : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (hg' : IsGLW g')
    (s : Fin n') (hs : Even s.val) (hA : RowsEvenTopsBefore Fr (s.val : ℤ)) (c : Fin k) :
    ordGe p n' O S.w n' r g' (firstKeyMinor p O Fr hrk g (s.val : ℤ) c) 1 := by
  have hlow : ∀ l : ℕ, 0 ≤ Arow Fr (s.val : ℤ) l + (n' : ℤ) * r := fun l => by
    have h1 := bk_Arow_low Fr (s.val : ℤ) l
    have h2 : (r : ℤ) * n' = (n' : ℤ) * r := mul_comm _ _
    have h3 : (0 : ℤ) ≤ s.val := by positivity
    omega
  have hs0 : 0 ≤ (s.val : ℤ) + (n' : ℤ) * r := by positivity
  have hK : firstKeyMinor p O Fr hrk g (s.val : ℤ) c =
      (Matrix.of fun l c' : Fin (r + 1) =>
        xg p n' O n' g ((Fin.cons (s.val : ℤ) (fun l : Fin r => Arow Fr (s.val : ℤ) l.val) : Fin (r + 1) → ℤ) l)
          ((Fin.snoc (Fin.castLE hrk) c : Fin (r + 1) → Fin k) c') ^
          p ^ (((s.val : ℤ) + (n' : ℤ) * r).toNat -
            (((Fin.cons (s.val : ℤ) (fun l : Fin r => Arow Fr (s.val : ℤ) l.val) : Fin (r + 1) → ℤ) l) +
              (n' : ℤ) * r).toNat)).det := by
    unfold firstKeyMinor
    refine congrArg Matrix.det (Matrix.ext fun l c' => ?_)
    have hexp : ∀ l : Fin r, rowPowerExponent p Fr (s.val : ℤ) l.val =
        p ^ (((s.val : ℤ) + (n' : ℤ) * r).toNat - (Arow Fr (s.val : ℤ) l.val + (n' : ℤ) * r).toNat) := fun l => by
      unfold rowPowerExponent
      congr 1
      have h1 := hlow l.val
      have h2 := (hA l.val l.2).2.2
      omega
    refine Fin.cases ?_ (fun i => ?_) l <;> refine Fin.lastCases ?_ (fun j => ?_) c' <;>
      simp [Formalism.CountingSumsFrames.borderedMatrix, hexp]
  show InWj S.w (subst p n' O S.w n' r g' (firstKeyMinor p O Fr hrk g (s.val : ℤ) c)) 1
  rw [hK]
  refine bk_vanish1 S hrk hn g hg hg' _ ?_ (fun l =>
    (((Fin.cons (s.val : ℤ) (fun l : Fin r => Arow Fr (s.val : ℤ) l.val) : Fin (r + 1) → ℤ) l) +
      (n' : ℤ) * r).toNat) ?_ _ ?_ _
  · intro l
    refine Fin.cases ?_ (fun i => ?_) l
    · simpa using (Int.even_coe_nat _).2 hs
    · simpa using (hA i.val i.2).1
  · intro l
    refine Fin.cases ?_ (fun i => ?_) l
    · simpa using bk_shift n' (s.val : ℤ) r hs0
    · simpa using bk_shift n' (Arow Fr (s.val : ℤ) i.val) r (hlow i.val)
  · intro l
    refine Fin.cases ?_ (fun i => ?_) l
    · simp
    · have h1 := hlow i.val
      have h2 := (hA i.val i.2).2.2
      simp only [Fin.cons_succ]
      omega

end V

/- English proof (translation)
Introduce `p n' r k _ _ O _ _ _ _ S hO hH Fr L₁ N₁ hV g g' hg hg' s hs hse c hc`. Conclude with `explicit_minor_order_positive S hH.2.2.1 hH.2.2.2.2 Fr g hg hg' s hse (window_holds_even_tops n' r Fr L₁ N₁ hV hH.2.2.2.2 (by have := hH.2.1; omega) (s.val : ℤ)) c`.
-/
theorem first_key_plane_order : ExplicitMinorsOrderRemaining := by
  intro p n' r k _ _ O _ _ _ _ S hO hH Fr L₁ N₁ hV g g' hg hg' s hs hse c hc
  exact explicit_minor_order_positive S hH.2.2.1 hH.2.2.2.2 Fr g hg hg' s hse
    (window_holds_even_tops n' r Fr L₁ N₁ hV hH.2.2.2.2 (by have := hH.2.1; omega) (s.val : ℤ)) c

/- English proof (translation)
The claim follows from `keys_of_explicit_minors D first_key_plane_order`.
-/
theorem keys_vanish_modulo_uniformiser (D : Formalism.BasicNotions.D7) : PointsLemma D := keys_of_explicit_minors D first_key_plane_order

end Formalism.MainNotions.G.WittFrameLocaliserOrders

end

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.G.WittFrameLocaliserOrders

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning

section C0

variable {O : Type} [CommRing O] [IsDomain O] {n' k : ℕ}

def bx_Gr (w : O) (r : ℕ) (P : MvPolynomial (TV n' k) (KK O)) : Prop :=
  ∀ m, ∃ c : O, P.coeff m = algebraMap O (KK O) (w ^ normDeg r m * c)

/- English proof (translation)
Rewrite using `[← weight_eq_normal_degree, ← weight_eq_normal_degree, ← weight_eq_normal_degree, map_add]`.
-/
theorem bx_normDeg_add (r : ℕ) (m m' : TV n' k →₀ ℕ) : normDeg r (m + m') = normDeg r m + normDeg r m' := by
  rw [← weight_eq_normal_degree, ← weight_eq_normal_degree, ← weight_eq_normal_degree, map_add]

/- English proof (translation)
Rewrite using `[← weight_eq_normal_degree, Finsupp.weight_single]`. Simplify using `[normalVariableWeight]`.
-/
theorem bx_normDeg_single (r : ℕ) (v : TV n' k) : normDeg r (Finsupp.single v 1) = if IsNormal r v then 1 else 0 := by
  rw [← weight_eq_normal_degree, Finsupp.weight_single]
  simp [normalVariableWeight]

/- English proof (translation)
Rewrite using `[← weight_eq_normal_degree, map_zero]`.
-/
theorem bx_normDeg_zero (r : ℕ) : normDeg r (0 : TV n' k →₀ ℕ) = 0 := by
  rw [← weight_eq_normal_degree, map_zero]

variable {w : O} {r : ℕ}

/- English proof (translation)
Introduce `m` and use `by obtain ⟨a, ha⟩ := hP m obtain ⟨b, hb⟩ := hQ m exact ⟨a + b, by rw [coeff_add, ha, hb, ← map_add]; ring_nf⟩`.
-/
theorem bx_Gr_add {P Q : MvPolynomial (TV n' k) (KK O)} (hP : bx_Gr w r P) (hQ : bx_Gr w r Q) : bx_Gr w r (P + Q) :=
  fun m => by
    obtain ⟨a, ha⟩ := hP m
    obtain ⟨b, hb⟩ := hQ m
    exact ⟨a + b, by rw [coeff_add, ha, hb, ← map_add]; ring_nf⟩

/- English proof (translation)
Introduce `m` and use `⟨0, by simp⟩`.
-/
theorem bx_Gr_zero : bx_Gr w r (0 : MvPolynomial (TV n' k) (KK O)) := fun m => ⟨0, by simp⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using bx_Gr_zero`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `bx_Gr_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem bx_Gr_sum {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial (TV n' k) (KK O))
    (h : ∀ i ∈ s, bx_Gr w r (P i)) : bx_Gr w r (∑ i ∈ s, P i) := by
  induction s using Finset.induction_on with
  | empty => simpa using bx_Gr_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact bx_Gr_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Introduce `m` and use `by choose a ha using hP choose b hb using hQ refine ⟨∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, a x.1 * b x.2, ?_⟩ rw [coeff_mul, Finset.mul_sum, map_sum] refine Finset.sum_congr rfl fun x hx => ?_ have hm : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.1 hx rw [ha, …`.
-/
theorem bx_Gr_mul {P Q : MvPolynomial (TV n' k) (KK O)} (hP : bx_Gr w r P) (hQ : bx_Gr w r Q) : bx_Gr w r (P * Q) :=
  fun m => by
    choose a ha using hP
    choose b hb using hQ
    refine ⟨∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, a x.1 * b x.2, ?_⟩
    rw [coeff_mul, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hm : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    rw [ha, hb, ← map_mul, ← hm, bx_normDeg_add, pow_add]
    congr 1
    ring

/- English proof (translation)
Introduce `m` and use `by by_cases h : 0 = m · subst h exact ⟨c, by rw [coeff_C, if_pos rfl, bx_normDeg_zero, pow_zero, one_mul]⟩ · exact ⟨0, by rw [coeff_C, if_neg h]; simp⟩`.
-/
theorem bx_Gr_C (c : O) : bx_Gr w r (C (algebraMap O (KK O) c) : MvPolynomial (TV n' k) (KK O)) := fun m => by
  by_cases h : 0 = m
  · subst h
    exact ⟨c, by rw [coeff_C, if_pos rfl, bx_normDeg_zero, pow_zero, one_mul]⟩
  · exact ⟨0, by rw [coeff_C, if_neg h]; simp⟩

/- English proof (translation)
Introduce `m` and use `by unfold newVar by_cases hm : Finsupp.single v 1 = m · subst hm rw [bx_normDeg_single] split_ifs with hN · exact ⟨1, by rw [coeff_C_mul, coeff_X, if_pos rfl, pow_one, mul_one, mul_one]⟩ · exact ⟨1, by rw [coeff_X, if_pos rfl, pow_zero, mul_one, map_one]⟩ · refine ⟨0, ?_⟩ split_i …`.
-/
theorem bx_Gr_newVar (v : TV n' k) : bx_Gr w r (newVar w r v) := fun m => by
  unfold newVar
  by_cases hm : Finsupp.single v 1 = m
  · subst hm
    rw [bx_normDeg_single]
    split_ifs with hN
    · exact ⟨1, by rw [coeff_C_mul, coeff_X, if_pos rfl, pow_one, mul_one, mul_one]⟩
    · exact ⟨1, by rw [coeff_X, if_pos rfl, pow_zero, mul_one, map_one]⟩
  · refine ⟨0, ?_⟩
    split_ifs with hN
    · rw [coeff_C_mul, coeff_X, if_neg hm]; simp
    · rw [coeff_X, if_neg hm]; simp

end C0

section lift_substitution_coeff_divisible

variable {p n' : ℕ} [Fact p.Prime] [NeZero n'] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p n') O] {k : ℕ}

/- English proof (translation)
The claim follows from `bx_Gr_C (algebraMap (WF p n') O (sigPow p n' s (g a b)))`.
-/
theorem bx_Gr_sig (w : O) (r : ℕ) (g : Matrix (Fin k) (Fin k) (WF p n')) (s : ℤ) (a b : Fin k) :
    bx_Gr w r (C (sigMat p n' O g s a b) : MvPolynomial (TV n' k) (KK O)) :=
  bx_Gr_C (algebraMap (WF p n') O (sigPow p n' s (g a b)))

/- English proof (translation)
Take `⟨s, c⟩` from `v`. Distinguish the cases in `hs : Even s.val`. Rewrite using `[subst_X_even w r g s hs c, sigmaMatrix_inv_general hg]`. Conclude with `bx_Gr_sum _ _ fun b _ => bx_Gr_mul (bx_Gr_newVar _) (bx_Gr_sig w r g⁻¹ _ b c)`. Rewrite using `[subst_X_odd w r g s hs c]`.

Conclude with `bx_Gr_sum _ _ fun b _ => bx_Gr_mul (bx_Gr_newVar _) (bx_Gr_sig w r g _ c b)`.
-/
theorem bx_Gr_subst_X (w : O) (r : ℕ) {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (v : TV n' k) :
    bx_Gr w r (subst p n' O w n' r g (X v)) := by
  obtain ⟨s, c⟩ := v
  by_cases hs : Even s.val
  · rw [subst_X_even w r g s hs c, sigmaMatrix_inv_general hg]
    exact bx_Gr_sum _ _ fun b _ => bx_Gr_mul (bx_Gr_newVar _) (bx_Gr_sig w r g⁻¹ _ b c)
  · rw [subst_X_odd w r g s hs c]
    exact bx_Gr_sum _ _ fun b _ => bx_Gr_mul (bx_Gr_newVar _) (bx_Gr_sig w r g _ c b)

/- English proof (translation)
Take `⟨h, rfl, -⟩` from `exists_map_of_inWj0 ((inA_iff_inWj0 (w := w) F).1 hF)`. Use `clear hF`. Proceed by induction on `h using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[map_C]`.

Establish `: subst p n' O w n' r g (C (algebraMap O (KK O) a)) = C (algebraMap O (KK O) a)`. Unfold `subst`. Conclude with `(liftSubst p n' O w r (LLT n') g).commutes _`. Rewrite using `[this]`. Conclude with `bx_Gr_C a`.

Consider the case `add a b ha hb => rw [map_add, map_add]`. Conclude with `bx_Gr_add ha hb`. Consider the case `mul_X a v ha => rw [map_mul, map_X, map_mul]`. Conclude with `bx_Gr_mul ha (bx_Gr_subst_X w r hg v)`.
-/
theorem bx_coeff_normDeg (w : O) (r : ℕ) {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g)
    {F : MvPolynomial (TV n' k) (KK O)} (hF : InA F) : bx_Gr w r (subst p n' O w n' r g F) := by
  obtain ⟨h, rfl, -⟩ := exists_map_of_inWj0 ((inA_iff_inWj0 (w := w) F).1 hF)
  clear hF
  induction h using MvPolynomial.induction_on with
  | C a =>
    rw [map_C]
    have : subst p n' O w n' r g (C (algebraMap O (KK O) a)) = C (algebraMap O (KK O) a) := by
      unfold subst; exact (liftSubst p n' O w r (LLT n') g).commutes _
    rw [this]; exact bx_Gr_C a
  | add a b ha hb => rw [map_add, map_add]; exact bx_Gr_add ha hb
  | mul_X a v ha => rw [map_mul, map_X, map_mul]; exact bx_Gr_mul ha (bx_Gr_subst_X w r hg v)

/- English proof (translation)
Establish `hX : ∀ v : TV n' k, v.1 ∈ Fr.TT →`. Substitute `p n' O w n' r g (X v) ∈ supported (KK O) {v : TV n' k | v.1 ∈ Fr.TT} := by` using the available equality. Introduce and unpack `⟨s, c⟩ hv`. Establish `hN : ∀ b : Fin k, newVar w r ((s, b) : TV n' k) ∈ supported (KK O) {v : TV n' k | v.1 ∈ Fr.TT}` using `fun b => by`. Unfold `newVar`.

Use `split_ifs`. Conclude with `mul_mem (Subalgebra.algebraMap_mem _ _) (X_mem_supported.2 hv)`. Conclude with `X_mem_supported.2 hv`. Distinguish the cases in `hs : Even s.val`. Rewrite using `[subst_X_even w r g s hs c]`.

Conclude with `sum_mem fun b _ => mul_mem (hN b) (Subalgebra.algebraMap_mem _ _)`. Rewrite using `[subst_X_odd w r g s hs c]`. Conclude with `sum_mem fun b _ => mul_mem (hN b) (Subalgebra.algebraMap_mem _ _)`. Establish `hmem : subst p n' O w n' r g F ∈ supported (KK O) {v : TV n' k | v.1 ∈ Fr.TT}`. Rewrite using `[F.as_sum, map_sum]`.

Use `sum_mem fun d hd => ?_` and prove the remaining obligations. Rewrite using `[monomial_eq, map_mul, Finsupp.prod, map_prod]`. Use `mul_mem ?_ (prod_mem fun i hi => ?_)` and prove the remaining obligations. Establish `: subst p n' O w n' r g (C (F.coeff d)) = C (F.coeff d)`. Unfold `subst`.

Conclude with `(liftSubst p n' O w r (LLT n') g).commutes _`. Rewrite using `[this]`. Conclude with `Subalgebra.algebraMap_mem _ _`. Rewrite using `[map_pow]`. Conclude with `pow_mem (hX i (hF i ((mem_vars i).2 ⟨d, hd, hi⟩))) _`.

Introduce `v hv`. Conclude with `(mem_supported.1 hmem) (Finset.mem_coe.2 hv)`.
-/
theorem bx_onTops_subst (w : O) {r : ℕ} (Fr : Frames n' r) (g : Matrix (Fin k) (Fin k) (WF p n'))
    {F : MvPolynomial (TV n' k) (KK O)} (hF : OnTops Fr F) : OnTops Fr (subst p n' O w n' r g F) := by
  have hX : ∀ v : TV n' k, v.1 ∈ Fr.TT →
      subst p n' O w n' r g (X v) ∈ supported (KK O) {v : TV n' k | v.1 ∈ Fr.TT} := by
    rintro ⟨s, c⟩ hv
    have hN : ∀ b : Fin k, newVar w r ((s, b) : TV n' k) ∈ supported (KK O) {v : TV n' k | v.1 ∈ Fr.TT} := fun b => by
      unfold newVar
      split_ifs
      · exact mul_mem (Subalgebra.algebraMap_mem _ _) (X_mem_supported.2 hv)
      · exact X_mem_supported.2 hv
    by_cases hs : Even s.val
    · rw [subst_X_even w r g s hs c]
      exact sum_mem fun b _ => mul_mem (hN b) (Subalgebra.algebraMap_mem _ _)
    · rw [subst_X_odd w r g s hs c]
      exact sum_mem fun b _ => mul_mem (hN b) (Subalgebra.algebraMap_mem _ _)
  have hmem : subst p n' O w n' r g F ∈ supported (KK O) {v : TV n' k | v.1 ∈ Fr.TT} := by
    rw [F.as_sum, map_sum]
    refine sum_mem fun d hd => ?_
    rw [monomial_eq, map_mul, Finsupp.prod, map_prod]
    refine mul_mem ?_ (prod_mem fun i hi => ?_)
    · have : subst p n' O w n' r g (C (F.coeff d)) = C (F.coeff d) := by
        unfold subst; exact (liftSubst p n' O w r (LLT n') g).commutes _
      rw [this]; exact Subalgebra.algebraMap_mem _ _
    · rw [map_pow]
      exact pow_mem (hX i (hF i ((mem_vars i).2 ⟨d, hd, hi⟩))) _
  intro v hv
  exact (mem_supported.1 hmem) (Finset.mem_coe.2 hv)

end lift_substitution_coeff_divisible

end Formalism.MainNotions.G.WittFrameLocaliserOrders

end

noncomputable section

open MvPolynomial Finset Classical Pointwise

namespace Formalism.MainNotions.G.WittFrameLocaliserOrders

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning

section Generic

variable {P : Type*} [CommRing P] {ι : Type*} [AddCommMonoid ι] {G : ι → ℕ → Set P}

/- English proof (translation)
Establish `h` using `AddSubmonoid.mul_mem_mul ha hb`. Rewrite `h` using `[AddSubmonoid.closure_mul_closure]`. Use `AddSubmonoid.closure_mono ?_ h` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, y, hy, rfl⟩`. Conclude with `hmul _ _ _ _ _ _ hx hy`.
-/
theorem bc_gr_mul (hmul : ∀ i j E E' a b, a ∈ G i E → b ∈ G j E' → a * b ∈ G (i + j) (E + E')) {i j : ι}
    {E E' : ℕ} {a b : P} (ha : a ∈ AddSubmonoid.closure (G i E)) (hb : b ∈ AddSubmonoid.closure (G j E')) :
    a * b ∈ AddSubmonoid.closure (G (i + j) (E + E')) := by
  have h := AddSubmonoid.mul_mem_mul ha hb
  rw [AddSubmonoid.closure_mul_closure] at h
  refine AddSubmonoid.closure_mono ?_ h
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact hmul _ _ _ _ _ _ hx hy

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using AddSubmonoid.subset_closure hone`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Use `bc_gr_mul hmul (h a (Finset.mem_insert_self a s)) (ih fun t ht => h t (Finset.mem_insert_of_mem ht))` as an intermediate fact.

Simplify using `using this`.
-/
theorem bc_gr_prod (hmul : ∀ i j E E' a b, a ∈ G i E → b ∈ G j E' → a * b ∈ G (i + j) (E + E'))
    (hone : (1 : P) ∈ G 0 0) {κ : Type*} (s : Finset κ) (f : κ → P) (e : κ → ι)
    (h : ∀ t ∈ s, f t ∈ AddSubmonoid.closure (G (e t) 0)) :
    ∏ t ∈ s, f t ∈ AddSubmonoid.closure (G (∑ t ∈ s, e t) 0) := by
  induction s using Finset.induction_on with
  | empty => simpa using AddSubmonoid.subset_closure hone
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have := bc_gr_mul hmul (h a (Finset.mem_insert_self a s)) (ih fun t ht => h t (Finset.mem_insert_of_mem ht))
    simpa using this

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert t0 s h0 ih`. Rewrite using `[Finset.prod_insert h0, Finset.prod_insert h0, Finset.sum_insert h0]`. Establish `hU` using `ih (fun t ht => ha t (Finset.mem_insert_of_mem ht)) (fun t ht => hb t (Finset.mem_insert_of_mem ht))`.

Establish `hA` using `bc_gr_prod hmul hone s a e (fun t ht => ha t (Finset.mem_insert_of_mem ht))`. Establish `h1 : a t0 + b t0 ∈ AddSubmonoid.closure (G (e t0) 0)` using `add_mem (ha t0 (Finset.mem_insert_self t0 s)) (AddSubmonoid.closure_mono (hmono _) (hb t0 (Finset.mem_insert_self t0 s)))`. Establish `e1` using `bc_gr_mul hmul h1 hU`. Establish `e2` using `bc_gr_mul hmul (hb t0 (Finset.mem_insert_self t0 s)) hA`. Establish `hid : (a t0 + b t0) * ∏ t ∈ s, (a t + b t) - a t0 * ∏ t ∈ s, a t = (a t0 + b t0) * (∏ t ∈ s, (a t + b t) - ∏ t ∈ s, a t) + b t0 * ∏ t ∈ s, a t` using `by ring`.

Rewrite using `[hid]`. Conclude with `add_mem (by simpa using e1) (by simpa using e2)`.
-/
theorem bc_gr_tel (hmul : ∀ i j E E' a b, a ∈ G i E → b ∈ G j E' → a * b ∈ G (i + j) (E + E'))
    (hone : (1 : P) ∈ G 0 0) (hmono : ∀ i, G i 1 ⊆ G i 0) {κ : Type*} (s : Finset κ) (a b : κ → P) (e : κ → ι)
    (ha : ∀ t ∈ s, a t ∈ AddSubmonoid.closure (G (e t) 0)) (hb : ∀ t ∈ s, b t ∈ AddSubmonoid.closure (G (e t) 1)) :
    ∏ t ∈ s, (a t + b t) - ∏ t ∈ s, a t ∈ AddSubmonoid.closure (G (∑ t ∈ s, e t) 1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert t0 s h0 ih =>
    rw [Finset.prod_insert h0, Finset.prod_insert h0, Finset.sum_insert h0]
    have hU := ih (fun t ht => ha t (Finset.mem_insert_of_mem ht)) (fun t ht => hb t (Finset.mem_insert_of_mem ht))
    have hA := bc_gr_prod hmul hone s a e (fun t ht => ha t (Finset.mem_insert_of_mem ht))
    have h1 : a t0 + b t0 ∈ AddSubmonoid.closure (G (e t0) 0) :=
      add_mem (ha t0 (Finset.mem_insert_self t0 s))
        (AddSubmonoid.closure_mono (hmono _) (hb t0 (Finset.mem_insert_self t0 s)))
    have e1 := bc_gr_mul hmul h1 hU
    have e2 := bc_gr_mul hmul (hb t0 (Finset.mem_insert_self t0 s)) hA
    have hid : (a t0 + b t0) * ∏ t ∈ s, (a t + b t) - a t0 * ∏ t ∈ s, a t =
        (a t0 + b t0) * (∏ t ∈ s, (a t + b t) - ∏ t ∈ s, a t) + b t0 * ∏ t ∈ s, a t := by ring
    rw [hid]
    exact add_mem (by simpa using e1) (by simpa using e2)

end Generic

section Concrete

variable {p n' r k : ℕ} [Fact p.Prime] [NeZero n'] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p n') O]
  (w : O) (Fr : Frames n' r) (Q : ℕ) (g : Matrix (Fin k) (Fin k) (WF p n'))

def bc_KP (A0 : MvPolynomial (TV n' k) (KK O)) (s : ℕ) : Prop :=
  ∃ l : List (MvPolynomial (TV n' k) (KK O) × ℕ × MvPolynomial (TV n' k) (KK O)),
    (∀ y ∈ l, IsKey p n' w n' r Q g y.1 y.2.1 y.2.2 ∧ OnTops Fr y.1 ∧ OnTops Fr y.2.2) ∧
    A0 = (l.map fun y => y.2.2).prod ∧ s = (l.map fun y => y.2.1).sum

/- English proof (translation)
Assemble the required witnesses or components as `⟨[], by simp, by simp, by simp⟩`.
-/
theorem isKeyProduct_one : bc_KP w Fr Q g (1 : MvPolynomial (TV n' k) (KK O)) 0 := ⟨[], by simp, by simp, by simp⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨[(ka, o, ka0)], by simpa using ⟨h, h1, h2⟩, by simp, by simp⟩`.
-/
theorem isKeyProduct_of_isKey {ka ka0 : MvPolynomial (TV n' k) (KK O)} {o : ℕ} (h : IsKey p n' w n' r Q g ka o ka0)
    (h1 : OnTops Fr ka) (h2 : OnTops Fr ka0) : bc_KP w Fr Q g ka0 o :=
  ⟨[(ka, o, ka0)], by simpa using ⟨h, h1, h2⟩, by simp, by simp⟩

variable {w Fr Q g}

/- English proof (translation)
Take `⟨l1, h1, rfl, rfl⟩` from `hA`. Take `⟨l2, h2, rfl, rfl⟩` from `hB`. Use `⟨l1 ++ l2, ?_, by simp, by simp⟩` and prove the remaining obligations. Introduce `y hy`. Break down `List.mem_append.1 hy with h | h` into its components or cases.

Conclude with `h1 y h`. Conclude with `h2 y h`.
-/
theorem isKeyProduct_mul {A B : MvPolynomial (TV n' k) (KK O)} {s t : ℕ} (hA : bc_KP w Fr Q g A s)
    (hB : bc_KP w Fr Q g B t) : bc_KP w Fr Q g (A * B) (s + t) := by
  obtain ⟨l1, h1, rfl, rfl⟩ := hA
  obtain ⟨l2, h2, rfl, rfl⟩ := hB
  refine ⟨l1 ++ l2, ?_, by simp, by simp⟩
  intro y hy
  rcases List.mem_append.1 hy with h | h
  · exact h1 y h
  · exact h2 y h

/- English proof (translation)
Take `⟨l, h1, rfl, rfl⟩` from `hA`. Proceed by induction on `l with`. Consider the case `nil => simpa using inWj_one`. Consider the case `cons y l ih`. Simplify using `only [List.map_cons, List.prod_cons, List.sum_cons]`.

Conclude with `inWj_mul (h1 y (List.mem_cons_self)).1.2.2.2.1 (ih fun z hz => h1 z (List.mem_cons_of_mem _ hz))`.
-/
theorem inWj_of_isKeyProduct {A : MvPolynomial (TV n' k) (KK O)} {s : ℕ} (hA : bc_KP w Fr Q g A s) : InWj w A s := by
  obtain ⟨l, h1, rfl, rfl⟩ := hA
  induction l with
  | nil => simpa using inWj_one
  | cons y l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact inWj_mul (h1 y (List.mem_cons_self)).1.2.2.2.1 (ih fun z hz => h1 z (List.mem_cons_of_mem _ hz))

variable (Fr)

def bc_IT (H : MvPolynomial (TV n' k) (KK O)) : Prop :=
  ∃ h : MvPolynomial (TV n' k) O, InTV r h ∧ OnTops Fr h ∧ H = MvPolynomial.map (algebraMap O (KK O)) h

variable {Fr}

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, fun v hv => by simp at hv, fun v hv => by simp at hv, by simp⟩`.
-/
theorem bc_IT_one : bc_IT Fr (1 : MvPolynomial (TV n' k) (KK O)) :=
  ⟨1, fun v hv => by simp at hv, fun v hv => by simp at hv, by simp⟩

/- English proof (translation)
Take `⟨a, a1, a2, rfl⟩` from `hA`. Take `⟨b, b1, b2, rfl⟩` from `hB`. Use `⟨a * b, ?_, ?_, by rw [map_mul]⟩` and prove the remaining obligations. Introduce `v hv`. Break down `Finset.mem_union.1 (vars_mul a b hv) with h | h` into its components or cases.

Conclude with `a1 v h`. Conclude with `b1 v h`. Introduce `v hv`. Break down `Finset.mem_union.1 (vars_mul a b hv) with h | h` into its components or cases. Conclude with `a2 v h`.

Conclude with `b2 v h`.
-/
theorem bc_IT_mul {A B : MvPolynomial (TV n' k) (KK O)} (hA : bc_IT Fr A) (hB : bc_IT Fr B) : bc_IT Fr (A * B) := by
  obtain ⟨a, a1, a2, rfl⟩ := hA
  obtain ⟨b, b1, b2, rfl⟩ := hB
  refine ⟨a * b, ?_, ?_, by rw [map_mul]⟩
  · intro v hv
    rcases Finset.mem_union.1 (vars_mul a b hv) with h | h
    · exact a1 v h
    · exact b1 v h
  · intro v hv
    rcases Finset.mem_union.1 (vars_mul a b hv) with h | h
    · exact a2 v h
    · exact b2 v h

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using bc_IT_one`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `bc_IT_mul ih hA`.
-/
theorem bc_IT_pow {A : MvPolynomial (TV n' k) (KK O)} (hA : bc_IT Fr A) (n : ℕ) : bc_IT Fr (A ^ n) := by
  induction n with
  | zero => simpa using bc_IT_one
  | succ n ih => rw [pow_succ]; exact bc_IT_mul ih hA

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using bc_IT_one`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha]`. Conclude with `bc_IT_mul (h a (Finset.mem_insert_self a s)) (ih fun t ht => h t (Finset.mem_insert_of_mem ht))`.
-/
theorem bc_IT_prod {κ : Type*} (s : Finset κ) (f : κ → MvPolynomial (TV n' k) (KK O)) (h : ∀ t ∈ s, bc_IT Fr (f t)) :
    bc_IT Fr (∏ t ∈ s, f t) := by
  induction s using Finset.induction_on with
  | empty => simpa using bc_IT_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact bc_IT_mul (h a (Finset.mem_insert_self a s)) (ih fun t ht => h t (Finset.mem_insert_of_mem ht))

/- English proof (translation)
Take `⟨a, _, _, rfl⟩` from `hA`. Conclude with `inWj_map a`.
-/
theorem bc_IT_inWj {A : MvPolynomial (TV n' k) (KK O)} (hA : bc_IT Fr A) : InWj w A 0 := by
  obtain ⟨a, _, _, rfl⟩ := hA
  exact inWj_map a

variable (w Fr Q g)

def bc_gen (Dl : ℕ → MvPolynomial (TV n' k) (KK O)) (idx : ℕ × (ℕ → ℕ)) (E : ℕ) :
    Set (MvPolynomial (TV n' k) (KK O)) :=
  {γ | ∃ (x s e : ℕ) (A0 : MvPolynomial (TV n' k) (KK O)) (ν : TV n' k →₀ ℕ) (y : ℕ → ℕ)
      (H : MvPolynomial (TV n' k) (KK O)),
    bc_KP w Fr Q g A0 s ∧ bc_IT Fr H ∧ (∀ v ∈ ν.support, IsNormal r v ∧ v.1 ∈ Fr.TT) ∧
    x + s = idx.1 + e ∧ E ≤ e ∧ ν.sum (fun _ m => m) ≤ x ∧ ν.sum (fun _ m => m) ≤ (2 * Q + 1) * e ∧
    (∀ j < Fr.J, idx.2 j ≤ y j + e) ∧
    γ = C (algebraMap O (KK O) (w ^ x)) * A0 * monomial ν 1 * (∏ j ∈ Finset.range Fr.J, Dl j ^ y j) * H}

/- English proof (translation)
Introduce and unpack `i j E E' _ _ ⟨x1, s1, e1, A1, ν1, y1, H1, hk1, hi1, hn1, hx1, hE1, hJ1, hq1, hy1, rfl⟩ ⟨x2, s2, e2, A2, ν2, y2, H2, hk2, hi2, hn2, hx2, hE2, hJ2, hq2, hy2, rfl⟩`. Use `⟨x1 + x2, s1 + s2, e1 + e2, A1 * A2, ν1 + ν2, fun t => y1 t + y2 t, H1 * H2, isKeyProduct_mul hk1 hk2, bc_IT_mul hi1 hi2, ?_, ?_, by omega, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `v hv`. Break down `Finset.mem_union.1 (Finsupp.support_add hv) with h | h` into its components or cases. Conclude with `hn1 v h`.

Conclude with `hn2 v h`. Simplify using `only [Prod.fst_add]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Nat.mul_add]`. Use linear arithmetic over natural numbers and integers. Introduce `t ht`. Establish `h1` using `hy1 t ht`. Establish `h2` using `hy2 t ht`.

Simplify using `only [Prod.snd_add, Pi.add_apply]`. Use linear arithmetic over natural numbers and integers. Establish `hm : monomial (ν1 + ν2) (1 : KK O) = monomial ν1 1 * monomial ν2 1`. Rewrite using `[monomial_mul, one_mul]`. Simplify using `only [pow_add, map_mul, hm, Finset.prod_mul_distrib]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem bc_gen_mul (Dl : ℕ → MvPolynomial (TV n' k) (KK O)) : ∀ (i j : ℕ × (ℕ → ℕ)) (E E' : ℕ)
    (a b : MvPolynomial (TV n' k) (KK O)), a ∈ bc_gen w Fr Q g Dl i E → b ∈ bc_gen w Fr Q g Dl j E' →
    a * b ∈ bc_gen w Fr Q g Dl (i + j) (E + E') := by
  rintro i j E E' _ _ ⟨x1, s1, e1, A1, ν1, y1, H1, hk1, hi1, hn1, hx1, hE1, hJ1, hq1, hy1, rfl⟩
    ⟨x2, s2, e2, A2, ν2, y2, H2, hk2, hi2, hn2, hx2, hE2, hJ2, hq2, hy2, rfl⟩
  refine ⟨x1 + x2, s1 + s2, e1 + e2, A1 * A2, ν1 + ν2, fun t => y1 t + y2 t, H1 * H2, isKeyProduct_mul hk1 hk2,
    bc_IT_mul hi1 hi2, ?_, ?_, by omega, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_union.1 (Finsupp.support_add hv) with h | h
    · exact hn1 v h
    · exact hn2 v h
  · simp only [Prod.fst_add]; omega
  · rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]; omega
  · rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Nat.mul_add]; omega
  · intro t ht
    have h1 := hy1 t ht
    have h2 := hy2 t ht
    simp only [Prod.snd_add, Pi.add_apply]; omega
  · have hm : monomial (ν1 + ν2) (1 : KK O) = monomial ν1 1 * monomial ν2 1 := by
      rw [monomial_mul, one_mul]
    simp only [pow_add, map_mul, hm, Finset.prod_mul_distrib]
    ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, 0, 0, 1, 0, fun _ => 0, 1, isKeyProduct_one w Fr Q g, bc_IT_one, fun v hv => by simp at hv, by simp, le_rfl, by simp, by simp, fun j _ => by simp, by simp⟩`.
-/
theorem bc_gen_one (Dl : ℕ → MvPolynomial (TV n' k) (KK O)) :
    (1 : MvPolynomial (TV n' k) (KK O)) ∈ bc_gen w Fr Q g Dl 0 0 :=
  ⟨0, 0, 0, 1, 0, fun _ => 0, 1, isKeyProduct_one w Fr Q g, bc_IT_one, fun v hv => by simp at hv, by simp, le_rfl, by simp,
    by simp, fun j _ => by simp, by simp⟩

/- English proof (translation)
Introduce and unpack `_ ⟨x, s, e, A0, ν, y, H, h1, h2, h3, h4, h5, h6⟩`. Conclude with `⟨x, s, e, A0, ν, y, H, h1, h2, h3, h4, Nat.zero_le _, h6⟩`.
-/
theorem bc_gen_mono (Dl : ℕ → MvPolynomial (TV n' k) (KK O)) (i : ℕ × (ℕ → ℕ)) :
    bc_gen w Fr Q g Dl i 1 ⊆ bc_gen w Fr Q g Dl i 0 := by
  rintro _ ⟨x, s, e, A0, ν, y, H, h1, h2, h3, h4, h5, h6⟩
  exact ⟨x, s, e, A0, ν, y, H, h1, h2, h3, h4, Nat.zero_le _, h6⟩

end Concrete

section Generic2

variable {P : Type*} [CommRing P] {ι : Type*} [AddCommMonoid ι] {G : ι → ℕ → Set P}

/- English proof (translation)
Use `bc_gr_prod hmul hone (Finset.range n) (fun _ => a) (fun _ => i) (fun _ _ => h)` as an intermediate fact. Simplify using `using this`.
-/
theorem bc_gr_pow (hmul : ∀ i j E E' a b, a ∈ G i E → b ∈ G j E' → a * b ∈ G (i + j) (E + E'))
    (hone : (1 : P) ∈ G 0 0) {i : ι} {a : P} (h : a ∈ AddSubmonoid.closure (G i 0)) (n : ℕ) :
    a ^ n ∈ AddSubmonoid.closure (G (n • i) 0) := by
  have := bc_gr_prod hmul hone (Finset.range n) (fun _ => a) (fun _ => i) (fun _ _ => h)
  simpa using this

end Generic2

section Absorb

variable {p n' r k : ℕ} [Fact p.Prime] [NeZero n'] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p n') O]
  (w : O) (Fr : Frames n' r) (Q : ℕ) (g : Matrix (Fin k) (Fin k) (WF p n'))

local notation "PP" => MvPolynomial (TV n' k) (KK O)

def bc_agen (J : ℕ) (_E : ℕ) : Set PP := {z | ∃ A1 H : PP, bc_KP w Fr Q g A1 J ∧ bc_IT Fr H ∧ z = A1 * H}

/- English proof (translation)
Introduce and unpack `i j E E' _ _ ⟨A1, H1, h1, h2, rfl⟩ ⟨A2, H2, h3, h4, rfl⟩`. Conclude with `⟨A1 * A2, H1 * H2, isKeyProduct_mul h1 h3, bc_IT_mul h2 h4, by ring⟩`.
-/
theorem bc_agen_mul : ∀ (i j : ℕ) (E E' : ℕ) (a b : PP), a ∈ bc_agen w Fr Q g i E → b ∈ bc_agen w Fr Q g j E' →
    a * b ∈ bc_agen w Fr Q g (i + j) (E + E') := by
  rintro i j E E' _ _ ⟨A1, H1, h1, h2, rfl⟩ ⟨A2, H2, h3, h4, rfl⟩
  exact ⟨A1 * A2, H1 * H2, isKeyProduct_mul h1 h3, bc_IT_mul h2 h4, by ring⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, 1, isKeyProduct_one w Fr Q g, bc_IT_one, by simp⟩`.
-/
theorem bc_agen_one : (1 : PP) ∈ bc_agen w Fr Q g 0 0 := ⟨1, 1, isKeyProduct_one w Fr Q g, bc_IT_one, by simp⟩

/- English proof (translation)
Establish `hid : C (algebraMap O (KK O) (w ^ ν.sum (fun _ m => m))) * monomial ν 1 * DD1 ^ (ν.sum fun _ m => m) = ∏ v ∈ ν.support, (C (algebraMap O (KK O) w) * X v * DD1) ^ ν v`. Rewrite using `[monomial_eq]`. Unfold `Finsupp.sum Finsupp.prod`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_pow, map_one, one_mul]`. Rewrite using `[hid]`.

Establish `hpow : ∀ v ∈ ν.support, (C (algebraMap O (KK O) w) * X v * DD1) ^ ν v ∈ AddSubmonoid.closure (bc_agen w Fr Q g (ν v) 0)`. Introduce `v hv`. Use `bc_gr_pow (bc_agen_mul w Fr Q g) (bc_agen_one w Fr Q g) (hD1 v (hν v hv).1 (hν v hv).2) (ν v)` as an intermediate fact. Simplify using `using this`. Conclude with `bc_gr_prod (bc_agen_mul w Fr Q g) (bc_agen_one w Fr Q g) ν.support _ (fun v => ν v) hpow`.
-/
theorem bc_mono_absorb (DD1 : PP)
    (hD1 : ∀ v : TV n' k, IsNormal r v → v.1 ∈ Fr.TT →
      C (algebraMap O (KK O) w) * X v * DD1 ∈ AddSubmonoid.closure (bc_agen w Fr Q g 1 0))
    (ν : TV n' k →₀ ℕ) (hν : ∀ v ∈ ν.support, IsNormal r v ∧ v.1 ∈ Fr.TT) :
    C (algebraMap O (KK O) (w ^ ν.sum (fun _ m => m))) * monomial ν 1 * DD1 ^ (ν.sum fun _ m => m) ∈
      AddSubmonoid.closure (bc_agen w Fr Q g (ν.sum fun _ m => m) 0) := by
  have hid : C (algebraMap O (KK O) (w ^ ν.sum (fun _ m => m))) * monomial ν 1 * DD1 ^ (ν.sum fun _ m => m) =
      ∏ v ∈ ν.support, (C (algebraMap O (KK O) w) * X v * DD1) ^ ν v := by
    rw [monomial_eq]
    unfold Finsupp.sum Finsupp.prod
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_pow, map_one, one_mul]
  rw [hid]
  have hpow : ∀ v ∈ ν.support, (C (algebraMap O (KK O) w) * X v * DD1) ^ ν v ∈
      AddSubmonoid.closure (bc_agen w Fr Q g (ν v) 0) := by
    intro v hv
    have := bc_gr_pow (bc_agen_mul w Fr Q g) (bc_agen_one w Fr Q g) (hD1 v (hν v hv).1 (hν v hv).2) (ν v)
    simpa using this
  exact bc_gr_prod (bc_agen_mul w Fr Q g) (bc_agen_one w Fr Q g) ν.support _ (fun v => ν v) hpow

variable (hrk : r ≤ k) (c' o mu la L : ℕ)

def bc_Phi (X : PP) : Prop :=
  ∃ (l : List (Term n' k O × ℕ × ℕ)) (ρ : PP), InWj w ρ (o + c') ∧
    X = (l.map fun y => y.1.sym p n' w Fr hrk g c' y.2.1 y.2.2).sum + ρ ∧
    ∀ y ∈ l, y.1.Valid p n' w n' r Q g ∧ y.1.InTops Fr ∧ L < y.1.level ∧ y.1.level < o + c' ∧
      (y.2.1 : ℤ) = (mu : ℤ) - (2 * (Q : ℤ) + 1) * ((y.1.level : ℤ) - L) ∧
      (y.2.2 : ℤ) = (la : ℤ) - ((y.1.level : ℤ) - L)

/- English proof (translation)
Assemble the required witnesses or components as `⟨[], ρ, h, by simp, by simp⟩`.
-/
theorem bc_Phi_rho {ρ : PP} (h : InWj w ρ (o + c')) : bc_Phi w Fr Q g hrk c' o mu la L ρ :=
  ⟨[], ρ, h, by simp, by simp⟩

/- English proof (translation)
Take `⟨l1, ρ1, h1, rfl, h3⟩` from `hX`. Take `⟨l2, ρ2, k1, rfl, k3⟩` from `hY`. Use `⟨l1 ++ l2, ρ1 + ρ2, inWj_add h1 k1, by rw [List.map_append, List.sum_append]; ring, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Break down `List.mem_append.1 hy with h | h` into its components or cases.

Conclude with `h3 y h`. Conclude with `k3 y h`.
-/
theorem bc_Phi_add {X Y : PP} (hX : bc_Phi w Fr Q g hrk c' o mu la L X) (hY : bc_Phi w Fr Q g hrk c' o mu la L Y) :
    bc_Phi w Fr Q g hrk c' o mu la L (X + Y) := by
  obtain ⟨l1, ρ1, h1, rfl, h3⟩ := hX
  obtain ⟨l2, ρ2, k1, rfl, k3⟩ := hY
  refine ⟨l1 ++ l2, ρ1 + ρ2, inWj_add h1 k1, by rw [List.map_append, List.sum_append]; ring, ?_⟩
  intro y hy
  rcases List.mem_append.1 hy with h | h
  · exact h3 y h
  · exact k3 y h

/- English proof (translation)
Take `⟨l, hl, rfl, rfl⟩` from `hA`. Take `⟨h, h1, h2, rfl⟩` from `hH`. Use `⟨⟨i', l.length, fun t => l[t.1].1, fun t => l[t.1].2.1, fun t => l[t.1].2.2, h⟩, ⟨fun t => (hl _ (List.getElem_mem t.2)).1, h1⟩, ⟨fun t => (hl _ (List.getElem_mem t.2)).2, h2⟩, ?_, ?_⟩` and prove the remaining obligations. Unfold `Term.level`. Simplify using `only`.

Rewrite using `[Fin.sum_univ_fun_getElem l (fun y => y.2.1)]`. Unfold `Term.sym`. Simplify using `only`. Rewrite using `[Fin.prod_univ_fun_getElem l (fun y => y.2.2)]`.
-/
theorem bc_sym_of_KP (mu' la' i' : ℕ) {A H : PP} {s : ℕ} (hA : bc_KP w Fr Q g A s) (hH : bc_IT Fr H) :
    ∃ τ' : Term n' k O, τ'.Valid p n' w n' r Q g ∧ τ'.InTops Fr ∧ τ'.level = i' + s ∧
      τ'.sym p n' w Fr hrk g c' mu' la' = C (algebraMap O (KK O) (w ^ i')) * A *
        (subst p n' O w n' r g (R0 p n' O Fr g)) ^ c' *
        (∏ j ∈ Finset.range Fr.J, (subst p n' O w n' r g (Del p n' O Fr g j)) ^ la') *
        subst p n' O w n' r g (DtopProd p n' O Fr hrk g mu') * H := by
  obtain ⟨l, hl, rfl, rfl⟩ := hA
  obtain ⟨h, h1, h2, rfl⟩ := hH
  refine ⟨⟨i', l.length, fun t => l[t.1].1, fun t => l[t.1].2.1, fun t => l[t.1].2.2, h⟩,
    ⟨fun t => (hl _ (List.getElem_mem t.2)).1, h1⟩, ⟨fun t => (hl _ (List.getElem_mem t.2)).2, h2⟩, ?_, ?_⟩
  · unfold Term.level
    simp only
    rw [Fin.sum_univ_fun_getElem l (fun y => y.2.1)]
  · unfold Term.sym
    simp only
    rw [Fin.prod_univ_fun_getElem l (fun y => y.2.2)]

end Absorb

section Absorb2

variable {p n' r k : ℕ} [Fact p.Prime] [NeZero n'] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p n') O]
  (w : O) (Fr : Frames n' r) (Q : ℕ) (g : Matrix (Fin k) (Fin k) (WF p n'))

local notation "PP" => MvPolynomial (TV n' k) (KK O)

/- English proof (translation)
Rewrite using `[← map_pow]`. Use `congr 1`. Unfold `DtopProd`. Simplify using `only [pow_one]`. Rewrite using `[Finset.prod_pow]`.
-/
theorem bc_DtopProd_pow (hrk : r ≤ k) (n : ℕ) :
    subst p n' O w n' r g (DtopProd p n' O Fr hrk g n) = (subst p n' O w n' r g (DtopProd p n' O Fr hrk g 1)) ^ n := by
  rw [← map_pow]
  congr 1
  unfold DtopProd
  simp only [pow_one]
  rw [Finset.prod_pow]

/- English proof (translation)
Establish `: (monomial ν 1 : PP) = MvPolynomial.map (algebraMap O (KK O)) (monomial ν 1)`. Rewrite using `[map_monomial, (algebraMap O (KK O)).map_one]`. Rewrite using `[this]`. Conclude with `inWj_map _`.
-/
theorem bc_inWj_monomial (ν : TV n' k →₀ ℕ) : InWj w (monomial ν 1 : PP) 0 := by
  have : (monomial ν 1 : PP) = MvPolynomial.map (algebraMap O (KK O)) (monomial ν 1) := by
    rw [map_monomial, (algebraMap O (KK O)).map_one]
  rw [this]; exact inWj_map _

/- English proof (translation)
Take `⟨x, s, e, A0, ν, y, H, hk, hi, hn, hx, hE, hJ, hq, hy, rfl⟩` from `hγ`. Simplify using `only at hx hy`. Distinguish the cases in `hcut : o + c' ≤ L + e`. Apply `bc_Phi_rho` to reduce the goal to its premises. Establish `hDDmu : bc_IT Fr (subst p n' O w n' r g (DtopProd p n' O Fr hrk g mu))`.

Rewrite using `[bc_DtopProd_pow w Fr g hrk mu]`. Conclude with `bc_IT_pow hDD mu`. Establish `h1` using `inWj_mul (inWj_mul (inWj_mul (inWj_mul (inWj_Cpow (σ := TV n' k) (w := w) i) (inWj_mul (inWj_mul (inWj_mul (inWj_mul (inWj_Cpow (σ := TV n' k) (w := w) x) (inWj_of_isKeyProduct hk)) (bc_inWj_monomial w ν)) (bc_IT_inWj (w := w) (bc_IT_prod (Finset.range Fr.J) _ fun j _ => bc_IT_po …`. Conclude with `inWj_mono (by omega) h1`. Establish `hcut' : L + e < o + c'` using `not_le.1 hcut`.

Establish `he : e ≤ o + c' - 1 - L` using `by omega`. Establish `hmu2 : (2 * Q + 1) * e ≤ mu` using `le_trans (Nat.mul_le_mul_left _ he) hmu`. Take `⟨mu', hmu'⟩` from `Nat.exists_eq_add_of_le hmu2`. Take `⟨la', hla'⟩` from `Nat.exists_eq_add_of_le (le_trans he hla)`. Take `⟨x', hx'⟩` from `Nat.exists_eq_add_of_le hJ`.

Take `⟨n2, hn2⟩` from `Nat.exists_eq_add_of_le hq`. Establish `hZ` using `bc_mono_absorb w Fr Q g _ hD1 ν hn`. Establish `hSur : bc_IT Fr (∏ j ∈ Finset.range Fr.J, (subst p n' O w n' r g (Del p n' O Fr g (j : ℤ))) ^ (y j + e - alpha p Fr k (j : ℤ) * c'))` using `bc_IT_prod _ _ fun j _ => bc_IT_pow (hDl j) _`. Establish `main : ∀ z ∈ AddSubmonoid.closure (bc_agen w Fr Q g (ν.sum fun _ m => m) 0), bc_Phi w Fr Q g hrk c' o mu la L (C (algebraMap O (KK O) (w ^ (i + x'))) * (A0 * z) * (subst p n' O w n' r g (R0 p n' O Fr g)) ^ c' * (∏ j ∈ Finset.range Fr.J, (subst p n' O w n' r g (Del p n' O Fr g j)) …`. Substitute `p n' O w n' r g (DtopProd p n' O Fr hrk g mu') *` using the available equality.

Use the proof step `((∏ j ∈ Finset.range Fr.J, (subst p n' O w n' r g (Del p n' O Fr g (j : ℤ))) ^ (y j + e - alpha p Fr k (j : ℤ) * c')) * (subst p n' O w n' r g (DtopProd p n' O Fr hrk g 1)) ^ n2 * H * Hh)) := by`. Introduce `z hz`. Use `AddSubmonoid.closure_induction (motive := fun z _ => bc_Phi w Fr Q g hrk c' o mu la L (C (algebraMap O (KK O) (w ^ (i + x'))) * (A0 * z) * (subst p n' O w n' r g (R0 p n' O Fr g)) ^ c' * (∏ j ∈ Finset.range Fr.J, (subst p n' O w n' r g (Del p n' O Fr g j)) ^ la') *` and prove the remaining obligations. Substitute `p n' O w n' r g (DtopProd p n' O Fr hrk g mu') *` using the available equality. Use the proof step `((∏ j ∈ Finset.range Fr.J, (subst p n' O w n' r g (Del p n' O Fr g (j : ℤ))) ^ (y j + e - alpha p Fr k (j : ℤ) * c')) * (subst p n' O w n' r g (DtopProd p n' O Fr hrk g 1)) ^ n2 * H * Hh))) ?_ ?_ ?_ hz`.

Introduce and unpack `_ ⟨A1, H1, hA1, hH1, rfl⟩`. Take `⟨τ', hv, ht, hlev, hsym⟩` from `bc_sym_of_KP w Fr Q g hrk c' mu' la' (i + x') (isKeyProduct_mul hk hA1) (bc_IT_mul hH1 (bc_IT_mul (bc_IT_mul (bc_IT_mul hSur (bc_IT_pow hDD n2)) hi) hh))`. Establish `hlev2 : τ'.level = L + e` using `by rw [hlev]; omega`. Use `⟨[(τ', mu', la')], 0, inWj_zero _, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]`.

Rewrite using `[hsym]`. Expand and normalize the polynomial expressions, which then agree. Introduce `yy hyy`. Rewrite `hyy` using `[List.mem_singleton]`. Substitute `hyy` using the available equality.

Use `⟨hv, ht, by simp only; omega, by simp only; omega, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hlev2, hmu']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only`. Rewrite using `[hlev2, hla']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [mul_zero, zero_mul]`.

Conclude with `bc_Phi_rho w Fr Q g hrk c' o mu la L (inWj_zero _)`. Introduce `z1 z2 _ _ h1 h2`. Use `bc_Phi_add w Fr Q g hrk c' o mu la L h1 h2` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Establish `hDel : (∏ j ∈ Finset.range Fr.J, (subst p n' O w n' r g (Del p n' O Fr g (j : ℤ))) ^ y j) * (∏ j ∈ Finset.range Fr.J, (subst p n' O w n' r g (Del p n' O Fr g (j : ℤ))) ^ la) = (subst p n' O w n' r g (R0 p n' O Fr g)) ^ c' * (∏ j ∈ Finset.range Fr.J, (subst p n' O w n' r g (Del p …`. Unfold `R0`. Rewrite using `[map_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `h1` using `hy j (Finset.mem_range.1 hj)`.

Rewrite `h1` using `[hβ j]`. Rewrite using `[map_pow, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `hfin` using `main _ hZ`.

Use `hfin using 1` and compare the differences between its conclusion and the goal. Rewrite using `[bc_DtopProd_pow w Fr g hrk mu, bc_DtopProd_pow w Fr g hrk mu', hmu', hn2]`. Use `conv_lhs => rw [hx']`. Simplify using `only [pow_add, map_mul]`. Take the linear combination `(C (algebraMap O (KK O) (w ^ i)) * C (algebraMap O (KK O) (w ^ (ν.sum fun _ m => m))) * C (algebraMap O (KK O) (w ^ x')) * A0 * monomial ν 1 * H * Hh * (subst p n' O w n' r g (DtopProd p n' O Fr hrk g 1)) ^ (ν.sum fun _ m => m) * (subst p n' O w n' r g (DtopProd p n' O Fr hrk g 1 …`.
-/
theorem bc_absorb (hrk : r ≤ k) (c' o mu la L : ℕ)
    (hDl : ∀ j : ℕ, bc_IT Fr (subst p n' O w n' r g (Del p n' O Fr g (j : ℤ))))
    (hDD : bc_IT Fr (subst p n' O w n' r g (DtopProd p n' O Fr hrk g 1)))
    (hD1 : ∀ v : TV n' k, IsNormal r v → v.1 ∈ Fr.TT →
      C (algebraMap O (KK O) w) * X v * subst p n' O w n' r g (DtopProd p n' O Fr hrk g 1) ∈
        AddSubmonoid.closure (bc_agen w Fr Q g 1 0))
    (i a : ℕ) (hL : L = i + a) {Hh : PP} (hh : bc_IT Fr Hh)
    (hmu : (2 * Q + 1) * (o + c' - 1 - L) ≤ mu) (hla : o + c' - 1 - L ≤ la)
    (β : ℕ → ℕ) (hβ : ∀ j : ℕ, β j = alpha p Fr k (j : ℤ) * c') {γ : PP}
    (hγ : γ ∈ bc_gen w Fr Q g (fun j : ℕ => subst p n' O w n' r g (Del p n' O Fr g (j : ℤ))) (a, β) 1) :
    bc_Phi w Fr Q g hrk c' o mu la L (C (algebraMap O (KK O) (w ^ i)) * γ *
      (∏ j ∈ Finset.range Fr.J, (subst p n' O w n' r g (Del p n' O Fr g j)) ^ la) *
      subst p n' O w n' r g (DtopProd p n' O Fr hrk g mu) * Hh) := by
  obtain ⟨x, s, e, A0, ν, y, H, hk, hi, hn, hx, hE, hJ, hq, hy, rfl⟩ := hγ
  simp only at hx hy
  by_cases hcut : o + c' ≤ L + e
  · apply bc_Phi_rho
    have hDDmu : bc_IT Fr (subst p n' O w n' r g (DtopProd p n' O Fr hrk g mu)) := by
      rw [bc_DtopProd_pow w Fr g hrk mu]; exact bc_IT_pow hDD mu
    have h1 := inWj_mul (inWj_mul (inWj_mul (inWj_mul (inWj_Cpow (σ := TV n' k) (w := w) i)
      (inWj_mul (inWj_mul (inWj_mul (inWj_mul (inWj_Cpow (σ := TV n' k) (w := w) x) (inWj_of_isKeyProduct hk))
        (bc_inWj_monomial w ν))
        (bc_IT_inWj (w := w) (bc_IT_prod (Finset.range Fr.J) _ fun j _ => bc_IT_pow (hDl j) (y j))))
        (bc_IT_inWj (w := w) hi)))
      (bc_IT_inWj (w := w) (bc_IT_prod (Finset.range Fr.J) _ fun j _ => bc_IT_pow (hDl j) la)))
      (bc_IT_inWj (w := w) hDDmu)) (bc_IT_inWj (w := w) hh)
    exact inWj_mono (by omega) h1
  · have hcut' : L + e < o + c' := not_le.1 hcut
    have he : e ≤ o + c' - 1 - L := by omega
    have hmu2 : (2 * Q + 1) * e ≤ mu := le_trans (Nat.mul_le_mul_left _ he) hmu
    obtain ⟨mu', hmu'⟩ := Nat.exists_eq_add_of_le hmu2
    obtain ⟨la', hla'⟩ := Nat.exists_eq_add_of_le (le_trans he hla)
    obtain ⟨x', hx'⟩ := Nat.exists_eq_add_of_le hJ
    obtain ⟨n2, hn2⟩ := Nat.exists_eq_add_of_le hq
    have hZ := bc_mono_absorb w Fr Q g _ hD1 ν hn
    have hSur : bc_IT Fr (∏ j ∈ Finset.range Fr.J,
        (subst p n' O w n' r g (Del p n' O Fr g (j : ℤ))) ^ (y j + e - alpha p Fr k (j : ℤ) * c')) :=
      bc_IT_prod _ _ fun j _ => bc_IT_pow (hDl j) _
    have main : ∀ z ∈ AddSubmonoid.closure (bc_agen w Fr Q g (ν.sum fun _ m => m) 0),
        bc_Phi w Fr Q g hrk c' o mu la L (C (algebraMap O (KK O) (w ^ (i + x'))) * (A0 * z) *
          (subst p n' O w n' r g (R0 p n' O Fr g)) ^ c' *
          (∏ j ∈ Finset.range Fr.J, (subst p n' O w n' r g (Del p n' O Fr g j)) ^ la') *
          subst p n' O w n' r g (DtopProd p n' O Fr hrk g mu') *
          ((∏ j ∈ Finset.range Fr.J,
            (subst p n' O w n' r g (Del p n' O Fr g (j : ℤ))) ^ (y j + e - alpha p Fr k (j : ℤ) * c')) *
            (subst p n' O w n' r g (DtopProd p n' O Fr hrk g 1)) ^ n2 * H * Hh)) := by
      intro z hz
      refine AddSubmonoid.closure_induction (motive := fun z _ =>
        bc_Phi w Fr Q g hrk c' o mu la L (C (algebraMap O (KK O) (w ^ (i + x'))) * (A0 * z) *
          (subst p n' O w n' r g (R0 p n' O Fr g)) ^ c' *
          (∏ j ∈ Finset.range Fr.J, (subst p n' O w n' r g (Del p n' O Fr g j)) ^ la') *
          subst p n' O w n' r g (DtopProd p n' O Fr hrk g mu') *
          ((∏ j ∈ Finset.range Fr.J,
            (subst p n' O w n' r g (Del p n' O Fr g (j : ℤ))) ^ (y j + e - alpha p Fr k (j : ℤ) * c')) *
            (subst p n' O w n' r g (DtopProd p n' O Fr hrk g 1)) ^ n2 * H * Hh))) ?_ ?_ ?_ hz
      · rintro _ ⟨A1, H1, hA1, hH1, rfl⟩
        obtain ⟨τ', hv, ht, hlev, hsym⟩ := bc_sym_of_KP w Fr Q g hrk c' mu' la' (i + x') (isKeyProduct_mul hk hA1)
          (bc_IT_mul hH1 (bc_IT_mul (bc_IT_mul (bc_IT_mul hSur (bc_IT_pow hDD n2)) hi) hh))
        have hlev2 : τ'.level = L + e := by rw [hlev]; omega
        refine ⟨[(τ', mu', la')], 0, inWj_zero _, ?_, ?_⟩
        · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          rw [hsym]; ring
        · intro yy hyy
          rw [List.mem_singleton] at hyy
          subst hyy
          refine ⟨hv, ht, by simp only; omega, by simp only; omega, ?_, ?_⟩
          · simp only
            rw [hlev2, hmu']
            push_cast
            ring
          · simp only
            rw [hlev2, hla']
            push_cast
            ring
      · simp only [mul_zero, zero_mul]
        exact bc_Phi_rho w Fr Q g hrk c' o mu la L (inWj_zero _)
      · intro z1 z2 _ _ h1 h2
        have := bc_Phi_add w Fr Q g hrk c' o mu la L h1 h2
        convert this using 1
        ring
    have hDel : (∏ j ∈ Finset.range Fr.J, (subst p n' O w n' r g (Del p n' O Fr g (j : ℤ))) ^ y j) *
        (∏ j ∈ Finset.range Fr.J, (subst p n' O w n' r g (Del p n' O Fr g (j : ℤ))) ^ la) =
        (subst p n' O w n' r g (R0 p n' O Fr g)) ^ c' *
        (∏ j ∈ Finset.range Fr.J, (subst p n' O w n' r g (Del p n' O Fr g (j : ℤ))) ^ la') *
        (∏ j ∈ Finset.range Fr.J,
            (subst p n' O w n' r g (Del p n' O Fr g (j : ℤ))) ^ (y j + e - alpha p Fr k (j : ℤ) * c')) := by
      unfold R0
      rw [map_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j hj => ?_
      have h1 := hy j (Finset.mem_range.1 hj)
      rw [hβ j] at h1
      rw [map_pow, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      omega
    have hfin := main _ hZ
    convert hfin using 1
    rw [bc_DtopProd_pow w Fr g hrk mu, bc_DtopProd_pow w Fr g hrk mu', hmu', hn2]
    conv_lhs => rw [hx']
    simp only [pow_add, map_mul]
    linear_combination (C (algebraMap O (KK O) (w ^ i)) * C (algebraMap O (KK O) (w ^ (ν.sum fun _ m => m))) *
      C (algebraMap O (KK O) (w ^ x')) * A0 * monomial ν 1 * H * Hh *
      (subst p n' O w n' r g (DtopProd p n' O Fr hrk g 1)) ^ (ν.sum fun _ m => m) *
      (subst p n' O w n' r g (DtopProd p n' O Fr hrk g 1)) ^ n2 *
      (subst p n' O w n' r g (DtopProd p n' O Fr hrk g 1)) ^ mu') * hDel

end Absorb2

section Facts

variable {p n' r k : ℕ} [Fact p.Prime] [NeZero n'] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p n') O]
  (w : O) (Fr : Frames n' r)

local notation "PP" => MvPolynomial (TV n' k) (KK O)

def bc_St (Fr : Frames n' r) (k : ℕ) : Set (TV n' k) := {v | ¬ IsNormal r v ∧ v.1 ∈ Fr.TT}

/- English proof (translation)
Rewrite `hh` using `[mem_supported]`. Conclude with `⟨h, fun v hv => (hh (Finset.mem_coe.2 hv)).1, fun v hv => (hh (Finset.mem_coe.2 hv)).2, rfl⟩`.
-/
theorem bc_IT_of_supp (h : MvPolynomial (TV n' k) O) (hh : h ∈ supported O (bc_St Fr k)) :
    bc_IT Fr (MvPolynomial.map (algebraMap O (KK O)) h) := by
  rw [mem_supported] at hh
  exact ⟨h, fun v hv => (hh (Finset.mem_coe.2 hv)).1, fun v hv => (hh (Finset.mem_coe.2 hv)).2, rfl⟩

/- English proof (translation)
Take `⟨h, rfl, hv⟩` from `exists_map_of_inWj0 h0`. Rewrite `hP` using `[mem_supported]`. Conclude with `⟨h, fun v hv' => (hP (Finset.mem_coe.2 (hv hv'))).1, fun v hv' => (hP (Finset.mem_coe.2 (hv hv'))).2, rfl⟩`.
-/
theorem bc_IT_of_K {P : PP} (h0 : InWj w P 0) (hP : P ∈ supported (KK O) (bc_St Fr k)) : bc_IT Fr P := by
  obtain ⟨h, rfl, hv⟩ := exists_map_of_inWj0 h0
  rw [mem_supported] at hP
  exact ⟨h, fun v hv' => (hP (Finset.mem_coe.2 (hv hv'))).1, fun v hv' => (hP (Finset.mem_coe.2 (hv hv'))).2, rfl⟩

/- English proof (translation)
Use `bc_IT_of_K w Fr (subst_integral w r hg (frame_determinant_integral Fr w g j)) ?_` and prove the remaining obligations. Unfold `Del minorI`. Rewrite using `[dif_pos (first_columns_card hrk), AlgHom.map_det]`. Use `det_mem_subalgebra_alt _ _ fun l i => ?_` and prove the remaining obligations. Use `show subst p n' O w n' r g (twRow p n' O Fr g j l.val ((Ifirst r k).orderEmbOfFin (first_columns_card hrk) i)) ∈ _`.

Unfold `twRow`. Rewrite using `[map_pow, subst_xg w r hg hn _ (hV.2.2.2.2.1 j l.val l.2).2]`. Use `pow_mem ?_ _` and prove the remaining obligations. Establish `hb : ((Ifirst r k).orderEmbOfFin (first_columns_card hrk) i).val < r`. Use `Finset.orderEmbOfFin_mem (Ifirst r k) (first_columns_card hrk) i` as an intermediate fact.

Establish `h2 : ∀ b ∈ Ifirst r k, b.val < r` using `fun b hb => (Finset.mem_filter.1 hb).2`. Conclude with `h2 _ this`. Establish `hE` using `(posOf_even hn (Fr.fr j l.val)).2 (hV.2.2.2.2.1 j l.val l.2).2`. Establish `hN : ¬ IsNormal r ((posOf n' (Fr.fr j l.val), (Ifirst r k).orderEmbOfFin (first_columns_card hrk) i) : TV n' k)`. Rewrite using `[normal_variable_iff_even_index hE]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[newVar, if_neg hN]`. Conclude with `X_mem_supported.2 ⟨hN, (hV.2.2.2.2.1 j l.val l.2).1⟩`.
-/
theorem bc_IT_Del {L₁ N₁ : ℕ} (hV : Fr.Valid L₁ N₁) (hn : Even n') (hrk : r ≤ k)
    {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (j : ℤ) :
    bc_IT Fr (subst p n' O w n' r g (Del p n' O Fr g j)) := by
  refine bc_IT_of_K w Fr (subst_integral w r hg (frame_determinant_integral Fr w g j)) ?_
  unfold Del minorI
  rw [dif_pos (first_columns_card hrk), AlgHom.map_det]
  refine det_mem_subalgebra_alt _ _ fun l i => ?_
  show subst p n' O w n' r g (twRow p n' O Fr g j l.val ((Ifirst r k).orderEmbOfFin (first_columns_card hrk) i)) ∈ _
  unfold twRow
  rw [map_pow, subst_xg w r hg hn _ (hV.2.2.2.2.1 j l.val l.2).2]
  refine pow_mem ?_ _
  have hb : ((Ifirst r k).orderEmbOfFin (first_columns_card hrk) i).val < r := by
    have := Finset.orderEmbOfFin_mem (Ifirst r k) (first_columns_card hrk) i
    have h2 : ∀ b ∈ Ifirst r k, b.val < r := fun b hb => (Finset.mem_filter.1 hb).2
    exact h2 _ this
  have hE := (posOf_even hn (Fr.fr j l.val)).2 (hV.2.2.2.2.1 j l.val l.2).2
  have hN : ¬ IsNormal r ((posOf n' (Fr.fr j l.val), (Ifirst r k).orderEmbOfFin (first_columns_card hrk) i) : TV n' k) := by
    rw [normal_variable_iff_even_index hE]; omega
  rw [newVar, if_neg hN]
  exact X_mem_supported.2 ⟨hN, (hV.2.2.2.2.1 j l.val l.2).1⟩

/- English proof (translation)
Establish `hA` using `window_holds_even_tops n' r Fr L₁ N₁ hV hn hr s`. Rewrite using `[subst_top_determinant w Fr hrk hg hn s hA]`. Use `bc_IT_of_supp Fr _ (det_mem_subalgebra_alt _ _ (row_power_mem_supported Fr hrk s _ fun l i => ?_))` and prove the remaining obligations. Establish `hE` using `(posOf_even hn _).2 (hA l.val l.2).1`. Use `⟨?_, (hA l.val l.2).2.1⟩` and prove the remaining obligations.

Rewrite using `[normal_variable_iff_even_index hE]`. Use `i.2` as an intermediate fact. Simplify using `only [Fin.coe_castLE]`. Use linear arithmetic over natural numbers and integers.
-/
theorem bc_IT_Dtop {L₁ N₁ : ℕ} (hV : Fr.Valid L₁ N₁) (hn : Even n') (hr : 1 ≤ r) (hrk : r ≤ k)
    {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (s : ℤ) :
    bc_IT Fr (subst p n' O w n' r g (Dtop p n' O Fr hrk g s)) := by
  have hA := window_holds_even_tops n' r Fr L₁ N₁ hV hn hr s
  rw [subst_top_determinant w Fr hrk hg hn s hA]
  refine bc_IT_of_supp Fr _ (det_mem_subalgebra_alt _ _ (row_power_mem_supported Fr hrk s _ fun l i => ?_))
  have hE := (posOf_even hn _).2 (hA l.val l.2).1
  refine ⟨?_, (hA l.val l.2).2.1⟩
  rw [normal_variable_iff_even_index hE]
  have := i.2
  simp only [Fin.coe_castLE]
  omega

end Facts

def bc_RestTail (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p n' r k : ℕ) [Fact p.Prime] [NeZero n'] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF p n') O] (S : UniformizedDVR p O), OHyp p n' O S → CommonHypotheses p n' r k →
  ∀ (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ → ∀ Q : ℕ, TwistBound p Fr Q →
  ∀ g : Matrix (Fin k) (Fin k) (WF p n'), IsGLW g →
  ∀ (ka ka0 : MvPolynomial (TV n' k) (KK O)) (o : ℕ), IsKey p n' S.w n' r Q g ka o ka0 → OnTops Fr ka →
    OnTops Fr ka0 →
    subst p n' O S.w n' r g ka - ka0 ∈ AddSubmonoid.closure
      (bc_gen S.w Fr Q g (fun j : ℕ => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ))) (o, 0) 1)

/- English proof (translation)
Introduce `p n' r k _ _ O _ _ _ _ S hO hH Fr L₁ N₁ hV Q hQ g hg c' o mu la τ hτ hτT hlev hmu hla`. Establish `hn : Even n'` using `hH.2.2.2.2`. Establish `hrk : r ≤ k` using `hH.2.2.1`. Establish `hr1 : 1 ≤ r` using `by have := hH.2.1; omega`. Establish `hDl : ∀ j : ℕ, bc_IT Fr (subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ)))` using `fun j => bc_IT_Del S.w Fr hV hn hrk hg j`.

Establish `hDt : ∀ s : ℤ, bc_IT Fr (subst p n' O S.w n' r g (Dtop p n' O Fr hrk g s))` using `fun s => bc_IT_Dtop S.w Fr hV hn hr1 hrk hg s`. Establish `hDD : bc_IT Fr (subst p n' O S.w n' r g (DtopProd p n' O Fr hrk g 1))`. Unfold `DtopProd`. Rewrite using `[map_prod]`. Conclude with `bc_IT_prod _ _ fun s _ => by rw [map_pow]; exact bc_IT_pow (hDt _) 1`.

Establish `hwne : algebraMap O (KK O) S.w ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 S.w_irr.ne_zero`. Establish `hw1 : (C (algebraMap O (KK O) S.w) : MvPolynomial (TV n' k) (KK O)) * C (wInv S.w) = 1`. Rewrite using `[← C_mul, wInv, mul_inv_cancel₀ hwne, C_1]`. Establish `hD1 : ∀ v : TV n' k, IsNormal r v → v.1 ∈ Fr.TT → C (algebraMap O (KK O) S.w) * X v * subst p n' O S.w n' r g (DtopProd p n' O Fr hrk g 1) ∈ AddSubmonoid.closure (bc_agen S.w Fr Q g 1 0)`. Introduce and unpack `⟨s, b⟩ hN hs`.

Take `⟨n, ka, ka0, H, hc, heq⟩` from `hK p n' r k O S hO hH Fr L₁ N₁ hV Q hQ g hg s hs b hN`. Establish `hsplit : subst p n' O S.w n' r g (DtopProd p n' O Fr hrk g 1) =`. Substitute `p n' O S.w n' r g (Dtop p n' O Fr hrk g (s.val : ℤ)) * ∏ s' ∈ Fr.TT.erase s, subst p n' O S.w n' r g (Dtop p n' O Fr hrk g (s'.val : ℤ)) := by` using the available equality. Unfold `DtopProd`. Simplify using `only [pow_one]`.

Rewrite using `[map_prod, Finset.mul_prod_erase Fr.TT (fun s' => subst p n' O S.w n' r g (Dtop p n' O Fr hrk g (s'.val : ℤ))) hs]`. Establish `hrest : bc_IT Fr (∏ s' ∈ Fr.TT.erase s, subst p n' O S.w n' r g (Dtop p n' O Fr hrk g (s'.val : ℤ)))` using `bc_IT_prod _ _ fun s' _ => hDt _`. Establish `hsum : C (algebraMap O (KK O) S.w) * X (s, b) * subst p n' O S.w n' r g (DtopProd p n' O Fr hrk g 1) = ∑ i, ka0 i * (MvPolynomial.map (algebraMap O (KK O)) (H i) * ∏ s' ∈ Fr.TT.erase s, subst p n' O S.w n' r g (Dtop p n' O Fr hrk g (s'.val : ℤ)))`. Rewrite using `[hsplit]`. Establish `e1 : C (algebraMap O (KK O) S.w) * X (s, b) * (subst p n' O S.w n' r g (Dtop p n' O Fr hrk g (s.val : ℤ)) * ∏ s' ∈ Fr.TT.erase s, subst p n' O S.w n' r g (Dtop p n' O Fr hrk g (s'.val : ℤ))) = C (algebraMap O (KK O) S.w) * (X (s, b) * subst p n' O S.w n' r g (Dtop p n' O Fr hrk g …` using `by ring`.

Rewrite using `[e1, heq, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Take the linear combination `(MvPolynomial.map (algebraMap O (KK O)) (H i) * ka0 i * ∏ s' ∈ Fr.TT.erase s, subst p n' O S.w n' r g (Dtop p n' O Fr hrk g (s'.val : ℤ))) * hw1`. Rewrite using `[hsum]`. Use `sum_mem fun i _ => AddSubmonoid.subset_closure ⟨ka0 i, _, isKeyProduct_of_isKey S.w Fr Q g (hc i).1 (hc i).2.2.1 (hc i).2.2.2.1, bc_IT_mul ⟨H i, fun v hv => ?_, (hc i).2.2.2.2, rfl⟩ hrest, rfl⟩` and prove the remaining obligations.

Establish `h1` using `(hc i).2.1 v hv`. Unfold `IsNormal`. Rewrite using `[if_pos h1.1]`. Use `h1.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hmul` using `bc_gen_mul S.w Fr Q g (fun j : ℕ => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ)))`. Establish `hone` using `bc_gen_one S.w Fr Q g (fun j : ℕ => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ)))`. Establish `hmono` using `bc_gen_mono S.w Fr Q g (fun j : ℕ => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ)))`. Establish `ha : ∀ l ∈ (Finset.univ : Finset (Fin τ.n)), τ.ka0 l ∈ AddSubmonoid.closure (bc_gen S.w Fr Q g (fun j : ℕ => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ))) (τ.o l, 0) 0)`. Introduce `l _`.

Use `AddSubmonoid.subset_closure ⟨0, τ.o l, 0, τ.ka0 l, 0, fun _ => 0, 1, isKeyProduct_of_isKey S.w Fr Q g (hτ.1 l) (hτT.1 l).1 (hτT.1 l).2, bc_IT_one, fun v hv => by simp at hv, by simp, le_rfl, by simp, by simp, fun j _ => by simp, by simp⟩` and prove the remaining obligations. Establish `hb : ∀ l ∈ (Finset.univ : Finset (Fin τ.n)), subst p n' O S.w n' r g (τ.ka l) - τ.ka0 l ∈ AddSubmonoid.closure (bc_gen S.w Fr Q g (fun j : ℕ => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ))) (τ.o l, 0) 1)` using `fun l _ => hT p n' r k O S hO hH Fr L₁ N₁ hV Q hQ g hg _ _ _ (hτ.1 l) (hτT.1 l).1 (hτT.1 l).2`. Establish `hR0 : subst p n' O S.w n' r g (R0 p n' O Fr g) ∈ AddSubmonoid.closure (bc_gen S.w Fr Q g (fun j : ℕ => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ))) (0, fun j : ℕ => alpha p Fr k (j : ℤ)) 0)`. Use `AddSubmonoid.subset_closure ⟨0, 0, 0, 1, 0, fun j : ℕ => alpha p Fr k (j : ℤ), 1, isKeyProduct_one S.w Fr Q g, bc_IT_one, fun v hv => by simp at hv, by simp, le_rfl, by simp, by simp, fun j _ => by simp, ?_⟩` and prove the remaining obligations. Unfold `R0`.

Simplify using `[map_prod, map_pow]`. Establish `hR1 : subst p n' O S.w n' r g (Rloc p n' O Fr g) - subst p n' O S.w n' r g (R0 p n' O Fr g) ∈ AddSubmonoid.closure (bc_gen S.w Fr Q g (fun j : ℕ => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ))) (0, fun j : ℕ => alpha p Fr k (j : ℤ)) 1)`. Take `⟨n, e, ex, nu, H, hc, heq⟩` from `hL p n' r k O S hO hH Fr L₁ N₁ hV g hg`. Rewrite using `[← map_sub, heq]`. Use `sum_mem fun i _ => AddSubmonoid.subset_closure ⟨e i, 0, e i, 1, nu i, ex i, MvPolynomial.map (algebraMap O (KK O)) (H i), isKeyProduct_one S.w Fr Q g, ⟨H i, fun v hv => ?_, (hc i).2.2.2.2.1, rfl⟩, (hc i).2.1, by simp, (hc i).1, (hc i).2.2.1, le_trans (hc i).2.2.1 (Nat.le_mul_of_p …` and prove the remaining obligations.

Establish `h1` using `(hc i).2.2.2.1 v hv`. Unfold `IsNormal`. Rewrite using `[if_pos h1.1]`. Use `h1.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `(hc i).2.2.2.2.2 j hj` as an intermediate fact. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Establish `hX0` using `bc_gr_prod hmul hone Finset.univ τ.ka0 (fun l => ((τ.o l, 0) : ℕ × (ℕ → ℕ))) ha`. Establish `hXt` using `bc_gr_tel hmul hone hmono Finset.univ τ.ka0 (fun l => subst p n' O S.w n' r g (τ.ka l) - τ.ka0 l) (fun l => ((τ.o l, 0) : ℕ × (ℕ → ℕ))) ha hb`.

Establish `hY0` using `bc_gr_prod hmul hone (Finset.range c') (fun _ => subst p n' O S.w n' r g (R0 p n' O Fr g)) (fun _ => ((0, fun j : ℕ => alpha p Fr k (j : ℤ)) : ℕ × (ℕ → ℕ))) (fun _ _ => hR0)`. Establish `hYt` using `bc_gr_tel hmul hone hmono (Finset.range c') (fun _ => subst p n' O S.w n' r g (R0 p n' O Fr g)) (fun _ => subst p n' O S.w n' r g (Rloc p n' O Fr g) - subst p n' O S.w n' r g (R0 p n' O Fr g)) (fun _ => ((0, fun j : ℕ => alpha p Fr k (j : ℤ)) : ℕ × (ℕ → ℕ))) (fun _ _ => hR0) (fun …`. Simplify using `only [add_sub_cancel, Finset.prod_const, Finset.card_range] at hXt hYt hY0`. Establish `hX : ∏ l, subst p n' O S.w n' r g (τ.ka l) ∈ AddSubmonoid.closure (bc_gen S.w Fr Q g (fun j : ℕ => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ))) (∑ l, ((τ.o l, 0) : ℕ × (ℕ → ℕ))) 0)`. Use `add_mem hX0 (AddSubmonoid.closure_mono (hmono _) hXt)` as an intermediate fact.

Simplify using `using this`. Establish `hdiff : (∏ l, subst p n' O S.w n' r g (τ.ka l)) * (subst p n' O S.w n' r g (Rloc p n' O Fr g)) ^ c' - (∏ l, τ.ka0 l) * (subst p n' O S.w n' r g (R0 p n' O Fr g)) ^ c' ∈ AddSubmonoid.closure (bc_gen S.w Fr Q g (fun j : ℕ => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ))) (∑ l, …`. Establish `e1` using `bc_gr_mul hmul hX hYt`. Establish `e2` using `bc_gr_mul hmul hXt hY0`. Establish `hidx : (∑ l, ((τ.o l, 0) : ℕ × (ℕ → ℕ))) + ∑ _t ∈ Finset.range c', ((0, fun j : ℕ => alpha p Fr k (j : ℤ)) : ℕ × (ℕ → ℕ)) = (∑ l, τ.o l, fun j : ℕ => alpha p Fr k (j : ℤ) * c')`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Simplify using `[Prod.fst_sum]`. Use function extensionality and compare the values at `j`. Simplify using `[Prod.snd_sum, mul_comm]`. Rewrite `e1`, `e2` using `[hidx]`.

Establish `hid : (∏ l, subst p n' O S.w n' r g (τ.ka l)) * (subst p n' O S.w n' r g (Rloc p n' O Fr g)) ^ c' - (∏ l, τ.ka0 l) * (subst p n' O S.w n' r g (R0 p n' O Fr g)) ^ c' = (∏ l, subst p n' O S.w n' r g (τ.ka l)) * ((subst p n' O S.w n' r g (Rloc p n' O Fr g)) ^ c' - (subst p n' O S.w …`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hid]`. Conclude with `add_mem (by simpa using e1) (by simpa using e2)`. Establish `hsubN : ((o + c' - 1 - τ.level : ℕ) : ℤ) = (o : ℤ) + c' - 1 - τ.level` using `by omega`.

Establish `hmuN : (2 * Q + 1) * (o + c' - 1 - τ.level) ≤ mu`. Establish `: (((2 * Q + 1) * (o + c' - 1 - τ.level) : ℕ) : ℤ) ≤ mu`. Rewrite using `[Nat.cast_mul, hsubN]`. Use `push_cast`. Conclude with `hmu`.

Conclude with `this` after adjusting the coercions. Establish `hlaN : o + c' - 1 - τ.level ≤ la` using `by omega`. Establish `hPhi : bc_Phi S.w Fr Q g hrk c' o mu la τ.level (C (algebraMap O (KK O) (S.w ^ τ.i)) * ((∏ l, subst p n' O S.w n' r g (τ.ka l)) * (subst p n' O S.w n' r g (Rloc p n' O Fr g)) ^ c' - (∏ l, τ.ka0 l) * (subst p n' O S.w n' r g (R0 p n' O Fr g)) ^ c') * (∏ j ∈ Finset.range Fr.J, (sub …`. Substitute `p n' O S.w n' r g (DtopProd p n' O Fr hrk g mu) * MvPolynomial.map (algebraMap O (KK O)) τ.h) := by` using the available equality. Use `AddSubmonoid.closure_induction (motive := fun z _ => bc_Phi S.w Fr Q g hrk c' o mu la τ.level (C (algebraMap O (KK O) (S.w ^ τ.i)) * z * (∏ j ∈ Finset.range Fr.J, (subst p n' O S.w n' r g (Del p n' O Fr g j)) ^ la) *` and prove the remaining obligations.

Substitute `p n' O S.w n' r g (DtopProd p n' O Fr hrk g mu) * MvPolynomial.map (algebraMap O (KK O)) τ.h))` using the available equality. Use the proof step `?_ ?_ ?_ hdiff`. Introduce `γ hγ`. Conclude with `bc_absorb S.w Fr Q g hrk c' o mu la τ.level hDl hDD hD1 τ.i (∑ l, τ.o l) rfl ⟨τ.h, hτ.2, hτT.2, rfl⟩ hmuN hlaN _ (fun _ => rfl) hγ`. Simplify using `only [mul_zero, zero_mul]`.

Conclude with `bc_Phi_rho S.w Fr Q g hrk c' o mu la τ.level (inWj_zero _)`. Introduce `z1 z2 _ _ h1 h2`. Use `bc_Phi_add S.w Fr Q g hrk c' o mu la τ.level h1 h2` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Take `⟨l, ρ, hρ, heq, hl⟩` from `hPhi`. Use `⟨l.length, fun t => l[t.1].1, fun t => l[t.1].2.1, fun t => l[t.1].2.2, ρ, hρ, ?_, fun t => hl _ (List.getElem_mem t.2)⟩` and prove the remaining obligations. Rewrite using `[heq, Fin.sum_univ_fun_getElem l (fun y => y.1.sym p n' S.w Fr hrk g c' y.2.1 y.2.2)]`.
-/
theorem bc_claim_of_tail (D : Formalism.BasicNotions.D7) (hL : Conclusion2 D) (hK : PointsLemma D) (hT : bc_RestTail D) : DifferenceClaimInCoordinates D := by
  intro p n' r k _ _ O _ _ _ _ S hO hH Fr L₁ N₁ hV Q hQ g hg c' o mu la τ hτ hτT hlev hmu hla
  have hn : Even n' := hH.2.2.2.2
  have hrk : r ≤ k := hH.2.2.1
  have hr1 : 1 ≤ r := by have := hH.2.1; omega
  have hDl : ∀ j : ℕ, bc_IT Fr (subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ))) :=
    fun j => bc_IT_Del S.w Fr hV hn hrk hg j
  have hDt : ∀ s : ℤ, bc_IT Fr (subst p n' O S.w n' r g (Dtop p n' O Fr hrk g s)) :=
    fun s => bc_IT_Dtop S.w Fr hV hn hr1 hrk hg s
  have hDD : bc_IT Fr (subst p n' O S.w n' r g (DtopProd p n' O Fr hrk g 1)) := by
    unfold DtopProd
    rw [map_prod]
    exact bc_IT_prod _ _ fun s _ => by rw [map_pow]; exact bc_IT_pow (hDt _) 1
  have hwne : algebraMap O (KK O) S.w ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 S.w_irr.ne_zero
  have hw1 : (C (algebraMap O (KK O) S.w) : MvPolynomial (TV n' k) (KK O)) * C (wInv S.w) = 1 := by
    rw [← C_mul, wInv, mul_inv_cancel₀ hwne, C_1]
  have hD1 : ∀ v : TV n' k, IsNormal r v → v.1 ∈ Fr.TT →
      C (algebraMap O (KK O) S.w) * X v * subst p n' O S.w n' r g (DtopProd p n' O Fr hrk g 1) ∈
        AddSubmonoid.closure (bc_agen S.w Fr Q g 1 0) := by
    rintro ⟨s, b⟩ hN hs
    obtain ⟨n, ka, ka0, H, hc, heq⟩ := hK p n' r k O S hO hH Fr L₁ N₁ hV Q hQ g hg s hs b hN
    have hsplit : subst p n' O S.w n' r g (DtopProd p n' O Fr hrk g 1) =
        subst p n' O S.w n' r g (Dtop p n' O Fr hrk g (s.val : ℤ)) *
          ∏ s' ∈ Fr.TT.erase s, subst p n' O S.w n' r g (Dtop p n' O Fr hrk g (s'.val : ℤ)) := by
      unfold DtopProd
      simp only [pow_one]
      rw [map_prod, Finset.mul_prod_erase Fr.TT (fun s' => subst p n' O S.w n' r g (Dtop p n' O Fr hrk g (s'.val : ℤ))) hs]
    have hrest : bc_IT Fr (∏ s' ∈ Fr.TT.erase s, subst p n' O S.w n' r g (Dtop p n' O Fr hrk g (s'.val : ℤ))) :=
      bc_IT_prod _ _ fun s' _ => hDt _
    have hsum : C (algebraMap O (KK O) S.w) * X (s, b) * subst p n' O S.w n' r g (DtopProd p n' O Fr hrk g 1) =
        ∑ i, ka0 i * (MvPolynomial.map (algebraMap O (KK O)) (H i) *
          ∏ s' ∈ Fr.TT.erase s, subst p n' O S.w n' r g (Dtop p n' O Fr hrk g (s'.val : ℤ))) := by
      rw [hsplit]
      have e1 : C (algebraMap O (KK O) S.w) * X (s, b) * (subst p n' O S.w n' r g (Dtop p n' O Fr hrk g (s.val : ℤ)) *
          ∏ s' ∈ Fr.TT.erase s, subst p n' O S.w n' r g (Dtop p n' O Fr hrk g (s'.val : ℤ))) =
          C (algebraMap O (KK O) S.w) * (X (s, b) * subst p n' O S.w n' r g (Dtop p n' O Fr hrk g (s.val : ℤ))) *
          ∏ s' ∈ Fr.TT.erase s, subst p n' O S.w n' r g (Dtop p n' O Fr hrk g (s'.val : ℤ)) := by ring
      rw [e1, heq, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      linear_combination (MvPolynomial.map (algebraMap O (KK O)) (H i) * ka0 i *
        ∏ s' ∈ Fr.TT.erase s, subst p n' O S.w n' r g (Dtop p n' O Fr hrk g (s'.val : ℤ))) * hw1
    rw [hsum]
    refine sum_mem fun i _ => AddSubmonoid.subset_closure ⟨ka0 i, _,
      isKeyProduct_of_isKey S.w Fr Q g (hc i).1 (hc i).2.2.1 (hc i).2.2.2.1,
      bc_IT_mul ⟨H i, fun v hv => ?_, (hc i).2.2.2.2, rfl⟩ hrest, rfl⟩
    have h1 := (hc i).2.1 v hv
    unfold IsNormal
    rw [if_pos h1.1]
    have := h1.2
    omega

  have hmul := bc_gen_mul S.w Fr Q g (fun j : ℕ => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ)))
  have hone := bc_gen_one S.w Fr Q g (fun j : ℕ => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ)))
  have hmono := bc_gen_mono S.w Fr Q g (fun j : ℕ => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ)))
  have ha : ∀ l ∈ (Finset.univ : Finset (Fin τ.n)), τ.ka0 l ∈ AddSubmonoid.closure
      (bc_gen S.w Fr Q g (fun j : ℕ => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ))) (τ.o l, 0) 0) := by
    intro l _
    refine AddSubmonoid.subset_closure ⟨0, τ.o l, 0, τ.ka0 l, 0, fun _ => 0, 1,
      isKeyProduct_of_isKey S.w Fr Q g (hτ.1 l) (hτT.1 l).1 (hτT.1 l).2, bc_IT_one, fun v hv => by simp at hv, by simp, le_rfl,
      by simp, by simp, fun j _ => by simp, by simp⟩
  have hb : ∀ l ∈ (Finset.univ : Finset (Fin τ.n)), subst p n' O S.w n' r g (τ.ka l) - τ.ka0 l ∈
      AddSubmonoid.closure
      (bc_gen S.w Fr Q g (fun j : ℕ => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ))) (τ.o l, 0) 1) :=
    fun l _ => hT p n' r k O S hO hH Fr L₁ N₁ hV Q hQ g hg _ _ _ (hτ.1 l) (hτT.1 l).1 (hτT.1 l).2
  have hR0 : subst p n' O S.w n' r g (R0 p n' O Fr g) ∈ AddSubmonoid.closure
      (bc_gen S.w Fr Q g (fun j : ℕ => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ)))
        (0, fun j : ℕ => alpha p Fr k (j : ℤ)) 0) := by
    refine AddSubmonoid.subset_closure ⟨0, 0, 0, 1, 0, fun j : ℕ => alpha p Fr k (j : ℤ), 1, isKeyProduct_one S.w Fr Q g,
      bc_IT_one, fun v hv => by simp at hv, by simp, le_rfl, by simp, by simp, fun j _ => by simp, ?_⟩
    unfold R0
    simp [map_prod, map_pow]
  have hR1 : subst p n' O S.w n' r g (Rloc p n' O Fr g) - subst p n' O S.w n' r g (R0 p n' O Fr g) ∈
      AddSubmonoid.closure
      (bc_gen S.w Fr Q g (fun j : ℕ => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ)))
        (0, fun j : ℕ => alpha p Fr k (j : ℤ)) 1) := by
    obtain ⟨n, e, ex, nu, H, hc, heq⟩ := hL p n' r k O S hO hH Fr L₁ N₁ hV g hg
    rw [← map_sub, heq]
    refine sum_mem fun i _ => AddSubmonoid.subset_closure ⟨e i, 0, e i, 1, nu i, ex i,
      MvPolynomial.map (algebraMap O (KK O)) (H i), isKeyProduct_one S.w Fr Q g,
      ⟨H i, fun v hv => ?_, (hc i).2.2.2.2.1, rfl⟩, (hc i).2.1, by simp, (hc i).1, (hc i).2.2.1,
      le_trans (hc i).2.2.1 (Nat.le_mul_of_pos_left _ (by omega)), fun j hj => ?_, by ring⟩
    · have h1 := (hc i).2.2.2.1 v hv
      unfold IsNormal
      rw [if_pos h1.1]
      have := h1.2
      omega
    · have := (hc i).2.2.2.2.2 j hj
      simp only
      omega
  have hX0 := bc_gr_prod hmul hone Finset.univ τ.ka0 (fun l => ((τ.o l, 0) : ℕ × (ℕ → ℕ))) ha
  have hXt := bc_gr_tel hmul hone hmono Finset.univ τ.ka0 (fun l => subst p n' O S.w n' r g (τ.ka l) - τ.ka0 l)
    (fun l => ((τ.o l, 0) : ℕ × (ℕ → ℕ))) ha hb
  have hY0 := bc_gr_prod hmul hone (Finset.range c') (fun _ => subst p n' O S.w n' r g (R0 p n' O Fr g))
    (fun _ => ((0, fun j : ℕ => alpha p Fr k (j : ℤ)) : ℕ × (ℕ → ℕ))) (fun _ _ => hR0)
  have hYt := bc_gr_tel hmul hone hmono (Finset.range c') (fun _ => subst p n' O S.w n' r g (R0 p n' O Fr g))
    (fun _ => subst p n' O S.w n' r g (Rloc p n' O Fr g) - subst p n' O S.w n' r g (R0 p n' O Fr g))
    (fun _ => ((0, fun j : ℕ => alpha p Fr k (j : ℤ)) : ℕ × (ℕ → ℕ))) (fun _ _ => hR0) (fun _ _ => hR1)
  simp only [add_sub_cancel, Finset.prod_const, Finset.card_range] at hXt hYt hY0
  have hX : ∏ l, subst p n' O S.w n' r g (τ.ka l) ∈ AddSubmonoid.closure
      (bc_gen S.w Fr Q g (fun j : ℕ => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ)))
        (∑ l, ((τ.o l, 0) : ℕ × (ℕ → ℕ))) 0) := by
    have := add_mem hX0 (AddSubmonoid.closure_mono (hmono _) hXt)
    simpa using this
  have hdiff : (∏ l, subst p n' O S.w n' r g (τ.ka l)) * (subst p n' O S.w n' r g (Rloc p n' O Fr g)) ^ c' -
      (∏ l, τ.ka0 l) * (subst p n' O S.w n' r g (R0 p n' O Fr g)) ^ c' ∈ AddSubmonoid.closure
      (bc_gen S.w Fr Q g (fun j : ℕ => subst p n' O S.w n' r g (Del p n' O Fr g (j : ℤ)))
        (∑ l, τ.o l, fun j : ℕ => alpha p Fr k (j : ℤ) * c') 1) := by
    have e1 := bc_gr_mul hmul hX hYt
    have e2 := bc_gr_mul hmul hXt hY0
    have hidx : (∑ l, ((τ.o l, 0) : ℕ × (ℕ → ℕ))) +
        ∑ _t ∈ Finset.range c', ((0, fun j : ℕ => alpha p Fr k (j : ℤ)) : ℕ × (ℕ → ℕ)) =
        (∑ l, τ.o l, fun j : ℕ => alpha p Fr k (j : ℤ) * c') := by
      refine Prod.ext ?_ ?_
      · simp [Prod.fst_sum]
      · funext j
        simp [Prod.snd_sum, mul_comm]
    rw [hidx] at e1 e2
    have hid : (∏ l, subst p n' O S.w n' r g (τ.ka l)) * (subst p n' O S.w n' r g (Rloc p n' O Fr g)) ^ c' -
      (∏ l, τ.ka0 l) * (subst p n' O S.w n' r g (R0 p n' O Fr g)) ^ c' =
      (∏ l, subst p n' O S.w n' r g (τ.ka l)) * ((subst p n' O S.w n' r g (Rloc p n' O Fr g)) ^ c' -
        (subst p n' O S.w n' r g (R0 p n' O Fr g)) ^ c') +
      (∏ l, subst p n' O S.w n' r g (τ.ka l) - ∏ l, τ.ka0 l) * (subst p n' O S.w n' r g (R0 p n' O Fr g)) ^ c' := by
      ring
    rw [hid]
    exact add_mem (by simpa using e1) (by simpa using e2)
  have hsubN : ((o + c' - 1 - τ.level : ℕ) : ℤ) = (o : ℤ) + c' - 1 - τ.level := by omega
  have hmuN : (2 * Q + 1) * (o + c' - 1 - τ.level) ≤ mu := by
    have : (((2 * Q + 1) * (o + c' - 1 - τ.level) : ℕ) : ℤ) ≤ mu := by
      rw [Nat.cast_mul, hsubN]; push_cast; exact hmu
    exact_mod_cast this
  have hlaN : o + c' - 1 - τ.level ≤ la := by omega
  have hPhi : bc_Phi S.w Fr Q g hrk c' o mu la τ.level (C (algebraMap O (KK O) (S.w ^ τ.i)) *
      ((∏ l, subst p n' O S.w n' r g (τ.ka l)) * (subst p n' O S.w n' r g (Rloc p n' O Fr g)) ^ c' -
        (∏ l, τ.ka0 l) * (subst p n' O S.w n' r g (R0 p n' O Fr g)) ^ c') *
      (∏ j ∈ Finset.range Fr.J, (subst p n' O S.w n' r g (Del p n' O Fr g j)) ^ la) *
      subst p n' O S.w n' r g (DtopProd p n' O Fr hrk g mu) * MvPolynomial.map (algebraMap O (KK O)) τ.h) := by
    refine AddSubmonoid.closure_induction (motive := fun z _ =>
      bc_Phi S.w Fr Q g hrk c' o mu la τ.level (C (algebraMap O (KK O) (S.w ^ τ.i)) * z *
      (∏ j ∈ Finset.range Fr.J, (subst p n' O S.w n' r g (Del p n' O Fr g j)) ^ la) *
      subst p n' O S.w n' r g (DtopProd p n' O Fr hrk g mu) * MvPolynomial.map (algebraMap O (KK O)) τ.h))
      ?_ ?_ ?_ hdiff
    · intro γ hγ
      exact bc_absorb S.w Fr Q g hrk c' o mu la τ.level hDl hDD hD1 τ.i (∑ l, τ.o l) rfl
        ⟨τ.h, hτ.2, hτT.2, rfl⟩ hmuN hlaN _ (fun _ => rfl) hγ
    · simp only [mul_zero, zero_mul]
      exact bc_Phi_rho S.w Fr Q g hrk c' o mu la τ.level (inWj_zero _)
    · intro z1 z2 _ _ h1 h2
      have := bc_Phi_add S.w Fr Q g hrk c' o mu la τ.level h1 h2
      convert this using 1
      ring
  obtain ⟨l, ρ, hρ, heq, hl⟩ := hPhi
  refine ⟨l.length, fun t => l[t.1].1, fun t => l[t.1].2.1, fun t => l[t.1].2.2, ρ, hρ, ?_,
    fun t => hl _ (List.getElem_mem t.2)⟩
  rw [heq, Fin.sum_univ_fun_getElem l (fun y => y.1.sym p n' S.w Fr hrk g c' y.2.1 y.2.2)]

/- English proof (translation)
Rewrite using `[Finsupp.sum_filter_index, Finsupp.support_filter, Finset.sum_filter]`. Both sides reduce to the same expression.
-/
theorem bc_filter_sum {n' k : ℕ} (r : ℕ) (m : TV n' k →₀ ℕ) :
    (m.filter (IsNormal r)).sum (fun _ a => a) = normDeg r m := by
  rw [Finsupp.sum_filter_index, Finsupp.support_filter, Finset.sum_filter]
  rfl

/- English proof (translation)
Introduce `p n' r k _ _ O _ _ _ _ S hO hH Fr L₁ N₁ hV Q hQ g hg ka ka0 o hk h1 h2`. Take `⟨hA, hoQ, hnd, h0, htail, _⟩` from `hk`. Take `⟨T, hTdef⟩ : ∃ T, T = subst p n' O S.w n' r g ka - ka0` from `⟨_, rfl⟩`. Rewrite using `[← hTdef]`. Establish `hc1 : ∀ m, ∃ c : O, coeff m T = algebraMap O (KK O) (S.w ^ (o + 1) * c)`.

Rewrite using `[hTdef]`. Conclude with `htail`. Establish `hc2 : ∀ m, ∃ c : O, coeff m T = algebraMap O (KK O) (S.w ^ (normDeg r m) * c)`. Introduce `m`. Take `⟨c1, hc1⟩` from `bx_coeff_normDeg S.w r hg hA m`.

Distinguish the cases in `hm : m ∈ ka0.support`. Take `⟨c2, hc2⟩` from `h0 m`. Use `⟨c1 - c2, ?_⟩` and prove the remaining obligations. Rewrite using `[hTdef, coeff_sub, hc1, hc2, hnd m hm, ← map_sub]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨c1, by rw [hTdef, coeff_sub, hc1, notMem_support_iff.1 hm, sub_zero]⟩`. Establish `hTop : ∀ v ∈ T.vars, v.1 ∈ Fr.TT`. Introduce `v hv`. Rewrite `hv` using `[hTdef]`.

Break down `Finset.mem_union.1 (vars_sub_subset _ hv) with h | h` into its components or cases. Conclude with `bx_onTops_subst S.w Fr g h1 v h`. Conclude with `h2 v h`. Rewrite using `[T.as_sum]`. Use `sum_mem fun m hm => ?_` and prove the remaining obligations.

Choose the witnesses or unpack the hypotheses as in `⟨x, c, hx1, hx2, hxc⟩ : ∃ (x : ℕ) (c : O), o + 1 ≤ x ∧ normDeg r m ≤ x ∧ coeff m T = algebraMap O (KK O) (S.w ^ x * c) := by`. Distinguish the cases in `h : o + 1 ≤ normDeg r m`. Take `⟨c, hc⟩` from `hc2 m`. Conclude with `⟨_, c, h, le_rfl, hc⟩`. Take `⟨c, hc⟩` from `hc1 m; exact ⟨_, c, le_rfl, by omega, hc⟩`.

Establish `hmv : ∀ v ∈ m.support, v.1 ∈ Fr.TT` using `fun v hv => hTop v ((mem_vars v).2 ⟨m, hm, hv⟩)`. Establish `hmon : ∀ v ∈ (monomial (m.filter fun v => ¬ IsNormal r v) c : MvPolynomial (TV n' k) O).vars, v ∈ (m.filter fun v => ¬ IsNormal r v).support`. Introduce `v hv`. Take `⟨d, hd, hvd⟩` from `(mem_vars v).1 hv`. Establish `hdm` using `Finset.mem_singleton.1 (support_monomial_subset hd)`.

Substitute `hdm` using the available equality. Conclude with `hvd`. Use `AddSubmonoid.subset_closure ⟨x, 0, x - o, 1, m.filter (IsNormal r), fun _ => 0, MvPolynomial.map (algebraMap O (KK O)) (monomial (m.filter fun v => ¬ IsNormal r v) c), isKeyProduct_one S.w Fr Q g, ⟨_, ?_, ?_, rfl⟩, ?_, by simp only; omega, by omega, ?_, ?_, fun j _ => by simp, ?_ …` and prove the remaining obligations. Introduce `v hv`. Use `hmon v hv` as an intermediate fact.

Rewrite `this` using `[Finsupp.support_filter, Finset.mem_filter]`. Conclude with `this.2`. Introduce `v hv`. Use `hmon v hv` as an intermediate fact. Rewrite `this` using `[Finsupp.support_filter, Finset.mem_filter]`.

Conclude with `hmv v this.1`. Introduce `v hv`. Rewrite `hv` using `[Finsupp.support_filter, Finset.mem_filter]`. Conclude with `⟨hv.2, hmv v hv.1⟩`. Rewrite using `[bc_filter_sum]`.

Conclude with `hx2`. Rewrite using `[bc_filter_sum]`. Conclude with `Formalism.CountingSumsFrames.Top.cleanArith.1 (normDeg r m) (x - normDeg r m) o (x - o) Q (by omega) hoQ (by omega)`. Rewrite using `[hxc, map_monomial]`. Simplify using `only [pow_zero, Finset.prod_const_one, mul_one]`.

Rewrite using `[C_mul_monomial, monomial_mul, Finsupp.filter_pos_add_filter_neg, mul_one, map_mul]`.
-/
theorem bc_restTail (D : Formalism.BasicNotions.D7) : bc_RestTail D := by
  intro p n' r k _ _ O _ _ _ _ S hO hH Fr L₁ N₁ hV Q hQ g hg ka ka0 o hk h1 h2
  obtain ⟨hA, hoQ, hnd, h0, htail, _⟩ := hk
  obtain ⟨T, hTdef⟩ : ∃ T, T = subst p n' O S.w n' r g ka - ka0 := ⟨_, rfl⟩
  rw [← hTdef]
  have hc1 : ∀ m, ∃ c : O, coeff m T = algebraMap O (KK O) (S.w ^ (o + 1) * c) := by
    rw [hTdef]; exact htail
  have hc2 : ∀ m, ∃ c : O, coeff m T = algebraMap O (KK O) (S.w ^ (normDeg r m) * c) := by
    intro m
    obtain ⟨c1, hc1⟩ := bx_coeff_normDeg S.w r hg hA m
    by_cases hm : m ∈ ka0.support
    · obtain ⟨c2, hc2⟩ := h0 m
      refine ⟨c1 - c2, ?_⟩
      rw [hTdef, coeff_sub, hc1, hc2, hnd m hm, ← map_sub]
      congr 1
      ring
    · exact ⟨c1, by rw [hTdef, coeff_sub, hc1, notMem_support_iff.1 hm, sub_zero]⟩
  have hTop : ∀ v ∈ T.vars, v.1 ∈ Fr.TT := by
    intro v hv
    rw [hTdef] at hv
    rcases Finset.mem_union.1 (vars_sub_subset _ hv) with h | h
    · exact bx_onTops_subst S.w Fr g h1 v h
    · exact h2 v h
  rw [T.as_sum]
  refine sum_mem fun m hm => ?_
  obtain ⟨x, c, hx1, hx2, hxc⟩ : ∃ (x : ℕ) (c : O), o + 1 ≤ x ∧ normDeg r m ≤ x ∧
      coeff m T = algebraMap O (KK O) (S.w ^ x * c) := by
    by_cases h : o + 1 ≤ normDeg r m
    · obtain ⟨c, hc⟩ := hc2 m; exact ⟨_, c, h, le_rfl, hc⟩
    · obtain ⟨c, hc⟩ := hc1 m; exact ⟨_, c, le_rfl, by omega, hc⟩
  have hmv : ∀ v ∈ m.support, v.1 ∈ Fr.TT := fun v hv => hTop v ((mem_vars v).2 ⟨m, hm, hv⟩)
  have hmon : ∀ v ∈ (monomial (m.filter fun v => ¬ IsNormal r v) c : MvPolynomial (TV n' k) O).vars,
      v ∈ (m.filter fun v => ¬ IsNormal r v).support := by
    intro v hv
    obtain ⟨d, hd, hvd⟩ := (mem_vars v).1 hv
    have hdm := Finset.mem_singleton.1 (support_monomial_subset hd)
    subst hdm
    exact hvd
  refine AddSubmonoid.subset_closure ⟨x, 0, x - o, 1, m.filter (IsNormal r), fun _ => 0,
    MvPolynomial.map (algebraMap O (KK O)) (monomial (m.filter fun v => ¬ IsNormal r v) c), isKeyProduct_one S.w Fr Q g,
    ⟨_, ?_, ?_, rfl⟩, ?_, by simp only; omega, by omega, ?_, ?_, fun j _ => by simp, ?_⟩
  · intro v hv
    have := hmon v hv
    rw [Finsupp.support_filter, Finset.mem_filter] at this
    exact this.2
  · intro v hv
    have := hmon v hv
    rw [Finsupp.support_filter, Finset.mem_filter] at this
    exact hmv v this.1
  · intro v hv
    rw [Finsupp.support_filter, Finset.mem_filter] at hv
    exact ⟨hv.2, hmv v hv.1⟩
  · rw [bc_filter_sum]; exact hx2
  · rw [bc_filter_sum]
    exact Formalism.CountingSumsFrames.Top.cleanArith.1 (normDeg r m) (x - normDeg r m) o (x - o) Q (by omega) hoQ (by omega)
  · rw [hxc, map_monomial]
    simp only [pow_zero, Finset.prod_const_one, mul_one]
    rw [C_mul_monomial, monomial_mul, Finsupp.filter_pos_add_filter_neg, mul_one, map_mul]

/- English proof (translation)
The claim follows from `bc_claim_of_tail D hL hK (bc_restTail D)`.
-/
theorem bc_claim (D : Formalism.BasicNotions.D7) (hL : Conclusion2 D) (hK : PointsLemma D) : DifferenceClaimInCoordinates D :=
  bc_claim_of_tail D hL hK (bc_restTail D)

/- English proof (translation)
The claim follows from `bc_claim D (localiser_expansion_lemma D) (keys_vanish_modulo_uniformiser D)`.
-/
theorem bc_claim' (D : Formalism.BasicNotions.D7) : DifferenceClaimInCoordinates D := bc_claim D (localiser_expansion_lemma D) (keys_vanish_modulo_uniformiser D)

/- English proof (translation)
The claim follows from `order_lemma_of_plane_coordinates D (localiser_vanishing_off_plane D) hT (bc_claim' D)`.
-/
theorem order_lemma_of_raw_on_tops (D : Formalism.BasicNotions.D7) (hT : RawTermOnTops D) : Conclusion4 D :=
  order_lemma_of_plane_coordinates D (localiser_vanishing_off_plane D) hT (bc_claim' D)

end Formalism.MainNotions.G.WittFrameLocaliserOrders

end

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.G.WittFrameLocaliserOrders

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning

def letterDeterminant (R : Type) [CommRing R] {ι : Type} {r : ℕ} (A : Fin r → ι) : MvPolynomial (ι × Fin r) R :=
  (Matrix.of fun i j : Fin r => (X (A i, j) : MvPolynomial (ι × Fin r) R)).det

def otherVectorDegree {ι : Type} [Fintype ι] {r : ℕ} (LL : Letters ι) (S : Set ι) (A : Fin r → ι) (d : ι → ℕ) : ℕ :=
  ∑ l, if l ∈ S ∧ LL.vec l = true ∧ l ∉ Set.range A then d l else 0

def FieldMultidegreeDivisibility : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (r : ℕ) [NeZero r] (S : Set ι)
    (A : Fin r → ι), Function.Injective A → (∀ l, A l ∈ S ∧ LL.vec (A l) = true) →
    (∀ (d : ι → ℕ) (G : MvPolynomial (ι × Fin r) R), G ∈ Pol R r d →
      ∀ th : ℤ, (th : WithTop ℤ) ≤ valS LL S G → (otherVectorDegree LL S A d : ℤ) < th →
        (letterDeterminant R A) ^ (th - otherVectorDegree LL S A d).toNat ∣ G) ∧
    (∀ (G H : MvPolynomial (ι × Fin r) R) (m : ℕ), G = (letterDeterminant R A) ^ m * H →
        ∀ S' : Set ι, valS LL S' G ≤ valS LL S' H + ((m : ℤ) : WithTop ℤ))

def multidegreeComponent {R : Type} [CommRing R] {ι : Type} {n : ℕ} (d : ι → ℕ) (G : MvPolynomial (ι × Fin n) R) :
    MvPolynomial (ι × Fin n) R :=
  ∑ m ∈ G.support.filter (fun m => (fun i => multideg m i) = d), monomial m (G.coeff m)

def IntegralToFieldBaseChange : Prop :=
  ∀ (R0 : Type) [CommRing R0] [IsDomain R0] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) [NeZero n] (S : Set ι)
    (G : MvPolynomial (ι × Fin n) R0),
    valS LL S (MvPolynomial.map (algebraMap R0 (FractionRing R0)) G) = valS LL S G

def ComponentsPreserveValuation : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) [NeZero n] (S : Set ι)
    (G : MvPolynomial (ι × Fin n) R) (d : ι → ℕ), valS LL S G ≤ valS LL S (multidegreeComponent d G)

def GaussQuotientIntegral : Prop :=
  ∀ (R0 : Type) [CommRing R0] [IsDomain R0] (ι : Type) [Fintype ι] (r : ℕ) (A : Fin r → ι), Function.Injective A →
    ∀ (n : ℕ) (G : MvPolynomial (ι × Fin r) R0),
      (letterDeterminant (FractionRing R0) A) ^ n ∣ MvPolynomial.map (algebraMap R0 (FractionRing R0)) G →
      (letterDeterminant R0 A) ^ n ∣ G

/- English proof (translation)
Establish `h1 : otherVectorDegree LL S A (fun i => multideg m i) = ∑ v ∈ m.support, if v.1 ∈ S ∧ LL.vec v.1 = true ∧ v.1 ∉ Set.range A then m v else 0`. Unfold `otherVectorDegree multideg`. Establish `h2 : ∀ l : Fin M, (if l ∈ S ∧ LL.vec l = true ∧ l ∉ Set.range A then ∑ c : Fin r, m (l, c) else 0) = ∑ c : Fin r, if l ∈ S ∧ LL.vec l = true ∧ l ∉ Set.range A then m (l, c) else 0`. Apply the tactic sequence `intro l; split_ifs <;> simp`. Repeatedly rewrite using `[h2]`.

Rewrite using `[← Fintype.sum_prod_type (f := fun v : Fin M × Fin r => if v.1 ∈ S ∧ LL.vec v.1 = true ∧ v.1 ∉ Set.range A then m v else 0)]`. Use `symm`. Apply `Finset.sum_subset (Finset.subset_univ _)` to reduce the goal to its premises. Introduce `v _ hv`. Establish `h3 : m v = 0` using `by simpa using hv`.

Simplify using `[h3]`. Rewrite using `[h1]`. Conclude with `Finset.le_sup (f := fun m : Fin M × Fin r →₀ ℕ => ∑ v ∈ m.support, if v.1 ∈ S ∧ LL.vec v.1 = true ∧ v.1 ∉ Set.range A then m v else 0) hm`.
-/
theorem otherVectorDegree_le_bound {O : Type} [CommRing O] {σN : Type} {M r : ℕ} (LL : Letters (Fin M)) (S : Set (Fin M))
    (A : Fin r → Fin M) (G : MvPolynomial (Fin M × Fin r) (MvPolynomial σN O)) (m : Fin M × Fin r →₀ ℕ)
    (hm : m ∈ G.support) :
    otherVectorDegree LL S A (fun i => multideg m i) ≤ Bprime LL S A G := by
  have h1 : otherVectorDegree LL S A (fun i => multideg m i) =
      ∑ v ∈ m.support, if v.1 ∈ S ∧ LL.vec v.1 = true ∧ v.1 ∉ Set.range A then m v else 0 := by
    unfold otherVectorDegree multideg
    have h2 : ∀ l : Fin M, (if l ∈ S ∧ LL.vec l = true ∧ l ∉ Set.range A then ∑ c : Fin r, m (l, c) else 0) =
        ∑ c : Fin r, if l ∈ S ∧ LL.vec l = true ∧ l ∉ Set.range A then m (l, c) else 0 := by
      intro l; split_ifs <;> simp
    simp_rw [h2]
    rw [← Fintype.sum_prod_type
      (f := fun v : Fin M × Fin r => if v.1 ∈ S ∧ LL.vec v.1 = true ∧ v.1 ∉ Set.range A then m v else 0)]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    have h3 : m v = 0 := by simpa using hv
    simp [h3]
  rw [h1]
  exact Finset.le_sup
    (f := fun m : Fin M × Fin r →₀ ℕ =>
      ∑ v ∈ m.support, if v.1 ∈ S ∧ LL.vec v.1 = true ∧ v.1 ∉ Set.range A then m v else 0) hm

/- English proof (translation)
Use `conv_lhs => rw [← G.support_sum_monomial_coeff]`. Unfold `multidegreeComponent`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (g := fun m => fun i => multideg m i) (t := G.support.image (fun m => fun i => multideg m i)) (fun m hm => Finset.mem_image_of_mem _ hm)]`.
-/
theorem eq_sum_multidegree_components {R : Type} [CommRing R] {ι : Type} {n : ℕ} (G : MvPolynomial (ι × Fin n) R) :
    G = ∑ d ∈ G.support.image (fun m => fun i => multideg m i), multidegreeComponent d G := by
  conv_lhs => rw [← G.support_sum_monomial_coeff]
  unfold multidegreeComponent
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun m => fun i => multideg m i)
    (t := G.support.image (fun m => fun i => multideg m i)) (fun m hm => Finset.mem_image_of_mem _ hm)]

/- English proof (translation)
Unfold `multidegreeComponent`. Apply `Submodule.sum_mem` to reduce the goal to its premises. Introduce `m hm`. Establish `hm2` using `(Finset.mem_filter.1 hm).2`. Unfold `Pol`.

Rewrite using `[MvPolynomial.mem_restrictSupport_iff]`. Introduce `m' hm'`. Establish `: m' = m`. Use `MvPolynomial.support_monomial_subset hm'` as an intermediate fact. Simplify using `using this`.

Substitute `this` using the available equality. Introduce `i`. Conclude with `congrFun hm2 i`.
-/
theorem homogeneous_component_mem {R : Type} [CommRing R] {ι : Type} {n : ℕ} (d : ι → ℕ) (G : MvPolynomial (ι × Fin n) R) :
    multidegreeComponent d G ∈ Pol R n d := by
  unfold multidegreeComponent
  apply Submodule.sum_mem
  intro m hm
  have hm2 := (Finset.mem_filter.1 hm).2
  unfold Pol
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro m' hm'
  have : m' = m := by
    have := MvPolynomial.support_monomial_subset hm'
    simpa using this
  subst this
  intro i
  exact congrFun hm2 i

/- English proof (translation)
Unfold `letterDeterminant`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem map_letter_determinant {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {ι : Type} {r : ℕ} (A : Fin r → ι) :
    MvPolynomial.map φ (letterDeterminant R A) = letterDeterminant S A := by
  unfold letterDeterminant
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp

/- English proof (translation)
Rewrite using `[eq_sum_multidegree_components G]`. Apply `Finset.dvd_sum` to reduce the goal to its premises. Introduce `d hd`. Take `⟨m, hm, rfl⟩` from `Finset.mem_image.1 hd`. Conclude with `h m hm`.
-/
theorem dvd_of_dvd_components {R : Type} [CommRing R] {ι : Type} {n : ℕ} (G P : MvPolynomial (ι × Fin n) R)
    (h : ∀ m ∈ G.support, P ∣ multidegreeComponent (fun i => multideg m i) G) : P ∣ G := by
  rw [eq_sum_multidegree_components G]
  apply Finset.dvd_sum
  intro d hd
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hd
  exact h m hm

/- English proof (translation)
Introduce `O _ _ _ σN M r _ LL s A G th hinj hA _hlast hval hBp`. Establish `hφ : Function.Injective (algebraMap (MvPolynomial σN O) (FractionRing (MvPolynomial σN O)))` using `IsFractionRing.injective _ _`. Take `⟨hE1, hE2⟩` from `hE (FractionRing (MvPolynomial σN O)) (Fin M) LL r {i | i < s} A hinj (fun l => ⟨(hA l).2, (hA l).1⟩)`. Establish `hsupp` using `MvPolynomial.support_map_of_injective G hφ`. Establish `hdvd : letterDeterminant (FractionRing (MvPolynomial σN O)) A ^ (th - Bprime LL {i | i < s} A G).toNat ∣ MvPolynomial.map (algebraMap (MvPolynomial σN O) (FractionRing (MvPolynomial σN O))) G`.

Apply `dvd_of_dvd_components` to reduce the goal to its premises. Introduce `m hm`. Establish `hle : (otherVectorDegree LL {i | i < s} A (fun i => multideg m i) : ℤ) ≤ Bprime LL {i | i < s} A G`. Conclude with `otherVectorDegree_le_bound LL {i | i < s} A G m (hsupp ▸ hm)` after adjusting the coercions. Establish `hv : (th : WithTop ℤ) ≤ valS LL {i | i < s} (multidegreeComponent (fun i => multideg m i) (MvPolynomial.map (algebraMap (MvPolynomial σN O) (FractionRing (MvPolynomial σN O))) G))`.

Use `le_trans ?_ (hC _ _ LL r _ _ _)` and prove the remaining obligations. Rewrite using `[hB]`. Conclude with `hval`. Establish `h1` using `hE1 _ _ (homogeneous_component_mem _ _) th hv (lt_of_le_of_lt hle hBp)`. Conclude with `dvd_trans (pow_dvd_pow _ (Int.toNat_le_toNat (by omega))) h1`.

Take `⟨Qt, hQt⟩` from `hG (MvPolynomial σN O) (Fin M) r A hinj _ G hdvd`. Use `⟨Qt, hQt, ?_⟩` and prove the remaining obligations. Introduce `J' t ht`. Establish `hmap : MvPolynomial.map (algebraMap (MvPolynomial σN O) (FractionRing (MvPolynomial σN O))) G = letterDeterminant (FractionRing (MvPolynomial σN O)) A ^ (th - Bprime LL {i | i < s} A G).toNat * MvPolynomial.map (algebraMap (MvPolynomial σN O) (FractionRing (MvPolynomial σN O))) Q …` using `by conv_lhs => rw [hQt]`. Rewrite using `[map_mul, map_pow, map_letter_determinant]`.

Establish `h2` using `hE2 _ _ _ hmap J'`. Rewrite `h2` using `[hB, hB]`. Establish `h3` using `le_trans ht h2`. Establish `hn : (((th - Bprime LL {i | i < s} A G).toNat : ℕ) : ℤ) = th - Bprime LL {i | i < s} A G` using `Int.toNat_of_nonneg (by omega)`. Rewrite `h3` using `[hn]`.

Consider the cases of `h : valS LL J' Qt with`. Consider the case `top => exact le_top`. Consider the case `coe z`. Rewrite `h3` using `[h]`. Normalize the coercions in `at h3 ⊢`.

Use linear arithmetic over natural numbers and integers.
-/
theorem divisibility_of_field_lemma_and_facts (D : Formalism.BasicNotions.D7) (hE : FieldMultidegreeDivisibility) (hB : IntegralToFieldBaseChange) (hC : ComponentsPreserveValuation)
    (hG : GaussQuotientIntegral) : Conclusion5 D := by
  intro O _ _ _ σN M r _ LL s A G th hinj hA _hlast hval hBp
  have hφ : Function.Injective (algebraMap (MvPolynomial σN O) (FractionRing (MvPolynomial σN O))) :=
    IsFractionRing.injective _ _
  obtain ⟨hE1, hE2⟩ := hE (FractionRing (MvPolynomial σN O)) (Fin M) LL r {i | i < s} A hinj
    (fun l => ⟨(hA l).2, (hA l).1⟩)
  have hsupp := MvPolynomial.support_map_of_injective G hφ
  have hdvd : letterDeterminant (FractionRing (MvPolynomial σN O)) A ^ (th - Bprime LL {i | i < s} A G).toNat ∣
      MvPolynomial.map (algebraMap (MvPolynomial σN O) (FractionRing (MvPolynomial σN O))) G := by
    apply dvd_of_dvd_components
    intro m hm
    have hle : (otherVectorDegree LL {i | i < s} A (fun i => multideg m i) : ℤ) ≤ Bprime LL {i | i < s} A G := by
      exact_mod_cast otherVectorDegree_le_bound LL {i | i < s} A G m (hsupp ▸ hm)
    have hv : (th : WithTop ℤ) ≤ valS LL {i | i < s}
        (multidegreeComponent (fun i => multideg m i)
          (MvPolynomial.map (algebraMap (MvPolynomial σN O) (FractionRing (MvPolynomial σN O))) G)) := by
      refine le_trans ?_ (hC _ _ LL r _ _ _)
      rw [hB]
      exact hval
    have h1 := hE1 _ _ (homogeneous_component_mem _ _) th hv (lt_of_le_of_lt hle hBp)
    exact dvd_trans (pow_dvd_pow _ (Int.toNat_le_toNat (by omega))) h1
  obtain ⟨Qt, hQt⟩ := hG (MvPolynomial σN O) (Fin M) r A hinj _ G hdvd
  refine ⟨Qt, hQt, ?_⟩
  intro J' t ht
  have hmap : MvPolynomial.map (algebraMap (MvPolynomial σN O) (FractionRing (MvPolynomial σN O))) G =
      letterDeterminant (FractionRing (MvPolynomial σN O)) A ^ (th - Bprime LL {i | i < s} A G).toNat *
        MvPolynomial.map (algebraMap (MvPolynomial σN O) (FractionRing (MvPolynomial σN O))) Qt := by
    conv_lhs => rw [hQt]
    rw [map_mul, map_pow, map_letter_determinant]
  have h2 := hE2 _ _ _ hmap J'
  rw [hB, hB] at h2
  have h3 := le_trans ht h2
  have hn : (((th - Bprime LL {i | i < s} A G).toNat : ℕ) : ℤ) = th - Bprime LL {i | i < s} A G :=
    Int.toNat_of_nonneg (by omega)
  rw [hn] at h3
  cases h : valS LL J' Qt with
  | top => exact le_top
  | coe z =>
    rw [h] at h3
    norm_cast at h3 ⊢
    omega

def letterWeight {ι : Type} {n : ℕ} : ι × Fin n → (ι → ℕ) := fun v => Pi.single v.1 1

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]`. Establish `h : ∀ v : ι × Fin n, (m v • (letterWeight v : ι → ℕ)) i = if v.1 = i then m v else 0`. Introduce `v`. Distinguish the cases in `hv : v.1 = i`.

Substitute `hv` using the available equality. Simplify using `[letterWeight]`. Simplify using `[letterWeight, hv, Ne.symm hv]`. Repeatedly rewrite using `[h]`. Rewrite using `[Finset.sum_subset (Finset.subset_univ _) (by`.

Introduce `v _ hv`. Establish `h0 : m v = 0` using `by simpa using hv`. Simplify using `[h0])]`. Rewrite using `[Fintype.sum_prod_type]`. Unfold `multideg`.

Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `l _ hl`. Simplify using `[hl]`. Simplify using the standard rewrite rules.
-/
theorem weight_eq_multidegree_fun {ι : Type} [Fintype ι] {n : ℕ} (m : ι × Fin n →₀ ℕ) :
    Finsupp.weight (letterWeight (ι := ι) (n := n)) m = fun i => multideg m i := by
  funext i
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  have h : ∀ v : ι × Fin n, (m v • (letterWeight v : ι → ℕ)) i = if v.1 = i then m v else 0 := by
    intro v
    by_cases hv : v.1 = i
    · subst hv; simp [letterWeight]
    · simp [letterWeight, hv, Ne.symm hv]
  simp_rw [h]
  rw [Finset.sum_subset (Finset.subset_univ _) (by
    intro v _ hv
    have h0 : m v = 0 := by simpa using hv
    simp [h0])]
  rw [Fintype.sum_prod_type]
  unfold multideg
  rw [Finset.sum_eq_single i]
  · simp
  · intro l _ hl; simp [hl]
  · simp

/- English proof (translation)
Unfold `twistSub`. Rewrite using `[eval₂Hom_X']`. Use `split_ifs`. Apply `IsWeightedHomogeneous.sum` to reduce the goal to its premises. Introduce `b _`.

Establish `h` using `(isWeightedHomogeneous_C (letterWeight (ι := ι) (n := n)) (twistMat R n j 1 b v.2)).mul (isWeightedHomogeneous_X (GLLaurent R n) (letterWeight (ι := ι) (n := n)) (v.1, b))`. Rewrite `h` using `[zero_add]`. Conclude with `h`. Apply `IsWeightedHomogeneous.sum` to reduce the goal to its premises. Introduce `b _`.

Establish `h` using `(isWeightedHomogeneous_C (letterWeight (ι := ι) (n := n)) (twistMat R n j (-1) v.2 b)).mul (isWeightedHomogeneous_X (GLLaurent R n) (letterWeight (ι := ι) (n := n)) (v.1, b))`. Rewrite `h` using `[zero_add]`. Conclude with `h`. Conclude with `isWeightedHomogeneous_X _ _ _`.
-/
theorem twist_variable_weighted_homogeneous {R : Type} [CommRing R] {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    (v : ι × Fin n) : IsWeightedHomogeneous letterWeight (twistSub (R := R) LL S j (X v)) (letterWeight v) := by
  unfold twistSub
  rw [eval₂Hom_X']
  split_ifs
  · apply IsWeightedHomogeneous.sum
    intro b _
    have h := (isWeightedHomogeneous_C (letterWeight (ι := ι) (n := n)) (twistMat R n j 1 b v.2)).mul
      (isWeightedHomogeneous_X (GLLaurent R n) (letterWeight (ι := ι) (n := n)) (v.1, b))
    rw [zero_add] at h
    exact h
  · apply IsWeightedHomogeneous.sum
    intro b _
    have h := (isWeightedHomogeneous_C (letterWeight (ι := ι) (n := n)) (twistMat R n j (-1) v.2 b)).mul
      (isWeightedHomogeneous_X (GLLaurent R n) (letterWeight (ι := ι) (n := n)) (v.1, b))
    rw [zero_add] at h
    exact h
  · exact isWeightedHomogeneous_X _ _ _

/- English proof (translation)
Rewrite using `[MvPolynomial.monomial_eq, map_mul, Finsupp.prod, map_prod]`. Establish `h1 : IsWeightedHomogeneous (letterWeight (ι` using `ι) (n := n)) (twistSub (R := R) LL S j (C c)) 0 := by`. Unfold `twistSub`. Rewrite using `[eval₂Hom_C]`. Conclude with `isWeightedHomogeneous_C _ _`.

Establish `h2` using `IsWeightedHomogeneous.prod m.support (fun v => twistSub (R := R) LL S j (X v ^ m v)) (fun v => m v • (letterWeight v : ι → ℕ)) (w := letterWeight) (fun v _ => by`. Rewrite using `[map_pow]`. Conclude with `(twist_variable_weighted_homogeneous LL S j v).pow (m v))`. Establish `h3` using `h1.mul h2`. Rewrite `h3` using `[zero_add]`.

Rewrite using `[Finsupp.weight_apply, Finsupp.sum]`. Conclude with `h3`.
-/
theorem twist_substitution_weighted_homog {R : Type} [CommRing R] {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    (m : ι × Fin n →₀ ℕ) (c : R) :
    IsWeightedHomogeneous letterWeight (twistSub (R := R) LL S j (monomial m c)) (Finsupp.weight letterWeight m) := by
  rw [MvPolynomial.monomial_eq, map_mul, Finsupp.prod, map_prod]
  have h1 : IsWeightedHomogeneous (letterWeight (ι := ι) (n := n)) (twistSub (R := R) LL S j (C c)) 0 := by
    unfold twistSub
    rw [eval₂Hom_C]
    exact isWeightedHomogeneous_C _ _
  have h2 := IsWeightedHomogeneous.prod m.support (fun v => twistSub (R := R) LL S j (X v ^ m v))
    (fun v => m v • (letterWeight v : ι → ℕ)) (w := letterWeight) (fun v _ => by
      rw [map_pow]; exact (twist_variable_weighted_homogeneous LL S j v).pow (m v))
  have h3 := h1.mul h2
  rw [zero_add] at h3
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact h3

/- English proof (translation)
The claim follows from `(Finset.mem_filter.1 h).2`.
-/
theorem mem_multidegree_filter {R : Type} [CommRing R] {ι : Type} {n : ℕ} (G : MvPolynomial (ι × Fin n) R) (d : ι → ℕ)
    (m : ι × Fin n →₀ ℕ) (h : m ∈ G.support.filter (fun m => (fun i => multideg m i) = d)) :
    (fun i => multideg m i) = d := (Finset.mem_filter.1 h).2

/- English proof (translation)
Introduce `R _ ι _ LL n _ S G d`. Unfold `valS`. Apply `Finset.inf_mono` to reduce the goal to its premises. Introduce `z hz`. Unfold `sDegs at hz ⊢`.

Rewrite `hz`, the goal using `[Finset.mem_biUnion]`. Take `⟨m', hm', hz'⟩` from `hz`. Establish `hWH : IsWeightedHomogeneous letterWeight (twistSub LL S (lastIdx n) (multidegreeComponent d G)) d`. Unfold `multidegreeComponent`. Rewrite using `[map_sum]`.

Apply `IsWeightedHomogeneous.sum` to reduce the goal to its premises. Introduce `m hm`. Establish `h` using `twist_substitution_weighted_homog LL S (lastIdx n) m (G.coeff m)`. Rewrite `h` using `[weight_eq_multidegree_fun, mem_multidegree_filter G d m hm]`. Then use the resulting hypothesis. Establish `hwt : Finsupp.weight letterWeight m' = d` using `hWH (mem_support_iff.1 hm')`.

Establish `hsplit : G = multidegreeComponent d G + ∑ m ∈ G.support.filter (fun m => ¬ (fun i => multideg m i) = d), monomial m (G.coeff m)`. Unfold `multidegreeComponent`. Rewrite using `[Finset.sum_filter_add_sum_filter_not]`. Conclude with `G.support_sum_monomial_coeff.symm`. Establish `key : (twistSub LL S (lastIdx n) (multidegreeComponent d G)).coeff m' = (twistSub LL S (lastIdx n) G).coeff m'` using `by conv_rhs => rw [hsplit]`.

Rewrite using `[map_add, coeff_add, map_sum, coeff_sum, Finset.sum_eq_zero, add_zero]`. Introduce `m hm`. Apply `(twist_substitution_weighted_homog LL S (lastIdx n) m (G.coeff m)).coeff_eq_zero` to reduce the goal to its premises. Introduce `h`. Apply `(Finset.mem_filter.1 hm).2` to reduce the goal to its premises.

Rewrite using `[← weight_eq_multidegree_fun, ← h, hwt]`. Use `⟨m', ?_, key ▸ hz'⟩` and prove the remaining obligations. Rewrite `hm'`, the goal using `[mem_support_iff]`. Rewrite using `[← key]` and apply the resulting hypothesis.
-/
theorem components_preserve_valuation : ComponentsPreserveValuation := by
  intro R _ ι _ LL n _ S G d
  unfold valS
  apply Finset.inf_mono
  intro z hz
  unfold sDegs at hz ⊢
  rw [Finset.mem_biUnion] at hz ⊢
  obtain ⟨m', hm', hz'⟩ := hz
  have hWH : IsWeightedHomogeneous letterWeight (twistSub LL S (lastIdx n) (multidegreeComponent d G)) d := by
    unfold multidegreeComponent
    rw [map_sum]
    apply IsWeightedHomogeneous.sum
    intro m hm
    have h := twist_substitution_weighted_homog LL S (lastIdx n) m (G.coeff m)
    rwa [weight_eq_multidegree_fun, mem_multidegree_filter G d m hm] at h
  have hwt : Finsupp.weight letterWeight m' = d := hWH (mem_support_iff.1 hm')
  have hsplit : G = multidegreeComponent d G +
      ∑ m ∈ G.support.filter (fun m => ¬ (fun i => multideg m i) = d), monomial m (G.coeff m) := by
    unfold multidegreeComponent
    rw [Finset.sum_filter_add_sum_filter_not]
    exact G.support_sum_monomial_coeff.symm
  have key : (twistSub LL S (lastIdx n) (multidegreeComponent d G)).coeff m' = (twistSub LL S (lastIdx n) G).coeff m' := by
    conv_rhs => rw [hsplit]
    rw [map_add, coeff_add, map_sum, coeff_sum, Finset.sum_eq_zero, add_zero]
    intro m hm
    apply (twist_substitution_weighted_homog LL S (lastIdx n) m (G.coeff m)).coeff_eq_zero
    intro h
    apply (Finset.mem_filter.1 hm).2
    rw [← weight_eq_multidegree_fun, ← h, hwt]
  refine ⟨m', ?_, key ▸ hz'⟩
  rw [mem_support_iff] at hm' ⊢
  rwa [← key]

/- English proof (translation)
Establish `hφ : Function.Injective (algebraMap R0 (FractionRing R0))` using `IsFractionRing.injective _ _`. Take `⟨g, rem, hG, _, hrem⟩` from `m.div_single hb G`. Distinguish the cases in `hr0 : rem = 0`. Rewrite using `[hG, hr0, add_zero]`. Conclude with `Dvd.intro_left g rfl`.

It suffices to derive a contradiction. Establish `hdr : MvPolynomial.map (algebraMap R0 (FractionRing R0)) b ∣ MvPolynomial.map (algebraMap R0 (FractionRing R0)) rem`. Establish `e : MvPolynomial.map (algebraMap R0 (FractionRing R0)) rem = MvPolynomial.map (algebraMap R0 (FractionRing R0)) G - MvPolynomial.map (algebraMap R0 (FractionRing R0)) g * MvPolynomial.map (algebraMap R0 (FractionRing R0)) b`. Rewrite using `[hG]`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Conclude with `dvd_sub h (Dvd.intro_left _ rfl)`. Take `⟨q, hq⟩` from `hdr`. Establish `hrem0 : MvPolynomial.map (algebraMap R0 (FractionRing R0)) rem ≠ 0`. Introduce `h0`.

Apply `hr0` to reduce the goal to its premises. Conclude with `(MvPolynomial.map_injective _ hφ) (by rw [h0, map_zero])`. Establish `hb0 : MvPolynomial.map (algebraMap R0 (FractionRing R0)) b ≠ 0`. Introduce `h0`. Rewrite `hq` using `[h0, zero_mul]`.

Conclude with `hrem0 hq`. Establish `hq0 : q ≠ 0`. Introduce `h0`. Rewrite `hq` using `[h0, mul_zero]`. Conclude with `hrem0 hq`.

Establish `hdeg : m.degree (MvPolynomial.map (algebraMap R0 (FractionRing R0)) rem) = m.degree (MvPolynomial.map (algebraMap R0 (FractionRing R0)) b) + m.degree q`. Rewrite using `[hq]`. Conclude with `m.degree_mul hb0 hq0`. Establish `hdb : m.degree (MvPolynomial.map (algebraMap R0 (FractionRing R0)) b) = m.degree b`. Unfold `MonomialOrder.degree`.

Rewrite using `[MvPolynomial.support_map_of_injective _ hφ]`. Establish `hmem : m.degree (MvPolynomial.map (algebraMap R0 (FractionRing R0)) rem) ∈ rem.support`. Rewrite using `[← MvPolynomial.support_map_of_injective rem hφ]`. Conclude with `(m.degree_mem_support_iff _).2 hrem0`. Apply `hrem _ hmem` to reduce the goal to its premises.

Rewrite using `[hdeg, hdb]`. Conclude with `le_self_add`.
-/
theorem dvd_of_dvd_fraction_field_unit_lead {R0 : Type} [CommRing R0] [IsDomain R0] {σ : Type} (m : MonomialOrder σ)
    (b G : MvPolynomial σ R0) (hb : IsUnit (m.leadingCoeff b))
    (h : MvPolynomial.map (algebraMap R0 (FractionRing R0)) b ∣
      MvPolynomial.map (algebraMap R0 (FractionRing R0)) G) : b ∣ G := by
  have hφ : Function.Injective (algebraMap R0 (FractionRing R0)) := IsFractionRing.injective _ _
  obtain ⟨g, rem, hG, _, hrem⟩ := m.div_single hb G
  by_cases hr0 : rem = 0
  · rw [hG, hr0, add_zero]
    exact Dvd.intro_left g rfl
  exfalso
  have hdr : MvPolynomial.map (algebraMap R0 (FractionRing R0)) b ∣
      MvPolynomial.map (algebraMap R0 (FractionRing R0)) rem := by
    have e : MvPolynomial.map (algebraMap R0 (FractionRing R0)) rem =
        MvPolynomial.map (algebraMap R0 (FractionRing R0)) G -
          MvPolynomial.map (algebraMap R0 (FractionRing R0)) g *
            MvPolynomial.map (algebraMap R0 (FractionRing R0)) b := by
      rw [hG]; simp
    rw [e]
    exact dvd_sub h (Dvd.intro_left _ rfl)
  obtain ⟨q, hq⟩ := hdr
  have hrem0 : MvPolynomial.map (algebraMap R0 (FractionRing R0)) rem ≠ 0 := by
    intro h0
    apply hr0
    exact (MvPolynomial.map_injective _ hφ) (by rw [h0, map_zero])
  have hb0 : MvPolynomial.map (algebraMap R0 (FractionRing R0)) b ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hq; exact hrem0 hq
  have hq0 : q ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hq; exact hrem0 hq
  have hdeg : m.degree (MvPolynomial.map (algebraMap R0 (FractionRing R0)) rem) =
      m.degree (MvPolynomial.map (algebraMap R0 (FractionRing R0)) b) + m.degree q := by
    rw [hq]; exact m.degree_mul hb0 hq0
  have hdb : m.degree (MvPolynomial.map (algebraMap R0 (FractionRing R0)) b) = m.degree b := by
    unfold MonomialOrder.degree
    rw [MvPolynomial.support_map_of_injective _ hφ]
  have hmem : m.degree (MvPolynomial.map (algebraMap R0 (FractionRing R0)) rem) ∈ rem.support := by
    rw [← MvPolynomial.support_map_of_injective rem hφ]
    exact (m.degree_mem_support_iff _).2 hrem0
  apply hrem _ hmem
  rw [hdeg, hdb]
  exact le_self_add

def DeterminantCoefficientsUnits : Prop :=
  ∀ (R0 : Type) [CommRing R0] [IsDomain R0] (ι : Type) [Fintype ι] (r : ℕ) (A : Fin r → ι), Function.Injective A →
    letterDeterminant R0 A ≠ 0 ∧ ∀ μ ∈ (letterDeterminant R0 A).support, IsUnit ((letterDeterminant R0 A).coeff μ)

/- English proof (translation)
Introduce `R0 _ _ ι _ r A hA n G hdvd`. Set `_ : LinearOrder (ι × Fin r)` to `LinearOrder.lift' (Fintype.equivFin (ι × Fin r)) (Fintype.equivFin (ι × Fin r)).injective`. Set `m : MonomialOrder (ι × Fin r)` to `MonomialOrder.lex`. Take `⟨h0, hu⟩` from `h R0 ι r A hA`. Establish `hlc : IsUnit (m.leadingCoeff (letterDeterminant R0 A))` using `hu _ ((m.degree_mem_support_iff _).2 h0)`.

Apply `dvd_of_dvd_fraction_field_unit_lead m` to reduce the goal to its premises. Rewrite using `[m.leadingCoeff_pow]`. Conclude with `hlc.pow n`. Rewrite using `[map_pow, map_letter_determinant]`. Conclude with `hdvd`.
-/
theorem gauss_of_det_coefficients (h : DeterminantCoefficientsUnits) : GaussQuotientIntegral := by
  intro R0 _ _ ι _ r A hA n G hdvd
  let _ : LinearOrder (ι × Fin r) :=
    LinearOrder.lift' (Fintype.equivFin (ι × Fin r)) (Fintype.equivFin (ι × Fin r)).injective
  let m : MonomialOrder (ι × Fin r) := MonomialOrder.lex
  obtain ⟨h0, hu⟩ := h R0 ι r A hA
  have hlc : IsUnit (m.leadingCoeff (letterDeterminant R0 A)) := hu _ ((m.degree_mem_support_iff _).2 h0)
  apply dvd_of_dvd_fraction_field_unit_lead m
  · rw [m.leadingCoeff_pow]; exact hlc.pow n
  · rw [map_pow, map_letter_determinant]; exact hdvd

/- English proof (translation)
Introduce `R0 _ _ ι _ r A hA`. Set `mu : Equiv.Perm (Fin r) → (ι × Fin r →₀ ℕ)` to `fun s => ∑ i, Finsupp.single (A (s i), i) 1`. Establish `hmu_apply : ∀ (s : Equiv.Perm (Fin r)) (l : ι) (i : Fin r), mu s (l, i) = if A (s i) = l then 1 else 0`. Introduce `s l i`. Simplify using `only [mu, Finsupp.finsetSum_apply, Finsupp.single_apply, Prod.mk.injEq]`.

Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `i' _ hi'`. Simplify using `[hi']`. Simplify using the standard rewrite rules.

Establish `hinj : Function.Injective mu`. Introduce `s t hst`. Apply `Equiv.ext` to reduce the goal to its premises. Introduce `i`. Establish `h1` using `DFunLike.congr_fun hst (A (s i), i)`.

Rewrite `h1` using `[hmu_apply, hmu_apply, if_pos rfl]`. Assume the negation of the conclusion as `hne`. Establish `h2 : A (t i) ≠ A (s i)` using `fun h => hne (hA h).symm`. Rewrite `h1` using `[if_neg h2]`. Conclude with `one_ne_zero h1`.

Establish `hdet : letterDeterminant R0 A = ∑ s : Equiv.Perm (Fin r), monomial (mu s) (((Equiv.Perm.sign s : ℤˣ) : ℤ) : R0)`. Unfold `letterDeterminant`. Rewrite using `[Matrix.det_apply]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `s _`.

Establish `h1 : ∏ i, (Matrix.of fun i j : Fin r => (X (A i, j) : MvPolynomial (ι × Fin r) R0)) (s i) i = monomial (mu s) 1`. Simplify using `only [Matrix.of_apply, mu]`. Rewrite using `[MvPolynomial.monomial_sum_one]`. Both sides reduce to the same expression. Rewrite using `[h1]`.

Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h <;> simp [h]`. Establish `hcoeff : ∀ s0, (letterDeterminant R0 A).coeff (mu s0) = (((Equiv.Perm.sign s0 : ℤˣ) : ℤ) : R0)`. Introduce `s0`. Rewrite using `[hdet, coeff_sum]`. Simplify using `only [coeff_monomial]`.

Rewrite using `[Finset.sum_eq_single s0]`. Simplify using the standard rewrite rules. Introduce `s _ hs`. Rewrite using `[if_neg (fun h => hs (hinj h))]`. Simplify using the standard rewrite rules.

Establish `hunit : ∀ s0 : Equiv.Perm (Fin r), IsUnit ((((Equiv.Perm.sign s0 : ℤˣ) : ℤ) : R0))` using `fun s0 => (Units.isUnit (Equiv.Perm.sign s0)).map (Int.castRingHom R0)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Establish `h1` using `hcoeff 1`. Rewrite `h1` using `[h0, coeff_zero]`.

Conclude with `(hunit 1).ne_zero h1.symm`. Introduce `μ hμ`. Distinguish the cases in `hex : ∃ s0, mu s0 = μ`. Take `⟨s0, rfl⟩` from `hex`. Rewrite using `[hcoeff]`.

Conclude with `hunit s0`. It suffices to derive a contradiction. Rewrite `hμ` using `[mem_support_iff]`. Apply `hμ` to reduce the goal to its premises. Rewrite using `[hdet, coeff_sum]`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `s _`. Rewrite using `[coeff_monomial, if_neg (fun h => hex ⟨s, h⟩)]`.
-/
theorem determinant_coefficients_units : DeterminantCoefficientsUnits := by
  intro R0 _ _ ι _ r A hA
  let mu : Equiv.Perm (Fin r) → (ι × Fin r →₀ ℕ) := fun s => ∑ i, Finsupp.single (A (s i), i) 1
  have hmu_apply : ∀ (s : Equiv.Perm (Fin r)) (l : ι) (i : Fin r),
      mu s (l, i) = if A (s i) = l then 1 else 0 := by
    intro s l i
    simp only [mu, Finsupp.finsetSum_apply, Finsupp.single_apply, Prod.mk.injEq]
    rw [Finset.sum_eq_single i]
    · simp
    · intro i' _ hi'; simp [hi']
    · simp
  have hinj : Function.Injective mu := by
    intro s t hst
    apply Equiv.ext
    intro i
    have h1 := DFunLike.congr_fun hst (A (s i), i)
    rw [hmu_apply, hmu_apply, if_pos rfl] at h1
    by_contra hne
    have h2 : A (t i) ≠ A (s i) := fun h => hne (hA h).symm
    rw [if_neg h2] at h1
    exact one_ne_zero h1
  have hdet : letterDeterminant R0 A = ∑ s : Equiv.Perm (Fin r), monomial (mu s) (((Equiv.Perm.sign s : ℤˣ) : ℤ) : R0) := by
    unfold letterDeterminant
    rw [Matrix.det_apply]
    apply Finset.sum_congr rfl
    intro s _
    have h1 : ∏ i, (Matrix.of fun i j : Fin r => (X (A i, j) : MvPolynomial (ι × Fin r) R0)) (s i) i =
        monomial (mu s) 1 := by
      simp only [Matrix.of_apply, mu]
      rw [MvPolynomial.monomial_sum_one]
      rfl
    rw [h1]
    rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h <;> simp [h]
  have hcoeff : ∀ s0, (letterDeterminant R0 A).coeff (mu s0) = (((Equiv.Perm.sign s0 : ℤˣ) : ℤ) : R0) := by
    intro s0
    rw [hdet, coeff_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_eq_single s0]
    · simp
    · intro s _ hs
      rw [if_neg (fun h => hs (hinj h))]
    · simp
  have hunit : ∀ s0 : Equiv.Perm (Fin r), IsUnit ((((Equiv.Perm.sign s0 : ℤˣ) : ℤ) : R0)) := fun s0 =>
    (Units.isUnit (Equiv.Perm.sign s0)).map (Int.castRingHom R0)
  refine ⟨?_, ?_⟩
  · intro h0
    have h1 := hcoeff 1
    rw [h0, coeff_zero] at h1
    exact (hunit 1).ne_zero h1.symm
  · intro μ hμ
    by_cases hex : ∃ s0, mu s0 = μ
    · obtain ⟨s0, rfl⟩ := hex
      rw [hcoeff]; exact hunit s0
    · exfalso
      rw [mem_support_iff] at hμ
      apply hμ
      rw [hdet, coeff_sum]
      apply Finset.sum_eq_zero
      intro s _
      rw [coeff_monomial, if_neg (fun h => hex ⟨s, h⟩)]

/- English proof (translation)
The claim follows from `gauss_of_det_coefficients determinant_coefficients_units`.
-/
theorem gauss_quotient_integral : GaussQuotientIntegral := gauss_of_det_coefficients determinant_coefficients_units

/- English proof (translation)
The claim follows from `divisibility_of_field_lemma_and_facts D hE hB components_preserve_valuation gauss_quotient_integral`.
-/
theorem divisibility_of_homogeneous_field_lemma (D : Formalism.BasicNotions.D7) (hE : FieldMultidegreeDivisibility) (hB : IntegralToFieldBaseChange) : Conclusion5 D :=
  divisibility_of_field_lemma_and_facts D hE hB components_preserve_valuation gauss_quotient_integral

/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.Top.lemma4Count N₁ ntops ((2 * Q + 3) * c') (k * Q) c' (alphaMax p Fr k) h`.
-/
theorem divisions_le_total_budget {n' r : ℕ} [NeZero n'] (p : ℕ) (Fr : Frames n' r) (k N₁ Q c' ntops : ℕ)
    (h : ntops ≤ N₁) :
    ntops * ((2 * Q + 3) * c' + k * Q + c') + (c' * alphaMax p Fr k + 2 * c') ≤ mStar p Fr k N₁ Q c' :=
  Formalism.CountingSumsFrames.Top.lemma4Count N₁ ntops ((2 * Q + 3) * c') (k * Q) c' (alphaMax p Fr k) h

/- English proof (translation)
The claim follows from `divisions_le_total_budget p Fr k N₁ Q c' _ (hV.2.2.2.2.2.2.2.1 j)`.
-/
theorem segment_divisions_le_bound {n' r : ℕ} [NeZero n'] (p : ℕ) (Fr : Frames n' r) (k L₁ N₁ Q c' : ℕ)
    (hV : Fr.Valid L₁ N₁) (j : ℤ) :
    (Fr.letters j).card * ((2 * Q + 3) * c' + k * Q + c') + (c' * alphaMax p Fr k + 2 * c') ≤
      mStar p Fr k N₁ Q c' :=
  divisions_le_total_budget p Fr k N₁ Q c' _ (hV.2.2.2.2.2.2.2.1 j)

/- English proof (translation)
Unfold `alpha`. Establish `h1 : Qj Fr p j - 1 ≤ Q` using `le_trans (Nat.sub_le _ _) (hT.1 j)`. Establish `h2 : r * (k - r) * (Qj Fr p j - 1) ≤ r * k * Q` using `Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) h1`. Apply the tactic sequence `have h3 : (if j = 0 then 1 else 0) ≤ 1 := by split_ifs <;> omega`. Use linear arithmetic over natural numbers and integers.
-/
theorem twist_alpha_le_bound {n' r : ℕ} [NeZero n'] (p : ℕ) (Fr : Frames n' r) (k Q : ℕ) (hT : TwistBound p Fr Q) (j : ℤ) :
    alpha p Fr k j ≤ 1 + r * k * Q := by
  unfold alpha
  have h1 : Qj Fr p j - 1 ≤ Q := le_trans (Nat.sub_le _ _) (hT.1 j)
  have h2 : r * (k - r) * (Qj Fr p j - 1) ≤ r * k * Q :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) h1
  have h3 : (if j = 0 then 1 else 0) ≤ 1 := by split_ifs <;> omega
  omega

/- English proof (translation)
The claim follows from `Finset.sup_le fun j _ => twist_alpha_le_bound p Fr k Q hT j`.
-/
theorem alphaMax_le_bound {n' r : ℕ} [NeZero n'] (p : ℕ) (Fr : Frames n' r) (k Q : ℕ) (hT : TwistBound p Fr Q) :
    alphaMax p Fr k ≤ 1 + r * k * Q :=
  Finset.sup_le fun j _ => twist_alpha_le_bound p Fr k Q hT j

/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.Top.lemma4Arith _ _ _ _ _ h0 hB' hsl hms hval`.
-/
theorem symbol_valuation_margin {n' r : ℕ} [NeZero n'] (p : ℕ) (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (k : ℕ) (j x : ℤ)
    (B' ms val : ℝ) (h0 : 0 ≤ Bo p Fr deg j x) (hB' : B' ≤ Bo p Fr deg j x / 80)
    (hsl : (sl p Fr deg Y k j x : ℝ) ≤ Bo p Fr deg j x / 100) (hms : ms ≤ (sl p Fr deg Y k j x : ℝ))
    (hval : Bo p Fr deg j x / 2 - sl p Fr deg Y k j x ≤ val) :
    Bo p Fr deg j x / 4 + ms ≤ val - B' ∧ ms ≤ Bo p Fr deg j x / 4 :=
  Formalism.CountingSumsFrames.Top.lemma4Arith _ _ _ _ _ h0 hB' hsl hms hval

/- English proof (translation)
Unfold `Bo levDeg`. Check the signs of the components of the expression.
-/
theorem level_degree_nonneg {n' r : ℕ} [NeZero n'] (p : ℕ) (Fr : Frames n' r) (deg : Fin n' → ℕ) (j x : ℤ) :
    0 ≤ Bo p Fr deg j x := by
  unfold Bo levDeg
  positivity

/- English proof (translation)
Unfold `Formalism.MainNotions.SourceCleaning.HypII at h`. Take `⟨_, g2, _, g4, g5, g6, g7, g8, g9, g10⟩` from `h`. Establish `e : (C + 1) * (Fr.TT.card : ℝ) * (k : ℝ) ^ 2 * Real.logb p a = C * (Fr.TT.card : ℝ) * (k : ℝ) ^ 2 * Real.logb p a + (Fr.TT.card : ℝ) * (k : ℝ) ^ 2 * Real.logb p a` using `by ring`. Establish `e2 : C * (Fr.TT.card : ℝ) * (k : ℝ) ^ 2 * Real.logb p a = C * ((Fr.TT.card : ℝ) * (k : ℝ) ^ 2 * Real.logb p a)` using `by ring`. Establish `hCX : 0 ≤ C * (Fr.TT.card : ℝ) * (k : ℝ) ^ 2 * Real.logb p a`.

Rewrite using `[e2]; exact mul_nonneg (by linarith) (by linarith)`. Establish `hD0 : 0 ≤ Dd` using `by linarith`. Establish `hfl` using `Nat.floor_le hD0`. Establish `hfl2` using `Nat.lt_floor_add_one Dd`. Use `⟨hp, hr, h1, ?_, g4, g5, by omega, ?_, by linarith, ?_, g10, h2, h3, h4, h5, h6, h7⟩` and prove the remaining obligations.

Conclude with `g2` after adjusting the coercions. Establish `e3 : ((L₁ : ℤ) - 1) = ((L₁ - 1 : ℕ) : ℤ)` using `by omega`. Rewrite `g7` using `[e3, zpow_natCast]`. Conclude with `g7`. Establish `: ((8 * (⌊Dd⌋₊ + 1) : ℕ) : ℝ) ≤ (cStar : ℝ)` using `by push_cast; linarith`.

Conclude with `this` after adjusting the coercions.
-/
theorem hypothesis_numeric_bounds {n' r : ℕ} [NeZero n'] (C : ℝ) (hC : 1 ≤ C) (p : ℕ) (Fr : Frames n' r) (k L₁ N₁ G' : ℕ)
    (deg : Fin n' → ℕ) (a : ℕ) (Y : ℝ) (c0 c'' cStar : ℕ) (Dd : ℝ) (Ns : ℕ) (hp : 13 ≤ p) (hr : 2 ≤ r)
    (h : Formalism.MainNotions.SourceCleaning.HypII C (C + 1) C p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd)
    (hX : 1 ≤ (Fr.TT.card : ℝ) * (k : ℝ) ^ 2 * Real.logb p a)
    (h1 : r ≤ N₁) (h2 : 1 ≤ L₁) (h3 : L₁ ≤ G') (h4 : Ns ≤ N₁) (h5 : Ns ≤ 2 * Fr.TT.card) (h6 : 1 ≤ Fr.J)
    (h7 : Fr.J * r ≤ Fr.TT.card) :
    Formalism.CountingSumsFrames.HypII C p r Fr.TT.card N₁ Ns Fr.J k n' L₁ G' Y a c0 c'' ⌊Dd⌋₊ cStar := by
  unfold Formalism.MainNotions.SourceCleaning.HypII at h
  obtain ⟨_, g2, _, g4, g5, g6, g7, g8, g9, g10⟩ := h
  have e : (C + 1) * (Fr.TT.card : ℝ) * (k : ℝ) ^ 2 * Real.logb p a =
      C * (Fr.TT.card : ℝ) * (k : ℝ) ^ 2 * Real.logb p a + (Fr.TT.card : ℝ) * (k : ℝ) ^ 2 * Real.logb p a := by ring
  have e2 : C * (Fr.TT.card : ℝ) * (k : ℝ) ^ 2 * Real.logb p a =
      C * ((Fr.TT.card : ℝ) * (k : ℝ) ^ 2 * Real.logb p a) := by ring
  have hCX : 0 ≤ C * (Fr.TT.card : ℝ) * (k : ℝ) ^ 2 * Real.logb p a := by
    rw [e2]; exact mul_nonneg (by linarith) (by linarith)
  have hD0 : 0 ≤ Dd := by linarith
  have hfl := Nat.floor_le hD0
  have hfl2 := Nat.lt_floor_add_one Dd
  refine ⟨hp, hr, h1, ?_, g4, g5, by omega, ?_, by linarith, ?_, g10, h2, h3, h4, h5, h6, h7⟩
  · exact_mod_cast g2
  · have e3 : ((L₁ : ℤ) - 1) = ((L₁ - 1 : ℕ) : ℤ) := by omega
    rw [e3, zpow_natCast] at g7
    exact g7
  · have : ((8 * (⌊Dd⌋₊ + 1) : ℕ) : ℝ) ≤ (cStar : ℝ) := by push_cast; linarith
    exact_mod_cast this

/- English proof (translation)
Take `⟨C, hC, H⟩` from `Formalism.CountingSumsFrames.Top.paramsII0 1 1 le_rfl le_rfl`. Use `⟨C, hC, ?_⟩` and prove the remaining obligations. Introduce `n' r _ p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd hp hr hII hT hX h1 h2 h3 h6 h7 j x hB`. Establish `hcore` using `hypothesis_numeric_bounds C hC p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd 0 hp hr hII hX h1 h2 h3 (Nat.zero_le _) (Nat.zero_le _) h6 h7`. Establish `hal : ((alphaMax p Fr k : ℕ) : ℝ) ≤ 1 + r * k * Formalism.CountingSumsFrames.QII p G'`.

Use `alphaMax_le_bound p Fr k (p ^ G') hT` as an intermediate fact. Unfold `Formalism.CountingSumsFrames.QII`. Conclude with `this` after adjusting the coercions. Take `⟨_, hs, _⟩` from `H p r Fr.TT.card N₁ 0 Fr.J k n' L₁ G' Y a (alphaMax p Fr k : ℝ) c0 c'' ⌊Dd⌋₊ cStar hcore (Nat.cast_nonneg _) hal`. Take `⟨hs1, hs2⟩` from `hs (Bo p Fr deg j x) hB`.

Establish `hms : ((mStar p Fr k N₁ (p ^ G') (cPrime n' r Fr.TT.card c0 c'' cStar) : ℕ) : ℝ) = Formalism.CountingSumsFrames.mStarII N₁ k (Formalism.CountingSumsFrames.QII p G') (Formalism.CountingSumsFrames.cPrII r Fr.TT.card n' c0 c'' cStar) (alphaMax p Fr k : ℝ)`. Unfold `mStar cPrime Formalism.CountingSumsFrames.mStarII Formalism.CountingSumsFrames.cPrII Formalism.CountingSumsFrames.omII Formalism.CountingSumsFrames.QII`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hsl : Formalism.CountingSumsFrames.slII Y k (Bo p Fr deg j x) = (sl p Fr deg Y k j x : ℝ)` using `rfl`.

Establish `hpos : 0 ≤ 100 * (r : ℝ) ^ 2 * Formalism.CountingSumsFrames.cPrII r Fr.TT.card n' c0 c'' cStar + 24 * ((N₁ : ℝ) + r) * c0`. Unfold `Formalism.CountingSumsFrames.cPrII Formalism.CountingSumsFrames.omII`. Check the signs of the components of the expression. Rewrite `hs1`, `hs2` using `[hsl]`. Use `⟨?_, hs2⟩` and prove the remaining obligations.

Rewrite using `[hms]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem slope_bounds_alt : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (n' r : ℕ) [NeZero n'] (p : ℕ) (Fr : Frames n' r) (k L₁ N₁ G' : ℕ) (deg : Fin n' → ℕ) (a : ℕ) (Y : ℝ)
      (c0 c'' cStar : ℕ) (Dd : ℝ), 13 ≤ p → 2 ≤ r →
      Formalism.MainNotions.SourceCleaning.HypII C (C + 1) C p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd → TwistBound p Fr (p ^ G') →
      1 ≤ (Fr.TT.card : ℝ) * (k : ℝ) ^ 2 * Real.logb p a →
      r ≤ N₁ → 1 ≤ L₁ → L₁ ≤ G' → 1 ≤ Fr.J → Fr.J * r ≤ Fr.TT.card →
      ∀ j x : ℤ, (a : ℝ) / (p : ℝ) ^ G' ≤ Bo p Fr deg j x →
        (mStar p Fr k N₁ (p ^ G') (cPrime n' r Fr.TT.card c0 c'' cStar) : ℝ) ≤ (sl p Fr deg Y k j x : ℝ) ∧
          (sl p Fr deg Y k j x : ℝ) ≤ Bo p Fr deg j x / 100 := by
  obtain ⟨C, hC, H⟩ := Formalism.CountingSumsFrames.Top.paramsII0 1 1 le_rfl le_rfl
  refine ⟨C, hC, ?_⟩
  intro n' r _ p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd hp hr hII hT hX h1 h2 h3 h6 h7 j x hB
  have hcore := hypothesis_numeric_bounds C hC p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd 0 hp hr hII hX h1 h2 h3
    (Nat.zero_le _) (Nat.zero_le _) h6 h7
  have hal : ((alphaMax p Fr k : ℕ) : ℝ) ≤ 1 + r * k * Formalism.CountingSumsFrames.QII p G' := by
    have := alphaMax_le_bound p Fr k (p ^ G') hT
    unfold Formalism.CountingSumsFrames.QII
    exact_mod_cast this
  obtain ⟨_, hs, _⟩ := H p r Fr.TT.card N₁ 0 Fr.J k n' L₁ G' Y a (alphaMax p Fr k : ℝ) c0 c'' ⌊Dd⌋₊ cStar hcore
    (Nat.cast_nonneg _) hal
  obtain ⟨hs1, hs2⟩ := hs (Bo p Fr deg j x) hB
  have hms : ((mStar p Fr k N₁ (p ^ G') (cPrime n' r Fr.TT.card c0 c'' cStar) : ℕ) : ℝ) =
      Formalism.CountingSumsFrames.mStarII N₁ k (Formalism.CountingSumsFrames.QII p G') (Formalism.CountingSumsFrames.cPrII r Fr.TT.card n' c0 c'' cStar)
        (alphaMax p Fr k : ℝ) := by
    unfold mStar cPrime Formalism.CountingSumsFrames.mStarII Formalism.CountingSumsFrames.cPrII Formalism.CountingSumsFrames.omII Formalism.CountingSumsFrames.QII
    push_cast
    ring
  have hsl : Formalism.CountingSumsFrames.slII Y k (Bo p Fr deg j x) = (sl p Fr deg Y k j x : ℝ) := rfl
  have hpos : 0 ≤ 100 * (r : ℝ) ^ 2 * Formalism.CountingSumsFrames.cPrII r Fr.TT.card n' c0 c'' cStar + 24 * ((N₁ : ℝ) + r) * c0 := by
    unfold Formalism.CountingSumsFrames.cPrII Formalism.CountingSumsFrames.omII
    positivity
  rw [hsl] at hs1 hs2
  refine ⟨?_, hs2⟩
  rw [hms]
  linarith

/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.Top.powerSplit _ Dp h _ P n c hP`.
-/
theorem pow_add_mul_mem_span_sup {O : Type} [CommRing O] {n' k : ℕ} (Dp h : MvPolynomial (TV n' k) O) (p P n c : ℕ)
    (hP : 1 ≤ P) :
    (Dp ^ P + (p : MvPolynomial (TV n' k) O) * h) ^ n ∈
      Ideal.span {Dp ^ (n - c)} ⊔ Ideal.span {(p : MvPolynomial (TV n' k) O) ^ c} :=
  Formalism.CountingSumsFrames.Top.powerSplit _ Dp h _ P n c hP

/- English proof (translation)
Establish `hidx : l.length - r < l.length` using `by omega`. Rewrite using `[List.getD_eq_getElem _ _ hidx]`. Conclude with `List.getElem_mem hidx`.
-/
theorem getD_mem_list (l : List ℤ) (r : ℕ) (hr : 1 ≤ r) (hl : 0 < l.length) : l.getD (l.length - r) 0 ∈ l := by
  have hidx : l.length - r < l.length := by omega
  rw [List.getD_eq_getElem _ _ hidx]
  exact List.getElem_mem hidx

/- English proof (translation)
Establish `hmono : ∀ i, i < r → Fr.fr (j - 1) 0 ≤ Fr.fr (j - 1) i`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro _`. Conclude with `le_rfl`.

Consider the case `succ i ih => intro hi; exact le_trans (ih (by omega)) (le_of_lt (hV.2.2.1 (j - 1) i hi))`. Establish `hx'` using `hx`. Unfold `Frames.letters at hx'`. Rewrite `hx'` using `[Finset.mem_filter, Finset.mem_Icc]`. Establish `hWx : Fr.fr (j - 1) (r - 1) < x`.

Unfold `Frames.IsW at hW`. Use linear arithmetic over natural numbers and integers. Establish `hy0 : Fr.fr (j - 1) (r - 1) ∈ (Fr.letters j).filter (fun z => Even z ∧ z < x)`. Rewrite using `[Finset.mem_filter]`. Use `⟨?_, (hV.2.2.2.2.1 (j - 1) (r - 1) (by omega)).2, hWx⟩` and prove the remaining obligations.

Unfold `Frames.letters`. Rewrite using `[Finset.mem_filter, Finset.mem_Icc]`. Conclude with `⟨⟨hmono (r - 1) (by omega), by omega⟩, (hV.2.2.2.2.1 (j - 1) (r - 1) (by omega)).1⟩`. Establish `hlen : 0 < (((Fr.letters j).filter fun z => Even z ∧ z < x).sort (· ≤ ·)).length`. Apply `List.length_pos_of_mem (a := Fr.fr (j - 1) (r - 1))` to reduce the goal to its premises.

Rewrite using `[Finset.mem_sort]`. Conclude with `hy0`. Establish `h : Fr.oldest j x ∈ ((Fr.letters j).filter fun z => Even z ∧ z < x).sort (· ≤ ·)` using `getD_mem_list _ r hr hlen`. Rewrite `h` using `[Finset.mem_sort]`. Conclude with `(Finset.mem_filter.1 h).1`.
-/
theorem oldest_mem_segment_letters {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (L₁ N₁ : ℕ) (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r)
    (j x : ℤ) (hx : x ∈ Fr.letters j) (hW : ¬ Fr.IsW j x) : Fr.oldest j x ∈ Fr.letters j := by
  have hmono : ∀ i, i < r → Fr.fr (j - 1) 0 ≤ Fr.fr (j - 1) i := by
    intro i
    induction i with
    | zero => intro _; exact le_rfl
    | succ i ih => intro hi; exact le_trans (ih (by omega)) (le_of_lt (hV.2.2.1 (j - 1) i hi))
  have hx' := hx
  unfold Frames.letters at hx'
  rw [Finset.mem_filter, Finset.mem_Icc] at hx'
  have hWx : Fr.fr (j - 1) (r - 1) < x := by
    unfold Frames.IsW at hW
    omega
  have hy0 : Fr.fr (j - 1) (r - 1) ∈ (Fr.letters j).filter (fun z => Even z ∧ z < x) := by
    rw [Finset.mem_filter]
    refine ⟨?_, (hV.2.2.2.2.1 (j - 1) (r - 1) (by omega)).2, hWx⟩
    unfold Frames.letters
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hmono (r - 1) (by omega), by omega⟩, (hV.2.2.2.2.1 (j - 1) (r - 1) (by omega)).1⟩
  have hlen : 0 < (((Fr.letters j).filter fun z => Even z ∧ z < x).sort (· ≤ ·)).length := by
    apply List.length_pos_of_mem (a := Fr.fr (j - 1) (r - 1))
    rw [Finset.mem_sort]
    exact hy0
  have h : Fr.oldest j x ∈ ((Fr.letters j).filter fun z => Even z ∧ z < x).sort (· ≤ ·) :=
    getD_mem_list _ r hr hlen
  rw [Finset.mem_sort] at h
  exact (Finset.mem_filter.1 h).1

/- English proof (translation)
Establish `hy` using `oldest_mem_segment_letters Fr L₁ N₁ hV hr j x hx hW`. Unfold `Formalism.MainNotions.SourceCleaning.HypII at h`. Take `⟨g1, _, g3, _⟩` from `h`. Unfold `Frames.letters at hy`. Rewrite `hy` using `[Finset.mem_filter, Finset.mem_Icc]`.

Take `⟨⟨hy1, hy2⟩, hy3⟩` from `hy`. Establish `hdeg` using `(g3 _ hy3).1`. Establish `hdist : Fr.dist j (Fr.oldest j x) ≤ G'`. Unfold `Frames.dist`. Establish `h1` using `g1 j`.

Unfold `zF at h1`. Conclude with `Int.toNat_le.2 (by omega)`. Unfold `Bo levDeg`. Establish `hp' : (1 : ℝ) ≤ p` using `by exact_mod_cast hp`. Establish `hpow : (p : ℝ) ^ (Fr.dist j (Fr.oldest j x)) ≤ (p : ℝ) ^ G'` using `pow_le_pow_right₀ hp' hdist`.

Establish `hpos : 0 < (p : ℝ) ^ (Fr.dist j (Fr.oldest j x))` using `pow_pos (by linarith) _`. Establish `hc : (0 : ℝ) ≤ c''` using `Nat.cast_nonneg _`. Conclude with `div_le_div₀ (Nat.cast_nonneg _) (by linarith) hpos hpow`.
-/
theorem level_degree_ge_ratio {n' r : ℕ} [NeZero n'] (CLa CD Csz : ℝ) (p : ℕ) (hp : 1 ≤ p) (Fr : Frames n' r)
    (k L₁ N₁ G' : ℕ) (deg : Fin n' → ℕ) (a : ℕ) (Y : ℝ) (c0 c'' cStar : ℕ) (Dd : ℝ) (hV : Fr.Valid L₁ N₁)
    (hr : 1 ≤ r) (h : Formalism.MainNotions.SourceCleaning.HypII CLa CD Csz p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd) (j x : ℤ)
    (hx : x ∈ Fr.letters j) (hW : ¬ Fr.IsW j x) : (a : ℝ) / (p : ℝ) ^ G' ≤ Bo p Fr deg j x := by
  have hy := oldest_mem_segment_letters Fr L₁ N₁ hV hr j x hx hW
  unfold Formalism.MainNotions.SourceCleaning.HypII at h
  obtain ⟨g1, _, g3, _⟩ := h
  unfold Frames.letters at hy
  rw [Finset.mem_filter, Finset.mem_Icc] at hy
  obtain ⟨⟨hy1, hy2⟩, hy3⟩ := hy
  have hdeg := (g3 _ hy3).1
  have hdist : Fr.dist j (Fr.oldest j x) ≤ G' := by
    unfold Frames.dist
    have h1 := g1 j
    unfold zF at h1
    exact Int.toNat_le.2 (by omega)
  unfold Bo levDeg
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpow : (p : ℝ) ^ (Fr.dist j (Fr.oldest j x)) ≤ (p : ℝ) ^ G' := pow_le_pow_right₀ hp' hdist
  have hpos : 0 < (p : ℝ) ^ (Fr.dist j (Fr.oldest j x)) := pow_pos (by linarith) _
  have hc : (0 : ℝ) ≤ c'' := Nat.cast_nonneg _
  exact div_le_div₀ (Nat.cast_nonneg _) (by linarith) hpos hpow

/- English proof (translation)
Take `⟨C, hC, H⟩` from `slope_bounds_alt`. Use `⟨C, hC, ?_⟩` and prove the remaining obligations. Introduce `n' r _ p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd hp hr hV hII hT hX h1 h2 h3 h7 j x hx hW`. Conclude with `H n' r p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd hp hr hII hT hX h1 h2 h3 hV.1 h7 j x (level_degree_ge_ratio _ _ _ p (by omega) Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd hV (by omega) hII j x hx hW)`.
-/
theorem slope_bounds_on_letters : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (n' r : ℕ) [NeZero n'] (p : ℕ) (Fr : Frames n' r) (k L₁ N₁ G' : ℕ) (deg : Fin n' → ℕ) (a : ℕ) (Y : ℝ)
      (c0 c'' cStar : ℕ) (Dd : ℝ), 13 ≤ p → 2 ≤ r → Fr.Valid L₁ N₁ →
      Formalism.MainNotions.SourceCleaning.HypII C (C + 1) C p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd → TwistBound p Fr (p ^ G') →
      1 ≤ (Fr.TT.card : ℝ) * (k : ℝ) ^ 2 * Real.logb p a →
      r ≤ N₁ → 1 ≤ L₁ → L₁ ≤ G' → Fr.J * r ≤ Fr.TT.card →
      ∀ j x : ℤ, x ∈ Fr.letters j → ¬ Fr.IsW j x →
        (mStar p Fr k N₁ (p ^ G') (cPrime n' r Fr.TT.card c0 c'' cStar) : ℝ) ≤ (sl p Fr deg Y k j x : ℝ) ∧
          (sl p Fr deg Y k j x : ℝ) ≤ Bo p Fr deg j x / 100 := by
  obtain ⟨C, hC, H⟩ := slope_bounds_alt
  refine ⟨C, hC, ?_⟩
  intro n' r _ p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd hp hr hV hII hT hX h1 h2 h3 h7 j x hx hW
  exact H n' r p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd hp hr hII hT hX h1 h2 h3 hV.1 h7 j x
    (level_degree_ge_ratio _ _ _ p (by omega) Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd hV (by omega) hII j x hx hW)

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro _`. Conclude with `le_rfl`. Consider the case `succ i ih => intro hi; exact le_trans (ih (by omega)) (le_of_lt (hV.2.2.1 j i hi))`.
-/
theorem frame_row_monotone {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (L₁ N₁ : ℕ) (hV : Fr.Valid L₁ N₁) (j : ℤ) :
    ∀ i, i < r → Fr.fr j 0 ≤ Fr.fr j i := by
  intro i
  induction i with
  | zero => intro _; exact le_rfl
  | succ i ih => intro hi; exact le_trans (ih (by omega)) (le_of_lt (hV.2.2.1 j i hi))

/- English proof (translation)
Establish `h4` using `hV.2.2.2.1 ((0 : ℤ) - 1)`. Rewrite `h4` using `[sub_add_cancel]`. Establish `hm0` using `frame_row_monotone Fr L₁ N₁ hV 0 (r - 1) (by omega)`. Establish `hm1` using `frame_row_monotone Fr L₁ N₁ hV ((0 : ℤ) - 1) (r - 1) (by omega)`. Establish `hx : Fr.fr 0 (r - 1) ∈ Fr.letters 0`.

Unfold `Frames.letters`. Rewrite using `[Finset.mem_filter, Finset.mem_Icc]`. Conclude with `⟨⟨by omega, le_rfl⟩, (hV.2.2.2.2.1 0 (r - 1) (by omega)).1⟩`. Establish `hW : ¬ Fr.IsW 0 (Fr.fr 0 (r - 1))`. Unfold `Frames.IsW`.

Use linear arithmetic over natural numbers and integers. Establish `h9` using `hV.2.2.2.2.2.2.2.2 0 _ hx hW`. Establish `hy` using `oldest_mem_segment_letters Fr L₁ N₁ hV hr 0 _ hx hW`. Unfold `Frames.letters at hy`. Rewrite `hy` using `[Finset.mem_filter, Finset.mem_Icc]`.

Establish `h1` using `g1 0`. Unfold `zF at h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem first_length_le_gap {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (L₁ N₁ G' : ℕ) (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r)
    (g1 : ∀ j : ℤ, zF Fr j - Fr.fr (j - 1) 0 ≤ G') : L₁ ≤ G' := by
  have h4 := hV.2.2.2.1 ((0 : ℤ) - 1)
  rw [sub_add_cancel] at h4
  have hm0 := frame_row_monotone Fr L₁ N₁ hV 0 (r - 1) (by omega)
  have hm1 := frame_row_monotone Fr L₁ N₁ hV ((0 : ℤ) - 1) (r - 1) (by omega)
  have hx : Fr.fr 0 (r - 1) ∈ Fr.letters 0 := by
    unfold Frames.letters
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, le_rfl⟩, (hV.2.2.2.2.1 0 (r - 1) (by omega)).1⟩
  have hW : ¬ Fr.IsW 0 (Fr.fr 0 (r - 1)) := by
    unfold Frames.IsW
    omega
  have h9 := hV.2.2.2.2.2.2.2.2 0 _ hx hW
  have hy := oldest_mem_segment_letters Fr L₁ N₁ hV hr 0 _ hx hW
  unfold Frames.letters at hy
  rw [Finset.mem_filter, Finset.mem_Icc] at hy
  have h1 := g1 0
  unfold zF at h1
  omega

/- English proof (translation)
The claim follows from `Finset.card_pos.2 ⟨_, (hV.2.2.2.2.1 0 0 (by omega)).1⟩`.
-/
theorem frame_tops_card_pos {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (L₁ N₁ : ℕ) (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) :
    1 ≤ Fr.TT.card :=
  Finset.card_pos.2 ⟨_, (hV.2.2.2.2.1 0 0 (by omega)).1⟩

/- English proof (translation)
Assume the negation of the conclusion as `hL`. Establish `hL0 : L₁ = 0` using `by omega`. Substitute `hL0` using the available equality. Establish `hp' : (1 : ℝ) ≤ p` using `by exact_mod_cast hp`. Establish `hk' : (1 : ℝ) ≤ k` using `by exact_mod_cast hk`.

Establish `hN' : (1 : ℝ) ≤ N` using `by exact_mod_cast hN`. Establish `e1 : (p : ℝ) ^ (((0 : ℕ) : ℤ) - 1) = (p : ℝ)⁻¹` using `by simp`. Rewrite `g7` using `[e1]`. Establish `h1 : (p : ℝ)⁻¹ ≤ 1` using `inv_le_one_of_one_le₀ hp'`. Establish `h2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 * N * Y ^ 2` using `one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hk') hN') (one_le_pow₀ hY)`.

Establish `e2 : 256 * (k : ℝ) ^ 2 * N * Y ^ 2 = 256 * ((k : ℝ) ^ 2 * N * Y ^ 2)` using `by ring`. Rewrite `g7` using `[e2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_le_first_length (p k N L₁ : ℕ) (Y : ℝ) (hp : 1 ≤ p) (hk : 1 ≤ k) (hN : 1 ≤ N) (hY : 1 ≤ Y)
    (g7 : 256 * (k : ℝ) ^ 2 * N * Y ^ 2 ≤ (p : ℝ) ^ ((L₁ : ℤ) - 1)) : 1 ≤ L₁ := by
  by_contra hL
  have hL0 : L₁ = 0 := by omega
  subst hL0
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have e1 : (p : ℝ) ^ (((0 : ℕ) : ℤ) - 1) = (p : ℝ)⁻¹ := by simp
  rw [e1] at g7
  have h1 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp'
  have h2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 * N * Y ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hk') hN') (one_le_pow₀ hY)
  have e2 : 256 * (k : ℝ) ^ 2 * N * Y ^ 2 = 256 * ((k : ℝ) ^ 2 * N * Y ^ 2) := by ring
  rw [e2] at g7
  linarith

/- English proof (translation)
Introduce `i'`. Proceed by induction on `i' with`. Consider the case `zero => intro h`. Use linear arithmetic over natural numbers and integers. Consider the case `succ t ih`.

Introduce `h ht`. Break down `Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'` into its components or cases. Conclude with `lt_trans (ih h' (by omega)) (hV.2.2.1 j t ht)`. Substitute `h'` using the available equality. Conclude with `hV.2.2.1 j i ht`.
-/
theorem frame_entries_strictMono {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (L₁ N₁ : ℕ) (hV : Fr.Valid L₁ N₁) (j : ℤ) (i : ℕ) :
    ∀ i', i < i' → i' < r → Fr.fr j i < Fr.fr j i' := by
  intro i'
  induction i' with
  | zero => intro h; omega
  | succ t ih =>
    intro h ht
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'
    · exact lt_trans (ih h' (by omega)) (hV.2.2.1 j t ht)
    · subst h'; exact hV.2.2.1 j i ht

/- English proof (translation)
Establish `h4` using `hV.2.2.2.1 ((0 : ℤ) - 1)`. Rewrite `h4` using `[sub_add_cancel]`. Establish `hm1` using `frame_row_monotone Fr L₁ N₁ hV ((0 : ℤ) - 1) (r - 1) (by omega)`. Establish `hcard : (Finset.range r).card ≤ (Fr.letters 0).card`. Apply `Finset.card_le_card_of_injOn (fun i => Fr.fr 0 i)` to reduce the goal to its premises.

Introduce `i hi`. Establish `hi' : i < r` using `Finset.mem_range.1 hi`. Establish `hm0` using `frame_row_monotone Fr L₁ N₁ hV 0 i hi'`. Establish `hup : Fr.fr 0 i ≤ Fr.fr 0 (r - 1)`. Break down `Nat.lt_or_ge i (r - 1) with h | h` into its components or cases.

Conclude with `le_of_lt (frame_entries_strictMono Fr L₁ N₁ hV 0 i (r - 1) h (by omega))`. Establish `: i = r - 1` using `by omega`. Rewrite using `[this]`. Use `show Fr.fr 0 i ∈ Fr.letters 0`. Unfold `Frames.letters`.

Rewrite using `[Finset.mem_filter, Finset.mem_Icc]`. Conclude with `⟨⟨by omega, hup⟩, (hV.2.2.2.2.1 0 i hi').1⟩`. Introduce `i hi i' hi' he`. Establish `h1 : i < r` using `Finset.mem_range.1 hi`. Establish `h2 : i' < r` using `Finset.mem_range.1 hi'`.

Establish `he' : Fr.fr 0 i = Fr.fr 0 i'` using `he`. Break down `Nat.lt_trichotomy i i' with h | h | h` into its components or cases. Use `frame_entries_strictMono Fr L₁ N₁ hV 0 i i' h h2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `h`.

Use `frame_entries_strictMono Fr L₁ N₁ hV 0 i' i h h1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite `hcard` using `[Finset.card_range]`. Conclude with `le_trans hcard (hV.2.2.2.2.2.2.2.1 0)`.
-/
theorem rank_le_segment_length {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (L₁ N₁ : ℕ) (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) :
    r ≤ N₁ := by
  have h4 := hV.2.2.2.1 ((0 : ℤ) - 1)
  rw [sub_add_cancel] at h4
  have hm1 := frame_row_monotone Fr L₁ N₁ hV ((0 : ℤ) - 1) (r - 1) (by omega)
  have hcard : (Finset.range r).card ≤ (Fr.letters 0).card := by
    apply Finset.card_le_card_of_injOn (fun i => Fr.fr 0 i)
    · intro i hi
      have hi' : i < r := Finset.mem_range.1 hi
      have hm0 := frame_row_monotone Fr L₁ N₁ hV 0 i hi'
      have hup : Fr.fr 0 i ≤ Fr.fr 0 (r - 1) := by
        rcases Nat.lt_or_ge i (r - 1) with h | h
        · exact le_of_lt (frame_entries_strictMono Fr L₁ N₁ hV 0 i (r - 1) h (by omega))
        · have : i = r - 1 := by omega
          rw [this]
      show Fr.fr 0 i ∈ Fr.letters 0
      unfold Frames.letters
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, hup⟩, (hV.2.2.2.2.1 0 i hi').1⟩
    · intro i hi i' hi' he
      have h1 : i < r := Finset.mem_range.1 hi
      have h2 : i' < r := Finset.mem_range.1 hi'
      have he' : Fr.fr 0 i = Fr.fr 0 i' := he
      rcases Nat.lt_trichotomy i i' with h | h | h
      · have := frame_entries_strictMono Fr L₁ N₁ hV 0 i i' h h2; omega
      · exact h
      · have := frame_entries_strictMono Fr L₁ N₁ hV 0 i' i h h1; omega
  rw [Finset.card_range] at hcard
  exact le_trans hcard (hV.2.2.2.2.2.2.2.1 0)

/- English proof (translation)
Establish `hp' : (2 : ℝ) ≤ p` using `by exact_mod_cast hp`. Establish `hk' : (1 : ℝ) ≤ k` using `by exact_mod_cast hk`. Establish `hN' : (1 : ℝ) ≤ N` using `by exact_mod_cast hN`. Establish `hr' : (1 : ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `hlog0 : 0 ≤ Real.logb p a`.

Unfold `Real.logb`. Conclude with `div_nonneg (Real.log_natCast_nonneg a) (Real.log_natCast_nonneg p)`. Establish `hD0 : 0 ≤ Dd`. Use `le_trans ?_ g8` and prove the remaining obligations. Conclude with `mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)) hlog0`.

Establish `hom : (0 : ℝ) ≤ (r : ℝ) * N * c0 + 2 * r * n' * c''` using `by positivity`. Establish `hc : (1 : ℝ) ≤ (cStar : ℝ) + ((r : ℝ) * N * c0 + 2 * r * n' * c'')` using `by linarith`. Establish `hQ : (p : ℝ) ≤ ((p : ℝ) ^ G') ^ 5`. Rewrite using `[← pow_mul]`. Combine the equalities or inequalities in the displayed calculation.

Establish `a1 : (1 : ℝ) ≤ C * (k : ℝ) ^ 3 * (r : ℝ) ^ 2 * N` using `one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hk')) (one_le_pow₀ hr')) hN'`. Establish `hQ0 : (0 : ℝ) ≤ ((p : ℝ) ^ G') ^ 5` using `by positivity`. Establish `a2 : (p : ℝ) ≤ C * (k : ℝ) ^ 3 * (r : ℝ) ^ 2 * N * ((p : ℝ) ^ G') ^ 5` using `le_trans hQ (le_mul_of_one_le_left hQ0 a1)`. Establish `a20 : (0 : ℝ) ≤ C * (k : ℝ) ^ 3 * (r : ℝ) ^ 2 * N * ((p : ℝ) ^ G') ^ 5` using `by linarith`. Establish `a3 : (p : ℝ) ≤ C * (k : ℝ) ^ 3 * (r : ℝ) ^ 2 * N * ((p : ℝ) ^ G') ^ 5 * ((cStar : ℝ) + ((r : ℝ) * N * c0 + 2 * r * n' * c''))` using `le_trans a2 (le_mul_of_one_le_right a20 hc)`.

Establish `a30 : (0 : ℝ) ≤ C * (k : ℝ) ^ 3 * (r : ℝ) ^ 2 * N * ((p : ℝ) ^ G') ^ 5 * ((cStar : ℝ) + ((r : ℝ) * N * c0 + 2 * r * n' * c''))` using `by linarith`. Establish `hpa : (p : ℝ) ≤ a` using `le_trans (le_trans a3 (le_mul_of_one_le_right a30 hY)) g10`. Establish `hlog1 : 1 ≤ Real.logb p a`. Rewrite using `[Real.le_logb_iff_rpow_le (by linarith) (by linarith)]`. Simplify using `using hpa`.

Conclude with `one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hN' (one_le_pow₀ hk')) hlog1`.
-/
theorem one_le_tops_log_bound (C : ℝ) (hC : 1 ≤ C) (p r N k n' G' a c0 c'' cStar : ℕ) (Y Dd : ℝ) (hp : 2 ≤ p) (hr : 1 ≤ r)
    (hN : 1 ≤ N) (hk : 1 ≤ k) (hG : 1 ≤ G') (hY : 1 ≤ Y)
    (g8 : (C + 1) * (N : ℝ) * (k : ℝ) ^ 2 * Real.logb p a ≤ Dd) (g9 : 8 * (Dd + 1) ≤ (cStar : ℝ))
    (g10 : C * (k : ℝ) ^ 3 * (r : ℝ) ^ 2 * N * ((p : ℝ) ^ G') ^ 5 *
      ((cStar : ℝ) + ((r : ℝ) * N * c0 + 2 * r * n' * c'')) * Y ≤ a) :
    1 ≤ (N : ℝ) * (k : ℝ) ^ 2 * Real.logb p a := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hlog0 : 0 ≤ Real.logb p a := by
    unfold Real.logb
    exact div_nonneg (Real.log_natCast_nonneg a) (Real.log_natCast_nonneg p)
  have hD0 : 0 ≤ Dd := by
    refine le_trans ?_ g8
    exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)) hlog0
  have hom : (0 : ℝ) ≤ (r : ℝ) * N * c0 + 2 * r * n' * c'' := by positivity
  have hc : (1 : ℝ) ≤ (cStar : ℝ) + ((r : ℝ) * N * c0 + 2 * r * n' * c'') := by linarith
  have hQ : (p : ℝ) ≤ ((p : ℝ) ^ G') ^ 5 := by
    rw [← pow_mul]
    calc (p : ℝ) = (p : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (p : ℝ) ^ (G' * 5) := pow_le_pow_right₀ (by linarith) (by omega)
  have a1 : (1 : ℝ) ≤ C * (k : ℝ) ^ 3 * (r : ℝ) ^ 2 * N :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hk')) (one_le_pow₀ hr')) hN'
  have hQ0 : (0 : ℝ) ≤ ((p : ℝ) ^ G') ^ 5 := by positivity
  have a2 : (p : ℝ) ≤ C * (k : ℝ) ^ 3 * (r : ℝ) ^ 2 * N * ((p : ℝ) ^ G') ^ 5 :=
    le_trans hQ (le_mul_of_one_le_left hQ0 a1)
  have a20 : (0 : ℝ) ≤ C * (k : ℝ) ^ 3 * (r : ℝ) ^ 2 * N * ((p : ℝ) ^ G') ^ 5 := by linarith
  have a3 : (p : ℝ) ≤ C * (k : ℝ) ^ 3 * (r : ℝ) ^ 2 * N * ((p : ℝ) ^ G') ^ 5 *
      ((cStar : ℝ) + ((r : ℝ) * N * c0 + 2 * r * n' * c'')) :=
    le_trans a2 (le_mul_of_one_le_right a20 hc)
  have a30 : (0 : ℝ) ≤ C * (k : ℝ) ^ 3 * (r : ℝ) ^ 2 * N * ((p : ℝ) ^ G') ^ 5 *
      ((cStar : ℝ) + ((r : ℝ) * N * c0 + 2 * r * n' * c'')) := by linarith
  have hpa : (p : ℝ) ≤ a := le_trans (le_trans a3 (le_mul_of_one_le_right a30 hY)) g10
  have hlog1 : 1 ≤ Real.logb p a := by
    rw [Real.le_logb_iff_rpow_le (by linarith) (by linarith)]
    simpa using hpa
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hN' (one_le_pow₀ hk')) hlog1

/- English proof (translation)
Take `⟨C, hC, H⟩` from `slope_bounds_on_letters`. Use `⟨C, hC, ?_⟩` and prove the remaining obligations. Introduce `n' r _ p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd hp hr hV hII hT h7 j x hx hW`. Establish `hII'` using `hII`. Unfold `Formalism.MainNotions.SourceCleaning.HypII at hII'`.

Take `⟨g1, _, _, g4, _, g6, g7, g8, g9, g10⟩` from `hII'`. Establish `hr' : (2 : ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `hY : 1 ≤ Y` using `by linarith`. Establish `hk : 1 ≤ k` using `by omega`. Establish `hN` using `frame_tops_card_pos Fr L₁ N₁ hV (by omega)`.

Establish `hL1` using `one_le_first_length p k Fr.TT.card L₁ Y (by omega) hk hN hY g7`. Establish `hLG` using `first_length_le_gap Fr L₁ N₁ G' hV (by omega) g1`. Establish `hX` using `one_le_tops_log_bound C hC p r Fr.TT.card k n' G' a c0 c'' cStar Y Dd (by omega) (by omega) hN hk (by omega) hY g8 g9 g10`. Conclude with `H n' r p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd hp hr hV hII hT hX (rank_le_segment_length Fr L₁ N₁ hV (by omega)) hL1 hLG h7 j x hx hW`.
-/
theorem segment_length_bounds_real : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (n' r : ℕ) [NeZero n'] (p : ℕ) (Fr : Frames n' r) (k L₁ N₁ G' : ℕ) (deg : Fin n' → ℕ) (a : ℕ) (Y : ℝ)
      (c0 c'' cStar : ℕ) (Dd : ℝ), 13 ≤ p → 2 ≤ r → Fr.Valid L₁ N₁ →
      Formalism.MainNotions.SourceCleaning.HypII C (C + 1) C p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd → TwistBound p Fr (p ^ G') →
      Fr.J * r ≤ Fr.TT.card →
      ∀ j x : ℤ, x ∈ Fr.letters j → ¬ Fr.IsW j x →
        (mStar p Fr k N₁ (p ^ G') (cPrime n' r Fr.TT.card c0 c'' cStar) : ℝ) ≤ (sl p Fr deg Y k j x : ℝ) ∧
          (sl p Fr deg Y k j x : ℝ) ≤ Bo p Fr deg j x / 100 := by
  obtain ⟨C, hC, H⟩ := slope_bounds_on_letters
  refine ⟨C, hC, ?_⟩
  intro n' r _ p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd hp hr hV hII hT h7 j x hx hW
  have hII' := hII
  unfold Formalism.MainNotions.SourceCleaning.HypII at hII'
  obtain ⟨g1, _, _, g4, _, g6, g7, g8, g9, g10⟩ := hII'
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hY : 1 ≤ Y := by linarith
  have hk : 1 ≤ k := by omega
  have hN := frame_tops_card_pos Fr L₁ N₁ hV (by omega)
  have hL1 := one_le_first_length p k Fr.TT.card L₁ Y (by omega) hk hN hY g7
  have hLG := first_length_le_gap Fr L₁ N₁ G' hV (by omega) g1
  have hX := one_le_tops_log_bound C hC p r Fr.TT.card k n' G' a c0 c'' cStar Y Dd (by omega) (by omega) hN hk (by omega) hY
    g8 g9 g10
  exact H n' r p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd hp hr hV hII hT hX
    (rank_le_segment_length Fr L₁ N₁ hV (by omega)) hL1 hLG h7 j x hx hW

/- English proof (translation)
Take `⟨C, hC, H⟩` from `segment_length_bounds_real`. Use `⟨C, hC, ?_⟩` and prove the remaining obligations. Introduce `n' r _ p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd hp hr hV hII hT h7 j x hx hW B' val hB' hval`. Take `⟨h1, h2⟩` from `H n' r p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd hp hr hV hII hT h7 j x hx hW`. Conclude with `symbol_valuation_margin p Fr deg Y k j x B' _ val (level_degree_nonneg p Fr deg j x) hB' h2 h1 hval`.
-/
theorem margin_real_bound : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (n' r : ℕ) [NeZero n'] (p : ℕ) (Fr : Frames n' r) (k L₁ N₁ G' : ℕ) (deg : Fin n' → ℕ) (a : ℕ) (Y : ℝ)
      (c0 c'' cStar : ℕ) (Dd : ℝ), 13 ≤ p → 2 ≤ r → Fr.Valid L₁ N₁ →
      Formalism.MainNotions.SourceCleaning.HypII C (C + 1) C p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd → TwistBound p Fr (p ^ G') →
      Fr.J * r ≤ Fr.TT.card →
      ∀ j x : ℤ, x ∈ Fr.letters j → ¬ Fr.IsW j x → ∀ B' val : ℝ, B' ≤ Bo p Fr deg j x / 80 →
        Bo p Fr deg j x / 2 - sl p Fr deg Y k j x ≤ val →
        Bo p Fr deg j x / 4 + (mStar p Fr k N₁ (p ^ G') (cPrime n' r Fr.TT.card c0 c'' cStar) : ℝ) ≤ val - B' ∧
          (mStar p Fr k N₁ (p ^ G') (cPrime n' r Fr.TT.card c0 c'' cStar) : ℝ) ≤ Bo p Fr deg j x / 4 := by
  obtain ⟨C, hC, H⟩ := segment_length_bounds_real
  refine ⟨C, hC, ?_⟩
  intro n' r _ p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd hp hr hV hII hT h7 j x hx hW B' val hB' hval
  obtain ⟨h1, h2⟩ := H n' r p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd hp hr hV hII hT h7 j x hx hW
  exact symbol_valuation_margin p Fr deg Y k j x B' _ val (level_degree_nonneg p Fr deg j x) hB' h2 h1 hval

/- English proof (translation)
Establish `hn : (0 : ℤ) < n'` using `by exact_mod_cast NeZero.pos n'`. Establish `h0 : 0 ≤ a % (n' : ℤ)` using `Int.emod_nonneg _ hn.ne'`. Establish `h1 : a % (n' : ℤ) < n'` using `Int.emod_lt_of_pos _ hn`. Unfold `posOf`. Simplify using `only`.

Establish `: (a % (n' : ℤ)).toNat < n'` using `by omega`. Rewrite using `[Nat.mod_eq_of_lt this]`. Use linear arithmetic over natural numbers and integers.
-/
theorem posOf_val_eq_emod (n' : ℕ) [NeZero n'] (a : ℤ) : ((posOf n' a).val : ℤ) = a % (n' : ℤ) := by
  have hn : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
  have h0 : 0 ≤ a % (n' : ℤ) := Int.emod_nonneg _ hn.ne'
  have h1 : a % (n' : ℤ) < n' := Int.emod_lt_of_pos _ hn
  unfold posOf
  simp only
  have : (a % (n' : ℤ)).toNat < n' := by omega
  rw [Nat.mod_eq_of_lt this]
  omega

/- English proof (translation)
Establish `h1 : x % (n' : ℤ) = y % (n' : ℤ)` using `by rw [← posOf_val_eq_emod, ← posOf_val_eq_emod, h]`. Establish `h2 : (n' : ℤ) ∣ x - y` using `Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.1 h1)`. Establish `h3 : |x - y| < (n' : ℤ)` using `abs_lt.2 ⟨by omega, by omega⟩`. Establish `h4` using `Int.eq_zero_of_abs_lt_dvd h2 h3`. Use linear arithmetic over natural numbers and integers.
-/
theorem residue_position_injective_window (n' : ℕ) [NeZero n'] (c x y : ℤ) (hx : c ≤ x ∧ x < c + n') (hy : c ≤ y ∧ y < c + n')
    (h : posOf n' x = posOf n' y) : x = y := by
  have h1 : x % (n' : ℤ) = y % (n' : ℤ) := by rw [← posOf_val_eq_emod, ← posOf_val_eq_emod, h]
  have h2 : (n' : ℤ) ∣ x - y := Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.1 h1)
  have h3 : |x - y| < (n' : ℤ) := abs_lt.2 ⟨by omega, by omega⟩
  have h4 := Int.eq_zero_of_abs_lt_dvd h2 h3
  omega

/- English proof (translation)
Break down `Nat.lt_or_ge i (r - 1) with h | h` into its components or cases. Conclude with `le_of_lt (frame_entries_strictMono Fr L₁ N₁ hV j i (r - 1) h (by omega))`. Establish `: i = r - 1` using `by omega`. Rewrite using `[this]`.
-/
theorem frame_entry_le_last {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (L₁ N₁ : ℕ) (hV : Fr.Valid L₁ N₁) (j : ℤ) (i : ℕ)
    (hi : i < r) : Fr.fr j i ≤ Fr.fr j (r - 1) := by
  rcases Nat.lt_or_ge i (r - 1) with h | h
  · exact le_of_lt (frame_entries_strictMono Fr L₁ N₁ hV j i (r - 1) h (by omega))
  · have : i = r - 1 := by omega
    rw [this]

/- English proof (translation)
Introduce `t`. Proceed by induction on `t with`. Consider the case `zero => simpa using hV.2.2.2.1 j`. Consider the case `succ t ih`. Establish `h1` using `frame_row_monotone Fr L₁ N₁ hV (j + 1 + t) (r - 1) (by omega)`.

Establish `h2` using `hV.2.2.2.1 (j + 1 + t)`. Establish `e : j + 1 + ((t + 1 : ℕ) : ℤ) = j + 1 + t + 1` using `by push_cast; ring`. Rewrite using `[e]`. Use linear arithmetic over natural numbers and integers.
-/
theorem frame_last_lt_next_first {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (L₁ N₁ : ℕ) (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r)
    (j : ℤ) : ∀ t : ℕ, Fr.fr j (r - 1) < Fr.fr (j + 1 + t) 0 := by
  intro t
  induction t with
  | zero => simpa using hV.2.2.2.1 j
  | succ t ih =>
    have h1 := frame_row_monotone Fr L₁ N₁ hV (j + 1 + t) (r - 1) (by omega)
    have h2 := hV.2.2.2.1 (j + 1 + t)
    have e : j + 1 + ((t + 1 : ℕ) : ℤ) = j + 1 + t + 1 := by push_cast; ring
    rw [e]
    omega

/- English proof (translation)
Establish `h1` using `frame_entry_le_last Fr L₁ N₁ hV (j : ℤ) i hi`. Establish `h2` using `frame_last_lt_next_first Fr L₁ N₁ hV hr (j : ℤ) (j' - j - 1)`. Establish `e : (j : ℤ) + 1 + ((j' - j - 1 : ℕ) : ℤ) = (j' : ℤ)` using `by omega`. Rewrite `h2` using `[e]`. Establish `h3` using `frame_row_monotone Fr L₁ N₁ hV (j' : ℤ) i' hi'`.

Use linear arithmetic over natural numbers and integers.
-/
theorem frame_entry_lt_of_lt {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (L₁ N₁ : ℕ) (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r)
    (j j' : ℕ) (h : j < j') (i i' : ℕ) (hi : i < r) (hi' : i' < r) : Fr.fr (j : ℤ) i < Fr.fr (j' : ℤ) i' := by
  have h1 := frame_entry_le_last Fr L₁ N₁ hV (j : ℤ) i hi
  have h2 := frame_last_lt_next_first Fr L₁ N₁ hV hr (j : ℤ) (j' - j - 1)
  have e : (j : ℤ) + 1 + ((j' - j - 1 : ℕ) : ℤ) = (j' : ℤ) := by omega
  rw [e] at h2
  have h3 := frame_row_monotone Fr L₁ N₁ hV (j' : ℤ) i' hi'
  omega

/- English proof (translation)
Establish `hwin : ∀ j i : ℕ, j < Fr.J → i < r → Fr.fr 0 0 ≤ Fr.fr (j : ℤ) i ∧ Fr.fr (j : ℤ) i < Fr.fr 0 0 + n'`. Introduce `j i hj hi`. Prove the components needed by the constructor for the conclusion. Break down `Nat.eq_zero_or_pos j with h | h` into its components or cases. Substitute `h` using the available equality.

Simplify using `using frame_row_monotone Fr L₁ N₁ hV 0 i hi`. Establish `h1` using `frame_entry_lt_of_lt Fr L₁ N₁ hV hr 0 j h 0 i (by omega) hi`. Simplify using `only [Nat.cast_zero] at h1`. Conclude with `le_of_lt h1`. Establish `h1` using `frame_entry_lt_of_lt Fr L₁ N₁ hV hr j Fr.J hj i 0 hi (by omega)`.

Establish `h2` using `hV.2.1 0 0`. Rewrite `h2` using `[zero_add]`. Use linear arithmetic over natural numbers and integers. Establish `hcard : ((Finset.range Fr.J) ×ˢ (Finset.range r)).card ≤ Fr.TT.card`. Apply `Finset.card_le_card_of_injOn (fun q : ℕ × ℕ => posOf n' (Fr.fr (q.1 : ℤ) q.2))` to reduce the goal to its premises.

Introduce `q hq`. Establish `hq'` using `Finset.mem_product.1 hq`. Conclude with `(hV.2.2.2.2.1 _ _ (Finset.mem_range.1 hq'.2)).1`. Introduce and unpack `⟨j, i⟩ hq ⟨j', i'⟩ hq' he`. Establish `a1` using `Finset.mem_product.1 hq`.

Establish `a2` using `Finset.mem_product.1 hq'`. Establish `hj : j < Fr.J` using `Finset.mem_range.1 a1.1`. Establish `hi : i < r` using `Finset.mem_range.1 a1.2`. Establish `hj' : j' < Fr.J` using `Finset.mem_range.1 a2.1`. Establish `hi' : i' < r` using `Finset.mem_range.1 a2.2`.

Establish `he' : posOf n' (Fr.fr (j : ℤ) i) = posOf n' (Fr.fr (j' : ℤ) i')` using `he`. Establish `hxy` using `residue_position_injective_window n' (Fr.fr 0 0) _ _ (hwin j i hj hi) (hwin j' i' hj' hi') he'`. Break down `Nat.lt_trichotomy j j' with h | h | h` into its components or cases. Use `frame_entry_lt_of_lt Fr L₁ N₁ hV hr j j' h i i' hi hi'` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Substitute `h` using the available equality. Break down `Nat.lt_trichotomy i i' with g | g | g` into its components or cases. Use `frame_entries_strictMono Fr L₁ N₁ hV (j : ℤ) i i' g hi'` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Substitute `g` using the available equality.

Both sides reduce to the same expression. Use `frame_entries_strictMono Fr L₁ N₁ hV (j : ℤ) i' i g hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `frame_entry_lt_of_lt Fr L₁ N₁ hV hr j' j h i' i hi' hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite `hcard` using `[Finset.card_product, Finset.card_range, Finset.card_range]`. Then use the resulting hypothesis.
-/
theorem frame_count_mul_le_tops {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (L₁ N₁ : ℕ) (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) :
    Fr.J * r ≤ Fr.TT.card := by
  have hwin : ∀ j i : ℕ, j < Fr.J → i < r →
      Fr.fr 0 0 ≤ Fr.fr (j : ℤ) i ∧ Fr.fr (j : ℤ) i < Fr.fr 0 0 + n' := by
    intro j i hj hi
    constructor
    · rcases Nat.eq_zero_or_pos j with h | h
      · subst h
        simpa using frame_row_monotone Fr L₁ N₁ hV 0 i hi
      · have h1 := frame_entry_lt_of_lt Fr L₁ N₁ hV hr 0 j h 0 i (by omega) hi
        simp only [Nat.cast_zero] at h1
        exact le_of_lt h1
    · have h1 := frame_entry_lt_of_lt Fr L₁ N₁ hV hr j Fr.J hj i 0 hi (by omega)
      have h2 := hV.2.1 0 0
      rw [zero_add] at h2
      omega
  have hcard : ((Finset.range Fr.J) ×ˢ (Finset.range r)).card ≤ Fr.TT.card := by
    apply Finset.card_le_card_of_injOn (fun q : ℕ × ℕ => posOf n' (Fr.fr (q.1 : ℤ) q.2))
    · intro q hq
      have hq' := Finset.mem_product.1 hq
      exact (hV.2.2.2.2.1 _ _ (Finset.mem_range.1 hq'.2)).1
    · rintro ⟨j, i⟩ hq ⟨j', i'⟩ hq' he
      have a1 := Finset.mem_product.1 hq
      have a2 := Finset.mem_product.1 hq'
      have hj : j < Fr.J := Finset.mem_range.1 a1.1
      have hi : i < r := Finset.mem_range.1 a1.2
      have hj' : j' < Fr.J := Finset.mem_range.1 a2.1
      have hi' : i' < r := Finset.mem_range.1 a2.2
      have he' : posOf n' (Fr.fr (j : ℤ) i) = posOf n' (Fr.fr (j' : ℤ) i') := he
      have hxy := residue_position_injective_window n' (Fr.fr 0 0) _ _ (hwin j i hj hi) (hwin j' i' hj' hi') he'
      rcases Nat.lt_trichotomy j j' with h | h | h
      · have := frame_entry_lt_of_lt Fr L₁ N₁ hV hr j j' h i i' hi hi'
        omega
      · subst h
        rcases Nat.lt_trichotomy i i' with g | g | g
        · have := frame_entries_strictMono Fr L₁ N₁ hV (j : ℤ) i i' g hi'
          omega
        · subst g; rfl
        · have := frame_entries_strictMono Fr L₁ N₁ hV (j : ℤ) i' i g hi
          omega
      · have := frame_entry_lt_of_lt Fr L₁ N₁ hV hr j' j h i' i hi' hi
        omega
  rwa [Finset.card_product, Finset.card_range, Finset.card_range] at hcard

/- English proof (translation)
Take `⟨C, hC, H⟩` from `segment_length_bounds_real`. Use `⟨C, hC, ?_⟩` and prove the remaining obligations. Introduce `n' r _ p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd hp hr hV hII hT j x hx hW`. Take `⟨h1, h2⟩` from `H n' r p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd hp hr hV hII hT (frame_count_mul_le_tops Fr L₁ N₁ hV (by omega)) j x hx hW`. Use `⟨⟨h1, h2⟩, fun B' val hB' hval => ?_⟩` and prove the remaining obligations.

Conclude with `symbol_valuation_margin p Fr deg Y k j x B' _ val (level_degree_nonneg p Fr deg j x) hB' h2 h1 hval`.
-/
theorem numeric_symbol_bound_real : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (n' r : ℕ) [NeZero n'] (p : ℕ) (Fr : Frames n' r) (k L₁ N₁ G' : ℕ) (deg : Fin n' → ℕ) (a : ℕ) (Y : ℝ)
      (c0 c'' cStar : ℕ) (Dd : ℝ), 13 ≤ p → 2 ≤ r → Fr.Valid L₁ N₁ →
      Formalism.MainNotions.SourceCleaning.HypII C (C + 1) C p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd → TwistBound p Fr (p ^ G') →
      ∀ j x : ℤ, x ∈ Fr.letters j → ¬ Fr.IsW j x →
        ((mStar p Fr k N₁ (p ^ G') (cPrime n' r Fr.TT.card c0 c'' cStar) : ℝ) ≤ (sl p Fr deg Y k j x : ℝ) ∧
          (sl p Fr deg Y k j x : ℝ) ≤ Bo p Fr deg j x / 100) ∧
        ∀ B' val : ℝ, B' ≤ Bo p Fr deg j x / 80 → Bo p Fr deg j x / 2 - sl p Fr deg Y k j x ≤ val →
          Bo p Fr deg j x / 4 + (mStar p Fr k N₁ (p ^ G') (cPrime n' r Fr.TT.card c0 c'' cStar) : ℝ) ≤ val - B' ∧
            (mStar p Fr k N₁ (p ^ G') (cPrime n' r Fr.TT.card c0 c'' cStar) : ℝ) ≤ Bo p Fr deg j x / 4 := by
  obtain ⟨C, hC, H⟩ := segment_length_bounds_real
  refine ⟨C, hC, ?_⟩
  intro n' r _ p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd hp hr hV hII hT j x hx hW
  obtain ⟨h1, h2⟩ := H n' r p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd hp hr hV hII hT
    (frame_count_mul_le_tops Fr L₁ N₁ hV (by omega)) j x hx hW
  refine ⟨⟨h1, h2⟩, fun B' val hB' hval => ?_⟩
  exact symbol_valuation_margin p Fr deg Y k j x B' _ val (level_degree_nonneg p Fr deg j x) hB' h2 h1 hval

end Formalism.MainNotions.G.WittFrameLocaliserOrders

end

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.G.WittFrameLocaliserOrders

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning

section BaseChange

variable (R0 : Type) [CommRing R0] [IsDomain R0] (n : ℕ)

local notation "K0" => FractionRing R0

def polyRingMap : MvPolynomial (Fin n × Fin n) R0 →+* MvPolynomial (Fin n × Fin n) K0 :=
  MvPolynomial.map (algebraMap R0 K0)

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[genMat, polyRingMap]`.
-/
theorem polyRingMap_genericMatrix : (genMat R0 n).map (polyRingMap R0 n) = genMat K0 n := by
  ext a b
  simp [genMat, polyRingMap]

/- English proof (translation)
Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, polyRingMap_genericMatrix]`.
-/
theorem coordinate_embedding_generic_det : polyRingMap R0 n (genMat R0 n).det = (genMat K0 n).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, polyRingMap_genericMatrix]

/- English proof (translation)
Rewrite using `[RingHom.comp_apply, coordinate_embedding_generic_det]`. Conclude with `IsLocalization.Away.algebraMap_isUnit _`.
-/
theorem isUnit_generic_det_image : IsUnit (((algebraMap (MvPolynomial (Fin n × Fin n) K0) (GLCoord K0 n)).comp (polyRingMap R0 n))
    (genMat R0 n).det) := by
  rw [RingHom.comp_apply, coordinate_embedding_generic_det]
  exact IsLocalization.Away.algebraMap_isUnit _

def glCoordRingMap : GLCoord R0 n →+* GLCoord K0 n :=
  IsLocalization.Away.lift (genMat R0 n).det (isUnit_generic_det_image R0 n)

/- English proof (translation)
The claim follows from `IsLocalization.Away.lift_eq _ (isUnit_generic_det_image R0 n) a`.
-/
theorem glCoordMap_algebraMap_eq (a : MvPolynomial (Fin n × Fin n) R0) :
    glCoordRingMap R0 n (algebraMap _ (GLCoord R0 n) a) = algebraMap _ (GLCoord K0 n) (polyRingMap R0 n a) :=
  IsLocalization.Away.lift_eq _ (isUnit_generic_det_image R0 n) a

/- English proof (translation)
Establish `h1 : algebraMap _ (GLCoord R0 n) (genMat R0 n).det * IsLocalization.Away.invSelf (genMat R0 n).det = 1` using `IsLocalization.Away.mul_invSelf _`. Establish `h2 : algebraMap _ (GLCoord K0 n) (genMat K0 n).det * IsLocalization.Away.invSelf (genMat K0 n).det = 1` using `IsLocalization.Away.mul_invSelf _`. Establish `h3` using `congrArg (glCoordRingMap R0 n) h1`. Rewrite `h3` using `[map_mul, map_one, glCoordMap_algebraMap_eq, coordinate_embedding_generic_det]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[h2, mul_one]`. Use `_ = (algebraMap _ (GLCoord K0 n) (genMat K0 n).det * glCoordRingMap R0 n (IsLocalization.Away.invSelf (genMat R0 n).det)) * IsLocalization.Away.invSelf (genMat K0 n).det := by ring`. Use `_ = _ := by rw [h3, one_mul]`.
-/
theorem glCoordMap_inv_det : glCoordRingMap R0 n (IsLocalization.Away.invSelf (genMat R0 n).det) =
    IsLocalization.Away.invSelf (genMat K0 n).det := by
  have h1 : algebraMap _ (GLCoord R0 n) (genMat R0 n).det * IsLocalization.Away.invSelf (genMat R0 n).det = 1 :=
    IsLocalization.Away.mul_invSelf _
  have h2 : algebraMap _ (GLCoord K0 n) (genMat K0 n).det * IsLocalization.Away.invSelf (genMat K0 n).det = 1 :=
    IsLocalization.Away.mul_invSelf _
  have h3 := congrArg (glCoordRingMap R0 n) h1
  rw [map_mul, map_one, glCoordMap_algebraMap_eq, coordinate_embedding_generic_det] at h3
  calc glCoordRingMap R0 n (IsLocalization.Away.invSelf (genMat R0 n).det)
      = glCoordRingMap R0 n (IsLocalization.Away.invSelf (genMat R0 n).det) *
          (algebraMap _ (GLCoord K0 n) (genMat K0 n).det * IsLocalization.Away.invSelf (genMat K0 n).det) := by
        rw [h2, mul_one]
    _ = (algebraMap _ (GLCoord K0 n) (genMat K0 n).det *
          glCoordRingMap R0 n (IsLocalization.Away.invSelf (genMat R0 n).det)) *
          IsLocalization.Away.invSelf (genMat K0 n).det := by ring
    _ = _ := by rw [h3, one_mul]

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨a, s, rfl⟩` from `IsLocalization.exists_mk'_eq (Submonoid.powers (genMat R0 n).det) x`. Establish `h1` using `IsLocalization.mk'_spec (GLCoord R0 n) a s`. Establish `h2` using `congrArg (glCoordRingMap R0 n) h1`.

Rewrite `h2` using `[map_mul, hx, zero_mul, glCoordMap_algebraMap_eq]`. Establish `hdet : (genMat K0 n).det ≠ 0` using `Matrix.det_mvPolynomialX_ne_zero (Fin n) K0`. Establish `hinj : Function.Injective (algebraMap (MvPolynomial (Fin n × Fin n) K0) (GLCoord K0 n))` using `IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hdet)`. Establish `h3 : polyRingMap R0 n a = 0` using `hinj (by rw [← h2, map_zero])`. Establish `h4 : a = 0` using `MvPolynomial.map_injective _ (IsFractionRing.injective R0 K0) (by rw [map_zero]; exact h3)`.

Rewrite using `[h4, IsLocalization.mk'_zero]`.
-/
theorem laurent_coordinate_embedding_injective : Function.Injective (glCoordRingMap R0 n) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers (genMat R0 n).det) x
  have h1 := IsLocalization.mk'_spec (GLCoord R0 n) a s
  have h2 := congrArg (glCoordRingMap R0 n) h1
  rw [map_mul, hx, zero_mul, glCoordMap_algebraMap_eq] at h2
  have hdet : (genMat K0 n).det ≠ 0 := Matrix.det_mvPolynomialX_ne_zero (Fin n) K0
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin n × Fin n) K0) (GLCoord K0 n)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hdet)
  have h3 : polyRingMap R0 n a = 0 := hinj (by rw [← h2, map_zero])
  have h4 : a = 0 := MvPolynomial.map_injective _ (IsFractionRing.injective R0 K0) (by rw [map_zero]; exact h3)
  rw [h4, IsLocalization.mk'_zero]

def laurentRingMap : GLLaurent R0 n →+* GLLaurent K0 n := AddMonoidAlgebra.mapRingHom ℤ (glCoordRingMap R0 n)

/- English proof (translation)
Rewrite using `[← LaurentPolynomial.single_eq_C, ← LaurentPolynomial.single_eq_C]`. Conclude with `AddMonoidAlgebra.mapRingHom_single _ _ _`.
-/
theorem laurentCoordinateMap_C (x : GLCoord R0 n) : laurentRingMap R0 n (LaurentPolynomial.C x) = LaurentPolynomial.C (glCoordRingMap R0 n x) := by
  rw [← LaurentPolynomial.single_eq_C, ← LaurentPolynomial.single_eq_C]
  exact AddMonoidAlgebra.mapRingHom_single _ _ _

/- English proof (translation)
Unfold `LaurentPolynomial.T laurentRingMap`. Rewrite using `[AddMonoidAlgebra.mapRingHom_single, map_one]`.
-/
theorem laurentRingMap_alt (k : ℤ) : laurentRingMap R0 n (LaurentPolynomial.T k) = LaurentPolynomial.T k := by
  unfold LaurentPolynomial.T laurentRingMap
  rw [AddMonoidAlgebra.mapRingHom_single, map_one]

/- English proof (translation)
Use extensionality with `z`. Rewrite using `[Finsupp.mem_support_iff, Finsupp.mem_support_iff]`. Unfold `laurentRingMap`. Rewrite using `[AddMonoidAlgebra.coeff_mapRingHom]`. Conclude with `map_ne_zero_iff _ (laurent_coordinate_embedding_injective R0 n)`.
-/
theorem laurentCoordinateMap_support (x : GLLaurent R0 n) : (laurentRingMap R0 n x).coeff.support = x.coeff.support := by
  ext z
  rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff]
  unfold laurentRingMap
  rw [AddMonoidAlgebra.coeff_mapRingHom]
  exact map_ne_zero_iff _ (laurent_coordinate_embedding_injective R0 n)

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `h` using `laurentCoordinateMap_support R0 n x`. Rewrite `h` using `[hx]`. Establish `h2 : x.coeff.support = ∅` using `by rw [← h]; simp`.

Establish `h3 : x.coeff = 0` using `Finsupp.support_eq_empty.1 h2`. Use extensionality with `z`. Rewrite using `[h3]`. Simplify using the standard rewrite rules.
-/
theorem laurentRingMap_injective : Function.Injective (laurentRingMap R0 n) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h := laurentCoordinateMap_support R0 n x
  rw [hx] at h
  have h2 : x.coeff.support = ∅ := by rw [← h]; simp
  have h3 : x.coeff = 0 := Finsupp.support_eq_empty.1 h2
  ext z
  rw [h3]; simp

/- English proof (translation)
Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Establish `he : polyRingMap R0 n (genMat R0 n a b) = genMat K0 n a b` using `by simp [genMat, polyRingMap]`. Simplify using `only [gL, Matrix.map_apply, laurentCoordinateMap_C, glCoordMap_algebraMap_eq, he]`.
-/
theorem laurentRingMap_genericMatrix : (gL R0 n).map (laurentRingMap R0 n) = gL K0 n := by
  refine Matrix.ext fun a b => ?_
  have he : polyRingMap R0 n (genMat R0 n a b) = genMat K0 n a b := by simp [genMat, polyRingMap]
  simp only [gL, Matrix.map_apply, laurentCoordinateMap_C, glCoordMap_algebraMap_eq, he]

/- English proof (translation)
Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Establish `he : polyRingMap R0 n ((genMat R0 n).adjugate a b) = (genMat K0 n).adjugate a b`. Establish `h` using `RingHom.map_adjugate (polyRingMap R0 n) (genMat R0 n)`. Rewrite `h` using `[RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, polyRingMap_genericMatrix]`. Conclude with `congrFun (congrFun h a) b`.

Simplify using `only [gLinv, Matrix.map_apply, laurentCoordinateMap_C, map_mul, glCoordMap_algebraMap_eq, glCoordMap_inv_det, he]`.
-/
theorem laurentRingMap_inverse_matrix : (gLinv R0 n).map (laurentRingMap R0 n) = gLinv K0 n := by
  refine Matrix.ext fun a b => ?_
  have he : polyRingMap R0 n ((genMat R0 n).adjugate a b) = (genMat K0 n).adjugate a b := by
    have h := RingHom.map_adjugate (polyRingMap R0 n) (genMat R0 n)
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, polyRingMap_genericMatrix] at h
    exact congrFun (congrFun h a) b
  simp only [gLinv, Matrix.map_apply, laurentCoordinateMap_C, map_mul, glCoordMap_algebraMap_eq, glCoordMap_inv_det, he]

/- English proof (translation)
Unfold `twistMat`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, laurentRingMap_genericMatrix, laurentRingMap_inverse_matrix, Matrix.diagonal_map (map_zero _)]`. Use `congr 3`. Use function extensionality and compare the values at `a`. Use `split_ifs`.

Conclude with `laurentRingMap_alt R0 n k`. Conclude with `map_one _`.
-/
theorem laurentCoordinateMap_twist (j : Fin n) (k : ℤ) : (twistMat R0 n j k).map (laurentRingMap R0 n) = twistMat K0 n j k := by
  unfold twistMat
  rw [Matrix.map_mul, Matrix.map_mul, laurentRingMap_genericMatrix, laurentRingMap_inverse_matrix, Matrix.diagonal_map (map_zero _)]
  congr 3
  funext a
  split_ifs
  · exact laurentRingMap_alt R0 n k
  · exact map_one _

/- English proof (translation)
Simplify using `only [coefL, RingHom.comp_apply, laurentCoordinateMap_C, glCoordMap_algebraMap_eq, polyRingMap, MvPolynomial.map_C]`.
-/
theorem laurentRingMap_coeff (x : R0) : laurentRingMap R0 n (coefL R0 n x) = coefL K0 n (algebraMap R0 K0 x) := by
  simp only [coefL, RingHom.comp_apply, laurentCoordinateMap_C, glCoordMap_algebraMap_eq, polyRingMap, MvPolynomial.map_C]

/- English proof (translation)
Establish `h : (twistSub (R` using `K0) LL S j).comp (MvPolynomial.map (algebraMap R0 K0)) = (MvPolynomial.map (laurentRingMap R0 n)).comp (twistSub (R := R0) LL S j) := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `x`. Simplify using `only [RingHom.comp_apply, MvPolynomial.map_C, twistSub, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, laurentRingMap_coeff]`. Introduce `v`.

Establish `ht : ∀ (k : ℤ) (a b : Fin n), laurentRingMap R0 n (twistMat R0 n j k a b) = twistMat K0 n j k a b` using `fun k a b => by`. Rewrite using `[← laurentCoordinateMap_twist R0 n j k]`. Both sides reduce to the same expression. Simplify using `only [RingHom.comp_apply, MvPolynomial.map_X, twistSub, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]`. Apply the tactic sequence `split_ifs <;> simp [ht]`.

Conclude with `RingHom.congr_fun h G`.
-/
theorem twist_substitution_natural {ι : Type} (LL : Letters ι) (S : Set ι) (j : Fin n) (G : MvPolynomial (ι × Fin n) R0) :
    twistSub LL S j (MvPolynomial.map (algebraMap R0 K0) G) =
      MvPolynomial.map (laurentRingMap R0 n) (twistSub LL S j G) := by
  have h : (twistSub (R := K0) LL S j).comp (MvPolynomial.map (algebraMap R0 K0)) =
      (MvPolynomial.map (laurentRingMap R0 n)).comp (twistSub (R := R0) LL S j) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp only [RingHom.comp_apply, MvPolynomial.map_C, twistSub, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C,
        laurentRingMap_coeff]
    · intro v
      have ht : ∀ (k : ℤ) (a b : Fin n), laurentRingMap R0 n (twistMat R0 n j k a b) = twistMat K0 n j k a b := fun k a b => by
        rw [← laurentCoordinateMap_twist R0 n j k]; rfl
      simp only [RingHom.comp_apply, MvPolynomial.map_X, twistSub, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
      split_ifs <;> simp [ht]
  exact RingHom.congr_fun h G

end BaseChange

/- English proof (translation)
Introduce `R0 _ _ ι _ LL n _ S G`. Unfold `valS sDegs`. Rewrite using `[twist_substitution_natural, MvPolynomial.support_map_of_injective _ (laurentRingMap_injective R0 n)]`. Use `congr 1`. Use `Finset.biUnion_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[MvPolynomial.coeff_map, laurentCoordinateMap_support]`.
-/
theorem valuation_fraction_field_extension : IntegralToFieldBaseChange := by
  intro R0 _ _ ι _ LL n _ S G
  unfold valS sDegs
  rw [twist_substitution_natural, MvPolynomial.support_map_of_injective _ (laurentRingMap_injective R0 n)]
  congr 1
  refine Finset.biUnion_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map, laurentCoordinateMap_support]

end Formalism.MainNotions.G.WittFrameLocaliserOrders

end

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.G.WittFrameLocaliserOrders

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning

/- English proof (translation)
Take `⟨m, hm⟩` from `MvPolynomial.support_nonempty.2 hP`. Establish `h1` using `((MvPolynomial.mem_restrictSupport_iff R).1 h) (Finset.mem_coe.2 hm)`. Establish `h2` using `((MvPolynomial.mem_restrictSupport_iff R).1 h') (Finset.mem_coe.2 hm)`. Use function extensionality and compare the values at `i`. Rewrite using `[← h1 i, ← h2 i]`.
-/
theorem multideg_unique {R : Type*} [CommRing R] {n' k : ℕ} {P : MvPolynomial (TV n' k) R} (hP : P ≠ 0)
    {d d' : Fin n' → ℕ} (h : HasMultideg P d) (h' : HasMultideg P d') : d' = d := by
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.2 hP
  have h1 := ((MvPolynomial.mem_restrictSupport_iff R).1 h) (Finset.mem_coe.2 hm)
  have h2 := ((MvPolynomial.mem_restrictSupport_iff R).1 h') (Finset.mem_coe.2 hm)
  funext i
  rw [← h1 i, ← h2 i]

def SymbolRealisabilityRemaining (_D : Formalism.BasicNotions.D7) (CLa CD Csz : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [Fact p.Prime] [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra (WF p n') O] (S : UniformizedDVR p O), OHyp p n' O S →
    ∀ hH : CommonHypotheses p n' r (r + K),
  ∀ (Fr : Frames n' r) (L₁ N₁ G' : ℕ), Fr.Valid L₁ N₁ → TwistBound p Fr (p ^ G') →
  ∀ (deg : Fin n' → ℕ) (a : ℕ) (Y : ℝ) (c0 c'' cStar : ℕ) (Dd : ℝ),
    HypII CLa CD Csz p Fr (r + K) L₁ N₁ G' deg a Y c0 c'' cStar Dd →
  let c' := cPrime n' r Fr.TT.card c0 c'' cStar
  ∀ g : Matrix (Fin (r + K)) (Fin (r + K)) (WF p n'), IsGLW g →
  ∀ (n : ℕ) (obd : ℤ → ℤ → ℝ) (xi : Fin n → ℤ → SegRing O r K) (dd : ℤ → ℤ → ℕ),
    (∀ (i : Fin n) (j : ℕ), j < Fr.J →
      xi i j ∈ XX' O r K Fr j (fun _ => (mStar p Fr (r + K) N₁ (p ^ G') c' : ℤ))
        (fun x => Bo p Fr deg j x / 2 - sl p Fr deg Y (r + K) j x) (obd j) ∧
      xi i j ∈ restrictSupport O {mm | ∀ x ∈ Fr.letters j, ∑ c : Fin (r + K), mm (x, c) = dd j x}) →
    (∀ j : ℕ, j < Fr.J → ∀ x ∈ Fr.letters j, (Fr.IsW j x ∨ x ∈ Fr.LLset j) →
        |(dd j x : ℝ) - levDeg p Fr deg j x| ≤ levDeg p Fr deg j x / 100) →
  ∀ (mon : Fin n' × Fin (r + K) →₀ ℕ), IsLabel p Fr mon → (∀ v ∈ mon.support, v.1 ∈ Fr.TT) →
  ∀ o : ℕ, (∀ m ∈ (monPh O K p Fr mon xi).support, normDeg r m = o) →
    ∃ (d : Fin n' → ℕ) (m : ℕ) (τ : Fin m → Term n' (r + K) O),
      (∀ i, (τ i).Valid p n' S.w n' r (p ^ G') g ∧ (τ i).InTops Fr ∧ o ≤ (τ i).level ∧
        HasMultideg ((τ i).sym p n' S.w Fr hH.2.2.1 g c' ((2 * p ^ G' + 3) * c') c') d ∧
        HasMultideg ((τ i).raw p n' S.w Fr hH.2.2.1 g c' ((2 * p ^ G' + 3) * c') c') d) ∧
      HasMultideg (MvPolynomial.map (algebraMap O (KK O)) (monPh O K p Fr mon xi)) d ∧
      InWj S.w (C (algebraMap O (KK O) (S.w ^ o)) * MvPolynomial.map (algebraMap O (KK O)) (monPh O K p Fr mon xi) -
        ∑ i, (τ i).sym p n' S.w Fr hH.2.2.1 g c' ((2 * p ^ G' + 3) * c') c') (o + c')

/- English proof (translation)
Introduce `p n' r K _ _ _ _ O _ _ _ _ S hO hH Fr L₁ N₁ G' hV hT deg a Y c0 c'' cStar Dd hII c' g hg n obd xi dd hxi hdd mon hmon hmonT o ho`. Take `⟨d, m, τ, hτ, hd, hcl⟩` from `h p n' r K O S hO hH Fr L₁ N₁ G' hV hT deg a Y c0 c'' cStar Dd hII g hg n obd xi dd hxi hdd mon hmon hmonT o ho`. Take `⟨F, hFA, hFT, hFd, hFw, hFo⟩` from `h4 p n' r (r + K) O S hO hH Fr L₁ N₁ hV (p ^ G') hT g hg c' o d m τ hτ`. Distinguish the cases in `h0 : MvPolynomial.map (algebraMap O (KK O)) (monPh O K p Fr mon xi) = 0`. Use `⟨0, (inA_iff_inWj0 (w := S.w) _).2 (inWj_zero 0), fun d' _ => Submodule.zero_mem _, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[h0, map_zero, mul_zero, sub_zero]`. Conclude with `inWj_zero _`. Introduce `g' _ _ show InWj S.w (subst p n' O S.w n' r g' 0) (o + c')`. Rewrite using `[map_zero]`. Conclude with `inWj_zero _`.

Use `⟨F, hFA, fun d' hd' => ?_, ?_, hFo⟩` and prove the remaining obligations. Rewrite using `[multideg_unique h0 hd hd']`. Conclude with `hFd`. Use `inWj_sub hFw hcl` as an intermediate fact. Establish `he : subst p n' O S.w n' r g F - C (algebraMap O (KK O) (S.w ^ o)) * MvPolynomial.map (algebraMap O (KK O)) (monPh O K p Fr mon xi) = (subst p n' O S.w n' r g F - ∑ i, (τ i).sym p n' S.w Fr hH.2.2.1 g c' ((2 * p ^ G' + 3) * c') c') - (C (algebraMap O (KK O) (S.w ^ o)) * MvPolynom …` using `by ring`.

Rewrite using `[he]`. Conclude with `this`.
-/
theorem real_bound_of_term_symbols (D : Formalism.BasicNotions.D7) (CLa CD Csz : ℝ) (h4 : Conclusion4 D) (h : SymbolRealisabilityRemaining D CLa CD Csz) :
    Conclusion6 D CLa CD Csz := by
  intro p n' r K _ _ _ _ O _ _ _ _ S hO hH Fr L₁ N₁ G' hV hT deg a Y c0 c'' cStar Dd hII c' g hg n obd xi dd hxi hdd
    mon hmon hmonT o ho
  obtain ⟨d, m, τ, hτ, hd, hcl⟩ := h p n' r K O S hO hH Fr L₁ N₁ G' hV hT deg a Y c0 c'' cStar Dd hII g hg n obd xi dd
    hxi hdd mon hmon hmonT o ho
  obtain ⟨F, hFA, hFT, hFd, hFw, hFo⟩ := h4 p n' r (r + K) O S hO hH Fr L₁ N₁ hV (p ^ G') hT g hg c' o d m τ hτ
  by_cases h0 : MvPolynomial.map (algebraMap O (KK O)) (monPh O K p Fr mon xi) = 0
  · refine ⟨0, (inA_iff_inWj0 (w := S.w) _).2 (inWj_zero 0), fun d' _ => Submodule.zero_mem _, ?_, ?_⟩
    · rw [h0, map_zero, mul_zero, sub_zero]; exact inWj_zero _
    · intro g' _ _
      show InWj S.w (subst p n' O S.w n' r g' 0) (o + c')
      rw [map_zero]; exact inWj_zero _
  · refine ⟨F, hFA, fun d' hd' => ?_, ?_, hFo⟩
    · rw [multideg_unique h0 hd hd']; exact hFd
    · have := inWj_sub hFw hcl
      have he : subst p n' O S.w n' r g F -
          C (algebraMap O (KK O) (S.w ^ o)) * MvPolynomial.map (algebraMap O (KK O)) (monPh O K p Fr mon xi) =
          (subst p n' O S.w n' r g F - ∑ i, (τ i).sym p n' S.w Fr hH.2.2.1 g c' ((2 * p ^ G' + 3) * c') c') -
          (C (algebraMap O (KK O) (S.w ^ o)) * MvPolynomial.map (algebraMap O (KK O)) (monPh O K p Fr mon xi) -
            ∑ i, (τ i).sym p n' S.w Fr hH.2.2.1 g c' ((2 * p ^ G' + 3) * c') c') := by ring
      rw [he]; exact this

end Formalism.MainNotions.G.WittFrameLocaliserOrders

end

noncomputable section

namespace Formalism.MainNotions.G.WittFrameLocaliserOrders

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning

/- English proof (translation)
The claim follows from `localiser_vanishing_off_plane D`.
-/
theorem theta_kernel_expansion (D : Formalism.BasicNotions.D7) : Conclusion1 D := localiser_vanishing_off_plane D

/- English proof (translation)
The claim follows from `localiser_expansion_lemma D`.
-/
theorem splitting_package_holds (D : Formalism.BasicNotions.D7) : Conclusion2 D := localiser_expansion_lemma D

/- English proof (translation)
The claim follows from `keys_vanish_modulo_uniformiser D`.
-/
theorem segment_statement_holds (D : Formalism.BasicNotions.D7) : PointsLemma D := keys_vanish_modulo_uniformiser D

/- English proof (translation)
The claim follows from `order_lemma_of_plane_coordinates D (localiser_vanishing_off_plane D) (bs_restRawTops D) (bc_claim' D)`.
-/
theorem order_lemma_holds (D : Formalism.BasicNotions.D7) : Conclusion4 D :=
  order_lemma_of_plane_coordinates D (localiser_vanishing_off_plane D) (bs_restRawTops D) (bc_claim' D)

/- English proof (translation)
The claim follows from `divisibility_of_homogeneous_field_lemma D h valuation_fraction_field_extension`.
-/
theorem divisibility_of_field_lemma (D : Formalism.BasicNotions.D7) (h : LargePrimeLengthVanishing D) : Conclusion5 D := divisibility_of_homogeneous_field_lemma D h valuation_fraction_field_extension

/- English proof (translation)
The claim follows from `real_bound_of_term_symbols D CLa CD Csz (order_lemma_holds D) hS`.
-/
theorem real_bound_reduced_to_symbols (D : Formalism.BasicNotions.D7) (CLa CD Csz : ℝ) (hS : SymbolRealisabilityRemaining D CLa CD Csz) : Conclusion6 D CLa CD Csz :=
  real_bound_of_term_symbols D CLa CD Csz (order_lemma_holds D) hS

/- English proof (translation)
The claim follows from `good_orbits_lemma D`.
-/
theorem orbit_lemma_holds (D : Formalism.BasicNotions.D7) : GoodOrbitPositions D := good_orbits_lemma D

/- English proof (translation)
The claim follows from `criterion_of_mod_w_clause D h`.
-/
theorem criterion_of_modulo_uniformiser (D : Formalism.BasicNotions.D7) (h : bd_RestCritModW D) : SpaceCriterionModuloUniformiser D := criterion_of_mod_w_clause D h

/- English proof (translation)
Introduce `hA`. Take `⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hE, _⟩` from `hA`. Conclude with `⟨theta_kernel_expansion D, splitting_package_holds D, segment_statement_holds D, order_lemma_holds D, divisibility_of_field_lemma D hE, real_bound_reduced_to_symbols D CLa' CD Csz hS⟩`.
-/
theorem stmt_of_rest (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz : ℝ)
    (hS : SymbolRealisabilityRemaining D CLa' CD Csz) : Stmt D CLa Ck Crk Cdeg CLa' CD Csz := by
  intro hA
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hE, _⟩ := hA
  exact ⟨theta_kernel_expansion D, splitting_package_holds D, segment_statement_holds D, order_lemma_holds D, divisibility_of_field_lemma D hE,
    real_bound_reduced_to_symbols D CLa' CD Csz hS⟩

/- English proof (translation)
Introduce `CLa Ck Crk Cdeg hA`. Take `⟨CLa', CD, Csz, h1, h2, h3, hS'⟩` from `hS`. Conclude with `⟨CLa', CD, Csz, h1, h2, h3, stmt_of_rest D CLa Ck Crk Cdeg CLa' CD Csz hS' hA⟩`.
-/
theorem stmtE_of_rest (D : Formalism.BasicNotions.D7)
    (hS : ∃ CLa' CD Csz : ℝ, 0 < CLa' ∧ 0 < CD ∧ 0 < Csz ∧ SymbolRealisabilityRemaining D CLa' CD Csz) : ClosedFormOfAdmitted D := by
  intro CLa Ck Crk Cdeg hA
  obtain ⟨CLa', CD, Csz, h1, h2, h3, hS'⟩ := hS
  exact ⟨CLa', CD, Csz, h1, h2, h3, stmt_of_rest D CLa Ck Crk Cdeg CLa' CD Csz hS' hA⟩

end Formalism.MainNotions.G.WittFrameLocaliserOrders
