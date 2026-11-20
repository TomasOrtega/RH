import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK
open Polynomial

/- English proof (translation)
Proceed by induction on `g using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Rewrite using `[map_add, add_sub_add_comm]`. Conclude with `dvd_add hp hq`. Consider the case `monomial n a`.

Rewrite using `[expand_monomial, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial, ← mul_sub]`. Apply `dvd_mul_of_dvd_right` to reduce the goal to its premises. Establish `h1 : (X : ℤ[X]) ^ (n * (1 + w)) - X ^ n = X ^ n * ((X ^ w) ^ n - 1 ^ n)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1]`.

Conclude with `dvd_mul_of_dvd_right (sub_dvd_pow_sub_pow _ _ _) _`.
-/
private theorem exp_cong (w : ℕ) (g : ℤ[X]) : (X ^ w - 1 : ℤ[X]) ∣ expand ℤ (1 + w) g - g := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, add_sub_add_comm]
    exact dvd_add hp hq
  | monomial n a =>
    rw [expand_monomial, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial, ← mul_sub]
    apply dvd_mul_of_dvd_right
    have h1 : (X : ℤ[X]) ^ (n * (1 + w)) - X ^ n = X ^ n * ((X ^ w) ^ n - 1 ^ n) := by
      ring
    rw [h1]
    exact dvd_mul_of_dvd_right (sub_dvd_pow_sub_pow _ _ _) _

/- English proof (translation)
Take `⟨y, rfl⟩` from `hx`. Establish `hE : expand ℤ (1 + w) (X ^ w - 1 : ℤ[X]) = (X ^ w - 1) * ∑ i ∈ Finset.range (1 + w), ((X : ℤ[X]) ^ w) ^ i`. Rewrite using `[mul_comm, geom_sum_mul]`. Simplify using `only [map_sub, map_pow, expand_X, map_one, ← pow_mul, mul_comm]`. Establish `hSk : (X ^ w - 1 : ℤ[X]) ∣ ∑ i ∈ Finset.range (1 + w), ((X : ℤ[X]) ^ w) ^ i - ((1 + w : ℕ) : ℤ[X])`.

Establish `h1 : ((1 + w : ℕ) : ℤ[X]) = ∑ i ∈ Finset.range (1 + w), ((1 : ℤ[X]) ^ i)` using `by simp`. Rewrite using `[h1, ← Finset.sum_sub_distrib]`. Conclude with `Finset.dvd_sum fun i _ => by simpa using sub_dvd_pow_sub_pow ((X : ℤ[X]) ^ w) 1 i`. Establish `hSj` using `hSk.trans (sub_dvd_pow_sub_pow _ _ j)`. Establish `key : expand ℤ (1 + w) ((X ^ w - 1 : ℤ[X]) ^ j * y) - ((1 + w : ℕ) : ℤ[X]) ^ j * ((X ^ w - 1) ^ j * y) = (X ^ w - 1) ^ j * ((( ∑ i ∈ Finset.range (1 + w), ((X : ℤ[X]) ^ w) ^ i) ^ j - ((1 + w : ℕ) : ℤ[X]) ^ j) * expand ℤ (1 + w) y + ((1 + w : ℕ) : ℤ[X]) ^ j * (expand ℤ (1 + w) y - …`.

Rewrite using `[map_mul, map_pow, hE, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, pow_succ]`. Conclude with `mul_dvd_mul_left _ (dvd_add (dvd_mul_of_dvd_left hSj _) (dvd_mul_of_dvd_right (exp_cong w y) _))`.
-/
private theorem exp_step (w j : ℕ) (x : ℤ[X]) (hx : (X ^ w - 1 : ℤ[X]) ^ j ∣ x) :
    (X ^ w - 1 : ℤ[X]) ^ (j + 1) ∣ expand ℤ (1 + w) x - ((1 + w : ℕ) : ℤ[X]) ^ j * x := by
  obtain ⟨y, rfl⟩ := hx
  have hE : expand ℤ (1 + w) (X ^ w - 1 : ℤ[X]) = (X ^ w - 1) * ∑ i ∈ Finset.range (1 + w), ((X : ℤ[X]) ^ w) ^ i := by
    rw [mul_comm, geom_sum_mul]
    simp only [map_sub, map_pow, expand_X, map_one, ← pow_mul, mul_comm]
  have hSk : (X ^ w - 1 : ℤ[X]) ∣ ∑ i ∈ Finset.range (1 + w), ((X : ℤ[X]) ^ w) ^ i - ((1 + w : ℕ) : ℤ[X]) := by
    have h1 : ((1 + w : ℕ) : ℤ[X]) = ∑ i ∈ Finset.range (1 + w), ((1 : ℤ[X]) ^ i) := by simp
    rw [h1, ← Finset.sum_sub_distrib]
    exact Finset.dvd_sum fun i _ => by simpa using sub_dvd_pow_sub_pow ((X : ℤ[X]) ^ w) 1 i
  have hSj := hSk.trans (sub_dvd_pow_sub_pow _ _ j)
  have key : expand ℤ (1 + w) ((X ^ w - 1 : ℤ[X]) ^ j * y) - ((1 + w : ℕ) : ℤ[X]) ^ j * ((X ^ w - 1) ^ j * y) =
      (X ^ w - 1) ^ j * ((( ∑ i ∈ Finset.range (1 + w), ((X : ℤ[X]) ^ w) ^ i) ^ j - ((1 + w : ℕ) : ℤ[X]) ^ j) *
        expand ℤ (1 + w) y + ((1 + w : ℕ) : ℤ[X]) ^ j * (expand ℤ (1 + w) y - y)) := by
    rw [map_mul, map_pow, hE, mul_pow]; ring
  rw [key, pow_succ]
  exact mul_dvd_mul_left _ (dvd_add (dvd_mul_of_dvd_left hSj _) (dvd_mul_of_dvd_right (exp_cong w y) _))

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih => rw [pow_succ', Module.End.mul_apply, ih]`. Simplify using `[← pow_mul, pow_succ']`.
-/
private theorem exp_pow (k i : ℕ) : (((expand ℤ k).toLinearMap : Module.End ℤ ℤ[X]) ^ i) X = X ^ k ^ i := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', Module.End.mul_apply, ih]; simp [← pow_mul, pow_succ']

/- English proof (translation)
Establish `hdeg : (∏ j ∈ Finset.range M, (X - C ((1 + (w : ℤ)) ^ j)) : ℤ[X]).natDegree = M`. Rewrite using `[natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C _)]`. Simplify using `only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]`. Establish `hsum : ∑ i ∈ Finset.range (M + 1), (∏ j ∈ Finset.range M, (X - C ((1 + (w : ℤ)) ^ j)) : ℤ[X]).coeff i • (X : ℤ[X]) ^ (1 + w) ^ i = (aeval ((expand ℤ (1 + w)).toLinearMap : Module.End ℤ ℤ[X]) (∏ j ∈ Finset.range M, (X - C ((1 + (w : ℤ)) ^ j)) : ℤ[X])) X`. Rewrite using `[aeval_eq_sum_range, hdeg, LinearMap.sum_apply]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, exp_pow]`. Rewrite using `[hsum]`. Use `clear hsum hdeg`. Proceed by induction on `M with`.

Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Finset.prod_range_succ_comm, map_mul, Module.End.mul_apply]`. Establish `h` using `exp_step w n _ ih`. Simplify using `only [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply, AlgHom.toLinearMap_apply]`.

Use `h using 3` and compare the differences between its conclusion and the goal. Rewrite using `[zsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem exp_dvd (w M : ℕ) : (X ^ w - 1 : ℤ[X]) ^ M ∣ ∑ i ∈ Finset.range (M + 1),
    (∏ j ∈ Finset.range M, (X - C ((1 + (w : ℤ)) ^ j)) : ℤ[X]).coeff i • (X : ℤ[X]) ^ (1 + w) ^ i := by
  have hdeg : (∏ j ∈ Finset.range M, (X - C ((1 + (w : ℤ)) ^ j)) : ℤ[X]).natDegree = M := by
    rw [natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C _)]
    simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  have hsum : ∑ i ∈ Finset.range (M + 1),
      (∏ j ∈ Finset.range M, (X - C ((1 + (w : ℤ)) ^ j)) : ℤ[X]).coeff i • (X : ℤ[X]) ^ (1 + w) ^ i =
      (aeval ((expand ℤ (1 + w)).toLinearMap : Module.End ℤ ℤ[X])
        (∏ j ∈ Finset.range M, (X - C ((1 + (w : ℤ)) ^ j)) : ℤ[X])) X := by
    rw [aeval_eq_sum_range, hdeg, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, exp_pow]
  rw [hsum]
  clear hsum hdeg
  induction M with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ_comm, map_mul, Module.End.mul_apply]
    have h := exp_step w n _ ih
    simp only [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply,
      AlgHom.toLinearMap_apply]
    convert h using 3
    rw [zsmul_eq_mul]; push_cast; ring

/- English proof (translation)
Take `⟨a, u, hu, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd h0 l hl.ne_one`. Establish `hac : a ≤ c`. Assume the negation of the conclusion as `hca`. Establish `h1 : l ^ c ≤ l ^ a` using `Nat.pow_le_pow_right hl.pos (by omega)`. Establish `h2 : l ^ a ≤ l ^ a * u` using `Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by rintro rfl; exact hu (dvd_zero l)))`.

Use linear arithmetic over natural numbers and integers. Establish `hcop : Nat.Coprime u (l ^ ν)` using `Nat.Coprime.pow_right _ (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hl).2 hu))`. Use `⟨(l : ZMod (l ^ ν)) ^ (c - a) * (((ZMod.unitOfCoprime u hcop)⁻¹ : (ZMod (l ^ ν))ˣ) : ZMod (l ^ ν)), ?_⟩` and prove the remaining obligations. Establish `hv : (u : ZMod (l ^ ν)) * (((ZMod.unitOfCoprime u hcop)⁻¹ : (ZMod (l ^ ν))ˣ) : ZMod (l ^ ν)) = 1` using `(ZMod.unitOfCoprime u hcop).mul_inv`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hv, mul_one, ← pow_add, Nat.add_sub_cancel' hac]`. Use `_ = _ := by push_cast; ring`.
-/
private theorem nat_dvd (l c ν n : ℕ) (hl : l.Prime) (h0 : n ≠ 0) (hn : n < l ^ c) :
    (n : ZMod (l ^ ν)) ∣ (l : ZMod (l ^ ν)) ^ c := by
  obtain ⟨a, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd h0 l hl.ne_one
  have hac : a ≤ c := by
    by_contra hca
    have h1 : l ^ c ≤ l ^ a := Nat.pow_le_pow_right hl.pos (by omega)
    have h2 : l ^ a ≤ l ^ a * u := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by rintro rfl; exact hu (dvd_zero l)))
    omega
  have hcop : Nat.Coprime u (l ^ ν) :=
    Nat.Coprime.pow_right _ (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hl).2 hu))
  refine ⟨(l : ZMod (l ^ ν)) ^ (c - a) * (((ZMod.unitOfCoprime u hcop)⁻¹ : (ZMod (l ^ ν))ˣ) : ZMod (l ^ ν)), ?_⟩
  have hv : (u : ZMod (l ^ ν)) * (((ZMod.unitOfCoprime u hcop)⁻¹ : (ZMod (l ^ ν))ˣ) : ZMod (l ^ ν)) = 1 :=
    (ZMod.unitOfCoprime u hcop).mul_inv
  calc (l : ZMod (l ^ ν)) ^ c = (l : ZMod (l ^ ν)) ^ a * (l : ZMod (l ^ ν)) ^ (c - a) *
        ((u : ZMod (l ^ ν)) * (((ZMod.unitOfCoprime u hcop)⁻¹ : (ZMod (l ^ ν))ˣ) : ZMod (l ^ ν))) := by
        rw [hv, mul_one, ← pow_add, Nat.add_sub_cancel' hac]
    _ = _ := by push_cast; ring

/- English proof (translation)
Break down `lt_or_gt_of_ne h with hst | hst` into its components or cases. Establish `h1` using `nat_dvd l c ν (t - s) hl (by omega) (by omega)`. Rewrite `h1` using `[Nat.cast_sub hst.le]`. Rewrite using `[← neg_sub, neg_dvd]`. Conclude with `h1`.

Establish `h1` using `nat_dvd l c ν (s - t) hl (by omega) (by omega)`. Rewrite `h1` using `[Nat.cast_sub hst.le]`. Then use the resulting hypothesis.
-/
private theorem diff_dvd (l c ν s t : ℕ) (hl : l.Prime) (h : s ≠ t) (hs : s < l ^ c) (ht : t < l ^ c) :
    ((s : ZMod (l ^ ν)) - t) ∣ (l : ZMod (l ^ ν)) ^ c := by
  rcases lt_or_gt_of_ne h with hst | hst
  · have h1 := nat_dvd l c ν (t - s) hl (by omega) (by omega)
    rw [Nat.cast_sub hst.le] at h1
    rw [← neg_sub, neg_dvd]
    exact h1
  · have h1 := nat_dvd l c ν (s - t) hl (by omega) (by omega)
    rwa [Nat.cast_sub hst.le] at h1

/- English proof (translation)
Take `⟨c, rfl⟩` from `h`. Establish `hc : a * c = c.val • a` using `by rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]`. Rewrite using `[hc]`. Establish `h1` using `sub_dvd_pow_sub_pow (AddMonoidAlgebra.single a (1 : ℤ)) 1 c.val`. Rewrite `h1` using `[one_pow, AddMonoidAlgebra.single_pow, one_pow]`. Then use the resulting hypothesis.
-/
private theorem sgl_dvd {q : ℕ} [NeZero q] (a b : ZMod q) (h : a ∣ b) :
    (AddMonoidAlgebra.single a 1 - 1 : AddMonoidAlgebra ℤ (ZMod q)) ∣ AddMonoidAlgebra.single b 1 - 1 := by
  obtain ⟨c, rfl⟩ := h
  have hc : a * c = c.val • a := by rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]
  rw [hc]
  have h1 := sub_dvd_pow_sub_pow (AddMonoidAlgebra.single a (1 : ℤ)) 1 c.val
  rwa [one_pow, AddMonoidAlgebra.single_pow, one_pow] at h1

/- English proof (translation)
Establish `h` using `map_dvd (aeval (R := ℤ) (AddMonoidAlgebra.single (1 : ZMod q) (1 : ℤ))) (exp_dvd w M)`. Simplify using `only [map_sum, map_zsmul, map_pow, map_sub, map_one, aeval_X, AddMonoidAlgebra.single_pow, one_pow, nsmul_one, AddMonoidAlgebra.smul_single', mul_one, Nat.cast_pow, Nat.cast_add, Nat.cast_one] at h`. Simplify `h` using `only [map_pow]`.
-/
private theorem alg_dvd (q w M : ℕ) :
    (AddMonoidAlgebra.single (w : ZMod q) 1 - 1 : AddMonoidAlgebra ℤ (ZMod q)) ^ M ∣ ∑ i ∈ Finset.range (M + 1),
      AddMonoidAlgebra.single ((1 + (w : ZMod q)) ^ i)
        ((∏ j ∈ Finset.range M, (X - C ((1 + (w : ℤ)) ^ j)) : ℤ[X]).coeff i) := by
  have h := map_dvd (aeval (R := ℤ) (AddMonoidAlgebra.single (1 : ZMod q) (1 : ℤ))) (exp_dvd w M)
  simp only [map_sum, map_zsmul, map_pow, map_sub, map_one, aeval_X, AddMonoidAlgebra.single_pow, one_pow,
    nsmul_one, AddMonoidAlgebra.smul_single', mul_one, Nat.cast_pow, Nat.cast_add, Nat.cast_one] at h
  simpa only [map_pow] using h

private def push (q : ℕ) (t : ZMod q) : ZMod q × ZMod q →+ ZMod q where
  toFun x := x.1 + t * x.2
  map_zero' := by simp
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add]; ring

/- English proof (translation)
Introduce `l c ν M hl hM _ t₀`. Establish `hp : l.Prime` using `hl.out`. Use `haveI : NeZero (l ^ ν) := ⟨pow_ne_zero _ hp.ne_zero⟩`. Establish `hF` using `alg_dvd (l ^ ν) (l ^ c) M`. Simplify using `only [Nat.cast_pow] at hF`.

Set `φ : ZMod (l ^ ν) → AddMonoidAlgebra ℤ (ZMod (l ^ ν) × ZMod (l ^ ν)) →+* AddMonoidAlgebra ℤ (ZMod (l ^ ν))` to `fun t => AddMonoidAlgebra.mapDomainRingHom ℤ (push (l ^ ν) t)`. Establish `hφ : ∀ (t : ZMod (l ^ ν)) (η : AddMonoidAlgebra ℤ (ZMod (l ^ ν) × ZMod (l ^ ν))), φ t η = AddMonoidAlgebra.mapDomain (fun x : ZMod (l ^ ν) × ZMod (l ^ ν) => x.1 + t * x.2) η`. Introduce `t η`. Simplify using `only [φ, AddMonoidAlgebra.mapDomainRingHom_apply]`. Both sides reduce to the same expression.

Establish `hφs : ∀ (t : ZMod (l ^ ν)) (x : ZMod (l ^ ν) × ZMod (l ^ ν)), φ t (AddMonoidAlgebra.single x 1) = AddMonoidAlgebra.single (x.1 + t * x.2) 1`. Introduce `t x`. Rewrite using `[hφ, AddMonoidAlgebra.mapDomain_single]`. Set `ι : AddMonoidAlgebra ℤ (ZMod (l ^ ν)) →+* AddMonoidAlgebra ℤ (ZMod (l ^ ν) × ZMod (l ^ ν))` to `AddMonoidAlgebra.mapDomainRingHom ℤ (AddMonoidHom.inl (ZMod (l ^ ν)) (ZMod (l ^ ν)))`. Establish `hφι : ∀ t y, φ t (ι y) = y`.

Introduce `t y`. Use `AddMonoidAlgebra.induction_linear y (by simp) (fun a b ha hb => by rw [map_add, map_add, ha, hb]) (fun m r => ?_)` and prove the remaining obligations. Simplify using `only [ι, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single, hφ]`. Simplify using the standard rewrite rules. Use `set s : Finset (Fin (M + 1)) := Finset.univ.erase t₀ with hs`.

Establish `hdiv : ∏ t' ∈ s, (AddMonoidAlgebra.single (((t₀ : ℕ) : ZMod (l ^ ν)) - ((t' : ℕ) : ZMod (l ^ ν))) (1 : ℤ) - 1) ∣ (AddMonoidAlgebra.single ((l : ZMod (l ^ ν)) ^ c) (1 : ℤ) - 1) ^ M`. Establish `hcard : s.card = M` using `by simp [hs, Finset.card_erase_of_mem]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨Q, hQ⟩` from `hdiv.trans hF`. Use `⟨((∏ t' ∈ s, (AddMonoidAlgebra.single ((0 : ZMod (l ^ ν)), (1 : ZMod (l ^ ν))) (1 : ℤ) - AddMonoidAlgebra.single (((t' : ℕ) : ZMod (l ^ ν)), (0 : ZMod (l ^ ν))) 1)) * ι (AddMonoidAlgebra.single (-∑ t' ∈ s, ((t' : ℕ) : ZMod (l ^ ν))) 1 * Q)).coeff, ?_, ?_⟩` and prove the remaining obligations.

Introduce `t ht`. Rewrite using `[← AddMonoidAlgebra.coeff_mapDomain, ← hφ, map_mul, map_prod]`. Rewrite using `[Finset.prod_eq_zero (i := t) (by simp [hs, ht]) (by rw [map_sub, hφs, hφs]; simp), zero_mul, AddMonoidAlgebra.coeff_zero]`. Rewrite using `[← AddMonoidAlgebra.coeff_mapDomain, ← hφ, map_mul, map_prod, hφι]`. Establish `hfac : ∀ t' : Fin (M + 1), φ ((t₀ : ℕ) : ZMod (l ^ ν)) (AddMonoidAlgebra.single ((0 : ZMod (l ^ ν)), (1 : ZMod (l ^ ν))) (1 : ℤ) - AddMonoidAlgebra.single (((t' : ℕ) : ZMod (l ^ ν)), (0 : ZMod (l ^ ν))) 1) = AddMonoidAlgebra.single ((t' : ℕ) : ZMod (l ^ ν)) (1 : ℤ) * (AddMonoidAl …`.

Introduce `t'`. Rewrite using `[map_sub, hφs, hφs, mul_sub, AddMonoidAlgebra.single_mul_single, mul_one, AddMonoidAlgebra.one_def, mul_one]`. Simplify using the standard rewrite rules. Establish `h1 : (∏ t' ∈ s, AddMonoidAlgebra.single ((t' : ℕ) : ZMod (l ^ ν)) (1 : ℤ)) * AddMonoidAlgebra.single (-∑ t' ∈ s, ((t' : ℕ) : ZMod (l ^ ν))) 1 = 1`. Rewrite using `[AddMonoidAlgebra.prod_single, AddMonoidAlgebra.single_mul_single, add_neg_cancel, Finset.prod_const_one, mul_one, AddMonoidAlgebra.one_def]`.

Establish `hmain : (∏ t' ∈ s, φ ((t₀ : ℕ) : ZMod (l ^ ν)) (AddMonoidAlgebra.single ((0 : ZMod (l ^ ν)), (1 : ZMod (l ^ ν))) (1 : ℤ) - AddMonoidAlgebra.single (((t' : ℕ) : ZMod (l ^ ν)), (0 : ZMod (l ^ ν))) 1)) * (AddMonoidAlgebra.single (-∑ t' ∈ s, ((t' : ℕ) : ZMod (l ^ ν))) 1 * Q) = (∏ t' …`. Simplify using `only [hfac, Finset.prod_mul_distrib]`. Take the linear combination `(∏ t' ∈ s, (AddMonoidAlgebra.single (((t₀ : ℕ) : ZMod (l ^ ν)) - ((t' : ℕ) : ZMod (l ^ ν))) (1 : ℤ) - 1)) * Q * h1`. Rewrite using `[hmain, ← hQ]`. Simplify using `[AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single]`.
-/
theorem UpperTheory.V.ZK.sEta :
    UpperTheory.V.ZK.SEta := by
  intro l c ν M hl hM _ t₀
  have hp : l.Prime := hl.out
  haveI : NeZero (l ^ ν) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hF := alg_dvd (l ^ ν) (l ^ c) M
  simp only [Nat.cast_pow] at hF
  let φ : ZMod (l ^ ν) → AddMonoidAlgebra ℤ (ZMod (l ^ ν) × ZMod (l ^ ν)) →+* AddMonoidAlgebra ℤ (ZMod (l ^ ν)) :=
    fun t => AddMonoidAlgebra.mapDomainRingHom ℤ (push (l ^ ν) t)
  have hφ : ∀ (t : ZMod (l ^ ν)) (η : AddMonoidAlgebra ℤ (ZMod (l ^ ν) × ZMod (l ^ ν))),
      φ t η = AddMonoidAlgebra.mapDomain (fun x : ZMod (l ^ ν) × ZMod (l ^ ν) => x.1 + t * x.2) η := by
    intro t η
    simp only [φ, AddMonoidAlgebra.mapDomainRingHom_apply]
    rfl
  have hφs : ∀ (t : ZMod (l ^ ν)) (x : ZMod (l ^ ν) × ZMod (l ^ ν)),
      φ t (AddMonoidAlgebra.single x 1) = AddMonoidAlgebra.single (x.1 + t * x.2) 1 := by
    intro t x; rw [hφ, AddMonoidAlgebra.mapDomain_single]
  let ι : AddMonoidAlgebra ℤ (ZMod (l ^ ν)) →+* AddMonoidAlgebra ℤ (ZMod (l ^ ν) × ZMod (l ^ ν)) :=
    AddMonoidAlgebra.mapDomainRingHom ℤ (AddMonoidHom.inl (ZMod (l ^ ν)) (ZMod (l ^ ν)))
  have hφι : ∀ t y, φ t (ι y) = y := by
    intro t y
    refine AddMonoidAlgebra.induction_linear y (by simp) (fun a b ha hb => by rw [map_add, map_add, ha, hb])
      (fun m r => ?_)
    simp only [ι, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single, hφ]
    simp
  set s : Finset (Fin (M + 1)) := Finset.univ.erase t₀ with hs
  have hdiv : ∏ t' ∈ s, (AddMonoidAlgebra.single (((t₀ : ℕ) : ZMod (l ^ ν)) - ((t' : ℕ) : ZMod (l ^ ν))) (1 : ℤ) - 1) ∣
      (AddMonoidAlgebra.single ((l : ZMod (l ^ ν)) ^ c) (1 : ℤ) - 1) ^ M := by
    have hcard : s.card = M := by simp [hs, Finset.card_erase_of_mem]
    calc _ ∣ ∏ _t' ∈ s, (AddMonoidAlgebra.single ((l : ZMod (l ^ ν)) ^ c) (1 : ℤ) - 1) :=
          Finset.prod_dvd_prod_of_dvd _ _ fun t' ht' => sgl_dvd _ _ (diff_dvd l c ν t₀ t' hp
            (fun h => (Finset.ne_of_mem_erase ht') (Fin.ext h).symm)
            (by have := t₀.isLt; omega) (by have := t'.isLt; omega))
      _ = _ := by rw [Finset.prod_const, hcard]
  obtain ⟨Q, hQ⟩ := hdiv.trans hF
  refine ⟨((∏ t' ∈ s, (AddMonoidAlgebra.single ((0 : ZMod (l ^ ν)), (1 : ZMod (l ^ ν))) (1 : ℤ) -
      AddMonoidAlgebra.single (((t' : ℕ) : ZMod (l ^ ν)), (0 : ZMod (l ^ ν))) 1)) *
      ι (AddMonoidAlgebra.single (-∑ t' ∈ s, ((t' : ℕ) : ZMod (l ^ ν))) 1 * Q)).coeff, ?_, ?_⟩
  · intro t ht
    rw [← AddMonoidAlgebra.coeff_mapDomain, ← hφ, map_mul, map_prod]
    rw [Finset.prod_eq_zero (i := t) (by simp [hs, ht]) (by rw [map_sub, hφs, hφs]; simp), zero_mul,
      AddMonoidAlgebra.coeff_zero]
  · rw [← AddMonoidAlgebra.coeff_mapDomain, ← hφ, map_mul, map_prod, hφι]
    have hfac : ∀ t' : Fin (M + 1), φ ((t₀ : ℕ) : ZMod (l ^ ν))
        (AddMonoidAlgebra.single ((0 : ZMod (l ^ ν)), (1 : ZMod (l ^ ν))) (1 : ℤ) -
          AddMonoidAlgebra.single (((t' : ℕ) : ZMod (l ^ ν)), (0 : ZMod (l ^ ν))) 1) =
        AddMonoidAlgebra.single ((t' : ℕ) : ZMod (l ^ ν)) (1 : ℤ) *
          (AddMonoidAlgebra.single (((t₀ : ℕ) : ZMod (l ^ ν)) - ((t' : ℕ) : ZMod (l ^ ν))) 1 - 1) := by
      intro t'
      rw [map_sub, hφs, hφs, mul_sub, AddMonoidAlgebra.single_mul_single, mul_one, AddMonoidAlgebra.one_def,
        mul_one]
      simp
    have h1 : (∏ t' ∈ s, AddMonoidAlgebra.single ((t' : ℕ) : ZMod (l ^ ν)) (1 : ℤ)) *
        AddMonoidAlgebra.single (-∑ t' ∈ s, ((t' : ℕ) : ZMod (l ^ ν))) 1 = 1 := by
      rw [AddMonoidAlgebra.prod_single, AddMonoidAlgebra.single_mul_single, add_neg_cancel,
        Finset.prod_const_one, mul_one, AddMonoidAlgebra.one_def]
    have hmain : (∏ t' ∈ s, φ ((t₀ : ℕ) : ZMod (l ^ ν))
        (AddMonoidAlgebra.single ((0 : ZMod (l ^ ν)), (1 : ZMod (l ^ ν))) (1 : ℤ) -
          AddMonoidAlgebra.single (((t' : ℕ) : ZMod (l ^ ν)), (0 : ZMod (l ^ ν))) 1)) *
        (AddMonoidAlgebra.single (-∑ t' ∈ s, ((t' : ℕ) : ZMod (l ^ ν))) 1 * Q) =
        (∏ t' ∈ s, (AddMonoidAlgebra.single (((t₀ : ℕ) : ZMod (l ^ ν)) -
          ((t' : ℕ) : ZMod (l ^ ν))) (1 : ℤ) - 1)) * Q := by
      simp only [hfac, Finset.prod_mul_distrib]
      linear_combination (∏ t' ∈ s, (AddMonoidAlgebra.single (((t₀ : ℕ) : ZMod (l ^ ν)) -
        ((t' : ℕ) : ZMod (l ^ ν))) (1 : ℤ) - 1)) * Q * h1
    rw [hmain, ← hQ]
    simp [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single]
