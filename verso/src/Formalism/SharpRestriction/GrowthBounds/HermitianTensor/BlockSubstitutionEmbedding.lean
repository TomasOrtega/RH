import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.SubYGenCoefHom

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf.QB

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

def th (K : Type) [Field K] (r : ℕ) (b : Bool) :
    MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K →ₐ[K]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K) :=
  (mapAlgHom (blockEmb K (k := r) (n := r) b)).comp (subY K r)

/- English proof (translation)
Use `show rename _ (X x) = _`. Rewrite using `[rename_X]`.
-/
theorem blockEmb_X (K : Type) [Field K] {k n : ℕ} (b : Bool) (x : Fin k × Fin n) :
    blockEmb K b (X x) = (X (b, x) : MvPolynomial (Bool × (Fin k × Fin n)) K) := by
  show rename _ (X x) = _
  rw [rename_X]

/- English proof (translation)
Rewrite using `[th, AlgHom.comp_apply, subY_C, mAH_C, algHom_C, algebraMap_eq]`.
-/
theorem th_C (K : Type) [Field K] (r : ℕ) (b : Bool) (a : K) : th K r b (C a) = C (C a) := by
  rw [th, AlgHom.comp_apply, subY_C, mAH_C, algHom_C, algebraMap_eq]

/- English proof (translation)
Rewrite using `[th, AlgHom.comp_apply, mAH_subY_mid]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[blockEmb_X]`.
-/
theorem th_X_mid (K : Type) [Field K] (r : ℕ) (b : Bool) (a : Fin (r + 1 + 1)) (j : Fin r) :
    th K r b (X (a, midI r j)) = ∑ i : Fin r, C (X (b, (i, j))) * X (a, midI r i) := by
  rw [th, AlgHom.comp_apply, mAH_subY_mid]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [blockEmb_X]

/- English proof (translation)
Rewrite using `[th, AlgHom.comp_apply, mAH_subY_none r _ a t h]`.
-/
theorem th_X_none (K : Type) [Field K] (r : ℕ) (b : Bool) (a t : Fin (r + 1 + 1)) (h : midOf t = none) :
    th K r b (X (a, t)) = X (a, t) := by
  rw [th, AlgHom.comp_apply, mAH_subY_none r _ a t h]

/- English proof (translation)
Rewrite using `[th, AlgHom.comp_apply, mAH_coeff]`.
-/
theorem th_coeff (K : Type) [Field K] (r : ℕ) (b : Bool) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (u : Fin (r + 1 + 1) × Fin (r + 1 + 1) →₀ ℕ) :
    coeff u (th K r b v) = blockEmb K b (coeff u (subY K r v)) := by
  rw [th, AlgHom.comp_apply, mAH_coeff]

/- English proof (translation)
Establish `: (sub2 K r).comp (blockEmb K (k` using `r + 1 + 1) (n := r + 1 + 1) b) = th K r b := by`. Apply `algHom_ext` to reduce the goal to its premises. Introduce `w`. Rewrite using `[AlgHom.comp_apply, blockEmb_X]`. Unfold `sub2`.

Rewrite using `[aeval_X]`. Both sides reduce to the same expression. Conclude with `AlgHom.congr_fun this v`.
-/
theorem block_substitution_embedding (K : Type) [Field K] (r : ℕ) (b : Bool) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) :
    sub2 K r (blockEmb K b v) = th K r b v := by
  have : (sub2 K r).comp (blockEmb K (k := r + 1 + 1) (n := r + 1 + 1) b) = th K r b := by
    apply algHom_ext
    intro w
    rw [AlgHom.comp_apply, blockEmb_X]
    unfold sub2
    rw [aeval_X]
    rfl
  exact AlgHom.congr_fun this v

/- English proof (translation)
Unfold `lamOf`. Rewrite using `[LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, block_substitution_embedding, block_substitution_embedding]`.
-/
theorem lam_eq (K : Type) [Field K] (r : ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) :
    lamOf K r L (blockEmb K true v * blockEmb K false t) = lcoef L (th K r true v * th K r false t) := by
  unfold lamOf
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, block_substitution_embedding, block_substitution_embedding]

section Psi

variable {K B σ : Type} [Field K] [CommRing B] [Algebra K B]

def psiB (B : Type) [CommRing B] [Algebra K B] (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) :
    MvPolynomial σ B →+* MvPolynomial σ B :=
  eval₂Hom C (fun w => map (algebraMap K B) (ψ (X w)))

/- English proof (translation)
Use `show eval₂ _ _ (C b) = _`. Rewrite using `[eval₂_C]`.
-/
theorem psiB_C (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) (b : B) : psiB B ψ (C b) = C b := by
  show eval₂ _ _ (C b) = _
  rw [eval₂_C]

/- English proof (translation)
Use `show eval₂ _ _ (X w) = _`. Rewrite using `[eval₂_X]`.
-/
theorem psiB_X (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) (w : σ) :
    psiB B ψ (X w) = map (algebraMap K B) (ψ (X w)) := by
  show eval₂ _ _ (X w) = _
  rw [eval₂_X]

/- English proof (translation)
Establish `: (psiB B ψ).comp (map (algebraMap K B)) = (map (algebraMap K B)).comp (ψ : MvPolynomial σ K →+* MvPolynomial σ K)`. Apply `ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `only [RingHom.comp_apply, RingHom.coe_coe, map_C, psiB_C, algHom_C, algebraMap_eq]`. Introduce `w`.

Simplify using `only [RingHom.comp_apply, RingHom.coe_coe, map_X, psiB_X]`. Conclude with `RingHom.congr_fun this G`.
-/
theorem psiB_map (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) (G : MvPolynomial σ K) :
    psiB B ψ (map (algebraMap K B) G) = map (algebraMap K B) (ψ G) := by
  have : (psiB B ψ).comp (map (algebraMap K B)) = (map (algebraMap K B)).comp (ψ : MvPolynomial σ K →+* MvPolynomial σ K) := by
    apply ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, RingHom.coe_coe, map_C, psiB_C, algHom_C, algebraMap_eq]
    · intro w
      simp only [RingHom.comp_apply, RingHom.coe_coe, map_X, psiB_X]
  exact RingHom.congr_fun this G

/- English proof (translation)
Use extensionality with `u`. Rewrite using `[coeff_lcoef, coeff_C_mul, coeff_map, coeff_smul, smul_eq_mul, mul_comm b, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]`.
-/
theorem lcoef_C_mul_map (L : B →ₗ[K] K) (b : B) (G : MvPolynomial σ K) :
    lcoef L (C b * map (algebraMap K B) G) = L b • G := by
  ext u
  rw [coeff_lcoef, coeff_C_mul, coeff_map, coeff_smul, smul_eq_mul, mul_comm b, ← Algebra.smul_def, map_smul,
    smul_eq_mul, mul_comm]

/- English proof (translation)
Proceed by induction on `h using MvPolynomial.induction_on' with`. Consider the case `monomial u b`. Establish `e : (monomial u b : MvPolynomial σ B) = C b * map (algebraMap K B) (monomial u 1)`. Rewrite using `[map_monomial, map_one, C_mul_monomial, mul_one]`. Rewrite using `[e, lcoef_C_mul_map, map_mul, psiB_map, psiB_C, lcoef_C_mul_map, map_smul]`.

Consider the case `add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]`.
-/
theorem lcoef_comm (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) (L : B →ₗ[K] K) (h : MvPolynomial σ B) :
    ψ (lcoef L h) = lcoef L (psiB B ψ h) := by
  induction h using MvPolynomial.induction_on' with
  | monomial u b =>
    have e : (monomial u b : MvPolynomial σ B) = C b * map (algebraMap K B) (monomial u 1) := by
      rw [map_monomial, map_one, C_mul_monomial, mul_one]
    rw [e, lcoef_C_mul_map, map_mul, psiB_map, psiB_C, lcoef_C_mul_map, map_smul]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]

/- English proof (translation)
Rewrite using `[ringHom_ext hC hX]`.
-/
theorem hom_eq_on {S : Type} [CommRing S] (f g : MvPolynomial σ K →+* S) (hC : ∀ a, f (C a) = g (C a))
    (hX : ∀ w, f (X w) = g (X w)) (v : MvPolynomial σ K) : f v = g v := by
  rw [ringHom_ext hC hX]

end Psi

/- English proof (translation)
Establish `h1 : (Polynomial.X ^ (a + 1) : Polynomial K) = Polynomial.X ^ (b + 1)`. Apply `Polynomial.funext` to reduce the goal to its premises. Introduce `c`. Simplify using `only [Polynomial.eval_pow, Polynomial.eval_X]`. Distinguish the cases in `hc : c = 0`.

Rewrite using `[hc, zero_pow (Nat.succ_ne_zero _), zero_pow (Nat.succ_ne_zero _)]`. Rewrite using `[pow_succ, pow_succ, h c hc]`. Establish `h2` using `congrArg Polynomial.natDegree h1`. Rewrite `h2` using `[Polynomial.natDegree_X_pow, Polynomial.natDegree_X_pow]`. Use linear arithmetic over natural numbers and integers.
-/
theorem pow_exp_inj {K : Type} [Field K] [Infinite K] (a b : ℕ) (h : ∀ c : K, c ≠ 0 → c ^ a = c ^ b) : a = b := by
  have h1 : (Polynomial.X ^ (a + 1) : Polynomial K) = Polynomial.X ^ (b + 1) := by
    apply Polynomial.funext
    intro c
    simp only [Polynomial.eval_pow, Polynomial.eval_X]
    by_cases hc : c = 0
    · rw [hc, zero_pow (Nat.succ_ne_zero _), zero_pow (Nat.succ_ne_zero _)]
    · rw [pow_succ, pow_succ, h c hc]
  have h2 := congrArg Polynomial.natDegree h1
  rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X_pow] at h2
  omega

section Scale

variable {K : Type} [Field K]

/- English proof (translation)
Rewrite using `[aeval_monomial]`. Simplify using `only [mul_pow]`. Rewrite using `[Finsupp.prod_mul]`. Establish `hC : (u.prod fun v e => (C (d v) : MvPolynomial σ K) ^ e) = C (u.prod fun v e => d v ^ e)`. Rewrite using `[map_finsuppProd]`.

Simplify using `only [map_pow]`. Rewrite using `[hC, monomial_eq, C_mul, algebraMap_eq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sc_monomial {σ : Type} (d : σ → K) (u : σ →₀ ℕ) (a : K) :
    aeval (fun w => C (d w) * X w) (monomial u a) = monomial u (a * u.prod fun w e => d w ^ e) := by
  rw [aeval_monomial]
  simp only [mul_pow]
  rw [Finsupp.prod_mul]
  have hC : (u.prod fun v e => (C (d v) : MvPolynomial σ K) ^ e) = C (u.prod fun v e => d v ^ e) := by
    rw [map_finsuppProd]; simp only [map_pow]
  rw [hC, monomial_eq, C_mul, algebraMap_eq]
  ring

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on' with`. Consider the case `monomial u a`. Rewrite using `[sc_monomial, coeff_monomial, coeff_monomial]`. Use `split_ifs with h`. Rewrite using `[h]`.

Rewrite using `[zero_mul]`. Consider the case `add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, add_mul]`.
-/
theorem sc_coeff {σ : Type} (d : σ → K) (f : MvPolynomial σ K) (m : σ →₀ ℕ) :
    coeff m (aeval (fun w => C (d w) * X w) f) = coeff m f * m.prod fun w e => d w ^ e := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [sc_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · rw [zero_mul]
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, add_mul]

def scCol (K : Type) [Field K] (k : ℕ) (t0 : Fin k) (c : K) :
    MvPolynomial (Fin k × Fin k) K →ₐ[K] MvPolynomial (Fin k × Fin k) K :=
  aeval (fun w => C (if w.2 = t0 then c else 1) * X w)

/- English proof (translation)
Unfold `scCol`. Rewrite using `[aeval_X]`.
-/
theorem scCol_X {k : ℕ} (t0 : Fin k) (c : K) (w : Fin k × Fin k) :
    scCol K k t0 c (X w) = C (if w.2 = t0 then c else 1) * X w := by
  unfold scCol
  rw [aeval_X]

/- English proof (translation)
Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, lccomp_weight_colW_apply, ← Finset.prod_pow_eq_pow_sum]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_eq_single t0]`. Simplify using the standard rewrite rules. Introduce `t _ ht`.

Simplify using `[ht]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem sc_prod {k : ℕ} (t0 : Fin k) (c : K) (m : Fin k × Fin k →₀ ℕ) :
    (m.prod fun w e => (if w.2 = t0 then c else 1) ^ e) = c ^ (Finsupp.weight (colW k k) m t0) := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, lccomp_weight_colW_apply,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.prod_eq_single t0]
  · simp
  · intro t _ ht
    simp [ht]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Unfold `scCol`. Rewrite using `[sc_coeff, sc_prod]`.
-/
theorem scCol_coeff {k : ℕ} (t0 : Fin k) (c : K) (f : MvPolynomial (Fin k × Fin k) K) (m : Fin k × Fin k →₀ ℕ) :
    coeff m (scCol K k t0 c f) = coeff m f * c ^ (Finsupp.weight (colW k k) m t0) := by
  unfold scCol
  rw [sc_coeff, sc_prod]

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[scCol_coeff, coeff_smul, smul_eq_mul, mul_comm]`. Distinguish the cases in `h : coeff m f = 0`. Rewrite using `[h, mul_zero, mul_zero]`. Rewrite using `[hf h]`.
-/
theorem scCol_of_hom {k : ℕ} (t0 : Fin k) (c : K) (f : MvPolynomial (Fin k × Fin k) K) (ν : Fin k → ℕ)
    (hf : IsWeightedHomogeneous (colW k k) f ν) : scCol K k t0 c f = c ^ ν t0 • f := by
  ext m
  rw [scCol_coeff, coeff_smul, smul_eq_mul, mul_comm]
  by_cases h : coeff m f = 0
  · rw [h, mul_zero, mul_zero]
  · rw [hf h]

/- English proof (translation)
Apply `pow_exp_inj (K := K)` to reduce the goal to its premises. Introduce `c hc`. Use `congrArg (coeff m) (h c hc)` as an intermediate fact. Rewrite `this` using `[scCol_coeff, coeff_smul, smul_eq_mul, mul_comm]`. Conclude with `mul_right_cancel₀ hm this`.
-/
theorem wt_of_scale [Infinite K] {k : ℕ} (t0 : Fin k) (n : ℕ) (f : MvPolynomial (Fin k × Fin k) K)
    (h : ∀ c : K, c ≠ 0 → scCol K k t0 c f = c ^ n • f) (m : Fin k × Fin k →₀ ℕ) (hm : coeff m f ≠ 0) :
    Finsupp.weight (colW k k) m t0 = n := by
  apply pow_exp_inj (K := K)
  intro c hc
  have := congrArg (coeff m) (h c hc)
  rw [scCol_coeff, coeff_smul, smul_eq_mul, mul_comm] at this
  exact mul_right_cancel₀ hm this

/- English proof (translation)
Establish `e : colAdd K l j c f = ∑ m ∈ f.support, colAdd K l j c (monomial m (coeff m f))` using `by conv_lhs => rw [f.as_sum]`. Rewrite using `[map_sum]`. Rewrite using `[e]`. Use `conv_rhs => rw [f.as_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations.

Unfold `colAdd`. Rewrite using `[aeval_monomial, monomial_eq, algebraMap_eq]`. Use `congr 1`. Apply `Finsupp.prod_congr` to reduce the goal to its premises. Introduce `w hw`.

Establish `hwj : w.2 ≠ j`. Introduce `h`. Establish `h0` using `hf m (mem_support_iff.1 hm)`. Rewrite `h0` using `[lccomp_weight_colW_apply]`. Establish `h1` using `Finset.sum_eq_zero_iff.1 h0 w.1 (Finset.mem_univ _)`.

Establish `e2 : w = (w.1, j)` using `Prod.ext rfl h`. Apply `Finsupp.mem_support_iff.1 hw` to reduce the goal to its premises. Rewrite using `[e2]`. Conclude with `h1`. Rewrite using `[if_neg hwj]`.
-/
theorem colAdd_trivial {k : ℕ} (l j : Fin k) (c : K) (f : MvPolynomial (Fin k × Fin k) K)
    (hf : ∀ m, coeff m f ≠ 0 → Finsupp.weight (colW k k) m j = 0) : colAdd K l j c f = f := by
  classical
  have e : colAdd K l j c f = ∑ m ∈ f.support, colAdd K l j c (monomial m (coeff m f)) := by
    conv_lhs => rw [f.as_sum]
    rw [map_sum]
  rw [e]
  conv_rhs => rw [f.as_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  unfold colAdd
  rw [aeval_monomial, monomial_eq, algebraMap_eq]
  congr 1
  apply Finsupp.prod_congr
  intro w hw
  have hwj : w.2 ≠ j := by
    intro h
    have h0 := hf m (mem_support_iff.1 hm)
    rw [lccomp_weight_colW_apply] at h0
    have h1 := Finset.sum_eq_zero_iff.1 h0 w.1 (Finset.mem_univ _)
    have e2 : w = (w.1, j) := Prod.ext rfl h
    apply Finsupp.mem_support_iff.1 hw
    rw [e2]
    exact h1
  rw [if_neg hwj]

end Scale

end Formalism.MainNotions.flipOneThree.Pf.QB

end
