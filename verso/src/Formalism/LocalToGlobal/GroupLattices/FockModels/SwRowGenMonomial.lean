import Formalism.LocalToGlobal.GroupLattices.FockModels.SwRowDivZero
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LEhwLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LGradedLemmas

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.GradedWeylDivisibility

/- English proof (translation)
Take `⟨b, hb, h2⟩` from `sSBasis R r n ν`. Rewrite `hf` using `[← hb.2.1]`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`.

Take `⟨-, -, K, sz, hsz, I, hshape, -, hbm⟩` from `h2 i`. Introduce `m hm k`. Rewrite `hm` using `[hbm]`. Establish `h` using `(bidetDominance R r n K sz hsz I m hm).1 k`. Rewrite `h` using `[hshape]`.

Conclude with `h`. Consider the case `zero`. Introduce `m hm`. Simplify using `at hm`. Consider the case `add x y _ _ hx hy`.

Introduce `m hm`. Break down `Finset.mem_union.mp (support_add hm) with h | h` into its components or cases. Conclude with `hx m h`. Conclude with `hy m h`. Consider the case `smul c x _ hx`.

Introduce `m hm`. Conclude with `hx m (support_smul hm)`.
-/
theorem sw_dom (R : Type) [CommRing R] [IsDomain R] {r n : ℕ} (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ dualWeyl R r n ν) :
    ∀ m ∈ f.support, ∀ k : ℕ,
      (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ t : Fin n with t.val < k, ν t := by
  classical
  obtain ⟨b, hb, h2⟩ := sSBasis R r n ν
  rw [← hb.2.1] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨-, -, K, sz, hsz, I, hshape, -, hbm⟩ := h2 i
    intro m hm k
    rw [hbm] at hm
    have h := (bidetDominance R r n K sz hsz I m hm).1 k
    rw [hshape] at h
    exact h
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (support_smul hm)

/- English proof (translation)
Establish `hGp : IsWeightedHomogeneous (lehwP a) G ((∑ a' : Fin r with a'.val < a.val + 1, rowNu (r` using `r) ν a' : ℕ) : ℤ) := by`. Introduce `m hm`. Rewrite using `[lehw_weight_P]`. Establish `hm'` using `hGh hm`. Use `congr 1`.

Use `Finset.sum_congr rfl fun a' _ => ?_` and prove the remaining obligations. Rewrite using `[← lehw_weight_rowW, hm']`. Establish `hsh` using `lehw_rowDiv_shift R (lehwP a) 1 a b (highestWeightCount_self_eq_succ_of_lt hab) _ k G hGp`. Establish `hmem` using `rowDivStable R r n ν a b k G hG`. Assume the negation of the conclusion as `hne`.

Take `⟨m, hm⟩` from `ne_zero_iff.mp hne`. Establish `h1` using `hsh hm`. Rewrite `h1` using `[lehw_weight_P]`. Establish `h2` using `sw_dom R ν _ hmem m (mem_support_iff.mpr hm) (a.val + 1)`. Rewrite `h2` using `[← rowNuSum r n ν hn]`.

Establish `h3 : ((∑ a' : Fin r with a'.val < a.val + 1, rowDeg m a' : ℕ) : ℤ) ≤ ((∑ a' : Fin r with a'.val < a.val + 1, rowNu (r` using `r) ν a' : ℕ) : ℤ) := by exact_mod_cast h2`. Establish `hk' : (1 : ℤ) ≤ k` using `by exact_mod_cast hk`. Rewrite `h3` using `[h1]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sw_kill (R : Type) [CommRing R] [IsDomain R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (G : MvPolynomial (Fin r × Fin n) R) (hG : G ∈ dualWeyl R r n ν)
    (hGh : IsWeightedHomogeneous (rowW r n) G (rowNu (r := r) ν))
    (a b : Fin r) (hab : a < b) (k : ℕ) (hk : 1 ≤ k) : rowDiv R a b k G = 0 := by
  classical
  have hGp : IsWeightedHomogeneous (lehwP a) G
      ((∑ a' : Fin r with a'.val < a.val + 1, rowNu (r := r) ν a' : ℕ) : ℤ) := by
    intro m hm
    rw [lehw_weight_P]
    have hm' := hGh hm
    congr 1
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← lehw_weight_rowW, hm']
  have hsh := lehw_rowDiv_shift R (lehwP a) 1 a b (highestWeightCount_self_eq_succ_of_lt hab) _ k G hGp
  have hmem := rowDivStable R r n ν a b k G hG
  by_contra hne
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hne
  have h1 := hsh hm
  rw [lehw_weight_P] at h1
  have h2 := sw_dom R ν _ hmem m (mem_support_iff.mpr hm) (a.val + 1)
  rw [← rowNuSum r n ν hn] at h2
  have h3 : ((∑ a' : Fin r with a'.val < a.val + 1, rowDeg m a' : ℕ) : ℤ) ≤
      ((∑ a' : Fin r with a'.val < a.val + 1, rowNu (r := r) ν a' : ℕ) : ℤ) := by exact_mod_cast h2
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  rw [h1] at h3
  linarith

/- English proof (translation)
Unfold `hw`. Rewrite using `[map_prod]`. Use `Finset.prod_eq_one fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, eval_idPoint_lpMinor R (r := r) (n := n) (s.val + 1) (by omega) (by omega), one_pow]`.
-/
theorem sw_eval_hw (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    eval (idPoint R r n) (hw R hn ν) = 1 := by
  unfold hw
  rw [map_prod]
  refine Finset.prod_eq_one fun s _ => ?_
  rw [map_pow, eval_idPoint_lpMinor R (r := r) (n := n) (s.val + 1) (by omega) (by omega), one_pow]

/- English proof (translation)
Take `⟨c, hc⟩` from `hwLine K r n hn ν hν G hG (fun a b hab k hk => sw_kill K hn ν G hG hGh a b hab k hk)`. Establish `h1 : eval (idPoint K r n) G = c`. Rewrite using `[hc, smul_eq_C_mul, map_mul, eval_C, sw_eval_hw, mul_one]`. Rewrite using `[h1]`. Conclude with `hc`.
-/
theorem sw_line (K : Type) [Field K] [Infinite K] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν)
    (G : MvPolynomial (Fin r × Fin n) K) (hG : G ∈ dualWeyl K r n ν)
    (hGh : IsWeightedHomogeneous (rowW r n) G (rowNu (r := r) ν)) :
    G = eval (idPoint K r n) G • hw K hn ν := by
  obtain ⟨c, hc⟩ := hwLine K r n hn ν hν G hG (fun a b hab k hk => sw_kill K hn ν G hG hGh a b hab k hk)
  have h1 : eval (idPoint K r n) G = c := by
    rw [hc, smul_eq_C_mul, map_mul, eval_C, sw_eval_hw, mul_one]
  rw [h1]
  exact hc

/- English proof (translation)
Rewrite using `[rowGen, aeval_X]`. Unfold `lgraded_wa`. Use `split_ifs with h`. Take `⟨b, s⟩` from `v`. Simplify using `only at h`.

Substitute `h` using the available equality. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem sw_rowGen_X_self (R : Type) [CommRing R] {r n : ℕ} (a : Fin r) (v : Fin r × Fin n) :
    rowGen R a a (X v) = Polynomial.C (X v) * (1 + Polynomial.X) ^ (lgraded_wa (n := n) a v) := by
  rw [rowGen, aeval_X]
  unfold lgraded_wa
  split_ifs with h
  · obtain ⟨b, s⟩ := v
    simp only at h
    subst h
    ring
  · simp

/- English proof (translation)
Rewrite using `[monomial_eq, map_mul, Finsupp.prod, map_prod, sw_rowGen_C]`. Repeatedly rewrite using `[map_pow, sw_rowGen_X_self, mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]`. Rewrite using `[Finsupp.weight_apply, Finsupp.sum, map_mul, map_prod]`. Repeatedly rewrite using `[map_pow, smul_eq_mul, mul_comm (lgraded_wa a _)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sw_rowGen_monomial (R : Type) [CommRing R] {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : R) :
    rowGen R a a (monomial m c) =
      Polynomial.C (monomial m c) * (1 + Polynomial.X) ^ (Finsupp.weight (lgraded_wa a) m) := by
  rw [monomial_eq, map_mul, Finsupp.prod, map_prod, sw_rowGen_C]
  simp_rw [map_pow, sw_rowGen_X_self, mul_pow, Finset.prod_mul_distrib, ← pow_mul,
    Finset.prod_pow_eq_pow_sum]
  rw [Finsupp.weight_apply, Finsupp.sum, map_mul, map_prod]
  simp_rw [map_pow, smul_eq_mul, mul_comm (lgraded_wa a _)]
  ring

/- English proof (translation)
Rewrite using `[rowDiv, sw_rowGen_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow, Nat.choose_one_right, smul_eq_C_mul, mul_comm]`. Simplify using the standard rewrite rules.
-/
theorem sw_euler_monomial (R : Type) [CommRing R] {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : R) :
    rowDiv R a a 1 (monomial m c) = ((Finsupp.weight (lgraded_wa a) m : ℕ) : R) • monomial m c := by
  rw [rowDiv, sw_rowGen_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow,
    Nat.choose_one_right, smul_eq_C_mul, mul_comm]
  simp

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on' with`. Consider the case `monomial u c`. Rewrite using `[sw_euler_monomial, coeff_smul, coeff_monomial, smul_eq_mul]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Both sides reduce to the same expression. Simplify using the standard rewrite rules. Consider the case `add p q hp hq => rw [rowDiv_add, coeff_add, coeff_add, hp, hq, mul_add]`.
-/
theorem sw_coeff_euler (R : Type) [CommRing R] {r n : ℕ} (a : Fin r) (f : MvPolynomial (Fin r × Fin n) R)
    (m : Fin r × Fin n →₀ ℕ) :
    coeff m (rowDiv R a a 1 f) = ((Finsupp.weight (lgraded_wa a) m : ℕ) : R) * coeff m f := by
  induction f using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [sw_euler_monomial, coeff_smul, coeff_monomial, smul_eq_mul]
    split_ifs with h
    · subst h; rfl
    · simp
  | add p q hp hq => rw [rowDiv_add, coeff_add, coeff_add, hp, hq, mul_add]

/- English proof (translation)
Establish `h` using `sw_step_eq R a 0 f`. Simplify using `only [zero_add, Nat.cast_one, one_smul, Nat.cast_zero, zero_smul, sub_zero, sw_rowDiv_zero] at h`. Conclude with `h.symm`.
-/
theorem sw_Dop_self (R : Type) [CommRing R] {r n : ℕ} (a : Fin r) (f : MvPolynomial (Fin r × Fin n) R) :
    Dop R a a f = rowDiv R a a 1 f := by
  have h := sw_step_eq R a 0 f
  simp only [zero_add, Nat.cast_one, one_smul, Nat.cast_zero, zero_smul, sub_zero, sw_rowDiv_zero] at h
  exact h.symm

/- English proof (translation)
Establish `h` using `sw_step_ne R a b hab 0 f`. Simplify using `only [zero_add, Nat.cast_one, one_smul, sw_rowDiv_zero] at h`. Conclude with `h.symm`.
-/
theorem sw_Dop_ne (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (hab : a ≠ b)
    (f : MvPolynomial (Fin r × Fin n) R) : Dop R a b f = rowDiv R a b 1 f := by
  have h := sw_step_ne R a b hab 0 f
  simp only [zero_add, Nat.cast_one, one_smul, sw_rowDiv_zero] at h
  exact h.symm

/- English proof (translation)
Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Conclude with `sw_Dop_self R a f`. Conclude with `sw_Dop_ne R a b hab f`.
-/
theorem sw_Dop_rowDiv (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r)
    (f : MvPolynomial (Fin r × Fin n) R) : Dop R a b f = rowDiv R a b 1 f := by
  by_cases hab : a = b
  · subst hab; exact sw_Dop_self R a f
  · exact sw_Dop_ne R a b hab f

/- English proof (translation)
Rewrite using `[sw_Dop_self]`. Use extensionality with `m`. Rewrite using `[sw_coeff_euler, coeff_smul, smul_eq_mul]`. Distinguish the cases in `hm : coeff m f = 0`. Rewrite using `[hm, mul_zero, mul_zero]`.

Rewrite using `[← lgraded_weight_rowW, hf hm]`.
-/
theorem sw_euler (R : Type) [CommRing R] {r n : ℕ} (a : Fin r) (μ : Fin r → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous (rowW r n) f μ) :
    Dop R a a f = (μ a : R) • f := by
  rw [sw_Dop_self]
  ext m
  rw [sw_coeff_euler, coeff_smul, smul_eq_mul]
  by_cases hm : coeff m f = 0
  · rw [hm, mul_zero, mul_zero]
  · rw [← lgraded_weight_rowW, hf hm]

/- English proof (translation)
Unfold `bideterminant initMinor`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_det]`. Use `congr 1`.

Use extensionality with `p q`. Simplify using the standard rewrite rules.
-/
theorem sw_bidet_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    map φ (bideterminant R sz hsz I) = bideterminant S sz hsz I := by
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp

/- English proof (translation)
Unfold `weyl at hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨w, rfl⟩` from `hx`. Rewrite using `[← lclosedeq_applyWord_map, lclosedeq_hw_map]`.

Conclude with `Submodule.subset_span ⟨w, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul c x _ hx`. Rewrite using `[smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem sw_weyl_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ} (hn : n ≤ r)
    (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ weyl R r n hn ν) :
    map φ f ∈ weyl S r n hn ν := by
  unfold weyl at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]
    exact Submodule.subset_span ⟨w, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Apply `le_antisymm (weylLeDual K r n hn ν hν)` to reduce the goal to its premises. Take `⟨b, hb, h2⟩` from `sSBasis K r n ν`. Rewrite using `[← hb.2.1, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Take `⟨-, -, N, sz, hsz, I, hshape, -, hbm⟩` from `h2 i`.

Establish `h3 : bideterminant ℤ sz hsz I ∈ dualWeyl ℤ r n ν`. Use `bidetMem ℤ r n N sz hsz I` as an intermediate fact. Rewrite `this` using `[hshape]`. Then use the resulting hypothesis. Take `⟨c, hc, h4⟩` from `weylRational r n hn ν hν _ h3`. Establish `h5` using `sw_weyl_map (Int.castRingHom K) hn ν _ h4`.

Rewrite `h5` using `[zsmul_eq_mul, map_mul, map_intCast, sw_bidet_map, ← hbm]`. Establish `hcK : (c : K) ≠ 0` using `by exact_mod_cast hc`. Establish `h6 : b i = (c : K)⁻¹ • (((c : ℤ) : MvPolynomial (Fin r × Fin n) K) * b i)`. Rewrite using `[smul_eq_C_mul, ← mul_assoc]`. Establish `: (C (c : K)⁻¹ : MvPolynomial (Fin r × Fin n) K) * ((c : ℤ) : MvPolynomial (Fin r × Fin n) K) = 1`.

Rewrite using `[← map_intCast (C : K →+* MvPolynomial (Fin r × Fin n) K), ← map_mul, inv_mul_cancel₀ hcK, map_one]`. Rewrite using `[this, one_mul]`. Use `show b i ∈ weyl K r n hn ν`. Rewrite using `[h6]`. Conclude with `Submodule.smul_mem _ _ h5`.
-/
theorem sw_weyl_eq (K : Type) [Field K] [CharZero K] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    weyl K r n hn ν = dualWeyl K r n ν := by
  apply le_antisymm (weylLeDual K r n hn ν hν)
  obtain ⟨b, hb, h2⟩ := sSBasis K r n ν
  rw [← hb.2.1, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨-, -, N, sz, hsz, I, hshape, -, hbm⟩ := h2 i
  have h3 : bideterminant ℤ sz hsz I ∈ dualWeyl ℤ r n ν := by
    have := bidetMem ℤ r n N sz hsz I
    rwa [hshape] at this
  obtain ⟨c, hc, h4⟩ := weylRational r n hn ν hν _ h3
  have h5 := sw_weyl_map (Int.castRingHom K) hn ν _ h4
  rw [zsmul_eq_mul, map_mul, map_intCast, sw_bidet_map, ← hbm] at h5
  have hcK : (c : K) ≠ 0 := by exact_mod_cast hc
  have h6 : b i = (c : K)⁻¹ • (((c : ℤ) : MvPolynomial (Fin r × Fin n) K) * b i) := by
    rw [smul_eq_C_mul, ← mul_assoc]
    have : (C (c : K)⁻¹ : MvPolynomial (Fin r × Fin n) K) * ((c : ℤ) : MvPolynomial (Fin r × Fin n) K) = 1 := by
      rw [← map_intCast (C : K →+* MvPolynomial (Fin r × Fin n) K), ← map_mul, inv_mul_cancel₀ hcK, map_one]
    rw [this, one_mul]
  show b i ∈ weyl K r n hn ν
  rw [h6]
  exact Submodule.smul_mem _ _ h5

end Formalism.L2.G.Model
