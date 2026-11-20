import Mathlib
import ReciprocityTheory.DualLattices.WFrobStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ZmodPrimeSqLocal

noncomputable section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory.WFrob

variable {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {Tw : ATowerL R₀ p} {K : LAlg R₀}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ, ih]`. Use `push_cast`.

Take the linear combination `((n : A) + 1) * u ^ n * hv`.
-/
private lemma pow_add_sqz {A : Type*} [CommRing A] (u v : A) (hv : v * v = 0) (n : ℕ) :
    (u + v) ^ (n + 1) = u ^ (n + 1) + ((n : A) + 1) * u ^ n * v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination ((n : A) + 1) * u ^ n * hv

/- English proof (translation)
Establish `: (p : (wd.W : Type)) ∈ RingHom.ker wd.πW.1`. Rewrite using `[wd.ker_πW]`. Conclude with `Ideal.subset_span rfl`. Conclude with `this`.
-/
private lemma p_ker (wd : WData Tw K) : wd.πW.1 (p : (wd.W : Type)) = 0 := by
  have : (p : (wd.W : Type)) ∈ RingHom.ker wd.πW.1 := by
    rw [wd.ker_πW]; exact Ideal.subset_span rfl
  exact this

/- English proof (translation)
Rewrite using `[map_mul, p_ker, zero_mul]`.
-/
private lemma π_pmul (wd : WData Tw K) (x : (wd.W : Type)) : wd.πW.1 (p * x) = 0 := by
  rw [map_mul, p_ker, zero_mul]

/- English proof (translation)
Establish `h` using `wd.witt_add 0 Fin.elim0`. Rewrite `h` using `[Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_empty]`. Apply `wd.T_kill` to reduce the goal to its premises. Establish `h2` using `congrArg wd.πW.1 h`. Rewrite `h2` using `[map_zero, map_add, π_pmul, add_zero]`.

Conclude with `h2.symm`.
-/
private lemma T_zero (wd : WData Tw K) : wd.T 0 = 0 := by
  have h := wd.witt_add 0 Fin.elim0
  rw [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_empty] at h
  apply wd.T_kill
  have h2 := congrArg wd.πW.1 h
  rw [map_zero, map_add, π_pmul, add_zero] at h2
  exact h2.symm

/- English proof (translation)
Establish `h` using `wd.witt_add 2 ![a, b]`. Rewrite `h` using `[Fin.sum_univ_two, Fin.sum_univ_two]`. Establish `h2` using `congrArg wd.πW.1 h`. Rewrite `h2` using `[map_add, map_add, π_pmul, add_zero]`. Simplify using `using h2.symm`.
-/
private lemma πT_add (wd : WData Tw K) (a b : wd.Rb) :
    wd.πW.1 (wd.T (a + b)) = wd.πW.1 (wd.T a) + wd.πW.1 (wd.T b) := by
  have h := wd.witt_add 2 ![a, b]
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at h
  have h2 := congrArg wd.πW.1 h
  rw [map_add, map_add, π_pmul, add_zero] at h2
  simpa using h2.symm

private def φW (wd : WData Tw K) : wd.Rb →+* (Tw.R 0 : Type) where
  toFun c := wd.πW.1 (wd.T c)
  map_one' := by rw [map_one, map_one]
  map_mul' a b := by rw [map_mul, map_mul]
  map_zero' := by rw [T_zero, map_zero]
  map_add' := πT_add wd

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma φW_apply (wd : WData Tw K) (c : wd.Rb) : φW wd c = wd.πW.1 (wd.T c) := rfl

/- English proof (translation)
Use `(wd.ann_p (a - b)).2 (by rw [map_sub, h, sub_self])` as an intermediate fact. Rewrite `this` using `[mul_sub, sub_eq_zero]`. Conclude with `this`.
-/
private lemma pmul_congr (wd : WData Tw K) (a b : (wd.W : Type)) (h : wd.πW.1 a = wd.πW.1 b) :
    (p : (wd.W : Type)) * a = p * b := by
  have := (wd.ann_p (a - b)).2 (by rw [map_sub, h, sub_self])
  rw [mul_sub, sub_eq_zero] at this
  exact this

/- English proof (translation)
Take `⟨k, hk⟩ : ∃ k, p = k + 1` from `⟨p - 1, (Nat.sub_add_cancel (Fact.out : p.Prime).one_le).symm⟩`. Establish `hv : (p * s) * (p * s) = 0`. Establish `: (p : (wd.W : Type)) * p * (s * s) = 0` using `by rw [← sq, wd.p_sq, zero_mul]`. Take the linear combination `this`. Use `pow_add_sqz u (p * s) hv k` as an intermediate fact.

Rewrite `this` using `[← hk]`. Rewrite using `[this]`. Establish `hk' : ((k : (wd.W : Type)) + 1) = p`. Use `congrArg (Nat.cast : ℕ → (wd.W : Type)) hk` as an intermediate fact. Rewrite using `[this]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hk']`. Establish `: (p : (wd.W : Type)) * u ^ k * (p * s) = (p : (wd.W : Type)) ^ 2 * (u ^ k * s)` using `by ring`. Rewrite using `[this, wd.p_sq, zero_mul, add_zero]`.
-/
private lemma pow_p_teich (wd : WData Tw K) (u s : (wd.W : Type)) :
    (u + p * s) ^ p = u ^ p := by
  obtain ⟨k, hk⟩ : ∃ k, p = k + 1 := ⟨p - 1, (Nat.sub_add_cancel (Fact.out : p.Prime).one_le).symm⟩
  have hv : (p * s) * (p * s) = 0 := by
    have : (p : (wd.W : Type)) * p * (s * s) = 0 := by rw [← sq, wd.p_sq, zero_mul]
    linear_combination this
  have := pow_add_sqz u (p * s) hv k
  rw [← hk] at this
  rw [this]
  have hk' : ((k : (wd.W : Type)) + 1) = p := by
    have := congrArg (Nat.cast : ℕ → (wd.W : Type)) hk
    rw [this]; push_cast; ring
  rw [hk']
  have : (p : (wd.W : Type)) * u ^ k * (p * s) = (p : (wd.W : Type)) ^ 2 * (u ^ k * s) := by ring
  rw [this, wd.p_sq, zero_mul, add_zero]

/- English proof (translation)
Distinguish the cases in `h : ∃ i, ¬ p ∣ m i`. Take `⟨e, he⟩` from `Ideal.mem_span_singleton'.1 (hG m h)`. Conclude with `⟨0, e, by rw [T_zero, zero_add, ← he, mul_comm], Or.inl rfl⟩`. Take `⟨d, e, he⟩` from `wd.decomp (MvPolynomial.coeff m G)`. Use `⟨d, e, he, Or.inr fun i => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hi`. Conclude with `h ⟨i, hi⟩`.
-/
private lemma coeff_decomp (wd : WData Tw K) {g : ℕ} (G : MvPolynomial (Fin g) (wd.W : Type))
    (hG : ∀ m, (∃ i, ¬ p ∣ m i) →
      MvPolynomial.coeff m G ∈ Ideal.span {(p : (wd.W : Type))}) (m : Fin g →₀ ℕ) :
    ∃ d : wd.Rb, ∃ e : (wd.W : Type), MvPolynomial.coeff m G = wd.T d + p * e ∧
      (d = 0 ∨ ∀ i, p ∣ m i) := by
  by_cases h : ∃ i, ¬ p ∣ m i
  · obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (hG m h)
    exact ⟨0, e, by rw [T_zero, zero_add, ← he, mul_comm], Or.inl rfl⟩
  · obtain ⟨d, e, he⟩ := wd.decomp (MvPolynomial.coeff m G)
    refine ⟨d, e, he, Or.inr fun i => ?_⟩
    by_contra hi
    exact h ⟨i, hi⟩

/- English proof (translation)
Break down `hd with rfl | hd` into its components or cases. Rewrite using `[zero_mul, T_zero, zero_mul]`. Rewrite using `[map_mul, map_prod]`. Use `congr 1`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Take `⟨k, hk⟩` from `hd i`. Rewrite using `[map_pow, hk, pow_mul, pow_p_teich, ← pow_mul]`.
-/
private lemma teich_term (wd : WData Tw K) {g : ℕ} (m : Fin g →₀ ℕ) (d : wd.Rb)
    (hd : d = 0 ∨ ∀ i, p ∣ m i) (η : Fin g → wd.Rb) (s : Fin g → (wd.W : Type)) :
    wd.T d * ∏ i, (wd.T (η i) + p * s i) ^ m i = wd.T (d * ∏ i, η i ^ m i) := by
  rcases hd with rfl | hd
  · rw [zero_mul, T_zero, zero_mul]
  · rw [map_mul, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    obtain ⟨k, hk⟩ := hd i
    rw [map_pow, hk, pow_mul, pow_p_teich, ← pow_mul]

/- English proof (translation)
Break down `hd with rfl | hd` into its components or cases. Rewrite using `[zero_mul, map_zero, zero_mul]`. Rewrite using `[map_mul, map_prod]`. Use `congr 1`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[RingEquiv.symm_apply_eq, frobeniusEquiv_apply, frobenius_def, ← pow_mul, Nat.div_mul_cancel (hd i)]`.
-/
private lemma root_term (wd : WData Tw K) {g : ℕ} (m : Fin g →₀ ℕ) (d : wd.Rb)
    (hd : d = 0 ∨ ∀ i, p ∣ m i) (η : Fin g → wd.Rb) :
    (frobeniusEquiv wd.Rb p).symm (d * ∏ i, η i ^ m i) =
      (frobeniusEquiv wd.Rb p).symm d * ∏ i, η i ^ (m i / p) := by
  rcases hd with rfl | hd
  · rw [zero_mul, map_zero, zero_mul]
  · rw [map_mul, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [RingEquiv.symm_apply_eq, frobeniusEquiv_apply, frobenius_def, ← pow_mul,
      Nat.div_mul_cancel (hd i)]

/- English proof (translation)
Introduce `R₀ _ p _ Tw K wd g G hG`. Use `choose d e hde hd using coeff_decomp wd G hG`. Use `set n := G.support.card with hn`. Set `μ : Fin n → (Fin g →₀ ℕ)` to `fun j => (G.support.equivFin.symm j : Fin g →₀ ℕ)`. Establish `hsum : ∀ (f : (Fin g →₀ ℕ) → (wd.W : Type)), ∑ m ∈ G.support, f m = ∑ j, f (μ j)`.

Introduce `f`. Rewrite using `[← Finset.sum_coe_sort G.support f]`. Conclude with `(Equiv.sum_comp G.support.equivFin.symm (fun x => f x)).symm`. Use `⟨MvPolynomial.eval₂ (Int.castRingHom _) (fun j => MvPolynomial.C (φW wd ((frobeniusEquiv wd.Rb p).symm (d (μ j)))) * ∏ i, MvPolynomial.X i ^ (μ j i / p)) (wS p n) + ∑ j, MvPolynomial.C (wd.πW.1 (e (μ j))) * ∏ i, MvPolynomial.X i ^ (μ j i), ?_⟩` and prove the remaining obligations. Introduce `y hy a ha`.

Use `choose η s hy' using fun i => wd.decomp (y i)`. Establish `hπy : ∀ i, wd.πW.1 (y i) = φW wd (η i)` using `fun i => by`. Rewrite using `[hy' i, map_add, π_pmul, add_zero, φW_apply]`. Establish `hw` using `wd.witt_add n (fun j => d (μ j) * ∏ i, η i ^ μ j i)`. Establish `hev : MvPolynomial.eval y G = ∑ j, wd.T (d (μ j) * ∏ i, η i ^ μ j i) + p * ∑ j, e (μ j) * ∏ i, y i ^ μ j i`.

Rewrite using `[MvPolynomial.eval_eq', hsum, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hde, add_mul, ← teich_term wd (μ j) (d (μ j)) (hd _) η s, mul_assoc]`. Simplify using `only [← hy']`. Rewrite `hev` using `[hw, add_assoc, ← mul_add]`.

Establish `h0 : wd.T (∑ j, d (μ j) * ∏ i, η i ^ μ j i) = 0`. Apply `wd.T_kill` to reduce the goal to its premises. Establish `h1 : wd.πW.1 (MvPolynomial.eval y G) = 0`. Rewrite `hy` using `[← wd.ker_πW]`. Conclude with `hy`.

Rewrite `h1` using `[hev, map_add, π_pmul, add_zero]`. Conclude with `h1`. Rewrite using `[hev, h0, zero_add]`. Apply `pmul_congr` to reduce the goal to its premises. Rewrite using `[ha, map_add, map_add, ← φW_apply, MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left]`.

Use `congr 1`. Use `congr 1`. Conclude with `RingHom.ext_int _ _`. Use function extensionality and compare the values at `j`. Rewrite using `[Function.comp_apply, Function.comp_apply, root_term wd (μ j) (d (μ j)) (hd _) η]`.

Simplify using `only [map_mul, map_prod, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X, hπy]`. Simplify using `only [map_sum, map_mul, map_prod, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X]`.
-/
theorem wFrob :
    (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {Tw : ATowerL R₀ p} {K : LAlg R₀}
      (wd : WData Tw K) (g : ℕ), WFrobStatement wd g) := by
  intro R₀ _ p _ Tw K wd g G hG
  classical
  choose d e hde hd using coeff_decomp wd G hG
  set n := G.support.card with hn
  let μ : Fin n → (Fin g →₀ ℕ) := fun j => (G.support.equivFin.symm j : Fin g →₀ ℕ)
  have hsum : ∀ (f : (Fin g →₀ ℕ) → (wd.W : Type)), ∑ m ∈ G.support, f m = ∑ j, f (μ j) := by
    intro f
    rw [← Finset.sum_coe_sort G.support f]
    exact (Equiv.sum_comp G.support.equivFin.symm (fun x => f x)).symm
  refine ⟨MvPolynomial.eval₂ (Int.castRingHom _)
      (fun j => MvPolynomial.C (φW wd ((frobeniusEquiv wd.Rb p).symm (d (μ j)))) *
        ∏ i, MvPolynomial.X i ^ (μ j i / p)) (wS p n) +
      ∑ j, MvPolynomial.C (wd.πW.1 (e (μ j))) * ∏ i, MvPolynomial.X i ^ (μ j i), ?_⟩
  intro y hy a ha
  choose η s hy' using fun i => wd.decomp (y i)
  have hπy : ∀ i, wd.πW.1 (y i) = φW wd (η i) := fun i => by
    rw [hy' i, map_add, π_pmul, add_zero, φW_apply]
  have hw := wd.witt_add n (fun j => d (μ j) * ∏ i, η i ^ μ j i)
  have hev : MvPolynomial.eval y G = ∑ j, wd.T (d (μ j) * ∏ i, η i ^ μ j i) +
      p * ∑ j, e (μ j) * ∏ i, y i ^ μ j i := by
    rw [MvPolynomial.eval_eq', hsum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hde, add_mul, ← teich_term wd (μ j) (d (μ j)) (hd _) η s, mul_assoc]
    simp only [← hy']
  rw [hw, add_assoc, ← mul_add] at hev
  have h0 : wd.T (∑ j, d (μ j) * ∏ i, η i ^ μ j i) = 0 := by
    apply wd.T_kill
    have h1 : wd.πW.1 (MvPolynomial.eval y G) = 0 := by
      rw [← wd.ker_πW] at hy
      exact hy
    rw [hev, map_add, π_pmul, add_zero] at h1
    exact h1
  rw [hev, h0, zero_add]
  apply pmul_congr
  rw [ha, map_add, map_add, ← φW_apply, MvPolynomial.eval₂_comp_left,
    MvPolynomial.eval₂_comp_left]
  congr 1
  · congr 1
    · exact RingHom.ext_int _ _
    · funext j
      rw [Function.comp_apply, Function.comp_apply, root_term wd (μ j) (d (μ j)) (hd _) η]
      simp only [map_mul, map_prod, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X, hπy]
  · simp only [map_sum, map_mul, map_prod, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X]

/- English proof (translation)
The claim follows from `wFrob _ _`.
-/
example (p : ℕ) [Fact p.Prime] : WFrobStatement (GlobalTheory.WModel.wModel p) 1 := wFrob _ _

end GlobalTheory.WFrob
