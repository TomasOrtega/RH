import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.NsPoint
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.FtHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.OzTwoMulEqPow

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

namespace UpperTheory.V.Alg.M.GradedPrimePointLifting

section

variable {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ} {N : Fin k → Submodule B A}

private def InP (p : Ideal (rees N)) (i : Fin k) (n : ℕ) (t : A) : Prop :=
  ∃ q ∈ p, q.1 = MvPolynomial.monomial (Finsupp.single i n) t

/- English proof (translation)
Apply the tactic sequence `rw [lat, Finset.prod_eq_single i] <;> simp +contextual [Finsupp.single_apply, eq_comm]`.
-/
private theorem lat_single_pow (i : Fin k) (n : ℕ) : lat N (Finsupp.single i n) = N i ^ n := by
  rw [lat, Finset.prod_eq_single i] <;> simp +contextual [Finsupp.single_apply, eq_comm]

variable {p : Ideal (rees N)} {i : Fin k}

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, p.zero_mem, by simp⟩`.
-/
private theorem InP.zero (n : ℕ) : InP p i n 0 := ⟨0, p.zero_mem, by simp⟩

/- English proof (translation)
Take `⟨q, hq, e1⟩` from `ht`. Take `⟨q', hq', e2⟩` from `hu`. Conclude with `⟨q + q', p.add_mem hq hq', by rw [Subalgebra.coe_add, e1, e2, map_add]⟩`.
-/
private theorem InP.add {n : ℕ} {t u : A} (ht : InP p i n t) (hu : InP p i n u) : InP p i n (t + u) := by
  obtain ⟨q, hq, e1⟩ := ht
  obtain ⟨q', hq', e2⟩ := hu
  exact ⟨q + q', p.add_mem hq hq', by rw [Subalgebra.coe_add, e1, e2, map_add]⟩

/- English proof (translation)
Take `⟨q, hq, e1⟩` from `ht`. Use `⟨q * mono N (Finsupp.single i m) u ((lat_single_pow (N := N) i m).symm ▸ hu), p.mul_mem_right _ hq, ?_⟩` and prove the remaining obligations. Rewrite using `[Subalgebra.coe_mul, e1, Finsupp.single_add, ← MvPolynomial.monomial_mul]`. Both sides reduce to the same expression.
-/
private theorem InP.mul {n m : ℕ} {t u : A} (ht : InP p i n t) (hu : u ∈ N i ^ m) : InP p i (n + m) (t * u) := by
  obtain ⟨q, hq, e1⟩ := ht
  refine ⟨q * mono N (Finsupp.single i m) u ((lat_single_pow (N := N) i m).symm ▸ hu), p.mul_mem_right _ hq, ?_⟩
  rw [Subalgebra.coe_mul, e1, Finsupp.single_add, ← MvPolynomial.monomial_mul]
  rfl

/- English proof (translation)
Take `⟨q, hq, e1⟩` from `h`. Establish `: q = mono N (Finsupp.single i n) t ((lat_single_pow (N` using `N) i n).symm ▸ ht) * mono N (Finsupp.single i m) u ((lat_single_pow (N := N) i m).symm ▸ hu) := by`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Subalgebra.coe_mul, e1, Finsupp.single_add, ← MvPolynomial.monomial_mul]`. Both sides reduce to the same expression.

Rewrite `hq` using `[this]`. Conclude with `(hp.mem_or_mem hq).imp (fun h => ⟨_, h, rfl⟩) (fun h => ⟨_, h, rfl⟩)`.
-/
private theorem InP.of_mul (hp : p.IsPrime) {n m : ℕ} {t u : A} (ht : t ∈ N i ^ n) (hu : u ∈ N i ^ m)
    (h : InP p i (n + m) (t * u)) : InP p i n t ∨ InP p i m u := by
  obtain ⟨q, hq, e1⟩ := h
  have : q = mono N (Finsupp.single i n) t ((lat_single_pow (N := N) i n).symm ▸ ht) *
      mono N (Finsupp.single i m) u ((lat_single_pow (N := N) i m).symm ▸ hu) := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, e1, Finsupp.single_add, ← MvPolynomial.monomial_mul]
    rfl
  rw [this] at hq
  exact (hp.mem_or_mem hq).imp (fun h => ⟨_, h, rfl⟩) (fun h => ⟨_, h, rfl⟩)

/- English proof (translation)
Establish `e0 : (algebraMap B (rees N) b).1 = MvPolynomial.monomial (Finsupp.single i 0) (algebraMap B A b)`. Rewrite using `[Finsupp.single_zero, Subalgebra.coe_algebraMap, MvPolynomial.algebraMap_apply]`. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q, hq, e1⟩`.

Rewrite using `[show algebraMap B (rees N) b = q from Subtype.ext (e0.trans e1.symm)]` and apply the resulting hypothesis. Conclude with `fun h => ⟨_, h, e0⟩`.
-/
private theorem inP_zero_iff (b : B) : InP p i 0 (algebraMap B A b) ↔ algebraMap B (rees N) b ∈ p := by
  have e0 : (algebraMap B (rees N) b).1 = MvPolynomial.monomial (Finsupp.single i 0) (algebraMap B A b) := by
    rw [Finsupp.single_zero, Subalgebra.coe_algebraMap, MvPolynomial.algebraMap_apply]
    rfl
  constructor
  · rintro ⟨q, hq, e1⟩
    rwa [show algebraMap B (rees N) b = q from Subtype.ext (e0.trans e1.symm)]
  · exact fun h => ⟨_, h, e0⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa [inP_zero_iff] using hb`. Consider the case `succ n ih`. Introduce `h1`. Rewrite `h1` using `[pow_succ, ← mul_assoc]`.

Use `(InP.of_mul hp ?_ (by rwa [pow_one]) h1).elim ih h` and prove the remaining obligations. Rewrite using `[← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ _ (Submodule.pow_mem_pow _ hf n)`.
-/
private theorem not_inP_pow (hp : p.IsPrime) {f : A} (hf : f ∈ N i) (h : ¬ InP p i 1 f) {b : B}
    (hb : algebraMap B (rees N) b ∉ p) (n : ℕ) : ¬ InP p i n (algebraMap B A b * f ^ n) := by
  induction n with
  | zero => simpa [inP_zero_iff] using hb
  | succ n ih =>
    intro h1
    rw [pow_succ, ← mul_assoc] at h1
    refine (InP.of_mul hp ?_ (by rwa [pow_one]) h1).elim ih h
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.pow_mem_pow _ hf n)

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Apply `h` to reduce the goal to its premises. Use `le_trans (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ i))) (Ideal.span_le.2 fun q hq => ?_)` and prove the remaining obligations. Take `⟨q', hq', e1⟩` from `hc _ (lat_single N i ▸ q.2 (Finsupp.single i 1))`.

Establish `he : e i = toDeg (Finsupp.single i 1)`. Use function extensionality and compare the values at `j`. Simplify using `[e, toDeg, Pi.single_apply, Finsupp.single_apply, eq_comm]`. Establish `: q = q'`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[e1]`. Use extensionality with `m`. Rewrite using `[MvPolynomial.coeff_monomial]`. Use `split_ifs with hm`. Rewrite using `[hm]`.

Conclude with `hq m fun h2 => hm (toDeg_injective (he.symm.trans h2.symm))`. Rewrite using `[this]`. Conclude with `hq'`.
-/
private theorem exists_not_inP (h : ¬ Irr (reesGr N) ≤ p) (i : Fin k) : ∃ f ∈ N i, ¬ InP p i 1 f := by
  classical
  by_contra hc
  push Not at hc
  apply h
  refine le_trans (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ i))) (Ideal.span_le.2 fun q hq => ?_)
  obtain ⟨q', hq', e1⟩ := hc _ (lat_single N i ▸ q.2 (Finsupp.single i 1))
  have he : e i = toDeg (Finsupp.single i 1) := by
    funext j; simp [e, toDeg, Pi.single_apply, Finsupp.single_apply, eq_comm]
  have : q = q' := by
    apply Subtype.ext
    rw [e1]
    ext m
    rw [MvPolynomial.coeff_monomial]
    split_ifs with hm
    · rw [hm]
    · exact hq m fun h2 => hm (toDeg_injective (he.symm.trans h2.symm))
  rw [this]
  exact hq'

end

section

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {𝒜 : ℤ → Submodule O A} [GradedAlgebra 𝒜]
  {k : ℕ} {N : Fin k → Submodule (𝒜 0) A}

private def idJ (p : Ideal (rees N)) (i : Fin k) : Ideal A where
  carrier := {t | ∀ (h : A) (n : ℕ), InP p i (n + 1) (DirectSum.decompose 𝒜 (h * t) (2 * ((n + 1 : ℕ) : ℤ)) : A)}
  add_mem' {a b} ha hb h n := by
    rw [mul_add, DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
    exact (ha h n).add (hb h n)
  zero_mem' h n := by
    rw [mul_zero, DirectSum.decompose_zero]
    exact InP.zero _
  smul_mem' c t ht h n := by
    rw [smul_eq_mul, ← mul_assoc]
    exact ht _ n

variable {p : Ideal (rees N)} {i : Fin k}

/- English proof (translation)
Introduce `h n`. Use `DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (a := h) (i := 2 * ((n + 1 : ℕ) : ℤ) - j) ht` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Rewrite using `[this]`. Conclude with `H n _ (Subtype.property _)`.
-/
private theorem mem_idJ {j : ℤ} {t : A} (ht : t ∈ 𝒜 j)
    (H : ∀ (n : ℕ), ∀ h ∈ 𝒜 (2 * ((n + 1 : ℕ) : ℤ) - j), InP p i (n + 1) (h * t)) : t ∈ idJ p i := by
  intro h n
  have := DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (a := h) (i := 2 * ((n + 1 : ℕ) : ℤ) - j) ht
  rw [sub_add_cancel] at this
  rw [this]
  exact H n _ (Subtype.property _)

/- English proof (translation)
The claim follows from `h ▸ SetLike.GradedMul.mul_mem ht hu`.
-/
private theorem mul_mem' {a b c : ℤ} {t u : A} (ht : t ∈ 𝒜 a) (hu : u ∈ 𝒜 b) (h : a + b = c) : t * u ∈ 𝒜 c :=
  h ▸ SetLike.GradedMul.mul_mem ht hu

/- English proof (translation)
Establish `h2 : oz 𝒜 2 = N i` using `by simpa using hpos 1`. Establish `L1 : ∀ c ∈ 𝒜 (-2), ∀ u ∈ 𝒜 (2 * ((m + 1 : ℕ) : ℤ)), InP p i m (c * u)`. Introduce `c hc u hu`. Rewrite `hu` using `[← mem_oz, hpos, pow_succ]`. Use `Submodule.mul_induction_on hu (fun v hv w hw => ?_) (fun v w hv hw => ?_)` and prove the remaining obligations.

Rewrite `hw` using `[← h2, mem_oz]`. Establish `h0 : InP p i 0 (algebraMap (𝒜 0) A ⟨c * w, mul_mem' hc hw (by norm_num)⟩)` using `(inP_zero_iff _).2 (hD (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨c, hc, w, hw, rfl⟩)))`. Establish `h1` using `h0.mul hv`. Rewrite `h1` using `[zero_add]`. Establish `e1 : c * (v * w) = c * w * v` using `by ring`.

Rewrite using `[e1]`. Conclude with `h1`. Rewrite using `[mul_add]`. Conclude with `hv.add hw`. Rewrite `ha` using `[← mem_oz, hneg, pow_succ, ← hneg]`.

Use `Submodule.mul_induction_on ha (fun v hv w hw => ?_) (fun v w hv hw => ?_)` and prove the remaining obligations. Establish `e1 : v * w * b = w * (v * b)` using `by ring`. Rewrite using `[e1]`. Conclude with `L1 w hw _ (mul_mem' hv hb (by push_cast; ring))`. Rewrite using `[add_mul]`.

Conclude with `hv.add hw`.
-/
private theorem inP_neg (hpos : ∀ n : ℕ, oz 𝒜 (2 * n) = N i ^ n) (hneg : ∀ n : ℕ, oz 𝒜 (-(2 * n)) = oz 𝒜 (-2) ^ n)
    (hD : (idD 𝒜).map (algebraMap (𝒜 0) (rees N)) ≤ p) (l m : ℕ) {a b : A} (ha : a ∈ 𝒜 (-(2 * ((l + 1 : ℕ) : ℤ))))
    (hb : b ∈ 𝒜 (2 * ((m + l + 1 : ℕ) : ℤ))) : InP p i m (a * b) := by
  have h2 : oz 𝒜 2 = N i := by simpa using hpos 1
  have L1 : ∀ c ∈ 𝒜 (-2), ∀ u ∈ 𝒜 (2 * ((m + 1 : ℕ) : ℤ)), InP p i m (c * u) := by
    intro c hc u hu
    rw [← mem_oz, hpos, pow_succ] at hu
    refine Submodule.mul_induction_on hu (fun v hv w hw => ?_) (fun v w hv hw => ?_)
    · rw [← h2, mem_oz] at hw
      have h0 : InP p i 0 (algebraMap (𝒜 0) A ⟨c * w, mul_mem' hc hw (by norm_num)⟩) :=
        (inP_zero_iff _).2 (hD (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨c, hc, w, hw, rfl⟩)))
      have h1 := h0.mul hv
      rw [zero_add] at h1
      have e1 : c * (v * w) = c * w * v := by ring
      rw [e1]
      exact h1
    · rw [mul_add]; exact hv.add hw
  rw [← mem_oz, hneg, pow_succ, ← hneg] at ha
  refine Submodule.mul_induction_on ha (fun v hv w hw => ?_) (fun v w hv hw => ?_)
  · have e1 : v * w * b = w * (v * b) := by ring
    rw [e1]
    exact L1 w hw _ (mul_mem' hv hb (by push_cast; ring))
  · rw [add_mul]; exact hv.add hw

/- English proof (translation)
Use `mem_idJ hg fun n h hh => ?_` and prove the remaining obligations. Take `⟨l, rfl⟩ : ∃ l : ℕ, j = -((l + 1 : ℕ) : ℤ)` from `⟨(-j - 1).toNat, by omega⟩`. Establish `hm : h * g ∈ N i ^ (n + 1)`. Rewrite using `[← hpos, mem_oz]; exact mul_mem' hh hg (by ring)`. Use `(InP.of_mul hp hm hm ?_).elim id id` and prove the remaining obligations.

Establish `e1 : h * g * (h * g) = (g * g) * (h * h)` using `by ring`. Rewrite using `[e1]`. Conclude with `inP_neg hpos hneg hD l _ (mul_mem' hg hg (by ring)) (mul_mem' hh hh (by push_cast; ring))`.
-/
private theorem neg_mem_idJ (hp : p.IsPrime) (hpos : ∀ n : ℕ, oz 𝒜 (2 * n) = N i ^ n)
    (hneg : ∀ n : ℕ, oz 𝒜 (-(2 * n)) = oz 𝒜 (-2) ^ n)
    (hD : (idD 𝒜).map (algebraMap (𝒜 0) (rees N)) ≤ p) {j : ℤ} (hj : j < 0) {g : A} (hg : g ∈ 𝒜 j) :
    g ∈ idJ p i := by
  refine mem_idJ hg fun n h hh => ?_
  obtain ⟨l, rfl⟩ : ∃ l : ℕ, j = -((l + 1 : ℕ) : ℤ) := ⟨(-j - 1).toNat, by omega⟩
  have hm : h * g ∈ N i ^ (n + 1) := by
    rw [← hpos, mem_oz]; exact mul_mem' hh hg (by ring)
  refine (InP.of_mul hp hm hm ?_).elim id id
  have e1 : h * g * (h * g) = (g * g) * (h * h) := by ring
  rw [e1]
  exact inP_neg hpos hneg hD l _ (mul_mem' hg hg (by ring)) (mul_mem' hh hh (by push_cast; ring))

/- English proof (translation)
Use `mem_idJ hg fun n h hh => ?_` and prove the remaining obligations. Establish `hm : h ∈ N i ^ n`. Rewrite using `[← hpos, mem_oz]`. Use `hh using 2` and compare the differences between its conclusion and the goal. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mul_comm, add_comm]`. Conclude with `H.mul hm`.
-/
private theorem two_mem_idJ (hpos : ∀ n : ℕ, oz 𝒜 (2 * n) = N i ^ n) {g : A} (hg : g ∈ 𝒜 2) (H : InP p i 1 g) :
    g ∈ idJ p i := by
  refine mem_idJ hg fun n h hh => ?_
  have hm : h ∈ N i ^ n := by
    rw [← hpos, mem_oz]; convert hh using 2; push_cast; ring
  rw [mul_comm, add_comm]
  exact H.mul hm

/- English proof (translation)
Use `mem_idJ hg fun n h hh => ?_` and prove the remaining obligations. Establish `hm : h * g ∈ N i ^ (n + 1)`. Rewrite using `[← hpos, mem_oz]; exact mul_mem' hh hg (by ring)`. Use `(InP.of_mul hp hm hm ?_).elim id id` and prove the remaining obligations. Establish `h2 : h * h ∈ N i ^ (2 * n + 1)`.

Rewrite using `[← hpos, mem_oz]; exact mul_mem' hh hh (by push_cast; ring)`. Establish `e1 : h * g * (h * g) = g ^ 2 * (h * h)` using `by ring`. Establish `e2 : n + 1 + (n + 1) = 1 + (2 * n + 1)` using `by ring`. Rewrite using `[e1, e2]`. Conclude with `H.mul h2`.
-/
private theorem one_mem_idJ (hp : p.IsPrime) (hpos : ∀ n : ℕ, oz 𝒜 (2 * n) = N i ^ n) {g : A} (hg : g ∈ 𝒜 1)
    (H : InP p i 1 (g ^ 2)) : g ∈ idJ p i := by
  refine mem_idJ hg fun n h hh => ?_
  have hm : h * g ∈ N i ^ (n + 1) := by
    rw [← hpos, mem_oz]; exact mul_mem' hh hg (by ring)
  refine (InP.of_mul hp hm hm ?_).elim id id
  have h2 : h * h ∈ N i ^ (2 * n + 1) := by
    rw [← hpos, mem_oz]; exact mul_mem' hh hh (by push_cast; ring)
  have e1 : h * g * (h * g) = g ^ 2 * (h * h) := by ring
  have e2 : n + 1 + (n + 1) = 1 + (2 * n + 1) := by ring
  rw [e1, e2]
  exact H.mul h2

/- English proof (translation)
Use `mem_idJ (j := 0) b.2 fun n h hh => ?_` and prove the remaining obligations. Establish `hm : h ∈ N i ^ (n + 1)`. Rewrite using `[← hpos, mem_oz]`. Rewrite `hh` using `[sub_zero]`. Then use the resulting hypothesis. Use `((inP_zero_iff b).2 H).mul hm` as an intermediate fact.

Rewrite `this` using `[zero_add, mul_comm]`. Then use the resulting hypothesis.
-/
private theorem zero_mem_idJ (hpos : ∀ n : ℕ, oz 𝒜 (2 * n) = N i ^ n) {b : 𝒜 0}
    (H : algebraMap (𝒜 0) (rees N) b ∈ p) : algebraMap (𝒜 0) A b ∈ idJ p i := by
  refine mem_idJ (j := 0) b.2 fun n h hh => ?_
  have hm : h ∈ N i ^ (n + 1) := by
    rw [← hpos, mem_oz]; rwa [sub_zero] at hh
  have := ((inP_zero_iff b).2 H).mul hm
  rwa [zero_add, mul_comm] at this

/- English proof (translation)
Introduce `H`. Apply `not_inP_pow hp hf h hb (n + 1)` to reduce the goal to its premises. Establish `h1` using `H f n`. Establish `e1 : f * (algebraMap (𝒜 0) A b * f ^ n) = algebraMap (𝒜 0) A b * f ^ (n + 1)` using `by ring`. Establish `hm : algebraMap (𝒜 0) A b * f ^ (n + 1) ∈ 𝒜 (2 * ((n + 1 : ℕ) : ℤ))`.

Rewrite using `[← mem_oz, hpos, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ _ (Submodule.pow_mem_pow _ hf _)`. Rewrite `h1` using `[e1, DirectSum.decompose_of_mem_same 𝒜 hm]`. Then use the resulting hypothesis.
-/
private theorem not_mem_idJ (hp : p.IsPrime) (hpos : ∀ n : ℕ, oz 𝒜 (2 * n) = N i ^ n) {f : A} (hf : f ∈ N i)
    (h : ¬ InP p i 1 f) {b : 𝒜 0} (hb : algebraMap (𝒜 0) (rees N) b ∉ p) (n : ℕ) :
    algebraMap (𝒜 0) A b * f ^ n ∉ idJ p i := by
  intro H
  apply not_inP_pow hp hf h hb (n + 1)
  have h1 := H f n
  have e1 : f * (algebraMap (𝒜 0) A b * f ^ n) = algebraMap (𝒜 0) A b * f ^ (n + 1) := by ring
  have hm : algebraMap (𝒜 0) A b * f ^ (n + 1) ∈ 𝒜 (2 * ((n + 1 : ℕ) : ℤ)) := by
    rw [← mem_oz, hpos, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.pow_mem_pow _ hf _)
  rwa [e1, DirectSum.decompose_of_mem_same 𝒜 hm] at h1

end

end UpperTheory.V.Alg.M.GradedPrimePointLifting

open UpperTheory.V.Alg.M.GradedPrimePointLifting in
/- English proof (translation)
Introduce `O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q p hp hI hs hZ hD σ hσ`. Establish `hpos : ∀ n : ℕ, oz 𝒜 (2 * n) = mN 𝒜 (Q.F (Fin.last r)) 1 ^ n` using `fun n => (oz_two_mul_eq_pow O A 𝒜 x hW n).2`. Establish `hneg : ∀ n : ℕ, oz 𝒜 (-(2 * n)) = oz 𝒜 (-2) ^ n` using `fun n => (oz_two_mul_eq_pow O A 𝒜 x hW n).1`. Establish `hk : ∀ b, σ b = 0 ↔ algebraMap (𝒜 0) (mR Q) b ∈ p` using `fun b => by`. Rewrite using `[← RingHom.mem_ker, hσ, Ideal.mem_comap]`.

Take `⟨f, hf, hfp⟩` from `exists_not_inP hI 1`. Use `haveI := (ft_holds O A 𝒜 x hW).1`. Take `⟨ξ, h0, hJ, hξ⟩` from `ns_holds O (𝒜 0) A K σ (idJ p 1) f (fun b hb => zero_mem_idJ hpos ((hk b).1 hb)) (fun b n hb => not_mem_idJ hp hpos hf hfp (fun h => hb ((hk b).2 h)) n)`. Establish `hN : NegZero 𝒜 ξ` using `fun j hj g hg => hJ _ (neg_mem_idJ hp hpos hneg hD hj hg)`. Use `⟨ξ, ?_, hN, fun h => hξ (h 2 (by norm_num) f hf), AlgHom.ext fun b => h0 b⟩` and prove the remaining obligations.

Introduce `g hg`. Use `(Ideal.span_le.2 ?_ : Q.ideal ≤ RingHom.ker ξ) hg` and prove the remaining obligations. Introduce and unpack `_ ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)`. Conclude with `hN _ (by norm_num) _ (Q.hF i)`. Conclude with `hN _ (by norm_num) _ (Q.hG i)`.

Use `hJ _ (one_mem_idJ hp hpos (Q.hE i) ⟨sec _ 1 (Q.E i ^ 2) (sq_mem_pos 𝒜 (Q.hE i)), hs (Ideal.subset_span ⟨e 1, ?_⟩), rfl⟩)` and prove the remaining obligations. Simplify using `only [ts, tsR, List.mem_append, List.mem_ofFn]`. Conclude with `Or.inr (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)))`. Use `hJ _ (two_mem_idJ hpos (Q.hE' i) ⟨sec _ 1 (Q.E' i) (Q.hE' i), hs (Ideal.subset_span ⟨e 1, ?_⟩), rfl⟩)` and prove the remaining obligations. Simplify using `only [ts, tsR, List.mem_append, List.mem_ofFn]`.

Conclude with `Or.inr (Or.inl (Or.inr ⟨i, rfl⟩))`. Conclude with `hJ _ (zero_mem_idJ hpos (hZ i))`.
-/
theorem UpperTheory.V.Alg.M.zp_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ p : Ideal (mR Q), p.IsPrime → ¬ Irr (mGr Q) ≤ p → secs (ts Q) ≤ p → (∀ i, algebraMap (𝒜 0) (mR Q) ⟨Q.Z i, (Q.hZ i).1⟩ ∈ p) →
      (idD 𝒜).map (algebraMap (𝒜 0) (mR Q)) ≤ p → ∀ σ : 𝒜 0 →ₐ[O] K, RingHom.ker σ = p.comap (algebraMap (𝒜 0) (mR Q)) →
      ∃ ξ : A →ₐ[O] K, OnS Q.ideal ξ ∧ NegZero 𝒜 ξ ∧ ¬ PosZero 𝒜 ξ ∧ res0 𝒜 ξ = σ := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q p hp hI hs hZ hD σ hσ
  have hpos : ∀ n : ℕ, oz 𝒜 (2 * n) = mN 𝒜 (Q.F (Fin.last r)) 1 ^ n := fun n => (oz_two_mul_eq_pow O A 𝒜 x hW n).2
  have hneg : ∀ n : ℕ, oz 𝒜 (-(2 * n)) = oz 𝒜 (-2) ^ n := fun n => (oz_two_mul_eq_pow O A 𝒜 x hW n).1
  have hk : ∀ b, σ b = 0 ↔ algebraMap (𝒜 0) (mR Q) b ∈ p := fun b => by
    rw [← RingHom.mem_ker, hσ, Ideal.mem_comap]
  obtain ⟨f, hf, hfp⟩ := exists_not_inP hI 1
  haveI := (ft_holds O A 𝒜 x hW).1
  obtain ⟨ξ, h0, hJ, hξ⟩ := ns_holds O (𝒜 0) A K σ (idJ p 1) f (fun b hb => zero_mem_idJ hpos ((hk b).1 hb))
    (fun b n hb => not_mem_idJ hp hpos hf hfp (fun h => hb ((hk b).2 h)) n)
  have hN : NegZero 𝒜 ξ := fun j hj g hg => hJ _ (neg_mem_idJ hp hpos hneg hD hj hg)
  refine ⟨ξ, ?_, hN, fun h => hξ (h 2 (by norm_num) f hf), AlgHom.ext fun b => h0 b⟩
  intro g hg
  refine (Ideal.span_le.2 ?_ : Q.ideal ≤ RingHom.ker ξ) hg
  rintro _ ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
  · exact hN _ (by norm_num) _ (Q.hF i)
  · exact hN _ (by norm_num) _ (Q.hG i)
  · refine hJ _ (one_mem_idJ hp hpos (Q.hE i)
      ⟨sec _ 1 (Q.E i ^ 2) (sq_mem_pos 𝒜 (Q.hE i)), hs (Ideal.subset_span ⟨e 1, ?_⟩), rfl⟩)
    simp only [ts, tsR, List.mem_append, List.mem_ofFn]
    exact Or.inr (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)))
  · refine hJ _ (two_mem_idJ hpos (Q.hE' i)
      ⟨sec _ 1 (Q.E' i) (Q.hE' i), hs (Ideal.subset_span ⟨e 1, ?_⟩), rfl⟩)
    simp only [ts, tsR, List.mem_append, List.mem_ofFn]
    exact Or.inr (Or.inl (Or.inr ⟨i, rfl⟩))
  · exact hJ _ (zero_mem_idJ hpos (hZ i))
