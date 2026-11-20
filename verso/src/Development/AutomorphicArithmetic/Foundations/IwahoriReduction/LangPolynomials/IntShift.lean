import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

/- English proof (translation)
Use `set P : Polynomial R := H.trunc N with hP`. Use `set Q : Polynomial R := P.comp ((1 + Polynomial.X) ^ g - 1) with hQ`. Establish `h1 : (PowerSeries.X : PowerSeries R) ^ N ∣ H - (P : PowerSeries R)`. Rewrite using `[PowerSeries.X_pow_dvd_iff]`. Introduce `m hm`.

Simplify using `[hP, PowerSeries.coeff_trunc, hm]`. Establish `hX : sb (R` using `R) g PowerSeries.X = (1 + PowerSeries.X) ^ g - 1 := by`. Unfold `sb`. Rewrite using `[PowerSeries.substAlgHom_X]`. Establish `h2 : sb g (P : PowerSeries R) = (Q : PowerSeries R)`.

Rewrite using `[hQ]`. Generalize the expression as in `P = S`. Proceed by induction on `S using Polynomial.induction_on' with`. Consider the case `add f h hf hh => simp only [Polynomial.coe_add, map_add, hf, hh, Polynomial.add_comp]`. Consider the case `monomial n a`.

Establish `hC : sb g (PowerSeries.C a : PowerSeries R) = PowerSeries.C a` using `(sb (R := R) g).commutes a`. Rewrite using `[← Polynomial.C_mul_X_pow_eq_monomial]`. Simplify using `[hC, hX]`. Establish `h3 : (PowerSeries.X : PowerSeries R) ^ N ∣ sb g H - (Q : PowerSeries R)`. Take `⟨u, hu⟩` from `h1`.

Rewrite using `[← h2, ← map_sub, hu, map_mul, map_pow, hX]`. Use `Dvd.dvd.mul_right (pow_dvd_pow_of_dvd ?_ N) _` and prove the remaining obligations. Rewrite using `[PowerSeries.X_dvd_iff]`. Simplify using the standard rewrite rules. Establish `h4 : (Polynomial.X : Polynomial R) ^ N ∣ (sb g H).trunc N - Q`.

Rewrite using `[Polynomial.X_pow_dvd_iff]`. Introduce `m hm`. Use `PowerSeries.X_pow_dvd_iff.1 h3 m hm` as an intermediate fact. Simplify `this` using `[PowerSeries.coeff_trunc, hm]`. Take `⟨v, hv⟩` from `h4`.

Establish `hev : ∀ (F : PowerSeries R) (s : R), (F.trunc N).eval s = ∑ n ∈ Finset.range N, F.coeff n * s ^ n`. Introduce `F s`. Use `PowerSeries.eval₂_trunc_eq_sum_range s (RingHom.id R) N F` as an intermediate fact. Simplify using `using this`. Use `⟨v.eval t, ?_⟩` and prove the remaining obligations.

Establish `h5` using `congrArg (Polynomial.eval t) hv`. Rewrite `h5` using `[Polynomial.eval_sub, hev, hQ, Polynomial.eval_comp, hP, hev]`. Simplify using `only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_mul] at h5`. Take the linear combination `h5`.
-/
private theorem truncSub {R : Type} [CommRing R] (H : PowerSeries R) (g N : ℕ) (t : R) :
    ∃ y : R, ∑ n ∈ Finset.range N, (sb g H).coeff n * t ^ n =
      ∑ n ∈ Finset.range N, H.coeff n * ((1 + t) ^ g - 1) ^ n + t ^ N * y := by
  set P : Polynomial R := H.trunc N with hP
  set Q : Polynomial R := P.comp ((1 + Polynomial.X) ^ g - 1) with hQ
  have h1 : (PowerSeries.X : PowerSeries R) ^ N ∣ H - (P : PowerSeries R) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    simp [hP, PowerSeries.coeff_trunc, hm]
  have hX : sb (R := R) g PowerSeries.X = (1 + PowerSeries.X) ^ g - 1 := by
    unfold sb; rw [PowerSeries.substAlgHom_X]
  have h2 : sb g (P : PowerSeries R) = (Q : PowerSeries R) := by
    rw [hQ]
    generalize P = S
    induction S using Polynomial.induction_on' with
    | add f h hf hh => simp only [Polynomial.coe_add, map_add, hf, hh, Polynomial.add_comp]
    | monomial n a =>
      have hC : sb g (PowerSeries.C a : PowerSeries R) = PowerSeries.C a := (sb (R := R) g).commutes a
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp [hC, hX]
  have h3 : (PowerSeries.X : PowerSeries R) ^ N ∣ sb g H - (Q : PowerSeries R) := by
    obtain ⟨u, hu⟩ := h1
    rw [← h2, ← map_sub, hu, map_mul, map_pow, hX]
    refine Dvd.dvd.mul_right (pow_dvd_pow_of_dvd ?_ N) _
    rw [PowerSeries.X_dvd_iff]
    simp
  have h4 : (Polynomial.X : Polynomial R) ^ N ∣ (sb g H).trunc N - Q := by
    rw [Polynomial.X_pow_dvd_iff]
    intro m hm
    have := PowerSeries.X_pow_dvd_iff.1 h3 m hm
    simpa [PowerSeries.coeff_trunc, hm] using this
  obtain ⟨v, hv⟩ := h4
  have hev : ∀ (F : PowerSeries R) (s : R), (F.trunc N).eval s = ∑ n ∈ Finset.range N, F.coeff n * s ^ n := by
    intro F s
    have := PowerSeries.eval₂_trunc_eq_sum_range s (RingHom.id R) N F
    simpa using this
  refine ⟨v.eval t, ?_⟩
  have h5 := congrArg (Polynomial.eval t) hv
  rw [Polynomial.eval_sub, hev, hQ, Polynomial.eval_comp, hP, hev] at h5
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X,
    Polynomial.eval_mul] at h5
  linear_combination h5

/- English proof (translation)
Establish `h0 : ξ ≠ 0` using `hξ.ne_zero hq.ne'`. Establish `hmod : ∀ a : ℕ, ξ ^ (a % q) = ξ ^ a` using `fun a => by conv_rhs => rw [← Nat.mod_add_div a q, pow_add, pow_mul, hξ.pow_eq_one, one_pow, mul_one]`. Establish `h1 : ∀ m : ℕ, ξ ^ (q - (m * x) % q) * (ξ ^ j) ^ m = (ξ ^ j / ξ ^ x) ^ m`. Introduce `m`. Rewrite using `[pow_sub₀ _ h0 (Nat.mod_lt _ hq).le, hξ.pow_eq_one, hmod, div_pow, ← pow_mul ξ x m, mul_comm x m]`.

Clear the denominators using the available nonvanishing facts. Simplify using `only [h1]`. Use `split_ifs with h`. Establish `: ξ ^ j / ξ ^ x = 1` using `by rw [← hmod j, h, div_self (pow_ne_zero _ h0)]`. Simplify using `[this]`.

Establish `hne : ξ ^ j / ξ ^ x ≠ 1`. Introduce `e`. Rewrite `e` using `[div_eq_one_iff_eq (pow_ne_zero _ h0), ← hmod j]`. Conclude with `h (hξ.pow_inj (Nat.mod_lt _ hq) hx e)`. Establish `: (ξ ^ j / ξ ^ x) ^ q = 1`.

Rewrite using `[div_pow, ← pow_mul, ← pow_mul, mul_comm j, mul_comm x, pow_mul, pow_mul, hξ.pow_eq_one]`. Simplify using the standard rewrite rules. Rewrite using `[geom_sum_eq hne, this]`. Simplify using the standard rewrite rules.
-/
private theorem orth {K : Type} [Field K] (q : ℕ) (hq : 0 < q) (ξ : K) (hξ : IsPrimitiveRoot ξ q) (x j : ℕ) (hx : x < q) :
    ∑ m ∈ Finset.range q, ξ ^ (q - (m * x) % q) * (ξ ^ j) ^ m = if j % q = x then (q : K) else 0 := by
  have h0 : ξ ≠ 0 := hξ.ne_zero hq.ne'
  have hmod : ∀ a : ℕ, ξ ^ (a % q) = ξ ^ a := fun a => by
    conv_rhs => rw [← Nat.mod_add_div a q, pow_add, pow_mul, hξ.pow_eq_one, one_pow, mul_one]
  have h1 : ∀ m : ℕ, ξ ^ (q - (m * x) % q) * (ξ ^ j) ^ m = (ξ ^ j / ξ ^ x) ^ m := by
    intro m
    rw [pow_sub₀ _ h0 (Nat.mod_lt _ hq).le, hξ.pow_eq_one, hmod, div_pow, ← pow_mul ξ x m, mul_comm x m]
    field_simp
  simp only [h1]
  split_ifs with h
  · have : ξ ^ j / ξ ^ x = 1 := by rw [← hmod j, h, div_self (pow_ne_zero _ h0)]
    simp [this]
  · have hne : ξ ^ j / ξ ^ x ≠ 1 := by
      intro e
      rw [div_eq_one_iff_eq (pow_ne_zero _ h0), ← hmod j] at e
      exact h (hξ.pow_inj (Nat.mod_lt _ hq) hx e)
    have : (ξ ^ j / ξ ^ x) ^ q = 1 := by
      rw [div_pow, ← pow_mul, ← pow_mul, mul_comm j, mul_comm x, pow_mul, pow_mul, hξ.pow_eq_one]; simp
    rw [geom_sum_eq hne, this]; simp

private def OO (l : ℕ) [Fact l.Prime] : Subring (Qbar l) where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' ha hb := by
    simp only [Set.mem_setOf_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' ha hb := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' ha := by simpa using ha

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Take `⟨y, hy⟩` from `exists_add_pow_prime_pow_eq hp (z - 1) 1 r`. Establish `h1 : ‖((z : Qbar l) - 1) ^ l ^ r‖ ≤ ‖(l : Qbar l)‖`. Establish `e : (z - 1) ^ l ^ r = -((l : OO l) * ((z - 1) * y))`. Rewrite `hy` using `[sub_add_cancel, hz, one_pow]`.

Take the linear combination `-hy`. Establish `e2 : ((z : Qbar l) - 1) ^ l ^ r = -((l : Qbar l) * (((z - 1) * y : OO l) : Qbar l))`. Use `congrArg (OO l).subtype e` as an intermediate fact. Simplify using `using this`. Rewrite using `[e2, norm_neg, norm_mul]`.

Conclude with `mul_le_of_le_one_right (norm_nonneg _) ((z - 1) * y).2`. Establish `hl : ‖(l : Qbar l)‖ ≤ 1` using `IsUltrametricDist.norm_natCast_le_one _ _`. Rewrite using `[show 3 * r = r + 2 * r by ring, pow_add, pow_mul, norm_pow, norm_pow (l : Qbar l)]`. Conclude with `(pow_le_pow_left₀ (norm_nonneg _) h1 _).trans (pow_le_pow_of_le_one (norm_nonneg _) hl (Nat.lt_pow_self hp.one_lt).le)`.
-/
private theorem rootBd (l : ℕ) [Fact l.Prime] (r : ℕ) (z : OO l) (hz : z ^ l ^ r = 1) :
    ‖((z : Qbar l) - 1) ^ l ^ (3 * r)‖ ≤ ‖(l : Qbar l) ^ (2 * r)‖ := by
  have hp : l.Prime := Fact.out
  obtain ⟨y, hy⟩ := exists_add_pow_prime_pow_eq hp (z - 1) 1 r
  have h1 : ‖((z : Qbar l) - 1) ^ l ^ r‖ ≤ ‖(l : Qbar l)‖ := by
    have e : (z - 1) ^ l ^ r = -((l : OO l) * ((z - 1) * y)) := by
      rw [sub_add_cancel, hz, one_pow] at hy
      linear_combination -hy
    have e2 : ((z : Qbar l) - 1) ^ l ^ r = -((l : Qbar l) * (((z - 1) * y : OO l) : Qbar l)) := by
      have := congrArg (OO l).subtype e
      simpa using this
    rw [e2, norm_neg, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((z - 1) * y).2
  have hl : ‖(l : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
  rw [show 3 * r = r + 2 * r by ring, pow_add, pow_mul, norm_pow, norm_pow (l : Qbar l)]
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 _).trans
    (pow_le_pow_of_le_one (norm_nonneg _) hl (Nat.lt_pow_self hp.one_lt).le)

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Establish `hz1 : ‖z‖ ≤ 1`. Use `congrArg norm hz` as an intermediate fact. Rewrite `this` using `[norm_pow, norm_one]`. Conclude with `((pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_pos hp.pos r).ne').1 this).le`.

Set `z' : OO l` to `⟨z, hz1⟩`. Set `H' : PowerSeries (OO l)` to `PowerSeries.mk fun n => ⟨H.coeff n, hH n⟩`. Establish `hm : PowerSeries.map (OO l).subtype H' = H`. Use extensionality with `n`. Simplify using `[H']`.

Establish `hs : PowerSeries.map (OO l).subtype (sb g H') = sb g H`. Rewrite using `[← hm]`. Unfold `sb`. Rewrite using `[PowerSeries.coe_substAlgHom, PowerSeries.coe_substAlgHom]`. Use `Eq.trans (PowerSeries.map_subst (hasSubst_pow (R := OO l) g) (h := (OO l).subtype) H') ?_` and prove the remaining obligations.

Use `congr 1`. Express the relevant statement in the definitionally equal form `PowerSeries.map (OO l).subtype _ = _`. Simplify using the standard rewrite rules. Take `⟨y, hy⟩` from `truncSub H' g (l ^ (3 * r)) (z' - 1)`. Establish `h2` using `congrArg (OO l).subtype hy`.

Establish `h3 : tval (sb g H) (l ^ (3 * r)) z - tval H (l ^ (3 * r)) (z ^ g) = (z - 1) ^ l ^ (3 * r) * (y : Qbar l)`. Unfold `tval`. Rewrite using `[← hs, sub_eq_iff_eq_add']`. Simplify `h2` using `[H', z']`. Rewrite using `[h3, norm_mul]`.

Conclude with `(mul_le_of_le_one_right (norm_nonneg _) y.2).trans (rootBd l r z' (Subtype.ext hz))`.
-/
private theorem tvalShift (l : ℕ) [Fact l.Prime] (H : PowerSeries (Qbar l)) (hH : ∀ n, ‖H.coeff n‖ ≤ 1) (g r : ℕ)
    (z : Qbar l) (hz : z ^ l ^ r = 1) :
    ‖tval (sb g H) (l ^ (3 * r)) z - tval H (l ^ (3 * r)) (z ^ g)‖ ≤ ‖(l : Qbar l) ^ (2 * r)‖ := by
  have hp : l.Prime := Fact.out
  have hz1 : ‖z‖ ≤ 1 := by
    have := congrArg norm hz
    rw [norm_pow, norm_one] at this
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_pos hp.pos r).ne').1 this).le
  let z' : OO l := ⟨z, hz1⟩
  let H' : PowerSeries (OO l) := PowerSeries.mk fun n => ⟨H.coeff n, hH n⟩
  have hm : PowerSeries.map (OO l).subtype H' = H := by
    ext n; simp [H']
  have hs : PowerSeries.map (OO l).subtype (sb g H') = sb g H := by
    rw [← hm]
    unfold sb
    rw [PowerSeries.coe_substAlgHom, PowerSeries.coe_substAlgHom]
    refine Eq.trans (PowerSeries.map_subst (hasSubst_pow (R := OO l) g) (h := (OO l).subtype) H') ?_
    congr 1
    change PowerSeries.map (OO l).subtype _ = _
    simp
  obtain ⟨y, hy⟩ := truncSub H' g (l ^ (3 * r)) (z' - 1)
  have h2 := congrArg (OO l).subtype hy
  have h3 : tval (sb g H) (l ^ (3 * r)) z - tval H (l ^ (3 * r)) (z ^ g) = (z - 1) ^ l ^ (3 * r) * (y : Qbar l) := by
    unfold tval
    rw [← hs, sub_eq_iff_eq_add']
    simpa [H', z'] using h2
  rw [h3, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) y.2).trans (rootBd l r z' (Subtype.ext hz))

/- English proof (translation)
Set `S : Polynomial (OO l)` to `∑ n ∈ Finset.range N, Polynomial.C (⟨H.coeff n, hH n⟩ : OO l) * (Polynomial.X - 1) ^ n`. Use `⟨S.natDegree + 1, fun i => (OO l).subtype (S.coeff i), fun i => (S.coeff i).2, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.eval₂_eq_sum_range]`. Simplify using `[S, tval, Polynomial.eval₂_finset_sum, Polynomial.eval₂_pow]`.
-/
private theorem tvalExp (l : ℕ) [Fact l.Prime] (H : PowerSeries (Qbar l)) (hH : ∀ n, ‖H.coeff n‖ ≤ 1) (N : ℕ) :
    ∃ (M : ℕ) (a : ℕ → Qbar l), (∀ i, ‖a i‖ ≤ 1) ∧ ∀ z, tval H N z = ∑ i ∈ Finset.range M, a i * z ^ i := by
  let S : Polynomial (OO l) := ∑ n ∈ Finset.range N, Polynomial.C (⟨H.coeff n, hH n⟩ : OO l) * (Polynomial.X - 1) ^ n
  refine ⟨S.natDegree + 1, fun i => (OO l).subtype (S.coeff i), fun i => (S.coeff i).2, fun z => ?_⟩
  rw [← Polynomial.eval₂_eq_sum_range]
  simp [S, tval, Polynomial.eval₂_finset_sum, Polynomial.eval₂_pow]

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Establish `hq : 0 < l ^ r` using `pow_pos hp.pos r`. Establish `h1 : ∀ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ k) * ∑ m ∈ Finset.range (l ^ r), ξ ^ (l ^ r - (m * x) % l ^ r) * ∑ i ∈ Finset.range M, a i * ((ξ ^ m) ^ g) ^ i = ∑ i ∈ Finset.range M, if (g * i) % l ^ r = x then (l : Qbar l) ^ r * (a i …`. Introduce `x hx`. Establish `hx' : x < l ^ r` using `Finset.mem_range.1 (Finset.mem_filter.1 hx).1`.

Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h` using `orth (l ^ r) hq ξ hξ x (g * i) hx'`. Establish `e : ∑ m ∈ Finset.range (l ^ r), φ (x : ZMod l) * ((x : Qbar l) ^ k) * (ξ ^ (l ^ r - (m * x) % l ^ r) * (a i * ((ξ ^ m) ^ g) ^ i)) = (a i * (φ (x : ZMod l) * ((x : Qbar l) ^ k))) * ∑ m ∈ Finset.range (l ^ r), ξ ^ (l ^ r - (m * x) % l ^ r) * (ξ ^ (g * i)) ^ m`.

Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun m _ => by ring`. Rewrite using `[e, h]`. Use `split_ifs`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_congr rfl h1, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_ite_eq]`.

Use `split_ifs with h`. Both sides reduce to the same expression. Establish `: l ∣ (g * i) % l ^ r`. Assume the negation of the conclusion as `hc`. Conclude with `h (Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.mod_lt _ hq), hc⟩)`.

Rewrite using `[(ZMod.natCast_eq_zero_iff _ _).2 this, MulChar.map_zero]`. Simplify using the standard rewrite rules.
-/
private theorem sumJ (l : ℕ) [Fact l.Prime] (φ : DirichletCharacter (Qbar l) l) (k r : ℕ) (ξ : Qbar l)
    (hξ : IsPrimitiveRoot ξ (l ^ r)) (M g : ℕ) (a : ℕ → Qbar l) :
    ∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ k) *
      ∑ m ∈ Finset.range (l ^ r), ξ ^ (l ^ r - (m * x) % l ^ r) * ∑ i ∈ Finset.range M, a i * ((ξ ^ m) ^ g) ^ i =
    ∑ i ∈ Finset.range M, (l : Qbar l) ^ r * (a i *
      (φ (((g * i) % l ^ r : ℕ) : ZMod l) * ((((g * i) % l ^ r : ℕ) : Qbar l) ^ k))) := by
  have hp : l.Prime := Fact.out
  have hq : 0 < l ^ r := pow_pos hp.pos r
  have h1 : ∀ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ k) *
      ∑ m ∈ Finset.range (l ^ r), ξ ^ (l ^ r - (m * x) % l ^ r) * ∑ i ∈ Finset.range M, a i * ((ξ ^ m) ^ g) ^ i =
      ∑ i ∈ Finset.range M, if (g * i) % l ^ r = x then (l : Qbar l) ^ r * (a i * (φ (x : ZMod l) * ((x : Qbar l) ^ k))) else 0 := by
    intro x hx
    have hx' : x < l ^ r := Finset.mem_range.1 (Finset.mem_filter.1 hx).1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := orth (l ^ r) hq ξ hξ x (g * i) hx'
    have e : ∑ m ∈ Finset.range (l ^ r), φ (x : ZMod l) * ((x : Qbar l) ^ k) *
        (ξ ^ (l ^ r - (m * x) % l ^ r) * (a i * ((ξ ^ m) ^ g) ^ i)) = (a i * (φ (x : ZMod l) * ((x : Qbar l) ^ k))) *
        ∑ m ∈ Finset.range (l ^ r), ξ ^ (l ^ r - (m * x) % l ^ r) * (ξ ^ (g * i)) ^ m := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [e, h]
    split_ifs
    · push_cast; ring
    · simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · have : l ∣ (g * i) % l ^ r := by
      by_contra hc
      exact h (Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.mod_lt _ hq), hc⟩)
    rw [(ZMod.natCast_eq_zero_iff _ _).2 this, MulChar.map_zero]
    simp

/- English proof (translation)
Establish `h : g ^ k * ((1 * i) % l ^ r) ^ k ≡ ((g * i) % l ^ r) ^ k [MOD l ^ r]`. Rewrite using `[← mul_pow, one_mul]`. Conclude with `(((Nat.mod_modEq i _).mul_left g).trans (Nat.mod_modEq _ _).symm).pow k`. Take `⟨c, hc⟩` from `h.dvd`. Use `congrArg (Int.cast : ℤ → Qbar l) hc` as an intermediate fact.

Simplify using `only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_pow, Nat.cast_mul, Int.cast_pow] at this`. Rewrite using `[this, norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ _)`.
-/
private theorem modBd (l : ℕ) [Fact l.Prime] (k r g i : ℕ) :
    ‖((((g * i) % l ^ r : ℕ) : Qbar l) ^ k) - (g : Qbar l) ^ k * (((1 * i) % l ^ r : ℕ) : Qbar l) ^ k‖ ≤ ‖(l : Qbar l) ^ r‖ := by
  have h : g ^ k * ((1 * i) % l ^ r) ^ k ≡ ((g * i) % l ^ r) ^ k [MOD l ^ r] := by
    rw [← mul_pow, one_mul]
    exact (((Nat.mod_modEq i _).mul_left g).trans (Nat.mod_modEq _ _).symm).pow k
  obtain ⟨c, hc⟩ := h.dvd
  have := congrArg (Int.cast : ℤ → Qbar l) hc
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_pow, Nat.cast_mul, Int.cast_pow] at this
  rw [this, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ _)

/- English proof (translation)
Introduce `l _ H hH g hg φ k r ξ hr hξ`. Establish `hp : l.Prime` using `Fact.out`. Establish `hq : 0 < l ^ r` using `pow_pos hp.pos r`. Take `⟨M, a, ha, hM⟩` from `tvalExp l H hH (l ^ (3 * r))`. Establish `hξ1 : ‖ξ‖ ≤ 1`.

Use `congrArg norm hξ.pow_eq_one` as an intermediate fact. Rewrite `this` using `[norm_pow, norm_one]`. Conclude with `((pow_eq_one_iff_of_nonneg (norm_nonneg _) hq.ne').1 this).le`. Establish `hA` using `sumJ l φ k r ξ hξ M g a`. Establish `hB` using `sumJ l φ k r ξ hξ M 1 a`.

Simplify using `only [← hM, pow_one] at hA hB`. Establish `hn : ∀ x : ℕ, ‖(x : Qbar l) ^ k‖ ≤ 1` using `fun x => by`. Rewrite using `[norm_pow]`. Conclude with `pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)`. Establish `h1 : ‖intg φ k (sb g H) r ξ - ∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ k) * ∑ m ∈ Finset.range (l ^ r), ξ ^ (l ^ r - (m * x) % l ^ r) * tval H (l ^ (3 * r)) ((ξ ^ m) ^ g)‖ ≤ ‖(l : Qbar l) ^ (2 * r)‖`.

Unfold `intg mass`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun x _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_mul]`. Use `(mul_le_of_le_one_left (norm_nonneg _) (mul_le_one₀ (φ.norm_le_one _) (norm_nonneg _) (hn x))).trans ?_` and prove the remaining obligations.

Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun m _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_sub, norm_mul, norm_pow]`. Use `(mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hξ1)).trans ?_` and prove the remaining obligations. Conclude with `tvalShift l H hH g r _ (by rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow])`. Establish `hc : ∀ j : ℕ, ((j % l ^ r : ℕ) : ZMod l) = (j : ZMod l)` using `fun j => (ZMod.natCast_eq_natCast_iff _ _ _).2 ((Nat.mod_modEq j _).of_dvd (dvd_pow_self l (by omega)))`.

Rewrite `h1` using `[hA]`. Establish `h2 : intg φ k H r ξ = _` using `hB`. Unfold `Cg`. Rewrite using `[h2, ← sub_add_sub_cancel]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_` and prove the remaining obligations. Establish `e : (l : Qbar l) ^ r * (a i * (φ (((g * i) % l ^ r : ℕ) : ZMod l) * ((((g * i) % l ^ r : ℕ) : Qbar l) ^ k))) - φ (g : ZMod l) * (g : Qbar l) ^ k * ((l : Qbar l) ^ r * (a i * (φ (((1 * i) % l ^ r : ℕ) : ZMod l) * ((((1 * i) % l ^ r : ℕ) : Qbar l) ^ k)))) = (l : Qbar l) ^ r * ((a i …`. Rewrite using `[hc, hc, one_mul i, Nat.cast_mul g i, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, two_mul, pow_add, norm_mul, norm_mul, norm_mul, norm_mul]`. Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) (mul_le_one₀ (ha i) (norm_nonneg _) (φ.norm_le_one _))).trans (modBd l k r g i)`.
-/
theorem UpperTheory.Kd.C7.pIntShift :
    UpperTheory.Kd.C7.SIntShift := by
  intro l _ H hH g hg φ k r ξ hr hξ
  have hp : l.Prime := Fact.out
  have hq : 0 < l ^ r := pow_pos hp.pos r
  obtain ⟨M, a, ha, hM⟩ := tvalExp l H hH (l ^ (3 * r))
  have hξ1 : ‖ξ‖ ≤ 1 := by
    have := congrArg norm hξ.pow_eq_one
    rw [norm_pow, norm_one] at this
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hq.ne').1 this).le
  have hA := sumJ l φ k r ξ hξ M g a
  have hB := sumJ l φ k r ξ hξ M 1 a
  simp only [← hM, pow_one] at hA hB
  have hn : ∀ x : ℕ, ‖(x : Qbar l) ^ k‖ ≤ 1 := fun x => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)
  have h1 : ‖intg φ k (sb g H) r ξ - ∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x),
      φ (x : ZMod l) * ((x : Qbar l) ^ k) * ∑ m ∈ Finset.range (l ^ r), ξ ^ (l ^ r - (m * x) % l ^ r) *
        tval H (l ^ (3 * r)) ((ξ ^ m) ^ g)‖ ≤ ‖(l : Qbar l) ^ (2 * r)‖ := by
    unfold intg mass
    rw [← Finset.sum_sub_distrib]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun x _ => ?_
    rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (mul_le_one₀ (φ.norm_le_one _) (norm_nonneg _) (hn x))).trans ?_
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun m _ => ?_
    rw [← mul_sub, norm_mul, norm_pow]
    refine (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hξ1)).trans ?_
    exact tvalShift l H hH g r _ (by rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow])
  have hc : ∀ j : ℕ, ((j % l ^ r : ℕ) : ZMod l) = (j : ZMod l) := fun j =>
    (ZMod.natCast_eq_natCast_iff _ _ _).2 ((Nat.mod_modEq j _).of_dvd (dvd_pow_self l (by omega)))
  rw [hA] at h1
  have h2 : intg φ k H r ξ = _ := hB
  unfold Cg
  rw [h2, ← sub_add_sub_cancel]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
  have e : (l : Qbar l) ^ r * (a i * (φ (((g * i) % l ^ r : ℕ) : ZMod l) * ((((g * i) % l ^ r : ℕ) : Qbar l) ^ k))) -
      φ (g : ZMod l) * (g : Qbar l) ^ k * ((l : Qbar l) ^ r * (a i *
      (φ (((1 * i) % l ^ r : ℕ) : ZMod l) * ((((1 * i) % l ^ r : ℕ) : Qbar l) ^ k)))) =
      (l : Qbar l) ^ r * ((a i * φ ((g * i : ℕ) : ZMod l)) *
        (((((g * i) % l ^ r : ℕ) : Qbar l) ^ k) - (g : Qbar l) ^ k * (((1 * i) % l ^ r : ℕ) : Qbar l) ^ k)) := by
    rw [hc, hc, one_mul i, Nat.cast_mul g i, map_mul]
    ring
  rw [e, two_mul, pow_add, norm_mul, norm_mul, norm_mul, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact (mul_le_of_le_one_left (norm_nonneg _) (mul_le_one₀ (ha i) (norm_nonneg _) (φ.norm_le_one _))).trans (modBd l k r g i)
