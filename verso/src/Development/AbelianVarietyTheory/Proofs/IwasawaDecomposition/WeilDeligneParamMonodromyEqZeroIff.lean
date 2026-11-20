import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module IsNilpotent

namespace GlobalTheory.WeilDeligne

namespace MonodromyThm

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => intro x hx; exact ⟨0, IsNilpotent.zero, by simp_all⟩`. Consider the case `succ k ih`. Introduce `x hx`. Establish `hn : IsNilpotent x` using `⟨_, hx⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨z, hz⟩ : ∃ z, exp (-x) = 1 - x + x ^ 2 * z := by`. Use `⟨∑ i ∈ Finset.range k, (((i + 2).factorial : ℚ)⁻¹) • (-x) ^ i, ?_⟩` and prove the remaining obligations. Rewrite using `[exp_eq_sum (k := k + 1 + 1) (by rw [neg_pow, hx, mul_zero]), Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum]`. Establish `: ∀ i, x ^ 2 * (((i + 2).factorial : ℚ)⁻¹ • (-x) ^ i) = ((i + 1 + 1).factorial : ℚ)⁻¹ • (-x) ^ (i + 1 + 1)` using `fun i => by`. Rewrite using `[mul_smul_comm]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [this]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Take `⟨y, hy, e⟩` from `ih (x ^ 2 * (z * (1 + x) - 1)) (by`. Rewrite using `[mul_pow, ← pow_mul, pow_eq_zero_of_le (by omega) hx, zero_mul])`. Use `⟨x + y, (Commute.all _ _).isNilpotent_add hn hy, ?_⟩` and prove the remaining obligations. Rewrite using `[exp_add_of_commute (Commute.all _ _) hn hy, e]`. Establish `h1` using `exp_mul_exp_neg_self hn`.

Establish `h2 : 1 + x ^ 2 * (z * (1 + x) - 1) = exp (-x) * (1 + x)` using `by rw [hz]; ring`. Rewrite using `[h2, ← mul_assoc, h1, one_mul]`.
-/
theorem exists_exp_eq_comm {R : Type*} [CommRing R] [Algebra ℚ R] (k : ℕ) :
    ∀ x : R, x ^ (k + 1) = 0 → ∃ y : R, IsNilpotent y ∧ exp y = 1 + x := by
  induction k with
  | zero => intro x hx; exact ⟨0, IsNilpotent.zero, by simp_all⟩
  | succ k ih =>
    intro x hx
    have hn : IsNilpotent x := ⟨_, hx⟩
    obtain ⟨z, hz⟩ : ∃ z, exp (-x) = 1 - x + x ^ 2 * z := by
      refine ⟨∑ i ∈ Finset.range k, (((i + 2).factorial : ℚ)⁻¹) • (-x) ^ i, ?_⟩
      rw [exp_eq_sum (k := k + 1 + 1) (by rw [neg_pow, hx, mul_zero]), Finset.sum_range_succ',
        Finset.sum_range_succ', Finset.mul_sum]
      have : ∀ i, x ^ 2 * (((i + 2).factorial : ℚ)⁻¹ • (-x) ^ i) =
          ((i + 1 + 1).factorial : ℚ)⁻¹ • (-x) ^ (i + 1 + 1) := fun i => by
        rw [mul_smul_comm]; congr 1; ring
      simp only [this]
      simp; ring
    obtain ⟨y, hy, e⟩ := ih (x ^ 2 * (z * (1 + x) - 1)) (by
      rw [mul_pow, ← pow_mul, pow_eq_zero_of_le (by omega) hx, zero_mul])
    refine ⟨x + y, (Commute.all _ _).isNilpotent_add hn hy, ?_⟩
    rw [exp_add_of_commute (Commute.all _ _) hn hy, e]
    have h1 := exp_mul_exp_neg_self hn
    have h2 : 1 + x ^ 2 * (z * (1 + x) - 1) = exp (-x) * (1 + x) := by rw [hz]; ring
    rw [h2, ← mul_assoc, h1, one_mul]

/- English proof (translation)
Take `⟨k, hk⟩` from `hu`. Set `f : AdjoinRoot (X ^ (k + 1) : ℚ[X]) →+* R` to `Ideal.Quotient.lift _ (aeval (u - 1) : ℚ[X] →ₐ[ℚ] R).toRingHom fun a ha => by`. Take `⟨b, rfl⟩` from `Ideal.mem_span_singleton'.mp ha`. Simplify using `[pow_succ', hk]`. Establish `hf : f (AdjoinRoot.root _) = u - 1` using `by show (aeval (u - 1) : ℚ[X] →ₐ[ℚ] R) X = _`.

Simplify using the standard rewrite rules. Take `⟨y, hy, e⟩` from `exists_exp_eq_comm k (AdjoinRoot.root (X ^ (k + 1) : ℚ[X])) (by`. Rewrite using `[← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self])`. Use `⟨f y, hy.map f, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_exp hy f, e, map_add, map_one, hf, add_sub_cancel]`.
-/
theorem exists_exp_eq {R : Type*} [Ring R] [Algebra ℚ R] {u : R} (hu : IsNilpotent (u - 1)) :
    ∃ y : R, IsNilpotent y ∧ exp y = u := by
  obtain ⟨k, hk⟩ := hu
  let f : AdjoinRoot (X ^ (k + 1) : ℚ[X]) →+* R :=
    Ideal.Quotient.lift _ (aeval (u - 1) : ℚ[X] →ₐ[ℚ] R).toRingHom fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp [pow_succ', hk]
  have hf : f (AdjoinRoot.root _) = u - 1 := by
    show (aeval (u - 1) : ℚ[X] →ₐ[ℚ] R) X = _
    simp
  obtain ⟨y, hy, e⟩ := exists_exp_eq_comm k (AdjoinRoot.root (X ^ (k + 1) : ℚ[X])) (by
    rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self])
  refine ⟨f y, hy.map f, ?_⟩
  rw [← map_exp hy f, e, map_add, map_one, hf, add_sub_cancel]

/- English proof (translation)
Establish `hfin : (spectrum K (M : Matrix n n K)).Finite` using `Matrix.finite_spectrum _`. Establish `hst : ∀ x ∈ spectrum K (M : Matrix n n K), x ^ q ∈ spectrum K (M : Matrix n n K)`. Introduce `x hx`. Establish `h1` using `spectrum.pow_mem_pow _ q hx`. Rewrite `h1` using `[← Units.val_pow_eq_pow_val, ← hPM, Units.val_mul, Units.val_mul, spectrum.units_conjugate]`. Then use the resulting hypothesis.

Establish `hroot : ∀ x ∈ spectrum K (M : Matrix n n K), IsOfFinOrder x`. Introduce `x hx`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Conclude with `(spectrum.zero_notMem_iff K).mpr M.isUnit hx`.

Establish `h2 : ∀ a : ℕ, x ^ q ^ a ∈ spectrum K (M : Matrix n n K)` using `fun a => by`. Proceed by induction on `a with`. Consider the case `zero => simpa using hx`. Consider the case `succ a ih => rw [_root_.pow_succ, pow_mul]`. Conclude with `hst _ ih`.

Take `⟨a, b, hab, e⟩` from `hfin.exists_lt_map_eq_of_forall_mem h2`. Establish `hlt : q ^ a < q ^ b` using `Nat.pow_lt_pow_right hq hab`. Use `isOfFinOrder_iff_pow_eq_one.mpr ⟨q ^ b - q ^ a, by omega, ?_⟩` and prove the remaining obligations. Apply `mul_left_cancel₀ (pow_ne_zero (q ^ a) hx0)` to reduce the goal to its premises. Rewrite using `[← pow_add, mul_one, Nat.add_sub_cancel' hlt.le, e]`.

Set `d` to `∏ x ∈ hfin.toFinset, orderOf x`. Establish `hd : 0 < d` using `Finset.prod_pos fun x hx => (hroot x (hfin.mem_toFinset.mp hx)).orderOf_pos`. Use `⟨d, hd, ?_⟩` and prove the remaining obligations. Establish `hsp : ∀ y ∈ spectrum K (((M ^ d : GL n K) : Matrix n n K) - 1), y = 0`. Introduce `y hy`.

Establish `h3 : y + 1 ∈ spectrum K ((M : Matrix n n K) ^ d)`. Use `(spectrum.add_mem_add_iff (R := K) (a := ((M ^ d : GL n K) : Matrix n n K) - 1) (r := y) (s := 1)).mpr hy` as an intermediate fact. Simplify using `using this`. Rewrite `h3` using `[spectrum.map_pow_of_pos _ hd]`. Take `⟨x, hx, e⟩` from `h3`.

Establish `: x ^ d = 1` using `orderOf_dvd_iff_pow_eq_one.mp (Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.mpr hx))`. Simplify `e.symm` using `[this]`. Use `set Y := ((M ^ d : GL n K) : Matrix n n K) - 1`. Establish `h4 : Y.charpoly = X ^ Fintype.card n`. Establish `h5` using `(IsAlgClosed.splits Y.charpoly).eq_prod_roots_of_monic Y.charpoly_monic`.

Establish `h6 : Y.charpoly.roots = Multiset.replicate (Fintype.card n) 0`. Rewrite using `[Multiset.eq_replicate]`. Use `⟨by rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim], fun y hy => hsp y (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr (isRoot_of_mem_roots hy))⟩` and prove the remaining obligations. Rewrite using `[h5, h6]`. Simplify using the standard rewrite rules.

Conclude with `⟨Fintype.card n, by simpa [h4] using Y.aeval_self_charpoly⟩`.
-/
theorem exists_pow_unipotent {K n : Type*} [Field K] [IsAlgClosed K] [Fintype n] [DecidableEq n]
    {P M : GL n K} {q : ℕ} (hq : 1 < q) (hPM : P * M * P⁻¹ = M ^ q) :
    ∃ d, 0 < d ∧ IsNilpotent (((M ^ d : GL n K) : Matrix n n K) - 1) := by
  have hfin : (spectrum K (M : Matrix n n K)).Finite := Matrix.finite_spectrum _
  have hst : ∀ x ∈ spectrum K (M : Matrix n n K), x ^ q ∈ spectrum K (M : Matrix n n K) := by
    intro x hx
    have h1 := spectrum.pow_mem_pow _ q hx
    rwa [← Units.val_pow_eq_pow_val, ← hPM, Units.val_mul, Units.val_mul,
      spectrum.units_conjugate] at h1
  have hroot : ∀ x ∈ spectrum K (M : Matrix n n K), IsOfFinOrder x := by
    intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact (spectrum.zero_notMem_iff K).mpr M.isUnit hx
    have h2 : ∀ a : ℕ, x ^ q ^ a ∈ spectrum K (M : Matrix n n K) := fun a => by
      induction a with
      | zero => simpa using hx
      | succ a ih => rw [_root_.pow_succ, pow_mul]; exact hst _ ih
    obtain ⟨a, b, hab, e⟩ := hfin.exists_lt_map_eq_of_forall_mem h2
    have hlt : q ^ a < q ^ b := Nat.pow_lt_pow_right hq hab
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨q ^ b - q ^ a, by omega, ?_⟩
    apply mul_left_cancel₀ (pow_ne_zero (q ^ a) hx0)
    rw [← pow_add, mul_one, Nat.add_sub_cancel' hlt.le, e]
  let d := ∏ x ∈ hfin.toFinset, orderOf x
  have hd : 0 < d := Finset.prod_pos fun x hx => (hroot x (hfin.mem_toFinset.mp hx)).orderOf_pos
  refine ⟨d, hd, ?_⟩
  have hsp : ∀ y ∈ spectrum K (((M ^ d : GL n K) : Matrix n n K) - 1), y = 0 := by
    intro y hy
    have h3 : y + 1 ∈ spectrum K ((M : Matrix n n K) ^ d) := by
      have := (spectrum.add_mem_add_iff (R := K) (a := ((M ^ d : GL n K) : Matrix n n K) - 1)
        (r := y) (s := 1)).mpr hy
      simpa using this
    rw [spectrum.map_pow_of_pos _ hd] at h3
    obtain ⟨x, hx, e⟩ := h3
    have : x ^ d = 1 := orderOf_dvd_iff_pow_eq_one.mp
      (Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.mpr hx))
    simpa [this] using e.symm
  set Y := ((M ^ d : GL n K) : Matrix n n K) - 1
  have h4 : Y.charpoly = X ^ Fintype.card n := by
    have h5 := (IsAlgClosed.splits Y.charpoly).eq_prod_roots_of_monic Y.charpoly_monic
    have h6 : Y.charpoly.roots = Multiset.replicate (Fintype.card n) 0 := by
      rw [Multiset.eq_replicate]
      refine ⟨by rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim],
        fun y hy => hsp y (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr (isRoot_of_mem_roots hy))⟩
    rw [h5, h6]; simp
  exact ⟨Fintype.card n, by simpa [h4] using Y.aeval_self_charpoly⟩

section Small

variable {K n : Type*} [NormedField K] [IsUltrametricDist K] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Conclude with `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) fun k _ => by`. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (hX _ _) (hY _ _) (norm_nonneg _) ha`.
-/
theorem norm_mul_apply_le {X Y : Matrix n n K} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hX : ∀ i j, ‖X i j‖ ≤ a) (hY : ∀ i j, ‖Y i j‖ ≤ b) (i j : n) : ‖(X * Y) i j‖ ≤ a * b := by
  rw [Matrix.mul_apply]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) fun k _ => by
    rw [norm_mul]; exact mul_le_mul (hX _ _) (hY _ _) (norm_nonneg _) ha

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => intro i j`. Simplify using `using mul_nonneg hc hc`. Consider the case `succ m ih`. Introduce `i j`.

Establish `e : (1 + X) ^ (m + 1) - 1 - ((m + 1 : ℕ) : K) • X = ((1 + X) ^ m - 1 - (m : K) • X) + (((1 + X) ^ m - 1 - (m : K) • X) * X + (m : K) • (X * X))`. Simplify using `only [_root_.pow_succ, mul_add, sub_mul, smul_mul_assoc, Nat.cast_succ, add_smul, one_smul, mul_one, one_mul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, Matrix.add_apply, Matrix.add_apply]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ih i j) ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)))` and prove the remaining obligations.

Conclude with `(norm_mul_apply_le (mul_nonneg hc hc) hc ih hX i j).trans (mul_le_of_le_one_right (mul_nonneg hc hc) hc1)`. Rewrite using `[Matrix.smul_apply, smul_eq_mul, norm_mul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K m)).trans (norm_mul_apply_le hc hc hX hX i j)`.
-/
theorem norm_pow_sub_le {X : Matrix n n K} {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hX : ∀ i j, ‖X i j‖ ≤ c) (m : ℕ) :
    ∀ i j, ‖((1 + X) ^ m - 1 - (m : K) • X) i j‖ ≤ c * c := by
  induction m with
  | zero => intro i j; simpa using mul_nonneg hc hc
  | succ m ih =>
    intro i j
    have e : (1 + X) ^ (m + 1) - 1 - ((m + 1 : ℕ) : K) • X =
        ((1 + X) ^ m - 1 - (m : K) • X) + (((1 + X) ^ m - 1 - (m : K) • X) * X
          + (m : K) • (X * X)) := by
      simp only [_root_.pow_succ, mul_add, sub_mul, smul_mul_assoc, Nat.cast_succ, add_smul, one_smul,
        mul_one, one_mul]
      abel
    rw [e, Matrix.add_apply, Matrix.add_apply]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ih i j)
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)))
    · exact (norm_mul_apply_le (mul_nonneg hc hc) hc ih hX i j).trans
        (mul_le_of_le_one_right (mul_nonneg hc hc) hc1)
    · rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K m)).trans
        (norm_mul_apply_le hc hc hX hX i j)

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨X, rfl⟩ : ∃ X, M = 1 + X` from `⟨M - 1, by simp⟩`. Rewrite `hM` using `[add_sub_cancel_left]`. Establish `hne' : ∃ i j, X i j ≠ 0`. Assume the negation of the conclusion as `H`.

Use `push Not at H`. Conclude with `hne (by rw [show X = 0 from Matrix.ext H, add_zero])`. Take `⟨i0, j0, h0⟩` from `hne'`. Take `⟨⟨i, j⟩, -, hij⟩` from `Finset.exists_max_image (Finset.univ : Finset (n × n)) (fun p => ‖X p.1 p.2‖) ⟨(i0, j0), Finset.mem_univ _⟩`. Establish `hle : ∀ a b, ‖X a b‖ ≤ ‖X i j‖` using `fun a b => hij (a, b) (Finset.mem_univ _)`.

Establish `hc : 0 < ‖X i j‖` using `(norm_pos_iff.mpr h0).trans_le (hle _ _)`. Take `⟨m, hm, hε⟩` from `h _ hc`. Establish `h1` using `(norm_pow_sub_le hc.le (hM i j).le hle m i j).trans_lt (mul_lt_of_lt_one_right hc (hM i j))`. Establish `e : (m : K) * X i j = ((1 + X) ^ m - 1) i j + -(((1 + X) ^ m - 1 - (m : K) • X) i j)`. Simplify using `[Matrix.sub_apply]`.

Establish `h2` using `IsUltrametricDist.norm_add_le_max (((1 + X) ^ m - 1) i j) (-(((1 + X) ^ m - 1 - (m : K) • X) i j))`. Rewrite `h2` using `[← e, norm_mul, hm, one_mul, norm_neg]`. Conclude with `absurd h2 (not_le.mpr (max_lt (hε i j) h1))`.
-/
theorem eq_one_of_pow_near {M : Matrix n n K} (hM : ∀ i j, ‖(M - 1) i j‖ < 1)
    (h : ∀ ε > (0 : ℝ), ∃ m : ℕ, ‖(m : K)‖ = 1 ∧ ∀ i j, ‖(M ^ m - 1) i j‖ < ε) : M = 1 := by
  by_contra hne
  obtain ⟨X, rfl⟩ : ∃ X, M = 1 + X := ⟨M - 1, by simp⟩
  rw [add_sub_cancel_left] at hM
  have hne' : ∃ i j, X i j ≠ 0 := by
    by_contra H
    push Not at H
    exact hne (by rw [show X = 0 from Matrix.ext H, add_zero])
  obtain ⟨i0, j0, h0⟩ := hne'
  obtain ⟨⟨i, j⟩, -, hij⟩ := Finset.exists_max_image (Finset.univ : Finset (n × n))
    (fun p => ‖X p.1 p.2‖) ⟨(i0, j0), Finset.mem_univ _⟩
  have hle : ∀ a b, ‖X a b‖ ≤ ‖X i j‖ := fun a b => hij (a, b) (Finset.mem_univ _)
  have hc : 0 < ‖X i j‖ := (norm_pos_iff.mpr h0).trans_le (hle _ _)
  obtain ⟨m, hm, hε⟩ := h _ hc
  have h1 := (norm_pow_sub_le hc.le (hM i j).le hle m i j).trans_lt
    (mul_lt_of_lt_one_right hc (hM i j))
  have e : (m : K) * X i j = ((1 + X) ^ m - 1) i j + -(((1 + X) ^ m - 1 - (m : K) • X) i j) := by
    simp [Matrix.sub_apply]
  have h2 := IsUltrametricDist.norm_add_le_max (((1 + X) ^ m - 1) i j)
    (-(((1 + X) ^ m - 1 - (m : K) • X) i j))
  rw [← e, norm_mul, hm, one_mul, norm_neg] at h2
  exact absurd h2 (not_le.mpr (max_lt (hε i j) h1))

end Small

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {l : ℕ} [Fact l.Prime] {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Establish `hvl : ¬ A.valuation (l : Ω) < 1` using `fun h' => hl (by rw [← h]; simpa using h')`. Establish `hvl1 : A.valuation (l : Ω) = 1` using `le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hvl)`. Establish `: IsGalois E Ω` using `IsAlgClosure.isGalois E Ω`. Take `⟨L, hL, hsub⟩` from `(krullTopology_mem_nhds_one_iff E Ω _).mp hV`.

Establish `hidx : L.fixingSubgroup.index ≠ 0`. Rewrite using `[← IntermediateField.finrank_eq_fixingSubgroup_index]`. Conclude with `Module.finrank_pos.ne'`. Take `⟨N, hN, -, hmem⟩` from `Subgroup.exists_pow_mem_of_index_ne_zero hidx σ`. Take `⟨a, m, hm, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hp.ne_one`.

Use `⟨m, hm, hsub ?_⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]`. Rewrite `hmem` using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Use `GlobalTheory.WildInertiaChar.fixed_of_pow_fixed A (σ ^ m) (pow_mem hσ m) (l ^ a) ?_ x ?_` and prove the remaining obligations.

Rewrite using `[Nat.cast_pow, map_pow, hvl1, one_pow]`. Conclude with `lt_irrefl _`. Rewrite using `[← pow_mul, mul_comm]`. Conclude with `hmem x hx`.
-/
theorem exists_pow_mem_of_wild (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal)
    {σ : G E Ω} (hσ : σ ∈ Wild E A) {V : Set (G E Ω)} (hV : V ∈ nhds 1) :
    ∃ m : ℕ, ¬ l ∣ m ∧ σ ^ m ∈ V := by
  have hp : l.Prime := Fact.out
  have hvl : ¬ A.valuation (l : Ω) < 1 := fun h' => hl (by rw [← h]; simpa using h')
  have hvl1 : A.valuation (l : Ω) = 1 :=
    le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hvl)
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff E Ω _).mp hV
  have hidx : L.fixingSubgroup.index ≠ 0 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx σ
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hp.ne_one
  refine ⟨m, hm, hsub ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  rw [IntermediateField.mem_fixingSubgroup_iff] at hmem
  intro x hx
  refine GlobalTheory.WildInertiaChar.fixed_of_pow_fixed A (σ ^ m) (pow_mem hσ m) (l ^ a) ?_ x ?_
  · rw [Nat.cast_pow, map_pow, hvl1, one_pow]; exact lt_irrefl _
  · rw [← pow_mul, mul_comm]; exact hmem x hx

/- English proof (translation)
Establish `h1 : S ≤ (Subgroup.zpowers (QuotientGroup.mk' S g)).comap (QuotientGroup.mk' S)` using `fun x hx => by`. Rewrite using `[Subgroup.mem_comap, QuotientGroup.mk'_apply S x, (QuotientGroup.eq_one_iff x).mpr hx]`. Conclude with `one_mem _`. Take `⟨k, hk⟩` from `GlobalTheory.TameCharUnique.mem_of_tameGen hγ _ (Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono h1 hS)) (Subgroup.mem_zpowers _) (fun τ hτ => h1 (hW hτ)) σ`. Conclude with `⟨k, QuotientGroup.eq.mp hk⟩`.
-/
theorem exists_zpow_of_tameGen {g : Ine (F := E) A} (hγ : Formalism.BasicNotions.TameGenAt A (g : G E Ω))
    (S : Subgroup (Ine (F := E) A)) [S.Normal] (hS : IsOpen (S : Set (Ine (F := E) A)))
    (hW : (Wild E A).subgroupOf (Ine (F := E) A) ≤ S) (σ : Ine (F := E) A) :
    ∃ k : ℤ, (g ^ k)⁻¹ * σ ∈ S := by
  have h1 : S ≤ (Subgroup.zpowers (QuotientGroup.mk' S g)).comap (QuotientGroup.mk' S) :=
    fun x hx => by
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply S x, (QuotientGroup.eq_one_iff x).mpr hx]
      exact one_mem _
  obtain ⟨k, hk⟩ := GlobalTheory.TameCharUnique.mem_of_tameGen hγ _
    (Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono h1 hS)) (Subgroup.mem_zpowers _)
    (fun τ hτ => h1 (hW hτ)) σ
  exact ⟨k, QuotientGroup.eq.mp hk⟩

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Use `compactSpace_Ine (E := E) A` as an intermediate fact. Take `⟨g, hγ⟩ : ∃ g : Ine (F` from `E) A, Formalism.BasicNotions.TameGenAt A (g : G E Ω) := by`. Take `⟨γ, hγ⟩` from `GlobalTheory.TameInertiaGen.exists_tameGenAt E Ω w A h`. Conclude with `⟨⟨γ, hγ.1⟩, hγ⟩`.

Use `set P := (Wild E A).subgroupOf (Ine (F := E) A)`. Establish `hP : P.Normal` using `⟨fun x hx y => conj_mem_Wild (Ine_le_Dec A y.2) hx⟩`. Set `T : ℕ → Subgroup (Ine (F` to `E) A) := fun a => (Ideal.span {(l : ℤ_[l]) ^ a}).toAddSubgroup.toSubgroup.comap t`. Establish `hT : ∀ a x, x ∈ T a ↔ (l : ℤ_[l]) ^ a ∣ (t x).toAdd` using `fun a x => Ideal.mem_span_singleton`. Establish `hTo : ∀ a, IsOpen (T a : Set (Ine (F` using `E) A)) := fun a => by`.

Establish `: (T a : Set (Ine (F` using `E) A)) = (fun x => (t x).toAdd) ⁻¹' Metric.closedBall 0 ((l : ℝ) ^ (-a : ℤ)) := by`. Use extensionality with `x`. Rewrite using `[SetLike.mem_coe, hT, Set.mem_preimage, mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]`. Rewrite using `[this]`. Conclude with `(IsUltrametricDist.isOpen_closedBall _ (zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero))).preimage (continuous_toAdd.comp ht.1)`.

Establish `hPT : ∀ a, P ≤ T a` using `fun a x hx => by`. Rewrite using `[hT, GlobalTheory.TameCharUnique.eq_zero_of_wild h hl t ht.1 x hx]`. Conclude with `dvd_zero _`. Establish `hu : IsUnit (t g).toAdd`. Take `⟨σ₀, h0⟩` from `ht.2 (Multiplicative.ofAdd 1)`.

Take `⟨k, hk⟩` from `exists_zpow_of_tameGen hγ (T 1) (hTo 1) (hPT 1) σ₀`. Rewrite `hk` using `[hT, map_mul, map_inv, map_zpow, h0, toAdd_mul, toAdd_inv, toAdd_zpow, toAdd_ofAdd, pow_one, zsmul_eq_mul]`. Assume the negation of the conclusion as `hn`. Establish `h1 : (l : ℤ_[l]) ∣ (t g).toAdd` using `(PadicInt.norm_lt_one_iff_dvd _).mp (lt_of_le_of_ne (PadicInt.norm_le_one _) (mt PadicInt.isUnit_iff.mpr hn))`. Establish `h2` using `dvd_add (h1.mul_left k) hk`.

Rewrite `h2` using `[add_neg_cancel_left]`. Conclude with `PadicInt.irreducible_p.not_isUnit (isUnit_of_dvd_one h2)`. Establish `hPV : IsOpen ((P ⊔ V : Subgroup _) : Set (Ine (F` using `E) A)) := Subgroup.isOpen_mono le_sup_right hV`. Establish `: Finite (Ine (F` using `E) A ⧸ (P ⊔ V)) := Subgroup.quotient_finite_of_isOpen _ hPV`. Take `⟨a, m, hm, e⟩` from `Nat.exists_eq_pow_mul_and_not_dvd (Subgroup.index_ne_zero_of_finite (H := P ⊔ V)) l hp.ne_one`.

Take `⟨k, hk⟩` from `exists_zpow_of_tameGen hγ ((P ⊔ V) ⊓ T a) (hPV.inter (hTo a)) (le_inf le_sup_left (hPT a)) σ`. Take `⟨hk1, hk2⟩` from `Subgroup.mem_inf.mp hk`. Rewrite `hk2` using `[hT, map_mul, map_inv, map_zpow, hσ, mul_one, toAdd_inv, toAdd_zpow, zsmul_eq_mul, dvd_neg, hu.dvd_mul_right, ← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_int_le_pow_iff_dvd]`. Take `⟨c, rfl⟩` from `hk2`. Establish `h3 : σ ^ m ∈ P ⊔ V`.

Rewrite using `[← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← QuotientGroup.eq.mpr hk1, QuotientGroup.mk_zpow, ← zpow_natCast, ← zpow_mul, mul_right_comm, zpow_mul]`. Establish `: (l : ℤ) ^ a * m = ((P ⊔ V).index : ℕ)` using `by rw [e]; push_cast; rfl`. Rewrite using `[this, zpow_natCast, ← QuotientGroup.mk_pow, (QuotientGroup.eq_one_iff _).mpr (Subgroup.pow_index_mem (P ⊔ V) g), one_zpow]`. Take `⟨p, hp', v, hv, e'⟩` from `Subgroup.mem_sup_of_normal_right.mp h3`. Take `⟨U, hU, hUV⟩` from `isOpen_induced_iff.1 hV`.

Take `⟨m', hm', h4⟩` from `exists_pow_mem_of_wild h hl hp' (V := U) (hU.mem_nhds (show (1 : Ine (F := E) A) ∈ Subtype.val ⁻¹' U by rw [hUV]; exact V.one_mem))`. Establish `h5 : p ^ m' ∈ V` using `by rw [← SetLike.mem_coe, ← hUV]; exact h4`. Use `⟨m * m', fun H => (hp.dvd_mul.mp H).elim hm hm', ?_⟩` and prove the remaining obligations. Rewrite using `[← QuotientGroup.eq_one_iff, pow_mul, ← e', QuotientGroup.mk_pow, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff v).mpr hv, mul_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]`. Conclude with `h5`.
-/
theorem exists_pow_mem_of_ker (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal)
    {t : Ine (F := E) A →* Multiplicative ℤ_[l]} (ht : IsTameChar t) {σ : Ine (F := E) A}
    (hσ : t σ = 1) (V : Subgroup (Ine (F := E) A)) [V.Normal]
    (hV : IsOpen (V : Set (Ine (F := E) A))) : ∃ m : ℕ, ¬ l ∣ m ∧ σ ^ m ∈ V := by
  have hp : l.Prime := Fact.out
  have := compactSpace_Ine (E := E) A
  obtain ⟨g, hγ⟩ : ∃ g : Ine (F := E) A, Formalism.BasicNotions.TameGenAt A (g : G E Ω) := by
    obtain ⟨γ, hγ⟩ := GlobalTheory.TameInertiaGen.exists_tameGenAt E Ω w A h
    exact ⟨⟨γ, hγ.1⟩, hγ⟩
  set P := (Wild E A).subgroupOf (Ine (F := E) A)
  have hP : P.Normal := ⟨fun x hx y => conj_mem_Wild (Ine_le_Dec A y.2) hx⟩

  let T : ℕ → Subgroup (Ine (F := E) A) := fun a =>
    (Ideal.span {(l : ℤ_[l]) ^ a}).toAddSubgroup.toSubgroup.comap t
  have hT : ∀ a x, x ∈ T a ↔ (l : ℤ_[l]) ^ a ∣ (t x).toAdd := fun a x => Ideal.mem_span_singleton
  have hTo : ∀ a, IsOpen (T a : Set (Ine (F := E) A)) := fun a => by
    have : (T a : Set (Ine (F := E) A)) =
        (fun x => (t x).toAdd) ⁻¹' Metric.closedBall 0 ((l : ℝ) ^ (-a : ℤ)) := by
      ext x
      rw [SetLike.mem_coe, hT, Set.mem_preimage, mem_closedBall_zero_iff,
        PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
    rw [this]
    exact (IsUltrametricDist.isOpen_closedBall _
      (zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero))).preimage (continuous_toAdd.comp ht.1)
  have hPT : ∀ a, P ≤ T a := fun a x hx => by
    rw [hT, GlobalTheory.TameCharUnique.eq_zero_of_wild h hl t ht.1 x hx]; exact dvd_zero _
  have hu : IsUnit (t g).toAdd := by
    obtain ⟨σ₀, h0⟩ := ht.2 (Multiplicative.ofAdd 1)
    obtain ⟨k, hk⟩ := exists_zpow_of_tameGen hγ (T 1) (hTo 1) (hPT 1) σ₀
    rw [hT, map_mul, map_inv, map_zpow, h0, toAdd_mul, toAdd_inv, toAdd_zpow, toAdd_ofAdd,
      pow_one, zsmul_eq_mul] at hk
    by_contra hn
    have h1 : (l : ℤ_[l]) ∣ (t g).toAdd := (PadicInt.norm_lt_one_iff_dvd _).mp
      (lt_of_le_of_ne (PadicInt.norm_le_one _) (mt PadicInt.isUnit_iff.mpr hn))
    have h2 := dvd_add (h1.mul_left k) hk
    rw [add_neg_cancel_left] at h2
    exact PadicInt.irreducible_p.not_isUnit (isUnit_of_dvd_one h2)
  have hPV : IsOpen ((P ⊔ V : Subgroup _) : Set (Ine (F := E) A)) :=
    Subgroup.isOpen_mono le_sup_right hV
  have : Finite (Ine (F := E) A ⧸ (P ⊔ V)) := Subgroup.quotient_finite_of_isOpen _ hPV
  obtain ⟨a, m, hm, e⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (Subgroup.index_ne_zero_of_finite (H := P ⊔ V)) l hp.ne_one
  obtain ⟨k, hk⟩ := exists_zpow_of_tameGen hγ ((P ⊔ V) ⊓ T a) (hPV.inter (hTo a))
    (le_inf le_sup_left (hPT a)) σ
  obtain ⟨hk1, hk2⟩ := Subgroup.mem_inf.mp hk
  rw [hT, map_mul, map_inv, map_zpow, hσ, mul_one, toAdd_inv, toAdd_zpow,
    zsmul_eq_mul, dvd_neg, hu.dvd_mul_right, ← Ideal.mem_span_singleton,
    ← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_int_le_pow_iff_dvd] at hk2
  obtain ⟨c, rfl⟩ := hk2
  have h3 : σ ^ m ∈ P ⊔ V := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← QuotientGroup.eq.mpr hk1,
      QuotientGroup.mk_zpow, ← zpow_natCast, ← zpow_mul, mul_right_comm, zpow_mul]
    have : (l : ℤ) ^ a * m = ((P ⊔ V).index : ℕ) := by rw [e]; push_cast; rfl
    rw [this, zpow_natCast, ← QuotientGroup.mk_pow,
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.pow_index_mem (P ⊔ V) g), one_zpow]
  obtain ⟨p, hp', v, hv, e'⟩ := Subgroup.mem_sup_of_normal_right.mp h3
  obtain ⟨U, hU, hUV⟩ := isOpen_induced_iff.1 hV
  obtain ⟨m', hm', h4⟩ := exists_pow_mem_of_wild h hl hp' (V := U)
    (hU.mem_nhds (show (1 : Ine (F := E) A) ∈ Subtype.val ⁻¹' U by rw [hUV]; exact V.one_mem))
  have h5 : p ^ m' ∈ V := by rw [← SetLike.mem_coe, ← hUV]; exact h4
  refine ⟨m * m', fun H => (hp.dvd_mul.mp H).elim hm hm', ?_⟩
  rw [← QuotientGroup.eq_one_iff, pow_mul, ← e', QuotientGroup.mk_pow, QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff v).mpr hv, mul_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact h5

/- English proof (translation)
Establish `: IsGalois E Ω` using `IsAlgClosure.isGalois E Ω`. Take `⟨W, hW, ho, h1⟩` from `mem_nhds_iff.mp hV`. Take `⟨U, hU⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho h1`. Conclude with `⟨U.toSubgroup, inferInstance, U.isOpen, hU.trans hW⟩`.
-/
theorem exists_open_normal {V : Set (G E Ω)} (hV : V ∈ nhds 1) :
    ∃ U : Subgroup (G E Ω), U.Normal ∧ IsOpen (U : Set (G E Ω)) ∧ (U : Set (G E Ω)) ⊆ V := by
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  obtain ⟨W, hW, ho, h1⟩ := mem_nhds_iff.mp hV
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho h1
  exact ⟨U.toSubgroup, inferInstance, U.isOpen, hU.trans hW⟩

variable {r : G E Ω →* GL n (Qbar l)}

omit [NumberField E] [IsAlgClosure E Ω] in

/- English proof (translation)
Use `IsOpen.mem_nhds ?_ (by simpa using fun _ _ => hε)` and prove the remaining obligations. Simplify using `only [Set.ofPred_forall]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_lt ((hr.sub continuous_const).matrix_elem i j).norm continuous_const`.
-/
theorem near_mem_nhds (hr : Continuous fun g => (r g : Matrix n n (Qbar l))) {ε : ℝ} (hε : 0 < ε) :
    {g | ∀ i j, ‖((r g : Matrix n n (Qbar l)) - 1) i j‖ < ε} ∈ nhds (1 : G E Ω) := by
  refine IsOpen.mem_nhds ?_ (by simpa using fun _ _ => hε)
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_lt ((hr.sub continuous_const).matrix_elem i j).norm continuous_const

/- English proof (translation)
Use `Units.val_eq_one.mp (eq_one_of_pow_near h1 fun ε hε => ?_)` and prove the remaining obligations. Take `⟨U, hn, hU, hsub⟩` from `exists_open_normal (near_mem_nhds hr hε)`. Take `⟨m, hm, H⟩` from `exists_pow_mem_of_ker h hl ht hσ (U.subgroupOf _) (hU.preimage continuous_subtype_val)`. Use `⟨m, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap', Padic.norm_natCast_eq_one_iff]`.

Conclude with `(Fact.out : l.Prime).coprime_iff_not_dvd.mpr hm`. Simplify using `using hsub H`.
-/
theorem eq_one_of_ker (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal)
    {t : Ine (F := E) A →* Multiplicative ℤ_[l]} (ht : IsTameChar t)
    (hr : Continuous fun g => (r g : Matrix n n (Qbar l))) {σ : Ine (F := E) A} (hσ : t σ = 1)
    (h1 : ∀ i j, ‖((r σ : Matrix n n (Qbar l)) - 1) i j‖ < 1) : r σ = 1 := by
  refine Units.val_eq_one.mp (eq_one_of_pow_near h1 fun ε hε => ?_)
  obtain ⟨U, hn, hU, hsub⟩ := exists_open_normal (near_mem_nhds hr hε)
  obtain ⟨m, hm, H⟩ := exists_pow_mem_of_ker h hl ht hσ (U.subgroupOf _)
    (hU.preimage continuous_subtype_val)
  refine ⟨m, ?_, ?_⟩
  · rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
    exact (Fact.out : l.Prime).coprime_iff_not_dvd.mpr hm
  · simpa using hsub H

end MonodromyThm

open MonodromyThm

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {l : ℕ} [Fact l.Prime] {n : Type} [Fintype n] [DecidableEq n]
variable {r : G E Ω →* GL n (Qbar l)}

/- English proof (translation)
Use `compactSpace_Ine (E := E) A` as an intermediate fact. Take `⟨U, hn, hU, hsub⟩` from `exists_open_normal (near_mem_nhds hr one_pos)`. Use `set U' := U.subgroupOf (Ine (F := E) A)`. Establish `hU' : IsOpen (U' : Set (Ine (F` using `E) A)) := hU.preimage continuous_subtype_val`. Establish `inj : ∀ σ τ : Ine (F` using `E) A, tval t σ = tval t τ → t σ = t τ := fun σ τ e => Multiplicative.toAdd.injective (Subtype.ext ((algebraMap ℚ_[l] (Qbar l)).injective e))`.

Establish `key : ∀ σ ∈ U', ∀ τ ∈ U', t σ = t τ → r σ = r τ` using `fun σ hσ τ hτ e => by`. Use `eq_one_of_ker h hl ht hr (σ := σ⁻¹ * τ) (by simp [e]) (hsub (show σ⁻¹ * τ ∈ U' from mul_mem (inv_mem hσ) hτ))` as an intermediate fact. Rewrite `this` using `[Subgroup.coe_mul, map_mul, Subgroup.coe_inv, map_inv, inv_mul_eq_one]`. Then use the resulting hypothesis. Take `⟨σ₁, h1, h1'⟩` from `ht.exists_tval_ne_zero hU'`. Establish `h2` using `key (ineConj (frob h) σ₁) (hn.conj_mem _ h1 _) (σ₁ ^ normV w) (pow_mem h1 _) (inj _ _ (by rw [ht.tval_ineConj hl, deg_frob, zpow_one, tval_pow]))`.

Take `⟨d, hd, hnil⟩` from `exists_pow_unipotent (P := r (frob h)) (M := r σ₁) (one_lt_normV w) (by rw [← map_pow, ← Subgroup.coe_pow, ← h2, ← map_inv, ← map_mul, ← map_mul]; rfl)`. Take `⟨Y, hY, eY⟩` from `exists_exp_eq hnil`. Use `set σ₀ := σ₁ ^ d with hσ₀`. Establish `h0 : σ₀ ∈ U'` using `pow_mem h1 _`. Establish `h0' : tval t σ₀ ≠ 0`.

Rewrite using `[hσ₀, tval_pow]`. Conclude with `mul_ne_zero (Nat.cast_ne_zero.mpr hd.ne') h1'`. Use `set N := (tval t σ₀)⁻¹ • Y with hN`. Establish `hNn : IsNilpotent N` using `hY.smul _`. Establish `e0 : (r σ₀ : Matrix n n (Qbar l)) = exp (tval t σ₀ • N)`.

Rewrite using `[hN, smul_inv_smul₀ h0', eY, hσ₀, Subgroup.coe_pow, map_pow]`. Establish `ct : Continuous fun σ => (t σ).toAdd` using `continuous_toAdd.comp ht.1`. Establish `ce : Continuous fun σ => exp (tval t σ • N)`. Take `⟨k, hk⟩` from `hNn`. Establish `c1 : Continuous (tval t)` using `(continuous_algebraMap _ _).comp (continuous_subtype_val.comp ct)`.

Establish `: ∀ σ, exp (tval t σ • N) = ∑ i ∈ Finset.range k, tval t σ ^ i • (((i.factorial : ℚ)⁻¹) • N ^ i)` using `fun σ => by`. Rewrite using `[exp_eq_sum (k := k) (by rw [_root_.smul_pow, hk, smul_zero])]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [_root_.smul_pow, smul_comm]`. Simplify using `only [this]`. Use `fun_prop`.

Set `S : Set (Ine (F` to `E) A) := (U' : Set _) ∩ {σ | (r σ : Matrix n n (Qbar l)) = exp (tval t σ • N)}`. Establish `hS : IsClosed ((fun σ => (t σ).toAdd) '' S)` using `(((U'.isClosed_of_isOpen hU').inter (isClosed_eq (hr.comp continuous_subtype_val) ce)).isCompact.image ct).isClosed`. Establish `hk : ∀ k : ℕ, σ₀ ^ k ∈ S` using `fun k => ⟨pow_mem h0 k, by show _ = _`. Proceed by induction on `k with`. Consider the case `zero => simp`.

Consider the case `succ k ih`. Rewrite using `[_root_.pow_succ, tval_mul, exp_add_smul hNn, ← ih, ← e0, Subgroup.coe_mul, map_mul, Units.val_mul]⟩`. Establish `hall : ∀ c : ℤ_[l], c * (t σ₀).toAdd ∈ (fun σ => (t σ).toAdd) '' S` using `fun c => PadicInt.denseRange_natCast.induction_on c (hS.preimage (continuous_mul_const _)) fun k => ⟨_, hk k, by simp⟩`. Establish `h3 : (t σ₀).toAdd ≠ 0` using `fun e => h0' (by simp [tval, e])`. Use `⟨N, .of_nhds hNn ?_⟩` and prove the remaining obligations.

Use `filter_upwards [hU'.mem_nhds U'.one_mem, (isOpen_lt ct.norm continuous_const).mem_nhds (show ‖(t 1).toAdd‖ < ‖(t σ₀).toAdd‖ by simpa using h3)] with σ hσ hlt`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : (t σ₀).toAdd ∣ (t σ).toAdd := by`. Break down `ValuationRing.dvd_total (t σ₀).toAdd (t σ).toAdd with H | ⟨c, hc⟩` into its components or cases. Conclude with `H`. Rewrite `hlt` using `[hc, norm_mul]`.

Conclude with `absurd (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one c)) hlt.not_ge`. Take `⟨τ, hτ, e⟩` from `hall c`. Establish `e' : t τ = t σ` using `Multiplicative.toAdd.injective (e.trans (by rw [hc, mul_comm]))`. Rewrite using `[key σ hσ τ hτ.1 e'.symm, hτ.2, tval, tval, e']`.
-/
theorem exists_isMonodromy (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal)
    {t : Ine (F := E) A →* Multiplicative ℤ_[l]} (ht : IsTameChar t)
    (hr : Continuous fun g => (r g : Matrix n n (Qbar l))) : ∃ N, IsMonodromy t r N := by
  have := compactSpace_Ine (E := E) A
  obtain ⟨U, hn, hU, hsub⟩ := exists_open_normal (near_mem_nhds hr one_pos)
  set U' := U.subgroupOf (Ine (F := E) A)
  have hU' : IsOpen (U' : Set (Ine (F := E) A)) := hU.preimage continuous_subtype_val
  have inj : ∀ σ τ : Ine (F := E) A, tval t σ = tval t τ → t σ = t τ := fun σ τ e =>
    Multiplicative.toAdd.injective (Subtype.ext ((algebraMap ℚ_[l] (Qbar l)).injective e))
  have key : ∀ σ ∈ U', ∀ τ ∈ U', t σ = t τ → r σ = r τ := fun σ hσ τ hτ e => by
    have := eq_one_of_ker h hl ht hr (σ := σ⁻¹ * τ) (by simp [e])
      (hsub (show σ⁻¹ * τ ∈ U' from mul_mem (inv_mem hσ) hτ))
    rwa [Subgroup.coe_mul, map_mul, Subgroup.coe_inv, map_inv, inv_mul_eq_one] at this
  obtain ⟨σ₁, h1, h1'⟩ := ht.exists_tval_ne_zero hU'
  have h2 := key (ineConj (frob h) σ₁) (hn.conj_mem _ h1 _) (σ₁ ^ normV w) (pow_mem h1 _)
    (inj _ _ (by rw [ht.tval_ineConj hl, deg_frob, zpow_one, tval_pow]))
  obtain ⟨d, hd, hnil⟩ := exists_pow_unipotent (P := r (frob h)) (M := r σ₁) (one_lt_normV w)
    (by rw [← map_pow, ← Subgroup.coe_pow, ← h2, ← map_inv, ← map_mul, ← map_mul]; rfl)
  obtain ⟨Y, hY, eY⟩ := exists_exp_eq hnil
  set σ₀ := σ₁ ^ d with hσ₀
  have h0 : σ₀ ∈ U' := pow_mem h1 _
  have h0' : tval t σ₀ ≠ 0 := by
    rw [hσ₀, tval_pow]; exact mul_ne_zero (Nat.cast_ne_zero.mpr hd.ne') h1'
  set N := (tval t σ₀)⁻¹ • Y with hN
  have hNn : IsNilpotent N := hY.smul _
  have e0 : (r σ₀ : Matrix n n (Qbar l)) = exp (tval t σ₀ • N) := by
    rw [hN, smul_inv_smul₀ h0', eY, hσ₀, Subgroup.coe_pow, map_pow]
  have ct : Continuous fun σ => (t σ).toAdd := continuous_toAdd.comp ht.1
  have ce : Continuous fun σ => exp (tval t σ • N) := by
    obtain ⟨k, hk⟩ := hNn
    have c1 : Continuous (tval t) :=
      (continuous_algebraMap _ _).comp (continuous_subtype_val.comp ct)
    have : ∀ σ, exp (tval t σ • N) =
        ∑ i ∈ Finset.range k, tval t σ ^ i • (((i.factorial : ℚ)⁻¹) • N ^ i) := fun σ => by
      rw [exp_eq_sum (k := k) (by rw [_root_.smul_pow, hk, smul_zero])]
      exact Finset.sum_congr rfl fun i _ => by rw [_root_.smul_pow, smul_comm]
    simp only [this]
    fun_prop
  let S : Set (Ine (F := E) A) :=
    (U' : Set _) ∩ {σ | (r σ : Matrix n n (Qbar l)) = exp (tval t σ • N)}
  have hS : IsClosed ((fun σ => (t σ).toAdd) '' S) :=
    (((U'.isClosed_of_isOpen hU').inter
      (isClosed_eq (hr.comp continuous_subtype_val) ce)).isCompact.image ct).isClosed
  have hk : ∀ k : ℕ, σ₀ ^ k ∈ S := fun k => ⟨pow_mem h0 k, by
    show _ = _
    induction k with
    | zero => simp
    | succ k ih =>
      rw [_root_.pow_succ, tval_mul, exp_add_smul hNn, ← ih, ← e0, Subgroup.coe_mul, map_mul,
        Units.val_mul]⟩
  have hall : ∀ c : ℤ_[l], c * (t σ₀).toAdd ∈ (fun σ => (t σ).toAdd) '' S := fun c =>
    PadicInt.denseRange_natCast.induction_on c (hS.preimage (continuous_mul_const _))
      fun k => ⟨_, hk k, by simp⟩
  have h3 : (t σ₀).toAdd ≠ 0 := fun e => h0' (by simp [tval, e])
  refine ⟨N, .of_nhds hNn ?_⟩
  filter_upwards [hU'.mem_nhds U'.one_mem, (isOpen_lt ct.norm continuous_const).mem_nhds
    (show ‖(t 1).toAdd‖ < ‖(t σ₀).toAdd‖ by simpa using h3)] with σ hσ hlt
  obtain ⟨c, hc⟩ : (t σ₀).toAdd ∣ (t σ).toAdd := by
    rcases ValuationRing.dvd_total (t σ₀).toAdd (t σ).toAdd with H | ⟨c, hc⟩
    · exact H
    · rw [hc, norm_mul] at hlt
      exact absurd (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one c)) hlt.not_ge
  obtain ⟨τ, hτ, e⟩ := hall c
  have e' : t τ = t σ := Multiplicative.toAdd.injective (e.trans (by rw [hc, mul_comm]))
  rw [key σ hσ τ hτ.1 e'.symm, hτ.2, tval, tval, e']

section Laws

variable (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ)
  (hr : Continuous fun g => (r g : Matrix n n (Qbar l)))

include hl hr in

/- English proof (translation)
Take `⟨x, hx⟩` from `(exists_isWDOf_iff (h := h) (ι := ι) hl (isTameChar_tameL h hl)).mpr (exists_isMonodromy h hl (isTameChar_tameL h hl) hr)`. Rewrite using `[hx.wdOf_eq hl]` and apply the resulting hypothesis.
-/
theorem isWDOf_wdOf : IsWDOf ι r (wdOf h hl ι r) := by
  obtain ⟨x, hx⟩ := (exists_isWDOf_iff (h := h) (ι := ι) hl (isTameChar_tameL h hl)).mpr
    (exists_isMonodromy h hl (isTameChar_tameL h hl) hr)
  rwa [hx.wdOf_eq hl]

include hr in

/- English proof (translation)
The claim follows from `(exists_isMonodromy h hl (isTameChar_tameL h hl) hr).choose_spec.unr_wdOf_iff hl (isTameChar_tameL h hl) ι`.
-/
theorem unr_wdOf_iff : (wdOf h hl ι r).unr ↔ ∀ σ ∈ Ine (F := E) A, r σ = 1 :=
  (exists_isMonodromy h hl (isTameChar_tameL h hl) hr).choose_spec.unr_wdOf_iff hl
    (isTameChar_tameL h hl) ι

include hr in

/- English proof (translation)
The claim follows from `(exists_isMonodromy h hl (isTameChar_tameL h hl) hr).choose_spec.charPol_wdOf hl (isTameChar_tameL h hl) ι g`.
-/
theorem charPol_wdOf (g : Weil h) :
    (wdOf h hl ι r).charPol g = (r g : Matrix n n (Qbar l)).charpoly.map ι.toRingHom :=
  (exists_isMonodromy h hl (isTameChar_tameL h hl) hr).choose_spec.charPol_wdOf hl
    (isTameChar_tameL h hl) ι g

include hr in

/- English proof (translation)
Rewrite using `[WD.inePol_of_mem_Ine _ hσ, charPol_wdOf hl ι hr, coe_ineIncl]`.
-/
theorem inePol_wdOf {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) :
    (r σ : Matrix n n (Qbar l)).charpoly.map ι.toRingHom = (wdOf h hl ι r).inePol σ := by
  rw [WD.inePol_of_mem_Ine _ hσ, charPol_wdOf hl ι hr, coe_ineIncl]

open Pointwise in
omit [IsAlgClosure E Ω] in

/- English proof (translation)
Establish `hm : ∀ x, g x ∈ g • A ↔ x ∈ A` using `fun x => ValuationSubring.smul_mem_pointwise_smul_iff`. Use `⟨?_, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1 : σ • g • A = g • A` using `hσ.1 show (g⁻¹ * σ * g) • A = A`. Rewrite using `[mul_smul, mul_smul, h1, inv_smul_smul]`. Establish `h1` using `hσ.2 (g x) (by rwa [ValuationSubring.valuation_le_one_iff, hm, ← ValuationSubring.valuation_le_one_iff])`.

Establish `e : σ (g x) - g x ^ q = g ((g⁻¹ * σ * g) x - x ^ q)`. Rewrite using `[map_sub, map_pow, AlgEquiv.mul_apply, AlgEquiv.mul_apply, mul_inv_apply]`. Rewrite `h1` using `[e, valuation_lt_one_iff', ← map_inv₀, hm, hm, map_eq_zero_iff _ g.injective, ← valuation_lt_one_iff']`. Then use the resulting hypothesis.
-/
theorem MonodromyThm.isFrob_conj {q : ℕ} {g σ : G E Ω} (hσ : IsFrob (g • A) q σ) :
    IsFrob A q (g⁻¹ * σ * g) := by
  have hm : ∀ x, g x ∈ g • A ↔ x ∈ A := fun x => ValuationSubring.smul_mem_pointwise_smul_iff
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h1, inv_smul_smul]
  · have h1 := hσ.2 (g x) (by rwa [ValuationSubring.valuation_le_one_iff, hm,
      ← ValuationSubring.valuation_le_one_iff])
    have e : σ (g x) - g x ^ q = g ((g⁻¹ * σ * g) x - x ^ q) := by
      rw [map_sub, map_pow, AlgEquiv.mul_apply, AlgEquiv.mul_apply, mul_inv_apply]
    rwa [e, valuation_lt_one_iff', ← map_inv₀, hm, hm, map_eq_zero_iff _ g.injective,
      ← valuation_lt_one_iff'] at h1

include hr in

/- English proof (translation)
Take `⟨g, rfl⟩` from `exists_smul_eq_of_isPlaceOver h hB`. Establish `h1` using `isFrob_conj hσ`. Rewrite using `[← WD.eig_eq_frobEig hu (φ := ⟨_, mem_Weil_of_isFrob h h1⟩) (deg_eq_one_iff.mpr h1), ← WD.charPol_eq_prod, charPol_wdOf hl ι hr]`. Use `congr 1`. Use `show _ = ((r (g⁻¹ * σ * g) : GL n (Qbar l)) : Matrix n n (Qbar l)).charpoly`.

Rewrite using `[map_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, ← map_mul, mul_inv_cancel_left]`.
-/
theorem frobEig_wdOf (hu : (wdOf h hl ι r).unr) {B : ValuationSubring Ω} {σ : G E Ω}
    (hB : IsPlaceOver B w) (hσ : IsFrob B (normV w) σ) :
    (r σ : Matrix n n (Qbar l)).charpoly.map ι.toRingHom =
      (((wdOf h hl ι r).frobEig).map fun α => X - C α).prod := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver h hB
  have h1 := isFrob_conj hσ
  rw [← WD.eig_eq_frobEig hu (φ := ⟨_, mem_Weil_of_isFrob h h1⟩) (deg_eq_one_iff.mpr h1),
    ← WD.charPol_eq_prod, charPol_wdOf hl ι hr]
  congr 1
  show _ = ((r (g⁻¹ * σ * g) : GL n (Qbar l)) : Matrix n n (Qbar l)).charpoly
  rw [map_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, ← map_mul,
    mul_inv_cancel_left]

include hr in

/- English proof (translation)
Establish `ht` using `isTameChar_tameL h hl`. Take `⟨N, hN⟩` from `exists_isMonodromy h hl ht hr`. Rewrite using `[hN.weilDeligneParam_monodromy_eq_zero_iff hl ht]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`.

Use `((isMonodromy_zero_iff (h := h)).mp hN).finite_range.subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨σ, hσ, rfl⟩`. Conclude with `⟨⟨σ, hσ⟩, rfl⟩`. Introduce `H`. Use `hN.unique ht (.of_nhds IsNilpotent.zero ?_)` and prove the remaining obligations.

Establish `hc : IsClosed (Units.val '' (r '' (Ine (F` using `E) A : Set (G E Ω))) \ {1}) := ((H.image _).sdiff).isClosed`. Use `filter_upwards [(hc.isOpen_compl.preimage (hr.comp continuous_subtype_val)).mem_nhds (show (1 : Ine (F := E) A) ∈ _ by simp)] with σ hσ`. Assume the negation of the conclusion as `hne`. Conclude with `hσ ⟨⟨_, ⟨σ, σ.2, rfl⟩, rfl⟩, by simpa using hne⟩`.
-/
theorem weilDeligneParam_monodromy_eq_zero_iff :
    (wdOf h hl ι r).mono0 ↔ (r '' (Ine (F := E) A : Set (G E Ω))).Finite := by
  have ht := isTameChar_tameL h hl
  obtain ⟨N, hN⟩ := exists_isMonodromy h hl ht hr
  rw [hN.weilDeligneParam_monodromy_eq_zero_iff hl ht]
  constructor
  · rintro rfl
    refine ((isMonodromy_zero_iff (h := h)).mp hN).finite_range.subset ?_
    rintro _ ⟨σ, hσ, rfl⟩
    exact ⟨⟨σ, hσ⟩, rfl⟩
  · intro H
    refine hN.unique ht (.of_nhds IsNilpotent.zero ?_)
    have hc : IsClosed (Units.val '' (r '' (Ine (F := E) A : Set (G E Ω))) \ {1}) :=
      ((H.image _).sdiff).isClosed
    filter_upwards [(hc.isOpen_compl.preimage (hr.comp continuous_subtype_val)).mem_nhds
      (show (1 : Ine (F := E) A) ∈ _ by simp)] with σ hσ
    by_contra hne
    exact hσ ⟨⟨_, ⟨σ, σ.2, rfl⟩, rfl⟩, by simpa using hne⟩

end Laws

variable (h) in

/- English proof (translation)
Assemble the required witnesses or components as `⟨by simp [lpDim_wdOf], fun hr => ⟨fun _ ht => exists_isMonodromy h hl ht hr, isWDOf_wdOf hl ι hr, unr_wdOf_iff hl ι hr, fun hu _ _ hB hσ => frobEig_wdOf hl ι hr hu hB hσ, fun _ hσ => inePol_wdOf hl ι hr hσ, weilDeligneParam_monodromy_eq_zero_iff hl ι hr⟩⟩`.
-/
theorem wdOf_laws (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ) {a : ℕ}
    (r : G E Ω →* GL (Fin a) (Qbar l)) :
    (wdOf h hl ι r).lpDim = a ∧
    (Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l))) →
      (∀ t : Ine (F := E) A →* Multiplicative ℤ_[l], IsTameChar t → ∃ N, IsMonodromy t r N) ∧
      IsWDOf ι r (wdOf h hl ι r) ∧
      ((wdOf h hl ι r).unr ↔ ∀ σ ∈ Ine (F := E) A, r σ = 1) ∧
      ((wdOf h hl ι r).unr → ∀ (B : ValuationSubring Ω) (σ : G E Ω), IsPlaceOver B w →
        IsFrob B (normV w) σ →
        (r σ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
          (((wdOf h hl ι r).frobEig).map fun α => X - C α).prod) ∧
      (∀ σ ∈ Ine (F := E) A, (r σ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
        (wdOf h hl ι r).inePol σ) ∧
      ((wdOf h hl ι r).mono0 ↔ (r '' (Ine (F := E) A : Set (G E Ω))).Finite)) :=
  ⟨by simp [lpDim_wdOf], fun hr => ⟨fun _ ht => exists_isMonodromy h hl ht hr, isWDOf_wdOf hl ι hr,
    unr_wdOf_iff hl ι hr, fun hu _ _ hB hσ => frobEig_wdOf hl ι hr hu hB hσ,
    fun _ hσ => inePol_wdOf hl ι hr hσ, weilDeligneParam_monodromy_eq_zero_iff hl ι hr⟩⟩

end GlobalTheory.WeilDeligne
