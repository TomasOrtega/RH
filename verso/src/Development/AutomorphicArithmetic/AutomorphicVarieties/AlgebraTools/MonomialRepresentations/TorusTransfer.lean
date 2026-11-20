import Mathlib

open Polynomial Matrix

/- English proof (translation)
Use `set q := p.map (algebraMap L p.SplittingField) with hq`. Establish `hqm : q.Monic` using `hp.map _`. Establish `hqd : q.natDegree = n`. Rewrite using `[hq, hp.natDegree_map, hn]`. Establish `hspl : q.Splits` using `SplittingField.splits p`.

Establish `hq0 : q ≠ 0` using `hqm.ne_zero`. Establish `hdeg : (derivative q).natDegree ≤ n` using `(natDegree_derivative_le q).trans (by rw [hqd]; exact Nat.sub_le n 1)`. Establish `hres : algebraMap L p.SplittingField (p.resultant (derivative p) n n) = (q.roots.map fun x => (derivative q).eval x).prod`. Rewrite using `[← resultant_map_map, ← derivative_map, ← hq]`. Establish `h` using `resultant_eq_prod_eval q (derivative q) n hdeg hspl`.

Rewrite `h` using `[hqd, hqm.leadingCoeff, one_pow, one_mul]`. Conclude with `h`. Rewrite using `[← separable_map (algebraMap L p.SplittingField), ← hq, ← nodup_roots_iff_of_splits hq0 hspl, ne_eq, ← map_eq_zero (algebraMap L p.SplittingField), hres, Multiset.prod_eq_zero_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hnd hz`.

Take `⟨α, hα, hα0⟩` from `Multiset.mem_map.1 hz`. Establish `hc` using `(Multiset.nodup_iff_count_le_one.1 hnd) α`. Rewrite `hc` using `[count_roots]`. Establish `hlt : 1 < rootMultiplicity α q` using `(one_lt_rootMultiplicity_iff_isRoot hq0).2 ⟨(mem_roots hq0).1 hα, hα0⟩`. Use linear arithmetic over natural numbers and integers.

Introduce `hne`. Rewrite using `[Multiset.nodup_iff_count_le_one]`. Introduce `α`. Rewrite using `[count_roots]`. Assume the negation of the conclusion as `hlt`.

Use `push_neg at hlt`. Take `⟨hr, hr'⟩` from `(one_lt_rootMultiplicity_iff_isRoot hq0).1 hlt`. Conclude with `hne (Multiset.mem_map.2 ⟨α, (mem_roots hq0).2 hr, hr'⟩)`.
-/
private lemma torusTransfer_sep_iff {L : Type*} [Field L] (p : L[X]) (hp : p.Monic) (n : ℕ)
    (hn : p.natDegree = n) :
    p.Separable ↔ p.resultant (derivative p) n n ≠ 0 := by
  classical
  set q := p.map (algebraMap L p.SplittingField) with hq
  have hqm : q.Monic := hp.map _
  have hqd : q.natDegree = n := by
    rw [hq, hp.natDegree_map, hn]
  have hspl : q.Splits := SplittingField.splits p
  have hq0 : q ≠ 0 := hqm.ne_zero
  have hdeg : (derivative q).natDegree ≤ n :=
    (natDegree_derivative_le q).trans (by rw [hqd]; exact Nat.sub_le n 1)
  have hres : algebraMap L p.SplittingField (p.resultant (derivative p) n n) =
      (q.roots.map fun x => (derivative q).eval x).prod := by
    rw [← resultant_map_map, ← derivative_map, ← hq]
    have h := resultant_eq_prod_eval q (derivative q) n hdeg hspl
    rw [hqd, hqm.leadingCoeff, one_pow, one_mul] at h
    exact h
  rw [← separable_map (algebraMap L p.SplittingField), ← hq, ← nodup_roots_iff_of_splits hq0 hspl,
    ne_eq, ← map_eq_zero (algebraMap L p.SplittingField), hres, Multiset.prod_eq_zero_iff]
  constructor
  · intro hnd hz
    obtain ⟨α, hα, hα0⟩ := Multiset.mem_map.1 hz
    have hc := (Multiset.nodup_iff_count_le_one.1 hnd) α
    rw [count_roots] at hc
    have hlt : 1 < rootMultiplicity α q :=
      (one_lt_rootMultiplicity_iff_isRoot hq0).2 ⟨(mem_roots hq0).1 hα, hα0⟩
    omega
  · intro hne
    rw [Multiset.nodup_iff_count_le_one]
    intro α
    rw [count_roots]
    by_contra hlt
    push_neg at hlt
    obtain ⟨hr, hr'⟩ := (one_lt_rootMultiplicity_iff_isRoot hq0).1 hlt
    exact hne (Multiset.mem_map.2 ⟨α, (mem_roots hq0).2 hr, hr'⟩)

/- English proof (translation)
Establish `hP : ∀ P : K[X], ∑ s ∈ S, c s * P.eval (v s) = 0`. Introduce `P`. Proceed by induction on `P using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Simplify using `only [eval_add, mul_add, Finset.sum_add_distrib, hp, hq, add_zero]`.

Consider the case `monomial n a`. Simplify using `only [eval_monomial]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun s _ => by ring`.

Use `_ = 0 := by rw [h n, mul_zero]`. Use `set P : K[X] := ∏ j' ∈ (S.image v).erase j, (X - C j') with hPdef`. Establish `hev : ∀ s ∈ S, P.eval (v s) = if v s = j then P.eval j else 0`. Introduce `s hs`. Use `split_ifs with hsj`.

Rewrite using `[hsj]`. Rewrite using `[hPdef, eval_prod]`. Apply `Finset.prod_eq_zero (i := v s)` to reduce the goal to its premises. Conclude with `Finset.mem_erase.2 ⟨hsj, Finset.mem_image_of_mem v hs⟩`. Simplify using the standard rewrite rules.

Establish `hPj : P.eval j ≠ 0`. Rewrite using `[hPdef, eval_prod]`. Conclude with `Finset.prod_ne_zero_iff.2 fun j' hj' => by`. Rewrite using `[eval_sub, eval_X, eval_C]`. Conclude with `sub_ne_zero.2 (Finset.ne_of_mem_erase hj').symm`.

Establish `h0` using `hP P`. Establish `h1 : ∑ s ∈ S, c s * P.eval (v s) = ∑ s ∈ S, if v s = j then c s * P.eval j else 0` using `Finset.sum_congr rfl fun s hs => by rw [hev s hs, mul_ite, mul_zero]`. Rewrite `h0` using `[h1, ← Finset.sum_filter, ← Finset.sum_mul]`. Conclude with `(mul_eq_zero.1 h0).resolve_right hPj`.
-/
private lemma torusTransfer_fiber {K : Type*} [Field K] {σ : Type*} [DecidableEq K]
    (S : Finset σ) (c : σ → K) (v : σ → K) (h : ∀ m : ℕ, ∑ s ∈ S, c s * v s ^ m = 0) (j : K) :
    ∑ s ∈ S with v s = j, c s = 0 := by
  classical
  have hP : ∀ P : K[X], ∑ s ∈ S, c s * P.eval (v s) = 0 := by
    intro P
    induction P using Polynomial.induction_on' with
    | add p q hp hq =>
      simp only [eval_add, mul_add, Finset.sum_add_distrib, hp, hq, add_zero]
    | monomial n a =>
      simp only [eval_monomial]
      calc ∑ s ∈ S, c s * (a * v s ^ n) = a * ∑ s ∈ S, c s * v s ^ n := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun s _ => by ring
        _ = 0 := by rw [h n, mul_zero]
  set P : K[X] := ∏ j' ∈ (S.image v).erase j, (X - C j') with hPdef
  have hev : ∀ s ∈ S, P.eval (v s) = if v s = j then P.eval j else 0 := by
    intro s hs
    split_ifs with hsj
    · rw [hsj]
    · rw [hPdef, eval_prod]
      apply Finset.prod_eq_zero (i := v s)
      · exact Finset.mem_erase.2 ⟨hsj, Finset.mem_image_of_mem v hs⟩
      · simp
  have hPj : P.eval j ≠ 0 := by
    rw [hPdef, eval_prod]
    exact Finset.prod_ne_zero_iff.2 fun j' hj' => by
      rw [eval_sub, eval_X, eval_C]
      exact sub_ne_zero.2 (Finset.ne_of_mem_erase hj').symm
  have h0 := hP P
  have h1 : ∑ s ∈ S, c s * P.eval (v s) = ∑ s ∈ S, if v s = j then c s * P.eval j else 0 :=
    Finset.sum_congr rfl fun s hs => by rw [hev s hs, mul_ite, mul_zero]
  rw [h1, ← Finset.sum_filter, ← Finset.sum_mul] at h0
  exact (mul_eq_zero.1 h0).resolve_right hPj

/- English proof (translation)
Use `set T : RatFunc K := RatFunc.X with hTdef`. Establish `hT : T ≠ 0` using `RatFunc.X_ne_zero`. Establish `hpow : ∀ μ : ι →₀ ℕ, ∏ i, (T ^ w i) ^ μ i = T ^ (∑ i, (μ i : ℤ) * w i)`. Introduce `μ`. Establish `key : ∀ s : Finset ι, ∏ i ∈ s, (T ^ w i) ^ μ i = T ^ (∑ i ∈ s, (μ i : ℤ) * w i)`.

Introduce `s`. Use `Finset.induction_on s (by simp) ?_` and prove the remaining obligations. Introduce `i s hi ih`. Rewrite using `[Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ hT, ih, ← zpow_natCast, ← _root_.zpow_mul, mul_comm (w i)]`. Conclude with `key _`.

Establish `hfib : ∀ j : K, ∑ μ ∈ F.support with (∏ i, (a i : K) ^ μ i) = j, F.coeff μ = 0`. Introduce `j`. Apply `torusTransfer_fiber F.support (fun μ => F.coeff μ) (fun μ => ∏ i, (a i : K) ^ μ i)` to reduce the goal to its premises. Introduce `m`. Establish `hm` using `h m`.

Rewrite `hm` using `[MvPolynomial.eval_eq']`. Rewrite using `[← hm]`. Use `Finset.sum_congr rfl fun μ _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_pow]`. Use `congr 1`.

Conclude with `Finset.prod_congr rfl fun i _ => by ring`. Establish `hterm : ∀ μ : ι →₀ ℕ, algebraMap K (RatFunc K) (F.coeff μ) * ∏ i, (T ^ w i) ^ μ i = algebraMap K (RatFunc K) (F.coeff μ) * T ^ (∑ i, (μ i : ℤ) * w i)` using `fun μ => by rw [hpow]`. Rewrite using `[MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq', Finset.sum_congr rfl fun μ _ => hterm μ, ← Finset.sum_fiberwise_of_maps_to (t := F.support.image fun μ => ∏ i, (a i : K) ^ μ i) (g := fun μ => ∏ i, (a i : K) ^ μ i) (fun μ hμ => Finset.mem_image_of_mem _ hμ) (fun μ => algebraMap …`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j _`.

Distinguish the cases in `hne : (F.support.filter fun μ => ∏ i, (a i : K) ^ μ i = j).Nonempty`. Take `⟨μ0, hμ0⟩` from `hne`. Establish `hsame : ∀ μ ∈ F.support.filter (fun μ => ∏ i, (a i : K) ^ μ i = j), algebraMap K (RatFunc K) (F.coeff μ) * T ^ (∑ i, (μ i : ℤ) * w i) = algebraMap K (RatFunc K) (F.coeff μ) * T ^ (∑ i, (μ0 i : ℤ) * w i)`. Introduce `μ hμ`. Rewrite `hμ`, `hμ0` using `[Finset.mem_filter]`.

Establish `hv : (∏ i, (a i : K) ^ μ i) = ∏ i, (a i : K) ^ μ0 i` using `hμ.2.trans hμ0.2.symm`. Establish `hvU : ∏ i, a i ^ μ i = ∏ i, a i ^ μ0 i`. Apply `Units.ext` to reduce the goal to its premises. Use `push_cast`. Conclude with `hv`.

Establish `h1 : ∏ i, a i ^ ((μ i : ℤ) - μ0 i) = 1`. Simplify using `only [_root_.zpow_sub, zpow_natCast]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_inv_distrib, hvU, mul_inv_cancel]`. Establish `h2` using `hw _ h1`. Simplify using `only [sub_mul, Finset.sum_sub_distrib] at h2`.

Rewrite using `[sub_eq_zero.1 h2]`. Rewrite using `[Finset.sum_congr rfl hsame, ← Finset.sum_mul, ← map_sum, hfib j, map_zero, zero_mul]`. Rewrite using `[Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty]`.
-/
private lemma torusTransfer_key {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    (a : ι → Kˣ) (w : ι → ℤ)
    (hw : ∀ m : ι → ℤ, ∏ i, a i ^ m i = 1 → ∑ i, m i * w i = 0)
    (F : MvPolynomial ι K)
    (h : ∀ m : ℕ, MvPolynomial.eval (fun i => (a i : K) ^ m) F = 0) :
    MvPolynomial.eval₂Hom (algebraMap K (RatFunc K))
      (fun i => (RatFunc.X : RatFunc K) ^ w i) F = 0 := by
  classical
  set T : RatFunc K := RatFunc.X with hTdef
  have hT : T ≠ 0 := RatFunc.X_ne_zero
  have hpow : ∀ μ : ι →₀ ℕ, ∏ i, (T ^ w i) ^ μ i = T ^ (∑ i, (μ i : ℤ) * w i) := by
    intro μ
    have key : ∀ s : Finset ι, ∏ i ∈ s, (T ^ w i) ^ μ i = T ^ (∑ i ∈ s, (μ i : ℤ) * w i) := by
      intro s
      refine Finset.induction_on s (by simp) ?_
      intro i s hi ih
      rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ hT, ih, ← zpow_natCast,
        ← _root_.zpow_mul, mul_comm (w i)]
    exact key _
  have hfib : ∀ j : K, ∑ μ ∈ F.support with (∏ i, (a i : K) ^ μ i) = j, F.coeff μ = 0 := by
    intro j
    apply torusTransfer_fiber F.support (fun μ => F.coeff μ) (fun μ => ∏ i, (a i : K) ^ μ i)
    intro m
    have hm := h m
    rw [MvPolynomial.eval_eq'] at hm
    rw [← hm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Finset.prod_pow]
    congr 1
    exact Finset.prod_congr rfl fun i _ => by ring
  have hterm : ∀ μ : ι →₀ ℕ, algebraMap K (RatFunc K) (F.coeff μ) * ∏ i, (T ^ w i) ^ μ i =
      algebraMap K (RatFunc K) (F.coeff μ) * T ^ (∑ i, (μ i : ℤ) * w i) := fun μ => by rw [hpow]
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq', Finset.sum_congr rfl fun μ _ => hterm μ,
    ← Finset.sum_fiberwise_of_maps_to (t := F.support.image fun μ => ∏ i, (a i : K) ^ μ i)
      (g := fun μ => ∏ i, (a i : K) ^ μ i) (fun μ hμ => Finset.mem_image_of_mem _ hμ)
      (fun μ => algebraMap K (RatFunc K) (F.coeff μ) * T ^ (∑ i, (μ i : ℤ) * w i))]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hne : (F.support.filter fun μ => ∏ i, (a i : K) ^ μ i = j).Nonempty
  · obtain ⟨μ0, hμ0⟩ := hne
    have hsame : ∀ μ ∈ F.support.filter (fun μ => ∏ i, (a i : K) ^ μ i = j),
        algebraMap K (RatFunc K) (F.coeff μ) * T ^ (∑ i, (μ i : ℤ) * w i) =
          algebraMap K (RatFunc K) (F.coeff μ) * T ^ (∑ i, (μ0 i : ℤ) * w i) := by
      intro μ hμ
      rw [Finset.mem_filter] at hμ hμ0
      have hv : (∏ i, (a i : K) ^ μ i) = ∏ i, (a i : K) ^ μ0 i := hμ.2.trans hμ0.2.symm
      have hvU : ∏ i, a i ^ μ i = ∏ i, a i ^ μ0 i := by
        apply Units.ext
        push_cast
        exact hv
      have h1 : ∏ i, a i ^ ((μ i : ℤ) - μ0 i) = 1 := by
        simp only [_root_.zpow_sub, zpow_natCast]
        rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, hvU, mul_inv_cancel]
      have h2 := hw _ h1
      simp only [sub_mul, Finset.sum_sub_distrib] at h2
      rw [sub_eq_zero.1 h2]
    rw [Finset.sum_congr rfl hsame, ← Finset.sum_mul, ← map_sum, hfib j, map_zero, zero_mul]
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty]

/- English proof (translation)
Establish `hM : (x.map (MvPolynomial.C : K →+* MvPolynomial ι K) * diagonal MvPolynomial.X).map (MvPolynomial.eval₂Hom f t) = x.map f * diagonal t`. Use extensionality with `i j`. Simplify using `[Matrix.mul_diagonal]`. Rewrite using `[← resultant_map_map, ← derivative_map, ← charpoly_map, hM]`. Conclude with `torusTransfer_sep_iff _ (charpoly_monic _) _ (charpoly_natDegree_eq_dim _)`.
-/
private lemma torusTransfer_spec {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Matrix ι ι K) {L : Type*} [Field L] (f : K →+* L) (t : ι → L) :
    (x.map f * diagonal t).charpoly.Separable ↔
      MvPolynomial.eval₂Hom f t
        ((x.map (MvPolynomial.C : K →+* MvPolynomial ι K) * diagonal MvPolynomial.X).charpoly.resultant
          (derivative (x.map (MvPolynomial.C : K →+* MvPolynomial ι K)
            * diagonal MvPolynomial.X).charpoly) (Fintype.card ι) (Fintype.card ι)) ≠ 0 := by
  have hM : (x.map (MvPolynomial.C : K →+* MvPolynomial ι K) * diagonal MvPolynomial.X).map
      (MvPolynomial.eval₂Hom f t) = x.map f * diagonal t := by
    ext i j
    simp [Matrix.mul_diagonal]
  rw [← resultant_map_map, ← derivative_map, ← charpoly_map, hM]
  exact torusTransfer_sep_iff _ (charpoly_monic _) _ (charpoly_natDegree_eq_dim _)

/- English proof (translation)
Introduce `K _ ι _ _ x a w hw hsep`. Establish `hne` using `(torusTransfer_spec x (algebraMap K (RatFunc K)) (fun i => (RatFunc.X : RatFunc K) ^ w i)).1 hsep`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Apply `hne` to reduce the goal to its premises.

Apply `torusTransfer_key a w hw` to reduce the goal to its premises. Introduce `m`. Establish `hx : x.map (RingHom.id K) = x`. Use extensionality with `i j`. Both sides reduce to the same expression.

Establish `hs` using `torusTransfer_spec x (RingHom.id K) (fun i => (a i : K) ^ m)`. Rewrite `hs` using `[hx]`. Conclude with `not_not.1 (mt hs.2 (hall m))`.
-/
theorem UpperTheory.V.AlgebraTools.torusTransfer :
    ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (x : Matrix ι ι K) (a : ι → Kˣ) (w : ι → ℤ),
      (∀ m : ι → ℤ, ∏ i, a i ^ m i = 1 → ∑ i, m i * w i = 0) →
      (x.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w i)).charpoly.Separable →
      ∃ m : ℕ, (x * diagonal (fun i => (a i : K) ^ m)).charpoly.Separable := by
  classical
  intro K _ ι _ _ x a w hw hsep
  have hne := (torusTransfer_spec x (algebraMap K (RatFunc K))
    (fun i => (RatFunc.X : RatFunc K) ^ w i)).1 hsep
  by_contra hall
  push_neg at hall
  apply hne
  apply torusTransfer_key a w hw
  intro m
  have hx : x.map (RingHom.id K) = x := by
    ext i j
    rfl
  have hs := torusTransfer_spec x (RingHom.id K) (fun i => (a i : K) ^ m)
  rw [hx] at hs
  exact not_not.1 (mt hs.2 (hall m))
