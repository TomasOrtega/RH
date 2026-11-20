import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomExtDense
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism GlobalTheory.CrysEval
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysEval

/- English proof (translation)
Rewrite using `[← map_natCast (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧), coeff_C_mul, ← map_natCast (C : K →+* K⟦X⟧), coeff_C_mul]`.
-/
theorem coeff_coeff_natCast_mul {K : Type} [CommRing K] (m : ℕ) (q : K⟦X⟧⟦X⟧) (i n : ℕ) :
    coeff n (coeff i ((m : K⟦X⟧⟦X⟧) * q)) = (m : K) * coeff n (coeff i q) := by
  rw [← map_natCast (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧), coeff_C_mul, ← map_natCast (C : K →+* K⟦X⟧), coeff_C_mul]

/- English proof (translation)
Introduce `l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t F hF r`. Establish `hK0` using `charZero_K (l := l) (K := K)`. Take `⟨w, hw, hFw⟩` from `hF`. Set `N : ℕ × ℕ → ℕ` to `fun x => x.1.factorial * (x.2 / e).factorial`. Establish `hNpos : ∀ x, N x ≠ 0` using `fun x => Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)`.

Establish `hN0 : ∀ x, (N x : K) ≠ 0` using `fun x => Nat.cast_ne_zero.2 (hNpos x)`. Set `ser : (ℕ × ℕ → Wq l a) → ZMod a → K⟦X⟧⟦X⟧` to `fun v τ => PowerSeries.mk fun i => PowerSeries.mk fun n => embK K t τ (v (i, n)) / (N (i, n) : K)`. Establish `coeff_ser : ∀ v τ i n, coeff n (coeff i (ser v τ)) = embK K t τ (v (i, n)) / (N (i, n) : K)`. Introduce `v τ i n`. Simplify using `[ser]`.

Establish `ser_mem : ∀ v, LTo0 l v → ser v ∈ PPSet t K e`. Introduce `v hv`. Use `⟨v, hv, fun τ i n => ?_⟩` and prove the remaining obligations. Rewrite using `[coeff_ser, mul_div_cancel₀ _ (hN0 (i, n))]`. Both sides reduce to the same expression.

Establish `coeff_F : ∀ τ i n, coeff n (coeff i (F τ)) = embK K t τ (w (i, n)) / (N (i, n) : K)`. Introduce `τ i n`. Rewrite using `[eq_div_iff (hN0 _), mul_comm]`. Conclude with `hFw τ i n`. Establish `hfin : {x | ¬ (l : Wq l a) ^ r ∣ w x}.Finite` using `Filter.eventually_cofinite.1 (hw r)`.

Set `s` to `hfin.toFinset`. Establish `mem_s : ∀ x, x ∈ s ↔ ¬ (l : Wq l a) ^ r ∣ w x` using `fun x => by simp [s]`. Set `c : ℕ × ℕ → Wq l a` to `fun x => if h : (l : Wq l a) ^ r ∣ w x then h.choose else 0`. Set `w₁ : ℕ × ℕ → Wq l a` to `fun x => if x ∈ s then w x else 0`. Establish `hsplit : ∀ x, w x = w₁ x + (l : Wq l a) ^ r * c x`.

Introduce `x`. Distinguish the cases in `h : (l : Wq l a) ^ r ∣ w x`. Establish `hx : x ∉ s` using `fun hx => (mem_s x).1 hx h`. Simplify using `only [w₁, c, hx, if_false, dif_pos h, zero_add]`. Conclude with `h.choose_spec`.

Establish `hx : x ∈ s` using `(mem_s x).2 h`. Simplify using `[w₁, c, hx, h]`. Establish `hw₁ : LTo0 l w₁`. Introduce `m`. Use `Filter.eventually_cofinite.2 (hfin.subset fun x hx => ?_)` and prove the remaining obligations.

Simplify using `only [Set.mem_setOf_eq] at hx ⊢`. Introduce `hd`. Apply `hx` to reduce the goal to its premises. Establish `: x ∉ s` using `fun hx' => (mem_s x).1 hx' hd`. Simplify using `[w₁, this]`.

Establish `hc : LTo0 l c`. Introduce `m`. Use `filter_upwards [hw (m + r)] with x hx`. Establish `h : (l : Wq l a) ^ r ∣ w x` using `dvd_trans (pow_dvd_pow _ (Nat.le_add_left r m)) hx`. Take `⟨d, hd⟩` from `hx`.

Establish `hcx : c x = h.choose` using `dif_pos h`. Establish `hspec` using `h.choose_spec`. Use `⟨d, ?_⟩` and prove the remaining obligations. Rewrite using `[hcx]`. Establish `hl0 : l ^ r ≠ 0` using `pow_ne_zero _ (Fact.out : l.Prime).ne_zero`.

Use `wq_nat_cancel (K := K) t hl0 (x := h.choose - (l : Wq l a) ^ m * d) (by` as an intermediate fact. Use `push_cast`. Take the linear combination `hd - hspec)`. Conclude with `sub_eq_zero.1 this`. Set `nn : ℕ` to `∏ x ∈ s, N x`.

Set `b : Bp l a` to `∑ x ∈ s, Polynomial.monomial x.1 (Polynomial.monomial x.2 ((nn / N x) • w x))`. Establish `coeff_b : ∀ i n, (b.coeff i).coeff n = if (i, n) ∈ s then (nn / N (i, n)) • w (i, n) else 0`. Introduce `i n`. Simplify using `only [b, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]`. Rewrite using `[Finset.sum_congr rfl (g := fun x => if x = (i, n) then (nn / N x) • w x else 0)]`.

Conclude with `Finset.sum_ite_eq' _ _ _`. Introduce `x _`. Take `⟨x1, x2⟩` from `x`. Apply the tactic sequence `by_cases h1 : x1 = i <;> by_cases h2 : x2 = n <;> simp [h1, h2, Polynomial.coeff_monomial, Prod.ext_iff] <;> first | done | (subst h1; simp_all) | (split_ifs <;> simp_all)`. Use `⟨nn, b, ser w₁, ser c, Finset.prod_ne_zero_iff.2 fun x _ => hNpos x, ser_mem _ hw₁, ser_mem _ hc, ?_, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `τ`. Use `PowerSeries.ext fun i => PowerSeries.ext fun n => ?_` and prove the remaining obligations. Rewrite using `[Pi.mul_apply, Pi.natCast_apply, coeff_coeff_natCast_mul, coeff_ser, coeff_iotaP, coeff_b]`. Use `split_ifs with hx`. Establish `hdvd : N (i, n) ∣ nn` using `Finset.dvd_prod_of_mem N hx`.

Simplify using `only [w₁, hx, if_true]`. Rewrite using `[map_nsmul, nsmul_eq_mul, Nat.cast_div hdvd (hN0 _)]`. Clear the denominators using the available nonvanishing facts. Simplify using `[w₁, hx]`. Use function extensionality and compare the values at `τ`.

Use `PowerSeries.ext fun i => PowerSeries.ext fun n => ?_` and prove the remaining obligations. Rewrite using `[← Nat.cast_pow, Pi.add_apply, Pi.mul_apply, Pi.natCast_apply, map_add, map_add, coeff_coeff_natCast_mul, coeff_F, coeff_ser, coeff_ser, hsplit (i, n), map_add, map_mul, map_pow, map_natCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_poly_approx_PPSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ PPSet t K e, ∀ r : ℕ, ∃ (n : ℕ) (b : Bp l a) (p h : ZMod a → K⟦X⟧⟦X⟧), n ≠ 0 ∧ p ∈ PPSet t K e ∧ h ∈ PPSet t K e ∧ (n : ZMod a → K⟦X⟧⟦X⟧) * p = iotaP K t b ∧ F = p + (l : ZMod a → K⟦X⟧⟦X⟧) ^ r * h := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t F hF r
  classical
  have hK0 := charZero_K (l := l) (K := K)
  obtain ⟨w, hw, hFw⟩ := hF
  let N : ℕ × ℕ → ℕ := fun x => x.1.factorial * (x.2 / e).factorial
  have hNpos : ∀ x, N x ≠ 0 := fun x => Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  have hN0 : ∀ x, (N x : K) ≠ 0 := fun x => Nat.cast_ne_zero.2 (hNpos x)
  let ser : (ℕ × ℕ → Wq l a) → ZMod a → K⟦X⟧⟦X⟧ := fun v τ =>
    PowerSeries.mk fun i => PowerSeries.mk fun n => embK K t τ (v (i, n)) / (N (i, n) : K)
  have coeff_ser : ∀ v τ i n, coeff n (coeff i (ser v τ)) = embK K t τ (v (i, n)) / (N (i, n) : K) := by
    intro v τ i n; simp [ser]
  have ser_mem : ∀ v, LTo0 l v → ser v ∈ PPSet t K e := by
    intro v hv
    refine ⟨v, hv, fun τ i n => ?_⟩
    rw [coeff_ser, mul_div_cancel₀ _ (hN0 (i, n))]
    rfl
  have coeff_F : ∀ τ i n, coeff n (coeff i (F τ)) = embK K t τ (w (i, n)) / (N (i, n) : K) := by
    intro τ i n
    rw [eq_div_iff (hN0 _), mul_comm]
    exact hFw τ i n
  have hfin : {x | ¬ (l : Wq l a) ^ r ∣ w x}.Finite := Filter.eventually_cofinite.1 (hw r)
  let s := hfin.toFinset
  have mem_s : ∀ x, x ∈ s ↔ ¬ (l : Wq l a) ^ r ∣ w x := fun x => by simp [s]
  let c : ℕ × ℕ → Wq l a := fun x => if h : (l : Wq l a) ^ r ∣ w x then h.choose else 0
  let w₁ : ℕ × ℕ → Wq l a := fun x => if x ∈ s then w x else 0
  have hsplit : ∀ x, w x = w₁ x + (l : Wq l a) ^ r * c x := by
    intro x
    by_cases h : (l : Wq l a) ^ r ∣ w x
    · have hx : x ∉ s := fun hx => (mem_s x).1 hx h
      simp only [w₁, c, hx, if_false, dif_pos h, zero_add]
      exact h.choose_spec
    · have hx : x ∈ s := (mem_s x).2 h
      simp [w₁, c, hx, h]
  have hw₁ : LTo0 l w₁ := by
    intro m
    refine Filter.eventually_cofinite.2 (hfin.subset fun x hx => ?_)
    simp only [Set.mem_setOf_eq] at hx ⊢
    intro hd
    apply hx
    have : x ∉ s := fun hx' => (mem_s x).1 hx' hd
    simp [w₁, this]
  have hc : LTo0 l c := by
    intro m
    filter_upwards [hw (m + r)] with x hx
    have h : (l : Wq l a) ^ r ∣ w x := dvd_trans (pow_dvd_pow _ (Nat.le_add_left r m)) hx
    obtain ⟨d, hd⟩ := hx
    have hcx : c x = h.choose := dif_pos h
    have hspec := h.choose_spec
    refine ⟨d, ?_⟩
    rw [hcx]
    have hl0 : l ^ r ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
    have := wq_nat_cancel (K := K) t hl0 (x := h.choose - (l : Wq l a) ^ m * d) (by
      push_cast
      linear_combination hd - hspec)
    exact sub_eq_zero.1 this
  let nn : ℕ := ∏ x ∈ s, N x
  let b : Bp l a := ∑ x ∈ s, Polynomial.monomial x.1 (Polynomial.monomial x.2 ((nn / N x) • w x))
  have coeff_b : ∀ i n, (b.coeff i).coeff n = if (i, n) ∈ s then (nn / N (i, n)) • w (i, n) else 0 := by
    intro i n
    simp only [b, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_congr rfl (g := fun x => if x = (i, n) then (nn / N x) • w x else 0)]
    · exact Finset.sum_ite_eq' _ _ _
    · intro x _
      obtain ⟨x1, x2⟩ := x
      by_cases h1 : x1 = i <;> by_cases h2 : x2 = n <;> simp [h1, h2, Polynomial.coeff_monomial, Prod.ext_iff] <;> first | done | (subst h1; simp_all) | (split_ifs <;> simp_all)
  refine ⟨nn, b, ser w₁, ser c, Finset.prod_ne_zero_iff.2 fun x _ => hNpos x, ser_mem _ hw₁, ser_mem _ hc, ?_, ?_⟩
  · funext τ
    refine PowerSeries.ext fun i => PowerSeries.ext fun n => ?_
    rw [Pi.mul_apply, Pi.natCast_apply, coeff_coeff_natCast_mul, coeff_ser, coeff_iotaP, coeff_b]
    split_ifs with hx
    · have hdvd : N (i, n) ∣ nn := Finset.dvd_prod_of_mem N hx
      simp only [w₁, hx, if_true]
      rw [map_nsmul, nsmul_eq_mul, Nat.cast_div hdvd (hN0 _)]
      field_simp
    · simp [w₁, hx]
  · funext τ
    refine PowerSeries.ext fun i => PowerSeries.ext fun n => ?_
    rw [← Nat.cast_pow, Pi.add_apply, Pi.mul_apply, Pi.natCast_apply, map_add, map_add, coeff_coeff_natCast_mul,
      coeff_F, coeff_ser, coeff_ser, hsplit (i, n), map_add, map_mul, map_pow, map_natCast]
    push_cast
    ring

end GlobalTheory.CrysEval
