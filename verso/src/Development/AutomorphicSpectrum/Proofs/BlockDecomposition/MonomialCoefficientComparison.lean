import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TZero

open Finset GlobalTheory.CompanionTheory.CoefId

namespace GlobalTheory.CompanionTheory.CoefId

/- English proof (translation)
Establish `hinj : Function.Injective (fun k : ℕ => ((1 + (k : ℂ) * Complex.I) / (1 - (k : ℂ) * Complex.I)))`. Introduce `s t hst`. Establish `h1 : ∀ k : ℕ, (1 - (k : ℂ) * Complex.I) ≠ 0`. Introduce `k h0`. Use `congrArg Complex.re h0` as an intermediate fact.

Simplify using `at this`. Establish `h2` using `(div_eq_div_iff (h1 s) (h1 t)).mp hst`. Establish `h3` using `congrArg Complex.im h2`. Simplify using `at h3`. Establish `h4 : (s : ℝ) = t` using `by linarith`.

Conclude with `h4` after adjusting the coercions. Use `Set.infinite_of_injective_forall_mem hinj fun k => ?_` and prove the remaining obligations. Establish `h5 : ‖(1 + (k : ℂ) * Complex.I)‖ = ‖(1 - (k : ℂ) * Complex.I)‖`. Rewrite using `[← Complex.norm_conj (1 + (k : ℂ) * Complex.I)]`. Simplify using `[sub_eq_add_neg]`.

Establish `h6 : ‖(1 - (k : ℂ) * Complex.I)‖ ≠ 0`. Rewrite using `[norm_ne_zero_iff]`. Introduce `h0`. Use `congrArg Complex.re h0` as an intermediate fact. Simplify using `at this`.

Simplify using `only [Set.mem_ofPred_eq, norm_div, h5]`. Conclude with `div_self h6`.
-/
theorem unitCircle_infinite : {z : ℂ | ‖z‖ = 1}.Infinite := by
  have hinj : Function.Injective (fun k : ℕ => ((1 + (k : ℂ) * Complex.I) / (1 - (k : ℂ) * Complex.I))) := by
    intro s t hst
    have h1 : ∀ k : ℕ, (1 - (k : ℂ) * Complex.I) ≠ 0 := by
      intro k h0
      have := congrArg Complex.re h0
      simp at this
    have h2 := (div_eq_div_iff (h1 s) (h1 t)).mp hst
    have h3 := congrArg Complex.im h2
    simp at h3
    have h4 : (s : ℝ) = t := by linarith
    exact_mod_cast h4
  refine Set.infinite_of_injective_forall_mem hinj fun k => ?_
  have h5 : ‖(1 + (k : ℂ) * Complex.I)‖ = ‖(1 - (k : ℂ) * Complex.I)‖ := by
    rw [← Complex.norm_conj (1 + (k : ℂ) * Complex.I)]
    simp [sub_eq_add_neg]
  have h6 : ‖(1 - (k : ℂ) * Complex.I)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h0
    have := congrArg Complex.re h0
    simp at this
  simp only [Set.mem_ofPred_eq, norm_div, h5]
  exact div_self h6

/- English proof (translation)
Use `set D : MvPolynomial (Fin n) ℂ := ∏ q ∈ prs n, (MvPolynomial.X q.1 ^ 2 - MvPolynomial.X q.2 ^ 2) with hD`. Establish `hD0 : D ≠ 0`. Use `Finset.prod_ne_zero_iff.mpr fun q hq => ?_` and prove the remaining obligations. Establish `hlt : q.1 < q.2` using `(mem_filter.mp hq).2`. Introduce `h0`.

Establish `h1 : (MvPolynomial.X q.1 ^ 2 : MvPolynomial (Fin n) ℂ) = MvPolynomial.X q.2 ^ 2` using `sub_eq_zero.mp h0`. Use `congrArg (MvPolynomial.eval (fun a => if a = q.1 then (1 : ℂ) else 0)) h1` as an intermediate fact. Simplify using `[hlt.ne'] at this`. Establish `hz : p * D = 0`. Apply `MvPolynomial.funext_set (fun _ => {z : ℂ | ‖z‖ = 1}) (fun _ => unitCircle_infinite)` to reduce the goal to its premises.

Introduce `x hx`. Establish `hx' : ∀ a, ‖x a‖ = 1` using `fun a => hx a (Set.mem_univ a)`. Rewrite using `[map_mul, map_zero]`. Distinguish the cases in `hi : Function.Injective (fun a => x a ^ 2)`. Rewrite using `[h x hx' hi, zero_mul]`.

Choose the witnesses or unpack the hypotheses as in `⟨a, b, hab, hne⟩ : ∃ a b, x a ^ 2 = x b ^ 2 ∧ a ≠ b := by`. Simplify `hi` using `[Function.Injective]`. Establish `: MvPolynomial.eval x D = 0`. Rewrite using `[hD, map_prod]`. Break down `lt_or_gt_of_ne hne with hlt | hlt` into its components or cases.

Conclude with `Finset.prod_eq_zero (i := (a, b)) (by simp [prs, hlt]) (by simp [hab])`. Conclude with `Finset.prod_eq_zero (i := (b, a)) (by simp [prs, hlt]) (by simp [hab])`. Rewrite using `[this, mul_zero]`. Conclude with `(mul_eq_zero.mp hz).resolve_right hD0`.
-/
theorem poly_zero_of_torus {n : ℕ} (p : MvPolynomial (Fin n) ℂ)
    (h : ∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → Function.Injective (fun a => z a ^ 2) →
      MvPolynomial.eval z p = 0) : p = 0 := by
  classical
  set D : MvPolynomial (Fin n) ℂ :=
    ∏ q ∈ prs n, (MvPolynomial.X q.1 ^ 2 - MvPolynomial.X q.2 ^ 2) with hD
  have hD0 : D ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun q hq => ?_
    have hlt : q.1 < q.2 := (mem_filter.mp hq).2
    intro h0
    have h1 : (MvPolynomial.X q.1 ^ 2 : MvPolynomial (Fin n) ℂ) = MvPolynomial.X q.2 ^ 2 :=
      sub_eq_zero.mp h0
    have := congrArg (MvPolynomial.eval (fun a => if a = q.1 then (1 : ℂ) else 0)) h1
    simp [hlt.ne'] at this
  have hz : p * D = 0 := by
    apply MvPolynomial.funext_set (fun _ => {z : ℂ | ‖z‖ = 1}) (fun _ => unitCircle_infinite)
    intro x hx
    have hx' : ∀ a, ‖x a‖ = 1 := fun a => hx a (Set.mem_univ a)
    rw [map_mul, map_zero]
    by_cases hi : Function.Injective (fun a => x a ^ 2)
    · rw [h x hx' hi, zero_mul]
    · obtain ⟨a, b, hab, hne⟩ : ∃ a b, x a ^ 2 = x b ^ 2 ∧ a ≠ b := by
        simpa [Function.Injective] using hi
      have : MvPolynomial.eval x D = 0 := by
        rw [hD, map_prod]
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact Finset.prod_eq_zero (i := (a, b)) (by simp [prs, hlt]) (by simp [hab])
        · exact Finset.prod_eq_zero (i := (b, a)) (by simp [prs, hlt]) (by simp [hab])
      rw [this, mul_zero]
  exact (mul_eq_zero.mp hz).resolve_right hD0

/- English proof (translation)
Use `set N : ℕ := ∑ m ∈ S, ∑ a, (m a).natAbs with hNdef`. Establish `hN : ∀ m ∈ S, ∀ a, 0 ≤ m a + (N : ℤ)`. Introduce `m hm a`. Establish `h1 : (m a).natAbs ≤ ∑ a, (m a).natAbs` using `Finset.single_le_sum (f := fun a => (m a).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ a)`. Establish `h2 : ∑ a, (m a).natAbs ≤ N` using `Finset.single_le_sum (f := fun m : Fin n → ℤ => ∑ a, (m a).natAbs) (fun _ _ => Nat.zero_le _) hm`.

Establish `h3 : ((m a).natAbs : ℤ) ≤ N` using `by exact_mod_cast h1.trans h2`. Establish `h4 : -((m a).natAbs : ℤ) ≤ m a`. Use `abs_nonneg (m a)` as an intermediate fact. Rewrite using `[Int.natCast_natAbs]`. Conclude with `neg_abs_le (m a)`.

Combine the linear equalities and inequalities to obtain the conclusion. Set `s : (Fin n → ℤ) → (Fin n →₀ ℕ)` to `fun m => Finsupp.equivFunOnFinite.symm (fun a => (m a + (N : ℤ)).toNat)`. Establish `hs : ∀ m ∈ S, ∀ a, ((s m a : ℕ) : ℤ) = m a + N`. Introduce `m hm a`. Simplify using `only [s, Finsupp.equivFunOnFinite_symm_apply_apply]`.

Conclude with `Int.toNat_of_nonneg (hN m hm a)`. Establish `hinj : ∀ m ∈ S, ∀ m' ∈ S, s m = s m' → m = m'`. Introduce `m hm m' hm' hss`. Use function extensionality and compare the values at `a`. Establish `h1` using `hs m hm a`.

Establish `h2` using `hs m' hm' a`. Rewrite `h1` using `[hss]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hp : (∑ m ∈ S, MvPolynomial.monomial (s m) (h m) : MvPolynomial (Fin n) ℂ) = 0`. Use `poly_zero_of_torus _ fun z hz hi => ?_` and prove the remaining obligations.

Establish `hz0 : ∀ a, z a ≠ 0`. Introduce `a h0`. Use `hz a` as an intermediate fact. Simplify using `[h0] at this`. Establish `hterm : ∀ m ∈ S, MvPolynomial.eval z (MvPolynomial.monomial (s m) (h m)) = (∏ a, z a ^ N) * (h m * mon m z)`.

Introduce `m hm`. Rewrite using `[MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mon]`. Establish `: ∀ a, z a ^ (s m a) = z a ^ N * z a ^ (m a)`. Introduce `a`. Rewrite using `[← zpow_natCast, hs m hm a, ← zpow_natCast, ← zpow_add₀ (hz0 a), add_comm]`.

Simplify using `only [this, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_sum, Finset.sum_congr rfl hterm, ← Finset.mul_sum, H z hz hi, mul_zero]`. Introduce `m hm`. Establish `h1` using `congrArg (MvPolynomial.coeff (s m)) hp`.

Rewrite `h1` using `[MvPolynomial.coeff_sum, Finset.sum_eq_single m]`. Simplify `h1` using `[MvPolynomial.coeff_monomial]`. Introduce `b hb hne`. Rewrite using `[MvPolynomial.coeff_monomial, if_neg fun e => hne (hinj b hb m hm e)]`. Conclude with `fun h' => absurd hm h'`.
-/
theorem coeff_zero_of_torus {n : ℕ} (S : Finset (Fin n → ℤ)) (h : (Fin n → ℤ) → ℂ)
    (H : ∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → Function.Injective (fun a => z a ^ 2) →
      ∑ m ∈ S, h m * mon m z = 0) : ∀ m ∈ S, h m = 0 := by
  classical
  set N : ℕ := ∑ m ∈ S, ∑ a, (m a).natAbs with hNdef
  have hN : ∀ m ∈ S, ∀ a, 0 ≤ m a + (N : ℤ) := by
    intro m hm a
    have h1 : (m a).natAbs ≤ ∑ a, (m a).natAbs :=
      Finset.single_le_sum (f := fun a => (m a).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ a)
    have h2 : ∑ a, (m a).natAbs ≤ N :=
      Finset.single_le_sum (f := fun m : Fin n → ℤ => ∑ a, (m a).natAbs)
        (fun _ _ => Nat.zero_le _) hm
    have h3 : ((m a).natAbs : ℤ) ≤ N := by exact_mod_cast h1.trans h2
    have h4 : -((m a).natAbs : ℤ) ≤ m a := by
      have := abs_nonneg (m a)
      rw [Int.natCast_natAbs]
      exact neg_abs_le (m a)
    linarith
  let s : (Fin n → ℤ) → (Fin n →₀ ℕ) := fun m =>
    Finsupp.equivFunOnFinite.symm (fun a => (m a + (N : ℤ)).toNat)
  have hs : ∀ m ∈ S, ∀ a, ((s m a : ℕ) : ℤ) = m a + N := by
    intro m hm a
    simp only [s, Finsupp.equivFunOnFinite_symm_apply_apply]
    exact Int.toNat_of_nonneg (hN m hm a)
  have hinj : ∀ m ∈ S, ∀ m' ∈ S, s m = s m' → m = m' := by
    intro m hm m' hm' hss
    funext a
    have h1 := hs m hm a
    have h2 := hs m' hm' a
    rw [hss] at h1
    linarith
  have hp : (∑ m ∈ S, MvPolynomial.monomial (s m) (h m) : MvPolynomial (Fin n) ℂ) = 0 := by
    refine poly_zero_of_torus _ fun z hz hi => ?_
    have hz0 : ∀ a, z a ≠ 0 := by
      intro a h0
      have := hz a
      simp [h0] at this
    have hterm : ∀ m ∈ S, MvPolynomial.eval z (MvPolynomial.monomial (s m) (h m)) =
        (∏ a, z a ^ N) * (h m * mon m z) := by
      intro m hm
      rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mon]
      have : ∀ a, z a ^ (s m a) = z a ^ N * z a ^ (m a) := by
        intro a
        rw [← zpow_natCast, hs m hm a, ← zpow_natCast, ← zpow_add₀ (hz0 a), add_comm]
      simp only [this, Finset.prod_mul_distrib]
      ring
    rw [map_sum, Finset.sum_congr rfl hterm, ← Finset.mul_sum, H z hz hi, mul_zero]
  intro m hm
  have h1 := congrArg (MvPolynomial.coeff (s m)) hp
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single m] at h1
  · simpa [MvPolynomial.coeff_monomial] using h1
  · intro b hb hne
    rw [MvPolynomial.coeff_monomial, if_neg fun e => hne (hinj b hb m hm e)]
  · exact fun h' => absurd hm h'

/- English proof (translation)
Use `set S : Finset (Fin n → ℤ) := insert m (I.image e ∪ J.image e') with hS`. Use `set h : (Fin n → ℤ) → ℂ := fun m => ∑ i ∈ I.filter (fun i => e i = m), f i - ∑ j ∈ J.filter (fun j => e' j = m), g j with hh`. Establish `hI : ∀ i ∈ I, e i ∈ S` using `fun i hi => mem_insert_of_mem (mem_union_left _ (mem_image_of_mem e hi))`. Establish `hJ : ∀ j ∈ J, e' j ∈ S` using `fun j hj => mem_insert_of_mem (mem_union_right _ (mem_image_of_mem e' hj))`. Establish `key` using `coeff_zero_of_torus S h (fun z hz hi => by`.

Establish `h1 : ∑ i ∈ I, f i * mon (e i) z = ∑ m ∈ S, (∑ i ∈ I.filter (fun i => e i = m), f i) * mon m z`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to hI]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations.

Rewrite using `[(mem_filter.mp hi).2]`. Establish `h2 : ∑ j ∈ J, g j * mon (e' j) z = ∑ m ∈ S, (∑ j ∈ J.filter (fun j => e' j = m), g j) * mon m z`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to hJ]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[(mem_filter.mp hj).2]`. Simplify using `only [hh, sub_mul, Finset.sum_sub_distrib]`. Rewrite using `[← h1, ← h2, H z hz hi, sub_self]) m (mem_insert_self _ _)`. Conclude with `sub_eq_zero.mp key`.
-/
theorem laurent_indep_torus {n : ℕ} {ι κ : Type} (I : Finset ι) (J : Finset κ) (f : ι → ℂ)
    (g : κ → ℂ) (e : ι → Fin n → ℤ) (e' : κ → Fin n → ℤ)
    (H : ∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → Function.Injective (fun a => z a ^ 2) →
      ∑ i ∈ I, f i * mon (e i) z = ∑ j ∈ J, g j * mon (e' j) z) (m : Fin n → ℤ) :
    ∑ i ∈ I.filter (fun i => e i = m), f i = ∑ j ∈ J.filter (fun j => e' j = m), g j := by
  classical
  set S : Finset (Fin n → ℤ) := insert m (I.image e ∪ J.image e') with hS
  set h : (Fin n → ℤ) → ℂ := fun m => ∑ i ∈ I.filter (fun i => e i = m), f i -
    ∑ j ∈ J.filter (fun j => e' j = m), g j with hh
  have hI : ∀ i ∈ I, e i ∈ S := fun i hi =>
    mem_insert_of_mem (mem_union_left _ (mem_image_of_mem e hi))
  have hJ : ∀ j ∈ J, e' j ∈ S := fun j hj =>
    mem_insert_of_mem (mem_union_right _ (mem_image_of_mem e' hj))
  have key := coeff_zero_of_torus S h (fun z hz hi => by
    have h1 : ∑ i ∈ I, f i * mon (e i) z =
        ∑ m ∈ S, (∑ i ∈ I.filter (fun i => e i = m), f i) * mon m z := by
      rw [← Finset.sum_fiberwise_of_maps_to hI]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [(mem_filter.mp hi).2]
    have h2 : ∑ j ∈ J, g j * mon (e' j) z =
        ∑ m ∈ S, (∑ j ∈ J.filter (fun j => e' j = m), g j) * mon m z := by
      rw [← Finset.sum_fiberwise_of_maps_to hJ]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [(mem_filter.mp hj).2]
    simp only [hh, sub_mul, Finset.sum_sub_distrib]
    rw [← h1, ← h2, H z hz hi, sub_self]) m (mem_insert_self _ _)
  exact sub_eq_zero.mp key

end GlobalTheory.CompanionTheory.CoefId
