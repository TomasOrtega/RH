import Mathlib

namespace GlobalTheory.AdicCoord

/- English proof (translation)
Use `IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {x}) R) y fun N => ?_` and prove the remaining obligations. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Conclude with `h N`.
-/
theorem eq_zero_of_forall_pow_dvd {R : Type} [CommRing R] (x : R)
    [IsHausdorff (Ideal.span {x}) R] (y : R) (h : ∀ N : ℕ, x ^ N ∣ y) : y = 0 := by
  refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {x}) R) y fun N => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact h N

/- English proof (translation)
Establish `key : ∀ (N : ℕ) (u v : R), u ≡ v [SMOD ((Ideal.span {x}) ^ N • ⊤ : Submodule R R)] ↔ x ^ N ∣ u - v`. Introduce `N u v`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Take `⟨L, hL⟩` from `IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {x}) R) (f := fun N => ∑ k ∈ Finset.range N, x ^ k * a k) (by`. Introduce `m n hmn`.

Rewrite using `[key, ← dvd_neg, neg_sub, ← Finset.sum_Ico_eq_sub _ hmn]`. Use `Finset.dvd_sum fun k hk => ?_` and prove the remaining obligations. Conclude with `Dvd.dvd.mul_right (pow_dvd_pow x (Finset.mem_Ico.1 hk).1) _)`. Conclude with `⟨L, fun N => (key N _ _).1 (hL N)⟩`.
-/
theorem exists_sum_series {R : Type} [CommRing R] (x : R)
    [IsPrecomplete (Ideal.span {x}) R] (a : ℕ → R) :
    ∃ L : R, ∀ N : ℕ, x ^ N ∣ (∑ k ∈ Finset.range N, x ^ k * a k) - L := by
  have key : ∀ (N : ℕ) (u v : R), u ≡ v [SMOD ((Ideal.span {x}) ^ N • ⊤ : Submodule R R)] ↔
      x ^ N ∣ u - v := by
    intro N u v
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {x}) R)
    (f := fun N => ∑ k ∈ Finset.range N, x ^ k * a k) (by
      intro m n hmn
      rw [key, ← dvd_neg, neg_sub, ← Finset.sum_Ico_eq_sub _ hmn]
      refine Finset.dvd_sum fun k hk => ?_
      exact Dvd.dvd.mul_right (pow_dvd_pow x (Finset.mem_Ico.1 hk).1) _)
  exact ⟨L, fun N => (key N _ _).1 (hL N)⟩

/- English proof (translation)
Introduce `p O EE W RW _ _ _ _ _ _ ι c d o huniq hE hW hstep e`. Use `choose g hg1 hg2 using hstep`. Use `choose w hw using hg1`. Simplify using `only [Ideal.mem_span_singleton] at hg2`. Use `choose h hh using hg2`.

Establish `hsep : ∀ r : RW, (∀ N : ℕ, (p : RW) ^ N ∣ r) → r = 0`. Introduce `r hr`. Take `⟨u, hu, huu⟩` from `huniq r`. Establish `hu0 : ∀ j, u j = 0`. Introduce `j`.

Use `eq_zero_of_forall_pow_dvd (p : W) _ fun N => ?_` and prove the remaining obligations. Take `⟨r', hr'⟩` from `hr N`. Take `⟨u', hu', -⟩` from `huniq r'`. Establish `: (fun j => (p : W) ^ N * u' j) = u`. Apply `huu` to reduce the goal to its premises.

Rewrite using `[hr', hu', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Conclude with `⟨u' j, by rw [← this]⟩`. Rewrite using `[hu]`.

Simplify using `[hu0]`. Use `choose F hF using fun j => exists_sum_series (p : EE) (fun k => g (h^[k] e) j)`. Use `choose V hV using fun j => exists_sum_series (p : W) (fun k => w (h^[k] e) j)`. Use `⟨F, fun j => ⟨V j, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`.

Use `hsep _ fun N => ?_` and prove the remaining obligations. Establish `h1` using `map_dvd ι (hF j N)`. Establish `h2` using `map_dvd c (hV j N)`. Simplify using `only [map_pow, map_natCast, map_sub, map_sum, map_mul, hw] at h1 h2`. Use `dvd_sub h1 h2` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `hiter : ∀ N : ℕ, e = ∑ j, o j • (∑ k ∈ Finset.range N, (p : EE) ^ k * g (h^[k] e) j) + (p : EE) ^ N * h^[N] e`. Introduce `N`. Proceed by induction on `N with`.

Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `h3` using `hh (h^[n] e)`. Rewrite `h3` using `[sub_eq_iff_eq_add]`. Rewrite using `[Function.iterate_succ_apply']`.

Simplify using `only [Finset.sum_range_succ, smul_add, Finset.sum_add_distrib]`. Establish `h4 : ∑ j, o j • ((p : EE) ^ n * g (h^[n] e) j) = (p : EE) ^ n * ∑ j, o j • g (h^[n] e) j`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => (mul_smul_comm _ _ _).symm`. Rewrite using `[h4]`.

Take the linear combination `ih + (p : EE) ^ n * h3`. Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_forall_pow_dvd (p : EE) _ fun N => ?_` and prove the remaining obligations. Establish `h5 : e - ∑ j, o j • F j = ∑ j, o j • ((∑ k ∈ Finset.range N, (p : EE) ^ k * g (h^[k] e) j) - F j) + (p : EE) ^ N * h^[N] e`. Simplify using `only [smul_sub, Finset.sum_sub_distrib]`.

Take the linear combination `hiter N`. Rewrite using `[h5]`. Use `dvd_add (Finset.dvd_sum fun j _ => ?_) (dvd_mul_right _ _)` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`. Conclude with `Dvd.dvd.mul_left (hF j N) _`.
-/
theorem exists_coord : ∀ (p : ℕ) (O EE W RW : Type) [CommRing O] [CommRing EE] [CommRing W] [CommRing RW] [Algebra O EE] [Algebra O RW] (ι : EE →ₐ[O] RW) (c : W →+* RW) (d : ℕ) (o : Fin d → O), (∀ r : RW, ∃! w : Fin d → W, r = ∑ j, o j • c (w j)) → IsAdicComplete (Ideal.span {(p : EE)}) EE → IsAdicComplete (Ideal.span {(p : W)}) W → (∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e - ∑ j, o j • e' j ∈ Ideal.span {(p : EE)}) → ∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e = ∑ j, o j • e' j := by
  intro p O EE W RW _ _ _ _ _ _ ι c d o huniq hE hW hstep e
  choose g hg1 hg2 using hstep
  choose w hw using hg1
  simp only [Ideal.mem_span_singleton] at hg2
  choose h hh using hg2

  have hsep : ∀ r : RW, (∀ N : ℕ, (p : RW) ^ N ∣ r) → r = 0 := by
    intro r hr
    obtain ⟨u, hu, huu⟩ := huniq r
    have hu0 : ∀ j, u j = 0 := by
      intro j
      refine eq_zero_of_forall_pow_dvd (p : W) _ fun N => ?_
      obtain ⟨r', hr'⟩ := hr N
      obtain ⟨u', hu', -⟩ := huniq r'
      have : (fun j => (p : W) ^ N * u' j) = u := by
        apply huu
        rw [hr', hu', Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp
      exact ⟨u' j, by rw [← this]⟩
    rw [hu]
    simp [hu0]
  choose F hF using fun j => exists_sum_series (p : EE) (fun k => g (h^[k] e) j)
  choose V hV using fun j => exists_sum_series (p : W) (fun k => w (h^[k] e) j)
  refine ⟨F, fun j => ⟨V j, ?_⟩, ?_⟩
  · rw [← sub_eq_zero]
    refine hsep _ fun N => ?_
    have h1 := map_dvd ι (hF j N)
    have h2 := map_dvd c (hV j N)
    simp only [map_pow, map_natCast, map_sub, map_sum, map_mul, hw] at h1 h2
    have := dvd_sub h1 h2
    convert this using 1
    ring
  · have hiter : ∀ N : ℕ, e = ∑ j, o j • (∑ k ∈ Finset.range N, (p : EE) ^ k * g (h^[k] e) j)
        + (p : EE) ^ N * h^[N] e := by
      intro N
      induction N with
      | zero => simp
      | succ n ih =>
        have h3 := hh (h^[n] e)
        rw [sub_eq_iff_eq_add] at h3
        rw [Function.iterate_succ_apply']
        simp only [Finset.sum_range_succ, smul_add, Finset.sum_add_distrib]
        have h4 : ∑ j, o j • ((p : EE) ^ n * g (h^[n] e) j)
            = (p : EE) ^ n * ∑ j, o j • g (h^[n] e) j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => (mul_smul_comm _ _ _).symm
        rw [h4]
        linear_combination ih + (p : EE) ^ n * h3
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_pow_dvd (p : EE) _ fun N => ?_
    have h5 : e - ∑ j, o j • F j =
        ∑ j, o j • ((∑ k ∈ Finset.range N, (p : EE) ^ k * g (h^[k] e) j) - F j)
        + (p : EE) ^ N * h^[N] e := by
      simp only [smul_sub, Finset.sum_sub_distrib]
      linear_combination hiter N
    rw [h5]
    refine dvd_add (Finset.dvd_sum fun j _ => ?_) (dvd_mul_right _ _)
    rw [Algebra.smul_def]
    exact Dvd.dvd.mul_left (hF j N) _

end GlobalTheory.AdicCoord
