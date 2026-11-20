import Mathlib

open Polynomial IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Use `set K := IntermediateField.adjoin (IsLocalRing.ResidueField T) {IsLocalRing.residue V γ} with hK`. Establish `hγK : residue V γ ∈ K` using `IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)`. Establish `hres : ∀ p : T[X], residue V (aeval γ p) ∈ K`. Introduce `p`. Proceed by induction on `p using Polynomial.induction_on with`.

Consider the case `C a`. Rewrite using `[aeval_C]`. Establish `: residue V (algebraMap T V a) = algebraMap (ResidueField T) (ResidueField V) (residue T a)` using `(ResidueField.map_residue _ a).symm`. Rewrite using `[this]`. Conclude with `K.algebraMap_mem _`.

Consider the case `add p q hp hq => rw [map_add, map_add]`. Conclude with `K.add_mem hp hq`. Consider the case `monomial n a ih`. Rewrite using `[pow_succ, ← mul_assoc, map_mul, aeval_X, map_mul]`. Conclude with `K.mul_mem ih hγK`.

Establish `hϖ0 : algebraMap T V ϖ ≠ 0`. Rewrite using `[Ne, ← map_zero (algebraMap T V)]`. Conclude with `fun h => hϖ.ne_zero (hinj h)`. Establish `hα0 : α ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hα` using `[zero_pow hm.ne']`. Conclude with `mul_ne_zero hγ.ne_zero hϖ0 hα.symm`. Establish `hαnu : ¬ IsUnit α`. Introduce `h`. Establish `h1 : IsUnit (γ * algebraMap T V ϖ)` using `hα ▸ h.pow m`.

Conclude with `hϖ.not_isUnit ((isUnit_map_iff (algebraMap T V) ϖ).1 (isUnit_of_mul_isUnit_right h1))`. Establish `hsmall : ∀ k : ℕ, 0 < k → ∀ x : V, residue V (α ^ k * x) = 0`. Introduce `k hk x`. Rewrite using `[residue_eq_zero_iff]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ ((mem_maximalIdeal _).2 hαnu) k hk)`.

Establish `hcomb : ∀ (u u' : V) (k : ℕ), 0 < k → IsUnit u → residue V u ∈ K → IsUnit (u + α ^ k * u') ∧ residue V (u + α ^ k * u') ∈ K`. Introduce `u u' k hk hu huK`. Establish `e : residue V (u + α ^ k * u') = residue V u` using `by rw [map_add, hsmall k hk, add_zero]`. Use `⟨?_, e ▸ huK⟩` and prove the remaining obligations. Rewrite using `[← residue_ne_zero_iff_isUnit, e, residue_ne_zero_iff_isUnit]`.

Conclude with `hu`. Set `Good : Finset ℕ → V → Prop` to `fun s x => x = 0 ∨ ∃ n u, IsUnit u ∧ residue V u ∈ K ∧ n % m ∈ s ∧ x = α ^ n * u`. Establish `hdec : ∀ p : T[X], ∃ a : ℕ → T[X], aeval α p = ∑ j ∈ Finset.range m, aeval γ (a j) * α ^ j`. Introduce `p`. Proceed by induction on `p using Polynomial.induction_on' with`.

Consider the case `add p q hp hq`. Take `⟨a, ha⟩` from `hp`. Take `⟨b, hb⟩` from `hq`. Conclude with `⟨a + b, by simp only [map_add, ha, hb, Pi.add_apply, add_mul, Finset.sum_add_distrib]⟩`. Consider the case `monomial n t`.

Use `⟨fun j => if j = n % m then C t * (C ϖ * X) ^ (n / m) else 0, ?_⟩` and prove the remaining obligations. Simplify using `only [apply_ite (aeval γ), ite_mul, map_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_range, Nat.mod_lt _ hm, if_true]`. Rewrite using `[aeval_monomial, map_mul, aeval_C, map_pow, map_mul, aeval_C, aeval_X]`. Use `conv_lhs => rw [← Nat.div_add_mod n m, pow_add, pow_mul, hα]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hterm : ∀ (a : T[X]) (j : ℕ), j < m → Good {j} (aeval γ a * α ^ j)`. Introduce `a j hj`. Break down `hpol a with h0 | ⟨b, h', c, hc, hh', hrel⟩` into its components or cases. Use `left`. Rewrite using `[h0, zero_mul]`.

Use `right`. Use `⟨m * b + j, ((hγ.unit⁻¹ ^ b * hc.unit⁻¹ : Vˣ) : V) * aeval γ h', (Units.isUnit _).mul hh', ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, map_units_inv, map_units_inv, IsUnit.unit_spec, IsUnit.unit_spec]`. Conclude with `K.mul_mem (K.mul_mem (pow_mem (K.inv_mem hγK) b) (K.inv_mem (hres c))) (hres h')`. Rewrite using `[Finset.mem_singleton, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]`.

Establish `e1 : (γ * ((hγ.unit⁻¹ : Vˣ) : V)) ^ b = 1`. Rewrite using `[IsUnit.mul_val_inv hγ, one_pow]`. Establish `e2 : aeval γ c * ((hc.unit⁻¹ : Vˣ) : V) = 1`. Conclude with `IsUnit.mul_val_inv hc`. Rewrite using `[pow_add, pow_mul, hα, Units.val_mul, Units.val_pow_eq_pow_val]`.

Take the linear combination `(-(aeval γ a * α ^ j)) * e2 + (((hc.unit⁻¹ : Vˣ) : V) * α ^ j) * hrel + (-(algebraMap T V ϖ ^ b * aeval γ h' * ((hc.unit⁻¹ : Vˣ) : V) * α ^ j)) * e1`. Establish `hsum : ∀ (a : ℕ → T[X]) (s : Finset ℕ), s ⊆ Finset.range m → Good s (∑ j ∈ s, aeval γ (a j) * α ^ j)`. Introduce `a s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro _`.

Use `left`. Simplify using the standard rewrite rules. Consider the case `insert j s hjs ih`. Introduce `hsub`. Rewrite using `[Finset.sum_insert hjs]`.

Establish `hj : j < m` using `Finset.mem_range.1 (hsub (Finset.mem_insert_self _ _))`. Establish `ih'` using `ih ((Finset.subset_insert _ _).trans hsub)`. Break down `hterm (a j) j hj with h0 | ⟨n, u, hu, huK, hn, he⟩` into its components or cases. Rewrite using `[h0, zero_add]`. Break down `ih' with h | ⟨n', u', hu', hu'K, hn', he'⟩` into its components or cases.

Use `left`. Conclude with `h`. Use `right`. Conclude with `⟨n', u', hu', hu'K, Finset.mem_insert_of_mem hn', he'⟩`. Rewrite `hn` using `[Finset.mem_singleton]`.

Break down `ih' with h | ⟨n', u', hu', hu'K, hn', he'⟩` into its components or cases. Use `right`. Rewrite using `[h, add_zero]`. Conclude with `⟨n, u, hu, huK, hn ▸ Finset.mem_insert_self _ _, he⟩`. Use `right`.

Establish `hne : n ≠ n'` using `by rintro rfl; exact hjs (hn ▸ hn')`. Break down `lt_or_gt_of_ne hne with hlt | hlt` into its components or cases. Take `⟨h1, h2⟩` from `hcomb u u' (n' - n) (Nat.sub_pos_of_lt hlt) hu huK`. Use `⟨n, _, h1, h2, hn ▸ Finset.mem_insert_self _ _, ?_⟩` and prove the remaining obligations. Rewrite using `[he, he', mul_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le]`.

Take `⟨h1, h2⟩` from `hcomb u' u (n - n') (Nat.sub_pos_of_lt hlt) hu' hu'K`. Use `⟨n', _, h1, h2, Finset.mem_insert_of_mem hn', ?_⟩` and prove the remaining obligations. Rewrite using `[he, he', mul_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le, add_comm]`. Distinguish the cases in `hv : IsUnit v`. Take `⟨f, g, hg0, hfg⟩` from `hgen v`.

Take `⟨a, ha⟩` from `hdec g`. Take `⟨b, hb⟩` from `hdec f`. Establish `Gg` using `hsum a _ subset_rfl`. Establish `Gf` using `hsum b _ subset_rfl`. Rewrite `Gg` using `[← ha]`.

Rewrite `Gf` using `[← hb]`. Break down `Gg with h | ⟨n, u, hu, huK, -, he⟩` into its components or cases. Conclude with `absurd h hg0`. Break down `Gf with h | ⟨n', u', hu', hu'K, -, he'⟩` into its components or cases. Conclude with `absurd (hfg.trans h) (mul_ne_zero hg0 hv.ne_zero)`.

Rewrite `hfg` using `[he, he']`. Establish `key : n = n'`. Break down `lt_trichotomy n n' with h | h | h` into its components or cases. It suffices to derive a contradiction. Establish `h2 : α ^ n * (u * v) = α ^ n * (α ^ (n' - n) * u')`.

Rewrite using `[← mul_assoc, hfg, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h.le]`. Establish `h3` using `mul_left_cancel₀ (pow_ne_zero n hα0) h2`. Establish `h4` using `hsmall (n' - n) (Nat.sub_pos_of_lt h) u'`. Rewrite `h4` using `[← h3]`. Conclude with `(residue_ne_zero_iff_isUnit _).2 (hu.mul hv) h4`.

Conclude with `h`. It suffices to derive a contradiction. Establish `h2 : α ^ n' * (α ^ (n - n') * (u * v)) = α ^ n' * u'`. Rewrite using `[← hfg, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h.le, mul_assoc]`. Establish `h3` using `mul_left_cancel₀ (pow_ne_zero n' hα0) h2`.

Establish `h4` using `hsmall (n - n') (Nat.sub_pos_of_lt h) (u * v)`. Rewrite `h4` using `[h3]`. Conclude with `(residue_ne_zero_iff_isUnit _).2 hu' h4`. Substitute `key` using the available equality. Establish `huv : u * v = u'` using `mul_left_cancel₀ (pow_ne_zero n hα0) (by rw [← mul_assoc, hfg])`.

Establish `hr : residue V u * residue V v = residue V u'` using `by rw [← map_mul, huv]`. Establish `hru : residue V u ≠ 0` using `(residue_ne_zero_iff_isUnit _).2 hu`. Establish `: residue V v = residue V u' / residue V u`. Rewrite using `[← hr]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this]`. Conclude with `K.div_mem hu'K huK`. Rewrite using `[(residue_eq_zero_iff v).2 ((mem_maximalIdeal _).2 hv)]`. Conclude with `K.zero_mem`.
-/
theorem kummer_residue_mem_adjoin (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra T V] [IsLocalHom (algebraMap T V)]
    (hinj : Function.Injective (algebraMap T V))
    (α γ : V) (ϖ : T) (m : ℕ) (hϖ : Irreducible ϖ) (hm : 0 < m) (hγ : IsUnit γ)
    (hα : α ^ m = γ * algebraMap T V ϖ)
    (hpol : ∀ h : Polynomial T, Polynomial.aeval γ h = 0 ∨
      ∃ (a : ℕ) (h' c : Polynomial T), IsUnit (Polynomial.aeval γ c) ∧ IsUnit (Polynomial.aeval γ h') ∧
        Polynomial.aeval γ c * Polynomial.aeval γ h = algebraMap T V ϖ ^ a * Polynomial.aeval γ h')
    (hgen : ∀ v : V, ∃ f g : Polynomial T, Polynomial.aeval α g ≠ 0 ∧
      Polynomial.aeval α g * v = Polynomial.aeval α f)
    (v : V) : IsLocalRing.residue V v ∈
      IntermediateField.adjoin (IsLocalRing.ResidueField T) {IsLocalRing.residue V γ} := by
  set K := IntermediateField.adjoin (IsLocalRing.ResidueField T) {IsLocalRing.residue V γ} with hK
  have hγK : residue V γ ∈ K := IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
  have hres : ∀ p : T[X], residue V (aeval γ p) ∈ K := by
    intro p
    induction p using Polynomial.induction_on with
    | C a =>
      rw [aeval_C]
      have : residue V (algebraMap T V a) =
          algebraMap (ResidueField T) (ResidueField V) (residue T a) :=
        (ResidueField.map_residue _ a).symm
      rw [this]; exact K.algebraMap_mem _
    | add p q hp hq => rw [map_add, map_add]; exact K.add_mem hp hq
    | monomial n a ih =>
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X, map_mul]
      exact K.mul_mem ih hγK
  have hϖ0 : algebraMap T V ϖ ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap T V)]; exact fun h => hϖ.ne_zero (hinj h)
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hα
    exact mul_ne_zero hγ.ne_zero hϖ0 hα.symm
  have hαnu : ¬ IsUnit α := by
    intro h
    have h1 : IsUnit (γ * algebraMap T V ϖ) := hα ▸ h.pow m
    exact hϖ.not_isUnit ((isUnit_map_iff (algebraMap T V) ϖ).1 (isUnit_of_mul_isUnit_right h1))
  have hsmall : ∀ k : ℕ, 0 < k → ∀ x : V, residue V (α ^ k * x) = 0 := by
    intro k hk x
    rw [residue_eq_zero_iff]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ ((mem_maximalIdeal _).2 hαnu) k hk)
  have hcomb : ∀ (u u' : V) (k : ℕ), 0 < k → IsUnit u → residue V u ∈ K →
      IsUnit (u + α ^ k * u') ∧ residue V (u + α ^ k * u') ∈ K := by
    intro u u' k hk hu huK
    have e : residue V (u + α ^ k * u') = residue V u := by rw [map_add, hsmall k hk, add_zero]
    refine ⟨?_, e ▸ huK⟩
    rw [← residue_ne_zero_iff_isUnit, e, residue_ne_zero_iff_isUnit]; exact hu
  let Good : Finset ℕ → V → Prop := fun s x =>
    x = 0 ∨ ∃ n u, IsUnit u ∧ residue V u ∈ K ∧ n % m ∈ s ∧ x = α ^ n * u
  have hdec : ∀ p : T[X], ∃ a : ℕ → T[X],
      aeval α p = ∑ j ∈ Finset.range m, aeval γ (a j) * α ^ j := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp; obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by simp only [map_add, ha, hb, Pi.add_apply, add_mul, Finset.sum_add_distrib]⟩
    | monomial n t =>
      refine ⟨fun j => if j = n % m then C t * (C ϖ * X) ^ (n / m) else 0, ?_⟩
      simp only [apply_ite (aeval γ), ite_mul, map_zero, zero_mul, Finset.sum_ite_eq',
        Finset.mem_range, Nat.mod_lt _ hm, if_true]
      rw [aeval_monomial, map_mul, aeval_C, map_pow, map_mul, aeval_C, aeval_X]
      conv_lhs => rw [← Nat.div_add_mod n m, pow_add, pow_mul, hα]
      ring
  have hterm : ∀ (a : T[X]) (j : ℕ), j < m → Good {j} (aeval γ a * α ^ j) := by
    intro a j hj
    rcases hpol a with h0 | ⟨b, h', c, hc, hh', hrel⟩
    · left; rw [h0, zero_mul]
    · right
      refine ⟨m * b + j, ((hγ.unit⁻¹ ^ b * hc.unit⁻¹ : Vˣ) : V) * aeval γ h',
        (Units.isUnit _).mul hh', ?_, ?_, ?_⟩
      · rw [map_mul, Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, map_units_inv,
          map_units_inv, IsUnit.unit_spec, IsUnit.unit_spec]
        exact K.mul_mem (K.mul_mem (pow_mem (K.inv_mem hγK) b) (K.inv_mem (hres c))) (hres h')
      · rw [Finset.mem_singleton, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
      · have e1 : (γ * ((hγ.unit⁻¹ : Vˣ) : V)) ^ b = 1 := by
          rw [IsUnit.mul_val_inv hγ, one_pow]
        have e2 : aeval γ c * ((hc.unit⁻¹ : Vˣ) : V) = 1 := by
          exact IsUnit.mul_val_inv hc
        rw [pow_add, pow_mul, hα, Units.val_mul, Units.val_pow_eq_pow_val]
        linear_combination (-(aeval γ a * α ^ j)) * e2 + (((hc.unit⁻¹ : Vˣ) : V) * α ^ j) * hrel
          + (-(algebraMap T V ϖ ^ b * aeval γ h' * ((hc.unit⁻¹ : Vˣ) : V) * α ^ j)) * e1
  have hsum : ∀ (a : ℕ → T[X]) (s : Finset ℕ), s ⊆ Finset.range m →
      Good s (∑ j ∈ s, aeval γ (a j) * α ^ j) := by
    intro a s
    induction s using Finset.induction_on with
    | empty => intro _; left; simp
    | insert j s hjs ih =>
      intro hsub
      rw [Finset.sum_insert hjs]
      have hj : j < m := Finset.mem_range.1 (hsub (Finset.mem_insert_self _ _))
      have ih' := ih ((Finset.subset_insert _ _).trans hsub)
      rcases hterm (a j) j hj with h0 | ⟨n, u, hu, huK, hn, he⟩
      · rw [h0, zero_add]
        rcases ih' with h | ⟨n', u', hu', hu'K, hn', he'⟩
        · left; exact h
        · right; exact ⟨n', u', hu', hu'K, Finset.mem_insert_of_mem hn', he'⟩
      · rw [Finset.mem_singleton] at hn
        rcases ih' with h | ⟨n', u', hu', hu'K, hn', he'⟩
        · right; rw [h, add_zero]
          exact ⟨n, u, hu, huK, hn ▸ Finset.mem_insert_self _ _, he⟩
        · right
          have hne : n ≠ n' := by rintro rfl; exact hjs (hn ▸ hn')
          rcases lt_or_gt_of_ne hne with hlt | hlt
          · obtain ⟨h1, h2⟩ := hcomb u u' (n' - n) (Nat.sub_pos_of_lt hlt) hu huK
            refine ⟨n, _, h1, h2, hn ▸ Finset.mem_insert_self _ _, ?_⟩
            rw [he, he', mul_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le]
          · obtain ⟨h1, h2⟩ := hcomb u' u (n - n') (Nat.sub_pos_of_lt hlt) hu' hu'K
            refine ⟨n', _, h1, h2, Finset.mem_insert_of_mem hn', ?_⟩
            rw [he, he', mul_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le, add_comm]
  by_cases hv : IsUnit v
  · obtain ⟨f, g, hg0, hfg⟩ := hgen v
    obtain ⟨a, ha⟩ := hdec g
    obtain ⟨b, hb⟩ := hdec f
    have Gg := hsum a _ subset_rfl
    have Gf := hsum b _ subset_rfl
    rw [← ha] at Gg
    rw [← hb] at Gf
    rcases Gg with h | ⟨n, u, hu, huK, -, he⟩
    · exact absurd h hg0
    rcases Gf with h | ⟨n', u', hu', hu'K, -, he'⟩
    · exact absurd (hfg.trans h) (mul_ne_zero hg0 hv.ne_zero)
    rw [he, he'] at hfg
    have key : n = n' := by
      rcases lt_trichotomy n n' with h | h | h
      · exfalso
        have h2 : α ^ n * (u * v) = α ^ n * (α ^ (n' - n) * u') := by
          rw [← mul_assoc, hfg, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h.le]
        have h3 := mul_left_cancel₀ (pow_ne_zero n hα0) h2
        have h4 := hsmall (n' - n) (Nat.sub_pos_of_lt h) u'
        rw [← h3] at h4
        exact (residue_ne_zero_iff_isUnit _).2 (hu.mul hv) h4
      · exact h
      · exfalso
        have h2 : α ^ n' * (α ^ (n - n') * (u * v)) = α ^ n' * u' := by
          rw [← hfg, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h.le, mul_assoc]
        have h3 := mul_left_cancel₀ (pow_ne_zero n' hα0) h2
        have h4 := hsmall (n - n') (Nat.sub_pos_of_lt h) (u * v)
        rw [h3] at h4
        exact (residue_ne_zero_iff_isUnit _).2 hu' h4
    subst key
    have huv : u * v = u' := mul_left_cancel₀ (pow_ne_zero n hα0) (by rw [← mul_assoc, hfg])
    have hr : residue V u * residue V v = residue V u' := by rw [← map_mul, huv]
    have hru : residue V u ≠ 0 := (residue_ne_zero_iff_isUnit _).2 hu
    have : residue V v = residue V u' / residue V u := by
      rw [← hr]; field_simp
    rw [this]; exact K.div_mem hu'K huK
  · rw [(residue_eq_zero_iff v).2 ((mem_maximalIdeal _).2 hv)]; exact K.zero_mem

end GlobalTheory
