import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.WeylLatticeDescent

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.RelativeIndexFlags

section Desc

variable {LL Kf ι : Type} [Field LL] [Field Kf] [Algebra LL Kf]

/- English proof (translation)
Use extensionality with `m`. Establish `hm` using `congrArg (fun P => ℓ (coeff m P)) h`. Simplify using `only [coeff_sum, coeff_C_mul, coeff_map, map_sum] at hm`. Simplify using `only [coeff_sum, coeff_smul, smul_eq_mul]`. Establish `e : ∀ (a : Kf) (r : LL), ℓ (a * algebraMap LL Kf r) = ℓ a * r`.

Introduce `a r`. Rewrite using `[mul_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, mul_comm]`. Simplify using `only [e] at hm`. Conclude with `hm`.
-/
theorem desc_fun (ℓ : Kf →ₗ[LL] LL) (t : Finset (MvPolynomial ι LL)) (c : MvPolynomial ι LL → Kf) (c0 : Kf)
    (Q : MvPolynomial ι LL)
    (h : ∑ x ∈ t, C (c x) * map (algebraMap LL Kf) x = C c0 * map (algebraMap LL Kf) Q) :
    ∑ x ∈ t, ℓ (c x) • x = ℓ c0 • Q := by
  ext m
  have hm := congrArg (fun P => ℓ (coeff m P)) h
  simp only [coeff_sum, coeff_C_mul, coeff_map, map_sum] at hm
  simp only [coeff_sum, coeff_smul, smul_eq_mul]
  have e : ∀ (a : Kf) (r : LL), ℓ (a * algebraMap LL Kf r) = ℓ a * r := by
    intro a r
    rw [mul_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, mul_comm]
  simp only [e] at hm
  exact hm

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`. Introduce and unpack `⟨x, hx, _⟩`. Simplify using `at hx`. Consider the case `insert a t' ha ih`.

Introduce and unpack `⟨x, hx, hfx⟩`. Distinguish the cases in `hex : ∃ x ∈ t', f x ≠ 0`. Take `⟨j, hj, hfj, hall⟩` from `ih hex`. Distinguish the cases in `hr : f a / f j ∈ R0`. Use `⟨j, Finset.mem_insert_of_mem hj, hfj, ?_⟩` and prove the remaining obligations.

Introduce `y hy`. Break down `Finset.mem_insert.mp hy with rfl | hy` into its components or cases. Conclude with `hr`. Conclude with `hall y hy`. Establish `hinv : f j / f a ∈ R0`.

Establish `h2` using `(hv (f a / f j)).resolve_left hr`. Rewrite `h2` using `[inv_div]`. Then use the resulting hypothesis. Establish `hfa : f a ≠ 0`. Introduce `h0`. Apply `hr` to reduce the goal to its premises.

Rewrite using `[h0, zero_div]`. Conclude with `R0.zero_mem`. Use `⟨a, Finset.mem_insert_self _ _, hfa, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Break down `Finset.mem_insert.mp hy with rfl | hy` into its components or cases.

Rewrite using `[div_self hfa]`. Conclude with `R0.one_mem`. Establish `h3` using `R0.mul_mem (hall y hy) hinv`. Establish `e : f y / f j * (f j / f a) = f y / f a`. Clear the denominators using the available nonvanishing facts.

Rewrite `h3` using `[e]`. Then use the resulting hypothesis. Use `push_neg at hex`. Establish `hfa : f a ≠ 0`. Break down `Finset.mem_insert.mp hx with rfl | hx'` into its components or cases. Conclude with `hfx`.

Conclude with `absurd (hex x hx') hfx`. Use `⟨a, Finset.mem_insert_self _ _, hfa, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Break down `Finset.mem_insert.mp hy with rfl | hy` into its components or cases. Rewrite using `[div_self hfa]`.

Conclude with `R0.one_mem`. Rewrite using `[hex y hy, zero_div]`. Conclude with `R0.zero_mem`.
-/
theorem exists_pivot {α : Type} [DecidableEq α] (R0 : Subring LL) (hv : ∀ x : LL, x ∈ R0 ∨ x⁻¹ ∈ R0) (f : α → LL)
    (t : Finset α) : (∃ x ∈ t, f x ≠ 0) → ∃ j ∈ t, f j ≠ 0 ∧ ∀ x ∈ t, f x / f j ∈ R0 := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rintro ⟨x, hx, _⟩
    simp at hx
  | insert a t' ha ih =>
    rintro ⟨x, hx, hfx⟩
    by_cases hex : ∃ x ∈ t', f x ≠ 0
    · obtain ⟨j, hj, hfj, hall⟩ := ih hex
      by_cases hr : f a / f j ∈ R0
      · refine ⟨j, Finset.mem_insert_of_mem hj, hfj, ?_⟩
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hr
        · exact hall y hy
      · have hinv : f j / f a ∈ R0 := by
          have h2 := (hv (f a / f j)).resolve_left hr
          rwa [inv_div] at h2
        have hfa : f a ≠ 0 := by
          intro h0
          apply hr
          rw [h0, zero_div]
          exact R0.zero_mem
        refine ⟨a, Finset.mem_insert_self _ _, hfa, ?_⟩
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · rw [div_self hfa]
          exact R0.one_mem
        · have h3 := R0.mul_mem (hall y hy) hinv
          have e : f y / f j * (f j / f a) = f y / f a := by
            field_simp
          rwa [e] at h3
    · push_neg at hex
      have hfa : f a ≠ 0 := by
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact hfx
        · exact absurd (hex x hx') hfx
      refine ⟨a, Finset.mem_insert_self _ _, hfa, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · rw [div_self hfa]
        exact R0.one_mem
      · rw [hex y hy, zero_div]
        exact R0.zero_mem

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hv ((Module.forall_dual_apply_eq_zero_iff LL v).mp hc)`.
-/
theorem exists_dual_ne {v : Kf} (hv : v ≠ 0) : ∃ ℓ : Kf →ₗ[LL] LL, ℓ v ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact hv ((Module.forall_dual_apply_eq_zero_iff LL v).mp hc)

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `t ht c _ Q hQ`. Rewrite `ht` using `[Finset.card_eq_zero]`.

Substitute `ht` using the available equality. Simplify using `only [Finset.sum_empty] at hQ`. Establish `hQ0 : Q = 0`. Apply `MvPolynomial.map_injective _ (algebraMap LL Kf).injective` to reduce the goal to its premises. Rewrite using `[← hQ, map_zero]`.

Rewrite using `[hQ0]`. Conclude with `zero_mem _`. Consider the case `succ k ih`. Introduce `t ht c hc Q hQ`. Distinguish the cases in `hdep : LinearIndependent LL (fun x : t => (x : MvPolynomial ι LL))`.

Establish `hsum : ∀ ℓ : Kf →ₗ[LL] LL, ∑ x ∈ t, ℓ (c x) • x = ℓ 1 • Q`. Introduce `ℓ`. Apply `desc_fun ℓ t c 1 Q` to reduce the goal to its premises. Rewrite using `[map_one, one_mul]`. Conclude with `hQ`.

Establish `hrange : ∀ x ∈ t, c x ∈ Set.range (algebraMap LL Kf)`. Introduce `x0 hx0`. Assume the negation of the conclusion as `hnot`. Establish `hmk : (Submodule.span LL {(1 : Kf)}).mkQ (c x0) ≠ 0`. Rewrite using `[ne_eq, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]`.

Introduce and unpack `⟨a, ha⟩`. Apply `hnot` to reduce the goal to its premises. Conclude with `⟨a, by rw [Algebra.algebraMap_eq_smul_one]; exact ha⟩`. Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Module.Dual LL (Kf ⧸ Submodule.span LL {(1 : Kf)}), φ ((Submodule.span LL {(1 : Kf)}).mkQ (c x0)) ≠ 0 := by`. Assume the negation of the conclusion as `hc'`.

Use `push_neg at hc'`. Conclude with `hmk ((Module.forall_dual_apply_eq_zero_iff LL _).mp hc')`. Use `set ℓ : Kf →ₗ[LL] LL := φ.comp (Submodule.span LL {(1 : Kf)}).mkQ with hℓ`. Establish `hℓ1 : ℓ 1 = 0`. Simplify using `only [hℓ, LinearMap.comp_apply, Submodule.mkQ_apply]`.

Rewrite using `[(Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self 1), map_zero]`. Establish `h0` using `hsum ℓ`. Rewrite `h0` using `[hℓ1, zero_smul, ← Finset.sum_coe_sort t]`. Establish `h1` using `Fintype.linearIndependent_iff.mp hdep (fun x : t => ℓ (c x)) h0 ⟨x0, hx0⟩`. Conclude with `hφ h1`.

Use `choose d hd using fun x (hx : x ∈ t) => hrange x hx`. Take `⟨ℓ0, hℓ0⟩` from `exists_dual_ne (LL := LL) (Kf := Kf) (one_ne_zero : (1 : Kf) ≠ 0)`. Use `set ℓ1 : Kf →ₗ[LL] LL := (ℓ0 1)⁻¹ • ℓ0 with hℓ1def`. Establish `hℓ11 : ℓ1 1 = 1`. Simplify using `only [hℓ1def, LinearMap.smul_apply, smul_eq_mul]`.

Conclude with `inv_mul_cancel₀ hℓ0`. Establish `h0` using `hsum ℓ1`. Rewrite `h0` using `[hℓ11, one_smul]`. Rewrite using `[← h0]`. Use `Submodule.sum_mem _ fun x hx => ?_` and prove the remaining obligations.

Establish `hdx : ℓ1 (c x) = d x hx`. Rewrite using `[← hd x hx, Algebra.algebraMap_eq_smul_one, LinearMap.map_smul, hℓ11, smul_eq_mul, mul_one]`. Establish `hR : d x hx ∈ R0`. Rewrite using `[hR0, hd x hx]`. Conclude with `hc x hx`.

Rewrite using `[hdx]`. Conclude with `Submodule.smul_mem _ (⟨d x hx, hR⟩ : R0) (Submodule.subset_span hx)`. Take `⟨g, hg, i0, hi0⟩` from `Fintype.not_linearIndependent_iff.mp hdep`. Use `set f : MvPolynomial ι LL → LL := fun x => if h : x ∈ t then g ⟨x, h⟩ else 0 with hfdef`. Establish `hfsum : ∑ x ∈ t, f x • x = 0`.

Rewrite using `[← hg, ← Finset.sum_coe_sort t]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Simplify using `[hfdef, x.2]`. Take `⟨j, hj, hfj, hpiv⟩` from `exists_pivot R0 (fun x => by`. Distinguish the cases in `hx : algebraMap LL Kf x ∈ A`.

Conclude with `Or.inl ((hR0 x).mpr hx)`. Use `right`. Rewrite using `[hR0, map_inv₀]`. Conclude with `(hA _).resolve_left hx) f t ⟨i0, i0.2, by simpa [hfdef] using hi0⟩`. Establish `hcard : (t.erase j).card = k`.

Rewrite using `[Finset.card_erase_of_mem hj, ht]`. Simplify using the standard rewrite rules. Use `set c' : MvPolynomial ι LL → Kf := fun x => c x - c j * algebraMap LL Kf (f x / f j) with hc'def`. Establish `hc' : ∀ x ∈ (t.erase j), c' x ∈ A`. Introduce `x hx`.

Establish `hx'` using `Finset.mem_of_mem_erase hx`. Establish `hr : algebraMap LL Kf (f x / f j) ∈ A` using `(hR0 _).mp (hpiv x hx')`. Conclude with `A.sub_mem (hc x hx') (A.mul_mem (hc j hj) hr)`. Establish `hrel : ∑ x ∈ t.erase j, (f x / f j) • x = -j`. Establish `h1` using `hfsum`.

Rewrite `h1` using `[← Finset.add_sum_erase t _ hj]`. Establish `h2 : ∑ x ∈ t.erase j, (f x / f j) • x = (f j)⁻¹ • ∑ x ∈ t.erase j, f x • x`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, div_eq_mul_inv, mul_comm]`.

Rewrite using `[h2, eq_neg_of_add_eq_zero_right h1, smul_neg, smul_smul, inv_mul_cancel₀ hfj, one_smul]`. Establish `hQ' : ∑ x ∈ (t.erase j), C (c' x) * map (algebraMap LL Kf) x = map (algebraMap LL Kf) Q`. Rewrite using `[← hQ, ← Finset.add_sum_erase t _ hj]`. Simplify using `only [hc'def, map_sub, map_mul, sub_mul, Finset.sum_sub_distrib]`. Establish `e1 : ∑ x ∈ (t.erase j), C (c j) * C (algebraMap LL Kf (f x / f j)) * map (algebraMap LL Kf) x = C (c j) * map (algebraMap LL Kf) (∑ x ∈ (t.erase j), (f x / f j) • x)`.

Rewrite using `[map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, mul_assoc]`. Rewrite using `[e1]`. Establish `e2 : map (algebraMap LL Kf) (∑ x ∈ (t.erase j), (f x / f j) • x) = -map (algebraMap LL Kf) j`.

Rewrite using `[hrel, map_neg]`. Rewrite using `[e2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmem` using `ih (t.erase j) hcard c' hc' Q hQ'`. Conclude with `Submodule.span_mono (by`.

Introduce `x hx`. Conclude with `Finset.mem_of_mem_erase hx) hmem`.
-/
theorem desc_main (A : Subring Kf) (hA : ∀ x : Kf, x ∈ A ∨ x⁻¹ ∈ A) (R0 : Subring LL)
    (hR0 : ∀ x, x ∈ R0 ↔ algebraMap LL Kf x ∈ A) :
    ∀ (n : ℕ) (t : Finset (MvPolynomial ι LL)), t.card = n → ∀ c : MvPolynomial ι LL → Kf, (∀ x ∈ t, c x ∈ A) →
    ∀ Q : MvPolynomial ι LL, ∑ x ∈ t, C (c x) * map (algebraMap LL Kf) x = map (algebraMap LL Kf) Q →
    Q ∈ Submodule.span R0 (t : Set (MvPolynomial ι LL)) := by
  classical
  intro n
  induction n with
  | zero =>
    intro t ht c _ Q hQ
    rw [Finset.card_eq_zero] at ht
    subst ht
    simp only [Finset.sum_empty] at hQ
    have hQ0 : Q = 0 := by
      apply MvPolynomial.map_injective _ (algebraMap LL Kf).injective
      rw [← hQ, map_zero]
    rw [hQ0]
    exact zero_mem _
  | succ k ih =>
    intro t ht c hc Q hQ
    by_cases hdep : LinearIndependent LL (fun x : t => (x : MvPolynomial ι LL))
    ·
      have hsum : ∀ ℓ : Kf →ₗ[LL] LL, ∑ x ∈ t, ℓ (c x) • x = ℓ 1 • Q := by
        intro ℓ
        apply desc_fun ℓ t c 1 Q
        rw [map_one, one_mul]
        exact hQ
      have hrange : ∀ x ∈ t, c x ∈ Set.range (algebraMap LL Kf) := by
        intro x0 hx0
        by_contra hnot
        have hmk : (Submodule.span LL {(1 : Kf)}).mkQ (c x0) ≠ 0 := by
          rw [ne_eq, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
          rintro ⟨a, ha⟩
          apply hnot
          exact ⟨a, by rw [Algebra.algebraMap_eq_smul_one]; exact ha⟩
        obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual LL (Kf ⧸ Submodule.span LL {(1 : Kf)}),
            φ ((Submodule.span LL {(1 : Kf)}).mkQ (c x0)) ≠ 0 := by
          by_contra hc'
          push_neg at hc'
          exact hmk ((Module.forall_dual_apply_eq_zero_iff LL _).mp hc')
        set ℓ : Kf →ₗ[LL] LL := φ.comp (Submodule.span LL {(1 : Kf)}).mkQ with hℓ
        have hℓ1 : ℓ 1 = 0 := by
          simp only [hℓ, LinearMap.comp_apply, Submodule.mkQ_apply]
          rw [(Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self 1), map_zero]
        have h0 := hsum ℓ
        rw [hℓ1, zero_smul, ← Finset.sum_coe_sort t] at h0
        have h1 := Fintype.linearIndependent_iff.mp hdep (fun x : t => ℓ (c x)) h0 ⟨x0, hx0⟩
        exact hφ h1
      choose d hd using fun x (hx : x ∈ t) => hrange x hx
      obtain ⟨ℓ0, hℓ0⟩ := exists_dual_ne (LL := LL) (Kf := Kf) (one_ne_zero : (1 : Kf) ≠ 0)
      set ℓ1 : Kf →ₗ[LL] LL := (ℓ0 1)⁻¹ • ℓ0 with hℓ1def
      have hℓ11 : ℓ1 1 = 1 := by
        simp only [hℓ1def, LinearMap.smul_apply, smul_eq_mul]
        exact inv_mul_cancel₀ hℓ0
      have h0 := hsum ℓ1
      rw [hℓ11, one_smul] at h0
      rw [← h0]
      refine Submodule.sum_mem _ fun x hx => ?_
      have hdx : ℓ1 (c x) = d x hx := by
        rw [← hd x hx, Algebra.algebraMap_eq_smul_one, LinearMap.map_smul, hℓ11, smul_eq_mul, mul_one]
      have hR : d x hx ∈ R0 := by
        rw [hR0, hd x hx]
        exact hc x hx
      rw [hdx]
      exact Submodule.smul_mem _ (⟨d x hx, hR⟩ : R0) (Submodule.subset_span hx)
    ·
      obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hdep
      set f : MvPolynomial ι LL → LL := fun x => if h : x ∈ t then g ⟨x, h⟩ else 0 with hfdef
      have hfsum : ∑ x ∈ t, f x • x = 0 := by
        rw [← hg, ← Finset.sum_coe_sort t]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp [hfdef, x.2]
      obtain ⟨j, hj, hfj, hpiv⟩ := exists_pivot R0
        (fun x => by
          by_cases hx : algebraMap LL Kf x ∈ A
          · exact Or.inl ((hR0 x).mpr hx)
          · right
            rw [hR0, map_inv₀]
            exact (hA _).resolve_left hx) f t ⟨i0, i0.2, by simpa [hfdef] using hi0⟩
      have hcard : (t.erase j).card = k := by
        rw [Finset.card_erase_of_mem hj, ht]
        simp
      set c' : MvPolynomial ι LL → Kf := fun x => c x - c j * algebraMap LL Kf (f x / f j) with hc'def
      have hc' : ∀ x ∈ (t.erase j), c' x ∈ A := by
        intro x hx
        have hx' := Finset.mem_of_mem_erase hx
        have hr : algebraMap LL Kf (f x / f j) ∈ A := (hR0 _).mp (hpiv x hx')
        exact A.sub_mem (hc x hx') (A.mul_mem (hc j hj) hr)
      have hrel : ∑ x ∈ t.erase j, (f x / f j) • x = -j := by
        have h1 := hfsum
        rw [← Finset.add_sum_erase t _ hj] at h1
        have h2 : ∑ x ∈ t.erase j, (f x / f j) • x = (f j)⁻¹ • ∑ x ∈ t.erase j, f x • x := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [smul_smul, div_eq_mul_inv, mul_comm]
        rw [h2, eq_neg_of_add_eq_zero_right h1, smul_neg, smul_smul, inv_mul_cancel₀ hfj, one_smul]
      have hQ' : ∑ x ∈ (t.erase j), C (c' x) * map (algebraMap LL Kf) x = map (algebraMap LL Kf) Q := by
        rw [← hQ, ← Finset.add_sum_erase t _ hj]
        simp only [hc'def, map_sub, map_mul, sub_mul, Finset.sum_sub_distrib]
        have e1 : ∑ x ∈ (t.erase j), C (c j) * C (algebraMap LL Kf (f x / f j)) * map (algebraMap LL Kf) x =
            C (c j) * map (algebraMap LL Kf) (∑ x ∈ (t.erase j), (f x / f j) • x) := by
          rw [map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, mul_assoc]
        rw [e1]
        have e2 : map (algebraMap LL Kf) (∑ x ∈ (t.erase j), (f x / f j) • x) = -map (algebraMap LL Kf) j := by
          rw [hrel, map_neg]
        rw [e2]
        ring
      have hmem := ih (t.erase j) hcard c' hc' Q hQ'
      exact Submodule.span_mono (by
        intro x hx
        exact Finset.mem_of_mem_erase hx) hmem

end Desc

/- English proof (translation)
Introduce `LL Kf O ι _ _ _ _ _ _ _ e R0 hR0 S Q hQ`. Use `letI : Algebra LL Kf := e.toAlgebra`. Establish `he : ∀ x, algebraMap LL Kf x = e x` using `fun x => rfl`. Set `A : Subring Kf` to `(algebraMap O Kf).range`. Establish `hA : ∀ x : Kf, x ∈ A ∨ x⁻¹ ∈ A`.

Introduce `x`. Break down `ValuationRing.isInteger_or_isInteger O x with ⟨r, hr⟩ | ⟨r, hr⟩` into its components or cases. Conclude with `Or.inl ⟨r, hr⟩`. Conclude with `Or.inr ⟨r, hr⟩`. Establish `hR0' : ∀ x, x ∈ R0 ↔ algebraMap LL Kf x ∈ A`.

Introduce `x`. Rewrite using `[hR0 x, he]`. Both sides reduce to the same expression. Take `⟨cc, hsupp, hsum⟩` from `Submodule.mem_span_set.mp hQ`. Establish `hpre : ∀ y ∈ cc.support, ∃ q ∈ S, MvPolynomial.map e q = y` using `fun y hy => hsupp hy`.

Use `choose! qof hqS hqy using hpre`. Establish `htS : ((cc.support.image qof : Finset (MvPolynomial ι LL)) : Set (MvPolynomial ι LL)) ⊆ S`. Introduce `q hq`. Rewrite `hq` using `[Finset.coe_image]`. Take `⟨y, hy, rfl⟩` from `hq`.

Conclude with `hqS y hy`. Establish `hinjOn : Set.InjOn qof (cc.support : Set (MvPolynomial ι Kf))`. Introduce `y hy y' hy' h`. Rewrite using `[← hqy y hy, ← hqy y' hy', h]`. Set `c' : MvPolynomial ι LL → Kf` to `fun q => algebraMap O Kf (cc (MvPolynomial.map e q))`.

Establish `hc' : ∀ q ∈ cc.support.image qof, c' q ∈ A` using `fun q _ => ⟨_, rfl⟩`. Establish `hrel : ∑ q ∈ cc.support.image qof, C (c' q) * MvPolynomial.map (algebraMap LL Kf) q = MvPolynomial.map (algebraMap LL Kf) Q` using `by show ∑ q ∈ cc.support.image qof, C (c' q) * MvPolynomial.map e q = MvPolynomial.map e Q`. Rewrite using `[Finset.sum_image hinjOn, ← hsum, Finsupp.sum]`. Use `Finset.sum_congr rfl fun y hy => ?_` and prove the remaining obligations. Simplify using `only [c', hqy y hy]`.

Rewrite using `[Algebra.smul_def, MvPolynomial.algebraMap_apply]`. Conclude with `Submodule.span_mono htS (desc_main A hA R0 hR0' (cc.support.image qof).card (cc.support.image qof) rfl c' hc' Q hrel)`.
-/
theorem descVal : DescVal := by
  intro LL Kf O ι _ _ _ _ _ _ _ e R0 hR0 S Q hQ
  classical
  letI : Algebra LL Kf := e.toAlgebra
  have he : ∀ x, algebraMap LL Kf x = e x := fun x => rfl
  let A : Subring Kf := (algebraMap O Kf).range
  have hA : ∀ x : Kf, x ∈ A ∨ x⁻¹ ∈ A := by
    intro x
    rcases ValuationRing.isInteger_or_isInteger O x with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact Or.inl ⟨r, hr⟩
    · exact Or.inr ⟨r, hr⟩
  have hR0' : ∀ x, x ∈ R0 ↔ algebraMap LL Kf x ∈ A := by
    intro x
    rw [hR0 x, he]
    rfl
  obtain ⟨cc, hsupp, hsum⟩ := Submodule.mem_span_set.mp hQ
  have hpre : ∀ y ∈ cc.support, ∃ q ∈ S, MvPolynomial.map e q = y := fun y hy => hsupp hy
  choose! qof hqS hqy using hpre
  have htS : ((cc.support.image qof : Finset (MvPolynomial ι LL)) : Set (MvPolynomial ι LL)) ⊆ S := by
    intro q hq
    rw [Finset.coe_image] at hq
    obtain ⟨y, hy, rfl⟩ := hq
    exact hqS y hy
  have hinjOn : Set.InjOn qof (cc.support : Set (MvPolynomial ι Kf)) := by
    intro y hy y' hy' h
    rw [← hqy y hy, ← hqy y' hy', h]
  let c' : MvPolynomial ι LL → Kf := fun q => algebraMap O Kf (cc (MvPolynomial.map e q))
  have hc' : ∀ q ∈ cc.support.image qof, c' q ∈ A := fun q _ => ⟨_, rfl⟩
  have hrel : ∑ q ∈ cc.support.image qof, C (c' q) * MvPolynomial.map (algebraMap LL Kf) q =
      MvPolynomial.map (algebraMap LL Kf) Q := by
    show ∑ q ∈ cc.support.image qof, C (c' q) * MvPolynomial.map e q = MvPolynomial.map e Q
    rw [Finset.sum_image hinjOn, ← hsum, Finsupp.sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    simp only [c', hqy y hy]
    rw [Algebra.smul_def, MvPolynomial.algebraMap_apply]
  exact Submodule.span_mono htS
    (desc_main A hA R0 hR0' (cc.support.image qof).card (cc.support.image qof) rfl c' hc' Q hrel)

end Formalism.L2.G.RelativeIndexFlags
