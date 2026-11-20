import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.NormGauss

/- English proof (translation)
Set `F : Subfield k` to `RingHom.eqLocusField s (RingHom.id k)`. Set `σ : k ≃ₐ[F] k` to `{ toFun := s, invFun := s, left_inv := hs, right_inv := hs, map_mul' := map_mul s, map_add' := map_add s, commutes' := fun r => r.2 }`. Establish `hσ_apply : ∀ x, σ x = s x` using `fun _ => rfl`. Establish `hσ1 : σ ≠ 1`. Take `⟨a, ha⟩` from `hne`.

Introduce `h`. Apply `ha` to reduce the goal to its premises. Use `AlgEquiv.ext_iff.1 h a` as an intermediate fact. Rewrite `this` using `[hσ_apply, AlgEquiv.one_apply]`. Then use the resulting hypothesis. Establish `hσ2 : σ ^ 2 = 1`.

Use extensionality with `a`. Rewrite using `[pow_two, AlgEquiv.mul_apply, hσ_apply, hσ_apply, hs, AlgEquiv.one_apply]`. Establish `hfix : IntermediateField.fixedField (Subgroup.zpowers σ) = ⊥`. Use extensionality with `x`. Rewrite using `[IntermediateField.mem_fixedField_iff, IntermediateField.mem_bot]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨⟨x, h σ (Subgroup.mem_zpowers σ)⟩, rfl⟩`. Introduce and unpack `⟨r, rfl⟩ τ _`. Conclude with `τ.commutes r`.

Establish `htop : Subgroup.zpowers σ = ⊤`. Rewrite using `[← IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers σ), hfix]`. Use extensionality with `τ`. Simplify using `only [Subgroup.mem_top, iff_true]`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`.

Introduce `x hx`. Take `⟨r, rfl⟩` from `IntermediateField.mem_bot.1 hx`. Conclude with `τ.commutes r`. Establish `hcard : Fintype.card (k ≃ₐ[F] k) = 2`. Rewrite using `[← Nat.card_eq_fintype_card, ← Subgroup.card_top, ← htop, Nat.card_zpowers, orderOf_eq_prime hσ2 hσ1]`.

Establish `huniv : (Finset.univ : Finset (k ≃ₐ[F] k)) = {1, σ}`. Use `symm`. Apply `Finset.eq_univ_of_card` to reduce the goal to its premises. Rewrite using `[Finset.card_pair hσ1.symm, hcard]`. Establish `hnorm : ∀ t : k, algebraMap F k (Algebra.norm F t) = t * s t`.

Introduce `t`. Rewrite using `[Algebra.norm_eq_prod_automorphisms, huniv, Finset.prod_pair hσ1.symm]`. Both sides reduce to the same expression. Take `⟨t, ht⟩` from `FiniteField.norm_surjective F k (⟨u, hu⟩ : F)`. Use `⟨t, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hnorm, ht]`. Both sides reduce to the same expression.
-/
theorem exists_norm_eq {k : Type} [Field k] [Finite k] (s : k →+* k) (hs : ∀ a, s (s a) = a)
    (hne : ∃ a, s a ≠ a) (u : k) (hu : s u = u) : ∃ t, t * s t = u := by
  classical
  let F : Subfield k := RingHom.eqLocusField s (RingHom.id k)
  let σ : k ≃ₐ[F] k :=
    { toFun := s, invFun := s, left_inv := hs, right_inv := hs,
      map_mul' := map_mul s, map_add' := map_add s, commutes' := fun r => r.2 }
  have hσ_apply : ∀ x, σ x = s x := fun _ => rfl
  have hσ1 : σ ≠ 1 := by
    obtain ⟨a, ha⟩ := hne
    intro h
    apply ha
    have := AlgEquiv.ext_iff.1 h a
    rwa [hσ_apply, AlgEquiv.one_apply] at this
  have hσ2 : σ ^ 2 = 1 := by
    ext a
    rw [pow_two, AlgEquiv.mul_apply, hσ_apply, hσ_apply, hs, AlgEquiv.one_apply]
  have hfix : IntermediateField.fixedField (Subgroup.zpowers σ) = ⊥ := by
    ext x
    rw [IntermediateField.mem_fixedField_iff, IntermediateField.mem_bot]
    constructor
    · intro h
      exact ⟨⟨x, h σ (Subgroup.mem_zpowers σ)⟩, rfl⟩
    · rintro ⟨r, rfl⟩ τ _
      exact τ.commutes r
  have htop : Subgroup.zpowers σ = ⊤ := by
    rw [← IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers σ), hfix]
    ext τ
    simp only [Subgroup.mem_top, iff_true]
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.1 hx
    exact τ.commutes r
  have hcard : Fintype.card (k ≃ₐ[F] k) = 2 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.card_top, ← htop, Nat.card_zpowers,
      orderOf_eq_prime hσ2 hσ1]
  have huniv : (Finset.univ : Finset (k ≃ₐ[F] k)) = {1, σ} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hσ1.symm, hcard]
  have hnorm : ∀ t : k, algebraMap F k (Algebra.norm F t) = t * s t := by
    intro t
    rw [Algebra.norm_eq_prod_automorphisms, huniv, Finset.prod_pair hσ1.symm]
    rfl
  obtain ⟨t, ht⟩ := FiniteField.norm_surjective F k (⟨u, hu⟩ : F)
  refine ⟨t, ?_⟩
  rw [← hnorm, ht]
  rfl

/- English proof (translation)
Set `F : Subfield k` to `RingHom.eqLocusField s (RingHom.id k)`. Establish `hs0 : ∀ x : k, s x = 0 → x = 0`. Introduce `x h`. Use `congrArg s h` as an intermediate fact. Rewrite `this` using `[hs, map_zero]`. Then use the resulting hypothesis.

Establish `hNF : ∀ t : k, t * s t ∈ F` using `fun t => by show s (t * s t) = t * s t`. Rewrite using `[map_mul, hs, mul_comm]`. Set `N : k → F` to `fun t => ⟨t * s t, hNF t⟩`. Establish `hN : ∀ t, ((N t : F) : k) = t * s t` using `fun _ => rfl`. Set `φ : AddChar F ℂ` to `ψ.compAddMonoidHom F.subtype.toAddMonoidHom`.

Establish `hφ_apply : ∀ u : F, φ u = ψ (u : k)` using `fun _ => rfl`. Establish `hφ : φ ≠ 1`. Take `⟨a, ha⟩` from `hψ`. Introduce `h`. Establish `hmem : a + s a ∈ F` using `by show s (a + s a) = a + s a`.

Rewrite using `[map_add, hs, add_comm]`. Apply `ha` to reduce the goal to its premises. Use `congrArg (fun χ : AddChar F ℂ => χ ⟨a + s a, hmem⟩) h` as an intermediate fact. Simplify `this` using `only [hφ_apply, AddChar.one_apply]`. Establish `hsumφ : ∑ u : F, ψ (u : k) = 0`.

Simplify `AddChar.sum_eq_zero_of_ne_one hφ` using `only [hφ_apply]`. Take `⟨c, hc⟩ : ∃ c : ℕ, c = (Finset.univ.filter (fun t : k => t * s t = 1)).card` from `⟨_, rfl⟩`. Establish `hfib : ∀ u : F, (Finset.univ.filter (fun t : k => N t = u)).card = if u = 0 then 1 else c`. Introduce `u`. Use `split_ifs with hu`.

Substitute `hu` using the available equality. Rewrite using `[Finset.card_eq_one]`. Use `⟨0, ?_⟩` and prove the remaining obligations. Use extensionality with `t`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : t * s t = 0` using `congrArg Subtype.val h`. Break down `mul_eq_zero.1 h' with h0 | h0` into its components or cases. Conclude with `h0`.

Conclude with `hs0 t h0`. Introduce and unpack `rfl`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hN, zero_mul]`. Both sides reduce to the same expression.

Take `⟨t0, ht0⟩` from `exists_norm_eq s hs hne (u : k) u.2`. Establish `hu0 : (u : k) ≠ 0` using `fun h => hu (Subtype.ext h)`. Establish `ht0ne : t0 ≠ 0`. Introduce and unpack `rfl`. Apply `hu0` to reduce the goal to its premises.

Rewrite using `[← ht0, zero_mul]`. Rewrite using `[hc]`. Apply `Finset.card_nbij' (fun t => t * t0⁻¹) (fun t => t * t0)` to reduce the goal to its premises. Introduce `t ht`. Simplify using `only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢`.

Establish `h' : t * s t = u` using `congrArg Subtype.val ht`. Establish `e : t * t0⁻¹ * s (t * t0⁻¹) = (t * s t) * (t0 * s t0)⁻¹`. Rewrite using `[map_mul, map_inv₀, mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, h', ht0, mul_inv_cancel₀ hu0]`.

Introduce `t ht`. Simplify using `only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hN]`. Establish `e : t * t0 * s (t * t0) = (t * s t) * (t0 * s t0)`.

Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, ht, ht0, one_mul]`. Introduce `t _`. Conclude with `inv_mul_cancel_right₀ ht0ne t`.

Introduce `t _`. Conclude with `mul_inv_cancel_right₀ ht0ne t`. Establish `hsplit : ∑ t : k, ψ (t * s t) = ∑ u : F, ((Finset.univ.filter (fun t : k => N t = u)).card : ℂ) * ψ (u : k)`. Rewrite using `[← Finset.sum_fiberwise Finset.univ N (fun t => ψ (t * s t))]`. Use `Finset.sum_congr rfl (fun u _ => ?_)` and prove the remaining obligations.

Rewrite using `[Finset.sum_congr rfl (g := fun _ => ψ (u : k)), Finset.sum_const, nsmul_eq_mul]`. Introduce `t ht`. Use `(Finset.mem_filter.1 ht).2` as an intermediate fact. Rewrite using `[← this]`. Establish `hψ0 : ψ ((0 : F) : k) = 1`.

Rewrite using `[ZeroMemClass.coe_zero, AddChar.map_zero_eq_one]`. Establish `key : ∀ u : F, (((if u = 0 then 1 else c : ℕ)) : ℂ) * ψ (u : k) = (c : ℂ) * ψ (u : k) + (if u = 0 then (1 - (c : ℂ)) else 0)`. Introduce `u`. Use `split_ifs with h`. Substitute `h` using the available equality.

Rewrite using `[hψ0]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree. Establish `hval : ∑ u : F, (((if u = 0 then 1 else c : ℕ)) : ℂ) * ψ (u : k) = 1 - c`.

Rewrite using `[Finset.sum_congr rfl (fun u _ => key u), Finset.sum_add_distrib, ← Finset.mul_sum, hsumφ, mul_zero, zero_add]`. Simplify using the standard rewrite rules. Establish `hc2 : 2 ≤ c`. Take `⟨a, ha⟩` from `hne`. Establish `ha0 : a ≠ 0`.

Introduce and unpack `rfl`. Conclude with `ha (map_zero s)`. Establish `hsa0 : s a ≠ 0` using `fun h => ha0 (hs0 a h)`. Establish `hne1 : a * (s a)⁻¹ ≠ 1`. Introduce `h`.

Apply `ha` to reduce the goal to its premises. Rewrite `h` using `[mul_inv_eq_one₀ hsa0]`. Conclude with `h.symm`. Rewrite using `[hc]`. Combine the equalities or inequalities in the displayed calculation.

Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `x hx`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hx`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Break down `hx with rfl | rfl` into its components or cases.

Rewrite using `[map_one, one_mul]`. Rewrite using `[map_mul, map_inv₀, hs]`. Clear the denominators using the available nonvanishing facts. Use `⟨(c : ℝ) - 1, ?_, ?_⟩` and prove the remaining obligations. Establish `: (2 : ℝ) ≤ c` using `by exact_mod_cast hc2`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hsplit]`. Repeatedly rewrite using `[hfib]`. Rewrite using `[hval]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_norm_neg {k : Type} [Field k] [Fintype k] (s : k →+* k) (hs : ∀ a, s (s a) = a)
    (hne : ∃ a, s a ≠ a) (ψ : AddChar k ℂ) (hψ : ∃ a, ψ (a + s a) ≠ 1) :
    ∃ m : ℝ, 0 < m ∧ ∑ t : k, ψ (t * s t) = -(m : ℂ) := by
  classical
  let F : Subfield k := RingHom.eqLocusField s (RingHom.id k)
  have hs0 : ∀ x : k, s x = 0 → x = 0 := by
    intro x h
    have := congrArg s h
    rwa [hs, map_zero] at this
  have hNF : ∀ t : k, t * s t ∈ F := fun t => by
    show s (t * s t) = t * s t
    rw [map_mul, hs, mul_comm]
  let N : k → F := fun t => ⟨t * s t, hNF t⟩
  have hN : ∀ t, ((N t : F) : k) = t * s t := fun _ => rfl
  let φ : AddChar F ℂ := ψ.compAddMonoidHom F.subtype.toAddMonoidHom
  have hφ_apply : ∀ u : F, φ u = ψ (u : k) := fun _ => rfl
  have hφ : φ ≠ 1 := by
    obtain ⟨a, ha⟩ := hψ
    intro h
    have hmem : a + s a ∈ F := by
      show s (a + s a) = a + s a
      rw [map_add, hs, add_comm]
    apply ha
    have := congrArg (fun χ : AddChar F ℂ => χ ⟨a + s a, hmem⟩) h
    simpa only [hφ_apply, AddChar.one_apply] using this
  have hsumφ : ∑ u : F, ψ (u : k) = 0 := by
    simpa only [hφ_apply] using AddChar.sum_eq_zero_of_ne_one hφ
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = (Finset.univ.filter (fun t : k => t * s t = 1)).card := ⟨_, rfl⟩
  have hfib : ∀ u : F,
      (Finset.univ.filter (fun t : k => N t = u)).card = if u = 0 then 1 else c := by
    intro u
    split_ifs with hu
    · subst hu
      rw [Finset.card_eq_one]
      refine ⟨0, ?_⟩
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        have h' : t * s t = 0 := congrArg Subtype.val h
        rcases mul_eq_zero.1 h' with h0 | h0
        · exact h0
        · exact hs0 t h0
      · rintro rfl
        apply Subtype.ext
        rw [hN, zero_mul]
        rfl
    · obtain ⟨t0, ht0⟩ := exists_norm_eq s hs hne (u : k) u.2
      have hu0 : (u : k) ≠ 0 := fun h => hu (Subtype.ext h)
      have ht0ne : t0 ≠ 0 := by
        rintro rfl
        apply hu0
        rw [← ht0, zero_mul]
      rw [hc]
      apply Finset.card_nbij' (fun t => t * t0⁻¹) (fun t => t * t0)
      · intro t ht
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
        have h' : t * s t = u := congrArg Subtype.val ht
        have e : t * t0⁻¹ * s (t * t0⁻¹) = (t * s t) * (t0 * s t0)⁻¹ := by
          rw [map_mul, map_inv₀, mul_inv]
          ring
        rw [e, h', ht0, mul_inv_cancel₀ hu0]
      · intro t ht
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
        apply Subtype.ext
        rw [hN]
        have e : t * t0 * s (t * t0) = (t * s t) * (t0 * s t0) := by
          rw [map_mul]
          ring
        rw [e, ht, ht0, one_mul]
      · intro t _
        exact inv_mul_cancel_right₀ ht0ne t
      · intro t _
        exact mul_inv_cancel_right₀ ht0ne t
  have hsplit : ∑ t : k, ψ (t * s t) =
      ∑ u : F, ((Finset.univ.filter (fun t : k => N t = u)).card : ℂ) * ψ (u : k) := by
    rw [← Finset.sum_fiberwise Finset.univ N (fun t => ψ (t * s t))]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.sum_congr rfl (g := fun _ => ψ (u : k)), Finset.sum_const, nsmul_eq_mul]
    intro t ht
    have := (Finset.mem_filter.1 ht).2
    rw [← this]
  have hψ0 : ψ ((0 : F) : k) = 1 := by
    rw [ZeroMemClass.coe_zero, AddChar.map_zero_eq_one]
  have key : ∀ u : F, (((if u = 0 then 1 else c : ℕ)) : ℂ) * ψ (u : k) =
      (c : ℂ) * ψ (u : k) + (if u = 0 then (1 - (c : ℂ)) else 0) := by
    intro u
    split_ifs with h
    · subst h
      rw [hψ0]
      push_cast
      ring
    · ring
  have hval : ∑ u : F, (((if u = 0 then 1 else c : ℕ)) : ℂ) * ψ (u : k) = 1 - c := by
    rw [Finset.sum_congr rfl (fun u _ => key u), Finset.sum_add_distrib, ← Finset.mul_sum, hsumφ,
      mul_zero, zero_add]
    simp
  have hc2 : 2 ≤ c := by
    obtain ⟨a, ha⟩ := hne
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact ha (map_zero s)
    have hsa0 : s a ≠ 0 := fun h => ha0 (hs0 a h)
    have hne1 : a * (s a)⁻¹ ≠ 1 := by
      intro h
      apply ha
      rw [mul_inv_eq_one₀ hsa0] at h
      exact h.symm
    rw [hc]
    calc 2 = ({1, a * (s a)⁻¹} : Finset k).card := (Finset.card_pair hne1.symm).symm
      _ ≤ _ := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hx with rfl | rfl
        · rw [map_one, one_mul]
        · rw [map_mul, map_inv₀, hs]
          field_simp
  refine ⟨(c : ℝ) - 1, ?_, ?_⟩
  · have : (2 : ℝ) ≤ c := by exact_mod_cast hc2
    linarith
  · rw [hsplit]
    simp_rw [hfib]
    rw [hval]
    push_cast
    ring

/- English proof (translation)
Introduce `R _ σ P _ _ hσ hP hne χ hχ hχP hχa`. Set `_ : Field (R ⧸ P)` to `Ideal.Quotient.field P`. Set `_ : Fintype (R ⧸ P)` to `Fintype.ofFinite _`. Establish `hle : P ≤ P.comap σ` using `fun a ha => hP a ha`. Set `s : R ⧸ P →+* R ⧸ P` to `Ideal.quotientMap P σ hle`.

Establish `hs_mk : ∀ a : R, s (Ideal.Quotient.mk P a) = Ideal.Quotient.mk P (σ a)` using `fun a => Ideal.quotientMap_mk`. Establish `hs : ∀ x, s (s x) = x`. Introduce `x`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite using `[hs_mk, hs_mk, hσ]`.

Establish `hsne : ∃ x, s x ≠ x`. Take `⟨a, ha⟩` from `hne`. Use `⟨Ideal.Quotient.mk P a, ?_⟩` and prove the remaining obligations. Rewrite using `[hs_mk]`. Introduce `h`.

Apply `ha` to reduce the goal to its premises. Establish `h'` using `P.neg_mem (Ideal.Quotient.eq.1 h)`. Rewrite `h'` using `[neg_sub]`. Then use the resulting hypothesis. Establish `hχ_congr : ∀ x y : R, x - y ∈ P → χ x = χ y`. Introduce `x y h`.

Establish `e : x = y + (x - y)` using `by ring`. Use `conv_lhs => rw [e]`. Rewrite using `[hχ, hχP _ h, mul_one]`. Set `ψ : AddChar (R ⧸ P) ℂ` to `{ toFun := fun q => χ (Quotient.out q) map_zero_eq_one' := by`. Apply `hχP` to reduce the goal to its premises.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_out]`. Use the proof step `map_add_eq_mul' := by`. Introduce `q₁ q₂`. Rewrite using `[← hχ]`. Apply `hχ_congr` to reduce the goal to its premises.

Rewrite using `[← Ideal.Quotient.eq, map_add, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out] }`. Establish `hψ_mk : ∀ a, ψ (Ideal.Quotient.mk P a) = χ a` using `fun a => hχ_congr _ _ (by rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out])`. Establish `hψne : ∃ x, ψ (x + s x) ≠ 1`. Take `⟨a, ha⟩` from `hχa`. Conclude with `⟨Ideal.Quotient.mk P a, by rw [hs_mk, ← map_add, hψ_mk]; exact ha⟩`.

Take `⟨m, hm, hsum⟩` from `sum_norm_neg s hs hsne ψ hψne`. Use `⟨m, hm, ?_⟩` and prove the remaining obligations. Rewrite using `[finsum_eq_sum_of_fintype, ← hsum]`. Use `Finset.sum_congr rfl (fun q _ => ?_)` and prove the remaining obligations. Use `conv_rhs => rw [← Ideal.Quotient.mk_out q]`.

Rewrite using `[hs_mk, ← map_mul, hψ_mk]`.
-/
theorem finsum_norm_neg : ∀ (R : Type) [CommRing R] (σ : R →+* R) (P : Ideal R) [P.IsMaximal] [Finite (R ⧸ P)], (∀ a, σ (σ a) = a) → (∀ a ∈ P, σ a ∈ P) → (∃ a, a - σ a ∉ P) → ∀ χ : R → ℂ, (∀ a b, χ (a + b) = χ a * χ b) → (∀ a ∈ P, χ a = 1) → (∃ a, χ (a + σ a) ≠ 1) → ∃ m : ℝ, 0 < m ∧ ∑ᶠ q : R ⧸ P, χ (Quotient.out q * σ (Quotient.out q)) = -(m : ℂ) := by
  intro R _ σ P _ _ hσ hP hne χ hχ hχP hχa
  classical
  let _ : Field (R ⧸ P) := Ideal.Quotient.field P
  let _ : Fintype (R ⧸ P) := Fintype.ofFinite _
  have hle : P ≤ P.comap σ := fun a ha => hP a ha
  let s : R ⧸ P →+* R ⧸ P := Ideal.quotientMap P σ hle
  have hs_mk : ∀ a : R, s (Ideal.Quotient.mk P a) = Ideal.Quotient.mk P (σ a) :=
    fun a => Ideal.quotientMap_mk
  have hs : ∀ x, s (s x) = x := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hs_mk, hs_mk, hσ]
  have hsne : ∃ x, s x ≠ x := by
    obtain ⟨a, ha⟩ := hne
    refine ⟨Ideal.Quotient.mk P a, ?_⟩
    rw [hs_mk]
    intro h
    apply ha
    have h' := P.neg_mem (Ideal.Quotient.eq.1 h)
    rwa [neg_sub] at h'
  have hχ_congr : ∀ x y : R, x - y ∈ P → χ x = χ y := by
    intro x y h
    have e : x = y + (x - y) := by ring
    conv_lhs => rw [e]
    rw [hχ, hχP _ h, mul_one]
  let ψ : AddChar (R ⧸ P) ℂ :=
    { toFun := fun q => χ (Quotient.out q)
      map_zero_eq_one' := by
        apply hχP
        rw [← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_out]
      map_add_eq_mul' := by
        intro q₁ q₂
        rw [← hχ]
        apply hχ_congr
        rw [← Ideal.Quotient.eq, map_add, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out,
          Ideal.Quotient.mk_out] }
  have hψ_mk : ∀ a, ψ (Ideal.Quotient.mk P a) = χ a := fun a =>
    hχ_congr _ _ (by rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out])
  have hψne : ∃ x, ψ (x + s x) ≠ 1 := by
    obtain ⟨a, ha⟩ := hχa
    exact ⟨Ideal.Quotient.mk P a, by rw [hs_mk, ← map_add, hψ_mk]; exact ha⟩
  obtain ⟨m, hm, hsum⟩ := sum_norm_neg s hs hsne ψ hψne
  refine ⟨m, hm, ?_⟩
  rw [finsum_eq_sum_of_fintype, ← hsum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  conv_rhs => rw [← Ideal.Quotient.mk_out q]
  rw [hs_mk, ← map_mul, hψ_mk]

end GlobalTheory.NormGauss
