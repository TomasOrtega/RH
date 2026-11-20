import Mathlib

/- English proof (translation)
Introduce `l _`. Establish `hna : ∀ x y : PadicAlgCl l, ‖x + y‖ ≤ max ‖x‖ ‖y‖` using `fun x y => IsUltrametricDist.norm_add_le_max x y`. Set `A : Subring (PadicAlgCl l)` to `{ carrier := {x | ‖x‖ ≤ 1} mul_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq, norm_mul] at *`. Conclude with `mul_le_one₀ ha (norm_nonneg _) hb`.

Use the proof step `one_mem' := by simp`. Use the proof step `add_mem' := fun {a b} ha hb => (hna a b).trans (max_le ha hb)`. Use the proof step `zero_mem' := by simp`. Use the proof step `neg_mem' := fun {a} ha => by simpa using ha }`. Establish `hA : ∀ x : PadicAlgCl l, x ∈ A ↔ ‖x‖ ≤ 1` using `fun x => Iff.rfl`.

Set `I : Ideal A` to `{ carrier := {x | ‖(x : PadicAlgCl l)‖ < 1} add_mem' := fun {a b} ha hb => lt_of_le_of_lt (hna _ _) (max_lt ha hb) zero_mem' := by simp smul_mem' := fun c x hx => by show ‖((c * x : A) : PadicAlgCl l)‖ < 1`. Rewrite using `[Subring.coe_mul, norm_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) c.2) hx }`. Establish `hI : ∀ x : A, x ∈ I ↔ ‖(x : PadicAlgCl l)‖ < 1` using `fun x => Iff.rfl`. Establish `hmax : I.IsMaximal`.

Rewrite using `[Ideal.isMaximal_iff]`. Use `⟨by simp [hI], fun J x hIJ hx hxJ => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[hI, not_lt]`. Establish `h1 : ‖(x : PadicAlgCl l)‖ = 1` using `le_antisymm x.2 hx`. Establish `hx0 : (x : PadicAlgCl l) ≠ 0`.

Introduce `h`. Rewrite `h1` using `[h, norm_zero]`. Conclude with `zero_ne_one h1`. Establish `hinv : (x : PadicAlgCl l)⁻¹ ∈ A`. Rewrite using `[hA, norm_inv, h1, inv_one]`.

Establish `: (⟨_, hinv⟩ : A) * x = 1` using `Subtype.ext (inv_mul_cancel₀ hx0)`. Rewrite using `[← this]`. Conclude with `J.mul_mem_left _ hxJ`. Use `haveI := hmax`. Establish `hl : ‖((l : A) : PadicAlgCl l)‖ < 1`.

Establish `h` using `congrArg NNReal.toReal (PadicAlgCl.valuation_p l)`. Rewrite `h` using `[PadicAlgCl.valuation_coe]`. Use `push_cast`. Rewrite using `[h]`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`.

Simplify using `only [one_div, NNReal.coe_inv, NNReal.coe_natCast]`. Conclude with `inv_lt_one_of_one_lt₀ hl1`. Use `⟨A ⧸ I, Ideal.Quotient.field I, ?_, A, Ideal.Quotient.mk I, hA, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)]`. Rewrite using `[← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `hl`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hI x`.
-/
theorem UpperTheory.exists_residue_map_padicAlgCl_integers :
    ∀ (l : ℕ) [Fact l.Prime], ∃ (k : Type) (_ : Field k) (_ : CharP k l) (A : Subring (PadicAlgCl l)) (red : A →+* k), (∀ x : PadicAlgCl l, x ∈ A ↔ ‖x‖ ≤ 1) ∧ ∀ x : A, red x = 0 ↔ ‖(x : PadicAlgCl l)‖ < 1 := by
  intro l _
  have hna : ∀ x y : PadicAlgCl l, ‖x + y‖ ≤ max ‖x‖ ‖y‖ := fun x y =>
    IsUltrametricDist.norm_add_le_max x y
  let A : Subring (PadicAlgCl l) :=
    { carrier := {x | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, norm_mul] at *
        exact mul_le_one₀ ha (norm_nonneg _) hb
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => (hna a b).trans (max_le ha hb)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by simpa using ha }
  have hA : ∀ x : PadicAlgCl l, x ∈ A ↔ ‖x‖ ≤ 1 := fun x => Iff.rfl
  let I : Ideal A :=
    { carrier := {x | ‖(x : PadicAlgCl l)‖ < 1}
      add_mem' := fun {a b} ha hb => lt_of_le_of_lt (hna _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        show ‖((c * x : A) : PadicAlgCl l)‖ < 1
        rw [Subring.coe_mul, norm_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) c.2) hx }
  have hI : ∀ x : A, x ∈ I ↔ ‖(x : PadicAlgCl l)‖ < 1 := fun x => Iff.rfl
  have hmax : I.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨by simp [hI], fun J x hIJ hx hxJ => ?_⟩
    rw [hI, not_lt] at hx
    have h1 : ‖(x : PadicAlgCl l)‖ = 1 := le_antisymm x.2 hx
    have hx0 : (x : PadicAlgCl l) ≠ 0 := by
      intro h
      rw [h, norm_zero] at h1
      exact zero_ne_one h1
    have hinv : (x : PadicAlgCl l)⁻¹ ∈ A := by
      rw [hA, norm_inv, h1, inv_one]
    have : (⟨_, hinv⟩ : A) * x = 1 := Subtype.ext (inv_mul_cancel₀ hx0)
    rw [← this]
    exact J.mul_mem_left _ hxJ
  haveI := hmax
  have hl : ‖((l : A) : PadicAlgCl l)‖ < 1 := by
    have h := congrArg NNReal.toReal (PadicAlgCl.valuation_p l)
    rw [PadicAlgCl.valuation_coe] at h
    push_cast
    rw [h]
    have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    simp only [one_div, NNReal.coe_inv, NNReal.coe_natCast]
    exact inv_lt_one_of_one_lt₀ hl1
  refine ⟨A ⧸ I, Ideal.Quotient.field I, ?_, A, Ideal.Quotient.mk I, hA, fun x => ?_⟩
  · rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)]
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact hl
  · rw [Ideal.Quotient.eq_zero_iff_mem]
    exact hI x
