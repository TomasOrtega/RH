import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Unfold `IsIdempotentElem`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun e he => (hs e he).one_sub`.
-/
private lemma idem_prod_one_sub {B : Type} [CommRing B] (s : Finset B)
    (hs : ∀ e ∈ s, IsIdempotentElem e) : IsIdempotentElem (∏ e ∈ s, (1 - e)) := by
  unfold IsIdempotentElem
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun e he => (hs e he).one_sub

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha]`. Establish `h1 : a ∈ I` using `hs a (Finset.mem_insert_self a s)`.

Establish `h2` using `ih fun e he => hs e (Finset.mem_insert_of_mem he)`. Establish `: 1 - (1 - a) * ∏ e ∈ s, (1 - e) = (1 - ∏ e ∈ s, (1 - e)) + a * ∏ e ∈ s, (1 - e)` using `by ring`. Rewrite using `[this]`. Conclude with `I.add_mem h2 (I.mul_mem_right _ h1)`.
-/
private lemma one_sub_prod_mem {B : Type} [CommRing B] (I : Ideal B) (s : Finset B)
    (hs : ∀ e ∈ s, e ∈ I) : 1 - ∏ e ∈ s, (1 - e) ∈ I := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h1 : a ∈ I := hs a (Finset.mem_insert_self a s)
    have h2 := ih fun e he => hs e (Finset.mem_insert_of_mem he)
    have : 1 - (1 - a) * ∏ e ∈ s, (1 - e) = (1 - ∏ e ∈ s, (1 - e)) + a * ∏ e ∈ s, (1 - e) := by ring
    rw [this]
    exact I.add_mem h2 (I.mul_mem_right _ h1)

/- English proof (translation)
Set `E : Set B` to `{e | IsIdempotentElem e ∧ ∃ σ, e ∈ J σ}`. Establish `hE : Ideal.span E = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨𝔪, hm, hle⟩` from `Ideal.exists_le_maximal _ hne`. Take `⟨σ, e, he, hi, hn⟩` from `h 𝔪 hm`.

Conclude with `hn (hle (Ideal.subset_span ⟨hi, σ, he⟩))`. Take `⟨t, htE, ht⟩` from `(Ideal.span_eq_top_iff_finite E).1 hE`. Use `⟨fun σ => 1 - ∏ e ∈ t.filter (· ∈ J σ), (1 - e), fun σ => ?_, fun σ => ?_, ?_⟩` and prove the remaining obligations. Conclude with `(idem_prod_one_sub _ fun e he => (htE (Finset.mem_filter.1 he).1).1).one_sub`. Conclude with `one_sub_prod_mem _ _ fun e he => (Finset.mem_filter.1 he).2`.

Use `set g : B := ∏ σ, (1 - (1 - ∏ e ∈ t.filter (· ∈ J σ), (1 - e))) with hg`. Establish `hkill : ∀ e ∈ t, e * g = 0`. Introduce `e he`. Take `⟨hi, σ, hσ⟩` from `htE he`. Establish `hef : e ∈ t.filter (· ∈ J σ)` using `Finset.mem_filter.2 ⟨he, hσ⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : (1 - e) ∣ g := by`. Use `dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ σ))` and prove the remaining obligations. Rewrite using `[sub_sub_cancel]`. Conclude with `Finset.dvd_prod_of_mem _ hef`. Establish `h0 : e * (1 - e) = 0`.

Establish `: e * e = e` using `hi`. Rewrite using `[mul_sub, mul_one, this, sub_self]`. Rewrite using `[hc, ← mul_assoc, h0, zero_mul]`. Establish `hall : ∀ x ∈ Ideal.span (t : Set B), x * g = 0`. Introduce `x hx`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact hkill x hx`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [add_mul, hx, hy, add_zero]`. Consider the case `smul a x _ hx => rw [smul_eq_mul, mul_assoc, hx, mul_zero]`.

Use `hall 1 (by rw [ht]; trivial)` as an intermediate fact. Rewrite `this` using `[one_mul]`. Then use the resulting hypothesis.
-/
private lemma cover_step {B : Type} [CommRing B] (Λ : Type) [Fintype Λ] (J : Λ → Ideal B)
    (h : ∀ 𝔪 : Ideal B, 𝔪.IsMaximal → ∃ σ, ∃ e ∈ J σ, IsIdempotentElem e ∧ e ∉ 𝔪) :
    ∃ f : Λ → B, (∀ σ, IsIdempotentElem (f σ)) ∧ (∀ σ, f σ ∈ J σ) ∧ ∏ σ, (1 - f σ) = 0 := by
  classical
  let E : Set B := {e | IsIdempotentElem e ∧ ∃ σ, e ∈ J σ}
  have hE : Ideal.span E = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨σ, e, he, hi, hn⟩ := h 𝔪 hm
    exact hn (hle (Ideal.subset_span ⟨hi, σ, he⟩))
  obtain ⟨t, htE, ht⟩ := (Ideal.span_eq_top_iff_finite E).1 hE
  refine ⟨fun σ => 1 - ∏ e ∈ t.filter (· ∈ J σ), (1 - e), fun σ => ?_, fun σ => ?_, ?_⟩
  · exact (idem_prod_one_sub _ fun e he => (htE (Finset.mem_filter.1 he).1).1).one_sub
  · exact one_sub_prod_mem _ _ fun e he => (Finset.mem_filter.1 he).2
  · set g : B := ∏ σ, (1 - (1 - ∏ e ∈ t.filter (· ∈ J σ), (1 - e))) with hg
    have hkill : ∀ e ∈ t, e * g = 0 := by
      intro e he
      obtain ⟨hi, σ, hσ⟩ := htE he
      have hef : e ∈ t.filter (· ∈ J σ) := Finset.mem_filter.2 ⟨he, hσ⟩
      obtain ⟨c, hc⟩ : (1 - e) ∣ g := by
        refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ σ))
        rw [sub_sub_cancel]
        exact Finset.dvd_prod_of_mem _ hef
      have h0 : e * (1 - e) = 0 := by
        have : e * e = e := hi
        rw [mul_sub, mul_one, this, sub_self]
      rw [hc, ← mul_assoc, h0, zero_mul]
    have hall : ∀ x ∈ Ideal.span (t : Set B), x * g = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact hkill x hx
      | zero => simp
      | add x y _ _ hx hy => rw [add_mul, hx, hy, add_zero]
      | smul a x _ hx => rw [smul_eq_mul, mul_assoc, hx, mul_zero]
    have := hall 1 (by rw [ht]; trivial)
    rwa [one_mul] at this

/- English proof (translation)
Introduce `B _ Λ _ J h`. Take `⟨f, hfi, hfJ, hf0⟩` from `cover_step Λ J h`. Use `letI : LinearOrder Λ := LinearOrder.lift' (Fintype.equivFin Λ) (Equiv.injective _)`. Set `P : Λ → B` to `fun σ => ∏ τ ∈ Finset.univ.filter (· < σ), (1 - f τ)`. Establish `hP : ∀ σ, IsIdempotentElem (P σ)`.

Introduce `σ`. Use `show P σ * P σ = P σ`. Simplify using `only [P]`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun τ _ => (hfi τ).one_sub`.

Establish `hkill : ∀ σ τ, τ < σ → P σ * f τ = 0`. Introduce `σ τ hτ`. Take `⟨c, hc⟩ : (1 - f τ) ∣ P σ` from `Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ τ, hτ⟩)`. Establish `h0 : (1 - f τ) * f τ = 0`. Establish `: f τ * f τ = f τ` using `hfi τ`.

Rewrite using `[sub_mul, one_mul, this, sub_self]`. Rewrite using `[hc, mul_comm (1 - f τ) c, mul_assoc, h0, mul_zero]`. Establish `hlt : ∀ σ τ, τ < σ → (f σ * P σ) * (f τ * P τ) = 0`. Introduce `σ τ hτ`. Establish `: (f σ * P σ) * (f τ * P τ) = f σ * (P σ * f τ) * P τ` using `by ring`.

Rewrite using `[this, hkill σ τ hτ, mul_zero, zero_mul]`. Use `⟨fun σ => f σ * P σ, ⟨⟨fun σ => (hfi σ).mul (hP σ), ?_⟩, ?_⟩, fun σ => (J σ).mul_mem_right _ (hfJ σ)⟩` and prove the remaining obligations. Introduce `σ τ hne`. Break down `lt_or_gt_of_ne hne with hl | hl` into its components or cases. Use `show (f σ * P σ) * (f τ * P τ) = 0`.

Rewrite using `[mul_comm]`. Conclude with `hlt τ σ hl`. Conclude with `hlt σ τ hl`. Use `Finset.prod_one_sub_ordered (Finset.univ : Finset Λ) f` as an intermediate fact. Rewrite `this` using `[hf0]`.

Conclude with `(sub_eq_zero.1 this.symm).symm`.
-/
theorem UpperTheory.Gal.crystallineComparison.idemCover_of :
    IdemCover := by
  intro B _ Λ _ J h
  classical
  obtain ⟨f, hfi, hfJ, hf0⟩ := cover_step Λ J h
  letI : LinearOrder Λ := LinearOrder.lift' (Fintype.equivFin Λ) (Equiv.injective _)
  let P : Λ → B := fun σ => ∏ τ ∈ Finset.univ.filter (· < σ), (1 - f τ)
  have hP : ∀ σ, IsIdempotentElem (P σ) := by
    intro σ
    show P σ * P σ = P σ
    simp only [P]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun τ _ => (hfi τ).one_sub
  have hkill : ∀ σ τ, τ < σ → P σ * f τ = 0 := by
    intro σ τ hτ
    obtain ⟨c, hc⟩ : (1 - f τ) ∣ P σ :=
      Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ τ, hτ⟩)
    have h0 : (1 - f τ) * f τ = 0 := by
      have : f τ * f τ = f τ := hfi τ
      rw [sub_mul, one_mul, this, sub_self]
    rw [hc, mul_comm (1 - f τ) c, mul_assoc, h0, mul_zero]
  have hlt : ∀ σ τ, τ < σ → (f σ * P σ) * (f τ * P τ) = 0 := by
    intro σ τ hτ
    have : (f σ * P σ) * (f τ * P τ) = f σ * (P σ * f τ) * P τ := by ring
    rw [this, hkill σ τ hτ, mul_zero, zero_mul]
  refine ⟨fun σ => f σ * P σ, ⟨⟨fun σ => (hfi σ).mul (hP σ), ?_⟩, ?_⟩, fun σ => (J σ).mul_mem_right _ (hfJ σ)⟩
  · intro σ τ hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · show (f σ * P σ) * (f τ * P τ) = 0
      rw [mul_comm]
      exact hlt τ σ hl
    · exact hlt σ τ hl
  · have := Finset.prod_one_sub_ordered (Finset.univ : Finset Λ) f
    rw [hf0] at this
    exact (sub_eq_zero.1 this.symm).symm
