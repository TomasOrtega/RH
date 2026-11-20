import Mathlib
import GroundTheory.Brauer.CrossedProduct
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Brauer

namespace CrossedProduct

open groupCohomology

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} {hf : IsMulCocycle₂ f}

/- English proof (translation)
Rewrite using `[coeff_sub, Finsupp.sub_apply, coeff_incl_mul, coeff_mul_incl]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeff_incl_mul_sub_mul_incl (σ₀ : L ≃ₐ[K] L) (b : L) (x : CrossedProduct hf)
    (σ : L ≃ₐ[K] L) :
    (incl (σ₀ b) * x - x * incl b).coeff σ = (σ₀ b - σ b) * x.coeff σ := by
  rw [coeff_sub, Finsupp.sub_apply, coeff_incl_mul, coeff_mul_incl]
  ring

/- English proof (translation)
Rewrite using `[incl_mul_u]`. Use `ext1`. Use extensionality with `σ`. Distinguish the cases in `hσ : σ = σ₀`. Substitute `hσ` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[h σ hσ, coeff_single, Finsupp.single_apply, if_neg (Ne.symm hσ)]`.
-/
theorem eq_incl_mul_u_of_coeff_eq_zero (x : CrossedProduct hf) (σ₀ : L ≃ₐ[K] L)
    (h : ∀ σ, σ ≠ σ₀ → x.coeff σ = 0) : x = incl (x.coeff σ₀) * u σ₀ := by
  classical
  rw [incl_mul_u]
  ext1
  ext σ
  by_cases hσ : σ = σ₀
  · subst hσ
    simp
  · rw [h σ hσ, coeff_single, Finsupp.single_apply, if_neg (Ne.symm hσ)]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨x₁, hx₁, hx₁0⟩ : ∃ x ∈ I, x ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Apply `hI` to reduce the goal to its premises. Use extensionality with `x`.

Rewrite using `[TwoSidedIdeal.mem_bot]`. Conclude with `⟨h x, fun hx => hx ▸ I.zero_mem⟩`. Establish `hex : ∃ n, ∃ x ∈ I, x ≠ 0 ∧ x.coeff.support.card = n` using `⟨_, x₁, hx₁, hx₁0, rfl⟩`. Take `⟨x, hxI, hx0, hcard⟩` from `Nat.find_spec hex`. Establish `hmin : ∀ y ∈ I, y ≠ 0 → x.coeff.support.card ≤ y.coeff.support.card` using `fun y hy hy0 => hcard ▸ Nat.find_min' hex ⟨y, hy, hy0, rfl⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨σ₀, hσ₀⟩ : x.coeff.support.Nonempty := by`. Rewrite using `[Finsupp.support_nonempty_iff]`. Conclude with `fun h => hx0 (coeff_injective h)`. Establish `hzero : ∀ σ, σ ≠ σ₀ → x.coeff σ = 0`. Introduce `σ hσ`.

Assume the negation of the conclusion as `hxσ`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b, σ₀ b ≠ σ b := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hσ (AlgEquiv.ext fun b => (h b).symm)`.

Establish `hyI : incl (σ₀ b) * x - x * incl b ∈ I` using `I.sub_mem (I.mul_mem_left _ _ hxI) (I.mul_mem_right _ _ hxI)`. Establish `hyσ : (incl (σ₀ b) * x - x * incl b).coeff σ ≠ 0`. Rewrite using `[coeff_incl_mul_sub_mul_incl]`. Conclude with `mul_ne_zero (sub_ne_zero.2 hb) hxσ`. Establish `hy0 : incl (σ₀ b) * x - x * incl b ≠ 0` using `fun h => hyσ (by rw [h]; rfl)`.

Establish `hsub : (incl (σ₀ b) * x - x * incl b).coeff.support ⊆ x.coeff.support.erase σ₀`. Introduce `τ hτ`. Rewrite `hτ` using `[Finsupp.mem_support_iff, coeff_incl_mul_sub_mul_incl]`. Rewrite using `[Finset.mem_erase, Finsupp.mem_support_iff]`. Use `⟨?_, right_ne_zero_of_mul hτ⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Simplify using `at hτ`. Establish `h1` using `Finset.card_le_card hsub`. Rewrite `h1` using `[Finset.card_erase_of_mem hσ₀]`. Establish `h2` using `hmin _ hyI hy0`.

Establish `h3 : 0 < x.coeff.support.card` using `Finset.card_pos.2 ⟨σ₀, hσ₀⟩`. Use linear arithmetic over natural numbers and integers. Establish `hunit : IsUnit x`. Rewrite using `[eq_incl_mul_u_of_coeff_eq_zero x σ₀ hzero]`. Conclude with `((isUnit_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hσ₀)).map incl).mul (isUnit_u σ₀)`.

Take `⟨v, hv⟩` from `hunit`. Establish `h1 : ((v⁻¹ : (CrossedProduct hf)ˣ) : CrossedProduct hf) * x ∈ I` using `I.mul_mem_left _ _ hxI`. Rewrite `h1` using `[← hv, Units.inv_mul]`. Conclude with `(TwoSidedIdeal.one_mem_iff I).1 h1`.
-/
theorem eq_top_of_ne_bot (I : TwoSidedIdeal (CrossedProduct hf)) (hI : I ≠ ⊥) : I = ⊤ := by
  classical
  obtain ⟨x₁, hx₁, hx₁0⟩ : ∃ x ∈ I, x ≠ 0 := by
    by_contra h
    push Not at h
    apply hI
    ext x
    rw [TwoSidedIdeal.mem_bot]
    exact ⟨h x, fun hx => hx ▸ I.zero_mem⟩
  have hex : ∃ n, ∃ x ∈ I, x ≠ 0 ∧ x.coeff.support.card = n := ⟨_, x₁, hx₁, hx₁0, rfl⟩
  obtain ⟨x, hxI, hx0, hcard⟩ := Nat.find_spec hex
  have hmin : ∀ y ∈ I, y ≠ 0 → x.coeff.support.card ≤ y.coeff.support.card :=
    fun y hy hy0 => hcard ▸ Nat.find_min' hex ⟨y, hy, hy0, rfl⟩
  obtain ⟨σ₀, hσ₀⟩ : x.coeff.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    exact fun h => hx0 (coeff_injective h)
  have hzero : ∀ σ, σ ≠ σ₀ → x.coeff σ = 0 := by
    intro σ hσ
    by_contra hxσ
    obtain ⟨b, hb⟩ : ∃ b, σ₀ b ≠ σ b := by
      by_contra h
      push Not at h
      exact hσ (AlgEquiv.ext fun b => (h b).symm)
    have hyI : incl (σ₀ b) * x - x * incl b ∈ I :=
      I.sub_mem (I.mul_mem_left _ _ hxI) (I.mul_mem_right _ _ hxI)
    have hyσ : (incl (σ₀ b) * x - x * incl b).coeff σ ≠ 0 := by
      rw [coeff_incl_mul_sub_mul_incl]
      exact mul_ne_zero (sub_ne_zero.2 hb) hxσ
    have hy0 : incl (σ₀ b) * x - x * incl b ≠ 0 := fun h => hyσ (by rw [h]; rfl)
    have hsub : (incl (σ₀ b) * x - x * incl b).coeff.support ⊆ x.coeff.support.erase σ₀ := by
      intro τ hτ
      rw [Finsupp.mem_support_iff, coeff_incl_mul_sub_mul_incl] at hτ
      rw [Finset.mem_erase, Finsupp.mem_support_iff]
      refine ⟨?_, right_ne_zero_of_mul hτ⟩
      rintro rfl
      simp at hτ
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hσ₀] at h1
    have h2 := hmin _ hyI hy0
    have h3 : 0 < x.coeff.support.card := Finset.card_pos.2 ⟨σ₀, hσ₀⟩
    omega
  have hunit : IsUnit x := by
    rw [eq_incl_mul_u_of_coeff_eq_zero x σ₀ hzero]
    exact ((isUnit_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hσ₀)).map incl).mul (isUnit_u σ₀)
  obtain ⟨v, hv⟩ := hunit
  have h1 : ((v⁻¹ : (CrossedProduct hf)ˣ) : CrossedProduct hf) * x ∈ I := I.mul_mem_left _ _ hxI
  rw [← hv, Units.inv_mul] at h1
  exact (TwoSidedIdeal.one_mem_iff I).1 h1

instance : IsSimpleRing (CrossedProduct hf) :=
  IsSimpleRing.of_eq_bot_or_eq_top fun I => or_iff_not_imp_left.2 (eq_top_of_ne_bot I)

/- English proof (translation)
Establish `hzero : ∀ σ, σ ≠ 1 → x.coeff σ = 0`. Introduce `σ hσ`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b, b ≠ σ b := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Conclude with `hσ (AlgEquiv.ext fun b => (h b).symm)`. Establish `h : (incl b * x - x * incl b).coeff σ = 0`. Rewrite using `[sub_eq_zero.2 (hx b)]`. Both sides reduce to the same expression. Establish `h'` using `coeff_incl_mul_sub_mul_incl 1 b x σ`.

Rewrite `h'` using `[AlgEquiv.one_apply]`. Rewrite `h` using `[h']`. Conclude with `(mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hb)`. Use `(AlgHom.mem_range _).2 ⟨x.coeff 1 * f (1, 1), ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [eq_incl_mul_u_of_coeff_eq_zero x 1 hzero]`.

Rewrite using `[u_one, ← map_mul]`.
-/
theorem mem_range_incl_of_commute (x : CrossedProduct hf) (hx : ∀ b : L, incl b * x = x * incl b) :
    x ∈ (incl : L →ₐ[K] CrossedProduct hf).range := by
  have hzero : ∀ σ, σ ≠ 1 → x.coeff σ = 0 := by
    intro σ hσ
    obtain ⟨b, hb⟩ : ∃ b, b ≠ σ b := by
      by_contra h
      push Not at h
      exact hσ (AlgEquiv.ext fun b => (h b).symm)
    have h : (incl b * x - x * incl b).coeff σ = 0 := by
      rw [sub_eq_zero.2 (hx b)]
      rfl
    have h' := coeff_incl_mul_sub_mul_incl 1 b x σ
    rw [AlgEquiv.one_apply] at h'
    rw [h'] at h
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hb)
  refine (AlgHom.mem_range _).2 ⟨x.coeff 1 * f (1, 1), ?_⟩
  conv_rhs => rw [eq_incl_mul_u_of_coeff_eq_zero x 1 hzero]
  rw [u_one, ← map_mul]

instance [FiniteDimensional K L] [IsGalois K L] : Algebra.IsCentral K (CrossedProduct hf) where
  out := by
    intro x hx
    rw [Subalgebra.mem_center_iff] at hx
    obtain ⟨a, rfl⟩ := (AlgHom.mem_range _).1 (mem_range_incl_of_commute x fun b => hx _)
    have hfix : ∀ σ : L ≃ₐ[K] L, σ a = a := by
      intro σ
      have h := hx (u σ)
      rw [u_mul_incl] at h
      exact incl_injective ((isUnit_u σ).mul_left_injective h)
    obtain ⟨c, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed a).2 hfix
    exact Algebra.mem_bot.2 ⟨c, (incl.commutes c).symm⟩

end CrossedProduct

end GroundTheory.Brauer

end
