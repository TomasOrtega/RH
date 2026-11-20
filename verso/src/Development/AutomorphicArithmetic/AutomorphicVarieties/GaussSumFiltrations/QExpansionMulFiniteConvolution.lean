import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.TotallyPositiveSummandsWithDenominatorFinite
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

/- English proof (translation)
Simplify using `[reAt, map_add]`.
-/
theorem reAt_add_qm {F : Type} [Field F] [NumberField F] (v : InfinitePlace F) (x y : F) :
    reAt v (x + y) = reAt v x + reAt v y := by
  simp [reAt, map_add]

/- English proof (translation)
Simplify using `only [ez, ← Complex.exp_add, reAt_add_qm, Complex.ofReal_add, add_mul, Finset.sum_add_distrib, mul_add]`.
-/
theorem ez_add_qm {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (x y : F) (z : Hn F) :
    ez (x + y) z = ez x z * ez y z := by
  simp only [ez, ← Complex.exp_add, reAt_add_qm, Complex.ofReal_add, add_mul, Finset.sum_add_distrib, mul_add]

/- English proof (translation)
Introduce `v` and use `by rw [reAt_add_qm]; exact add_pos (hx v) (hy v)`.
-/
theorem TP_add {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {x y : F} (hx : TP x) (hy : TP y) :
    TP (x + y) := fun v => by rw [reAt_add_qm]; exact add_pos (hx v) (hy v)

/- English proof (translation)
Introduce `F _ _ _ f g a b ⟨⟨D, hD, ha⟩, hf⟩ ⟨⟨E, hE, hb⟩, hg⟩`. Establish `hfin : ∀ ξ, (Function.support fun η => a η * b (ξ - η)).Finite`. Introduce `ξ`. Use `(GlobalTheory.T.totallyPositive_summands_with_denominator_finite F D hD ξ).subset ?_` and prove the remaining obligations. Introduce `η hη`.

Establish `h1 : a η ≠ 0` using `left_ne_zero_of_mul hη`. Establish `h2 : b (ξ - η) ≠ 0` using `right_ne_zero_of_mul hη`. Conclude with `⟨(ha η h1).1, (hb _ h2).1, (ha η h1).2⟩`. Use `⟨fun ξ => ∑ η ∈ (hfin ξ).toFinset, a η * b (ξ - η), ⟨⟨D * E, Nat.mul_pos hD hE, ?_⟩, ?_⟩, fun ξ => ⟨_, rfl⟩⟩` and prove the remaining obligations. Introduce `ξ hξ`.

Take `⟨η, -, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hξ`. Establish `h1 : a η ≠ 0` using `left_ne_zero_of_mul hne`. Establish `h2 : b (ξ - η) ≠ 0` using `right_ne_zero_of_mul hne`. Take `⟨p1, i1⟩` from `ha η h1`. Take `⟨p2, i2⟩` from `hb _ h2`.

Establish `hsum : ξ = η + (ξ - η)` using `by ring`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rcases p1 with e1 | t1 <;> rcases p2 with e2 | t2`. Use `left`. Rewrite `e2` using `[e1, sub_zero]`.

Conclude with `e2`. Use `right`. Rewrite `t2` using `[e1, sub_zero]`. Conclude with `t2`. Use `right`.

Rewrite `e2` using `[sub_eq_zero]`. Rewrite using `[e2]`. Conclude with `t1`. Use `right`. Rewrite using `[hsum]`.

Conclude with `TP_add t1 t2`. Establish `hE' : IsIntegral ℤ (E : F)`. Use `isIntegral_algebraMap (R := ℤ) (A := F) (x := (E : ℤ))` as an intermediate fact. Simplify using `using this`. Establish `hD' : IsIntegral ℤ (D : F)`.

Use `isIntegral_algebraMap (R := ℤ) (A := F) (x := (D : ℤ))` as an intermediate fact. Simplify using `using this`. Establish `: ((D * E : ℕ) : F) * ξ = (E : F) * ((D : F) * η) + (D : F) * ((E : F) * (ξ - η))` using `by push_cast; ring`. Rewrite using `[this]`. Conclude with `(hE'.mul i1).add (hD'.mul i2)`.

Introduce `z`. Establish `hu` using `summable_norm_iff.mpr (hf z).summable`. Establish `hw` using `summable_norm_iff.mpr (hg z).summable`. Establish `H : HasSum (fun p : F × F => (a p.1 * ez p.1 z) * (b p.2 * ez p.2 z)) (f z * g z)`. Establish `hs` using `summable_mul_of_summable_norm hu hw`.

Establish `ht` using `tsum_mul_tsum_of_summable_norm hu hw`. Rewrite `ht` using `[(hf z).tsum_eq, (hg z).tsum_eq]`. Rewrite using `[ht]`. Conclude with `hs.hasSum`. Set `e : F × F ≃ F × F` to `{ toFun := fun p => (p.2, p.1 - p.2), invFun := fun q => (q.1 + q.2, q.1), left_inv := fun p => by simp, right_inv := fun q => by simp }`.

Establish `H2` using `(e.hasSum_iff).mpr H`. Use `H2.prod_fiberwise fun ξ => ?_` and prove the remaining obligations. Establish `hx : (fun η => ((fun p : F × F => (a p.1 * ez p.1 z) * (b p.2 * ez p.2 z)) ∘ e) (ξ, η)) = fun η => a η * b (ξ - η) * ez ξ z`. Use function extensionality and compare the values at `η`. Simplify using `only [Function.comp, e, Equiv.coe_fn_mk]`.

Establish `: ez ξ z = ez η z * ez (ξ - η) z` using `by rw [← ez_add_qm, add_sub_cancel]`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hx, Finset.sum_mul]`. Apply `hasSum_sum_of_ne_finset_zero` to reduce the goal to its premises.

Introduce `η hη`. Establish `: a η * b (ξ - η) = 0`. Assume the negation of the conclusion as `h`. Conclude with `hη ((hfin ξ).mem_toFinset.mpr h)`. Rewrite using `[this, zero_mul]`.
-/
theorem hasQ_mul : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (f g : Hn F → ℂ) (a b : F → ℂ),
    HasQ f a → HasQ g b → ∃ c, HasQ (f * g) c ∧ ∀ ξ, ∃ s : Finset F, c ξ = ∑ η ∈ s, a η * b (ξ - η) := by
  intro F _ _ _ f g a b ⟨⟨D, hD, ha⟩, hf⟩ ⟨⟨E, hE, hb⟩, hg⟩
  have hfin : ∀ ξ, (Function.support fun η => a η * b (ξ - η)).Finite := by
    intro ξ
    refine (GlobalTheory.T.totallyPositive_summands_with_denominator_finite F D hD ξ).subset ?_
    intro η hη
    have h1 : a η ≠ 0 := left_ne_zero_of_mul hη
    have h2 : b (ξ - η) ≠ 0 := right_ne_zero_of_mul hη
    exact ⟨(ha η h1).1, (hb _ h2).1, (ha η h1).2⟩
  refine ⟨fun ξ => ∑ η ∈ (hfin ξ).toFinset, a η * b (ξ - η), ⟨⟨D * E, Nat.mul_pos hD hE, ?_⟩, ?_⟩,
    fun ξ => ⟨_, rfl⟩⟩
  · intro ξ hξ
    obtain ⟨η, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hξ
    have h1 : a η ≠ 0 := left_ne_zero_of_mul hne
    have h2 : b (ξ - η) ≠ 0 := right_ne_zero_of_mul hne
    obtain ⟨p1, i1⟩ := ha η h1
    obtain ⟨p2, i2⟩ := hb _ h2
    have hsum : ξ = η + (ξ - η) := by ring
    refine ⟨?_, ?_⟩
    · rcases p1 with e1 | t1 <;> rcases p2 with e2 | t2
      · left; rw [e1, sub_zero] at e2; exact e2
      · right; rw [e1, sub_zero] at t2; exact t2
      · right; rw [sub_eq_zero] at e2; rw [e2]; exact t1
      · right; rw [hsum]; exact TP_add t1 t2
    · have hE' : IsIntegral ℤ (E : F) := by
        have := isIntegral_algebraMap (R := ℤ) (A := F) (x := (E : ℤ))
        simpa using this
      have hD' : IsIntegral ℤ (D : F) := by
        have := isIntegral_algebraMap (R := ℤ) (A := F) (x := (D : ℤ))
        simpa using this
      have : ((D * E : ℕ) : F) * ξ = (E : F) * ((D : F) * η) + (D : F) * ((E : F) * (ξ - η)) := by
        push_cast; ring
      rw [this]
      exact (hE'.mul i1).add (hD'.mul i2)
  · intro z
    have hu := summable_norm_iff.mpr (hf z).summable
    have hw := summable_norm_iff.mpr (hg z).summable
    have H : HasSum (fun p : F × F => (a p.1 * ez p.1 z) * (b p.2 * ez p.2 z)) (f z * g z) := by
      have hs := summable_mul_of_summable_norm hu hw
      have ht := tsum_mul_tsum_of_summable_norm hu hw
      rw [(hf z).tsum_eq, (hg z).tsum_eq] at ht
      rw [ht]; exact hs.hasSum
    let e : F × F ≃ F × F :=
      { toFun := fun p => (p.2, p.1 - p.2), invFun := fun q => (q.1 + q.2, q.1),
        left_inv := fun p => by simp, right_inv := fun q => by simp }
    have H2 := (e.hasSum_iff).mpr H
    refine H2.prod_fiberwise fun ξ => ?_
    have hx : (fun η => ((fun p : F × F => (a p.1 * ez p.1 z) * (b p.2 * ez p.2 z)) ∘ e) (ξ, η)) =
        fun η => a η * b (ξ - η) * ez ξ z := by
      funext η
      simp only [Function.comp, e, Equiv.coe_fn_mk]
      have : ez ξ z = ez η z * ez (ξ - η) z := by rw [← ez_add_qm, add_sub_cancel]
      rw [this]; ring
    rw [hx, Finset.sum_mul]
    apply hasSum_sum_of_ne_finset_zero
    intro η hη
    have : a η * b (ξ - η) = 0 := by
      by_contra h
      exact hη ((hfin ξ).mem_toFinset.mpr h)
    rw [this, zero_mul]

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.HilbertThetaSeries.hasQ_mul | exact GlobalTheory.HilbertThetaSeries.hasQ_mul | (intros; apply GlobalTheory.HilbertThetaSeries.hasQ_mul <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.qExpansion_mul_finite_convolution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (f g : Hn F → ℂ) (a b : F → ℂ), HasQ f a → HasQ g b → ∃ c, HasQ (f * g) c ∧ ∀ ξ, ∃ s : Finset F, c ξ = ∑ η ∈ s, a η * b (ξ - η) := by
  first | exact @GlobalTheory.HilbertThetaSeries.hasQ_mul | exact GlobalTheory.HilbertThetaSeries.hasQ_mul | (intros; apply GlobalTheory.HilbertThetaSeries.hasQ_mul <;> assumption)
