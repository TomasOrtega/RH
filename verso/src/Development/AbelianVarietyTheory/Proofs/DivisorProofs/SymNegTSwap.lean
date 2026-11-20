import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

/- English proof (translation)
Introduce `a b c d`. Establish `h1` using `h d c b a`. Simplify using `only [negT, neg_mul_neg]`. Establish `e1 : F b a * F d c - F d c * F b a = -(F d c * F b a - F b a * F d c)` using `by abel`. Rewrite using `[e1, h1]`.

Simplify using `only [@eq_comm _ c b, @eq_comm _ a d]`. Apply the tactic sequence `split_ifs <;> abel`.
-/
theorem isGl_negT {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (F : ι → ι → Module.End ℂ M) (h : IsGl F) : IsGl (negT F) := by
  intro a b c d
  have h1 := h d c b a
  simp only [negT, neg_mul_neg]
  have e1 : F b a * F d c - F d c * F b a = -(F d c * F b a - F b a * F d c) := by abel
  rw [e1, h1]
  simp only [@eq_comm _ c b, @eq_comm _ a d]
  split_ifs <;> abel

/- English proof (translation)
Take `⟨hfd, hst, ip, hsym, hpos, hadj⟩` from `h`. Use `⟨hfd, fun a b hab u hu => ?_, ip, hsym, hpos, fun a b hab x hx y hy => ?_⟩` and prove the remaining obligations. Simplify using `only [negT, LinearMap.neg_apply]`. Conclude with `U.neg_mem (hst b a hab.symm u hu)`. Simplify using `only [negT, LinearMap.neg_apply, map_neg, LinearMap.neg_apply]`.

Rewrite using `[hadj b a hab.symm x hx y hy]`.
-/
theorem unitOn_negT {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M) (h : UnitOn s F U) :
    UnitOn s (negT F) U := by
  obtain ⟨hfd, hst, ip, hsym, hpos, hadj⟩ := h
  refine ⟨hfd, fun a b hab u hu => ?_, ip, hsym, hpos, fun a b hab x hx y hy => ?_⟩
  · simp only [negT, LinearMap.neg_apply]
    exact U.neg_mem (hst b a hab.symm u hu)
  · simp only [negT, LinearMap.neg_apply, map_neg, LinearMap.neg_apply]
    rw [hadj b a hab.symm x hx y hy]

/- English proof (translation)
Take `⟨hfd, hst, ip, hsym, hpos, hadj⟩` from `h`. Use `⟨hfd, fun a b hab u hu => hst a b (by simpa using hab) u hu, ip, hsym, hpos, fun a b hab x hx y hy => hadj a b (by simpa using hab) x hx y hy⟩` and prove the remaining obligations.
-/
theorem unitOn_not {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M) (h : UnitOn s F U) :
    UnitOn (fun a => !s a) F U := by
  obtain ⟨hfd, hst, ip, hsym, hpos, hadj⟩ := h
  refine ⟨hfd, fun a b hab u hu => hst a b (by simpa using hab) u hu, ip, hsym, hpos,
    fun a b hab x hx y hy => hadj a b (by simpa using hab) x hx y hy⟩

/- English proof (translation)
Introduce `ι M _ _ _ _ s F`. Use `⟨isGl_negT F, ?_, ?_, fun U hU => ⟨unitOn_negT s F U hU, unitOn_not s F U hU⟩, fun h => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Unfold `cas negT`. Simplify using `only [neg_mul_neg]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [eq_comm]`. Unfold `cas`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [Bool.not_inj_iff]`.

Introduce `t`. Take `⟨U, hU, hUn⟩` from `h t`. Conclude with `⟨U, hU, unitOn_negT s F U hUn⟩`. Introduce `t`. Take `⟨U, hU, hUn⟩` from `h t`.

Conclude with `⟨U, hU, unitOn_not s F U hUn⟩`.
-/
theorem sym_negT_swap : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), (IsGl F → IsGl (negT F)) ∧ cas s (negT F) = cas s F ∧ cas (fun a => !s a) F = cas s F ∧ (∀ U, UnitOn s F U → UnitOn s (negT F) U ∧ UnitOn (fun a => !s a) F U) ∧ (LocU s F → LocU s (negT F) ∧ LocU (fun a => !s a) F) := by
  intro ι M _ _ _ _ s F
  refine ⟨isGl_negT F, ?_, ?_, fun U hU => ⟨unitOn_negT s F U hU, unitOn_not s F U hU⟩, fun h => ⟨?_, ?_⟩⟩
  · unfold cas negT
    simp only [neg_mul_neg]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [eq_comm]
  · unfold cas
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [Bool.not_inj_iff]
  · intro t
    obtain ⟨U, hU, hUn⟩ := h t
    exact ⟨U, hU, unitOn_negT s F U hUn⟩
  · intro t
    obtain ⟨U, hU, hUn⟩ := h t
    exact ⟨U, hU, unitOn_not s F U hUn⟩

end GlobalTheory.HoweR
