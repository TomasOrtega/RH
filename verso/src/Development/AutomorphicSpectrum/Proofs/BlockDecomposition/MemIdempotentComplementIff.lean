import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.CompIdeal

/- English proof (translation)
Introduce `S _ P hP x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Unfold `compI Ideal.span at hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem a ha`. Take `⟨hi, haP⟩` from `ha`. Use `⟨1 - a, hi.one_sub, fun h => hP.ne_top ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Ideal.eq_top_iff_one P).2 (by simpa using P.add_mem h haP)`. Rewrite using `[sub_mul, one_mul, hi.eq, sub_self]`.

Consider the case `zero => exact ⟨1, IsIdempotentElem.one, fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h), mul_zero 1⟩`. Consider the case `add a b _ _ iha ihb`. Take `⟨e, he, heP, hea⟩` from `iha`. Take `⟨f, hf, hfP, hfb⟩` from `ihb`. Use `⟨e * f, he.mul hf, fun h => (hP.mem_or_mem h).elim heP hfP, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Consider the case `smul s a _ ih`. Take `⟨e, he, heP, hea⟩` from `ih`. Use `⟨e, he, heP, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Introduce and unpack `⟨e, he, heP, hex⟩`. Establish `h0 : e * (1 - e) ∈ P`. Rewrite using `[mul_sub, mul_one, he.eq, sub_self]`. Conclude with `P.zero_mem`. Establish `h1 : 1 - e ∈ P` using `(hP.mem_or_mem h0).resolve_left heP`.

Establish `h2 : x = x * (1 - e)`. Rewrite using `[mul_sub, mul_one, mul_comm x e, hex, sub_zero]`. Rewrite using `[h2]`. Conclude with `Ideal.mul_mem_left _ x (Ideal.subset_span ⟨he.one_sub, h1⟩)`.
-/
theorem mem_compI_iff : ∀ {S : Type} [CommRing S] (P : Ideal S), P.IsPrime → ∀ x : S,
    x ∈ compI P ↔ ∃ e, IsIdempotentElem e ∧ e ∉ P ∧ e * x = 0 := by
  intro S _ P hP x
  constructor
  · intro hx
    unfold compI Ideal.span at hx
    induction hx using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨hi, haP⟩ := ha
      refine ⟨1 - a, hi.one_sub, fun h => hP.ne_top ?_, ?_⟩
      · exact (Ideal.eq_top_iff_one P).2 (by simpa using P.add_mem h haP)
      · rw [sub_mul, one_mul, hi.eq, sub_self]
    | zero => exact ⟨1, IsIdempotentElem.one, fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h), mul_zero 1⟩
    | add a b _ _ iha ihb =>
      obtain ⟨e, he, heP, hea⟩ := iha
      obtain ⟨f, hf, hfP, hfb⟩ := ihb
      refine ⟨e * f, he.mul hf, fun h => (hP.mem_or_mem h).elim heP hfP, ?_⟩
      calc e * f * (a + b) = f * (e * a) + e * (f * b) := by ring
        _ = 0 := by rw [hea, hfb, mul_zero, mul_zero, add_zero]
    | smul s a _ ih =>
      obtain ⟨e, he, heP, hea⟩ := ih
      refine ⟨e, he, heP, ?_⟩
      calc e * s • a = s * (e * a) := by rw [smul_eq_mul]; ring
        _ = 0 := by rw [hea, mul_zero]
  · rintro ⟨e, he, heP, hex⟩
    have h0 : e * (1 - e) ∈ P := by
      rw [mul_sub, mul_one, he.eq, sub_self]
      exact P.zero_mem
    have h1 : 1 - e ∈ P := (hP.mem_or_mem h0).resolve_left heP
    have h2 : x = x * (1 - e) := by
      rw [mul_sub, mul_one, mul_comm x e, hex, sub_zero]
    rw [h2]
    exact Ideal.mul_mem_left _ x (Ideal.subset_span ⟨he.one_sub, h1⟩)

end GlobalTheory.CompanionTheory.CompIdeal
