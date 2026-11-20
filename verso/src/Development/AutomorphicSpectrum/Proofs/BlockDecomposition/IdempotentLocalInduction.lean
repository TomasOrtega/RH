import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.Idem

/- English proof (translation)
Introduce `S _ Q h0 hmul hadd hloc`. Set `I : Ideal S` to `{ carrier := {x | ∃ e : S, IsIdempotentElem e ∧ Q e ∧ e * x = x} zero_mem' := ⟨0, IsIdempotentElem.zero, h0, by simp⟩ add_mem' := by`. Introduce and unpack `x y ⟨e, he, hQe, hex⟩ ⟨e', he', hQe', hey⟩`. Establish `hee : e * e = e` using `he`. Establish `hee' : e' * e' = e'` using `he'`.

Establish `h1e : IsIdempotentElem (1 - e)` using `he.one_sub`. Establish `hg : IsIdempotentElem (e' * (1 - e))` using `IsIdempotentElem.mul he' h1e`. Establish `horth : e * (e' * (1 - e)) = 0`. Establish `: e * (e' * (1 - e)) = e' * (e - e * e)` using `by ring`. Rewrite using `[this, hee]`.

Simplify using the standard rewrite rules. Use `⟨e + e' * (1 - e), ?_, hadd e _ he hg horth hQe (hmul e' _ he' h1e hQe'), ?_⟩` and prove the remaining obligations. Use `show (e + e' * (1 - e)) * (e + e' * (1 - e)) = e + e' * (1 - e)`. Establish `hg' : (e' * (1 - e)) * (e' * (1 - e)) = e' * (1 - e)` using `hg`. Establish `: (e + e' * (1 - e)) * (e + e' * (1 - e)) = e * e + 2 * (e * (e' * (1 - e))) + (e' * (1 - e)) * (e' * (1 - e))` using `by ring`.

Rewrite using `[this, hee, horth, hg']`. Simplify using the standard rewrite rules. Establish `h1 : (e + e' * (1 - e)) * x = x`. Establish `: (e + e' * (1 - e)) * x = e * x + e' * (x - e * x)` using `by ring`. Rewrite using `[this, hex]`.

Simplify using the standard rewrite rules. Establish `h2 : (e + e' * (1 - e)) * y = y`. Establish `: (e + e' * (1 - e)) * y = e * y + (e' * y) - e * (e' * y)` using `by ring`. Rewrite using `[this, hey]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[mul_add, h1, h2]`. Use the proof step `smul_mem' := by`. Introduce and unpack `c x ⟨e, he, hQe, hex⟩`. Use `⟨e, he, hQe, ?_⟩` and prove the remaining obligations. Use `show e * (c * x) = c * x`.

Combine the equalities or inequalities in the displayed calculation. Establish `htop : I = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨m, hm, hIm⟩` from `Ideal.exists_le_maximal I hne`. Take `⟨e, he, hem, hQ⟩` from `hloc m hm`.

Conclude with `hem (hIm ⟨e, he, hQ, by rw [show e * e = e from he]⟩)`. Establish `h1 : (1 : S) ∈ I` using `by rw [htop]; exact Submodule.mem_top`. Take `⟨e, _, hQ, he1⟩` from `h1`. Establish `: e = 1` using `by simpa using he1`. Conclude with `this ▸ hQ`.
-/
theorem glue_idempotent_property :
    ∀ {S : Type} [CommRing S] (Q : S → Prop), Q 0 →
      (∀ e e' : S, IsIdempotentElem e → IsIdempotentElem e' → Q e → Q (e * e')) →
      (∀ e e' : S, IsIdempotentElem e → IsIdempotentElem e' → e * e' = 0 → Q e → Q e' →
        Q (e + e')) →
      (∀ m : Ideal S, m.IsMaximal → ∃ e, IsIdempotentElem e ∧ e ∉ m ∧ Q e) → Q 1 := by
  intro S _ Q h0 hmul hadd hloc
  let I : Ideal S :=
    { carrier := {x | ∃ e : S, IsIdempotentElem e ∧ Q e ∧ e * x = x}
      zero_mem' := ⟨0, IsIdempotentElem.zero, h0, by simp⟩
      add_mem' := by
        rintro x y ⟨e, he, hQe, hex⟩ ⟨e', he', hQe', hey⟩
        have hee : e * e = e := he
        have hee' : e' * e' = e' := he'
        have h1e : IsIdempotentElem (1 - e) := he.one_sub
        have hg : IsIdempotentElem (e' * (1 - e)) :=
          IsIdempotentElem.mul he' h1e
        have horth : e * (e' * (1 - e)) = 0 := by
          have : e * (e' * (1 - e)) = e' * (e - e * e) := by ring
          rw [this, hee]; simp
        refine ⟨e + e' * (1 - e), ?_, hadd e _ he hg horth hQe (hmul e' _ he' h1e hQe'), ?_⟩
        · show (e + e' * (1 - e)) * (e + e' * (1 - e)) = e + e' * (1 - e)
          have hg' : (e' * (1 - e)) * (e' * (1 - e)) = e' * (1 - e) := hg
          have : (e + e' * (1 - e)) * (e + e' * (1 - e))
              = e * e + 2 * (e * (e' * (1 - e))) + (e' * (1 - e)) * (e' * (1 - e)) := by ring
          rw [this, hee, horth, hg']; simp
        · have h1 : (e + e' * (1 - e)) * x = x := by
            have : (e + e' * (1 - e)) * x = e * x + e' * (x - e * x) := by ring
            rw [this, hex]; simp
          have h2 : (e + e' * (1 - e)) * y = y := by
            have : (e + e' * (1 - e)) * y = e * y + (e' * y) - e * (e' * y) := by ring
            rw [this, hey]; ring
          rw [mul_add, h1, h2]
      smul_mem' := by
        rintro c x ⟨e, he, hQe, hex⟩
        refine ⟨e, he, hQe, ?_⟩
        show e * (c * x) = c * x
        calc e * (c * x) = c * (e * x) := by ring
          _ = c * x := by rw [hex]  }
  have htop : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨e, he, hem, hQ⟩ := hloc m hm
    exact hem (hIm ⟨e, he, hQ, by rw [show e * e = e from he]⟩)
  have h1 : (1 : S) ∈ I := by rw [htop]; exact Submodule.mem_top
  obtain ⟨e, _, hQ, he1⟩ := h1
  have : e = 1 := by simpa using he1
  exact this ▸ hQ

end GlobalTheory.CompanionTheory.Idem
