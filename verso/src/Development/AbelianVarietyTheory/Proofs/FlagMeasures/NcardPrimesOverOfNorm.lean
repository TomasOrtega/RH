import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelPrimeSplitsCompletelyInCmField

namespace GlobalTheory.RankSplit

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

/- English proof (translation)
The claim follows from `PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible`.
-/
private lemma span_prime_isMaximal' {p : ℕ} (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
/- English proof (translation)
Use `⟨(span_prime_isMaximal' hp).eq_of_le (Ideal.IsPrime.comap (algebraMap ℤ A)).ne_top ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]`. Simplify using `using h`.
-/
private lemma liesOver_span_of_prime_natCast_mem {A : Type*} [CommRing A] {p : ℕ} (hp : p.Prime) (P : Ideal A) [hP : P.IsPrime]
    (h : (p : A) ∈ P) : P.LiesOver (Ideal.span {(p : ℤ)}) := by
  refine ⟨(span_prime_isMaximal' hp).eq_of_le (Ideal.IsPrime.comap (algebraMap ℤ A)).ne_top ?_⟩
  rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
  simpa using h

/- English proof (translation)
Establish `hp0 : Ideal.span {(p : ℤ)} ≠ ⊥`. Simplify using `[Ideal.span_singleton_eq_bot, hp.ne_zero]`. Use `haveI := span_prime_isMaximal' hp`. Rewrite using `[← Ideal.sum_ramification_inertia (R := ℤ) (S := 𝓞 E) ℚ E hp0, ← IsDedekindDomain.coe_primesOverFinset hp0 (𝓞 E), Set.ncard_coe_finset, Finset.card_eq_sum_ones]`. Use `Finset.sum_congr rfl fun P hP => ?_` and prove the remaining obligations.

Rewrite `hP` using `[IsDedekindDomain.mem_primesOverFinset_iff hp0]`. Take `⟨hPp, hPl⟩` from `hP`. Establish `hPne : P ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P`. Use `haveI hPm : P.IsMaximal := hPp.isMaximal hPne`. Establish `hpP : (p : 𝓞 E) ∈ P`.

Use `(Ideal.mem_of_liesOver P (Ideal.span {(p : ℤ)}) (p : ℤ)).mp (Ideal.mem_span_singleton_self _)` as an intermediate fact. Simplify using `using this`. Take `⟨hn, hsq⟩` from `h P hPm hpP`. Establish `hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)}`. Rewrite using `[Ideal.map_span, Set.image_singleton]`.

Simplify using the standard rewrite rules. Establish `he : Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) P = 1`. Apply `Ideal.ramificationIdx'_spec` to reduce the goal to its premises. Rewrite using `[hmap, pow_one, Ideal.span_singleton_le_iff_mem]`. Conclude with `hpP`.

Rewrite using `[hmap, Ideal.span_singleton_le_iff_mem]`. Conclude with `hsq`. Establish `hf : Ideal.inertiaDeg' (Ideal.span {(p : ℤ)}) P = 1`. Rewrite using `[Ideal.inertiaDeg'_eq_inertiaDeg]`. Establish `h1` using `Ideal.pow_inertiaDeg p P`.

Rewrite `h1` using `[hn]`. Conclude with `(Nat.pow_eq_self_iff hp.one_lt).mp h1`. Rewrite using `[he, hf]`.
-/
theorem ncard_primesOver_of_norm {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : ∀ P : Ideal (𝓞 E), P.IsMaximal → ((p : 𝓞 E) ∈ P) → Ideal.absNorm P = p ∧ (p : 𝓞 E) ∉ P ^ 2) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
  classical
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simp [Ideal.span_singleton_eq_bot, hp.ne_zero]
  haveI := span_prime_isMaximal' hp
  rw [← Ideal.sum_ramification_inertia (R := ℤ) (S := 𝓞 E) ℚ E hp0,
    ← IsDedekindDomain.coe_primesOverFinset hp0 (𝓞 E), Set.ncard_coe_finset, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [IsDedekindDomain.mem_primesOverFinset_iff hp0] at hP
  obtain ⟨hPp, hPl⟩ := hP
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
  haveI hPm : P.IsMaximal := hPp.isMaximal hPne
  have hpP : (p : 𝓞 E) ∈ P := by
    have := (Ideal.mem_of_liesOver P (Ideal.span {(p : ℤ)}) (p : ℤ)).mp (Ideal.mem_span_singleton_self _)
    simpa using this
  obtain ⟨hn, hsq⟩ := h P hPm hpP
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  have he : Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) P = 1 := by
    apply Ideal.ramificationIdx'_spec
    · rw [hmap, pow_one, Ideal.span_singleton_le_iff_mem]
      exact hpP
    · rw [hmap, Ideal.span_singleton_le_iff_mem]
      exact hsq
  have hf : Ideal.inertiaDeg' (Ideal.span {(p : ℤ)}) P = 1 := by
    rw [Ideal.inertiaDeg'_eq_inertiaDeg]
    have h1 := Ideal.pow_inertiaDeg p P
    rw [hn] at h1
    exact (Nat.pow_eq_self_iff hp.one_lt).mp h1
  rw [he, hf]

/- English proof (translation)
Introduce `D p hp h`. Establish `hE` using `ncard_primesOver_of_norm hp h`. Establish `hF` using `GlobalTheory.ColClassCompare.ncard_primesOver_of_split (F := D.host.F) hp hE`. Rewrite `hF` using `[GlobalTheory.ColClassCompare.finrank_F]`. Use `⟨?_, fun v hv => (GlobalTheory.ColClassCompare.unram_card_of_split (F := D.host.F) hp hE v.asIdeal hv).2⟩` and prove the remaining obligations.

Rewrite using `[← hF, ← Nat.card_coe_set_eq]`. Use `Nat.card_congr { toFun := fun v => ⟨v.1.asIdeal, v.1.isPrime, liesOver_span_of_prime_natCast_mem hp v.1.asIdeal v.2⟩ invFun := fun P => ⟨⟨P.1, P.2.1, ?_⟩, ?_⟩ left_inv := fun v => rfl right_inv := fun P => rfl }` and prove the remaining obligations. Use `P.2.2` as an intermediate fact. Establish `h0 : Ideal.span {(p : ℤ)} ≠ ⊥` using `by simp [Ideal.span_singleton_eq_bot, hp.ne_zero]`. Conclude with `Ideal.ne_bot_of_liesOver_of_ne_bot h0 P.1`.

Use `P.2.2` as an intermediate fact. Establish `h2` using `(Ideal.mem_of_liesOver P.1 (Ideal.span {(p : ℤ)}) (p : ℤ)).mp (Ideal.mem_span_singleton_self _)`. Simplify using `using h2`.
-/
theorem splitsF_of_norm : ∀ (D : D7) (p : ℕ), p.Prime →
    (∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → ((p : 𝓞 D.host.E) ∈ P) →
      Ideal.absNorm P = p ∧ (p : 𝓞 D.host.E) ∉ P ^ 2) → StandardLattice.SplitsF D p := by
  intro D p hp h
  have hE := ncard_primesOver_of_norm hp h
  have hF := GlobalTheory.ColClassCompare.ncard_primesOver_of_split (F := D.host.F) hp hE
  rw [GlobalTheory.ColClassCompare.finrank_F] at hF
  refine ⟨?_, fun v hv => (GlobalTheory.ColClassCompare.unram_card_of_split (F := D.host.F) hp hE v.asIdeal hv).2⟩
  rw [← hF, ← Nat.card_coe_set_eq]
  refine Nat.card_congr
    { toFun := fun v => ⟨v.1.asIdeal, v.1.isPrime, liesOver_span_of_prime_natCast_mem hp v.1.asIdeal v.2⟩
      invFun := fun P => ⟨⟨P.1, P.2.1, ?_⟩, ?_⟩
      left_inv := fun v => rfl
      right_inv := fun P => rfl }
  · have := P.2.2
    have h0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by simp [Ideal.span_singleton_eq_bot, hp.ne_zero]
    exact Ideal.ne_bot_of_liesOver_of_ne_bot h0 P.1
  · have := P.2.2
    have h2 := (Ideal.mem_of_liesOver P.1 (Ideal.span {(p : ℤ)}) (p : ℤ)).mp (Ideal.mem_span_singleton_self _)
    simpa using h2

end GlobalTheory.RankSplit
