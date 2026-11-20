import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.HermitianPerpSubgroup
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.ColumnDimensionRational
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MulVecMemHatSmul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible

open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped TensorProduct ENNReal Pointwise
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColCmp

namespace GlobalTheory.SplitResidue

/- English proof (translation)
Establish `hp : Prime (g : ℤ)` using `Nat.prime_iff_prime_int.mp hg`. Use `haveI : (Ideal.span {(g : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp`. Establish `hne : (Ideal.span {(g : ℤ)}) ≠ ⊥` using `by simpa using hg.ne_zero`. Use `haveI hmax : (Ideal.span {(g : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne`. Rewrite using `[← Nat.card_coe_set_eq]`.

Use `Nat.card_congr (Equiv.ofBijective (fun w => ⟨w.1.asIdeal, w.1.isPrime, ?_⟩) ⟨?_, ?_⟩)` and prove the remaining obligations. Use `haveI := w.1.isPrime`. Use `⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]`. Simplify using `using w.2`.

Introduce `a b h`. Conclude with `Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))`. Introduce and unpack `⟨P, hP, hPl⟩`. Use `⟨⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot hne P⟩, ?_⟩, rfl⟩` and prove the remaining obligations. Simplify using `using (Ideal.mem_of_liesOver P (Ideal.span {(g : ℤ)}) (g : ℤ)).1 (Ideal.mem_span_singleton_self _)`.
-/
theorem card_eq_ncard_primesOver (E : Type) [Field E] [NumberField E] {g : ℕ} (hg : g.Prime) :
    Nat.card {w : HeightOneSpectrum (𝓞 E) // (g : 𝓞 E) ∈ w.asIdeal} =
      (Ideal.primesOver (Ideal.span {(g : ℤ)}) (𝓞 E)).ncard := by
  have hp : Prime (g : ℤ) := Nat.prime_iff_prime_int.mp hg
  haveI : (Ideal.span {(g : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have hne : (Ideal.span {(g : ℤ)}) ≠ ⊥ := by simpa using hg.ne_zero
  haveI hmax : (Ideal.span {(g : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr (Equiv.ofBijective (fun w => ⟨w.1.asIdeal, w.1.isPrime, ?_⟩) ⟨?_, ?_⟩)
  · haveI := w.1.isPrime
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
    simpa using w.2
  · intro a b h
    exact Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
  · rintro ⟨P, hP, hPl⟩
    refine ⟨⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot hne P⟩, ?_⟩, rfl⟩
    simpa using (Ideal.mem_of_liesOver P (Ideal.span {(g : ℤ)}) (g : ℤ)).1
      (Ideal.mem_span_singleton_self _)

/- English proof (translation)
Introduce `E _ _ g hg h w hw`. Use `haveI := w.isPrime`. Use `haveI := Fact.mk hg`. Establish `h'` using `(card_eq_ncard_primesOver E hg).symm.trans h`. Take `⟨h1, h2⟩` from `GlobalTheory.LocSplit.split_prime hg h' w.asIdeal hw`.

Use `⟨?_, h1⟩` and prove the remaining obligations. Use `haveI : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.2 w.isPrime.ne_top`. Use `haveI : CharP (𝓞 E ⧸ w.asIdeal) g := by`. Rewrite using `[CharP.charP_iff_prime_eq_zero hg, ← map_natCast (Ideal.Quotient.mk w.asIdeal), Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hw`.

Use `⟨(RingEquiv.ofBijective (ZMod.castHom (dvd_refl g) (𝓞 E ⧸ w.asIdeal)) ⟨ZMod.castHom_injective _, fun y => ?_⟩).symm⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Take `⟨m, hm⟩` from `h2 x`. Use `⟨(m : ZMod g), ?_⟩` and prove the remaining obligations. Rewrite using `[map_intCast, ← map_intCast (Ideal.Quotient.mk w.asIdeal), eq_comm, Ideal.Quotient.eq]`.

Conclude with `hm`.
-/
theorem residue_and_unramified : ∀ (E : Type) [Field E] [NumberField E] (g : ℕ), g.Prime →
    FlagUnipotentStabilizers.SplitsCompletely E g →
    ∀ w : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ w.asIdeal →
      Nonempty ((𝓞 E ⧸ w.asIdeal) ≃+* ZMod g) ∧ (g : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  intro E _ _ g hg h w hw
  haveI := w.isPrime
  haveI := Fact.mk hg
  have h' := (card_eq_ncard_primesOver E hg).symm.trans h
  obtain ⟨h1, h2⟩ := GlobalTheory.LocSplit.split_prime hg h' w.asIdeal hw
  refine ⟨?_, h1⟩
  haveI : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.2 w.isPrime.ne_top
  haveI : CharP (𝓞 E ⧸ w.asIdeal) g := by
    rw [CharP.charP_iff_prime_eq_zero hg, ← map_natCast (Ideal.Quotient.mk w.asIdeal),
      Ideal.Quotient.eq_zero_iff_mem]
    exact hw
  refine ⟨(RingEquiv.ofBijective (ZMod.castHom (dvd_refl g) (𝓞 E ⧸ w.asIdeal))
    ⟨ZMod.castHom_injective _, fun y => ?_⟩).symm⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨m, hm⟩ := h2 x
  refine ⟨(m : ZMod g), ?_⟩
  rw [map_intCast, ← map_intCast (Ideal.Quotient.mk w.asIdeal), eq_comm, Ideal.Quotient.eq]
  exact hm

end GlobalTheory.SplitResidue
