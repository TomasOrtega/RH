import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqZeroIffV

set_option autoImplicit false

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

namespace GlobalTheory.PrimePart

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Establish `hmem : ((p : ℕ) : 𝓞 E) ∈ RingHom.ker f`. Rewrite using `[RingHom.mem_ker, map_natCast]`. Conclude with `CharP.cast_eq_zero k p`. Establish `hne : RingHom.ker f ≠ ⊥`.

Introduce `h`. Rewrite `hmem` using `[h, Ideal.mem_bot]`. Conclude with `hp.ne_zero (Nat.cast_eq_zero.1 hmem)`. Establish `hmax : (RingHom.ker f).IsMaximal` using `(RingHom.ker_isPrime f).isMaximal hne`. Use `⟨hmax, ?_⟩` and prove the remaining obligations.

Use `haveI : Finite (𝓞 E ⧸ RingHom.ker f) := Ideal.finiteQuotientOfFreeOfNeBot _ hne`. Use `letI : Fintype (𝓞 E ⧸ RingHom.ker f) := Fintype.ofFinite _`. Use `letI : Field (𝓞 E ⧸ RingHom.ker f) := Ideal.Quotient.field _`. Use `haveI : CharP (𝓞 E ⧸ RingHom.ker f) p := by`. Use `(CharP.charP_iff_prime_eq_zero hp).2 ?_` and prove the remaining obligations.

Rewrite using `[← map_natCast (Ideal.Quotient.mk (RingHom.ker f)), Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hmem`. Take `⟨n, -, hn⟩` from `FiniteField.card (𝓞 E ⧸ RingHom.ker f) p`. Conclude with `⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩`.
-/
theorem ker_isMaximal_card {E k : Type} [Field E] [NumberField E] [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : 𝓞 E →+* k) :
    (RingHom.ker f).IsMaximal ∧ ∃ h : ℕ, 0 < h ∧ Nat.card (𝓞 E ⧸ RingHom.ker f) = p ^ h := by
  have hp : p.Prime := Fact.out
  have hmem : ((p : ℕ) : 𝓞 E) ∈ RingHom.ker f := by
    rw [RingHom.mem_ker, map_natCast]
    exact CharP.cast_eq_zero k p
  have hne : RingHom.ker f ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hmem
    exact hp.ne_zero (Nat.cast_eq_zero.1 hmem)
  have hmax : (RingHom.ker f).IsMaximal := (RingHom.ker_isPrime f).isMaximal hne
  refine ⟨hmax, ?_⟩
  haveI : Finite (𝓞 E ⧸ RingHom.ker f) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  letI : Fintype (𝓞 E ⧸ RingHom.ker f) := Fintype.ofFinite _
  letI : Field (𝓞 E ⧸ RingHom.ker f) := Ideal.Quotient.field _
  haveI : CharP (𝓞 E ⧸ RingHom.ker f) p := by
    refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
    rw [← map_natCast (Ideal.Quotient.mk (RingHom.ker f)), Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 E ⧸ RingHom.ker f) p
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

/- English proof (translation)
Use `haveI := charP_residueField_of_irreducible X`. Rewrite using `[primeBelow_eq_ker]`. Conclude with `ker_isMaximal_card p (red io X τ)`.
-/
theorem primeBelow_isMaximal_card (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H)
    (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p) (τ : E →+* ℂ) :
    (primeBelow io X τ).IsMaximal ∧ ∃ h : ℕ, 0 < h ∧ Nat.card (𝓞 E ⧸ primeBelow io X τ) = p ^ h := by
  haveI := charP_residueField_of_irreducible X
  rw [primeBelow_eq_ker]
  exact ker_isMaximal_card p (red io X τ)

end GlobalTheory.PrimePart
