import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PulledRead
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionKilledByIdealCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroOfIsUnit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

/- English proof (translation)
Introduce `hW p _ D O _ _ _ _ f b N r w _ hS M V _ _ _ _ hp x W`. Take `⟨ρ, -, -, hρ3, -⟩` from `hW p D O b N M w V x`. Establish `hpO : (p : O) ∈ IsLocalRing.maximalIdeal O` using `hS.pmem`. Establish `hK : CharZero (FractionRing V)`. Set `φ : O →+* V` to `(Spec.preimage (x ≫ M.s)).hom`.

Use `haveI : CharP (FractionRing V) (ringChar (FractionRing V)) := ringChar.charP _`. Break down `CharP.char_is_prime_or_zero (FractionRing V) (ringChar (FractionRing V)) with hq | hq` into its components or cases. It suffices to derive a contradiction. Establish `hqK : ((ringChar (FractionRing V) : ℕ) : FractionRing V) = 0` using `ringChar.Nat.cast_ringChar`. Establish `hqV : ((ringChar (FractionRing V) : ℕ) : V) = 0`.

Apply `IsFractionRing.injective V (FractionRing V)` to reduce the goal to its premises. Rewrite using `[map_natCast, map_zero]`. Conclude with `hqK`. Distinguish the cases in `hpq : ringChar (FractionRing V) = p`. Conclude with `hp (hpq ▸ hqV)`.

Establish `hcop : Nat.Coprime p (ringChar (FractionRing V))` using `(Nat.coprime_primes Fact.out hq).2 (Ne.symm hpq)`. Establish `hu : IsUnit ((ringChar (FractionRing V) : ℕ) : O)`. Assume the negation of the conclusion as `hnu`. Establish `hm : ((ringChar (FractionRing V) : ℕ) : O) ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal _).2 hnu`. Take `⟨a, c, hac⟩` from `(Nat.isCoprime_iff_coprime.2 hcop).intCast (R := O)`.

Simplify using `only [Int.cast_natCast] at hac`. Establish `h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O`. Rewrite using `[← hac]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpO) (Ideal.mul_mem_left _ _ hm)`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)`.

Use `(hu.map φ).ne_zero` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Conclude with `this hqV`. Use `haveI := ringChar.of_eq hq`. Conclude with `CharP.charP_to_charZero (FractionRing V)`.

Establish `hpf : p ^ f ≠ 0` using `pow_ne_zero f (Fact.out : Nat.Prime p).ne_zero`. Establish `hw : w ≠ ⊥`. Introduce `h`. Use `hS.norm` as an intermediate fact. Rewrite `this` using `[h, Ideal.absNorm_bot]`.

Conclude with `hpf this.symm`. Establish `hcard` using `CharZeroCount.card_killedBy_charZero p D O b N M.X M.s M.univ w hw (FractionRing V) (spMap (algebraMap V (FractionRing V)) ≫ x)`. Set `Φ : {g : Over.mk x ⟶ M.univ.A // KilledBy M.univ w g} → {h : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ x) ⟶ M.univ.A // KilledBy M.univ w h}` to `fun g => ⟨ρ g.1, (hρ3 g.1).1 g.2⟩`. Establish `hΦ : Function.Bijective Φ`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩ he`. Conclude with `Subtype.ext (ρ.injective (congrArg Subtype.val he))`. Introduce and unpack `⟨h, hh⟩`. Use `⟨⟨ρ.symm h, (hρ3 _).2 (by simpa using hh)⟩, ?_⟩` and prove the remaining obligations. Conclude with `Subtype.ext (by simp [Φ])`.

Set `Ψ : W.H → {g : Over.mk x ⟶ M.univ.A // KilledBy M.univ w g}` to `fun h => ⟨W.pt h, (W.range _).1 ⟨h, rfl⟩⟩`. Establish `hΨ : Function.Bijective Ψ`. Prove the components needed by the constructor for the conclusion. Introduce `a c hac`. Conclude with `W.inj (congrArg Subtype.val hac)`.

Introduce and unpack `⟨g, hg⟩`. Take `⟨h, rfl⟩` from `(W.range g).2 hg`. Conclude with `⟨h, rfl⟩`. Establish `hH : Nat.card W.H = Ideal.absNorm w ^ D.n`. Rewrite using `[Nat.card_eq_of_bijective _ (hΦ.comp hΨ), hcard, hS.m1, _root_.one_mul]`.

Establish `hnz : Ideal.absNorm w ≠ 0` using `by rw [hS.norm]; exact hpf`. Use `haveI : Finite W.H := Nat.finite_of_card_ne_zero (by rw [hH]; exact pow_ne_zero _ hnz)`. Establish `hk : Nat.card (𝓞 D.F ⧸ w) = Ideal.absNorm w`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Use `haveI : Finite (𝓞 D.F ⧸ w) := Nat.finite_of_card_ne_zero (by rw [hk]; exact hnz)`.

Establish `h2 : 2 ≤ Ideal.absNorm w`. Rewrite using `[← hk]`. Conclude with `Finite.one_lt_card`. Use `⟨Module.Finite.of_finite, ?_⟩` and prove the remaining obligations. Use `letI := Fintype.ofFinite W.H`.

Use `letI := Fintype.ofFinite (𝓞 D.F ⧸ w)`. Use `Module.card_eq_pow_finrank (K := 𝓞 D.F ⧸ w) (V := W.H)` as an intermediate fact. Rewrite `this` using `[← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hH, hk]`. Conclude with `(Nat.pow_right_injective h2 this).symm`.
-/
theorem UpperTheory.Gal.crystallineComparison.Mod.rankN_of :
    WVal → RankN := by
  intro hW p _ D O _ _ _ _ f b N r w _ hS M V _ _ _ _ hp x W
  obtain ⟨ρ, -, -, hρ3, -⟩ := hW p D O b N M w V x
  have hpO : (p : O) ∈ IsLocalRing.maximalIdeal O := hS.pmem
  have hK : CharZero (FractionRing V) := by
    let φ : O →+* V := (Spec.preimage (x ≫ M.s)).hom
    haveI : CharP (FractionRing V) (ringChar (FractionRing V)) := ringChar.charP _
    rcases CharP.char_is_prime_or_zero (FractionRing V) (ringChar (FractionRing V)) with hq | hq
    · exfalso
      have hqK : ((ringChar (FractionRing V) : ℕ) : FractionRing V) = 0 := ringChar.Nat.cast_ringChar
      have hqV : ((ringChar (FractionRing V) : ℕ) : V) = 0 := by
        apply IsFractionRing.injective V (FractionRing V)
        rw [map_natCast, map_zero]
        exact hqK
      by_cases hpq : ringChar (FractionRing V) = p
      · exact hp (hpq ▸ hqV)
      · have hcop : Nat.Coprime p (ringChar (FractionRing V)) :=
          (Nat.coprime_primes Fact.out hq).2 (Ne.symm hpq)
        have hu : IsUnit ((ringChar (FractionRing V) : ℕ) : O) := by
          by_contra hnu
          have hm : ((ringChar (FractionRing V) : ℕ) : O) ∈ IsLocalRing.maximalIdeal O :=
            (IsLocalRing.mem_maximalIdeal _).2 hnu
          obtain ⟨a, c, hac⟩ := (Nat.isCoprime_iff_coprime.2 hcop).intCast (R := O)
          simp only [Int.cast_natCast] at hac
          have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
            rw [← hac]
            exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpO) (Ideal.mul_mem_left _ _ hm)
          exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)
        have := (hu.map φ).ne_zero
        rw [map_natCast] at this
        exact this hqV
    · haveI := ringChar.of_eq hq
      exact CharP.charP_to_charZero (FractionRing V)
  have hpf : p ^ f ≠ 0 := pow_ne_zero f (Fact.out : Nat.Prime p).ne_zero
  have hw : w ≠ ⊥ := by
    intro h
    have := hS.norm
    rw [h, Ideal.absNorm_bot] at this
    exact hpf this.symm
  have hcard := CharZeroCount.card_killedBy_charZero p D O b N M.X M.s M.univ w hw (FractionRing V)
    (spMap (algebraMap V (FractionRing V)) ≫ x)
  let Φ : {g : Over.mk x ⟶ M.univ.A // KilledBy M.univ w g} →
      {h : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ x) ⟶ M.univ.A // KilledBy M.univ w h} :=
    fun g => ⟨ρ g.1, (hρ3 g.1).1 g.2⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩ he
      exact Subtype.ext (ρ.injective (congrArg Subtype.val he))
    · rintro ⟨h, hh⟩
      refine ⟨⟨ρ.symm h, (hρ3 _).2 (by simpa using hh)⟩, ?_⟩
      exact Subtype.ext (by simp [Φ])
  let Ψ : W.H → {g : Over.mk x ⟶ M.univ.A // KilledBy M.univ w g} :=
    fun h => ⟨W.pt h, (W.range _).1 ⟨h, rfl⟩⟩
  have hΨ : Function.Bijective Ψ := by
    constructor
    · intro a c hac
      exact W.inj (congrArg Subtype.val hac)
    · rintro ⟨g, hg⟩
      obtain ⟨h, rfl⟩ := (W.range g).2 hg
      exact ⟨h, rfl⟩
  have hH : Nat.card W.H = Ideal.absNorm w ^ D.n := by
    rw [Nat.card_eq_of_bijective _ (hΦ.comp hΨ), hcard, hS.m1, _root_.one_mul]
  have hnz : Ideal.absNorm w ≠ 0 := by rw [hS.norm]; exact hpf
  haveI : Finite W.H := Nat.finite_of_card_ne_zero (by rw [hH]; exact pow_ne_zero _ hnz)
  have hk : Nat.card (𝓞 D.F ⧸ w) = Ideal.absNorm w := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.F ⧸ w) := Nat.finite_of_card_ne_zero (by rw [hk]; exact hnz)
  have h2 : 2 ≤ Ideal.absNorm w := by
    rw [← hk]
    exact Finite.one_lt_card
  refine ⟨Module.Finite.of_finite, ?_⟩
  letI := Fintype.ofFinite W.H
  letI := Fintype.ofFinite (𝓞 D.F ⧸ w)
  have := Module.card_eq_pow_finrank (K := 𝓞 D.F ⧸ w) (V := W.H)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hH, hk] at this
  exact (Nat.pow_right_injective h2 this).symm
