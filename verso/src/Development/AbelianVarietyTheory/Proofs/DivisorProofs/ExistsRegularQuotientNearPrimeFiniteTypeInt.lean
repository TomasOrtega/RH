import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericallyRegularQuotientDominatingPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationQuotientComapEquiv
open IsLocalRing TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `B _ _ p hp`. Distinguish the cases in `h : ∀ a : ℤ, algebraMap ℤ B a ∈ p → a = 0`. Conclude with `GlobalTheory.T.exists_genericallyRegular_quotient_dominating_prime ℤ B p h`. Use `push_neg at h`. Take `⟨a, ha, ha0⟩` from `h`.

Establish `hP : (p.comap (algebraMap ℤ B)) ≠ ⊥`. Introduce `hb`. Apply `ha0` to reduce the goal to its premises. Establish `: a ∈ p.comap (algebraMap ℤ B)` using `ha`. Rewrite `this` using `[hb]`.

Simplify using `using this`. Take `⟨x, hx, hxp⟩` from `Ideal.IsPrime.exists_mem_prime_of_ne_bot (Ideal.IsPrime.comap _) hP`. Use `set l := x.natAbs with hl`. Establish `hlp : l.Prime` using `Int.prime_iff_natAbs_prime.mp hxp`. Use `haveI : Fact l.Prime := ⟨hlp⟩`.

Establish `hlmem : (l : B) ∈ p`. Establish `hx' : algebraMap ℤ B x ∈ p` using `hx`. Break down `Int.natAbs_eq x with h1 | h1` into its components or cases. Rewrite `hx'` using `[h1]`. Simplify `hx'` using `[hl]`.

Rewrite `hx'` using `[h1]`. Simplify `hx'` using `[hl]`. Use `set I : Ideal B := Ideal.span {(l : B)} with hI`. Set `mk` to `Ideal.Quotient.mk I`. Establish `hmk : Function.Surjective mk` using `Ideal.Quotient.mk_surjective`.

Establish `hker : RingHom.ker mk = I` using `Ideal.mk_ker`. Establish `hIp : I ≤ p`. Rewrite using `[hI, Ideal.span_le]`. Simplify using `using hlmem`. Establish `hl0 : ∀ a ∈ Ideal.span {((l : ℕ) : ℤ)}, (Int.castRingHom (B ⧸ I)) a = 0`.

Introduce `a ha`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton.mp ha`. Establish `: ((l : ℕ) : B ⧸ I) = 0`. Establish `h0 : (Ideal.Quotient.mk I) (l : B) = 0` using `(Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span rfl)`. Simplify using `using h0`.

Simplify using `[this]`. Set `ψ : ZMod l →+* B ⧸ I` to `(Ideal.Quotient.lift (Ideal.span {((l : ℕ) : ℤ)}) (Int.castRingHom (B ⧸ I)) hl0).comp (Int.quotientSpanNatEquivZMod l).symm.toRingHom`. Use `letI : Algebra (ZMod l) (B ⧸ I) := ψ.toAlgebra`. Use `haveI : IsScalarTower ℤ (ZMod l) (B ⧸ I) := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)`. Use `haveI : Algebra.FiniteType (ZMod l) (B ⧸ I) := Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod l) (B ⧸ I)`.

Use `haveI : PerfectField (FractionRing (ZMod l)) := by`. Establish `: Finite (FractionRing (ZMod l))` using `Finite.of_equiv _ (FractionRing.algEquiv (ZMod l) (ZMod l)).toEquiv.symm`. Use `infer_instance`. Establish `corr : ∀ (r : Ideal B), r.IsPrime → I ≤ r → (r.map mk).IsPrime ∧ (r.map mk).comap mk = r`. Introduce `r hr hIr`.

Use `⟨Ideal.map_isPrime_of_surjective hmk (by rw [hker]; exact hIr), ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.comap_map_of_surjective' mk hmk, hker]`. Conclude with `sup_eq_left.mpr hIr`. Take `⟨p', hp', rfl⟩ : ∃ p' : Ideal (B ⧸ I), p'.IsPrime ∧ p'.comap mk = p` from `⟨p.map mk, corr p hp hIp⟩`. Establish `hdom : ∀ a : ZMod l, algebraMap (ZMod l) (B ⧸ I) a ∈ p' → a = 0`.

Introduce `a ha`. Assume the negation of the conclusion as `ha0`. Conclude with `hp'.ne_top (Ideal.eq_top_of_isUnit_mem _ ha ((IsUnit.mk0 a ha0).map _))`. Take `⟨g', hg'p, hg'⟩` from `GlobalTheory.T.exists_genericallyRegular_quotient_dominating_prime (ZMod l) (B ⧸ I) p' hdom`. Take `⟨g, rfl⟩` from `hmk g'`.

Use `⟨g, fun hg => hg'p hg, ?_⟩` and prove the remaining obligations. Introduce `q hq hpq hgq`. Establish `hIq : I ≤ q` using `hIp.trans hpq`. Take `⟨q', hq', rfl⟩ : ∃ q' : Ideal (B ⧸ I), q'.IsPrime ∧ q'.comap mk = q` from `⟨q.map mk, corr q hq hIq⟩`. Establish `hpq' : p' ≤ q'`.

Introduce `y hy`. Take `⟨y, rfl⟩` from `hmk y`. Conclude with `hpq hy`. Establish `hreg` using `hg' q' hpq' (fun h => hgq h)`. Take `⟨e⟩` from `GlobalTheory.localization_quotient_comap_equiv B (B ⧸ I) mk hmk p' q'`.

Conclude with `IsRegularLocalRing.of_ringEquiv e.symm`.
-/
theorem generically_regular_quotient_of_finiteType_int :
    ∀ (B : Type) [CommRing B] [Algebra.FiniteType ℤ B] (p : Ideal B) [p.IsPrime], ∃ g, g ∉ p ∧
      ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q →
        IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) := by
  intro B _ _ p hp
  by_cases h : ∀ a : ℤ, algebraMap ℤ B a ∈ p → a = 0
  · exact GlobalTheory.T.exists_genericallyRegular_quotient_dominating_prime ℤ B p h
  push_neg at h
  obtain ⟨a, ha, ha0⟩ := h
  have hP : (p.comap (algebraMap ℤ B)) ≠ ⊥ := by
    intro hb
    apply ha0
    have : a ∈ p.comap (algebraMap ℤ B) := ha
    rw [hb] at this
    simpa using this
  obtain ⟨x, hx, hxp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot (Ideal.IsPrime.comap _) hP
  set l := x.natAbs with hl
  have hlp : l.Prime := Int.prime_iff_natAbs_prime.mp hxp
  haveI : Fact l.Prime := ⟨hlp⟩
  have hlmem : (l : B) ∈ p := by
    have hx' : algebraMap ℤ B x ∈ p := hx
    rcases Int.natAbs_eq x with h1 | h1
    · rw [h1] at hx'
      simpa [hl] using hx'
    · rw [h1] at hx'
      simpa [hl] using hx'
  set I : Ideal B := Ideal.span {(l : B)} with hI
  let mk := Ideal.Quotient.mk I
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker mk = I := Ideal.mk_ker
  have hIp : I ≤ p := by
    rw [hI, Ideal.span_le]; simpa using hlmem
  have hl0 : ∀ a ∈ Ideal.span {((l : ℕ) : ℤ)}, (Int.castRingHom (B ⧸ I)) a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    have : ((l : ℕ) : B ⧸ I) = 0 := by
      have h0 : (Ideal.Quotient.mk I) (l : B) = 0 :=
        (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span rfl)
      simpa using h0
    simp [this]
  let ψ : ZMod l →+* B ⧸ I :=
    (Ideal.Quotient.lift (Ideal.span {((l : ℕ) : ℤ)}) (Int.castRingHom (B ⧸ I)) hl0).comp
      (Int.quotientSpanNatEquivZMod l).symm.toRingHom
  letI : Algebra (ZMod l) (B ⧸ I) := ψ.toAlgebra
  haveI : IsScalarTower ℤ (ZMod l) (B ⧸ I) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : Algebra.FiniteType (ZMod l) (B ⧸ I) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod l) (B ⧸ I)
  haveI : PerfectField (FractionRing (ZMod l)) := by
    have : Finite (FractionRing (ZMod l)) :=
      Finite.of_equiv _ (FractionRing.algEquiv (ZMod l) (ZMod l)).toEquiv.symm
    infer_instance

  have corr : ∀ (r : Ideal B), r.IsPrime → I ≤ r → (r.map mk).IsPrime ∧ (r.map mk).comap mk = r := by
    intro r hr hIr
    refine ⟨Ideal.map_isPrime_of_surjective hmk (by rw [hker]; exact hIr), ?_⟩
    rw [Ideal.comap_map_of_surjective' mk hmk, hker]
    exact sup_eq_left.mpr hIr
  obtain ⟨p', hp', rfl⟩ : ∃ p' : Ideal (B ⧸ I), p'.IsPrime ∧ p'.comap mk = p :=
    ⟨p.map mk, corr p hp hIp⟩
  have hdom : ∀ a : ZMod l, algebraMap (ZMod l) (B ⧸ I) a ∈ p' → a = 0 := by
    intro a ha
    by_contra ha0
    exact hp'.ne_top (Ideal.eq_top_of_isUnit_mem _ ha ((IsUnit.mk0 a ha0).map _))
  obtain ⟨g', hg'p, hg'⟩ := GlobalTheory.T.exists_genericallyRegular_quotient_dominating_prime (ZMod l) (B ⧸ I) p' hdom
  obtain ⟨g, rfl⟩ := hmk g'
  refine ⟨g, fun hg => hg'p hg, ?_⟩
  intro q hq hpq hgq
  have hIq : I ≤ q := hIp.trans hpq
  obtain ⟨q', hq', rfl⟩ : ∃ q' : Ideal (B ⧸ I), q'.IsPrime ∧ q'.comap mk = q :=
    ⟨q.map mk, corr q hq hIq⟩
  have hpq' : p' ≤ q' := by
    intro y hy
    obtain ⟨y, rfl⟩ := hmk y
    exact hpq hy
  have hreg := hg' q' hpq' (fun h => hgq h)
  obtain ⟨e⟩ := GlobalTheory.localization_quotient_comap_equiv B (B ⧸ I) mk hmk p' q'
  exact IsRegularLocalRing.of_ringEquiv e.symm

end GlobalTheory
