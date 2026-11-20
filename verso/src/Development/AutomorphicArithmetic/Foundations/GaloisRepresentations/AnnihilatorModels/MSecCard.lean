import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PulledRead
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeomClausesIff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

/- English proof (translation)
Introduce `p _ D R _ b N M r w j c T hm K _ _ hp x y hxy`. Substitute `hxy` using the available equality. Set `β : R →+* K` to `(Spec.preimage (y ≫ T.s ≫ M.s)).hom`. Use `haveI : CharZero K := by`. Break down `CharP.char_is_prime_or_zero K (ringChar K) with hq | hq` into its components or cases.

It suffices to derive a contradiction. Establish `hcast : ((ringChar K : ℕ) : K) = 0` using `ringChar.Nat.cast_ringChar`. Distinguish the cases in `hqp : ringChar K = p`. Rewrite `hcast` using `[hqp]`. Conclude with `hp hcast`.

Establish `hcop : (ringChar K).Coprime p` using `(Nat.coprime_primes hq (Fact.out)).mpr hqp`. Establish `hu` using `(b.unit _ hcop).map β`. Rewrite `hu` using `[map_natCast, hcast]`. Conclude with `not_isUnit_zero hu`. Use `haveI : CharP K 0 := ringChar.of_eq hq`.

Conclude with `CharP.charP_to_charZero K`. Take `⟨-, hcard⟩` from `T.tj K y`. Rewrite `hcard` using `[hm, Nat.one_mul]`. Rewrite using `[← hcard]`. Use `symm`.

Establish `hK : ∀ a : Over.mk y ⟶ T.o.A, KilledBy T.o w a ↔ KilledBy M.univ w (T.ms.ptEquiv (Over.mk y) a)`. Introduce `a`. Unfold `KilledBy`. Use `forall₂_congr (fun c _ => ?_)` and prove the remaining obligations. Rewrite using `[← ObjMap.ptEquiv_act, MulEquiv.map_eq_one_iff]`.

Establish `hker : ∀ a : Over.mk y ⟶ T.o.A, KerAt T y (T.ms.ptEquiv (Over.mk y) a).left ↔ a ≫ T.ψ = 1`. Introduce `a`. Rewrite using `[ObjMap.ptEquiv_left]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `h a rfl`. Introduce `h a' ha'`. Establish `ha : a' = a`. Apply `(T.ms.ptEquiv (Over.mk y)).injective` to reduce the goal to its premises. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Rewrite using `[ObjMap.ptEquiv_left, ObjMap.ptEquiv_left, ha']`. Rewrite using `[ha]`. Conclude with `h`. Use `Nat.card_congr (Equiv.subtypeEquiv (T.ms.ptEquiv (Over.mk y)).toEquiv (fun a => ?_))` and prove the remaining obligations. Conclude with `⟨fun h => ⟨(hK a).mp h.2, (hker a).mpr h.1⟩, fun h => ⟨(hker a).mp h.2, (hK a).mpr h.1⟩⟩`.
-/
theorem UpperTheory.Gal.crystallineComparison.Mod.secCard_of :
    SecCard := by
  intro p _ D R _ b N M r w j c T hm K _ _ hp x y hxy
  subst hxy
  let β : R →+* K := (Spec.preimage (y ≫ T.s ≫ M.s)).hom
  haveI : CharZero K := by
    rcases CharP.char_is_prime_or_zero K (ringChar K) with hq | hq
    · exfalso
      have hcast : ((ringChar K : ℕ) : K) = 0 := ringChar.Nat.cast_ringChar
      by_cases hqp : ringChar K = p
      · rw [hqp] at hcast
        exact hp hcast
      · have hcop : (ringChar K).Coprime p := (Nat.coprime_primes hq (Fact.out)).mpr hqp
        have hu := (b.unit _ hcop).map β
        rw [map_natCast, hcast] at hu
        exact not_isUnit_zero hu
    · haveI : CharP K 0 := ringChar.of_eq hq
      exact CharP.charP_to_charZero K
  obtain ⟨-, hcard⟩ := T.tj K y
  rw [hm, Nat.one_mul] at hcard
  rw [← hcard]
  symm
  have hK : ∀ a : Over.mk y ⟶ T.o.A,
      KilledBy T.o w a ↔ KilledBy M.univ w (T.ms.ptEquiv (Over.mk y) a) := by
    intro a
    unfold KilledBy
    refine forall₂_congr (fun c _ => ?_)
    rw [← ObjMap.ptEquiv_act, MulEquiv.map_eq_one_iff]
  have hker : ∀ a : Over.mk y ⟶ T.o.A,
      KerAt T y (T.ms.ptEquiv (Over.mk y) a).left ↔ a ≫ T.ψ = 1 := by
    intro a
    rw [ObjMap.ptEquiv_left]
    constructor
    · intro h
      exact h a rfl
    · intro h a' ha'
      have ha : a' = a := by
        apply (T.ms.ptEquiv (Over.mk y)).injective
        apply Over.OverMorphism.ext
        rw [ObjMap.ptEquiv_left, ObjMap.ptEquiv_left, ha']
      rw [ha]
      exact h
  refine Nat.card_congr (Equiv.subtypeEquiv (T.ms.ptEquiv (Over.mk y)).toEquiv (fun a => ?_))
  exact ⟨fun h => ⟨(hK a).mp h.2, (hker a).mpr h.1⟩, fun h => ⟨(hker a).mp h.2, (hK a).mpr h.1⟩⟩
