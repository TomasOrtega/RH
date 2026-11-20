import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedQuadraticCharSignSplitEqOneInertEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.TwistTypePlaces

/- English proof (translation)
Use `set p := (P.under (𝓞 F)).asIdeal with hp`. Establish `hp0 : p ≠ ⊥` using `(P.under (𝓞 F)).ne_bot`. Establish `: p.IsMaximal` using `(P.under (𝓞 F)).isMaximal`. Establish `: P.asIdeal.LiesOver p` using `⟨by rw [hp, HeightOneSpectrum.under_asIdeal]⟩`. Establish `hsum` using `Ideal.sum_ramification_inertia (𝓞 E) F E (p := p) hp0`.

Establish `hcard : (IsDedekindDomain.primesOverFinset p (𝓞 E)).card = 2`. Rewrite using `[← h2, ← IsDedekindDomain.coe_primesOverFinset hp0 (𝓞 E), Set.ncard_coe_finset]`. Establish `hle : ∀ Q ∈ IsDedekindDomain.primesOverFinset p (𝓞 E), 1 ≤ p.ramificationIdx' Q * p.inertiaDeg' Q`. Introduce `Q hQ`. Take `⟨hQp, hQl⟩` from `(IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 E)).1 hQ`.

Establish `h1 : 0 < p.inertiaDeg' Q` using `Ideal.inertiaDeg'_pos p Q`. Establish `h2 : 0 < p.ramificationIdx' Q`. Rewrite using `[Ideal.ramificationIdx'_eq_ramificationIdx p Q hp0]`. Conclude with `Ideal.ramificationIdx_pos Q (𝓞 F)`. Conclude with `Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero h2.ne' h1.ne')`.

Establish `heq` using `(Finset.sum_eq_sum_iff_of_le hle).1 (by rw [hsum, hr, Finset.sum_const, hcard]; rfl)`. Establish `hPm : P.asIdeal ∈ IsDedekindDomain.primesOverFinset p (𝓞 E)` using `(IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 E)).2 ⟨P.isPrime, inferInstance⟩`. Establish `hf : p.inertiaDeg' P.asIdeal = 1` using `Nat.eq_one_of_mul_eq_one_left (heq _ hPm).symm`. Establish `hn` using `Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.asIdeal p (P.under (𝓞 F)).isPrime hp0`. Rewrite `hn` using `[hf, pow_one, Ideal.absNorm_apply, Submodule.cardQuot_apply]`.

Conclude with `hn`.
-/
theorem card_quot_of_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (hr : Module.finrank F E = 2) (P : HeightOneSpectrum (𝓞 E))
    (h2 : (Ideal.primesOver (P.under (𝓞 F)).asIdeal (𝓞 E)).ncard = 2) :
    Nat.card (𝓞 E ⧸ P.asIdeal) = Ideal.absNorm (P.under (𝓞 F)).asIdeal := by
  classical
  set p := (P.under (𝓞 F)).asIdeal with hp
  have hp0 : p ≠ ⊥ := (P.under (𝓞 F)).ne_bot
  have : p.IsMaximal := (P.under (𝓞 F)).isMaximal
  have : P.asIdeal.LiesOver p := ⟨by rw [hp, HeightOneSpectrum.under_asIdeal]⟩
  have hsum := Ideal.sum_ramification_inertia (𝓞 E) F E (p := p) hp0
  have hcard : (IsDedekindDomain.primesOverFinset p (𝓞 E)).card = 2 := by
    rw [← h2, ← IsDedekindDomain.coe_primesOverFinset hp0 (𝓞 E), Set.ncard_coe_finset]
  have hle : ∀ Q ∈ IsDedekindDomain.primesOverFinset p (𝓞 E), 1 ≤ p.ramificationIdx' Q * p.inertiaDeg' Q := by
    intro Q hQ
    obtain ⟨hQp, hQl⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 E)).1 hQ
    have h1 : 0 < p.inertiaDeg' Q := Ideal.inertiaDeg'_pos p Q
    have h2 : 0 < p.ramificationIdx' Q := by
      rw [Ideal.ramificationIdx'_eq_ramificationIdx p Q hp0]
      exact Ideal.ramificationIdx_pos Q (𝓞 F)
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero h2.ne' h1.ne')
  have heq := (Finset.sum_eq_sum_iff_of_le hle).1 (by rw [hsum, hr, Finset.sum_const, hcard]; rfl)
  have hPm : P.asIdeal ∈ IsDedekindDomain.primesOverFinset p (𝓞 E) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 E)).2 ⟨P.isPrime, inferInstance⟩
  have hf : p.inertiaDeg' P.asIdeal = 1 := Nat.eq_one_of_mul_eq_one_left (heq _ hPm).symm
  have hn := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.asIdeal p (P.under (𝓞 F)).isPrime hp0
  rw [hf, pow_one, Ideal.absNorm_apply, Submodule.cardQuot_apply] at hn
  exact hn

end GlobalTheory.TwistTypePlaces

namespace GlobalTheory.TwistTypePlaces

/- English proof (translation)
Establish `hfix : ∀ x : 𝓞 D.host.F, Formalism.DivisionValues.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x`. Introduce `x`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `show star ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x : 𝓞 D.host.E) : D.host.E) = _`. Conclude with `(D.sp.cm.fixed _).2 ⟨(x : D.host.F), rfl⟩`.

Establish `hinv : ∀ z, Formalism.DivisionValues.cO D.host.E (Formalism.DivisionValues.cO D.host.E z) = z` using `fun z => RingOfIntegers.ext (star_star (z : D.host.E))`. Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `x`. Simplify using `only [HeightOneSpectrum.under_asIdeal, Ideal.mem_comap]`. Express the relevant statement in the definitionally equal form `algebraMap _ _ x ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) ↔ _`.

Rewrite using `[Ideal.mem_map_of_equiv]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, hzx⟩`. Establish `e : z = algebraMap _ _ x` using `by rw [← hinv z, hzx, hfix]`. Rewrite using `[← e]` and apply the resulting hypothesis.

Introduce `h`. Conclude with `⟨_, h, hfix x⟩`.
-/
theorem under_conjPl {D : D7} (P : Pl D.host.E) :
    (conjPl P).under (𝓞 D.host.F) = P.under (𝓞 D.host.F) := by
  have hfix : ∀ x : 𝓞 D.host.F,
      Formalism.DivisionValues.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x := by
    intro x
    apply RingOfIntegers.ext
    show star ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x : 𝓞 D.host.E) : D.host.E) = _
    exact (D.sp.cm.fixed _).2 ⟨(x : D.host.F), rfl⟩
  have hinv : ∀ z, Formalism.DivisionValues.cO D.host.E (Formalism.DivisionValues.cO D.host.E z) = z :=
    fun z => RingOfIntegers.ext (star_star (z : D.host.E))
  apply HeightOneSpectrum.ext
  ext x
  simp only [HeightOneSpectrum.under_asIdeal, Ideal.mem_comap]
  change algebraMap _ _ x ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) ↔ _
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨z, hz, hzx⟩
    have e : z = algebraMap _ _ x := by rw [← hinv z, hzx, hfix]
    rwa [← e]
  · intro h
    exact ⟨_, h, hfix x⟩

/- English proof (translation)
Use `Ideal.mem_map_of_mem (Formalism.DivisionValues.cO D.host.E) h` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.
-/
theorem natCast_mem_conjPl {D : D7} (P : Pl D.host.E) (n : ℕ) (h : (n : 𝓞 D.host.E) ∈ P.asIdeal) :
    (n : 𝓞 D.host.E) ∈ (conjPl P).asIdeal := by
  have := Ideal.mem_map_of_mem (Formalism.DivisionValues.cO D.host.E) h
  rwa [map_natCast] at this

/- English proof (translation)
Rewrite using `[GlobalTheory.QuadSignLocal.ncard_primesOver]`. Establish `hs : {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)} = {P, conjPl P}`. Use extensionality with `u`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion.

Conclude with `GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq`. Introduce and unpack `(rfl | rfl)`. Both sides reduce to the same expression. Conclude with `under_conjPl P`. Rewrite using `[hs, Set.ncard_pair h.symm]`.
-/
theorem ncard_primesOver_two {D : D7} (P : Pl D.host.E) (h : conjPl P ≠ P) :
    (Ideal.primesOver (P.under (𝓞 D.host.F)).asIdeal (𝓞 D.host.E)).ncard = 2 := by
  rw [GlobalTheory.QuadSignLocal.ncard_primesOver]
  have hs : {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)} = {P, conjPl P} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · exact GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq
    · rintro (rfl | rfl)
      · rfl
      · exact under_conjPl P
  rw [hs, Set.ncard_pair h.symm]

/- English proof (translation)
Introduce `hm`. Establish `hnt : Nontrivial (kP PP)` using `Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top`. Establish `hq0 : ((q : ℕ) : kP PP) = 0`. Use `card_nsmul_eq_zero' (G := kP PP) (x := 1)` as an intermediate fact. Rewrite `this` using `[hc, nsmul_one]`. Then use the resulting hypothesis.

Establish `hg0 : ((g : ℕ) : kP PP) = 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk PP.asIdeal), Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hm`. Take `⟨a, b, hab⟩ : IsCoprime (q : ℤ) (g : ℤ)` from `Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hg).2 hne)`. Establish `h1 : ((a * q + b * g : ℤ) : kP PP) = 1` using `by rw [hab, Int.cast_one]`.

Move the coercions through the operations in `at h1`. Rewrite `h1` using `[hq0, hg0, mul_zero, mul_zero, add_zero]`. Conclude with `zero_ne_one h1`.
-/
theorem natCast_not_mem_of_card {E : Type} [Field E] [NumberField E] (PP : Pl E) {q g : ℕ} (hq : q.Prime) (hg : g.Prime)
    (hc : Nat.card (kP PP) = q) (hne : q ≠ g) : ((g : ℕ) : 𝓞 E) ∉ PP.asIdeal := by
  intro hm
  have hnt : Nontrivial (kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
  have hq0 : ((q : ℕ) : kP PP) = 0 := by
    have := card_nsmul_eq_zero' (G := kP PP) (x := 1)
    rwa [hc, nsmul_one] at this
  have hg0 : ((g : ℕ) : kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hm
  obtain ⟨a, b, hab⟩ : IsCoprime (q : ℤ) (g : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hg).2 hne)
  have h1 : ((a * q + b * g : ℤ) : kP PP) = 1 := by rw [hab, Int.cast_one]
  push_cast at h1
  rw [hq0, hg0, mul_zero, mul_zero, add_zero] at h1
  exact zero_ne_one h1

end GlobalTheory.TwistTypePlaces

namespace GlobalTheory.TwistTypePlaces

/- English proof (translation)
Introduce `D G _ _ Pl0 T A Ks _ _ _ R F hC t`. Establish `hL` using `hC.lev`. Establish `hPg` using `hL.Pg`. Establish `hQ` using `hL.Q_pl t`. Establish `gP : ∀ PP ∈ R.Pg, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal`.

Introduce `PP h`. Take `⟨k, hk⟩` from `(hPg PP).1 h`. Conclude with `⟨k, R.C.P.overP hk⟩`. Establish `qN : ∀ PP ∈ R.Q t, ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal`. Introduce `PP h k`.

Take `⟨q, hq, hc, -, hne⟩` from `(hQ PP h).1`. Conclude with `natCast_not_mem_of_card PP hq (D.host.g_prime k) hc (hne k)`. Establish `hdis : Disjoint R.Pg (R.Q t)`. Rewrite using `[Finset.disjoint_left]`. Introduce `PP h1 h2`.

Take `⟨k, hk⟩` from `gP PP h1`. Conclude with `qN PP h2 k hk`. Establish `cross : ∀ PP ∈ R.Pg, ∀ PP' ∈ R.Q t, PP' ≠ conjPl PP`. Introduce and unpack `PP h PP' h' rfl`. Take `⟨k, hk⟩` from `gP PP h`.

Conclude with `qN _ h' k (natCast_mem_conjPl PP _ hk)`. Establish `hnc : ∀ PP ∈ R.Pg ∪ R.Q t, ∀ PP' ∈ R.Pg ∪ R.Q t, PP' ≠ conjPl PP`. Introduce `PP h PP' h' e`. Apply the tactic sequence `rcases Finset.mem_union.1 h with h | h <;> rcases Finset.mem_union.1 h' with h' | h'`. Conclude with `GlobalTheory.TypePlaces.not_isConjPl R.C.P R.Pg hPg PP h PP' h' (GlobalTheory.GoodPrimes.isConjPl_iff.2 e)`.

Conclude with `cross PP h PP' h' e`. Use `cross PP' h' PP h ?_` and prove the remaining obligations. Rewrite using `[e, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]`. Conclude with `(hQ PP h).2 PP' h' (GlobalTheory.GoodPrimes.isConjPl_iff.2 e)`. Use `⟨hdis, ?_, ?_⟩` and prove the remaining obligations.

Introduce `PP h PP' h' e`. Break down `GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with e' | e'` into its components or cases. Conclude with `e'.symm`. Conclude with `absurd e' (hnc PP h PP' h')`. Introduce `PP h`.

Establish `h2` using `ncard_primesOver_two PP (fun e => hnc PP h PP h e.symm)`. Conclude with `⟨h2, card_quot_of_two D.sp.cm.deg2 PP h2⟩`.
-/
theorem places_split : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ t : T, Disjoint R.Pg (R.Q t) ∧ Set.InjOn (fun PP : Pl D.host.E => PP.under (𝓞 D.host.F)) ↑(R.Pg ∪ R.Q t) ∧ ∀ PP ∈ R.Pg ∪ R.Q t, (Ideal.primesOver (PP.under (𝓞 D.host.F)).asIdeal (𝓞 D.host.E)).ncard = 2 ∧ Nat.card (kP PP) = Ideal.absNorm (PP.under (𝓞 D.host.F)).asIdeal := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t
  have hL := hC.lev
  have hPg := hL.Pg
  have hQ := hL.Q_pl t
  have gP : ∀ PP ∈ R.Pg, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP h
    obtain ⟨k, hk⟩ := (hPg PP).1 h
    exact ⟨k, R.C.P.overP hk⟩
  have qN : ∀ PP ∈ R.Q t, ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP h k
    obtain ⟨q, hq, hc, -, hne⟩ := (hQ PP h).1
    exact natCast_not_mem_of_card PP hq (D.host.g_prime k) hc (hne k)
  have hdis : Disjoint R.Pg (R.Q t) := by
    rw [Finset.disjoint_left]
    intro PP h1 h2
    obtain ⟨k, hk⟩ := gP PP h1
    exact qN PP h2 k hk
  have cross : ∀ PP ∈ R.Pg, ∀ PP' ∈ R.Q t, PP' ≠ conjPl PP := by
    rintro PP h PP' h' rfl
    obtain ⟨k, hk⟩ := gP PP h
    exact qN _ h' k (natCast_mem_conjPl PP _ hk)
  have hnc : ∀ PP ∈ R.Pg ∪ R.Q t, ∀ PP' ∈ R.Pg ∪ R.Q t, PP' ≠ conjPl PP := by
    intro PP h PP' h' e
    rcases Finset.mem_union.1 h with h | h <;> rcases Finset.mem_union.1 h' with h' | h'
    · exact GlobalTheory.TypePlaces.not_isConjPl R.C.P R.Pg hPg PP h PP' h' (GlobalTheory.GoodPrimes.isConjPl_iff.2 e)
    · exact cross PP h PP' h' e
    · refine cross PP' h' PP h ?_
      rw [e, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
    · exact (hQ PP h).2 PP' h' (GlobalTheory.GoodPrimes.isConjPl_iff.2 e)
  refine ⟨hdis, ?_, ?_⟩
  · intro PP h PP' h' e
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with e' | e'
    · exact e'.symm
    · exact absurd e' (hnc PP h PP' h')
  · intro PP h
    have h2 := ncard_primesOver_two PP (fun e => hnc PP h PP h e.symm)
    exact ⟨h2, card_quot_of_two D.sp.cm.deg2 PP h2⟩

end GlobalTheory.TwistTypePlaces
