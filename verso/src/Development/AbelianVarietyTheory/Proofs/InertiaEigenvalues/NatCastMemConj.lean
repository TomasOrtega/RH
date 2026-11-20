import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmallCoeffFieldEmbeddingCompHostMap
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaChrTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsResOfChrEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnrAtOfOff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameAtOfCongr
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterTrivialOnSubfieldOfIdelicReadingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.SeriesTie
open Formalism.L2.Host (embLL0)
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.TwistProduct

variable {D : D7}

/- English proof (translation)
Proceed by induction on `n, hn using Nat.le_induction with`. Consider the case `base => simpa using h`. Consider the case `succ n _ ih => rw [pow_succ, pow_succ]`. Conclude with `GlobalTheory.TowerCharRead.chrEq_mul ih h`.
-/
theorem chrEq_pow {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ) (n : ℕ) (hn : 0 < n) :
    ChrEq (c ^ n) (χ ^ n) := by
  induction n, hn using Nat.le_induction with
  | base => simpa using h
  | succ n _ ih => rw [pow_succ, pow_succ]; exact GlobalTheory.TowerCharRead.chrEq_mul ih h

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨continuous_const, fun _ => rfl⟩, fun _ _ _ _ _ _ => rfl⟩`.
-/
theorem chrEq_one_one : ChrEq (1 : (AE D)ˣ →* Circle) (1 : Formalism.L2.Host.HChar D.host.E) :=
  ⟨⟨continuous_const, fun _ => rfl⟩, fun _ _ _ _ _ _ => rfl⟩

/- English proof (translation)
Take `⟨c, hc, e⟩` from `h _ hn`. Establish `: c = (n : 𝓞 D.host.E)` using `RingOfIntegers.ext (by rw [e]; simp)`. Conclude with `this ▸ hc`.
-/
theorem natCast_mem_conj {P P' : Pl D.host.E} (h : Formalism.IndefR.Lev.IsConjPl P P') {n : ℕ}
    (hn : (n : 𝓞 D.host.E) ∈ P.asIdeal) : (n : 𝓞 D.host.E) ∈ P'.asIdeal := by
  obtain ⟨c, hc, e⟩ := h _ hn
  have : c = (n : 𝓞 D.host.E) := RingOfIntegers.ext (by rw [e]; simp)
  exact this ▸ hc

/- English proof (translation)
Distinguish the cases in `hv : v ∈ t.Q`. Establish `hr` using `GlobalTheory.TwistResidue.isRes_of_chrEq D t ht χ hχ v hv`. Use `GlobalTheory.TameConjPlace.tameAt_of_congr χ v fun a b ka kb hka hkb ha hab => ?_` and prove the remaining obligations. Use `haveI : v.asIdeal.IsMaximal := v.isMaximal`. Establish `hma : (Ideal.Quotient.mk v.asIdeal a : kP v) ≠ 0`.

Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `ha`. Establish `e1` using `hr a ka (Units.mk0 _ hma) hka rfl`. Establish `e2` using `hr b kb (Units.mk0 _ hma) hkb (Ideal.Quotient.eq.mpr hab)`. Rewrite using `[← e1, ← e2]`.

Distinguish the cases in `hc : ∃ P' ∈ t.Q, Formalism.IndefR.Lev.IsConjPl P' v`. Take `⟨P', hP', hPc⟩` from `hc`. Conclude with `GlobalTheory.TameConjPlace.tameAt_conj D t ht χ hχ P' hP' v hPc`. Establish `hu` using `GlobalTheory.TwistUnrOff.unrAt_of_off D t ht χ hχ v hv hc`. Introduce `x hx _`.

Conclude with `hu x hx`.
-/
theorem tameAt_of_good (t : Twist D Circle) (ht : t.Good) (χ : Formalism.L2.Host.HChar D.host.E) (hχ : ChrEq t.chi χ)
    (v : Pl D.host.E) : χ.TameAt v := by
  by_cases hv : v ∈ t.Q
  · have hr := GlobalTheory.TwistResidue.isRes_of_chrEq D t ht χ hχ v hv
    refine GlobalTheory.TameConjPlace.tameAt_of_congr χ v fun a b ka kb hka hkb ha hab => ?_
    haveI : v.asIdeal.IsMaximal := v.isMaximal
    have hma : (Ideal.Quotient.mk v.asIdeal a : kP v) ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact ha
    have e1 := hr a ka (Units.mk0 _ hma) hka rfl
    have e2 := hr b kb (Units.mk0 _ hma) hkb (Ideal.Quotient.eq.mpr hab)
    rw [← e1, ← e2]
  · by_cases hc : ∃ P' ∈ t.Q, Formalism.IndefR.Lev.IsConjPl P' v
    · obtain ⟨P', hP', hPc⟩ := hc
      exact GlobalTheory.TameConjPlace.tameAt_conj D t ht χ hχ P' hP' v hPc
    · have hu := GlobalTheory.TwistUnrOff.unrAt_of_off D t ht χ hχ v hv hc
      intro x hx _
      exact hu x hx

/- English proof (translation)
Use `GlobalTheory.TwistUnrOff.unrAt_of_off D t ht χ hχ v (fun h => hv (hpd v h)) ?_` and prove the remaining obligations. Introduce and unpack `⟨P', hP', hc⟩`. Conclude with `hv (natCast_mem_conj hc (hpd P' hP'))`.
-/
theorem unrAt_of_good (t : Twist D Circle) (ht : t.Good) (χ : Formalism.L2.Host.HChar D.host.E) (hχ : ChrEq t.chi χ) (pd : ℕ)
    (hpd : ∀ PP ∈ t.Q, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (v : Pl D.host.E)
    (hv : ((pd : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) : χ.UnrAt v := by
  refine GlobalTheory.TwistUnrOff.unrAt_of_off D t ht χ hχ v (fun h => hv (hpd v h)) ?_
  rintro ⟨P', hP', hc⟩
  exact hv (natCast_mem_conj hc (hpd P' hP'))

/- English proof (translation)
Introduce `D t t' ht ht' _ _ pd k _ σ hn hpd hval`. Take `⟨χ, hχ⟩` from `GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D t.chi ht.isHeckeChar`. Take `⟨χ', hχ'⟩` from `GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D t'.chi ht'.isHeckeChar`. Establish `hc : ChrEq (t.chi * t'.chi) (χ * χ')` using `GlobalTheory.TowerCharRead.chrEq_mul hχ hχ'`. Establish `hpd1 : ∀ PP ∈ t.Q, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal` using `fun PP h => hpd PP (Finset.mem_union_left _ h)`.

Establish `hpd2 : ∀ PP ∈ t'.Q, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal` using `fun PP h => hpd PP (Finset.mem_union_right _ h)`. Use `⟨χ * χ', hc, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨n, hn0, hnx⟩` from `hn`. Use `⟨n, hn0, ?_⟩` and prove the remaining obligations. Establish `hp` using `chrEq_pow hc n hn0`.

Establish `h1 : (t.chi * t'.chi) ^ n = 1` using `MonoidHom.ext fun x => by`. Rewrite using `[MonoidHom.pow_apply, hnx x, MonoidHom.one_apply]`. Rewrite `hp` using `[h1]`. Conclude with `GlobalTheory.ChrEqUnique.hchar_unique D 1 _ _ hp chrEq_one_one`. Conclude with `GlobalTheory.T.heckeCharacter_trivialOnSubfield_of_idelicReading D _ _ hc fun a => by rw [MonoidHom.mul_apply, ht.real, ht'.real, one_mul]`.

Introduce `v x hx hx1 show χ.loc v x * χ'.loc v x = 1`. Rewrite using `[tameAt_of_good t ht χ hχ v x hx hx1, tameAt_of_good t' ht' χ' hχ' v x hx hx1, one_mul]`. Introduce `v hv x hx show χ.loc v x * χ'.loc v x = 1`. Rewrite using `[unrAt_of_good t ht χ hχ pd hpd1 v hv x hx, unrAt_of_good t' ht' χ' hχ' pd hpd2 v hv x hx, one_mul]`. Introduce `v _`.

Take `⟨j, j1, j2, j3⟩` from `GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D`. Take `⟨e, he, -⟩` from `GlobalTheory.PlaceIdem.exists_isPlIdem D j j1 j2 j3 v`. Establish `hee : e * e = e` using `he.1`. Take `⟨y, hy⟩` from `RingHom.mem_fieldRange.1 (hval (Formalism.L2.JoinChr.locU hee (Formalism.L2.Host.unif v)))`. Use `⟨y, ?_⟩` and prove the remaining obligations.

Rewrite using `[hy, hc.2 v e he (Formalism.L2.Host.unif v) _ (Formalism.L2.JoinChr.locU_val hee _)]`. Simplify using `[Formalism.L2.Host.HChar.valTw, Formalism.L2.Host.HChar.val]`.
-/
theorem isTwist_mul : ∀ (D : D7) (t t' : Twist D Circle), t.Good → t'.Good → SplitSet (t.Q ∪ t'.Q) → Disjoint t.Q t'.Q →
    ∀ (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ), (∃ n : ℕ, 0 < n ∧ ∀ x, (t.chi * t'.chi) x ^ n = 1) →
    (∀ PP ∈ t.Q ∪ t'.Q, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ x, (((t.chi * t'.chi) x : Circle) : ℂ) ∈ σ.fieldRange) →
    ∃ δ : Formalism.L2.Host.HChar D.host.E, IsTwist pd σ δ (t.chi * t'.chi) := by
  intro D t t' ht ht' _ _ pd k _ σ hn hpd hval
  obtain ⟨χ, hχ⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D t.chi ht.isHeckeChar
  obtain ⟨χ', hχ'⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D t'.chi ht'.isHeckeChar
  have hc : ChrEq (t.chi * t'.chi) (χ * χ') := GlobalTheory.TowerCharRead.chrEq_mul hχ hχ'
  have hpd1 : ∀ PP ∈ t.Q, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP h => hpd PP (Finset.mem_union_left _ h)
  have hpd2 : ∀ PP ∈ t'.Q, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP h => hpd PP (Finset.mem_union_right _ h)
  refine ⟨χ * χ', hc, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨n, hn0, hnx⟩ := hn
    refine ⟨n, hn0, ?_⟩
    have hp := chrEq_pow hc n hn0
    have h1 : (t.chi * t'.chi) ^ n = 1 := MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, hnx x, MonoidHom.one_apply]
    rw [h1] at hp
    exact GlobalTheory.ChrEqUnique.hchar_unique D 1 _ _ hp chrEq_one_one
  · exact GlobalTheory.T.heckeCharacter_trivialOnSubfield_of_idelicReading D _ _ hc fun a => by rw [MonoidHom.mul_apply, ht.real, ht'.real, one_mul]
  · intro v x hx hx1
    show χ.loc v x * χ'.loc v x = 1
    rw [tameAt_of_good t ht χ hχ v x hx hx1, tameAt_of_good t' ht' χ' hχ' v x hx hx1, one_mul]
  · intro v hv x hx
    show χ.loc v x * χ'.loc v x = 1
    rw [unrAt_of_good t ht χ hχ pd hpd1 v hv x hx, unrAt_of_good t' ht' χ' hχ' pd hpd2 v hv x hx, one_mul]
  · intro v _
    obtain ⟨j, j1, j2, j3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
    obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D j j1 j2 j3 v
    have hee : e * e = e := he.1
    obtain ⟨y, hy⟩ := RingHom.mem_fieldRange.1 (hval (Formalism.L2.JoinChr.locU hee (Formalism.L2.Host.unif v)))
    refine ⟨y, ?_⟩
    rw [hy, hc.2 v e he (Formalism.L2.Host.unif v) _ (Formalism.L2.JoinChr.locU_val hee _)]
    simp [Formalism.L2.Host.HChar.valTw, Formalism.L2.Host.HChar.val]

end GlobalTheory.TwistProduct
