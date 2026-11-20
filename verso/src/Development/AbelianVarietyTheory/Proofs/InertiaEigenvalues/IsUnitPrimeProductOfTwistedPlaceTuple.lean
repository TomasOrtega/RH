import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitCardResidueFieldOffExceptionalPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceUnit

/- English proof (translation)
Use `haveI : Finite (kP P) := P.asIdeal.finiteQuotientOfFreeOfNeBot P.ne_bot`. Conclude with `Nat.card_pos.ne'`.
-/
theorem card_residueField_ne_zero {E : Type} [Field E] [NumberField E] (P : Pl E) : Nat.card (kP P) ≠ 0 := by
  haveI : Finite (kP P) := P.asIdeal.finiteQuotientOfFreeOfNeBot P.ne_bot
  exact Nat.card_pos.ne'

/- English proof (translation)
Use `haveI : Finite (kP P) := P.asIdeal.finiteQuotientOfFreeOfNeBot P.ne_bot`. Use `letI : Fintype (kP P) := Fintype.ofFinite _`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast, Nat.card_eq_fintype_card]`. Conclude with `Nat.cast_card_eq_zero (kP P)`.
-/
theorem card_residueField_mem {E : Type} [Field E] [NumberField E] (P : Pl E) : ((Nat.card (kP P) : ℕ) : 𝓞 E) ∈ P.asIdeal := by
  haveI : Finite (kP P) := P.asIdeal.finiteQuotientOfFreeOfNeBot P.ne_bot
  letI : Fintype (kP P) := Fintype.ofFinite _
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, Nat.card_eq_fintype_card]
  exact Nat.cast_card_eq_zero (kP P)

/- English proof (translation)
Introduce `hl`. Take `⟨a, b, hab⟩` from `Nat.isCoprime_iff_coprime.2 h`. Apply `P.isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `h1 : ((a : 𝓞 E) * ((q : ℕ) : 𝓞 E) + (b : 𝓞 E) * ((l : ℕ) : 𝓞 E)) = 1`.

Use `congrArg (Int.cast : ℤ → 𝓞 E) hab` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Rewrite using `[← h1]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hq) (Ideal.mul_mem_left _ _ hl)`.
-/
theorem not_mem_of_coprime {E : Type} [Field E] [NumberField E] (P : Pl E) {q l : ℕ} (h : Nat.Coprime q l)
    (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) : ((l : ℕ) : 𝓞 E) ∉ P.asIdeal := by
  intro hl
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  apply P.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : ((a : 𝓞 E) * ((q : ℕ) : 𝓞 E) + (b : 𝓞 E) * ((l : ℕ) : 𝓞 E)) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 E) hab
    push_cast at this
    exact this
  rw [← h1]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hq) (Ideal.mul_mem_left _ _ hl)

/- English proof (translation)
Establish `h : P ∈ placesOver D.host.E (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde)`. Rewrite using `[← D.ntw.pD_eq i]`. Conclude with `hP`. Establish `hl : (D.ntw.l i).Prime` using `(D.ntw.lPrime i).out`. Use `not_mem_of_coprime P ?_ h` and prove the remaining obligations.

Use `split_ifs with e`. Conclude with `(Nat.coprime_primes D.host.pde'_prime hl).2 (e ▸ D.host.pde_ne.symm)`. Conclude with `(Nat.coprime_primes D.host.pde_prime hl).2 (Ne.symm e)`.
-/
theorem not_mem_of_pD {D : D7} (i : D.ntw.Tw) {P : Pl D.host.E} (hP : P ∈ D.ntw.pD i) :
    ((D.ntw.l i : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  have h : P ∈ placesOver D.host.E (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← D.ntw.pD_eq i]; exact hP
  have hl : (D.ntw.l i).Prime := (D.ntw.lPrime i).out
  refine not_mem_of_coprime P ?_ h
  split_ifs with e
  · exact (Nat.coprime_primes D.host.pde'_prime hl).2 (e ▸ D.host.pde_ne.symm)
  · exact (Nat.coprime_primes D.host.pde_prime hl).2 (Ne.symm e)

/- English proof (translation)
Use `haveI := D.ntw.Ok_fin (c.twI w) (c.k' w)`. Establish `h : IsUnit ((Nat.card (kP P) : ℕ) : D.ntw.Ok (c.twI w) (c.k' w))` using `GlobalTheory.ResidueUnit.isUnit_of_coprime _ _ (GlobalTheory.ResidueUnit.card_residueField_coprime P _ (D.ntw.lPrime _).out hl) (GlobalTheory.ResidueUnit.natCast_mem_maximalIdeal_of_finite (O := D.ntw.O (c.twI w)) _ (D.ntw.O_l _))`. Simplify using `using h.map (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w))`.
-/
theorem isUnit_card_residueField_Oe {D : D7} (c : NChoice D) (w : D.what₂.places.Pl) {P : Pl D.host.E}
    (hl : ((D.ntw.l (c.twI w) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) : IsUnit ((Nat.card (kP P) : ℕ) : c.Oe w) := by
  haveI := D.ntw.Ok_fin (c.twI w) (c.k' w)
  have h : IsUnit ((Nat.card (kP P) : ℕ) : D.ntw.Ok (c.twI w) (c.k' w)) :=
    GlobalTheory.ResidueUnit.isUnit_of_coprime _ _ (GlobalTheory.ResidueUnit.card_residueField_coprime P _ (D.ntw.lPrime _).out hl)
      (GlobalTheory.ResidueUnit.natCast_mem_maximalIdeal_of_finite (O := D.ntw.O (c.twI w)) _ (D.ntw.O_l _))
  simpa using h.map (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w))

/- English proof (translation)
Introduce `D X X0 Y S YS Z c w j H ι hι`. Establish `hQ` using `(H.tup ι hι).2`. Use `⟨?_, fun P hP => ?_, ?_⟩` and prove the remaining obligations. Use `Finset.prod_ne_zero_iff.2 fun q hq => ?_` and prove the remaining obligations. Take `⟨P, -, rfl⟩` from `Finset.mem_image.1 hq`.

Conclude with `card_residueField_ne_zero P`. Take `⟨m, hm⟩ : Nat.card (kP P) ∣ GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w))` from `Finset.dvd_prod_of_mem (fun q : ℕ => q) (Finset.mem_image_of_mem (fun PP => Nat.card (kP PP)) hP)`. Rewrite using `[hm, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ (card_residueField_mem P)`. Rewrite using `[GlobalTheory.TwistField.tupPrime, Nat.cast_prod]`.

Use `IsUnit.prod_iff.2 fun q hq => ?_` and prove the remaining obligations. Take `⟨P, hP, rfl⟩` from `Finset.mem_image.1 hq`. Use `isUnit_card_residueField_Oe c w ?_` and prove the remaining obligations. Rewrite `hP` using `[hQ, Finset.mem_union]`. Break down `hP with hP | hP` into its components or cases.

Rewrite `hP` using `[Z.good.delta]`. Conclude with `not_mem_of_pD _ (mem_half.1 hP).1`. Conclude with `fun h => Finset.disjoint_left.1 H.ok.2.1 (mem_half.1 hP).1 (D.ntw.twistExcludedPlaces_contains_residueChar _ h)`.
-/
theorem tupPrime_isUnit : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) ≠ 0 ∧ (∀ P ∈ X.R.Q (Y.tupT (D.what₂.muTw w)), ((GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) ∧
  IsUnit ((GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) : ℕ) : c.Oe w) := by
  classical
  intro D X X0 Y S YS Z c w j H ι hι
  have hQ := (H.tup ι hι).2
  refine ⟨?_, fun P hP => ?_, ?_⟩
  · refine Finset.prod_ne_zero_iff.2 fun q hq => ?_
    obtain ⟨P, -, rfl⟩ := Finset.mem_image.1 hq
    exact card_residueField_ne_zero P
  · obtain ⟨m, hm⟩ : Nat.card (kP P) ∣ GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) :=
      Finset.dvd_prod_of_mem (fun q : ℕ => q) (Finset.mem_image_of_mem (fun PP => Nat.card (kP PP)) hP)
    rw [hm, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (card_residueField_mem P)
  · rw [GlobalTheory.TwistField.tupPrime, Nat.cast_prod]
    refine IsUnit.prod_iff.2 fun q hq => ?_
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
    refine isUnit_card_residueField_Oe c w ?_
    rw [hQ, Finset.mem_union] at hP
    rcases hP with hP | hP
    · rw [Z.good.delta] at hP
      exact not_mem_of_pD _ (mem_half.1 hP).1
    · exact fun h => Finset.disjoint_left.1 H.ok.2.1 (mem_half.1 hP).1 (D.ntw.twistExcludedPlaces_contains_residueChar _ h)

end GlobalTheory.PlaceUnit
