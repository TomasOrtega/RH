import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMtCutPartCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open scoped TensorProduct

namespace GlobalTheory.TameCharProd

open Formalism.L2.Host

/- English proof (translation)
Establish `hk0 : P.valuation L (k : L) ≠ 0` using `(Valuation.ne_zero_iff _).2 k.ne_zero`. Establish `hak : ((atFin P k : (P.adicCompletion L)ˣ) : P.adicCompletion L) = algebraMap L _ (k : L)` using `rfl`. Establish `hK0 : algebraMap L (P.adicCompletion L) (k : L) ≠ 0` using `(map_ne_zero _).2 k.ne_zero`. Establish `hval : Valued.v (algebraMap L (P.adicCompletion L) (k : L)) = P.valuation L (k : L)` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P (k : L)`. Use `set u : (P.adicCompletion L)ˣ := a * (atFin P k)⁻¹ with hu_def`.

Establish `hu : IsUnitAt P u`. Unfold `IsUnitAt`. Rewrite using `[hu_def, Units.val_mul, Units.val_inv_eq_inv_val, hak, map_mul, map_inv₀, hval, h1, mul_inv_cancel₀ hk0]`. Establish `hu1 : Valued.v ((u : P.adicCompletion L) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ))`. Establish `e : (u : P.adicCompletion L) - 1 = ((a : P.adicCompletion L) - algebraMap L _ (k : L)) * (algebraMap L (P.adicCompletion L) (k : L))⁻¹`.

Rewrite using `[hu_def, Units.val_mul, Units.val_inv_eq_inv_val, hak, sub_mul, mul_inv_cancel₀ hK0]`. Rewrite using `[e, map_mul, map_inv₀, hval, Nat.cast_one]`. Combine the equalities or inequalities in the displayed calculation. Establish `hχ` using `hP u hu hu1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem loc_eq_locK_of_tame {L : Type} [Field L] [NumberField L] (χ : HChar L) (P : HeightOneSpectrum (𝓞 L))
    (hP : χ.TameAt P) (a : (P.adicCompletion L)ˣ) (k : Lˣ)
    (h1 : Valued.v (a : P.adicCompletion L) = P.valuation L (k : L))
    (h2 : Valued.v ((a : P.adicCompletion L) - algebraMap L _ (k : L)) ≤ WithZero.exp (-1 : ℤ) * P.valuation L (k : L)) :
    χ.loc P a = χ.locK P k := by
  have hk0 : P.valuation L (k : L) ≠ 0 := (Valuation.ne_zero_iff _).2 k.ne_zero
  have hak : ((atFin P k : (P.adicCompletion L)ˣ) : P.adicCompletion L) = algebraMap L _ (k : L) := rfl
  have hK0 : algebraMap L (P.adicCompletion L) (k : L) ≠ 0 := (map_ne_zero _).2 k.ne_zero
  have hval : Valued.v (algebraMap L (P.adicCompletion L) (k : L)) = P.valuation L (k : L) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P (k : L)
  set u : (P.adicCompletion L)ˣ := a * (atFin P k)⁻¹ with hu_def
  have hu : IsUnitAt P u := by
    unfold IsUnitAt
    rw [hu_def, Units.val_mul, Units.val_inv_eq_inv_val, hak, map_mul, map_inv₀, hval, h1, mul_inv_cancel₀ hk0]
  have hu1 : Valued.v ((u : P.adicCompletion L) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    have e : (u : P.adicCompletion L) - 1 = ((a : P.adicCompletion L) - algebraMap L _ (k : L)) *
        (algebraMap L (P.adicCompletion L) (k : L))⁻¹ := by
      rw [hu_def, Units.val_mul, Units.val_inv_eq_inv_val, hak, sub_mul, mul_inv_cancel₀ hK0]
    rw [e, map_mul, map_inv₀, hval, Nat.cast_one]
    calc Valued.v ((a : P.adicCompletion L) - algebraMap L _ (k : L)) * (P.valuation L (k : L))⁻¹
        ≤ WithZero.exp (-1 : ℤ) * P.valuation L (k : L) * (P.valuation L (k : L))⁻¹ := by gcongr
      _ = WithZero.exp (-1 : ℤ) := by rw [mul_assoc, mul_inv_cancel₀ hk0, mul_one]
  have hχ := hP u hu hu1
  calc χ.loc P a = χ.loc P (u * atFin P k) := by rw [hu_def, inv_mul_cancel_right]
    _ = χ.locK P k := by rw [map_mul, hχ, one_mul]; rfl

end GlobalTheory.TameCharProd

namespace GlobalTheory.TameCharProd

/- English proof (translation)
Introduce `D c χ hc T hT a x hx hT1 hT0`. Establish `hsp` using `GlobalTheory.StdFrames.toAd_spec D`. Set `sw` to `Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E`. Set `φ : (Af D.host.F ⊗[D.host.F] D.host.E) →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E` to `(GlobalTheory.StdFrames.toAd D).comp sw.toRingEquiv.toRingHom`. Establish `hbij : Function.Bijective φ` using `⟨(GlobalTheory.AdeleBaseChange.map_injective hsp).comp sw.injective, (GlobalTheory.AdeleBaseChange.map_surjective hsp).comp sw.surjective⟩`.

Set `ι` to `RingEquiv.ofBijective φ hbij`. Establish `hxP : ∀ P, ι (finPart D (x : AE D)) P = GlobalTheory.StdFrames.cpt P (toEAf D (x : AE D))` using `fun P => rfl`. Establish `hι : ∀ y : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] y) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) y`. Introduce `y`. Use `show GlobalTheory.StdFrames.toAd D (sw ((1 : Af D.host.F) ⊗ₜ[D.host.F] y)) = _`.

Rewrite using `[Algebra.TensorProduct.comm_tmul]`. Conclude with `GlobalTheory.AdeleBaseChange.map_tmul_one hsp y`. Establish `hint : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1`. Introduce `y`. Rewrite using `[GlobalTheory.HostAdeleIso.mem_intAE_iff_comm]`.

Prove the components needed by the constructor for the conclusion. Introduce `h P`. Establish `h'` using `GlobalTheory.AdeleBaseChange.map_mem_int hsp h`. Conclude with `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h' P)`. Introduce `h`.

Conclude with `GlobalTheory.AdeleBaseChange.mem_int_of_map hsp fun P => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h P)`. Establish `hidem : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, Formalism.L2.JoinChr.IsPlIdem D e P ∧ infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0`. Introduce `P`. Take `⟨ι₀, h1, h2, h3⟩` from `GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D`. Take `⟨e, he, -⟩` from `GlobalTheory.PlaceIdem.exists_isPlIdem D ι₀ h1 h2 h3 P`.

Conclude with `⟨e, he, GlobalTheory.HeckeTensorRead.isPlIdem_parts D ι hι hint he⟩`. Take `⟨N, hN, hmain⟩` from `GlobalTheory.CharLocProd.char_eq_prod_locK D ι hι hint hidem c χ hc`. Establish `hk : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ k : D.host.Eˣ, (P ∈ T → Valued.v ((a P : Kw P) : P.adicCompletion D.host.E) = P.valuation D.host.E (k : D.host.E) ∧ Valued.v ((a P : P.adicCompletion D.host.E) - algebraMap D.host.E _ (k : D.host.E)) ≤ P.valuation D.host.E (N : D.host. …`. Introduce `P`. Distinguish the cases in `hP : P ∈ T`.

Take `⟨k, h1, h2, h3⟩` from `GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN P (a P : P.adicCompletion D.host.E) (a P).ne_zero`. Conclude with `⟨k, fun _ => ⟨h1, h2, h3⟩, fun h => absurd hP h⟩`. Conclude with `⟨1, fun h => absurd h hP, fun _ => rfl⟩`. Use `choose k hkT hk1 using hk`. Establish `hfin : {P : HeightOneSpectrum (𝓞 D.host.E) | (N : 𝓞 D.host.E) ∈ P.asIdeal}.Finite`.

Establish `hN0 : (N : 𝓞 D.host.E) ≠ 0` using `by exact_mod_cast hN.ne'`. Use `(Ideal.finite_factors (I := Ideal.span {(N : 𝓞 D.host.E)}) (by simpa [Ideal.span_singleton_eq_bot] using hN0)).subset ?_` and prove the remaining obligations. Introduce `P hP`. Conclude with `Ideal.dvd_span_singleton.2 hP`. Establish `hTS : T ⊆ T ∪ hfin.toFinset` using `Finset.subset_union_left`.

Establish `key` using `hmain x hx (T ∪ hfin.toFinset) k (fun P _ => by`. Distinguish the cases in `hP : P ∈ T`. Rewrite using `[hxP, hT1 P hP]`. Conclude with `⟨(hkT P hP).1, (hkT P hP).2.1⟩`. Rewrite using `[hxP, hT0 P hP, hk1 P hP] simp) (fun P hP => by`.

Simplify using `only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or] at hP`. Rewrite using `[hxP, hT0 P hP.1]`. Conclude with `⟨map_one _, hP.2⟩)`. Rewrite using `[key, ← Finset.prod_subset hTS (fun P _ hP => by rw [hk1 P hP, map_one, Units.val_one])]`. Use `Finset.prod_congr rfl fun P hP => ?_` and prove the remaining obligations.

Rewrite using `[loc_eq_locK_of_tame χ P (hT P hP) (a P) (k P) (hkT P hP).1 (hkT P hP).2.2]`.
-/
theorem char_eq_prod_loc_of_tame : ∀ {D : D7} {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E}, ChrEq c χ → ∀ (T : Finset (Pl D.host.E)), (∀ P ∈ T, χ.TameAt P) → ∀ (a : ∀ P : Pl D.host.E, (Kw P)ˣ) (x : (AE D)ˣ), infPart D (x : AE D) = 1 → (∀ P ∈ T, GlobalTheory.StdFrames.cpt P (toEAf D (x : AE D)) = (a P : Kw P)) → (∀ P ∉ T, GlobalTheory.StdFrames.cpt P (toEAf D (x : AE D)) = 1) → ((c x : Circle) : ℂ) = ∏ P ∈ T, ((χ.loc P (a P) : ℂˣ) : ℂ) := by
  intro D c χ hc T hT a x hx hT1 hT0
  classical
  have hsp := GlobalTheory.StdFrames.toAd_spec D
  let sw := Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E
  let φ : (Af D.host.F ⊗[D.host.F] D.host.E) →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    (GlobalTheory.StdFrames.toAd D).comp sw.toRingEquiv.toRingHom
  have hbij : Function.Bijective φ :=
    ⟨(GlobalTheory.AdeleBaseChange.map_injective hsp).comp sw.injective,
      (GlobalTheory.AdeleBaseChange.map_surjective hsp).comp sw.surjective⟩
  let ι := RingEquiv.ofBijective φ hbij
  have hxP : ∀ P, ι (finPart D (x : AE D)) P = GlobalTheory.StdFrames.cpt P (toEAf D (x : AE D)) := fun P => rfl
  have hι : ∀ y : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] y) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) y := by
    intro y
    show GlobalTheory.StdFrames.toAd D (sw ((1 : Af D.host.F) ⊗ₜ[D.host.F] y)) = _
    rw [Algebra.TensorProduct.comm_tmul]
    exact GlobalTheory.AdeleBaseChange.map_tmul_one hsp y
  have hint : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1 := by
    intro y
    rw [GlobalTheory.HostAdeleIso.mem_intAE_iff_comm]
    constructor
    · intro h P
      have h' := GlobalTheory.AdeleBaseChange.map_mem_int hsp h
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h' P)
    · intro h
      exact GlobalTheory.AdeleBaseChange.mem_int_of_map hsp fun P =>
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h P)
  have hidem : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, Formalism.L2.JoinChr.IsPlIdem D e P ∧ infPart D e = 0 ∧
      ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0 := by
    intro P
    obtain ⟨ι₀, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
    obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι₀ h1 h2 h3 P
    exact ⟨e, he, GlobalTheory.HeckeTensorRead.isPlIdem_parts D ι hι hint he⟩
  obtain ⟨N, hN, hmain⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι hι hint hidem c χ hc
  have hk : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ k : D.host.Eˣ,
      (P ∈ T → Valued.v ((a P : Kw P) : P.adicCompletion D.host.E) = P.valuation D.host.E (k : D.host.E) ∧
        Valued.v ((a P : P.adicCompletion D.host.E) - algebraMap D.host.E _ (k : D.host.E)) ≤
          P.valuation D.host.E (N : D.host.E) * P.valuation D.host.E (k : D.host.E) ∧
        Valued.v ((a P : P.adicCompletion D.host.E) - algebraMap D.host.E _ (k : D.host.E)) ≤
          WithZero.exp (-1 : ℤ) * P.valuation D.host.E (k : D.host.E)) ∧ (P ∉ T → k = 1) := by
    intro P
    by_cases hP : P ∈ T
    · obtain ⟨k, h1, h2, h3⟩ :=
        GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN P (a P : P.adicCompletion D.host.E) (a P).ne_zero
      exact ⟨k, fun _ => ⟨h1, h2, h3⟩, fun h => absurd hP h⟩
    · exact ⟨1, fun h => absurd h hP, fun _ => rfl⟩
  choose k hkT hk1 using hk
  have hfin : {P : HeightOneSpectrum (𝓞 D.host.E) | (N : 𝓞 D.host.E) ∈ P.asIdeal}.Finite := by
    have hN0 : (N : 𝓞 D.host.E) ≠ 0 := by exact_mod_cast hN.ne'
    refine (Ideal.finite_factors (I := Ideal.span {(N : 𝓞 D.host.E)})
      (by simpa [Ideal.span_singleton_eq_bot] using hN0)).subset ?_
    intro P hP
    exact Ideal.dvd_span_singleton.2 hP
  have hTS : T ⊆ T ∪ hfin.toFinset := Finset.subset_union_left
  have key := hmain x hx (T ∪ hfin.toFinset) k (fun P _ => by
      by_cases hP : P ∈ T
      · rw [hxP, hT1 P hP]
        exact ⟨(hkT P hP).1, (hkT P hP).2.1⟩
      · rw [hxP, hT0 P hP, hk1 P hP]
        simp) (fun P hP => by
      simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or] at hP
      rw [hxP, hT0 P hP.1]
      exact ⟨map_one _, hP.2⟩)
  rw [key, ← Finset.prod_subset hTS (fun P _ hP => by rw [hk1 P hP, map_one, Units.val_one])]
  refine Finset.prod_congr rfl fun P hP => ?_
  rw [loc_eq_locK_of_tame χ P (hT P hP) (a P) (k P) (hkT P hP).1 (hkT P hP).2.2]

end GlobalTheory.TameCharProd
