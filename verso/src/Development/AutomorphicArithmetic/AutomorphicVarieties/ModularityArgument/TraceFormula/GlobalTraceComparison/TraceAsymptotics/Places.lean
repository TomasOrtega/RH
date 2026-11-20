import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitAtIffCPlNeAndCPlCPl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDegreeOneAvoiding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimePlacesSplit

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Distinguish the cases in `hs : IsSplitAt w`. Conclude with `(GlobalTheory.SplitPts.over_split hs).2.2 u h`. Assume the negation of the conclusion as `hc`. Conclude with `hs ⟨u, fun e => hc (Or.inl e), h⟩`.
-/
private theorem eq_or_eq_cPl (w u : Pl E)
    (h : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) : u = w ∨ u = cPl w := by
  by_cases hs : IsSplitAt w
  · exact (GlobalTheory.SplitPts.over_split hs).2.2 u h
  · by_contra hc
    exact hs ⟨u, fun e => hc (Or.inl e), h⟩

/- English proof (translation)
Set `s : Setoid (Pl E)` to `Setoid.ker fun w : Pl E => w.under (𝓞 (maximalRealSubfield E))`. Use `⟨Set.range fun q : Quotient s => q.out, fun w => ⟨(Quotient.mk s w).out, ⟨⟨_, rfl⟩, ?_⟩, ?_⟩⟩` and prove the remaining obligations. Conclude with `Quotient.mk_out (s := s) w`. Introduce and unpack `u ⟨⟨q, rfl⟩, h⟩`. Establish `hq : q = Quotient.mk s w` using `by conv_lhs => rw [← Quotient.out_eq q]`.

Conclude with `Quotient.sound h`. Rewrite using `[hq]`.
-/
private theorem exists_section : ∃ S : Set (Pl E), IsSection S := by
  let s : Setoid (Pl E) := Setoid.ker fun w : Pl E => w.under (𝓞 (maximalRealSubfield E))
  refine ⟨Set.range fun q : Quotient s => q.out, fun w => ⟨(Quotient.mk s w).out, ⟨⟨_, rfl⟩, ?_⟩, ?_⟩⟩
  · exact Quotient.mk_out (s := s) w
  · rintro u ⟨⟨q, rfl⟩, h⟩
    have hq : q = Quotient.mk s w := by
      conv_lhs => rw [← Quotient.out_eq q]
      exact Quotient.sound h
    rw [hq]

/- English proof (translation)
Introduce `hfin`. Take `⟨m, hm⟩` from `(hfin.image fun w : Pl E => Ideal.absNorm w.asIdeal).bddAbove`. Take `⟨p, hp, hmp, hs⟩` from `GlobalTheory.LargeSplitPrime.exists_splitsCompl E m`. Use `haveI hPmax : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible`. Establish `hinj : Function.Injective (algebraMap ℤ (𝓞 E))` using `(algebraMap ℤ (𝓞 E)).injective_int`.

Take `⟨Q, hQmax, hQ⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) (Ideal.span {(p : ℤ)}) (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)`. Establish `hpQ : (p : 𝓞 E) ∈ Q`. Establish `: (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E))` using `hQ ▸ Ideal.subset_span rfl`. Simplify using `using this`. Establish `hp0 : (p : 𝓞 E) ≠ 0` using `by exact_mod_cast hp.ne_zero`.

Set `w : Pl E` to `⟨Q, hQmax.isPrime, fun h => hp0 (by rw [h] at hpQ; simpa using hpQ)⟩`. Establish `hv : (p : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal` using `by show algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal`. Rewrite using `[map_natCast]`. Conclude with `hpQ`. Establish `h2 : Module.finrank (maximalRealSubfield E) E = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two _ _`.

Establish `hsplit : IsSplitAt w`. Take `⟨a, b, hab, ha, hb⟩` from `GlobalTheory.SplitPlace.isSplit_of_norm h2 hp (fun u hu => hs u.asIdeal u.isMaximal hu) _ hv`. Distinguish the cases in `h : a = w`. Conclude with `⟨b, fun e => hab (h.trans e.symm), HeightOneSpectrum.ext hb⟩`. Conclude with `⟨a, h, HeightOneSpectrum.ext ha⟩`.

Establish `hN : Ideal.absNorm w.asIdeal = p` using `(hs w.asIdeal w.isMaximal hpQ).1`. Establish `hle : Ideal.absNorm w.asIdeal ≤ m` using `hm ⟨w, hsplit, rfl⟩`. Use linear arithmetic over natural numbers and integers.
-/
private theorem infinite_split : {w : Pl E | IsSplitAt w}.Infinite := by
  intro hfin
  obtain ⟨m, hm⟩ := (hfin.image fun w : Pl E => Ideal.absNorm w.asIdeal).bddAbove
  obtain ⟨p, hp, hmp, hs⟩ := GlobalTheory.LargeSplitPrime.exists_splitsCompl E m
  haveI hPmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hinj : Function.Injective (algebraMap ℤ (𝓞 E)) := (algebraMap ℤ (𝓞 E)).injective_int
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E)
    (Ideal.span {(p : ℤ)}) (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  have hpQ : (p : 𝓞 E) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := hQ ▸ Ideal.subset_span rfl
    simpa using this
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  let w : Pl E := ⟨Q, hQmax.isPrime, fun h => hp0 (by rw [h] at hpQ; simpa using hpQ)⟩
  have hv : (p : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal := by
    show algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal
    rw [map_natCast]
    exact hpQ
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hsplit : IsSplitAt w := by
    obtain ⟨a, b, hab, ha, hb⟩ :=
      GlobalTheory.SplitPlace.isSplit_of_norm h2 hp (fun u hu => hs u.asIdeal u.isMaximal hu) _ hv
    by_cases h : a = w
    · exact ⟨b, fun e => hab (h.trans e.symm), HeightOneSpectrum.ext hb⟩
    · exact ⟨a, h, HeightOneSpectrum.ext ha⟩
  have hN : Ideal.absNorm w.asIdeal = p := (hs w.asIdeal w.isMaximal hpQ).1
  have hle : Ideal.absNorm w.asIdeal ≤ m := hm ⟨w, hsplit, rfl⟩
  omega

/- English proof (translation)
Introduce `E _ _ _`. Use `⟨exists_section, fun w => ?_, infinite_split, fun S hS w => ⟨?_, fun h₁ h₂ => ?_⟩⟩` and prove the remaining obligations. Take `⟨h₁, h₂⟩` from `GlobalTheory.EulerTw.isSplitAt_iff_cPl_ne_and_cPl_cPl E w`. Conclude with `⟨h₂, h₁⟩`. Take `⟨u, ⟨hu, hw⟩, -⟩` from `hS w`.

Break down `eq_or_eq_cPl w u hw with rfl | rfl` into its components or cases. Conclude with `Or.inl hu`. Conclude with `Or.inr hu`. Conclude with `(hS w).unique ⟨h₂, GlobalTheory.LocInj.under_conjSrc w⟩ ⟨h₁, rfl⟩`.
-/
theorem places : Places := by
  intro E _ _ _
  refine ⟨exists_section, fun w => ?_, infinite_split, fun S hS w => ⟨?_, fun h₁ h₂ => ?_⟩⟩
  · obtain ⟨h₁, h₂⟩ := GlobalTheory.EulerTw.isSplitAt_iff_cPl_ne_and_cPl_cPl E w
    exact ⟨h₂, h₁⟩
  · obtain ⟨u, ⟨hu, hw⟩, -⟩ := hS w
    rcases eq_or_eq_cPl w u hw with rfl | rfl
    · exact Or.inl hu
    · exact Or.inr hu
  · exact (hS w).unique ⟨h₂, GlobalTheory.LocInj.under_conjSrc w⟩ ⟨h₁, rfl⟩

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
