import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorNefAmpleFiniteFieldFibreStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelAmpleNearFibreFlatProjective
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAmpleLBOfFibres
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticVarietyGenericFibre
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
open Limits

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AmpleNefFibZ

/- English proof (translation)
Take `⟨M, hM, hPM⟩` from `Ideal.exists_le_maximal P (Ideal.IsPrime.ne_top ‹_›)`. Use `set m := Submodule.IsPrincipal.generator M`. Establish `hmM : Ideal.span {m} = M` using `Submodule.IsPrincipal.span_singleton_generator M`. Establish `hm0 : m ≠ 0`. Introduce and unpack `h`.

Use `Ideal.bot_lt_of_maximal M Int.not_isField` as an intermediate fact. Rewrite `this` using `[← hmM, h, Ideal.span_singleton_eq_bot.2 rfl]`. Conclude with `lt_irrefl _ this`. Establish `hmp : Prime m` using `(Ideal.span_singleton_prime hm0).1 (hmM ▸ hM.isPrime)`. Use `⟨m.natAbs, Int.prime_iff_natAbs_prime.1 hmp, fun r hr hrP => hr ?_⟩` and prove the remaining obligations.

Rewrite using `[Ideal.mem_span_singleton, Int.natAbs_dvd]`. Rewrite using `[← Ideal.mem_span_singleton, hmM]`. Conclude with `hPM hrP`.
-/
theorem exists_prime_le (P : Ideal ℤ) [P.IsPrime] :
    ∃ l : ℕ, l.Prime ∧ ∀ r : ℤ, r ∉ Ideal.span {(l : ℤ)} → r ∉ P := by
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P (Ideal.IsPrime.ne_top ‹_›)
  set m := Submodule.IsPrincipal.generator M
  have hmM : Ideal.span {m} = M := Submodule.IsPrincipal.span_singleton_generator M
  have hm0 : m ≠ 0 := by
    rintro h
    have := Ideal.bot_lt_of_maximal M Int.not_isField
    rw [← hmM, h, Ideal.span_singleton_eq_bot.2 rfl] at this
    exact lt_irrefl _ this
  have hmp : Prime m := (Ideal.span_singleton_prime hm0).1 (hmM ▸ hM.isPrime)
  refine ⟨m.natAbs, Int.prime_iff_natAbs_prime.1 hmp, fun r hr hrP => hr ?_⟩
  rw [Ideal.mem_span_singleton, Int.natAbs_dvd]
  rw [← Ideal.mem_span_singleton, hmM]
  exact hPM hrP

/- English proof (translation)
Introduce `k _ X _ p D hX L A hL hA`. Use `haveI : Module.Finite ℤ k := hX.finite`. Use `set s : X ⟶ Sp ℤ := p ≫ spMap (Int.castRingHom k) with hs_def`. Establish `hsZ : s = ShFam.Pad.toSpZ X` using `specZIsTerminal.hom_ext _ _`. Establish `hP : IsProjOver s` using `hsZ ▸ ShFam.Pad.isProjOver_toSpZ hX.isProjOver`.

Establish `hPB : AbLaw.IsProjBy s` using `(ProjSpace.isProjBy_iff_isProjOver s).2 hP`. Use `haveI : IsProper s := hsZ ▸ FibreProj.isProper_of_isArithVar (ShFam.Pad.isArithVar_toSpZ hX)`. Establish `hM : (L.tens A).B.IsLB` using `(L.tens A).isLB`. Use `haveI : IsProper (Over.mk s).hom := ‹IsProper s›`. Use `(relAmple_iff_isAmpleLB_of_isAffine (Over.mk s) hM).1 ?_` and prove the remaining obligations.

Use `AmpleLocal.relAmple_of_locally _ (Over.mk s) _ hM inferInstance inferInstance fun P => ?_` and prove the remaining obligations. Take `⟨l, hl, hlP⟩` from `@exists_prime_le P.asIdeal P.isPrime`. Use `haveI : Fact l.Prime := ⟨hl⟩`. Establish `F` using `GlobalTheory.T.isAmple_tensor_nef_ample_finiteFieldFibre k X p D hX L A hL hA l`. Establish `hFib : Out.RelAmple ((Over.pullback (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod l))))).obj (Over.mk s)) ((L.tens A).B.pull (pullback.fst s (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod l))))))` using `by haveI : IsProper ((Over.pullback (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod l))))).obj (Over.mk s)).hom := inferInstanceAs (IsProper (pullback.snd s _))`.

Conclude with `(relAmple_iff_isAmpleLB_of_isAffine _ (LB.isLB_pull hM _)).2 F`. Establish `hfrac : ∀ y : ZMod l, ∃ a b : ℤ, Int.castRingHom (ZMod l) b ≠ 0 ∧ y * Int.castRingHom (ZMod l) b = Int.castRingHom (ZMod l) a` using `fun y => ⟨(y.val : ℤ), 1, by simp, by simp⟩`. Take `⟨r, hr, hA'⟩` from `AmpleNear.relAmple_near_fibre ℤ (Over.mk s) (L.tens A).B hX.flat hPB hM (ZMod l) (Int.castRingHom (ZMod l)) hfrac hFib`. Establish `hrl : r ∉ Ideal.span {(l : ℤ)}`. Rewrite using `[Ideal.mem_span_singleton]`.

Introduce `h`. Conclude with `hr ((ZMod.intCast_zmod_eq_zero_iff_dvd r l).2 h)`. Set `U : (Spec (CommRingCat.of ℤ)).Opens` to `PrimeSpectrum.basicOpen r`. Use `haveI : IsAffine U.toScheme := IsAffineOpen.Spec_basicOpen (R := CommRingCat.of ℤ) r`. Conclude with `⟨U, hlP r hrl, AmpleFibres.relAmple_restrict U (Over.mk s) hM hA'⟩`.
-/
theorem isAmpleLB_tens_of_nefFib : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L A : HermLB p, NefFib L → IsAmpleLB A.B → IsAmpleLB (L.tens A).B := by
  intro k _ X _ p D hX L A hL hA
  haveI : Module.Finite ℤ k := hX.finite
  set s : X ⟶ Sp ℤ := p ≫ spMap (Int.castRingHom k) with hs_def
  have hsZ : s = ShFam.Pad.toSpZ X := specZIsTerminal.hom_ext _ _
  have hP : IsProjOver s := hsZ ▸ ShFam.Pad.isProjOver_toSpZ hX.isProjOver
  have hPB : AbLaw.IsProjBy s := (ProjSpace.isProjBy_iff_isProjOver s).2 hP
  haveI : IsProper s := hsZ ▸ FibreProj.isProper_of_isArithVar (ShFam.Pad.isArithVar_toSpZ hX)
  have hM : (L.tens A).B.IsLB := (L.tens A).isLB
  haveI : IsProper (Over.mk s).hom := ‹IsProper s›
  refine (relAmple_iff_isAmpleLB_of_isAffine (Over.mk s) hM).1 ?_
  refine AmpleLocal.relAmple_of_locally _ (Over.mk s) _ hM inferInstance inferInstance fun P => ?_
  obtain ⟨l, hl, hlP⟩ := @exists_prime_le P.asIdeal P.isPrime
  haveI : Fact l.Prime := ⟨hl⟩
  have F := GlobalTheory.T.isAmple_tensor_nef_ample_finiteFieldFibre k X p D hX L A hL hA l
  have hFib : Out.RelAmple ((Over.pullback (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod l))))).obj (Over.mk s))
      ((L.tens A).B.pull (pullback.fst s (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod l)))))) := by
    haveI : IsProper ((Over.pullback (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod l))))).obj (Over.mk s)).hom :=
      inferInstanceAs (IsProper (pullback.snd s _))
    exact (relAmple_iff_isAmpleLB_of_isAffine _ (LB.isLB_pull hM _)).2 F
  have hfrac : ∀ y : ZMod l, ∃ a b : ℤ, Int.castRingHom (ZMod l) b ≠ 0 ∧
      y * Int.castRingHom (ZMod l) b = Int.castRingHom (ZMod l) a :=
    fun y => ⟨(y.val : ℤ), 1, by simp, by simp⟩
  obtain ⟨r, hr, hA'⟩ := AmpleNear.relAmple_near_fibre ℤ (Over.mk s) (L.tens A).B hX.flat hPB hM (ZMod l)
    (Int.castRingHom (ZMod l)) hfrac hFib
  have hrl : r ∉ Ideal.span {(l : ℤ)} := by
    rw [Ideal.mem_span_singleton]
    intro h
    exact hr ((ZMod.intCast_zmod_eq_zero_iff_dvd r l).2 h)
  let U : (Spec (CommRingCat.of ℤ)).Opens := PrimeSpectrum.basicOpen r
  haveI : IsAffine U.toScheme := IsAffineOpen.Spec_basicOpen (R := CommRingCat.of ℤ) r
  exact ⟨U, hlP r hrl, AmpleFibres.relAmple_restrict U (Over.mk s) hM hA'⟩

end GlobalTheory.AmpleNefFibZ
