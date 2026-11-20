import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.BaseFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)
open UpperTheory.Gal UpperTheory.Gal.Mod

/- English proof (translation)
Use `haveI : y.asIdeal.IsPrime := PrimeSpectrum.isPrime y`. Use `letI : Algebra O ((Spec (CommRingCat.of O)).presheaf.stalk y) := StructureSheaf.stalkAlgebra (CommRingCat.of O) y`. Use `haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of O)).presheaf.stalk y) y.asIdeal := StructureSheaf.IsLocalization.to_stalk (CommRingCat.of O) y`. Conclude with `GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_isDomain y.asIdeal _`.
-/
private theorem nml_spec (O : Type) [CommRing O] [IsDomain O] [IsIntegrallyClosed O]
    (y : Spec (CommRingCat.of O)) :
    IsDomain ((Spec (CommRingCat.of O)).presheaf.stalk y) ∧
      IsIntegrallyClosed ((Spec (CommRingCat.of O)).presheaf.stalk y) := by
  haveI : y.asIdeal.IsPrime := PrimeSpectrum.isPrime y
  letI : Algebra O ((Spec (CommRingCat.of O)).presheaf.stalk y) :=
    StructureSheaf.stalkAlgebra (CommRingCat.of O) y
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of O)).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of O) y
  exact GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_isDomain y.asIdeal _

/- English proof (translation)
Simplify using `[fn]`.
-/
private theorem natCast_eq_fn {O : Type} [CommRing O] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of O)) (p : ℕ) :
    (p : Γ(Y, ⊤)) = fn g (p : O) := by
  simp [fn]

/- English proof (translation)
Rewrite using `[fn, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]`. Both sides reduce to the same expression.
-/
private theorem mem_basicOpen_fn {O : Type} [CommRing O] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of O)) (a : O)
    (y : Y) : y ∈ Y.basicOpen (fn g a) ↔ g y ∈ PrimeSpectrum.basicOpen a := by
  rw [fn, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  rfl

/- English proof (translation)
Set `s : Spec (CommRingCat.of O)` to `⟨⊥, Ideal.isPrime_bot⟩`. Establish `hs : s ⤳ g y` using `(PrimeSpectrum.le_iff_specializes _ _).1 bot_le`. Take `⟨η, hη, rfl'⟩` from `(Flat.generalizingMap g) hs`. Use `⟨η, ?_, hη⟩` and prove the remaining obligations. Rewrite using `[mem_basicOpen_fn, rfl']`.

Conclude with `ha`.
-/
private theorem exists_generic {O : Type} [CommRing O] [IsDomain O] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of O))
    [Flat g] (a : O) (ha : a ≠ 0) (y : Y) : ∃ η ∈ Y.basicOpen (fn g a), η ⤳ y := by
  let s : Spec (CommRingCat.of O) := ⟨⊥, Ideal.isPrime_bot⟩
  have hs : s ⤳ g y := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨η, hη, rfl'⟩ := (Flat.generalizingMap g) hs
  refine ⟨η, ?_, hη⟩
  rw [mem_basicOpen_fn, rfl']
  exact ha

/- English proof (translation)
Introduce `p O _ _ _ ϖ hϖ hp0 hpu Y g _`. Use `haveI : Flat g := inferInstance`. Use `haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g`. Establish `hbo : Y.basicOpen (p : Γ(Y, ⊤)) = Y.basicOpen (fn g (p : O))`. Rewrite using `[natCast_eq_fn g p]`.

Establish `hϖp : ϖ ∣ (p : O)`. Take `⟨n, hn⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hp0 hϖ`. Consider the cases of `n with`. Consider the case `zero => exact absurd (hn.isUnit_iff.mpr (by simp)) hpu`. Consider the case `succ n => exact (dvd_pow_self ϖ (Nat.succ_ne_zero n)).trans hn.symm.dvd`.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `TranscendenceTraces.nmlLoc_holds Y (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth g (nml_spec O)) (Or.inr inferInstance)`. Introduce `y hy`. Take `⟨η, hη, hηy⟩` from `exists_generic g (p : O) hp0 y`. Rewrite using `[hbo, ← hy η hηy]`.

Conclude with `hη`. Introduce `y`. Take `⟨η, hη, hηy⟩` from `exists_generic g (p : O) hp0 y`. Conclude with `⟨η, hbo ▸ hη, hηy⟩`. Introduce `y hy`.

Rewrite `hy` using `[hbo, mem_basicOpen_fn]`. Rewrite using `[mem_basicOpen_fn]`. Express the relevant statement in the definitionally equal form `(p : O) ∉ (g y).asIdeal at hy`. Express the relevant statement in the definitionally equal form `ϖ ∉ (g y).asIdeal`. Introduce `h`.

Take `⟨c, hc⟩` from `hϖp`. Conclude with `hy (hc ▸ Ideal.mul_mem_right c _ h)`.
-/
theorem UpperTheory.Gal.Mod.baseFacts :
    BaseFacts := by
  intro p O _ _ _ ϖ hϖ hp0 hpu Y g _
  haveI : Flat g := inferInstance
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have hbo : Y.basicOpen (p : Γ(Y, ⊤)) = Y.basicOpen (fn g (p : O)) := by
    rw [natCast_eq_fn g p]
  have hϖp : ϖ ∣ (p : O) := by
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hp0 hϖ
    cases n with
    | zero => exact absurd (hn.isUnit_iff.mpr (by simp)) hpu
    | succ n => exact (dvd_pow_self ϖ (Nat.succ_ne_zero n)).trans hn.symm.dvd
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact TranscendenceTraces.nmlLoc_holds Y
      (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth g (nml_spec O)) (Or.inr inferInstance)
  · intro y hy
    obtain ⟨η, hη, hηy⟩ := exists_generic g (p : O) hp0 y
    rw [hbo, ← hy η hηy]
    exact hη
  · intro y
    obtain ⟨η, hη, hηy⟩ := exists_generic g (p : O) hp0 y
    exact ⟨η, hbo ▸ hη, hηy⟩
  · intro y hy
    rw [hbo, mem_basicOpen_fn] at hy
    rw [mem_basicOpen_fn]
    change (p : O) ∉ (g y).asIdeal at hy
    change ϖ ∉ (g y).asIdeal
    intro h
    obtain ⟨c, hc⟩ := hϖp
    exact hy (hc ▸ Ideal.mul_mem_right c _ h)
