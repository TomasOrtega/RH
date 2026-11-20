import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SpecGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PSpValsub
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.GenericFibreEqvOfSmoothOfNormalLocalDomain
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.SpecializationEqvOfProperOfStrictlyHenselian
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PSpUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PSpHqBij
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PSpPbEqv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PSpPaste
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et GlobalTheory.EtC

/- English proof (translation)
Unfold `pullHQ`. Rewrite using `[pullHl_comp, LinearMap.baseChange_comp]`. Both sides reduce to the same expression.
-/
private theorem pullHQ_comp' (l : ℕ) [Fact l.Prime] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n i : ℤ)
    (x : HQ l E'' n i) : pullHQ l (f ≫ g) n i x = pullHQ l f n i (pullHQ l g n i x) := by
  unfold pullHQ
  rw [pullHl_comp, LinearMap.baseChange_comp]
  rfl

/- English proof (translation)
Introduce `hE2 hE3 O _ K _ _ κ _ _ Ω _ _ _ V hV kb _ _ _ r hr hrO Y p _ _ iY jY hi1 hi2 hj1 hj2`. Take `⟨hAIC, hSH⟩` from `UpperTheory.Gal.Mod.spValsub Ω V`. Use `set ι : O →+* V := RingHom.codRestrict ((algebraMap K Ω).comp (algebraMap O K)) V hV with hι`. Establish `hpbJ : IsPullback jY (pullback.snd _ _) (pullback.snd p (Spec.map (CommRingCat.ofHom ι))) (Spec.map (CommRingCat.ofHom V.subtype))`. Use `UpperTheory.Gal.Mod.spPaste p (Spec.map (CommRingCat.ofHom ι)) (Spec.map (CommRingCat.ofHom (algebraMap O K))) (Spec.map (CommRingCat.ofHom V.subtype)) (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ?_ jY hj1 hj2` and prove the remaining obligations.

Rewrite using `[← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]`. Both sides reduce to the same expression. Establish `hpbI : IsPullback iY (pullback.snd _ _) (pullback.snd p (Spec.map (CommRingCat.ofHom ι))) (Spec.map (CommRingCat.ofHom r))`. Use `UpperTheory.Gal.Mod.spPaste p (Spec.map (CommRingCat.ofHom ι)) (Spec.map (CommRingCat.ofHom (algebraMap O κ))) (Spec.map (CommRingCat.ofHom r)) (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ?_ iY hi1 hi2` and prove the remaining obligations. Rewrite using `[← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]`.

Use `congr 2`. Use extensionality with `a`. Conclude with `hrO a`. Establish `hpbJ' : IsPullback jY (pullback.snd _ _) (pullback.snd p (Spec.map (CommRingCat.ofHom ι))) (Spec.map (CommRingCat.ofHom (algebraMap V Ω)))` using `hpbJ`. Establish `hEq : ∀ q : ℕ, IsUnit (q : kb) → ∀ i : ℤ, Eqv _ (sch.map iY) (tw q i) ∧ Eqv _ (sch.map jY) (tw q i)`.

Introduce `q hq i`. Establish `hqV : IsUnit (q : V)` using `UpperTheory.Gal.Mod.spUnit V kb r hr q hq`. Use `haveI : NeZero q := ⟨by rintro rfl; simp at hq⟩`. Establish `h2` using `UpperTheory.Gal.Mod.specialization_eqv_of_proper_of_strictly_henselian hE2 q V hSH hqV kb r hr (pullback.snd p (Spec.map (CommRingCat.ofHom ι))) i`. Establish `h3` using `UpperTheory.Gal.Mod.generic_fibre_eqv_of_smooth_of_normal_local_domain hE3 q V hAIC hqV Ω (pullback.snd p (Spec.map (CommRingCat.ofHom ι))) i`.

Conclude with `⟨UpperTheory.Gal.Mod.spPbEqv _ _ _ _ _ _ hpbI h2, UpperTheory.Gal.Mod.spPbEqv _ _ _ _ _ _ hpbJ' h3⟩`. Use `⟨hEq, ?_⟩` and prove the remaining obligations. Introduce `l _ hl n i`. Establish `hlk : ∀ k : ℕ, IsUnit (((l ^ k : ℕ)) : kb)` using `fun k => by`. Use `push_cast`.

Conclude with `hl.pow k`. Establish `hbI : Function.Bijective (pullHQ l (sch.map iY) n i)` using `UpperTheory.Gal.Mod.spHqBij l _ n i (fun k => (hEq _ (hlk k) i).1 n)`. Establish `hbJ : Function.Bijective (pullHQ l (sch.map jY) n i)` using `UpperTheory.Gal.Mod.spHqBij l _ n i (fun k => (hEq _ (hlk k) i).2 n)`. Set `eI` to `LinearEquiv.ofBijective _ hbI`. Set `eJ` to `LinearEquiv.ofBijective _ hbJ`.

Establish `hsp : ∀ x, (eI.symm.trans eJ) (pullHQ l (sch.map iY) n i x) = pullHQ l (sch.map jY) n i x`. Introduce `x`. Establish `: eI.symm (pullHQ l (sch.map iY) n i x) = x` using `eI.symm_apply_apply x`. Express the relevant statement in the definitionally equal form `eJ (eI.symm (pullHQ l (sch.map iY) n i x)) = _`. Rewrite using `[this]`.

Both sides reduce to the same expression. Use `⟨eI.symm.trans eJ, hsp, ?_⟩` and prove the remaining obligations. Introduce `σ τ hσ hτ x`. Take `⟨y, rfl⟩` from `hbI.2 x`. Set `σV : V →+* V` to `RingHom.codRestrict ((σ : Ω →+* Ω).comp V.subtype) V (fun v => hσ v v.2)`.

Establish `hσι : Spec.map (CommRingCat.ofHom σV) ≫ Spec.map (CommRingCat.ofHom ι) = Spec.map (CommRingCat.ofHom ι)`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Use extensionality with `a`. Conclude with `σ.commutes (algebraMap O K a)`.

Set `s : pullback p (Spec.map (CommRingCat.ofHom ι)) ⟶ pullback p (Spec.map (CommRingCat.ofHom ι))` to `pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom σV)) (by`. Rewrite using `[Category.assoc, hσι, pullback.condition])`. Establish `hs1 : s ≫ pullback.fst _ _ = pullback.fst _ _` using `pullback.lift_fst _ _ _`. Establish `hs2 : s ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom σV)` using `pullback.lift_snd _ _ _`. Establish `hJ : galMap Ω (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap O K)))) σ ≫ jY = jY ≫ s`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, hj1, hs1, hj1, galMap_fst_assoc]`. Rewrite using `[Category.assoc, Category.assoc, hj2, hs2, galMap_snd_assoc, ← Category.assoc jY, hj2, Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]`. Both sides reduce to the same expression. Establish `hI : galMap kb (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) τ ≫ iY = iY ≫ s`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, hi1, hs1, hi1, galMap_fst_assoc]`. Rewrite using `[Category.assoc, Category.assoc, hi2, hs2, galMap_snd_assoc, ← Category.assoc iY, hi2, Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]`. Use `congr 3`. Use extensionality with `v`.

Conclude with `(hτ v).symm`. Establish `hgI : galHQ l kb (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) n i τ (pullHQ l (sch.map iY) n i y) = pullHQ l (sch.map iY) n i (pullHQ l (sch.map s) n i y)`. Rewrite using `[← pullHQ_comp', ← Functor.map_comp, ← hI, Functor.map_comp, pullHQ_comp']`. Both sides reduce to the same expression. Establish `hgJ : galHQ l Ω (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap O K)))) n i σ (pullHQ l (sch.map jY) n i y) = pullHQ l (sch.map jY) n i (pullHQ l (sch.map s) n i y)`.

Rewrite using `[← pullHQ_comp', ← Functor.map_comp, ← hJ, Functor.map_comp, pullHQ_comp']`. Both sides reduce to the same expression. Rewrite using `[hgI, hsp, hsp, hgJ]`.
-/
theorem UpperTheory.Gal.Mod.spSpecIf :
    GlobalTheory.EtC.E2 → GlobalTheory.EtC.E3 → GlobalTheory.EtC.SpecGood := by
  intro hE2 hE3 O _ K _ _ κ _ _ Ω _ _ _ V hV kb _ _ _ r hr hrO Y p _ _ iY jY hi1 hi2 hj1 hj2
  obtain ⟨hAIC, hSH⟩ := UpperTheory.Gal.Mod.spValsub Ω V
  set ι : O →+* V := RingHom.codRestrict ((algebraMap K Ω).comp (algebraMap O K)) V hV with hι
  have hpbJ : IsPullback jY (pullback.snd _ _) (pullback.snd p (Spec.map (CommRingCat.ofHom ι)))
      (Spec.map (CommRingCat.ofHom V.subtype)) := by
    refine UpperTheory.Gal.Mod.spPaste p (Spec.map (CommRingCat.ofHom ι))
      (Spec.map (CommRingCat.ofHom (algebraMap O K))) (Spec.map (CommRingCat.ofHom V.subtype))
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ?_ jY hj1 hj2
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hpbI : IsPullback iY (pullback.snd _ _) (pullback.snd p (Spec.map (CommRingCat.ofHom ι)))
      (Spec.map (CommRingCat.ofHom r)) := by
    refine UpperTheory.Gal.Mod.spPaste p (Spec.map (CommRingCat.ofHom ι))
      (Spec.map (CommRingCat.ofHom (algebraMap O κ))) (Spec.map (CommRingCat.ofHom r))
      (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ?_ iY hi1 hi2
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    exact hrO a
  have hpbJ' : IsPullback jY (pullback.snd _ _) (pullback.snd p (Spec.map (CommRingCat.ofHom ι)))
      (Spec.map (CommRingCat.ofHom (algebraMap V Ω))) := hpbJ
  have hEq : ∀ q : ℕ, IsUnit (q : kb) → ∀ i : ℤ,
      Eqv _ (sch.map iY) (tw q i) ∧ Eqv _ (sch.map jY) (tw q i) := by
    intro q hq i
    have hqV : IsUnit (q : V) := UpperTheory.Gal.Mod.spUnit V kb r hr q hq
    haveI : NeZero q := ⟨by rintro rfl; simp at hq⟩
    have h2 := UpperTheory.Gal.Mod.specialization_eqv_of_proper_of_strictly_henselian hE2 q V hSH hqV kb r hr
      (pullback.snd p (Spec.map (CommRingCat.ofHom ι))) i
    have h3 := UpperTheory.Gal.Mod.generic_fibre_eqv_of_smooth_of_normal_local_domain hE3 q V hAIC hqV Ω
      (pullback.snd p (Spec.map (CommRingCat.ofHom ι))) i
    exact ⟨UpperTheory.Gal.Mod.spPbEqv _ _ _ _ _ _ hpbI h2, UpperTheory.Gal.Mod.spPbEqv _ _ _ _ _ _ hpbJ' h3⟩
  refine ⟨hEq, ?_⟩
  intro l _ hl n i
  have hlk : ∀ k : ℕ, IsUnit (((l ^ k : ℕ)) : kb) := fun k => by
    push_cast
    exact hl.pow k
  have hbI : Function.Bijective (pullHQ l (sch.map iY) n i) :=
    UpperTheory.Gal.Mod.spHqBij l _ n i (fun k => (hEq _ (hlk k) i).1 n)
  have hbJ : Function.Bijective (pullHQ l (sch.map jY) n i) :=
    UpperTheory.Gal.Mod.spHqBij l _ n i (fun k => (hEq _ (hlk k) i).2 n)
  let eI := LinearEquiv.ofBijective _ hbI
  let eJ := LinearEquiv.ofBijective _ hbJ
  have hsp : ∀ x, (eI.symm.trans eJ) (pullHQ l (sch.map iY) n i x) = pullHQ l (sch.map jY) n i x := by
    intro x
    have : eI.symm (pullHQ l (sch.map iY) n i x) = x := eI.symm_apply_apply x
    change eJ (eI.symm (pullHQ l (sch.map iY) n i x)) = _
    rw [this]
    rfl
  refine ⟨eI.symm.trans eJ, hsp, ?_⟩
  intro σ τ hσ hτ x
  obtain ⟨y, rfl⟩ := hbI.2 x
  let σV : V →+* V := RingHom.codRestrict ((σ : Ω →+* Ω).comp V.subtype) V (fun v => hσ v v.2)
  have hσι : Spec.map (CommRingCat.ofHom σV) ≫ Spec.map (CommRingCat.ofHom ι) = Spec.map (CommRingCat.ofHom ι) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    exact σ.commutes (algebraMap O K a)
  let s : pullback p (Spec.map (CommRingCat.ofHom ι)) ⟶ pullback p (Spec.map (CommRingCat.ofHom ι)) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom σV)) (by
      rw [Category.assoc, hσι, pullback.condition])
  have hs1 : s ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hs2 : s ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom σV) :=
    pullback.lift_snd _ _ _
  have hJ : galMap Ω (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap O K)))) σ ≫ jY = jY ≫ s := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hj1, hs1, hj1, galMap_fst_assoc]
    · rw [Category.assoc, Category.assoc, hj2, hs2, galMap_snd_assoc, ← Category.assoc jY, hj2,
        Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp]
      rfl
  have hI : galMap kb (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) τ ≫ iY = iY ≫ s := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hi1, hs1, hi1, galMap_fst_assoc]
    · rw [Category.assoc, Category.assoc, hi2, hs2, galMap_snd_assoc, ← Category.assoc iY, hi2,
        Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp]
      congr 3
      ext v
      exact (hτ v).symm
  have hgI : galHQ l kb (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) n i τ
      (pullHQ l (sch.map iY) n i y) = pullHQ l (sch.map iY) n i (pullHQ l (sch.map s) n i y) := by
    rw [← pullHQ_comp', ← Functor.map_comp, ← hI, Functor.map_comp, pullHQ_comp']
    rfl
  have hgJ : galHQ l Ω (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap O K)))) n i σ
      (pullHQ l (sch.map jY) n i y) = pullHQ l (sch.map jY) n i (pullHQ l (sch.map s) n i y) := by
    rw [← pullHQ_comp', ← Functor.map_comp, ← hJ, Functor.map_comp, pullHQ_comp']
    rfl
  rw [hgI, hsp, hsp, hgJ]
