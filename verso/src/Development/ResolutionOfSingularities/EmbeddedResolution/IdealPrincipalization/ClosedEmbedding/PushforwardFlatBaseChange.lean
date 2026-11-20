import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IdealSheafFlatDescent
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Use `hd` as an intermediate fact. Establish `: AlgebraicGeometry.Flat (pullback.snd d c)` using `inferInstance`. Rewrite using `[← sq.flip.isoPullback_hom_snd]`. Use `infer_instance`.
-/
private theorem flat_of_isPullback {A B C D : Scheme.{u}}
    {a : A ⟶ B} {b : A ⟶ C} {c : B ⟶ D} {d : C ⟶ D}
    (sq : IsPullback a b c d) (hd : AlgebraicGeometry.Flat d) :
    AlgebraicGeometry.Flat a := by
  have := hd
  have : AlgebraicGeometry.Flat (pullback.snd d c) := inferInstance
  rw [← sq.flip.isoPullback_hom_snd]
  infer_instance

/- English proof (translation)
Use `hd` as an intermediate fact. Establish `: IsClosedImmersion (pullback.snd d c)` using `inferInstance`. Rewrite using `[← sq.flip.isoPullback_hom_snd]`. Use `infer_instance`.
-/
private theorem isClosedImmersion_of_isPullback {A B C D : Scheme.{u}}
    {a : A ⟶ B} {b : A ⟶ C} {c : B ⟶ D} {d : C ⟶ D}
    (sq : IsPullback a b c d) (hd : IsClosedImmersion d) : IsClosedImmersion a := by
  have := hd
  have : IsClosedImmersion (pullback.snd d c) := inferInstance
  rw [← sq.flip.isoPullback_hom_snd]
  infer_instance

/- English proof (translation)
Introduce `b`. Proceed by induction on `b with`. Consider the case `zero`. Introduce `hb`. Rewrite using `[SequenceOfBlowups.projectionToBase_zero, SequenceOfBlowups.projectionToBase_zero]`.

Conclude with `hzero`. Consider the case `succ n ih`. Introduce `hb`. Establish `hn : n < L` using `hb`. Establish `h1` using `hstep n hn`.

Rewrite using `[SequenceOfBlowups.projectionToBase_succ, SequenceOfBlowups.projectionToBase_succ, ← Category.assoc, h1, Category.assoc, ih hn.le, Category.assoc]`.
-/
theorem comp_projectionToBase_of_comp_blowupMorphism {S X : Scheme.{u}} (s : SequenceOfBlowups S) (t : SequenceOfBlowups X)
    (L : ℕ) (j : S ⟶ X) (σ : ∀ i : ℕ, i ≤ L → (s.schemeAt i ⟶ t.schemeAt i))
    (hzero : σ 0 (Nat.zero_le _) ≫ t.isoZero.hom = s.isoZero.hom ≫ j)
    (hstep : ∀ i : ℕ, ∀ hi : i < L,
      σ (i + 1) hi ≫ t.transitionMapSucc i = s.transitionMapSucc i ≫ σ i hi.le) :
    ∀ b : ℕ, ∀ hb : b ≤ L, σ b hb ≫ t.projectionToBase b = s.projectionToBase b ≫ j := by
  intro b
  induction b with
  | zero =>
    intro hb
    rw [SequenceOfBlowups.projectionToBase_zero, SequenceOfBlowups.projectionToBase_zero]
    exact hzero
  | succ n ih =>
    intro hb
    have hn : n < L := hb
    have h1 := hstep n hn
    rw [SequenceOfBlowups.projectionToBase_succ, SequenceOfBlowups.projectionToBase_succ, ← Category.assoc, h1,
      Category.assoc, ih hn.le, Category.assoc]

namespace IsPushforwardBlowupSeq

/- English proof (translation)
Take `⟨hlen1, σ, hσci, hσ0, hσstep, hσcen, hσker⟩` from `hpush`. Take `⟨hlen2, τ, hτ0, hτstep, hτcen⟩` from `hs'`. Take `⟨hlen3, ρ, hρ0, hρstep, hρcen⟩` from `ht'`. Establish `hA : ∀ i : ℕ, i ≤ s'.length → i ≤ s.length` using `fun i hi => by omega`. Establish `hB : ∀ i : ℕ, i ≤ s'.length → i ≤ t'.length` using `fun i hi => by omega`.

Establish `Pt` using `isPullback_projectionToBase_of_isPullback_blowupMorphism g t' t t'.length ρ hρ0 hρstep`. Establish `Ps` using `isPullback_projectionToBase_of_isPullback_blowupMorphism p s' s s'.length τ hτ0 hτstep`. Establish `hσS` using `comp_projectionToBase_of_comp_blowupMorphism s t s.length j σ hσ0 hσstep`. Establish `hflatρ : ∀ i : ℕ, ∀ hi : i ≤ t'.length, AlgebraicGeometry.Flat (ρ i hi)` using `fun i hi => flat_of_isPullback (Pt i hi) inferInstance`. Establish `hw : ∀ i : ℕ, ∀ hi : i ≤ s'.length, (τ i hi ≫ σ i (hA i hi)) ≫ t.projectionToBase i = (s'.projectionToBase i ≫ j') ≫ g`.

Introduce `i hi`. Rewrite using `[Category.assoc, hσS i (hA i hi), ← Category.assoc, (Ps i hi).w, Category.assoc, ← hsq.w, Category.assoc]`. Take `⟨σ', hσ'1, hσ'2⟩ : ∃ σ' : ∀ i : ℕ, i ≤ s'.length → (s'.schemeAt i ⟶ t'.schemeAt i), (∀ i : ℕ, ∀ hi : i ≤ s'.length, σ' i hi ≫ ρ i (hB i hi) = τ i hi ≫ σ i (hA i hi)) ∧ (∀ i : ℕ, ∀ hi : i ≤ s'.length, σ' i hi ≫ t'.projectionToBase i = s'.projectionToBase i ≫ j')` from `⟨fun i hi => (Pt i (hB i hi)).lift (τ i hi ≫ σ i (hA i hi)) (s'.projectionToBase i ≫ j') (hw i hi), fun i hi => (Pt i (hB i hi)).lift_fst _ _ (hw i hi), fun i hi => (Pt i (hB i hi)).lift_snd _ _ (hw i hi)⟩`. Establish `Psq : ∀ i : ℕ, ∀ hi : i ≤ s'.length, IsPullback (σ' i hi) (τ i hi) (ρ i (hB i hi)) (σ i (hA i hi))`. Introduce `i hi`.

Use `IsPullback.of_right ?_ (hσ'1 i hi) (Pt i (hB i hi)).flip` and prove the remaining obligations. Rewrite using `[hσ'2 i hi, hσS i (hA i hi)]`. Conclude with `((Ps i hi).flip).paste_horiz hsq`. Establish `hci' : ∀ i : ℕ, ∀ hi : i ≤ s'.length, IsClosedImmersion (σ' i hi)` using `fun i hi => isClosedImmersion_of_isPullback (Psq i hi) (hσci i (hA i hi))`. Establish `hzero' : σ' 0 (Nat.zero_le _) ≫ t'.isoZero.hom = s'.isoZero.hom ≫ j'`.

Establish `h` using `hσ'2 0 (Nat.zero_le _)`. Rewrite `h` using `[SequenceOfBlowups.projectionToBase_zero, SequenceOfBlowups.projectionToBase_zero]`. Then use the resulting hypothesis. Establish `hstep' : ∀ i : ℕ, ∀ hi : i < s'.length, σ' (i + 1) hi ≫ t'.transitionMapSucc i = s'.transitionMapSucc i ≫ σ' i hi.le`. Introduce `i hi`. Establish `hit : i < t'.length` using `by omega`.

Establish `his : i < s.length` using `by omega`. Use `(Pt i (hB i hi.le)).hom_ext ?_ ?_` and prove the remaining obligations. Simplify using `only [Category.assoc]`. Rewrite using `[← (hρstep i hit).w, hσ'1 i hi.le, ← Category.assoc, hσ'1 (i + 1) hi, Category.assoc, hσstep i his, ← Category.assoc, (hτstep i hi).w, Category.assoc]`. Simplify using `only [Category.assoc]`.

Rewrite using `[← SequenceOfBlowups.projectionToBase_succ, hσ'2 (i + 1) hi, hσ'2 i hi.le, SequenceOfBlowups.projectionToBase_succ, Category.assoc]`. Establish `hcen' : ∀ i : ℕ, ∀ hi : i < s'.length, t'.center i = imageIdealSheaf (σ' i hi.le) (s'.center i)`. Introduce `i hi`. Establish `hit : i < t'.length` using `by omega`. Establish `his : i < s.length` using `by omega`.

Use `hσci i (hA i hi.le)` as an intermediate fact. Establish `: QuasiCompact (σ i (hA i hi.le))` using `inferInstance`. Use `hflatρ i (hB i hi.le)` as an intermediate fact. Rewrite using `[hρcen i hit, hτcen i hi, hσcen i his, ← map_eq_imageIdealSheaf, ← map_eq_imageIdealSheaf]`. Conclude with `comap_map_eq_map_comap_of_isPullback (Psq i hi.le).flip (s.center i)`.

Establish `hker' : ∀ i : ℕ, ∀ hi : i < s'.length, (σ' (i + 1) hi).ker = Blowup.strictTransform (t'.transitionMapSucc i) (t'.center i) (σ' i hi.le).ker`. Introduce `i hi`. Establish `hit : i < t'.length` using `by omega`. Establish `his : i < s.length` using `by omega`. Establish `hitt : i < t.length` using `by omega`.

Use `hσci i (hA i hi.le)` as an intermediate fact. Use `hσci (i + 1) (hA (i + 1) hi)` as an intermediate fact. Use `hci' i hi.le` as an intermediate fact. Use `hci' (i + 1) hi` as an intermediate fact. Use `hflatρ i (hB i hi.le)` as an intermediate fact.

Use `hflatρ (i + 1) (hB (i + 1) hi)` as an intermediate fact. Establish `: IsLocallyNoetherian (t.schemeAt (i + 1))` using `hnoeth (i + 1) (by omega)`. Establish `: IsLocallyNoetherian (t'.schemeAt (i + 1))` using `hnoeth' (i + 1) (by omega)`. Rewrite using `[ker_eq_comap_ker_of_isPullback_of_flat (Psq (i + 1) hi).flip, ker_eq_comap_ker_of_isPullback_of_flat (Psq i hi.le).flip, hσker i his, hρcen i hit]`. Conclude with `comap_strictTransform_of_flat_of_isLocallyNoetherian (t.transitionMapSucc i) (ρ i (hB i hi.le)) (t'.transitionMapSucc i) (ρ (i + 1) (hB (i + 1) hi)) (hρstep i hit) (t.center i) (σ i (hA i hi.le)).ker (t.isBlowupAlongIdealSheaf_blowupMorphism i hitt)`.

Establish `hlen : s'.length = t'.length` using `by omega`. Conclude with `And.intro hlen (Exists.intro σ' ⟨hci', hzero', hstep', hcen', hker'⟩)`.
-/
theorem of_flat_isPullback {S X S' X' : Scheme.{u}}
    (j : S ⟶ X) (j' : S' ⟶ X') (g : X' ⟶ X) (p : S' ⟶ S)
    [IsClosedImmersion j] [IsClosedImmersion j'] [AlgebraicGeometry.Flat g]
    (hsq : IsPullback j' p g j)
    (s : SequenceOfBlowups S) (t : SequenceOfBlowups X) (s' : SequenceOfBlowups S') (t' : SequenceOfBlowups X')
    (hnoeth : ∀ i : ℕ, i ≤ t.length → IsLocallyNoetherian (t.schemeAt i))
    (hnoeth' : ∀ i : ℕ, i ≤ t'.length → IsLocallyNoetherian (t'.schemeAt i))
    (hpush : IsPushforwardBlowupSeq j s t)
    (hs' : IsStrictPullbackBlowupSeq p s' s)
    (ht' : IsStrictPullbackBlowupSeq g t' t) :
    IsPushforwardBlowupSeq j' s' t' := by
  obtain ⟨hlen1, σ, hσci, hσ0, hσstep, hσcen, hσker⟩ := hpush
  obtain ⟨hlen2, τ, hτ0, hτstep, hτcen⟩ := hs'
  obtain ⟨hlen3, ρ, hρ0, hρstep, hρcen⟩ := ht'
  have hA : ∀ i : ℕ, i ≤ s'.length → i ≤ s.length := fun i hi => by omega
  have hB : ∀ i : ℕ, i ≤ s'.length → i ≤ t'.length := fun i hi => by omega
  have Pt := isPullback_projectionToBase_of_isPullback_blowupMorphism g t' t t'.length ρ hρ0 hρstep
  have Ps := isPullback_projectionToBase_of_isPullback_blowupMorphism p s' s s'.length τ hτ0 hτstep
  have hσS := comp_projectionToBase_of_comp_blowupMorphism s t s.length j σ hσ0 hσstep
  have hflatρ : ∀ i : ℕ, ∀ hi : i ≤ t'.length, AlgebraicGeometry.Flat (ρ i hi) := fun i hi =>
    flat_of_isPullback (Pt i hi) inferInstance
  have hw : ∀ i : ℕ, ∀ hi : i ≤ s'.length,
      (τ i hi ≫ σ i (hA i hi)) ≫ t.projectionToBase i = (s'.projectionToBase i ≫ j') ≫ g := by
    intro i hi
    rw [Category.assoc, hσS i (hA i hi), ← Category.assoc, (Ps i hi).w, Category.assoc,
      ← hsq.w, Category.assoc]
  obtain ⟨σ', hσ'1, hσ'2⟩ :
      ∃ σ' : ∀ i : ℕ, i ≤ s'.length → (s'.schemeAt i ⟶ t'.schemeAt i),
        (∀ i : ℕ, ∀ hi : i ≤ s'.length,
          σ' i hi ≫ ρ i (hB i hi) = τ i hi ≫ σ i (hA i hi)) ∧
        (∀ i : ℕ, ∀ hi : i ≤ s'.length,
          σ' i hi ≫ t'.projectionToBase i = s'.projectionToBase i ≫ j') :=
    ⟨fun i hi => (Pt i (hB i hi)).lift (τ i hi ≫ σ i (hA i hi)) (s'.projectionToBase i ≫ j') (hw i hi),
      fun i hi => (Pt i (hB i hi)).lift_fst _ _ (hw i hi),
      fun i hi => (Pt i (hB i hi)).lift_snd _ _ (hw i hi)⟩
  have Psq : ∀ i : ℕ, ∀ hi : i ≤ s'.length,
      IsPullback (σ' i hi) (τ i hi) (ρ i (hB i hi)) (σ i (hA i hi)) := by
    intro i hi
    refine IsPullback.of_right ?_ (hσ'1 i hi) (Pt i (hB i hi)).flip
    rw [hσ'2 i hi, hσS i (hA i hi)]
    exact ((Ps i hi).flip).paste_horiz hsq
  have hci' : ∀ i : ℕ, ∀ hi : i ≤ s'.length, IsClosedImmersion (σ' i hi) := fun i hi =>
    isClosedImmersion_of_isPullback (Psq i hi) (hσci i (hA i hi))
  have hzero' : σ' 0 (Nat.zero_le _) ≫ t'.isoZero.hom = s'.isoZero.hom ≫ j' := by
    have h := hσ'2 0 (Nat.zero_le _)
    rwa [SequenceOfBlowups.projectionToBase_zero, SequenceOfBlowups.projectionToBase_zero] at h
  have hstep' : ∀ i : ℕ, ∀ hi : i < s'.length,
      σ' (i + 1) hi ≫ t'.transitionMapSucc i = s'.transitionMapSucc i ≫ σ' i hi.le := by
    intro i hi
    have hit : i < t'.length := by omega
    have his : i < s.length := by omega
    refine (Pt i (hB i hi.le)).hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [← (hρstep i hit).w, hσ'1 i hi.le, ← Category.assoc, hσ'1 (i + 1) hi,
        Category.assoc, hσstep i his, ← Category.assoc, (hτstep i hi).w, Category.assoc]
    · simp only [Category.assoc]
      rw [← SequenceOfBlowups.projectionToBase_succ, hσ'2 (i + 1) hi, hσ'2 i hi.le,
        SequenceOfBlowups.projectionToBase_succ, Category.assoc]
  have hcen' : ∀ i : ℕ, ∀ hi : i < s'.length,
      t'.center i = imageIdealSheaf (σ' i hi.le) (s'.center i) := by
    intro i hi
    have hit : i < t'.length := by omega
    have his : i < s.length := by omega
    have := hσci i (hA i hi.le)
    have : QuasiCompact (σ i (hA i hi.le)) := inferInstance
    have := hflatρ i (hB i hi.le)
    rw [hρcen i hit, hτcen i hi, hσcen i his, ← map_eq_imageIdealSheaf, ← map_eq_imageIdealSheaf]
    exact comap_map_eq_map_comap_of_isPullback (Psq i hi.le).flip (s.center i)
  have hker' : ∀ i : ℕ, ∀ hi : i < s'.length,
      (σ' (i + 1) hi).ker =
        Blowup.strictTransform (t'.transitionMapSucc i) (t'.center i) (σ' i hi.le).ker := by
    intro i hi
    have hit : i < t'.length := by omega
    have his : i < s.length := by omega
    have hitt : i < t.length := by omega
    have := hσci i (hA i hi.le)
    have := hσci (i + 1) (hA (i + 1) hi)
    have := hci' i hi.le
    have := hci' (i + 1) hi
    have := hflatρ i (hB i hi.le)
    have := hflatρ (i + 1) (hB (i + 1) hi)
    have : IsLocallyNoetherian (t.schemeAt (i + 1)) := hnoeth (i + 1) (by omega)
    have : IsLocallyNoetherian (t'.schemeAt (i + 1)) := hnoeth' (i + 1) (by omega)
    rw [ker_eq_comap_ker_of_isPullback_of_flat (Psq (i + 1) hi).flip,
      ker_eq_comap_ker_of_isPullback_of_flat (Psq i hi.le).flip, hσker i his, hρcen i hit]
    exact comap_strictTransform_of_flat_of_isLocallyNoetherian (t.transitionMapSucc i)
      (ρ i (hB i hi.le)) (t'.transitionMapSucc i) (ρ (i + 1) (hB (i + 1) hi)) (hρstep i hit)
      (t.center i) (σ i (hA i hi.le)).ker (t.isBlowupAlongIdealSheaf_blowupMorphism i hitt)
  have hlen : s'.length = t'.length := by omega
  exact And.intro hlen (Exists.intro σ' ⟨hci', hzero', hstep', hcen', hker'⟩)

end IsPushforwardBlowupSeq

end FunctorialResolution.EmbeddedResolution
