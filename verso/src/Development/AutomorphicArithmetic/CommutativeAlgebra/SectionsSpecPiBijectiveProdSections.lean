import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC TensorProduct

private noncomputable abbrev sι {n : ℕ} (C : Fin n → Type) [∀ i, CommRing (C i)] (i : Fin n) :
    Spec (CommRingCat.of (C i)) ⟶ Spec (CommRingCat.of (∀ i, C i)) :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))

/- English proof (translation)
The claim follows from `(ι_sigmaSpec (fun i => CommRingCat.of (C i)) i).symm`.
-/
private lemma sι_eq {n : ℕ} (C : Fin n → Type) [∀ i, CommRing (C i)] (i : Fin n) :
    sι C i = Sigma.ι (fun i => Spec (CommRingCat.of (C i))) i ≫ sigmaSpec (fun i => CommRingCat.of (C i)) :=
  (ι_sigmaSpec (fun i => CommRingCat.of (C i)) i).symm

private instance {n : ℕ} (C : Fin n → Type) [∀ i, CommRing (C i)] (i : Fin n) : IsOpenImmersion (sι C i) := by
  rw [sι_eq]; infer_instance

/- English proof (translation)
Establish `hcov` using `hP.isSheafFor _ (sigmaOpenCover X).mem_grothendieckTopology`. Rewrite `hcov` using `[Presieve.isSheafFor_arrows_iff]`. Establish `hcomp : ∀ x : ∀ i, P.obj (op (X i)), Presieve.Arrows.Compatible P (Sigma.ι X) x`. Introduce `x i j Z gi gj h`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Rewrite `h` using `[cancel_mono]`. Rewrite using `[h]`. Use `haveI := isEmpty_of_commSq_sigmaι_of_ne ⟨h⟩ hij`. Conclude with `(hP (⊥ : Sieve Z) (Scheme.bot_mem_grothendieckTopology Z)).isSeparatedFor.ext (fun _ _ hf => hf.elim)`.

Prove the components needed by the constructor for the conclusion. Introduce `s t hst`. Conclude with `(hcov (fun i => P.map (Sigma.ι X i).op s) (hcomp _)).unique (fun i => rfl) (fun i => (congr_fun hst i).symm)`. Introduce `y`. Take `⟨t, ht, -⟩` from `hcov y (hcomp y)`.

Conclude with `⟨t, funext ht⟩`.
-/
private theorem bijective_sheaf_sigma_restrict {P : Scheme.{0}ᵒᵖ ⥤ Type 1}
    (hP : Presieve.IsSheaf Scheme.zariskiTopology P) {n : ℕ} (X : Fin n → Scheme.{0}) :
    Function.Bijective (fun (s : P.obj (op (∐ X))) (i : Fin n) => P.map (Sigma.ι X i).op s) := by
  have hcov := hP.isSheafFor _ (sigmaOpenCover X).mem_grothendieckTopology
  rw [Presieve.isSheafFor_arrows_iff] at hcov
  have hcomp : ∀ x : ∀ i, P.obj (op (X i)), Presieve.Arrows.Compatible P (Sigma.ι X) x := by
    intro x i j Z gi gj h
    by_cases hij : i = j
    · subst hij
      rw [cancel_mono] at h
      rw [h]
    · haveI := isEmpty_of_commSq_sigmaι_of_ne ⟨h⟩ hij
      exact (hP (⊥ : Sieve Z) (Scheme.bot_mem_grothendieckTopology Z)).isSeparatedFor.ext
        (fun _ _ hf => hf.elim)
  constructor
  · intro s t hst
    exact (hcov (fun i => P.map (Sigma.ι X i).op s) (hcomp _)).unique (fun i => rfl)
      (fun i => (congr_fun hst i).symm)
  · intro y
    obtain ⟨t, ht, -⟩ := hcov y (hcomp y)
    exact ⟨t, funext ht⟩

/- English proof (translation)
Introduce `R _ F n C _`. Establish `hG : Presieve.IsSheaf Scheme.zariskiTopology (F.obj ⋙ CategoryTheory.forget (ModuleCat (ULift.{1, 0} R)))`. Apply `Presieve.isSheaf_of_le _ Scheme.zariskiTopology_le_etaleTopology` to reduce the goal to its premises. Rewrite using `[← isSheaf_iff_isSheaf_of_type]`. Conclude with `(Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget _)).mp F.cond`.

Establish `key` using `bijective_sheaf_sigma_restrict hG (fun i => Spec (CommRingCat.of (C i)))`. Establish `hiso : Function.Bijective ((F.obj ⋙ CategoryTheory.forget _).map (sigmaSpec (fun i => CommRingCat.of (C i))).op)` using `(isIso_iff_bijective _).mp inferInstance`. Use `key.comp hiso using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `s i`. Rewrite using `[show Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i)) = _ from sι_eq C i]`.

Simplify using `only [Sec.res, Function.comp_apply, op_comp, Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.sections_specPi_bijective_prod_sections :
    ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℕ) (C : Fin n → Type) [∀ i, CommRing (C i)],
        Function.Bijective (fun (s : Sec F (Spec (CommRingCat.of (∀ i, C i)))) (i : Fin n) =>
          (Sec.res (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))) s : Sec F (Spec (CommRingCat.of (C i))))) := by
  intro R _ F n C _
  have hG : Presieve.IsSheaf Scheme.zariskiTopology
      (F.obj ⋙ CategoryTheory.forget (ModuleCat (ULift.{1, 0} R))) := by
    apply Presieve.isSheaf_of_le _ Scheme.zariskiTopology_le_etaleTopology
    rw [← isSheaf_iff_isSheaf_of_type]
    exact (Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget _)).mp F.cond
  have key := bijective_sheaf_sigma_restrict hG (fun i => Spec (CommRingCat.of (C i)))
  have hiso : Function.Bijective ((F.obj ⋙ CategoryTheory.forget _).map
      (sigmaSpec (fun i => CommRingCat.of (C i))).op) :=
    (isIso_iff_bijective _).mp inferInstance
  convert key.comp hiso using 1
  funext s i
  rw [show Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i)) = _ from sι_eq C i]
  simp only [Sec.res, Function.comp_apply, op_comp, Functor.map_comp]
  rfl
