import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtaleSurjectiveProj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

/- English proof (translation)
Take `⟨pt⟩ : Nonempty (Spec (CommRingCat.of K))` from `inferInstance`. Take `⟨⟨i, w⟩, hw⟩` from `(sigmaMk (fun _ : I => W)).surjective (y pt)`. Rewrite `hw` using `[sigmaMk_mk]`. Use `⟨i, IsOpenImmersion.lift (Sigma.ι (fun _ : I => W) i) y ?_, IsOpenImmersion.lift_fac _ _ _⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨q, rfl⟩`.

Rewrite using `[Subsingleton.elim q pt]`. Conclude with `⟨w, hw⟩`.
-/
private theorem exists_sigma_point {W : Scheme.{0}} {I : Type} (K : Type) [Field K]
    (y : Spec (CommRingCat.of K) ⟶ ∐ fun _ : I => W) :
    ∃ (i : I) (y' : Spec (CommRingCat.of K) ⟶ W), y' ≫ Sigma.ι (fun _ : I => W) i = y := by
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  obtain ⟨⟨i, w⟩, hw⟩ := (sigmaMk (fun _ : I => W)).surjective (y pt)
  rw [sigmaMk_mk] at hw
  refine ⟨i, IsOpenImmersion.lift (Sigma.ι (fun _ : I => W) i) y ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨q, rfl⟩
  rw [Subsingleton.elim q pt]
  exact ⟨w, hw⟩

/- English proof (translation)
Set `F : I × {y' : Spec (CommRingCat.of K) ⟶ Y // y' ≫ s = x} → {y : Spec (CommRingCat.of K) ⟶ ∐ (fun _ : I => Y) // y ≫ (Sigma.desc fun _ : I => s) = x}` to `fun q => ⟨q.2.1 ≫ Sigma.ι (fun _ : I => Y) q.1, by`. Rewrite using `[Category.assoc, Sigma.ι_desc]`. Conclude with `q.2.2⟩`. Establish `hF : Function.Bijective F`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨i, a, ha⟩ ⟨j, b, hb⟩ h`. Establish `h' : a ≫ Sigma.ι (fun _ : I => Y) i = b ≫ Sigma.ι (fun _ : I => Y) j` using `congrArg Subtype.val h`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Establish `hab : a = b` using `(cancel_mono _).mp h'`.

Substitute `hab` using the available equality. Both sides reduce to the same expression. It suffices to derive a contradiction. Establish `hE` using `isEmpty_of_commSq_sigmaι_of_ne (g := fun _ : I => Y) ⟨h'⟩ hij`. Take `⟨p⟩` from `(inferInstance : Nonempty (Spec (CommRingCat.of K)))`.

Conclude with `hE.false p`. Introduce and unpack `⟨y, hy⟩`. Take `⟨i, y', rfl⟩` from `exists_sigma_point K y`. Use `⟨⟨i, y', ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite `hy` using `[Category.assoc, Sigma.ι_desc]`.

Conclude with `hy`. Rewrite using `[← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_prod]`.
-/
private theorem card_sigma_fibre {Y Z : Scheme.{0}} (s : Y ⟶ Z) (I : Type) (K : Type) [Field K]
    (x : Spec (CommRingCat.of K) ⟶ Z) :
    Nat.card {y : Spec (CommRingCat.of K) ⟶ ∐ (fun _ : I => Y) // y ≫ (Sigma.desc fun _ : I => s) = x} =
      Nat.card I * Nat.card {y' : Spec (CommRingCat.of K) ⟶ Y // y' ≫ s = x} := by
  let F : I × {y' : Spec (CommRingCat.of K) ⟶ Y // y' ≫ s = x} →
      {y : Spec (CommRingCat.of K) ⟶ ∐ (fun _ : I => Y) // y ≫ (Sigma.desc fun _ : I => s) = x} :=
    fun q => ⟨q.2.1 ≫ Sigma.ι (fun _ : I => Y) q.1, by
      rw [Category.assoc, Sigma.ι_desc]
      exact q.2.2⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨i, a, ha⟩ ⟨j, b, hb⟩ h
      have h' : a ≫ Sigma.ι (fun _ : I => Y) i = b ≫ Sigma.ι (fun _ : I => Y) j :=
        congrArg Subtype.val h
      by_cases hij : i = j
      · subst hij
        have hab : a = b := (cancel_mono _).mp h'
        subst hab
        rfl
      · exfalso
        have hE := isEmpty_of_commSq_sigmaι_of_ne (g := fun _ : I => Y) ⟨h'⟩ hij
        obtain ⟨p⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of K)))
        exact hE.false p
    · rintro ⟨y, hy⟩
      obtain ⟨i, y', rfl⟩ := exists_sigma_point K y
      refine ⟨⟨i, y', ?_⟩, rfl⟩
      rw [Category.assoc, Sigma.ι_desc] at hy
      exact hy
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_prod]

/- English proof (translation)
Introduce `Y Z s d I _ hs`. Take `⟨hfin, het, hcard⟩` from `hs`. Take `⟨n, ⟨e⟩⟩` from `Finite.exists_equiv_fin I`. Establish `hid : IsFinite (Sigma.desc fun _ : I => 𝟙 Y)`. Establish `h1` using `GlobalTheory.Et.TrivTors.isFinite_sigmaDesc_fin Y n`.

Establish `h2 : IsFinite ((Sigma.reindex e (fun _ : Fin n => Y)).hom ≫ Sigma.desc fun _ : Fin n => 𝟙 Y)` using `inferInstance`. Establish `h3 : (Sigma.desc fun _ : I => 𝟙 Y) = (Sigma.reindex e (fun _ : Fin n => Y)).hom ≫ Sigma.desc fun _ : Fin n => 𝟙 Y`. Use `Sigma.hom_ext (f := fun _ : I => Y) _ _ fun i => ?_` and prove the remaining obligations. Rewrite using `[Sigma.ι_desc, ← Category.assoc]`. Use `erw [Sigma.ι_reindex_hom (f := fun _ : Fin n => Y) e i]`.

Rewrite using `[Sigma.ι_desc]`. Rewrite using `[h3]`. Conclude with `h2`. Establish `hfac : (Sigma.desc fun _ : I => s) = (Sigma.desc fun _ : I => 𝟙 Y) ≫ s`. Use `Sigma.hom_ext (f := fun _ : I => Y) _ _ fun i => ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules. Establish `hloc : IsZariskiLocalAtSource @Etale.{0}` using `HasRingHomProperty.instIsZariskiLocalAtSource`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hfac] infer_instance`. Conclude with `IsZariskiLocalAtSource.sigmaDesc (P := @Etale.{0}) fun _ => het`.

Introduce `K _ _ x`. Rewrite using `[card_sigma_fibre, hcard]`.
-/
theorem UpperTheory.Gal.G3.pSigmaFEt :
    SigmaFEt := by
  intro Y Z s d I _ hs
  obtain ⟨hfin, het, hcard⟩ := hs
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  have hid : IsFinite (Sigma.desc fun _ : I => 𝟙 Y) := by
    have h1 := GlobalTheory.Et.TrivTors.isFinite_sigmaDesc_fin Y n
    have h2 : IsFinite ((Sigma.reindex e (fun _ : Fin n => Y)).hom ≫
        Sigma.desc fun _ : Fin n => 𝟙 Y) := inferInstance
    have h3 : (Sigma.desc fun _ : I => 𝟙 Y) =
        (Sigma.reindex e (fun _ : Fin n => Y)).hom ≫ Sigma.desc fun _ : Fin n => 𝟙 Y := by
      refine Sigma.hom_ext (f := fun _ : I => Y) _ _ fun i => ?_
      rw [Sigma.ι_desc, ← Category.assoc]
      erw [Sigma.ι_reindex_hom (f := fun _ : Fin n => Y) e i]
      rw [Sigma.ι_desc]
    rw [h3]
    exact h2
  have hfac : (Sigma.desc fun _ : I => s) = (Sigma.desc fun _ : I => 𝟙 Y) ≫ s := by
    refine Sigma.hom_ext (f := fun _ : I => Y) _ _ fun i => ?_
    simp
  have hloc : IsZariskiLocalAtSource @Etale.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  refine ⟨?_, ?_, ?_⟩
  · rw [hfac]
    infer_instance
  · exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale.{0}) fun _ => het
  · intro K _ _ x
    rw [card_sigma_fibre, hcard]
