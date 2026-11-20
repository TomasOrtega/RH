import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.StrictTransformClosedImmersion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.IsomorphismTransport
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace IsPushforwardBlowupSeq

/- English proof (translation)
The claim follows from `(ker_comp_eq_imageIdealSheaf_ker f g).trans (imageIdealSheaf_eq_ker g f.ker)`.
-/
private theorem ker_comp_eq_ker_subschemeι_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    Scheme.Hom.ker (f ≫ g) = Scheme.Hom.ker ((Scheme.Hom.ker f).subschemeι ≫ g) :=
  (ker_comp_eq_imageIdealSheaf_ker f g).trans (imageIdealSheaf_eq_ker g f.ker)

/- English proof (translation)
Take `⟨hl1, a, haci, ha0, hasq, hac, hak⟩` from `hst`. Take `⟨hl2, b, hbci, hb0, hbsq, hbc, hbk⟩` from `htu`. Use `⟨hl1.trans hl2, fun i hi => a i hi ≫ b i (by omega), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Establish `hit : i ≤ t.length` using `by omega`.

Use `haci i hi` as an intermediate fact. Use `hbci i hit` as an intermediate fact. Use `show IsClosedImmersion (a i hi ≫ b i hit)`. Use `infer_instance`. Use `show (a 0 (Nat.zero_le _) ≫ b 0 (Nat.zero_le _)) ≫ u.isoZero.hom = s.isoZero.hom ≫ (σ ≫ ρ)`.

Rewrite using `[Category.assoc, hb0, ← Category.assoc, ha0, Category.assoc]`. Introduce `i hi`. Establish `hit : i < t.length` using `by omega`. Use `show (a (i + 1) hi ≫ b (i + 1) hit) ≫ u.transitionMapSucc i = s.transitionMapSucc i ≫ (a i hi.le ≫ b i hit.le)`. Rewrite using `[Category.assoc, hbsq i hit, ← Category.assoc, hasq i hi, Category.assoc]`.

Introduce `i hi`. Establish `hit : i < t.length` using `by omega`. Use `haci i hi.le` as an intermediate fact. Use `hbci i hit.le` as an intermediate fact. Use `show u.center i = imageIdealSheaf (a i hi.le ≫ b i hit.le) (s.center i)`.

Rewrite using `[hbc i hit, hac i hi, imageIdealSheaf_comp]`. Introduce `i hi`. Establish `hit : i < t.length` using `by omega`. Establish `hiu : i < u.length` using `by omega`. Use `hbci i hit.le` as an intermediate fact.

Use `hbci (i + 1) hit` as an intermediate fact. Use `haci i hi.le` as an intermediate fact. Use `haci (i + 1) hi` as an intermediate fact. Use `hNt (i + 1) hit` as an intermediate fact. Use `hNu (i + 1) hiu` as an intermediate fact.

Establish `hker : Scheme.Hom.ker (b (i + 1) hit) = Blowup.strictTransform (u.transitionMapSucc i) (Scheme.Hom.ker ((t.center i).subschemeι ≫ b i hit.le)) (Scheme.Hom.ker (b i hit.le))`. Rewrite using `[hbk i hit, hbc i hit, imageIdealSheaf_eq_ker]`. Establish `key` using `image_strictTransform_eq_strictTransform_image (b i hit.le) (t.center i) (Scheme.Hom.ker (a i hi.le)) (t.transitionMapSucc i) (u.transitionMapSucc i) (b (i + 1) hit) (hbsq i hit) hker`. Establish `hL : Scheme.Hom.ker (a (i + 1) hi ≫ b (i + 1) hit) = Scheme.Hom.ker ((Blowup.strictTransform (t.transitionMapSucc i) (t.center i) (Scheme.Hom.ker (a i hi.le))).subschemeι ≫ b (i + 1) hit)`. Rewrite using `[ker_comp_eq_ker_subschemeι_comp, hak i hi]`.

Establish `hD : Scheme.Hom.ker (a i hi.le ≫ b i hit.le) = Scheme.Hom.ker ((Scheme.Hom.ker (a i hi.le)).subschemeι ≫ b i hit.le)` using `ker_comp_eq_ker_subschemeι_comp _ _`. Establish `hC : u.center i = Scheme.Hom.ker ((t.center i).subschemeι ≫ b i hit.le)`. Rewrite using `[hbc i hit, imageIdealSheaf_eq_ker]`. Use `show Scheme.Hom.ker (a (i + 1) hi ≫ b (i + 1) hit) = Blowup.strictTransform (u.transitionMapSucc i) (u.center i) (Scheme.Hom.ker (a i hi.le ≫ b i hit.le))`. Rewrite using `[hL, key, hC, hD]`.
-/
theorem comp {Y H X : Scheme.{u}} (σ : Y ⟶ H) [IsClosedImmersion σ]
    (ρ : H ⟶ X) [IsClosedImmersion ρ]
    {s : SequenceOfBlowups Y} {t : SequenceOfBlowups H} {u : SequenceOfBlowups X}
    (hNt : ∀ i : ℕ, i ≤ t.length → AlgebraicGeometry.IsNoetherian (t.schemeAt i))
    (hNu : ∀ i : ℕ, i ≤ u.length → AlgebraicGeometry.IsNoetherian (u.schemeAt i))
    (hst : IsPushforwardBlowupSeq σ s t) (htu : IsPushforwardBlowupSeq ρ t u) :
    IsPushforwardBlowupSeq (σ ≫ ρ) s u := by
  obtain ⟨hl1, a, haci, ha0, hasq, hac, hak⟩ := hst
  obtain ⟨hl2, b, hbci, hb0, hbsq, hbc, hbk⟩ := htu
  refine ⟨hl1.trans hl2, fun i hi => a i hi ≫ b i (by omega), ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hit : i ≤ t.length := by omega
    have := haci i hi
    have := hbci i hit
    show IsClosedImmersion (a i hi ≫ b i hit)
    infer_instance
  · show (a 0 (Nat.zero_le _) ≫ b 0 (Nat.zero_le _)) ≫ u.isoZero.hom
      = s.isoZero.hom ≫ (σ ≫ ρ)
    rw [Category.assoc, hb0, ← Category.assoc, ha0, Category.assoc]
  · intro i hi
    have hit : i < t.length := by omega
    show (a (i + 1) hi ≫ b (i + 1) hit) ≫ u.transitionMapSucc i
      = s.transitionMapSucc i ≫ (a i hi.le ≫ b i hit.le)
    rw [Category.assoc, hbsq i hit, ← Category.assoc, hasq i hi, Category.assoc]
  · intro i hi
    have hit : i < t.length := by omega
    have := haci i hi.le
    have := hbci i hit.le
    show u.center i = imageIdealSheaf (a i hi.le ≫ b i hit.le) (s.center i)
    rw [hbc i hit, hac i hi, imageIdealSheaf_comp]
  · intro i hi
    have hit : i < t.length := by omega
    have hiu : i < u.length := by omega
    have := hbci i hit.le
    have := hbci (i + 1) hit
    have := haci i hi.le
    have := haci (i + 1) hi
    have := hNt (i + 1) hit
    have := hNu (i + 1) hiu
    have hker : Scheme.Hom.ker (b (i + 1) hit)
        = Blowup.strictTransform (u.transitionMapSucc i)
            (Scheme.Hom.ker ((t.center i).subschemeι ≫ b i hit.le))
            (Scheme.Hom.ker (b i hit.le)) := by
      rw [hbk i hit, hbc i hit, imageIdealSheaf_eq_ker]
    have key := image_strictTransform_eq_strictTransform_image (b i hit.le) (t.center i)
      (Scheme.Hom.ker (a i hi.le)) (t.transitionMapSucc i) (u.transitionMapSucc i) (b (i + 1) hit)
      (hbsq i hit) hker
    have hL : Scheme.Hom.ker (a (i + 1) hi ≫ b (i + 1) hit)
        = Scheme.Hom.ker ((Blowup.strictTransform (t.transitionMapSucc i) (t.center i)
            (Scheme.Hom.ker (a i hi.le))).subschemeι ≫ b (i + 1) hit) := by
      rw [ker_comp_eq_ker_subschemeι_comp, hak i hi]
    have hD : Scheme.Hom.ker (a i hi.le ≫ b i hit.le)
        = Scheme.Hom.ker ((Scheme.Hom.ker (a i hi.le)).subschemeι ≫ b i hit.le) :=
      ker_comp_eq_ker_subschemeι_comp _ _
    have hC : u.center i = Scheme.Hom.ker ((t.center i).subschemeι ≫ b i hit.le) := by
      rw [hbc i hit, imageIdealSheaf_eq_ker]
    show Scheme.Hom.ker (a (i + 1) hi ≫ b (i + 1) hit)
      = Blowup.strictTransform (u.transitionMapSucc i) (u.center i)
          (Scheme.Hom.ker (a i hi.le ≫ b i hit.le))
    rw [hL, key, hC, hD]

/- English proof (translation)
Take `⟨hlen, e, h0, hsqe, hce⟩` from `hs`. Establish `hpb : IsStrictPullbackBlowupSeq (𝟙 S) s' s`. Use `⟨hlen.symm, fun i hi => (e i (by omega)).inv, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show (e 0 (Nat.zero_le _)).inv ≫ s.isoZero.hom = s'.isoZero.hom ≫ 𝟙 S`. Rewrite using `[Category.comp_id, ← h0, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]`.

Introduce `i hi`. Establish `hi' : i < s.length` using `by omega`. Establish `hsq : (e (i + 1) hi').inv ≫ s.transitionMapSucc i = s'.transitionMapSucc i ≫ (e i hi'.le).inv`. Rewrite using `[Iso.inv_comp_eq, ← Category.assoc, hsqe i hi', Category.assoc, Iso.hom_inv_id, Category.comp_id]`. Use `show IsPullback ((e (i + 1) hi').inv) (s'.transitionMapSucc i) (s.transitionMapSucc i) ((e i hi'.le).inv)`.

Conclude with `IsPullback.of_horiz_isIso ⟨hsq⟩`. Introduce `i hi`. Establish `hi' : i < s.length` using `by omega`. Establish `h1 : imageIdealSheaf (e i hi'.le).hom ((s'.center i).comap (e i hi'.le).hom) = imageIdealSheaf (e i hi'.le).hom (s.center i)` using `by rw [hce i hi']`. Rewrite `h1` using `[imageIdealSheaf_comap]`.

Establish `h2 : inv (e i hi'.le).hom = (e i hi'.le).inv` using `IsIso.inv_eq_of_hom_inv_id (Iso.hom_inv_id (e i hi'.le))`. Use `show s'.center i = (s.center i).comap ((e i hi'.le).inv)`. Rewrite using `[h1, imageIdealSheaf_eq_comap_inv, h2]`. Conclude with `IsPushforwardBlowupSeq.isIso_comp (𝟙 S) j j (Category.id_comp j).symm hpb h`.
-/
theorem of_isomorphic_source {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    {s s' : SequenceOfBlowups S} {t : SequenceOfBlowups X}
    (hs : s.Isomorphic s') (h : IsPushforwardBlowupSeq j s t) :
    IsPushforwardBlowupSeq j s' t := by
  obtain ⟨hlen, e, h0, hsqe, hce⟩ := hs
  have hpb : IsStrictPullbackBlowupSeq (𝟙 S) s' s := by
    refine ⟨hlen.symm, fun i hi => (e i (by omega)).inv, ?_, ?_, ?_⟩
    · show (e 0 (Nat.zero_le _)).inv ≫ s.isoZero.hom = s'.isoZero.hom ≫ 𝟙 S
      rw [Category.comp_id, ← h0, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    · intro i hi
      have hi' : i < s.length := by omega
      have hsq : (e (i + 1) hi').inv ≫ s.transitionMapSucc i
          = s'.transitionMapSucc i ≫ (e i hi'.le).inv := by
        rw [Iso.inv_comp_eq, ← Category.assoc, hsqe i hi', Category.assoc,
          Iso.hom_inv_id, Category.comp_id]
      show IsPullback ((e (i + 1) hi').inv) (s'.transitionMapSucc i) (s.transitionMapSucc i)
        ((e i hi'.le).inv)
      exact IsPullback.of_horiz_isIso ⟨hsq⟩
    · intro i hi
      have hi' : i < s.length := by omega
      have h1 : imageIdealSheaf (e i hi'.le).hom ((s'.center i).comap (e i hi'.le).hom)
          = imageIdealSheaf (e i hi'.le).hom (s.center i) := by rw [hce i hi']
      rw [imageIdealSheaf_comap] at h1
      have h2 : inv (e i hi'.le).hom = (e i hi'.le).inv :=
        IsIso.inv_eq_of_hom_inv_id (Iso.hom_inv_id (e i hi'.le))
      show s'.center i = (s.center i).comap ((e i hi'.le).inv)
      rw [h1, imageIdealSheaf_eq_comap_inv, h2]
  exact IsPushforwardBlowupSeq.isIso_comp (𝟙 S) j j (Category.id_comp j).symm hpb h

end IsPushforwardBlowupSeq

end FunctorialResolution.EmbeddedResolution
