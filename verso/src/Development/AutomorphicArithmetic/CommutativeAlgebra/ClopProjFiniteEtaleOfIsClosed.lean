import Mathlib
import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

/- English proof (translation)
The claim follows from `IsPullback.of_hasPullback T.hom G.hom`.
-/
private lemma UpperTheory.isPullback_fst_snd_over {S : Scheme.{0}} {T G : Over S} :
    IsPullback (fst T G).left (snd T G).left T.hom G.hom :=
  IsPullback.of_hasPullback T.hom G.hom

/- English proof (translation)
Introduce `S T G V hf he hV`. Establish `hpb : IsPullback (snd T G).left (fst T G).left G.hom T.hom` using `UpperTheory.isPullback_fst_snd_over.flip`. Use `haveI : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hV)`. Use `haveI : IsFinite (fst T G).left := MorphismProperty.of_isPullback (P := @IsFinite) hpb hf`. Use `haveI : Etale (fst T G).left := MorphismProperty.of_isPullback (P := @Etale) hpb he`.

Conclude with `⟨inferInstanceAs (IsFinite (V.ι ≫ (fst T G).left)), inferInstanceAs (Etale (V.ι ≫ (fst T G).left))⟩`.
-/
theorem UpperTheory.clopProj_finite_etale_of_isClosed :
    ∀ {S : Scheme.{0}} {T G : Over S} (V : (T ⊗ G).left.Opens), IsFinite G.hom → Etale G.hom → IsClosed (V : Set (T ⊗ G).left) → IsFinite (UpperTheory.RepresentationRank.proj V) ∧ Etale (UpperTheory.RepresentationRank.proj V) := by
  intro S T G V hf he hV
  have hpb : IsPullback (snd T G).left (fst T G).left G.hom T.hom := UpperTheory.isPullback_fst_snd_over.flip
  haveI : IsClosedImmersion V.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hV)
  haveI : IsFinite (fst T G).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) hpb hf
  haveI : Etale (fst T G).left :=
    MorphismProperty.of_isPullback (P := @Etale) hpb he
  exact ⟨inferInstanceAs (IsFinite (V.ι ≫ (fst T G).left)),
    inferInstanceAs (Etale (V.ι ≫ (fst T G).left))⟩
