import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClopRepPullback
import Development.AutomorphicArithmetic.CommutativeAlgebra.ClopRepFiniteEtaleOfConstantRank
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClopRepOfClopRepOfRank
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClopRepOfRankOfLocallyNoetherian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

/- English proof (translation)
Establish `hfl : Flat G.hom` using `inferInstance`. Establish `hlc` using `Scheme.Hom.isLocallyConstant_finrank G.hom`. Set `W : ℕ → S.Opens` to `fun n => ⟨G.hom.finrank ⁻¹' {n}, hlc.isOpen_fiber n⟩`. Establish `hW : iSup W = ⊤`. Use `top_le_iff.mp fun s _ => ?_` and prove the remaining obligations.

Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨G.hom.finrank s, rfl⟩`. Establish `key : ∀ n, IsFinite (pullback.snd Y.hom (W n).ι) ∧ Etale (pullback.snd Y.hom (W n).ι)`. Introduce `n`. Take `⟨U', hU'⟩` from `UpperTheory.exists_clopRep_pullback (W n).ι G Y U hr`. Establish `hG' : IsFinite ((Over.pullback (W n).ι).obj G).hom` using `inferInstanceAs (IsFinite (pullback.snd G.hom (W n).ι))`.

Establish `hG'' : Etale ((Over.pullback (W n).ι).obj G).hom` using `inferInstanceAs (Etale (pullback.snd G.hom (W n).ι))`. Use `UpperTheory.clopRep_finite_etale_of_constant_rank _ _ U' n hG' hG'' (fun s => ?_) hU'` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(pullback.snd G.hom (W n).ι).finrank s = n`. Rewrite using `[Scheme.Hom.finrank_pullback_snd]`. Conclude with `s.2`.

Prove the components needed by the constructor for the conclusion. Establish `: IsZariskiLocalAtTarget @IsFinite.{0}` using `by set_option backward.isDefEq.respectTransparency.types false in exact inferInstance`. Use `IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsFinite) W hW fun n => ?_` and prove the remaining obligations. Establish `h` using `pullbackRestrictIsoRestrict_hom_morphismRestrict Y.hom (W n)`. Use `(key n).1` as an intermediate fact.

Establish `e : Y.hom ∣_ W n = (pullbackRestrictIsoRestrict Y.hom (W n)).inv ≫ pullback.snd Y.hom (W n).ι`. Rewrite using `[← h, Iso.inv_hom_id_assoc]`. Rewrite using `[e]`. Use `infer_instance`. Establish `: IsZariskiLocalAtTarget @Etale.{0}` using `HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Etale.{0})`.

Use `IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Etale) W hW fun n => ?_` and prove the remaining obligations. Establish `h` using `pullbackRestrictIsoRestrict_hom_morphismRestrict Y.hom (W n)`. Use `(key n).2` as an intermediate fact. Establish `e : Y.hom ∣_ W n = (pullbackRestrictIsoRestrict Y.hom (W n)).inv ≫ pullback.snd Y.hom (W n).ι`. Rewrite using `[← h, Iso.inv_hom_id_assoc]`.

Rewrite using `[e]`. Use `infer_instance`.
-/
private theorem UpperTheory.RepresentationRank.finite_etale_of_rep {S : Scheme.{0}} (G Y : Over S) (U : (Y ⊗ G).left.Opens)
    (hf : IsFinite G.hom) (he : Etale G.hom) (hr : UpperTheory.RepresentationRank.Rep G Y U) :
    IsFinite Y.hom ∧ Etale Y.hom := by
  have hfl : Flat G.hom := inferInstance
  have hlc := Scheme.Hom.isLocallyConstant_finrank G.hom
  let W : ℕ → S.Opens := fun n => ⟨G.hom.finrank ⁻¹' {n}, hlc.isOpen_fiber n⟩
  have hW : iSup W = ⊤ := by
    refine top_le_iff.mp fun s _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨G.hom.finrank s, rfl⟩
  have key : ∀ n, IsFinite (pullback.snd Y.hom (W n).ι) ∧ Etale (pullback.snd Y.hom (W n).ι) := by
    intro n
    obtain ⟨U', hU'⟩ := UpperTheory.exists_clopRep_pullback (W n).ι G Y U hr
    have hG' : IsFinite ((Over.pullback (W n).ι).obj G).hom :=
      inferInstanceAs (IsFinite (pullback.snd G.hom (W n).ι))
    have hG'' : Etale ((Over.pullback (W n).ι).obj G).hom :=
      inferInstanceAs (Etale (pullback.snd G.hom (W n).ι))
    refine UpperTheory.clopRep_finite_etale_of_constant_rank _ _ U' n hG' hG'' (fun s => ?_) hU'
    change (pullback.snd G.hom (W n).ι).finrank s = n
    rw [Scheme.Hom.finrank_pullback_snd]
    exact s.2
  constructor
  · have : IsZariskiLocalAtTarget @IsFinite.{0} := by
      set_option backward.isDefEq.respectTransparency.types false in exact inferInstance
    refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsFinite) W hW fun n => ?_
    have h := pullbackRestrictIsoRestrict_hom_morphismRestrict Y.hom (W n)
    have := (key n).1
    have e : Y.hom ∣_ W n = (pullbackRestrictIsoRestrict Y.hom (W n)).inv ≫ pullback.snd Y.hom (W n).ι := by
      rw [← h, Iso.inv_hom_id_assoc]
    rw [e]
    infer_instance
  · have : IsZariskiLocalAtTarget @Etale.{0} :=
      HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Etale.{0})
    refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Etale) W hW fun n => ?_
    have h := pullbackRestrictIsoRestrict_hom_morphismRestrict Y.hom (W n)
    have := (key n).2
    have e : Y.hom ∣_ W n = (pullbackRestrictIsoRestrict Y.hom (W n)).inv ≫ pullback.snd Y.hom (W n).ι := by
      rw [← h, Iso.inv_hom_id_assoc]
    rw [e]
    infer_instance

/- English proof (translation)
Introduce `S _ G hf he`. Use `choose Y U h using UpperTheory.exists_clopRepOfRank_of_locallyNoetherian S G hf he`. Take `⟨Y', U', hr⟩` from `UpperTheory.exists_clopRep_of_clopRepOfRank G hf he Y U h`. Take `⟨h1, h2⟩` from `UpperTheory.RepresentationRank.finite_etale_of_rep G Y' U' hf he hr`. Conclude with `⟨Y', U', h1, h2, hr.1, hr.2⟩`.
-/
theorem UpperTheory.Cb.exists_finite_etale_representing_clopen_subschemes :
    ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S), IsFinite G.hom → Etale G.hom → ∃ (Y : Over S) (U : (Y ⊗ G).left.Opens), IsFinite Y.hom ∧ Etale Y.hom ∧ IsClosed (U : Set (Y ⊗ G).left) ∧ ∀ (T : Over S) (V : (T ⊗ G).left.Opens), IsClosed (V : Set (T ⊗ G).left) → ∃! y : T ⟶ Y, (y ▷ G).left ⁻¹ᵁ U = V := by
  intro S _ G hf he
  choose Y U h using UpperTheory.exists_clopRepOfRank_of_locallyNoetherian S G hf he
  obtain ⟨Y', U', hr⟩ := UpperTheory.exists_clopRep_of_clopRepOfRank G hf he Y U h
  obtain ⟨h1, h2⟩ := UpperTheory.RepresentationRank.finite_etale_of_rep G Y' U' hf he hr
  exact ⟨Y', U', h1, h2, hr.1, hr.2⟩
