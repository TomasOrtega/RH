import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreProjectiveEmbeddingFactorsProperStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleChartProductAtClosedPointClosedFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackRestrictISupOfForallRestrictStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothISupOpensCompOfForallSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFieldPointsClosedFibreSameProjectiveImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfClosedPointsClosedFibreMemStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ _ hR M G' _ _ hG E`. Establish `hRn : IsNoetherianRing R` using `hR.1`. Establish `hRi : IsIntegrallyClosed R` using `hR.2.2.1`. Take `⟨hΓ, hsurj⟩` from `GlobalTheory.T.appTop_bijective_and_surjective_normalDomain R M`. Take `⟨P', b, X, a, hPn, hbs, hbl, hap, -, hab, hcomm, hX, hlift⟩` from `GlobalTheory.T.closedFibre_projectiveEmbedding_factors_proper R hR M G' hG E`.

Establish `hsq : a ≫ b ≫ PSpace.str R E.N = (X.ι ≫ E.H.ι ≫ G'.hom) ≫ M.π`. Rewrite using `[← Category.assoc, hcomm, Category.assoc, E.f_over]`. Simplify using `only [Category.assoc]`. Establish `hpt : ∀ w : X.toScheme, (b ≫ PSpace.str R E.N) (a w) = M.π (G'.hom (E.H.ι (X.ι w)))`. Introduce `w`.

Use `congrArg (fun f => f w) hsq` as an intermediate fact. Simplify `this` using `[Scheme.Hom.comp_apply]`. Establish `key : ∀ c : {x : P' // IsClosed ({x} : Set P') ∧ (b ≫ PSpace.str R E.N) x = closedPoint R}, ∃ V : P'.Opens, c.1 ∈ V ∧ Smooth (V.ι ≫ b ≫ PSpace.str R E.N) ∧ IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) (V.ι ≫ b ≫ PSpace.str R E.N) M.π`. Introduce and unpack `⟨x, hx1, hx2⟩`. Use `GlobalTheory.T.exists_smooth_open_nbhd_isPullback_at_closedPoint R hR M G' hG E P' b X a hbs hbl hap hab hcomm hΓ hsurj x hx1 hx2 ?_ (hlift x hx1 hx2)` and prove the remaining obligations.

Introduce `Ω _ p p' hr he hs`. Establish `hc : ∀ t, M.π (G'.hom (E.H.ι ((p ≫ X.ι) t))) = closedPoint R`. Introduce `t`. Establish `ht : (p ≫ a) t = x`. Establish `: (p ≫ a) t ∈ Set.range (p ≫ a)` using `⟨t, rfl⟩`.

Rewrite `this` using `[hr]`. Conclude with `this`. Use `hpt (p t)` as an intermediate fact. Rewrite `ht` using `[Scheme.Hom.comp_apply]`. Rewrite `this` using `[ht, hx2]`.

Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `this.symm`. Establish `hf : (p ≫ X.ι) ≫ E.f = (p' ≫ X.ι) ≫ E.f`. Rewrite using `[Category.assoc, Category.assoc, ← hcomm, ← Category.assoc, he, Category.assoc]`. Use `GlobalTheory.T.eq_of_fieldPoints_closedFibre_same_projective_image R M G' E Ω (p ≫ X.ι) (p' ≫ X.ι) hc (by simpa only [Category.assoc] using hs) hf` as an intermediate fact.

Conclude with `(cancel_mono X.ι).1 this`. Use `choose V hxV hVs hVp using key`. Use `set U : P'.Opens := ⨆ c, V c with hUdef`. Establish `hUp : IsPullback (a ∣_ U) ((a ⁻¹ᵁ U).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) (U.ι ≫ b ≫ PSpace.str R E.N) M.π` using `GlobalTheory.T.isPullback_restrict_iSup_of_forall_restrict _ _ _ _ a _ _ _ hsq _ V hVp`. Establish `hUs : Smooth (U.ι ≫ b ≫ PSpace.str R E.N)` using `GlobalTheory.T.smooth_iSup_opens_comp_of_forall_smooth _ _ _ _ V hVs`.

Establish `hlft : LocallyOfFiniteType (b ≫ PSpace.str R E.N)`. Establish `: IsProper (PSpace.str R E.N)` using `ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R E.N`. Use `infer_instance`. Establish `hU0 : ∀ y : P', (b ≫ PSpace.str R E.N) y = closedPoint R → y ∈ U`. Use `GlobalTheory.T.mem_of_closedPoints_closedFibre_mem' R P' (b ≫ PSpace.str R E.N) hlft U ?_` and prove the remaining obligations.

Introduce `y hy1 hy2`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy1, hy2⟩, hxV _⟩`. Establish `hsep : IsSeparated (U.ι ≫ b ≫ PSpace.str R E.N)`. Establish `: IsProper (PSpace.str R E.N)` using `ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R E.N`. Use `infer_instance`.

Establish `hqc : QuasiCompact (U.ι ≫ b ≫ PSpace.str R E.N)` using `by haveI := hPn`. Establish `: CompactSpace U` using `isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (U : Set P'))`. Conclude with `(quasiCompact_iff_compactSpace _).2 this`. Set `e` to `hUp.isoPullback`. Use `⟨Near.mk (Over.mk (U.ι ≫ b ≫ PSpace.str R E.N)) hUs hsep hqc (e.inv ≫ (a ⁻¹ᵁ U).ι ≫ X.ι ≫ E.H.ι) inferInstance ?_ ?_, U.ι ≫ b, e.inv ≫ (a ⁻¹ᵁ U).ι ≫ X.ι, ?_, ?_⟩` and prove the remaining obligations.

Use `hUp.isoPullback_inv_snd` as an intermediate fact. Conclude with `this`. Introduce `g hg`. Take `⟨z, rfl⟩ : g ∈ Set.range E.H.ι` from `by rw [Scheme.Opens.range_ι]; exact E.H_all g hg`. Take `⟨w, rfl⟩ : z ∈ Set.range X.ι` from `by rw [Scheme.Opens.range_ι]; exact hX z hg`.

Establish `hw : a w ∈ U` using `hU0 _ (by rw [hpt]; exact hg)`. Take `⟨w', rfl⟩ : w ∈ Set.range (a ⁻¹ᵁ U).ι` from `by rw [Scheme.Opens.range_ι]; exact hw`. Use `⟨e.hom w', ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply e.hom, Iso.hom_inv_id_assoc]`. Simplify using `only [Scheme.Hom.comp_apply]`.

Simplify using `only [Category.assoc]`. Use `show e.inv ≫ (a ⁻¹ᵁ U).ι ≫ X.ι ≫ E.f = pullback.fst (U.ι ≫ b ≫ PSpace.str R E.N) M.π ≫ U.ι ≫ b`. Rewrite using `[← hcomm, ← Category.assoc ((a ⁻¹ᵁ U).ι), ← morphismRestrict_ι, ← Category.assoc e.inv]`. Simplify using `only [Category.assoc]`. Rewrite using `[← Category.assoc e.inv (a ∣_ U), hUp.isoPullback_inv_fst]`.
-/
theorem exists_near : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∃ (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u ∧ l ≫ E.f = pullback.fst _ _ ≫ fU := by
  intro R _ _ _ hR M G' _ _ hG E
  have hRn : IsNoetherianRing R := hR.1
  have hRi : IsIntegrallyClosed R := hR.2.2.1
  obtain ⟨hΓ, hsurj⟩ := GlobalTheory.T.appTop_bijective_and_surjective_normalDomain R M
  obtain ⟨P', b, X, a, hPn, hbs, hbl, hap, -, hab, hcomm, hX, hlift⟩ := GlobalTheory.T.closedFibre_projectiveEmbedding_factors_proper R hR M G' hG E
  have hsq : a ≫ b ≫ PSpace.str R E.N = (X.ι ≫ E.H.ι ≫ G'.hom) ≫ M.π := by
    rw [← Category.assoc, hcomm, Category.assoc, E.f_over]; simp only [Category.assoc]
  have hpt : ∀ w : X.toScheme, (b ≫ PSpace.str R E.N) (a w) = M.π (G'.hom (E.H.ι (X.ι w))) := by
    intro w
    have := congrArg (fun f => f w) hsq
    simpa [Scheme.Hom.comp_apply] using this
  have key : ∀ c : {x : P' // IsClosed ({x} : Set P') ∧ (b ≫ PSpace.str R E.N) x = closedPoint R},
      ∃ V : P'.Opens, c.1 ∈ V ∧ Smooth (V.ι ≫ b ≫ PSpace.str R E.N) ∧
        IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) (V.ι ≫ b ≫ PSpace.str R E.N) M.π := by
    rintro ⟨x, hx1, hx2⟩
    refine GlobalTheory.T.exists_smooth_open_nbhd_isPullback_at_closedPoint R hR M G' hG E P' b X a hbs hbl hap hab hcomm hΓ hsurj x hx1 hx2 ?_ (hlift x hx1 hx2)
    intro Ω _ p p' hr he hs
    have hc : ∀ t, M.π (G'.hom (E.H.ι ((p ≫ X.ι) t))) = closedPoint R := by
      intro t
      have ht : (p ≫ a) t = x := by
        have : (p ≫ a) t ∈ Set.range (p ≫ a) := ⟨t, rfl⟩
        rw [hr] at this; exact this
      have := hpt (p t)
      rw [Scheme.Hom.comp_apply] at ht
      rw [ht, hx2] at this
      rw [Scheme.Hom.comp_apply]; exact this.symm
    have hf : (p ≫ X.ι) ≫ E.f = (p' ≫ X.ι) ≫ E.f := by
      rw [Category.assoc, Category.assoc, ← hcomm, ← Category.assoc, he, Category.assoc]
    have := GlobalTheory.T.eq_of_fieldPoints_closedFibre_same_projective_image R M G' E Ω (p ≫ X.ι) (p' ≫ X.ι) hc (by simpa only [Category.assoc] using hs) hf
    exact (cancel_mono X.ι).1 this
  choose V hxV hVs hVp using key
  set U : P'.Opens := ⨆ c, V c with hUdef
  have hUp : IsPullback (a ∣_ U) ((a ⁻¹ᵁ U).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) (U.ι ≫ b ≫ PSpace.str R E.N) M.π :=
    GlobalTheory.T.isPullback_restrict_iSup_of_forall_restrict _ _ _ _ a _ _ _ hsq _ V hVp
  have hUs : Smooth (U.ι ≫ b ≫ PSpace.str R E.N) := GlobalTheory.T.smooth_iSup_opens_comp_of_forall_smooth _ _ _ _ V hVs
  have hlft : LocallyOfFiniteType (b ≫ PSpace.str R E.N) := by
    have : IsProper (PSpace.str R E.N) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R E.N
    infer_instance
  have hU0 : ∀ y : P', (b ≫ PSpace.str R E.N) y = closedPoint R → y ∈ U := by
    refine GlobalTheory.T.mem_of_closedPoints_closedFibre_mem' R P' (b ≫ PSpace.str R E.N) hlft U ?_
    intro y hy1 hy2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy1, hy2⟩, hxV _⟩
  have hsep : IsSeparated (U.ι ≫ b ≫ PSpace.str R E.N) := by
    have : IsProper (PSpace.str R E.N) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R E.N
    infer_instance
  have hqc : QuasiCompact (U.ι ≫ b ≫ PSpace.str R E.N) := by
    haveI := hPn
    have : CompactSpace U := isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (U : Set P'))
    exact (quasiCompact_iff_compactSpace _).2 this
  let e := hUp.isoPullback
  refine ⟨Near.mk (Over.mk (U.ι ≫ b ≫ PSpace.str R E.N)) hUs hsep hqc
      (e.inv ≫ (a ⁻¹ᵁ U).ι ≫ X.ι ≫ E.H.ι) inferInstance ?_ ?_,
    U.ι ≫ b, e.inv ≫ (a ⁻¹ᵁ U).ι ≫ X.ι, ?_, ?_⟩
  · have := hUp.isoPullback_inv_snd
    exact this
  · intro g hg
    obtain ⟨z, rfl⟩ : g ∈ Set.range E.H.ι := by rw [Scheme.Opens.range_ι]; exact E.H_all g hg
    obtain ⟨w, rfl⟩ : z ∈ Set.range X.ι := by rw [Scheme.Opens.range_ι]; exact hX z hg
    have hw : a w ∈ U := hU0 _ (by rw [hpt]; exact hg)
    obtain ⟨w', rfl⟩ : w ∈ Set.range (a ⁻¹ᵁ U).ι := by rw [Scheme.Opens.range_ι]; exact hw
    refine ⟨e.hom w', ?_⟩
    rw [← Scheme.Hom.comp_apply e.hom, Iso.hom_inv_id_assoc]
    simp only [Scheme.Hom.comp_apply]
  · simp only [Category.assoc]
  · show e.inv ≫ (a ⁻¹ᵁ U).ι ≫ X.ι ≫ E.f = pullback.fst (U.ι ≫ b ≫ PSpace.str R E.N) M.π ≫ U.ι ≫ b
    rw [← hcomm, ← Category.assoc ((a ⁻¹ᵁ U).ι), ← morphismRestrict_ι,
      ← Category.assoc e.inv]
    simp only [Category.assoc]
    rw [← Category.assoc e.inv (a ∣_ U), hUp.isoPullback_inv_fst]

end GlobalTheory.Mum
