import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.AbelianSchemeSpreadsOverLocalization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitelyManySectionsPointsClosedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StalkIdealRepresentsClosedSubschemeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrivialLocusRepresentsTrivialityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedFibreStructureCohomologyFiniteStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.CompanionTheory.FirstCohomologyLowerBound

/- English proof (translation)
Establish `hm : IsLocalRing.maximalIdeal R ∈ I.minimalPrimes`. Take `⟨p, hp⟩` from `Ideal.nonempty_minimalPrimes hne`. Rewrite using `[← hI p hp.1.1 hp.1.2]` and apply the resulting hypothesis. Establish `h1` using `Ideal.height_le_spanRank_toENat_of_mem_minimal_primes I _ hm`. Establish `h2 : Submodule.spanRank I ≤ n`.

Rewrite using `[← hf]`. Use `(Submodule.spanRank_span_le_card (R := R) (Set.range f)).trans (Cardinal.mk_range_le.trans ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `h3 : (IsLocalRing.maximalIdeal R).height ≤ n`. Use `h1.trans ?_` and prove the remaining obligations.

Simplify using `using Cardinal.toENat.monotone' h2`. Establish `h4 : (((IsLocalRing.maximalIdeal R).height : ℕ∞) : WithBot ℕ∞) = ((g : ℕ∞) : WithBot ℕ∞)` using `(IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)).trans hg`. Rewrite `h3` using `[WithBot.coe_inj.1 h4]`. Conclude with `h3` after adjusting the coercions.
-/
theorem dim_le (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (g n : ℕ) (hg : ringKrullDim R = g)
    (I : Ideal R) (hne : I ≠ ⊤) (hI : ∀ q : Ideal R, q.IsPrime → I ≤ q → q = IsLocalRing.maximalIdeal R)
    (f : Fin n → R) (hf : Ideal.span (Set.range f) = I) : g ≤ n := by
  have hm : IsLocalRing.maximalIdeal R ∈ I.minimalPrimes := by
    obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hne
    rwa [← hI p hp.1.1 hp.1.2]
  have h1 := Ideal.height_le_spanRank_toENat_of_mem_minimal_primes I _ hm
  have h2 : Submodule.spanRank I ≤ n := by
    rw [← hf]
    refine (Submodule.spanRank_span_le_card (R := R) (Set.range f)).trans (Cardinal.mk_range_le.trans ?_)
    simp
  have h3 : (IsLocalRing.maximalIdeal R).height ≤ n := by
    refine h1.trans ?_
    simpa using Cardinal.toENat.monotone' h2
  have h4 : (((IsLocalRing.maximalIdeal R).height : ℕ∞) : WithBot ℕ∞) = ((g : ℕ∞) : WithBot ℕ∞) :=
    (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)).trans hg
  rw [WithBot.coe_inj.1 h4] at h3
  exact_mod_cast h3

/- English proof (translation)
Use `haveI := hA.proper`. Take `⟨M, hM⟩` from `GlobalTheory.exists_isAmpleLB_of_isProjOver (PositivityTheory.Xgn.AbelianSchemeSpreading.isProjOver_abelian k A hA)`. Conclude with `⟨M, hM.isLB, (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A hM.isLB).2 hM⟩`.
-/
theorem exists_ample (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (hA : IsAbelianScheme A) :
    ∃ L : LB A.left, L.IsLB ∧ Out.RelAmple A L := by
  haveI := hA.proper
  obtain ⟨M, hM⟩ := GlobalTheory.exists_isAmpleLB_of_isProjOver (PositivityTheory.Xgn.AbelianSchemeSpreading.isProjOver_abelian k A hA)
  exact ⟨M, hM.isLB, (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A hM.isLB).2 hM⟩

/- English proof (translation)
Rewrite using `[evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst, lift_snd]`.
-/
theorem evc_lam' {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hP : (abelian₂ A L).IsLB)
    {Y : Over S} (a b : Y ⟶ A) : evc hP a b = lam (cls L hL) a b := by
  rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
    lift_snd]

/- English proof (translation)
Establish `hP : (abelian₂ A L).IsLB` using `LB.isLB_linComb hL _ _`. Rewrite using `[triv_ev_iff hP, evc_lam' hL, lam_one_left]`.
-/
theorem triv_lam_one {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (hL : L.IsLB) :
    Triv (ev (abelian₂ A L) (1 : A ⟶ A) (𝟙 A)) := by
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  rw [triv_ev_iff hP, evc_lam' hL, lam_one_left]

/- English proof (translation)
Establish `hP : (abelian₂ A L).IsLB` using `LB.isLB_linComb hL _ _`. Use `(h.2 T 1).1 ?_` and prove the remaining obligations. Rewrite using `[triv_ev_iff hP, evc_lam' hL, MonObj.comp_one, lam_one_right]`.
-/
theorem one_mem_locus {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (hL : L.IsLB)
    (Z : Over S) (i : Z ⟶ A) (h : PositivityTheory.ObstructionTrivialLocus.IsTrivLocus A (abelian₂ A L) i) (T : Over S) :
    ∃ z : T ⟶ Z, z ≫ i = 1 := by
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  refine (h.2 T 1).1 ?_
  rw [triv_ev_iff hP, evc_lam' hL, MonObj.comp_one, lam_one_right]

/- English proof (translation)
Establish `h : IsPullback (fst A T).left (snd A T).left A.hom T.hom` using `IsPullback.of_hasPullback _ _`. Conclude with `⟨MorphismProperty.of_isPullback h inferInstance, MorphismProperty.of_isPullback h inferInstance⟩`.
-/
theorem snd_smooth_proper {S : Scheme.{0}} (A T : Over S) [Smooth A.hom] [IsProper A.hom] :
    Smooth (snd A T).left ∧ IsProper (snd A T).left := by
  have h : IsPullback (fst A T).left (snd A T).left A.hom T.hom := IsPullback.of_hasPullback _ _
  exact ⟨MorphismProperty.of_isPullback h inferInstance, MorphismProperty.of_isPullback h inferInstance⟩

/- English proof (translation)
Establish `hP : (abelian₂ A L).IsLB` using `LB.isLB_linComb hL _ _`. Rewrite `h`, the goal using `[triv_ev_iff hP]`. Establish `e` using `congrArg (CechPic.pull (lift (snd T A) (fst T A)).left) h`. Rewrite `e` using `[pull_evc, map_zero, lift_fst, lift_snd_assoc, evc_lam' hL, lam_comm]`. Rewrite using `[evc_lam' hL]` and apply the resulting hypothesis.
-/
theorem lam_triv_left {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB)
    {T : Over S} (x : T ⟶ A) (h : Triv (ev (abelian₂ A L) (fst A T) (snd A T ≫ x))) :
    Triv (ev (abelian₂ A L) (fst T A ≫ x) (snd T A)) := by
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  rw [triv_ev_iff hP] at h ⊢
  have e := congrArg (CechPic.pull (lift (snd T A) (fst T A)).left) h
  rw [pull_evc, map_zero, lift_fst, lift_snd_assoc, evc_lam' hL, lam_comm] at e
  rwa [evc_lam' hL]

/- English proof (translation)
Use `haveI := hA.comm`. Use `haveI : IsClosedImmersion i.left := h.1`. Establish `hF` using `hK (Sp k) A hA L hL hamp k (𝟙 _)`. Use `Set.Finite.of_finite_image (f := fun σ ↦ σ ≫ i.left) ((hF.image fun x ↦ x.left).subset ?_) (fun a _ b _ e ↦ (cancel_mono i.left).1 e)` and prove the remaining obligations. Introduce and unpack `_ ⟨σ, hσ, rfl⟩`.

Set `z : Over.mk (𝟙 (Sp k)) ⟶ Z` to `Over.homMk σ hσ`. Use `⟨z ≫ i, lam_triv_left hL _ ((h.2 _ _).2 ⟨z, rfl⟩), rfl⟩` and prove the remaining obligations.
-/
theorem finite_sections (hK : PositivityTheory.ObstructionTrivialLocus.KFinite) (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A]
    (hA : IsAbelianScheme A) (L : LB A.left) (hL : L.IsLB) (hamp : Out.RelAmple A L) (Z : Over (Sp k)) (i : Z ⟶ A)
    (h : PositivityTheory.ObstructionTrivialLocus.IsTrivLocus A (abelian₂ A L) i) : Set.Finite {σ : Sp k ⟶ Z.left | σ ≫ Z.hom = 𝟙 _} := by
  haveI := hA.comm
  haveI : IsClosedImmersion i.left := h.1
  have hF := hK (Sp k) A hA L hL hamp k (𝟙 _)
  refine Set.Finite.of_finite_image (f := fun σ ↦ σ ≫ i.left) ((hF.image fun x ↦ x.left).subset ?_)
    (fun a _ b _ e ↦ (cancel_mono i.left).1 e)
  rintro _ ⟨σ, hσ, rfl⟩
  let z : Over.mk (𝟙 (Sp k)) ⟶ Z := Over.homMk σ hσ
  refine ⟨z ≫ i, lam_triv_left hL _ ((h.2 _ _).2 ⟨z, rfl⟩), rfl⟩

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem stalk_local (X : Scheme.{0}) (x : X) : IsLocalRing (X.presheaf.stalk x) := inferInstance

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem stalk_noeth (X : Scheme.{0}) [IsLocallyNoetherian X] (x : X) : IsNoetherianRing (X.presheaf.stalk x) :=
  inferInstance

/- English proof (translation)
Set `T : Over (Sp k)` to `Over.mk (y₀ ≫ A.hom)`. Set `y : T ⟶ A` to `Over.homMk y₀ rfl`. Establish `hs` using `snd_smooth_proper A T`. Take `⟨f, hf⟩` from `hFew R (A ⊗ T).left (snd A T).left (Module.finrank k (HO1 A.hom)) hs.1 hs.2 (fun X' s' φ h ↦ GlobalTheory.T.closed_fibre_structure_cohomology_finite hFB k A hfin R _ X' s' φ h) (ev N (fst A T) (snd A T ≫ y)) (pull_isLB hN _) I hne (fun J ↦ (GlobalTheory.T.trivial_locus_represents …`. Conclude with `dim_le R g _ hdim I hne hrad f hf`.
-/
theorem core (hFew : FewEqSt) (hFB : FlatBCSt) (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] [Smooth A.hom]
    [IsProper A.hom] (hfin : Module.Finite k (HO1 A.hom)) (N : LB (A ⊗ A).left) (hN : N.IsLB) (Z : Over (Sp k))
    (i : Z ⟶ A) (hi : PositivityTheory.ObstructionTrivialLocus.IsTrivLocus A N i) (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (y₀ : Sp R ⟶ A.left) (g : ℕ) (hdim : ringKrullDim R = g) (I : Ideal R) (hne : I ≠ ⊤)
    (hrad : ∀ q : Ideal R, q.IsPrime → I ≤ q → q = IsLocalRing.maximalIdeal R)
    (hJ : ∀ J : Ideal R, (∃ z : Sp (R ⧸ J) ⟶ Z.left, z ≫ i.left = spMap (Ideal.Quotient.mk J) ≫ y₀) ↔ I ≤ J) :
    g ≤ Module.finrank k (HO1 A.hom) := by
  let T : Over (Sp k) := Over.mk (y₀ ≫ A.hom)
  let y : T ⟶ A := Over.homMk y₀ rfl
  have hs := snd_smooth_proper A T
  obtain ⟨f, hf⟩ := hFew R (A ⊗ T).left (snd A T).left (Module.finrank k (HO1 A.hom))
    hs.1 hs.2 (fun X' s' φ h ↦ GlobalTheory.T.closed_fibre_structure_cohomology_finite hFB k A hfin R _ X' s' φ h)
    (ev N (fst A T) (snd A T ≫ y)) (pull_isLB hN _) I hne
    (fun J ↦ (GlobalTheory.T.trivial_locus_represents_triviality A A Z N hN i hi T y (spMap (Ideal.Quotient.mk J))).trans (hJ J))
  exact dim_le R g _ hdim I hne hrad f hf

/- English proof (translation)
Introduce `hTL hKF hFB hFew hSD k _ _ A _ g hA hsm hfin`. Take `⟨L, hL, hamp⟩` from `exists_ample k A hA`. Use `haveI := hA.comm`. Use `haveI := hA.smooth`. Use `haveI := hA.proper`.

Establish `hP : (abelian₂ A L).IsLB` using `LB.isLB_linComb hL _ _`. Use `haveI hnoeth : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom`. Take `⟨Z, i, hi⟩` from `hTL (Sp k) A A hA hnoeth (abelian₂ A L) hP (triv_lam_one A L hL)`. Use `haveI : IsClosedImmersion i.left := hi.1`. Use `haveI : LocallyOfFiniteType Z.hom := by`.

Rewrite using `[← Over.w i]`. Use `infer_instance`. Establish `hcl` using `GlobalTheory.T.finitely_many_sections_points_closed k Z.left Z.hom (finite_sections hKF k A hA L hL hamp Z i hi)`. Set `e : Sp k ⟶ A.left` to `(1 : Over.mk (𝟙 (Sp k)) ⟶ A).left`. Establish `he : e ≫ A.hom = 𝟙 _` using `Over.w (1 : Over.mk (𝟙 (Sp k)) ⟶ A)`.

Set `p : Sp k` to `IsLocalRing.closedPoint k`. Take `⟨z, hz⟩` from `one_mem_locus A L hL Z i hi (Over.mk (𝟙 (Sp k)))`. Establish `hx : e.base p ∈ Set.range i.left` using `⟨z.left.base p, by`. Establish `: z.left ≫ i.left = e` using `congrArg (fun q ↦ q.left) hz`. Rewrite using `[← this]`.

Use the proof step `rfl⟩`. Establish `hd` using `hSD k A.left A.hom e g he hsm p`. Generalize the expression as in `(e.base p : A.left) = x at hx hd`. Take `⟨I, hne, hrad, hJ⟩` from `GlobalTheory.T.stalk_ideal_represents_closed_subscheme A.left Z.left i.left x hx hcl`. Conclude with `@core hFew hFB k _ A _ _ _ hfin (abelian₂ A L) hP Z i hi (A.left.presheaf.stalk x) _ (stalk_local A.left x) (stalk_noeth A.left x) (A.left.fromSpecStalk x) g hd I hne hrad hJ`.
-/
theorem first_cohomology_dimension_lower_bound : PositivityTheory.ObstructionTrivialLocus.TrivLocus → PositivityTheory.ObstructionTrivialLocus.KFinite → FlatBCSt → FewEqSt → StalkDimSt → H1DimGeAbelianDim := by
  intro hTL hKF hFB hFew hSD k _ _ A _ g hA hsm hfin
  obtain ⟨L, hL, hamp⟩ := exists_ample k A hA
  haveI := hA.comm
  haveI := hA.smooth
  haveI := hA.proper
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  haveI hnoeth : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  obtain ⟨Z, i, hi⟩ := hTL (Sp k) A A hA hnoeth (abelian₂ A L) hP (triv_lam_one A L hL)
  haveI : IsClosedImmersion i.left := hi.1
  haveI : LocallyOfFiniteType Z.hom := by
    rw [← Over.w i]
    infer_instance
  have hcl := GlobalTheory.T.finitely_many_sections_points_closed k Z.left Z.hom (finite_sections hKF k A hA L hL hamp Z i hi)
  let e : Sp k ⟶ A.left := (1 : Over.mk (𝟙 (Sp k)) ⟶ A).left
  have he : e ≫ A.hom = 𝟙 _ := Over.w (1 : Over.mk (𝟙 (Sp k)) ⟶ A)
  let p : Sp k := IsLocalRing.closedPoint k
  obtain ⟨z, hz⟩ := one_mem_locus A L hL Z i hi (Over.mk (𝟙 (Sp k)))
  have hx : e.base p ∈ Set.range i.left := ⟨z.left.base p, by
    have : z.left ≫ i.left = e := congrArg (fun q ↦ q.left) hz
    rw [← this]; rfl⟩
  have hd := hSD k A.left A.hom e g he hsm p
  generalize (e.base p : A.left) = x at hx hd
  obtain ⟨I, hne, hrad, hJ⟩ := GlobalTheory.T.stalk_ideal_represents_closed_subscheme A.left Z.left i.left x hx hcl
  exact @core hFew hFB k _ A _ _ _ hfin (abelian₂ A L) hP Z i hi (A.left.presheaf.stalk x) _ (stalk_local A.left x)
    (stalk_noeth A.left x) (A.left.fromSpecStalk x) g hd I hne hrad hJ

end GlobalTheory.CompanionTheory.FirstCohomologyLowerBound
