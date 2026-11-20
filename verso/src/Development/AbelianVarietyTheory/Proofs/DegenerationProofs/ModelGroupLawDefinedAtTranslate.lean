import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelMapGenericallyOpenImmersionCalculusStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TranslationBySection
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GlobalTheory.SS.LawDef
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' : Over (Sp K)}

/- English proof (translation)
Establish `h2` using `congrArg (fun q => q.left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))) h`. Establish `h4 : ((Over.pullback (spMap (algebraMap R K))).map g).left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K)) = pullback.fst M.Y.hom (spMap (algebraMap R K)) ≫ g.left` using `pullback.lift_fst _ _ _`. Simplify using `only [Over.comp_left, Category.assoc] at h2`. Unfold `Model.j`. Rewrite using `[Category.assoc]`.

Conclude with `(congrArg (fun q => M.e.inv.left ≫ q) h4).symm.trans h2`.
-/
theorem j_comm (M : Model R A) (N : Model R A') (f : A ⟶ A') (g : M.Y ⟶ N.Y)
    (h : M.e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map g = f ≫ N.e.inv) : M.j ≫ g.left = f.left ≫ N.j := by
  have h2 := congrArg (fun q => q.left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))) h
  have h4 : ((Over.pullback (spMap (algebraMap R K))).map g).left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))
      = pullback.fst M.Y.hom (spMap (algebraMap R K)) ≫ g.left := pullback.lift_fst _ _ _
  simp only [Over.comp_left, Category.assoc] at h2
  unfold Model.j
  rw [Category.assoc]
  exact (congrArg (fun q => M.e.inv.left ≫ q) h4).symm.trans h2

/- English proof (translation)
Conclude with `j_comm (M.prod N) M (fst A A') (fst M.Y N.Y) (by simp [Model.prod])`.
-/
theorem prod_j_fst (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (fst M.Y N.Y).left = (fst A A').left ≫ M.j := by
  exact j_comm (M.prod N) M (fst A A') (fst M.Y N.Y) (by simp [Model.prod])

/- English proof (translation)
Conclude with `j_comm (M.prod N) N (snd A A') (snd M.Y N.Y) (by simp [Model.prod])`.
-/
theorem prod_j_snd (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (snd M.Y N.Y).left = (snd A A').left ≫ N.j := by
  exact j_comm (M.prod N) N (snd A A') (snd M.Y N.Y) (by simp [Model.prod])

/- English proof (translation)
The claim follows from `pullback.hom_ext h1 h2`.
-/
theorem prod_ext (M : Model R A) (N : Model R A') {T : Scheme.{0}} {u v : T ⟶ (M.prod N).Y.left}
    (h1 : u ≫ (fst M.Y N.Y).left = v ≫ (fst M.Y N.Y).left)
    (h2 : u ≫ (snd M.Y N.Y).left = v ≫ (snd M.Y N.Y).left) : u = v :=
  pullback.hom_ext h1 h2

/- English proof (translation)
Establish `hp` using `isPullback_morphismRestrict M.j U`. Establish `e2` using `hp.lift_fst u t e`. Establish `e1` using `hp.lift_snd u t e`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ext_test {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {U : M.Y.left.Opens} {g : U.toScheme ⟶ N.Y.left}
    (h : Extends M N f U g) {T : Scheme.{0}} (t : T ⟶ A.left) (u : T ⟶ U.toScheme) (e : u ≫ U.ι = t ≫ M.j) :
    u ≫ g = t ≫ f.left ≫ N.j := by
  have hp := isPullback_morphismRestrict M.j U
  have e2 := hp.lift_fst u t e
  have e1 := hp.lift_snd u t e
  calc u ≫ g = hp.lift u t e ≫ (M.j ∣_ U) ≫ g := by rw [← Category.assoc, e2]
    _ = _ := by rw [h.2, ← Category.assoc, e1]

/- English proof (translation)
Use `⟨i.opensRange, i.isoOpensRange.inv ≫ g, ⟨y, rfl⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, h1, Scheme.Hom.isoOpensRange_inv_comp_assoc]`. Rewrite using `[← Category.assoc]`. Apply `h2` to reduce the goal to its premises. Rewrite using `[Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]`.
-/
theorem defAt_mk (M : Model R A) (N : Model R A') (f : A ⟶ A') {V : Scheme.{0}} (i : V ⟶ M.Y.left)
    [IsOpenImmersion i] (g : V ⟶ N.Y.left) (h1 : g ≫ N.Y.hom = i ≫ M.Y.hom)
    (h2 : ∀ (T : Scheme.{0}) (t : T ⟶ A.left) (u : T ⟶ V), u ≫ i = t ≫ M.j → u ≫ g = t ≫ f.left ≫ N.j) (y : V) :
    DefAt M N f (i y) := by
  refine ⟨i.opensRange, i.isoOpensRange.inv ≫ g, ⟨y, rfl⟩, ?_, ?_⟩
  · rw [Category.assoc, h1, Scheme.Hom.isoOpensRange_inv_comp_assoc]
  · rw [← Category.assoc]
    apply h2
    rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]

/- English proof (translation)
Assemble the required witnesses or components as `⟨by simp, by rw [morphismRestrict_ι_assoc, h]⟩`.
-/
theorem defAt_global (M : Model R A) (N : Model R A') (f : A ⟶ A') (g : M.Y ⟶ N.Y)
    (h : M.j ≫ g.left = f.left ≫ N.j) : Extends M N f ⊤ ((⊤ : M.Y.left.Opens).ι ≫ g.left) :=
  ⟨by simp, by rw [morphismRestrict_ι_assoc, h]⟩

/- English proof (translation)
Take `⟨V, g', hy, h'⟩` from `h'`. Use `defAt_mk M P (f ≫ f') ((g ⁻¹ᵁ V).ι ≫ U.ι) ((g ∣_ V) ≫ g') ?_ ?_ ⟨y, hy⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, h'.1, morphismRestrict_ι_assoc, h.1, Category.assoc]`. Introduce `T t u e`. Establish `e1` using `ext_test h t (u ≫ (g ⁻¹ᵁ V).ι) (by rw [Category.assoc, e])`.

Establish `e2` using `ext_test h' (t ≫ f.left) (u ≫ (g ∣_ V)) (by`. Rewrite using `[Category.assoc, morphismRestrict_ι, ← Category.assoc, e1, Category.assoc])`. Rewrite using `[← Category.assoc, e2, Over.comp_left, Category.assoc, Category.assoc]`.
-/
theorem defAt_comp {M : Model R A} {N : Model R A'} {P : Model R A''} {f : A ⟶ A'} {f' : A' ⟶ A''}
    {U : M.Y.left.Opens} {g : U.toScheme ⟶ N.Y.left} (h : Extends M N f U g) (y : U.toScheme)
    (h' : DefAt N P f' (g y)) : DefAt M P (f ≫ f') (U.ι y) := by
  obtain ⟨V, g', hy, h'⟩ := h'
  refine defAt_mk M P (f ≫ f') ((g ⁻¹ᵁ V).ι ≫ U.ι) ((g ∣_ V) ≫ g') ?_ ?_ ⟨y, hy⟩
  · rw [Category.assoc, h'.1, morphismRestrict_ι_assoc, h.1, Category.assoc]
  · intro T t u e
    have e1 := ext_test h t (u ≫ (g ⁻¹ᵁ V).ι) (by rw [Category.assoc, e])
    have e2 := ext_test h' (t ≫ f.left) (u ≫ (g ∣_ V)) (by
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, e1, Category.assoc])
    rw [← Category.assoc, e2, Over.comp_left, Category.assoc, Category.assoc]

/- English proof (translation)
Take `⟨U, g, hy, h⟩` from `h`. Conclude with `defAt_comp h ⟨y, hy⟩ (h' _)`.
-/
theorem defAt_comp_all {M : Model R A} {N : Model R A'} {P : Model R A''} {f : A ⟶ A'} {f' : A' ⟶ A''}
    {y : M.Y.left} (h : DefAt M N f y) (h' : ∀ w, DefAt N P f' w) : DefAt M P (f ≫ f') y := by
  obtain ⟨U, g, hy, h⟩ := h
  exact defAt_comp h ⟨y, hy⟩ (h' _)

/- English proof (translation)
Take `⟨U, g, hy, h⟩` from `h`. Take `⟨V, g', hy', h'⟩` from `h'`. Set `i₁` to `M.Y.left.homOfLE (inf_le_left : U ⊓ V ≤ U)`. Set `i₂` to `M.Y.left.homOfLE (inf_le_right : U ⊓ V ≤ V)`. Establish `e₁ : i₁ ≫ U.ι = (U ⊓ V).ι` using `Scheme.homOfLE_ι _ _`.

Establish `e₂ : i₂ ≫ V.ι = (U ⊓ V).ι` using `Scheme.homOfLE_ι _ _`. Establish `w : (i₁ ≫ g) ≫ N.Y.hom = (i₂ ≫ g') ≫ P.Y.hom`. Rewrite using `[Category.assoc, Category.assoc, h.1, h'.1, reassoc_of% e₁, reassoc_of% e₂]`. Set `G : (U ⊓ V).toScheme ⟶ (N.prod P).Y.left` to `pullback.lift _ _ w`. Establish `G1 : G ≫ (fst N.Y P.Y).left = i₁ ≫ g` using `pullback.lift_fst _ _ _`.

Establish `G2 : G ≫ (snd N.Y P.Y).left = i₂ ≫ g'` using `pullback.lift_snd _ _ _`. Use `defAt_mk M (N.prod P) _ (U ⊓ V).ι G ?_ ?_ ⟨y, hy, hy'⟩` and prove the remaining obligations. Establish `: (N.prod P).Y.hom = (fst N.Y P.Y).left ≫ N.Y.hom` using `(Over.w (fst N.Y P.Y)).symm`. Rewrite using `[this, reassoc_of% G1, h.1, reassoc_of% e₁]`. Introduce `T t u e`.

Apply `prod_ext` to reduce the goal to its premises. Use `ext_test h t (u ≫ i₁) (by rw [Category.assoc, e₁, e])` as an intermediate fact. Simplify using `only [Category.assoc] at this ⊢`. Rewrite using `[G1, this, prod_j_fst, ← Over.comp_left_assoc, lift_fst]`. Use `ext_test h' t (u ≫ i₂) (by rw [Category.assoc, e₂, e])` as an intermediate fact.

Simplify using `only [Category.assoc] at this ⊢`. Rewrite using `[G2, this, prod_j_snd, ← Over.comp_left_assoc, lift_snd]`.
-/
theorem defAt_lift {M : Model R A} {N : Model R A'} {P : Model R A''} {f : A ⟶ A'} {f' : A ⟶ A''}
    {y : M.Y.left} (h : DefAt M N f y) (h' : DefAt M P f' y) : DefAt M (N.prod P) (lift f f') y := by
  obtain ⟨U, g, hy, h⟩ := h
  obtain ⟨V, g', hy', h'⟩ := h'
  let i₁ := M.Y.left.homOfLE (inf_le_left : U ⊓ V ≤ U)
  let i₂ := M.Y.left.homOfLE (inf_le_right : U ⊓ V ≤ V)
  have e₁ : i₁ ≫ U.ι = (U ⊓ V).ι := Scheme.homOfLE_ι _ _
  have e₂ : i₂ ≫ V.ι = (U ⊓ V).ι := Scheme.homOfLE_ι _ _
  have w : (i₁ ≫ g) ≫ N.Y.hom = (i₂ ≫ g') ≫ P.Y.hom := by
    rw [Category.assoc, Category.assoc, h.1, h'.1, reassoc_of% e₁, reassoc_of% e₂]
  let G : (U ⊓ V).toScheme ⟶ (N.prod P).Y.left := pullback.lift _ _ w
  have G1 : G ≫ (fst N.Y P.Y).left = i₁ ≫ g := pullback.lift_fst _ _ _
  have G2 : G ≫ (snd N.Y P.Y).left = i₂ ≫ g' := pullback.lift_snd _ _ _
  refine defAt_mk M (N.prod P) _ (U ⊓ V).ι G ?_ ?_ ⟨y, hy, hy'⟩
  · have : (N.prod P).Y.hom = (fst N.Y P.Y).left ≫ N.Y.hom := (Over.w (fst N.Y P.Y)).symm
    rw [this, reassoc_of% G1, h.1, reassoc_of% e₁]
  · intro T t u e
    apply prod_ext
    · have := ext_test h t (u ≫ i₁) (by rw [Category.assoc, e₁, e])
      simp only [Category.assoc] at this ⊢
      rw [G1, this, prod_j_fst, ← Over.comp_left_assoc, lift_fst]
    · have := ext_test h' t (u ≫ i₂) (by rw [Category.assoc, e₂, e])
      simp only [Category.assoc] at this ⊢
      rw [G2, this, prod_j_snd, ← Over.comp_left_assoc, lift_snd]

/- English proof (translation)
Take `⟨U, g, hy, h1, h2⟩` from `h`. Use `⟨U, g, hy, h1, h2.trans ?_⟩` and prove the remaining obligations. Simplify using `[Model.j, Model.twist]`.
-/
theorem defAt_twist {M : Model R A} {N : Model R A'} {f : A ⟶ A''} (t : A' ≅ A'') {y : M.Y.left}
    (h : DefAt M N (f ≫ t.inv) y) : DefAt M (N.twist t) f y := by
  obtain ⟨U, g, hy, h1, h2⟩ := h
  refine ⟨U, g, hy, h1, h2.trans ?_⟩
  simp [Model.j, Model.twist]

/- English proof (translation)
Use `isOpenImmersion_spMap_of_isDiscreteValuationRing R K` as an intermediate fact. Establish `: IsIso M.e.inv.left` using `inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))`. Establish `: IsOpenImmersion M.j` using `by unfold Model.j; infer_instance`. Choose the witnesses or unpack the hypotheses as in `⟨x, rfl⟩ : y ∈ Set.range M.j := by`. Establish `h1 : y ∈ Set.range (pullback.fst M.Y.hom (spMap (algebraMap R K)))`.

Rewrite using `[Scheme.Pullback.range_fst]`. Use `⟨(⊥ : PrimeSpectrum K), ?_⟩` and prove the remaining obligations. Establish `hp : PrimeSpectrum.asIdeal (R` using `R) (M.Y.hom y) = ⊥ := by`. Assume the negation of the conclusion as `h`. Conclude with `hy (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ((M.Y.hom y).isPrime.isMaximal h)))`.

Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Rewrite using `[hp]`. Conclude with `(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)`. Take `⟨w, rfl⟩` from `h1`. Take `⟨x, rfl⟩` from `M.e.inv.left.surjective w`.

Conclude with `⟨x, rfl⟩`. Use `defAt_mk M N f M.j (f.left ≫ N.j) ?_ ?_ x` and prove the remaining obligations. Rewrite using `[Category.assoc, N.j_hom, M.j_hom, Over.w_assoc]`. Introduce `T t u e`. Rewrite using `[(cancel_mono _).1 e]`.
-/
theorem defAt_generic [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    (M : Model R A) (N : Model R A') (f : A ⟶ A') (y : M.Y.left) (hy : y ∉ M.sp) : DefAt M N f y := by
  have := isOpenImmersion_spMap_of_isDiscreteValuationRing R K
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  have : IsOpenImmersion M.j := by unfold Model.j; infer_instance
  obtain ⟨x, rfl⟩ : y ∈ Set.range M.j := by
    have h1 : y ∈ Set.range (pullback.fst M.Y.hom (spMap (algebraMap R K))) := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨(⊥ : PrimeSpectrum K), ?_⟩
      have hp : PrimeSpectrum.asIdeal (R := R) (M.Y.hom y) = ⊥ := by
        by_contra h
        exact hy (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ((M.Y.hom y).isPrime.isMaximal h)))
      apply PrimeSpectrum.ext
      rw [hp]
      exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)
    obtain ⟨w, rfl⟩ := h1
    obtain ⟨x, rfl⟩ := M.e.inv.left.surjective w
    exact ⟨x, rfl⟩
  refine defAt_mk M N f M.j (f.left ≫ N.j) ?_ ?_ x
  · rw [Category.assoc, N.j_hom, M.j_hom, Over.w_assoc]
  · intro T t u e
    rw [(cancel_mono _).1 e]

/- English proof (translation)
Rewrite using `[isOpen_iff_forall_mem_open]`. Introduce and unpack `y ⟨U, g, hy, h⟩`. Conclude with `⟨U, fun w hw => ⟨U, g, hw, h⟩, U.isOpen, hy⟩`.
-/
theorem isOpen_isoAt (M : Model R A) (N : Model R A') (f : A ⟶ A') : IsOpen {y | IsoAt M N f y} := by
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨U, g, hy, h⟩
  exact ⟨U, fun w hw => ⟨U, g, hw, h⟩, U.isOpen, hy⟩

def Sec (M : Model R A) (p : 𝟙_ (Over (Sp K)) ⟶ A) (s : 𝟙_ (Over (Sp R)) ⟶ M.Y) : Prop :=
  p.left ≫ M.j = spMap (algebraMap R K) ≫ s.left

/- English proof (translation)
Apply `prod_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, prod_j_fst, ← Over.comp_left_assoc, lift_fst, ← Over.comp_left, lift_fst]`. Conclude with `h`. Rewrite using `[Category.assoc, Category.assoc, prod_j_snd, ← Over.comp_left_assoc, lift_snd, ← Over.comp_left, lift_snd]`. Conclude with `h'`.
-/
theorem sec_lift {M : Model R A} {N : Model R A'} {p : 𝟙_ (Over (Sp K)) ⟶ A} {q : 𝟙_ (Over (Sp K)) ⟶ A'}
    {s : 𝟙_ (Over (Sp R)) ⟶ M.Y} {t : 𝟙_ (Over (Sp R)) ⟶ N.Y} (h : Sec M p s) (h' : Sec N q t) :
    Sec (M.prod N) (lift p q) (lift s t) := by
  apply prod_ext
  · rw [Category.assoc, Category.assoc, prod_j_fst, ← Over.comp_left_assoc, lift_fst, ← Over.comp_left, lift_fst]
    exact h
  · rw [Category.assoc, Category.assoc, prod_j_snd, ← Over.comp_left_assoc, lift_snd, ← Over.comp_left, lift_snd]
    exact h'

/- English proof (translation)
Use `M.sep` as an intermediate fact. Use `isDominant_spMap_of_isFractionRing R K` as an intermediate fact. Establish `: IsReduced (𝟙_ (Over (Sp R))).left` using `inferInstanceAs (IsReduced (Sp R))`. Use `ext1`. Conclude with `ext_of_isDominant_of_isSeparated M.Y.hom ((Over.w s).trans (Over.w t).symm) (spMap (algebraMap R K)) (h.symm.trans h')`.
-/
theorem sec_unique [IsDomain R] [IsFractionRing R K] {M : Model R A} {p : 𝟙_ (Over (Sp K)) ⟶ A}
    {s t : 𝟙_ (Over (Sp R)) ⟶ M.Y} (h : Sec M p s) (h' : Sec M p t) : s = t := by
  have := M.sep
  have := isDominant_spMap_of_isFractionRing R K
  have : IsReduced (𝟙_ (Over (Sp R))).left := inferInstanceAs (IsReduced (Sp R))
  ext1
  exact ext_of_isDominant_of_isSeparated M.Y.hom ((Over.w s).trans (Over.w t).symm) (spMap (algebraMap R K))
    (h.symm.trans h')

variable [IsLocalRing R]

def sp0 {Y : Over (Sp R)} (s : 𝟙_ (Over (Sp R)) ⟶ Y) : Y.left := s.left (IsLocalRing.closedPoint R)

/- English proof (translation)
Unfold `sp0`. Rewrite using `[Over.comp_left, Scheme.Hom.comp_apply]`.
-/
theorem map_modelSectionSpecialPoint_comp {Y Z : Over (Sp R)} (s : 𝟙_ (Over (Sp R)) ⟶ Y) (g : Y ⟶ Z) : g.left (sp0 s) = sp0 (s ≫ g) := by
  unfold sp0
  rw [Over.comp_left, Scheme.Hom.comp_apply]

/- English proof (translation)
Use `show M.Y.hom (s.left _) = _`. Rewrite using `[← Scheme.Hom.comp_apply, Over.w s]`. Both sides reduce to the same expression.
-/
theorem modelSectionSpecialPoint_mem_specialFibre (M : Model R A) (s : 𝟙_ (Over (Sp R)) ⟶ M.Y) : sp0 s ∈ M.sp := by
  show M.Y.hom (s.left _) = _
  rw [← Scheme.Hom.comp_apply, Over.w s]
  rfl

/- English proof (translation)
Establish `hr : Set.range s.left ⊆ Set.range U.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Use `range_subset_opens_of_isLocalRing (B := CommRingCat.of R) s.left ?_` and prove the remaining obligations. Use `show sp0 s ∈ U`. Rewrite using `[← hy]`.

Conclude with `y.2`. Set `s'` to `IsOpenImmersion.lift U.ι s.left hr`. Establish `e : s' ≫ U.ι = s.left` using `IsOpenImmersion.lift_fac _ _ _`. Use `⟨Over.homMk (s' ≫ g) (by rw [Category.assoc, h.1, reassoc_of% e, Over.w s]), ?_, ?_⟩` and prove the remaining obligations. Use `ext_test h p.left (spMap (algebraMap R K) ≫ s') (by rw [Category.assoc, e]; exact hs.symm) show (p ≫ f).left ≫ N.j = spMap (algebraMap R K) ≫ s' ≫ g` as an intermediate fact.

Rewrite using `[← Category.assoc (spMap _), this, Over.comp_left, Category.assoc]`. Establish `: y = s' (IsLocalRing.closedPoint R)`. Apply `U.ι.isOpenEmbedding.injective` to reduce the goal to its premises. Rewrite using `[hy, ← Scheme.Hom.comp_apply, e]`. Both sides reduce to the same expression.

Rewrite using `[this, ← Scheme.Hom.comp_apply]`. Both sides reduce to the same expression.
-/
theorem sec_exists {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {U : M.Y.left.Opens} {g : U.toScheme ⟶ N.Y.left}
    (h : Extends M N f U g) {p : 𝟙_ (Over (Sp K)) ⟶ A} {s : 𝟙_ (Over (Sp R)) ⟶ M.Y} (hs : Sec M p s)
    (y : U.toScheme) (hy : U.ι y = sp0 s) : ∃ t, Sec N (p ≫ f) t ∧ g y = sp0 t := by
  have hr : Set.range s.left ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    refine range_subset_opens_of_isLocalRing (B := CommRingCat.of R) s.left ?_
    show sp0 s ∈ U
    rw [← hy]; exact y.2
  let s' := IsOpenImmersion.lift U.ι s.left hr
  have e : s' ≫ U.ι = s.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.homMk (s' ≫ g) (by rw [Category.assoc, h.1, reassoc_of% e, Over.w s]), ?_, ?_⟩
  · have := ext_test h p.left (spMap (algebraMap R K) ≫ s') (by rw [Category.assoc, e]; exact hs.symm)
    show (p ≫ f).left ≫ N.j = spMap (algebraMap R K) ≫ s' ≫ g
    rw [← Category.assoc (spMap _), this, Over.comp_left, Category.assoc]
  · have : y = s' (IsLocalRing.closedPoint R) := by
      apply U.ι.isOpenEmbedding.injective
      rw [hy, ← Scheme.Hom.comp_apply, e]; rfl
    rw [this, ← Scheme.Hom.comp_apply]; rfl

/- English proof (translation)
Take `⟨U, g, hy, h⟩` from `h`. Take `⟨t', ht', e⟩` from `sec_exists h hs ⟨_, hy⟩ rfl`. Rewrite `h'` using `[sec_unique ht ht', ← e]`. Conclude with `defAt_comp h _ h'`.
-/
theorem defAt_comp_sec [IsDomain R] [IsFractionRing R K] {M : Model R A} {N : Model R A'} {P : Model R A''}
    {f : A ⟶ A'} {f' : A' ⟶ A''} {p : 𝟙_ (Over (Sp K)) ⟶ A} {s : 𝟙_ (Over (Sp R)) ⟶ M.Y}
    {t : 𝟙_ (Over (Sp R)) ⟶ N.Y} (hs : Sec M p s) (ht : Sec N (p ≫ f) t) (h : DefAt M N f (sp0 s))
    (h' : DefAt N P f' (sp0 t)) : DefAt M P (f ≫ f') (sp0 s) := by
  obtain ⟨U, g, hy, h⟩ := h
  obtain ⟨t', ht', e⟩ := sec_exists h hs ⟨_, hy⟩ rfl
  rw [sec_unique ht ht', ← e] at h'
  exact defAt_comp h _ h'

/- English proof (translation)
Take `⟨-, hH, hk, -⟩` from `hR`. Use `M.smooth` as an intermediate fact. Set `r` to `Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))`. Set `i` to `pullback.fst M.Y.hom r`. Set `q` to `pullback.snd M.Y.hom r`.

Use `LocallyOfFiniteType.jacobsonSpace q` as an intermediate fact. Take `⟨y, hy, hy'⟩` from `hne`. Choose the witnesses or unpack the hypotheses as in `⟨w, rfl⟩ : y ∈ Set.range i := by`. Rewrite using `[range_fst_residue]`. Conclude with `hy'`.

Take `⟨c, hc, hc'⟩` from `nonempty_inter_closedPoints (Z := i ⁻¹' C) ⟨w, hy⟩ (hC.preimage i.continuous)`. Take `⟨⟨x, hx⟩, hx'⟩` from `reducePoint_residue_surjective M.Y.hom R (𝟙 _) ⟨pointOfClosedPoint q c hc' ≫ i, by`. Rewrite using `[Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc, Category.comp_id]⟩`. Establish `e : r ≫ x = pointOfClosedPoint q c hc' ≫ i` using `congrArg Subtype.val hx'`. Use `⟨Over.homMk x hx, ?_⟩` and prove the remaining obligations.

Establish `e'` using `congrArg (fun m => m (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) e`. Simplify using `only [Scheme.Hom.comp_apply, pointOfClosedPoint_apply] at e'`. Establish `e2 : r (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) = IsLocalRing.closedPoint R` using `IsLocalRing.comap_closedPoint (IsLocalRing.residue R)`. Rewrite `e'` using `[e2]`. Use `show x _ ∈ C`.

Conclude with `e' ▸ hc`.
-/
theorem exists_section [IsDomain R] (hR : SH R K) (M : Model R A) {C : Set M.Y.left} (hC : IsLocallyClosed C)
    (hne : (C ∩ M.sp).Nonempty) : ∃ s : 𝟙_ (Over (Sp R)) ⟶ M.Y, sp0 s ∈ C := by
  obtain ⟨-, hH, hk, -⟩ := hR
  have := M.smooth
  let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let i := pullback.fst M.Y.hom r
  let q := pullback.snd M.Y.hom r
  have := LocallyOfFiniteType.jacobsonSpace q
  obtain ⟨y, hy, hy'⟩ := hne
  obtain ⟨w, rfl⟩ : y ∈ Set.range i := by
    rw [range_fst_residue]; exact hy'
  obtain ⟨c, hc, hc'⟩ := nonempty_inter_closedPoints (Z := i ⁻¹' C) ⟨w, hy⟩ (hC.preimage i.continuous)
  obtain ⟨⟨x, hx⟩, hx'⟩ := reducePoint_residue_surjective M.Y.hom R (𝟙 _)
    ⟨pointOfClosedPoint q c hc' ≫ i, by
      rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc, Category.comp_id]⟩
  have e : r ≫ x = pointOfClosedPoint q c hc' ≫ i := congrArg Subtype.val hx'
  refine ⟨Over.homMk x hx, ?_⟩
  have e' := congrArg (fun m => m (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) e
  simp only [Scheme.Hom.comp_apply, pointOfClosedPoint_apply] at e'
  have e2 : r (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) = IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
  rw [e2] at e'
  show x _ ∈ C
  exact e' ▸ hc

omit [IsLocalRing R] in
/- English proof (translation)
Use `⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => c.fst ≫ snd Y Z) ?_ ?_ ?_⟩⟩` and prove the remaining obligations. Introduce `c ext1`. Use `c.condition` as an intermediate fact. Simplify using `[this, ← Category.assoc, toUnit_unique (_ ≫ toUnit Z) c.snd]`. Simplify using the standard rewrite rules.

Introduce `c`. Conclude with `toUnit_unique _ _`. Introduce `c m h _`. Simplify using `[← h]`.
-/
theorem isPullback_fibre_fst {Y Z : Over (Sp R)} (s : 𝟙_ (Over (Sp R)) ⟶ Y) :
    IsPullback (lift (toUnit Z ≫ s) (𝟙 Z)) (toUnit Z) (fst Y Z) s := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => c.fst ≫ snd Y Z) ?_ ?_ ?_⟩⟩
  · intro c
    ext1
    · have := c.condition
      simp [this, ← Category.assoc, toUnit_unique (_ ≫ toUnit Z) c.snd]
    · simp
  · intro c; exact toUnit_unique _ _
  · intro c m h _
    simp [← h]

omit [IsLocalRing R] in
/- English proof (translation)
Use `⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => c.fst ≫ fst Z Y) ?_ ?_ ?_⟩⟩` and prove the remaining obligations. Introduce `c ext1`. Simplify using the standard rewrite rules. Use `c.condition` as an intermediate fact. Simplify using `[this, ← Category.assoc, toUnit_unique (_ ≫ toUnit Z) c.snd]`.

Introduce `c`. Conclude with `toUnit_unique _ _`. Introduce `c m h _`. Simplify using `[← h]`.
-/
theorem isPullback_fibre_snd {Y Z : Over (Sp R)} (s : 𝟙_ (Over (Sp R)) ⟶ Y) :
    IsPullback (lift (𝟙 Z) (toUnit Z ≫ s)) (toUnit Z) (snd Z Y) s := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => c.fst ≫ fst Z Y) ?_ ?_ ?_⟩⟩
  · intro c
    ext1
    · simp
    · have := c.condition
      simp [this, ← Category.assoc, toUnit_unique (_ ≫ toUnit Z) c.snd]
  · intro c; exact toUnit_unique _ _
  · intro c m h _
    simp [← h]

/- English proof (translation)
Take `⟨u, h1, h2⟩` from `Scheme.exists_preimage_of_isPullback (h.map (Over.forget _)) z (IsLocalRing.closedPoint R) hz`. Use `⟨u, ?_, h1⟩` and prove the remaining obligations. Establish `e` using `Over.w (toUnit M.Y)`. Use `show M.Y.hom u = _`. Rewrite using `[← e, Scheme.Hom.comp_apply]`.

Conclude with `h2`.
-/
theorem exists_fibre {M : Model R A} {W Y : Over (Sp R)} {l : M.Y ⟶ W} {p : W ⟶ Y} {s : 𝟙_ (Over (Sp R)) ⟶ Y}
    (h : IsPullback l (toUnit _) p s) (z : W.left) (hz : p.left z = sp0 s) : ∃ u ∈ M.sp, l.left u = z := by
  obtain ⟨u, h1, h2⟩ := Scheme.exists_preimage_of_isPullback (h.map (Over.forget _)) z (IsLocalRing.closedPoint R) hz
  refine ⟨u, ?_, h1⟩
  have e := Over.w (toUnit M.Y)
  show M.Y.hom u = _
  rw [← e, Scheme.Hom.comp_apply]
  exact h2

/- English proof (translation)
Take `⟨w, hw, U, g, hwU, hg, ho⟩` from `hf`. Establish `key : ∀ u : U.toScheme, g u ∈ M.sp ↔ U.ι u ∈ M.sp`. Introduce `u`. Use `show M.Y.hom (g u) = _ ↔ M.Y.hom (U.ι u) = _`. Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hg.1]`.

Take `⟨_, h1, ⟨u, rfl⟩, h2⟩` from `hi.2 (Set.range g) V₂ g.isOpenEmbedding.isOpen_range o₂ ⟨g ⟨w, hwU⟩, (key _).2 hw, _, rfl⟩ n₂`. Establish `o₃ : IsOpen (U.ι '' (g ⁻¹' V₂))` using `U.ι.isOpenEmbedding.isOpenMap _ (o₂.preimage g.continuous)`. Take `⟨v, h3, h4⟩` from `hi.2 V₁ _ o₁ o₃ n₁ ⟨U.ι u, (key _).1 h1, u, h2, rfl⟩`. Take `⟨s, hs, u', hu', e⟩` from `exists_section hR M (o₁.inter o₃).isLocallyClosed ⟨v, h4, h3⟩`. Use `⟨s, hs, fun p hp => ?_⟩` and prove the remaining obligations.

Take `⟨t, ht, e'⟩` from `sec_exists hg hp u' e`. Conclude with `⟨t, ht, e' ▸ hu'⟩`.
-/
theorem exists_section_general [IsDomain R] (hR : SH R K) {M : Model R A} (hi : M.Irr) {f : A ⟶ A}
    (hf : GenIso M M f) {V₁ V₂ : Set M.Y.left} (o₁ : IsOpen V₁) (o₂ : IsOpen V₂) (n₁ : (M.sp ∩ V₁).Nonempty)
    (n₂ : (M.sp ∩ V₂).Nonempty) :
    ∃ (s : 𝟙_ (Over (Sp R)) ⟶ M.Y), sp0 s ∈ V₁ ∧ ∀ p, Sec M p s → ∃ t, Sec M (p ≫ f) t ∧ sp0 t ∈ V₂ := by
  obtain ⟨w, hw, U, g, hwU, hg, ho⟩ := hf
  have key : ∀ u : U.toScheme, g u ∈ M.sp ↔ U.ι u ∈ M.sp := by
    intro u
    show M.Y.hom (g u) = _ ↔ M.Y.hom (U.ι u) = _
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hg.1]
  obtain ⟨_, h1, ⟨u, rfl⟩, h2⟩ := hi.2 (Set.range g) V₂ g.isOpenEmbedding.isOpen_range o₂
    ⟨g ⟨w, hwU⟩, (key _).2 hw, _, rfl⟩ n₂
  have o₃ : IsOpen (U.ι '' (g ⁻¹' V₂)) := U.ι.isOpenEmbedding.isOpenMap _ (o₂.preimage g.continuous)
  obtain ⟨v, h3, h4⟩ := hi.2 V₁ _ o₁ o₃ n₁ ⟨U.ι u, (key _).1 h1, u, h2, rfl⟩
  obtain ⟨s, hs, u', hu', e⟩ := exists_section hR M (o₁.inter o₃).isLocallyClosed ⟨v, h4, h3⟩
  refine ⟨s, hs, fun p hp => ?_⟩
  obtain ⟨t, ht, e'⟩ := sec_exists hg hp u' e
  exact ⟨t, ht, e' ▸ hu'⟩

/- English proof (translation)
Use `hR.2.2.2` as an intermediate fact. Take `⟨x, hx, -, -⟩` from `GlobalTheory.SS.SectionTranslation.translation_by_section R K hR A hA M hM X`. Take `⟨y, hy, gy, -⟩` from `GlobalTheory.SS.SectionTranslation.translation_by_section R K hR A hA M hM Y`. Establish `gφ` using `(GlobalTheory.T.modelMapGenericallyOpenImmersion_calculus R K hR).2.1 A A A M M M _ _ hM.1.1 hM.1.2.2 gy`. Take `⟨z₁, hz₁, i₁⟩` from `(hM.2 false _ (modelSectionSpecialPoint_mem_specialFibre M Y)).2`.

Take `⟨z₂, hz₂, i₂⟩` from `(hM.2 true _ (modelSectionSpecialPoint_mem_specialFibre M X)).1`. Take `⟨u₁, m₁, rfl⟩` from `exists_fibre (isPullback_fibre_snd (Z := M.Y) Y) z₁ hz₁`. Take `⟨u₂, m₂, rfl⟩` from `exists_fibre (isPullback_fibre_fst (Z := M.Y) X) z₂ hz₂`. Take `⟨s, hs, hs'⟩` from `exists_section_general hR hM.1.1 gφ ((isOpen_isoAt (M.prod M) (M.prod M) (shear A false)).preimage (lift (𝟙 M.Y) (toUnit M.Y ≫ Y)).left.continuous) ((isOpen_isoAt (M.prod M) (M.prod M) (shear A true)).preimage (lift (toUnit M.Y ≫ X) (𝟙 M.Y)).left.continuous) ⟨u₁, m₁, i₁⟩ ⟨u₂, m₂, …`. Take `⟨a, ha, ga, ha'⟩` from `GlobalTheory.SS.SectionTranslation.translation_by_section R K hR A hA M hM s`.

Take `⟨t, ht, ht'⟩` from `hs' a ha`. Establish `u1 : ∀ (w : 𝟙_ (Over (Sp R)) ⟶ M.Y), w ≫ toUnit M.Y = 𝟙 _` using `fun w => toUnit_unique _ _`. Establish `u2 : ∀ (w : 𝟙_ (Over (Sp K)) ⟶ A), w ≫ toUnit A = 𝟙 _` using `fun w => toUnit_unique _ _`. Establish `d1 : DefAt M M (transl a).inv (sp0 Y)`. Use `(ha' (sp0 Y) false ?_).defAt` and prove the remaining obligations.

Apply the tactic sequence `have e : s ≫ lift (𝟙 M.Y) (toUnit M.Y ≫ Y) = Y ≫ lift (toUnit M.Y ≫ s) (𝟙 M.Y) := by ext1 <;> simp [reassoc_of% u1]`. Rewrite using `[map_modelSectionSpecialPoint_comp, ← e, ← map_modelSectionSpecialPoint_comp]`. Conclude with `hs`. Establish `d2 : DefAt (M.prod M) (M.prod M) (shear A true) (sp0 (lift X t))`. Apply the tactic sequence `have e : t ≫ lift (toUnit M.Y ≫ X) (𝟙 M.Y) = lift X t := by ext1 <;> simp [reassoc_of% u1]`.

Rewrite using `[← e, ← map_modelSectionSpecialPoint_comp]`. Conclude with `IsoAt.defAt ht'`. Establish `ef` using `defAt_global (M.prod M) M _ _ (prod_j_fst M M)`. Establish `es` using `defAt_global (M.prod M) M _ _ (prod_j_snd M M)`. Establish `d3 : DefAt (M.prod M) M (snd A A ≫ (transl a).inv) (sp0 (lift X Y))`.

Use `defAt_comp es ⟨sp0 (lift X Y), trivial⟩ ?_` and prove the remaining obligations. Establish `: ((⊤ : (M.prod M).Y.left.Opens).ι ≫ (snd M.Y M.Y).left) ⟨sp0 (lift X Y), trivial⟩ = sp0 Y`. Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `(map_modelSectionSpecialPoint_comp (lift X Y) (snd M.Y M.Y)).trans (by rw [lift_snd])`. Rewrite using `[this]`.

Conclude with `d1`. Establish `d4` using `defAt_lift (⟨⊤, _, trivial, ef⟩ : DefAt (M.prod M) M (fst A A) (sp0 (lift X Y))) d3`. Establish `e5 : lift x y ≫ lift (fst A A) (snd A A ≫ (transl a).inv) = lift x (a ≫ ι[A] ≫ (transl y).hom)` using `by ext1`. Simplify using the standard rewrite rules. Establish `: a ≫ ι[A] = a⁻¹` using `rfl`.

Simplify using `only [Category.assoc, lift_snd, lift_snd_assoc, ← Category.assoc a, this]`. Simplify using `only [transl, MonObj.comp_mul, GrpObj.comp_inv, reassoc_of% u2, Category.comp_id]`. Conclude with `_root_.mul_comm _ _`. Establish `d5` using `defAt_comp_sec (sec_lift hx hy) (by rw [e5]; exact sec_lift hx ht) d4 d2`. Establish `d6` using `defAt_comp_all d5 (fun w => (⟨⊤, _, trivial, es⟩ : DefAt (M.prod M) M (snd A A) w))`.

Use `⟨a, ga, defAt_twist _ ?_⟩` and prove the remaining obligations. Use `d6 using 1` and compare the differences between its conclusion and the goal. Establish `hμ : μ[A] = fst A A * snd A A`. Rewrite using `[Hom.mul_def]`. Simplify using the standard rewrite rules.

Establish `u3 : ∀ (w : A ⊗ A ⟶ A), w ≫ toUnit A = toUnit _` using `fun w => toUnit_unique _ _`. Simplify using `only [shear, transl, Category.assoc, lift_snd, MonObj.comp_mul, GrpObj.comp_inv, lift_fst, reassoc_of% u3, Category.comp_id]`. Rewrite using `[hμ, _root_.mul_left_comm]`.
-/
theorem lawdef_section [IsDomain R] (hR : SH R K) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) (M : Model R A) (hM : Strict M) (X Y : 𝟙_ (Over (Sp R)) ⟶ M.Y) :
    ∃ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso M M (transl a).hom ∧
      DefAt (M.prod M) (M.twist (transl a)) (μ[A]) (sp0 (lift X Y)) := by
  have := hR.2.2.2
  obtain ⟨x, hx, -, -⟩ := GlobalTheory.SS.SectionTranslation.translation_by_section R K hR A hA M hM X
  obtain ⟨y, hy, gy, -⟩ := GlobalTheory.SS.SectionTranslation.translation_by_section R K hR A hA M hM Y
  have gφ := (GlobalTheory.T.modelMapGenericallyOpenImmersion_calculus R K hR).2.1 A A A M M M _ _ hM.1.1 hM.1.2.2 gy
  obtain ⟨z₁, hz₁, i₁⟩ := (hM.2 false _ (modelSectionSpecialPoint_mem_specialFibre M Y)).2
  obtain ⟨z₂, hz₂, i₂⟩ := (hM.2 true _ (modelSectionSpecialPoint_mem_specialFibre M X)).1
  obtain ⟨u₁, m₁, rfl⟩ := exists_fibre (isPullback_fibre_snd (Z := M.Y) Y) z₁ hz₁
  obtain ⟨u₂, m₂, rfl⟩ := exists_fibre (isPullback_fibre_fst (Z := M.Y) X) z₂ hz₂
  obtain ⟨s, hs, hs'⟩ := exists_section_general hR hM.1.1 gφ
    ((isOpen_isoAt (M.prod M) (M.prod M) (shear A false)).preimage (lift (𝟙 M.Y) (toUnit M.Y ≫ Y)).left.continuous)
    ((isOpen_isoAt (M.prod M) (M.prod M) (shear A true)).preimage (lift (toUnit M.Y ≫ X) (𝟙 M.Y)).left.continuous)
    ⟨u₁, m₁, i₁⟩ ⟨u₂, m₂, i₂⟩
  obtain ⟨a, ha, ga, ha'⟩ := GlobalTheory.SS.SectionTranslation.translation_by_section R K hR A hA M hM s
  obtain ⟨t, ht, ht'⟩ := hs' a ha
  have u1 : ∀ (w : 𝟙_ (Over (Sp R)) ⟶ M.Y), w ≫ toUnit M.Y = 𝟙 _ := fun w => toUnit_unique _ _
  have u2 : ∀ (w : 𝟙_ (Over (Sp K)) ⟶ A), w ≫ toUnit A = 𝟙 _ := fun w => toUnit_unique _ _
  have d1 : DefAt M M (transl a).inv (sp0 Y) := by
    refine (ha' (sp0 Y) false ?_).defAt
    have e : s ≫ lift (𝟙 M.Y) (toUnit M.Y ≫ Y) = Y ≫ lift (toUnit M.Y ≫ s) (𝟙 M.Y) := by
      ext1 <;> simp [reassoc_of% u1]
    rw [map_modelSectionSpecialPoint_comp, ← e, ← map_modelSectionSpecialPoint_comp]
    exact hs
  have d2 : DefAt (M.prod M) (M.prod M) (shear A true) (sp0 (lift X t)) := by
    have e : t ≫ lift (toUnit M.Y ≫ X) (𝟙 M.Y) = lift X t := by
      ext1 <;> simp [reassoc_of% u1]
    rw [← e, ← map_modelSectionSpecialPoint_comp]
    exact IsoAt.defAt ht'
  have ef := defAt_global (M.prod M) M _ _ (prod_j_fst M M)
  have es := defAt_global (M.prod M) M _ _ (prod_j_snd M M)
  have d3 : DefAt (M.prod M) M (snd A A ≫ (transl a).inv) (sp0 (lift X Y)) := by
    refine defAt_comp es ⟨sp0 (lift X Y), trivial⟩ ?_
    have : ((⊤ : (M.prod M).Y.left.Opens).ι ≫ (snd M.Y M.Y).left) ⟨sp0 (lift X Y), trivial⟩ = sp0 Y := by
      rw [Scheme.Hom.comp_apply]
      exact (map_modelSectionSpecialPoint_comp (lift X Y) (snd M.Y M.Y)).trans (by rw [lift_snd])
    rw [this]; exact d1
  have d4 := defAt_lift (⟨⊤, _, trivial, ef⟩ : DefAt (M.prod M) M (fst A A) (sp0 (lift X Y))) d3
  have e5 : lift x y ≫ lift (fst A A) (snd A A ≫ (transl a).inv) = lift x (a ≫ ι[A] ≫ (transl y).hom) := by
    ext1
    · simp
    · have : a ≫ ι[A] = a⁻¹ := rfl
      simp only [Category.assoc, lift_snd, lift_snd_assoc, ← Category.assoc a, this]
      simp only [transl, MonObj.comp_mul, GrpObj.comp_inv, reassoc_of% u2, Category.comp_id]
      exact _root_.mul_comm _ _
  have d5 := defAt_comp_sec (sec_lift hx hy) (by rw [e5]; exact sec_lift hx ht) d4 d2
  have d6 := defAt_comp_all d5 (fun w => (⟨⊤, _, trivial, es⟩ : DefAt (M.prod M) M (snd A A) w))
  refine ⟨a, ga, defAt_twist _ ?_⟩
  convert d6 using 1
  have hμ : μ[A] = fst A A * snd A A := by
    rw [Hom.mul_def]; simp
  have u3 : ∀ (w : A ⊗ A ⟶ A), w ≫ toUnit A = toUnit _ := fun w => toUnit_unique _ _
  simp only [shear, transl, Category.assoc, lift_snd, MonObj.comp_mul, GrpObj.comp_inv, lift_fst, reassoc_of% u3,
    Category.comp_id]
  rw [hμ, _root_.mul_left_comm]

end GlobalTheory.SS.LawDef

open GlobalTheory.SS.LawDef in

/- English proof (translation)
Introduce `R K _ _ _ _ _ hR A _ _ hA M hM z`. Distinguish the cases in `hz : z ∈ (M.prod M).sp`. Take `⟨Z, hZ⟩` from `exists_section hR (M.prod M) (C := closure {z}) isClosed_closure.isLocallyClosed ⟨z, subset_closure rfl, hz⟩`. Take `⟨a, ga, U, g, hU, h⟩` from `lawdef_section hR A hA M hM (Z ≫ fst M.Y M.Y) (Z ≫ snd M.Y M.Y)`. Establish `e : lift (Z ≫ fst M.Y M.Y) (Z ≫ snd M.Y M.Y) = Z`.

Rewrite using `[← comp_lift, lift_fst_snd]`. Conclude with `Category.comp_id _`. Rewrite `hU` using `[e]`. Conclude with `⟨a, ga, U, g, (specializes_iff_mem_closure.2 hZ).mem_open U.isOpen hU, h⟩`. Use `hR.1` as an intermediate fact.

Use `hR.2.2.2` as an intermediate fact. Take `⟨y, hy⟩` from `hM.1.1.nonempty`. Establish `e : (transl (1 : 𝟙_ (Over (Sp K)) ⟶ A)).hom = 𝟙 A` using `by simp [transl]`. Conclude with `⟨1, ⟨y, hy, e ▸ isoAt_id M y⟩, defAt_generic _ _ _ z hz⟩`.
-/
theorem GlobalTheory.SS.defAt_mul_twist : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, Strict M → ∀ z : (M.prod M).Y.left, ∃ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso M M (transl a).hom ∧ DefAt (M.prod M) (M.twist (transl a)) (μ[A]) z := by
  intro R K _ _ _ _ _ hR A _ _ hA M hM z
  by_cases hz : z ∈ (M.prod M).sp
  · obtain ⟨Z, hZ⟩ := exists_section hR (M.prod M) (C := closure {z}) isClosed_closure.isLocallyClosed
      ⟨z, subset_closure rfl, hz⟩
    obtain ⟨a, ga, U, g, hU, h⟩ := lawdef_section hR A hA M hM (Z ≫ fst M.Y M.Y) (Z ≫ snd M.Y M.Y)
    have e : lift (Z ≫ fst M.Y M.Y) (Z ≫ snd M.Y M.Y) = Z := by
      rw [← comp_lift, lift_fst_snd]; exact Category.comp_id _
    rw [e] at hU
    exact ⟨a, ga, U, g, (specializes_iff_mem_closure.2 hZ).mem_open U.isOpen hU, h⟩
  · have := hR.1
    have := hR.2.2.2
    obtain ⟨y, hy⟩ := hM.1.1.nonempty
    have e : (transl (1 : 𝟙_ (Over (Sp K)) ⟶ A)).hom = 𝟙 A := by simp [transl]
    exact ⟨1, ⟨y, hy, e ▸ isoAt_id M y⟩, defAt_generic _ _ _ z hz⟩
end
