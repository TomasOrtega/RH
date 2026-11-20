import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFullLevelAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsClopenSpecializationsGenPt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermGenPtInjectiveRangeRegAt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EssFiniteTypeOfFiniteDimensional
import Development.WeilBound.CoreStatements.HodgeTatePoints.MfBase

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint

noncomputable section

namespace PositivityTheory.HtPt.Mf

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

/- English proof (translation)
Rewrite using `[Scheme.preimage_eq_top_of_closedPoint_mem ξ (q.2.mem_open U.isOpen hq)]`.
-/
theorem le_preimage_of_cpt (ξ : Sp Ω ⟶ X) (q : Cpt ξ) {U : X.Opens} (hq : q.1 ∈ U) : ⊤ ≤ ξ ⁻¹ᵁ U := by
  rw [Scheme.preimage_eq_top_of_closedPoint_mem ξ (q.2.mem_open U.isOpen hq)]

/- English proof (translation)
Establish `hU : ξ (IsLocalRing.closedPoint Ω) ∈ U` using `q.2.mem_open U.isOpen hq`. Establish `hle` using `le_preimage_of_cpt ξ q hq`. Establish `e1 : X.presheaf.germ U q.1 hq ≫ X.presheaf.stalkSpecializes q.2 = X.presheaf.germ U _ hU` using `TopCat.Presheaf.germ_stalkSpecializes _ _ _`. Establish `e5 : (X.presheaf.germ U q.1 hq ≫ X.presheaf.stalkSpecializes q.2) ≫ Scheme.stalkClosedPointTo ξ = X.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo ξ` using `congrArg (· ≫ Scheme.stalkClosedPointTo ξ) e1`. Establish `e6 : X.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo ξ = Scheme.Hom.appLE ξ U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom`.

Rewrite using `[Scheme.germ_stalkClosedPointTo, Iso.trans_hom, ← Category.assoc]`. Use `congr 1`. Establish `e4` using `congrArg (fun φ => φ.hom s) (e5.trans e6)`. Simplify using `only [valR, dif_pos hle]`. Conclude with `e4`.
-/
theorem genMap_germ_eq (ξ : Sp Ω ⟶ X) (q : Cpt ξ) {U : X.Opens} (hq : q.1 ∈ U) (s : Γ(X, U)) :
    genMap ξ q ((X.presheaf.germ U q.1 hq).hom s) = valR ξ U s := by
  have hU : ξ (IsLocalRing.closedPoint Ω) ∈ U := q.2.mem_open U.isOpen hq
  have hle := le_preimage_of_cpt ξ q hq
  have e1 : X.presheaf.germ U q.1 hq ≫ X.presheaf.stalkSpecializes q.2 = X.presheaf.germ U _ hU :=
    TopCat.Presheaf.germ_stalkSpecializes _ _ _
  have e5 : (X.presheaf.germ U q.1 hq ≫ X.presheaf.stalkSpecializes q.2) ≫ Scheme.stalkClosedPointTo ξ =
      X.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo ξ :=
    congrArg (· ≫ Scheme.stalkClosedPointTo ξ) e1
  have e6 : X.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo ξ =
      Scheme.Hom.appLE ξ U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom := by
    rw [Scheme.germ_stalkClosedPointTo, Iso.trans_hom, ← Category.assoc]
    congr 1
  have e4 := congrArg (fun φ => φ.hom s) (e5.trans e6)
  simp only [valR, dif_pos hle]
  exact e4

/- English proof (translation)
Take `⟨i, hi⟩` from `GlobalTheory.ProjSpace.exists_mem_chart o n (y (IsLocalRing.closedPoint Ω))`. Establish `hle : ⊤ ≤ y ⁻¹ᵁ chart o n i` using `(Scheme.preimage_eq_top_of_closedPoint_mem y hi).ge`. Set `t : Fin (n + 1) → Ω` to `fun j => valR y (chart o n i) (ratio o n i j)`. Establish `hti : t i = 1`. Simplify using `only [t, ratio, GlobalTheory.ProjSpace.ratioOn_self, valR, dif_pos hle, map_one]`.

Establish `ht : t ≠ 0` using `fun h0 => one_ne_zero (hti.symm.trans (congrFun h0 i))`. Use `⟨t, ht, GlobalTheory.TuplePoint.eq_point hy (i := i) (by rw [hti]; exact one_ne_zero) hle (fun j => ?_)⟩` and prove the remaining obligations. Rewrite using `[hti, div_one]`.
-/
theorem exists_point {o : Type} [CommRing o] [Algebra o Ω] {n : ℕ} (y : Sp Ω ⟶ PSpace o n)
    (hy : y ≫ PSpace.str o n = spMap (algebraMap o Ω)) :
    ∃ (t : Fin (n + 1) → Ω) (ht : t ≠ 0), y = point o t ht := by
  obtain ⟨i, hi⟩ := GlobalTheory.ProjSpace.exists_mem_chart o n (y (IsLocalRing.closedPoint Ω))
  have hle : ⊤ ≤ y ⁻¹ᵁ chart o n i := (Scheme.preimage_eq_top_of_closedPoint_mem y hi).ge
  let t : Fin (n + 1) → Ω := fun j => valR y (chart o n i) (ratio o n i j)
  have hti : t i = 1 := by
    simp only [t, ratio, GlobalTheory.ProjSpace.ratioOn_self, valR, dif_pos hle, map_one]
  have ht : t ≠ 0 := fun h0 => one_ne_zero (hti.symm.trans (congrFun h0 i))
  refine ⟨t, ht, GlobalTheory.TuplePoint.eq_point hy (i := i) (by rw [hti]; exact one_ne_zero) hle (fun j => ?_)⟩
  rw [hti, div_one]

section

variable {o : Type} [CommRing o] [Algebra o Ω] {n : ℕ} {t : Fin (n + 1) → Ω} {ht : t ≠ 0}
  {ξ : Sp Ω ⟶ X} {i : X ⟶ PSpace o n}

/- English proof (translation)
Establish `key : ∀ (d : Fin (n + 1)) (hd : q.1 ∈ i ⁻¹ᵁ chart o n d) (c' : Fin (n + 1)), genMap ξ q ((X.presheaf.germ _ q.1 hd).hom (pullRatio i (i ⁻¹ᵁ chart o n d) d le_rfl c')) = t c' / t d`. Introduce `d hd c'`. Rewrite using `[genMap_germ_eq ξ q hd]`. Conclude with `valR_pullRatio hi (le_preimage_of_cpt ξ q hd) le_rfl c'`. Establish `hne : ∀ d : Fin (n + 1), q.1 ∈ i ⁻¹ᵁ chart o n d → t d ≠ 0`.

Introduce `d hd h0`. Establish `h1` using `key d hd d`. Rewrite `h1` using `[pullRatio_self, map_one, map_one, h0, div_zero]`. Conclude with `one_ne_zero h1`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hc, hreg⟩`. Choose the witnesses or unpack the hypotheses as in `⟨d, hd⟩ : ∃ d, q.1 ∈ i ⁻¹ᵁ chart o n d := by`. Establish `hmem : i q.1 ∈ (⨆ d, chart o n d)`. Rewrite using `[iSup_chart]`. Discharge the goal by the elementary cases of `trivial`.

Take `⟨d, hd⟩` from `TopologicalSpace.Opens.mem_iSup.mp hmem`. Conclude with `⟨d, hd⟩`. Establish `htd` using `hne d hd`. Establish `hunit : IsUnit ((X.presheaf.germ _ q.1 hd).hom (pullRatio i (i ⁻¹ᵁ chart o n d) d le_rfl c))`. Take `⟨y, hy⟩` from `RingHom.mem_range.mp (hreg d)`.

Use `IsUnit.of_mul_eq_one y (hξ.inj q ?_)` and prove the remaining obligations. Rewrite using `[map_mul, map_one, key d hd c, hy]`. Clear the denominators using the available nonvanishing facts. Establish `hmem` using `(X.mem_basicOpen _ q.1 hd).mpr hunit`. Rewrite `hmem` using `[basicOpen_pullRatio]`.

Conclude with `(TopologicalSpace.Opens.mem_inf.mp hmem).2`. Introduce `hq`. Conclude with `⟨hne c hq, fun c' => ⟨_, key c hq c'⟩⟩`.
-/
theorem inChart_iff (hξ : IsCptGen ξ) (hi : ξ ≫ i = point o t ht) (c : Fin (n + 1)) (q : Cpt ξ) :
    InChart ξ t c q ↔ q.1 ∈ i ⁻¹ᵁ chart o n c := by
  have key : ∀ (d : Fin (n + 1)) (hd : q.1 ∈ i ⁻¹ᵁ chart o n d) (c' : Fin (n + 1)),
      genMap ξ q ((X.presheaf.germ _ q.1 hd).hom (pullRatio i (i ⁻¹ᵁ chart o n d) d le_rfl c')) = t c' / t d := by
    intro d hd c'
    rw [genMap_germ_eq ξ q hd]
    exact valR_pullRatio hi (le_preimage_of_cpt ξ q hd) le_rfl c'
  have hne : ∀ d : Fin (n + 1), q.1 ∈ i ⁻¹ᵁ chart o n d → t d ≠ 0 := by
    intro d hd h0
    have h1 := key d hd d
    rw [pullRatio_self, map_one, map_one, h0, div_zero] at h1
    exact one_ne_zero h1
  constructor
  · rintro ⟨hc, hreg⟩
    obtain ⟨d, hd⟩ : ∃ d, q.1 ∈ i ⁻¹ᵁ chart o n d := by
      have hmem : i q.1 ∈ (⨆ d, chart o n d) := by
        rw [iSup_chart]
        trivial
      obtain ⟨d, hd⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
      exact ⟨d, hd⟩
    have htd := hne d hd
    have hunit : IsUnit ((X.presheaf.germ _ q.1 hd).hom (pullRatio i (i ⁻¹ᵁ chart o n d) d le_rfl c)) := by
      obtain ⟨y, hy⟩ := RingHom.mem_range.mp (hreg d)
      refine IsUnit.of_mul_eq_one y (hξ.inj q ?_)
      rw [map_mul, map_one, key d hd c, hy]
      field_simp
    have hmem := (X.mem_basicOpen _ q.1 hd).mpr hunit
    rw [basicOpen_pullRatio] at hmem
    exact (TopologicalSpace.Opens.mem_inf.mp hmem).2
  · intro hq
    exact ⟨hne c hq, fun c' => ⟨_, key c hq c'⟩⟩

/- English proof (translation)
Establish `htop : ⊤ ≤ point o t ht ⁻¹ᵁ chart o n c`. Establish `h1` using `valR_point_ratio (L := Ω) (o := o) (t := t) (ht := ht) hc c`. Assume the negation of the conclusion as `hne`. Simplify using `only [valR, dif_neg hne] at h1`. Rewrite `h1` using `[div_self hc]`.

Conclude with `zero_ne_one h1`. Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C r`. Rewrite using `[MvPolynomial.aeval_C, MvPolynomial.aeval_C, algebraMap_sections_eq, CommRingCat.hom_comp, RingHom.comp_apply]`. Use `(valR_appLE (point o t ht) (PSpace.str o n) _ htop _).trans ?_` and prove the remaining obligations.

Rewrite using `[point_str, ← preimage_apply, Spec.preimage_map, CommRingCat.hom_ofHom]`. Consider the case `add p q hp hq`. Rewrite using `[map_add, map_add, valR_add _ _ htop, hp, hq]`. Consider the case `mul_X p j hp`. Rewrite using `[map_mul, map_mul, valR_mul _ _ htop, hp, MvPolynomial.aeval_X, MvPolynomial.aeval_X, valR_point_ratio hc j]`.
-/
private theorem valR_point_chart_aeval_ratio {o : Type} [CommRing o] [Algebra o Ω] {n : ℕ} {t : Fin (n + 1) → Ω}
    {ht : t ≠ 0} {c : Fin (n + 1)} (hc : t c ≠ 0) (P : MvPolynomial (Fin (n + 1)) o) :
    valR (point o t ht) (chart o n c) (MvPolynomial.aeval (ratio o n c) P) =
      MvPolynomial.aeval (fun j => t j / t c) P := by
  have htop : ⊤ ≤ point o t ht ⁻¹ᵁ chart o n c := by
    have h1 := valR_point_ratio (L := Ω) (o := o) (t := t) (ht := ht) hc c
    by_contra hne
    simp only [valR, dif_neg hne] at h1
    rw [div_self hc] at h1
    exact zero_ne_one h1
  induction P using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C, algebraMap_sections_eq, CommRingCat.hom_comp,
      RingHom.comp_apply]
    refine (valR_appLE (point o t ht) (PSpace.str o n) _ htop _).trans ?_
    rw [point_str, ← preimage_apply, Spec.preimage_map, CommRingCat.hom_ofHom]
  | add p q hp hq =>
    rw [map_add, map_add, valR_add _ _ htop, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, map_mul, valR_mul _ _ htop, hp, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
      valR_point_ratio hc j]

/- English proof (translation)
Establish `key : ∀ g : Γ(PSpace o n, chart o n c), valR ξ (i ⁻¹ᵁ chart o n c) ((i.app (chart o n c)).hom g) = valR (point o t ht) (chart o n c) g`. Introduce `g`. Rewrite using `[← valR_comp, hi]`. Rewrite using `[Algebra.adjoin_range_eq_range_aeval, AlgHom.mem_range]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨f, rfl⟩`. Take `⟨g, rfl⟩` from `i.app_surjective (chart o n c) (isAffineOpen_chart o n c) f`. Take `⟨P, rfl⟩` from `aeval_ratio_surjective o n c g`. Conclude with `⟨P, by rw [key, valR_point_chart_aeval_ratio hc]⟩`. Introduce and unpack `⟨P, rfl⟩`.

Conclude with `⟨(i.app _).hom (MvPolynomial.aeval (ratio o n c) P), by rw [key, valR_point_chart_aeval_ratio hc]⟩`.
-/
private theorem exists_valR_eq_iff_mem_adjoin_ratio [IsClosedImmersion i] (hi : ξ ≫ i = point o t ht) {c : Fin (n + 1)}
    (hc : t c ≠ 0) (a : Ω) :
    (∃ f : Γ(X, i ⁻¹ᵁ chart o n c), valR ξ (i ⁻¹ᵁ chart o n c) f = a) ↔
      a ∈ Algebra.adjoin o (Set.range fun j => t j / t c) := by
  have key : ∀ g : Γ(PSpace o n, chart o n c),
      valR ξ (i ⁻¹ᵁ chart o n c) ((i.app (chart o n c)).hom g) = valR (point o t ht) (chart o n c) g := by
    intro g
    rw [← valR_comp, hi]
  rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.mem_range]
  constructor
  · rintro ⟨f, rfl⟩
    obtain ⟨g, rfl⟩ := i.app_surjective (chart o n c) (isAffineOpen_chart o n c) f
    obtain ⟨P, rfl⟩ := aeval_ratio_surjective o n c g
    exact ⟨P, by rw [key, valR_point_chart_aeval_ratio hc]⟩
  · rintro ⟨P, rfl⟩
    exact ⟨(i.app _).hom (MvPolynomial.aeval (ratio o n c) P), by rw [key, valR_point_chart_aeval_ratio hc]⟩

/- English proof (translation)
Establish `hinU : ∀ p : Cpt ξ, InChart ξ t c p ↔ p.1 ∈ i ⁻¹ᵁ chart o n c` using `fun p => inChart_iff hξ hi c p`. Establish `hgU : GlobalTheory.CompanionTheory.Ar.genPt ξ ∈ i ⁻¹ᵁ chart o n c`. Establish `h0 : ∀ b : Ω, b ∈ regAt ξ ⟨GlobalTheory.CompanionTheory.Ar.genPt ξ, specializes_refl _⟩`. Introduce `b`. Take `⟨g, hg⟩` from `hξ.bij.2 b`.

Use `⟨g, ?_⟩` and prove the remaining obligations. Establish `e : X.presheaf.stalkSpecializes (specializes_refl (GlobalTheory.CompanionTheory.Ar.genPt ξ)) = 𝟙 _` using `TopCat.Presheaf.stalkSpecializes_refl _ _`. Establish `h3` using `congrArg (fun φ => (φ ≫ Scheme.stalkClosedPointTo ξ).hom g) e`. Simplify using `only [Category.id_comp] at h3`. Conclude with `h3.trans hg`.

Conclude with `(hinU ⟨_, specializes_refl _⟩).mp ⟨hc, fun j => h0 _⟩`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f, rfl⟩ p hp`. Conclude with `⟨_, genMap_germ_eq ξ p ((hinU p).mp hp) f⟩`. Introduce `hreg haveI hint : AlgebraicGeometry.IsIntegral X := (PositivityTheory.HtPt.Mf.xr_normal X Ω ξ hξ hall).1`.

Establish `hU : IsAffineOpen (i ⁻¹ᵁ chart o n c)` using `(isAffineOpen_chart o n c).preimage i`. Use `haveI : Nonempty (i ⁻¹ᵁ chart o n c) := ⟨⟨_, hgU⟩⟩`. Use `haveI := functionField_isFractionRing_of_isAffineOpen X _ hU`. Set `ψ : X.functionField →+* Ω` to `(X.presheaf.stalkSpecializes (hall (genericPoint X)) ≫ Scheme.stalkClosedPointTo ξ).hom`. Establish `hgpU : genericPoint X ∈ i ⁻¹ᵁ chart o n c` using `(genericPoint_specializes (GlobalTheory.CompanionTheory.Ar.genPt ξ)).mem_open (i ⁻¹ᵁ chart o n c).isOpen hgU`.

Establish `hcompat : ∀ (x : X) (hx : x ∈ i ⁻¹ᵁ chart o n c) (f : Γ(X, i ⁻¹ᵁ chart o n c)), genMap ξ ⟨x, hall x⟩ ((X.presheaf.germ _ x hx).hom f) = ψ (algebraMap Γ(X, i ⁻¹ᵁ chart o n c) X.functionField f)`. Introduce `x hx f`. Establish `e1 : X.presheaf.germ _ x hx ≫ X.presheaf.stalkSpecializes (hall x) = X.presheaf.germ _ (GlobalTheory.CompanionTheory.Ar.genPt ξ) hgU` using `TopCat.Presheaf.germ_stalkSpecializes _ _ _`. Establish `e2 : X.presheaf.germ _ (genericPoint X) hgpU ≫ X.presheaf.stalkSpecializes (hall (genericPoint X)) = X.presheaf.germ _ (GlobalTheory.CompanionTheory.Ar.genPt ξ) hgU` using `TopCat.Presheaf.germ_stalkSpecializes _ _ _`. Establish `h1 : algebraMap Γ(X, i ⁻¹ᵁ chart o n c) X.functionField f = (X.presheaf.germ _ (genericPoint X) hgpU).hom f` using `rfl`.

Establish `h3` using `congrArg (fun φ => (φ ≫ Scheme.stalkClosedPointTo ξ).hom f) e1`. Establish `h4` using `congrArg (fun φ => (φ ≫ Scheme.stalkClosedPointTo ξ).hom f) e2`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at h3 h4`. Rewrite using `[h1]`. Simplify using `only [ψ, CommRingCat.hom_comp, RingHom.comp_apply]`.

Conclude with `h3.trans h4.symm`. Establish `hsurj : Function.Surjective ψ`. Introduce `a'`. Take `⟨g, rfl⟩` from `hξ.bij.2 a'`. Use `⟨(X.presheaf.stalkSpecializes (genericPoint_specializes (GlobalTheory.CompanionTheory.Ar.genPt ξ))).hom g, ?_⟩` and prove the remaining obligations.

Establish `hc2 : X.presheaf.stalkSpecializes (genericPoint_specializes (GlobalTheory.CompanionTheory.Ar.genPt ξ)) ≫ X.presheaf.stalkSpecializes (hall (genericPoint X)) = 𝟙 _` using `(TopCat.Presheaf.stalkSpecializes_comp _ _ _).trans (TopCat.Presheaf.stalkSpecializes_refl _ _)`. Establish `h3` using `congrArg (fun φ => (φ ≫ Scheme.stalkClosedPointTo ξ).hom g) hc2`. Simplify using `only [Category.id_comp, CommRingCat.hom_comp, RingHom.comp_apply] at h3`. Simplify using `only [ψ, CommRingCat.hom_comp, RingHom.comp_apply]`. Conclude with `h3`.

Take `⟨b, rfl⟩` from `hsurj a`. Establish `hb : b ∈ (⊥ : Subalgebra Γ(X, i ⁻¹ᵁ chart o n c) X.functionField)`. Rewrite using `[← PrimeSpectrum.iInf_localization_eq_bot Γ(X, i ⁻¹ᵁ chart o n c) X.functionField, Algebra.mem_iInf]`. Introduce `v`. Establish `hyU : hU.fromSpec v ∈ i ⁻¹ᵁ chart o n c`.

Establish `hr` using `hU.range_fromSpec`. Rewrite `hr` using `[Set.ext_iff]`. Conclude with `(hr _).mp ⟨v, rfl⟩`. Use `letI : Algebra Γ(X, i ⁻¹ᵁ chart o n c) (X.presheaf.stalk (hU.fromSpec v)) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec v, hyU⟩`. Use `haveI hloc : IsLocalization v.asIdeal.primeCompl (X.presheaf.stalk (hU.fromSpec v)) := hU.isLocalization_stalk' v hyU`.

Establish `hp : InChart ξ t c ⟨hU.fromSpec v, hall _⟩` using `(hinU _).mpr hyU`. Take `⟨g, hg⟩ : ∃ g : X.presheaf.stalk (hU.fromSpec v), genMap ξ ⟨hU.fromSpec v, hall _⟩ g = ψ b` from `RingHom.mem_range.mp (hreg _ hp)`. Take `⟨⟨r, s⟩, rfl⟩` from `IsLocalization.mk'_surjective v.asIdeal.primeCompl g`. Establish `hspec` using `IsLocalization.mk'_spec (X.presheaf.stalk (hU.fromSpec v)) r s`. Establish `hm` using `congrArg (genMap ξ ⟨hU.fromSpec v, hall _⟩) hspec`.

Rewrite `hm` using `[map_mul, hg]`. Establish `hr : algebraMap Γ(X, i ⁻¹ᵁ chart o n c) (X.presheaf.stalk (hU.fromSpec v)) r = (X.presheaf.germ _ _ hyU).hom r` using `rfl`. Establish `hs' : algebraMap Γ(X, i ⁻¹ᵁ chart o n c) (X.presheaf.stalk (hU.fromSpec v)) s = (X.presheaf.germ _ _ hyU).hom s` using `rfl`. Rewrite `hm` using `[hr, hs', hcompat _ hyU, hcompat _ hyU, ← map_mul]`. Establish `hb'` using `ψ.injective hm`.

Establish `hs0 : algebraMap Γ(X, i ⁻¹ᵁ chart o n c) X.functionField (s : Γ(X, i ⁻¹ᵁ chart o n c)) ≠ 0`. Rewrite using `[map_ne_zero_iff _ (IsFractionRing.injective Γ(X, i ⁻¹ᵁ chart o n c) X.functionField)]`. Introduce `h0`. Conclude with `s.2 (by rw [h0]; exact v.asIdeal.zero_mem)`. Use `⟨r, s, s.2, ?_⟩` and prove the remaining obligations.

Rewrite using `[eq_mul_inv_iff_mul_eq₀ hs0, hb']`. Take `⟨f, hf⟩` from `Algebra.mem_bot.mp hb`. Use `⟨f, ?_⟩` and prove the remaining obligations. Establish `e` using `genMap_germ_eq ξ ⟨_, hall (GlobalTheory.CompanionTheory.Ar.genPt ξ)⟩ hgU f`. Conclude with `(e.symm.trans (hcompat _ hgU f)).trans (congrArg ψ hf)`.
-/
private theorem exists_valR_eq_iff_forall_inChart_mem_regAt [IsClosedImmersion i] (hξ : IsCptGen ξ)
    (hall : ∀ q : X, GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q) (hi : ξ ≫ i = point o t ht) {c : Fin (n + 1)}
    (hc : t c ≠ 0) (a : Ω) :
    (∃ f : Γ(X, i ⁻¹ᵁ chart o n c), valR ξ (i ⁻¹ᵁ chart o n c) f = a) ↔
      ∀ p : Cpt ξ, InChart ξ t c p → a ∈ regAt ξ p := by
  have hinU : ∀ p : Cpt ξ, InChart ξ t c p ↔ p.1 ∈ i ⁻¹ᵁ chart o n c := fun p => inChart_iff hξ hi c p
  have hgU : GlobalTheory.CompanionTheory.Ar.genPt ξ ∈ i ⁻¹ᵁ chart o n c := by
    have h0 : ∀ b : Ω, b ∈ regAt ξ ⟨GlobalTheory.CompanionTheory.Ar.genPt ξ, specializes_refl _⟩ := by
      intro b
      obtain ⟨g, hg⟩ := hξ.bij.2 b
      refine ⟨g, ?_⟩
      have e : X.presheaf.stalkSpecializes (specializes_refl (GlobalTheory.CompanionTheory.Ar.genPt ξ)) = 𝟙 _ :=
        TopCat.Presheaf.stalkSpecializes_refl _ _
      have h3 := congrArg (fun φ => (φ ≫ Scheme.stalkClosedPointTo ξ).hom g) e
      simp only [Category.id_comp] at h3
      exact h3.trans hg
    exact (hinU ⟨_, specializes_refl _⟩).mp ⟨hc, fun j => h0 _⟩
  constructor
  · rintro ⟨f, rfl⟩ p hp
    exact ⟨_, genMap_germ_eq ξ p ((hinU p).mp hp) f⟩
  · intro hreg
    haveI hint : AlgebraicGeometry.IsIntegral X := (PositivityTheory.HtPt.Mf.xr_normal X Ω ξ hξ hall).1
    have hU : IsAffineOpen (i ⁻¹ᵁ chart o n c) := (isAffineOpen_chart o n c).preimage i
    haveI : Nonempty (i ⁻¹ᵁ chart o n c) := ⟨⟨_, hgU⟩⟩
    haveI := functionField_isFractionRing_of_isAffineOpen X _ hU
    let ψ : X.functionField →+* Ω :=
      (X.presheaf.stalkSpecializes (hall (genericPoint X)) ≫ Scheme.stalkClosedPointTo ξ).hom
    have hgpU : genericPoint X ∈ i ⁻¹ᵁ chart o n c :=
      (genericPoint_specializes (GlobalTheory.CompanionTheory.Ar.genPt ξ)).mem_open (i ⁻¹ᵁ chart o n c).isOpen hgU
    have hcompat : ∀ (x : X) (hx : x ∈ i ⁻¹ᵁ chart o n c) (f : Γ(X, i ⁻¹ᵁ chart o n c)),
        genMap ξ ⟨x, hall x⟩ ((X.presheaf.germ _ x hx).hom f) =
          ψ (algebraMap Γ(X, i ⁻¹ᵁ chart o n c) X.functionField f) := by
      intro x hx f
      have e1 : X.presheaf.germ _ x hx ≫ X.presheaf.stalkSpecializes (hall x) =
          X.presheaf.germ _ (GlobalTheory.CompanionTheory.Ar.genPt ξ) hgU := TopCat.Presheaf.germ_stalkSpecializes _ _ _
      have e2 : X.presheaf.germ _ (genericPoint X) hgpU ≫ X.presheaf.stalkSpecializes (hall (genericPoint X)) =
          X.presheaf.germ _ (GlobalTheory.CompanionTheory.Ar.genPt ξ) hgU := TopCat.Presheaf.germ_stalkSpecializes _ _ _
      have h1 : algebraMap Γ(X, i ⁻¹ᵁ chart o n c) X.functionField f =
          (X.presheaf.germ _ (genericPoint X) hgpU).hom f := rfl
      have h3 := congrArg (fun φ => (φ ≫ Scheme.stalkClosedPointTo ξ).hom f) e1
      have h4 := congrArg (fun φ => (φ ≫ Scheme.stalkClosedPointTo ξ).hom f) e2
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3 h4
      rw [h1]
      simp only [ψ, CommRingCat.hom_comp, RingHom.comp_apply]
      exact h3.trans h4.symm
    have hsurj : Function.Surjective ψ := by
      intro a'
      obtain ⟨g, rfl⟩ := hξ.bij.2 a'
      refine ⟨(X.presheaf.stalkSpecializes (genericPoint_specializes (GlobalTheory.CompanionTheory.Ar.genPt ξ))).hom g, ?_⟩
      have hc2 : X.presheaf.stalkSpecializes (genericPoint_specializes (GlobalTheory.CompanionTheory.Ar.genPt ξ)) ≫
          X.presheaf.stalkSpecializes (hall (genericPoint X)) = 𝟙 _ :=
        (TopCat.Presheaf.stalkSpecializes_comp _ _ _).trans (TopCat.Presheaf.stalkSpecializes_refl _ _)
      have h3 := congrArg (fun φ => (φ ≫ Scheme.stalkClosedPointTo ξ).hom g) hc2
      simp only [Category.id_comp, CommRingCat.hom_comp, RingHom.comp_apply] at h3
      simp only [ψ, CommRingCat.hom_comp, RingHom.comp_apply]
      exact h3
    obtain ⟨b, rfl⟩ := hsurj a
    have hb : b ∈ (⊥ : Subalgebra Γ(X, i ⁻¹ᵁ chart o n c) X.functionField) := by
      rw [← PrimeSpectrum.iInf_localization_eq_bot Γ(X, i ⁻¹ᵁ chart o n c) X.functionField,
        Algebra.mem_iInf]
      intro v
      have hyU : hU.fromSpec v ∈ i ⁻¹ᵁ chart o n c := by
        have hr := hU.range_fromSpec
        rw [Set.ext_iff] at hr
        exact (hr _).mp ⟨v, rfl⟩
      letI : Algebra Γ(X, i ⁻¹ᵁ chart o n c) (X.presheaf.stalk (hU.fromSpec v)) :=
        TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec v, hyU⟩
      haveI hloc : IsLocalization v.asIdeal.primeCompl (X.presheaf.stalk (hU.fromSpec v)) :=
        hU.isLocalization_stalk' v hyU
      have hp : InChart ξ t c ⟨hU.fromSpec v, hall _⟩ := (hinU _).mpr hyU
      obtain ⟨g, hg⟩ : ∃ g : X.presheaf.stalk (hU.fromSpec v),
          genMap ξ ⟨hU.fromSpec v, hall _⟩ g = ψ b := RingHom.mem_range.mp (hreg _ hp)
      obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl g
      have hspec := IsLocalization.mk'_spec (X.presheaf.stalk (hU.fromSpec v)) r s
      have hm := congrArg (genMap ξ ⟨hU.fromSpec v, hall _⟩) hspec
      rw [map_mul, hg] at hm
      have hr : algebraMap Γ(X, i ⁻¹ᵁ chart o n c) (X.presheaf.stalk (hU.fromSpec v)) r =
          (X.presheaf.germ _ _ hyU).hom r := rfl
      have hs' : algebraMap Γ(X, i ⁻¹ᵁ chart o n c) (X.presheaf.stalk (hU.fromSpec v)) s =
          (X.presheaf.germ _ _ hyU).hom s := rfl
      rw [hr, hs', hcompat _ hyU, hcompat _ hyU, ← map_mul] at hm
      have hb' := ψ.injective hm
      have hs0 : algebraMap Γ(X, i ⁻¹ᵁ chart o n c) X.functionField (s : Γ(X, i ⁻¹ᵁ chart o n c)) ≠ 0 := by
        rw [map_ne_zero_iff _ (IsFractionRing.injective Γ(X, i ⁻¹ᵁ chart o n c) X.functionField)]
        intro h0
        exact s.2 (by rw [h0]; exact v.asIdeal.zero_mem)
      refine ⟨r, s, s.2, ?_⟩
      rw [eq_mul_inv_iff_mul_eq₀ hs0, hb']
    obtain ⟨f, hf⟩ := Algebra.mem_bot.mp hb
    refine ⟨f, ?_⟩
    have e := genMap_germ_eq ξ ⟨_, hall (GlobalTheory.CompanionTheory.Ar.genPt ξ)⟩ hgU f
    exact (e.symm.trans (hcompat _ hgU f)).trans (congrArg ψ hf)

/- English proof (translation)
Use `⟨hξ, fun p => ?_, fun c hc => ?_, fun c hc a => ?_⟩` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨d, hd⟩ : ∃ d, p.1 ∈ i ⁻¹ᵁ chart o n d := by`. Establish `hmem : i p.1 ∈ (⨆ d, chart o n d)`. Rewrite using `[iSup_chart]`. Discharge the goal by the elementary cases of `trivial`.

Take `⟨d, hd⟩` from `TopologicalSpace.Opens.mem_iSup.mp hmem`. Conclude with `⟨d, hd⟩`. Conclude with `⟨d, (inChart_iff hξ hi d p).mpr hd⟩`. Use `⟨i ⁻¹ᵁ chart o n c, (isAffineOpen_chart o n c).preimage i, fun q => ⟨fun hq => ⟨hall q, (inChart_iff hξ hi c ⟨q, hall q⟩).mpr hq⟩, fun ⟨h, hin⟩ => (inChart_iff hξ hi c ⟨q, h⟩).mp hin⟩⟩` and prove the remaining obligations. Conclude with `(exists_valR_eq_iff_mem_adjoin_ratio hi hc a).symm.trans (exists_valR_eq_iff_forall_inChart_mem_regAt hξ hall hi hc a)`.
-/
theorem coordTie_of_all [IsClosedImmersion i] (hξ : IsCptGen ξ) (hall : ∀ q : X, GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q)
    (hi : ξ ≫ i = point o t ht) : CoordTie o ξ t := by
  refine ⟨hξ, fun p => ?_, fun c hc => ?_, fun c hc a => ?_⟩
  · obtain ⟨d, hd⟩ : ∃ d, p.1 ∈ i ⁻¹ᵁ chart o n d := by
      have hmem : i p.1 ∈ (⨆ d, chart o n d) := by
        rw [iSup_chart]
        trivial
      obtain ⟨d, hd⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
      exact ⟨d, hd⟩
    exact ⟨d, (inChart_iff hξ hi d p).mpr hd⟩
  · refine ⟨i ⁻¹ᵁ chart o n c, (isAffineOpen_chart o n c).preimage i, fun q => ⟨fun hq => ⟨hall q,
      (inChart_iff hξ hi c ⟨q, hall q⟩).mpr hq⟩, fun ⟨h, hin⟩ => (inChart_iff hξ hi c ⟨q, h⟩).mp hin⟩⟩
  · exact (exists_valR_eq_iff_mem_adjoin_ratio hi hc a).symm.trans (exists_valR_eq_iff_forall_inChart_mem_regAt hξ hall hi hc a)

end

/- English proof (translation)
Unfold `GlobalTheory.CompanionTheory.Ar.InChart`. Rewrite using `[regAt_push]`.
-/
private theorem inChart_push_iff {W : Scheme.{0}} (ξ : Sp Ω ⟶ W) (f : W ⟶ X) [SurjectiveOnStalks f]
    {κ : Type} (x : κ → Ω) (c : κ) (p : Cpt ξ) :
    InChart (ξ ≫ f) x c (push ξ f p) ↔ InChart ξ x c p := by
  unfold GlobalTheory.CompanionTheory.Ar.InChart
  rw [regAt_push]

/- English proof (translation)
Use `haveI : SurjectiveOnStalks f := inferInstance`. Use `⟨hξ, fun q => ?_, fun c hc => ?_, fun c hc a => ?_⟩` and prove the remaining obligations. Take `⟨p, rfl⟩` from `hr q`. Take `⟨c, hc⟩` from `h.cover p`. Conclude with `⟨c, (inChart_push_iff ξ f x c p).mpr hc⟩`.

Take `⟨V, hV, hVmem⟩` from `h.affine c hc`. Use `⟨f ''ᵁ V, hV.image_of_isOpenImmersion f, fun q => ?_⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q', hq'V, rfl⟩`. Take `⟨h', hin⟩` from `(hVmem q').mp hq'V`.

Conclude with `⟨(push ξ f ⟨q', h'⟩).2, (inChart_push_iff ξ f x c ⟨q', h'⟩).mpr hin⟩`. Introduce and unpack `⟨hq, hin⟩`. Take `⟨p, hp⟩` from `hr ⟨q, hq⟩`. Establish `hin' : InChart (ξ ≫ f) x c (push ξ f p)`. Rewrite using `[hp]`.

Conclude with `hin`. Establish `hpV : p.1 ∈ V` using `(hVmem p.1).mpr ⟨p.2, (inChart_push_iff ξ f x c p).mp hin'⟩`. Establish `hq' : f p.1 = q` using `congrArg Subtype.val hp`. Conclude with `⟨p.1, hpV, hq'⟩`. Rewrite using `[h.ring c hc a]`.

Prove the components needed by the constructor for the conclusion. Introduce `H q hq`. Take `⟨p, rfl⟩` from `hr q`. Rewrite using `[regAt_push]`. Conclude with `H p ((inChart_push_iff ξ f x c p).mp hq)`.

Introduce `H p hp`. Establish `hm` using `H (push ξ f p) ((inChart_push_iff ξ f x c p).mpr hp)`. Rewrite `hm` using `[regAt_push]`. Then use the resulting hypothesis.
-/
theorem coordTie_comp {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω} {W : Scheme.{0}}
    {ξ : Sp Ω ⟶ W} (f : W ⟶ X) [IsOpenImmersion f] (hξ : IsCptGen (ξ ≫ f))
    (hr : ∀ q : Cpt (ξ ≫ f), ∃ p, push ξ f p = q) (h : CoordTie o ξ x) : CoordTie o (ξ ≫ f) x := by
  haveI : SurjectiveOnStalks f := inferInstance
  refine ⟨hξ, fun q => ?_, fun c hc => ?_, fun c hc a => ?_⟩
  · obtain ⟨p, rfl⟩ := hr q
    obtain ⟨c, hc⟩ := h.cover p
    exact ⟨c, (inChart_push_iff ξ f x c p).mpr hc⟩
  · obtain ⟨V, hV, hVmem⟩ := h.affine c hc
    refine ⟨f ''ᵁ V, hV.image_of_isOpenImmersion f, fun q => ?_⟩
    constructor
    · rintro ⟨q', hq'V, rfl⟩
      obtain ⟨h', hin⟩ := (hVmem q').mp hq'V
      exact ⟨(push ξ f ⟨q', h'⟩).2, (inChart_push_iff ξ f x c ⟨q', h'⟩).mpr hin⟩
    · rintro ⟨hq, hin⟩
      obtain ⟨p, hp⟩ := hr ⟨q, hq⟩
      have hin' : InChart (ξ ≫ f) x c (push ξ f p) := by
        rw [hp]
        exact hin
      have hpV : p.1 ∈ V := (hVmem p.1).mpr ⟨p.2, (inChart_push_iff ξ f x c p).mp hin'⟩
      have hq' : f p.1 = q := congrArg Subtype.val hp
      exact ⟨p.1, hpV, hq'⟩
  · rw [h.ring c hc a]
    constructor
    · intro H q hq
      obtain ⟨p, rfl⟩ := hr q
      rw [regAt_push]
      exact H p ((inChart_push_iff ξ f x c p).mp hq)
    · intro H p hp
      have hm := H (push ξ f p) ((inChart_push_iff ξ f x c p).mpr hp)
      rwa [regAt_push] at hm

/- English proof (translation)
Introduce `o _ _ X s hs Ω _ _ ξ hgen hover`. Take `⟨N, i, hi, his⟩` from `hs`. Use `haveI := hi`. Use `haveI hLN : IsLocallyNoetherian X := by`. Use `isLocallyNoetherian_of_affine_cover (S := fun c : Fin (N + 1) => ⟨i ⁻¹ᵁ chart o N c, (isAffineOpen_chart o N c).preimage i⟩) ?_ ?_` and prove the remaining obligations.

Rewrite using `[← Scheme.Hom.preimage_iSup, iSup_chart, Scheme.Hom.preimage_top]`. Introduce `c haveI : IsNoetherianRing Γ(PSpace o N, chart o N c) := isNoetherianRing_of_ringEquiv _ (chartAlgEquiv o N c).toRingEquiv`. Conclude with `isNoetherianRing_of_surjective _ _ (i.app (chart o N c)).hom (i.app_surjective _ (isAffineOpen_chart o N c))`. Establish `hW` using `isClopen_setOf_genPt_specializes X Ω ξ hgen`. Set `W : X.Opens` to `⟨{q | GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q}, hW.isOpen⟩`.

Establish `hrange : Set.range ξ ⊆ Set.range W.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨x, rfl⟩`. Use `show GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ ξ x`. Rewrite using `[Subsingleton.elim x (IsLocalRing.closedPoint Ω)]`.

Both sides reduce to the same expression. Set `ξ' : Sp Ω ⟶ W.toScheme` to `IsOpenImmersion.lift W.ι ξ hrange`. Establish `hfac : ξ' ≫ W.ι = ξ` using `IsOpenImmersion.lift_fac _ _ _`. Use `haveI : IsClosedImmersion W.ι := IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hW.isClosed)`. Establish `hy : (ξ' ≫ W.ι ≫ i) ≫ PSpace.str o N = spMap (algebraMap o Ω)`.

Rewrite using `[Category.assoc, Category.assoc, his, ← Category.assoc, hfac, hover]`. Take `⟨t, ht, hpt⟩` from `exists_point (ξ' ≫ W.ι ≫ i) hy`. Establish `hgen' : IsCptGen (ξ' ≫ W.ι)`. Rewrite using `[hfac]`. Conclude with `hgen`.

Establish `hcg : IsCptGen ξ'` using `isCptGen_of_comp ξ' W.ι hgen'`. Establish `hgp : W.ι (GlobalTheory.CompanionTheory.Ar.genPt ξ') = GlobalTheory.CompanionTheory.Ar.genPt ξ` using `by show (ξ' ≫ W.ι) (IsLocalRing.closedPoint Ω) = ξ (IsLocalRing.closedPoint Ω)`. Rewrite using `[hfac]`. Establish `hall' : ∀ q : W.toScheme, GlobalTheory.CompanionTheory.Ar.genPt ξ' ⤳ q`. Introduce `q`.

Rewrite using `[← W.ι.isOpenEmbedding.toIsInducing.specializes_iff, hgp]`. Conclude with `q.2`. Establish `hct : CoordTie o ξ' t` using `coordTie_of_all (i := W.ι ≫ i) hcg hall' hpt`. Establish `hr : ∀ q : Cpt (ξ' ≫ W.ι), ∃ p, push ξ' W.ι p = q`. Introduce `q`.

Establish `hq : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q.1`. Establish `h2` using `q.2`. Rewrite using `[← hgp]`. Conclude with `h2`. Conclude with `⟨⟨⟨q.1, hq⟩, hall' ⟨q.1, hq⟩⟩, rfl⟩`.

Establish `hfin` using `coordTie_comp W.ι hgen' hr hct`. Rewrite `hfin` using `[hfac]`. Conclude with `⟨N + 1, t, hfin⟩`.
-/
theorem xr_coords : ∀ (o : Type) [CommRing o] [IsNoetherianRing o] (X : Scheme.{0}) (s : X ⟶ Sp o), IsProjOver s → ∀ (Ω : Type) [Field Ω] [Algebra o Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → ξ ≫ s = spMap (algebraMap o Ω) → ∃ (n : ℕ) (x : Fin n → Ω), CoordTie o ξ x := by
  intro o _ _ X s hs Ω _ _ ξ hgen hover
  obtain ⟨N, i, hi, his⟩ := hs
  haveI := hi
  haveI hLN : IsLocallyNoetherian X := by
    refine isLocallyNoetherian_of_affine_cover
      (S := fun c : Fin (N + 1) => ⟨i ⁻¹ᵁ chart o N c, (isAffineOpen_chart o N c).preimage i⟩) ?_ ?_
    · rw [← Scheme.Hom.preimage_iSup, iSup_chart, Scheme.Hom.preimage_top]
    · intro c
      haveI : IsNoetherianRing Γ(PSpace o N, chart o N c) :=
        isNoetherianRing_of_ringEquiv _ (chartAlgEquiv o N c).toRingEquiv
      exact isNoetherianRing_of_surjective _ _ (i.app (chart o N c)).hom
        (i.app_surjective _ (isAffineOpen_chart o N c))
  have hW := isClopen_setOf_genPt_specializes X Ω ξ hgen
  let W : X.Opens := ⟨{q | GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q}, hW.isOpen⟩
  have hrange : Set.range ξ ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    show GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ ξ x
    rw [Subsingleton.elim x (IsLocalRing.closedPoint Ω)]
    rfl
  let ξ' : Sp Ω ⟶ W.toScheme := IsOpenImmersion.lift W.ι ξ hrange
  have hfac : ξ' ≫ W.ι = ξ := IsOpenImmersion.lift_fac _ _ _
  haveI : IsClosedImmersion W.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hW.isClosed)
  have hy : (ξ' ≫ W.ι ≫ i) ≫ PSpace.str o N = spMap (algebraMap o Ω) := by
    rw [Category.assoc, Category.assoc, his, ← Category.assoc, hfac, hover]
  obtain ⟨t, ht, hpt⟩ := exists_point (ξ' ≫ W.ι ≫ i) hy
  have hgen' : IsCptGen (ξ' ≫ W.ι) := by
    rw [hfac]
    exact hgen
  have hcg : IsCptGen ξ' := isCptGen_of_comp ξ' W.ι hgen'
  have hgp : W.ι (GlobalTheory.CompanionTheory.Ar.genPt ξ') = GlobalTheory.CompanionTheory.Ar.genPt ξ := by
    show (ξ' ≫ W.ι) (IsLocalRing.closedPoint Ω) = ξ (IsLocalRing.closedPoint Ω)
    rw [hfac]
  have hall' : ∀ q : W.toScheme, GlobalTheory.CompanionTheory.Ar.genPt ξ' ⤳ q := by
    intro q
    rw [← W.ι.isOpenEmbedding.toIsInducing.specializes_iff, hgp]
    exact q.2
  have hct : CoordTie o ξ' t := coordTie_of_all (i := W.ι ≫ i) hcg hall' hpt
  have hr : ∀ q : Cpt (ξ' ≫ W.ι), ∃ p, push ξ' W.ι p = q := by
    intro q
    have hq : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q.1 := by
      have h2 := q.2
      rw [← hgp]
      exact h2
    exact ⟨⟨⟨q.1, hq⟩, hall' ⟨q.1, hq⟩⟩, rfl⟩
  have hfin := coordTie_comp W.ι hgen' hr hct
  rw [hfac] at hfin
  exact ⟨N + 1, t, hfin⟩

/- English proof (translation)
Rewrite using `[specializes_iff_mem_closure]`. Establish `hr : Set.range ξ.base = {GlobalTheory.CompanionTheory.Ar.genPt ξ}`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`.

Rewrite using `[Set.mem_singleton_iff, Subsingleton.elim x (IsLocalRing.closedPoint Ω)]`. Both sides reduce to the same expression. Introduce and unpack `rfl`. Conclude with `⟨_, rfl⟩`. Rewrite using `[← hr, (Scheme.Hom.denseRange ξ).closure_range]`.

Discharge the goal by the elementary cases of `trivial`.
-/
theorem all_of_isDominant (ξ : Sp Ω ⟶ X) [IsDominant ξ] (q : X) : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q := by
  rw [specializes_iff_mem_closure]
  have hr : Set.range ξ.base = {GlobalTheory.CompanionTheory.Ar.genPt ξ} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      rw [Set.mem_singleton_iff, Subsingleton.elim x (IsLocalRing.closedPoint Ω)]
      rfl
    · rintro rfl
      exact ⟨_, rfl⟩
  rw [← hr, (Scheme.Hom.denseRange ξ).closure_range]
  trivial

/- English proof (translation)
Establish `hall` using `all_of_isDominant ξ`. Use `haveI : IrreducibleSpace X := by`. Rewrite using `[irreducibleSpace_def]`. Establish `hcl : closure {GlobalTheory.CompanionTheory.Ar.genPt ξ} = (Set.univ : Set X)` using `Set.eq_univ_of_forall fun q => specializes_iff_mem_closure.mp (hall q)`. Rewrite using `[Set.top_eq_univ, ← hcl]`.

Conclude with `isIrreducible_singleton.closure`. Use `haveI : AlgebraicGeometry.IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X`. Use `⟨h, fun p => ?_⟩` and prove the remaining obligations. Establish `hinj : Function.Injective (X.presheaf.stalkSpecializes p.2).hom`. Establish `hc : X.presheaf.stalkSpecializes p.2 ≫ X.presheaf.stalkSpecializes (genericPoint_specializes (GlobalTheory.CompanionTheory.Ar.genPt ξ)) = X.presheaf.stalkSpecializes (genericPoint_specializes p.1)` using `TopCat.Presheaf.stalkSpecializes_comp _ _ _`.

Establish `hi : Function.Injective (algebraMap (X.presheaf.stalk p.1) X.functionField)` using `IsFractionRing.injective _ _`. Introduce `a b hab`. Apply `hi` to reduce the goal to its premises. Establish `ea` using `congrArg (fun φ => φ.hom a) hc`. Establish `eb` using `congrArg (fun φ => φ.hom b) hc`.

Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at ea eb`. Use `show (X.presheaf.stalkSpecializes (genericPoint_specializes p.1)).hom a = (X.presheaf.stalkSpecializes (genericPoint_specializes p.1)).hom b`. Rewrite using `[← ea, ← eb, hab]`. Introduce `a b hab`. Conclude with `hinj (h.1 hab)`.
-/
theorem isCptGen_of_isDominant (ξ : Sp Ω ⟶ X) [IsDominant ξ] [IsReduced X]
    (h : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom) : IsCptGen ξ := by
  have hall := all_of_isDominant ξ
  haveI : IrreducibleSpace X := by
    rw [irreducibleSpace_def]
    have hcl : closure {GlobalTheory.CompanionTheory.Ar.genPt ξ} = (Set.univ : Set X) :=
      Set.eq_univ_of_forall fun q => specializes_iff_mem_closure.mp (hall q)
    rw [Set.top_eq_univ, ← hcl]
    exact isIrreducible_singleton.closure
  haveI : AlgebraicGeometry.IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  refine ⟨h, fun p => ?_⟩
  have hinj : Function.Injective (X.presheaf.stalkSpecializes p.2).hom := by
    have hc : X.presheaf.stalkSpecializes p.2 ≫
        X.presheaf.stalkSpecializes (genericPoint_specializes (GlobalTheory.CompanionTheory.Ar.genPt ξ)) =
        X.presheaf.stalkSpecializes (genericPoint_specializes p.1) :=
      TopCat.Presheaf.stalkSpecializes_comp _ _ _
    have hi : Function.Injective (algebraMap (X.presheaf.stalk p.1) X.functionField) :=
      IsFractionRing.injective _ _
    intro a b hab
    apply hi
    have ea := congrArg (fun φ => φ.hom a) hc
    have eb := congrArg (fun φ => φ.hom b) hc
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at ea eb
    show (X.presheaf.stalkSpecializes (genericPoint_specializes p.1)).hom a =
      (X.presheaf.stalkSpecializes (genericPoint_specializes p.1)).hom b
    rw [← ea, ← eb, hab]
  intro a b hab
  exact hinj (h.1 hab)

/- English proof (translation)
Take `⟨i, hi⟩` from `GlobalTheory.ProjSpace.exists_mem_chart o n q.1`. Establish `hg : point o t ht (IsLocalRing.closedPoint Ω) ∈ chart o n i` using `q.2.mem_open (chart o n i).isOpen hi`. Establish `hle : ⊤ ≤ point o t ht ⁻¹ᵁ chart o n i` using `(Scheme.preimage_eq_top_of_closedPoint_mem _ hg).ge`. Establish `hti : t i ≠ 0` using `(GlobalTheory.TuplePoint.le_point_preimage_iff i).mp hle`. Rewrite using `[GlobalTheory.TupleNorm.ratioField_eq o hti]`.

Establish `hU : IsAffineOpen (chart o n i)` using `GlobalTheory.ProjSpace.isAffineOpen_chart o n i`. Set `xU : (chart o n i : (PSpace o n).Opens)` to `⟨q.1, hi⟩`. Use `letI := TopCat.Presheaf.algebra_section_stalk (PSpace o n).presheaf xU`. Use `haveI := hU.isLocalization_stalk xU`. Take `⟨⟨a, s⟩, hs⟩` from `IsLocalization.surj (hU.primeIdealOf xU).asIdeal.primeCompl g`.

Establish `hmem : ∀ b : Γ(PSpace o n, chart o n i), genMap (point o t ht) q ((PSpace o n).presheaf.germ _ q.1 hi b) ∈ GlobalTheory.TupleCone.ratioRing o t i`. Introduce `b`. Rewrite using `[genMap_germ_eq _ q hi b]`. Establish `hb : valR (point o t ht) (chart o n i) b ∈ Set.range (valMap (point o t ht) (chart o n i) hle).hom` using `⟨b, by simp [valR, dif_pos hle, valMap]⟩`. Rewrite `hb` using `[GlobalTheory.TuplePoint.range_valMap_point hle]`.

Conclude with `hb`. Establish `hunit : IsUnit (algebraMap Γ(PSpace o n, chart o n i) ((PSpace o n).presheaf.stalk q.1) s)` using `IsLocalization.map_units _ s`. Establish `hs'` using `congrArg (genMap (point o t ht) q) hs`. Rewrite `hs'` using `[map_mul]`. Establish `hne : genMap (point o t ht) q (algebraMap Γ(PSpace o n, chart o n i) ((PSpace o n).presheaf.stalk q.1) s) ≠ 0` using `(hunit.map _).ne_zero`.

Establish `heq : genMap (point o t ht) q g = genMap (point o t ht) q (algebraMap Γ(PSpace o n, chart o n i) ((PSpace o n).presheaf.stalk q.1) a) / genMap (point o t ht) q (algebraMap Γ(PSpace o n, chart o n i) ((PSpace o n).presheaf.stalk q.1) s)`. Rewrite using `[← hs', mul_div_cancel_right₀ _ hne]`. Rewrite using `[heq]`. Conclude with `div_mem (Subfield.subset_closure (hmem a)) (Subfield.subset_closure (hmem s))`.
-/
theorem genMap_point_mem {o : Type} [CommRing o] [Algebra o Ω] {n : ℕ} {t : Fin (n + 1) → Ω} {ht : t ≠ 0}
    (q : Cpt (point o t ht)) (g : (PSpace o n).presheaf.stalk q.1) :
    genMap (point o t ht) q g ∈ GlobalTheory.TupleNorm.ratioField o t := by
  obtain ⟨i, hi⟩ := GlobalTheory.ProjSpace.exists_mem_chart o n q.1
  have hg : point o t ht (IsLocalRing.closedPoint Ω) ∈ chart o n i := q.2.mem_open (chart o n i).isOpen hi
  have hle : ⊤ ≤ point o t ht ⁻¹ᵁ chart o n i := (Scheme.preimage_eq_top_of_closedPoint_mem _ hg).ge
  have hti : t i ≠ 0 := (GlobalTheory.TuplePoint.le_point_preimage_iff i).mp hle
  rw [GlobalTheory.TupleNorm.ratioField_eq o hti]
  have hU : IsAffineOpen (chart o n i) := GlobalTheory.ProjSpace.isAffineOpen_chart o n i
  let xU : (chart o n i : (PSpace o n).Opens) := ⟨q.1, hi⟩
  letI := TopCat.Presheaf.algebra_section_stalk (PSpace o n).presheaf xU
  haveI := hU.isLocalization_stalk xU
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (hU.primeIdealOf xU).asIdeal.primeCompl g
  have hmem : ∀ b : Γ(PSpace o n, chart o n i),
      genMap (point o t ht) q ((PSpace o n).presheaf.germ _ q.1 hi b) ∈ GlobalTheory.TupleCone.ratioRing o t i := by
    intro b
    rw [genMap_germ_eq _ q hi b]
    have hb : valR (point o t ht) (chart o n i) b ∈
        Set.range (valMap (point o t ht) (chart o n i) hle).hom :=
      ⟨b, by simp [valR, dif_pos hle, valMap]⟩
    rw [GlobalTheory.TuplePoint.range_valMap_point hle] at hb
    exact hb
  have hunit : IsUnit (algebraMap Γ(PSpace o n, chart o n i) ((PSpace o n).presheaf.stalk q.1) s) :=
    IsLocalization.map_units _ s
  have hs' := congrArg (genMap (point o t ht) q) hs
  rw [map_mul] at hs'
  have hne : genMap (point o t ht) q (algebraMap Γ(PSpace o n, chart o n i) ((PSpace o n).presheaf.stalk q.1) s) ≠ 0 :=
    (hunit.map _).ne_zero
  have heq : genMap (point o t ht) q g =
      genMap (point o t ht) q (algebraMap Γ(PSpace o n, chart o n i) ((PSpace o n).presheaf.stalk q.1) a) /
      genMap (point o t ht) q (algebraMap Γ(PSpace o n, chart o n i) ((PSpace o n).presheaf.stalk q.1) s) := by
    rw [← hs', mul_div_cancel_right₀ _ hne]
  rw [heq]
  exact div_mem (Subfield.subset_closure (hmem a)) (Subfield.subset_closure (hmem s))

/- English proof (translation)
Introduce `X s hproj Ω _ _ ξ hfin`. Take `⟨N, i, hi_ci, hstr⟩` from `hproj`. Establish `hy : (ξ ≫ i) ≫ PSpace.str ℤ N = spMap (algebraMap ℤ Ω)` using `specZIsTerminal.hom_ext _ _`. Take `⟨t, ht, hpt⟩` from `exists_point (ξ ≫ i) hy`. Establish `hrange : ∀ k, (Scheme.descResidueField (Scheme.stalkClosedPointTo ξ)).hom k ∈ GlobalTheory.TupleNorm.ratioField ℤ t`.

Introduce `k`. Take `⟨g, rfl⟩` from `X.residue_surjective _ k`. Establish `e1 : (Scheme.descResidueField (Scheme.stalkClosedPointTo ξ)).hom ((X.residue _).hom g) = (Scheme.stalkClosedPointTo ξ).hom g`. Rewrite using `[← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.residue_descResidueField]`. Rewrite using `[e1]`.

Take `⟨g', rfl⟩` from `i.stalkMap_surjective _ g`. Establish `e2 : (Scheme.stalkClosedPointTo ξ).hom ((i.stalkMap _).hom g') = (Scheme.stalkClosedPointTo (ξ ≫ i)).hom g'`. Rewrite using `[Scheme.stalkClosedPointTo_comp]`. Both sides reduce to the same expression. Rewrite using `[e2]`.

Establish `key : ∀ (g₁ g₂ : Sp Ω ⟶ PSpace ℤ N) (_ : g₁ = g₂) (b : (PSpace ℤ N).presheaf.stalk (g₁ (IsLocalRing.closedPoint Ω))), ∃ b', (Scheme.stalkClosedPointTo g₂).hom b' = (Scheme.stalkClosedPointTo g₁).hom b`. Introduce and unpack `g₁ g₂ rfl b`. Conclude with `⟨b, rfl⟩`. Take `⟨b', hb'⟩` from `key _ _ hpt g'`. Rewrite using `[← hb']`.

Establish `hq` using `genMap_point_mem (⟨GlobalTheory.CompanionTheory.Ar.genPt (point ℤ t ht), specializes_refl _⟩ : Cpt (point ℤ t ht)) b'`. Establish `e3 : genMap (point ℤ t ht) ⟨GlobalTheory.CompanionTheory.Ar.genPt (point ℤ t ht), specializes_refl _⟩ b' = (Scheme.stalkClosedPointTo (point ℤ t ht)).hom b'`. Establish `h4` using `congrArg (fun φ => (φ ≫ Scheme.stalkClosedPointTo (point ℤ t ht)).hom b') (TopCat.Presheaf.stalkSpecializes_refl (PSpace ℤ N).presheaf (GlobalTheory.CompanionTheory.Ar.genPt (point ℤ t ht)))`. Simplify using `only [Category.id_comp] at h4`. Conclude with `h4`.

Rewrite `hq` using `[e3]`. Then use the resulting hypothesis. Use `haveI hFD : FiniteDimensional (GlobalTheory.TupleNorm.ratioField ℤ t) Ω := by`. Set `d'` to `(Scheme.descResidueField (Scheme.stalkClosedPointTo ξ)).hom.codRestrict (GlobalTheory.TupleNorm.ratioField ℤ t) hrange`. Establish `hcomp : (algebraMap (GlobalTheory.TupleNorm.ratioField ℤ t) Ω).comp d' = (Scheme.descResidueField (Scheme.stalkClosedPointTo ξ)).hom` using `rfl`. Rewrite `hfin` using `[← hcomp]`.

Conclude with `RingHom.finite_algebraMap.mp (RingHom.Finite.of_comp_finite hfin)`. Use `haveI : Algebra.EssFiniteType ℤ Ω := GlobalTheory.TupleNorm.essFiniteType_of_finiteDimensional ℤ t ht`. Set `ν` to `GlobalTheory.TupleNorm.nmPoint ℤ t ht`. Use `haveI : AlgebraicGeometry.IsIntegral (GlobalTheory.TupleNorm.Nm ℤ t ht) := GlobalTheory.TupleNorm.isIntegral_Nm ℤ t ht`. Establish `hsupp` using `Scheme.Hom.support_ker ν`.

Rewrite `hsupp` using `[Scheme.Hom.ker_toNormalization, Scheme.IdealSheafData.support_bot]`. Use `haveI hdom : IsDominant ν := ⟨by`. Rewrite using `[DenseRange, dense_iff_closure_eq, ← hsupp]`. Use the proof step `simp⟩`. Establish `hall` using `all_of_isDominant ν`.

Establish `hbij` using `(bijective_iff_isIso_stalkMap ν (IsLocalRing.closedPoint Ω)).mpr (GlobalTheory.TupleNorm.isIso_stalkMap_nmPoint ℤ t ht _)`. Establish `hgen : IsCptGen ν` using `isCptGen_of_isDominant ν hbij`. Take `⟨n, x, htie⟩` from `xr_coords ℤ _ (GlobalTheory.TupleNorm.str ℤ t ht) (GlobalTheory.TupleNorm.isProjOver_str ℤ t ht) Ω ν hgen (GlobalTheory.TupleNorm.nmPoint_str ℤ t ht)`. Establish `hnorm : Flat.NormalCpt ν` using `((xr_normal _ Ω ν hgen hall).2).mpr (GlobalTheory.TupleNorm.isNormalScheme_Nm ℤ t ht)`. Establish `hker : i.ker ≤ (GlobalTheory.TupleNorm.clι ℤ t ht).ker`.

Rewrite using `[GlobalTheory.TupleNorm.clι, Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι, ← hpt]`. Conclude with `Scheme.Hom.le_ker_comp ξ i`. Set `l` to `IsClosedImmersion.lift i (GlobalTheory.TupleNorm.clι ℤ t ht) hker`. Establish `hl : l ≫ i = GlobalTheory.TupleNorm.clι ℤ t ht` using `IsClosedImmersion.lift_fac _ _ _`. Use `haveI : IsClosedImmersion l := by haveI : IsClosedImmersion (l ≫ i) := by`.

Rewrite using `[hl]`. Use `infer_instance`. Conclude with `IsClosedImmersion.of_comp_isClosedImmersion l i`. Use `haveI : IsFinite (GlobalTheory.TupleNorm.toCl ℤ t ht) := GlobalTheory.TupleNorm.isFinite_toCl ℤ t ht`. Use `⟨n, x, ⟨_, ν, GlobalTheory.TupleNorm.str ℤ t ht, GlobalTheory.TupleNorm.nmPoint_str ℤ t ht, hall, htie⟩, GlobalTheory.TupleNorm.toCl ℤ t ht ≫ l, hnorm, inferInstance, ?_⟩` and prove the remaining obligations.

Use `show ν ≫ GlobalTheory.TupleNorm.toCl ℤ t ht ≫ l = ξ`. Rewrite using `[← cancel_mono i, Category.assoc, Category.assoc, hl, hpt]`. Conclude with `GlobalTheory.TupleNorm.nmPoint_toProj ℤ t ht`.
-/
theorem xr_norm : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℤ), IsProjOver s → ∀ (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X), (Scheme.descResidueField (Scheme.stalkClosedPointTo ξ)).hom.Finite → ∃ (n : ℕ) (x : Fin n → Ω) (M : PModel ℤ x) (π : M.X ⟶ X), Flat.NormalCpt M.ξ ∧ IsFinite π ∧ M.ξ ≫ π = ξ := by
  intro X s hproj Ω _ _ ξ hfin
  obtain ⟨N, i, hi_ci, hstr⟩ := hproj
  have hy : (ξ ≫ i) ≫ PSpace.str ℤ N = spMap (algebraMap ℤ Ω) := specZIsTerminal.hom_ext _ _
  obtain ⟨t, ht, hpt⟩ := exists_point (ξ ≫ i) hy
  have hrange : ∀ k, (Scheme.descResidueField (Scheme.stalkClosedPointTo ξ)).hom k ∈
      GlobalTheory.TupleNorm.ratioField ℤ t := by
    intro k
    obtain ⟨g, rfl⟩ := X.residue_surjective _ k
    have e1 : (Scheme.descResidueField (Scheme.stalkClosedPointTo ξ)).hom ((X.residue _).hom g) =
        (Scheme.stalkClosedPointTo ξ).hom g := by
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.residue_descResidueField]
    rw [e1]
    obtain ⟨g', rfl⟩ := i.stalkMap_surjective _ g
    have e2 : (Scheme.stalkClosedPointTo ξ).hom ((i.stalkMap _).hom g') =
        (Scheme.stalkClosedPointTo (ξ ≫ i)).hom g' := by
      rw [Scheme.stalkClosedPointTo_comp]
      rfl
    rw [e2]
    have key : ∀ (g₁ g₂ : Sp Ω ⟶ PSpace ℤ N) (_ : g₁ = g₂)
        (b : (PSpace ℤ N).presheaf.stalk (g₁ (IsLocalRing.closedPoint Ω))),
        ∃ b', (Scheme.stalkClosedPointTo g₂).hom b' = (Scheme.stalkClosedPointTo g₁).hom b := by
      rintro g₁ g₂ rfl b
      exact ⟨b, rfl⟩
    obtain ⟨b', hb'⟩ := key _ _ hpt g'
    rw [← hb']
    have hq := genMap_point_mem (⟨GlobalTheory.CompanionTheory.Ar.genPt (point ℤ t ht), specializes_refl _⟩ : Cpt (point ℤ t ht)) b'
    have e3 : genMap (point ℤ t ht) ⟨GlobalTheory.CompanionTheory.Ar.genPt (point ℤ t ht), specializes_refl _⟩ b' =
        (Scheme.stalkClosedPointTo (point ℤ t ht)).hom b' := by
      have h4 := congrArg (fun φ => (φ ≫ Scheme.stalkClosedPointTo (point ℤ t ht)).hom b')
        (TopCat.Presheaf.stalkSpecializes_refl (PSpace ℤ N).presheaf (GlobalTheory.CompanionTheory.Ar.genPt (point ℤ t ht)))
      simp only [Category.id_comp] at h4
      exact h4
    rwa [e3] at hq
  haveI hFD : FiniteDimensional (GlobalTheory.TupleNorm.ratioField ℤ t) Ω := by
    let d' := (Scheme.descResidueField (Scheme.stalkClosedPointTo ξ)).hom.codRestrict
      (GlobalTheory.TupleNorm.ratioField ℤ t) hrange
    have hcomp : (algebraMap (GlobalTheory.TupleNorm.ratioField ℤ t) Ω).comp d' =
        (Scheme.descResidueField (Scheme.stalkClosedPointTo ξ)).hom := rfl
    rw [← hcomp] at hfin
    exact RingHom.finite_algebraMap.mp (RingHom.Finite.of_comp_finite hfin)
  haveI : Algebra.EssFiniteType ℤ Ω := GlobalTheory.TupleNorm.essFiniteType_of_finiteDimensional ℤ t ht
  let ν := GlobalTheory.TupleNorm.nmPoint ℤ t ht
  haveI : AlgebraicGeometry.IsIntegral (GlobalTheory.TupleNorm.Nm ℤ t ht) := GlobalTheory.TupleNorm.isIntegral_Nm ℤ t ht
  have hsupp := Scheme.Hom.support_ker ν
  rw [Scheme.Hom.ker_toNormalization, Scheme.IdealSheafData.support_bot] at hsupp
  haveI hdom : IsDominant ν := ⟨by
    rw [DenseRange, dense_iff_closure_eq, ← hsupp]
    simp⟩
  have hall := all_of_isDominant ν
  have hbij := (bijective_iff_isIso_stalkMap ν (IsLocalRing.closedPoint Ω)).mpr
    (GlobalTheory.TupleNorm.isIso_stalkMap_nmPoint ℤ t ht _)
  have hgen : IsCptGen ν := isCptGen_of_isDominant ν hbij
  obtain ⟨n, x, htie⟩ := xr_coords ℤ _ (GlobalTheory.TupleNorm.str ℤ t ht) (GlobalTheory.TupleNorm.isProjOver_str ℤ t ht)
    Ω ν hgen (GlobalTheory.TupleNorm.nmPoint_str ℤ t ht)
  have hnorm : Flat.NormalCpt ν :=
    ((xr_normal _ Ω ν hgen hall).2).mpr (GlobalTheory.TupleNorm.isNormalScheme_Nm ℤ t ht)
  have hker : i.ker ≤ (GlobalTheory.TupleNorm.clι ℤ t ht).ker := by
    rw [GlobalTheory.TupleNorm.clι, Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι, ← hpt]
    exact Scheme.Hom.le_ker_comp ξ i
  let l := IsClosedImmersion.lift i (GlobalTheory.TupleNorm.clι ℤ t ht) hker
  have hl : l ≫ i = GlobalTheory.TupleNorm.clι ℤ t ht := IsClosedImmersion.lift_fac _ _ _
  haveI : IsClosedImmersion l := by
    haveI : IsClosedImmersion (l ≫ i) := by
      rw [hl]
      infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion l i
  haveI : IsFinite (GlobalTheory.TupleNorm.toCl ℤ t ht) := GlobalTheory.TupleNorm.isFinite_toCl ℤ t ht
  refine ⟨n, x, ⟨_, ν, GlobalTheory.TupleNorm.str ℤ t ht, GlobalTheory.TupleNorm.nmPoint_str ℤ t ht, hall, htie⟩,
    GlobalTheory.TupleNorm.toCl ℤ t ht ≫ l, hnorm, inferInstance, ?_⟩
  show ν ≫ GlobalTheory.TupleNorm.toCl ℤ t ht ≫ l = ξ
  rw [← cancel_mono i, Category.assoc, Category.assoc, hl, hpt]
  exact GlobalTheory.TupleNorm.nmPoint_toProj ℤ t ht

end PositivityTheory.HtPt.Mf
