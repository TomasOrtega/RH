import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EigenBasisIffTangentBasis
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LieBasisIffTangentBasisPullbackUniversal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsTangentVectorBasisAtPointBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueScaledBaseChangeFibreSection
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFibreSectionNowhereZeroOfPullbackTriple
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionGeneratesOfNowhereZeroNoetherianBase
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsChartEigenframe
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankOfIsSecBasis
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsOfH0EqOneClosedFields
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsBasisOfFormEq
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.Frames

namespace GlobalTheory.LocalFrame

/- English proof (translation)
Use `(GlobalTheory.AbLaw.AllLaws.laws_of_h0_eq_one fun K _ _ P => ?_).1.secBaseChange` and prove the remaining obligations. Take `⟨b, hb⟩` from `GlobalTheory.PowBasis.exists_basis_pow hT P 1 le_rfl K (𝟙 _)`. Establish `: Nontrivial Γ((Over.mk (𝟙 (Spec (CommRingCat.of K)))).left, ⊤)` using `(Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial`. Conclude with `(GlobalTheory.SecTwist.finrank_of_isSecBasis P.A P.L _ _ b hb).trans (one_pow _)`.
-/
theorem secBaseChange_of_secTwist (hT : Out.SecTwistSt) : Out.SecBaseChangeSt := by
  refine (GlobalTheory.AbLaw.AllLaws.laws_of_h0_eq_one fun K _ _ P => ?_).1.secBaseChange
  obtain ⟨b, hb⟩ := GlobalTheory.PowBasis.exists_basis_pow hT P 1 le_rfl K (𝟙 _)
  have : Nontrivial Γ((Over.mk (𝟙 (Spec (CommRingCat.of K)))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  exact (GlobalTheory.SecTwist.finrank_of_isSecBasis P.A P.L _ _ b hb).trans (one_pow _)

/- English proof (translation)
Take `⟨s, hs⟩` from `(IsNoetherian.noetherian (RingHom.ker (algebraMap R (Localization.AtPrime q))))`. Establish `h1 : ∀ a : s, ∃ m : q.primeCompl, (m : R) * a = 0` using `fun a => (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) (a : R)).1 (by rw [← RingHom.mem_ker, ← hs]; exact Submodule.subset_span a.2)`. Use `choose m hm using h1`. Set `g : q.primeCompl` to `∏ a, m a`. Establish `hg : ∀ a ∈ RingHom.ker (algebraMap R (Localization.AtPrime q)), (g : R) * a = 0`.

Introduce `a ha`. Rewrite `ha` using `[← hs]`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem a ha`. Choose the witnesses or unpack the hypotheses as in `⟨r, hr⟩ : (m ⟨a, ha⟩ : R) ∣ (g : R) := by`.

Simplify using `only [g, Submonoid.coe_finset_prod]`. Conclude with `Finset.dvd_prod_of_mem (fun a => (m a : R)) (Finset.mem_univ _)`. Rewrite using `[hr, mul_right_comm, hm ⟨a, ha⟩, zero_mul]`. Consider the case `zero => exact mul_zero _`. Consider the case `add a b _ _ ha hb => rw [mul_add, ha, hb, add_zero]`.

Consider the case `smul r a _ ha => rw [smul_eq_mul, mul_left_comm, ha, mul_zero]`. Use `⟨g, g.2, ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit (algebraMap R (Localization.AtPrime q) g)` using `IsLocalization.map_units _ g`. Set `f : Localization.Away (g : R) →+* Localization.AtPrime q` to `IsLocalization.Away.lift (g : R) hu`. Use `Function.Injective.isDomain f ((injective_iff_map_eq_zero f).2 fun x hx => ?_)` and prove the remaining obligations.

Take `⟨n, a, ha⟩` from `IsLocalization.Away.surj (g : R) x`. Establish `h2 : algebraMap R (Localization.AtPrime q) a = 0`. Rewrite using `[← IsLocalization.Away.lift_eq (S := Localization.Away (g : R)) (g : R) hu a, ← ha, map_mul]`. Conclude with `(congrArg (· * _) hx).trans (zero_mul _)`. Establish `hu' : IsUnit (algebraMap R (Localization.Away (g : R)) g)` using `IsLocalization.Away.algebraMap_isUnit _`.

Establish `h3 : algebraMap R (Localization.Away (g : R)) a = 0`. Rewrite using `[← hu'.mul_right_eq_zero, ← map_mul, hg a h2, map_zero]`. Rewrite `ha` using `[h3]`. Conclude with `(hu'.pow n).mul_left_eq_zero.1 ha`.
-/
theorem exists_away_isDomain {R : Type} [CommRing R] [IsNoetherianRing R] (q : Ideal R) [q.IsPrime]
    [IsDomain (Localization.AtPrime q)] : ∃ g ∉ q, IsDomain (Localization.Away g) := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (RingHom.ker (algebraMap R (Localization.AtPrime q))))
  have h1 : ∀ a : s, ∃ m : q.primeCompl, (m : R) * a = 0 := fun a =>
    (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) (a : R)).1
      (by rw [← RingHom.mem_ker, ← hs]; exact Submodule.subset_span a.2)
  choose m hm using h1
  let g : q.primeCompl := ∏ a, m a
  have hg : ∀ a ∈ RingHom.ker (algebraMap R (Localization.AtPrime q)), (g : R) * a = 0 := by
    intro a ha
    rw [← hs] at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨r, hr⟩ : (m ⟨a, ha⟩ : R) ∣ (g : R) := by
        simp only [g, Submonoid.coe_finset_prod]
        exact Finset.dvd_prod_of_mem (fun a => (m a : R)) (Finset.mem_univ _)
      rw [hr, mul_right_comm, hm ⟨a, ha⟩, zero_mul]
    | zero => exact mul_zero _
    | add a b _ _ ha hb => rw [mul_add, ha, hb, add_zero]
    | smul r a _ ha => rw [smul_eq_mul, mul_left_comm, ha, mul_zero]
  refine ⟨g, g.2, ?_⟩
  have hu : IsUnit (algebraMap R (Localization.AtPrime q) g) := IsLocalization.map_units _ g
  let f : Localization.Away (g : R) →+* Localization.AtPrime q := IsLocalization.Away.lift (g : R) hu
  refine Function.Injective.isDomain f ((injective_iff_map_eq_zero f).2 fun x hx => ?_)
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (g : R) x
  have h2 : algebraMap R (Localization.AtPrime q) a = 0 := by
    rw [← IsLocalization.Away.lift_eq (S := Localization.Away (g : R)) (g : R) hu a, ← ha, map_mul]
    exact (congrArg (· * _) hx).trans (zero_mul _)
  have hu' : IsUnit (algebraMap R (Localization.Away (g : R)) g) := IsLocalization.Away.algebraMap_isUnit _
  have h3 : algebraMap R (Localization.Away (g : R)) a = 0 := by
    rw [← hu'.mul_right_eq_zero, ← map_mul, hg a h2, map_zero]
  rw [h3] at ha
  exact (hu'.pow n).mul_left_eq_zero.1 ha

/- English proof (translation)
Introduce `τ`. Establish `hcard : Nat.card {i // (e i).1 = τ} = Dw.mult τ`. Establish `e2 : {i // (e i).1 = τ} ≃ {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ}` using `e.subtypeEquiv (fun _ => Iff.rfl)`. Establish `e3 : {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ} ≃ Fin (Dw.mult τ)` using `Equiv.sigmaSubtype τ`. Rewrite using `[Nat.card_congr (e2.trans e3), Nat.card_eq_fintype_card, Fintype.card_fin]`.

Use `⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Use `hcard.trans ?_` and prove the remaining obligations. Unfold `Datum.mult`. Rewrite using `[if_pos h]`. Use `hcard.trans ?_` and prove the remaining obligations.

Unfold `Datum.mult`. Rewrite using `[if_neg h]`.
-/
theorem isTypeFn_fst {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : IsTypeFn H Dw.p Dw.q (fun j => (e j).1) := by
  intro τ
  have hcard : Nat.card {i // (e i).1 = τ} = Dw.mult τ := by
    have e2 : {i // (e i).1 = τ} ≃ {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ} :=
      e.subtypeEquiv (fun _ => Iff.rfl)
    have e3 : {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ} ≃ Fin (Dw.mult τ) := Equiv.sigmaSubtype τ
    rw [Nat.card_congr (e2.trans e3), Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine hcard.trans ?_
    unfold Datum.mult
    rw [if_pos h]
  · refine hcard.trans ?_
    unfold Datum.mult
    rw [if_neg h]

/- English proof (translation)
Unfold `spMap`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

/- English proof (translation)
Apply the tactic sequence `ext s <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem dualMap_comp_epsMul {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    (dualMap ψ).comp (epsMul a) = (epsMul (ψ a)).comp (dualMap ψ) := by
  ext s <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Introduce `a`. Rewrite using `[Category.assoc, hv a, ← Category.assoc, spMap_spMap, dualMap_comp_epsMul, ← spMap_spMap, Category.assoc, hψ]`.
-/
theorem isEigAt_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (ψ : S →+* T) (hψ : ∀ a, ψ (algebraMap c.F S a) = algebraMap c.F T a) (τ : E →+* ℂ)
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsEigAt c τ v) :
    IsEigAt c τ (spMap (dualMap ψ) ≫ v) := by
  intro a
  rw [Category.assoc, hv a, ← Category.assoc, spMap_spMap, dualMap_comp_epsMul, ← spMap_spMap,
    Category.assoc, hψ]

/- English proof (translation)
Use `Xo.smooth` as an intermediate fact. Establish `: Smooth Xo.s` using `SmoothOfRelativeDimension.smooth Dw.dim Xo.s`. Establish `h : Smooth (spMap (algebraMap c.F R))` using `by rw [← hs]; infer_instance`. Establish `h'` using `(HasRingHomProperty.Spec_iff (P := @Smooth)).1 h`. Conclude with `RingHom.smooth_algebraMap.1 h'`.
-/
theorem smooth_of_chart {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {R : Type} [CommRing R] [Algebra c.F R] (j : Sp R ⟶ Xo.XF c)
    [IsOpenImmersion j] (hs : j ≫ pullback.snd _ _ = spMap (algebraMap c.F R)) : Algebra.Smooth c.F R := by
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have h : Smooth (spMap (algebraMap c.F R)) := by rw [← hs]; infer_instance
  have h' := (HasRingHomProperty.Spec_iff (P := @Smooth)).1 h
  exact RingHom.smooth_algebraMap.1 h'

/- English proof (translation)
Introduce `hT E _ _ _ H Dw l Xo c z`. Establish `hS` using `secBaseChange_of_secTwist hT`. Set `e` to `(Fintype.equivFin (Σ τ : E →+* ℂ, Fin (Dw.mult τ))).symm`. Take `⟨R, _, _, jR, o, v, th, hft, hred, hjR, ⟨q, hq⟩, hs, ⟨m⟩, hv, hev, hth, -⟩` from `GlobalTheory.ModuliChart.exists_chart_eigenframe hS E H Dw l Xo c _ _ (isTypeFn_fst Dw e) z`. Set `x : Sp R ⟶ Xo.X` to `jR ≫ pullback.fst _ _`.

Establish `hb : TanBasis x (fun i => (v i).left ≫ m.cm.F)` using `((GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo R x o.t.G m.cm.F m.cart).2 _ v).1 hv`. Set `u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left)` to `fun τ i => (v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F`. Establish `heig : ∀ τ i, IsEigAt c τ (u τ i)`. Introduce `τ i a`. Establish `h` using `hev (e.symm ⟨τ, i⟩) a`.

Simplify using `only [Equiv.apply_symm_apply] at h`. Establish `h' : (v (e.symm ⟨τ, i⟩)).left ≫ (o.t.act.act a).left = spMap (epsMul (algebraMap c.F R (embK c τ a))) ≫ (v (e.symm ⟨τ, i⟩)).left` using `h`. Use `show ((v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F) ≫ _ = _ ≫ (v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F`. Rewrite using `[Category.assoc, ← m.act a, ← Category.assoc, h', Category.assoc]`. Take `⟨s, hsn⟩` from `GlobalTheory.SecTransport.exists_sec_nonzero E H Dw l Xo R x o.t m.toSABMap th hth`.

Establish `hsm : Algebra.Smooth c.F R` using `smooth_of_chart jR hs`. Establish `hreg : IsRegularRing R` using `GlobalTheory.isRegularRing_of_smooth c.F R`. Establish `hq' : q.asIdeal.IsPrime` using `q.isPrime`. Establish `hdom : IsDomain (Localization.AtPrime q.asIdeal)` using `GlobalTheory.isDomain_of_isRegularLocalRing _`. Take `⟨g, hg, hA⟩` from `exists_away_isDomain q.asIdeal`.

Set `A` to `Localization.Away g`. Set `ψ : R →+* A` to `algebraMap R A`. Establish `hψ : ∀ a, ψ (algebraMap c.F R a) = algebraMap c.F A a` using `fun a => (IsScalarTower.algebraMap_apply c.F R A a).symm`. Establish `hopen : IsOpenImmersion (spMap ψ)` using `inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))))`. Establish `hsA : (spMap ψ ≫ jR) ≫ pullback.snd _ _ = spMap (algebraMap c.F A)`.

Rewrite using `[Category.assoc, hs, spMap_spMap]`. Set `x' : Sp A ⟶ Xo.X` to `spMap ψ ≫ x`. Set `u' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber A) ⟶ Xo.univ.t.G.left)` to `fun τ i => spMap (dualMap ψ) ≫ u τ i`. Establish `hbA` using `GlobalTheory.Frames.tanBasis_baseChange E H Dw l Xo R A ψ x _ _ hb`. Establish `htan : ∀ τ i, IsTanAt x' (u' τ i)` using `fun τ i => hbA.1 _`.

Establish `heig' : ∀ τ i, IsEigAt c τ (u' τ i)` using `fun τ i => isEigAt_pull ψ hψ τ (heig τ i)`. Establish `hb' : TanBasis x' (fun j => u' (e j).1 (e j).2)`. Establish `: (fun j => u' (e j).1 (e j).2) = fun i => spMap (dualMap ψ) ≫ (v i).left ≫ m.cm.F`. Use function extensionality and compare the values at `j`. Use `show _ ≫ (v (e.symm (e j))).left ≫ m.cm.F = _`.

Rewrite using `[Equiv.symm_apply_apply]`. Rewrite using `[this]`. Conclude with `hbA`. Establish `hbasis` using `(GlobalTheory.Frames.eigBasis_iff_tanBasis E H Dw l Xo c A x' u' _ e htan heig').2 hb'`. Take `⟨s', hs', -⟩` from `GlobalTheory.Frames.SecPull.existsUnique_secBC E H Dw l Xo R A ψ 1 x x' rfl s`.

Establish `hgen` using `GlobalTheory.FrameGenerator.secGen_of_secNZ_baseChange hS E H Dw l Xo R x s hsn A ψ x' s' rfl hs'`. Establish `hx : x' ≫ Xo.s = sOf c A`. Establish `h1 : x' ≫ Xo.s = ((spMap ψ ≫ jR) ≫ pullback.snd _ _) ≫ spMap (IntermediateField.inclusion c.le).toRingHom`. Simplify using `only [x', x, Category.assoc]`. Rewrite using `[pullback.condition]`.

Rewrite using `[h1, hsA, sOf, spMap_spMap]`. Use `⟨A, inferInstance, hA, inferInstance, spMap ψ ≫ jR, ⟨x', hx, u', htan, heig', hbasis, s', hgen⟩, inferInstance, ?_, hsA, smooth_of_chart _ hsA, (Category.assoc _ _ _).symm⟩` and prove the remaining obligations. Establish `hr : q ∈ Set.range (PrimeSpectrum.comap ψ)`. Rewrite using `[PrimeSpectrum.localization_away_comap_range A g]`. Conclude with `hg`.

Take `⟨q', hq''⟩` from `hr`. Use `⟨q', ?_⟩` and prove the remaining obligations. Conclude with `(Scheme.Hom.comp_apply _ _ _).trans ((congrArg jR hq'').trans hq)`.
-/
theorem exists_integral_chart_frame : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ p : Xo.XF c, ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : Algebra c.F A) (j : Sp A ⟶ Xo.XF c) (y : FrPt Xo c A), IsOpenImmersion j ∧ p ∈ Set.range j ∧ j ≫ pullback.snd _ _ = spMap (algebraMap c.F A) ∧ Algebra.Smooth c.F A ∧ y.x = j ≫ pullback.fst _ _ := by
  intro hT E _ _ _ H Dw l Xo c z
  classical
  have hS := secBaseChange_of_secTwist hT
  let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (Dw.mult τ))).symm
  obtain ⟨R, _, _, jR, o, v, th, hft, hred, hjR, ⟨q, hq⟩, hs, ⟨m⟩, hv, hev, hth, -⟩ :=
    GlobalTheory.ModuliChart.exists_chart_eigenframe hS E H Dw l Xo c _ _ (isTypeFn_fst Dw e) z
  let x : Sp R ⟶ Xo.X := jR ≫ pullback.fst _ _
  have hb : TanBasis x (fun i => (v i).left ≫ m.cm.F) :=
    ((GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo R x o.t.G m.cm.F m.cart).2 _ v).1 hv
  let u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left) :=
    fun τ i => (v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F
  have heig : ∀ τ i, IsEigAt c τ (u τ i) := by
    intro τ i a
    have h := hev (e.symm ⟨τ, i⟩) a
    simp only [Equiv.apply_symm_apply] at h
    have h' : (v (e.symm ⟨τ, i⟩)).left ≫ (o.t.act.act a).left =
      spMap (epsMul (algebraMap c.F R (embK c τ a))) ≫ (v (e.symm ⟨τ, i⟩)).left := h
    show ((v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F) ≫ _ = _ ≫ (v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F
    rw [Category.assoc, ← m.act a, ← Category.assoc, h', Category.assoc]
  obtain ⟨s, hsn⟩ := GlobalTheory.SecTransport.exists_sec_nonzero E H Dw l Xo R x o.t m.toSABMap th hth
  have hsm : Algebra.Smooth c.F R := smooth_of_chart jR hs
  have hreg : IsRegularRing R := GlobalTheory.isRegularRing_of_smooth c.F R
  have hq' : q.asIdeal.IsPrime := q.isPrime
  have hdom : IsDomain (Localization.AtPrime q.asIdeal) := GlobalTheory.isDomain_of_isRegularLocalRing _
  obtain ⟨g, hg, hA⟩ := exists_away_isDomain q.asIdeal
  let A := Localization.Away g
  let ψ : R →+* A := algebraMap R A
  have hψ : ∀ a, ψ (algebraMap c.F R a) = algebraMap c.F A a := fun a =>
    (IsScalarTower.algebraMap_apply c.F R A a).symm
  have hopen : IsOpenImmersion (spMap ψ) := inferInstanceAs
    (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))))
  have hsA : (spMap ψ ≫ jR) ≫ pullback.snd _ _ = spMap (algebraMap c.F A) := by
    rw [Category.assoc, hs, spMap_spMap]
  let x' : Sp A ⟶ Xo.X := spMap ψ ≫ x
  let u' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber A) ⟶ Xo.univ.t.G.left) :=
    fun τ i => spMap (dualMap ψ) ≫ u τ i
  have hbA := GlobalTheory.Frames.tanBasis_baseChange E H Dw l Xo R A ψ x _ _ hb
  have htan : ∀ τ i, IsTanAt x' (u' τ i) := fun τ i => hbA.1 _
  have heig' : ∀ τ i, IsEigAt c τ (u' τ i) := fun τ i => isEigAt_pull ψ hψ τ (heig τ i)
  have hb' : TanBasis x' (fun j => u' (e j).1 (e j).2) := by
    have : (fun j => u' (e j).1 (e j).2) = fun i => spMap (dualMap ψ) ≫ (v i).left ≫ m.cm.F := by
      funext j
      show _ ≫ (v (e.symm (e j))).left ≫ m.cm.F = _
      rw [Equiv.symm_apply_apply]
    rw [this]; exact hbA
  have hbasis := (GlobalTheory.Frames.eigBasis_iff_tanBasis E H Dw l Xo c A x' u' _ e htan heig').2 hb'
  obtain ⟨s', hs', -⟩ := GlobalTheory.Frames.SecPull.existsUnique_secBC E H Dw l Xo R A ψ 1 x x' rfl s
  have hgen := GlobalTheory.FrameGenerator.secGen_of_secNZ_baseChange hS E H Dw l Xo R x s hsn A ψ x' s' rfl hs'
  have hx : x' ≫ Xo.s = sOf c A := by
    have h1 : x' ≫ Xo.s =
        ((spMap ψ ≫ jR) ≫ pullback.snd _ _) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
      simp only [x', x, Category.assoc]
      rw [pullback.condition]
    rw [h1, hsA, sOf, spMap_spMap]
  refine ⟨A, inferInstance, hA, inferInstance, spMap ψ ≫ jR, ⟨x', hx, u', htan, heig', hbasis, s', hgen⟩,
    inferInstance, ?_, hsA, smooth_of_chart _ hsA, (Category.assoc _ _ _).symm⟩
  have hr : q ∈ Set.range (PrimeSpectrum.comap ψ) := by
    rw [PrimeSpectrum.localization_away_comap_range A g]
    exact hg
  obtain ⟨q', hq''⟩ := hr
  refine ⟨q', ?_⟩
  exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg jR hq'').trans hq)

end GlobalTheory.LocalFrame
