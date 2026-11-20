import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonomialFormOnChartRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupDivisorAmpleCriterion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriod
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PelTrivialisationIsUnitOnAbelianLocus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

open GlobalTheory.TraitChartForm in

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c X Z π hπ R _ _ _ ξ tR mR PR hCN hTor W _ _ _ hW _ ϖ hϖ χ t mt P hr be hmon V _ _ _ hV f ψ hfi hfl hψl _ hc hrV`. Establish `hV' : CDvr V` using `hV`. Take `⟨hWd, hWc, hW0⟩` from `hW`. Take `⟨hVd, hVc, hV0⟩` from `hV`. Take `⟨hRN, hRI, hRA, hR0⟩` from `hCN`.

Take `⟨L₁, L₂, L₃, L₄, L₅⟩` from `GlobalTheory.firstFiveLaws`. Take `⟨tV, ⟨mV⟩⟩` from `GlobalTheory.TraitOrder.exists_pull (spMap f) t`. Take `⟨tRV, ⟨mRV⟩⟩` from `GlobalTheory.TraitOrder.exists_pull (spMap ψ) tR`. Take `⟨n₀⟩` from `GlobalTheory.TraitOrder.comp rfl mt mV`. Take `⟨n₂⟩` from `GlobalTheory.TraitOrder.comp rfl mR mRV`.

Establish `j : Function.Injective ((algebraMap V (FractionRing V)).comp f)` using `(IsFractionRing.injective V _).comp hfi`. Set `g : FractionRing W →+* FractionRing V` to `IsFractionRing.lift j`. Establish `eg : jK V ≫ spMap f = spMap g ≫ jK W` using `(GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm`. Take `⟨yW, hyW⟩` from `GlobalTheory.TraitRank.exists_generic_of_range Z W χ hr`. Establish `hZy : jK V ≫ (spMap f ≫ χ) = (spMap g ≫ yW) ≫ Z.j`.

Rewrite using `[Category.assoc, hyW, ← Category.assoc (spMap g), ← eg, Category.assoc]`. Establish `hXy : jK V ≫ (spMap f ≫ χ ≫ π) = (spMap g ≫ yW) ≫ X.j`. Rewrite using `[← hπ, ← Category.assoc (spMap g ≫ yW), ← hZy]`. Simplify using `only [Category.assoc]`. Take `⟨n₁⟩` from `GlobalTheory.ArcOrder.exists_sabMap_of_generic X Z hV' (spMap g ≫ yW) (spMap f ≫ χ ≫ π) (spMap f ≫ χ) hXy hZy n₀`.

Take `⟨k₁⟩` from `GlobalTheory.TraitOrder.cancel (show 𝟙 _ ≫ (spMap f ≫ χ ≫ π) = spMap ψ ≫ ξ by rw [Category.id_comp, hc]) n₁ n₂`. Establish `hpV : PolAt tV (jK V)` using `GlobalTheory.DatUniq.polAt_pull mV (GlobalTheory.DatUniq.polAt_of_unif P) (jK V) (spMap g) eg.symm`. Establish `hpRV : PolAt tRV (jK V)` using `GlobalTheory.DatUniq.polAt_pull k₁ hpV (jK V) (𝟙 _) (by rw [Category.id_comp, Category.comp_id])`. Take `⟨B, -, gen, hg, hw, -⟩` from `GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H V tV hpV`. Take `⟨BR, -, genR, hgR, hwR, -⟩` from `GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H V tRV hpRV`.

Establish `hχgen : χ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W) ∈ abLocus Z.t.G`. Set `p : Sp (FractionRing W)` to `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing W))`. Take `⟨w, hw⟩` from `hr ⟨p, rfl⟩`. Rewrite using `[← jK_apply_eq_bot W p, ← Scheme.Hom.comp_apply, ← hw]`. Conclude with `j_mem_abLocus Z w`.

Establish `hfbot : spMap f (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W)`. Rewrite using `[← ker_eq_spMap_bot]`. Conclude with `PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot f).1 hfi)`. Establish `hlocW : ∀ a ∈ maximalIdeal W, f a ∈ maximalIdeal V` using `fun a ha => (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit f a h)`. Set `Ww : Set (Sp W)` to `abLocus t.G ∩ {p | ϖ ∉ p.asIdeal}`.

Establish `hWo : IsOpen Ww` using `(GlobalTheory.AbLocusOpen.isOpen_abLocus_local t.G t.semi).inter (PrimeSpectrum.isOpen_basicOpen (a := ϖ))`. Establish `hkerW : (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum W) ∈ Ww`. Rewrite using `[ker_eq_spMap_bot, hfbot]`. Use `⟨(abLocus_pullback abLocusOne Z.t.semi mt.cart.1 _).1 hχgen, fun h => hϖ.ne_zero ((Submodule.mem_bot W).1 h)⟩` and prove the remaining obligations. Establish `hψW : ∀ y, PsiUnitOn P.D.toPre y Ww` using `fun y => hmon.psiUnitOn y fun p hp => by simpa using hp.2`.

Take `⟨PV, e₁, he₁⟩` from `GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H W V f t tV mV P Ww inferInstance inferInstance hWc inferInstance inferInstance hVc hlocW hWo Set.inter_subset_left hψW hkerW ⟨B, gen, hg, hw⟩`. Establish `hlocR : ∀ a ∈ maximalIdeal R, ψ a ∈ maximalIdeal V` using `fun a ha => (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit ψ a h)`. Establish `hRo : IsOpen (abLocus tR.G)` using `GlobalTheory.AbLocusOpen.isOpen_abLocus_local tR.G tR.semi`. Establish `hAdm : admitted R (maximalIdeal R)` using `⟨⟨hRN, inferInstance, hRI, hRA⟩, hRA, hR0, inferInstance, by letI := Ideal.Quotient.field (maximalIdeal R); infer_instance⟩`. Establish `hψR : ∀ y, PsiUnitOn PR.D.toPre y (abLocus tR.G)` using `GlobalTheory.psiUnitOn_abLocus_pel L₁ L₂ L₃ L₄ L₅ E H R (maximalIdeal R) hAdm tR PR hTor hRo`.

Establish `hkerR : (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) ∈ abLocus tR.G`. Rewrite using `[ker_eq_spMap_bot]`. Use `(abLocus_pullback abLocusOne X.t.semi mR.cart.1 _).1 ?_` and prove the remaining obligations. Set `p : Sp (FractionRing V)` to `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))`. Take `⟨w, hw⟩` from `hrV ⟨p, rfl⟩`.

Establish `key : ξ (spMap ψ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)) = (jK V ≫ spMap ψ ≫ ξ) p`. Rewrite using `[Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, jK_apply_eq_bot V p]`. Rewrite using `[key, ← hw]`. Conclude with `j_mem_abLocus X w`. Take `⟨PRV, e₂, he₂⟩` from `GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H R V ψ tR tRV mRV PR (abLocus tR.G) hRN hRI hRA inferInstance inferInstance hVc hlocR hRo subset_rfl hψR hkerR ⟨BR, genR, hgR, hwR⟩`.

Take `⟨e₃, he₃⟩` from `GlobalTheory.SameCoord.exists_equiv_psiCoord E H V tV tRV k₁ PV PRV inferInstance inferInstance hVc`. Use `⟨(e₂.trans e₃.symm).trans e₁.symm, fun y => ?_⟩` and prove the remaining obligations. Take `⟨r, hr⟩` from `(GlobalTheory.PeriodFormCompare.exists_psiCoord_iff PR.D.toPre y).2 (GlobalTheory.PeriodFormCompare.psiIn_top PR.D y)`. Use `set x := ((e₂.trans e₃.symm).trans e₁.symm) y with hx`. Establish `hx2 : e₃ (e₁ x) = e₂ y` using `by simp [hx]`.

Take `⟨u₀, nW, hnW, hcW⟩` from `hmon x`. Take `⟨u₁, h₁⟩` from `he₁ x _ hcW`. Take `⟨u₃, h₃⟩` from `he₃ _ _ h₁`. Take `⟨u₂, h₂⟩` from `he₂ y r hr`. Rewrite `h₃` using `[hx2]`.

Take `⟨w, hw⟩` from `GlobalTheory.PsiCoordLocal.exists_unit_of_coord h₃ h₂`. Establish `key : ψ r = ((u₂⁻¹ * w * u₃ * u₁ * Units.map f.toMonoidHom u₀ : Vˣ) : V) * f ϖ ^ nW 0`. Establish `e` using `congrArg (fun z => ((u₂⁻¹ : Vˣ) : V) * z) hw`. Simplify using `only [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow] at e`. Rewrite `e` using `[← mul_assoc, Units.inv_mul, one_mul]`.

Rewrite using `[e]`. Simplify using `only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨r, nW 0, hr, by simpa using hnW 0, ?_⟩` and prove the remaining obligations. Conclude with `Associated.symm (⟨_, by rw [key, mul_comm]⟩ : Associated (f ϖ ^ nW 0) (ψ r))`.
-/
theorem GlobalTheory.TraitBlowForm.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Z.j ≫ π = X.j → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X.X) (tR : SAB H (Sp R)) (_ : SABMap tR X.t ξ) (PR : PELUnif (maximalIdeal R) tR), IsCN R → PR.TorsionIso → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ¬ (∀ p : ℕ, p.Prime → IsUnit (p : W)) → ∀ ϖ : W, Irreducible ϖ → ∀ (χ : Sp W ⟶ Z.X) (t : SAB H (Sp W)) (_ : SABMap t Z.t χ) (P : PELUnif (maximalIdeal W) t), Set.range (jK W ≫ χ) ⊆ Set.range Z.j → ∀ be : LinearMap.BilinForm ℤ P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (f : W →+* V) (ψ : R →+* V), Function.Injective f → IsLocalHom f → IsLocalHom ψ → Irreducible (f ϖ) → spMap f ≫ χ ≫ π = spMap ψ ≫ ξ → Set.range (jK V ≫ spMap ψ ≫ ξ) ⊆ Set.range X.j → ∃ ε : PR.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X, ∀ y, ∃ (r : R) (n : ℕ), PsiCoord PR.D.toPre y r ∧ be (ε y) (ε y) = 2 * n ∧ Associated (ψ r) (f ϖ ^ n) := by
  intro E _ _ _ H D l Xo c X Z π hπ R _ _ _ ξ tR mR PR hCN hTor W _ _ _ hW _ ϖ hϖ χ t mt P hr be hmon V _ _ _ hV f ψ
    hfi hfl hψl _ hc hrV
  have hV' : CDvr V := hV
  obtain ⟨hWd, hWc, hW0⟩ := hW
  obtain ⟨hVd, hVc, hV0⟩ := hV
  obtain ⟨hRN, hRI, hRA, hR0⟩ := hCN
  obtain ⟨L₁, L₂, L₃, L₄, L₅⟩ := GlobalTheory.firstFiveLaws

  obtain ⟨tV, ⟨mV⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap f) t
  obtain ⟨tRV, ⟨mRV⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap ψ) tR
  obtain ⟨n₀⟩ := GlobalTheory.TraitOrder.comp rfl mt mV
  obtain ⟨n₂⟩ := GlobalTheory.TraitOrder.comp rfl mR mRV
  have j : Function.Injective ((algebraMap V (FractionRing V)).comp f) := (IsFractionRing.injective V _).comp hfi
  let g : FractionRing W →+* FractionRing V := IsFractionRing.lift j
  have eg : jK V ≫ spMap f = spMap g ≫ jK W :=
    (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm
  obtain ⟨yW, hyW⟩ := GlobalTheory.TraitRank.exists_generic_of_range Z W χ hr
  have hZy : jK V ≫ (spMap f ≫ χ) = (spMap g ≫ yW) ≫ Z.j := by
    rw [Category.assoc, hyW, ← Category.assoc (spMap g), ← eg, Category.assoc]
  have hXy : jK V ≫ (spMap f ≫ χ ≫ π) = (spMap g ≫ yW) ≫ X.j := by
    rw [← hπ, ← Category.assoc (spMap g ≫ yW), ← hZy]
    simp only [Category.assoc]
  obtain ⟨n₁⟩ := GlobalTheory.ArcOrder.exists_sabMap_of_generic X Z hV' (spMap g ≫ yW) (spMap f ≫ χ ≫ π) (spMap f ≫ χ)
    hXy hZy n₀
  obtain ⟨k₁⟩ := GlobalTheory.TraitOrder.cancel (show 𝟙 _ ≫ (spMap f ≫ χ ≫ π) = spMap ψ ≫ ξ by rw [Category.id_comp, hc])
    n₁ n₂

  have hpV : PolAt tV (jK V) := GlobalTheory.DatUniq.polAt_pull mV (GlobalTheory.DatUniq.polAt_of_unif P) (jK V) (spMap g) eg.symm
  have hpRV : PolAt tRV (jK V) :=
    GlobalTheory.DatUniq.polAt_pull k₁ hpV (jK V) (𝟙 _) (by rw [Category.id_comp, Category.comp_id])
  obtain ⟨B, -, gen, hg, hw, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H V tV hpV
  obtain ⟨BR, -, genR, hgR, hwR, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H V tRV hpRV

  have hχgen : χ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W) ∈ abLocus Z.t.G := by
    let p : Sp (FractionRing W) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing W))
    obtain ⟨w, hw⟩ := hr ⟨p, rfl⟩
    rw [← jK_apply_eq_bot W p, ← Scheme.Hom.comp_apply, ← hw]
    exact j_mem_abLocus Z w
  have hfbot : spMap f (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W) := by
    rw [← ker_eq_spMap_bot]
    exact PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot f).1 hfi)

  have hlocW : ∀ a ∈ maximalIdeal W, f a ∈ maximalIdeal V := fun a ha =>
    (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit f a h)
  let Ww : Set (Sp W) := abLocus t.G ∩ {p | ϖ ∉ p.asIdeal}
  have hWo : IsOpen Ww :=
    (GlobalTheory.AbLocusOpen.isOpen_abLocus_local t.G t.semi).inter (PrimeSpectrum.isOpen_basicOpen (a := ϖ))
  have hkerW : (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum W) ∈ Ww := by
    rw [ker_eq_spMap_bot, hfbot]
    refine ⟨(abLocus_pullback abLocusOne Z.t.semi mt.cart.1 _).1 hχgen, fun h => hϖ.ne_zero ((Submodule.mem_bot W).1 h)⟩
  have hψW : ∀ y, PsiUnitOn P.D.toPre y Ww := fun y => hmon.psiUnitOn y fun p hp => by simpa using hp.2
  obtain ⟨PV, e₁, he₁⟩ := GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H W V f t tV mV P Ww inferInstance inferInstance
    hWc inferInstance inferInstance hVc hlocW hWo Set.inter_subset_left hψW hkerW ⟨B, gen, hg, hw⟩

  have hlocR : ∀ a ∈ maximalIdeal R, ψ a ∈ maximalIdeal V := fun a ha =>
    (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit ψ a h)
  have hRo : IsOpen (abLocus tR.G) := GlobalTheory.AbLocusOpen.isOpen_abLocus_local tR.G tR.semi
  have hAdm : admitted R (maximalIdeal R) := ⟨⟨hRN, inferInstance, hRI, hRA⟩, hRA, hR0, inferInstance,
    by letI := Ideal.Quotient.field (maximalIdeal R); infer_instance⟩
  have hψR : ∀ y, PsiUnitOn PR.D.toPre y (abLocus tR.G) :=
    GlobalTheory.psiUnitOn_abLocus_pel L₁ L₂ L₃ L₄ L₅ E H R (maximalIdeal R) hAdm tR PR hTor hRo
  have hkerR : (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) ∈ abLocus tR.G := by
    rw [ker_eq_spMap_bot]
    refine (abLocus_pullback abLocusOne X.t.semi mR.cart.1 _).1 ?_
    let p : Sp (FractionRing V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
    obtain ⟨w, hw⟩ := hrV ⟨p, rfl⟩
    have key : ξ (spMap ψ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)) = (jK V ≫ spMap ψ ≫ ξ) p := by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, jK_apply_eq_bot V p]
    rw [key, ← hw]
    exact j_mem_abLocus X w
  obtain ⟨PRV, e₂, he₂⟩ := GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H R V ψ tR tRV mRV PR (abLocus tR.G) hRN hRI
    hRA inferInstance inferInstance hVc hlocR hRo subset_rfl hψR hkerR ⟨BR, genR, hgR, hwR⟩

  obtain ⟨e₃, he₃⟩ := GlobalTheory.SameCoord.exists_equiv_psiCoord E H V tV tRV k₁ PV PRV inferInstance inferInstance hVc
  refine ⟨(e₂.trans e₃.symm).trans e₁.symm, fun y => ?_⟩
  obtain ⟨r, hr⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff PR.D.toPre y).2
    (GlobalTheory.PeriodFormCompare.psiIn_top PR.D y)
  set x := ((e₂.trans e₃.symm).trans e₁.symm) y with hx
  have hx2 : e₃ (e₁ x) = e₂ y := by simp [hx]
  obtain ⟨u₀, nW, hnW, hcW⟩ := hmon x
  obtain ⟨u₁, h₁⟩ := he₁ x _ hcW
  obtain ⟨u₃, h₃⟩ := he₃ _ _ h₁
  obtain ⟨u₂, h₂⟩ := he₂ y r hr
  rw [hx2] at h₃
  obtain ⟨w, hw⟩ := GlobalTheory.PsiCoordLocal.exists_unit_of_coord h₃ h₂
  have key : ψ r = ((u₂⁻¹ * w * u₃ * u₁ * Units.map f.toMonoidHom u₀ : Vˣ) : V) * f ϖ ^ nW 0 := by
    have e := congrArg (fun z => ((u₂⁻¹ : Vˣ) : V) * z) hw
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow] at e
    rw [← mul_assoc, Units.inv_mul, one_mul] at e
    rw [e]
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    ring
  refine ⟨r, nW 0, hr, by simpa using hnW 0, ?_⟩
  exact Associated.symm (⟨_, by rw [key, mul_comm]⟩ : Associated (f ϖ ^ nW 0) (ψ r))
