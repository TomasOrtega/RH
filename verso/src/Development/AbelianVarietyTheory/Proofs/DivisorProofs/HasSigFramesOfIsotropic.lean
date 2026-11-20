import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIndexRelOfHasSigFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearPatPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubTransfer
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDvrExtensionForMonicFamily

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.CM GlobalTheory.PointMap GlobalTheory.FlatCM GlobalTheory.PointSig GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMKernel

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type}
  [CommRing O] [Algebra O C] [hO : Fact ¬IsUnit (ℓ : O)] [IsAdicComplete (Ideal.span {(ℓ : O)}) O] [Algebra ℤ_[ℓ] O]
  [Algebra ℤ_[ℓ] C] [IsScalarTower ℤ_[ℓ] O C] {Λ : Type} [CommRing Λ] [StarRing Λ]

omit [IsAlgClosed C] in

/- English proof (translation)
Use `haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)`. Use `haveI : ValuationRing O := ValuationRing.of_integers v hv`. Use `haveI : CharZero O := (algebraMap O C).charZero`. Set `f : ℤ_[ℓ] ⊗[ℤ] R →ₐ[ℤ_[ℓ]] O` to `Algebra.TensorProduct.lift (Algebra.ofId _ _) j.toIntAlgHom fun _ _ => .all _ _`. Use `haveI : Module.Finite ℤ_[ℓ] f.range := Module.Finite.of_surjective f.rangeRestrict.toLinearMap f.rangeRestrict_surjective`.

Use `haveI : IsLocalRing f.range := GlobalTheory.isLocalRing_of_domain_finite_padicInt ℓ _`. Use `haveI : IsAdicComplete (maximalIdeal ℤ_[ℓ]) ℤ_[ℓ] := inferInstance`. Use `⟨f.range, inferInstance, inferInstance, inferInstance, IsNoetherianRing.of_finite ℤ_[ℓ] _, inferInstance, CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[ℓ] _, f.rangeRestrict.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom, f.range.val.toRingHom, RingHom.ex …` and prove the remaining obligations. Establish `h1 : (((maximalIdeal O).comap f.range.val.toRingHom).comap (algebraMap ℤ_[ℓ] f.range)).IsMaximal`. Use `Ideal.IsPrime.isMaximal inferInstance fun h => ?_` and prove the remaining obligations.

Establish `: (ℓ : ℤ_[ℓ]) ∈ ((maximalIdeal O).comap f.range.val.toRingHom).comap (algebraMap ℤ_[ℓ] f.range)`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, map_natCast, map_natCast]`. Conclude with `hO.out`. Rewrite `this` using `[h, Ideal.mem_bot, Nat.cast_eq_zero]`. Conclude with `(Fact.out : ℓ.Prime).ne_zero this`.

Establish `h2` using `eq_maximalIdeal (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ h1)`. Conclude with `⟨fun a ha => by_contra fun hn => (h2.ge hn) ha⟩`.
-/
theorem exists_factor (ℓ : ℕ) [Fact ℓ.Prime] [hO : Fact ¬IsUnit (ℓ : O)] [Algebra ℤ_[ℓ] O] (hv : v.Integers O) {R : Type} [CommRing R] [Module.Finite ℤ R] (j : R →+* O) :
    ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T) (_ : IsLocalRing T) (_ : IsNoetherianRing T) (_ : CharZero T)
      (_ : IsAdicComplete (maximalIdeal T) T) (φ : R →+* T) (g : T →+* O), g.comp φ = j ∧ IsLocalHom g := by
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : CharZero O := (algebraMap O C).charZero
  let f : ℤ_[ℓ] ⊗[ℤ] R →ₐ[ℤ_[ℓ]] O := Algebra.TensorProduct.lift (Algebra.ofId _ _) j.toIntAlgHom fun _ _ => .all _ _
  haveI : Module.Finite ℤ_[ℓ] f.range := Module.Finite.of_surjective f.rangeRestrict.toLinearMap f.rangeRestrict_surjective
  haveI : IsLocalRing f.range := GlobalTheory.isLocalRing_of_domain_finite_padicInt ℓ _
  haveI : IsAdicComplete (maximalIdeal ℤ_[ℓ]) ℤ_[ℓ] := inferInstance
  refine ⟨f.range, inferInstance, inferInstance, inferInstance, IsNoetherianRing.of_finite ℤ_[ℓ] _, inferInstance,
    CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[ℓ] _,
    f.rangeRestrict.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom, f.range.val.toRingHom,
    RingHom.ext fun a => by simp [f], ?_⟩
  have h1 : (((maximalIdeal O).comap f.range.val.toRingHom).comap (algebraMap ℤ_[ℓ] f.range)).IsMaximal := by
    refine Ideal.IsPrime.isMaximal inferInstance fun h => ?_
    have : (ℓ : ℤ_[ℓ]) ∈ ((maximalIdeal O).comap f.range.val.toRingHom).comap (algebraMap ℤ_[ℓ] f.range) := by
      rw [Ideal.mem_comap, Ideal.mem_comap, map_natCast, map_natCast]
      exact hO.out
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at this
    exact (Fact.out : ℓ.Prime).ne_zero this
  have h2 := eq_maximalIdeal (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ h1)
  exact ⟨fun a ha => by_contra fun hn => (h2.ge hn) ha⟩

omit [Algebra ℤ_[ℓ] C] [IsScalarTower ℤ_[ℓ] O C] in

/- English proof (translation)
Take `⟨T, _, _, _, _, _, _, φ, g, hg, hloc⟩` from `exists_factor ℓ hv j`. Establish `hL` using `GlobalTheory.firstFiveLaws.1`. Set `B'` to `StrictPull.polPull B (spMap φ)`. Take `⟨A, eA, hA, w, hw⟩` from `GoodReductionUnif.exists_baseChange hL.polBaseChange (Out.jK T) B'`. Take `⟨D, -, -, ⟨U⟩⟩` from `exists_unif_abelianScheme hL.globalFns hL.secBaseChange hL.cube T (maximalIdeal T) B' A eA hA ⟨w, hw⟩`.

Use `letI := g.toAlgebra`. Establish `e : spMap g ≫ spMap φ = spMap j` using `by rw [spMap_spMap, hg]`. Establish `hπ : IsGrpPullback (goodPoint hv ε j B o).G B.A (spMap j) (pullback.fst _ _)` using `isGrpPullback_pullback B.A _`. Establish `hc : IsGrpPullback B'.A B.A (spMap φ) (pullback.fst _ _)` using `isGrpPullback_pullback B.A _`. Establish `w' : pullback.fst B.A.hom (spMap j) ≫ B.A.hom = ((goodPoint hv ε j B o).G.hom ≫ spMap g) ≫ spMap φ`.

Rewrite using `[Category.assoc, e]`. Conclude with `hπ.1.w`. Establish `hπ' : IsGrpPullback (goodPoint hv ε j B o).G B'.A (spMap g) (hc.1.lift _ _ w')` using `hc.cancel (hπ.congr e.symm (hc.1.lift_fst _ _ _).symm) (hc.1.lift_snd _ _ _)`. Use `haveI := B'.isAb.comm`. Use `haveI := B'.smoothDim`.

Use `haveI : Smooth B'.A.hom := SmoothOfRelativeDimension.smooth B'.g _`. Take `⟨d, x, hx⟩` from `Chart.univChartLoc B'.A`. Take `⟨F, hF⟩` from `(JetSer.lawSt_of JetSer.jetAlg (JetSer.repSt_of_jetAlgSt JetSer.jetAlg) _ B'.A d x hx).1`. Take `⟨x', hx'⟩` from `ChartCharacter.exists_isChartJ B'.A x hx F hF`. Take `⟨N, u, hu, hspan⟩` from `ChF.hodgeTate_inclusion_chart ℓ T (fun h => hO.out (by simpa using h.map g)) B'.A D A U.toUnifPre d F x' hx' C v O hv g hloc`.

Introduce `a ha`. Conclude with `FormalChar.smul_mem_htSpan (goodPoint hv ε j B o) hπ' hx F hF hu (hspan a (by rwa [map_natCast]))`.
-/
theorem htChar_goodPoint (hv : v.Integers O) (ε : Eps ℓ C) {R : Type} [CommRing R] [Module.Finite ℤ R] (j : R →+* O)
    (B : Out.PolAV (Sp R)) (o : B.OAct Λ) : HTChar ℓ v (goodPoint hv ε j B o).Gt := by
  obtain ⟨T, _, _, _, _, _, _, φ, g, hg, hloc⟩ := exists_factor ℓ hv j
  have hL := GlobalTheory.firstFiveLaws.1
  let B' := StrictPull.polPull B (spMap φ)
  obtain ⟨A, eA, hA, w, hw⟩ := GoodReductionUnif.exists_baseChange hL.polBaseChange (Out.jK T) B'
  obtain ⟨D, -, -, ⟨U⟩⟩ := exists_unif_abelianScheme hL.globalFns hL.secBaseChange hL.cube T (maximalIdeal T) B' A eA hA
    ⟨w, hw⟩
  letI := g.toAlgebra
  have e : spMap g ≫ spMap φ = spMap j := by rw [spMap_spMap, hg]
  have hπ : IsGrpPullback (goodPoint hv ε j B o).G B.A (spMap j) (pullback.fst _ _) := isGrpPullback_pullback B.A _
  have hc : IsGrpPullback B'.A B.A (spMap φ) (pullback.fst _ _) := isGrpPullback_pullback B.A _
  have w' : pullback.fst B.A.hom (spMap j) ≫ B.A.hom = ((goodPoint hv ε j B o).G.hom ≫ spMap g) ≫ spMap φ := by
    rw [Category.assoc, e]
    exact hπ.1.w
  have hπ' : IsGrpPullback (goodPoint hv ε j B o).G B'.A (spMap g) (hc.1.lift _ _ w') :=
    hc.cancel (hπ.congr e.symm (hc.1.lift_fst _ _ _).symm) (hc.1.lift_snd _ _ _)
  haveI := B'.isAb.comm
  haveI := B'.smoothDim
  haveI : Smooth B'.A.hom := SmoothOfRelativeDimension.smooth B'.g _
  obtain ⟨d, x, hx⟩ := Chart.univChartLoc B'.A
  obtain ⟨F, hF⟩ := (JetSer.lawSt_of JetSer.jetAlg (JetSer.repSt_of_jetAlgSt JetSer.jetAlg) _ B'.A d x hx).1
  obtain ⟨x', hx'⟩ := ChartCharacter.exists_isChartJ B'.A x hx F hF
  obtain ⟨N, u, hu, hspan⟩ := ChF.hodgeTate_inclusion_chart ℓ T (fun h => hO.out (by simpa using h.map g)) B'.A
    D A U.toUnifPre d F x' hx' C v O hv g hloc
  intro a ha
  exact FormalChar.smul_mem_htSpan (goodPoint hv ε j B o) hπ' hx F hF hu (hspan a (by rwa [map_natCast]))

variable (P : Point ℓ v O Λ)

/- English proof (translation)
Introduce `f` and use `by have h1 : v (algebraMap O C (ℓ : O)) ^ (ℓ - 1) ≤ v (ℓ : C) := by have hle := P.integers.map_le_one (ℓ : O) rw [map_natCast] at hle ⊢ exact pow_le_of_le_one zero_le hle (by have := (Fact.out : ℓ.Prime).two_le; omega) have h2 := h (ℓ : O) h1 f.1 f.2 rw [← (weilChar_surjective_an …`.
-/
theorem cokernelBound_of_htChar (h : HTChar ℓ v P.Gt) : CokernelBound P := fun f => by
  have h1 : v (algebraMap O C (ℓ : O)) ^ (ℓ - 1) ≤ v (ℓ : C) := by
    have hle := P.integers.map_le_one (ℓ : O)
    rw [map_natCast] at hle ⊢
    exact pow_le_of_le_one zero_le hle (by have := (Fact.out : ℓ.Prime).two_le; omega)
  have h2 := h (ℓ : O) h1 f.1 f.2
  rw [← (weilChar_surjective_and_map_range_al ℓ C v O Λ P).2] at h2
  obtain ⟨t, ht, e⟩ := h2
  rw [sq, mul_smul, ← show t = (ℓ : O) • f from Subtype.ext e]
  exact Submodule.smul_mem _ _ ht

/- English proof (translation)
Establish `h1` using `(GlobalTheory.T.hodge_tate_kernel_annihilator ℓ C v O Λ P).2`. Establish `h2` using `GlobalTheory.T.finrank_W_eq_dimension ℓ C v O Λ P hcok`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_span (hcok : CokernelBound P) : Module.finrank C (Submodule.span C (Set.range P.bLie)) = P.A.g := by
  have h1 := (GlobalTheory.T.hodge_tate_kernel_annihilator ℓ C v O Λ P).2
  have h2 := GlobalTheory.T.finrank_W_eq_dimension ℓ C v O Λ P hcok
  omega

/- English proof (translation)
Use `(Submodule.eq_of_le_of_finrank_eq (fun y hy => ?_) ((finrank_span P hcok).trans (GlobalTheory.T.finrank_W_eq_dimension ℓ C v O Λ P hcok).symm)).symm` and prove the remaining obligations. Conclude with `(KerPerp.mem_W_iff ℓ C v O Λ P y).2 fun x => h _ (Submodule.subset_span ⟨x, rfl⟩) y hy`.
-/
theorem W_eq_of_isotropic (hcok : CokernelBound P) (h : ∀ x ∈ Submodule.span C (Set.range P.bLie),
    ∀ y ∈ Submodule.span C (Set.range P.bLie), P.pairV x y = 0) : P.W = Submodule.span C (Set.range P.bLie) := by
  refine (Submodule.eq_of_le_of_finrank_eq (fun y hy => ?_)
    ((finrank_span P hcok).trans (GlobalTheory.T.finrank_W_eq_dimension ℓ C v O Λ P hcok).symm)).symm
  exact (KerPerp.mem_W_iff ℓ C v O Λ P y).2 fun x => h _ (Submodule.subset_span ⟨x, rfl⟩) y hy

/- English proof (translation)
The claim follows from `(Submodule.span_le (p := (Submodule.span C (Set.range P.bLie)).comap (P.actV a))).2 (by rintro _ ⟨y, rfl⟩; exact Submodule.subset_span ⟨_, P.bLie_act a y⟩) hx`.
-/
theorem actV_mem (a : Λ) {x : P.V} (hx : x ∈ Submodule.span C (Set.range P.bLie)) :
    P.actV a x ∈ Submodule.span C (Set.range P.bLie) :=
  (Submodule.span_le (p := (Submodule.span C (Set.range P.bLie)).comap (P.actV a))).2
    (by rintro _ ⟨y, rfl⟩; exact Submodule.subset_span ⟨_, P.bLie_act a y⟩) hx

/- English proof (translation)
Use `haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)`. Use `haveI : IsFractionRing O C := P.integers.isFractionRing`. Establish `hinj` using `bLie_injective P hcok`. Establish `key : ∀ k, AvDefs.rTau P.Gt P.oGt (σ k) = 0 → ∀ x ∈ Submodule.span C (Set.range P.bLie), proj hs P.actV k x = 0` using `fun k hk x hx => by`. Establish `h1 : ∀ t : C ⊗[ℤ] Λ, tensorAction P.actV t x ∈ Submodule.span C (Set.range P.bLie)` using `fun t => by`.

Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add s t hs ht => rw [map_add, LinearMap.add_apply]`. Conclude with `add_mem hs ht`. Consider the case `tmul c a => rw [tensorAction_tmul]`.

Conclude with `Submodule.smul_mem _ _ (actV_mem P a hx)`. Establish `h2 : proj hs P.actV k x ∈ P.eigV (σ k)` using `proj_mem hs P.actV k x`. Take `⟨s, hs0, z, hz⟩` from `HodgeTateEigenRank.exists_smul_mem_of_mem_span (C := C) P.latLie (show proj hs P.actV k x ∈ _ from h1 _)`. Establish `hs' : algebraMap O C s ≠ 0` using `fun h => hs0 (P.integers.hom_inj (by rw [h, map_zero]))`. Establish `h3 : P.bLie z ∈ P.eigV (σ k)`.

Rewrite using `[hz, ← algebraMap_smul C s]`. Conclude with `Submodule.smul_mem _ _ h2`. Establish `h4 : AvDefs.IsEig P.Gt P.oGt (σ k) z` using `fun a => hinj (by`. Rewrite using `[P.bLie_act, P.bLie_scale, mem_eigenSub.1 h3 a, RingHom.comp_apply, algebraMap_smul])`. Take `⟨e, -, -, he⟩` from `exists_basis_wRec P hinj (σ k) hk`.

Establish `h5 : P.bLie z ∈ P.wRec (σ k)` using `⟨⟨z, h4⟩, rfl⟩`. Rewrite `h5` using `[← he, Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot, hz, ← algebraMap_smul C s]`. Conclude with `(smul_eq_zero.1 h5).resolve_left hs'`. Introduce `x hx y hy`. Rewrite using `[← sum_proj hs P.actV x, ← sum_proj hs P.actV y]`.

Simplify using `only [map_sum, LinearMap.sum_apply]`. Use `Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : AvDefs.rTau P.Gt P.oGt (σ k) = 0`. Rewrite using `[key k hk x hx, map_zero, LinearMap.zero_apply]`. Distinguish the cases in `hl : AvDefs.rTau P.Gt P.oGt (σ l) = 0`.

Rewrite using `[key l hl y hy, map_zero]`. Conclude with `Model.pairV_eq_zero P (proj_mem hs P.actV k x) (proj_mem hs P.actV l y) a (h k l hk hl)`.
-/
theorem isotropic_of_types (hcok : CokernelBound P) {J : Type} [Fintype J] [DecidableEq J] {σ : J → Λ →+* O}
    (hs : IsSplitting (embC C σ)) (a : Λ) (h : ∀ k l, AvDefs.rTau P.Gt P.oGt (σ k) ≠ 0 → AvDefs.rTau P.Gt P.oGt (σ l) ≠ 0 →
      algebraMap O C (σ k a) ≠ algebraMap O C (σ l (star a))) :
    ∀ x ∈ Submodule.span C (Set.range P.bLie), ∀ y ∈ Submodule.span C (Set.range P.bLie), P.pairV x y = 0 := by
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  haveI : IsFractionRing O C := P.integers.isFractionRing
  have hinj := bLie_injective P hcok
  have key : ∀ k, AvDefs.rTau P.Gt P.oGt (σ k) = 0 → ∀ x ∈ Submodule.span C (Set.range P.bLie),
      proj hs P.actV k x = 0 := fun k hk x hx => by
    have h1 : ∀ t : C ⊗[ℤ] Λ, tensorAction P.actV t x ∈ Submodule.span C (Set.range P.bLie) := fun t => by
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add s t hs ht => rw [map_add, LinearMap.add_apply]; exact add_mem hs ht
      | tmul c a => rw [tensorAction_tmul]; exact Submodule.smul_mem _ _ (actV_mem P a hx)
    have h2 : proj hs P.actV k x ∈ P.eigV (σ k) := proj_mem hs P.actV k x
    obtain ⟨s, hs0, z, hz⟩ := HodgeTateEigenRank.exists_smul_mem_of_mem_span (C := C) P.latLie
      (show proj hs P.actV k x ∈ _ from h1 _)
    have hs' : algebraMap O C s ≠ 0 := fun h => hs0 (P.integers.hom_inj (by rw [h, map_zero]))
    have h3 : P.bLie z ∈ P.eigV (σ k) := by
      rw [hz, ← algebraMap_smul C s]
      exact Submodule.smul_mem _ _ h2
    have h4 : AvDefs.IsEig P.Gt P.oGt (σ k) z := fun a => hinj (by
      rw [P.bLie_act, P.bLie_scale, mem_eigenSub.1 h3 a, RingHom.comp_apply, algebraMap_smul])
    obtain ⟨e, -, -, he⟩ := exists_basis_wRec P hinj (σ k) hk
    have h5 : P.bLie z ∈ P.wRec (σ k) := ⟨⟨z, h4⟩, rfl⟩
    rw [← he, Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot, hz, ← algebraMap_smul C s] at h5
    exact (smul_eq_zero.1 h5).resolve_left hs'
  intro x hx y hy
  rw [← sum_proj hs P.actV x, ← sum_proj hs P.actV y]
  simp only [map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : AvDefs.rTau P.Gt P.oGt (σ k) = 0
  · rw [key k hk x hx, map_zero, LinearMap.zero_apply]
  by_cases hl : AvDefs.rTau P.Gt P.oGt (σ l) = 0
  · rw [key l hl y hy, map_zero]
  exact Model.pairV_eq_zero P (proj_mem hs P.actV k x) (proj_mem hs P.actV l y) a (h k l hk hl)

/- English proof (translation)
Set `S` to `Submodule.span C (Set.range A.bLie)`. Set `S'` to `Submodule.span C (Set.range A'.bLie)`. Set `F : ((Fin p → S) × (Fin q → S')) →ₗ[C] B.V` to `(∑ k, φ k ∘ₗ S.subtype ∘ₗ LinearMap.proj k).coprod (∑ k, φ' k ∘ₗ S'.subtype ∘ₗ LinearMap.proj k)`. Establish `hF : ∀ z, F z = ∑ k, φ k (z.1 k) + ∑ k, φ' k (z.2 k)` using `fun z => by simp [F]`. Establish `hFi : Function.Injective F` using `fun z z' e => by`.

Use `@hinj (fun k => z.1 k, fun k => z.2 k) (fun k => z'.1 k, fun k => z'.2 k) ((hF z).symm.trans (e.trans (hF z')))` as an intermediate fact. Conclude with `Prod.ext (funext fun k => Subtype.ext (congrFun (congrArg Prod.fst this) k)) (funext fun k => Subtype.ext (congrFun (congrArg Prod.snd this) k))`. Establish `hr : LinearMap.range F = Submodule.span C (Set.range B.bLie)`. Use `Submodule.eq_of_le_of_finrank_eq ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨z, rfl⟩`.

Rewrite using `[hF]`. Use `add_mem (Submodule.sum_mem _ fun k _ => ?_) (Submodule.sum_mem _ fun k _ => ?_)` and prove the remaining obligations. Conclude with `(Submodule.span_le (p := (Submodule.span C (Set.range B.bLie)).comap (φ k))).2 (by rintro _ ⟨y, rfl⟩; exact Submodule.subset_span (hφ k y)) (z.1 k).2`. Conclude with `(Submodule.span_le (p := (Submodule.span C (Set.range B.bLie)).comap (φ' k))).2 (by rintro _ ⟨y, rfl⟩; exact Submodule.subset_span (hφ' k y)) (z.2 k).2`. Rewrite using `[LinearMap.finrank_range_of_inj hFi, finrank_span B hB, hg, Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_pi_fintype, finrank_span A hA, finrank_span A' hA']`.

Simplify using the standard rewrite rules. Rewrite using `[← hr]`. Introduce and unpack `_ ⟨z, rfl⟩ _ ⟨w, rfl⟩`. Establish `h₄ : ∀ a b x y, B.pairV (φ' a x) (φ b y) = 0` using `fun a b x y => by rw [B.pairV_swap, h₃, neg_zero]`. Establish `h₅ : ∀ a b, A.pairV (A.actV (g a b) (z.1 a)) (w.1 b) = 0` using `fun a b => iA _ (actV_mem A _ (z.1 a).2) _ (w.1 b).2`.

Establish `h₆ : ∀ a b, A'.pairV (A'.actV (g' a b) (z.2 a)) (w.2 b) = 0` using `fun a b => iA' _ (actV_mem A' _ (z.2 a).2) _ (w.2 b).2`. Simplify using `only [hF, map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply, h₁, h₂, h₃, h₄, h₅, h₆, Finset.sum_const_zero, add_zero]`.
-/
theorem isotropic_of_sum {A A' B : Point ℓ v O Λ} {p q : ℕ} (φ : Fin p → (A.V →ₗ[C] B.V)) (φ' : Fin q → (A'.V →ₗ[C] B.V))
    (hA : CokernelBound A) (hA' : CokernelBound A') (hB : CokernelBound B) (hg : B.A.g = p * A.A.g + q * A'.A.g)
    (hφ : ∀ a x, ∃ z, B.bLie z = φ a (A.bLie x)) (hφ' : ∀ a x, ∃ z, B.bLie z = φ' a (A'.bLie x))
    (hinj : Function.Injective fun z : (Fin p → A.V) × (Fin q → A'.V) => ∑ k, φ k (z.1 k) + ∑ k, φ' k (z.2 k))
    {g : Matrix (Fin p) (Fin p) Λ} {g' : Matrix (Fin q) (Fin q) Λ}
    (h₁ : ∀ a b x y, B.pairV (φ a x) (φ b y) = A.pairV (A.actV (g a b) x) y)
    (h₂ : ∀ a b x y, B.pairV (φ' a x) (φ' b y) = A'.pairV (A'.actV (g' a b) x) y)
    (h₃ : ∀ a b x y, B.pairV (φ a x) (φ' b y) = 0)
    (iA : ∀ x ∈ Submodule.span C (Set.range A.bLie), ∀ y ∈ Submodule.span C (Set.range A.bLie), A.pairV x y = 0)
    (iA' : ∀ x ∈ Submodule.span C (Set.range A'.bLie), ∀ y ∈ Submodule.span C (Set.range A'.bLie), A'.pairV x y = 0) :
    ∀ x ∈ Submodule.span C (Set.range B.bLie), ∀ y ∈ Submodule.span C (Set.range B.bLie), B.pairV x y = 0 := by
  let S := Submodule.span C (Set.range A.bLie)
  let S' := Submodule.span C (Set.range A'.bLie)
  let F : ((Fin p → S) × (Fin q → S')) →ₗ[C] B.V :=
    (∑ k, φ k ∘ₗ S.subtype ∘ₗ LinearMap.proj k).coprod (∑ k, φ' k ∘ₗ S'.subtype ∘ₗ LinearMap.proj k)
  have hF : ∀ z, F z = ∑ k, φ k (z.1 k) + ∑ k, φ' k (z.2 k) := fun z => by simp [F]
  have hFi : Function.Injective F := fun z z' e => by
    have := @hinj (fun k => z.1 k, fun k => z.2 k) (fun k => z'.1 k, fun k => z'.2 k) ((hF z).symm.trans (e.trans (hF z')))
    exact Prod.ext (funext fun k => Subtype.ext (congrFun (congrArg Prod.fst this) k))
      (funext fun k => Subtype.ext (congrFun (congrArg Prod.snd this) k))
  have hr : LinearMap.range F = Submodule.span C (Set.range B.bLie) := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨z, rfl⟩
      rw [hF]
      refine add_mem (Submodule.sum_mem _ fun k _ => ?_) (Submodule.sum_mem _ fun k _ => ?_)
      · exact (Submodule.span_le (p := (Submodule.span C (Set.range B.bLie)).comap (φ k))).2
          (by rintro _ ⟨y, rfl⟩; exact Submodule.subset_span (hφ k y)) (z.1 k).2
      · exact (Submodule.span_le (p := (Submodule.span C (Set.range B.bLie)).comap (φ' k))).2
          (by rintro _ ⟨y, rfl⟩; exact Submodule.subset_span (hφ' k y)) (z.2 k).2
    · rw [LinearMap.finrank_range_of_inj hFi, finrank_span B hB, hg, Module.finrank_prod, Module.finrank_pi_fintype,
        Module.finrank_pi_fintype, finrank_span A hA, finrank_span A' hA']
      simp
  rw [← hr]
  rintro _ ⟨z, rfl⟩ _ ⟨w, rfl⟩
  have h₄ : ∀ a b x y, B.pairV (φ' a x) (φ b y) = 0 := fun a b x y => by rw [B.pairV_swap, h₃, neg_zero]
  have h₅ : ∀ a b, A.pairV (A.actV (g a b) (z.1 a)) (w.1 b) = 0 := fun a b => iA _ (actV_mem A _ (z.1 a).2) _ (w.1 b).2
  have h₆ : ∀ a b, A'.pairV (A'.actV (g' a b) (z.2 a)) (w.2 b) = 0 := fun a b =>
    iA' _ (actV_mem A' _ (z.2 a).2) _ (w.2 b).2
  simp only [hF, map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply, h₁, h₂, h₃, h₄, h₅, h₆,
    Finset.sum_const_zero, add_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C)

/- English proof (translation)
The claim follows from `letI := H.starRing cokernelBound_of_htChar _ (htChar_goodPoint hv ε _ _ _)`.
-/
theorem cokernelBound_patPoint (T : PAT H (Sp (𝓞 K))) : letI := H.starRing; CokernelBound (patPoint hv ε i T) :=
  letI := H.starRing
  cokernelBound_of_htChar _ (htChar_goodPoint hv ε _ _ _)

open Classical in

/- English proof (translation)
Use `letI := H.starRing`. Use `isotropic_of_types _ (cokernelBound_patPoint hv ε i T) (σ := fun φ : E →+* C => embO hv φ) (isSplitting_embO hv) H.rt fun k l hk hl e => ?_` and prove the remaining obligations. Rewrite `hk`, `hl` using `[rTau_patPoint hv ε i T hT]`. Rewrite `e` using `[show star H.rt = -H.rt from EigDec.bar_rt H, map_neg, map_neg]`. Establish `sq : ∀ k : E →+* C, algebraMap O C (embO hv k H.rt) ^ 2 = i (ρ : K) ^ 2` using `fun k => by`.

Rewrite using `[← map_pow, ← map_pow, H.rt_sq, RingOfIntegers.coe_eq_algebraMap, ← map_pow, ← map_pow, hρ]`. Simplify using the standard rewrite rules. Establish `ne : i (ρ : K) ≠ 0` using `fun h => by`. Rewrite `h` using `[map_eq_zero, RingOfIntegers.coe_eq_algebraMap, map_eq_zero_iff _ RingOfIntegers.coe_injective]`. Conclude with `H.d_prime.ne_zero (by simpa [h] using hρ)`.

Break down `h0 with rfl | rfl` into its components or cases. Establish `h1` using `(sq_eq_sq_iff_eq_or_eq_neg.1 (sq k)).resolve_left fun h => hk (if_pos h)`. Establish `h2` using `(sq_eq_sq_iff_eq_or_eq_neg.1 (sq l)).resolve_left fun h => hl (if_pos h)`. Rewrite `e` using `[h1, h2, neg_neg]`. Conclude with `ne (neg_eq_self.1 e)`.

Establish `h1` using `by_contra fun h => hk (if_neg h)`. Establish `h2` using `by_contra fun h => hl (if_neg h)`. Rewrite `e` using `[h1, h2]`. Conclude with `ne (neg_eq_self.1 e.symm)`.
-/
theorem isotropic_pure (T : PAT H (Sp (𝓞 K))) {ρ : 𝓞 K} (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) {m n : ℕ} (hT : HasType H T.t.act ρ m n)
    (h0 : m = 0 ∨ n = 0) : letI := H.starRing
    ∀ x ∈ Submodule.span C (Set.range (patPoint hv ε i T).bLie),
      ∀ y ∈ Submodule.span C (Set.range (patPoint hv ε i T).bLie), (patPoint hv ε i T).pairV x y = 0 := by
  letI := H.starRing
  refine isotropic_of_types _ (cokernelBound_patPoint hv ε i T) (σ := fun φ : E →+* C => embO hv φ) (isSplitting_embO hv)
    H.rt fun k l hk hl e => ?_
  rw [rTau_patPoint hv ε i T hT] at hk hl
  rw [show star H.rt = -H.rt from EigDec.bar_rt H, map_neg, map_neg] at e
  have sq : ∀ k : E →+* C, algebraMap O C (embO hv k H.rt) ^ 2 = i (ρ : K) ^ 2 := fun k => by
    rw [← map_pow, ← map_pow, H.rt_sq, RingOfIntegers.coe_eq_algebraMap, ← map_pow, ← map_pow, hρ]
    simp
  have ne : i (ρ : K) ≠ 0 := fun h => by
    rw [map_eq_zero, RingOfIntegers.coe_eq_algebraMap, map_eq_zero_iff _ RingOfIntegers.coe_injective] at h
    exact H.d_prime.ne_zero (by simpa [h] using hρ)
  rcases h0 with rfl | rfl
  · have h1 := (sq_eq_sq_iff_eq_or_eq_neg.1 (sq k)).resolve_left fun h => hk (if_pos h)
    have h2 := (sq_eq_sq_iff_eq_or_eq_neg.1 (sq l)).resolve_left fun h => hl (if_pos h)
    rw [h1, h2, neg_neg] at e
    exact ne (neg_eq_self.1 e)
  · have h1 := by_contra fun h => hk (if_neg h)
    have h2 := by_contra fun h => hl (if_neg h)
    rw [h1, h2] at e
    exact ne (neg_eq_self.1 e.symm)

/- English proof (translation)
Use `letI := H.starRing`. Introduce `h`. Use `hasSigFrames_of_rTau _ (cokernelBound_patPoint hv ε i T) (W_eq_of_isotropic _ (cokernelBound_patPoint hv ε i T) h) H.rt τ (fun h0 => conj_rt_ne H ?_) fun χ => ?_` and prove the remaining obligations. Rewrite using `[← H.bar_eq]`. Conclude with `τ.injective h0`.

Rewrite using `[hτ]`. Conclude with `rTau_patPoint hv ε i T hT χ`.
-/
theorem hasSigFrames_of_isotropic (T : PAT H (Sp (𝓞 K))) {ρ : 𝓞 K} {m n : ℕ} (hT : HasType H T.t.act ρ m n)
    (τ : E →+* C) (hτ : τ (H.rt : E) = i (ρ : K)) : letI := H.starRing
    (∀ x ∈ Submodule.span C (Set.range (patPoint hv ε i T).bLie),
      ∀ y ∈ Submodule.span C (Set.range (patPoint hv ε i T).bLie), (patPoint hv ε i T).pairV x y = 0) →
    HasSigFrames (patPoint hv ε i T) H.rt τ m n := by
  letI := H.starRing
  intro h
  refine hasSigFrames_of_rTau _ (cokernelBound_patPoint hv ε i T)
    (W_eq_of_isotropic _ (cokernelBound_patPoint hv ε i T) h) H.rt τ (fun h0 => conj_rt_ne H ?_) fun χ => ?_
  · rw [← H.bar_eq]
    exact τ.injective h0
  · rw [hτ]
    exact rTau_patPoint hv ε i T hT χ

/- English proof (translation)
Use `letI := H.starRing`. Establish `iP` using `isotropic_pure hv ε i _ X.ρ_sq X.typeP (.inr rfl)`. Establish `iQ` using `isotropic_pure hv ε i _ X.ρ_sq X.typeM (.inl rfl)`. Take `⟨g₁, g₂, g₃⟩` from `GramAt.gram_V hv ε i X h`. Take `⟨d₁, d₂, -⟩` from `GramAt.dims X`.

Use `⟨hasSigFrames_of_isotropic hv ε i _ X.typeB τ hτ ?_, hasSigFrames_of_isotropic hv ε i _ X.typeP τ hτ iP, hasSigFrames_of_isotropic hv ε i _ X.typeM τ hτ iQ⟩` and prove the remaining obligations. Use `isotropic_of_sum (A := pointA hv ε i X true) (A' := pointA hv ε i X false) (B := pointB hv ε i X) (phiVP hv ε i X) (phiVQ hv ε i X) (cokernelBound_patPoint hv ε i _) (cokernelBound_patPoint hv ε i _) (cokernelBound_patPoint hv ε i _) ?_ (fun a x => ⟨_, (patV_bLie (T := X.A true) …` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `X.B.g = p * (X.A true).g + q * (X.A false).g`. Rewrite using `[d₂, d₁, d₁]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasSigFrames_of_isGram {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ₁ p q)
    {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ) (τ : E →+* C)
    (hτ : τ (H.rt : E) = i (ρ : K)) : letI := H.starRing
    HasSigFrames (pointB hv ε i X) H.rt τ p q ∧ HasSigFrames (pointA hv ε i X true) H.rt τ 1 0 ∧
      HasSigFrames (pointA hv ε i X false) H.rt τ 0 1 := by
  letI := H.starRing
  have iP := isotropic_pure hv ε i _ X.ρ_sq X.typeP (.inr rfl)
  have iQ := isotropic_pure hv ε i _ X.ρ_sq X.typeM (.inl rfl)
  obtain ⟨g₁, g₂, g₃⟩ := GramAt.gram_V hv ε i X h
  obtain ⟨d₁, d₂, -⟩ := GramAt.dims X
  refine ⟨hasSigFrames_of_isotropic hv ε i _ X.typeB τ hτ ?_, hasSigFrames_of_isotropic hv ε i _ X.typeP τ hτ iP,
    hasSigFrames_of_isotropic hv ε i _ X.typeM τ hτ iQ⟩
  refine isotropic_of_sum (A := pointA hv ε i X true) (A' := pointA hv ε i X false) (B := pointB hv ε i X)
    (phiVP hv ε i X) (phiVQ hv ε i X) (cokernelBound_patPoint hv ε i _) (cokernelBound_patPoint hv ε i _)
    (cokernelBound_patPoint hv ε i _) ?_ (fun a x => ⟨_, (patV_bLie (T := X.A true) hv ε i (X.lin (.inl a)) x).symm⟩)
    (fun a x => ⟨_, (patV_bLie (T := X.A false) hv ε i (X.lin (.inr a)) x).symm⟩)
    (GramAt.sumV_bijective hv ε i X).1 g₁ g₂ g₃ iP iQ
  change X.B.g = p * (X.A true).g + q * (X.A false).g
  rw [d₂, d₁, d₁]
  ring

end GlobalTheory.CMKernel
