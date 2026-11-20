import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology

noncomputable section

namespace GlobalTheory.HolHomOnto

open GlobalTheory.TangentOrigin GlobalTheory.HolHom

/- English proof (translation)
Take `⟨U₀, -, U, hU, hp, hle, hsm⟩` from `Smooth.exists_isStandardSmooth s (x (default : PrimeSpectrum ℂ))`. Establish `hU₀ : U₀ = ⊤`. Use `eq_top_iff.2 fun y _ => ?_` and prove the remaining obligations. Establish `h1 : s (x (default : PrimeSpectrum ℂ)) ∈ U₀` using `hle hp`. Establish `h2 : y = s (x (default : PrimeSpectrum ℂ))` using `Subsingleton.elim (α := PrimeSpectrum ℂ) _ _`.

Rewrite using `[h2]`. Conclude with `h1`. Substitute `hU₀` using the available equality. Choose the witnesses or unpack the hypotheses as in `⟨n, hn⟩ : ∃ n, RingHom.IsStandardSmoothOfRelativeDimension n (s.appLE ⊤ U hle).hom := by`. Set `_` to `(s.appLE ⊤ U hle).hom.toAlgebra`.

Establish `: Algebra.IsStandardSmooth Γ(Sp ℂ, ⊤) Γ(Y, U)` using `hsm`. Take `⟨_, _, _, _, ⟨P⟩⟩` from `this`. Conclude with `⟨P.dimension, _, _, _, ‹_›, P, rfl⟩`. Set `c : ℂ →+* Γ(Y, U)` to `(s.appLE ⊤ U hle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom`. Establish `hcc : ∀ a, constFn s U a = c a` using `fun a => rfl`.

Establish `hc : c.IsStandardSmoothOfRelativeDimension n` using `RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 (s.appLE ⊤ U hle).hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv hn`. Establish `hconst : ∀ {R : Type} [CommRing R] (ψ : ℂ →+* R) (y : Sp R ⟶ Y) (hy : ⊤ ≤ y ⁻¹ᵁ U), y ≫ s = spMap ψ → ∀ a, evalPt y U hy (c a) = ψ a`. Introduce `R _ ψ y hy hys a`. Rewrite using `[← hcc, evalPt_constFn]`. Conclude with `(congrArg (fun y : Sp R ⟶ Sp ℂ => evalPt y ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) hys).trans (evalPt_spMap _ a)`.

Establish `hxU : ⊤ ≤ x ⁻¹ᵁ U` using `(le_preimage_iff x U).2 hp`. Establish `hxc : ∀ a, evalPt x U hxU (c a) = a` using `hconst (RingHom.id ℂ) x hxU (hx.trans (Spec.map_id _).symm)`. Take `⟨φ, hφc, hφ, hφ0⟩` from `HolChart.exists_etale_coords_vanishing c hc (evalPt x U hxU) hxc`. Establish `hφc' : ∀ a, φ (MvPolynomial.C a) = c a` using `fun a => by rw [← hφc]; rfl`. Set `_ : Algebra ℂ Γ(Y, U)` to `c.toAlgebra`.

Set `_ : Algebra (MvPolynomial (Fin n) ℂ) Γ(Y, U)` to `φ.toAlgebra`. Establish `_ : IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(Y, U)` using `IsScalarTower.of_algebraMap_eq' hφc.symm`. Establish `_ : Algebra.Etale (MvPolynomial (Fin n) ℂ) Γ(Y, U)` using `hφ`. Set `eA : Γ(Y, U) →ₐ[ℂ] ℂ` to `{ evalPt x U hxU with commutes' := hxc }`. Take `⟨W, σ, m, f, ε, hW, hW0, -, -, -, hσt, -⟩` from `exists_holomorphic_section_of_etale n Γ(Y, U) eA hφ0`.

Use `⟨n, U, fun i => φ (MvPolynomial.X i), W, hxU, hW, hW0, fun w hw => ?_, fun v v' hv hv' h0 h0' ht => ?_⟩` and prove the remaining obligations. Take `⟨p, hpU, hpσ⟩` from `exists_evalPt_eq hU (σ w).toRingHom`. Use `⟨p, ?_, hpU, fun i => ?_⟩` and prove the remaining obligations. Use `(eq_spMap_of_evalPt _ (RingHom.id ℂ) fun a => ?_).trans (Spec.map_id _)` and prove the remaining obligations. Rewrite using `[← evalPt_constFn s p U hpU, hpσ, hcc]`.

Conclude with `(σ w).commutes a`. Rewrite using `[valAt'_eq_evalPt _ _ hpU, hpσ]`. Conclude with `hσt w hw i`. Establish `hvU` using `(le_preimage_dual_iff h0 U).2 hxU`. Establish `hvU'` using `(le_preimage_dual_iff h0' U).2 hxU`.

Establish `e1 : ∀ f, valR v U f = evalPt v U hvU f` using `valR_eq _ _ hvU`. Establish `e2 : ∀ f, valR v' U f = evalPt v' U hvU' f` using `valR_eq _ _ hvU'`. Establish `f1 : ∀ f, (evalPt v U hvU f).fst = evalPt x U hxU f` using `fun f => by`. Rewrite using `[← e1, fst_valR h0 hxU, valAt'_eq_evalPt]`. Establish `f2 : ∀ f, (evalPt v' U hvU' f).fst = evalPt x U hxU f` using `fun f => by`.

Rewrite using `[← e2, fst_valR h0' hxU, valAt'_eq_evalPt]`. Set `D : Γ(Y, U) →+ ℂ` to `{ toFun := fun f => (evalPt v U hvU f).snd - (evalPt v' U hvU' f).snd map_zero' := by simp map_add' := fun f f' => by`. Simplify using `only [map_add, TrivSqZeroExt.snd_add]`. Use `ring }`. Establish `hD : ∀ f, D f = (evalPt v U hvU f).snd - (evalPt v' U hvU' f).snd` using `fun _ => rfl`.

Establish `hz : D = 0`. Use `HolChart.derivation_eq_zero φ hφ (evalPt x U hxU) D (fun a => ?_) (fun f f' => ?_) fun i => ?_` and prove the remaining obligations. Rewrite using `[hD, hφc', hconst _ v hvU hv, hconst _ v' hvU' hv', sub_self]`. Rewrite using `[hD, hD, hD, map_mul, map_mul, DualNumber.snd_mul, DualNumber.snd_mul, f1, f1, f2, f2]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hD, ← e1, ← e2, ht, sub_self]`. Use `ext_evalPt hU hvU hvU' (RingHom.ext fun f => TrivSqZeroExt.ext ((f1 f).trans (f2 f).symm) ?_)` and prove the remaining obligations. Use `hD f` as an intermediate fact. Rewrite `this` using `[hz]`. Conclude with `sub_eq_zero.1 this.symm`.
-/
theorem exists_coords {Y : Scheme.{0}} (s : Y ⟶ Sp ℂ) [Smooth s] (x : Sp ℂ ⟶ Y) (hx : x ≫ s = 𝟙 _) :
    ∃ (n : ℕ) (U : Y.Opens) (t : Fin n → Γ(Y, U)) (W : Set (Fin n → ℂ)),
      ⊤ ≤ x ⁻¹ᵁ U ∧ IsOpen W ∧ 0 ∈ W ∧
      (∀ w ∈ W, ∃ p : Sp ℂ ⟶ Y, p ≫ s = 𝟙 _ ∧ ⊤ ≤ p ⁻¹ᵁ U ∧ ∀ i, valAt' p U (t i) = w i) ∧
      ∀ v v' : Sp (DualNumber ℂ) ⟶ Y, v ≫ s = spMap (algebraMap ℂ (DualNumber ℂ)) →
        v' ≫ s = spMap (algebraMap ℂ (DualNumber ℂ)) → spMap fstC ≫ v = x → spMap fstC ≫ v' = x →
        (∀ i, (valR v U (t i)).snd = (valR v' U (t i)).snd) → v = v' := by
  obtain ⟨U₀, -, U, hU, hp, hle, hsm⟩ := Smooth.exists_isStandardSmooth s (x (default : PrimeSpectrum ℂ))
  have hU₀ : U₀ = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : s (x (default : PrimeSpectrum ℂ)) ∈ U₀ := hle hp
    have h2 : y = s (x (default : PrimeSpectrum ℂ)) :=
      Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [h2]; exact h1
  subst hU₀
  obtain ⟨n, hn⟩ : ∃ n, RingHom.IsStandardSmoothOfRelativeDimension n (s.appLE ⊤ U hle).hom := by
    let _ := (s.appLE ⊤ U hle).hom.toAlgebra
    have : Algebra.IsStandardSmooth Γ(Sp ℂ, ⊤) Γ(Y, U) := hsm
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := this
    exact ⟨P.dimension, _, _, _, ‹_›, P, rfl⟩
  let c : ℂ →+* Γ(Y, U) :=
    (s.appLE ⊤ U hle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have hcc : ∀ a, constFn s U a = c a := fun a => rfl
  have hc : c.IsStandardSmoothOfRelativeDimension n :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 (s.appLE ⊤ U hle).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv hn
  have hconst : ∀ {R : Type} [CommRing R] (ψ : ℂ →+* R) (y : Sp R ⟶ Y) (hy : ⊤ ≤ y ⁻¹ᵁ U), y ≫ s = spMap ψ →
      ∀ a, evalPt y U hy (c a) = ψ a := by
    intro R _ ψ y hy hys a
    rw [← hcc, evalPt_constFn]
    exact (congrArg (fun y : Sp R ⟶ Sp ℂ => evalPt y ⊤ le_rfl
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) hys).trans (evalPt_spMap _ a)
  have hxU : ⊤ ≤ x ⁻¹ᵁ U := (le_preimage_iff x U).2 hp
  have hxc : ∀ a, evalPt x U hxU (c a) = a := hconst (RingHom.id ℂ) x hxU (hx.trans (Spec.map_id _).symm)
  obtain ⟨φ, hφc, hφ, hφ0⟩ := HolChart.exists_etale_coords_vanishing c hc (evalPt x U hxU) hxc
  have hφc' : ∀ a, φ (MvPolynomial.C a) = c a := fun a => by rw [← hφc]; rfl
  let _ : Algebra ℂ Γ(Y, U) := c.toAlgebra
  let _ : Algebra (MvPolynomial (Fin n) ℂ) Γ(Y, U) := φ.toAlgebra
  have _ : IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(Y, U) :=
    IsScalarTower.of_algebraMap_eq' hφc.symm
  have _ : Algebra.Etale (MvPolynomial (Fin n) ℂ) Γ(Y, U) := hφ
  let eA : Γ(Y, U) →ₐ[ℂ] ℂ := { evalPt x U hxU with commutes' := hxc }
  obtain ⟨W, σ, m, f, ε, hW, hW0, -, -, -, hσt, -⟩ :=
    exists_holomorphic_section_of_etale n Γ(Y, U) eA hφ0
  refine ⟨n, U, fun i => φ (MvPolynomial.X i), W, hxU, hW, hW0, fun w hw => ?_, fun v v' hv hv' h0 h0' ht => ?_⟩
  · obtain ⟨p, hpU, hpσ⟩ := exists_evalPt_eq hU (σ w).toRingHom
    refine ⟨p, ?_, hpU, fun i => ?_⟩
    · refine (eq_spMap_of_evalPt _ (RingHom.id ℂ) fun a => ?_).trans (Spec.map_id _)
      rw [← evalPt_constFn s p U hpU, hpσ, hcc]
      exact (σ w).commutes a
    · rw [valAt'_eq_evalPt _ _ hpU, hpσ]
      exact hσt w hw i
  · have hvU := (le_preimage_dual_iff h0 U).2 hxU
    have hvU' := (le_preimage_dual_iff h0' U).2 hxU
    have e1 : ∀ f, valR v U f = evalPt v U hvU f := valR_eq _ _ hvU
    have e2 : ∀ f, valR v' U f = evalPt v' U hvU' f := valR_eq _ _ hvU'
    have f1 : ∀ f, (evalPt v U hvU f).fst = evalPt x U hxU f := fun f => by
      rw [← e1, fst_valR h0 hxU, valAt'_eq_evalPt]
    have f2 : ∀ f, (evalPt v' U hvU' f).fst = evalPt x U hxU f := fun f => by
      rw [← e2, fst_valR h0' hxU, valAt'_eq_evalPt]
    let D : Γ(Y, U) →+ ℂ :=
      { toFun := fun f => (evalPt v U hvU f).snd - (evalPt v' U hvU' f).snd
        map_zero' := by simp
        map_add' := fun f f' => by
          simp only [map_add, TrivSqZeroExt.snd_add]
          ring }
    have hD : ∀ f, D f = (evalPt v U hvU f).snd - (evalPt v' U hvU' f).snd := fun _ => rfl
    have hz : D = 0 := by
      refine HolChart.derivation_eq_zero φ hφ (evalPt x U hxU) D (fun a => ?_) (fun f f' => ?_) fun i => ?_
      · rw [hD, hφc', hconst _ v hvU hv, hconst _ v' hvU' hv', sub_self]
      · rw [hD, hD, hD, map_mul, map_mul, DualNumber.snd_mul, DualNumber.snd_mul, f1, f1, f2, f2]
        ring
      · rw [hD, ← e1, ← e2, ht, sub_self]
    refine ext_evalPt hU hvU hvU' (RingHom.ext fun f => TrivSqZeroExt.ext ((f1 f).trans (f2 f).symm) ?_)
    have := hD f
    rw [hz] at this
    exact sub_eq_zero.1 this.symm

/- English proof (translation)
Introduce `G _ y hy hs g e he hsurj hol v hv hv0`. Substitute `hy` using the available equality. Take `⟨n, U, t, W, h0, hW, hW0, hp, hext⟩` from `exists_coords G.hom (e 0).left (Over.w (e 0))`. Establish `hA` using `holAt_of_isHolTo hol (Set.mem_univ 0)`. Set `L : (Fin g → ℂ) →ₗ[ℂ] (Fin n → ℂ)` to `LinearMap.pi fun i => (fderiv ℂ (fun z => valAt' (e z).left U (t i)) 0).toLinearMap`.

Establish `hover : ∀ {w u}, IsDerivAt (fun z => (show Sp ℂ ⟶ G.left from (e z).left)) 0 w u → u ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ))` using `fun hu => (IsDerivAt.over (a := e) hu).trans (Category.comp_id _)`. Establish `key : ∀ (w : Fin g → ℂ) (u : Sp (DualNumber ℂ) ⟶ G.left), u ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) → spMap fstC ≫ u = (e 0).left → (L w = fun i => (valR u U (t i)).snd) → IsDerivAt (fun z => (show Sp ℂ ⟶ G.left from (e z).left)) 0 w u`. Introduce `w u hu hu0 hL`. Take `⟨u', hu'⟩` from `hA.exists_isDerivAt w`. Establish `: u = u'` using `hext u u' hu (hover hu') hu0 hu'.1 fun i => (congrFun hL i).symm.trans (hu'.2 U h0 (t i)).symm`.

Conclude with `this ▸ hu'`. It suffices to establish `hL : Function.Surjective L by`. Take `⟨w, hw⟩` from `hL fun i => (valR v U (t i)).snd`. Conclude with `⟨w, key w v hv hv0 hw⟩`. Take `⟨ρ, hρ⟩` from `L.rangeRestrict.exists_rightInverse_of_surjective L.range_rangeRestrict`.

Set `P : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)` to `LinearMap.toContinuousLinearMap (ρ ∘ₗ L.rangeRestrict)`. Establish `hLP : ∀ z, L (P z) = L z` using `fun z => congrArg Subtype.val (DFunLike.congr_fun hρ (L.rangeRestrict z))`. Establish `hfac : e = fun z => e (P z)`. Use `eq_of_fderiv_eq he (fun z w => by rw [map_add, he]) hol (isHolTo_of_holAt isOpen_univ fun z _ => (holAt_of_isHolTo hol (Set.mem_univ (P z))).precomp P.differentiableAt) fun V hV f => ?_` and prove the remaining obligations. Use `ext1 z`.

Establish `h1 : HasFDerivAt (fun z => valAt' (e z).left V f) (fderiv ℂ (fun z => valAt' (e z).left V f) 0) (P 0)`. Rewrite using `[map_zero]`. Conclude with `((hA V hV).2 f).hasFDerivAt`. Use `Eq.trans ?_ (congrArg (· z) (h1.comp 0 P.hasFDerivAt).fderiv).symm` and prove the remaining obligations. Take `⟨u, hu⟩` from `hA.exists_isDerivAt z`.

Establish `hu'` using `key (P z) u (hover hu) hu.1 ((hLP z).trans (funext fun i => (hu.2 U h0 (t i)).symm))`. Conclude with `(hu.2 V hV f).symm.trans (hu'.2 V hV f)`. Establish `hol' : IsHolTo Set.univ (fun r : LinearMap.range L => (show Sp ℂ ⟶ G.left from (e (ρ r)).left))` using `isHolTo_of_holAt isOpen_univ fun r _ => (holAt_of_isHolTo hol (Set.mem_univ (ρ r))).precomp (LinearMap.toContinuousLinearMap ρ).differentiableAt`. Rewrite using `[← LinearMap.range_eq_top]`. Assume the negation of the conclusion as `hne`.

Establish `hlt : Module.finrank ℂ (LinearMap.range L) < n`. Simplify using `using Submodule.finrank_lt hne`. Establish `hnull` using `AffinePoints.volume_image_eq_zero_of_finrank_lt hlt (f := fun r i => valAt' (e (ρ r)).left U (t i)) (differentiableOn_pi.2 fun i => (hol' U (t i)).2)`. Use `(hW.measure_pos MeasureTheory.volume ⟨0, hW0⟩).ne' (MeasureTheory.measure_mono_null (fun w hw => ?_) hnull)` and prove the remaining obligations. Take `⟨p, hps, hpU, hpt⟩` from `hp w hw`.

Take `⟨z, hz⟩` from `hsurj (Over.homMk p hps)`. Establish `hz' : (e (ρ (L.rangeRestrict z))).left = p` using `congrArg (·.left) ((congrFun hfac z).symm.trans hz)`. Use `⟨L.rangeRestrict z, ⟨trivial, ?_⟩, funext fun i => ?_⟩` and prove the remaining obligations. Substitute `hz'` using the available equality. Conclude with `hpU`.

Substitute `hz'` using the available equality. Conclude with `hpt i`.
-/
theorem exists_isDerivAt_of_surjective : ∀ (G : Over (Sp ℂ)) [GrpObj G] (y : Sp ℂ ⟶ Sp ℂ), y = 𝟙 _ → Smooth G.hom → ∀ (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), (∀ z w, e (z + w) = e z * e w) → Function.Surjective e → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G.left from (e z).left)) → ∀ v : Sp (DualNumber ℂ) ⟶ G.left, v ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = (e 0).left → ∃ w, GlobalTheory.HolHom.IsDerivAt (fun z => (show Sp ℂ ⟶ G.left from (e z).left)) 0 w v := by
  intro G _ y hy hs g e he hsurj hol v hv hv0
  subst hy
  obtain ⟨n, U, t, W, h0, hW, hW0, hp, hext⟩ := exists_coords G.hom (e 0).left (Over.w (e 0))
  have hA := holAt_of_isHolTo hol (Set.mem_univ 0)
  let L : (Fin g → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    LinearMap.pi fun i => (fderiv ℂ (fun z => valAt' (e z).left U (t i)) 0).toLinearMap
  have hover : ∀ {w u}, IsDerivAt (fun z => (show Sp ℂ ⟶ G.left from (e z).left)) 0 w u →
      u ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := fun hu =>
    (IsDerivAt.over (a := e) hu).trans (Category.comp_id _)
  have key : ∀ (w : Fin g → ℂ) (u : Sp (DualNumber ℂ) ⟶ G.left), u ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) →
      spMap fstC ≫ u = (e 0).left → (L w = fun i => (valR u U (t i)).snd) →
      IsDerivAt (fun z => (show Sp ℂ ⟶ G.left from (e z).left)) 0 w u := by
    intro w u hu hu0 hL
    obtain ⟨u', hu'⟩ := hA.exists_isDerivAt w
    have : u = u' := hext u u' hu (hover hu') hu0 hu'.1 fun i =>
      (congrFun hL i).symm.trans (hu'.2 U h0 (t i)).symm
    exact this ▸ hu'
  suffices hL : Function.Surjective L by
    obtain ⟨w, hw⟩ := hL fun i => (valR v U (t i)).snd
    exact ⟨w, key w v hv hv0 hw⟩
  obtain ⟨ρ, hρ⟩ := L.rangeRestrict.exists_rightInverse_of_surjective L.range_rangeRestrict
  let P : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap (ρ ∘ₗ L.rangeRestrict)
  have hLP : ∀ z, L (P z) = L z := fun z =>
    congrArg Subtype.val (DFunLike.congr_fun hρ (L.rangeRestrict z))
  have hfac : e = fun z => e (P z) := by
    refine eq_of_fderiv_eq he (fun z w => by rw [map_add, he]) hol
      (isHolTo_of_holAt isOpen_univ fun z _ =>
        (holAt_of_isHolTo hol (Set.mem_univ (P z))).precomp P.differentiableAt) fun V hV f => ?_
    ext1 z
    have h1 : HasFDerivAt (fun z => valAt' (e z).left V f) (fderiv ℂ (fun z => valAt' (e z).left V f) 0) (P 0) := by
      rw [map_zero]; exact ((hA V hV).2 f).hasFDerivAt
    refine Eq.trans ?_ (congrArg (· z) (h1.comp 0 P.hasFDerivAt).fderiv).symm
    obtain ⟨u, hu⟩ := hA.exists_isDerivAt z
    have hu' := key (P z) u (hover hu) hu.1 ((hLP z).trans (funext fun i => (hu.2 U h0 (t i)).symm))
    exact (hu.2 V hV f).symm.trans (hu'.2 V hV f)
  have hol' : IsHolTo Set.univ (fun r : LinearMap.range L => (show Sp ℂ ⟶ G.left from (e (ρ r)).left)) :=
    isHolTo_of_holAt isOpen_univ fun r _ =>
      (holAt_of_isHolTo hol (Set.mem_univ (ρ r))).precomp (LinearMap.toContinuousLinearMap ρ).differentiableAt
  rw [← LinearMap.range_eq_top]
  by_contra hne
  have hlt : Module.finrank ℂ (LinearMap.range L) < n := by
    simpa using Submodule.finrank_lt hne
  have hnull := AffinePoints.volume_image_eq_zero_of_finrank_lt hlt
    (f := fun r i => valAt' (e (ρ r)).left U (t i)) (differentiableOn_pi.2 fun i => (hol' U (t i)).2)
  refine (hW.measure_pos MeasureTheory.volume ⟨0, hW0⟩).ne' (MeasureTheory.measure_mono_null (fun w hw => ?_) hnull)
  obtain ⟨p, hps, hpU, hpt⟩ := hp w hw
  obtain ⟨z, hz⟩ := hsurj (Over.homMk p hps)
  have hz' : (e (ρ (L.rangeRestrict z))).left = p :=
    congrArg (·.left) ((congrFun hfac z).symm.trans hz)
  refine ⟨L.rangeRestrict z, ⟨trivial, ?_⟩, funext fun i => ?_⟩
  · subst hz'
    exact hpU
  · subst hz'
    exact hpt i

end GlobalTheory.HolHomOnto
