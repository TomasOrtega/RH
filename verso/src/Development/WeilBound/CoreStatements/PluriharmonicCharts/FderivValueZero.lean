import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
import Development.WeilBound.CoreStatements.VolumeEquality.CoverRootsSch
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open scoped Matrix ComplexOrder

noncomputable section

namespace PositivityTheory.Xgp.c_bm_exists_period

/- English proof (translation)
Use `letI := β.toAlgebra`. Use `letI := s.toAlgebra`. Take `⟨I₁, x, hx⟩` from `exists_isTranscendenceBasis' K k`. Take `⟨κ, z, hz⟩` from `exists_isTranscendenceBasis' K ℂ`. Establish `hI₁ : Countable I₁` using `hx.1.injective.countable`.

Establish `hκ : Cardinal.mk ℂ = Cardinal.mk κ`. Use `IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' z hz (Cardinal.mk_le_aleph0_iff.2 inferInstance) (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum)` as an intermediate fact. Conclude with `this`. Establish `hle : Cardinal.mk I₁ ≤ Cardinal.mk κ`. Rewrite using `[← hκ, Cardinal.mk_complex]`.

Conclude with `(Cardinal.mk_le_aleph0_iff.2 hI₁).trans Cardinal.aleph0_le_continuum`. Take `⟨e⟩` from `hle`. Establish `hz' : AlgebraicIndependent K (z ∘ e)` using `hz.1.comp e e.injective`. Use `letI : Algebra (MvPolynomial I₁ K) k := (MvPolynomial.aeval x : MvPolynomial I₁ K →ₐ[K] k).toRingHom.toAlgebra`. Use `letI : Algebra (MvPolynomial I₁ K) ℂ := (MvPolynomial.aeval (z ∘ e) : MvPolynomial I₁ K →ₐ[K] ℂ).toRingHom.toAlgebra`.

Use `haveI : FaithfulSMul (MvPolynomial I₁ K) k := (faithfulSMul_iff_algebraMap_injective _ _).2 hx.1`. Use `haveI : FaithfulSMul (MvPolynomial I₁ K) ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hz'`. Use `haveI : Algebra.IsAlgebraic (MvPolynomial I₁ K) k := by haveI := hx.isAlgebraic`. Conclude with `Algebra.IsAlgebraic.of_ringHom_of_comp_eq (S := Algebra.adjoin K (Set.range x)) (B := k) hx.1.aevalEquiv (RingHom.id k) hx.1.aevalEquiv.surjective Function.injective_id (RingHom.ext fun p => hx.1.algebraMap_aevalEquiv p)`. Set `j : k →ₐ[MvPolynomial I₁ K] ℂ` to `IsAlgClosed.lift`.

Use `⟨j.toRingHom, RingHom.ext fun a => ?_⟩` and prove the remaining obligations. Establish `h` using `j.commutes (MvPolynomial.C a)`. Establish `h1 : algebraMap (MvPolynomial I₁ K) k (MvPolynomial.C a) = β a` using `MvPolynomial.aeval_C x a`. Establish `h2 : algebraMap (MvPolynomial I₁ K) ℂ (MvPolynomial.C a) = s a` using `MvPolynomial.aeval_C (z ∘ e) a`. Rewrite `h` using `[h1, h2]`.

Conclude with `h`.
-/
theorem exists_embedding (K k : Type) [Field K] [Field k] [Countable K] [Countable k] (β : K →+* k) (s : K →+* ℂ) :
    ∃ j : k →+* ℂ, j.comp β = s := by
  letI := β.toAlgebra
  letI := s.toAlgebra
  obtain ⟨I₁, x, hx⟩ := exists_isTranscendenceBasis' K k
  obtain ⟨κ, z, hz⟩ := exists_isTranscendenceBasis' K ℂ
  have hI₁ : Countable I₁ := hx.1.injective.countable
  have hκ : Cardinal.mk ℂ = Cardinal.mk κ := by
    have := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' z hz
      (Cardinal.mk_le_aleph0_iff.2 inferInstance) (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum)
    exact this
  have hle : Cardinal.mk I₁ ≤ Cardinal.mk κ := by
    rw [← hκ, Cardinal.mk_complex]
    exact (Cardinal.mk_le_aleph0_iff.2 hI₁).trans Cardinal.aleph0_le_continuum
  obtain ⟨e⟩ := hle
  have hz' : AlgebraicIndependent K (z ∘ e) := hz.1.comp e e.injective
  letI : Algebra (MvPolynomial I₁ K) k := (MvPolynomial.aeval x : MvPolynomial I₁ K →ₐ[K] k).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial I₁ K) ℂ := (MvPolynomial.aeval (z ∘ e) : MvPolynomial I₁ K →ₐ[K] ℂ).toRingHom.toAlgebra
  haveI : FaithfulSMul (MvPolynomial I₁ K) k := (faithfulSMul_iff_algebraMap_injective _ _).2 hx.1
  haveI : FaithfulSMul (MvPolynomial I₁ K) ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hz'
  haveI : Algebra.IsAlgebraic (MvPolynomial I₁ K) k := by
    haveI := hx.isAlgebraic
    exact Algebra.IsAlgebraic.of_ringHom_of_comp_eq (S := Algebra.adjoin K (Set.range x)) (B := k) hx.1.aevalEquiv
      (RingHom.id k) hx.1.aevalEquiv.surjective Function.injective_id
      (RingHom.ext fun p => hx.1.algebraMap_aevalEquiv p)
  let j : k →ₐ[MvPolynomial I₁ K] ℂ := IsAlgClosed.lift
  refine ⟨j.toRingHom, RingHom.ext fun a => ?_⟩
  have h := j.commutes (MvPolynomial.C a)
  have h1 : algebraMap (MvPolynomial I₁ K) k (MvPolynomial.C a) = β a := MvPolynomial.aeval_C x a
  have h2 : algebraMap (MvPolynomial I₁ K) ℂ (MvPolynomial.C a) = s a := MvPolynomial.aeval_C (z ∘ e) a
  rw [h1, h2] at h
  exact h

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

/- English proof (translation)
Substitute `hq` using the available equality. Establish `: X.presheaf.stalkSpecializes h = 𝟙 _` using `TopCat.Presheaf.stalkSpecializes_refl _ _`. Use `⟨hξ.inj _, ?_⟩` and prove the remaining obligations. Unfold `genMap`. Simplify using `only [this]`.

Conclude with `hξ.bij.2`.
-/
theorem genMap_bij (hξ : IsCptGen ξ) (q : X) (hq : q = genPt ξ) (h : genPt ξ ⤳ q) :
    Function.Bijective (genMap ξ ⟨q, h⟩) := by
  subst hq
  have : X.presheaf.stalkSpecializes h = 𝟙 _ := TopCat.Presheaf.stalkSpecializes_refl _ _
  refine ⟨hξ.inj _, ?_⟩
  unfold genMap
  simp only [this]
  exact hξ.bij.2

/- English proof (translation)
Take `⟨c, hc⟩` from `h.cover ⟨genPt ξ, specializes_rfl⟩`. Use `haveI : Countable (MvPolynomial κ ℤ) := by`. Rewrite using `[← Cardinal.mk_le_aleph0_iff]`. Conclude with `MvPolynomial.cardinalMk_le_max.trans (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl)`. Use `Function.Surjective.countable (f := fun a : MvPolynomial κ ℤ × MvPolynomial κ ℤ => MvPolynomial.aeval (fun j => x j / x c) a.1 / MvPolynomial.aeval (fun j => x j / x c) a.2) fun a => ?_` and prove the remaining obligations.

Take `⟨s, hs, hu, hsa⟩` from `(GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x h c _ hc a).1 ((genMap_bij h.gen _ rfl _).2 a)`. Rewrite `hs`, `hsa` using `[Algebra.adjoin_range_eq_range_aeval]`. Take `⟨f, hf⟩` from `hs`. Take `⟨g, hg⟩` from `hsa`. Use `⟨(g, f), ?_⟩` and prove the remaining obligations.

Establish `hf' : MvPolynomial.aeval (fun j => x j / x c) f = s` using `hf`. Establish `hg' : MvPolynomial.aeval (fun j => x j / x c) g = s * a` using `hg`. Simplify using `only [hf', hg']`. Conclude with `mul_div_cancel_left₀ _ hu.1`.
-/
theorem countable_of_tie {κ : Type} [Finite κ] {x : κ → Ω} (h : CoordTie ℤ ξ x) : Countable Ω := by
  obtain ⟨c, hc⟩ := h.cover ⟨genPt ξ, specializes_rfl⟩
  haveI : Countable (MvPolynomial κ ℤ) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact MvPolynomial.cardinalMk_le_max.trans (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl)
  refine Function.Surjective.countable (f := fun a : MvPolynomial κ ℤ × MvPolynomial κ ℤ =>
    MvPolynomial.aeval (fun j => x j / x c) a.1 / MvPolynomial.aeval (fun j => x j / x c) a.2) fun a => ?_
  obtain ⟨s, hs, hu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x h c _ hc a).1 ((genMap_bij h.gen _ rfl _).2 a)
  rw [Algebra.adjoin_range_eq_range_aeval] at hs hsa
  obtain ⟨f, hf⟩ := hs
  obtain ⟨g, hg⟩ := hsa
  refine ⟨(g, f), ?_⟩
  have hf' : MvPolynomial.aeval (fun j => x j / x c) f = s := hf
  have hg' : MvPolynomial.aeval (fun j => x j / x c) g = s * a := hg
  simp only [hf', hg']
  exact mul_div_cancel_left₀ _ hu.1

/- English proof (translation)
Establish `e` using `LieTangent.spec_genMap ξ ⟨genPt ξ, specializes_rfl⟩`. Establish `h' : (spMap a ≫ Spec.map (CommRingCat.ofHom (genMap ξ ⟨genPt ξ, specializes_rfl⟩))) ≫ X.fromSpecStalk _ = (spMap b ≫ Spec.map (CommRingCat.ofHom (genMap ξ ⟨genPt ξ, specializes_rfl⟩))) ≫ X.fromSpecStalk _`. Rewrite using `[Category.assoc, Category.assoc, e, h]`. Rewrite `h'` using `[cancel_mono, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp]`. Establish `h2` using `congrArg CommRingCat.Hom.hom (Spec.map_injective h')`.

Use `RingHom.ext fun t => ?_` and prove the remaining obligations. Take `⟨s, rfl⟩` from `(genMap_bij hξ _ rfl specializes_rfl).2 t`. Conclude with `DFunLike.congr_fun h2 s`.
-/
theorem cancel_gen (hξ : IsCptGen ξ) {R : Type} [CommRing R] {a b : Ω →+* R} (h : spMap a ≫ ξ = spMap b ≫ ξ) :
    a = b := by
  have e := LieTangent.spec_genMap ξ ⟨genPt ξ, specializes_rfl⟩
  have h' : (spMap a ≫ Spec.map (CommRingCat.ofHom (genMap ξ ⟨genPt ξ, specializes_rfl⟩))) ≫ X.fromSpecStalk _ =
      (spMap b ≫ Spec.map (CommRingCat.ofHom (genMap ξ ⟨genPt ξ, specializes_rfl⟩))) ≫ X.fromSpecStalk _ := by
    rw [Category.assoc, Category.assoc, e, h]
  rw [cancel_mono, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp] at h'
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h')
  refine RingHom.ext fun t => ?_
  obtain ⟨s, rfl⟩ := (genMap_bij hξ _ rfl specializes_rfl).2 t
  exact DFunLike.congr_fun h2 s

/- English proof (translation)
Establish `h : genPt ξ ⤳ centre V` using `hV ▸ specializes_rfl`. Set `e` to `RingEquiv.ofBijective _ (genMap_bij hξ _ hV h)`. Use `⟨(Scheme.stalkClosedPointTo V).hom.comp e.symm.toRingHom, ?_⟩` and prove the remaining obligations. Establish `e1` using `LieTangent.spec_genMap ξ ⟨centre V, h⟩`. Establish `e2` using `LieTangent.spec_centre V`.

Use `(congrArg (spMap _ ≫ ·) e1.symm).trans (Eq.trans ?_ e2)` and prove the remaining obligations. Rewrite using `[← Category.assoc, spMap, ← Spec.map_comp]`. Use `congr 2`. Use extensionality with `s`. Conclude with `congrArg (Scheme.stalkClosedPointTo V).hom (e.symm_apply_apply s)`.
-/
theorem factor_gen (hξ : IsCptGen ξ) {R : Type} [CommRing R] [IsLocalRing R] (V : Sp R ⟶ X)
    (hV : centre V = genPt ξ) : ∃ δ : Ω →+* R, spMap δ ≫ ξ = V := by
  have h : genPt ξ ⤳ centre V := hV ▸ specializes_rfl
  let e := RingEquiv.ofBijective _ (genMap_bij hξ _ hV h)
  refine ⟨(Scheme.stalkClosedPointTo V).hom.comp e.symm.toRingHom, ?_⟩
  have e1 := LieTangent.spec_genMap ξ ⟨centre V, h⟩
  have e2 := LieTangent.spec_centre V
  refine (congrArg (spMap _ ≫ ·) e1.symm).trans (Eq.trans ?_ e2)
  rw [← Category.assoc, spMap, ← Spec.map_comp]
  congr 2
  ext s
  exact congrArg (Scheme.stalkClosedPointTo V).hom (e.symm_apply_apply s)

/- English proof (translation)
Use `letI := i.toAlgebra`. Use `letI := (δ.comp i).toAlgebra`. Use `haveI : CharZero F₀ := i.charZero`. Use `haveI : Module.Finite F₀ F := Module.finite_of_finrank_pos hfin`. Establish `hu : Algebra.FormallyUnramified F₀ F` using `Algebra.FormallyUnramified.of_isSeparable F₀ F`.

Establish `h` using `Algebra.FormallyUnramified.ext' (R := F₀) (A := F) (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ⟨2, by`. Rewrite using `[Submodule.zero_eq_bot, eq_bot_iff, sq, Ideal.mul_le]`. Introduce `a ha b hb`. Establish `ha' : a.fst = 0` using `ha`. Establish `hb' : b.fst = 0` using `hb`.

Rewrite using `[Ideal.mem_bot]`. Apply the tactic sequence `ext <;> simp [ha', hb']⟩`. Use the proof step `{ δ with commutes' := fun _ => rfl } { δ' with commutes' := fun r => (DFunLike.congr_fun h r).symm } h'`. Conclude with `RingHom.ext fun x => DFunLike.congr_fun h x`.
-/
theorem hom_dual_ext {F₀ F : Type} [Field F₀] [Field F] [CharZero F] (i : F₀ →+* F)
    (hfin : 0 < (letI := i.toAlgebra; Module.finrank F₀ F)) {δ δ' : F →+* DualNumber ℂ} (h : δ.comp i = δ'.comp i)
    (h' : ∀ x, (δ x).fst = (δ' x).fst) : δ = δ' := by
  letI := i.toAlgebra
  letI := (δ.comp i).toAlgebra
  haveI : CharZero F₀ := i.charZero
  haveI : Module.Finite F₀ F := Module.finite_of_finrank_pos hfin
  have hu : Algebra.FormallyUnramified F₀ F := Algebra.FormallyUnramified.of_isSeparable F₀ F
  have h := Algebra.FormallyUnramified.ext' (R := F₀) (A := F) (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom
    ⟨2, by
      rw [Submodule.zero_eq_bot, eq_bot_iff, sq, Ideal.mul_le]
      intro a ha b hb
      have ha' : a.fst = 0 := ha
      have hb' : b.fst = 0 := hb
      rw [Ideal.mem_bot]
      ext <;> simp [ha', hb']⟩
    { δ with commutes' := fun _ => rfl } { δ' with commutes' := fun r => (DFunLike.congr_fun h r).symm } h'
  exact RingHom.ext fun x => DFunLike.congr_fun h x

/- English proof (translation)
Establish `hc : centre V = genPt ξ`. Establish `a1 : centre (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ V) = centre V`. Conclude with `congrArg V (Spec_closedPoint (f := CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom))`. Rewrite using `[← a1, h1]`. Conclude with `SheetDecomposition.CovSch.centre_spMap φ ξ`.

Take `⟨δ, rfl⟩` from `factor_gen hξ V hc`. Establish `sc : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C), spMap (g.comp f) = spMap g ≫ spMap f` using `fun f g => Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)`. Establish `e1 : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp δ = φ` using `cancel_gen hξ (by rw [sc, Category.assoc, h1])`. Establish `e2 : δ.comp i = ((algebraMap ℂ (DualNumber ℂ)).comp φ).comp i` using `cancel_gen hξ₀ (by`. Rewrite using `[sc, sc _ ((algebraMap ℂ (DualNumber ℂ)).comp φ), sc φ, Category.assoc, Category.assoc, Category.assoc, ← hf]`.

Simplify `h2)` using `only [Category.assoc]`. Rewrite using `[hom_dual_ext i hfin e2 fun x => by`. Simplify `DFunLike.congr_fun e1 x, sc, Category.assoc]` using `[TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem const_of_finite {Y : Scheme.{0}} {Ω₀ : Type} [Field Ω₀] [CharZero Ω] {ξ₀ : Sp Ω₀ ⟶ Y} (hξ : IsCptGen ξ)
    (hξ₀ : IsCptGen ξ₀) {f : X ⟶ Y} {i : Ω₀ →+* Ω} (hf : ξ ≫ f = spMap i ≫ ξ₀)
    (hfin : 0 < (letI := i.toAlgebra; Module.finrank Ω₀ Ω)) {φ : Ω →+* ℂ} {V : Sp (DualNumber ℂ) ⟶ X}
    (h1 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ V = spMap φ ≫ ξ)
    (h2 : V ≫ f = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (spMap φ ≫ ξ) ≫ f) :
    V = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap φ ≫ ξ := by
  have hc : centre V = genPt ξ := by
    have a1 : centre (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ V) = centre V := by
      exact congrArg V (Spec_closedPoint (f := CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom))
    rw [← a1, h1]
    exact SheetDecomposition.CovSch.centre_spMap φ ξ
  obtain ⟨δ, rfl⟩ := factor_gen hξ V hc
  have sc : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap (g.comp f) = spMap g ≫ spMap f := fun f g => Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)
  have e1 : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp δ = φ := cancel_gen hξ (by rw [sc, Category.assoc, h1])
  have e2 : δ.comp i = ((algebraMap ℂ (DualNumber ℂ)).comp φ).comp i := cancel_gen hξ₀ (by
    rw [sc, sc _ ((algebraMap ℂ (DualNumber ℂ)).comp φ), sc φ, Category.assoc, Category.assoc, Category.assoc, ← hf]
    simpa only [Category.assoc] using h2)
  rw [hom_dual_ext i hfin e2 fun x => by
    simpa [TrivSqZeroExt.algebraMap_eq_inl] using DFunLike.congr_fun e1 x, sc, Category.assoc]

/- English proof (translation)
Take `⟨g, rfl⟩` from `hξ.bij.2 a`. Take `⟨U, hU, s, rfl⟩` from `X.presheaf.exists_germ_eq g`. Establish `hU0 : ⊤ ≤ p 0 ⁻¹ᵁ U` using `(SheetDecomposition.CovSch.top_le_iff _ _).2 (hc ▸ hU)`. Establish `he : r =ᶠ[nhds 0] fun u => valAt' (p u) U s` using `by filter_upwards [hr, GlobalTheory.LocalLift.hol_eventually_mem hp h0 hU0] with u h1 h2`. Establish `h3` using `(SheetDecomposition.CovSch.top_le_iff _ _).1 h2.2`.

Rewrite using `[SheetDecomposition.CovSch.valAt'_eq _ _ h3]`. Conclude with `SheetDecomposition.CovSch.v_unique hξ h1 (SheetDecomposition.CovSch.valAt_sec (hall _) U h3 hU s)`. Establish `h1 : ⊤ ≤ (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p 0) ⁻¹ᵁ U` using `fun q _ => hU0 (Set.mem_univ _)`. Rewrite using `[he.fderiv_eq, ← hv.2 U h1 s]`. Use `GlobalTheory.TangentOrigin.evalPt_spMap_comp (algebraMap ℂ (DualNumber ℂ)) (p 0) U hU0 h1 s` as an intermediate fact.

Use `(congrArg TrivSqZeroExt.snd this).trans ?_` and prove the remaining obligations. Simplify using `[TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem fderiv_value_zero (hξ : IsCptGen ξ) (hall : ∀ q : X, genPt ξ ⤳ q) {n : ℕ} {B : Set (Fin n → ℂ)}
    {p : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (hp : IsHolTo B p) (h0 : 0 ∈ B) (hc : centre (p 0) = centre ξ) {v : Fin n → ℂ}
    (hv : IsDerivAt0 p v (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p 0)) {a : Ω} {r : (Fin n → ℂ) → ℂ}
    (hr : ∀ᶠ u in nhds 0, ValAt ξ (p u) a (r u)) : fderiv ℂ r 0 v = 0 := by
  obtain ⟨g, rfl⟩ := hξ.bij.2 a
  obtain ⟨U, hU, s, rfl⟩ := X.presheaf.exists_germ_eq g
  have hU0 : ⊤ ≤ p 0 ⁻¹ᵁ U := (SheetDecomposition.CovSch.top_le_iff _ _).2 (hc ▸ hU)
  have he : r =ᶠ[nhds 0] fun u => valAt' (p u) U s := by
    filter_upwards [hr, GlobalTheory.LocalLift.hol_eventually_mem hp h0 hU0] with u h1 h2
    have h3 := (SheetDecomposition.CovSch.top_le_iff _ _).1 h2.2
    rw [SheetDecomposition.CovSch.valAt'_eq _ _ h3]
    exact SheetDecomposition.CovSch.v_unique hξ h1 (SheetDecomposition.CovSch.valAt_sec (hall _) U h3 hU s)
  have h1 : ⊤ ≤ (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p 0) ⁻¹ᵁ U := fun q _ => hU0 (Set.mem_univ _)
  rw [he.fderiv_eq, ← hv.2 U h1 s]
  have := GlobalTheory.TangentOrigin.evalPt_spMap_comp (algebraMap ℂ (DualNumber ℂ)) (p 0) U hU0 h1 s
  refine (congrArg TrivSqZeroExt.snd this).trans ?_
  simp [TrivSqZeroExt.algebraMap_eq_inl]

end PositivityTheory.Xgp.c_bm_exists_period
