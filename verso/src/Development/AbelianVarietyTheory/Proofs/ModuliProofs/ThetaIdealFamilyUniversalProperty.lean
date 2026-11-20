import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGrpPullbackOfLoc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaConstantsLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasThStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointsVanishingIdealRadicalHomogeneous
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescentStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelIsoUniqueOfDenseCommonFibresStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.FamRep

/- English proof (translation)
Assemble the required witnesses or components as `⟨(Spec.preimage x).hom, Spec.map_preimage x⟩`.
-/
theorem spMap_surj {R R' : Type} [CommRing R] [CommRing R'] (x : Sp R' ⟶ Sp R) : ∃ β : R →+* R', spMap β = x :=
  ⟨(Spec.preimage x).hom, Spec.map_preimage x⟩

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (h : B →+* C) :
    spMap h ≫ spMap f = spMap (h.comp f) := by
  rw [← Spec.map_comp]; rfl

/- English proof (translation)
The claim follows from `congrArg CommRingCat.Hom.hom (Spec.map_injective h)`.
-/
theorem spMap_inj {R R' : Type} [CommRing R] [CommRing R'] {f f' : R →+* R'} (h : spMap f = spMap f') : f = f' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

open MvPolynomial in

/- English proof (translation)
Rewrite using `[eval₂_eq, eval₂_eq, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations. Establish `hd : ∑ j ∈ a.support, a j = e`. Use `hF (mem_support_iff.1 ha)` as an intermediate fact. Rewrite using `[← this, Finsupp.weight_apply, Finsupp.sum]`.

Simplify using the standard rewrite rules. Simplify using `only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval₂_scale {σ R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (c : A) (x : σ → A) {F : MvPolynomial σ R}
    {e : ℕ} (hF : F.IsHomogeneous e) : eval₂ φ (fun j => c * x j) F = c ^ e * eval₂ φ x F := by
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hd : ∑ j ∈ a.support, a j = e := by
    have := hF (mem_support_iff.1 ha)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {s : S ⟶ Sp o}

/- English proof (translation)
Take `⟨β, rfl⟩` from `spMap_surj sw`. Take `⟨w', hw'⟩` from `tObj_pull o g _ J b _ _ s _ z t e`. Take `⟨ψ, hψ⟩` from `tMap_iff.1 hw'`. Take `⟨χ, rfl, hχ⟩` from `hψ.cancel (h.congr (Category.id_comp z).symm rfl)`. Take `⟨χ', rfl, hχ'⟩` from `hψ.cancel (h'.congr (Category.id_comp z).symm rfl)`.

Rewrite using `[(GlobalTheory.T.thetaLevel_iso_unique_of_dense_common_fibres hL hL2 o g N' J b m R β w w' hm hd ho ?_).2 χ χ' hχ.1 hχ'.1 hχ.2.1 hχ'.2.1 fun i => (hχ.2.2.1 i).trans (hχ'.2.2.1 i).symm]`. Use `Dense.mono (fun p _ => ?_) dense_univ` and prove the remaining obligations. Take `⟨u, hu⟩` from `tObj_pull o g _ J b _ _ _ _ ((Sp R).fromSpecResidueField p) w rfl`. Use `⟨(Sp R).residueField p, inferInstance, (Sp R).fromSpecResidueField p, u, ?_, hu, ?_⟩` and prove the remaining obligations. Conclude with `⟨IsLocalRing.closedPoint _, Scheme.fromSpecResidueField_apply _ _⟩`.

Use `tMap_comp hu (tMap_iff.2 ⟨_, hχ⟩)` as an intermediate fact. Rewrite `this` using `[Category.comp_id]`. Then use the resulting hypothesis.
-/
theorem isTM_unique (hL : Out.Laws) (hL2 : Out.Laws2) {m : ℕ} (hm : 2 ≤ m) (hd : m ^ 2 ∣ N') (ho : Odd N')
    (t : TObj g (N' ^ 2) J b s) (R : Type) [CommRing R] [IsReduced R] (z : Sp R ⟶ S) (sw : Sp R ⟶ Sp o)
    (e : z ≫ s = sw) (w : TObj g (N' ^ 2) J b sw) (φ φ' : w.A.left ⟶ t.A.left) (h : IsTM w t z φ)
    (h' : IsTM w t z φ') : φ = φ' := by
  obtain ⟨β, rfl⟩ := spMap_surj sw
  obtain ⟨w', hw'⟩ := tObj_pull o g _ J b _ _ s _ z t e
  obtain ⟨ψ, hψ⟩ := tMap_iff.1 hw'
  obtain ⟨χ, rfl, hχ⟩ := hψ.cancel (h.congr (Category.id_comp z).symm rfl)
  obtain ⟨χ', rfl, hχ'⟩ := hψ.cancel (h'.congr (Category.id_comp z).symm rfl)
  rw [(GlobalTheory.T.thetaLevel_iso_unique_of_dense_common_fibres hL hL2 o g N' J b m R β w w' hm hd ho ?_).2 χ χ' hχ.1 hχ'.1 hχ.2.1 hχ'.2.1
    fun i => (hχ.2.2.1 i).trans (hχ'.2.2.1 i).symm]
  refine Dense.mono (fun p _ => ?_) dense_univ
  obtain ⟨u, hu⟩ := tObj_pull o g _ J b _ _ _ _ ((Sp R).fromSpecResidueField p) w rfl
  refine ⟨(Sp R).residueField p, inferInstance, (Sp R).fromSpecResidueField p, u, ?_, hu, ?_⟩
  · exact ⟨IsLocalRing.closedPoint _, Scheme.fromSpecResidueField_apply _ _⟩
  · have := tMap_comp hu (tMap_iff.2 ⟨_, hχ⟩)
    rwa [Category.comp_id] at this

/- English proof (translation)
Take `⟨R, _, x, v, hx, hp, hv⟩` from `ThetaLocal.exists_hasTh hL hL2 o g N' J b S s t ho (y (IsLocalRing.closedPoint K))`. Establish `hr : Set.range y ⊆ Set.range x`. Introduce and unpack `_ ⟨q, rfl⟩`. Rewrite using `[Subsingleton.elim (α := PrimeSpectrum K) q (IsLocalRing.closedPoint K)]` and apply the resulting hypothesis. Take `⟨ρ, hρ⟩` from `spMap_surj (IsOpenImmersion.lift x y hr)`.

Use `GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b S s t R K ρ x v hv` as an intermediate fact. Rewrite `this` using `[hρ, IsOpenImmersion.lift_fac]`. Conclude with `⟨_, this⟩`.
-/
theorem exists_hasTh_field (hL : Out.Laws) (hL2 : Out.Laws2) (ho : Odd N') (t : TObj g (N' ^ 2) J b s)
    (K : Type) [Field K] (y : Sp K ⟶ S) : ∃ v, t.HasTh y v := by
  obtain ⟨R, _, x, v, hx, hp, hv⟩ := ThetaLocal.exists_hasTh hL hL2 o g N' J b S s t ho (y (IsLocalRing.closedPoint K))
  have hr : Set.range y ⊆ Set.range x := by
    rintro _ ⟨q, rfl⟩
    rwa [Subsingleton.elim (α := PrimeSpectrum K) q (IsLocalRing.closedPoint K)]
  obtain ⟨ρ, hρ⟩ := spMap_surj (IsOpenImmersion.lift x y hr)
  have := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b S s t R K ρ x v hv
  rw [hρ, IsOpenImmersion.lift_fac] at this
  exact ⟨_, this⟩

/- English proof (translation)
Take `⟨K₀, _, β₀, i, j, t₀, tx, tc, hj, hi, h1, h2, h3, hC⟩` from `hy`. Take `⟨v₀, hv₀⟩` from `exists_hasTh_field hL hL2 ho t₀ K₀ (𝟙 _)`. Establish `a1 : tx.HasTh (𝟙 _) v` using `(hasTh_iff_of_tmap o g N' J b _ _ t _ _ tx y K _ v h1).2 (by rwa [Category.id_comp])`. Establish `a2 : tx.HasTh (𝟙 _) (fun a => i (v₀ a))` using `(hasTh_iff_of_tmap o g N' J b _ _ t₀ _ _ tx _ K _ _ h2).2 (by`. Use `GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b _ _ t₀ K₀ K i _ v₀ hv₀` as an intermediate fact.

Rewrite using `[Category.comp_id, ← Category.id_comp (spMap i)] at this)` and apply the resulting hypothesis. Establish `a3 : tc.HasTh (𝟙 _) (fun a => j (v₀ a))` using `(hasTh_iff_of_tmap o g N' J b _ _ t₀ _ _ tc _ ℂ _ _ h3).2 (by`. Use `GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b _ _ t₀ K₀ ℂ j _ v₀ hv₀` as an intermediate fact. Rewrite using `[Category.comp_id, ← Category.id_comp (spMap j)] at this)` and apply the resulting hypothesis. Take `⟨c, hc⟩` from `GlobalTheory.T.thetaCosetNonvanishing_of_hasTh hL hL2 o g N' J b _ _ tx n K _ _ ⊥ hn hd a2 Ideal.isPrime_bot 0`.

Take `⟨u, hu⟩` from `hasTh_unique_unit hL hL2 o g N' J b _ _ tx K _ _ _ a2 a1 (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, rfl⟩) (Ne.isUnit (by simpa using hc)))`. Take `rfl : β = i.comp β₀` from `spMap_inj (hβ.symm.trans (hi.trans (spMap_comp_eq _ _)))`. Take `rfl : v = fun a => (u : K) * i (v₀ a)` from `funext hu`. Introduce `F hF`. Rewrite using `[← F.sum_homogeneousComponent, MvPolynomial.eval₂_sum]`.

Use `Finset.sum_eq_zero fun e _ => ?_` and prove the remaining obligations. Establish `hG` using `(GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree o g N' J b em C hem).2.1 F hF e`. Establish `h0 : MvPolynomial.eval₂ em (fun a => j (v₀ a)) (MvPolynomial.homogeneousComponent e F) = 0`. Simplify using `only [thIdeal, Ideal.mem_iInf] at hG`. Conclude with `hG tc _ ⟨hC, a3⟩`.

Establish `h4 : MvPolynomial.eval₂ β₀ v₀ (MvPolynomial.homogeneousComponent e F) = 0`. Apply `j.injective` to reduce the goal to its premises. Rewrite using `[MvPolynomial.eval₂_comp_left, hj, map_zero]`. Conclude with `h0`. Rewrite using `[eval₂_scale _ _ _ (MvPolynomial.homogeneousComponent_isHomogeneous e F)]`.

Establish `h5` using `congrArg i h4`. Rewrite `h5` using `[MvPolynomial.eval₂_comp_left, map_zero]`. Conclude with `mul_eq_zero_of_right _ h5`.
-/
theorem eval_eq_zero_of_fromC (hL : Out.Laws) (hL2 : Out.Laws2) {n : ℕ} (hn : 2 ≤ n) (hd : n ∣ N') (ho : Odd N')
    {em : o →+* ℂ} (hem : Function.Injective em) {C : TObj g (N' ^ 2) J b (spMap em) → Prop}
    (t : TObj g (N' ^ 2) J b s) {K : Type} [Field K] (y : Sp K ⟶ S) (hy : FromC em C t y) (β : o →+* K)
    (hβ : y ≫ s = spMap β) (v : Ix g (N' ^ 2) → K) (hv : t.HasTh y v) :
    ∀ F ∈ thIdeal em C, MvPolynomial.eval₂ β v F = 0 := by
  obtain ⟨K₀, _, β₀, i, j, t₀, tx, tc, hj, hi, h1, h2, h3, hC⟩ := hy
  obtain ⟨v₀, hv₀⟩ := exists_hasTh_field hL hL2 ho t₀ K₀ (𝟙 _)
  have a1 : tx.HasTh (𝟙 _) v := (hasTh_iff_of_tmap o g N' J b _ _ t _ _ tx y K _ v h1).2 (by rwa [Category.id_comp])
  have a2 : tx.HasTh (𝟙 _) (fun a => i (v₀ a)) := (hasTh_iff_of_tmap o g N' J b _ _ t₀ _ _ tx _ K _ _ h2).2 (by
    have := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b _ _ t₀ K₀ K i _ v₀ hv₀
    rwa [Category.comp_id, ← Category.id_comp (spMap i)] at this)
  have a3 : tc.HasTh (𝟙 _) (fun a => j (v₀ a)) := (hasTh_iff_of_tmap o g N' J b _ _ t₀ _ _ tc _ ℂ _ _ h3).2 (by
    have := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b _ _ t₀ K₀ ℂ j _ v₀ hv₀
    rwa [Category.comp_id, ← Category.id_comp (spMap j)] at this)
  obtain ⟨c, hc⟩ := GlobalTheory.T.thetaCosetNonvanishing_of_hasTh hL hL2 o g N' J b _ _ tx n K _ _ ⊥ hn hd a2 Ideal.isPrime_bot 0
  obtain ⟨u, hu⟩ := hasTh_unique_unit hL hL2 o g N' J b _ _ tx K _ _ _ a2 a1
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, rfl⟩) (Ne.isUnit (by simpa using hc)))
  obtain rfl : β = i.comp β₀ := spMap_inj (hβ.symm.trans (hi.trans (spMap_comp_eq _ _)))
  obtain rfl : v = fun a => (u : K) * i (v₀ a) := funext hu
  intro F hF
  rw [← F.sum_homogeneousComponent, MvPolynomial.eval₂_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  have hG := (GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree o g N' J b em C hem).2.1 F hF e
  have h0 : MvPolynomial.eval₂ em (fun a => j (v₀ a)) (MvPolynomial.homogeneousComponent e F) = 0 := by
    simp only [thIdeal, Ideal.mem_iInf] at hG
    exact hG tc _ ⟨hC, a3⟩
  have h4 : MvPolynomial.eval₂ β₀ v₀ (MvPolynomial.homogeneousComponent e F) = 0 := by
    apply j.injective
    rw [MvPolynomial.eval₂_comp_left, hj, map_zero]
    exact h0
  rw [eval₂_scale _ _ _ (MvPolynomial.homogeneousComponent_isHomogeneous e F)]
  have h5 := congrArg i h4
  rw [MvPolynomial.eval₂_comp_left, map_zero] at h5
  exact mul_eq_zero_of_right _ h5

/- English proof (translation)
Use `Dense.mono (fun p hp => ?_) (hD.preimage x.isOpenEmbedding.isOpenMap)` and prove the remaining obligations. Take `⟨K, _, y, ⟨q, hq⟩, hy⟩` from `hp`. Establish `hr : Set.range y ⊆ Set.range x`. Introduce and unpack `_ ⟨q', rfl⟩`. Rewrite using `[Subsingleton.elim (α := PrimeSpectrum K) q' q, hq]`.

Conclude with `⟨p, rfl⟩`. Take `⟨ρ, hρ⟩` from `spMap_surj (IsOpenImmersion.lift x y hr)`. Establish `e : spMap ρ ≫ x = y` using `by rw [hρ, IsOpenImmersion.lift_fac]`. Use `⟨K, inferInstance, ρ, ⟨q, x.isOpenEmbedding.injective ?_⟩, by rwa [e]⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, e, hq]`.
-/
theorem dense_affine {k : ℕ} {b : TBase o k} {em : o →+* ℂ} {C : TObj g k J b (spMap em) → Prop} {t : TObj g k J b s}
    (hD : Dense (fromSet em C t)) {R : Type} [CommRing R] (x : Sp R ⟶ S) [IsOpenImmersion x] :
    Dense {p : Sp R | ∃ (K : Type) (_ : Field K) (ψ : R →+* K), p ∈ Set.range (spMap ψ) ∧ FromC em C t (spMap ψ ≫ x)} := by
  refine Dense.mono (fun p hp => ?_) (hD.preimage x.isOpenEmbedding.isOpenMap)
  obtain ⟨K, _, y, ⟨q, hq⟩, hy⟩ := hp
  have hr : Set.range y ⊆ Set.range x := by
    rintro _ ⟨q', rfl⟩
    rw [Subsingleton.elim (α := PrimeSpectrum K) q' q, hq]
    exact ⟨p, rfl⟩
  obtain ⟨ρ, hρ⟩ := spMap_surj (IsOpenImmersion.lift x y hr)
  have e : spMap ρ ≫ x = y := by rw [hρ, IsOpenImmersion.lift_fac]
  refine ⟨K, inferInstance, ρ, ⟨q, x.isOpenEmbedding.injective ?_⟩, by rwa [e]⟩
  rw [← Scheme.Hom.comp_apply, e, hq]

/- English proof (translation)
Use `⟨fun F hF => ?_, fun q hq => GlobalTheory.T.thetaCosetNonvanishing_of_hasTh hL hL2 o g N' J b S s t n R x v q hn hd hv hq⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hb : PrimeSpectrum.basicOpen (MvPolynomial.eval₂ β v F) ≠ ⊥` using `fun h => hne ((PrimeSpectrum.basicOpen_eq_bot_iff _).1 h).eq_zero`. Take `⟨p, ⟨K, _, ψ, ⟨q, rfl⟩, hy⟩, hp⟩` from `(dense_affine hD x).exists_mem_open (PrimeSpectrum.basicOpen (MvPolynomial.eval₂ β v F)).isOpen ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hb)`. Establish `h0` using `eval_eq_zero_of_fromC hL hL2 hn hd ho hem t _ hy (ψ.comp β) (by rw [Category.assoc, hβ, spMap_comp_eq]) _ (GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b S s t R K ψ x v hv) F hF`.

Use `hp (show ψ (MvPolynomial.eval₂ β v F) ∈ (show PrimeSpectrum K from q).asIdeal from ?_)` and prove the remaining obligations. Rewrite using `[MvPolynomial.eval₂_comp_left]`. Conclude with `(show MvPolynomial.eval₂ (ψ.comp β) (ψ ∘ v) F = 0 from h0) ▸ Ideal.zero_mem _`.
-/
theorem inMM_of_dense (hL : Out.Laws) (hL2 : Out.Laws2) {n : ℕ} (hn : 2 ≤ n) (hd : n ∣ N') (ho : Odd N')
    {em : o →+* ℂ} (hem : Function.Injective em) {C : TObj g (N' ^ 2) J b (spMap em) → Prop}
    {t : TObj g (N' ^ 2) J b s} (hD : Dense (fromSet em C t)) {R : Type} [CommRing R] [IsReduced R] (x : Sp R ⟶ S)
    [IsOpenImmersion x] (β : o →+* R) (hβ : x ≫ s = spMap β) (v : Ix g (N' ^ 2) → R) (hv : t.HasTh x v) :
    InMM n N' (thIdeal em C) β v := by
  refine ⟨fun F hF => ?_, fun q hq => GlobalTheory.T.thetaCosetNonvanishing_of_hasTh hL hL2 o g N' J b S s t n R x v q hn hd hv hq⟩
  by_contra hne
  have hb : PrimeSpectrum.basicOpen (MvPolynomial.eval₂ β v F) ≠ ⊥ := fun h =>
    hne ((PrimeSpectrum.basicOpen_eq_bot_iff _).1 h).eq_zero
  obtain ⟨p, ⟨K, _, ψ, ⟨q, rfl⟩, hy⟩, hp⟩ := (dense_affine hD x).exists_mem_open
    (PrimeSpectrum.basicOpen (MvPolynomial.eval₂ β v F)).isOpen
    ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hb)
  have h0 := eval_eq_zero_of_fromC hL hL2 hn hd ho hem t _ hy (ψ.comp β)
    (by rw [Category.assoc, hβ, spMap_comp_eq]) _ (GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b S s t R K ψ x v hv) F hF
  refine hp (show ψ (MvPolynomial.eval₂ β v F) ∈ (show PrimeSpectrum K from q).asIdeal from ?_)
  rw [MvPolynomial.eval₂_comp_left]
  exact (show MvPolynomial.eval₂ (ψ.comp β) (ψ ∘ v) F = 0 from h0) ▸ Ideal.zero_mem _

/- English proof (translation)
Take `⟨β, hβ⟩` from `spMap_surj (x ≫ s)`. Take `⟨tx, htx⟩` from `tObj_pull o g _ J b _ _ s _ x t hβ.symm`. Take `⟨ux, hux⟩` from `tObj_pull o g _ J b _ _ sM _ y u (hxy.trans hβ.symm)`. Establish `key : TMap tx ux (𝟙 _)`. Use `(GlobalTheory.T.thetaLevel_iso_unique_of_dense_common_fibres hL hL2 o g N' J b m R β tx ux hm hd ho (Dense.mono (fun p hp => ?_) (dense_affine hD x))).1` and prove the remaining obligations.

Take `⟨K, _, ψ, ⟨q, rfl⟩, K₀, _, β₀, i, j, t₀, tK, tc, -, -, h1, h2, h3, hc⟩` from `hp`. Set `a` to `algebraMap K (AlgebraicClosure K)`. Establish `ez : spMap a ≫ spMap ψ = spMap (a.comp ψ)` using `spMap_comp_eq _ _`. Take `⟨t', ht'⟩` from `tObj_pull o g _ J b _ _ _ ((spMap (a.comp ψ) ≫ y) ≫ sM) (spMap (a.comp ψ)) tx (by rw [Category.assoc, hxy, hβ])`. Take `⟨u', hu'⟩` from `tObj_pull o g _ J b _ _ _ _ (spMap (a.comp ψ)) tx rfl`.

Establish `s0 : t₀.Shape Mat κ` using `((GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w₀ w₀ _ _ _ _ _ t₀ tc h3).2.2 K₀ rfl inferInstance inferInstance).1 (hC tc hc)`. Establish `s1 : tK.Shape Mat κ` using `(GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w₀ w₀ _ _ _ _ _ t₀ tK h2).1 s0`. Establish `m1 : TMap t' t (spMap (a.comp ψ) ≫ x)` using `tMap_comp ht' htx`. Establish `m2 : TMap t' tK (spMap a)` using `tMap_cancel h1 (by rwa [← Category.assoc, ez])`. Establish `s2 : t'.Shape Mat κ` using `(GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w₀ w₀ _ _ _ _ _ tK t' m2).1 s1`.

Establish `m3 : TMap t' u (spMap (a.comp ψ) ≫ y)` using `hu _ _ t' _ s2 ((hasTh_iff_of_tmap o g N' J b _ _ t _ _ t' _ _ _ _ m1).2 (by`. Rewrite using `[Category.id_comp]`. Conclude with `GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b S s t R _ (a.comp ψ) x v hv))`. Use the proof step `(GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b M sM u R _ (a.comp ψ) y v hv')`. Establish `m4 : TMap u' t' (𝟙 _)` using `tMap_cancel ht' (by rwa [Category.id_comp])`.

Establish `m5` using `tMap_comp m4 m3`. Rewrite `m5` using `[Category.id_comp]`. Use `⟨AlgebraicClosure K, inferInstance, spMap (a.comp ψ), u', ⟨IsLocalRing.closedPoint _, ?_⟩, hu', tMap_cancel hux m5⟩` and prove the remaining obligations. Rewrite using `[← ez]`. Conclude with `(Scheme.Hom.comp_apply _ _ _).trans (congrArg _ (Subsingleton.elim (α := PrimeSpectrum K) _ _))`.

Establish `m : TMap w tx (𝟙 _)` using `tMap_cancel htx (by rwa [Category.id_comp])`. Use `tMap_comp (tMap_comp m key) hux` as an intermediate fact. Rewrite `this` using `[Category.id_comp, Category.id_comp]`. Then use the resulting hypothesis.
-/
theorem tMap_affine (hL : Out.Laws) (hL2 : Out.Laws2) {m : ℕ} (hm : 2 ≤ m) (hd : m ^ 2 ∣ N') (ho : Odd N')
    {em : o →+* ℂ} {C : TObj g (N' ^ 2) J b (spMap em) → Prop} {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ}
    (w₀ : J) (hC : ∀ t, C t → t.Shape Mat κ) {M : Scheme.{0}} {sM : M ⟶ Sp o} (u : TObj g (N' ^ 2) J b sM)
    (hu : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M) (t' : TObj g (N' ^ 2) J b (x ≫ sM)) v,
      t'.Shape Mat κ → t'.HasTh (𝟙 _) v → u.HasTh x v → TMap t' u x)
    {t : TObj g (N' ^ 2) J b s} (hD : Dense (fromSet em C t)) {R : Type} [CommRing R] [IsReduced R] (x : Sp R ⟶ S)
    [IsOpenImmersion x] (y : Sp R ⟶ M) (hxy : y ≫ sM = x ≫ s) (v : Ix g (N' ^ 2) → R) (hv : t.HasTh x v)
    (hv' : u.HasTh y v) (w : TObj g (N' ^ 2) J b (x ≫ s)) (hw : TMap w t x) : TMap w u y := by
  obtain ⟨β, hβ⟩ := spMap_surj (x ≫ s)
  obtain ⟨tx, htx⟩ := tObj_pull o g _ J b _ _ s _ x t hβ.symm
  obtain ⟨ux, hux⟩ := tObj_pull o g _ J b _ _ sM _ y u (hxy.trans hβ.symm)
  have key : TMap tx ux (𝟙 _) := by
    refine (GlobalTheory.T.thetaLevel_iso_unique_of_dense_common_fibres hL hL2 o g N' J b m R β tx ux hm hd ho (Dense.mono (fun p hp => ?_) (dense_affine hD x))).1
    obtain ⟨K, _, ψ, ⟨q, rfl⟩, K₀, _, β₀, i, j, t₀, tK, tc, -, -, h1, h2, h3, hc⟩ := hp
    let a := algebraMap K (AlgebraicClosure K)
    have ez : spMap a ≫ spMap ψ = spMap (a.comp ψ) := spMap_comp_eq _ _
    obtain ⟨t', ht'⟩ := tObj_pull o g _ J b _ _ _ ((spMap (a.comp ψ) ≫ y) ≫ sM) (spMap (a.comp ψ)) tx
      (by rw [Category.assoc, hxy, hβ])
    obtain ⟨u', hu'⟩ := tObj_pull o g _ J b _ _ _ _ (spMap (a.comp ψ)) tx rfl
    have s0 : t₀.Shape Mat κ := ((GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w₀ w₀ _ _ _ _ _ t₀ tc h3).2.2 K₀ rfl
      inferInstance inferInstance).1 (hC tc hc)
    have s1 : tK.Shape Mat κ := (GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w₀ w₀ _ _ _ _ _ t₀ tK h2).1 s0
    have m1 : TMap t' t (spMap (a.comp ψ) ≫ x) := tMap_comp ht' htx
    have m2 : TMap t' tK (spMap a) := tMap_cancel h1 (by rwa [← Category.assoc, ez])
    have s2 : t'.Shape Mat κ := (GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w₀ w₀ _ _ _ _ _ tK t' m2).1 s1
    have m3 : TMap t' u (spMap (a.comp ψ) ≫ y) := hu _ _ t' _ s2
      ((hasTh_iff_of_tmap o g N' J b _ _ t _ _ t' _ _ _ _ m1).2 (by
        rw [Category.id_comp]; exact GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b S s t R _ (a.comp ψ) x v hv))
      (GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b M sM u R _ (a.comp ψ) y v hv')
    have m4 : TMap u' t' (𝟙 _) := tMap_cancel ht' (by rwa [Category.id_comp])
    have m5 := tMap_comp m4 m3
    rw [Category.id_comp] at m5
    refine ⟨AlgebraicClosure K, inferInstance, spMap (a.comp ψ), u', ⟨IsLocalRing.closedPoint _, ?_⟩, hu',
      tMap_cancel hux m5⟩
    rw [← ez]
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg _ (Subsingleton.elim (α := PrimeSpectrum K) _ _))
  have m : TMap w tx (𝟙 _) := tMap_cancel htx (by rwa [Category.id_comp])
  have := tMap_comp (tMap_comp m key) hux
  rwa [Category.id_comp, Category.id_comp] at this

/- English proof (translation)
Introduce `hL hL2 g J _ Mat κ n w w' hn hodd`. Use `⟨2, fun j hj o _ b em C d hem hC Y u hu hq S s' t hS hD => ?_⟩` and prove the remaining obligations. Establish `ho : Odd (n ^ j)` using `hodd.pow`. Establish `hd : n ^ 2 ∣ n ^ j` using `pow_dvd_pow n hj`. Establish `hd1 : n ∣ n ^ j` using `dvd_pow_self n (by omega)`.

Establish `hred : ∀ (R : Type) [CommRing R] (x : Sp R ⟶ S), IsOpenImmersion x → _root_.IsReduced R` using `fun R _ x _ => (affine_isReduced_iff (CommRingCat.of R)).1 (isReduced_of_isOpenImmersion x)`. Establish `uniq : ∀ (R : Type) [CommRing R] (y y' : Sp R ⟶ Y.MM) (v : Ix g ((n ^ j) ^ 2) → R), y ≫ Y.s = y' ≫ Y.s → u.HasTh y v → u.HasTh y' v → y = y'`. Introduce `R _ y y' v e h h'`. Take `⟨β, hβ⟩` from `spMap_surj (y ≫ Y.s)`. Conclude with `(Y.pts R β v (Y.loc R β y v hβ.symm ((hu R y v).1 h))).unique ⟨hβ.symm, (hu R y v).1 h⟩ ⟨e.symm.trans hβ.symm, (hu R y' v).1 h'⟩`.

Use `choose R cR x v hx hp hv using ThetaLocal.exists_hasTh hL hL2 o g _ J b S s' t ho`. Establish `loc : ∀ p, ∃ y : Sp (R p) ⟶ Y.MM, y ≫ Y.s = x p ≫ s' ∧ u.HasTh y (v p)` using `fun p => by`. Use `hx p` as an intermediate fact. Use `hred _ _ (hx p)` as an intermediate fact. Take `⟨β, hβ⟩` from `spMap_surj (x p ≫ s')`.

Take `⟨y, ⟨h1, h2⟩, -⟩` from `Y.pts _ β _ (inMM_of_dense hL hL2 hn.two_le hd1 ho hem.2.2 hD (x p) β hβ.symm _ (hv p))`. Conclude with `⟨y, h1.trans hβ, (hu _ _ _).2 h2⟩`. Use `choose y hy hy' using loc`. Use `choose tx htx using fun p => tObj_pull o g _ J b _ _ s' _ (x p) t rfl`. Establish `hty : ∀ p, TMap (tx p) u (y p)` using `fun p => haveI := hx p haveI := hred _ _ (hx p) tMap_affine hL hL2 hn.two_le hd ho w (fun t ht => (hC.shape t ht).1) u (fun K _ _ x t' v h1 h2 h3 => hq K x t' v h1 h2 ((hu _ _ _).1 h3)) hD (x p) (y p) (hy p) (v p) (hv p) (hy' p) (tx p) (htx p)`.

Establish `tr : ∀ p (T : Type) [CommRing T] (a : Sp T ⟶ Sp (R p)) (c : Ix g ((n ^ j) ^ 2) → T), t.HasTh (a ≫ x p) c → u.HasTh (a ≫ y p) c` using `fun p T _ a c h => (hasTh_iff_of_tmap o g _ J b _ _ u _ _ (tx p) _ T a c (hty p)).1 ((hasTh_iff_of_tmap o g _ J b _ _ t _ _ (tx p) _ T a c (htx p)).2 h)`. Take `⟨f, hf⟩` from `exists_glue _ x y hx (fun p => ⟨p, hp p⟩) fun i i' q hq => by`. Use `hx i` as an intermediate fact. Use `hx i'` as an intermediate fact. Take `⟨T, z, hz, ⟨r, hr⟩, hs⟩` from `Scheme.exists_affine_mem_range_and_range_subset (U := (x i).opensRange ⊓ (x i').opensRange) (x := x i q) ⟨⟨q, rfl⟩, hq⟩`.

Take `⟨a, e1⟩ : ∃ a : Sp T ⟶ Sp (R i), a ≫ x i = z` from `⟨_, IsOpenImmersion.lift_fac (x i) z (fun p hp => (hs hp).1)⟩`. Take `⟨a', e2⟩ : ∃ a' : Sp T ⟶ Sp (R i'), a' ≫ x i' = z` from `⟨_, IsOpenImmersion.lift_fac (x i') z (fun p hp => (hs hp).2)⟩`. Establish `: IsOpenImmersion (a ≫ x i)` using `by rw [e1]; exact hz`. Use `⟨_, a, a', IsOpenImmersion.of_comp a (x i), ⟨r, (x i).isOpenEmbedding.injective ?_⟩, e1.trans e2.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, e1, hr]`.

Take `⟨ρ, hρ⟩` from `spMap_surj (R' := T) a`. Establish `h` using `GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g _ J b S s' t _ T ρ (x i) (v i) (hv i)`. Rewrite `h` using `[hρ]`. Use `uniq T _ _ _ ?_ (tr i T a _ h) (tr i' T a' _ (by rw [e2, ← e1]; exact h))` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, hy, hy, ← Category.assoc, ← Category.assoc]`.

Conclude with `congrArg (· ≫ s') (e1.trans e2.symm)`. Establish `hfs : f ≫ Y.s = s'` using `hom_ext_loc fun p => ⟨_, x p, hx p, hp p, by rw [← Category.assoc, hf, hy]⟩`. Use `⟨f, ⟨hfs, ?_⟩, fun f' hf' => hom_ext_loc fun p => ⟨_, x p, hx p, hp p, ?_⟩⟩` and prove the remaining obligations. Take `⟨u', hu'⟩` from `tObj_pull o g _ J b _ _ Y.s s' f u hfs`. Use `tMap_comp (tMap_of_loc hL.globalFns t u' (fun p => ⟨_, x p, tx p, hx p, hp p, htx p, tMap_cancel hu' (by rw [hf]; exact hty p)⟩) (fun t T _ z => tObj_pull o g _ J b _ _ s' _ z t rfl) (fun t T _ z w φ φ' hz h h' => haveI := hred T z hz isTM_unique hL hL2 hn.two_le hd ho t T z _ rf …` as an intermediate fact.

Rewrite `this` using `[Category.id_comp]`. Then use the resulting hypothesis. Rewrite using `[hf]`. Conclude with `uniq _ _ _ (v p) (by rw [Category.assoc, hf'.1, hy]) ((hasTh_iff_of_tmap o g _ J b _ _ u _ _ t f' _ (x p) (v p) hf'.2).1 (hv p)) (hy' p)`.
-/
theorem family_universal : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (Y : MMPre n (n ^ j) (thIdeal em C)) (u : TObj g ((n ^ j) ^ 2) J b Y.s), (∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.MM) (v : Ix g ((n ^ j) ^ 2) → R), u.HasTh x v ↔ SecCoord Y.de Y.th x v) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Y.MM) (t' : TObj g ((n ^ j) ^ 2) J b (x ≫ Y.s)) v, t'.Shape Mat κ → t'.HasTh (𝟙 _) v → SecCoord Y.de Y.th x v → TMap t' u x) → ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s'), IsReduced S → Dense (fromSet em C t) → ∃! f : S ⟶ Y.MM, f ≫ Y.s = s' ∧ TMap t u f := by
  intro hL hL2 g J _ Mat κ n w w' hn hodd
  refine ⟨2, fun j hj o _ b em C d hem hC Y u hu hq S s' t hS hD => ?_⟩
  have ho : Odd (n ^ j) := hodd.pow
  have hd : n ^ 2 ∣ n ^ j := pow_dvd_pow n hj
  have hd1 : n ∣ n ^ j := dvd_pow_self n (by omega)
  have hred : ∀ (R : Type) [CommRing R] (x : Sp R ⟶ S), IsOpenImmersion x → _root_.IsReduced R := fun R _ x _ =>
    (affine_isReduced_iff (CommRingCat.of R)).1 (isReduced_of_isOpenImmersion x)
  have uniq : ∀ (R : Type) [CommRing R] (y y' : Sp R ⟶ Y.MM) (v : Ix g ((n ^ j) ^ 2) → R), y ≫ Y.s = y' ≫ Y.s →
      u.HasTh y v → u.HasTh y' v → y = y' := by
    intro R _ y y' v e h h'
    obtain ⟨β, hβ⟩ := spMap_surj (y ≫ Y.s)
    exact (Y.pts R β v (Y.loc R β y v hβ.symm ((hu R y v).1 h))).unique ⟨hβ.symm, (hu R y v).1 h⟩
      ⟨e.symm.trans hβ.symm, (hu R y' v).1 h'⟩
  choose R cR x v hx hp hv using ThetaLocal.exists_hasTh hL hL2 o g _ J b S s' t ho
  have loc : ∀ p, ∃ y : Sp (R p) ⟶ Y.MM, y ≫ Y.s = x p ≫ s' ∧ u.HasTh y (v p) := fun p => by
    have := hx p
    have := hred _ _ (hx p)
    obtain ⟨β, hβ⟩ := spMap_surj (x p ≫ s')
    obtain ⟨y, ⟨h1, h2⟩, -⟩ := Y.pts _ β _ (inMM_of_dense hL hL2 hn.two_le hd1 ho hem.2.2 hD (x p) β hβ.symm _ (hv p))
    exact ⟨y, h1.trans hβ, (hu _ _ _).2 h2⟩
  choose y hy hy' using loc
  choose tx htx using fun p => tObj_pull o g _ J b _ _ s' _ (x p) t rfl
  have hty : ∀ p, TMap (tx p) u (y p) := fun p =>
    haveI := hx p
    haveI := hred _ _ (hx p)
    tMap_affine hL hL2 hn.two_le hd ho w (fun t ht => (hC.shape t ht).1) u
      (fun K _ _ x t' v h1 h2 h3 => hq K x t' v h1 h2 ((hu _ _ _).1 h3)) hD (x p) (y p) (hy p) (v p) (hv p) (hy' p)
      (tx p) (htx p)
  have tr : ∀ p (T : Type) [CommRing T] (a : Sp T ⟶ Sp (R p)) (c : Ix g ((n ^ j) ^ 2) → T),
      t.HasTh (a ≫ x p) c → u.HasTh (a ≫ y p) c := fun p T _ a c h =>
    (hasTh_iff_of_tmap o g _ J b _ _ u _ _ (tx p) _ T a c (hty p)).1
      ((hasTh_iff_of_tmap o g _ J b _ _ t _ _ (tx p) _ T a c (htx p)).2 h)
  obtain ⟨f, hf⟩ := exists_glue _ x y hx (fun p => ⟨p, hp p⟩) fun i i' q hq => by
    have := hx i
    have := hx i'
    obtain ⟨T, z, hz, ⟨r, hr⟩, hs⟩ := Scheme.exists_affine_mem_range_and_range_subset
      (U := (x i).opensRange ⊓ (x i').opensRange) (x := x i q) ⟨⟨q, rfl⟩, hq⟩
    obtain ⟨a, e1⟩ : ∃ a : Sp T ⟶ Sp (R i), a ≫ x i = z :=
      ⟨_, IsOpenImmersion.lift_fac (x i) z (fun p hp => (hs hp).1)⟩
    obtain ⟨a', e2⟩ : ∃ a' : Sp T ⟶ Sp (R i'), a' ≫ x i' = z :=
      ⟨_, IsOpenImmersion.lift_fac (x i') z (fun p hp => (hs hp).2)⟩
    have : IsOpenImmersion (a ≫ x i) := by rw [e1]; exact hz
    refine ⟨_, a, a', IsOpenImmersion.of_comp a (x i), ⟨r, (x i).isOpenEmbedding.injective ?_⟩, e1.trans e2.symm, ?_⟩
    · rw [← Scheme.Hom.comp_apply, e1, hr]
    · obtain ⟨ρ, hρ⟩ := spMap_surj (R' := T) a
      have h := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g _ J b S s' t _ T ρ (x i) (v i) (hv i)
      rw [hρ] at h
      refine uniq T _ _ _ ?_ (tr i T a _ h) (tr i' T a' _ (by rw [e2, ← e1]; exact h))
      rw [Category.assoc, Category.assoc, hy, hy, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ s') (e1.trans e2.symm)
  have hfs : f ≫ Y.s = s' := hom_ext_loc fun p => ⟨_, x p, hx p, hp p, by rw [← Category.assoc, hf, hy]⟩
  refine ⟨f, ⟨hfs, ?_⟩, fun f' hf' => hom_ext_loc fun p => ⟨_, x p, hx p, hp p, ?_⟩⟩
  · obtain ⟨u', hu'⟩ := tObj_pull o g _ J b _ _ Y.s s' f u hfs
    have := tMap_comp (tMap_of_loc hL.globalFns t u'
      (fun p => ⟨_, x p, tx p, hx p, hp p, htx p, tMap_cancel hu' (by rw [hf]; exact hty p)⟩)
      (fun t T _ z => tObj_pull o g _ J b _ _ s' _ z t rfl)
      (fun t T _ z w φ φ' hz h h' => haveI := hred T z hz
        isTM_unique hL hL2 hn.two_le hd ho t T z _ rfl w φ φ' h h')) hu'
    rwa [Category.id_comp] at this
  · rw [hf]
    exact uniq _ _ _ (v p) (by rw [Category.assoc, hf'.1, hy])
      ((hasTh_iff_of_tmap o g _ J b _ _ u _ _ t f' _ (x p) (v p) hf'.2).1 (hv p)) (hy' p)

end GlobalTheory.FamRep
end
