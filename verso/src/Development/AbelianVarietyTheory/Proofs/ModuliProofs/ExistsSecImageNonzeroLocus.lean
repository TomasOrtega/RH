import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

noncomputable section

namespace GlobalTheory.FiniteAmple

open Polynomial CategoryTheory

section Algebra

variable {A B A' B' : Type} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']

def FinFree (φ : A →+* B) : Prop :=
  φ.Finite ∧ (letI := φ.toAlgebra; Module.Free A B)

def revChar (φ : A →+* B) (h : FinFree φ) (b : B) : A[X] :=
  letI := φ.toAlgebra
  haveI : Module.Finite A B := h.1
  haveI : Module.Free A B := h.2
  (Algebra.lmul A B b).charpoly.reverse

/- English proof (translation)
Set `` to `φ.toAlgebra`. Establish `: Module.Finite A B` using `h.1`. Establish `: Module.Free A B` using `h.2`. Set `e` to `Module.Free.chooseBasis A B`. Establish `h₁ : Algebra.lmul A B (φ u * b) = u • Algebra.lmul A B b`.

Rewrite using `[← map_smul, Algebra.smul_def]`. Both sides reduce to the same expression. Simplify using `only [revChar]`. Rewrite using `[h₁, ← LinearMap.charpoly_toMatrix _ e, ← LinearMap.charpoly_toMatrix _ e, Matrix.reverse_charpoly, Matrix.reverse_charpoly, map_smul, mul_comm, ← comp_C_mul_X_coeff]`. Generalize the expression as in `LinearMap.toMatrix e e (Algebra.lmul A B b) = M`.

Use `congr 1`. Rewrite using `[Matrix.charpolyRev, Matrix.charpolyRev, ← coe_compRingHom_apply, RingHom.map_det]`. Use `congr 1`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hij : i = j <;> simp [hij] <;> ring`.
-/
theorem coeff_revChar_mul (φ : A →+* B) (h : FinFree φ) (u : A) (b : B) (k : ℕ) :
    (revChar φ h (φ u * b)).coeff k = u ^ k * (revChar φ h b).coeff k := by
  classical
  let := φ.toAlgebra
  have : Module.Finite A B := h.1
  have : Module.Free A B := h.2
  let e := Module.Free.chooseBasis A B
  have h₁ : Algebra.lmul A B (φ u * b) = u • Algebra.lmul A B b := by
    rw [← map_smul, Algebra.smul_def]; rfl
  simp only [revChar]
  rw [h₁, ← LinearMap.charpoly_toMatrix _ e, ← LinearMap.charpoly_toMatrix _ e, Matrix.reverse_charpoly,
    Matrix.reverse_charpoly, map_smul, mul_comm, ← comp_C_mul_X_coeff]
  generalize LinearMap.toMatrix e e (Algebra.lmul A B b) = M
  congr 1
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← coe_compRingHom_apply, RingHom.map_det]
  congr 1
  refine Matrix.ext fun i j => ?_
  by_cases hij : i = j <;> simp [hij] <;> ring

/- English proof (translation)
Set `` to `φ.toAlgebra`. Establish `: Module.Finite A B` using `h.1`. Establish `: Module.Free A B` using `h.2`. Establish `: Nontrivial A` using `p.nontrivial`. Use `(PrimeSpectrum.mem_image_comap_basicOpen b p).trans ?_` and prove the remaining obligations.

Rewrite using `[isNilpotent_tensor_residueField_iff]`. Express the relevant statement in the definitionally equal form `_ ↔ ∃ k, 1 ≤ k ∧ (Algebra.lmul A B b).charpoly.reverse.coeff k ∉ p.asIdeal`. Simplify using `only [coeff_reverse, LinearMap.charpoly_natDegree, not_forall]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, hi, H⟩`.

Use `⟨Module.finrank A B - i, by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[revAt_le (by omega), Nat.sub_sub_self hi.le]` and apply the resulting hypothesis. Introduce and unpack `⟨k, hk, H⟩`. Distinguish the cases in `hle : k ≤ Module.finrank A B`. Rewrite `H` using `[revAt_le hle]`.

Conclude with `⟨_, by omega, H⟩`. Rewrite `H` using `[revAt_eq_self_of_lt (not_le.1 hle), coeff_eq_zero_of_natDegree_lt (by rw [LinearMap.charpoly_natDegree]; exact not_le.1 hle)]`. Conclude with `(H (zero_mem _)).elim`.
-/
theorem mem_image_basicOpen_iff (φ : A →+* B) (h : FinFree φ) (b : B) (p : PrimeSpectrum A) :
    p ∈ PrimeSpectrum.comap φ '' PrimeSpectrum.basicOpen b ↔
      ∃ k, 1 ≤ k ∧ (revChar φ h b).coeff k ∉ p.asIdeal := by
  let := φ.toAlgebra
  have : Module.Finite A B := h.1
  have : Module.Free A B := h.2
  have : Nontrivial A := p.nontrivial
  refine (PrimeSpectrum.mem_image_comap_basicOpen b p).trans ?_
  rw [isNilpotent_tensor_residueField_iff]
  change _ ↔ ∃ k, 1 ≤ k ∧ (Algebra.lmul A B b).charpoly.reverse.coeff k ∉ p.asIdeal
  simp only [coeff_reverse, LinearMap.charpoly_natDegree, not_forall]
  constructor
  · rintro ⟨i, hi, H⟩
    refine ⟨Module.finrank A B - i, by omega, ?_⟩
    rwa [revAt_le (by omega), Nat.sub_sub_self hi.le]
  · rintro ⟨k, hk, H⟩
    by_cases hle : k ≤ Module.finrank A B
    · rw [revAt_le hle] at H
      exact ⟨_, by omega, H⟩
    · rw [revAt_eq_self_of_lt (not_le.1 hle), coeff_eq_zero_of_natDegree_lt
        (by rw [LinearMap.charpoly_natDegree]; exact not_le.1 hle)] at H
      exact (H (zero_mem _)).elim

/- English proof (translation)
Use `algebraize [φ, α, β, φ', φ'.comp α]`. Establish `: IsScalarTower A B B'` using `IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom H.w).symm`. Establish `P : Algebra.IsPushout A B A' B'` using `CommRingCat.isPushout_iff_isPushout.1 H`. Use `haveI : Module.Finite A B := h.1`. Use `haveI : Module.Free A B := h.2`.

Establish `hb : IsBaseChange A' (IsScalarTower.toAlgHom A B B').toLinearMap` using `P.symm.out`. Use `⟨⟨Module.Finite.equiv hb.equiv, hb.free⟩, fun h' b => ?_⟩` and prove the remaining obligations. Use `haveI : Module.Finite A' B' := h'.1`. Use `haveI : Module.Free A' B' := h'.2`. Establish `e : (Algebra.lmul A' B' (β b)).charpoly = (Algebra.lmul A B b).charpoly.map α`.

Rewrite using `[show α = algebraMap A A' from rfl, ← LinearMap.charpoly_baseChange, ← hb.equiv.charpoly_conj]`. Use `congr 1`. Use extensionality with `y`. Take `⟨t, rfl⟩` from `hb.equiv.surjective y`. Simplify using `only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]`.

Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r x => simp [IsBaseChange.equiv_tmul]`. Both sides reduce to the same expression. Consider the case `add s t hs ht => simp only [map_add, hs, ht]`.

Simplify using `only [revChar]`. Rewrite using `[e, reverse, reverse, (LinearMap.charpoly_monic _).natDegree_map, reflect_map]`.
-/
theorem finFree_revChar_of_isPushout {φ : A →+* B} {α : A →+* A'} {β : B →+* B'} {φ' : A' →+* B'}
    (H : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ'))
    (h : FinFree φ) : FinFree φ' ∧ ∀ [Nontrivial A'] (h' : FinFree φ') (b : B),
      revChar φ' h' (β b) = (revChar φ h b).map α := by
  algebraize [φ, α, β, φ', φ'.comp α]
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom H.w).symm
  have P : Algebra.IsPushout A B A' B' := CommRingCat.isPushout_iff_isPushout.1 H
  haveI : Module.Finite A B := h.1
  haveI : Module.Free A B := h.2
  have hb : IsBaseChange A' (IsScalarTower.toAlgHom A B B').toLinearMap := P.symm.out
  refine ⟨⟨Module.Finite.equiv hb.equiv, hb.free⟩, fun h' b => ?_⟩
  haveI : Module.Finite A' B' := h'.1
  haveI : Module.Free A' B' := h'.2
  have e : (Algebra.lmul A' B' (β b)).charpoly = (Algebra.lmul A B b).charpoly.map α := by
    rw [show α = algebraMap A A' from rfl, ← LinearMap.charpoly_baseChange, ← hb.equiv.charpoly_conj]
    congr 1
    ext y
    obtain ⟨t, rfl⟩ := hb.equiv.surjective y
    simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r x => simp [IsBaseChange.equiv_tmul]; rfl
    | add s t hs ht => simp only [map_add, hs, ht]
  simp only [revChar]
  rw [e, reverse, reverse, (LinearMap.charpoly_monic _).natDegree_map, reflect_map]

/- English proof (translation)
Use `algebraize [φ]`. Establish `: Module.FinitePresentation A B` using `Module.finitePresentation_of_finite A B`. Establish `: Module.Free (Localization p.asIdeal.primeCompl) (LocalizedModule p.asIdeal.primeCompl B)` using `Module.free_of_flat_of_isLocalRing`. Take `⟨r, hr, hfree, -⟩` from `Module.FinitePresentation.exists_free_localizedModule_powers p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl B) (Localization p.asIdeal.primeCompl)`. Use `⟨r, hr, ?_⟩` and prove the remaining obligations.

Introduce `A' B' _ _ α β φ' H hu`. Use `algebraize [α, β, φ', φ'.comp α]`. Establish `: IsScalarTower A B B'` using `IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom H.w).symm`. Establish `P : Algebra.IsPushout A B A' B'` using `CommRingCat.isPushout_iff_isPushout.1 H`. Establish `hb : IsBaseChange A' (IsScalarTower.toAlgHom A B B').toLinearMap` using `P.symm.out`.

Use `⟨Module.Finite.equiv hb.equiv, ?_⟩` and prove the remaining obligations. Use `letI : Algebra (Localization.Away r) A' := (IsLocalization.Away.lift r (g := α) hu).toAlgebra`. Establish `: IsScalarTower A (Localization.Away r) A'` using `IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq r hu x).symm`. Establish `h₁ : Module.Free (Localization.Away r) (TensorProduct A (Localization.Away r) B)` using `Module.Free.of_equiv (IsLocalizedModule.isBaseChange (.powers r) (Localization.Away r) (LocalizedModule.mkLinearMap (.powers r) B)).equiv.symm`. Conclude with `Module.Free.of_equiv ((TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.Away r) A' A' B).trans hb.equiv)`.
-/
theorem exists_finFree_away [IsNoetherianRing A] {φ : A →+* B} (hf : φ.Finite) (hfl : φ.Flat) (p : PrimeSpectrum A) :
    ∃ r ∉ p.asIdeal, ∀ {A' B' : Type} [CommRing A'] [CommRing B'] {α : A →+* A'} {β : B →+* B'} {φ' : A' →+* B'},
      IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ') →
      IsUnit (α r) → FinFree φ' := by
  algebraize [φ]
  have : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  have : Module.Free (Localization p.asIdeal.primeCompl) (LocalizedModule p.asIdeal.primeCompl B) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl B) (Localization p.asIdeal.primeCompl)
  refine ⟨r, hr, ?_⟩
  intro A' B' _ _ α β φ' H hu
  algebraize [α, β, φ', φ'.comp α]
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom H.w).symm
  have P : Algebra.IsPushout A B A' B' := CommRingCat.isPushout_iff_isPushout.1 H
  have hb : IsBaseChange A' (IsScalarTower.toAlgHom A B B').toLinearMap := P.symm.out
  refine ⟨Module.Finite.equiv hb.equiv, ?_⟩
  letI : Algebra (Localization.Away r) A' := (IsLocalization.Away.lift r (g := α) hu).toAlgebra
  have : IsScalarTower A (Localization.Away r) A' :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq r hu x).symm
  have h₁ : Module.Free (Localization.Away r) (TensorProduct A (Localization.Away r) B) :=
    Module.Free.of_equiv (IsLocalizedModule.isBaseChange (.powers r) (Localization.Away r)
      (LocalizedModule.mkLinearMap (.powers r) B)).equiv.symm
  exact Module.Free.of_equiv
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.Away r) A' A' B).trans hb.equiv)

end Algebra

section Geometry

open AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LBGerm

variable {X Y : Scheme.{0}} (f : Y ⟶ X)

/- English proof (translation)
Establish `H : IsPullback (𝟙 Y) f f (𝟙 X)` using `IsPullback.of_horiz_isIso ⟨by simp⟩`. Establish `e : f ⁻¹ᵁ W = 𝟙 Y ⁻¹ᵁ (f ⁻¹ᵁ V) ⊓ f ⁻¹ᵁ W` using `(inf_eq_right.2 fun _ hy => h hy).symm`. Establish `po` using `(isIso_pushoutSection_iff H (US := V) (UT := W) (UX := f ⁻¹ᵁ V) h le_rfl e).1 (isIso_pushoutSection_of_isAffineOpen H _ _ _ hV hW (hV.preimage f))`. Rewrite `po` using `[← Scheme.Hom.app_eq_appLE, ← Scheme.Hom.app_eq_appLE]`. Apply the tactic sequence `convert po using 1 <;> exact (Category.id_comp _).symm`.
-/
theorem isPushout_app [IsAffineHom f] {V W : X.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : W ≤ V) :
    IsPushout (f.app V) (X.presheaf.map (homOfLE h).op)
      (Y.presheaf.map (homOfLE (show f ⁻¹ᵁ W ≤ f ⁻¹ᵁ V from fun _ hy => h hy)).op) (f.app W) := by
  have H : IsPullback (𝟙 Y) f f (𝟙 X) := IsPullback.of_horiz_isIso ⟨by simp⟩
  have e : f ⁻¹ᵁ W = 𝟙 Y ⁻¹ᵁ (f ⁻¹ᵁ V) ⊓ f ⁻¹ᵁ W := (inf_eq_right.2 fun _ hy => h hy).symm
  have po := (isIso_pushoutSection_iff H (US := V) (UT := W) (UX := f ⁻¹ᵁ V) h le_rfl e).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ hV hW (hV.preimage f))
  rw [← Scheme.Hom.app_eq_appLE, ← Scheme.Hom.app_eq_appLE] at po
  convert po using 1 <;> exact (Category.id_comp _).symm

/- English proof (translation)
Take `⟨V, hV, hxV, hle⟩` from `exists_isAffineOpen_mem_and_subset hx`. Establish `: IsNoetherianRing Γ(X, V)` using `IsLocallyNoetherian.component_noetherian ⟨V, hV⟩`. Establish `hfl : (f.app V).hom.Flat`. Rewrite using `[Scheme.Hom.app_eq_appLE]`. Conclude with `f.flat_appLE hV (hV.preimage f) _`.

Take `⟨r, hr, H⟩` from `exists_finFree_away (f.finite_app V hV) hfl (hV.primeIdealOf ⟨x, hxV⟩)`. Use `⟨X.basicOpen r, hV.basicOpen r, ?_, (X.basicOpen_le r).trans hle, H (isPushout_app f hV (hV.basicOpen r) (X.basicOpen_le r)) (X.toRingedSpace.isUnit_res_basicOpen r)⟩` and prove the remaining obligations. Establish `e` using `hV.fromSpec_primeIdealOf ⟨x, hxV⟩`. Establish `h₁ : hV.primeIdealOf ⟨x, hxV⟩ ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen r`. Rewrite using `[hV.fromSpec_preimage_basicOpen]`.

Conclude with `hr`. Conclude with `(congrArg (· ∈ X.basicOpen r) e).mp h₁`.
-/
theorem exists_finFree_app [IsFinite f] [Flat f] [IsLocallyNoetherian X] {x : X} {U : X.Opens} (hx : x ∈ U) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ U ∧ FinFree (f.app V).hom := by
  obtain ⟨V, hV, hxV, hle⟩ := exists_isAffineOpen_mem_and_subset hx
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hfl : (f.app V).hom.Flat := by
    rw [Scheme.Hom.app_eq_appLE]
    exact f.flat_appLE hV (hV.preimage f) _
  obtain ⟨r, hr, H⟩ := exists_finFree_away (f.finite_app V hV) hfl (hV.primeIdealOf ⟨x, hxV⟩)
  refine ⟨X.basicOpen r, hV.basicOpen r, ?_, (X.basicOpen_le r).trans hle,
    H (isPushout_app f hV (hV.basicOpen r) (X.basicOpen_le r)) (X.toRingedSpace.isUnit_res_basicOpen r)⟩
  have e := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  have h₁ : hV.primeIdealOf ⟨x, hxV⟩ ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen r := by
    rw [hV.fromSpec_preimage_basicOpen]
    exact hr
  exact (congrArg (· ∈ X.basicOpen r) e).mp h₁

/- English proof (translation)
Establish `hV'` using `hV.preimage f`. Establish `sq` using `hV.SpecMap_appLE_fromSpec f hV' le_rfl`. Rewrite `sq` using `[← Scheme.Hom.app_eq_appLE]`. Establish `pt : ∀ q : PrimeSpectrum Γ(Y, f ⁻¹ᵁ V), hV.fromSpec (PrimeSpectrum.comap (f.app V).hom q) = f (hV'.fromSpec q)` using `fun q => congr($(sq) q)`. Take `⟨p, rfl⟩ : x ∈ Set.range hV.fromSpec` from `by rwa [hV.range_fromSpec]`.

Establish `e₁ : ∀ c : Γ(X, V), hV.fromSpec p ∈ X.basicOpen c ↔ c ∉ p.asIdeal` using `fun c => by`. Rewrite using `[← Scheme.Hom.mem_preimage, hV.fromSpec_preimage_basicOpen]`. Both sides reduce to the same expression. Establish `e₂ : ∀ q : PrimeSpectrum Γ(Y, f ⁻¹ᵁ V), hV'.fromSpec q ∈ Y.basicOpen b ↔ q ∈ PrimeSpectrum.basicOpen b` using `fun q : Spec Γ(Y, f ⁻¹ᵁ V) => by rw [← Scheme.Hom.mem_preimage, hV'.fromSpec_preimage_basicOpen]; rfl`. Simplify using `only [e₁]`.

Rewrite using `[← mem_image_basicOpen_iff _ h b p]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, e⟩`. Choose the witnesses or unpack the hypotheses as in `⟨q, rfl⟩ : y ∈ Set.range hV'.fromSpec := by`. Rewrite using `[hV'.range_fromSpec]`.

Conclude with `Y.basicOpen_le b hy`. Conclude with `⟨q, (e₂ q).1 hy, hV.fromSpec.isOpenEmbedding.injective ((pt q).trans e)⟩`. Introduce and unpack `⟨q, hq, rfl⟩`. Conclude with `⟨_, (e₂ q).2 hq, (pt q).symm⟩`.
-/
theorem mem_image_basicOpen_app [IsAffineHom f] {V : X.Opens} (hV : IsAffineOpen V) (h : FinFree (f.app V).hom)
    (b : Γ(Y, f ⁻¹ᵁ V)) {x : X} (hx : x ∈ V) :
    (∃ y ∈ Y.basicOpen b, f y = x) ↔ ∃ k, 1 ≤ k ∧ x ∈ X.basicOpen ((revChar _ h b).coeff k) := by
  have hV' := hV.preimage f
  have sq := hV.SpecMap_appLE_fromSpec f hV' le_rfl
  rw [← Scheme.Hom.app_eq_appLE] at sq
  have pt : ∀ q : PrimeSpectrum Γ(Y, f ⁻¹ᵁ V),
      hV.fromSpec (PrimeSpectrum.comap (f.app V).hom q) = f (hV'.fromSpec q) := fun q => congr($(sq) q)
  obtain ⟨p, rfl⟩ : x ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
  have e₁ : ∀ c : Γ(X, V), hV.fromSpec p ∈ X.basicOpen c ↔ c ∉ p.asIdeal := fun c => by
    rw [← Scheme.Hom.mem_preimage, hV.fromSpec_preimage_basicOpen]; rfl
  have e₂ : ∀ q : PrimeSpectrum Γ(Y, f ⁻¹ᵁ V), hV'.fromSpec q ∈ Y.basicOpen b ↔ q ∈ PrimeSpectrum.basicOpen b :=
    fun q : Spec Γ(Y, f ⁻¹ᵁ V) => by rw [← Scheme.Hom.mem_preimage, hV'.fromSpec_preimage_basicOpen]; rfl
  simp only [e₁]
  rw [← mem_image_basicOpen_iff _ h b p]
  constructor
  · rintro ⟨y, hy, e⟩
    obtain ⟨q, rfl⟩ : y ∈ Set.range hV'.fromSpec := by
      rw [hV'.range_fromSpec]; exact Y.basicOpen_le b hy
    exact ⟨q, (e₂ q).1 hy, hV.fromSpec.isOpenEmbedding.injective ((pt q).trans e)⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨_, (e₂ q).2 hq, (pt q).symm⟩

/- English proof (translation)
Set `α : Type` to `{p : X.Opens × M.ι // IsAffineOpen p.1 ∧ p.1 ≤ M.U p.2 ∧ FinFree (f.app p.1).hom}`. Establish `cov : ∀ x : X, ∃ a : α, x ∈ a.1.1` using `fun x => by`. Take `⟨i, hi⟩` from `exists_chart hM x`. Take `⟨V, hV, hx, hle, hF⟩` from `exists_finFree_app f hi`. Conclude with `⟨⟨(V, i), hV, hle, hF⟩, hx⟩`.

Establish `le : ∀ a : α, f ⁻¹ᵁ a.1.1 ≤ (M.pull f).U fun _ => a.1.2` using `fun a y hy => mem_pull.2 (a.2.2.1 hy)`. Set `τ : ∀ a : α, Γ(Y, f ⁻¹ᵁ a.1.1)` to `fun a => resG Y (le a) (t.f fun _ => a.1.2)`. Set `c : ∀ (k : ℕ) (a : α), Γ(X, a.1.1)` to `fun k a => (revChar _ a.2.2.2 (τ a)).coeff k`. Establish `key : ∀ k (x : X) (a b : α), x ∈ a.1.1 → x ∈ b.1.1 → gs (𝟙 X) x _ (c k a) = (gm (𝟙 X) x (M.U a.1.2 ⊓ M.U b.1.2) (M.g a.1.2 b.1.2)).val ^ k * gs (𝟙 X) x _ (c k b)`. Introduce `k x a b ha hb`.

Take `⟨W, hW, hx, hle⟩` from `exists_isAffineOpen_mem_and_subset (U := a.1.1 ⊓ b.1.1) (x := x) ⟨ha, hb⟩`. Establish `hle : W ≤ a.1.1 ⊓ b.1.1` using `hle`. Establish `la : W ≤ a.1.1` using `hle.trans inf_le_left`. Establish `lb : W ≤ b.1.1` using `hle.trans inf_le_right`. Establish `lg : W ≤ M.U a.1.2 ⊓ M.U b.1.2` using `le_inf (la.trans a.2.2.1) (lb.trans b.2.2.1)`.

Establish `: Nonempty W` using `⟨⟨x, hx⟩⟩`. Take `⟨hF, ea⟩` from `finFree_revChar_of_isPushout (isPushout_app f a.2.1 hW la) a.2.2.2`. Establish `ea` using `congrArg (coeff · k) (ea hF (τ a))`. Establish `eb` using `congrArg (coeff · k) ((finFree_revChar_of_isPushout (isPushout_app f b.2.1 hW lb) b.2.2.2).2 hF (τ b))`. Simplify using `only [coeff_map] at ea eb`.

Establish `eτ : resG Y (show f ⁻¹ᵁ W ≤ f ⁻¹ᵁ a.1.1 from fun _ hy => la hy) (τ a) = (f.app W).hom (resG X lg (M.g a.1.2 b.1.2).val) * resG Y (show f ⁻¹ᵁ W ≤ f ⁻¹ᵁ b.1.1 from fun _ hy => lb hy) (τ b)` using `fn_ext fun y hy => by`. Establish `hy' : (𝟙 Y ≫ f) y ∈ W` using `hy`. Rewrite using `[gs_mul (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy, gs_res (𝟙 Y) y (le a) (la hy), gs_res (𝟙 Y) y (le b) (lb hy), gs_pull (𝟙 Y) f y W hy, gs_res (𝟙 Y ≫ f) y _ hy', gs_unit (𝟙 Y ≫ f) y _ (lg hy'), ← gm_pull_g M f (𝟙 Y) y (fun _ => a.1.2) (fun _ => b.1.2) (le a (la hy)) …`. Conclude with `gs_compat t (𝟙 Y) y (le a (la hy)) (le b (lb hy))`. Establish `e : resG X la (c k a) = resG X lg (M.g a.1.2 b.1.2).val ^ k * resG X lb (c k b)` using `ea.symm.trans ((congrArg (fun z => (revChar _ hF z).coeff k) eτ).trans ((coeff_revChar_mul _ hF _ _ k).trans (congrArg (_ * ·) eb)))`.

Establish `e'` using `congrArg (gs (𝟙 X) x W) e`. Rewrite `e'` using `[gs_mul _ x _ hx, gs_pow _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx, gs_unit _ x _ (lg hx)]`. Then use the resulting hypothesis. Use `choose u hu using fun k => exists_sec_of_refinement (isLB_lbPow hM k) (fun a : α => a.1.1) (fun a _ => a.1.2) (fun a x hx => mem_powChart.2 (a.2.2.1 hx)) cov (c k) fun x a b ha hb => by`. Rewrite using `[gm_lbPow_g k (𝟙 X) x _ _ (mem_powChart.2 (a.2.2.1 ha)) (mem_powChart.2 (b.2.2.1 hb)), Units.val_pow_eq_pow_val]`. Conclude with `key k x a b ha hb`.

Use `⟨u, fun x => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `cov x`. Establish `loc : ∀ k, x ∈ nonzeroLocus (u k) ↔ x ∈ X.basicOpen (c k a)` using `fun k => by`. Establish `hJ : x ∈ (lbPow M k).U fun _ => a.1.2` using `mem_powChart.2 (a.2.2.1 ha)`. Rewrite using `[mem_nonzeroLocus_iff_isUnit (u k) hJ, hu k x _ a hJ ha, Units.isUnit_units_mul]`.

Conclude with `isUnit_gs_iff (𝟙 X) x _ ha _`. Simplify using `only [loc]`. Rewrite using `[← mem_image_basicOpen_app f a.2.1 a.2.2.2 (τ a) ha]`. Use `exists_congr fun y => and_congr_left fun e => ?_` and prove the remaining obligations. Establish `hy : y ∈ f ⁻¹ᵁ a.1.1` using `show f y ∈ a.1.1 from e ▸ ha`.

Rewrite using `[mem_nonzeroLocus_iff_isUnit t (le a hy), ← gs_res (𝟙 Y) y (le a) hy]`. Conclude with `isUnit_gs_iff (𝟙 Y) y _ hy _`.
-/
theorem exists_sec_image_nonzeroLocus [IsFinite f] [Flat f] [IsLocallyNoetherian X] {M : LB X} (hM : M.IsLB)
    (t : (M.pull f).Sec) : ∃ u : ∀ k, (lbPow M k).Sec, ∀ x : X,
      (∃ y ∈ nonzeroLocus t, f y = x) ↔ ∃ k, 1 ≤ k ∧ x ∈ nonzeroLocus (u k) := by
  let α : Type := {p : X.Opens × M.ι // IsAffineOpen p.1 ∧ p.1 ≤ M.U p.2 ∧ FinFree (f.app p.1).hom}
  have cov : ∀ x : X, ∃ a : α, x ∈ a.1.1 := fun x => by
    obtain ⟨i, hi⟩ := exists_chart hM x
    obtain ⟨V, hV, hx, hle, hF⟩ := exists_finFree_app f hi
    exact ⟨⟨(V, i), hV, hle, hF⟩, hx⟩
  have le : ∀ a : α, f ⁻¹ᵁ a.1.1 ≤ (M.pull f).U fun _ => a.1.2 := fun a y hy => mem_pull.2 (a.2.2.1 hy)
  let τ : ∀ a : α, Γ(Y, f ⁻¹ᵁ a.1.1) := fun a => resG Y (le a) (t.f fun _ => a.1.2)
  let c : ∀ (k : ℕ) (a : α), Γ(X, a.1.1) := fun k a => (revChar _ a.2.2.2 (τ a)).coeff k
  have key : ∀ k (x : X) (a b : α), x ∈ a.1.1 → x ∈ b.1.1 → gs (𝟙 X) x _ (c k a) =
      (gm (𝟙 X) x (M.U a.1.2 ⊓ M.U b.1.2) (M.g a.1.2 b.1.2)).val ^ k * gs (𝟙 X) x _ (c k b) := by
    intro k x a b ha hb
    obtain ⟨W, hW, hx, hle⟩ := exists_isAffineOpen_mem_and_subset (U := a.1.1 ⊓ b.1.1) (x := x) ⟨ha, hb⟩
    have hle : W ≤ a.1.1 ⊓ b.1.1 := hle
    have la : W ≤ a.1.1 := hle.trans inf_le_left
    have lb : W ≤ b.1.1 := hle.trans inf_le_right
    have lg : W ≤ M.U a.1.2 ⊓ M.U b.1.2 := le_inf (la.trans a.2.2.1) (lb.trans b.2.2.1)
    have : Nonempty W := ⟨⟨x, hx⟩⟩
    obtain ⟨hF, ea⟩ := finFree_revChar_of_isPushout (isPushout_app f a.2.1 hW la) a.2.2.2
    have ea := congrArg (coeff · k) (ea hF (τ a))
    have eb := congrArg (coeff · k)
      ((finFree_revChar_of_isPushout (isPushout_app f b.2.1 hW lb) b.2.2.2).2 hF (τ b))
    simp only [coeff_map] at ea eb
    have eτ : resG Y (show f ⁻¹ᵁ W ≤ f ⁻¹ᵁ a.1.1 from fun _ hy => la hy) (τ a) =
        (f.app W).hom (resG X lg (M.g a.1.2 b.1.2).val) *
          resG Y (show f ⁻¹ᵁ W ≤ f ⁻¹ᵁ b.1.1 from fun _ hy => lb hy) (τ b) := fn_ext fun y hy => by
      have hy' : (𝟙 Y ≫ f) y ∈ W := hy
      rw [gs_mul (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy, gs_res (𝟙 Y) y (le a) (la hy),
        gs_res (𝟙 Y) y (le b) (lb hy), gs_pull (𝟙 Y) f y W hy, gs_res (𝟙 Y ≫ f) y _ hy',
        gs_unit (𝟙 Y ≫ f) y _ (lg hy'),
        ← gm_pull_g M f (𝟙 Y) y (fun _ => a.1.2) (fun _ => b.1.2) (le a (la hy)) (le b (lb hy))]
      exact gs_compat t (𝟙 Y) y (le a (la hy)) (le b (lb hy))
    have e : resG X la (c k a) = resG X lg (M.g a.1.2 b.1.2).val ^ k * resG X lb (c k b) :=
      ea.symm.trans ((congrArg (fun z => (revChar _ hF z).coeff k) eτ).trans
        ((coeff_revChar_mul _ hF _ _ k).trans (congrArg (_ * ·) eb)))
    have e' := congrArg (gs (𝟙 X) x W) e
    rwa [gs_mul _ x _ hx, gs_pow _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx,
      gs_unit _ x _ (lg hx)] at e'
  choose u hu using fun k => exists_sec_of_refinement (isLB_lbPow hM k) (fun a : α => a.1.1)
    (fun a _ => a.1.2) (fun a x hx => mem_powChart.2 (a.2.2.1 hx)) cov (c k) fun x a b ha hb => by
      rw [gm_lbPow_g k (𝟙 X) x _ _ (mem_powChart.2 (a.2.2.1 ha)) (mem_powChart.2 (b.2.2.1 hb)),
        Units.val_pow_eq_pow_val]
      exact key k x a b ha hb
  refine ⟨u, fun x => ?_⟩
  obtain ⟨a, ha⟩ := cov x
  have loc : ∀ k, x ∈ nonzeroLocus (u k) ↔ x ∈ X.basicOpen (c k a) := fun k => by
    have hJ : x ∈ (lbPow M k).U fun _ => a.1.2 := mem_powChart.2 (a.2.2.1 ha)
    rw [mem_nonzeroLocus_iff_isUnit (u k) hJ, hu k x _ a hJ ha, Units.isUnit_units_mul]
    exact isUnit_gs_iff (𝟙 X) x _ ha _
  simp only [loc]
  rw [← mem_image_basicOpen_app f a.2.1 a.2.2.2 (τ a) ha]
  refine exists_congr fun y => and_congr_left fun e => ?_
  have hy : y ∈ f ⁻¹ᵁ a.1.1 := show f y ∈ a.1.1 from e ▸ ha
  rw [mem_nonzeroLocus_iff_isUnit t (le a hy), ← gs_res (𝟙 Y) y (le a) hy]
  exact isUnit_gs_iff (𝟙 Y) y _ hy _

/- English proof (translation)
Use `h.compactSpace` as an intermediate fact. Establish `: CompactSpace X` using `f.surjective.compactSpace f.continuous`. Use `isAmpleLB_of_forall_le hL fun x U hx => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `f.surjective x`. Take `⟨n, hn, s, hs, hle, -⟩` from `h.exists_affine_le (x := y) (U := f ⁻¹ᵁ U) hx`.

Take `⟨t, ht⟩` from `exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull (isLB_lbPow hL n) f) (isLB_lbPow h.isLB n) (lbIso_lbPow_pull hL f n).symm s`. Take `⟨u, hu⟩` from `exists_sec_image_nonzeroLocus f (isLB_lbPow hL n) t`. Take `⟨k, hk, hy⟩` from `(hu (f y)).1 ⟨y, ht.ge hs, rfl⟩`. Establish `e` using `nonzeroLocus_secOfPowPow (u k)`. Use `⟨n * k, Nat.mul_pos hn hk, secOfPowPow (u k), e.ge hy, fun z hz => ?_⟩` and prove the remaining obligations.

Take `⟨w, hw, rfl⟩` from `(hu z).2 ⟨k, hk, e.le hz⟩`. Conclude with `hle (ht.le hw)`.
-/
theorem isAmpleLB_of_pull [IsFinite f] [Flat f] [Surjective f] [IsLocallyNoetherian X] {L : LB X} (hL : L.IsLB)
    (h : IsAmpleLB (L.pull f)) : IsAmpleLB L := by
  have := h.compactSpace
  have : CompactSpace X := f.surjective.compactSpace f.continuous
  refine isAmpleLB_of_forall_le hL fun x U hx => ?_
  obtain ⟨y, rfl⟩ := f.surjective x
  obtain ⟨n, hn, s, hs, hle, -⟩ := h.exists_affine_le (x := y) (U := f ⁻¹ᵁ U) hx
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull (isLB_lbPow hL n) f) (isLB_lbPow h.isLB n)
    (lbIso_lbPow_pull hL f n).symm s
  obtain ⟨u, hu⟩ := exists_sec_image_nonzeroLocus f (isLB_lbPow hL n) t
  obtain ⟨k, hk, hy⟩ := (hu (f y)).1 ⟨y, ht.ge hs, rfl⟩
  have e := nonzeroLocus_secOfPowPow (u k)
  refine ⟨n * k, Nat.mul_pos hn hk, secOfPowPow (u k), e.ge hy, fun z hz => ?_⟩
  obtain ⟨w, hw, rfl⟩ := (hu z).2 ⟨k, hk, e.le hz⟩
  exact hle (ht.le hw)

/- English proof (translation)
The claim follows from `LBIso.chartPull (chartPullLinComb L f (fun _ : PUnit => g) (fun _ => g ≫ f) _ (𝟙 Z) fun _ => by simp) (chartPullLinComb L f' (fun _ : PUnit => g') (fun _ => g ≫ f) _ (𝟙 Z) fun _ => by simp [e]) (lbIso_refl (LB.isLB_pull hL _))`.
-/
theorem lbIso_pull_pull {Z Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {g : Z ⟶ Y} {g' : Z ⟶ Y'} {f' : Y' ⟶ X}
    (e : g ≫ f = g' ≫ f') : LBIso ((L.pull f).pull g) ((L.pull f').pull g') :=
  LBIso.chartPull (chartPullLinComb L f (fun _ : PUnit => g) (fun _ => g ≫ f) _ (𝟙 Z) fun _ => by simp)
    (chartPullLinComb L f' (fun _ : PUnit => g') (fun _ => g ≫ f) _ (𝟙 Z) fun _ => by simp [e])
    (lbIso_refl (LB.isLB_pull hL _))

end Geometry

end GlobalTheory.FiniteAmple

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

/- English proof (translation)
Introduce `S _ A B _ _ ψ M n hn hA hB hM hψ`. Use `hA.proper` as an intermediate fact. Use `hB.proper` as an intermediate fact. Establish `: IsLocallyNoetherian B.left` using `LocallyOfFiniteType.isLocallyNoetherian B.hom`. Establish `pre : ∀ U : S.Opens, A.hom ⁻¹ᵁ U = ψ.left ⁻¹ᵁ (B.hom ⁻¹ᵁ U)` using `fun U => by`.

Rewrite using `[← Over.w ψ, Scheme.Hom.comp_preimage]`. Establish `cmp : ∀ V : B.left.Opens, IsAmpleLB ((M.pull ψ.left).pull (ψ.left ⁻¹ᵁ V).ι) ↔ IsAmpleLB ((M.pull V.ι).pull (ψ.left ∣_ V))` using `fun V => isAmpleLB_congr (LB.isLB_pull (LB.isLB_pull hM _) _) (LB.isLB_pull (LB.isLB_pull hM _) _) (FiniteAmple.lbIso_pull_pull _ hM (morphismRestrict_ι ψ.left V).symm)`. Rewrite using `[relAmple_iff_isAmpleLB B hM, relAmple_iff_isAmpleLB B (isLB_lbPow hM n), relAmple_iff_isAmpleLB A (LB.isLB_pull hM _)]`. Use `⟨fun h U hU => ?_, forall₂_congr fun U hU => ?_, fun _ _ h U hU => ?_, fun M' hM' H h => ?_⟩` and prove the remaining obligations. Rewrite using `[pre, cmp]`.

Conclude with `(h U hU).pull_of_isFinite _`. Conclude with `(isAmpleLB_congr (isLB_lbPow (LB.isLB_pull hM _) n) (LB.isLB_pull (isLB_lbPow hM n) _) (lbIso_lbPow_pull hM _ n)).symm.trans (isAmpleLB_pow_iff (LB.isLB_pull hM _) hn)`. Establish `h'` using `h U hU`. Rewrite `h'` using `[pre, cmp]`. Establish `: Surjective (ψ.left ∣_ B.hom ⁻¹ᵁ U)` using `IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› _`.

Conclude with `FiniteAmple.isAmpleLB_of_pull _ (LB.isLB_pull hM _) h'`. Conclude with `relAmple_of_isAmpleLB B hM' fun U hU => (h U hU).of_lbIso (LB.isLB_pull hM' _) (LBIso.chartPull (GlobalTheory.chartPullPull M' _) (GlobalTheory.chartPullPull M _) H.symm)`.
-/
theorem relAmple_finite_pow_iso : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [GrpObj B]
    (ψ : A ⟶ B) (M : LB B.left) (n : ℕ), 0 < n → IsAbelianScheme A → IsAbelianScheme B → M.IsLB →
    IsFinite ψ.left → (Out.RelAmple B M → Out.RelAmple A (M.pull ψ.left)) ∧
      (Out.RelAmple B (lbPow M n) ↔ Out.RelAmple B M) ∧
      (Flat ψ.left → Surjective ψ.left → Out.RelAmple A (M.pull ψ.left) → Out.RelAmple B M) ∧
      ∀ M' : LB B.left, M'.IsLB → LBIso M M' → Out.RelAmple B M → Out.RelAmple B M' := by
  intro S _ A B _ _ ψ M n hn hA hB hM hψ
  have := hA.proper
  have := hB.proper
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have pre : ∀ U : S.Opens, A.hom ⁻¹ᵁ U = ψ.left ⁻¹ᵁ (B.hom ⁻¹ᵁ U) := fun U => by
    rw [← Over.w ψ, Scheme.Hom.comp_preimage]
  have cmp : ∀ V : B.left.Opens, IsAmpleLB ((M.pull ψ.left).pull (ψ.left ⁻¹ᵁ V).ι) ↔
      IsAmpleLB ((M.pull V.ι).pull (ψ.left ∣_ V)) := fun V =>
    isAmpleLB_congr (LB.isLB_pull (LB.isLB_pull hM _) _) (LB.isLB_pull (LB.isLB_pull hM _) _)
      (FiniteAmple.lbIso_pull_pull _ hM (morphismRestrict_ι ψ.left V).symm)
  rw [relAmple_iff_isAmpleLB B hM, relAmple_iff_isAmpleLB B (isLB_lbPow hM n),
    relAmple_iff_isAmpleLB A (LB.isLB_pull hM _)]
  refine ⟨fun h U hU => ?_, forall₂_congr fun U hU => ?_, fun _ _ h U hU => ?_, fun M' hM' H h => ?_⟩
  · rw [pre, cmp]
    exact (h U hU).pull_of_isFinite _
  · exact (isAmpleLB_congr (isLB_lbPow (LB.isLB_pull hM _) n) (LB.isLB_pull (isLB_lbPow hM n) _)
      (lbIso_lbPow_pull hM _ n)).symm.trans (isAmpleLB_pow_iff (LB.isLB_pull hM _) hn)
  · have h' := h U hU
    rw [pre, cmp] at h'
    have : Surjective (ψ.left ∣_ B.hom ⁻¹ᵁ U) := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› _
    exact FiniteAmple.isAmpleLB_of_pull _ (LB.isLB_pull hM _) h'
  · exact relAmple_of_isAmpleLB B hM' fun U hU => (h U hU).of_lbIso (LB.isLB_pull hM' _)
      (LBIso.chartPull (GlobalTheory.chartPullPull M' _) (GlobalTheory.chartPullPull M _) H.symm)

end GlobalTheory
