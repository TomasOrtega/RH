import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarisedModelLocalizationAwayStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelEndomorphismsSpreadOverBasicOpenStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaPointShapePrimitivityNearGenericStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SpreadGeneric

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `(Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm`.
-/
theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    (h : A →+* C) (e : g.comp f = h) : spMap g ≫ spMap f = spMap h := by
  subst e
  exact (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

section Algebra
variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

def Near {R' : Type} [CommRing R'] (io : R →+* R') (χ : R' →+* K) (x : R') : Prop :=
  ∃ (F : R) (_ : F ≠ 0) (φ : R' →+* Localization.Away F) (ψ : Localization.Away F →+* K),
    φ.comp io = algebraMap R _ ∧ ψ.comp (algebraMap R _) = algebraMap R K ∧ ψ.comp φ = χ ∧ IsUnit (φ x)

/- English proof (translation)
Take `⟨F, hF, φ, ψ, h1, h2, h3, -⟩` from `h`. Take `⟨⟨a, ⟨s, n, rfl⟩⟩, ha⟩` from `IsLocalization.surj (Submonoid.powers F) (φ x)`. Simplify using `only at ha`. Establish `hinj` using `IsFractionRing.injective R K`. Establish `hK : ∀ r : R, ψ (algebraMap R _ r) = algebraMap R K r` using `fun r => RingHom.congr_fun h2 r`.

Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Use `congrArg ψ ha` as an intermediate fact. Rewrite `this` using `[map_mul, hK, hK, map_zero, ← RingHom.comp_apply, h3]`. Break down `mul_eq_zero.1 this with h | h` into its components or cases.

Conclude with `hx h`. Conclude with `pow_ne_zero n hF (hinj (h.trans (map_zero _).symm))`. Establish `hFa : F * a ≠ 0` using `mul_ne_zero hF ha0`. Establish `hu : IsUnit (algebraMap R (Localization.Away (F * a)) (F * a))` using `IsLocalization.Away.algebraMap_isUnit (F * a)`. Rewrite `hu` using `[map_mul]`.

Establish `huK : IsUnit (algebraMap R K (F * a))` using `isUnit_iff_ne_zero.2 fun h => hFa (hinj (h.trans (map_zero _).symm))`. Set `ρ : Localization.Away F →+* Localization.Away (F * a)` to `IsLocalization.Away.lift F (isUnit_of_mul_isUnit_left hu)`. Establish `hρ : ρ.comp (algebraMap R _) = algebraMap R _` using `IsLocalization.Away.lift_comp _ _`. Set `ψ' : Localization.Away (F * a) →+* K` to `IsLocalization.Away.lift (F * a) huK`. Establish `hψ' : ψ'.comp (algebraMap R _) = algebraMap R K` using `IsLocalization.Away.lift_comp _ _`.

Establish `hc : ψ'.comp ρ = ψ`. Apply `IsLocalization.ringHom_ext (Submonoid.powers F)` to reduce the goal to its premises. Rewrite using `[RingHom.comp_assoc, hρ, hψ', h2]`. Use `⟨F * a, hFa, ρ.comp φ, ψ', ?_, hψ', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.comp_assoc, h1, hρ]`.

Rewrite using `[← RingHom.comp_assoc, hc, h3]`. Use `congrArg ρ ha` as an intermediate fact. Rewrite `this` using `[map_mul, show ρ (algebraMap R _ a) = algebraMap R _ a from RingHom.congr_fun hρ a]`. Conclude with `isUnit_of_mul_isUnit_left (this ▸ isUnit_of_mul_isUnit_right hu)`.
-/
theorem Near.shrink {R' : Type} [CommRing R'] {io : R →+* R'} {χ : R' →+* K} {y : R'} (h : Near io χ y)
    (x : R') (hx : χ x ≠ 0) : Near io χ x := by
  obtain ⟨F, hF, φ, ψ, h1, h2, h3, -⟩ := h
  obtain ⟨⟨a, ⟨s, n, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers F) (φ x)
  simp only at ha
  have hinj := IsFractionRing.injective R K
  have hK : ∀ r : R, ψ (algebraMap R _ r) = algebraMap R K r := fun r => RingHom.congr_fun h2 r
  have ha0 : a ≠ 0 := by
    rintro rfl
    have := congrArg ψ ha
    rw [map_mul, hK, hK, map_zero, ← RingHom.comp_apply, h3] at this
    rcases mul_eq_zero.1 this with h | h
    · exact hx h
    · exact pow_ne_zero n hF (hinj (h.trans (map_zero _).symm))
  have hFa : F * a ≠ 0 := mul_ne_zero hF ha0
  have hu : IsUnit (algebraMap R (Localization.Away (F * a)) (F * a)) :=
    IsLocalization.Away.algebraMap_isUnit (F * a)
  rw [map_mul] at hu
  have huK : IsUnit (algebraMap R K (F * a)) :=
    isUnit_iff_ne_zero.2 fun h => hFa (hinj (h.trans (map_zero _).symm))
  let ρ : Localization.Away F →+* Localization.Away (F * a) :=
    IsLocalization.Away.lift F (isUnit_of_mul_isUnit_left hu)
  have hρ : ρ.comp (algebraMap R _) = algebraMap R _ := IsLocalization.Away.lift_comp _ _
  let ψ' : Localization.Away (F * a) →+* K := IsLocalization.Away.lift (F * a) huK
  have hψ' : ψ'.comp (algebraMap R _) = algebraMap R K := IsLocalization.Away.lift_comp _ _
  have hc : ψ'.comp ρ = ψ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers F)
    rw [RingHom.comp_assoc, hρ, hψ', h2]
  refine ⟨F * a, hFa, ρ.comp φ, ψ', ?_, hψ', ?_, ?_⟩
  · rw [RingHom.comp_assoc, h1, hρ]
  · rw [← RingHom.comp_assoc, hc, h3]
  · have := congrArg ρ ha
    rw [map_mul, show ρ (algebraMap R _ a) = algebraMap R _ a from RingHom.congr_fun hρ a] at this
    exact isUnit_of_mul_isUnit_left (this ▸ isUnit_of_mul_isUnit_right hu)

omit [IsDomain R] [IsFractionRing R K] in
/- English proof (translation)
Take `⟨F, hF, φ, ψ, h1, h2, h3, h4⟩` from `h`. Establish `hρ : (IsLocalization.Away.lift (S` using `Localization.Away x) x h4).comp (algebraMap R' _) = φ := IsLocalization.Away.lift_comp _ _`. Use `⟨F, hF, IsLocalization.Away.lift x h4, ψ, ?_, h2, ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[← RingHom.comp_assoc, hρ, h1]`. Apply `IsLocalization.ringHom_ext (Submonoid.powers x)` to reduce the goal to its premises.

Rewrite using `[RingHom.comp_assoc, hρ, h3, e]`.
-/
theorem Near.away {R' : Type} [CommRing R'] {io : R →+* R'} {χ : R' →+* K} {x : R'} (h : Near io χ x)
    (χ' : Localization.Away x →+* K) (e : χ'.comp (algebraMap R' _) = χ) :
    Near ((algebraMap R' (Localization.Away x)).comp io) χ' 1 := by
  obtain ⟨F, hF, φ, ψ, h1, h2, h3, h4⟩ := h
  have hρ : (IsLocalization.Away.lift (S := Localization.Away x) x h4).comp (algebraMap R' _) = φ :=
    IsLocalization.Away.lift_comp _ _
  refine ⟨F, hF, IsLocalization.Away.lift x h4, ψ, ?_, h2, ?_, by simp⟩
  · rw [← RingHom.comp_assoc, hρ, h1]
  · apply IsLocalization.ringHom_ext (Submonoid.powers x)
    rw [RingHom.comp_assoc, hρ, h3, e]

omit [IsFractionRing R K] in
/- English proof (translation)
The claim follows from `IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf)`.
-/
theorem isDomain_away {f : R} (hf : f ≠ 0) : IsDomain (Localization.Away f) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf)

/- English proof (translation)
Use `letI := ψ.toAlgebra`. Use `haveI : IsScalarTower R (Localization.Away f) K := IsScalarTower.of_algebraMap_eq' e.symm`. Conclude with `IsFractionRing.isFractionRing_of_isLocalization (Submonoid.powers f) _ K (powers_le_nonZeroDivisors_of_noZeroDivisors hf)`.
-/
theorem isFractionRing_away {f : R} (hf : f ≠ 0) (ψ : Localization.Away f →+* K)
    (e : ψ.comp (algebraMap R _) = algebraMap R K) :
    letI := ψ.toAlgebra
    IsFractionRing (Localization.Away f) K := by
  letI := ψ.toAlgebra
  haveI : IsScalarTower R (Localization.Away f) K := IsScalarTower.of_algebraMap_eq' e.symm
  exact IsFractionRing.isFractionRing_of_isLocalization (Submonoid.powers f) _ K
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)

end Algebra

/- English proof (translation)
Introduce `l1 l2 o _ g N' J b Mat κ w w' _ R K _ _ _ _ _ _ β v t hth hsh hpr`. Take `⟨f, hf, ψ₁, P', φ, e₁, hg, hpb, hL⟩` from `GlobalTheory.T.exists_principallyPolarised_model_localizationAway R K t.pol`. Use `haveI := isDomain_away hf`. Use `letI := ψ₁.toAlgebra`. Use `haveI := isFractionRing_away hf ψ₁ e₁`.

Establish `key : ∀ (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (φ : t.A.left ⟶ P'.A.left), s = spMap (algebraMap (Localization.Away f) K) ≫ spMap ((algebraMap R (Localization.Away f)).comp β) → IsGrpPullback t.A P'.A (spMap ψ₁) φ → LBIso t.L (P'.L.pull φ) → ∃ (f₁ : Localization.Away f) (_ …`. Introduce and unpack `s t φ rfl h1 h2`. Take `⟨f₁, h, t', ψ, h3, h4⟩` from `GlobalTheory.T.thetaLevel_endomorphisms_spread_over_basicOpen l1 l2 o g (N' ^ 2) J b (Localization.Away f) K ((algebraMap R (Localization.Away f)).comp β) t P' φ hg h1 h2`. Conclude with `⟨f₁, h, _, t', ψ, rfl, h3, h4⟩`. Take `⟨f₁, hf₁, s₂, t₂, ψ₂, hs₂, e₂, hm⟩` from `key _ t φ (by`.

Rewrite using `[spMap_comp_eq _ _ _ rfl, spMap_comp_eq _ _ _ rfl, ← RingHom.comp_assoc]`. Conclude with `congrArg (fun r => spMap (RingHom.comp r β)) e₁.symm) hpb hL`. Use `haveI := isDomain_away hf₁`. Use `letI := ψ₂.toAlgebra`. Use `haveI := isFractionRing_away (K := K) hf₁ ψ₂ e₂`.

Set `io : R →+* Localization.Away f₁` to `(algebraMap (Localization.Away f) _).comp (algebraMap R _)`. Establish `hio : ψ₂.comp io = algebraMap R K` using `by rw [← RingHom.comp_assoc, e₂, e₁]`. Establish `hv : (fun a => algebraMap (Localization.Away f₁) K (io (v a))) = fun a => algebraMap R K (v a)`. Use function extensionality and compare the values at `fun a => RingHom.congr_fun hio (v a)`. Take `⟨f₂, hf₂, H⟩` from `GlobalTheory.T.exists_thetaPoint_shape_primitivity_near_generic l1 l2 o g N' J b Mat κ w w' (Localization.Away f₁) K s₂ _ t₂ t (fun a => io (v a)) hm (hv ▸ hth) hsh hpr`.

Establish `n0 : Near (algebraMap R (Localization.Away f)) ψ₁ 1` using `⟨f, hf, RingHom.id _, ψ₁, rfl, e₁, rfl, isUnit_one⟩`. Establish `n1` using `(n0.shrink f₁ fun h => hf₁ (IsFractionRing.injective (Localization.Away f) K (h.trans (map_zero _).symm))).away ψ₂ e₂`. Take `⟨F, hF, ρ, ψ, h1, h2, h3, h4⟩` from `n1.shrink f₂ fun h => hf₂ (IsFractionRing.injective (Localization.Away f₁) K (h.trans (map_zero _).symm))`. Take `⟨t', ht'⟩` from `GlobalTheory.tObj_pull o g (N' ^ 2) J b _ _ s₂ (spMap (algebraMap R (Localization.Away F)) ≫ spMap β) (spMap ρ) t₂ (by`. Rewrite using `[hs₂, spMap_comp_eq _ _ _ rfl, spMap_comp_eq _ _ _ rfl, spMap_comp_eq _ _ _ rfl, ← h1])`.

Take `⟨c1, c2, c3⟩` from `H _ ρ _ t' h4 ht'`. Use `⟨F, hF, t', ψ, h2, ?_, ?_, c2, c3⟩` and prove the remaining obligations. Use `((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g (N' ^ 2) J b _ _ _ _ _ _ t₂ t' t).2 (spMap ρ) (spMap ψ) ht').2 ?_` and prove the remaining obligations. Rewrite using `[spMap_comp_eq _ _ _ h3]`. Conclude with `hm`.

Establish `: (fun a => ρ (io (v a))) = fun a => algebraMap R (Localization.Away F) (v a)`. Use function extensionality and compare the values at `fun a => RingHom.congr_fun h1 (v a)`. Conclude with `this ▸ c1`.
-/
theorem exists_spread : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) Mat κ (w w' : J) [Finite J] (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (t : TObj g (N' ^ 2) J b (spMap (algebraMap R K) ≫ spMap β)), t.HasTh (𝟙 _) (fun a => algebraMap R K (v a)) → t.Shape Mat κ → t.Prim w w' → ∃ (f : R) (_ : f ≠ 0) (t' : TObj g (N' ^ 2) J b (spMap (algebraMap R (Localization.Away f)) ≫ spMap β)) (ψ : Localization.Away f →+* K), ψ.comp (algebraMap R _) = algebraMap R K ∧ TMap t t' (spMap ψ) ∧ t'.HasTh (𝟙 _) (fun a => algebraMap R _ (v a)) ∧ t'.Shape Mat κ ∧ t'.Prim w w' := by
  intro l1 l2 o _ g N' J b Mat κ w w' _ R K _ _ _ _ _ _ β v t hth hsh hpr
  obtain ⟨f, hf, ψ₁, P', φ, e₁, hg, hpb, hL⟩ := GlobalTheory.T.exists_principallyPolarised_model_localizationAway R K t.pol
  haveI := isDomain_away hf
  letI := ψ₁.toAlgebra
  haveI := isFractionRing_away hf ψ₁ e₁
  have key : ∀ (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (φ : t.A.left ⟶ P'.A.left),
      s = spMap (algebraMap (Localization.Away f) K) ≫ spMap ((algebraMap R (Localization.Away f)).comp β) →
      IsGrpPullback t.A P'.A (spMap ψ₁) φ → LBIso t.L (P'.L.pull φ) →
      ∃ (f₁ : Localization.Away f) (_ : f₁ ≠ 0) (s' : Sp (Localization.Away f₁) ⟶ Sp o)
        (t' : TObj g (N' ^ 2) J b s') (ψ : Localization.Away f₁ →+* K),
        s' = spMap (algebraMap _ (Localization.Away f₁)) ≫ spMap ((algebraMap R (Localization.Away f)).comp β) ∧
        ψ.comp (algebraMap _ _) = ψ₁ ∧ TMap t t' (spMap ψ) := by
    rintro s t φ rfl h1 h2
    obtain ⟨f₁, h, t', ψ, h3, h4⟩ := GlobalTheory.T.thetaLevel_endomorphisms_spread_over_basicOpen l1 l2 o g (N' ^ 2) J b (Localization.Away f) K
      ((algebraMap R (Localization.Away f)).comp β) t P' φ hg h1 h2
    exact ⟨f₁, h, _, t', ψ, rfl, h3, h4⟩
  obtain ⟨f₁, hf₁, s₂, t₂, ψ₂, hs₂, e₂, hm⟩ := key _ t φ (by
    rw [spMap_comp_eq _ _ _ rfl, spMap_comp_eq _ _ _ rfl, ← RingHom.comp_assoc]
    exact congrArg (fun r => spMap (RingHom.comp r β)) e₁.symm) hpb hL
  haveI := isDomain_away hf₁
  letI := ψ₂.toAlgebra
  haveI := isFractionRing_away (K := K) hf₁ ψ₂ e₂
  let io : R →+* Localization.Away f₁ := (algebraMap (Localization.Away f) _).comp (algebraMap R _)
  have hio : ψ₂.comp io = algebraMap R K := by rw [← RingHom.comp_assoc, e₂, e₁]
  have hv : (fun a => algebraMap (Localization.Away f₁) K (io (v a))) = fun a => algebraMap R K (v a) :=
    funext fun a => RingHom.congr_fun hio (v a)
  obtain ⟨f₂, hf₂, H⟩ := GlobalTheory.T.exists_thetaPoint_shape_primitivity_near_generic l1 l2 o g N' J b Mat κ w w' (Localization.Away f₁) K s₂ _ t₂ t
    (fun a => io (v a)) hm (hv ▸ hth) hsh hpr
  have n0 : Near (algebraMap R (Localization.Away f)) ψ₁ 1 :=
    ⟨f, hf, RingHom.id _, ψ₁, rfl, e₁, rfl, isUnit_one⟩
  have n1 := (n0.shrink f₁ fun h =>
    hf₁ (IsFractionRing.injective (Localization.Away f) K (h.trans (map_zero _).symm))).away ψ₂ e₂
  obtain ⟨F, hF, ρ, ψ, h1, h2, h3, h4⟩ := n1.shrink f₂ fun h =>
    hf₂ (IsFractionRing.injective (Localization.Away f₁) K (h.trans (map_zero _).symm))
  obtain ⟨t', ht'⟩ := GlobalTheory.tObj_pull o g (N' ^ 2) J b _ _ s₂
    (spMap (algebraMap R (Localization.Away F)) ≫ spMap β) (spMap ρ) t₂ (by
      rw [hs₂, spMap_comp_eq _ _ _ rfl, spMap_comp_eq _ _ _ rfl, spMap_comp_eq _ _ _ rfl, ← h1])
  obtain ⟨c1, c2, c3⟩ := H _ ρ _ t' h4 ht'
  refine ⟨F, hF, t', ψ, h2, ?_, ?_, c2, c3⟩
  · refine ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g (N' ^ 2) J b _ _ _ _ _ _ t₂ t' t).2 (spMap ρ) (spMap ψ) ht').2 ?_
    rw [spMap_comp_eq _ _ _ h3]
    exact hm
  · have : (fun a => ρ (io (v a))) = fun a => algebraMap R (Localization.Away F) (v a) :=
      funext fun a => RingHom.congr_fun h1 (v a)
    exact this ▸ c1

end GlobalTheory.SpreadGeneric
