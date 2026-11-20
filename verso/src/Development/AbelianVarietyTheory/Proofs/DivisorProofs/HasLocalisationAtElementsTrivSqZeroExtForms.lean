import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationOfData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitMpOmjExtIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechDR

/- English proof (translation)
Set `L : Om R A j →ₗ[A] Om R B j` to `{ toFun := h.mOm j map_add' := map_add _ map_smul' := fun a y ↦ by`. Rewrite using `[h.mOm_smul, RingHom.id_apply, e]`. Conclude with `algebraMap_smul B a _ }`. Establish `hL : L = GlobalTheory.exteriorPowerMapOver B j (KaehlerDifferential.map R R A B)`. Apply `exteriorPower.linearMap_ext` to reduce the goal to its premises.

Use `ext1 v`. Rewrite using `[LinearMap.compAlternatingMap_apply, LinearMap.compAlternatingMap_apply, GlobalTheory.exteriorPowerMapOver_ιMulti]`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `h.mDR _ = _`. Rewrite using `[exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]`.

Use `congr 1`. Use `congrArg List.ofFn (funext fun i ↦ ?_)` and prove the remaining obligations. Conclude with `(h.mDR_ι (v i)).trans (congrArg _ (h.oneFormMap_eq_kaehlerDifferential_map e (v i)))`. Conclude with `LinearMap.congr_fun hL x`.
-/
theorem mOm_eq_exteriorPowerMapOver {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] {α : A →+* B}
    (h : SemiHom (RingHom.id R) α) (e : ∀ a, α a = algebraMap A B a) (j : ℕ) (x : Om R A j) :
    h.mOm j x = GlobalTheory.exteriorPowerMapOver B j (KaehlerDifferential.map R R A B) x := by
  let L : Om R A j →ₗ[A] Om R B j :=
    { toFun := h.mOm j
      map_add' := map_add _
      map_smul' := fun a y ↦ by
        rw [h.mOm_smul, RingHom.id_apply, e]; exact algebraMap_smul B a _ }
  have hL : L = GlobalTheory.exteriorPowerMapOver B j (KaehlerDifferential.map R R A B) := by
    apply exteriorPower.linearMap_ext
    ext1 v
    rw [LinearMap.compAlternatingMap_apply, LinearMap.compAlternatingMap_apply,
      GlobalTheory.exteriorPowerMapOver_ιMulti]
    apply Subtype.ext
    change h.mDR _ = _
    rw [exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
      ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
    congr 1
    refine congrArg List.ofFn (funext fun i ↦ ?_)
    exact (h.mDR_ι (v i)).trans (congrArg _ (h.oneFormMap_eq_kaehlerDifferential_map e (v i)))
  exact LinearMap.congr_fun hL x

end GlobalTheory.CechDR

namespace GlobalTheory.CechDR.FormExtJ

attribute [local instance] opModJ isCentralScalarJ isScalarTowerJ

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (j : ℕ)

/- English proof (translation)
Apply `TrivSqZeroExt.ext` to reduce the goal to its premises. Rewrite using `[TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, fst_extMapJ, fst_extMapJ]`. Simplify using `only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, map_mul, map_pow] at ha ⊢`. Take the linear combination `(mp F l c.fst) ^ (k₂ + 1) * ha`. Rewrite using `[TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _), TrivSqZeroExt.fst_pow, snd_extMapJ, fst_extMapJ, snd_extMapJ]`.

Simplify using `only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, map_add, map_nsmul, pOm_smul, map_mul, map_pow, op_smul_eq_smul, Nat.pred_succ] at ha hη ⊢`. Rewrite using `[← hη, ← ha]`. Use `module`.
-/
theorem surj_keyJ {T T' : C} (l : T ⟶ T') (c : TrivSqZeroExt (F.obj T) (Om R (F.obj T) j))
    (y : TrivSqZeroExt (F.obj T') (Om R (F.obj T') j)) (a₀ : F.obj T) (η₀ : Om R (F.obj T) j)
    (k₁ k₂ : ℕ) (ha : y.fst * mp F l (c.fst ^ k₁) = mp F l a₀)
    (hη : mp F l (c.fst ^ k₂) • y.snd = pOm F j l η₀) :
    y * extMapJ F j l c ^ (k₁ + k₂ + 1) = extMapJ F j l (TrivSqZeroExt.inl (a₀ * c.fst ^ (k₂ + 1)) +
      TrivSqZeroExt.inr ((k₁ + k₂ + 1) • (a₀ * c.fst ^ k₂) • c.snd + c.fst ^ (k₁ + 1) • η₀)) := by
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, fst_extMapJ, fst_extMapJ]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, map_mul,
      map_pow] at ha ⊢
    linear_combination (mp F l c.fst) ^ (k₂ + 1) * ha
  · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _),
      TrivSqZeroExt.fst_pow, snd_extMapJ, fst_extMapJ, snd_extMapJ]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, map_add, map_nsmul,
      pOm_smul, map_mul, map_pow, op_smul_eq_smul, Nat.pred_succ] at ha hη ⊢
    rw [← hη, ← ha]
    module

/- English proof (translation)
Apply `TrivSqZeroExt.ext` to reduce the goal to its premises. Rewrite using `[TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_zero]`. Take the linear combination `c.fst ^ (m₂ + 1) * h₁`. Rewrite using `[TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _), TrivSqZeroExt.fst_pow, TrivSqZeroExt.snd_zero, op_smul_eq_smul, Nat.pred_succ]`. Take the linear combination `(norm := module) c.fst ^ (m₁ + 1) • h₂ + h₁ • ((m₁ + m₂ + 1) • c.fst ^ m₂ • c.snd)`.
-/
theorem ker_keyJ {T : C} (c x : TrivSqZeroExt (F.obj T) (Om R (F.obj T) j)) (m₁ m₂ : ℕ)
    (h₁ : c.fst ^ m₁ * x.fst = 0) (h₂ : c.fst ^ m₂ • x.snd = 0) : c ^ (m₁ + m₂ + 1) * x = 0 := by
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_zero]
    linear_combination c.fst ^ (m₂ + 1) * h₁
  · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _),
      TrivSqZeroExt.fst_pow, TrivSqZeroExt.snd_zero, op_smul_eq_smul, Nat.pred_succ]
    linear_combination (norm := module) c.fst ^ (m₁ + 1) • h₂ + h₁ • ((m₁ + m₂ + 1) • c.fst ^ m₂ • c.snd)

/- English proof (translation)
Introduce `T c`. Take `⟨T', l, h1, h2, h3, h4⟩` from `H T c.fst`. Use `letI : Algebra (F.obj T) (F.obj T') := (mp F l : F.obj T →+* F.obj T').toAlgebra`. Use `haveI : IsScalarTower R (F.obj T) (F.obj T') := IsScalarTower.of_algebraMap_eq fun r ↦ ((mp F l).commutes r).symm`. Use `haveI := FormExt.isLocalization_of_data F l c.fst h1 h2 h3`.

Use `haveI : Algebra.FormallyEtale (F.obj T) (F.obj T') := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers c.fst)`. Establish `hb` using `GlobalTheory.TopForm.isBaseChange_exteriorPower (KaehlerDifferential.isBaseChange_of_formallyEtale R (F.obj T) (F.obj T')) j`. Use `haveI := (isLocalizedModule_iff_isBaseChange (Submonoid.powers c.fst) (F.obj T') _).2 hb`. Establish `hp : ∀ ω, pOm F j l ω = GlobalTheory.exteriorPowerMapOver (F.obj T') j (KaehlerDifferential.map R R (F.obj T) (F.obj T')) ω` using `mOm_eq_exteriorPowerMapOver _ (fun _ ↦ rfl) j`. Establish `hs : ∀ (a : F.obj T) (η : Om R (F.obj T') j), a • η = mp F l a • η` using `fun a η ↦ (algebraMap_smul (F.obj T') a η).symm`.

Use `⟨T', l, (isUnit_mp_omjExt_iff F j l c).2 h1, fun y ↦ ?_, fun x hx ↦ ?_, fun S u hu ↦ h4 S u ((isUnit_mp_omjExt_iff F j u c).1 hu)⟩` and prove the remaining obligations. Take `⟨⟨a₀, _, k₁, rfl⟩, ha⟩` from `IsLocalization.surj (Submonoid.powers c.fst) y.fst`. Take `⟨⟨η₀, _, k₂, rfl⟩, hη⟩` from `IsLocalizedModule.surj (Submonoid.powers c.fst) (GlobalTheory.exteriorPowerMapOver (F.obj T') j (KaehlerDifferential.map R R (F.obj T) (F.obj T'))) y.snd`. Express the relevant statement in the definitionally equal form `y.fst * mp F l (c.fst ^ k₁) = mp F l a₀ at ha`. Express the relevant statement in the definitionally equal form `(c.fst ^ k₂) • y.snd = _ at hη`.

Rewrite `hη` using `[hs, ← hp]`. Use `⟨k₁ + k₂ + 1, TrivSqZeroExt.inl (a₀ * c.fst ^ (k₂ + 1)) + TrivSqZeroExt.inr ((k₁ + k₂ + 1) • (a₀ * c.fst ^ k₂) • c.snd + c.fst ^ (k₁ + 1) • η₀), ?_⟩` and prove the remaining obligations. Conclude with `surj_keyJ F j l c y a₀ η₀ k₁ k₂ ha hη`. Establish `e1 : mp F l x.fst = 0` using `(fst_extMapJ F j l x).symm.trans (congrArg TrivSqZeroExt.fst hx)`. Establish `e2 : GlobalTheory.exteriorPowerMapOver (F.obj T') j (KaehlerDifferential.map R R (F.obj T) (F.obj T')) x.snd = 0` using `(hp _).symm.trans ((snd_extMapJ F j l x).symm.trans (congrArg TrivSqZeroExt.snd hx))`.

Take `⟨m₁, h₁⟩` from `h3 _ e1`. Take `⟨⟨_, m₂, rfl⟩, h₂⟩` from `IsLocalizedModule.exists_of_eq (S := Submonoid.powers c.fst) (f := GlobalTheory.exteriorPowerMapOver (F.obj T') j (KaehlerDifferential.map R R (F.obj T) (F.obj T'))) (x₁ := x.snd) (x₂ := 0) (by rw [e2, map_zero])`. Rewrite `h₂` using `[smul_zero, Submonoid.smul_def]`. Conclude with `⟨m₁ + m₂ + 1, ker_keyJ F j c x m₁ m₂ h₁ h₂⟩`.
-/
theorem hasLoc_omjExt (H : Desc.HasLoc F) : Desc.HasLoc (omjExt F j) := by
  intro T c
  obtain ⟨T', l, h1, h2, h3, h4⟩ := H T c.fst
  letI : Algebra (F.obj T) (F.obj T') := (mp F l : F.obj T →+* F.obj T').toAlgebra
  haveI : IsScalarTower R (F.obj T) (F.obj T') :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((mp F l).commutes r).symm
  haveI := FormExt.isLocalization_of_data F l c.fst h1 h2 h3
  haveI : Algebra.FormallyEtale (F.obj T) (F.obj T') :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers c.fst)
  have hb := GlobalTheory.TopForm.isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale R (F.obj T) (F.obj T')) j
  haveI := (isLocalizedModule_iff_isBaseChange (Submonoid.powers c.fst) (F.obj T') _).2 hb
  have hp : ∀ ω, pOm F j l ω =
      GlobalTheory.exteriorPowerMapOver (F.obj T') j (KaehlerDifferential.map R R (F.obj T) (F.obj T')) ω :=
    mOm_eq_exteriorPowerMapOver _ (fun _ ↦ rfl) j
  have hs : ∀ (a : F.obj T) (η : Om R (F.obj T') j), a • η = mp F l a • η := fun a η ↦
    (algebraMap_smul (F.obj T') a η).symm
  refine ⟨T', l, (isUnit_mp_omjExt_iff F j l c).2 h1, fun y ↦ ?_, fun x hx ↦ ?_,
    fun S u hu ↦ h4 S u ((isUnit_mp_omjExt_iff F j u c).1 hu)⟩
  · obtain ⟨⟨a₀, _, k₁, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers c.fst) y.fst
    obtain ⟨⟨η₀, _, k₂, rfl⟩, hη⟩ := IsLocalizedModule.surj (Submonoid.powers c.fst)
      (GlobalTheory.exteriorPowerMapOver (F.obj T') j (KaehlerDifferential.map R R (F.obj T) (F.obj T'))) y.snd
    change y.fst * mp F l (c.fst ^ k₁) = mp F l a₀ at ha
    change (c.fst ^ k₂) • y.snd = _ at hη
    rw [hs, ← hp] at hη
    refine ⟨k₁ + k₂ + 1, TrivSqZeroExt.inl (a₀ * c.fst ^ (k₂ + 1)) +
      TrivSqZeroExt.inr ((k₁ + k₂ + 1) • (a₀ * c.fst ^ k₂) • c.snd + c.fst ^ (k₁ + 1) • η₀), ?_⟩
    exact surj_keyJ F j l c y a₀ η₀ k₁ k₂ ha hη
  · have e1 : mp F l x.fst = 0 := (fst_extMapJ F j l x).symm.trans (congrArg TrivSqZeroExt.fst hx)
    have e2 : GlobalTheory.exteriorPowerMapOver (F.obj T') j
        (KaehlerDifferential.map R R (F.obj T) (F.obj T')) x.snd = 0 :=
      (hp _).symm.trans ((snd_extMapJ F j l x).symm.trans (congrArg TrivSqZeroExt.snd hx))
    obtain ⟨m₁, h₁⟩ := h3 _ e1
    obtain ⟨⟨_, m₂, rfl⟩, h₂⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers c.fst)
      (f := GlobalTheory.exteriorPowerMapOver (F.obj T') j (KaehlerDifferential.map R R (F.obj T) (F.obj T')))
      (x₁ := x.snd) (x₂ := 0) (by rw [e2, map_zero])
    rw [smul_zero, Submonoid.smul_def] at h₂
    exact ⟨m₁ + m₂ + 1, ker_keyJ F j c x m₁ m₂ h₁ h₂⟩

end GlobalTheory.CechDR.FormExtJ
