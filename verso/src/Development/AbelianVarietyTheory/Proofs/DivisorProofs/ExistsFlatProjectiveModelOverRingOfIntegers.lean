import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SpreadModel

open TopologicalSpace

/- English proof (translation)
Establish `hp (y : Y) : (p (j y)).asIdeal = ⊥`. Rewrite using `[← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]`. Express the relevant statement in the definitionally equal form `Ideal.comap (algebraMap O K) (q y).asIdeal = ⊥`. Rewrite using `[(Ideal.eq_bot_or_top _).resolve_right (q y).2.ne_top]`. Conclude with `Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)`.

Establish `hx : (p (genericPoint X)).asIdeal = ⊥` using `eq_bot_iff.2 (((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 ((PrimeSpectrum.le_iff_specializes _ _).2 ((genericPoint_specializes (j (genericPoint Y))).map p.continuous))).trans (hp _).le)`. Establish `hr : genericPoint X ∈ Set.range j`. Rewrite using `[← H.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, H.isoPullback.hom.surjective.range_eq, Set.image_univ, Scheme.Pullback.range_fst]`. Use `⟨IsLocalRing.closedPoint K, PrimeSpectrum.ext (Eq.trans ?_ hx.symm)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.comap (algebraMap O K) (IsLocalRing.maximalIdeal K) = ⊥`.

Rewrite using `[IsLocalRing.maximalIdeal_eq_bot]`. Conclude with `Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)`. Take `⟨y, hy⟩` from `hr`. Conclude with `hy ▸ (genericPoint_specializes y).map j.continuous`.
-/
theorem gen_specializes {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {p : X ⟶ Sp O} {j : Y ⟶ X} {q : Y ⟶ Sp K}
    (H : IsPullback j q p (spMap (algebraMap O K))) : j (genericPoint Y) ⤳ genericPoint X := by
  have hp (y : Y) : (p (j y)).asIdeal = ⊥ := by
    rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
    change Ideal.comap (algebraMap O K) (q y).asIdeal = ⊥
    rw [(Ideal.eq_bot_or_top _).resolve_right (q y).2.ne_top]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)
  have hx : (p (genericPoint X)).asIdeal = ⊥ :=
    eq_bot_iff.2 (((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 ((PrimeSpectrum.le_iff_specializes _ _).2
      ((genericPoint_specializes (j (genericPoint Y))).map p.continuous))).trans (hp _).le)
  have hr : genericPoint X ∈ Set.range j := by
    rw [← H.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.range_comp, H.isoPullback.hom.surjective.range_eq, Set.image_univ,
      Scheme.Pullback.range_fst]
    refine ⟨IsLocalRing.closedPoint K, PrimeSpectrum.ext (Eq.trans ?_ hx.symm)⟩
    change Ideal.comap (algebraMap O K) (IsLocalRing.maximalIdeal K) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)
  obtain ⟨y, hy⟩ := hr
  exact hy ▸ (genericPoint_specializes y).map j.continuous

/- English proof (translation)
Establish `e₁ : j.app ⊤ (algX p ⊤ a) = algX (j ≫ p) ⊤ a`. Simplify using `[algX, Scheme.Hom.appLE]`. Both sides reduce to the same expression. Rewrite using `[e₁, w]`. Establish `e₂` using `congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ))`.

Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e₂`. Simplify using `only [algX, RingHom.comp_apply]`. Rewrite using `[e₂]`. Simplify using `[Scheme.Hom.appLE]`. Both sides reduce to the same expression.
-/
theorem app_algX {k k' : Type} [CommRing k] [CommRing k'] {σ : k →+* k'} {X Y : Scheme.{0}} {p : X ⟶ Sp k}
    {q : Y ⟶ Sp k'} {j : Y ⟶ X} (w : j ≫ p = q ≫ spMap σ) (a : k) :
    j.app ⊤ (algX p ⊤ a) = algX q ⊤ (σ a) := by
  have e₁ : j.app ⊤ (algX p ⊤ a) = algX (j ≫ p) ⊤ a := by
    simp [algX, Scheme.Hom.appLE]
    rfl
  rw [e₁, w]
  have e₂ := congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e₂
  simp only [algX, RingHom.comp_apply]
  rw [e₂]
  simp [Scheme.Hom.appLE]
  rfl

/- English proof (translation)
Introduce `K Ω _ _ _ _ D m y Y _ q B hB t ψ hq hD ht hψ hK hy`. Set `c` to `q ≫ spMap (algebraMap (𝓞 K) K)`. Take `⟨X, π, j, hX, hπ, hfl, H, hg⟩` from `IntModel.exists_flat_model (O := 𝓞 K) q hq (fun _ : Unit => PSpace (𝓞 K) m) (fun _ => PSpace.str (𝓞 K) m) (fun _ => ProjSpace.toProj c t ht) (fun _ => ⟨m, 𝟙 _, inferInstance, Category.id_comp _⟩) (fun _ => ProjSpace.toProj_str c t ht)`. Take `⟨g, hg₁, hg₂⟩` from `hg ()`. Use `CommonModel.isProper_of_isProjOver hπ` as an intermediate fact.

Establish `hZ : Flat (spMap (Int.castRingHom (𝓞 K)))`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Conclude with `(RingHom.flat_algebraMap_iff (R := ℤ) (S := 𝓞 K)).2 inferInstance`. Establish `har : IsArithVar π D` using `⟨inferInstance, inferInstance, hX, hπ, inferInstance, IntModel.topologicalKrullDim_eq_succ (RingOfIntegers.not_isField K) H hD⟩`. Establish `hη` using `gen_specializes H`.

Establish `hpre : IsPreimmersion j`. Use `IsPreimmersion.of_isLocalization (R := 𝓞 K) (S := K) (nonZeroDivisors (𝓞 K))` as an intermediate fact. Use the proof step `MorphismProperty.of_isPullback H.flip this`. Set `e : X.functionField ≃+* Y.functionField` to `RingEquiv.ofBijective (SmallSec.fnMap j hη) ⟨(SmallSec.fnMap j hη).injective, SmallSec.fnMap_surjective j hη⟩`. Establish `he (u) : e u = SmallSec.fnMap j hη u` using `rfl`.

Establish `he' (a : Ω) : e ((e.symm.toRingHom.comp ψ) a) = ψ a` using `e.apply_symm_apply _`. Use `⟨X, hX, π, g, e.symm.toRingHom.comp ψ, hg₂, har, e.symm.bijective.comp hψ, fun a => ?_, fun k l i h => ?_⟩` and prove the remaining obligations. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[he', hK, he, SmallSec.fnMap_fnOf j hη _ (Opens.mem_top _), app_algX H.w]`. Both sides reduce to the same expression.

Apply `e.injective` to reduce the goal to its premises. Establish `h' : genericPoint Y ∈ j ⁻¹ᵁ ((ProjSpace.O1 (𝓞 K) m).pull g).U i` using `hη.mem_open (Opens.isOpen _) h`. Establish `hU₀ : j ⁻¹ᵁ ((ProjSpace.O1 (𝓞 K) m).pull g).U i ≤ (j ≫ g) ⁻¹ᵁ ProjSpace.chart (𝓞 K) m (i PUnit.unit)` using `fun x hx => (pull_U _ g i).le hx`. Establish `hU : j ⁻¹ᵁ ((ProjSpace.O1 (𝓞 K) m).pull g).U i ≤ ProjSpace.toProj c t ht ⁻¹ᵁ ProjSpace.chart (𝓞 K) m (i PUnit.unit)` using `hg₁ ▸ hU₀`. Establish `hf (a) : j.app _ ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m a) g).f i) = ProjSpace.pullRatio (ProjSpace.toProj c t ht) _ (i PUnit.unit) hU a`.

Use `Eq.trans ?_ (ProjSpace.pullRatio_of_eq hg₁ hU₀ _)` and prove the remaining obligations. Rewrite using `[Scheme.Hom.app_eq_appLE]`. Conclude with `congrArg (fun ψ => ψ.hom (ProjSpace.ratio (𝓞 K) m (i PUnit.unit) a)) (Scheme.Hom.appLE_comp_appLE j g _ _ _ (pull_U _ g i).le le_rfl)`. Take `⟨n, hn⟩` from `exists_chart hB (genericPoint Y)`. Establish `key (a)` using `congrArg (fnOf _ (memInf h' hn)) (ProjSpace.sec_eq_pullRatio_toProj_mul c t ht (i PUnit.unit) a n (W := _ ⊓ B.U n) (inf_le_left.trans hU) inf_le_right)`.

Establish `hne : fnOf _ hn ((t (i PUnit.unit)).f n) ≠ 0`. Establish `hu` using `(ProjSpace.isUnit_resG_sec (t (i PUnit.unit)) n (W := _ ⊓ B.U n) (inf_le_left.trans (hU.trans (ProjSpace.toProj_preimage_chart c t ht _).le)) inf_le_right).map (fnOf _ (memInf h' hn))`. Rewrite `hu` using `[fnOf_resG]`. Conclude with `hu.ne_zero`. Establish `key' (a) : fnOf _ hn ((t a).f n) = e (fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m a) g).f i)) * fnOf _ hn ((t (i PUnit.unit)).f n)`.

Establish `e₁` using `key a`. Rewrite `e₁` using `[map_mul, fnOf_resG, fnOf_resG, ← ProjSpace.resG_pullRatio (hi := hU) inf_le_left, fnOf_resG]`. Rewrite using `[he, SmallSec.fnMap_fnOf j hη h h', hf]`. Conclude with `e₁`. Establish `h₀` using `hy k l n hn`.

Rewrite `h₀` using `[key' k, key' l, ← mul_assoc, ← mul_assoc]`. Rewrite using `[map_mul, map_mul, he', he']`. Conclude with `mul_right_cancel₀ hne h₀`.
-/
theorem exists_spread : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (D m : ℕ) (y : Fin (m + 1) → Ω) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp K) (B : LB Y) (_ : B.IsLB) (t : Fin (m + 1) → B.Sec) (ψ : Ω →+* Y.functionField),
    IsProjOver q → topologicalKrullDim Y = D → (⨆ k, nonzeroLocus (t k) = ⊤) → Function.Bijective ψ →
    (∀ a : K, ψ (algebraMap K Ω a) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX q ⊤ a)) →
    (∀ (k l : Fin (m + 1)) (i : B.ι) (h : genericPoint Y ∈ B.U i), ψ (y k) * fnOf _ h ((t l).f i) = ψ (y l) * fnOf _ h ((t k).f i)) →
    ∃ (X : Scheme.{0}) (_ : IsIntegral X) (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (ψ' : Ω →+* X.functionField),
      g ≫ PSpace.str (𝓞 K) m = p ∧ IsArithVar p D ∧ Function.Bijective ψ' ∧
      (∀ a : 𝓞 K, ψ' (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a)) ∧
      ∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι) (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
        ψ' (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i) =
          ψ' (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i) := by
  intro K Ω _ _ _ _ D m y Y _ q B hB t ψ hq hD ht hψ hK hy
  let c := q ≫ spMap (algebraMap (𝓞 K) K)
  obtain ⟨X, π, j, hX, hπ, hfl, H, hg⟩ := IntModel.exists_flat_model (O := 𝓞 K) q hq
    (fun _ : Unit => PSpace (𝓞 K) m) (fun _ => PSpace.str (𝓞 K) m) (fun _ => ProjSpace.toProj c t ht)
    (fun _ => ⟨m, 𝟙 _, inferInstance, Category.id_comp _⟩) (fun _ => ProjSpace.toProj_str c t ht)
  obtain ⟨g, hg₁, hg₂⟩ := hg ()
  have := CommonModel.isProper_of_isProjOver hπ
  have hZ : Flat (spMap (Int.castRingHom (𝓞 K))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (RingHom.flat_algebraMap_iff (R := ℤ) (S := 𝓞 K)).2 inferInstance
  have har : IsArithVar π D := ⟨inferInstance, inferInstance, hX, hπ, inferInstance,
    IntModel.topologicalKrullDim_eq_succ (RingOfIntegers.not_isField K) H hD⟩
  have hη := gen_specializes H
  have hpre : IsPreimmersion j :=
    have := IsPreimmersion.of_isLocalization (R := 𝓞 K) (S := K) (nonZeroDivisors (𝓞 K))
    MorphismProperty.of_isPullback H.flip this
  let e : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective (SmallSec.fnMap j hη)
    ⟨(SmallSec.fnMap j hη).injective, SmallSec.fnMap_surjective j hη⟩
  have he (u) : e u = SmallSec.fnMap j hη u := rfl
  have he' (a : Ω) : e ((e.symm.toRingHom.comp ψ) a) = ψ a := e.apply_symm_apply _
  refine ⟨X, hX, π, g, e.symm.toRingHom.comp ψ, hg₂, har, e.symm.bijective.comp hψ, fun a => ?_, fun k l i h => ?_⟩
  · apply e.injective
    rw [he', hK, he, SmallSec.fnMap_fnOf j hη _ (Opens.mem_top _), app_algX H.w]
    rfl
  · apply e.injective
    have h' : genericPoint Y ∈ j ⁻¹ᵁ ((ProjSpace.O1 (𝓞 K) m).pull g).U i := hη.mem_open (Opens.isOpen _) h
    have hU₀ : j ⁻¹ᵁ ((ProjSpace.O1 (𝓞 K) m).pull g).U i ≤ (j ≫ g) ⁻¹ᵁ ProjSpace.chart (𝓞 K) m (i PUnit.unit) :=
      fun x hx => (pull_U _ g i).le hx
    have hU : j ⁻¹ᵁ ((ProjSpace.O1 (𝓞 K) m).pull g).U i ≤
        ProjSpace.toProj c t ht ⁻¹ᵁ ProjSpace.chart (𝓞 K) m (i PUnit.unit) := hg₁ ▸ hU₀
    have hf (a) : j.app _ ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m a) g).f i) =
        ProjSpace.pullRatio (ProjSpace.toProj c t ht) _ (i PUnit.unit) hU a := by
      refine Eq.trans ?_ (ProjSpace.pullRatio_of_eq hg₁ hU₀ _)
      rw [Scheme.Hom.app_eq_appLE]
      exact congrArg (fun ψ => ψ.hom (ProjSpace.ratio (𝓞 K) m (i PUnit.unit) a))
        (Scheme.Hom.appLE_comp_appLE j g _ _ _ (pull_U _ g i).le le_rfl)
    obtain ⟨n, hn⟩ := exists_chart hB (genericPoint Y)
    have key (a) := congrArg (fnOf _ (memInf h' hn)) (ProjSpace.sec_eq_pullRatio_toProj_mul c t ht (i PUnit.unit) a n
      (W := _ ⊓ B.U n) (inf_le_left.trans hU) inf_le_right)
    have hne : fnOf _ hn ((t (i PUnit.unit)).f n) ≠ 0 := by
      have hu := (ProjSpace.isUnit_resG_sec (t (i PUnit.unit)) n (W := _ ⊓ B.U n)
        (inf_le_left.trans (hU.trans (ProjSpace.toProj_preimage_chart c t ht _).le)) inf_le_right).map
          (fnOf _ (memInf h' hn))
      rw [fnOf_resG] at hu
      exact hu.ne_zero
    have key' (a) : fnOf _ hn ((t a).f n) = e (fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m a) g).f i)) *
        fnOf _ hn ((t (i PUnit.unit)).f n) := by
      have e₁ := key a
      rw [map_mul, fnOf_resG, fnOf_resG, ← ProjSpace.resG_pullRatio (hi := hU) inf_le_left, fnOf_resG] at e₁
      rw [he, SmallSec.fnMap_fnOf j hη h h', hf]
      exact e₁
    have h₀ := hy k l n hn
    rw [key' k, key' l, ← mul_assoc, ← mul_assoc] at h₀
    rw [map_mul, map_mul, he', he']
    exact mul_right_cancel₀ hne h₀

end GlobalTheory.SpreadModel
