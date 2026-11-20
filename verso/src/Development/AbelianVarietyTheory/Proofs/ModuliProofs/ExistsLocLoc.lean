import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullbackStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullbackStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChangeStatement
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

/- English proof (translation)
Take `⟨t, hth, hall⟩` from `h`. Establish `hs : spMap ρ ≫ spMap β = spMap (ρ.comp β)` using `(spMap_comp ρ β).symm`. Take `⟨t₂, h₂⟩` from `GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g (N' ^ 2) J b (Sp R) (Sp R') (spMap β) (spMap (ρ.comp β)) (spMap ρ) t hs`. Use `⟨t₂, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b (Sp R) (spMap β) t (Sp R') (spMap (ρ.comp β)) t₂ (spMap ρ) R' (𝟙 _) _ h₂, Category.id_comp]`.

Establish `hpush` using `GlobalTheory.T.hasThetaConstants_ring_baseChange hL o g N' J b (Sp R) (spMap β) t R R' ρ (𝟙 _) v hth`. Rewrite `hpush` using `[Category.comp_id]`. Then use the resulting hypothesis. Introduce `K _ _ x s t' hg`. Rewrite `hg` using `[good_comp]`. Establish `h3` using `hall K (x.comp ρ) s t' hg`.

Rewrite `h3` using `[spMap_comp]`. Conclude with `((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g (N' ^ 2) J b (Sp R) (Sp R') (Sp K) (spMap β) (spMap (ρ.comp β)) s t t₂ t').2 (spMap ρ) (spMap x) h₂).2 h3`.
-/
theorem concl_map (hL : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ} {R R' : Type} [CommRing R] [CommRing R']
    {β : o →+* R} {v : Ix g (N' ^ 2) → R} (h : Concl b Mat κ β v) (ρ : R →+* R') :
    Concl b Mat κ (ρ.comp β) (fun a => ρ (v a)) := by
  obtain ⟨t, hth, hall⟩ := h
  have hs : spMap ρ ≫ spMap β = spMap (ρ.comp β) := (spMap_comp ρ β).symm
  obtain ⟨t₂, h₂⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g (N' ^ 2) J b (Sp R) (Sp R') (spMap β) (spMap (ρ.comp β)) (spMap ρ) t hs
  refine ⟨t₂, ?_, ?_⟩
  · rw [GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b (Sp R) (spMap β) t (Sp R') (spMap (ρ.comp β)) t₂ (spMap ρ) R' (𝟙 _) _ h₂,
      Category.id_comp]
    have hpush := GlobalTheory.T.hasThetaConstants_ring_baseChange hL o g N' J b (Sp R) (spMap β) t R R' ρ (𝟙 _) v hth
    rwa [Category.comp_id] at hpush
  · intro K _ _ x s t' hg
    rw [good_comp] at hg
    have h3 := hall K (x.comp ρ) s t' hg
    rw [spMap_comp] at h3
    exact ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g (N' ^ 2) J b (Sp R) (Sp R') (Sp K) (spMap β) (spMap (ρ.comp β)) s t t₂ t').2
      (spMap ρ) (spMap x) h₂).2 h3

/- English proof (translation)
Take `⟨n, a, ha⟩` from `IsLocalization.Away.surj f f'`. Establish `hunit : IsUnit (loc f f)` using `IsLocalization.Away.algebraMap_isUnit f`. Establish `hfq : loc f f ∉ q₁` using `fun hm => hq.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hunit)`. Use `⟨f * a, ?_, ?_⟩` and prove the remaining obligations. Introduce `hm`.

Rewrite `hm` using `[Ideal.mem_comap, map_mul]`. Break down `hq.mem_or_mem hm with h1 | h1` into its components or cases. Conclude with `hfq h1`. Establish `h2 : f' * algebraMap R (Localization.Away f) f ^ n ∈ q₁` using `by rw [ha]; exact h1`. Break down `hq.mem_or_mem h2 with h3 | h3` into its components or cases.

Conclude with `hf' h3`. Conclude with `hfq (hq.mem_of_pow_mem n h3)`. Establish `hF : IsUnit (loc (f * a) (f * a))` using `IsLocalization.Away.algebraMap_isUnit (f * a)`. Rewrite `hF` using `[map_mul]`. Establish `hf1 : IsUnit (loc (f * a) f)` using `isUnit_of_mul_isUnit_left hF`.

Establish `ha1 : IsUnit (loc (f * a) a)` using `isUnit_of_mul_isUnit_right hF`. Establish `hσ : (IsLocalization.Away.lift f hf1).comp (loc f) = loc (f * a)` using `IsLocalization.Away.lift_comp f hf1`. Establish `e : IsLocalization.Away.lift f hf1 f' * IsLocalization.Away.lift f hf1 (loc f f) ^ n = loc (f * a) a`. Rewrite using `[← map_pow, ← map_mul, ha]`. Conclude with `RingHom.congr_fun hσ a`.

Rewrite `ha1` using `[← e]`. Establish `hu : IsUnit (IsLocalization.Away.lift f hf1 f')` using `isUnit_of_mul_isUnit_left ha1`. Use `⟨IsLocalization.Away.lift f' hu, ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocalization.Away.lift_comp f' hu]`. Conclude with `hσ`.
-/
theorem exists_loc_loc {R : Type} [CommRing R] (f : R) (q₁ : Ideal (Localization.Away f)) (hq : q₁.IsPrime)
    (f' : Localization.Away f) (hf' : f' ∉ q₁) :
    ∃ F : R, F ∉ q₁.comap (loc f) ∧ ∃ ρ : Localization.Away f' →+* Localization.Away F,
      (ρ.comp (loc f')).comp (loc f) = loc F := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj f f'
  have hunit : IsUnit (loc f f) := IsLocalization.Away.algebraMap_isUnit f
  have hfq : loc f f ∉ q₁ := fun hm => hq.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hunit)
  refine ⟨f * a, ?_, ?_⟩
  · intro hm
    rw [Ideal.mem_comap, map_mul] at hm
    rcases hq.mem_or_mem hm with h1 | h1
    · exact hfq h1
    · have h2 : f' * algebraMap R (Localization.Away f) f ^ n ∈ q₁ := by rw [ha]; exact h1
      rcases hq.mem_or_mem h2 with h3 | h3
      · exact hf' h3
      · exact hfq (hq.mem_of_pow_mem n h3)
  · have hF : IsUnit (loc (f * a) (f * a)) := IsLocalization.Away.algebraMap_isUnit (f * a)
    rw [map_mul] at hF
    have hf1 : IsUnit (loc (f * a) f) := isUnit_of_mul_isUnit_left hF
    have ha1 : IsUnit (loc (f * a) a) := isUnit_of_mul_isUnit_right hF
    have hσ : (IsLocalization.Away.lift f hf1).comp (loc f) = loc (f * a) := IsLocalization.Away.lift_comp f hf1
    have e : IsLocalization.Away.lift f hf1 f' * IsLocalization.Away.lift f hf1 (loc f f) ^ n = loc (f * a) a := by
      rw [← map_pow, ← map_mul, ha]
      exact RingHom.congr_fun hσ a
    rw [← e] at ha1
    have hu : IsUnit (IsLocalization.Away.lift f hf1 f') := isUnit_of_mul_isUnit_left ha1
    refine ⟨IsLocalization.Away.lift f' hu, ?_⟩
    rw [IsLocalization.Away.lift_comp f' hu]
    exact hσ

/- English proof (translation)
Introduce `hL o _ g N' J b Mat κ R _ β v f q₁ hq h`. Take `⟨f', hf', hc⟩` from `h`. Take `⟨F, hF, ρ, hρ⟩` from `exists_loc_loc f q₁ hq f' hf'`. Use `⟨F, hF, ?_⟩` and prove the remaining obligations. Establish `key : ∀ r : R, ρ (loc f' (loc f r)) = loc F r` using `fun r => RingHom.congr_fun hρ r`.

Establish `hc2 : Concl b Mat κ (ρ.comp ((loc f').comp ((loc f).comp β))) (fun a => ρ (loc f' (loc f (v a))))` using `concl_map hL hc ρ`. Establish `e1 : ρ.comp ((loc f').comp ((loc f).comp β)) = (loc F).comp β` using `RingHom.ext fun r => key (β r)`. Establish `e2 : (fun a => ρ (loc f' (loc f (v a)))) = fun a => loc F (v a)` using `funext fun a => key (v a)`. Rewrite `hc2` using `[e1, e2]`. Conclude with `hc2`.
-/
theorem nearC_of_loc : Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (f : R) (q₁ : Ideal (Localization.Away f)), q₁.IsPrime → NearC b Mat κ ((loc f).comp β) (fun a => loc f (v a)) q₁ → NearC b Mat κ β v (q₁.comap (loc f)) := by
  intro hL o _ g N' J b Mat κ R _ β v f q₁ hq h
  obtain ⟨f', hf', hc⟩ := h
  obtain ⟨F, hF, ρ, hρ⟩ := exists_loc_loc f q₁ hq f' hf'
  refine ⟨F, hF, ?_⟩
  have key : ∀ r : R, ρ (loc f' (loc f r)) = loc F r := fun r => RingHom.congr_fun hρ r
  have hc2 : Concl b Mat κ (ρ.comp ((loc f').comp ((loc f).comp β))) (fun a => ρ (loc f' (loc f (v a)))) :=
    concl_map hL hc ρ
  have e1 : ρ.comp ((loc f').comp ((loc f).comp β)) = (loc F).comp β := RingHom.ext fun r => key (β r)
  have e2 : (fun a => ρ (loc f' (loc f (v a)))) = fun a => loc F (v a) := funext fun a => key (v a)
  rw [e1, e2] at hc2
  exact hc2

end GlobalTheory.ZM.NearBuild
end
