import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLbOfGeneratedSystem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerSquaresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLocalUnitsAlongNilpotentThickeningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeQuotientClosedImmersionIdealSheafStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftedRatiosProjectiveRelationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerChartsPreimageAndGermPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFramesOfPullbackPowerOnNonzeroLocusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLineBundleOfCompatibleLocalFramesStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

/- English proof (translation)
Introduce and unpack `R _ I Y β hβ n C H₀ s₀ hH₀ ⟨hD, hρs⟩ γ hγ0 hγs e k L hL ⟨w, hw⟩`. Establish `hpb : IsPullback (γ e) (Y 0).hom ((Y e).hom ≫ thick R I e) (thick R I 0)` using `(GlobalTheory.T.isPullback_thick_tower_squares R I Y β hβ).2 γ hγ0 hγs e`. Establish `hsurj : ∀ e, Surjective (γ e)`. Introduce `e`. Proceed by induction on `e with`.

Consider the case `zero => rw [hγ0]`. Use `infer_instance`. Consider the case `succ e ih`. Rewrite using `[← hγs e]`. Use `MorphismProperty.of_isPullback (P := @Surjective) (hβ e).flip (GlobalTheory.GenSystem.surjective_thickTrans R I e)` as an intermediate fact.

Use `infer_instance`. Establish `hpre` using `fun i => GlobalTheory.T.thickeningTowerCharts_preimage_and_germ_pullback R I Y β n C γ hγ0 hγs e i`. Establish `hu` using `fun i => GlobalTheory.T.exists_local_frames_of_pullback_power_on_nonzeroLocus _ _ (γ e) H₀ (s₀ i) k L hL hH₀ w hw (C.D e i) ((hpre i).1.trans (hD i))`. Use `choose u hu1 hu2 using hu`. Establish `ht` using `fun i => GlobalTheory.T.lift_local_units_along_nilpotent_thickening R (I ^ (0 + 1)) (Y e).left (Y 0).left ((Y e).hom ≫ thick R I e) (γ e) (Y 0).hom hpb (hsurj e) L hL (C.D e i) (C.aff e i) (u i) (hu1 i)`.

Use `choose τ hτ1 hτ2 using ht`. Take `⟨g, hgLB, hgIso, hg⟩` from `GlobalTheory.T.cech_lineBundle_of_compatible_local_frames (Y e).left L hL n (C.D e) (C.cover e) τ hτ2`. Use `⟨g, hgLB, hgIso, fun i j => ?_⟩` and prove the remaining obligations. Establish `hVaff : IsAffineOpen (C.D e i ⊓ C.D e j)`. Use `(C.aff e i).basicOpen (C.ρ e i j)` as an intermediate fact.

Rewrite `this` using `[(GlobalTheory.T.thickeningTower_liftedRatios_projective_relations R I Y β hβ n C).1 e i j]`. Then use the resulting hypothesis. Take `⟨-, -, hker⟩` from `GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (0 + 1)) (Y e).left (Y 0).left ((Y e).hom ≫ thick R I e) (γ e) (Y 0).hom hpb`. Establish `hk` using `(hker _ hVaff).2`. Establish `hτu : ∀ i m z (hz : γ e z ∈ C.D e i ⊓ L.U m), gm (γ e) z _ (τ i m) = gm (𝟙 _) z _ (u i m)`. Introduce `i m z hz`.

Establish `h1` using `gm_pull (𝟙 _) (γ e) z _ hz (τ i m)`. Rewrite `h1` using `[Category.id_comp]`. Rewrite using `[← h1]`. Use `congr 1`. Conclude with `Units.ext (hτ1 i m)`.

Establish `hmem : (g i j).val - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k ∈ RingHom.ker ((γ e).app (C.D e i ⊓ C.D e j)).hom`. Rewrite using `[RingHom.mem_ker]`. Apply `fn_ext` to reduce the goal to its premises. Introduce `z hz`. Establish `hz' : γ e z ∈ C.D e i ⊓ C.D e j` using `hz`.

Take `⟨m, hm⟩` from `exists_chart hL (γ e z)`. Take `⟨a, ha⟩` from `exists_chart hH₀ z`. Establish `hzi : z ∈ C.D 0 i` using `(hpre i).1 ▸ hz'.1`. Establish `hzj : z ∈ C.D 0 j` using `(hpre j).1 ▸ hz'.2`. Establish `hm3 : γ e z ∈ C.D e i ⊓ C.D e j ⊓ L.U m` using `⟨hz', hm⟩`.

Establish `hgz : gs (γ e) z _ (g i j).val = (gm (𝟙 _) z _ (u j m)).val * ((gm (𝟙 _) z _ (u i m))⁻¹).val`. Rewrite using `[gs_unit _ z _ hz', ← gm_res (γ e) z (inf_le_left : C.D e i ⊓ C.D e j ⊓ L.U m ≤ C.D e i ⊓ C.D e j) hm3, hg i j m, map_mul, map_inv, gm_res _ z _ hm3, gm_res _ z _ hm3, hτu j m z ⟨hz'.2, hm⟩, hτu i m z ⟨hz'.1, hm⟩, Units.val_mul]`. Establish `hsj` using `hu2 j z m a ⟨hz'.2, hm⟩ ha`. Establish `hsi` using `hu2 i z m a ⟨hz'.1, hm⟩ ha`. Establish `hrel : gs (𝟙 _) z _ ((s₀ j).f a) = gs (𝟙 _) z _ (C.ρ 0 i j) * gs (𝟙 _) z _ ((s₀ i).f a)`.

Establish `h` using `congrArg (gs (𝟙 _) z (C.D 0 i ⊓ H₀.U a)) (hρs i j a)`. Establish `hmz : (𝟙 (Y 0).left) z ∈ C.D 0 i ⊓ H₀.U a` using `⟨hzi, ha⟩`. Rewrite `h` using `[gs_mul _ z _ hmz, gs_res _ z _ hmz, gs_res _ z _ hmz, gs_res _ z _ hmz]`. Then use the resulting hypothesis. Establish `hρz : gs (γ e) z _ (rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k) = gs (𝟙 _) z _ (C.ρ 0 i j) ^ k`. Rewrite using `[gs_eq _ z _ hz', map_pow, map_pow, ← gs_eq _ z _ hz', gs_res _ z _ hz', (hpre i).2 j z hzi]`.

Establish `hu' : (gm (𝟙 _) z _ (u j m)).val = gs (𝟙 _) z _ (C.ρ 0 i j) ^ k * (gm (𝟙 _) z _ (u i m)).val`. Establish `hW` using `(gm (𝟙 (Y 0).left) z _ (w.s (a, fun _ => m))).isUnit`. Apply `hW.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[mul_comm _ (gm (𝟙 _) z _ (u j m)).val, ← hsj, hrel, mul_pow, hsi]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hsub` using `gs_pull (𝟙 _) (γ e) z (C.D e i ⊓ C.D e j) hz' ((g i j).val - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k)`. Rewrite `hsub` using `[Category.id_comp]`. Establish `h0 : gs (𝟙 _) z (γ e ⁻¹ᵁ (C.D e i ⊓ C.D e j)) 0 = 0` using `by rw [gs_eq _ z _ hz, map_zero, map_zero]`. Rewrite using `[h0, hsub, gs_eq _ z _ hz', map_sub, map_sub, ← gs_eq _ z _ hz', ← gs_eq _ z _ hz', hgz, hρz, hu']`. Rewrite using `[mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one, sub_self]`.

Rewrite `hmem` using `[hk]`. Simplify `hmem` using `only [towerIdeal, zero_add, pow_one]`.
-/
theorem GlobalTheory.FormalAlg.exists_chart_cocycle_of_pull : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (H₀ : LB (Y 0).left) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → ((∀ i, C.D 0 i = nonzeroLocus (s₀ i)) ∧ ∀ i j (m : H₀.ι), rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ j).f m) = rs (Y 0).left (inf_le_left : C.D 0 i ⊓ H₀.U m ≤ C.D 0 i) (C.ρ 0 i j) * rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ i).f m)) → ∀ γ : ∀ e, (Y 0).left ⟶ (Y e).left, γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e k : ℕ) (L : LB (Y e).left), L.IsLB → LBIso (L.pull (γ e)) (GlobalTheory.AbLaw.pw H₀ k) → ∃ g : ∀ i j, Γ((Y e).left, C.D e i ⊓ C.D e j)ˣ, (⟨Fin (n + 1), C.D e, g⟩ : LB (Y e).left).IsLB ∧ LBIso L ⟨Fin (n + 1), C.D e, g⟩ ∧ ∀ i j, (g i j).val - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k ∈ towerIdeal Y e I (C.D e i ⊓ C.D e j) := by
  rintro R _ I Y β hβ n C H₀ s₀ hH₀ ⟨hD, hρs⟩ γ hγ0 hγs e k L hL ⟨w, hw⟩
  have hpb : IsPullback (γ e) (Y 0).hom ((Y e).hom ≫ thick R I e) (thick R I 0) :=
    (GlobalTheory.T.isPullback_thick_tower_squares R I Y β hβ).2 γ hγ0 hγs e
  have hsurj : ∀ e, Surjective (γ e) := by
    intro e
    induction e with
    | zero => rw [hγ0]; infer_instance
    | succ e ih =>
      rw [← hγs e]
      have := MorphismProperty.of_isPullback (P := @Surjective) (hβ e).flip (GlobalTheory.GenSystem.surjective_thickTrans R I e)
      infer_instance
  have hpre := fun i => GlobalTheory.T.thickeningTowerCharts_preimage_and_germ_pullback R I Y β n C γ hγ0 hγs e i
  have hu := fun i => GlobalTheory.T.exists_local_frames_of_pullback_power_on_nonzeroLocus _ _ (γ e) H₀ (s₀ i) k L hL hH₀ w hw (C.D e i) ((hpre i).1.trans (hD i))
  choose u hu1 hu2 using hu
  have ht := fun i => GlobalTheory.T.lift_local_units_along_nilpotent_thickening R (I ^ (0 + 1)) (Y e).left (Y 0).left ((Y e).hom ≫ thick R I e) (γ e) (Y 0).hom
    hpb (hsurj e) L hL (C.D e i) (C.aff e i) (u i) (hu1 i)
  choose τ hτ1 hτ2 using ht
  obtain ⟨g, hgLB, hgIso, hg⟩ := GlobalTheory.T.cech_lineBundle_of_compatible_local_frames (Y e).left L hL n (C.D e) (C.cover e) τ hτ2
  refine ⟨g, hgLB, hgIso, fun i j => ?_⟩
  have hVaff : IsAffineOpen (C.D e i ⊓ C.D e j) := by
    have := (C.aff e i).basicOpen (C.ρ e i j)
    rwa [(GlobalTheory.T.thickeningTower_liftedRatios_projective_relations R I Y β hβ n C).1 e i j] at this
  obtain ⟨-, -, hker⟩ := GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (0 + 1)) (Y e).left (Y 0).left ((Y e).hom ≫ thick R I e) (γ e) (Y 0).hom hpb
  have hk := (hker _ hVaff).2

  have hτu : ∀ i m z (hz : γ e z ∈ C.D e i ⊓ L.U m), gm (γ e) z _ (τ i m) = gm (𝟙 _) z _ (u i m) := by
    intro i m z hz
    have h1 := gm_pull (𝟙 _) (γ e) z _ hz (τ i m)
    rw [Category.id_comp] at h1
    rw [← h1]
    congr 1
    exact Units.ext (hτ1 i m)
  have hmem : (g i j).val - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k ∈
      RingHom.ker ((γ e).app (C.D e i ⊓ C.D e j)).hom := by
    rw [RingHom.mem_ker]
    apply fn_ext
    intro z hz
    have hz' : γ e z ∈ C.D e i ⊓ C.D e j := hz
    obtain ⟨m, hm⟩ := exists_chart hL (γ e z)
    obtain ⟨a, ha⟩ := exists_chart hH₀ z
    have hzi : z ∈ C.D 0 i := (hpre i).1 ▸ hz'.1
    have hzj : z ∈ C.D 0 j := (hpre j).1 ▸ hz'.2
    have hm3 : γ e z ∈ C.D e i ⊓ C.D e j ⊓ L.U m := ⟨hz', hm⟩

    have hgz : gs (γ e) z _ (g i j).val = (gm (𝟙 _) z _ (u j m)).val * ((gm (𝟙 _) z _ (u i m))⁻¹).val := by
      rw [gs_unit _ z _ hz', ← gm_res (γ e) z (inf_le_left : C.D e i ⊓ C.D e j ⊓ L.U m ≤ C.D e i ⊓ C.D e j) hm3,
        hg i j m, map_mul, map_inv, gm_res _ z _ hm3, gm_res _ z _ hm3, hτu j m z ⟨hz'.2, hm⟩,
        hτu i m z ⟨hz'.1, hm⟩, Units.val_mul]

    have hsj := hu2 j z m a ⟨hz'.2, hm⟩ ha
    have hsi := hu2 i z m a ⟨hz'.1, hm⟩ ha
    have hrel : gs (𝟙 _) z _ ((s₀ j).f a) = gs (𝟙 _) z _ (C.ρ 0 i j) * gs (𝟙 _) z _ ((s₀ i).f a) := by
      have h := congrArg (gs (𝟙 _) z (C.D 0 i ⊓ H₀.U a)) (hρs i j a)
      have hmz : (𝟙 (Y 0).left) z ∈ C.D 0 i ⊓ H₀.U a := ⟨hzi, ha⟩
      rwa [gs_mul _ z _ hmz, gs_res _ z _ hmz, gs_res _ z _ hmz, gs_res _ z _ hmz] at h
    have hρz : gs (γ e) z _ (rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k) =
        gs (𝟙 _) z _ (C.ρ 0 i j) ^ k := by
      rw [gs_eq _ z _ hz', map_pow, map_pow, ← gs_eq _ z _ hz', gs_res _ z _ hz', (hpre i).2 j z hzi]
    have hu' : (gm (𝟙 _) z _ (u j m)).val = gs (𝟙 _) z _ (C.ρ 0 i j) ^ k * (gm (𝟙 _) z _ (u i m)).val := by
      have hW := (gm (𝟙 (Y 0).left) z _ (w.s (a, fun _ => m))).isUnit
      apply hW.mul_left_cancel
      rw [mul_comm _ (gm (𝟙 _) z _ (u j m)).val, ← hsj, hrel, mul_pow, hsi]
      ring
    have hsub := gs_pull (𝟙 _) (γ e) z (C.D e i ⊓ C.D e j) hz' ((g i j).val - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k)
    rw [Category.id_comp] at hsub
    have h0 : gs (𝟙 _) z (γ e ⁻¹ᵁ (C.D e i ⊓ C.D e j)) 0 = 0 := by rw [gs_eq _ z _ hz, map_zero, map_zero]
    rw [h0, hsub, gs_eq _ z _ hz', map_sub, map_sub, ← gs_eq _ z _ hz', ← gs_eq _ z _ hz', hgz, hρz, hu']
    rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one, sub_self]
  rw [hk] at hmem
  simpa only [towerIdeal, zero_add, pow_one] using hmem
