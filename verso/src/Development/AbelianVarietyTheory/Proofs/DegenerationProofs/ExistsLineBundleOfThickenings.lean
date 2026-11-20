import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SerreVanishingVeryAmple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLineBundleOfThickenings
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompatibleSectionsThickeningsLocalRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLbOfGeneratedSystem

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBAlgLocal

open GlobalTheory.MorAlg GlobalTheory.LBAlg

/- English proof (translation)
Take `⟨σ₀, w₀, hw₀, c₀⟩` from `exists_isPull φ hH σ`. Use `⟨σ₀, GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R X f H m σ hH hσ _ g _ _ φ h.w ?_ _ w₀ _ (pull_isLB hH _) hw₀ c₀⟩` and prove the remaining obligations. Establish `e : pullback.lift φ f' h.w = h.isoPullback.hom`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[pullback.lift_fst, IsPullback.isoPullback_hom_fst]`.

Rewrite using `[pullback.lift_snd, IsPullback.isoPullback_hom_snd]`. Rewrite using `[e]`. Use `infer_instance`.
-/
theorem exists_veryAmpleBy_of_isPullback {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R')} {φ : X' ⟶ X} (g : R →+* R')
    (h : IsPullback φ f' f (Spec.map (CommRingCat.ofHom g))) {H : LB X} (hH : H.IsLB) {m : ℕ}
    {σ : Fin (m + 1) → LB.Sec H} (hσ : VeryAmpleBy f H σ) :
    ∃ σ' : Fin (m + 1) → LB.Sec (H.pull φ), VeryAmpleBy f' (H.pull φ) σ' := by
  obtain ⟨σ₀, w₀, hw₀, c₀⟩ := exists_isPull φ hH σ
  refine ⟨σ₀, GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R X f H m σ hH hσ _ g _ _ φ h.w ?_ _ w₀ _
    (pull_isLB hH _) hw₀ c₀⟩
  have e : pullback.lift φ f' h.w = h.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, IsPullback.isoPullback_hom_fst]
    · rw [pullback.lift_snd, IsPullback.isoPullback_hom_snd]
  rw [e]
  infer_instance

/- English proof (translation)
Introduce `R _ _ _ I hI hcomp Y β hβ B b hB hfl hb hc N v hN`. Take `⟨H, hH, m, σ, hσ⟩` from `id hB`. Establish `hL : ∀ e, (H.pull (b e)).IsLB` using `fun e => pull_isLB hH _`. Use `choose σ' hva using fun e => exists_veryAmpleBy_of_isPullback (Ideal.Quotient.mk (I ^ (e + 1))) (hb e) hH hσ`. Establish `hI' : I ^ (0 + 1) ≠ ⊤` using `by simpa using hI`.

Establish `: Nontrivial (R ⧸ I ^ (0 + 1))` using `Ideal.Quotient.nontrivial_iff.2 hI'`. Take `⟨𝔪, h𝔪⟩` from `Ideal.exists_maximal (R ⧸ I ^ (0 + 1))`. Set `_` to `Ideal.Quotient.field 𝔪`. Establish `hπ` using `IsPullback.of_hasPullback (Y 0).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔪)))`. Generalize the expression as in `pullback.snd (Y 0).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔪))) = f₀ at hπ`.

Generalize the expression as in `pullback.fst (Y 0).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔪))) = π at hπ`. Take `⟨σ₀, hσ₀⟩` from `exists_veryAmpleBy_of_isPullback (Ideal.Quotient.mk 𝔪) hπ (hL 0) (hva 0)`. Take `⟨t₁, ht₁⟩` from `GlobalTheory.AbLaw.serre_h1Zero_and_sections_polynomial.1 _ _ _ _ _ _ (pull_isLB (hL 0) π) hσ₀ ((N 0).pull π) (pull_isLB (hN 0).1 π)`. Take `⟨t₂, ht₂⟩` from `GlobalTheory.TwistGen.twist_generated _ _ _ _ _ _ (hL 0) (hva 0) (N 0) (hN 0).1`. Take `⟨t, h₁, h₂⟩ : ∃ t, t₁ ≤ t ∧ t₂ ≤ t` from `⟨max t₁ t₂, le_max_left _ _, le_max_right _ _⟩`.

Take `⟨n, u, hu⟩` from `ht₂ t h₂`. Establish `hT : ∀ e, (tw (N e) (H.pull (b e)) t).IsLB` using `fun e => isLB_tw (hN e).1 (hL e) t`. Establish `hv' : ∀ e, LBIso (tw (N e) (H.pull (b e)) t) ((tw (N (e + 1)) (H.pull (b (e + 1))) t).pull (β e))` using `fun e => LBIso.trans (hT e) (isLB_tw (pull_isLB (hN (e + 1)).1 _) (hL e) t) (pull_isLB (hT (e + 1)) _) (lbIso_tw_congr (hL e) t ⟨v e, (hN e).2⟩) (LBIso.chartPull (chartPullTw (Geo.Tor.chartPullPull _ _ _ rfl) (chartPullSame H _ _ _ (β e) fun _ => (hc e).symm) t) (Geo.Tor.chartPul …`. Use `choose v' hv' using hv'`. Establish `hflY : ∀ e, Flat (Y e).hom` using `fun e => MorphismProperty.of_isPullback (P := @Flat) (hb e) hfl`.

Establish `hP : ∀ e, IsProjBy (Y e).hom` using `fun e => ⟨_, hL e, m, σ' e, hva e⟩`. Take `⟨w₀, hw₀⟩ : LBIso (tw ((N 0).pull π) ((H.pull (b 0)).pull π) t) ((tw (N 0) (H.pull (b 0)) t).pull π)` from `LBIso.chartPull (chartPullTw (Geo.Tor.chartPullPull _ _ _ rfl) (Geo.Tor.chartPullPull _ _ _ rfl) t) (Geo.Tor.chartPullPull _ _ _ rfl) (lbIso_self (hT 0))`. Use `choose s hs0 hs using fun j => GlobalTheory.SecLifts.exists_compatible_sections_local R I hI Y β hβ hflY hP (fun e => tw (N e) (H.pull (b e)) t) v' (fun e => ⟨hT e, hv' e⟩) _ (Ideal.Quotient.mk 𝔪) Ideal.Quotient.mk_surjective _ π f₀ hπ _ w₀ (isLB_tw (pull_isLB (hN 0).1 π) (pull_i …`. Take `⟨M, hM, hNM⟩` from `GlobalTheory.GenSystem.exists_lb_of_generated_system R I hI hcomp Y β hβ B b hB hfl hb hc (fun e => tw (N e) (H.pull (b e)) t) v' (fun e => ⟨hT e, hv' e⟩) n (fun e j => s j e) (fun e j => hs j e) (by simpa only [hs0] using hu)`. Establish `hM' : (tw M H (-t)).IsLB` using `isLB_tw hM hH _`.

Use `⟨tw M H (-t), hM', fun e => ?_⟩` and prove the remaining obligations. Establish `hO' : (tw (M.pull (b e)) (H.pull (b e)) (-t)).IsLB` using `isLB_tw (pull_isLB hM _) (hL e) _`. Conclude with `LBIso.trans (hN e).1 hO' (pull_isLB hM' _) (LBIso.trans (hN e).1 (isLB_tw (hT e) (hL e) _) hO' (lbIso_tw_tw (hN e).1 (hL e) t) (lbIso_tw_congr (hL e) (-t) (hNM e))) (LBIso.chartPull (chartPullTw (Geo.Tor.chartPullPull _ _ _ rfl) (Geo.Tor.chartPullPull _ _ _ rfl) (-t)) (Geo.Tor.ch …`.
-/
theorem exists_lineBundle_of_thickenings : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (B : Over (Spec (CommRingCat.of R))) (b : ∀ e, (Y e).left ⟶ B.left), IsProjBy B.hom → Flat B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → ∃ M : LB B.left, M.IsLB ∧ ∀ e, LBIso (N e) (M.pull (b e)) := by
  intro R _ _ _ I hI hcomp Y β hβ B b hB hfl hb hc N v hN
  obtain ⟨H, hH, m, σ, hσ⟩ := id hB
  have hL : ∀ e, (H.pull (b e)).IsLB := fun e => pull_isLB hH _
  choose σ' hva using fun e =>
    exists_veryAmpleBy_of_isPullback (Ideal.Quotient.mk (I ^ (e + 1))) (hb e) hH hσ
  have hI' : I ^ (0 + 1) ≠ ⊤ := by simpa using hI
  have : Nontrivial (R ⧸ I ^ (0 + 1)) := Ideal.Quotient.nontrivial_iff.2 hI'
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal (R ⧸ I ^ (0 + 1))
  let _ := Ideal.Quotient.field 𝔪
  have hπ := IsPullback.of_hasPullback (Y 0).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔪)))
  generalize pullback.snd (Y 0).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔪))) = f₀ at hπ
  generalize pullback.fst (Y 0).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔪))) = π at hπ
  obtain ⟨σ₀, hσ₀⟩ := exists_veryAmpleBy_of_isPullback (Ideal.Quotient.mk 𝔪) hπ (hL 0) (hva 0)
  obtain ⟨t₁, ht₁⟩ := GlobalTheory.AbLaw.serre_h1Zero_and_sections_polynomial.1 _ _ _ _ _ _ (pull_isLB (hL 0) π) hσ₀ ((N 0).pull π) (pull_isLB (hN 0).1 π)
  obtain ⟨t₂, ht₂⟩ := GlobalTheory.TwistGen.twist_generated _ _ _ _ _ _ (hL 0) (hva 0) (N 0) (hN 0).1
  obtain ⟨t, h₁, h₂⟩ : ∃ t, t₁ ≤ t ∧ t₂ ≤ t := ⟨max t₁ t₂, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨n, u, hu⟩ := ht₂ t h₂
  have hT : ∀ e, (tw (N e) (H.pull (b e)) t).IsLB := fun e => isLB_tw (hN e).1 (hL e) t
  have hv' : ∀ e, LBIso (tw (N e) (H.pull (b e)) t) ((tw (N (e + 1)) (H.pull (b (e + 1))) t).pull (β e)) :=
    fun e => LBIso.trans (hT e) (isLB_tw (pull_isLB (hN (e + 1)).1 _) (hL e) t) (pull_isLB (hT (e + 1)) _)
      (lbIso_tw_congr (hL e) t ⟨v e, (hN e).2⟩)
      (LBIso.chartPull (chartPullTw (Geo.Tor.chartPullPull _ _ _ rfl)
        (chartPullSame H _ _ _ (β e) fun _ => (hc e).symm) t) (Geo.Tor.chartPullPull _ _ _ rfl)
        (lbIso_self (hT (e + 1))))
  choose v' hv' using hv'
  have hflY : ∀ e, Flat (Y e).hom := fun e => MorphismProperty.of_isPullback (P := @Flat) (hb e) hfl
  have hP : ∀ e, IsProjBy (Y e).hom := fun e => ⟨_, hL e, m, σ' e, hva e⟩
  obtain ⟨w₀, hw₀⟩ : LBIso (tw ((N 0).pull π) ((H.pull (b 0)).pull π) t) ((tw (N 0) (H.pull (b 0)) t).pull π) :=
    LBIso.chartPull (chartPullTw (Geo.Tor.chartPullPull _ _ _ rfl) (Geo.Tor.chartPullPull _ _ _ rfl) t)
      (Geo.Tor.chartPullPull _ _ _ rfl) (lbIso_self (hT 0))
  choose s hs0 hs using fun j => GlobalTheory.SecLifts.exists_compatible_sections_local R I hI Y β hβ hflY hP
    (fun e => tw (N e) (H.pull (b e)) t) v' (fun e => ⟨hT e, hv' e⟩) _ (Ideal.Quotient.mk 𝔪)
    Ideal.Quotient.mk_surjective _ π f₀ hπ _ w₀ (isLB_tw (pull_isLB (hN 0).1 π) (pull_isLB (hL 0) π) t) hw₀
    (ht₁ t h₁) (u j)
  obtain ⟨M, hM, hNM⟩ := GlobalTheory.GenSystem.exists_lb_of_generated_system R I hI hcomp Y β hβ B b hB hfl hb hc
    (fun e => tw (N e) (H.pull (b e)) t) v' (fun e => ⟨hT e, hv' e⟩) n (fun e j => s j e) (fun e j => hs j e)
    (by simpa only [hs0] using hu)
  have hM' : (tw M H (-t)).IsLB := isLB_tw hM hH _
  refine ⟨tw M H (-t), hM', fun e => ?_⟩
  have hO' : (tw (M.pull (b e)) (H.pull (b e)) (-t)).IsLB := isLB_tw (pull_isLB hM _) (hL e) _
  exact LBIso.trans (hN e).1 hO' (pull_isLB hM' _)
    (LBIso.trans (hN e).1 (isLB_tw (hT e) (hL e) _) hO' (lbIso_tw_tw (hN e).1 (hL e) t)
      (lbIso_tw_congr (hL e) (-t) (hNM e)))
    (LBIso.chartPull (chartPullTw (Geo.Tor.chartPullPull _ _ _ rfl) (Geo.Tor.chartPullPull _ _ _ rfl) (-t))
      (Geo.Tor.chartPullPull _ _ _ rfl) (lbIso_self hM'))

end GlobalTheory.LBAlgLocal
