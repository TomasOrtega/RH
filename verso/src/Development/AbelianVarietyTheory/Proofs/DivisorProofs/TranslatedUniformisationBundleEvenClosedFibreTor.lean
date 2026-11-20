import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreUniformisationDataIsEvenCubicalOnClosedFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalTrivTranslateOrderTwoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedCubicalBundleClosedFibreUniformisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.TransEven
open GlobalTheory.UU

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `R _ _ _ hR D A G _ _ hS U a ha P hP hsym hcub`. Establish `hG` using `GlobalTheory.firstFiveLaws.1.globalFns`. Take `⟨wA, hwA⟩` from `U.ext`. Set `U'` to `GlobalTheory.ValueForm.toPreU U.toUnifPre hG hS wA hwA`. Use `set g := U.gt 0 with hg`.

Use `g.q_hom` as an intermediate fact. Use `g.i_hom` as an intermediate fact. Use `g.q_flat` as an intermediate fact. Use `g.q_surj` as an intermediate fact. Use `g.q_affine` as an intermediate fact.

Establish `hB : IsAbelianScheme (thickObj R (maximalIdeal R) 0 D.toPre.P.A)` using `GlobalTheory.isAbelianScheme_pullback_obj _ _ D.toPre.P.isAb`. Use `hB.comm` as an intermediate fact. Take `⟨O, h₁, h₂, h₃, hd⟩` from `GlobalTheory.exists_gtDatum_of_splitTorus_extension _ D.toPre.X (thickObj R (maximalIdeal R) 0 G) (thickObj R (maximalIdeal R) 0 D.toPre.P.A) hB g.q g.i g.q_hom g.i_hom g.q_flat g.q_surj inferInstance g.isKernel`. Take `⟨d, hdq, hdi⟩` from `hd hB`. Set `Q : TQ (thickObj R (maximalIdeal R) 0 G) D.toPre.X` to `{ B := thickObj R (maximalIdeal R) 0 D.toPre.P.A isAb := hB q := g.q i := g.i q_hom := g.q_hom i_hom := g.i_hom q_flat := g.q_flat q_surj := g.q_surj q_affine := g.q_affine isKernel := g.isKernel loc := by`.

Establish `l` using `(TQ.ofGtDatum d).loc`. Rewrite `l` using `[show (TQ.ofGtDatum d).q = g.q from hdq, show (TQ.ofGtDatum d).i = g.i from hdi]`. Conclude with `l }`. Take `⟨P₀, hlev⟩` from `exists_isLevelCP (maximalIdeal R) 0 U'.P`. Establish `hlev'` using `hlev`.

Take `⟨w₀, h₀⟩` from `hlev`. Take `⟨rig, hr, c, σ, h₁, h₂, h₃, H⟩` from `exists_isCPMap U'.P (toBase_mul_pullback G (thick R (maximalIdeal R) 0)) _ (pull_isLB U'.P.L.isLB _) _ (pullIso_isGen U'.P.L.isLB (pullback.fst G.hom (thick R (maximalIdeal R) 0)))`. Take `⟨w₁, k₁⟩` from `GlobalTheory.ClosedPol.cpMap_congr (Category.id_comp _).symm (Category.id_comp _).symm h₀ (by rw [Category.id_comp, Category.id_comp]; exact pullback.condition)`. Take `⟨w₂, k₂, -⟩` from `(isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ P₀ _ _ _ (𝟙 _) (by simp) _ H).2 (toBase_mul_of_isMonHom (𝟙 _) _) w₁ k₁`. Establish `H'` using `GlobalTheory.ClosedPol.isCPMap_w hG U' 0 H`.

Take `⟨w₃, -, k₃⟩` from `H'.exists_comp k₂ (by rw [Category.id_comp, Category.id_comp]; exact Over.w (U'.gt 0).pG)`. Take `⟨M, wM, hM⟩` from `exists_isLevelCP (maximalIdeal R) 0 (CP.ofDegPre hG D.toPre)`. Take `⟨w₄, k₄⟩` from `GlobalTheory.ClosedPol.cpMap_congr rfl (Category.id_comp _) k₃ (by rw [Category.assoc, pullback.condition, Category.id_comp]; simpa using Over.w (U'.gt 0).pG)`. Take `⟨w₅, k₅, -⟩` from `(isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ M P₀ _ _ _ g.q.left ((Over.w g.q).trans (Category.comp_id _).symm) _ hM).2 (toBase_mul_of_isMonHom g.q _) w₄ k₄`. Establish `De : Q.Desc P₀` using `⟨M, w₅, k₅⟩`.

Take `⟨a₀, P', -, ha₀, hl', hL', hs', hc'⟩` from `GlobalTheory.T.translatedCubicalBundle_closedFibre_uniformisation R D A G U a ha P hP hsym hcub P₀ hlev'`. Take `⟨σ', hσ'⟩` from `GlobalTheory.T.exists_even_cubicalTriv_translate_order_two _ _ D.toPre.X Q P₀ ⟨De⟩ a₀ ha₀ P' hL' hs' hc'`. Conclude with `⟨D.toPre.X, inferInstance, inferInstance, inferInstance, Q, P', hl', σ', hσ'⟩`.
-/
theorem evenOn_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 →
    ∀ P : GlobalTheory.UU.CP G, P.L.L = U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left →
      (∀ (T : Over (Sp R)) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val U.symG ((toUnit T ≫ a) * x).left z J * (val U.symG (toUnit T ≫ a).left z J)⁻¹) →
      (∀ (T : Over (Sp R)) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV U.cubG z J x y ((toUnit T ≫ a) * u) * (cubV U.cubG z J x y (toUnit T ≫ a))⁻¹) →
      EvenOn P := by
  intro R _ _ _ hR D A G _ _ hS U a ha P hP hsym hcub
  have hG := GlobalTheory.firstFiveLaws.1.globalFns
  obtain ⟨wA, hwA⟩ := U.ext
  let U' := GlobalTheory.ValueForm.toPreU U.toUnifPre hG hS wA hwA
  set g := U.gt 0 with hg
  have := g.q_hom
  have := g.i_hom
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have hB : IsAbelianScheme (thickObj R (maximalIdeal R) 0 D.toPre.P.A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ D.toPre.P.isAb
  have := hB.comm
  obtain ⟨O, h₁, h₂, h₃, hd⟩ := GlobalTheory.exists_gtDatum_of_splitTorus_extension _ D.toPre.X (thickObj R (maximalIdeal R) 0 G)
    (thickObj R (maximalIdeal R) 0 D.toPre.P.A) hB g.q g.i g.q_hom g.i_hom g.q_flat g.q_surj inferInstance g.isKernel
  obtain ⟨d, hdq, hdi⟩ := hd hB
  let Q : TQ (thickObj R (maximalIdeal R) 0 G) D.toPre.X :=
    { B := thickObj R (maximalIdeal R) 0 D.toPre.P.A
      isAb := hB
      q := g.q
      i := g.i
      q_hom := g.q_hom
      i_hom := g.i_hom
      q_flat := g.q_flat
      q_surj := g.q_surj
      q_affine := g.q_affine
      isKernel := g.isKernel
      loc := by
        have l := (TQ.ofGtDatum d).loc
        rw [show (TQ.ofGtDatum d).q = g.q from hdq, show (TQ.ofGtDatum d).i = g.i from hdi] at l
        exact l }
  obtain ⟨P₀, hlev⟩ := exists_isLevelCP (maximalIdeal R) 0 U'.P
  have hlev' := hlev
  obtain ⟨w₀, h₀⟩ := hlev
  obtain ⟨rig, hr, c, σ, h₁, h₂, h₃, H⟩ := exists_isCPMap U'.P (toBase_mul_pullback G (thick R (maximalIdeal R) 0)) _
    (pull_isLB U'.P.L.isLB _) _ (pullIso_isGen U'.P.L.isLB (pullback.fst G.hom (thick R (maximalIdeal R) 0)))
  obtain ⟨w₁, k₁⟩ := GlobalTheory.ClosedPol.cpMap_congr (Category.id_comp _).symm (Category.id_comp _).symm h₀
    (by rw [Category.id_comp, Category.id_comp]; exact pullback.condition)
  obtain ⟨w₂, k₂, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ P₀ _ _ _ (𝟙 _) (by simp) _ H).2
    (toBase_mul_of_isMonHom (𝟙 _) _) w₁ k₁
  have H' := GlobalTheory.ClosedPol.isCPMap_w hG U' 0 H
  obtain ⟨w₃, -, k₃⟩ := H'.exists_comp k₂ (by rw [Category.id_comp, Category.id_comp]; exact Over.w (U'.gt 0).pG)
  obtain ⟨M, wM, hM⟩ := exists_isLevelCP (maximalIdeal R) 0 (CP.ofDegPre hG D.toPre)
  obtain ⟨w₄, k₄⟩ := GlobalTheory.ClosedPol.cpMap_congr rfl (Category.id_comp _) k₃
    (by rw [Category.assoc, pullback.condition, Category.id_comp]; simpa using Over.w (U'.gt 0).pG)
  obtain ⟨w₅, k₅, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ M P₀ _ _ _ g.q.left
    ((Over.w g.q).trans (Category.comp_id _).symm) _ hM).2
    (toBase_mul_of_isMonHom g.q _) w₄ k₄
  have De : Q.Desc P₀ := ⟨M, w₅, k₅⟩
  obtain ⟨a₀, P', -, ha₀, hl', hL', hs', hc'⟩ := GlobalTheory.T.translatedCubicalBundle_closedFibre_uniformisation R D A G U a ha P hP hsym hcub P₀ hlev'
  obtain ⟨σ', hσ'⟩ := GlobalTheory.T.exists_even_cubicalTriv_translate_order_two _ _ D.toPre.X Q P₀ ⟨De⟩ a₀ ha₀ P' hL' hs' hc'
  exact ⟨D.toPre.X, inferInstance, inferInstance, inferInstance, Q, P', hl', σ', hσ'⟩

end GlobalTheory.Mum.TransEven
