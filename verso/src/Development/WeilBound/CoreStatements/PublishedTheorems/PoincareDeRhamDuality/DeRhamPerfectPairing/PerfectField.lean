import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechRepresentativeChernClassTangentValueStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.EqOneOfIsRep
import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.FinrankOfRankAtStalk

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace CrystallinePoints.Pd

/- English proof (translation)
Use `haveI := hA.comm`. Take `⟨I, _, c, ω, hω, hch, hψf⟩` from `chern_eq_sum hF hH hA hg hψ hiso`. Take `⟨hfin, -, hrk⟩` from `AbelianDeRham.Free.prim hF hA hg`. Take `⟨hLie, -, -, -, hrkF⟩` from `hH K A g hA hg`. Establish `d1 : Module.finrank K (primDR A) = 2 * g` using `finrank_of_rankAtStalk hrk`.

Establish `d2 : Module.finrank K (PrimitiveSubmodule A) = g` using `finrank_of_rankAtStalk hrkF`. Establish `d3 : Module.finrank K (Fil A) = g`. Use `Subspace.finrank_add_finrank_dualAnnihilator_eq (PrimitiveSubmodule A)` as an intermediate fact. Rewrite `this` using `[d1, d2]`. Express the relevant statement in the definitionally equal form `g + Module.finrank K (Fil A) = _ at this`.

Use linear arithmetic over natural numbers and integers. Use `perf_of_lag (Fil A) g (Subspace.dual_finrank_eq.trans d1) d3 ψ hψ.isAlt hiso fun x hx ↦ ?_` and prove the remaining obligations. Take `⟨v, hv, -⟩` from `hLie.1 x`. Use `choose z hz using fun k ↦ H1.mk_surjective _ (c k).1`. Establish `hmem : ∑ k, tanVal v (ω k) • c k ∈ PrimitiveSubmodule A`.

Rewrite using `[← Subspace.dualAnnihilator_dualCoannihilator_eq (W := PrimitiveSubmodule A), Submodule.mem_dualCoannihilator]`. Introduce `f hf`. Establish `e` using `hx f hf`. Rewrite `e` using `[hψf f hf]`. Rewrite using `[← e, map_sum]`.

Use `Finset.sum_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, hv.2 (ω k) (hω k), _root_.mul_comm]`. Establish `hch' : IsChern (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L (∑ k, cup _ (H1.mk _ (z k)) (Form.cl _ (ω k)))`. Simplify `hch` using `only [hz]`. Set `J : Type` to `{p : A.left.affineOpens × L.ι // p.1.1 ≤ L.U p.2}`.

Establish `hr` using `GlobalTheory.T.isCechRepresentative_chernClass_tangentValue K A hA L hL I z ω hch' v hv.1 J (fun j ↦ j.1.1) (fun j ↦ j.1.2) fun j ↦ j.2`. Establish `hcov : ⨆ j : J, j.1.1.1 = ⊤`. Use `eq_top_iff.2 fun p _ ↦ ?_` and prove the remaining obligations. Take `⟨k, hk⟩` from `TopologicalSpace.Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ p))`. Take `⟨U, hU, hp, hle⟩` from `exists_isAffineOpen_mem_and_subset (U := L.U k) hk`.

Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨U, hU⟩, k), hle⟩, hp⟩`. Establish `h1 : v = 1` using `eq_one_of_isRep hL hK hv.1 _ hcov _ (fun j ↦ j.2) _ hr (by`. Use `Submodule.mem_comap.1 hmem` as an intermediate fact. Simplify using `only [map_sum, map_smul] at this`. Simplify using `only [map_sum, map_smul, hz]`.

Conclude with `this)`. Substitute `h1` using the available equality. Conclude with `isLieImage_one_iff.1 hv`.
-/
theorem perfect_field (hF : AbelianDeRham.Free) (hH : AbelianDeRham.Hodge) {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) {L : LB A.left} (hL : L.IsLB) {ψ : LinearMap.BilinForm K (HdR A)} (hψ : IsPolForm (dp0 K) (𝟙 _) A L ψ) (hiso : ∀ x ∈ Fil A, ∀ y ∈ Fil A, ψ x y = 0) (hK : ReciprocityTheory.ChartRestriction.G.Out.KTriv A L) : LinearMap.IsPerfPair ψ := by
  classical
  haveI := hA.comm
  obtain ⟨I, _, c, ω, hω, hch, hψf⟩ := chern_eq_sum hF hH hA hg hψ hiso
  obtain ⟨hfin, -, hrk⟩ := AbelianDeRham.Free.prim hF hA hg
  obtain ⟨hLie, -, -, -, hrkF⟩ := hH K A g hA hg
  have d1 : Module.finrank K (primDR A) = 2 * g := finrank_of_rankAtStalk hrk
  have d2 : Module.finrank K (PrimitiveSubmodule A) = g := finrank_of_rankAtStalk hrkF
  have d3 : Module.finrank K (Fil A) = g := by
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq (PrimitiveSubmodule A)
    rw [d1, d2] at this
    change g + Module.finrank K (Fil A) = _ at this
    omega
  refine perf_of_lag (Fil A) g (Subspace.dual_finrank_eq.trans d1) d3 ψ hψ.isAlt hiso fun x hx ↦ ?_
  obtain ⟨v, hv, -⟩ := hLie.1 x
  choose z hz using fun k ↦ H1.mk_surjective _ (c k).1
  have hmem : ∑ k, tanVal v (ω k) • c k ∈ PrimitiveSubmodule A := by
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := PrimitiveSubmodule A), Submodule.mem_dualCoannihilator]
    intro f hf
    have e := hx f hf
    rw [hψf f hf] at e
    rw [← e, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_smul, smul_eq_mul, hv.2 (ω k) (hω k), _root_.mul_comm]
  have hch' : IsChern (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L (∑ k, cup _ (H1.mk _ (z k)) (Form.cl _ (ω k))) := by
    simpa only [hz] using hch
  let J : Type := {p : A.left.affineOpens × L.ι // p.1.1 ≤ L.U p.2}
  have hr := GlobalTheory.T.isCechRepresentative_chernClass_tangentValue K A hA L hL I z ω hch' v hv.1 J (fun j ↦ j.1.1) (fun j ↦ j.1.2) fun j ↦ j.2
  have hcov : ⨆ j : J, j.1.1.1 = ⊤ := by
    refine eq_top_iff.2 fun p _ ↦ ?_
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ p))
    obtain ⟨U, hU, hp, hle⟩ := exists_isAffineOpen_mem_and_subset (U := L.U k) hk
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨U, hU⟩, k), hle⟩, hp⟩
  have h1 : v = 1 := eq_one_of_isRep hL hK hv.1 _ hcov _ (fun j ↦ j.2) _ hr (by
    have := Submodule.mem_comap.1 hmem
    simp only [map_sum, map_smul] at this
    simp only [map_sum, map_smul, hz]
    exact this)
  subst h1
  exact isLieImage_one_iff.1 hv

end CrystallinePoints.Pd
