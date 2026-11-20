import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeStableUnderActionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EventuallyOneTmulAdicIntegralCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

open GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.LieVB

section Frame

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {V : Type} [AddCommGroup V]
  [Module Ω V] {K : Type} [Field K]

/- English proof (translation)
Take `⟨hs, v, hv, rfl⟩` from `(M.valAt_iff z e w).1 h`. Use `(M.valAt_iff z _ _).2 ⟨hs, v ≫ f, ?_, by rw [Category.assoc]⟩` and prove the remaining obligations. Rewrite `hv`, the goal using `[LieModel.extends_iff]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `(isTanAt_iff v).1 hv.1`.

Use `(isTanAt_iff _).2 ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, h1, one_comp]`. Rewrite using `[hf e, hv.2, Category.assoc]`.
-/
theorem valAt_of_isDiffOf {M : LieModel G ξ V} {z : Sp K ⟶ X} (f : G ⟶ G) [IsMonHom f] (A : V →ₗ[Ω] V)
    (hf : M.IsDiffOf f A) {e : V} {w : epsAt z ⟶ G} (h : M.ValAt z e w) : M.ValAt z (A e) (w ≫ f) := by
  obtain ⟨hs, v, hv, rfl⟩ := (M.valAt_iff z e w).1 h
  refine (M.valAt_iff z _ _).2 ⟨hs, v ≫ f, ?_, by rw [Category.assoc]⟩
  rw [LieModel.extends_iff] at hv ⊢
  refine ⟨?_, ?_⟩
  · have h1 := (isTanAt_iff v).1 hv.1
    refine (isTanAt_iff _).2 ?_
    rw [← Category.assoc, h1, one_comp]
  · rw [hf e, hv.2, Category.assoc]

/- English proof (translation)
Take `⟨F, _, _, ⟨MF⟩⟩` from `lieModel_exists X G K z`. Take `⟨ev, hev, hsm, hsp⟩` from `GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ V M K z h F MF hξ inferInstance`. Establish `hmem : ∀ i, ℓ i ∈ M.lat ⟨_, h⟩` using `fun i => by`. Rewrite using `[hℓ.2]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`.

Set `u : Fin g → F` to `fun i => ev ⟨ℓ i, hmem i⟩`. Establish `hcomb : ∀ x : Fin g → regAt ξ ⟨_, h⟩, comb ℓ x ∈ M.lat ⟨_, h⟩` using `fun x => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (x i) (hmem i)`. Establish `hevc : ∀ x : Fin g → regAt ξ ⟨_, h⟩, ev ⟨comb ℓ x, hcomb x⟩ = ∑ i, ψ (x i) • u i`. Introduce `x`. Establish `e1 : (⟨comb ℓ x, hcomb x⟩ : M.lat ⟨_, h⟩) = ∑ i, x i • (⟨ℓ i, hmem i⟩ : M.lat ⟨_, h⟩)`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[comb]`. Both sides reduce to the same expression. Rewrite using `[e1, map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => hsm (x i) (ψ (x i)) _ (hψ (x i))`.

Establish `hle : ⊤ ≤ Submodule.span K (Set.range u)`. Establish `hr : Set.range ev ⊆ (Submodule.span K (Set.range u) : Set F)`. Introduce and unpack `_ ⟨⟨e, he⟩, rfl⟩`. Establish `he'` using `he`. Rewrite `he'` using `[hℓ.2, Submodule.mem_span_range_iff_exists_fun]`.

Take `⟨x, rfl⟩` from `he'`. Establish `e2 : (∑ i, x i • ℓ i) = comb ℓ x` using `rfl`. Simplify using `only [e2]`. Rewrite using `[hevc x]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Rewrite using `[← hsp]`. Conclude with `Submodule.span_le.2 hr`. Establish `hcard : Fintype.card (Fin g) = Module.finrank K F`. Take `⟨_, hU, b', hb'sp, hb'⟩` from `(lieLat_isVB_of_smooth X Ω ξ G V M hξ inferInstance).1 ⟨_, h⟩ trivial`. Establish `hfr` using `hb' ⟨_, h⟩ trivial hU`.

Establish `htop : Submodule.span Ω (Set.range ℓ) = ⊤`. Rewrite using `[eq_top_iff, ← hb'sp, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `h3 : b' i ∈ M.lat ⟨_, h⟩`. Rewrite using `[hfr.2]`.

Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Rewrite `h3` using `[hℓ.2, Submodule.mem_span_range_iff_exists_fun]`. Take `⟨x, hx⟩` from `h3`. Rewrite using `[← hx]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Establish `hg : Module.finrank Ω V = g`. Rewrite using `[← finrank_top, ← htop, finrank_span_eq_card hℓ.1, Fintype.card_fin]`. Take `⟨R', _, x, hx, F', _, _, MR, n, b, hp⟩` from `exists_chart G (centre z)`. Establish `hgen : genPt ξ ∈ x.opensRange` using `h.mem_open x.opensRange.isOpen hp`. Take `⟨φ, hφ⟩` from `exists_lift x ξ hgen`.

Take `⟨a, ha⟩` from `exists_lift x z hp`. Take `⟨β, B, -, -⟩` from `basis_tr a x z ha MR MF b`. Take `⟨c, hli, hsp', -⟩` from `frame_of_basis x MR b ξ M φ hφ`. Establish `hn : n = Module.finrank Ω V`. Rewrite using `[Module.finrank_eq_card_basis (Module.Basis.mk hli hsp'.ge), Fintype.card_fin]`.

Rewrite using `[Module.finrank_eq_card_basis B, Fintype.card_fin, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers. Set `bb : Module.Basis (Fin g) K F` to `basisOfTopLeSpanOfCardEqFinrank u hle hcard`. Use `⟨lieModelOfEquiv MF bb.equivFun.symm, fun x => ?_⟩` and prove the remaining obligations. Establish `e3 : bb.equivFun.symm (fun i => ψ (x i)) = ev ⟨comb ℓ x, hcomb x⟩`.

Rewrite using `[hevc, Module.Basis.equivFun_symm_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => by simp [bb]`. Express the relevant statement in the definitionally equal form `M.ValAt z (comb ℓ x) (MF.pt (bb.equivFun.symm fun i => ψ (x i)))`. Rewrite using `[e3]`. Conclude with `(hev _ _).2 ⟨hcomb x, rfl⟩`.
-/
theorem exists_model_of_frame [IsCommMonObj G] [Smooth G.hom] (hξ : IsCptGen ξ) (M : LieModel G ξ V) (z : Sp K ⟶ X)
    (h : genPt ξ ⤳ centre z) (ψ : regAt ξ ⟨_, h⟩ →+* K) (hψ : ∀ a : regAt ξ ⟨_, h⟩, ValAt ξ z (a : Ω) (ψ a)) {g : ℕ}
    (ℓ : Fin g → V) (hℓ : M.lat.IsFrameAt ℓ ⟨_, h⟩) :
    ∃ MY : LieModel G z (Fin g → K), ∀ x : Fin g → regAt ξ ⟨_, h⟩,
      M.ValAt z (comb ℓ x) (MY.pt fun i => ψ (x i)) := by
  obtain ⟨F, _, _, ⟨MF⟩⟩ := lieModel_exists X G K z
  obtain ⟨ev, hev, hsm, hsp⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ V M K z h F MF hξ inferInstance
  have hmem : ∀ i, ℓ i ∈ M.lat ⟨_, h⟩ := fun i => by
    rw [hℓ.2]
    exact Submodule.subset_span ⟨i, rfl⟩
  let u : Fin g → F := fun i => ev ⟨ℓ i, hmem i⟩
  have hcomb : ∀ x : Fin g → regAt ξ ⟨_, h⟩, comb ℓ x ∈ M.lat ⟨_, h⟩ := fun x =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (x i) (hmem i)
  have hevc : ∀ x : Fin g → regAt ξ ⟨_, h⟩, ev ⟨comb ℓ x, hcomb x⟩ = ∑ i, ψ (x i) • u i := by
    intro x
    have e1 : (⟨comb ℓ x, hcomb x⟩ : M.lat ⟨_, h⟩) = ∑ i, x i • (⟨ℓ i, hmem i⟩ : M.lat ⟨_, h⟩) := by
      apply Subtype.ext
      simp [comb]
      rfl
    rw [e1, map_sum]
    exact Finset.sum_congr rfl fun i _ => hsm (x i) (ψ (x i)) _ (hψ (x i))
  have hle : ⊤ ≤ Submodule.span K (Set.range u) := by
    have hr : Set.range ev ⊆ (Submodule.span K (Set.range u) : Set F) := by
      rintro _ ⟨⟨e, he⟩, rfl⟩
      have he' := he
      rw [hℓ.2, Submodule.mem_span_range_iff_exists_fun] at he'
      obtain ⟨x, rfl⟩ := he'
      have e2 : (∑ i, x i • ℓ i) = comb ℓ x := rfl
      simp only [e2]
      rw [hevc x]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [← hsp]
    exact Submodule.span_le.2 hr
  have hcard : Fintype.card (Fin g) = Module.finrank K F := by
    obtain ⟨_, hU, b', hb'sp, hb'⟩ := (lieLat_isVB_of_smooth X Ω ξ G V M hξ inferInstance).1 ⟨_, h⟩ trivial
    have hfr := hb' ⟨_, h⟩ trivial hU
    have htop : Submodule.span Ω (Set.range ℓ) = ⊤ := by
      rw [eq_top_iff, ← hb'sp, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have h3 : b' i ∈ M.lat ⟨_, h⟩ := by
        rw [hfr.2]
        exact Submodule.subset_span ⟨i, rfl⟩
      rw [hℓ.2, Submodule.mem_span_range_iff_exists_fun] at h3
      obtain ⟨x, hx⟩ := h3
      rw [← hx]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hg : Module.finrank Ω V = g := by
      rw [← finrank_top, ← htop, finrank_span_eq_card hℓ.1, Fintype.card_fin]
    obtain ⟨R', _, x, hx, F', _, _, MR, n, b, hp⟩ := exists_chart G (centre z)
    have hgen : genPt ξ ∈ x.opensRange := h.mem_open x.opensRange.isOpen hp
    obtain ⟨φ, hφ⟩ := exists_lift x ξ hgen
    obtain ⟨a, ha⟩ := exists_lift x z hp
    obtain ⟨β, B, -, -⟩ := basis_tr a x z ha MR MF b
    obtain ⟨c, hli, hsp', -⟩ := frame_of_basis x MR b ξ M φ hφ
    have hn : n = Module.finrank Ω V := by
      rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp'.ge), Fintype.card_fin]
    rw [Module.finrank_eq_card_basis B, Fintype.card_fin, Fintype.card_fin]
    omega
  let bb : Module.Basis (Fin g) K F := basisOfTopLeSpanOfCardEqFinrank u hle hcard
  refine ⟨lieModelOfEquiv MF bb.equivFun.symm, fun x => ?_⟩
  have e3 : bb.equivFun.symm (fun i => ψ (x i)) = ev ⟨comb ℓ x, hcomb x⟩ := by
    rw [hevc, Module.Basis.equivFun_symm_apply]
    exact Finset.sum_congr rfl fun i _ => by simp [bb]
  change M.ValAt z (comb ℓ x) (MF.pt (bb.equivFun.symm fun i => ψ (x i)))
  rw [e3]
  exact (hev _ _).2 ⟨hcomb x, rfl⟩

/- English proof (translation)
Take `⟨ρ', hρ', -⟩` from `lieModel_exists_unique_act _ G K z _ MY (𝓞 E) act.act act.hom act.one act.mul act.add`. It suffices to establish `hq : ρ' = ρK from hq ▸ hρ'`. Use `RingHom.ext fun a => (Pi.basisFun K (Fin g)).ext fun i => ?_` and prove the remaining obligations. Set `x : Fin g → regAt ξ ⟨_, h⟩` to `Pi.single i 1`. Establish `hx : (fun j => ψ (x j)) = Pi.basisFun K (Fin g) i`.

Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `[x]`. Simplify using `[x, hj]`.

Establish `hmem : ρ a (comb ℓ x) ∈ M.lat ⟨_, h⟩`. Use `GlobalTheory.T.lie_lattice_stable_under_action X Ω ξ G V M (𝓞 E) act ρ hact ⟨_, h⟩ a _ ?_` and prove the remaining obligations. Rewrite using `[hℓ.2]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Rewrite `hmem` using `[hℓ.2, Submodule.mem_span_range_iff_exists_fun]`.

Take `⟨x', hx'⟩` from `hmem`. Establish `hc : comb ℓ x' = ρ a (comb ℓ x)` using `hx'`. Use `act.hom a` as an intermediate fact. Establish `h1 : M.ValAt z (ρ a (comb ℓ x)) (MY.pt (fun j => ψ (x j)) ≫ act.act a)` using `valAt_of_isDiffOf (act.act a) (ρ a) (hact a) (hY x)`. Establish `h2` using `hY x'`.

Rewrite `h2` using `[hc]`. Establish `h3` using `h2.unique hξ h1`. Rewrite `h3` using `[← hρ' a]`. Establish `h4` using `MY.inj h3`. Rewrite using `[← hx, ← h4]`.

Conclude with `(hT a x x' hc.symm).symm`.
-/
theorem isActOf_of_frame {E : Type} [Field E] [NumberField E] (hξ : IsCptGen ξ) {M : LieModel G ξ V} {z : Sp K ⟶ X}
    {h : genPt ξ ⤳ centre z} {ψ : regAt ξ ⟨_, h⟩ →+* K} {g : ℕ} {ℓ : Fin g → V}
    (hℓ : M.lat.IsFrameAt ℓ ⟨_, h⟩) (act : OAct (𝓞 E) G) {ρ : 𝓞 E →+* Module.End Ω V}
    (hact : M.IsActOf act.act ρ) {ρK : 𝓞 E →+* Module.End K (Fin g → K)} (hT : Tied ℓ ψ ρ ρK)
    {MY : LieModel G z (Fin g → K)}
    (hY : ∀ x : Fin g → regAt ξ ⟨_, h⟩, M.ValAt z (comb ℓ x) (MY.pt fun i => ψ (x i))) :
    MY.IsActOf act.act ρK := by
  obtain ⟨ρ', hρ', -⟩ := lieModel_exists_unique_act _ G K z _ MY (𝓞 E) act.act act.hom act.one act.mul act.add
  suffices hq : ρ' = ρK from hq ▸ hρ'
  refine RingHom.ext fun a => (Pi.basisFun K (Fin g)).ext fun i => ?_
  let x : Fin g → regAt ξ ⟨_, h⟩ := Pi.single i 1
  have hx : (fun j => ψ (x j)) = Pi.basisFun K (Fin g) i := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [x]
    · simp [x, hj]
  have hmem : ρ a (comb ℓ x) ∈ M.lat ⟨_, h⟩ := by
    refine GlobalTheory.T.lie_lattice_stable_under_action X Ω ξ G V M (𝓞 E) act ρ hact ⟨_, h⟩ a _ ?_
    rw [hℓ.2]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [hℓ.2, Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨x', hx'⟩ := hmem
  have hc : comb ℓ x' = ρ a (comb ℓ x) := hx'
  have := act.hom a
  have h1 : M.ValAt z (ρ a (comb ℓ x)) (MY.pt (fun j => ψ (x j)) ≫ act.act a) :=
    valAt_of_isDiffOf (act.act a) (ρ a) (hact a) (hY x)
  have h2 := hY x'
  rw [hc] at h2
  have h3 := h2.unique hξ h1
  rw [← hρ' a] at h3
  have h4 := MY.inj h3
  rw [← hx, ← h4]
  exact (hT a x x' hc.symm).symm

end Frame

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O _ _ _ β Y U Z K _ y h₁ ψ g ℓ ρK hψ hℓ hT`. Establish `: Smooth Y.t.G.hom` using `Y.t.semi.smooth`. Take `⟨MY, hMY⟩` from `exists_model_of_frame Z.gen Z.M (y ≫ Y.j) h₁ ψ hψ ℓ hℓ`. Establish `hY : MY.IsActOf Y.t.act.act ρK` using `isActOf_of_frame Z.gen hℓ Y.t.act Z.act hT hMY`. Establish `hp : IsGrpPullback Y.oF.t.G Xo.univ.t.G (pullback.fst _ _) Y.m0.toSABMap.φ` using `Y.m0.cart`.

Establish `hq : IsGrpPullback Y.oF.t.G Y.t.G Y.j Y.m.φ` using `Y.m.cart`. Take `⟨Mo, hMo⟩` from `(LiePull.lieModel_pullback _ _ Y.t.G Y.oF.t.G Y.j Y.m.φ hq K y (Fin g → K)).1 MY`. Take `⟨MU, hMU⟩` from `(LiePull.lieModel_pullback _ _ Xo.univ.t.G Y.oF.t.G (pullback.fst _ _) Y.m0.toSABMap.φ hp K y (Fin g → K)).2 Mo`. Establish `hMoAct : ∀ (a : 𝓞 E) (e : Fin g → K), Mo.pt (ρK a e) = Mo.pt e ≫ Y.oF.t.act.act a`. Introduce `a e`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `hq.1.hom_ext` to reduce the goal to its premises. Rewrite using `[hMo, hY a e, Over.comp_left, Over.comp_left, Category.assoc, Y.m.act, ← Category.assoc, hMo]`. Rewrite using `[Over.w, Over.comp_left, Category.assoc, Over.w, Over.w]`. Use `⟨MU, MY, fun e => ⟨(Mo.pt e).left, Over.w (Mo.pt e), hMU e, hMo e⟩, hMY, fun a e => ?_, hY⟩` and prove the remaining obligations.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[← hMU, hMoAct a e, Over.comp_left, Over.comp_left, Category.assoc, Y.m0.act, ← Category.assoc, hMU]`.
-/
theorem tangent_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (K : Type) [Field K] (y : Sp K ⟶ Xo.XF c) (h₁ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j))
    (ψ : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ →+* K) (g : ℕ) (ℓ : Fin g → Z.V) (ρK : 𝓞 E →+* Module.End K (Fin g → K)),
    (∀ a : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (a : Z.Ω) (ψ a)) → Z.M.lat.IsFrameAt ℓ ⟨_, h₁⟩ → Tied ℓ ψ Z.ρ ρK →
    ∃ (MU : LieModel Xo.univ.t.G (under y) (Fin g → K)) (MY : LieModel Y.t.G (y ≫ Y.j) (Fin g → K)),
      (∀ e, SameVec Y y (MU.pt e) (MY.pt e)) ∧
      (∀ x : Fin g → regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, Z.M.ValAt (y ≫ Y.j) (comb ℓ x) (MY.pt (fun i => ψ (x i)))) ∧
      MU.IsActOf Xo.univ.t.act.act ρK ∧ MY.IsActOf Y.t.act.act ρK := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y U Z K _ y h₁ ψ g ℓ ρK hψ hℓ hT
  have : Smooth Y.t.G.hom := Y.t.semi.smooth
  obtain ⟨MY, hMY⟩ := exists_model_of_frame Z.gen Z.M (y ≫ Y.j) h₁ ψ hψ ℓ hℓ
  have hY : MY.IsActOf Y.t.act.act ρK := isActOf_of_frame Z.gen hℓ Y.t.act Z.act hT hMY
  have hp : IsGrpPullback Y.oF.t.G Xo.univ.t.G (pullback.fst _ _) Y.m0.toSABMap.φ := Y.m0.cart
  have hq : IsGrpPullback Y.oF.t.G Y.t.G Y.j Y.m.φ := Y.m.cart
  obtain ⟨Mo, hMo⟩ := (LiePull.lieModel_pullback _ _ Y.t.G Y.oF.t.G Y.j Y.m.φ hq K y (Fin g → K)).1 MY
  obtain ⟨MU, hMU⟩ := (LiePull.lieModel_pullback _ _ Xo.univ.t.G Y.oF.t.G (pullback.fst _ _) Y.m0.toSABMap.φ hp
    K y (Fin g → K)).2 Mo
  have hMoAct : ∀ (a : 𝓞 E) (e : Fin g → K), Mo.pt (ρK a e) = Mo.pt e ≫ Y.oF.t.act.act a := by
    intro a e
    apply Over.OverMorphism.ext
    apply hq.1.hom_ext
    · rw [hMo, hY a e, Over.comp_left, Over.comp_left, Category.assoc, Y.m.act, ← Category.assoc, hMo]
    · rw [Over.w, Over.comp_left, Category.assoc, Over.w, Over.w]
  refine ⟨MU, MY, fun e => ⟨(Mo.pt e).left, Over.w (Mo.pt e), hMU e, hMo e⟩, hMY, fun a e => ?_, hY⟩
  apply Over.OverMorphism.ext
  rw [← hMU, hMoAct a e, Over.comp_left, Over.comp_left, Category.assoc, Y.m0.act, ← Category.assoc, hMU]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
