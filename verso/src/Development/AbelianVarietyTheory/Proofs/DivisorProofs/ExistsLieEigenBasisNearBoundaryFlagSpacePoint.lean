import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadGenericEigenFrameAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeNearImage
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false
noncomputable section
open scoped Matrix
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.LogPole.EigNear

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

set_option maxHeartbeats 1000000 in
open GlobalTheory.LogKSDiv.Spread GlobalTheory.ShFam.EigSpread GlobalTheory.ShFam.EigLoc GlobalTheory.LieLocBasis in

/- English proof (translation)
Take `⟨U₁, hU₁, hp₁, x₁, hx₁, C, n, xc, hx⟩` from `exists_affine_chart TF.Y.t (𝟙 TF.Y.X) p`. Set `L : Type` to `TF.Y.X.presheaf.stalk p`. Use `letI : Algebra Γ(TF.Y.X, U₁) L := TopCat.Presheaf.algebra_section_stalk TF.Y.X.presheaf ⟨p, hp₁⟩`. Establish `hloc` using `hU₁.isLocalization_stalk ⟨p, hp₁⟩`. Set `ρ₁ : Γ(TF.Y.X, U₁) →+* L` to `algebraMap _ _`.

Establish `hK : spMap ρ₁ ≫ hU₁.fromSpec = TF.Y.X.fromSpecStalk p`. Rewrite using `[← hU₁.fromSpecStalk_eq_fromSpecStalk hp₁]`. Both sides reduce to the same expression. Establish `hid : spMap (RingHom.id c.F) = 𝟙 _` using `Spec.map_id _`. Use `haveI : IsIso (spMap (RingHom.id c.F)) := by rw [hid]; infer_instance`.

Use `haveI : IsIso (GlobalTheory.Toroidal.genι TF.Y) := inferInstanceAs (IsIso (pullback.fst TF.Y.s (spMap (RingHom.id c.F))))`. Establish `hs : inv (GlobalTheory.Toroidal.genι TF.Y) ≫ GlobalTheory.Toroidal.genStr TF.Y = TF.Y.s`. Rewrite using `[IsIso.inv_comp_eq]`. Combine the equalities or inequalities in the displayed calculation. Set `φ₀ : c.F →+* L` to `(Spec.preimage (TF.Y.X.fromSpecStalk p ≫ TF.Y.s)).hom`.

Establish `hφ₀ : spMap φ₀ = TF.Y.X.fromSpecStalk p ≫ TF.Y.s` using `Spec.map_preimage _`. Take `⟨f₀'⟩` from `GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c c.F (RingHom.id c.F) TF.Y L φ₀ (TF.Y.X.fromSpecStalk p ≫ inv (GlobalTheory.Toroidal.genι TF.Y)) (by rw [Category.assoc, hs, hφ₀])`. Establish `e0 : (TF.Y.X.fromSpecStalk p ≫ inv (GlobalTheory.Toroidal.genι TF.Y)) ≫ GlobalTheory.Toroidal.genι TF.Y = TF.Y.X.fromSpecStalk p` using `by simp`. Take `⟨f₀⟩ : Nonempty (GlobalTheory.ShFam.EigFrame TF.Y φ₀ (TF.Y.X.fromSpecStalk p))` from `e0 ▸ ⟨f₀'⟩`. Set `φ₁` to `cst TF.Y.s U₁`.

Establish `hφ₁ : spMap φ₁ = hU₁.fromSpec ≫ TF.Y.s` using `spMap_cst _ hU₁`. Establish `hρφ : ρ₁.comp φ₁ = φ₀` using `spMap_inj (by`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp, hφ₁, ← Category.assoc, hK, hφ₀])`. Take `⟨xcK, hxK, hcK⟩` from `vec_bc_of_chart C hx ρ₁ (x' := TF.Y.X.fromSpecStalk p) (by rw [hx₁, Category.comp_id, hK])`. Take `⟨Pr, hPr⟩` from `exists_projectors c φ₁ hx`.

Use `choose Bv hBv using fun τ i => vec_exists hxK _ (f₀.tan τ i)`. Establish `hBe : ∀ τ i, Bv τ i ∈ eig c φ₀ hxK τ` using `fun τ i => (vec_eig_iff hxK _ _).1 (by rw [← hBv]; exact f₀.eig τ i)`. Establish `hPK : ∀ τ i, (Pr τ).map ρ₁ *ᵥ Bv τ i = Bv τ i` using `fun τ i => (hPr ρ₁ hxK hcK τ (Bv τ i)).2 (by rw [hρφ]; exact hBe τ i)`. Use `letI : Algebra c.F L := φ₀.toAlgebra`. Establish `hEig : ∀ z : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hxK) (embK c z.1) (Bv z.1 z.2)` using `fun z => (ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff _ _ _ _).1 (hBe z.1 z.2)`.

Establish `hblk : ∀ τ w, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hxK) (embK c τ) w → ∃! a : Fin (Dw.mult τ) → L, ∑ i, a i • Bv τ i = w` using `fun τ w hw => by`. Use `f₀.basis τ _ (vec_tan hxK w) ((vec_eig_iff hxK _ w).2 ((ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff _ _ _ _).2 hw))` as an intermediate fact. Rewrite `this` using `[show f₀.v τ = fun i => vec TF.Y.t _ xcK (Bv τ i) from funext (hBv τ)]`. Simplify `this` using `only [comb_iff hxK, eq_comm]`. Establish `hglob` using `GlobalTheory.FlagEmb.EigSpread.global_basis (GlobalTheory.FlagEmb.EigSpread.splits c) (fun z => Bv z.1 z.2) hEig hblk`.

Take `⟨hli, hsp⟩` from `(GlobalTheory.FlagEmb.EigSpread.existsUnique_iff _).1 hglob`. Set `bK` to `Module.Basis.mk hli hsp.ge`. Establish `hcard : Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) = n`. Rewrite using `[← Module.finrank_eq_card_basis bK, Module.finrank_fin_fun]`. Set `e` to `Fintype.equivFinOfCardEq hcard`.

Establish `hdet : IsUnit (Matrix.of fun i j => Bv (e.symm j).1 (e.symm j).2 i).det`. Establish `h1 : (Matrix.of fun i j => Bv (e.symm j).1 (e.symm j).2 i) = (Pi.basisFun L (Fin n)).toMatrix (bK.reindex e)`. Use extensionality with `i j`. Simplify using `[Module.Basis.toMatrix_apply, bK]`. Rewrite using `[h1]`.

Conclude with `Matrix.isUnit_det_of_right_inverse (Module.Basis.toMatrix_mul_toMatrix_flip _ _)`. Take `⟨g, hg, s0, B₀, -, hψB⟩` from `spread_exact (hU₁.primeIdealOf ⟨p, hp₁⟩).asIdeal (fun j => Bv (e.symm j).1 (e.symm j).2) hdet (fun j => Pr (e.symm j).1) (fun j => hPK _ _)`. Establish `hU : IsAffineOpen (TF.Y.X.basicOpen g)` using `hU₁.basicOpen g`. Establish `hU' : TF.Y.X.basicOpen g ∈ TF.Y.X.affineOpens` using `hU`. Establish `hpU : p ∈ TF.Y.X.basicOpen g`.

Rewrite using `[Scheme.mem_basicOpen _ _ _ hp₁]`. Conclude with `IsLocalization.map_units L (⟨g, hg⟩ : (hU₁.primeIdealOf ⟨p, hp₁⟩).asIdeal.primeCompl)`. Set `ψ : Γ(TF.Y.X, U₁) →+* Γ(TF.Y.X, TF.Y.X.basicOpen g)` to `(TF.Y.X.presheaf.map (homOfLE (TF.Y.X.basicOpen_le g)).op).hom`. Establish `hψg : IsUnit (ψ g)` using `TF.Y.X.toRingedSpace.isUnit_res_basicOpen g`. Take `⟨hs0, hdet0, hQ0⟩` from `hψB _ ψ hψg`.

Establish `hmap : spMap ψ ≫ hU₁.fromSpec = hU.fromSpec` using `hU₁.map_fromSpec hU _`. Take `⟨xcU, hxU, hcU⟩` from `vec_bc_of_chart C hx ψ (x' := LogKS.chart ⟨_, hU'⟩) (by rw [hx₁, Category.comp_id]; exact hmap.symm)`. Establish `hψφ : ψ.comp φ₁ = cst TF.Y.s (TF.Y.X.basicOpen g)` using `spMap_inj (by`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp, hφ₁, ← Category.assoc, hmap, spMap_cst _ hU])`. Set `u` to `hs0.unit`.

Set `cU : Fin n → Fin n → Γ(TF.Y.X, TF.Y.X.basicOpen g)` to `fun j => (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g)) • (ψ ∘ B₀ j)`. Establish `hdetU : IsUnit (Matrix.of fun i j => cU j i).det`. Establish `: (Matrix.of fun i j => cU j i) = (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g)) • Matrix.of fun i j => ψ (B₀ j i)`. Use extensionality with `i j`. Both sides reduce to the same expression.

Rewrite using `[this, Matrix.det_smul]`. Conclude with `(u⁻¹.isUnit.pow _).mul hdet0`. Establish `hcUd : ∀ j, cU j = (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g)) • (ψ ∘ B₀ j)` using `fun j => rfl`. Use `clear_value cU`. Use `⟨⟨_, hU'⟩, n, e, fun j => vec TF.Y.t _ xcU (cU j), hpU, fun j => vec_tan hxU _, fun w' hw' => ?_, fun a τ i => ?_⟩` and prove the remaining obligations.

Take `⟨cc, rfl⟩` from `vec_exists hxU w' hw'`. Simplify using `only [comb_iff hxU]`. Conclude with `basis_of_det cU hdetU cc`. Establish `hq` using `hQ0 (e ⟨τ, i⟩)`. Simplify using `only [Equiv.symm_apply_apply] at hq`.

Establish `hfix : (Pr τ).map ψ *ᵥ cU (e ⟨τ, i⟩) = cU (e ⟨τ, i⟩)`. Rewrite using `[hcUd, Matrix.mulVec_smul, hq]`. Establish `hmem` using `(hPr ψ hxU hcU τ (cU (e ⟨τ, i⟩))).1`. Rewrite `hmem` using `[hfix, hψφ]`. Establish `heig : vec TF.Y.t (LogKS.chart ⟨_, hU'⟩) xcU (cU (e ⟨τ, i⟩)) ≫ (TF.Y.t.act.act a).left = spMap (epsMul (cst TF.Y.s (TF.Y.X.basicOpen g) (embK c τ a))) ≫ vec TF.Y.t (LogKS.chart ⟨_, hU'⟩) xcU (cU (e ⟨τ, i⟩))` using `(vec_eig_iff hxU (fun a => cst TF.Y.s (TF.Y.X.basicOpen g) (embK c τ a)) (cU (e ⟨τ, i⟩))).2 hmem a`.

Establish `hc : IsCombAtG TF.Y.t (LogKS.chart ⟨_, hU'⟩) (fun j => vec TF.Y.t _ xcU (cU j)) (Pi.single (e ⟨τ, i⟩) (cst TF.Y.s (TF.Y.X.basicOpen g) (embK c τ a))) (vec TF.Y.t _ xcU (cst TF.Y.s (TF.Y.X.basicOpen g) (embK c τ a) • cU (e ⟨τ, i⟩)))`. Rewrite using `[comb_iff hxU, Finset.sum_eq_single (e ⟨τ, i⟩) (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul]) (fun hk => absurd (Finset.mem_univ _) hk), Pi.single_eq_same]`. Rewrite `hc` using `[vec_smul hxU, ← heig]`. Conclude with `hc`.
-/
theorem exists_eigBasis_at (TF : TorFlag Xo c) (p : TF.Y.X) :
    ∃ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
      (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), p ∈ U.1 ∧ IsEigBasis TF U e v := by
  classical
  obtain ⟨U₁, hU₁, hp₁, x₁, hx₁, C, n, xc, hx⟩ := exists_affine_chart TF.Y.t (𝟙 TF.Y.X) p
  let L : Type := TF.Y.X.presheaf.stalk p
  letI : Algebra Γ(TF.Y.X, U₁) L := TopCat.Presheaf.algebra_section_stalk TF.Y.X.presheaf ⟨p, hp₁⟩
  have hloc := hU₁.isLocalization_stalk ⟨p, hp₁⟩
  let ρ₁ : Γ(TF.Y.X, U₁) →+* L := algebraMap _ _
  have hK : spMap ρ₁ ≫ hU₁.fromSpec = TF.Y.X.fromSpecStalk p := by
    rw [← hU₁.fromSpecStalk_eq_fromSpecStalk hp₁]
    rfl
  have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  haveI : IsIso (spMap (RingHom.id c.F)) := by rw [hid]; infer_instance
  haveI : IsIso (GlobalTheory.Toroidal.genι TF.Y) := inferInstanceAs (IsIso (pullback.fst TF.Y.s (spMap (RingHom.id c.F))))
  have hs : inv (GlobalTheory.Toroidal.genι TF.Y) ≫ GlobalTheory.Toroidal.genStr TF.Y = TF.Y.s := by
    rw [IsIso.inv_comp_eq]
    calc GlobalTheory.Toroidal.genStr TF.Y = GlobalTheory.Toroidal.genStr TF.Y ≫ spMap (RingHom.id c.F) := by rw [hid, Category.comp_id]
      _ = GlobalTheory.Toroidal.genι TF.Y ≫ TF.Y.s := pullback.condition.symm
  let φ₀ : c.F →+* L := (Spec.preimage (TF.Y.X.fromSpecStalk p ≫ TF.Y.s)).hom
  have hφ₀ : spMap φ₀ = TF.Y.X.fromSpecStalk p ≫ TF.Y.s := Spec.map_preimage _
  obtain ⟨f₀'⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c c.F (RingHom.id c.F) TF.Y L φ₀
    (TF.Y.X.fromSpecStalk p ≫ inv (GlobalTheory.Toroidal.genι TF.Y)) (by rw [Category.assoc, hs, hφ₀])
  have e0 : (TF.Y.X.fromSpecStalk p ≫ inv (GlobalTheory.Toroidal.genι TF.Y)) ≫ GlobalTheory.Toroidal.genι TF.Y =
      TF.Y.X.fromSpecStalk p := by simp
  obtain ⟨f₀⟩ : Nonempty (GlobalTheory.ShFam.EigFrame TF.Y φ₀ (TF.Y.X.fromSpecStalk p)) := e0 ▸ ⟨f₀'⟩
  let φ₁ := cst TF.Y.s U₁
  have hφ₁ : spMap φ₁ = hU₁.fromSpec ≫ TF.Y.s := spMap_cst _ hU₁
  have hρφ : ρ₁.comp φ₁ = φ₀ := spMap_inj (by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp, hφ₁, ← Category.assoc, hK, hφ₀])
  obtain ⟨xcK, hxK, hcK⟩ := vec_bc_of_chart C hx ρ₁ (x' := TF.Y.X.fromSpecStalk p)
    (by rw [hx₁, Category.comp_id, hK])
  obtain ⟨Pr, hPr⟩ := exists_projectors c φ₁ hx
  choose Bv hBv using fun τ i => vec_exists hxK _ (f₀.tan τ i)
  have hBe : ∀ τ i, Bv τ i ∈ eig c φ₀ hxK τ := fun τ i => (vec_eig_iff hxK _ _).1 (by rw [← hBv]; exact f₀.eig τ i)
  have hPK : ∀ τ i, (Pr τ).map ρ₁ *ᵥ Bv τ i = Bv τ i := fun τ i =>
    (hPr ρ₁ hxK hcK τ (Bv τ i)).2 (by rw [hρφ]; exact hBe τ i)
  letI : Algebra c.F L := φ₀.toAlgebra
  have hEig : ∀ z : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hxK) (embK c z.1) (Bv z.1 z.2) :=
    fun z => (ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff _ _ _ _).1 (hBe z.1 z.2)
  have hblk : ∀ τ w, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hxK) (embK c τ) w →
      ∃! a : Fin (Dw.mult τ) → L, ∑ i, a i • Bv τ i = w := fun τ w hw => by
    have := f₀.basis τ _ (vec_tan hxK w) ((vec_eig_iff hxK _ w).2 ((ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff _ _ _ _).2 hw))
    rw [show f₀.v τ = fun i => vec TF.Y.t _ xcK (Bv τ i) from funext (hBv τ)] at this
    simpa only [comb_iff hxK, eq_comm] using this
  have hglob := GlobalTheory.FlagEmb.EigSpread.global_basis (GlobalTheory.FlagEmb.EigSpread.splits c) (fun z => Bv z.1 z.2) hEig hblk
  obtain ⟨hli, hsp⟩ := (GlobalTheory.FlagEmb.EigSpread.existsUnique_iff _).1 hglob
  let bK := Module.Basis.mk hli hsp.ge
  have hcard : Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) = n := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fin_fun]
  let e := Fintype.equivFinOfCardEq hcard
  have hdet : IsUnit (Matrix.of fun i j => Bv (e.symm j).1 (e.symm j).2 i).det := by
    have h1 : (Matrix.of fun i j => Bv (e.symm j).1 (e.symm j).2 i) =
        (Pi.basisFun L (Fin n)).toMatrix (bK.reindex e) := by
      ext i j
      simp [Module.Basis.toMatrix_apply, bK]
    rw [h1]
    exact Matrix.isUnit_det_of_right_inverse (Module.Basis.toMatrix_mul_toMatrix_flip _ _)
  obtain ⟨g, hg, s0, B₀, -, hψB⟩ := spread_exact (hU₁.primeIdealOf ⟨p, hp₁⟩).asIdeal
    (fun j => Bv (e.symm j).1 (e.symm j).2) hdet (fun j => Pr (e.symm j).1) (fun j => hPK _ _)
  have hU : IsAffineOpen (TF.Y.X.basicOpen g) := hU₁.basicOpen g
  have hU' : TF.Y.X.basicOpen g ∈ TF.Y.X.affineOpens := hU
  have hpU : p ∈ TF.Y.X.basicOpen g := by
    rw [Scheme.mem_basicOpen _ _ _ hp₁]
    exact IsLocalization.map_units L (⟨g, hg⟩ : (hU₁.primeIdealOf ⟨p, hp₁⟩).asIdeal.primeCompl)
  let ψ : Γ(TF.Y.X, U₁) →+* Γ(TF.Y.X, TF.Y.X.basicOpen g) :=
    (TF.Y.X.presheaf.map (homOfLE (TF.Y.X.basicOpen_le g)).op).hom
  have hψg : IsUnit (ψ g) := TF.Y.X.toRingedSpace.isUnit_res_basicOpen g
  obtain ⟨hs0, hdet0, hQ0⟩ := hψB _ ψ hψg
  have hmap : spMap ψ ≫ hU₁.fromSpec = hU.fromSpec := hU₁.map_fromSpec hU _
  obtain ⟨xcU, hxU, hcU⟩ := vec_bc_of_chart C hx ψ (x' := LogKS.chart ⟨_, hU'⟩)
    (by rw [hx₁, Category.comp_id]; exact hmap.symm)
  have hψφ : ψ.comp φ₁ = cst TF.Y.s (TF.Y.X.basicOpen g) := spMap_inj (by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp, hφ₁, ← Category.assoc, hmap, spMap_cst _ hU])
  let u := hs0.unit
  let cU : Fin n → Fin n → Γ(TF.Y.X, TF.Y.X.basicOpen g) := fun j => (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g)) • (ψ ∘ B₀ j)
  have hdetU : IsUnit (Matrix.of fun i j => cU j i).det := by
    have : (Matrix.of fun i j => cU j i) = (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g)) • Matrix.of fun i j => ψ (B₀ j i) := by
      ext i j; rfl
    rw [this, Matrix.det_smul]
    exact (u⁻¹.isUnit.pow _).mul hdet0
  have hcUd : ∀ j, cU j = (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g)) • (ψ ∘ B₀ j) := fun j => rfl
  clear_value cU
  refine ⟨⟨_, hU'⟩, n, e, fun j => vec TF.Y.t _ xcU (cU j), hpU, fun j => vec_tan hxU _, fun w' hw' => ?_,
    fun a τ i => ?_⟩
  · obtain ⟨cc, rfl⟩ := vec_exists hxU w' hw'
    simp only [comb_iff hxU]
    exact basis_of_det cU hdetU cc
  · have hq := hQ0 (e ⟨τ, i⟩)
    simp only [Equiv.symm_apply_apply] at hq
    have hfix : (Pr τ).map ψ *ᵥ cU (e ⟨τ, i⟩) = cU (e ⟨τ, i⟩) := by
      rw [hcUd, Matrix.mulVec_smul, hq]
    have hmem := (hPr ψ hxU hcU τ (cU (e ⟨τ, i⟩))).1
    rw [hfix, hψφ] at hmem
    have heig : vec TF.Y.t (LogKS.chart ⟨_, hU'⟩) xcU (cU (e ⟨τ, i⟩)) ≫ (TF.Y.t.act.act a).left =
        spMap (epsMul (cst TF.Y.s (TF.Y.X.basicOpen g) (embK c τ a))) ≫
          vec TF.Y.t (LogKS.chart ⟨_, hU'⟩) xcU (cU (e ⟨τ, i⟩)) :=
      (vec_eig_iff hxU (fun a => cst TF.Y.s (TF.Y.X.basicOpen g) (embK c τ a)) (cU (e ⟨τ, i⟩))).2 hmem a
    have hc : IsCombAtG TF.Y.t (LogKS.chart ⟨_, hU'⟩) (fun j => vec TF.Y.t _ xcU (cU j))
        (Pi.single (e ⟨τ, i⟩) (cst TF.Y.s (TF.Y.X.basicOpen g) (embK c τ a)))
        (vec TF.Y.t _ xcU (cst TF.Y.s (TF.Y.X.basicOpen g) (embK c τ a) • cU (e ⟨τ, i⟩))) := by
      rw [comb_iff hxU, Finset.sum_eq_single (e ⟨τ, i⟩) (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
        (fun hk => absurd (Finset.mem_univ _) hk), Pi.single_eq_same]
    rw [vec_smul hxU, ← heig] at hc
    exact hc

end GlobalTheory.LogPole.EigNear

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c TF Z _ y`. Conclude with `GlobalTheory.LogPole.EigNear.exists_eigBasis_at TF (toBase TF Z y)`.
-/
theorem GlobalTheory.LogPole.exists_eigBasis_near : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ y : Y₀ TF.X Z, ∃ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), toBase TF Z y ∈ U.1 ∧ IsEigBasis TF U e v := by
  intro E _ _ _ H Dw l Xo c TF Z _ y
  exact GlobalTheory.LogPole.EigNear.exists_eigBasis_at TF (toBase TF Z y)
