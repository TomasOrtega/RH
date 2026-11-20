import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutsSecOfIsLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSectionsFormFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameAtFieldPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualFrameTransitionCoefficients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualFrameCoefficients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSheafLocalModelBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameAtIntegralPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ChainPts
open GlobalTheory.LineNorm (IsTanBasis)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.OmegaHT.Link

open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.Conormal GlobalTheory.DualPull GlobalTheory.TanSec
open GlobalTheory.Twist (resM resM_resM resM_self app_resM resM_smul)

/- English proof (translation)
Use `conv_lhs => rw [← (he.basis hU).sum_repr σ]`. Rewrite using `[map_sum, dualApp_sum, LinearMap.sum_apply, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Scheme.Modules.Hom.app_smul, dualApp_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, map_mul, appLE_resG, IsFrame.basis_apply, valF, dif_pos (hw.trans (w.preimage_mono hT)), app_resM, dualApp_res]`.
-/
theorem val_eq_sum {X : Scheme.{0}} {F P : X.Modules} (θ : F ⟶ dual P) {g : ℕ} {V U : X.Opens}
    {e : Fin g → Γ(F, V)} (he : VB.IsFrame e) (hU : U ≤ V) (σ : Γ(F, U)) {k : Type} [Field k]
    (w : Sp k ⟶ X) {T : X.Opens} (hT : T ≤ U) (hw : ⊤ ≤ w ⁻¹ᵁ T) (μ : Γ(P, T)) :
    (Scheme.ΓSpecIso (.of k)).hom (w.appLE T ⊤ hw (dualApp (θ.app _ σ) hT μ)) =
      ∑ l, valF w _ ((he.basis hU).repr σ l) *
        (Scheme.ΓSpecIso (.of k)).hom (w.appLE T ⊤ hw (dualApp (θ.app _ (e l)) (hT.trans hU) μ)) := by
  conv_lhs => rw [← (he.basis hU).sum_repr σ]
  rw [map_sum, dualApp_sum, LinearMap.sum_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.Hom.app_smul, dualApp_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, map_mul, appLE_resG,
    IsFrame.basis_apply, valF, dif_pos (hw.trans (w.preimage_mono hT)), app_resM, dualApp_res]

section Tan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {X : Scheme.{0}} (t : SAB H X)

open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet GlobalTheory.LocM.TanPair MonoidalCategory CartesianMonoidalCategory MonObj in

/- English proof (translation)
Establish `h₁ : spMap (RingHom.id R) = 𝟙 _` using `Spec.map_id _`. Establish `h₂ : spMap (Formalism.L2.Pj.dualMap (RingHom.id R)) = 𝟙 _`. Establish `: Formalism.L2.Pj.dualMap (RingHom.id R) = RingHom.id _`. Use `RingHom.ext fun z => ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [Formalism.L2.Pj.dualMap]`.

Rewrite using `[this]`. Conclude with `Spec.map_id _`. Establish `h` using `he.2 R (RingHom.id R) (PullbackSections.tv m).left`. Simplify using `only [h₁, h₂, Category.id_comp] at h`. Conclude with `(existsUnique_congr fun a => LieMet.isComb_iff (fun l => LieMet.tanOf (he.1 l)) a m).1 (h (LieMet.isTan_tv m))`.
-/
theorem exists_unique_coords {R : Type} [CommRing R] {x : Sp R ⟶ X} {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : IsTanBasis t x e) (m : PullbackSections.TanM x t.G) :
    ∃! a : Fin g → R, m = ∑ l, a l • LieMet.tanOf (he.1 l) := by
  have h₁ : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _
  have h₂ : spMap (Formalism.L2.Pj.dualMap (RingHom.id R)) = 𝟙 _ := by
    have : Formalism.L2.Pj.dualMap (RingHom.id R) = RingHom.id _ := by
      refine RingHom.ext fun z => ?_
      ext <;> simp [Formalism.L2.Pj.dualMap]
    rw [this]
    exact Spec.map_id _
  have h := he.2 R (RingHom.id R) (PullbackSections.tv m).left
  simp only [h₁, h₂, Category.id_comp] at h
  exact (existsUnique_congr fun a => LieMet.isComb_iff (fun l => LieMet.tanOf (he.1 l)) a m).1 (h (LieMet.isTan_tv m))

/- English proof (translation)
Use `t.semi` as an intermediate fact. Use `t.semi.smooth` as an intermediate fact. Set `j : Sp Γ(S, V) ⟶ S` to `hV.fromSpec`. Establish `: IsOpenImmersion j` using `hV.isOpenImmersion_fromSpec`. Establish `hj : j ''ᵁ ⊤ = V`.

Rewrite using `[Scheme.Hom.image_top_eq_opensRange]`. Conclude with `hV.opensRange_fromSpec`. Establish `hθ` using `Frame.isIso_theta h (Frame.frames_pullback π (exists_isFrame_omega t.G))`. Establish `hθ'` using `Frame.isIso_theta j (Frame.frames_pullback (h ≫ π) (exists_isFrame_omega t.G))`. Establish `h₁` using `Frame.isFrame_form _ (exists_unique_coords t he)`.

Establish `h₂` using `h₁.map_iso (dualIso ((Scheme.Modules.pullbackComp j (h ≫ π)).app (omega t.G))).hom`. Establish `h₃ : VB.IsFrame fun l => secOf j ((Scheme.Modules.pullback (h ≫ π)).obj (omega t.G)) ((Scheme.Modules.pullbackComp j (h ≫ π)).hom.app _ ≫ tanMor t.G (j ≫ h ≫ π) (e l))`. Use `Frame.isFrame_secOf j _ hθ' _ ?_` and prove the remaining obligations. Use `(congrArg VB.IsFrame (funext fun i => ?_)).mpr h₂` and prove the remaining obligations. Rewrite using `[Frame.tanMor_eq (he.1 i)]`.

Both sides reduce to the same expression. Establish `h₄` using `((h₃.res hj.ge).map_iso (dualIso ((Scheme.Modules.pullbackComp h π).app (omega t.G))).hom).map_iso (inv (theta h ((Scheme.Modules.pullback π).obj (omega t.G))))`. Use `⟨_, h₄, fun k _ κ l hv U hU s T hT T' hT' hTT hw => ?_⟩` and prove the remaining obligations. Establish `h₅ : T' ≤ (h ≫ π) ⁻¹ᵁ U` using `hTT.trans (h.preimage_mono hT)`. Rewrite using `[← Glue.appLE_dualApp_secOf_tanMor t κ j (h ≫ π) hθ' (he.1 l) rfl (Category.assoc _ _ _) hv hU s (hT'.trans hj.ge) h₅ hw]`.

Establish `e₀` using `IsIso.inv_hom_id (theta h ((Scheme.Modules.pullback π).obj (omega t.G)))`. Establish `e₁ (σ) : (theta h ((Scheme.Modules.pullback π).obj (omega t.G))).app V ((inv (theta h ((Scheme.Modules.pullback π).obj (omega t.G)))).app V σ) = σ` using `congr(($e₀).app V σ)`. Establish `e₂` using `Vert.DivPull.pullbackComp_inv_app h π (omega t.G) hT hTT h₅ s`. Establish `e₃` using `((Scheme.Modules.pullbackComp h π).app (omega t.G)).inv_hom_id`. Establish `e₄ : ((Scheme.Modules.pullbackComp h π).hom.app (omega t.G)).app _ (((Scheme.Modules.pullbackComp h π).inv.app (omega t.G)).app _ (pullbackSections (h ≫ π) _ h₅ s)) = pullbackSections (h ≫ π) _ h₅ s` using `congr(($e₃).app _ (pullbackSections (h ≫ π) _ h₅ s))`.

Rewrite `e₄` using `[e₂]`. Rewrite using `[e₁, ← e₄]`. Both sides reduce to the same expression.
-/
theorem exists_frame {Z S : Scheme.{0}} (π : Z ⟶ X) (h : S ⟶ Z) {V : S.Opens} (hV : IsAffineOpen V) {g : ℕ}
    {e : Fin g → (Sp (DualNumber Γ(S, V)) ⟶ t.G.left)} (he : IsTanBasis t (R := Γ(S, V)) (hV.fromSpec ≫ h ≫ π) e) :
    ∃ ε : Fin g → Γ((Scheme.Modules.pullback h).obj (dual ((Scheme.Modules.pullback π).obj (omega t.G))), V),
      VB.IsFrame ε ∧ ∀ (k : Type) [Field k] (κ : Γ(S, V) →+* k) (l : Fin g)
        (hv : IsTanAtG t (spMap κ ≫ hV.fromSpec ≫ h ≫ π) (spMap (Formalism.L2.Pj.dualMap κ) ≫ e l)) {U : X.Opens}
        (hU : ⊤ ≤ (spMap κ ≫ hV.fromSpec ≫ h ≫ π) ⁻¹ᵁ U) (s : Γ(omega t.G, U)) {T : Z.Opens} (hT : T ≤ π ⁻¹ᵁ U)
        {T' : S.Opens} (hT' : T' ≤ V) (hTT : T' ≤ h ⁻¹ᵁ T) (hw : ⊤ ≤ (spMap κ ≫ hV.fromSpec) ⁻¹ᵁ T'),
        (Scheme.ΓSpecIso (.of k)).hom ((spMap κ ≫ hV.fromSpec).appLE T' ⊤ hw
          (dualApp ((theta h _).app V (ε l)) hT' (pullbackSections h _ hTT (pullbackSections π _ hT s)))) =
          tanEv t hv hU s := by
  have := t.semi
  have := t.semi.smooth
  let j : Sp Γ(S, V) ⟶ S := hV.fromSpec
  have : IsOpenImmersion j := hV.isOpenImmersion_fromSpec
  have hj : j ''ᵁ ⊤ = V := by
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact hV.opensRange_fromSpec
  have hθ := Frame.isIso_theta h (Frame.frames_pullback π (exists_isFrame_omega t.G))
  have hθ' := Frame.isIso_theta j (Frame.frames_pullback (h ≫ π) (exists_isFrame_omega t.G))
  have h₁ := Frame.isFrame_form _ (exists_unique_coords t he)
  have h₂ := h₁.map_iso (dualIso ((Scheme.Modules.pullbackComp j (h ≫ π)).app (omega t.G))).hom
  have h₃ : VB.IsFrame fun l => secOf j ((Scheme.Modules.pullback (h ≫ π)).obj (omega t.G))
      ((Scheme.Modules.pullbackComp j (h ≫ π)).hom.app _ ≫ tanMor t.G (j ≫ h ≫ π) (e l)) := by
    refine Frame.isFrame_secOf j _ hθ' _ ?_
    refine (congrArg VB.IsFrame (funext fun i => ?_)).mpr h₂
    rw [Frame.tanMor_eq (he.1 i)]
    rfl
  have h₄ := ((h₃.res hj.ge).map_iso (dualIso ((Scheme.Modules.pullbackComp h π).app (omega t.G))).hom).map_iso
    (inv (theta h ((Scheme.Modules.pullback π).obj (omega t.G))))
  refine ⟨_, h₄, fun k _ κ l hv U hU s T hT T' hT' hTT hw => ?_⟩
  have h₅ : T' ≤ (h ≫ π) ⁻¹ᵁ U := hTT.trans (h.preimage_mono hT)
  rw [← Glue.appLE_dualApp_secOf_tanMor t κ j (h ≫ π) hθ' (he.1 l) rfl (Category.assoc _ _ _) hv hU s
    (hT'.trans hj.ge) h₅ hw]
  have e₀ := IsIso.inv_hom_id (theta h ((Scheme.Modules.pullback π).obj (omega t.G)))
  have e₁ (σ) : (theta h ((Scheme.Modules.pullback π).obj (omega t.G))).app V
      ((inv (theta h ((Scheme.Modules.pullback π).obj (omega t.G)))).app V σ) = σ := congr(($e₀).app V σ)
  have e₂ := Vert.DivPull.pullbackComp_inv_app h π (omega t.G) hT hTT h₅ s
  have e₃ := ((Scheme.Modules.pullbackComp h π).app (omega t.G)).inv_hom_id
  have e₄ : ((Scheme.Modules.pullbackComp h π).hom.app (omega t.G)).app _
      (((Scheme.Modules.pullbackComp h π).inv.app (omega t.G)).app _ (pullbackSections (h ≫ π) _ h₅ s)) =
      pullbackSections (h ≫ π) _ h₅ s := congr(($e₃).app _ (pullbackSections (h ≫ π) _ h₅ s))
  rw [e₂] at e₄
  rw [e₁, ← e₄]
  rfl

end Tan

/- English proof (translation)
Introduce `V g e he`. Use `(Y Z.i).t.semi` as an intermediate fact. Use `(Y Z.i).t.semi.smooth` as an intermediate fact. Take `⟨ε, hε, hval⟩` from `exists_frame (Y Z.i).t Z.π h V.2 he`. Use `⟨hε.coord, hε.dual, fun k _ κ a φ hφ cf v hv => ?_⟩` and prove the remaining obligations.

Set `w : Sp k ⟶ X` to `spMap κ ≫ V.2.fromSpec`. Establish `hφ' : spMap φ ≫ Z.chart a = w ≫ h` using `hφ.trans (Category.assoc _ _ _).symm`. Establish `hy : (w ≫ h) ≫ Z.π = spMap κ ≫ V.2.fromSpec ≫ h ≫ Z.π` using `by simp only [w, Category.assoc]`. Establish `hpt {S : Scheme.{0}} (g : Sp k ⟶ S) {U : S.Opens} (hU : g default ∈ U) : ⊤ ≤ g ⁻¹ᵁ U` using `fun q _ => by`. Rewrite using `[Subsingleton.elim q default]`.

Conclude with `hU`. Establish `hch : (w ≫ h) default ∈ (Z.U a).1`. Rewrite using `[← hφ']`. Conclude with `(chart_image_top Z a).le ⟨spMap φ default, trivial, rfl⟩`. Establish `hwV : w default ∈ V.1`.

Rewrite using `[← SetLike.mem_coe, ← V.2.range_fromSpec]`. Conclude with `⟨spMap κ default, rfl⟩`. Establish `htan (i : Fin r) : IsTanAtG (Y Z.i).t (spMap κ ≫ V.2.fromSpec ≫ h ≫ Z.π) ((Z.fr a).bc φ (x i).1 (x i).2)` using `LieMet.isTan_map φ (by rw [← Category.assoc, hφ', hy]) ((Z.frame a).1 _ _).1`. Establish `hte (l : Fin g) : IsTanAtG (Y Z.i).t (spMap κ ≫ V.2.fromSpec ≫ h ≫ Z.π) (spMap (Formalism.L2.Pj.dualMap κ) ≫ e l)` using `LieMet.isTan_map κ rfl (he.1 l)`. Take `⟨U, n, m, hx, hm⟩` from `exists_isFrame_omega (Y Z.i).t.G ((spMap κ ≫ V.2.fromSpec ≫ h ≫ Z.π) default)`.

Establish `hU` using `hpt _ hx`. Establish `key (i : Fin r) : IsCombAtG (Y Z.i).t (spMap κ ≫ V.2.fromSpec ≫ h ≫ Z.π) (fun l => spMap (Formalism.L2.Pj.dualMap κ) ≫ e l) (fun l => valF w _ (crd (hfr a).dual (hε.coord l) i)) ((Z.fr a).bc φ (x i).1 (x i).2)`. Use `Glue.isCombAtG_of_tanEv _ hU hm hte (htan i) _ fun b => ?_` and prove the remaining obligations. Set `T : Z.X.Opens` to `(Z.U a).1 ⊓ Z.π ⁻¹ᵁ U`. Establish `hgT : ⊤ ≤ (w ≫ h) ⁻¹ᵁ T` using `hpt _ ⟨hch, hx⟩`.

Set `T' : X.Opens` to `V.1 ⊓ h ⁻¹ᵁ T`. Establish `hwT : ⊤ ≤ w ⁻¹ᵁ T'` using `hpt _ ⟨hwV, hch, hx⟩`. Establish `hT' : T' ≤ V.1 ⊓ h ⁻¹ᵁ (Z.U a).1` using `inf_le_inf_left _ (h.preimage_mono inf_le_left)`. Set `μ : Γ(om Z, T)` to `pullbackSections Z.π _ inf_le_right (m b)`. Establish `e₁ : resM ((Scheme.Modules.pullback h).obj (VB.dual (om Z))) (inf_le_right : V.1 ⊓ _ ≤ _) (secX Z h x a i) = pullbackSections h _ inf_le_right (TanSec.sec Z a (Z.fr a (x i).1 (x i).2))` using `res_pullbackSections h _ _ _ _`.

Establish `e₂` using `val_eq_sum (theta h (om Z)) hε inf_le_left (resM _ inf_le_right (secX Z h x a i)) w hT' hwT (pullbackSections h (om Z) inf_le_right μ)`. Use `Eq.trans ?_ (e₂.trans (Finset.sum_congr rfl fun l _ => ?_))` and prove the remaining obligations. Rewrite using `[e₁]`. Use `(Glue.appLE_dualApp_sec Z a ((Z.frame a).1 _ _).1 φ hφ' hy (htan i) hU (m b) inf_le_left inf_le_right hgT).symm.trans (congrArg (Scheme.ΓSpecIso (.of k)).hom (Eq.symm ?_))` and prove the remaining obligations. Conclude with `(congrArg (w.appLE _ ⊤ hwT) (dualApp_theta h _ inf_le_left inf_le_right hT' inf_le_right μ)).trans (appLE_appLE rfl _ _ _ _)`.

Use `congrArg₂ (· * ·) (congrArg (valF w _) ?_) (hval k κ l (hte l) hU (m b) _ _ _ hwT)` and prove the remaining obligations. Use `Eq.symm (((hfr a).dual_basis_repr inf_le_right _ i).trans ?_)` and prove the remaining obligations. Conclude with `(congr($(dualApp_res (hε.coord l) inf_le_left le_rfl) _)).trans (hε.dualApp_coord l _ _)`. Use `LineNorm.Chart.comb_comb hte key hv` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `l`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, w]`.
-/
theorem hasDualFrames {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
    {i₀ : Idx H p} (Z : LocM.Mdl Y i₀) {X : Scheme.{0}} (h : X ⟶ Z.X) {r : ℕ} (x : Fin r → Letter Dw)
    (hfr : ∀ a, VB.IsFrame (secX Z h x a)) : HasDualFrames Z h x fun a => (hfr a).dual := by
  intro V g e he
  have := (Y Z.i).t.semi
  have := (Y Z.i).t.semi.smooth
  obtain ⟨ε, hε, hval⟩ := exists_frame (Y Z.i).t Z.π h V.2 he
  refine ⟨hε.coord, hε.dual, fun k _ κ a φ hφ cf v hv => ?_⟩
  let w : Sp k ⟶ X := spMap κ ≫ V.2.fromSpec
  have hφ' : spMap φ ≫ Z.chart a = w ≫ h := hφ.trans (Category.assoc _ _ _).symm
  have hy : (w ≫ h) ≫ Z.π = spMap κ ≫ V.2.fromSpec ≫ h ≫ Z.π := by simp only [w, Category.assoc]
  have hpt {S : Scheme.{0}} (g : Sp k ⟶ S) {U : S.Opens} (hU : g default ∈ U) : ⊤ ≤ g ⁻¹ᵁ U := fun q _ => by
    rw [Subsingleton.elim q default]; exact hU
  have hch : (w ≫ h) default ∈ (Z.U a).1 := by
    rw [← hφ']
    exact (chart_image_top Z a).le ⟨spMap φ default, trivial, rfl⟩
  have hwV : w default ∈ V.1 := by
    rw [← SetLike.mem_coe, ← V.2.range_fromSpec]
    exact ⟨spMap κ default, rfl⟩
  have htan (i : Fin r) :
      IsTanAtG (Y Z.i).t (spMap κ ≫ V.2.fromSpec ≫ h ≫ Z.π) ((Z.fr a).bc φ (x i).1 (x i).2) :=
    LieMet.isTan_map φ (by rw [← Category.assoc, hφ', hy]) ((Z.frame a).1 _ _).1
  have hte (l : Fin g) : IsTanAtG (Y Z.i).t (spMap κ ≫ V.2.fromSpec ≫ h ≫ Z.π)
      (spMap (Formalism.L2.Pj.dualMap κ) ≫ e l) := LieMet.isTan_map κ rfl (he.1 l)
  obtain ⟨U, n, m, hx, hm⟩ := exists_isFrame_omega (Y Z.i).t.G ((spMap κ ≫ V.2.fromSpec ≫ h ≫ Z.π) default)
  have hU := hpt _ hx
  have key (i : Fin r) : IsCombAtG (Y Z.i).t (spMap κ ≫ V.2.fromSpec ≫ h ≫ Z.π)
      (fun l => spMap (Formalism.L2.Pj.dualMap κ) ≫ e l)
      (fun l => valF w _ (crd (hfr a).dual (hε.coord l) i)) ((Z.fr a).bc φ (x i).1 (x i).2) := by
    refine Glue.isCombAtG_of_tanEv _ hU hm hte (htan i) _ fun b => ?_
    let T : Z.X.Opens := (Z.U a).1 ⊓ Z.π ⁻¹ᵁ U
    have hgT : ⊤ ≤ (w ≫ h) ⁻¹ᵁ T := hpt _ ⟨hch, hx⟩
    let T' : X.Opens := V.1 ⊓ h ⁻¹ᵁ T
    have hwT : ⊤ ≤ w ⁻¹ᵁ T' := hpt _ ⟨hwV, hch, hx⟩
    have hT' : T' ≤ V.1 ⊓ h ⁻¹ᵁ (Z.U a).1 := inf_le_inf_left _ (h.preimage_mono inf_le_left)
    let μ : Γ(om Z, T) := pullbackSections Z.π _ inf_le_right (m b)
    have e₁ : resM ((Scheme.Modules.pullback h).obj (VB.dual (om Z))) (inf_le_right : V.1 ⊓ _ ≤ _) (secX Z h x a i) =
        pullbackSections h _ inf_le_right (TanSec.sec Z a (Z.fr a (x i).1 (x i).2)) := res_pullbackSections h _ _ _ _
    have e₂ := val_eq_sum (theta h (om Z)) hε inf_le_left (resM _ inf_le_right (secX Z h x a i)) w hT' hwT
      (pullbackSections h (om Z) inf_le_right μ)
    refine Eq.trans ?_ (e₂.trans (Finset.sum_congr rfl fun l _ => ?_))
    · rw [e₁]
      refine (Glue.appLE_dualApp_sec Z a ((Z.frame a).1 _ _).1 φ hφ' hy (htan i) hU (m b) inf_le_left inf_le_right
        hgT).symm.trans (congrArg (Scheme.ΓSpecIso (.of k)).hom (Eq.symm ?_))
      exact (congrArg (w.appLE _ ⊤ hwT) (dualApp_theta h _ inf_le_left inf_le_right hT' inf_le_right μ)).trans
        (appLE_appLE rfl _ _ _ _)
    · refine congrArg₂ (· * ·) (congrArg (valF w _) ?_) (hval k κ l (hte l) hU (m b) _ _ _ hwT)
      refine Eq.symm (((hfr a).dual_basis_repr inf_le_right _ i).trans ?_)
      exact (congr($(dualApp_res (hε.coord l) inf_le_left le_rfl) _)).trans (hε.dualApp_coord l _ _)
  have := LineNorm.Chart.comb_comb hte key hv
  convert this using 1
  funext l
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, w]

/- English proof (translation)
Introduce `E _ _ _ H Dw Xo p W Y i₀ Z X h r x hx`. Establish `hvb : IsVB (om Z) r` using `GlobalTheory.T.tangent_sheaf_local_model_bundle E H Dw Xo p W Y i₀ Z r x hx`. Use `haveI : (dual (om Z)).IsQuasicoherent := hvb.dual.isQuasicoherent`. Establish `hfr : ∀ a, VB.IsFrame (secX Z h x a)` using `fun a => (Frame.isFrame_sec E H Dw Xo p W Y i₀ Z r x hx a).pullback h`. Establish `hvbX : IsVB (lieX Z h) r` using `hvb.dual.pullback h`.

Use `⟨dual (lieX Z h), fun a => (hfr a).coord, ⟨fun a => (hfr a).dual, ?_, ?_⟩, hvbX.dual, hasDualFrames Z h x hfr⟩` and prove the remaining obligations. Introduce `k _ w a a' φ φ' h1 h2 j`. Simplify using `only [coef_dual]`. Conclude with `Glue.isCombAtG_coef E H Dw Xo p W Y i₀ Z X h r x hx hfr k w a a' φ φ' h1 h2 j`. Introduce `y w hw a φ hφ V e he hV cf v hv`.

Take `⟨e', he', hc⟩` from `exists_frame_coef_dual_eq X (lieX Z h) r r hvbX V e he`. Simplify using `only [hc]`. Conclude with `GlobalTheory.T.tangent_frame_at_integral_point E H Dw Xo p W Y i₀ Z X h r x hx hfr y w hw a φ hφ V e' he' hV cf v hv`.
-/
theorem linkSt : GlobalTheory.OmegaHT.LinkSt := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z X h r x hx
  have hvb : IsVB (om Z) r := GlobalTheory.T.tangent_sheaf_local_model_bundle E H Dw Xo p W Y i₀ Z r x hx
  haveI : (dual (om Z)).IsQuasicoherent := hvb.dual.isQuasicoherent
  have hfr : ∀ a, VB.IsFrame (secX Z h x a) := fun a => (Frame.isFrame_sec E H Dw Xo p W Y i₀ Z r x hx a).pullback h
  have hvbX : IsVB (lieX Z h) r := hvb.dual.pullback h
  refine ⟨dual (lieX Z h), fun a => (hfr a).coord, ⟨fun a => (hfr a).dual, ?_, ?_⟩, hvbX.dual,
    hasDualFrames Z h x hfr⟩
  · intro k _ w a a' φ φ' h1 h2 j
    simp only [coef_dual]
    exact Glue.isCombAtG_coef E H Dw Xo p W Y i₀ Z X h r x hx hfr k w a a' φ φ' h1 h2 j
  · intro y w hw a φ hφ V e he hV cf v hv
    obtain ⟨e', he', hc⟩ := exists_frame_coef_dual_eq X (lieX Z h) r r hvbX V e he
    simp only [hc]
    exact GlobalTheory.T.tangent_frame_at_integral_point E H Dw Xo p W Y i₀ Z X h r x hx hfr y w hw a φ hφ V e' he' hV cf v hv

end GlobalTheory.OmegaHT.Link
