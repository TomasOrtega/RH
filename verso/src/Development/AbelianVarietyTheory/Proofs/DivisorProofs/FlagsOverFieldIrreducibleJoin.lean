import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellColumnsFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackFrameEndomorphismMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameMatrixUnitsIrreducibleStatement

open CategoryTheory AlgebraicGeometry GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPath

/- English proof (translation)
Introduce `L _ ι _ M r hM φ`. Establish `hframe : ∀ a, ∃ e : Fin (r a) → Γ(M a, ⊤), VB.IsFrame e` using `fun a => by`. Take `⟨x⟩ : Nonempty (Spec (CommRingCat.of L))` from `inferInstance`. Take `⟨U, e, hx, he⟩` from `hM a x`. Take `rfl : U = ⊤` from `eq_top_iff.2 fun y _ => Subsingleton.elim x y ▸ hx`.

Conclude with `⟨e, he⟩`. Use `choose e he using hframe`. Set `K` to `Scheme.ΓSpecIso (CommRingCat.of L)`. Set `b : ∀ a, Module.Basis (Fin (r a)) Γ(Spec (CommRingCat.of L), ⊤) Γ(M a, ⊤)` to `fun a => (he a).basis le_top`. Establish `hb : ∀ a i, b a i = e a i` using `fun a i => by`.

Rewrite using `[VB.IsFrame.basis_apply, Twist.resM_self]`. Set `A' : ∀ a, Matrix (Fin (r a)) (Fin (r a)) Γ(Spec (CommRingCat.of L), ⊤)` to `fun a => LinearMap.toMatrix (b a) (b a) (QCoh.appLinear (φ a).hom ⊤)`. Set `A : ∀ a, Matrix (Fin (r a)) (Fin (r a)) L` to `fun a => K.hom.hom.mapMatrix (A' a)`. Establish `hA : ∀ a, IsUnit (A a).det` using `fun a => by`. Establish `hu : IsUnit (LinearMap.det (QCoh.appLinear (φ a).hom ⊤))` using `LinearEquiv.isUnit_det' (LinearEquiv.ofBijective (QCoh.appLinear (φ a).hom ⊤) (ConcreteCategory.bijective_of_isIso ((φ a).hom.app ⊤)))`.

Establish `: (A a).det = K.hom.hom (A' a).det` using `(RingHom.map_det _ _).symm`. Rewrite using `[this, LinearMap.det_toMatrix]`. Conclude with `hu.map _`. Establish `hAe : ∀ a i, (φ a).hom.app ⊤ (e a i) = ∑ j, K.inv (A a j i) • e a j` using `fun a i => by`. Establish `hK : ∀ j, K.inv (A a j i) = A' a j i` using `fun j => by`.

Express the relevant statement in the definitionally equal form `K.inv (K.hom (A' a j i)) = _`. Rewrite using `[← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]`. Simplify using `only [hK, A', LinearMap.toMatrix_apply, ← hb]`. Conclude with `((b a).sum_repr _).symm`. Take `⟨T, c, t₁, t₂, h₁, h₂, B, hT, hB, hB₁, hB₂⟩` from `GlobalTheory.T.frame_matrix_units_irreducible L ι r A hA`.

Establish `hq : ∀ a, (M a).IsQuasicoherent` using `fun a => (hM a).isQuasicoherent`. Establish `hc : ∀ a, VB.IsFrame (fun i => QCoh.pullbackSections c (M a) (le_refl (⊤ : T.Opens)) (e a i))` using `fun a => (he a).pullback c`. Establish `hm : ∀ a, VB.IsFrame (fun j => ∑ i, B a i j • QCoh.pullbackSections c (M a) (le_refl (⊤ : T.Opens)) (e a i))` using `fun a => FlagZ.Univ.isFrame_sum_smul_of_isUnit (hc a) (B a) (hB a)`. Use `⟨T, c, t₁, t₂, h₁, h₂, fun a => (hc a).iso (hm a), hT, fun a => ?_, fun a => ?_⟩` and prove the remaining obligations. Establish `H` using `GlobalTheory.T.pullback_frame_endomorphism_matrix _ _ c t₁ h₁ (M a) _ (e a) (he a) ((hc a).iso (hm a)).hom (B a) (fun i => (hc a).iso_hom_app (hm a) i) (𝟙 _) (fun i => by`.

Simplify using `only [hB₁, Matrix.one_apply]`. Simplify using `[apply_ite])`. Use `(cancel_mono ((Scheme.Modules.pullbackComp t₁ c).hom.app (M a) ≫ (Scheme.Modules.pullbackCongr h₁).hom.app (M a) ≫ (Scheme.Modules.pullbackId _).hom.app (M a))).1 ?_` and prove the remaining obligations. Conclude with `H.trans ((Category.comp_id _).trans (Category.id_comp _).symm)`. Conclude with `GlobalTheory.T.pullback_frame_endomorphism_matrix _ _ c t₂ h₂ (M a) _ (e a) (he a) ((hc a).iso (hm a)).hom (B a) (fun i => (hc a).iso_hom_app (hm a) i) (φ a).hom (fun i => by`.

Simplify using `only [hB₂]`. Conclude with `hAe a i)`.
-/
theorem exists_path_auto : ∀ (L : Type) [Field L] (ι : Type) [Fintype ι] (M : ι → (Spec (CommRingCat.of L)).Modules) (r : ι → ℕ), (∀ a, VB.IsVB (M a) (r a)) → ∀ φ : ∀ a, M a ≅ M a, ∃ (T : Scheme.{0}) (c : T ⟶ Spec (CommRingCat.of L)) (t₁ t₂ : Spec (CommRingCat.of L) ⟶ T) (h₁ : t₁ ≫ c = 𝟙 _) (h₂ : t₂ ≫ c = 𝟙 _) (Φ : ∀ a, (Scheme.Modules.pullback c).obj (M a) ≅ (Scheme.Modules.pullback c).obj (M a)), IrreducibleSpace T ∧ (∀ a, (Scheme.Modules.pullback t₁).map (Φ a).hom = 𝟙 _) ∧ ∀ a, (Scheme.Modules.pullback t₂).map (Φ a).hom ≫ (Scheme.Modules.pullbackComp t₂ c).hom.app (M a) ≫ (Scheme.Modules.pullbackCongr h₂).hom.app (M a) ≫ (Scheme.Modules.pullbackId _).hom.app (M a) = ((Scheme.Modules.pullbackComp t₂ c).hom.app (M a) ≫ (Scheme.Modules.pullbackCongr h₂).hom.app (M a) ≫ (Scheme.Modules.pullbackId _).hom.app (M a)) ≫ (φ a).hom := by
  intro L _ ι _ M r hM φ
  have hframe : ∀ a, ∃ e : Fin (r a) → Γ(M a, ⊤), VB.IsFrame e := fun a => by
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
    obtain ⟨U, e, hx, he⟩ := hM a x
    obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => Subsingleton.elim x y ▸ hx
    exact ⟨e, he⟩
  choose e he using hframe
  let K := Scheme.ΓSpecIso (CommRingCat.of L)
  let b : ∀ a, Module.Basis (Fin (r a)) Γ(Spec (CommRingCat.of L), ⊤) Γ(M a, ⊤) :=
    fun a => (he a).basis le_top
  have hb : ∀ a i, b a i = e a i := fun a i => by
    rw [VB.IsFrame.basis_apply, Twist.resM_self]
  let A' : ∀ a, Matrix (Fin (r a)) (Fin (r a)) Γ(Spec (CommRingCat.of L), ⊤) := fun a =>
    LinearMap.toMatrix (b a) (b a) (QCoh.appLinear (φ a).hom ⊤)
  let A : ∀ a, Matrix (Fin (r a)) (Fin (r a)) L := fun a => K.hom.hom.mapMatrix (A' a)
  have hA : ∀ a, IsUnit (A a).det := fun a => by
    have hu : IsUnit (LinearMap.det (QCoh.appLinear (φ a).hom ⊤)) :=
      LinearEquiv.isUnit_det' (LinearEquiv.ofBijective (QCoh.appLinear (φ a).hom ⊤)
        (ConcreteCategory.bijective_of_isIso ((φ a).hom.app ⊤)))
    have : (A a).det = K.hom.hom (A' a).det := (RingHom.map_det _ _).symm
    rw [this, LinearMap.det_toMatrix]
    exact hu.map _
  have hAe : ∀ a i, (φ a).hom.app ⊤ (e a i) = ∑ j, K.inv (A a j i) • e a j := fun a i => by
    have hK : ∀ j, K.inv (A a j i) = A' a j i := fun j => by
      change K.inv (K.hom (A' a j i)) = _
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
    simp only [hK, A', LinearMap.toMatrix_apply, ← hb]
    exact ((b a).sum_repr _).symm
  obtain ⟨T, c, t₁, t₂, h₁, h₂, B, hT, hB, hB₁, hB₂⟩ := GlobalTheory.T.frame_matrix_units_irreducible L ι r A hA
  have hq : ∀ a, (M a).IsQuasicoherent := fun a => (hM a).isQuasicoherent
  have hc : ∀ a, VB.IsFrame
      (fun i => QCoh.pullbackSections c (M a) (le_refl (⊤ : T.Opens)) (e a i)) :=
    fun a => (he a).pullback c
  have hm : ∀ a, VB.IsFrame (fun j => ∑ i, B a i j •
      QCoh.pullbackSections c (M a) (le_refl (⊤ : T.Opens)) (e a i)) :=
    fun a => FlagZ.Univ.isFrame_sum_smul_of_isUnit (hc a) (B a) (hB a)
  refine ⟨T, c, t₁, t₂, h₁, h₂, fun a => (hc a).iso (hm a), hT, fun a => ?_, fun a => ?_⟩
  · have H := GlobalTheory.T.pullback_frame_endomorphism_matrix _ _ c t₁ h₁ (M a) _ (e a) (he a) ((hc a).iso (hm a)).hom
      (B a) (fun i => (hc a).iso_hom_app (hm a) i) (𝟙 _) (fun i => by
        simp only [hB₁, Matrix.one_apply]
        simp [apply_ite])
    refine (cancel_mono ((Scheme.Modules.pullbackComp t₁ c).hom.app (M a) ≫
      (Scheme.Modules.pullbackCongr h₁).hom.app (M a) ≫
      (Scheme.Modules.pullbackId _).hom.app (M a))).1 ?_
    exact H.trans ((Category.comp_id _).trans (Category.id_comp _).symm)
  · exact GlobalTheory.T.pullback_frame_endomorphism_matrix _ _ c t₂ h₂ (M a) _ (e a) (he a) ((hc a).iso (hm a)).hom
      (B a) (fun i => (hc a).iso_hom_app (hm a) i) (φ a).hom (fun i => by
        simp only [hB₂]
        exact hAe a i)

end GlobalTheory.FlagPath

end
