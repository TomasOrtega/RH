import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameOfBijectiveStalk
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.Twist (resM)

/- English proof (translation)
Introduce `X Y f Q r U s V h y hQ hy hs`. Use `hQ.isQuasicoherent` as an intermediate fact. Take `⟨U', c, -, hx, hle, hc⟩` from `hQ.exists_affine (h hy : f y ∈ U)`. Use `set v : Fin r → Γ(Q, U') := fun k => resM Q hle (s k) with hv`. Establish `hT : V ⊓ f ⁻¹ᵁ U' ≤ f ⁻¹ᵁ U'` using `inf_le_right`.

Establish `hu : IsUnit (f.appLE U' _ hT ((hc.basis le_rfl).det v))`. Establish `h1` using `hs (V ⊓ f ⁻¹ᵁ U') inf_le_left`. Rewrite `h1` using `[Ker.bijective_iff_isUnit_det ((hc.pullback f).basis (hT.trans (f.preimage_mono le_rfl)))]`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[Module.Basis.det_apply, Module.Basis.det_apply]`.

Use `(RingHom.map_det (f.appLE U' _ hT).hom _).trans ?_` and prove the remaining obligations. Use `congr 1`. Use extensionality with `i j`. Use `Eq.trans (hc.pullback_basis_repr f le_rfl hT (v j) i).symm ?_` and prove the remaining obligations. Rewrite using `[Module.Basis.toMatrix_apply]`.

Use `congr 2`. Conclude with `(QCoh.pullbackSections_res f Q hT hle _).trans (QCoh.res_pullbackSections f Q _ _ _).symm`. Establish `hb` using `Y.basicOpen_of_isUnit hu`. Rewrite `hb` using `[Scheme.basicOpen_appLE]`. Establish `hy' : y ∈ V ⊓ f ⁻¹ᵁ U'` using `⟨hy, hx⟩`.

Rewrite `hy'` using `[← hb]`. Use `⟨X.basicOpen ((hc.basis le_rfl).det v), (X.basicOpen_le _).trans hle, hy'.2, fun T hT => ?_⟩` and prove the remaining obligations. Simplify using `only [Twist.resM_resM]`. Rewrite using `[Ker.bijective_iff_isUnit_det (hc.basis ((hT.trans (X.basicOpen_le _)).trans le_rfl))]`. Establish `h2` using `hc.resG_det le_rfl (hT.trans (X.basicOpen_le _)) v`.

Simplify using `only [hv, Twist.resM_resM] at h2`. Rewrite using `[← h2, ← LB.resG_resG (X.basicOpen_le _) hT]`. Conclude with `(X.toRingedSpace.isUnit_res_basicOpen _).map _`.
-/
theorem UpperTheory.frame_extends_from_pullback :
    ∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (Q : X.Modules) (r : ℕ) (U : X.Opens) (s : Fin r → Γ(Q, U)) (V : Y.Opens)
        (h : V ≤ f ⁻¹ᵁ U) (y : Y), IsVB Q r → y ∈ V → IsFrame (fun k => pullbackSections f Q h (s k)) →
        ∃ (W : X.Opens) (hW : W ≤ U), f y ∈ W ∧ IsFrame fun k => resM Q hW (s k) := by
  intro X Y f Q r U s V h y hQ hy hs
  classical
  have := hQ.isQuasicoherent
  obtain ⟨U', c, -, hx, hle, hc⟩ := hQ.exists_affine (h hy : f y ∈ U)
  set v : Fin r → Γ(Q, U') := fun k => resM Q hle (s k) with hv
  have hT : V ⊓ f ⁻¹ᵁ U' ≤ f ⁻¹ᵁ U' := inf_le_right
  have hu : IsUnit (f.appLE U' _ hT ((hc.basis le_rfl).det v)) := by
    have h1 := hs (V ⊓ f ⁻¹ᵁ U') inf_le_left
    rw [Ker.bijective_iff_isUnit_det ((hc.pullback f).basis (hT.trans (f.preimage_mono le_rfl)))] at h1
    convert h1 using 1
    rw [Module.Basis.det_apply, Module.Basis.det_apply]
    refine (RingHom.map_det (f.appLE U' _ hT).hom _).trans ?_
    congr 1
    ext i j
    refine Eq.trans (hc.pullback_basis_repr f le_rfl hT (v j) i).symm ?_
    rw [Module.Basis.toMatrix_apply]
    congr 2
    exact (QCoh.pullbackSections_res f Q hT hle _).trans (QCoh.res_pullbackSections f Q _ _ _).symm
  have hb := Y.basicOpen_of_isUnit hu
  rw [Scheme.basicOpen_appLE] at hb
  have hy' : y ∈ V ⊓ f ⁻¹ᵁ U' := ⟨hy, hx⟩
  rw [← hb] at hy'
  refine ⟨X.basicOpen ((hc.basis le_rfl).det v), (X.basicOpen_le _).trans hle, hy'.2, fun T hT => ?_⟩
  simp only [Twist.resM_resM]
  rw [Ker.bijective_iff_isUnit_det (hc.basis ((hT.trans (X.basicOpen_le _)).trans le_rfl))]
  have h2 := hc.resG_det le_rfl (hT.trans (X.basicOpen_le _)) v
  simp only [hv, Twist.resM_resM] at h2
  rw [← h2, ← LB.resG_resG (X.basicOpen_le _) hT]
  exact (X.toRingedSpace.isUnit_res_basicOpen _).map _
