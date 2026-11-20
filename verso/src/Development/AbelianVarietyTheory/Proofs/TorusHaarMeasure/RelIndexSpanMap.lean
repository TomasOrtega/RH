import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsBasisMem

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.HeightInv

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in

/- English proof (translation)
Set `g : V →+ V` to `f.toAddMonoidHom`. Establish `hg : Function.Injective g` using `hinj`. Establish `hΛmap : Λ.toAddSubgroup.map g = Λ.toAddSubgroup`. Use extensionality with `v`. Simplify using `only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `(hΛ x).1 hx`. Introduce `hv`. Take `⟨x, rfl⟩` from `hsurj v`.

Conclude with `⟨x, (hΛ x).2 hv, rfl⟩`. Establish `hK : Submodule.span K (Set.range fun a => f (w a)) = (Submodule.span K (Set.range w)).map f`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Establish `hR : Submodule.span R (Set.range fun a => f (w a)) = (Submodule.span R (Set.range w)).map (f.restrictScalars R)`.

Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Establish `hKg : ((Submodule.span K (Set.range w)).map f).toAddSubgroup = (Submodule.span K (Set.range w)).toAddSubgroup.map g`. Use extensionality with `v`. Simplify using `[Submodule.mem_map, AddSubgroup.mem_map, g]`.

Establish `hRg : ((Submodule.span R (Set.range w)).map (f.restrictScalars R)).toAddSubgroup = (Submodule.span R (Set.range w)).toAddSubgroup.map g`. Use extensionality with `v`. Simplify using `[Submodule.mem_map, AddSubgroup.mem_map, g]`. Establish `hinf : Λ.toAddSubgroup ⊓ (Submodule.span K (Set.range w)).toAddSubgroup.map g = (Λ.toAddSubgroup ⊓ (Submodule.span K (Set.range w)).toAddSubgroup).map g`. Rewrite using `[AddSubgroup.map_inf_eq _ _ _ hg, hΛmap]`.

Rewrite using `[hK, hR, hKg, hRg, hinf, AddSubgroup.relIndex_map_map_of_injective _ _ hg]`.
-/
theorem _root_.GlobalTheory.HeightInv.relIndex_span_map {R K V ι : Type} [CommRing R] [Field K] [Algebra R K] [AddCommGroup V]
    [Module K V] [Module R V] [IsScalarTower R K V] (Λ : Submodule R V) (f : V →ₗ[K] V)
    (hinj : Function.Injective f) (hsurj : Function.Surjective f) (hΛ : ∀ x, x ∈ Λ ↔ f x ∈ Λ)
    (w : ι → V) :
    (Submodule.span R (Set.range fun a => f (w a))).toAddSubgroup.relIndex
        (Λ.toAddSubgroup ⊓ (Submodule.span K (Set.range fun a => f (w a))).toAddSubgroup) =
      (Submodule.span R (Set.range w)).toAddSubgroup.relIndex
        (Λ.toAddSubgroup ⊓ (Submodule.span K (Set.range w)).toAddSubgroup) := by
  let g : V →+ V := f.toAddMonoidHom
  have hg : Function.Injective g := hinj
  have hΛmap : Λ.toAddSubgroup.map g = Λ.toAddSubgroup := by
    ext v
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hΛ x).1 hx
    · intro hv
      obtain ⟨x, rfl⟩ := hsurj v
      exact ⟨x, (hΛ x).2 hv, rfl⟩
  have hK : Submodule.span K (Set.range fun a => f (w a)) = (Submodule.span K (Set.range w)).map f := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hR : Submodule.span R (Set.range fun a => f (w a)) =
      (Submodule.span R (Set.range w)).map (f.restrictScalars R) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hKg : ((Submodule.span K (Set.range w)).map f).toAddSubgroup =
      (Submodule.span K (Set.range w)).toAddSubgroup.map g := by
    ext v
    simp [Submodule.mem_map, AddSubgroup.mem_map, g]
  have hRg : ((Submodule.span R (Set.range w)).map (f.restrictScalars R)).toAddSubgroup =
      (Submodule.span R (Set.range w)).toAddSubgroup.map g := by
    ext v
    simp [Submodule.mem_map, AddSubgroup.mem_map, g]
  have hinf : Λ.toAddSubgroup ⊓ (Submodule.span K (Set.range w)).toAddSubgroup.map g =
      (Λ.toAddSubgroup ⊓ (Submodule.span K (Set.range w)).toAddSubgroup).map g := by
    rw [AddSubgroup.map_inf_eq _ _ _ hg, hΛmap]
  rw [hK, hR, hKg, hRg, hinf, AddSubgroup.relIndex_map_map_of_injective _ _ hg]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Introduce `r X d hd γ hγ x hx`. Establish `hmat : ∀ τ : X.Ψ, mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ` using `fun τ => rfl`. Establish `hγdet : (γ : Matrix (Fin r) (Fin r) E).det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero`. Establish `hτdet : ∀ τ : X.Ψ, ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det ≠ 0`. Introduce `τ`.

Use `τ.1.map_det (γ : Matrix (Fin r) (Fin r) E)` as an intermediate fact. Rewrite `this` using `[RingHom.mapMatrix_apply]`. Rewrite using `[← this]`. Conclude with `(map_ne_zero τ.1).2 hγdet`. Establish `hx' : ∀ τ : X.Ψ, (mat (lact γ x) τ).det ≠ 0`.

Introduce `τ`. Rewrite using `[hmat, Matrix.det_mul]`. Conclude with `mul_ne_zero (hτdet τ) (hx τ)`. Use `⟨hx', fun W => ?_⟩` and prove the remaining obligations. Take `⟨w, hw, hwΛ, hsp⟩` from `GlobalTheory.LatBasis.exists_basis_mem r X W`.

Use `set f := (γ : Matrix (Fin r) (Fin r) E).mulVecLin with hf`. Establish `hinj : Function.Injective f` using `Matrix.mulVec_injective_of_isUnit γ.isUnit`. Establish `hsurj : Function.Surjective f` using `LinearMap.injective_iff_surjective.1 hinj`. Establish `hΛ : ∀ y, y ∈ X.Λ ↔ f y ∈ X.Λ` using `hγ.2`. Establish `hw' : LinearIndependent E (fun a => f (w a))` using `hw.map' f (LinearMap.ker_eq_bot.2 hinj)`.

Establish `hsp' : W.map f = Submodule.span E (Set.range fun a => f (w a))` using `by conv_lhs => rw [← hsp]`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Establish `e1` using `hd (lact γ x) hx' _ (fun a => f (w a)) hw' (fun a => (hΛ _).1 (hwΛ a))`. Establish `e2` using `hd x hx _ w hw hwΛ`.

Establish `hM : ∀ τ : X.Ψ, (mat (lact γ x) τ)⁻¹ * (Matrix.of fun k a => τ.1 (f (w a) k)) = (mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k))`. Introduce `τ`. Establish `: (Matrix.of fun k a => τ.1 (f (w a) k)) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (Matrix.of fun k a => τ.1 (w a k))`. Use extensionality with `k a`. Simplify using `[hf, Matrix.mul_apply, Matrix.mulVec, dotProduct]`.

Rewrite using `[this, hmat, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (hτdet τ).isUnit]`. Rewrite using `[hsp', e1, relIndex_span_map X.Λ f hinj hsurj hΛ w]`. Rewrite `e2` using `[hsp]`. Rewrite using `[e2, hsp]`. Simplify using `only [hM]`.
-/
theorem height_lact : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → (∀ τ : X.Ψ, (mat (lact γ x) τ).det ≠ 0) ∧ ∀ W : Submodule E (Fin r → E), d (lact γ x) (W.map (γ : Matrix (Fin r) (Fin r) E).mulVecLin) = d x W) := by
  intro r X d hd γ hγ x hx
  have hmat : ∀ τ : X.Ψ, mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ :=
    fun τ => rfl
  have hγdet : (γ : Matrix (Fin r) (Fin r) E).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero
  have hτdet : ∀ τ : X.Ψ, ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det ≠ 0 := by
    intro τ
    have := τ.1.map_det (γ : Matrix (Fin r) (Fin r) E)
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (map_ne_zero τ.1).2 hγdet
  have hx' : ∀ τ : X.Ψ, (mat (lact γ x) τ).det ≠ 0 := by
    intro τ
    rw [hmat, Matrix.det_mul]
    exact mul_ne_zero (hτdet τ) (hx τ)
  refine ⟨hx', fun W => ?_⟩
  obtain ⟨w, hw, hwΛ, hsp⟩ := GlobalTheory.LatBasis.exists_basis_mem r X W
  set f := (γ : Matrix (Fin r) (Fin r) E).mulVecLin with hf
  have hinj : Function.Injective f := Matrix.mulVec_injective_of_isUnit γ.isUnit
  have hsurj : Function.Surjective f := LinearMap.injective_iff_surjective.1 hinj
  have hΛ : ∀ y, y ∈ X.Λ ↔ f y ∈ X.Λ := hγ.2
  have hw' : LinearIndependent E (fun a => f (w a)) :=
    hw.map' f (LinearMap.ker_eq_bot.2 hinj)
  have hsp' : W.map f = Submodule.span E (Set.range fun a => f (w a)) := by
    conv_lhs => rw [← hsp]
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  have e1 := hd (lact γ x) hx' _ (fun a => f (w a)) hw' (fun a => (hΛ _).1 (hwΛ a))
  have e2 := hd x hx _ w hw hwΛ
  have hM : ∀ τ : X.Ψ, (mat (lact γ x) τ)⁻¹ * (Matrix.of fun k a => τ.1 (f (w a) k)) =
      (mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)) := by
    intro τ
    have : (Matrix.of fun k a => τ.1 (f (w a) k)) =
        (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (Matrix.of fun k a => τ.1 (w a k)) := by
      ext k a
      simp [hf, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [this, hmat, Matrix.mul_inv_rev, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hτdet τ).isUnit]
  rw [hsp', e1, relIndex_span_map X.Λ f hinj hsurj hΛ w]
  rw [hsp] at e2
  rw [e2, hsp]
  simp only [hM]

end GlobalTheory.HeightInv
