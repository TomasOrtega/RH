import Mathlib
import GroundTheory.AutomorphicForms.MeasuresModulus
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.HaarMeasureGL

noncomputable section

open Matrix Module ValuativeRel MeasureTheory

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

/- English proof (translation)
Set `e : V ≃ₗ[k] (Fin (Module.finrank k V) → k)` to `(Module.finBasis k V).equivFun`. Set `ι : (Fin (Module.finrank k V) → k) →ₗ[k] Matrix (Fin n) (Fin n) k` to `V.subtype ∘ₗ e.symm.toLinearMap`. Establish `hι : ∀ c, ι c = ((e.symm c : V) : Matrix (Fin n) (Fin n) k)` using `fun c => rfl`. Establish `hιinj : Function.Injective ι` using `fun a b h => e.symm.injective (Subtype.ext h)`. Set `L : (Fin (Module.finrank k V) → k) ≃ₗ[k] (Fin (Module.finrank k V) → k)` to `(e.symm.trans φ).trans e`.

Establish `hdet : LinearEquiv.det L = LinearEquiv.det φ` using `LinearEquiv.det_conj φ e`. Set `X'` to `X.comap ι.toAddMonoidHom`. Set `Y'` to `Y.comap ι.toAddMonoidHom`. Establish `hXV : ∀ y ∈ X, y ∈ V` using `fun y hy => ((hX y).1 hy).1`. Establish `hYV : ∀ y ∈ Y, y ∈ V`.

Introduce `y hy`. Take `⟨x, -, rfl⟩` from `(hY y).1 hy`. Conclude with `(φ x).2`. Establish `hmap : ∀ W : AddSubgroup (Matrix (Fin n) (Fin n) k), (∀ y ∈ W, y ∈ V) → (W.comap ι.toAddMonoidHom).map ι.toAddMonoidHom = W`. Introduce `W hW`.

Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc, rfl⟩`. Conclude with `hc`. Introduce `hy`.

Use `⟨e ⟨y, hW y hy⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show ι (e ⟨y, hW y hy⟩) ∈ W`. Rewrite using `[hι, LinearEquiv.symm_apply_apply]`. Conclude with `hy`. Use `show ι (e ⟨y, hW y hy⟩) = y`.

Rewrite using `[hι, LinearEquiv.symm_apply_apply]`. Establish `hinf : (X ⊓ Y).comap ι.toAddMonoidHom = X' ⊓ Y'` using `AddSubgroup.comap_inf _ _ _`. Establish `i1 : (X ⊓ Y).relIndex X = (X' ⊓ Y').relIndex X'`. Rewrite using `[← hinf, AddSubgroup.relIndex_comap, hmap X hXV]`. Establish `i2 : (X ⊓ Y).relIndex Y = (X' ⊓ Y').relIndex Y'`.

Rewrite using `[← hinf, AddSubgroup.relIndex_comap, hmap Y hYV]`. Establish `hιc : Continuous ι` using `ι.continuous_on_pi`. Set `B : Set (Matrix (Fin n) (Fin n) k)` to `{M | ∀ i j, valuation k (M i j) ≤ γ}`. Establish `hXset : (X' : Set (Fin (Module.finrank k V) → k)) = ι ⁻¹' B`. Use extensionality with `c`.

Use `show ι c ∈ X ↔ ∀ i j, valuation k (ι c i j) ≤ γ`. Rewrite using `[hX]`. Conclude with `⟨fun h => h.2, fun h => ⟨by rw [hι]; exact (e.symm c).2, h⟩⟩`. Establish `hBo : IsOpen B`. Establish `: B = ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) k => M i j) ⁻¹' {x : k | valuation k x ≤ γ}`.

Use extensionality with `M`. Simplify using `[B]`. Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (GroundTheory.Automorphic.GLnLocal.isOpen_valuation_le k hγ).preimage (continuous_id.matrix_elem i j)`. Establish `hBc : IsCompact B`.

Establish `h : IsCompact (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => {x : k | valuation k x ≤ γ})` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k γ`. Establish `hs : B = (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => {x : k | valuation k x ≤ γ})`. Use extensionality with `M`. Prove the components needed by the constructor for the conclusion. Introduce `h i _ j _`.

Conclude with `h i j`. Introduce `h i j`. Conclude with `h i (Set.mem_univ _) j (Set.mem_univ _)`. Rewrite using `[hs]`. Conclude with `h`.

Establish `hXo : IsOpen (X' : Set (Fin (Module.finrank k V) → k))` using `hXset ▸ hBo.preimage hιc`. Take `⟨ρ, hρ⟩` from `ι.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hιinj)`. Set `cl : (Fin n × Fin n → k) →ₗ[k] Matrix (Fin n) (Fin n) k` to `{ toFun := fun f => Matrix.of fun i j => f (i, j) map_add' := fun f g => by ext; simp map_smul' := fun c f => by ext; simp }`. Establish `hρc : Continuous ρ`. Establish `h1 : (ρ : Matrix (Fin n) (Fin n) k → _) = (ρ ∘ₗ cl) ∘ (fun M p => M p.1 p.2)`.

Use function extensionality and compare the values at `M`. Simplify using `only [Function.comp_apply, LinearMap.coe_comp]`. Use `congr 1`. Rewrite using `[h1]`. Conclude with `(ρ ∘ₗ cl).continuous_on_pi.comp (continuous_pi fun p => continuous_id.matrix_elem p.1 p.2)`.

Establish `hsub : (X' : Set (Fin (Module.finrank k V) → k)) ⊆ ρ '' B`. Introduce `c hc`. Rewrite `hc` using `[hXset]`. Conclude with `⟨ι c, hc, LinearMap.congr_fun hρ c⟩`. Establish `hXc : IsCompact (X' : Set (Fin (Module.finrank k V) → k))` using `(hBc.image hρc).of_isClosed_subset (AddSubgroup.isClosed_of_isOpen X' hXo) hsub`.

Establish `hYset : (Y' : Set (Fin (Module.finrank k V) → k)) = L '' (X' : Set _)`. Use extensionality with `c`. Use `show ι c ∈ Y ↔ _`. Rewrite using `[hY]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, hxc⟩`. Use `⟨e x, ?_, ?_⟩` and prove the remaining obligations. Use `show ι (e x) ∈ X`. Rewrite using `[hι, LinearEquiv.symm_apply_apply]`. Conclude with `hx`.

Establish `h1 : φ x = e.symm c` using `Subtype.ext (by rw [hxc, hι]) show e (φ (e.symm (e x))) = c`. Rewrite using `[LinearEquiv.symm_apply_apply, h1, LinearEquiv.apply_symm_apply]`. Introduce and unpack `⟨c0, hc0, rfl⟩`. Use `⟨e.symm c0, hc0, ?_⟩` and prove the remaining obligations. Use `show ((φ (e.symm c0) : V) : Matrix (Fin n) (Fin n) k) = ι (e (φ (e.symm c0)))`.

Rewrite using `[hι, LinearEquiv.symm_apply_apply]`. Take `⟨n1, n2, hr⟩` from `ratio_pi X' Y' hXc hXo L hYset`. Rewrite using `[i1, i2]`. Conclude with `⟨n1, n2, by rw [hr, hdet]⟩`.
-/
theorem ratio (V : Submodule k (Matrix (Fin n) (Fin n) k)) (γ : ValueGroupWithZero k) (hγ : γ ≠ 0)
    (φ : V ≃ₗ[k] V) (X Y : AddSubgroup (Matrix (Fin n) (Fin n) k))
    (hX : ∀ y, y ∈ X ↔ y ∈ V ∧ ∀ i j, valuation k (y i j) ≤ γ)
    (hY : ∀ y, y ∈ Y ↔ ∃ x : V, (x : Matrix (Fin n) (Fin n) k) ∈ X ∧ ((φ x : V) : Matrix (Fin n) (Fin n) k) = y) :
    (X ⊓ Y).relIndex X ≠ 0 ∧ (X ⊓ Y).relIndex Y ≠ 0 ∧
      ((X ⊓ Y).relIndex Y : ℝ) / ((X ⊓ Y).relIndex X : ℝ) = (distribHaarChar k (LinearEquiv.det φ) : ℝ) := by
  classical
  let e : V ≃ₗ[k] (Fin (Module.finrank k V) → k) := (Module.finBasis k V).equivFun
  let ι : (Fin (Module.finrank k V) → k) →ₗ[k] Matrix (Fin n) (Fin n) k := V.subtype ∘ₗ e.symm.toLinearMap
  have hι : ∀ c, ι c = ((e.symm c : V) : Matrix (Fin n) (Fin n) k) := fun c => rfl
  have hιinj : Function.Injective ι := fun a b h => e.symm.injective (Subtype.ext h)
  let L : (Fin (Module.finrank k V) → k) ≃ₗ[k] (Fin (Module.finrank k V) → k) := (e.symm.trans φ).trans e
  have hdet : LinearEquiv.det L = LinearEquiv.det φ := LinearEquiv.det_conj φ e
  let X' := X.comap ι.toAddMonoidHom
  let Y' := Y.comap ι.toAddMonoidHom
  have hXV : ∀ y ∈ X, y ∈ V := fun y hy => ((hX y).1 hy).1
  have hYV : ∀ y ∈ Y, y ∈ V := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := (hY y).1 hy
    exact (φ x).2
  have hmap : ∀ W : AddSubgroup (Matrix (Fin n) (Fin n) k), (∀ y ∈ W, y ∈ V) →
      (W.comap ι.toAddMonoidHom).map ι.toAddMonoidHom = W := by
    intro W hW
    ext y
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact hc
    · intro hy
      refine ⟨e ⟨y, hW y hy⟩, ?_, ?_⟩
      · show ι (e ⟨y, hW y hy⟩) ∈ W
        rw [hι, LinearEquiv.symm_apply_apply]
        exact hy
      · show ι (e ⟨y, hW y hy⟩) = y
        rw [hι, LinearEquiv.symm_apply_apply]
  have hinf : (X ⊓ Y).comap ι.toAddMonoidHom = X' ⊓ Y' := AddSubgroup.comap_inf _ _ _
  have i1 : (X ⊓ Y).relIndex X = (X' ⊓ Y').relIndex X' := by
    rw [← hinf, AddSubgroup.relIndex_comap, hmap X hXV]
  have i2 : (X ⊓ Y).relIndex Y = (X' ⊓ Y').relIndex Y' := by
    rw [← hinf, AddSubgroup.relIndex_comap, hmap Y hYV]

  have hιc : Continuous ι := ι.continuous_on_pi
  let B : Set (Matrix (Fin n) (Fin n) k) := {M | ∀ i j, valuation k (M i j) ≤ γ}
  have hXset : (X' : Set (Fin (Module.finrank k V) → k)) = ι ⁻¹' B := by
    ext c
    show ι c ∈ X ↔ ∀ i j, valuation k (ι c i j) ≤ γ
    rw [hX]
    exact ⟨fun h => h.2, fun h => ⟨by rw [hι]; exact (e.symm c).2, h⟩⟩
  have hBo : IsOpen B := by
    have : B = ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) k => M i j) ⁻¹' {x : k | valuation k x ≤ γ} := by
      ext M; simp [B]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (GroundTheory.Automorphic.GLnLocal.isOpen_valuation_le k hγ).preimage (continuous_id.matrix_elem i j)
  have hBc : IsCompact B := by
    have h : IsCompact (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => {x : k | valuation k x ≤ γ}) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k γ
    have hs : B = (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => {x : k | valuation k x ≤ γ}) := by
      ext M
      constructor
      · intro h i _ j _
        exact h i j
      · intro h i j
        exact h i (Set.mem_univ _) j (Set.mem_univ _)
    rw [hs]; exact h
  have hXo : IsOpen (X' : Set (Fin (Module.finrank k V) → k)) := hXset ▸ hBo.preimage hιc
  obtain ⟨ρ, hρ⟩ := ι.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hιinj)
  let cl : (Fin n × Fin n → k) →ₗ[k] Matrix (Fin n) (Fin n) k :=
    { toFun := fun f => Matrix.of fun i j => f (i, j)
      map_add' := fun f g => by ext; simp
      map_smul' := fun c f => by ext; simp }
  have hρc : Continuous ρ := by
    have h1 : (ρ : Matrix (Fin n) (Fin n) k → _) = (ρ ∘ₗ cl) ∘ (fun M p => M p.1 p.2) := by
      funext M
      simp only [Function.comp_apply, LinearMap.coe_comp]
      congr 1
    rw [h1]
    exact (ρ ∘ₗ cl).continuous_on_pi.comp (continuous_pi fun p => continuous_id.matrix_elem p.1 p.2)
  have hsub : (X' : Set (Fin (Module.finrank k V) → k)) ⊆ ρ '' B := by
    intro c hc
    rw [hXset] at hc
    exact ⟨ι c, hc, LinearMap.congr_fun hρ c⟩
  have hXc : IsCompact (X' : Set (Fin (Module.finrank k V) → k)) :=
    (hBc.image hρc).of_isClosed_subset (AddSubgroup.isClosed_of_isOpen X' hXo) hsub
  have hYset : (Y' : Set (Fin (Module.finrank k V) → k)) = L '' (X' : Set _) := by
    ext c
    show ι c ∈ Y ↔ _
    rw [hY]
    constructor
    · rintro ⟨x, hx, hxc⟩
      refine ⟨e x, ?_, ?_⟩
      · show ι (e x) ∈ X
        rw [hι, LinearEquiv.symm_apply_apply]; exact hx
      · have h1 : φ x = e.symm c := Subtype.ext (by rw [hxc, hι])
        show e (φ (e.symm (e x))) = c
        rw [LinearEquiv.symm_apply_apply, h1, LinearEquiv.apply_symm_apply]
    · rintro ⟨c0, hc0, rfl⟩
      refine ⟨e.symm c0, hc0, ?_⟩
      show ((φ (e.symm c0) : V) : Matrix (Fin n) (Fin n) k) = ι (e (φ (e.symm c0)))
      rw [hι, LinearEquiv.symm_apply_apply]
  obtain ⟨n1, n2, hr⟩ := ratio_pi X' Y' hXc hXo L hYset
  rw [i1, i2]
  exact ⟨n1, n2, by rw [hr, hdet]⟩

end PositivityTheory.RgUd.T.Nil.Orb.BModbound
