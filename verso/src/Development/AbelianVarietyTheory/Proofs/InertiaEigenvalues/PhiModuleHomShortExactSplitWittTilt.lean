import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory

/- English proof (translation)
Set `g₁ : ↥T₁.L.T →ₗ[O] ↥T₂.L.T` to `(g.f.restrictScalars O).restrict g.T_le`. Set `f₁ : ↥T₀.L.T →ₗ[O] ↥T₁.L.T` to `(f.f.restrictScalars O).restrict f.T_le`. Establish `hg₁s : Function.Surjective g₁`. Introduce and unpack `⟨y, hy⟩`. Take `⟨x, hx, hxy⟩` from `hS.2.2.1 y hy`.

Conclude with `⟨⟨x, hx⟩, Subtype.ext hxy⟩`. Use `haveI : Module.Free O ↥T₂.L.T := T₂.L.free`. Take `⟨s, hs⟩` from `Module.projective_lifting_property g₁ LinearMap.id hg₁s`. Establish `hs' : ∀ y, g₁ (s y) = y` using `fun y => LinearMap.congr_fun hs y`. Establish `hf₁i : Function.Injective f₁` using `fun x y h => Subtype.ext (hS.1 (congrArg Subtype.val h))`.

Establish `hgf : ∀ y, g₁ (f₁ y) = 0` using `fun y => Subtype.ext ((hS.2.2.2.1 _).2 ⟨y, rfl⟩)`. Set `p : ↥T₁.L.T →ₗ[O] ↥T₁.L.T` to `LinearMap.id - s ∘ₗ g₁`. Establish `hp : ∀ x, p x ∈ LinearMap.range f₁`. Introduce `x`. Establish `h0 : g₁ (p x) = 0`.

Simplify using `only [p, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, hs', sub_self]`. Take `⟨y, hy⟩` from `(hS.2.2.2.1 _).1 (congrArg Subtype.val h0)`. Establish `hy0 : y ∈ T₀.L.T` using `hS.2.2.2.2 y (hy ▸ (p x).2)`. Conclude with `⟨⟨y, hy0⟩, Subtype.ext hy⟩`. Set `r : ↥T₁.L.T →ₗ[O] ↥T₀.L.T` to `(LinearEquiv.ofInjective f₁ hf₁i).symm.toLinearMap ∘ₗ p.codRestrict (LinearMap.range f₁) hp`.

Establish `hr : ∀ y, r (f₁ y) = y`. Introduce `y`. Establish `h1 : p.codRestrict (LinearMap.range f₁) hp (f₁ y) = LinearEquiv.ofInjective f₁ hf₁i y`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[p, hgf]`.

Simplify using `only [r, LinearMap.comp_apply, h1, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]`. Set `Sw` to `s.baseChange (OW l O)`. Set `Rw` to `r.baseChange (OW l O)`. Establish `hSw : ∀ x, latW g (Sw x) = x`. Introduce `x`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul c y`. Simplify using `only [Sw, LinearMap.baseChange_tmul, latW, TensorProduct.map_tmul, LinearMap.id_apply]`. Conclude with `congrArg _ (hs' y)`.

Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Establish `hRw : ∀ x, Rw (latW f x) = x`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul c y`. Simplify using `only [Rw, LinearMap.baseChange_tmul, latW, TensorProduct.map_tmul, LinearMap.id_apply]`. Conclude with `congrArg _ (hr y)`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Set `SL : (μ → OW l O) →ₗ[OW l O] (κ → OW l O)` to `I₁.j.symm.toLinearMap ∘ₗ Sw ∘ₗ I₂.j.toLinearMap`.

Set `RL : (κ → OW l O) →ₗ[OW l O] (ι → OW l O)` to `I₀.j.symm.toLinearMap ∘ₗ Rw ∘ₗ I₁.j.toLinearMap`. Establish `hSL : homW t ϖ H ∘ₗ SL = LinearMap.id`. Use `LinearMap.ext fun v => I₂.j.injective ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, hH]`. Simplify using `only [SL, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hSw, LinearMap.id_apply]`.

Establish `hRL : RL ∘ₗ homW t ϖ F = LinearMap.id`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `I₀.j.symm (Rw (I₁.j (homW t ϖ F v))) = v`. Rewrite using `[hF, hRw, LinearEquiv.symm_apply_apply]`. Establish `hM : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (M : Matrix α β (OW l O)), LinearMap.toMatrix' M.mulVecLin = M` using `fun M => LinearMap.toMatrix'_toLin' M`.

Use `⟨⟨LinearMap.toMatrix' SL, ?_⟩, ⟨LinearMap.toMatrix' RL, ?_⟩⟩` and prove the remaining obligations. Establish `h` using `congrArg LinearMap.toMatrix' hSL`. Rewrite `h` using `[LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id]`. Rewrite using `[← h, homW, hM]`. Establish `h` using `congrArg LinearMap.toMatrix' hRL`.

Rewrite `h` using `[LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id]`. Rewrite using `[← h, homW, hM]`.
-/
theorem phiModuleHom_shortExact_split_wittTilt {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {G : Type}
    [Group G] [TopologicalSpace G] {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype μ] [DecidableEq μ] {P₀ : PhiMod O K l e a ι} {P₁ : PhiMod O K l e a κ} {P₂ : PhiMod O K l e a μ}
    {T₀ T₁ T₂ : LocLat G ℚ_[l] K O} {I₀ : Ident t ϖ P₀ T₀} {I₁ : Ident t ϖ P₁ T₁} {I₂ : Ident t ϖ P₂ T₂}
    {f : LatHom T₀.L T₁.L} {g : LatHom T₁.L T₂.L} {F : GlobalTheory.BK.Hom P₀ P₁} {H : GlobalTheory.BK.Hom P₁ P₂}
    (hS : IsSESLat (Qp := ℚ_[l]) f g) (hF : IsMapOf I₀ I₁ f F) (hH : IsMapOf I₁ I₂ g H) :
    (∃ Z : Matrix κ μ (OW l O), (homMat t ϖ H).map (inclO l O) * Z = 1) ∧
      (∃ Y : Matrix ι κ (OW l O), Y * (homMat t ϖ F).map (inclO l O) = 1) := by
  classical

  let g₁ : ↥T₁.L.T →ₗ[O] ↥T₂.L.T := (g.f.restrictScalars O).restrict g.T_le
  let f₁ : ↥T₀.L.T →ₗ[O] ↥T₁.L.T := (f.f.restrictScalars O).restrict f.T_le
  have hg₁s : Function.Surjective g₁ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := hS.2.2.1 y hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  haveI : Module.Free O ↥T₂.L.T := T₂.L.free
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g₁ LinearMap.id hg₁s
  have hs' : ∀ y, g₁ (s y) = y := fun y => LinearMap.congr_fun hs y
  have hf₁i : Function.Injective f₁ := fun x y h => Subtype.ext (hS.1 (congrArg Subtype.val h))
  have hgf : ∀ y, g₁ (f₁ y) = 0 := fun y => Subtype.ext ((hS.2.2.2.1 _).2 ⟨y, rfl⟩)
  let p : ↥T₁.L.T →ₗ[O] ↥T₁.L.T := LinearMap.id - s ∘ₗ g₁
  have hp : ∀ x, p x ∈ LinearMap.range f₁ := by
    intro x
    have h0 : g₁ (p x) = 0 := by
      simp only [p, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, hs', sub_self]
    obtain ⟨y, hy⟩ := (hS.2.2.2.1 _).1 (congrArg Subtype.val h0)
    have hy0 : y ∈ T₀.L.T := hS.2.2.2.2 y (hy ▸ (p x).2)
    exact ⟨⟨y, hy0⟩, Subtype.ext hy⟩
  let r : ↥T₁.L.T →ₗ[O] ↥T₀.L.T :=
    (LinearEquiv.ofInjective f₁ hf₁i).symm.toLinearMap ∘ₗ p.codRestrict (LinearMap.range f₁) hp
  have hr : ∀ y, r (f₁ y) = y := by
    intro y
    have h1 : p.codRestrict (LinearMap.range f₁) hp (f₁ y) = LinearEquiv.ofInjective f₁ hf₁i y := by
      apply Subtype.ext
      simp [p, hgf]
    simp only [r, LinearMap.comp_apply, h1, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

  let Sw := s.baseChange (OW l O)
  let Rw := r.baseChange (OW l O)
  have hSw : ∀ x, latW g (Sw x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c y =>
      simp only [Sw, LinearMap.baseChange_tmul, latW, TensorProduct.map_tmul, LinearMap.id_apply]
      exact congrArg _ (hs' y)
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hRw : ∀ x, Rw (latW f x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c y =>
      simp only [Rw, LinearMap.baseChange_tmul, latW, TensorProduct.map_tmul, LinearMap.id_apply]
      exact congrArg _ (hr y)
    | add x y hx hy => rw [map_add, map_add, hx, hy]

  let SL : (μ → OW l O) →ₗ[OW l O] (κ → OW l O) := I₁.j.symm.toLinearMap ∘ₗ Sw ∘ₗ I₂.j.toLinearMap
  let RL : (κ → OW l O) →ₗ[OW l O] (ι → OW l O) := I₀.j.symm.toLinearMap ∘ₗ Rw ∘ₗ I₁.j.toLinearMap
  have hSL : homW t ϖ H ∘ₗ SL = LinearMap.id := by
    refine LinearMap.ext fun v => I₂.j.injective ?_
    rw [LinearMap.comp_apply, hH]
    simp only [SL, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hSw,
      LinearMap.id_apply]
  have hRL : RL ∘ₗ homW t ϖ F = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    change I₀.j.symm (Rw (I₁.j (homW t ϖ F v))) = v
    rw [hF, hRw, LinearEquiv.symm_apply_apply]
  have hM : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (M : Matrix α β (OW l O)), LinearMap.toMatrix' M.mulVecLin = M := fun M => LinearMap.toMatrix'_toLin' M
  refine ⟨⟨LinearMap.toMatrix' SL, ?_⟩, ⟨LinearMap.toMatrix' RL, ?_⟩⟩
  · have h := congrArg LinearMap.toMatrix' hSL
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at h
    rw [← h, homW, hM]
  · have h := congrArg LinearMap.toMatrix' hRL
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at h
    rw [← h, homW, hM]

end GlobalTheory
