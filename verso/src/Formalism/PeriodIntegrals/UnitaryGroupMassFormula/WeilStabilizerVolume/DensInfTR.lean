import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensInfSS

noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open scoped TensorProduct
open PI.AdicCompletionValuation

/- English proof (translation)
Set `e1 : (κ → X) ≃ₜ (κ → Fin k → ℝ)` to `Homeomorph.piCongrRight fun _ => e`. Establish `h1 : ∀ x y, e1 (x + y) = e1 x + e1 y`. Introduce `x y`. Use function extensionality and compare the values at `i`. Conclude with `he (x i) (y i)`.

Set `L` to `ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := κ → Fin k → ℝ) (F := Fin (Module.finrank ℝ (κ → Fin k → ℝ)) → ℝ) (Module.finrank_fin_fun ℝ).symm`. Use `⟨_, e1.trans L.toHomeomorph, fun x y => ?_⟩` and prove the remaining obligations. Use `show L (e1 (x + y)) = L (e1 x) + L (e1 y)`. Rewrite using `[h1, map_add]`.
-/
theorem exists_coord_pi {X : Type} [AddCommGroup X] [TopologicalSpace X] {k : ℕ}
    (e : X ≃ₜ (Fin k → ℝ)) (he : ∀ x y, e (x + y) = e x + e y) (κ : Type) [Fintype κ] :
    ∃ (n : ℕ) (e' : (κ → X) ≃ₜ (Fin n → ℝ)), ∀ x y, e' (x + y) = e' x + e' y := by
  let e1 : (κ → X) ≃ₜ (κ → Fin k → ℝ) := Homeomorph.piCongrRight fun _ => e
  have h1 : ∀ x y, e1 (x + y) = e1 x + e1 y := by
    intro x y; funext i; exact he (x i) (y i)
  let L := ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := κ → Fin k → ℝ)
    (F := Fin (Module.finrank ℝ (κ → Fin k → ℝ)) → ℝ) (Module.finrank_fin_fun ℝ).symm
  refine ⟨_, e1.trans L.toHomeomorph, fun x y => ?_⟩
  show L (e1 (x + y)) = L (e1 x) + L (e1 y)
  rw [h1, map_add]

/- English proof (translation)
Set `e1 : Ainf F ≃ₜ (InfinitePlace F → ℝ)` to `Homeomorph.piCongrRight fun v => (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).toHomeomorph`. Establish `h1 : ∀ x y, e1 (x + y) = e1 x + e1 y`. Introduce `x y`. Use function extensionality and compare the values at `v`. Conclude with `(InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).map_add _ _`.

Set `L` to `ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := InfinitePlace F → ℝ) (F := Fin (Module.finrank ℝ (InfinitePlace F → ℝ)) → ℝ) (Module.finrank_fin_fun ℝ).symm`. Use `⟨_, e1.trans L.toHomeomorph, fun x y => ?_⟩` and prove the remaining obligations. Use `show L (e1 (x + y)) = L (e1 x) + L (e1 y)`. Rewrite using `[h1, map_add]`.
-/
theorem exists_coord_Ainf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    ∃ (k : ℕ) (e : Ainf F ≃ₜ (Fin k → ℝ)), ∀ x y, e (x + y) = e x + e y := by
  let e1 : Ainf F ≃ₜ (InfinitePlace F → ℝ) :=
    Homeomorph.piCongrRight fun v =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).toHomeomorph
  have h1 : ∀ x y, e1 (x + y) = e1 x + e1 y := by
    intro x y; funext v
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).map_add _ _
  let L := ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := InfinitePlace F → ℝ)
    (F := Fin (Module.finrank ℝ (InfinitePlace F → ℝ)) → ℝ) (Module.finrank_fin_fun ℝ).symm
  refine ⟨_, e1.trans L.toHomeomorph, fun x y => ?_⟩
  show L (e1 (x + y)) = L (e1 x) + L (e1 y)
  rw [h1, map_add]

/- English proof (translation)
Set `R` to `Ainf F`. Set `b` to `Module.Free.chooseBasis R (R ⊗[F] E)`. Set `eL : (R ⊗[F] E) ≃ₗ[R] (Module.Free.ChooseBasisIndex R (R ⊗[F] E) → R)` to `b.equivFun`. Set `e0 : R ⊗[F] E ≃ₜ (Module.Free.ChooseBasisIndex R (R ⊗[F] E) → R)` to `{ toEquiv := eL.toEquiv continuous_toFun := IsModuleTopology.continuous_of_linearMap eL.toLinearMap continuous_invFun := IsModuleTopology.continuous_of_linearMap eL.symm.toLinearMap }`. Take `⟨k0, eA, hA⟩` from `exists_coord_Ainf F`.

Take `⟨k, e1, h1⟩` from `exists_coord_pi eA hA (Module.Free.ChooseBasisIndex R (R ⊗[F] E))`. Use `⟨k, e0.trans e1, fun x y => ?_⟩` and prove the remaining obligations. Use `show e1 (e0 (x + y)) = e1 (e0 x) + e1 (e0 y)`. Rewrite using `[show e0 (x + y) = e0 x + e0 y from eL.map_add x y, h1]`.
-/
theorem exists_coord_tens (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E]
    [NumberField E] [Algebra F E] :
    ∃ (k : ℕ) (e : Ainf F ⊗[F] E ≃ₜ (Fin k → ℝ)), ∀ x y, e (x + y) = e x + e y := by
  classical
  let R := Ainf F
  let b := Module.Free.chooseBasis R (R ⊗[F] E)
  let eL : (R ⊗[F] E) ≃ₗ[R] (Module.Free.ChooseBasisIndex R (R ⊗[F] E) → R) := b.equivFun
  let e0 : R ⊗[F] E ≃ₜ (Module.Free.ChooseBasisIndex R (R ⊗[F] E) → R) :=
    { toEquiv := eL.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap eL.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap eL.symm.toLinearMap }
  obtain ⟨k0, eA, hA⟩ := exists_coord_Ainf F
  obtain ⟨k, e1, h1⟩ := exists_coord_pi eA hA (Module.Free.ChooseBasisIndex R (R ⊗[F] E))
  refine ⟨k, e0.trans e1, fun x y => ?_⟩
  show e1 (e0 (x + y)) = e1 (e0 x) + e1 (e0 y)
  rw [show e0 (x + y) = e0 x + e0 y from eL.map_add x y, h1]

/- English proof (translation)
Set `eA : X →+ (Fin N → ℝ)` to `AddMonoidHom.mk' e he`. Establish `hq : ∀ (q : ℚ), ∀ x ∈ H, (q : ℝ) • e x ∈ e '' (H : Set X)`. Introduce `q x hx`. Take `⟨y, hy, hyx⟩` from `hdiv q.den q.den_pos x hx`. Use `⟨q.num • y, H.zsmul_mem hy _, ?_⟩` and prove the remaining obligations.

Establish `e1 : e (q.num • y) = (q.num : ℝ) • e y`. Rewrite using `[show e (q.num • y) = eA (q.num • y) from rfl, map_zsmul, Int.cast_smul_eq_zsmul]`. Both sides reduce to the same expression. Establish `e2 : e x = (q.den : ℝ) • e y`. Rewrite using `[← hyx, show e (q.den • y) = eA (q.den • y) from rfl, map_nsmul, Nat.cast_smul_eq_nsmul]`.

Both sides reduce to the same expression. Rewrite using `[e1, e2, smul_smul]`. Use `congr 1`. Conclude with `(Rat.mul_den_eq_num q).symm` after adjusting the coercions. Establish `hcl : IsClosed (e '' (H : Set X))` using `e.isClosedMap _ hH`.

Set `W : Submodule ℝ (Fin N → ℝ)` to `{ carrier := e '' (H : Set X) add_mem' := by`. Introduce and unpack `_ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩`. Conclude with `⟨x + y, H.add_mem hx hy, he x y⟩`. Use the proof step `zero_mem' := ⟨0, H.zero_mem, map_zero eA⟩`. Use the proof step `smul_mem' := by`.

Introduce and unpack `r _ ⟨x, hx, rfl⟩`. Establish `hc : IsClosed {s : ℝ | s • e x ∈ e '' (H : Set X)}` using `hcl.preimage (continuous_id.smul continuous_const)`. Establish `hsub : Set.range ((↑) : ℚ → ℝ) ⊆ {s : ℝ | s • e x ∈ e '' (H : Set X)}`. Introduce and unpack `_ ⟨q, rfl⟩`. Conclude with `hq q x hx`.

Use `(hc.closure_subset_iff.2 hsub) (Rat.denseRange_cast (𝕜 := ℝ) r)` as an intermediate fact. Conclude with `this }`. Set `e0 : H ≃ₜ W` to `e.subtype (p := fun x => x ∈ H) (q := fun y => y ∈ W) (fun x => by`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Conclude with `⟨x, hx, rfl⟩`. Introduce and unpack `⟨x', hx', hx'e⟩`. Rewrite using `[← e.injective hx'e]`. Conclude with `hx')`. Set `L` to `ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := W) (F := Fin (Module.finrank ℝ W) → ℝ) (Module.finrank_fin_fun ℝ).symm`.

Use `⟨_, e0.trans L.toHomeomorph, fun x y => ?_⟩` and prove the remaining obligations. Use `show L (e0 (x + y)) = L (e0 x) + L (e0 y)`. Rewrite using `[show e0 (x + y) = e0 x + e0 y from Subtype.ext (he x y), map_add]`.
-/
theorem exists_coord_sub {X : Type} [AddCommGroup X] [TopologicalSpace X] {N : ℕ}
    (e : X ≃ₜ (Fin N → ℝ)) (he : ∀ x y, e (x + y) = e x + e y) (H : AddSubgroup X)
    (hH : IsClosed (H : Set X)) (hdiv : ∀ n : ℕ, 0 < n → ∀ x ∈ H, ∃ y ∈ H, n • y = x) :
    ∃ (m : ℕ) (eH : H ≃ₜ (Fin m → ℝ)), ∀ x y, eH (x + y) = eH x + eH y := by
  let eA : X →+ (Fin N → ℝ) := AddMonoidHom.mk' e he
  have hq : ∀ (q : ℚ), ∀ x ∈ H, (q : ℝ) • e x ∈ e '' (H : Set X) := by
    intro q x hx
    obtain ⟨y, hy, hyx⟩ := hdiv q.den q.den_pos x hx
    refine ⟨q.num • y, H.zsmul_mem hy _, ?_⟩
    have e1 : e (q.num • y) = (q.num : ℝ) • e y := by
      rw [show e (q.num • y) = eA (q.num • y) from rfl, map_zsmul, Int.cast_smul_eq_zsmul]; rfl
    have e2 : e x = (q.den : ℝ) • e y := by
      rw [← hyx, show e (q.den • y) = eA (q.den • y) from rfl, map_nsmul, Nat.cast_smul_eq_nsmul]
      rfl
    rw [e1, e2, smul_smul]
    congr 1
    exact_mod_cast (Rat.mul_den_eq_num q).symm
  have hcl : IsClosed (e '' (H : Set X)) := e.isClosedMap _ hH
  let W : Submodule ℝ (Fin N → ℝ) :=
    { carrier := e '' (H : Set X)
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, H.add_mem hx hy, he x y⟩
      zero_mem' := ⟨0, H.zero_mem, map_zero eA⟩
      smul_mem' := by
        rintro r _ ⟨x, hx, rfl⟩
        have hc : IsClosed {s : ℝ | s • e x ∈ e '' (H : Set X)} :=
          hcl.preimage (continuous_id.smul continuous_const)
        have hsub : Set.range ((↑) : ℚ → ℝ) ⊆ {s : ℝ | s • e x ∈ e '' (H : Set X)} := by
          rintro _ ⟨q, rfl⟩; exact hq q x hx
        have := (hc.closure_subset_iff.2 hsub) (Rat.denseRange_cast (𝕜 := ℝ) r)
        exact this }
  let e0 : H ≃ₜ W := e.subtype (p := fun x => x ∈ H) (q := fun y => y ∈ W) (fun x => by
    constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨x', hx', hx'e⟩; rw [← e.injective hx'e]; exact hx')
  let L := ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := W)
    (F := Fin (Module.finrank ℝ W) → ℝ) (Module.finrank_fin_fun ℝ).symm
  refine ⟨_, e0.trans L.toHomeomorph, fun x y => ?_⟩
  show L (e0 (x + y)) = L (e0 x) + L (e0 y)
  rw [show e0 (x + y) = e0 x + e0 y from Subtype.ext (he x y), map_add]

end PI.VolStabW
