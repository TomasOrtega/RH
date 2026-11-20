import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.SmGL.ParIndAdm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {W : Type} [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Take `⟨R, hR⟩` from `(GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := n)).elim_finite_subcover (fun x : GL n k => (fun y => x⁻¹ * y) ⁻¹' (K : Set (GL n k))) (fun x => hK.preimage (by fun_prop)) (fun w _ => Set.mem_iUnion.2 ⟨w, by simp [one_mem]⟩)`. Use `⟨R, fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨r, hr, h⟩` from `Set.mem_iUnion₂.1 (hR hw)`. Conclude with `⟨r, hr, h⟩`.
-/
theorem exists_finset_KO_cover (K : Subgroup (GL n k)) (hK : IsOpen (K : Set (GL n k))) :
    ∃ R : Finset (GL n k), ∀ w ∈ KO k n, ∃ r ∈ R, r⁻¹ * w ∈ K := by
  obtain ⟨R, hR⟩ := (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := n)).elim_finite_subcover
    (fun x : GL n k => (fun y => x⁻¹ * y) ⁻¹' (K : Set (GL n k)))
    (fun x => hK.preimage (by fun_prop))
    (fun w _ => Set.mem_iUnion.2 ⟨w, by simp [one_mem]⟩)
  refine ⟨R, fun w hw => ?_⟩
  obtain ⟨r, hr, h⟩ := Set.mem_iUnion₂.1 (hR hw)
  exact ⟨r, hr, h⟩

/- English proof (translation)
Establish `hfix : ∀ κ ∈ K, ∀ x, f.1.1 (x * κ) = f.1.1 x` using `fun κ hκ x => by`. Use `congrArg (fun φ : IndSp e ρ => φ.1.1 x) (hf ⟨κ, hκ⟩)` as an intermediate fact. Simplify using `using this`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `x`. Take `⟨u, l, w, hw, rfl⟩` from `UnitInd.exists_iwasawa e x`. Take `⟨r, hr, hrw⟩` from `hR w hw`. Set `p : parab k e` to `⟨(u : GL n k) * leviEmb k e l, mul_mem (unipRad_le_parab k e u.2) (leviEmb_mem_parab k e l)⟩`. Establish `hw' : f.1.1 w = 0`.

Use `hfix _ hrw r` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`. Rewrite using `[this, h0 r hr]`. Use `show f.1.1 ((p : GL n k) * w) = 0`. Rewrite using `[parInd_law, hw', map_zero, smul_zero]`.
-/
theorem eq_zero_of_fixed (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) (K : Subgroup (GL n k))
    (R : Finset (GL n k)) (hR : ∀ w ∈ KO k n, ∃ r ∈ R, r⁻¹ * w ∈ K)
    (f : IndSp e ρ) (hf : f ∈ fixed (parInd e ρ) K) (h0 : ∀ r ∈ R, f.1.1 r = 0) : f = 0 := by
  have hfix : ∀ κ ∈ K, ∀ x, f.1.1 (x * κ) = f.1.1 x := fun κ hκ x => by
    have := congrArg (fun φ : IndSp e ρ => φ.1.1 x) (hf ⟨κ, hκ⟩)
    simpa using this
  apply Subtype.ext; apply Subtype.ext; funext x
  obtain ⟨u, l, w, hw, rfl⟩ := UnitInd.exists_iwasawa e x
  obtain ⟨r, hr, hrw⟩ := hR w hw
  let p : parab k e := ⟨(u : GL n k) * leviEmb k e l,
    mul_mem (unipRad_le_parab k e u.2) (leviEmb_mem_parab k e l)⟩
  have hw' : f.1.1 w = 0 := by
    have := hfix _ hrw r
    rw [mul_inv_cancel_left] at this
    rw [this, h0 r hr]
  show f.1.1 ((p : GL n k) * w) = 0
  rw [parInd_law, hw', map_zero, smul_zero]

/- English proof (translation)
Use `⟨isSmooth_parInd e ρ, fun K hKo _ => ?_⟩` and prove the remaining obligations. Take `⟨R, hR⟩` from `exists_finset_KO_cover K hKo`. Set `L : fixed (parInd e ρ) K →ₗ[ℂ] (R → W)` to `{ toFun := fun f r => f.1.1.1 r map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Use `Module.Finite.of_injective L fun f g hfg => ?_` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`.

Establish `h` using `eq_zero_of_fixed e ρ K R hR (f - g).1 (f - g).2 fun r hr => by`. Use `congrFun hfg ⟨r, hr⟩` as an intermediate fact. Simplify using `only [L, LinearMap.coe_mk, AddHom.coe_mk] at this`. Use `show f.1.1.1 r - g.1.1.1 r = 0`. Rewrite using `[this, sub_self]`.

Conclude with `Subtype.ext h`.
-/
theorem isAdmissible_parInd (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W)
    [FiniteDimensional ℂ W] : IsAdmissible (parInd e ρ) := by
  refine ⟨isSmooth_parInd e ρ, fun K hKo _ => ?_⟩
  obtain ⟨R, hR⟩ := exists_finset_KO_cover K hKo
  let L : fixed (parInd e ρ) K →ₗ[ℂ] (R → W) :=
    { toFun := fun f r => f.1.1.1 r
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective L fun f g hfg => ?_
  rw [← sub_eq_zero]
  have h := eq_zero_of_fixed e ρ K R hR (f - g).1 (f - g).2 fun r hr => by
    have := congrFun hfg ⟨r, hr⟩
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk] at this
    show f.1.1.1 r - g.1.1.1 r = 0
    rw [this, sub_self]
  exact Subtype.ext h

end GlobalTheory.SmGL.ParIndAdm

namespace GlobalTheory.ThK.MidJac

/- English proof (translation)
Introduce `k _ _ _ _ x x' α β`. Conclude with `GlobalTheory.SmGL.ParIndAdm.isAdmissible_parInd _ _`.
-/
theorem isAdmissible_detInd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x x' : ℕ) (α β : kˣ →* ℂˣ), GlobalTheory.PRep.IsAdmissible (GlobalTheory.ThK.MidJac.detInd x x' α β) := by
  intro k _ _ _ _ x x' α β
  exact GlobalTheory.SmGL.ParIndAdm.isAdmissible_parInd _ _

end GlobalTheory.ThK.MidJac
