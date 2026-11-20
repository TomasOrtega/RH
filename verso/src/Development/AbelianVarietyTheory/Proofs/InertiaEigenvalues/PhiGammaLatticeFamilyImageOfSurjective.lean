import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam.Img

section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W]
  [IsScalarTower k⟦X⟧ k⸨X⸩ W]

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨y, hy, rfl⟩, rfl⟩`. Conclude with `mem_sh_iff_exists.2 ⟨f y, ⟨y, hy, rfl⟩, (f.map_smul _ y).symm⟩`. Introduce `hx`.

Take `⟨_, ⟨y, hy, rfl⟩, rfl⟩` from `mem_sh_iff_exists.1 hx`. Conclude with `⟨_, mem_sh_iff_exists.2 ⟨y, hy, rfl⟩, f.map_smul _ y⟩`.
-/
theorem map_sh (f : V →ₗ[k⸨X⸩] W) (a : ℤ) (N : Submodule k⟦X⟧ V) :
    (sh a N).map (f.restrictScalars k⟦X⟧) = sh a (N.map (f.restrictScalars k⟦X⟧)) := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact mem_sh_iff_exists.2 ⟨f y, ⟨y, hy, rfl⟩, (f.map_smul _ y).symm⟩
  · intro hx
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := mem_sh_iff_exists.1 hx
    exact ⟨_, mem_sh_iff_exists.2 ⟨y, hy, rfl⟩, f.map_smul _ y⟩

/- English proof (translation)
Use `⟨h.1.map _, ?_⟩` and prove the remaining obligations. Establish `: ((N.map (f.restrictScalars k⟦X⟧) : Submodule k⟦X⟧ W) : Set W) = f '' (N : Set V)` using `rfl`. Rewrite using `[this, ← Submodule.map_span, h.2, Submodule.map_top, LinearMap.range_eq_top.2 hf]`.
-/
theorem isLat_map (f : V →ₗ[k⸨X⸩] W) (hf : Function.Surjective f) {N : Submodule k⟦X⟧ V} (h : IsLat N) :
    IsLat (N.map (f.restrictScalars k⟦X⟧)) := by
  refine ⟨h.1.map _, ?_⟩
  have : ((N.map (f.restrictScalars k⟦X⟧) : Submodule k⟦X⟧ W) : Set W) = f '' (N : Set V) := rfl
  rw [this, ← Submodule.map_span, h.2, Submodule.map_top, LinearMap.range_eq_top.2 hf]

/- English proof (translation)
Rewrite using `[pull, pull, Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]`. Use `congr 1`. Conclude with `Set.image_congr fun x _ => h x`.
-/
theorem map_pull [Module k V] [Module k W] (f g : V →ₗ[k⸨X⸩] W) (φ : V →ₗ[k] V) (φ' : W →ₗ[k] W)
    (h : ∀ x, f (φ x) = φ' (g x)) (N : Submodule k⟦X⟧ V) :
    (pull φ N).map (f.restrictScalars k⟦X⟧) = pull φ' (N.map (g.restrictScalars k⟦X⟧)) := by
  rw [pull, pull, Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  exact Set.image_congr fun x _ => h x

end

/- English proof (translation)
Introduce `k _ l _ _ R n _ V _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ D D' f hf hφ hγ w w' N hN hAB hC N'`. Use `⟨fun i => isLat_map (f i) (hf i) (hN i), fun i => ?_, fun i => ?_⟩` and prove the remaining obligations. Simplify using `only [N']`. Rewrite using `[← map_pull (f i) (f (i - 1)) (D.φ i) (D'.φ i) (hφ i), ← map_sh, ← map_sh]`. Conclude with `⟨Submodule.map_mono (hAB i).1, Submodule.map_mono (hAB i).2⟩`.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Simplify using `only [N']`. Rewrite using `[← map_sh]`. Use `⟨_, hC i x hx, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f i _ = D'.γ i (f i x) - f i x`.

Rewrite using `[map_sub, hγ]`.
-/
theorem image_lattice : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [Module k W] [IsScalarTower k⟦X⟧ k⸨X⸩ W] [IsScalarTower k k⸨X⸩ W] [IsScalarTower k k⟦X⟧ W] [FiniteDimensional k⸨X⸩ W] (D : ModPG R n V) (D' : ModPG R n W) (f : ZMod n → V →ₗ[k⸨X⸩] W), (∀ i, Function.Surjective (f i)) → (∀ i x, f i (D.φ i x) = D'.φ i (f (i - 1) x)) → (∀ i x, f i (D.γ i x) = D'.γ i (f i x)) → ∀ (w w' : ZMod n → ℤ) (N : ZMod n → Submodule k⟦X⟧ V), (∀ i, IsLat (N i)) → CondAB D.φ w w' N → (∀ i, CondC (D.γ i) (N i)) → let N' := fun i => (N i).map ((f i).restrictScalars k⟦X⟧); (∀ i, IsLat (N' i)) ∧ CondAB D'.φ w w' N' ∧ ∀ i, CondC (D'.γ i) (N' i) := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ D D' f hf hφ hγ w w' N hN hAB hC N'
  refine ⟨fun i => isLat_map (f i) (hf i) (hN i), fun i => ?_, fun i => ?_⟩
  · simp only [N']
    rw [← map_pull (f i) (f (i - 1)) (D.φ i) (D'.φ i) (hφ i), ← map_sh, ← map_sh]
    exact ⟨Submodule.map_mono (hAB i).1, Submodule.map_mono (hAB i).2⟩
  · rintro _ ⟨x, hx, rfl⟩
    simp only [N']
    rw [← map_sh]
    refine ⟨_, hC i x hx, ?_⟩
    change f i _ = D'.γ i (f i x) - f i x
    rw [map_sub, hγ]

end GlobalTheory.PhiGam.Img
