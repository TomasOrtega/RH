import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLeviUnipotentProj
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothSmInd
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibFin

/- English proof (translation)
Establish `hcover : K ⊆ ⋃ g : K, (fun x => (g : G) * x) '' (S : Set G)`. Introduce `x hx`. Conclude with `Set.mem_iUnion.2 ⟨⟨x, hx⟩, 1, S.one_mem, mul_one x⟩`. Take `⟨T, hT⟩` from `hK.elim_finite_subcover (fun g : K => (fun x => (g : G) * x) '' (S : Set G)) (fun g => (Homeomorph.mulLeft (g : G)).isOpenMap _ hS) hcover`. Apply `(T.finite_toSet.image (fun g : K => F g)).subset` to reduce the goal to its premises.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨g, hg, hxg⟩` from `Set.mem_iUnion₂.1 (hT hx)`. Take `⟨s, hs, rfl⟩` from `hxg`. Conclude with `⟨g, hg, (hF g s hs).symm⟩`.
-/
theorem finite_image_of_rightInvariant {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (S : Subgroup G) (hS : IsOpen (S : Set G)) {K : Set G} (hK : IsCompact K) (F : G → X)
    (hF : ∀ g, ∀ s ∈ S, F (g * s) = F g) : (F '' K).Finite := by
  have hcover : K ⊆ ⋃ g : K, (fun x => (g : G) * x) '' (S : Set G) := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, 1, S.one_mem, mul_one x⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover (fun g : K => (fun x => (g : G) * x) '' (S : Set G))
    (fun g => (Homeomorph.mulLeft (g : G)).isOpenMap _ hS) hcover
  apply (T.finite_toSet.image (fun g : K => F g)).subset
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.1 (hT hx)
  obtain ⟨s, hs, rfl⟩ := hxg
  exact ⟨g, hg, (hF g s hs).symm⟩

/- English proof (translation)
Establish `hst : IsOpen {m : GlobalTheory.BZMir.Mir k (i + t) | GlobalTheory.BZMir.Leib.prodPG τ σ m f = f}` using `GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd (GlobalTheory.BZMir.Leib.HPG k i t) (GlobalTheory.CompanionTheory.BZPsiPG.hRep τ σ) f`. Set `H : Subgroup (GL (Fin (i + t)) k)` to `{ carrier := {g | ∀ κ, GlobalTheory.CompanionTheory.BZPsiPG.fibV f (κ * g) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f κ} mul_mem' := by`. Introduce `a b ha hb κ`. Establish `ha' : ∀ κ, GlobalTheory.CompanionTheory.BZPsiPG.fibV f (κ * a) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f κ` using `ha`. Establish `hb' : ∀ κ, GlobalTheory.CompanionTheory.BZPsiPG.fibV f (κ * b) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f κ` using `hb`.

Rewrite using `[← mul_assoc, hb', ha']`. Use the proof step `one_mem' := by`. Introduce `κ`. Rewrite using `[mul_one]`. Use the proof step `inv_mem' := by`.

Introduce `a ha κ`. Establish `ha' : ∀ κ, GlobalTheory.CompanionTheory.BZPsiPG.fibV f (κ * a) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f κ` using `ha`. Rewrite using `[← ha' (κ * a⁻¹), mul_assoc, inv_mul_cancel, mul_one] }`. Establish `hcont` using `(GlobalTheory.CompanionTheory.BZPsiPG.continuous_levi_uM_mirProj k (i + t)).1`. Establish `hO` using `hcont.isOpen_preimage _ hst`.

Establish `hone : (1 : GL (Fin (i + t)) k) ∈ GlobalTheory.BZMir.levi k (i + t) ⁻¹' {m : GlobalTheory.BZMir.Mir k (i + t) | GlobalTheory.BZMir.Leib.prodPG τ σ m f = f}` using `by show GlobalTheory.BZMir.Leib.prodPG τ σ (GlobalTheory.BZMir.levi k (i + t) 1) f = f`. Simplify using the standard rewrite rules. Establish `hsub : GlobalTheory.BZMir.levi k (i + t) ⁻¹' {m : GlobalTheory.BZMir.Mir k (i + t) | GlobalTheory.BZMir.Leib.prodPG τ σ m f = f} ⊆ (H : Set _)`. Introduce `g hg κ`. Establish `hg' : GlobalTheory.BZMir.Leib.prodPG τ σ (GlobalTheory.BZMir.levi k (i + t) g) f = f` using `hg`.

Use function extensionality and compare the values at `v`. Establish `h1` using `congrArg (fun φ => GlobalTheory.CompanionTheory.BZPsiPG.fibV φ κ v) hg'`. Simplify using `only [GlobalTheory.CompanionTheory.BZPsiPG.fibV, map_mul, ← mul_assoc] at h1 ⊢`. Conclude with `h1`. Establish `hHopen : IsOpen (H : Set (GL (Fin (i + t)) k))` using `Subgroup.isOpen_of_mem_nhds H (Filter.mem_of_superset (hO.mem_nhds hone) hsub)`.

Establish `hF : ∀ g : GL (Fin (i + t)) k, ∀ s ∈ H, GlobalTheory.CompanionTheory.BZPsiPG.fibV f (g * s) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f g` using `fun g s hs => hs g`. Conclude with `GlobalTheory.CompanionTheory.BZPsiPG.FibFin.finite_image_of_rightInvariant H hHopen GlobalTheory.SplitFlip.isCompact_KO _ hF`.
-/
theorem finite_fibV_image (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (f : cIndSpace (HPG k i t) (hRep τ σ)) :
    ((fun κ : GL (Fin (i + t)) k => fibV f κ) ''
      (GlobalTheory.SplitWeil.KO k (Fin (i + t)) : Set (GL (Fin (i + t)) k))).Finite := by
  have hst : IsOpen {m : GlobalTheory.BZMir.Mir k (i + t) | GlobalTheory.BZMir.Leib.prodPG τ σ m f = f} :=
    GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd (GlobalTheory.BZMir.Leib.HPG k i t)
      (GlobalTheory.CompanionTheory.BZPsiPG.hRep τ σ) f
  let H : Subgroup (GL (Fin (i + t)) k) :=
    { carrier := {g | ∀ κ, GlobalTheory.CompanionTheory.BZPsiPG.fibV f (κ * g) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f κ}
      mul_mem' := by
        intro a b ha hb κ
        have ha' : ∀ κ, GlobalTheory.CompanionTheory.BZPsiPG.fibV f (κ * a) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f κ := ha
        have hb' : ∀ κ, GlobalTheory.CompanionTheory.BZPsiPG.fibV f (κ * b) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f κ := hb
        rw [← mul_assoc, hb', ha']
      one_mem' := by
        intro κ
        rw [mul_one]
      inv_mem' := by
        intro a ha κ
        have ha' : ∀ κ, GlobalTheory.CompanionTheory.BZPsiPG.fibV f (κ * a) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f κ := ha
        rw [← ha' (κ * a⁻¹), mul_assoc, inv_mul_cancel, mul_one] }
  have hcont := (GlobalTheory.CompanionTheory.BZPsiPG.continuous_levi_uM_mirProj k (i + t)).1
  have hO := hcont.isOpen_preimage _ hst
  have hone : (1 : GL (Fin (i + t)) k) ∈ GlobalTheory.BZMir.levi k (i + t) ⁻¹'
      {m : GlobalTheory.BZMir.Mir k (i + t) | GlobalTheory.BZMir.Leib.prodPG τ σ m f = f} := by
    show GlobalTheory.BZMir.Leib.prodPG τ σ (GlobalTheory.BZMir.levi k (i + t) 1) f = f
    simp
  have hsub : GlobalTheory.BZMir.levi k (i + t) ⁻¹'
      {m : GlobalTheory.BZMir.Mir k (i + t) | GlobalTheory.BZMir.Leib.prodPG τ σ m f = f} ⊆ (H : Set _) := by
    intro g hg κ
    have hg' : GlobalTheory.BZMir.Leib.prodPG τ σ (GlobalTheory.BZMir.levi k (i + t) g) f = f := hg
    funext v
    have h1 := congrArg (fun φ => GlobalTheory.CompanionTheory.BZPsiPG.fibV φ κ v) hg'
    simp only [GlobalTheory.CompanionTheory.BZPsiPG.fibV, map_mul, ← mul_assoc] at h1 ⊢
    exact h1
  have hHopen : IsOpen (H : Set (GL (Fin (i + t)) k)) :=
    Subgroup.isOpen_of_mem_nhds H (Filter.mem_of_superset (hO.mem_nhds hone) hsub)
  have hF : ∀ g : GL (Fin (i + t)) k, ∀ s ∈ H,
      GlobalTheory.CompanionTheory.BZPsiPG.fibV f (g * s) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f g := fun g s hs => hs g
  exact GlobalTheory.CompanionTheory.BZPsiPG.FibFin.finite_image_of_rightInvariant H hHopen GlobalTheory.SplitFlip.isCompact_KO _ hF

end GlobalTheory.CompanionTheory.BZPsiPG.FibFin
