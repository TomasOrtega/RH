import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology

namespace GlobalTheory.CompanionTheory.ThetaGLLen

section Smooth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable (a c d : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

/- English proof (translation)
Establish `hA : ∀ s : ℂ, IsSmoothChar (absPow k s)` using `fun s => isSmoothChar_of_isUnram (isUnram_absPow k s)`. Use `IsSmoothChar.mul (IsSmoothChar.mul ?_ ?_) ?_` and prove the remaining obligations. Conclude with `(IsSmoothChar.detChar (hμ.inv.mul (hA _))).comp _ continuous_fst`. Conclude with `(IsSmoothChar.detChar ((hμ.mul (hA _)).mul (hA _))).comp _ (continuous_fst.comp continuous_snd)`. Conclude with `(IsSmoothChar.detChar ((hμ.mul (hA _)).mul (hA _))).comp _ (continuous_snd.comp continuous_snd)`.
-/
theorem isSmoothChar_fibChar {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ) :
    IsSmoothChar (fibChar (k := k) a c d μ) := by
  have hA : ∀ s : ℂ, IsSmoothChar (absPow k s) := fun s => isSmoothChar_of_isUnram (isUnram_absPow k s)
  refine IsSmoothChar.mul (IsSmoothChar.mul ?_ ?_) ?_
  · exact (IsSmoothChar.detChar (hμ.inv.mul (hA _))).comp _ continuous_fst
  · exact (IsSmoothChar.detChar ((hμ.mul (hA _)).mul (hA _))).comp _ (continuous_fst.comp continuous_snd)
  · exact (IsSmoothChar.detChar ((hμ.mul (hA _)).mul (hA _))).comp _ (continuous_snd.comp continuous_snd)

/- English proof (translation)
Apply `GlobalTheory.SmGL.isSmooth_of_nhds` to reduce the goal to its premises. Introduce `φ`. Take `⟨hlc, hcs⟩` from `φ.2`. Establish `hopen : IsOpen {z : Γ × X | (φ : X → ℂ) (r z.2 z.1) = (φ : X → ℂ) z.2}`. Establish `h1lc : IsLocallyConstant (fun z : Γ × X => (φ : X → ℂ) (r z.2 z.1))` using `hlc.comp_continuous (hj.comp continuous_swap)`.

Establish `h2lc : IsLocallyConstant (fun z : Γ × X => (φ : X → ℂ) z.2)` using `hlc.comp_continuous continuous_snd`. Use `(h1lc.comp₂ h2lc (fun u v => u - v)).isOpen_fiber 0` as an intermediate fact. Simplify `this` using `only [sub_eq_zero]`. Establish `hev : ∀ᶠ γ in 𝓝 (1 : Γ), ∀ x ∈ tsupport (φ : X → ℂ), (φ : X → ℂ) (r x γ) = (φ : X → ℂ) x`. Use `IsCompact.eventually_forall_of_forall_eventually hcs ?_` and prove the remaining obligations.

Introduce `x _`. Conclude with `hopen.mem_nhds (by simp only [Set.mem_ofPred_eq, h1])`. Establish `hev' : ∀ᶠ γ in 𝓝 (1 : Γ), ∀ x ∈ tsupport (φ : X → ℂ), (φ : X → ℂ) (r x γ⁻¹) = (φ : X → ℂ) x`. Establish `ht : Filter.Tendsto (fun γ : Γ => γ⁻¹) (𝓝 1) (𝓝 1)`. Simplify using `using (continuous_inv.tendsto (1 : Γ))`.

Conclude with `ht.eventually hev`. Use `filter_upwards [hev, hev'] with γ hγ hγ'`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Use `show (φ : X → ℂ) (r x γ) = (φ : X → ℂ) x`.

Distinguish the cases in `hx : x ∈ tsupport (φ : X → ℂ)`. Conclude with `hγ x hx`. Distinguish the cases in `hy : r x γ ∈ tsupport (φ : X → ℂ)`. Establish `e` using `hγ' _ hy`. Rewrite `e` using `[← hm, mul_inv_cancel, h1]`.

Conclude with `e.symm`. Rewrite using `[image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hy]`.
-/
private theorem isSmooth_sbRep_of_continuous_action {Γ X : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [TopologicalSpace X] (r : X → Γ → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ (x : X) (g h : Γ), r x (g * h) = r (r x g) h)
    (hc : ∀ g, Continuous fun x => r x g) (hj : Continuous fun p : X × Γ => r p.1 p.2) :
    IsSmooth (GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.sbRep r h1 hm hc) := by
  apply GlobalTheory.SmGL.isSmooth_of_nhds
  intro φ
  obtain ⟨hlc, hcs⟩ := φ.2
  have hopen : IsOpen {z : Γ × X | (φ : X → ℂ) (r z.2 z.1) = (φ : X → ℂ) z.2} := by
    have h1lc : IsLocallyConstant (fun z : Γ × X => (φ : X → ℂ) (r z.2 z.1)) :=
      hlc.comp_continuous (hj.comp continuous_swap)
    have h2lc : IsLocallyConstant (fun z : Γ × X => (φ : X → ℂ) z.2) :=
      hlc.comp_continuous continuous_snd
    have := (h1lc.comp₂ h2lc (fun u v => u - v)).isOpen_fiber 0
    simpa only [sub_eq_zero] using this
  have hev : ∀ᶠ γ in 𝓝 (1 : Γ), ∀ x ∈ tsupport (φ : X → ℂ), (φ : X → ℂ) (r x γ) = (φ : X → ℂ) x := by
    refine IsCompact.eventually_forall_of_forall_eventually hcs ?_
    intro x _
    exact hopen.mem_nhds (by simp only [Set.mem_ofPred_eq, h1])
  have hev' : ∀ᶠ γ in 𝓝 (1 : Γ), ∀ x ∈ tsupport (φ : X → ℂ),
      (φ : X → ℂ) (r x γ⁻¹) = (φ : X → ℂ) x := by
    have ht : Filter.Tendsto (fun γ : Γ => γ⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv.tendsto (1 : Γ))
    exact ht.eventually hev
  filter_upwards [hev, hev'] with γ hγ hγ'
  apply Subtype.ext
  funext x
  show (φ : X → ℂ) (r x γ) = (φ : X → ℂ) x
  by_cases hx : x ∈ tsupport (φ : X → ℂ)
  · exact hγ x hx
  · by_cases hy : r x γ ∈ tsupport (φ : X → ℂ)
    · have e := hγ' _ hy
      rw [← hm, mul_inv_cancel, h1] at e
      exact e.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hy]

/- English proof (translation)
Use `show IsSmooth (GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.sbRep _ _ _ _)`. Apply `isSmooth_sbRep_of_continuous_action` to reduce the goal to its premises. Apply `Continuous.subtype_mk` to reduce the goal to its premises. Establish `hinv : Continuous fun p : GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a c {κ} × (GL a k × GL c k) => (((p.2.2)⁻¹ : GL c k) : Matrix c c k)` using `Units.continuous_val.comp (continuous_inv.comp (continuous_snd.comp continuous_snd))`. Establish `hx : Continuous fun p : GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a c {κ} × (GL a k × GL c k) => (p.1 : Matrix c a k)` using `continuous_subtype_val.comp continuous_fst`.

Establish `hg : Continuous fun p : GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a c {κ} × (GL a k × GL c k) => ((p.2.1 : GL a k) : Matrix a a k)` using `Units.continuous_val.comp (continuous_fst.comp continuous_snd)`. Conclude with `(hinv.matrix_mul hx).matrix_mul hg`.
-/
private theorem isSmooth_fibBase (κ : ℕ) : IsSmooth (fibBase (k := k) a c κ) := by
  show IsSmooth (GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.sbRep _ _ _ _)
  apply isSmooth_sbRep_of_continuous_action
  apply Continuous.subtype_mk
  have hinv : Continuous fun p : GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a c {κ} × (GL a k × GL c k) =>
      (((p.2.2)⁻¹ : GL c k) : Matrix c c k) :=
    Units.continuous_val.comp (continuous_inv.comp (continuous_snd.comp continuous_snd))
  have hx : Continuous fun p : GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a c {κ} × (GL a k × GL c k) =>
      (p.1 : Matrix c a k) :=
    continuous_subtype_val.comp continuous_fst
  have hg : Continuous fun p : GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a c {κ} × (GL a k × GL c k) =>
      ((p.2.1 : GL a k) : Matrix a a k) :=
    Units.continuous_val.comp (continuous_fst.comp continuous_snd)
  exact (hinv.matrix_mul hx).matrix_mul hg

/- English proof (translation)
Establish `hB` using `isSmooth_fibBase (k := k) a c κ`. Establish `hρ` using `isSmooth_comp hB ((MonoidHom.id (GL a k)).prodMap (MonoidHom.fst (GL c k) (GL d k))) (continuous_id.prodMap continuous_fst)`. Establish `ht` using `isSmooth_twist hρ (isSmoothChar_fibChar a c d hμ)`. Conclude with `isSmooth_comp ht (MonoidHom.inr (GL a k) (GL c k × GL d k)) (continuous_const.prodMk continuous_id)`.
-/
theorem isSmooth_fibRep_levi (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) (κ : ℕ) :
    IsSmooth ((fibRep (k := k) a c d μ κ).comp (MonoidHom.inr (GL a k) (GL c k × GL d k))) := by
  have hB := isSmooth_fibBase (k := k) a c κ
  have hρ := isSmooth_comp hB ((MonoidHom.id (GL a k)).prodMap (MonoidHom.fst (GL c k) (GL d k)))
    (continuous_id.prodMap continuous_fst)
  have ht := isSmooth_twist hρ (isSmoothChar_fibChar a c d hμ)
  exact isSmooth_comp ht (MonoidHom.inr (GL a k) (GL c k × GL d k)) (continuous_const.prodMk continuous_id)

end Smooth

end GlobalTheory.CompanionTheory.ThetaGLLen

namespace GlobalTheory.CompanionTheory.ThetaGLLen

/- English proof (translation)
Introduce `k _ _ _ _ a c d _ _ _ _ _ _ μ hμ κ`. Conclude with `isSmooth_fibRep_levi a c d μ hμ κ`.
-/
theorem isSmooth_fibRep_inr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a c d : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] (μ : kˣ →* ℂˣ), IsSmoothChar μ → ∀ κ : ℕ, IsSmooth ((fibRep (k := k) a c d μ κ).comp (MonoidHom.inr (GL a k) (GL c k × GL d k))) := by
  intro k _ _ _ _ a c d _ _ _ _ _ _ μ hμ κ
  exact isSmooth_fibRep_levi a c d μ hμ κ

end GlobalTheory.CompanionTheory.ThetaGLLen
