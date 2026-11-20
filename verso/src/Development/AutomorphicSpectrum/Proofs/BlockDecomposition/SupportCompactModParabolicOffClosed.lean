import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.SuppOff

section Abstract

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Establish `hopen : IsOpen {g : G | GlobalTheory.PRep.ind H σ g f.1 = f.1}` using `f.2`. Establish `htrans : ∀ g x : G, GlobalTheory.PRep.ind H σ g f.1 = f.1 → f.1.1 (x * g) = f.1.1 x`. Introduce `g x hg`. Conclude with `congrArg (fun φ : GlobalTheory.PRep.indSpace H σ => (φ : G → W) x) hg`. Rewrite using `[← isOpen_compl_iff, isOpen_iff_mem_nhds]`.

Introduce `c hc`. Establish `hc0 : f.1.1 c = 0` using `by simpa using hc`. Establish `h1 : c⁻¹ * c ∈ {g : G | GlobalTheory.PRep.ind H σ g f.1 = f.1}` using `by show GlobalTheory.PRep.ind H σ (c⁻¹ * c) f.1 = f.1`. Rewrite using `[inv_mul_cancel, map_one]`. Both sides reduce to the same expression.

Use `Filter.mem_of_superset ((continuous_mul_left c⁻¹).continuousAt.preimage_mem_nhds (hopen.mem_nhds h1)) ?_` and prove the remaining obligations. Introduce `x hx`. Establish `hx' : GlobalTheory.PRep.ind H σ (c⁻¹ * x) f.1 = f.1` using `hx`. Establish `hfx : f.1.1 x = 0`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `using hfx`.
-/
theorem isClosed_support (H : Subgroup G) (σ : Representation ℂ H W) (f : smoothPart (ind H σ)) :
    IsClosed {c : G | f.1.1 c ≠ 0} := by
  have hopen : IsOpen {g : G | GlobalTheory.PRep.ind H σ g f.1 = f.1} := f.2
  have htrans : ∀ g x : G, GlobalTheory.PRep.ind H σ g f.1 = f.1 → f.1.1 (x * g) = f.1.1 x := by
    intro g x hg
    exact congrArg (fun φ : GlobalTheory.PRep.indSpace H σ => (φ : G → W) x) hg
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro c hc
  have hc0 : f.1.1 c = 0 := by simpa using hc
  have h1 : c⁻¹ * c ∈ {g : G | GlobalTheory.PRep.ind H σ g f.1 = f.1} := by
    show GlobalTheory.PRep.ind H σ (c⁻¹ * c) f.1 = f.1
    rw [inv_mul_cancel, map_one]
    rfl
  refine Filter.mem_of_superset
    ((continuous_mul_left c⁻¹).continuousAt.preimage_mem_nhds (hopen.mem_nhds h1)) ?_
  intro x hx
  have hx' : GlobalTheory.PRep.ind H σ (c⁻¹ * x) f.1 = f.1 := hx
  have hfx : f.1.1 x = 0 := by
    calc f.1.1 x = f.1.1 (c * (c⁻¹ * x)) := by rw [mul_inv_cancel_left]
      _ = f.1.1 c := htrans _ _ hx'
      _ = 0 := hc0
  simpa using hfx

/- English proof (translation)
Establish `key : ∀ F : GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind H σ), (∃ C : Set G, IsCompact C ∧ ∀ g, F.1.1 g ≠ 0 → ∃ h ∈ H, ∃ c ∈ C, g = h * c) → (∀ x ∈ T, F.1.1 x = 0) → ∃ C : Set G, IsCompact C ∧ (∀ c ∈ C, c ∉ T) ∧ ∀ g, F.1.1 g ≠ 0 → ∃ h ∈ H, ∃ c ∈ C, g = h * c`. Introduce and unpack `F ⟨C, hC, hsupp⟩ hF`. Establish `hequiv : ∀ (h : H) (g : G), F.1.1 (h * g) = σ h (F.1.1 g)` using `F.1.2`. Use `⟨C ∩ {c | F.1.1 c ≠ 0}, hC.inter_right (GlobalTheory.CompanionTheory.BZPhiPG.SuppOff.isClosed_support H σ F), ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `c ⟨-, hc⟩ hcT`.

Conclude with `hc (hF c hcT)`. Introduce `g hg`. Take `⟨h, hH, c, hcC, rfl⟩` from `hsupp g hg`. Use `⟨h, hH, c, ⟨hcC, ?_⟩, rfl⟩` and prove the remaining obligations. Introduce `hc0`.

Apply `hg` to reduce the goal to its premises. Establish `e : F.1.1 (h * c) = σ ⟨h, hH⟩ (F.1.1 c)` using `hequiv ⟨h, hH⟩ c`. Rewrite using `[e]`. Establish `hc0' : F.1.1 c = 0` using `by simpa using hc0`. Rewrite using `[hc0', map_zero]`.

Conclude with `key _ f.2 hf`.
-/
theorem exists_compact_off (H : Subgroup G) (σ : Representation ℂ H W) (f : cIndSpace H σ) (T : Set G)
    (hf : ∀ x ∈ T, (f : smoothPart (ind H σ)).1.1 x = 0) :
    ∃ C : Set G, IsCompact C ∧ (∀ c ∈ C, c ∉ T) ∧
      ∀ g, (f : smoothPart (ind H σ)).1.1 g ≠ 0 → ∃ h ∈ H, ∃ c ∈ C, g = h * c := by
  have key : ∀ F : GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind H σ),
      (∃ C : Set G, IsCompact C ∧ ∀ g, F.1.1 g ≠ 0 → ∃ h ∈ H, ∃ c ∈ C, g = h * c) →
      (∀ x ∈ T, F.1.1 x = 0) →
      ∃ C : Set G, IsCompact C ∧ (∀ c ∈ C, c ∉ T) ∧
        ∀ g, F.1.1 g ≠ 0 → ∃ h ∈ H, ∃ c ∈ C, g = h * c := by
    rintro F ⟨C, hC, hsupp⟩ hF
    have hequiv : ∀ (h : H) (g : G), F.1.1 (h * g) = σ h (F.1.1 g) := F.1.2
    refine ⟨C ∩ {c | F.1.1 c ≠ 0}, hC.inter_right (GlobalTheory.CompanionTheory.BZPhiPG.SuppOff.isClosed_support H σ F), ?_, ?_⟩
    · rintro c ⟨-, hc⟩ hcT
      exact hc (hF c hcT)
    · intro g hg
      obtain ⟨h, hH, c, hcC, rfl⟩ := hsupp g hg
      refine ⟨h, hH, c, ⟨hcC, ?_⟩, rfl⟩
      intro hc0
      apply hg
      have e : F.1.1 (h * c) = σ ⟨h, hH⟩ (F.1.1 c) := hequiv ⟨h, hH⟩ c
      rw [e]
      have hc0' : F.1.1 c = 0 := by simpa using hc0
      rw [hc0', map_zero]
  exact key _ f.2 hf

end Abstract

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.BZPhiPG.SuppOff.exists_compact_off (GlobalTheory.BZMir.Leib.HPG k (i + 1) (t + 1)) (GlobalTheory.CompanionTheory.BZPhiPG.sigX τ σ) f _ hf`.
-/
theorem exists_compact_off_Cl (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (hf : ∀ x ∈ Cl k i t, evX f x = 0) :
    ∃ C : Set (Mir k ((i + 1) + t + 1)), IsCompact C ∧ (∀ c ∈ C, c ∉ Cl k i t) ∧
      ∀ g, evX f g ≠ 0 → ∃ h ∈ HPG k (i + 1) (t + 1), ∃ c ∈ C, g = h * c :=
  GlobalTheory.CompanionTheory.BZPhiPG.SuppOff.exists_compact_off (GlobalTheory.BZMir.Leib.HPG k (i + 1) (t + 1))
    (GlobalTheory.CompanionTheory.BZPhiPG.sigX τ σ) f _ hf

end GlobalTheory.CompanionTheory.BZPhiPG.SuppOff
