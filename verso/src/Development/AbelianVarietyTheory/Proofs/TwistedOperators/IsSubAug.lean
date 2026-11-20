import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField

noncomputable section

open GlobalTheory.SplitWeil

namespace GlobalTheory.ThetaGLSub

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

variable (m : ℕ) in

def aug (χ : GL (Fin n) k →* ℂˣ) : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ) :=
  Submodule.span ℂ {z | ∃ h : GL (Fin n) k, ∃ Φ ∈ SB (Matrix (Fin n) (Fin m) k),
    z = om 1 (1 : GL (Fin m) k) h Φ - (χ h : ℂ) • Φ}

def IsSub {m : ℕ} (χ : GL (Fin n) k →* ℂˣ) (N : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)) : Prop :=
  aug m χ ≤ N ∧ N ≤ SB _ ∧ ∀ g : GL (Fin m) k, ∀ Φ ∈ N, om 1 g (1 : GL (Fin n) k) Φ ∈ N

variable {m : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [om, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem om_add (μ : kˣ →* ℂˣ) (g : GL (Fin m) k) (h : GL (Fin n) k) (Φ Ψ : Matrix (Fin n) (Fin m) k → ℂ) :
    om μ g h (Φ + Ψ) = om μ g h Φ + om μ g h Ψ := by
  funext x; simp only [om, Pi.add_apply]; ring

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [om, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem om_smul (μ : kˣ →* ℂˣ) (g : GL (Fin m) k) (h : GL (Fin n) k) (c : ℂ) (Φ : Matrix (Fin n) (Fin m) k → ℂ) :
    om μ g h (c • Φ) = c • om μ g h Φ := by
  funext x; simp only [om, Pi.smul_apply, smul_eq_mul]; ring

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [om, Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem om_sub (μ : kˣ →* ℂˣ) (g : GL (Fin m) k) (h : GL (Fin n) k) (Φ Ψ : Matrix (Fin n) (Fin m) k → ℂ) :
    om μ g h (Φ - Ψ) = om μ g h Φ - om μ g h Ψ := by
  funext x; simp only [om, Pi.sub_apply]; ring

/- English proof (translation)
Simplify using `only [← Model.om_mul, mul_one, one_mul]`.
-/
theorem om_comm (μ : kˣ →* ℂˣ) (g : GL (Fin m) k) (h : GL (Fin n) k) (Φ : Matrix (Fin n) (Fin m) k → ℂ) :
    om μ g 1 (om μ 1 h Φ) = om μ 1 h (om μ g 1 Φ) := by
  simp only [← Model.om_mul, mul_one, one_mul]

/- English proof (translation)
Rewrite using `[aug, Submodule.span_le]`. Introduce and unpack `_ ⟨h, Φ, hΦ, rfl⟩`. Conclude with `Submodule.sub_mem _ (Model.om_mem_SB 1 1 h hΦ) (Submodule.smul_mem _ _ hΦ)`.
-/
theorem aug_le_SB (χ : GL (Fin n) k →* ℂˣ) : aug m χ ≤ SB (Matrix (Fin n) (Fin m) k) := by
  rw [aug, Submodule.span_le]
  rintro _ ⟨h, Φ, hΦ, rfl⟩
  exact Submodule.sub_mem _ (Model.om_mem_SB 1 1 h hΦ) (Submodule.smul_mem _ _ hΦ)

/- English proof (translation)
Use `⟨le_rfl, aug_le_SB χ, fun g Φ hΦ => ?_⟩` and prove the remaining obligations. Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨h, Ψ, hΨ, rfl⟩` from `hz`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨h, om 1 g 1 Ψ, Model.om_mem_SB 1 g 1 hΨ, ?_⟩` and prove the remaining obligations. Rewrite using `[om_sub, om_smul, om_comm]`. Consider the case `zero`. Rewrite using `[show om (1 : kˣ →* ℂˣ) g (1 : GL (Fin n) k) 0 = 0 from funext fun x => by simp [om]]`. Conclude with `(aug m χ).zero_mem`.

Consider the case `add x y _ _ hx hy => rw [om_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [om_smul]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem isSub_aug (χ : GL (Fin n) k →* ℂˣ) : IsSub χ (aug m χ) := by
  refine ⟨le_rfl, aug_le_SB χ, fun g Φ hΦ => ?_⟩
  induction hΦ using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨h, Ψ, hΨ, rfl⟩ := hz
    apply Submodule.subset_span
    refine ⟨h, om 1 g 1 Ψ, Model.om_mem_SB 1 g 1 hΨ, ?_⟩
    rw [om_sub, om_smul, om_comm]
  | zero =>
    rw [show om (1 : kˣ →* ℂˣ) g (1 : GL (Fin n) k) 0 = 0 from funext fun x => by simp [om]]
    exact (aug m χ).zero_mem
  | add x y _ _ hx hy => rw [om_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [om_smul]; exact Submodule.smul_mem _ c hx

/- English proof (translation)
Use `⟨le_sup_of_le_left h.1, sup_le h.2.1 h'.2.1, fun g Φ hΦ => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 hΦ`. Rewrite using `[om_add]`. Conclude with `Submodule.add_mem_sup (h.2.2 g y hy) (h'.2.2 g z hz)`.
-/
theorem IsSub.sup {χ : GL (Fin n) k →* ℂˣ} {N N' : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)} (h : IsSub χ N)
    (h' : IsSub χ N') : IsSub χ (N ⊔ N') := by
  refine ⟨le_sup_of_le_left h.1, sup_le h.2.1 h'.2.1, fun g Φ hΦ => ?_⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hΦ
  rw [om_add]
  exact Submodule.add_mem_sup (h.2.2 g y hy) (h'.2.2 g z hz)

end GlobalTheory.ThetaGLSub
