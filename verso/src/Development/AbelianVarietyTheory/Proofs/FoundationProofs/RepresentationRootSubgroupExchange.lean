import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImportsMore
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.ComplexValueBound.main`. Consider the case `exact _root_.GlobalTheory.ComplexValueBound.main`. Consider the case `(apply _root_.GlobalTheory.ComplexValueBound.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.ComplexValueBound.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.ComplexValueBound.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.ComplexValueBound.main ..)`.
-/
theorem eq_zero_of_sum_joint_eigenvectors {ι κ M : Type} [AddCommGroup M] [Module ℂ M]
    (T : κ → M →ₗ[ℂ] M) (l : ι → κ → ℂ) (hl : ∀ i j, i ≠ j → ∃ k, l i k ≠ l j k)
    (s : Finset ι) : ∀ u : ι → M, (∀ i k, T k (u i) = l i k • u i) → ∑ i ∈ s, u i = 0 →
      ∀ i ∈ s, u i = 0 := by
  first
  | exact @_root_.GlobalTheory.ComplexValueBound.main
  | exact _root_.GlobalTheory.ComplexValueBound.main
  | (apply _root_.GlobalTheory.ComplexValueBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ComplexValueBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ComplexValueBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ComplexValueBound.main ..)

/- English proof (translation)
Introduce `G _ _ M _ _ _ ρ B X Y χ hXB hBX hc hsep n v hv hvi`. Establish `hmul : ∀ (g h : G) (m : M), ρ (g * h) m = ρ g (ρ h m)` using `fun g h m => by`. Rewrite using `[map_mul]`. Both sides reduce to the same expression. Set `S : M →ₗ[ℂ] M` to `∑ x : X, ρ (x : G)`.

Establish `hS : ∀ m, S m = ∑ x : X, ρ (x : G) m` using `fun m => by`. Simplify using `only [S, LinearMap.sum_apply]`. Establish `hinj : ∀ m : M, (∀ b ∈ B, ρ b m = χ b • m) → (∀ y ∈ Y, ρ y m = m) → S m = 0 → m = 0`. Introduce `m hb hy h0`. Rewrite `h0` using `[hS]`.

Use `eq_zero_of_sum_joint_eigenvectors (ι := X) (κ := Y) (fun y => ρ (y : G)) (fun x y => χ ((y : G)⁻¹ * (x : G)⁻¹ * y * x)) (fun x x' hne => by` as an intermediate fact. Take `⟨y, hyY, h⟩` from `hsep x x.2 x' x'.2 (fun h => hne (Subtype.ext h))`. Conclude with `⟨⟨y, hyY⟩, h⟩) Finset.univ (fun x => ρ (x : G) m)`. Use the proof step `(fun x y => by`. Establish `e : (y : G) * x = x * (y * ((y : G)⁻¹ * (x : G)⁻¹ * y * x))` using `by group`.

Use `show ρ (y : G) (ρ (x : G) m) = _`. Rewrite using `[← hmul, e, hmul, hmul, hb _ (hc x x.2 y y.2), map_smul, hy y y.2, map_smul]) h0`. Use `1 (Finset.mem_univ _)`. Simplify using `using this`. Use `⟨fun i => S (v i), ?_, fun i => ⟨fun b hb => ?_, fun x hx => ?_⟩⟩` and prove the remaining obligations.

Rewrite `hv`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Apply `hv g` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises. Introduce `b hb`.

Rewrite using `[map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, (hvi i).1 b hb, smul_comm]`. Introduce `y hy`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, (hvi i).2 y hy]`. Rewrite using `[map_sum, ← hg]`. Simplify using `only [map_smul]`. Use `choose f hf g hg hfg hχ using hBX b hb`.

Set `F : X → X` to `fun x => ⟨f x x.2, hf x x.2⟩`. Establish `hF : Function.Injective F`. Introduce `x1 x2 h`. Establish `h' : f x1 x1.2 = f x2 x2.2` using `congrArg Subtype.val h`. Establish `e1` using `hfg x1 x1.2`.

Establish `e2` using `hfg x2 x2.2`. Rewrite `e2` using `[← h']`. Establish `e : (x1 : G)⁻¹ * x2 = (g x1 x1.2)⁻¹ * g x2 x2.2`. Combine the equalities or inequalities in the displayed calculation. Use `hXB _ (X.mul_mem (X.inv_mem x1.2) x2.2) (e ▸ B.mul_mem (B.inv_mem (hg x1 x1.2)) (hg x2 x2.2))` as an intermediate fact.

Conclude with `Subtype.ext (inv_mul_eq_one.1 this)`. Establish `hB : Function.Bijective F` using `Finite.injective_iff_bijective.1 hF`. Use `show ρ b (S (v i)) = χ b • S (v i)`. Rewrite using `[hS, map_sum, Finset.smul_sum]`. Use `Fintype.sum_bijective F hB _ _ fun x => ?_` and prove the remaining obligations.

Rewrite using `[← hmul, hfg x x.2, hmul, (hvi i).1 _ (hg x x.2), hχ, map_smul]`. Use `show ρ x (S (v i)) = S (v i)`. Rewrite using `[hS, map_sum]`. Use `Fintype.sum_equiv (Equiv.mulLeft (⟨x, hx⟩ : X)) _ _ fun z => ?_` and prove the remaining obligations. Rewrite using `[← hmul]`.

Both sides reduce to the same expression.
-/
theorem root_exchange : ∀ (G : Type) [Group G] [Fintype G] (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M), ∀ (B X Y : Subgroup G) (χ : G → ℂ), (∀ x ∈ X, x ∈ B → x = 1) → (∀ b ∈ B, ∀ x ∈ X, ∃ x' ∈ X, ∃ b' ∈ B, b * x = x' * b' ∧ χ b' = χ b) → (∀ x ∈ X, ∀ y ∈ Y, y⁻¹ * x⁻¹ * y * x ∈ B) → (∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → ∃ y ∈ Y, χ (y⁻¹ * x⁻¹ * y * x) ≠ χ (y⁻¹ * x'⁻¹ * y * x')) → ∀ (n : ℕ) (v : Fin n → M), LinearIndependent ℂ v → (∀ i, (∀ b ∈ B, ρ b (v i) = χ b • v i) ∧ ∀ y ∈ Y, ρ y (v i) = v i) → ∃ w : Fin n → M, LinearIndependent ℂ w ∧ ∀ i, (∀ b ∈ B, ρ b (w i) = χ b • w i) ∧ ∀ x ∈ X, ρ x (w i) = w i := by
  intro G _ _ M _ _ _ ρ B X Y χ hXB hBX hc hsep n v hv hvi
  have hmul : ∀ (g h : G) (m : M), ρ (g * h) m = ρ g (ρ h m) := fun g h m => by
    rw [map_mul]; rfl
  let S : M →ₗ[ℂ] M := ∑ x : X, ρ (x : G)
  have hS : ∀ m, S m = ∑ x : X, ρ (x : G) m := fun m => by
    simp only [S, LinearMap.sum_apply]
  have hinj : ∀ m : M, (∀ b ∈ B, ρ b m = χ b • m) → (∀ y ∈ Y, ρ y m = m) → S m = 0 → m = 0 := by
    intro m hb hy h0
    rw [hS] at h0
    have := eq_zero_of_sum_joint_eigenvectors (ι := X) (κ := Y) (fun y => ρ (y : G))
      (fun x y => χ ((y : G)⁻¹ * (x : G)⁻¹ * y * x))
      (fun x x' hne => by
        obtain ⟨y, hyY, h⟩ := hsep x x.2 x' x'.2 (fun h => hne (Subtype.ext h))
        exact ⟨⟨y, hyY⟩, h⟩) Finset.univ (fun x => ρ (x : G) m)
      (fun x y => by
        have e : (y : G) * x = x * (y * ((y : G)⁻¹ * (x : G)⁻¹ * y * x)) := by group
        show ρ (y : G) (ρ (x : G) m) = _
        rw [← hmul, e, hmul, hmul, hb _ (hc x x.2 y y.2), map_smul, hy y y.2, map_smul]) h0
      1 (Finset.mem_univ _)
    simpa using this
  refine ⟨fun i => S (v i), ?_, fun i => ⟨fun b hb => ?_, fun x hx => ?_⟩⟩
  · rw [Fintype.linearIndependent_iff] at hv ⊢
    intro g hg
    apply hv g
    apply hinj
    · intro b hb
      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, (hvi i).1 b hb, smul_comm]
    · intro y hy
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, (hvi i).2 y hy]
    · rw [map_sum, ← hg]
      simp only [map_smul]
  · choose f hf g hg hfg hχ using hBX b hb
    let F : X → X := fun x => ⟨f x x.2, hf x x.2⟩
    have hF : Function.Injective F := by
      intro x1 x2 h
      have h' : f x1 x1.2 = f x2 x2.2 := congrArg Subtype.val h
      have e1 := hfg x1 x1.2
      have e2 := hfg x2 x2.2
      rw [← h'] at e2
      have e : (x1 : G)⁻¹ * x2 = (g x1 x1.2)⁻¹ * g x2 x2.2 := by
        calc (x1 : G)⁻¹ * x2 = (b * x1)⁻¹ * (b * x2) := by group
          _ = _ := by rw [e1, e2]; group
      have := hXB _ (X.mul_mem (X.inv_mem x1.2) x2.2)
        (e ▸ B.mul_mem (B.inv_mem (hg x1 x1.2)) (hg x2 x2.2))
      exact Subtype.ext (inv_mul_eq_one.1 this)
    have hB : Function.Bijective F := Finite.injective_iff_bijective.1 hF
    show ρ b (S (v i)) = χ b • S (v i)
    rw [hS, map_sum, Finset.smul_sum]
    refine Fintype.sum_bijective F hB _ _ fun x => ?_
    rw [← hmul, hfg x x.2, hmul, (hvi i).1 _ (hg x x.2), hχ, map_smul]
  · show ρ x (S (v i)) = S (v i)
    rw [hS, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨x, hx⟩ : X)) _ _ fun z => ?_
    rw [← hmul]; rfl

end GlobalTheory.BadShare
