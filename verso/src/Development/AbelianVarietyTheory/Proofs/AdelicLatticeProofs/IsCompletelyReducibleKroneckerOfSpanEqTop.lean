import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsometryMatrixRange
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsLogKronecker
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsConjHarmOfSpanStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SsTransfer
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

/- English proof (translation)
Establish `h : (Submodule.span ℂ (Set.range f)).FG` using `Submodule.FG.of_finite`. Take `⟨s, hs, hsp⟩` from `(Submodule.fg_span_iff_fg_span_finset_subset _).1 h`. Establish `hs' : (s : Set V) ⊆ f '' Set.univ` using `by simpa using hs`. Take `⟨T, -, hT⟩` from `Finset.subset_set_image_iff.1 hs'`. Use `⟨T, fun S hS => le_antisymm (Submodule.span_mono (Set.image_subset_range _ _)) ?_⟩` and prove the remaining obligations.

Rewrite using `[hsp, ← hT, Finset.coe_image]`. Conclude with `Submodule.span_mono (Set.image_mono hS)`.
-/
theorem exists_finset_span_image_eq {G V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : G → V) : ∃ T : Finset G, ∀ S : Set G, (T : Set G) ⊆ S →
      Submodule.span ℂ (f '' S) = Submodule.span ℂ (Set.range f) := by
  classical
  have h : (Submodule.span ℂ (Set.range f)).FG := Submodule.FG.of_finite
  obtain ⟨s, hs, hsp⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 h
  have hs' : (s : Set V) ⊆ f '' Set.univ := by simpa using hs
  obtain ⟨T, -, hT⟩ := Finset.subset_set_image_iff.1 hs'
  refine ⟨T, fun S hS => le_antisymm (Submodule.span_mono (Set.image_subset_range _ _)) ?_⟩
  rw [hsp, ← hT, Finset.coe_image]
  exact Submodule.span_mono (Set.image_mono hS)

/- English proof (translation)
Introduce `ι _ _ κ _ _ G _ ρ ρ' h h'`. Take `⟨T₁, h₁⟩` from `exists_finset_span_image_eq (ρ : G → Matrix ι ι ℂ)`. Take `⟨T₂, h₂⟩` from `exists_finset_span_image_eq (ρ' : G → Matrix κ κ ℂ)`. Take `⟨T₃, h₃⟩` from `exists_finset_span_image_eq (fun g => ρ g ⊗ₖ ρ' g)`. Use `set T : Finset G := T₁ ∪ T₂ ∪ T₃ with hT`.

Use `set S : Finset G := T ∪ T.image (fun g => g⁻¹) with hS`. Establish `hinv : ∀ g ∈ S, g⁻¹ ∈ S`. Introduce `g hg`. Rewrite `hg`, the goal using `[hS, Finset.mem_union]`. Break down `hg with hg | hg` into its components or cases.

Conclude with `Or.inr (Finset.mem_image_of_mem _ hg)`. Take `⟨a, ha, rfl⟩` from `Finset.mem_image.1 hg`. Conclude with `Or.inl (by simpa using ha)`. Set `τ : S ≃ S` to `{ toFun := fun s => ⟨s.1⁻¹, hinv _ s.2⟩ invFun := fun s => ⟨s.1⁻¹, hinv _ s.2⟩ left_inv := fun s => Subtype.ext (inv_inv _) right_inv := fun s => Subtype.ext (inv_inv _) }`. Establish `hτ : ∀ s : S, (τ s : G) = (s : G)⁻¹` using `fun _ => rfl`.

Establish `e₁` using `h₁ (S : Set G) (by intro x hx; simp [hS, hT, Finset.mem_coe.1 hx])`. Establish `e₂` using `h₂ (S : Set G) (by intro x hx; simp [hS, hT, Finset.mem_coe.1 hx])`. Establish `e₃` using `h₃ (S : Set G) (by intro x hx; simp [hS, hT, Finset.mem_coe.1 hx])`. Rewrite `e₁`, `e₂`, `e₃` using `[Set.image_eq_range]`. Establish `i₁ : ∀ s : S, ρ (τ s : G) * ρ (s : G) = 1` using `fun s => by`.

Rewrite using `[hτ, ← map_mul, inv_mul_cancel, map_one]`. Establish `i₂ : ∀ s : S, ρ' (τ s : G) * ρ' (s : G) = 1` using `fun s => by`. Rewrite using `[hτ, ← map_mul, inv_mul_cancel, map_one]`. Take `⟨P, hP, HP⟩` from `GlobalTheory.T.exists_conj_harm_of_span' ι S τ (fun s => ρ (s : G)) i₁ (e₁.trans h)`. Take `⟨Q, hQ, HQ⟩` from `GlobalTheory.T.exists_conj_harm_of_span' κ S τ (fun s => ρ' (s : G)) i₂ (e₂.trans h')`.

Establish `HK` using `harm_kronecker ι κ S _ _ HP HQ`. Establish `hPQ : IsUnit (P ⊗ₖ Q).det`. Rewrite using `[det_kronecker]`. Conclude with `(hP.pow _).mul (hQ.pow _)`. Establish `key : ∀ s : S, (P * ρ (s : G) * P⁻¹) ⊗ₖ (Q * ρ' (s : G) * Q⁻¹) = (P ⊗ₖ Q) * (ρ (s : G) ⊗ₖ ρ' (s : G)) * (P ⊗ₖ Q)⁻¹` using `fun s => by`.

Rewrite using `[inv_kronecker, mul_kronecker_mul, mul_kronecker_mul]`. Establish `conj : ∀ {n : Type} [Fintype n] [DecidableEq n] (A X Y : Matrix n n ℂ), IsUnit A.det → X * Y = 1 → (A * X * A⁻¹) * (A * Y * A⁻¹) = 1`. Introduce `n _ _ A X Y hA hXY`. Combine the equalities or inequalities in the displayed calculation. Establish `hss` using `ss_of_harm (ι × κ) S τ _ (fun s => by show ((P * ρ (τ s : G) * P⁻¹) ⊗ₖ (Q * ρ' (τ s : G) * Q⁻¹)) * ((P * ρ (s : G) * P⁻¹) ⊗ₖ (Q * ρ' (s : G) * Q⁻¹)) = 1`.

Rewrite using `[← mul_kronecker_mul, conj _ _ _ hP (i₁ s), conj _ _ _ hQ (i₂ s), one_kronecker_one]) HK`. Establish `hss' : SS (Set.range fun s : S => ρ (s : G) ⊗ₖ ρ' (s : G))`. Use `(ss_transfer (ι × κ) _ ∅).2 (P ⊗ₖ Q) hPQ ?_` and prove the remaining obligations. Rewrite using `[← Set.range_comp]`. Use `hss using 2` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `s`. Conclude with `(key s).symm`. Use `(ss_transfer (ι × κ) _ _).1 ?_ ?_ hss'` and prove the remaining obligations. Introduce and unpack `_ ⟨s, rfl⟩`. Conclude with `⟨s, rfl⟩`.

Introduce `x hx`. Establish `: x ∈ Submodule.span ℂ (Set.range fun g => ρ g ⊗ₖ ρ' g)` using `Submodule.subset_span hx`. Rewrite `this` using `[← e₃]`. Conclude with `this`.
-/
theorem ss_kronecker_of_span_top : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Type) [Group G] (ρ : G →* Matrix ι ι ℂ) (ρ' : G →* Matrix κ κ ℂ), Submodule.span ℂ (Set.range ρ) = ⊤ → Submodule.span ℂ (Set.range ρ') = ⊤ → SS (Set.range fun g => ρ g ⊗ₖ ρ' g) := by
  intro ι _ _ κ _ _ G _ ρ ρ' h h'
  classical
  obtain ⟨T₁, h₁⟩ := exists_finset_span_image_eq (ρ : G → Matrix ι ι ℂ)
  obtain ⟨T₂, h₂⟩ := exists_finset_span_image_eq (ρ' : G → Matrix κ κ ℂ)
  obtain ⟨T₃, h₃⟩ := exists_finset_span_image_eq (fun g => ρ g ⊗ₖ ρ' g)
  set T : Finset G := T₁ ∪ T₂ ∪ T₃ with hT
  set S : Finset G := T ∪ T.image (fun g => g⁻¹) with hS
  have hinv : ∀ g ∈ S, g⁻¹ ∈ S := by
    intro g hg
    rw [hS, Finset.mem_union] at hg ⊢
    rcases hg with hg | hg
    · exact Or.inr (Finset.mem_image_of_mem _ hg)
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hg
      exact Or.inl (by simpa using ha)
  let τ : S ≃ S :=
    { toFun := fun s => ⟨s.1⁻¹, hinv _ s.2⟩
      invFun := fun s => ⟨s.1⁻¹, hinv _ s.2⟩
      left_inv := fun s => Subtype.ext (inv_inv _)
      right_inv := fun s => Subtype.ext (inv_inv _) }
  have hτ : ∀ s : S, (τ s : G) = (s : G)⁻¹ := fun _ => rfl
  have e₁ := h₁ (S : Set G) (by intro x hx; simp [hS, hT, Finset.mem_coe.1 hx])
  have e₂ := h₂ (S : Set G) (by intro x hx; simp [hS, hT, Finset.mem_coe.1 hx])
  have e₃ := h₃ (S : Set G) (by intro x hx; simp [hS, hT, Finset.mem_coe.1 hx])
  rw [Set.image_eq_range] at e₁ e₂ e₃
  have i₁ : ∀ s : S, ρ (τ s : G) * ρ (s : G) = 1 := fun s => by
    rw [hτ, ← map_mul, inv_mul_cancel, map_one]
  have i₂ : ∀ s : S, ρ' (τ s : G) * ρ' (s : G) = 1 := fun s => by
    rw [hτ, ← map_mul, inv_mul_cancel, map_one]
  obtain ⟨P, hP, HP⟩ := GlobalTheory.T.exists_conj_harm_of_span' ι S τ (fun s => ρ (s : G)) i₁ (e₁.trans h)
  obtain ⟨Q, hQ, HQ⟩ := GlobalTheory.T.exists_conj_harm_of_span' κ S τ (fun s => ρ' (s : G)) i₂ (e₂.trans h')
  have HK := harm_kronecker ι κ S _ _ HP HQ
  have hPQ : IsUnit (P ⊗ₖ Q).det := by
    rw [det_kronecker]
    exact (hP.pow _).mul (hQ.pow _)
  have key : ∀ s : S, (P * ρ (s : G) * P⁻¹) ⊗ₖ (Q * ρ' (s : G) * Q⁻¹) =
      (P ⊗ₖ Q) * (ρ (s : G) ⊗ₖ ρ' (s : G)) * (P ⊗ₖ Q)⁻¹ := fun s => by
    rw [inv_kronecker, mul_kronecker_mul, mul_kronecker_mul]
  have conj : ∀ {n : Type} [Fintype n] [DecidableEq n] (A X Y : Matrix n n ℂ), IsUnit A.det → X * Y = 1 →
      (A * X * A⁻¹) * (A * Y * A⁻¹) = 1 := by
    intro n _ _ A X Y hA hXY
    calc (A * X * A⁻¹) * (A * Y * A⁻¹) = A * (X * (A⁻¹ * A) * Y) * A⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [nonsing_inv_mul _ hA, Matrix.mul_one, hXY, Matrix.mul_one, mul_nonsing_inv _ hA]
  have hss := ss_of_harm (ι × κ) S τ _ (fun s => by
    show ((P * ρ (τ s : G) * P⁻¹) ⊗ₖ (Q * ρ' (τ s : G) * Q⁻¹)) *
      ((P * ρ (s : G) * P⁻¹) ⊗ₖ (Q * ρ' (s : G) * Q⁻¹)) = 1
    rw [← mul_kronecker_mul, conj _ _ _ hP (i₁ s), conj _ _ _ hQ (i₂ s), one_kronecker_one]) HK
  have hss' : SS (Set.range fun s : S => ρ (s : G) ⊗ₖ ρ' (s : G)) := by
    refine (ss_transfer (ι × κ) _ ∅).2 (P ⊗ₖ Q) hPQ ?_
    rw [← Set.range_comp]
    convert hss using 2
    funext s
    exact (key s).symm
  refine (ss_transfer (ι × κ) _ _).1 ?_ ?_ hss'
  · rintro _ ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  · intro x hx
    have : x ∈ Submodule.span ℂ (Set.range fun g => ρ g ⊗ₖ ρ' g) := Submodule.subset_span hx
    rw [← e₃] at this
    exact this

end GlobalTheory.ClassFin
