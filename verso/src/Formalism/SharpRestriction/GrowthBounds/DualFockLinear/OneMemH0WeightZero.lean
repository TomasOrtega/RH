import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.FilterOfSupported
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OneSidedLemma4

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.MainNotions.G.LatticeSystems (kp_lamAt_antitone H0_le_twisted_nabla)

structure Peel {n' m : ℕ} (A : Finset (Fin n')) (X XT sp : Fin n' → Fin (m + 1) → ℤ) : Prop where
  top : ∀ s ∈ A, XT s = X s ∧ sp s = 0
  off : ∀ s, s ∉ A → XT s = 0 ∧ sp s = X s

/- English proof (translation)
Unfold `lamAt`. Rewrite using `[h]`.
-/
theorem lamAt_congr {n' m : ℕ} {X Y : Fin n' → Fin (m + 1) → ℤ} {s : Fin n'} (h : X s = Y s) : lamAt X s = lamAt Y s := by
  unfold lamAt
  rw [h]

/- English proof (translation)
Unfold `lamAt`. Rewrite using `[h]`. Use `split_ifs`. Both sides reduce to the same expression. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules.
-/
theorem lamAt_zero {n' m : ℕ} {X : Fin n' → Fin (m + 1) → ℤ} {s : Fin n'} (h : X s = 0) : lamAt X s = 0 := by
  unfold lamAt
  rw [h]
  split_ifs
  · rfl
  · funext i
    simp

/- English proof (translation)
Use function extensionality and compare the values at `t`. Simplify using `[nuOf]`.
-/
theorem nuOf_zero (m : ℕ) : nuOf (0 : Fin (m + 1) → ℤ) = 0 := by
  funext t
  simp [nuOf]

/- English proof (translation)
Introduce `_ _ _` and use `le_rfl`.
-/
theorem anti_zero (m : ℕ) : Antitone (0 : Fin (m + 1) → ℤ) := fun _ _ _ => le_rfl

/- English proof (translation)
Unfold `H0`. Rewrite using `[if_pos (anti_zero m)]`. Simplify using `only [Submodule.mem_iInf]`. Introduce and unpack `g ⟨hg, -⟩`. Rewrite using `[nablaLTwMem O Kf m 0 g hg]`.

Use `⟨1, ?_, ?_⟩` and prove the remaining obligations. Establish `: (fun t : Fin (m + 1) => (((0 : Fin (m + 1) → ℤ) t) - (0 : Fin (m + 1) → ℤ) (Fin.last m)).toNat) = 0`. Use function extensionality and compare the values at `t`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `one_mem_dualWeyl`. Simplify using the standard rewrite rules.
-/
theorem one_mem_H0_weight_zero (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (Λ : Submodule O (Fin (m + 1) → Kf)) :
    (1 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) ∈ H0 O m 0 Λ := by
  unfold H0
  rw [if_pos (anti_zero m)]
  simp only [Submodule.mem_iInf]
  rintro g ⟨hg, -⟩
  rw [nablaLTwMem O Kf m 0 g hg]
  refine ⟨1, ?_, ?_⟩
  · have : (fun t : Fin (m + 1) => (((0 : Fin (m + 1) → ℤ) t) - (0 : Fin (m + 1) → ℤ) (Fin.last m)).toNat) = 0 := by
      funext t
      simp
    rw [this]
    exact one_mem_dualWeyl
  · simp

section

variable {Kf : Type} [Field Kf] {n' m : ℕ} {A : Finset (Fin n')} {X XT sp : Fin n' → Fin (m + 1) → ℤ}

/- English proof (translation)
Introduce `u hu`. Take `⟨y, hy, he⟩` from `slice_tensor (R := Kf) A (fun s => if Antitone (lamAt X s) then dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt X s)) else ⊥) (fun s => if Antitone (lamAt XT s) then dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt XT s)) else ⊥) (fun s => if Antitone (lamAt sp s) then dualWeyl Kf (m + 1) (m + …`. Rewrite using `[lamAt_zero (hP.top s hs).2, if_pos (anti_zero m), nuOf_zero]`. Conclude with `one_mem_dualWeyl⟩)`. Use the proof step `(fun s hs => ⟨by rw [lamAt_zero (hP.off s hs).1, if_pos (anti_zero m), nuOf_zero]; exact one_mem_dualWeyl, by`.

Rewrite using `[lamAt_congr (hP.off s hs).2]⟩)`. Use `γ 1 (fun Q _ => ⟨γ Q, by simp⟩) u hu`. Rewrite using `[he, one_smul]`. Conclude with `hy`.
-/
theorem slice_V (hP : Peel A X XT sp)
    (γ : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf →ₗ[Kf] Kf) :
    ∀ u ∈ Vsp Kf X, slice A γ u ∈ Vsp Kf XT := by
  intro u hu
  obtain ⟨y, hy, he⟩ := slice_tensor (R := Kf) A
    (fun s => if Antitone (lamAt X s) then dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt X s)) else ⊥)
    (fun s => if Antitone (lamAt XT s) then dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt XT s)) else ⊥)
    (fun s => if Antitone (lamAt sp s) then dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt sp s)) else ⊥)
    (fun s hs => ⟨by rw [lamAt_congr (hP.top s hs).1], by
      rw [lamAt_zero (hP.top s hs).2, if_pos (anti_zero m), nuOf_zero]; exact one_mem_dualWeyl⟩)
    (fun s hs => ⟨by rw [lamAt_zero (hP.off s hs).1, if_pos (anti_zero m), nuOf_zero]; exact one_mem_dualWeyl, by
      rw [lamAt_congr (hP.off s hs).2]⟩)
    γ 1 (fun Q _ => ⟨γ Q, by simp⟩) u hu
  rw [he, one_smul]
  exact hy

variable {O : Type} [CommRing O] [Algebra O Kf]

/- English proof (translation)
The claim follows from `slice_tensor (R := O) A _ _ _ (fun s hs => ⟨by rw [lamAt_congr (hP.top s hs).1], by rw [lamAt_zero (hP.top s hs).2]; exact one_mem_H0_weight_zero O Kf m _⟩) (fun s hs => ⟨by rw [lamAt_zero (hP.off s hs).1]; exact one_mem_H0_weight_zero O Kf m _, by rw [lamAt_congr (hP.off s hs).2 …`.
-/
theorem slice_Hten (hP : Peel A X XT sp) (Λ : Fin n' → Submodule O (Fin (m + 1) → Kf))
    (γ : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf →ₗ[Kf] Kf) (c : Kf)
    (hγ : ∀ Q ∈ Hten O sp Λ, ∃ a : O, γ Q = c * algebraMap O Kf a) :
    ∀ u ∈ Hten O X Λ, ∃ y ∈ Hten O XT Λ, slice A γ u = c • y :=
  slice_tensor (R := O) A _ _ _
    (fun s hs => ⟨by rw [lamAt_congr (hP.top s hs).1], by
      rw [lamAt_zero (hP.top s hs).2]; exact one_mem_H0_weight_zero O Kf m _⟩)
    (fun s hs => ⟨by rw [lamAt_zero (hP.off s hs).1]; exact one_mem_H0_weight_zero O Kf m _, by
      rw [lamAt_congr (hP.off s hs).2]⟩)
    γ c hγ

/- English proof (translation)
Introduce `Q hQ`. Use `choose g hg hΛg using hΛ`. Establish `h1 : Q ∈ tensorLat O Kf (fun s => nablaLTw O Kf m (lamAt X s) (g s))`. Use `Submodule.span_mono ?_ hQ` and prove the remaining obligations. Introduce and unpack `_ ⟨F, hF, rfl⟩`.

Use `⟨F, fun s => ?_, rfl⟩` and prove the remaining obligations. Establish `h0 : F s ∈ H0 O m (lamAt X s) (Λ s)` using `hF s`. Rewrite `h0` using `[hΛg s]`. Conclude with `H0_le_twisted_nabla m _ (kp_lamAt_antitone X hd s) (g s) (hg s) h0`. Establish `h2` using `tr_tens_le O Kf m (fun s => lamAt X s) g hg Q h1`.

Unfold `Vsp`. Establish `: (fun s => if Antitone (lamAt X s) then dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt X s)) else ⊥) = fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt X s))`. Use function extensionality and compare the values at `s`. Rewrite using `[if_pos (kp_lamAt_antitone X hd s)]`. Rewrite using `[this]`.

Conclude with `h2`.
-/
theorem Hten_le_V (hd : IsDominant X) (Λ : Fin n' → Submodule O (Fin (m + 1) → Kf))
    (hΛ : ∀ s, ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit g.det ∧ Λ s = colSpan O g) :
    ∀ Q ∈ Hten O X Λ, Q ∈ Vsp Kf X := by
  intro Q hQ
  choose g hg hΛg using hΛ
  have h1 : Q ∈ tensorLat O Kf (fun s => nablaLTw O Kf m (lamAt X s) (g s)) := by
    refine Submodule.span_mono ?_ hQ
    rintro _ ⟨F, hF, rfl⟩
    refine ⟨F, fun s => ?_, rfl⟩
    have h0 : F s ∈ H0 O m (lamAt X s) (Λ s) := hF s
    rw [hΛg s] at h0
    exact H0_le_twisted_nabla m _ (kp_lamAt_antitone X hd s) (g s) (hg s) h0
  have h2 := tr_tens_le O Kf m (fun s => lamAt X s) g hg Q h1
  unfold Vsp
  have : (fun s => if Antitone (lamAt X s) then dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt X s)) else ⊥) =
      fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt X s)) := by
    funext s
    rw [if_pos (kp_lamAt_antitone X hd s)]
  rw [this]
  exact h2

end

end Formalism.MainNotions.TestSideCounting
