import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothDetPair

open scoped TensorProduct
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL

namespace GlobalTheory.FiltStepCut

/- English proof (translation)
Proceed by induction on `j' using Fin.induction with`. Consider the case `zero`. Introduce `h _`. Take `rfl : j = 0` from `le_antisymm h (Fin.zero_le _)`. Conclude with `⟨[], by simp, by simp⟩`.

Consider the case `succ i ih`. Introduce `h ht`. Break down `h.eq_or_lt with rfl | h` into its components or cases. Conclude with `⟨[], by simp, by simp⟩`. Establish `h' : j ≤ i.castSucc` using `Fin.le_castSucc_iff.2 h`.

Establish `hi : i ≠ t₀` using `ht i h' le_rfl`. Take `⟨l, hl, hm⟩` from `ih h' fun t a b => ht t a (b.trans (Fin.castSucc_lt_succ).le)`. Use `⟨l ++ [i], ?_, fun w hw => ?_⟩` and prove the remaining obligations. Introduce `t htl`. Break down `List.mem_append.1 htl with a | a` into its components or cases.

Conclude with `hl t a`. Rewrite using `[List.mem_singleton.1 a]`. Conclude with `hi`. Rewrite using `[List.map_append, List.prod_append]`. Simplify using `using hm _ (hQ i hi w hw)`.
-/
theorem exists_prod_maps {J : Type} [AddCommGroup J] [Module ℂ J] {N : ℕ}
    (S : Fin (N + 1) → Submodule ℂ J) (t₀ : Fin N) (Q : Fin N → Module.End ℂ J)
    (hQ : ∀ t, t ≠ t₀ → ∀ w ∈ S t.succ, Q t w ∈ S t.castSucc) (j j' : Fin (N + 1)) :
    j ≤ j' → (∀ t : Fin N, j ≤ t.castSucc → t.succ ≤ j' → t ≠ t₀) →
      ∃ l : List (Fin N), (∀ t ∈ l, t ≠ t₀) ∧ ∀ w ∈ S j', (l.map Q).prod w ∈ S j := by
  induction j' using Fin.induction with
  | zero =>
    intro h _
    obtain rfl : j = 0 := le_antisymm h (Fin.zero_le _)
    exact ⟨[], by simp, by simp⟩
  | succ i ih =>
    intro h ht
    rcases h.eq_or_lt with rfl | h
    · exact ⟨[], by simp, by simp⟩
    · have h' : j ≤ i.castSucc := Fin.le_castSucc_iff.2 h
      have hi : i ≠ t₀ := ht i h' le_rfl
      obtain ⟨l, hl, hm⟩ := ih h' fun t a b => ht t a (b.trans (Fin.castSucc_lt_succ).le)
      refine ⟨l ++ [i], ?_, fun w hw => ?_⟩
      · intro t htl
        rcases List.mem_append.1 htl with a | a
        · exact hl t a
        · rw [List.mem_singleton.1 a]; exact hi
      · rw [List.map_append, List.prod_append]
        simpa using hm _ (hQ i hi w hw)

/- English proof (translation)
Introduce `L J _ _ _ ρ N S _ h0 hN t₀ z c hz hc`. Use `set Q : Fin N → Module.End ℂ J := fun t => ρ (z t) - c t • (1 : Module.End ℂ J) with hQdef`. Establish `hQ : ∀ t, t ≠ t₀ → ∀ w ∈ (S t.succ).toSubmodule, Q t w ∈ (S t.castSucc).toSubmodule`. Introduce `t ht w hw`. Establish `h1` using `hc t ht (Submodule.Quotient.mk ⟨w, hw⟩)`.

Rewrite `h1` using `[← Submodule.Quotient.mk_smul]`. Conclude with `(Submodule.Quotient.eq ((S t.castSucc).toSubmodule.comap (S t.succ).toSubmodule.subtype) (x := (S t.succ).toRepresentation (z t) ⟨w, hw⟩) (y := c t • (⟨w, hw⟩ : (S t.succ).toSubmodule))).1 h1`. Establish `hcomm : ∀ t y, Commute (ρ y) (Q t)`. Introduce `t y`. Use `Commute.sub_right ?_ ((Commute.one_right _).smul_right _)` and prove the remaining obligations.

Use `show ρ y * ρ (z t) = ρ (z t) * ρ y`. Rewrite using `[← map_mul, ← map_mul, hz]`. Take `⟨l₁, hl₁, hm₁⟩` from `exists_prod_maps (fun j => (S j).toSubmodule) t₀ Q hQ t₀.succ (Fin.last N) (Fin.le_last _) (by`. Introduce and unpack `t a - rfl`. Conclude with `absurd a (not_le.2 Fin.castSucc_lt_succ))`.

Take `⟨l₂, hl₂, hm₂⟩` from `exists_prod_maps (fun j => (S j).toSubmodule) t₀ Q hQ 0 t₀.castSucc (Fin.zero_le _) (by`. Introduce and unpack `t - a rfl`. Conclude with `absurd a (not_le.2 Fin.castSucc_lt_succ))`. Establish `hP : ∀ y, Commute (ρ y) (l₂.map Q).prod` using `fun y => Commute.list_prod_right _ _ fun x hx => by`. Take `⟨t, -, rfl⟩` from `List.mem_map.1 hx`.

Conclude with `hcomm t y`. Establish `hker : (S t₀.castSucc).toSubmodule.comap (S t₀.succ).toSubmodule.subtype ≤ LinearMap.ker ((l₂.map Q).prod ∘ₗ (S t₀.succ).toSubmodule.subtype)`. Introduce `x hx`. Use `hm₂ _ hx` as an intermediate fact. Simplify using `only [h0] at this`.

Conclude with `this`. Use `⟨l₂ ++ l₁, ⟨Submodule.liftQ _ _ hker, fun g => Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)⟩, ?_, fun w => ?_⟩` and prove the remaining obligations. Conclude with `(LinearMap.congr_fun (hP g).eq (x : J)).symm`. Introduce `t htl`. Break down `List.mem_append.1 htl with a | a` into its components or cases.

Conclude with `hl₂ t a`. Conclude with `hl₁ t a`. Establish `hw : w ∈ (S (Fin.last N)).toSubmodule` using `by rw [hN]; trivial`. Use `⟨Submodule.Quotient.mk ⟨_, hm₁ w hw⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[List.map_append, List.prod_append]`.

Both sides reduce to the same expression.
-/
theorem exists_prod_mem_range : ∀ (L J : Type) [Group L] [AddCommGroup J] [Module ℂ J]
    (ρ : Representation ℂ L J) (N : ℕ)
    (S : Fin (N + 1) → Subrepresentation ρ), Monotone S → S 0 = ⊥ → S (Fin.last N) = ⊤ →
    ∀ (t₀ : Fin N) (z : Fin N → L) (c : Fin N → ℂ), (∀ t y, y * z t = z t * y) →
      (∀ t, t ≠ t₀ → ∀ y, subQuot (S t.succ) (S t.castSucc) (z t) y = c t • y) →
      ∃ (l : List (Fin N))
        (A : Representation.IntertwiningMap (subQuot (S t₀.succ) (S t₀.castSucc)) ρ),
        (∀ t ∈ l, t ≠ t₀) ∧ ∀ w, (l.map fun t => ρ (z t) - c t • (1 : Module.End ℂ J)).prod w ∈
          LinearMap.range A.toLinearMap := by
  intro L J _ _ _ ρ N S _ h0 hN t₀ z c hz hc
  set Q : Fin N → Module.End ℂ J := fun t => ρ (z t) - c t • (1 : Module.End ℂ J) with hQdef
  have hQ : ∀ t, t ≠ t₀ → ∀ w ∈ (S t.succ).toSubmodule, Q t w ∈ (S t.castSucc).toSubmodule := by
    intro t ht w hw
    have h1 := hc t ht (Submodule.Quotient.mk ⟨w, hw⟩)
    rw [← Submodule.Quotient.mk_smul] at h1
    exact (Submodule.Quotient.eq ((S t.castSucc).toSubmodule.comap (S t.succ).toSubmodule.subtype)
      (x := (S t.succ).toRepresentation (z t) ⟨w, hw⟩) (y := c t • (⟨w, hw⟩ : (S t.succ).toSubmodule))).1 h1
  have hcomm : ∀ t y, Commute (ρ y) (Q t) := by
    intro t y
    refine Commute.sub_right ?_ ((Commute.one_right _).smul_right _)
    show ρ y * ρ (z t) = ρ (z t) * ρ y
    rw [← map_mul, ← map_mul, hz]
  obtain ⟨l₁, hl₁, hm₁⟩ := exists_prod_maps (fun j => (S j).toSubmodule) t₀ Q hQ t₀.succ (Fin.last N)
    (Fin.le_last _) (by
      rintro t a - rfl
      exact absurd a (not_le.2 Fin.castSucc_lt_succ))
  obtain ⟨l₂, hl₂, hm₂⟩ := exists_prod_maps (fun j => (S j).toSubmodule) t₀ Q hQ 0 t₀.castSucc
    (Fin.zero_le _) (by
      rintro t - a rfl
      exact absurd a (not_le.2 Fin.castSucc_lt_succ))
  have hP : ∀ y, Commute (ρ y) (l₂.map Q).prod := fun y =>
    Commute.list_prod_right _ _ fun x hx => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
      exact hcomm t y
  have hker : (S t₀.castSucc).toSubmodule.comap (S t₀.succ).toSubmodule.subtype ≤
      LinearMap.ker ((l₂.map Q).prod ∘ₗ (S t₀.succ).toSubmodule.subtype) := by
    intro x hx
    have := hm₂ _ hx
    simp only [h0] at this
    exact this
  refine ⟨l₂ ++ l₁, ⟨Submodule.liftQ _ _ hker, fun g => Submodule.linearMap_qext _
    (LinearMap.ext fun x => ?_)⟩, ?_, fun w => ?_⟩
  · exact (LinearMap.congr_fun (hP g).eq (x : J)).symm
  · intro t htl
    rcases List.mem_append.1 htl with a | a
    · exact hl₂ t a
    · exact hl₁ t a
  · have hw : w ∈ (S (Fin.last N)).toSubmodule := by rw [hN]; trivial
    refine ⟨Submodule.Quotient.mk ⟨_, hm₁ w hw⟩, ?_⟩
    rw [List.map_append, List.prod_append]
    rfl

end GlobalTheory.FiltStepCut
