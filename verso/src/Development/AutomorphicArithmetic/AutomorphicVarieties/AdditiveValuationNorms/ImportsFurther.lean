import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.Imports

open UpperTheory.V UpperTheory.V.PropA

/- English proof (translation)
Introduce `l _ X _ _ g a ha hg`. Take `⟨N, hN⟩` from `hg`. Take `⟨c, hc⟩` from `ha`. Establish `left : ∀ f h : Module.End ℤ_[l] X, InPow 1 f → InPow 1 (h * f)`. Introduce `f h hf v`.

Take `⟨w, hw⟩` from `hf v`. Conclude with `⟨h w, by rw [Module.End.mul_apply, hw, map_smul]⟩`. Establish `right : ∀ f h : Module.End ℤ_[l] X, InPow 1 f → InPow 1 (f * h)`. Introduce `f h hf v`. Conclude with `hf (h v)`.

Establish `zero : InPow 1 (0 : Module.End ℤ_[l] X)` using `fun v => ⟨0, by simp⟩`. Establish `add : ∀ f h : Module.End ℤ_[l] X, InPow 1 f → InPow 1 h → InPow 1 (f + h)`. Introduce `f h hf hh v`. Take `⟨w, hw⟩` from `hf v`. Take `⟨u, hu⟩` from `hh v`.

Conclude with `⟨w + u, by rw [LinearMap.add_apply, hw, hu, smul_add]⟩`. Establish `hB : InPow 1 ((a - 1) • g)`. Introduce `v`. Use `⟨c • g v, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, hc, mul_smul, pow_one]`.

Establish `hcomm : Commute (g - 1) ((a - 1) • g)` using `((Commute.refl g).sub_left (Commute.one_left g)).smul_right (a - 1)`. Establish `hsplit : a • g - 1 = (g - 1) + (a - 1) • g`. Rewrite using `[sub_smul, one_smul]`. Normalize the expressions using the abelian group laws. Use `⟨N, ?_⟩` and prove the remaining obligations.

Rewrite using `[hsplit, hcomm.add_pow]`. Use `Finset.sum_induction _ (InPow 1) add zero ?_` and prove the remaining obligations. Introduce `m hm`. Break down `Nat.lt_or_ge m N with hlt | hge` into its components or cases. Take `⟨k, hk⟩ : ∃ k, N - m = k + 1` from `⟨N - m - 1, by omega⟩`.

Rewrite using `[hk, pow_succ']`. Apply `right` to reduce the goal to its premises. Rewrite using `[← mul_assoc]`. Apply `right` to reduce the goal to its premises. Conclude with `left _ _ hB`.

Establish `hmN : m = N`. Simplify using `only [Finset.mem_range] at hm`. Use linear arithmetic over natural numbers and integers. Substitute `hmN` using the available equality. Conclude with `right _ _ (right _ _ hN)`.
-/
theorem UpperTheory.V.PropA.twist :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (g : Module.End ℤ_[l] X) (a : ℤ_[l]), (l : ℤ_[l]) ∣ a - 1 →
      Unip g → Unip (a • g) := by
  intro l _ X _ _ g a ha hg
  obtain ⟨N, hN⟩ := hg
  obtain ⟨c, hc⟩ := ha
  have left : ∀ f h : Module.End ℤ_[l] X, InPow 1 f → InPow 1 (h * f) := by
    intro f h hf v
    obtain ⟨w, hw⟩ := hf v
    exact ⟨h w, by rw [Module.End.mul_apply, hw, map_smul]⟩
  have right : ∀ f h : Module.End ℤ_[l] X, InPow 1 f → InPow 1 (f * h) := by
    intro f h hf v
    exact hf (h v)
  have zero : InPow 1 (0 : Module.End ℤ_[l] X) := fun v => ⟨0, by simp⟩
  have add : ∀ f h : Module.End ℤ_[l] X, InPow 1 f → InPow 1 h → InPow 1 (f + h) := by
    intro f h hf hh v
    obtain ⟨w, hw⟩ := hf v
    obtain ⟨u, hu⟩ := hh v
    exact ⟨w + u, by rw [LinearMap.add_apply, hw, hu, smul_add]⟩
  have hB : InPow 1 ((a - 1) • g) := by
    intro v
    refine ⟨c • g v, ?_⟩
    rw [LinearMap.smul_apply, hc, mul_smul, pow_one]
  have hcomm : Commute (g - 1) ((a - 1) • g) :=
    ((Commute.refl g).sub_left (Commute.one_left g)).smul_right (a - 1)
  have hsplit : a • g - 1 = (g - 1) + (a - 1) • g := by
    rw [sub_smul, one_smul]
    abel
  refine ⟨N, ?_⟩
  rw [hsplit, hcomm.add_pow]
  refine Finset.sum_induction _ (InPow 1) add zero ?_
  intro m hm
  rcases Nat.lt_or_ge m N with hlt | hge
  · obtain ⟨k, hk⟩ : ∃ k, N - m = k + 1 := ⟨N - m - 1, by omega⟩
    rw [hk, pow_succ']
    apply right
    rw [← mul_assoc]
    apply right
    exact left _ _ hB
  · have hmN : m = N := by
      simp only [Finset.mem_range] at hm
      omega
    subst hmN
    exact right _ _ (right _ _ hN)
