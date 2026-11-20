import Development.EtaleCohomology.EtaleSheaves.StandardChartsLineZero

noncomputable section
open LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.IdempotentLiftingAlt

def LZIdemSumNoeth : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : Type) [Field K]
  [Algebra A K] (B C : Subalgebra A K) (t : K), Charts B C t → B.FG → C.FG → ∀ e f : K, IdemPair B C t e f →
  e - f ∈ mS B ⊔ mS C

def LZIdemSumApprox : Prop := LZIdemSumNoeth → ∀ (A : Type) [CommRing A] [IsLocalRing A] (K : Type) [Field K]
  [Algebra A K] (B C : Subalgebra A K) (t : K), Charts B C t → ∀ e f : K, IdemPair B C t e f →
  e - f ∈ mS B ⊔ mS C

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

/- English proof (translation)
Unfold `mS`. Conclude with `Submodule.smul_le_right`.
-/
theorem mS_le (S : Subalgebra A K) : mS S ≤ Subalgebra.toSubmodule S := by
  unfold mS
  exact Submodule.smul_le_right

/- English proof (translation)
Take `⟨β, hβ, γ, hγ, hsum⟩` from `Submodule.mem_sup.mp h`. Establish `hβB : β ∈ B` using `mS_le B hβ`. Establish `hγC : γ ∈ C` using `mS_le C hγ`. Use `⟨e - β, B.sub_mem he hβB, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `: e - β = f + γ` using `by linear_combination -hsum`.

Rewrite using `[this]`. Conclude with `C.add_mem hf hγC`. Establish `: e - β - e = -β` using `by ring`. Rewrite using `[this]`. Conclude with `(mS B).neg_mem hβ`.

Establish `: e - β - f = γ` using `by linear_combination -hsum`. Rewrite using `[this]`. Conclude with `hγ`.
-/
theorem lift_of_sum (B C : Subalgebra A K) (e f : K) (he : e ∈ B) (hf : f ∈ C) (h : e - f ∈ mS B ⊔ mS C) :
    ∃ g ∈ B, g ∈ C ∧ g - e ∈ mS B ∧ g - f ∈ mS C := by
  obtain ⟨β, hβ, γ, hγ, hsum⟩ := Submodule.mem_sup.mp h
  have hβB : β ∈ B := mS_le B hβ
  have hγC : γ ∈ C := mS_le C hγ
  refine ⟨e - β, B.sub_mem he hβB, ?_, ?_, ?_⟩
  · have : e - β = f + γ := by linear_combination -hsum
    rw [this]; exact C.add_mem hf hγC
  · have : e - β - e = -β := by ring
    rw [this]; exact (mS B).neg_mem hβ
  · have : e - β - f = γ := by linear_combination -hsum
    rw [this]; exact hγ

/- English proof (translation)
Introduce `A _ _ _ K _ _ B C t hc e f hp`. Conclude with `lift_of_sum B C e f hp.1 hp.2.1 (hA hN A K B C t hc e f hp)`.
-/
theorem IdemLift_of (hN : LZIdemSumNoeth) (hA : LZIdemSumApprox) : LateralTheory.E.StandardEtaleChartsIdempotentGluing.IdemLift := by
  intro A _ _ _ K _ _ B C t hc e f hp
  exact lift_of_sum B C e f hp.1 hp.2.1 (hA hN A K B C t hc e f hp)

end LateralTheory.E.IdempotentLiftingAlt
