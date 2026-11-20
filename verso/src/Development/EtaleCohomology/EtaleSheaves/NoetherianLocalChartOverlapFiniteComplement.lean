import Development.EtaleCohomology.EtaleSheaves.LZIdemSumApprox

noncomputable section
open LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.LZIdemSumNoetherian

def NoetherianLocalChartOverlapFiniteComplement : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : Type) [Field K]
  [Algebra A K] (B C : Subalgebra A K) (t : K), Charts B C t → B.FG → C.FG →
  ∃ N : Submodule A K, N.FG ∧ Subalgebra.toSubmodule (AdjoinInv B t) ≤
    Subalgebra.toSubmodule B ⊔ Subalgebra.toSubmodule C ⊔ N

def LZIdemPow : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] (K : Type) [Field K] [Algebra A K]
  (B C : Subalgebra A K) (t : K), Charts B C t → ∀ e f : K, IdemPair B C t e f → ∀ k : ℕ,
  ∃ b ∈ B, ∃ c ∈ C, e - b ∈ mS B ∧ c - f ∈ mS C ∧
    b - c ∈ (IsLocalRing.maximalIdeal A ^ k) • Subalgebra.toSubmodule (AdjoinInv B t)

def LZARStep : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (M : Type) [AddCommGroup M]
  [Module A M] (N P : Submodule A M), N.FG →
  ∃ k : ℕ, 1 ≤ k ∧ (IsLocalRing.maximalIdeal A ^ k) • N ⊓ P ≤ IsLocalRing.maximalIdeal A • P

/- English proof (translation)
Introduce `A _ _ _ K _ _ B C t hc hB hC e f hp`. Take `⟨N, hN, hD⟩` from `h1 A K B C t hc hB hC`. Take `⟨k, hk, hAR⟩` from `h3 A K N (Subalgebra.toSubmodule B ⊔ Subalgebra.toSubmodule C) hN`. Take `⟨b, hb, c, hcC, heb, hcf, hbc⟩` from `h2 A K B C t hc e f hp k`. Establish `hmk : IsLocalRing.maximalIdeal A ^ k ≤ IsLocalRing.maximalIdeal A` using `Ideal.pow_le_self (by omega)`.

Establish `hbc'` using `Submodule.smul_mono (le_refl (IsLocalRing.maximalIdeal A ^ k)) hD hbc`. Rewrite `hbc'` using `[Submodule.smul_sup, Submodule.smul_sup]`. Take `⟨x, hx, n, hn, hxn⟩` from `Submodule.mem_sup.mp hbc'`. Take `⟨β, hβ, γ, hγ, hβγ⟩` from `Submodule.mem_sup.mp hx`. Establish `hβB : β ∈ B` using `Submodule.smul_le_right hβ`.

Establish `hγC : γ ∈ C` using `Submodule.smul_le_right hγ`. Establish `hnP : n ∈ Subalgebra.toSubmodule B ⊔ Subalgebra.toSubmodule C`. Use `Submodule.mem_sup.mpr ⟨b - β, B.sub_mem hb hβB, -(c + γ), C.neg_mem (C.add_mem hcC hγC), ?_⟩` and prove the remaining obligations. Take the linear combination `-hxn - hβγ`. Establish `hnm` using `hAR ⟨hn, hnP⟩`.

Rewrite `hnm` using `[Submodule.smul_sup]`. Take `⟨u, hu, v, hv, huv⟩` from `Submodule.mem_sup.mp hnm`. Establish `hβm : β ∈ mS B` using `Submodule.smul_mono_left hmk hβ`. Establish `hγm : γ ∈ mS C` using `Submodule.smul_mono_left hmk hγ`. Establish `hum : u ∈ mS B` using `hu`.

Establish `hvm : v ∈ mS C` using `hv`. Use `Submodule.mem_sup.mpr ⟨(e - b) + β + u, (mS B).add_mem ((mS B).add_mem heb hβm) hum, γ + v + (c - f), (mS C).add_mem ((mS C).add_mem hγm hvm) hcf, ?_⟩` and prove the remaining obligations. Take the linear combination `hxn + hβγ + huv`.
-/
theorem goal_of (h1 : NoetherianLocalChartOverlapFiniteComplement) (h2 : LZIdemPow) (h3 : LZARStep) :
    LateralTheory.E.IdempotentLiftingAlt.LZIdemSumNoeth := by
  intro A _ _ _ K _ _ B C t hc hB hC e f hp
  obtain ⟨N, hN, hD⟩ := h1 A K B C t hc hB hC
  obtain ⟨k, hk, hAR⟩ := h3 A K N (Subalgebra.toSubmodule B ⊔ Subalgebra.toSubmodule C) hN
  obtain ⟨b, hb, c, hcC, heb, hcf, hbc⟩ := h2 A K B C t hc e f hp k
  have hmk : IsLocalRing.maximalIdeal A ^ k ≤ IsLocalRing.maximalIdeal A := Ideal.pow_le_self (by omega)
  have hbc' := Submodule.smul_mono (le_refl (IsLocalRing.maximalIdeal A ^ k)) hD hbc
  rw [Submodule.smul_sup, Submodule.smul_sup] at hbc'
  obtain ⟨x, hx, n, hn, hxn⟩ := Submodule.mem_sup.mp hbc'
  obtain ⟨β, hβ, γ, hγ, hβγ⟩ := Submodule.mem_sup.mp hx
  have hβB : β ∈ B := Submodule.smul_le_right hβ
  have hγC : γ ∈ C := Submodule.smul_le_right hγ
  have hnP : n ∈ Subalgebra.toSubmodule B ⊔ Subalgebra.toSubmodule C := by
    refine Submodule.mem_sup.mpr ⟨b - β, B.sub_mem hb hβB, -(c + γ), C.neg_mem (C.add_mem hcC hγC), ?_⟩
    linear_combination -hxn - hβγ
  have hnm := hAR ⟨hn, hnP⟩
  rw [Submodule.smul_sup] at hnm
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hnm
  have hβm : β ∈ mS B := Submodule.smul_mono_left hmk hβ
  have hγm : γ ∈ mS C := Submodule.smul_mono_left hmk hγ
  have hum : u ∈ mS B := hu
  have hvm : v ∈ mS C := hv
  refine Submodule.mem_sup.mpr ⟨(e - b) + β + u, (mS B).add_mem ((mS B).add_mem heb hβm) hum,
    γ + v + (c - f), (mS C).add_mem ((mS C).add_mem hγm hvm) hcf, ?_⟩
  linear_combination hxn + hβγ + huv

end LateralTheory.E.LZIdemSumNoetherian
