import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Klm
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ

open scoped MatrixGroups TensorProduct in
open Matrix in

/- English proof (translation)
Introduce `γ hγ`. Rewrite `hγ`, the goal using `[CongruenceSubgroup.Gamma_mem]`. Take `⟨h1, h2, h3, h4⟩` from `hγ`. Establish `e : ∀ z : ℤ, (z : ZMod M) = ZMod.castHom h (ZMod M) (z : ZMod M')` using `fun z => (map_intCast _ z).symm`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[e, h1, map_one]`. Rewrite using `[e, h2, map_zero]`. Rewrite using `[e, h3, map_zero]`. Rewrite using `[e, h4, map_one]`.
-/
theorem _root_.GlobalTheory.KZ.gamma_le_of_dvd {M M' : ℕ} (h : M ∣ M') :
    CongruenceSubgroup.Gamma M' ≤ CongruenceSubgroup.Gamma M := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  have e : ∀ z : ℤ, (z : ZMod M) = ZMod.castHom h (ZMod M) (z : ZMod M') := fun z =>
    (map_intCast _ z).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e, h1, map_one]
  · rw [e, h2, map_zero]
  · rw [e, h3, map_zero]
  · rw [e, h4, map_one]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

/- English proof (translation)
Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `x ⟨f, hf, rfl⟩`. Conclude with `⟨f, fun γ hγ => hf γ (gamma_le_of_dvd h hγ), rfl⟩`.
-/
theorem Tower.lev_mono (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] {M M' : ℕ} (h : M ∣ M') :
    X.Lev l M ≤ X.Lev l M' := by
  apply Submodule.span_mono
  rintro x ⟨f, hf, rfl⟩
  exact ⟨f, fun γ hγ => hf γ (gamma_le_of_dvd h hγ), rfl⟩

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨1, one_pos, Submodule.zero_mem _⟩`. Consider the case `tmul a f`. Take `⟨M, hM, hf⟩` from `X.level (Additive.toMul f : X.Kˣ)`. Use `⟨M, hM, ?_⟩` and prove the remaining obligations.

Establish `hmem : (1 : ℤ_[l]) ⊗ₜ[ℤ] f ∈ X.Lev l M` using `Submodule.subset_span ⟨Additive.toMul f, fun γ hγ => hf γ hγ, rfl⟩`. Establish `e : a ⊗ₜ[ℤ] f = a • ((1 : ℤ_[l]) ⊗ₜ[ℤ] f)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ a hmem`.

Consider the case `add y z hy hz`. Take `⟨M, hM, hy⟩` from `hy`. Take `⟨M', hM', hz⟩` from `hz`. Use `⟨M * M', Nat.mul_pos hM hM', Submodule.add_mem _ ?_ ?_⟩` and prove the remaining obligations. Conclude with `X.lev_mono l (dvd_mul_right M M') hy`.

Conclude with `X.lev_mono l (dvd_mul_left M' M) hz`.
-/
theorem Tower.exists_lev (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (y : X.Kl l) :
    ∃ M : ℕ, 0 < M ∧ y ∈ X.Lev l M := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, Submodule.zero_mem _⟩
  | tmul a f =>
    obtain ⟨M, hM, hf⟩ := X.level (Additive.toMul f : X.Kˣ)
    refine ⟨M, hM, ?_⟩
    have hmem : (1 : ℤ_[l]) ⊗ₜ[ℤ] f ∈ X.Lev l M :=
      Submodule.subset_span ⟨Additive.toMul f, fun γ hγ => hf γ hγ, rfl⟩
    have e : a ⊗ₜ[ℤ] f = a • ((1 : ℤ_[l]) ⊗ₜ[ℤ] f) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e]
    exact Submodule.smul_mem _ a hmem
  | add y z hy hz =>
    obtain ⟨M, hM, hy⟩ := hy
    obtain ⟨M', hM', hz⟩ := hz
    refine ⟨M * M', Nat.mul_pos hM hM', Submodule.add_mem _ ?_ ?_⟩
    · exact X.lev_mono l (dvd_mul_right M M') hy
    · exact X.lev_mono l (dvd_mul_left M' M) hz

/- English proof (translation)
Introduce `Ω _ _ ε X l _ K ι _ y hK`. Use `choose L hL hy using fun i => X.exists_lev l (y i)`. Use `⟨K * ∏ i, L i, Nat.mul_pos hK (Finset.prod_pos fun i _ => hL i), dvd_mul_right _ _, fun i => ?_⟩` and prove the remaining obligations. Use `X.lev_mono l ?_ (hy i)` and prove the remaining obligations. Conclude with `Dvd.dvd.mul_left (Finset.dvd_prod_of_mem L (Finset.mem_univ i)) K`.
-/
theorem Tower.exists_lev_family : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ)
    [Fact l.Prime] (K : ℕ) {ι : Type} [Fintype ι] (y : ι → X.Kl l), 0 < K →
    ∃ M : ℕ, 0 < M ∧ K ∣ M ∧ ∀ i, y i ∈ X.Lev l M := by
  intro Ω _ _ ε X l _ K ι _ y hK
  choose L hL hy using fun i => X.exists_lev l (y i)
  refine ⟨K * ∏ i, L i, Nat.mul_pos hK (Finset.prod_pos fun i _ => hL i), dvd_mul_right _ _, fun i => ?_⟩
  refine X.lev_mono l ?_ (hy i)
  exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem L (Finset.mem_univ i)) K

end GlobalTheory.KZ
