import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed

open NumberField

namespace GlobalTheory.NatSmulMemOfSpan

/- English proof (translation)
Establish `halg : IsAlgebraic ℤ c` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic c)`. Take `⟨y, hy, hint⟩` from `halg.exists_integral_multiple`. Establish `hint' : IsIntegral ℤ ((y.natAbs : K) * c)`. Establish `hc : (y.natAbs : K) = ((y.natAbs : ℤ) : K)` using `(Int.cast_natCast _).symm`. Rewrite `hint` using `[zsmul_eq_mul]`.

Break down `Int.natAbs_eq y with h | h` into its components or cases. Rewrite using `[hc, ← h]`. Conclude with `hint`. Establish `h2 : ((y.natAbs : ℤ) : K) = -(y : K)`. Establish `: (y.natAbs : ℤ) = -y` using `by omega`.

Rewrite using `[this, Int.cast_neg]`. Rewrite using `[hc, h2, neg_mul]`. Conclude with `hint.neg`. Conclude with `⟨y.natAbs, Int.natAbs_pos.2 hy, ⟨_, hint'⟩, rfl⟩`.
-/
theorem exists_nat_mul_eq_coe {K : Type*} [Field K] [NumberField K] (c : K) :
    ∃ m : ℕ, 0 < m ∧ ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = (m : K) * c := by
  have halg : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  have hint' : IsIntegral ℤ ((y.natAbs : K) * c) := by
    have hc : (y.natAbs : K) = ((y.natAbs : ℤ) : K) := (Int.cast_natCast _).symm
    rw [zsmul_eq_mul] at hint
    rcases Int.natAbs_eq y with h | h
    · rw [hc, ← h]; exact hint
    · have h2 : ((y.natAbs : ℤ) : K) = -(y : K) := by
        have : (y.natAbs : ℤ) = -y := by omega
        rw [this, Int.cast_neg]
      rw [hc, h2, neg_mul]; exact hint.neg
  exact ⟨y.natAbs, Int.natAbs_pos.2 hy, ⟨_, hint'⟩, rfl⟩

/- English proof (translation)
Establish `key : ∀ (a : 𝓞 K) (w : V), w ∈ Λ → algebraMap (𝓞 K) K a • w ∈ Λ` using `fun a w hw => by`. Rewrite using `[algebraMap_smul]`. Conclude with `Λ.smul_mem a hw`. Establish `keyN : ∀ (m : ℕ) (w : V), w ∈ Λ → (m : K) • w ∈ Λ` using `fun m w hw => by`. Simplify using `using key (m : 𝓞 K) w hw`.

Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_pos, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_pos, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨m, hm, hx⟩` from `hx`.

Take `⟨n, hn, hy⟩` from `hy`. Use `⟨m * n, Nat.mul_pos hm hn, ?_⟩` and prove the remaining obligations. Establish `: ((m * n : ℕ) : K) • (x + y) = (n : K) • ((m : K) • x) + (m : K) • ((n : K) • y)`. Rewrite using `[smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (n : K)]`. Rewrite using `[this]`.

Conclude with `Λ.add_mem (keyN n _ hx) (keyN m _ hy)`. Consider the case `smul c x _ hx`. Take `⟨n, hn, hx⟩` from `hx`. Take `⟨m, hm, a, ha⟩` from `exists_nat_mul_eq_coe c`. Use `⟨m * n, Nat.mul_pos hm hn, ?_⟩` and prove the remaining obligations.

Establish `: ((m * n : ℕ) : K) • (c • x) = algebraMap (𝓞 K) K a • ((n : K) • x)`. Rewrite using `[ha, smul_smul, smul_smul, Nat.cast_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `key a _ hx`.
-/
theorem exists_nat_smul_mem_of_mem_span {K V : Type*} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Λ : Submodule (𝓞 K) V) {v : V}
    (hv : v ∈ Submodule.span K (Λ : Set V)) : ∃ n : ℕ, 0 < n ∧ (n : K) • v ∈ Λ := by
  have key : ∀ (a : 𝓞 K) (w : V), w ∈ Λ → algebraMap (𝓞 K) K a • w ∈ Λ := fun a w hw => by
    rw [algebraMap_smul]; exact Λ.smul_mem a hw
  have keyN : ∀ (m : ℕ) (w : V), w ∈ Λ → (m : K) • w ∈ Λ := fun m w hw => by
    simpa using key (m : 𝓞 K) w hw
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hx⟩ := hx
    obtain ⟨n, hn, hy⟩ := hy
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    have : ((m * n : ℕ) : K) • (x + y) = (n : K) • ((m : K) • x) + (m : K) • ((n : K) • y) := by
      rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (n : K)]
    rw [this]
    exact Λ.add_mem (keyN n _ hx) (keyN m _ hy)
  | smul c x _ hx =>
    obtain ⟨n, hn, hx⟩ := hx
    obtain ⟨m, hm, a, ha⟩ := exists_nat_mul_eq_coe c
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    have : ((m * n : ℕ) : K) • (c • x) = algebraMap (𝓞 K) K a • ((n : K) • x) := by
      rw [ha, smul_smul, smul_smul, Nat.cast_mul]
      congr 1
      ring
    rw [this]
    exact key a _ hx

/- English proof (translation)
The claim follows from `exists_nat_smul_mem_of_mem_span Λ (by rw [hΛ.span_eq_top]; exact Submodule.mem_top)`.
-/
theorem exists_nat_smul_mem {D : Formalism.BasicNotions.D7} (Λ : GlobalTheory.Unfold.LV D)
    (hΛ : Submodule.IsLattice ((Formalism.BasicNotions.D7.host D).E) Λ)
    (v : Formalism.BasicNotions.HSpace.V (Formalism.MainNotions.S.VS D)) :
    ∃ n : ℕ, 0 < n ∧ (n : (Formalism.BasicNotions.D7.host D).E) • v ∈ Λ :=
  exists_nat_smul_mem_of_mem_span Λ (by rw [hΛ.span_eq_top]; exact Submodule.mem_top)

end GlobalTheory.NatSmulMemOfSpan
