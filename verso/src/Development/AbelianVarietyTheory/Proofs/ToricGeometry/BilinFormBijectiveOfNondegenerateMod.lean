import Mathlib

open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

/- English proof (translation)
Use `set b := Module.Free.chooseBasis ℤ X`. Establish `hinj : Function.Injective E`. Use `(injective_iff_map_eq_zero E).2 fun a ha => ?_` and prove the remaining obligations. Use `b.ext_elem fun i => ?_` and prove the remaining obligations. Take `⟨n, hn⟩ : ∃ n, (b.repr a i).natAbs = n` from `⟨_, rfl⟩`.

Take `⟨a', ha'⟩` from `h (n + 1) a (Nat.succ_pos n) (fun y => by rw [ha]; simp)`. Establish `hdvd : ((n + 1 : ℕ) : ℤ) ∣ b.repr a i` using `⟨b.repr a' i, by rw [ha']; simp⟩`. Rewrite using `[map_zero, Finsupp.zero_apply]`. Use `Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd ?_` and prove the remaining obligations. Rewrite using `[Int.natAbs_natCast, hn]`.

Conclude with `Nat.lt_succ_self n`. Establish `hrank : Module.rank ℤ (Module.Dual ℤ X ⧸ LinearMap.range E) = 0`. Establish `h1` using `rank_quotient_add_rank_of_isDomain (LinearMap.range E)`. Rewrite `h1` using `[← (LinearEquiv.ofInjective E hinj).rank_eq, ← b.toDualEquiv.rank_eq]`. Take `⟨n, hn⟩` from `Cardinal.lt_aleph0.1 (Module.rank_lt_aleph0 ℤ X)`.

Establish `hq : Module.rank ℤ (Module.Dual ℤ X ⧸ LinearMap.range E) < Cardinal.aleph0` using `lt_of_le_of_lt (le_self_add) (h1 ▸ Module.rank_lt_aleph0 ℤ X)`. Take `⟨m, hm⟩` from `Cardinal.lt_aleph0.1 hq`. Rewrite `h1` using `[hm, hn]`. Rewrite using `[hm]`. Establish `: m + n = n` using `by exact_mod_cast h1`.

Conclude with `(by omega : m = 0)` after adjusting the coercions. Use `⟨hinj, fun f => ?_⟩` and prove the remaining obligations. Take `⟨c, hc0, hcf⟩` from `rank_eq_zero_iff.1 hrank (Submodule.Quotient.mk f)`. Rewrite `hcf` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Take `⟨x, hx⟩` from `hcf`.

Establish `hk : 0 < c.natAbs * c.natAbs` using `Nat.mul_pos (Int.natAbs_pos.2 hc0) (Int.natAbs_pos.2 hc0)`. Take `⟨a', ha'⟩` from `h (c.natAbs * c.natAbs) (c • x) hk (fun y => by`. Rewrite using `[Int.natAbs_mul_self, map_smul, hx, smul_smul]`. Use the proof step `simp)`. Use `⟨a', ?_⟩` and prove the remaining obligations.

Establish `hEq : E (c • x) = ((c.natAbs * c.natAbs : ℕ) : ℤ) • f`. Rewrite using `[Int.natAbs_mul_self, map_smul, hx, smul_smul]`. Rewrite `hEq` using `[ha', map_smul]`. Use extensionality with `y`. Establish `hy` using `LinearMap.congr_fun hEq y`.

Simplify using `only [LinearMap.smul_apply, smul_eq_mul] at hy`. Conclude with `mul_left_cancel₀ (by exact_mod_cast hk.ne') hy`.
-/
theorem bilinForm_bijective_of_nondegenerate_mod (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (E : LinearMap.BilinForm ℤ X)
    (h : ∀ (k : ℕ) (a : X), 0 < k → (∀ b, (k : ℤ) ∣ E a b) → ∃ a', a = (k : ℤ) • a') :
    Function.Bijective E := by
  classical
  set b := Module.Free.chooseBasis ℤ X
  have hinj : Function.Injective E := by
    refine (injective_iff_map_eq_zero E).2 fun a ha => ?_
    refine b.ext_elem fun i => ?_
    obtain ⟨n, hn⟩ : ∃ n, (b.repr a i).natAbs = n := ⟨_, rfl⟩
    obtain ⟨a', ha'⟩ := h (n + 1) a (Nat.succ_pos n) (fun y => by rw [ha]; simp)
    have hdvd : ((n + 1 : ℕ) : ℤ) ∣ b.repr a i := ⟨b.repr a' i, by rw [ha']; simp⟩
    rw [map_zero, Finsupp.zero_apply]
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd ?_
    rw [Int.natAbs_natCast, hn]
    exact Nat.lt_succ_self n
  have hrank : Module.rank ℤ (Module.Dual ℤ X ⧸ LinearMap.range E) = 0 := by
    have h1 := rank_quotient_add_rank_of_isDomain (LinearMap.range E)
    rw [← (LinearEquiv.ofInjective E hinj).rank_eq, ← b.toDualEquiv.rank_eq] at h1
    obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.1 (Module.rank_lt_aleph0 ℤ X)
    have hq : Module.rank ℤ (Module.Dual ℤ X ⧸ LinearMap.range E) < Cardinal.aleph0 :=
      lt_of_le_of_lt (le_self_add) (h1 ▸ Module.rank_lt_aleph0 ℤ X)
    obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.1 hq
    rw [hm, hn] at h1
    rw [hm]
    have : m + n = n := by exact_mod_cast h1
    exact_mod_cast (by omega : m = 0)
  refine ⟨hinj, fun f => ?_⟩
  obtain ⟨c, hc0, hcf⟩ := rank_eq_zero_iff.1 hrank (Submodule.Quotient.mk f)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hcf
  obtain ⟨x, hx⟩ := hcf
  have hk : 0 < c.natAbs * c.natAbs := Nat.mul_pos (Int.natAbs_pos.2 hc0) (Int.natAbs_pos.2 hc0)
  obtain ⟨a', ha'⟩ := h (c.natAbs * c.natAbs) (c • x) hk (fun y => by
    rw [Int.natAbs_mul_self, map_smul, hx, smul_smul]
    simp)
  refine ⟨a', ?_⟩
  have hEq : E (c • x) = ((c.natAbs * c.natAbs : ℕ) : ℤ) • f := by
    rw [Int.natAbs_mul_self, map_smul, hx, smul_smul]
  rw [ha', map_smul] at hEq
  ext y
  have hy := LinearMap.congr_fun hEq y
  simp only [LinearMap.smul_apply, smul_eq_mul] at hy
  exact mul_left_cancel₀ (by exact_mod_cast hk.ne') hy

end GlobalTheory
