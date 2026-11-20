import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.LatPow

/- English proof (translation)
Introduce `l _ O K _ _ _ _ _ G _ _ T v`. Establish `hv : v ∈ Submodule.span K (T.L.T : Set T.V)` using `by rw [T.L.span]; trivial`. It suffices to establish `h : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → (l : K) ^ n • v ∈ T.L.T by`. Take `⟨n₀, h⟩` from `h`. Conclude with `⟨n₀, fun n hn => ⟨⟨_, h n hn⟩, rfl⟩⟩`.

Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Use `⟨0, fun n _ => ?_⟩` and prove the remaining obligations. Establish `: (l : K) ^ n • x = ((l : O) ^ n) • x`. Rewrite using `[← algebraMap_smul K ((l : O) ^ n) x, map_pow, map_natCast]`.

Rewrite using `[this]`. Conclude with `T.L.T.smul_mem _ hx`. Consider the case `zero => exact ⟨0, fun n _ => by rw [smul_zero]; exact T.L.T.zero_mem⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`.

Take `⟨b, hb⟩` from `hy`. Conclude with `⟨max a b, fun n hn => by`. Rewrite using `[smul_add]`. Conclude with `T.L.T.add_mem (ha n (le_of_max_le_left hn)) (hb n (le_of_max_le_right hn))⟩`. Consider the case `smul c x _ hx`.

Take `⟨a, ha⟩` from `hx`. Take `⟨m, b, hb⟩` from `exists_pow_mul_mem (O := O) l c`. Use `⟨a + m, fun n hn => ?_⟩` and prove the remaining obligations. Establish `e : (l : K) ^ n • c • x = b • ((l : K) ^ (n - m) • x)`. Rewrite using `[← algebraMap_smul K b, ← hb, smul_smul, smul_smul]`.

Use `congr 1`. Rewrite using `[mul_comm ((l : K) ^ m) c, mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega), mul_comm]`. Rewrite using `[e]`. Conclude with `T.L.T.smul_mem _ (ha _ (by omega))`.
-/
theorem pow_smul_mem : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [NormedField K] [Algebra O K]
    [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (G : Type) [Group G] [TopologicalSpace G]
    (T : LocLat G ℚ_[l] K O) (v : T.V), ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∃ x : ↥T.L.T, (x : T.V) = (l : K) ^ n • v := by
  intro l _ O K _ _ _ _ _ G _ _ T v
  have hv : v ∈ Submodule.span K (T.L.T : Set T.V) := by rw [T.L.span]; trivial
  suffices h : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → (l : K) ^ n • v ∈ T.L.T by
    obtain ⟨n₀, h⟩ := h
    exact ⟨n₀, fun n hn => ⟨⟨_, h n hn⟩, rfl⟩⟩
  induction hv using Submodule.span_induction with
  | mem x hx =>
    refine ⟨0, fun n _ => ?_⟩
    have : (l : K) ^ n • x = ((l : O) ^ n) • x := by
      rw [← algebraMap_smul K ((l : O) ^ n) x, map_pow, map_natCast]
    rw [this]
    exact T.L.T.smul_mem _ hx
  | zero => exact ⟨0, fun n _ => by rw [smul_zero]; exact T.L.T.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨max a b, fun n hn => by
      rw [smul_add]
      exact T.L.T.add_mem (ha n (le_of_max_le_left hn)) (hb n (le_of_max_le_right hn))⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨m, b, hb⟩ := exists_pow_mul_mem (O := O) l c
    refine ⟨a + m, fun n hn => ?_⟩
    have e : (l : K) ^ n • c • x = b • ((l : K) ^ (n - m) • x) := by
      rw [← algebraMap_smul K b, ← hb, smul_smul, smul_smul]
      congr 1
      rw [mul_comm ((l : K) ^ m) c, mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega), mul_comm]
    rw [e]
    exact T.L.T.smul_mem _ (ha _ (by omega))

end GlobalTheory.LatPow
