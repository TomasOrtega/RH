import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinianLimitLiftOfCompatibleStatement

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.Tower

/- English proof (translation)
Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le h`. Proceed by induction on `d with`. Consider the case `zero => exact L.ρ_self b _`. Consider the case `succ d ih`. Establish `h'` using `L.ρ_succ (b + d) b (Nat.le_add_right _ _) (x.1 (b + d + 1))`.

Rewrite `h'` using `[x.2 (b + d), ih (Nat.le_add_right _ _)]`. Conclude with `h'`.
-/
theorem rho_lim {W : Type} [CommRing W] {l : ℕ} {S S' : Sys.{1} W} (L : LSeq l S S') (x : S.lim)
    (b c : ℕ) (h : b ≤ c) : L.ρ c b (x.1 c) = x.1 b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact L.ρ_self b _
  | succ d ih =>
    have h' := L.ρ_succ (b + d) b (Nat.le_add_right _ _) (x.1 (b + d + 1))
    rw [x.2 (b + d), ih (Nat.le_add_right _ _)] at h'
    exact h'

/- English proof (translation)
Introduce `W _ l S S' L hA n x hx`. Establish `hex : ∀ a, ∃ y, L.ν a (n + a) y = x.1 (n + a)` using `fun a => L.ex₁ a n (n + a) (Nat.add_comm _ _) _ (by rw [rho_lim L x n (n + a) (Nat.le_add_right _ _), hx])`. Use `choose y hy using hex`. Establish `hN : ∀ a w, w ∈ LinearMap.ker (L.ν (a + 1) (n + (a + 1))) → S.r a w ∈ LinearMap.ker (L.ν a (n + a))`. Introduce `a w hw`.

Establish `hw' : L.ν (a + 1) (n + a + 1) w = 0` using `hw`. Rewrite using `[LinearMap.mem_ker, ← L.ν_r a (n + a) (Nat.le_add_left _ _), hw', map_zero]`. Establish `hc : ∀ a, S.r a (y (a + 1)) - y a ∈ LinearMap.ker (L.ν a (n + a))`. Introduce `a`. Establish `h1 : L.ν (a + 1) (n + a + 1) (y (a + 1)) = x.1 (n + a + 1)` using `hy (a + 1)`.

Rewrite using `[LinearMap.mem_ker, map_sub, ← L.ν_r a (n + a) (Nat.le_add_left _ _), h1, x.2 (n + a), hy a, sub_self]`. Take `⟨z, hz⟩` from `GlobalTheory.T.artinian_limit_lift_of_compatible W S hA (fun a => LinearMap.ker (L.ν a (n + a))) y hN hc`. Establish `key : ∀ a, ((l : W) ^ n) • z.1 (n + a) = x.1 (n + a)`. Introduce `a`. Establish `h1` using `L.ν_ρ a (n + a) (Nat.le_add_left _ _) (z.1 (n + a))`.

Establish `h2 : L.ν a (n + a) (z.1 a) = x.1 (n + a)`. Establish `h3 : L.ν a (n + a) (z.1 a - y a) = 0` using `hz a`. Rewrite `h3` using `[map_sub, hy a, sub_eq_zero]`. Conclude with `h3`. Rewrite `h1` using `[rho_lim L z a (n + a) (Nat.le_add_left _ _), h2, Nat.add_sub_cancel]`.

Conclude with `h1.symm`. Use `⟨z, Subtype.ext (funext fun c => ?_)⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lim_eq_pow_smul : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' : Sys.{1} W) (_ : LSeq l S S'),
    (∀ n, IsArtinian W (S.M n)) → ∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y := by
  intro W _ l S S' L hA n x hx
  have hex : ∀ a, ∃ y, L.ν a (n + a) y = x.1 (n + a) := fun a =>
    L.ex₁ a n (n + a) (Nat.add_comm _ _) _ (by rw [rho_lim L x n (n + a) (Nat.le_add_right _ _), hx])
  choose y hy using hex
  have hN : ∀ a w, w ∈ LinearMap.ker (L.ν (a + 1) (n + (a + 1))) →
      S.r a w ∈ LinearMap.ker (L.ν a (n + a)) := by
    intro a w hw
    have hw' : L.ν (a + 1) (n + a + 1) w = 0 := hw
    rw [LinearMap.mem_ker, ← L.ν_r a (n + a) (Nat.le_add_left _ _), hw', map_zero]
  have hc : ∀ a, S.r a (y (a + 1)) - y a ∈ LinearMap.ker (L.ν a (n + a)) := by
    intro a
    have h1 : L.ν (a + 1) (n + a + 1) (y (a + 1)) = x.1 (n + a + 1) := hy (a + 1)
    rw [LinearMap.mem_ker, map_sub, ← L.ν_r a (n + a) (Nat.le_add_left _ _), h1, x.2 (n + a), hy a,
      sub_self]
  obtain ⟨z, hz⟩ := GlobalTheory.T.artinian_limit_lift_of_compatible W S hA (fun a => LinearMap.ker (L.ν a (n + a))) y hN hc
  have key : ∀ a, ((l : W) ^ n) • z.1 (n + a) = x.1 (n + a) := by
    intro a
    have h1 := L.ν_ρ a (n + a) (Nat.le_add_left _ _) (z.1 (n + a))
    have h2 : L.ν a (n + a) (z.1 a) = x.1 (n + a) := by
      have h3 : L.ν a (n + a) (z.1 a - y a) = 0 := hz a
      rw [map_sub, hy a, sub_eq_zero] at h3
      exact h3
    rw [rho_lim L z a (n + a) (Nat.le_add_left _ _), h2, Nat.add_sub_cancel] at h1
    exact h1.symm
  refine ⟨z, Subtype.ext (funext fun c => ?_)⟩
  calc x.1 c = L.ρ (n + c) c (x.1 (n + c)) := (rho_lim L x c (n + c) (Nat.le_add_left _ _)).symm
    _ = L.ρ (n + c) c (((l : W) ^ n) • z.1 (n + c)) := by rw [key]
    _ = ((l : W) ^ n) • L.ρ (n + c) c (z.1 (n + c)) := map_smul _ _ _
    _ = ((l : W) ^ n) • z.1 c := by rw [rho_lim L z c (n + c) (Nat.le_add_left _ _)]

end GlobalTheory.CompanionTheory.Tower
