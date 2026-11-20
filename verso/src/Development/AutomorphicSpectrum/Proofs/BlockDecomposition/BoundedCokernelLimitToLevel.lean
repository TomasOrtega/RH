import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinianLimitLiftOfCompatibleStatement

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TwCok

/- English proof (translation)
Use `haveI := isNoetherian_of_isNoetherianRing_of_finite W T`. Set `f : ℕ →o Submodule W T` to `⟨fun k => LinearMap.ker ((r ^ k) • LinearMap.id : T →ₗ[W] T), fun a b hab t ht => by`. Simplify using `only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at ht ⊢`. Take `⟨c, rfl⟩` from `Nat.exists_eq_add_of_le hab`. Rewrite using `[pow_add, mul_comm, mul_smul, ht, smul_zero]⟩`.

Take `⟨n, hn⟩` from `monotone_stabilizes_iff_noetherian.mpr inferInstance f`. Use `⟨n, fun k t ht => ?_⟩` and prove the remaining obligations. Break down `le_total k n with hkn | hnk` into its components or cases. Take `⟨c, rfl⟩` from `Nat.exists_eq_add_of_le hkn`. Rewrite using `[pow_add, mul_comm, mul_smul, ht, smul_zero]`.

Establish `h1 : t ∈ f k`. Simplify using `only [f, OrderHom.coe_mk, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]`. Conclude with `ht`. Rewrite `h1` using `[← hn k hnk]`. Establish `h2 : t ∈ LinearMap.ker ((r ^ n) • LinearMap.id : T →ₗ[W] T)` using `h1`.

Rewrite `h2` using `[LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]`. Conclude with `h2`.
-/
theorem pow_torsion_bounded {W : Type} [CommRing W] [IsNoetherianRing W] (r : W) (T : Type 1)
    [AddCommGroup T] [Module W T] [Module.Finite W T] :
    ∃ c : ℕ, ∀ (k : ℕ) (t : T), r ^ k • t = 0 → r ^ c • t = 0 := by
  haveI := isNoetherian_of_isNoetherianRing_of_finite W T
  let f : ℕ →o Submodule W T :=
    ⟨fun k => LinearMap.ker ((r ^ k) • LinearMap.id : T →ₗ[W] T), fun a b hab t ht => by
      simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at ht ⊢
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
      rw [pow_add, mul_comm, mul_smul, ht, smul_zero]⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance f
  refine ⟨n, fun k t ht => ?_⟩
  rcases le_total k n with hkn | hnk
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hkn
    rw [pow_add, mul_comm, mul_smul, ht, smul_zero]
  · have h1 : t ∈ f k := by
      simp only [f, OrderHom.coe_mk, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
      exact ht
    rw [← hn k hnk] at h1
    have h2 : t ∈ LinearMap.ker ((r ^ n) • LinearMap.id : T →ₗ[W] T) := h1
    rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at h2
    exact h2

variable {W : Type} [CommRing W] {l : ℕ} {S S' : Sys.{1} W}

def conn (Q : LSeq l S S') (n : ℕ) (x : S.M n) : S'.lim :=
  ⟨fun a => Q.δ n a x, fun a => Q.δ_r n a x⟩

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `a`. Simplify using `[conn]`.
-/
theorem conn_smul (Q : LSeq l S S') (n : ℕ) (s : W) (x : S.M n) :
    s • conn Q n x = conn Q n (s • x) := by
  apply Subtype.ext
  funext a
  simp [conn]

/- English proof (translation)
Rewrite using `[conn_smul, Q.kill n x]`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `a`. Simplify using `[conn]`.
-/
theorem conn_kill (Q : LSeq l S S') (n : ℕ) (x : S.M n) : ((l : W) ^ n) • conn Q n x = 0 := by
  rw [conn_smul, Q.kill n x]
  apply Subtype.ext
  funext a
  simp [conn]

/- English proof (translation)
Establish `hy : ∀ m, n ≤ m → ∃ u : S.M m, Q.ρ m n u = x` using `fun m hm => Q.ex₂ (m - n) n m (by omega) x (h _)`. Set `y : ∀ m, S.M m` to `fun m => if hm : n ≤ m then (hy m hm).choose else 0`. Establish `hyx : ∀ m (hm : n ≤ m), Q.ρ m n (y m) = x`. Introduce `m hm`. Simplify using `only [y, dif_pos hm]`.

Conclude with `(hy m hm).choose_spec`. Set `N : ∀ m, Submodule W (S.M m)` to `fun m => if n ≤ m then LinearMap.ker (Q.ρ m n) else ⊤`. Establish `hN : ∀ m (hm : n ≤ m), N m = LinearMap.ker (Q.ρ m n)` using `fun m hm => if_pos hm`. Establish `hN' : ∀ m (hm : ¬ n ≤ m), N m = ⊤` using `fun m hm => if_neg hm`. Establish `hNr : ∀ m, ∀ u ∈ N (m + 1), S.r m u ∈ N m`.

Introduce `m u hu`. Distinguish the cases in `hm : n ≤ m`. Rewrite `hu` using `[hN (m + 1) (by omega), LinearMap.mem_ker]`. Rewrite using `[hN m hm, LinearMap.mem_ker, ← Q.ρ_succ m n hm]`. Conclude with `hu`.

Rewrite using `[hN' m hm]`. Conclude with `Submodule.mem_top`. Establish `hyr : ∀ m, S.r m (y (m + 1)) - y m ∈ N m`. Introduce `m`. Distinguish the cases in `hm : n ≤ m`.

Rewrite using `[hN m hm, LinearMap.mem_ker, map_sub, ← Q.ρ_succ m n hm, hyx (m + 1) (by omega), hyx m hm, sub_self]`. Rewrite using `[hN' m hm]`. Conclude with `Submodule.mem_top`. Take `⟨z, hz⟩` from `GlobalTheory.T.artinian_limit_lift_of_compatible W S hA N y hNr hyr`. Use `⟨z, ?_⟩` and prove the remaining obligations.

Establish `h1` using `hz n`. Rewrite `h1` using `[hN n le_rfl, LinearMap.mem_ker, map_sub, Q.ρ_self, Q.ρ_self, sub_eq_zero]`. Establish `h2` using `hyx n le_rfl`. Rewrite `h2` using `[Q.ρ_self]`. Rewrite using `[← h2]`.

Conclude with `h1`.
-/
theorem lift_of_conn_zero (Q : LSeq l S S') (hA : ∀ n, IsArtinian W (S.M n)) (n : ℕ) (x : S.M n)
    (h : ∀ a, Q.δ n a x = 0) : ∃ y : S.lim, y.1 n = x := by
  classical
  have hy : ∀ m, n ≤ m → ∃ u : S.M m, Q.ρ m n u = x := fun m hm =>
    Q.ex₂ (m - n) n m (by omega) x (h _)
  let y : ∀ m, S.M m := fun m => if hm : n ≤ m then (hy m hm).choose else 0
  have hyx : ∀ m (hm : n ≤ m), Q.ρ m n (y m) = x := by
    intro m hm
    simp only [y, dif_pos hm]
    exact (hy m hm).choose_spec
  let N : ∀ m, Submodule W (S.M m) := fun m => if n ≤ m then LinearMap.ker (Q.ρ m n) else ⊤
  have hN : ∀ m (hm : n ≤ m), N m = LinearMap.ker (Q.ρ m n) := fun m hm => if_pos hm
  have hN' : ∀ m (hm : ¬ n ≤ m), N m = ⊤ := fun m hm => if_neg hm
  have hNr : ∀ m, ∀ u ∈ N (m + 1), S.r m u ∈ N m := by
    intro m u hu
    by_cases hm : n ≤ m
    · rw [hN (m + 1) (by omega), LinearMap.mem_ker] at hu
      rw [hN m hm, LinearMap.mem_ker, ← Q.ρ_succ m n hm]
      exact hu
    · rw [hN' m hm]
      exact Submodule.mem_top
  have hyr : ∀ m, S.r m (y (m + 1)) - y m ∈ N m := by
    intro m
    by_cases hm : n ≤ m
    · rw [hN m hm, LinearMap.mem_ker, map_sub, ← Q.ρ_succ m n hm, hyx (m + 1) (by omega), hyx m hm,
        sub_self]
    · rw [hN' m hm]
      exact Submodule.mem_top
  obtain ⟨z, hz⟩ := GlobalTheory.T.artinian_limit_lift_of_compatible W S hA N y hNr hyr
  refine ⟨z, ?_⟩
  have h1 := hz n
  rw [hN n le_rfl, LinearMap.mem_ker, map_sub, Q.ρ_self, Q.ρ_self, sub_eq_zero] at h1
  have h2 := hyx n le_rfl
  rw [Q.ρ_self] at h2
  rw [← h2]
  exact h1

/- English proof (translation)
Introduce `W _ _ l S S' Q hA hF`. Take `⟨c, hc⟩` from `pow_torsion_bounded ((l : W)) S'.lim`. Use `⟨c, fun n x => lift_of_conn_zero Q hA n _ (fun a => ?_)⟩` and prove the remaining obligations. Establish `h0 : conn Q n ((l : W) ^ c • x) = 0`. Rewrite using `[← conn_smul]`.

Conclude with `hc n _ (conn_kill Q n x)`. Establish `h3` using `congrArg (fun v : S'.lim => (v : ∀ m, S'.M m) a) h0`. Simplify `h3` using `[conn]`.
-/
theorem lim_cokernel_bounded : ∀ (W : Type) [CommRing W] [IsNoetherianRing W] (l : ℕ) (S S' : Sys.{1} W)
    (_ : LSeq l S S'), (∀ n, IsArtinian W (S.M n)) → Module.Finite W S'.lim →
    ∃ c : ℕ, ∀ n (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x := by
  intro W _ _ l S S' Q hA hF
  obtain ⟨c, hc⟩ := pow_torsion_bounded ((l : W)) S'.lim
  refine ⟨c, fun n x => lift_of_conn_zero Q hA n _ (fun a => ?_)⟩
  have h0 : conn Q n ((l : W) ^ c • x) = 0 := by
    rw [← conn_smul]
    exact hc n _ (conn_kill Q n x)
  have h3 := congrArg (fun v : S'.lim => (v : ∀ m, S'.M m) a) h0
  simpa [conn] using h3

end GlobalTheory.CompanionTheory.TwCok
