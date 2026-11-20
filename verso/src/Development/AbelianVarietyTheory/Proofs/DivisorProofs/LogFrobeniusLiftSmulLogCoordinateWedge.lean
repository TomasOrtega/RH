import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ p n x γ hγ c I`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul, hγ.1]`. Use `congr 1`. Unfold `logWedge`. Rewrite using `[map_list_prod, List.map_map]`.

Use `congr 1`. Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `i _`. Conclude with `hγ.2 i`.
-/
theorem cartierMap_smul_logWedge : ∀ (K : Type) [Field K] (p : ℕ) (n : ℕ) (x : Fin n → Kˣ) (γ : abelian₂ K →+* abelian₂ K),
    IsCartierMap p x γ → ∀ (c : K) (I : Finset (Fin n)), γ (c • logWedge x I) = c ^ p • logWedge x I := by
  intro K _ p n x γ hγ c I
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, hγ.1]
  congr 1
  unfold logWedge
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact hγ.2 i

end GlobalTheory
