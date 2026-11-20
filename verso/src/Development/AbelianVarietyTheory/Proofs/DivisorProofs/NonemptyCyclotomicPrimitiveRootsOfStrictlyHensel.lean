import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

open Polynomial in

/- English proof (translation)
Introduce `q A _ hSH hq`. Take `⟨hH, hsep⟩` from `hSH`. Set `k` to `IsLocalRing.ResidueField A`. Establish `hqk : IsUnit ((q : ℕ) : k)`. Use `hq.map (IsLocalRing.residue A)` as an intermediate fact.

Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Use `haveI : NeZero ((q : ℕ) : k) := ⟨hqk.ne_zero⟩`. Establish `hq0 : 0 < q`. Break down `Nat.eq_zero_or_pos q with h | h` into its components or cases. Substitute `h` using the available equality.

Simplify using `at hqk`. Conclude with `h`. Establish `hsepk : (cyclotomic q k).Separable` using `separable_cyclotomic q k`. Take `⟨a₀, ha₀⟩` from `IsSepClosed.exists_root (cyclotomic q k) (degree_cyclotomic_pos q k hq0).ne' hsepk`. Establish `hmap : (cyclotomic q A).map (algebraMap A k) = cyclotomic q k` using `map_cyclotomic q _`.

Establish `h1 : aeval a₀ (cyclotomic q A) = 0`. Rewrite using `[aeval_def, eval₂_eq_eval_map, hmap]`. Conclude with `ha₀`. Establish `h2 : aeval a₀ (derivative (cyclotomic q A)) ≠ 0`. Rewrite using `[aeval_def, eval₂_eq_eval_map, ← derivative_map, hmap]`.

Use `hsepk.aeval_derivative_ne_zero (x := a₀) (by simpa [aeval_def] using ha₀)` as an intermediate fact. Simplify `this` using `[aeval_def]`. Establish `hT` using `(HenselianLocalRing.TFAE A).out 0 1`. Take `⟨a, ha, -⟩` from `hT.mp hH (cyclotomic q A) (cyclotomic.monic q A) a₀ h1 h2`. Use `⟨⟨a, hq, ?_⟩⟩` and prove the remaining obligations.

Establish `: (cyclotomic q ℤ).map (Int.castRingHom A) = cyclotomic q A` using `map_cyclotomic q _`. Rewrite using `[aeval_def, eval₂_eq_eval_map, algebraMap_int_eq, this]`. Conclude with `ha`.
-/
theorem prim_of_strictlyHenselian : ∀ (q : ℕ) (A : Type) [CommRing A], SH A → IsUnit (q : A) → Nonempty (Prim q A) := by
  intro q A _ hSH hq
  obtain ⟨hH, hsep⟩ := hSH
  let k := IsLocalRing.ResidueField A
  have hqk : IsUnit ((q : ℕ) : k) := by
    have := hq.map (IsLocalRing.residue A)
    rwa [map_natCast] at this
  haveI : NeZero ((q : ℕ) : k) := ⟨hqk.ne_zero⟩
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp at hqk
    · exact h
  have hsepk : (cyclotomic q k).Separable := separable_cyclotomic q k
  obtain ⟨a₀, ha₀⟩ := IsSepClosed.exists_root (cyclotomic q k)
    (degree_cyclotomic_pos q k hq0).ne' hsepk
  have hmap : (cyclotomic q A).map (algebraMap A k) = cyclotomic q k := map_cyclotomic q _
  have h1 : aeval a₀ (cyclotomic q A) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, hmap]; exact ha₀
  have h2 : aeval a₀ (derivative (cyclotomic q A)) ≠ 0 := by
    rw [aeval_def, eval₂_eq_eval_map, ← derivative_map, hmap]
    have := hsepk.aeval_derivative_ne_zero (x := a₀) (by simpa [aeval_def] using ha₀)
    simpa [aeval_def] using this
  have hT := (HenselianLocalRing.TFAE A).out 0 1
  obtain ⟨a, ha, -⟩ := hT.mp hH (cyclotomic q A) (cyclotomic.monic q A) a₀ h1 h2
  refine ⟨⟨a, hq, ?_⟩⟩
  have : (cyclotomic q ℤ).map (Int.castRingHom A) = cyclotomic q A := map_cyclotomic q _
  rw [aeval_def, eval₂_eq_eval_map, algebraMap_int_eq, this]
  exact ha

end GlobalTheory.EtC
