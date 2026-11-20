import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SubstSub

/- English proof (translation)
Introduce `B Q _ _ _ σ τ _ S f u hu hf β`. Establish `hc : ∀ i, constantCoeff (up Q u i) = 0` using `fun i => by`. Simplify using `only [up]`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hu, map_zero]`. Establish `ha : HasSubst (up Q u)` using `hasSubst_of_constantCoeff_zero hc`.

Rewrite using `[coeff_subst ha]`. Use `finsum_induction (fun x => x ∈ S) S.zero_mem (fun x y hx hy => S.add_mem hx hy) ?_` and prove the remaining obligations. Introduce `d`. Establish `hp : (d.prod fun s e => (up Q u s) ^ e) = map (algebraMap B Q) (d.prod fun s e => (u s) ^ e)`. Simplify using `only [up, Finsupp.prod, map_prod, map_pow]`.

Simplify using `only [hp, coeff_map, smul_eq_mul]`. Rewrite using `[mul_comm, ← Algebra.smul_def]`. Conclude with `S.smul_mem _ (hf d)`.
-/
theorem coeff_subst_up_mem : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (σ τ : Type) [Fintype σ] (S : Submodule B Q) (f : MvPowerSeries σ Q) (u : σ → MvPowerSeries τ B), (∀ i, constantCoeff (u i) = 0) → (∀ α, coeff α f ∈ S) → ∀ β, coeff β (subst (up Q u) f) ∈ S := by
  intro B Q _ _ _ σ τ _ S f u hu hf β
  have hc : ∀ i, constantCoeff (up Q u i) = 0 := fun i => by
    simp only [up]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hu, map_zero]
  have ha : HasSubst (up Q u) := hasSubst_of_constantCoeff_zero hc
  rw [coeff_subst ha]
  refine finsum_induction (fun x => x ∈ S) S.zero_mem (fun x y hx hy => S.add_mem hx hy) ?_
  intro d
  have hp : (d.prod fun s e => (up Q u s) ^ e) = map (algebraMap B Q) (d.prod fun s e => (u s) ^ e) := by
    simp only [up, Finsupp.prod, map_prod, map_pow]
  simp only [hp, coeff_map, smul_eq_mul]
  rw [mul_comm, ← Algebra.smul_def]
  exact S.smul_mem _ (hf d)

end GlobalTheory.SubstSub
