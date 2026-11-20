import Mathlib

/- English proof (translation)
Introduce `Ω _ _ A`. Use `IsAlgClosed.of_exists_root _ fun p hp hirr => ?_` and prove the remaining obligations. Establish `hsurj : Function.Surjective (IsLocalRing.residue A)` using `IsLocalRing.residue_surjective`. Establish `hl : p ∈ Polynomial.lifts (IsLocalRing.residue A)` using `(Polynomial.mem_lifts _).2 (Polynomial.map_surjective _ hsurj p)`. Take `⟨q, hq, hdeg, hm⟩` from `Polynomial.lifts_and_degree_eq_and_monic hl hp`.

Establish `hd : q.degree ≠ 0`. Rewrite using `[hdeg]`. Conclude with `(Polynomial.degree_pos_of_irreducible hirr).ne'`. Establish `hinj : Function.Injective (algebraMap A Ω)` using `Subtype.val_injective`. Establish `hd' : (q.map (algebraMap A Ω)).degree ≠ 0`.

Rewrite using `[hm.degree_map]` and apply the resulting hypothesis. Take `⟨x, hx⟩` from `IsAlgClosed.exists_root _ hd'`. Establish `hx' : Polynomial.eval₂ (algebraMap A Ω) x q = 0`. Rewrite using `[← Polynomial.eval_map]`. Conclude with `hx`.

Establish `hint : IsIntegral A x` using `⟨q, hm, hx'⟩`. Take `⟨y, rfl⟩` from `IsIntegrallyClosed.algebraMap_eq_of_integral hint`. Establish `hy : q.eval y = 0`. Apply `hinj` to reduce the goal to its premises. Rewrite `hx'` using `[Polynomial.eval₂_at_apply]`.

Rewrite using `[hx', map_zero]`. Use `⟨IsLocalRing.residue A y, ?_⟩` and prove the remaining obligations. Rewrite using `[← hq, Polynomial.eval_map, Polynomial.eval₂_at_apply, hy, map_zero]`.
-/
theorem UpperTheory.Reformulated.B.Qk69.res_algClosed :
    ∀ {Ω : Type} [inst : Field Ω] [IsAlgClosed Ω]
    (A : ValuationSubring Ω), IsAlgClosed (IsLocalRing.ResidueField ↥A) := by
  intro Ω _ _ A
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hsurj : Function.Surjective (IsLocalRing.residue A) := IsLocalRing.residue_surjective
  have hl : p ∈ Polynomial.lifts (IsLocalRing.residue A) :=
    (Polynomial.mem_lifts _).2 (Polynomial.map_surjective _ hsurj p)
  obtain ⟨q, hq, hdeg, hm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hp
  have hd : q.degree ≠ 0 := by
    rw [hdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  have hinj : Function.Injective (algebraMap A Ω) := Subtype.val_injective
  have hd' : (q.map (algebraMap A Ω)).degree ≠ 0 := by
    rwa [hm.degree_map]
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd'
  have hx' : Polynomial.eval₂ (algebraMap A Ω) x q = 0 := by
    rw [← Polynomial.eval_map]
    exact hx
  have hint : IsIntegral A x := ⟨q, hm, hx'⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hy : q.eval y = 0 := by
    apply hinj
    rw [Polynomial.eval₂_at_apply] at hx'
    rw [hx', map_zero]
  refine ⟨IsLocalRing.residue A y, ?_⟩
  rw [← hq, Polynomial.eval_map, Polynomial.eval₂_at_apply, hy, map_zero]
