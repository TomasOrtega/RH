import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

/- English proof (translation)
Introduce `V _ _ _ _`. Use `IsAlgClosed.of_exists_root _ ?_` and prove the remaining obligations. Introduce `p hm hirr`. Establish `hsurj : Function.Surjective (IsLocalRing.residue V)` using `IsLocalRing.residue_surjective`. Establish `hl : p ∈ Polynomial.lifts (IsLocalRing.residue V)` using `Polynomial.mem_lifts _ |>.2 (Polynomial.map_surjective _ hsurj p)`.

Take `⟨P, hP, hdeg, hPm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hl hm`. Establish `hinj : Function.Injective (algebraMap V (FractionRing V))` using `IsFractionRing.injective V (FractionRing V)`. Establish `hpos : 0 < P.natDegree` using `hdeg ▸ hirr.natDegree_pos`. Establish `hd : (P.map (algebraMap V (FractionRing V))).degree ≠ 0`. Rewrite using `[Polynomial.degree_map_eq_of_injective hinj]`.

Conclude with `(Polynomial.natDegree_pos_iff_degree_pos.1 hpos).ne'`. Take `⟨x, hx⟩` from `IsAlgClosed.exists_root _ hd`. Establish `hint : IsIntegral V x`. Use `⟨P, hPm, ?_⟩` and prove the remaining obligations. Simplify `hx` using `[Polynomial.IsRoot.def, Polynomial.eval_map]`.

Take `⟨y, rfl⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hint`. Establish `hy : P.eval y = 0`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]`. Conclude with `hx`.

Use `⟨IsLocalRing.residue V y, ?_⟩` and prove the remaining obligations. Rewrite using `[← hP, Polynomial.eval_map, Polynomial.eval₂_at_apply, hy, map_zero]`.
-/
theorem UpperTheory.Gal.crystallineComparison.Mod.resClosed_of :
    ResClosed := by
  intro V _ _ _ _
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hm hirr
  have hsurj : Function.Surjective (IsLocalRing.residue V) := IsLocalRing.residue_surjective
  have hl : p ∈ Polynomial.lifts (IsLocalRing.residue V) :=
    Polynomial.mem_lifts _ |>.2 (Polynomial.map_surjective _ hsurj p)
  obtain ⟨P, hP, hdeg, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hm
  have hinj : Function.Injective (algebraMap V (FractionRing V)) :=
    IsFractionRing.injective V (FractionRing V)
  have hpos : 0 < P.natDegree := hdeg ▸ hirr.natDegree_pos
  have hd : (P.map (algebraMap V (FractionRing V))).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective hinj]
    exact (Polynomial.natDegree_pos_iff_degree_pos.1 hpos).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd
  have hint : IsIntegral V x := by
    refine ⟨P, hPm, ?_⟩
    simpa [Polynomial.IsRoot.def, Polynomial.eval_map] using hx
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hy : P.eval y = 0 := by
    apply hinj
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
    exact hx
  refine ⟨IsLocalRing.residue V y, ?_⟩
  rw [← hP, Polynomial.eval_map, Polynomial.eval₂_at_apply, hy, map_zero]
