import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem UpperTheory.V.Two.deg_sup_le (A B : AbF) : (A.sup B).deg ≤ A.deg * B.deg := by
  haveI : NeZero (A.m * B.m) := ⟨(Nat.mul_pos A.pos B.pos).ne'⟩
  have h1 := A.H.index_comap_of_surjective (ZMod.unitsMap_surjective (dvd_mul_right A.m B.m))
  have h2 := B.H.index_comap_of_surjective (ZMod.unitsMap_surjective (dvd_mul_left B.m A.m))
  unfold AbF.deg
  rw [← h1, ← h2]
  exact Subgroup.index_inf_le

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Evaluate the decidable proposition. A detailed English derivation is pending.
-/
private theorem UpperTheory.V.Two.deg_cyc_four : (AbF.cyc 4).deg = 2 := by
  show (⊥ : Subgroup (ZMod 4)ˣ).index = 2
  rw [Subgroup.index_bot, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  decide

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem UpperTheory.V.Two.deg_quad_dvd (p : ℕ) (hp : p.Prime) : (AbF.quad p).deg ∣ 2 := by
  show ((powMonoidHom 2 : (ZMod (max p 1))ˣ →* _).range).index ∣ 2
  have hp' : (max p 1).Prime := by rwa [max_eq_left hp.pos]
  haveI := Fact.mk hp'
  rw [IsCyclic.index_powMonoidHom_range]
  exact Nat.gcd_dvd_right _ _

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation.
-/
theorem UpperTheory.V.Two.degBasic :
    (∀ A B : AbF, (A.sup B).deg ≤ A.deg * B.deg) ∧ (AbF.cyc 4).deg = 2 ∧ (∀ p : ℕ, p.Prime → (AbF.quad p).deg ∣ 2) ∧ ∀ (M : AbF) (q d : ℕ), q.Prime → d.Prime → (base2 M q d).deg ≤ 8 * M.deg := by
  refine ⟨deg_sup_le, deg_cyc_four, deg_quad_dvd, fun M q d hq hd => ?_⟩
  have h1 : (withI M).deg ≤ M.deg * 2 := deg_cyc_four ▸ deg_sup_le M (AbF.cyc 4)
  have hq2 := Nat.le_of_dvd two_pos (deg_quad_dvd q hq)
  have hd2 := Nat.le_of_dvd two_pos (deg_quad_dvd d hd)
  calc (base2 M q d).deg ≤ ((withI M).sup (AbF.quad q)).deg * (AbF.quad d).deg := deg_sup_le _ _
    _ ≤ ((withI M).deg * (AbF.quad q).deg) * 2 := Nat.mul_le_mul (deg_sup_le _ _) hd2
    _ ≤ (M.deg * 2 * 2) * 2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul h1 hq2)
    _ = 8 * M.deg := by ring
