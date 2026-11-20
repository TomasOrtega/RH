import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

/- English proof (translation)
Use `haveI : NeZero (A.m * B.m) := ⟨(Nat.mul_pos A.pos B.pos).ne'⟩`. Establish `h1` using `A.H.index_comap_of_surjective (ZMod.unitsMap_surjective (dvd_mul_right A.m B.m))`. Establish `h2` using `B.H.index_comap_of_surjective (ZMod.unitsMap_surjective (dvd_mul_left B.m A.m))`. Unfold `AbF.deg`. Rewrite using `[← h1, ← h2]`.

Conclude with `Subgroup.index_inf_le`.
-/
private theorem UpperTheory.V.Two.deg_sup_le (A B : AbF) : (A.sup B).deg ≤ A.deg * B.deg := by
  haveI : NeZero (A.m * B.m) := ⟨(Nat.mul_pos A.pos B.pos).ne'⟩
  have h1 := A.H.index_comap_of_surjective (ZMod.unitsMap_surjective (dvd_mul_right A.m B.m))
  have h2 := B.H.index_comap_of_surjective (ZMod.unitsMap_surjective (dvd_mul_left B.m A.m))
  unfold AbF.deg
  rw [← h1, ← h2]
  exact Subgroup.index_inf_le

/- English proof (translation)
Use `show (⊥ : Subgroup (ZMod 4)ˣ).index = 2`. Rewrite using `[Subgroup.index_bot, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]`. Evaluate the decidable proposition.
-/
private theorem UpperTheory.V.Two.deg_cyc_four : (AbF.cyc 4).deg = 2 := by
  show (⊥ : Subgroup (ZMod 4)ˣ).index = 2
  rw [Subgroup.index_bot, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  decide

/- English proof (translation)
Use `show ((powMonoidHom 2 : (ZMod (max p 1))ˣ →* _).range).index ∣ 2`. Establish `hp' : (max p 1).Prime` using `by rwa [max_eq_left hp.pos]`. Use `haveI := Fact.mk hp'`. Rewrite using `[IsCyclic.index_powMonoidHom_range]`. Conclude with `Nat.gcd_dvd_right _ _`.
-/
private theorem UpperTheory.V.Two.deg_quad_dvd (p : ℕ) (hp : p.Prime) : (AbF.quad p).deg ∣ 2 := by
  show ((powMonoidHom 2 : (ZMod (max p 1))ˣ →* _).range).index ∣ 2
  have hp' : (max p 1).Prime := by rwa [max_eq_left hp.pos]
  haveI := Fact.mk hp'
  rw [IsCyclic.index_powMonoidHom_range]
  exact Nat.gcd_dvd_right _ _

/- English proof (translation)
Use `⟨deg_sup_le, deg_cyc_four, deg_quad_dvd, fun M q d hq hd => ?_⟩` and prove the remaining obligations. Establish `h1 : (withI M).deg ≤ M.deg * 2` using `deg_cyc_four ▸ deg_sup_le M (AbF.cyc 4)`. Establish `hq2` using `Nat.le_of_dvd two_pos (deg_quad_dvd q hq)`. Establish `hd2` using `Nat.le_of_dvd two_pos (deg_quad_dvd d hd)`. Combine the equalities or inequalities in the displayed calculation.
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
