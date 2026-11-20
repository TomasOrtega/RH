import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.LineUnitBunF

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

/- English proof (translation)
Substitute `hn hi` using the available equality. Both sides reduce to the same expression.
-/
private theorem cohomology_cast_zsmul {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (c : ℤ)
    (x : Ht q E n i) : Ht.cast hn hi (c • x) = c • Ht.cast hn hi x := by
  subst hn hi
  rfl

/- English proof (translation)
Introduce `q E y m j`. Proceed by induction on `j with`. Consider the case `zero`. Rewrite using `[cpow_zero, cpow_zero, pow_zero, one_smul]`. Consider the case `succ k ih`.

Rewrite using `[cpow_succ, cpow_succ, ih, map_zsmul, map_zsmul, AddMonoidHom.zsmul_apply, smul_smul, ← pow_succ', cohomology_cast_zsmul]`.
-/
theorem UpperTheory.chernPower_zsmul_eq_pow_smul :
    ∀ (q : ℕ) {E : Spc} (y : Ht q E 2 1) (m : ℤ) (j : ℕ), cpow q (m • y) j = (m ^ j) • cpow q y j := by
  intro q E y m j
  induction j with
  | zero =>
    rw [cpow_zero, cpow_zero, pow_zero, one_smul]
  | succ k ih =>
    rw [cpow_succ, cpow_succ, ih, map_zsmul, map_zsmul, AddMonoidHom.zsmul_apply, smul_smul,
      ← pow_succ', cohomology_cast_zsmul]
