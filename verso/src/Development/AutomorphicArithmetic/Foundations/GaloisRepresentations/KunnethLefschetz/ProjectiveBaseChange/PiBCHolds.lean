import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.AdicTopOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

/- English proof (translation)
Introduce `l _ r A B _ _ _ _ f hf`. Set `e` to `LinearEquiv.ofBijective (LinearMap.pi f) hf`. Set `g` to `(LinearEquiv.baseChange ℤ_[l] ℚ_[l] A (∀ s, B s) e).trans (TensorProduct.piRight ℤ_[l] ℚ_[l] ℚ_[l] B)`. Establish `key : (fun x s => (LinearMap.baseChange ℚ_[l] (f s)) x) = g`. Use function extensionality and compare the values at `x`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => funext s`. Simplify using the standard rewrite rules. Consider the case `tmul a b`. Use function extensionality and compare the values at `s`.

Simplify using `[g, e]`. Both sides reduce to the same expression. Consider the case `add x y hx hy`. Rewrite using `[map_add, ← hx, ← hy]`. Use function extensionality and compare the values at `s`.

Simplify using the standard rewrite rules. Rewrite using `[key]`. Conclude with `g.bijective`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.piBC_holds :
    UpperTheory.Gal.KunnethLefschetz.PiBC := by
  intro l _ r A B _ _ _ _ f hf
  classical
  let e := LinearEquiv.ofBijective (LinearMap.pi f) hf
  let g := (LinearEquiv.baseChange ℤ_[l] ℚ_[l] A (∀ s, B s) e).trans
    (TensorProduct.piRight ℤ_[l] ℚ_[l] ℚ_[l] B)
  have key : (fun x s => (LinearMap.baseChange ℚ_[l] (f s)) x) = g := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => funext s; simp
    | tmul a b =>
      funext s
      simp [g, e]
      rfl
    | add x y hx hy =>
      rw [map_add, ← hx, ← hy]
      funext s
      simp
  rw [key]
  exact g.bijective
