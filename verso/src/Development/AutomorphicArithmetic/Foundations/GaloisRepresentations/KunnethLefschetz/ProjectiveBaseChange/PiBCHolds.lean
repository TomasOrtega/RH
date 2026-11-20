import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.AdicTopOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Both sides reduce to the same expression. Treat this case separately. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
