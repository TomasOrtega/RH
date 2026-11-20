import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob Matrix

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. A detailed English derivation is pending.
-/
private lemma star_mulVec_fin_three {L : Type} [CommRing L] [StarRing L] (N : Matrix (Fin 3) (Fin 3) L) (v : Fin 3 → L) :
    star (N *ᵥ v) = N.map star *ᵥ star v := by
  funext i
  have h := RingHom.map_mulVec (starRingEnd L) N v i
  exact h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.semilinear_coords_eq_mulVec_star :
    ∀ (K : Type) [Field K] (Δ τ : K) (d : EL Δ τ) (A N : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (e v : Fin 3 → Lsq K Δ),
        A * N.map star = N * A → A *ᵥ star e = e → A *ᵥ star v = d.re • v + d.im • (N *ᵥ v) →
        N *ᵥ (N *ᵥ v) = algebraMap K (Lsq K Δ) τ • (N *ᵥ v) - v → ∀ x : Sp Δ τ,
        (semi d x).1 • e + (semi d x).2.re • v + (semi d x).2.im • (N *ᵥ v) = A *ᵥ star (x.1 • e + x.2.re • v + x.2.im • (N *ᵥ v)) := by
  intro K _ Δ τ d A N e v hAN he hv hN x
  have hNv : A *ᵥ star (N *ᵥ v) = d.re • (N *ᵥ v) + d.im • (algebraMap K (Lsq K Δ) τ • (N *ᵥ v) - v) := by
    rw [star_mulVec_fin_three, Matrix.mulVec_mulVec, hAN, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul, hN]
  have hs : star (x.1 • e + x.2.re • v + x.2.im • (N *ᵥ v)) =
      star x.1 • star e + star x.2.re • star v + star x.2.im • star (N *ᵥ v) := by
    funext i
    simp [mul_comm]
  rw [hs, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, he, hv, hNv]
  funext i
  simp only [semi, sigL, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  simp
  ring
