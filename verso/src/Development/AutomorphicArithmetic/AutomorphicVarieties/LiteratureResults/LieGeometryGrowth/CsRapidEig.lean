import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
open UpperTheory.V.Lit.Geo.Cs
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
private theorem one_comm (X : Lie E a) (φ : Sm E a) :
    lie E a (oneL E a) (lie E a X φ) = lie E a X (lie E a (oneL E a) φ) := by
  have h := lie_comm (oneL E a) X
  have e : Matrix.of (oneL E a) * Matrix.of X = Matrix.of X * Matrix.of (oneL E a) :=
    (one_mul (Matrix.of X)).trans (mul_one (Matrix.of X)).symm
  rw [e, sub_self, sub_eq_zero] at h
  exact LinearMap.congr_fun h φ

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
private theorem eig_prod (c : ℂ) (φ : Sm E a) (h : lie E a (oneL E a) φ = c • φ) (l : List (Lie E a)) :
    lie E a (oneL E a) ((l.map (lie E a)).prod φ) = c • (l.map (lie E a)).prod φ := by
  induction l with
  | nil => simpa using h
  | cons X l ih => rw [List.map_cons, List.prod_cons, Module.End.mul_apply, one_comm, ih, map_smul]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.
-/
private theorem cmp_rTensor {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (j : Fin d) (T : Module.End ℂ W)
    (m : W ⊗[ℂ] (Fin d → ℂ)) : Bor.cmp j (T.rTensor _ m) = T (Bor.cmp j m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul φ v => rw [LinearMap.rTensor_tmul, cmp_tmul, cmp_tmul, map_smul]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.
-/
private theorem cmp_prod (Ξ : AlgRep E a) (j : Fin Ξ.d) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) (l : List (Lie E a)) :
    Bor.cmp j ((l.map (smA Ξ)).prod m) = (l.map (lie E a)).prod (Bor.cmp j m) := by
  induction l with
  | nil => simp
  | cons X l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, smA_apply, cmp_rTensor, ih, List.map_cons, List.prod_cons,
      Module.End.mul_apply]

/- English proof (translation)
Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Treat this case separately.

Treat this case separately. Rewrite the conclusion using the stated equalities.
-/
private theorem ev_eq {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) (g : GA E a) : ev m g j = (Bor.cmp j m).1 g := by
  induction m using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero]
    rfl
  | tmul φ v => simp [mul_comm]
  | add x y hx hy =>
    rw [map_add, map_add, Pi.add_apply, Pi.add_apply, Submodule.coe_add, Pi.add_apply, hx, hy]

end

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Lit.Geo.Cs.rapidEig :
    RapidEig := by
  intro E _ _ _ a U Ξ r hr q α hα X j l
  refine ⟨eig_prod _ _ ?_ l, fun g => by rw [ev_eq, cmp_prod]⟩
  have h : Bor.cmp j (α X) ∈ LinearMap.eqLocus (lie E a (oneL E a)) (-(r : ℂ) • LinearMap.id) :=
    mem_tens.1 (span_le_tens (fun φ hφ => hφ.2.2 _ hr) (hα.val X)) j
  exact h
