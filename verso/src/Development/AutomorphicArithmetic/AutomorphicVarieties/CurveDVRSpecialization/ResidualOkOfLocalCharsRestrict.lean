import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CrDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ResidualDatumInertiaCharactersTrivial

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

section
open Polynomial UpperTheory.V.W

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem chi_ofRep' {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A)
    (y : MonoidAlgebra A G) : (GDet.ofRep ρ).chi y =
      (Matrix.scalar (Fin n) X - GDet.repAlg ρ A[X] (MonoidAlgebra.mapRingHom G C y)).det := by
  show Matrix.det (GDet.repAlg ρ A[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)) = _
  rw [map_sub]
  congr 2
  simp [GDet.repAlg, MonoidAlgebra.lift_single, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
private theorem prod_diagonal {n : ℕ} {A : Type} [CommRing A] (L : List (Fin n → A)) :
    (L.map Matrix.diagonal).prod = Matrix.diagonal L.prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, ih, List.prod_cons, Matrix.diagonal_mul_diagonal]
    rfl

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem rep_oEl {l : ℕ} [Fact l.Prime] {G : GFrame l} {k : Type} [CommRing k] {n : ℕ}
    (χ : Fin n → G.G₀ →* kˣ) (v : G.Vl) (ψ : Fin n → G.Gv v →* kˣ) (h : ∀ i g, ψ i g = χ i (G.φ v g))
    (g : Fin n → G.Gv v) :
    GDet.repAlg (diagRep χ) k[X] (MonoidAlgebra.mapRingHom _ C (G.oEl v ψ g)) = 0 := by
  have hf : ∀ i, GDet.repAlg (diagRep χ) k[X] (MonoidAlgebra.mapRingHom _ C
      (MonoidAlgebra.single (G.φ v (g i)) 1 - MonoidAlgebra.single 1 ((ψ i (g i) : kˣ) : k))) =
      Matrix.diagonal (fun j => C ((χ j (G.φ v (g i)) : kˣ) : k) - C ((ψ i (g i) : kˣ) : k)) := by
    intro i
    simp [GDet.repAlg, MonoidAlgebra.lift_single, diagRep, Matrix.smul_one_eq_diagonal,
      Matrix.diagonal_sub]
  unfold GFrame.oEl
  rw [map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
  simp only [Function.comp_def, hf]
  have key : (List.ofFn fun i => Matrix.diagonal
      (fun j => C ((χ j (G.φ v (g i)) : kˣ) : k) - C ((ψ i (g i) : kˣ) : k))) =
      (List.ofFn fun i j => C ((χ j (G.φ v (g i)) : kˣ) : k) - C ((ψ i (g i) : kˣ) : k)).map
        Matrix.diagonal := by
    rw [List.map_ofFn]
    rfl
  rw [key, prod_diagonal]
  have hz : (List.ofFn fun i j => C ((χ j (G.φ v (g i)) : kˣ) : k) - C ((ψ i (g i) : kˣ) : k)).prod
      = 0 := by
    funext j
    rw [List.prod_ofFn, Finset.prod_apply]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [h]
  rw [hz]
  exact Matrix.diagonal_zero

end

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.residual_ok_of_local_chars_restrict :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [CharP (ResidueField O) l]
      {G : W.GFrame l} {n : ℕ} (r : W.Resid G O n), 1 ≤ n →
      (∀ v i g, r.psib v i g = r.chib i (G.φ v g)) → r.Ok := by
  intro l _ O _ _ _ _ G n r hn hps
  refine ⟨fun v g h => ?_, fun v i g => ?_⟩
  · simp only [W.Resid.Dbar, W.GDet.tr, W.GDet.lam]
    rw [chi_ofRep', map_mul, map_mul, rep_oEl r.chib v (r.psib v) (hps v) g, mul_zero, sub_zero,
      Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
  · rw [(W.residualDatum_inertia_characters_trivial l G O n r v i g).1, (W.residualDatum_inertia_characters_trivial l G O n r v i g).2]
