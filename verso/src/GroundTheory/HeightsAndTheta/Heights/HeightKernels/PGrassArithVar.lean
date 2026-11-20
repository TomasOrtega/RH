import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace GrassmannianArithmeticVariety

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem det_submatrix_sign {R : Type*} [CommRing R] {j N : ℕ} (A : Matrix (Fin j) (Fin N) R)
    (g h : Fin j → Fin N) (hg : Function.Injective g) (hh : Function.Injective h)
    (hr : Set.range h = Set.range g) :
    ∃ s : ℤˣ, (A.submatrix id h).det = ((s : ℤ) : R) * (A.submatrix id g).det := by
  let σ : Equiv.Perm (Fin j) :=
    (Equiv.ofInjective h hh).trans ((Equiv.setCongr hr).trans (Equiv.ofInjective g hg).symm)
  have hσ : ∀ i, g (σ i) = h i := by
    intro i
    simp [σ, Equiv.apply_ofInjective_symm]
  refine ⟨Equiv.Perm.sign σ, ?_⟩
  have : A.submatrix id h = (A.submatrix id g).submatrix id σ := by
    ext r i; simp [hσ]
  rw [this, det_permute']

def col {j m : ℕ} (a : Fin j) (b : Fin m) (i : Fin j) : Fin (j + m) :=
  if i = a then Fin.natAdd j b else Fin.castAdd m i

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem col_injective {j m : ℕ} (a : Fin j) (b : Fin m) : Function.Injective (col a b) := by
  intro x y hxy
  simp only [col] at hxy
  split_ifs at hxy with h1 h2 h2
  · exact h1.trans h2.symm
  · rw [Fin.ext_iff] at hxy; simp at hxy; omega
  · rw [Fin.ext_iff] at hxy; simp at hxy; omega
  · rw [Fin.ext_iff] at hxy; exact Fin.ext (by simpa using hxy)

def idx {j m : ℕ} (a : Fin j) (b : Fin m) : PlIdx j m :=
  ⟨Finset.univ.map ⟨col a b, col_injective a b⟩, by simp⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

By extensionality, compare the relevant components. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression.
-/
theorem minor_idx {R : Type*} [CommRing R] {j m : ℕ} (Z : Matrix (Fin j) (Fin m) R)
    (a : Fin j) (b : Fin m) :
    ∃ s : ℤˣ, (colsOf (onePipe Z) (idx a b)).det = ((s : ℤ) : R) * Z a b := by
  obtain ⟨s, hs⟩ := det_submatrix_sign (onePipe Z) (col a b) _ (col_injective a b)
    ((idx a b).1.orderEmbOfFin (idx a b).2).injective (by
      rw [Finset.range_orderEmbOfFin]; simp [idx])
  refine ⟨s, ?_⟩
  have hcol : (onePipe Z).submatrix id (col a b) = (1 : Matrix (Fin j) (Fin j) R).updateCol a
      (fun r => Z r b) := by
    ext r i
    by_cases hi : i = a
    · simp [col, onePipe, hi]
    · simp [col, onePipe, hi]
  rw [colsOf, hs, hcol, ← cramer_apply, cramer_one]
  rfl

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem colsOf_anchor {R : Type*} [CommRing R] {j m : ℕ} (Z : Matrix (Fin j) (Fin m) R) :
    colsOf (onePipe Z) (plAnchor j m) = 1 := by
  have he : ((plAnchor j m).1.orderEmbOfFin (plAnchor j m).2 : Fin j → Fin (j + m)) =
      Fin.castAdd m :=
    (Finset.orderEmbOfFin_unique _ (fun x => by simp [plAnchor]) (Fin.strictMono_castAdd m)).symm
  ext r i
  simp [colsOf, onePipe, he]

end GrassmannianArithmeticVariety

open GrassmannianArithmeticVariety in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Separate the alternatives or extract the components of the hypothesis. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem GrassArithVar.proof (h : CoordConeArithVar.Statement) : GrassArithVar.Statement := by
  intro f j m hf
  let e : Fin (f * j * m) ≃ Fin f × Fin j × Fin m :=
    finProdFinEquiv.symm.trans
      ((finProdFinEquiv.symm.prodCongr (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _))
  let φ := IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin f × Fin j × Fin m) ℚ) (GrassField f j m)
  let t : Fin (f * j * m) → GrassField f j m := fun i => φ (X (e i))
  have anchor : ∀ τ, grassCoord f j m ⟨τ, plAnchor j m⟩ = 1 := by
    intro τ
    have hp : grassPolyCoord f j m ⟨τ, plAnchor j m⟩ = 1 :=
      (congrArg Matrix.det (colsOf_anchor _)).trans det_one
    rw [grassCoord, hp, map_one]
  have hmem : ∀ q : MvPolynomial (Fin f × Fin j × Fin m) ℚ,
      algebraMap _ (GrassField f j m) q ∈ IntermediateField.adjoin ℚ (Set.range t) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact IntermediateField.algebraMap_mem _ c
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact mul_mem hp (IntermediateField.subset_adjoin _ _ ⟨e.symm i, by simp [t, φ]⟩)
  refine h (Fin f) (plBlocks f j m) (GrassField f j m) (grassCoord f j m) (fun _ => plAnchor j m)
    (f * j * m) t ⟨⟨0, hf⟩⟩ (fun τ => by rw [anchor]; exact one_ne_zero) ?_ ?_ ?_
  · exact ((MvPolynomial.algebraicIndependent_X _ ℚ).map' (f := φ)
      (IsFractionRing.injective _ _)).comp e e.injective
  · intro i
    rcases hi : e i with ⟨τ, a, b⟩
    obtain ⟨s, hs⟩ : ∃ s : ℤˣ, grassPolyCoord f j m ⟨τ, idx a b⟩ =
        ((s : ℤ) : MvPolynomial (Fin f × Fin j × Fin m) ℚ) * X (τ, a, b) :=
      minor_idx _ a b
    have hr : grassCoord f j m ⟨τ, idx a b⟩ / grassCoord f j m ⟨τ, plAnchor j m⟩ ∈
        IntermediateField.adjoin ℚ (coneRatios (grassCoord f j m) fun _ => plAnchor j m) :=
      IntermediateField.subset_adjoin _ _ ⟨⟨τ, idx a b⟩, rfl⟩
    have hy : grassCoord f j m ⟨τ, idx a b⟩ = ((s : ℤ) : GrassField f j m) * t i := by
      rw [grassCoord, hs, map_mul, map_intCast]
      simp [t, φ, hi]
    rw [anchor, div_one, hy] at hr
    rcases Int.units_eq_one_or s with rfl | rfl
    · simpa using hr
    · simpa using neg_mem hr
  · rintro r ⟨⟨τ, I⟩, rfl⟩
    have hr : grassCoord f j m ⟨τ, I⟩ / grassCoord f j m ⟨τ, plAnchor j m⟩ ∈
        IntermediateField.adjoin ℚ (Set.range t) := by
      rw [anchor, div_one]; exact hmem _
    exact isAlgebraic_algebraMap (R := IntermediateField.adjoin ℚ (Set.range t))
      (A := GrassField f j m) ⟨_, hr⟩

end

end GroundTheory.Heights₂.Heights
