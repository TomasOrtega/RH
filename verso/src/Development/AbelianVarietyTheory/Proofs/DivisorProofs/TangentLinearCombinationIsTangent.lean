import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop

noncomputable section

namespace GlobalTheory.SecJet.TanComb

variable {R : Type} [CommRing R]

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem zeroPt_w : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (epsR R).hom = (𝟙_ (Over (Sp R))).hom := by
  show spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [← Spec.map_id]
  congr 1

def zeroPt : 𝟙_ (Over (Sp R)) ⟶ epsR R :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) zeroPt_w

variable {G : Over (Sp R)} [GrpObj G]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts.
-/
theorem isTangent_iff (v : epsR R ⟶ G) : IsTangent v ↔ zeroPt ≫ v = 1 := by
  have h1 : (1 : 𝟙_ (Over (Sp R)) ⟶ G) = η[G] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  rw [h1, IsTangent]
  constructor
  · intro h
    apply Over.OverMorphism.ext
    simpa [zeroPt] using h
  · intro h
    simpa [zeroPt] using congrArg (fun q => q.left) h

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem zeroPt_epsScale (c : R) : zeroPt ≫ epsScale R c = zeroPt := by
  apply Over.OverMorphism.ext
  show spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (epsScaleR c) = spMap (TrivSqZeroExt.fstHom R R R).toRingHom
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro r
  simp [epsScaleR]

/- English proof (translation)
Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities.
-/
theorem zeroPt_prod (l : List (epsR R ⟶ G)) (hl : ∀ x ∈ l, zeroPt ≫ x = 1) : zeroPt ≫ l.prod = 1 := by
  induction l with
  | nil =>
    rw [List.prod_nil, Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (zeroPt ≫ toUnit _) (toUnit _)]
  | cons a l ih =>
    rw [List.prod_cons, MonObj.comp_mul, hl a (List.mem_cons_self ..), ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)), _root_.mul_one]

end GlobalTheory.SecJet.TanComb

namespace GlobalTheory.SecJet

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isTangent_tanComb (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (m : ℕ) (v : Fin m → (epsR R ⟶ G))
    (c : Fin m → R) : (∀ i, IsTangent (v i)) → IsTangent (tanComb c v) := by
  intro hv
  rw [TanComb.isTangent_iff, tanComb]
  refine TanComb.zeroPt_prod _ fun x hx => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  rw [← Category.assoc, TanComb.zeroPt_epsScale, ← TanComb.isTangent_iff]
  exact hv i

end GlobalTheory.SecJet
