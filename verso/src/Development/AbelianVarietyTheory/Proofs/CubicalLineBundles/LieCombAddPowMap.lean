import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section

namespace GlobalTheory.LieCombHom

variable {R : Type} [CommRing R] {G G' : Over (Sp R)} [GrpObj G] [GrpObj G'] {n : ℕ}
  {v : Fin n → (epsR R ⟶ G)}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isLieComb_zero [IsCommMonObj G] (hv : ∀ i, IsTangent (v i)) : IsLieComb 0 v 1 :=
  (LieComb.isLieComb_iff_tanExp _ _).2
    (congrArg Additive.toMul (map_zero (LieComb.combHom hv))).symm

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isLieComb_add [IsCommMonObj G] (hv : ∀ i, IsTangent (v i)) {c c' : Fin n → R}
    {w w' : epsR R ⟶ G} (h : IsLieComb c v w) (h' : IsLieComb c' v w') :
    IsLieComb (c + c') v (w * w') := by
  rw [LieComb.isLieComb_iff_tanExp] at h h' ⊢
  rw [h, h']
  exact (congrArg Additive.toMul (map_add (LieComb.combHom hv) c c')).symm

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem isLieComb_nsmul [IsCommMonObj G] (hv : ∀ i, IsTangent (v i)) {c : Fin n → R}
    {w : epsR R ⟶ G} (h : IsLieComb c v w) (N : ℕ) : IsLieComb (N • c) v (w ^ N) := by
  induction N with
  | zero => rw [zero_smul, pow_zero]; exact isLieComb_zero hv
  | succ N ih => rw [succ_nsmul, pow_succ]; exact isLieComb_add hv ih h

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem isTangent_comp (f : G ⟶ G') [IsMonHom f] {x : epsR R ⟶ G} (hx : IsTangent x) :
    IsTangent (x ≫ f) := by
  unfold IsTangent at hx ⊢
  rw [Over.comp_left, ← Category.assoc, hx, ← Over.comp_left, IsMonHom.one_hom]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem list_prod_comp (f : G ⟶ G') [IsMonHom f] (l : List (epsR R ⟶ G)) :
    l.prod ≫ f = (l.map (· ≫ f)).prod := by
  induction l with
  | nil => simpa using MonObj.one_comp f
  | cons a l ih => rw [List.prod_cons, List.map_cons, List.prod_cons, MonObj.mul_comp, ih]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem isLieComb_comp (f : G ⟶ G') [IsMonHom f] {c : Fin n → R} {w : epsR R ⟶ G}
    (h : IsLieComb c v w) : IsLieComb c (fun i => v i ≫ f) (w ≫ f) := by
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨fun i => u i ≫ f, fun i => ?_, ?_⟩
  · rw [Over.comp_left, Over.comp_left, hu i, Category.assoc]
  · rw [list_prod_comp, List.map_ofFn]
    rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem lieComb_add_pow_map : ∀ (R : Type) [CommRing R] (G G' : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] (n : ℕ) (v : Fin n → (epsR R ⟶ G)), (∀ i, IsTangent (v i)) → IsLieComb 0 v 1 ∧ (∀ c c' w w', IsLieComb c v w → IsLieComb c' v w' → IsLieComb (c + c') v (w * w')) ∧ (∀ c w (N : ℕ), IsLieComb c v w → IsLieComb (N • c) v (w ^ N)) ∧ ∀ f : G ⟶ G', IsMonHom f → (∀ i, IsTangent (v i ≫ f)) ∧ ∀ c w, IsLieComb c v w → IsLieComb c (fun i => v i ≫ f) (w ≫ f) := by
  intro R _ G G' _ _ _ n v hv
  exact ⟨isLieComb_zero hv, fun _ _ _ _ h h' => isLieComb_add hv h h',
    fun _ _ N h => isLieComb_nsmul hv h N,
    fun f _ => ⟨fun i => isTangent_comp f (hv i), fun _ _ h => isLieComb_comp f h⟩⟩

end GlobalTheory.LieCombHom
