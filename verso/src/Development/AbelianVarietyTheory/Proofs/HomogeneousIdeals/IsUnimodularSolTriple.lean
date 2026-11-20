import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsLiftAddOfIsReducedEq

open GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

namespace GlobalTheory.WeightScale

variable {A B : Type*} [CommRing A] [CommRing B]

def curve (u : A) (V : WeierstrassCurve A) : WeierstrassCurve A :=
  ⟨u * V.a₁, u ^ 2 * V.a₂, u ^ 3 * V.a₃, u ^ 4 * V.a₄, u ^ 6 * V.a₆⟩

def triple (u : A) (P : Fin 3 → A) : Fin 3 → A := ![u ^ 2 * P 0, u ^ 3 * P 1, P 2]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem curve_eq_smul (u : Aˣ) (V : WeierstrassCurve A) :
    curve (u : A) V = (⟨u⁻¹, 0, 0, 0⟩ : WeierstrassCurve.VariableChange A) • V := by
  ext <;> simp [curve, WeierstrassCurve.variableChange_def]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem map_curve (g : A →+* B) (u : A) (V : WeierstrassCurve A) :
    (curve u V).map g = curve (g u) (V.map g) := by
  ext <;> simp [curve]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem curve_map_eq (g : A →+* B) {u : A} {V : WeierstrassCurve A} (h : curve u V = V) :
    curve (g u) (V.map g) = V.map g := by
  rw [← map_curve, h]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem comp_triple (g : A →+* B) (u : A) (P : Fin 3 → A) :
    g ∘ triple u P = triple (g u) (g ∘ P) := by
  ext i; fin_cases i <;> simp [triple]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem triple_triple (u v : A) (P : Fin 3 → A) : triple u (triple v P) = triple (u * v) P := by
  ext i; fin_cases i <;> simp [triple] <;> ring

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem triple_one (P : Fin 3 → A) : triple 1 P = P := by
  ext i; fin_cases i <;> simp [triple]

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem equation_triple (u : A) {V : WeierstrassCurve A} {P : Fin 3 → A}
    (h : V.toProjective.Equation P) : (curve u V).toProjective.Equation (triple u P) := by
  rw [WeierstrassCurve.Projective.equation_iff] at h ⊢
  simp only [curve, triple, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  linear_combination u ^ 6 * h

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem span_le_span_triple {u : A} (hu : IsUnit u) (P : Fin 3 → A) :
    Ideal.span (Set.range P) ≤ Ideal.span (Set.range (triple u P)) := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact (Ideal.unit_mul_mem_iff_mem _ (hu.pow 2)).mp (Ideal.subset_span ⟨0, rfl⟩)
  · exact (Ideal.unit_mul_mem_iff_mem _ (hu.pow 3)).mp (Ideal.subset_span ⟨1, rfl⟩)
  · exact Ideal.subset_span ⟨2, rfl⟩

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem isUnimodularSol_triple {u : A} (hu : IsUnit u) {V : WeierstrassCurve A}
    (hV : curve u V = V) {P : Fin 3 → A} (h : IsUnimodularSol V P) :
    IsUnimodularSol V (triple u P) :=
  ⟨hV ▸ equation_triple u h.equation,
    top_le_iff.mp (h.span_eq_top.ge.trans (span_le_span_triple hu P))⟩

open WeierstrassCurve.Projective in
/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem addXYZ_triple (u : A) (V : WeierstrassCurve A) (P Q : Fin 3 → A) :
    (curve u V).toProjective.addXYZ (triple u P) (triple u Q) =
      u ^ 6 • triple u (V.toProjective.addXYZ P Q) := by
  ext i
  fin_cases i <;>
    simp [curve, triple, addXYZ, addX, addY, negAddY, addZ, negY] <;> ring

open WeierstrassCurve.Projective in
/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem diagXYZ_triple (u : A) (V : WeierstrassCurve A) (P Q : Fin 3 → A) :
    diagXYZ (curve u V).toProjective (triple u P) (triple u Q) =
      u ^ 9 • triple u (diagXYZ V.toProjective P Q) := by
  ext i
  fin_cases i <;>
    simp [curve, triple, diagXYZ, diagX, diagY, negDiagY, diagZ, negY] <;> ring

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation. Take a linear combination of the given relations to obtain the conclusion. Take a linear combination of the given relations to obtain the conclusion. Take a linear combination of the given relations to obtain the conclusion.

Take a linear combination of the given relations to obtain the conclusion. Take a linear combination of the given relations to obtain the conclusion. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem proportional_triple (u c : A) {T S : Fin 3 → A} (h : Proportional T S) :
    Proportional (triple u T) (c • triple u S) := by
  refine (Proportional.smul_left (fun i j => ?_) c).symm
  fin_cases i <;> fin_cases j <;> simp only [triple, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · linear_combination u ^ 5 * h 1 0
  · linear_combination u ^ 2 * h 2 0
  · linear_combination u ^ 5 * h 0 1
  · linear_combination u ^ 3 * h 2 1
  · linear_combination u ^ 2 * h 0 2
  · linear_combination u ^ 3 * h 1 2

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components.
-/
theorem isSumTriple_triple {u : A} {V : WeierstrassCurve A} (hV : curve u V = V)
    {P Q T : Fin 3 → A} (h : IsSumTriple V P Q T) :
    IsSumTriple V (triple u P) (triple u Q) (triple u T) := by
  have h₁ := addXYZ_triple u V P Q
  have h₂ := diagXYZ_triple u V P Q
  rw [hV] at h₁ h₂
  exact ⟨h₁ ▸ proportional_triple u _ h.add, h₂ ▸ proportional_triple u _ h.diag⟩

open WeierstrassCurve.Projective in
/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem isSumTriple_cubeRoot {w : A} (hw : w ^ 2 + w + 1 = 0) {X Y Z : A}
    (h : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve A).toProjective.Equation ![X, Y, Z]) :
    IsSumTriple ⟨0, 0, 1, 0, 0⟩ ![X, Y, Z] ![w * X, Y, Z] ![w ^ 2 * X, -Y - Z, Z] := by
  rw [WeierstrassCurve.Projective.equation_iff] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [addXYZ, addX, addY, negAddY, addZ, diagXYZ, diagX, diagY, negDiagY, diagZ, negY] <;>
    grind

end GlobalTheory.WeightScale
