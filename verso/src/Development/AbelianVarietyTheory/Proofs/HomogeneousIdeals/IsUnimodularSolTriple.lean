import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsLiftAddOfIsReducedEq

open GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

namespace GlobalTheory.WeightScale

variable {A B : Type*} [CommRing A] [CommRing B]

def curve (u : A) (V : WeierstrassCurve A) : WeierstrassCurve A :=
  ⟨u * V.a₁, u ^ 2 * V.a₂, u ^ 3 * V.a₃, u ^ 4 * V.a₄, u ^ 6 * V.a₆⟩

def triple (u : A) (P : Fin 3 → A) : Fin 3 → A := ![u ^ 2 * P 0, u ^ 3 * P 1, P 2]

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [curve, WeierstrassCurve.variableChange_def]`.
-/
theorem curve_eq_smul (u : Aˣ) (V : WeierstrassCurve A) :
    curve (u : A) V = (⟨u⁻¹, 0, 0, 0⟩ : WeierstrassCurve.VariableChange A) • V := by
  ext <;> simp [curve, WeierstrassCurve.variableChange_def]

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [curve]`.
-/
theorem map_curve (g : A →+* B) (u : A) (V : WeierstrassCurve A) :
    (curve u V).map g = curve (g u) (V.map g) := by
  ext <;> simp [curve]

/- English proof (translation)
Rewrite using `[← map_curve, h]`.
-/
theorem curve_map_eq (g : A →+* B) {u : A} {V : WeierstrassCurve A} (h : curve u V = V) :
    curve (g u) (V.map g) = V.map g := by
  rw [← map_curve, h]

/- English proof (translation)
Apply the tactic sequence `ext i; fin_cases i <;> simp [triple]`.
-/
theorem comp_triple (g : A →+* B) (u : A) (P : Fin 3 → A) :
    g ∘ triple u P = triple (g u) (g ∘ P) := by
  ext i; fin_cases i <;> simp [triple]

/- English proof (translation)
Apply the tactic sequence `ext i; fin_cases i <;> simp [triple] <;> ring`.
-/
theorem triple_triple (u v : A) (P : Fin 3 → A) : triple u (triple v P) = triple (u * v) P := by
  ext i; fin_cases i <;> simp [triple] <;> ring

/- English proof (translation)
Apply the tactic sequence `ext i; fin_cases i <;> simp [triple]`.
-/
theorem triple_one (P : Fin 3 → A) : triple 1 P = P := by
  ext i; fin_cases i <;> simp [triple]

/- English proof (translation)
Rewrite `h`, the goal using `[WeierstrassCurve.Projective.equation_iff]`. Simplify using `only [curve, triple, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]`. Take the linear combination `u ^ 6 * h`.
-/
theorem equation_triple (u : A) {V : WeierstrassCurve A} {P : Fin 3 → A}
    (h : V.toProjective.Equation P) : (curve u V).toProjective.Equation (triple u P) := by
  rw [WeierstrassCurve.Projective.equation_iff] at h ⊢
  simp only [curve, triple, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  linear_combination u ^ 6 * h

/- English proof (translation)
Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Use `fin_cases i`. Conclude with `(Ideal.unit_mul_mem_iff_mem _ (hu.pow 2)).mp (Ideal.subset_span ⟨0, rfl⟩)`. Conclude with `(Ideal.unit_mul_mem_iff_mem _ (hu.pow 3)).mp (Ideal.subset_span ⟨1, rfl⟩)`.

Conclude with `Ideal.subset_span ⟨2, rfl⟩`.
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
Assemble the required witnesses or components as `⟨hV ▸ equation_triple u h.equation, top_le_iff.mp (h.span_eq_top.ge.trans (span_le_span_triple hu P))⟩`.
-/
theorem isUnimodularSol_triple {u : A} (hu : IsUnit u) {V : WeierstrassCurve A}
    (hV : curve u V = V) {P : Fin 3 → A} (h : IsUnimodularSol V P) :
    IsUnimodularSol V (triple u P) :=
  ⟨hV ▸ equation_triple u h.equation,
    top_le_iff.mp (h.span_eq_top.ge.trans (span_le_span_triple hu P))⟩

open WeierstrassCurve.Projective in
/- English proof (translation)
Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;>`. Apply the tactic sequence `simp [curve, triple, addXYZ, addX, addY, negAddY, addZ, negY] <;> ring`.
-/
theorem addXYZ_triple (u : A) (V : WeierstrassCurve A) (P Q : Fin 3 → A) :
    (curve u V).toProjective.addXYZ (triple u P) (triple u Q) =
      u ^ 6 • triple u (V.toProjective.addXYZ P Q) := by
  ext i
  fin_cases i <;>
    simp [curve, triple, addXYZ, addX, addY, negAddY, addZ, negY] <;> ring

open WeierstrassCurve.Projective in
/- English proof (translation)
Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;>`. Apply the tactic sequence `simp [curve, triple, diagXYZ, diagX, diagY, negDiagY, diagZ, negY] <;> ring`.
-/
theorem diagXYZ_triple (u : A) (V : WeierstrassCurve A) (P Q : Fin 3 → A) :
    diagXYZ (curve u V).toProjective (triple u P) (triple u Q) =
      u ^ 9 • triple u (diagXYZ V.toProjective P Q) := by
  ext i
  fin_cases i <;>
    simp [curve, triple, diagXYZ, diagX, diagY, negDiagY, diagZ, negY] <;> ring

/- English proof (translation)
Use `(Proportional.smul_left (fun i j => ?_) c).symm` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp only [triple, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]`. Take the linear combination `u ^ 5 * h 1 0`. Take the linear combination `u ^ 2 * h 2 0`. Take the linear combination `u ^ 5 * h 0 1`.

Take the linear combination `u ^ 3 * h 2 1`. Take the linear combination `u ^ 2 * h 0 2`. Take the linear combination `u ^ 3 * h 1 2`.
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
Establish `h₁` using `addXYZ_triple u V P Q`. Establish `h₂` using `diagXYZ_triple u V P Q`. Rewrite `h₁`, `h₂` using `[hV]`. Conclude with `⟨h₁ ▸ proportional_triple u _ h.add, h₂ ▸ proportional_triple u _ h.diag⟩`.
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
Rewrite `h` using `[WeierstrassCurve.Projective.equation_iff]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h`. Apply the tactic sequence `constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [addXYZ, addX, addY, negAddY, addZ, diagXYZ, diagX, diagY, negDiagY, diagZ, negY] <;>`. Use `grind`.
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
