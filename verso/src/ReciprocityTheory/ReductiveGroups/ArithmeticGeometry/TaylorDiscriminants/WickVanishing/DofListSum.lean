import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.G2

variable {k : Type} [CommRing k] {d : ℕ}

section Dof
variable (F : Fin d → PS k 2 d) (v : Fin d → k)

/- English proof (translation)
Unfold `Dof`. Simplify using `only [map_add, mul_add, Finset.sum_add_distrib]`.
-/
theorem dof_add (f g : PS k 1 d) : Dof F v (f + g) = Dof F v f + Dof F v g := by
  unfold Dof
  simp only [map_add, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[Dof]`.
-/
theorem dof_zero : Dof F v (0 : PS k 1 d) = 0 := by
  simp [Dof]

/- English proof (translation)
Unfold `Dof`. Establish `h : ∀ j : Fin d, pderiv k ((0 : Fin 1), j) (C a : PS k 1 d) = 0` using `fun j => by`. Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
theorem dof_C (a : k) : Dof F v (C a : PS k 1 d) = 0 := by
  unfold Dof
  have h : ∀ j : Fin d, pderiv k ((0 : Fin 1), j) (C a : PS k 1 d) = 0 := fun j => by
    simp
  simp [h]

/- English proof (translation)
Unfold `Dof`. Rewrite using `[Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dof_mul (f g : PS k 1 d) : Dof F v (f * g) = Dof F v f * g + f * Dof F v g := by
  unfold Dof
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  ring

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simp [dof_zero]`. Consider the case `cons a L ih => simp [dof_add, ih]`.
-/
theorem dof_list_sum (L : List (PS k 1 d)) : Dof F v L.sum = (L.map (Dof F v)).sum := by
  induction L with
  | nil => simp [dof_zero]
  | cons a L ih => simp [dof_add, ih]

end Dof

section Words
variable (F : Fin d → PS k 2 d) {ι : Type} (u : ι → Fin d → k)

def T (w : List ι) (A : PS k 1 d) : PS k 1 d := w.foldr (fun l g => Dof F (u l) g) A

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem T_cons (l : ι) (w : List ι) (A : PS k 1 d) : T F u (l :: w) A = Dof F (u l) (T F u w A) := rfl

/- English proof (translation)
Simplify using `[T, List.foldr_append]`.
-/
theorem T_append (w w' : List ι) (A : PS k 1 d) : T F u (w ++ w') A = T F u w (T F u w' A) := by
  simp [T, List.foldr_append]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons l w ih => rw [T_cons, T_cons, T_cons, ih, dof_add]`.
-/
theorem T_add (w : List ι) (A B : PS k 1 d) : T F u w (A + B) = T F u w A + T F u w B := by
  induction w with
  | nil => rfl
  | cons l w ih => rw [T_cons, T_cons, T_cons, ih, dof_add]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons l w ih => rw [T_cons, ih, dof_zero]`.
-/
theorem T_zero (w : List ι) : T F u w (0 : PS k 1 d) = 0 := by
  induction w with
  | nil => rfl
  | cons l w ih => rw [T_cons, ih, dof_zero]

def splits : List ι → List (List ι × List ι)
  | [] => [([], [])]
  | l :: w => (splits w).map (fun p => (l :: p.1, p.2)) ++ (splits w).map (fun p => (p.1, l :: p.2))

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => simp [splits, T]`. Consider the case `cons l w ih`. Rewrite using `[T_cons, ih, dof_list_sum, List.map_map]`. Simplify using `only [splits, List.map_append, List.map_map, List.sum_append]`.

Rewrite using `[← List.sum_map_add]`. Use `congr 1`. Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `p _`. Simplify using `only [Function.comp_apply]`.

Rewrite using `[dof_mul]`. Both sides reduce to the same expression.
-/
theorem T_mul (w : List ι) (A B : PS k 1 d) :
    T F u w (A * B) = ((splits w).map (fun p => T F u p.1 A * T F u p.2 B)).sum := by
  induction w with
  | nil => simp [splits, T]
  | cons l w ih =>
    rw [T_cons, ih, dof_list_sum, List.map_map]
    simp only [splits, List.map_append, List.map_map, List.sum_append]
    rw [← List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro p _
    simp only [Function.comp_apply]
    rw [dof_mul]
    rfl

end Words

end ReciprocityTheory.ChartRestriction.G.TB.G2
