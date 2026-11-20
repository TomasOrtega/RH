import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.DofListSum

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.G2

variable {k : Type} [CommRing k] {d : ℕ}

section Q
variable {ι : Type} (c : ι → ι → k)

def ev2 : List ι → k
  | [x, y] => c x y
  | _ => 0

variable (F : Fin d → PS k 2 d) (u : ι → Fin d → k) (q : PS k 1 d)
  (hq0 : constantCoeff q = 0) (hq1 : ∀ l, constantCoeff (Dof F (u l) q) = 0)
  (hq2 : ∀ l l', Dof F (u l) (Dof F (u l') q) = C (c l l'))
include hq2

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => simp at hw`. Consider the case `cons a w ih`. Rewrite using `[T_cons]`. Break down `w with _ | ⟨b, _ | ⟨e, _ | ⟨f, w⟩⟩⟩` into its components or cases.

Simplify using `at hw`. Simplify using `at hw`. Rewrite using `[T_cons, T_cons]`. Express the relevant statement in the definitionally equal form `Dof F (u a) (Dof F (u b) (Dof F (u e) q)) = 0`. Rewrite using `[hq2, dof_C]`.

Rewrite using `[ih (by simp)]`. Conclude with `dof_zero ..`.
-/
theorem T_q_long (w : List ι) (hw : 3 ≤ w.length) : T F u w q = 0 := by
  induction w with
  | nil => simp at hw
  | cons a w ih =>
    rw [T_cons]
    rcases w with _ | ⟨b, _ | ⟨e, _ | ⟨f, w⟩⟩⟩
    · simp at hw
    · simp at hw
    · rw [T_cons, T_cons]
      change Dof F (u a) (Dof F (u b) (Dof F (u e) q)) = 0
      rw [hq2, dof_C]
    · rw [ih (by simp)]
      exact dof_zero ..

include hq0 hq1

/- English proof (translation)
Break down `b with _ | ⟨x, _ | ⟨y, _ | ⟨z, b⟩⟩⟩` into its components or cases. Conclude with `hq0`. Rewrite using `[T_cons]`. Conclude with `hq1 x`. Rewrite using `[T_cons, T_cons]`.

Express the relevant statement in the definitionally equal form `constantCoeff (Dof F (u x) (Dof F (u y) q)) = c x y`. Rewrite using `[hq2, constantCoeff_C]`. Rewrite using `[T_q_long c F u q hq2 _ (by simp), map_zero]`. Both sides reduce to the same expression.
-/
theorem cc_T_q (b : List ι) : constantCoeff (T F u b q) = ev2 c b := by
  rcases b with _ | ⟨x, _ | ⟨y, _ | ⟨z, b⟩⟩⟩
  · exact hq0
  · rw [T_cons]
    exact hq1 x
  · rw [T_cons, T_cons]
    change constantCoeff (Dof F (u x) (Dof F (u y) q)) = c x y
    rw [hq2, constantCoeff_C]
  · rw [T_q_long c F u q hq2 _ (by simp), map_zero]
    rfl

/- English proof (translation)
Rewrite using `[T_mul, map_list_sum, List.map_map]`. Use `congr 1`. Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `p _`. Simplify using `only [Function.comp_apply, map_mul]`.

Rewrite using `[cc_T_q c F u q hq0 hq1 hq2]`.
-/
theorem cc_T_mul_q (w : List ι) (A : PS k 1 d) :
    constantCoeff (T F u w (A * q)) =
      ((splits w).map (fun p => constantCoeff (T F u p.1 A) * ev2 c p.2)).sum := by
  rw [T_mul, map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply, map_mul]
  rw [cc_T_q c F u q hq0 hq1 hq2]

end Q

end ReciprocityTheory.ChartRestriction.G.TB.G2
