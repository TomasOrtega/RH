import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipPaths

variable {T : Type}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem arrows_comp {X Y : Node} (p : Path T X Y) : ∀ {Z : Node} (q : Path T Y Z), (p.comp q).arrows = p.arrows ++ q.arrows
  | _, .nil => by simp [Path.comp, Path.arrows]
  | _, .snoc a q => by simp [Path.comp, Path.arrows, arrows_comp p q]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rowPath_arrows (j : ℕ) : ∀ n, (rowPath T j n).arrows = (List.range n).map fun i => Arrow.right i j
  | 0 => by simp [rowPath, Path.arrows]
  | n + 1 => by simp [rowPath, Path.arrows, rowPath_arrows j n, List.range_succ]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem downPath_arrows (t : T) (i : ℕ) : ∀ n, (downPath t i n).arrows = (List.range n).reverse.map fun j => Arrow.down t i j
  | 0 => by simp [downPath, Path.arrows]
  | n + 1 => by simp [downPath, arrows_comp, Path.arrows, downPath_arrows t i n, List.range_succ]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation. Simplify the hypotheses and the goal together.
-/
theorem edgeOf_inj {m : ℕ} {t : T} {a b : Arrow T} (ha : GlobalTheory.FlipRun.IsGridArrow m t a) (hb : GlobalTheory.FlipRun.IsGridArrow m t b)
    (h : GlobalTheory.FlipRun.edgeOf a = GlobalTheory.FlipRun.edgeOf b) : a = b := by
  rcases ha with ⟨i, j, -, -, rfl⟩ | ⟨i, j, -, -, rfl⟩ <;> rcases hb with ⟨k, l, -, -, rfl⟩ | ⟨k, l, -, -, rfl⟩ <;>
    simp_all [GlobalTheory.FlipRun.edgeOf]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem map_edgeOf_inj {m : ℕ} {t : T} : ∀ (l₁ l₂ : List (Arrow T)), (∀ a ∈ l₁, GlobalTheory.FlipRun.IsGridArrow m t a) →
    (∀ a ∈ l₂, GlobalTheory.FlipRun.IsGridArrow m t a) → l₁.map GlobalTheory.FlipRun.edgeOf = l₂.map GlobalTheory.FlipRun.edgeOf → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [edgeOf_inj (h₁ a (by simp)) (h₂ b (by simp)) h.1,
      map_edgeOf_inj l₁ l₂ (fun x hx => h₁ x (by simp [hx])) (fun x hx => h₂ x (by simp [hx])) h.2]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data.

Treat this case separately. Treat this case separately. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data.

Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.

Substitute using the available equality. Establish an intermediate fact. Substitute using the available equality. Both sides reduce to the same expression.
-/
theorem gridArrowPath_heq_of_arrows_eq {X : Node} : ∀ {Y : Node} (p : Path T X Y) {Y' : Node} (q : Path T X Y'),
    p.arrows = q.arrows → HEq p q := by
  intro Y p
  induction p with
  | nil =>
    intro Y' q h
    cases q with
    | nil => rfl
    | snoc b q => simp [Path.arrows] at h
  | snoc a p ih =>
    intro Y' q h
    cases q with
    | nil => simp [Path.arrows] at h
    | snoc b q =>
      simp only [Path.arrows] at h
      obtain ⟨h1, h2⟩ := List.append_inj' h rfl
      simp only [List.cons.injEq, and_true] at h2
      subst h2
      have := eq_of_heq (ih q h1)
      subst this
      rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem eq_of_arrows {X Y : Node} (p q : Path T X Y) (h : p.arrows = q.arrows) : p = q :=
  eq_of_heq (gridArrowPath_heq_of_arrows_eq p q h)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem givenPath_arrows (t : T) (m : ℕ) : (givenPath t m).arrows =
    (List.range m).reverse.map (fun j => Arrow.down t 0 j) ++ (List.range m).map fun i => Arrow.right i 0 := by
  simp [givenPath, arrows_comp, rowPath_arrows, downPath_arrows]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem oppPath_arrows (t : T) (m : ℕ) : (oppPath t m).arrows =
    (List.range m).map (fun i => Arrow.right i m) ++ (List.range m).reverse.map fun j => Arrow.down t m j := by
  simp [oppPath, arrows_comp, rowPath_arrows, downPath_arrows]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Separate the alternatives or extract the components of the hypothesis. Prove the second alternative. Prove the first alternative. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. Prove the first alternative. Prove the second alternative.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem given_opp_paths : ∀ {T : Type} (m : ℕ) (t : T), (GlobalTheory.FlipRun.OnGrid m t (GlobalTheory.FunObj.givenPath t m) ∧ GlobalTheory.FlipRun.edges (GlobalTheory.FunObj.givenPath t m) = GlobalTheory.SplitFlip.givenPath m) ∧ (GlobalTheory.FlipRun.OnGrid m t (GlobalTheory.FunObj.oppPath t m) ∧ GlobalTheory.FlipRun.edges (GlobalTheory.FunObj.oppPath t m) = GlobalTheory.SplitFlip.oppositePath m) ∧ ∀ {X Y : Node} (p q : Path T X Y), GlobalTheory.FlipRun.OnGrid m t p → GlobalTheory.FlipRun.OnGrid m t q → GlobalTheory.FlipRun.edges p = GlobalTheory.FlipRun.edges q → p = q := by
  intro T m t
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro a ha
    rw [givenPath_arrows] at ha
    simp only [List.mem_append, List.mem_map, List.mem_reverse, List.mem_range] at ha
    rcases ha with ⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩
    · exact Or.inr ⟨0, j, Nat.zero_le _, hj, rfl⟩
    · exact Or.inl ⟨i, 0, hi, Nat.zero_le _, rfl⟩
  · simp [GlobalTheory.FlipRun.edges, givenPath_arrows, GlobalTheory.SplitFlip.givenPath, GlobalTheory.FlipRun.edgeOf, Function.comp_def]
  · intro a ha
    rw [oppPath_arrows] at ha
    simp only [List.mem_append, List.mem_map, List.mem_reverse, List.mem_range] at ha
    rcases ha with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
    · exact Or.inl ⟨i, m, hi, le_rfl, rfl⟩
    · exact Or.inr ⟨m, j, le_rfl, hj, rfl⟩
  · simp [GlobalTheory.FlipRun.edges, oppPath_arrows, GlobalTheory.SplitFlip.oppositePath, GlobalTheory.FlipRun.edgeOf, Function.comp_def]
  · intro X Y p q hp hq h
    exact eq_of_arrows p q (map_edgeOf_inj _ _ hp hq h)

end GlobalTheory.FlipPaths
