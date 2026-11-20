import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.HeckeLevelWordBase

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact ⟨0, le_rfl, by simp⟩`. Consider the case `cons g l ih`. Take `⟨R, hR, hs⟩` from `ih`. Break down `g with c | t` into its components or cases.

Use `⟨R, hR, fun s hm => ?_⟩` and prove the remaining obligations. Break down `List.mem_cons.1 hm with h | h` into its components or cases. Consider the cases of `h`. Conclude with `hs s h`. Use `⟨max R (max t.T (t.r + B.c)), le_max_of_le_left hR, fun s hm => ?_⟩` and prove the remaining obligations.

Break down `List.mem_cons.1 hm with h | h` into its components or cases. Consider the cases of `h`. Conclude with `⟨le_max_of_le_right (le_max_left _ _), le_max_of_le_right (le_max_right _ _)⟩`. Conclude with `⟨(hs s h).1.trans (le_max_left _ _), (hs s h).2.trans (le_max_left _ _)⟩`.
-/
private theorem exists_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E} (l : List (BGen B)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ s, Sum.inr s ∈ l → s.T ≤ R ∧ s.r + B.c ≤ R := by
  induction l with
  | nil => exact ⟨0, le_rfl, by simp⟩
  | cons g l ih =>
    obtain ⟨R, hR, hs⟩ := ih
    rcases g with c | t
    · refine ⟨R, hR, fun s hm => ?_⟩
      rcases List.mem_cons.1 hm with h | h
      · cases h
      · exact hs s h
    · refine ⟨max R (max t.T (t.r + B.c)), le_max_of_le_left hR, fun s hm => ?_⟩
      rcases List.mem_cons.1 hm with h | h
      · cases h
        exact ⟨le_max_of_le_right (le_max_left _ _), le_max_of_le_right (le_max_right _ _)⟩
      · exact ⟨(hs s h).1.trans (le_max_left _ _), (hs s h).2.trans (le_max_left _ _)⟩

/- English proof (translation)
Introduce `hW hR E _ _ _ n π S T F₀ F h i`. Establish `hadj` using `(hW E (F.B i) [] (F.t₂ i) 0 (by simp) (h.tok i).2 le_rfl (by simp)).2.2.2.2.1`. Establish `hgl : ∀ p, (gl F i p).Ok ∧ (gl F i p).op = if p.2 then star (F.g p.1 i).op else (F.g p.1 i).op`. Introduce and unpack `⟨x, s⟩`. Consider the cases of `s with`.

Consider the case `false => exact ⟨h.ok x i, rfl⟩`. Consider the case `true`. Use `⟨(hadj _ (h.ok x i)).1, ?_⟩` and prove the remaining obligations. Use `show (F.g x i).adj.op = star (F.g x i).op`. Rewrite using `[(hadj _ (h.ok x i)).2, ContinuousLinearMap.star_eq_adjoint]`.

Establish `hbw : ∀ w, ∀ g ∈ bw F i w, g.Ok`. Introduce `w g hg`. Break down `List.mem_append.1 hg with hg | hg` into its components or cases. Rewrite using `[List.eq_of_mem_replicate hg]`. Conclude with `h.βok i`.

Take `⟨p, -, rfl⟩` from `List.mem_map.1 hg`. Conclude with `(hgl p).1`. Use `⟨hgl, hbw, fun ws => ?_⟩` and prove the remaining obligations. Take `⟨R, hR0, hRs⟩` from `exists_bound (Sum.inr (F.t₁ i) :: (ws.map (bw F i)).flatten)`. Use `(hW E (F.B i) _ (F.t₂ i) R ?_ (h.tok i).2 hR0 hRs).1` and prove the remaining obligations.

Introduce `g hg`. Break down `List.mem_cons.1 hg with rfl | hg` into its components or cases. Conclude with `(h.tok i).1`. Take `⟨l, hl, hgl'⟩` from `List.mem_flatten.1 hg`. Take `⟨w, -, rfl⟩` from `List.mem_map.1 hl`.

Conclude with `hbw w g hgl'`.
-/
theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.twok_pf :
    BlockWordOperators → TwOk := by
  intro hW hR E _ _ _ n π S T F₀ F h i
  have hadj := (hW E (F.B i) [] (F.t₂ i) 0 (by simp) (h.tok i).2 le_rfl (by simp)).2.2.2.2.1
  have hgl : ∀ p, (gl F i p).Ok ∧ (gl F i p).op = if p.2 then star (F.g p.1 i).op else (F.g p.1 i).op := by
    rintro ⟨x, s⟩
    cases s with
    | false => exact ⟨h.ok x i, rfl⟩
    | true =>
      refine ⟨(hadj _ (h.ok x i)).1, ?_⟩
      show (F.g x i).adj.op = star (F.g x i).op
      rw [(hadj _ (h.ok x i)).2, ContinuousLinearMap.star_eq_adjoint]
  have hbw : ∀ w, ∀ g ∈ bw F i w, g.Ok := by
    intro w g hg
    rcases List.mem_append.1 hg with hg | hg
    · rw [List.eq_of_mem_replicate hg]
      exact h.βok i
    · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hg
      exact (hgl p).1
  refine ⟨hgl, hbw, fun ws => ?_⟩
  obtain ⟨R, hR0, hRs⟩ := exists_bound (Sum.inr (F.t₁ i) :: (ws.map (bw F i)).flatten)
  refine (hW E (F.B i) _ (F.t₂ i) R ?_ (h.tok i).2 hR0 hRs).1
  intro g hg
  rcases List.mem_cons.1 hg with rfl | hg
  · exact (h.tok i).1
  · obtain ⟨l, hl, hgl'⟩ := List.mem_flatten.1 hg
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hl
    exact hbw w g hgl'

end
