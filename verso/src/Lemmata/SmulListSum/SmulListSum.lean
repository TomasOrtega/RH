import Mathlib

universe u_1

namespace Bl.SmulListSum

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp only [List.sum_nil, List.map_nil, smul_zero]`. Consider the case `cons a t ih => simp only [List.sum_cons, List.map_cons, smul_add, ih]`.
-/
private theorem smul_list_sum {U : Type u_1} [AddCommGroup U] [Module Complex U]
    (c : Complex) (l : List U) : c • l.sum = (l.map (fun w => c • w)).sum := by
  induction l with
  | nil => simp only [List.sum_nil, List.map_nil, smul_zero]
  | cons a t ih => simp only [List.sum_cons, List.map_cons, smul_add, ih]

/- English proof (translation)
Introduce `U _ _ G hG y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Use `⟨[x], ?_, ?_⟩` and prove the remaining obligations. Introduce `w hw`.

Rewrite `hw` using `[List.mem_singleton]`. Rewrite using `[hw]`. Conclude with `hx`. Simplify using `only [List.sum_cons, List.sum_nil, add_zero]`. Consider the case `zero => exact ⟨[], fun w hw => absurd hw (List.not_mem_nil), by simp only [List.sum_nil]⟩`.

Consider the case `add a b _ _ iha ihb`. Take `⟨la, hla, rfl⟩` from `iha`. Take `⟨lb, hlb, rfl⟩` from `ihb`. Use `⟨la ++ lb, ?_, ?_⟩` and prove the remaining obligations. Introduce `w hw`.

Break down `List.mem_append.mp hw with h | h` into its components or cases. Conclude with `hla w h`. Conclude with `hlb w h`. Rewrite using `[List.sum_append]`. Consider the case `smul c a _ iha`.

Take `⟨la, hla, rfl⟩` from `iha`. Use `⟨la.map (fun w => c • w), ?_, smul_list_sum c la⟩` and prove the remaining obligations. Introduce `w hw`. Take `⟨v, hv, rfl⟩` from `List.mem_map.mp hw`. Conclude with `hG v (hla v hv) c`.
-/
theorem goal1 :
  ∀ {U : Type u_1} [inst : AddCommGroup.{u_1} U] [inst_1 : Module.{0, u_1} Complex U] {G : Set.{u_1} U},
  (∀ (w : U),
      Membership.mem.{u_1, u_1} G w → ∀ (c : Complex), Membership.mem.{u_1, u_1} G (HSMul.hSMul.{0, u_1, u_1} c w)) →
    ∀ {y : U},
      Membership.mem.{u_1, u_1} (Submodule.span.{0, u_1} Complex G) y →
        Exists.{u_1 + 1} fun (l : List.{u_1} U) ↦
          And (∀ (w : U), Membership.mem.{u_1, u_1} l w → Membership.mem.{u_1, u_1} G w)
            (Eq.{u_1 + 1} y (List.sum.{u_1} l)) := by
  intro U _ _ G hG y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    refine ⟨[x], ?_, ?_⟩
    · intro w hw
      rw [List.mem_singleton] at hw
      rw [hw]; exact hx
    · simp only [List.sum_cons, List.sum_nil, add_zero]
  | zero => exact ⟨[], fun w hw => absurd hw (List.not_mem_nil), by simp only [List.sum_nil]⟩
  | add a b _ _ iha ihb =>
    obtain ⟨la, hla, rfl⟩ := iha
    obtain ⟨lb, hlb, rfl⟩ := ihb
    refine ⟨la ++ lb, ?_, ?_⟩
    · intro w hw
      rcases List.mem_append.mp hw with h | h
      · exact hla w h
      · exact hlb w h
    · rw [List.sum_append]
  | smul c a _ iha =>
    obtain ⟨la, hla, rfl⟩ := iha
    refine ⟨la.map (fun w => c • w), ?_, smul_list_sum c la⟩
    intro w hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    exact hG v (hla v hv) c

end Bl.SmulListSum
