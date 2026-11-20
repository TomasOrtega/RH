import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open Formalism.REAL

namespace GlobalTheory

inductive LoweringWord {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) : ℕ → V → Prop
  | base : LoweringWord E v 0 v
  | step {N : ℕ} {x : V} (a b : Fin n) (h : b < a) :
      LoweringWord E v N x → LoweringWord E v (N + (a.val - b.val)) (E a b x)

section
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
  {E : Fin n → Fin n → Module.End ℂ V} {ν : Fin n → ℂ} {v : V}

/- English proof (translation)
Establish `h` using `congrArg (fun f : Module.End ℂ V => f y) (hE a b c d)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at h`. Apply the tactic sequence `have h1 : (if b = c then E a d else 0) y = if b = c then E a d y else 0 := by split_ifs <;> simp`. Apply the tactic sequence `have h2 : (if d = a then E c b else 0) y = if d = a then E c b y else 0 := by split_ifs <;> simp`. Rewrite `h` using `[h1, h2]`.

Rewrite using `[add_sub_assoc, ← h]`. Normalize the expressions using the abelian group laws.
-/
theorem glRel_apply_comm (hE : GlRel E) (a b c d : Fin n) (y : V) :
    E a b (E c d y) = E c d (E a b y) + (if b = c then E a d y else 0)
      - (if d = a then E c b y else 0) := by
  have h := congrArg (fun f : Module.End ℂ V => f y) (hE a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  have h1 : (if b = c then E a d else 0) y = if b = c then E a d y else 0 := by
    split_ifs <;> simp
  have h2 : (if d = a then E c b else 0) y = if d = a then E c b y else 0 := by
    split_ifs <;> simp
  rw [h1, h2] at h
  rw [add_sub_assoc, ← h]
  abel

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨N, hN⟩` from `hx`. Conclude with `Submodule.subset_span ⟨_, hN.step a b hab⟩`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem loweringWord_span_lower (a b : Fin n) (hab : b < a) :
    ∀ x ∈ Submodule.span ℂ {x | ∃ N, LoweringWord E v N x},
      E a b x ∈ Submodule.span ℂ {x | ∃ N, LoweringWord E v N x} := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨N, hN⟩ := hx
    exact Submodule.subset_span ⟨_, hN.step a b hab⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Proceed by induction on `hx with`. Consider the case `base`. Introduce `a b`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Rewrite using `[hv.2 a b h]`.

Conclude with `Submodule.zero_mem _`. Substitute `h` using the available equality. Rewrite using `[hv.1 a]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, LoweringWord.base⟩)`. Conclude with `Submodule.subset_span ⟨_, LoweringWord.base.step a b h⟩`.

Consider the case `step c d h _ ih`. Introduce `a b`. Rewrite using `[glRel_apply_comm hE]`. Use `Submodule.sub_mem _ (Submodule.add_mem _ (loweringWord_span_lower c d h _ (ih a b)) ?_) ?_` and prove the remaining obligations. Use `split_ifs`.

Conclude with `ih _ _`. Conclude with `Submodule.zero_mem _`. Use `split_ifs`. Conclude with `ih _ _`. Conclude with `Submodule.zero_mem _`.
-/
theorem loweringWord_apply_mem (hE : GlRel E) (hv : IsHW E ν v) {N : ℕ} {x : V}
    (hx : LoweringWord E v N x) :
    ∀ a b, E a b x ∈ Submodule.span ℂ {x | ∃ N, LoweringWord E v N x} := by
  induction hx with
  | base =>
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · rw [hv.2 a b h]; exact Submodule.zero_mem _
    · subst h
      rw [hv.1 a]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, LoweringWord.base⟩)
    · exact Submodule.subset_span ⟨_, LoweringWord.base.step a b h⟩
  | step c d h _ ih =>
    intro a b
    rw [glRel_apply_comm hE]
    refine Submodule.sub_mem _ (Submodule.add_mem _ (loweringWord_span_lower c d h _ (ih a b)) ?_) ?_
    · split_ifs
      · exact ih _ _
      · exact Submodule.zero_mem _
    · split_ifs
      · exact ih _ _
      · exact Submodule.zero_mem _

/- English proof (translation)
Proceed by induction on `hx with`. Consider the case `base`. Simplify using `[LinearMap.sum_apply, hv.1, Finset.sum_smul, mul_smul]`. Consider the case `@step N y c d h _ ih`. Establish `key : (∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a) (E c d y) = E c d ((∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a) y) + ((c.val : ℕ) : ℂ) • E c d y - ((d.val : ℕ) : ℂ) • E c d y`.

Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]`. Simplify using `only [glRel_apply_comm hE _ _ c d y, smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[key, ih, map_smul]`. Establish `hle : d.val ≤ c.val` using `le_of_lt h`. Move the coercions through the operations in `[Nat.cast_sub hle]`.

Use `module`.
-/
theorem loweringWord_height (hE : GlRel E) (hv : IsHW E ν v) {N : ℕ} {x : V}
    (hx : LoweringWord E v N x) :
    (∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a) x
      = ((∑ a : Fin n, ((a.val : ℕ) : ℂ) * ν a) + (N : ℂ)) • x := by
  induction hx with
  | base =>
    simp [LinearMap.sum_apply, hv.1, Finset.sum_smul, mul_smul]
  | @step N y c d h _ ih =>
    have key : (∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a) (E c d y)
        = E c d ((∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a) y)
          + ((c.val : ℕ) : ℂ) • E c d y - ((d.val : ℕ) : ℂ) • E c d y := by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
      simp only [glRel_apply_comm hE _ _ c d y, smul_sub, smul_add, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    rw [key, ih, map_smul]
    have hle : d.val ≤ c.val := le_of_lt h
    push_cast [Nat.cast_sub hle]
    module

/- English proof (translation)
Consider the cases of `hx with`. Consider the case `base => exact Or.inl rfl`. Consider the case `step c d h _ => right`. Establish `: d.val < c.val` using `h`. Use linear arithmetic over natural numbers and integers.
-/
theorem loweringWord_zero_or_pos {N : ℕ} {x : V} (hx : LoweringWord E v N x) :
    x = v ∨ 0 < N := by
  cases hx with
  | base => exact Or.inl rfl
  | step c d h _ =>
    right
    have : d.val < c.val := h
    omega

end

/- English proof (translation)
Introduce `V _ _ n E ν v hE hv`. Use `⟨Submodule.span ℂ {x | ∃ N, LoweringWord E v N x}, ?_, Submodule.subset_span ⟨0, LoweringWord.base⟩, ?_⟩` and prove the remaining obligations. Introduce `a b x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨N, hN⟩` from `hx`. Conclude with `loweringWord_apply_mem hE hv hN a b`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ _ hx`. Introduce `x hx hw set H : Module.End ℂ V := ∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a with hH set h : ℂ := ∑ a : Fin n, ((a.val : ℕ) : ℂ) * ν a with hh`. Establish `hle : Submodule.span ℂ {x | ∃ N, LoweringWord E v N x} ≤ Submodule.span ℂ {v} ⊔ ⨆ (μ : ℂ) (_ : μ ≠ h), H.eigenspace μ`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `y ⟨N, hN⟩`. Break down `loweringWord_zero_or_pos hN with rfl | hpos` into its components or cases. Conclude with `Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)`. Use `Submodule.mem_sup_right ?_` and prove the remaining obligations. Establish `hne : h + (N : ℂ) ≠ h`.

Establish `: (N : ℂ) ≠ 0` using `by exact_mod_cast hpos.ne'`. Simplify using `using this`. Use `Submodule.mem_iSup_of_mem (h + (N : ℂ)) (Submodule.mem_iSup_of_mem hne ?_)` and prove the remaining obligations. Rewrite using `[Module.End.mem_eigenspace_iff]`. Conclude with `loweringWord_height hE hv hN`.

Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.1 (hle hx)`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hy`. Establish `hxe : x ∈ H.eigenspace h`. Rewrite using `[Module.End.mem_eigenspace_iff]`. Simplify using `[hH, hh, LinearMap.sum_apply, hw, Finset.sum_smul, mul_smul]`.

Establish `hve : v ∈ H.eigenspace h`. Rewrite using `[Module.End.mem_eigenspace_iff]`. Simplify using `[hH, hh, LinearMap.sum_apply, hv.1, Finset.sum_smul, mul_smul]`. Establish `hze : z ∈ H.eigenspace h`. Establish `: z = x - c • v` using `by rw [← hyz]; abel`.

Rewrite using `[this]`. Conclude with `Submodule.sub_mem _ hxe (Submodule.smul_mem _ _ hve)`. Establish `hd` using `Module.End.eigenspaces_iSupIndep H h`. Establish `hz0 : z = 0` using `(Submodule.disjoint_def.1 hd) z hze hz`. Conclude with `⟨c, by rw [← hyz, hz0, add_zero]⟩`.
-/
theorem exists_stable_submodule_topWeight_line :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
      (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
      ∃ S : Submodule ℂ V, (∀ a b, ∀ x ∈ S, E a b x ∈ S) ∧ v ∈ S ∧
        ∀ x ∈ S, (∀ a, E a a x = ν a • x) → ∃ c : ℂ, x = c • v := by
  intro V _ _ n E ν v hE hv
  refine ⟨Submodule.span ℂ {x | ∃ N, LoweringWord E v N x}, ?_,
    Submodule.subset_span ⟨0, LoweringWord.base⟩, ?_⟩
  · intro a b x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨N, hN⟩ := hx
      exact loweringWord_apply_mem hE hv hN a b
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · intro x hx hw
    set H : Module.End ℂ V := ∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a with hH
    set h : ℂ := ∑ a : Fin n, ((a.val : ℕ) : ℂ) * ν a with hh
    have hle : Submodule.span ℂ {x | ∃ N, LoweringWord E v N x}
        ≤ Submodule.span ℂ {v} ⊔ ⨆ (μ : ℂ) (_ : μ ≠ h), H.eigenspace μ := by
      rw [Submodule.span_le]
      rintro y ⟨N, hN⟩
      rcases loweringWord_zero_or_pos hN with rfl | hpos
      · exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
      · refine Submodule.mem_sup_right ?_
        have hne : h + (N : ℂ) ≠ h := by
          have : (N : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
          simpa using this
        refine Submodule.mem_iSup_of_mem (h + (N : ℂ)) (Submodule.mem_iSup_of_mem hne ?_)
        rw [Module.End.mem_eigenspace_iff]
        exact loweringWord_height hE hv hN
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hle hx)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hxe : x ∈ H.eigenspace h := by
      rw [Module.End.mem_eigenspace_iff]
      simp [hH, hh, LinearMap.sum_apply, hw, Finset.sum_smul, mul_smul]
    have hve : v ∈ H.eigenspace h := by
      rw [Module.End.mem_eigenspace_iff]
      simp [hH, hh, LinearMap.sum_apply, hv.1, Finset.sum_smul, mul_smul]
    have hze : z ∈ H.eigenspace h := by
      have : z = x - c • v := by rw [← hyz]; abel
      rw [this]
      exact Submodule.sub_mem _ hxe (Submodule.smul_mem _ _ hve)
    have hd := Module.End.eigenspaces_iSupIndep H h
    have hz0 : z = 0 := (Submodule.disjoint_def.1 hd) z hze hz
    exact ⟨c, by rw [← hyz, hz0, add_zero]⟩

end GlobalTheory
