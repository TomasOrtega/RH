import Mathlib

noncomputable def UpperTheory.Reformulated.B.ParabolicUnipotentGL.IsGlRep.{u_1} :
    {n : ℕ} →
      {M : Type u_1} → [inst : AddCommGroup M] → [inst_1 : _root_.Module ℂ M] → (Fin n → Fin n → Module.End ℂ M) → Prop :=
    fun {n : ℕ} {M : Type u_1} [AddCommGroup M] [_root_.Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) ↦
      ∀ (a b c d : Fin n),
        E a b * E c d - E c d * E a b =
          (if b = c then E a d else (0 : Module.End ℂ M)) - if d = a then E c b else (0 : Module.End ℂ M)

noncomputable def UpperTheory.Reformulated.B.ParabolicUnipotentGL.U :
    {n : ℕ} →
      {V : Type} →
        [inst : AddCommGroup V] →
          [inst_1 : _root_.Module ℂ V] → (Fin n → Fin n → Module.End ℂ V) → ℕ → Submodule ℂ (Module.End ℂ V) :=
    fun {n : ℕ} {V : Type} [AddCommGroup V] [_root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (k : ℕ) ↦
      Submodule.span ℂ
        {x : Module.End ℂ V |
          ∃ (l : List (Fin n × Fin n)), l.length ≤ k ∧ x = (List.map (fun (p : Fin n × Fin n) ↦ E p.1 p.2) l).prod}

namespace UpperTheory.Reformulated.B.ParabolicUnipotentGL

section helpers

variable {n : ℕ} {V : Type} [AddCommGroup V] [_root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)

private abbrev P (l : List (Fin n × Fin n)) : Module.End ℂ V :=
  (List.map (fun (p : Fin n × Fin n) ↦ E p.1 p.2) l).prod

/- English proof (translation)
Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `x ⟨l, hl, rfl⟩`. Conclude with `⟨l, hl.trans h, rfl⟩`.
-/
private theorem U_mono {j k : ℕ} (h : j ≤ k) : U E j ≤ U E k := by
  apply Submodule.span_mono
  rintro x ⟨l, hl, rfl⟩
  exact ⟨l, hl.trans h, rfl⟩

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨l, h, rfl⟩`.
-/
private theorem monomial_mem_filtration_of_length_le (l : List (Fin n × Fin n)) {k : ℕ} (h : l.length ≤ k) : P E l ∈ U E k :=
  Submodule.subset_span ⟨l, h, rfl⟩

/- English proof (translation)
Use `monomial_mem_filtration_of_length_le E [(a, b)] (k := 1) (by simp)` as an intermediate fact. Simplify `this` using `[P]`.
-/
private theorem gen_mem (a b : Fin n) : E a b ∈ U E 1 := by
  have := monomial_mem_filtration_of_length_le E [(a, b)] (k := 1) (by simp)
  simpa [P] using this

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨l, hl, rfl⟩` from `hx`.

Take `⟨m, hm, rfl⟩` from `hy`. Use `Submodule.subset_span ⟨l ++ m, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [List.length_append]`. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules.

Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [mul_add]`. Conclude with `add_mem ha hb`. Consider the case `smul c a _ ha => rw [mul_smul_comm]`. Conclude with `Submodule.smul_mem _ c ha`.

Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [add_mul]`. Conclude with `add_mem ha hb`. Consider the case `smul c a _ ha => rw [smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ c ha`.
-/
private theorem mul_mem_U {j k : ℕ} {x y : Module.End ℂ V} (hx : x ∈ U E j) (hy : y ∈ U E k) :
    x * y ∈ U E (j + k) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hx
      obtain ⟨m, hm, rfl⟩ := hy
      refine Submodule.subset_span ⟨l ++ m, ?_, ?_⟩
      · simp only [List.length_append]; omega
      · simp
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
    | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha
  | zero => simp
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ha

/- English proof (translation)
Rewrite using `[hE a b c d]`. Use `sub_mem ?_ ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `gen_mem E _ _`. Conclude with `zero_mem _`.

Use `split_ifs`. Conclude with `gen_mem E _ _`. Conclude with `zero_mem _`.
-/
private theorem gen_comm_mem (hE : IsGlRep E) (a b c d : Fin n) :
    E a b * E c d - E c d * E a b ∈ U E 1 := by
  rw [hE a b c d]
  refine sub_mem ?_ ?_
  · split_ifs
    · exact gen_mem E _ _
    · exact zero_mem _
  · split_ifs
    · exact gen_mem E _ _
    · exact zero_mem _

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp [P]`. Consider the case `cons p t ih`. Establish `e : E a b * P E (p :: t) - P E (p :: t) * E a b = (E a b * E p.1 p.2 - E p.1 p.2 * E a b) * P E t + E p.1 p.2 * (E a b * P E t - P E t * E a b)`. Simplify using `only [P, List.map_cons, List.prod_cons]`.

Use `noncomm_ring`. Rewrite using `[e, List.length_cons, add_comm t.length 1]`. Conclude with `add_mem (mul_mem_U E (gen_comm_mem E hE _ _ _ _) (monomial_mem_filtration_of_length_le E t le_rfl)) (mul_mem_U E (gen_mem E _ _) ih)`.
-/
private theorem gen_comm_P (hE : IsGlRep E) (a b : Fin n) (l : List (Fin n × Fin n)) :
    E a b * P E l - P E l * E a b ∈ U E l.length := by
  induction l with
  | nil => simp [P]
  | cons p t ih =>
    have e : E a b * P E (p :: t) - P E (p :: t) * E a b
        = (E a b * E p.1 p.2 - E p.1 p.2 * E a b) * P E t
          + E p.1 p.2 * (E a b * P E t - P E t * E a b) := by
      simp only [P, List.map_cons, List.prod_cons]
      noncomm_ring
    rw [e, List.length_cons, add_comm t.length 1]
    exact add_mem (mul_mem_U E (gen_comm_mem E hE _ _ _ _) (monomial_mem_filtration_of_length_le E t le_rfl))
      (mul_mem_U E (gen_mem E _ _) ih)

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp [P]`. Consider the case `cons p t ih`. Establish `e : P E (p :: t) * P E (q :: m) - P E (q :: m) * P E (p :: t) = E p.1 p.2 * (P E t * P E (q :: m) - P E (q :: m) * P E t) + (E p.1 p.2 * P E (q :: m) - P E (q :: m) * E p.1 p.2) * P E t`. Generalize the expression as in `P E (q :: m) = y`.

Simplify using `only [P, List.map_cons, List.prod_cons]`. Use `noncomm_ring`. Rewrite using `[e]`. Use `add_mem ?_ ?_` and prove the remaining obligations. Conclude with `U_mono E (by simp only [List.length_cons]; omega) (mul_mem_U E (gen_mem E _ _) ih)`.

Conclude with `U_mono E (by simp only [List.length_cons]; omega) (mul_mem_U E (gen_comm_P E hE _ _ (q :: m)) (monomial_mem_filtration_of_length_le E t le_rfl))`.
-/
private theorem monomial_commutator_mem_filtration (hE : IsGlRep E) (l : List (Fin n × Fin n)) (q : Fin n × Fin n)
    (m : List (Fin n × Fin n)) :
    P E l * P E (q :: m) - P E (q :: m) * P E l ∈ U E (l.length + m.length) := by
  induction l with
  | nil => simp [P]
  | cons p t ih =>
    have e : P E (p :: t) * P E (q :: m) - P E (q :: m) * P E (p :: t)
        = E p.1 p.2 * (P E t * P E (q :: m) - P E (q :: m) * P E t)
          + (E p.1 p.2 * P E (q :: m) - P E (q :: m) * E p.1 p.2) * P E t := by
      generalize P E (q :: m) = y
      simp only [P, List.map_cons, List.prod_cons]
      noncomm_ring
    rw [e]
    refine add_mem ?_ ?_
    · exact U_mono E (by simp only [List.length_cons]; omega) (mul_mem_U E (gen_mem E _ _) ih)
    · exact U_mono E (by simp only [List.length_cons]; omega)
        (mul_mem_U E (gen_comm_P E hE _ _ (q :: m)) (monomial_mem_filtration_of_length_le E t le_rfl))

end helpers

end UpperTheory.Reformulated.B.ParabolicUnipotentGL

/- English proof (translation)
Introduce `n V _ _ E hE j k x y hx hy`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨l, hl, rfl⟩` from `hx`. Take `⟨m, hm, rfl⟩` from `hy`. Consider the cases of `m with`. Consider the case `nil => simp`. Consider the case `cons q t`.

Simplify using `only [List.length_cons] at hm`. Conclude with `UpperTheory.Reformulated.B.ParabolicUnipotentGL.U_mono E (by omega) (UpperTheory.Reformulated.B.ParabolicUnipotentGL.monomial_commutator_mem_filtration E hE l q t)`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb`. Establish `e : x * (a + b) - (a + b) * x = (x * a - a * x) + (x * b - b * x)` using `by noncomm_ring`.

Rewrite using `[e]`. Conclude with `add_mem ha hb`. Consider the case `smul c a _ ha`. Establish `e : x * (c • a) - (c • a) * x = c • (x * a - a * x)`. Rewrite using `[mul_smul_comm, smul_mul_assoc, smul_sub]`.

Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ c ha`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb`. Establish `e : (a + b) * y - y * (a + b) = (a * y - y * a) + (b * y - y * b)` using `by noncomm_ring`.

Rewrite using `[e]`. Conclude with `add_mem ha hb`. Consider the case `smul c a _ ha`. Establish `e : (c • a) * y - y * (c • a) = c • (a * y - y * a)`. Rewrite using `[mul_smul_comm, smul_mul_assoc, smul_sub]`.

Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ c ha`.
-/
theorem UpperTheory.Reformulated.B.ParabolicUnipotentGL.main :
    ∀ {n : ℕ} {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
      UpperTheory.Reformulated.B.ParabolicUnipotentGL.IsGlRep E →
        ∀ {j k : ℕ} {x y : Module.End ℂ V},
          x ∈ UpperTheory.Reformulated.B.ParabolicUnipotentGL.U E j →
            y ∈ UpperTheory.Reformulated.B.ParabolicUnipotentGL.U E k → x * y - y * x ∈ UpperTheory.Reformulated.B.ParabolicUnipotentGL.U E (j + k - (1 : ℕ)) := by
  intro n V _ _ E hE j k x y hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hx
      obtain ⟨m, hm, rfl⟩ := hy
      cases m with
      | nil => simp
      | cons q t =>
        simp only [List.length_cons] at hm
        exact UpperTheory.Reformulated.B.ParabolicUnipotentGL.U_mono E (by omega) (UpperTheory.Reformulated.B.ParabolicUnipotentGL.monomial_commutator_mem_filtration E hE l q t)
    | zero => simp
    | add a b _ _ ha hb =>
      have e : x * (a + b) - (a + b) * x = (x * a - a * x) + (x * b - b * x) := by noncomm_ring
      rw [e]; exact add_mem ha hb
    | smul c a _ ha =>
      have e : x * (c • a) - (c • a) * x = c • (x * a - a * x) := by
        rw [mul_smul_comm, smul_mul_assoc, smul_sub]
      rw [e]; exact Submodule.smul_mem _ c ha
  | zero => simp
  | add a b _ _ ha hb =>
    have e : (a + b) * y - y * (a + b) = (a * y - y * a) + (b * y - y * b) := by noncomm_ring
    rw [e]; exact add_mem ha hb
  | smul c a _ ha =>
    have e : (c • a) * y - y * (c • a) = c • (a * y - y * a) := by
      rw [mul_smul_comm, smul_mul_assoc, smul_sub]
    rw [e]; exact Submodule.smul_mem _ c ha
