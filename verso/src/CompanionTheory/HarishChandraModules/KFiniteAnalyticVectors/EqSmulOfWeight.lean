import Formalism.HermitianCurvature.CapelliDeterminantAndBranching

open Formalism.REAL Formalism.FourierDecayAlt.Qr

noncomputable section

namespace CompanionTheory.D.gk.HwAlg

variable {U : Type} [AddCommGroup U] [Module ℂ U] {n : ℕ}

def Lower (l : List (Fin n × Fin n)) : Prop := ∀ p ∈ l, p.2 < p.1

def word (F : Fin n → Fin n → Module.End ℂ U) (l : List (Fin n × Fin n)) : Module.End ℂ U :=
  (l.map fun p => F p.1 p.2).prod

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma word_nil (F : Fin n → Fin n → Module.End ℂ U) : word F [] = 1 := rfl

/- English proof (translation)
Simplify using `[word]`.
-/
@[simp] lemma word_cons (F : Fin n → Fin n → Module.End ℂ U) (p : Fin n × Fin n) (l : List (Fin n × Fin n)) :
    word F (p :: l) = F p.1 p.2 * word F l := by
  simp [word]

def lowSpan (F : Fin n → Fin n → Module.End ℂ U) (w : U) : Submodule ℂ U :=
  Submodule.span ℂ {x | ∃ l, Lower l ∧ x = word F l w}

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨l, hl, rfl⟩`.
-/
lemma word_mem (F : Fin n → Fin n → Module.End ℂ U) (w : U) {l : List (Fin n × Fin n)} (hl : Lower l) :
    word F l w ∈ lowSpan F w :=
  Submodule.subset_span ⟨l, hl, rfl⟩

/- English proof (translation)
Simplify using `using word_mem F w (l := []) (by simp [Lower])`.
-/
lemma self_mem (F : Fin n → Fin n → Module.End ℂ U) (w : U) : w ∈ lowSpan F w := by
  simpa using word_mem F w (l := []) (by simp [Lower])

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨l, hl, rfl⟩` from `hy`. Establish `: F a b (word F l w) = word F ((a, b) :: l) w` using `by simp`. Rewrite using `[this]`.

Use `word_mem F w ?_` and prove the remaining obligations. Introduce `p hp`. Break down `List.mem_cons.1 hp with rfl | hp` into its components or cases. Conclude with `hab`. Conclude with `hl p hp`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
lemma lower_mem (F : Fin n → Fin n → Module.End ℂ U) (w : U) {a b : Fin n} (hab : b < a) {x : U}
    (hx : x ∈ lowSpan F w) : F a b x ∈ lowSpan F w := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    have : F a b (word F l w) = word F ((a, b) :: l) w := by simp
    rw [this]
    refine word_mem F w ?_
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hab
    · exact hl p hp
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/- English proof (translation)
Establish `h` using `congrArg (fun T : Module.End ℂ U => T u) (hF i j a b)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at h`. Apply the tactic sequence `split_ifs at h ⊢ <;> simp_all [sub_eq_iff_eq_add, add_comm]`.
-/
lemma comm_apply {F : Fin n → Fin n → Module.End ℂ U} (hF : GlRel F) (i j a b : Fin n) (u : U) :
    F i j (F a b u) = F a b (F i j u) +
      ((if j = a then F i b u else 0) - (if b = i then F a j u else 0)) := by
  have h := congrArg (fun T : Module.End ℂ U => T u) (hF i j a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  split_ifs at h ⊢ <;> simp_all [sub_eq_iff_eq_add, add_comm]

variable {F : Fin n → Fin n → Module.End ℂ U} {ν : Fin n → ℂ} {w : U}

/- English proof (translation)
Introduce `l`. Proceed by induction on `l with`. Consider the case `nil`. Introduce `_ i j`. Simplify using `only [word_nil, Module.End.one_apply]`.

Break down `lt_trichotomy i j with h | rfl | h` into its components or cases. Rewrite using `[hw.2 i j h]`. Conclude with `Submodule.zero_mem _`. Rewrite using `[hw.1 i]`. Conclude with `Submodule.smul_mem _ _ (self_mem F w)`.

Conclude with `lower_mem F w h (self_mem F w)`. Consider the case `cons p l ih`. Introduce `hl i j`. Establish `hl' : Lower l` using `fun q hq => hl q (List.mem_cons_of_mem _ hq)`. Establish `hp : p.2 < p.1` using `hl p (by simp)`.

Rewrite using `[word_cons, Module.End.mul_apply, comm_apply hF]`. Use `Submodule.add_mem _ (lower_mem F w hp (ih hl' i j)) (Submodule.sub_mem _ ?_ ?_)` and prove the remaining obligations. Use `split_ifs`. Conclude with `ih hl' _ _`. Conclude with `Submodule.zero_mem _`.

Use `split_ifs`. Conclude with `ih hl' _ _`. Conclude with `Submodule.zero_mem _`.
-/
lemma gen_mem (hF : GlRel F) (hw : IsHW F ν w) :
    ∀ (l : List (Fin n × Fin n)), Lower l → ∀ i j, F i j (word F l w) ∈ lowSpan F w := by
  intro l
  induction l with
  | nil =>
    intro _ i j
    simp only [word_nil, Module.End.one_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [hw.2 i j h]; exact Submodule.zero_mem _
    · rw [hw.1 i]; exact Submodule.smul_mem _ _ (self_mem F w)
    · exact lower_mem F w h (self_mem F w)
  | cons p l ih =>
    intro hl i j
    have hl' : Lower l := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp : p.2 < p.1 := hl p (by simp)
    rw [word_cons, Module.End.mul_apply, comm_apply hF]
    refine Submodule.add_mem _ (lower_mem F w hp (ih hl' i j)) (Submodule.sub_mem _ ?_ ?_)
    · split_ifs
      · exact ih hl' _ _
      · exact Submodule.zero_mem _
    · split_ifs
      · exact ih hl' _ _
      · exact Submodule.zero_mem _

/- English proof (translation)
Introduce `i j x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨l, hl, rfl⟩` from `hy`. Conclude with `gen_mem hF hw l hl i j`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem stab_lowSpan (hF : GlRel F) (hw : IsHW F ν w) : Stab F (lowSpan F w) := by
  intro i j x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact gen_mem hF hw l hl i j
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

def wt (ν : Fin n → ℂ) : List (Fin n × Fin n) → Fin n → ℂ
  | [] => ν
  | p :: l => wt ν l + (Pi.single p.1 1 - Pi.single p.2 1)

/- English proof (translation)
Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => intro c`. Simplify `hw.1 c` using `[wt]`. Consider the case `cons p l ih`.

Introduce `c`. Rewrite using `[word_cons, Module.End.mul_apply, comm_apply hF, ih, map_smul]`. Simplify using `only [wt, Pi.add_apply, Pi.sub_apply, Pi.single_apply]`. Apply the tactic sequence `by_cases h1 : c = p.1 <;> by_cases h2 : p.2 = c`. Substitute `h1` using the available equality.

Rewrite `*` using `[h2]`. Simplify using the standard rewrite rules. Substitute `h1` using the available equality. Simplify using `[h2, Ne.symm h2, add_smul]`. Substitute `h2` using the available equality.

Simplify using `[h1, add_smul, sub_eq_add_neg]`. Simplify using `[h1, h2, Ne.symm h2]`.
-/
lemma diag_word (hF : GlRel F) (hw : IsHW F ν w) :
    ∀ (l : List (Fin n × Fin n)) (c : Fin n), F c c (word F l w) = wt ν l c • word F l w := by
  intro l
  induction l with
  | nil => intro c; simpa [wt] using hw.1 c
  | cons p l ih =>
    intro c
    rw [word_cons, Module.End.mul_apply, comm_apply hF, ih, map_smul]
    simp only [wt, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    by_cases h1 : c = p.1 <;> by_cases h2 : p.2 = c
    · subst h1; rw [h2] at *; simp
    · subst h1; simp [h2, Ne.symm h2, add_smul]
    · subst h2; simp [h1, add_smul, sub_eq_add_neg]
    · simp [h1, h2, Ne.symm h2]

def hgt (μ : Fin n → ℂ) : ℂ := ∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) * μ c

/- English proof (translation)
Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => intro`. Simplify using `[wt]`. Consider the case `cons p l ih`.

Introduce `hl`. Establish `hl' : Lower l` using `fun q hq => hl q (List.mem_cons_of_mem _ hq)`. Establish `hp : p.2 < p.1` using `hl p (by simp)`. Establish `hsum : hgt (wt ν (p :: l)) = hgt (wt ν l) + (((p.2 : ℕ) : ℂ) - ((p.1 : ℕ) : ℂ))`. Simplify using `only [hgt, wt, Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsum, Complex.add_re, Complex.sub_re, Complex.natCast_re, Complex.natCast_re]`. Establish `: ((p.2 : ℕ) : ℝ) + 1 ≤ ((p.1 : ℕ) : ℝ)` using `by exact_mod_cast hp`. Use `ih hl'` as an intermediate fact. Simplify using `only [List.length_cons, Nat.cast_add, Nat.cast_one]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma hgt_wt_re (ν : Fin n → ℂ) :
    ∀ l : List (Fin n × Fin n), Lower l → (hgt (wt ν l)).re ≤ (hgt ν).re - l.length := by
  intro l
  induction l with
  | nil => intro; simp [wt]
  | cons p l ih =>
    intro hl
    have hl' : Lower l := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp : p.2 < p.1 := hl p (by simp)
    have hsum : hgt (wt ν (p :: l)) = hgt (wt ν l) + (((p.2 : ℕ) : ℂ) - ((p.1 : ℕ) : ℂ)) := by
      simp only [hgt, wt, Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      ring
    rw [hsum, Complex.add_re, Complex.sub_re, Complex.natCast_re, Complex.natCast_re]
    have : ((p.2 : ℕ) : ℝ) + 1 ≤ ((p.1 : ℕ) : ℝ) := by exact_mod_cast hp
    have := ih hl'
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

def hOp (F : Fin n → Fin n → Module.End ℂ U) : Module.End ℂ U :=
  ∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) • F c c

/- English proof (translation)
Simplify using `only [hOp, LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul, hgt, Finset.sum_smul]`.
-/
lemma hOp_of_diag {x : U} {μ : Fin n → ℂ} (hx : ∀ c, F c c x = μ c • x) : hOp F x = hgt μ • x := by
  simp only [hOp, LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul, hgt, Finset.sum_smul]

/- English proof (translation)
Use `set S1 : Set U := {y | ∃ l, Lower l ∧ l ≠ [] ∧ y = word F l w} with hS1`. Establish `hset : {y | ∃ l, Lower l ∧ y = word F l w} = insert w S1`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨l, hl, rfl⟩`.

Break down `l with _ | ⟨p, l⟩` into its components or cases. Use `left`. Simplify using the standard rewrite rules. Use the proof step `right; exact ⟨p :: l, hl, by simp, rfl⟩`. Introduce and unpack `(rfl | ⟨l, hl, -, rfl⟩)`.

Conclude with `⟨[], by simp [Lower], by simp⟩`. Conclude with `⟨l, hl, rfl⟩`. Rewrite `hx` using `[lowSpan, hset, Submodule.mem_span_insert]`. Take `⟨t, y, hy, rfl⟩` from `hx`. Use `⟨t, ?_⟩` and prove the remaining obligations.

It suffices to establish `y = 0 by rw [this, add_zero]`. Establish `hy1 : y ∈ ⨆ (μ : ℂ) (_ : μ ≠ hgt ν), (hOp F).eigenspace μ`. Use `(Submodule.span_le.2 ?_) hy` and prove the remaining obligations. Introduce and unpack `z ⟨l, hl, hne, rfl⟩`. Establish `hre` using `hgt_wt_re ν l hl`.

Establish `hlen : (1 : ℝ) ≤ l.length`. Break down `l with _ | ⟨p, l⟩` into its components or cases. Conclude with `absurd rfl hne`. Simplify using the standard rewrite rules. Establish `hne' : hgt (wt ν l) ≠ hgt ν`.

Introduce `h`. Rewrite `hre` using `[h]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `Submodule.mem_iSup_of_mem (hgt (wt ν l)) (Submodule.mem_iSup_of_mem hne' ?_)` and prove the remaining obligations. Rewrite using `[Module.End.mem_eigenspace_iff]`.

Conclude with `hOp_of_diag (diag_word hF hw l)`. Establish `hy2 : y ∈ (hOp F).eigenspace (hgt ν)`. Rewrite using `[Module.End.mem_eigenspace_iff]`. Establish `h1 : hOp F (t • w + y) = hgt ν • (t • w + y)` using `hOp_of_diag hxν`. Establish `h2 : hOp F w = hgt ν • w` using `hOp_of_diag hw.1`.

Rewrite `h1` using `[map_add, map_smul, h2, smul_add, smul_comm]`. Conclude with `add_left_cancel h1`. Establish `hdisj` using `(Module.End.eigenspaces_iSupIndep (hOp F)) (hgt ν)`. Conclude with `(Submodule.disjoint_def.1 hdisj) y hy2 hy1`.
-/
theorem eq_smul_of_weight (hF : GlRel F) (hw : IsHW F ν w) {x : U} (hx : x ∈ lowSpan F w)
    (hxν : ∀ c, F c c x = ν c • x) : ∃ t : ℂ, x = t • w := by
  set S1 : Set U := {y | ∃ l, Lower l ∧ l ≠ [] ∧ y = word F l w} with hS1
  have hset : {y | ∃ l, Lower l ∧ y = word F l w} = insert w S1 := by
    ext y; constructor
    · rintro ⟨l, hl, rfl⟩
      rcases l with _ | ⟨p, l⟩
      · left; simp
      · right; exact ⟨p :: l, hl, by simp, rfl⟩
    · rintro (rfl | ⟨l, hl, -, rfl⟩)
      · exact ⟨[], by simp [Lower], by simp⟩
      · exact ⟨l, hl, rfl⟩
  rw [lowSpan, hset, Submodule.mem_span_insert] at hx
  obtain ⟨t, y, hy, rfl⟩ := hx
  refine ⟨t, ?_⟩
  suffices y = 0 by rw [this, add_zero]

  have hy1 : y ∈ ⨆ (μ : ℂ) (_ : μ ≠ hgt ν), (hOp F).eigenspace μ := by
    refine (Submodule.span_le.2 ?_) hy
    rintro z ⟨l, hl, hne, rfl⟩
    have hre := hgt_wt_re ν l hl
    have hlen : (1 : ℝ) ≤ l.length := by
      rcases l with _ | ⟨p, l⟩
      · exact absurd rfl hne
      · simp
    have hne' : hgt (wt ν l) ≠ hgt ν := by
      intro h; rw [h] at hre; linarith
    refine Submodule.mem_iSup_of_mem (hgt (wt ν l)) (Submodule.mem_iSup_of_mem hne' ?_)
    rw [Module.End.mem_eigenspace_iff]
    exact hOp_of_diag (diag_word hF hw l)

  have hy2 : y ∈ (hOp F).eigenspace (hgt ν) := by
    rw [Module.End.mem_eigenspace_iff]
    have h1 : hOp F (t • w + y) = hgt ν • (t • w + y) := hOp_of_diag hxν
    have h2 : hOp F w = hgt ν • w := hOp_of_diag hw.1
    rw [map_add, map_smul, h2, smul_add, smul_comm] at h1
    exact add_left_cancel h1
  have hdisj := (Module.End.eigenspaces_iSupIndep (hOp F)) (hgt ν)
  exact (Submodule.disjoint_def.1 hdisj) y hy2 hy1

end CompanionTheory.D.gk.HwAlg
