import Formalism.PieriBlockIdeals.StatementLP
import Formalism.PieriBlockIdeals.PieriColumnMinors.BinaryFormsExample

namespace Formalism.CohomologicalDescent.LP

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

section Gen

variable {A R : Type*} [Ring A] [DecidableEq R]

/- English proof (translation)
Introduce `a b c d`. Establish `h1` using `hP a b c d`. Establish `h2` using `hQ a b c d`. Establish `h3` using `(hPQ a b c d).eq`. Establish `h4` using `(hPQ c d a b).eq`.

Use `show (P a b + Q a b) * (P c d + Q c d) - (P c d + Q c d) * (P a b + Q a b) = (if b = c then P a d + Q a d else 0) - (if d = a then P c b + Q c b else 0)`. Establish `e : (P a b + Q a b) * (P c d + Q c d) - (P c d + Q c d) * (P a b + Q a b) = (P a b * P c d - P c d * P a b) + (Q a b * Q c d - Q c d * Q a b) + (P a b * Q c d - Q c d * P a b) + (Q a b * P c d - P c d * Q a b)` using `by noncomm_ring`. Rewrite using `[e, h1, h2, h3, h4]`. Simplify using `only [sub_self, add_zero]`. Apply the tactic sequence `split_ifs <;> abel`.
-/
theorem lpc_glrel_add (P Q : R → R → A) (hP : GlRel P) (hQ : GlRel Q) (hPQ : ∀ a b c d, Commute (P a b) (Q c d)) :
    GlRel (fun a b => P a b + Q a b) := by
  intro a b c d
  have h1 := hP a b c d
  have h2 := hQ a b c d
  have h3 := (hPQ a b c d).eq
  have h4 := (hPQ c d a b).eq
  show (P a b + Q a b) * (P c d + Q c d) - (P c d + Q c d) * (P a b + Q a b) =
    (if b = c then P a d + Q a d else 0) - (if d = a then P c b + Q c b else 0)
  have e : (P a b + Q a b) * (P c d + Q c d) - (P c d + Q c d) * (P a b + Q a b) =
      (P a b * P c d - P c d * P a b) + (Q a b * Q c d - Q c d * Q a b) + (P a b * Q c d - Q c d * P a b) +
        (Q a b * P c d - P c d * Q a b) := by noncomm_ring
  rw [e, h1, h2, h3, h4]
  simp only [sub_self, add_zero]
  split_ifs <;> abel

end Gen

section TensOps

variable (K : Type*) {R P M : Type*} [CommRing K] [AddCommGroup M] [Module K M] [DecidableEq R] [DecidableEq P] {n : ℕ}

/- English proof (translation)
Simplify using `[Dpart]`.
-/
theorem lpc_Dpart_zero (EM : R → R → Module.End K M) (a b : R) :
    (Dpart K EM 0 a b : Module.End K (Tens R P M n)) = onM K (EM a b) := by
  simp [Dpart]

/- English proof (translation)
Unfold `Dpart`. Rewrite using `[add_assoc]`. Use `congr 1`. Rewrite using `[Finset.sum_filter, Finset.sum_filter]`. Establish `key : ∀ s : Fin n, (if s.val < j + 1 then unitY K s a b else 0 : Module.End K (Tens R P M n)) = (if s.val < j then unitY K s a b else 0) + (if s.val = j then unitY K s a b else 0)`.

Introduce `s`. Break down `lt_trichotomy s.val j with h | h | h` into its components or cases. Establish `h1 : s.val < j + 1` using `by omega`. Establish `h3 : ¬ s.val = j` using `by omega`. Simplify using `[h, h1, h3]`.

Simplify using `[h]`. Establish `h1 : ¬ s.val < j + 1` using `by omega`. Establish `h2 : ¬ s.val < j` using `by omega`. Establish `h3 : ¬ s.val = j` using `by omega`. Simplify using `[h1, h2, h3]`.

Rewrite using `[Finset.sum_congr rfl (fun s _ => key s), Finset.sum_add_distrib]`. Use `congr 1`. Unfold `epsY`. Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single (⟨j, h⟩ : Fin n)]`.

Simplify using the standard rewrite rules. Introduce `s _ hs`. Rewrite using `[if_neg]`. Introduce `e`. Conclude with `hs (Fin.ext e)`.

Introduce `h'`. Conclude with `absurd (Finset.mem_univ _) h'`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `s _`. Rewrite using `[if_neg]`.

Use `s.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem lpc_Dpart_succ (EM : R → R → Module.End K M) (j : ℕ) (a b : R) :
    (Dpart K EM (j + 1) a b : Module.End K (Tens R P M n)) = Dpart K EM j a b + epsY K n j a b := by
  unfold Dpart
  rw [add_assoc]
  congr 1
  rw [Finset.sum_filter, Finset.sum_filter]
  have key : ∀ s : Fin n, (if s.val < j + 1 then unitY K s a b else 0 : Module.End K (Tens R P M n)) =
      (if s.val < j then unitY K s a b else 0) + (if s.val = j then unitY K s a b else 0) := by
    intro s
    rcases lt_trichotomy s.val j with h | h | h
    · have h1 : s.val < j + 1 := by omega
      have h3 : ¬ s.val = j := by omega
      simp [h, h1, h3]
    · simp [h]
    · have h1 : ¬ s.val < j + 1 := by omega
      have h2 : ¬ s.val < j := by omega
      have h3 : ¬ s.val = j := by omega
      simp [h1, h2, h3]
  rw [Finset.sum_congr rfl (fun s _ => key s), Finset.sum_add_distrib]
  congr 1
  unfold epsY
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨j, h⟩ : Fin n)]
    · simp
    · intro s _ hs
      rw [if_neg]
      intro e
      exact hs (Fin.ext e)
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · apply Finset.sum_eq_zero
    intro s _
    rw [if_neg]
    have := s.2
    omega

/- English proof (translation)
Distinguish the cases in `hj : j < n`. Simplify using `only [epsY, dif_pos hj]`. Conclude with `unitSecond_mul_unitSecond K _ a b c d`. Simplify using `[epsY, hj]`.
-/
theorem lpc_eps_mul (j : ℕ) (a b c d : R) :
    (epsY K n j a b * epsY K n j c d : Module.End K (Tens R P M n)) = if b = c then epsY K n j a d else 0 := by
  by_cases hj : j < n
  · simp only [epsY, dif_pos hj]
    exact unitSecond_mul_unitSecond K _ a b c d
  · simp [epsY, hj]

/- English proof (translation)
Introduce `a b c d`. Rewrite using `[lpc_eps_mul, lpc_eps_mul]`.
-/
theorem lpc_eps_glrel (j : ℕ) : GlRel (epsY K n j : R → R → Module.End K (Tens R P M n)) := by
  intro a b c d
  rw [lpc_eps_mul, lpc_eps_mul]

/- English proof (translation)
Unfold `epsY`. Use `split_ifs with h`. Unfold `Dpart`. Use `(onModule_commute_unitSecond K _ _ _ _).add_left (Commute.sum_left _ _ _ fun s hs => ?_)` and prove the remaining obligations. Use `unitSecond_commute_of_ne K ?_ _ _ _ _` and prove the remaining obligations.

Introduce `e`. Establish `h1` using `(Finset.mem_filter.1 hs).2`. Rewrite `h1` using `[e]`. Simplify using `at h1`. Use linear arithmetic over natural numbers and integers.

Conclude with `Commute.zero_right _`.
-/
theorem lpc_Dpart_comm_eps (EM : R → R → Module.End K M) (i j : ℕ) (hij : i ≤ j) (a b c d : R) :
    Commute (Dpart K EM i a b : Module.End K (Tens R P M n)) (epsY K n j c d) := by
  unfold epsY
  split_ifs with h
  · unfold Dpart
    refine (onModule_commute_unitSecond K _ _ _ _).add_left (Commute.sum_left _ _ _ fun s hs => ?_)
    refine unitSecond_commute_of_ne K ?_ _ _ _ _
    intro e
    have h1 := (Finset.mem_filter.1 hs).2
    rw [e] at h1
    simp at h1
    omega
  · exact Commute.zero_right _

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Establish `e : (Dpart K EM 0 : R → R → Module.End K (Tens R P M n)) = fun a b => onM K (EM a b)`. Use function extensionality and compare the values at `a b`. Conclude with `lpc_Dpart_zero K EM a b`.

Rewrite using `[e]`. Conclude with `onModule_gl_relations K h`. Consider the case `succ j ih`. Establish `e : (Dpart K EM (j + 1) : R → R → Module.End K (Tens R P M n)) = fun a b => Dpart K EM j a b + epsY K n j a b`. Use function extensionality and compare the values at `a b`.

Conclude with `lpc_Dpart_succ K EM j a b`. Rewrite using `[e]`. Conclude with `lpc_glrel_add _ _ ih (lpc_eps_glrel K j) (fun a b c d => lpc_Dpart_comm_eps K EM j j le_rfl a b c d)`.
-/
theorem lpc_Dpart_glrel {EM : R → R → Module.End K M} (h : GlRel EM) (j : ℕ) :
    GlRel (Dpart K EM j : R → R → Module.End K (Tens R P M n)) := by
  induction j with
  | zero =>
    have e : (Dpart K EM 0 : R → R → Module.End K (Tens R P M n)) = fun a b => onM K (EM a b) := by
      funext a b
      exact lpc_Dpart_zero K EM a b
    rw [e]
    exact onModule_gl_relations K h
  | succ j ih =>
    have e : (Dpart K EM (j + 1) : R → R → Module.End K (Tens R P M n)) =
        fun a b => Dpart K EM j a b + epsY K n j a b := by
      funext a b
      exact lpc_Dpart_succ K EM j a b
    rw [e]
    exact lpc_glrel_add _ _ ih (lpc_eps_glrel K j) (fun a b c d => lpc_Dpart_comm_eps K EM j j le_rfl a b c d)

/- English proof (translation)
Rewrite using `[unitOnTensor_apply]`. Use `split_ifs with h`. Use `congr 1`. Rewrite using `[← h]`. Conclude with `Function.update_eq_self _ _`.

Both sides reduce to the same expression.
-/
theorem lpc_unitY_diag (s : Fin n) (a : R) (z : Tens R P M n) (g : Fin n → R × P) :
    unitY K s a a z g = if (g s).1 = a then z g else 0 := by
  rw [unitOnTensor_apply]
  split_ifs with h
  · congr 1
    rw [← h]
    exact Function.update_eq_self _ _
  · rfl

/- English proof (translation)
Use `LinearMap.ext fun z => funext fun g => ?_` and prove the remaining obligations. Simplify using `only [epsY, dif_pos hj, LinearMap.sum_apply, Finset.sum_apply, lpc_unitY_diag, Module.End.one_apply]`. Simplify using the standard rewrite rules.
-/
theorem lpc_eps_one [Fintype R] (j : ℕ) (hj : j < n) :
    (∑ a, epsY K n j a a : Module.End K (Tens R P M n)) = 1 := by
  refine LinearMap.ext fun z => funext fun g => ?_
  simp only [epsY, dif_pos hj, LinearMap.sum_apply, Finset.sum_apply, lpc_unitY_diag, Module.End.one_apply]
  simp

def lpc_cnt (j : ℕ) (a : R) (g : Fin n → R × P) : ℕ :=
  ((Finset.univ.filter (fun s : Fin n => s.val < j)).filter (fun s => (g s).1 = a)).card

/- English proof (translation)
Unfold `Dpart`. Rewrite using `[LinearMap.add_apply, Pi.add_apply, LinearMap.sum_apply, Finset.sum_apply, onModule_apply]`. Use `congr 1`. Simplify using `only [lpc_unitY_diag]`. Rewrite using `[← Finset.sum_filter, Finset.sum_const, lpc_cnt, Nat.cast_smul_eq_nsmul]`.
-/
theorem lpc_Dpart_diag (EM : R → R → Module.End K M) (j : ℕ) (a : R) (z : Tens R P M n) (g : Fin n → R × P) :
    Dpart K EM j a a z g = EM a a (z g) + (lpc_cnt j a g : K) • z g := by
  unfold Dpart
  rw [LinearMap.add_apply, Pi.add_apply, LinearMap.sum_apply, Finset.sum_apply, onModule_apply]
  congr 1
  simp only [lpc_unitY_diag]
  rw [← Finset.sum_filter, Finset.sum_const, lpc_cnt, Nat.cast_smul_eq_nsmul]

end TensOps

/- English proof (translation)
Introduce `K P M q _ _ _ _ EM n κ h z μ hz hw`. Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : ∃ g, z g ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hz (funext hc)`.

Use `h (z g) μ hg ⟨?_, ?_⟩` and prove the remaining obligations. Introduce `a b hab`. Use `congrFun (hw.1 a b hab) g` as an intermediate fact. Rewrite `this` using `[lpc_Dpart_zero]`. Then use the resulting hypothesis. Introduce `a`.

Use `congrFun (hw.2 a) g` as an intermediate fact. Rewrite `this` using `[lpc_Dpart_zero]`. Then use the resulting hypothesis.
-/
theorem tensor_base_case : TensBase := by
  intro K P M q _ _ _ _ EM n κ h z μ hz hw
  obtain ⟨g, hg⟩ : ∃ g, z g ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hz (funext hc)
  refine h (z g) μ hg ⟨?_, ?_⟩
  · intro a b hab
    have := congrFun (hw.1 a b hab) g
    rwa [lpc_Dpart_zero] at this
  · intro a
    have := congrFun (hw.2 a) g
    rwa [lpc_Dpart_zero] at this

section Form

variable {K R P M : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup M] [Module K M]
  [Fintype R] [Fintype P] [DecidableEq R] [DecidableEq P] {n : ℕ}

/- English proof (translation)
Simplify using `[tensForm, LinearMap.sum_apply, LinearMap.BilinForm.comp_apply]`.
-/
theorem lpc_form_apply (B : LinearMap.BilinForm K M) (x y : Tens R P M n) :
    tensForm n B x y = ∑ g, B (x g) (y g) := by
  simp [tensForm, LinearMap.sum_apply, LinearMap.BilinForm.comp_apply]

/- English proof (translation)
Rewrite using `[lpc_form_apply, lpc_form_apply]`. Simplify using `only [unitOnTensor_apply]`. Establish `e1 : ∀ g : Fin n → R × P, B (if (g s).1 = a then x (Function.update g s (b, (g s).2)) else 0) (y g) = if (g s).1 = a then B (x (Function.update g s (b, (g s).2))) (y g) else 0`. Introduce `g`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `e2 : ∀ g : Fin n → R × P, B (x g) (if (g s).1 = b then y (Function.update g s (a, (g s).2)) else 0) = if (g s).1 = b then B (x g) (y (Function.update g s (a, (g s).2))) else 0`. Introduce `g`. Apply the tactic sequence `split_ifs <;> simp`. Simplify using `only [e1, e2]`. Rewrite using `[← Finset.sum_filter, ← Finset.sum_filter]`.

Use `Finset.sum_nbij' (fun g => Function.update g s (b, (g s).2)) (fun g => Function.update g s (a, (g s).2)) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `g _`. Simplify using the standard rewrite rules. Introduce `g _`. Simplify using the standard rewrite rules.

Introduce `g hg`. Establish `hg' : (g s).1 = a` using `(Finset.mem_filter.1 hg).2`. Simplify using `only [Function.update_self, Function.update_idem]`. Rewrite using `[← hg']`. Conclude with `Function.update_eq_self _ _`.

Introduce `g hg`. Establish `hg' : (g s).1 = b` using `(Finset.mem_filter.1 hg).2`. Simplify using `only [Function.update_self, Function.update_idem]`. Rewrite using `[← hg']`. Conclude with `Function.update_eq_self _ _`.

Introduce `g hg`. Establish `hg' : (g s).1 = a` using `(Finset.mem_filter.1 hg).2`. Simplify using `only [Function.update_self, Function.update_idem]`. Use `congr 2`. Rewrite using `[← hg']`.

Conclude with `(Function.update_eq_self _ _).symm`.
-/
theorem lpc_form_unitY (B : LinearMap.BilinForm K M) (s : Fin n) (a b : R) (x y : Tens R P M n) :
    tensForm n B (unitY K s a b x) y = tensForm n B x (unitY K s b a y) := by
  rw [lpc_form_apply, lpc_form_apply]
  simp only [unitOnTensor_apply]
  have e1 : ∀ g : Fin n → R × P, B (if (g s).1 = a then x (Function.update g s (b, (g s).2)) else 0) (y g) =
      if (g s).1 = a then B (x (Function.update g s (b, (g s).2))) (y g) else 0 := by
    intro g
    split_ifs <;> simp
  have e2 : ∀ g : Fin n → R × P, B (x g) (if (g s).1 = b then y (Function.update g s (a, (g s).2)) else 0) =
      if (g s).1 = b then B (x g) (y (Function.update g s (a, (g s).2))) else 0 := by
    intro g
    split_ifs <;> simp
  simp only [e1, e2]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun g => Function.update g s (b, (g s).2)) (fun g => Function.update g s (a, (g s).2)) ?_ ?_ ?_ ?_ ?_
  · intro g _
    simp
  · intro g _
    simp
  · intro g hg
    have hg' : (g s).1 = a := (Finset.mem_filter.1 hg).2
    simp only [Function.update_self, Function.update_idem]
    rw [← hg']
    exact Function.update_eq_self _ _
  · intro g hg
    have hg' : (g s).1 = b := (Finset.mem_filter.1 hg).2
    simp only [Function.update_self, Function.update_idem]
    rw [← hg']
    exact Function.update_eq_self _ _
  · intro g hg
    have hg' : (g s).1 = a := (Finset.mem_filter.1 hg).2
    simp only [Function.update_self, Function.update_idem]
    congr 2
    rw [← hg']
    exact (Function.update_eq_self _ _).symm

end Form

/- English proof (translation)
The claim follows from `lpc_Dpart_glrel K h.gl j symm := by intro x y rw [lpc_form_apply, lpc_form_apply] exact Finset.sum_congr rfl fun g _ => h.symm _ _ pos := by intro x hx obtain ⟨g, hg⟩ : ∃ g, x g ≠ 0 := by by_contra hc push Not at hc exact hx (funext hc) rw [lpc_form_apply] refine Finset.sum_pos' …`.
-/
theorem lpc_formMod {K P M : Type} {q : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup M] [Module K M]
    [DecidableEq P] [Fintype P] (EM : Fin q → Fin q → Module.End K M) (B : LinearMap.BilinForm K M) (n : ℕ) (h : FormMod EM B)
    (j : ℕ) : FormMod (Dpart K EM j : Fin q → Fin q → Module.End K (Tens (Fin q) P M n)) (tensForm n B) where
  gl := lpc_Dpart_glrel K h.gl j
  symm := by
    intro x y
    rw [lpc_form_apply, lpc_form_apply]
    exact Finset.sum_congr rfl fun g _ => h.symm _ _
  pos := by
    intro x hx
    obtain ⟨g, hg⟩ : ∃ g, x g ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hx (funext hc)
    rw [lpc_form_apply]
    refine Finset.sum_pos' ?_ ⟨g, Finset.mem_univ _, h.pos _ hg⟩
    intro g' _
    by_cases h0 : x g' = 0
    · simp [h0]
    · exact (h.pos _ h0).le
  adj := by
    intro a b x y
    unfold Dpart
    simp only [LinearMap.add_apply, map_add, LinearMap.sum_apply, map_sum, lpc_form_unitY]
    congr 1
    rw [lpc_form_apply, lpc_form_apply]
    exact Finset.sum_congr rfl fun g _ => h.adj a b _ _
  diag := by
    intro a
    rw [eq_top_iff]
    intro z _
    have hz : z = ∑ g, LinearMap.single K (fun _ : Fin n → Fin q × P => M) g (z g) := by
      funext g'
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hz]
    refine Submodule.sum_mem _ fun g _ => ?_
    have hm : z g ∈ ⨆ μ : K, Module.End.eigenspace (EM a a) μ := by
      rw [h.diag a]
      trivial
    refine Submodule.iSup_induction (motive := fun m => LinearMap.single K (fun _ : Fin n → Fin q × P => M) g m ∈
      ⨆ μ : K, Module.End.eigenspace (Dpart K EM j a a : Module.End K (Tens (Fin q) P M n)) μ) _ hm ?_ ?_ ?_
    · intro μ m hμ
      refine Submodule.mem_iSup_of_mem (μ + (lpc_cnt j a g : K)) ?_
      rw [Module.End.mem_eigenspace_iff] at hμ ⊢
      funext g'
      rw [lpc_Dpart_diag]
      by_cases hg : g' = g
      · subst hg
        simp [hμ, add_smul]
      · simp [hg]
    · simp
    · intro m1 m2 h1 h2
      rw [map_add]
      exact Submodule.add_mem _ h1 h2

/- English proof (translation)
Introduce `K P M q _ _ _ _ _ _ _ EM B n h`. Conclude with `{ form := fun j _ => lpc_formMod EM B n h j step := fun j _ a b => lpc_Dpart_succ K EM j a b unit_mul := fun j _ a b c d => lpc_eps_mul K j a b c d unit_one := fun j hj => lpc_eps_one K j hj comm := fun i j hij _ a b c d => lpc_Dpart_comm_eps K EM i j hij a b c d }`.
-/
theorem tensor_tower : TensTower := by
  intro K P M q _ _ _ _ _ _ _ EM B n h
  exact
    { form := fun j _ => lpc_formMod EM B n h j
      step := fun j _ a b => lpc_Dpart_succ K EM j a b
      unit_mul := fun j _ a b c d => lpc_eps_mul K j a b c d
      unit_one := fun j hj => lpc_eps_one K j hj
      comm := fun i j hij _ a b c d => lpc_Dpart_comm_eps K EM i j hij a b c d }

end Formalism.CohomologicalDescent.LP
