import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.MemLAOfNsmul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.WBasis

noncomputable section

open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk

namespace PI.ScRefExists.WF

variable {I : Formalism.MainNotions.S.AutInst} {p : ℕ}

section Frame

variable {r k : ℕ} {e f : Fin r → Fin I.n → I.E} {w : Fin (k + 1) → Fin I.n → I.E}

def fam (e f : Fin r → Fin I.n → I.E) (w : Fin (k + 1) → Fin I.n → I.E) :
    Fin r ⊕ (Fin r ⊕ Fin (k + 1)) → Fin I.n → I.E :=
  Sum.elim e (Sum.elim f w)

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Simplify using `only [fam, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at hg`. Establish `hfe : ∀ a b, hG I (f a) (e b) = if a = b then 1 else 0`. Introduce `a b`.

Rewrite using `[hG_symm I (e b) (f a), hef b a]`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`.

Establish `hb : ∀ a, g (Sum.inr (Sum.inl a)) = 0`. Introduce `a`. Establish `hw1 : ∀ i, hG I (e a) (w i) = 0` using `fun i => (hw i a).1`. Establish `h1` using `congrArg (hG I (e a)) hg`. Simplify `h1` using `[hG_add_right, hG_sum_right, hG_smul_right, he, hef, hw1, hG_zero_right]`.

Establish `ha : ∀ a, g (Sum.inl a) = 0`. Introduce `a`. Establish `hw2 : ∀ i, hG I (f a) (w i) = 0` using `fun i => (hw i a).2`. Establish `h1` using `congrArg (hG I (f a)) hg`. Simplify `h1` using `[hG_add_right, hG_sum_right, hG_smul_right, hf, hfe, hw2, hG_zero_right]`.

Simplify using `only [ha, hb, zero_smul, Finset.sum_const_zero, zero_add] at hg`. Establish `hc` using `Fintype.linearIndependent_iff.1 hli (fun i => g (Sum.inr (Sum.inr i))) hg`. Introduce `i`. Break down `i with a | a | i` into its components or cases. Conclude with `ha a`.

Conclude with `hb a`. Conclude with `hc i`.
-/
theorem fam_li (he : ∀ a b, hG I (e a) (e b) = 0) (hf : ∀ a b, hG I (f a) (f b) = 0)
    (hef : ∀ a b, hG I (e a) (f b) = if a = b then 1 else 0)
    (hw : ∀ i a, hG I (e a) (w i) = 0 ∧ hG I (f a) (w i) = 0) (hli : LinearIndependent I.E w) :
    LinearIndependent I.E (fam e f w) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [fam, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at hg
  have hfe : ∀ a b, hG I (f a) (e b) = if a = b then 1 else 0 := by
    intro a b
    rw [hG_symm I (e b) (f a), hef b a]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  have hb : ∀ a, g (Sum.inr (Sum.inl a)) = 0 := by
    intro a
    have hw1 : ∀ i, hG I (e a) (w i) = 0 := fun i => (hw i a).1
    have h1 := congrArg (hG I (e a)) hg
    simpa [hG_add_right, hG_sum_right, hG_smul_right, he, hef, hw1, hG_zero_right] using h1
  have ha : ∀ a, g (Sum.inl a) = 0 := by
    intro a
    have hw2 : ∀ i, hG I (f a) (w i) = 0 := fun i => (hw i a).2
    have h1 := congrArg (hG I (f a)) hg
    simpa [hG_add_right, hG_sum_right, hG_smul_right, hf, hfe, hw2, hG_zero_right] using h1
  simp only [ha, hb, zero_smul, Finset.sum_const_zero, zero_add] at hg
  have hc := Fintype.linearIndependent_iff.1 hli (fun i => g (Sum.inr (Sum.inr i))) hg
  intro i
  rcases i with a | a | i
  · exact ha a
  · exact hb a
  · exact hc i

/- English proof (translation)
Rewrite using `[← I.L_span, Submodule.span_le]`. Introduce `y hy`. Establish `hyA : y ∈ LA I p` using `L_le_LA hy`. Establish `hz : y - proj e f y ∈ Submodule.span (Ap I p) (Set.range w)`. Apply `hW _ (sub_mem hyA (proj_mem hp heA hfA hyA))` to reduce the goal to its premises.

Introduce `a`. Rewrite using `[hG_sub_right, hG_sub_right, hG_e_proj he hef, hG_f_proj hf hef, sub_self, sub_self]`. Conclude with `⟨rfl, rfl⟩`. Establish `key : ∀ z ∈ Submodule.span (Ap I p) (Set.range w), z ∈ Submodule.span I.E (Set.range (fam e f w))`. Introduce `z hz`.

Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨Sum.inr (Sum.inr i), rfl⟩`. Consider the case `zero => exact zero_mem _`.

Consider the case `add x y _ _ hx hy => exact add_mem hx hy`. Consider the case `smul c x _ hx => exact Submodule.smul_mem _ (c : I.E) hx`. Establish `hp' : proj e f y ∈ Submodule.span I.E (Set.range (fam e f w))`. Unfold `proj`. Use `Submodule.sum_mem _ fun a _ => add_mem ?_ ?_` and prove the remaining obligations.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl a, rfl⟩)`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr (Sum.inl a), rfl⟩)`. Use `add_mem hp' (key _ hz)` as an intermediate fact. Simplify using `using this`.
-/
theorem fam_sp (hp : p.Prime) (he : ∀ a b, hG I (e a) (e b) = 0) (hf : ∀ a b, hG I (f a) (f b) = 0)
    (hef : ∀ a b, hG I (e a) (f b) = if a = b then 1 else 0)
    (heA : ∀ a, e a ∈ LA I p) (hfA : ∀ a, f a ∈ LA I p)
    (hW : ∀ x ∈ LA I p, (∀ a, hG I (e a) x = 0 ∧ hG I (f a) x = 0) →
        x ∈ Submodule.span (Ap I p) (Set.range w)) :
    ⊤ ≤ Submodule.span I.E (Set.range (fam e f w)) := by
  rw [← I.L_span, Submodule.span_le]
  intro y hy
  have hyA : y ∈ LA I p := L_le_LA hy
  have hz : y - proj e f y ∈ Submodule.span (Ap I p) (Set.range w) := by
    apply hW _ (sub_mem hyA (proj_mem hp heA hfA hyA))
    intro a
    rw [hG_sub_right, hG_sub_right, hG_e_proj he hef, hG_f_proj hf hef, sub_self, sub_self]
    exact ⟨rfl, rfl⟩
  have key : ∀ z ∈ Submodule.span (Ap I p) (Set.range w),
      z ∈ Submodule.span I.E (Set.range (fam e f w)) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨Sum.inr (Sum.inr i), rfl⟩
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx => exact Submodule.smul_mem _ (c : I.E) hx
  have hp' : proj e f y ∈ Submodule.span I.E (Set.range (fam e f w)) := by
    unfold proj
    refine Submodule.sum_mem _ fun a _ => add_mem ?_ ?_
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl a, rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr (Sum.inl a), rfl⟩)
  have := add_mem hp' (key _ hz)
  simpa using this

end Frame

/- English proof (translation)
Introduce `I p r k e f M hp hn he hf hef hM heM`. Take `⟨w, hw1, hwli, hwsp⟩` from `hWB I p r k e f M hp (hPID I p hp) hn he hf hef hM heM`. Establish `heA : ∀ a, e a ∈ LA I p` using `fun a => mem_LA_of_nsmul hp hM (heM a).1`. Establish `hfA : ∀ a, f a ∈ LA I p` using `fun a => mem_LA_of_nsmul hp hM (heM a).2`. Establish `hwA : ∀ i, w i ∈ LA I p` using `fun i => (hw1 i).1`.

Establish `hwo : ∀ i a, hG I (e a) (w i) = 0 ∧ hG I (f a) (w i) = 0` using `fun i a => (hw1 i).2 a`. Establish `hli` using `fam_li he hf hef hwo hwli`. Establish `hsp` using `fam_sp hp he hf hef heA hfA hwsp`. Establish `hT0 : ∀ u, (∀ j, hG I (fam e f w j) u = 0) → u = 0`. Introduce `u hu`.

Apply `hG_nondeg` to reduce the goal to its premises. Introduce `x`. Establish `hx : x ∈ Submodule.span I.E (Set.range (fam e f w))` using `hsp Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨j, rfl⟩` from `hx`. Conclude with `hu j`. Consider the case `zero => exact hG_zero_left I u`. Consider the case `add x y _ _ hx hy => rw [hG_add_left, hx, hy, add_zero]`. Consider the case `smul c x _ hx => rw [hG_smul_left, hx, mul_zero]`.

Set `T : (Fin I.n → I.E) →ₗ[I.E] (Fin r ⊕ (Fin r ⊕ Fin (k + 1)) → I.E)` to `{ toFun := fun d j => hG I (fam e f w j) d map_add' := fun x y => by`. Use extensionality with `j`. Simplify using `[hG_add_right]`. Use the proof step `map_smul' := fun c x => by`. Use extensionality with `j`.

Simplify using `[hG_smul_right] }`. Establish `hTi : Function.Injective T`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `u hu`. Conclude with `hT0 u (fun j => congrFun hu j)`.

Establish `hdim : Module.finrank I.E (Fin I.n → I.E) = Module.finrank I.E (Fin r ⊕ (Fin r ⊕ Fin (k + 1)) → I.E)`. Rewrite using `[Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, hn]`. Expand and normalize the polynomial expressions, which then agree. Establish `hTs : Function.Surjective T` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hTi`. Establish `hex : ∀ i : Fin (k + 1), ∃ d : Fin I.n → I.E, ∀ j, hG I (fam e f w j) d = if j = Sum.inr (Sum.inr i) then 1 else 0`.

Introduce `i`. Take `⟨d, hd⟩` from `hTs (fun j => if j = Sum.inr (Sum.inr i) then 1 else 0)`. Conclude with `⟨d, fun j => congrFun hd j⟩`. Use `choose wd hwd using hex`. Establish `hewd : ∀ a i, hG I (e a) (wd i) = 0` using `fun a i => by`.

Simplify `hwd i (Sum.inl a)` using `[fam]`. Establish `hfwd : ∀ a i, hG I (f a) (wd i) = 0` using `fun a i => by`. Simplify `hwd i (Sum.inr (Sum.inl a))` using `[fam]`. Establish `hwwd : ∀ j i, hG I (w j) (wd i) = if j = i then 1 else 0` using `fun j i => by`. Simplify `hwd i (Sum.inr (Sum.inr j))` using `[fam]`.

Establish `hdual : ∀ i j, hG I (wd i) (w j) = if i = j then 1 else 0`. Introduce `i j`. Rewrite using `[hG_symm I (w j) (wd i), hwwd j i]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`. Establish `hyS : ∀ y ∈ I.L, y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w)`. Introduce `y hy`. Establish `hyA : y ∈ LA I p` using `L_le_LA hy`.

Establish `hz : y - proj e f y ∈ Submodule.span (Ap I p) (Set.range w)`. Apply `hwsp _ (sub_mem hyA (proj_mem hp heA hfA hyA))` to reduce the goal to its premises. Introduce `a`. Rewrite using `[hG_sub_right, hG_sub_right, hG_e_proj he hef, hG_f_proj hf hef, sub_self, sub_self]`. Conclude with `⟨rfl, rfl⟩`.

Establish `h1` using `proj_span e f hp heA hfA hyA (Set.range e ∪ Set.range f ∪ Set.range w) Set.subset_union_left`. Establish `h2 : y - proj e f y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w)` using `Submodule.span_mono Set.subset_union_right hz`. Use `add_mem h1 h2` as an intermediate fact. Simplify using `using this`. Establish `hwdAp : ∀ i, ∀ y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w), hG I (wd i) y ∈ Ap I p`.

Introduce `i y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Break down `hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨j, rfl⟩` into its components or cases. Rewrite using `[hG_symm I (e a) (wd i), hewd a i, star_zero]`.

Conclude with `zero_mem _`. Rewrite using `[hG_symm I (f a) (wd i), hfwd a i, star_zero]`. Conclude with `zero_mem _`. Rewrite using `[hdual i j] split_ifs`. Conclude with `one_mem _`.

Conclude with `zero_mem _`. Consider the case `zero => rw [hG_zero_right]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [hG_add_right]`. Conclude with `add_mem hx hy`.

Consider the case `smul c x _ hx => show hG I (wd i) ((c : I.E) • x) ∈ Ap I p`. Rewrite using `[hG_smul_right]`. Conclude with `mul_mem c.2 hx`. Establish `hwdA : ∀ i, wd i ∈ LA I p` using `fun i => dual_LA hp fun y hy => by`. Rewrite using `[hG_symm I (wd i) y]`.

Conclude with `star_mem_Ap (hwdAp i y (hyS y hy))`. Establish `hyS' : ∀ y ∈ I.L, y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range wd)`. Introduce `y hy`. Establish `hyA : y ∈ LA I p` using `L_le_LA hy`. Establish `hzA : y - proj e f y ∈ LA I p` using `sub_mem hyA (proj_mem hp heA hfA hyA)`.

Establish `hze : ∀ a, hG I (e a) (y - proj e f y) = 0` using `fun a => by`. Rewrite using `[hG_sub_right, hG_e_proj he hef, sub_self]`. Establish `hzf : ∀ a, hG I (f a) (y - proj e f y) = 0` using `fun a => by`. Rewrite using `[hG_sub_right, hG_f_proj hf hef, sub_self]`. Establish `hzeq : y - proj e f y = ∑ i, hG I (w i) (y - proj e f y) • wd i`.

Rewrite using `[← sub_eq_zero]`. Apply `hT0` to reduce the goal to its premises. Introduce `j`. Rewrite using `[hG_sub_right, hG_sum_right]`. Simplify using `only [hG_smul_right]`.

Break down `j with a | a | j` into its components or cases. Simplify using `[fam, hze a, hewd]`. Simplify using `[fam, hzf a, hfwd]`. Simplify using `[fam, hwwd]`. Establish `hz' : y - proj e f y ∈ Submodule.span (Ap I p) (Set.range wd)`.

Rewrite using `[hzeq]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Conclude with `Submodule.smul_mem _ (⟨_, hG_LA hp (hwA i) hzA⟩ : Ap I p) (Submodule.subset_span ⟨i, rfl⟩)`. Establish `h1` using `proj_span e f hp heA hfA hyA (Set.range e ∪ Set.range f ∪ Set.range wd) Set.subset_union_left`. Establish `h2 : y - proj e f y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range wd)` using `Submodule.span_mono Set.subset_union_right hz'`.

Use `add_mem h1 h2` as an intermediate fact. Simplify using `using this`. Conclude with `⟨w, wd, fun i => ⟨hwA i, hwdA i⟩, fun a i => ⟨(hwo i a).1, (hwo i a).2, hewd a i, hfwd a i⟩, hdual, fun y hy => ⟨hyS y hy, hyS' y hy⟩⟩`.
-/
theorem wFrame_of (hPID : ApPID) (hWB : WBasis) : WFrame := by
  intro I p r k e f M hp hn he hf hef hM heM
  obtain ⟨w, hw1, hwli, hwsp⟩ := hWB I p r k e f M hp (hPID I p hp) hn he hf hef hM heM
  have heA : ∀ a, e a ∈ LA I p := fun a => mem_LA_of_nsmul hp hM (heM a).1
  have hfA : ∀ a, f a ∈ LA I p := fun a => mem_LA_of_nsmul hp hM (heM a).2
  have hwA : ∀ i, w i ∈ LA I p := fun i => (hw1 i).1
  have hwo : ∀ i a, hG I (e a) (w i) = 0 ∧ hG I (f a) (w i) = 0 := fun i a => (hw1 i).2 a
  have hli := fam_li he hf hef hwo hwli
  have hsp := fam_sp hp he hf hef heA hfA hwsp
  have hT0 : ∀ u, (∀ j, hG I (fam e f w j) u = 0) → u = 0 := by
    intro u hu
    apply hG_nondeg
    intro x
    have hx : x ∈ Submodule.span I.E (Set.range (fam e f w)) := hsp Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact hu j
    | zero => exact hG_zero_left I u
    | add x y _ _ hx hy => rw [hG_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [hG_smul_left, hx, mul_zero]
  let T : (Fin I.n → I.E) →ₗ[I.E] (Fin r ⊕ (Fin r ⊕ Fin (k + 1)) → I.E) :=
    { toFun := fun d j => hG I (fam e f w j) d
      map_add' := fun x y => by
        ext j
        simp [hG_add_right]
      map_smul' := fun c x => by
        ext j
        simp [hG_smul_right] }
  have hTi : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    exact hT0 u (fun j => congrFun hu j)
  have hdim : Module.finrank I.E (Fin I.n → I.E) =
      Module.finrank I.E (Fin r ⊕ (Fin r ⊕ Fin (k + 1)) → I.E) := by
    rw [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
      Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, hn]
    ring
  have hTs : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hTi
  have hex : ∀ i : Fin (k + 1), ∃ d : Fin I.n → I.E, ∀ j,
      hG I (fam e f w j) d = if j = Sum.inr (Sum.inr i) then 1 else 0 := by
    intro i
    obtain ⟨d, hd⟩ := hTs (fun j => if j = Sum.inr (Sum.inr i) then 1 else 0)
    exact ⟨d, fun j => congrFun hd j⟩
  choose wd hwd using hex
  have hewd : ∀ a i, hG I (e a) (wd i) = 0 := fun a i => by
    simpa [fam] using hwd i (Sum.inl a)
  have hfwd : ∀ a i, hG I (f a) (wd i) = 0 := fun a i => by
    simpa [fam] using hwd i (Sum.inr (Sum.inl a))
  have hwwd : ∀ j i, hG I (w j) (wd i) = if j = i then 1 else 0 := fun j i => by
    simpa [fam] using hwd i (Sum.inr (Sum.inr j))
  have hdual : ∀ i j, hG I (wd i) (w j) = if i = j then 1 else 0 := by
    intro i j
    rw [hG_symm I (w j) (wd i), hwwd j i]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  have hyS : ∀ y ∈ I.L,
      y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w) := by
    intro y hy
    have hyA : y ∈ LA I p := L_le_LA hy
    have hz : y - proj e f y ∈ Submodule.span (Ap I p) (Set.range w) := by
      apply hwsp _ (sub_mem hyA (proj_mem hp heA hfA hyA))
      intro a
      rw [hG_sub_right, hG_sub_right, hG_e_proj he hef, hG_f_proj hf hef, sub_self, sub_self]
      exact ⟨rfl, rfl⟩
    have h1 := proj_span e f hp heA hfA hyA (Set.range e ∪ Set.range f ∪ Set.range w)
      Set.subset_union_left
    have h2 : y - proj e f y ∈
        Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w) :=
      Submodule.span_mono Set.subset_union_right hz
    have := add_mem h1 h2
    simpa using this
  have hwdAp : ∀ i, ∀ y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w),
      hG I (wd i) y ∈ Ap I p := by
    intro i y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨j, rfl⟩
      · rw [hG_symm I (e a) (wd i), hewd a i, star_zero]
        exact zero_mem _
      · rw [hG_symm I (f a) (wd i), hfwd a i, star_zero]
        exact zero_mem _
      · rw [hdual i j]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
    | zero => rw [hG_zero_right]; exact zero_mem _
    | add x y _ _ hx hy => rw [hG_add_right]; exact add_mem hx hy
    | smul c x _ hx =>
      show hG I (wd i) ((c : I.E) • x) ∈ Ap I p
      rw [hG_smul_right]
      exact mul_mem c.2 hx
  have hwdA : ∀ i, wd i ∈ LA I p := fun i => dual_LA hp fun y hy => by
    rw [hG_symm I (wd i) y]
    exact star_mem_Ap (hwdAp i y (hyS y hy))
  have hyS' : ∀ y ∈ I.L,
      y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range wd) := by
    intro y hy
    have hyA : y ∈ LA I p := L_le_LA hy
    have hzA : y - proj e f y ∈ LA I p := sub_mem hyA (proj_mem hp heA hfA hyA)
    have hze : ∀ a, hG I (e a) (y - proj e f y) = 0 := fun a => by
      rw [hG_sub_right, hG_e_proj he hef, sub_self]
    have hzf : ∀ a, hG I (f a) (y - proj e f y) = 0 := fun a => by
      rw [hG_sub_right, hG_f_proj hf hef, sub_self]
    have hzeq : y - proj e f y = ∑ i, hG I (w i) (y - proj e f y) • wd i := by
      rw [← sub_eq_zero]
      apply hT0
      intro j
      rw [hG_sub_right, hG_sum_right]
      simp only [hG_smul_right]
      rcases j with a | a | j
      · simp [fam, hze a, hewd]
      · simp [fam, hzf a, hfwd]
      · simp [fam, hwwd]
    have hz' : y - proj e f y ∈ Submodule.span (Ap I p) (Set.range wd) := by
      rw [hzeq]
      refine Submodule.sum_mem _ fun i _ => ?_
      exact Submodule.smul_mem _ (⟨_, hG_LA hp (hwA i) hzA⟩ : Ap I p)
        (Submodule.subset_span ⟨i, rfl⟩)
    have h1 := proj_span e f hp heA hfA hyA (Set.range e ∪ Set.range f ∪ Set.range wd)
      Set.subset_union_left
    have h2 : y - proj e f y ∈
        Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range wd) :=
      Submodule.span_mono Set.subset_union_right hz'
    have := add_mem h1 h2
    simpa using this
  exact ⟨w, wd, fun i => ⟨hwA i, hwdA i⟩,
    fun a i => ⟨(hwo i a).1, (hwo i a).2, hewd a i, hfwd a i⟩, hdual,
    fun y hy => ⟨hyS y hy, hyS' y hy⟩⟩

end PI.ScRefExists.WF
