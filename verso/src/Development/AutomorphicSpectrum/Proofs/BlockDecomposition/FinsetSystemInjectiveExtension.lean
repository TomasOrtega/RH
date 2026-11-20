import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.Exc
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

section Tuples
variable {ι : Type}

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[Fin.succAbove_zero]`.
-/
theorem cons_comp_zero {n : ℕ} (a : ι) (i : Fin (n + 1) → ι) :
    (Fin.cons a i : Fin (n + 2) → ι) ∘ (0 : Fin (n + 2)).succAbove = i := by
  funext k
  simp [Fin.succAbove_zero]

/- English proof (translation)
Use function extensionality and compare the values at `t`. Consider the cases of `t using Fin.cases with`. Consider the case `zero => simp only [Function.comp_apply, Fin.succ_succAbove_zero, Fin.cons_zero]`. Consider the case `succ t => simp only [Function.comp_apply, Fin.succ_succAbove_succ, Fin.cons_succ]`.
-/
theorem cons_comp_succ {n : ℕ} (a : ι) (i : Fin (n + 1) → ι) (k : Fin (n + 1)) :
    (Fin.cons a i : Fin (n + 2) → ι) ∘ k.succ.succAbove = Fin.cons a (i ∘ k.succAbove) := by
  funext t
  cases t using Fin.cases with
  | zero => simp only [Function.comp_apply, Fin.succ_succAbove_zero, Fin.cons_zero]
  | succ t => simp only [Function.comp_apply, Fin.succ_succAbove_succ, Fin.cons_succ]

/- English proof (translation)
Simplify using `only [ent, Finset.mem_image, Finset.mem_univ, true_and] at h ⊢`. Take `⟨k, rfl⟩` from `h`. Consider the cases of `k using Fin.cases with`. Consider the case `zero => left`. Simplify using `only [Fin.cons_zero]`.

Consider the case `succ k => right`. Conclude with `⟨k, by simp only [Fin.cons_succ]⟩`.
-/
theorem mem_ent_cons [DecidableEq ι] {n : ℕ} {a x : ι} {i : Fin n → ι}
    (h : x ∈ ent (Fin.cons a i : Fin (n + 1) → ι)) : x = a ∨ x ∈ ent i := by
  simp only [ent, Finset.mem_image, Finset.mem_univ, true_and] at h ⊢
  obtain ⟨k, rfl⟩ := h
  cases k using Fin.cases with
  | zero =>
    left
    simp only [Fin.cons_zero]
  | succ k =>
    right
    exact ⟨k, by simp only [Fin.cons_succ]⟩

end Tuples

section Coordinates
variable {K : Type} [CommRing K] {ι : Type} [DecidableEq ι] [Fintype ι] {W : Type} [AddCommGroup W] [Module K W] {Λ : Type}
  (b : Module.Basis Λ K W) (good' : Λ → Prop) (T : Λ → Finset ι)

def Sup (S : Finset ι) (w : W) : Prop := ∀ l, b.repr w l ≠ 0 → good' l ∧ T l ⊆ S

/- English proof (translation)
Rewrite using `[Module.Basis.mem_span_image]`. Prove the components needed by the constructor for the conclusion. Introduce `h l hl`. Conclude with `h (Finsupp.mem_support_iff.2 hl)`. Introduce `h l hl`.

Rewrite `hl` using `[Finset.mem_coe, Finsupp.mem_support_iff]`. Conclude with `h l hl`.
-/
theorem mem_span_iff (S : Finset ι) (w : W) :
    w ∈ Submodule.span K (b '' {l | good' l ∧ T l ⊆ S}) ↔ Sup b good' T S w := by
  rw [Module.Basis.mem_span_image]
  constructor
  · intro h l hl
    exact h (Finsupp.mem_support_iff.2 hl)
  · intro h l hl
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hl
    exact h l hl

/- English proof (translation)
Rewrite using `[map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, Finsupp.smul_apply]`.
-/
theorem coord_sum {n : ℕ} (D : Fin n → W) (l : Λ) :
    b.repr (∑ k : Fin n, (-1 : ℤ) ^ (k : ℕ) • D k) l = ∑ k : Fin n, (-1 : ℤ) ^ (k : ℕ) • b.repr (D k) l := by
  rw [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, Finsupp.smul_apply]

open Classical in

def contr {n : ℕ} (C : (Fin (n + 1) → ι) → W) (a : ∀ l, good' l → ι) (i : Fin n → ι) : W :=
  b.repr.symm (Finsupp.onFinset (Finset.univ.biUnion fun a' : ι => (b.repr (C (Fin.cons a' i))).support)
    (fun l => if h : good' l then b.repr (C (Fin.cons (a l h) i)) l else 0) (by
      intro l hl
      by_cases h : good' l
      · rw [dif_pos h] at hl
        exact Finset.mem_biUnion.2 ⟨a l h, Finset.mem_univ _, Finsupp.mem_support_iff.2 hl⟩
      · rw [dif_neg h] at hl
        exact absurd rfl hl))

open Classical in
/- English proof (translation)
Unfold `contr`. Rewrite using `[LinearEquiv.apply_symm_apply, Finsupp.onFinset_apply]`.
-/
theorem contr_apply {n : ℕ} (C : (Fin (n + 1) → ι) → W) (a : ∀ l, good' l → ι) (i : Fin n → ι) (l : Λ) :
    b.repr (contr b good' C a i) l = if h : good' l then b.repr (C (Fin.cons (a l h) i)) l else 0 := by
  unfold contr
  rw [LinearEquiv.apply_symm_apply, Finsupp.onFinset_apply]

/- English proof (translation)
Introduce `l hl`. Rewrite `hl` using `[contr_apply]`. Distinguish the cases in `h : good' l`. Rewrite `hl` using `[dif_pos h]`. Take `⟨-, hT⟩` from `hC _ l hl`.

Use `⟨h, fun x hx => ?_⟩` and prove the remaining obligations. Break down `mem_ent_cons (hT hx) with rfl | hx'` into its components or cases. Conclude with `absurd hx (ha l h)`. Conclude with `hx'`. Rewrite `hl` using `[dif_neg h]`.

Conclude with `absurd rfl hl`.
-/
theorem contr_sup {n : ℕ} (C : (Fin (n + 1) → ι) → W) (hC : ∀ i, Sup b good' T (ent i) (C i))
    (a : ∀ l, good' l → ι) (ha : ∀ l h, a l h ∉ T l) (i : Fin n → ι) :
    Sup b good' T (ent i) (contr b good' C a i) := by
  intro l hl
  rw [contr_apply] at hl
  by_cases h : good' l
  · rw [dif_pos h] at hl
    obtain ⟨-, hT⟩ := hC _ l hl
    refine ⟨h, fun x hx => ?_⟩
    rcases mem_ent_cons (hT hx) with rfl | hx'
    · exact absurd hx (ha l h)
    · exact hx'
  · rw [dif_neg h] at hl
    exact absurd rfl hl

/- English proof (translation)
Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `l`. Rewrite using `[coord_sum]`. Simplify using `only [contr_apply]`. Distinguish the cases in `h : good' l`.

Simplify using `only [dif_pos h]`. Establish `hz` using `congrArg (fun w => b.repr w l) (hZ (Fin.cons (a l h) i))`. Rewrite `hz` using `[Fin.sum_univ_succ]`. Simplify using `only [Fin.val_zero, pow_zero, one_smul, cons_comp_zero, Fin.val_succ, cons_comp_succ, map_add, map_sum, map_zsmul, Finsupp.add_apply, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply, pow_succ, mul_neg, mul_one, neg_smul, Fins …`. Rewrite `hz` using `[← sub_eq_add_neg, sub_eq_zero]`.

Conclude with `hz.symm`. Simplify using `only [dif_neg h, smul_zero, Finset.sum_const_zero]`. Assume the negation of the conclusion as `hne`. Conclude with `h (hC i l (Ne.symm hne)).1`.
-/
theorem homotopy {n : ℕ} (C : (Fin (n + 1) → ι) → W) (hC : ∀ i, Sup b good' T (ent i) (C i))
    (hZ : ∀ i : Fin (n + 2) → ι, ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • C (i ∘ k.succAbove) = 0)
    (a : ∀ l, good' l → ι) (i : Fin (n + 1) → ι) :
    ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • contr b good' C a (i ∘ k.succAbove) = C i := by
  apply b.repr.injective
  ext l
  rw [coord_sum]
  simp only [contr_apply]
  by_cases h : good' l
  · simp only [dif_pos h]
    have hz := congrArg (fun w => b.repr w l) (hZ (Fin.cons (a l h) i))
    rw [Fin.sum_univ_succ] at hz
    simp only [Fin.val_zero, pow_zero, one_smul, cons_comp_zero, Fin.val_succ, cons_comp_succ,
      map_add, map_sum, map_zsmul, Finsupp.add_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply, pow_succ, mul_neg, mul_one,
      neg_smul, Finset.sum_neg_distrib, map_neg, Finsupp.coe_neg, Pi.neg_apply] at hz
    rw [← sub_eq_add_neg, sub_eq_zero] at hz
    exact hz.symm
  · simp only [dif_neg h, smul_zero, Finset.sum_const_zero]
    by_contra hne
    exact h (hC i l (Ne.symm hne)).1

end Coordinates

section Main

/- English proof (translation)
Simplify using `only [dZ, map_sum, map_zsmul, hr]`.
-/
theorem j_dZ {ι : Type} [DecidableEq ι] {W : Type} [AddCommGroup W] (M : Finset ι → Type) [∀ S, AddCommGroup (M S)]
    (r : ∀ {S S' : Finset ι}, S ⊆ S' → M S → M S') (j : ∀ S, M S →+ W)
    (hr : ∀ {S S' : Finset ι} (h : S ⊆ S') x, j S' (r h x) = j S x) (m : ℕ)
    (c : ∀ i : Fin (m + 1) → ι, M (ent i)) (i : Fin (m + 2) → ι) :
    j (ent i) (dZ M r m c i) = ∑ k : Fin (m + 2), (-1 : ℤ) ^ (k : ℕ) • j _ (c (i ∘ k.succAbove)) := by
  simp only [dZ, map_sum, map_zsmul, hr]

/- English proof (translation)
Introduce `K _ ι _ _ W _ _ Λ b good' T hT M _ r j hj hr hspan`. Establish `hout : ∀ l, good' l → ∃ y, y ∉ T l`. Introduce `l hl`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Conclude with `hT l hl (Finset.eq_univ_iff_forall.2 hc)`. Use `choose a ha using hout`. Establish `hsup : ∀ S (x : M S), Sup b good' T S (j S x)` using `fun S x => (mem_span_iff b good' T S _).1 ((hspan S _).1 ⟨x, rfl⟩)`. Establish `hlift : ∀ S w, Sup b good' T S w → ∃ x, j S x = w` using `fun S w h => (hspan S w).2 ((mem_span_iff b good' T S w).2 h)`. Use `⟨fun x hx => ?_, fun c hc => ?_, fun m c hc => ?_⟩` and prove the remaining obligations.

Establish `hw : j ∅ x = 0`. Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `l`. Rewrite using `[map_zero, Finsupp.coe_zero, Pi.zero_apply]`. Assume the negation of the conclusion as `hne`.

Take `⟨hg, -⟩` from `hsup ∅ x l hne`. Establish `h0` using `hr (Finset.empty_subset (ent (fun _ : Fin 1 => a l hg))) x`. Establish `hx0 : r (Finset.empty_subset (ent (fun _ : Fin 1 => a l hg))) x = 0` using `hx _`. Rewrite `h0` using `[hx0, map_zero]`. Rewrite `hne` using `[← h0]`.

Conclude with `hne (by rw [map_zero, Finsupp.coe_zero, Pi.zero_apply])`. Conclude with `hj ∅ (hw.trans (map_zero (j ∅)).symm)`. Establish `hZ : ∀ i : Fin (0 + 2) → ι, ∑ k : Fin (0 + 2), (-1 : ℤ) ^ (k : ℕ) • j _ (c (i ∘ k.succAbove)) = 0`. Introduce `i`. Rewrite using `[← j_dZ M r j hr 0 c i, hc, Pi.zero_apply, map_zero]`.

Establish `hCs : ∀ i : Fin (0 + 1) → ι, Sup b good' T (ent i) (j (ent i) (c i))` using `fun i => hsup _ (c i)`. Establish `hw` using `contr_sup b good' T (fun i : Fin (0 + 1) → ι => j (ent i) (c i)) hCs a ha Fin.elim0`. Establish `he : ent (Fin.elim0 : Fin 0 → ι) = ∅` using `by simp [ent]`. Rewrite `hw` using `[he]`. Take `⟨x, hx⟩` from `hlift ∅ _ hw`.

Use `⟨x, fun i => hj _ ?_⟩` and prove the remaining obligations. Rewrite using `[hr, hx]`. Establish `hh` using `homotopy b good' T (fun i : Fin (0 + 1) → ι => j (ent i) (c i)) hCs hZ a i`. Rewrite `hh` using `[Fin.sum_univ_succ]`. Simplify using `only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Fin.val_zero, pow_zero, one_smul] at hh`.

Use `hh using 2` and compare the differences between its conclusion and the goal. Establish `hZ : ∀ i : Fin (m + 1 + 2) → ι, ∑ k : Fin (m + 1 + 2), (-1 : ℤ) ^ (k : ℕ) • j _ (c (i ∘ k.succAbove)) = 0`. Introduce `i`. Rewrite using `[← j_dZ M r j hr (m + 1) c i, hc, Pi.zero_apply, map_zero]`. Establish `hCs : ∀ i : Fin (m + 1 + 1) → ι, Sup b good' T (ent i) (j (ent i) (c i))` using `fun i => hsup _ (c i)`.

Establish `hb : ∀ i' : Fin (m + 1) → ι, ∃ x : M (ent i'), j (ent i') x = contr b good' (fun i : Fin (m + 1 + 1) → ι => j (ent i) (c i)) a i'` using `fun i' => hlift _ _ (contr_sup b good' T _ hCs a ha i')`. Use `choose b' hb' using hb`. Use `⟨b', funext fun i => hj _ ?_⟩` and prove the remaining obligations. Rewrite using `[j_dZ M r j hr m b' i]`. Simplify using `only [hb']`.

Conclude with `homotopy b good' T (fun i : Fin (m + 1 + 1) → ι => j (ent i) (c i)) hCs hZ a i`.
-/
theorem exP_of_basis : ∀ {K : Type} [CommRing K] {ι : Type} [DecidableEq ι] [Fintype ι] {W : Type} [AddCommGroup W]
    [Module K W] {Λ : Type} (b : Module.Basis Λ K W) (good' : Λ → Prop) (T : Λ → Finset ι),
    (∀ l, good' l → T l ≠ Finset.univ) → ∀ (M : Finset ι → Type) [∀ S, AddCommGroup (M S)]
    (r : ∀ {S S' : Finset ι}, S ⊆ S' → M S → M S') (j : ∀ S, M S →+ W), (∀ S, Function.Injective (j S)) →
    (∀ {S S' : Finset ι} (h : S ⊆ S') x, j S' (r h x) = j S x) →
    (∀ S w, (∃ x, j S x = w) ↔ w ∈ Submodule.span K (b '' {l | good' l ∧ T l ⊆ S})) → ExP M r := by
  intro K _ ι _ _ W _ _ Λ b good' T hT M _ r j hj hr hspan
  have hout : ∀ l, good' l → ∃ y, y ∉ T l := by
    intro l hl
    by_contra hc
    push Not at hc
    exact hT l hl (Finset.eq_univ_iff_forall.2 hc)
  choose a ha using hout
  have hsup : ∀ S (x : M S), Sup b good' T S (j S x) := fun S x =>
    (mem_span_iff b good' T S _).1 ((hspan S _).1 ⟨x, rfl⟩)
  have hlift : ∀ S w, Sup b good' T S w → ∃ x, j S x = w := fun S w h =>
    (hspan S w).2 ((mem_span_iff b good' T S w).2 h)
  refine ⟨fun x hx => ?_, fun c hc => ?_, fun m c hc => ?_⟩
  · have hw : j ∅ x = 0 := by
      apply b.repr.injective
      ext l
      rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
      by_contra hne
      obtain ⟨hg, -⟩ := hsup ∅ x l hne
      have h0 := hr (Finset.empty_subset (ent (fun _ : Fin 1 => a l hg))) x
      have hx0 : r (Finset.empty_subset (ent (fun _ : Fin 1 => a l hg))) x = 0 := hx _
      rw [hx0, map_zero] at h0
      rw [← h0] at hne
      exact hne (by rw [map_zero, Finsupp.coe_zero, Pi.zero_apply])
    exact hj ∅ (hw.trans (map_zero (j ∅)).symm)
  · have hZ : ∀ i : Fin (0 + 2) → ι,
        ∑ k : Fin (0 + 2), (-1 : ℤ) ^ (k : ℕ) • j _ (c (i ∘ k.succAbove)) = 0 := by
      intro i
      rw [← j_dZ M r j hr 0 c i, hc, Pi.zero_apply, map_zero]
    have hCs : ∀ i : Fin (0 + 1) → ι, Sup b good' T (ent i) (j (ent i) (c i)) := fun i => hsup _ (c i)
    have hw := contr_sup b good' T (fun i : Fin (0 + 1) → ι => j (ent i) (c i)) hCs a ha Fin.elim0
    have he : ent (Fin.elim0 : Fin 0 → ι) = ∅ := by simp [ent]
    rw [he] at hw
    obtain ⟨x, hx⟩ := hlift ∅ _ hw
    refine ⟨x, fun i => hj _ ?_⟩
    rw [hr, hx]
    have hh := homotopy b good' T (fun i : Fin (0 + 1) → ι => j (ent i) (c i)) hCs hZ a i
    rw [Fin.sum_univ_succ] at hh
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Fin.val_zero, pow_zero,
      one_smul] at hh
    convert hh using 2
  · have hZ : ∀ i : Fin (m + 1 + 2) → ι,
        ∑ k : Fin (m + 1 + 2), (-1 : ℤ) ^ (k : ℕ) • j _ (c (i ∘ k.succAbove)) = 0 := by
      intro i
      rw [← j_dZ M r j hr (m + 1) c i, hc, Pi.zero_apply, map_zero]
    have hCs : ∀ i : Fin (m + 1 + 1) → ι, Sup b good' T (ent i) (j (ent i) (c i)) :=
      fun i => hsup _ (c i)
    have hb : ∀ i' : Fin (m + 1) → ι, ∃ x : M (ent i'),
        j (ent i') x = contr b good' (fun i : Fin (m + 1 + 1) → ι => j (ent i) (c i)) a i' :=
      fun i' => hlift _ _ (contr_sup b good' T _ hCs a ha i')
    choose b' hb' using hb
    refine ⟨b', funext fun i => hj _ ?_⟩
    rw [j_dZ M r j hr m b' i]
    simp only [hb']
    exact homotopy b good' T (fun i : Fin (m + 1 + 1) → ι => j (ent i) (c i)) hCs hZ a i

end Main

end GlobalTheory.CompanionTheory.SurjectionOntoH4.Exc
