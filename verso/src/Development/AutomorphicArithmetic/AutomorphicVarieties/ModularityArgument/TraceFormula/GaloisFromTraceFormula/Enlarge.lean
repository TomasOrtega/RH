import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

namespace UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private noncomputable def listProd {ι : Type} {a b : ℕ} (d : ι → Ex (Fin (a + 1) × Fin (b + 1))) :
    List ι → Ex (Fin (a + 1) × Fin (b + 1))
  | [] => .one
  | i :: l => .mul (d i) (listProd d l)

/- English proof (translation)
The claim follows from `| [] => .one | i :: l => .mul (h i) (list_prod_unitary_test h l)`.
-/
private theorem list_prod_unitary_test {ι : Type} {a b : ℕ} {d : ι → Ex (Fin (a + 1) × Fin (b + 1))}
    (h : ∀ i, U1 (d i)) : ∀ l : List ι, U1 (listProd d l)
  | [] => .one
  | i :: l => .mul (h i) (list_prod_unitary_test h l)

/- English proof (translation)
The claim follows from `| [], h => by simp at h | j :: l, h => by rcases List.mem_cons.1 h with rfl | h · simp [listProd, Ex.ev, h0] · simp [listProd, Ex.ev, listProd_ev_zero x h0 l h]`.
-/
private theorem listProd_ev_zero {ι : Type} {a b : ℕ} {d : ι → Ex (Fin (a + 1) × Fin (b + 1))}
    (x : Fin (a + 1) × Fin (b + 1) → ℂ) {i : ι} (h0 : (d i).ev x = 0) :
    ∀ l : List ι, i ∈ l → (listProd d l).ev x = 0
  | [], h => by simp at h
  | j :: l, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp [listProd, Ex.ev, h0]
    · simp [listProd, Ex.ev, listProd_ev_zero x h0 l h]

end UpperTheory.V.Z.Tf.GaloisFromTraceFormula

open scoped Classical in
/- English proof (translation)
Introduce `hSt hEv hSep hPl E _ _ _ hunr a b S hS Z T hZ hT hTZ e₁ e₂ I _ u C₁ C₂ hC`. Take `⟨-, hcp, -, hsec⟩` from `hPl E`. Establish `hd : ∀ i, ∃ e, U1 e ∧ ev2 a b (u i) e (C₁ i (u i)) (C₂ i (u i)) = 0` using `fun i => hSep E (u i) a b _ _ (hC i).2.1 (hC i).2.2.1 (hC i).2.2.2`. Use `choose d hdU hd0 using hd`. Use `haveI : Fintype I := Fintype.ofFinite I`.

Establish `hnsS : ∀ w : Pl E, ¬ IsSplitAt w → w ∈ S`. Introduce `w hw`. Establish `hc : cPl w = w`. Assume the negation of the conclusion as `h`. Conclude with `hw ((hcp w).2.2 h)`.

Break down `(hsec S hS w).1 with h | h` into its components or cases. Conclude with `h`. Rewrite `h` using `[hc]`. Then use the resulting hypothesis. Establish `hTns : ∀ w ∈ T, IsSplitAt w` using `fun w hw => (hT w hw).2`. Establish `hZns : ∀ w ∈ Z, IsSplitAt w` using `fun w hw => (hZ w hw).2`.

Set `L : Pl E → List I` to `fun w => (Finset.univ.filter fun i => u i = w).toList`. Set `T' : Finset (Pl E)` to `T ∪ Finset.univ.image u`. Set `f₁ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))` to `fun w => if w ∈ T then e₁ w else listProd d (L w)`. Set `f₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))` to `fun w => if w ∈ T then e₂ w else .one`. Establish `hfU : ∀ w, w ∉ T → U1 (f₁ w)`.

Introduce `w hw`. Simplify using `only [f₁, if_neg hw]`. Conclude with `list_prod_unitary_test hdU _`. Establish `hf₂ : ∀ w, w ∉ T → f₂ w = .one` using `fun w hw => by simp only [f₂, if_neg hw]`. Establish `hT'ns : ∀ w ∈ T', w ∉ T → ¬ IsSplitAt w`.

Introduce `w hw hwT`. Break down `Finset.mem_union.1 hw with h | h` into its components or cases. Conclude with `absurd h hwT`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 h`. Conclude with `(hC i).1`.

Establish `huT : ∀ i, u i ∉ T` using `fun i h => (hC i).1 (hTns _ h)`. Use `⟨T', f₁, f₂, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `w hw`. Distinguish the cases in `hwT : w ∈ T`. Conclude with `(hT w hwT).1`.

Conclude with `hnsS w (hT'ns w hw hwT)`. Rewrite using `[Finset.disjoint_left]`. Introduce `w hw hwZ`. Distinguish the cases in `hwT : w ∈ T`. Conclude with `Finset.disjoint_left.1 hTZ hwT hwZ`.

Conclude with `hT'ns w hw hwT (hZns w hwZ)`. Introduce `w hw hns`. Establish `hwT : w ∉ T` using `fun h => hns (hTns w h)`. Conclude with `hf₂ w hwT`. Introduce `i`.

Use `Finset.prod_eq_zero (i := u i) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))) ?_` and prove the remaining obligations. Establish `: ev2 a b (u i) (f₁ (u i)) (C₁ i (u i)) (C₂ i (u i)) = 0`. Simplify using `only [f₁, if_neg (huT i)]`. Use `listProd_ev_zero _ (hd0 i) _ ?_` and prove the remaining obligations. Simplify using `[L]`.

Rewrite using `[this, zero_mul]`. Introduce `B₁ B₂ hB`. Unfold `UpperTheory.V.Z.Tf.GlobalTraceComparison.val`. Use `symm`. Establish `hsub : T ⊆ T'` using `Finset.subset_union_left`.

Rewrite using `[← Finset.prod_subset hsub]`. Use `Finset.prod_congr rfl fun w hw => ?_` and prove the remaining obligations. Simplify using `only [f₁, f₂, if_pos hw]`. Introduce `w hw hwT`. Break down `Finset.mem_union.1 hw with h | h` into its components or cases.

Conclude with `absurd h hwT`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 h`. Rewrite using `[hf₂ _ hwT, hEv E (u i) a b _ (hfU _ hwT) _ _ (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2]`. Simplify using `[ev2, Ex.ev]`. Introduce `l₁ l₂ φ k`.

Establish `hloc : ∀ (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X]), Q₁.Separable → Q₂.Separable → stTw2 a b w Q₁ Q₂ (fam Z T' φ f₁ f₂ k w) = stTw2 a b w Q₁ Q₂ (fam Z T φ e₁ e₂ k w)`. Introduce `w Q₁ Q₂ h₁ h₂`. Unfold `fam`. Distinguish the cases in `hwZ : w ∈ Z`. Simplify using `only [if_pos hwZ]`.

Simplify using `only [if_neg hwZ]`. Distinguish the cases in `hwT : w ∈ T`. Establish `hw' : w ∈ T'` using `Finset.mem_union_left _ hwT`. Simplify using `only [if_pos hwT, if_pos hw', f₁, f₂]`. Distinguish the cases in `hw' : w ∈ T'`.

Simplify using `only [if_neg hwT, if_pos hw']`. Rewrite using `[hf₂ w hwT]`. Conclude with `hSt E hunr w (hT'ns w hw' hwT) a b _ (.mul ((hfU w hwT).pow k) ((U1.one).pow k)) Q₁ Q₂ h₁ h₂`. Simplify using `only [if_neg hwT, if_neg hw']`. Unfold `PositivityTheory.Rg.BcB.G8.geomSt2`.

Use `finsum_mem_congr rfl fun p hp => ?_` and prove the remaining obligations. Use `congr 1`. Use `finprod_congr fun w => finprod_congr fun _ => ?_` and prove the remaining obligations. Conclude with `hloc w _ _ (hp.1.2.2.1.map) (hp.2.1.2.2.1.map)`.
-/
theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.enlarge :
    StUnit → EvaluationAtUnitaryOne → SeparatesUnitaryOne → Places → Enlarge := by
  intro hSt hEv hSep hPl E _ _ _ hunr a b S hS Z T hZ hT hTZ e₁ e₂ I _ u C₁ C₂ hC
  obtain ⟨-, hcp, -, hsec⟩ := hPl E
  have hd : ∀ i, ∃ e, U1 e ∧ ev2 a b (u i) e (C₁ i (u i)) (C₂ i (u i)) = 0 := fun i =>
    hSep E (u i) a b _ _ (hC i).2.1 (hC i).2.2.1 (hC i).2.2.2
  choose d hdU hd0 using hd
  haveI : Fintype I := Fintype.ofFinite I
  have hnsS : ∀ w : Pl E, ¬ IsSplitAt w → w ∈ S := by
    intro w hw
    have hc : cPl w = w := by
      by_contra h
      exact hw ((hcp w).2.2 h)
    rcases (hsec S hS w).1 with h | h
    · exact h
    · rwa [hc] at h
  have hTns : ∀ w ∈ T, IsSplitAt w := fun w hw => (hT w hw).2
  have hZns : ∀ w ∈ Z, IsSplitAt w := fun w hw => (hZ w hw).2
  let L : Pl E → List I := fun w => (Finset.univ.filter fun i => u i = w).toList
  let T' : Finset (Pl E) := T ∪ Finset.univ.image u
  let f₁ : Pl E → Ex (Fin (a + 1) × Fin (b + 1)) := fun w => if w ∈ T then e₁ w else listProd d (L w)
  let f₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1)) := fun w => if w ∈ T then e₂ w else .one
  have hfU : ∀ w, w ∉ T → U1 (f₁ w) := by
    intro w hw
    simp only [f₁, if_neg hw]
    exact list_prod_unitary_test hdU _
  have hf₂ : ∀ w, w ∉ T → f₂ w = .one := fun w hw => by simp only [f₂, if_neg hw]
  have hT'ns : ∀ w ∈ T', w ∉ T → ¬ IsSplitAt w := by
    intro w hw hwT
    rcases Finset.mem_union.1 hw with h | h
    · exact absurd h hwT
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      exact (hC i).1
  have huT : ∀ i, u i ∉ T := fun i h => (hC i).1 (hTns _ h)
  refine ⟨T', f₁, f₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    by_cases hwT : w ∈ T
    · exact (hT w hwT).1
    · exact hnsS w (hT'ns w hw hwT)
  · rw [Finset.disjoint_left]
    intro w hw hwZ
    by_cases hwT : w ∈ T
    · exact Finset.disjoint_left.1 hTZ hwT hwZ
    · exact hT'ns w hw hwT (hZns w hwZ)
  · intro w hw hns
    have hwT : w ∉ T := fun h => hns (hTns w h)
    exact hf₂ w hwT
  · intro i
    refine Finset.prod_eq_zero (i := u i) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))) ?_
    have : ev2 a b (u i) (f₁ (u i)) (C₁ i (u i)) (C₂ i (u i)) = 0 := by
      simp only [f₁, if_neg (huT i)]
      refine listProd_ev_zero _ (hd0 i) _ ?_
      simp [L]
    rw [this, zero_mul]
  · intro B₁ B₂ hB
    unfold UpperTheory.V.Z.Tf.GlobalTraceComparison.val
    symm
    have hsub : T ⊆ T' := Finset.subset_union_left
    rw [← Finset.prod_subset hsub]
    · refine Finset.prod_congr rfl fun w hw => ?_
      simp only [f₁, f₂, if_pos hw]
    · intro w hw hwT
      rcases Finset.mem_union.1 hw with h | h
      · exact absurd h hwT
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      rw [hf₂ _ hwT, hEv E (u i) a b _ (hfU _ hwT) _ _ (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2]
      simp [ev2, Ex.ev]
  · intro l₁ l₂ φ k
    have hloc : ∀ (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X]), Q₁.Separable → Q₂.Separable →
        stTw2 a b w Q₁ Q₂ (fam Z T' φ f₁ f₂ k w) = stTw2 a b w Q₁ Q₂ (fam Z T φ e₁ e₂ k w) := by
      intro w Q₁ Q₂ h₁ h₂
      unfold fam
      by_cases hwZ : w ∈ Z
      · simp only [if_pos hwZ]
      simp only [if_neg hwZ]
      by_cases hwT : w ∈ T
      · have hw' : w ∈ T' := Finset.mem_union_left _ hwT
        simp only [if_pos hwT, if_pos hw', f₁, f₂]
      by_cases hw' : w ∈ T'
      · simp only [if_neg hwT, if_pos hw']
        rw [hf₂ w hwT]
        exact hSt E hunr w (hT'ns w hw' hwT) a b _
          (.mul ((hfU w hwT).pow k) ((U1.one).pow k)) Q₁ Q₂ h₁ h₂
      · simp only [if_neg hwT, if_neg hw']
    unfold PositivityTheory.Rg.BcB.G8.geomSt2
    refine finsum_mem_congr rfl fun p hp => ?_
    congr 1
    refine finprod_congr fun w => finprod_congr fun _ => ?_
    exact hloc w _ _ (hp.1.2.2.1.map) (hp.2.1.2.2.1.map)
