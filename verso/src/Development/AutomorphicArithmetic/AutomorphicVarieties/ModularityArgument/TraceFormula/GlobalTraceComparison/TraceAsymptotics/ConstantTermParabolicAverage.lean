import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private def lprod {ι : Type} : List (Ex ι) → Ex ι
  | [] => Ex.one
  | a :: l => Ex.mul a (lprod l)

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp [lprod, Ex.ev]`. Consider the case `cons a l ih => simp [lprod, Ex.ev, ih]`.
-/
private theorem ev_lprod {ι : Type} (x : ι → ℂ) (l : List (Ex ι)) :
    (lprod l).ev x = (l.map (Ex.ev x)).prod := by
  induction l with
  | nil => simp [lprod, Ex.ev]
  | cons a l ih => simp [lprod, Ex.ev, ih]

/- English proof (translation)
Establish `hd : x i - y i ≠ 0` using `sub_ne_zero.2 h`. Use `⟨Ex.smul (x i - y i)⁻¹ (Ex.add (Ex.gen i) (Ex.smul (-y i) Ex.one)), ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Ex.ev]`. Establish `: x i + -y i * 1 = x i - y i` using `by ring`. Rewrite using `[this]`.

Conclude with `inv_mul_cancel₀ hd`. Simplify using `[Ex.ev]`.
-/
private theorem exists_aff {ι : Type} (x y : ι → ℂ) (i : ι) (h : x i ≠ y i) :
    ∃ e : Ex ι, e.ev x = 1 ∧ e.ev y = 0 := by
  have hd : x i - y i ≠ 0 := sub_ne_zero.2 h
  refine ⟨Ex.smul (x i - y i)⁻¹ (Ex.add (Ex.gen i) (Ex.smul (-y i) Ex.one)), ?_, ?_⟩
  · simp only [Ex.ev]
    have : x i + -y i * 1 = x i - y i := by ring
    rw [this]
    exact inv_mul_cancel₀ hd
  · simp [Ex.ev]

/- English proof (translation)
Establish `hex : ∃ j, j ≤ n ∧ satEig (qV E w) n A j ≠ satEig (qV E w) n A' j`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hne (eq_of_satEig_eq (qV_ne_zero w) h h' hc).symm`. Take `⟨j, hj, hj'⟩` from `hex`.

Conclude with `exists_aff (fun j : Fin (n + 1) => satEig (qV E w) n A j) (fun j : Fin (n + 1) => satEig (qV E w) n A' j) ⟨j, Nat.lt_succ_of_le hj⟩ hj'`.
-/
private theorem sep_one (n : ℕ) (w : Pl E) {A A' : Multiset ℂˣ} (h : A.card = n) (h' : A'.card = n)
    (hne : A' ≠ A) : ∃ e : Ex (Fin (n + 1)), ev1 n w e A = 1 ∧ ev1 n w e A' = 0 := by
  have hex : ∃ j, j ≤ n ∧ satEig (qV E w) n A j ≠ satEig (qV E w) n A' j := by
    by_contra hc
    push_neg at hc
    exact hne (eq_of_satEig_eq (qV_ne_zero w) h h' hc).symm
  obtain ⟨j, hj, hj'⟩ := hex
  exact exists_aff (fun j : Fin (n + 1) => satEig (qV E w) n A j)
    (fun j : Fin (n + 1) => satEig (qV E w) n A' j) ⟨j, Nat.lt_succ_of_le hj⟩ hj'

/- English proof (translation)
Take `⟨-, hc, -, hs⟩` from `hP E`. Take `⟨w, ⟨hwZ, hcZ⟩, hsp, hB, hC, hne⟩` from `h`. Break down `(hs S hS w).1 with hw | hw` into its components or cases. Take `⟨e, h1, h0⟩` from `sep_one n w hB hC hne`. Use `⟨w, e, Ex.one, hw, hsp, hwZ, h1, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `[ev1, Ex.ev]`. Rewrite using `[h0, zero_mul]`. Establish `hcc : cPl (cPl w) = w` using `(hc w).1`. Establish `hsp' : IsSplitAt (cPl w)` using `(hc (cPl w)).2.2 (by rw [hcc]; exact fun h => (hc w).2.1 hsp |>.elim h.symm)`. Take `⟨e, h1, h0⟩` from `sep_one n (cPl w) (A := inv (B w)) (A' := inv (C w)) (by simpa [inv] using hB) (by simpa [inv] using hC) (fun h => hne (Multiset.map_injective inv_injective h))`.

Use `⟨cPl w, Ex.one, e, hw, hsp', hcZ, by simp [ev1, Ex.ev], by rw [hcc]; exact h1, ?_⟩` and prove the remaining obligations. Rewrite using `[hcc, h0, mul_zero]`.
-/
private theorem sep_at (hP : Places) (n : ℕ) (S : Set (Pl E)) (hS : IsSection S) (Z : Finset (Pl E))
    (B C : Pl E → Multiset ℂˣ)
    (h : ∃ w, Off Z w ∧ IsSplitAt w ∧ (B w).card = n ∧ (C w).card = n ∧ C w ≠ B w) :
    ∃ (t : Pl E) (e₁ e₂ : Ex (Fin (n + 1))), t ∈ S ∧ IsSplitAt t ∧ t ∉ Z ∧ ev1 n t e₁ (B t) = 1 ∧
      ev1 n t e₂ (inv (B (cPl t))) = 1 ∧ ev1 n t e₁ (C t) * ev1 n t e₂ (inv (C (cPl t))) = 0 := by
  obtain ⟨-, hc, -, hs⟩ := hP E
  obtain ⟨w, ⟨hwZ, hcZ⟩, hsp, hB, hC, hne⟩ := h
  rcases (hs S hS w).1 with hw | hw
  · obtain ⟨e, h1, h0⟩ := sep_one n w hB hC hne
    refine ⟨w, e, Ex.one, hw, hsp, hwZ, h1, ?_, ?_⟩
    · simp [ev1, Ex.ev]
    · rw [h0, zero_mul]
  · have hcc : cPl (cPl w) = w := (hc w).1
    have hsp' : IsSplitAt (cPl w) :=
      (hc (cPl w)).2.2 (by rw [hcc]; exact fun h => (hc w).2.1 hsp |>.elim h.symm)
    obtain ⟨e, h1, h0⟩ := sep_one n (cPl w) (A := inv (B w)) (A' := inv (C w))
      (by simpa [inv] using hB) (by simpa [inv] using hC)
      (fun h => hne (Multiset.map_injective inv_injective h))
    refine ⟨cPl w, Ex.one, e, hw, hsp', hcZ, by simp [ev1, Ex.ev], by rw [hcc]; exact h1, ?_⟩
    rw [hcc, h0, mul_zero]

private def comb {I : Type} [Fintype I] {n : ℕ} (t : I → Pl E) (e : I → Ex (Fin (n + 1))) (w : Pl E) :
    Ex (Fin (n + 1)) :=
  lprod ((Finset.univ : Finset I).toList.map fun j => if t j = w then e j else Ex.one)

/- English proof (translation)
Rewrite using `[← Finset.prod_map_toList]`. Simplify using `only [ev1, comb]`. Rewrite using `[ev_lprod, List.map_map]`. Use `congr 1`. Use `List.map_congr_left fun j _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `by_cases hj : t j = w <;> simp [hj, Ex.ev]`.
-/
private theorem evaluation_combined_test_function {I : Type} [Fintype I] {n : ℕ} (t : I → Pl E) (e : I → Ex (Fin (n + 1)))
    (w : Pl E) (X : Multiset ℂˣ) :
    ev1 n w (comb t e w) X = ∏ j, if t j = w then ev1 n w (e j) X else 1 := by
  rw [← Finset.prod_map_toList]
  simp only [ev1, comb]
  rw [ev_lprod, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  by_cases hj : t j = w <;> simp [hj, Ex.ev]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

/- English proof (translation)
Introduce `hP E _ _ _ n S hS Z I _ B C h`. Use `haveI := Fintype.ofFinite I`. Use `choose t e₁ e₂ htS hts htZ hB₁ hB₂ hC using fun j => sep_at hP n S hS Z B (C j) (h j)`. Use `⟨Finset.univ.image t, comb t e₁, comb t e₂, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `w hw`.

Take `⟨j, -, rfl⟩` from `Finset.mem_image.1 hw`. Conclude with `⟨htS j, hts j⟩`. Use `Finset.disjoint_left.2 fun w hw hz => ?_` and prove the remaining obligations. Take `⟨j, -, rfl⟩` from `Finset.mem_image.1 hw`. Conclude with `htZ j hz`.

Use `Finset.prod_eq_one fun w _ => ?_` and prove the remaining obligations. Rewrite using `[evaluation_combined_test_function, evaluation_combined_test_function]`. Rewrite using `[show ∀ a b : ℂ, a = 1 → b = 1 → a * b = 1 from fun a b ha hb => by rw [ha, hb, one_mul]]`. Use `Finset.prod_eq_one fun j _ => ?_ split_ifs with hj` and prove the remaining obligations. Substitute `hj` using the available equality.

Conclude with `hB₁ j`. Both sides reduce to the same expression. Use `Finset.prod_eq_one fun j _ => ?_ split_ifs with hj` and prove the remaining obligations. Substitute `hj` using the available equality. Conclude with `hB₂ j`.

Both sides reduce to the same expression. Introduce `j`. Use `Finset.prod_eq_zero (Finset.mem_image_of_mem t (Finset.mem_univ j)) ?_` and prove the remaining obligations. Rewrite using `[evaluation_combined_test_function, evaluation_combined_test_function]`. Break down `mul_eq_zero.1 (hC j) with h0 | h0` into its components or cases.

Conclude with `mul_eq_zero.2 (Or.inl (Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_pos rfl]; exact h0)))`. Conclude with `mul_eq_zero.2 (Or.inr (Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_pos rfl]; exact h0)))`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.rSep :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.RSep := by
  intro hP E _ _ _ n S hS Z I _ B C h
  haveI := Fintype.ofFinite I
  choose t e₁ e₂ htS hts htZ hB₁ hB₂ hC using fun j => sep_at hP n S hS Z B (C j) (h j)
  refine ⟨Finset.univ.image t, comb t e₁, comb t e₂, ?_, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hw
    exact ⟨htS j, hts j⟩
  · refine Finset.disjoint_left.2 fun w hw hz => ?_
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hw
    exact htZ j hz
  · refine Finset.prod_eq_one fun w _ => ?_
    rw [evaluation_combined_test_function, evaluation_combined_test_function]
    rw [show ∀ a b : ℂ, a = 1 → b = 1 → a * b = 1 from fun a b ha hb => by rw [ha, hb, one_mul]]
    · refine Finset.prod_eq_one fun j _ => ?_
      split_ifs with hj
      · subst hj
        exact hB₁ j
      · rfl
    · refine Finset.prod_eq_one fun j _ => ?_
      split_ifs with hj
      · subst hj
        exact hB₂ j
      · rfl
  · intro j
    refine Finset.prod_eq_zero (Finset.mem_image_of_mem t (Finset.mem_univ j)) ?_
    rw [evaluation_combined_test_function, evaluation_combined_test_function]
    rcases mul_eq_zero.1 (hC j) with h0 | h0
    · exact mul_eq_zero.2 (Or.inl (Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_pos rfl]; exact h0)))
    · exact mul_eq_zero.2 (Or.inr (Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_pos rfl]; exact h0)))
