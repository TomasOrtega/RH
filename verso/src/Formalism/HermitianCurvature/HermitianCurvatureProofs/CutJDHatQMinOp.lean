import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatOpA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HomogeneityNaturalDegree

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.QMinOp

open Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem qminorWordSum (k r t : ℕ) (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    ∃ L : List (ℂ × List (B.Mat k r)),
      (∀ cw ∈ L, (∀ X ∈ cw.2, B.unitLie k r X) ∧ cw.2.length ≤ t) ∧
      ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
        B.CkOn (t : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
          qminorOp (Q.EH k r) a b u f g = (L.map fun cw => cw.1 • B.Rw cw.2 f g).sum := by
  let ts : Equiv.Perm (Fin t) → List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) :=
    fun σ => List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), a (σ j), b j)
  refine ⟨(Finset.univ : Finset (Equiv.Perm (Fin t))).toList.flatMap
      (fun σ => (expand k r (ts σ)).map fun cw => (((Equiv.Perm.sign σ : ℤ) : ℂ) * cw.1, cw.2)), ?_, ?_⟩
  · intro cw hcw
    simp only [List.mem_flatMap, List.mem_map] at hcw
    obtain ⟨σ, _, cw', hm', rfl⟩ := hcw
    have := expand_words (k := k) (r := r) (ts σ) cw' hm'
    refine ⟨this.1, this.2.trans ?_⟩
    simp [ts]
  · intro E _ _ UU f hf g hgU hg
    have hloc : ∀ σ, Loc ((ts σ).length : ℕ∞) f g := by
      intro σ
      obtain ⟨U, f', a, b, c, d⟩ := hf g hgU
      refine ⟨U, f', a, b, ?_, d⟩
      simpa [ts] using c
    have e1 : qminorOp (Q.EH k r) a b u f g = ∑ σ, (((Equiv.Perm.sign σ : ℤ) : ℂ)) • foldT (ts σ) f g := by
      simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      congr 1
      simp only [foldT, ts, List.map_ofFn]
      rfl
    rw [e1, sum_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [expand_eq (ts σ) f g hg (hloc σ), List.map_map, ← sum_map_mul_smul]
    rfl

section terms

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Replace the relevant objects with their definitions. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem hsv_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  ext i
  simp

open Classical in

def pTerm (P : B.Mat k r → ℂ) (w : List (B.Mat k r)) : B.DTerm k r Wp Wq where
  coef := fun g => P g • ContinuousLinearMap.id ℂ _
  coefAdj := fun g => star (P g) • ContinuousLinearMap.id ℂ _
  word := if ∀ X ∈ w, B.inLie k r X then w else []
  word_lie := by
    split_ifs with h
    · exact h
    · simp
  adj_id := by
    intro x A B'
    simp only [B.hsInner, _root_.smul_apply, ContinuousLinearMap.id_apply, hsv_smul,
      inner_smul_left, inner_smul_right]
    simp

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem pTerm_word {P : B.Mat k r → ℂ} {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X) :
    (pTerm (Wp := Wp) (Wq := Wq) P w).word = w := by
  simp only [pTerm]
  rw [if_pos hw]

/- English proof (translation)
Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem pTerm_word_le (P : B.Mat k r → ℂ) (w : List (B.Mat k r)) :
    (pTerm (Wp := Wp) (Wq := Wq) P w).word.length ≤ w.length := by
  simp only [pTerm]
  split_ifs
  · exact le_refl _
  · simp

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem inLie_zero : B.inLie k r 0 := by
  unfold B.inLie
  simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem foldr_max_le_lemma (t : ℕ) : ∀ l : List ℕ, (∀ x ∈ l, x ≤ t) → l.foldr max 0 ≤ t := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro h
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
private theorem le_foldr_max_lemma_2 : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil => intro x hx; simp at hx
  | cons a l ih =>
    intro x hx
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_max_left _ _
    · exact le_trans (ih x hx) (le_max_right _ _)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem foldr_max_eq (t : ℕ) : ∀ l : List ℕ, (∀ x ∈ l, x ≤ t) → t ∈ l → l.foldr max 0 = t := by
  intro l hl ht
  exact le_antisymm (foldr_max_le_lemma t l hl) (le_foldr_max_lemma_2 l t ht)

end terms

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the indicated hypotheses using the stated equalities. Substitute using the available equality.

Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem qminOpRep {k r t κ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {ι : Type} (s : Finset ι)
    (a : Fin t → Fin (2 * r + k + 1)) (b : ι → Fin t → Fin (2 * r + k + 1)) (β : ι → B.Mat k r → ℂ)
    (hβ : ∀ j ∈ s, U.IsPolyDeg κ (β j)) (u : ℂ) :
    ∃ Θ : B.DiffOp k r Wp Wq, PolyOp t κ Θ ∧ B.opOrder Θ = t ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn (t : ℕ∞) UU F → ∀ g ∈ UU, g ∈ B.GV k r →
        B.opApply Θ F g = ∑ j ∈ s, β j g • qminorOp (Q.EH k r) a (b j) u F g := by
  have h := fun j => qminorWordSum k r t a (b j) u
  choose L hL hE using h
  let Θ₁ : B.DiffOp k r Wp Wq :=
    s.toList.flatMap fun j => (L j).map fun cw => pTerm (fun g => β j g * cw.1) cw.2
  let T₀ : B.DTerm k r Wp Wq := pTerm (fun _ => 0) (List.replicate t 0)
  have hT₀ : T₀.word = List.replicate t 0 := pTerm_word (fun X hX => by
    rw [List.eq_of_mem_replicate hX]; exact inLie_zero)
  refine ⟨Θ₁ ++ [T₀], ?_, ?_, ?_⟩
  · intro Tm hTm
    rcases List.mem_append.1 hTm with h1 | h1
    · simp only [Θ₁, List.mem_flatMap, List.mem_map, Finset.mem_toList] at h1
      obtain ⟨j, hj, cw, hcw, rfl⟩ := h1
      refine ⟨(pTerm_word_le _ _).trans (hL j cw hcw).2, fun g => β j g * cw.1, ?_, fun g => rfl, fun g => rfl⟩
      have := Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_mul (hβ j hj) (Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_const cw.1 0)
      simpa using this
    · rw [List.mem_singleton] at h1
      subst h1
      refine ⟨by rw [hT₀]; simp, fun _ => 0, Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_const 0 κ, fun g => rfl, fun g => rfl⟩
  · unfold B.opOrder
    apply foldr_max_eq
    · intro x hx
      simp only [List.mem_map, List.mem_append, List.mem_singleton] at hx
      obtain ⟨Tm, hTm | rfl, rfl⟩ := hx
      · simp only [Θ₁, List.mem_flatMap, List.mem_map, Finset.mem_toList] at hTm
        obtain ⟨j, _, cw, hcw, rfl⟩ := hTm
        exact (pTerm_word_le _ _).trans (hL j cw hcw).2
      · rw [hT₀]; simp
    · simp only [List.mem_map, List.mem_append, List.mem_singleton]
      exact ⟨T₀, Or.inr rfl, by rw [hT₀]; simp⟩
  · intro UU F hF g hgU hg
    have hT₀a : T₀.coef g (B.Rw T₀.word F g) = 0 := by
      change ((0 : ℂ) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (B.Rw T₀.word F g) = 0
      simp
    simp only [B.opApply, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, hT₀a,
      add_zero, Θ₁]
    rw [sum_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hE j _ UU F hF g hgU hg, List.map_map, ← sum_map_mul_smul]
    congr 1
    apply List.map_congr_left
    intro cw hcw
    simp only [Function.comp_apply]
    rw [pTerm_word (fun X hX => ((hL j cw hcw).1 X hX).1)]
    change ((β j g * cw.1) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (B.Rw cw.2 F g) = _
    rfl

section basic₂

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem polyOp_mono {o o' κ κ' : ℕ} {Θ : B.DiffOp k r Wp Wq} (h : PolyOp o κ Θ) (ho : o ≤ o') (hκ : κ ≤ κ') :
    PolyOp o' κ' Θ := by
  unfold PolyOp at *
  intro Tm hTm
  obtain ⟨h1, P, hP, h2, h3⟩ := h Tm hTm
  obtain ⟨q, hq, hq'⟩ := hP
  exact ⟨h1.trans ho, P, ⟨q, hq.trans hκ, hq'⟩, h2, h3⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem polyOp_append {o κ : ℕ} {Θ₁ Θ₂ : B.DiffOp k r Wp Wq} (h₁ : PolyOp o κ Θ₁) (h₂ : PolyOp o κ Θ₂) :
    PolyOp o κ (Θ₁ ++ Θ₂) := by
  unfold PolyOp at *
  intro Tm hTm
  rcases List.mem_append.mp hTm with h | h
  · exact h₁ Tm h
  · exact h₂ Tm h

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem opApply_append (Θ₁ Θ₂ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    B.opApply (Θ₁ ++ Θ₂) F g = B.opApply Θ₁ F g + B.opApply Θ₂ F g := by
  unfold B.opApply
  rw [List.map_append, List.sum_append]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
private theorem foldr_max_init_lemma_3 : ∀ (l : List ℕ) (b : ℕ), l.foldr max b = max (l.foldr max 0) b := by
  intro l
  induction l with
  | nil => intro b; simp
  | cons a l ih =>
    intro b
    simp only [List.foldr_cons]
    rw [ih b, max_assoc]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem opOrder_append (Θ₁ Θ₂ : B.DiffOp k r Wp Wq) :
    B.opOrder (Θ₁ ++ Θ₂) = max (B.opOrder Θ₁) (B.opOrder Θ₂) := by
  unfold B.opOrder
  rw [List.map_append, List.foldr_append]
  exact foldr_max_init_lemma_3 _ _

end basic₂

def QMinorCov : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (Pm Qm : Matrix (Fin n) (Fin n) ℂ),
    Qm * Pm = 1 → ∀ (a b : Fin t → Fin n) (u : ℂ),
      qminor (Formalism.FourierDecayAlt.Q.Econj E Pm Qm) a b u =
        ∑ a' : Fin t → Fin n, ∑ b' : Fin t → Fin n,
          ((∏ k, Pm (a' k) (a k)) * ∏ k, Qm (b k) (b' k)) • qminor E a' b' u

end

end Formalism.FourierDecayAlt.P.CutMP.QMinOp
