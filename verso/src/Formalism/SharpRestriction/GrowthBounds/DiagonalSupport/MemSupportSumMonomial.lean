import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ValLamOfSubset

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G

section MH

variable {A : Type*} [CommRing A] {ι : Type*} {n : ℕ}

def IsMH (P : MvPolynomial (ι × Fin n) A) (δ : ι → ℕ) : Prop := ∀ m ∈ P.support, ∀ i, multideg m i = δ i

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem multideg_add (a b : ι × Fin n →₀ ℕ) (i : ι) : multideg (a + b) i = multideg a i + multideg b i := by
  simp [multideg, Finsupp.add_apply, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem multideg_zero (i : ι) : multideg (0 : ι × Fin n →₀ ℕ) i = 0 := by
  simp [multideg]

/- English proof (translation)
Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem multideg_single (v : ι × Fin n) (b : ℕ) (i : ι) :
    multideg (Finsupp.single v b) i = if v.1 = i then b else 0 := by
  unfold multideg
  obtain ⟨vi, vc⟩ := v
  by_cases h : vi = i
  · subst h
    simp [Finsupp.single_apply]
  · simp [Finsupp.single_apply, h]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem IsMH.congr {P : MvPolynomial (ι × Fin n) A} {δ δ' : ι → ℕ} (h : IsMH P δ) (hd : ∀ i, δ i = δ' i) : IsMH P δ' :=
  fun m hm i => (h m hm i).trans (hd i)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem IsMH.add {P Q : MvPolynomial (ι × Fin n) A} {δ : ι → ℕ} (hP : IsMH P δ) (hQ : IsMH Q δ) : IsMH (P + Q) δ := by
  intro m hm
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hP m h
  · exact hQ m h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem IsMH.zero (δ : ι → ℕ) : IsMH (0 : MvPolynomial (ι × Fin n) A) δ := by
  intro m hm
  simp at hm

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem IsMH.sum {α : Type*} (s : Finset α) (f : α → MvPolynomial (ι × Fin n) A) (δ : ι → ℕ)
    (h : ∀ x ∈ s, IsMH (f x) δ) : IsMH (∑ x ∈ s, f x) δ := by
  induction s using Finset.induction_on with
  | empty => simpa using IsMH.zero δ
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).add (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.
-/
theorem IsMH.mul {P Q : MvPolynomial (ι × Fin n) A} {δ ε : ι → ℕ} (hP : IsMH P δ) (hQ : IsMH Q ε) :
    IsMH (P * Q) (fun i => δ i + ε i) := by
  intro m hm i
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hm)
  rw [multideg_add, hP a ha i, hQ b hb i]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem IsMH.monomial (u : ι × Fin n →₀ ℕ) (c : A) : IsMH (MvPolynomial.monomial u c) (fun i => multideg u i) := by
  intro m hm i
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem IsMH.C (c : A) : IsMH (MvPolynomial.C c : MvPolynomial (ι × Fin n) A) (fun _ => 0) := by
  rw [MvPolynomial.C_apply]
  exact (IsMH.monomial 0 c).congr fun i => multideg_zero i

/- English proof (translation)
Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem IsMH.pow {P : MvPolynomial (ι × Fin n) A} {δ : ι → ℕ} (hP : IsMH P δ) (b : ℕ) :
    IsMH (P ^ b) (fun i => b * δ i) := by
  induction b with
  | zero =>
    rw [pow_zero, ← MvPolynomial.C_1]
    exact (IsMH.C 1).congr fun i => by simp
  | succ b ih =>
    rw [pow_succ]
    exact (ih.mul hP).congr fun i => by ring

end MH

section Tw

variable {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem twistSub_X_MH (v : ι × Fin n) : IsMH (twistSub (R := R) LL S j (X v)) (fun i => if v.1 = i then 1 else 0) := by
  have hX : ∀ w : ι × Fin n, IsMH (X w : MvPolynomial (ι × Fin n) (GLLaurent R n))
      (fun i => if w.1 = i then 1 else 0) :=
    fun w => (IsMH.monomial (Finsupp.single w 1) 1).congr fun i => multideg_single w 1 i
  have hCX : ∀ (c : GLLaurent R n) (b : Fin n), IsMH (MvPolynomial.C c * X (v.1, b) :
      MvPolynomial (ι × Fin n) (GLLaurent R n)) (fun i => if v.1 = i then 1 else 0) :=
    fun c b => ((IsMH.C c).mul (hX (v.1, b))).congr fun i => by simp
  simp only [twistSub, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
  split_ifs
  · exact IsMH.sum _ _ _ fun b _ => hCX _ b
  · exact IsMH.sum _ _ _ fun b _ => hCX _ b
  · exact hX v

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem twistSub_monomial_MH (u : ι × Fin n →₀ ℕ) :
    ∀ c : R, IsMH (twistSub LL S j (MvPolynomial.monomial u c)) (fun i => multideg u i) := by
  refine Finsupp.induction u ?_ ?_
  · intro c
    rw [← MvPolynomial.C_apply]
    simp only [twistSub, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
    exact (IsMH.C _).congr fun i => (multideg_zero i).symm
  · intro a b f _ _ ih c
    have hm : (MvPolynomial.monomial (Finsupp.single a b + f) c : MvPolynomial (ι × Fin n) R) =
        X a ^ b * MvPolynomial.monomial f c := by
      rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul]
    rw [hm, map_mul, map_pow]
    refine (((twistSub_X_MH LL S j a).pow b).mul (ih c)).congr fun i => ?_
    rw [multideg_add, multideg_single]
    split_ifs <;> simp

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem twistSub_support (F : MvPolynomial (ι × Fin n) R) (m : ι × Fin n →₀ ℕ)
    (hm : m ∈ (twistSub LL S j F).support) : ∃ u ∈ F.support, ∀ i, multideg m i = multideg u i := by
  rw [F.as_sum, map_sum] at hm
  obtain ⟨u, hu, hmu⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  exact ⟨u, hu, twistSub_monomial_MH LL S j u _ m hmu⟩

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem twistSub_monomial_off (M : ι × Fin n →₀ ℕ) (h : ∀ v ∈ M.support, v.1 ∉ S) :
    twistSub (R := R) LL S j (MvPolynomial.monomial M 1) = MvPolynomial.monomial M 1 := by
  simp only [twistSub, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, RingHom.comp_apply, map_one,
    one_mul]
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul]
  apply Finsupp.prod_congr
  intro v hv
  simp [h v hv]

end Tw

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem mem_support_sum_monomial {A σ α : Type*} [CommRing A] (s : Finset α) (g : α → σ →₀ ℕ) (c : α → A) (m : σ →₀ ℕ)
    (hm : m ∈ (∑ x ∈ s, MvPolynomial.monomial (g x) (c x)).support) : ∃ x ∈ s, g x = m := by
  classical
  obtain ⟨x, hx, hmx⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  exact ⟨x, hx, (Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hmx)).symm⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem valComp : ValComp := by
  intro R _ _ ι n _ LL S F δ
  classical
  have hcoef : ∀ u, (homComp δ F).coeff u = if (∀ i, multideg u i = δ i) then F.coeff u else 0 := by
    intro u
    unfold homComp
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    first
      | rw [Finset.sum_ite_eq']
      | rw [Finset.sum_ite_eq]
    simp only [Finset.mem_filter, MvPolynomial.mem_support_iff]
    by_cases h : ∀ i, multideg u i = δ i <;> by_cases h2 : F.coeff u = 0 <;> simp [h, h2]
  have hsplit : ∀ (j : Fin n) m, (twistSub LL S j (homComp δ F)).coeff m =
      if (∀ i, multideg m i = δ i) then (twistSub LL S j F).coeff m else 0 := by
    intro j m
    have hF : F = homComp δ F + (F - homComp δ F) := by ring
    have hrest : ∀ u ∈ (F - homComp δ F).support, ¬ ∀ i, multideg u i = δ i := by
      intro u hu hcond
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, hcoef, if_pos hcond, sub_self] at hu
      exact hu rfl
    have hhom : ∀ u ∈ (homComp δ F).support, ∀ i, multideg u i = δ i := by
      intro u hu
      by_contra hc
      rw [MvPolynomial.mem_support_iff, hcoef, if_neg hc] at hu
      exact hu rfl
    by_cases hm : ∀ i, multideg m i = δ i
    · rw [if_pos hm]
      conv_rhs => rw [hF, map_add, MvPolynomial.coeff_add]
      have h0 : (twistSub LL S j (F - homComp δ F)).coeff m = 0 := by
        by_contra hne
        obtain ⟨u, hu, hmu⟩ := twistSub_support LL S j _ m (MvPolynomial.mem_support_iff.mpr hne)
        exact hrest u hu fun i => (hmu i).symm.trans (hm i)
      rw [h0, add_zero]
    · rw [if_neg hm]
      by_contra hne
      obtain ⟨u, hu, hmu⟩ := twistSub_support LL S j _ m (MvPolynomial.mem_support_iff.mpr hne)
      exact hm fun i => (hmu i).trans (hhom u hu i)
  refine val_lam_of_subset LL S LL S (homComp δ F) F fun j => sDegs_subset_of LL S LL S j (homComp δ F) F ?_
  intro k hk m
  rw [hsplit]
  split_ifs
  · exact hk m
  · first
      | simp
      | rfl

end Formalism.MainNotions.Proposition5Numerics
