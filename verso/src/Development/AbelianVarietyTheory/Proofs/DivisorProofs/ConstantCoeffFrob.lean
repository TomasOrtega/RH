import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.QLog.Window

section Integral

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem in_top_iff (f : MvPowerSeries σ Q) :
    In (⊤ : Ideal B) f ↔ ∃ s : MvPowerSeries σ B, f = map (algebraMap B Q) s := by
  constructor
  · intro h
    choose b _ hb using h
    let s : MvPowerSeries σ B := fun α => b α
    refine ⟨s, ?_⟩
    ext α
    rw [coeff_map, hb]
    rfl
  · rintro ⟨s, rfl⟩ α
    exact ⟨coeff α s, Submodule.mem_top, by rw [coeff_map]⟩

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem in_zero (N : Ideal B) : In N (0 : MvPowerSeries σ Q) := fun _ =>
  ⟨0, N.zero_mem, by simp⟩

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem in_add {N : Ideal B} {f g : MvPowerSeries σ Q} (hf : In N f) (hg : In N g) :
    In N (f + g) := fun α => by
  obtain ⟨a, ha, ea⟩ := hf α
  obtain ⟨b, hb, eb⟩ := hg α
  exact ⟨a + b, N.add_mem ha hb, by rw [map_add, ea, eb, map_add]⟩

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem in_neg {N : Ideal B} {f : MvPowerSeries σ Q} (hf : In N f) : In N (-f) := fun α => by
  obtain ⟨a, ha, ea⟩ := hf α
  exact ⟨-a, N.neg_mem ha, by rw [map_neg, ea, map_neg]⟩

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem in_smul {N : Ideal B} {f : MvPowerSeries σ Q} (hf : In N f) (b : B) :
    In N (algebraMap B Q b • f) := fun α => by
  obtain ⟨a, ha, ea⟩ := hf α
  exact ⟨b * a, N.mul_mem_left b ha, by rw [map_smul, smul_eq_mul, ea, ← map_mul]⟩

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem in_sum {N : Ideal B} {ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ Q)
    (hf : ∀ i ∈ s, In N (f i)) : In N (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using in_zero (σ := σ) (Q := Q) N
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact in_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end Integral

section Frob

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] (p : ℕ) [hp : Fact p.Prime]
  {σ : Type} [Finite σ] (s : Q →+* Q)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hasSubst_X_pow : HasSubst (fun i : σ => (X i : MvPowerSeries σ Q) ^ p) :=
  HasSubst.X_pow hp.out.ne_zero

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem frob_add (f g : MvPowerSeries σ Q) : frob p s (f + g) = frob p s f + frob p s g := by
  unfold frob
  rw [map_add, subst_add (hasSubst_X_pow p)]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem frob_zero : frob p s (0 : MvPowerSeries σ Q) = 0 := by
  have h := frob_add p s (0 : MvPowerSeries σ Q) 0
  rw [add_zero] at h
  exact left_eq_add.1 h

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem frob_sub (f g : MvPowerSeries σ Q) : frob p s (f - g) = frob p s f - frob p s g := by
  unfold frob
  rw [map_sub, subst_sub (hasSubst_X_pow p)]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.
-/
theorem map_smul' {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (r : R)
    (f : MvPowerSeries σ R) : map φ (r • f) = φ r • map φ f := by
  ext α
  rw [coeff_map, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul, coeff_map, map_mul]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem frob_smul (r : Q) (f : MvPowerSeries σ Q) : frob p s (r • f) = s r • frob p s f := by
  unfold frob
  rw [map_smul', subst_smul (hasSubst_X_pow p)]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem frob_sum {ι : Type} (t : Finset ι) (f : ι → MvPowerSeries σ Q) :
    frob p s (∑ i ∈ t, f i) = ∑ i ∈ t, frob p s (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using frob_zero p s
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, frob_add, ih]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem frob_comb (σ' : B →+* B) (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (σ' b))
    {ι : Type} [Fintype ι] (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    frob p s (comb b e) = comb (fun i => σ' (b i)) fun i => frob p s (e i) := by
  unfold comb
  rw [frob_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [frob_smul, hs]

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem constantCoeff_frob {f : MvPowerSeries σ Q} (hf : constantCoeff f = 0) :
    constantCoeff (frob p s f) = 0 := by
  unfold frob
  refine constantCoeff_subst_eq_zero (hasSubst_X_pow p) (fun i => ?_) ?_
  · rw [map_pow, constantCoeff_X, zero_pow hp.out.ne_zero]
  · rw [constantCoeff_map, hf, map_zero]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem in_frob (σ' : B →+* B) (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (σ' b))
    {f : MvPowerSeries σ Q} (hf : In (⊤ : Ideal B) f) : In (⊤ : Ideal B) (frob p s f) := by
  obtain ⟨t, rfl⟩ := (in_top_iff f).1 hf
  refine (in_top_iff _).2 ⟨subst (fun i : σ => (X i : MvPowerSeries σ B) ^ p) (map σ' t), ?_⟩
  have hm : map s (map (algebraMap B Q) t) = map (algebraMap B Q) (map σ' t) := by
    ext α
    simp only [coeff_map, hs]
  unfold frob
  rw [hm, map_subst (HasSubst.X_pow hp.out.ne_zero)]
  simp only [map_pow, map_X]

end Frob

section Cob

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem map_formalGroupLawCoboundaryOne_eq {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (h : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) R) :
    map φ (cob1 μ f) = cob1 (fun i => map φ (μ i)) (map φ f) := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, map_subst (hasSubst_of_constantCoeff_zero h),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  simp only [map_X]

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ}
  {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem constantCoeff_up (hμ : ∀ i, constantCoeff (μ i) = 0) (i : Fin d) :
    constantCoeff (up Q μ i) = 0 := by
  rw [up, constantCoeff_map, hμ, map_zero]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ql_zero (hμ : ∀ i, constantCoeff (μ i) = 0) (N : Ideal B) :
    QL μ N (0 : MvPowerSeries (Fin d) Q) := by
  refine ⟨map_zero _, fun i => ⟨0, N.zero_mem, by simp [lin]⟩, ?_⟩
  have h := formalCoboundary_smul (constantCoeff_up (Q := Q) hμ) (0 : Q) 0
  rw [zero_smul, zero_smul] at h
  rw [h]
  exact in_zero N

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ql_add_smul (hμ : ∀ i, constantCoeff (μ i) = 0) {N : Ideal B}
    {f g : MvPowerSeries (Fin d) Q} (hf : QL μ N f) (hg : QL μ N g) (b : B) :
    QL μ N (f + algebraMap B Q b • g) := by
  refine ⟨?_, fun i => ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, map_add, map_smul, coeff_zero_eq_constantCoeff_apply,
      coeff_zero_eq_constantCoeff_apply, hf.1, hg.1, smul_zero, add_zero]
  · obtain ⟨a, ha, ea⟩ := hf.2.1 i
    obtain ⟨a', ha', ea'⟩ := hg.2.1 i
    refine ⟨a + b * a', N.add_mem ha (N.mul_mem_left b ha'), ?_⟩
    simp only [lin] at ea ea' ⊢
    rw [map_add, map_smul, ea, ea', smul_eq_mul, map_add, map_mul]
  · rw [formalCoboundary_add (constantCoeff_up hμ), formalCoboundary_smul (constantCoeff_up hμ)]
    exact in_add hf.2.2 (in_smul hg.2.2 b)

/- English proof (translation)
Replace the relevant objects with their definitions. Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem ql_comb (hμ : ∀ i, constantCoeff (μ i) = 0) {N : Ideal B} {ι : Type} [Fintype ι]
    (e : ι → MvPowerSeries (Fin d) Q) (he : ∀ i, QL μ N (e i)) (b : ι → B) :
    QL μ N (comb b e) := by
  classical
  unfold comb
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using ql_zero (Q := Q) hμ N
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, add_comm]
    exact ql_add_smul hμ ih (he a) (b a)

end Cob

end GlobalTheory.QLog.Window
