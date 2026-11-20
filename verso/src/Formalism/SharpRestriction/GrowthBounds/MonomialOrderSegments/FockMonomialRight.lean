import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.MemPolKIff
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapCastMono

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K]

section Elem

variable (v : AddValuation K (WithTop ℚ))

/- English proof (translation)
Replace the relevant objects with their definitions. Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem vge_iff' (a : ℝ) (x : K) : vge v a x ↔ ∀ n : ℚ, v x = (n : WithTop ℚ) → a ≤ n := by
  unfold vge vR
  cases h : v x with
  | top => simp
  | coe m =>
    simp only [WithTop.map_coe, WithTop.coe_le_coe, WithTop.coe_inj]
    constructor
    · intro h1 n hn; rw [← hn]; exact h1
    · intro h1; exact h1 m rfl

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities.
-/
theorem vge_zero' (a : ℝ) : vge v a (0 : K) := by
  rw [vge_iff']; intro n hn; rw [AddValuation.map_zero] at hn; exact absurd hn (by simp)

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem vge_mono' {a b : ℝ} {x : K} (hab : b ≤ a) (h : vge v a x) : vge v b x := by
  rw [vge_iff'] at *; intro n hn; exact hab.trans (h n hn)

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem vge_add' {a : ℝ} {x y : K} (hx : vge v a x) (hy : vge v a y) : vge v a (x + y) := by
  rw [vge_iff'] at *
  intro n hn
  have h := v.map_add x y
  rw [hn] at h
  rcases min_le_iff.mp h with h1 | h1
  · obtain ⟨m, hm, hmn⟩ := WithTop.le_coe_iff.mp h1
    exact (hx m hm).trans (by exact_mod_cast hmn)
  · obtain ⟨m, hm, hmn⟩ := WithTop.le_coe_iff.mp h1
    exact (hy m hm).trans (by exact_mod_cast hmn)

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Split into cases according to the possible forms of the given data. Treat this case separately.

Simplify using the standard rewrite rules. Treat this case separately. Split into cases according to the possible forms of the given data. Treat this case separately. Simplify using the standard rewrite rules.

Treat this case separately. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem vge_mul' {a b : ℝ} {x y : K} (hx : vge v a x) (hy : vge v b y) : vge v (a + b) (x * y) := by
  rw [vge_iff'] at *
  intro n hn
  rw [v.map_mul] at hn
  cases h1 : v x with
  | top => rw [h1] at hn; simp at hn
  | coe m =>
    cases h2 : v y with
    | top => rw [h2] at hn; simp at hn
    | coe k =>
      rw [h1, h2, ← WithTop.coe_add, WithTop.coe_inj] at hn
      have := hx m h1
      have := hy k h2
      rw [← hn]; push_cast; linarith

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem vge_sum' {ι : Type} {a : ℝ} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, vge v a (f i)) :
    vge v a (∑ i ∈ s, f i) := by
  first | exact UpperTheory.Reformulated.B.Qh31.vge_sum .. | (apply UpperTheory.Reformulated.B.Qh31.vge_sum <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh31.vge_sum <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh31.vge_sum <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh31.vge_sum <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh31.vge_sum <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› v ι a s f h | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› v ι a s f | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› v ι a s | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› v ι a | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› v ι | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› v | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem fact_ne_zero' {σ : Type} (α : σ →₀ ℕ) : fact α ≠ 0 := by
  unfold fact Finsupp.prod
  exact Finset.prod_ne_zero_iff.mpr fun x _ => Nat.factorial_ne_zero _

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem vge_vN' (n : ℕ) : vge v (vN v n) (n : K) := by
  rw [vge_iff']
  intro m hm
  unfold vN
  rw [hm]; simp

end Elem

section Fock

variable {σ : Type}

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fock_eq_sum_of (F G : MvPolynomial σ K) (s : Finset (σ →₀ ℕ))
    (h : ∀ α, F.coeff α ≠ 0 → G.coeff α ≠ 0 → α ∈ s) :
    fock F G = ∑ α ∈ s, F.coeff α * G.coeff α * (fact α : K) := by
  classical
  unfold fock
  have h1 : ∑ α ∈ F.support, F.coeff α * G.coeff α * (fact α : K) =
      ∑ α ∈ F.support ∪ s, F.coeff α * G.coeff α * (fact α : K) := by
    apply Finset.sum_subset Finset.subset_union_left
    intro α _ hα
    rw [notMem_support_iff.mp hα]; simp
  have h2 : ∑ α ∈ s, F.coeff α * G.coeff α * (fact α : K) =
      ∑ α ∈ F.support ∪ s, F.coeff α * G.coeff α * (fact α : K) := by
    apply Finset.sum_subset Finset.subset_union_right
    intro α _ hα
    by_cases hF : F.coeff α = 0
    · rw [hF]; simp
    · by_cases hG : G.coeff α = 0
      · rw [hG]; simp
      · exact absurd (h α hF hG) hα
  rw [h1, h2]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem fock_eq_sum (F G : MvPolynomial σ K) (s : Finset (σ →₀ ℕ))
    (h : F.support ⊆ s ∨ G.support ⊆ s) :
    fock F G = ∑ α ∈ s, F.coeff α * G.coeff α * (fact α : K) := by
  apply fock_eq_sum_of
  intro α hF hG
  rcases h with h | h
  · exact h (mem_support_iff.mpr hF)
  · exact h (mem_support_iff.mpr hG)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem fock_comm (F G : MvPolynomial σ K) : fock F G = fock G F := by
  rw [fock_eq_sum F G G.support (Or.inr (Finset.Subset.refl _))]
  unfold fock
  exact Finset.sum_congr rfl fun α _ => by ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fock_add_left (F F' G : MvPolynomial σ K) : fock (F + F') G = fock F G + fock F' G := by
  rw [fock_eq_sum (F + F') G G.support (Or.inr (Finset.Subset.refl _)),
    fock_eq_sum F G G.support (Or.inr (Finset.Subset.refl _)),
    fock_eq_sum F' G G.support (Or.inr (Finset.Subset.refl _)), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun α _ => by rw [coeff_add]; ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem fock_add_right (F G G' : MvPolynomial σ K) : fock F (G + G') = fock F G + fock F G' := by
  rw [fock_comm, fock_add_left, fock_comm G, fock_comm G']

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fock_smul_left (c : K) (F G : MvPolynomial σ K) : fock (c • F) G = c * fock F G := by
  rw [fock_eq_sum (c • F) G G.support (Or.inr (Finset.Subset.refl _)),
    fock_eq_sum F G G.support (Or.inr (Finset.Subset.refl _)), Finset.mul_sum]
  exact Finset.sum_congr rfl fun α _ => by rw [coeff_smul, smul_eq_mul]; ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem fock_smul_right (c : K) (F G : MvPolynomial σ K) : fock F (c • G) = c * fock F G := by
  rw [fock_comm, fock_smul_left, fock_comm]

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem fock_zero_left (G : MvPolynomial σ K) : fock 0 G = 0 := by
  unfold fock; simp

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem fock_neg_left (F G : MvPolynomial σ K) : fock (-F) G = -fock F G := by
  have := fock_smul_left (-1 : K) F G
  simpa using this

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem fock_neg_right (F G : MvPolynomial σ K) : fock F (-G) = -fock F G := by
  rw [fock_comm, fock_neg_left, fock_comm]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem fock_sub_left (F F' G : MvPolynomial σ K) : fock (F - F') G = fock F G - fock F' G := by
  rw [sub_eq_add_neg, fock_add_left, fock_neg_left, ← sub_eq_add_neg]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem fock_sub_right (F G G' : MvPolynomial σ K) : fock F (G - G') = fock F G - fock F G' := by
  rw [sub_eq_add_neg, fock_add_right, fock_neg_right, ← sub_eq_add_neg]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem fock_sum_left {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ K) (G : MvPolynomial σ K) :
    fock (∑ i ∈ s, f i) G = ∑ i ∈ s, fock (f i) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fock_zero_left]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, fock_add_left, ih]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fock_sum_right {ι : Type} (s : Finset ι) (F : MvPolynomial σ K) (f : ι → MvPolynomial σ K) :
    fock F (∑ i ∈ s, f i) = ∑ i ∈ s, fock F (f i) := by
  rw [fock_comm, fock_sum_left]
  exact Finset.sum_congr rfl fun i _ => fock_comm _ _

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem fock_monomial_right (F : MvPolynomial σ K) (α : σ →₀ ℕ) (c : K) :
    fock F (monomial α c) = F.coeff α * c * (fact α : K) := by
  classical
  rw [fock_eq_sum F (monomial α c) {α} (Or.inr (support_monomial_subset)), Finset.sum_singleton,
    coeff_monomial, if_pos rfl]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fock_eq_sum_right (F G : MvPolynomial σ K) :
    fock F G = ∑ α ∈ G.support, F.coeff α * G.coeff α * (fact α : K) :=
  fock_eq_sum F G G.support (Or.inr (Finset.Subset.refl _))

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem dg_eq_sum_f (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) :
    dg f F = ∑ α ∈ F.support, monomial α (f α * F.coeff α) := by
  conv_lhs => rw [← support_sum_monomial_coeff F]
  rw [map_sum]
  exact Finset.sum_congr rfl fun α _ => dg_monomial f α _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem support_dg_subset (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) :
    (dg f F).support ⊆ F.support := by
  intro α hα
  rw [mem_support_iff, coeff_dg] at hα
  exact mem_support_iff.mpr (right_ne_zero_of_mul hα)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem gaAct_eq_dg (D : TwistData K) (G : MvPolynomial (D.OL × Fin D.r) K) :
    D.gaAct G = dg D.ga G := by
  rw [dg_eq_sum_f]; rfl

end Fock

section BB

variable (v : AddValuation K (WithTop ℚ)) {σ : Type}

/- English proof (translation)
Replace the relevant objects with their definitions. Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.
-/
theorem vge_sub_iff (a w : ℝ) (x : K) :
    vge v (a - w) x ↔ ((a : ℝ) : WithTop ℝ) ≤ vR v x + ((w : ℝ) : WithTop ℝ) := by
  unfold vge
  cases vR v x with
  | top => simp
  | coe y =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe, sub_le_iff_le_add]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem bge_iff (a : ℝ) (F : MvPolynomial σ K) :
    bge v a F ↔ ((a : ℝ) : WithTop ℝ) ≤ vBB v F := by
  unfold bge vBB
  rw [Finset.le_inf_iff]
  constructor
  · intro h α _
    exact (vge_sub_iff v a _ _).mp (h α)
  · intro h α
    by_cases hα : α ∈ F.support
    · exact (vge_sub_iff v a _ _).mpr (h α hα)
    · rw [notMem_support_iff.mp hα]; exact vge_zero' v _

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem bge_mono {a b : ℝ} {F : MvPolynomial σ K} (hab : b ≤ a) (h : bge v a F) : bge v b F :=
  fun α => vge_mono' v (by linarith) (h α)

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem bge_monomial {a : ℝ} (α : σ →₀ ℕ) {c : K} (hc : vge v a c) :
    bge v (a + vN v (fact α) / 2) (monomial α c) := fun β => by
  classical
  rw [coeff_monomial]
  split_ifs with h
  · rw [← h]; exact vge_mono' v (by linarith) hc
  · exact vge_zero' v _

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem bge_dg {a b : ℝ} {f : (σ →₀ ℕ) → K} {F : MvPolynomial σ K} (hf : ∀ α, vge v a (f α))
    (hF : bge v b F) : bge v (a + b) (dg f F) := fun α => by
  rw [coeff_dg]
  exact vge_mono' v (by linarith) (vge_mul' v (hf α) (hF α))

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Replace the relevant objects with their definitions.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Split into cases according to the possible forms of the given data. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem exists_of_vBB_zero (F : MvPolynomial σ K) (h : vBB v F = 0) :
    (∃ α ∈ F.support, vge v (-(vN v (fact α)) / 2) (F.coeff α) ∧
      vle v (-(vN v (fact α)) / 2) (F.coeff α)) ∧ bge v 0 F := by
  refine ⟨?_, (bge_iff v 0 F).mpr (by rw [h]; rfl)⟩
  have hne : F.support.Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    unfold vBB at h
    rw [hc, Finset.inf_empty] at h
    exact absurd h (by simp)
  obtain ⟨α, hα, hinf⟩ := Finset.exists_mem_eq_inf F.support hne
    (fun α => vR v (F.coeff α) + ((((v (fact α : K)).untopD 0 : ℚ) : ℝ) / 2 : ℝ))
  refine ⟨α, hα, ?_⟩
  have h0 : vR v (F.coeff α) + ((vN v (fact α) / 2 : ℝ) : WithTop ℝ) = 0 := by
    rw [← h]; exact hinf.symm
  unfold vge vle
  cases hx : vR v (F.coeff α) with
  | top => rw [hx] at h0; simp at h0
  | coe y =>
    rw [hx, ← WithTop.coe_add] at h0
    have h1 : y + vN v (fact α) / 2 = 0 := by exact_mod_cast h0
    have h2 : y = -(vN v (fact α)) / 2 := by linarith
    rw [h2]
    exact ⟨le_refl _, le_refl _⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem vge_fock {a b : ℝ} {F G : MvPolynomial σ K} (hF : bge v a F) (hG : bge v b G) :
    vge v (a + b) (fock F G) := by
  unfold fock
  apply vge_sum'
  intro α _
  have h1 := vge_mul' v (vge_mul' v (hF α) (hG α)) (vge_vN' v (fact α))
  exact vge_mono' v (by linarith) h1

end BB

end Formalism.MainNotions.PlaneGram
