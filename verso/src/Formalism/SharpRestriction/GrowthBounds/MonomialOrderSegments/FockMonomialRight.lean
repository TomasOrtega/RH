import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.MemPolKIff
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapCastMono

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K]

section Elem

variable (v : AddValuation K (WithTop ℚ))

/- English proof (translation)
Unfold `vge vR`. Consider the cases of `h : v x with`. Consider the case `top => simp`. Consider the case `coe m`. Simplify using `only [WithTop.map_coe, WithTop.coe_le_coe, WithTop.coe_inj]`.

Prove the components needed by the constructor for the conclusion. Introduce `h1 n hn`. Rewrite using `[← hn]`. Conclude with `h1`. Introduce `h1`.

Conclude with `h1 m rfl`.
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
Rewrite using `[vge_iff']; intro n hn; rw [AddValuation.map_zero] at hn; exact absurd hn (by simp)`.
-/
theorem vge_zero' (a : ℝ) : vge v a (0 : K) := by
  rw [vge_iff']; intro n hn; rw [AddValuation.map_zero] at hn; exact absurd hn (by simp)

/- English proof (translation)
Rewrite `*` using `[vge_iff']`. Introduce `n hn`. Conclude with `hab.trans (h n hn)`.
-/
theorem vge_mono' {a b : ℝ} {x : K} (hab : b ≤ a) (h : vge v a x) : vge v b x := by
  rw [vge_iff'] at *; intro n hn; exact hab.trans (h n hn)

/- English proof (translation)
Rewrite `*` using `[vge_iff']`. Introduce `n hn`. Establish `h` using `v.map_add x y`. Rewrite `h` using `[hn]`. Break down `min_le_iff.mp h with h1 | h1` into its components or cases.

Take `⟨m, hm, hmn⟩` from `WithTop.le_coe_iff.mp h1`. Conclude with `(hx m hm).trans (by exact_mod_cast hmn)`. Take `⟨m, hm, hmn⟩` from `WithTop.le_coe_iff.mp h1`. Conclude with `(hy m hm).trans (by exact_mod_cast hmn)`.
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
Rewrite `*` using `[vge_iff']`. Introduce `n hn`. Rewrite `hn` using `[v.map_mul]`. Consider the cases of `h1 : v x with`. Consider the case `top => rw [h1] at hn`.

Simplify using `at hn`. Consider the case `coe m`. Consider the cases of `h2 : v y with`. Consider the case `top => rw [h2] at hn`. Simplify using `at hn`.

Consider the case `coe k`. Rewrite `hn` using `[h1, h2, ← WithTop.coe_add, WithTop.coe_inj]`. Use `hx m h1` as an intermediate fact. Use `hy k h2` as an intermediate fact. Rewrite using `[← hn]`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
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
Apply the tactic sequence `first | exact UpperTheory.Reformulated.B.Qh31.vge_sum .. | (apply UpperTheory.Reformulated.B.Qh31.vge_sum <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh31.vge_sum <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh31.vge_sum <;> assumption) | (intros; apply @U …`.
-/
theorem vge_sum' {ι : Type} {a : ℝ} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, vge v a (f i)) :
    vge v a (∑ i ∈ s, f i) := by
  first | exact UpperTheory.Reformulated.B.Qh31.vge_sum .. | (apply UpperTheory.Reformulated.B.Qh31.vge_sum <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh31.vge_sum <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh31.vge_sum <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh31.vge_sum <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh31.vge_sum <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› v ι a s f h | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› v ι a s f | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› v ι a s | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› v ι a | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› v ι | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› v | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K

/- English proof (translation)
Unfold `fact Finsupp.prod`. Conclude with `Finset.prod_ne_zero_iff.mpr fun x _ => Nat.factorial_ne_zero _`.
-/
theorem fact_ne_zero' {σ : Type} (α : σ →₀ ℕ) : fact α ≠ 0 := by
  unfold fact Finsupp.prod
  exact Finset.prod_ne_zero_iff.mpr fun x _ => Nat.factorial_ne_zero _

/- English proof (translation)
Rewrite using `[vge_iff']`. Introduce `m hm`. Unfold `vN`. Rewrite using `[hm]`. Simplify using the standard rewrite rules.
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
Unfold `fock`. Establish `h1 : ∑ α ∈ F.support, F.coeff α * G.coeff α * (fact α : K) = ∑ α ∈ F.support ∪ s, F.coeff α * G.coeff α * (fact α : K)`. Apply `Finset.sum_subset Finset.subset_union_left` to reduce the goal to its premises. Introduce `α _ hα`. Rewrite using `[notMem_support_iff.mp hα]`.

Simplify using the standard rewrite rules. Establish `h2 : ∑ α ∈ s, F.coeff α * G.coeff α * (fact α : K) = ∑ α ∈ F.support ∪ s, F.coeff α * G.coeff α * (fact α : K)`. Apply `Finset.sum_subset Finset.subset_union_right` to reduce the goal to its premises. Introduce `α _ hα`. Distinguish the cases in `hF : F.coeff α = 0`.

Rewrite using `[hF]`. Simplify using the standard rewrite rules. Distinguish the cases in `hG : G.coeff α = 0`. Rewrite using `[hG]`. Simplify using the standard rewrite rules.

Conclude with `absurd (h α hF hG) hα`. Rewrite using `[h1, h2]`.
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
Apply `fock_eq_sum_of` to reduce the goal to its premises. Introduce `α hF hG`. Break down `h with h | h` into its components or cases. Conclude with `h (mem_support_iff.mpr hF)`. Conclude with `h (mem_support_iff.mpr hG)`.
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
Rewrite using `[fock_eq_sum F G G.support (Or.inr (Finset.Subset.refl _))]`. Unfold `fock`. Conclude with `Finset.sum_congr rfl fun α _ => by ring`.
-/
theorem fock_comm (F G : MvPolynomial σ K) : fock F G = fock G F := by
  rw [fock_eq_sum F G G.support (Or.inr (Finset.Subset.refl _))]
  unfold fock
  exact Finset.sum_congr rfl fun α _ => by ring

/- English proof (translation)
Rewrite using `[fock_eq_sum (F + F') G G.support (Or.inr (Finset.Subset.refl _)), fock_eq_sum F G G.support (Or.inr (Finset.Subset.refl _)), fock_eq_sum F' G G.support (Or.inr (Finset.Subset.refl _)), ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun α _ => by rw [coeff_add]; ring`.
-/
theorem fock_add_left (F F' G : MvPolynomial σ K) : fock (F + F') G = fock F G + fock F' G := by
  rw [fock_eq_sum (F + F') G G.support (Or.inr (Finset.Subset.refl _)),
    fock_eq_sum F G G.support (Or.inr (Finset.Subset.refl _)),
    fock_eq_sum F' G G.support (Or.inr (Finset.Subset.refl _)), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun α _ => by rw [coeff_add]; ring

/- English proof (translation)
Rewrite using `[fock_comm, fock_add_left, fock_comm G, fock_comm G']`.
-/
theorem fock_add_right (F G G' : MvPolynomial σ K) : fock F (G + G') = fock F G + fock F G' := by
  rw [fock_comm, fock_add_left, fock_comm G, fock_comm G']

/- English proof (translation)
Rewrite using `[fock_eq_sum (c • F) G G.support (Or.inr (Finset.Subset.refl _)), fock_eq_sum F G G.support (Or.inr (Finset.Subset.refl _)), Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun α _ => by rw [coeff_smul, smul_eq_mul]; ring`.
-/
theorem fock_smul_left (c : K) (F G : MvPolynomial σ K) : fock (c • F) G = c * fock F G := by
  rw [fock_eq_sum (c • F) G G.support (Or.inr (Finset.Subset.refl _)),
    fock_eq_sum F G G.support (Or.inr (Finset.Subset.refl _)), Finset.mul_sum]
  exact Finset.sum_congr rfl fun α _ => by rw [coeff_smul, smul_eq_mul]; ring

/- English proof (translation)
Rewrite using `[fock_comm, fock_smul_left, fock_comm]`.
-/
theorem fock_smul_right (c : K) (F G : MvPolynomial σ K) : fock F (c • G) = c * fock F G := by
  rw [fock_comm, fock_smul_left, fock_comm]

/- English proof (translation)
Unfold `fock`. Simplify using the standard rewrite rules.
-/
theorem fock_zero_left (G : MvPolynomial σ K) : fock 0 G = 0 := by
  unfold fock; simp

/- English proof (translation)
Use `fock_smul_left (-1 : K) F G` as an intermediate fact. Simplify using `using this`.
-/
theorem fock_neg_left (F G : MvPolynomial σ K) : fock (-F) G = -fock F G := by
  have := fock_smul_left (-1 : K) F G
  simpa using this

/- English proof (translation)
Rewrite using `[fock_comm, fock_neg_left, fock_comm]`.
-/
theorem fock_neg_right (F G : MvPolynomial σ K) : fock F (-G) = -fock F G := by
  rw [fock_comm, fock_neg_left, fock_comm]

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, fock_add_left, fock_neg_left, ← sub_eq_add_neg]`.
-/
theorem fock_sub_left (F F' G : MvPolynomial σ K) : fock (F - F') G = fock F G - fock F' G := by
  rw [sub_eq_add_neg, fock_add_left, fock_neg_left, ← sub_eq_add_neg]

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, fock_add_right, fock_neg_right, ← sub_eq_add_neg]`.
-/
theorem fock_sub_right (F G G' : MvPolynomial σ K) : fock F (G - G') = fock F G - fock F G' := by
  rw [sub_eq_add_neg, fock_add_right, fock_neg_right, ← sub_eq_add_neg]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [fock_zero_left]`. Consider the case `insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, fock_add_left, ih]`.
-/
theorem fock_sum_left {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ K) (G : MvPolynomial σ K) :
    fock (∑ i ∈ s, f i) G = ∑ i ∈ s, fock (f i) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fock_zero_left]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, fock_add_left, ih]

/- English proof (translation)
Rewrite using `[fock_comm, fock_sum_left]`. Conclude with `Finset.sum_congr rfl fun i _ => fock_comm _ _`.
-/
theorem fock_sum_right {ι : Type} (s : Finset ι) (F : MvPolynomial σ K) (f : ι → MvPolynomial σ K) :
    fock F (∑ i ∈ s, f i) = ∑ i ∈ s, fock F (f i) := by
  rw [fock_comm, fock_sum_left]
  exact Finset.sum_congr rfl fun i _ => fock_comm _ _

/- English proof (translation)
Rewrite using `[fock_eq_sum F (monomial α c) {α} (Or.inr (support_monomial_subset)), Finset.sum_singleton, coeff_monomial, if_pos rfl]`.
-/
theorem fock_monomial_right (F : MvPolynomial σ K) (α : σ →₀ ℕ) (c : K) :
    fock F (monomial α c) = F.coeff α * c * (fact α : K) := by
  classical
  rw [fock_eq_sum F (monomial α c) {α} (Or.inr (support_monomial_subset)), Finset.sum_singleton,
    coeff_monomial, if_pos rfl]

/- English proof (translation)
The claim follows from `fock_eq_sum F G G.support (Or.inr (Finset.Subset.refl _))`.
-/
theorem fock_eq_sum_right (F G : MvPolynomial σ K) :
    fock F G = ∑ α ∈ G.support, F.coeff α * G.coeff α * (fact α : K) :=
  fock_eq_sum F G G.support (Or.inr (Finset.Subset.refl _))

/- English proof (translation)
Use `conv_lhs => rw [← support_sum_monomial_coeff F]`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun α _ => dg_monomial f α _`.
-/
theorem dg_eq_sum_f (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) :
    dg f F = ∑ α ∈ F.support, monomial α (f α * F.coeff α) := by
  conv_lhs => rw [← support_sum_monomial_coeff F]
  rw [map_sum]
  exact Finset.sum_congr rfl fun α _ => dg_monomial f α _

/- English proof (translation)
Introduce `α hα`. Rewrite `hα` using `[mem_support_iff, coeff_dg]`. Conclude with `mem_support_iff.mpr (right_ne_zero_of_mul hα)`.
-/
theorem support_dg_subset (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) :
    (dg f F).support ⊆ F.support := by
  intro α hα
  rw [mem_support_iff, coeff_dg] at hα
  exact mem_support_iff.mpr (right_ne_zero_of_mul hα)

/- English proof (translation)
Rewrite using `[dg_eq_sum_f]`. Both sides reduce to the same expression.
-/
theorem gaAct_eq_dg (D : TwistData K) (G : MvPolynomial (D.OL × Fin D.r) K) :
    D.gaAct G = dg D.ga G := by
  rw [dg_eq_sum_f]; rfl

end Fock

section BB

variable (v : AddValuation K (WithTop ℚ)) {σ : Type}

/- English proof (translation)
Unfold `vge`. Consider the cases of `vR v x with`. Consider the case `top => simp`. Consider the case `coe y`. Rewrite using `[← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe, sub_le_iff_le_add]`.
-/
theorem vge_sub_iff (a w : ℝ) (x : K) :
    vge v (a - w) x ↔ ((a : ℝ) : WithTop ℝ) ≤ vR v x + ((w : ℝ) : WithTop ℝ) := by
  unfold vge
  cases vR v x with
  | top => simp
  | coe y =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe, sub_le_iff_le_add]

/- English proof (translation)
Unfold `bge vBB`. Rewrite using `[Finset.le_inf_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h α _`. Conclude with `(vge_sub_iff v a _ _).mp (h α)`.

Introduce `h α`. Distinguish the cases in `hα : α ∈ F.support`. Conclude with `(vge_sub_iff v a _ _).mpr (h α hα)`. Rewrite using `[notMem_support_iff.mp hα]`. Conclude with `vge_zero' v _`.
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
Introduce `α` and use `vge_mono' v (by linarith) (h α)`.
-/
theorem bge_mono {a b : ℝ} {F : MvPolynomial σ K} (hab : b ≤ a) (h : bge v a F) : bge v b F :=
  fun α => vge_mono' v (by linarith) (h α)

/- English proof (translation)
Introduce `β` and use `by classical rw [coeff_monomial] split_ifs with h · rw [← h]; exact vge_mono' v (by linarith) hc · exact vge_zero' v _`.
-/
theorem bge_monomial {a : ℝ} (α : σ →₀ ℕ) {c : K} (hc : vge v a c) :
    bge v (a + vN v (fact α) / 2) (monomial α c) := fun β => by
  classical
  rw [coeff_monomial]
  split_ifs with h
  · rw [← h]; exact vge_mono' v (by linarith) hc
  · exact vge_zero' v _

/- English proof (translation)
Introduce `α` and use `by rw [coeff_dg] exact vge_mono' v (by linarith) (vge_mul' v (hf α) (hF α))`.
-/
theorem bge_dg {a b : ℝ} {f : (σ →₀ ℕ) → K} {F : MvPolynomial σ K} (hf : ∀ α, vge v a (f α))
    (hF : bge v b F) : bge v (a + b) (dg f F) := fun α => by
  rw [coeff_dg]
  exact vge_mono' v (by linarith) (vge_mul' v (hf α) (hF α))

/- English proof (translation)
Use `⟨?_, (bge_iff v 0 F).mpr (by rw [h]; rfl)⟩` and prove the remaining obligations. Establish `hne : F.support.Nonempty`. Assume the negation of the conclusion as `hc`. Rewrite `hc` using `[Finset.not_nonempty_iff_eq_empty]`. Unfold `vBB at h`.

Rewrite `h` using `[hc, Finset.inf_empty]`. Conclude with `absurd h (by simp)`. Take `⟨α, hα, hinf⟩` from `Finset.exists_mem_eq_inf F.support hne (fun α => vR v (F.coeff α) + ((((v (fact α : K)).untopD 0 : ℚ) : ℝ) / 2 : ℝ))`. Use `⟨α, hα, ?_⟩` and prove the remaining obligations. Establish `h0 : vR v (F.coeff α) + ((vN v (fact α) / 2 : ℝ) : WithTop ℝ) = 0`.

Rewrite using `[← h]`. Conclude with `hinf.symm`. Unfold `vge vle`. Consider the cases of `hx : vR v (F.coeff α) with`. Consider the case `top => rw [hx] at h0`.

Simplify using `at h0`. Consider the case `coe y`. Rewrite `h0` using `[hx, ← WithTop.coe_add]`. Establish `h1 : y + vN v (fact α) / 2 = 0` using `by exact_mod_cast h0`. Establish `h2 : y = -(vN v (fact α)) / 2` using `by linarith`.

Rewrite using `[h2]`. Conclude with `⟨le_refl _, le_refl _⟩`.
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
Unfold `fock`. Apply `vge_sum'` to reduce the goal to its premises. Introduce `α _`. Establish `h1` using `vge_mul' v (vge_mul' v (hF α) (hG α)) (vge_vN' v (fact α))`. Conclude with `vge_mono' v (by linarith) h1`.
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
