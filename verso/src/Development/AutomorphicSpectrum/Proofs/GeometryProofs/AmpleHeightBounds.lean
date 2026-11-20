import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArchimedeanValueBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightLowerBoundChartNormStatement
import ReciprocityTheory.SemistableReduction.LogNormCoeffSubLeBlockSphereLogMean

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht.AmpleBd

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

section Places

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Take `⟨i₀, hi₀⟩` from `hx`. Use `haveI : Nonempty ι := ⟨i₀⟩`. Establish `hS : (⋃ i ∈ Finset.univ.filter (fun i => x i ≠ 0), Function.mulSupport fun v : FinitePlace L => v (x i)).Finite`. Use `Set.Finite.biUnion (Finset.finite_toSet _) fun i hi => ?_` and prove the remaining obligations. Conclude with `FinitePlace.mulSupport_finite (by simpa using hi)`.

Use `hS.subset fun v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Apply `hv` to reduce the goal to its premises. Establish `h1 : ∀ i, x i ≠ 0 → v (x i) = 1`. Introduce `i hi`.

Assume the negation of the conclusion as `h`. Conclude with `hn (Set.mem_biUnion (by simpa using hi) h)`. Establish `h2 : ∀ i, v (x i) ≤ 1`. Introduce `i`. Distinguish the cases in `hi : x i = 0`.

Simplify using `[hi]`. Conclude with `(h1 i hi).le`. Establish `h3 : (⨆ i, v (x i)) = 1`. Establish `hle : (⨆ i, v (x i)) ≤ 1` using `ciSup_le h2`. Establish `hge : (1 : ℝ) ≤ ⨆ i, v (x i)`.

Establish `hb : BddAbove (Set.range fun i => v (x i))` using `(Set.finite_range _).bddAbove`. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_antisymm hle hge`. Simplify using `[h3]`.
-/
lemma log_sup_support {ι : Type} [Fintype ι] (x : ι → L) (hx : ∃ i, x i ≠ 0) :
    (Function.support fun v : FinitePlace L => Real.log (⨆ i, v (x i))).Finite := by
  classical
  obtain ⟨i₀, hi₀⟩ := hx
  haveI : Nonempty ι := ⟨i₀⟩
  have hS : (⋃ i ∈ Finset.univ.filter (fun i => x i ≠ 0),
      Function.mulSupport fun v : FinitePlace L => v (x i)).Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun i hi => ?_
    exact FinitePlace.mulSupport_finite (by simpa using hi)
  refine hS.subset fun v hv => ?_
  by_contra hn
  apply hv
  have h1 : ∀ i, x i ≠ 0 → v (x i) = 1 := by
    intro i hi
    by_contra h
    exact hn (Set.mem_biUnion (by simpa using hi) h)
  have h2 : ∀ i, v (x i) ≤ 1 := by
    intro i
    by_cases hi : x i = 0
    · simp [hi]
    · exact (h1 i hi).le
  have h3 : (⨆ i, v (x i)) = 1 := by
    have hle : (⨆ i, v (x i)) ≤ 1 := ciSup_le h2
    have hge : (1 : ℝ) ≤ ⨆ i, v (x i) := by
      have hb : BddAbove (Set.range fun i => v (x i)) := (Set.finite_range _).bddAbove
      calc (1 : ℝ) = v (x i₀) := (h1 i₀ hi₀).symm
        _ ≤ _ := le_ciSup hb i₀
    exact le_antisymm hle hge
  simp [h3]

/- English proof (translation)
Use `(FinitePlace.mulSupport_finite hx).subset fun v hv => ?_` and prove the remaining obligations. Introduce `h`. Apply `hv` to reduce the goal to its premises. Simplify using `only [h, Real.log_one]`.
-/
lemma log_support {x : L} (hx : x ≠ 0) : (Function.support fun v : FinitePlace L => Real.log (v x)).Finite := by
  refine (FinitePlace.mulSupport_finite hx).subset fun v hv => ?_
  intro h
  apply hv
  simp only [h, Real.log_one]

/- English proof (translation)
Establish `h` using `prod_abs_eq_one hx`. Rewrite `h` using `[InfinitePlace.prod_eq_abs_norm]`. Rewrite using `[ReciprocityTheory.MultiplicativeHeights.sum_log_norm_embedding_eq x hx]`. Establish `hf : (Function.mulSupport fun v : FinitePlace L => v x).Finite` using `FinitePlace.mulSupport_finite hx`. Establish `hpos : ∀ v : FinitePlace L, v x ≠ 0` using `fun v => by`.

Simplify using `using hx`. Establish `e : (∑ᶠ v : FinitePlace L, Real.log (v x)) = Real.log (∏ᶠ v : FinitePlace L, v x)`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset (s := hf.toFinset) _ (by simp), finsum_eq_sum_of_support_subset (s := hf.toFinset) _ ?_, Real.log_prod fun v _ => hpos v]`. Introduce `v hv`. Simplify using `only [Set.Finite.coe_toFinset, Function.mem_mulSupport]`.

Introduce `h1`. Apply `hv` to reduce the goal to its premises. Simplify using `only [h1, Real.log_one]`. Establish `hP : (∏ᶠ v : FinitePlace L, v x) ≠ 0`. Introduce `h0`.

Rewrite `h` using `[h0, mul_zero]`. Conclude with `zero_ne_one h`. Establish `hN : ((Algebra.norm ℚ x : ℚ) : ℝ) ≠ 0`. Conclude with `(Algebra.norm_ne_zero_iff.2 hx)` after adjusting the coercions. Rewrite using `[e, Real.log_abs]`.

Establish `h2 : |((Algebra.norm ℚ x : ℚ) : ℝ)| * ∏ᶠ v : FinitePlace L, v x = 1`. Rewrite using `[← h]`. Use `push_cast`. Both sides reduce to the same expression. Establish `h3` using `congrArg Real.log h2`.

Rewrite `h3` using `[Real.log_mul (abs_ne_zero.2 hN) hP, Real.log_abs, Real.log_one]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma product_formula {x : L} (hx : x ≠ 0) :
    (∑ᶠ v : FinitePlace L, Real.log (v x)) + ∑ σ : L →+* ℂ, Real.log ‖σ x‖ = 0 := by
  classical
  have h := prod_abs_eq_one hx
  rw [InfinitePlace.prod_eq_abs_norm] at h
  rw [ReciprocityTheory.MultiplicativeHeights.sum_log_norm_embedding_eq x hx]
  have hf : (Function.mulSupport fun v : FinitePlace L => v x).Finite := FinitePlace.mulSupport_finite hx
  have hpos : ∀ v : FinitePlace L, v x ≠ 0 := fun v => by
    simpa using hx
  have e : (∑ᶠ v : FinitePlace L, Real.log (v x)) = Real.log (∏ᶠ v : FinitePlace L, v x) := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := hf.toFinset) _ (by simp),
      finsum_eq_sum_of_support_subset (s := hf.toFinset) _ ?_, Real.log_prod fun v _ => hpos v]
    intro v hv
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hv
    simp only [h1, Real.log_one]
  have hP : (∏ᶠ v : FinitePlace L, v x) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h
    exact zero_ne_one h
  have hN : ((Algebra.norm ℚ x : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast (Algebra.norm_ne_zero_iff.2 hx)
  rw [e, Real.log_abs]
  have h2 : |((Algebra.norm ℚ x : ℚ) : ℝ)| * ∏ᶠ v : FinitePlace L, v x = 1 := by
    rw [← h]
    push_cast
    rfl
  have h3 := congrArg Real.log h2
  rw [Real.log_mul (abs_ne_zero.2 hN) hP, Real.log_abs, Real.log_one] at h3
  linarith

/- English proof (translation)
Rewrite using `[finsum_eq_sum_of_support_subset (s := hf.toFinset ∪ hg.toFinset) f (by simp [Set.subset_def]; tauto), finsum_eq_sum_of_support_subset (s := hf.toFinset ∪ hg.toFinset) g (by simp [Set.subset_def]; tauto)]`. Conclude with `Finset.sum_le_sum fun a _ => h a`.
-/
lemma finsum_le_of_le {α : Type} {f g : α → ℝ} (hf : (Function.support f).Finite) (hg : (Function.support g).Finite)
    (h : ∀ a, f a ≤ g a) : ∑ᶠ a, f a ≤ ∑ᶠ a, g a := by
  classical
  rw [finsum_eq_sum_of_support_subset (s := hf.toFinset ∪ hg.toFinset) f (by simp [Set.subset_def]; tauto),
    finsum_eq_sum_of_support_subset (s := hf.toFinset ∪ hg.toFinset) g (by simp [Set.subset_def]; tauto)]
  exact Finset.sum_le_sum fun a _ => h a

/- English proof (translation)
The claim follows from `|(Module.finrank ℚ L : ℝ)⁻¹ * ∑ σ, S σ| ≤ C := by have hd : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos have hc : ∑ _σ : L →+* ℂ, C = Module.finrank ℚ L * C := by simp [Finset.card_univ, Embeddings.card L ℂ] rw [abs_mul, abs_of_pos (inv_pos.2 hd), inv_mul …`.
-/
lemma avg_abs_le (S : (L →+* ℂ) → ℝ) {C : ℝ} (h : ∀ σ, |S σ| ≤ C) :
    |(Module.finrank ℚ L : ℝ)⁻¹ * ∑ σ, S σ| ≤ C := by
  have hd : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have hc : ∑ _σ : L →+* ℂ, C = Module.finrank ℚ L * C := by
    simp [Finset.card_univ, Embeddings.card L ℂ]
  rw [abs_mul, abs_of_pos (inv_pos.2 hd), inv_mul_le_iff₀ hd, ← hc]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun σ _ => h σ)

end Places

section Blocks

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def bnorm (z : (Σ k, ι k) → ℂ) (k : K) : ℝ :=
  Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2)

/- English proof (translation)
Use `Real.le_sqrt_of_sq_le ?_` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)`.
-/
lemma norm_le_bnorm (z : (Σ k, ι k) → ℂ) (k : K) (i : ι k) : ‖z ⟨k, i⟩‖ ≤ bnorm z k := by
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)

/- English proof (translation)
Take `⟨i, hi⟩` from `h`. Conclude with `(norm_pos_iff.2 hi).trans_le (norm_le_bnorm z k i)`.
-/
lemma bnorm_pos {z : (Σ k, ι k) → ℂ} {k : K} (h : ∃ i, z ⟨k, i⟩ ≠ 0) : 0 < bnorm z k := by
  obtain ⟨i, hi⟩ := h
  exact (norm_pos_iff.2 hi).trans_le (norm_le_bnorm z k i)

/- English proof (translation)
Unfold `bnorm`. Simplify using `only [norm_mul, mul_pow, ← Finset.mul_sum]`. Rewrite using `[Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]`.
-/
lemma bnorm_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (k : K) :
    bnorm (fun p => c p.1 * z p) k = ‖c k‖ * bnorm z k := by
  unfold bnorm
  simp only [norm_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

/- English proof (translation)
The claim follows from `Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => ((continuous_apply (⟨k, i⟩ : Σ k, ι k)).norm).pow 2)`.
-/
lemma continuous_bnorm (k : K) : Continuous fun z : (Σ k, ι k) → ℂ => bnorm z k :=
  Real.continuous_sqrt.comp
    (continuous_finset_sum _ fun i _ => ((continuous_apply (⟨k, i⟩ : Σ k, ι k)).norm).pow 2)

/- English proof (translation)
Establish `h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun z : (Σ k, ι k) → ℂ => ∑ i, ‖z ⟨k, i⟩‖ ^ 2` using `ContDiff.sum fun i _ => (contDiff_apply ℝ ℂ (⟨k, i⟩ : Σ k, ι k)).norm_sq ℝ`. Use `h1.contDiffOn.sqrt fun z hz => ?_` and prove the remaining obligations. Use `bnorm_pos (hz k)` as an intermediate fact. Unfold `bnorm at this`. Conclude with `fun h0 => by simp [h0] at this`.
-/
lemma contDiffOn_bnorm (k : K) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => bnorm z k) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun z : (Σ k, ι k) → ℂ => ∑ i, ‖z ⟨k, i⟩‖ ^ 2 :=
    ContDiff.sum fun i _ => (contDiff_apply ℝ ℂ (⟨k, i⟩ : Σ k, ι k)).norm_sq ℝ
  refine h1.contDiffOn.sqrt fun z hz => ?_
  have := bnorm_pos (hz k)
  unfold bnorm at this
  exact fun h0 => by simp [h0] at this

/- English proof (translation)
The claim follows from `|Real.log (B.h z) - ∑ k, (B.a k : ℝ) * Real.log (bnorm z k)| ≤ C := by set S : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, bnorm z k = 1} with hS have hcl : IsClosed S := by simp only [hS, Set.setOf_forall] exact isClosed_iInter fun k => isClosed_eq (continuous_bnorm k) continuous_const ha …`.
-/
lemma exists_bound (B : HermLine ι) (hB : IsSmoothHerm B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      |Real.log (B.h z) - ∑ k, (B.a k : ℝ) * Real.log (bnorm z k)| ≤ C := by
  set S : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, bnorm z k = 1} with hS
  have hcl : IsClosed S := by
    simp only [hS, Set.setOf_forall]
    exact isClosed_iInter fun k => isClosed_eq (continuous_bnorm k) continuous_const
  have hsub : S ⊆ Metric.closedBall 0 1 := by
    intro z hz
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    rintro ⟨k, i⟩
    exact (norm_le_bnorm z k i).trans (hz k).le
  have hcpt : IsCompact S := (isCompact_closedBall 0 1).of_isClosed_subset hcl hsub
  have hmc : ∀ z ∈ S, ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
    intro z hz k
    by_contra hn
    push_neg at hn
    have := hz k
    simp [bnorm, hn] at this
  have hcont : ContinuousOn (fun z => Real.log (B.h z)) S :=
    (ContDiffOn.continuousOn hB |>.mono fun z hz => hmc z hz).log fun z hz => (B.pos z (hmc z hz)).ne'
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun z hz => ?_⟩
  have hb : ∀ k, 0 < bnorm z k := fun k => bnorm_pos (hz k)
  set c : K → ℂ := fun k => (((bnorm z k)⁻¹ : ℝ) : ℂ) with hc
  have hcn : ∀ k, ‖c k‖ = (bnorm z k)⁻¹ := fun k => by
    simp only [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hb k))]
  have hc0 : ∀ k, c k ≠ 0 := fun k => by
    rw [← norm_pos_iff, hcn]
    exact inv_pos.2 (hb k)
  have hz' : (fun p => c p.1 * z p) ∈ S := fun k => by
    rw [bnorm_smul, hcn, inv_mul_cancel₀ (hb k).ne']
  have h1 := hC _ hz'
  rw [B.smul c z hc0, Real.norm_eq_abs] at h1
  have hprod : (∏ k, ‖c k‖ ^ B.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc0 k))
  have hzpos := B.pos z hz
  rw [Real.log_mul hprod hzpos.ne',
    Real.log_prod fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc0 k))] at h1
  have h2 : ∑ k, Real.log (‖c k‖ ^ B.a k) = -∑ k, (B.a k : ℝ) * Real.log (bnorm z k) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Real.log_zpow, hcn, Real.log_inv]
    ring
  rw [h2] at h1
  rw [show Real.log (B.h z) - ∑ k, (B.a k : ℝ) * Real.log (bnorm z k) =
    -∑ k, (B.a k : ℝ) * Real.log (bnorm z k) + Real.log (B.h z) by ring]
  exact h1.trans (le_max_left _ _)

def twistLine (A : HermLine ι) (m : ℕ) : HermLine ι where
  a := fun k => (m : ℤ) * A.a k - 1
  h z := A.h z ^ m / ∏ k, bnorm z k
  pos z hz := div_pos (pow_pos (A.pos z hz) m) (Finset.prod_pos fun k _ => bnorm_pos (hz k))
  smul c z hc := by
    have hn : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.2 (hc k)
    have h1 : ∀ k, ‖c k‖ ^ ((m : ℤ) * A.a k - 1) = (‖c k‖ ^ A.a k) ^ m / ‖c k‖ := fun k => by
      rw [zpow_sub₀ (hn k), zpow_one, mul_comm (m : ℤ), zpow_mul, zpow_natCast]
    simp only [h1, A.smul c z hc, bnorm_smul, Finset.prod_mul_distrib, Finset.prod_div_distrib, mul_pow,
      Finset.prod_pow]
    rw [mul_div_mul_comm]

/- English proof (translation)
Use `ContDiffOn.div (ContDiffOn.pow hA m) (contDiffOn_prod fun k _ => contDiffOn_bnorm k) fun z hz => ?_` and prove the remaining obligations. Conclude with `(Finset.prod_pos fun k _ => bnorm_pos (hz k)).ne'`.
-/
lemma twistLine_smooth {A : HermLine ι} (hA : IsSmoothHerm A) (m : ℕ) : IsSmoothHerm (twistLine A m) := by
  refine ContDiffOn.div (ContDiffOn.pow hA m) (contDiffOn_prod fun k _ => contDiffOn_bnorm k) fun z hz => ?_
  exact (Finset.prod_pos fun k _ => bnorm_pos (hz k)).ne'

end Blocks

section Heights

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def blockHt (L : Type) [Field L] [NumberField L] (w : (Σ k, ι k) → L) (k : K) : ℝ :=
  (Module.finrank ℚ L : ℝ)⁻¹ *
    ((∑ᶠ v : FinitePlace L, Real.log (⨆ i, v (w ⟨k, i⟩))) + ∑ σ : L →+* ℂ, Real.log (bnorm (fun p => σ (w p)) k))

def sumHt (L : Type) [Field L] [NumberField L] (w : (Σ k, ι k) → L) : ℝ :=
  ∑ k, blockHt L w k

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Take `⟨i₀, hi₀⟩` from `h`. Use `mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) ?_` and prove the remaining obligations. Rewrite using `[← product_formula hi₀]`. Use `add_le_add ?_ (Finset.sum_le_sum fun σ _ => ?_)` and prove the remaining obligations. Use `finsum_le_of_le (log_support hi₀) (log_sup_support (fun i => w ⟨k, i⟩) ⟨i₀, hi₀⟩) fun v => ?_` and prove the remaining obligations.

Establish `hp : 0 < v (w ⟨k, i₀⟩)`. Establish `: v (w ⟨k, i₀⟩) ≠ 0` using `by simpa using hi₀`. Conclude with `lt_of_le_of_ne (apply_nonneg v _) this.symm`. Conclude with `Real.log_le_log hp (le_ciSup (f := fun i => v (w ⟨k, i⟩)) (Set.finite_range _).bddAbove i₀)`. Conclude with `Real.log_le_log (norm_pos_iff.2 ((map_ne_zero σ).2 hi₀)) (norm_le_bnorm (fun p => σ (w p)) k i₀)`.
-/
lemma blockHt_nonneg (w : (Σ k, ι k) → L) (k : K) (h : ∃ i, w ⟨k, i⟩ ≠ 0) : 0 ≤ blockHt L w k := by
  obtain ⟨i₀, hi₀⟩ := h
  refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) ?_
  rw [← product_formula hi₀]
  refine add_le_add ?_ (Finset.sum_le_sum fun σ _ => ?_)
  · refine finsum_le_of_le (log_support hi₀) (log_sup_support (fun i => w ⟨k, i⟩) ⟨i₀, hi₀⟩) fun v => ?_
    have hp : 0 < v (w ⟨k, i₀⟩) := by
      have : v (w ⟨k, i₀⟩) ≠ 0 := by simpa using hi₀
      exact lt_of_le_of_ne (apply_nonneg v _) this.symm
    exact Real.log_le_log hp (le_ciSup (f := fun i => v (w ⟨k, i⟩)) (Set.finite_range _).bddAbove i₀)
  · exact Real.log_le_log (norm_pos_iff.2 ((map_ne_zero σ).2 hi₀))
      (norm_le_bnorm (fun p => σ (w p)) k i₀)

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun k _ => blockHt_nonneg w k (h k)`.
-/
lemma sumHt_nonneg (w : (Σ k, ι k) → L) (h : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) : 0 ≤ sumHt L w :=
  Finset.sum_nonneg fun k _ => blockHt_nonneg w k (h k)

/- English proof (translation)
Establish `e : (∑ᶠ v : FinitePlace L, ∑ k, a k * Real.log (⨆ i, v (w ⟨k, i⟩))) = ∑ k, a k * ∑ᶠ v : FinitePlace L, Real.log (⨆ i, v (w ⟨k, i⟩))`. Rewrite using `[finsum_sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_finsum]`. Introduce `k _`.

Conclude with `(log_sup_support (fun i => w ⟨k, i⟩) (hw k)).subset fun v hv => right_ne_zero_of_mul hv`. Establish `e2 : ∑ σ : L →+* ℂ, ∑ k, a k * Real.log (bnorm (fun p => σ (w p)) k) = ∑ k, a k * ∑ σ : L →+* ℂ, Real.log (bnorm (fun p => σ (w p)) k)`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm`. Establish `e3 : ∑ k, a k * blockHt L w k = (Module.finrank ℚ L : ℝ)⁻¹ * (∑ k, a k * ∑ᶠ v : FinitePlace L, Real.log (⨆ i, v (w ⟨k, i⟩)) + ∑ k, a k * ∑ σ : L →+* ℂ, Real.log (bnorm (fun p => σ (w p)) k))`.

Rewrite using `[← Finset.sum_add_distrib, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Unfold `blockHt`. Expand and normalize the polynomial expressions, which then agree. Unfold `ptHt`.

Rewrite using `[e, Finset.sum_sub_distrib, e2, e3]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma ptHt_eq (a : K → ℝ) (φ : ((Σ k, ι k) → ℂ) → ℝ) (w : (Σ k, ι k) → L) (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    ptHt a φ L w = ∑ k, a k * blockHt L w k + (Module.finrank ℚ L : ℝ)⁻¹ *
      ∑ σ : L →+* ℂ, (φ (fun p => σ (w p)) - ∑ k, a k * Real.log (bnorm (fun p => σ (w p)) k)) := by
  have e : (∑ᶠ v : FinitePlace L, ∑ k, a k * Real.log (⨆ i, v (w ⟨k, i⟩))) =
      ∑ k, a k * ∑ᶠ v : FinitePlace L, Real.log (⨆ i, v (w ⟨k, i⟩)) := by
    rw [finsum_sum_comm]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_finsum]
    · intro k _
      exact (log_sup_support (fun i => w ⟨k, i⟩) (hw k)).subset fun v hv => right_ne_zero_of_mul hv
  have e2 : ∑ σ : L →+* ℂ, ∑ k, a k * Real.log (bnorm (fun p => σ (w p)) k) =
      ∑ k, a k * ∑ σ : L →+* ℂ, Real.log (bnorm (fun p => σ (w p)) k) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
  have e3 : ∑ k, a k * blockHt L w k = (Module.finrank ℚ L : ℝ)⁻¹ *
      (∑ k, a k * ∑ᶠ v : FinitePlace L, Real.log (⨆ i, v (w ⟨k, i⟩)) +
        ∑ k, a k * ∑ σ : L →+* ℂ, Real.log (bnorm (fun p => σ (w p)) k)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold blockHt
    ring
  unfold ptHt
  rw [e, Finset.sum_sub_distrib, e2, e3]
  ring

/- English proof (translation)
Unfold `lineHt`. Rewrite using `[ptHt_eq _ _ w hw, ptHt_eq _ _ w hw]`. Establish `h1 : ∀ σ : L →+* ℂ, Real.log ((twistLine A m).h fun p => σ (w p)) - ∑ k, (((twistLine A m).a k : ℤ) : ℝ) * Real.log (bnorm (fun p => σ (w p)) k) = m * (Real.log (A.h fun p => σ (w p)) - ∑ k, (A.a k : ℝ) * Real.log (bnorm (fun p => σ (w p)) k))`. Introduce `σ`. Establish `hz : ∀ k, ∃ i, (fun p => σ (w p)) ⟨k, i⟩ ≠ 0` using `fun k => by`.

Take `⟨i, hi⟩` from `hw k`. Conclude with `⟨i, (map_ne_zero σ).2 hi⟩`. Establish `hb : ∀ k, bnorm (fun p => σ (w p)) k ≠ 0` using `fun k => (bnorm_pos (hz k)).ne'`. Establish `e : (twistLine A m).h (fun p => σ (w p)) = (A.h fun p => σ (w p)) ^ m / ∏ k, bnorm (fun p => σ (w p)) k` using `rfl`. Rewrite using `[e, Real.log_div (pow_ne_zero _ (A.pos _ hz).ne') (Finset.prod_ne_zero_iff.2 fun k _ => hb k), Real.log_pow, Real.log_prod fun k _ => hb k]`.

Simplify using `only [twistLine]`. Use `push_cast`. Simplify using `only [sub_mul, one_mul, Finset.sum_sub_distrib, mul_sub, Finset.mul_sum, mul_assoc]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h1, ← Finset.mul_sum]`.

Establish `h2 : ∑ k, (((twistLine A m).a k : ℤ) : ℝ) * blockHt L w k = m * ∑ k, (A.a k : ℝ) * blockHt L w k - sumHt L w`. Simplify using `only [twistLine, sumHt]`. Use `push_cast`. Simplify using `only [sub_mul, one_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]`. Rewrite using `[h2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma lineHt_twist (A : HermLine ι) (m : ℕ) (w : (Σ k, ι k) → L) (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    lineHt (twistLine A m) L w = m * lineHt A L w - sumHt L w := by
  unfold lineHt
  rw [ptHt_eq _ _ w hw, ptHt_eq _ _ w hw]
  have h1 : ∀ σ : L →+* ℂ, Real.log ((twistLine A m).h fun p => σ (w p)) -
      ∑ k, (((twistLine A m).a k : ℤ) : ℝ) * Real.log (bnorm (fun p => σ (w p)) k) =
      m * (Real.log (A.h fun p => σ (w p)) - ∑ k, (A.a k : ℝ) * Real.log (bnorm (fun p => σ (w p)) k)) := by
    intro σ
    have hz : ∀ k, ∃ i, (fun p => σ (w p)) ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨i, hi⟩ := hw k
      exact ⟨i, (map_ne_zero σ).2 hi⟩
    have hb : ∀ k, bnorm (fun p => σ (w p)) k ≠ 0 := fun k => (bnorm_pos (hz k)).ne'
    have e : (twistLine A m).h (fun p => σ (w p)) =
        (A.h fun p => σ (w p)) ^ m / ∏ k, bnorm (fun p => σ (w p)) k := rfl
    rw [e, Real.log_div (pow_ne_zero _ (A.pos _ hz).ne') (Finset.prod_ne_zero_iff.2 fun k _ => hb k),
      Real.log_pow, Real.log_prod fun k _ => hb k]
    simp only [twistLine]
    push_cast
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib, mul_sub, Finset.mul_sum, mul_assoc]
    ring
  simp only [h1, ← Finset.mul_sum]
  have h2 : ∑ k, (((twistLine A m).a k : ℤ) : ℝ) * blockHt L w k =
      m * ∑ k, (A.a k : ℝ) * blockHt L w k - sumHt L w := by
    simp only [twistLine, sumHt]
    push_cast
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  rw [h2]
  ring

/- English proof (translation)
Take `⟨C, hC0, hC⟩` from `exists_bound B hB`. Use `⟨∑ k, |(B.a k : ℝ)|, C, Finset.sum_nonneg fun _ _ => abs_nonneg _, hC0, fun L _ _ w hw => ?_⟩` and prove the remaining obligations. Establish `hh : ∀ k, 0 ≤ blockHt L w k` using `fun k => blockHt_nonneg w k (hw k)`. Unfold `lineHt`. Rewrite using `[ptHt_eq _ _ w hw]`.

Use `(abs_add_le _ _).trans (add_le_add ?_ (avg_abs_le _ fun σ => hC _ fun k => ?_))` and prove the remaining obligations. Use `(Finset.abs_sum_le_sum_abs _ _).trans ?_` and prove the remaining obligations. Unfold `sumHt`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[abs_mul, abs_of_nonneg (hh k)]`. Conclude with `mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun k => |(B.a k : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)) (hh k)`. Take `⟨i, hi⟩` from `hw k`. Conclude with `⟨i, (map_ne_zero σ).2 hi⟩`.
-/
lemma abs_lineHt_le (B : HermLine ι) (hB : IsSmoothHerm B) :
    ∃ n C : ℝ, 0 ≤ n ∧ 0 ≤ C ∧ ∀ (L : Type) [Field L] [NumberField L] (w : (Σ k, ι k) → L),
      (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → |lineHt B L w| ≤ n * sumHt L w + C := by
  obtain ⟨C, hC0, hC⟩ := exists_bound B hB
  refine ⟨∑ k, |(B.a k : ℝ)|, C, Finset.sum_nonneg fun _ _ => abs_nonneg _, hC0, fun L _ _ w hw => ?_⟩
  have hh : ∀ k, 0 ≤ blockHt L w k := fun k => blockHt_nonneg w k (hw k)
  unfold lineHt
  rw [ptHt_eq _ _ w hw]
  refine (abs_add_le _ _).trans (add_le_add ?_ (avg_abs_le _ fun σ => hC _ fun k => ?_))
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    unfold sumHt
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [abs_mul, abs_of_nonneg (hh k)]
    exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := fun k => |(B.a k : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)) (hh k)
  · obtain ⟨i, hi⟩ := hw k
    exact ⟨i, (map_ne_zero σ).2 hi⟩

end Heights

section Sections

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
The claim follows from `(comp_aeval_apply (R := ℤ) (f := z) σ.toIntAlgHom f).symm`.
-/
lemma aeval_emb {L : Type} [Field L] (σ : L →+* ℂ) (z : (Σ k, ι k) → L) (f : MRing ι) :
    aeval (fun p => σ (z p)) f = σ (aeval z f) :=
  (comp_aeval_apply (R := ℤ) (f := z) σ.toIntAlgHom f).symm

/- English proof (translation)
Use `⟨fun k => ?_, fun f hf => ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `hz.1 k`. Conclude with `⟨i, (map_ne_zero σ).2 hi⟩`. Rewrite using `[aeval_emb, hz.2 f hf, map_zero]`.
-/
lemma ptsOver_emb {L : Type} [Field L] (σ : L →+* ℂ) {P : Ideal (MRing ι)} {z : (Σ k, ι k) → L}
    (hz : z ∈ ptsOver L P) : (fun p => σ (z p)) ∈ ptsOver ℂ P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, (map_ne_zero σ).2 hi⟩
  · rw [aeval_emb, hz.2 f hf, map_zero]

/- English proof (translation)
Take `⟨dg, dh, g, f, hg, hf, hd, hy, h0, h1⟩` from `h`. Use `⟨dg, dh, g, f, hg, hf, hd, hy, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[aeval_emb]`. Conclude with `(map_ne_zero σ).2 h0`. Rewrite using `[aeval_emb, aeval_emb, h1, map_mul]`.
-/
lemma hasVal_emb {L : Type} [Field L] (σ : L →+* ℂ) {y : (Σ k, ι k) → Ω} {a : K → ℤ} {u : Ω}
    {z : (Σ k, ι k) → L} {w : L} (h : HasVal y a u z w) : HasVal y a u (fun p => σ (z p)) (σ w) := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, hy, h0, h1⟩ := h
  refine ⟨dg, dh, g, f, hg, hf, hd, hy, ?_, ?_⟩
  · rw [aeval_emb]
    exact (map_ne_zero σ).2 h0
  · rw [aeval_emb, aeval_emb, h1, map_mul]

/- English proof (translation)
Establish `hu' : ((1 : ℕ) : Ω) * u ^ 1 ∈ chartLatNm y M.a 1` using `by simpa using hu`. Take `⟨C, hC⟩` from `GlobalTheory.T.archimedean_value_bound K ι Ω y d hv hb M 1 1 u hM one_pos one_pos hu'`. Use `⟨C, fun L _ _ w hw val hval hw' => ?_⟩` and prove the remaining obligations. Establish `h1` using `GlobalTheory.T.height_lower_bound_chart_norm K ι Ω y d hv hb M.a u 1 1 one_pos one_pos hu' (fun z => Real.log (M.h z)) L w hw val hval hw'`. Simplify using `only [Nat.cast_one, Real.log_one, div_one, sub_zero] at h1`.

Use `le_trans ?_ h1` and prove the remaining obligations. Establish `hd : (0 : ℝ) < Module.finrank ℚ L` using `by exact_mod_cast Module.finrank_pos`. Establish `hc : ∑ _σ : L →+* ℂ, (-C) = Module.finrank ℚ L * (-C)`. Simplify using `[Finset.card_univ, Embeddings.card L ℂ]`. Rewrite using `[le_inv_mul_iff₀ hd, ← hc]`.

Use `Finset.sum_le_sum fun σ _ => ?_` and prove the remaining obligations. Establish `hz` using `ptsOver_emb σ hw`. Establish `h2` using `hC _ hz (σ val) (hasVal_emb σ hw')`. Establish `hvp : 0 < ‖σ val‖` using `norm_pos_iff.2 ((map_ne_zero σ).2 hval)`. Establish `hpos` using `M.pos (fun p => σ (w p)) hz.1`.

Establish `h3` using `Real.log_le_log hvp h2`. Rewrite `h3` using `[Real.log_mul (Real.exp_pos C).ne' hpos.ne', Real.log_exp]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma lineHt_lower {y : (Σ k, ι k) → Ω} {d : ℕ} (hv : IsArithVar (mCoordIdeal y) d) (hb : Birational y)
    (M : HermLine ι) (hM : IsSmoothHerm M) (u : Ω) (hu : u ∈ chartLatNm y M.a 1) :
    ∃ C : ℝ, ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), ∀ val : L, val ≠ 0 →
      HasVal y M.a u w val → -C ≤ lineHt M L w := by
  have hu' : ((1 : ℕ) : Ω) * u ^ 1 ∈ chartLatNm y M.a 1 := by simpa using hu
  obtain ⟨C, hC⟩ := GlobalTheory.T.archimedean_value_bound K ι Ω y d hv hb M 1 1 u hM one_pos one_pos hu'
  refine ⟨C, fun L _ _ w hw val hval hw' => ?_⟩
  have h1 := GlobalTheory.T.height_lower_bound_chart_norm K ι Ω y d hv hb M.a u 1 1 one_pos one_pos hu' (fun z => Real.log (M.h z)) L w hw val hval hw'
  simp only [Nat.cast_one, Real.log_one, div_one, sub_zero] at h1
  refine le_trans ?_ h1
  have hd : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have hc : ∑ _σ : L →+* ℂ, (-C) = Module.finrank ℚ L * (-C) := by
    simp [Finset.card_univ, Embeddings.card L ℂ]
  rw [le_inv_mul_iff₀ hd, ← hc]
  refine Finset.sum_le_sum fun σ _ => ?_
  have hz := ptsOver_emb σ hw
  have h2 := hC _ hz (σ val) (hasVal_emb σ hw')
  have hvp : 0 < ‖σ val‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hval)
  have hpos := M.pos (fun p => σ (w p)) hz.1
  have h3 := Real.log_le_log hvp h2
  rw [Real.log_mul (Real.exp_pos C).ne' hpos.ne', Real.log_exp] at h3
  linarith

/- English proof (translation)
Take `⟨m, l, s, hs, hcov⟩` from `ha`. Establish `hM` using `twistLine_smooth hA m`. Use `choose C hC using fun i => lineHt_lower hv hb (twistLine A m) hM (s i) (hs i)`. Use `⟨m, ∑ i, |C i|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun L _ _ w hw => ?_⟩` and prove the remaining obligations. Take `⟨i, val, hval, hw'⟩` from `hcov L w hw`.

Establish `h1` using `hC i L w hw val hval hw'`. Rewrite `h1` using `[lineHt_twist A m w hw.1]`. Establish `h2 : C i ≤ ∑ i, |C i|` using `(le_abs_self _).trans (Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i))`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma sumHt_le {y : (Σ k, ι k) → Ω} {d : ℕ} (hv : IsArithVar (mCoordIdeal y) d) (hb : Birational y)
    (A : HermLine ι) (hA : IsSmoothHerm A) (ha : AmpleQ y A.a) :
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y),
      sumHt L w ≤ m * lineHt A L w + C := by
  obtain ⟨m, l, s, hs, hcov⟩ := ha
  have hM := twistLine_smooth hA m
  choose C hC using fun i => lineHt_lower hv hb (twistLine A m) hM (s i) (hs i)
  refine ⟨m, ∑ i, |C i|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun L _ _ w hw => ?_⟩
  obtain ⟨i, val, hval, hw'⟩ := hcov L w hw
  have h1 := hC i L w hw val hval hw'
  rw [lineHt_twist A m w hw.1] at h1
  have h2 : C i ≤ ∑ i, |C i| := (le_abs_self _).trans
    (Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  linarith

end Sections

/- English proof (translation)
Introduce `K _ ι _ Ω _ y d hv hb A hA ha`. Take `⟨m, C, hC0, hC⟩` from `sumHt_le hv hb A hA ha`. Take `⟨nA, CA, hnA, hCA, hAle⟩` from `abs_lineHt_le A hA`. Break down `Nat.eq_zero_or_pos m with hm | hm` into its components or cases. Substitute `hm` using the available equality.

Establish `hsum : ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), sumHt L w ≤ C`. Introduce `L _ _ w hw`. Simplify using `using hC L w hw`. Use `⟨⟨nA * C + CA, fun L _ _ w hw => ?_⟩, fun B hB => ?_⟩` and prove the remaining obligations. Establish `h1` using `hAle L w hw.1`.

Establish `h2` using `mul_le_mul_of_nonneg_left (hsum L w hw) hnA`. Combine the linear relations using `[neg_abs_le (lineHt A L w)]`. Take `⟨n, CB, hn, hCB, hBle⟩` from `abs_lineHt_le B hB`. Use `⟨0, n * C + CB, le_rfl, fun L _ _ w hw => ?_⟩` and prove the remaining obligations. Establish `h1` using `hBle L w hw.1`.

Establish `h2` using `mul_le_mul_of_nonneg_left (hsum L w hw) hn`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmr : (0 : ℝ) < m` using `by exact_mod_cast hm`. Use `⟨⟨C / m, fun L _ _ w hw => ?_⟩, fun B hB => ?_⟩` and prove the remaining obligations. Establish `h1` using `hC L w hw`.

Establish `h2` using `sumHt_nonneg w hw.1`. Rewrite using `[neg_le_iff_add_nonneg, ← mul_le_mul_iff_right₀ hmr]`. Establish `h3 : (m : ℝ) * (lineHt A L w + C / m) = m * lineHt A L w + C`. Clear the denominators using the available nonvanishing facts. Rewrite using `[mul_zero, h3]`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨n, CB, hn, hCB, hBle⟩` from `abs_lineHt_le B hB`. Use `⟨n * m, n * C + CB, mul_nonneg hn hmr.le, fun L _ _ w hw => ?_⟩` and prove the remaining obligations. Establish `h1` using `hBle L w hw.1`. Establish `h2` using `mul_le_mul_of_nonneg_left (hC L w hw) hn`.

Use polynomial arithmetic with `[h1, h2]`.
-/
theorem height_bound : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), IsArithVar (mCoordIdeal y) d → Birational y → ∀ A : HermLine ι, IsSmoothHerm A → AmpleQ y A.a → (∃ C : ℝ, ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), -C ≤ lineHt A L w) ∧ ∀ B : HermLine ι, IsSmoothHerm B → ∃ n C : ℝ, 0 ≤ n ∧ ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), |lineHt B L w| ≤ n * lineHt A L w + C := by
  intro K _ ι _ Ω _ y d hv hb A hA ha
  obtain ⟨m, C, hC0, hC⟩ := sumHt_le hv hb A hA ha
  obtain ⟨nA, CA, hnA, hCA, hAle⟩ := abs_lineHt_le A hA
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hsum : ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), sumHt L w ≤ C := by
      intro L _ _ w hw
      simpa using hC L w hw
    refine ⟨⟨nA * C + CA, fun L _ _ w hw => ?_⟩, fun B hB => ?_⟩
    · have h1 := hAle L w hw.1
      have h2 := mul_le_mul_of_nonneg_left (hsum L w hw) hnA
      linarith [neg_abs_le (lineHt A L w)]
    · obtain ⟨n, CB, hn, hCB, hBle⟩ := abs_lineHt_le B hB
      refine ⟨0, n * C + CB, le_rfl, fun L _ _ w hw => ?_⟩
      have h1 := hBle L w hw.1
      have h2 := mul_le_mul_of_nonneg_left (hsum L w hw) hn
      linarith
  · have hmr : (0 : ℝ) < m := by exact_mod_cast hm
    refine ⟨⟨C / m, fun L _ _ w hw => ?_⟩, fun B hB => ?_⟩
    · have h1 := hC L w hw
      have h2 := sumHt_nonneg w hw.1
      rw [neg_le_iff_add_nonneg, ← mul_le_mul_iff_right₀ hmr]
      have h3 : (m : ℝ) * (lineHt A L w + C / m) = m * lineHt A L w + C := by
        field_simp
      rw [mul_zero, h3]
      linarith
    · obtain ⟨n, CB, hn, hCB, hBle⟩ := abs_lineHt_le B hB
      refine ⟨n * m, n * C + CB, mul_nonneg hn hmr.le, fun L _ _ w hw => ?_⟩
      have h1 := hBle L w hw.1
      have h2 := mul_le_mul_of_nonneg_left (hC L w hw) hn
      nlinarith [h1, h2]

end GlobalTheory.CompanionTheory.Ar.Ht.AmpleBd
