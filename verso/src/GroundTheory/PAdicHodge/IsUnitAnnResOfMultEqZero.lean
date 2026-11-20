import Mathlib
import GroundTheory.PAdicHodge.WAFracAnnCris
import GroundTheory.PAdicHodge.WAFracAnnPt
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
  {ρ0 : Set.Ioo (0 : ℝ) 1} {σ0 : Set.Ioc (0 : ℝ) ρ0}

/- English proof (translation)
Establish `hK : IsCompact (Set.Icc (σ0 : ℝ) ρ0)` using `isCompact_Icc`. Establish `hne : (Set.Icc (σ0 : ℝ) ρ0).Nonempty` using `⟨σ0, le_rfl, σ0.2.2⟩`. Take `⟨x, hx, hmin⟩` from `hK.exists_isMinOn hne (T.continuousOn_annNormR v)`. Use `⟨T.annNormR v x, ?_, fun r => ?_⟩` and prove the remaining obligations. Rewrite using `[T.annNormR_of_mem v ⟨x, hx⟩]`.

Conclude with `hv _`. Rewrite using `[← T.annNormR_of_mem v r]`. Conclude with `hmin r.2`.
-/
theorem exists_pos_le_annNorm (v : T.Ann ρ0 σ0) (hv : ∀ r, 0 < T.annNorm ρ0 σ0 r v) :
    ∃ μ > 0, ∀ r, μ ≤ T.annNorm ρ0 σ0 r v := by
  have hK : IsCompact (Set.Icc (σ0 : ℝ) ρ0) := isCompact_Icc
  have hne : (Set.Icc (σ0 : ℝ) ρ0).Nonempty := ⟨σ0, le_rfl, σ0.2.2⟩
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne (T.continuousOn_annNormR v)
  refine ⟨T.annNormR v x, ?_, fun r => ?_⟩
  · rw [T.annNormR_of_mem v ⟨x, hx⟩]; exact hv _
  · rw [← T.annNormR_of_mem v r]; exact hmin r.2

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.sum_empty, annNorm_zero]`. Conclude with `hM`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi]`.

Conclude with `(T.annNorm_add_le r _ _).trans (max_le (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj)))`.
-/
theorem annNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → T.Ann ρ0 σ0) (r : AnnRad ρ0 σ0) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ i ∈ s, T.annNorm ρ0 σ0 r (f i) ≤ M) :
    T.annNorm ρ0 σ0 r (∑ i ∈ s, f i) ≤ M := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, annNorm_zero]; exact hM
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (T.annNorm_add_le r _ _).trans (max_le (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj)))

/- English proof (translation)
Use `set lam := max (T.annNorm ρ0 σ0 (annIn ρ0 σ0) e) (T.annNorm ρ0 σ0 (annOut ρ0 σ0) e) with hlam`. Establish `hl1 : lam < 1` using `max_lt h1 h2`. Establish `hl0 : 0 ≤ lam` using `le_max_of_le_left (T.annNorm_nonneg _ _)`. Establish `hpow : ∀ (r : AnnRad ρ0 σ0), (r = annIn ρ0 σ0 ∨ r = annOut ρ0 σ0) → ∀ n : ℕ, T.annNorm ρ0 σ0 r ((-e) ^ n) ≤ lam ^ n`. Introduce `r hr n`.

Rewrite using `[annNorm_pow, annNorm_neg]`. Use `pow_le_pow_left₀ (T.annNorm_nonneg _ _) ?_ n` and prove the remaining obligations. Break down `hr with rfl | rfl` into its components or cases. Conclude with `le_max_left _ _`. Conclude with `le_max_right _ _`.

Use `set S : ℕ → T.Ann ρ0 σ0 := fun n => ∑ k ∈ Finset.range n, (-e) ^ k`. Establish `hS : ∀ (r : AnnRad ρ0 σ0), (r = annIn ρ0 σ0 ∨ r = annOut ρ0 σ0) → ∀ m n, m ≤ n → T.annNorm ρ0 σ0 r (S n - S m) ≤ lam ^ m`. Introduce `r hr m n hmn`. Establish `e1 : S n - S m = ∑ k ∈ Finset.Ico m n, (-e) ^ k`. Simplify using `only [S]`.

Rewrite using `[Finset.sum_Ico_eq_sub _ hmn]`. Rewrite using `[e1]`. Use `T.annNorm_sum_le _ _ r (pow_nonneg hl0 m) fun k hk => ?_` and prove the remaining obligations. Conclude with `(hpow r hr k).trans (pow_le_pow_of_le_one hl0 hl1.le (Finset.mem_Ico.1 hk).1)`. Take `⟨g, hg⟩` from `T.exists_limit_ann (z := S) fun ε hε => by`.

Take `⟨J₀, hJ₀⟩` from `exists_pow_lt_of_lt_one hε hl1`. Use `⟨J₀, fun J hJ K hK => ?_⟩` and prove the remaining obligations. Establish `key : ∀ r : AnnRad ρ0 σ0, (r = annIn ρ0 σ0 ∨ r = annOut ρ0 σ0) → T.annNorm ρ0 σ0 r (S J - S K) ≤ ε`. Introduce `r hr`. Break down `le_total K J with h | h` into its components or cases.

Conclude with `(hS r hr K J h).trans ((pow_le_pow_of_le_one hl0 hl1.le hK).trans hJ₀.le)`. Rewrite using `[annNorm_sub_comm]`. Conclude with `(hS r hr J K h).trans ((pow_le_pow_of_le_one hl0 hl1.le hJ).trans hJ₀.le)`. Conclude with `⟨key _ (Or.inl rfl), key _ (Or.inr rfl)⟩`. Use `IsUnit.of_mul_eq_one g (T.eq_of_annNorm_sub ?_ ?_)` and prove the remaining obligations.

Use `all_goals`. Use `le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (T.annNorm_nonneg _ _)` and prove the remaining obligations. Rewrite using `[zero_add]`. Use `set r := annIn ρ0 σ0 set B := T.annNorm ρ0 σ0 r (1 + e) + 1`. Establish `hB : 0 < B` using `by have := T.annNorm_nonneg r (1 + e); positivity`.

Take `⟨J₁, hJ₁⟩` from `eventually_atTop.1 ((hg r).eventually (gt_mem_nhds (div_pos hε hB)))`. Take `⟨J₂, hJ₂⟩` from `exists_pow_lt_of_lt_one hε hl1`. Use `set J := max J₁ J₂`. Establish `hgeom : (1 + e) * S J = 1 - (-e) ^ J`. Simplify using `only [S]`.

Use `geom_sum_mul_neg (-e) J` as an intermediate fact. Rewrite using `[mul_comm, show 1 + e = 1 - -e by ring]; exact this`. Establish `e1 : (1 + e) * g - 1 = (1 + e) * (g - S J) + -((-e) ^ J)`. Rewrite using `[mul_sub, hgeom]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1]`. Use `(T.annNorm_add_le r _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[annNorm_mul, annNorm_sub_comm]`. Establish `h3` using `(hJ₁ J (le_max_left _ _)).le`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[annNorm_neg]`. Conclude with `(hpow r (Or.inl rfl) J).trans ((pow_le_pow_of_le_one hl0 hl1.le (le_max_right _ _)).trans hJ₂.le)`. Use `set r := annOut ρ0 σ0 set B := T.annNorm ρ0 σ0 r (1 + e) + 1`. Establish `hB : 0 < B` using `by have := T.annNorm_nonneg r (1 + e); positivity`. Take `⟨J₁, hJ₁⟩` from `eventually_atTop.1 ((hg r).eventually (gt_mem_nhds (div_pos hε hB)))`.

Take `⟨J₂, hJ₂⟩` from `exists_pow_lt_of_lt_one hε hl1`. Use `set J := max J₁ J₂`. Establish `hgeom : (1 + e) * S J = 1 - (-e) ^ J`. Simplify using `only [S]`. Use `geom_sum_mul_neg (-e) J` as an intermediate fact.

Rewrite using `[mul_comm, show 1 + e = 1 - -e by ring]; exact this`. Establish `e1 : (1 + e) * g - 1 = (1 + e) * (g - S J) + -((-e) ^ J)`. Rewrite using `[mul_sub, hgeom]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`.

Use `(T.annNorm_add_le r _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[annNorm_mul, annNorm_sub_comm]`. Establish `h3` using `(hJ₁ J (le_max_left _ _)).le`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[annNorm_neg]`.

Conclude with `(hpow r (Or.inr rfl) J).trans ((pow_le_pow_of_le_one hl0 hl1.le (le_max_right _ _)).trans hJ₂.le)`.
-/
theorem isUnit_one_add_ann (e : T.Ann ρ0 σ0) (h1 : T.annNorm ρ0 σ0 (annIn ρ0 σ0) e < 1)
    (h2 : T.annNorm ρ0 σ0 (annOut ρ0 σ0) e < 1) : IsUnit (1 + e) := by
  set lam := max (T.annNorm ρ0 σ0 (annIn ρ0 σ0) e) (T.annNorm ρ0 σ0 (annOut ρ0 σ0) e) with hlam
  have hl1 : lam < 1 := max_lt h1 h2
  have hl0 : 0 ≤ lam := le_max_of_le_left (T.annNorm_nonneg _ _)
  have hpow : ∀ (r : AnnRad ρ0 σ0), (r = annIn ρ0 σ0 ∨ r = annOut ρ0 σ0) → ∀ n : ℕ,
      T.annNorm ρ0 σ0 r ((-e) ^ n) ≤ lam ^ n := by
    intro r hr n
    rw [annNorm_pow, annNorm_neg]
    refine pow_le_pow_left₀ (T.annNorm_nonneg _ _) ?_ n
    rcases hr with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  set S : ℕ → T.Ann ρ0 σ0 := fun n => ∑ k ∈ Finset.range n, (-e) ^ k
  have hS : ∀ (r : AnnRad ρ0 σ0), (r = annIn ρ0 σ0 ∨ r = annOut ρ0 σ0) → ∀ m n, m ≤ n →
      T.annNorm ρ0 σ0 r (S n - S m) ≤ lam ^ m := by
    intro r hr m n hmn
    have e1 : S n - S m = ∑ k ∈ Finset.Ico m n, (-e) ^ k := by
      simp only [S]; rw [Finset.sum_Ico_eq_sub _ hmn]
    rw [e1]
    refine T.annNorm_sum_le _ _ r (pow_nonneg hl0 m) fun k hk => ?_
    exact (hpow r hr k).trans (pow_le_pow_of_le_one hl0 hl1.le (Finset.mem_Ico.1 hk).1)
  obtain ⟨g, hg⟩ := T.exists_limit_ann (z := S) fun ε hε => by
    obtain ⟨J₀, hJ₀⟩ := exists_pow_lt_of_lt_one hε hl1
    refine ⟨J₀, fun J hJ K hK => ?_⟩
    have key : ∀ r : AnnRad ρ0 σ0, (r = annIn ρ0 σ0 ∨ r = annOut ρ0 σ0) →
        T.annNorm ρ0 σ0 r (S J - S K) ≤ ε := by
      intro r hr
      rcases le_total K J with h | h
      · exact (hS r hr K J h).trans ((pow_le_pow_of_le_one hl0 hl1.le hK).trans hJ₀.le)
      · rw [annNorm_sub_comm]
        exact (hS r hr J K h).trans ((pow_le_pow_of_le_one hl0 hl1.le hJ).trans hJ₀.le)
    exact ⟨key _ (Or.inl rfl), key _ (Or.inr rfl)⟩
  refine IsUnit.of_mul_eq_one g (T.eq_of_annNorm_sub ?_ ?_)
  all_goals
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (T.annNorm_nonneg _ _)
    rw [zero_add]
  · set r := annIn ρ0 σ0
    set B := T.annNorm ρ0 σ0 r (1 + e) + 1
    have hB : 0 < B := by have := T.annNorm_nonneg r (1 + e); positivity
    obtain ⟨J₁, hJ₁⟩ := eventually_atTop.1 ((hg r).eventually (gt_mem_nhds (div_pos hε hB)))
    obtain ⟨J₂, hJ₂⟩ := exists_pow_lt_of_lt_one hε hl1
    set J := max J₁ J₂
    have hgeom : (1 + e) * S J = 1 - (-e) ^ J := by
      simp only [S]
      have := geom_sum_mul_neg (-e) J
      rw [mul_comm, show 1 + e = 1 - -e by ring]; exact this
    have e1 : (1 + e) * g - 1 = (1 + e) * (g - S J) + -((-e) ^ J) := by
      rw [mul_sub, hgeom]; ring
    rw [e1]
    refine (T.annNorm_add_le r _ _).trans (max_le ?_ ?_)
    · rw [annNorm_mul, annNorm_sub_comm]
      have h3 := (hJ₁ J (le_max_left _ _)).le
      calc T.annNorm ρ0 σ0 r (1 + e) * T.annNorm ρ0 σ0 r (S J - g) ≤ B * (ε / B) :=
            mul_le_mul (by linarith) h3 (T.annNorm_nonneg _ _) hB.le
        _ = ε := by field_simp
    · rw [annNorm_neg]
      exact (hpow r (Or.inl rfl) J).trans ((pow_le_pow_of_le_one hl0 hl1.le (le_max_right _ _)).trans hJ₂.le)
  · set r := annOut ρ0 σ0
    set B := T.annNorm ρ0 σ0 r (1 + e) + 1
    have hB : 0 < B := by have := T.annNorm_nonneg r (1 + e); positivity
    obtain ⟨J₁, hJ₁⟩ := eventually_atTop.1 ((hg r).eventually (gt_mem_nhds (div_pos hε hB)))
    obtain ⟨J₂, hJ₂⟩ := exists_pow_lt_of_lt_one hε hl1
    set J := max J₁ J₂
    have hgeom : (1 + e) * S J = 1 - (-e) ^ J := by
      simp only [S]
      have := geom_sum_mul_neg (-e) J
      rw [mul_comm, show 1 + e = 1 - -e by ring]; exact this
    have e1 : (1 + e) * g - 1 = (1 + e) * (g - S J) + -((-e) ^ J) := by
      rw [mul_sub, hgeom]; ring
    rw [e1]
    refine (T.annNorm_add_le r _ _).trans (max_le ?_ ?_)
    · rw [annNorm_mul, annNorm_sub_comm]
      have h3 := (hJ₁ J (le_max_left _ _)).le
      calc T.annNorm ρ0 σ0 r (1 + e) * T.annNorm ρ0 σ0 r (S J - g) ≤ B * (ε / B) :=
            mul_le_mul (by linarith) h3 (T.annNorm_nonneg _ _) hB.le
        _ = ε := by field_simp
    · rw [annNorm_neg]
      exact (hpow r (Or.inr rfl) J).trans ((pow_le_pow_of_le_one hl0 hl1.le (le_max_right _ _)).trans hJ₂.le)

/- English proof (translation)
Take `⟨u', rfl⟩` from `hu`. Establish `hx : x = (u' : T.Ann ρ0 σ0) * (1 + ((u'⁻¹ : (T.Ann ρ0 σ0)ˣ) : T.Ann ρ0 σ0) * (x - u'))`. Rewrite using `[mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hx]`.

Use `u'.isUnit.mul (T.isUnit_one_add_ann _ ?_ ?_)` and prove the remaining obligations. Establish `hn` using `congrArg (T.annNorm ρ0 σ0 (annIn ρ0 σ0)) (Units.inv_mul u')`. Rewrite `hn` using `[annNorm_mul, annNorm_one]`. Establish `hpos : 0 < T.annNorm ρ0 σ0 (annIn ρ0 σ0) (u' : T.Ann ρ0 σ0)` using `lt_of_le_of_lt (T.annNorm_nonneg _ _) h1`. Rewrite using `[annNorm_mul]`.

Combine the equalities or inequalities in the displayed calculation. Use `mul_lt_mul_of_pos_left h1 ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h0`. Establish `: T.annNorm ρ0 σ0 (annIn ρ0 σ0) ((u'⁻¹ : (T.Ann ρ0 σ0)ˣ) : T.Ann ρ0 σ0) = 0` using `le_antisymm (not_lt.1 h0) (T.annNorm_nonneg _ _)`. Rewrite `hn` using `[this, zero_mul]`.

Conclude with `zero_ne_one hn`. Use `_ = 1 := hn`. Establish `hn` using `congrArg (T.annNorm ρ0 σ0 (annOut ρ0 σ0)) (Units.inv_mul u')`. Rewrite `hn` using `[annNorm_mul, annNorm_one]`. Rewrite using `[annNorm_mul]`.

Combine the equalities or inequalities in the displayed calculation. Use `mul_lt_mul_of_pos_left h2 ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h0`. Establish `: T.annNorm ρ0 σ0 (annOut ρ0 σ0) ((u'⁻¹ : (T.Ann ρ0 σ0)ˣ) : T.Ann ρ0 σ0) = 0` using `le_antisymm (not_lt.1 h0) (T.annNorm_nonneg _ _)`. Rewrite `hn` using `[this, zero_mul]`.

Conclude with `zero_ne_one hn`. Use `_ = 1 := hn`.
-/
theorem isUnit_of_annNorm_sub_lt {u x : T.Ann ρ0 σ0} (hu : IsUnit u)
    (h1 : T.annNorm ρ0 σ0 (annIn ρ0 σ0) (x - u) < T.annNorm ρ0 σ0 (annIn ρ0 σ0) u)
    (h2 : T.annNorm ρ0 σ0 (annOut ρ0 σ0) (x - u) < T.annNorm ρ0 σ0 (annOut ρ0 σ0) u) : IsUnit x := by
  obtain ⟨u', rfl⟩ := hu
  have hx : x = (u' : T.Ann ρ0 σ0) * (1 + ((u'⁻¹ : (T.Ann ρ0 σ0)ˣ) : T.Ann ρ0 σ0) * (x - u')) := by
    rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]; ring
  rw [hx]
  refine u'.isUnit.mul (T.isUnit_one_add_ann _ ?_ ?_)
  · have hn := congrArg (T.annNorm ρ0 σ0 (annIn ρ0 σ0)) (Units.inv_mul u')
    rw [annNorm_mul, annNorm_one] at hn
    have hpos : 0 < T.annNorm ρ0 σ0 (annIn ρ0 σ0) (u' : T.Ann ρ0 σ0) :=
      lt_of_le_of_lt (T.annNorm_nonneg _ _) h1
    rw [annNorm_mul]
    calc T.annNorm ρ0 σ0 (annIn ρ0 σ0) ((u'⁻¹ : (T.Ann ρ0 σ0)ˣ) : T.Ann ρ0 σ0) *
          T.annNorm ρ0 σ0 (annIn ρ0 σ0) (x - u')
        < T.annNorm ρ0 σ0 (annIn ρ0 σ0) ((u'⁻¹ : (T.Ann ρ0 σ0)ˣ) : T.Ann ρ0 σ0) *
          T.annNorm ρ0 σ0 (annIn ρ0 σ0) (u' : T.Ann ρ0 σ0) := by
          refine mul_lt_mul_of_pos_left h1 ?_
          by_contra h0
          have : T.annNorm ρ0 σ0 (annIn ρ0 σ0) ((u'⁻¹ : (T.Ann ρ0 σ0)ˣ) : T.Ann ρ0 σ0) = 0 :=
            le_antisymm (not_lt.1 h0) (T.annNorm_nonneg _ _)
          rw [this, zero_mul] at hn; exact zero_ne_one hn
      _ = 1 := hn
  · have hn := congrArg (T.annNorm ρ0 σ0 (annOut ρ0 σ0)) (Units.inv_mul u')
    rw [annNorm_mul, annNorm_one] at hn
    rw [annNorm_mul]
    calc T.annNorm ρ0 σ0 (annOut ρ0 σ0) ((u'⁻¹ : (T.Ann ρ0 σ0)ˣ) : T.Ann ρ0 σ0) *
          T.annNorm ρ0 σ0 (annOut ρ0 σ0) (x - u')
        < T.annNorm ρ0 σ0 (annOut ρ0 σ0) ((u'⁻¹ : (T.Ann ρ0 σ0)ˣ) : T.Ann ρ0 σ0) *
          T.annNorm ρ0 σ0 (annOut ρ0 σ0) (u' : T.Ann ρ0 σ0) := by
          refine mul_lt_mul_of_pos_left h2 ?_
          by_contra h0
          have : T.annNorm ρ0 σ0 (annOut ρ0 σ0) ((u'⁻¹ : (T.Ann ρ0 σ0)ˣ) : T.Ann ρ0 σ0) = 0 :=
            le_antisymm (not_lt.1 h0) (T.annNorm_nonneg _ _)
          rw [this, zero_mul] at hn; exact zero_ne_one hn
      _ = 1 := hn

def monoB (i : ℤ) (a : L) : T.B := ((T.piB ^ i : T.Bˣ) : T.B) * algebraMap Γ T.B (T.teich a)

/- English proof (translation)
Use function extensionality and compare the values at `n`. Rewrite using `[monoB, coeffB_piB_zpow_mul, zcoeff_teich]`. Distinguish the cases in `h : n = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Pi.single_apply, if_neg (sub_ne_zero.2 h), Pi.single_apply, if_neg h]`.
-/
theorem coeffB_monoB (i : ℤ) (a : L) : T.coeffB (T.monoB i a) = Pi.single i a := by
  funext n
  rw [monoB, coeffB_piB_zpow_mul, zcoeff_teich]
  by_cases h : n = i
  · subst h; simp
  · rw [Pi.single_apply, if_neg (sub_ne_zero.2 h), Pi.single_apply, if_neg h]

/- English proof (translation)
Rewrite using `[monoB, monoB, monoB, T.teich_mul, map_mul, zpow_add, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem monoB_mul_monoB (i j : ℤ) (a b : L) : T.monoB i a * T.monoB j b = T.monoB (i + j) (a * b) := by
  rw [monoB, monoB, monoB, T.teich_mul, map_mul, zpow_add, Units.val_mul]; ring

/- English proof (translation)
Rewrite using `[monoB, zpow_zero, Units.val_one, T.teich_one, map_one, one_mul]`.
-/
theorem monoB_zero_one : T.monoB 0 1 = 1 := by
  rw [monoB, zpow_zero, Units.val_one, T.teich_one, map_one, one_mul]

/- English proof (translation)
Rewrite using `[mem_Econ, coeffB_monoB]`. Conclude with `convergesAt_pi_single _ _ _`.
-/
theorem monoB_mem_Econ (i : ℤ) (a : L) (ρ : Set.Ioo (0 : ℝ) 1) : T.monoB i a ∈ T.Econ ρ := by
  rw [mem_Econ, coeffB_monoB]; exact convergesAt_pi_single _ _ _

/- English proof (translation)
Rewrite using `[coeffB_monoB]`. Use `le_antisymm (gaussNorm_le fun n => ?_) ?_` and prove the remaining obligations. Distinguish the cases in `h : n = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Pi.single_apply, if_neg h, norm_zero, zero_mul]`. Check the signs of the components of the expression. Use `(convergesAt_pi_single (L := L) i a s).le_gaussNorm i` as an intermediate fact. Simplify using `using this`.
-/
theorem gaussNorm_monoB (i : ℤ) (a : L) {s : ℝ} (hs : 0 < s) :
    gaussNorm (T.coeffB (T.monoB i a)) s = ‖a‖ * s ^ i := by
  rw [coeffB_monoB]
  refine le_antisymm (gaussNorm_le fun n => ?_) ?_
  · by_cases h : n = i
    · subst h; simp
    · rw [Pi.single_apply, if_neg h, norm_zero, zero_mul]; positivity
  · have := (convergesAt_pi_single (L := L) i a s).le_gaussNorm i
    simpa using this

/- English proof (translation)
Establish `hX` using `T.num_spec b`. Use `set N := T.den b`. Use `set X := T.num b`. Establish `hb'` using `T.coeffB_eq hX`. Establish `hiN : 0 ≤ i + N`.

Assume the negation of the conclusion as `h`. Apply `hi` to reduce the goal to its premises. Rewrite using `[hb']`. Conclude with `T.zcoeff_of_neg _ (not_le.1 h)`. Use `set k0 := (i + N).toNat with hk0def`.

Establish `hk0 : (k0 : ℤ) = i + N` using `Int.toNat_of_nonneg hiN`. Use `set a := T.coeffB b i with hadef`. Establish `ha : T.coeff X k0 = a`. Rewrite using `[hadef, hb']`. Simplify using `only`.

Rewrite using `[← hk0, zcoeff_natCast]`. Use `set f : ℕ → L := Function.update (T.coeff X) k0 0`. Establish `hg : T.ofCoeff (Pi.single k0 a) = T.π ^ k0 * T.teich a` using `T.eq_of_coeff_eq (funext fun n => by`. Rewrite using `[coeff_ofCoeff, coeff_π_pow_mul_teich, Pi.single_apply])`. Establish `hXf : X = T.ofCoeff f + T.π ^ k0 * T.teich a`.

Rewrite using `[← hg, T.ofCoeff_add_of_disjoint (fun n => by`. Distinguish the cases in `h : n = k0`. Use `left`. Rewrite using `[h]`. Simplify using `[f]`.

Use `right`. Rewrite using `[Pi.single_apply, if_neg h])]`. Use `conv_lhs => rw [← T.ofCoeff_coeff X]`. Use `congr 1`. Use function extensionality and compare the values at `n`.

Distinguish the cases in `h : n = k0`. Substitute `h` using the available equality. Simplify using `[f, ha]`. Simplify using `[f, h]`. Establish `hd : T.monoB i a * algebraMap Γ T.B T.π ^ N = algebraMap Γ T.B (T.π ^ k0 * T.teich a)`.

Rewrite using `[monoB, map_mul, map_pow]`. Establish `e : ((T.piB ^ i : T.Bˣ) : T.B) * algebraMap Γ T.B T.π ^ N = algebraMap Γ T.B T.π ^ k0`. Rewrite using `[← piB_val, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← Units.val_mul, ← zpow_add, ← zpow_natCast, hk0]`. Combine the equalities or inequalities in the displayed calculation. Establish `hsub : (b - T.monoB i a) * algebraMap Γ T.B T.π ^ N = algebraMap Γ T.B (T.ofCoeff f)`.

Rewrite using `[sub_mul, hX, hd, ← map_sub, hXf, add_sub_cancel_right]`. Rewrite using `[T.coeffB_eq hsub]`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality.

Rewrite using `[Function.update_self, ← hk0, zcoeff_natCast, coeff_ofCoeff]`. Simplify using `[f]`. Rewrite using `[Function.update_of_ne hk, hb']`. Simplify using `only`. Break down `lt_or_ge (k + N) 0 with hkN | hkN` into its components or cases.

Rewrite using `[T.zcoeff_of_neg _ hkN, T.zcoeff_of_neg _ hkN]`. Use `lift k + N to ℕ using hkN with m hm`. Rewrite using `[zcoeff_natCast, zcoeff_natCast, coeff_ofCoeff]`. Establish `hm' : m ≠ k0`. Introduce `h`.

Apply `hk` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers. Simplify using `[f, Function.update_of_ne hm']`.
-/
theorem coeffB_sub_monoB (b : T.B) (i : ℤ) (hi : T.coeffB b i ≠ 0) :
    T.coeffB (b - T.monoB i (T.coeffB b i)) = Function.update (T.coeffB b) i 0 := by
  classical
  have hX := T.num_spec b
  set N := T.den b
  set X := T.num b
  have hb' := T.coeffB_eq hX
  have hiN : 0 ≤ i + N := by
    by_contra h
    apply hi
    rw [hb']
    exact T.zcoeff_of_neg _ (not_le.1 h)
  set k0 := (i + N).toNat with hk0def
  have hk0 : (k0 : ℤ) = i + N := Int.toNat_of_nonneg hiN
  set a := T.coeffB b i with hadef
  have ha : T.coeff X k0 = a := by
    rw [hadef, hb']; simp only; rw [← hk0, zcoeff_natCast]
  set f : ℕ → L := Function.update (T.coeff X) k0 0
  have hg : T.ofCoeff (Pi.single k0 a) = T.π ^ k0 * T.teich a :=
    T.eq_of_coeff_eq (funext fun n => by
      rw [coeff_ofCoeff, coeff_π_pow_mul_teich, Pi.single_apply])
  have hXf : X = T.ofCoeff f + T.π ^ k0 * T.teich a := by
    rw [← hg, T.ofCoeff_add_of_disjoint (fun n => by
      by_cases h : n = k0
      · left; rw [h]; simp [f]
      · right; rw [Pi.single_apply, if_neg h])]
    conv_lhs => rw [← T.ofCoeff_coeff X]
    congr 1
    funext n
    by_cases h : n = k0
    · subst h; simp [f, ha]
    · simp [f, h]
  have hd : T.monoB i a * algebraMap Γ T.B T.π ^ N = algebraMap Γ T.B (T.π ^ k0 * T.teich a) := by
    rw [monoB, map_mul, map_pow]
    have e : ((T.piB ^ i : T.Bˣ) : T.B) * algebraMap Γ T.B T.π ^ N = algebraMap Γ T.B T.π ^ k0 := by
      rw [← piB_val, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← zpow_natCast,
        ← Units.val_mul, ← zpow_add, ← zpow_natCast, hk0]
    calc ((T.piB ^ i : T.Bˣ) : T.B) * algebraMap Γ T.B (T.teich a) * algebraMap Γ T.B T.π ^ N
        = (((T.piB ^ i : T.Bˣ) : T.B) * algebraMap Γ T.B T.π ^ N) * algebraMap Γ T.B (T.teich a) := by ring
      _ = _ := by rw [e]
  have hsub : (b - T.monoB i a) * algebraMap Γ T.B T.π ^ N = algebraMap Γ T.B (T.ofCoeff f) := by
    rw [sub_mul, hX, hd, ← map_sub, hXf, add_sub_cancel_right]
  rw [T.coeffB_eq hsub]
  funext k
  by_cases hk : k = i
  · subst hk
    rw [Function.update_self, ← hk0, zcoeff_natCast, coeff_ofCoeff]
    simp [f]
  · rw [Function.update_of_ne hk, hb']
    simp only
    rcases lt_or_ge (k + N) 0 with hkN | hkN
    · rw [T.zcoeff_of_neg _ hkN, T.zcoeff_of_neg _ hkN]
    · lift k + N to ℕ using hkN with m hm
      rw [zcoeff_natCast, zcoeff_natCast, coeff_ofCoeff]
      have hm' : m ≠ k0 := by
        intro h; apply hk; omega
      simp [f, Function.update_of_ne hm']

/- English proof (translation)
Use `set i := lowIndex (T.coeffB b) s`. Establish `hmem` using `lowIndex_mem hs0 hb hb0`. Establish `hi : T.coeffB b i ≠ 0` using `ne_zero_of_mem_domSet hs0 hb hb0 hmem`. Establish `hpos : 0 < gaussNorm (T.coeffB b) s` using `gaussNorm_pos hs0 hb hb0`. Rewrite using `[T.coeffB_sub_monoB b i hi]`.

Establish `hconv : ConvergesAt (Function.update (T.coeffB b) i 0) s` using `(convergesAt_of_norm_le hs0 (fun n => by`. Distinguish the cases in `h : n = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne h]) hb).1`.

Distinguish the cases in `h0 : Function.update (T.coeffB b) i 0 = 0`. Rewrite using `[h0]`. Simplify `hpos` using `[gaussNorm]`. Take `⟨j, hj⟩` from `hconv.exists_eq_gaussNorm hs0 h0`. Rewrite using `[← hj]`.

Establish `hji : j ≠ i`. Introduce `h`. Substitute `h` using the available equality. Rewrite `hj` using `[Function.update_self, norm_zero, zero_mul]`. Use `gaussNorm_pos hs0 hconv h0` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Function.update_of_ne hji]`. Use `lt_of_le_of_ne (hb.le_gaussNorm j) fun heq => hji ?_` and prove the remaining obligations. Establish `hjmem : j ∈ domSet (T.coeffB b) s` using `heq`. Conclude with `le_antisymm (hli ▸ le_highIndex hs0 hb hb0 hjmem) (lowIndex_le hs0 hb hb0 hjmem)`.
-/
theorem gaussNorm_sub_monoB_lt {b : T.B} {s : ℝ} (hs0 : 0 < s) (hb : ConvergesAt (T.coeffB b) s)
    (hb0 : T.coeffB b ≠ 0) (hli : lowIndex (T.coeffB b) s = highIndex (T.coeffB b) s) :
    gaussNorm (T.coeffB (b - T.monoB (lowIndex (T.coeffB b) s) (T.coeffB b (lowIndex (T.coeffB b) s)))) s <
      gaussNorm (T.coeffB b) s := by
  set i := lowIndex (T.coeffB b) s
  have hmem := lowIndex_mem hs0 hb hb0
  have hi : T.coeffB b i ≠ 0 := ne_zero_of_mem_domSet hs0 hb hb0 hmem
  have hpos : 0 < gaussNorm (T.coeffB b) s := gaussNorm_pos hs0 hb hb0
  rw [T.coeffB_sub_monoB b i hi]
  have hconv : ConvergesAt (Function.update (T.coeffB b) i 0) s :=
    (convergesAt_of_norm_le hs0 (fun n => by
      by_cases h : n = i
      · subst h; simp
      · rw [Function.update_of_ne h]) hb).1
  by_cases h0 : Function.update (T.coeffB b) i 0 = 0
  · rw [h0]; simpa [gaussNorm] using hpos
  obtain ⟨j, hj⟩ := hconv.exists_eq_gaussNorm hs0 h0
  rw [← hj]
  have hji : j ≠ i := by
    intro h; subst h
    rw [Function.update_self, norm_zero, zero_mul] at hj
    have := gaussNorm_pos hs0 hconv h0
    linarith
  rw [Function.update_of_ne hji]
  refine lt_of_le_of_ne (hb.le_gaussNorm j) fun heq => hji ?_
  have hjmem : j ∈ domSet (T.coeffB b) s := heq
  exact le_antisymm (hli ▸ le_highIndex hs0 hb hb0 hjmem) (lowIndex_le hs0 hb hb0 hjmem)

/- English proof (translation)
Introduce `h0`. Establish `hc0 : c = 0` using `T.coe_injective_Econ (by rw [h0, Completion.coe_zero])`. Rewrite `hc` using `[hc0, map_zero, sub_zero]`. Conclude with `lt_irrefl _ hc`.
-/
theorem coe_ne_zero_of_annNorm_sub_lt {v : T.Ann ρ0 σ0} {c : T.Econ ρ0} (r : AnnRad ρ0 σ0)
    (hc : T.annNorm ρ0 σ0 r (v - T.coeAnn c) < T.annNorm ρ0 σ0 r v) : (c : T.RobbaExt ρ0) ≠ 0 := by
  intro h0
  have hc0 : c = 0 := T.coe_injective_Econ (by rw [h0, Completion.coe_zero])
  rw [hc0, map_zero, sub_zero] at hc
  exact lt_irrefl _ hc

/- English proof (translation)
Establish `h1` using `T.annNorm_sub_le r x (x - y)`. Rewrite `h1` using `[sub_sub_cancel]`. Establish `h2` using `T.annNorm_add_le r (x - y) y`. Rewrite `h2` using `[sub_add_cancel]`. Apply `le_antisymm` to reduce the goal to its premises.

Conclude with `h1.trans (max_le le_rfl h.le)`. Break down `le_max_iff.1 h2 with h3 | h3` into its components or cases. Conclude with `absurd h3 (not_le.2 h)`. Conclude with `h3`.
-/
theorem annNorm_eq_of_sub_lt {x y : T.Ann ρ0 σ0} {r : AnnRad ρ0 σ0}
    (h : T.annNorm ρ0 σ0 r (x - y) < T.annNorm ρ0 σ0 r x) :
    T.annNorm ρ0 σ0 r y = T.annNorm ρ0 σ0 r x := by
  have h1 := T.annNorm_sub_le r x (x - y)
  rw [sub_sub_cancel] at h1
  have h2 := T.annNorm_add_le r (x - y) y
  rw [sub_add_cancel] at h2
  apply le_antisymm
  · exact h1.trans (max_le le_rfl h.le)
  · rcases le_max_iff.1 h2 with h3 | h3
    · exact absurd h3 (not_le.2 h)
    · exact h3

/- English proof (translation)
Establish `hc0 : (c : T.RobbaExt ρ0) ≠ 0` using `T.coe_ne_zero_of_annNorm_sub_lt (annIn ρ0 σ0) (hc _)`. Establish `ha : (0 : ℝ) < σ1` using `σ1.2.1`. Establish `hab : (σ1 : ℝ) ≤ ρ1` using `σ1.2.2`. Establish `hsum` using `T.sum_mult_breaksR hc0 ha hab h`. Establish `h0 : ∑ ρ ∈ (T.breaksR_finite hc0 ha hab h).toFinset, T.mult (c : T.RobbaExt ρ0) ρ = 0` using `Finset.sum_eq_zero fun ρ hρ => by`.

Simplify using `only [Set.Finite.mem_toFinset, breaksR, Set.mem_ofPred_eq] at hρ`. Conclude with `hm ρ hρ.1.1 hρ.1.2`. Establish `hma` using `hm σ1 le_rfl hab`. Establish `hmb` using `hm ρ1 hab le_rfl`. Rewrite `hma`, `hmb` using `[mult]`.

Establish `hia` using `T.idx_coe hc0 ⟨ha, hab.trans_lt h⟩`. Establish `hib` using `T.idx_coe hc0 ⟨ha.trans_le hab, h⟩`. Use `set a := T.coeffB (c : T.B)`. Establish `hA : ConvergesAt a σ1` using `T.convergesAt_rad ρ0 c ⟨σ1, ha, hab.trans h.le⟩`. Establish `hB : ConvergesAt a ρ1` using `T.convergesAt_rad ρ0 c ⟨ρ1, ha.trans_le hab, h.le⟩`.

Establish `ha0 : a ≠ 0`. Introduce `h0'`. Apply `hc0` to reduce the goal to its premises. Establish `: (c : T.B) = 0`. Take `⟨N, y, hy⟩` from `IsLocalization.Away.surj T.π (c : T.B)`.

Establish `hy0 : y = 0`. Use `(T.zcoeff_eq_zero_iff y).1 (funext fun k => ?_)` and prove the remaining obligations. Use `congrFun h0' (k - N)` as an intermediate fact. Rewrite `this` using `[show a = T.coeffB (c : T.B) from rfl, T.coeffB_eq hy]`. Simplify using `using this`.

Rewrite `hy` using `[hy0, map_zero]`. Conclude with `T.eq_zero_of_mul_pow hy`. Rewrite using `[show c = 0 from Subtype.ext this, Completion.coe_zero]`. Establish `e1 : lowIndex a σ1 = highIndex a σ1` using `by rw [← hia.1, ← hia.2]; omega`. Establish `e2 : lowIndex a ρ1 = highIndex a ρ1` using `by rw [← hib.1, ← hib.2]; omega`.

Establish `e3 : lowIndex a ρ1 = lowIndex a σ1` using `by rw [← hib.1, ← hia.1]; omega`. Use `set i := lowIndex a σ1`. Use `set d : T.Econ ρ0 := ⟨T.monoB i (a i), T.monoB_mem_Econ _ _ _⟩`. Use `set dinv : T.Econ ρ0 := ⟨T.monoB (-i) (a i)⁻¹, T.monoB_mem_Econ _ _ _⟩`. Establish `hai : a i ≠ 0` using `ne_zero_of_mem_domSet ha hA ha0 (lowIndex_mem ha hA ha0)`.

Establish `hdd : d * dinv = 1` using `Subtype.ext (by show T.monoB i (a i) * T.monoB (-i) (a i)⁻¹ = 1`. Rewrite using `[monoB_mul_monoB, add_neg_cancel, mul_inv_cancel₀ hai, monoB_zero_one])`. Establish `hlt1` using `T.gaussNorm_sub_monoB_lt ha hA ha0 e1`. Establish `hlt2` using `T.gaussNorm_sub_monoB_lt (ha.trans_le hab) hB ha0 e2`. Rewrite `hlt2` using `[e3]`.

Establish `hdn : ∀ s : ℝ, 0 < s → gaussNorm (T.coeffB (d : T.B)) s = ‖a i‖ * s ^ i` using `fun s hs => T.gaussNorm_monoB i (a i) hs`. Establish `hcn1 : gaussNorm a σ1 = ‖a i‖ * (σ1 : ℝ) ^ i` using `(lowIndex_mem ha hA ha0).symm`. Establish `hcn2 : gaussNorm a ρ1 = ‖a i‖ * (ρ1 : ℝ) ^ i`. Use `(lowIndex_mem (ha.trans_le hab) hB ha0).symm` as an intermediate fact. Rewrite `this` using `[e3]`.

Conclude with `this`. Use `set C := T.annRes h.le hs (T.coeAnn c)`. Use `set D := T.annRes h.le hs (T.coeAnn d)`. Establish `hD : IsUnit D` using `IsUnit.of_mul_eq_one (T.annRes h.le hs (T.coeAnn dinv)) (by`. Rewrite using `[← map_mul, ← map_mul, hdd, map_one, map_one])`.

Establish `hnC : ∀ r : AnnRad ρ1 σ1, T.annNorm ρ1 σ1 r C = gaussNorm a r` using `fun r => by`. Rewrite using `[T.annNorm_annRes, annNorm_coeAnn]`. Both sides reduce to the same expression. Establish `hnD : ∀ r : AnnRad ρ1 σ1, T.annNorm ρ1 σ1 r D = gaussNorm (T.coeffB (d : T.B)) r` using `fun r => by`. Rewrite using `[T.annNorm_annRes, annNorm_coeAnn]`.

Both sides reduce to the same expression. Establish `hnCD : ∀ r : AnnRad ρ1 σ1, T.annNorm ρ1 σ1 r (C - D) = gaussNorm (T.coeffB ((c : T.B) - T.monoB i (a i))) r` using `fun r => by`. Rewrite using `[← map_sub, ← map_sub, T.annNorm_annRes, annNorm_coeAnn]`. Both sides reduce to the same expression. Establish `hCu : IsUnit C`.

Use `T.isUnit_of_annNorm_sub_lt hD ?_ ?_` and prove the remaining obligations. Rewrite using `[hnCD, hnD, coe_annIn, hdn _ ha, ← hcn1]`. Conclude with `hlt1`. Rewrite using `[hnCD, hnD, coe_annOut, hdn _ (ha.trans_le hab), ← hcn2]`. Conclude with `hlt2`.

Use `T.isUnit_of_annNorm_sub_lt hCu ?_ ?_` and prove the remaining obligations. Use `all_goals`. Rewrite using `[← map_sub, T.annNorm_annRes, T.annNorm_annRes, annRadOf]`. Use `(hc _).trans_le (le_of_eq ?_)` and prove the remaining obligations. Conclude with `(T.annNorm_eq_of_sub_lt (hc _)).symm`.
-/
theorem isUnit_annRes_of_mult_eq_zero (v : T.Ann ρ0 σ0) (c : T.Econ ρ0)
    (hc : ∀ r, T.annNorm ρ0 σ0 r (v - T.coeAnn c) < T.annNorm ρ0 σ0 r v)
    {ρ1 : Set.Ioo (0 : ℝ) 1} {σ1 : Set.Ioc (0 : ℝ) ρ1} (h : (ρ1 : ℝ) < ρ0) (hs : (σ0 : ℝ) ≤ σ1)
    (hm : ∀ s : ℝ, (σ1 : ℝ) ≤ s → s ≤ ρ1 → T.mult (c : T.RobbaExt ρ0) s = 0) :
    IsUnit (T.annRes h.le hs v) := by
  have hc0 : (c : T.RobbaExt ρ0) ≠ 0 := T.coe_ne_zero_of_annNorm_sub_lt (annIn ρ0 σ0) (hc _)
  have ha : (0 : ℝ) < σ1 := σ1.2.1
  have hab : (σ1 : ℝ) ≤ ρ1 := σ1.2.2

  have hsum := T.sum_mult_breaksR hc0 ha hab h
  have h0 : ∑ ρ ∈ (T.breaksR_finite hc0 ha hab h).toFinset, T.mult (c : T.RobbaExt ρ0) ρ = 0 :=
    Finset.sum_eq_zero fun ρ hρ => by
      simp only [Set.Finite.mem_toFinset, breaksR, Set.mem_ofPred_eq] at hρ
      exact hm ρ hρ.1.1 hρ.1.2
  have hma := hm σ1 le_rfl hab
  have hmb := hm ρ1 hab le_rfl
  rw [mult] at hma hmb
  have hia := T.idx_coe hc0 ⟨ha, hab.trans_lt h⟩
  have hib := T.idx_coe hc0 ⟨ha.trans_le hab, h⟩
  set a := T.coeffB (c : T.B)
  have hA : ConvergesAt a σ1 := T.convergesAt_rad ρ0 c ⟨σ1, ha, hab.trans h.le⟩
  have hB : ConvergesAt a ρ1 := T.convergesAt_rad ρ0 c ⟨ρ1, ha.trans_le hab, h.le⟩
  have ha0 : a ≠ 0 := by
    intro h0'
    apply hc0
    have : (c : T.B) = 0 := by
      obtain ⟨N, y, hy⟩ := IsLocalization.Away.surj T.π (c : T.B)
      have hy0 : y = 0 := by
        refine (T.zcoeff_eq_zero_iff y).1 (funext fun k => ?_)
        have := congrFun h0' (k - N)
        rw [show a = T.coeffB (c : T.B) from rfl, T.coeffB_eq hy] at this
        simpa using this
      rw [hy0, map_zero] at hy
      exact T.eq_zero_of_mul_pow hy
    rw [show c = 0 from Subtype.ext this, Completion.coe_zero]
  have e1 : lowIndex a σ1 = highIndex a σ1 := by rw [← hia.1, ← hia.2]; omega
  have e2 : lowIndex a ρ1 = highIndex a ρ1 := by rw [← hib.1, ← hib.2]; omega
  have e3 : lowIndex a ρ1 = lowIndex a σ1 := by rw [← hib.1, ← hia.1]; omega
  set i := lowIndex a σ1
  set d : T.Econ ρ0 := ⟨T.monoB i (a i), T.monoB_mem_Econ _ _ _⟩
  set dinv : T.Econ ρ0 := ⟨T.monoB (-i) (a i)⁻¹, T.monoB_mem_Econ _ _ _⟩
  have hai : a i ≠ 0 := ne_zero_of_mem_domSet ha hA ha0 (lowIndex_mem ha hA ha0)
  have hdd : d * dinv = 1 := Subtype.ext (by
    show T.monoB i (a i) * T.monoB (-i) (a i)⁻¹ = 1
    rw [monoB_mul_monoB, add_neg_cancel, mul_inv_cancel₀ hai, monoB_zero_one])

  have hlt1 := T.gaussNorm_sub_monoB_lt ha hA ha0 e1
  have hlt2 := T.gaussNorm_sub_monoB_lt (ha.trans_le hab) hB ha0 e2
  rw [e3] at hlt2
  have hdn : ∀ s : ℝ, 0 < s → gaussNorm (T.coeffB (d : T.B)) s = ‖a i‖ * s ^ i := fun s hs =>
    T.gaussNorm_monoB i (a i) hs
  have hcn1 : gaussNorm a σ1 = ‖a i‖ * (σ1 : ℝ) ^ i := (lowIndex_mem ha hA ha0).symm
  have hcn2 : gaussNorm a ρ1 = ‖a i‖ * (ρ1 : ℝ) ^ i := by
    have := (lowIndex_mem (ha.trans_le hab) hB ha0).symm
    rw [e3] at this; exact this

  set C := T.annRes h.le hs (T.coeAnn c)
  set D := T.annRes h.le hs (T.coeAnn d)
  have hD : IsUnit D := IsUnit.of_mul_eq_one (T.annRes h.le hs (T.coeAnn dinv)) (by
    rw [← map_mul, ← map_mul, hdd, map_one, map_one])
  have hnC : ∀ r : AnnRad ρ1 σ1, T.annNorm ρ1 σ1 r C = gaussNorm a r := fun r => by
    rw [T.annNorm_annRes, annNorm_coeAnn]; rfl
  have hnD : ∀ r : AnnRad ρ1 σ1, T.annNorm ρ1 σ1 r D = gaussNorm (T.coeffB (d : T.B)) r := fun r => by
    rw [T.annNorm_annRes, annNorm_coeAnn]; rfl
  have hnCD : ∀ r : AnnRad ρ1 σ1, T.annNorm ρ1 σ1 r (C - D) =
      gaussNorm (T.coeffB ((c : T.B) - T.monoB i (a i))) r := fun r => by
    rw [← map_sub, ← map_sub, T.annNorm_annRes, annNorm_coeAnn]; rfl
  have hCu : IsUnit C := by
    refine T.isUnit_of_annNorm_sub_lt hD ?_ ?_
    · rw [hnCD, hnD, coe_annIn, hdn _ ha, ← hcn1]; exact hlt1
    · rw [hnCD, hnD, coe_annOut, hdn _ (ha.trans_le hab), ← hcn2]; exact hlt2
  refine T.isUnit_of_annNorm_sub_lt hCu ?_ ?_
  all_goals
    rw [← map_sub, T.annNorm_annRes, T.annNorm_annRes, annRadOf]
    refine (hc _).trans_le (le_of_eq ?_)
    exact (T.annNorm_eq_of_sub_lt (hc _)).symm

/- English proof (translation)
Rewrite using `[ptEvalB, coeffB_monoB, ptEvalSeq, tsum_eq_single i (fun n hn => by`. Rewrite using `[ptTerm, Pi.single_apply, if_neg hn, map_zero, mul_zero]), norm_ptTerm, Pi.single_eq_same]`.
-/
theorem ptEvalB_monoB {ξ : T.int} (hξ : T.IsPrimOne ξ) (i : ℤ) (c : L) :
    ‖T.ptEvalB hξ (T.monoB i c)‖ = ‖c‖ * T.ptRad ξ ^ i := by
  rw [ptEvalB, coeffB_monoB, ptEvalSeq, tsum_eq_single i (fun n hn => by
    rw [ptTerm, Pi.single_apply, if_neg hn, map_zero, mul_zero]), norm_ptTerm, Pi.single_eq_same]

/- English proof (translation)
Establish `hr0` using `T.ptRad_pos' hξ`. Establish `hr1` using `T.ptRad_lt_one' hξ`. Use `set i := lowIndex (T.coeffB b) (T.ptRad ξ)`. Use `set m := T.monoB i (T.coeffB b i)`. Establish `hmc : ConvergesAt (T.coeffB m) (T.ptRad ξ)`.

Rewrite using `[coeffB_monoB]`. Conclude with `convergesAt_pi_single _ _ _`. Establish `hdc : ConvergesAt (T.coeffB (b - m)) (T.ptRad ξ)`. Rewrite using `[sub_eq_add_neg]`. Conclude with `(T.convergesAt_coeffB_add hr0 hr1 hb (T.convergesAt_coeffB_neg hr0 hr1 hmc).1).1`.

Establish `hlt` using `T.gaussNorm_sub_monoB_lt hr0 hb hb0 hli`. Establish `hdom : gaussNorm (T.coeffB b) (T.ptRad ξ) = ‖T.coeffB b i‖ * T.ptRad ξ ^ i` using `(lowIndex_mem hr0 hb hb0).symm`. Establish `h1 : ‖T.ptEvalB hξ m‖ = gaussNorm (T.coeffB b) (T.ptRad ξ)`. Rewrite using `[T.ptEvalB_monoB hξ, hdom]`. Establish `h2 : ‖T.ptEvalB hξ (b - m)‖ < gaussNorm (T.coeffB b) (T.ptRad ξ)` using `(T.norm_ptEvalB_le hξ hdc).trans_lt hlt`.

Establish `e : b = m + (b - m)` using `by ring`. Rewrite using `[e, T.ptEvalB_add hξ hmc hdc, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h1]; exact h2.ne'), h1, max_eq_left h2.le]`. Rewrite using `[← e]`.
-/
theorem norm_ptEvalB_of_dom {ξ : T.int} (hξ : T.IsPrimOne ξ) {b : T.B}
    (hb : ConvergesAt (T.coeffB b) (T.ptRad ξ)) (hb0 : T.coeffB b ≠ 0)
    (hli : lowIndex (T.coeffB b) (T.ptRad ξ) = highIndex (T.coeffB b) (T.ptRad ξ)) :
    ‖T.ptEvalB hξ b‖ = gaussNorm (T.coeffB b) (T.ptRad ξ) := by
  have hr0 := T.ptRad_pos' hξ
  have hr1 := T.ptRad_lt_one' hξ
  set i := lowIndex (T.coeffB b) (T.ptRad ξ)
  set m := T.monoB i (T.coeffB b i)
  have hmc : ConvergesAt (T.coeffB m) (T.ptRad ξ) := by
    rw [coeffB_monoB]; exact convergesAt_pi_single _ _ _
  have hdc : ConvergesAt (T.coeffB (b - m)) (T.ptRad ξ) := by
    rw [sub_eq_add_neg]
    exact (T.convergesAt_coeffB_add hr0 hr1 hb (T.convergesAt_coeffB_neg hr0 hr1 hmc).1).1
  have hlt := T.gaussNorm_sub_monoB_lt hr0 hb hb0 hli
  have hdom : gaussNorm (T.coeffB b) (T.ptRad ξ) = ‖T.coeffB b i‖ * T.ptRad ξ ^ i :=
    (lowIndex_mem hr0 hb hb0).symm
  have h1 : ‖T.ptEvalB hξ m‖ = gaussNorm (T.coeffB b) (T.ptRad ξ) := by
    rw [T.ptEvalB_monoB hξ, hdom]
  have h2 : ‖T.ptEvalB hξ (b - m)‖ < gaussNorm (T.coeffB b) (T.ptRad ξ) :=
    (T.norm_ptEvalB_le hξ hdc).trans_lt hlt
  have e : b = m + (b - m) := by ring
  rw [e, T.ptEvalB_add hξ hmc hdc, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
    (by rw [h1]; exact h2.ne'), h1, max_eq_left h2.le]
  rw [← e]

/- English proof (translation)
Establish `h : 0 < T.ptRad ξ ∧ T.ptRad ξ < ρ0` using `⟨T.ptRad_pos' hξ, hr⟩`. Establish `hc` using `T.approx_spec hu h (T.ptRadIoc hξ hr.le) le_rfl (mid_rad h).2.2.le`. Establish `hl` using `T.lowIdx_eq_approx hu h`. Establish `hh` using `T.highIdx_eq_approx hu h`. Rewrite `hm` using `[mult, hh, hl]`.

Use `set c := T.approx hu h`. Establish `hc0 : (c : T.B) ≠ 0` using `T.coe_ne_zero_of_approx hc`. Establish `hcoeff0 : T.coeffB (c : T.B) ≠ 0`. Introduce `h0`. Take `⟨N, y, hy⟩` from `IsLocalization.Away.surj T.π (c : T.B)`.

Establish `hy0 : y = 0`. Use `(T.zcoeff_eq_zero_iff y).1 (funext fun k => ?_)` and prove the remaining obligations. Use `congrFun h0 (k - N)` as an intermediate fact. Rewrite `this` using `[T.coeffB_eq hy]`. Simplify using `using this`.

Rewrite `hy` using `[hy0, map_zero]`. Conclude with `hc0 (T.eq_zero_of_mul_pow hy)`. Establish `hcv : ConvergesAt (T.coeffB (c : T.B)) (T.ptRad ξ)` using `T.convergesAt_rad ρ0 c (T.ptRadIoc hξ hr.le)`. Establish `h1 : ‖T.ptEval hξ hr.le (c : T.RobbaExt ρ0)‖ = T.extNorm ρ0 (T.ptRadIoc hξ hr.le) u`. Rewrite using `[ptEval_coe, T.norm_ptEvalB_of_dom hξ hcv hcoeff0 (by omega), ← T.extNorm_eq_of_lt hc, extNorm_coe]`.

Both sides reduce to the same expression. Establish `h2 : ‖T.ptEval hξ hr.le (u - c)‖ < T.extNorm ρ0 (T.ptRadIoc hξ hr.le) u` using `(T.norm_ptEval_le hξ hr.le _).trans_lt hc`. Establish `e : u = (c : T.RobbaExt ρ0) + (u - c)` using `by ring`. Rewrite using `[e, map_add, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h1]; exact h2.ne'), h1, max_eq_left h2.le, ← e]`.
-/
theorem norm_ptEval_of_mult_eq_zero {u : T.RobbaExt ρ0} (hu : u ≠ 0) {ξ : T.int} (hξ : T.IsPrimOne ξ)
    (hr : T.ptRad ξ < ρ0) (hm : T.mult u (T.ptRad ξ) = 0) :
    ‖T.ptEval hξ hr.le u‖ = T.extNorm ρ0 (T.ptRadIoc hξ hr.le) u := by
  have h : 0 < T.ptRad ξ ∧ T.ptRad ξ < ρ0 := ⟨T.ptRad_pos' hξ, hr⟩
  have hc := T.approx_spec hu h (T.ptRadIoc hξ hr.le) le_rfl (mid_rad h).2.2.le
  have hl := T.lowIdx_eq_approx hu h
  have hh := T.highIdx_eq_approx hu h
  rw [mult, hh, hl] at hm
  set c := T.approx hu h
  have hc0 : (c : T.B) ≠ 0 := T.coe_ne_zero_of_approx hc
  have hcoeff0 : T.coeffB (c : T.B) ≠ 0 := by
    intro h0
    obtain ⟨N, y, hy⟩ := IsLocalization.Away.surj T.π (c : T.B)
    have hy0 : y = 0 := by
      refine (T.zcoeff_eq_zero_iff y).1 (funext fun k => ?_)
      have := congrFun h0 (k - N)
      rw [T.coeffB_eq hy] at this
      simpa using this
    rw [hy0, map_zero] at hy
    exact hc0 (T.eq_zero_of_mul_pow hy)
  have hcv : ConvergesAt (T.coeffB (c : T.B)) (T.ptRad ξ) := T.convergesAt_rad ρ0 c (T.ptRadIoc hξ hr.le)
  have h1 : ‖T.ptEval hξ hr.le (c : T.RobbaExt ρ0)‖ = T.extNorm ρ0 (T.ptRadIoc hξ hr.le) u := by
    rw [ptEval_coe, T.norm_ptEvalB_of_dom hξ hcv hcoeff0 (by omega), ← T.extNorm_eq_of_lt hc,
      extNorm_coe]
    rfl
  have h2 : ‖T.ptEval hξ hr.le (u - c)‖ < T.extNorm ρ0 (T.ptRadIoc hξ hr.le) u :=
    (T.norm_ptEval_le hξ hr.le _).trans_lt hc
  have e : u = (c : T.RobbaExt ρ0) + (u - c) := by ring
  rw [e, map_add, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h1]; exact h2.ne'), h1,
    max_eq_left h2.le, ← e]

def annLogNorm (q : T.Ann ρ0 σ0) (t : ℝ) : ℝ := Real.log (T.annNormR q (Real.exp t))

/- English proof (translation)
Rewrite using `[annLogNorm, Real.exp_log (σ0.2.1.trans_le r.2.1), T.annNormR_of_mem q r]`.
-/
theorem annLogNorm_of_mem (q : T.Ann ρ0 σ0) (r : AnnRad ρ0 σ0) :
    T.annLogNorm q (Real.log r) = Real.log (T.annNorm ρ0 σ0 r q) := by
  rw [annLogNorm, Real.exp_log (σ0.2.1.trans_le r.2.1), T.annNormR_of_mem q r]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[← Real.exp_log σ0.2.1]`. Conclude with `Real.exp_le_exp.2 ht.1`. Rewrite using `[← Real.exp_log ρ0.2.1]`. Conclude with `Real.exp_le_exp.2 ht.2`.
-/
theorem exp_mem_of_mem_Icc {t : ℝ} (ht : t ∈ Set.Icc (Real.log σ0) (Real.log ρ0)) :
    Real.exp t ∈ Set.Icc (σ0 : ℝ) ρ0 := by
  constructor
  · rw [← Real.exp_log σ0.2.1]; exact Real.exp_le_exp.2 ht.1
  · rw [← Real.exp_log ρ0.2.1]; exact Real.exp_le_exp.2 ht.2

/- English proof (translation)
Use `⟨convex_Icc _ _, fun x hx y hy a b ha hb hab => ?_⟩` and prove the remaining obligations. Use `set r₁ : AnnRad ρ0 σ0 := ⟨Real.exp x, exp_mem_of_mem_Icc hx⟩`. Use `set r₂ : AnnRad ρ0 σ0 := ⟨Real.exp y, exp_mem_of_mem_Icc hy⟩`. Establish `hz : a • x + b • y ∈ Set.Icc (Real.log σ0) (Real.log ρ0)` using `(convex_Icc _ _) hx hy ha hb hab`. Use `set r : AnnRad ρ0 σ0 := ⟨Real.exp (a • x + b • y), exp_mem_of_mem_Icc hz⟩`.

Establish `hr : (r : ℝ) = (r₁ : ℝ) ^ (1 - b) * (r₂ : ℝ) ^ b` using `by show Real.exp (a • x + b • y) = Real.exp x ^ (1 - b) * Real.exp y ^ b`. Rewrite using `[← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, smul_eq_mul, smul_eq_mul, show 1 - b = a by linarith]`. Put the polynomial expressions in normal form. Establish `hi` using `T.annNorm_interp_le r₁ r₂ r (by linarith) (by linarith) hr q`. Establish `h1` using `hq r₁`.

Establish `h2` using `hq r₂`. Establish `hlog` using `Real.log_le_log (hq r) hi`. Rewrite `hlog` using `[Real.log_mul (Real.rpow_pos_of_pos h1 _).ne' (Real.rpow_pos_of_pos h2 _).ne', Real.log_rpow h1, Real.log_rpow h2, show 1 - b = a by linarith]`. Simplify using `only [smul_eq_mul]`. Establish `e1 : T.annLogNorm q x = Real.log (T.annNorm ρ0 σ0 r₁ q)`.

Rewrite using `[annLogNorm, T.annNormR_of_mem q r₁]`. Establish `e2 : T.annLogNorm q y = Real.log (T.annNorm ρ0 σ0 r₂ q)`. Rewrite using `[annLogNorm, T.annNormR_of_mem q r₂]`. Establish `e3 : T.annLogNorm q (a • x + b • y) = Real.log (T.annNorm ρ0 σ0 r q)`. Rewrite using `[annLogNorm, T.annNormR_of_mem q r]`.

Rewrite `e3` using `[smul_eq_mul, smul_eq_mul]`. Rewrite using `[e1, e2, e3]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem convexOn_annLogNorm (q : T.Ann ρ0 σ0) (hq : ∀ r, 0 < T.annNorm ρ0 σ0 r q) :
    ConvexOn ℝ (Set.Icc (Real.log σ0) (Real.log ρ0)) (T.annLogNorm q) := by
  refine ⟨convex_Icc _ _, fun x hx y hy a b ha hb hab => ?_⟩
  set r₁ : AnnRad ρ0 σ0 := ⟨Real.exp x, exp_mem_of_mem_Icc hx⟩
  set r₂ : AnnRad ρ0 σ0 := ⟨Real.exp y, exp_mem_of_mem_Icc hy⟩
  have hz : a • x + b • y ∈ Set.Icc (Real.log σ0) (Real.log ρ0) := (convex_Icc _ _) hx hy ha hb hab
  set r : AnnRad ρ0 σ0 := ⟨Real.exp (a • x + b • y), exp_mem_of_mem_Icc hz⟩
  have hr : (r : ℝ) = (r₁ : ℝ) ^ (1 - b) * (r₂ : ℝ) ^ b := by
    show Real.exp (a • x + b • y) = Real.exp x ^ (1 - b) * Real.exp y ^ b
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, smul_eq_mul, smul_eq_mul,
      show 1 - b = a by linarith]
    ring_nf
  have hi := T.annNorm_interp_le r₁ r₂ r (by linarith) (by linarith) hr q
  have h1 := hq r₁
  have h2 := hq r₂
  have hlog := Real.log_le_log (hq r) hi
  rw [Real.log_mul (Real.rpow_pos_of_pos h1 _).ne' (Real.rpow_pos_of_pos h2 _).ne',
    Real.log_rpow h1, Real.log_rpow h2, show 1 - b = a by linarith] at hlog
  simp only [smul_eq_mul]
  have e1 : T.annLogNorm q x = Real.log (T.annNorm ρ0 σ0 r₁ q) := by
    rw [annLogNorm, T.annNormR_of_mem q r₁]
  have e2 : T.annLogNorm q y = Real.log (T.annNorm ρ0 σ0 r₂ q) := by
    rw [annLogNorm, T.annNormR_of_mem q r₂]
  have e3 : T.annLogNorm q (a • x + b • y) = Real.log (T.annNorm ρ0 σ0 r q) := by
    rw [annLogNorm, T.annNormR_of_mem q r]
  rw [smul_eq_mul, smul_eq_mul] at e3
  rw [e1, e2, e3]
  linarith

/- English proof (translation)
Break down `eq_or_lt_of_le hbc with h | h` into its components or cases. Substitute `h` using the available equality. Conclude with `hf.slope_mono_adjacent ha hd hab hcd`. Conclude with `(hf.slope_mono_adjacent ha hc hab h).trans (hf.slope_mono_adjacent hb hd h hcd)`.
-/
theorem slope_le_slope_of_convexOn {f : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f) {a b c d : ℝ}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s) (hab : a < b) (hbc : b ≤ c) (hcd : c < d) :
    (f b - f a) / (b - a) ≤ (f d - f c) / (d - c) := by
  rcases eq_or_lt_of_le hbc with h | h
  · subst h
    exact hf.slope_mono_adjacent ha hd hab hcd
  · exact (hf.slope_mono_adjacent ha hc hab h).trans (hf.slope_mono_adjacent hb hd h hcd)

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp [annNorm_one]`. Consider the case `cons P l ih => rw [List.map_cons, List.prod_cons, annNorm_mul, T.annNorm_ξAnn P.2, ih, List.map_cons, List.prod_cons]`.
-/
theorem annNorm_list_prod_ξAnn (l : List T.Pt) (r : AnnRad ρ0 σ0) :
    T.annNorm ρ0 σ0 r (l.map fun P => T.ξAnn P.1).prod =
      (l.map fun P => max (T.ptRad P.1) (r : ℝ)).prod := by
  induction l with
  | nil => simp [annNorm_one]
  | cons P l ih => rw [List.map_cons, List.prod_cons, annNorm_mul, T.annNorm_ξAnn P.2, ih,
      List.map_cons, List.prod_cons]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons P l ih`. Rewrite using `[List.map_cons, List.prod_cons, max_eq_left (h P List.mem_cons_self), ih fun Q hQ => h Q (List.mem_cons_of_mem _ hQ)]`. Both sides reduce to the same expression.
-/
theorem list_prod_max_eq_left (l : List T.Pt) {s : ℝ} (h : ∀ P ∈ l, s ≤ T.ptRad P.1) :
    (l.map fun P => max (T.ptRad P.1) s).prod = (l.map fun P => T.ptRad P.1).prod := by
  induction l with
  | nil => rfl
  | cons P l ih =>
    rw [List.map_cons, List.prod_cons, max_eq_left (h P List.mem_cons_self),
      ih fun Q hQ => h Q (List.mem_cons_of_mem _ hQ)]; rfl

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons P l ih`. Rewrite using `[List.map_cons, List.prod_cons, max_eq_right (h P List.mem_cons_self), ih fun Q hQ => h Q (List.mem_cons_of_mem _ hQ), List.length_cons, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem list_prod_max_eq_right (l : List T.Pt) {s : ℝ} (h : ∀ P ∈ l, T.ptRad P.1 ≤ s) :
    (l.map fun P => max (T.ptRad P.1) s).prod = s ^ l.length := by
  induction l with
  | nil => simp
  | cons P l ih =>
    rw [List.map_cons, List.prod_cons, max_eq_right (h P List.mem_cons_self),
      ih fun Q hQ => h Q (List.mem_cons_of_mem _ hQ), List.length_cons, pow_succ]; ring

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons P l ih => rw [List.map_cons, List.prod_cons]`. Conclude with `mul_pos (T.ptRad_pos' P.2) ih`.
-/
theorem list_prod_ptRad_pos (l : List T.Pt) : 0 < (l.map fun P => T.ptRad P.1).prod := by
  induction l with
  | nil => simp
  | cons P l ih => rw [List.map_cons, List.prod_cons]; exact mul_pos (T.ptRad_pos' P.2) ih

/- English proof (translation)
Take `⟨q, hq⟩` from `hdvd`. Use `set P := (l.map fun P => T.ξAnn P.1).prod`. Establish `hpos : ∀ r : AnnRad ρ0 σ0, 0 < T.annNorm ρ0 σ0 r P` using `fun r => by`. Rewrite using `[T.annNorm_list_prod_ξAnn]`. Conclude with `List.prod_pos fun x hx => by`.

Take `⟨Q, -, rfl⟩` from `List.mem_map.1 hx`. Conclude with `lt_of_lt_of_le (T.ptRad_pos' Q.2) (le_max_left _ _)`. Establish `hqpos : ∀ r, 0 < T.annNorm ρ0 σ0 r q` using `fun r => by`. Establish `h` using `hw r`. Rewrite `h` using `[hq, annNorm_mul]`.

Conclude with `pos_of_mul_pos_right h (hpos r).le`. Establish `hnw : ∀ r : AnnRad ρ0 σ0, Real.log (T.annNorm ρ0 σ0 r w) = Real.log (T.annNorm ρ0 σ0 r P) + Real.log (T.annNorm ρ0 σ0 r q)` using `fun r => by`. Rewrite using `[hq, annNorm_mul, Real.log_mul (hpos r).ne' (hqpos r).ne']`. Establish `hPa : T.annNorm ρ0 σ0 a P = (l.map fun P => T.ptRad P.1).prod`. Rewrite using `[T.annNorm_list_prod_ξAnn, T.list_prod_max_eq_left l fun Q hQ => hab.le.trans (hl Q hQ).1]`.

Establish `hPb : T.annNorm ρ0 σ0 b P = (l.map fun P => T.ptRad P.1).prod`. Rewrite using `[T.annNorm_list_prod_ξAnn, T.list_prod_max_eq_left l fun Q hQ => (hl Q hQ).1]`. Establish `hPc : T.annNorm ρ0 σ0 c P = (c : ℝ) ^ l.length`. Rewrite using `[T.annNorm_list_prod_ξAnn, T.list_prod_max_eq_right l fun Q hQ => (hl Q hQ).2]`. Establish `hPd : T.annNorm ρ0 σ0 d P = (d : ℝ) ^ l.length`.

Rewrite using `[T.annNorm_list_prod_ξAnn, T.list_prod_max_eq_right l fun Q hQ => (hl Q hQ).2.trans hcd.le]`. Establish `hmem : ∀ r : AnnRad ρ0 σ0, Real.log r ∈ Set.Icc (Real.log σ0) (Real.log ρ0)` using `fun r => ⟨Real.log_le_log σ0.2.1 r.2.1, Real.log_le_log (σ0.2.1.trans_le r.2.1) r.2.2⟩`. Establish `hc0 : (0 : ℝ) < c` using `σ0.2.1.trans_le c.2.1`. Establish `hd0 : (0 : ℝ) < d` using `σ0.2.1.trans_le d.2.1`. Establish `ha0 : (0 : ℝ) < a` using `σ0.2.1.trans_le a.2.1`.

Establish `hb0 : (0 : ℝ) < b` using `σ0.2.1.trans_le b.2.1`. Establish `hlab : Real.log a < Real.log b` using `Real.log_lt_log ha0 hab`. Establish `hlbc : Real.log b ≤ Real.log c` using `Real.log_le_log hb0 hbc`. Establish `hlcd : Real.log c < Real.log d` using `Real.log_lt_log hc0 hcd`. Establish `key` using `slope_le_slope_of_convexOn (T.convexOn_annLogNorm q hqpos) (hmem a) (hmem b) (hmem c) (hmem d) hlab hlbc hlcd`.

Rewrite `key` using `[T.annLogNorm_of_mem, T.annLogNorm_of_mem, T.annLogNorm_of_mem, T.annLogNorm_of_mem]`. Rewrite using `[hnw a, hnw b, hnw c, hnw d, hPa, hPb, hPc, hPd, Real.log_pow, Real.log_pow]`. Establish `e1 : (Real.log (l.map fun P => T.ptRad P.1).prod + Real.log (T.annNorm ρ0 σ0 b q) - (Real.log (l.map fun P => T.ptRad P.1).prod + Real.log (T.annNorm ρ0 σ0 a q))) / (Real.log b - Real.log a) = (Real.log (T.annNorm ρ0 σ0 b q) - Real.log (T.annNorm ρ0 σ0 a q)) / (Real.log b - Real. …`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `e2 : ((l.length : ℝ) * Real.log d + Real.log (T.annNorm ρ0 σ0 d q) - ((l.length : ℝ) * Real.log c + Real.log (T.annNorm ρ0 σ0 c q))) / (Real.log d - Real.log c) = l.length + (Real.log (T.annNorm ρ0 σ0 d q) - Real.log (T.annNorm ρ0 σ0 c q)) / (Real.log d - Real.log c)`. Establish `hne : Real.log d - Real.log c ≠ 0` using `by linarith`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem length_le_of_prod_dvd (w : T.Ann ρ0 σ0) (hw : ∀ r, 0 < T.annNorm ρ0 σ0 r w)
    (a b c d : AnnRad ρ0 σ0) (hab : (a : ℝ) < b) (hbc : (b : ℝ) ≤ c) (hcd : (c : ℝ) < d)
    (l : List T.Pt) (hl : ∀ P ∈ l, (b : ℝ) ≤ T.ptRad P.1 ∧ T.ptRad P.1 ≤ c)
    (hdvd : (l.map fun P => T.ξAnn P.1).prod ∣ w) :
    (l.length : ℝ) ≤
      (Real.log (T.annNorm ρ0 σ0 d w) - Real.log (T.annNorm ρ0 σ0 c w)) / (Real.log d - Real.log c) -
      (Real.log (T.annNorm ρ0 σ0 b w) - Real.log (T.annNorm ρ0 σ0 a w)) / (Real.log b - Real.log a) := by
  obtain ⟨q, hq⟩ := hdvd
  set P := (l.map fun P => T.ξAnn P.1).prod
  have hpos : ∀ r : AnnRad ρ0 σ0, 0 < T.annNorm ρ0 σ0 r P := fun r => by
    rw [T.annNorm_list_prod_ξAnn]
    exact List.prod_pos fun x hx => by
      obtain ⟨Q, -, rfl⟩ := List.mem_map.1 hx
      exact lt_of_lt_of_le (T.ptRad_pos' Q.2) (le_max_left _ _)
  have hqpos : ∀ r, 0 < T.annNorm ρ0 σ0 r q := fun r => by
    have h := hw r
    rw [hq, annNorm_mul] at h
    exact pos_of_mul_pos_right h (hpos r).le
  have hnw : ∀ r : AnnRad ρ0 σ0, Real.log (T.annNorm ρ0 σ0 r w) =
      Real.log (T.annNorm ρ0 σ0 r P) + Real.log (T.annNorm ρ0 σ0 r q) := fun r => by
    rw [hq, annNorm_mul, Real.log_mul (hpos r).ne' (hqpos r).ne']
  have hPa : T.annNorm ρ0 σ0 a P = (l.map fun P => T.ptRad P.1).prod := by
    rw [T.annNorm_list_prod_ξAnn, T.list_prod_max_eq_left l fun Q hQ => hab.le.trans (hl Q hQ).1]
  have hPb : T.annNorm ρ0 σ0 b P = (l.map fun P => T.ptRad P.1).prod := by
    rw [T.annNorm_list_prod_ξAnn, T.list_prod_max_eq_left l fun Q hQ => (hl Q hQ).1]
  have hPc : T.annNorm ρ0 σ0 c P = (c : ℝ) ^ l.length := by
    rw [T.annNorm_list_prod_ξAnn, T.list_prod_max_eq_right l fun Q hQ => (hl Q hQ).2]
  have hPd : T.annNorm ρ0 σ0 d P = (d : ℝ) ^ l.length := by
    rw [T.annNorm_list_prod_ξAnn, T.list_prod_max_eq_right l fun Q hQ => (hl Q hQ).2.trans hcd.le]
  have hmem : ∀ r : AnnRad ρ0 σ0, Real.log r ∈ Set.Icc (Real.log σ0) (Real.log ρ0) := fun r =>
    ⟨Real.log_le_log σ0.2.1 r.2.1, Real.log_le_log (σ0.2.1.trans_le r.2.1) r.2.2⟩
  have hc0 : (0 : ℝ) < c := σ0.2.1.trans_le c.2.1
  have hd0 : (0 : ℝ) < d := σ0.2.1.trans_le d.2.1
  have ha0 : (0 : ℝ) < a := σ0.2.1.trans_le a.2.1
  have hb0 : (0 : ℝ) < b := σ0.2.1.trans_le b.2.1
  have hlab : Real.log a < Real.log b := Real.log_lt_log ha0 hab
  have hlbc : Real.log b ≤ Real.log c := Real.log_le_log hb0 hbc
  have hlcd : Real.log c < Real.log d := Real.log_lt_log hc0 hcd
  have key := slope_le_slope_of_convexOn (T.convexOn_annLogNorm q hqpos) (hmem a) (hmem b) (hmem c)
    (hmem d) hlab hlbc hlcd
  rw [T.annLogNorm_of_mem, T.annLogNorm_of_mem, T.annLogNorm_of_mem, T.annLogNorm_of_mem] at key
  rw [hnw a, hnw b, hnw c, hnw d, hPa, hPb, hPc, hPd, Real.log_pow, Real.log_pow]
  have e1 : (Real.log (l.map fun P => T.ptRad P.1).prod + Real.log (T.annNorm ρ0 σ0 b q) -
      (Real.log (l.map fun P => T.ptRad P.1).prod + Real.log (T.annNorm ρ0 σ0 a q))) /
      (Real.log b - Real.log a) =
      (Real.log (T.annNorm ρ0 σ0 b q) - Real.log (T.annNorm ρ0 σ0 a q)) / (Real.log b - Real.log a) := by
    congr 1; ring
  have e2 : ((l.length : ℝ) * Real.log d + Real.log (T.annNorm ρ0 σ0 d q) -
      ((l.length : ℝ) * Real.log c + Real.log (T.annNorm ρ0 σ0 c q))) / (Real.log d - Real.log c) =
      l.length + (Real.log (T.annNorm ρ0 σ0 d q) - Real.log (T.annNorm ρ0 σ0 c q)) /
        (Real.log d - Real.log c) := by
    have hne : Real.log d - Real.log c ≠ 0 := by linarith
    field_simp
    ring
  rw [e1, e2]
  linarith

end TeichLift

end GroundTheory.PAdicHodge
