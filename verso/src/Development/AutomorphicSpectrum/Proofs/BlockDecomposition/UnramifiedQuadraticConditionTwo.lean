import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.QuadAtOf

noncomputable section

namespace GlobalTheory.CompanionTheory.ValuationCompleteness

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gunr Filter Topology
open scoped TensorProduct

section Abstract

variable {K A : Type} [NormedField K] [CommRing A] [Algebra K A] {d : ℕ}
  (b : Module.Basis (Fin d) K A) (S : Subring A)

/- English proof (translation)
Establish `hpow : ∀ c : A, c * (algebraMap K A ϖ) ^ k = ϖ ^ k • c`. Introduce `c`. Rewrite using `[← map_pow, Algebra.smul_def, mul_comm]`. Establish `hcoe : ∀ c : S, ((c * (⟨_, hϖ⟩ : S) ^ k : S) : A) = ϖ ^ k • (c : A)`. Introduce `c`.

Rewrite using `[← hpow]`. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion. Introduce `ha i`. Rewrite `ha` using `[lev, Ideal.mem_span_singleton']`.

Take `⟨c, hc⟩` from `ha`. Establish `hc' : (a : A) = ϖ ^ k • (c : A)`. Rewrite using `[← hc, hcoe]`. Rewrite using `[hc', map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul, norm_pow]`. Establish `hci` using `(hS c).1 c.2 i`.

Combine the equalities or inequalities in the displayed calculation. Introduce `ha`. Rewrite using `[lev, Ideal.mem_span_singleton']`. Establish `hpos : 0 < ‖ϖ‖ ^ k` using `pow_pos (norm_pos_iff.mpr h0) k`. Establish `hcS : (ϖ ^ k)⁻¹ • (a : A) ∈ S`.

Rewrite using `[hS]`. Introduce `i`. Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul, norm_inv, norm_pow, inv_mul_le_iff₀ hpos, mul_one]`. Conclude with `ha i`. Use `⟨⟨_, hcS⟩, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hcoe]`. Express the relevant statement in the definitionally equal form `ϖ ^ k • ((ϖ ^ k)⁻¹ • (a : A)) = (a : A)`. Rewrite using `[smul_smul, mul_inv_cancel₀ (pow_ne_zero k h0), one_smul]`.
-/
theorem mem_lev_iff (hS : ∀ x, x ∈ S ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {ϖ : K} (h0 : ϖ ≠ 0)
    (hϖ : algebraMap K A ϖ ∈ S) (a : S) (k : ℕ) :
    a ∈ lev (⟨_, hϖ⟩ : S) k ↔ ∀ i, ‖b.repr (a : A) i‖ ≤ ‖ϖ‖ ^ k := by
  have hpow : ∀ c : A, c * (algebraMap K A ϖ) ^ k = ϖ ^ k • c := by
    intro c
    rw [← map_pow, Algebra.smul_def, mul_comm]
  have hcoe : ∀ c : S, ((c * (⟨_, hϖ⟩ : S) ^ k : S) : A) = ϖ ^ k • (c : A) := by
    intro c
    rw [← hpow]
    rfl
  constructor
  · intro ha i
    rw [lev, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, hc⟩ := ha
    have hc' : (a : A) = ϖ ^ k • (c : A) := by
      rw [← hc, hcoe]
    rw [hc', map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul, norm_pow]
    have hci := (hS c).1 c.2 i
    calc ‖ϖ‖ ^ k * ‖b.repr (c : A) i‖ ≤ ‖ϖ‖ ^ k * 1 := by gcongr
      _ = ‖ϖ‖ ^ k := mul_one _
  · intro ha
    rw [lev, Ideal.mem_span_singleton']
    have hpos : 0 < ‖ϖ‖ ^ k := pow_pos (norm_pos_iff.mpr h0) k
    have hcS : (ϖ ^ k)⁻¹ • (a : A) ∈ S := by
      rw [hS]
      intro i
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul, norm_inv, norm_pow,
        inv_mul_le_iff₀ hpos, mul_one]
      exact ha i
    refine ⟨⟨_, hcS⟩, ?_⟩
    apply Subtype.ext
    rw [hcoe]
    change ϖ ^ k • ((ϖ ^ k)⁻¹ • (a : A)) = (a : A)
    rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero k h0), one_smul]

/- English proof (translation)
Establish `hi : ∀ i, b.repr (a : A) i = 0`. Introduce `i`. Establish `hle : ∀ k : ℕ, ‖b.repr (a : A) i‖ ≤ ‖ϖ‖ ^ k` using `fun k => (mem_lev_iff b S hS h0 hϖ a k).1 (h k) i`. Establish `ht : Tendsto (fun k : ℕ => ‖ϖ‖ ^ k) atTop (𝓝 0)` using `tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h1`. Conclude with `norm_le_zero_iff.mp (ge_of_tendsto' ht hle)`.

Establish `hr : b.repr (a : A) = 0`. Use extensionality with `i`. Conclude with `hi i`. Establish `ha : (a : A) = 0` using `(LinearEquiv.map_eq_zero_iff b.repr).mp hr`. Conclude with `ha` after adjusting the coercions.
-/
theorem separated (hS : ∀ x, x ∈ S ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {ϖ : K} (h0 : ϖ ≠ 0) (h1 : ‖ϖ‖ < 1)
    (hϖ : algebraMap K A ϖ ∈ S) (a : S) (h : ∀ k, a ∈ lev (⟨_, hϖ⟩ : S) k) : a = 0 := by
  have hi : ∀ i, b.repr (a : A) i = 0 := by
    intro i
    have hle : ∀ k : ℕ, ‖b.repr (a : A) i‖ ≤ ‖ϖ‖ ^ k :=
      fun k => (mem_lev_iff b S hS h0 hϖ a k).1 (h k) i
    have ht : Tendsto (fun k : ℕ => ‖ϖ‖ ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h1
    exact norm_le_zero_iff.mp (ge_of_tendsto' ht hle)
  have hr : b.repr (a : A) = 0 := by
    ext i
    exact hi i
  have ha : (a : A) = 0 := (LinearEquiv.map_eq_zero_iff b.repr).mp hr
  exact_mod_cast ha

variable [CompleteSpace K] [IsUltrametricDist K]

/- English proof (translation)
Use `set x : ℕ → Fin d → K := fun k i => b.repr (f k : A) i with hx`. Establish `hstep : ∀ k i, ‖x (k + 1) i - x k i‖ ≤ ‖ϖ‖ ^ k`. Introduce `k i`. Use `(mem_lev_iff b S hS h0 hϖ _ k).1 (hf k) i` as an intermediate fact. Simplify `this` using `[hx, map_sub]`.

Establish `hn0 : 0 ≤ ‖ϖ‖` using `norm_nonneg _`. Establish `hle1 : ‖ϖ‖ ≤ 1` using `le_of_lt h1`. Establish `hfar : ∀ i k m, k ≤ m → ‖x m i - x k i‖ ≤ ‖ϖ‖ ^ k`. Introduce `i k m hkm`. Proceed by induction on `m, hkm using Nat.le_induction with`.

Consider the case `base => simp`. Consider the case `succ m hkm ih`. Establish `e : x (m + 1) i - x k i = (x (m + 1) i - x m i) + (x m i - x k i)` using `by ring`. Rewrite using `[e]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)` and prove the remaining obligations.

Conclude with `(hstep m i).trans (pow_le_pow_of_le_one hn0 hle1 hkm)`. Establish `hcau : ∀ i, CauchySeq (fun k => x k i)`. Introduce `i`. Use `cauchySeq_of_le_geometric ‖ϖ‖ 1 h1 (fun n => ?_)` and prove the remaining obligations. Rewrite using `[dist_eq_norm, ← norm_neg, neg_sub, one_mul]`.

Conclude with `hstep n i`. Use `choose c hc using fun i => cauchySeq_tendsto_of_complete (hcau i)`. Establish `hbd : ∀ i k, ‖c i - x k i‖ ≤ ‖ϖ‖ ^ k`. Introduce `i k`. Establish `ht : Tendsto (fun m => ‖x m i - x k i‖) atTop (𝓝 ‖c i - x k i‖)` using `((hc i).sub_const _).norm`.

Use `le_of_tendsto ht ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop k] with m hm`. Conclude with `hfar i k m hm`. Use `set aA : A := b.equivFun.symm c with haA`. Establish `hrep : ∀ i, b.repr aA i = c i`.

Introduce `i`. Rewrite using `[← b.equivFun_apply, haA, LinearEquiv.apply_symm_apply]`. Establish `hmem : aA ∈ S`. Rewrite using `[hS]`. Introduce `i`.

Rewrite using `[hrep]`. Establish `e : c i = (c i - x 0 i) + x 0 i` using `by ring`. Rewrite using `[e]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Simplify using `using hbd i 0`.

Conclude with `(hS _).1 (f 0).2 i`. Use `⟨⟨aA, hmem⟩, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_lev_iff b S hS h0 hϖ]`. Introduce `i`. Establish `e : ((⟨aA, hmem⟩ - f k : S) : A) = aA - (f k : A)` using `rfl`.

Rewrite using `[e, map_sub, Finsupp.sub_apply, hrep]`. Conclude with `hbd i k`.
-/
theorem complete (hS : ∀ x, x ∈ S ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {ϖ : K} (h0 : ϖ ≠ 0) (h1 : ‖ϖ‖ < 1)
    (hϖ : algebraMap K A ϖ ∈ S) (f : ℕ → S) (hf : ∀ k, f (k + 1) - f k ∈ lev (⟨_, hϖ⟩ : S) k) :
    ∃ a, ∀ k, a - f k ∈ lev (⟨_, hϖ⟩ : S) k := by
  set x : ℕ → Fin d → K := fun k i => b.repr (f k : A) i with hx
  have hstep : ∀ k i, ‖x (k + 1) i - x k i‖ ≤ ‖ϖ‖ ^ k := by
    intro k i
    have := (mem_lev_iff b S hS h0 hϖ _ k).1 (hf k) i
    simpa [hx, map_sub] using this
  have hn0 : 0 ≤ ‖ϖ‖ := norm_nonneg _
  have hle1 : ‖ϖ‖ ≤ 1 := le_of_lt h1
  have hfar : ∀ i k m, k ≤ m → ‖x m i - x k i‖ ≤ ‖ϖ‖ ^ k := by
    intro i k m hkm
    induction m, hkm using Nat.le_induction with
    | base => simp
    | succ m hkm ih =>
      have e : x (m + 1) i - x k i = (x (m + 1) i - x m i) + (x m i - x k i) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
      exact (hstep m i).trans (pow_le_pow_of_le_one hn0 hle1 hkm)
  have hcau : ∀ i, CauchySeq (fun k => x k i) := by
    intro i
    refine cauchySeq_of_le_geometric ‖ϖ‖ 1 h1 (fun n => ?_)
    rw [dist_eq_norm, ← norm_neg, neg_sub, one_mul]
    exact hstep n i
  choose c hc using fun i => cauchySeq_tendsto_of_complete (hcau i)
  have hbd : ∀ i k, ‖c i - x k i‖ ≤ ‖ϖ‖ ^ k := by
    intro i k
    have ht : Tendsto (fun m => ‖x m i - x k i‖) atTop (𝓝 ‖c i - x k i‖) :=
      ((hc i).sub_const _).norm
    refine le_of_tendsto ht ?_
    filter_upwards [eventually_ge_atTop k] with m hm
    exact hfar i k m hm
  set aA : A := b.equivFun.symm c with haA
  have hrep : ∀ i, b.repr aA i = c i := by
    intro i
    rw [← b.equivFun_apply, haA, LinearEquiv.apply_symm_apply]
  have hmem : aA ∈ S := by
    rw [hS]
    intro i
    rw [hrep]
    have e : c i = (c i - x 0 i) + x 0 i := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · simpa using hbd i 0
    · exact (hS _).1 (f 0).2 i
  refine ⟨⟨aA, hmem⟩, fun k => ?_⟩
  rw [mem_lev_iff b S hS h0 hϖ]
  intro i
  have e : ((⟨aA, hmem⟩ - f k : S) : A) = aA - (f k : A) := rfl
  rw [e, map_sub, Finsupp.sub_apply, hrep]
  exact hbd i k

end Abstract

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d bs v S σS ϖ hQ hϖ`. Take `⟨-, -, hSR, -, h0, h1, -, -⟩` from `hQ`. Establish `hS : ∀ x, x ∈ S ↔ ∀ i, ‖(Algebra.TensorProduct.basis (Fv F v) bs).repr x i‖ ≤ 1`. Introduce `x`. Rewrite using `[← SetLike.mem_coe, hSR]`.

Conclude with `forall_congr' fun i => (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).trans Valued.toNormedField.norm_le_one_iff.symm`. Conclude with `⟨fun a ha => separated _ S hS h0 h1 hϖ a ha, fun f hf => complete _ S hS h0 h1 hϖ f hf⟩`.
-/
theorem q2 : Q2 := by
  intro F E _ _ _ _ _ σ d bs v S σS ϖ hQ hϖ
  obtain ⟨-, -, hSR, -, h0, h1, -, -⟩ := hQ
  have hS : ∀ x, x ∈ S ↔ ∀ i, ‖(Algebra.TensorProduct.basis (Fv F v) bs).repr x i‖ ≤ 1 := by
    intro x
    rw [← SetLike.mem_coe, hSR]
    exact forall_congr' fun i =>
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).trans
        Valued.toNormedField.norm_le_one_iff.symm
  exact ⟨fun a ha => separated _ S hS h0 h1 hϖ a ha, fun f hf => complete _ S hS h0 h1 hϖ f hf⟩

end GlobalTheory.CompanionTheory.ValuationCompleteness

end
