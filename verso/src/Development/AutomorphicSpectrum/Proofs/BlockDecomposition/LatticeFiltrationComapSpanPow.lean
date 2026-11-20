import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeSubIffSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerFiltrationSpanPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeXiMulDpowSucc

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatPdpEq

section
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

def dq (i : ℕ) : ℚ := ((i.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ i

/- English proof (translation)
Establish `h1 : (l : ℚ) ≠ 0` using `by exact_mod_cast hl`. Establish `h2 : (i.factorial : ℚ) ≠ 0` using `by exact_mod_cast i.factorial_ne_zero`. Unfold `dq`. Check the signs of the components of the expression.
-/
theorem dq_ne_zero (hl : l ≠ 0) (i : ℕ) : dq l M i ≠ 0 := by
  have h1 : (l : ℚ) ≠ 0 := by exact_mod_cast hl
  have h2 : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  unfold dq
  positivity

/- English proof (translation)
Unfold `Lat.dpE Lat.η dq`. Rewrite using `[smul_pow, smul_smul]`.
-/
theorem dpE_eq_smul (i : ℕ) : Lat.dpE f ξ l M i = dq l M i • f ξ ^ i := by
  unfold Lat.dpE Lat.η dq
  rw [smul_pow, smul_smul]

/- English proof (translation)
Rewrite using `[dpE_eq_smul, ← Nat.add_sub_of_le hi, pow_add, hm, zero_mul, smul_zero]`.
-/
theorem dpE_eq_zero {m i : ℕ} (hm : f ξ ^ m = 0) (hi : m ≤ i) : Lat.dpE f ξ l M i = 0 := by
  rw [dpE_eq_smul, ← Nat.add_sub_of_le hi, pow_add, hm, zero_mul, smul_zero]

/- English proof (translation)
Rewrite using `[dpE_eq_smul, Algebra.smul_def]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton.2 (pow_dvd_pow _ hi))`.
-/
theorem dpE_mem_span {k i : ℕ} (hi : k ≤ i) : Lat.dpE f ξ l M i ∈ Ideal.span {f ξ ^ k} := by
  rw [dpE_eq_smul, Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton.2 (pow_dvd_pow _ hi))

/- English proof (translation)
The claim follows from `Subtype.property (p := fun y => y ∈ Lat.sub f ξ l M) x`.
-/
theorem ι_mem (x : Lat.A f ξ l M) : Lat.ι f ξ l M x ∈ Lat.sub f ξ l M :=
  Subtype.property (p := fun y => y ∈ Lat.sub f ξ l M) x

/- English proof (translation)
Use `show Lat.dpE f ξ l M 1 ∈ Lat.IB f ξ`. Use `dpE_mem_span f ξ l M (k := 1) le_rfl` as an intermediate fact. Simplify `this` using `[Lat.IB]`.
-/
theorem dpA_one_mem : Lat.dpA f ξ l M 1 ∈ Lat.I f ξ l M := by
  show Lat.dpE f ξ l M 1 ∈ Lat.IB f ξ
  have := dpE_mem_span f ξ l M (k := 1) le_rfl
  simpa [Lat.IB] using this

/- English proof (translation)
Apply `Lat.ι_injective f ξ l M` to reduce the goal to its premises. Rewrite using `[Lat.ι_γ f ξ l M hc (dpA_one_mem f ξ l M), Lat.ι_dpA, Lat.ι_dpA]`. Establish `hy : Lat.dpE f ξ l M 1 ∈ Lat.IB f ξ` using `dpA_one_mem f ξ l M`. Rewrite using `[RatAlgebra.dpow_eq_inv_fact_smul _ (Lat.γB f ξ) hy, Ring.inverse_eq_inv']`. Simplify using `[Lat.dpE]`.
-/
theorem dpow_dpA (hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ)) (i : ℕ) :
    (Lat.γ f ξ l M hc).dpow i (Lat.dpA f ξ l M 1) = Lat.dpA f ξ l M i := by
  apply Lat.ι_injective f ξ l M
  rw [Lat.ι_γ f ξ l M hc (dpA_one_mem f ξ l M), Lat.ι_dpA, Lat.ι_dpA]
  have hy : Lat.dpE f ξ l M 1 ∈ Lat.IB f ξ := dpA_one_mem f ξ l M
  rw [RatAlgebra.dpow_eq_inv_fact_smul _ (Lat.γB f ξ) hy, Ring.inverse_eq_inv']
  simp [Lat.dpE]

/- English proof (translation)
Use `Ideal.subset_span ⟨[(i, Lat.dpA f ξ l M 1)], ?_, by simpa using hi, ?_⟩` and prove the remaining obligations. Introduce `q hq`. Rewrite `hq` using `[List.mem_singleton]`. Substitute `hq` using the available equality. Conclude with `dpA_one_mem f ξ l M`.

Simplify using `[dpow_dpA f ξ l M hc i]`.
-/
theorem dpA_mem_pdP (hl : l ≠ 0) (hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ)) {r i : ℕ} (hi : r ≤ i) :
    Lat.dpA f ξ l M i ∈ pdP (Lat.γ f ξ l M hc) r := by
  refine Ideal.subset_span ⟨[(i, Lat.dpA f ξ l M 1)], ?_, by simpa using hi, ?_⟩
  · intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact dpA_one_mem f ξ l M
  · simp [dpow_dpA f ξ l M hc i]

variable {f ξ l M}

/- English proof (translation)
Rewrite `hy` using `[Finset.sum_eq_sum_Ico_succ_bot (by omega)]`. Establish `ht : ∑ i ∈ Finset.Ico (j + 1) (m + 1), f (c i) * Lat.dpE f ξ l M i ∈ Ideal.span {f ξ ^ (j + 1)}` using `Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ (dpE_mem_span f ξ l M (Finset.mem_Ico.1 hi).1)`. Establish `hh` using `(Ideal.add_mem_iff_left _ ht).1 hy`. Take `⟨b, hb⟩` from `Ideal.mem_span_singleton.1 hh`. Use `h.gr j hj (c j) ((dq l M j)⁻¹ • b) ?_` and prove the remaining obligations.

Rewrite `hb` using `[dpE_eq_smul, mul_smul_comm]`. Rewrite using `[mul_smul_comm, ← hb, smul_smul, inv_mul_cancel₀ (dq_ne_zero l M hl j), one_smul]`.
-/
theorem coeff_dvd {m j : ℕ} (h : Lat.Hyp f ξ l m) (hl : l ≠ 0) (hj : j < m) (c : ℕ → W)
    (hy : ∑ i ∈ Finset.Ico j (m + 1), f (c i) * Lat.dpE f ξ l M i ∈ Ideal.span {f ξ ^ (j + 1)}) :
    ξ ∣ c j := by
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)] at hy
  have ht : ∑ i ∈ Finset.Ico (j + 1) (m + 1), f (c i) * Lat.dpE f ξ l M i ∈ Ideal.span {f ξ ^ (j + 1)} :=
    Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ (dpE_mem_span f ξ l M (Finset.mem_Ico.1 hi).1)
  have hh := (Ideal.add_mem_iff_left _ ht).1 hy
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 hh
  refine h.gr j hj (c j) ((dq l M j)⁻¹ • b) ?_
  rw [dpE_eq_smul, mul_smul_comm] at hb
  rw [mul_smul_comm, ← hb, smul_smul, inv_mul_cancel₀ (dq_ne_zero l M hl j), one_smul]

/- English proof (translation)
Take `⟨d, hd⟩` from `coeff_dvd h hl hj c (M := M) (e ▸ hy)`. Use `⟨Function.update c (j + 1) (c (j + 1) + d * ((l : W) ^ M * ((j : W) + 1))), ?_⟩` and prove the remaining obligations. Rewrite using `[e, Finset.sum_eq_sum_Ico_succ_bot (by omega), Finset.sum_eq_sum_Ico_succ_bot (a := j + 1) (by omega), Finset.sum_eq_sum_Ico_succ_bot (a := j + 1) (by omega)]`. Establish `hs : ∑ i ∈ Finset.Ico (j + 1 + 1) (m + 1), f (Function.update c (j + 1) (c (j + 1) + d * ((l : W) ^ M * ((j : W) + 1))) i) * Lat.dpE f ξ l M i = ∑ i ∈ Finset.Ico (j + 1 + 1) (m + 1), f (c i) * Lat.dpE f ξ l M i`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations.

Rewrite using `[Function.update_of_ne (by have := (Finset.mem_Ico.1 hi).1; omega)]`. Rewrite using `[hs, Function.update_self, hd, map_mul, mul_assoc, mul_left_comm (f ξ) (f d), GlobalTheory.CompanionTheory.LatDp.mul_divPow_eq f ξ l M hl j]`. Simplify using `only [map_add, map_mul, map_pow, map_natCast, map_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem push {m j : ℕ} (h : Lat.Hyp f ξ l m) (hl : l ≠ 0) (hj : j < m) (c : ℕ → W) {y : B}
    (e : y = ∑ i ∈ Finset.Ico j (m + 1), f (c i) * Lat.dpE f ξ l M i)
    (hy : y ∈ Ideal.span {f ξ ^ (j + 1)}) :
    ∃ c' : ℕ → W, y = ∑ i ∈ Finset.Ico (j + 1) (m + 1), f (c' i) * Lat.dpE f ξ l M i := by
  obtain ⟨d, hd⟩ := coeff_dvd h hl hj c (M := M) (e ▸ hy)
  refine ⟨Function.update c (j + 1) (c (j + 1) + d * ((l : W) ^ M * ((j : W) + 1))), ?_⟩
  rw [e, Finset.sum_eq_sum_Ico_succ_bot (by omega), Finset.sum_eq_sum_Ico_succ_bot (a := j + 1) (by omega),
    Finset.sum_eq_sum_Ico_succ_bot (a := j + 1) (by omega)]
  have hs : ∑ i ∈ Finset.Ico (j + 1 + 1) (m + 1), f (Function.update c (j + 1)
      (c (j + 1) + d * ((l : W) ^ M * ((j : W) + 1))) i) * Lat.dpE f ξ l M i =
      ∑ i ∈ Finset.Ico (j + 1 + 1) (m + 1), f (c i) * Lat.dpE f ξ l M i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (by have := (Finset.mem_Ico.1 hi).1; omega)]
  rw [hs, Function.update_self, hd, map_mul, mul_assoc, mul_left_comm (f ξ) (f d), GlobalTheory.CompanionTheory.LatDp.mul_divPow_eq f ξ l M hl j]
  simp only [map_add, map_mul, map_pow, map_natCast, map_one]
  ring

/- English proof (translation)
Take `⟨n, c, rfl⟩` from `(GlobalTheory.CompanionTheory.LatSpan.mem_sub_iff f ξ l M y).1 hy`. Use `⟨fun i => if h : i < n then c ⟨i, h⟩ else 0, ?_⟩` and prove the remaining obligations. Establish `h1 : ∑ i : Fin n, f (c i) * Lat.dpE f ξ l M i = ∑ i ∈ Finset.range n, f (if h : i < n then c ⟨i, h⟩ else 0) * Lat.dpE f ξ l M i`. Rewrite using `[← Fin.sum_univ_eq_sum_range (fun i => f (if h : i < n then c ⟨i, h⟩ else 0) * Lat.dpE f ξ l M i) n]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules. Rewrite using `[h1, Nat.Ico_zero_eq_range]`. Establish `h2` using `Finset.sum_subset (s₁ := Finset.range n) (s₂ := Finset.range (n + m + 1)) (f := fun i => f (if h : i < n then c ⟨i, h⟩ else 0) * Lat.dpE f ξ l M i) (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega) (fun i _ hi => by simp only [Finset.mem_range] at hi; simp [hi])`. Establish `h3` using `Finset.sum_subset (s₁ := Finset.range (m + 1)) (s₂ := Finset.range (n + m + 1)) (f := fun i => f (if h : i < n then c ⟨i, h⟩ else 0) * Lat.dpE f ξ l M i) (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega) (fun i _ hi => by`. Simplify using `only [Finset.mem_range] at hi`.

Simplify using `only [dpE_eq_zero f ξ l M hm (show m ≤ i by omega), mul_zero])`. Conclude with `h2.trans h3.symm`.
-/
theorem exists_rep {m : ℕ} (hm : f ξ ^ m = 0) {y : B} (hy : y ∈ Lat.sub f ξ l M) :
    ∃ c : ℕ → W, y = ∑ i ∈ Finset.Ico 0 (m + 1), f (c i) * Lat.dpE f ξ l M i := by
  obtain ⟨n, c, rfl⟩ := (GlobalTheory.CompanionTheory.LatSpan.mem_sub_iff f ξ l M y).1 hy
  refine ⟨fun i => if h : i < n then c ⟨i, h⟩ else 0, ?_⟩
  have h1 : ∑ i : Fin n, f (c i) * Lat.dpE f ξ l M i =
      ∑ i ∈ Finset.range n, f (if h : i < n then c ⟨i, h⟩ else 0) * Lat.dpE f ξ l M i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => f (if h : i < n then c ⟨i, h⟩ else 0) * Lat.dpE f ξ l M i) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  rw [h1, Nat.Ico_zero_eq_range]
  have h2 := Finset.sum_subset (s₁ := Finset.range n) (s₂ := Finset.range (n + m + 1))
    (f := fun i => f (if h : i < n then c ⟨i, h⟩ else 0) * Lat.dpE f ξ l M i)
    (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)
    (fun i _ hi => by simp only [Finset.mem_range] at hi; simp [hi])
  have h3 := Finset.sum_subset (s₁ := Finset.range (m + 1)) (s₂ := Finset.range (n + m + 1))
    (f := fun i => f (if h : i < n then c ⟨i, h⟩ else 0) * Lat.dpE f ξ l M i)
    (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)
    (fun i _ hi => by
      simp only [Finset.mem_range] at hi
      simp only [dpE_eq_zero f ξ l M hm (show m ≤ i by omega), mul_zero])
  exact h2.trans h3.symm

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => exact exists_rep h.nil hy`. Consider the case `succ j ih`. Take `⟨c, e⟩` from `ih (by omega) (by omega)`. Establish `hle : Ideal.span {f ξ ^ r} ≤ Ideal.span {f ξ ^ (j + 1)}` using `Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hjr)`.

Conclude with `push h hl (by omega) c e (hle hr)`.
-/
theorem exists_rep_high {m r : ℕ} (h : Lat.Hyp f ξ l m) (hl : l ≠ 0) {y : B} (hy : y ∈ Lat.sub f ξ l M)
    (hr : y ∈ Ideal.span {f ξ ^ r}) (j : ℕ) (hjr : j ≤ r) (hjm : j ≤ m) :
    ∃ c : ℕ → W, y = ∑ i ∈ Finset.Ico j (m + 1), f (c i) * Lat.dpE f ξ l M i := by
  induction j with
  | zero => exact exists_rep h.nil hy
  | succ j ih =>
    obtain ⟨c, e⟩ := ih (by omega) (by omega)
    have hle : Ideal.span {f ξ ^ r} ≤ Ideal.span {f ξ ^ (j + 1)} :=
      Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hjr)
    exact push h hl (by omega) c e (hle hr)

end

/- English proof (translation)
Introduce `W B _ _ _ f ξ l M m h hc r`. Establish `hl : l ≠ 0` using `fun e => h.l0 (by simp [e])`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Establish `hdp : IsDPMorphism (Lat.γ f ξ l M hc) (Lat.γB f ξ) (Lat.ι f ξ l M)` using `⟨Ideal.map_le_iff_le_comap.2 le_rfl, fun {n} a ha => (Lat.ι_γ f ξ l M hc ha).symm⟩`.

Use `dividedPowerFiltration_map hdp r hx` as an intermediate fact. Rewrite `this` using `[GlobalTheory.CompanionTheory.DPFiltration.pdP_γB f ξ r]`. Then use the resulting hypothesis. Introduce `x hx`. Take `⟨c, e⟩` from `exists_rep_high h hl (ι_mem f ξ l M x) hx (min r m) (by omega) (by omega)`. Establish `hx' : x = ∑ i ∈ Finset.Ico (min r m) (m + 1), Lat.ofW f ξ l M (c i) * Lat.dpA f ξ l M i`.

Apply `Lat.ι_injective f ξ l M` to reduce the goal to its premises. Rewrite using `[e, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, Lat.ι_ofW, Lat.ι_dpA]`. Rewrite using `[hx']`.

Use `Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ ?_` and prove the remaining obligations. Take `⟨h1, h2⟩` from `Finset.mem_Ico.1 hi`. Distinguish the cases in `hir : r ≤ i`. Conclude with `dpA_mem_pdP f ξ l M hl hc hir`. Establish `: Lat.dpA f ξ l M i = 0`.

Apply `Lat.ι_injective f ξ l M` to reduce the goal to its premises. Rewrite using `[Lat.ι_dpA, map_zero]`. Conclude with `dpE_eq_zero f ξ l M h.nil (by omega)`. Rewrite using `[this]`. Conclude with `Ideal.zero_mem _`.
-/
theorem dividedPowerFiltration_eq : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
    Lat.Hyp f ξ l m → ∀ hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ), ∀ r : ℕ,
    pdP (Lat.γ f ξ l M hc) r = (Ideal.span {f ξ ^ r}).comap (Lat.ι f ξ l M) := by
  intro W B _ _ _ f ξ l M m h hc r
  have hl : l ≠ 0 := fun e => h.l0 (by simp [e])
  apply le_antisymm
  · intro x hx
    have hdp : IsDPMorphism (Lat.γ f ξ l M hc) (Lat.γB f ξ) (Lat.ι f ξ l M) :=
      ⟨Ideal.map_le_iff_le_comap.2 le_rfl, fun {n} a ha => (Lat.ι_γ f ξ l M hc ha).symm⟩
    have := dividedPowerFiltration_map hdp r hx
    rwa [GlobalTheory.CompanionTheory.DPFiltration.pdP_γB f ξ r] at this
  · intro x hx
    obtain ⟨c, e⟩ := exists_rep_high h hl (ι_mem f ξ l M x) hx (min r m) (by omega) (by omega)
    have hx' : x = ∑ i ∈ Finset.Ico (min r m) (m + 1), Lat.ofW f ξ l M (c i) * Lat.dpA f ξ l M i := by
      apply Lat.ι_injective f ξ l M
      rw [e, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, Lat.ι_ofW, Lat.ι_dpA]
    rw [hx']
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hi
    by_cases hir : r ≤ i
    · exact dpA_mem_pdP f ξ l M hl hc hir
    · have : Lat.dpA f ξ l M i = 0 := by
        apply Lat.ι_injective f ξ l M
        rw [Lat.ι_dpA, map_zero]
        exact dpE_eq_zero f ξ l M h.nil (by omega)
      rw [this]
      exact Ideal.zero_mem _

end GlobalTheory.CompanionTheory.LatPdpEq
