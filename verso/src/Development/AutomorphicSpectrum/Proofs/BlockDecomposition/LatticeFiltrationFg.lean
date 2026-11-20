import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeSubIffSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationComapSpanPowStatement

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatFG

section
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

/- English proof (translation)
Simplify using `only [Lat.dpE, Lat.η, smul_pow, mul_smul]`.
-/
theorem dpE_eq (i : ℕ) : Lat.dpE f ξ l M i =
    (((i.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ i) • f ξ ^ i := by
  simp only [Lat.dpE, Lat.η, smul_pow, mul_smul]

/- English proof (translation)
Rewrite using `[dpE_eq, Ideal.mem_span_singleton']`. Use `⟨(((i.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ i) • f ξ ^ (i - k), ?_⟩` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, ← pow_add, Nat.sub_add_cancel h]`.
-/
theorem dpE_mem {k i : ℕ} (h : k ≤ i) : Lat.dpE f ξ l M i ∈ Ideal.span {f ξ ^ k} := by
  rw [dpE_eq, Ideal.mem_span_singleton']
  refine ⟨(((i.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ i) • f ξ ^ (i - k), ?_⟩
  rw [smul_mul_assoc, ← pow_add, Nat.sub_add_cancel h]

variable {f ξ} in
/- English proof (translation)
Rewrite using `[dpE_eq, pow_eq_zero_of_le h hn, smul_zero]`.
-/
theorem dpE_eq_zero {m : ℕ} (hn : f ξ ^ m = 0) {i : ℕ} (h : m ≤ i) : Lat.dpE f ξ l M i = 0 := by
  rw [dpE_eq, pow_eq_zero_of_le h hn, smul_zero]

/- English proof (translation)
Establish `hl' : ((l : ℚ) ^ M) ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.2 hl)`. Establish `h : f ξ = ((l : ℚ) ^ M) • Lat.η f ξ l M`. Simplify using `only [Lat.η, smul_smul, mul_inv_cancel₀ hl', one_smul]`. Establish `hnat : ((l ^ M * (j + 1) : ℕ) : B) = ((l : ℚ) ^ M * ((j : ℚ) + 1)) • (1 : B)`. Rewrite using `[Algebra.smul_def, mul_one, ← map_natCast (algebraMap ℚ B)]`.

Use `push_cast`. Both sides reduce to the same expression. Simplify using `only [Lat.dpE]`. Generalize the expression as in `Lat.η f ξ l M = e at h`. Rewrite using `[h, hnat]`.

Simplify using `only [smul_mul_assoc, mul_smul_comm, one_mul, smul_smul, pow_succ']`. Use `congr 1`. Rewrite using `[Nat.factorial_succ]`. Establish `h1 : ((j : ℚ) + 1) ≠ 0` using `by positivity`. Establish `h2 : ((j.factorial : ℚ)) ≠ 0` using `by exact_mod_cast j.factorial_ne_zero`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem mul_dpE {l : ℕ} (hl : l ≠ 0) (j : ℕ) :
    f ξ * Lat.dpE f ξ l M j = ((l ^ M * (j + 1) : ℕ) : B) * Lat.dpE f ξ l M (j + 1) := by
  have hl' : ((l : ℚ) ^ M) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl)
  have h : f ξ = ((l : ℚ) ^ M) • Lat.η f ξ l M := by
    simp only [Lat.η, smul_smul, mul_inv_cancel₀ hl', one_smul]
  have hnat : ((l ^ M * (j + 1) : ℕ) : B) = ((l : ℚ) ^ M * ((j : ℚ) + 1)) • (1 : B) := by
    rw [Algebra.smul_def, mul_one, ← map_natCast (algebraMap ℚ B)]; push_cast; rfl
  simp only [Lat.dpE]
  generalize Lat.η f ξ l M = e at h
  rw [h, hnat]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, smul_smul, pow_succ']
  congr 1
  rw [Nat.factorial_succ]
  have h1 : ((j : ℚ) + 1) ≠ 0 := by positivity
  have h2 : ((j.factorial : ℚ)) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  push_cast
  field_simp

variable {f ξ l M} in
/- English proof (translation)
Distinguish the cases in `hk : k < m`. Rewrite using `[Finset.sum_eq_single k]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb]`.

Introduce `h`. Conclude with `absurd (Finset.mem_range.2 hk) h`. Rewrite using `[dpE_eq_zero l M hn (not_lt.1 hk), mul_zero]`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Establish `: i ≠ k`.

Use `Finset.mem_range.1 hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `[Pi.single_eq_of_ne this]`.
-/
theorem sum_single {m : ℕ} (hn : f ξ ^ m = 0) (k : ℕ) (a : W) :
    ∑ i ∈ Finset.range m, f ((Pi.single k a : ℕ → W) i) * Lat.dpE f ξ l M i = f a * Lat.dpE f ξ l M k := by
  by_cases hk : k < m
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro h
      exact absurd (Finset.mem_range.2 hk) h
  · rw [dpE_eq_zero l M hn (not_lt.1 hk), mul_zero]
    refine Finset.sum_eq_zero fun i hi => ?_
    have : i ≠ k := by
      have := Finset.mem_range.1 hi
      omega
    simp [Pi.single_eq_of_ne this]

variable {f ξ l} in
/- English proof (translation)
Introduce and unpack `rfl`. Conclude with `h.l0 (by simp)`.
-/
theorem l_ne {m : ℕ} (h : Lat.Hyp f ξ l m) : l ≠ 0 := by
  rintro rfl
  exact h.l0 (by simp)

variable {f ξ l} in

/- English proof (translation)
Establish `hl' : ((l : ℚ) ^ M)⁻¹ ≠ 0` using `inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (l_ne h)))`. Establish `h2 : ((j.factorial : ℚ))⁻¹ ≠ 0` using `inv_ne_zero (by exact_mod_cast j.factorial_ne_zero)`. Establish `hu : (((j.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ j) ≠ 0` using `mul_ne_zero h2 (pow_ne_zero _ hl')`. Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.1 hmem`. Rewrite `hb` using `[dpE_eq]`.

Generalize the expression as in `(((j.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ j) = u at hb hu`. Use `h.gr j hj a (u⁻¹ • b) ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, mul_comm (f ξ ^ (j + 1)), hb, mul_smul_comm, smul_smul, inv_mul_cancel₀ hu, one_smul]`.
-/
theorem dvd_of_mem {m : ℕ} (h : Lat.Hyp f ξ l m) {j : ℕ} (hj : j < m) {a : W}
    (hmem : f a * Lat.dpE f ξ l M j ∈ Ideal.span {f ξ ^ (j + 1)}) : ξ ∣ a := by
  have hl' : ((l : ℚ) ^ M)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (l_ne h)))
  have h2 : ((j.factorial : ℚ))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast j.factorial_ne_zero)
  have hu : (((j.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ j) ≠ 0 := mul_ne_zero h2 (pow_ne_zero _ hl')
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hmem
  rw [dpE_eq] at hb
  generalize (((j.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ j) = u at hb hu
  refine h.gr j hj a (u⁻¹ • b) ?_
  rw [mul_smul_comm, mul_comm (f ξ ^ (j + 1)), hb, mul_smul_comm, smul_smul, inv_mul_cancel₀ hu, one_smul]

variable {f ξ l} in

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Take `⟨n, c, hc⟩` from `(GlobalTheory.T.mem_lattice_sub_iff_sum f ξ l M x).1 hx`. Use `⟨fun i => if hi : i < n then c ⟨i, hi⟩ else 0, fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩` and prove the remaining obligations. Use `set g : ℕ → B := fun i => f (if hi : i < n then c ⟨i, hi⟩ else 0) * Lat.dpE f ξ l M i with hg`.

Establish `h1 : x = ∑ i ∈ Finset.range n, g i`. Rewrite using `[hc, ← Fin.sum_univ_eq_sum_range]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[hg]`. Establish `h2 : ∑ i ∈ Finset.range n, g i = ∑ i ∈ Finset.range (max n m), g i` using `Finset.sum_subset (Finset.range_mono (le_max_left _ _)) fun i _ hi => by`.

Establish `: ¬ i < n` using `by simpa using hi`. Simplify using `[hg, this]`. Establish `h3 : ∑ i ∈ Finset.range m, g i = ∑ i ∈ Finset.range (max n m), g i` using `Finset.sum_subset (Finset.range_mono (le_max_right _ _)) fun i _ hi => by`. Establish `: m ≤ i` using `by simpa using hi`. Simplify using `[hg, dpE_eq_zero l M h.nil this]`.

Rewrite using `[h1, h2, ← h3]`. Consider the case `succ j ih`. Take `⟨c, hc, hxc⟩` from `ih (by omega)`. Use `set c' : ℕ → W := c - Pi.single j (c j) with hc'`. Establish `hsum : ∑ i ∈ Finset.range m, f (c' i) * Lat.dpE f ξ l M i = x - f (c j) * Lat.dpE f ξ l M j`.

Rewrite using `[← sum_single h.nil j (c j), hxc, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hc', Pi.sub_apply, map_sub, sub_mul]`. Establish `hz : ∀ i ≤ j, c' i = 0`. Introduce `i hi`.

Break down `hi.lt_or_eq with hi | rfl` into its components or cases. Rewrite using `[hc', Pi.sub_apply, hc i hi, Pi.single_eq_of_ne hi.ne, sub_zero]`. Rewrite using `[hc', Pi.sub_apply, Pi.single_eq_same, sub_self]`. Establish `hrest : ∑ i ∈ Finset.range m, f (c' i) * Lat.dpE f ξ l M i ∈ Ideal.span {f ξ ^ (j + 1)}`. Use `Ideal.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hi : i ≤ j`. Rewrite using `[hz i hi, map_zero, zero_mul]`. Conclude with `Ideal.zero_mem _`. Conclude with `Ideal.mul_mem_left _ _ (dpE_mem f ξ l M (by omega))`. Establish `hx1 : x ∈ Ideal.span {f ξ ^ (j + 1)}` using `(Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hj)) hr`.

Establish `hterm : f (c j) * Lat.dpE f ξ l M j ∈ Ideal.span {f ξ ^ (j + 1)}`. Use `Ideal.sub_mem _ hx1 hrest` as an intermediate fact. Rewrite `this` using `[hsum, sub_sub_cancel]`. Then use the resulting hypothesis. Choose the witnesses or unpack the hypotheses as in `⟨e, he⟩ : ∃ e : W, f (c j) * Lat.dpE f ξ l M j = f e * Lat.dpE f ξ l M (j + 1) := by`. Distinguish the cases in `hjm : j < m`.

Take `⟨d, hd⟩` from `dvd_of_mem M h hjm hterm`. Use `⟨d * ((l ^ M * (j + 1) : ℕ) : W), ?_⟩` and prove the remaining obligations. Rewrite using `[hd, map_mul, map_mul, map_natCast, mul_comm (f ξ), mul_assoc, mul_dpE f ξ M (l_ne h), mul_assoc]`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[dpE_eq_zero l M h.nil (not_lt.1 hjm), map_zero, zero_mul, mul_zero]`.

Use `⟨c' + Pi.single (j + 1) e, fun i hi => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.add_apply, hz i (by omega), Pi.single_eq_of_ne (by omega), add_zero]`. Simplify using `only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`. Rewrite using `[hsum, sum_single h.nil, ← he, sub_add_cancel]`.
-/
theorem exists_coeff {m : ℕ} (h : Lat.Hyp f ξ l m) {x : B} (hx : x ∈ Lat.sub f ξ l M) {r : ℕ}
    (hr : x ∈ Ideal.span {f ξ ^ r}) (j : ℕ) (hj : j ≤ r) :
    ∃ c : ℕ → W, (∀ i < j, c i = 0) ∧ x = ∑ i ∈ Finset.range m, f (c i) * Lat.dpE f ξ l M i := by
  induction j with
  | zero =>
    obtain ⟨n, c, hc⟩ := (GlobalTheory.T.mem_lattice_sub_iff_sum f ξ l M x).1 hx
    refine ⟨fun i => if hi : i < n then c ⟨i, hi⟩ else 0, fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    set g : ℕ → B := fun i => f (if hi : i < n then c ⟨i, hi⟩ else 0) * Lat.dpE f ξ l M i with hg
    have h1 : x = ∑ i ∈ Finset.range n, g i := by
      rw [hc, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [hg]
    have h2 : ∑ i ∈ Finset.range n, g i = ∑ i ∈ Finset.range (max n m), g i :=
      Finset.sum_subset (Finset.range_mono (le_max_left _ _)) fun i _ hi => by
        have : ¬ i < n := by simpa using hi
        simp [hg, this]
    have h3 : ∑ i ∈ Finset.range m, g i = ∑ i ∈ Finset.range (max n m), g i :=
      Finset.sum_subset (Finset.range_mono (le_max_right _ _)) fun i _ hi => by
        have : m ≤ i := by simpa using hi
        simp [hg, dpE_eq_zero l M h.nil this]
    rw [h1, h2, ← h3]
  | succ j ih =>
    obtain ⟨c, hc, hxc⟩ := ih (by omega)
    set c' : ℕ → W := c - Pi.single j (c j) with hc'
    have hsum : ∑ i ∈ Finset.range m, f (c' i) * Lat.dpE f ξ l M i =
        x - f (c j) * Lat.dpE f ξ l M j := by
      rw [← sum_single h.nil j (c j), hxc, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc', Pi.sub_apply, map_sub, sub_mul]
    have hz : ∀ i ≤ j, c' i = 0 := by
      intro i hi
      rcases hi.lt_or_eq with hi | rfl
      · rw [hc', Pi.sub_apply, hc i hi, Pi.single_eq_of_ne hi.ne, sub_zero]
      · rw [hc', Pi.sub_apply, Pi.single_eq_same, sub_self]
    have hrest : ∑ i ∈ Finset.range m, f (c' i) * Lat.dpE f ξ l M i ∈ Ideal.span {f ξ ^ (j + 1)} := by
      refine Ideal.sum_mem _ fun i _ => ?_
      by_cases hi : i ≤ j
      · rw [hz i hi, map_zero, zero_mul]
        exact Ideal.zero_mem _
      · exact Ideal.mul_mem_left _ _ (dpE_mem f ξ l M (by omega))
    have hx1 : x ∈ Ideal.span {f ξ ^ (j + 1)} :=
      (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hj)) hr
    have hterm : f (c j) * Lat.dpE f ξ l M j ∈ Ideal.span {f ξ ^ (j + 1)} := by
      have := Ideal.sub_mem _ hx1 hrest
      rwa [hsum, sub_sub_cancel] at this
    obtain ⟨e, he⟩ : ∃ e : W, f (c j) * Lat.dpE f ξ l M j = f e * Lat.dpE f ξ l M (j + 1) := by
      by_cases hjm : j < m
      · obtain ⟨d, hd⟩ := dvd_of_mem M h hjm hterm
        refine ⟨d * ((l ^ M * (j + 1) : ℕ) : W), ?_⟩
        rw [hd, map_mul, map_mul, map_natCast, mul_comm (f ξ), mul_assoc, mul_dpE f ξ M (l_ne h), mul_assoc]
      · refine ⟨0, ?_⟩
        rw [dpE_eq_zero l M h.nil (not_lt.1 hjm), map_zero, zero_mul, mul_zero]
    refine ⟨c' + Pi.single (j + 1) e, fun i hi => ?_, ?_⟩
    · rw [Pi.add_apply, hz i (by omega), Pi.single_eq_of_ne (by omega), add_zero]
    · simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
      rw [hsum, sum_single h.nil, ← he, sub_add_cancel]

end

/- English proof (translation)
Introduce `W B _ _ _ f ξ l M m h hc r`. Establish `key : pdP (Lat.γ f ξ l M hc) r = Ideal.span (Lat.dpA f ξ l M '' (↑(Finset.Ico r m) : Set ℕ))`. Rewrite using `[GlobalTheory.T.lattice_filtration_comap_span_pow f ξ l M m h hc r]`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`.

Establish `hxs : Lat.ι f ξ l M x ∈ Lat.sub f ξ l M` using `x.2`. Take `⟨c, hc0, hxc⟩` from `exists_coeff M h hxs (Ideal.mem_comap.1 hx) r le_rfl`. Establish `hx' : x = ∑ i ∈ Finset.range m, Lat.ofW f ξ l M (c i) * Lat.dpA f ξ l M i`. Apply `Lat.ι_injective f ξ l M` to reduce the goal to its premises. Rewrite using `[hxc, map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, Lat.ι_ofW, Lat.ι_dpA]`. Rewrite using `[hx']`. Use `Ideal.sum_mem _ fun i hi => ?_` and prove the remaining obligations. Distinguish the cases in `hir : i < r`.

Rewrite using `[hc0 i hir, map_zero, zero_mul]`. Conclude with `Ideal.zero_mem _`. Use `Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, ?_, rfl⟩)` and prove the remaining obligations. Simplify using `only [Finset.coe_Ico, Set.mem_Ico]`. Conclude with `⟨not_lt.1 hir, Finset.mem_range.1 hi⟩`.

Use `Ideal.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, hi, rfl⟩`. Simplify using `only [Finset.coe_Ico, Set.mem_Ico] at hi`. Conclude with `Ideal.mem_comap.2 (dpE_mem f ξ l M hi.1)`. Rewrite using `[key]`.

Conclude with `Submodule.fg_span ((Finset.finite_toSet _).image _)`.
-/
theorem dividedPowerFiltration_fg : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
    Lat.Hyp f ξ l m → ∀ hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ), ∀ r : ℕ,
      (pdP (Lat.γ f ξ l M hc) r).FG := by
  intro W B _ _ _ f ξ l M m h hc r
  have key : pdP (Lat.γ f ξ l M hc) r =
      Ideal.span (Lat.dpA f ξ l M '' (↑(Finset.Ico r m) : Set ℕ)) := by
    rw [GlobalTheory.T.lattice_filtration_comap_span_pow f ξ l M m h hc r]
    apply le_antisymm
    · intro x hx
      have hxs : Lat.ι f ξ l M x ∈ Lat.sub f ξ l M := x.2
      obtain ⟨c, hc0, hxc⟩ := exists_coeff M h hxs (Ideal.mem_comap.1 hx) r le_rfl
      have hx' : x = ∑ i ∈ Finset.range m, Lat.ofW f ξ l M (c i) * Lat.dpA f ξ l M i := by
        apply Lat.ι_injective f ξ l M
        rw [hxc, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, Lat.ι_ofW, Lat.ι_dpA]
      rw [hx']
      refine Ideal.sum_mem _ fun i hi => ?_
      by_cases hir : i < r
      · rw [hc0 i hir, map_zero, zero_mul]
        exact Ideal.zero_mem _
      · refine Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, ?_, rfl⟩)
        simp only [Finset.coe_Ico, Set.mem_Ico]
        exact ⟨not_lt.1 hir, Finset.mem_range.1 hi⟩
    · refine Ideal.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      simp only [Finset.coe_Ico, Set.mem_Ico] at hi
      exact Ideal.mem_comap.2 (dpE_mem f ξ l M hi.1)
  rw [key]
  exact Submodule.fg_span ((Finset.finite_toSet _).image _)

end GlobalTheory.CompanionTheory.LatFG
