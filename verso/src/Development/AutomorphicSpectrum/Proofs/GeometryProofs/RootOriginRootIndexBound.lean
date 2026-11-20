import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.RootUnit

section Lin

variable {Ω : Type} [Field Ω] {L : Type} [AddCommGroup L] [Module Ω L] {r : ℕ}

/- English proof (translation)
Take `⟨l, hl, rfl⟩` from `(Finsupp.mem_span_image_iff_linearCombination Ω).mp h`. Use `⟨l, fun j hj => ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Conclude with `hj (hl (Finsupp.mem_support_iff.mpr hne))`. Rewrite using `[Finsupp.linearCombination_apply, Finsupp.sum_fintype]`.

Introduce `i`. Conclude with `zero_smul _ _`.
-/
theorem exists_coeff_of_mem {c : Fin r → L} {s : Set (Fin r)} {x : L} (h : x ∈ Submodule.span Ω (c '' s)) :
    ∃ f : Fin r → Ω, (∀ j, j ∉ s → f j = 0) ∧ x = ∑ j, f j • c j := by
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).mp h
  refine ⟨l, fun j hj => ?_, ?_⟩
  · by_contra hne
    exact hj (hl (Finsupp.mem_support_iff.mpr hne))
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i
    exact zero_smul _ _

/- English proof (translation)
Establish `h0 : ∑ j, (f - g) j • c j = 0`. Simplify using `only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self]`. Use `Fintype.linearIndependent_iff.mp hc (f - g) h0 j` as an intermediate fact. Rewrite `this` using `[Pi.sub_apply, sub_eq_zero]`. Then use the resulting hypothesis.
-/
theorem coeff_unique {c : Fin r → L} (hc : LinearIndependent Ω c) {f g : Fin r → Ω}
    (h : ∑ j, f j • c j = ∑ j, g j • c j) (j : Fin r) : f j = g j := by
  have h0 : ∑ j, (f - g) j • c j = 0 := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self]
  have := Fintype.linearIndependent_iff.mp hc (f - g) h0 j
  rwa [Pi.sub_apply, sub_eq_zero] at this

/- English proof (translation)
Establish `hr : ∀ v : Fin r → L, flagStep Ω v r = Submodule.span Ω (Set.range v)`. Introduce `v`. Use `show Submodule.span Ω (v '' {k : Fin r | (k : ℕ) < r}) = _`. Rewrite using `[← Set.image_univ]`. Use `congr 2`.

Use extensionality with `k`. Simplify using `[k.isLt]`. Establish `hc : LinearIndependent Ω c`. Rewrite using `[linearIndependent_iff_card_eq_finrank_span]`. Use `show Fintype.card (Fin r) = Module.finrank Ω (Submodule.span Ω (Set.range c))`.

Rewrite using `[← hr c, ← hf r, hr b, finrank_span_eq_card hb]`. Use `⟨hc, fun i j hij => ?_⟩` and prove the remaining obligations. Establish `hmem : b i ∈ Submodule.span Ω (c '' {k : Fin r | (k : ℕ) < (i : ℕ) + 1})`. Establish `h1 : b i ∈ flagStep Ω b ((i : ℕ) + 1)` using `Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩`. Rewrite `h1` using `[hf]`.

Conclude with `h1`. Take `⟨f, hf0, hfx⟩` from `exists_coeff_of_mem hmem`. Rewrite using `[coeff_unique hc ((hT i).symm.trans hfx) j]`. Use `hf0 j (fun hj => ?_)` and prove the remaining obligations. Establish `h2 : (i : ℕ) < j` using `hij`.

Establish `h3 : (j : ℕ) < (i : ℕ) + 1` using `hj`. Use linear arithmetic over natural numbers and integers.
-/
theorem flag_change {b c : Fin r → L} {T : Matrix (Fin r) (Fin r) Ω} (hb : LinearIndependent Ω b)
    (hf : ∀ i : ℕ, flagStep Ω b i = flagStep Ω c i) (hT : ∀ i, b i = ∑ j, T i j • c j) :
    LinearIndependent Ω c ∧ ∀ i j, i < j → T i j = 0 := by
  have hr : ∀ v : Fin r → L, flagStep Ω v r = Submodule.span Ω (Set.range v) := by
    intro v
    show Submodule.span Ω (v '' {k : Fin r | (k : ℕ) < r}) = _
    rw [← Set.image_univ]
    congr 2
    ext k
    simp [k.isLt]
  have hc : LinearIndependent Ω c := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    show Fintype.card (Fin r) = Module.finrank Ω (Submodule.span Ω (Set.range c))
    rw [← hr c, ← hf r, hr b, finrank_span_eq_card hb]
  refine ⟨hc, fun i j hij => ?_⟩
  have hmem : b i ∈ Submodule.span Ω (c '' {k : Fin r | (k : ℕ) < (i : ℕ) + 1}) := by
    have h1 : b i ∈ flagStep Ω b ((i : ℕ) + 1) := Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩
    rw [hf] at h1
    exact h1
  obtain ⟨f, hf0, hfx⟩ := exists_coeff_of_mem hmem
  rw [coeff_unique hc ((hT i).symm.trans hfx) j]
  refine hf0 j (fun hj => ?_)
  have h2 : (i : ℕ) < j := hij
  have h3 : (j : ℕ) < (i : ℕ) + 1 := hj
  omega

/- English proof (translation)
Take `⟨hc, htri⟩` from `flag_change hb hf hT`. Establish `hterm : ∀ (v : Fin r → L) (g : Fin r → Ω), (∀ k, i < k → g k = 0) → ∑ k ∈ Finset.univ.erase i, g k • v k ∈ flagStep Ω v i`. Introduce `v g hg`. Use `Submodule.sum_mem _ fun k hk => ?_` and prove the remaining obligations. Break down `lt_trichotomy k i with hki | hki | hki` into its components or cases.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hki, rfl⟩)`. Conclude with `absurd hki (Finset.ne_of_mem_erase hk)`. Rewrite using `[hg k hki, zero_smul]`. Conclude with `Submodule.zero_mem _`. Establish `hbi : b i - T i i • c i ∈ flagStep Ω c i`.

Use `hterm c (fun j => T i j) (fun k hk => htri i k hk)` as an intermediate fact. Rewrite `this` using `[Finset.sum_erase_eq_sub (Finset.mem_univ i), ← hT i]`. Then use the resulting hypothesis. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `t ⟨e, he, het⟩`.

Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun A).mp he`. Use `set α : Fin r → Ω := fun k => (a k : Ω) with hα`. Establish `hsum : ∑ k, a k • b k = ∑ k, α k • b k` using `rfl`. Rewrite `het` using `[hsum]`. Establish `hci : c i ∈ flagStep Ω c ((i : ℕ) + 1)` using `Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩`.

Establish `hmono : flagStep Ω c i ≤ flagStep Ω c ((i : ℕ) + 1)` using `Submodule.span_mono (Set.image_mono fun k (hk : (k : ℕ) < i) => Nat.lt_succ_of_lt hk)`. Establish `he1 : ∑ k, α k • b k ∈ Submodule.span Ω (b '' {k : Fin r | (k : ℕ) < (i : ℕ) + 1})`. Establish `h1 : ∑ k, α k • b k ∈ flagStep Ω c ((i : ℕ) + 1)`. Use `add_mem (hmono het) (Submodule.smul_mem _ t hci)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.

Rewrite `h1` using `[← hf]`. Conclude with `h1`. Take `⟨f, hf0, hfe⟩` from `exists_coeff_of_mem he1`. Establish `hαz : ∀ k, i < k → α k = 0`. Introduce `k hk`.

Rewrite using `[coeff_unique hb hfe k]`. Use `hf0 k (fun hk' => ?_)` and prove the remaining obligations. Establish `h2 : (i : ℕ) < k` using `hk`. Establish `h3 : (k : ℕ) < (i : ℕ) + 1` using `hk'`. Use linear arithmetic over natural numbers and integers.

Establish `hC : ∑ k, α k • b k - α i • b i ∈ flagStep Ω c i`. Rewrite using `[← hf, ← Finset.sum_erase_eq_sub (Finset.mem_univ i)]`. Conclude with `hterm b α hαz`. Establish `hE : (α i * T i i - t) • c i ∈ flagStep Ω c i`. Establish `heq : (α i * T i i - t) • c i = (∑ k, α k • b k - t • c i) - (∑ k, α k • b k - α i • b i) - α i • (b i - T i i • c i)`.

Rewrite using `[sub_smul, mul_smul, smul_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[heq]`. Conclude with `sub_mem (sub_mem het hC) (Submodule.smul_mem _ (α i) hbi)`. Establish `ht : t = α i * T i i`.

Assume the negation of the conclusion as `hne`. Establish `hne' : α i * T i i - t ≠ 0` using `sub_ne_zero.mpr (Ne.symm hne)`. Establish `hmem : c i ∈ flagStep Ω c i`. Use `Submodule.smul_mem _ (α i * T i i - t)⁻¹ hE` as an intermediate fact. Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hne', one_smul]`. Then use the resulting hypothesis.

Conclude with `hc.notMem_span_image (s := {k : Fin r | (k : ℕ) < i}) (x := i) (fun h => lt_irrefl (i : ℕ) h) hmem`. Rewrite using `[ht]`. Conclude with `Submodule.mem_span_singleton.mpr ⟨a i, rfl⟩`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Conclude with `Submodule.subset_span ⟨b i, Submodule.subset_span ⟨i, rfl⟩, hbi⟩`.
-/
theorem span_gr_eq (A : Subring Ω) {b c : Fin r → L} {T : Matrix (Fin r) (Fin r) Ω} (hb : LinearIndependent Ω b)
    (hf : ∀ i : ℕ, flagStep Ω b i = flagStep Ω c i) (hT : ∀ i, b i = ∑ j, T i j • c j) (i : Fin r) :
    Submodule.span A {t : Ω | ∃ e ∈ Submodule.span A (Set.range b), e - t • c i ∈ flagStep Ω c i} =
      Submodule.span A {T i i} := by
  obtain ⟨hc, htri⟩ := flag_change hb hf hT
  have hterm : ∀ (v : Fin r → L) (g : Fin r → Ω), (∀ k, i < k → g k = 0) →
      ∑ k ∈ Finset.univ.erase i, g k • v k ∈ flagStep Ω v i := by
    intro v g hg
    refine Submodule.sum_mem _ fun k hk => ?_
    rcases lt_trichotomy k i with hki | hki | hki
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hki, rfl⟩)
    · exact absurd hki (Finset.ne_of_mem_erase hk)
    · rw [hg k hki, zero_smul]
      exact Submodule.zero_mem _
  have hbi : b i - T i i • c i ∈ flagStep Ω c i := by
    have := hterm c (fun j => T i j) (fun k hk => htri i k hk)
    rwa [Finset.sum_erase_eq_sub (Finset.mem_univ i), ← hT i] at this
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro t ⟨e, he, het⟩
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp he
    set α : Fin r → Ω := fun k => (a k : Ω) with hα
    have hsum : ∑ k, a k • b k = ∑ k, α k • b k := rfl
    rw [hsum] at het
    have hci : c i ∈ flagStep Ω c ((i : ℕ) + 1) := Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩
    have hmono : flagStep Ω c i ≤ flagStep Ω c ((i : ℕ) + 1) :=
      Submodule.span_mono (Set.image_mono fun k (hk : (k : ℕ) < i) => Nat.lt_succ_of_lt hk)
    have he1 : ∑ k, α k • b k ∈ Submodule.span Ω (b '' {k : Fin r | (k : ℕ) < (i : ℕ) + 1}) := by
      have h1 : ∑ k, α k • b k ∈ flagStep Ω c ((i : ℕ) + 1) := by
        have := add_mem (hmono het) (Submodule.smul_mem _ t hci)
        rwa [sub_add_cancel] at this
      rw [← hf] at h1
      exact h1
    obtain ⟨f, hf0, hfe⟩ := exists_coeff_of_mem he1
    have hαz : ∀ k, i < k → α k = 0 := by
      intro k hk
      rw [coeff_unique hb hfe k]
      refine hf0 k (fun hk' => ?_)
      have h2 : (i : ℕ) < k := hk
      have h3 : (k : ℕ) < (i : ℕ) + 1 := hk'
      omega
    have hC : ∑ k, α k • b k - α i • b i ∈ flagStep Ω c i := by
      rw [← hf, ← Finset.sum_erase_eq_sub (Finset.mem_univ i)]
      exact hterm b α hαz
    have hE : (α i * T i i - t) • c i ∈ flagStep Ω c i := by
      have heq : (α i * T i i - t) • c i =
          (∑ k, α k • b k - t • c i) - (∑ k, α k • b k - α i • b i) - α i • (b i - T i i • c i) := by
        rw [sub_smul, mul_smul, smul_sub]
        abel
      rw [heq]
      exact sub_mem (sub_mem het hC) (Submodule.smul_mem _ (α i) hbi)
    have ht : t = α i * T i i := by
      by_contra hne
      have hne' : α i * T i i - t ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      have hmem : c i ∈ flagStep Ω c i := by
        have := Submodule.smul_mem _ (α i * T i i - t)⁻¹ hE
        rwa [smul_smul, inv_mul_cancel₀ hne', one_smul] at this
      exact hc.notMem_span_image (s := {k : Fin r | (k : ℕ) < i}) (x := i) (fun h => lt_irrefl (i : ℕ) h) hmem
    rw [ht]
    exact Submodule.mem_span_singleton.mpr ⟨a i, rfl⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨b i, Submodule.subset_span ⟨i, rfl⟩, hbi⟩

end Lin

section Lines

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

/- English proof (translation)
Establish `h1 : σ ∈ Submodule.span A {s}`. Rewrite using `[← h]`. Conclude with `Submodule.mem_span_singleton_self σ`. Establish `h2 : s ∈ Submodule.span A {σ}`. Rewrite using `[h]`.

Conclude with `Submodule.mem_span_singleton_self s`. Take `⟨u, hu⟩` from `Submodule.mem_span_singleton.mp h1`. Take `⟨v, hv⟩` from `Submodule.mem_span_singleton.mp h2`. Establish `hu' : (u : Ω) * s = σ` using `hu`. Establish `hv' : (v : Ω) * σ = s` using `hv`.

Establish `huv : (u : Ω) * v = 1`. Establish `h3 : (u : Ω) * v * σ = 1 * σ` using `by rw [mul_assoc, hv', hu', one_mul]`. Conclude with `mul_right_cancel₀ hσ h3`. Establish `hmem : ∀ n : ℤ, (u : Ω) ^ n ∈ A`. Introduce `n`.

Break down `n with n | n` into its components or cases. Simplify using `using pow_mem u.2 n`. Establish `h4 : (u : Ω) ^ (Int.negSucc n) = (v : Ω) ^ (n + 1)`. Rewrite using `[zpow_negSucc, ← inv_pow, inv_eq_of_mul_eq_one_right huv]`. Rewrite using `[h4]`.

Conclude with `pow_mem v.2 _`. Rewrite using `[Submodule.mem_span_singleton]`. Use `⟨⟨(u : Ω) ^ a, hmem a⟩, ?_⟩` and prove the remaining obligations. Use `show (u : Ω) ^ a * s ^ a = σ ^ a`. Rewrite using `[← mul_zpow, hu']`.
-/
theorem zpow_mem_span {A : Subring Ω} {s σ : Ω} (hs : s ≠ 0) (hσ : σ ≠ 0)
    (h : Submodule.span A {σ} = Submodule.span A {s}) (a : ℤ) : σ ^ a ∈ Submodule.span A {s ^ a} := by
  have h1 : σ ∈ Submodule.span A {s} := by
    rw [← h]
    exact Submodule.mem_span_singleton_self σ
  have h2 : s ∈ Submodule.span A {σ} := by
    rw [h]
    exact Submodule.mem_span_singleton_self s
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp h1
  obtain ⟨v, hv⟩ := Submodule.mem_span_singleton.mp h2
  have hu' : (u : Ω) * s = σ := hu
  have hv' : (v : Ω) * σ = s := hv
  have huv : (u : Ω) * v = 1 := by
    have h3 : (u : Ω) * v * σ = 1 * σ := by rw [mul_assoc, hv', hu', one_mul]
    exact mul_right_cancel₀ hσ h3
  have hmem : ∀ n : ℤ, (u : Ω) ^ n ∈ A := by
    intro n
    rcases n with n | n
    · simpa using pow_mem u.2 n
    · have h4 : (u : Ω) ^ (Int.negSucc n) = (v : Ω) ^ (n + 1) := by
        rw [zpow_negSucc, ← inv_pow, inv_eq_of_mul_eq_one_right huv]
      rw [h4]
      exact pow_mem v.2 _
  rw [Submodule.mem_span_singleton]
  refine ⟨⟨(u : Ω) ^ a, hmem a⟩, ?_⟩
  show (u : Ω) ^ a * s ^ a = σ ^ a
  rw [← mul_zpow, hu']

/- English proof (translation)
Establish `hs0 : s ≠ 0` using `hs.1`. Establish `hsa : s ^ a ∈ Lat.tens (fun _ : Unit => Λ) (fun _ => a) q`. Apply `Submodule.subset_span` to reduce the goal to its premises. Conclude with `⟨fun _ => s, fun _ => hs, by simp⟩`. Establish `hle : Lat.tens (fun _ : Unit => Λ) (fun _ => a) q ≤ Submodule.span (regAt ξ q) {s ^ a}`.

Apply `Submodule.span_le.mpr` to reduce the goal to its premises. Introduce and unpack `t ⟨σ', hσ', rfl⟩`. Establish `hσ` using `hσ' ()`. Establish `heq : Submodule.span (regAt ξ q) {σ' ()} = Submodule.span (regAt ξ q) {s}` using `hσ.2.symm.trans hs.2`. Simplify using `using zpow_mem_span hs0 hσ.1 heq a`.

Establish `hMmem : M ∈ Lat.tens (fun _ : Unit => Λ) (fun _ => a) q`. Rewrite using `[hM]`. Conclude with `Submodule.mem_span_singleton_self M`. Take `⟨r', hr'⟩` from `Submodule.mem_span_singleton.mp (hle hMmem)`. Rewrite `hsa` using `[hM]`.

Take `⟨r, hr⟩` from `Submodule.mem_span_singleton.mp hsa`. Establish `hr1 : (r' : Ω) * s ^ a = M` using `hr'`. Establish `hr2 : (r : Ω) * M = s ^ a` using `hr`. Establish `hsa0 : s ^ a ≠ 0` using `zpow_ne_zero a hs0`. Prove the components needed by the constructor for the conclusion.

Establish `h5 : M * s ^ (-a) = r'`. Rewrite using `[← hr1, zpow_neg, mul_assoc, mul_inv_cancel₀ hsa0, mul_one]`. Rewrite using `[h5]`. Conclude with `r'.2`. Establish `h6 : (M * s ^ (-a))⁻¹ = r`.

Rewrite using `[zpow_neg, mul_inv, inv_inv, ← hr2, mul_comm (r : Ω) M, ← mul_assoc, inv_mul_cancel₀ hM0, one_mul]`. Rewrite using `[h6]`. Conclude with `r.2`.
-/
theorem unit_of_tens (Λ : Lat ξ Ω) (q : Cpt ξ) (a : ℤ) {s M : Ω} (hs : Λ.IsGenAt q s) (hM0 : M ≠ 0)
    (hM : Lat.tens (fun _ : Unit => Λ) (fun _ => a) q = Submodule.span (regAt ξ q) {M}) :
    M * s ^ (-a) ∈ regAt ξ q ∧ (M * s ^ (-a))⁻¹ ∈ regAt ξ q := by
  have hs0 : s ≠ 0 := hs.1
  have hsa : s ^ a ∈ Lat.tens (fun _ : Unit => Λ) (fun _ => a) q := by
    apply Submodule.subset_span
    exact ⟨fun _ => s, fun _ => hs, by simp⟩
  have hle : Lat.tens (fun _ : Unit => Λ) (fun _ => a) q ≤ Submodule.span (regAt ξ q) {s ^ a} := by
    apply Submodule.span_le.mpr
    rintro t ⟨σ', hσ', rfl⟩
    have hσ := hσ' ()
    have heq : Submodule.span (regAt ξ q) {σ' ()} = Submodule.span (regAt ξ q) {s} := hσ.2.symm.trans hs.2
    simpa using zpow_mem_span hs0 hσ.1 heq a
  have hMmem : M ∈ Lat.tens (fun _ : Unit => Λ) (fun _ => a) q := by
    rw [hM]
    exact Submodule.mem_span_singleton_self M
  obtain ⟨r', hr'⟩ := Submodule.mem_span_singleton.mp (hle hMmem)
  rw [hM] at hsa
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hsa
  have hr1 : (r' : Ω) * s ^ a = M := hr'
  have hr2 : (r : Ω) * M = s ^ a := hr
  have hsa0 : s ^ a ≠ 0 := zpow_ne_zero a hs0
  constructor
  · have h5 : M * s ^ (-a) = r' := by
      rw [← hr1, zpow_neg, mul_assoc, mul_inv_cancel₀ hsa0, mul_one]
    rw [h5]
    exact r'.2
  · have h6 : (M * s ^ (-a))⁻¹ = r := by
      rw [zpow_neg, mul_inv, inv_inv, ← hr2, mul_comm (r : Ω) M, ← mul_assoc, inv_mul_cancel₀ hM0, one_mul]
    rw [h6]
    exact r.2

end Lines

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or ρ q ch hch b Tm hfl hfr hT hd`. Establish `hL : (Or.Fl.rootLat ρ).IsDegOn Set.univ RM.y (RM.xdeg ρ) (Or.e ρ)` using `Or.lines ρ`. Take `⟨_, hL2⟩` from `hL`. Establish `hdeg : Lat.tens (fun _ : Unit => (Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1).gr (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1) (HodgeCpt.rootIdx Dw ρ).2) (fun _ => HodgeCpt.rootSgn Dw ρ) q = Submodule.span (regAt Or.𝔐.ξ q) {(∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ}` using `hL2 q (Set.mem_univ q) ch hch`. Establish `hgr : ((Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1).gr (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1) (HodgeCpt.rootIdx Dw ρ).2).IsGenAt q (Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2)`.

Use `⟨hd _, ?_⟩` and prove the remaining obligations. Establish `h1` using `span_gr_eq (regAt Or.𝔐.ξ q) hfr.1 hfl hT (HodgeCpt.rootIdx Dw ρ).2`. Rewrite `h1` using `[← hfr.2]`. Conclude with `h1`. Establish `hM0 : (∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ ≠ 0`.

Introduce `h0`. Establish `hmem : Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2 ^ HodgeCpt.rootSgn Dw ρ ∈ Lat.tens (fun _ : Unit => (Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1).gr (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1) (HodgeCpt.rootIdx Dw ρ).2) (fun _ => HodgeCpt.rootSgn Dw ρ) q`. Apply `Submodule.subset_span` to reduce the goal to its premises. Conclude with `⟨fun _ => Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2, fun _ => hgr, by simp⟩`. Rewrite `hmem` using `[hdeg, h0]`.

Take `⟨x, hx⟩` from `Submodule.mem_span_singleton.mp hmem`. Establish `hx' : (x : RM.Ω) * 0 = _` using `hx`. Rewrite `hx'` using `[mul_zero]`. Conclude with `zpow_ne_zero _ (hd _) hx'.symm`. Conclude with `unit_of_tens _ q _ hgr hM0 hdeg`.
-/
theorem root_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (ρ : RootIx Dw) (q : Cpt Or.𝔐.ξ) (ch : (k : RM.K) → RM.ι k), InChart Or.𝔐.ξ (fun c' : (k : RM.K) → RM.ι k => ∏ k, RM.y ⟨k, c' k⟩) ch q → ∀ (b : Fin (labelRk Dw (HodgeCpt.rootIdx Dw ρ).1) → Or.𝔐.Li) (Tm : Matrix (Fin (labelRk Dw (HodgeCpt.rootIdx Dw ρ).1)) (Fin (labelRk Dw (HodgeCpt.rootIdx Dw ρ).1)) RM.Ω), (∀ i : ℕ, flagStep RM.Ω b i = flagStep RM.Ω (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1) i) → (Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1).IsFrameAt b q → (∀ i, b i = ∑ j, Tm i j • Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1 j) → (∀ i, Tm i i ≠ 0) → ((∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ) * (Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2) ^ (-HodgeCpt.rootSgn Dw ρ) ∈ regAt Or.𝔐.ξ q ∧ (((∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ) * (Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2) ^ (-HodgeCpt.rootSgn Dw ρ))⁻¹ ∈ regAt Or.𝔐.ξ q := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or ρ q ch hch b Tm hfl hfr hT hd
  have hL : (Or.Fl.rootLat ρ).IsDegOn Set.univ RM.y (RM.xdeg ρ) (Or.e ρ) := Or.lines ρ
  obtain ⟨_, hL2⟩ := hL
  have hdeg : Lat.tens (fun _ : Unit => (Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1).gr
      (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1) (HodgeCpt.rootIdx Dw ρ).2) (fun _ => HodgeCpt.rootSgn Dw ρ) q =
      Submodule.span (regAt Or.𝔐.ξ q) {(∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ} :=
    hL2 q (Set.mem_univ q) ch hch
  have hgr : ((Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1).gr (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1)
      (HodgeCpt.rootIdx Dw ρ).2).IsGenAt q (Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2) := by
    refine ⟨hd _, ?_⟩
    have h1 := span_gr_eq (regAt Or.𝔐.ξ q) hfr.1 hfl hT (HodgeCpt.rootIdx Dw ρ).2
    rw [← hfr.2] at h1
    exact h1
  have hM0 : (∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ ≠ 0 := by
    intro h0
    have hmem : Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2 ^ HodgeCpt.rootSgn Dw ρ ∈
        Lat.tens (fun _ : Unit => (Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1).gr
          (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1) (HodgeCpt.rootIdx Dw ρ).2) (fun _ => HodgeCpt.rootSgn Dw ρ) q := by
      apply Submodule.subset_span
      exact ⟨fun _ => Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2, fun _ => hgr, by simp⟩
    rw [hdeg, h0] at hmem
    obtain ⟨x, hx⟩ := Submodule.mem_span_singleton.mp hmem
    have hx' : (x : RM.Ω) * 0 = _ := hx
    rw [mul_zero] at hx'
    exact zpow_ne_zero _ (hd _) hx'.symm
  exact unit_of_tens _ q _ hgr hM0 hdeg

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.RootUnit
