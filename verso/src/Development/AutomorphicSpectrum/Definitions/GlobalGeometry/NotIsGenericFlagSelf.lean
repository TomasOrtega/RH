import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagModel

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

/- English proof (translation)
Introduce `p _`. Conclude with `⟨⊤, trivial, b, fun _ => rfl, fun q _ _ => And.intro hb rfl⟩`.
-/
theorem isFlagVBOn_frame {r : ℕ} (b : Fin r → E) (hb : LinearIndependent Ω b) (T : Set (Cpt ξ)) :
    Lat.IsFlagVBOn (fun p => Submodule.span (regAt ξ p) (Set.range b) : Lat ξ E) T b := by
  intro p _
  exact ⟨⊤, trivial, b, fun _ => rfl, fun q _ _ => And.intro hb rfl⟩

/- English proof (translation)
Conclude with `hb.notMem_span_image (by simp)`.
-/
theorem not_mem_flagStep {r : ℕ} (b : Fin r → E) (hb : LinearIndependent Ω b) (i : Fin r) :
    b i ∉ flagStep Ω b i := by
  exact hb.notMem_span_image (by simp)

/- English proof (translation)
Take `⟨hb, hLp⟩` from `hL`. Establish `hbi : b i ∉ flagStep Ω b i` using `not_mem_flagStep b hb i`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Apply `hbi` to reduce the goal to its premises.

Rewrite using `[hF]`. Simplify using `using hc`. Use `⟨hc0, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `t ⟨e, he, het⟩`.

Rewrite `he` using `[hLp]`. Take `⟨d, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun (regAt ξ p)).mp he`. Establish `het' : ∑ k, (d k : Ω) • b k - t • b₀ i ∈ flagStep Ω b₀ i` using `het`. Use `set S : Submodule Ω E := Submodule.span Ω (b '' {k | k ≠ i}) with hS`. Establish `hFS : flagStep Ω b₀ i ≤ S`.

Rewrite using `[← hF]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, hk, rfl⟩`. Use `⟨k, fun hki => ?_, rfl⟩` and prove the remaining obligations. Substitute `hki` using the available equality.

Conclude with `lt_irrefl (k : ℕ) hk`. Establish `h1 : c • (∑ k, (d k : Ω) • b k - t • b₀ i) ∈ S` using `S.smul_mem c (hFS het')`. Establish `h2 : c • ∑ k ∈ Finset.univ.erase i, (d k : Ω) • b k ∈ S` using `S.smul_mem c (Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, Finset.ne_of_mem_erase hk, rfl⟩))`. Establish `h3 : t • (b i - c • b₀ i) ∈ S` using `S.smul_mem t (hFS hc)`. Establish `heq : (c * (d i : Ω) - t) • b i = c • (∑ k, (d k : Ω) • b k - t • b₀ i) - c • ∑ k ∈ Finset.univ.erase i, (d k : Ω) • b k - t • (b i - c • b₀ i)`.

Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ i)]`. Use `module`. Establish `key : (c * (d i : Ω) - t) • b i ∈ S`. Rewrite using `[heq]`. Conclude with `S.sub_mem (S.sub_mem h1 h2) h3`.

Establish `hzero : c * (d i : Ω) - t = 0`. Assume the negation of the conclusion as `hne`. Apply `hb.notMem_span_image (s := {k | k ≠ i}) (x := i) (by simp)` to reduce the goal to its premises. Use `S.smul_mem (c * (d i : Ω) - t)⁻¹ key` as an intermediate fact. Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hne, one_smul]`. Then use the resulting hypothesis.

Use `Submodule.mem_span_singleton.mpr ⟨d i, ?_⟩` and prove the remaining obligations. Use `show (d i : Ω) * c = t`. Rewrite using `[mul_comm]`. Conclude with `sub_eq_zero.mp hzero`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations.

Introduce and unpack `_ rfl`. Use `Submodule.subset_span ⟨b i, ?_, hc⟩` and prove the remaining obligations. Rewrite using `[hLp]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`.
-/
theorem gr_isGenAt {r : ℕ} (L : Lat ξ E) (b b₀ : Fin r → E) (p : Cpt ξ) (hL : L.IsFrameAt b p)
    (hF : ∀ i, flagStep Ω b i = flagStep Ω b₀ i) (i : Fin r) (c : Ω)
    (hc : b i - c • b₀ i ∈ flagStep Ω b₀ i) : (L.gr b₀ i).IsGenAt p c := by
  obtain ⟨hb, hLp⟩ := hL
  have hbi : b i ∉ flagStep Ω b i := not_mem_flagStep b hb i
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hbi
    rw [hF]
    simpa using hc
  refine ⟨hc0, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro t ⟨e, he, het⟩
    rw [hLp] at he
    obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (regAt ξ p)).mp he
    have het' : ∑ k, (d k : Ω) • b k - t • b₀ i ∈ flagStep Ω b₀ i := het
    set S : Submodule Ω E := Submodule.span Ω (b '' {k | k ≠ i}) with hS
    have hFS : flagStep Ω b₀ i ≤ S := by
      rw [← hF]
      refine Submodule.span_mono ?_
      rintro _ ⟨k, hk, rfl⟩
      refine ⟨k, fun hki => ?_, rfl⟩
      subst hki
      exact lt_irrefl (k : ℕ) hk
    have h1 : c • (∑ k, (d k : Ω) • b k - t • b₀ i) ∈ S := S.smul_mem c (hFS het')
    have h2 : c • ∑ k ∈ Finset.univ.erase i, (d k : Ω) • b k ∈ S :=
      S.smul_mem c (Submodule.sum_mem _ fun k hk =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, Finset.ne_of_mem_erase hk, rfl⟩))
    have h3 : t • (b i - c • b₀ i) ∈ S := S.smul_mem t (hFS hc)
    have heq : (c * (d i : Ω) - t) • b i =
        c • (∑ k, (d k : Ω) • b k - t • b₀ i) - c • ∑ k ∈ Finset.univ.erase i, (d k : Ω) • b k -
          t • (b i - c • b₀ i) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      module
    have key : (c * (d i : Ω) - t) • b i ∈ S := by
      rw [heq]
      exact S.sub_mem (S.sub_mem h1 h2) h3
    have hzero : c * (d i : Ω) - t = 0 := by
      by_contra hne
      apply hb.notMem_span_image (s := {k | k ≠ i}) (x := i) (by simp)
      have := S.smul_mem (c * (d i : Ω) - t)⁻¹ key
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
    refine Submodule.mem_span_singleton.mpr ⟨d i, ?_⟩
    show (d i : Ω) * c = t
    rw [mul_comm]
    exact sub_eq_zero.mp hzero
  · refine Submodule.span_le.mpr ?_
    rintro _ rfl
    refine Submodule.subset_span ⟨b i, ?_, hc⟩
    rw [hLp]
    exact Submodule.subset_span ⟨i, rfl⟩

/- English proof (translation)
Take `⟨U, hpU, b, hF, hfr⟩` from `h p hp`. Establish `hL` using `hfr p hp hpU`. Establish `hmem : b i ∈ flagStep Ω b₀ ((i : ℕ) + 1)`. Rewrite using `[← hF]`. Conclude with `Submodule.subset_span ⟨i, Nat.lt_add_one _, rfl⟩`.

Establish `hsub : b₀ '' {k : Fin r | (k : ℕ) < (i : ℕ) + 1} ⊆ insert (b₀ i) (b₀ '' {k : Fin r | (k : ℕ) < i})`. Introduce and unpack `_ ⟨k, hk, rfl⟩`. Break down `(Nat.lt_add_one_iff.mp hk).lt_or_eq with h' | h'` into its components or cases. Conclude with `Set.mem_insert_of_mem _ ⟨k, h', rfl⟩`. Rewrite using `[Fin.ext h']`.

Conclude with `Set.mem_insert _ _`. Establish `hmem' : b i ∈ Submodule.span Ω (insert (b₀ i) (b₀ '' {k : Fin r | (k : ℕ) < i}))` using `Submodule.span_mono hsub hmem`. Rewrite `hmem'` using `[Submodule.span_insert]`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.mp hmem'`. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.mp hy`.

Use `⟨a, gr_isGenAt L b b₀ p hL hF i a ?_⟩` and prove the remaining obligations. Rewrite using `[← hyz, add_sub_cancel_left]`. Conclude with `hz`.
-/
theorem exists_gen {r : ℕ} (L : Lat ξ E) (T : Set (Cpt ξ)) (b₀ : Fin r → E) (h : L.IsFlagVBOn T b₀)
    (p : Cpt ξ) (hp : p ∈ T) (i : Fin r) : ∃ c, (L.gr b₀ i).IsGenAt p c := by
  obtain ⟨U, hpU, b, hF, hfr⟩ := h p hp
  have hL := hfr p hp hpU
  have hmem : b i ∈ flagStep Ω b₀ ((i : ℕ) + 1) := by
    rw [← hF]
    exact Submodule.subset_span ⟨i, Nat.lt_add_one _, rfl⟩
  have hsub : b₀ '' {k : Fin r | (k : ℕ) < (i : ℕ) + 1} ⊆
      insert (b₀ i) (b₀ '' {k : Fin r | (k : ℕ) < i}) := by
    rintro _ ⟨k, hk, rfl⟩
    rcases (Nat.lt_add_one_iff.mp hk).lt_or_eq with h' | h'
    · exact Set.mem_insert_of_mem _ ⟨k, h', rfl⟩
    · rw [Fin.ext h']
      exact Set.mem_insert _ _
  have hmem' : b i ∈ Submodule.span Ω (insert (b₀ i) (b₀ '' {k : Fin r | (k : ℕ) < i})) :=
    Submodule.span_mono hsub hmem
  rw [Submodule.span_insert] at hmem'
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem'
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
  refine ⟨a, gr_isGenAt L b b₀ p hL hF i a ?_⟩
  rw [← hyz, add_sub_cancel_left]
  exact hz

/- English proof (translation)
Take `⟨hs0, hsp⟩` from `hs`. Take `⟨ht0, htp⟩` from `ht`. Establish `h1 : t ∈ Submodule.span (regAt ξ p) {s}`. Rewrite using `[← hsp, htp]`. Conclude with `Submodule.mem_span_singleton_self t`.

Establish `h2 : s ∈ Submodule.span (regAt ξ p) {t}`. Rewrite using `[← htp, hsp]`. Conclude with `Submodule.mem_span_singleton_self s`. Take `⟨a, ha⟩` from `Submodule.mem_span_singleton.mp h1`. Take `⟨a', ha'⟩` from `Submodule.mem_span_singleton.mp h2`.

Establish `hts : t / s = a`. Rewrite using `[div_eq_iff hs0]`. Conclude with `ha.symm`. Establish `hst : s / t = a'`. Rewrite using `[div_eq_iff ht0]`.

Conclude with `ha'.symm`. Break down `n with m | m` into its components or cases. Rewrite using `[Int.ofNat_eq_natCast, zpow_natCast, hts]`. Conclude with `pow_mem a.2 m`. Rewrite using `[zpow_negSucc, ← inv_pow, inv_div, hst]`.

Conclude with `pow_mem a'.2 _`.
-/
theorem zpow_ratio (Λ : Lat ξ Ω) (p : Cpt ξ) (s t : Ω) (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) (n : ℤ) :
    (t / s) ^ n ∈ regAt ξ p := by
  obtain ⟨hs0, hsp⟩ := hs
  obtain ⟨ht0, htp⟩ := ht
  have h1 : t ∈ Submodule.span (regAt ξ p) {s} := by
    rw [← hsp, htp]
    exact Submodule.mem_span_singleton_self t
  have h2 : s ∈ Submodule.span (regAt ξ p) {t} := by
    rw [← htp, hsp]
    exact Submodule.mem_span_singleton_self s
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h1
  obtain ⟨a', ha'⟩ := Submodule.mem_span_singleton.mp h2
  have hts : t / s = a := by
    rw [div_eq_iff hs0]
    exact ha.symm
  have hst : s / t = a' := by
    rw [div_eq_iff ht0]
    exact ha'.symm
  rcases n with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast, hts]
    exact pow_mem a.2 m
  · rw [zpow_negSucc, ← inv_pow, inv_div, hst]
    exact pow_mem a'.2 _

/- English proof (translation)
Use `⟨Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hs i).1, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `t ⟨s', hs', rfl⟩`. Establish `hr : ∏ i, (s' i / s i) ^ a i ∈ regAt ξ p` using `prod_mem fun i _ => zpow_ratio (Λ i) p (s i) (s' i) (hs i) (hs' i) (a i)`. Use `Submodule.mem_span_singleton.mpr ⟨⟨_, hr⟩, ?_⟩` and prove the remaining obligations.

Use `show (∏ i, (s' i / s i) ^ a i) * ∏ i, s i ^ a i = ∏ i, s' i ^ a i`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_zpow, div_mul_cancel₀ _ (hs i).1]`. Conclude with `Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨s, hs, rfl⟩)`.
-/
theorem tens_isGenAt {I : Type} [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) (p : Cpt ξ) (s : I → Ω)
    (hs : ∀ i, (Λ i).IsGenAt p (s i)) : (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  refine ⟨Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hs i).1, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro t ⟨s', hs', rfl⟩
    have hr : ∏ i, (s' i / s i) ^ a i ∈ regAt ξ p :=
      prod_mem fun i _ => zpow_ratio (Λ i) p (s i) (s' i) (hs i) (hs' i) (a i)
    refine Submodule.mem_span_singleton.mpr ⟨⟨_, hr⟩, ?_⟩
    show (∏ i, (s' i / s i) ^ a i) * ∏ i, s i ^ a i = ∏ i, s' i ^ a i
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← mul_zpow, div_mul_cancel₀ _ (hs i).1]
  · exact Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨s, hs, rfl⟩)

/- English proof (translation)
Establish `hq : ∀ q : Σ σ, Fin (r σ), ∃ c, ((L q.1).gr (b₀ q.1) q.2).IsGenAt p c` using `fun q => exists_gen (L q.1) T (b₀ q.1) (h q.1) p hp q.2`. Use `choose s hs using hq`. Conclude with `⟨_, tens_isGenAt _ a p s hs⟩`.
-/
theorem grTens_exists_gen {S : Type} [Fintype S] {r : S → ℕ} (L : S → Lat ξ E) (b₀ : ∀ σ, Fin (r σ) → E)
    (a : (Σ σ, Fin (r σ)) → ℤ) (T : Set (Cpt ξ)) (h : ∀ σ, (L σ).IsFlagVBOn T (b₀ σ)) (p : Cpt ξ) (hp : p ∈ T) :
    ∃ c, (Lat.grTens L b₀ a).IsGenAt p c := by
  have hq : ∀ q : Σ σ, Fin (r σ), ∃ c, ((L q.1).gr (b₀ q.1) q.2).IsGenAt p c :=
    fun q => exists_gen (L q.1) T (b₀ q.1) (h q.1) p hp q.2
  choose s hs using hq
  exact ⟨_, tens_isGenAt _ a p s hs⟩

def jPlane (Ω : Type) [Field Ω] : (Fin 2 → Ω) →+ (Fin 2 → RatFunc Ω) :=
  ((algebraMap Ω (RatFunc Ω)).toAddMonoidHom).compLeft (Fin 2)

/- English proof (translation)
Establish `hj : ∀ (v : Fin 2 → Ω) (m : Fin 2), jPlane Ω v m = algebraMap Ω (RatFunc Ω) (v m)` using `fun _ _ => rfl`. Establish `hU : ∀ (ι : Type) (hι : Unique ι) (x : ι → RatFunc Ω), x default = RatFunc.X → AlgebraicIndependent Ω x`. Introduce `ι hι x hx`. Rewrite using `[algebraicIndependent_unique_type_iff, hx]`. Conclude with `RatFunc.transcendental_X`.

Establish `key : ∀ K : IntermediateField Ω (RatFunc Ω), RatFunc.X ∈ K → Module.finrank K (RatFunc Ω) = 1`. Introduce `K hK`. Establish `hK' : K = ⊤`. Rewrite using `[eq_top_iff, ← RatFunc.adjoin_X]`. Conclude with `IntermediateField.adjoin_simple_le_iff.mpr hK`.

Substitute `hK'` using the available equality. Conclude with `IntermediateField.finrank_top`. Use `⟨fun _ => ⇑(Pi.basisFun Ω (Fin 2)), fun _ => !![1, 0; RatFunc.X, 1], fun _ => ⟨(Pi.basisFun Ω (Fin 2)).linearIndependent, (Pi.basisFun Ω (Fin 2)).span_eq⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Nat.one_pos, ?_⟩` and prove the remaining obligations. Introduce `a e`. Use extensionality with `m`.

Simplify using `[hj, map_mul]`. Introduce `_`. Use `(Pi.basisFun (RatFunc Ω) (Fin 2)).linearIndependent using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first`. Consider the case `rfl`.

Consider the case `(ext k m fin_cases k <;> fin_cases m <;> simp [hj])`. Introduce `_`. Use `LinearIndependent.pair_iff.mpr fun s t h => ?_` and prove the remaining obligations. Establish `h0` using `congrFun h 0`. Establish `h1` using `congrFun h 1`.

Simplify using `at h0 h1`. Substitute `h0` using the available equality. Simplify using `using h1`. Apply the tactic sequence `intro _ k fin_cases k <;> simp`. Apply the tactic sequence `intro _ l k h fin_cases l <;> fin_cases k <;> simp at h ⊢`.

Introduce `_ i`. Use `congr 1`. Use extensionality with `k m`. Apply the tactic sequence `fin_cases k <;> fin_cases m <;> simp [hj, Fin.sum_univ_two, Finset.sum_apply]`. Use `hU _ ?_ _ ?_` and prove the remaining obligations.

Use `⟨⟨⟨(), ⟨(1, 0), by decide⟩⟩⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨⟨⟩, ⟨⟨l, k⟩, h⟩⟩`. Apply the tactic sequence `fin_cases l <;> fin_cases k <;> first | rfl | exact absurd h (by decide)`. Both sides reduce to the same expression. Conclude with `key _ (IntermediateField.subset_adjoin _ _ ⟨⟨(), (1, 0)⟩, by simp⟩)`.
-/
theorem isGenericFlag_plane :
    IsGenericFlag (Ω := Ω) (Ω' := RatFunc Ω) (jPlane Ω) (S := Unit) (r := fun _ => 2) (fun _ => ⊤)
      (fun _ => ![![1, RatFunc.X], ![0, 1]]) 1 := by
  have hj : ∀ (v : Fin 2 → Ω) (m : Fin 2), jPlane Ω v m = algebraMap Ω (RatFunc Ω) (v m) :=
    fun _ _ => rfl
  have hU : ∀ (ι : Type) (hι : Unique ι) (x : ι → RatFunc Ω), x default = RatFunc.X →
      AlgebraicIndependent Ω x := by
    intro ι hι x hx
    rw [algebraicIndependent_unique_type_iff, hx]
    exact RatFunc.transcendental_X
  have key : ∀ K : IntermediateField Ω (RatFunc Ω), RatFunc.X ∈ K →
      Module.finrank K (RatFunc Ω) = 1 := by
    intro K hK
    have hK' : K = ⊤ := by
      rw [eq_top_iff, ← RatFunc.adjoin_X]
      exact IntermediateField.adjoin_simple_le_iff.mpr hK
    subst hK'
    exact IntermediateField.finrank_top
  refine ⟨fun _ => ⇑(Pi.basisFun Ω (Fin 2)), fun _ => !![1, 0; RatFunc.X, 1],
    fun _ => ⟨(Pi.basisFun Ω (Fin 2)).linearIndependent, (Pi.basisFun Ω (Fin 2)).span_eq⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, Nat.one_pos, ?_⟩
  · intro a e
    ext m
    simp [hj, map_mul]
  · intro _
    convert (Pi.basisFun (RatFunc Ω) (Fin 2)).linearIndependent using 1
    all_goals first
      | rfl
      | (ext k m
         fin_cases k <;> fin_cases m <;> simp [hj])
  · intro _
    refine LinearIndependent.pair_iff.mpr fun s t h => ?_
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    subst h0
    simpa using h1
  · intro _ k
    fin_cases k <;> simp
  · intro _ l k h
    fin_cases l <;> fin_cases k <;> simp at h ⊢
  · intro _ i
    congr 1
    ext k m
    fin_cases k <;> fin_cases m <;> simp [hj, Fin.sum_univ_two, Finset.sum_apply]
  · refine hU _ ?_ _ ?_
    · refine ⟨⟨⟨(), ⟨(1, 0), by decide⟩⟩⟩, ?_⟩
      rintro ⟨⟨⟩, ⟨⟨l, k⟩, h⟩⟩
      fin_cases l <;> fin_cases k <;> first | rfl | exact absurd h (by decide)
    · rfl
  · exact key _ (IntermediateField.subset_adjoin _ _ ⟨⟨(), (1, 0)⟩, by simp⟩)

/- English proof (translation)
Introduce and unpack `⟨c, u, -, -, -, -, -, -, -, hai, -, -⟩`. Conclude with `hai.transcendental ⟨(), ⟨(1, 0), by decide⟩⟩ (isAlgebraic_algebraMap (R := Ω) (A := Ω) _)`.
-/
theorem not_isGenericFlag_self {E' : Type} [AddCommGroup E'] [Module Ω E'] (j : E →+ E') (V : Unit → Submodule Ω E)
    (b₀ : Unit → Fin 2 → E') (d : ℕ) : ¬ IsGenericFlag (Ω' := Ω) j (r := fun _ => 2) V b₀ d := by
  rintro ⟨c, u, -, -, -, -, -, -, -, hai, -, -⟩
  exact hai.transcendental ⟨(), ⟨(1, 0), by decide⟩⟩ (isAlgebraic_algebraMap (R := Ω) (A := Ω) _)

end GlobalTheory.CompanionTheory.Ar.FlagModel
