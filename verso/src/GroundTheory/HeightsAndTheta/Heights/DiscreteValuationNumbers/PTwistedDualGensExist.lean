import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsTwistedDualGensExist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Chart

variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω] {τ : Type*}
  {r : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

def TwistedDualGensExist.latSub {x : τ → Ω} (B : ChartBundle O x r E) (c : τ) :
    Submodule (chartRing O x c) E where
  carrier := B.lat c
  add_mem' := (B.lat c).add_mem
  zero_mem' := (B.lat c).zero_mem
  smul_mem' a e he := B.stable c a a.2 e he

def TwistedDualGensExist.dualSub {x : τ → Ω} (B : ChartBundle O x r E) (c : τ) :
    Submodule (chartRing O x c) (Module.Dual Ω E) where
  carrier := {ψ | ∀ v ∈ B.lat c, ψ v ∈ chartRing O x c}
  add_mem' {ψ χ} hψ hχ v hv := by
    simpa using add_mem (hψ v hv) (hχ v hv)
  zero_mem' v _ := by simp
  smul_mem' a ψ hψ v hv := by
    show ((a : Ω) • ψ) v ∈ _
    rw [LinearMap.smul_apply, smul_eq_mul]
    exact mul_mem a.2 (hψ v hv)

/- English proof (translation)
Use `set f' : Fin k → A := fun l => ⟨f l, hf l⟩ with hf'`. Establish `h1 : Ideal.span (Set.range f') = ⊤`. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `: (1 : A) = ∑ l, (⟨cc l, hcc l⟩ : A) * f' l` using `Subtype.ext (by simp [f', hsum])`. Rewrite using `[this]`.

Conclude with `Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)`. Establish `h2` using `Ideal.span_pow_eq_top _ h1 N`. Rewrite `h2` using `[← Set.range_comp]`. Establish `h3 : (1 : A) ∈ Ideal.span (Set.range ((fun z : A => z ^ N) ∘ f'))`. Rewrite using `[h2]`.

Discharge the goal by the elementary cases of `trivial`. Take `⟨g, hg⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 h3`. Use `⟨fun l => g l, fun l => (g l).2, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hg` as an intermediate fact. Simplify `this` using `[f']`.
-/
theorem TwistedDualGensExist.exists_pow_combination (A : Subalgebra O Ω) {k : ℕ} (f cc : Fin k → Ω)
    (hf : ∀ l, f l ∈ A) (hcc : ∀ l, cc l ∈ A) (hsum : ∑ l, cc l * f l = 1) (N : ℕ) :
    ∃ g : Fin k → Ω, (∀ l, g l ∈ A) ∧ ∑ l, g l * f l ^ N = 1 := by
  set f' : Fin k → A := fun l => ⟨f l, hf l⟩ with hf'
  have h1 : Ideal.span (Set.range f') = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have : (1 : A) = ∑ l, (⟨cc l, hcc l⟩ : A) * f' l := Subtype.ext (by simp [f', hsum])
    rw [this]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
  have h2 := Ideal.span_pow_eq_top _ h1 N
  rw [← Set.range_comp] at h2
  have h3 : (1 : A) ∈ Ideal.span (Set.range ((fun z : A => z ^ N) ∘ f')) := by
    rw [h2]; trivial
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h3
  refine ⟨fun l => g l, fun l => (g l).2, ?_⟩
  have := congrArg Subtype.val hg
  simpa [f'] using this

/- English proof (translation)
Take `⟨k, f, cc, hf, hcc, hsum, hb⟩` from `B.frame c hc`. Use `choose b hli hsp hiff using hb`. Apply the tactic sequence `have hbl : ∀ l q, ∃ n : ℕ, f l ^ n • b l q ∈ B.lat c := fun l q => (hiff l (b l q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by by_cases h : q' = q <;> simp [h]⟩, by simp [Pi.single_apply]⟩`. Use `choose n hn using hbl`. Use `⟨(Set.finite_range fun p : Fin k × Fin r => f p.1 ^ n p.1 p.2 • b p.1 p.2).toFinset, ?_⟩` and prove the remaining obligations.

Rewrite using `[Set.Finite.coe_toFinset]`. Use `set P := Submodule.span (chartRing O x c) (Set.range fun p : Fin k × Fin r => f p.1 ^ n p.1 p.2 • b p.1 p.2) with hP`. Establish `hsm : ∀ {a : Ω}, a ∈ chartRing O x c → ∀ {v : E}, v ∈ P → a • v ∈ P` using `fun {a} ha {v} hv => P.smul_mem (⟨a, ha⟩ : chartRing O x c) hv`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨p, rfl⟩`. Conclude with `hn p.1 p.2`. Introduce `e he`. Establish `he' : e ∈ B.lat c` using `he`. Establish `hloc : ∀ l, ∃ M : ℕ, ∀ M', M ≤ M' → f l ^ M' • e ∈ P`.

Introduce `l`. Take `⟨a, ha, hea⟩` from `(hiff l e).1 ⟨0, by simpa using he'⟩`. Use `choose m hm using ha`. Use `⟨∑ q, (m q + n l q), fun M' hM' => ?_⟩` and prove the remaining obligations. Rewrite using `[hea, Finset.smul_sum]`.

Use `Submodule.sum_mem _ fun q _ => ?_` and prove the remaining obligations. Establish `hq : m q + n l q ≤ M'` using `le_trans (Finset.single_le_sum (f := fun q => m q + n l q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)) hM'`. Establish `heq : f l ^ M' • a q • b l q = (f l ^ (M' - (m q + n l q)) * (f l ^ m q * a q)) • (f l ^ n l q • b l q)`. Rewrite using `[smul_smul, smul_smul]`. Use `congr 1`.

Rewrite using `[← Nat.sub_add_cancel hq]`. Simplify using `only [Nat.add_sub_cancel, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`. Conclude with `hsm (mul_mem (pow_mem (hf l) _) (hm q)) (Submodule.subset_span ⟨(l, q), rfl⟩)`.

Use `choose Ml hMl using hloc`. Take `⟨g, hg, hgsum⟩` from `TwistedDualGensExist.exists_pow_combination (chartRing O x c) f cc hf hcc hsum (∑ l, Ml l)`. Establish `: e = ∑ l, g l • (f l ^ (∑ l, Ml l) • e)`. Simplify using `only [smul_smul, ← Finset.sum_smul, hgsum, one_smul]`. Use `show e ∈ P`.

Rewrite using `[this]`. Use `Submodule.sum_mem _ fun l _ => hsm (hg l) (hMl l _ ?_)` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := Ml) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)`.
-/
theorem TwistedDualGensExist.latSub_fg {x : τ → Ω} (B : ChartBundle O x r E) {c : τ} (hc : x c ≠ 0) :
    (TwistedDualGensExist.latSub B c).FG := by
  obtain ⟨k, f, cc, hf, hcc, hsum, hb⟩ := B.frame c hc
  choose b hli hsp hiff using hb
  have hbl : ∀ l q, ∃ n : ℕ, f l ^ n • b l q ∈ B.lat c := fun l q =>
    (hiff l (b l q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by by_cases h : q' = q <;> simp [h]⟩,
      by simp [Pi.single_apply]⟩
  choose n hn using hbl
  refine ⟨(Set.finite_range fun p : Fin k × Fin r => f p.1 ^ n p.1 p.2 • b p.1 p.2).toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset]
  set P := Submodule.span (chartRing O x c)
    (Set.range fun p : Fin k × Fin r => f p.1 ^ n p.1 p.2 • b p.1 p.2) with hP
  have hsm : ∀ {a : Ω}, a ∈ chartRing O x c → ∀ {v : E}, v ∈ P → a • v ∈ P :=
    fun {a} ha {v} hv => P.smul_mem (⟨a, ha⟩ : chartRing O x c) hv
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact hn p.1 p.2
  · intro e he
    have he' : e ∈ B.lat c := he
    have hloc : ∀ l, ∃ M : ℕ, ∀ M', M ≤ M' → f l ^ M' • e ∈ P := by
      intro l
      obtain ⟨a, ha, hea⟩ := (hiff l e).1 ⟨0, by simpa using he'⟩
      choose m hm using ha
      refine ⟨∑ q, (m q + n l q), fun M' hM' => ?_⟩
      rw [hea, Finset.smul_sum]
      refine Submodule.sum_mem _ fun q _ => ?_
      have hq : m q + n l q ≤ M' :=
        le_trans (Finset.single_le_sum (f := fun q => m q + n l q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)) hM'
      have heq : f l ^ M' • a q • b l q =
          (f l ^ (M' - (m q + n l q)) * (f l ^ m q * a q)) • (f l ^ n l q • b l q) := by
        rw [smul_smul, smul_smul]
        congr 1
        rw [← Nat.sub_add_cancel hq]
        simp only [Nat.add_sub_cancel, pow_add]
        ring
      rw [heq]
      exact hsm (mul_mem (pow_mem (hf l) _) (hm q)) (Submodule.subset_span ⟨(l, q), rfl⟩)
    choose Ml hMl using hloc
    obtain ⟨g, hg, hgsum⟩ := TwistedDualGensExist.exists_pow_combination (chartRing O x c) f cc hf hcc
      hsum (∑ l, Ml l)
    have : e = ∑ l, g l • (f l ^ (∑ l, Ml l) • e) := by
      simp only [smul_smul, ← Finset.sum_smul, hgsum, one_smul]
    show e ∈ P
    rw [this]
    refine Submodule.sum_mem _ fun l _ => hsm (hg l) (hMl l _ ?_)
    exact Finset.single_le_sum (f := Ml) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)

/- English proof (translation)
Rewrite using `[← Nat.sub_add_cancel hn, pow_add, mul_assoc]`. Conclude with `mul_mem (pow_mem (div_mem_chartRing x c' c) _) h`.
-/
theorem TwistedDualGensExist.pow_mul_mem_mono {x : τ → Ω} {c c' : τ} {z : Ω} {n n' : ℕ}
    (h : (x c / x c') ^ n * z ∈ chartRing O x c') (hn : n ≤ n') :
    (x c / x c') ^ n' * z ∈ chartRing O x c' := by
  rw [← Nat.sub_add_cancel hn, pow_add, mul_assoc]
  exact mul_mem (pow_mem (div_mem_chartRing x c' c) _) h

/- English proof (translation)
Establish `: IsNoetherianRing (chartRing O x c)` using `isNoetherianRing_of_fg (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)`. Take `⟨k, f, cc, hf, hcc, hsum, hb⟩` from `B.frame c hc`. Use `choose b hli hsp hiff using hb`. Take `⟨l0, hl0⟩ : ∃ l0, f l0 ≠ 0` from `by by_contra! h`. Simplify using `[h] at hsum`.

Use `set β : Module.Basis (Fin r) Ω E := Module.Basis.mk (hli l0) (hsp l0).ge with hβdef`. Establish `hβ : ∀ q, β q = b l0 q` using `fun q => Module.Basis.mk_apply _ _ _`. Establish `hbl : ∀ q, ∃ n : ℕ, f l0 ^ n • β q ∈ B.lat c` using `fun q => by`. Rewrite using `[hβ]`. Apply the tactic sequence `exact (hiff l0 (b l0 q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by by_cases h : q' = q <;> simp [h]⟩, by simp [Pi.single_apply]⟩`.

Use `choose n hn using hbl`. Use `set N := ∑ q, n q with hNdef`. Establish `hN : ∀ q, f l0 ^ N • β q ∈ B.lat c`. Introduce `q`. Establish `hq : n q ≤ N` using `Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)`.

Establish `: f l0 ^ N • β q = f l0 ^ (N - n q) • (f l0 ^ n q • β q)`. Rewrite using `[smul_smul, ← pow_add, Nat.sub_add_cancel hq]`. Rewrite using `[this]`. Conclude with `B.stable c _ (pow_mem (hf l0) _) _ (hn q)`. Establish `hf0 : f l0 ^ N ≠ 0` using `pow_ne_zero _ hl0`.

Use `Submodule.FG.of_le (Submodule.fg_span (Set.finite_range fun q => (f l0 ^ N)⁻¹ • β.coord q)) ?_` and prove the remaining obligations. Introduce `ψ hψ`. Establish `hψ' : ∀ v ∈ B.lat c, ψ v ∈ chartRing O x c` using `hψ`. Rewrite using `[← β.sum_dual_apply_smul_coord ψ]`. Use `Submodule.sum_mem _ fun q _ => ?_` and prove the remaining obligations.

Establish `hmem : f l0 ^ N * ψ (β q) ∈ chartRing O x c`. Use `hψ' _ (hN q)` as an intermediate fact. Rewrite `this` using `[map_smul, smul_eq_mul]`. Then use the resulting hypothesis. Establish `: ψ (β q) • β.coord q = (⟨_, hmem⟩ : chartRing O x c) • ((f l0 ^ N)⁻¹ • β.coord q)` using `by show _ = (f l0 ^ N * ψ (β q)) • ((f l0 ^ N)⁻¹ • β.coord q)`. Rewrite using `[smul_smul]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)`.
-/
theorem TwistedDualGensExist.dualSub_fg [IsNoetherianRing O] [Fintype τ] {x : τ → Ω}
    (B : ChartBundle O x r E) {c : τ} (hc : x c ≠ 0) :
    (TwistedDualGensExist.dualSub B c).FG := by
  have : IsNoetherianRing (chartRing O x c) :=
    isNoetherianRing_of_fg (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
  obtain ⟨k, f, cc, hf, hcc, hsum, hb⟩ := B.frame c hc
  choose b hli hsp hiff using hb
  obtain ⟨l0, hl0⟩ : ∃ l0, f l0 ≠ 0 := by
    by_contra! h
    simp [h] at hsum
  set β : Module.Basis (Fin r) Ω E := Module.Basis.mk (hli l0) (hsp l0).ge with hβdef
  have hβ : ∀ q, β q = b l0 q := fun q => Module.Basis.mk_apply _ _ _
  have hbl : ∀ q, ∃ n : ℕ, f l0 ^ n • β q ∈ B.lat c := fun q => by
    rw [hβ]
    exact (hiff l0 (b l0 q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by by_cases h : q' = q <;> simp [h]⟩,
      by simp [Pi.single_apply]⟩
  choose n hn using hbl
  set N := ∑ q, n q with hNdef
  have hN : ∀ q, f l0 ^ N • β q ∈ B.lat c := by
    intro q
    have hq : n q ≤ N := Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    have : f l0 ^ N • β q = f l0 ^ (N - n q) • (f l0 ^ n q • β q) := by
      rw [smul_smul, ← pow_add, Nat.sub_add_cancel hq]
    rw [this]
    exact B.stable c _ (pow_mem (hf l0) _) _ (hn q)
  have hf0 : f l0 ^ N ≠ 0 := pow_ne_zero _ hl0
  refine Submodule.FG.of_le (Submodule.fg_span (Set.finite_range fun q => (f l0 ^ N)⁻¹ • β.coord q)) ?_
  intro ψ hψ
  have hψ' : ∀ v ∈ B.lat c, ψ v ∈ chartRing O x c := hψ
  rw [← β.sum_dual_apply_smul_coord ψ]
  refine Submodule.sum_mem _ fun q _ => ?_
  have hmem : f l0 ^ N * ψ (β q) ∈ chartRing O x c := by
    have := hψ' _ (hN q)
    rwa [map_smul, smul_eq_mul] at this
  have : ψ (β q) • β.coord q = (⟨_, hmem⟩ : chartRing O x c) • ((f l0 ^ N)⁻¹ • β.coord q) := by
    show _ = (f l0 ^ N * ψ (β q)) • ((f l0 ^ N)⁻¹ • β.coord q)
    rw [smul_smul]
    congr 1
    field_simp
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)

/- English proof (translation)
Take `⟨S, hS⟩` from `TwistedDualGensExist.dualSub_fg B hc`. Use `⟨S, fun ψ hψ => ?_, fun ψ' hψ' => ?_⟩` and prove the remaining obligations. Establish `: ψ ∈ TwistedDualGensExist.dualSub B c` using `hS ▸ Submodule.subset_span hψ`. Conclude with `this`. Establish `h : ψ' ∈ Submodule.span (chartRing O x c) (S : Set (Module.Dual Ω E))`.

Rewrite using `[hS]`. Conclude with `hψ'`. Take `⟨u, -, hu⟩` from `Submodule.mem_span_finset.1 h`. Conclude with `⟨fun ψ => u ψ, fun ψ => (u ψ).2, hu⟩`.
-/
theorem TwistedDualGensExist.exists_dual_gens [IsNoetherianRing O] [Fintype τ] {x : τ → Ω}
    (B : ChartBundle O x r E) {c : τ} (hc : x c ≠ 0) :
    ∃ S : Finset (Module.Dual Ω E), (∀ ψ ∈ S, ∀ v ∈ B.lat c, ψ v ∈ chartRing O x c) ∧
      ∀ ψ' : Module.Dual Ω E, (∀ v ∈ B.lat c, ψ' v ∈ chartRing O x c) →
        ∃ u : Module.Dual Ω E → Ω, (∀ ψ, u ψ ∈ chartRing O x c) ∧ ∑ ψ ∈ S, u ψ • ψ = ψ' := by
  obtain ⟨S, hS⟩ := TwistedDualGensExist.dualSub_fg B hc
  refine ⟨S, fun ψ hψ => ?_, fun ψ' hψ' => ?_⟩
  · have : ψ ∈ TwistedDualGensExist.dualSub B c := hS ▸ Submodule.subset_span hψ
    exact this
  · have h : ψ' ∈ Submodule.span (chartRing O x c) (S : Set (Module.Dual Ω E)) := by
      rw [hS]
      exact hψ'
    obtain ⟨u, -, hu⟩ := Submodule.mem_span_finset.1 h
    exact ⟨fun ψ => u ψ, fun ψ => (u ψ).2, hu⟩

/- English proof (translation)
Establish `hone : ∀ c', ∃ n : ℕ, x c' ≠ 0 → ∀ v ∈ B.lat c', (x c / x c') ^ n * ψ v ∈ chartRing O x c'`. Introduce `c'`. Distinguish the cases in `hc' : x c' = 0`. Conclude with `⟨0, fun h => (h hc').elim⟩`. Take `⟨S, hS⟩` from `TwistedDualGensExist.latSub_fg B hc'`.

Establish `hgen : ∀ v ∈ S, ∃ m : ℕ, (x c / x c') ^ m * ψ v ∈ chartRing O x c'`. Introduce `v hv`. Establish `hv' : v ∈ B.lat c'`. Establish `: v ∈ TwistedDualGensExist.latSub B c'` using `hS ▸ Submodule.subset_span hv`. Conclude with `this`.

Take `⟨m, hm⟩` from `B.overlap c' c hc' hc v hv'`. Establish `hw` using `hψ _ hm`. Rewrite `hw` using `[map_smul, smul_eq_mul]`. Take `⟨m', hm'⟩` from `exists_pow_mul_mem_chartRing x c c' hc hw`. Use `⟨m', ?_⟩` and prove the remaining obligations.

Establish `hu : (x c / x c') ^ m * (x c' / x c) ^ m = 1`. Rewrite using `[← mul_pow, div_mul_div_comm, mul_comm (x c), div_self (mul_ne_zero hc' hc), one_pow]`. Establish `: (x c / x c') ^ m' * ψ v = (x c / x c') ^ m * ((x c / x c') ^ m' * ((x c' / x c) ^ m * ψ v))`. Take the linear combination `(-(x c / x c') ^ m' * ψ v) * hu`. Rewrite using `[this]`.

Conclude with `mul_mem (pow_mem (div_mem_chartRing x c' c) _) hm'`. Use `choose! m hm using hgen`. Use `⟨∑ v ∈ S, m v, fun _ v hv => ?_⟩` and prove the remaining obligations. Establish `hv' : v ∈ Submodule.span (chartRing O x c') (S : Set E)`. Rewrite using `[hS]`.

Conclude with `hv`. Use `clear hv`. Proceed by induction on `hv' using Submodule.span_induction with`. Consider the case `mem w hw`. Conclude with `TwistedDualGensExist.pow_mul_mem_mono (hm w hw) (Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) hw)`.

Consider the case `zero => simp`. Consider the case `add w z _ _ hw hz`. Rewrite using `[map_add, mul_add]`. Conclude with `add_mem hw hz`. Consider the case `smul a w _ hw => show (x c / x c') ^ _ * ψ ((a : Ω) • w) ∈ _`.

Rewrite using `[map_smul, smul_eq_mul, mul_left_comm]`. Conclude with `mul_mem a.2 hw`. Use `choose n hn using hone`. Use `⟨∑ c', n c', fun c' hc' v hv => TwistedDualGensExist.pow_mul_mem_mono (hn c' hc' v hv) ?_⟩` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c')`.
-/
theorem TwistedDualGensExist.exists_twist [Fintype τ] {x : τ → Ω} (B : ChartBundle O x r E) {c : τ}
    (hc : x c ≠ 0) {ψ : Module.Dual Ω E} (hψ : ∀ v ∈ B.lat c, ψ v ∈ chartRing O x c) :
    ∃ n : ℕ, ∀ c', x c' ≠ 0 → ∀ v ∈ B.lat c', (x c / x c') ^ n * ψ v ∈ chartRing O x c' := by
  have hone : ∀ c', ∃ n : ℕ, x c' ≠ 0 → ∀ v ∈ B.lat c',
      (x c / x c') ^ n * ψ v ∈ chartRing O x c' := by
    intro c'
    by_cases hc' : x c' = 0
    · exact ⟨0, fun h => (h hc').elim⟩
    obtain ⟨S, hS⟩ := TwistedDualGensExist.latSub_fg B hc'
    have hgen : ∀ v ∈ S, ∃ m : ℕ, (x c / x c') ^ m * ψ v ∈ chartRing O x c' := by
      intro v hv
      have hv' : v ∈ B.lat c' := by
        have : v ∈ TwistedDualGensExist.latSub B c' := hS ▸ Submodule.subset_span hv
        exact this
      obtain ⟨m, hm⟩ := B.overlap c' c hc' hc v hv'
      have hw := hψ _ hm
      rw [map_smul, smul_eq_mul] at hw
      obtain ⟨m', hm'⟩ := exists_pow_mul_mem_chartRing x c c' hc hw
      refine ⟨m', ?_⟩
      have hu : (x c / x c') ^ m * (x c' / x c) ^ m = 1 := by
        rw [← mul_pow, div_mul_div_comm, mul_comm (x c), div_self (mul_ne_zero hc' hc), one_pow]
      have : (x c / x c') ^ m' * ψ v =
          (x c / x c') ^ m * ((x c / x c') ^ m' * ((x c' / x c) ^ m * ψ v)) := by
        linear_combination (-(x c / x c') ^ m' * ψ v) * hu
      rw [this]
      exact mul_mem (pow_mem (div_mem_chartRing x c' c) _) hm'
    choose! m hm using hgen
    refine ⟨∑ v ∈ S, m v, fun _ v hv => ?_⟩
    have hv' : v ∈ Submodule.span (chartRing O x c') (S : Set E) := by
      rw [hS]
      exact hv
    clear hv
    induction hv' using Submodule.span_induction with
    | mem w hw =>
      exact TwistedDualGensExist.pow_mul_mem_mono (hm w hw)
        (Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) hw)
    | zero => simp
    | add w z _ _ hw hz =>
      rw [map_add, mul_add]
      exact add_mem hw hz
    | smul a w _ hw =>
      show (x c / x c') ^ _ * ψ ((a : Ω) • w) ∈ _
      rw [map_smul, smul_eq_mul, mul_left_comm]
      exact mul_mem a.2 hw
  choose n hn using hone
  refine ⟨∑ c', n c', fun c' hc' v hv => TwistedDualGensExist.pow_mul_mem_mono (hn c' hc' v hv) ?_⟩
  exact Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c')

end Chart

section Segre

variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
  {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*}

/- English proof (translation)
Establish `hy : ∀ k', y ⟨k', c k'⟩ ≠ 0` using `fun k' => (Finset.prod_ne_zero_iff.1 hc) k' (Finset.mem_univ _)`. Establish `h` using `div_mem_chartRing (o := O) (segreVec y) c (Function.update c k j)`. Establish `e1 : segreVec y (Function.update c k j) = y ⟨k, j⟩ * ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩`. Rewrite using `[segreVec, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]`. Use `congr 1`.

Simplify using the standard rewrite rules. Use `Finset.prod_congr rfl fun k' hk' => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (Finset.ne_of_mem_erase hk')]`. Establish `e2 : segreVec y c = y ⟨k, c k⟩ * ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩`. Rewrite using `[segreVec, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]`.

Establish `hP : ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k' _ => hy k'`. Rewrite `h` using `[e1, e2, mul_div_mul_right _ _ hP]`. Conclude with `h`.
-/
theorem TwistedDualGensExist.ratio_mem (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} (hc : segreVec y c ≠ 0)
    (k : K) (j : ι k) : y ⟨k, j⟩ / y ⟨k, c k⟩ ∈ chartRing O (segreVec y) c := by
  have hy : ∀ k', y ⟨k', c k'⟩ ≠ 0 := fun k' => (Finset.prod_ne_zero_iff.1 hc) k' (Finset.mem_univ _)
  have h := div_mem_chartRing (o := O) (segreVec y) c (Function.update c k j)
  have e1 : segreVec y (Function.update c k j) =
      y ⟨k, j⟩ * ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ := by
    rw [segreVec, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
    congr 1
    · simp
    · refine Finset.prod_congr rfl fun k' hk' => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')]
  have e2 : segreVec y c = y ⟨k, c k⟩ * ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ := by
    rw [segreVec, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  have hP : ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => hy k'
  rw [e1, e2, mul_div_mul_right _ _ hP] at h
  exact h

/- English proof (translation)
Introduce `O _ _ Ω _ _ K _ ι _ y N E _ _ B`. Establish `hG : ∀ c : {c : ∀ k, ι k // segreVec y c ≠ 0}, ∃ S : Finset (Module.Dual Ω E), (∀ ψ ∈ S, ∀ v ∈ B.lat c.1, ψ v ∈ chartRing O (segreVec y) c.1) ∧ ∀ ψ' : Module.Dual Ω E, (∀ v ∈ B.lat c.1, ψ' v ∈ chartRing O (segreVec y) c.1) → ∃ u : Module.Dual Ω E → Ω, (∀ ψ, u ψ ∈ chartRing O (seg …` using `fun c => TwistedDualGensExist.exists_dual_gens B c.2`. Use `choose G hGmem hGgen using hG`. Establish `hT : ∀ (c : {c : ∀ k, ι k // segreVec y c ≠ 0}) (ψ : Module.Dual Ω E), ∃ n : ℕ, ψ ∈ G c → ∀ c', segreVec y c' ≠ 0 → ∀ v ∈ B.lat c', (segreVec y c.1 / segreVec y c') ^ n * ψ v ∈ chartRing O (segreVec y) c'`. Introduce `c ψ`.

Distinguish the cases in `h : ψ ∈ G c`. Take `⟨n, hn⟩` from `TwistedDualGensExist.exists_twist B c.2 (hGmem c ψ h)`. Conclude with `⟨n, fun _ => hn⟩`. Conclude with `⟨0, fun h' => (h h').elim⟩`. Use `choose nn hnn using hT`.

Use `set n : ℕ := ∑ c, ∑ ψ ∈ G c, nn c ψ with hn`. Establish `hle : ∀ c ψ, ψ ∈ G c → nn c ψ ≤ n`. Introduce `c ψ hψ`. Conclude with `le_trans (Finset.single_le_sum (f := nn c) (fun _ _ => Nat.zero_le _) hψ) (Finset.single_le_sum (f := fun c => ∑ ψ ∈ G c, nn c ψ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c))`. Use `⟨fun _ => (n : ℤ), fun a ha => ?_⟩` and prove the remaining obligations.

Take `⟨b, hab⟩ : ∃ b : K → ℕ, ∀ k, a k = (n : ℤ) + (b k : ℤ)` from `⟨fun k => (a k - n).toNat, fun k => by have h := ha k; dsimp only at h ⊢; omega⟩`. Establish `hy : ∀ c : ∀ k, ι k, segreVec y c ≠ 0 → ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun c hc k => (Finset.prod_ne_zero_iff.1 hc) k (Finset.mem_univ _)`. Establish `hprod : ∀ c : ∀ k, ι k, segreVec y c ≠ 0 → ∏ k, y ⟨k, c k⟩ ^ a k = segreVec y c ^ n * ∏ k, y ⟨k, c k⟩ ^ b k`. Introduce `c hc`. Rewrite using `[segreVec, ← Finset.prod_pow, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hab k, zpow_add₀ (hy c hc k), zpow_natCast, zpow_natCast]`. Use `set T : Finset (Module.Dual Ω E) := Finset.univ.biUnion G with hTdef`. Take `⟨Φ, hΦ⟩ : ∃ Φ : {c : ∀ k, ι k // segreVec y c ≠ 0} × T × (∀ k, ι k) → Module.Dual Ω E, ∀ c ψ d, Φ (c, ψ, d) = if (ψ : Module.Dual Ω E) ∈ G c then (segreVec y c.1 ^ n * ∏ k, y ⟨k, d k⟩ ^ b k) • (ψ : Module.Dual Ω E) else 0` from `⟨fun i => if (i.2.1 : Module.Dual Ω E) ∈ G i.1 then (segreVec y i.1.1 ^ n * ∏ k, y ⟨k, i.2.2 k⟩ ^ b k) • (i.2.1 : Module.Dual Ω E) else 0, fun _ _ _ => rfl⟩`. Take `⟨M, ⟨e⟩⟩ : ∃ M : ℕ, Nonempty ({c : ∀ k, ι k // segreVec y c ≠ 0} × T × (∀ k, ι k) ≃ Fin M)` from `⟨_, ⟨Fintype.equivFin _⟩⟩`.

Use `⟨M, fun l => Φ (e.symm l), ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce `c' hc' l v hv`. Take `⟨c, ψ, d⟩` from `e.symm l`. Rewrite using `[hΦ]`. Use `split_ifs with hψ`.

Use `⟨((segreVec y c.1 / segreVec y c') ^ n * (ψ : Module.Dual Ω E) v) * ∏ k, (y ⟨k, d k⟩ / y ⟨k, c' k⟩) ^ b k, mul_mem (TwistedDualGensExist.pow_mul_mem_mono (hnn c ψ hψ c' hc' v hv) (hle c ψ hψ)) (prod_mem fun k _ => pow_mem (TwistedDualGensExist.ratio_mem y hc' k (d k)) _), ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, smul_eq_mul, hprod c' hc', Finset.prod_congr rfl (fun k _ => div_pow _ _ _), Finset.prod_div_distrib, div_pow]`. Establish `h1 : segreVec y c' ^ n ≠ 0` using `pow_ne_zero _ hc'`. Establish `h2 : ∏ k, y ⟨k, c' k⟩ ^ b k ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy c' hc' k)`. Clear the denominators using the available nonvanishing facts.

Conclude with `⟨0, zero_mem _, by simp⟩`. Introduce `c' hc' ψ' hψ'`. Take `⟨u, hu, hsum⟩` from `hGgen ⟨c', hc'⟩ ψ' hψ'`. Use `set c'' : {c : ∀ k, ι k // segreVec y c ≠ 0} := ⟨c', hc'⟩ with hc''`. Take `⟨U, hU⟩ : ∃ U : {c : ∀ k, ι k // segreVec y c ≠ 0} × T × (∀ k, ι k) → Ω, ∀ c ψ d, U (c, ψ, d) = if c = c'' ∧ d = c' then u ψ else 0` from `⟨fun i => if i.1 = c'' ∧ i.2.2 = c' then u i.2.1 else 0, fun _ _ _ => rfl⟩`.

Use `⟨fun l => U (e.symm l), fun l => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only`. Take `⟨c, ψ, d⟩` from `e.symm l`. Rewrite using `[hU]`. Use `split_ifs`.

Use `exacts [hu _, zero_mem _]`. Establish `hYX : (∏ k, y ⟨k, c' k⟩ ^ (-a k)) * (segreVec y c' ^ n * ∏ k, y ⟨k, c' k⟩ ^ b k) = 1`. Rewrite using `[← hprod c' hc', ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_eq_one fun k _ => by rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hy c' hc' k))]`. Establish `hterm : ∀ c ψ d, (U (c, ψ, d) * ∏ k, y ⟨k, c' k⟩ ^ (-a k)) • Φ (c, ψ, d) = if c = c'' ∧ d = c' then (if (ψ : Module.Dual Ω E) ∈ G c'' then u ψ • (ψ : Module.Dual Ω E) else 0) else 0`.

Introduce `c ψ d`. Rewrite using `[hU, hΦ]`. Distinguish the cases in `h : c = c'' ∧ d = c'`. Rewrite using `[if_pos h, if_pos h]`. Take `⟨h1, h2⟩` from `h`.

Rewrite using `[h1, h2]`. Use `split_ifs with hψ`. Rewrite using `[smul_smul, mul_assoc, hYX, mul_one]`. Rewrite using `[smul_zero]`. Rewrite using `[if_neg h, if_neg h, zero_mul, zero_smul]`.

Establish `hre` using `Equiv.sum_comp e.symm (fun i => (U i * ∏ k, y ⟨k, c' k⟩ ^ (-a k)) • Φ i)`. Use `Eq.trans ?_ hre.symm` and prove the remaining obligations. Rewrite using `[Fintype.sum_prod_type, Fintype.sum_eq_single c'']`. Rewrite using `[Fintype.sum_prod_type]`. Simplify using `only [hterm, true_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Rewrite using `[Finset.sum_coe_sort T (fun ψ => if ψ ∈ G c'' then u ψ • ψ else 0), Finset.sum_ite_mem, Finset.inter_eq_right.2 (Finset.subset_biUnion_of_mem G (Finset.mem_univ c'')), hsum]`. Introduce `c hc`. Use `Finset.sum_eq_zero fun p _ => ?_` and prove the remaining obligations. Take `⟨ψ, d⟩` from `p`. Rewrite using `[hterm, if_neg fun h => hc h.1]`.
-/
theorem TwistedDualGensExist.proof : TwistedDualGensExist.Statement := by
  classical
  intro O _ _ Ω _ _ K _ ι _ y N E _ _ B
  have hG : ∀ c : {c : ∀ k, ι k // segreVec y c ≠ 0}, ∃ S : Finset (Module.Dual Ω E),
      (∀ ψ ∈ S, ∀ v ∈ B.lat c.1, ψ v ∈ chartRing O (segreVec y) c.1) ∧
      ∀ ψ' : Module.Dual Ω E, (∀ v ∈ B.lat c.1, ψ' v ∈ chartRing O (segreVec y) c.1) →
        ∃ u : Module.Dual Ω E → Ω, (∀ ψ, u ψ ∈ chartRing O (segreVec y) c.1) ∧
          ∑ ψ ∈ S, u ψ • ψ = ψ' :=
    fun c => TwistedDualGensExist.exists_dual_gens B c.2
  choose G hGmem hGgen using hG
  have hT : ∀ (c : {c : ∀ k, ι k // segreVec y c ≠ 0}) (ψ : Module.Dual Ω E), ∃ n : ℕ, ψ ∈ G c →
      ∀ c', segreVec y c' ≠ 0 → ∀ v ∈ B.lat c',
        (segreVec y c.1 / segreVec y c') ^ n * ψ v ∈ chartRing O (segreVec y) c' := by
    intro c ψ
    by_cases h : ψ ∈ G c
    · obtain ⟨n, hn⟩ := TwistedDualGensExist.exists_twist B c.2 (hGmem c ψ h)
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h' => (h h').elim⟩
  choose nn hnn using hT
  set n : ℕ := ∑ c, ∑ ψ ∈ G c, nn c ψ with hn
  have hle : ∀ c ψ, ψ ∈ G c → nn c ψ ≤ n := by
    intro c ψ hψ
    exact le_trans (Finset.single_le_sum (f := nn c) (fun _ _ => Nat.zero_le _) hψ)
      (Finset.single_le_sum (f := fun c => ∑ ψ ∈ G c, nn c ψ) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ c))
  refine ⟨fun _ => (n : ℤ), fun a ha => ?_⟩
  obtain ⟨b, hab⟩ : ∃ b : K → ℕ, ∀ k, a k = (n : ℤ) + (b k : ℤ) :=
    ⟨fun k => (a k - n).toNat, fun k => by have h := ha k; dsimp only at h ⊢; omega⟩
  have hy : ∀ c : ∀ k, ι k, segreVec y c ≠ 0 → ∀ k, y ⟨k, c k⟩ ≠ 0 :=
    fun c hc k => (Finset.prod_ne_zero_iff.1 hc) k (Finset.mem_univ _)
  have hprod : ∀ c : ∀ k, ι k, segreVec y c ≠ 0 →
      ∏ k, y ⟨k, c k⟩ ^ a k = segreVec y c ^ n * ∏ k, y ⟨k, c k⟩ ^ b k := by
    intro c hc
    rw [segreVec, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hab k, zpow_add₀ (hy c hc k), zpow_natCast, zpow_natCast]
  set T : Finset (Module.Dual Ω E) := Finset.univ.biUnion G with hTdef
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : {c : ∀ k, ι k // segreVec y c ≠ 0} × T × (∀ k, ι k) → Module.Dual Ω E,
      ∀ c ψ d, Φ (c, ψ, d) = if (ψ : Module.Dual Ω E) ∈ G c then
        (segreVec y c.1 ^ n * ∏ k, y ⟨k, d k⟩ ^ b k) • (ψ : Module.Dual Ω E) else 0 :=
    ⟨fun i => if (i.2.1 : Module.Dual Ω E) ∈ G i.1 then
      (segreVec y i.1.1 ^ n * ∏ k, y ⟨k, i.2.2 k⟩ ^ b k) • (i.2.1 : Module.Dual Ω E) else 0,
      fun _ _ _ => rfl⟩
  obtain ⟨M, ⟨e⟩⟩ : ∃ M : ℕ,
      Nonempty ({c : ∀ k, ι k // segreVec y c ≠ 0} × T × (∀ k, ι k) ≃ Fin M) :=
    ⟨_, ⟨Fintype.equivFin _⟩⟩
  refine ⟨M, fun l => Φ (e.symm l), ⟨?_, ?_⟩⟩
  · intro c' hc' l v hv
    obtain ⟨c, ψ, d⟩ := e.symm l
    rw [hΦ]
    split_ifs with hψ
    · refine ⟨((segreVec y c.1 / segreVec y c') ^ n * (ψ : Module.Dual Ω E) v) *
          ∏ k, (y ⟨k, d k⟩ / y ⟨k, c' k⟩) ^ b k,
        mul_mem (TwistedDualGensExist.pow_mul_mem_mono (hnn c ψ hψ c' hc' v hv) (hle c ψ hψ))
          (prod_mem fun k _ => pow_mem (TwistedDualGensExist.ratio_mem y hc' k (d k)) _), ?_⟩
      rw [LinearMap.smul_apply, smul_eq_mul, hprod c' hc',
        Finset.prod_congr rfl (fun k _ => div_pow _ _ _), Finset.prod_div_distrib, div_pow]
      have h1 : segreVec y c' ^ n ≠ 0 := pow_ne_zero _ hc'
      have h2 : ∏ k, y ⟨k, c' k⟩ ^ b k ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy c' hc' k)
      field_simp
    · exact ⟨0, zero_mem _, by simp⟩
  · intro c' hc' ψ' hψ'
    obtain ⟨u, hu, hsum⟩ := hGgen ⟨c', hc'⟩ ψ' hψ'
    set c'' : {c : ∀ k, ι k // segreVec y c ≠ 0} := ⟨c', hc'⟩ with hc''
    obtain ⟨U, hU⟩ : ∃ U : {c : ∀ k, ι k // segreVec y c ≠ 0} × T × (∀ k, ι k) → Ω,
        ∀ c ψ d, U (c, ψ, d) = if c = c'' ∧ d = c' then u ψ else 0 :=
      ⟨fun i => if i.1 = c'' ∧ i.2.2 = c' then u i.2.1 else 0, fun _ _ _ => rfl⟩
    refine ⟨fun l => U (e.symm l), fun l => ?_, ?_⟩
    · dsimp only
      obtain ⟨c, ψ, d⟩ := e.symm l
      rw [hU]
      split_ifs
      exacts [hu _, zero_mem _]
    have hYX : (∏ k, y ⟨k, c' k⟩ ^ (-a k)) * (segreVec y c' ^ n * ∏ k, y ⟨k, c' k⟩ ^ b k) = 1 := by
      rw [← hprod c' hc', ← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun k _ => by rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hy c' hc' k))]
    have hterm : ∀ c ψ d, (U (c, ψ, d) * ∏ k, y ⟨k, c' k⟩ ^ (-a k)) • Φ (c, ψ, d) =
        if c = c'' ∧ d = c' then
          (if (ψ : Module.Dual Ω E) ∈ G c'' then u ψ • (ψ : Module.Dual Ω E) else 0) else 0 := by
      intro c ψ d
      rw [hU, hΦ]
      by_cases h : c = c'' ∧ d = c'
      · rw [if_pos h, if_pos h]
        obtain ⟨h1, h2⟩ := h
        rw [h1, h2]
        split_ifs with hψ
        · rw [smul_smul, mul_assoc, hYX, mul_one]
        · rw [smul_zero]
      · rw [if_neg h, if_neg h, zero_mul, zero_smul]
    have hre := Equiv.sum_comp e.symm (fun i => (U i * ∏ k, y ⟨k, c' k⟩ ^ (-a k)) • Φ i)
    refine Eq.trans ?_ hre.symm
    rw [Fintype.sum_prod_type, Fintype.sum_eq_single c'']
    · rw [Fintype.sum_prod_type]
      simp only [hterm, true_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [Finset.sum_coe_sort T (fun ψ => if ψ ∈ G c'' then u ψ • ψ else 0), Finset.sum_ite_mem,
        Finset.inter_eq_right.2 (Finset.subset_biUnion_of_mem G (Finset.mem_univ c'')), hsum]
    · intro c hc
      refine Finset.sum_eq_zero fun p _ => ?_
      obtain ⟨ψ, d⟩ := p
      rw [hterm, if_neg fun h => hc h.1]

end Segre

end

end GroundTheory.Heights₂.Heights.NumbersDVR
