import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfLinearZeroCoboundaryZeroFractionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCoboundarySwapPullbackCommute

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog.Conv

section SlopeTestRemainingChoices

variable {O E : Type} [CommRing O] [CommRing E] [Algebra O E] {d : ℕ}

/- English proof (translation)
Take `⟨L, hL⟩` from `h.complete.toIsPrecomplete.prec (f := fun N => ∑ n ∈ Finset.range N, (p : O) ^ n * a n) (by`. Introduce `m n hmn`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← Finset.sum_range_add_sum_Ico _ hmn, sub_add_cancel_left]`. Conclude with `dvd_neg.2 (Finset.dvd_sum fun k hk => dvd_mul_of_dvd_left (pow_dvd_pow _ (Finset.mem_Ico.1 hk).1) _))`. Use `⟨L, fun N => ?_⟩` and prove the remaining obligations.

Establish `hN : (∑ n ∈ Finset.range N, (p : O) ^ n * a n) ≡ L [SMOD (Ideal.span {(p : O)}) ^ N • (⊤ : Submodule O O)]` using `hL N`. Rewrite `hN` using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Take `⟨c, hc⟩` from `hN`. Conclude with `⟨-c, by linear_combination -hc⟩`.
-/
theorem exists_lim {p : ℕ} (h : IsFrame p E (RingHom.id O)) (a : ℕ → O) :
    ∃ L : O, ∀ N : ℕ, ∃ c : O,
      L = ∑ n ∈ Finset.range N, (p : O) ^ n * a n + (p : O) ^ N * c := by
  obtain ⟨L, hL⟩ := h.complete.toIsPrecomplete.prec
    (f := fun N => ∑ n ∈ Finset.range N, (p : O) ^ n * a n) (by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton, ← Finset.sum_range_add_sum_Ico _ hmn, sub_add_cancel_left]
      exact dvd_neg.2 (Finset.dvd_sum fun k hk => dvd_mul_of_dvd_left
        (pow_dvd_pow _ (Finset.mem_Ico.1 hk).1) _))
  refine ⟨L, fun N => ?_⟩
  have hN : (∑ n ∈ Finset.range N, (p : O) ^ n * a n) ≡ L
      [SMOD (Ideal.span {(p : O)}) ^ N • (⊤ : Submodule O O)] := hL N
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hN
  obtain ⟨c, hc⟩ := hN
  exact ⟨-c, by linear_combination -hc⟩

/- English proof (translation)
Take `⟨b, hb⟩` from `hx 0`. Establish `h0 : (p : O) ^ 0 * b = 0` using `h.eq_zero_of_forall_pow_dvd fun N => by`. Take `⟨c, hc⟩` from `hx N`. Conclude with `⟨c, h.inj (hb.symm.trans hc)⟩`. Rewrite using `[hb, h0, map_zero]`.
-/
theorem eq_zero_of_forall {p : ℕ} (h : IsFrame p E (RingHom.id O)) {x : E}
    (hx : ∀ N : ℕ, ∃ b : O, x = algebraMap O E ((p : O) ^ N * b)) : x = 0 := by
  obtain ⟨b, hb⟩ := hx 0
  have h0 : (p : O) ^ 0 * b = 0 := h.eq_zero_of_forall_pow_dvd fun N => by
    obtain ⟨c, hc⟩ := hx N
    exact ⟨c, h.inj (hb.symm.trans hc)⟩
  rw [hb, h0, map_zero]

/- English proof (translation)
Unfold `comb`. Simplify using `only [map_add, map_mul, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]`.
-/
theorem comb_add_mul {ι : Type} [Fintype ι] (x y : ι → O) (c : O)
    (e : ι → MvPowerSeries (Fin d) E) :
    comb (fun i => x i + c * y i) e = comb x e + algebraMap O E c • comb y e := by
  unfold comb
  simp only [map_add, map_mul, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

def IntD (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (g : MvPowerSeries (Fin d) E) : Prop :=
  (∀ i, ∃ b : O, lin g i = algebraMap O E b) ∧ In (⊤ : Ideal O) (cob1 (up E μ) g)

variable {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O}

/- English proof (translation)
Simplify using `[up, hμ]`.
-/
theorem up_const (hμ : ∀ i, constantCoeff (μ i) = 0) (i : Fin d) :
    constantCoeff (up E μ i) = 0 := by
  simp [up, hμ]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i => (hg.2.1 i).imp fun _ hb => hb.2, hg.2.2⟩`.
-/
theorem IntD.ofQL {g : MvPowerSeries (Fin d) E} (hg : QL μ ⊤ g) : IntD μ g :=
  ⟨fun i => (hg.2.1 i).imp fun _ hb => hb.2, hg.2.2⟩

/- English proof (translation)
Establish `h0 : cob1 (up E μ) (0 : MvPowerSeries (Fin d) E) = 0`. Simplify using `using formalCoboundary_smul (up_const hμ) (0 : E) (0 : MvPowerSeries (Fin d) E)`. Use `⟨fun i => ⟨0, by simp [lin]⟩, fun α => ⟨0, trivial, by simp [h0]⟩⟩` and prove the remaining obligations.
-/
theorem IntD.zero (hμ : ∀ i, constantCoeff (μ i) = 0) : IntD μ (0 : MvPowerSeries (Fin d) E) := by
  have h0 : cob1 (up E μ) (0 : MvPowerSeries (Fin d) E) = 0 := by
    simpa using formalCoboundary_smul (up_const hμ) (0 : E) (0 : MvPowerSeries (Fin d) E)
  refine ⟨fun i => ⟨0, by simp [lin]⟩, fun α => ⟨0, trivial, by simp [h0]⟩⟩

/- English proof (translation)
Use `⟨fun i => ?_, fun α => ?_⟩` and prove the remaining obligations. Take `⟨b, hb⟩` from `hg.1 i`. Take `⟨b', hb'⟩` from `hg'.1 i`. Use `⟨b + b', ?_⟩` and prove the remaining obligations. Simplify using `only [lin, map_add] at hb hb' ⊢`.

Rewrite using `[hb, hb']`. Take `⟨b, -, hb⟩` from `hg.2 α`. Take `⟨b', -, hb'⟩` from `hg'.2 α`. Conclude with `⟨b + b', trivial, by rw [formalCoboundary_add (up_const hμ), map_add, hb, hb', map_add]⟩`.
-/
theorem IntD.add (hμ : ∀ i, constantCoeff (μ i) = 0) {g g' : MvPowerSeries (Fin d) E}
    (hg : IntD μ g) (hg' : IntD μ g') : IntD μ (g + g') := by
  refine ⟨fun i => ?_, fun α => ?_⟩
  · obtain ⟨b, hb⟩ := hg.1 i
    obtain ⟨b', hb'⟩ := hg'.1 i
    refine ⟨b + b', ?_⟩
    simp only [lin, map_add] at hb hb' ⊢
    rw [hb, hb']
  · obtain ⟨b, -, hb⟩ := hg.2 α
    obtain ⟨b', -, hb'⟩ := hg'.2 α
    exact ⟨b + b', trivial, by rw [formalCoboundary_add (up_const hμ), map_add, hb, hb', map_add]⟩

/- English proof (translation)
Use `⟨fun i => ?_, fun α => ?_⟩` and prove the remaining obligations. Take `⟨b, hb⟩` from `hg.1 i`. Use `⟨c * b, ?_⟩` and prove the remaining obligations. Simplify using `only [lin, coeff_smul] at hb ⊢`. Rewrite using `[hb, map_mul]`.

Take `⟨b, -, hb⟩` from `hg.2 α`. Conclude with `⟨c * b, trivial, by rw [formalCoboundary_smul (up_const hμ), coeff_smul, hb, map_mul]⟩`.
-/
theorem IntD.smul (hμ : ∀ i, constantCoeff (μ i) = 0) (c : O) {g : MvPowerSeries (Fin d) E}
    (hg : IntD μ g) : IntD μ (algebraMap O E c • g) := by
  refine ⟨fun i => ?_, fun α => ?_⟩
  · obtain ⟨b, hb⟩ := hg.1 i
    refine ⟨c * b, ?_⟩
    simp only [lin, coeff_smul] at hb ⊢
    rw [hb, map_mul]
  · obtain ⟨b, -, hb⟩ := hg.2 α
    exact ⟨c * b, trivial, by rw [formalCoboundary_smul (up_const hμ), coeff_smul, hb, map_mul]⟩

/- English proof (translation)
Establish `: g - g' = g + algebraMap O E (-1) • g'`. Rewrite using `[map_neg, map_one, neg_one_smul, sub_eq_add_neg]`. Rewrite using `[this]`. Conclude with `hg.add hμ (hg'.smul hμ _)`.
-/
theorem IntD.sub (hμ : ∀ i, constantCoeff (μ i) = 0) {g g' : MvPowerSeries (Fin d) E}
    (hg : IntD μ g) (hg' : IntD μ g') : IntD μ (g - g') := by
  have : g - g' = g + algebraMap O E (-1) • g' := by
    rw [map_neg, map_one, neg_one_smul, sub_eq_add_neg]
  rw [this]
  exact hg.add hμ (hg'.smul hμ _)

/- English proof (translation)
The claim follows from `Finset.sum_induction _ (IntD μ) (fun _ _ h1 h2 => h1.add hμ h2) (IntD.zero hμ) fun i _ => (he i).smul hμ (b i)`.
-/
theorem IntD.comb (hμ : ∀ i, constantCoeff (μ i) = 0) {ι : Type} [Fintype ι] (b : ι → O)
    {e : ι → MvPowerSeries (Fin d) E} (he : ∀ i, IntD μ (e i)) : IntD μ (comb b e) :=
  Finset.sum_induction _ (IntD μ) (fun _ _ h1 h2 => h1.add hμ h2) (IntD.zero hμ)
    fun i _ => (he i).smul hμ (b i)

/- English proof (translation)
Use `⟨fun i => ⟨coeff (Finsupp.single i 1) s, by simp [lin, coeff_map]⟩, ?_⟩` and prove the remaining obligations. Use `((map_cob_swap_pull O d μ hμ E (algebraMap O E)).1 s).symm` as an intermediate fact. Rewrite using `[show cob1 (up E μ) (MvPowerSeries.map (algebraMap O E) s) = MvPowerSeries.map (algebraMap O E) (cob1 μ s) from this]`. Conclude with `In.top_iff.2 ⟨_, rfl⟩`.
-/
theorem IntD.map (hμ : ∀ i, constantCoeff (μ i) = 0) (s : MvPowerSeries (Fin d) O) :
    IntD μ (MvPowerSeries.map (algebraMap O E) s) := by
  refine ⟨fun i => ⟨coeff (Finsupp.single i 1) s, by simp [lin, coeff_map]⟩, ?_⟩
  have := ((map_cob_swap_pull O d μ hμ E (algebraMap O E)).1 s).symm
  rw [show cob1 (up E μ) (MvPowerSeries.map (algebraMap O E) s) =
      MvPowerSeries.map (algebraMap O E) (cob1 μ s) from this]
  exact In.top_iff.2 ⟨_, rfl⟩

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `p _ O E _ _ _ h d μ hμ ι _ e he H f hf`. Establish `hc` using `hμ.const`. Use `choose! bf sf ff hQ hff using H`. Take `⟨F, hF0, hFs⟩ : ∃ F : ℕ → MvPowerSeries (Fin d) E, F 0 = f ∧ ∀ n, F (n + 1) = ff (F n)` from `⟨fun n => ff^[n] f, rfl, fun n => Function.iterate_succ_apply' ff n f⟩`. Establish `hFQ : ∀ n, QL μ ⊤ (F n)`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => rw [hF0]`. Conclude with `hf`. Consider the case `succ n ih => rw [hFs]`.

Conclude with `hQ _ ih`. Establish `step : ∀ n, F n = comb (bf (F n)) e + map (algebraMap O E) (sf (F n)) + (p : E) • F (n + 1)` using `fun n => by rw [hFs]; exact hff _ (hFQ n)`. Establish `hpE : ∀ N : ℕ, (p : E) ^ N = algebraMap O E ((p : O) ^ N)` using `fun N => by`. Rewrite using `[map_pow, map_natCast]`. Establish `tele : ∀ N : ℕ, f = comb (fun i => ∑ n ∈ Finset.range N, (p : O) ^ n * bf (F n) i) e + ∑ n ∈ Finset.range N, (p : E) ^ n • map (algebraMap O E) (sf (F n)) + (p : E) ^ N • F N`.

Introduce `N`. Proceed by induction on `N with`. Consider the case `zero`. Establish `: comb (fun _ : ι => (0 : O)) e = 0` using `by simp [comb]`. Simplify using `only [Finset.range_zero, Finset.sum_empty, this, pow_zero, one_smul, zero_add, hF0]`.

Consider the case `succ N ih`. Simplify using `only [Finset.sum_range_succ]`. Rewrite using `[comb_add_mul, ← hpE]`. Establish `hs` using `step N`. Rewrite `*` using `[ih]`.

Take the linear combination `(norm := module) ((p : E) ^ N) • hs`. Use `choose Bv hB using fun i => exists_lim h (fun n => bf (F n) i)`. Use `choose Sc hS using fun α => exists_lim h (fun n => coeff α (sf (F n)))`. Take `⟨S, hSd⟩ : ∃ S : MvPowerSeries (Fin d) O, ∀ α, coeff α S = Sc α` from `⟨Sc, fun _ => rfl⟩`. Establish `key : ∀ N : ℕ, ∃ g, Conv.IntD μ g ∧ f - comb Bv e - map (algebraMap O E) S = (p : E) ^ N • g`.

Introduce `N`. Use `choose cB hcB using fun i => hB i N`. Use `choose cS hcS using fun α => hS α N`. Take `⟨T, hTd⟩ : ∃ T : MvPowerSeries (Fin d) O, ∀ α, coeff α T = cS α` from `⟨cS, fun _ => rfl⟩`. Use `⟨F N - comb cB e - map (algebraMap O E) T, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `((IntD.ofQL (hFQ N)).sub hc (IntD.comb hc cB fun i => IntD.ofQL (he i))).sub hc (IntD.map hc T)`. Establish `h1 : comb Bv e = comb (fun i => ∑ n ∈ Finset.range N, (p : O) ^ n * bf (F n) i) e + (p : E) ^ N • comb cB e`. Rewrite using `[hpE, ← comb_add_mul]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Conclude with `hcB i`. Establish `h2 : map (algebraMap O E) S = ∑ n ∈ Finset.range N, (p : E) ^ n • map (algebraMap O E) (sf (F n)) + (p : E) ^ N • map (algebraMap O E) T`. Use extensionality with `α`. Rewrite using `[coeff_map, hSd, hcS α, map_add, map_add, coeff_smul, coeff_map, hTd, map_sum (coeff α)]`. Simplify using `only [coeff_smul, coeff_map, map_sum, map_mul, map_pow, map_natCast]`.

Rewrite using `[h1, h2]`. Take the linear combination `(norm := module) tele N`. Establish `hR : f - comb Bv e - map (algebraMap O E) S = 0`. Use `GlobalTheory.T.eq_zero_of_lin_zero_cob1_zero p O E h d μ hμ _ ?_ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Use `Conv.eq_zero_of_forall h fun N => ?_` and prove the remaining obligations. Take `⟨g, hg, hgN⟩` from `key N`. Take `⟨b, hb⟩` from `hg.1 i`. Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite using `[hgN]`.

Simplify using `only [lin, coeff_smul] at hb ⊢`. Rewrite using `[hb, hpE, map_mul]`. Use extensionality with `α`. Rewrite using `[coeff_zero]`. Use `Conv.eq_zero_of_forall h fun N => ?_` and prove the remaining obligations.

Take `⟨g, hg, hgN⟩` from `key N`. Take `⟨b, -, hb⟩` from `hg.2 α`. Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite using `[hgN, formalCoboundary_smul (up_const hc), coeff_smul, hb, hpE, map_mul]`. Conclude with `⟨Bv, In.top_iff.2 ⟨S, (sub_eq_zero.1 hR).symm⟩⟩`.
-/
theorem generate_of_step : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) E), (∀ i, QL μ ⊤ (e i)) → (∀ f, QL μ ⊤ f → ∃ (b : ι → O) (s : MvPowerSeries (Fin d) O) (f₁ : MvPowerSeries (Fin d) E), QL μ ⊤ f₁ ∧ f = comb b e + map (algebraMap O E) s + (p : E) • f₁) → ∀ f, QL μ ⊤ f → ∃ b : ι → O, In (⊤ : Ideal O) (f - comb b e) := by
  intro p _ O E _ _ _ h d μ hμ ι _ e he H f hf
  have hc := hμ.const
  choose! bf sf ff hQ hff using H
  obtain ⟨F, hF0, hFs⟩ : ∃ F : ℕ → MvPowerSeries (Fin d) E, F 0 = f ∧ ∀ n, F (n + 1) = ff (F n) :=
    ⟨fun n => ff^[n] f, rfl, fun n => Function.iterate_succ_apply' ff n f⟩
  have hFQ : ∀ n, QL μ ⊤ (F n) := by
    intro n
    induction n with
    | zero => rw [hF0]; exact hf
    | succ n ih => rw [hFs]; exact hQ _ ih
  have step : ∀ n, F n = comb (bf (F n)) e + map (algebraMap O E) (sf (F n)) + (p : E) • F (n + 1) :=
    fun n => by rw [hFs]; exact hff _ (hFQ n)
  have hpE : ∀ N : ℕ, (p : E) ^ N = algebraMap O E ((p : O) ^ N) := fun N => by
    rw [map_pow, map_natCast]
  have tele : ∀ N : ℕ, f = comb (fun i => ∑ n ∈ Finset.range N, (p : O) ^ n * bf (F n) i) e +
      ∑ n ∈ Finset.range N, (p : E) ^ n • map (algebraMap O E) (sf (F n)) + (p : E) ^ N • F N := by
    intro N
    induction N with
    | zero =>
      have : comb (fun _ : ι => (0 : O)) e = 0 := by simp [comb]
      simp only [Finset.range_zero, Finset.sum_empty, this, pow_zero, one_smul, zero_add, hF0]
    | succ N ih =>
      simp only [Finset.sum_range_succ]
      rw [comb_add_mul, ← hpE]
      have hs := step N
      rw [ih] at *
      linear_combination (norm := module) ((p : E) ^ N) • hs
  choose Bv hB using fun i => exists_lim h (fun n => bf (F n) i)
  choose Sc hS using fun α => exists_lim h (fun n => coeff α (sf (F n)))
  obtain ⟨S, hSd⟩ : ∃ S : MvPowerSeries (Fin d) O, ∀ α, coeff α S = Sc α := ⟨Sc, fun _ => rfl⟩
  have key : ∀ N : ℕ, ∃ g, Conv.IntD μ g ∧
      f - comb Bv e - map (algebraMap O E) S = (p : E) ^ N • g := by
    intro N
    choose cB hcB using fun i => hB i N
    choose cS hcS using fun α => hS α N
    obtain ⟨T, hTd⟩ : ∃ T : MvPowerSeries (Fin d) O, ∀ α, coeff α T = cS α := ⟨cS, fun _ => rfl⟩
    refine ⟨F N - comb cB e - map (algebraMap O E) T, ?_, ?_⟩
    · exact ((IntD.ofQL (hFQ N)).sub hc (IntD.comb hc cB fun i => IntD.ofQL (he i))).sub hc
        (IntD.map hc T)
    · have h1 : comb Bv e = comb (fun i => ∑ n ∈ Finset.range N, (p : O) ^ n * bf (F n) i) e +
          (p : E) ^ N • comb cB e := by
        rw [hpE, ← comb_add_mul]
        congr 1
        funext i
        exact hcB i
      have h2 : map (algebraMap O E) S =
          ∑ n ∈ Finset.range N, (p : E) ^ n • map (algebraMap O E) (sf (F n)) +
            (p : E) ^ N • map (algebraMap O E) T := by
        ext α
        rw [coeff_map, hSd, hcS α, map_add, map_add, coeff_smul, coeff_map, hTd, map_sum (coeff α)]
        simp only [coeff_smul, coeff_map, map_sum, map_mul, map_pow, map_natCast]
      rw [h1, h2]
      linear_combination (norm := module) tele N
  have hR : f - comb Bv e - map (algebraMap O E) S = 0 := by
    refine GlobalTheory.T.eq_zero_of_lin_zero_cob1_zero p O E h d μ hμ _ ?_ ?_
    · funext i
      refine Conv.eq_zero_of_forall h fun N => ?_
      obtain ⟨g, hg, hgN⟩ := key N
      obtain ⟨b, hb⟩ := hg.1 i
      refine ⟨b, ?_⟩
      rw [hgN]
      simp only [lin, coeff_smul] at hb ⊢
      rw [hb, hpE, map_mul]
    · ext α
      rw [coeff_zero]
      refine Conv.eq_zero_of_forall h fun N => ?_
      obtain ⟨g, hg, hgN⟩ := key N
      obtain ⟨b, -, hb⟩ := hg.2 α
      refine ⟨b, ?_⟩
      rw [hgN, formalCoboundary_smul (up_const hc), coeff_smul, hb, hpE, map_mul]
  exact ⟨Bv, In.top_iff.2 ⟨S, (sub_eq_zero.1 hR).symm⟩⟩

end GlobalTheory.QLog.Conv
