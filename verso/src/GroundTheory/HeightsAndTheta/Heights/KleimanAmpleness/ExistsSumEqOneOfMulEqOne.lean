import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraTer
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemClosureOfMemChartRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)

noncomputable section

section Loc

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

/- English proof (translation)
Establish `he0 : e ≠ 0`. Introduce and unpack `rfl`. Establish `h0 : (⟨0, hAB he⟩ : B) = 0` using `rfl`. Conclude with `heP (h0 ▸ P.zero_mem)`. Establish `hpow : ∀ M : ℕ, (⟨e, hAB he⟩ : B) ^ M ∉ P` using `fun M h => heP (hP.mem_of_pow_mem M h)`.

Apply `le_antisymm` to reduce the goal to its premises. Use `Subring.closure_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, b, hb, rfl⟩`. Take `⟨K, hK⟩` from `hB a.2`. Take `⟨K', hK'⟩` from `hB b.2`.

Establish `ha' : e ^ (K + K') * a ∈ A`. Rewrite using `[pow_add, mul_comm (e ^ K), mul_assoc]`. Conclude with `A.mul_mem (A.pow_mem he _) hK`. Establish `hb' : e ^ (K + K') * b ∈ A`. Rewrite using `[pow_add, mul_assoc]`.

Conclude with `A.mul_mem (A.pow_mem he _) hK'`. Use `Subring.subset_closure ⟨⟨_, ha'⟩, ⟨_, hb'⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.mem_comap]`. Introduce `h`. Establish `h' : (⟨e, hAB he⟩ : B) ^ (K + K') * b ∈ P`.

Use `h using 1` and compare the differences between its conclusion and the goal. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Break down `hP.mem_or_mem h' with h1 | h1` into its components or cases. Conclude with `hpow _ h1`.

Conclude with `hb h1`. Simplify using `only`. Rewrite using `[mul_div_mul_left _ _ (pow_ne_zero _ he0)]`. Use `Subring.closure_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, b, hb, rfl⟩`.

Conclude with `Subring.subset_closure ⟨Subalgebra.inclusion hAB a, Subalgebra.inclusion hAB b, hb, rfl⟩`.
-/
theorem locIn_eq_of_le_powMulMem {A B : Subalgebra S Ω} (hAB : A ≤ B) {e : Ω} (he : e ∈ A)
    (hB : B ≤ powMulMem A e he) (P : Ideal B) (hP : P.IsPrime) (heP : (⟨e, hAB he⟩ : B) ∉ P) :
    IndefiniteRowSideFullHecke.Kleiman2.locIn B P = IndefiniteRowSideFullHecke.Kleiman2.locIn A (P.comap (Subalgebra.inclusion hAB)) := by
  have he0 : e ≠ 0 := by
    rintro rfl
    have h0 : (⟨0, hAB he⟩ : B) = 0 := rfl
    exact heP (h0 ▸ P.zero_mem)
  have hpow : ∀ M : ℕ, (⟨e, hAB he⟩ : B) ^ M ∉ P := fun M h => heP (hP.mem_of_pow_mem M h)
  apply le_antisymm
  · refine Subring.closure_le.mpr ?_
    rintro _ ⟨a, b, hb, rfl⟩
    obtain ⟨K, hK⟩ := hB a.2
    obtain ⟨K', hK'⟩ := hB b.2
    have ha' : e ^ (K + K') * a ∈ A := by
      rw [pow_add, mul_comm (e ^ K), mul_assoc]; exact A.mul_mem (A.pow_mem he _) hK
    have hb' : e ^ (K + K') * b ∈ A := by
      rw [pow_add, mul_assoc]; exact A.mul_mem (A.pow_mem he _) hK'
    refine Subring.subset_closure ⟨⟨_, ha'⟩, ⟨_, hb'⟩, ?_, ?_⟩
    · rw [Ideal.mem_comap]
      intro h
      have h' : (⟨e, hAB he⟩ : B) ^ (K + K') * b ∈ P := by
        convert h using 1
        apply Subtype.ext
        simp
      rcases hP.mem_or_mem h' with h1 | h1
      · exact hpow _ h1
      · exact hb h1
    · simp only
      rw [mul_div_mul_left _ _ (pow_ne_zero _ he0)]
  · refine Subring.closure_le.mpr ?_
    rintro _ ⟨a, b, hb, rfl⟩
    exact Subring.subset_closure ⟨Subalgebra.inclusion hAB a, Subalgebra.inclusion hAB b, hb, rfl⟩

/- English proof (translation)
Establish `hpow : ∀ M : ℕ, (⟨e, he⟩ : A) ^ M ∉ p` using `fun M h => hep (hp.mem_of_pow_mem M h)`. Set `P : Ideal B` to `{ carrier := {b | ∃ M : ℕ, ∃ a ∈ p, e ^ M * (b : Ω) = (a : Ω)} add_mem' := by`. Introduce and unpack `b b' ⟨M, a, ha, hab⟩ ⟨M', a', ha', hab'⟩`. Use `⟨M + M', ⟨e, he⟩ ^ M' * a + ⟨e, he⟩ ^ M * a', p.add_mem (p.mul_mem_left _ ha) (p.mul_mem_left _ ha'), ?_⟩` and prove the remaining obligations. Simplify using `only [Subalgebra.coe_add, Subalgebra.coe_mul, SubmonoidClass.coe_pow]`.

Rewrite using `[← hab, ← hab']`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `zero_mem' := ⟨0, 0, p.zero_mem, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c b ⟨M, a, ha, hab⟩`.

Take `⟨K, hK⟩` from `hB c.2`. Use `⟨K + M, ⟨_, hK⟩ * a, p.mul_mem_left _ ha, ?_⟩` and prove the remaining obligations. Simplify using `only [smul_eq_mul, Subalgebra.coe_mul]`. Rewrite using `[← hab]`. Use `ring }`.

Establish `hmemP : ∀ b : B, b ∈ P ↔ ∃ M : ℕ, ∃ a ∈ p, e ^ M * (b : Ω) = (a : Ω)` using `fun _ => Iff.rfl`. Establish `hPprime : P.IsPrime`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.ne_top_iff_one, hmemP]`. Introduce and unpack `⟨M, a, ha, hab⟩`.

Apply `hpow M` to reduce the goal to its premises. Use `ha using 1` and compare the differences between its conclusion and the goal. Conclude with `Subtype.ext (by simpa using hab)`. Introduce `b b' hbb`. Take `⟨M, a, ha, hab⟩` from `(hmemP _).mp hbb`.

Take `⟨K, hK⟩` from `hB b.2`. Take `⟨K', hK'⟩` from `hB b'.2`. Establish `h1 : (⟨e, he⟩ : A) ^ M * ((⟨_, hK⟩ : A) * ⟨_, hK'⟩) = ⟨e, he⟩ ^ (K + K') * a`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subalgebra.coe_mul, SubmonoidClass.coe_pow]`.

Rewrite using `[← hab]`. Simplify using `only [Subalgebra.coe_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (⟨e, he⟩ : A) ^ M * ((⟨_, hK⟩ : A) * ⟨_, hK'⟩) ∈ p`. Rewrite using `[h1]`.

Conclude with `p.mul_mem_left _ ha`. Break down `hp.mem_or_mem h2 with h3 | h3` into its components or cases. Conclude with `absurd h3 (hpow M)`. Break down `hp.mem_or_mem h3 with h4 | h4` into its components or cases. Conclude with `Or.inl ⟨K, _, h4, rfl⟩`.

Conclude with `Or.inr ⟨K', _, h4, rfl⟩`. Establish `heP : (⟨e, hAB he⟩ : B) ∉ P`. Introduce and unpack `⟨M, a, ha, hab⟩`. Apply `hpow (M + 1)` to reduce the goal to its premises. Use `ha using 1` and compare the differences between its conclusion and the goal.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [SubmonoidClass.coe_pow]`. Rewrite using `[← hab, pow_succ]`. Establish `hcomap : P.comap (Subalgebra.inclusion hAB) = p`. Use extensionality with `a`.

Rewrite using `[Ideal.mem_comap]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨M, a', ha', hab⟩`. Establish `h1 : (⟨e, he⟩ : A) ^ M * a = a'`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `using hab`. Establish `h2 : (⟨e, he⟩ : A) ^ M * a ∈ p` using `by rw [h1]; exact ha'`. Break down `hp.mem_or_mem h2 with h3 | h3` into its components or cases. Conclude with `absurd h3 (hpow M)`. Conclude with `h3`.

Introduce `ha`. Conclude with `⟨0, a, ha, by simp⟩`. Use `⟨P, hPprime, ?_⟩` and prove the remaining obligations. Rewrite using `[locIn_eq_of_le_powMulMem hAB he hB P hPprime heP, hcomap]`.
-/
theorem exists_isPrime_locIn_eq {A B : Subalgebra S Ω} (hAB : A ≤ B) {e : Ω} (he : e ∈ A)
    (hB : B ≤ powMulMem A e he) (p : Ideal A) (hp : p.IsPrime) (hep : (⟨e, he⟩ : A) ∉ p) :
    ∃ P : Ideal B, P.IsPrime ∧ IndefiniteRowSideFullHecke.Kleiman2.locIn B P = IndefiniteRowSideFullHecke.Kleiman2.locIn A p := by
  have hpow : ∀ M : ℕ, (⟨e, he⟩ : A) ^ M ∉ p := fun M h => hep (hp.mem_of_pow_mem M h)
  let P : Ideal B :=
    { carrier := {b | ∃ M : ℕ, ∃ a ∈ p, e ^ M * (b : Ω) = (a : Ω)}
      add_mem' := by
        rintro b b' ⟨M, a, ha, hab⟩ ⟨M', a', ha', hab'⟩
        refine ⟨M + M', ⟨e, he⟩ ^ M' * a + ⟨e, he⟩ ^ M * a',
          p.add_mem (p.mul_mem_left _ ha) (p.mul_mem_left _ ha'), ?_⟩
        simp only [Subalgebra.coe_add, Subalgebra.coe_mul, SubmonoidClass.coe_pow]
        rw [← hab, ← hab']
        ring
      zero_mem' := ⟨0, 0, p.zero_mem, by simp⟩
      smul_mem' := by
        rintro c b ⟨M, a, ha, hab⟩
        obtain ⟨K, hK⟩ := hB c.2
        refine ⟨K + M, ⟨_, hK⟩ * a, p.mul_mem_left _ ha, ?_⟩
        simp only [smul_eq_mul, Subalgebra.coe_mul]
        rw [← hab]
        ring }
  have hmemP : ∀ b : B, b ∈ P ↔ ∃ M : ℕ, ∃ a ∈ p, e ^ M * (b : Ω) = (a : Ω) := fun _ => Iff.rfl
  have hPprime : P.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, hmemP]
      rintro ⟨M, a, ha, hab⟩
      apply hpow M
      convert ha using 1
      exact Subtype.ext (by simpa using hab)
    · intro b b' hbb
      obtain ⟨M, a, ha, hab⟩ := (hmemP _).mp hbb
      obtain ⟨K, hK⟩ := hB b.2
      obtain ⟨K', hK'⟩ := hB b'.2
      have h1 : (⟨e, he⟩ : A) ^ M * ((⟨_, hK⟩ : A) * ⟨_, hK'⟩) = ⟨e, he⟩ ^ (K + K') * a := by
        apply Subtype.ext
        simp only [Subalgebra.coe_mul, SubmonoidClass.coe_pow]
        rw [← hab]
        simp only [Subalgebra.coe_mul]
        ring
      have h2 : (⟨e, he⟩ : A) ^ M * ((⟨_, hK⟩ : A) * ⟨_, hK'⟩) ∈ p := by
        rw [h1]; exact p.mul_mem_left _ ha
      rcases hp.mem_or_mem h2 with h3 | h3
      · exact absurd h3 (hpow M)
      rcases hp.mem_or_mem h3 with h4 | h4
      · exact Or.inl ⟨K, _, h4, rfl⟩
      · exact Or.inr ⟨K', _, h4, rfl⟩
  have heP : (⟨e, hAB he⟩ : B) ∉ P := by
    rintro ⟨M, a, ha, hab⟩
    apply hpow (M + 1)
    convert ha using 1
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow]
    rw [← hab, pow_succ]
  have hcomap : P.comap (Subalgebra.inclusion hAB) = p := by
    ext a
    rw [Ideal.mem_comap]
    constructor
    · rintro ⟨M, a', ha', hab⟩
      have h1 : (⟨e, he⟩ : A) ^ M * a = a' := by
        apply Subtype.ext
        simpa using hab
      have h2 : (⟨e, he⟩ : A) ^ M * a ∈ p := by rw [h1]; exact ha'
      rcases hp.mem_or_mem h2 with h3 | h3
      · exact absurd h3 (hpow M)
      · exact h3
    · intro ha
      exact ⟨0, a, ha, by simp⟩
  refine ⟨P, hPprime, ?_⟩
  rw [locIn_eq_of_le_powMulMem hAB he hB P hPprime heP, hcomap]

/- English proof (translation)
Establish `hone : (1 : Ω) ∈ Submodule.span A (Set.range g) * Q'`. Rewrite using `[hQQ]`. Conclude with `Submodule.mem_one.mpr ⟨1, map_one _⟩`. Choose the witnesses or unpack the hypotheses as in `⟨w, hwQ, hsum⟩ : ∃ w : Fin m → Ω, (∀ b, w b ∈ Q') ∧ ∑ b, g b * w b = 1 := by`. Use `Submodule.mul_induction_on (C := fun z => ∃ w : Fin m → Ω, (∀ b, w b ∈ Q') ∧ ∑ b, g b * w b = z) hone ?_ ?_` and prove the remaining obligations.

Introduce `q hq q' hq'`. Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun A).mp hq`. Use `⟨fun b => (a b : Ω) * q', fun b => Q'.smul_mem (a b) hq', ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[Subalgebra.smul_def, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `_ _ ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩`. Use `⟨w + w', fun b => Q'.add_mem (hw b) (hw' b), ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl fun b _ => by simp [mul_add]`. Use `⟨w, fun a b => ?_, hsum⟩` and prove the remaining obligations. Establish `h` using `Submodule.mul_mem_mul (Submodule.subset_span ⟨a, rfl⟩ : g a ∈ Submodule.span A (Set.range g)) (hwQ b)`. Rewrite `h` using `[hQQ, Submodule.mem_one]`. Take `⟨y, hy⟩` from `h`.

Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem exists_sum_eq_one_of_mul_eq_one (A : Subalgebra S Ω) (Q' : Submodule A Ω) {m : ℕ} (g : Fin m → Ω)
    (hQQ : Submodule.span A (Set.range g) * Q' = 1) :
    ∃ w : Fin m → Ω, (∀ a b, g a * w b ∈ A) ∧ ∑ b, g b * w b = 1 := by
  classical
  have hone : (1 : Ω) ∈ Submodule.span A (Set.range g) * Q' := by
    rw [hQQ]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  obtain ⟨w, hwQ, hsum⟩ : ∃ w : Fin m → Ω, (∀ b, w b ∈ Q') ∧ ∑ b, g b * w b = 1 := by
    refine Submodule.mul_induction_on
      (C := fun z => ∃ w : Fin m → Ω, (∀ b, w b ∈ Q') ∧ ∑ b, g b * w b = z) hone ?_ ?_
    · intro q hq q' hq'
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hq
      refine ⟨fun b => (a b : Ω) * q', fun b => Q'.smul_mem (a b) hq', ?_⟩
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Subalgebra.smul_def, smul_eq_mul]
      ring
    · rintro _ _ ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩
      refine ⟨w + w', fun b => Q'.add_mem (hw b) (hw' b), ?_⟩
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by simp [mul_add]
  refine ⟨w, fun a b => ?_, hsum⟩
  have h := Submodule.mul_mem_mul (Submodule.subset_span ⟨a, rfl⟩ : g a ∈ Submodule.span A (Set.range g))
    (hwQ b)
  rw [hQQ, Submodule.mem_one] at h
  obtain ⟨y, hy⟩ := h
  rw [← hy]
  exact y.2

end Loc

section Graph

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N m : ℕ} {x : Fin (N + 1) → Ω}

/- English proof (translation)
Use `set I := Kleiman.singleChart hi with hIdef`. Establish `hiI : i ∈ I.1` using `Finset.mem_singleton_self i`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨b, rfl⟩`.

Establish `hb : s b ∈ (Q.twist (Kleiman.twistSys S x n)).sub I`. Rewrite using `[← hgen I]`. Conclude with `Submodule.subset_span ⟨b, rfl⟩`. Take `⟨y, hy, hyb⟩` from `(TranslateEq.mem_twist_twistSys_iff Q.toSubSystem n I hiI (s b)).mp hb`. Establish `: x i ^ (-n) * s b = y`.

Rewrite using `[hyb, smul_eq_mul, zpow_neg, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero n hi), one_mul]`. Use `show x i ^ (-n) * s b ∈ Q.sub I`. Rewrite using `[this]`. Conclude with `hy`. Introduce `y hy`.

Establish `hy' : x i ^ n * y ∈ Submodule.span (Kleiman.chartRing S x I) (Set.range s)`. Rewrite using `[hgen I]`. Conclude with `(TranslateEq.mem_twist_twistSys_iff Q.toSubSystem n I hiI _).mpr ⟨y, hy, rfl⟩`. Take `⟨a, ha⟩` from `(Submodule.mem_span_range_iff_exists_fun _).mp hy'`. Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`.

Use `⟨a, ?_⟩` and prove the remaining obligations. Simplify using `only [Subalgebra.smul_def, smul_eq_mul] at ha ⊢`. Establish `: ∑ b, (a b : Ω) * (x i ^ (-n) * s b) = x i ^ (-n) * ∑ b, (a b : Ω) * s b`. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring`. Rewrite using `[this, ha, zpow_neg, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero n hi), one_mul]`.
-/
theorem span_graphGens_eq (Q : Kleiman.LineBundle S x) (n : ℤ) (s : Fin m → Ω) (hgen : IsGraphGen Q n s)
    {i : Fin (N + 1)} (hi : x i ≠ 0) :
    Submodule.span (Kleiman.chartRing S x (Kleiman.singleChart hi)) (Set.range fun b => x i ^ (-n) * s b) =
      Q.sub (Kleiman.singleChart hi) := by
  set I := Kleiman.singleChart hi with hIdef
  have hiI : i ∈ I.1 := Finset.mem_singleton_self i
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    have hb : s b ∈ (Q.twist (Kleiman.twistSys S x n)).sub I := by
      rw [← hgen I]; exact Submodule.subset_span ⟨b, rfl⟩
    obtain ⟨y, hy, hyb⟩ := (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem n I hiI (s b)).mp hb
    have : x i ^ (-n) * s b = y := by
      rw [hyb, smul_eq_mul, zpow_neg, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero n hi), one_mul]
    show x i ^ (-n) * s b ∈ Q.sub I
    rw [this]
    exact hy
  · intro y hy
    have hy' : x i ^ n * y ∈ Submodule.span (Kleiman.chartRing S x I) (Set.range s) := by
      rw [hgen I]
      exact (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem n I hiI _).mpr ⟨y, hy, rfl⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hy'
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨a, ?_⟩
    simp only [Subalgebra.smul_def, smul_eq_mul] at ha ⊢
    have : ∑ b, (a b : Ω) * (x i ^ (-n) * s b) = x i ^ (-n) * ∑ b, (a b : Ω) * s b := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
    rw [this, ha, zpow_neg, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero n hi), one_mul]

/- English proof (translation)
Take `⟨Q', hQ'⟩` from `Q.invertible (Kleiman.singleChart hi)`. Rewrite `hQ'` using `[← span_graphGens_eq Q n s hgen hi]`. Take `⟨w, hw, hsum⟩` from `exists_sum_eq_one_of_mul_eq_one _ Q' _ hQ'`. Use `⟨w, fun a b => ?_, hsum⟩` and prove the remaining obligations. Rewrite using `[chartRingOver_oneBlock x (fun _ => i) hi]`.

Conclude with `hw a b`.
-/
theorem exists_graph_inverse (Q : Kleiman.LineBundle S x) (n : ℤ) (s : Fin m → Ω) (hgen : IsGraphGen Q n s)
    {i : Fin (N + 1)} (hi : x i ≠ 0) :
    ∃ w : Fin m → Ω, (∀ a b, x i ^ (-n) * s a * w b ∈ chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i)) ∧
      ∑ b, x i ^ (-n) * s b * w b = 1 := by
  obtain ⟨Q', hQ'⟩ := Q.invertible (Kleiman.singleChart hi)
  rw [← span_graphGens_eq Q n s hgen hi] at hQ'
  obtain ⟨w, hw, hsum⟩ := exists_sum_eq_one_of_mul_eq_one _ Q' _ hQ'
  refine ⟨w, fun a b => ?_, hsum⟩
  rw [chartRingOver_oneBlock x (fun _ => i) hi]
  exact hw a b

/- English proof (translation)
Establish `hA` using `chartRingOver_oneBlock (S := S) x (fun _ => i) hi`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hA]`. Conclude with `chartRing_le_graphRing x s hi j`. Use `graphRing_le x s hi j _ (fun a ha => ⟨0, ?_⟩) fun c => ⟨1, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_zero, one_mul, hA]`. Conclude with `ha`. Establish `: (x i ^ (-n) * s j * w b) ^ 1 * (s c / s j) = x i ^ (-n) * s c * w b`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`.

Conclude with `hw c b`.
-/
theorem graphRing_between {i : Fin (N + 1)} (hi : x i ≠ 0) (n : ℤ) (s : Fin m → Ω) (w : Fin m → Ω)
    (hw : ∀ a b, x i ^ (-n) * s a * w b ∈ chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i))
    {j : Fin m} (hj : s j ≠ 0) (b : Fin m) :
    chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i) ≤ graphRing S x s i j ∧
      graphRing S x s i j ≤ powMulMem _ _ (hw j b) := by
  have hA := chartRingOver_oneBlock (S := S) x (fun _ => i) hi
  refine ⟨?_, ?_⟩
  · rw [hA]; exact chartRing_le_graphRing x s hi j
  · refine graphRing_le x s hi j _ (fun a ha => ⟨0, ?_⟩) fun c => ⟨1, ?_⟩
    · rw [pow_zero, one_mul, hA]; exact ha
    · have : (x i ^ (-n) * s j * w b) ^ 1 * (s c / s j) = x i ^ (-n) * s c * w b := by
        field_simp
      rw [this]
      exact hw c b

end Graph

/- English proof (translation)
Introduce `S _ N Ω _ _ x Q n m s hx hgen`. Take `⟨i₀, hi₀⟩` from `hx`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `(⟨⟩ | ⟨⟩)`. Conclude with `⟨i₀, hi₀⟩`.

Take `⟨w, -, hsum⟩` from `exists_graph_inverse Q n s hgen hi₀`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `h0 : ∀ b, s b = 0` using `fun b => h b`. Simplify using `[h0] at hsum`.

Use `show IndefiniteRowSideFullHecke.Kleiman2.modelPts S (graphVec x s) = IndefiniteRowSideFullHecke.Kleiman2.modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc, P, hP, rfl⟩`. Take `⟨i, j, rfl⟩ : ∃ (i : Fin (N + 1)) (j : Fin m), c = graphChart i j` from `⟨c (Sum.inl ()), c (Sum.inr ()), graphChart_eta c⟩`.

Establish `hi : x i ≠ 0` using `hc (Sum.inl ())`. Establish `hj : s j ≠ 0` using `hc (Sum.inr ())`. Take `⟨w, hw, hsum⟩` from `exists_graph_inverse Q n s hgen hi`. Establish `hB : ∀ b, chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i) ≤ graphRing S x s i j ∧ graphRing S x s i j ≤ powMulMem _ _ (hw j b)` using `graphRing_between hi n s w hw hj`. Take `⟨hAB, -⟩` from `hB j`.

Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b, (⟨_, hAB (hw j b)⟩ : graphRing S x s i j) ∉ P := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Apply `hP.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`.

Establish `h1 : (1 : graphRing S x s i j) = ∑ b, (⟨s b / s j, div_mem_graphRing_inr x s i j b⟩ : graphRing S x s i j) * ⟨_, hAB (hw j b)⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subalgebra.coe_one, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul]`. Rewrite using `[← hsum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Clear the denominators using the available nonvanishing facts. Rewrite using `[h1]`. Conclude with `Ideal.sum_mem _ fun b _ => P.mul_mem_left _ (h b)`. Take `⟨hAB', hle⟩` from `hB b`. Establish `hP' : (P.comap (Subalgebra.inclusion hAB')).IsPrime` using `Ideal.comap_isPrime _ _`.

Use `⟨fun _ => i, fun _ => hi, _, hP', ?_⟩` and prove the remaining obligations. Conclude with `locIn_eq_of_le_powMulMem hAB' (hw j b) hle P hP hb`. Introduce and unpack `⟨c, hc, p, hp, rfl⟩`. Take `⟨i, rfl⟩ : ∃ i : Fin (N + 1), c = fun _ => i` from `⟨c (), funext fun u => rfl⟩`. Establish `hi : x i ≠ 0` using `hc ()`.

Take `⟨w, hw, hsum⟩` from `exists_graph_inverse Q n s hgen hi`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, (⟨_, hw j j⟩ : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i)) ∉ p := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Apply `hp.ne_top` to reduce the goal to its premises.

Rewrite using `[Ideal.eq_top_iff_one]`. Establish `h1 : (1 : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i)) = ∑ b, ⟨_, hw b b⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subalgebra.coe_one, AddSubmonoidClass.coe_finsetSum]`. Conclude with `hsum.symm`.

Rewrite using `[h1]`. Conclude with `Ideal.sum_mem _ fun b _ => h b`. Establish `hsj : s j ≠ 0`. Introduce `h0`. Apply `hj` to reduce the goal to its premises.

Establish `: (⟨_, hw j j⟩ : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i)) = 0` using `Subtype.ext (by simp [h0])`. Rewrite using `[this]`. Conclude with `p.zero_mem`. Take `⟨hAB, hle⟩` from `graphRing_between hi n s w hw hsj j`. Take `⟨P, hP, hPeq⟩` from `exists_isPrime_locIn_eq hAB (hw j j) hle p hp hj`.

Use `⟨graphChart i j, ?_, P, hP, hPeq.symm⟩` and prove the remaining obligations. Introduce and unpack `(⟨⟩ | ⟨⟩)`. Conclude with `hi`. Conclude with `hsj`.
-/
theorem GraphModel.full : GraphModel.Statement := by
  intro S _ N Ω _ _ x Q n m s hx hgen
  obtain ⟨i₀, hi₀⟩ := hx
  refine ⟨?_, ?_⟩
  · rintro (⟨⟩ | ⟨⟩)
    · exact ⟨i₀, hi₀⟩
    · obtain ⟨w, -, hsum⟩ := exists_graph_inverse Q n s hgen hi₀
      by_contra h
      push Not at h
      have h0 : ∀ b, s b = 0 := fun b => h b
      simp [h0] at hsum
  · show IndefiniteRowSideFullHecke.Kleiman2.modelPts S (graphVec x s) = IndefiniteRowSideFullHecke.Kleiman2.modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)
    ext z
    constructor
    · rintro ⟨c, hc, P, hP, rfl⟩
      obtain ⟨i, j, rfl⟩ : ∃ (i : Fin (N + 1)) (j : Fin m), c = graphChart i j :=
        ⟨c (Sum.inl ()), c (Sum.inr ()), graphChart_eta c⟩
      have hi : x i ≠ 0 := hc (Sum.inl ())
      have hj : s j ≠ 0 := hc (Sum.inr ())
      obtain ⟨w, hw, hsum⟩ := exists_graph_inverse Q n s hgen hi
      have hB : ∀ b, chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i) ≤ graphRing S x s i j ∧
          graphRing S x s i j ≤ powMulMem _ _ (hw j b) := graphRing_between hi n s w hw hj
      obtain ⟨hAB, -⟩ := hB j
      obtain ⟨b, hb⟩ : ∃ b, (⟨_, hAB (hw j b)⟩ : graphRing S x s i j) ∉ P := by
        by_contra h
        push Not at h
        apply hP.ne_top
        rw [Ideal.eq_top_iff_one]
        have h1 : (1 : graphRing S x s i j) =
            ∑ b, (⟨s b / s j, div_mem_graphRing_inr x s i j b⟩ : graphRing S x s i j) * ⟨_, hAB (hw j b)⟩ := by
          apply Subtype.ext
          simp only [Subalgebra.coe_one, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul]
          rw [← hsum]
          refine Finset.sum_congr rfl fun b _ => ?_
          field_simp
        rw [h1]
        exact Ideal.sum_mem _ fun b _ => P.mul_mem_left _ (h b)
      obtain ⟨hAB', hle⟩ := hB b
      have hP' : (P.comap (Subalgebra.inclusion hAB')).IsPrime := Ideal.comap_isPrime _ _
      refine ⟨fun _ => i, fun _ => hi, _, hP', ?_⟩
      exact locIn_eq_of_le_powMulMem hAB' (hw j b) hle P hP hb
    · rintro ⟨c, hc, p, hp, rfl⟩
      obtain ⟨i, rfl⟩ : ∃ i : Fin (N + 1), c = fun _ => i := ⟨c (), funext fun u => rfl⟩
      have hi : x i ≠ 0 := hc ()
      obtain ⟨w, hw, hsum⟩ := exists_graph_inverse Q n s hgen hi
      obtain ⟨j, hj⟩ : ∃ j, (⟨_, hw j j⟩ : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i)) ∉ p := by
        by_contra h
        push Not at h
        apply hp.ne_top
        rw [Ideal.eq_top_iff_one]
        have h1 : (1 : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i)) = ∑ b, ⟨_, hw b b⟩ := by
          apply Subtype.ext
          simp only [Subalgebra.coe_one, AddSubmonoidClass.coe_finsetSum]
          exact hsum.symm
        rw [h1]
        exact Ideal.sum_mem _ fun b _ => h b
      have hsj : s j ≠ 0 := by
        intro h0
        apply hj
        have : (⟨_, hw j j⟩ : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i)) = 0 :=
          Subtype.ext (by simp [h0])
        rw [this]
        exact p.zero_mem
      obtain ⟨hAB, hle⟩ := graphRing_between hi n s w hw hsj j
      obtain ⟨P, hP, hPeq⟩ := exists_isPrime_locIn_eq hAB (hw j j) hle p hp hj
      refine ⟨graphChart i j, ?_, P, hP, hPeq.symm⟩
      rintro (⟨⟩ | ⟨⟩)
      · exact hi
      · exact hsj

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
