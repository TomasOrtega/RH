import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA.RegDense

open scoped Polynomial

noncomputable def cay {F K : Type} [Field F] [Field K] [Algebra F K] (d β : F) (p q r n e : K) : Q d β K :=
  ⟨(1 + e ^ 2 * n) / (1 - e ^ 2 * n), 2 * e * p / (1 - e ^ 2 * n), 2 * e * q / (1 - e ^ 2 * n),
    2 * e * r / (1 - e ^ 2 * n)⟩

/- English proof (translation)
Simplify using `only [qn, cay]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hn]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qn_cay {F K : Type} [Field F] [Field K] [Algebra F K] (d β : F) (p q r n e : K)
    (hn : n = algebraMap F K d * p ^ 2 + algebraMap F K β * q ^ 2
      - algebraMap F K d * algebraMap F K β * r ^ 2)
    (h : 1 - e ^ 2 * n ≠ 0) : qn (cay d β p q r n e) = 1 := by
  simp only [qn, cay]
  field_simp
  rw [hn]
  ring

/- English proof (translation)
Establish `hD : algebraMap F K d ≠ 0` using `by simpa using hd`. Establish `hB : algebraMap F K β ≠ 0` using `by simpa using hb`. Establish `hex : ∃ p q r n : K, n = algebraMap F K d * p ^ 2 + algebraMap F K β * q ^ 2 - algebraMap F K d * algebraMap F K β * r ^ 2 ∧ n ≠ 0 ∧ n ≠ 1`. Distinguish the cases in `h1 : algebraMap F K d = 1`. Distinguish the cases in `h3 : algebraMap F K β = 1`.

Use `⟨0, 0, 1, -1, by rw [h1, h3]; ring, by simp, ?_⟩` and prove the remaining obligations. Introduce `h`. Apply `h2` to reduce the goal to its premises. Take the linear combination `-h`. Conclude with `⟨0, 1, 0, _, rfl, by simpa using hB, by simpa using h3⟩`.

Conclude with `⟨1, 0, 0, _, rfl, by simpa using hD, by simpa using h1⟩`. Take `⟨p, q, r, n, hn, hn0, hn1⟩` from `hex`. Establish `hW : 1 - (1 : K) ^ 2 * n ≠ 0`. Introduce `h`. Apply `hn1` to reduce the goal to its premises.

Take the linear combination `-h`. Use `⟨cay d β p q r n 1, qn_cay d β p q r n 1 hn hW, ?_⟩` and prove the remaining obligations. Introduce `h`. Establish `hW' : 1 - n ≠ 0` using `by simpa using hW`. Simplify using `only [cay, one_pow, one_mul] at h`.

Rewrite `h` using `[div_pow, div_eq_one_iff_eq (pow_ne_zero 2 hW')]`. Establish `h4 : (2 : K) * 2 * n = 0` using `by linear_combination h`. Conclude with `(mul_ne_zero (mul_ne_zero h2 h2) hn0) h4`.
-/
theorem exists_regular {F K : Type} [Field F] [Field K] [Algebra F K] (d β : F)
    (h2 : (2 : K) ≠ 0) (hd : d ≠ 0) (hb : β ≠ 0) :
    ∃ b : Q d β K, qn b = 1 ∧ b.re ^ 2 ≠ 1 := by
  have hD : algebraMap F K d ≠ 0 := by simpa using hd
  have hB : algebraMap F K β ≠ 0 := by simpa using hb
  have hex : ∃ p q r n : K, n = algebraMap F K d * p ^ 2 + algebraMap F K β * q ^ 2
      - algebraMap F K d * algebraMap F K β * r ^ 2 ∧ n ≠ 0 ∧ n ≠ 1 := by
    by_cases h1 : algebraMap F K d = 1
    · by_cases h3 : algebraMap F K β = 1
      · refine ⟨0, 0, 1, -1, by rw [h1, h3]; ring, by simp, ?_⟩
        intro h
        apply h2
        linear_combination -h
      · exact ⟨0, 1, 0, _, rfl, by simpa using hB, by simpa using h3⟩
    · exact ⟨1, 0, 0, _, rfl, by simpa using hD, by simpa using h1⟩
  obtain ⟨p, q, r, n, hn, hn0, hn1⟩ := hex
  have hW : 1 - (1 : K) ^ 2 * n ≠ 0 := by
    intro h
    apply hn1
    linear_combination -h
  refine ⟨cay d β p q r n 1, qn_cay d β p q r n 1 hn hW, ?_⟩
  intro h
  have hW' : 1 - n ≠ 0 := by simpa using hW
  simp only [cay, one_pow, one_mul] at h
  rw [div_pow, div_eq_one_iff_eq (pow_ne_zero 2 hW')] at h
  have h4 : (2 : K) * 2 * n = 0 := by linear_combination h
  exact (mul_ne_zero (mul_ne_zero h2 h2) hn0) h4

/- English proof (translation)
Take `⟨V, hV, h1⟩` from `hV`. Establish `key : ∀ r : K, ∀ᶠ e in 𝓝[≠] (0 : K), e ≠ r`. Introduce `r`. Distinguish the cases in `hr : r = 0`. Substitute `hr` using the available equality.

Conclude with `eventually_mem_nhdsWithin`. Establish `hc : ContinuousAt (fun x : K => x * r⁻¹) 0` using `by fun_prop`. Establish `hm : (fun x : K => x * r⁻¹) ⁻¹' V ∈ 𝓝 (0 : K)` using `hc (by simpa using hV)`. Use `Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_` and prove the remaining obligations. Use `filter_upwards [hm] with e he hne`.

Substitute `hne` using the available equality. Apply `h1` to reduce the goal to its premises. Simplify `he` using `[hr]`. Establish `hall` using `(Filter.eventually_all_finset P.roots.toFinset).2 (fun r _ => key r)`. Use `filter_upwards [hall] with e he h0`.

Conclude with `he e (by simp [hP, Polynomial.IsRoot, h0]) rfl`.
-/
theorem eventually_eval_ne {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
    (hV : ∃ V ∈ 𝓝 (0 : K), (1 : K) ∉ V) (P : K[X]) (hP : P ≠ 0) :
    ∀ᶠ e in 𝓝[≠] (0 : K), P.eval e ≠ 0 := by
  obtain ⟨V, hV, h1⟩ := hV
  have key : ∀ r : K, ∀ᶠ e in 𝓝[≠] (0 : K), e ≠ r := by
    intro r
    by_cases hr : r = 0
    · subst hr
      exact eventually_mem_nhdsWithin
    · have hc : ContinuousAt (fun x : K => x * r⁻¹) 0 := by fun_prop
      have hm : (fun x : K => x * r⁻¹) ⁻¹' V ∈ 𝓝 (0 : K) := hc (by simpa using hV)
      refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
      filter_upwards [hm] with e he hne
      subst hne
      apply h1
      simpa [hr] using he
  classical
  have hall := (Filter.eventually_all_finset P.roots.toFinset).2 (fun r _ => key r)
  filter_upwards [hall] with e he h0
  exact he e (by simp [hP, Polynomial.IsRoot, h0]) rfl

/- English proof (translation)
Establish `hW : (1 : K) - 0 ^ 2 * n ≠ 0` using `by simp`. Establish `hden : ContinuousAt (fun e : K => 1 - e ^ 2 * n) 0` using `by fun_prop`. Establish `h1 : ContinuousAt (fun e : K => (1 + e ^ 2 * n) / (1 - e ^ 2 * n)) 0` using `ContinuousAt.div (by fun_prop) hden hW`. Establish `h2 : ∀ t : K, ContinuousAt (fun e : K => 2 * e * t / (1 - e ^ 2 * n)) 0` using `fun t => ContinuousAt.div (by fun_prop) hden hW`. Use `(qHomeo (d := d) (β := β) (R := K)).isInducing.continuousAt_iff.2 ?_` and prove the remaining obligations.

Conclude with `h1.prodMk ((h2 p).prodMk ((h2 q).prodMk (h2 r)))`.
-/
theorem continuousAt_cay {F K : Type} [Field F] [Field K] [Algebra F K] [TopologicalSpace K]
    [IsTopologicalDivisionRing K] (d β : F) (p q r n : K) :
    ContinuousAt (fun e : K => cay d β p q r n e) 0 := by
  have hW : (1 : K) - 0 ^ 2 * n ≠ 0 := by simp
  have hden : ContinuousAt (fun e : K => 1 - e ^ 2 * n) 0 := by fun_prop
  have h1 : ContinuousAt (fun e : K => (1 + e ^ 2 * n) / (1 - e ^ 2 * n)) 0 :=
    ContinuousAt.div (by fun_prop) hden hW
  have h2 : ∀ t : K, ContinuousAt (fun e : K => 2 * e * t / (1 - e ^ 2 * n)) 0 := fun t =>
    ContinuousAt.div (by fun_prop) hden hW
  refine (qHomeo (d := d) (β := β) (R := K)).isInducing.continuousAt_iff.2 ?_
  exact h1.prodMk ((h2 p).prodMk ((h2 q).prodMk (h2 r)))

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [cay]`.
-/
theorem cay_zero {F K : Type} [Field F] [Field K] [Algebra F K] (d β : F) (p q r n : K) :
    cay d β p q r n 0 = 1 := by
  ext <;> simp [cay]

noncomputable def quartic {K : Type} [Field K] (A B D : K) : K[X] :=
  Polynomial.C (A ^ 2 - 1) + Polynomial.C (4 * A * B) * Polynomial.X
    + Polynomial.C (4 * B ^ 2 + 2 * A ^ 2 * D + 2 * D) * Polynomial.X ^ 2
    + Polynomial.C (4 * A * B * D) * Polynomial.X ^ 3
    + Polynomial.C (D ^ 2 * (A ^ 2 - 1)) * Polynomial.X ^ 4

/- English proof (translation)
Introduce `h`. Establish `gen : ∀ c0 c1 c2 c3 c4 : K, (Polynomial.C c0 + Polynomial.C c1 * Polynomial.X + Polynomial.C c2 * Polynomial.X ^ 2 + Polynomial.C c3 * Polynomial.X ^ 3 + Polynomial.C c4 * Polynomial.X ^ 4 : K[X]).coeff 0 = c0 ∧ (Polynomial.C c0 + Polynomial.C c1 * Polynomial.X + Polynomial.C c2 …`. Introduce `c0 c1 c2 c3 c4`. Simplify using `[Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]`. Take `⟨g0, g1, g2⟩` from `gen (A ^ 2 - 1) (4 * A * B) (4 * B ^ 2 + 2 * A ^ 2 * D + 2 * D) (4 * A * B * D) (D ^ 2 * (A ^ 2 - 1))`.

Unfold `quartic at h`. Rewrite `g0`, `g1`, `g2` using `[h, Polynomial.coeff_zero]`. Establish `c0` using `g0.symm`. Establish `c1` using `g1.symm`. Establish `c2` using `g2.symm`.

Establish `hB : (2 : K) * 2 * B = 0`. Take the linear combination `A * c1 - 4 * B * c0`. Establish `hB0 : B = 0`. Break down `mul_eq_zero.1 hB with h | h` into its components or cases. Conclude with `absurd h (mul_ne_zero h2 h2)`.

Conclude with `h`. Establish `h4 : (2 : K) * 2 * D = 0`. Rewrite `c2` using `[hB0]`. Take the linear combination `c2 - 2 * D * c0`. Conclude with `(mul_ne_zero (mul_ne_zero h2 h2) hD) h4`.
-/
theorem quartic_ne_zero {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (A B D : K) (hD : D ≠ 0) :
    quartic A B D ≠ 0 := by
  intro h
  have gen : ∀ c0 c1 c2 c3 c4 : K,
      (Polynomial.C c0 + Polynomial.C c1 * Polynomial.X + Polynomial.C c2 * Polynomial.X ^ 2
        + Polynomial.C c3 * Polynomial.X ^ 3 + Polynomial.C c4 * Polynomial.X ^ 4 : K[X]).coeff 0 = c0 ∧
      (Polynomial.C c0 + Polynomial.C c1 * Polynomial.X + Polynomial.C c2 * Polynomial.X ^ 2
        + Polynomial.C c3 * Polynomial.X ^ 3 + Polynomial.C c4 * Polynomial.X ^ 4 : K[X]).coeff 1 = c1 ∧
      (Polynomial.C c0 + Polynomial.C c1 * Polynomial.X + Polynomial.C c2 * Polynomial.X ^ 2
        + Polynomial.C c3 * Polynomial.X ^ 3 + Polynomial.C c4 * Polynomial.X ^ 4 : K[X]).coeff 2 = c2 := by
    intro c0 c1 c2 c3 c4
    simp [Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
  obtain ⟨g0, g1, g2⟩ := gen (A ^ 2 - 1) (4 * A * B) (4 * B ^ 2 + 2 * A ^ 2 * D + 2 * D)
    (4 * A * B * D) (D ^ 2 * (A ^ 2 - 1))
  unfold quartic at h
  rw [h, Polynomial.coeff_zero] at g0 g1 g2
  have c0 := g0.symm
  have c1 := g1.symm
  have c2 := g2.symm
  have hB : (2 : K) * 2 * B = 0 := by
    linear_combination A * c1 - 4 * B * c0
  have hB0 : B = 0 := by
    rcases mul_eq_zero.1 hB with h | h
    · exact absurd h (mul_ne_zero h2 h2)
    · exact h
  have h4 : (2 : K) * 2 * D = 0 := by
    rw [hB0] at c2
    linear_combination c2 - 2 * D * c0
  exact (mul_ne_zero (mul_ne_zero h2 h2) hD) h4

/- English proof (translation)
Simplify using `only [quartic, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_quartic {K : Type} [Field K] (A B D e : K) :
    (quartic A B D).eval e = (A * (1 + e ^ 2 * D) + 2 * e * B) ^ 2 - (1 - e ^ 2 * D) ^ 2 := by
  simp only [quartic, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow]
  ring

/- English proof (translation)
Introduce `F K _ _ _ _ _ d β h2 hd hb hne a ha U hU`. Distinguish the cases in `hV : ∃ V ∈ 𝓝 (0 : K), (1 : K) ∉ V`. Establish `hD : algebraMap F K d ≠ 0` using `by simpa using hd`. Establish `e1` using `eventually_eval_ne hV _ (quartic_ne_zero h2 a.re (algebraMap F K d * a.imI) (algebraMap F K d) hD)`. Establish `hP2 : (1 - Polynomial.X ^ 2 * Polynomial.C (algebraMap F K d) : K[X]) ≠ 0`.

Introduce `h`. Use `congrArg (fun P : K[X] => P.eval 0) h` as an intermediate fact. Simplify using `at this`. Establish `e2` using `eventually_eval_ne hV _ hP2`. Establish `e3 : ∀ᶠ e in 𝓝[≠] (0 : K), a * cay d β (1 : K) 0 0 (algebraMap F K d) e ∈ U`.

Establish `hc : ContinuousAt (fun e : K => a * cay d β (1 : K) 0 0 (algebraMap F K d) e) 0` using `continuousAt_const.mul (continuousAt_cay d β _ _ _ _)`. Use `Filter.Eventually.filter_mono nhdsWithin_le_nhds (hc ?_)` and prove the remaining obligations. Simplify `hU` using `[cay_zero]`. Take `⟨e, h1, hW, h3⟩` from `(e1.and (e2.and e3)).exists`. Establish `hW' : 1 - e ^ 2 * algebraMap F K d ≠ 0`.

Simplify `hW` using `only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]`. Use `⟨_, h3, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[qn_mul, ha, one_mul]`. Conclude with `qn_cay d β _ _ _ _ _ (by ring) hW'`. Introduce `hre`.

Apply `h1` to reduce the goal to its premises. Rewrite using `[eval_quartic]`. Establish `hr : (a * cay d β (1 : K) 0 0 (algebraMap F K d) e).re = (a.re * (1 + e ^ 2 * algebraMap F K d) + 2 * e * (algebraMap F K d * a.imI)) / (1 - e ^ 2 * algebraMap F K d)`. Simplify using `only [QuaternionAlgebra.re_mul, cay]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hre` using `[hr, div_pow, div_eq_one_iff_eq (pow_ne_zero 2 hW')]`. Rewrite using `[hre, sub_self]`. Use `push_neg at hV`. Take `⟨b, hb1, hb2⟩` from `exists_regular (K := K) d β h2 hd hb`.

Use `⟨b, ?_, hb1, hb2⟩` and prove the remaining obligations. Set `g : K → Q d β K` to `fun t => ⟨a.re + t * (b.re - a.re), a.imI + t * (b.imI - a.imI), a.imJ + t * (b.imJ - a.imJ), a.imK + t * (b.imK - a.imK)⟩`. Establish `hg : Continuous g` using `continuous_q_iff.2 ⟨by dsimp only [g]; fun_prop, by dsimp only [g]; fun_prop, by dsimp only [g]; fun_prop, by dsimp only [g]; fun_prop⟩`. Apply the tactic sequence `have hg0 : g 0 = a := by ext <;> simp [g]`. Apply the tactic sequence `have hg1 : g 1 = b := by ext <;> simp [g]`.

Establish `hm : g ⁻¹' U ∈ 𝓝 (0 : K)` using `hg.continuousAt (by rw [hg0]; exact hU)`. Use `hV _ hm` as an intermediate fact. Rewrite `this` using `[Set.mem_preimage, hg1]`. Then use the resulting hypothesis.
-/
theorem regular_dense : ∀ {F K : Type} [Field F] [Field K] [Algebra F K] [TopologicalSpace K] [IsTopologicalDivisionRing K] (d β : F),
  (2 : K) ≠ 0 → d ≠ 0 → β ≠ 0 → (𝓝[≠] (0 : K)).NeBot →
  ∀ a : Q d β K, qn a = 1 → ∀ U ∈ 𝓝 a, ∃ b ∈ U, qn b = 1 ∧ b.re ^ 2 ≠ 1 := by
  intro F K _ _ _ _ _ d β h2 hd hb hne a ha U hU
  by_cases hV : ∃ V ∈ 𝓝 (0 : K), (1 : K) ∉ V
  · have hD : algebraMap F K d ≠ 0 := by simpa using hd
    have e1 := eventually_eval_ne hV _
      (quartic_ne_zero h2 a.re (algebraMap F K d * a.imI) (algebraMap F K d) hD)
    have hP2 : (1 - Polynomial.X ^ 2 * Polynomial.C (algebraMap F K d) : K[X]) ≠ 0 := by
      intro h
      have := congrArg (fun P : K[X] => P.eval 0) h
      simp at this
    have e2 := eventually_eval_ne hV _ hP2
    have e3 : ∀ᶠ e in 𝓝[≠] (0 : K),
        a * cay d β (1 : K) 0 0 (algebraMap F K d) e ∈ U := by
      have hc : ContinuousAt (fun e : K => a * cay d β (1 : K) 0 0 (algebraMap F K d) e) 0 :=
        continuousAt_const.mul (continuousAt_cay d β _ _ _ _)
      refine Filter.Eventually.filter_mono nhdsWithin_le_nhds (hc ?_)
      simpa [cay_zero] using hU
    obtain ⟨e, h1, hW, h3⟩ := (e1.and (e2.and e3)).exists
    have hW' : 1 - e ^ 2 * algebraMap F K d ≠ 0 := by
      simpa only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C] using hW
    refine ⟨_, h3, ?_, ?_⟩
    · rw [qn_mul, ha, one_mul]
      exact qn_cay d β _ _ _ _ _ (by ring) hW'
    · intro hre
      apply h1
      rw [eval_quartic]
      have hr : (a * cay d β (1 : K) 0 0 (algebraMap F K d) e).re =
          (a.re * (1 + e ^ 2 * algebraMap F K d) + 2 * e * (algebraMap F K d * a.imI)) /
            (1 - e ^ 2 * algebraMap F K d) := by
        simp only [QuaternionAlgebra.re_mul, cay]
        field_simp
        ring
      rw [hr, div_pow, div_eq_one_iff_eq (pow_ne_zero 2 hW')] at hre
      rw [hre, sub_self]
  · push_neg at hV
    obtain ⟨b, hb1, hb2⟩ := exists_regular (K := K) d β h2 hd hb
    refine ⟨b, ?_, hb1, hb2⟩
    let g : K → Q d β K := fun t =>
      ⟨a.re + t * (b.re - a.re), a.imI + t * (b.imI - a.imI), a.imJ + t * (b.imJ - a.imJ),
        a.imK + t * (b.imK - a.imK)⟩
    have hg : Continuous g :=
      continuous_q_iff.2 ⟨by dsimp only [g]; fun_prop, by dsimp only [g]; fun_prop,
        by dsimp only [g]; fun_prop, by dsimp only [g]; fun_prop⟩
    have hg0 : g 0 = a := by ext <;> simp [g]
    have hg1 : g 1 = b := by ext <;> simp [g]
    have hm : g ⁻¹' U ∈ 𝓝 (0 : K) := hg.continuousAt (by rw [hg0]; exact hU)
    have := hV _ hm
    rwa [Set.mem_preimage, hg1] at this

end GlobalTheory.CompanionTheory.PlaneSA.RegDense
