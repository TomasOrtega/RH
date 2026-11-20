import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StWeaklyHolomorphicIntegral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalBranchedCovering
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalZerosNowhereDense
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalTrace
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

/- English proof (translation)
Rewrite using `[sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul_zero, Polynomial.coeff_C_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeff_X_sub_C_mul_zero (a : ℂ) (q : Polynomial ℂ) :
    ((Polynomial.X - Polynomial.C a) * q).coeff 0 = -a * q.coeff 0 := by
  rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul_zero, Polynomial.coeff_C_mul]
  ring

/- English proof (translation)
Rewrite using `[sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]`.
-/
theorem coeff_X_sub_C_mul_succ (a : ℂ) (q : Polynomial ℂ) (n : ℕ) :
    ((Polynomial.X - Polynomial.C a) * q).coeff (n + 1) = q.coeff n - a * q.coeff (n + 1) := by
  rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `n`. Simplify using `only [Finset.prod_empty]`. Conclude with `differentiableAt_const _`.

Consider the case `insert i s hi ih`. Establish `hai : DifferentiableAt ℂ (a i) x` using `ha i (Finset.mem_insert_self i s)`. Establish `ih'` using `ih fun j hj => ha j (Finset.mem_insert_of_mem hj)`. Introduce `n`. Simplify using `only [Finset.prod_insert hi]`.

Consider the cases of `n with`. Consider the case `zero`. Simplify using `only [coeff_X_sub_C_mul_zero]`. Conclude with `hai.neg.mul (ih' 0)`. Consider the case `succ n`.

Simplify using `only [coeff_X_sub_C_mul_succ]`. Conclude with `(ih' n).sub (hai.mul (ih' (n + 1)))`.
-/
theorem differentiableAt_coeff_prod_X_sub_C {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (a : ι → E → ℂ) (x : E) (ha : ∀ i ∈ s, DifferentiableAt ℂ (a i) x) :
    ∀ n, DifferentiableAt ℂ (fun x => (∏ i ∈ s, (Polynomial.X - Polynomial.C (a i x))).coeff n) x := by
  induction s using Finset.induction_on with
  | empty =>
    intro n
    simp only [Finset.prod_empty]
    exact differentiableAt_const _
  | insert i s hi ih =>
    have hai : DifferentiableAt ℂ (a i) x := ha i (Finset.mem_insert_self i s)
    have ih' := ih fun j hj => ha j (Finset.mem_insert_of_mem hj)
    intro n
    simp only [Finset.prod_insert hi]
    cases n with
    | zero =>
      simp only [coeff_X_sub_C_mul_zero]
      exact hai.neg.mul (ih' 0)
    | succ n =>
      simp only [coeff_X_sub_C_mul_succ]
      exact (ih' n).sub (hai.mul (ih' (n + 1)))

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `n`. Simplify using `only [Finset.prod_empty, Finset.card_empty, pow_zero, Polynomial.coeff_one]`. Apply the tactic sequence `split_ifs <;> simp`.

Consider the case `insert i s hi ih`. Establish `hai : ‖a i‖ ≤ M` using `ha i (Finset.mem_insert_self i s)`. Establish `ih'` using `ih fun j hj => ha j (Finset.mem_insert_of_mem hj)`. Establish `hB : 0 ≤ (2 * M) ^ s.card` using `pow_nonneg (by linarith) _`. Introduce `n`.

Rewrite using `[Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ]`. Consider the cases of `n with`. Consider the case `zero`. Rewrite using `[coeff_X_sub_C_mul_zero, norm_mul, norm_neg]`. Use polynomial arithmetic with `[ih' 0, norm_nonneg (a i), norm_nonneg ((∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))).coeff 0)]`.

Consider the case `succ n`. Rewrite using `[coeff_X_sub_C_mul_succ]`. Use `(norm_sub_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Use polynomial arithmetic with `[ih' n, ih' (n + 1), norm_nonneg (a i), norm_nonneg ((∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))).coeff (n + 1))]`.
-/
theorem norm_coeff_prod_X_sub_C_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℂ) {M : ℝ}
    (hM1 : 1 ≤ M) (ha : ∀ i ∈ s, ‖a i‖ ≤ M) :
    ∀ n, ‖(∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))).coeff n‖ ≤ (2 * M) ^ s.card := by
  induction s using Finset.induction_on with
  | empty =>
    intro n
    simp only [Finset.prod_empty, Finset.card_empty, pow_zero, Polynomial.coeff_one]
    split_ifs <;> simp
  | insert i s hi ih =>
    have hai : ‖a i‖ ≤ M := ha i (Finset.mem_insert_self i s)
    have ih' := ih fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hB : 0 ≤ (2 * M) ^ s.card := pow_nonneg (by linarith) _
    intro n
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ]
    cases n with
    | zero =>
      rw [coeff_X_sub_C_mul_zero, norm_mul, norm_neg]
      nlinarith [ih' 0, norm_nonneg (a i), norm_nonneg ((∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))).coeff 0)]
    | succ n =>
      rw [coeff_X_sub_C_mul_succ]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul]
      nlinarith [ih' n, ih' (n + 1), norm_nonneg (a i),
        norm_nonneg ((∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))).coeff (n + 1))]

/- English proof (translation)
Rewrite using `[Polynomial.eval_eq_sum_range, hd, Finset.sum_range_succ, ← hd, Polynomial.coeff_natDegree, hp.leadingCoeff, hd, one_mul, add_comm, Fin.sum_univ_eq_sum_range (fun j => p.coeff j * t ^ j) m]`.
-/
theorem monic_eval_eq_pow_add_sum {p : Polynomial ℂ} {m : ℕ} (hp : p.Monic) (hd : p.natDegree = m) (t : ℂ) :
    p.eval t = t ^ m + ∑ j : Fin m, p.coeff j * t ^ (j : ℕ) := by
  rw [Polynomial.eval_eq_sum_range, hd, Finset.sum_range_succ, ← hd, Polynomial.coeff_natDegree,
    hp.leadingCoeff, hd, one_mul, add_comm,
    Fin.sum_univ_eq_sum_range (fun j => p.coeff j * t ^ j) m]

/- English proof (translation)
Use `⟨Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C (a j), ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.natDegree_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C (a j)]`. Simplify using the standard rewrite rules.
-/
theorem prod_X_sub_C_monic_natDegree {m : ℕ} (a : Fin m → ℂ) :
    (∏ j, (Polynomial.X - Polynomial.C (a j))).Monic ∧
      (∏ j, (Polynomial.X - Polynomial.C (a j))).natDegree = m := by
  refine ⟨Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C (a j), ?_⟩
  rw [Polynomial.natDegree_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C (a j)]
  simp

/- English proof (translation)
Take `⟨Q, hQ⟩ : ∃ Q : (Fin k → ℂ) → Polynomial ℂ, ∀ y, Q y = ∏ᶠ x ∈ {x | x ∈ Z ∩ W ∧ A x = y}, (Polynomial.X - Polynomial.C (φ x))` from `⟨_, fun _ => rfl⟩`. Establish `hQs : ∀ (y : Fin k → ℂ) (s : Fin m → σ → ℂ), (∀ j, s j ∈ Z ∩ W ∧ A (s j) = y) → Function.Injective s → (∀ z ∈ Z ∩ W, A z = y → z ∈ Set.range s) → Q y = ∏ j, (Polynomial.X - Polynomial.C (φ (s j)))`. Introduce `y s hs hinj hcov`. Establish `hset : {x | x ∈ Z ∩ W ∧ A x = y} = Set.range s`. Use extensionality with `z`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hz, hAz⟩`. Conclude with `hcov z hz hAz`. Introduce and unpack `⟨j, rfl⟩`. Conclude with `hs j`.

Rewrite using `[hQ, hset, finprod_mem_range hinj, finprod_eq_prod_of_fintype]`. Establish `hcd : ∀ n : ℕ, DifferentiableOn ℂ (fun y => (Q y).coeff n) (D ∩ {t | g t ≠ 0})`. Introduce and unpack `n y ⟨hyD, hyg⟩`. Take `⟨O, s, hOo, hyO, hsd, hsO⟩` from `hsheets y hyD (hgδ y hyD hyg)`. Establish `hev : (fun y => (Q y).coeff n) =ᶠ[𝓝 y] fun y' => (∏ i, (Polynomial.X - Polynomial.C (φ (s i y')))).coeff n` using `by filter_upwards [hOo.mem_nhds hyO] with y' hy'`.

Rewrite using `[hQs y' (fun i => s i y') (hsO y' hy').1 (hsO y' hy').2.1 (hsO y' hy').2.2]`. Use `(DifferentiableAt.congr_of_eventuallyEq ?_ hev).differentiableWithinAt` and prove the remaining obligations. Use `differentiableAt_coeff_prod_X_sub_C Finset.univ (fun i y' => φ (s i y')) y (fun i _ => ?_) n` and prove the remaining obligations. Use `hφ.differentiableAt_comp ((hsd i).differentiableAt (hOo.mem_nhds hyO)) ?_` and prove the remaining obligations. Establish `hgc : ContinuousAt g y` using `(hgd.differentiableAt (hDo.mem_nhds hyD)).continuousAt`.

Use `filter_upwards [hOo.mem_nhds hyO, hDo.mem_nhds hyD, hgc.eventually_ne hyg] with y' h1 h2 h3`. Establish `hs'` using `(hsO y' h1).1 i`. Conclude with `⟨hs'.1, by rw [hs'.2]; exact h2, by rw [hs'.2]; exact h3⟩`. Use `set M' : ℝ := max M 1`. Establish `hcb : ∀ n : ℕ, ∀ y ∈ D ∩ {t | g t ≠ 0}, ‖(Q y).coeff n‖ ≤ (2 * M') ^ m`.

Introduce and unpack `n y ⟨hyD, hyg⟩`. Take `⟨O, s, hOo, hyO, hsd, hsO⟩` from `hsheets y hyD (hgδ y hyD hyg)`. Take `⟨h1, h2, h3⟩` from `hsO y hyO`. Rewrite using `[hQs y (fun i => s i y) h1 h2 h3]`. Use `norm_coeff_prod_X_sub_C_le Finset.univ (fun i => φ (s i y)) (le_max_right M 1) (fun i _ => (hM _ (h1 i).1 (by rw [(h1 i).2]; exact hyD) (by rw [(h1 i).2]; exact hyg)).trans (le_max_left M 1)) n` as an intermediate fact.

Simplify using `using this`. Establish `hext : ∀ j : Fin m, ∃ F : (Fin k → ℂ) → ℂ, DifferentiableOn ℂ F D ∧ Set.EqOn F (fun y => (Q y).coeff j) (D ∩ {t | g t ≠ 0})`. Introduce `j`. Conclude with `RiemannExtensionAnalytic.proof k D g (fun y => (Q y).coeff j) hDo hgd hgne (hcd j) (fun τ _ => ⟨Set.univ, Filter.univ_mem, isBounded_iff_forall_norm_le.2 ⟨(2 * M') ^ m, by`. Introduce and unpack `_ ⟨y, ⟨⟨_, hyD⟩, hyg⟩, rfl⟩`.

Conclude with `hcb j y ⟨hyD, hyg⟩⟩⟩)`. Use `choose c hcD hceq using hext`. Use `⟨c, hcD, ?_⟩` and prove the remaining obligations. Introduce `y hyD hyg s hs hinj hcov t`. Establish `hQy` using `hQs y s hs hinj hcov`.

Take `⟨hmon, hdeg⟩` from `prod_X_sub_C_monic_natDegree (fun j => φ (s j))`. Establish `hcy : ∀ j : Fin m, c j y = (∏ i, (Polynomial.X - Polynomial.C (φ (s i)))).coeff j`. Introduce `j`. Rewrite using `[hceq j ⟨hyD, hyg⟩]`. Simplify using `only`.

Rewrite using `[hQy]`. Repeatedly rewrite using `[hcy]`. Rewrite using `[← monic_eval_eq_pow_add_sum hmon hdeg t, Polynomial.eval_prod]`. Simplify using the standard rewrite rules.
-/
theorem fibre_coeffs_extend {σ : Type} [Fintype σ] {k m : ℕ} (Z W : Set (σ → ℂ))
    (A : (σ → ℂ) →L[ℂ] (Fin k → ℂ)) (D : Set (Fin k → ℂ)) (δ g : (Fin k → ℂ) → ℂ) (φ : (σ → ℂ) → ℂ) (M : ℝ)
    (hDo : IsOpen D) (hgd : DifferentiableOn ℂ g D)
    (hgne : ∀ V : Set (Fin k → ℂ), IsOpen V → V ⊆ D → V.Nonempty → ∃ t ∈ V, g t ≠ 0)
    (hgδ : ∀ y ∈ D, g y ≠ 0 → δ y ≠ 0)
    (hsheets : ∀ y ∈ D, δ y ≠ 0 → ∃ (O : Set (Fin k → ℂ)) (s : Fin m → (Fin k → ℂ) → σ → ℂ),
        IsOpen O ∧ y ∈ O ∧ (∀ j, DifferentiableOn ℂ (s j) O) ∧
        ∀ y' ∈ O, (∀ j, s j y' ∈ Z ∩ W ∧ A (s j y') = y') ∧
          Function.Injective (fun j => s j y') ∧
          ∀ z ∈ Z ∩ W, A z = y' → z ∈ Set.range (fun j => s j y'))
    (hφ : HolomorphicOnSubset φ {x | x ∈ Z ∩ W ∧ A x ∈ D ∧ g (A x) ≠ 0})
    (hM : ∀ x ∈ Z ∩ W, A x ∈ D → g (A x) ≠ 0 → ‖φ x‖ ≤ M) :
    ∃ c : Fin m → (Fin k → ℂ) → ℂ, (∀ j, DifferentiableOn ℂ (c j) D) ∧
      ∀ y ∈ D, g y ≠ 0 → ∀ s : Fin m → σ → ℂ, (∀ j, s j ∈ Z ∩ W ∧ A (s j) = y) →
        Function.Injective s → (∀ z ∈ Z ∩ W, A z = y → z ∈ Set.range s) →
        ∀ t : ℂ, t ^ m + ∑ j, c j y * t ^ (j : ℕ) = ∏ j, (t - φ (s j)) := by
  classical
  obtain ⟨Q, hQ⟩ : ∃ Q : (Fin k → ℂ) → Polynomial ℂ,
      ∀ y, Q y = ∏ᶠ x ∈ {x | x ∈ Z ∩ W ∧ A x = y}, (Polynomial.X - Polynomial.C (φ x)) := ⟨_, fun _ => rfl⟩
  have hQs : ∀ (y : Fin k → ℂ) (s : Fin m → σ → ℂ), (∀ j, s j ∈ Z ∩ W ∧ A (s j) = y) →
      Function.Injective s → (∀ z ∈ Z ∩ W, A z = y → z ∈ Set.range s) →
      Q y = ∏ j, (Polynomial.X - Polynomial.C (φ (s j))) := by
    intro y s hs hinj hcov
    have hset : {x | x ∈ Z ∩ W ∧ A x = y} = Set.range s := by
      ext z
      constructor
      · rintro ⟨hz, hAz⟩
        exact hcov z hz hAz
      · rintro ⟨j, rfl⟩
        exact hs j
    rw [hQ, hset, finprod_mem_range hinj, finprod_eq_prod_of_fintype]
  have hcd : ∀ n : ℕ, DifferentiableOn ℂ (fun y => (Q y).coeff n) (D ∩ {t | g t ≠ 0}) := by
    rintro n y ⟨hyD, hyg⟩
    obtain ⟨O, s, hOo, hyO, hsd, hsO⟩ := hsheets y hyD (hgδ y hyD hyg)
    have hev : (fun y => (Q y).coeff n) =ᶠ[𝓝 y]
        fun y' => (∏ i, (Polynomial.X - Polynomial.C (φ (s i y')))).coeff n := by
      filter_upwards [hOo.mem_nhds hyO] with y' hy'
      rw [hQs y' (fun i => s i y') (hsO y' hy').1 (hsO y' hy').2.1 (hsO y' hy').2.2]
    refine (DifferentiableAt.congr_of_eventuallyEq ?_ hev).differentiableWithinAt
    refine differentiableAt_coeff_prod_X_sub_C Finset.univ (fun i y' => φ (s i y')) y (fun i _ => ?_) n
    refine hφ.differentiableAt_comp ((hsd i).differentiableAt (hOo.mem_nhds hyO)) ?_
    have hgc : ContinuousAt g y := (hgd.differentiableAt (hDo.mem_nhds hyD)).continuousAt
    filter_upwards [hOo.mem_nhds hyO, hDo.mem_nhds hyD, hgc.eventually_ne hyg] with y' h1 h2 h3
    have hs' := (hsO y' h1).1 i
    exact ⟨hs'.1, by rw [hs'.2]; exact h2, by rw [hs'.2]; exact h3⟩
  set M' : ℝ := max M 1
  have hcb : ∀ n : ℕ, ∀ y ∈ D ∩ {t | g t ≠ 0}, ‖(Q y).coeff n‖ ≤ (2 * M') ^ m := by
    rintro n y ⟨hyD, hyg⟩
    obtain ⟨O, s, hOo, hyO, hsd, hsO⟩ := hsheets y hyD (hgδ y hyD hyg)
    obtain ⟨h1, h2, h3⟩ := hsO y hyO
    rw [hQs y (fun i => s i y) h1 h2 h3]
    have := norm_coeff_prod_X_sub_C_le Finset.univ (fun i => φ (s i y)) (le_max_right M 1)
      (fun i _ => (hM _ (h1 i).1 (by rw [(h1 i).2]; exact hyD) (by rw [(h1 i).2]; exact hyg)).trans
        (le_max_left M 1)) n
    simpa using this
  have hext : ∀ j : Fin m, ∃ F : (Fin k → ℂ) → ℂ, DifferentiableOn ℂ F D ∧
      Set.EqOn F (fun y => (Q y).coeff j) (D ∩ {t | g t ≠ 0}) := by
    intro j
    exact RiemannExtensionAnalytic.proof k D g (fun y => (Q y).coeff j) hDo hgd hgne (hcd j) (fun τ _ =>
      ⟨Set.univ, Filter.univ_mem, isBounded_iff_forall_norm_le.2 ⟨(2 * M') ^ m, by
        rintro _ ⟨y, ⟨⟨_, hyD⟩, hyg⟩, rfl⟩
        exact hcb j y ⟨hyD, hyg⟩⟩⟩)
  choose c hcD hceq using hext
  refine ⟨c, hcD, ?_⟩
  intro y hyD hyg s hs hinj hcov t
  have hQy := hQs y s hs hinj hcov
  obtain ⟨hmon, hdeg⟩ := prod_X_sub_C_monic_natDegree (fun j => φ (s j))
  have hcy : ∀ j : Fin m, c j y = (∏ i, (Polynomial.X - Polynomial.C (φ (s i)))).coeff j := by
    intro j
    rw [hceq j ⟨hyD, hyg⟩]
    dsimp only
    rw [hQy]
  simp_rw [hcy]
  rw [← monic_eval_eq_pow_add_sum hmon hdeg t, Polynomial.eval_prod]
  simp

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hev : ∀ᶠ z in 𝓝 x, z ∈ V₀ ∧ z ∈ W ∧ A z ∈ D ∧ Ψ z ≠ 0` using `Filter.Eventually.and (hV₀ : ∀ᶠ z in 𝓝 x, z ∈ V₀) (Filter.Eventually.and (hWo.mem_nhds hx.2 : ∀ᶠ z in 𝓝 x, z ∈ W) (Filter.Eventually.and (A.continuous.continuousAt.preimage_mem_nhds (hDo.mem_nhds hAx) : ∀ᶠ z in 𝓝 x, A z ∈ D) (hΨ.eventually_ne hne)))`. Take `⟨ε, hε, hball⟩` from `Metric.eventually_nhds_iff_ball.1 hev`. Establish `hn : A '' (Z ∩ Metric.ball x ε) ∩ D ∈ 𝓝 (A x)` using `Filter.inter_mem (hopen x hx ε hε) (hDo.mem_nhds hAx)`. Take `⟨V, hVsub, hVo, hxV⟩` from `mem_nhds_iff.1 hn`.

Take `⟨t, htV, hgt⟩` from `hgne V hVo (fun v hv => (hVsub hv).2) ⟨_, hxV⟩`. Take `⟨⟨z, ⟨hzZ, hzb⟩, rfl⟩, -⟩` from `hVsub htV`. Take `⟨hzV, hzW, hzD, hΨz⟩` from `hball z hzb`. Conclude with `hΨz (h0 z ⟨⟨hzZ, hzW⟩, hzV⟩ hzD hgt)`.
-/
theorem eq_zero_of_zero_over_nonzero {σ : Type} [Fintype σ] {k : ℕ} (Z W : Set (σ → ℂ))
    (A : (σ → ℂ) →L[ℂ] (Fin k → ℂ)) (D : Set (Fin k → ℂ)) (g : (Fin k → ℂ) → ℂ) (hWo : IsOpen W)
    (hDo : IsOpen D) (hgne : ∀ V : Set (Fin k → ℂ), IsOpen V → V ⊆ D → V.Nonempty → ∃ t ∈ V, g t ≠ 0)
    (hopen : ∀ z ∈ Z ∩ W, ∀ ε > 0, A '' (Z ∩ Metric.ball z ε) ∈ 𝓝 (A z)) {x : σ → ℂ} (hx : x ∈ Z ∩ W)
    (hAx : A x ∈ D) (Ψ : (σ → ℂ) → ℂ) (hΨ : ContinuousAt Ψ x) (V₀ : Set (σ → ℂ)) (hV₀ : V₀ ∈ 𝓝 x)
    (h0 : ∀ z ∈ Z ∩ W ∩ V₀, A z ∈ D → g (A z) ≠ 0 → Ψ z = 0) : Ψ x = 0 := by
  by_contra hne
  have hev : ∀ᶠ z in 𝓝 x, z ∈ V₀ ∧ z ∈ W ∧ A z ∈ D ∧ Ψ z ≠ 0 :=
    Filter.Eventually.and (hV₀ : ∀ᶠ z in 𝓝 x, z ∈ V₀) (Filter.Eventually.and
      (hWo.mem_nhds hx.2 : ∀ᶠ z in 𝓝 x, z ∈ W) (Filter.Eventually.and
        (A.continuous.continuousAt.preimage_mem_nhds (hDo.mem_nhds hAx) : ∀ᶠ z in 𝓝 x, A z ∈ D)
        (hΨ.eventually_ne hne)))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hn : A '' (Z ∩ Metric.ball x ε) ∩ D ∈ 𝓝 (A x) :=
    Filter.inter_mem (hopen x hx ε hε) (hDo.mem_nhds hAx)
  obtain ⟨V, hVsub, hVo, hxV⟩ := mem_nhds_iff.1 hn
  obtain ⟨t, htV, hgt⟩ := hgne V hVo (fun v hv => (hVsub hv).2) ⟨_, hxV⟩
  obtain ⟨⟨z, ⟨hzZ, hzb⟩, rfl⟩, -⟩ := hVsub htV
  obtain ⟨hzV, hzW, hzD, hΨz⟩ := hball z hzb
  exact hΨz (h0 z ⟨⟨hzZ, hzW⟩, hzV⟩ hzD hgt)

/- English proof (translation)
Establish `key : ∀ Q' : Set (Fin k → ℂ), IsOpen Q' → Q' ⊆ O → Q'.Nonempty → ∀ j, ∃ y ∈ Q', G (s j y) ≠ 0`. Introduce `Q' hQ'o hQ'O ⟨y1, hy1⟩ j`. Establish `hx1` using `(hsO y1 (hQ'O hy1)).1 j`. Establish `hV : ∀ᶠ z in 𝓝 (s j y1), z ∈ W ∧ A z ∈ Q' ∧ ∀ i, i ≠ j → s i (A z) - z ≠ 0`. Use `Filter.Eventually.and (hWo.mem_nhds hx1.1.2 : ∀ᶠ z in 𝓝 (s j y1), z ∈ W) (Filter.Eventually.and (A.continuous.continuousAt.preimage_mem_nhds (hQ'o.mem_nhds (by rw [hx1.2]; exact hy1)) : ∀ᶠ z in 𝓝 (s j y1), A z ∈ Q') (Filter.eventually_all.2 fun i => ?_))` and prove the remaining obligations.

Distinguish the cases in `hij : i = j`. Conclude with `Filter.Eventually.of_forall fun _ h => absurd hij h`. Establish `hsi : ContinuousAt (s i) (A (s j y1))`. Rewrite using `[hx1.2]`. Conclude with `((hsd i).differentiableAt (hOo.mem_nhds (hQ'O hy1))).continuousAt`.

Establish `hc : ContinuousAt (fun z => s i (A z) - z) (s j y1)` using `(hsi.comp A.continuous.continuousAt).sub continuousAt_id`. Establish `hne : s i (A (s j y1)) - s j y1 ≠ 0`. Rewrite using `[hx1.2, sub_ne_zero]`. Conclude with `fun h => hij ((hsO y1 (hQ'O hy1)).2.1 h)`. Conclude with `(hc.eventually_ne hne).mono fun _ h _ => h`.

Take `⟨x, ⟨hxZ, hxW, hxQ, hxs⟩, hGx⟩` from `hnd _ hx1.1 _ hV`. Take `⟨i, hi⟩` from `(hsO (A x) (hQ'O hxQ)).2.2 x ⟨hxZ, hxW⟩ rfl`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Use `⟨A x, hxQ, ?_⟩` and prove the remaining obligations.

Simplify using `only at hi`. Rewrite using `[hi]`. Conclude with `hGx`. Conclude with `absurd (sub_eq_zero.2 hi) (hxs i hij)`. Establish `hcont : ∀ j, ContinuousOn (fun y => G (s j y)) O` using `fun j => hGc.comp (hsd j).continuousOn fun y hy => ((hsO y hy).1 j).1.2`.

Establish `step : ∀ n, n ≤ m → ∃ Q' : Set (Fin k → ℂ), IsOpen Q' ∧ Q' ⊆ Q ∧ Q'.Nonempty ∧ ∀ y ∈ Q', ∀ j : Fin m, (j : ℕ) < n → G (s j y) ≠ 0`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact fun _ => ⟨Q, hQo, subset_rfl, hQne, fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩`. Consider the case `succ n ih`.

Introduce `hn`. Take `⟨Q', hQ'o, hQ'Q, hQ'ne, hQ'⟩` from `ih (by omega)`. Take `⟨y, hyQ', hy⟩` from `key Q' hQ'o (hQ'Q.trans hQO) hQ'ne ⟨n, by omega⟩`. Use `⟨Q' ∩ (fun y => G (s ⟨n, by omega⟩ y)) ⁻¹' {0}ᶜ, ((hcont _).mono (hQ'Q.trans hQO)).isOpen_inter_preimage hQ'o isOpen_compl_singleton, Set.inter_subset_left.trans hQ'Q, ⟨y, hyQ', hy⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `y' ⟨hy'Q', hy'⟩ j hj`.

Break down `Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj` into its components or cases. Conclude with `hQ' y' hy'Q' j hj`. Establish `: j = ⟨n, by omega⟩` using `Fin.ext hj`. Rewrite using `[this]`. Conclude with `hy'`.

Take `⟨Q', -, hQ'Q, ⟨y, hy⟩, hQ'⟩` from `step m le_rfl`. Conclude with `⟨y, hQ'Q hy, fun j => hQ' y hy j j.isLt⟩`.
-/
theorem exists_sheets_nonzero {σ : Type} [Fintype σ] {k m : ℕ} (Z W : Set (σ → ℂ))
    (A : (σ → ℂ) →L[ℂ] (Fin k → ℂ)) (G : (σ → ℂ) → ℂ) (O Q : Set (Fin k → ℂ))
    (s : Fin m → (Fin k → ℂ) → σ → ℂ) (hWo : IsOpen W) (hOo : IsOpen O) (hQo : IsOpen Q) (hQO : Q ⊆ O)
    (hQne : Q.Nonempty) (hsd : ∀ j, DifferentiableOn ℂ (s j) O)
    (hsO : ∀ y' ∈ O, (∀ j, s j y' ∈ Z ∩ W ∧ A (s j y') = y') ∧ Function.Injective (fun j => s j y') ∧
      ∀ z ∈ Z ∩ W, A z = y' → z ∈ Set.range (fun j => s j y'))
    (hGc : ContinuousOn G W) (hnd : ∀ z ∈ Z ∩ W, ∀ V ∈ 𝓝 z, ∃ x ∈ Z ∩ V, G x ≠ 0) :
    ∃ y ∈ Q, ∀ j, G (s j y) ≠ 0 := by
  have key : ∀ Q' : Set (Fin k → ℂ), IsOpen Q' → Q' ⊆ O → Q'.Nonempty → ∀ j, ∃ y ∈ Q', G (s j y) ≠ 0 := by
    intro Q' hQ'o hQ'O ⟨y1, hy1⟩ j
    have hx1 := (hsO y1 (hQ'O hy1)).1 j
    have hV : ∀ᶠ z in 𝓝 (s j y1), z ∈ W ∧ A z ∈ Q' ∧ ∀ i, i ≠ j → s i (A z) - z ≠ 0 := by
      refine Filter.Eventually.and (hWo.mem_nhds hx1.1.2 : ∀ᶠ z in 𝓝 (s j y1), z ∈ W)
        (Filter.Eventually.and (A.continuous.continuousAt.preimage_mem_nhds
          (hQ'o.mem_nhds (by rw [hx1.2]; exact hy1)) : ∀ᶠ z in 𝓝 (s j y1), A z ∈ Q')
          (Filter.eventually_all.2 fun i => ?_))
      by_cases hij : i = j
      · exact Filter.Eventually.of_forall fun _ h => absurd hij h
      · have hsi : ContinuousAt (s i) (A (s j y1)) := by
          rw [hx1.2]
          exact ((hsd i).differentiableAt (hOo.mem_nhds (hQ'O hy1))).continuousAt
        have hc : ContinuousAt (fun z => s i (A z) - z) (s j y1) :=
          (hsi.comp A.continuous.continuousAt).sub continuousAt_id
        have hne : s i (A (s j y1)) - s j y1 ≠ 0 := by
          rw [hx1.2, sub_ne_zero]
          exact fun h => hij ((hsO y1 (hQ'O hy1)).2.1 h)
        exact (hc.eventually_ne hne).mono fun _ h _ => h
    obtain ⟨x, ⟨hxZ, hxW, hxQ, hxs⟩, hGx⟩ := hnd _ hx1.1 _ hV
    obtain ⟨i, hi⟩ := (hsO (A x) (hQ'O hxQ)).2.2 x ⟨hxZ, hxW⟩ rfl
    by_cases hij : i = j
    · subst hij
      refine ⟨A x, hxQ, ?_⟩
      simp only at hi
      rw [hi]
      exact hGx
    · exact absurd (sub_eq_zero.2 hi) (hxs i hij)
  have hcont : ∀ j, ContinuousOn (fun y => G (s j y)) O := fun j =>
    hGc.comp (hsd j).continuousOn fun y hy => ((hsO y hy).1 j).1.2
  have step : ∀ n, n ≤ m → ∃ Q' : Set (Fin k → ℂ), IsOpen Q' ∧ Q' ⊆ Q ∧ Q'.Nonempty ∧
      ∀ y ∈ Q', ∀ j : Fin m, (j : ℕ) < n → G (s j y) ≠ 0 := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨Q, hQo, subset_rfl, hQne, fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ n ih =>
      intro hn
      obtain ⟨Q', hQ'o, hQ'Q, hQ'ne, hQ'⟩ := ih (by omega)
      obtain ⟨y, hyQ', hy⟩ := key Q' hQ'o (hQ'Q.trans hQO) hQ'ne ⟨n, by omega⟩
      refine ⟨Q' ∩ (fun y => G (s ⟨n, by omega⟩ y)) ⁻¹' {0}ᶜ,
        ((hcont _).mono (hQ'Q.trans hQO)).isOpen_inter_preimage hQ'o isOpen_compl_singleton,
        Set.inter_subset_left.trans hQ'Q, ⟨y, hyQ', hy⟩, ?_⟩
      rintro y' ⟨hy'Q', hy'⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact hQ' y' hy'Q' j hj
      · have : j = ⟨n, by omega⟩ := Fin.ext hj
        rw [this]
        exact hy'
  obtain ⟨Q', -, hQ'Q, ⟨y, hy⟩, hQ'⟩ := step m le_rfl
  exact ⟨y, hQ'Q hy, fun j => hQ' y hy j j.isLt⟩

/- English proof (translation)
Introduce `σ _ I w N G f hI hnorm hw hNo hwN hG hGne hf hfb`. Take `⟨U₀, hU₀o, hwU₀, hU₀N, hnd'⟩` from `hnd σ I w N G hI hnorm hw hNo hwN hG hGne`. Take `⟨k, A, W, D, m, δ, hWo, hwW, hWc, hWU, hDo, hAwD, -, -, hδd, hδne, hsheets, hopen⟩` from `hbc σ I w U₀ hI hw (hU₀o.mem_nhds hwU₀)`. Establish `hWU₀ : W ⊆ U₀` using `fun z hz => hWU (subset_closure hz)`. Establish `hWN : W ⊆ N` using `hWU₀.trans hU₀N`.

Establish `hnd'' : ∀ z ∈ zeroSetIn I ∩ W, ∀ V ∈ 𝓝 z, ∃ x ∈ zeroSetIn I ∩ V, G x ≠ 0` using `fun z hz => hnd' z ⟨hz.1, hWU₀ hz.2⟩`. Establish `hGat : ∀ z ∈ N, DifferentiableAt ℂ G z` using `fun z hz => hG.differentiableAt (hNo.mem_nhds hz)`. Establish `hKc : IsCompact (zeroSetIn I ∩ closure W)` using `hWc.inter_left (isClosed_zeroSetIn_of_ideal I)`. Take `⟨MG, hMG⟩ : ∃ MG, ∀ z ∈ zeroSetIn I ∩ closure W, ‖G z‖ ≤ MG` from `hKc.exists_bound_of_continuousOn (hG.continuousOn.mono fun z hz => hU₀N (hWU hz.2))`. Take `⟨cG, hcGd, hcGeq⟩` from `fibre_coeffs_extend (zeroSetIn I) W A D δ δ G MG hDo hδd hδne (fun _ _ h => h) hsheets (fun z hz => ⟨N, hNo, hWN hz.1.2, G, hG, fun _ _ => rfl⟩) (fun x hx _ _ => hMG x ⟨hx.1, subset_closure hx.2⟩)`.

Establish `hGeq : ∀ x ∈ zeroSetIn I ∩ W, A x ∈ D → G x ^ m + ∑ j, cG j (A x) * G x ^ (j : ℕ) = 0`. Introduce `x hx hAx`. Use `eq_zero_of_zero_over_nonzero (zeroSetIn I) W A D δ hWo hDo hδne hopen hx hAx (fun z => G z ^ m + ∑ j, cG j (A z) * G z ^ (j : ℕ)) ?_ Set.univ Filter.univ_mem ?_` and prove the remaining obligations. Use `DifferentiableAt.continuousAt (((hGat x (hWN hx.2)).pow m).add (DifferentiableAt.fun_sum fun j _ => ?_))` and prove the remaining obligations. Conclude with `(((hcGd j).differentiableAt (hDo.mem_nhds hAx)).comp x A.differentiableAt).mul ((hGat x (hWN hx.2)).pow _)`.

Introduce and unpack `z ⟨⟨hzZ, hzW⟩, -⟩ hAz hδz`. Take `⟨O, s, -, hyO, -, hsO⟩` from `hsheets (A z) hAz hδz`. Take `⟨h1, h2, h3⟩` from `hsO (A z) hyO`. Rewrite using `[hcGeq (A z) hAz hδz (fun j => s j (A z)) h1 h2 h3 (G z)]`. Take `⟨i, hi⟩` from `h3 z ⟨hzZ, hzW⟩ rfl`.

Use `Finset.prod_eq_zero (Finset.mem_univ i) ?_` and prove the remaining obligations. Simplify using `only at hi`. Rewrite using `[hi, sub_self]`. Use `set P : (Fin k → ℂ) → ℂ := fun y => (0 : ℂ) ^ m + ∑ j, cG j y * (0 : ℂ) ^ (j : ℕ) with hP`. Establish `hPd : DifferentiableOn ℂ P D` using `(differentiableOn_const _).add (DifferentiableOn.fun_sum fun j _ => (hcGd j).mul_const _)`.

Establish `hPzero : ∀ x ∈ zeroSetIn I ∩ W, A x ∈ D → G x = 0 → P (A x) = 0`. Introduce `x hx hAx hGx`. Use `hGeq x hx hAx` as an intermediate fact. Rewrite `this` using `[hGx]`. Conclude with `this`.

Use `set g : (Fin k → ℂ) → ℂ := fun y => δ y * P y with hg`. Establish `hgd : DifferentiableOn ℂ g D` using `hδd.mul hPd`. Establish `hgne : ∀ V : Set (Fin k → ℂ), IsOpen V → V ⊆ D → V.Nonempty → ∃ t ∈ V, g t ≠ 0`. Introduce `V hVo hVD hVne`. Take `⟨y, hyV, hδy⟩` from `hδne V hVo hVD hVne`.

Take `⟨O, s, hOo, hyO, hsd, hsO⟩` from `hsheets y (hVD hyV) hδy`. Establish `hQo : IsOpen ((V ∩ O) ∩ δ ⁻¹' {0}ᶜ)` using `(hδd.continuousOn.mono (Set.inter_subset_left.trans hVD)).isOpen_inter_preimage (hVo.inter hOo) isOpen_compl_singleton`. Take `⟨y', ⟨⟨hy'V, hy'O⟩, hy'δ⟩, hall⟩` from `exists_sheets_nonzero (zeroSetIn I) W A G O _ s hWo hOo hQo (fun _ h => h.1.2) ⟨y, ⟨hyV, hyO⟩, hδy⟩ hsd hsO (hG.continuousOn.mono hWN) hnd''`. Use `⟨y', hy'V, mul_ne_zero hy'δ ?_⟩` and prove the remaining obligations. Take `⟨h1, h2, h3⟩` from `hsO y' hy'O`.

Establish `hval` using `hcGeq y' (hVD hy'V) hy'δ (fun j => s j y') h1 h2 h3 0`. Use `show P y' ≠ 0`. Rewrite using `[hP]`. Simplify using `only`. Rewrite using `[hval]`.

Conclude with `Finset.prod_ne_zero_iff.2 fun j _ => by rw [zero_sub, neg_ne_zero]; exact hall j`. Establish `hS : ∀ x ∈ zeroSetIn I ∩ W, A x ∈ D → g (A x) ≠ 0 → x ∈ (zeroSetIn I ∩ N) \ {z | G z = 0}`. Introduce `x hx hAx hgx`. Use `⟨⟨hx.1, hWN hx.2⟩, fun hGx => hgx ?_⟩` and prove the remaining obligations. Use `show δ (A x) * P (A x) = 0`.

Rewrite using `[hPzero x hx hAx hGx, mul_zero]`. Establish `hfS : HolomorphicOnSubset f {x | x ∈ zeroSetIn I ∩ W ∧ A x ∈ D ∧ g (A x) ≠ 0}`. Introduce `x hx`. Take `⟨U, hU, hxU, F, hF, hfF⟩` from `hf x (hS x hx.1 hx.2.1 hx.2.2)`. Conclude with `⟨U, hU, hxU, F, hF, fun z hz => hfF ⟨hS z hz.1.1 hz.1.2.1 hz.1.2.2, hz.2⟩⟩`.

Take `⟨Mf, hMf⟩` from `isBounded_iff_forall_norm_le.1 hfb`. Take `⟨cf, hcfd, hcfeq⟩` from `fibre_coeffs_extend (zeroSetIn I) W A D δ g f Mf hDo hgd hgne (fun _ _ h => left_ne_zero_of_mul h) hsheets hfS (fun x hx hAx hgx => hMf _ ⟨x, hS x hx hAx hgx, rfl⟩)`. Use `⟨W ∩ A ⁻¹' D, hWo.inter (hDo.preimage A.continuous), ⟨hwW, hAwD⟩, fun z hz => hWN hz.1, m, fun j z => cf j (A z), fun j => (hcfd j).comp A.differentiableOn fun z hz => hz.2, ?_⟩` and prove the remaining obligations. Introduce and unpack `z ⟨⟨hzZ, hzW, hzD⟩, hGz⟩`. Establish `hzS : z ∈ (zeroSetIn I ∩ N) \ {z | G z = 0}` using `⟨⟨hzZ, hWN hzW⟩, hGz⟩`.

Take `⟨U, hUo, hzU, F, hFd, hfF⟩` from `hf z hzS`. Establish `hGc : ContinuousAt G z` using `(hGat z (hWN hzW)).continuousAt`. Establish `hV₀ : U ∩ N ∩ {x | G x ≠ 0} ∈ 𝓝 z` using `Filter.inter_mem (Filter.inter_mem (hUo.mem_nhds hzU) (hNo.mem_nhds (hWN hzW))) (hGc.eventually_ne hGz)`. Establish `key` using `eq_zero_of_zero_over_nonzero (zeroSetIn I) W A D g hWo hDo hgne hopen ⟨hzZ, hzW⟩ hzD (fun x => F x ^ m + ∑ j, cf j (A x) * F x ^ (j : ℕ)) ?_ _ hV₀ ?_`. Use `show f z ^ m + ∑ j, cf j (A z) * f z ^ (j : ℕ) = 0`.

Rewrite using `[hfF ⟨hzS, hzU⟩]`. Conclude with `key`. Establish `hFz : DifferentiableAt ℂ F z` using `hFd.differentiableAt (hUo.mem_nhds hzU)`. Use `DifferentiableAt.continuousAt ((hFz.pow m).add (DifferentiableAt.fun_sum fun j _ => ?_))` and prove the remaining obligations. Conclude with `(((hcfd j).differentiableAt (hDo.mem_nhds hzD)).comp z A.differentiableAt).mul (hFz.pow _)`.

Introduce and unpack `x ⟨⟨hxZ, hxW⟩, ⟨hxU, hxN⟩, hxG⟩ hAx hgx`. Establish `hxS : x ∈ (zeroSetIn I ∩ N) \ {z | G z = 0}` using `⟨⟨hxZ, hxN⟩, hxG⟩`. Use `show F x ^ m + ∑ j, cf j (A x) * F x ^ (j : ℕ) = 0`. Rewrite using `[← hfF ⟨hxS, hxU⟩]`. Take `⟨O, s, -, hyO, -, hsO⟩` from `hsheets (A x) hAx (left_ne_zero_of_mul hgx)`.

Take `⟨h1, h2, h3⟩` from `hsO (A x) hyO`. Rewrite using `[hcfeq (A x) hAx hgx (fun j => s j (A x)) h1 h2 h3 (f x)]`. Take `⟨i, hi⟩` from `h3 x ⟨hxZ, hxW⟩ rfl`. Use `Finset.prod_eq_zero (Finset.mem_univ i) ?_` and prove the remaining obligations. Simplify using `only at hi`.

Rewrite using `[hi, sub_self]`.
-/
theorem WeaklyHolomorphicIntegral.proof (hbc : LocalBranchedCovering.Statement)
    (hnd : NormalZerosNowhereDense.Statement) : WeaklyHolomorphicIntegral.Statement := by
  intro σ _ I w N G f hI hnorm hw hNo hwN hG hGne hf hfb
  obtain ⟨U₀, hU₀o, hwU₀, hU₀N, hnd'⟩ := hnd σ I w N G hI hnorm hw hNo hwN hG hGne
  obtain ⟨k, A, W, D, m, δ, hWo, hwW, hWc, hWU, hDo, hAwD, -, -, hδd, hδne, hsheets, hopen⟩ :=
    hbc σ I w U₀ hI hw (hU₀o.mem_nhds hwU₀)
  have hWU₀ : W ⊆ U₀ := fun z hz => hWU (subset_closure hz)
  have hWN : W ⊆ N := hWU₀.trans hU₀N
  have hnd'' : ∀ z ∈ zeroSetIn I ∩ W, ∀ V ∈ 𝓝 z, ∃ x ∈ zeroSetIn I ∩ V, G x ≠ 0 :=
    fun z hz => hnd' z ⟨hz.1, hWU₀ hz.2⟩
  have hGat : ∀ z ∈ N, DifferentiableAt ℂ G z := fun z hz => hG.differentiableAt (hNo.mem_nhds hz)

  have hKc : IsCompact (zeroSetIn I ∩ closure W) := hWc.inter_left (isClosed_zeroSetIn_of_ideal I)
  obtain ⟨MG, hMG⟩ : ∃ MG, ∀ z ∈ zeroSetIn I ∩ closure W, ‖G z‖ ≤ MG :=
    hKc.exists_bound_of_continuousOn (hG.continuousOn.mono fun z hz => hU₀N (hWU hz.2))

  obtain ⟨cG, hcGd, hcGeq⟩ := fibre_coeffs_extend (zeroSetIn I) W A D δ δ G MG hDo hδd hδne
    (fun _ _ h => h) hsheets (fun z hz => ⟨N, hNo, hWN hz.1.2, G, hG, fun _ _ => rfl⟩)
    (fun x hx _ _ => hMG x ⟨hx.1, subset_closure hx.2⟩)

  have hGeq : ∀ x ∈ zeroSetIn I ∩ W, A x ∈ D →
      G x ^ m + ∑ j, cG j (A x) * G x ^ (j : ℕ) = 0 := by
    intro x hx hAx
    refine eq_zero_of_zero_over_nonzero (zeroSetIn I) W A D δ hWo hDo hδne hopen hx hAx
      (fun z => G z ^ m + ∑ j, cG j (A z) * G z ^ (j : ℕ)) ?_ Set.univ Filter.univ_mem ?_
    · refine DifferentiableAt.continuousAt (((hGat x (hWN hx.2)).pow m).add
        (DifferentiableAt.fun_sum fun j _ => ?_))
      exact (((hcGd j).differentiableAt (hDo.mem_nhds hAx)).comp x A.differentiableAt).mul
        ((hGat x (hWN hx.2)).pow _)
    · rintro z ⟨⟨hzZ, hzW⟩, -⟩ hAz hδz
      obtain ⟨O, s, -, hyO, -, hsO⟩ := hsheets (A z) hAz hδz
      obtain ⟨h1, h2, h3⟩ := hsO (A z) hyO
      rw [hcGeq (A z) hAz hδz (fun j => s j (A z)) h1 h2 h3 (G z)]
      obtain ⟨i, hi⟩ := h3 z ⟨hzZ, hzW⟩ rfl
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      simp only at hi
      rw [hi, sub_self]

  set P : (Fin k → ℂ) → ℂ := fun y => (0 : ℂ) ^ m + ∑ j, cG j y * (0 : ℂ) ^ (j : ℕ) with hP
  have hPd : DifferentiableOn ℂ P D :=
    (differentiableOn_const _).add (DifferentiableOn.fun_sum fun j _ => (hcGd j).mul_const _)
  have hPzero : ∀ x ∈ zeroSetIn I ∩ W, A x ∈ D → G x = 0 → P (A x) = 0 := by
    intro x hx hAx hGx
    have := hGeq x hx hAx
    rw [hGx] at this
    exact this

  set g : (Fin k → ℂ) → ℂ := fun y => δ y * P y with hg
  have hgd : DifferentiableOn ℂ g D := hδd.mul hPd
  have hgne : ∀ V : Set (Fin k → ℂ), IsOpen V → V ⊆ D → V.Nonempty → ∃ t ∈ V, g t ≠ 0 := by
    intro V hVo hVD hVne
    obtain ⟨y, hyV, hδy⟩ := hδne V hVo hVD hVne
    obtain ⟨O, s, hOo, hyO, hsd, hsO⟩ := hsheets y (hVD hyV) hδy
    have hQo : IsOpen ((V ∩ O) ∩ δ ⁻¹' {0}ᶜ) :=
      (hδd.continuousOn.mono (Set.inter_subset_left.trans hVD)).isOpen_inter_preimage (hVo.inter hOo)
        isOpen_compl_singleton
    obtain ⟨y', ⟨⟨hy'V, hy'O⟩, hy'δ⟩, hall⟩ := exists_sheets_nonzero (zeroSetIn I) W A G O _ s hWo hOo hQo
      (fun _ h => h.1.2) ⟨y, ⟨hyV, hyO⟩, hδy⟩ hsd hsO (hG.continuousOn.mono hWN) hnd''
    refine ⟨y', hy'V, mul_ne_zero hy'δ ?_⟩
    obtain ⟨h1, h2, h3⟩ := hsO y' hy'O
    have hval := hcGeq y' (hVD hy'V) hy'δ (fun j => s j y') h1 h2 h3 0
    show P y' ≠ 0
    rw [hP]
    dsimp only
    rw [hval]
    exact Finset.prod_ne_zero_iff.2 fun j _ => by rw [zero_sub, neg_ne_zero]; exact hall j

  have hS : ∀ x ∈ zeroSetIn I ∩ W, A x ∈ D → g (A x) ≠ 0 →
      x ∈ (zeroSetIn I ∩ N) \ {z | G z = 0} := by
    intro x hx hAx hgx
    refine ⟨⟨hx.1, hWN hx.2⟩, fun hGx => hgx ?_⟩
    show δ (A x) * P (A x) = 0
    rw [hPzero x hx hAx hGx, mul_zero]
  have hfS : HolomorphicOnSubset f {x | x ∈ zeroSetIn I ∩ W ∧ A x ∈ D ∧ g (A x) ≠ 0} := by
    intro x hx
    obtain ⟨U, hU, hxU, F, hF, hfF⟩ := hf x (hS x hx.1 hx.2.1 hx.2.2)
    exact ⟨U, hU, hxU, F, hF, fun z hz => hfF ⟨hS z hz.1.1 hz.1.2.1 hz.1.2.2, hz.2⟩⟩
  obtain ⟨Mf, hMf⟩ := isBounded_iff_forall_norm_le.1 hfb

  obtain ⟨cf, hcfd, hcfeq⟩ := fibre_coeffs_extend (zeroSetIn I) W A D δ g f Mf hDo hgd hgne
    (fun _ _ h => left_ne_zero_of_mul h) hsheets hfS (fun x hx hAx hgx => hMf _ ⟨x, hS x hx hAx hgx, rfl⟩)
  refine ⟨W ∩ A ⁻¹' D, hWo.inter (hDo.preimage A.continuous), ⟨hwW, hAwD⟩, fun z hz => hWN hz.1, m,
    fun j z => cf j (A z), fun j => (hcfd j).comp A.differentiableOn fun z hz => hz.2, ?_⟩
  rintro z ⟨⟨hzZ, hzW, hzD⟩, hGz⟩
  have hzS : z ∈ (zeroSetIn I ∩ N) \ {z | G z = 0} := ⟨⟨hzZ, hWN hzW⟩, hGz⟩
  obtain ⟨U, hUo, hzU, F, hFd, hfF⟩ := hf z hzS
  have hGc : ContinuousAt G z := (hGat z (hWN hzW)).continuousAt
  have hV₀ : U ∩ N ∩ {x | G x ≠ 0} ∈ 𝓝 z :=
    Filter.inter_mem (Filter.inter_mem (hUo.mem_nhds hzU) (hNo.mem_nhds (hWN hzW))) (hGc.eventually_ne hGz)
  have key := eq_zero_of_zero_over_nonzero (zeroSetIn I) W A D g hWo hDo hgne hopen ⟨hzZ, hzW⟩ hzD
    (fun x => F x ^ m + ∑ j, cf j (A x) * F x ^ (j : ℕ)) ?_ _ hV₀ ?_
  · show f z ^ m + ∑ j, cf j (A z) * f z ^ (j : ℕ) = 0
    rw [hfF ⟨hzS, hzU⟩]
    exact key
  · have hFz : DifferentiableAt ℂ F z := hFd.differentiableAt (hUo.mem_nhds hzU)
    refine DifferentiableAt.continuousAt ((hFz.pow m).add (DifferentiableAt.fun_sum fun j _ => ?_))
    exact (((hcfd j).differentiableAt (hDo.mem_nhds hzD)).comp z A.differentiableAt).mul (hFz.pow _)
  · rintro x ⟨⟨hxZ, hxW⟩, ⟨hxU, hxN⟩, hxG⟩ hAx hgx
    have hxS : x ∈ (zeroSetIn I ∩ N) \ {z | G z = 0} := ⟨⟨hxZ, hxN⟩, hxG⟩
    show F x ^ m + ∑ j, cf j (A x) * F x ^ (j : ℕ) = 0
    rw [← hfF ⟨hxS, hxU⟩]
    obtain ⟨O, s, -, hyO, -, hsO⟩ := hsheets (A x) hAx (left_ne_zero_of_mul hgx)
    obtain ⟨h1, h2, h3⟩ := hsO (A x) hyO
    rw [hcfeq (A x) hAx hgx (fun j => s j (A x)) h1 h2 h3 (f x)]
    obtain ⟨i, hi⟩ := h3 x ⟨hxZ, hxW⟩ rfl
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp only at hi
    rw [hi, sub_self]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
