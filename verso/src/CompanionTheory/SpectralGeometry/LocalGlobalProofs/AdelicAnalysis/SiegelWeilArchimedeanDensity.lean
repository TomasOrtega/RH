import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaIntegralOverCoordinatesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaMeasureNonzeroVectorsBoundStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteComponentCoordinatesActionStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdelicLatticeMembershipIffStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MeasurableFiniteLevelLatticeSetStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BB.CountHyp

/- English proof (translation)
Simplify using `only [sizeTup, sizeInf, xw, cv, he, Fintype.sum_prod_type, Fin.sum_univ_one]`. Use `symm`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_comm`.
-/
theorem size_eq_sum {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {M d : ℕ} (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (he : ∀ y w, |e y w| = ‖y w‖) (X : Fin 1 → Fin M → Ainf F ⊗[F] E) :
    sizeTup b X = ∑ w, ∑ p, |xw e b X w p| := by
  simp only [sizeTup, sizeInf, xw, cv, he, Fintype.sum_prod_type, Fin.sum_univ_one]
  symm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

/- English proof (translation)
Rewrite using `[size_eq_sum b e he]`. Establish `h1 : ∀ w, ∑ p, |xw e b X w p| ≤ ((M * d : ℕ) : ℝ) * R`. Introduce `w`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ _ := by`. Apply `mul_le_mul_of_nonneg_right _ hR.le` to reduce the goal to its premises.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem size_le {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {M d : ℕ} (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (he : ∀ y w, |e y w| = ‖y w‖) (X : Fin 1 → Fin M → Ainf F ⊗[F] E) {R : ℝ} (hR : 0 < R)
    (h : ∀ w, ‖xw e b X w‖ ≤ R) :
    sizeTup b X ≤ ((M * d * Fintype.card (InfinitePlace F) + 1 : ℕ) : ℝ) * R := by
  rw [size_eq_sum b e he]
  have h1 : ∀ w, ∑ p, |xw e b X w p| ≤ ((M * d : ℕ) : ℝ) * R := by
    intro w
    calc ∑ p, |xw e b X w p| ≤ ∑ _p : Fin M × Fin d, R :=
          Finset.sum_le_sum fun p _ => (norm_le_pi_norm (xw e b X w) p).trans (h w)
      _ = ((M * d : ℕ) : ℝ) * R := by simp
  calc ∑ w, ∑ p, |xw e b X w p| ≤ ∑ _w : InfinitePlace F, ((M * d : ℕ) : ℝ) * R :=
        Finset.sum_le_sum fun w _ => h1 w
    _ = ((M * d * Fintype.card (InfinitePlace F) : ℕ) : ℝ) * R := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hR.le
        push_cast
        linarith

/- English proof (translation)
Use `not_congr ⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `⟨i, k⟩`. Establish `h1 : ∑ k, x (i, k) • b k = 0` using `congrFun (congrFun h 0) i`. Conclude with `Fintype.linearIndependent_iff.1 b.linearIndependent (fun k => x (i, k)) h1 k`. Substitute `h` using the available equality.

Use function extensionality and compare the values at `a i`. Simplify using `[ofF]`.
-/
theorem ofF_ne_zero_iff {F E : Type} [Field F] [Field E] [Algebra F E] {M d : ℕ}
    (b : Module.Basis (Fin d) F E) (x : Fin M × Fin d → F) : ofF b x ≠ 0 ↔ x ≠ 0 := by
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩
  · funext ⟨i, k⟩
    have h1 : ∑ k, x (i, k) • b k = 0 := congrFun (congrFun h 0) i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent (fun k => x (i, k)) h1 k
  · subst h
    funext a i
    simp [ofF]

/- English proof (translation)
Establish `hc0 : 0 < c` using `by linarith`. Establish `ha : 0 < c ^ a` using `by positivity`. Establish `hb : 0 < c ^ b` using `by positivity`. Establish `hRa : 0 < R ^ a` using `by positivity`. Establish `hRb : 0 < R ^ b` using `by positivity`.

Establish `h1 : C₀ * ((c * R) ^ a + (c * R) ^ b) ≤ |C₀| * ((c * R) ^ a + (c * R) ^ b)` using `mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)`. Use `h1.trans ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Apply `mul_le_mul_of_nonneg_left _ (abs_nonneg _)` to reduce the goal to its premises. Rewrite using `[mul_pow, mul_pow]`.

Use polynomial arithmetic with `[mul_pos ha hRb, mul_pos hb hRa]`.
-/
theorem real_bound {C₀ c R : ℝ} (hc : 1 ≤ c) (hR : 0 < R) (a b : ℕ) :
    C₀ * ((c * R) ^ a + (c * R) ^ b) ≤ (|C₀| * (c ^ a + c ^ b)) * (R ^ a + R ^ b) := by
  have hc0 : 0 < c := by linarith
  have ha : 0 < c ^ a := by positivity
  have hb : 0 < c ^ b := by positivity
  have hRa : 0 < R ^ a := by positivity
  have hRb : 0 < R ^ b := by positivity
  have h1 : C₀ * ((c * R) ^ a + (c * R) ^ b) ≤ |C₀| * ((c * R) ^ a + (c * R) ^ b) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  refine h1.trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  rw [mul_pow, mul_pow]
  nlinarith [mul_pos ha hRb, mul_pos hb hRa]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ hM d b ρ e hom hρ he μ 𝓕 hμ hF N hN`. Take `⟨C₀, hC₀⟩` from `GlobalTheory.T.theta_measure_nonzero_vectors_bound F E σ hCM M J hJ hM d b μ 𝓕 hμ hF N hN`. Use `set c : ℕ := M * d * Fintype.card (InfinitePlace F) + 1 with hc`. Establish `hc1 : (1 : ℝ) ≤ (c : ℝ)`. Establish `: 1 ≤ c` using `by omega`.

Conclude with `this` after adjusting the coercions. Use `set a := Module.finrank ℚ F * M with ha`. Use `set a2 := 2 * Module.finrank ℚ F * M with ha2`. Use `⟨|C₀| * ((c : ℝ) ^ a + (c : ℝ) ^ a2), fun R hR => ?_⟩` and prove the remaining obligations. Use `set S : Set (Fin 1 → Fin M → AF F ⊗[F] E) := {X | (∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV b v) ∧ sizeTup b (projInf X) ≤ c * R} with hS`.

Establish `hmeasSize : Measurable fun X : Fin 1 → Fin M → AF F ⊗[F] E => sizeTup b (projInf X)`. Take `⟨hp, -, -, -, -, -, -, -, hs⟩` from `GlobalTheory.T.adelic_tuple_projections F E σ hCM d b 1 1`. Establish `hcont : Continuous fun y : AF F ⊗[F] E => sizeInf b (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) y)`. Establish `h` using `hs.comp (hp.comp (continuous_pi fun _ : Fin 1 => continuous_pi fun _ : Fin 1 => (continuous_id : Continuous fun y : AF F ⊗[F] E => y)))`. Simplify `h` using `[Function.comp_def, sizeTup, projInf]`.

Use `haveI : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩`. Establish `hm` using `hcont.measurable`. Unfold `sizeTup projInf`. Use `Finset.measurable_sum _ fun p _ => Finset.measurable_sum _ fun i _ => ?_` and prove the remaining obligations. Conclude with `hm.comp ((measurable_pi_apply i).comp (measurable_pi_apply p))`.

Establish `hmeasS : MeasurableSet S` using `(GlobalTheory.T.measurable_finite_level_lattice_set F E σ hCM d M b N).inter (measurableSet_le hmeasSize measurable_const)`. Establish `hpull` using `GlobalTheory.T.theta_integral_over_coordinates F E σ hCM M J hJ d b μ 𝓕 hμ hF {x : Fin M × Fin d → F | x ≠ 0} {X : Fin 1 → Fin M → E | X ≠ 0} (fun x => ofF_ne_zero_iff b x) (S.indicator fun _ => (1 : ℝ≥0∞)) (measurable_const.indicator hmeasS)`. Rewrite `hpull` using `[lintegral_indicator_const hmeasS, one_mul]`. Establish `hpt : ∀ (ω : HA (AF F) σ J) (x : {x : Fin M × Fin d → F // x ≠ 0}), Set.indicator {x : Fin M × Fin d → F | (∀ i v, ((N : Af F) * (gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x j)) i) v ∈ v.adicCompletionIntegers F) ∧ ∀ w, ‖ginf e σ J b ω w *ᵥ fun j => ρ w (x j)‖ ≤ R} (fun _ => …`. Introduce `ω x`.

Distinguish the cases in `hA : x.1 ∈ {x : Fin M × Fin d → F | (∀ i v, ((N : Af F) * (gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x j)) i) v ∈ v.adicCompletionIntegers F) ∧ ∀ w, ‖ginf e σ J b ω w *ᵥ fun j => ρ w (x j)‖ ≤ R}`. Take `⟨h1, h2⟩` from `GlobalTheory.T.infinite_component_coordinates_action F E σ hCM M J hJ d b ρ e hρ ω x.1`. Establish `hY : actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1)) ∈ S`. Use `⟨(GlobalTheory.T.finite_adelic_lattice_membership_iff F E d M b N _).2 ?_, size_le b e he _ hR fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[h2]`.

Conclude with `hA.1`. Rewrite using `[h1 w]`. Conclude with `hA.2 w`. Rewrite using `[Set.indicator_of_mem hA, Set.indicator_of_mem hY]`. Rewrite using `[Set.indicator_of_notMem hA]`.

Conclude with `bot_le`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem main_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → (∀ y w, |e y w| = ‖y w‖) → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ N : ℕ, 0 < N → ∃ C : ℝ, ∀ R : ℝ, 0 < R → ∫⁻ ω, ∑' x : {x : Fin M × Fin d → F // x ≠ 0}, Set.indicator {x : Fin M × Fin d → F | (∀ i v, ((N : Af F) * (gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x j)) i) v ∈ v.adicCompletionIntegers F) ∧ ∀ w, ‖ginf e σ J b ω w *ᵥ fun j => ρ w (x j)‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) x.1 ∂(prH μ 𝓕) ≤ ENNReal.ofReal (C * (R ^ (Module.finrank ℚ F * M) + R ^ (2 * Module.finrank ℚ F * M))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM d b ρ e hom hρ he μ 𝓕 hμ hF N hN
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.T.theta_measure_nonzero_vectors_bound F E σ hCM M J hJ hM d b μ 𝓕 hμ hF N hN
  set c : ℕ := M * d * Fintype.card (InfinitePlace F) + 1 with hc
  have hc1 : (1 : ℝ) ≤ (c : ℝ) := by
    have : 1 ≤ c := by omega
    exact_mod_cast this
  set a := Module.finrank ℚ F * M with ha
  set a2 := 2 * Module.finrank ℚ F * M with ha2
  refine ⟨|C₀| * ((c : ℝ) ^ a + (c : ℝ) ^ a2), fun R hR => ?_⟩

  set S : Set (Fin 1 → Fin M → AF F ⊗[F] E) :=
    {X | (∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV b v) ∧
      sizeTup b (projInf X) ≤ c * R} with hS
  have hmeasSize : Measurable fun X : Fin 1 → Fin M → AF F ⊗[F] E => sizeTup b (projInf X) := by
    obtain ⟨hp, -, -, -, -, -, -, -, hs⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hCM d b 1 1
    have hcont : Continuous fun y : AF F ⊗[F] E =>
        sizeInf b (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) y) := by
      have h := hs.comp (hp.comp (continuous_pi fun _ : Fin 1 => continuous_pi fun _ : Fin 1 =>
        (continuous_id : Continuous fun y : AF F ⊗[F] E => y)))
      simpa [Function.comp_def, sizeTup, projInf] using h
    haveI : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
    have hm := hcont.measurable
    unfold sizeTup projInf
    refine Finset.measurable_sum _ fun p _ => Finset.measurable_sum _ fun i _ => ?_
    exact hm.comp ((measurable_pi_apply i).comp (measurable_pi_apply p))
  have hmeasS : MeasurableSet S :=
    (GlobalTheory.T.measurable_finite_level_lattice_set F E σ hCM d M b N).inter (measurableSet_le hmeasSize measurable_const)
  have hpull := GlobalTheory.T.theta_integral_over_coordinates F E σ hCM M J hJ d b μ 𝓕 hμ hF
    {x : Fin M × Fin d → F | x ≠ 0} {X : Fin 1 → Fin M → E | X ≠ 0}
    (fun x => ofF_ne_zero_iff b x) (S.indicator fun _ => (1 : ℝ≥0∞))
    (measurable_const.indicator hmeasS)
  rw [lintegral_indicator_const hmeasS, one_mul] at hpull
  have hpt : ∀ (ω : HA (AF F) σ J) (x : {x : Fin M × Fin d → F // x ≠ 0}),
      Set.indicator {x : Fin M × Fin d → F | (∀ i v, ((N : Af F) * (gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x j)) i) v ∈ v.adicCompletionIntegers F) ∧ ∀ w, ‖ginf e σ J b ω w *ᵥ fun j => ρ w (x j)‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) x.1 ≤
      S.indicator (fun _ => (1 : ℝ≥0∞)) (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1))) := by
    intro ω x
    by_cases hA : x.1 ∈ {x : Fin M × Fin d → F | (∀ i v, ((N : Af F) * (gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x j)) i) v ∈ v.adicCompletionIntegers F) ∧ ∀ w, ‖ginf e σ J b ω w *ᵥ fun j => ρ w (x j)‖ ≤ R}
    · obtain ⟨h1, h2⟩ := GlobalTheory.T.infinite_component_coordinates_action F E σ hCM M J hJ d b ρ e hρ ω x.1
      have hY : actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1)) ∈ S := by
        refine ⟨(GlobalTheory.T.finite_adelic_lattice_membership_iff F E d M b N _).2 ?_, size_le b e he _ hR fun w => ?_⟩
        · rw [h2]
          exact hA.1
        · rw [h1 w]
          exact hA.2 w
      rw [Set.indicator_of_mem hA, Set.indicator_of_mem hY]
    · rw [Set.indicator_of_notMem hA]
      exact bot_le
  calc _ ≤ ∫⁻ ω, ∑' x : {x : Fin M × Fin d → F // x ≠ 0},
        S.indicator (fun _ => (1 : ℝ≥0∞)) (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1))) ∂(prH μ 𝓕) :=
        lintegral_mono fun ω => ENNReal.tsum_le_tsum fun x => hpt ω x
    _ = thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0} S := hpull.symm
    _ ≤ ENNReal.ofReal (C₀ * (((c : ℝ) * R) ^ a + ((c : ℝ) * R) ^ a2)) :=
        hC₀ ((c : ℝ) * R) (mul_pos (by linarith) hR)
    _ ≤ _ := ENNReal.ofReal_le_ofReal (real_bound hc1 hR a a2)

end GlobalTheory.CompanionTheory.SW.BB.CountHyp
