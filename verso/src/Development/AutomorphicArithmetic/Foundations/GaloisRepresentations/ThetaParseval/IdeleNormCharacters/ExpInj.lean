import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.AbsFactsAlt

open NumberField IsDedekindDomain GlobalTheory.AdelicU

namespace UpperTheory.Gal.TP.Chr

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `hs` using `InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex (IsTotallyComplex.isComplex (InfinitePlace.mk τ))`. Establish `hc : Continuous (InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk τ))` using `(InfinitePlace.Completion.isometry_extensionEmbedding _).continuous`. Establish `hv : ∀ x : E, InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk τ) (algebraMap E _ x) = (InfinitePlace.mk τ).embedding x` using `fun x => InfinitePlace.Completion.extensionEmbedding_coe _ (WithAbs.toAbs _ x)`. Break down `InfinitePlace.embedding_mk_eq τ with h | h` into its components or cases. Conclude with `⟨_, hc, hs, fun x => by rw [hv, h]⟩`.

Use `⟨fun z => starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding _ z), Complex.continuous_conj.comp hc, fun y => ?_, fun x => ?_⟩` and prove the remaining obligations. Take `⟨z, hz⟩` from `hs (starRingEnd ℂ y)`. Conclude with `⟨z, by simp [hz]⟩`. Simplify using `only [hv, h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]`.
-/
private lemma exists_ext (τ : E →+* ℂ) :
    ∃ e : (InfinitePlace.mk τ).Completion → ℂ, Continuous e ∧ Function.Surjective e ∧
      ∀ x : E, e (algebraMap E _ x) = τ x := by
  have hs := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex
    (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
  have hc : Continuous (InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk τ)) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous
  have hv : ∀ x : E, InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk τ)
      (algebraMap E _ x) = (InfinitePlace.mk τ).embedding x := fun x =>
    InfinitePlace.Completion.extensionEmbedding_coe _ (WithAbs.toAbs _ x)
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · exact ⟨_, hc, hs, fun x => by rw [hv, h]⟩
  · refine ⟨fun z => starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding _ z),
      Complex.continuous_conj.comp hc, fun y => ?_, fun x => ?_⟩
    · obtain ⟨z, hz⟩ := hs (starRingEnd ℂ y)
      exact ⟨z, by simp [hz]⟩
    · simp only [hv, h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

/- English proof (translation)
Establish `key : ∀ w, (InfinitePlace.mk (emb w).1).comap (algebraMap (maximalRealSubfield E) E) = w`. Introduce `w`. Rewrite using `[InfinitePlace.comap_mk, (emb w).2, InfinitePlace.mk_embedding]`. Establish `hinj : ∀ w w', InfinitePlace.mk (emb w).1 = InfinitePlace.mk (emb w').1 → w = w'`. Introduce `w w' h`.

Rewrite using `[← key w, ← key w', h]`. Use `choose e hc hs he using fun w => exists_ext (emb w).1`. Set `T : (∀ v : InfinitePlace E, v.Completion) → (∀ _ : InfinitePlace (maximalRealSubfield E), ℂ)` to `fun f w => e w (f (InfinitePlace.mk (emb w).1))`. Establish `hT : Continuous T` using `continuous_pi fun w => (hc w).comp (continuous_apply _)`. Establish `hTs : Function.Surjective T`.

Introduce `y`. Use `choose g hg using fun w => hs w (y w)`. Establish `hcast : ∀ w w' (h : InfinitePlace.mk (emb w').1 = InfinitePlace.mk (emb w).1), (h ▸ g w' : (InfinitePlace.mk (emb w).1).Completion) = g w`. Introduce `w w' h`. Take `rfl` from `hinj _ _ h`.

Both sides reduce to the same expression. Use `⟨fun v => if h : ∃ w, InfinitePlace.mk (emb w).1 = v then h.choose_spec ▸ g h.choose else 0, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `w`. Establish `hex : ∃ w', InfinitePlace.mk (emb w').1 = InfinitePlace.mk (emb w).1` using `⟨w, rfl⟩`. Simplify using `only [T, dif_pos hex]`.

Rewrite using `[hcast w _ hex.choose_spec, hg]`. Establish `hd` using `hTs.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hT`. Use `hd using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x w`. Conclude with `(he w x).symm`.
-/
private lemma dense_emb (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w) :
    DenseRange (fun (x : E) (w : InfinitePlace (maximalRealSubfield E)) => (emb w).1 x) := by
  classical
  have key : ∀ w, (InfinitePlace.mk (emb w).1).comap (algebraMap (maximalRealSubfield E) E) = w := by
    intro w
    rw [InfinitePlace.comap_mk, (emb w).2, InfinitePlace.mk_embedding]
  have hinj : ∀ w w', InfinitePlace.mk (emb w).1 = InfinitePlace.mk (emb w').1 → w = w' := by
    intro w w' h
    rw [← key w, ← key w', h]
  choose e hc hs he using fun w => exists_ext (emb w).1
  let T : (∀ v : InfinitePlace E, v.Completion) → (∀ _ : InfinitePlace (maximalRealSubfield E), ℂ) :=
    fun f w => e w (f (InfinitePlace.mk (emb w).1))
  have hT : Continuous T := continuous_pi fun w => (hc w).comp (continuous_apply _)
  have hTs : Function.Surjective T := by
    intro y
    choose g hg using fun w => hs w (y w)
    have hcast : ∀ w w' (h : InfinitePlace.mk (emb w').1 = InfinitePlace.mk (emb w).1),
        (h ▸ g w' : (InfinitePlace.mk (emb w).1).Completion) = g w := by
      intro w w' h
      obtain rfl := hinj _ _ h
      rfl
    refine ⟨fun v => if h : ∃ w, InfinitePlace.mk (emb w).1 = v then h.choose_spec ▸ g h.choose else 0, ?_⟩
    funext w
    have hex : ∃ w', InfinitePlace.mk (emb w').1 = InfinitePlace.mk (emb w).1 := ⟨w, rfl⟩
    simp only [T, dif_pos hex]
    rw [hcast w _ hex.choose_spec, hg]
  have hd := hTs.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hT
  convert hd using 1
  funext x w
  exact (he w x).symm

end

/- English proof (translation)
Introduce `E _ _ _ emb m m' s s' h`. Use function extensionality and compare the values at `w₀`. Set `F : (InfinitePlace (maximalRealSubfield E) → ℤ) → ℤ → (InfinitePlace (maximalRealSubfield E) → ℂ) → ℂ` to `fun n t y => ∏ w, (y w / ‖y w‖) ^ n w * ((‖y w‖ : ℝ) : ℂ) ^ t`. Set `U : Set (InfinitePlace (maximalRealSubfield E) → ℂ)` to `{y | ∀ w, y w ≠ 0}`. Establish `hU : IsOpen U`.

Simplify using `only [U, Set.setOf_forall]`. Conclude with `isOpen_iInter_of_finite fun w => isOpen_ne_fun (continuous_apply w) continuous_const`. Establish `hcont : ∀ n t, ContinuousOn (F n t) U`. Introduce `n t`. Use `continuousOn_finset_prod _ fun w _ => ?_` and prove the remaining obligations.

Establish `h1 : Continuous fun y : InfinitePlace (maximalRealSubfield E) → ℂ => y w` using `continuous_apply w`. Establish `h2 : Continuous fun y : InfinitePlace (maximalRealSubfield E) → ℂ => ((‖y w‖ : ℝ) : ℂ)` using `Complex.continuous_ofReal.comp h1.norm`. Establish `hne : ∀ y ∈ U, ((‖y w‖ : ℝ) : ℂ) ≠ 0` using `fun y hy => by`. Simplify using `using hy w`. Use `ContinuousOn.mul (ContinuousOn.zpow₀ (h1.continuousOn.div h2.continuousOn hne) _ fun y hy => Or.inl (div_ne_zero (hy w) (hne y hy))) (ContinuousOn.zpow₀ h2.continuousOn _ fun y hy => Or.inl (hne y hy))` and prove the remaining obligations.

Establish `hEq : ∀ y ∈ U, F m s y = F m' s' y`. Introduce `y hy`. Assume the negation of the conclusion as `hne`. Establish `hop` using `((hcont m s).sub (hcont m' s')).isOpen_inter_preimage hU (isOpen_compl_singleton (x := (0 : ℂ)))`. Take `⟨x, hxU, hx⟩` from `(dense_emb emb).exists_mem_open hop ⟨y, hy, fun h0 => hne (sub_eq_zero.1 h0)⟩`.

Establish `hx0 : x ≠ 0` using `fun h0 => hxU w₀ (by simp [h0])`. Conclude with `hx (sub_eq_zero.2 (h (Units.mk0 x hx0)))`. Establish `hF : ∀ n t (θ : ℝ), F n t (Function.update (1 : InfinitePlace (maximalRealSubfield E) → ℂ) w₀ (Complex.exp (θ * Complex.I))) = Complex.exp (θ * Complex.I) ^ n w₀`. Introduce `n t θ`. Simplify using `only [F]`.

Rewrite using `[Finset.prod_eq_single w₀]`. Simplify using `[Complex.norm_exp_ofReal_mul_I]`. Introduce `w _ hw`. Simplify using `[Function.update_of_ne hw]`. Simplify using the standard rewrite rules.

Establish `hUy : ∀ θ : ℝ, Function.update (1 : InfinitePlace (maximalRealSubfield E) → ℂ) w₀ (Complex.exp (θ * Complex.I)) ∈ U`. Introduce `θ w`. Distinguish the cases in `hw : w = w₀`. Substitute `hw` using the available equality. Simplify using `[Complex.exp_ne_zero]`.

Simplify using `[Function.update_of_ne hw]`. Assume the negation of the conclusion as `hne`. Establish `hd0 : ((m w₀ - m' w₀ : ℤ) : ℝ) ≠ 0`. Conclude with `sub_ne_zero.2 hne` after adjusting the coercions. Use `set θ : ℝ := Real.pi / ((m w₀ - m' w₀ : ℤ) : ℝ) with hθ`.

Establish `h1` using `hEq _ (hUy θ)`. Rewrite `h1` using `[hF, hF]`. Establish `h2 : Complex.exp (θ * Complex.I) ^ (m w₀ - m' w₀) = 1`. Rewrite using `[zpow_sub₀ (Complex.exp_ne_zero _), h1, div_self (zpow_ne_zero _ (Complex.exp_ne_zero _))]`. Rewrite `h2` using `[← Complex.exp_int_mul]`.

Establish `h3 : ((m w₀ - m' w₀ : ℤ) : ℂ) * (θ * Complex.I) = Real.pi * Complex.I`. Establish `: ((m w₀ - m' w₀ : ℤ) : ℂ) * (θ : ℂ) = Real.pi`. Establish `: ((m w₀ - m' w₀ : ℤ) : ℝ) * θ = Real.pi`. Rewrite using `[hθ]`. Clear the denominators using the available nonvanishing facts.

Conclude with `this` after adjusting the coercions. Rewrite using `[← mul_assoc, this]`. Rewrite `h2` using `[h3, Complex.exp_pi_mul_I]`. Evaluate the numerical expressions using `at h2`.
-/
theorem expInj : ExpInj := by
  intro E _ _ _ emb m m' s s' h
  classical
  funext w₀
  let F : (InfinitePlace (maximalRealSubfield E) → ℤ) → ℤ →
      (InfinitePlace (maximalRealSubfield E) → ℂ) → ℂ :=
    fun n t y => ∏ w, (y w / ‖y w‖) ^ n w * ((‖y w‖ : ℝ) : ℂ) ^ t
  let U : Set (InfinitePlace (maximalRealSubfield E) → ℂ) := {y | ∀ w, y w ≠ 0}
  have hU : IsOpen U := by
    simp only [U, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun w => isOpen_ne_fun (continuous_apply w) continuous_const
  have hcont : ∀ n t, ContinuousOn (F n t) U := by
    intro n t
    refine continuousOn_finset_prod _ fun w _ => ?_
    have h1 : Continuous fun y : InfinitePlace (maximalRealSubfield E) → ℂ => y w := continuous_apply w
    have h2 : Continuous fun y : InfinitePlace (maximalRealSubfield E) → ℂ => ((‖y w‖ : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp h1.norm
    have hne : ∀ y ∈ U, ((‖y w‖ : ℝ) : ℂ) ≠ 0 := fun y hy => by
      simpa using hy w
    refine ContinuousOn.mul (ContinuousOn.zpow₀ (h1.continuousOn.div h2.continuousOn hne) _
      fun y hy => Or.inl (div_ne_zero (hy w) (hne y hy))) (ContinuousOn.zpow₀ h2.continuousOn _
      fun y hy => Or.inl (hne y hy))
  have hEq : ∀ y ∈ U, F m s y = F m' s' y := by
    intro y hy
    by_contra hne
    have hop := ((hcont m s).sub (hcont m' s')).isOpen_inter_preimage hU
      (isOpen_compl_singleton (x := (0 : ℂ)))
    obtain ⟨x, hxU, hx⟩ := (dense_emb emb).exists_mem_open hop
      ⟨y, hy, fun h0 => hne (sub_eq_zero.1 h0)⟩
    have hx0 : x ≠ 0 := fun h0 => hxU w₀ (by simp [h0])
    exact hx (sub_eq_zero.2 (h (Units.mk0 x hx0)))
  have hF : ∀ n t (θ : ℝ), F n t (Function.update (1 : InfinitePlace (maximalRealSubfield E) → ℂ) w₀ (Complex.exp (θ * Complex.I))) =
      Complex.exp (θ * Complex.I) ^ n w₀ := by
    intro n t θ
    simp only [F]
    rw [Finset.prod_eq_single w₀]
    · simp [Complex.norm_exp_ofReal_mul_I]
    · intro w _ hw
      simp [Function.update_of_ne hw]
    · simp
  have hUy : ∀ θ : ℝ, Function.update (1 : InfinitePlace (maximalRealSubfield E) → ℂ) w₀ (Complex.exp (θ * Complex.I)) ∈ U := by
    intro θ w
    by_cases hw : w = w₀
    · subst hw; simp [Complex.exp_ne_zero]
    · simp [Function.update_of_ne hw]
  by_contra hne
  have hd0 : ((m w₀ - m' w₀ : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.2 hne
  set θ : ℝ := Real.pi / ((m w₀ - m' w₀ : ℤ) : ℝ) with hθ
  have h1 := hEq _ (hUy θ)
  rw [hF, hF] at h1
  have h2 : Complex.exp (θ * Complex.I) ^ (m w₀ - m' w₀) = 1 := by
    rw [zpow_sub₀ (Complex.exp_ne_zero _), h1, div_self (zpow_ne_zero _ (Complex.exp_ne_zero _))]
  rw [← Complex.exp_int_mul] at h2
  have h3 : ((m w₀ - m' w₀ : ℤ) : ℂ) * (θ * Complex.I) = Real.pi * Complex.I := by
    have : ((m w₀ - m' w₀ : ℤ) : ℂ) * (θ : ℂ) = Real.pi := by
      have : ((m w₀ - m' w₀ : ℤ) : ℝ) * θ = Real.pi := by
        rw [hθ]; field_simp
      exact_mod_cast this
    rw [← mul_assoc, this]
  rw [h3, Complex.exp_pi_mul_I] at h2
  norm_num at h2

end UpperTheory.Gal.TP.Chr
