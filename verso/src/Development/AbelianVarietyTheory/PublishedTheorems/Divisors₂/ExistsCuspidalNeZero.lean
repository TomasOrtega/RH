import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.SiegelSet.Model

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `e : ∑ i, σ (z i) * z i = 0`. Simplify `hz` using `[hE, Formalism.UG.hform, Matrix.one_apply]`. Establish `e2` using `congrArg (fun x => (τ x).re) e`. Simplify using `only [map_sum, map_mul, h.2.2.2, map_zero, Complex.zero_re, Complex.re_sum, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re] at e2`.

Use function extensionality and compare the values at `i`. Use `(Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg (τ (z i))).1 e2 i (Finset.mem_univ i)` as an intermediate fact. Conclude with `τ.injective (by simpa using this)`.
-/
theorem aniso_one (h : IsCMExt F E σ) (z : Fin n → E) (hz : hE σ (1 : Matrix (Fin n) (Fin n) E) z z = 0) : z = 0 := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have e : ∑ i, σ (z i) * z i = 0 := by
    simpa [hE, Formalism.UG.hform, Matrix.one_apply] using hz
  have e2 := congrArg (fun x => (τ x).re) e
  simp only [map_sum, map_mul, h.2.2.2, map_zero, Complex.zero_re, Complex.re_sum, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re] at e2
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg (τ (z i))).1 e2 i (Finset.mem_univ i)
  exact τ.injective (by simpa using this)

/- English proof (translation)
Assemble the required witnesses or components as `⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _, fun z _ _ hz => aniso_one h z hz⟩`.
-/
theorem isWittFrame_one (h : IsCMExt F E σ) :
    IsWittFrame σ (1 : Matrix (Fin n) (Fin n) E) (0 : Matrix (Fin n) (Fin 0) E) 0 :=
  ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _, fun z _ _ hz => aniso_one h z hz⟩

/- English proof (translation)
Introduce and unpack `r C ⟨hr, hC, h0⟩`. Establish `h1` using `(gram_apply (σ := σ) (J := J) C C ⟨0, hr⟩ ⟨0, hr⟩).symm.trans (congrFun (congrFun h0 _) _)`. Use `absurd (hW.aniso (Cᵀ ⟨0, hr⟩) (Subsingleton.elim _ _) (Subsingleton.elim _ _) ?_) (hC.ne_zero _)` and prove the remaining obligations. Use `Eq.trans ?_ h1` and prove the remaining obligations. Simplify using `only [hE, Formalism.UG.hform, toLinearMapₛₗ₂'_apply, smul_eq_mul, RingHom.id_apply]`.

Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem isCuspidal_of_empty {X Y : Matrix (Fin n) (Fin 0) E} (hW : IsWittFrame σ J X Y) (φ : GAd σ J → ℂ) :
    IsCuspidal σ J φ := by
  rintro r C ⟨hr, hC, h0⟩
  have h1 := (gram_apply (σ := σ) (J := J) C C ⟨0, hr⟩ ⟨0, hr⟩).symm.trans (congrFun (congrFun h0 _) _)
  refine absurd (hW.aniso (Cᵀ ⟨0, hr⟩) (Subsingleton.elim _ _) (Subsingleton.elim _ _) ?_) (hC.ne_zero _)
  refine Eq.trans ?_ h1
  simp only [hE, Formalism.UG.hform, toLinearMapₛₗ₂'_apply, smul_eq_mul, RingHom.id_apply]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => 1, fun e => one_ne_zero (congrFun e 1), isSmoothModerate_const σ _ 1, isCuspidal_of_empty (isWittFrame_one h) _⟩`.
-/
theorem exists_cuspidal_ne_zero (h : IsCMExt F E σ) : ∃ φ : GAd σ (1 : Matrix (Fin n) (Fin n) E) → ℂ,
    φ ≠ 0 ∧ IsSmoothModerate σ _ φ ∧ IsCuspidal σ _ φ :=
  ⟨fun _ => 1, fun e => one_ne_zero (congrFun e 1), isSmoothModerate_const σ _ 1,
    isCuspidal_of_empty (isWittFrame_one h) _⟩

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Take `⟨τ⟩ : Nonempty (EmbOver E w)` from `inferInstance`. Establish `e` using `(h.2 w τ).1.symm.trans (h'.2 w τ).1`. Use function extensionality and compare the values at `i`. Assume the negation of the conclusion as `hne`.

Establish `hx : ∀ k, X k i = 0` using `fun k => by`. Use `congrFun (congrFun e k) i` as an intermediate fact. Simplify using `only [mul_diagonal, map_apply] at this`. Break down `mul_eq_mul_left_iff.1 this with h1 | h1` into its components or cases. Conclude with `absurd (Complex.ofReal_injective h1) hne`.

Conclude with `τ.1.injective (h1.trans (map_zero _).symm)`. Use `congrFun (congrFun hW.xy i) i` as an intermediate fact. Simplify using `[Matrix.mul_apply, cT, hx] at this`.
-/
theorem param_unique {X Y : Matrix (Fin n) (Fin r) E} (hW : IsWittFrame σ J X Y) {t t' : Fin r → ℝ} {a : GAd σ J}
    (h : IsTorusElt σ J X Y t a) (h' : IsTorusElt σ J X Y t' a) : t = t' := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  have e := (h.2 w τ).1.symm.trans (h'.2 w τ).1
  funext i
  by_contra hne
  have hx : ∀ k, X k i = 0 := fun k => by
    have := congrFun (congrFun e k) i
    simp only [mul_diagonal, map_apply] at this
    rcases mul_eq_mul_left_iff.1 this with h1 | h1
    · exact absurd (Complex.ofReal_injective h1) hne
    · exact τ.1.injective (h1.trans (map_zero _).symm)
  have := congrFun (congrFun hW.xy i) i
  simp [Matrix.mul_apply, cT, hx] at this

/- English proof (translation)
Use `GAd_ext σ J (fun w => ?_) fun v => by rw [mem_infPts_iff_forall.1 ha.1 v, map_one]` and prove the remaining obligations. Take `⟨τ⟩ : Nonempty (EmbOver E w)` from `inferInstance`. Apply `(archEquiv J h τ).injective` to reduce the goal to its premises. Rewrite using `[map_one, map_one]`. Use `Subtype.ext (Units.ext ?_)` and prove the remaining obligations.

Rewrite using `[← GlobalTheory.Orb.archMat_eq_archEquiv J h]`. Use extensionality with `i j`. Use `congrFun ((ha.2 w τ).2.2 (Pi.single j 1) (Subsingleton.elim _ _) (Subsingleton.elim _ _)) i` as an intermediate fact. Simplify `this` using `[mulVec, dotProduct, Pi.single_apply, apply_ite, Matrix.one_apply]`.
-/
theorem torus_eq_one (h : IsCMExt F E σ) {X Y : Matrix (Fin n) (Fin 0) E} {t : Fin 0 → ℝ} {a : GAd σ J}
    (ha : IsTorusElt σ J X Y t a) : a = 1 := by
  refine GAd_ext σ J (fun w => ?_) fun v => by rw [mem_infPts_iff_forall.1 ha.1 v, map_one]
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  apply (archEquiv J h τ).injective
  rw [map_one, map_one]
  refine Subtype.ext (Units.ext ?_)
  rw [← GlobalTheory.Orb.archMat_eq_archEquiv J h]
  ext i j
  have := congrFun ((ha.2 w τ).2.2 (Pi.single j 1) (Subsingleton.elim _ _) (Subsingleton.elim _ _)) i
  simpa [mulVec, dotProduct, Pi.single_apply, apply_ite, Matrix.one_apply] using this

/- English proof (translation)
Take `⟨K, Ω, c, hK, hΩ, -, -, -, -, hcov, -⟩` from `hP F E σ h n J hJ 0 X Y hW`. Use `⟨_, hΩ.mul hK, fun g => ?_⟩` and prove the remaining obligations. Take `⟨γ, hγ, _, ⟨p, hp, t, -, a, ha, k, hk, rfl⟩, e⟩` from `hcov g`. Conclude with `⟨γ, hγ, _, ⟨p, hp, k, hk, rfl⟩, by rw [e, torus_eq_one h ha, mul_one]⟩`.
-/
theorem compact_quotient (hP : GlobalTheory.Published.SiegelSetUnitary) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    {X Y : Matrix (Fin n) (Fin 0) E} (hW : IsWittFrame σ J X Y) :
    ∃ C : Set (GAd σ J), IsCompact C ∧ ∀ g, ∃ γ ∈ ratPts σ J, ∃ s ∈ C, g = γ * s := by
  obtain ⟨K, Ω, c, hK, hΩ, -, -, -, -, hcov, -⟩ := hP F E σ h n J hJ 0 X Y hW
  refine ⟨_, hΩ.mul hK, fun g => ?_⟩
  obtain ⟨γ, hγ, _, ⟨p, hp, t, -, a, ha, k, hk, rfl⟩, e⟩ := hcov g
  exact ⟨γ, hγ, _, ⟨p, hp, k, hk, rfl⟩, by rw [e, torus_eq_one h ha, mul_one]⟩

/- English proof (translation)
Establish `hc : ∀ t : Fin 0 → ℝ, t ∈ cone 0 1` using `fun t => ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩`. Establish `ht : ∀ t : Fin 0 → ℝ, IsTorusElt σ J X Y t 1` using `fun t => by`. Take `⟨a, ha⟩` from `exists_isTorusElt h hJ hW (t := t) fun i => i.elim0`. Conclude with `torus_eq_one h ha ▸ ha`. Establish `hP : ∀ g, g ∈ minParOne σ J X` using `fun g => ⟨0, fun i => i.elim0, Matrix.ext fun _ j => j.elim0, fun i => i.elim0⟩`.

Establish `hS : siegelSet σ J X Y Ω 1 ⊥ = Ω`. Use extensionality with `g`. Use `⟨?_, fun hg => ⟨g, hg, 0, hc _, 1, ht _, 1, one_mem _, by simp⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨p, hp, t, -, a, ha, k, hk, rfl⟩`. Rewrite using `[torus_eq_one h ha, Subgroup.mem_bot.1 hk, mul_one, mul_one]` and apply the resulting hypothesis.

Establish `hh : Continuous (height σ J)` using `(GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val`. Use `⟨⊥, Ω, 1, by simp, hΩ, fun g _ => hP g, one_pos, fun g => ⟨g, hP g, 0, 1, fun i => i.elim0, ht _, 1, one_mem _, by simp⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hS]`. Use `⟨hΩ.isClosed, hcov, ⟨Ω, hΩ, fun p hp t _ a ha => by simpa [torus_eq_one h ha] using hp⟩, fun μ _ => ⟨hΩ.measure_lt_top, (μ Ω).toNNReal, fun f k _ hf => ?_⟩, ?_, fun φ hφ _ N => ?_⟩` and prove the remaining obligations. Establish `e : cone 0 1 = Set.univ` using `Set.eq_univ_of_forall hc`.

Establish `e2 : (volume : Measure (Fin 0 → ℝ)) = Measure.dirac 0`. Rewrite using `[volume_pi, Measure.pi_of_empty _ 0]`. Rewrite using `[e, Measure.restrict_univ, e2, lintegral_dirac, ENNReal.coe_toNNReal hΩ.measure_lt_top.ne]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨g₀, -, hg₀⟩` from `hΩ.exists_isMaxOn ⟨1, h1⟩ hh.continuousOn`.

Conclude with `⟨height σ J g₀, 0, fun g hg γ _ => by simpa using hg₀ hg⟩`. Establish `hcont : Continuous fun g => ‖φ g‖ * (height σ J g : ℝ) ^ N` using `hφ.cont.norm.mul ((NNReal.continuous_coe.comp hh).pow N)`. Take `⟨g₀, -, hg₀⟩` from `hΩ.exists_isMaxOn ⟨1, h1⟩ hcont.continuousOn`. Conclude with `⟨_, fun g hg => hg₀ hg⟩`.
-/
theorem clauses_of_compact (h : IsCMExt F E σ) (hJ : IsHermND σ J) {X Y : Matrix (Fin n) (Fin 0) E}
    (hW : IsWittFrame σ J X Y) {Ω : Set (GAd σ J)} (hΩ : IsCompact Ω) (h1 : (1 : GAd σ J) ∈ Ω)
    (hcov : ∀ g, ∃ γ ∈ ratPts σ J, ∃ s ∈ Ω, g = γ * s) :
    ∃ (K : Subgroup (GAd σ J)) (Ω : Set (GAd σ J)) (c : ℝ),
      IsCompact (K : Set (GAd σ J)) ∧ IsCompact Ω ∧ Ω ⊆ minParOne σ J X ∧ 0 < c ∧
      (∀ g, ∃ p ∈ minParOne σ J X, ∃ t a, (∀ i, 0 < t i) ∧ IsTorusElt σ J X Y t a ∧ ∃ k ∈ K, g = p * a * k) ∧
      IsClosed (siegelSet σ J X Y Ω c K) ∧
      (∀ g, ∃ γ ∈ ratPts σ J, ∃ s ∈ siegelSet σ J X Y Ω c K, g = γ * s) ∧
      (∃ C : Set (GAd σ J), IsCompact C ∧ ∀ p ∈ Ω, ∀ t ∈ cone 0 c, ∀ a, IsTorusElt σ J X Y t a → a⁻¹ * p * a ∈ C) ∧
      (∀ μ : Measure (GAd σ J), μ.IsHaarMeasure → μ (siegelSet σ J X Y Ω c K) < ⊤ ∧
        ∃ C : ℝ≥0, ∀ (f : GAd σ J → ℝ≥0∞) (h : (Fin 0 → ℝ) → ℝ≥0∞), Measurable h →
          (∀ p ∈ Ω, ∀ t ∈ cone 0 c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ K, f (p * a * k) ≤ h t) →
          ∫⁻ g in siegelSet σ J X Y Ω c K, f g ∂μ ≤
            C * ∫⁻ t in cone 0 c, h t * ENNReal.ofReal ((modulus F n t * ∏ i, t i)⁻¹)) ∧
      (∃ (C : ℝ≥0) (A : ℕ), ∀ g ∈ siegelSet σ J X Y Ω c K, ∀ γ ∈ ratPts σ J,
        height σ J g ≤ C * height σ J (γ * g) ^ A) ∧
      ∀ φ : GAd σ J → ℂ, IsSmoothModerate σ J φ → IsCuspidal σ J φ →
        ∀ N : ℕ, ∃ C : ℝ, ∀ g ∈ siegelSet σ J X Y Ω c K, ‖φ g‖ * (height σ J g : ℝ) ^ N ≤ C := by
  have hc : ∀ t : Fin 0 → ℝ, t ∈ cone 0 1 := fun t => ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  have ht : ∀ t : Fin 0 → ℝ, IsTorusElt σ J X Y t 1 := fun t => by
    obtain ⟨a, ha⟩ := exists_isTorusElt h hJ hW (t := t) fun i => i.elim0
    exact torus_eq_one h ha ▸ ha
  have hP : ∀ g, g ∈ minParOne σ J X := fun g =>
    ⟨0, fun i => i.elim0, Matrix.ext fun _ j => j.elim0, fun i => i.elim0⟩
  have hS : siegelSet σ J X Y Ω 1 ⊥ = Ω := by
    ext g
    refine ⟨?_, fun hg => ⟨g, hg, 0, hc _, 1, ht _, 1, one_mem _, by simp⟩⟩
    rintro ⟨p, hp, t, -, a, ha, k, hk, rfl⟩
    rwa [torus_eq_one h ha, Subgroup.mem_bot.1 hk, mul_one, mul_one]
  have hh : Continuous (height σ J) := (GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val
  refine ⟨⊥, Ω, 1, by simp, hΩ, fun g _ => hP g, one_pos,
    fun g => ⟨g, hP g, 0, 1, fun i => i.elim0, ht _, 1, one_mem _, by simp⟩, ?_⟩
  rw [hS]
  refine ⟨hΩ.isClosed, hcov, ⟨Ω, hΩ, fun p hp t _ a ha => by simpa [torus_eq_one h ha] using hp⟩,
    fun μ _ => ⟨hΩ.measure_lt_top, (μ Ω).toNNReal, fun f k _ hf => ?_⟩, ?_, fun φ hφ _ N => ?_⟩
  · have e : cone 0 1 = Set.univ := Set.eq_univ_of_forall hc
    have e2 : (volume : Measure (Fin 0 → ℝ)) = Measure.dirac 0 := by
      rw [volume_pi, Measure.pi_of_empty _ 0]
    rw [e, Measure.restrict_univ, e2, lintegral_dirac, ENNReal.coe_toNNReal hΩ.measure_lt_top.ne]
    calc ∫⁻ g in Ω, f g ∂μ ≤ ∫⁻ _ in Ω, k 0 ∂μ :=
          setLIntegral_mono' hΩ.measurableSet fun g hg => by simpa using hf g hg 0 (hc _) 1 (ht _) 1 (one_mem _)
      _ = _ := by simp [modulus, mul_comm]
  · obtain ⟨g₀, -, hg₀⟩ := hΩ.exists_isMaxOn ⟨1, h1⟩ hh.continuousOn
    exact ⟨height σ J g₀, 0, fun g hg γ _ => by simpa using hg₀ hg⟩
  · have hcont : Continuous fun g => ‖φ g‖ * (height σ J g : ℝ) ^ N :=
      hφ.cont.norm.mul ((NNReal.continuous_coe.comp hh).pow N)
    obtain ⟨g₀, -, hg₀⟩ := hΩ.exists_isMaxOn ⟨1, h1⟩ hcont.continuousOn
    exact ⟨_, fun g hg => hg₀ hg⟩

/- English proof (translation)
Use `⟨?_, isCompact_singleton, fun g => ⟨1, one_mem _, 1, rfl, Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hr`. Use `congrFun (congrFun hW.xy ⟨0, Nat.pos_of_ne_zero hr⟩) ⟨0, Nat.pos_of_ne_zero hr⟩` as an intermediate fact. Simplify using `[Matrix.mul_apply] at this`.
-/
theorem rank_zero {J : Matrix (Fin 0) (Fin 0) E} {X Y : Matrix (Fin 0) (Fin r) E} (hW : IsWittFrame σ J X Y) :
    r = 0 ∧ IsCompact ({1} : Set (GAd σ J)) ∧ ∀ g, ∃ γ ∈ ratPts σ J, ∃ s ∈ ({1} : Set (GAd σ J)), g = γ * s := by
  refine ⟨?_, isCompact_singleton, fun g => ⟨1, one_mem _, 1, rfl, Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩⟩
  by_contra hr
  have := congrFun (congrFun hW.xy ⟨0, Nat.pos_of_ne_zero hr⟩) ⟨0, Nat.pos_of_ne_zero hr⟩
  simp [Matrix.mul_apply] at this

/- English proof (translation)
Take `⟨h1, h2, -⟩` from `ha.2 w τ`. Establish `a0` using `congrFun (congrFun h1 0) 0`. Establish `a1` using `congrFun (congrFun h1 1) 0`. Establish `b0` using `congrFun (congrFun h2 0) 0`. Establish `b1` using `congrFun (congrFun h2 1) 0`.

Simplify using `[Matrix.mul_apply, Fin.sum_univ_two] at a0 a1 b0 b1`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [a0, a1, b0, b1]`.
-/
theorem torus_plane {t : Fin 1 → ℝ} {a : GAd σ (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E)}
    (ha : IsTorusElt σ _ (!![1; 0] : Matrix (Fin 2) (Fin 1) E) !![0; 1] t a) (w : InfinitePlace F) (τ : EmbOver E w) :
    archMat σ _ τ (projArch σ _ w a) = !![(t 0 : ℂ), 0; 0, (t 0 : ℂ)⁻¹] := by
  obtain ⟨h1, h2, -⟩ := ha.2 w τ
  have a0 := congrFun (congrFun h1 0) 0
  have a1 := congrFun (congrFun h1 1) 0
  have b0 := congrFun (congrFun h2 0) 0
  have b1 := congrFun (congrFun h2 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at a0 a1 b0 b1
  ext i j; fin_cases i <;> fin_cases j <;> simp [a0, a1, b0, b1]

/- English proof (translation)
Simplify using `[modulus]`.
-/
example (t : Fin 1 → ℝ) : modulus ℚ 3 t = t 0 ^ 4 := by
  simp [modulus]
/- English proof (translation)
Simplify using `[modulus, Fin.prod_univ_two]`.
-/
example (t : Fin 2 → ℝ) : modulus ℚ 4 t = t 0 ^ 6 * t 1 ^ 2 := by
  simp [modulus, Fin.prod_univ_two]

end GlobalTheory.SiegelSet.Model

end
