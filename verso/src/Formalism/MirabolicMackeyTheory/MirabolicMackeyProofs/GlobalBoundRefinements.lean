import Formalism.MirabolicMackeyTheory.LocalConditionsWeighted
import Formalism.MirabolicMackeyTheory.MirabolicIsMackey
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.LocalConditionsGlobalForm
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

/- English proof (translation)
Introduce `K _ _ _ Z _ _ _ _ _ w M Th1 Th hM h1 hT h1T hTM E r h W`. Establish `a` using `(idxCutLe K Z w ⊤ W M Th hM hT hTM le_top).1`. Establish `b` using `(idxCutLe K Z w ⊤ W Th Th1 hT h1 h1T le_top).1`. Establish `c` using `(idxCutLe K Z w ⊤ W Th1 Th1 h1 h1 le_rfl le_top).1`. Establish `d : cut W Th1 ≤ cut W Th` using `inf_le_inf_right _ h1T`.

Establish `e` using `idxMono K Z w W (cut W M) (cut W Th1) (cut W Th) a c b d`. Establish `e' : (lix w (cut W M) (cut W Th) : ℝ) ≤ (lix w (cut W M) (cut W Th1) : ℝ)` using `by exact_mod_cast e`. Conclude with `le_trans e' (h W)`.
-/
theorem enlarge_initial_lattice : EnlargeInitialLattice := by
  intro K _ _ _ Z _ _ _ _ _ w M Th1 Th hM h1 hT h1T hTM E r h W
  have a := (idxCutLe K Z w ⊤ W M Th hM hT hTM le_top).1
  have b := (idxCutLe K Z w ⊤ W Th Th1 hT h1 h1T le_top).1
  have c := (idxCutLe K Z w ⊤ W Th1 Th1 h1 h1 le_rfl le_top).1
  have d : cut W Th1 ≤ cut W Th := inf_le_inf_right _ h1T
  have e := idxMono K Z w W (cut W M) (cut W Th1) (cut W Th) a c b d
  have e' : (lix w (cut W M) (cut W Th) : ℝ) ≤ (lix w (cut W M) (cut W Th1) : ℝ) := by exact_mod_cast e
  exact le_trans e' (h W)

/- English proof (translation)
Introduce `K _ _ _ Z _ _ _ _ _ w W e A Th0 ThJ X₃ hA h0 hJ hle ε h`. Establish `a` using `idxMono K Z w W A _ _ hA h0 hJ (Submodule.map_mono hle)`. Establish `a' : (lix w A (ThJ.map (e.restrictScalars (𝓞 K))) : ℝ) ≤ (lix w A (Th0.map (e.restrictScalars (𝓞 K))) : ℝ)` using `by exact_mod_cast a`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem twist_chain : TwChain := by
  intro K _ _ _ Z _ _ _ _ _ w W e A Th0 ThJ X₃ hA h0 hJ hle ε h
  have a := idxMono K Z w W A _ _ hA h0 hJ (Submodule.map_mono hle)
  have a' : (lix w A (ThJ.map (e.restrictScalars (𝓞 K))) : ℝ) ≤
      (lix w A (Th0.map (e.restrictScalars (𝓞 K))) : ℝ) := by exact_mod_cast a
  linarith

/- English proof (translation)
Introduce `K _ _ _ Z _ _ _ _ _ w P _ _ ρ U ψ hMk V₀ e he hr M Th ThK Th0 ThJ X₃ X₄ hM hTh hThK hle hFG hEig hMs hTs σ hσ hsc hdata a E r ha hE hT0 h0 hJ h0J h3 h4 h34 ε hTW d φ hinj hrng Mj Tj hMj hTj`. Conclude with `onLocal K Z w P ρ U ψ hMk V₀ e he hr M Th ThK Th0 X₃ X₄ hM hTh hThK hle hFG hEig hMs hTs σ hσ hsc hdata a E r ha hE hT0 h0 h3 h4 h34 ε (twist_chain K Z w _ e _ Th0 ThJ X₃ (idxCutLe K Z w ⊤ _ M Th hM hTh hle le_top).1 h0 hJ h0J ε hTW) d φ hinj hrng Mj Tj hMj hTj`.
-/
theorem local_conditions_family : OnLocalJ := by
  intro K _ _ _ Z _ _ _ _ _ w P _ _ ρ U ψ hMk V₀ e he hr M Th ThK Th0 ThJ X₃ X₄ hM hTh hThK hle hFG hEig hMs hTs
    σ hσ hsc hdata a E r ha hE hT0 h0 hJ h0J h3 h4 h34 ε hTW d φ hinj hrng Mj Tj hMj hTj
  exact onLocal K Z w P ρ U ψ hMk V₀ e he hr M Th ThK Th0 X₃ X₄ hM hTh hThK hle hFG hEig hMs hTs σ hσ hsc hdata
    a E r ha hE hT0 h0 h3 h4 h34 ε
    (twist_chain K Z w _ e _ Th0 ThJ X₃ (idxCutLe K Z w ⊤ _ M Th hM hTh hle le_top).1 h0 hJ h0J ε hTW)
    d φ hinj hrng Mj Tj hMj hTj

/- English proof (translation)
Conclude with `fun K _ _ _ Z _ _ _ _ _ w P _ _ ρ U ψ hMk V₀ e he hr M Th ThK Th0 X₃ X₄ hM hTh hThK hle hFG hEig hMs hTs σ hσ hsc hdata a E r ha hE hT0 h0 h3 h4 h34 ε hTW => h K Z w P ρ U ψ hMk V₀ e he hr M Th ThK Th0 Th0 X₃ X₄ hM hTh hThK hle hFG hEig hMs hTs σ hσ hsc hdata a E r ha hE hT0 h0 h …`.
-/
theorem onLocal_of_onLocalJ (h : OnLocalJ) : OnLocal := by
  exact fun K _ _ _ Z _ _ _ _ _ w P _ _ ρ U ψ hMk V₀ e he hr M Th ThK Th0 X₃ X₄ hM hTh hThK hle hFG hEig hMs hTs
    σ hσ hsc hdata a E r ha hE hT0 h0 h3 h4 h34 ε hTW =>
    h K Z w P ρ U ψ hMk V₀ e he hr M Th ThK Th0 Th0 X₃ X₄ hM hTh hThK hle hFG hEig hMs hTs
      σ hσ hsc hdata a E r ha hE hT0 h0 h0 le_rfl h3 h4 h34 ε hTW

/- English proof (translation)
Introduce `R X Y _ _ _ _ _ θ eX pr e hc hk Mt`. Establish `key : ∀ m, θ (pr (eX m)) = e (θ m)`. Introduce `m`. Establish `h1` using `hk (eX m) (LinearMap.mem_range_self eX m)`. Rewrite `h1` using `[LinearMap.mem_ker, map_sub, sub_eq_zero]`.

Rewrite using `[← h1, ← LinearMap.comp_apply θ eX, hc, LinearMap.comp_apply]`. Use extensionality with `y`. Simplify using `only [Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, ⟨x, ⟨m, hm, rfl⟩, rfl⟩, rfl⟩`.

Conclude with `⟨θ m, ⟨m, hm, rfl⟩, (key m).symm⟩`. Introduce and unpack `⟨z, ⟨m, hm, rfl⟩, rfl⟩`. Conclude with `⟨pr (eX m), ⟨eX m, ⟨m, hm, rfl⟩, rfl⟩, key m⟩`.
-/
theorem theta_identity : ThetaIdentity := by
  intro R X Y _ _ _ _ _ θ eX pr e hc hk Mt
  have key : ∀ m, θ (pr (eX m)) = e (θ m) := by
    intro m
    have h1 := hk (eX m) (LinearMap.mem_range_self eX m)
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h1
    rw [← h1, ← LinearMap.comp_apply θ eX, hc, LinearMap.comp_apply]
  ext y
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨z, ⟨x, ⟨m, hm, rfl⟩, rfl⟩, rfl⟩
    exact ⟨θ m, ⟨m, hm, rfl⟩, (key m).symm⟩
  · rintro ⟨z, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨pr (eX m), ⟨eX m, ⟨m, hm, rfl⟩, rfl⟩, key m⟩

/- English proof (translation)
Introduce `R X Y A _ _ _ _ _ _ θ eX p e h hc hsym hp hker hrange`. Establish `hkerθ : ∀ k ∈ LinearMap.ker θ, eX k ∈ LinearMap.ker θ`. Introduce `k hk`. Rewrite `hk`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[← LinearMap.comp_apply θ eX, hc, LinearMap.comp_apply, hk, map_zero]`.

Establish `hpp : ∀ x, p (p x) = p x` using `fun x => by rw [← LinearMap.comp_apply p p, hp]`. Establish `hrp : ∀ x, p x ∈ LinearMap.range p` using `fun x => LinearMap.mem_range_self p x`. Establish `hsub : ∀ x, x - p x ∈ LinearMap.ker θ` using `fun x => by`. Rewrite using `[← hker, LinearMap.mem_ker, map_sub, hpp, sub_self]`. Establish `hEr : ∀ x ∈ LinearMap.range p, eX x ∈ LinearMap.range p`.

Introduce `x hx`. Rewrite `hx`, the goal using `[hrange]`. Introduce `k hk`. Rewrite using `[← hsym]`. Conclude with `hx _ (hkerθ k hk)`.

Establish `hfix : ∀ y ∈ LinearMap.range p, p y = y`. Introduce and unpack `y ⟨z, rfl⟩`. Conclude with `hpp z`. Establish `hcomm : ∀ x, p (eX x) = eX (p x)`. Introduce `x`.

Establish `h1 : eX x = eX (p x) + eX (x - p x)`. Rewrite using `[← map_add]`. Use `congr 1`. Normalize the expressions using the abelian group laws. Establish `h2 : p (eX (x - p x)) = 0`.

Rewrite using `[← LinearMap.mem_ker, hker]`. Conclude with `hkerθ _ (hsub x)`. Rewrite using `[h1, map_add, h2, add_zero, hfix _ (hEr _ (hrp x))]`. Use `⟨LinearMap.ext hcomm, fun x hx => ⟨?_, hsub x, fun k hk => (hrange (p x)).1 (hrp x) k hk⟩, fun Mt => ?_⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `hx`.

Rewrite using `[hcomm]`. Conclude with `LinearMap.mem_range_self eX (p y)`. Establish `key : ∀ m, θ (eX (p m)) = e (θ m)`. Introduce `m`. Establish `hm : θ (p m) = θ m`.

Use `hsub m` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, map_sub, sub_eq_zero]`. Conclude with `this.symm`. Rewrite using `[← LinearMap.comp_apply θ eX, hc, LinearMap.comp_apply, hm]`. Use extensionality with `y`.

Simplify using `only [Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, ⟨x, ⟨m, hm, rfl⟩, rfl⟩, rfl⟩`. Conclude with `⟨θ m, ⟨m, hm, rfl⟩, (key m).symm⟩`. Introduce and unpack `⟨z, ⟨m, hm, rfl⟩, rfl⟩`.

Conclude with `⟨eX (p m), ⟨p m, ⟨m, hm, rfl⟩, rfl⟩, key m⟩`.
-/
theorem theta_identity_orthogonal : ThetaIdentityOrth := by
  intro R X Y A _ _ _ _ _ _ θ eX p e h hc hsym hp hker hrange
  have hkerθ : ∀ k ∈ LinearMap.ker θ, eX k ∈ LinearMap.ker θ := by
    intro k hk
    rw [LinearMap.mem_ker] at hk ⊢
    rw [← LinearMap.comp_apply θ eX, hc, LinearMap.comp_apply, hk, map_zero]
  have hpp : ∀ x, p (p x) = p x := fun x => by rw [← LinearMap.comp_apply p p, hp]
  have hrp : ∀ x, p x ∈ LinearMap.range p := fun x => LinearMap.mem_range_self p x
  have hsub : ∀ x, x - p x ∈ LinearMap.ker θ := fun x => by
    rw [← hker, LinearMap.mem_ker, map_sub, hpp, sub_self]
  have hEr : ∀ x ∈ LinearMap.range p, eX x ∈ LinearMap.range p := by
    intro x hx
    rw [hrange] at hx ⊢
    intro k hk
    rw [← hsym]
    exact hx _ (hkerθ k hk)
  have hfix : ∀ y ∈ LinearMap.range p, p y = y := by
    rintro y ⟨z, rfl⟩
    exact hpp z
  have hcomm : ∀ x, p (eX x) = eX (p x) := by
    intro x
    have h1 : eX x = eX (p x) + eX (x - p x) := by
      rw [← map_add]
      congr 1
      abel
    have h2 : p (eX (x - p x)) = 0 := by
      rw [← LinearMap.mem_ker, hker]
      exact hkerθ _ (hsub x)
    rw [h1, map_add, h2, add_zero, hfix _ (hEr _ (hrp x))]
  refine ⟨LinearMap.ext hcomm, fun x hx => ⟨?_, hsub x, fun k hk => (hrange (p x)).1 (hrp x) k hk⟩, fun Mt => ?_⟩
  · obtain ⟨y, rfl⟩ := hx
    rw [hcomm]
    exact LinearMap.mem_range_self eX (p y)
  · have key : ∀ m, θ (eX (p m)) = e (θ m) := by
      intro m
      have hm : θ (p m) = θ m := by
        have := hsub m
        rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
        exact this.symm
      rw [← LinearMap.comp_apply θ eX, hc, LinearMap.comp_apply, hm]
    ext y
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨z, ⟨x, ⟨m, hm, rfl⟩, rfl⟩, rfl⟩
      exact ⟨θ m, ⟨m, hm, rfl⟩, (key m).symm⟩
    · rintro ⟨z, ⟨m, hm, rfl⟩, rfl⟩
      exact ⟨eX (p m), ⟨p m, ⟨m, hm, rfl⟩, rfl⟩, key m⟩

/- English proof (translation)
Introduce `R N Y Γ _ _ _ _ _ _ _ ρ lam θ hθ P`. Use `⟨fun γ' => ?_, ?_, fun N0 hρ hl hP => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum, Finset.smul_sum]`. Simplify using `only [map_smul]`. Apply `Fintype.sum_equiv (Equiv.mulLeft γ')` to reduce the goal to its premises.

Introduce `γ`. Establish `hl1 : lam γ'⁻¹ * lam γ' = 1` using `by first`. Consider the case `rw [← map_mul, inv_mul_cancel, map_one]`. Consider the case `rw [← map_mul, mul_left_inv, map_one]`. Consider the case `simp [← map_mul]`.

Simplify using `only [Equiv.coe_mulLeft, map_mul, smul_smul]`. Rewrite using `[← mul_assoc, hl1, one_mul]`. Use `first`. Consider the case `rfl`. Consider the case `simp [Module.End.mul_apply]`.

Rewrite using `[map_sum]`. Simplify using `only [map_smul]`. Rewrite using `[Finset.sum_congr rfl (fun γ _ => (hθ γ P).symm), Finset.sum_const, Finset.card_univ]`. Use `first`. Consider the case `rw [Nat.cast_smul_eq_nsmul]`.

Consider the case `simp`. Conclude with `AddSubgroup.sum_mem N0 (fun γ _ => hl γ _ (hρ γ P hP))`.
-/
theorem trace_class : TraceClass := by
  intro R N Y Γ _ _ _ _ _ _ _ ρ lam θ hθ P
  refine ⟨fun γ' => ?_, ?_, fun N0 hρ hl hP => ?_⟩
  · rw [map_sum, Finset.smul_sum]
    simp only [map_smul]
    apply Fintype.sum_equiv (Equiv.mulLeft γ')
    intro γ
    have hl1 : lam γ'⁻¹ * lam γ' = 1 := by
      first
        | rw [← map_mul, inv_mul_cancel, map_one]
        | rw [← map_mul, mul_left_inv, map_one]
        | simp [← map_mul]
    simp only [Equiv.coe_mulLeft, map_mul, smul_smul]
    rw [← mul_assoc, hl1, one_mul]
    first
      | rfl
      | simp [Module.End.mul_apply]
  · rw [map_sum]
    simp only [map_smul]
    rw [Finset.sum_congr rfl (fun γ _ => (hθ γ P).symm), Finset.sum_const, Finset.card_univ]
    first
      | rw [Nat.cast_smul_eq_nsmul]
      | simp
  · exact AddSubgroup.sum_mem N0 (fun γ _ => hl γ _ (hρ γ P hP))

/- English proof (translation)
Introduce `ρ vS T ν β hρ`. Establish `hρ' : (ρ : ℝ) ≠ 0` using `by exact_mod_cast hρ.ne'`. Establish `hq : (ρ : ℝ) * ((vS : ℝ) / (ρ : ℝ)) = vS` using `by first`. Consider the case `field_simp`. Consider the case `exact mul_div_cancel₀ _ hρ'`.

Establish `e : (ρ : ℝ) * ((T : ℝ) * (ν - (vS : ℝ) / (ρ : ℝ) + β)) = (ρ : ℝ) * ((T : ℝ) * (ν + β)) - (((T : ℤ) * vS : ℤ) : ℝ)`. Use `push_cast`. Take the linear combination `(-(T : ℝ)) * hq`. Rewrite using `[e]`. Use `first`.

Consider the case `rw [Int.ceil_sub_intCast]`. Consider the case `rw [Int.ceil_sub_int]`. Consider the case `simp`.
-/
theorem ceiling_shift : CeilShift := by
  intro ρ vS T ν β hρ
  have hρ' : (ρ : ℝ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hq : (ρ : ℝ) * ((vS : ℝ) / (ρ : ℝ)) = vS := by
    first
      | field_simp
      | exact mul_div_cancel₀ _ hρ'
  have e : (ρ : ℝ) * ((T : ℝ) * (ν - (vS : ℝ) / (ρ : ℝ) + β)) =
      (ρ : ℝ) * ((T : ℝ) * (ν + β)) - (((T : ℤ) * vS : ℤ) : ℝ) := by
    push_cast
    linear_combination (-(T : ℝ)) * hq
  rw [e]
  first
    | rw [Int.ceil_sub_intCast]
    | rw [Int.ceil_sub_int]
    | simp

/- English proof (translation)
Introduce `ρ T DL Dk g hρ hDL hTD hg`. Establish `hDk : 0 ≤ Dk` using `le_trans (mul_nonneg (Nat.cast_nonneg T) hDL) hTD`. Establish `hg1 : 0 < g - 1` using `by linarith`. Establish `hx : (T : ℝ) * (DL / (g - 1) + 1) ≤ (T : ℝ) + 1`. Establish `e1 : (T : ℝ) * (DL / (g - 1) + 1) = (T : ℝ) * DL / (g - 1) + T` using `by ring`.

Establish `e2 : (T : ℝ) * DL / (g - 1) ≤ 1` using `by first`. Consider the case `(rw [div_le_one hg1]; linarith)`. Consider the case `(rw [div_le_one₀ hg1]; linarith)`. Consider the case `(rw [div_le_iff₀ hg1]; linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[Int.ceil_le]`. Use `push_cast`. Conclude with `mul_le_mul_of_nonneg_left hx (by exact_mod_cast hρ)`.
-/
theorem level_ceiling : LevelCeil := by
  intro ρ T DL Dk g hρ hDL hTD hg
  have hDk : 0 ≤ Dk := le_trans (mul_nonneg (Nat.cast_nonneg T) hDL) hTD
  have hg1 : 0 < g - 1 := by linarith
  have hx : (T : ℝ) * (DL / (g - 1) + 1) ≤ (T : ℝ) + 1 := by
    have e1 : (T : ℝ) * (DL / (g - 1) + 1) = (T : ℝ) * DL / (g - 1) + T := by ring
    have e2 : (T : ℝ) * DL / (g - 1) ≤ 1 := by
      first
        | (rw [div_le_one hg1]; linarith)
        | (rw [div_le_one₀ hg1]; linarith)
        | (rw [div_le_iff₀ hg1]; linarith)
    linarith
  rw [Int.ceil_le]
  push_cast
  exact mul_le_mul_of_nonneg_left hx (by exact_mod_cast hρ)

/- English proof (translation)
Unfold `vw`. Rewrite using `[← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]`.
-/
theorem valuation_pow_alt (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K))
    (a : K) (ha : a ≠ 0) (n : ℕ) : vw w (a ^ n) = (n : ℤ) * vw w a := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]

/- English proof (translation)
Unfold `vw`. Rewrite using `[← FractionalIdeal.spanSingleton_mul_spanSingleton]`. Apply the tactic sequence `apply FractionalIdeal.count_mul <;> rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]`.
-/
private theorem vw_mul_lemma (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K))
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) : vw w (a * b) = vw w a + vw w b := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
  apply FractionalIdeal.count_mul <;> rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]

/- English proof (translation)
Introduce `K _ _ _ w nnL nnF q Z1 Z2 T c h1 h2 h3 h4 h5 z1 z2`. Rewrite using `[vw_mul_lemma K w _ _ (pow_ne_zero _ (mul_ne_zero h1 h4)) (mul_ne_zero (mul_ne_zero h2 (pow_ne_zero _ h3)) h5), valuation_pow_alt K w _ (mul_ne_zero h1 h4), vw_mul_lemma K w _ _ h1 h4, vw_mul_lemma K w _ _ (mul_ne_zero h2 (pow_ne_zero _ h3)) h5, vw_mul_lemma K w _ _ h2 (pow_ne_ze …`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem scalar_level : ScalarLevel := by
  intro K _ _ _ w nnL nnF q Z1 Z2 T c h1 h2 h3 h4 h5 z1 z2
  rw [vw_mul_lemma K w _ _ (pow_ne_zero _ (mul_ne_zero h1 h4)) (mul_ne_zero (mul_ne_zero h2 (pow_ne_zero _ h3)) h5),
    valuation_pow_alt K w _ (mul_ne_zero h1 h4), vw_mul_lemma K w _ _ h1 h4,
    vw_mul_lemma K w _ _ (mul_ne_zero h2 (pow_ne_zero _ h3)) h5, vw_mul_lemma K w _ _ h2 (pow_ne_zero _ h3),
    valuation_pow_alt K w _ h3, vw_mul_lemma K w _ _ (pow_ne_zero _ h1) h2, valuation_pow_alt K w _ h1, z1, z2]
  ring

/- English proof (translation)
Unfold `ramw vw`. Establish `e : ((plc w : ℕ) : K) = algebraMap (𝓞 K) K ((plc w : ℕ) : 𝓞 K)` using `by simp`. Rewrite using `[e, ← FractionalIdeal.coeIdeal_span_singleton]`. Apply `FractionalIdeal.count_coe_nonneg` to reduce the goal to its premises.
-/
private theorem ramw_nonneg_lemma_2 (K : Type) [Field K] [NumberField K] [StarRing K]
    (w : HeightOneSpectrum (𝓞 K)) : 0 ≤ ramw w := by
  unfold ramw vw
  have e : ((plc w : ℕ) : K) = algebraMap (𝓞 K) K ((plc w : ℕ) : 𝓞 K) := by simp
  rw [e, ← FractionalIdeal.coeIdeal_span_singleton]
  apply FractionalIdeal.count_coe_nonneg

/- English proof (translation)
Introduce `K _ _ _ w nnL nnF q Z1 Z2 T c DL Dk g h1 h2 h3 h4 h5 z1 z2 hq hT h0 hTD hg`. Rewrite using `[scalar_level K w nnL nnF q Z1 Z2 T c h1 h2 h3 h4 h5 z1 z2]`. Establish `hR` using `ramw_nonneg_lemma_2 K w`. Establish `hc` using `level_ceiling (ramw w) T DL Dk g hR h0 hTD hg`. Establish `hA : 0 ≤ ramw w * ((T : ℤ) - 1)` using `mul_nonneg hR (by omega)`.

Establish `hB : 0 ≤ (c : ℤ) * vw w q` using `mul_nonneg (by omega) hq`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem level_at_place_alt : LevelPlace := by
  intro K _ _ _ w nnL nnF q Z1 Z2 T c DL Dk g h1 h2 h3 h4 h5 z1 z2 hq hT h0 hTD hg
  rw [scalar_level K w nnL nnF q Z1 Z2 T c h1 h2 h3 h4 h5 z1 z2]
  have hR := ramw_nonneg_lemma_2 K w
  have hc := level_ceiling (ramw w) T DL Dk g hR h0 hTD hg
  have hA : 0 ≤ ramw w * ((T : ℤ) - 1) := mul_nonneg hR (by omega)
  have hB : 0 ≤ (c : ℤ) * vw w q := mul_nonneg (by omega) hq
  linarith

/- English proof (translation)
Introduce `RR PP DF d' n1 nW g' qmin hRR hDF hd hn1 hn hq hqg hPP`. Establish `hg : 0 < g'` using `lt_of_lt_of_le hq hqg`. Establish `hnW : 0 ≤ nW` using `le_trans hn1 hn`. Establish `hd3 : 0 ≤ d' ^ 3` using `pow_nonneg hd 3`. Establish `hd4 : 0 ≤ d' ^ 4` using `pow_nonneg hd 4`.

Establish `hPP0 : 0 ≤ PP` using `by nlinarith [mul_nonneg hd4 hnW]`. Establish `hDF2 : 1 ≤ DF ^ 2` using `by nlinarith`. Establish `k1 : 0 ≤ RR * DF ^ 2 * (PP - (d' ^ 4 * nW + 2 * d' ^ 3))` using `mul_nonneg (mul_nonneg hRR (sq_nonneg DF)) (by linarith)`. Establish `k2 : 0 ≤ RR * d' ^ 4 * (nW * DF ^ 2 - n1 / 4)` using `mul_nonneg (mul_nonneg hRR hd4) (by nlinarith)`. Establish `hC : n1 * d' * (RR * d' ^ 3) / 4 + 2 * (RR * d' ^ 3) * DF ^ 2 ≤ RR * PP * DF ^ 2`.

Use polynomial arithmetic with `[k1, k2]`. Establish `hN : 0 ≤ RR * PP * DF ^ 2` using `mul_nonneg (mul_nonneg hRR hPP0) (sq_nonneg DF)`. Establish `hinv : g'⁻¹ ≤ qmin⁻¹` using `by first`. Consider the case `exact inv_anti₀ hq hqg`. Consider the case `exact inv_le_inv_of_le hq hqg`.

Consider the case `exact (inv_le_inv hg hq).2 hqg`. Combine the equalities or inequalities in the displayed calculation. Consider the case `ring`. Consider the case `(field_simp; ring)`. Use `_ ≤ RR * PP * DF ^ 2 * g'⁻¹ := mul_le_mul_of_nonneg_right hC (inv_nonneg.mpr hg.le)`.

Use `_ ≤ RR * PP * DF ^ 2 * qmin⁻¹ := mul_le_mul_of_nonneg_left hinv hN`. Use `_ = RR * PP * DF ^ 2 / qmin := by rw [div_eq_mul_inv]`.
-/
theorem constant_b_bound : ConstB := by
  intro RR PP DF d' n1 nW g' qmin hRR hDF hd hn1 hn hq hqg hPP
  have hg : 0 < g' := lt_of_lt_of_le hq hqg
  have hnW : 0 ≤ nW := le_trans hn1 hn
  have hd3 : 0 ≤ d' ^ 3 := pow_nonneg hd 3
  have hd4 : 0 ≤ d' ^ 4 := pow_nonneg hd 4
  have hPP0 : 0 ≤ PP := by nlinarith [mul_nonneg hd4 hnW]
  have hDF2 : 1 ≤ DF ^ 2 := by nlinarith
  have k1 : 0 ≤ RR * DF ^ 2 * (PP - (d' ^ 4 * nW + 2 * d' ^ 3)) :=
    mul_nonneg (mul_nonneg hRR (sq_nonneg DF)) (by linarith)
  have k2 : 0 ≤ RR * d' ^ 4 * (nW * DF ^ 2 - n1 / 4) :=
    mul_nonneg (mul_nonneg hRR hd4) (by nlinarith)
  have hC : n1 * d' * (RR * d' ^ 3) / 4 + 2 * (RR * d' ^ 3) * DF ^ 2 ≤ RR * PP * DF ^ 2 := by
    nlinarith [k1, k2]
  have hN : 0 ≤ RR * PP * DF ^ 2 := mul_nonneg (mul_nonneg hRR hPP0) (sq_nonneg DF)
  have hinv : g'⁻¹ ≤ qmin⁻¹ := by
    first
      | exact inv_anti₀ hq hqg
      | exact inv_le_inv_of_le hq hqg
      | exact (inv_le_inv hg hq).2 hqg
  calc n1 * d' * (RR * d' ^ 3) / (4 * g') + 2 * (RR * d' ^ 3) * DF ^ 2 / g'
      = (n1 * d' * (RR * d' ^ 3) / 4 + 2 * (RR * d' ^ 3) * DF ^ 2) * g'⁻¹ := by
        first
          | ring
          | (field_simp; ring)
    _ ≤ RR * PP * DF ^ 2 * g'⁻¹ := mul_le_mul_of_nonneg_right hC (inv_nonneg.mpr hg.le)
    _ ≤ RR * PP * DF ^ 2 * qmin⁻¹ := mul_le_mul_of_nonneg_left hinv hN
    _ = RR * PP * DF ^ 2 / qmin := by rw [div_eq_mul_inv]

/- English proof (translation)
Introduce `K _ _ _ J _ ε0 w h`. Establish `hp : 0 ≤ 1 / (plc w : ℝ) ^ 2` using `by positivity`. Establish `e2 : (2 : ℝ) / (plc w : ℝ) ^ 2 = 1 / (plc w : ℝ) ^ 2 + 1 / (plc w : ℝ) ^ 2` using `by ring`. Rewrite using `[e2]`. Distinguish the cases in `hc : conjPl w = w`.

Simplify using `only [if_pos hc, add_zero] at h`. Rewrite using `[hc, Finset.sum_add_distrib]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [if_neg hc] at h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem twist_set_double : TwistSetDouble := by
  intro K _ _ _ J _ ε0 w h
  have hp : 0 ≤ 1 / (plc w : ℝ) ^ 2 := by positivity
  have e2 : (2 : ℝ) / (plc w : ℝ) ^ 2 = 1 / (plc w : ℝ) ^ 2 + 1 / (plc w : ℝ) ^ 2 := by ring
  rw [e2]
  by_cases hc : conjPl w = w
  · simp only [if_pos hc, add_zero] at h
    rw [hc, Finset.sum_add_distrib]
    linarith
  · simp only [if_neg hc] at h
    linarith

/- English proof (translation)
Introduce `K _ _ _ D hD Tup μ J _ d hd M T θ S e0 r0 ε0 F0 errl Jx vU0 gq dK EA Rb EJ δq E3 hδ h1 h2 hsh hv hdep htw0 hEA hRb hEJ hE3`. Establish `hR : RamBasic` using `ramBasic`. Establish `hDr : (0 : ℝ) < D` using `by exact_mod_cast hD`. Establish `htw : ∀ w ∈ S, ∑ j, (ε0 w j + ε0 (conjPl w) j) ≤ 2 / (plc w : ℝ) ^ 2` using `fun w hw => twist_set_double K J ε0 w (by convert htw0 w hw)`. Take `⟨c1, c2, c3⟩` from `local_conditions_global_form K D hD Tup μ J d hd M T θ S e0 r0 ε0 F0 errl Jx vU0 gq dK EA Rb EJ δq E3 hδ h1 h2 hsh hv hdep htw hEA hRb hEJ hE3`.

Use `⟨?_, c1, c2, c3⟩` and prove the remaining obligations. Introduce `w hw`. Take `⟨hp, hr1, hpc, hrc, hell⟩` from `hR K w`. Establish `hρ : (1 : ℝ) ≤ (ramw w : ℝ)` using `by exact_mod_cast hr1`. Take `⟨hv0, hvc, hvg⟩` from `hv w hw`.

Establish `key : ∀ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) + (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ)) ≤ (2 * ((ramw w : ℝ) * F0 w j) + (ramw w : ℝ) * (errl w j + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ)))) * D + (ramw w : ℝ) * (ε0 w j + ε0 (conjPl w) j)`. Introduce `j`. Establish `a1` using `h1 w hw j`. Establish `a2` using `h2 w hw j`. Rewrite `a2` using `[hrc, hvc]`.

Establish `hdj : (d j : ℝ) = D` using `by exact_mod_cast hd j`. Rewrite `a1`, `a2` using `[hdj]`. Establish `a3` using `hdep w hw j`. Establish `a4` using `hsh j`. Establish `e1 : (r0 w j + dK j * vU0 w) / δq = r0 w j / δq + dK j / δq * vU0 w`.

Clear the denominators using the available nonvanishing facts. Establish `e2 : (r0 (conjPl w) j + dK j * vU0 w) / δq = r0 (conjPl w) j / δq + dK j / δq * vU0 w`. Clear the denominators using the available nonvanishing facts. Establish `e3 : (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ)) * D = r0 w j / δq + r0 (conjPl w) j / δq`. Clear the denominators using the available nonvanishing facts.

Rewrite `a1` using `[e1]`. Rewrite `a2` using `[e2]`. Establish `b1 : dK j / δq * vU0 w ≤ 3 * (D : ℝ) * vU0 w` using `mul_le_mul_of_nonneg_right a4 hv0`. Establish `b2 : (e0 w j + e0 (conjPl w) j + 8 * vU0 w) * (D : ℝ) ≤ (2 * F0 w j + errl w j) * D` using `mul_le_mul_of_nonneg_right (by linarith) hDr.le`. Establish `b3 : ((e0 w j + vU0 w) * (D : ℝ) + (r0 w j / δq + dK j / δq * vU0 w) + ε0 w j) + ((e0 (conjPl w) j + vU0 w) * (D : ℝ) + (r0 (conjPl w) j / δq + dK j / δq * vU0 w) + ε0 (conjPl w) j) ≤ (2 * F0 w j + errl w j) * D + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ)) * D + (ε0 w j + ε0 (co …`.

Rewrite using `[e3]`. Use the polynomial consequences of the given equalities and inequalities. Establish `b4` using `mul_le_mul_of_nonneg_left b3 (by linarith : (0 : ℝ) ≤ (ramw w : ℝ))`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]`. Use `_ ≤ _ := by`. Rewrite using `[hell]`. Establish `c1` using `mul_le_mul_of_nonneg_left (htw w hw) (by linarith : (0 : ℝ) ≤ (ramw w : ℝ))`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem local_conditions_global_set : OnExportSet := by
  classical
  intro K _ _ _ D hD Tup μ J _ d hd M T θ S e0 r0 ε0 F0 errl Jx vU0 gq dK EA Rb EJ δq E3 hδ h1 h2 hsh hv
    hdep htw0 hEA hRb hEJ hE3
  have hR : RamBasic := ramBasic
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have htw : ∀ w ∈ S, ∑ j, (ε0 w j + ε0 (conjPl w) j) ≤ 2 / (plc w : ℝ) ^ 2 :=
    fun w hw => twist_set_double K J ε0 w (by convert htw0 w hw)
  obtain ⟨c1, c2, c3⟩ := local_conditions_global_form K D hD Tup μ J d hd M T θ S e0 r0 ε0 F0 errl Jx vU0 gq dK EA Rb EJ δq E3
    hδ h1 h2 hsh hv hdep htw hEA hRb hEJ hE3
  refine ⟨?_, c1, c2, c3⟩
  intro w hw
  obtain ⟨hp, hr1, hpc, hrc, hell⟩ := hR K w
  have hρ : (1 : ℝ) ≤ (ramw w : ℝ) := by exact_mod_cast hr1
  obtain ⟨hv0, hvc, hvg⟩ := hv w hw
  have key : ∀ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
        (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ)) ≤
      (2 * ((ramw w : ℝ) * F0 w j) +
          (ramw w : ℝ) * (errl w j + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ)))) * D +
        (ramw w : ℝ) * (ε0 w j + ε0 (conjPl w) j) := by
    intro j
    have a1 := h1 w hw j
    have a2 := h2 w hw j
    rw [hrc, hvc] at a2
    have hdj : (d j : ℝ) = D := by exact_mod_cast hd j
    rw [hdj] at a1 a2
    have a3 := hdep w hw j
    have a4 := hsh j
    have e1 : (r0 w j + dK j * vU0 w) / δq = r0 w j / δq + dK j / δq * vU0 w := by
      field_simp
    have e2 : (r0 (conjPl w) j + dK j * vU0 w) / δq = r0 (conjPl w) j / δq + dK j / δq * vU0 w := by
      field_simp
    have e3 : (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ)) * D = r0 w j / δq + r0 (conjPl w) j / δq := by
      field_simp
    rw [e1] at a1
    rw [e2] at a2
    have b1 : dK j / δq * vU0 w ≤ 3 * (D : ℝ) * vU0 w := mul_le_mul_of_nonneg_right a4 hv0
    have b2 : (e0 w j + e0 (conjPl w) j + 8 * vU0 w) * (D : ℝ) ≤ (2 * F0 w j + errl w j) * D :=
      mul_le_mul_of_nonneg_right (by linarith) hDr.le
    have b3 : ((e0 w j + vU0 w) * (D : ℝ) + (r0 w j / δq + dK j / δq * vU0 w) + ε0 w j) +
        ((e0 (conjPl w) j + vU0 w) * (D : ℝ) + (r0 (conjPl w) j / δq + dK j / δq * vU0 w) +
          ε0 (conjPl w) j) ≤
        (2 * F0 w j + errl w j) * D + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ)) * D +
          (ε0 w j + ε0 (conjPl w) j) := by
      rw [e3]; nlinarith
    have b4 := mul_le_mul_of_nonneg_left b3 (by linarith : (0 : ℝ) ≤ (ramw w : ℝ))
    calc _ ≤ _ := add_le_add a1 a2
      _ = (ramw w : ℝ) * (((e0 w j + vU0 w) * (D : ℝ) + (r0 w j / δq + dK j / δq * vU0 w) + ε0 w j) +
        ((e0 (conjPl w) j + vU0 w) * (D : ℝ) + (r0 (conjPl w) j / δq + dK j / δq * vU0 w) +
          ε0 (conjPl w) j)) := by ring
      _ ≤ _ := b4
      _ = _ := by ring
  calc _ ≤ _ := Finset.sum_le_sum (fun j _ => key j)
    _ = (∑ j, (2 * ((ramw w : ℝ) * F0 w j) +
          (ramw w : ℝ) * (errl w j + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ))))) * D +
        (ramw w : ℝ) * ∑ j, (ε0 w j + ε0 (conjPl w) j) := by
          rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    _ ≤ _ := by
      rw [hell]
      have c1 := mul_le_mul_of_nonneg_left (htw w hw) (by linarith : (0 : ℝ) ≤ (ramw w : ℝ))
      linarith

/- English proof (translation)
Introduce `K _ _ _ Z _ _ _ _ _ w P _ _ ρ U ψ hMk V₀ e he hr M Th1 Th ThK Th0 ThJ X₃ hM hTh1 hTh hThK h1le hle hFG hEig hMs hTs σ hσ hsc hdata a E r ha hE hT0 h0 hJ h0J h3 X _ _ _ _ θ' eX pr Mt hc hk h4 h34 ε hTW d φ hinj hrng Mj Tj hMj hTj`. Establish `hT0'` using `enlarge_initial_lattice K Z w M Th1 Th hM hTh1 hTh h1le hle (E : ℝ) r hT0`. Establish `hc' : (θ'.restrictScalars (𝓞 K)) ∘ₗ (eX.restrictScalars (𝓞 K)) = (e.restrictScalars (𝓞 K)) ∘ₗ (θ'.restrictScalars (𝓞 K))` using `LinearMap.ext fun x => LinearMap.congr_fun hc x`. Establish `hk' : ∀ x ∈ LinearMap.range (eX.restrictScalars (𝓞 K)), x - (pr.restrictScalars (𝓞 K)) x ∈ LinearMap.ker (θ'.restrictScalars (𝓞 K))`. Introduce `x hx`.

Take `⟨y, rfl⟩` from `LinearMap.mem_range.1 hx`. Conclude with `LinearMap.mem_ker.2 (LinearMap.mem_ker.1 (hk _ (LinearMap.mem_range_self eX y)))`. Establish `hid` using `theta_identity (𝓞 K) X Z (θ'.restrictScalars (𝓞 K)) (eX.restrictScalars (𝓞 K)) (pr.restrictScalars (𝓞 K)) (e.restrictScalars (𝓞 K)) hc' hk' Mt`. Conclude with `local_conditions_family K Z w P ρ U ψ hMk V₀ e he hr M Th ThK Th0 ThJ X₃ ((Mt.map (θ'.restrictScalars (𝓞 K))).map (e.restrictScalars (𝓞 K))) hM hTh hThK hle hFG hEig hMs hTs σ hσ hsc hdata a E r ha hE hT0' h0 hJ h0J h3 h4 h34 ε hTW d φ hinj hrng Mj Tj hMj (hTj.trans hid)`.
-/
theorem local_conditions_weighted : LocalConditionsWeighted := by
  intro K _ _ _ Z _ _ _ _ _ w P _ _ ρ U ψ hMk V₀ e he hr M Th1 Th ThK Th0 ThJ X₃ hM hTh1 hTh hThK h1le hle hFG hEig
    hMs hTs σ hσ hsc hdata a E r ha hE hT0 h0 hJ h0J h3 X _ _ _ _ θ' eX pr Mt hc hk h4 h34 ε hTW d φ hinj hrng
    Mj Tj hMj hTj
  have hT0' := enlarge_initial_lattice K Z w M Th1 Th hM hTh1 hTh h1le hle (E : ℝ) r hT0
  have hc' : (θ'.restrictScalars (𝓞 K)) ∘ₗ (eX.restrictScalars (𝓞 K)) =
      (e.restrictScalars (𝓞 K)) ∘ₗ (θ'.restrictScalars (𝓞 K)) :=
    LinearMap.ext fun x => LinearMap.congr_fun hc x
  have hk' : ∀ x ∈ LinearMap.range (eX.restrictScalars (𝓞 K)),
      x - (pr.restrictScalars (𝓞 K)) x ∈ LinearMap.ker (θ'.restrictScalars (𝓞 K)) := by
    intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hx
    exact LinearMap.mem_ker.2 (LinearMap.mem_ker.1 (hk _ (LinearMap.mem_range_self eX y)))
  have hid := theta_identity (𝓞 K) X Z (θ'.restrictScalars (𝓞 K)) (eX.restrictScalars (𝓞 K))
    (pr.restrictScalars (𝓞 K)) (e.restrictScalars (𝓞 K)) hc' hk' Mt
  exact local_conditions_family K Z w P ρ U ψ hMk V₀ e he hr M Th ThK Th0 ThJ X₃
    ((Mt.map (θ'.restrictScalars (𝓞 K))).map (e.restrictScalars (𝓞 K))) hM hTh hThK hle hFG hEig hMs hTs
    σ hσ hsc hdata a E r ha hE hT0' h0 hJ h0J h3 h4 h34 ε hTW d φ hinj hrng Mj Tj hMj (hTj.trans hid)

/- English proof (translation)
Establish `hfix : X₄.map (e.restrictScalars (𝓞 K)) = X₄`. Establish `h4c` using `h4`. Take `⟨-, h4s⟩` from `h4c`. Establish `hsub : ∀ x ∈ X₄, e x = x`. Introduce `x hx`.

Establish `hx1 : x ∈ Submodule.span K (X₄ : Set Z)` using `Submodule.subset_span hx`. Rewrite `hx1` using `[h4s]`. Establish `hx2 : x ∈ LinearMap.range e`. Rewrite using `[hr]`. Conclude with `(Submodule.mem_inf.1 hx1).2`.

Take `⟨y, rfl⟩` from `LinearMap.mem_range.1 hx2`. Rewrite using `[← LinearMap.comp_apply e e, he]`. Use extensionality with `x`. Simplify using `only [Submodule.mem_map, LinearMap.coe_restrictScalars]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩`. Rewrite using `[hsub y hy]`. Conclude with `hy`. Introduce `hx`. Conclude with `⟨x, hx, hsub x hx⟩`.

Establish `hid : X₄.map ((LinearMap.id : Z →ₗ[K] Z).restrictScalars (𝓞 K)) = X₄`. Use extensionality with `x`. Simplify using the standard rewrite rules. Conclude with `h K Z w P ρ U ψ hMk V₀ e he hr M Th Th ThK Th0 ThJ X₃ hM hTh hTh hThK le_rfl hle hFG hEig hMs hTs σ hσ hsc hdata a E r ha hE hT0 h0 hJ h0J h3 Z LinearMap.id e LinearMap.id X₄ (by rw [LinearMap.id_comp, LinearMap.comp_id]) (fun x _ => by simp) (by rw [hid, hfix]; exact h4) (by rw …`.
-/
theorem localConditionsFamily_of_weighted (h : LocalConditionsWeighted)
    (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (P : Type) [Group P] [Finite P] (ρ : Representation K P Z)
    (U : Subgroup P) (ψ : P → 𝓞 K) (hMk : IsMackey U ψ)
    (V₀ : Submodule K Z) (e : Z →ₗ[K] Z) (he : e ∘ₗ e = e) (hr : LinearMap.range e = V₀)
    (M Th ThK Th0 ThJ X₃ X₄ : Submodule (𝓞 K) Z)
    (hM : IsLatIn ⊤ M) (hTh : IsLatIn ⊤ Th) (hThK : IsLatIn ⊤ ThK) (hle : Th ≤ M) (hFG : Th0.FG)
    (hEig : Th0 ≤ (eig ρ U ψ).restrictScalars (𝓞 K))
    (hMs : ∀ g : P, M.map ((ρ g).restrictScalars (𝓞 K)) ≤ M)
    (hTs : ∀ g : P, Th.map ((ρ g).restrictScalars (𝓞 K)) ≤ Th)
    (σ : K) (hσ : σ ≠ 0) (hsc : Th ≤ sc σ ThK)
    (hdata : sc ((Nat.card U : ℕ) : K) (cut (eig ρ U ψ) ThK) ≤ Th0)
    (a : K) (E : ℕ) (r : ℝ) (ha : a ≠ 0) (hE : vw w a = (E : ℤ))
    (hT0 : ∀ W : Submodule K Z, (lix w (cut W M) (cut W Th) : ℝ) ≤ (E : ℝ) * (finrank K W : ℝ) + r)
    (h0 : IsLatIn (eig ρ U ψ ⊓ V₀) (Th0.map (e.restrictScalars (𝓞 K))))
    (hJ : IsLatIn (eig ρ U ψ ⊓ V₀) (ThJ.map (e.restrictScalars (𝓞 K)))) (h0J : Th0 ≤ ThJ)
    (h3 : IsLatIn (eig ρ U ψ ⊓ V₀) X₃) (h4 : IsLatIn (eig ρ U ψ ⊓ V₀) X₄) (h34 : X₃ ≤ X₄)
    (ε : ℝ)
    (hTW : (lix w (cut (eig ρ U ψ ⊓ V₀) M) X₃ : ℝ) ≤
      (lix w (cut (eig ρ U ψ ⊓ V₀) M) (ThJ.map (e.restrictScalars (𝓞 K))) : ℝ) + ε)
    (d : ℕ) (φ : (Fin d → K) →ₗ[K] Z) (hinj : Function.Injective φ)
    (hrng : LinearMap.range φ = eig ρ U ψ ⊓ V₀)
    (Mj Tj : Submodule (𝓞 K) (Fin d → K))
    (hMj : Mj.map (φ.restrictScalars (𝓞 K)) = cut (eig ρ U ψ ⊓ V₀) M)
    (hTj : Tj.map (φ.restrictScalars (𝓞 K)) = X₄) :
      (idx w Mj Tj : ℝ) ≤
        ((E : ℝ) - (vw w σ : ℝ) + (vw w ((Nat.card U : ℕ) : K) : ℝ)) * (d : ℝ) +
          (r + (finrank K Z : ℝ) * (vw w ((Nat.card U : ℕ) : K) : ℝ)) / (U.index : ℝ) + ε := by
  have hfix : X₄.map (e.restrictScalars (𝓞 K)) = X₄ := by
    have h4c := h4
    obtain ⟨-, h4s⟩ := h4c
    have hsub : ∀ x ∈ X₄, e x = x := by
      intro x hx
      have hx1 : x ∈ Submodule.span K (X₄ : Set Z) := Submodule.subset_span hx
      rw [h4s] at hx1
      have hx2 : x ∈ LinearMap.range e := by
        rw [hr]
        exact (Submodule.mem_inf.1 hx1).2
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hx2
      rw [← LinearMap.comp_apply e e, he]
    ext x
    simp only [Submodule.mem_map, LinearMap.coe_restrictScalars]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hsub y hy]
      exact hy
    · intro hx
      exact ⟨x, hx, hsub x hx⟩
  have hid : X₄.map ((LinearMap.id : Z →ₗ[K] Z).restrictScalars (𝓞 K)) = X₄ := by
    ext x
    simp
  exact h K Z w P ρ U ψ hMk V₀ e he hr M Th Th ThK Th0 ThJ X₃ hM hTh hTh hThK le_rfl hle hFG hEig hMs hTs
    σ hσ hsc hdata a E r ha hE hT0 h0 hJ h0J h3 Z LinearMap.id e LinearMap.id X₄
    (by rw [LinearMap.id_comp, LinearMap.comp_id]) (fun x _ => by simp)
    (by rw [hid, hfix]; exact h4) (by rw [hid, hfix]; exact h34) ε hTW d φ hinj hrng Mj Tj hMj
    (by rw [hTj, hfix, hid, hid])

/- English proof (translation)
Introduce `R _ I r t A A' B B' C C' D D' hM hB`. Rewrite `hM` using `[Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]`. Take `⟨hTL, hTR, -, -⟩` from `hM`. Establish `hB0 : B.map (Ideal.Quotient.mk I) = 0`. Use extensionality with `i j`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (hB i j)`. Establish `hTL' : A.map (Ideal.Quotient.mk I) * A'.map (Ideal.Quotient.mk I) = 1`. Establish `h1` using `congrArg (fun X => X.map (Ideal.Quotient.mk I)) hTL`. Simplify using `only [Matrix.map_add _ (map_add (Ideal.Quotient.mk I)), Matrix.map_mul, hB0, Matrix.zero_mul, add_zero, Matrix.map_one _ (map_zero (Ideal.Quotient.mk I)) (map_one (Ideal.Quotient.mk I))] at h1`. Conclude with `h1`.

Establish `hTR' : A.map (Ideal.Quotient.mk I) * B'.map (Ideal.Quotient.mk I) = 0`. Establish `h1` using `congrArg (fun X => X.map (Ideal.Quotient.mk I)) hTR`. Simplify using `only [Matrix.map_add _ (map_add (Ideal.Quotient.mk I)), Matrix.map_mul, hB0, Matrix.zero_mul, add_zero, Matrix.map_zero _ (map_zero (Ideal.Quotient.mk I))] at h1`. Conclude with `h1`. Establish `hA'A : A'.map (Ideal.Quotient.mk I) * A.map (Ideal.Quotient.mk I) = 1` using `by first`.

Consider the case `exact mul_eq_one_comm.1 hTL'`. Consider the case `exact Matrix.mul_eq_one_comm.mp hTL'`. Consider the case `exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hTL'`. Establish `hB'0 : B'.map (Ideal.Quotient.mk I) = 0`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hA'A, Matrix.one_mul]`. Use `_ = A'.map (Ideal.Quotient.mk I) * (A.map (Ideal.Quotient.mk I) * B'.map (Ideal.Quotient.mk I)) := Matrix.mul_assoc _ _ _`. Use `_ = 0 := by rw [hTR', Matrix.mul_zero]`. Establish `hent : ∀ {m n : Type} (X : Matrix m n R), X.map (Ideal.Quotient.mk I) = 0 → ∀ i j, X i j ∈ I`. Introduce `m n X hX i j`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (congrFun hX i) j)`. Use `⟨?_, hent _ ?_, hent _ ?_, hent _ hB'0⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq]`. Simplify using `only [RingHom.map_det, map_mul, RingHom.mapMatrix_apply, Matrix.fromBlocks_map, hB0, Matrix.det_fromBlocks_zero₁₂]`. Rewrite using `[Matrix.map_sub _ (map_sub (Ideal.Quotient.mk I)), Matrix.map_mul, Matrix.map_one _ (map_zero (Ideal.Quotient.mk I)) (map_one (Ideal.Quotient.mk I)), hTL', sub_self]`.

Rewrite using `[Matrix.map_sub _ (map_sub (Ideal.Quotient.mk I)), Matrix.map_mul, Matrix.map_one _ (map_zero (Ideal.Quotient.mk I)) (map_one (Ideal.Quotient.mk I)), hA'A, sub_self]`.
-/
theorem block_type : BlockType := by
  intro R _ I r t A A' B B' C C' D D' hM hB
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at hM
  obtain ⟨hTL, hTR, -, -⟩ := hM
  have hB0 : B.map (Ideal.Quotient.mk I) = 0 := by
    ext i j
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hB i j)
  have hTL' : A.map (Ideal.Quotient.mk I) * A'.map (Ideal.Quotient.mk I) = 1 := by
    have h1 := congrArg (fun X => X.map (Ideal.Quotient.mk I)) hTL
    simp only [Matrix.map_add _ (map_add (Ideal.Quotient.mk I)), Matrix.map_mul, hB0, Matrix.zero_mul, add_zero,
      Matrix.map_one _ (map_zero (Ideal.Quotient.mk I)) (map_one (Ideal.Quotient.mk I))] at h1
    exact h1
  have hTR' : A.map (Ideal.Quotient.mk I) * B'.map (Ideal.Quotient.mk I) = 0 := by
    have h1 := congrArg (fun X => X.map (Ideal.Quotient.mk I)) hTR
    simp only [Matrix.map_add _ (map_add (Ideal.Quotient.mk I)), Matrix.map_mul, hB0, Matrix.zero_mul, add_zero,
      Matrix.map_zero _ (map_zero (Ideal.Quotient.mk I))] at h1
    exact h1
  have hA'A : A'.map (Ideal.Quotient.mk I) * A.map (Ideal.Quotient.mk I) = 1 := by
    first
      | exact mul_eq_one_comm.1 hTL'
      | exact Matrix.mul_eq_one_comm.mp hTL'
      | exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hTL'
  have hB'0 : B'.map (Ideal.Quotient.mk I) = 0 := by
    calc B'.map (Ideal.Quotient.mk I)
        = (A'.map (Ideal.Quotient.mk I) * A.map (Ideal.Quotient.mk I)) * B'.map (Ideal.Quotient.mk I) := by
          rw [hA'A, Matrix.one_mul]
      _ = A'.map (Ideal.Quotient.mk I) * (A.map (Ideal.Quotient.mk I) * B'.map (Ideal.Quotient.mk I)) :=
          Matrix.mul_assoc _ _ _
      _ = 0 := by rw [hTR', Matrix.mul_zero]
  have hent : ∀ {m n : Type} (X : Matrix m n R), X.map (Ideal.Quotient.mk I) = 0 → ∀ i j, X i j ∈ I := by
    intro m n X hX i j
    exact Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (congrFun hX i) j)
  refine ⟨?_, hent _ ?_, hent _ ?_, hent _ hB'0⟩
  · rw [← Ideal.Quotient.eq]
    simp only [RingHom.map_det, map_mul, RingHom.mapMatrix_apply, Matrix.fromBlocks_map, hB0,
      Matrix.det_fromBlocks_zero₁₂]
  · rw [Matrix.map_sub _ (map_sub (Ideal.Quotient.mk I)), Matrix.map_mul,
      Matrix.map_one _ (map_zero (Ideal.Quotient.mk I)) (map_one (Ideal.Quotient.mk I)), hTL', sub_self]
  · rw [Matrix.map_sub _ (map_sub (Ideal.Quotient.mk I)), Matrix.map_mul,
      Matrix.map_one _ (map_zero (Ideal.Quotient.mk I)) (map_one (Ideal.Quotient.mk I)), hA'A, sub_self]

/- English proof (translation)
Introduce `T D nW r t h0 c hD hr ht hnW hT`. Establish `h2 : 2 * (D + 2) ≤ (D + 2) * nW` using `by nlinarith`. Establish `hb : 0 ≤ T + D + 2 + r` using `by linarith`. Establish `hle : T + D + 2 + r ≤ 3 / 2 * T` using `by linarith`. Establish `hsq` using `mul_self_le_mul_self hb hle`.

Establish `key : (T + D + 2) * (T + D + 2 + 2 * r) ≤ 9 / 4 * T ^ 2` using `by nlinarith [sq_nonneg r]`. Establish `e : (3.75 : ℝ) = 15 / 4` using `by norm_num`. Rewrite using `[e]`. Conclude with `⟨by nlinarith [sq_nonneg T], fun hh hc => by nlinarith [sq_nonneg T]⟩`.
-/
theorem gapConditions_of_largeGaps : GapNum := by
  intro T D nW r t h0 c hD hr ht hnW hT
  have h2 : 2 * (D + 2) ≤ (D + 2) * nW := by nlinarith
  have hb : 0 ≤ T + D + 2 + r := by linarith
  have hle : T + D + 2 + r ≤ 3 / 2 * T := by linarith
  have hsq := mul_self_le_mul_self hb hle
  have key : (T + D + 2) * (T + D + 2 + 2 * r) ≤ 9 / 4 * T ^ 2 := by nlinarith [sq_nonneg r]
  have e : (3.75 : ℝ) = 15 / 4 := by norm_num
  rw [e]
  exact ⟨by nlinarith [sq_nonneg T], fun hh hc => by nlinarith [sq_nonneg T]⟩

/- English proof (translation)
Introduce `R K σ _ _ _ hinj Del Q m c hD hc`. Establish `hcoef : c = algebraMap R K (Q.coeff m)`. Establish `h1` using `congrArg (MvPolynomial.coeff m) hc`. Rewrite `h1` using `[MvPolynomial.coeff_smul, MvPolynomial.coeff_map, MvPolynomial.coeff_map, hD, map_one, smul_eq_mul, mul_one]`. Conclude with `h1`.

Use `⟨Q.coeff m, hcoef.symm, ?_⟩` and prove the remaining obligations. Establish `hmap : MvPolynomial.map (algebraMap R K) Q = MvPolynomial.map (algebraMap R K) (Q.coeff m • Del)`. Rewrite using `[← hc, hcoef, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]`. Use `first`. Consider the case `exact MvPolynomial.map_injective _ hinj hmap`.

Consider the case `exact MvPolynomial.map_injective hinj hmap`.
-/
theorem primitive_line : PrimitiveLine := by
  intro R K σ _ _ _ hinj Del Q m c hD hc
  have hcoef : c = algebraMap R K (Q.coeff m) := by
    have h1 := congrArg (MvPolynomial.coeff m) hc
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, MvPolynomial.coeff_map, hD, map_one, smul_eq_mul,
      mul_one] at h1
    exact h1
  refine ⟨Q.coeff m, hcoef.symm, ?_⟩
  have hmap : MvPolynomial.map (algebraMap R K) Q = MvPolynomial.map (algebraMap R K) (Q.coeff m • Del) := by
    rw [← hc, hcoef, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
  first
    | exact MvPolynomial.map_injective _ hinj hmap
    | exact MvPolynomial.map_injective hinj hmap

/- English proof (translation)
Apply the tactic sequence `rw [Int.ceil_eq_iff]; constructor <;> norm_num`.
-/
example : ⌈((1 : ℤ) : ℝ) * (((3 : ℕ) : ℝ) * ((2 : ℝ) / (15 - 1) + 1))⌉ = (1 : ℤ) * (((3 : ℕ) : ℤ) + 1) := by
  rw [Int.ceil_eq_iff]; constructor <;> norm_num

/- English proof (translation)
Rewrite using `[Int.ceil_le]`. Evaluate the numerical expressions.
-/
example : ¬ (⌈((1 : ℤ) : ℝ) * (((3 : ℕ) : ℝ) * ((2 : ℝ) / (2 - 1) + 1))⌉ ≤ (1 : ℤ) * (((3 : ℕ) : ℤ) + 1)) := by
  rw [Int.ceil_le]; norm_num

/- English proof (translation)
The claim follows from `constant_b_bound 1 3 1 1 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)`.
-/
example : (1 : ℝ) * 1 * (1 * 1 ^ 3) / (4 * 1) + 2 * (1 * 1 ^ 3) * 1 ^ 2 / 1 ≤ 1 * 3 * 1 ^ 2 / 1 :=
  constant_b_bound 1 3 1 1 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/- English proof (translation)
The claim follows from `theta_identity ℤ (ℤ × ℤ) ℤ (LinearMap.fst ℤ ℤ ℤ) LinearMap.id _ LinearMap.id rfl (by intro x _; simp [LinearMap.mem_ker]) Mt`.
-/
example (Mt : Submodule ℤ (ℤ × ℤ)) :
    ((Mt.map (LinearMap.id : ℤ × ℤ →ₗ[ℤ] ℤ × ℤ)).map
      ((LinearMap.inl ℤ ℤ ℤ) ∘ₗ (LinearMap.fst ℤ ℤ ℤ))).map (LinearMap.fst ℤ ℤ ℤ) =
      (Mt.map (LinearMap.fst ℤ ℤ ℤ)).map (LinearMap.id : ℤ →ₗ[ℤ] ℤ) :=
  theta_identity ℤ (ℤ × ℤ) ℤ (LinearMap.fst ℤ ℤ ℤ) LinearMap.id _ LinearMap.id rfl
    (by intro x _; simp [LinearMap.mem_ker]) Mt

/- English proof (translation)
The claim follows from `(theta_identity_orthogonal ℤ (ℤ × ℤ) ℤ ℤ (LinearMap.fst ℤ ℤ ℤ) LinearMap.id (LinearMap.inl ℤ ℤ ℤ ∘ₗ LinearMap.fst ℤ ℤ ℤ) LinearMap.id (fun x y => x.1 * y.1 + x.2 * y.2) rfl (fun _ _ => rfl) (by ext <;> simp) (by ext x; simp [LinearMap.mem_ker]) (by intro x constructor · rintro ⟨y …`.
-/
example : (LinearMap.inl ℤ ℤ ℤ ∘ₗ LinearMap.fst ℤ ℤ ℤ) ∘ₗ (LinearMap.id : ℤ × ℤ →ₗ[ℤ] ℤ × ℤ) =
    (LinearMap.id : ℤ × ℤ →ₗ[ℤ] ℤ × ℤ) ∘ₗ (LinearMap.inl ℤ ℤ ℤ ∘ₗ LinearMap.fst ℤ ℤ ℤ) :=
  (theta_identity_orthogonal ℤ (ℤ × ℤ) ℤ ℤ (LinearMap.fst ℤ ℤ ℤ) LinearMap.id
    (LinearMap.inl ℤ ℤ ℤ ∘ₗ LinearMap.fst ℤ ℤ ℤ) LinearMap.id (fun x y => x.1 * y.1 + x.2 * y.2) rfl
    (fun _ _ => rfl) (by ext <;> simp)
    (by ext x; simp [LinearMap.mem_ker])
    (by
      intro x
      constructor
      · rintro ⟨y, rfl⟩ k hk
        have : k.1 = 0 := by simpa [LinearMap.mem_ker] using hk
        simp [this]
      · intro hx
        have := hx (0, 1) (by simp [LinearMap.mem_ker])
        refine ⟨x, ?_⟩
        ext <;> simp at this ⊢
        exact this.symm)).1

/- English proof (translation)
The claim follows from `(gapConditions_of_largeGaps 8 0 2 2 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1`.
-/
example : ((8 : ℝ) + 0 + 2) * (8 + 0 + 2 + 2 * 2) ≤ 3.75 * 8 ^ 2 :=
  (gapConditions_of_largeGaps 8 0 2 2 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1

/- English proof (translation)
Introduce `K _ _ _ D hD Tup μ J _ d hd M T θ S e0 r0 ε0 F0 errl Jx vU0 gq dK EA Rb EJ δq E3 hδ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10`. Take `⟨-, hA, hB, hC⟩` from `h K D hD Tup μ J d hd M T θ S e0 r0 ε0 F0 errl Jx vU0 gq dK EA Rb EJ δq E3 hδ h1 h2 h3 h4 h5 (fun w hw => by`. Establish `hw6` using `h6 w hw`. Establish `hp : 0 ≤ 1 / (plc w : ℝ) ^ 2` using `by positivity`. Distinguish the cases in `hc : conjPl w = w`.

Simplify using `only [if_pos hc, add_zero]`. Rewrite `hw6` using `[hc, Finset.sum_add_distrib]`. Distinguish the cases in `hs : 0 ≤ ∑ j, ε0 w j`. Combine the linear equalities and inequalities to obtain the conclusion. Use `push_neg at hs`.

Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [if_neg hc]`. Conclude with `hw6) h7 h8 h9 h10`. Conclude with `⟨hA, hB, hC⟩`.
-/
theorem onExport_of_onExportSet (h : OnExportSet) : OnExport := by
  intro K _ _ _ D hD Tup μ J _ d hd M T θ S e0 r0 ε0 F0 errl Jx vU0 gq dK EA Rb EJ δq E3 hδ h1 h2 h3 h4 h5 h6 h7 h8
    h9 h10
  obtain ⟨-, hA, hB, hC⟩ := h K D hD Tup μ J d hd M T θ S e0 r0 ε0 F0 errl Jx vU0 gq dK EA Rb EJ δq E3 hδ h1 h2 h3
    h4 h5 (fun w hw => by
    have hw6 := h6 w hw
    have hp : 0 ≤ 1 / (plc w : ℝ) ^ 2 := by positivity
    by_cases hc : conjPl w = w
    · simp only [if_pos hc, add_zero]
      rw [hc, Finset.sum_add_distrib] at hw6
      by_cases hs : 0 ≤ ∑ j, ε0 w j
      · linarith
      · push_neg at hs
        linarith
    · simp only [if_neg hc]
      exact hw6) h7 h8 h9 h10
  exact ⟨hA, hB, hC⟩

open Classical in

/- English proof (translation)
Introduce `w hw`. Conclude with `twist_set_double K J ε0 w (h w hw)`.
-/
theorem twistSetDouble_finset (K : Type) [Field K] [NumberField K] [StarRing K] (J : Type) [Fintype J]
    (ε0 : HeightOneSpectrum (𝓞 K) → J → ℝ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (h : ∀ w ∈ S, ∑ j, (ε0 w j + (if conjPl w = w then 0 else ε0 (conjPl w) j)) ≤ 1 / (plc w : ℝ) ^ 2) :
    ∀ w ∈ S, ∑ j, (ε0 w j + ε0 (conjPl w) j) ≤ 2 / (plc w : ℝ) ^ 2 := by
  intro w hw
  exact twist_set_double K J ε0 w (h w hw)

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem levelCeil_tower (ρ1 ρ2 : ℤ) (T : ℕ) (DL Dk g : ℝ) (h1 : 0 ≤ ρ1) (h2 : 0 ≤ ρ2) (h3 : 0 ≤ DL)
    (h4 : (T : ℝ) * DL ≤ Dk) (h5 : 2 * Dk + 2 < g) :
    ρ1 * ⌈(ρ2 : ℝ) * ((T : ℝ) * (DL / (g - 1) + 1))⌉ ≤ (ρ1 * ρ2) * ((T : ℤ) + 1) := by
  calc ρ1 * ⌈(ρ2 : ℝ) * ((T : ℝ) * (DL / (g - 1) + 1))⌉ ≤ ρ1 * (ρ2 * ((T : ℤ) + 1)) :=
        mul_le_mul_of_nonneg_left (level_ceiling ρ2 T DL Dk g h2 h3 h4 h5) h1
    _ = (ρ1 * ρ2) * ((T : ℤ) + 1) := by ring

/- English proof (translation)
Establish `a : ⌈((2 : ℤ) : ℝ) * (1.25 : ℝ)⌉ = 3` using `by rw [Int.ceil_eq_iff]; norm_num`. Establish `b : ⌈((1 : ℤ) : ℝ) * (1.25 : ℝ)⌉ = 2` using `by rw [Int.ceil_eq_iff]; norm_num`. Rewrite using `[a, b]`. Evaluate the numerical expressions.
-/
example : ⌈((2 : ℤ) : ℝ) * (1.25 : ℝ)⌉ < 2 * ⌈((1 : ℤ) : ℝ) * (1.25 : ℝ)⌉ := by
  have a : ⌈((2 : ℤ) : ℝ) * (1.25 : ℝ)⌉ = 3 := by rw [Int.ceil_eq_iff]; norm_num
  have b : ⌈((1 : ℤ) : ℝ) * (1.25 : ℝ)⌉ = 2 := by rw [Int.ceil_eq_iff]; norm_num
  rw [a, b]; norm_num

/- English proof (translation)
Rewrite using `[scalar_level K w nnL nnF q Z1 Z2 T c h1 h2 h3 h4 h5 z1 z2]`. Establish `hR` using `ramw_nonneg_lemma_2 K w`. Establish `hA : 0 ≤ ramw w * ((T : ℤ) - 1)` using `mul_nonneg hR (by omega)`. Establish `hB : 0 ≤ (c : ℤ) * vw w q` using `mul_nonneg (by omega) hq`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem levelPlace_any (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K))
    (nnL nnF q Z1 Z2 : K) (T c : ℕ) (E : ℤ) (h1 : nnL ≠ 0) (h2 : nnF ≠ 0) (h3 : q ≠ 0) (h4 : Z1 ≠ 0) (h5 : Z2 ≠ 0)
    (z1 : vw w Z1 = 0) (z2 : vw w Z2 = 0) (hq : 0 ≤ vw w q) (hT : 1 ≤ T) (hE : E ≤ ramw w * ((T : ℤ) + 1)) :
    E - vw w ((nnL * Z1) ^ T * (nnF * q ^ c * Z2)) ≤ ramw w * (2 * (T : ℤ)) - vw w (nnL ^ T * nnF) := by
  rw [scalar_level K w nnL nnF q Z1 Z2 T c h1 h2 h3 h4 h5 z1 z2]
  have hR := ramw_nonneg_lemma_2 K w
  have hA : 0 ≤ ramw w * ((T : ℤ) - 1) := mul_nonneg hR (by omega)
  have hB : 0 ≤ (c : ℤ) * vw w q := mul_nonneg (by omega) hq
  linarith

/- English proof (translation)
Conclude with `levelPlace_any K w nnL nnF q Z1 Z2 T c _ h1 h2 h3 h4 h5 z1 z2 hq hT (by rw [hρ]; exact levelCeil_tower ρ1 ρ2 T DL Dk g r1 r2 h0 hTD hg)`.
-/
theorem levelPlace_tower (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K))
    (nnL nnF q Z1 Z2 : K) (T c : ℕ) (DL Dk g : ℝ) (ρ1 ρ2 : ℤ) (h1 : nnL ≠ 0) (h2 : nnF ≠ 0) (h3 : q ≠ 0)
    (h4 : Z1 ≠ 0) (h5 : Z2 ≠ 0) (z1 : vw w Z1 = 0) (z2 : vw w Z2 = 0) (hq : 0 ≤ vw w q) (hT : 1 ≤ T) (h0 : 0 ≤ DL)
    (hTD : (T : ℝ) * DL ≤ Dk) (hg : 2 * Dk + 2 < g) (r1 : 0 ≤ ρ1) (r2 : 0 ≤ ρ2) (hρ : ramw w = ρ1 * ρ2) :
    ρ1 * ⌈(ρ2 : ℝ) * ((T : ℝ) * (DL / (g - 1) + 1))⌉ - vw w ((nnL * Z1) ^ T * (nnF * q ^ c * Z2)) ≤
      ramw w * (2 * (T : ℤ)) - vw w (nnL ^ T * nnF) := by
  exact levelPlace_any K w nnL nnF q Z1 Z2 T c _ h1 h2 h3 h4 h5 z1 z2 hq hT
    (by rw [hρ]; exact levelCeil_tower ρ1 ρ2 T DL Dk g r1 r2 h0 hTD hg)

section Instance

variable (K : Type) [Field K] [NumberField K] [StarRing K]

def unitLat : Submodule (𝓞 K) K := Submodule.span (𝓞 K) {(1 : K)}

/- English proof (translation)
Unfold `IsLatIn unitLat`. Use `⟨Submodule.fg_span_singleton _, ?_⟩` and prove the remaining obligations. Use `first`. Consider the case `(rw [Submodule.span_span_of_tower]`. Conclude with `eq_top_iff.2 fun x _ => Submodule.mem_span_singleton.2 ⟨x, by simp⟩)`.

Consider the case `(refine eq_top_iff.2 fun x _ => ?_`. Establish `h1 : (1 : K) ∈ (Submodule.span (𝓞 K) {(1 : K)} : Set K)` using `Submodule.subset_span rfl`. Establish `h2` using `Submodule.smul_mem (Submodule.span K (Submodule.span (𝓞 K) {(1 : K)} : Set K)) x (Submodule.subset_span h1)`. Simplify using `using h2)`.
-/
theorem unitLat_isLatIn : IsLatIn (⊤ : Submodule K K) (unitLat K) := by
  unfold IsLatIn unitLat
  refine ⟨Submodule.fg_span_singleton _, ?_⟩
  first
    | (rw [Submodule.span_span_of_tower]
       exact eq_top_iff.2 fun x _ => Submodule.mem_span_singleton.2 ⟨x, by simp⟩)
    | (refine eq_top_iff.2 fun x _ => ?_
       have h1 : (1 : K) ∈ (Submodule.span (𝓞 K) {(1 : K)} : Set K) := Submodule.subset_span rfl
       have h2 := Submodule.smul_mem (Submodule.span K (Submodule.span (𝓞 K) {(1 : K)} : Set K)) x
         (Submodule.subset_span h1)
       simpa using h2)

/- English proof (translation)
Apply `eq_top_iff.2` to reduce the goal to its premises. Introduce `x _`. Unfold `eig`. Rewrite using `[Submodule.mem_iInf]`. Introduce `u`.

Rewrite using `[LinearMap.mem_ker]`. Simplify using the standard rewrite rules.
-/
theorem eig_trivial : eig (1 : Representation K Unit K) ⊤ (fun _ => (1 : 𝓞 K)) = ⊤ := by
  apply eq_top_iff.2
  intro x _
  unfold eig
  rw [Submodule.mem_iInf]
  intro u
  rw [LinearMap.mem_ker]
  simp

/- English proof (translation)
Use `first`. Consider the case `(ext x; simp)`. Consider the case `exact Submodule.map_id A`.
-/
theorem map_id_restrict (A : Submodule (𝓞 K) K) :
    A.map ((LinearMap.id : K →ₗ[K] K).restrictScalars (𝓞 K)) = A := by
  first
    | (ext x; simp)
    | exact Submodule.map_id A

/- English proof (translation)
Introduce `d φ hinj hrng Mj Tj hMj hTj`. Establish `hv1 : vw w (1 : K) = 0`. Unfold `vw`. Rewrite using `[FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]`. Establish `hc : ((Nat.card (⊤ : Subgroup Unit) : ℕ) : K) = 1` using `by first`.

Consider the case `simp`. Consider the case `(rw [Subgroup.card_top, Nat.card_unique, Nat.cast_one])`. Establish `hidx : (((⊤ : Subgroup Unit).index : ℕ) : ℝ) = 1`. Rewrite using `[Subgroup.index_top, Nat.cast_one]`. Establish `hcut : cut (eig (1 : Representation K Unit K) ⊤ (fun _ => (1 : 𝓞 K)) ⊓ ⊤) (unitLat K) = unitLat K`.

Unfold `cut`. Rewrite using `[eig_trivial K]`. Simplify using the standard rewrite rules. Establish `hMT : Mj = Tj`. Apply `Submodule.map_injective_of_injective (f := φ.restrictScalars (𝓞 K)) hinj` to reduce the goal to its premises.

Rewrite using `[hMj, hTj, hcut, map_id_restrict K, map_id_restrict K, map_id_restrict K]`. Substitute `hMT` using the available equality. Establish `h0 : idx w Mj Mj = 0`. Unfold `idx Formalism.HermitianLatticesTheory.lidx`. Conclude with `sub_self _`.

Rewrite using `[h0, hc, hv1, hidx]`. Simplify using the standard rewrite rules.
-/
theorem localConditionsWeighted_trivial_instance (w : HeightOneSpectrum (𝓞 K)) :
    ∀ (d : ℕ) (φ : (Fin d → K) →ₗ[K] K), Function.Injective φ →
    LinearMap.range φ = eig (1 : Representation K Unit K) ⊤ (fun _ => (1 : 𝓞 K)) ⊓ ⊤ →
    ∀ (Mj Tj : Submodule (𝓞 K) (Fin d → K)),
    Mj.map (φ.restrictScalars (𝓞 K)) =
      cut (eig (1 : Representation K Unit K) ⊤ (fun _ => (1 : 𝓞 K)) ⊓ ⊤) (unitLat K) →
    Tj.map (φ.restrictScalars (𝓞 K)) =
      (((unitLat K).map ((LinearMap.id : K →ₗ[K] K).restrictScalars (𝓞 K))).map
        ((LinearMap.id : K →ₗ[K] K).restrictScalars (𝓞 K))).map ((LinearMap.id : K →ₗ[K] K).restrictScalars (𝓞 K)) →
      (idx w Mj Tj : ℝ) ≤
        (((0 : ℕ) : ℝ) - (vw w (1 : K) : ℝ) + (vw w ((Nat.card (⊤ : Subgroup Unit) : ℕ) : K) : ℝ)) * (d : ℝ) +
          (0 + (finrank K K : ℝ) * (vw w ((Nat.card (⊤ : Subgroup Unit) : ℕ) : K) : ℝ)) /
            ((⊤ : Subgroup Unit).index : ℝ) + 0 := by
  intro d φ hinj hrng Mj Tj hMj hTj
  have hv1 : vw w (1 : K) = 0 := by
    unfold vw
    rw [FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]
  have hc : ((Nat.card (⊤ : Subgroup Unit) : ℕ) : K) = 1 := by
    first
      | simp
      | (rw [Subgroup.card_top, Nat.card_unique, Nat.cast_one])
  have hidx : (((⊤ : Subgroup Unit).index : ℕ) : ℝ) = 1 := by
    rw [Subgroup.index_top, Nat.cast_one]
  have hcut : cut (eig (1 : Representation K Unit K) ⊤ (fun _ => (1 : 𝓞 K)) ⊓ ⊤) (unitLat K) = unitLat K := by
    unfold cut
    rw [eig_trivial K]
    simp
  have hMT : Mj = Tj := by
    apply Submodule.map_injective_of_injective (f := φ.restrictScalars (𝓞 K)) hinj
    rw [hMj, hTj, hcut, map_id_restrict K, map_id_restrict K, map_id_restrict K]
  subst hMT
  have h0 : idx w Mj Mj = 0 := by
    unfold idx Formalism.HermitianLatticesTheory.lidx
    exact sub_self _
  rw [h0, hc, hv1, hidx]
  simp

/- English proof (translation)
Establish `hcut : cut (eig (1 : Representation K Unit K) ⊤ (fun _ => (1 : 𝓞 K)) ⊓ ⊤) (unitLat K) = unitLat K`. Unfold `cut`. Rewrite using `[eig_trivial K]`. Simplify using the standard rewrite rules. Use `⟨(LinearEquiv.funUnique (Fin 1) K K).toLinearMap, (unitLat K).comap ((LinearEquiv.funUnique (Fin 1) K K).toLinearMap.restrictScalars (𝓞 K)), (LinearEquiv.funUnique (Fin 1) K K).injective, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[eig_trivial K, inf_top_eq]`. Conclude with `LinearEquiv.range _`. Rewrite using `[Submodule.map_comap_eq_of_surjective (f := (LinearEquiv.funUnique (Fin 1) K K).toLinearMap.restrictScalars (𝓞 K)) (LinearEquiv.funUnique (Fin 1) K K).surjective, hcut]`. Rewrite using `[Submodule.map_comap_eq_of_surjective (f := (LinearEquiv.funUnique (Fin 1) K K).toLinearMap.restrictScalars (𝓞 K)) (LinearEquiv.funUnique (Fin 1) K K).surjective, map_id_restrict K, map_id_restrict K, map_id_restrict K]`. Unfold `idx Formalism.HermitianLatticesTheory.lidx`.

Simplify using the standard rewrite rules.
-/
theorem localConditionsWeighted_trivial_coords (w : HeightOneSpectrum (𝓞 K)) :
    ∃ (φ : (Fin 1 → K) →ₗ[K] K) (Mj : Submodule (𝓞 K) (Fin 1 → K)), Function.Injective φ ∧
      LinearMap.range φ = eig (1 : Representation K Unit K) ⊤ (fun _ => (1 : 𝓞 K)) ⊓ ⊤ ∧
      Mj.map (φ.restrictScalars (𝓞 K)) =
        cut (eig (1 : Representation K Unit K) ⊤ (fun _ => (1 : 𝓞 K)) ⊓ ⊤) (unitLat K) ∧
      Mj.map (φ.restrictScalars (𝓞 K)) =
        (((unitLat K).map ((LinearMap.id : K →ₗ[K] K).restrictScalars (𝓞 K))).map
          ((LinearMap.id : K →ₗ[K] K).restrictScalars (𝓞 K))).map
            ((LinearMap.id : K →ₗ[K] K).restrictScalars (𝓞 K)) ∧
      (idx w Mj Mj : ℝ) ≤ 0 := by
  have hcut : cut (eig (1 : Representation K Unit K) ⊤ (fun _ => (1 : 𝓞 K)) ⊓ ⊤) (unitLat K) = unitLat K := by
    unfold cut
    rw [eig_trivial K]
    simp
  refine ⟨(LinearEquiv.funUnique (Fin 1) K K).toLinearMap,
    (unitLat K).comap ((LinearEquiv.funUnique (Fin 1) K K).toLinearMap.restrictScalars (𝓞 K)),
    (LinearEquiv.funUnique (Fin 1) K K).injective, ?_, ?_, ?_, ?_⟩
  · rw [eig_trivial K, inf_top_eq]
    exact LinearEquiv.range _
  · rw [Submodule.map_comap_eq_of_surjective
      (f := (LinearEquiv.funUnique (Fin 1) K K).toLinearMap.restrictScalars (𝓞 K))
      (LinearEquiv.funUnique (Fin 1) K K).surjective, hcut]
  · rw [Submodule.map_comap_eq_of_surjective
      (f := (LinearEquiv.funUnique (Fin 1) K K).toLinearMap.restrictScalars (𝓞 K))
      (LinearEquiv.funUnique (Fin 1) K K).surjective, map_id_restrict K,
      map_id_restrict K, map_id_restrict K]
  · unfold idx Formalism.HermitianLatticesTheory.lidx
    simp

end Instance

end Formalism.EigenvalueLevelCeiling
