import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorPowUpperVanishHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoefExtendsHolomorphically
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothCycOfKFinSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlRelationsOnKFiniteVectorsStatement
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

noncomputable section

namespace GlobalTheory.StdInfChar

/- English proof (translation)
Establish `hsucc : ∀ i : ℕ, LinearMap.range (φ ^ (i + 1)) = (LinearMap.range (φ ^ i)).map φ` using `fun i => by`. Rewrite using `[pow_succ', Module.End.mul_eq_comp, LinearMap.range_comp]`. Establish `hle : ∀ i : ℕ, LinearMap.range (φ ^ (i + 1)) ≤ LinearMap.range (φ ^ i)` using `fun i => by`. Rewrite using `[pow_succ, Module.End.mul_eq_comp]`. Conclude with `LinearMap.range_comp_le_range _ _`.

Choose the witnesses or unpack the hypotheses as in `⟨N, hN⟩ : ∃ N : ℕ, LinearMap.range (φ ^ (N + 1)) = LinearMap.range (φ ^ N) := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `ha : StrictAnti fun i : ℕ => LinearMap.range (φ ^ i)` using `strictAnti_nat_of_succ_lt fun i => lt_of_le_of_ne (hle i) (h i)`. Use `hl (l + 1) (fun i => LinearMap.range (φ ^ (l + 1 - i.val))) (fun i => hS _) fun i j hij => ha (by have := j.2; have : i.val < j.val := hij; omega)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hst : ∀ m : ℕ, LinearMap.range (φ ^ (N + m)) = LinearMap.range (φ ^ N)` using `fun m => by`. Proceed by induction on `m with`. Consider the case `zero => rfl`. Consider the case `succ m ih => rw [← add_assoc, hsucc, ih, ← hsucc, hN]`.

Use `⟨N, eq_top_iff.2 fun v _ => ?_⟩` and prove the remaining obligations. Establish `: (φ ^ (N + 1)) v ∈ LinearMap.range (φ ^ (N + (N + 2)))`. Rewrite using `[hst, ← hN]`. Conclude with `⟨v, rfl⟩`. Take `⟨w, hw⟩` from `this`.

Use `Submodule.mem_sup.2 ⟨v - (φ ^ (N + 1)) w, ?_, _, ⟨w, rfl⟩, sub_add_cancel _ _⟩` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, map_sub, ← hw, ← Module.End.mul_apply, ← pow_add, show N + 1 + (N + 1) = N + (N + 2) by omega, sub_self]`.
-/
theorem exists_ker_sup_range {M : Type} [AddCommGroup M] [Module ℂ M] (φ : Module.End ℂ M)
    (S : Submodule ℂ M → Prop) (hS : ∀ i : ℕ, S (LinearMap.range (φ ^ i))) (l : ℕ)
    (hl : ∀ (r : ℕ) (Y : Fin (r + 1) → Submodule ℂ M), (∀ i, S (Y i)) → StrictMono Y → r ≤ l) :
    ∃ N : ℕ, LinearMap.ker (φ ^ (N + 1)) ⊔ LinearMap.range (φ ^ (N + 1)) = ⊤ := by
  have hsucc : ∀ i : ℕ, LinearMap.range (φ ^ (i + 1)) = (LinearMap.range (φ ^ i)).map φ := fun i => by
    rw [pow_succ', Module.End.mul_eq_comp, LinearMap.range_comp]
  have hle : ∀ i : ℕ, LinearMap.range (φ ^ (i + 1)) ≤ LinearMap.range (φ ^ i) := fun i => by
    rw [pow_succ, Module.End.mul_eq_comp]
    exact LinearMap.range_comp_le_range _ _
  obtain ⟨N, hN⟩ : ∃ N : ℕ, LinearMap.range (φ ^ (N + 1)) = LinearMap.range (φ ^ N) := by
    by_contra h
    push Not at h
    have ha : StrictAnti fun i : ℕ => LinearMap.range (φ ^ i) :=
      strictAnti_nat_of_succ_lt fun i => lt_of_le_of_ne (hle i) (h i)
    have := hl (l + 1) (fun i => LinearMap.range (φ ^ (l + 1 - i.val))) (fun i => hS _) fun i j hij =>
      ha (by have := j.2; have : i.val < j.val := hij; omega)
    omega
  have hst : ∀ m : ℕ, LinearMap.range (φ ^ (N + m)) = LinearMap.range (φ ^ N) := fun m => by
    induction m with
    | zero => rfl
    | succ m ih => rw [← add_assoc, hsucc, ih, ← hsucc, hN]
  refine ⟨N, eq_top_iff.2 fun v _ => ?_⟩
  have : (φ ^ (N + 1)) v ∈ LinearMap.range (φ ^ (N + (N + 2))) := by
    rw [hst, ← hN]; exact ⟨v, rfl⟩
  obtain ⟨w, hw⟩ := this
  refine Submodule.mem_sup.2 ⟨v - (φ ^ (N + 1)) w, ?_, _, ⟨w, rfl⟩, sub_add_cancel _ _⟩
  rw [LinearMap.mem_ker, map_sub, ← hw, ← Module.End.mul_apply, ← pow_add,
    show N + 1 + (N + 1) = N + (N + 2) by omega, sub_self]

variable {n : ℕ} {ε : Fin n → Bool}

/- English proof (translation)
Establish `hJ` using `Jm_mul_self ε`. Establish `hJ' : ∀ B : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * B) = B` using `fun B => by`. Rewrite using `[← mul_assoc, hJ, one_mul]`. Use `⟨(1 / 2 : ℂ) • (Y - Jm ε * Yᴴ * Jm ε), ?_, (-Complex.I / 2) • (Y + Jm ε * Yᴴ * Jm ε), ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ᴴ * Jm ε + Jm ε * _ = 0`.

Simplify using `only [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, Jm_conjTranspose, conjTranspose_conjTranspose, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, mul_assoc, hJ, hJ', mul_one]`. Establish `: star (1 / 2 : ℂ) = 1 / 2` using `by simp`. Rewrite using `[this]`. Use `module`. Express the relevant statement in the definitionally equal form `_ᴴ * Jm ε + Jm ε * _ = 0`.

Simplify using `only [conjTranspose_smul, conjTranspose_add, conjTranspose_mul, Jm_conjTranspose, conjTranspose_conjTranspose, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, mul_assoc, hJ, hJ', mul_one]`. Establish `: star (-Complex.I / 2 : ℂ) = Complex.I / 2` using `by simp`. Rewrite using `[this]`. Use `module`. Rewrite using `[smul_smul, show Complex.I * (-Complex.I / 2) = 1 / 2 by`.

Take the linear combination `(-1 / 2 : ℂ) * Complex.I_mul_I]`. Use `module`.
-/
theorem exists_lieSet_add (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    ∃ X₁ ∈ lieSet ε, ∃ X₂ ∈ lieSet ε, Y = X₁ + Complex.I • X₂ := by
  have hJ := Jm_mul_self ε
  have hJ' : ∀ B : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * B) = B := fun B => by
    rw [← mul_assoc, hJ, one_mul]
  refine ⟨(1 / 2 : ℂ) • (Y - Jm ε * Yᴴ * Jm ε), ?_, (-Complex.I / 2) • (Y + Jm ε * Yᴴ * Jm ε), ?_, ?_⟩
  · change _ᴴ * Jm ε + Jm ε * _ = 0
    simp only [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, Jm_conjTranspose,
      conjTranspose_conjTranspose, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, mul_assoc, hJ, hJ', mul_one]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this]
    module
  · change _ᴴ * Jm ε + Jm ε * _ = 0
    simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_mul, Jm_conjTranspose,
      conjTranspose_conjTranspose, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, mul_assoc, hJ, hJ', mul_one]
    have : star (-Complex.I / 2 : ℂ) = Complex.I / 2 := by simp
    rw [this]
    module
  · rw [smul_smul, show Complex.I * (-Complex.I / 2) = 1 / 2 by
      linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I]
    module

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

/- English proof (translation)
Establish `hKU : ∀ k : KG ε, toMK k ∈ UJset ε` using `fun k => (maximal_compact_facts n ε).1 _ k.2`. Establish `hc : ∀ x : H, Continuous (fun k : KG ε => σ (toMK k) x)` using `fun x => (hcont x).comp_continuous (GlobalTheory.KHolExt.isEmb ε).continuous hKU`. Establish `hint : ∀ {E : Type} [NormedAddCommGroup E] {G : KG ε → E}, Continuous G → Integrable G (muK ε)` using `fun hG => integrableOn_univ.1 (hG.continuousOn.integrableOn_compact isCompact_univ)`. Take `⟨x, hx⟩` from `exists_ne (0 : H)`. Establish `h1 : σ (toMK (1 : KG ε)) = 1` using `hσ.1`.

Establish `hex : ∃ p : C(KG ε, ℂ), GlobalTheory.KHolExt.Sep ε p ∧ ∫ k, p k • σ (toMK k) x ∂(muK ε) ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `h0` using `GlobalTheory.KHolExt.eq_zero_of_orth (ε := ε) ⟨fun k => ⟪x, σ (toMK k) x⟫_ℂ, continuous_const.inner (hc x)⟩ (fun p hp => by`. Establish `hi : Integrable (fun k => p k • σ (toMK k) x) (muK ε)` using `hint (p.continuous.smul (hc x))`.

Establish `h2` using `integral_inner (𝕜 := ℂ) hi x`. Rewrite `h2` using `[hcon p hp, inner_zero_right]`. Simplify `h2)` using `only [inner_smul_right, ContinuousMap.coe_mk]`. Establish `h3 : ⟪x, σ (toMK (1 : KG ε)) x⟫_ℂ = 0` using `congrArg (fun f : C(KG ε, ℂ) => f 1) h0`. Rewrite `h3` using `[h1]`.

Conclude with `hx (inner_self_eq_zero.1 h3)`. Take `⟨p, ⟨ι, _, a, b, -, h⟩, hp⟩` from `hex`. Use `set s := ∫ k, p k • σ (toMK k) x ∂(muK ε) with hs`. Establish `hL : ∀ g : KG ε, σ (toMK g) s ∈ Submodule.span ℂ (Set.range fun i => ∫ k, b i k • σ (toMK k) x ∂(muK ε))`. Introduce `g`.

Establish `hi : Integrable (fun k => p k • σ (toMK k) x) (muK ε)` using `hint (p.continuous.smul (hc x))`. Establish `e : σ (toMK g) s = ∑ i, a i g • ∫ k, b i k • σ (toMK k) x ∂(muK ε)`. Rewrite using `[hs, ← ContinuousLinearMap.integral_comp_comm _ hi]`. Establish `h2` using `integral_mul_left_eq_self (μ := muK ε) (fun k => p (g⁻¹ * k) • σ (toMK k) x) g`. Simplify using `only [inv_mul_cancel_left] at h2`.

Establish `h3 : ∀ k, σ (toMK g) (p k • σ (toMK k) x) = p k • σ (toMK (g * k)) x`. Introduce `k`. Rewrite using `[map_smul, GlobalTheory.KHolExt.toMK_mul, hσ.2 _ (hKU g) _ (hKU k)]`. Both sides reduce to the same expression. Simplify using `only [h3]`.

Rewrite using `[h2]`. Simplify using `only [h, Finset.sum_smul, mul_smul]`. Rewrite using `[integral_finsetSum]`. Conclude with `Finset.sum_congr rfl fun i _ => integral_smul _ _`. Introduce `i _`.

Conclude with `hint (continuous_const.smul ((b i).continuous.smul (hc x)))`. Rewrite using `[e]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Use `haveI := FiniteDimensional.span_of_finite ℂ (Set.finite_range fun i => ∫ k, b i k • σ (toMK k) x ∂(muK ε))`. Use `⟨s, hp, Submodule.span ℂ (Set.range fun g : KG ε => σ (toMK g) s), Submodule.finiteDimensional_of_le (Submodule.span_le.2 (Set.range_subset_iff.2 hL)), Submodule.subset_span ⟨1, by simp only [h1]; rfl⟩, fun k hk v hv => ?_⟩` and prove the remaining obligations.

Rewrite `hk` using `[← range_toMK]`. Take `⟨g, rfl⟩` from `hk`. Use `(Submodule.span_le (p := (Submodule.span ℂ (Set.range fun g : KG ε => σ (toMK g) s)).comap (σ (toMK g) : H →ₗ[ℂ] H))).2 ?_ hv` and prove the remaining obligations. Introduce and unpack `_ ⟨g', rfl⟩`. Use `Submodule.subset_span ⟨g * g', ?_⟩` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[GlobalTheory.KHolExt.toMK_mul, hσ.2 _ (hKU g) _ (hKU g')]`. Both sides reduce to the same expression.
-/
theorem exists_isKFin_ne_zero [CompleteSpace H] [Nontrivial H] (hσ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) σ)
    (hcont : ∀ v, ContinuousOn (fun g => σ g v) (UJset ε)) : ∃ s : H, s ≠ 0 ∧ IsKFin ε σ s := by
  have hKU : ∀ k : KG ε, toMK k ∈ UJset ε := fun k => (maximal_compact_facts n ε).1 _ k.2
  have hc : ∀ x : H, Continuous (fun k : KG ε => σ (toMK k) x) := fun x =>
    (hcont x).comp_continuous (GlobalTheory.KHolExt.isEmb ε).continuous hKU
  have hint : ∀ {E : Type} [NormedAddCommGroup E] {G : KG ε → E}, Continuous G → Integrable G (muK ε) :=
    fun hG => integrableOn_univ.1 (hG.continuousOn.integrableOn_compact isCompact_univ)
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  have h1 : σ (toMK (1 : KG ε)) = 1 := hσ.1
  have hex : ∃ p : C(KG ε, ℂ), GlobalTheory.KHolExt.Sep ε p ∧ ∫ k, p k • σ (toMK k) x ∂(muK ε) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 := GlobalTheory.KHolExt.eq_zero_of_orth (ε := ε)
      ⟨fun k => ⟪x, σ (toMK k) x⟫_ℂ, continuous_const.inner (hc x)⟩
      (fun p hp => by
        have hi : Integrable (fun k => p k • σ (toMK k) x) (muK ε) := hint (p.continuous.smul (hc x))
        have h2 := integral_inner (𝕜 := ℂ) hi x
        rw [hcon p hp, inner_zero_right] at h2
        simpa only [inner_smul_right, ContinuousMap.coe_mk] using h2)
    have h3 : ⟪x, σ (toMK (1 : KG ε)) x⟫_ℂ = 0 := congrArg (fun f : C(KG ε, ℂ) => f 1) h0
    rw [h1] at h3
    exact hx (inner_self_eq_zero.1 h3)
  obtain ⟨p, ⟨ι, _, a, b, -, h⟩, hp⟩ := hex
  set s := ∫ k, p k • σ (toMK k) x ∂(muK ε) with hs
  have hL : ∀ g : KG ε, σ (toMK g) s ∈
      Submodule.span ℂ (Set.range fun i => ∫ k, b i k • σ (toMK k) x ∂(muK ε)) := by
    intro g
    have hi : Integrable (fun k => p k • σ (toMK k) x) (muK ε) := hint (p.continuous.smul (hc x))
    have e : σ (toMK g) s = ∑ i, a i g • ∫ k, b i k • σ (toMK k) x ∂(muK ε) := by
      rw [hs, ← ContinuousLinearMap.integral_comp_comm _ hi]
      have h2 := integral_mul_left_eq_self (μ := muK ε) (fun k => p (g⁻¹ * k) • σ (toMK k) x) g
      simp only [inv_mul_cancel_left] at h2
      have h3 : ∀ k, σ (toMK g) (p k • σ (toMK k) x) = p k • σ (toMK (g * k)) x := by
        intro k
        rw [map_smul, GlobalTheory.KHolExt.toMK_mul, hσ.2 _ (hKU g) _ (hKU k)]
        rfl
      simp only [h3]
      rw [h2]
      simp only [h, Finset.sum_smul, mul_smul]
      rw [integral_finsetSum]
      · exact Finset.sum_congr rfl fun i _ => integral_smul _ _
      · intro i _
        exact hint (continuous_const.smul ((b i).continuous.smul (hc x)))
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI := FiniteDimensional.span_of_finite ℂ (Set.finite_range fun i => ∫ k, b i k • σ (toMK k) x ∂(muK ε))
  refine ⟨s, hp, Submodule.span ℂ (Set.range fun g : KG ε => σ (toMK g) s),
    Submodule.finiteDimensional_of_le (Submodule.span_le.2 (Set.range_subset_iff.2 hL)),
    Submodule.subset_span ⟨1, by simp only [h1]; rfl⟩, fun k hk v hv => ?_⟩
  rw [← range_toMK] at hk
  obtain ⟨g, rfl⟩ := hk
  refine (Submodule.span_le (p := (Submodule.span ℂ (Set.range fun g : KG ε => σ (toMK g) s)).comap
    (σ (toMK g) : H →ₗ[ℂ] H))).2 ?_ hv
  rintro _ ⟨g', rfl⟩
  refine Submodule.subset_span ⟨g * g', ?_⟩
  dsimp only
  rw [GlobalTheory.KHolExt.toMK_mul, hσ.2 _ (hKU g) _ (hKU g')]
  rfl

/- English proof (translation)
Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨v, -, rfl⟩`. Conclude with `hσ.smooth _ v.2`. Introduce and unpack `_ ⟨v, -, rfl⟩`. Conclude with `v.2`.

Introduce and unpack `κ hκ _ ⟨v, hv, rfl⟩`. Conclude with `⟨⟨_, hσ.kStable κ hκ _ v.2⟩, hK κ hκ v _ rfl hv, rfl⟩`. Introduce and unpack `X hX _ ⟨v, hv, rfl⟩`. Conclude with `⟨⟨_, hσ.lieStable X hX _ v.2⟩, hL X hX v _ rfl hv, rfl⟩`.
-/
theorem isGKSub_map (hσ : IsGKSub ε σ (kFinVec ε σ)) (Y : Submodule ℂ (kFinVec ε σ))
    (hK : ∀ κ ∈ Kset ε, ∀ v w : kFinVec ε σ, (w : H) = σ κ v → v ∈ Y → w ∈ Y)
    (hL : ∀ X ∈ lieSet ε, ∀ v w : kFinVec ε σ, (w : H) = dRep σ X v → v ∈ Y → w ∈ Y) :
    IsGKSub ε σ (Y.map (kFinVec ε σ).subtype) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨v, -, rfl⟩
    exact hσ.smooth _ v.2
  · rintro _ ⟨v, -, rfl⟩
    exact v.2
  · rintro κ hκ _ ⟨v, hv, rfl⟩
    exact ⟨⟨_, hσ.kStable κ hκ _ v.2⟩, hK κ hκ v _ rfl hv, rfl⟩
  · rintro X hX _ ⟨v, hv, rfl⟩
    exact ⟨⟨_, hσ.lieStable X hX _ v.2⟩, hL X hX v _ rfl hv, rfl⟩

/- English proof (translation)
Establish `h0 : ∀ X, dRep σ X 0 = 0` using `fun X => by simp [dRep]`. Use `⟨isGKSub_map hσ _ (fun κ hκ v w e hv => Subtype.ext ?_) (fun X hX v w e hv => Subtype.ext ?_), isGKSub_map hσ _ ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[hφ.1 κ hκ v w e, LinearMap.mem_ker.1 hv]`. Simplify using the standard rewrite rules. Rewrite using `[hφ.2 X hX v w e, LinearMap.mem_ker.1 hv]`.

Simplify using `[h0]`. Introduce and unpack `κ hκ _ w e ⟨v, rfl⟩`. Conclude with `⟨⟨_, hσ.kStable κ hκ _ v.2⟩, Subtype.ext ((hφ.1 κ hκ v _ rfl).trans e.symm)⟩`. Introduce and unpack `X hX _ w e ⟨v, rfl⟩`. Conclude with `⟨⟨_, hσ.lieStable X hX _ v.2⟩, Subtype.ext ((hφ.2 X hX v _ rfl).trans e.symm)⟩`.
-/
theorem isGKSub_ker_range (hσ : IsGKSub ε σ (kFinVec ε σ)) {φ : Module.End ℂ (kFinVec ε σ)}
    (hφ : IsGKHom ε σ σ φ) : IsGKSub ε σ ((LinearMap.ker φ).map (kFinVec ε σ).subtype) ∧
      IsGKSub ε σ ((LinearMap.range φ).map (kFinVec ε σ).subtype) := by
  have h0 : ∀ X, dRep σ X 0 = 0 := fun X => by simp [dRep]
  refine ⟨isGKSub_map hσ _ (fun κ hκ v w e hv => Subtype.ext ?_) (fun X hX v w e hv => Subtype.ext ?_),
    isGKSub_map hσ _ ?_ ?_⟩
  · rw [hφ.1 κ hκ v w e, LinearMap.mem_ker.1 hv]; simp
  · rw [hφ.2 X hX v w e, LinearMap.mem_ker.1 hv]; simp [h0]
  · rintro κ hκ _ w e ⟨v, rfl⟩
    exact ⟨⟨_, hσ.kStable κ hκ _ v.2⟩, Subtype.ext ((hφ.1 κ hκ v _ rfl).trans e.symm)⟩
  · rintro X hX _ w e ⟨v, rfl⟩
    exact ⟨⟨_, hσ.lieStable X hX _ v.2⟩, Subtype.ext ((hφ.2 X hX v _ rfl).trans e.symm)⟩

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => exact isGKHom_id ε σ`. Consider the case `succ i ih`. Rewrite using `[pow_succ']`. Conclude with `⟨fun κ hκ v w e => hφ.1 κ hκ _ _ (ih.1 κ hκ v w e), fun X hX v w e => hφ.2 X hX _ _ (ih.2 X hX v w e)⟩`.
-/
theorem isGKHom_pow {φ : Module.End ℂ (kFinVec ε σ)} (hφ : IsGKHom ε σ σ φ) (i : ℕ) : IsGKHom ε σ σ (φ ^ i) := by
  induction i with
  | zero => exact isGKHom_id ε σ
  | succ i ih =>
    rw [pow_succ']
    exact ⟨fun κ hκ v w e => hφ.1 κ hκ _ _ (ih.1 κ hκ v w e), fun X hX v w e => hφ.2 X hX _ _ (ih.2 X hX v w e)⟩

/- English proof (translation)
Establish `: ∀ a b v, T (epow E k a b v) = epow E' k a b (T v)`. Proceed by induction on `k with`. Consider the case `zero => intro a b v; simp only [epow]; split_ifs <;> simp`. Consider the case `succ k ih => intro a b v`. Simplify using `only [epow, LinearMap.sum_apply, map_sum, Module.End.mul_apply, ih, h]`.

Simplify using `only [etr, LinearMap.sum_apply, map_sum, this]`.
-/
theorem map_etr {M M' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] (T : M →ₗ[ℂ] M')
    {E : Fin n → Fin n → Module.End ℂ M} {E' : Fin n → Fin n → Module.End ℂ M'}
    (h : ∀ a b v, T (E a b v) = E' a b (T v)) (k : ℕ) (v : M) : T (etr E k v) = etr E' k (T v) := by
  have : ∀ a b v, T (epow E k a b v) = epow E' k a b (T v) := by
    induction k with
    | zero => intro a b v; simp only [epow]; split_ifs <;> simp
    | succ k ih => intro a b v; simp only [epow, LinearMap.sum_apply, map_sum, Module.End.mul_apply, ih, h]
  simp only [etr, LinearMap.sum_apply, map_sum, this]

/- English proof (translation)
Establish `: ∀ a b, f (epow E k a b) = epow (fun a b => f (E a b)) k a b`. Proceed by induction on `k with`. Consider the case `zero => intro a b; simp only [epow]; split_ifs <;> simp`. Consider the case `succ k ih => intro a b`. Simplify using `only [epow, map_sum, map_mul, ih]`.

Simplify using `only [etr, map_sum, this]`.
-/
theorem ringHom_etr {A B : Type} [Ring A] [Ring B] (f : A →+* B) (E : Fin n → Fin n → A) (k : ℕ) :
    f (etr E k) = etr (fun a b => f (E a b)) k := by
  have : ∀ a b, f (epow E k a b) = epow (fun a b => f (E a b)) k a b := by
    induction k with
    | zero => intro a b; simp only [epow]; split_ifs <;> simp
    | succ k ih => intro a b; simp only [epow, map_sum, map_mul, ih]
  simp only [etr, map_sum, this]

/- English proof (translation)
Introduce `hL n ε V _ _ _ π hπ hsm χ hχ I hI Z hF k v hv`. Take `⟨hadm, ⟨l, hl⟩, hGK, -⟩` from `hL.1 n ε I`. Take `⟨ν, hν⟩` from `GlobalTheory.Published.Langlands.exists_isHaarSub_nbar I.toDatum`. Take `⟨-, -, Z₀, -, hZg, hZ₀, hmax, -⟩` from `hL.2.1 n ε I hI ν hν`. Take `⟨-, -, -, T, hT, -, -, hTL⟩` from `hF`.

Establish `hTm : ∀ w ∈ kFinVec ε I.ρ, T w ∈ kFinVec ε π` using `fun w hw => hT ▸ Submodule.mem_map_of_mem hw`. Establish `hGK' : IsGKSub ε π (kFinVec ε π)`. Use `⟨fun w hw => GlobalTheory.SmoothCyclicApprox.smoothVec_of_smoothOnH (IsUnit.of_mul_eq_one _ (Jm_mul_self ε)) (hsm w hw), fun w hw => hw, isKStableOn_kFinVec ε π, fun X hX w hw => ?_⟩` and prove the remaining obligations. Rewrite `hw` using `[← hT]`. Take `⟨u, hu, rfl⟩` from `hw`.

Rewrite using `[← hTL X hX u hu]`. Conclude with `hTm _ (hGK.lieStable X hX u hu)`. Take `⟨A, hA, hP, hact, hK, -⟩` from `GlobalTheory.T.gl_relations_on_k_finite_vectors n ε I.H I.ρ hadm hGK`. Take `⟨A', hA', -, -, -, hχ'⟩` from `GlobalTheory.T.gl_relations_on_k_finite_vectors n ε V π hπ.2.1 hGK'`. Use `set E : Fin n → Fin n → Module.End ℂ (kFinVec ε I.ρ) := fun a b => A (Matrix.single a b 1) with hE`.

Establish `hgl : GlRel E` using `by simpa using (hP 1 isUnit_one).1`. Use `set c := gelfVal χ (k + 1)`. Use `set φ : Module.End ℂ (kFinVec ε I.ρ) := etr E (k + 1) - algebraMap ℂ _ c with hφ`. Establish `hφv : ∀ u, φ u = etr E (k + 1) u - c • u` using `fun u => by simp [hφ]`. Establish `hcomm : ∀ X u, etr E (k + 1) (A X u) = A X (etr E (k + 1) u)` using `fun X u => by`.

Establish `h1 : A X = ∑ a, ∑ b, X a b • E a b` using `by conv_lhs => rw [Matrix.matrix_eq_sum_single X]`. Simplify using `only [map_sum, hE, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]`. Establish `h2` using `fun a b u => LinearMap.congr_fun (generatorTraceCentral_holds _ n E hgl (k + 1) a b) u`. Simplify using `only [Module.End.mul_apply] at h2`. Simplify using `only [h1, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h2]`.

Establish `hhom : IsGKHom ε I.ρ I.ρ φ`. Use `⟨fun κ hκ u w e => ?_, fun X hX u w e => ?_⟩` and prove the remaining obligations. Simplify using `only [hφv, Submodule.coe_sub, Submodule.coe_smul, map_sub, map_smul, hK κ hκ (k + 1) u w e, e]`. Take `rfl : w = A X u` from `Subtype.ext (e.trans (hA X hX u).symm)`. Rewrite using `[← hA X hX, hφv, hφv, hcomm, map_sub, map_smul]`.

Set `T' : kFinVec ε I.ρ →ₗ[ℂ] kFinVec ε π` to `T.restrict hTm`. Establish `hTA : ∀ Y u, T' (A Y u) = A' Y (T' u)` using `fun Y u => by`. Establish `h1 : ∀ X ∈ lieSet ε, T' (A X u) = A' X (T' u)` using `fun X hX => Subtype.ext (by`. Rewrite using `[hA' X hX]`. Express the relevant statement in the definitionally equal form `T (A X u) = dRep π X (T u)`.

Rewrite using `[hA X hX, hTL X hX _ u.2])`. Take `⟨X₁, h₁, X₂, h₂, rfl⟩` from `exists_lieSet_add ε Y`. Simplify using `only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, h1 _ h₁, h1 _ h₂]`. Establish `hTφ : ∀ u, T' (φ u) = 0` using `fun u => by`. Rewrite using `[hφv, map_sub, map_smul, map_etr T' (fun a b u => hTA _ u), hχ' χ hχ, sub_self]`.

Take `⟨N, hN⟩` from `exists_ker_sup_range φ (fun Y => IsGKSub ε I.ρ (Y.map (kFinVec ε I.ρ).subtype)) (fun i => (isGKSub_ker_range hGK (isGKHom_pow hhom i)).2) l fun r Y hY hm => hl r _ hY ((Submodule.map_strictMono_of_injective (kFinVec ε I.ρ).injective_subtype).comp hm)`. Take `⟨hker, hran⟩` from `isGKSub_ker_range hGK (isGKHom_pow hhom (N + 1))`. Establish `hran' : (LinearMap.range (φ ^ (N + 1))).map (kFinVec ε I.ρ).subtype ≤ Z₀`. Use `(hmax _ hran).resolve_left fun e => ?_` and prove the remaining obligations. Use `haveI := hπ.1`.

Take `⟨s, hs0, hs⟩` from `exists_isKFin_ne_zero hπ.2.1.1 hπ.2.1.2.1`. Establish `: s ∈ (kFinVec ε I.ρ).map T` using `hT ▸ hs`. Take `⟨u, hu, rfl⟩` from `this`. Rewrite `hu` using `[← e]`. Take `⟨_, ⟨w, rfl⟩, rfl⟩` from `hu`.

Rewrite `hs0` using `[pow_succ']`. Conclude with `hs0 (congrArg Subtype.val (hTφ _))`. Establish `hker' : (LinearMap.ker (φ ^ (N + 1))).map (kFinVec ε I.ρ).subtype = kFinVec ε I.ρ`. Use `(hmax _ hker).resolve_right fun e => hZ₀ (le_antisymm (fun w hw => hZg.kFin w hw) ?_)` and prove the remaining obligations. Use `sup_le e hran'` as an intermediate fact.

Rewrite `this` using `[← Submodule.map_sup, hN, Submodule.map_subtype_top]`. Then use the resulting hypothesis. Use `⟨N + 1, ?_⟩` and prove the remaining obligations. Establish `hv' : v ∈ (LinearMap.ker (φ ^ (N + 1))).map (kFinVec ε I.ρ).subtype` using `hker'.symm ▸ hv`. Take `⟨u, hu, rfl⟩` from `hv'`. Rewrite using `[Submodule.subtype_apply, hact, map_pow, map_sub, AlgHom.commutes]`.

Use `ringHom_etr (FreeAlgebra.lift ℂ (fun ab : Fin n × Fin n => A (Matrix.single ab.1 ab.2 1))).toRingHom (Egl n) (k + 1)` as an intermediate fact. Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Egl, FreeAlgebra.lift_ι_apply] at this`. Use `erw [this]`. Conclude with `congrArg Subtype.val (LinearMap.mem_ker.1 hu)`.
-/
theorem genInfChar_of_isFactor : GlobalTheory.Published.LanglandsClassification → ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsIrrAdm ε π → (∀ v, IsKFin ε π v → Formalism.QuantumDeterminants.SmoothOnH (Jm ε) (fun g => π g v)) → ∀ χ : Fin n → ℂ, HasInfChar ε χ π → ∀ I : IndModule ε, I.Positive → ∀ Z, IsFactor ε I.ρ Z (kFinVec ε I.ρ) π → (∀ (k : ℕ) v, IsKFin ε I.ρ v → ∃ N : ℕ, actU ε I.ρ ((etr (Egl n) (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1))) ^ N) v = 0) := by
  intro hL n ε V _ _ _ π hπ hsm χ hχ I hI Z hF k v hv
  obtain ⟨hadm, ⟨l, hl⟩, hGK, -⟩ := hL.1 n ε I
  obtain ⟨ν, hν⟩ := GlobalTheory.Published.Langlands.exists_isHaarSub_nbar I.toDatum
  obtain ⟨-, -, Z₀, -, hZg, hZ₀, hmax, -⟩ := hL.2.1 n ε I hI ν hν
  obtain ⟨-, -, -, T, hT, -, -, hTL⟩ := hF
  have hTm : ∀ w ∈ kFinVec ε I.ρ, T w ∈ kFinVec ε π := fun w hw => hT ▸ Submodule.mem_map_of_mem hw
  have hGK' : IsGKSub ε π (kFinVec ε π) := by
    refine ⟨fun w hw => GlobalTheory.SmoothCyclicApprox.smoothVec_of_smoothOnH
      (IsUnit.of_mul_eq_one _ (Jm_mul_self ε)) (hsm w hw), fun w hw => hw, isKStableOn_kFinVec ε π,
      fun X hX w hw => ?_⟩
    rw [← hT] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    rw [← hTL X hX u hu]
    exact hTm _ (hGK.lieStable X hX u hu)
  obtain ⟨A, hA, hP, hact, hK, -⟩ := GlobalTheory.T.gl_relations_on_k_finite_vectors n ε I.H I.ρ hadm hGK
  obtain ⟨A', hA', -, -, -, hχ'⟩ := GlobalTheory.T.gl_relations_on_k_finite_vectors n ε V π hπ.2.1 hGK'
  set E : Fin n → Fin n → Module.End ℂ (kFinVec ε I.ρ) := fun a b => A (Matrix.single a b 1) with hE
  have hgl : GlRel E := by simpa using (hP 1 isUnit_one).1
  set c := gelfVal χ (k + 1)
  set φ : Module.End ℂ (kFinVec ε I.ρ) := etr E (k + 1) - algebraMap ℂ _ c with hφ
  have hφv : ∀ u, φ u = etr E (k + 1) u - c • u := fun u => by simp [hφ]

  have hcomm : ∀ X u, etr E (k + 1) (A X u) = A X (etr E (k + 1) u) := fun X u => by
    have h1 : A X = ∑ a, ∑ b, X a b • E a b := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single X]
      simp only [map_sum, hE, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
    have h2 := fun a b u => LinearMap.congr_fun (generatorTraceCentral_holds _ n E hgl (k + 1) a b) u
    simp only [Module.End.mul_apply] at h2
    simp only [h1, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h2]
  have hhom : IsGKHom ε I.ρ I.ρ φ := by
    refine ⟨fun κ hκ u w e => ?_, fun X hX u w e => ?_⟩
    · simp only [hφv, Submodule.coe_sub, Submodule.coe_smul, map_sub, map_smul, hK κ hκ (k + 1) u w e, e]
    · obtain rfl : w = A X u := Subtype.ext (e.trans (hA X hX u).symm)
      rw [← hA X hX, hφv, hφv, hcomm, map_sub, map_smul]

  let T' : kFinVec ε I.ρ →ₗ[ℂ] kFinVec ε π := T.restrict hTm
  have hTA : ∀ Y u, T' (A Y u) = A' Y (T' u) := fun Y u => by
    have h1 : ∀ X ∈ lieSet ε, T' (A X u) = A' X (T' u) := fun X hX => Subtype.ext (by
      rw [hA' X hX]
      change T (A X u) = dRep π X (T u)
      rw [hA X hX, hTL X hX _ u.2])
    obtain ⟨X₁, h₁, X₂, h₂, rfl⟩ := exists_lieSet_add ε Y
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, h1 _ h₁, h1 _ h₂]
  have hTφ : ∀ u, T' (φ u) = 0 := fun u => by
    rw [hφv, map_sub, map_smul, map_etr T' (fun a b u => hTA _ u), hχ' χ hχ, sub_self]
  obtain ⟨N, hN⟩ := exists_ker_sup_range φ (fun Y => IsGKSub ε I.ρ (Y.map (kFinVec ε I.ρ).subtype))
    (fun i => (isGKSub_ker_range hGK (isGKHom_pow hhom i)).2) l fun r Y hY hm =>
      hl r _ hY ((Submodule.map_strictMono_of_injective (kFinVec ε I.ρ).injective_subtype).comp hm)
  obtain ⟨hker, hran⟩ := isGKSub_ker_range hGK (isGKHom_pow hhom (N + 1))
  have hran' : (LinearMap.range (φ ^ (N + 1))).map (kFinVec ε I.ρ).subtype ≤ Z₀ := by
    refine (hmax _ hran).resolve_left fun e => ?_
    haveI := hπ.1
    obtain ⟨s, hs0, hs⟩ := exists_isKFin_ne_zero hπ.2.1.1 hπ.2.1.2.1
    have : s ∈ (kFinVec ε I.ρ).map T := hT ▸ hs
    obtain ⟨u, hu, rfl⟩ := this
    rw [← e] at hu
    obtain ⟨_, ⟨w, rfl⟩, rfl⟩ := hu
    rw [pow_succ'] at hs0
    exact hs0 (congrArg Subtype.val (hTφ _))
  have hker' : (LinearMap.ker (φ ^ (N + 1))).map (kFinVec ε I.ρ).subtype = kFinVec ε I.ρ := by
    refine (hmax _ hker).resolve_right fun e => hZ₀ (le_antisymm (fun w hw => hZg.kFin w hw) ?_)
    have := sup_le e hran'
    rwa [← Submodule.map_sup, hN, Submodule.map_subtype_top] at this
  refine ⟨N + 1, ?_⟩
  have hv' : v ∈ (LinearMap.ker (φ ^ (N + 1))).map (kFinVec ε I.ρ).subtype := hker'.symm ▸ hv
  obtain ⟨u, hu, rfl⟩ := hv'
  rw [Submodule.subtype_apply, hact, map_pow, map_sub, AlgHom.commutes]
  have := ringHom_etr (FreeAlgebra.lift ℂ (fun ab : Fin n × Fin n => A (Matrix.single ab.1 ab.2 1))).toRingHom
    (Egl n) (k + 1)
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Egl, FreeAlgebra.lift_ι_apply] at this
  erw [this]
  exact congrArg Subtype.val (LinearMap.mem_ker.1 hu)

end GlobalTheory.StdInfChar
