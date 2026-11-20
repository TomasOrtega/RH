import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormsEqZeroOfPeriodSubConjCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspidalOfEichlerPeriodSubConjMemCoboundariesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerPeriodCocycleMemCocyclesAndEqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraConjCocyclesCoboundariesPeriodSmulStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankEichlerShimuraCoboundariesOfGammaLeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankEichlerShimuraCocyclesLeGamma1Statement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddWeightModularCuspDimensionLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolyDegreeSlashActionRightActionPropertiesStatement

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.EichlerShimura

/- English proof (translation)
Establish `: FiniteDimensional ℂ B` using `Submodule.finiteDimensional_of_le hBZ`. Establish `hPs' : ∀ (r : ℝ) x, P (r • x) = (r : ℂ) • P x` using `fun r x => hPs r x`. Establish `hQs' : ∀ (r : ℝ) x, Q (r • x) = (r : ℂ) • Q x` using `fun r x => hQs r x`. Establish `hP0 : P 0 = 0` using `by simpa using hPa 0 0`. Establish `hQ0 : Q 0 = 0` using `by simpa using hQa 0 0`.

Set `Φ : (A × A') × B →ₗ[ℝ] Z` to `{ toFun := fun p => ⟨P p.1.1 + Q p.1.2 + (p.2 : V), Z.add_mem (Z.add_mem (hPZ _) (hQZ _)) (hBZ p.2.2)⟩ map_add' := fun p q => by`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `P (p.1.1 + q.1.1) + Q (p.1.2 + q.1.2) + ((p.2 : V) + q.2) = (P p.1.1 + Q p.1.2 + p.2) + (P q.1.1 + Q q.1.2 + q.2)`. Rewrite using `[hPa, hQa]`. Normalize the expressions using the abelian group laws.

Use the proof step `map_smul' := fun r p => by`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `P (r • p.1.1) + Q (r • p.1.2) + (r : ℂ) • (p.2 : V) = (r : ℂ) • (P p.1.1 + Q p.1.2 + p.2)`. Rewrite using `[hPs', hQs', smul_add, smul_add] }`. Establish `hΦ : Function.Injective Φ`.

Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce and unpack `⟨⟨x, y⟩, b⟩ h`. Establish `h' : P x + Q y + (b : V) = 0` using `congrArg Subtype.val h`. Establish `hmem : P x + Q y ∈ B`. Rewrite using `[eq_neg_of_add_eq_zero_left h']`.

Conclude with `B.neg_mem b.2`. Take `⟨rfl, rfl⟩` from `hinj x y hmem`. Establish `hb : b = 0` using `Subtype.ext (by simpa [hP0, hQ0] using h')`. Simplify using `[hb]`. Establish `hle : Module.finrank ℝ Z ≤ Module.finrank ℝ ((A × A') × B)`.

Establish `hZ : Module.finrank ℝ Z = 2 * Module.finrank ℂ Z` using `finrank_real_of_complex Z`. Establish `hA : Module.finrank ℝ A = 2 * Module.finrank ℂ A` using `finrank_real_of_complex A`. Establish `hA' : Module.finrank ℝ A' = 2 * Module.finrank ℂ A'` using `finrank_real_of_complex A'`. Establish `hB : Module.finrank ℝ B = 2 * Module.finrank ℂ B` using `finrank_real_of_complex B`. Rewrite using `[Module.finrank_prod, Module.finrank_prod, hZ, hA, hA', hB]`.

Use linear arithmetic over natural numbers and integers. Establish `hsurj` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (le_antisymm (LinearMap.finrank_le_finrank_of_injective hΦ) hle)).1 hΦ`. Introduce `z hz`. Take `⟨⟨⟨x, y⟩, b⟩, hp⟩` from `hsurj ⟨z, hz⟩`. Use `⟨x, y, ?_⟩` and prove the remaining obligations.

Establish `hz' : P x + Q y + (b : V) = z` using `congrArg Subtype.val hp`. Establish `: z - P x - Q y = b` using `by rw [← hz']; abel`. Rewrite using `[this]`. Conclude with `b.2`.
-/
theorem exists_of_finrank_le {A A' V : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ A] [FiniteDimensional ℂ A']
    (Z B : Submodule ℂ V) [FiniteDimensional ℂ Z] (hBZ : B ≤ Z) (P : A → V) (Q : A' → V)
    (hPa : ∀ x y, P (x + y) = P x + P y) (hQa : ∀ x y, Q (x + y) = Q x + Q y)
    (hPs : ∀ (r : ℝ) x, P ((r : ℂ) • x) = (r : ℂ) • P x) (hQs : ∀ (r : ℝ) x, Q ((r : ℂ) • x) = (r : ℂ) • Q x)
    (hPZ : ∀ x, P x ∈ Z) (hQZ : ∀ x, Q x ∈ Z)
    (hinj : ∀ x y, P x + Q y ∈ B → x = 0 ∧ y = 0)
    (hdim : Module.finrank ℂ Z ≤ Module.finrank ℂ A + Module.finrank ℂ A' + Module.finrank ℂ B) :
    ∀ z ∈ Z, ∃ x y, z - P x - Q y ∈ B := by
  classical
  have : FiniteDimensional ℂ B := Submodule.finiteDimensional_of_le hBZ
  have hPs' : ∀ (r : ℝ) x, P (r • x) = (r : ℂ) • P x := fun r x => hPs r x
  have hQs' : ∀ (r : ℝ) x, Q (r • x) = (r : ℂ) • Q x := fun r x => hQs r x
  have hP0 : P 0 = 0 := by simpa using hPa 0 0
  have hQ0 : Q 0 = 0 := by simpa using hQa 0 0
  let Φ : (A × A') × B →ₗ[ℝ] Z :=
    { toFun := fun p => ⟨P p.1.1 + Q p.1.2 + (p.2 : V),
        Z.add_mem (Z.add_mem (hPZ _) (hQZ _)) (hBZ p.2.2)⟩
      map_add' := fun p q => by
        apply Subtype.ext
        change P (p.1.1 + q.1.1) + Q (p.1.2 + q.1.2) + ((p.2 : V) + q.2) =
          (P p.1.1 + Q p.1.2 + p.2) + (P q.1.1 + Q q.1.2 + q.2)
        rw [hPa, hQa]
        abel
      map_smul' := fun r p => by
        apply Subtype.ext
        change P (r • p.1.1) + Q (r • p.1.2) + (r : ℂ) • (p.2 : V) =
          (r : ℂ) • (P p.1.1 + Q p.1.2 + p.2)
        rw [hPs', hQs', smul_add, smul_add] }
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨x, y⟩, b⟩ h
    have h' : P x + Q y + (b : V) = 0 := congrArg Subtype.val h
    have hmem : P x + Q y ∈ B := by
      rw [eq_neg_of_add_eq_zero_left h']
      exact B.neg_mem b.2
    obtain ⟨rfl, rfl⟩ := hinj x y hmem
    have hb : b = 0 := Subtype.ext (by simpa [hP0, hQ0] using h')
    simp [hb]
  have hle : Module.finrank ℝ Z ≤ Module.finrank ℝ ((A × A') × B) := by
    have hZ : Module.finrank ℝ Z = 2 * Module.finrank ℂ Z := finrank_real_of_complex Z
    have hA : Module.finrank ℝ A = 2 * Module.finrank ℂ A := finrank_real_of_complex A
    have hA' : Module.finrank ℝ A' = 2 * Module.finrank ℂ A' := finrank_real_of_complex A'
    have hB : Module.finrank ℝ B = 2 * Module.finrank ℂ B := finrank_real_of_complex B
    rw [Module.finrank_prod, Module.finrank_prod, hZ, hA, hA', hB]
    omega
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (le_antisymm (LinearMap.finrank_le_finrank_of_injective hΦ) hle)).1 hΦ
  intro z hz
  obtain ⟨⟨⟨x, y⟩, b⟩, hp⟩ := hsurj ⟨z, hz⟩
  refine ⟨x, y, ?_⟩
  have hz' : P x + Q y + (b : V) = z := congrArg Subtype.val hp
  have : z - P x - Q y = b := by rw [← hz']; abel
  rw [this]
  exact b.2

/- English proof (translation)
Introduce `z hz`. Take `⟨p, rfl⟩` from `LinearMap.mem_range.1 hz`. Establish `hp : (p : ℂ[X]) ∈ degreeLT ℂ (w + 1)` using `p.2`. Use `⟨fun γ => ?_, fun γ δ => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `slP w (mat γ) p - p ∈ degreeLT ℂ (w + 1)`.

Conclude with `Submodule.sub_mem _ (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w (mat γ) 1 p hp).1 hp`. Express the relevant statement in the definitionally equal form `slP w (mat ((γ * δ : Γ) : SL(2, ℤ))) p - p = slP w (mat δ) (slP w (mat γ) p - p) + (slP w (mat δ) p - p)`. Establish `hmat : mat ((γ * δ : Γ) : SL(2, ℤ)) = mat γ * mat δ` using `by simp [mat]`. Rewrite using `[hmat, (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w (mat γ) (mat δ) p hp).2.1, map_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem coboundaries_le_cocycles (Γ : Subgroup SL(2, ℤ)) (w : ℕ) : B1 Γ w ≤ Z1 Γ w := by
  intro z hz
  obtain ⟨p, rfl⟩ := LinearMap.mem_range.1 hz
  have hp : (p : ℂ[X]) ∈ degreeLT ℂ (w + 1) := p.2
  refine ⟨fun γ => ?_, fun γ δ => ?_⟩
  · change slP w (mat γ) p - p ∈ degreeLT ℂ (w + 1)
    exact Submodule.sub_mem _ (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w (mat γ) 1 p hp).1 hp
  · change slP w (mat ((γ * δ : Γ) : SL(2, ℤ))) p - p =
      slP w (mat δ) (slP w (mat γ) p - p) + (slP w (mat δ) p - p)
    have hmat : mat ((γ * δ : Γ) : SL(2, ℤ)) = mat γ * mat δ := by simp [mat]
    rw [hmat, (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w (mat γ) (mat δ) p hp).2.1, map_sub]
    abel

/- English proof (translation)
Establish `hd` using `UpperHalfPlane.mdifferentiable_iff.1 hf`. Establish `him : ∀ t ∈ Set.uIcc (0 : ℝ) 1, 0 < (Complex.I + t * ((τ : ℂ) - Complex.I)).im`. Introduce `t ht`. Rewrite `ht` using `[Set.uIcc_of_le zero_le_one]`. Take `⟨h0, h1⟩` from `ht`.

Establish `hτ` using `τ.im_pos`. Establish `e : (Complex.I + t * ((τ : ℂ) - Complex.I)).im = (1 - t) + t * τ.im`. Simplify using `[Complex.mul_im]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Break down `h1.lt_or_eq with h1 | rfl` into its components or cases. Use polynomial arithmetic with `[mul_nonneg h0 hτ.le]`. Simplify using `using hτ`. Establish `hpath : Continuous fun t : ℝ => Complex.I + t * ((τ : ℂ) - Complex.I)` using `by fun_prop`. Establish `hc : ContinuousOn (fun t : ℝ => (f ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I))) (Set.uIcc 0 1)` using `hd.continuousOn.comp hpath.continuousOn fun t ht => him t ht`.

Establish `hpow : Continuous fun t : ℝ => (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ n` using `by fun_prop`. Conclude with `((hc.mul hpow.continuousOn).mul continuousOn_const).intervalIntegrable`.
-/
theorem integrable_seg {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (n : ℕ) (τ : ℍ) :
    IntervalIntegrable (fun t : ℝ => (f ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
      (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ n * ((τ : ℂ) - Complex.I)) MeasureTheory.volume 0 1 := by
  have hd := UpperHalfPlane.mdifferentiable_iff.1 hf
  have him : ∀ t ∈ Set.uIcc (0 : ℝ) 1, 0 < (Complex.I + t * ((τ : ℂ) - Complex.I)).im := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    obtain ⟨h0, h1⟩ := ht
    have hτ := τ.im_pos
    have e : (Complex.I + t * ((τ : ℂ) - Complex.I)).im = (1 - t) + t * τ.im := by
      simp [Complex.mul_im]
      ring
    rw [e]
    rcases h1.lt_or_eq with h1 | rfl
    · nlinarith [mul_nonneg h0 hτ.le]
    · simpa using hτ
  have hpath : Continuous fun t : ℝ => Complex.I + t * ((τ : ℂ) - Complex.I) := by fun_prop
  have hc : ContinuousOn (fun t : ℝ => (f ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)))
      (Set.uIcc 0 1) :=
    hd.continuousOn.comp hpath.continuousOn fun t ht => him t ht
  have hpow : Continuous fun t : ℝ => (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ n := by fun_prop
  exact ((hc.mul hpow.continuousOn).mul continuousOn_const).intervalIntegrable

/- English proof (translation)
Establish `he : ∀ τ : ℍ, eichler w (f + g) τ = eichler w f τ + eichler w g τ`. Introduce `τ`. Simplify using `only [eichler, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hint : (∫ t in (0 : ℝ)..1, ((f + g) ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) * (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I)) = (∫ t in (0 : ℝ)..1, (f ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) * ( …`.

Rewrite using `[← intervalIntegral.integral_add (integrable_seg hf (w - j) τ) (integrable_seg hg (w - j) τ)]`. Use `intervalIntegral.integral_congr fun t _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hint, mul_add, C_add, add_mul]`.

Use function extensionality and compare the values at `γ`. Simplify using `only [per, Pi.add_apply, he, map_add]`.
-/
theorem per_add (Γ : Subgroup SL(2, ℤ)) (w : ℕ) {f g : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) : per Γ w (f + g) = per Γ w f + per Γ w g := by
  have he : ∀ τ : ℍ, eichler w (f + g) τ = eichler w f τ + eichler w g τ := by
    intro τ
    simp only [eichler, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hint : (∫ t in (0 : ℝ)..1, ((f + g) ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
          (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I)) =
        (∫ t in (0 : ℝ)..1, (f ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
          (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I)) +
        (∫ t in (0 : ℝ)..1, (g ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
          (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I)) := by
      rw [← intervalIntegral.integral_add (integrable_seg hf (w - j) τ) (integrable_seg hg (w - j) τ)]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [Function.comp_apply, Pi.add_apply]
      ring
    rw [hint, mul_add, C_add, add_mul]
  funext γ
  simp only [per, Pi.add_apply, he, map_add]

/- English proof (translation)
Use function extensionality and compare the values at `γ`. Simplify using `[cj, Polynomial.map_add]`.
-/
theorem cj_add {Γ : Type} (x y : Γ → ℂ[X]) : cj (x + y) = cj x + cj y := by
  funext γ
  simp [cj, Polynomial.map_add]

/- English proof (translation)
Use function extensionality and compare the values at `γ`. Express the relevant statement in the definitionally equal form `((r : ℂ) • x γ).map (starRingEnd ℂ) = (r : ℂ) • (x γ).map (starRingEnd ℂ)`. Rewrite using `[Polynomial.map_smul, Complex.conj_ofReal]`.
-/
theorem cj_real_smul {Γ : Type} (r : ℝ) (x : Γ → ℂ[X]) : cj ((r : ℂ) • x) = (r : ℂ) • cj x := by
  funext γ
  change ((r : ℂ) • x γ).map (starRingEnd ℂ) = (r : ℂ) • (x γ).map (starRingEnd ℂ)
  rw [Polynomial.map_smul, Complex.conj_ofReal]

/- English proof (translation)
Introduce `N M Γ k hN hM hΓM hΓN hk hk3 z hz`. Establish `: NeZero M` using `⟨hM.ne'⟩`. Establish `hfi : Γ.FiniteIndex` using `Subgroup.finiteIndex_of_le hΓM`. Take `⟨hfdM, hfdC, hcount⟩` from `GlobalTheory.T.oddWeight_modular_cusp_dimension_lower_bound N M Γ k hN hM hΓM hΓN hk hk3`. Take `⟨hfdZ, hZ⟩` from `GlobalTheory.T.finrank_z1_le_of_le_gamma1_of_finiteIndex N Γ (k - 2) hN hΓN hfi`.

Establish `hB` using `GlobalTheory.T.finrank_b1_eq_of_gamma_le M Γ (k - 2) hM (by omega) hΓM`. Establish `hk2 : 2 ≤ k` using `by omega`. Establish `hsm` using `(GlobalTheory.T.eichlerShimura_conj_cocycles_coboundaries_period_smul Γ (k - 2)).2.2`. Establish `hnegper : ∀ g : ℍ → ℂ, per Γ (k - 2) (-g) = -per Γ (k - 2) g`. Introduce `g`.

Simplify using `using hsm g (-1)`. Establish `hcjneg : ∀ x : Γ → ℂ[X], cj (-x) = -cj x`. Introduce `x`. Use function extensionality and compare the values at `γ`. Simplify using `[cj, Polynomial.map_neg]`.

Establish `key` using `exists_of_finrank_le (A := ModularForm Γ k) (A' := CuspForm Γ k) (Z1 Γ (k - 2)) (B1 Γ (k - 2)) (coboundaries_le_cocycles Γ (k - 2)) (fun f => per Γ (k - 2) ⇑f) (fun h => -cj (per Γ (k - 2) ⇑h)) (fun x y => by`. Simplify using `only [FunLike.coe_add]`. Conclude with `per_add Γ _ (ModularFormClass.holo x) (ModularFormClass.holo y))`. Use the proof step `(fun x y => by`. Simplify using `only [FunLike.coe_add, per_add Γ _ (ModularFormClass.holo x) (ModularFormClass.holo y), cj_add, neg_add])`.

Use the proof step `(fun r x => by`. Simplify using `only [FunLike.coe_smul]`. Conclude with `hsm _ _)`. Use the proof step `(fun r x => by simp only [FunLike.coe_smul, hsm, cj_real_smul, smul_neg])`. Use the proof step `(fun x => (GlobalTheory.T.eichlerPeriodCocycle_mem_cocycles_and_eq Γ k hk2 x).1)`.

Use the proof step `(fun y => Submodule.neg_mem _ ((GlobalTheory.T.eichlerShimura_conj_cocycles_coboundaries_period_smul Γ (k - 2)).1 _ (GlobalTheory.T.eichlerPeriodCocycle_mem_cocycles_and_eq Γ k hk2 (ModularFormClass.modularForm y)).1))`. Use the proof step `(fun x y hxy => by`. Establish `hxy' : per Γ (k - 2) ⇑x - cj (per Γ (k - 2) ⇑y) ∈ B1 Γ (k - 2)`. Simplify `hxy` using `[sub_eq_add_neg]`. Take `⟨f', hf'⟩` from `GlobalTheory.T.cuspidal_of_eichlerPeriod_sub_conj_mem_coboundaries N Γ k hN hΓN hfi hk3 x y hxy'`.

Rewrite `hxy'` using `[← hf']`. Take `⟨h1, h2⟩` from `GlobalTheory.T.cuspForms_eq_zero_of_period_sub_conj_coboundary N Γ k hN hΓN hfi hk3 f' y hxy'`. Use `⟨DFunLike.coe_injective ?_, h2⟩` and prove the remaining obligations. Rewrite using `[← hf', h1]`. Use the proof step `simp)`.

Use the proof step `(by`. Rewrite using `[hB]`. Establish `e : k - 1 = k - 2 + 1` using `by omega`. Rewrite `hcount` using `[e]`. Rewrite `hZ` using `[Nat.mul_add]`.

Use the proof step `omega)`. Take `⟨f, h, hfh⟩` from `key z hz`. Use `⟨f, -h, ?_⟩` and prove the remaining obligations. Simplify `hfh` using `[FunLike.coe_neg, hnegper, hcjneg, sub_eq_add_neg]`.
-/
theorem exists_per_add_cj_per : ∀ (N M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 5 ≤ N → 0 < M →
    CongruenceSubgroup.Gamma M ≤ Γ → Γ ≤ CongruenceSubgroup.Gamma1 N → Odd k → 3 ≤ k →
    ∀ z ∈ Z1 Γ (k - 2), ∃ (f : ModularForm Γ (k : ℤ)) (h : CuspForm Γ (k : ℤ)),
      z - per Γ (k - 2) ⇑f - cj (per Γ (k - 2) ⇑h) ∈ B1 Γ (k - 2) := by
  intro N M Γ k hN hM hΓM hΓN hk hk3 z hz
  have : NeZero M := ⟨hM.ne'⟩
  have hfi : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓM
  obtain ⟨hfdM, hfdC, hcount⟩ := GlobalTheory.T.oddWeight_modular_cusp_dimension_lower_bound N M Γ k hN hM hΓM hΓN hk hk3
  obtain ⟨hfdZ, hZ⟩ := GlobalTheory.T.finrank_z1_le_of_le_gamma1_of_finiteIndex N Γ (k - 2) hN hΓN hfi
  have hB := GlobalTheory.T.finrank_b1_eq_of_gamma_le M Γ (k - 2) hM (by omega) hΓM
  have hk2 : 2 ≤ k := by omega
  have hsm := (GlobalTheory.T.eichlerShimura_conj_cocycles_coboundaries_period_smul Γ (k - 2)).2.2
  have hnegper : ∀ g : ℍ → ℂ, per Γ (k - 2) (-g) = -per Γ (k - 2) g := by
    intro g
    simpa using hsm g (-1)
  have hcjneg : ∀ x : Γ → ℂ[X], cj (-x) = -cj x := by
    intro x
    funext γ
    simp [cj, Polynomial.map_neg]
  have key := exists_of_finrank_le (A := ModularForm Γ k) (A' := CuspForm Γ k)
    (Z1 Γ (k - 2)) (B1 Γ (k - 2)) (coboundaries_le_cocycles Γ (k - 2))
    (fun f => per Γ (k - 2) ⇑f) (fun h => -cj (per Γ (k - 2) ⇑h))
    (fun x y => by
      simp only [FunLike.coe_add]
      exact per_add Γ _ (ModularFormClass.holo x) (ModularFormClass.holo y))
    (fun x y => by
      simp only [FunLike.coe_add, per_add Γ _ (ModularFormClass.holo x) (ModularFormClass.holo y), cj_add,
        neg_add])
    (fun r x => by
      simp only [FunLike.coe_smul]
      exact hsm _ _)
    (fun r x => by simp only [FunLike.coe_smul, hsm, cj_real_smul, smul_neg])
    (fun x => (GlobalTheory.T.eichlerPeriodCocycle_mem_cocycles_and_eq Γ k hk2 x).1)
    (fun y => Submodule.neg_mem _
      ((GlobalTheory.T.eichlerShimura_conj_cocycles_coboundaries_period_smul Γ (k - 2)).1 _ (GlobalTheory.T.eichlerPeriodCocycle_mem_cocycles_and_eq Γ k hk2 (ModularFormClass.modularForm y)).1))
    (fun x y hxy => by
      have hxy' : per Γ (k - 2) ⇑x - cj (per Γ (k - 2) ⇑y) ∈ B1 Γ (k - 2) := by
        simpa [sub_eq_add_neg] using hxy
      obtain ⟨f', hf'⟩ := GlobalTheory.T.cuspidal_of_eichlerPeriod_sub_conj_mem_coboundaries N Γ k hN hΓN hfi hk3 x y hxy'
      rw [← hf'] at hxy'
      obtain ⟨h1, h2⟩ := GlobalTheory.T.cuspForms_eq_zero_of_period_sub_conj_coboundary N Γ k hN hΓN hfi hk3 f' y hxy'
      refine ⟨DFunLike.coe_injective ?_, h2⟩
      rw [← hf', h1]
      simp)
    (by
      rw [hB]
      have e : k - 1 = k - 2 + 1 := by omega
      rw [e] at hcount
      rw [Nat.mul_add] at hZ
      omega)
  obtain ⟨f, h, hfh⟩ := key z hz
  refine ⟨f, -h, ?_⟩
  simpa [FunLike.coe_neg, hnegper, hcjneg, sub_eq_add_neg] using hfh

end GlobalTheory.HeckeFamilyMatrices.EichlerShimura
