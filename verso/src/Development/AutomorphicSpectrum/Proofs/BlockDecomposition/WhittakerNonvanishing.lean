import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.WhNe

section Plane

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Use `⟨(hf.1.comp_continuous (continuous_apply 0)).mul (hg.1.comp_continuous (continuous_apply 1)), ?_⟩` and prove the remaining obligations. Use `HasCompactSupport.intro (K := Set.univ.pi fun _ : Fin 2 => tsupport f ∪ tsupport g) (isCompact_univ_pi fun _ => hf.2.isCompact.union hg.2.isCompact) fun x hx => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Apply `hx` to reduce the goal to its premises. Establish `h0 : f (x 0) ≠ 0` using `fun h => hne (by simp [pt, h])`.

Establish `h1 : g (x 1) ≠ 0` using `fun h => hne (by simp [pt, h])`. Introduce `i _`. Use `fin_cases i`. Conclude with `Or.inl (subset_tsupport _ h0)`. Conclude with `Or.inr (subset_tsupport _ h1)`.
-/
theorem pt_mem_plane {f g : F → ℂ} (hf : f ∈ schwartzBruhat F) (hg : g ∈ schwartzBruhat F) :
    pt f g ∈ GodementSectionLocal.schwartzBruhat2 F := by
  refine ⟨(hf.1.comp_continuous (continuous_apply 0)).mul
    (hg.1.comp_continuous (continuous_apply 1)), ?_⟩
  refine HasCompactSupport.intro (K := Set.univ.pi fun _ : Fin 2 => tsupport f ∪ tsupport g)
    (isCompact_univ_pi fun _ => hf.2.isCompact.union hg.2.isCompact) fun x hx => ?_
  by_contra hne
  apply hx
  have h0 : f (x 0) ≠ 0 := fun h => hne (by simp [pt, h])
  have h1 : g (x 1) ≠ 0 := fun h => hne (by simp [pt, h])
  intro i _
  fin_cases i
  · exact Or.inl (subset_tsupport _ h0)
  · exact Or.inr (subset_tsupport _ h1)

def unitSet (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) : Set F :=
  Units.val '' (unitFiltrationUnits F n : Set Fˣ)

/- English proof (translation)
The claim follows from `(isCompact_unitFiltrationUnits n).image Units.continuous_val`.
-/
theorem isCompact_unitSet (n : ℕ) : IsCompact (unitSet F n) :=
  (isCompact_unitFiltrationUnits n).image Units.continuous_val

/- English proof (translation)
Take `⟨t, ht, hU⟩` from `Units.isEmbedding_val₀.isInducing.isOpen_iff.mp (isOpen_unitFiltrationUnits (K := F) n)`. Establish `: unitSet F n = t ∩ {0}ᶜ`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`.

Use `⟨?_, u.ne_zero⟩` and prove the remaining obligations. Establish `: u ∈ Units.val ⁻¹' t` using `by rw [hU]; exact hu`. Conclude with `this`. Introduce and unpack `⟨hy, hy0⟩`. Use `⟨Units.mk0 y hy0, ?_, rfl⟩` and prove the remaining obligations.

Rewrite using `[← hU]`. Conclude with `hy`. Rewrite using `[this]`. Conclude with `ht.inter isOpen_compl_singleton`.
-/
theorem isOpen_unitSet (n : ℕ) : IsOpen (unitSet F n) := by
  obtain ⟨t, ht, hU⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.mp
    (isOpen_unitFiltrationUnits (K := F) n)
  have : unitSet F n = t ∩ {0}ᶜ := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨?_, u.ne_zero⟩
      have : u ∈ Units.val ⁻¹' t := by rw [hU]; exact hu
      exact this
    · rintro ⟨hy, hy0⟩
      refine ⟨Units.mk0 y hy0, ?_, rfl⟩
      rw [← hU]
      exact hy
  rw [this]
  exact ht.inter isOpen_compl_singleton

/- English proof (translation)
Assemble the required witnesses or components as `⟨GodementSectionLocal.isLocallyConstant_indicator ⟨(isCompact_unitSet n).isClosed, isOpen_unitSet n⟩ (IsLocallyConstant.const 1), HasCompactSupport.intro (isCompact_unitSet n) fun _ hx => Set.indicator_of_notMem hx _⟩`.
-/
theorem indicator_unitSet_mem (n : ℕ) :
    (unitSet F n).indicator (fun _ => (1 : ℂ)) ∈ schwartzBruhat F :=
  ⟨GodementSectionLocal.isLocallyConstant_indicator ⟨(isCompact_unitSet n).isClosed, isOpen_unitSet n⟩
      (IsLocallyConstant.const 1),
    HasCompactSupport.intro (isCompact_unitSet n) fun _ hx => Set.indicator_of_notMem hx _⟩

/- English proof (translation)
The claim follows from `indicator_valBall_zero_mem_schwartzBruhat`.
-/
theorem indicator_ball_mem :
    (valBall F 0 : Set F).indicator (fun _ => (1 : ℂ)) ∈ schwartzBruhat F :=
  indicator_valBall_zero_mem_schwartzBruhat

/- English proof (translation)
The claim follows from `modulus_eq_one_iff.mpr ⟨h.ne_zero, mem_unitFiltrationUnits_zero_iff_ord.mp (unitFiltrationUnits_antitone (Nat.zero_le n) hh)⟩`.
-/
theorem modulus_eq_one_of_mem {n : ℕ} {h : Fˣ} (hh : h ∈ unitFiltrationUnits F n) :
    modulus (h : F) = 1 :=
  modulus_eq_one_iff.mpr ⟨h.ne_zero, mem_unitFiltrationUnits_zero_iff_ord.mp
    (unitFiltrationUnits_antitone (Nat.zero_le n) hh)⟩

/- English proof (translation)
Establish `hO : ∀ {u : Fˣ}, u ∈ unitFiltrationUnits F n → (u : F) ∈ 𝒪[F]` using `fun hu => modulus_le_one_iff.mp (modulus_eq_one_of_mem hu).le`. Simplify using `only [SetLike.mem_coe, mem_valBall_zero_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `mul_mem (hO (inv_mem hh)) hx` as an intermediate fact.

Simplify using `using this`. Conclude with `fun hx => mul_mem (hO hh) hx`.
-/
theorem mul_mem_ball_iff {n : ℕ} {h : Fˣ} (hh : h ∈ unitFiltrationUnits F n) (x : F) :
    (h : F) * x ∈ (valBall F 0 : Set F) ↔ x ∈ (valBall F 0 : Set F) := by
  have hO : ∀ {u : Fˣ}, u ∈ unitFiltrationUnits F n → (u : F) ∈ 𝒪[F] := fun hu =>
    modulus_le_one_iff.mp (modulus_eq_one_of_mem hu).le
  simp only [SetLike.mem_coe, mem_valBall_zero_iff]
  constructor
  · intro hx
    have := mul_mem (hO (inv_mem hh)) hx
    simpa using this
  · exact fun hx => mul_mem (hO hh) hx

end Plane

section Main

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Simplify using `[W2, mp, modulus_one]`.
-/
theorem whittaker_at_identity_integral (ψ : AddChar F Circle) (μ₁ μ₂ : Fˣ →* ℂˣ) (φ : (Fin 2 → F) → ℂ) :
    W2 ψ μ₁ μ₂ φ 1 = ∫ h : Fˣ, (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 *
      (∫ x, φ ![(h : F), h * x] * (ψ (-x) : ℂ) ∂selfDualMeasure ψ) ∂multHaar F := by
  simp [W2, mp, modulus_one]

/- English proof (translation)
Establish `hfun : (fun x => (valBall F 0 : Set F).indicator (fun _ => (1 : ℂ)) ((h : F) * x) * (ψ (-x) : ℂ)) = (valBall F 0 : Set F).indicator (fun _ => (1 : ℂ))`. Use extensionality with `x`. Distinguish the cases in `hx : x ∈ (valBall F 0 : Set F)`. Establish `hneg : -x ∈ valBall F (addCharConductor ψ)`. Rewrite using `[hψ.2.2]`.

Conclude with `neg_mem hx`. Rewrite using `[Set.indicator_of_mem ((mul_mem_ball_iff hh x).mpr hx), Set.indicator_of_mem hx, isTrivialOn_addCharConductor hψ.1 hψ.2.1 _ hneg]`. Simplify using the standard rewrite rules. Rewrite using `[Set.indicator_of_notMem (fun h' => hx ((mul_mem_ball_iff hh x).mp h')), Set.indicator_of_notMem hx, zero_mul]`. Rewrite using `[hfun, integral_indicator_const _ (isOpen_valBall 0).measurableSet, selfDualMeasure_real_valBall_zero, hψ.2.2]`.

Simplify using the standard rewrite rules.
-/
theorem inner_eq (ψ : AddChar F Circle) (hψ : IsStd ψ) {n : ℕ} {h : Fˣ}
    (hh : h ∈ unitFiltrationUnits F n) :
    (∫ x, (valBall F 0 : Set F).indicator (fun _ => (1 : ℂ)) ((h : F) * x) * (ψ (-x) : ℂ)
      ∂selfDualMeasure ψ) = 1 := by
  have hfun : (fun x => (valBall F 0 : Set F).indicator (fun _ => (1 : ℂ)) ((h : F) * x) *
      (ψ (-x) : ℂ)) = (valBall F 0 : Set F).indicator (fun _ => (1 : ℂ)) := by
    ext x
    by_cases hx : x ∈ (valBall F 0 : Set F)
    · have hneg : -x ∈ valBall F (addCharConductor ψ) := by
        rw [hψ.2.2]
        exact neg_mem hx
      rw [Set.indicator_of_mem ((mul_mem_ball_iff hh x).mpr hx), Set.indicator_of_mem hx,
        isTrivialOn_addCharConductor hψ.1 hψ.2.1 _ hneg]
      simp
    · rw [Set.indicator_of_notMem (fun h' => hx ((mul_mem_ball_iff hh x).mp h')),
        Set.indicator_of_notMem hx, zero_mul]
  rw [hfun, integral_indicator_const _ (isOpen_valBall 0).measurableSet,
    selfDualMeasure_real_valBall_zero, hψ.2.2]
  simp

/- English proof (translation)
Establish `hfun : (fun h : Fˣ => (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 * (∫ x, pt ((unitSet F n).indicator fun _ => (1 : ℂ)) ((valBall F 0 : Set F).indicator fun _ => (1 : ℂ)) ![(h : F), h * x] * (ψ (-x) : ℂ) ∂selfDualMeasure ψ)) = (unitFiltrationUnits F n : Set Fˣ).indicator (fun _ => (1 : …`. Use extensionality with `h`. Distinguish the cases in `hh : h ∈ (unitFiltrationUnits F n : Set Fˣ)`. Establish `hmem : (h : F) ∈ unitSet F n` using `⟨h, hh, rfl⟩`. Establish `hin` using `inner_eq ψ hψ (SetLike.mem_coe.mp hh)`.

Simplify using `only [pt, Matrix.cons_val_zero, Matrix.cons_val_one, Set.indicator_of_mem hmem, one_mul]`. Rewrite using `[hin, hker h hh, Set.indicator_of_mem hh]`. Simplify using `[mp, modulus_eq_one_of_mem (SetLike.mem_coe.mp hh)]`. Establish `hmem : (h : F) ∉ unitSet F n`. Introduce and unpack `⟨u, hu, huh⟩`.

Conclude with `hh (by rwa [← Units.ext huh])`. Simplify using `only [pt, Matrix.cons_val_zero, Set.indicator_of_notMem hmem, zero_mul, integral_zero, mul_zero]`. Rewrite using `[Set.indicator_of_notMem hh]`. Establish `hmeas : MeasurableSet (unitFiltrationUnits F n : Set Fˣ)`. Establish `h1 : (unitFiltrationUnits F n : Set Fˣ) = Units.val ⁻¹' unitSet F n`.

Use extensionality with `u`. Prove the components needed by the constructor for the conclusion. Conclude with `fun hu => ⟨u, hu, rfl⟩`. Introduce and unpack `⟨v, hv, hvu⟩`. Rewrite using `[← Units.ext hvu]` and apply the resulting hypothesis.

Rewrite using `[h1]`. Conclude with `measurableEmbedding_units_val.measurable (isOpen_unitSet n).measurableSet`. Rewrite using `[whittaker_at_identity_integral, hfun, integral_indicator_const _ hmeas]`. Simplify using the standard rewrite rules.
-/
theorem whittaker_indicator_at_identity (ψ : AddChar F Circle) (hψ : IsStd ψ) (μ₁ μ₂ : Fˣ →* ℂˣ) {n : ℕ}
    (hker : ∀ h ∈ unitFiltrationUnits F n, (μ₁ h)⁻¹ * μ₂ h = 1) :
    W2 ψ μ₁ μ₂ (pt ((unitSet F n).indicator fun _ => (1 : ℂ))
      ((valBall F 0 : Set F).indicator fun _ => (1 : ℂ))) 1 =
      (((multHaar F).real (unitFiltrationUnits F n : Set Fˣ) : ℝ) : ℂ) := by
  have hfun : (fun h : Fˣ => (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 *
      (∫ x, pt ((unitSet F n).indicator fun _ => (1 : ℂ))
        ((valBall F 0 : Set F).indicator fun _ => (1 : ℂ)) ![(h : F), h * x] * (ψ (-x) : ℂ)
          ∂selfDualMeasure ψ)) =
      (unitFiltrationUnits F n : Set Fˣ).indicator (fun _ => (1 : ℂ)) := by
    ext h
    by_cases hh : h ∈ (unitFiltrationUnits F n : Set Fˣ)
    · have hmem : (h : F) ∈ unitSet F n := ⟨h, hh, rfl⟩
      have hin := inner_eq ψ hψ (SetLike.mem_coe.mp hh)
      simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one, Set.indicator_of_mem hmem, one_mul]
      rw [hin, hker h hh, Set.indicator_of_mem hh]
      simp [mp, modulus_eq_one_of_mem (SetLike.mem_coe.mp hh)]
    · have hmem : (h : F) ∉ unitSet F n := by
        rintro ⟨u, hu, huh⟩
        exact hh (by rwa [← Units.ext huh])
      simp only [pt, Matrix.cons_val_zero, Set.indicator_of_notMem hmem, zero_mul,
        integral_zero, mul_zero]
      rw [Set.indicator_of_notMem hh]
  have hmeas : MeasurableSet (unitFiltrationUnits F n : Set Fˣ) := by
    have h1 : (unitFiltrationUnits F n : Set Fˣ) = Units.val ⁻¹' unitSet F n := by
      ext u
      constructor
      · exact fun hu => ⟨u, hu, rfl⟩
      · rintro ⟨v, hv, hvu⟩
        rwa [← Units.ext hvu]
    rw [h1]
    exact measurableEmbedding_units_val.measurable (isOpen_unitSet n).measurableSet
  rw [whittaker_at_identity_integral, hfun, integral_indicator_const _ hmeas]
  simp

end Main

/- English proof (translation)
Introduce `F _ _ _ _ _ _ ψ hψ μ₁ μ₂ h₁ h₂`. Establish `hc : Continuous (μ₁⁻¹ * μ₂)` using `by show Continuous fun x => (μ₁ x)⁻¹ * μ₂ x`. Conclude with `h₁.1.inv.mul h₂.1`. Take `⟨n, hn⟩` from `exists_unitFiltrationUnits_le_ker hc`. Use `⟨_, pt_mem_plane (indicator_unitSet_mem n) indicator_ball_mem, ?_⟩` and prove the remaining obligations.

Rewrite using `[whittaker_indicator_at_identity ψ hψ μ₁ μ₂ (fun h hh => hn hh)]`. Establish `h0 : multHaar F (unitFiltrationUnits F n : Set Fˣ) ≠ 0` using `(isOpen_unitFiltrationUnits n).measure_ne_zero _ ⟨1, one_mem _⟩`. Establish `ht` using `(multHaar_unitFiltrationUnits_lt_top (K := F) n).ne`. Conclude with `(ENNReal.toReal_pos h0 ht).ne'` after adjusting the coercions.
-/
theorem sNe : Ad3.SchwartzSpaceL2.SNe := by
  intro F _ _ _ _ _ _ ψ hψ μ₁ μ₂ h₁ h₂
  have hc : Continuous (μ₁⁻¹ * μ₂) := by
    show Continuous fun x => (μ₁ x)⁻¹ * μ₂ x
    exact h₁.1.inv.mul h₂.1
  obtain ⟨n, hn⟩ := exists_unitFiltrationUnits_le_ker hc
  refine ⟨_, pt_mem_plane (indicator_unitSet_mem n) indicator_ball_mem, ?_⟩
  rw [whittaker_indicator_at_identity ψ hψ μ₁ μ₂ (fun h hh => hn hh)]
  have h0 : multHaar F (unitFiltrationUnits F n : Set Fˣ) ≠ 0 :=
    (isOpen_unitFiltrationUnits n).measure_ne_zero _ ⟨1, one_mem _⟩
  have ht := (multHaar_unitFiltrationUnits_lt_top (K := F) n).ne
  exact_mod_cast (ENNReal.toReal_pos h0 ht).ne'

end GlobalTheory.CompanionTheory.WhNe
