import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical

namespace GlobalTheory.CompanionTheory.NewformLiftLocalWhittaker

open Ad3 Ad3.R

section Unr

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Use `(mem_unitFiltrationUnits_zero_iff_ord (K := F) (u := 1)).1 (one_mem _)` as an intermediate fact. Simplify using `using this`.
-/
theorem ord_one' : ord (1 : F) = 0 := by
  have := (mem_unitFiltrationUnits_zero_iff_ord (K := F) (u := 1)).1 (one_mem _)
  simpa using this

def ordH : Fˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (ord (x : F))
  map_one' := by simp [ord_one']
  map_mul' x y := by rw [ord_units_mul, ofAdd_add]

/- English proof (translation)
Establish `h` using `map_zpow (ordH (F := F)) x n`. Establish `h2 : Multiplicative.ofAdd (ord ((x ^ n : Fˣ) : F)) = (Multiplicative.ofAdd (ord (x : F))) ^ n` using `h`. Rewrite `h2` using `[← ofAdd_zsmul]`. Simplify using `using Multiplicative.ofAdd.injective h2`.
-/
theorem ord_zpow (x : Fˣ) (n : ℤ) : ord ((x ^ n : Fˣ) : F) = n * ord (x : F) := by
  have h := map_zpow (ordH (F := F)) x n
  have h2 : Multiplicative.ofAdd (ord ((x ^ n : Fˣ) : F)) = (Multiplicative.ofAdd (ord (x : F))) ^ n := h
  rw [← ofAdd_zsmul] at h2
  simpa using Multiplicative.ofAdd.injective h2

def unrC (z : ℂˣ) : Fˣ →* ℂˣ where
  toFun x := z ^ ord (x : F)
  map_one' := by simp [ord_one']
  map_mul' x y := by rw [ord_units_mul, _root_.zpow_add]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem unrC_apply (z : ℂˣ) (x : Fˣ) : unrC z x = z ^ ord (x : F) := rfl

/- English proof (translation)
Simplify using `[unrC_apply, ord_unifUnit]`.
-/
theorem unrC_unif (z : ℂˣ) : unrC (F := F) z (unifUnit F) = z := by
  simp [unrC_apply, ord_unifUnit]

/- English proof (translation)
Introduce `x hx`. Rewrite using `[MonoidHom.mem_ker, unrC_apply, mem_unitFiltrationUnits_zero_iff_ord.1 hx, zpow_zero]`.
-/
theorem unrC_unram (z : ℂˣ) : IsUnramifiedChar (unrC (F := F) z) := by
  intro x hx
  rw [MonoidHom.mem_ker, unrC_apply, mem_unitFiltrationUnits_zero_iff_ord.1 hx, zpow_zero]

/- English proof (translation)
Use `continuous_of_continuousAt_one _ ?_` and prove the remaining obligations. Establish `h : (unrC (F` using `F) z) =ᶠ[𝓝 1] fun _ => 1 := by filter_upwards [(isOpen_unitFiltrationUnits (K := F) 0).mem_nhds (one_mem _)] with x hx`. Conclude with `unrC_unram z hx`. Use `ContinuousAt.congr ?_ h.symm` and prove the remaining obligations. Conclude with `continuousAt_const`.
-/
theorem unrC_cont (z : ℂˣ) : Continuous (unrC (F := F) z) := by
  refine continuous_of_continuousAt_one _ ?_
  have h : (unrC (F := F) z) =ᶠ[𝓝 1] fun _ => 1 := by
    filter_upwards [(isOpen_unitFiltrationUnits (K := F) 0).mem_nhds (one_mem _)] with x hx
    exact unrC_unram z hx
  refine ContinuousAt.congr ?_ h.symm
  exact continuousAt_const

/- English proof (translation)
Use `⟨unrC_cont z, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[unrC_apply, Units.val_zpow_eq_zpow_val, norm_zpow, hz, _root_.one_zpow]`.
-/
theorem unrC_unit {z : ℂˣ} (hz : ‖(z : ℂ)‖ = 1) : IsUnit1 (unrC (F := F) z) := by
  refine ⟨unrC_cont z, fun x => ?_⟩
  rw [unrC_apply, Units.val_zpow_eq_zpow_val, norm_zpow, hz, _root_.one_zpow]

/- English proof (translation)
Establish `hu : x * (unifUnit F ^ ord (x : F))⁻¹ ∈ unitFiltrationUnits F 0`. Rewrite using `[mem_unitFiltrationUnits_zero_iff_ord, ord_units_mul, ord_units_inv, ord_zpow, ord_unifUnit]`. Simplify using the standard rewrite rules. Establish `h2` using `h hu`. Rewrite `h2` using `[MonoidHom.mem_ker, map_mul, map_inv, map_zpow, mul_inv_eq_one]`.

Conclude with `h2`.
-/
theorem unram_apply {χ : Fˣ →* ℂˣ} (h : IsUnramifiedChar χ) (x : Fˣ) :
    χ x = χ (unifUnit F) ^ ord (x : F) := by
  have hu : x * (unifUnit F ^ ord (x : F))⁻¹ ∈ unitFiltrationUnits F 0 := by
    rw [mem_unitFiltrationUnits_zero_iff_ord, ord_units_mul, ord_units_inv, ord_zpow, ord_unifUnit]
    simp
  have h2 := h hu
  rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, mul_inv_eq_one] at h2
  exact h2

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[unram_apply h, unram_apply h', e]`.
-/
theorem unram_ext {χ μ : Fˣ →* ℂˣ} (h : IsUnramifiedChar χ) (h' : IsUnramifiedChar μ)
    (e : χ (unifUnit F) = μ (unifUnit F)) : χ = μ := by
  ext x
  rw [unram_apply h, unram_apply h', e]

/- English proof (translation)
Introduce `x hx`. Establish `h1` using `h hx`. Establish `h2` using `h' hx`. Rewrite `*` using `[MonoidHom.mem_ker]`. Simplify using `[h1, h2]`.
-/
theorem unram_mul {χ μ : Fˣ →* ℂˣ} (h : IsUnramifiedChar χ) (h' : IsUnramifiedChar μ) :
    IsUnramifiedChar (χ * μ) := by
  intro x hx
  have h1 := h hx
  have h2 := h' hx
  rw [MonoidHom.mem_ker] at *
  simp [h1, h2]

/- English proof (translation)
Unfold `quasiCharConductor`. Use `congr 1`. Use extensionality with `n`. Simplify using `only [Set.mem_setOf_eq]`. Establish `hμ : unitFiltrationUnits F n ≤ μ.ker` using `(unitFiltrationUnits_antitone (Nat.zero_le n)).trans h`.

Prove the components needed by the constructor for the conclusion. Introduce `hh x hx`. Establish `h1` using `hh hx`. Establish `h2` using `hμ hx`. Rewrite `*` using `[MonoidHom.mem_ker]`.

Simplify `h1` using `[h2]`. Introduce `hh x hx`. Establish `h1` using `hh hx`. Establish `h2` using `hμ hx`. Rewrite `*` using `[MonoidHom.mem_ker]`.

Simplify using `[h1, h2]`.
-/
theorem conductor_twist {χ μ : Fˣ →* ℂˣ} (h : IsUnramifiedChar μ) :
    quasiCharConductor (χ * μ⁻¹) = quasiCharConductor χ := by
  unfold quasiCharConductor
  congr 1
  ext n
  simp only [Set.mem_setOf_eq]
  have hμ : unitFiltrationUnits F n ≤ μ.ker := (unitFiltrationUnits_antitone (Nat.zero_le n)).trans h
  constructor
  · intro hh x hx
    have h1 := hh hx
    have h2 := hμ hx
    rw [MonoidHom.mem_ker] at *
    simpa [h2] using h1
  · intro hh x hx
    have h1 := hh hx
    have h2 := hμ hx
    rw [MonoidHom.mem_ker] at *
    simp [h1, h2]

end Unr

section Law

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun x g => by simp only [hA.1, hB.1]; ring, fun z g => by simp only [hA.2, hB.2]; ring⟩`.
-/
theorem law_sub {ψ : AddChar F Circle} {ω : Fˣ →* ℂˣ} {A B : GL (Fin 2) F → ℂ} (c : ℂ)
    (hA : Law ψ ω A) (hB : Law ψ ω B) : Law ψ ω (fun y => A y - c * B y) :=
  ⟨fun x g => by simp only [hA.1, hB.1]; ring, fun z g => by simp only [hA.2, hB.2]; ring⟩

/- English proof (translation)
Use `⟨fun x d hx g => ?_, fun ϖ S hR g => ?_⟩` and prove the remaining obligations. Simplify using `only [hA.1 x d hx, hB.1 x d hx]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_sub_distrib, ← Finset.mul_sum]`. Take the linear combination `hA.2 ϖ S hR g - c * hB.2 ϖ S hR g`.
-/
theorem typeU_sub {ω : Fˣ →* ℂˣ} {n : ℕ} {lam : ℂ} {A B : GL (Fin 2) F → ℂ} (c : ℂ)
    (hA : TypeU ω n lam A) (hB : TypeU ω n lam B) : TypeU ω n lam (fun y => A y - c * B y) := by
  refine ⟨fun x d hx g => ?_, fun ϖ S hR g => ?_⟩
  · simp only [hA.1 x d hx, hB.1 x d hx]; ring
  · rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    linear_combination hA.2 ϖ S hR g - c * hB.2 ϖ S hR g

/- English proof (translation)
Use `⟨fun x hx g => ?_, fun ϖ S hR g => ?_⟩` and prove the remaining obligations. Simplify using `only [hA.1 x hx, hB.1 x hx]`. Rewrite using `[Finset.sum_sub_distrib, ← Finset.mul_sum]`. Take the linear combination `hA.2 ϖ S hR g - c * hB.2 ϖ S hR g`.
-/
theorem typeT_sub {lam : ℂ} {A B : GL (Fin 2) F → ℂ} (c : ℂ)
    (hA : TypeT lam A) (hB : TypeT lam B) : TypeT lam (fun y => A y - c * B y) := by
  refine ⟨fun x hx g => ?_, fun ϖ S hR g => ?_⟩
  · simp only [hA.1 x hx, hB.1 x hx]
  · rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    linear_combination hA.2 ϖ S hR g - c * hB.2 ϖ S hR g

/- English proof (translation)
Establish `hw` using `(hL F ψ hψ μ₁ μ₂ h₁ h₂).1`. Establish `hm : W2 ψ μ₁ μ₂ φ₀ ∈ V2 ψ μ₁ μ₂` using `Submodule.subset_span ⟨φ₀, hs, rfl⟩`. Conclude with `⟨hw.psi _ hm, hw.cen _ hm⟩`.
-/
theorem local_whittaker_transformation_law (hL : Loc2) {ψ : AddChar F Circle} (hψ : IsStd ψ) {μ₁ μ₂ : Fˣ →* ℂˣ}
    (h₁ : IsUnit1 μ₁) (h₂ : IsUnit1 μ₂) {φ₀ : (Fin 2 → F) → ℂ} (hs : SB φ₀) :
    Law ψ (μ₁ * μ₂) (W2 ψ μ₁ μ₂ φ₀) := by
  have hw := (hL F ψ hψ μ₁ μ₂ h₁ h₂).1
  have hm : W2 ψ μ₁ μ₂ φ₀ ∈ V2 ψ μ₁ μ₂ := Submodule.subset_span ⟨φ₀, hs, rfl⟩
  exact ⟨hw.psi _ hm, hw.cen _ hm⟩

end Law

section Glob

/- English proof (translation)
Rewrite using `[Units.continuous_iff]`. Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `refine continuous_matrix fun i j => ?_ fin_cases i <;> fin_cases j <;> simp [uni2] <;> fun_prop`. Apply the tactic sequence `refine continuous_matrix fun i j => ?_ fin_cases i <;> fin_cases j <;> simp [uni2] <;> fun_prop`.
-/
theorem continuous_unipotentGL2 : Continuous (uni2 : 𝔸[ℚ] → G2) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [uni2] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [uni2] <;> fun_prop

/- English proof (translation)
Take `⟨C, hC, hCs⟩ : ∃ C : Set 𝔸[ℚ], IsCompact C ∧ fundamentalSet ℚ ⊆ C` from `⟨closure (fundamentalSetInfinite ℚ) ×ˢ (integralFiniteAdeles (𝓞 ℚ) ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)), (isCompact_closure_fundamentalSetInfinite ℚ).prod (isCompact_integralFiniteAdeles ℚ), Set.prod_mono subset_closure le_rfl⟩`. Establish `hc : Continuous fun x : 𝔸[ℚ] => φ (uni2 x * g) * (adelicChar ℚ (-x) : ℂ)` using `(hφ.comp (continuous_unipotentGL2.mul continuous_const)).mul (continuous_subtype_val.comp (continuous_adelicChar.comp continuous_neg))`. Conclude with `(hc.continuousOn.integrableOn_compact hC).mono_set hCs`.
-/
theorem wh_integrable {φ : G2 → ℂ} (hφ : Continuous φ) (g : G2) :
    IntegrableOn (fun x => φ (uni2 x * g) * (adelicChar ℚ (-x) : ℂ)) (fundamentalSet ℚ)
      (adeleMeasure ℚ) := by
  obtain ⟨C, hC, hCs⟩ : ∃ C : Set 𝔸[ℚ], IsCompact C ∧ fundamentalSet ℚ ⊆ C :=
    ⟨closure (fundamentalSetInfinite ℚ) ×ˢ
      (integralFiniteAdeles (𝓞 ℚ) ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)),
      (isCompact_closure_fundamentalSetInfinite ℚ).prod (isCompact_integralFiniteAdeles ℚ),
      Set.prod_mono subset_closure le_rfl⟩
  have hc : Continuous fun x : 𝔸[ℚ] => φ (uni2 x * g) * (adelicChar ℚ (-x) : ℂ) :=
    (hφ.comp (continuous_unipotentGL2.mul continuous_const)).mul
      (continuous_subtype_val.comp (continuous_adelicChar.comp continuous_neg))
  exact (hc.continuousOn.integrableOn_compact hC).mono_set hCs

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem wh_eq (φ : G2 → ℂ) (g : G2) :
    Wh φ g = ∫ x in fundamentalSet ℚ, φ (uni2 x * g) * (adelicChar ℚ (-x) : ℂ) ∂adeleMeasure ℚ := rfl

/- English proof (translation)
Simplify using `only [wh_eq]`. Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify using `only [h t, mul_assoc]`.
-/
theorem wh_one {φ : G2 → ℂ} {G G₀ : G2} {c : ℂ} (h : ∀ t : 𝔸[ℚ], φ (uni2 t * G) = c * φ (uni2 t * G₀)) :
    Wh φ G = c * Wh φ G₀ := by
  simp only [wh_eq]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [h t, mul_assoc]

/- English proof (translation)
Simplify using `only [wh_eq]`. Rewrite using `[← integral_finset_sum _ (fun b _ => wh_integrable hφ (G b)), ← integral_const_mul]`. Use `integral_congr_ae (Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify using `only [← Finset.sum_mul, h t, mul_assoc]`.
-/
theorem wh_sum {φ : G2 → ℂ} (hφ : Continuous φ) {ι : Type} (S : Finset ι) (G : ι → G2) {G₀ : G2} {c : ℂ}
    (h : ∀ t : 𝔸[ℚ], ∑ b ∈ S, φ (uni2 t * G b) = c * φ (uni2 t * G₀)) :
    ∑ b ∈ S, Wh φ (G b) = c * Wh φ G₀ := by
  simp only [wh_eq]
  rw [← integral_finset_sum _ (fun b _ => wh_integrable hφ (G b)), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [← Finset.sum_mul, h t, mul_assoc]

/- English proof (translation)
Simplify using `only [wh_eq]`. Rewrite using `[← integral_finset_sum _ (fun b _ => wh_integrable hφ (G b)), ← integral_add (integrable_finset_sum _ fun b _ => wh_integrable hφ (G b)) (wh_integrable hφ G'), ← integral_const_mul]`. Use `integral_congr_ae (Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify using `only [← Finset.sum_mul, ← add_mul, h t, mul_assoc]`.
-/
theorem wh_sum' {φ : G2 → ℂ} (hφ : Continuous φ) {ι : Type} (S : Finset ι) (G : ι → G2) {G' G₀ : G2} {c : ℂ}
    (h : ∀ t : 𝔸[ℚ], ∑ b ∈ S, φ (uni2 t * G b) + φ (uni2 t * G') = c * φ (uni2 t * G₀)) :
    ∑ b ∈ S, Wh φ (G b) + Wh φ G' = c * Wh φ G₀ := by
  simp only [wh_eq]
  rw [← integral_finset_sum _ (fun b _ => wh_integrable hφ (G b)),
    ← integral_add (integrable_finset_sum _ fun b _ => wh_integrable hφ (G b)) (wh_integrable hφ G'),
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [← Finset.sum_mul, ← add_mul, h t, mul_assoc]

/- English proof (translation)
Use `hB.2.2.2.1 h h' (fun v' => ?_) (fun w => ?_)` and prove the remaining obligations. Distinguish the cases in `e : v' = v`. Substitute `e` using the available equality. Rewrite using `[h₁.1, h₂.1]`. Rewrite using `[h₁.2.1 v' e, h₂.2.1 v' e]`.

Rewrite using `[h₁.2.2 w, h₂.2.2 w]`.
-/
theorem loc_unique (hB : B0) {v : Pl} {x : GL (Fin 2) (Qv v)} {h h' : G2}
    (h₁ : IsLoc2 v x h) (h₂ : IsLoc2 v x h') : h = h' := by
  refine hB.2.2.2.1 h h' (fun v' => ?_) (fun w => ?_)
  · by_cases e : v' = v
    · subst e
      rw [h₁.1, h₂.1]
    · rw [h₁.2.1 v' e, h₂.2.1 v' e]
  · rw [h₁.2.2 w, h₂.2.2 w]

/- English proof (translation)
Assemble the required witnesses or components as `⟨by rw [Reduction.finAt_mul, h₁.1, h₂.1], fun v' e => by rw [Reduction.finAt_mul, h₁.2.1 v' e, h₂.2.1 v' e, one_mul], fun w => by rw [Reduction.infAt_mul, h₁.2.2 w, h₂.2.2 w, one_mul]⟩`.
-/
theorem loc_mul {v : Pl} {x y : GL (Fin 2) (Qv v)} {h h' : G2}
    (h₁ : IsLoc2 v x h) (h₂ : IsLoc2 v y h') : IsLoc2 v (x * y) (h * h') :=
  ⟨by rw [Reduction.finAt_mul, h₁.1, h₂.1],
    fun v' e => by rw [Reduction.finAt_mul, h₁.2.1 v' e, h₂.2.1 v' e, one_mul],
    fun w => by rw [Reduction.infAt_mul, h₁.2.2 w, h₂.2.2 w, one_mul]⟩

/- English proof (translation)
Use `hB.2.2.2.1 _ _ (fun v' => ?_) (fun w => ?_)` and prove the remaining obligations. Rewrite using `[Reduction.finAt_mul, Reduction.finAt_mul]`. Distinguish the cases in `e : v' = v`. Substitute `e` using the available equality. Rewrite using `[hg, one_mul, mul_one]`.

Rewrite using `[h₁.2.1 v' e, one_mul, mul_one]`. Rewrite using `[Reduction.infAt_mul, Reduction.infAt_mul, h₁.2.2 w, one_mul, mul_one]`.
-/
theorem loc_comm (hB : B0) {v : Pl} {x : GL (Fin 2) (Qv v)} {h g : G2}
    (h₁ : IsLoc2 v x h) (hg : finAt v g = 1) : g * h = h * g := by
  refine hB.2.2.2.1 _ _ (fun v' => ?_) (fun w => ?_)
  · rw [Reduction.finAt_mul, Reduction.finAt_mul]
    by_cases e : v' = v
    · subst e
      rw [hg, one_mul, mul_one]
    · rw [h₁.2.1 v' e, one_mul, mul_one]
  · rw [Reduction.infAt_mul, Reduction.infAt_mul, h₁.2.2 w, one_mul, mul_one]

/- English proof (translation)
Use `⟨fun x y => ?_, fun z y => ?_⟩` and prove the remaining obligations. Take `⟨x', a', d', h1, -, h3, -, -⟩` from `hB.2.2.2.2.2.2.2 v x 1 1`. Establish `e : hh (uni2 x * y) = uni2 x' * hh y` using `loc_unique hB (hhl _) (loc_mul h1 (hhl y))`. Use `show Wh φ (g * hh (uni2 x * y)) = _ * Wh φ (g * hh y)`. Rewrite using `[e, ← mul_assoc, loc_comm hB h1 hg, mul_assoc, hW, h3]`.

Take `⟨x', a', d', -, h2, -, h4, h5⟩` from `hB.2.2.2.2.2.2.2 v 0 z z`. Take `rfl` from `h4 rfl`. Establish `e : hh (dg2 z z * y) = dg2 a' a' * hh y` using `loc_unique hB (hhl _) (loc_mul h2 (hhl y))`. Use `show Wh φ (g * hh (dg2 z z * y)) = _ * Wh φ (g * hh y)`. Rewrite using `[e, ← mul_assoc, loc_comm hB h2 hg, mul_assoc, hZ, (h5 ω).1]`.
-/
theorem law_A (hB : B0) {φ : G2 → ℂ} {ω : HeckeCharacter ℚ}
    (hW : ∀ x g, Wh φ (uni2 x * g) = (adelicChar ℚ x : ℂ) * Wh φ g)
    (hZ : ∀ (z : Jd) g, Wh φ (dg2 z z * g) = (ω.toIdele z : ℂ) * Wh φ g)
    {v : Pl} {hh : GL (Fin 2) (Qv v) → G2} (hhl : ∀ x, IsLoc2 v x (hh x)) {g : G2} (hg : finAt v g = 1) :
    Law (localAdelicChar ℚ v) (localChar ω v) (fun y => Wh φ (g * hh y)) := by
  refine ⟨fun x y => ?_, fun z y => ?_⟩
  · obtain ⟨x', a', d', h1, -, h3, -, -⟩ := hB.2.2.2.2.2.2.2 v x 1 1
    have e : hh (uni2 x * y) = uni2 x' * hh y := loc_unique hB (hhl _) (loc_mul h1 (hhl y))
    show Wh φ (g * hh (uni2 x * y)) = _ * Wh φ (g * hh y)
    rw [e, ← mul_assoc, loc_comm hB h1 hg, mul_assoc, hW, h3]
  · obtain ⟨x', a', d', -, h2, -, h4, h5⟩ := hB.2.2.2.2.2.2.2 v 0 z z
    obtain rfl := h4 rfl
    have e : hh (dg2 z z * y) = dg2 a' a' * hh y := loc_unique hB (hhl _) (loc_mul h2 (hhl y))
    show Wh φ (g * hh (dg2 z z * y)) = _ * Wh φ (g * hh y)
    rw [e, ← mul_assoc, loc_comm hB h2 hg, mul_assoc, hZ, (h5 ω).1]

/- English proof (translation)
Introduce `x h hx`. Use `show φ (g₀ * hh x) = φ (g₀ * h)`. Rewrite using `[loc_unique hB (hhl x) hx]`.
-/
theorem locFn_of (hB : B0) {φ : G2 → ℂ} {v : Pl} {hh : GL (Fin 2) (Qv v) → G2}
    (hhl : ∀ x, IsLoc2 v x (hh x)) (g₀ : G2) : LocFn v φ g₀ (fun y => φ (g₀ * hh y)) := by
  intro x h hx
  show φ (g₀ * hh x) = φ (g₀ * h)
  rw [loc_unique hB (hhl x) hx]

/- English proof (translation)
Use `⟨fun x d hx y => ?_, fun ϖ S hR y => ?_⟩` and prove the remaining obligations. Use `wh_one fun t => ?_` and prove the remaining obligations. Use `(hbad (uni2 t * g) _ (locFn_of hB hhl _)).1 x d hx y` as an intermediate fact. Simplify `this` using `only [mul_assoc]`. Use `wh_sum hφ S (fun b => g * hh (y * upm ϖ b)) fun t => ?_` and prove the remaining obligations.

Use `(hbad (uni2 t * g) _ (locFn_of hB hhl _)).2 ϖ S hR y` as an intermediate fact. Simplify `this` using `only [mul_assoc]`.
-/
theorem typeU_A (hB : B0) {φ : G2 → ℂ} (hφ : Continuous φ) {v : Pl} {ω' : (Qv v)ˣ →* ℂˣ} {n : ℕ} {lam : ℂ}
    (hbad : ∀ g W, LocFn v φ g W → TypeU ω' n lam W)
    {hh : GL (Fin 2) (Qv v) → G2} (hhl : ∀ x, IsLoc2 v x (hh x)) (g : G2) :
    TypeU ω' n lam (fun y => Wh φ (g * hh y)) := by
  refine ⟨fun x d hx y => ?_, fun ϖ S hR y => ?_⟩
  · refine wh_one fun t => ?_
    have := (hbad (uni2 t * g) _ (locFn_of hB hhl _)).1 x d hx y
    simpa only [mul_assoc] using this
  · refine wh_sum hφ S (fun b => g * hh (y * upm ϖ b)) fun t => ?_
    have := (hbad (uni2 t * g) _ (locFn_of hB hhl _)).2 ϖ S hR y
    simpa only [mul_assoc] using this

/- English proof (translation)
Use `⟨fun x hx y => ?_, fun ϖ S hR y => ?_⟩` and prove the remaining obligations. Establish `h` using `wh_one (φ := φ) (G := g * hh (y * x)) (G₀ := g * hh y) (c := 1) fun t => by`. Use `(hgood (uni2 t * g) _ (locFn_of hB hhl _)).1 x hx y` as an intermediate fact. Simplify `this` using `only [mul_assoc, one_mul]`. Simplify using `using h`.

Use `wh_sum' hφ S (fun b => g * hh (y * upm ϖ b)) fun t => ?_` and prove the remaining obligations. Use `(hgood (uni2 t * g) _ (locFn_of hB hhl _)).2 ϖ S hR y` as an intermediate fact. Simplify `this` using `only [mul_assoc]`.
-/
theorem typeT_A (hB : B0) {φ : G2 → ℂ} (hφ : Continuous φ) {v : Pl} {lam : ℂ}
    (hgood : ∀ g W, LocFn v φ g W → TypeT lam W)
    {hh : GL (Fin 2) (Qv v) → G2} (hhl : ∀ x, IsLoc2 v x (hh x)) (g : G2) :
    TypeT lam (fun y => Wh φ (g * hh y)) := by
  refine ⟨fun x hx y => ?_, fun ϖ S hR y => ?_⟩
  · have h := wh_one (φ := φ) (G := g * hh (y * x)) (G₀ := g * hh y) (c := 1) fun t => by
      have := (hgood (uni2 t * g) _ (locFn_of hB hhl _)).1 x hx y
      simpa only [mul_assoc, one_mul] using this
    simpa using h
  · refine wh_sum' hφ S (fun b => g * hh (y * upm ϖ b)) fun t => ?_
    have := (hgood (uni2 t * g) _ (locFn_of hB hhl _)).2 ϖ S hR y
    simpa only [mul_assoc] using this

/- English proof (translation)
Introduce `g hg x h hx`. Use `choose hh hhl using (hB.1 v).2.2.2.2.2.1`. Establish `h1 : hh 1 = 1` using `loc_unique hB (hhl 1) ⟨Reduction.finAt_one v, fun v' _ => Reduction.finAt_one v', fun w => Reduction.infAt_one w⟩`. Establish `hD` using `huniq _ (law_sub (Wh φ g) (law_A hB hW hZ hhl hg) hlaw) (hsub _ _ (hPA hh hhl g)) (by simp [h1, hone])`. Establish `hx'` using `congrFun hD x`.

Rewrite using `[loc_unique hB hx (hhl x)]`. Simplify `hx'` using `[sub_eq_zero]`.
-/
theorem fac_gen (hB : B0) {φ : G2 → ℂ} {ω : HeckeCharacter ℚ}
    (hW : ∀ x g, Wh φ (uni2 x * g) = (adelicChar ℚ x : ℂ) * Wh φ g)
    (hZ : ∀ (z : Jd) g, Wh φ (dg2 z z * g) = (ω.toIdele z : ℂ) * Wh φ g)
    {v : Pl} (P : (GL (Fin 2) (Qv v) → ℂ) → Prop) {W₂ : GL (Fin 2) (Qv v) → ℂ} (hone : W₂ 1 = 1)
    (hlaw : Law (localAdelicChar ℚ v) (localChar ω v) W₂)
    (hsub : ∀ A c, P A → P (fun y => A y - c * W₂ y))
    (huniq : ∀ D, Law (localAdelicChar ℚ v) (localChar ω v) D → P D → D 1 = 0 → D = 0)
    (hPA : ∀ hh : GL (Fin 2) (Qv v) → G2, (∀ x, IsLoc2 v x (hh x)) → ∀ g, P (fun y => Wh φ (g * hh y))) :
    ∀ g, finAt v g = 1 → ∀ x h, IsLoc2 v x h → Wh φ (g * h) = Wh φ g * W₂ x := by
  intro g hg x h hx
  choose hh hhl using (hB.1 v).2.2.2.2.2.1
  have h1 : hh 1 = 1 := loc_unique hB (hhl 1)
    ⟨Reduction.finAt_one v, fun v' _ => Reduction.finAt_one v', fun w => Reduction.infAt_one w⟩
  have hD := huniq _ (law_sub (Wh φ g) (law_A hB hW hZ hhl hg) hlaw) (hsub _ _ (hPA hh hhl g))
    (by simp [h1, hone])
  have hx' := congrFun hD x
  rw [loc_unique hB hx (hhl x)]
  simpa [sub_eq_zero] using hx'

end Glob

section Places

/- English proof (translation)
Take `⟨hψ, hq, hp, -, -, -, hω⟩` from `hB.1 v`. Establish `hω'` using `hω ω`. Establish `hp0 : (0 : ℝ) < pOf v` using `by exact_mod_cast hp.pos`. Establish `hs0 : Real.sqrt (pOf v) ≠ 0` using `(Real.sqrt_pos.2 hp0).ne'`. Establish `hln : ‖lam‖ = Real.sqrt (pOf v)` using `by rw [← hl, Real.sqrt_sq (norm_nonneg _)]`.

Establish `hlam : lam ≠ 0`. Introduce `h`. Rewrite `hln` using `[h, norm_zero]`. Conclude with `hs0 hln.symm`. Establish `hr : ((Real.sqrt (pOf v) : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hs0`.

Take `⟨z, hzv⟩ : ∃ z : ℂˣ, (z : ℂ) = lam / ((Real.sqrt (pOf v) : ℝ) : ℂ)` from `⟨Units.mk0 _ (div_ne_zero hlam hr), rfl⟩`. Establish `hz : ‖(z : ℂ)‖ = 1`. Rewrite using `[hzv, norm_div, hln, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), div_self hs0]`. Take `⟨μ₂, hμ₂⟩ : ∃ μ₂ : (Qv v)ˣ →* ℂˣ, μ₂ = unrC z` from `⟨_, rfl⟩`. Take `⟨μ₁, hμ₁⟩ : ∃ μ₁ : (Qv v)ˣ →* ℂˣ, μ₁ = localChar ω v * μ₂⁻¹` from `⟨_, rfl⟩`.

Establish `un₂ : IsUnramifiedChar μ₂` using `hμ₂ ▸ unrC_unram z`. Establish `u₂ : IsUnit1 μ₂` using `hμ₂ ▸ unrC_unit hz`. Establish `u₁ : IsUnit1 μ₁`. Use `⟨hμ₁ ▸ hω'.1.mul (continuous_quasiChar_inv u₂.1), fun x => ?_⟩` and prove the remaining obligations. Establish `h1` using `hω'.2 x`.

Establish `h2` using `u₂.2 x`. Rewrite using `[hμ₁, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, h1, h2]`. Evaluate the numerical expressions. Establish `e : μ₁ * μ₂ = localChar ω v` using `by rw [hμ₁]; exact inv_mul_cancel_right _ _`. Establish `hcond : quasiCharConductor μ₁ = n` using `by rw [hμ₁, conductor_twist un₂, hc]`.

Take `⟨φ₀, hs, h1, hT⟩` from `hM1 (Qv v) _ hψ μ₁ μ₂ u₁ u₂ un₂ (by omega)`. Establish `hv : ((Real.sqrt (residueCard (Qv v)) : ℝ) : ℂ) * ((μ₂ (unifUnit (Qv v)) : ℂˣ) : ℂ) = lam`. Rewrite using `[hq, hμ₂, unrC_unif, hzv]`. Clear the denominators using the available nonvanishing facts. Rewrite `hT` using `[hcond, e, hv]`.

Use `⟨μ₁, μ₂, φ₀, u₁, u₂, e, hs, h1, ?_⟩` and prove the remaining obligations. Establish `hlaw` using `local_whittaker_transformation_law hL hψ u₁ u₂ hs`. Rewrite `hlaw` using `[e]`. Conclude with `fac_gen hB hW hZ (TypeU (localChar ω v) n lam) h1 hlaw (fun A c hA => typeU_sub c hA hT) (fun D hD hT' h0 => hU1 (Qv v) _ hψ _ n lam D hn hlam hD hT' h0) (fun hh hhl g => typeU_A hB hφ hbad hhl g)`.
-/
theorem place_bad (hL : Loc2) (hU1 : U1) (hM1 : M1) (hB : B0) {φ : G2 → ℂ} (hφ : Continuous φ)
    {ω : HeckeCharacter ℚ}
    (hW : ∀ x g, Wh φ (uni2 x * g) = (adelicChar ℚ x : ℂ) * Wh φ g)
    (hZ : ∀ (z : Jd) g, Wh φ (dg2 z z * g) = (ω.toIdele z : ℂ) * Wh φ g)
    {v : Pl} {n : ℕ} {lam : ℂ} (hn : 1 ≤ n) (hc : quasiCharConductor (localChar ω v) = n)
    (hl : ‖lam‖ ^ 2 = (pOf v : ℝ))
    (hbad : ∀ g W, LocFn v φ g W → TypeU (localChar ω v) n lam W) :
    ∃ (μ₁ μ₂ : (Qv v)ˣ →* ℂˣ) (φ₀ : (Fin 2 → Qv v) → ℂ), IsUnit1 μ₁ ∧ IsUnit1 μ₂ ∧
      μ₁ * μ₂ = localChar ω v ∧ SB φ₀ ∧ W2 (localAdelicChar ℚ v) μ₁ μ₂ φ₀ 1 = 1 ∧
      ∀ g, finAt v g = 1 → ∀ x h, IsLoc2 v x h →
        Wh φ (g * h) = Wh φ g * W2 (localAdelicChar ℚ v) μ₁ μ₂ φ₀ x := by
  obtain ⟨hψ, hq, hp, -, -, -, hω⟩ := hB.1 v
  have hω' := hω ω
  have hp0 : (0 : ℝ) < pOf v := by exact_mod_cast hp.pos
  have hs0 : Real.sqrt (pOf v) ≠ 0 := (Real.sqrt_pos.2 hp0).ne'
  have hln : ‖lam‖ = Real.sqrt (pOf v) := by rw [← hl, Real.sqrt_sq (norm_nonneg _)]
  have hlam : lam ≠ 0 := by
    intro h
    rw [h, norm_zero] at hln
    exact hs0 hln.symm
  have hr : ((Real.sqrt (pOf v) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0
  obtain ⟨z, hzv⟩ : ∃ z : ℂˣ, (z : ℂ) = lam / ((Real.sqrt (pOf v) : ℝ) : ℂ) :=
    ⟨Units.mk0 _ (div_ne_zero hlam hr), rfl⟩
  have hz : ‖(z : ℂ)‖ = 1 := by
    rw [hzv, norm_div, hln, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), div_self hs0]
  obtain ⟨μ₂, hμ₂⟩ : ∃ μ₂ : (Qv v)ˣ →* ℂˣ, μ₂ = unrC z := ⟨_, rfl⟩
  obtain ⟨μ₁, hμ₁⟩ : ∃ μ₁ : (Qv v)ˣ →* ℂˣ, μ₁ = localChar ω v * μ₂⁻¹ := ⟨_, rfl⟩
  have un₂ : IsUnramifiedChar μ₂ := hμ₂ ▸ unrC_unram z
  have u₂ : IsUnit1 μ₂ := hμ₂ ▸ unrC_unit hz
  have u₁ : IsUnit1 μ₁ := by
    refine ⟨hμ₁ ▸ hω'.1.mul (continuous_quasiChar_inv u₂.1), fun x => ?_⟩
    have h1 := hω'.2 x
    have h2 := u₂.2 x
    rw [hμ₁, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, norm_mul, Units.val_inv_eq_inv_val,
      norm_inv, h1, h2]
    norm_num
  have e : μ₁ * μ₂ = localChar ω v := by rw [hμ₁]; exact inv_mul_cancel_right _ _
  have hcond : quasiCharConductor μ₁ = n := by rw [hμ₁, conductor_twist un₂, hc]
  obtain ⟨φ₀, hs, h1, hT⟩ := hM1 (Qv v) _ hψ μ₁ μ₂ u₁ u₂ un₂ (by omega)
  have hv : ((Real.sqrt (residueCard (Qv v)) : ℝ) : ℂ) * ((μ₂ (unifUnit (Qv v)) : ℂˣ) : ℂ) = lam := by
    rw [hq, hμ₂, unrC_unif, hzv]
    field_simp
  rw [hcond, e, hv] at hT
  refine ⟨μ₁, μ₂, φ₀, u₁, u₂, e, hs, h1, ?_⟩
  have hlaw := local_whittaker_transformation_law hL hψ u₁ u₂ hs
  rw [e] at hlaw
  exact fac_gen hB hW hZ (TypeU (localChar ω v) n lam) h1 hlaw (fun A c hA => typeU_sub c hA hT)
    (fun D hD hT' h0 => hU1 (Qv v) _ hψ _ n lam D hn hlam hD hT' h0)
    (fun hh hhl g => typeU_A hB hφ hbad hhl g)

/- English proof (translation)
Establish `e : r = p ^ (((k : ℝ) - 1) / 2)`. Establish `h3 : r = (r ^ 2) ^ (1 / 2 : ℝ)` using `by rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hr]`. Rewrite using `[h3, h2, ← Real.rpow_natCast, ← Real.rpow_mul hp.le, Nat.cast_sub hk]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, ← Real.rpow_add hp, Real.sqrt_eq_rpow]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sqrt_eq_mul {p : ℝ} (hp : 0 < p) {k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hr : 0 ≤ r) (h2 : r ^ 2 = p ^ (k - 1)) :
    Real.sqrt p = p ^ (1 - (k : ℝ) / 2) * r := by
  have e : r = p ^ (((k : ℝ) - 1) / 2) := by
    have h3 : r = (r ^ 2) ^ (1 / 2 : ℝ) := by rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hr]
    rw [h3, h2, ← Real.rpow_natCast, ← Real.rpow_mul hp.le, Nat.cast_sub hk]
    congr 1
    push_cast
    ring
  rw [e, ← Real.rpow_add hp, Real.sqrt_eq_rpow]
  congr 1
  ring

/- English proof (translation)
Take `⟨hψ, hq, hp, -, -, -, -⟩` from `hB.1 v`. Establish `hp0 : (0 : ℝ) < pOf v` using `by exact_mod_cast hp.pos`. Establish `hpc : (pOf v : ℂ) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `hc0 : c ≠ 0`. Introduce `h`.

Rewrite `hcn` using `[h, norm_zero]`. Conclude with `zero_ne_one hcn`. Establish `hC0 : c * (pOf v : ℂ) ^ (k - 1) ≠ 0` using `mul_ne_zero hc0 (pow_ne_zero _ hpc)`. Take `⟨d, hd⟩` from `IsAlgClosed.exists_pow_nat_eq (A ^ 2 - 4 * (c * (pOf v : ℂ) ^ (k - 1))) (n := 2) (by norm_num)`. Take `⟨α, hα⟩ : ∃ α : ℂ, α = (A + d) / 2` from `⟨_, rfl⟩`.

Take `⟨β, hβ⟩ : ∃ β : ℂ, β = (A - d) / 2` from `⟨_, rfl⟩`. Establish `hs : α + β = A` using `by rw [hα, hβ]; ring`. Establish `hm : α * β = c * (pOf v : ℂ) ^ (k - 1)`. Rewrite using `[hα, hβ]`. Take the linear combination `(-1 / 4 : ℂ) * hd`.

Establish `hα0 : α ≠ 0` using `left_ne_zero_of_mul (hm ▸ hC0)`. Establish `hβ0 : β ≠ 0` using `right_ne_zero_of_mul (hm ▸ hC0)`. Establish `hnorm` using `hpure α β hs hm`. Take `⟨r, hrv⟩ : ∃ r : ℝ, r = ‖α‖` from `⟨_, rfl⟩`. Establish `hr0 : 0 < r` using `hrv ▸ norm_pos_iff.2 hα0`.

Establish `hr2 : r ^ 2 = (pOf v : ℝ) ^ (k - 1)`. Establish `h` using `congrArg norm hm`. Rewrite `h` using `[norm_mul, norm_mul, ← hnorm, hcn, one_mul, norm_pow, Complex.norm_natCast]`. Rewrite using `[hrv, sq]`. Conclude with `h`.

Establish `hrc : (r : ℂ) ≠ 0` using `by exact_mod_cast hr0.ne'`. Establish `hr2c : (r : ℂ) ^ 2 = (pOf v : ℂ) ^ (k - 1)` using `by exact_mod_cast hr2`. Take `⟨αU, hαU⟩ : ∃ αU : ℂˣ, (αU : ℂ) = α` from `⟨Units.mk0 α hα0, rfl⟩`. Take `⟨βU, hβU⟩ : ∃ βU : ℂˣ, (βU : ℂ) = β` from `⟨Units.mk0 β hβ0, rfl⟩`. Take `⟨rU, hrU⟩ : ∃ rU : ℂˣ, (rU : ℂ) = r` from `⟨Units.mk0 _ hrc, rfl⟩`.

Establish `hz₁ : ‖((αU / rU : ℂˣ) : ℂ)‖ = 1`. Rewrite using `[Units.val_div_eq_div_val, hαU, hrU, norm_div, Complex.norm_real, Real.norm_of_nonneg hr0.le, ← hrv, div_self hr0.ne']`. Establish `hz₂ : ‖((βU / rU : ℂˣ) : ℂ)‖ = 1`. Rewrite using `[Units.val_div_eq_div_val, hβU, hrU, norm_div, Complex.norm_real, Real.norm_of_nonneg hr0.le, ← hnorm, ← hrv, div_self hr0.ne']`. Take `⟨μ₁, hμ₁⟩ : ∃ μ₁ : (Qv v)ˣ →* ℂˣ, μ₁ = unrC (αU / rU)` from `⟨_, rfl⟩`.

Take `⟨μ₂, hμ₂⟩ : ∃ μ₂ : (Qv v)ˣ →* ℂˣ, μ₂ = unrC (βU / rU)` from `⟨_, rfl⟩`. Establish `un₁ : IsUnramifiedChar μ₁` using `hμ₁ ▸ unrC_unram _`. Establish `un₂ : IsUnramifiedChar μ₂` using `hμ₂ ▸ unrC_unram _`. Establish `u₁ : IsUnit1 μ₁` using `hμ₁ ▸ unrC_unit hz₁`. Establish `u₂ : IsUnit1 μ₂` using `hμ₂ ▸ unrC_unit hz₂`.

Establish `v₁ : μ₁ (unifUnit (Qv v)) = αU / rU` using `by rw [hμ₁, unrC_unif]`. Establish `v₂ : μ₂ (unifUnit (Qv v)) = βU / rU` using `by rw [hμ₂, unrC_unif]`. Establish `e : μ₁ * μ₂ = localChar ω v`. Use `unram_ext (unram_mul un₁ un₂) hun (Units.ext ?_)` and prove the remaining obligations. Rewrite using `[hωv, MonoidHom.mul_apply, v₁, v₂, Units.val_mul, Units.val_div_eq_div_val, Units.val_div_eq_div_val, hαU, hβU, hrU, div_mul_div_comm, hm, ← sq, hr2c]`.

Clear the denominators using the available nonvanishing facts. Take `⟨hs', h1, hT⟩` from `hM0 (Qv v) _ hψ μ₁ μ₂ u₁ u₂ un₁ un₂`. Establish `hv : ((Real.sqrt (residueCard (Qv v)) : ℝ) : ℂ) * (((μ₁ (unifUnit (Qv v)) : ℂˣ) : ℂ) + ((μ₂ (unifUnit (Qv v)) : ℂˣ) : ℂ)) = A * (((pOf v : ℝ) ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ)`. Rewrite using `[hq, v₁, v₂, Units.val_div_eq_div_val, Units.val_div_eq_div_val, hαU, hβU, hrU, sqrt_eq_mul hp0 hk hr0.le hr2, ← add_div, hs]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Rewrite `hT` using `[hv]`. Establish `hlaw` using `local_whittaker_transformation_law hL hψ u₁ u₂ hs'`. Rewrite `hlaw` using `[e]`. Use `⟨μ₁, μ₂, ind0, u₁, u₂, e, hs', h1, ?_, un₁, un₂, rfl, αU, βU, ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `fac_gen hB hW hZ (TypeT _) h1 hlaw (fun A c hA => typeT_sub c hA hT) (fun D hD hT' h0 => hU0 (Qv v) _ hψ _ _ D hD hT' h0) (fun hh hhl g => typeT_A hB hφ hgood hhl g)`. Rewrite using `[hαU, hβU, hs]`. Rewrite using `[hαU, hβU, hm]`. Rewrite using `[MonoidHom.mul_apply, MonoidHom.inv_apply, v₁, v₂, ← div_eq_mul_inv, div_div_div_cancel_right]`.
-/
theorem place_good (hL : Loc2) (hU0 : U0) (hM0 : M0) (hB : B0) {φ : G2 → ℂ} (hφ : Continuous φ)
    {ω : HeckeCharacter ℚ}
    (hW : ∀ x g, Wh φ (uni2 x * g) = (adelicChar ℚ x : ℂ) * Wh φ g)
    (hZ : ∀ (z : Jd) g, Wh φ (dg2 z z * g) = (ω.toIdele z : ℂ) * Wh φ g)
    {v : Pl} {k : ℕ} (hk : 1 ≤ k) {A c : ℂ} (hcn : ‖c‖ = 1)
    (hpure : ∀ α β : ℂ, α + β = A → α * β = c * (pOf v : ℂ) ^ (k - 1) → ‖α‖ = ‖β‖)
    (hun : IsUnramifiedChar (localChar ω v)) (hωv : ((localChar ω v (unifUnit (Qv v)) : ℂˣ) : ℂ) = c)
    (hgood : ∀ g W, LocFn v φ g W → TypeT (A * (((pOf v : ℝ) ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ)) W) :
    ∃ (μ₁ μ₂ : (Qv v)ˣ →* ℂˣ) (φ₀ : (Fin 2 → Qv v) → ℂ), IsUnit1 μ₁ ∧ IsUnit1 μ₂ ∧
      μ₁ * μ₂ = localChar ω v ∧ SB φ₀ ∧ W2 (localAdelicChar ℚ v) μ₁ μ₂ φ₀ 1 = 1 ∧
      (∀ g, finAt v g = 1 → ∀ x h, IsLoc2 v x h →
        Wh φ (g * h) = Wh φ g * W2 (localAdelicChar ℚ v) μ₁ μ₂ φ₀ x) ∧
      IsUnramifiedChar μ₁ ∧ IsUnramifiedChar μ₂ ∧ φ₀ = ind0 ∧
      ∃ α β : ℂˣ, (α : ℂ) + β = A ∧ (α : ℂ) * β = c * (pOf v : ℂ) ^ (k - 1) ∧
        (μ₁ * μ₂⁻¹) (unifUnit (Qv v)) = α / β := by
  obtain ⟨hψ, hq, hp, -, -, -, -⟩ := hB.1 v
  have hp0 : (0 : ℝ) < pOf v := by exact_mod_cast hp.pos
  have hpc : (pOf v : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hcn
    exact zero_ne_one hcn
  have hC0 : c * (pOf v : ℂ) ^ (k - 1) ≠ 0 := mul_ne_zero hc0 (pow_ne_zero _ hpc)
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (A ^ 2 - 4 * (c * (pOf v : ℂ) ^ (k - 1))) (n := 2) (by norm_num)
  obtain ⟨α, hα⟩ : ∃ α : ℂ, α = (A + d) / 2 := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℂ, β = (A - d) / 2 := ⟨_, rfl⟩
  have hs : α + β = A := by rw [hα, hβ]; ring
  have hm : α * β = c * (pOf v : ℂ) ^ (k - 1) := by
    rw [hα, hβ]
    linear_combination (-1 / 4 : ℂ) * hd
  have hα0 : α ≠ 0 := left_ne_zero_of_mul (hm ▸ hC0)
  have hβ0 : β ≠ 0 := right_ne_zero_of_mul (hm ▸ hC0)
  have hnorm := hpure α β hs hm
  obtain ⟨r, hrv⟩ : ∃ r : ℝ, r = ‖α‖ := ⟨_, rfl⟩
  have hr0 : 0 < r := hrv ▸ norm_pos_iff.2 hα0
  have hr2 : r ^ 2 = (pOf v : ℝ) ^ (k - 1) := by
    have h := congrArg norm hm
    rw [norm_mul, norm_mul, ← hnorm, hcn, one_mul, norm_pow, Complex.norm_natCast] at h
    rw [hrv, sq]
    exact h
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hr2c : (r : ℂ) ^ 2 = (pOf v : ℂ) ^ (k - 1) := by exact_mod_cast hr2
  obtain ⟨αU, hαU⟩ : ∃ αU : ℂˣ, (αU : ℂ) = α := ⟨Units.mk0 α hα0, rfl⟩
  obtain ⟨βU, hβU⟩ : ∃ βU : ℂˣ, (βU : ℂ) = β := ⟨Units.mk0 β hβ0, rfl⟩
  obtain ⟨rU, hrU⟩ : ∃ rU : ℂˣ, (rU : ℂ) = r := ⟨Units.mk0 _ hrc, rfl⟩
  have hz₁ : ‖((αU / rU : ℂˣ) : ℂ)‖ = 1 := by
    rw [Units.val_div_eq_div_val, hαU, hrU, norm_div, Complex.norm_real, Real.norm_of_nonneg hr0.le, ← hrv,
      div_self hr0.ne']
  have hz₂ : ‖((βU / rU : ℂˣ) : ℂ)‖ = 1 := by
    rw [Units.val_div_eq_div_val, hβU, hrU, norm_div, Complex.norm_real, Real.norm_of_nonneg hr0.le, ← hnorm, ← hrv,
      div_self hr0.ne']
  obtain ⟨μ₁, hμ₁⟩ : ∃ μ₁ : (Qv v)ˣ →* ℂˣ, μ₁ = unrC (αU / rU) := ⟨_, rfl⟩
  obtain ⟨μ₂, hμ₂⟩ : ∃ μ₂ : (Qv v)ˣ →* ℂˣ, μ₂ = unrC (βU / rU) := ⟨_, rfl⟩
  have un₁ : IsUnramifiedChar μ₁ := hμ₁ ▸ unrC_unram _
  have un₂ : IsUnramifiedChar μ₂ := hμ₂ ▸ unrC_unram _
  have u₁ : IsUnit1 μ₁ := hμ₁ ▸ unrC_unit hz₁
  have u₂ : IsUnit1 μ₂ := hμ₂ ▸ unrC_unit hz₂
  have v₁ : μ₁ (unifUnit (Qv v)) = αU / rU := by rw [hμ₁, unrC_unif]
  have v₂ : μ₂ (unifUnit (Qv v)) = βU / rU := by rw [hμ₂, unrC_unif]
  have e : μ₁ * μ₂ = localChar ω v := by
    refine unram_ext (unram_mul un₁ un₂) hun (Units.ext ?_)
    rw [hωv, MonoidHom.mul_apply, v₁, v₂, Units.val_mul, Units.val_div_eq_div_val, Units.val_div_eq_div_val,
      hαU, hβU, hrU, div_mul_div_comm, hm, ← sq, hr2c]
    field_simp
  obtain ⟨hs', h1, hT⟩ := hM0 (Qv v) _ hψ μ₁ μ₂ u₁ u₂ un₁ un₂
  have hv : ((Real.sqrt (residueCard (Qv v)) : ℝ) : ℂ) *
      (((μ₁ (unifUnit (Qv v)) : ℂˣ) : ℂ) + ((μ₂ (unifUnit (Qv v)) : ℂˣ) : ℂ)) =
      A * (((pOf v : ℝ) ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ) := by
    rw [hq, v₁, v₂, Units.val_div_eq_div_val, Units.val_div_eq_div_val, hαU, hβU, hrU,
      sqrt_eq_mul hp0 hk hr0.le hr2, ← add_div, hs]
    push_cast
    field_simp
  rw [hv] at hT
  have hlaw := local_whittaker_transformation_law hL hψ u₁ u₂ hs'
  rw [e] at hlaw
  refine ⟨μ₁, μ₂, ind0, u₁, u₂, e, hs', h1, ?_, un₁, un₂, rfl, αU, βU, ?_, ?_, ?_⟩
  · exact fac_gen hB hW hZ (TypeT _) h1 hlaw (fun A c hA => typeT_sub c hA hT)
      (fun D hD hT' h0 => hU0 (Qv v) _ hψ _ _ D hD hT' h0)
      (fun hh hhl g => typeT_A hB hφ hgood hhl g)
  · rw [hαU, hβU, hs]
  · rw [hαU, hβU, hm]
  · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, v₁, v₂, ← div_eq_mul_inv, div_div_div_cancel_right]

end Places

/- English proof (translation)
Introduce `hL hB hU0 hU1 hM0 hM1 hF0b hF1 hF2 hF3 hF4 k N _ hk χ hχ f a hf he ω φ hOm hLift hPure`. Establish `h1` using `hF1 k N χ f a hf he.2.1 ω hOm`. Establish `hOL` using `hF0b k N χ hχ h1.1 ω hOm`. Take `⟨-, hW, hZ, -⟩` from `hF2 k N hk χ hχ f a hf he ω φ hOm hLift`. Establish `hH` using `hF3 k N hk χ hχ f a hf he ω φ hOm hLift`.

Establish `h4` using `hF4 k N hk χ hχ f a hf he ω φ hOm hLift`. Establish `hφ` using `hLift.cont`. Establish `place : ∀ v : Pl, ∃ (μ₁ μ₂ : (Qv v)ˣ →* ℂˣ) (φ₀ : (Fin 2 → Qv v) → ℂ), IsUnit1 μ₁ ∧ IsUnit1 μ₂ ∧ μ₁ * μ₂ = localChar ω v ∧ SB φ₀ ∧ W2 (localAdelicChar ℚ v) μ₁ μ₂ φ₀ 1 = 1 ∧ (∀ g, finAt v g = 1 → ∀ x h, IsLoc2 v x h → Wh φ (g * h) = Wh φ g * W2 (localAdelicChar ℚ v) μ₁ μ₂ φ₀ x) ∧ …`. Introduce `v`. Establish `hp : (pOf v).Prime` using `(hB.1 v).2.2.1`.

Distinguish the cases in `hv : pOf v ∣ N`. Take `⟨μ₁, μ₂, φ₀, u₁, u₂, e, hs, ho, hfac⟩` from `place_bad hL hU1 hM1 hB hφ hW hZ (hp.factorization_pos_of_dvd (NeZero.ne N) hv) (hOL.bad v hv) (h4 v hv) (hH.bad v hv)`. Conclude with `⟨μ₁, μ₂, φ₀, u₁, u₂, e, hs, ho, hfac, fun h => absurd hv h⟩`. Establish `hu : IsUnit ((pOf v : ℕ) : ZMod N)` using `(ZMod.isUnit_iff_coprime _ _).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hv)`. Establish `hcn : ‖χ (pOf v)‖ = 1`.

Use `DirichletCharacter.unit_norm_eq_one χ hu.unit` as an intermediate fact. Simplify using `using this`. Take `⟨μ₁, μ₂, φ₀, u₁, u₂, e, hs, ho, hfac, r⟩` from `place_good hL hU0 hM0 hB hφ hW hZ (by omega : 1 ≤ k) hcn (hPure (pOf v) hp hv) (hOL.good v hv).1 (hOL.good v hv).2 (hH.good v hv)`. Conclude with `⟨μ₁, μ₂, φ₀, u₁, u₂, e, hs, ho, hfac, fun _ => r⟩`. Use `choose μ₁ μ₂ φ₀ u₁ u₂ e hs ho hfac hg using place`.

Use `⟨μ₁, μ₂, φ₀, ⟨u₁, u₂, e, hs, ho, fun v hv => ?_, hfac⟩, fun v hv => ?_⟩` and prove the remaining obligations. Conclude with `⟨(hg v hv).1, (hg v hv).2.1, (hg v hv).2.2.1⟩`. Conclude with `(hg v hv).2.2.2`.
-/
theorem f7 : Ad3.Loc2 → Ad3.R.B0 → Ad3.R.U0 → Ad3.R.U1 → Ad3.R.M0 → Ad3.R.M1 → Ad3.R.F0b → Ad3.R.F1 →
    Ad3.R.F2 → Ad3.R.F3 → Ad3.R.F4 → Ad3.R.F7 := by
  intro hL hB hU0 hU1 hM0 hM1 hF0b hF1 hF2 hF3 hF4 k N _ hk χ hχ f a hf he ω φ hOm hLift hPure
  have h1 := hF1 k N χ f a hf he.2.1 ω hOm
  have hOL := hF0b k N χ hχ h1.1 ω hOm
  obtain ⟨-, hW, hZ, -⟩ := hF2 k N hk χ hχ f a hf he ω φ hOm hLift
  have hH := hF3 k N hk χ hχ f a hf he ω φ hOm hLift
  have h4 := hF4 k N hk χ hχ f a hf he ω φ hOm hLift
  have hφ := hLift.cont
  have place : ∀ v : Pl, ∃ (μ₁ μ₂ : (Qv v)ˣ →* ℂˣ) (φ₀ : (Fin 2 → Qv v) → ℂ), IsUnit1 μ₁ ∧ IsUnit1 μ₂ ∧
      μ₁ * μ₂ = localChar ω v ∧ SB φ₀ ∧ W2 (localAdelicChar ℚ v) μ₁ μ₂ φ₀ 1 = 1 ∧
      (∀ g, finAt v g = 1 → ∀ x h, IsLoc2 v x h →
        Wh φ (g * h) = Wh φ g * W2 (localAdelicChar ℚ v) μ₁ μ₂ φ₀ x) ∧
      (¬ pOf v ∣ N → IsUnramifiedChar μ₁ ∧ IsUnramifiedChar μ₂ ∧ φ₀ = ind0 ∧
        ∃ α β : ℂˣ, (α : ℂ) + β = a (pOf v) ∧ (α : ℂ) * β = χ (pOf v) * (pOf v : ℂ) ^ (k - 1) ∧
          (μ₁ * μ₂⁻¹) (unifUnit (Qv v)) = α / β) := by
    intro v
    have hp : (pOf v).Prime := (hB.1 v).2.2.1
    by_cases hv : pOf v ∣ N
    · obtain ⟨μ₁, μ₂, φ₀, u₁, u₂, e, hs, ho, hfac⟩ := place_bad hL hU1 hM1 hB hφ hW hZ
        (hp.factorization_pos_of_dvd (NeZero.ne N) hv) (hOL.bad v hv) (h4 v hv) (hH.bad v hv)
      exact ⟨μ₁, μ₂, φ₀, u₁, u₂, e, hs, ho, hfac, fun h => absurd hv h⟩
    · have hu : IsUnit ((pOf v : ℕ) : ZMod N) :=
        (ZMod.isUnit_iff_coprime _ _).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hv)
      have hcn : ‖χ (pOf v)‖ = 1 := by
        have := DirichletCharacter.unit_norm_eq_one χ hu.unit
        simpa using this
      obtain ⟨μ₁, μ₂, φ₀, u₁, u₂, e, hs, ho, hfac, r⟩ := place_good hL hU0 hM0 hB hφ hW hZ (by omega : 1 ≤ k)
        hcn (hPure (pOf v) hp hv) (hOL.good v hv).1 (hOL.good v hv).2 (hH.good v hv)
      exact ⟨μ₁, μ₂, φ₀, u₁, u₂, e, hs, ho, hfac, fun _ => r⟩
  choose μ₁ μ₂ φ₀ u₁ u₂ e hs ho hfac hg using place
  refine ⟨μ₁, μ₂, φ₀, ⟨u₁, u₂, e, hs, ho, fun v hv => ?_, hfac⟩, fun v hv => ?_⟩
  · exact ⟨(hg v hv).1, (hg v hv).2.1, (hg v hv).2.2.1⟩
  · exact (hg v hv).2.2.2

end GlobalTheory.CompanionTheory.NewformLiftLocalWhittaker
end
