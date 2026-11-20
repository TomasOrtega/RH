import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecMapApply
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCoinvQuotEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocallyConstantSplitOm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagCoIsotropic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatAnyCharacter

noncomputable section

open GlobalTheory.WeilM GlobalTheory.LinPair MeasureTheory Matrix ValuativeRel Filter
open scoped Topology

namespace GlobalTheory.HypPair

/- English proof (translation)
Use `choose M hM1 hM2 using hM`. Establish `uniq : ∀ g (T : Module.End ℂ V), (∀ w, T * ρ w = ρ (a g w) * T) → ∃ z : ℂ, T = z • (M g).val`. Introduce `g T hT`. Take `⟨z, hz⟩` from `schur (((M g)⁻¹).val * T) fun w => by`. Rewrite using `[mul_assoc, hT, ← mul_assoc, ← mul_assoc]`.

Use `congr 1`. Rewrite using `[Units.inv_mul_eq_iff_eq_mul, ← mul_assoc, hM1, Units.mul_inv_cancel_right]`. Conclude with `⟨z, by rw [Units.inv_mul_eq_iff_eq_mul] at hz; rw [hz, mul_smul_comm, mul_one]⟩`. Establish `one : ∀ z : ℂ, z • l = l → z = 1` using `fun z hz => smul_left_injective ℂ hl (hz.trans (one_smul ℂ l).symm)`. Establish `uniq' : ∀ g (T : Module.End ℂ V), (∀ w, T * ρ w = ρ (a g w) * T) → l ∘ₗ T = l → T = (M g).val`.

Introduce `g T hT hlT`. Take `⟨z, hz⟩` from `uniq g T hT`. Rewrite `hlT` using `[hz, LinearMap.comp_smul, hM2]`. Rewrite using `[hz, one z hlT, one_smul]`. Use `⟨{ toFun := fun g => (M g).val map_one' := (uniq' 1 1 (fun w => by rw [a_one, one_mul, mul_one]) rfl).symm map_mul' := fun g g' => (uniq' _ _ (fun w => by` and prove the remaining obligations.

Rewrite using `[mul_assoc, hM1, ← mul_assoc, hM1, a_mul, mul_assoc]) (by`. Rewrite using `[Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hM2, hM2])).symm }, hM1, hM2, fun g h => ?_⟩`. Establish `ex : ∀ h, ∃ z : ℂ, om h * (M g).val * om h⁻¹ = z • (M g).val` using `fun h => uniq g _ fun w => by`. Rewrite using `[mul_assoc, hom, ← mul_assoc, mul_assoc (om h), hM1, ← mul_assoc, hom, hab, b_inv, mul_assoc, mul_assoc, mul_assoc]`. Use `choose z hz using ex`.

Establish `hne : (M g).val ≠ 0` using `fun h0 => hl (by rw [← hM2 g, h0, LinearMap.comp_zero])`. Establish `hz' : ∀ h, om h * (M g).val = z h • ((M g).val * om h)` using `fun h => by`. Rewrite using `[← smul_mul_assoc, ← hz, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]`. Set `χ : H →* ℂ` to `{ toFun := z map_one' := smul_left_injective ℂ hne (by simp only [← hz]; simp) map_mul' := fun h h' => smul_left_injective ℂ hne (by`. Simplify using `only [mul_smul]`.

Rewrite using `[smul_comm, ← hz, ← hz h, ← smul_mul_assoc, ← mul_smul_comm, ← hz h', _root_.mul_inv_rev, map_mul, map_mul]`. Simplify using `only [mul_assoc]) }`. Establish `h1 : z h = 1` using `hχ χ (fun p hp => by`. Take `⟨y, hy0, hy⟩` from `hP p hp`. Establish `e` using `congrArg (fun T => l ∘ₗ T) (hz' p)`.

Simplify using `only [Module.End.mul_eq_comp, LinearMap.comp_smul, ← LinearMap.comp_assoc, hy, hM2, LinearMap.smul_comp] at e`. Rewrite `e` using `[smul_comm]`. Conclude with `one _ (smul_right_injective _ hy0 e).symm) h`. Use `show (M g).val * om h = om h * (M g).val`. Rewrite using `[hz', h1, one_smul]`.
-/
theorem exists_hom_commute {V W G H : Type} [AddCommGroup V] [Module ℂ V] [Group G] [Group H] (ρ : W → Module.End ℂ V)
    (schur : ∀ T : Module.End ℂ V, (∀ w, T * ρ w = ρ w * T) → ∃ z : ℂ, T = z • (1 : Module.End ℂ V))
    (a : G → W → W) (a_one : ∀ w, a 1 w = w) (a_mul : ∀ g g' w, a (g * g') w = a g (a g' w))
    (b : H → W → W) (b_inv : ∀ h w, b h (b h⁻¹ w) = w) (hab : ∀ g h w, a g (b h w) = b h (a g w))
    (om : H →* Module.End ℂ V) (hom : ∀ h w, om h * ρ w = ρ (b h w) * om h) (l : V →ₗ[ℂ] ℂ) (hl : l ≠ 0)
    (hM : ∀ g, ∃ T : (Module.End ℂ V)ˣ, (∀ w, T.val * ρ w = ρ (a g w) * T.val) ∧ l ∘ₗ T.val = l)
    (P : Set H) (hP : ∀ p ∈ P, ∃ z : ℂ, z ≠ 0 ∧ l ∘ₗ om p = z • l)
    (hχ : ∀ χ : H →* ℂ, (∀ p ∈ P, χ p = 1) → ∀ h, χ h = 1) :
    ∃ M : G →* Module.End ℂ V, (∀ g w, M g * ρ w = ρ (a g w) * M g) ∧ (∀ g, l ∘ₗ M g = l) ∧
      ∀ g h, Commute (M g) (om h) := by
  choose M hM1 hM2 using hM
  have uniq : ∀ g (T : Module.End ℂ V), (∀ w, T * ρ w = ρ (a g w) * T) → ∃ z : ℂ, T = z • (M g).val := by
    intro g T hT
    obtain ⟨z, hz⟩ := schur (((M g)⁻¹).val * T) fun w => by
      rw [mul_assoc, hT, ← mul_assoc, ← mul_assoc]
      congr 1
      rw [Units.inv_mul_eq_iff_eq_mul, ← mul_assoc, hM1, Units.mul_inv_cancel_right]
    exact ⟨z, by rw [Units.inv_mul_eq_iff_eq_mul] at hz; rw [hz, mul_smul_comm, mul_one]⟩
  have one : ∀ z : ℂ, z • l = l → z = 1 := fun z hz =>
    smul_left_injective ℂ hl (hz.trans (one_smul ℂ l).symm)
  have uniq' : ∀ g (T : Module.End ℂ V), (∀ w, T * ρ w = ρ (a g w) * T) → l ∘ₗ T = l → T = (M g).val := by
    intro g T hT hlT
    obtain ⟨z, hz⟩ := uniq g T hT
    rw [hz, LinearMap.comp_smul, hM2] at hlT
    rw [hz, one z hlT, one_smul]
  refine ⟨{ toFun := fun g => (M g).val
            map_one' := (uniq' 1 1 (fun w => by rw [a_one, one_mul, mul_one]) rfl).symm
            map_mul' := fun g g' => (uniq' _ _ (fun w => by
              rw [mul_assoc, hM1, ← mul_assoc, hM1, a_mul, mul_assoc]) (by
                rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hM2, hM2])).symm }, hM1, hM2, fun g h => ?_⟩
  have ex : ∀ h, ∃ z : ℂ, om h * (M g).val * om h⁻¹ = z • (M g).val := fun h => uniq g _ fun w => by
    rw [mul_assoc, hom, ← mul_assoc, mul_assoc (om h), hM1, ← mul_assoc, hom, hab, b_inv, mul_assoc, mul_assoc, mul_assoc]
  choose z hz using ex
  have hne : (M g).val ≠ 0 := fun h0 => hl (by rw [← hM2 g, h0, LinearMap.comp_zero])
  have hz' : ∀ h, om h * (M g).val = z h • ((M g).val * om h) := fun h => by
    rw [← smul_mul_assoc, ← hz, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  let χ : H →* ℂ :=
    { toFun := z
      map_one' := smul_left_injective ℂ hne (by simp only [← hz]; simp)
      map_mul' := fun h h' => smul_left_injective ℂ hne (by
        simp only [mul_smul]
        rw [smul_comm, ← hz, ← hz h, ← smul_mul_assoc, ← mul_smul_comm, ← hz h', _root_.mul_inv_rev, map_mul, map_mul]
        simp only [mul_assoc]) }
  have h1 : z h = 1 := hχ χ (fun p hp => by
    obtain ⟨y, hy0, hy⟩ := hP p hp
    have e := congrArg (fun T => l ∘ₗ T) (hz' p)
    simp only [Module.End.mul_eq_comp, LinearMap.comp_smul, ← LinearMap.comp_assoc, hy, hM2, LinearMap.smul_comp] at e
    rw [smul_comm] at e
    exact one _ (smul_right_injective _ hy0 e).symm) h
  show (M g).val * om h = om h * (M g).val
  rw [hz', h1, one_smul]

/- English proof (translation)
Take `⟨Q, hQ⟩` from `S.exists_isCompl`. Use `⟨((S.prodEquivOfIsCompl Q hQ).conjRingEquiv.toRingHom.toMonoidHom.comp (LinearMap.prodMapRingHom ℂ S Q).toMonoidHom).comp (MonoidHom.inl _ _), fun T v => ?_⟩` and prove the remaining obligations. Simplify using `[LinearEquiv.conjRingEquiv, LinearEquiv.arrowCongrAddEquiv]`.
-/
theorem exists_extend_hom {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) :
    ∃ x : Module.End ℂ S →* Module.End ℂ V, ∀ T (v : S), x T v = T v := by
  obtain ⟨Q, hQ⟩ := S.exists_isCompl
  refine ⟨((S.prodEquivOfIsCompl Q hQ).conjRingEquiv.toRingHom.toMonoidHom.comp
    (LinearMap.prodMapRingHom ℂ S Q).toMonoidHom).comp (MonoidHom.inl _ _), fun T v => ?_⟩
  simp [LinearEquiv.conjRingEquiv, LinearEquiv.arrowCongrAddEquiv]

section Char

variable {k E : Type} [Field k] [Field E] [Algebra k E] {c : E →ₐ[k] E}

def slU (x y z t : E) (hx : c x = x) (hy : c y = y) (hz : c z = z) (ht : c t = t) (h : x * t - y * z = 1) :
    UG c (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) E) :=
  ⟨GeneralLinearGroup.mkOfDetNeZero !![x, y; z, t] (by rw [det_fin_two_of, h]; exact one_ne_zero), by
    show (!![x, y; z, t])ᵀ * _ * (!![x, y; z, t]).map c = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, hx, hy, hz, ht, vecMul, dotProduct] <;>
      first | ring1 | linear_combination h | linear_combination -h⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem slU_val (x y z t : E) (hx : c x = x) (hy : c y = y) (hz : c z = z) (ht : c t = t) (h : x * t - y * z = 1) :
    ((slU x y z t hx hy hz ht h : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) = !![x, y; z, t] := rfl

/- English proof (translation)
Set `w : UG c (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) E)` to `slU 0 1 (-1) 0 (by simp) (by simp) (by simp) (by simp) (by simp)`. Set `n : ∀ s : E, c s = s → UG c (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) E)` to `fun s hs => slU 1 s 0 1 (by simp) hs (by simp) (by simp) (by simp)`. Establish `hn : ∀ s hs, χ (n s hs) = 1` using `fun s hs => hχ _ rfl`. Establish `e : w * w = n 1 (map_one c) * w * n 1 (map_one c) * (w * w * w) * n 1 (map_one c) * w`. Use `Subtype.ext (Units.ext ?_)` and prove the remaining obligations.

Simplify using `only [Subgroup.coe_mul, Units.val_mul, w, n, slU_val]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`. Establish `hww : χ (w * w) = 1` using `hχ _ (by simp [w, slU_val])`. Establish `hw : χ w = 1`.

Use `congrArg χ e` as an intermediate fact. Rewrite `this` using `[hww]`. Rewrite `hww` using `[map_mul]`. Simplify using `only [map_mul, hn, hww, one_mul, mul_one] at this`. Conclude with `this.symm`.

Distinguish the cases in `h0 : (h : GL (Fin 2) E).val 1 0 = 0`. Conclude with `hχ h h0`. Establish `h1` using `congrFun (congrFun (show (h : GL (Fin 2) E).valᵀ * _ * (h : GL (Fin 2) E).val.map c = _ from h.2) 0) 0`. Simplify using `[mul_apply, Fin.sum_univ_two, vecMul, dotProduct] at h1`. Establish `h2 : c ((h : GL (Fin 2) E).val 1 0) ≠ 0` using `(map_ne_zero c).2 h0`.

Establish `hs : c (-((h : GL (Fin 2) E).val 0 0 / (h : GL (Fin 2) E).val 1 0)) = -((h : GL (Fin 2) E).val 0 0 / (h : GL (Fin 2) E).val 1 0)`. Rewrite using `[map_neg, map_div₀, neg_inj, div_eq_div_iff h2 h0]`. Take the linear combination `-h1`. Use `hχ (w * n _ hs * h) (by` as an intermediate fact. Simplify using `only [Subgroup.coe_mul, Units.val_mul, w, n, slU_val]`.

Simplify using `[mul_apply, Fin.sum_univ_two, vecMul, dotProduct, h0])`. Rewrite `this` using `[map_mul, map_mul, hw, hn, one_mul, one_mul]`. Then use the resulting hypothesis.
-/
theorem char_eq_one (χ : UG c (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) E) →* ℂ)
    (hχ : ∀ p : UG c (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) E), (p : GL (Fin 2) E).val 1 0 = 0 → χ p = 1)
    (h : UG c (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) E)) : χ h = 1 := by
  let w : UG c (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) E) := slU 0 1 (-1) 0 (by simp) (by simp) (by simp) (by simp) (by simp)
  let n : ∀ s : E, c s = s → UG c (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) E) := fun s hs =>
    slU 1 s 0 1 (by simp) hs (by simp) (by simp) (by simp)
  have hn : ∀ s hs, χ (n s hs) = 1 := fun s hs => hχ _ rfl
  have e : w * w = n 1 (map_one c) * w * n 1 (map_one c) * (w * w * w) * n 1 (map_one c) * w := by
    refine Subtype.ext (Units.ext ?_)
    simp only [Subgroup.coe_mul, Units.val_mul, w, n, slU_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hww : χ (w * w) = 1 := hχ _ (by simp [w, slU_val])
  have hw : χ w = 1 := by
    have := congrArg χ e
    rw [hww] at this
    rw [map_mul] at hww
    simp only [map_mul, hn, hww, one_mul, mul_one] at this
    exact this.symm
  by_cases h0 : (h : GL (Fin 2) E).val 1 0 = 0
  · exact hχ h h0
  have h1 := congrFun (congrFun (show (h : GL (Fin 2) E).valᵀ * _ * (h : GL (Fin 2) E).val.map c = _ from h.2) 0) 0
  simp [mul_apply, Fin.sum_univ_two, vecMul, dotProduct] at h1
  have h2 : c ((h : GL (Fin 2) E).val 1 0) ≠ 0 := (map_ne_zero c).2 h0
  have hs : c (-((h : GL (Fin 2) E).val 0 0 / (h : GL (Fin 2) E).val 1 0)) =
      -((h : GL (Fin 2) E).val 0 0 / (h : GL (Fin 2) E).val 1 0) := by
    rw [map_neg, map_div₀, neg_inj, div_eq_div_iff h2 h0]
    linear_combination -h1
  have := hχ (w * n _ hs * h) (by
    simp only [Subgroup.coe_mul, Units.val_mul, w, n, slU_val]
    simp [mul_apply, Fin.sum_univ_two, vecMul, dotProduct, h0])
  rwa [map_mul, map_mul, hw, hn, one_mul, one_mul] at this

end Char

section Schr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  {ψ : AddChar k ℂ} {κ : Type} [Fintype κ]

/- English proof (translation)
Use `nonarch_field k` as an intermediate fact. Conclude with `⟨((isLocallyConstant_addChar ψ hψ).comp_continuous ((continuous_id.dotProduct continuous_const).add continuous_const)).mul (hφ.1.comp_continuous (continuous_id.add continuous_const)), (hφ.2.comp_homeomorph (Homeomorph.addRight w.1)).mul_left⟩`.
-/
theorem schr_mem (hψ : Continuous ψ) (w : (κ → k) × (κ → k)) {φ : (κ → k) → ℂ} (hφ : φ ∈ SB (κ → k)) :
    schr ψ w φ ∈ SB (κ → k) := by
  have := nonarch_field k
  exact ⟨((isLocallyConstant_addChar ψ hψ).comp_continuous
      ((continuous_id.dotProduct continuous_const).add continuous_const)).mul
    (hφ.1.comp_continuous (continuous_id.add continuous_const)),
    (hφ.2.comp_homeomorph (Homeomorph.addRight w.1)).mul_left⟩

def schrS (hψ : Continuous ψ) (w : (κ → k) × (κ → k)) : Module.End ℂ (SB (κ → k)) :=
  (GlobalTheory.VacLoc.schrL ψ w).restrict fun _ hφ => schr_mem hψ w hφ

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem schrS_coe (hψ : Continuous ψ) (w : (κ → k) × (κ → k)) (φ : SB (κ → k)) :
    (schrS hψ w φ : (κ → k) → ℂ) = schr ψ w φ := rfl

/- English proof (translation)
Use `GlobalTheory.SplitWeil.t2Space k` as an intermediate fact. Set `ev : ((κ → k) → ℂ) →ₗ[ℂ] ℂ` to `LinearMap.proj 0`. Take `⟨l, hl⟩` from `LinearMap.exists_extend (ev ∘ₗ (SB (κ → k)).subtype ∘ₗ T)`. Establish `hl' : ∀ φ : SB (κ → k), l φ = (T φ).1 0` using `fun φ => LinearMap.congr_fun hl φ`. Establish `hT' : ∀ w φ, (T (schrS hψ w φ)).1 = schr ψ w (T φ).1` using `fun w φ => congrArg Subtype.val (LinearMap.congr_fun (hT w) φ)`.

Take `⟨z, hz⟩` from `GlobalTheory.LagrInvForm.proportional k ψ hψ hψ1 κ (LinearMap.range (LinearMap.inr k _ _)) (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; simp) (by rw [LinearMap.finrank_range_of_inj LinearMap.inr_injective, Module.finrank_fintype_fun_eq_card]) l ev (by`. Introduce and unpack `_ ⟨a, rfl⟩ φ hφ`. Rewrite using `[← schrS_coe hψ _ ⟨φ, hφ⟩, hl', hT', hl' ⟨φ, hφ⟩]`. Simplify using `[schr])`. Use the proof step `(by rintro _ ⟨a, rfl⟩ φ _; simp [ev, schr])`.

Use the proof step `(by`. Take `⟨U, hUo, hUc, hU0⟩` from `GlobalTheory.LagrFormLine.exists_compact_open k κ`. Conclude with `⟨U.indicator fun _ => (1 : ℂ), ⟨(LocallyConstant.charFn ℂ (⟨hUc.isClosed, hUo⟩ : IsClopen U)).isLocallyConstant, HasCompactSupport.intro hUc fun x hx => Set.indicator_of_notMem hx _⟩, by simp [ev, hU0]⟩)`. Use `⟨z, LinearMap.ext fun φ => Subtype.ext (funext fun x => ?_)⟩` and prove the remaining obligations. Establish `h1` using `hz _ (schrS hψ (x, 0) φ).2`.

Rewrite `h1` using `[hl', hT', schrS_coe]`. Simplify `h1` using `[schr, ev]`.
-/
theorem schur (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (T : Module.End ℂ (SB (κ → k)))
    (hT : ∀ w, T * schrS hψ w = schrS hψ w * T) : ∃ z : ℂ, T = z • (1 : Module.End ℂ (SB (κ → k))) := by
  have := GlobalTheory.SplitWeil.t2Space k
  let ev : ((κ → k) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj 0
  obtain ⟨l, hl⟩ := LinearMap.exists_extend (ev ∘ₗ (SB (κ → k)).subtype ∘ₗ T)
  have hl' : ∀ φ : SB (κ → k), l φ = (T φ).1 0 := fun φ => LinearMap.congr_fun hl φ
  have hT' : ∀ w φ, (T (schrS hψ w φ)).1 = schr ψ w (T φ).1 := fun w φ => congrArg Subtype.val (LinearMap.congr_fun (hT w) φ)
  obtain ⟨z, hz⟩ := GlobalTheory.LagrInvForm.proportional k ψ hψ hψ1 κ (LinearMap.range (LinearMap.inr k _ _))
    (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; simp)
    (by rw [LinearMap.finrank_range_of_inj LinearMap.inr_injective, Module.finrank_fintype_fun_eq_card]) l ev
    (by
      rintro _ ⟨a, rfl⟩ φ hφ
      rw [← schrS_coe hψ _ ⟨φ, hφ⟩, hl', hT', hl' ⟨φ, hφ⟩]
      simp [schr])
    (by rintro _ ⟨a, rfl⟩ φ _; simp [ev, schr])
    (by
      obtain ⟨U, hUo, hUc, hU0⟩ := GlobalTheory.LagrFormLine.exists_compact_open k κ
      exact ⟨U.indicator fun _ => (1 : ℂ),
        ⟨(LocallyConstant.charFn ℂ (⟨hUc.isClosed, hUo⟩ : IsClopen U)).isLocallyConstant,
          HasCompactSupport.intro hUc fun x hx => Set.indicator_of_notMem hx _⟩, by simp [ev, hU0]⟩)
  refine ⟨z, LinearMap.ext fun φ => Subtype.ext (funext fun x => ?_)⟩
  have h1 := hz _ (schrS hψ (x, 0) φ).2
  rw [hl', hT', schrS_coe] at h1
  simpa [schr, ev] using h1

/- English proof (translation)
Set `r : Matrix (Fin 1) (Fin n) k →+ (Fin n → k)` to `Pi.evalAddMonoidHom (fun _ : Fin 1 => Fin n → k) 0`. Take `⟨ι, hι, hT, hM⟩` from `GlobalTheory.SvNAnyChar.stoneVonNeumann_any_char ψ hψ hψ1 ((σ.toLinearMap ∘ₗ LinearMap.inl k _ _).toAddMonoidHom.comp r) ((σ.toLinearMap ∘ₗ LinearMap.inr k _ _).toAddMonoidHom.comp r) (fun Y Y' => (hσ _ _).trans (by simp)) (fun Y Y' => (hσ _ _).trans (by simp)) (fun Y z => (hσ _ …`. Rewrite using `[← map_add]`. Use the proof step `simp⟩)`. Set `h : (Fin n → k) ≃ₜ Matrix (Fin 1) (Fin n) k` to `(Homeomorph.funUnique (Fin 1) (Fin n → k)).symm`.

Establish `hsb : ∀ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y), ∀ f ∈ SB Y, f ∘ e ∈ SB X` using `fun e f hf => ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩`. Set `T : Module.End ℂ (SB (Fin n → k))` to `(LinearMap.funLeft ℂ ℂ h ∘ₗ ι).restrict fun φ hφ => hsb h _ (hι.1 hφ)`. Establish `hTc : ∀ φ, (T φ).1 = ι φ ∘ h` using `fun _ => rfl`. Establish `hb : Function.Bijective T` using `⟨fun φ φ' e => Subtype.ext (hι.2.1 φ.2 φ'.2 (h.surjective.right_cancellable.1 (congrArg Subtype.val e))), fun φ => by`. Take `⟨f, hf, e⟩` from `hι.2.2 (hsb h.symm _ φ.2)`.

Use `⟨⟨f, hf⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hTc, e]`. Use function extensionality and compare the values at `x`. Use the proof step `simp⟩`. Use `⟨((Module.End.isUnit_iff T).2 hb).unit, fun w => LinearMap.ext fun φ => Subtype.ext ?_⟩` and prove the remaining obligations.

Use `show (T (schrS hψ (σ w) φ)).1 = schr ψ w (T φ).1`. Establish `e1` using `schr_schr ψ (σ (0, w.2)) (σ (w.1, 0)) φ`. Establish `e2` using `schr_schr ψ (0, w.2) (w.1, 0) (T φ).1`. Rewrite `e1` using `[hσ, ← map_add]`. Simplify using `only [Prod.mk_add_mk, zero_add, add_zero, Prod.mk.eta] at e1 e2`.

Establish `hne : ∀ t, ψ t ≠ 0` using `fun t => (ψ.val_isUnit t).ne_zero`. Use `smul_right_injective _ (hne _) (Eq.trans ?_ e2)` and prove the remaining obligations. Establish `e3` using `hT (h w.1) φ φ.2`. Establish `e4` using `hM (h w.2) _ (schr_mem hψ (σ (w.1, 0)) φ.2)`. Use `show _ • (ι (schr ψ (σ w) φ) ∘ h) = _`.

Rewrite using `[← Pi.smul_comp, ← map_smul, ← e1]`. Use `(congrArg (· ∘ h) e4).trans ?_` and prove the remaining obligations. Rewrite using `[show ι (schr ψ (σ (w.1, 0)) φ) = _ from e3, hTc]`. Use function extensionality and compare the values at `x`. Simplify using `[schr, dotProduct]`.

Both sides reduce to the same expression.
-/
theorem exists_implementer [CharZero k] {n : ℕ} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (σ : ((Fin n → k) × (Fin n → k)) ≃ₗ[k] ((Fin n → k) × (Fin n → k)))
    (hσ : ∀ w w', (σ w).1 ⬝ᵥ (σ w').2 - (σ w').1 ⬝ᵥ (σ w).2 = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) :
    ∃ T : (Module.End ℂ (SB (Fin n → k)))ˣ, ∀ w, T.val * schrS hψ (σ w) = schrS hψ w * T.val := by
  let r : Matrix (Fin 1) (Fin n) k →+ (Fin n → k) := Pi.evalAddMonoidHom (fun _ : Fin 1 => Fin n → k) 0
  obtain ⟨ι, hι, hT, hM⟩ := GlobalTheory.SvNAnyChar.stoneVonNeumann_any_char ψ hψ hψ1
    ((σ.toLinearMap ∘ₗ LinearMap.inl k _ _).toAddMonoidHom.comp r) ((σ.toLinearMap ∘ₗ LinearMap.inr k _ _).toAddMonoidHom.comp r)
    (fun Y Y' => (hσ _ _).trans (by simp)) (fun Y Y' => (hσ _ _).trans (by simp))
    (fun Y z => (hσ _ _).trans (by simp [dotProduct, r]; rfl))
    (fun w => ⟨of fun _ => (σ.symm w).1, of fun _ => (σ.symm w).2, by
      show σ ((σ.symm w).1, 0) + σ (0, (σ.symm w).2) = w
      rw [← map_add]; simp⟩)
  let h : (Fin n → k) ≃ₜ Matrix (Fin 1) (Fin n) k := (Homeomorph.funUnique (Fin 1) (Fin n → k)).symm
  have hsb : ∀ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y), ∀ f ∈ SB Y, f ∘ e ∈ SB X :=
    fun e f hf => ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩
  let T : Module.End ℂ (SB (Fin n → k)) :=
    (LinearMap.funLeft ℂ ℂ h ∘ₗ ι).restrict fun φ hφ => hsb h _ (hι.1 hφ)
  have hTc : ∀ φ, (T φ).1 = ι φ ∘ h := fun _ => rfl
  have hb : Function.Bijective T := ⟨fun φ φ' e => Subtype.ext (hι.2.1 φ.2 φ'.2
      (h.surjective.right_cancellable.1 (congrArg Subtype.val e))), fun φ => by
    obtain ⟨f, hf, e⟩ := hι.2.2 (hsb h.symm _ φ.2)
    refine ⟨⟨f, hf⟩, Subtype.ext ?_⟩
    rw [hTc, e]
    funext x
    simp⟩
  refine ⟨((Module.End.isUnit_iff T).2 hb).unit, fun w => LinearMap.ext fun φ => Subtype.ext ?_⟩
  show (T (schrS hψ (σ w) φ)).1 = schr ψ w (T φ).1
  have e1 := schr_schr ψ (σ (0, w.2)) (σ (w.1, 0)) φ
  have e2 := schr_schr ψ (0, w.2) (w.1, 0) (T φ).1
  rw [hσ, ← map_add] at e1
  simp only [Prod.mk_add_mk, zero_add, add_zero, Prod.mk.eta] at e1 e2
  have hne : ∀ t, ψ t ≠ 0 := fun t => (ψ.val_isUnit t).ne_zero
  refine smul_right_injective _ (hne _) (Eq.trans ?_ e2)
  have e3 := hT (h w.1) φ φ.2
  have e4 := hM (h w.2) _ (schr_mem hψ (σ (w.1, 0)) φ.2)
  show _ • (ι (schr ψ (σ w) φ) ∘ h) = _
  rw [← Pi.smul_comp, ← map_smul, ← e1]
  refine (congrArg (· ∘ h) e4).trans ?_
  rw [show ι (schr ψ (σ (w.1, 0)) φ) = _ from e3, hTc]
  funext x
  simp [schr, dotProduct]
  rfl

end Schr

section Lin

variable {k : Type} [Field k] [Invertible (2 : k)] {E : Type} [Field E] [Algebra k E] {c : E →ₐ[k] E} {δ : E}

def trB (c : E →ₐ[k] E) : LinearMap.BilinForm k (Fin 2 → E) :=
  LinearMap.mk₂ k (fun u v => Algebra.trace k E (u 0 * c (v 1) - u 1 * c (v 0)))
    (fun u u' v => by rw [← map_add]; congr 1; simp only [Pi.add_apply]; ring)
    (fun a u v => by rw [← map_smul]; congr 1; simp [smul_sub])
    (fun u v v' => by rw [← map_add]; congr 1; simp only [Pi.add_apply, map_add]; ring)
    (fun a u v => by rw [← map_smul]; congr 1; simp [smul_sub])

omit [Invertible (2 : k)] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem trB_apply (u v : Fin 2 → E) : trB c u v = Algebra.trace k E (u 0 * c (v 1) - u 1 * c (v 0)) := rfl

omit [Invertible (2 : k)] in
/- English proof (translation)
The claim follows from `Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom c c (AlgHom.ext hq.invol) (AlgHom.ext hq.invol)) z`.
-/
theorem trace_conj (hq : IsQuad c δ) (z : E) : Algebra.trace k E (c z) = Algebra.trace k E z :=
  Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom c c (AlgHom.ext hq.invol) (AlgHom.ext hq.invol)) z

omit [Invertible (2 : k)] in
/- English proof (translation)
Rewrite using `[trB_apply, trB_apply, ← trace_conj hq (y 0 0 * _ - _), ← map_sub, symp]`. Use `congr 1`. Simplify using `[hTens, Fin.sum_univ_two, hq.invol]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem symp_eq (hq : IsQuad c δ) (x y : Matrix (Fin 2) (Fin 2) E) :
    symp c 1 (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) E) x y =
      trB c (x 0) (y 1) - trB c (y 0) (x 1) := by
  rw [trB_apply, trB_apply, ← trace_conj hq (y 0 0 * _ - _), ← map_sub, symp]
  congr 1
  simp [hTens, Fin.sum_univ_two, hq.invol]
  ring

omit [Invertible (2 : k)] in
/- English proof (translation)
Establish `h1` using `fun i j => congrFun (congrFun (show (h : GL (Fin 2) E).valᵀ * _ * (h : GL (Fin 2) E).val.map c = _ from h.2) i) j`. Establish `h00` using `h1 0 0`. Establish `h01` using `h1 0 1`. Establish `h10` using `h1 1 0`. Establish `h11` using `h1 1 1`.

Simplify using `[mul_apply, Fin.sum_univ_two, vecMul, dotProduct] at h00 h01 h10 h11`. Rewrite using `[trB_apply, trB_apply]`. Use `congr 1`. Simplify using `[mulVec, dotProduct, Fin.sum_univ_two]`. Take the linear combination `u 0 * c (v 0) * h00 + u 0 * c (v 1) * h01 + u 1 * c (v 0) * h10 + u 1 * c (v 1) * h11`.
-/
theorem trB_mulVec (h : UG c (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) E)) (u v : Fin 2 → E) :
    trB c ((h : GL (Fin 2) E).val *ᵥ u) ((h : GL (Fin 2) E).val *ᵥ v) = trB c u v := by
  have h1 := fun i j => congrFun (congrFun (show (h : GL (Fin 2) E).valᵀ * _ * (h : GL (Fin 2) E).val.map c = _ from h.2) i) j
  have h00 := h1 0 0
  have h01 := h1 0 1
  have h10 := h1 1 0
  have h11 := h1 1 1
  simp [mul_apply, Fin.sum_univ_two, vecMul, dotProduct] at h00 h01 h10 h11
  rw [trB_apply, trB_apply]
  congr 1
  simp [mulVec, dotProduct, Fin.sum_univ_two]
  linear_combination u 0 * c (v 0) * h00 + u 0 * c (v 1) * h01 + u 1 * c (v 0) * h10 + u 1 * c (v 1) * h11

omit [Invertible (2 : k)] in
/- English proof (translation)
Establish `h1` using `fun i j => congrFun (congrFun (show (g : GL (Fin 2) E).valᵀ * _ * (g : GL (Fin 2) E).val.map c = _ from g.2) i) j`. Establish `h00` using `h1 0 0`. Establish `h01` using `h1 0 1`. Establish `h10` using `h1 1 0`. Establish `h11` using `h1 1 1`.

Simplify using `[mul_apply, Fin.sum_univ_two, vecMul, dotProduct] at h00 h01 h10 h11`. Unfold `symp`. Use `congr 2`. Simplify using `[hTens, mul_apply, Fin.sum_univ_two]`. Take the linear combination `(x 0 0 * c (y 0 1) - x 0 1 * c (y 0 0)) * h00 + (x 0 0 * c (y 1 1) - x 0 1 * c (y 1 0)) * h01 + (x 1 0 * c (y 0 1) - x 1 1 * c (y 0 0)) * h10 + (x 1 0 * c (y 1 1) - x 1 1 * c (y 1 0)) * h11`.
-/
theorem symp_mul (g : UG c (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E)) (x y : Matrix (Fin 2) (Fin 2) E) :
    symp c 1 (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) E)
      ((g : GL (Fin 2) E).val * x) ((g : GL (Fin 2) E).val * y) = symp c 1 !![0, 1; 1, 0] !![0, 1; -1, 0] x y := by
  have h1 := fun i j => congrFun (congrFun (show (g : GL (Fin 2) E).valᵀ * _ * (g : GL (Fin 2) E).val.map c = _ from g.2) i) j
  have h00 := h1 0 0
  have h01 := h1 0 1
  have h10 := h1 1 0
  have h11 := h1 1 1
  simp [mul_apply, Fin.sum_univ_two, vecMul, dotProduct] at h00 h01 h10 h11
  unfold symp
  congr 2
  simp [hTens, mul_apply, Fin.sum_univ_two]
  linear_combination (x 0 0 * c (y 0 1) - x 0 1 * c (y 0 0)) * h00 + (x 0 0 * c (y 1 1) - x 0 1 * c (y 1 0)) * h01 +
    (x 1 0 * c (y 0 1) - x 1 1 * c (y 0 0)) * h10 + (x 1 0 * c (y 1 1) - x 1 1 * c (y 1 0)) * h11

/- English proof (translation)
Take `⟨b, -, -⟩` from `hq.basis`. Use `Module.Finite.of_basis b` as an intermediate fact. Establish `h2 : Module.finrank k E = 2` using `by rw [Module.finrank_eq_card_basis b]; simp`. Establish `h4 : Module.finrank k (Fin 2 → E) = 4` using `by simp [Module.finrank_pi_fintype, h2]`. Set `β` to `Module.finBasisOfFinrankEq k (Fin 2 → E) h4`.

Set `f : (Fin 2 → E) →ₗ[k] (Fin 4 → k)` to `LinearMap.pi fun i => trB c (β i)`. Establish `hf : ∀ u v, β.equivFun u ⬝ᵥ f v = trB c u v` using `fun u v => by conv_rhs => rw [← β.sum_equivFun u]`. Simplify using `only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]`. Both sides reduce to the same expression. Establish `ht : Algebra.trace k E 1 ≠ 0`.

Rewrite using `[← map_one (algebraMap k E), Algebra.trace_algebraMap, h2, nsmul_eq_mul, mul_one]`. Conclude with `Invertible.ne_zero (2 : k)` after adjusting the coercions. Establish `hi : Function.Injective f` using `(injective_iff_map_eq_zero f).2 fun v hv => by`. Establish `h0 : ∀ u, trB c u v = 0` using `fun u => by rw [← hf, hv, dotProduct_zero]`. Use function extensionality and compare the values at `i`.

Assume the negation of the conclusion as `hne`. Establish `hc` using `(_root_.map_ne_zero c).2 hne`. Use `fin_cases i`. Use `h0 ![0, -(c (v 0))⁻¹]` as an intermediate fact. Rewrite `this` using `[trB_apply]`.

Simplify using `at this hc`. Conclude with `ht (by rwa [inv_mul_cancel₀ ((_root_.map_ne_zero c).2 hc)] at this)`. Use `h0 ![(c (v 1))⁻¹, 0]` as an intermediate fact. Rewrite `this` using `[trB_apply]`. Simplify using `at this hc`.

Conclude with `ht (by rwa [inv_mul_cancel₀ ((_root_.map_ne_zero c).2 hc)] at this)`. Set `f'` to `LinearMap.linearEquivOfInjective f hi (by simp [h4])`. Use `⟨β.equivFun, ⟨(LinearEquiv.finTwoArrow k (Fin 2 → E)).trans (β.equivFun.prodCongr f'), fun x y => ?_⟩, fun x => ⟨rfl, fun u => hf u _⟩⟩` and prove the remaining obligations. Rewrite using `[symp_eq hq, ← hf, ← hf]`. Both sides reduce to the same expression.
-/
theorem exists_coord (hq : IsQuad c δ) : ∃ (e : (Fin 2 → E) ≃ₗ[k] (Fin 4 → k))
    (co : Darboux (symp c 1 (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) E)) (Fin 4)),
    ∀ x, (co.e x).1 = e (x 0) ∧ ∀ u, e u ⬝ᵥ (co.e x).2 = trB c u (x 1) := by
  obtain ⟨b, -, -⟩ := hq.basis
  have := Module.Finite.of_basis b
  have h2 : Module.finrank k E = 2 := by rw [Module.finrank_eq_card_basis b]; simp
  have h4 : Module.finrank k (Fin 2 → E) = 4 := by simp [Module.finrank_pi_fintype, h2]
  let β := Module.finBasisOfFinrankEq k (Fin 2 → E) h4
  let f : (Fin 2 → E) →ₗ[k] (Fin 4 → k) := LinearMap.pi fun i => trB c (β i)
  have hf : ∀ u v, β.equivFun u ⬝ᵥ f v = trB c u v := fun u v => by
    conv_rhs => rw [← β.sum_equivFun u]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
    rfl
  have ht : Algebra.trace k E 1 ≠ 0 := by
    rw [← map_one (algebraMap k E), Algebra.trace_algebraMap, h2, nsmul_eq_mul, mul_one]
    exact_mod_cast Invertible.ne_zero (2 : k)
  have hi : Function.Injective f := (injective_iff_map_eq_zero f).2 fun v hv => by
    have h0 : ∀ u, trB c u v = 0 := fun u => by rw [← hf, hv, dotProduct_zero]
    funext i
    by_contra hne
    have hc := (_root_.map_ne_zero c).2 hne
    fin_cases i
    · have := h0 ![0, -(c (v 0))⁻¹]
      rw [trB_apply] at this
      simp at this hc
      exact ht (by rwa [inv_mul_cancel₀ ((_root_.map_ne_zero c).2 hc)] at this)
    · have := h0 ![(c (v 1))⁻¹, 0]
      rw [trB_apply] at this
      simp at this hc
      exact ht (by rwa [inv_mul_cancel₀ ((_root_.map_ne_zero c).2 hc)] at this)
  let f' := LinearMap.linearEquivOfInjective f hi (by simp [h4])
  refine ⟨β.equivFun, ⟨(LinearEquiv.finTwoArrow k (Fin 2 → E)).trans (β.equivFun.prodCongr f'), fun x y => ?_⟩,
    fun x => ⟨rfl, fun u => hf u _⟩⟩
  rw [symp_eq hq, ← hf, ← hf]
  rfl

omit [Invertible (2 : k)]

def actC (e : (Fin 2 → E) ≃ₗ[k] (Fin 4 → k)) (g : GL (Fin 2) E) : (Fin 4 → k) →ₗ[k] (Fin 4 → k) :=
  e.toLinearMap ∘ₗ (Matrix.toLin' g.val).restrictScalars k ∘ₗ e.symm.toLinearMap

/- English proof (translation)
Simplify using `[actC]`.
-/
theorem actC_apply (e : (Fin 2 → E) ≃ₗ[k] (Fin 4 → k)) (g : GL (Fin 2) E) (u : Fin 2 → E) :
    actC e g (e u) = e (g.val *ᵥ u) := by simp [actC]

/- English proof (translation)
Simplify using `[actC]`.
-/
theorem actC_actC (e : (Fin 2 → E) ≃ₗ[k] (Fin 4 → k)) (g g' : GL (Fin 2) E) (x : Fin 4 → k) :
    actC e g (actC e g' x) = actC e (g * g') x := by simp [actC]

/- English proof (translation)
Simplify using `[actC]`.
-/
theorem actC_one (e : (Fin 2 → E) ≃ₗ[k] (Fin 4 → k)) (x : Fin 4 → k) : actC e 1 x = x := by simp [actC]

def linOm (e : (Fin 2 → E) ≃ₗ[k] (Fin 4 → k)) (J : Matrix (Fin 2) (Fin 2) E) :
    UG c J →* Module.End ℂ ((Fin 4 → k) → ℂ) where
  toFun h := LinearMap.funLeft ℂ ℂ (actC e (h : GL (Fin 2) E)⁻¹)
  map_one' := LinearMap.ext fun φ => funext fun x => by simp [LinearMap.funLeft, actC_one]
  map_mul' h h' := LinearMap.ext fun φ => funext fun x => by simp [LinearMap.funLeft, actC_actC]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem linOm_apply (e : (Fin 2 → E) ≃ₗ[k] (Fin 4 → k)) (J : Matrix (Fin 2) (Fin 2) E) (h : UG c J) (φ : (Fin 4 → k) → ℂ)
    (x : Fin 4 → k) : linOm e J h φ x = φ (actC e (h : GL (Fin 2) E)⁻¹ x) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Take `⟨u, rfl⟩` from `e.surjective x`. Establish `hr : ∀ i, actB c h w i = (h : GL (Fin 2) E).val *ᵥ w i` using `fun i => by`. Use function extensionality and compare the values at `j`. Simplify using `[actB, mul_apply, mulVec, dotProduct, mul_comm]`.

Establish `h1 : trB c u ((h : GL (Fin 2) E).val *ᵥ w 1) = trB c (((h : GL (Fin 2) E)⁻¹).val *ᵥ u) (w 1)`. Rewrite using `[← trB_mulVec h (_ *ᵥ u), mulVec_mulVec, Units.mul_inv, one_mulVec]`. Simplify using `only [linOm_apply, Darboux.rho, schr, (hco _).1, (hco _).2, actC_apply, ← map_add e, hr, trB_mulVec, h1, mulVec_add, mulVec_mulVec, Units.inv_mul, one_mulVec]`.
-/
theorem linOm_impl [Invertible (2 : k)] (ψ : AddChar k ℂ) (e : (Fin 2 → E) ≃ₗ[k] (Fin 4 → k))
    (co : Darboux (symp c 1 (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) E)) (Fin 4))
    (hco : ∀ x, (co.e x).1 = e (x 0) ∧ ∀ u, e u ⬝ᵥ (co.e x).2 = trB c u (x 1))
    (h : UG c (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) E)) (w : Matrix (Fin 2) (Fin 2) E) (φ : (Fin 4 → k) → ℂ) :
    linOm e _ h (co.rho ψ w φ) = co.rho ψ (actB c h w) (linOm e _ h φ) := by
  funext x
  obtain ⟨u, rfl⟩ := e.surjective x
  have hr : ∀ i, actB c h w i = (h : GL (Fin 2) E).val *ᵥ w i := fun i => by
    funext j; simp [actB, mul_apply, mulVec, dotProduct, mul_comm]
  have h1 : trB c u ((h : GL (Fin 2) E).val *ᵥ w 1) = trB c (((h : GL (Fin 2) E)⁻¹).val *ᵥ u) (w 1) := by
    rw [← trB_mulVec h (_ *ᵥ u), mulVec_mulVec, Units.mul_inv, one_mulVec]
  simp only [linOm_apply, Darboux.rho, schr, (hco _).1, (hco _).2, actC_apply, ← map_add e, hr, trB_mulVec, h1, mulVec_add,
    mulVec_mulVec, Units.inv_mul, one_mulVec]

end Lin

section Top

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  {E : Type} [Field E] [Algebra k E] {c : E →ₐ[k] E} {δ : E} {ψ : AddChar k ℂ}

omit [Invertible (2 : k)] in
/- English proof (translation)
Set `a : (Fin 4 → k) ≃ₜ (Fin 4 → k)` to `{ toFun := actC e (h : GL (Fin 2) E)⁻¹ invFun := actC e (h : GL (Fin 2) E) left_inv := fun x => by rw [actC_actC, mul_inv_cancel, actC_one] right_inv := fun x => by rw [actC_actC, inv_mul_cancel, actC_one] continuous_toFun := LinearMap.continuous_on_pi _ continuous_invFun := Line …`. Conclude with `⟨hφ.1.comp_continuous a.continuous, hφ.2.comp_homeomorph a⟩`.
-/
theorem linOm_mem (e : (Fin 2 → E) ≃ₗ[k] (Fin 4 → k)) (J : Matrix (Fin 2) (Fin 2) E) (h : UG c J)
    {φ : (Fin 4 → k) → ℂ} (hφ : φ ∈ SB (Fin 4 → k)) : linOm e J h φ ∈ SB (Fin 4 → k) := by
  let a : (Fin 4 → k) ≃ₜ (Fin 4 → k) :=
    { toFun := actC e (h : GL (Fin 2) E)⁻¹
      invFun := actC e (h : GL (Fin 2) E)
      left_inv := fun x => by rw [actC_actC, mul_inv_cancel, actC_one]
      right_inv := fun x => by rw [actC_actC, inv_mul_cancel, actC_one]
      continuous_toFun := LinearMap.continuous_on_pi _
      continuous_invFun := LinearMap.continuous_on_pi _ }
  exact ⟨hφ.1.comp_continuous a.continuous, hφ.2.comp_homeomorph a⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Rewrite using `[actC, LinearMap.det_conj, LinearMap.det_restrictScalars, LinearMap.det_toLin']`. Apply `hq.algebraMap_injective` to reduce the goal to its premises. Establish `h1` using `congrArg det (show (h : GL (Fin 2) E).valᵀ * _ * (h : GL (Fin 2) E).val.map c = _ from h.2)`. Rewrite `h1` using `[det_mul, det_mul, det_transpose, show ((h : GL (Fin 2) E).val.map c).det = c (h : GL (Fin 2) E).val.det from (c.toRingHom.map_det _).symm]`. Rewrite using `[hq.algebraMap_norm, map_one]`.

Simplify using `using h1`.
-/
theorem det_actC (hq : IsQuad c δ) (e : (Fin 2 → E) ≃ₗ[k] (Fin 4 → k))
    (h : UG c (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) E)) : LinearMap.det (actC e (h : GL (Fin 2) E)) = 1 := by
  rw [actC, LinearMap.det_conj, LinearMap.det_restrictScalars, LinearMap.det_toLin']
  apply hq.algebraMap_injective
  have h1 := congrArg det (show (h : GL (Fin 2) E).valᵀ * _ * (h : GL (Fin 2) E).val.map c = _ from h.2)
  rw [det_mul, det_mul, det_transpose,
    show ((h : GL (Fin 2) E).val.map c).det = c (h : GL (Fin 2) E).val.det from (c.toRingHom.map_det _).symm] at h1
  rw [hq.algebraMap_norm, map_one]
  simpa using h1

/- English proof (translation)
Use `borelize k`. Use `GlobalTheory.SplitWeil.secondCountable k` as an intermediate fact. Use `GlobalTheory.SplitWeil.t2Space k` as an intermediate fact. Unfold `IsUnitaryOn`. Rewrite using `[← (BorelSpace.measurable_eq : (MeasurableSpace.pi : MeasurableSpace (Fin 4 → k)) = borel _)]`.

Introduce `μ hμ h φ hφ`. Set `G : Matrix (Fin 4) (Fin 4) k` to `LinearMap.toMatrix' (actC e (h : GL (Fin 2) E)⁻¹)`. Establish `hG : ((1 : kˣ) : k) = G.det`. Rewrite using `[LinearMap.det_toMatrix']`. Conclude with `(det_actC hq e h⁻¹).symm`.

Establish `hm : Measurable fun x => ‖φ x‖ₑ ^ 2` using `(hφ.1.continuous.measurable.enorm).pow_const 2`. Rewrite using `[Measure.isAddLeftInvariant_eq_smul μ (Measure.pi fun _ : Fin 4 => (Measure.addHaar : Measure k)), lintegral_smul_measure, lintegral_smul_measure]`. Use `congr 1`. Use `conv_rhs => rw [← smul_map_mulVec_pi Measure.addHaar G _ hG, map_one, ENNReal.coe_one, one_smul, lintegral_map hm (show Measurable G.mulVec from (continuous_const.matrix_mulVec continuous_id).measurable)]`. Simplify using `only [linOm_apply, G, LinearMap.toMatrix'_mulVec]`.
-/
theorem isUnitaryOn_linOm (hq : IsQuad c δ) (e : (Fin 2 → E) ≃ₗ[k] (Fin 4 → k)) :
    IsUnitaryOn (sbClass k) (linOm (c := c) e (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) E)) := by
  borelize k
  have := GlobalTheory.SplitWeil.secondCountable k
  have := GlobalTheory.SplitWeil.t2Space k
  unfold IsUnitaryOn
  rw [← (BorelSpace.measurable_eq : (MeasurableSpace.pi : MeasurableSpace (Fin 4 → k)) = borel _)]
  intro μ hμ h φ hφ
  let G : Matrix (Fin 4) (Fin 4) k := LinearMap.toMatrix' (actC e (h : GL (Fin 2) E)⁻¹)
  have hG : ((1 : kˣ) : k) = G.det := by
    rw [LinearMap.det_toMatrix']
    exact (det_actC hq e h⁻¹).symm
  have hm : Measurable fun x => ‖φ x‖ₑ ^ 2 := (hφ.1.continuous.measurable.enorm).pow_const 2
  rw [Measure.isAddLeftInvariant_eq_smul μ (Measure.pi fun _ : Fin 4 => (Measure.addHaar : Measure k)),
    lintegral_smul_measure, lintegral_smul_measure]
  congr 1
  conv_rhs => rw [← smul_map_mulVec_pi Measure.addHaar G _ hG, map_one, ENNReal.coe_one, one_smul,
    lintegral_map hm (show Measurable G.mulVec from (continuous_const.matrix_mulVec continuous_id).measurable)]
  simp only [linOm_apply, G, LinearMap.toMatrix'_mulVec]

omit [Invertible (2 : k)] in

/- English proof (translation)
Take `⟨b, -, -⟩` from `hq.basis`. Use `Module.Finite.of_basis b` as an intermediate fact. Use `IsModuleTopology.isTopologicalRing k E` as an intermediate fact. Use `IsModuleTopology.toContinuousAdd k E` as an intermediate fact. Use `isLocallyConstant_orbit _ ?_` and prove the remaining obligations.

Establish `c1 : Continuous e` using `IsModuleTopology.continuous_of_linearMap e.toLinearMap`. Establish `c2 : Continuous e.symm` using `LinearMap.continuous_on_pi e.symm.toLinearMap`. Establish `hc : ∀ M : UG c J → GL (Fin 2) E, Continuous M → Continuous fun q : UG c J × (Fin 4 → k) => actC e (M q.1) q.2` using `fun M hM => by`. Establish `c3 : Continuous fun q : UG c J × (Fin 4 → k) => (M q.1).val` using `Units.continuous_val.comp (hM.comp continuous_fst)`. Establish `c4 : Continuous fun q : UG c J × (Fin 4 → k) => e.symm q.2` using `c2.comp continuous_snd`.

Conclude with `(c1.comp (c3.matrix_mulVec c4)).congr fun q => by simp [actC]`. Establish `c5 : Continuous fun p : UG c J => (p : GL (Fin 2) E)` using `continuous_subtype_val`. Use `filter_upwards [eventually_comp_eq (p₀ := (1 : UG c J)) (fun p v => actC e (p : GL (Fin 2) E)⁻¹ v) (fun p v => actC e (p : GL (Fin 2) E) v) (hc (fun p => (p : GL (Fin 2) E)⁻¹) c5.inv) (hc (fun p => (p : GL (Fin 2) E)) c5) (by simp [actC_one]) (by simp [actC_one]) (fun p v => by r …`. Conclude with `funext h1`.
-/
theorem isLocallyConstant_linOm [TopologicalSpace E] [IsModuleTopology k E] (hq : IsQuad c δ)
    (e : (Fin 2 → E) ≃ₗ[k] (Fin 4 → k)) (J : Matrix (Fin 2) (Fin 2) E) {φ : (Fin 4 → k) → ℂ} (hφ : φ ∈ SB (Fin 4 → k)) :
    IsLocallyConstant fun h : UG c J => linOm e J h φ := by
  obtain ⟨b, -, -⟩ := hq.basis
  have := Module.Finite.of_basis b
  have := IsModuleTopology.isTopologicalRing k E
  have := IsModuleTopology.toContinuousAdd k E
  refine isLocallyConstant_orbit _ ?_
  have c1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have c2 : Continuous e.symm := LinearMap.continuous_on_pi e.symm.toLinearMap
  have hc : ∀ M : UG c J → GL (Fin 2) E, Continuous M → Continuous fun q : UG c J × (Fin 4 → k) => actC e (M q.1) q.2 :=
    fun M hM => by
      have c3 : Continuous fun q : UG c J × (Fin 4 → k) => (M q.1).val := Units.continuous_val.comp (hM.comp continuous_fst)
      have c4 : Continuous fun q : UG c J × (Fin 4 → k) => e.symm q.2 := c2.comp continuous_snd
      exact (c1.comp (c3.matrix_mulVec c4)).congr fun q => by simp [actC]
  have c5 : Continuous fun p : UG c J => (p : GL (Fin 2) E) := continuous_subtype_val
  filter_upwards [eventually_comp_eq (p₀ := (1 : UG c J)) (fun p v => actC e (p : GL (Fin 2) E)⁻¹ v)
    (fun p v => actC e (p : GL (Fin 2) E) v) (hc (fun p => (p : GL (Fin 2) E)⁻¹) c5.inv) (hc (fun p => (p : GL (Fin 2) E)) c5)
    (by simp [actC_one]) (by simp [actC_one]) (fun p v => by rw [actC_actC, mul_inv_cancel, actC_one]) hφ] with h h1
  exact funext h1

/- English proof (translation)
Use `borelize k`. Use `GlobalTheory.SplitWeil.secondCountable k` as an intermediate fact. Use `GlobalTheory.SplitWeil.t2Space k` as an intermediate fact. Take `⟨b, -, -⟩` from `hq.basis`. Set `ν : Measure (Fin 2 → k)` to `Measure.pi fun _ => Measure.addHaar`.

Set `j : (Fin 2 → k) →ₗ[k] (Fin 4 → k)` to `e.toLinearMap ∘ₗ LinearMap.single k (fun _ : Fin 2 => E) 0 ∘ₗ b.equivFun.symm.toLinearMap`. Establish `hj : ∀ a, j a = e (Pi.single 0 (b.equivFun.symm a))` using `fun _ => rfl`. Set `p : (Fin 4 → k) →ₗ[k] (Fin 2 → k)` to `b.equivFun.toLinearMap ∘ₗ LinearMap.proj 0 ∘ₗ e.symm.toLinearMap`. Establish `hpj : ∀ a, p (j a) = a` using `fun a => by show b.equivFun (e.symm (e (Pi.single 0 (b.equivFun.symm a))) 0) = a`. Rewrite using `[e.symm_apply_apply, Pi.single_eq_same, b.equivFun.apply_symm_apply]`.

Establish `hjc : Continuous j` using `LinearMap.continuous_on_pi j`. Establish `hpc : Continuous p` using `LinearMap.continuous_on_pi p`. Establish `hint : ∀ φ ∈ SB (Fin 4 → k), Integrable (fun a => φ (j a)) ν` using `fun φ hφ => by`. Use `(hφ.1.continuous.comp hjc).integrable_of_hasCompactSupport (HasCompactSupport.intro (hφ.2.image hpc) fun x hx => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `h`.

Conclude with `hx ⟨j x, subset_tsupport _ h, hpj x⟩`. Set `f : SB (Fin 4 → k) →ₗ[ℂ] ℂ` to `{ toFun := fun φ => ∫ a, φ.1 (j a) ∂ν map_add' := fun φ φ' => integral_add (hint _ φ.2) (hint _ φ'.2) map_smul' := fun z φ => integral_const_mul z _ }`. Take `⟨l, hl⟩` from `LinearMap.exists_extend f`. Establish `hl' : ∀ φ ∈ SB (Fin 4 → k), l φ = ∫ a, φ (j a) ∂ν` using `fun φ hφ => LinearMap.congr_fun hl ⟨φ, hφ⟩`. Establish `hY : IsYForm c ψ co (!![1; 0] : Matrix (Fin 2) (Fin 1) E) l`.

Use `⟨fun z φ hφ => ?_, ?_⟩` and prove the remaining obligations. Establish `hr : ∀ i, (z * (!![1; 0] : Matrix (Fin 2) (Fin 1) E)ᵀ) i = Pi.single 0 (z i 0)` using `fun i => by`. Apply the tactic sequence `funext i'; fin_cases i' <;> simp [mul_apply]`. Rewrite using `[Darboux.rho, hl' _ (schr_mem hψ _ hφ), hl' _ hφ, ← integral_add_right_eq_self (μ := ν) (fun a => φ (j a)) (b.equivFun (z 0 0))]`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Simplify using `only [schr, (hco _).1, hj, (hco _).2, hr, trB_apply, map_add, Pi.single_add, LinearEquiv.symm_apply_apply]`. Simplify using the standard rewrite rules. Take `⟨U, hUo, hUc, hU0⟩` from `GlobalTheory.LagrFormLine.exists_compact_open k (Fin 4)`. Establish `hm : (U.indicator fun _ => (1 : ℂ)) ∈ SB (Fin 4 → k)` using `⟨(LocallyConstant.charFn ℂ (⟨hUc.isClosed, hUo⟩ : IsClopen U)).isLocallyConstant, HasCompactSupport.intro hUc fun x hx => Set.indicator_of_notMem hx _⟩`.

Use `⟨_, hm, ?_⟩` and prove the remaining obligations. Establish `hSo : IsOpen (j ⁻¹' U)` using `hUo.preimage hjc`. Establish `hfin : ν (j ⁻¹' U) < ⊤` using `lt_of_le_of_lt (measure_mono (show j ⁻¹' U ⊆ p '' U from fun y hy => ⟨j y, hy, hpj y⟩)) ((hUc.image hpc).measure_lt_top)`. Establish `hpos : 0 < ν (j ⁻¹' U)` using `hSo.measure_pos ν ⟨0, by simpa using hU0⟩`. Rewrite using `[hl' _ hm, show (fun a => U.indicator (fun _ => (1 : ℂ)) (j a)) = (j ⁻¹' U).indicator (fun _ => (1 : ℂ)) from rfl, integral_indicator_const _ hSo.measurableSet]`.

Conclude with `smul_ne_zero (ENNReal.toReal_ne_zero.mpr ⟨hpos.ne', hfin.ne⟩) one_ne_zero`. Introduce `l₁ _ hl₁ q t hqt φ hφ`. Establish `hL` using `GlobalTheory.LinPair.Model.lagr_plane c`. Take `⟨y, hy⟩` from `GlobalTheory.LagrInvForm.proportional k ψ hψ hψ1 _ _ (GlobalTheory.LagrFormLine.lagCo_isotropic co hL.1) (GlobalTheory.LagrFormLine.finrank_lagCo co hL) l₁ l (by rintro _ ⟨z, rfl⟩; exact hl₁ z) (by rintro _ ⟨z, rfl⟩; exact hY.1 z) hY.2`. Establish `hφ'` using `linOm_mem e _ q hφ`.

Rewrite using `[hy _ hφ, hy _ hφ', mul_left_comm, hl' _ hφ, hl' _ hφ']`. Use `congr 1`. Use `set u := GeneralLinearGroup.det t with hu`. Establish `hu' : (u : E) = t.val 0 0` using `by rw [hu, GeneralLinearGroup.val_det_apply, det_fin_one]`. Set `g : GL (Fin 2) k` to `Units.map (Algebra.leftMulMatrix b).toMonoidHom u`.

Establish `hg : GeneralLinearGroup.det g = Units.map (Algebra.norm k : E →* k) u` using `Units.ext (Algebra.norm_eq_matrix_det b _).symm`. Establish `hq0 : ∀ s : E, (q : GL (Fin 2) E).val *ᵥ Pi.single 0 s = Pi.single 0 ((u : E) * s)` using `fun s => by`. Use function extensionality and compare the values at `i`. Use `congrFun (congrFun hqt i) 0` as an intermediate fact. Apply the tactic sequence `fin_cases i <;> simp [mul_apply, Fin.sum_univ_two] at this <;> simp [this, hu']`.

Establish `hjg : ∀ a, actC e (q : GL (Fin 2) E)⁻¹ (j (g.val *ᵥ a)) = j a` using `fun a => by`. Take `⟨s, rfl⟩` from `b.equivFun.surjective a`. Establish `: g.val *ᵥ b.equivFun s = b.equivFun ((u : E) * s)` using `Algebra.leftMulMatrix_mulVec_repr b _ _`. Rewrite using `[this, hj, hj, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, actC_apply, ← hq0, mulVec_mulVec, Units.inv_mul, one_mulVec]`. Rewrite using `[← integral_comp_mulVec Measure.addHaar g]`.

Simplify using `only [linOm_apply, hjg, hg]`. Simplify using `[sbClass, ν]`.
-/
theorem siegelRule_linOm (hq : IsQuad c δ) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (e : (Fin 2 → E) ≃ₗ[k] (Fin 4 → k))
    (co : Darboux (symp c 1 (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) E)) (Fin 4))
    (hco : ∀ x, (co.e x).1 = e (x 0) ∧ ∀ u, e u ⬝ᵥ (co.e x).2 = trB c u (x 1)) :
    SiegelRule c (sbClass k) ψ 1 _ _ co 1 (!![1; 0] : Matrix (Fin 2) (Fin 1) E) (linOm e _) := by
  borelize k
  have := GlobalTheory.SplitWeil.secondCountable k
  have := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨b, -, -⟩ := hq.basis
  let ν : Measure (Fin 2 → k) := Measure.pi fun _ => Measure.addHaar
  let j : (Fin 2 → k) →ₗ[k] (Fin 4 → k) :=
    e.toLinearMap ∘ₗ LinearMap.single k (fun _ : Fin 2 => E) 0 ∘ₗ b.equivFun.symm.toLinearMap
  have hj : ∀ a, j a = e (Pi.single 0 (b.equivFun.symm a)) := fun _ => rfl
  let p : (Fin 4 → k) →ₗ[k] (Fin 2 → k) := b.equivFun.toLinearMap ∘ₗ LinearMap.proj 0 ∘ₗ e.symm.toLinearMap
  have hpj : ∀ a, p (j a) = a := fun a => by
    show b.equivFun (e.symm (e (Pi.single 0 (b.equivFun.symm a))) 0) = a
    rw [e.symm_apply_apply, Pi.single_eq_same, b.equivFun.apply_symm_apply]
  have hjc : Continuous j := LinearMap.continuous_on_pi j
  have hpc : Continuous p := LinearMap.continuous_on_pi p
  have hint : ∀ φ ∈ SB (Fin 4 → k), Integrable (fun a => φ (j a)) ν := fun φ hφ => by
    refine (hφ.1.continuous.comp hjc).integrable_of_hasCompactSupport (HasCompactSupport.intro (hφ.2.image hpc) fun x hx => ?_)
    by_contra h
    exact hx ⟨j x, subset_tsupport _ h, hpj x⟩
  let f : SB (Fin 4 → k) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∫ a, φ.1 (j a) ∂ν
      map_add' := fun φ φ' => integral_add (hint _ φ.2) (hint _ φ'.2)
      map_smul' := fun z φ => integral_const_mul z _ }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend f
  have hl' : ∀ φ ∈ SB (Fin 4 → k), l φ = ∫ a, φ (j a) ∂ν := fun φ hφ => LinearMap.congr_fun hl ⟨φ, hφ⟩
  have hY : IsYForm c ψ co (!![1; 0] : Matrix (Fin 2) (Fin 1) E) l := by
    refine ⟨fun z φ hφ => ?_, ?_⟩
    · have hr : ∀ i, (z * (!![1; 0] : Matrix (Fin 2) (Fin 1) E)ᵀ) i = Pi.single 0 (z i 0) := fun i => by
        funext i'; fin_cases i' <;> simp [mul_apply]
      rw [Darboux.rho, hl' _ (schr_mem hψ _ hφ), hl' _ hφ,
        ← integral_add_right_eq_self (μ := ν) (fun a => φ (j a)) (b.equivFun (z 0 0))]
      congr 1
      funext a
      simp only [schr, (hco _).1, hj, (hco _).2, hr, trB_apply, map_add, Pi.single_add, LinearEquiv.symm_apply_apply]
      simp
    · obtain ⟨U, hUo, hUc, hU0⟩ := GlobalTheory.LagrFormLine.exists_compact_open k (Fin 4)
      have hm : (U.indicator fun _ => (1 : ℂ)) ∈ SB (Fin 4 → k) :=
        ⟨(LocallyConstant.charFn ℂ (⟨hUc.isClosed, hUo⟩ : IsClopen U)).isLocallyConstant,
          HasCompactSupport.intro hUc fun x hx => Set.indicator_of_notMem hx _⟩
      refine ⟨_, hm, ?_⟩
      have hSo : IsOpen (j ⁻¹' U) := hUo.preimage hjc
      have hfin : ν (j ⁻¹' U) < ⊤ := lt_of_le_of_lt
        (measure_mono (show j ⁻¹' U ⊆ p '' U from fun y hy => ⟨j y, hy, hpj y⟩)) ((hUc.image hpc).measure_lt_top)
      have hpos : 0 < ν (j ⁻¹' U) := hSo.measure_pos ν ⟨0, by simpa using hU0⟩
      rw [hl' _ hm, show (fun a => U.indicator (fun _ => (1 : ℂ)) (j a)) = (j ⁻¹' U).indicator (fun _ => (1 : ℂ)) from rfl,
        integral_indicator_const _ hSo.measurableSet]
      exact smul_ne_zero (ENNReal.toReal_ne_zero.mpr ⟨hpos.ne', hfin.ne⟩) one_ne_zero
  intro l₁ _ hl₁ q t hqt φ hφ
  have hL := GlobalTheory.LinPair.Model.lagr_plane c
  obtain ⟨y, hy⟩ := GlobalTheory.LagrInvForm.proportional k ψ hψ hψ1 _ _ (GlobalTheory.LagrFormLine.lagCo_isotropic co hL.1)
    (GlobalTheory.LagrFormLine.finrank_lagCo co hL) l₁ l (by rintro _ ⟨z, rfl⟩; exact hl₁ z) (by rintro _ ⟨z, rfl⟩; exact hY.1 z) hY.2
  have hφ' := linOm_mem e _ q hφ
  rw [hy _ hφ, hy _ hφ', mul_left_comm, hl' _ hφ, hl' _ hφ']
  congr 1
  set u := GeneralLinearGroup.det t with hu
  have hu' : (u : E) = t.val 0 0 := by rw [hu, GeneralLinearGroup.val_det_apply, det_fin_one]
  let g : GL (Fin 2) k := Units.map (Algebra.leftMulMatrix b).toMonoidHom u
  have hg : GeneralLinearGroup.det g = Units.map (Algebra.norm k : E →* k) u :=
    Units.ext (Algebra.norm_eq_matrix_det b _).symm
  have hq0 : ∀ s : E, (q : GL (Fin 2) E).val *ᵥ Pi.single 0 s = Pi.single 0 ((u : E) * s) := fun s => by
    funext i
    have := congrFun (congrFun hqt i) 0
    fin_cases i <;> simp [mul_apply, Fin.sum_univ_two] at this <;> simp [this, hu']
  have hjg : ∀ a, actC e (q : GL (Fin 2) E)⁻¹ (j (g.val *ᵥ a)) = j a := fun a => by
    obtain ⟨s, rfl⟩ := b.equivFun.surjective a
    have : g.val *ᵥ b.equivFun s = b.equivFun ((u : E) * s) := Algebra.leftMulMatrix_mulVec_repr b _ _
    rw [this, hj, hj, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, actC_apply, ← hq0, mulVec_mulVec,
      Units.inv_mul, one_mulVec]
  rw [← integral_comp_mulVec Measure.addHaar g]
  simp only [linOm_apply, hjg, hg]
  simp [sbClass, ν]

end Top

/- English proof (translation)
Introduce `k _ _ _ _ _ _ E _ _ _ _ c δ hq ψ hψ hn hψ1`. Take `⟨e, co, hco⟩` from `exists_coord hq`. Establish `hL` using `GlobalTheory.LinPair.Model.lagr_plane c`. Take `⟨⟨l, hl⟩, hu⟩` from `GlobalTheory.LagrFormLine.yform_line k E c δ hq ψ hψ hn hψ1 _ _ _ _ _ _ _ co _ hL`. Establish `hS` using `siegelRule_linOm hq hψ hψ1 e co hco`.

Set `ω : UG c (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) E) →* Module.End ℂ (SB (Fin 4 → k))` to `{ toFun := fun h => (linOm e _ h).restrict fun _ hφ => linOm_mem e _ h hφ map_one' := LinearMap.ext fun φ => Subtype.ext (LinearMap.congr_fun (linOm e _).map_one φ.1) map_mul' := fun h h' => LinearMap.ext fun φ => Subtype.ext (LinearMap.congr_fun ((linOm e _).map_mul h h') φ.1) }`. Establish `hω : ∀ h φ, (ω h φ).1 = linOm e _ h φ.1` using `fun _ _ => rfl`. Establish `hl0 : l ∘ₗ (SB (Fin 4 → k)).subtype ≠ 0` using `fun h => by`. Take `⟨φ, hφ, h0⟩` from `hl.2`. Conclude with `h0 (LinearMap.congr_fun h ⟨φ, hφ⟩)`.

Take `⟨M, hM1, hM2, hM3⟩` from `exists_hom_commute (G := UG c (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E)) (fun w => schrS hψ (co.e w)) (fun T hT => schur hψ hψ1 T fun w => by simpa using hT (co.e.symm w)) (fun g w => (g : GL (Fin 2) E).val * w) (fun w => by simp) (fun g g' w => by simp [Matrix.mul_assoc]) (act …`. Set `a : Matrix (Fin 2) (Fin 2) E ≃ₗ[k] Matrix (Fin 2) (Fin 2) E` to `{ toFun := fun w => ((g : GL (Fin 2) E)⁻¹).val * w invFun := fun w => (g : GL (Fin 2) E).val * w map_add' := fun _ _ => Matrix.mul_add _ _ _ map_smul' := fun _ _ => Matrix.mul_smul _ _ _ left_inv := fun w => Units.mul_inv_cancel_left _ _ right_inv := fun w => Units.inv_mul_cancel …`. Take `⟨T, hT⟩` from `exists_implementer hψ hψ1 (co.e.symm.trans (a.trans co.e)) fun w w' => by`. Take `⟨w, rfl⟩` from `co.e.surjective w`. Take `⟨w', rfl⟩` from `co.e.surjective w'`.

Simplify using `only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, ← co.form]`. Conclude with `symp_mul g⁻¹ w w'`. Establish `hT' : ∀ w, T.val * schrS hψ (co.e w) = schrS hψ (co.e ((g : GL (Fin 2) E).val * w)) * T.val` using `fun w => by`. Rewrite using `[← hT]`. Simplify using `[a]`.

Take `⟨l₁, hl₁⟩` from `LinearMap.exists_extend (l ∘ₗ (SB (Fin 4 → k)).subtype ∘ₗ T.val)`. Establish `hl₁' : ∀ φ : SB (Fin 4 → k), l₁ φ = l (T.val φ)` using `fun φ => LinearMap.congr_fun hl₁ φ`. Take `⟨z, hz⟩` from `hu l₁ l (fun y φ hφ => by`. Rewrite using `[Darboux.rho, ← schrS_coe hψ _ ⟨φ, hφ⟩, hl₁', hl₁' ⟨φ, hφ⟩, ← Module.End.mul_apply, hT', ← Matrix.mul_assoc]`. Conclude with `hl.1 _ _ (T.val ⟨φ, hφ⟩).2) hl`.

Establish `hz0 : z ≠ 0` using `fun h => hl0 (LinearMap.ext fun φ => by`. Use `hz _ ((T⁻¹).val φ).2` as an intermediate fact. Rewrite using `[hl₁', h, zero_mul, ← Module.End.mul_apply, Units.mul_inv] at this)` and apply the resulting hypothesis. Use `⟨(Units.mk0 z hz0)⁻¹ • T, fun w => ?_, LinearMap.ext fun φ => ?_⟩` and prove the remaining obligations. Simplify using `only [Units.val_smul, smul_mul_assoc, mul_smul_comm, hT']`.

Use `hz _ φ.2` as an intermediate fact. Rewrite `this` using `[hl₁']`. Simplify using `[Units.smul_def, this, hz0])`. Use the proof step `{p | (p : GL (Fin 2) E).val 1 0 = 0}`. Use the proof step `(fun p hp => by`.

Establish `h0 : (p : GL (Fin 2) E).val 0 0 ≠ 0` using `fun h => (p : GL (Fin 2) E).det_ne_zero (by`. Rewrite using `[det_fin_two, h, hp]`. Use the proof step `simp)`. Establish `key` using `hS l trivial hl.1 p (GeneralLinearGroup.mkOfDetNeZero !![(p : GL (Fin 2) E).val 0 0] (by simpa using h0)) (by`. Use extensionality with `i j`.

Establish `hp' : (p : GL (Fin 2) E).val 1 0 = 0` using `hp`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, hp'])`. Establish `fin : ∀ z : ℂ, z ≠ 0 → (∀ φ ∈ SB (Fin 4 → k), l (linOm e _ p φ) = z * l φ) → ∃ z : ℂ, z ≠ 0 ∧ (l ∘ₗ (SB (Fin 4 → k)).subtype) ∘ₗ ω p = z • (l ∘ₗ (SB (Fin 4 → k)).subtype)` using `fun z hz h => ⟨z, hz, LinearMap.ext fun φ => h φ φ.2⟩`. Conclude with `fin _ (mul_ne_zero (Circle.coe_ne_zero _) (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (distribHaarChar_pos (A := k)) _).ne')) key)`. Use `char_eq_one`.

Take `⟨x, hx⟩` from `exists_extend_hom (SB (Fin 4 → k))`. Set `om` to `x.comp (M.noncommCoprod ω hM3)`. Establish `hB : ∀ h, ∀ φ ∈ SB (Fin 4 → k), om.comp (MonoidHom.inr _ _) h φ = linOm e _ h φ` using `fun h φ hφ => by`. Rewrite using `[← hω h ⟨φ, hφ⟩, ← hx]`. Simplify using `[om]`.

Establish `hA : ∀ g (φ : SB (Fin 4 → k)), om (g, 1) φ = M g φ` using `fun g φ => by`. Rewrite using `[← hx]`. Simplify using `[om]`. Use `⟨_, co, om, l, ⟨⟨hL, ⟨⟨fun h φ hφ => ?_, fun h w φ hφ => ?_, fun _ _ _ => trivial⟩, fun μ hμ h φ hφ => ?_, .of_isLocallyConstant fun φ hφ => ?_⟩, fun l' h1 h2 p t hp φ hφ => ?_⟩, fun g φ hφ => ?_, fun g w φ hφ => ?_, fun l' hl' g φ hφ => ?_⟩, hl⟩` and prove the remaining obligations. Rewrite using `[hB h φ hφ]`.

Conclude with `linOm_mem e _ h hφ`. Rewrite using `[hB h φ hφ, hB h (co.rho ψ w φ) (schr_mem hψ _ hφ), linOm_impl ψ e co hco]`. Rewrite using `[hB h φ hφ]`. Conclude with `isUnitaryOn_linOm hq e μ hμ h φ hφ`. Simplify using `only [hB _ φ hφ]`.

Conclude with `isLocallyConstant_linOm hq e _ hφ`. Rewrite using `[hB p φ hφ]`. Conclude with `hS l' h1 h2 p t hp φ hφ`. Rewrite using `[hA g ⟨φ, hφ⟩]`. Conclude with `(M g _).2`.

Rewrite using `[hA g ⟨φ, hφ⟩, Darboux.rho, ← schrS_coe hψ _ ⟨φ, hφ⟩, hA, ← Module.End.mul_apply, hM1]`. Both sides reduce to the same expression. Take `⟨z, hz⟩` from `hu l' l hl' hl`. Rewrite using `[hA g ⟨φ, hφ⟩, hz _ (M g _).2, hz _ hφ]`. Conclude with `congrArg (z * ·) (LinearMap.congr_fun (hM2 g) ⟨φ, hφ⟩)`.
-/
theorem exists_linPair : ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
  ∃ (Cy : Matrix (Fin 2) (Fin 1) E) (co : Darboux (symp c 1 (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) E)) (Fin 4))
    (om : UG c (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) × UG c (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) E) →* Module.End ℂ ((Fin 4 → k) → ℂ))
    (l : ((Fin 4 → k) → ℂ) →ₗ[ℂ] ℂ), IsLinPair c ψ 1 !![0, 1; 1, 0] !![0, 1; -1, 0] co 1 Cy om ∧ IsYForm c ψ co Cy l := by
  intro k _ _ _ _ _ _ E _ _ _ _ c δ hq ψ hψ hn hψ1
  obtain ⟨e, co, hco⟩ := exists_coord hq
  have hL := GlobalTheory.LinPair.Model.lagr_plane c
  obtain ⟨⟨l, hl⟩, hu⟩ := GlobalTheory.LagrFormLine.yform_line k E c δ hq ψ hψ hn hψ1 _ _ _ _ _ _ _ co _ hL
  have hS := siegelRule_linOm hq hψ hψ1 e co hco
  let ω : UG c (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) E) →* Module.End ℂ (SB (Fin 4 → k)) :=
    { toFun := fun h => (linOm e _ h).restrict fun _ hφ => linOm_mem e _ h hφ
      map_one' := LinearMap.ext fun φ => Subtype.ext (LinearMap.congr_fun (linOm e _).map_one φ.1)
      map_mul' := fun h h' => LinearMap.ext fun φ => Subtype.ext (LinearMap.congr_fun ((linOm e _).map_mul h h') φ.1) }
  have hω : ∀ h φ, (ω h φ).1 = linOm e _ h φ.1 := fun _ _ => rfl
  have hl0 : l ∘ₗ (SB (Fin 4 → k)).subtype ≠ 0 := fun h => by
    obtain ⟨φ, hφ, h0⟩ := hl.2
    exact h0 (LinearMap.congr_fun h ⟨φ, hφ⟩)
  obtain ⟨M, hM1, hM2, hM3⟩ := exists_hom_commute (G := UG c (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E))
    (fun w => schrS hψ (co.e w)) (fun T hT => schur hψ hψ1 T fun w => by simpa using hT (co.e.symm w))
    (fun g w => (g : GL (Fin 2) E).val * w) (fun w => by simp) (fun g g' w => by simp [Matrix.mul_assoc])
    (actB c) (fun h w => by simp [actB, Matrix.mul_assoc, ← transpose_mul]) (fun g h w => by simp [actB, Matrix.mul_assoc])
    ω (fun h w => LinearMap.ext fun φ => Subtype.ext (linOm_impl ψ e co hco h w φ.1)) _ hl0
    (fun g => by
      let a : Matrix (Fin 2) (Fin 2) E ≃ₗ[k] Matrix (Fin 2) (Fin 2) E :=
        { toFun := fun w => ((g : GL (Fin 2) E)⁻¹).val * w
          invFun := fun w => (g : GL (Fin 2) E).val * w
          map_add' := fun _ _ => Matrix.mul_add _ _ _
          map_smul' := fun _ _ => Matrix.mul_smul _ _ _
          left_inv := fun w => Units.mul_inv_cancel_left _ _
          right_inv := fun w => Units.inv_mul_cancel_left _ _ }
      obtain ⟨T, hT⟩ := exists_implementer hψ hψ1 (co.e.symm.trans (a.trans co.e)) fun w w' => by
        obtain ⟨w, rfl⟩ := co.e.surjective w
        obtain ⟨w', rfl⟩ := co.e.surjective w'
        simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, ← co.form]
        exact symp_mul g⁻¹ w w'
      have hT' : ∀ w, T.val * schrS hψ (co.e w) = schrS hψ (co.e ((g : GL (Fin 2) E).val * w)) * T.val := fun w => by
        rw [← hT]
        simp [a]
      obtain ⟨l₁, hl₁⟩ := LinearMap.exists_extend (l ∘ₗ (SB (Fin 4 → k)).subtype ∘ₗ T.val)
      have hl₁' : ∀ φ : SB (Fin 4 → k), l₁ φ = l (T.val φ) := fun φ => LinearMap.congr_fun hl₁ φ
      obtain ⟨z, hz⟩ := hu l₁ l (fun y φ hφ => by
        rw [Darboux.rho, ← schrS_coe hψ _ ⟨φ, hφ⟩, hl₁', hl₁' ⟨φ, hφ⟩, ← Module.End.mul_apply, hT', ← Matrix.mul_assoc]
        exact hl.1 _ _ (T.val ⟨φ, hφ⟩).2) hl
      have hz0 : z ≠ 0 := fun h => hl0 (LinearMap.ext fun φ => by
        have := hz _ ((T⁻¹).val φ).2
        rwa [hl₁', h, zero_mul, ← Module.End.mul_apply, Units.mul_inv] at this)
      refine ⟨(Units.mk0 z hz0)⁻¹ • T, fun w => ?_, LinearMap.ext fun φ => ?_⟩
      · simp only [Units.val_smul, smul_mul_assoc, mul_smul_comm, hT']
      · have := hz _ φ.2
        rw [hl₁'] at this
        simp [Units.smul_def, this, hz0])
    {p | (p : GL (Fin 2) E).val 1 0 = 0}
    (fun p hp => by
      have h0 : (p : GL (Fin 2) E).val 0 0 ≠ 0 := fun h => (p : GL (Fin 2) E).det_ne_zero (by
        rw [det_fin_two, h, hp]; simp)
      have key := hS l trivial hl.1 p
        (GeneralLinearGroup.mkOfDetNeZero !![(p : GL (Fin 2) E).val 0 0] (by simpa using h0)) (by
          ext i j
          have hp' : (p : GL (Fin 2) E).val 1 0 = 0 := hp
          fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, hp'])
      have fin : ∀ z : ℂ, z ≠ 0 → (∀ φ ∈ SB (Fin 4 → k), l (linOm e _ p φ) = z * l φ) →
          ∃ z : ℂ, z ≠ 0 ∧ (l ∘ₗ (SB (Fin 4 → k)).subtype) ∘ₗ ω p = z • (l ∘ₗ (SB (Fin 4 → k)).subtype) :=
        fun z hz h => ⟨z, hz, LinearMap.ext fun φ => h φ φ.2⟩
      exact fin _ (mul_ne_zero (Circle.coe_ne_zero _)
        (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (distribHaarChar_pos (A := k)) _).ne')) key)
    char_eq_one
  obtain ⟨x, hx⟩ := exists_extend_hom (SB (Fin 4 → k))
  let om := x.comp (M.noncommCoprod ω hM3)
  have hB : ∀ h, ∀ φ ∈ SB (Fin 4 → k), om.comp (MonoidHom.inr _ _) h φ = linOm e _ h φ := fun h φ hφ => by
    rw [← hω h ⟨φ, hφ⟩, ← hx]
    simp [om]
  have hA : ∀ g (φ : SB (Fin 4 → k)), om (g, 1) φ = M g φ := fun g φ => by
    rw [← hx]
    simp [om]
  refine ⟨_, co, om, l, ⟨⟨hL, ⟨⟨fun h φ hφ => ?_, fun h w φ hφ => ?_, fun _ _ _ => trivial⟩, fun μ hμ h φ hφ => ?_,
    .of_isLocallyConstant fun φ hφ => ?_⟩, fun l' h1 h2 p t hp φ hφ => ?_⟩, fun g φ hφ => ?_, fun g w φ hφ => ?_,
    fun l' hl' g φ hφ => ?_⟩, hl⟩
  · rw [hB h φ hφ]
    exact linOm_mem e _ h hφ
  · rw [hB h φ hφ, hB h (co.rho ψ w φ) (schr_mem hψ _ hφ), linOm_impl ψ e co hco]
  · rw [hB h φ hφ]
    exact isUnitaryOn_linOm hq e μ hμ h φ hφ
  · simp only [hB _ φ hφ]
    exact isLocallyConstant_linOm hq e _ hφ
  · rw [hB p φ hφ]
    exact hS l' h1 h2 p t hp φ hφ
  · rw [hA g ⟨φ, hφ⟩]
    exact (M g _).2
  · rw [hA g ⟨φ, hφ⟩, Darboux.rho, ← schrS_coe hψ _ ⟨φ, hφ⟩, hA, ← Module.End.mul_apply, hM1]
    rfl
  · obtain ⟨z, hz⟩ := hu l' l hl' hl
    rw [hA g ⟨φ, hφ⟩, hz _ (M g _).2, hz _ hφ]
    exact congrArg (z * ·) (LinearMap.congr_fun (hM2 g) ⟨φ, hφ⟩)

end GlobalTheory.HypPair

end
