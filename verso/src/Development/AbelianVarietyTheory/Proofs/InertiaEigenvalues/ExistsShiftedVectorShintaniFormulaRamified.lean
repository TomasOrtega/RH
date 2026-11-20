import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CondExpEqZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicWhittakerEquivariantBumpMirabolicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovSemilocalSmoothBumpStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaCellsDisjointOffFinset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAutomorphicFormFixedOfLocallyIntegralFixedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerMulTorusShiftAddEqSphericalProductStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSphericalWhittakerTorusElementNeZeroStatement

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

namespace GlobalTheory.RamShift

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

/- English proof (translation)
Establish `h` using `infGL_mul_finGL q`. Rewrite `h` using `[hq, map_one, one_mul]`. Conclude with `h.symm`.
-/
theorem eq_finGL_of_pInf {q : GA E n} (hq : GeneralLinearGroup.map (pInf E) q = 1) :
    q = finGL E n (GeneralLinearGroup.map (pFin E) q) := by
  have h := infGL_mul_finGL q
  rw [hq, map_one, one_mul] at h
  exact h.symm

/- English proof (translation)
Unfold `GlobalTheory.CellDec.tl`. Conclude with `pInf_finGL _`.
-/
theorem pInf_tl (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) :
    GeneralLinearGroup.map (pInf E) (GlobalTheory.CellDec.tl n ϖ l) = 1 := by
  unfold GlobalTheory.CellDec.tl
  exact pInf_finGL _

/- English proof (translation)
Rewrite using `[GlobalTheory.CellDec.compV_tl, hv, GlobalTheory.IwaCell.tD_zero]`.
-/
theorem compV_tl_of_eq_zero (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) {v : HeightOneSpectrum (𝓞 E)} (hv : l v = 0) :
    GlobalTheory.CellDec.compV E n v (GlobalTheory.CellDec.tl n ϖ l) = 1 := by
  rw [GlobalTheory.CellDec.compV_tl, hv, GlobalTheory.IwaCell.tD_zero]

/- English proof (translation)
Use `⟨fun w _ => map_one _, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_one, Matrix.one_apply]`. Distinguish the cases in `h : j = Fin.last m`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg (Ne.symm h), if_neg h]`.
-/
theorem one_mem_mirS (S : Finset (HeightOneSpectrum (𝓞 E))) (m : ℕ) : (1 : GA E (m + 1)) ∈ GlobalTheory.JSW.mirS E S m := by
  refine ⟨fun w _ => map_one _, fun j => ?_⟩
  rw [Units.val_one, Matrix.one_apply]
  by_cases h : j = Fin.last m
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]

/- English proof (translation)
The claim follows from `(GlobalTheory.SmGL.mem_unipB (Ad E)).2 ⟨fun i j hij => hu.1 i j hij, hu.2⟩`.
-/
theorem mem_NA_of_mem {u : GA E n} (hu : u ∈ GlobalTheory.JSW.NA E n) : u ∈ GlobalTheory.CellDec.NA E n :=
  (GlobalTheory.SmGL.mem_unipB (Ad E)).2 ⟨fun i j hij => hu.1 i j hij, hu.2⟩

end GlobalTheory.RamShift

open GlobalTheory.RamShift in

/- English proof (translation)
Introduce `E _ _ _ m T π _ α hα ϖ hϖ`. Use `set l₀ := shift m T ϖ with hl₀`. Use `set t₀ := GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 with ht₀def`. Establish `ht₀inf : GeneralLinearGroup.map (pInf E) t₀ = 1` using `pInf_tl ϖ l₀.1`. Use `set D := GeneralLinearGroup.map (pFin E) t₀ with hD`.

Establish `ht₀ : t₀ = finGL E (m + 1) D` using `eq_finGL_of_pInf ht₀inf`. Take `⟨b, hb1, hbN, hbC, hbU, hbS⟩` from `GlobalTheory.T.exists_adelic_whittaker_equivariant_bump_mirabolic E m T`. Take `⟨φ, hφV, hφK, x₀, hx₀, hW₀⟩` from `GlobalTheory.T.exists_spherical_whittaker_torusElement_ne_zero E m T π α hα ϖ hϖ`. Use `set φ' := act (.fin D) φ with hφ'def`. Establish `hφ'V : φ' ∈ π.V` using `π.stable _ φ hφV`.

Establish `hφ' : ∀ g, φ'.1 g = φ.1 (g * t₀)` using `fun g => by rw [ht₀]; rfl`. Establish `hWφ' : ∀ y, whit φ'.1 y = whit φ.1 (y * t₀)` using `fun y => by`. Rewrite using `[whit_mul_right]`. Use `congr 1`. Use function extensionality and compare the values at `z`.

Conclude with `hφ' z`. Take `⟨F₀, hF₀V, hF₀b, hF₀U, hF₀inv, hF₀rel⟩` from `GlobalTheory.T.kirillov_semilocal_smooth_bump E m T b hbN hbC hbU hbS π φ' hφ'V ⟨x₀, hx₀, by rw [hWφ']; exact hW₀⟩`. Establish `hWF : ∀ y, whit (fun g => F₀ (g * t₀⁻¹)) y = whit F₀ (y * t₀⁻¹)` using `fun y => (whit_mul_right F₀ y t₀⁻¹).symm`. Use `⟨fun g => F₀ (g * t₀⁻¹), mspanR_rt hF₀V _, l₀, fun w => shift_last m T ϖ w, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨U, hUo, hU⟩` from `hF₀U`.

Use `⟨U.comap (MulAut.conj D).toMonoidHom, ?_, fun u hu g => ?_⟩` and prove the remaining obligations. Conclude with `hUo.preimage ((continuous_const.mul continuous_id).mul continuous_const)`. Establish `e : g * finGL E (m + 1) u * t₀⁻¹ = g * t₀⁻¹ * finGL E (m + 1) (D * u * D⁻¹)`. Rewrite using `[ht₀, map_mul, map_mul, map_inv]`. Use `group`.

Use `show F₀ (g * finGL E (m + 1) u * t₀⁻¹) = F₀ (g * t₀⁻¹)`. Rewrite using `[e]`. Conclude with `hU _ hu _`. Introduce `k hk hkinf hkT g`. Establish `hkf` using `eq_finGL_of_pInf hkinf`.

Use `set kf := GeneralLinearGroup.map (pFin E) k with hkfdef`. Establish `hφk : act (.fin kf) φ = φ` using `GlobalTheory.T.smoothAutomorphicForm_fixed_of_locally_integral_fixed E (m + 1) φ (π.cusp φ hφV).1 T hφK kf (fun w hw => by`. Use `GlobalTheory.CellDec.mem_US.1 hk w hw` as an intermediate fact. Conclude with `this)`. Use the proof step `(fun w hw => hkT w hw)`.

Establish `e : g * k * t₀⁻¹ = g * t₀⁻¹ * (t₀ * k * t₀⁻¹)` using `by group`. Use `show F₀ (g * k * t₀⁻¹) = F₀ (g * t₀⁻¹)`. Rewrite using `[e]`. Use `hF₀inv _ ?_ ?_ ?_ _` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_inv, ht₀inf, hkinf]`.

Simplify using the standard rewrite rules. Introduce `w hw`. Express the relevant statement in the definitionally equal form `GlobalTheory.CellDec.compV E (m + 1) w (t₀ * k * t₀⁻¹) = 1`. Rewrite using `[map_mul, map_mul, map_inv, compV_tl_of_eq_zero ϖ l₀.1 (l₀.2 w hw), hkT w hw]`. Simplify using the standard rewrite rules.

Introduce `y`. Rewrite using `[hφ', hφ']`. Establish `e2 : y * (t₀ * k * t₀⁻¹) * t₀ = y * t₀ * finGL E (m + 1) kf` using `by rw [← hkf]; group`. Rewrite using `[e2]`. Conclude with `congrArg (fun ψ : Sm E (m + 1) => ψ.1 (y * t₀)) hφk`.

Rewrite using `[hWF, mul_inv_cancel, hF₀b 1 (one_mem_mirS T m), hb1]`. Conclude with `one_ne_zero`. Take `⟨C, hC, hCp⟩` from `hbC`. Use `⟨C, hC, fun p hp hne => ?_⟩` and prove the remaining obligations. Rewrite `hne` using `[hWF, mul_inv_cancel_right, hF₀b p hp]`.

Take `⟨u, hu, hup⟩` from `hCp p hp hne`. Conclude with `⟨u⁻¹, inv_mem (mem_NA_of_mem hu), hup⟩`. Introduce `p hp l hl`. Establish `hcomm : GlobalTheory.CellDec.tl (m + 1) ϖ (l₀.1 + l.1) = GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * t₀`. Rewrite using `[add_comm l₀.1 l.1, GlobalTheory.CellDec.tl_add]`.

Rewrite using `[hWF, hWF, hcomm, ← mul_assoc, mul_inv_cancel_right, mul_inv_cancel_right]`. Rewrite using `[hF₀rel (GlobalTheory.CellDec.tl (m + 1) ϖ l.1) _ (pInf_tl ϖ l.1) (fun w hw => compV_tl_of_eq_zero ϖ l.1 (l.2 w hw)) (fun x hx => ?_) p hp.1, mul_comm]`. Rewrite using `[hWφ', hWφ', mul_assoc, ← GlobalTheory.CellDec.tl_add, add_comm l.1 l₀.1, GlobalTheory.T.whittaker_mul_torusShift_add_eq_sphericalProduct E m T π α hα φ hφV hφK ϖ hϖ x hx l hl, mul_comm]`.
-/
theorem GlobalTheory.RamShift.exists_shifted_bump_shintani : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (π : CuspSub E (m + 1)), π.IsUnitary → ∀ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ),
    (∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w))) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∃ F ∈ GlobalTheory.JSW.mspanR π, ∃ l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, l₀.1 w (Fin.last m) = 0) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧
      (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
        (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, F (g * k) = F g) ∧
      GlobalTheory.JSW.whit F (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 ∧
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E T m,
        GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 → ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * p ∈ C) ∧
      ∀ p ∈ GlobalTheory.JSW.mirS E T m, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, 0 ≤ l.1 w (Fin.last m)) →
        GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ (l₀.1 + l.1)) = GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) *
          ∏ w ∈ l.1.support, (if h : w ∈ T then 1 else
            GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) (l.1 w)) := by
  intro E _ _ _ m T π _ α hα ϖ hϖ
  set l₀ := shift m T ϖ with hl₀
  set t₀ := GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 with ht₀def
  have ht₀inf : GeneralLinearGroup.map (pInf E) t₀ = 1 := pInf_tl ϖ l₀.1
  set D := GeneralLinearGroup.map (pFin E) t₀ with hD
  have ht₀ : t₀ = finGL E (m + 1) D := eq_finGL_of_pInf ht₀inf
  obtain ⟨b, hb1, hbN, hbC, hbU, hbS⟩ := GlobalTheory.T.exists_adelic_whittaker_equivariant_bump_mirabolic E m T
  obtain ⟨φ, hφV, hφK, x₀, hx₀, hW₀⟩ := GlobalTheory.T.exists_spherical_whittaker_torusElement_ne_zero E m T π α hα ϖ hϖ
  set φ' := act (.fin D) φ with hφ'def
  have hφ'V : φ' ∈ π.V := π.stable _ φ hφV
  have hφ' : ∀ g, φ'.1 g = φ.1 (g * t₀) := fun g => by rw [ht₀]; rfl
  have hWφ' : ∀ y, whit φ'.1 y = whit φ.1 (y * t₀) := fun y => by
    rw [whit_mul_right]
    congr 1
    funext z
    exact hφ' z
  obtain ⟨F₀, hF₀V, hF₀b, hF₀U, hF₀inv, hF₀rel⟩ :=
    GlobalTheory.T.kirillov_semilocal_smooth_bump E m T b hbN hbC hbU hbS π φ' hφ'V ⟨x₀, hx₀, by rw [hWφ']; exact hW₀⟩
  have hWF : ∀ y, whit (fun g => F₀ (g * t₀⁻¹)) y = whit F₀ (y * t₀⁻¹) := fun y =>
    (whit_mul_right F₀ y t₀⁻¹).symm
  refine ⟨fun g => F₀ (g * t₀⁻¹), mspanR_rt hF₀V _, l₀, fun w => shift_last m T ϖ w, ?_, ?_, ?_, ?_, ?_⟩
  ·
    obtain ⟨U, hUo, hU⟩ := hF₀U
    refine ⟨U.comap (MulAut.conj D).toMonoidHom, ?_, fun u hu g => ?_⟩
    · exact hUo.preimage ((continuous_const.mul continuous_id).mul continuous_const)
    · have e : g * finGL E (m + 1) u * t₀⁻¹ = g * t₀⁻¹ * finGL E (m + 1) (D * u * D⁻¹) := by
        rw [ht₀, map_mul, map_mul, map_inv]; group
      show F₀ (g * finGL E (m + 1) u * t₀⁻¹) = F₀ (g * t₀⁻¹)
      rw [e]
      exact hU _ hu _
  ·
    intro k hk hkinf hkT g
    have hkf := eq_finGL_of_pInf hkinf
    set kf := GeneralLinearGroup.map (pFin E) k with hkfdef
    have hφk : act (.fin kf) φ = φ := GlobalTheory.T.smoothAutomorphicForm_fixed_of_locally_integral_fixed E (m + 1) φ (π.cusp φ hφV).1 T hφK kf
      (fun w hw => by
        have := GlobalTheory.CellDec.mem_US.1 hk w hw
        exact this)
      (fun w hw => hkT w hw)
    have e : g * k * t₀⁻¹ = g * t₀⁻¹ * (t₀ * k * t₀⁻¹) := by group
    show F₀ (g * k * t₀⁻¹) = F₀ (g * t₀⁻¹)
    rw [e]
    refine hF₀inv _ ?_ ?_ ?_ _
    · rw [map_mul, map_mul, map_inv, ht₀inf, hkinf]; simp
    · intro w hw
      change GlobalTheory.CellDec.compV E (m + 1) w (t₀ * k * t₀⁻¹) = 1
      rw [map_mul, map_mul, map_inv, compV_tl_of_eq_zero ϖ l₀.1 (l₀.2 w hw), hkT w hw]; simp
    · intro y
      rw [hφ', hφ']
      have e2 : y * (t₀ * k * t₀⁻¹) * t₀ = y * t₀ * finGL E (m + 1) kf := by rw [← hkf]; group
      rw [e2]
      exact congrArg (fun ψ : Sm E (m + 1) => ψ.1 (y * t₀)) hφk
  ·
    rw [hWF, mul_inv_cancel, hF₀b 1 (one_mem_mirS T m), hb1]
    exact one_ne_zero
  ·
    obtain ⟨C, hC, hCp⟩ := hbC
    refine ⟨C, hC, fun p hp hne => ?_⟩
    rw [hWF, mul_inv_cancel_right, hF₀b p hp] at hne
    obtain ⟨u, hu, hup⟩ := hCp p hp hne
    exact ⟨u⁻¹, inv_mem (mem_NA_of_mem hu), hup⟩
  ·
    intro p hp l hl
    have hcomm : GlobalTheory.CellDec.tl (m + 1) ϖ (l₀.1 + l.1) = GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * t₀ := by
      rw [add_comm l₀.1 l.1, GlobalTheory.CellDec.tl_add]
    rw [hWF, hWF, hcomm, ← mul_assoc, mul_inv_cancel_right, mul_inv_cancel_right]
    rw [hF₀rel (GlobalTheory.CellDec.tl (m + 1) ϖ l.1) _ (pInf_tl ϖ l.1)
      (fun w hw => compV_tl_of_eq_zero ϖ l.1 (l.2 w hw)) (fun x hx => ?_) p hp.1, mul_comm]
    rw [hWφ', hWφ', mul_assoc, ← GlobalTheory.CellDec.tl_add, add_comm l.1 l₀.1, GlobalTheory.T.whittaker_mul_torusShift_add_eq_sphericalProduct E m T π α hα φ hφV hφK ϖ hϖ x hx l hl, mul_comm]
