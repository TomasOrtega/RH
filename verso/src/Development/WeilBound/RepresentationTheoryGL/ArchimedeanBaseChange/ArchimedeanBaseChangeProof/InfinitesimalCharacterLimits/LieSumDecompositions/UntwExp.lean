import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.GrowPHolds
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpTw
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SqIntCritHolds

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux.Tw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

omit [IsCMField E] in
/- English proof (translation)
Rewrite using `[Complex.div_re]`. Simplify using `[hz]`.
-/
theorem re_tw {z : ℂ} (hz : z.re = 0) : (z / (N * (Module.finrank ℚ E : ℂ))).re = 0 := by
  rw [Complex.div_re]
  simp [hz]

/- English proof (translation)
Establish `hd : (Module.finrank ℚ E : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Module.finrank_pos.ne'`. Establish `hNc : (N : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`. Use `set w := z / (N * (Module.finrank ℚ E : ℂ)) with hw`. Establish `hcd : ∀ t : ℝ, ((chiDet N (Model.absC E (-w)) (splitCentre E N t) : ℂˣ) : ℂ) = Complex.exp (-(z * t))`. Introduce `t`.

Rewrite using `[ExponentTwist.splitCentre_eq, ExponentTwist.chiDet_aT le_rfl]`. Use `congr 1`. Rewrite using `[hw]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[mulChi_apply, mulChi_apply, hc t g, map_mul, Units.val_mul, hcd t]`.

Establish `e : Complex.exp (z * t) * Complex.exp (-(z * t)) = 1`. Rewrite using `[← Complex.exp_add]`. Simplify using the standard rewrite rules. Take the linear combination `(φ.1 g * ((chiDet N (Model.absC E (-w)) g : ℂˣ) : ℂ)) * e`.
-/
theorem untw_cen (hN : 0 < N) {z : ℂ} {φ : Sm E N}
    (hc : ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = Complex.exp (z * t) * φ.1 g) (t : ℝ) (g : GA E N) :
    (mulChi N (Model.absC E (-(z / (N * (Module.finrank ℚ E : ℂ))))) φ).1 (splitCentre E N t * g) =
      (mulChi N (Model.absC E (-(z / (N * (Module.finrank ℚ E : ℂ))))) φ).1 g := by
  have hd : (Module.finrank ℚ E : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  set w := z / (N * (Module.finrank ℚ E : ℂ)) with hw
  have hcd : ∀ t : ℝ, ((chiDet N (Model.absC E (-w)) (splitCentre E N t) : ℂˣ) : ℂ) = Complex.exp (-(z * t)) := by
    intro t
    rw [ExponentTwist.splitCentre_eq, ExponentTwist.chiDet_aT le_rfl]
    congr 1
    rw [hw]
    field_simp
  rw [mulChi_apply, mulChi_apply, hc t g, map_mul, Units.val_mul, hcd t]
  have e : Complex.exp (z * t) * Complex.exp (-(z * t)) = 1 := by
    rw [← Complex.exp_add]; simp
  linear_combination (φ.1 g * ((chiDet N (Model.absC E (-w)) g : ℂˣ) : ℂ)) * e

/- English proof (translation)
Establish `hd : (Module.finrank ℚ E : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Module.finrank_pos.ne'`. Establish `hNc : (N : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Use `set w := z / (N * (Module.finrank ℚ E : ℂ)) with hw`. Establish `h1` using `expTw_holds E N φ (-w) hA r hr hrN c hc`. Use `⟨_, h1, ?_⟩` and prove the remaining obligations.

Establish `e : -w * (r : ℂ) * (Module.finrank ℚ E : ℂ) = (((-(r : ℝ) / N) : ℝ) : ℂ) * z`. Rewrite using `[hw]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `hre : (c - -w * (r : ℂ) * (Module.finrank ℚ E : ℂ)).re = c.re`.

Rewrite using `[e, Complex.sub_re, Complex.re_ofReal_mul, hz, mul_zero, sub_zero]`. Unfold `pE`. Rewrite using `[hre]`.
-/
theorem untw_exp {z : ℂ} (hz : z.re = 0) {φ : Sm E N} (hA : IsAutForm φ) (r : ℕ) (hr : 0 < r) (hrN : r < N) (c : ℂ)
    (hc : c ∈ Exp r (mulChi N (Model.absC E (-(z / (N * (Module.finrank ℚ E : ℂ))))) φ).1) :
    ∃ c' ∈ Exp r φ.1, pE E N r c = pE E N r c' := by
  have hd : (Module.finrank ℚ E : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set w := z / (N * (Module.finrank ℚ E : ℂ)) with hw
  have h1 := expTw_holds E N φ (-w) hA r hr hrN c hc
  refine ⟨_, h1, ?_⟩
  have e : -w * (r : ℂ) * (Module.finrank ℚ E : ℂ) = (((-(r : ℝ) / N) : ℝ) : ℂ) * z := by
    rw [hw]; push_cast; field_simp
  have hre : (c - -w * (r : ℂ) * (Module.finrank ℚ E : ℂ)).re = c.re := by
    rw [e, Complex.sub_re, Complex.re_ofReal_mul, hz, mul_zero, sub_zero]
  unfold pE
  rw [hre]

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux.Tw

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

open Tw ParabolicProjection in
/- English proof (translation)
Introduce `E _ _ _ N τ hN U hU φ hφU hneg hφ0`. Take `⟨⟨hst, hA⟩, -, hNP, ⟨z, hz, hcent⟩, -⟩` from `hU`. Use `set w := z / (N * (Module.finrank ℚ E : ℂ)) with hw`. Establish `hU'st : IsStable (tw U (-w))` using `isStable_tw hst (-w)`. Establish `hU'A : ∀ χ ∈ tw U (-w), IsAutForm χ`.

Introduce and unpack `_ ⟨ψ, hψ, rfl⟩`. Conclude with `(hA ψ hψ).mulChi _`. Establish `hU'P : ∀ χ ∈ tw U (-w), GrowP χ.1`. Introduce and unpack `_ ⟨ψ, hψ, rfl⟩`. Use `hP E N _ ((hA ψ hψ).mulChi _) (untw_cen hN (hcent ψ hψ)) fun r hr hrN c hc => ?_` and prove the remaining obligations.

Take `⟨c', hc', e⟩` from `untw_exp hz (hA ψ hψ) r hr hrN c hc`. Rewrite using `[e]`. Conclude with `hNP ψ hψ r hr hrN c' hc'`. Establish `hφ'A2 : mulChi N (Model.absC E (-w)) φ ∈ A2 E N`. Use `Submodule.subset_span ⟨(hA φ hφU).mulChi _, sqIntCrit_holds E N _ ((hA φ hφU).mulChi _) (untw_cen hN (hcent φ hφU)) fun r hr hrN c hc => ?_⟩` and prove the remaining obligations.

Take `⟨c', hc', e⟩` from `untw_exp hz (hA φ hφU) r hr hrN c hc`. Rewrite using `[e]`. Conclude with `hneg r hr hrN c' hc'`. Establish `hφ'0 : mulChi N (Model.absC E (-w)) φ ≠ 0`. Rewrite using `[Ne, LinearEquiv.map_eq_zero_iff]`.

Conclude with `hφ0`. Take `⟨V, p, hV, hpV, hpe, hp0⟩` from `hC E N (tw U (-w)) hU'st hU'A hU'P _ ⟨φ, hφU, rfl⟩ hφ'A2 hφ'0`. Establish `hUle : ∀ ψ ∈ U, ψ ∈ tw (tw U (-w)) w` using `fun ψ hψ => ⟨_, ⟨ψ, hψ, rfl⟩, mulChi_absC_neg' N w ψ⟩`. Use `⟨.leaf V w, twMap N w p, Or.inr ⟨hN, hV, re_tw hz⟩, hN, fun o ψ hψ => twMap_equiv hU'st hpe o ψ (hUle ψ hψ), fun ψ hψ => twMap_mem hpV ψ (hUle ψ hψ), ?_⟩` and prove the remaining obligations. Rewrite using `[twMap_apply, Ne, LinearEquiv.map_eq_zero_iff]`.

Conclude with `hp0`.
-/
theorem leaf_of (hC : Core) (hP : GrowPHolds) : Leaf := by
  intro E _ _ _ N τ hN U hU φ hφU hneg hφ0
  obtain ⟨⟨hst, hA⟩, -, hNP, ⟨z, hz, hcent⟩, -⟩ := hU
  set w := z / (N * (Module.finrank ℚ E : ℂ)) with hw
  have hU'st : IsStable (tw U (-w)) := isStable_tw hst (-w)
  have hU'A : ∀ χ ∈ tw U (-w), IsAutForm χ := by
    rintro _ ⟨ψ, hψ, rfl⟩
    exact (hA ψ hψ).mulChi _
  have hU'P : ∀ χ ∈ tw U (-w), GrowP χ.1 := by
    rintro _ ⟨ψ, hψ, rfl⟩
    refine hP E N _ ((hA ψ hψ).mulChi _) (untw_cen hN (hcent ψ hψ)) fun r hr hrN c hc => ?_
    obtain ⟨c', hc', e⟩ := untw_exp hz (hA ψ hψ) r hr hrN c hc
    rw [e]
    exact hNP ψ hψ r hr hrN c' hc'
  have hφ'A2 : mulChi N (Model.absC E (-w)) φ ∈ A2 E N := by
    refine Submodule.subset_span ⟨(hA φ hφU).mulChi _, sqIntCrit_holds E N _ ((hA φ hφU).mulChi _)
      (untw_cen hN (hcent φ hφU)) fun r hr hrN c hc => ?_⟩
    obtain ⟨c', hc', e⟩ := untw_exp hz (hA φ hφU) r hr hrN c hc
    rw [e]
    exact hneg r hr hrN c' hc'
  have hφ'0 : mulChi N (Model.absC E (-w)) φ ≠ 0 := by
    rw [Ne, LinearEquiv.map_eq_zero_iff]; exact hφ0
  obtain ⟨V, p, hV, hpV, hpe, hp0⟩ :=
    hC E N (tw U (-w)) hU'st hU'A hU'P _ ⟨φ, hφU, rfl⟩ hφ'A2 hφ'0
  have hUle : ∀ ψ ∈ U, ψ ∈ tw (tw U (-w)) w := fun ψ hψ => ⟨_, ⟨ψ, hψ, rfl⟩, mulChi_absC_neg' N w ψ⟩
  refine ⟨.leaf V w, twMap N w p, Or.inr ⟨hN, hV, re_tw hz⟩, hN,
    fun o ψ hψ => twMap_equiv hU'st hpe o ψ (hUle ψ hψ), fun ψ hψ => twMap_mem hpV ψ (hUle ψ hψ), ?_⟩
  rw [twMap_apply, Ne, LinearEquiv.map_eq_zero_iff]
  exact hp0

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

end
