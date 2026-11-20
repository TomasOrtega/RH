import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchSmulAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.NormDiag
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ConjDesc
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.StrictNormal
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bridge

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[val_diagT]`. Simplify using `[val_diagT, Matrix.diagonal_apply, hij]`.
-/
private theorem map_diag {E F : Type} [Field E] [Field F] {n : ℕ} (f : E →+* F) (u : Fin n → Eˣ) :
    Matrix.GeneralLinearGroup.map f (diagT E (Fin n) u) = diagT F (Fin n) fun i => Units.map (f : E →* F) (u i) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [val_diagT]
  · simp [val_diagT, Matrix.diagonal_apply, hij]

/- English proof (translation)
Rewrite using `[← map_mul, ← map_mul, mul_comm]`.
-/
private theorem diag_comm {E : Type} [Field E] {n : ℕ} (u v : Fin n → Eˣ) :
    diagT E (Fin n) u * diagT E (Fin n) v = diagT E (Fin n) v * diagT E (Fin n) u := by
  rw [← map_mul, ← map_mul, mul_comm]

/- English proof (translation)
Introduce `i j hij`. Establish `h` using `ht i j hij`. Rewrite `h` using `[← (valuation k).vlt_iff_lt]`. Rewrite using `[← (valuation E).vlt_iff_lt]`. Simplify using `only [Units.coe_map, MonoidHom.coe_coe]`.

Introduce `hle`. Conclude with `h ((ValuativeExtension.vle_iff_vle _ _).mp hle)`.
-/
private theorem strict_map {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] {n : ℕ} {t : Fin n → kˣ} (ht : Strict t) :
    Strict fun i => Units.map (algebraMap k E : k →* E) (t i) := by
  intro i j hij
  have h := ht i j hij
  rw [← (valuation k).vlt_iff_lt] at h
  rw [← (valuation E).vlt_iff_lt]
  simp only [Units.coe_map, MonoidHom.coe_coe]
  intro hle
  exact h ((ValuativeExtension.vle_iff_vle _ _).mp hle)

/- English proof (translation)
Introduce `k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hσ n δ h y γ d hd hnorm hy`. Take `⟨hcyc, -, hb⟩` from `bridge k E σ`. Take `⟨hsg, hnrm, -, -, -⟩` from `hb n`. Take `⟨hND, -, -⟩` from `normDiag k E σ hσ n`. Take `⟨hN, hstr, hreg⟩` from `hND d`.

Establish `e` using `nrm_conj hcyc.ord δ y`. Rewrite `e` using `[hsg y, hy, hnrm, hnrm, hN, hnorm]`. Use `set T := diagT k (Fin n) (UpperTheory.Gal.InertialTypesAlt.L.nrmT k d) with hTdef`. Take `⟨z, hz⟩` from `conjDesc k E n T γ (hreg hd) ⟨h⁻¹ * y, by rw [e]; group⟩`. Use `⟨z, by rw [hz]; group, ?_⟩` and prove the remaining obligations.

Introduce `t ht`. Establish `hct : γ * t = t * γ` using `Subgroup.mem_centralizer_iff.mp ht γ rfl`. Use `set m : Fin n → Eˣ := fun i => Units.map (algebraMap k E : k →* E) (UpperTheory.Gal.InertialTypesAlt.L.nrmT k d i) with hm`. Establish `hms : Strict m` using `strict_map (hstr hd)`. Establish `hT : (incl T : GL (Fin n) E) = diagT E (Fin n) m` using `map_diag (algebraMap k E) _`.

Establish `hrefl : Cyc (RingEquiv.refl E) 1` using `⟨fun x => rfl, one_pos, fun x => rfl⟩`. Establish `hsgr : ∀ g : GL (Fin n) E, sg (RingEquiv.refl E) g = g`. Introduce `g`. Use extensionality with `i j`. Both sides reduce to the same expression.

Use `set u := z⁻¹ * t * z with hu`. Establish `huc : u * T = T * u`. Establish `hz' : T = z⁻¹ * γ * z` using `by rw [hz]; group`. Rewrite using `[hz', hu]`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨s2, hs2⟩` from `strictNormal E n (RingEquiv.refl E) 1 hrefl m m hms hms (incl u) (by`. Rewrite using `[hsgr, ← hT, ← map_inv, ← map_mul, ← map_mul, mul_assoc, ← huc]`. Use `congr 1`. Use the proof step `group)`. Use `set w := y⁻¹ * h * incl z with hw`.

Establish `hg : (incl γ : GL (Fin n) E) = incl z * incl T * (incl z)⁻¹`. Rewrite using `[hz]`. Simplify using `only [map_mul, map_inv]`. Establish `hwc0 : (incl T : GL (Fin n) E) = w * incl T * w⁻¹` using `by conv_lhs => rw [e]`. Rewrite using `[hg, hw]`.

Use `group`. Establish `hwc : w⁻¹ * diagT E (Fin n) m * w = diagT E (Fin n) m`. Rewrite using `[← hT]`. Use `conv_lhs => rw [hwc0]`. Use `group`.

Take `⟨s1, hs1⟩` from `strictNormal E n (RingEquiv.refl E) 1 hrefl m m hms hms w (by rw [hsgr]; exact hwc)`. Establish `ht' : (incl t : GL (Fin n) E) = incl z * incl u * (incl z)⁻¹`. Rewrite using `[hu]`. Simplify using `only [map_mul, map_inv]`. Use `group`.

Establish `key : y⁻¹ * (h * incl t * h⁻¹) * y = w * incl u * w⁻¹`. Rewrite using `[ht', hw]`. Use `group`. Rewrite using `[key, hs1, hs2, diag_comm]`. Use `group`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.L.align :
    UpperTheory.Gal.InertialTypesAlt.L.Align := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hσ n δ h y γ d hd hnorm hy
  obtain ⟨hcyc, -, hb⟩ := bridge k E σ
  obtain ⟨hsg, hnrm, -, -, -⟩ := hb n
  obtain ⟨hND, -, -⟩ := normDiag k E σ hσ n
  obtain ⟨hN, hstr, hreg⟩ := hND d
  have e := nrm_conj hcyc.ord δ y
  rw [hsg y, hy, hnrm, hnrm, hN, hnorm] at e
  set T := diagT k (Fin n) (UpperTheory.Gal.InertialTypesAlt.L.nrmT k d) with hTdef
  obtain ⟨z, hz⟩ := conjDesc k E n T γ (hreg hd) ⟨h⁻¹ * y, by rw [e]; group⟩
  refine ⟨z, by rw [hz]; group, ?_⟩
  intro t ht
  have hct : γ * t = t * γ := Subgroup.mem_centralizer_iff.mp ht γ rfl
  set m : Fin n → Eˣ := fun i => Units.map (algebraMap k E : k →* E) (UpperTheory.Gal.InertialTypesAlt.L.nrmT k d i) with hm
  have hms : Strict m := strict_map (hstr hd)
  have hT : (incl T : GL (Fin n) E) = diagT E (Fin n) m := map_diag (algebraMap k E) _
  have hrefl : Cyc (RingEquiv.refl E) 1 := ⟨fun x => rfl, one_pos, fun x => rfl⟩
  have hsgr : ∀ g : GL (Fin n) E, sg (RingEquiv.refl E) g = g := by
    intro g
    ext i j
    rfl
  set u := z⁻¹ * t * z with hu
  have huc : u * T = T * u := by
    have hz' : T = z⁻¹ * γ * z := by rw [hz]; group
    rw [hz', hu]
    calc z⁻¹ * t * z * (z⁻¹ * γ * z) = z⁻¹ * (t * γ) * z := by group
      _ = z⁻¹ * (γ * t) * z := by rw [hct]
      _ = z⁻¹ * γ * z * (z⁻¹ * t * z) := by group
  obtain ⟨s2, hs2⟩ := strictNormal E n (RingEquiv.refl E) 1 hrefl m m hms hms (incl u) (by
    rw [hsgr, ← hT, ← map_inv, ← map_mul, ← map_mul, mul_assoc, ← huc]
    congr 1
    group)
  set w := y⁻¹ * h * incl z with hw
  have hg : (incl γ : GL (Fin n) E) = incl z * incl T * (incl z)⁻¹ := by
    rw [hz]
    simp only [map_mul, map_inv]
  have hwc0 : (incl T : GL (Fin n) E) = w * incl T * w⁻¹ := by
    conv_lhs => rw [e]
    rw [hg, hw]
    group
  have hwc : w⁻¹ * diagT E (Fin n) m * w = diagT E (Fin n) m := by
    rw [← hT]
    conv_lhs => rw [hwc0]
    group
  obtain ⟨s1, hs1⟩ := strictNormal E n (RingEquiv.refl E) 1 hrefl m m hms hms w (by rw [hsgr]; exact hwc)
  have ht' : (incl t : GL (Fin n) E) = incl z * incl u * (incl z)⁻¹ := by
    rw [hu]
    simp only [map_mul, map_inv]
    group
  have key : y⁻¹ * (h * incl t * h⁻¹) * y = w * incl u * w⁻¹ := by
    rw [ht', hw]
    group
  rw [key, hs1, hs2, diag_comm]
  group
