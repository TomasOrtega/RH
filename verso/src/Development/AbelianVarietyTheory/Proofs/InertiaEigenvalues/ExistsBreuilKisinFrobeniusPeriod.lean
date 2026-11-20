import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompatibleRootsOfUnityAndTiltPadic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineThetaEqZeroIffFontaineXiElementDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfUnitFrobeniusEqMulStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Introduce `l hl K bk`. Take `⟨ζ, e, h0, -, h1, hr⟩` from `GlobalTheory.MemLoc.exists_zeta_eps l`. Establish `he : e.untilt = 1` using `Subtype.ext (by`. Use `hr 0` as an intermediate fact. Rewrite `this` using `[h0, map_one]`.

Conclude with `this)`. Establish `hE : GlobalTheory.MemLoc.IsEps e` using `⟨he, fun hh => h1 (by`. Apply `(algebraMap (Om l) ℂ_[l]).injective` to reduce the goal to its premises. Rewrite using `[← hr 1, map_one]`. Conclude with `congrArg Subtype.val hh)⟩`.

Use `set x : Ainf l := Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e) with hx`. Establish `hxl : x ^ l = Per.tm e`. Rewrite using `[hx, ← map_pow, frobeniusEquiv_symm_pow_p]`. Establish `hφx : WittVector.frobenius x = Per.tm e`. Rewrite using `[hx, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, frobeniusEquiv_symm_pow_p]`.

Establish `hξ : GlobalTheory.MemLoc.xi e * (x - 1) = Per.tm e - 1`. Rewrite using `[GlobalTheory.MemLoc.xi, ← hx, geom_sum_mul, hxl]`. Establish `hsp : Ideal.span {bk.ev bk.E} = Ideal.span {GlobalTheory.MemLoc.xi e}` using `bk.span_ev.trans (GlobalTheory.MemLoc.ker_theta_eq_span_xi hE)`. Take `⟨ω, hω⟩` from `Ideal.span_singleton_eq_span_singleton.1 hsp.symm`. Take `⟨η, hη⟩` from `GlobalTheory.T.exists_ainf_unit_frobenius_eq_mul l ω`.

Use `⟨(x - 1) * η, ?_, e, ω * η, hE, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_sub, map_one, hφx, hη, ← hω, ← hξ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_mul, map_sub, map_one, hφx, hη, Units.val_mul]`. Rewrite using `[mul_comm]`.
-/
theorem exists_isPer : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ τ : Ainf l, bk.IsPer τ := by
  intro l hl K bk
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : e.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps e := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  set x : Ainf l := Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e) with hx
  have hxl : x ^ l = Per.tm e := by
    rw [hx, ← map_pow, frobeniusEquiv_symm_pow_p]
  have hφx : WittVector.frobenius x = Per.tm e := by
    rw [hx, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def,
      frobeniusEquiv_symm_pow_p]
  have hξ : GlobalTheory.MemLoc.xi e * (x - 1) = Per.tm e - 1 := by
    rw [GlobalTheory.MemLoc.xi, ← hx, geom_sum_mul, hxl]
  have hsp : Ideal.span {bk.ev bk.E} = Ideal.span {GlobalTheory.MemLoc.xi e} :=
    bk.span_ev.trans (GlobalTheory.MemLoc.ker_theta_eq_span_xi hE)
  obtain ⟨ω, hω⟩ := Ideal.span_singleton_eq_span_singleton.1 hsp.symm
  obtain ⟨η, hη⟩ := GlobalTheory.T.exists_ainf_unit_frobenius_eq_mul l ω
  refine ⟨(x - 1) * η, ?_, e, ω * η, hE, ?_⟩
  · rw [map_mul, map_sub, map_one, hφx, hη, ← hω, ← hξ]
    ring
  · rw [map_mul, map_sub, map_one, hφx, hη, Units.val_mul]
    rw [mul_comm]
end GlobalTheory.BSP
