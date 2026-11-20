import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselThetaIntegrandIsUnfoldingTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiActionUnipotentLawsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselBasePointIsUnfoldingBasePointSpecStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittExtensionHomMulEmbeddedAnisotropic
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SymplecticAdelicFormBiadditiveAlternatingRationa
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
open GlobalTheory.Unf.FB

noncomputable section

open GlobalTheory.ThLaws in

/- English proof (translation)
Introduce `D ψ hψ σ J B y hy x₀ hx₀`. Take `⟨hcont, -, hleft, hcen, -, -⟩` from `GlobalTheory.T.jacobiActionUnipotent_laws D ψ hψ σ J B y hy`. Use `beta_reduce at hcen hleft`. Take `⟨x₁, hx₁, -, -, hlast, hq⟩` from `GlobalTheory.T.besselBasePoint_isUnfoldingBasePoint_spec D σ B`. Establish `e : x₁ = x₀` using `rat_injective (hx₁.trans hx₀.symm)`.

Use `⟨hcont.comp continuous_subtype_val, fun γ hγQ hγN n hn => hleft γ hγN hγQ n hn, fun c n hn => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hcen c n hn, hx₀, hq]`. Introduce `j a ha1 ha0 hg`. Establish `hl : a (Fin.last σ) = 0` using `hlast a (by rw [e]; exact hg)`. Establish `hj : j.1 < σ`.

Assume the negation of the conclusion as `hc`. Establish `: j = Fin.last σ` using `Fin.ext (by have := j.2; simp only [Fin.val_last]; omega)`. Rewrite `ha1` using `[this, hl]`. Conclude with `zero_ne_one ha1`. Set `j' : Fin (σ + 1)` to `⟨j.1 + 1, by omega⟩`.

Establish `hjj : j < j'` using `by rw [Fin.lt_def]; simp [j']`. Take `⟨t, ht⟩` from `exists_psiE_ne_one hψ`. Set `A : Fin (σ + 1) → AE D` to `GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a`. Set `Bv : Fin (σ + 1) → AE D` to `fun k => if k = j' then cA D t else 0`. Establish `hB0 : ∀ k, k ≠ j' → Bv k = 0` using `fun k hk => if_neg hk`.

Establish `hA0 : ∀ i, j < i → A i = 0` using `fun i hi => by show incA D (a i) = 0`. Rewrite using `[ha0 i hi, map_zero]`. Establish `hN : ∀ i k, ¬(i ≤ j ∧ k = j') → A i * cA D (Bv k) = 0`. Introduce `i k hik`. Distinguish the cases in `hk : k = j'`.

Rewrite using `[hA0 i (not_le.1 fun hi => hik ⟨hi, hk⟩), zero_mul]`. Rewrite using `[hB0 k hk, map_zero, mul_zero]`. Establish `hAB : (fun k => cA D (Bv k)) ⬝ᵥ A = 0`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`.

Conclude with `hN k k fun h => absurd (h.2 ▸ h.1) (not_le.2 hjj)`. Establish `hupper : tvGL A Bv hAB ∈ upperUni (σ + 1) (AE D)` using `fun i k => by`. Use `⟨fun hki => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[tvGL_val, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hki), tvN_apply, hN i k fun h => absurd (h.2 ▸ hki) (not_lt.2 (le_of_lt (lt_of_le_of_lt h.1 hjj))), zero_add]`. Rewrite using `[tvGL_val, Matrix.add_apply, Matrix.one_apply_eq, tvN_apply, hN i i fun h => absurd (h.2 ▸ h.1) (not_le.2 hjj), add_zero]`.

Establish `hUX : tvGL A Bv hAB ∈ UX D (σ + 1)` using `mem_UX.2 hupper`. Establish `hu : J.d.levi (tvGL A Bv hAB) ∈ flagN J.d` using `J.d.levi_mem_NFlag hupper`. Establish `hup : upSum (tvN A Bv) = t`. Unfold `upSum`. Rewrite using `[Finset.sum_eq_single j, Finset.sum_eq_single j']`.

Rewrite using `[if_pos (by simp [j']), tvN_apply, show Bv j' = cA D t from if_pos rfl, cA_cA'] show incA D (a j) * t = t`. Rewrite using `[ha1, map_one, one_mul]`. Introduce `k _ hk`. Rewrite using `[tvN_apply, hB0 k hk, map_zero, mul_zero, ite_self]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Introduce `i _ hi`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k = j'`. Rewrite using `[if_neg]`.

Introduce `h`. Apply `hi` to reduce the goal to its premises. Rewrite `h` using `[hk]`. Conclude with `Fin.ext (by simp [j'] at h; omega)`. Rewrite using `[tvN_apply, hB0 k hk, map_zero, mul_zero, ite_self]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Use `⟨J.d.jY *ᵥ Bv, J.d.levi (tvGL A Bv hAB), star (psiE ψ t), ?_, levi_isTransv J.d A Bv hAB, Subgroup.mem_inf.2 ⟨hu, Subgroup.mem_iInf.2 fun i => ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form J.W (J.d.jX *ᵥ A) (J.d.jY *ᵥ Bv) = 0`. Rewrite using `[form_mulVec, ← J.d.pX_eq, Matrix.mulVec_mulVec, J.d.pX_jX, Matrix.one_mulVec, hAB]`.

Rewrite using `[mem_fixer]`. Establish `hcol : ∀ m, (tvGL A Bv hAB).1 m i.1 = (1 : Mx D (σ + 1) (σ + 1)) m i.1` using `fun m => by`. Rewrite using `[tvGL_val, Matrix.add_apply, tvN_apply, hN m i.1 fun h => absurd (h.2 ▸ i.2) (not_le.2 hjj), add_zero]`. Use extensionality with `k l`. Establish `h1` using `congrFun (congrFun (J.d.levi_jX (tvGL A Bv hAB)) k) i.1`.

Simplify using `only [Matrix.mul_apply, Matrix.submatrix_apply, id] at h1 ⊢`. Rewrite using `[h1]`. Simplify using `only [hcol, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Introduce `h1`. Apply `ht` to reduce the goal to its premises.

Rewrite using `[← star_star (psiE ψ t), h1, star_one]`. Introduce `n hn n' hn'`. Establish `hx : ∀ u ∈ UX D (σ + 1), zEll B.L (σ + 1) B.ζ ⬝ u.1 = zEll B.L (σ + 1) B.ζ` using `fun u hu => zEll_mul B.L B.ζ hu`. Establish `hJu : jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (J.d.levi (tvGL A Bv hAB)) = id`. Use `jacS_levi_mul ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (hx _ hUX) 1` as an intermediate fact.

Rewrite `this` using `[mul_one, jacS_one]`. Then use the resulting hypothesis. Establish `hpu : psiFlag ψ J.d (J.d.levi (tvGL A Bv hAB)) = psiE ψ t`. Rewrite using `[psiFlag, blockX_levi, tvGL_val, upSum_add, upSum_one, zero_add, hup]`. Use `beta_reduce`. Rewrite using `[GlobalTheory.JacHom.jacS_mul J.d hx ψ (mul_mem hn hu) hn', GlobalTheory.JacHom.jacS_mul J.d hx ψ hn hu, hJu, GlobalTheory.JacHom.jacS_mul J.d hx ψ hn hn', psiFlag_mul J.d ψ (mul_mem hn hu) hn', psiFlag_mul J.d ψ hn hu, psiFlag_mul J.d ψ hn hn', hpu]`.

Simplify using `only [id, star_mul']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.th_isTh_lev : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (y : WO J.W₀ B.L → ℂ), GlobalTheory.Unf.FB.Quasi ψ J.W₀ B.L y → ∀ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E, (rat x₀ : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ) → IsTh ψ J.d B.V x₀ (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) := by
  intro D ψ hψ σ J B y hy x₀ hx₀
  obtain ⟨hcont, -, hleft, hcen, -, -⟩ := GlobalTheory.T.jacobiActionUnipotent_laws D ψ hψ σ J B y hy
  beta_reduce at hcen hleft
  obtain ⟨x₁, hx₁, -, -, hlast, hq⟩ := GlobalTheory.T.besselBasePoint_isUnfoldingBasePoint_spec D σ B
  have e : x₁ = x₀ := rat_injective (hx₁.trans hx₀.symm)
  refine ⟨hcont.comp continuous_subtype_val, fun γ hγQ hγN n hn => hleft γ hγN hγQ n hn, fun c n hn => ?_, ?_⟩
  · rw [hcen c n hn, hx₀, hq]
  intro j a ha1 ha0 hg
  have hl : a (Fin.last σ) = 0 := hlast a (by rw [e]; exact hg)
  have hj : j.1 < σ := by
    by_contra hc
    have : j = Fin.last σ := Fin.ext (by have := j.2; simp only [Fin.val_last]; omega)
    rw [this, hl] at ha1
    exact zero_ne_one ha1
  let j' : Fin (σ + 1) := ⟨j.1 + 1, by omega⟩
  have hjj : j < j' := by rw [Fin.lt_def]; simp [j']
  obtain ⟨t, ht⟩ := exists_psiE_ne_one hψ
  let A : Fin (σ + 1) → AE D := GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a
  let Bv : Fin (σ + 1) → AE D := fun k => if k = j' then cA D t else 0
  have hB0 : ∀ k, k ≠ j' → Bv k = 0 := fun k hk => if_neg hk
  have hA0 : ∀ i, j < i → A i = 0 := fun i hi => by
    show incA D (a i) = 0
    rw [ha0 i hi, map_zero]
  have hN : ∀ i k, ¬(i ≤ j ∧ k = j') → A i * cA D (Bv k) = 0 := by
    intro i k hik
    by_cases hk : k = j'
    · rw [hA0 i (not_le.1 fun hi => hik ⟨hi, hk⟩), zero_mul]
    · rw [hB0 k hk, map_zero, mul_zero]
  have hAB : (fun k => cA D (Bv k)) ⬝ᵥ A = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [mul_comm]
    exact hN k k fun h => absurd (h.2 ▸ h.1) (not_le.2 hjj)
  have hupper : tvGL A Bv hAB ∈ upperUni (σ + 1) (AE D) := fun i k => by
    refine ⟨fun hki => ?_, ?_⟩
    · rw [tvGL_val, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hki), tvN_apply,
        hN i k fun h => absurd (h.2 ▸ hki) (not_lt.2 (le_of_lt (lt_of_le_of_lt h.1 hjj))), zero_add]
    · rw [tvGL_val, Matrix.add_apply, Matrix.one_apply_eq, tvN_apply,
        hN i i fun h => absurd (h.2 ▸ h.1) (not_le.2 hjj), add_zero]
  have hUX : tvGL A Bv hAB ∈ UX D (σ + 1) := mem_UX.2 hupper
  have hu : J.d.levi (tvGL A Bv hAB) ∈ flagN J.d := J.d.levi_mem_NFlag hupper
  have hup : upSum (tvN A Bv) = t := by
    unfold upSum
    rw [Finset.sum_eq_single j, Finset.sum_eq_single j']
    · rw [if_pos (by simp [j']), tvN_apply, show Bv j' = cA D t from if_pos rfl, cA_cA']
      show incA D (a j) * t = t
      rw [ha1, map_one, one_mul]
    · intro k _ hk
      rw [tvN_apply, hB0 k hk, map_zero, mul_zero, ite_self]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro i _ hi
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k = j'
      · rw [if_neg]
        intro h
        apply hi
        rw [hk] at h
        exact Fin.ext (by simp [j'] at h; omega)
      · rw [tvN_apply, hB0 k hk, map_zero, mul_zero, ite_self]
    · intro h; exact absurd (Finset.mem_univ _) h
  refine ⟨J.d.jY *ᵥ Bv, J.d.levi (tvGL A Bv hAB), star (psiE ψ t), ?_, levi_isTransv J.d A Bv hAB,
    Subgroup.mem_inf.2 ⟨hu, Subgroup.mem_iInf.2 fun i => ?_⟩, ?_, ?_⟩
  · show GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form J.W (J.d.jX *ᵥ A) (J.d.jY *ᵥ Bv) = 0
    rw [form_mulVec, ← J.d.pX_eq, Matrix.mulVec_mulVec, J.d.pX_jX, Matrix.one_mulVec, hAB]
  · rw [mem_fixer]
    have hcol : ∀ m, (tvGL A Bv hAB).1 m i.1 = (1 : Mx D (σ + 1) (σ + 1)) m i.1 := fun m => by
      rw [tvGL_val, Matrix.add_apply, tvN_apply,
        hN m i.1 fun h => absurd (h.2 ▸ i.2) (not_le.2 hjj), add_zero]
    ext k l
    have h1 := congrFun (congrFun (J.d.levi_jX (tvGL A Bv hAB)) k) i.1
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id] at h1 ⊢
    rw [h1]
    simp only [hcol, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · intro h1
    apply ht
    rw [← star_star (psiE ψ t), h1, star_one]
  · intro n hn n' hn'
    have hx : ∀ u ∈ UX D (σ + 1), zEll B.L (σ + 1) B.ζ ⬝ u.1 = zEll B.L (σ + 1) B.ζ := fun u hu => zEll_mul B.L B.ζ hu
    have hJu : jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (J.d.levi (tvGL A Bv hAB)) = id := by
      have := jacS_levi_mul ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (hx _ hUX) 1
      rwa [mul_one, jacS_one] at this
    have hpu : psiFlag ψ J.d (J.d.levi (tvGL A Bv hAB)) = psiE ψ t := by
      rw [psiFlag, blockX_levi, tvGL_val, upSum_add, upSum_one, zero_add, hup]
    beta_reduce
    rw [GlobalTheory.JacHom.jacS_mul J.d hx ψ (mul_mem hn hu) hn', GlobalTheory.JacHom.jacS_mul J.d hx ψ hn hu, hJu,
      GlobalTheory.JacHom.jacS_mul J.d hx ψ hn hn', psiFlag_mul J.d ψ (mul_mem hn hu) hn', psiFlag_mul J.d ψ hn hu,
      psiFlag_mul J.d ψ hn hn', hpu]
    simp only [id, star_mul']
    ring
