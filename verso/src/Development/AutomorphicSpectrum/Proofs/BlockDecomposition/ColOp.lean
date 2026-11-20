import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns

noncomputable section

open MeasureTheory
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KernelColumns

/- English proof (translation)
Introduce `hB hC hL hM X ι _ ψ hψ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `y j`. Establish `hm : MemLp (fun x => ker X.Γ ψ x y) 2 X.ν` using `(hL X ψ hψ).1 y`. Use `⟨WithLp.toLp 2 (Pi.single j (hm.toLp _)), ?_, ?_⟩` and prove the remaining obligations.

Establish `e : (WithLp.toLp 2 (Pi.single j (hm.toLp _)) : X.Hs ι) j = hm.toLp _`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `hm.coeFn_toLp`. Introduce `l hl ext1`.

Simplify using `[Pi.single_eq_of_ne hl]`. Introduce `Φ T hΦ hT y j u hu`. Establish `key : ∀ i, (T u i : X.G → ℂ) =ᵐ[X.ν] fun x => ker X.Γ (cv X.μ (Φ i j) ψ) x y`. Introduce `i`. Use `filter_upwards [hT u i] with x hx`.

Rewrite using `[hx, Finset.sum_eq_single j]`. Rewrite using `[← hM X (Φ i j) ψ (hΦ i j) hψ x y]`. Apply `integral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hu.1] with z hz`. Rewrite using `[hz]`.

Introduce `l _ hl`. Establish `h0 : (u l : X.G → ℂ) =ᵐ[X.ν] 0`. Rewrite using `[hu.2 l hl]`. Conclude with `Lp.coeFn_zero _ _ _`. Establish `: (fun z => ker X.Γ (Φ i l) x z * (u l : X.G → ℂ) z) =ᵐ[X.ν] fun _ => 0` using `by filter_upwards [h0] with z hz`.

Rewrite using `[hz]`. Simplify using the standard rewrite rules. Rewrite using `[integral_congr_ae this]`. Simplify using the standard rewrite rules. Introduce `h`.

Conclude with `absurd (Finset.mem_univ j) h`. Use `⟨key, ?_⟩` and prove the remaining obligations. Introduce `x i v hv`. Establish `hc` using `hC X (Φ i j) ψ (hΦ i j) hψ`. Establish `ha` using `(hB X ψ hψ).2.2.2.1`.

Establish `hadj` using `(hB X ψ hψ).2.2.2.2.1`. Rewrite using `[PiLp.inner_apply, Finset.sum_eq_single i]`. Rewrite using `[L2.inner_def, ← hM X (adj ψ) (cv X.μ (Φ i j) ψ) ha hc.1 x y]`. Apply `integral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hv.1, key i] with z hz1 hz2`.

Rewrite using `[hz1, hz2, RCLike.inner_apply, hadj x z, mul_comm]`. Introduce `l _ hl`. Rewrite using `[hv.2 l hl]`. Simplify using the standard rewrite rules. Introduce `h`.

Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem colOp : KerBasic → CvTest → KernelL2RowsColumns → KerMul → ColOp := by
  intro hB hC hL hM X ι _ ψ hψ
  classical
  refine ⟨?_, ?_⟩
  · intro y j
    have hm : MemLp (fun x => ker X.Γ ψ x y) 2 X.ν := (hL X ψ hψ).1 y
    refine ⟨WithLp.toLp 2 (Pi.single j (hm.toLp _)), ?_, ?_⟩
    · have e : (WithLp.toLp 2 (Pi.single j (hm.toLp _)) : X.Hs ι) j = hm.toLp _ := by
        simp
      rw [e]
      exact hm.coeFn_toLp
    · intro l hl
      ext1
      simp [Pi.single_eq_of_ne hl]
  · intro Φ T hΦ hT y j u hu
    have key : ∀ i, (T u i : X.G → ℂ) =ᵐ[X.ν] fun x => ker X.Γ (cv X.μ (Φ i j) ψ) x y := by
      intro i
      filter_upwards [hT u i] with x hx
      rw [hx, Finset.sum_eq_single j]
      · rw [← hM X (Φ i j) ψ (hΦ i j) hψ x y]
        apply integral_congr_ae
        filter_upwards [hu.1] with z hz
        rw [hz]
      · intro l _ hl
        have h0 : (u l : X.G → ℂ) =ᵐ[X.ν] 0 := by
          rw [hu.2 l hl]
          exact Lp.coeFn_zero _ _ _
        have : (fun z => ker X.Γ (Φ i l) x z * (u l : X.G → ℂ) z) =ᵐ[X.ν] fun _ => 0 := by
          filter_upwards [h0] with z hz
          rw [hz]
          simp
        rw [integral_congr_ae this]
        simp
      · intro h
        exact absurd (Finset.mem_univ j) h
    refine ⟨key, ?_⟩
    intro x i v hv
    have hc := hC X (Φ i j) ψ (hΦ i j) hψ
    have ha := (hB X ψ hψ).2.2.2.1
    have hadj := (hB X ψ hψ).2.2.2.2.1
    rw [PiLp.inner_apply, Finset.sum_eq_single i]
    · rw [L2.inner_def, ← hM X (adj ψ) (cv X.μ (Φ i j) ψ) ha hc.1 x y]
      apply integral_congr_ae
      filter_upwards [hv.1, key i] with z hz1 hz2
      rw [hz1, hz2, RCLike.inner_apply, hadj x z, mul_comm]
    · intro l _ hl
      rw [hv.2 l hl]
      simp
    · intro h
      exact absurd (Finset.mem_univ i) h

end GlobalTheory.CompanionTheory.KernelColumns

end
