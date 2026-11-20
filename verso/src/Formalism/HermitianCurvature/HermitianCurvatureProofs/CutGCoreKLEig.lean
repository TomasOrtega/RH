import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTKLineCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedF

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

namespace KLEigPf

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

/- English proof (translation)
Establish `hQv : ∀ ρ σ v, Qs ρ (Qs σ v) = if ρ = σ then Qs ρ v else 0`. Introduce `ρ σ v`. Establish `h` using `congrArg (fun T : Wq →L[ℂ] Wq => T v) (hQQ ρ σ)`. Simplify using `only [ContinuousLinearMap.comp_apply] at h`. Rewrite using `[h]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hEC : ∀ Y v, E (C Y v) = ∑ σ, x σ Y • E (Qs σ v)`. Introduce `Y v`. Establish `h` using `congrArg (fun T : Wq →L[ℂ] Wp => T v) (hid Y)`. Simplify using `only [ContinuousLinearMap.comp_apply] at h`.

Rewrite using `[← h]`. Simplify using `[map_sum]`. Establish `hEv : ∀ v, E v = ∑ σ, E (Qs σ v)`. Introduce `v`. Establish `h : (∑ σ, Qs σ) v = v` using `by rw [hsum, ContinuousLinearMap.one_apply]`.

Use `conv_lhs => rw [← h]`. Rewrite using `[ContinuousLinearMap.sum_apply, map_sum]`. Prove the components needed by the constructor for the conclusion. Introduce `h Y v`. Establish `hE : ∀ w, E (Qs ρ w) = E w` using `fun w => congrArg (fun T : Wq →L[ℂ] Wp => T w) h`.

Establish `hσ : ∀ σ, E (Qs σ v) = if ρ = σ then E v else 0`. Introduce `σ`. Rewrite using `[← hE (Qs σ v), hQv]`. Use `split_ifs`. Conclude with `hE v`.

Conclude with `map_zero E`. Rewrite using `[hEC]`. Simplify using `[hσ, Finset.sum_ite_eq]`. Introduce `h`. Establish `h0 : ∀ σ, σ ≠ ρ → ∀ v, E (Qs σ v) = 0`.

Introduce `σ hσ v`. Take `⟨Y, hY⟩` from `hsep ρ σ (Ne.symm hσ)`. Establish `h1` using `h Y (Qs σ v)`. Rewrite `h1` using `[hEC]`. Establish `h2 : ∑ τ, x τ Y • E (Qs τ (Qs σ v)) = x σ Y • E (Qs σ v)`.

Simplify using `only [hQv]`. Rewrite using `[Finset.sum_eq_single σ]`. Simplify using the standard rewrite rules. Introduce `τ _ hτ`. Simplify using `[hτ]`.

Simplify using the standard rewrite rules. Rewrite `h1` using `[h2]`. Establish `h3 : (x σ Y - x ρ Y) • E (Qs σ v) = 0` using `by rw [sub_smul, h1, sub_self]`. Conclude with `(smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm hY))`. Use extensionality with `v`.

Rewrite using `[ContinuousLinearMap.comp_apply, hEv v, Finset.sum_eq_single ρ]`. Introduce `σ _ hσ`. Conclude with `h0 σ hσ v`. Simplify using the standard rewrite rules.
-/
theorem alg {ι : Type} [Fintype ι] [DecidableEq ι] (Qs : ι → (Wq →L[ℂ] Wq)) (x : ι → ℂ → ℂ)
    (C : ℂ → (Wq →L[ℂ] Wq)) (E : Wq →L[ℂ] Wp)
    (hQQ : ∀ ρ σ, (Qs ρ).comp (Qs σ) = if ρ = σ then Qs ρ else 0) (hsum : ∑ ρ, Qs ρ = 1)
    (hsep : ∀ ρ σ, ρ ≠ σ → ∃ Y, x ρ Y ≠ x σ Y)
    (hid : ∀ Y, E.comp (∑ σ, x σ Y • Qs σ) = E.comp (C Y)) (ρ : ι) :
    E.comp (Qs ρ) = E ↔ ∀ (Y : ℂ) (v : Wq), E (C Y v) = x ρ Y • E v := by
  have hQv : ∀ ρ σ v, Qs ρ (Qs σ v) = if ρ = σ then Qs ρ v else 0 := by
    intro ρ σ v
    have h := congrArg (fun T : Wq →L[ℂ] Wq => T v) (hQQ ρ σ)
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [h]
    split_ifs <;> simp
  have hEC : ∀ Y v, E (C Y v) = ∑ σ, x σ Y • E (Qs σ v) := by
    intro Y v
    have h := congrArg (fun T : Wq →L[ℂ] Wp => T v) (hid Y)
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [← h]
    simp [map_sum]
  have hEv : ∀ v, E v = ∑ σ, E (Qs σ v) := by
    intro v
    have h : (∑ σ, Qs σ) v = v := by rw [hsum, ContinuousLinearMap.one_apply]
    conv_lhs => rw [← h]
    rw [ContinuousLinearMap.sum_apply, map_sum]
  constructor
  · intro h Y v
    have hE : ∀ w, E (Qs ρ w) = E w := fun w => congrArg (fun T : Wq →L[ℂ] Wp => T w) h
    have hσ : ∀ σ, E (Qs σ v) = if ρ = σ then E v else 0 := by
      intro σ
      rw [← hE (Qs σ v), hQv]
      split_ifs
      · exact hE v
      · exact map_zero E
    rw [hEC]
    simp [hσ, Finset.sum_ite_eq]
  · intro h
    have h0 : ∀ σ, σ ≠ ρ → ∀ v, E (Qs σ v) = 0 := by
      intro σ hσ v
      obtain ⟨Y, hY⟩ := hsep ρ σ (Ne.symm hσ)
      have h1 := h Y (Qs σ v)
      rw [hEC] at h1
      have h2 : ∑ τ, x τ Y • E (Qs τ (Qs σ v)) = x σ Y • E (Qs σ v) := by
        simp only [hQv]
        rw [Finset.sum_eq_single σ]
        · simp
        · intro τ _ hτ
          simp [hτ]
        · simp
      rw [h2] at h1
      have h3 : (x σ Y - x ρ Y) • E (Qs σ v) = 0 := by rw [sub_smul, h1, sub_self]
      exact (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm hY))
    ext v
    rw [ContinuousLinearMap.comp_apply, hEv v, Finset.sum_eq_single ρ]
    · intro σ _ hσ
      exact h0 σ hσ v
    · simp

end KLEigPf

open KLEigPf in
/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P Bs X d hH Qρ hK ζ hζ Fr hFr ρ E hE`. Take `⟨hpl, hk, hcs, hL, -, -, hQ⟩` from `id hH`. Take `⟨hOK, hz, hz', hTz, hTz', -, -⟩` from `id hpl`. Establish `hT : 0 < Tz P.k P.r Bs.z` using `by rw [hTz]; exact hOK.T_pos`. Establish `hT' : 0 < Tz P.k P.r Bs.z'` using `by rw [hTz']; exact hOK.T'_pos`.

Establish `hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ`. Rewrite using `[hTz, hTz']`. Conclude with `hζ`. Use `set c0 : Fin P.r → ℂ := fun _ => 1 with hc0def`. Establish `hq : ((c0, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z'` using `⟨fun _ => one_ne_zero, hζ'⟩`.

Use `set φ : (Fin P.r → ℂ) × ℂ → (Wq →L[ℂ] Wp) := (NF.QR P.k P.r Bs.z Bs.z').indicator (fun _ => E) with hφdef`. Establish `hφ : φ ∈ NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π'`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `contDiffOn_const.congr (fun q hq' => Set.indicator_of_mem hq' _)`. Introduce `q hq'`.

Rewrite using `[hφdef, Set.indicator_of_mem hq']`. Establish `hst` using `hcs.2 q.2 ζ hq'.2 hζ'`. Introduce `p hp`. Conclude with `hE p (hst ▸ hp)`. Introduce `q hq'`.

Conclude with `Set.indicator_of_notMem hq' _`. Establish `hbase : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π'` using `⟨by omega, hz, hz', hT, hT', hcs.1, Bs.π_rep, Bs.π'_rep, Bs.π_cont, Bs.π'_cont⟩`. Take `⟨Φ, hΦ, hΦr⟩` from `Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hbase φ hφ`. Use `set g := NF.muZ P.k P.r Bs.μsec ζ with hgdef`. Establish `hval : Φ c0 g = E`.

Establish `h1` using `congrFun hΦr (c0, ζ)`. Simplify using `only [NF.radR, Set.indicator_of_mem hq, hφdef] at h1`. Conclude with `h1`. Establish `hx : (c0, g) ∈ Q.DomR P.k P.r Bs.z Bs.z'` using `Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hcs.1 hq`. Use `set Φ' : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := ⟨Φ, hΦ⟩ with hΦ'def`.

Set `qq : MA.Qp P.r P.TT` to `⟨(c0, ζ), ⟨fun _ => one_ne_zero, hζ⟩⟩`. Establish `hx1 : ∀ Y : ℂ, (d.x Y).1 = X.fn 5 * X.t Y 1 1`. Introduce `Y`. Establish `h : d.x Y = d.L.GGi * X.QQ Y 1 1`. Rewrite using `[hQ]`.

Simplify using `only [Q.NFData.QQ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val_zero]`. Rewrite using `[← mul_assoc, d.L.GGi_GG, one_mul]`. Use `show Formalism.FourierDecayAlt.P5.Kfp.fstAlg _ (d.x Y) = _`. Rewrite using `[h, hL.2.2.2.2.2.2.2.2.2.2.2.1]`. Both sides reduce to the same expression.

Set `C : ℂ → (Wq →L[ℂ] Wq)` to `fun Y => LinearMap.toContinuousLinearMap (qdet (Qr.EB Bs.π' Fr) (Y + ((P.k : ℂ) - 2) / 2))`. Establish `hid : ∀ Y, E.comp (∑ σ, M.xC P σ Y • Qρ σ) = E.comp (C Y)`. Introduce `Y`. Use extensionality with `v`. Establish `hk1` using `hK.2.2.2 (fun σ => M.xC P σ Y) Φ' qq`.

Establish `hk2` using `congrArg (fun L : Wq →L[ℂ] Wp => L v) hk1`. Establish `hact` using `Formalism.FourierDecayAlt.P5.Kfp.diagonal_transfer_action X hz hz' Bs.π'_rep Bs.π'_cont hx Fr hFr Y Φ' v`. Establish `hκx : (d.κ fun σ => M.xC P σ Y) = d.x Y` using `rfl`. Rewrite `hk2` using `[hκx, hx1 Y]`. Express the relevant statement in the definitionally equal form `(((X.fn 5 * X.t Y 1 1) Φ' : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 g v = (Φ c0 g) ((∑ σ, M.xC P σ Y • Qρ σ) v) at hk2`.

Rewrite `hk2` using `[hact, hval]`. Rewrite using `[ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← hk2]`. Use `show (Φ c0 g) _ = _`. Rewrite using `[hval]`. Both sides reduce to the same expression.

Take `⟨Y₀, hY₀⟩` from `Formalism.FourierDecayAlt.P5.Kfp.sep_real hOK`. Establish `hsep : ∀ ρ σ : M.Ty P, ρ ≠ σ → ∃ Y, M.xC P ρ Y ≠ M.xC P σ Y` using `fun ρ σ h => ⟨(Y₀ : ℂ), fun he => h (hY₀ he)⟩`. Conclude with `alg Qρ (fun σ Y => M.xC P σ Y) C E hK.1 hK.2.1 hsep hid ρ`.
-/
theorem lie_eigenvalue_holds : KLEig := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH Qρ hK ζ hζ Fr hFr ρ E hE
  obtain ⟨hpl, hk, hcs, hL, -, -, hQ⟩ := id hH
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hT : 0 < Tz P.k P.r Bs.z := by rw [hTz]; exact hOK.T_pos
  have hT' : 0 < Tz P.k P.r Bs.z' := by rw [hTz']; exact hOK.T'_pos
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζ
  set c0 : Fin P.r → ℂ := fun _ => 1 with hc0def
  have hq : ((c0, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨fun _ => one_ne_zero, hζ'⟩
  set φ : (Fin P.r → ℂ) × ℂ → (Wq →L[ℂ] Wp) := (NF.QR P.k P.r Bs.z Bs.z').indicator (fun _ => E) with hφdef
  have hφ : φ ∈ NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    refine ⟨?_, ?_, ?_⟩
    · exact contDiffOn_const.congr (fun q hq' => Set.indicator_of_mem hq' _)
    · intro q hq'
      rw [hφdef, Set.indicator_of_mem hq']
      have hst := hcs.2 q.2 ζ hq'.2 hζ'
      intro p hp
      exact hE p (hst ▸ hp)
    · intro q hq'
      exact Set.indicator_of_notMem hq' _
  have hbase : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' :=
    ⟨by omega, hz, hz', hT, hT', hcs.1, Bs.π_rep, Bs.π'_rep, Bs.π_cont, Bs.π'_cont⟩
  obtain ⟨Φ, hΦ, hΦr⟩ := Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hbase φ hφ
  set g := NF.muZ P.k P.r Bs.μsec ζ with hgdef
  have hval : Φ c0 g = E := by
    have h1 := congrFun hΦr (c0, ζ)
    simp only [NF.radR, Set.indicator_of_mem hq, hφdef] at h1
    exact h1
  have hx : (c0, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hcs.1 hq
  set Φ' : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := ⟨Φ, hΦ⟩ with hΦ'def
  let qq : MA.Qp P.r P.TT := ⟨(c0, ζ), ⟨fun _ => one_ne_zero, hζ⟩⟩
  have hx1 : ∀ Y : ℂ, (d.x Y).1 = X.fn 5 * X.t Y 1 1 := by
    intro Y
    have h : d.x Y = d.L.GGi * X.QQ Y 1 1 := by
      rw [hQ]
      simp only [Q.NFData.QQ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val_zero]
      rw [← mul_assoc, d.L.GGi_GG, one_mul]
    show Formalism.FourierDecayAlt.P5.Kfp.fstAlg _ (d.x Y) = _
    rw [h, hL.2.2.2.2.2.2.2.2.2.2.2.1]
    rfl
  let C : ℂ → (Wq →L[ℂ] Wq) := fun Y =>
    LinearMap.toContinuousLinearMap (qdet (Qr.EB Bs.π' Fr) (Y + ((P.k : ℂ) - 2) / 2))
  have hid : ∀ Y, E.comp (∑ σ, M.xC P σ Y • Qρ σ) = E.comp (C Y) := by
    intro Y
    ext v
    have hk1 := hK.2.2.2 (fun σ => M.xC P σ Y) Φ' qq
    have hk2 := congrArg (fun L : Wq →L[ℂ] Wp => L v) hk1
    have hact := Formalism.FourierDecayAlt.P5.Kfp.diagonal_transfer_action X hz hz' Bs.π'_rep Bs.π'_cont hx Fr hFr Y Φ' v
    have hκx : (d.κ fun σ => M.xC P σ Y) = d.x Y := rfl
    rw [hκx, hx1 Y] at hk2
    change (((X.fn 5 * X.t Y 1 1) Φ' : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 g v =
      (Φ c0 g) ((∑ σ, M.xC P σ Y • Qρ σ) v) at hk2
    rw [hact, hval] at hk2
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← hk2]
    show (Φ c0 g) _ = _
    rw [hval]
    rfl
  obtain ⟨Y₀, hY₀⟩ := Formalism.FourierDecayAlt.P5.Kfp.sep_real hOK
  have hsep : ∀ ρ σ : M.Ty P, ρ ≠ σ → ∃ Y, M.xC P ρ Y ≠ M.xC P σ Y :=
    fun ρ σ h => ⟨(Y₀ : ℂ), fun he => h (hY₀ he)⟩
  classical
  exact alg Qρ (fun σ Y => M.xC P σ Y) C E hK.1 hK.2.1 hsep hid ρ

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
