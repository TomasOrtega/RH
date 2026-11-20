import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASectionCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSTr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnTrSmooth

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSTr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P Bs hpl e he U`. Set `g : (Fin P.r → ℂ) × ℂ → (Wq →L[ℂ] Wp)` to `fun x => (((Real.sqrt (MA.wq P.k x P.TT))⁻¹ : ℝ) : ℂ) • ∑ ρ, MA.ext (U ρ : MA.Qp P.r P.TT → ℂ) x • e ρ x.2`. Set `φ` to `(NF.QR P.k P.r Bs.z Bs.z').indicator g`. Establish `hQR : NF.QR P.k P.r Bs.z Bs.z' = MA.Qset P.r P.TT` using `Set.ext (qr_iff P Bs hpl)`. Establish `hg : ContDiffOn ℝ ∞ g (MA.Qset P.r P.TT)`.

Establish `hw : ContDiffOn ℝ ∞ (fun x : MA.E P.r => (((Real.sqrt (MA.wq P.k x P.TT))⁻¹ : ℝ) : ℂ)) (MA.Qset P.r P.TT)`. Use `Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_ofReal ?_` and prove the remaining obligations. Use `ContDiffOn.inv ?_ fun x hx => (Real.sqrt_pos.2 (Formalism.FourierDecayAlt.P.CutMP.En.wq_pos hx)).ne'` and prove the remaining obligations. Conclude with `(Formalism.FourierDecayAlt.P.CutMP.En.wq_contDiff P.k P.r P.TT).contDiffOn.sqrt fun x hx => (Formalism.FourierDecayAlt.P.CutMP.En.wq_pos hx).ne'`. Use `hw.smul (ContDiffOn.sum fun ρ _ => ?_)` and prove the remaining obligations.

Establish `hF : ContDiffOn ℝ ∞ (MA.ext (U ρ : MA.Qp P.r P.TT → ℂ)) (MA.Qset P.r P.TT)` using `(U ρ).2`. Establish `he' : ContDiffOn ℝ ∞ (fun x : MA.E P.r => e ρ x.2) (MA.Qset P.r P.TT)` using `(he.1 ρ).comp contDiff_snd.contDiffOn fun x hx => hx.2`. Conclude with `hF.smul he'`. Establish `hφ : φ ∈ NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π'`. Use `⟨?_, fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations.

Rewrite using `[hQR]`. Conclude with `hg.congr fun x hx => by simp only [φ, hQR, Set.indicator_of_mem hx]`. Simplify using `only [φ, Set.indicator_of_mem hx, g]`. Establish `hx' : P.TT < Complex.normSq x.2` using `((qr_iff P Bs hpl x).1 hx).2`. Establish `h1` using `fib_sum_smul P Bs x.2 (fun ρ => MA.ext (U ρ : MA.Qp P.r P.TT → ℂ) x) (fun ρ => e ρ x.2) fun ρ => (he.2 x.2 hx').1 ρ`.

Distinguish the cases in `hne : Nonempty (M.Ty P)`. Take `⟨ρ0⟩` from `hne`. Introduce `p hp`. Establish `h3` using `fib_sum_smul P Bs x.2 (fun ρ => if ρ = ρ0 then (((Real.sqrt (MA.wq P.k x P.TT))⁻¹ : ℝ) : ℂ) else 0) (fun _ => ∑ ρ, MA.ext (U ρ : MA.Qp P.r P.TT → ℂ) x • e ρ x.2) (fun _ => h1) p hp`. Simplify using `only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h3`.

Conclude with `h3`. Establish `: ∑ ρ, MA.ext (U ρ : MA.Qp P.r P.TT → ℂ) x • e ρ x.2 = 0`. Rewrite using `[Finset.univ_eq_empty_iff.2 (not_nonempty_iff.1 hne)]`. Simplify using the standard rewrite rules. Rewrite using `[this, smul_zero]`.

Introduce `p hp`. Use extensionality with `v`. Simplify using the standard rewrite rules. Simplify using `[φ, Set.indicator_of_notMem hx]`. Take `⟨Φ, hΦ, hrad⟩` from `Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' (radBase P Bs hpl) φ hφ`.

Use `⟨Φ, hΦ, fun q => ?_⟩` and prove the remaining obligations. Establish `hq : q.1 ∈ NF.QR P.k P.r Bs.z Bs.z'` using `(qr_iff P Bs hpl q.1).2 q.2`. Establish `h` using `congrFun hrad q.1`. Simplify using `only [NF.radR, Set.indicator_of_mem hq, φ] at h`. Rewrite using `[h]`.

Simplify using `only [g]`. Use `congr 1`. Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Use `congr 1`. Simplify using `[MA.ext, q.2]`.
-/
theorem radial_section_holds : SARadSec := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl e he U
  classical
  let g : (Fin P.r → ℂ) × ℂ → (Wq →L[ℂ] Wp) := fun x =>
    (((Real.sqrt (MA.wq P.k x P.TT))⁻¹ : ℝ) : ℂ) • ∑ ρ, MA.ext (U ρ : MA.Qp P.r P.TT → ℂ) x • e ρ x.2
  let φ := (NF.QR P.k P.r Bs.z Bs.z').indicator g
  have hQR : NF.QR P.k P.r Bs.z Bs.z' = MA.Qset P.r P.TT := Set.ext (qr_iff P Bs hpl)
  have hg : ContDiffOn ℝ ∞ g (MA.Qset P.r P.TT) := by
    have hw : ContDiffOn ℝ ∞ (fun x : MA.E P.r => (((Real.sqrt (MA.wq P.k x P.TT))⁻¹ : ℝ) : ℂ))
        (MA.Qset P.r P.TT) := by
      refine Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_ofReal ?_
      refine ContDiffOn.inv ?_ fun x hx => (Real.sqrt_pos.2 (Formalism.FourierDecayAlt.P.CutMP.En.wq_pos hx)).ne'
      exact (Formalism.FourierDecayAlt.P.CutMP.En.wq_contDiff P.k P.r P.TT).contDiffOn.sqrt fun x hx =>
        (Formalism.FourierDecayAlt.P.CutMP.En.wq_pos hx).ne'
    refine hw.smul (ContDiffOn.sum fun ρ _ => ?_)
    have hF : ContDiffOn ℝ ∞ (MA.ext (U ρ : MA.Qp P.r P.TT → ℂ)) (MA.Qset P.r P.TT) := (U ρ).2
    have he' : ContDiffOn ℝ ∞ (fun x : MA.E P.r => e ρ x.2) (MA.Qset P.r P.TT) :=
      (he.1 ρ).comp contDiff_snd.contDiffOn fun x hx => hx.2
    exact hF.smul he'
  have hφ : φ ∈ NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    refine ⟨?_, fun x hx => ?_, fun x hx => ?_⟩
    · rw [hQR]
      exact hg.congr fun x hx => by simp only [φ, hQR, Set.indicator_of_mem hx]
    · simp only [φ, Set.indicator_of_mem hx, g]
      have hx' : P.TT < Complex.normSq x.2 := ((qr_iff P Bs hpl x).1 hx).2
      have h1 := fib_sum_smul P Bs x.2 (fun ρ => MA.ext (U ρ : MA.Qp P.r P.TT → ℂ) x) (fun ρ => e ρ x.2) fun ρ => (he.2 x.2 hx').1 ρ
      by_cases hne : Nonempty (M.Ty P)
      · obtain ⟨ρ0⟩ := hne
        intro p hp
        have h3 := fib_sum_smul P Bs x.2 (fun ρ => if ρ = ρ0 then (((Real.sqrt (MA.wq P.k x P.TT))⁻¹ : ℝ) : ℂ) else 0)
          (fun _ => ∑ ρ, MA.ext (U ρ : MA.Qp P.r P.TT → ℂ) x • e ρ x.2) (fun _ => h1) p hp
        simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h3
        exact h3
      · have : ∑ ρ, MA.ext (U ρ : MA.Qp P.r P.TT → ℂ) x • e ρ x.2 = 0 := by
          rw [Finset.univ_eq_empty_iff.2 (not_nonempty_iff.1 hne)]; simp
        rw [this, smul_zero]
        intro p hp
        ext v
        simp
    · simp [φ, Set.indicator_of_notMem hx]
  obtain ⟨Φ, hΦ, hrad⟩ := Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π'
    (radBase P Bs hpl) φ hφ
  refine ⟨Φ, hΦ, fun q => ?_⟩
  have hq : q.1 ∈ NF.QR P.k P.r Bs.z Bs.z' := (qr_iff P Bs hpl q.1).2 q.2
  have h := congrFun hrad q.1
  simp only [NF.radR, Set.indicator_of_mem hq, φ] at h
  rw [h]
  simp only [g]
  congr 1
  refine Finset.sum_congr rfl fun ρ _ => ?_
  congr 1
  simp [MA.ext, q.2]

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
