import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASectionCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSTr

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

/- English proof (translation)
Take `⟨Φ, hΦ, hval⟩` from `hR Wp Wq P Bs hpl e he U`. Take `⟨D₀, hD₀, K, hK, hKv⟩` from `hD Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bs.z_mem Bs.z'_mem Φ hΦ`. Establish `hsub : ∀ g ∈ Q.Glev P.k P.r 0 ∩ Q.OmPlus P.k P.r Bs.z Bs.z', g ∈ D₀`. Introduce `g hg`. Take `⟨n, hn, n', hn', c, hc, g₁, hg₁, hGG, hgeq⟩` from `hC P.k P.r Bs.z Bs.z' Bs.z_mem Bs.z'_mem g hg`.

Establish `hw` using `(hKv c hc g₁ hg₁ hGG).1`. Establish `hwG : Q.wCell P.k P.r (Fin.last P.r) c * g₁ ∈ Q.Glev P.k P.r 0` using `Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _) (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hg₁)`. Rewrite using `[hgeq]`. Conclude with `hD₀.2 _ ⟨hwG, hw⟩ n ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one _, n, hn, (Matrix.one_mul n).symm⟩ n' ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one _, n', hn', (Matrix.one_mul n').symm⟩`. Use `⟨K, ?_, ?_⟩` and prove the remaining obligations.

Take `⟨hs, hL, hRt, hW⟩` from `hK`. Conclude with `⟨fun g₀ hg₀ => hs g₀ ⟨hg₀.1, hsub g₀ hg₀⟩, fun g hg n hn => hL g ⟨hg.1, hsub g hg⟩ n hn, fun g hg n hn => hRt g ⟨hg.1, hsub g hg⟩ n hn, fun g hg h hh h' hh' => hW g ⟨hg.1, hsub g hg⟩ h hh h' hh'⟩`. Use function extensionality and compare the values at `ρ`. Establish `hraw : Gauge.rawJ P Bs e K ρ = (U ρ : MA.Qp P.r P.TT → ℂ)`. Use function extensionality and compare the values at `q`.

Establish `hζ : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq q.1.2`. Rewrite using `[Gauge.GC.SSTr.tz_eq P Bs hpl]`. Conclude with `q.2.2`. Establish `hG : NF.muZ P.k P.r Bs.μsec q.1.2 ∈ Q.Glev P.k P.r (Fin.last P.r)` using `Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_uwb Bs.sec hζ)`. Establish `hGG : 0 < Q.GGl P.k P.r Bs.z Bs.z' (NF.muZ P.k P.r Bs.μsec q.1.2)`.

Unfold `Q.GGl`. Rewrite using `[Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ Bs.z_mem Bs.z'_mem Bs.sec hζ]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hζ' : P.TT < Complex.normSq q.1.2` using `q.2.2`. Establish `horth` using `(he.2 q.1.2 hζ').2.1`.

Establish `hwpos : 0 < Real.sqrt (MA.wq P.k q.1 P.TT)` using `Real.sqrt_pos.2 (Formalism.FourierDecayAlt.P.CutMP.En.wq_pos q.2)`. Establish `hw : ((Real.sqrt (MA.wq P.k q.1 P.TT) : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hwpos.ne'`. Simplify using `only [Gauge.rawJ]`. Rewrite using `[Gauge.tc_gq, (hKv q.1.1 q.2.1 _ hG hGG).2, hval q, Gauge.tc_hsVec_smul, inner_smul_right, Gauge.tc_hsVec_sum, inner_sum]`. Simplify using `only [Gauge.tc_hsVec_smul, inner_smul_right, horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Use `show MA.toSm P (Gauge.rawJ P Bs e K ρ) = U ρ`. Establish `hm : Gauge.rawJ P Bs e K ρ ∈ MA.smSub P.r P.TT` using `by rw [hraw]; exact (U ρ).2`. Rewrite using `[Gauge.toSm_of_mem P hm]`.

Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `hraw`.
-/
theorem sec_at (hR : SARadSec) (hD : SADescend) (hC : SACover)
    {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : Gauge.IsFrameB P Bs e)
    (U : M.Ty P → MA.SmQ P.r P.TT) :
    ∃ K ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Q.OmPlus P.k P.r Bs.z Bs.z'), Gauge.trJB P Bs e K = U := by
  obtain ⟨Φ, hΦ, hval⟩ := hR Wp Wq P Bs hpl e he U
  obtain ⟨D₀, hD₀, K, hK, hKv⟩ := hD Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bs.z_mem Bs.z'_mem Φ hΦ
  have hsub : ∀ g ∈ Q.Glev P.k P.r 0 ∩ Q.OmPlus P.k P.r Bs.z Bs.z', g ∈ D₀ := by
    intro g hg
    obtain ⟨n, hn, n', hn', c, hc, g₁, hg₁, hGG, hgeq⟩ := hC P.k P.r Bs.z Bs.z' Bs.z_mem Bs.z'_mem g hg
    have hw := (hKv c hc g₁ hg₁ hGG).1
    have hwG : Q.wCell P.k P.r (Fin.last P.r) c * g₁ ∈ Q.Glev P.k P.r 0 :=
      Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _)
        (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hg₁)
    rw [hgeq]
    exact hD₀.2 _ ⟨hwG, hw⟩ n ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one _, n, hn, (Matrix.one_mul n).symm⟩ n'
      ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one _, n', hn', (Matrix.one_mul n').symm⟩
  refine ⟨K, ?_, ?_⟩
  · obtain ⟨hs, hL, hRt, hW⟩ := hK
    exact ⟨fun g₀ hg₀ => hs g₀ ⟨hg₀.1, hsub g₀ hg₀⟩, fun g hg n hn => hL g ⟨hg.1, hsub g hg⟩ n hn,
      fun g hg n hn => hRt g ⟨hg.1, hsub g hg⟩ n hn, fun g hg h hh h' hh' => hW g ⟨hg.1, hsub g hg⟩ h hh h' hh'⟩
  · funext ρ
    have hraw : Gauge.rawJ P Bs e K ρ = (U ρ : MA.Qp P.r P.TT → ℂ) := by
      funext q
      have hζ : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq q.1.2 := by
        rw [Gauge.GC.SSTr.tz_eq P Bs hpl]; exact q.2.2
      have hG : NF.muZ P.k P.r Bs.μsec q.1.2 ∈ Q.Glev P.k P.r (Fin.last P.r) :=
        Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_uwb Bs.sec hζ)
      have hGG : 0 < Q.GGl P.k P.r Bs.z Bs.z' (NF.muZ P.k P.r Bs.μsec q.1.2) := by
        unfold Q.GGl
        rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ Bs.z_mem Bs.z'_mem Bs.sec hζ]
        linarith
      have hζ' : P.TT < Complex.normSq q.1.2 := q.2.2
      have horth := (he.2 q.1.2 hζ').2.1
      have hwpos : 0 < Real.sqrt (MA.wq P.k q.1 P.TT) := Real.sqrt_pos.2 (Formalism.FourierDecayAlt.P.CutMP.En.wq_pos q.2)
      have hw : ((Real.sqrt (MA.wq P.k q.1 P.TT) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hwpos.ne'
      simp only [Gauge.rawJ]
      rw [Gauge.tc_gq, (hKv q.1.1 q.2.1 _ hG hGG).2, hval q, Gauge.tc_hsVec_smul, inner_smul_right,
        Gauge.tc_hsVec_sum, inner_sum]
      simp only [Gauge.tc_hsVec_smul, inner_smul_right, horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      push_cast
      field_simp
    show MA.toSm P (Gauge.rawJ P Bs e K ρ) = U ρ
    have hm : Gauge.rawJ P Bs e K ρ ∈ MA.smSub P.r P.TT := by rw [hraw]; exact (U ρ).2
    rw [Gauge.toSm_of_mem P hm]
    apply Subtype.ext
    exact hraw

/- English proof (translation)
Use `⟨0, ?_⟩` and prove the remaining obligations. Introduce `E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he U _`. Take `⟨hIB, -, -, -⟩` from `hB`. Take `⟨-, -, -, hIsB, -⟩` from `hIB`. Establish `hpl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π'` using `(hIsB.2 v).2.2.2.1`.

Take `⟨K, hK, hKU⟩` from `sec_at hR hD hC (D.parOf S v) (T v).base hpl e he U`. Use `⟨K, ?_, hKU⟩` and prove the remaining obligations. Use `show K ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)`. Rewrite using `[Formalism.FourierDecayAlt.P.CutMP.JA.FFS.omP_eq E Wp Wq S T v]`. Conclude with `hK`.
-/
theorem sASection_of_parts (hR : SARadSec) (hD : SADescend) (hC : SACover) : SASection := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he U _
  obtain ⟨hIB, -, -, -⟩ := hB
  obtain ⟨-, -, -, hIsB, -⟩ := hIB
  have hpl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hIsB.2 v).2.2.2.1
  obtain ⟨K, hK, hKU⟩ := sec_at hR hD hC (D.parOf S v) (T v).base hpl e he U
  refine ⟨K, ?_, hKU⟩
  show K ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)
  rw [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.omP_eq E Wp Wq S T v]
  exact hK

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
