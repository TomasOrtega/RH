import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipIdxNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdemSumMulOfSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.FlipIdemSum

open Formalism.L2.NTheta (IsIdemAt)

/- English proof (translation)
Introduce `D e eT e' P T he hT hTP he'`. Take `⟨⟨es, hes, hsum⟩, hc⟩` from `he`. Take `⟨⟨ts, hts, htsum⟩, -⟩` from `hT`. Take `⟨⟨gs, hgs, hgsum⟩, -⟩` from `he'`. Establish `hmul : ∀ Q ∈ P, e * es Q = es Q` using `fun Q hQ => by`.

Rewrite using `[hsum, Finset.sum_mul, Finset.sum_eq_single_of_mem Q hQ]`. Conclude with `(hes Q hQ).1.1`. Introduce `R hR hne`. Conclude with `GlobalTheory.Tow.idemAt_orth (hes R hR) (hes Q hQ) hne`. Establish `hconj : ∀ PP ∈ P, IsIdemAt (cA D (es PP)) (Formalism.L2.DIV.conjPl PP)` using `fun PP hPP => GlobalTheory.MovedIdem.isIdemAt_conj (hes PP hPP) fun _ => Iff.rfl`.

Establish `hne : ∀ (a : AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)), IsIdemAt a Q → a ≠ 0`. Introduce and unpack `a Q h rfl`. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot Q.ne_bot`. Use `(h.2 x hx0).1 hx` as an intermediate fact. Rewrite `this` using `[zero_mul, RingHom.map_zero]`.

Conclude with `this (zero_mem _)`. Establish `hdisj : Disjoint (P \ T) (T.image Formalism.L2.DIV.conjPl)`. Rewrite using `[Finset.disjoint_left]`. Introduce `Q hQ hQ'`. Take `⟨PP, hPP, rfl⟩` from `Finset.mem_image.1 hQ'`.

Establish `hPPP` using `hTP hPP`. Establish `h1` using `hmul _ (Finset.mem_sdiff.1 hQ).1`. Rewrite `h1` using `[GlobalTheory.Tow.idemAt_unique (hes _ (Finset.mem_sdiff.1 hQ).1) (hconj PP hPPP)]`. Establish `hea' : cA D e * cA D (es PP) = cA D (es PP)` using `by rw [← map_mul, hmul PP hPPP]`. Conclude with `hne _ _ (hconj PP hPPP) (by linear_combination (-1 : AE D) * h1 - e * hea' + cA D (es PP) * hc)`.

Establish `hinj : ∀ a ∈ T, ∀ b ∈ T, Formalism.L2.DIV.conjPl a = Formalism.L2.DIV.conjPl b → a = b` using `fun a _ b _ hab => by`. Rewrite using `[← Formalism.L2.DIV.conjPl_conjPl a, hab, Formalism.L2.DIV.conjPl_conjPl b]`. Establish `hA : ∑ Q ∈ P \ T, gs Q = ∑ Q ∈ P \ T, es Q` using `Finset.sum_congr rfl fun Q hQ => GlobalTheory.Tow.idemAt_unique (hgs Q (Finset.mem_union_left _ hQ)) (hes Q (Finset.mem_sdiff.1 hQ).1)`. Establish `hB : ∑ Q ∈ T.image Formalism.L2.DIV.conjPl, gs Q = cA D eT`. Rewrite using `[Finset.sum_image hinj, htsum, map_sum]`.

Use `Finset.sum_congr rfl fun PP hPP => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.Tow.idemAt_unique (hts PP hPP) (hes PP (hTP hPP))]`. Conclude with `GlobalTheory.Tow.idemAt_unique (hgs _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hPP))) (hconj PP (hTP hPP))`. Establish `hTs : eT = ∑ Q ∈ T, es Q`. Rewrite using `[htsum]`.

Conclude with `Finset.sum_congr rfl fun PP hPP => GlobalTheory.Tow.idemAt_unique (hts PP hPP) (hes PP (hTP hPP))`. Rewrite using `[hgsum, Finset.sum_union hdisj, hA, hB, hTs, hsum, ← Finset.sum_sdiff hTP]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem idemSum_flip_subset : ∀ (D : D7) (e eT e' : AE D) (P T : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → IsIdemSum eT T → T ⊆ P → IsIdemSum e' ((P \ T) ∪ T.image Formalism.L2.DIV.conjPl) → e' = e - eT + cA D eT := by
  intro D e eT e' P T he hT hTP he'
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := he
  obtain ⟨⟨ts, hts, htsum⟩, -⟩ := hT
  obtain ⟨⟨gs, hgs, hgsum⟩, -⟩ := he'
  have hmul : ∀ Q ∈ P, e * es Q = es Q := fun Q hQ => by
    rw [hsum, Finset.sum_mul, Finset.sum_eq_single_of_mem Q hQ]
    · exact (hes Q hQ).1.1
    · intro R hR hne
      exact GlobalTheory.Tow.idemAt_orth (hes R hR) (hes Q hQ) hne
  have hconj : ∀ PP ∈ P, IsIdemAt (cA D (es PP)) (Formalism.L2.DIV.conjPl PP) := fun PP hPP =>
    GlobalTheory.MovedIdem.isIdemAt_conj (hes PP hPP) fun _ => Iff.rfl
  have hne : ∀ (a : AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)), IsIdemAt a Q → a ≠ 0 := by
    rintro a Q h rfl
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot Q.ne_bot
    have := (h.2 x hx0).1 hx
    rw [zero_mul, RingHom.map_zero] at this
    exact this (zero_mem _)
  have hdisj : Disjoint (P \ T) (T.image Formalism.L2.DIV.conjPl) := by
    rw [Finset.disjoint_left]
    intro Q hQ hQ'
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hQ'
    have hPPP := hTP hPP
    have h1 := hmul _ (Finset.mem_sdiff.1 hQ).1
    rw [GlobalTheory.Tow.idemAt_unique (hes _ (Finset.mem_sdiff.1 hQ).1) (hconj PP hPPP)] at h1
    have hea' : cA D e * cA D (es PP) = cA D (es PP) := by rw [← map_mul, hmul PP hPPP]
    exact hne _ _ (hconj PP hPPP)
      (by linear_combination (-1 : AE D) * h1 - e * hea' + cA D (es PP) * hc)
  have hinj : ∀ a ∈ T, ∀ b ∈ T, Formalism.L2.DIV.conjPl a = Formalism.L2.DIV.conjPl b → a = b := fun a _ b _ hab => by
    rw [← Formalism.L2.DIV.conjPl_conjPl a, hab, Formalism.L2.DIV.conjPl_conjPl b]
  have hA : ∑ Q ∈ P \ T, gs Q = ∑ Q ∈ P \ T, es Q := Finset.sum_congr rfl fun Q hQ =>
    GlobalTheory.Tow.idemAt_unique (hgs Q (Finset.mem_union_left _ hQ)) (hes Q (Finset.mem_sdiff.1 hQ).1)
  have hB : ∑ Q ∈ T.image Formalism.L2.DIV.conjPl, gs Q = cA D eT := by
    rw [Finset.sum_image hinj, htsum, map_sum]
    refine Finset.sum_congr rfl fun PP hPP => ?_
    rw [GlobalTheory.Tow.idemAt_unique (hts PP hPP) (hes PP (hTP hPP))]
    exact GlobalTheory.Tow.idemAt_unique (hgs _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hPP))) (hconj PP (hTP hPP))
  have hTs : eT = ∑ Q ∈ T, es Q := by
    rw [htsum]
    exact Finset.sum_congr rfl fun PP hPP => GlobalTheory.Tow.idemAt_unique (hts PP hPP) (hes PP (hTP hPP))
  rw [hgsum, Finset.sum_union hdisj, hA, hB, hTs, hsum, ← Finset.sum_sdiff hTP]
  ring

end GlobalTheory.FlipIdemSum
