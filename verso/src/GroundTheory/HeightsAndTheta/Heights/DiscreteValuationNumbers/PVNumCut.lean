import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.DivisorIdealBotUniformiser
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealCorresp
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealSurj
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialMultAt
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialCycleEval
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ G n hGp hGh hϖG hdim s c hs hsG bs`. Use `set π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) := MvPolynomial.map (IsLocalRing.residue O) with hπ`. Establish `hsp : ∀ V : Ideal (MRing ι O), specialIdeal V = V.map π` using `fun V => rfl`. Establish `hsurj : Function.Surjective π` using `MvPolynomial.map_surjective _ IsLocalRing.residue_surjective`. Establish `hker : RingHom.ker π = Ideal.span {C ϖ}` using `ker_map_residue_eq_span hϖ`.

Establish `hGbp : (specialIdeal G).IsPrime` using `(SpecialIdealCorresp.proof O ϖ hϖ K ι G G hGp hϖG).1`. Establish `hGbh : IsMultiHomogIdeal (specialIdeal G)` using `SpecialIdealMultiHomog.proof O K ι G hGh`. Establish `hdimb : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal G) < ((n + 2 + Fintype.card K : ℕ) : WithBot ℕ∞)`. Rewrite using `[SpecialQuotDim.proof O ϖ hϖ K ι G hϖG]`. Conclude with `hdim`.

Establish `hsb : IsMultiHomog (π s) c` using `isWeightedHomogeneous_map_of _ _ hs`. Establish `hsbG : π s ∉ specialIdeal G`. Introduce `hm`. Apply `hsG` to reduce the goal to its premises. Establish `hcm : (G.map π).comap π = G`.

Rewrite using `[Ideal.comap_map_of_surjective' π hsurj, hker, sup_eq_left, Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `hϖG`. Rewrite using `[← hcm]`. Conclude with `hm`. Establish `hcut` using `h (IsLocalRing.ResidueField O) K ι n (specialIdeal G) hGbp hGbh hdimb (π s) c hsb hsbG bs`.

Establish `hJ : G ⊔ Ideal.span {s} ⊔ Ideal.span {C ϖ} = G ⊔ Ideal.span {s}`. Rewrite using `[sup_eq_left, Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `Ideal.mem_sup_left hϖG`. Establish `hdiv : divCycle G s = divCycle (G ⊔ Ideal.span {s}) (C ϖ)`. Rewrite using `[divCycle_eq_idealCycle, divCycle_eq_idealCycle, hJ]`.

Establish `hmapJ : specialIdeal (G ⊔ Ideal.span {s}) = specialIdeal G ⊔ Ideal.span {π s}`. Rewrite using `[hsp, hsp, Ideal.map_sup, Ideal.map_span, Set.image_singleton]`. Establish `htr` using `SpecialCycleEval.proof SpecialIdealCorresp.proof SpecialIdealSurj.proof SpecialMultAt.proof O ϖ hϖ K ι (G ⊔ Ideal.span {s}) (fun V => intNum (IsLocalRing.ResidueField O) V bs)`. Rewrite `htr` using `[hmapJ, ← divCycle_eq_idealCycle]`. Use `show intNum (IsLocalRing.ResidueField O) (specialIdeal G) _ = cycEval (fun U => intNum (IsLocalRing.ResidueField O) (specialIdeal U) bs) (divCycle G s)`.

Rewrite using `[hcut, hdiv, htr]`.
-/
theorem VNumCut.proof (h : CutByForm.Statement.{u}) : VNumCut.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ G n hGp hGh hϖG hdim s c hs hsG bs
  set π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O) with hπ
  have hsp : ∀ V : Ideal (MRing ι O), specialIdeal V = V.map π := fun V => rfl
  have hsurj : Function.Surjective π :=
    MvPolynomial.map_surjective _ IsLocalRing.residue_surjective
  have hker : RingHom.ker π = Ideal.span {C ϖ} := ker_map_residue_eq_span hϖ

  have hGbp : (specialIdeal G).IsPrime :=
    (SpecialIdealCorresp.proof O ϖ hϖ K ι G G hGp hϖG).1
  have hGbh : IsMultiHomogIdeal (specialIdeal G) := SpecialIdealMultiHomog.proof O K ι G hGh
  have hdimb : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal G) <
      ((n + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [SpecialQuotDim.proof O ϖ hϖ K ι G hϖG]; exact hdim
  have hsb : IsMultiHomog (π s) c := isWeightedHomogeneous_map_of _ _ hs
  have hsbG : π s ∉ specialIdeal G := by
    intro hm
    apply hsG
    have hcm : (G.map π).comap π = G := by
      rw [Ideal.comap_map_of_surjective' π hsurj, hker, sup_eq_left, Ideal.span_le,
        Set.singleton_subset_iff]
      exact hϖG
    rw [← hcm]
    exact hm

  have hcut := h (IsLocalRing.ResidueField O) K ι n (specialIdeal G) hGbp hGbh hdimb (π s) c hsb
    hsbG bs

  have hJ : G ⊔ Ideal.span {s} ⊔ Ideal.span {C ϖ} = G ⊔ Ideal.span {s} := by
    rw [sup_eq_left, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_sup_left hϖG
  have hdiv : divCycle G s = divCycle (G ⊔ Ideal.span {s}) (C ϖ) := by
    rw [divCycle_eq_idealCycle, divCycle_eq_idealCycle, hJ]
  have hmapJ : specialIdeal (G ⊔ Ideal.span {s}) = specialIdeal G ⊔ Ideal.span {π s} := by
    rw [hsp, hsp, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have htr := SpecialCycleEval.proof SpecialIdealCorresp.proof SpecialIdealSurj.proof
    SpecialMultAt.proof O ϖ hϖ K ι (G ⊔ Ideal.span {s})
    (fun V => intNum (IsLocalRing.ResidueField O) V bs)
  rw [hmapJ, ← divCycle_eq_idealCycle] at htr
  show intNum (IsLocalRing.ResidueField O) (specialIdeal G) _ =
    cycEval (fun U => intNum (IsLocalRing.ResidueField O) (specialIdeal U) bs) (divCycle G s)
  rw [hcut, hdiv, htr]

end GroundTheory.Heights₂.Heights.NumbersDVR
