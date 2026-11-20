import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKleimanScheme
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAmpleOfGenTwist
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsLast
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsSide
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsExtra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

/- English proof (translation)
Introduce `W hW hQW` and use `hN W hW (hVQ.trans hQW)`.
-/
theorem nefOnF_mono {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {I : IFamily F ι} {V Q : Ideal (MRingOver F ι)} {α : K → ℤ} (hN : KH.NefOnF I V α) (hVQ : V ≤ Q) :
    KH.NefOnF I Q α :=
  fun W hW hQW => hN W hW (hVQ.trans hQW)

/- English proof (translation)
Take `⟨q₂, hq₂, hgen, hvan⟩` from `h`. Use `⟨q₂ * q, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_, fun e => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul]` and apply the resulting hypothesis. Take `⟨c₁, hc⟩` from `hvan e`. Use `⟨c₁, fun c hc' => ?_⟩` and prove the remaining obligations.

Use `hc c hc'` as an intermediate fact. Rewrite `this` using `[smul_smul, mul_assoc]`. Then use the resulting hypothesis.
-/
theorem ampleV_of_nsmul {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {V : Ideal (MRingOver S ι)} {N : K → ℤ} {q : ℕ} (hq : 1 ≤ q)
    (h : KH.AmpleV S V (q • N)) : KH.AmpleV S V N := by
  obtain ⟨q₂, hq₂, hgen, hvan⟩ := h
  refine ⟨q₂ * q, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_, fun e => ?_⟩
  · rwa [mul_smul]
  · obtain ⟨c₁, hc⟩ := hvan e
    refine ⟨c₁, fun c hc' => ?_⟩
    have := hc c hc'
    rwa [smul_smul, mul_assoc] at this

/- English proof (translation)
Introduce `F _ K _ _ ι _ _ I V α b a hI hV hN hb ha`. Establish `hamp : H1GenAmple F V (b • α + fun _ => (a : ℤ))` using `hDev F K ι V _ inferInstance fun P hP hVP => hVar F K ι I P α b a hI hP (nefOnF_mono hN hVP) hb ha`. Take `⟨c₁, hc⟩` from `hGen F K ι V _ hV hamp (fun _ => -1)`. Establish `hg` using `hc (c₁ + 1) (Nat.le_succ c₁)`. Establish `h` using `hAG F K ι V _ 1 1 hV hg le_rfl`.

Establish `e : ((1 : ℕ) : ℤ) • ((fun _ => (-1 : ℤ)) + (c₁ + 1) • (b • α + fun _ => (a : ℤ))) + (fun _ => ((1 : ℕ) : ℤ)) = (c₁ + 1) • (b • α + fun _ => (a : ℤ))`. Use function extensionality and compare the values at `k`. Simplify using `only [Nat.cast_one, one_smul, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[e]`.

Conclude with `ampleV_of_nsmul (Nat.le_add_left 1 c₁) h`.
-/
theorem KleimanScheme.proof (hVar : KleimanVarietyH1Generation.Statement) (hDev : H1GenerationDevissage.Statement)
    (hGen : GenerationOfH1GenAmple.Statement) (hAG : AmpleOfGenTwist.Statement) : KleimanScheme.Statement := by
  intro F _ K _ _ ι _ _ I V α b a hI hV hN hb ha

  have hamp : H1GenAmple F V (b • α + fun _ => (a : ℤ)) :=
    hDev F K ι V _ inferInstance fun P hP hVP => hVar F K ι I P α b a hI hP (nefOnF_mono hN hVP) hb ha

  obtain ⟨c₁, hc⟩ := hGen F K ι V _ hV hamp (fun _ => -1)
  have hg := hc (c₁ + 1) (Nat.le_succ c₁)

  have h := hAG F K ι V _ 1 1 hV hg le_rfl
  have e : ((1 : ℕ) : ℤ) • ((fun _ => (-1 : ℤ)) + (c₁ + 1) • (b • α + fun _ => (a : ℤ))) +
      (fun _ => ((1 : ℕ) : ℤ)) = (c₁ + 1) • (b • α + fun _ => (a : ℤ)) := by
    funext k
    simp only [Nat.cast_one, one_smul, Pi.add_apply]
    ring
  rw [e] at h
  exact ampleV_of_nsmul (Nat.le_add_left 1 c₁) h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
