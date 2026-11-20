import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscOnto
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PhiCountingHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscriminantGroupCounts

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.G5

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

/- English proof (translation)
Unfold `AlphaDisc`. Introduce `K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hd L hL hLi 𝔭 h𝔭 b a hJ`. Use `haveI : Fact (IsFixF K F) := ⟨hF⟩`. Establish `hk1 : 2 * vd h L 𝔭 + 1 ≤ 2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1` using `by omega`. Establish `hk2 : 2 * vJof 𝔭 a + 1 ≤ 2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1` using `by omega`.

Establish `hk0 : 1 ≤ 2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1` using `by omega`. Establish `ha : ∀ i, a i ≠ 0` using `hJ.2.2.2.2`. Establish `hm : finrank K (⊤ : Submodule K V) = finrank K V` using `finrank_top K V`. Establish `hphi` using `hP K F hK 𝔭 h𝔭 _ a ha _ hk0 0 (by simp) (fun i j => by simp)`. Establish `hfib : ∀ T : Matrix (Fin (finrank K (⊤ : Submodule K V))) (Fin (finrank K (⊤ : Submodule K V))) (𝓞 K ⧸ extP K 𝔭 ^ (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1)), Tᴴ = T → (∀ i j, T i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1)))) → Nat.card {Y : Matrix …`.

Introduce `T hT hTm`. Establish `h1` using `hP K F hK 𝔭 h𝔭 _ a ha _ hk0 T hT hTm`. Conclude with `h1.trans hphi.symm` after adjusting the coercions. Establish `hker` using `hKc K F hK 𝔭 h𝔭 _ a ha _ hk2 _ hfib`. Establish `hdisc` using `hD K F V hK h hs hd L hL hLi 𝔭 h𝔭 b a hJ _ hk2`.

Establish `hpos : (0 : ℝ) < Ideal.absNorm 𝔭` using `by exact_mod_cast Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms.absNorm_pos h𝔭`. Establish `e1 : (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K (⊤ : Submodule K V) ^ 2 * (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1)) = (Ideal.absNorm 𝔭 : ℝ) ^ ((2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1) * finrank K V ^ 2)`. Establish `h1` using `congrArg (fun m : ℕ => (Ideal.absNorm 𝔭 : ℝ) ^ (m ^ 2 * (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1))) hm`. Rewrite using `[h1]`. Expand and normalize the polynomial expressions, which then agree.

Establish `e2 : finrank K (⊤ : Submodule K V) - cJof 𝔭 a = finrank K V - cJof 𝔭 a` using `congrArg (fun x => x - cJof 𝔭 a) hm`. Rewrite using `[Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hL hLi h𝔭 hk1, hdisc, hker, Nat.cast_mul, hphi, e1, e2]`. Establish `hne : (Ideal.absNorm 𝔭 : ℝ) ^ ((2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1) * finrank K V ^ 2) ≠ 0` using `pow_ne_zero _ hpos.ne'`. Clear the denominators using the available nonvanishing facts.
-/
theorem alphaDisc_of (hP : PhiCount) (hKc : KerCount) (hD : DiscOnto) : AlphaDisc := by
  unfold AlphaDisc
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hd L hL hLi 𝔭 h𝔭 b a hJ
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  have hk1 : 2 * vd h L 𝔭 + 1 ≤ 2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1 := by omega
  have hk2 : 2 * vJof 𝔭 a + 1 ≤ 2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1 := by omega
  have hk0 : 1 ≤ 2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1 := by omega
  have ha : ∀ i, a i ≠ 0 := hJ.2.2.2.2
  have hm : finrank K (⊤ : Submodule K V) = finrank K V := finrank_top K V
  have hphi := hP K F hK 𝔭 h𝔭 _ a ha _ hk0 0 (by simp) (fun i j => by simp)
  have hfib : ∀ T : Matrix (Fin (finrank K (⊤ : Submodule K V))) (Fin (finrank K (⊤ : Submodule K V)))
      (𝓞 K ⧸ extP K 𝔭 ^ (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1)), Tᴴ = T →
      (∀ i j, T i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1)))) →
      Nat.card {Y : Matrix (Fin (finrank K (⊤ : Submodule K V))) (Fin (finrank K (⊤ : Submodule K V)))
        (𝓞 K ⧸ extP K 𝔭 ^ (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1)) //
          phiQ K 𝔭 (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1) a Y = T} =
      Nat.card {Y : Matrix (Fin (finrank K (⊤ : Submodule K V))) (Fin (finrank K (⊤ : Submodule K V)))
        (𝓞 K ⧸ extP K 𝔭 ^ (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1)) //
          phiQ K 𝔭 (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1) a Y = 0} := by
    intro T hT hTm
    have h1 := hP K F hK 𝔭 h𝔭 _ a ha _ hk0 T hT hTm
    exact_mod_cast h1.trans hphi.symm
  have hker := hKc K F hK 𝔭 h𝔭 _ a ha _ hk2 _ hfib
  have hdisc := hD K F V hK h hs hd L hL hLi 𝔭 h𝔭 b a hJ _ hk2
  have hpos : (0 : ℝ) < Ideal.absNorm 𝔭 := by exact_mod_cast Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms.absNorm_pos h𝔭
  have e1 : (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K (⊤ : Submodule K V) ^ 2 * (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1)) =
      (Ideal.absNorm 𝔭 : ℝ) ^ ((2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1) * finrank K V ^ 2) := by
    have h1 := congrArg (fun m : ℕ => (Ideal.absNorm 𝔭 : ℝ) ^ (m ^ 2 * (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1))) hm
    rw [h1]
    ring
  have e2 : finrank K (⊤ : Submodule K V) - cJof 𝔭 a = finrank K V - cJof 𝔭 a :=
    congrArg (fun x => x - cJof 𝔭 a) hm
  rw [Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hL hLi h𝔭 hk1, hdisc, hker, Nat.cast_mul, hphi, e1, e2]
  have hne : (Ideal.absNorm 𝔭 : ℝ) ^ ((2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1) * finrank K V ^ 2) ≠ 0 :=
    pow_ne_zero _ hpos.ne'
  field_simp

/- English proof (translation)
The claim follows from `alphaDisc_of Formalism.L2.SG.Pf.LocalizedFibreSets.phi_counting_holds (by unfold KerCount intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk N hN exact Formalism.L2.SG.Pf.discriminantGroupCounts.kerCount_main hK h𝔭 ha hk N hN) hD`.
-/
theorem alphaDisc_of_discOnto (hD : DiscOnto) : AlphaDisc :=
  alphaDisc_of Formalism.L2.SG.Pf.LocalizedFibreSets.phi_counting_holds
    (by
      unfold KerCount
      intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk N hN
      exact Formalism.L2.SG.Pf.discriminantGroupCounts.kerCount_main hK h𝔭 ha hk N hN) hD

end Formalism.L2.SG.Pf.G5
