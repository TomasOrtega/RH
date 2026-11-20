import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift GlobalTheory.TateTop

namespace GlobalTheory.TateTop

/- English proof (translation)
Introduce `l _ P K LL _ _ _ O _ _ hO L1 hL1`. Take `⟨hΦ1, hΦ2⟩` from `continuous_fixingSubgroupEquiv K.1`. Use `set Φ := K.1.fixingSubgroupEquiv with hΦ`. Establish `hcyc : IsCyc P.χQ` using `P.χQ_cyc`. Set `χZ : Formalism.GaloisCohomology.GK l K.1 →* ℤ_[l]ˣ` to `(cyclotomicCharacter (PadicAlgCl l) l).comp (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK l K.1) (PadicAlgCl l))`.

Establish `hχZ : ∀ g, ((χZ g : ℤ_[l]) : ℚ_[l]) = (P.χQ (Φ.symm g : GQ l) : ℚ_[l])` using `fun g => by`. Rewrite using `[isCyc_unique hcyc (isCyc_cycChar l)]`. Both sides reduce to the same expression. Establish `hχc : Continuous fun g => (χZ g : ℤ_[l])`. Rewrite using `[continuous_iff_coe]`.

Simplify using `only [hχZ]`. Conclude with `hcyc.continuous.comp (continuous_subtype_val.comp hΦ1)`. Take `⟨c, hc⟩` from `exists_gen_all hχc fun r => by`. Establish `: NeZero (l ^ (r + 1))` using `⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Conclude with `exists_gen hχc (hT l K.1 K.2 (r + 1) (ZMod (l ^ (r + 1))) (ReciprocityTheory.Gal.charRep (redChar χZ (r + 1))) (Nat.succ_pos _) (contAction_charRep _ ((continuous_toZModPow _).comp hχc))).1 fun M _ _ _ _ _ rho hrho => (hT l K.1 K.2 (r + 1) M rho (Nat.succ_pos _) hrho).2.2.2.2`.

Establish `hcpt : CompactSpace (GK K)` using `Φ.symm.surjective.compactSpace hΦ1`. Take `⟨ι, hι⟩` from `exists_ringHom hO`. Set `: Module ℤ_[l] (LL ⧸ L1.T)` to `Module.compHom _ ι`. Establish `: SMulCommClass ℤ_[l] O (LL ⧸ L1.T)` using `⟨fun a o x => smul_comm (ι a) o x⟩`. Establish `hs : ∀ (a : ℤ_[l]) (x : LL), a • (Submodule.Quotient.mk x : LL ⧸ L1.T) = Submodule.Quotient.mk (algebraMap ℚ_[l] LL a * x)` using `fun a x => by`.

Rewrite using `[← hι, ← Algebra.smul_def]`. Both sides reduce to the same expression. Use `@h2_equiv_of_torsion_character l _ (GK K) _ _ _ _ _ _ hcpt _ (fun r => (hc r).transport Φ hΦ2 hΦ1) (fun x => ?_) O _ _ _ _ fun g x => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Take `⟨n, hn⟩` from `exists_pow_smul_mem hO x`.

Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[hs, Submodule.Quotient.mk_eq_zero, hL1]`. Simplify using `using hn 1`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite using `[hs]`.

Establish `h1` using `hχZ (Φ g)`. Rewrite `h1` using `[show Φ.symm (Φ g) = g from Φ.symm_apply_apply g, ← P.PD_χ K g]`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (algebraMap ℚ_[l] LL ((P.PD K).χ g : ℚ_[l]) * x) = _`. Rewrite using `[← h1]`. Both sides reduce to the same expression.
-/
theorem tateH2_of_duality_loc (hT : Formalism.GaloisCohomology.LocalTateDualityK) :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), LocalTateTopDegree (P.PD K) := by
  intro l _ P K LL _ _ _ O _ _ hO L1 hL1
  obtain ⟨hΦ1, hΦ2⟩ := continuous_fixingSubgroupEquiv K.1
  set Φ := K.1.fixingSubgroupEquiv with hΦ
  have hcyc : IsCyc P.χQ := P.χQ_cyc
  let χZ : Formalism.GaloisCohomology.GK l K.1 →* ℤ_[l]ˣ := (cyclotomicCharacter (PadicAlgCl l) l).comp
      (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK l K.1) (PadicAlgCl l))
  have hχZ : ∀ g, ((χZ g : ℤ_[l]) : ℚ_[l]) = (P.χQ (Φ.symm g : GQ l) : ℚ_[l]) := fun g => by
    rw [isCyc_unique hcyc (isCyc_cycChar l)]; rfl
  have hχc : Continuous fun g => (χZ g : ℤ_[l]) := by
    rw [continuous_iff_coe]
    simp only [hχZ]
    exact hcyc.continuous.comp (continuous_subtype_val.comp hΦ1)
  obtain ⟨c, hc⟩ := exists_gen_all hχc fun r => by
    have : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact exists_gen hχc
      (hT l K.1 K.2 (r + 1) (ZMod (l ^ (r + 1))) (ReciprocityTheory.Gal.charRep (redChar χZ (r + 1)))
        (Nat.succ_pos _) (contAction_charRep _ ((continuous_toZModPow _).comp hχc))).1
      fun M _ _ _ _ _ rho hrho => (hT l K.1 K.2 (r + 1) M rho (Nat.succ_pos _) hrho).2.2.2.2
  have hcpt : CompactSpace (GK K) := Φ.symm.surjective.compactSpace hΦ1
  obtain ⟨ι, hι⟩ := exists_ringHom hO
  let : Module ℤ_[l] (LL ⧸ L1.T) := Module.compHom _ ι
  have : SMulCommClass ℤ_[l] O (LL ⧸ L1.T) := ⟨fun a o x => smul_comm (ι a) o x⟩
  have hs : ∀ (a : ℤ_[l]) (x : LL), a • (Submodule.Quotient.mk x : LL ⧸ L1.T) =
      Submodule.Quotient.mk (algebraMap ℚ_[l] LL a * x) := fun a x => by
    rw [← hι, ← Algebra.smul_def]
    rfl
  refine @h2_equiv_of_torsion_character l _ (GK K) _ _ _ _ _ _ hcpt _ (fun r => (hc r).transport Φ hΦ2 hΦ1)
    (fun x => ?_) O _ _ _ _ fun g x => ?_
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨n, hn⟩ := exists_pow_smul_mem hO x
    refine ⟨n, ?_⟩
    rw [hs, Submodule.Quotient.mk_eq_zero, hL1]
    simpa using hn 1
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [hs]
    have h1 := hχZ (Φ g)
    rw [show Φ.symm (Φ g) = g from Φ.symm_apply_apply g, ← P.PD_χ K g] at h1
    change Submodule.Quotient.mk (algebraMap ℚ_[l] LL ((P.PD K).χ g : ℚ_[l]) * x) = _
    rw [← h1]
    rfl

end GlobalTheory.TateTop
