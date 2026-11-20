import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObjMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjPiQuotPowKerEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLaRingOfIntegersStatement

open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

/- English proof (translation)
Equip the data with the indicated structure. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Reduce the argument to an intermediate assertion. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities.

Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_smul_top_iff_wSub {p : ℕ} [Fact p.Prime] (D : Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (x : D.La) :
    letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
    x ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) D.La) ↔ x ∈ wSub D w0 r := by
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun c hc z _ => ?_) (fun u v hu hv => add_mem hu hv)
    exact Submodule.subset_span ⟨c, hc, z, rfl⟩
  · intro hx
    suffices H : ∀ b : D.O, b • x ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) D.La) by simpa using H 1
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, hc, z', rfl⟩ := hz
      intro b
      rw [smul_smul, ← Algebra.commutes, ← smul_smul]
      exact Submodule.smul_mem_smul (M := D.La) hc Submodule.mem_top
    | zero => intro b; rw [smul_zero]; exact zero_mem _
    | add u v _ _ hu hv => intro b; rw [smul_add]; exact add_mem (hu b) (hv b)
    | smul a u _ hu => intro b; rw [smul_smul]; exact hu (b * a)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem latQuot_free : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ),
    w0.IsMaximal →
    ∃ g : D.La →+ (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r), Function.Surjective g ∧
      (∀ (c : 𝓞 D.F) (x : D.La), g (algebraMap (𝓞 D.F) D.O c • x) = Ideal.Quotient.mk (w0 ^ r) c • g x) ∧
      ∀ x, g x = 0 ↔ x ∈ GlobalTheory.UPel.HT.EtLev.wSub D w0 r := by
  intro p _ D w0 r hw
  letI iL : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  haveI := projective_La_int D
  haveI := D.finLa
  haveI : Module.Finite (𝓞 D.F) D.La := Module.Finite.of_restrictScalars_finite ℤ (𝓞 D.F) D.La
  obtain ⟨g, hs, hk⟩ := GlobalTheory.T.exists_surjective_pi_quotient_pow_ker_eq w0 hw r _ (GlobalTheory.T.finrank_La_ringOfIntegers' D)
  refine ⟨g.toAddMonoidHom, hs, fun c x => ?_, fun x => ?_⟩
  · show g (c • x) = _
    rw [map_smul, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
    rfl
  · show g x = 0 ↔ _
    rw [hk]
    exact mem_smul_top_iff_wSub D w0 r x

end GlobalTheory.UPel.HT.EtLev
