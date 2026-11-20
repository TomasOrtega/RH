import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObjMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjPiQuotPowKerEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLaRingOfIntegersStatement

open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

/- English proof (translation)
Use `letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `Submodule.smul_induction_on hx (fun c hc z _ => ?_) (fun u v hu hv => add_mem hu hv)` and prove the remaining obligations. Conclude with `Submodule.subset_span ⟨c, hc, z, rfl⟩`.

Introduce `hx`. It suffices to establish `H : ∀ b : D.O, b • x ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) D.La) by simpa using H 1`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨c, hc, z', rfl⟩` from `hz`.

Introduce `b`. Rewrite using `[smul_smul, ← Algebra.commutes, ← smul_smul]`. Conclude with `Submodule.smul_mem_smul (M := D.La) hc Submodule.mem_top`. Consider the case `zero => intro b`. Rewrite using `[smul_zero]`.

Conclude with `zero_mem _`. Consider the case `add u v _ _ hu hv => intro b`. Rewrite using `[smul_add]`. Conclude with `add_mem (hu b) (hv b)`. Consider the case `smul a u _ hu => intro b`.

Rewrite using `[smul_smul]`. Conclude with `hu (b * a)`.
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
Introduce `p _ D w0 r hw`. Use `letI iL : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)`. Use `haveI := projective_La_int D`. Use `haveI := D.finLa`. Use `haveI : Module.Finite (𝓞 D.F) D.La := Module.Finite.of_restrictScalars_finite ℤ (𝓞 D.F) D.La`.

Take `⟨g, hs, hk⟩` from `GlobalTheory.T.exists_surjective_pi_quotient_pow_ker_eq w0 hw r _ (GlobalTheory.T.finrank_La_ringOfIntegers' D)`. Use `⟨g.toAddMonoidHom, hs, fun c x => ?_, fun x => ?_⟩` and prove the remaining obligations. Use `show g (c • x) = _`. Rewrite using `[map_smul, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]`. Both sides reduce to the same expression.

Use `show g x = 0 ↔ _`. Rewrite using `[hk]`. Conclude with `mem_smul_top_iff_wSub D w0 r x`.
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
