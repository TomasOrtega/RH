import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogReducesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmEqPSmulAddIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesReductionModPrimeRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionCommutesFormalGroupLawCoboundariesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiLogRedStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

/- English proof (translation)
Introduce `p _ k _ _ _ d μ h V _ _ ρ hρ`. Establish `hμ' : ∀ i, constantCoeff (Katz.lift p (μ i)) = 0` using `fun i => constantCoeff_lift p (h.const i)`. Establish `hR1` using `GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d)`. Establish `hR2` using `GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)`. Establish `hC` using `GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d μ h.const`.

Establish `hD` using `GlobalTheory.T.quasiLog_reduces_to_cocycle p k d μ h`. Establish `hK` using `GlobalTheory.T.quasiLogarithm_eq_p_smul_add_integral p k d μ h`. Establish `hS` using `GlobalTheory.T.exists_quasiLog_red_coboundary_and_linear p k d μ h`. Establish `hVu : ∀ (v : Fin d → Fr p k) (w w' : Fin d → k), RedV p v w → RedV p v w' → w = w'`. Introduce `v w w' h1 h2`.

Use function extensionality and compare the values at `i`. Take `⟨a, ha, ha'⟩` from `h1 i`. Take `⟨b, hb, hb'⟩` from `h2 i`. Rewrite `hb` using `[ha]`. Rewrite using `[← ha', ← hb', IsFractionRing.injective (WittVector p k) (Fr p k) hb]`.

Establish `hVa : ∀ (v v' : Fin d → Fr p k) (w w' : Fin d → k), RedV p v w → RedV p v' w' → RedV p (v + v') (w + w')`. Introduce `v v' w w' h1 h2 i`. Take `⟨a, ha, ha'⟩` from `h1 i`. Take `⟨b, hb, hb'⟩` from `h2 i`. Conclude with `⟨a + b, by rw [Pi.add_apply, ha, hb, map_add], by rw [map_add, ha', hb']; rfl⟩`.

Establish `hVs : ∀ (r : WittVector p k) (v : Fin d → Fr p k) (w : Fin d → k), RedV p v w → RedV p (fun i => algebraMap _ (Fr p k) r * v i) (WittVector.constantCoeff r • w)`. Introduce `r v w h1 i`. Take `⟨a, ha, ha'⟩` from `h1 i`. Conclude with `⟨r * a, by beta_reduce; rw [ha, ← map_mul], by rw [map_mul, ha']; rfl⟩`. Establish `hlinadd : ∀ f g : MvPowerSeries (Fin d) (Fr p k), lin (f + g) = lin f + lin g`.

Introduce `f g`. Use function extensionality and compare the values at `i`. Simplify using `[lin]`. Establish `hlinsmul : ∀ (r : WittVector p k) (f : MvPowerSeries (Fin d) (Fr p k)), lin (r • f) = fun i => algebraMap _ (Fr p k) r * lin f i`. Introduce `r f`.

Use function extensionality and compare the values at `i`. Simplify using `only [lin, ← algebraMap_smul (Fr p k) r f, coeff_smul, smul_eq_mul]`. Establish `hcobs : ∀ (r : WittVector p k) (f : MvPowerSeries (Fin d) (Fr p k)), cob1 (fun i => Katz.lift p (μ i)) (r • f) = r • cob1 (fun i => Katz.lift p (μ i)) f`. Introduce `r f`. Rewrite using `[← algebraMap_smul (Fr p k) r f, formalCoboundary_smul hμ', algebraMap_smul]`.

Use `choose c w hc hw using hD.1`. Establish `key : ∀ f (hf : f ∈ quasiLog p h) c' w', Red p (cob1 (fun i => Katz.lift p (μ i)) f) c' → RedV p (lin f) w' → ρ (c f hf, w f hf) = ρ (c', w')`. Introduce `f hf c' w' h1 h2`. Rewrite using `[hR2.2.1 _ _ _ (hc f hf) h1, hVu _ _ _ (hw f hf) h2]`. Set `Φ : quasiLog p h →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] V` to `{ toFun := fun f => ρ (c f.1 f.2, w f.1 f.2) map_add' := fun f g => by`.

Rewrite using `[key (f + g).1 (f + g).2 (c f.1 f.2 + c g.1 g.2) (w f.1 f.2 + w g.1 g.2), ← map_add, Prod.mk_add_mk]`. Rewrite using `[Submodule.coe_add, formalCoboundary_add hμ']`. Conclude with `(hR2.2.2.2.1 _ _ _ _ (hc _ _) (hc _ _)).1`. Rewrite using `[Submodule.coe_add, hlinadd]`. Conclude with `hVa _ _ _ _ (hw _ _) (hw _ _)`.

Use the proof step `map_smul' := fun r f => by`. Rewrite using `[key (r • f).1 (r • f).2 (WittVector.constantCoeff r • c f.1 f.2) (WittVector.constantCoeff r • w f.1 f.2), ← map_smul, Prod.smul_mk]`. Rewrite using `[Submodule.coe_smul, hcobs]`. Conclude with `hR2.2.2.2.2.1 _ _ _ (hc _ _)`. Rewrite using `[Submodule.coe_smul, hlinsmul]`.

Conclude with `hVs _ _ _ (hw _ _) }`. Establish `hΦ : ∀ f : quasiLog p h, Φ f = ρ (c f.1 f.2, w f.1 f.2)` using `fun _ => rfl`. Establish `hker : (intBy p k (Fin d) 1).submoduleOf (quasiLog p h) ≤ LinearMap.ker Φ`. Introduce `f hf`. Rewrite using `[LinearMap.mem_ker, hΦ]`.

Establish `hf' : (f : MvPowerSeries (Fin d) (Fr p k)) ∈ intBy p k (Fin d) 1` using `hf`. Take `⟨b, hb⟩` from `(hR1.1 _).1 hf'`. Take `⟨h1, h2⟩` from `hC.2.1 _ _ hb`. Rewrite using `[key _ _ _ _ h1 h2]`. Conclude with `((hρ.ker _ _ (hD.2 _ f.2 _ h1)).2 ⟨b, rfl, rfl⟩)`.

Use `⟨Submodule.liftQ _ Φ hker, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `f c' w' h1 h2`. Rewrite using `[Submodule.liftQ_apply, hΦ, key _ _ _ _ h1 h2]`. Introduce `v`. Take `⟨c', w', hcoc, rfl⟩` from `hρ.surj v`.

Take `⟨f, hf, h1, h2⟩` from `hS c' hcoc w'`. Conclude with `⟨Submodule.Quotient.mk ⟨f, hf⟩, by rw [Submodule.liftQ_apply, hΦ, key _ _ _ _ h1 h2]⟩`. Introduce `m`. Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ m`. Rewrite using `[Submodule.liftQ_apply, hΦ]`.

Prove the components needed by the constructor for the conclusion. Introduce `h0`. Take `⟨b, hb1, hb2⟩` from `(hρ.ker _ _ (hD.2 _ f.2 _ (hc f.1 f.2))).1 h0`. Establish `h1` using `hc f.1 f.2`. Establish `h2` using `hw f.1 f.2`.

Rewrite `h1` using `[hb1]`. Rewrite `h2` using `[hb2]`. Take `⟨g, hg, hfg⟩` from `hK f.1 f.2 b h1 h2`. Use `⟨Submodule.Quotient.mk ⟨g, hg⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← Nat.cast_smul_eq_nsmul (WittVector p k), ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]`.

Conclude with `hfg`. Introduce and unpack `⟨n, hn⟩`. Establish `: Φ f = Submodule.liftQ _ Φ hker (p • n)`. Rewrite using `[← hn, Submodule.liftQ_apply]`. Rewrite using `[← hΦ, this, map_nsmul, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]`.
-/
theorem Katz.reductionMap : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ) (V : Type) [AddCommGroup V] [Module k V] (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] V), IsRigOf μ ρ → ∃ r : Mod p h →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] V, (∀ (f : quasiLog p h) c w, Red p (cob1 (fun i => Katz.lift p (μ i)) f.1) c → RedV p (lin f.1) w → r (Submodule.Quotient.mk f) = ρ (c, w)) ∧ Function.Surjective r ∧ ∀ m, r m = 0 ↔ ∃ n, m = p • n := by
  intro p _ k _ _ _ d μ h V _ _ ρ hρ
  have hμ' : ∀ i, constantCoeff (Katz.lift p (μ i)) = 0 := fun i => constantCoeff_lift p (h.const i)
  have hR1 := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d)
  have hR2 := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)
  have hC := GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d μ h.const
  have hD := GlobalTheory.T.quasiLog_reduces_to_cocycle p k d μ h
  have hK := GlobalTheory.T.quasiLogarithm_eq_p_smul_add_integral p k d μ h
  have hS := GlobalTheory.T.exists_quasiLog_red_coboundary_and_linear p k d μ h
  have hVu : ∀ (v : Fin d → Fr p k) (w w' : Fin d → k), RedV p v w → RedV p v w' → w = w' := by
    intro v w w' h1 h2
    funext i
    obtain ⟨a, ha, ha'⟩ := h1 i
    obtain ⟨b, hb, hb'⟩ := h2 i
    rw [ha] at hb
    rw [← ha', ← hb', IsFractionRing.injective (WittVector p k) (Fr p k) hb]
  have hVa : ∀ (v v' : Fin d → Fr p k) (w w' : Fin d → k), RedV p v w → RedV p v' w' →
      RedV p (v + v') (w + w') := by
    intro v v' w w' h1 h2 i
    obtain ⟨a, ha, ha'⟩ := h1 i
    obtain ⟨b, hb, hb'⟩ := h2 i
    exact ⟨a + b, by rw [Pi.add_apply, ha, hb, map_add], by rw [map_add, ha', hb']; rfl⟩
  have hVs : ∀ (r : WittVector p k) (v : Fin d → Fr p k) (w : Fin d → k), RedV p v w →
      RedV p (fun i => algebraMap _ (Fr p k) r * v i) (WittVector.constantCoeff r • w) := by
    intro r v w h1 i
    obtain ⟨a, ha, ha'⟩ := h1 i
    exact ⟨r * a, by beta_reduce; rw [ha, ← map_mul], by rw [map_mul, ha']; rfl⟩
  have hlinadd : ∀ f g : MvPowerSeries (Fin d) (Fr p k), lin (f + g) = lin f + lin g := by
    intro f g; funext i; simp [lin]
  have hlinsmul : ∀ (r : WittVector p k) (f : MvPowerSeries (Fin d) (Fr p k)),
      lin (r • f) = fun i => algebraMap _ (Fr p k) r * lin f i := by
    intro r f; funext i
    simp only [lin, ← algebraMap_smul (Fr p k) r f, coeff_smul, smul_eq_mul]
  have hcobs : ∀ (r : WittVector p k) (f : MvPowerSeries (Fin d) (Fr p k)),
      cob1 (fun i => Katz.lift p (μ i)) (r • f) = r • cob1 (fun i => Katz.lift p (μ i)) f := by
    intro r f
    rw [← algebraMap_smul (Fr p k) r f, formalCoboundary_smul hμ', algebraMap_smul]
  choose c w hc hw using hD.1
  have key : ∀ f (hf : f ∈ quasiLog p h) c' w', Red p (cob1 (fun i => Katz.lift p (μ i)) f) c' →
      RedV p (lin f) w' → ρ (c f hf, w f hf) = ρ (c', w') := by
    intro f hf c' w' h1 h2
    rw [hR2.2.1 _ _ _ (hc f hf) h1, hVu _ _ _ (hw f hf) h2]
  let Φ : quasiLog p h →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] V :=
    { toFun := fun f => ρ (c f.1 f.2, w f.1 f.2)
      map_add' := fun f g => by
        rw [key (f + g).1 (f + g).2 (c f.1 f.2 + c g.1 g.2) (w f.1 f.2 + w g.1 g.2), ← map_add,
          Prod.mk_add_mk]
        · rw [Submodule.coe_add, formalCoboundary_add hμ']
          exact (hR2.2.2.2.1 _ _ _ _ (hc _ _) (hc _ _)).1
        · rw [Submodule.coe_add, hlinadd]
          exact hVa _ _ _ _ (hw _ _) (hw _ _)
      map_smul' := fun r f => by
        rw [key (r • f).1 (r • f).2 (WittVector.constantCoeff r • c f.1 f.2)
          (WittVector.constantCoeff r • w f.1 f.2), ← map_smul, Prod.smul_mk]
        · rw [Submodule.coe_smul, hcobs]
          exact hR2.2.2.2.2.1 _ _ _ (hc _ _)
        · rw [Submodule.coe_smul, hlinsmul]
          exact hVs _ _ _ (hw _ _) }
  have hΦ : ∀ f : quasiLog p h, Φ f = ρ (c f.1 f.2, w f.1 f.2) := fun _ => rfl
  have hker : (intBy p k (Fin d) 1).submoduleOf (quasiLog p h) ≤ LinearMap.ker Φ := by
    intro f hf
    rw [LinearMap.mem_ker, hΦ]
    have hf' : (f : MvPowerSeries (Fin d) (Fr p k)) ∈ intBy p k (Fin d) 1 := hf
    obtain ⟨b, hb⟩ := (hR1.1 _).1 hf'
    obtain ⟨h1, h2⟩ := hC.2.1 _ _ hb
    rw [key _ _ _ _ h1 h2]
    exact ((hρ.ker _ _ (hD.2 _ f.2 _ h1)).2 ⟨b, rfl, rfl⟩)
  refine ⟨Submodule.liftQ _ Φ hker, ?_, ?_, ?_⟩
  · intro f c' w' h1 h2
    rw [Submodule.liftQ_apply, hΦ, key _ _ _ _ h1 h2]
  · intro v
    obtain ⟨c', w', hcoc, rfl⟩ := hρ.surj v
    obtain ⟨f, hf, h1, h2⟩ := hS c' hcoc w'
    exact ⟨Submodule.Quotient.mk ⟨f, hf⟩, by rw [Submodule.liftQ_apply, hΦ, key _ _ _ _ h1 h2]⟩
  · intro m
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [Submodule.liftQ_apply, hΦ]
    constructor
    · intro h0
      obtain ⟨b, hb1, hb2⟩ := (hρ.ker _ _ (hD.2 _ f.2 _ (hc f.1 f.2))).1 h0
      have h1 := hc f.1 f.2
      have h2 := hw f.1 f.2
      rw [hb1] at h1
      rw [hb2] at h2
      obtain ⟨g, hg, hfg⟩ := hK f.1 f.2 b h1 h2
      refine ⟨Submodule.Quotient.mk ⟨g, hg⟩, ?_⟩
      rw [← Nat.cast_smul_eq_nsmul (WittVector p k), ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.eq]
      exact hfg
    · rintro ⟨n, hn⟩
      have : Φ f = Submodule.liftQ _ Φ hker (p • n) := by
        rw [← hn, Submodule.liftQ_apply]
      rw [← hΦ, this, map_nsmul, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]

end GlobalTheory
