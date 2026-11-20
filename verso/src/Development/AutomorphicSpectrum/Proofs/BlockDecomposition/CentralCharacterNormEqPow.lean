import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterExistsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealExponentAbsSmoothCharacterLocalField
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.CentralExp

/- English proof (translation)
Establish `hs : Continuous (fun a : k => Matrix.scalar (Fin n) a)`. Establish `: (fun a : k => Matrix.scalar (Fin n) a) = fun a => Matrix.diagonal (fun _ => a)`. Use function extensionality and compare the values at `a`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `Continuous.matrix_diagonal (continuous_pi fun _ => continuous_id)`. Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `hs.comp Units.continuous_val`. Conclude with `hs.comp (Units.continuous_val.comp continuous_inv)`.
-/
theorem continuous_scalarGL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) :
    Continuous (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ →* GL (Fin n) k) := by
  have hs : Continuous (fun a : k => Matrix.scalar (Fin n) a) := by
    have : (fun a : k => Matrix.scalar (Fin n) a) = fun a => Matrix.diagonal (fun _ => a) := by
      funext a; rfl
    rw [this]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => continuous_id)
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact hs.comp Units.continuous_val
  · exact hs.comp (Units.continuous_val.comp continuous_inv)

/- English proof (translation)
Introduce `k _ _ _ _ x hx`. Establish `hirr` using `x.2.rep.irr`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v : x.2.rep.V, v ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Use `haveI : Subsingleton x.2.rep.V := ⟨fun a b => by rw [hcon a, hcon b]⟩`. Take `⟨a, b, hab⟩` from `exists_pair_ne (Subrepresentation x.rep)`. Conclude with `hab (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))`. Establish `huniq : ∀ (t : kˣ) (c c' : ℂ), Zl.ScalarBy x t c → Zl.ScalarBy x t c' → c = c'`. Introduce `t c c' h h'`.

Conclude with `smul_left_injective ℂ hv ((h v).symm.trans (h' v))`. Use `choose f hf using GlobalTheory.T.central_character_exists k x`. Establish `hmul : ∀ a b : kˣ, f (a * b) = f a * f b`. Introduce `a b`. Use `huniq (a * b) _ _ (hf _) fun w => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_mul, Module.End.mul_apply, hf b w, map_smul, hf a w, smul_smul, mul_comm]`. Establish `hone : f 1 = 1`. Use `huniq 1 _ _ (hf _) fun w => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Set `χ₀ : kˣ →* ℂ` to `{ toFun := f, map_one' := hone, map_mul' := hmul }`.

Set `χ : kˣ →* ℂˣ` to `χ₀.toHomUnits`. Establish `hχ : ∀ t, ((χ t : ℂˣ) : ℂ) = f t` using `fun t => rfl`. Establish `hsm : IsSmoothChar χ`. Establish `hset : (χ.ker : Set kˣ) = (Matrix.GeneralLinearGroup.scalar (Fin x.1) : kˣ →* GL (Fin x.1) k) ⁻¹' {g | x.rep g v = v}`. Use extensionality with `t`.

Simplify using `only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_setOf_eq]`. Rewrite using `[hf t v]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `: f t = 1` using `by rw [← hχ, h]; rfl`.

Rewrite using `[this, one_smul]`. Introduce `h`. Establish `: f t = 1` using `smul_left_injective ℂ hv (by simpa using h)`. Conclude with `Units.ext (by rw [hχ, this]; rfl)`. Use `show IsOpen (χ.ker : Set kˣ)`.

Rewrite using `[hset]`. Conclude with `(x.2.rep.smooth v).preimage (continuous_scalarGL k x.1)`. Take `⟨s, hs⟩` from `GlobalTheory.SmoothCharNorm.norm_eq_nabs_rpow k χ hsm`. Establish `hn : (x.1 : ℝ) ≠ 0` using `by exact_mod_cast hx.ne'`. Use `⟨s / x.1, fun t c hc => ?_⟩` and prove the remaining obligations.

Rewrite using `[huniq t c (f t) hc (hf t), ← hχ, hs t, mul_div_cancel₀ _ hn]`.
-/
theorem norm_scalarBy_eq_nabs_rpow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL k), 0 < x.1 → ∃ s : ℝ, ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy x t c → ‖c‖ = nabs k t ^ ((x.1 : ℝ) * s) := by
  intro k _ _ _ _ x hx
  have hirr := x.2.rep.irr
  obtain ⟨v, hv⟩ : ∃ v : x.2.rep.V, v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    haveI : Subsingleton x.2.rep.V := ⟨fun a b => by rw [hcon a, hcon b]⟩
    obtain ⟨a, b, hab⟩ := exists_pair_ne (Subrepresentation x.rep)
    exact hab (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  have huniq : ∀ (t : kˣ) (c c' : ℂ), Zl.ScalarBy x t c → Zl.ScalarBy x t c' → c = c' := by
    intro t c c' h h'
    exact smul_left_injective ℂ hv ((h v).symm.trans (h' v))
  choose f hf using GlobalTheory.T.central_character_exists k x
  have hmul : ∀ a b : kˣ, f (a * b) = f a * f b := by
    intro a b
    refine huniq (a * b) _ _ (hf _) fun w => ?_
    rw [map_mul, map_mul, Module.End.mul_apply, hf b w, map_smul, hf a w, smul_smul, mul_comm]
  have hone : f 1 = 1 := by
    refine huniq 1 _ _ (hf _) fun w => ?_
    simp
  let χ₀ : kˣ →* ℂ := { toFun := f, map_one' := hone, map_mul' := hmul }
  let χ : kˣ →* ℂˣ := χ₀.toHomUnits
  have hχ : ∀ t, ((χ t : ℂˣ) : ℂ) = f t := fun t => rfl
  have hsm : IsSmoothChar χ := by
    have hset : (χ.ker : Set kˣ) = (Matrix.GeneralLinearGroup.scalar (Fin x.1) : kˣ →* GL (Fin x.1) k) ⁻¹'
        {g | x.rep g v = v} := by
      ext t
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_setOf_eq]
      rw [hf t v]
      constructor
      · intro h
        have : f t = 1 := by rw [← hχ, h]; rfl
        rw [this, one_smul]
      · intro h
        have : f t = 1 := smul_left_injective ℂ hv (by simpa using h)
        exact Units.ext (by rw [hχ, this]; rfl)
    show IsOpen (χ.ker : Set kˣ)
    rw [hset]
    exact (x.2.rep.smooth v).preimage (continuous_scalarGL k x.1)
  obtain ⟨s, hs⟩ := GlobalTheory.SmoothCharNorm.norm_eq_nabs_rpow k χ hsm
  have hn : (x.1 : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
  refine ⟨s / x.1, fun t c hc => ?_⟩
  rw [huniq t c (f t) hc (hf t), ← hχ, hs t, mul_div_cancel₀ _ hn]

end GlobalTheory.CompanionTheory.CentralExp
