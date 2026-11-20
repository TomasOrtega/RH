import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.IrrTI
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.FreeEtaleSheafZmodExistsHomSendingGenerator
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.DerExt

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

/- English proof (translation)
Introduce `l _ c _ F C₀ n hF hn S ξ hI hT hX`. Establish `hirr` using `irrTI l c F C₀ n hF hn S ξ hI hT`. Establish `key : ∀ D ∈ FixTan S ξ, ∃ t : Qbar l, (∀ (g : F.G0) (i j : Fin n), D (S.u.r g i j) = t * ↑(Fr.w n i - Fr.w n j) * ξ (S.u.r g i j)) ∧ ∀ (v : F.V) (i : Fin n) (g : F.Gv v), D ↑((S.u.ψ v i) g) = 0`. Introduce `D hD`. Take `⟨X, hXD⟩` from `hX D hD`.

Conclude with `torus l c F C₀ n hF hn S ξ hI D hD.1 hirr X hXD`. Distinguish the cases in `h0 : ∀ D ∈ FixTan S ξ, D = 0`. Establish `hbot : FixTan S ξ = ⊥` using `eq_bot_iff.2 fun D hD => (Submodule.mem_bot _).2 (h0 D hD)`. Rewrite using `[hbot]`. Simplify using the standard rewrite rules.

Use `push_neg at h0`. Take `⟨D1, hD1, hne⟩` from `h0`. Take `⟨t1, h1r, h1ψ⟩` from `key D1 hD1`. Establish `ht1 : t1 ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hne (derExt l c F C₀ n hF hn S ξ D1 hD1.1 (fun g i j => by simp [h1r]) h1ψ)`. Use `haveI : Module.Free (Qbar l) (FixTan S ξ) := Module.Free.of_divisionRing _ _`. Use `(rank_submodule_le_one_iff _).2 ⟨D1, hD1, fun D hD => ?_⟩` and prove the remaining obligations. Take `⟨t, hr, hψ⟩` from `key D hD`. Establish `hE : t1 • D - t • D1 = 0` using `derExt l c F C₀ n hF hn S ξ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hD.1) (Submodule.smul_mem _ _ hD1.1)) (fun g i j => by`.

Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hr, h1r]`. Use the proof step `ring)`. Use the proof step `(fun v i g => by simp [hψ, h1ψ])`. Rewrite using `[Submodule.mem_span_singleton]`. Use `⟨t1⁻¹ * t, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_smul, ← sub_eq_zero.1 hE, smul_smul, inv_mul_cancel₀ ht1, one_smul]`.
-/
theorem UpperTheory.V.J.fixLe :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ ξ : S.A →ₐ[c.O] Qbar l, IntPt S ξ → S.u.TI (RingHom.ker ξ) →
          (∀ D ∈ FixTan S ξ, ∃ X : Matrix (Fin n) (Fin n) (Qbar l), ∀ g, (S.u.r g).map D = X * (ptRep S ξ).r g - (ptRep S ξ).r g * X) →
          Module.rank (Qbar l) (FixTan S ξ) ≤ 1 := by
  intro l _ c _ F C₀ n hF hn S ξ hI hT hX
  have hirr := irrTI l c F C₀ n hF hn S ξ hI hT
  have key : ∀ D ∈ FixTan S ξ, ∃ t : Qbar l,
      (∀ (g : F.G0) (i j : Fin n), D (S.u.r g i j) = t * ↑(Fr.w n i - Fr.w n j) * ξ (S.u.r g i j)) ∧
      ∀ (v : F.V) (i : Fin n) (g : F.Gv v), D ↑((S.u.ψ v i) g) = 0 := by
    intro D hD
    obtain ⟨X, hXD⟩ := hX D hD
    exact torus l c F C₀ n hF hn S ξ hI D hD.1 hirr X hXD
  by_cases h0 : ∀ D ∈ FixTan S ξ, D = 0
  · have hbot : FixTan S ξ = ⊥ := eq_bot_iff.2 fun D hD => (Submodule.mem_bot _).2 (h0 D hD)
    rw [hbot]
    simp
  push_neg at h0
  obtain ⟨D1, hD1, hne⟩ := h0
  obtain ⟨t1, h1r, h1ψ⟩ := key D1 hD1
  have ht1 : t1 ≠ 0 := by
    rintro rfl
    exact hne (derExt l c F C₀ n hF hn S ξ D1 hD1.1 (fun g i j => by simp [h1r]) h1ψ)
  haveI : Module.Free (Qbar l) (FixTan S ξ) := Module.Free.of_divisionRing _ _
  refine (rank_submodule_le_one_iff _).2 ⟨D1, hD1, fun D hD => ?_⟩
  obtain ⟨t, hr, hψ⟩ := key D hD
  have hE : t1 • D - t • D1 = 0 :=
    derExt l c F C₀ n hF hn S ξ _
      (Submodule.sub_mem _ (Submodule.smul_mem _ _ hD.1) (Submodule.smul_mem _ _ hD1.1))
      (fun g i j => by
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hr, h1r]
        ring)
      (fun v i g => by simp [hψ, h1ψ])
  rw [Submodule.mem_span_singleton]
  refine ⟨t1⁻¹ * t, ?_⟩
  rw [mul_smul, ← sub_eq_zero.1 hE, smul_smul, inv_mul_cancel₀ ht1, one_smul]
