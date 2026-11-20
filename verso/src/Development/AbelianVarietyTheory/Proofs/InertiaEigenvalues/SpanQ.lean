import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalTwoCocycleOfLocalTateDualityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousTwoCocycleMultipleOfFundamentalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanCyclotomicTwoCocyclesFiniteExtensionStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.InvLine

/- English proof (translation)
Introduce `hT l _ P K`. Take `⟨hcpt, χ, c, hχc, hχ, hgen, hfin⟩` from `GlobalTheory.T.exists_fundamentalTwoCocycle_of_localTateDuality hT l P K`. Take `⟨⟨hcc, hcoc⟩, hsp⟩` from `GlobalTheory.T.continuous_twoCocycle_multiple_of_fundamental l ↥(GK K) χ c hχc hgen hfin`. Establish `hcyc : ∀ g, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) = ((χ g : ℤ_[l]) : ℚ_[l])` using `fun g => by`. Rewrite using `[hχ]`.

Both sides reduce to the same expression. Use `⟨fun p => (c p : ℚ_[l]), ⟨hcc, fun g h k => by rw [hcyc]; exact hcoc g h k⟩, fun z hz hzc => ?_⟩` and prove the remaining obligations. Take `⟨x, f, hf, hfd⟩` from `hsp z hz (fun g h k => by rw [← hcyc]; exact hzc g h k)`. Use `⟨x, f, hf, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`.

Take `⟨g, h⟩` from `p`. Establish `e` using `hfd g h`. Rewrite `e` using `[← hcyc]`. Simplify using `only [ReciprocityTheory.Def.d1, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← e]`.

Simplify using `[charRep]`.
-/
theorem spanQ : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), ∃ z0 : ↥(GK K) × ↥(GK K) → ℚ_[l], (Continuous z0 ∧ ∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧ ∀ z : ↥(GK K) × ↥(GK K) → ℚ_[l], Continuous z → (∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ x : ℚ_[l], CobL (P.PD K) (z - x • z0) := by
  intro hT l _ P K
  obtain ⟨hcpt, χ, c, hχc, hχ, hgen, hfin⟩ := GlobalTheory.T.exists_fundamentalTwoCocycle_of_localTateDuality hT l P K
  obtain ⟨⟨hcc, hcoc⟩, hsp⟩ := GlobalTheory.T.continuous_twoCocycle_multiple_of_fundamental l ↥(GK K) χ c hχc hgen hfin
  have hcyc : ∀ g, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) = ((χ g : ℤ_[l]) : ℚ_[l]) := fun g => by
    rw [hχ]; rfl
  refine ⟨fun p => (c p : ℚ_[l]), ⟨hcc, fun g h k => by rw [hcyc]; exact hcoc g h k⟩, fun z hz hzc => ?_⟩
  obtain ⟨x, f, hf, hfd⟩ := hsp z hz (fun g h k => by rw [← hcyc]; exact hzc g h k)
  refine ⟨x, f, hf, ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  have e := hfd g h
  rw [← hcyc] at e
  simp only [ReciprocityTheory.Def.d1, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← e]
  simp [charRep]

/- English proof (translation)
Introduce `hT l _ P K LL _ _ _ O _ _ hO`. Take `⟨z0, ⟨hz0c, hz0⟩, hspan⟩` from `GlobalTheory.T.span_cyclotomic_twoCocycles_finite_extension l P K LL O hO (spanQ hT l P K)`. Establish `htr : IsTopologicalRing LL` using `hO.2.2.2.1`. Set `Z : Submodule LL (↥(GK K) × ↥(GK K) → LL)` to `{ carrier := {z | Continuous z ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0} add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun g h k => by`. Establish `e1` using `ha.2 g h k`.

Establish `e2` using `hb.2 g h k`. Simplify using `only [Pi.add_apply]`. Take the linear combination `e1 + e2⟩`. Use the proof step `zero_mem' := ⟨continuous_const, fun g h k => by simp⟩`. Use the proof step `smul_mem' := fun c a ha => ⟨ha.1.const_smul c, fun g h k => by`.

Establish `e1` using `ha.2 g h k`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Take the linear combination `c * e1⟩ }`. Establish `hZ : ∀ z, z ∈ Z ↔ Continuous z ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0` using `fun z => Iff.rfl`. Set `B : Submodule LL ↥Z` to `{ carrier := {z | CobL (P.PD K) z.1} add_mem' := fun {a b} ha hb => by`.

Take `⟨f1, hf1, e1⟩` from `ha`. Take `⟨f2, hf2, e2⟩` from `hb`. Conclude with `⟨f1 + f2, hf1.add hf2, by rw [map_add, e1, e2]; rfl⟩`. Use the proof step `zero_mem' := ⟨0, continuous_const, by rw [map_zero]; rfl⟩`. Use the proof step `smul_mem' := fun c a ha => by`.

Take `⟨f1, hf1, e1⟩` from `ha`. Conclude with `⟨c • f1, hf1.const_smul c, by rw [map_smul, e1]; rfl⟩ }`. Establish `hB : ∀ z : ↥Z, z ∈ B ↔ CobL (P.PD K) z.1` using `fun z => Iff.rfl`. Set `z0' : ↥Z` to `⟨z0, hz0c, hz0⟩`. Establish `hQ : ∀ z : ↥Z, ∃ x : LL, B.mkQ z = x • B.mkQ z0'`.

Introduce `z`. Take `⟨x, hx⟩` from `hspan z.1 z.2.1 z.2.2`. Use `⟨x, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `hx`.

Use `⟨Z, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h0 : B.mkQ z0' = 0`. Use `⟨0, hZ, fun z => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `hQ z`. Rewrite `hx` using `[h0, smul_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`.

Simplify using `only [LinearMap.zero_apply, true_iff]`. Conclude with `hx`. Establish `htop : Submodule.span LL {B.mkQ z0'} = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `q _`.

Take `⟨z, rfl⟩` from `B.mkQ_surjective q`. Take `⟨x, hx⟩` from `hQ z`. Rewrite using `[hx]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span rfl)`. Set `φ` to `LinearEquiv.toSpanNonzeroSingleton LL _ _ h0`.

Set `inv : ↥Z →ₗ[LL] LL` to `(φ.symm.toLinearMap.comp (LinearEquiv.ofTop _ htop).symm.toLinearMap).comp B.mkQ`. Establish `hinj : Function.Injective (φ.symm.toLinearMap.comp (LinearEquiv.ofTop _ htop).symm.toLinearMap)` using `φ.symm.injective.comp (LinearEquiv.ofTop _ htop).symm.injective`. Use `⟨inv, hZ, fun z => ?_⟩` and prove the remaining obligations. Establish `e1 : inv z = 0 ↔ B.mkQ z = 0` using `(injective_iff_map_eq_zero' _).1 hinj (B.mkQ z)`. Rewrite using `[e1, ← hB, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`.
-/
theorem exists_inv : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∃ (Z : Submodule LL (↥(GK K) × ↥(GK K) → LL)) (inv : ↥Z →ₗ[LL] LL), (∀ z, z ∈ Z ↔ Continuous z ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) ∧ ∀ z : ↥Z, inv z = 0 ↔ CobL (P.PD K) z.1 := by
  intro hT l _ P K LL _ _ _ O _ _ hO
  obtain ⟨z0, ⟨hz0c, hz0⟩, hspan⟩ := GlobalTheory.T.span_cyclotomic_twoCocycles_finite_extension l P K LL O hO (spanQ hT l P K)
  have htr : IsTopologicalRing LL := hO.2.2.2.1
  let Z : Submodule LL (↥(GK K) × ↥(GK K) → LL) :=
    { carrier := {z | Continuous z ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0}
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun g h k => by
        have e1 := ha.2 g h k
        have e2 := hb.2 g h k
        simp only [Pi.add_apply]
        linear_combination e1 + e2⟩
      zero_mem' := ⟨continuous_const, fun g h k => by simp⟩
      smul_mem' := fun c a ha => ⟨ha.1.const_smul c, fun g h k => by
        have e1 := ha.2 g h k
        simp only [Pi.smul_apply, smul_eq_mul]
        linear_combination c * e1⟩ }
  have hZ : ∀ z, z ∈ Z ↔ Continuous z ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0 := fun z => Iff.rfl
  let B : Submodule LL ↥Z :=
    { carrier := {z | CobL (P.PD K) z.1}
      add_mem' := fun {a b} ha hb => by
        obtain ⟨f1, hf1, e1⟩ := ha
        obtain ⟨f2, hf2, e2⟩ := hb
        exact ⟨f1 + f2, hf1.add hf2, by rw [map_add, e1, e2]; rfl⟩
      zero_mem' := ⟨0, continuous_const, by rw [map_zero]; rfl⟩
      smul_mem' := fun c a ha => by
        obtain ⟨f1, hf1, e1⟩ := ha
        exact ⟨c • f1, hf1.const_smul c, by rw [map_smul, e1]; rfl⟩ }
  have hB : ∀ z : ↥Z, z ∈ B ↔ CobL (P.PD K) z.1 := fun z => Iff.rfl
  let z0' : ↥Z := ⟨z0, hz0c, hz0⟩
  have hQ : ∀ z : ↥Z, ∃ x : LL, B.mkQ z = x • B.mkQ z0' := by
    intro z
    obtain ⟨x, hx⟩ := hspan z.1 z.2.1 z.2.2
    refine ⟨x, ?_⟩
    rw [← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hx
  refine ⟨Z, ?_⟩
  by_cases h0 : B.mkQ z0' = 0
  · refine ⟨0, hZ, fun z => ?_⟩
    obtain ⟨x, hx⟩ := hQ z
    rw [h0, smul_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    simp only [LinearMap.zero_apply, true_iff]
    exact hx
  · have htop : Submodule.span LL {B.mkQ z0'} = ⊤ := by
      rw [eq_top_iff]
      intro q _
      obtain ⟨z, rfl⟩ := B.mkQ_surjective q
      obtain ⟨x, hx⟩ := hQ z
      rw [hx]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    let φ := LinearEquiv.toSpanNonzeroSingleton LL _ _ h0
    let inv : ↥Z →ₗ[LL] LL :=
      (φ.symm.toLinearMap.comp (LinearEquiv.ofTop _ htop).symm.toLinearMap).comp B.mkQ
    have hinj : Function.Injective (φ.symm.toLinearMap.comp (LinearEquiv.ofTop _ htop).symm.toLinearMap) :=
      φ.symm.injective.comp (LinearEquiv.ofTop _ htop).symm.injective
    refine ⟨inv, hZ, fun z => ?_⟩
    have e1 : inv z = 0 ↔ B.mkQ z = 0 :=
      (injective_iff_map_eq_zero' _).1 hinj (B.mkQ z)
    rw [e1, ← hB, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

end GlobalTheory.InvLine
