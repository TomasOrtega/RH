import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Introduce `hIn hli hsp hb`. Set `B : Module.Basis ι R M` to `Module.Basis.mk hli (by rw [hsp])`. Set `ν : Module.End R M` to `B.constr R (fun i => b' i - b i)`. Establish `hν : ∀ i, ν (b i) = b' i - b i`. Introduce `i`.

Use `B.constr_basis R (fun i => b' i - b i) i` as an intermediate fact. Simplify `this` using `[B, Module.Basis.mk_apply]`. Establish `hrange : LinearMap.range ν ≤ I • (⊤ : Submodule R M)`. Establish `e : LinearMap.range ν = Submodule.map ν (Submodule.span R (Set.range b))`. Rewrite using `[hsp, LinearMap.range_eq_map]`.

Rewrite using `[e, Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨i, rfl⟩, rfl⟩`. Use `show ν (b i) ∈ _`. Rewrite using `[hν]`. Conclude with `hb i`.

Establish `hpow : ∀ k : ℕ, LinearMap.range (ν ^ k) ≤ I ^ k • (⊤ : Submodule R M)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`.

Rewrite using `[pow_succ', Module.End.mul_eq_comp, LinearMap.range_comp]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `Submodule.smul_mono le_rfl (by rw [← LinearMap.range_eq_map]; exact hrange)`. Use `_ = I ^ (k + 1) • (⊤ : Submodule R M) := by`. Rewrite using `[pow_succ, Submodule.mul_smul]`.

Establish `hnil : IsNilpotent ν`. Use `⟨n, ?_⟩` and prove the remaining obligations. Use `hpow n` as an intermediate fact. Rewrite `this` using `[hIn, Submodule.bot_smul, le_bot_iff, LinearMap.range_eq_bot]`. Conclude with `this`.

Establish `hunit : IsUnit (1 + ν)` using `hnil.isUnit_one_add`. Establish `hbij : Function.Bijective ⇑(1 + ν)` using `(Module.End.isUnit_iff _).1 hunit`. Establish `hcomp : b' = ⇑(1 + ν) ∘ b`. Use function extensionality and compare the values at `i`. Simplify using `[hν]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hcomp]`. Conclude with `hli.map' (1 + ν) (LinearMap.ker_eq_bot.2 hbij.1)`. Rewrite using `[hcomp, Set.range_comp, ← Submodule.map_span, hsp, ← LinearMap.range_eq_map, LinearMap.range_eq_top.2 hbij.2]`.
-/
theorem family_congr_basis_mod_nilpotent (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (ι : Type) (b b' : ι → M) (I : Ideal R) (n : ℕ) :
    I ^ n = ⊥ → LinearIndependent R b → Submodule.span R (Set.range b) = ⊤ →
    (∀ k, b' k - b k ∈ I • (⊤ : Submodule R M)) →
    LinearIndependent R b' ∧ Submodule.span R (Set.range b') = ⊤ := by
  intro hIn hli hsp hb
  let B : Module.Basis ι R M := Module.Basis.mk hli (by rw [hsp])
  let ν : Module.End R M := B.constr R (fun i => b' i - b i)
  have hν : ∀ i, ν (b i) = b' i - b i := by
    intro i
    have := B.constr_basis R (fun i => b' i - b i) i
    simpa [B, Module.Basis.mk_apply] using this
  have hrange : LinearMap.range ν ≤ I • (⊤ : Submodule R M) := by
    have e : LinearMap.range ν = Submodule.map ν (Submodule.span R (Set.range b)) := by
      rw [hsp, LinearMap.range_eq_map]
    rw [e, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    show ν (b i) ∈ _
    rw [hν]; exact hb i
  have hpow : ∀ k : ℕ, LinearMap.range (ν ^ k) ≤ I ^ k • (⊤ : Submodule R M) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.range_comp]
      calc Submodule.map ν (LinearMap.range (ν ^ k))
          ≤ Submodule.map ν (I ^ k • (⊤ : Submodule R M)) := Submodule.map_mono ih
        _ = I ^ k • Submodule.map ν ⊤ := Submodule.map_smul'' _ _ _
        _ ≤ I ^ k • (I • (⊤ : Submodule R M)) := by
            exact Submodule.smul_mono le_rfl (by rw [← LinearMap.range_eq_map]; exact hrange)
        _ = I ^ (k + 1) • (⊤ : Submodule R M) := by
            rw [pow_succ, Submodule.mul_smul]
  have hnil : IsNilpotent ν := by
    refine ⟨n, ?_⟩
    have := hpow n
    rw [hIn, Submodule.bot_smul, le_bot_iff, LinearMap.range_eq_bot] at this
    exact this
  have hunit : IsUnit (1 + ν) := hnil.isUnit_one_add
  have hbij : Function.Bijective ⇑(1 + ν) := (Module.End.isUnit_iff _).1 hunit
  have hcomp : b' = ⇑(1 + ν) ∘ b := by
    funext i; simp [hν]
  refine ⟨?_, ?_⟩
  · rw [hcomp]
    exact hli.map' (1 + ν) (LinearMap.ker_eq_bot.2 hbij.1)
  · rw [hcomp, Set.range_comp, ← Submodule.map_span, hsp, ← LinearMap.range_eq_map,
      LinearMap.range_eq_top.2 hbij.2]

end GlobalTheory.BSP
