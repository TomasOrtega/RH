import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeComp

/- English proof (translation)
Take `⟨n, hn⟩` from `GlobalTheory.Mem.UnrAe.exists_levelLe χ w`. Establish `hu` using `unif_spec w`. Use `set c : w.adicCompletion E := ((atFin w (unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) ^ (n + 1) with hc`. Establish `hv : Valued.v c = WithZero.exp (-((n : ℤ) + 1))`. Unfold `IsUnifAt at hu`.

Rewrite using `[hc, map_pow, hu, ← WithZero.exp_nsmul]`. Use `congr 1`. Simplify using the standard rewrite rules. Establish `ho : IsOpen {x : (w.adicCompletion E)ˣ | ((x : w.adicCompletion E) - 1) * c⁻¹ ∈ w.adicCompletionIntegers E}` using `(Valued.isOpen_valuationSubring _).preimage ((Units.continuous_val.sub continuous_const).mul continuous_const)`. Use `Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (ho.mem_nhds (by simp)) fun x hx => ?_)` and prove the remaining obligations.

Establish `h1 : Valued.v (((x : w.adicCompletion E) - 1) * c⁻¹) ≤ 1` using `hx`. Rewrite `h1` using `[map_mul, map_inv₀, hv, mul_inv_le_iff₀ WithZero.exp_pos, one_mul]`. Establish `h2 : Valued.v ((x : w.adicCompletion E) - 1) < 1` using `h1.trans_lt (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)`. Use `hn x ?_ (h1.trans (WithZero.exp_le_exp.2 (by omega)))` and prove the remaining obligations. Use `Valuation.map_one_add_of_lt _ h2` as an intermediate fact.

Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem smooth_loc {E : Type} [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) :
    GlobalTheory.SmGL.IsSmoothChar (χ.loc w) := by
  obtain ⟨n, hn⟩ := GlobalTheory.Mem.UnrAe.exists_levelLe χ w
  have hu := unif_spec w
  set c : w.adicCompletion E := ((atFin w (unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) ^ (n + 1) with hc
  have hv : Valued.v c = WithZero.exp (-((n : ℤ) + 1)) := by
    unfold IsUnifAt at hu
    rw [hc, map_pow, hu, ← WithZero.exp_nsmul]; congr 1; simp
  have ho : IsOpen {x : (w.adicCompletion E)ˣ | ((x : w.adicCompletion E) - 1) * c⁻¹ ∈ w.adicCompletionIntegers E} :=
    (Valued.isOpen_valuationSubring _).preimage ((Units.continuous_val.sub continuous_const).mul continuous_const)
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (ho.mem_nhds (by simp)) fun x hx => ?_)
  have h1 : Valued.v (((x : w.adicCompletion E) - 1) * c⁻¹) ≤ 1 := hx
  rw [map_mul, map_inv₀, hv, mul_inv_le_iff₀ WithZero.exp_pos, one_mul] at h1
  have h2 : Valued.v ((x : w.adicCompletion E) - 1) < 1 :=
    h1.trans_lt (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  refine hn x ?_ (h1.trans (WithZero.exp_le_exp.2 (by omega)))
  have := Valuation.map_one_add_of_lt _ h2
  rwa [add_sub_cancel] at this

/- English proof (translation)
Establish `hs` using `hξ'.1.mul hξ.1.inv`. Establish `hc` using `Subgroup.isClosed_of_isOpen _ hs`. Use `mul_inv_eq_one.1 (MonoidHom.ext fun y => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `hy`. Take `⟨U, hU, hU'⟩` from `Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hc.isOpen_compl`.

Establish `hyU : (y : w.adicCompletion E) ∈ U`. Establish `: y ∈ Units.val ⁻¹' U` using `by rw [hU']; exact hy`. Conclude with `this`. Take `⟨k, hk1, hk2⟩` from `(HeightOneSpectrum.denseRange_algebraMap E w).exists_mem_open (hU.inter isOpen_ne (t := {z | z ≠ 0})) ⟨y, hyU, y.ne_zero⟩`. Establish `hk0 : k ≠ 0` using `fun e => hk2 (by rw [e, map_zero])`.

Establish `h3 : Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom (Units.mk0 k hk0) ∈ Units.val ⁻¹' U` using `hk1`. Rewrite `h3` using `[hU']`. Use `h3 ?_` and prove the remaining obligations. Use `show ξ' _ * (ξ _)⁻¹ = 1`. Rewrite using `[hξ.2, hξ'.2]`.

Conclude with `mul_inv_cancel _`.
-/
theorem eq_of_isComp {E : Type} [Field E] [NumberField E] {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    {ξ ξ' : (w.adicCompletion E)ˣ →* ℂˣ} (hξ : IsComp χ w ξ) (hξ' : IsComp χ w ξ') : ξ' = ξ := by
  have hs := hξ'.1.mul hξ.1.inv
  have hc := Subgroup.isClosed_of_isOpen _ hs
  refine mul_inv_eq_one.1 (MonoidHom.ext fun y => ?_)
  by_contra hy
  obtain ⟨U, hU, hU'⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hc.isOpen_compl
  have hyU : (y : w.adicCompletion E) ∈ U := by
    have : y ∈ Units.val ⁻¹' U := by rw [hU']; exact hy
    exact this
  obtain ⟨k, hk1, hk2⟩ := (HeightOneSpectrum.denseRange_algebraMap E w).exists_mem_open
    (hU.inter isOpen_ne (t := {z | z ≠ 0})) ⟨y, hyU, y.ne_zero⟩
  have hk0 : k ≠ 0 := fun e => hk2 (by rw [e, map_zero])
  have h3 : Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom (Units.mk0 k hk0) ∈ Units.val ⁻¹' U := hk1
  rw [hU'] at h3
  refine h3 ?_
  show ξ' _ * (ξ _)⁻¹ = 1
  rw [hξ.2, hξ'.2]
  exact mul_inv_cancel _

/- English proof (translation)
Introduce `E _ _ χ w`. Establish `hc : IsComp χ w (χ.loc w)` using `⟨smooth_loc χ w, fun _ => rfl⟩`. Conclude with `⟨χ.loc w, hc, fun ξ' h' => eq_of_isComp hc h', fun hu x => hu _⟩`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)), ∃ ξ, IsComp χ w ξ ∧ (∀ ξ', IsComp χ w ξ' → ξ' = ξ) ∧ (χ.IsUnitary → ∀ x, ‖((ξ x : ℂˣ) : ℂ)‖ = 1) := by
  intro E _ _ χ w
  have hc : IsComp χ w (χ.loc w) := ⟨smooth_loc χ w, fun _ => rfl⟩
  exact ⟨χ.loc w, hc, fun ξ' h' => eq_of_isComp hc h', fun hu x => hu _⟩

end GlobalTheory.HeckeComp
