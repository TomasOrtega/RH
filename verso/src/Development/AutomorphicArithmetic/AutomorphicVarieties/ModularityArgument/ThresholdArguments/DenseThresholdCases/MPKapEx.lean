import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.PKapEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.KapEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TTwist

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix
namespace UpperTheory.V.Cu2
namespace KapEx
end KapEx
open UpperTheory.V.Cu2.KapEx in
/- English proof (translation)
Introduce `hP Ω _ _ _ l _ ι K' _ hl2 hK2 hTC hld hsp hcc`. Take `⟨cc, hcc⟩` from `hcc`. Establish `: IsTotallyComplex K'` using `hTC`. Establish `: IsAlgClosure K' Ω` using `⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K'⟩`. Establish `: IsGalois ℚ Ω` using `IsAlgClosure.isGalois ℚ Ω`.

Establish `: IsGalois K' Ω` using `IsGalois.tower_top_of_isGalois ℚ K' Ω`. Establish `: CompactSpace (G K' Ω)` using `inferInstanceAs (CompactSpace (Ω ≃ₐ[K'] Ω))`. Take `⟨κ₀, htw⟩` from `_root_.UpperTheory.V.Sd.twist_of_printed_results hP K' Ω hK2 l hl2 hld ι cc hcc`. Take `⟨art, Y, a, τ, hart, hYa, hL, ha1, ha0, -⟩` from `htw.alg`. Take `⟨mo, hmo0, -, hmo⟩` from `htw.ord`.

Establish `hi : (galOf ℚ K' Ω).index = 2` using `(galEmbTop ℚ K' Ω).2.2.trans hK2`. Establish `hccK : cc ∉ galOf ℚ K' Ω` using `cc_notMem K' hcc`. Establish `hfix : ∀ t : G ℚ Ω, t ∈ K'.fixingSubgroup → t ∈ galOf ℚ K' Ω` using `fun t h => (mem_galOf ℚ K' Ω).2 fun x => (IntermediateField.mem_fixingSubgroup_iff K' t).1 h x x.2`. Establish `hIne : ∀ (A : ValuationSubring Ω) (h : G K' Ω), resQ K' h ∈ Ine (F` using `ℚ) A → h ∈ Ine (F := K') A := fun A h hh => ⟨hh.1, hh.2⟩`. Establish `hεc : Continuous (cycBar K' Ω l)`.

Establish `hf : Continuous (((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom : ℤ_[l] → Qbar l)` using `(continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val`. Conclude with `(Units.continuous_map hf).comp (continuous_cycZ K' Ω l)`. Establish `hεunr : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ h ∈ Ine (F` using `K') A, cycBar K' Ω l h = 1 := by`. Introduce `A hA h hh`. Establish `e : cycZ K' Ω l h = 1` using `MonoidHom.mem_ker.1 (((places K' Ω l A).2.2.2 hA) hh)`.

Simplify using `only [cycBar, MonoidHom.comp_apply, e, map_one]`. Establish `hεres : ∀ h : G K' Ω, cycBar K' Ω l h = cycBar ℚ Ω l (resQ K' h)` using `fun h => rfl`. Establish `hlam : ∀ h : G K' Ω, (κ₀ ^ 2 * cycBar K' Ω l) h = κ₀ h ^ 2 * cycBar K' Ω l h` using `fun h => by`. Rewrite using `[MonoidHom.mul_apply, MonoidHom.pow_apply]`. Establish `hlamc : Continuous ⇑(κ₀ ^ 2 * cycBar K' Ω l : G K' Ω →* (Qbar l)ˣ)`.

Establish `e : ⇑(κ₀ ^ 2 * cycBar K' Ω l : G K' Ω →* (Qbar l)ˣ) = fun h => κ₀ h ^ 2 * cycBar K' Ω l h` using `funext hlam`. Rewrite using `[e]`. Conclude with `(htw.cont.pow 2).mul hεc`. Take `⟨d, hd0, hd⟩` from `exists_pow_cong _ hlamc`. Use `⟨d * mo, (κ₀ ^ 2 * cycBar K' Ω l) ^ (d * mo), fun j hj => ?_⟩` and prove the remaining obligations.

Rewrite using `[← pow_mul]`. Establish `hN : 0 < d * mo * j` using `Nat.mul_pos (Nat.mul_pos hd0 hmo0) (by omega)`. Take `⟨Y', hY', hL'⟩` from `h2 K' Ω l ι art Y a κ₀ hart hYa hL (2 * (d * mo * j)) (d * mo * j)`. Establish `hpw : (κ₀ ^ 2 * cycBar K' Ω l) ^ (d * mo * j) = κ₀ ^ (2 * (d * mo * j)) * cycBar K' Ω l ^ (d * mo * j)`. Rewrite using `[mul_pow, ← pow_mul]`.

Use `⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `e : ⇑((κ₀ ^ 2 * cycBar K' Ω l) ^ (d * mo * j) : G K' Ω →* (Qbar l)ˣ) = fun h => (κ₀ h ^ 2 * cycBar K' Ω l h) ^ (d * mo * j)`. Use function extensionality and compare the values at `fun h => by rw [MonoidHom.pow_apply, hlam]`. Rewrite using `[e]`. Conclude with `((htw.cont.pow 2).mul hεc).pow _`.

Use `⟨art, Y', _, τ, hart, hY', by rw [hpw]; exact hL', ?_, ?_⟩` and prove the remaining obligations. Use `show ((2 * (d * mo * j) : ℕ) : ℤ) * a τ + ((d * mo * j : ℕ) : ℤ) = -((d * mo * j : ℕ) : ℤ)`. Rewrite using `[ha1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `show ((2 * (d * mo * j) : ℕ) : ℤ) * a (ComplexEmbedding.conjugate τ) + ((d * mo * j : ℕ) : ℤ) = ((d * mo * j : ℕ) : ℤ)`. Rewrite using `[ha0]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `t ht h h' hh'`.

Establish `htg : t ∉ galOf ℚ K' Ω` using `fun h0 => ht (by`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Conclude with `(mem_galOf ℚ K' Ω).1 h0 ⟨x, hx⟩)`. Establish `hu : cc⁻¹ * t ∈ galOf ℚ K' Ω`.

Rewrite using `[Subgroup.mul_mem_iff_of_index_two hi, inv_mem_iff]`. Conclude with `iff_of_false hccK htg`. Rewrite `hu` using `[← range_galEmb]`. Take `⟨v, hv⟩` from `hu`. Establish `hh'' : galEmb ℚ K' Ω h' = t * galEmb ℚ K' Ω h * t⁻¹` using `hh'`.

Establish `hs : galEmb ℚ K' Ω h' = cc * galEmb ℚ K' Ω (v * h * v⁻¹) * cc⁻¹`. Rewrite using `[map_mul, map_mul, map_inv, hv, hh'']`. Use `group`. Establish `hc` using `htw.conj (v * h * v⁻¹) h' hs`. Simplify using `only [map_mul, map_inv, mul_inv_cancel_comm] at hc`.

Establish `hε' : cycBar K' Ω l h' = cycBar K' Ω l h`. Rewrite using `[hεres, hεres h, hh', map_mul, map_mul, map_inv, mul_inv_cancel_comm]`. Rewrite using `[MonoidHom.pow_apply, MonoidHom.pow_apply, ← mul_pow, hlam, hlam, hε', mul_mul_mul_comm, ← mul_pow, hc, ← sq (cycBar K' Ω l h), inv_pow, inv_mul_cancel, one_pow]`. Introduce `t ht h hh`. Establish `htg : t ∉ galOf ℚ K' Ω` using `fun h0 => ht (by`.

Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Conclude with `(mem_galOf ℚ K' Ω).1 h0 ⟨x, hx⟩)`. Establish `e1` using `htw.ver h t htg hh`. Establish `e2 : cycBar K' Ω l h = cycBar ℚ Ω l t * cycBar ℚ Ω l t`.

Rewrite using `[hεres, hh, map_mul]`. Rewrite using `[MonoidHom.pow_apply, hlam, e1, e2, neg_sq, inv_pow, ← sq (cycBar ℚ Ω l t), inv_mul_cancel, one_pow]`. Introduce `h`. Apply `cong_of_mem` to reduce the goal to its premises. Rewrite using `[MonoidHom.pow_apply, pow_mul, pow_mul]`.

Conclude with `pow_mem (pow_mem (hd h) mo) j`. Introduce `A hA h hh`. Establish `h'` using `hIne A h hh`. Rewrite using `[MonoidHom.pow_apply, hlam, hεunr A hA h h', mul_one, ← pow_mul, show 2 * (d * mo * j) = mo * (2 * d * j) by ring, pow_mul, hmo A hA h h', one_pow]`. Introduce `A hA`.

Break down `h1 Ω l ι K' hK2 hTC hld hsp cc κ₀ htw A hA with e | e` into its components or cases. Use `Or.inr fun h hh => ?_` and prove the remaining obligations. Rewrite using `[MonoidHom.pow_apply, hlam, e h (hIne A h hh), zpow_neg, zpow_natCast, sq, mul_assoc, inv_mul_cancel, mul_one, inv_pow]`. Use `Or.inl fun h hh => ?_` and prove the remaining obligations. Rewrite using `[MonoidHom.pow_apply, hlam, e h (hIne A h hh), one_pow, one_mul, zpow_natCast]`.
-/
theorem kapEx_alt (h1 : TwistIne) (h2 : AlgType) : _root_.UpperTheory.V.Cu2.KapExAlt := by
  intro hP Ω _ _ _ l _ ι K' _ hl2 hK2 hTC hld hsp hcc
  obtain ⟨cc, hcc⟩ := hcc
  have : IsTotallyComplex K' := hTC
  have : IsAlgClosure K' Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K'⟩
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have : IsGalois K' Ω := IsGalois.tower_top_of_isGalois ℚ K' Ω
  have : CompactSpace (G K' Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[K'] Ω))
  obtain ⟨κ₀, htw⟩ := _root_.UpperTheory.V.Sd.twist_of_printed_results hP K' Ω hK2 l hl2 hld ι cc hcc
  obtain ⟨art, Y, a, τ, hart, hYa, hL, ha1, ha0, -⟩ := htw.alg
  obtain ⟨mo, hmo0, -, hmo⟩ := htw.ord
  have hi : (galOf ℚ K' Ω).index = 2 := (galEmbTop ℚ K' Ω).2.2.trans hK2
  have hccK : cc ∉ galOf ℚ K' Ω := cc_notMem K' hcc
  have hfix : ∀ t : G ℚ Ω, t ∈ K'.fixingSubgroup → t ∈ galOf ℚ K' Ω := fun t h =>
    (mem_galOf ℚ K' Ω).2 fun x => (IntermediateField.mem_fixingSubgroup_iff K' t).1 h x x.2
  have hIne : ∀ (A : ValuationSubring Ω) (h : G K' Ω), resQ K' h ∈ Ine (F := ℚ) A → h ∈ Ine (F := K') A :=
    fun A h hh => ⟨hh.1, hh.2⟩
  have hεc : Continuous (cycBar K' Ω l) := by
    have hf : Continuous (((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom : ℤ_[l] → Qbar l) :=
      (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val
    exact (Units.continuous_map hf).comp (continuous_cycZ K' Ω l)
  have hεunr : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ h ∈ Ine (F := K') A, cycBar K' Ω l h = 1 := by
    intro A hA h hh
    have e : cycZ K' Ω l h = 1 := MonoidHom.mem_ker.1 (((places K' Ω l A).2.2.2 hA) hh)
    simp only [cycBar, MonoidHom.comp_apply, e, map_one]
  have hεres : ∀ h : G K' Ω, cycBar K' Ω l h = cycBar ℚ Ω l (resQ K' h) := fun h => rfl
  have hlam : ∀ h : G K' Ω, (κ₀ ^ 2 * cycBar K' Ω l) h = κ₀ h ^ 2 * cycBar K' Ω l h := fun h => by
    rw [MonoidHom.mul_apply, MonoidHom.pow_apply]
  have hlamc : Continuous ⇑(κ₀ ^ 2 * cycBar K' Ω l : G K' Ω →* (Qbar l)ˣ) := by
    have e : ⇑(κ₀ ^ 2 * cycBar K' Ω l : G K' Ω →* (Qbar l)ˣ) = fun h => κ₀ h ^ 2 * cycBar K' Ω l h := funext hlam
    rw [e]
    exact (htw.cont.pow 2).mul hεc
  obtain ⟨d, hd0, hd⟩ := exists_pow_cong _ hlamc
  refine ⟨d * mo, (κ₀ ^ 2 * cycBar K' Ω l) ^ (d * mo), fun j hj => ?_⟩
  rw [← pow_mul]
  have hN : 0 < d * mo * j := Nat.mul_pos (Nat.mul_pos hd0 hmo0) (by omega)
  obtain ⟨Y', hY', hL'⟩ := h2 K' Ω l ι art Y a κ₀ hart hYa hL (2 * (d * mo * j)) (d * mo * j)
  have hpw : (κ₀ ^ 2 * cycBar K' Ω l) ^ (d * mo * j) =
      κ₀ ^ (2 * (d * mo * j)) * cycBar K' Ω l ^ (d * mo * j) := by
    rw [mul_pow, ← pow_mul]
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : ⇑((κ₀ ^ 2 * cycBar K' Ω l) ^ (d * mo * j) : G K' Ω →* (Qbar l)ˣ) = fun h => (κ₀ h ^ 2 * cycBar K' Ω l h) ^ (d * mo * j) :=
      funext fun h => by rw [MonoidHom.pow_apply, hlam]
    rw [e]
    exact ((htw.cont.pow 2).mul hεc).pow _
  · refine ⟨art, Y', _, τ, hart, hY', by rw [hpw]; exact hL', ?_, ?_⟩
    · show ((2 * (d * mo * j) : ℕ) : ℤ) * a τ + ((d * mo * j : ℕ) : ℤ) = -((d * mo * j : ℕ) : ℤ)
      rw [ha1]
      push_cast
      ring
    · show ((2 * (d * mo * j) : ℕ) : ℤ) * a (ComplexEmbedding.conjugate τ) + ((d * mo * j : ℕ) : ℤ) = ((d * mo * j : ℕ) : ℤ)
      rw [ha0]
      push_cast
      ring
  · intro t ht h h' hh'
    have htg : t ∉ galOf ℚ K' Ω := fun h0 => ht (by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact (mem_galOf ℚ K' Ω).1 h0 ⟨x, hx⟩)
    have hu : cc⁻¹ * t ∈ galOf ℚ K' Ω := by
      rw [Subgroup.mul_mem_iff_of_index_two hi, inv_mem_iff]
      exact iff_of_false hccK htg
    rw [← range_galEmb] at hu
    obtain ⟨v, hv⟩ := hu
    have hh'' : galEmb ℚ K' Ω h' = t * galEmb ℚ K' Ω h * t⁻¹ := hh'
    have hs : galEmb ℚ K' Ω h' = cc * galEmb ℚ K' Ω (v * h * v⁻¹) * cc⁻¹ := by
      rw [map_mul, map_mul, map_inv, hv, hh'']
      group
    have hc := htw.conj (v * h * v⁻¹) h' hs
    simp only [map_mul, map_inv, mul_inv_cancel_comm] at hc
    have hε' : cycBar K' Ω l h' = cycBar K' Ω l h := by
      rw [hεres, hεres h, hh', map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    rw [MonoidHom.pow_apply, MonoidHom.pow_apply, ← mul_pow, hlam, hlam, hε', mul_mul_mul_comm, ← mul_pow, hc,
      ← sq (cycBar K' Ω l h), inv_pow, inv_mul_cancel, one_pow]
  · intro t ht h hh
    have htg : t ∉ galOf ℚ K' Ω := fun h0 => ht (by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact (mem_galOf ℚ K' Ω).1 h0 ⟨x, hx⟩)
    have e1 := htw.ver h t htg hh
    have e2 : cycBar K' Ω l h = cycBar ℚ Ω l t * cycBar ℚ Ω l t := by
      rw [hεres, hh, map_mul]
    rw [MonoidHom.pow_apply, hlam, e1, e2, neg_sq, inv_pow, ← sq (cycBar ℚ Ω l t), inv_mul_cancel, one_pow]
  · intro h
    apply cong_of_mem
    rw [MonoidHom.pow_apply, pow_mul, pow_mul]
    exact pow_mem (pow_mem (hd h) mo) j
  · intro A hA h hh
    have h' := hIne A h hh
    rw [MonoidHom.pow_apply, hlam, hεunr A hA h h', mul_one, ← pow_mul,
      show 2 * (d * mo * j) = mo * (2 * d * j) by ring, pow_mul, hmo A hA h h', one_pow]
  · intro A hA
    rcases h1 Ω l ι K' hK2 hTC hld hsp cc κ₀ htw A hA with e | e
    · refine Or.inr fun h hh => ?_
      rw [MonoidHom.pow_apply, hlam, e h (hIne A h hh), zpow_neg, zpow_natCast, sq, mul_assoc, inv_mul_cancel, mul_one,
        inv_pow]
    · refine Or.inl fun h hh => ?_
      rw [MonoidHom.pow_apply, hlam, e h (hIne A h hh), one_pow, one_mul, zpow_natCast]
end UpperTheory.V.Cu2
end
end
