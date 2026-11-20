import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUHerm

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.VolV

open Formalism.L2.SG.Pf.NcVal Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def aL (g : Fv F v) (θ : Fv F v ⊗[F] E) : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E) :=
  LinearMap.id + (g - 1) • (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)).smulRight θ

/- English proof (translation)
Simplify using `[aL, LinearMap.smulRight_apply, smul_smul]`.
-/
theorem aL_apply (g : Fv F v) (θ z : Fv F v ⊗[F] E) :
    aL v g θ z = z + ((g - 1) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z) • θ := by
  simp [aL, LinearMap.smulRight_apply, smul_smul]

/- English proof (translation)
Rewrite using `[aL_apply, map_add, map_smul, hθ, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem trace_aL (g : Fv F v) (θ z : Fv F v ⊗[F] E) (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (aL v g θ z) = g * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z := by
  rw [aL_apply, map_add, map_smul, hθ, smul_eq_mul]
  ring

/- English proof (translation)
Establish `hrank : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2`. Rewrite using `[Module.finrank_baseChange, hfin]`. Establish `hli : LinearIndependent (Fv F v) ![θ, Δ]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`.

Establish `h1` using `congrArg (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)) hst`. Simplify using `only [map_add, map_smul, hθ, hΔ, smul_eq_mul, mul_one, mul_zero, add_zero, map_zero] at h1`. Substitute `h1` using the available equality. Rewrite `hst` using `[zero_smul, zero_add, smul_eq_zero]`. Conclude with `⟨rfl, hst.resolve_right hΔ0⟩`.

Set `b` to `basisOfLinearIndependentOfCardEqFinrank hli (by rw [hrank]; rfl)`. Establish `hb0 : b 0 = θ` using `by simp [b]`. Establish `hb1 : b 1 = Δ` using `by simp [b]`. Establish `hf0 : aL v g θ (b 0) = g • b 0`. Rewrite using `[hb0, aL_apply, hθ, mul_one, sub_smul, one_smul]`.

Normalize the expressions using the abelian group laws. Establish `hf1 : aL v g θ (b 1) = b 1`. Rewrite using `[hb1, aL_apply, hΔ, mul_zero, zero_smul, add_zero]`. Rewrite using `[← LinearMap.det_toMatrix b, Matrix.det_fin_two]`. Simplify using `only [LinearMap.toMatrix_apply, hf0, hf1, map_smul, b.repr_self, Finsupp.smul_apply, Finsupp.single_apply]`.

Simplify using the standard rewrite rules.
-/
theorem det_aL (hfin : Module.finrank F E = 2) (g : Fv F v) (θ Δ : Fv F v ⊗[F] E)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (hΔ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) Δ = 0)
    (hΔ0 : Δ ≠ 0) : LinearMap.det (aL v g θ) = g := by
  classical
  have hrank : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange, hfin]
  have hli : LinearIndependent (Fv F v) ![θ, Δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)) hst
    simp only [map_add, map_smul, hθ, hΔ, smul_eq_mul, mul_one, mul_zero, add_zero, map_zero] at h1
    subst h1
    rw [zero_smul, zero_add, smul_eq_zero] at hst
    exact ⟨rfl, hst.resolve_right hΔ0⟩
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by rw [hrank]; rfl)
  have hb0 : b 0 = θ := by simp [b]
  have hb1 : b 1 = Δ := by simp [b]
  have hf0 : aL v g θ (b 0) = g • b 0 := by
    rw [hb0, aL_apply, hθ, mul_one, sub_smul, one_smul]
    abel
  have hf1 : aL v g θ (b 1) = b 1 := by
    rw [hb1, aL_apply, hΔ, mul_zero, zero_smul, add_zero]
  rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, hf0, hf1, map_smul, b.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply]
  simp

/- English proof (translation)
Express the relevant statement in the definitionally equal form `z ∈ Submodule.span (v.adicCompletionIntegers F) _ at hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨a, -, rfl⟩` from `hy`. Rewrite using `[PI.UnitaryGroupMassFormula.LocJacTyp.Sd.trace_inclR]`.

Establish `hint : IsIntegral ℤ (Algebra.trace F E (a : E))` using `Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe a)`. Use `HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := F) (v := v) (⟨_, hint⟩ : 𝓞 F)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Conclude with `(IsScalarTower.algebraMap_apply (𝓞 F) F (Fv F v) (⟨_, hint⟩ : 𝓞 F)).symm`. Consider the case `zero => rw [map_zero]`.

Conclude with `zero_mem _`. Consider the case `add y w _ _ hy hw => rw [map_add]`. Conclude with `add_mem hy hw`. Consider the case `smul c y _ hy`. Rewrite using `[show c • y = (c : Fv F v) • y from rfl, map_smul, smul_eq_mul]`.

Conclude with `mul_mem c.2 hy`.
-/
private theorem int_of_alg_lemma (z : Fv F v ⊗[F] E) (hz : z ∈ OEv (E := E) v) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z ∈ v.adicCompletionIntegers F := by
  change z ∈ Submodule.span (v.adicCompletionIntegers F) _ at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, -, rfl⟩ := hy
    rw [PI.UnitaryGroupMassFormula.LocJacTyp.Sd.trace_inclR]
    have hint : IsIntegral ℤ (Algebra.trace F E (a : E)) :=
      Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe a)
    have := HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := F) (v := v) (⟨_, hint⟩ : 𝓞 F)
    convert this using 1
    exact (IsScalarTower.algebraMap_apply (𝓞 F) F (Fv F v) (⟨_, hint⟩ : 𝓞 F)).symm
  | zero => rw [map_zero]; exact zero_mem _
  | add y w _ _ hy hw => rw [map_add]; exact add_mem hy hw
  | smul c y _ hy =>
    rw [show c • y = (c : Fv F v) • y from rfl, map_smul, smul_eq_mul]
    exact mul_mem c.2 hy

/- English proof (translation)
Express the relevant statement in the definitionally equal form `z ∈ Submodule.span (v.adicCompletionIntegers F) _ at hz`. Express the relevant statement in the definitionally equal form `_ ∈ Submodule.span (v.adicCompletionIntegers F) _`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨b, -, rfl⟩` from `hy`.

Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨a * b, Set.mem_univ _, ?_⟩` and prove the remaining obligations. Use `show inclR (Fv F v) ((a * b : 𝓞 E) : E) = inclR (Fv F v) (a : E) * inclR (Fv F v) (b : E)`. Rewrite using `[show ((a * b : 𝓞 E) : E) = (a : E) * (b : E) from rfl, map_mul]`. Consider the case `zero => rw [mul_zero]`.

Conclude with `zero_mem _`. Consider the case `add y w _ _ hy hw => rw [mul_add]`. Conclude with `add_mem hy hw`. Consider the case `smul c y _ hy`. Rewrite using `[show c • y = (c : Fv F v) • y from rfl, mul_smul_comm]`.

Conclude with `Submodule.smul_mem _ c hy`.
-/
private theorem int_of_alg_lemma_2 (a : 𝓞 E) (z : Fv F v ⊗[F] E) (hz : z ∈ OEv (E := E) v) :
    inclR (Fv F v) (a : E) * z ∈ OEv (E := E) v := by
  change z ∈ Submodule.span (v.adicCompletionIntegers F) _ at hz
  change _ ∈ Submodule.span (v.adicCompletionIntegers F) _
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, -, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨a * b, Set.mem_univ _, ?_⟩
    show inclR (Fv F v) ((a * b : 𝓞 E) : E) = inclR (Fv F v) (a : E) * inclR (Fv F v) (b : E)
    rw [show ((a * b : 𝓞 E) : E) = (a : E) * (b : E) from rfl, map_mul]
  | zero => rw [mul_zero]; exact zero_mem _
  | add y w _ _ hy hw => rw [mul_add]; exact add_mem hy hw
  | smul c y _ hy =>
    rw [show c • y = (c : Fv F v) • y from rfl, mul_smul_comm]
    exact Submodule.smul_mem _ c hy

/- English proof (translation)
Express the relevant statement in the definitionally equal form `x ∈ Submodule.span (v.adicCompletionIntegers F) _ at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨a, -, rfl⟩` from `hy`. Conclude with `int_of_alg_lemma_2 v a z hz`.

Consider the case `zero => rw [zero_mul]`. Conclude with `(Submodule.span _ _).zero_mem`. Consider the case `add y w _ _ hy hw`. Rewrite using `[add_mul]`. Conclude with `(Submodule.span (v.adicCompletionIntegers F) _).add_mem hy hw`.

Consider the case `smul c y _ hy`. Rewrite using `[show c • y = (c : Fv F v) • y from rfl, smul_mul_assoc]`. Conclude with `(Submodule.span (v.adicCompletionIntegers F) _).smul_mem c hy`.
-/
private theorem int_of_alg_lemma_3 (x z : Fv F v ⊗[F] E) (hx : x ∈ OEv (E := E) v) (hz : z ∈ OEv (E := E) v) :
    x * z ∈ OEv (E := E) v := by
  change x ∈ Submodule.span (v.adicCompletionIntegers F) _ at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, -, rfl⟩ := hy
    exact int_of_alg_lemma_2 v a z hz
  | zero => rw [zero_mul]; exact (Submodule.span _ _).zero_mem
  | add y w _ _ hy hw =>
    rw [add_mul]
    exact (Submodule.span (v.adicCompletionIntegers F) _).add_mem hy hw
  | smul c y _ hy =>
    rw [show c • y = (c : Fv F v) • y from rfl, smul_mul_assoc]
    exact (Submodule.span (v.adicCompletionIntegers F) _).smul_mem c hy

/- English proof (translation)
Establish `h` using `int_of_alg_lemma v _ (int_of_alg_lemma_3 v _ _ hx hθO)`. Rewrite `h` using `[Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, hθ, smul_eq_mul, mul_one]`. Conclude with `h`.
-/
theorem int_of_alg {θ : Fv F v ⊗[F] E} (hθO : θ ∈ OEv (E := E) v)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) {x : Fv F v}
    (hx : algebraMap (Fv F v) (Fv F v ⊗[F] E) x ∈ OEv (E := E) v) : x ∈ v.adicCompletionIntegers F := by
  have h := int_of_alg_lemma v _ (int_of_alg_lemma_3 v _ _ hx hθO)
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, hθ, smul_eq_mul, mul_one] at h
  exact h

/- English proof (translation)
Establish `hsc : ∀ c : Fv F v, sc (E` using `E) v c = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := fun c => by`. Rewrite using `[Algebra.algebraMap_eq_smul_one, ← Formalism.L2.SG.Pf.NcVal.VolTU.sc_mul_eq_smul, mul_one]`. Establish `hcond : (y + sigR (Fv F v) σ y) * sc (E` using `E) v (g : Fv F v)⁻¹ = algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y * (g : Fv F v)⁻¹) := by`. Rewrite using `[← htr, hsc, map_mul]`. Establish `hone : (1 : Fv F v ⊗[F] E) ∈ OEv (E` using `E) v := by`.

Use `PI.UnitaryGroupMassFormula.LocJacTyp.Sd.inclR_mem (E := E) v 1` as an intermediate fact. Simplify using `only [OneMemClass.coe_one, map_one] at this`. Conclude with `this`. Establish `hsmul : ∀ c ∈ v.adicCompletionIntegers F, ∀ x ∈ OEv (E` using `E) v, c • x ∈ OEv (E := E) v := fun c hc x hx => by`. Rewrite using `[← Formalism.L2.SG.Pf.NcVal.VolTU.sc_mul_eq_smul]`.

Conclude with `Formalism.L2.SG.Pf.NcVal.VolTU.sc_mul_mem v hc hx`. Establish `halg : ∀ c ∈ v.adicCompletionIntegers F, algebraMap (Fv F v) (Fv F v ⊗[F] E) c ∈ OEv (E` using `E) v := fun c hc => by`. Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Conclude with `hsmul c hc 1 hone`. Establish `hgO : (g : Fv F v) - 1 ∈ v.adicCompletionIntegers F` using `sub_mem (Formalism.L2.SG.Pf.NcVal.VolTU.natCast_memO v g) (one_mem _)`.

Establish `hgne : (g : Fv F v) ≠ 0` using `Formalism.L2.SG.Pf.NcVal.VolTU.natCast_ne_zero v hg0`. Rewrite using `[hcond]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Establish `htz` using `int_of_alg_lemma v z hz`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[aL_apply]`. Conclude with `add_mem hz (hsmul _ (mul_mem hgO htz) θ hθO)`. Rewrite using `[trace_aL v _ θ z hθ, mul_comm, ← mul_assoc, inv_mul_cancel₀ hgne, one_mul]`. Conclude with `halg _ htz`.

Introduce and unpack `⟨hy, ht⟩`. Establish `htO` using `int_of_alg v hθO hθ ht`. Use `set t := Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y * (g : Fv F v)⁻¹ with ht_def`. Use `⟨y - (((g : Fv F v) - 1) * t) • θ, sub_mem hy (hsmul _ (mul_mem hgO htO) θ hθO), ?_⟩` and prove the remaining obligations. Establish `htr' : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y = (g : Fv F v) * t`.

Rewrite using `[ht_def, mul_comm, mul_assoc, inv_mul_cancel₀ hgne, mul_one]`. Rewrite using `[aL_apply]`. Establish `: Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (y - (((g : Fv F v) - 1) * t) • θ) = t`. Rewrite using `[map_sub, map_smul, hθ, smul_eq_mul, mul_one, htr']`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, sub_add_cancel]`.
-/
theorem mem_aL_image (σ : E →ₐ[F] E)
    (htr : ∀ w : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w) =
      w + sigR (Fv F v) σ w)
    {g : ℕ} (hg0 : g ≠ 0) {θ : Fv F v ⊗[F] E} (hθO : θ ∈ OEv (E := E) v)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (y : Fv F v ⊗[F] E) :
    y ∈ aL v (g : Fv F v) θ '' OEv (E := E) v ↔
      y ∈ OEv (E := E) v ∧ (y + sigR (Fv F v) σ y) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v := by
  classical
  have hsc : ∀ c : Fv F v, sc (E := E) v c = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := fun c => by
    rw [Algebra.algebraMap_eq_smul_one, ← Formalism.L2.SG.Pf.NcVal.VolTU.sc_mul_eq_smul, mul_one]
  have hcond : (y + sigR (Fv F v) σ y) * sc (E := E) v (g : Fv F v)⁻¹ =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y * (g : Fv F v)⁻¹) := by
    rw [← htr, hsc, map_mul]
  have hone : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
    have := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.inclR_mem (E := E) v 1
    simp only [OneMemClass.coe_one, map_one] at this
    exact this
  have hsmul : ∀ c ∈ v.adicCompletionIntegers F, ∀ x ∈ OEv (E := E) v, c • x ∈ OEv (E := E) v :=
    fun c hc x hx => by
      rw [← Formalism.L2.SG.Pf.NcVal.VolTU.sc_mul_eq_smul]
      exact Formalism.L2.SG.Pf.NcVal.VolTU.sc_mul_mem v hc hx
  have halg : ∀ c ∈ v.adicCompletionIntegers F, algebraMap (Fv F v) (Fv F v ⊗[F] E) c ∈ OEv (E := E) v :=
    fun c hc => by
      rw [Algebra.algebraMap_eq_smul_one]
      exact hsmul c hc 1 hone
  have hgO : (g : Fv F v) - 1 ∈ v.adicCompletionIntegers F :=
    sub_mem (Formalism.L2.SG.Pf.NcVal.VolTU.natCast_memO v g) (one_mem _)
  have hgne : (g : Fv F v) ≠ 0 := Formalism.L2.SG.Pf.NcVal.VolTU.natCast_ne_zero v hg0
  rw [hcond]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have htz := int_of_alg_lemma v z hz
    refine ⟨?_, ?_⟩
    · rw [aL_apply]
      exact add_mem hz (hsmul _ (mul_mem hgO htz) θ hθO)
    · rw [trace_aL v _ θ z hθ, mul_comm, ← mul_assoc, inv_mul_cancel₀ hgne, one_mul]
      exact halg _ htz
  · rintro ⟨hy, ht⟩
    have htO := int_of_alg v hθO hθ ht
    set t := Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y * (g : Fv F v)⁻¹ with ht_def
    refine ⟨y - (((g : Fv F v) - 1) * t) • θ, sub_mem hy (hsmul _ (mul_mem hgO htO) θ hθO), ?_⟩
    have htr' : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y = (g : Fv F v) * t := by
      rw [ht_def, mul_comm, mul_assoc, inv_mul_cancel₀ hgne, mul_one]
    rw [aL_apply]
    have : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (y - (((g : Fv F v) - 1) * t) • θ) = t := by
      rw [map_sub, map_smul, hθ, smul_eq_mul, mul_one, htr']
      ring
    rw [this, sub_add_cancel]

end Formalism.L2.SG.Pf.NcVal.VolV
