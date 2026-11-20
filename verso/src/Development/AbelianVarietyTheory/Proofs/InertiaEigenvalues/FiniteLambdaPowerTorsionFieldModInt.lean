import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleModuleIffLatticeQuotients
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

namespace GlobalTheory.UseLoc.Cases

/- English proof (translation)
Use `haveI := GlobalTheory.FullCharpoly.hasFiniteQuotients_OL LL`. Establish `hinj : Function.Injective (algebraMap ↥(OL LL) ↥LL.1)` using `Subtype.val_injective`. Establish `hne : lam ^ a ≠ 0` using `pow_ne_zero _ hlam.ne_zero`. Establish `hK : algebraMap ↥(OL LL) ↥LL.1 (lam ^ a) ≠ 0`. Introduce `h; exact hne (hinj (by rw [h, map_zero]))`.

Use `haveI : Finite (↥(OL LL) ⧸ Ideal.span {lam ^ a}) := Ring.HasFiniteQuotients.finiteQuotient (by`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot])` and apply the resulting hypothesis. Establish `hex : ∀ x : ↥(Xq ↥LL.1 lam a), ∃ c : ↥(OL LL), ∃ s : ↥LL.1, Submodule.Quotient.mk (p` using `intO (O := ↥(OL LL)) ↥LL.1) s = x.1 ∧ algebraMap ↥(OL LL) ↥LL.1 c = lam ^ a • s := by`. Introduce `x`. Take `⟨s, hs⟩` from `Submodule.Quotient.mk_surjective _ x.1`.

Establish `hx` using `x.2`. Simplify using `only [Xq, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at hx`. Rewrite `hx` using `[← hs, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Take `⟨c, hc⟩` from `hx`. Conclude with `⟨c, s, hs, hc⟩`.

Set `f : ↥(Xq ↥LL.1 lam a) → ↥(OL LL) ⧸ Ideal.span {lam ^ a}` to `fun x => Ideal.Quotient.mk _ (hex x).choose`. Use `Finite.of_injective f ?_` and prove the remaining obligations. Introduce `x y hxy`. Take `⟨s, hs, hc⟩` from `(hex x).choose_spec`. Take `⟨t, ht, hd⟩` from `(hex y).choose_spec`.

Establish `h1` using `hxy`. Simplify using `only [f, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h1`. Take `⟨d, hd'⟩` from `h1`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hs, ← ht, ← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]`.

Use `⟨d, ?_⟩` and prove the remaining obligations. Establish `h2 : algebraMap ↥(OL LL) ↥LL.1 (lam ^ a) * (s - t) = algebraMap ↥(OL LL) ↥LL.1 (lam ^ a) * algebraMap ↥(OL LL) ↥LL.1 d`. Rewrite using `[← map_mul, mul_comm (lam ^ a) d, hd', map_sub, hc, hd, Algebra.smul_def, Algebra.smul_def, mul_sub]`. Use `mul_left_cancel₀ hK h2` as an intermediate fact. Simplify using `only [Algebra.linearMap_apply]`.

Conclude with `this.symm`.
-/
theorem finite_Xq {l : ℕ} [Fact l.Prime] (LL : FinExt l) (lam : ↥(OL LL)) (hlam : Irreducible lam) (a : ℕ) :
    Finite ↥(Xq ↥LL.1 lam a) := by
  classical
  haveI := GlobalTheory.FullCharpoly.hasFiniteQuotients_OL LL
  have hinj : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hne : lam ^ a ≠ 0 := pow_ne_zero _ hlam.ne_zero
  have hK : algebraMap ↥(OL LL) ↥LL.1 (lam ^ a) ≠ 0 := by
    intro h; exact hne (hinj (by rw [h, map_zero]))
  haveI : Finite (↥(OL LL) ⧸ Ideal.span {lam ^ a}) := Ring.HasFiniteQuotients.finiteQuotient (by
    rwa [Ne, Ideal.span_singleton_eq_bot])
  have hex : ∀ x : ↥(Xq ↥LL.1 lam a), ∃ c : ↥(OL LL), ∃ s : ↥LL.1,
      Submodule.Quotient.mk (p := intO (O := ↥(OL LL)) ↥LL.1) s = x.1 ∧ algebraMap ↥(OL LL) ↥LL.1 c = lam ^ a • s := by
    intro x
    obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ x.1
    have hx := x.2
    simp only [Xq, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at hx
    rw [← hs, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨c, hc⟩ := hx
    exact ⟨c, s, hs, hc⟩
  let f : ↥(Xq ↥LL.1 lam a) → ↥(OL LL) ⧸ Ideal.span {lam ^ a} := fun x => Ideal.Quotient.mk _ (hex x).choose
  refine Finite.of_injective f ?_
  intro x y hxy
  obtain ⟨s, hs, hc⟩ := (hex x).choose_spec
  obtain ⟨t, ht, hd⟩ := (hex y).choose_spec
  have h1 := hxy
  simp only [f, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h1
  obtain ⟨d, hd'⟩ := h1
  apply Subtype.ext
  rw [← hs, ← ht, ← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
  refine ⟨d, ?_⟩
  have h2 : algebraMap ↥(OL LL) ↥LL.1 (lam ^ a) * (s - t) = algebraMap ↥(OL LL) ↥LL.1 (lam ^ a) * algebraMap ↥(OL LL) ↥LL.1 d := by
    rw [← map_mul, mul_comm (lam ^ a) d, hd', map_sub, hc, hd, Algebra.smul_def, Algebra.smul_def, mul_sub]
  have := mul_left_cancel₀ hK h2
  simp only [Algebra.linearMap_apply]
  exact this.symm

end GlobalTheory.UseLoc.Cases
