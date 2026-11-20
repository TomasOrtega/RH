import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes

open scoped TensorProduct

namespace GlobalTheory.LKRes

/- English proof (translation)
Establish `h1 : frobK p (Q0 p) (b : PadicAlgCl p) = b` using `congrArg Subtype.val hb`. Establish `h2 : (b : PadicAlgCl p) ∈ Q0 p` using `mem_of_frobK_fixed inferInstance (Kn_le_Kur hr b.2) h1`. Take `⟨c, hc⟩` from `IntermediateField.mem_bot.1 h2`. Conclude with `⟨c, Subtype.ext hc⟩`.
-/
theorem frobQ_fixed_mem (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : 0 < r) (b : Qr p r) (hb : frobQ p r b = b) :
    ∃ c : ℚ_[p], algebraMap ℚ_[p] (Qr p r) c = b := by
  have h1 : frobK p (Q0 p) (b : PadicAlgCl p) = b := congrArg Subtype.val hb
  have h2 : (b : PadicAlgCl p) ∈ Q0 p := mem_of_frobK_fixed inferInstance (Kn_le_Kur hr b.2) h1
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 h2
  exact ⟨c, Subtype.ext hc⟩

/- English proof (translation)
Introduce `p _ K r hr`. Express the relevant statement in the definitionally equal form `∀ x : K ⊗[ℚ_[p]] Qr p r, Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r) x = x → ∃ a : K, (Algebra.TensorProduct.includeLeft : K →ₐ[ℚ_[p]] K ⊗[ℚ_[p]] Qr p r) a = x`. Introduce `x hx`. Set `f : ℚ_[p] →ₗ[ℚ_[p]] Qr p r` to `Algebra.linearMap _ _`. Set `g : Qr p r →ₗ[ℚ_[p]] Qr p r` to `(frobQ p r).toLinearMap - LinearMap.id`.

Establish `hex : Function.Exact f g`. Introduce `b`. Prove the components needed by the constructor for the conclusion. Introduce `hb`. Establish `hb' : frobQ p r b = b` using `sub_eq_zero.1 hb`.

Conclude with `frobQ_fixed_mem p r hr b hb'`. Introduce and unpack `⟨c, rfl⟩`. Simplify using `[g, f]`. Establish `hex2` using `Module.Flat.lTensor_exact K hex`. Establish `hg : g.lTensor K = (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r)).toLinearMap - LinearMap.id`.

Use `TensorProduct.ext' fun a b => ?_` and prove the remaining obligations. Simplify using `[g, TensorProduct.tmul_sub]`. Establish `hx0 : g.lTensor K x = 0`. Rewrite using `[hg, LinearMap.sub_apply, LinearMap.id_apply, AlgHom.toLinearMap_apply]`. Conclude with `sub_eq_zero.2 hx`.

Take `⟨y, hy⟩` from `(hex2 x).1 hx0`. Use `⟨TensorProduct.rid ℚ_[p] K y, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy]`. Use `clear hy hx hx0`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a c`. Simplify using `only [TensorProduct.rid_tmul, LinearMap.lTensor_tmul, f, Algebra.linearMap_apply]`. Express the relevant statement in the definitionally equal form `(c • a) ⊗ₜ[ℚ_[p]] (1 : Qr p r) = a ⊗ₜ[ℚ_[p]] (algebraMap ℚ_[p] (Qr p r) c)`. Rewrite using `[Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`.

Consider the case `add u v hu hv`. Rewrite using `[map_add, map_add, hu, hv, map_add]`.
-/
theorem sigKQ_fixed_eq_inclK : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ), 0 < r →
    ∀ x : GlobalTheory.LKRes.KQ p K r, GlobalTheory.LKRes.sigKQ p K r x = x → ∃ a : K, GlobalTheory.LKRes.inclK p K r a = x := by
  intro p _ K r hr
  change ∀ x : K ⊗[ℚ_[p]] Qr p r, Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r) x = x →
    ∃ a : K, (Algebra.TensorProduct.includeLeft : K →ₐ[ℚ_[p]] K ⊗[ℚ_[p]] Qr p r) a = x
  intro x hx
  let f : ℚ_[p] →ₗ[ℚ_[p]] Qr p r := Algebra.linearMap _ _
  let g : Qr p r →ₗ[ℚ_[p]] Qr p r := (frobQ p r).toLinearMap - LinearMap.id
  have hex : Function.Exact f g := by
    intro b
    constructor
    · intro hb
      have hb' : frobQ p r b = b := sub_eq_zero.1 hb
      exact frobQ_fixed_mem p r hr b hb'
    · rintro ⟨c, rfl⟩
      simp [g, f]
  have hex2 := Module.Flat.lTensor_exact K hex
  have hg : g.lTensor K =
      (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r)).toLinearMap - LinearMap.id := by
    refine TensorProduct.ext' fun a b => ?_
    simp [g, TensorProduct.tmul_sub]
  have hx0 : g.lTensor K x = 0 := by
    rw [hg, LinearMap.sub_apply, LinearMap.id_apply, AlgHom.toLinearMap_apply]
    exact sub_eq_zero.2 hx
  obtain ⟨y, hy⟩ := (hex2 x).1 hx0
  refine ⟨TensorProduct.rid ℚ_[p] K y, ?_⟩
  rw [← hy]
  clear hy hx hx0
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    simp only [TensorProduct.rid_tmul, LinearMap.lTensor_tmul, f, Algebra.linearMap_apply]
    change (c • a) ⊗ₜ[ℚ_[p]] (1 : Qr p r) = a ⊗ₜ[ℚ_[p]] (algebraMap ℚ_[p] (Qr p r) c)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add u v hu hv =>
    rw [map_add, map_add, hu, hv, map_add]

end GlobalTheory.LKRes
