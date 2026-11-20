import Mathlib
import ReciprocityTheory.NeutralLocalFields.Duality
import ReciprocityTheory.GroupCohomology.ContinuousContractNth

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

/- English proof (translation)
Establish `hint : Algebra.IsIntegral K (PadicAlgCl p)` using `Algebra.IsIntegral.tower_top (R := ℚ_[p])`. Use `show Continuous fun q : GK p K × KbarMult p => kbarRep p K q.1 q.2`. Rewrite using `[continuous_prod_of_discrete_right]`. Introduce `y`. Rewrite using `[continuous_discrete_rng]`.

Introduce `x`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `g0 hg0`. Establish `hop` using `stabilizer_isOpen_of_isIntegral (K := K) (L := PadicAlgCl p) (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p)`. Establish `hn : (fun g : GK p K => g0⁻¹ * g) ⁻¹' (MulAction.stabilizer (GK p K) (((Additive.toMul (α` using `(PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p) : Set (GK p K)) ∈ nhds g0 := (hop.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)`.

Use `filter_upwards [hn] with g hg`. Establish `hg' : (g0⁻¹ * g) (((Additive.toMul (α` using `(PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p) = (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p) := hg`. Establish `hgg : g (((Additive.toMul (α` using `(PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p) = g0 (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p) := by`. Use `congrArg g0 hg'` as an intermediate fact. Rewrite `this` using `[AlgEquiv.mul_apply]`.

Rewrite using `[← this]`. Conclude with `(g0.apply_symm_apply _).symm`. Establish `hxy : kbarRep p K g y = kbarRep p K g0 y` using `Units.ext hgg`. Use `show kbarRep p K g y = x`. Rewrite using `[hxy]`.

Conclude with `hg0`.
-/
theorem kbarRep_contAction : ReciprocityTheory.Gal.ContAction (kbarRep p K) := by
  have hint : Algebra.IsIntegral K (PadicAlgCl p) := Algebra.IsIntegral.tower_top (R := ℚ_[p])
  show Continuous fun q : GK p K × KbarMult p => kbarRep p K q.1 q.2
  rw [continuous_prod_of_discrete_right]
  intro y
  rw [continuous_discrete_rng]
  intro x
  rw [isOpen_iff_mem_nhds]
  intro g0 hg0
  have hop := stabilizer_isOpen_of_isIntegral (K := K) (L := PadicAlgCl p)
    (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p)
  have hn : (fun g : GK p K => g0⁻¹ * g) ⁻¹' (MulAction.stabilizer (GK p K)
      (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p) : Set (GK p K)) ∈ nhds g0 :=
    (hop.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [hn] with g hg
  have hg' : (g0⁻¹ * g) (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p)
      = (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p) := hg
  have hgg : g (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p)
      = g0 (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p) := by
    have := congrArg g0 hg'
    rw [AlgEquiv.mul_apply] at this
    rw [← this]
    exact (g0.apply_symm_apply _).symm
  have hxy : kbarRep p K g y = kbarRep p K g0 y := Units.ext hgg
  show kbarRep p K g y = x
  rw [hxy]
  exact hg0

noncomputable def kbarT : TRep ℤ (GK p K) where
  V := KbarMult p
  rho := kbarRep p K
  cont := kbarRep_contAction p K

scoped instance : DiscreteTopology (kbarT p K).V := inferInstanceAs (DiscreteTopology (KbarMult p))

end ReciprocityTheory.DiscreteGroups.LocalClassField
