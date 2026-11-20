import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.IsEquivAdicAbvNormAbv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.NormLeOneOfInteger
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.EmbExt

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]

def scalarLift (φ : E →+* Om l) : ℚ_[l] ⊗[ℚ] E →ₐ[ℚ_[l]] Om l :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ_[l] (Om l)) φ.toRatAlgHom (fun _ _ => Commute.all _ _)

/- English proof (translation)
Simplify using `[scalarLift]`.
-/
theorem scalarLift_tmul (φ : E →+* Om l) (a : ℚ_[l]) (y : E) :
    scalarLift φ (a ⊗ₜ y) = algebraMap ℚ_[l] (Om l) a * φ y := by
  simp [scalarLift]

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => intro ε hε; exact ⟨0, by simpa using hε, by simpa using hε⟩`. Consider the case `tmul a y`. Introduce `ε hε`. Establish `hM : 0 < ‖φ y‖ + ‖ψ y‖ + 1` using `by positivity`.

Take `⟨q, hq⟩` from `Padic.rat_dense l a (div_pos hε hM)`. Use `⟨(q : E) * y, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[scalarLift_tmul, map_mul, map_ratCast, ← map_ratCast (algebraMap ℚ_[l] (Om l)) q, ← sub_mul, ← map_sub, norm_mul, PadicAlgCl.norm_extends]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[scalarLift_tmul, map_mul, map_ratCast, ← map_ratCast (algebraMap ℚ_[l] (Om l)) q, ← sub_mul, ← map_sub, norm_mul, PadicAlgCl.norm_extends]`.

Combine the equalities or inequalities in the displayed calculation. Consider the case `add t₁ t₂ h₁ h₂`. Introduce `ε hε`. Take `⟨x₁, a₁, b₁⟩` from `h₁ (ε / 2) (half_pos hε)`. Take `⟨x₂, a₂, b₂⟩` from `h₂ (ε / 2) (half_pos hε)`.

Use `⟨x₁ + x₂, ?_, ?_⟩` and prove the remaining obligations. Establish `e : scalarLift φ (t₁ + t₂) - φ (x₁ + x₂) = (scalarLift φ t₁ - φ x₁) + (scalarLift φ t₂ - φ x₂)`. Rewrite using `[map_add, map_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Combine the linear relations using `[norm_add_le (scalarLift φ t₁ - φ x₁) (scalarLift φ t₂ - φ x₂)]`. Establish `e : scalarLift ψ (t₁ + t₂) - ψ (x₁ + x₂) = (scalarLift ψ t₁ - ψ x₁) + (scalarLift ψ t₂ - ψ x₂)`. Rewrite using `[map_add, map_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Combine the linear relations using `[norm_add_le (scalarLift ψ t₁ - ψ x₁) (scalarLift ψ t₂ - ψ x₂)]`.
-/
theorem exists_near (φ ψ : E →+* Om l) (t : ℚ_[l] ⊗[ℚ] E) :
    ∀ ε : ℝ, 0 < ε → ∃ x : E, ‖scalarLift φ t - φ x‖ < ε ∧ ‖scalarLift ψ t - ψ x‖ < ε := by
  induction t using TensorProduct.induction_on with
  | zero => intro ε hε; exact ⟨0, by simpa using hε, by simpa using hε⟩
  | tmul a y =>
    intro ε hε
    have hM : 0 < ‖φ y‖ + ‖ψ y‖ + 1 := by positivity
    obtain ⟨q, hq⟩ := Padic.rat_dense l a (div_pos hε hM)
    refine ⟨(q : E) * y, ?_, ?_⟩
    · rw [scalarLift_tmul, map_mul, map_ratCast, ← map_ratCast (algebraMap ℚ_[l] (Om l)) q, ← sub_mul,
        ← map_sub, norm_mul, PadicAlgCl.norm_extends]
      calc ‖a - (q : ℚ_[l])‖ * ‖φ y‖ ≤ ‖a - (q : ℚ_[l])‖ * (‖φ y‖ + ‖ψ y‖ + 1) := by
            gcongr; linarith [norm_nonneg (ψ y)]
        _ < ε / (‖φ y‖ + ‖ψ y‖ + 1) * (‖φ y‖ + ‖ψ y‖ + 1) := by gcongr
        _ = ε := div_mul_cancel₀ _ hM.ne'
    · rw [scalarLift_tmul, map_mul, map_ratCast, ← map_ratCast (algebraMap ℚ_[l] (Om l)) q, ← sub_mul,
        ← map_sub, norm_mul, PadicAlgCl.norm_extends]
      calc ‖a - (q : ℚ_[l])‖ * ‖ψ y‖ ≤ ‖a - (q : ℚ_[l])‖ * (‖φ y‖ + ‖ψ y‖ + 1) := by
            gcongr; linarith [norm_nonneg (φ y)]
        _ < ε / (‖φ y‖ + ‖ψ y‖ + 1) * (‖φ y‖ + ‖ψ y‖ + 1) := by gcongr
        _ = ε := div_mul_cancel₀ _ hM.ne'
  | add t₁ t₂ h₁ h₂ =>
    intro ε hε
    obtain ⟨x₁, a₁, b₁⟩ := h₁ (ε / 2) (half_pos hε)
    obtain ⟨x₂, a₂, b₂⟩ := h₂ (ε / 2) (half_pos hε)
    refine ⟨x₁ + x₂, ?_, ?_⟩
    · have e : scalarLift φ (t₁ + t₂) - φ (x₁ + x₂) = (scalarLift φ t₁ - φ x₁) + (scalarLift φ t₂ - φ x₂) := by
        rw [map_add, map_add]; ring
      rw [e]; linarith [norm_add_le (scalarLift φ t₁ - φ x₁) (scalarLift φ t₂ - φ x₂)]
    · have e : scalarLift ψ (t₁ + t₂) - ψ (x₁ + x₂) = (scalarLift ψ t₁ - ψ x₁) + (scalarLift ψ t₂ - ψ x₂) := by
        rw [map_add, map_add]; ring
      rw [e]; linarith [norm_add_le (scalarLift ψ t₁ - ψ x₁) (scalarLift ψ t₂ - ψ x₂)]

/- English proof (translation)
Use `le_of_forall_pos_le_add fun ε hε => ?_` and prove the remaining obligations. Take `⟨x, h₁, h₂⟩` from `exists_near φ ψ t (ε / 2) (half_pos hε)`. Establish `e1 : ‖scalarLift ψ t‖ ≤ ‖scalarLift ψ t - ψ x‖ + ‖ψ x‖`. Simplify using `using norm_add_le (scalarLift ψ t - ψ x) (ψ x)`. Establish `e2 : ‖φ x‖ ≤ ‖φ x - scalarLift φ t‖ + ‖scalarLift φ t‖`.

Simplify using `using norm_add_le (φ x - scalarLift φ t) (scalarLift φ t)`. Rewrite `e2` using `[norm_sub_rev]`. Rewrite `e1` using `[← h x]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_scalarLift_le (φ ψ : E →+* Om l) (h : ∀ x, ‖φ x‖ = ‖ψ x‖) (t : ℚ_[l] ⊗[ℚ] E) :
    ‖scalarLift ψ t‖ ≤ ‖scalarLift φ t‖ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨x, h₁, h₂⟩ := exists_near φ ψ t (ε / 2) (half_pos hε)
  have e1 : ‖scalarLift ψ t‖ ≤ ‖scalarLift ψ t - ψ x‖ + ‖ψ x‖ := by
    simpa using norm_add_le (scalarLift ψ t - ψ x) (ψ x)
  have e2 : ‖φ x‖ ≤ ‖φ x - scalarLift φ t‖ + ‖scalarLift φ t‖ := by
    simpa using norm_add_le (φ x - scalarLift φ t) (scalarLift φ t)
  rw [norm_sub_rev] at e2
  rw [← h x] at e1
  linarith

/- English proof (translation)
Establish `e1` using `PI.CompDegEF.isEquiv_adicAbv_normAbv τ w hw (fun x => ⟨PI.CompDegEF.norm_le_one_of_integer τ x, hτ x⟩)`. Establish `e2` using `PI.CompDegEF.isEquiv_adicAbv_normAbv φ w hw (fun x => ⟨PI.CompDegEF.norm_le_one_of_integer φ x, hφ x⟩)`. Take `⟨c, hc, hce⟩` from `AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 (e1.symm.trans e2)`. Establish `hl` using `congrFun hce ((l : ℕ) : E)`. Simplify using `only [PI.CompDegEF.normAbv_apply, map_natCast] at hl`.

Establish `hpos` using `PI.CompDegEF.norm_natCast_pos l`. Establish `hlt` using `PI.CompDegEF.norm_natCast_lt_one l`. Establish `hL : Real.log ‖((l : ℕ) : Om l)‖ ≠ 0` using `(Real.log_neg hpos hlt).ne`. Establish `hc1 : c = 1`. Use `congrArg Real.log hl` as an intermediate fact.

Rewrite `this` using `[Real.log_rpow hpos]`. Conclude with `(mul_eq_right₀ hL).1 this`. Establish `hx` using `congrFun hce x`. Simplify using `only [PI.CompDegEF.normAbv_apply, hc1, Real.rpow_one] at hx`. Conclude with `hx`.
-/
theorem norm_eq_of_same_place (τ φ : E →+* Om l) (w : HeightOneSpectrum (𝓞 E)) (hw : w ∈ placesOver E l)
    (hτ : ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal) (hφ : ∀ x : 𝓞 E, ‖φ (x : E)‖ < 1 ↔ x ∈ w.asIdeal)
    (x : E) : ‖τ x‖ = ‖φ x‖ := by
  have e1 := PI.CompDegEF.isEquiv_adicAbv_normAbv τ w hw
    (fun x => ⟨PI.CompDegEF.norm_le_one_of_integer τ x, hτ x⟩)
  have e2 := PI.CompDegEF.isEquiv_adicAbv_normAbv φ w hw
    (fun x => ⟨PI.CompDegEF.norm_le_one_of_integer φ x, hφ x⟩)
  obtain ⟨c, hc, hce⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 (e1.symm.trans e2)
  have hl := congrFun hce ((l : ℕ) : E)
  simp only [PI.CompDegEF.normAbv_apply, map_natCast] at hl
  have hpos := PI.CompDegEF.norm_natCast_pos l
  have hlt := PI.CompDegEF.norm_natCast_lt_one l
  have hL : Real.log ‖((l : ℕ) : Om l)‖ ≠ 0 := (Real.log_neg hpos hlt).ne
  have hc1 : c = 1 := by
    have := congrArg Real.log hl
    rw [Real.log_rpow hpos] at this
    exact (mul_eq_right₀ hL).1 this
  have hx := congrFun hce x
  simp only [PI.CompDegEF.normAbv_apply, hc1, Real.rpow_one] at hx
  exact hx

/- English proof (translation)
Introduce `D l _ w O _ _ _ Bw hj τ hτ LL' hLL`. Set `jE : D.host.E →+* Om l` to `Bw.j.comp (algebraMap D.host.E D.nd.Om)`. Establish `hA` using `D.nd.plOm.2 w`. Establish `hw` using `hj.mem_placesOver hA`. Establish `hjE : ∀ x : 𝓞 D.host.E, ‖jE (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal` using `fun x => (hj.valuation_lt_one_iff _).symm.trans (hA x)`.

Establish `iso` using `norm_eq_of_same_place τ jE w hw hτ hjE`. Establish `hker : ∀ t ∈ RingHom.ker (scalarLift jE), scalarLift τ t = 0` using `fun t ht => norm_eq_zero.1 (le_antisymm ((norm_scalarLift_le jE τ (fun x => (iso x).symm) t).trans (by rw [RingHom.mem_ker.1 ht, norm_zero])) (norm_nonneg _))`. Establish `hrange : (scalarLift jE).range ≤ Bw.Kw.1.toSubalgebra`. Introduce and unpack `_ ⟨t, rfl⟩`. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a y`. Express the relevant statement in the definitionally equal form `scalarLift jE (a ⊗ₜ y) ∈ _`. Rewrite using `[scalarLift_tmul]`. Conclude with `mul_mem (Bw.Kw.1.algebraMap_mem a) (Bw.j_E y)`.

Consider the case `add t₁ t₂ h₁ h₂ => rw [map_add]`. Conclude with `add_mem h₁ h₂`. Establish `hfin : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule (scalarLift jE).range)` using `by haveI : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule Bw.Kw.1.toSubalgebra) := Bw.Kw.2`. Conclude with `Submodule.finiteDimensional_of_le (Subalgebra.toSubmodule.monotone hrange)`. Establish `hclosed : IsClosed ((scalarLift jE).range : Set (Om l))` using `Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule (scalarLift jE).range)`.

Establish `hle : Bw.Kw.1.toSubalgebra ≤ (scalarLift jE).range`. Introduce `y hy`. Use `closure_minimal ?_ hclosed (Bw.j_dense hy)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `⟨1 ⊗ₜ x, by change scalarLift jE (1 ⊗ₜ x) = jE x; rw [scalarLift_tmul, map_one, one_mul]⟩`.

Set `σ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l` to `((Ideal.Quotient.liftₐ (RingHom.ker (scalarLift jE)) (scalarLift τ) hker).comp (Ideal.quotientKerEquivRange (scalarLift jE)).symm.toAlgHom).comp (Subalgebra.inclusion hle)`. Use `⟨σ.codRestrict LL'.1.toSubalgebra (fun y => hLL (Bw.LL_split σ y)), fun x => ?_⟩` and prove the remaining obligations. Establish `key : (Ideal.quotientKerEquivRange (scalarLift jE)).symm (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩) = Ideal.Quotient.mk _ (1 ⊗ₜ x)`. Rewrite using `[AlgEquiv.symm_apply_eq]`. Apply `Subtype.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `jE x = scalarLift jE (1 ⊗ₜ x)`. Rewrite using `[scalarLift_tmul, map_one, one_mul]`. Express the relevant statement in the definitionally equal form `τ x = σ ⟨jE x, Bw.j_E x⟩`. Express the relevant statement in the definitionally equal form `τ x = Ideal.Quotient.liftₐ _ (scalarLift τ) hker ((Ideal.quotientKerEquivRange (scalarLift jE)).symm (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩))`. Rewrite using `[key, Ideal.Quotient.liftₐ_apply]`.

Express the relevant statement in the definitionally equal form `τ x = scalarLift τ (1 ⊗ₜ x)`. Rewrite using `[scalarLift_tmul, map_one, one_mul]`.
-/
theorem main : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (w : PlE D.host) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw → ∀ τ : D.host.E →+* Qbar l, (∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal) → ∀ LL' : FinExt l, Bw.LL.1 ≤ LL'.1 → ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1, GlobalTheory.Pst.IsInduced Bw τ τ' := by
  intro D l _ w O _ _ _ Bw hj τ hτ LL' hLL
  let jE : D.host.E →+* Om l := Bw.j.comp (algebraMap D.host.E D.nd.Om)
  have hA := D.nd.plOm.2 w
  have hw := hj.mem_placesOver hA
  have hjE : ∀ x : 𝓞 D.host.E, ‖jE (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal := fun x =>
    (hj.valuation_lt_one_iff _).symm.trans (hA x)
  have iso := norm_eq_of_same_place τ jE w hw hτ hjE
  have hker : ∀ t ∈ RingHom.ker (scalarLift jE), scalarLift τ t = 0 := fun t ht =>
    norm_eq_zero.1 (le_antisymm ((norm_scalarLift_le jE τ (fun x => (iso x).symm) t).trans
      (by rw [RingHom.mem_ker.1 ht, norm_zero])) (norm_nonneg _))
  have hrange : (scalarLift jE).range ≤ Bw.Kw.1.toSubalgebra := by
    rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
      change scalarLift jE (a ⊗ₜ y) ∈ _
      rw [scalarLift_tmul]
      exact mul_mem (Bw.Kw.1.algebraMap_mem a) (Bw.j_E y)
    | add t₁ t₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  have hfin : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule (scalarLift jE).range) := by
    haveI : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule Bw.Kw.1.toSubalgebra) := Bw.Kw.2
    exact Submodule.finiteDimensional_of_le (Subalgebra.toSubmodule.monotone hrange)
  have hclosed : IsClosed ((scalarLift jE).range : Set (Om l)) :=
    Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule (scalarLift jE).range)
  have hle : Bw.Kw.1.toSubalgebra ≤ (scalarLift jE).range := by
    intro y hy
    refine closure_minimal ?_ hclosed (Bw.j_dense hy)
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by change scalarLift jE (1 ⊗ₜ x) = jE x; rw [scalarLift_tmul, map_one, one_mul]⟩
  let σ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l :=
    ((Ideal.Quotient.liftₐ (RingHom.ker (scalarLift jE)) (scalarLift τ) hker).comp
      (Ideal.quotientKerEquivRange (scalarLift jE)).symm.toAlgHom).comp (Subalgebra.inclusion hle)
  refine ⟨σ.codRestrict LL'.1.toSubalgebra (fun y => hLL (Bw.LL_split σ y)), fun x => ?_⟩
  have key : (Ideal.quotientKerEquivRange (scalarLift jE)).symm
      (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩) = Ideal.Quotient.mk _ (1 ⊗ₜ x) := by
    rw [AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    change jE x = scalarLift jE (1 ⊗ₜ x)
    rw [scalarLift_tmul, map_one, one_mul]
  change τ x = σ ⟨jE x, Bw.j_E x⟩
  change τ x = Ideal.Quotient.liftₐ _ (scalarLift τ) hker ((Ideal.quotientKerEquivRange (scalarLift jE)).symm
    (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩))
  rw [key, Ideal.Quotient.liftₐ_apply]
  change τ x = scalarLift τ (1 ⊗ₜ x)
  rw [scalarLift_tmul, map_one, one_mul]

end GlobalTheory.EmbExt
