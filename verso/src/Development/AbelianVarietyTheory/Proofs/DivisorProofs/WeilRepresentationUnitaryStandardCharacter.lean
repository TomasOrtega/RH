import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryOperatorCommutesSchrodingerStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.SplitScalar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open scoped Classical in

/- English proof (translation)
Introduce `g _`. Use `⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩` and prove the remaining obligations. Simplify using `[pureA, mul_comm]`.
-/
theorem proj_mem_adm (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
  simp [pureA, mul_comm]

/- English proof (translation)
Introduce `h` and use `hf (by have e : T q⁻¹ (T q f) = f := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] rw [← e, h, map_zero])`.
-/
theorem apply_ne_zero {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (T : G →* Module.End ℂ V) (q : G) {f : V}
    (hf : f ≠ 0) : T q f ≠ 0 := fun h => hf (by
  have e : T q⁻¹ (T q f) = f := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← e, h, map_zero])

variable {σ : E →ₐ[F] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/- English proof (translation)
Introduce `u hu`. Establish `e : ((g⁻¹).1 : Matrix β β (AE F E)) - 1 = -(((g⁻¹).1 : Matrix β β (AE F E)) * ((g.1 : Matrix β β (AE F E)) - 1))`. Rewrite using `[Matrix.mul_sub, Matrix.mul_one]`. Establish `: ((g⁻¹).1 : Matrix β β (AE F E)) * (g.1 : Matrix β β (AE F E)) = 1`. Rewrite using `[Subgroup.coe_inv, Units.inv_mul]`.

Rewrite using `[this]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]`.
-/
theorem at_inv {JB : Matrix β β (AE F E)} {g : UG (cA σ) JB}
    (hg : At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)) : At (evI F) (((g⁻¹).1 : Matrix β β (AE F E)) - 1) := by
  intro u hu
  have e : ((g⁻¹).1 : Matrix β β (AE F E)) - 1 = -(((g⁻¹).1 : Matrix β β (AE F E)) * ((g.1 : Matrix β β (AE F E)) - 1)) := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    have : ((g⁻¹).1 : Matrix β β (AE F E)) * (g.1 : Matrix β β (AE F E)) = 1 := by
      rw [Subgroup.coe_inv, Units.inv_mul]
    rw [this]; abel
  rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]

/- English proof (translation)
Introduce `u hu`. Establish `e : ((g * h).1 : Matrix β β (AE F E)) - 1 = (g.1 : Matrix β β (AE F E)) * ((h.1 : Matrix β β (AE F E)) - 1) + ((g.1 : Matrix β β (AE F E)) - 1)`. Rewrite using `[Subgroup.coe_mul, Units.val_mul, Matrix.mul_sub, Matrix.mul_one]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, smul_add, ← Matrix.mul_smul, hh u hu, hg u hu, Matrix.mul_zero, add_zero]`.
-/
theorem at_mul {JB : Matrix β β (AE F E)} {g h : UG (cA σ) JB}
    (hg : At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)) (hh : At (evI F) ((h.1 : Matrix β β (AE F E)) - 1)) :
    At (evI F) (((g * h).1 : Matrix β β (AE F E)) - 1) := by
  intro u hu
  have e : ((g * h).1 : Matrix β β (AE F E)) - 1 =
      (g.1 : Matrix β β (AE F E)) * ((h.1 : Matrix β β (AE F E)) - 1) + ((g.1 : Matrix β β (AE F E)) - 1) := by
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_sub, Matrix.mul_one]; abel
  rw [e, smul_add, ← Matrix.mul_smul, hh u hu, hg u hu, Matrix.mul_zero, add_zero]

/- English proof (translation)
Unfold `actB`. Rewrite using `[Matrix.mul_assoc, ← Matrix.transpose_mul, Subgroup.coe_inv, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one]`.
-/
theorem actB_actB_inv {JB : Matrix β β (AE F E)} (g : UG (cA σ) JB) (x : Matrix α β (AE F E)) :
    actB (cA σ) g (actB (cA σ) g⁻¹ x) = x := by
  unfold actB
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul, Subgroup.coe_inv, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one]

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d om ω₀ hψ hom hω hcont`. Establish `key : ∀ g : UG (cA σ) JB, ∃ z : ℂ, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ∀ φ ∈ schA F κ, om g φ = z • ω₀ g φ`. Introduce `g`. Distinguish the cases in `hg : At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)`. Use `swap`.

Conclude with `⟨1, fun h => absurd h hg⟩`. Establish `hgi` using `at_inv hg`. Take `⟨z, hz⟩` from `GlobalTheory.T.unitary_operator_commutes_schrodinger hP F κ ψ hψ (om g * ω₀ g⁻¹) (fun φ hφ => hom.pres g _ ((hω _ hgi).1 φ hφ)) (fun w φ hφ => by`. Establish `e1 : schr ψ w φ = d.rho ψ (d.e.symm w) φ` using `by simp [Darboux.rho]`. Rewrite using `[Module.End.mul_apply, Module.End.mul_apply, e1, (hω _ hgi).2.1 _ φ hφ, hom.impl g _ _ ((hω _ hgi).1 φ hφ), actB_actB_inv]`.

Simplify using `[Darboux.rho])`. Use the proof step `(fun μ hμ φ hφ => by`. Rewrite using `[Module.End.mul_apply, hom.unit μ hμ g _ ((hω _ hgi).1 φ hφ), (hω _ hgi).2.2 μ hμ φ hφ])`. Use `⟨z, fun _ φ hφ => ?_⟩` and prove the remaining obligations. Use `hz (ω₀ g φ) ((hω g hg).1 φ hφ)` as an intermediate fact.

Rewrite `this` using `[Module.End.mul_apply, ← Module.End.mul_apply (ω₀ g⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Then use the resulting hypothesis. Use `choose z hz using key`. Distinguish the cases in `h0 : ∃ φ₀ ∈ schA F κ, φ₀ ≠ 0`. Use `swap`. Use `push_neg at h0`.

Use `⟨fun _ => 1, fun g _ φ hφ => ?_, fun _ _ _ _ => by simp, continuousOn_const, fun _ _ => one_ne_zero⟩` and prove the remaining obligations. Rewrite using `[h0 φ hφ, map_zero, map_zero, smul_zero]`. Take `⟨φ₀, hφ₀, hne⟩` from `h0`. Use `⟨z, hz, fun g h hg hh => ?_, fun g hg => ?_, fun g hg h0 => ?_⟩` and prove the remaining obligations. Establish `hgh` using `at_mul hg hh`.

Apply `smul_left_injective ℂ (apply_ne_zero ω₀ (g * h) hne)` to reduce the goal to its premises. Use `show z (g * h) • ω₀ (g * h) φ₀ = (z g * z h) • ω₀ (g * h) φ₀`. Rewrite using `[← hz _ hgh φ₀ hφ₀, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hz h hh φ₀ hφ₀, map_smul, hz g hg _ ((hω h hh).1 φ₀ hφ₀), smul_smul, mul_comm]`. Take `⟨x, hx⟩` from `Function.ne_iff.1 (apply_ne_zero ω₀ g hne)`. Establish `hl` using `proj_mem_adm F κ x`.

Establish `c1 : ContinuousWithinAt (fun q => (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ q φ₀)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} g` using `hcont _ hl φ₀ hφ₀ g hg`. Establish `c2 : ContinuousWithinAt (fun q => (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (om q φ₀)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} g` using `(hom.cont _ hl φ₀ hφ₀).continuousWithinAt`. Establish `hx' : (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ g φ₀) ≠ 0` using `hx`. Establish `c3` using `c2.div c1 hx'`. Establish `hq : ∀ q, At (evI F) ((q.1 : Matrix β β (AE F E)) - 1) → (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ q φ₀) ≠ 0 → z q = (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (om q φ₀) / (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ q φ₀)`.

Introduce `q hqS hq0`. Rewrite using `[hz q hqS φ₀ hφ₀, map_smul, smul_eq_mul, mul_div_cancel_right₀ _ hq0]`. Use `c3.congr_of_eventuallyEq ?_ (hq g hg hx')` and prove the remaining obligations. Use `filter_upwards [Filter.Tendsto.eventually_ne c1 hx', self_mem_nhdsWithin] with q hq0 hqS`. Conclude with `hq q hqS hq0`.

Use `hz g hg φ₀ hφ₀` as an intermediate fact. Rewrite `this` using `[h0, zero_smul]`. Conclude with `apply_ne_zero om g hne this`.
-/
theorem splittings_differ_by_character : GlobalTheory.FunPr.Hypotheses₂ →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (om ω₀ : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)), IsStd ψ →
    IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om →
    (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ) ∧
        (∀ w, ∀ φ ∈ schA F κ, ω₀ g (d.rho ψ w φ) = d.rho ψ (actB (cA σ) g w) (ω₀ g φ)) ∧
        ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
          ∀ φ ∈ schA F κ, ∫⁻ x, ‖ω₀ g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ l ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ,
        ContinuousOn (fun g => l (ω₀ g φ)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) →
    ∃ ν : UG (cA σ) JB → ℂ,
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ∀ φ ∈ schA F κ, om g φ = ν g • ω₀ g φ) ∧
      (∀ g h : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → At (evI F) ((h.1 : Matrix β β (AE F E)) - 1) →
        ν (g * h) = ν g * ν h) ∧
      ContinuousOn ν {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} ∧
      ∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ν g ≠ 0 := by
  intro hP F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d om ω₀ hψ hom hω hcont
  have key : ∀ g : UG (cA σ) JB, ∃ z : ℂ, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
      ∀ φ ∈ schA F κ, om g φ = z • ω₀ g φ := by
    intro g
    by_cases hg : At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)
    swap
    · exact ⟨1, fun h => absurd h hg⟩
    have hgi := at_inv hg
    obtain ⟨z, hz⟩ := GlobalTheory.T.unitary_operator_commutes_schrodinger hP F κ ψ hψ (om g * ω₀ g⁻¹)
      (fun φ hφ => hom.pres g _ ((hω _ hgi).1 φ hφ))
      (fun w φ hφ => by
        have e1 : schr ψ w φ = d.rho ψ (d.e.symm w) φ := by simp [Darboux.rho]
        rw [Module.End.mul_apply, Module.End.mul_apply, e1, (hω _ hgi).2.1 _ φ hφ,
          hom.impl g _ _ ((hω _ hgi).1 φ hφ), actB_actB_inv]
        simp [Darboux.rho])
      (fun μ hμ φ hφ => by
        rw [Module.End.mul_apply, hom.unit μ hμ g _ ((hω _ hgi).1 φ hφ), (hω _ hgi).2.2 μ hμ φ hφ])
    refine ⟨z, fun _ φ hφ => ?_⟩
    have := hz (ω₀ g φ) ((hω g hg).1 φ hφ)
    rwa [Module.End.mul_apply, ← Module.End.mul_apply (ω₀ g⁻¹), ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at this
  choose z hz using key
  by_cases h0 : ∃ φ₀ ∈ schA F κ, φ₀ ≠ 0
  swap
  · push_neg at h0
    refine ⟨fun _ => 1, fun g _ φ hφ => ?_, fun _ _ _ _ => by simp, continuousOn_const, fun _ _ => one_ne_zero⟩
    rw [h0 φ hφ, map_zero, map_zero, smul_zero]
  obtain ⟨φ₀, hφ₀, hne⟩ := h0
  refine ⟨z, hz, fun g h hg hh => ?_, fun g hg => ?_, fun g hg h0 => ?_⟩
  · have hgh := at_mul hg hh
    apply smul_left_injective ℂ (apply_ne_zero ω₀ (g * h) hne)
    show z (g * h) • ω₀ (g * h) φ₀ = (z g * z h) • ω₀ (g * h) φ₀
    rw [← hz _ hgh φ₀ hφ₀, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hz h hh φ₀ hφ₀, map_smul,
      hz g hg _ ((hω h hh).1 φ₀ hφ₀), smul_smul, mul_comm]
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 (apply_ne_zero ω₀ g hne)
    have hl := proj_mem_adm F κ x
    have c1 : ContinuousWithinAt (fun q => (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ q φ₀))
        {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} g := hcont _ hl φ₀ hφ₀ g hg
    have c2 : ContinuousWithinAt (fun q => (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (om q φ₀))
        {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} g :=
      (hom.cont _ hl φ₀ hφ₀).continuousWithinAt
    have hx' : (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ g φ₀) ≠ 0 := hx
    have c3 := c2.div c1 hx'
    have hq : ∀ q, At (evI F) ((q.1 : Matrix β β (AE F E)) - 1) →
        (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ q φ₀) ≠ 0 →
        z q = (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (om q φ₀) /
          (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ q φ₀) := by
      intro q hqS hq0
      rw [hz q hqS φ₀ hφ₀, map_smul, smul_eq_mul, mul_div_cancel_right₀ _ hq0]
    refine c3.congr_of_eventuallyEq ?_ (hq g hg hx')
    filter_upwards [Filter.Tendsto.eventually_ne c1 hx', self_mem_nhdsWithin] with q hq0 hqS
    exact hq q hqS hq0
  · have := hz g hg φ₀ hφ₀
    rw [h0, zero_smul] at this
    exact apply_ne_zero om g hne this

end GlobalTheory.SplitScalar
