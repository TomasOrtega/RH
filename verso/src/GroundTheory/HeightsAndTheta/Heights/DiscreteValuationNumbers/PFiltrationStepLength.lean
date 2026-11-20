import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

/- English proof (translation)
Introduce `R _ K ι L W _ f`. Set `g₁ : (MRing ι R ⧸ L.colon {f}) →ₗ[MRing ι R] MRing ι R ⧸ L` to `Submodule.mapQ _ _ (LinearMap.mulRight (MRing ι R) f) (fun x hx => by`. Use `Submodule.mem_colon_singleton.mp hx` as an intermediate fact. Simplify `this)` using `[smul_eq_mul]`. Set `g₂ : (MRing ι R ⧸ L) →ₗ[MRing ι R] MRing ι R ⧸ (L ⊔ Ideal.span {f})` to `Submodule.mapQ _ _ LinearMap.id (fun x hx => Submodule.mem_sup_left hx)`.

Establish `hinj : Function.Injective g₁`. Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`. Introduce `y hy`. Proceed by induction on `y using Submodule.Quotient.induction_on with | _ c => ?_`. Rewrite `hy` using `[LinearMap.mem_ker]`.

Simplify using `only [g₁, Submodule.mapQ_apply, LinearMap.mulRight_apply, Submodule.Quotient.mk_eq_zero] at hy`. Simplify using `only [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]`. Conclude with `Submodule.mem_colon_singleton.mpr (by simpa [smul_eq_mul] using hy)`. Establish `hsurj : Function.Surjective g₂`. Introduce `y`.

Proceed by induction on `y using Submodule.Quotient.induction_on with | _ a => ?_`. Conclude with `⟨Submodule.Quotient.mk a, rfl⟩`. Establish `hex : Function.Exact g₁ g₂`. Introduce `y`. Proceed by induction on `y using Submodule.Quotient.induction_on with | _ a => ?_`.

Simplify using `only [g₂, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero, Set.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce `ha`. Take `⟨l, hl, m, hm, rfl⟩` from `Submodule.mem_sup.mp ha`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hm`.

Use `⟨Submodule.Quotient.mk c, ?_⟩` and prove the remaining obligations. Simplify using `only [g₁, Submodule.mapQ_apply, LinearMap.mulRight_apply]`. Rewrite using `[Submodule.Quotient.eq]`. Establish `e : c * f - (l + c * f) = -l` using `by ring`. Rewrite using `[e]`.

Conclude with `L.neg_mem hl`. Introduce and unpack `⟨x, hx⟩`. Proceed by induction on `x using Submodule.Quotient.induction_on with | _ c => ?_`. Simplify using `only [g₁, Submodule.mapQ_apply, LinearMap.mulRight_apply] at hx`. Rewrite `hx` using `[Submodule.Quotient.eq]`.

Establish `e : a = -(c * f - a) + c * f` using `by ring`. Rewrite using `[e]`. Conclude with `Submodule.add_mem_sup (L.neg_mem hx) (Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩)`. Establish `key` using `Module.length_eq_add_of_exact (R := Localization.AtPrime W) (LocalizedModule.map W.primeCompl g₁) (LocalizedModule.map W.primeCompl g₂) (LocalizedModule.map_injective _ _ hinj) (LocalizedModule.map_surjective _ _ hsurj) (LocalizedModule.map_exact _ _ _ hex)`. Unfold `multAt`.

Rewrite using `[add_comm]`. Conclude with `key`.
-/
theorem FiltrationStepLength.proof : FiltrationStepLength.Statement := by
  intro R _ K ι L W _ f
  let g₁ : (MRing ι R ⧸ L.colon {f}) →ₗ[MRing ι R] MRing ι R ⧸ L :=
    Submodule.mapQ _ _ (LinearMap.mulRight (MRing ι R) f) (fun x hx => by
      have := Submodule.mem_colon_singleton.mp hx
      simpa [smul_eq_mul] using this)
  let g₂ : (MRing ι R ⧸ L) →ₗ[MRing ι R] MRing ι R ⧸ (L ⊔ Ideal.span {f}) :=
    Submodule.mapQ _ _ LinearMap.id (fun x hx => Submodule.mem_sup_left hx)
  have hinj : Function.Injective g₁ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    induction y using Submodule.Quotient.induction_on with | _ c => ?_
    rw [LinearMap.mem_ker] at hy
    simp only [g₁, Submodule.mapQ_apply, LinearMap.mulRight_apply,
      Submodule.Quotient.mk_eq_zero] at hy
    simp only [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_colon_singleton.mpr (by simpa [smul_eq_mul] using hy)
  have hsurj : Function.Surjective g₂ := by
    intro y
    induction y using Submodule.Quotient.induction_on with | _ a => ?_
    exact ⟨Submodule.Quotient.mk a, rfl⟩
  have hex : Function.Exact g₁ g₂ := by
    intro y
    induction y using Submodule.Quotient.induction_on with | _ a => ?_
    simp only [g₂, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
      Set.mem_range]
    constructor
    · intro ha
      obtain ⟨l, hl, m, hm, rfl⟩ := Submodule.mem_sup.mp ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hm
      refine ⟨Submodule.Quotient.mk c, ?_⟩
      simp only [g₁, Submodule.mapQ_apply, LinearMap.mulRight_apply]
      rw [Submodule.Quotient.eq]
      have e : c * f - (l + c * f) = -l := by ring
      rw [e]
      exact L.neg_mem hl
    · rintro ⟨x, hx⟩
      induction x using Submodule.Quotient.induction_on with | _ c => ?_
      simp only [g₁, Submodule.mapQ_apply, LinearMap.mulRight_apply] at hx
      rw [Submodule.Quotient.eq] at hx
      have e : a = -(c * f - a) + c * f := by ring
      rw [e]
      exact Submodule.add_mem_sup (L.neg_mem hx) (Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩)
  have key := Module.length_eq_add_of_exact (R := Localization.AtPrime W)
    (LocalizedModule.map W.primeCompl g₁) (LocalizedModule.map W.primeCompl g₂)
    (LocalizedModule.map_injective _ _ hinj) (LocalizedModule.map_surjective _ _ hsurj)
    (LocalizedModule.map_exact _ _ _ hex)
  unfold multAt
  rw [add_comm]
  exact key

end GroundTheory.Heights₂.Heights.NumbersDVR
