import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField GlobalTheory.Mem.Per
open scoped Pointwise nonZeroDivisors

namespace GlobalTheory.Mem.EigenLine

variable {R : Ranks} (H : Host R)

/- English proof (translation)
Use `FractionalIdeal.coeIdeal_ne_zero.2 ?_` and prove the remaining obligations. Introduce `h0`. Establish `hd : differentIdeal (𝓞 H.K) (𝓞 H.E) ≠ ⊥` using `differentIdeal_ne_bot`. Apply `hd` to reduce the goal to its premises. Use `H.𝔟_spec.1` as an intermediate fact.

Rewrite `this` using `[h0, Ideal.bot_mul]`. Conclude with `this`.
-/
theorem half_ne_zero :
    ((H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 := by
  refine FractionalIdeal.coeIdeal_ne_zero.2 ?_
  intro h0
  have hd : differentIdeal (𝓞 H.K) (𝓞 H.E) ≠ ⊥ := differentIdeal_ne_bot
  apply hd
  have := H.𝔟_spec.1
  rw [h0, Ideal.bot_mul] at this
  exact this

/- English proof (translation)
The claim follows from `mul_inv_cancel₀ (half_ne_zero H)`.
-/
theorem half_mul_inv :
    ((H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) * H.AA0 = 1 :=
  mul_inv_cancel₀ (half_ne_zero H)

/- English proof (translation)
Establish `h : differentIdeal (𝓞 H.K) (𝓞 H.E) = H.𝔟 * (H.conj • H.𝔟)` using `H.𝔟_spec.1`. Rewrite using `[h, FractionalIdeal.coeIdeal_mul, ← mul_assoc, mul_comm H.AA0, half_mul_inv, one_mul]`.
-/
theorem inv_mul_different :
    H.AA0 * ((differentIdeal (𝓞 H.K) (𝓞 H.E) : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) =
      ((H.conj • H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) := by
  have h : differentIdeal (𝓞 H.K) (𝓞 H.E) = H.𝔟 * (H.conj • H.𝔟) := H.𝔟_spec.1
  rw [h, FractionalIdeal.coeIdeal_mul, ← mul_assoc, mul_comm H.AA0, half_mul_inv, one_mul]

/- English proof (translation)
Rewrite using `[inv_mul_different, FractionalIdeal.mem_coeIdeal]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc, rfl⟩`. Rewrite `hc` using `[Ideal.pointwise_smul_def]`. Take `⟨b, hb, rfl⟩` from `(Ideal.mem_map_iff_of_surjective _ (MulSemiringAction.toRingEquiv _ (𝓞 H.E) H.conj).surjective).1 hc`.

Conclude with `⟨b, hb, rfl⟩`. Introduce and unpack `⟨b, hb, rfl⟩`. Conclude with `⟨H.conj • b, Ideal.smul_mem_pointwise_smul _ _ _ hb, rfl⟩`.
-/
theorem mem_inv_mul_different (x : H.E) :
    x ∈ H.AA0 * ((differentIdeal (𝓞 H.K) (𝓞 H.E) : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) ↔
      ∃ b ∈ H.𝔟, x = H.conj ((b : 𝓞 H.E) : H.E) := by
  rw [inv_mul_different, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [Ideal.pointwise_smul_def] at hc
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _
      (MulSemiringAction.toRingEquiv _ (𝓞 H.E) H.conj).surjective).1 hc
    exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨H.conj • b, Ideal.smul_mem_pointwise_smul _ _ _ hb, rfl⟩

/- English proof (translation)
Use `FractionalIdeal.mul_induction_on hx ?_ ?_` and prove the remaining obligations. Introduce `i hi j hj`. Take `⟨b, hb, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hj`. Conclude with `Submodule.subset_span ⟨i, hi, b, hb, rfl⟩`. Introduce `a b ha hb`.

Rewrite using `[map_add, map_add]`. Conclude with `Submodule.add_mem _ ha hb`.
-/
theorem map_mem_ellLat {LL : Type} [Field LL] [NumberField LL] (embE : H.E →+* LL)
    (g : R.GG) (x : H.E)
    (hx : x ∈ H.AA0 * ((differentIdeal (𝓞 H.K) (𝓞 H.E) : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E)) :
    embE (H.sigmaOf g x) ∈ ellLat H embE g := by
  refine FractionalIdeal.mul_induction_on hx ?_ ?_
  · intro i hi j hj
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hj
    exact Submodule.subset_span ⟨i, hi, b, hb, rfl⟩
  · intro a b ha hb
    rw [map_add, map_add]
    exact Submodule.add_mem _ ha hb

/- English proof (translation)
Introduce `D M _ embE hE τ`. Establish `hτ : ∀ (τ : D.what₂.Tau) x, embT D τ x = ((embE (D.host.sigmaOf (D.eTau τ).1 x) : M) : ℂ)`. Introduce `τ x`. Rewrite using `[hE]`. Both sides reduce to the same expression.

Establish `hM : ∀ τ x, embT D τ x ∈ M` using `fun τ x => by`. Rewrite using `[hτ]`. Conclude with `Subtype.property _`. Set `φ : D.host.E →+* M` to `embE.comp (((D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E)).comp (D.host.conj : D.host.E →+* D.host.E))`. Establish `hφ : ∀ y, φ y = embE (D.host.sigmaOf (D.eTau τ).1 (D.host.conj y))` using `fun _ => rfl`.

Establish `hone` using `half_mul_inv D.host`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx` using `[GlobalTheory.Glob.mem_ellT_iff hM]`. Establish `key : ∀ z ∈ ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) * D.host.AA0, x * φ z ∈ ellLat D.host embE (D.eTau τ).1`.

Introduce `z hz`. Use `FractionalIdeal.mul_induction_on hz ?_ ?_` and prove the remaining obligations. Introduce `i hi j hj`. Take `⟨b, hb, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hi`. Establish `hint : IsIntegral ℤ (x * φ j)`.

Use `(isIntegral_algHom_iff (M.val.toRingHom.toIntAlgHom) M.val.injective).1 ?_` and prove the remaining obligations. Use `hx j hj` as an intermediate fact. Rewrite `this` using `[hτ]`. Conclude with `this`. Set `c : 𝓞 M` to `⟨x * φ j, hint⟩`.

Establish `: c • φ (b : D.host.E) ∈ ellLat D.host embE (D.eTau τ).1` using `Submodule.smul_mem _ _ (map_mem_ellLat D.host embE _ _ ((mem_inv_mul_different D.host _).2 ⟨b, hb, rfl⟩))`. Use `this using 1` and compare the differences between its conclusion and the goal. Express the relevant statement in the definitionally equal form `x * φ (b * j) = x * φ j * φ b`. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `a b ha hb`. Rewrite using `[map_add, mul_add]`. Conclude with `Submodule.add_mem _ ha hb`. Use `key 1 (hone ▸ FractionalIdeal.one_mem_one _)` as an intermediate fact. Simplify using `using this`.

Unfold `ellLat`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `x ⟨a, ha, d, hd, rfl⟩`. Take `⟨b, hb, hab⟩` from `(mem_inv_mul_different D.host (a * (d : D.host.E))).1 (FractionalIdeal.mul_mem_mul ha ((FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩))`. Rewrite using `[SetLike.mem_coe, GlobalTheory.Glob.mem_ellT_iff hM]`.

Introduce `y hy`. Establish `h1 : (b : D.host.E) * y ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)` using `hone ▸ FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨b, hb, rfl⟩) hy`. Take `⟨r, hr⟩` from `(FractionalIdeal.mem_one_iff _).1 h1`. Rewrite using `[← hτ, hab, ← map_mul, ← map_mul, ← hr]`. Conclude with `map_isIntegral_int ((embT D τ).comp (D.host.conj : D.host.E →+* D.host.E)) r.isIntegral_coe`.
-/
theorem ellT_eq_ellLat : ∀ (D : D7) (M : IntermediateField ℚ ℂ) [NumberField M] (embE : D.host.E →+* M),
    (∀ x, ((embE x : M) : ℂ) = D.host.φ₀ x) → ∀ τ : D.what₂.Tau,
      ellT D M τ = ellLat D.host embE (D.eTau τ).1 := by
  intro D M _ embE hE τ
  have hτ : ∀ (τ : D.what₂.Tau) x, embT D τ x = ((embE (D.host.sigmaOf (D.eTau τ).1 x) : M) : ℂ) := by
    intro τ x
    rw [hE]
    rfl
  have hM : ∀ τ x, embT D τ x ∈ M := fun τ x => by
    rw [hτ]
    exact Subtype.property _
  let φ : D.host.E →+* M := embE.comp (((D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E)).comp
    (D.host.conj : D.host.E →+* D.host.E))
  have hφ : ∀ y, φ y = embE (D.host.sigmaOf (D.eTau τ).1 (D.host.conj y)) := fun _ => rfl
  have hone := half_mul_inv D.host
  apply le_antisymm
  · intro x hx
    rw [GlobalTheory.Glob.mem_ellT_iff hM] at hx
    have key : ∀ z ∈ ((D.host.𝔟 : Ideal (𝓞 D.host.E)) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) * D.host.AA0,
        x * φ z ∈ ellLat D.host embE (D.eTau τ).1 := by
      intro z hz
      refine FractionalIdeal.mul_induction_on hz ?_ ?_
      · intro i hi j hj
        obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hi
        have hint : IsIntegral ℤ (x * φ j) := by
          refine (isIntegral_algHom_iff (M.val.toRingHom.toIntAlgHom) M.val.injective).1 ?_
          have := hx j hj
          rw [hτ] at this
          exact this
        let c : 𝓞 M := ⟨x * φ j, hint⟩
        have : c • φ (b : D.host.E) ∈ ellLat D.host embE (D.eTau τ).1 :=
          Submodule.smul_mem _ _ (map_mem_ellLat D.host embE _ _
            ((mem_inv_mul_different D.host _).2 ⟨b, hb, rfl⟩))
        convert this using 1
        change x * φ (b * j) = x * φ j * φ b
        rw [map_mul]; ring
      · intro a b ha hb
        rw [map_add, mul_add]
        exact Submodule.add_mem _ ha hb
    have := key 1 (hone ▸ FractionalIdeal.one_mem_one _)
    simpa using this
  · unfold ellLat
    rw [Submodule.span_le]
    rintro x ⟨a, ha, d, hd, rfl⟩
    obtain ⟨b, hb, hab⟩ := (mem_inv_mul_different D.host (a * (d : D.host.E))).1
      (FractionalIdeal.mul_mem_mul ha ((FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩))
    rw [SetLike.mem_coe, GlobalTheory.Glob.mem_ellT_iff hM]
    intro y hy
    have h1 : (b : D.host.E) * y ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
      hone ▸ FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨b, hb, rfl⟩) hy
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [← hτ, hab, ← map_mul, ← map_mul, ← hr]
    exact map_isIntegral_int ((embT D τ).comp (D.host.conj : D.host.E →+* D.host.E)) r.isIntegral_coe

end GlobalTheory.Mem.EigenLine
