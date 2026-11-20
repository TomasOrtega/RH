import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import GroundTheory.GlobalFields.TateThesis.ArchCharsUnitary
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CentralChar

variable {n : ℕ}

/- English proof (translation)
Use `show Formalism.REAL.inUJ ε _`. Unfold `Formalism.REAL.inUJ`. Rewrite using `[conjTranspose_smul, conjTranspose_one, smul_mul_assoc, Matrix.one_mul, mul_smul_comm, Matrix.mul_one, smul_smul]`. Establish `: z * star z = 1`. Rewrite using `[RCLike.star_def, RCLike.mul_conj, hz]`.

Simplify using the standard rewrite rules. Rewrite using `[this, one_smul]`.
-/
theorem smul_one_mem (ε : Fin n → Bool) {z : ℂ} (hz : ‖z‖ = 1) :
    (z • (1 : Matrix (Fin n) (Fin n) ℂ)) ∈ UJset ε := by
  show Formalism.REAL.inUJ ε _
  unfold Formalism.REAL.inUJ
  rw [conjTranspose_smul, conjTranspose_one, smul_mul_assoc, Matrix.one_mul, mul_smul_comm,
    Matrix.mul_one, smul_smul]
  have : z * star z = 1 := by
    rw [RCLike.star_def, RCLike.mul_conj, hz]; simp
  rw [this, one_smul]

/- English proof (translation)
Establish `hg' : gᴴ * Jm ε * g = Jm ε` using `hg`. Establish `hl : (Jm ε * gᴴ * Jm ε) * g = 1`. Combine the equalities or inequalities in the displayed calculation. Establish `hr : g * (Jm ε * gᴴ * Jm ε) = 1` using `mul_eq_one_comm.mp hl`. Use `⟨hl, hr, ?_⟩` and prove the remaining obligations.

Use `show (Jm ε * gᴴ * Jm ε)ᴴ * Jm ε * (Jm ε * gᴴ * Jm ε) = Jm ε`. Rewrite using `[conjTranspose_mul, conjTranspose_mul, Jm_conjTranspose, conjTranspose_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem inv_facts (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    (Jm ε * gᴴ * Jm ε) * g = 1 ∧ g * (Jm ε * gᴴ * Jm ε) = 1 ∧ (Jm ε * gᴴ * Jm ε) ∈ UJset ε := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hl : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    calc (Jm ε * gᴴ * Jm ε) * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', Jm_mul_self]
  have hr : g * (Jm ε * gᴴ * Jm ε) = 1 := mul_eq_one_comm.mp hl
  refine ⟨hl, hr, ?_⟩
  show (Jm ε * gᴴ * Jm ε)ᴴ * Jm ε * (Jm ε * gᴴ * Jm ε) = Jm ε
  rw [conjTranspose_mul, conjTranspose_mul, Jm_conjTranspose, conjTranspose_conjTranspose]
  calc Jm ε * (g * Jm ε) * Jm ε * (Jm ε * gᴴ * Jm ε)
      = Jm ε * (g * (Jm ε * Jm ε) * (Jm ε * gᴴ * Jm ε)) := by simp only [Matrix.mul_assoc]
    _ = Jm ε * (g * (Jm ε * gᴴ * Jm ε)) := by rw [Jm_mul_self, Matrix.mul_one]
    _ = Jm ε := by rw [hr, Matrix.mul_one]

/- English proof (translation)
Introduce `n _ ε H _ _ σ hc hnt hrep hirr`. Take `⟨⟨h1, hmul⟩, hiso, hcont⟩` from `hrep`. Establish `hstar : ∀ g ∈ UJset ε, star (σ g) = σ (Jm ε * gᴴ * Jm ε)`. Introduce `g hg`. Take `⟨-, hr, hm⟩` from `inv_facts ε hg`.

Rewrite using `[ContinuousLinearMap.star_eq_adjoint]`. Use `symm`. Rewrite using `[ContinuousLinearMap.eq_adjoint_iff]`. Introduce `x y`. Set `L : H →ₗᵢ[ℂ] H` to `⟨(σ g).toLinearMap, hiso g hg⟩`.

Establish `hx : σ g (σ (Jm ε * gᴴ * Jm ε) x) = x`. Rewrite using `[← ContinuousLinearMap.comp_apply, ← hmul g hg _ hm, hr, h1]`. Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hx]`.

Establish `hscal : ∀ z : ℂ, ‖z‖ = 1 → ∃ c : ℂ, σ (z • 1) = c • (1 : H →L[ℂ] H)`. Introduce `z hz`. Apply `Formalism.MainNotions.BridgeCSchur.schur_bounded (σ '' UJset ε)` to reduce the goal to its premises. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Conclude with `⟨_, (inv_facts ε hg).2.2, (hstar g hg).symm⟩`.

Introduce `S hS hst`. Conclude with `hirr S hS (fun g hg v hv => hst _ ⟨g, hg, rfl⟩ v hv)`. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Establish `hz1` using `smul_one_mem ε hz`. Use `show σ (z • 1) * σ g = σ g * σ (z • 1)`.

Rewrite using `[ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, ← hmul _ hz1 _ hg, ← hmul _ hg _ hz1, smul_mul_assoc, Matrix.one_mul, mul_smul_comm, Matrix.mul_one]`. Take `⟨v0, hv0⟩` from `exists_ne (0 : H)`. Set `χ : ℂ → ℂ` to `fun z => ⟪v0, σ (z • 1) v0⟫_ℂ / ⟪v0, v0⟫_ℂ`. Establish `hvv : ⟪v0, v0⟫_ℂ ≠ 0` using `inner_self_ne_zero.mpr hv0`. Establish `hχ : ∀ z : ℂ, ‖z‖ = 1 → σ (z • 1) = χ z • (1 : H →L[ℂ] H)`.

Introduce `z hz`. Take `⟨c, hc'⟩` from `hscal z hz`. Establish `: χ z = c`. Simplify using `only [χ, hc', ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_right]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this, hc']`. Establish `hχv : ∀ z : ℂ, ‖z‖ = 1 → σ (z • 1) v0 = χ z • v0`. Introduce `z hz`. Rewrite using `[hχ z hz]`. Both sides reduce to the same expression.

Establish `hnorm : ∀ z : ℂ, ‖z‖ = 1 → ‖χ z‖ = 1`. Introduce `z hz`. Establish `h` using `hiso _ (smul_one_mem ε hz) v0`. Rewrite `h` using `[hχv z hz, norm_smul]`. Establish `hp : 0 < ‖v0‖` using `norm_pos_iff.mpr hv0`.

Use polynomial arithmetic with `[h]`. Establish `hne : ∀ w : Circle, χ w ≠ 0`. Introduce `w h0`. Use `hnorm w (Circle.norm_coe _)` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`.

Conclude with `zero_ne_one this`. Establish `hcontχ : Continuous fun w : Circle => χ w`. Establish `hc1 : Continuous fun w : Circle => σ ((w : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) v0` using `(hcont v0).comp_continuous (by fun_prop) (fun w => smul_one_mem ε (Circle.norm_coe _))`. Conclude with `(continuous_const.inner hc1).div_const _`. Set `χU : Circle →ₜ* ℂˣ` to `{ toFun := fun w => Units.mk0 (χ w) (hne w) map_one' := by`.

Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mk0, Units.val_one, Circle.coe_one, χ, one_smul, h1, ContinuousLinearMap.one_apply]`. Conclude with `div_self hvv`. Use the proof step `map_mul' := by`. Introduce `a b`.

Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mk0, Units.val_mul]`. Establish `ha` using `smul_one_mem ε (z := (a : ℂ)) (Circle.norm_coe _)`. Establish `hb` using `smul_one_mem ε (z := (b : ℂ)) (Circle.norm_coe _)`. Establish `hab : σ (((a * b : Circle) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) v0 = (χ a * χ b) • v0`.

Rewrite using `[Circle.coe_mul, show ((a : ℂ) * b) • (1 : Matrix (Fin n) (Fin n) ℂ) = ((a : ℂ) • 1) * ((b : ℂ) • 1) by rw [smul_mul_smul_comm, Matrix.one_mul], hmul _ ha _ hb, ContinuousLinearMap.comp_apply, hχv _ (Circle.norm_coe b), map_smul, hχv _ (Circle.norm_coe a), smul_smul, mul_comm]`. Rewrite `hab` using `[hχv _ (Circle.norm_coe (a * b))]`. Conclude with `smul_left_injective ℂ hv0 hab`. Use `continuous_toFun := by`. Rewrite using `[Units.continuous_iff]`.

Use `⟨hcontχ, ?_⟩` and prove the remaining obligations. Simplify using `only [Units.val_inv_eq_inv_val, Units.val_mk0]`. Conclude with `hcontχ.inv₀ hne }`. Take `⟨m, hm, -⟩` from `GroundTheory.Global.existsUnique_circle_zpow χU`. Use `⟨m, fun z hz g hg => ?_⟩` and prove the remaining obligations.

Establish `hz1` using `smul_one_mem ε hz`. Establish `hw : ((Circle.exp (Complex.arg z) : Circle) : ℂ) = z`. Rewrite using `[Circle.coe_exp]`. Use `Complex.norm_mul_exp_arg_mul_I z` as an intermediate fact. Rewrite `this` using `[hz]`.

Simplify using `using this`. Establish `hχz : χ z = z ^ m`. Establish `: χ ((Circle.exp (Complex.arg z) : Circle) : ℂ) = ((Circle.exp (Complex.arg z) : Circle) : ℂ) ^ m` using `hm (Circle.exp (Complex.arg z))`. Rewrite `this` using `[hw]`. Then use the resulting hypothesis. Rewrite using `[show z • g = (z • (1 : Matrix (Fin n) (Fin n) ℂ)) * g by rw [smul_mul_assoc, Matrix.one_mul], hmul _ hz1 _ hg.1, hχ z hz, hχz]`.

Use extensionality with `v`. Both sides reduce to the same expression.
-/
theorem central_char : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), CompleteSpace H →
    Nontrivial H → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∃ m : ℤ, Ext ε m σ σ := by
  intro n _ ε H _ _ σ hc hnt hrep hirr
  obtain ⟨⟨h1, hmul⟩, hiso, hcont⟩ := hrep
  have hstar : ∀ g ∈ UJset ε, star (σ g) = σ (Jm ε * gᴴ * Jm ε) := by
    intro g hg
    obtain ⟨-, hr, hm⟩ := inv_facts ε hg
    rw [ContinuousLinearMap.star_eq_adjoint]
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    let L : H →ₗᵢ[ℂ] H := ⟨(σ g).toLinearMap, hiso g hg⟩
    have hx : σ g (σ (Jm ε * gᴴ * Jm ε) x) = x := by
      rw [← ContinuousLinearMap.comp_apply, ← hmul g hg _ hm, hr, h1]; rfl
    calc ⟪σ (Jm ε * gᴴ * Jm ε) x, y⟫_ℂ = ⟪L (σ (Jm ε * gᴴ * Jm ε) x), L y⟫_ℂ :=
          (L.inner_map_map _ _).symm
      _ = ⟪x, σ g y⟫_ℂ := by
          show ⟪σ g (σ (Jm ε * gᴴ * Jm ε) x), σ g y⟫_ℂ = _
          rw [hx]
  have hscal : ∀ z : ℂ, ‖z‖ = 1 → ∃ c : ℂ, σ (z • 1) = c • (1 : H →L[ℂ] H) := by
    intro z hz
    apply Formalism.MainNotions.BridgeCSchur.schur_bounded (σ '' UJset ε)
    · rintro _ ⟨g, hg, rfl⟩; exact ⟨_, (inv_facts ε hg).2.2, (hstar g hg).symm⟩
    · intro S hS hst; exact hirr S hS (fun g hg v hv => hst _ ⟨g, hg, rfl⟩ v hv)
    · rintro _ ⟨g, hg, rfl⟩
      have hz1 := smul_one_mem ε hz
      show σ (z • 1) * σ g = σ g * σ (z • 1)
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, ← hmul _ hz1 _ hg,
        ← hmul _ hg _ hz1, smul_mul_assoc, Matrix.one_mul, mul_smul_comm, Matrix.mul_one]
  obtain ⟨v0, hv0⟩ := exists_ne (0 : H)
  let χ : ℂ → ℂ := fun z => ⟪v0, σ (z • 1) v0⟫_ℂ / ⟪v0, v0⟫_ℂ
  have hvv : ⟪v0, v0⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hv0
  have hχ : ∀ z : ℂ, ‖z‖ = 1 → σ (z • 1) = χ z • (1 : H →L[ℂ] H) := by
    intro z hz
    obtain ⟨c, hc'⟩ := hscal z hz
    have : χ z = c := by
      simp only [χ, hc', ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
        inner_smul_right]
      field_simp
    rw [this, hc']
  have hχv : ∀ z : ℂ, ‖z‖ = 1 → σ (z • 1) v0 = χ z • v0 := by
    intro z hz; rw [hχ z hz]; rfl
  have hnorm : ∀ z : ℂ, ‖z‖ = 1 → ‖χ z‖ = 1 := by
    intro z hz
    have h := hiso _ (smul_one_mem ε hz) v0
    rw [hχv z hz, norm_smul] at h
    have hp : 0 < ‖v0‖ := norm_pos_iff.mpr hv0
    nlinarith [h]
  have hne : ∀ w : Circle, χ w ≠ 0 := by
    intro w h0
    have := hnorm w (Circle.norm_coe _)
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have hcontχ : Continuous fun w : Circle => χ w := by
    have hc1 : Continuous fun w : Circle => σ ((w : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) v0 :=
      (hcont v0).comp_continuous (by fun_prop) (fun w => smul_one_mem ε (Circle.norm_coe _))
    exact (continuous_const.inner hc1).div_const _
  let χU : Circle →ₜ* ℂˣ :=
    { toFun := fun w => Units.mk0 (χ w) (hne w)
      map_one' := by
        apply Units.ext
        simp only [Units.val_mk0, Units.val_one, Circle.coe_one, χ, one_smul, h1,
          ContinuousLinearMap.one_apply]
        exact div_self hvv
      map_mul' := by
        intro a b
        apply Units.ext
        simp only [Units.val_mk0, Units.val_mul]
        have ha := smul_one_mem ε (z := (a : ℂ)) (Circle.norm_coe _)
        have hb := smul_one_mem ε (z := (b : ℂ)) (Circle.norm_coe _)
        have hab : σ (((a * b : Circle) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) v0
            = (χ a * χ b) • v0 := by
          rw [Circle.coe_mul, show ((a : ℂ) * b) • (1 : Matrix (Fin n) (Fin n) ℂ) =
            ((a : ℂ) • 1) * ((b : ℂ) • 1) by rw [smul_mul_smul_comm, Matrix.one_mul], hmul _ ha _ hb,
            ContinuousLinearMap.comp_apply, hχv _ (Circle.norm_coe b), map_smul, hχv _ (Circle.norm_coe a),
            smul_smul, mul_comm]
        rw [hχv _ (Circle.norm_coe (a * b))] at hab
        exact smul_left_injective ℂ hv0 hab
      continuous_toFun := by
        rw [Units.continuous_iff]
        refine ⟨hcontχ, ?_⟩
        simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
        exact hcontχ.inv₀ hne }
  obtain ⟨m, hm, -⟩ := GroundTheory.Global.existsUnique_circle_zpow χU
  refine ⟨m, fun z hz g hg => ?_⟩
  have hz1 := smul_one_mem ε hz
  have hw : ((Circle.exp (Complex.arg z) : Circle) : ℂ) = z := by
    rw [Circle.coe_exp]
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hz] at this; simpa using this
  have hχz : χ z = z ^ m := by
    have : χ ((Circle.exp (Complex.arg z) : Circle) : ℂ) = ((Circle.exp (Complex.arg z) : Circle) : ℂ) ^ m :=
      hm (Circle.exp (Complex.arg z))
    rwa [hw] at this
  rw [show z • g = (z • (1 : Matrix (Fin n) (Fin n) ℂ)) * g by rw [smul_mul_assoc, Matrix.one_mul],
    hmul _ hz1 _ hg.1, hχ z hz, hχz]
  ext v
  rfl

end GlobalTheory.CentralChar
