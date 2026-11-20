import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.FexTheta

/- English proof (translation)
Establish `key : ∀ x : (Qv v)ˣ, ((x : Qv v) ∈ 𝒪[Qv v]) ↔ 0 ≤ ord (x : Qv v)`. Introduce `x`. Establish `h : ((x : Qv v) ∈ (𝒪[Qv v] : Set (Qv v))) ↔ (x : Qv v) ∈ (valBall (Qv v) 0 : Set (Qv v))` using `by rw [coe_valBall_zero]`. Conclude with `h.trans (mem_valBall_iff_le_ord x.ne_zero)`. Use `show ((w : Qv v) ∈ 𝒪[Qv v] ∧ ((w⁻¹ : (Qv v)ˣ) : Qv v) ∈ 𝒪[Qv v]) ↔ _`.

Rewrite using `[key, key, ord_units_inv]`. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_unQ_iff_ord_eq_zero {v : Pl} (w : (Qv v)ˣ) :
    w ∈ unQ v ↔ ord ((w : (Qv v)ˣ) : Qv v) = 0 := by
  have key : ∀ x : (Qv v)ˣ, ((x : Qv v) ∈ 𝒪[Qv v]) ↔ 0 ≤ ord (x : Qv v) := by
    intro x
    have h : ((x : Qv v) ∈ (𝒪[Qv v] : Set (Qv v))) ↔
        (x : Qv v) ∈ (valBall (Qv v) 0 : Set (Qv v)) := by rw [coe_valBall_zero]
    exact h.trans (mem_valBall_iff_le_ord x.ne_zero)
  show ((w : Qv v) ∈ 𝒪[Qv v] ∧ ((w⁻¹ : (Qv v)ˣ) : Qv v) ∈ 𝒪[Qv v]) ↔ _
  rw [key, key, ord_units_inv]
  omega

/- English proof (translation)
Establish `h` using `(measurePreserving_mul_left (multHaar (Qv v)) e).restrict_preimage_emb (MeasurableEquiv.mulLeft e).measurableEmbedding (unQ v)`. Establish `hs : (fun x : (Qv v)ˣ => e * x) ⁻¹' unQ v = unQ v`. Use extensionality with `x`. Establish `he0` using `(mem_unQ_iff_ord_eq_zero e).1 he`. Simplify using `only [Set.mem_preimage, mem_unQ_iff_ord_eq_zero, ord_units_mul, he0, zero_add]`.

Rewrite `h` using `[hs]`. Conclude with `h`.
-/
theorem measurePreserving_mulLeft_unQ (v : Pl) (e : (Qv v)ˣ) (he : e ∈ unQ v) :
    MeasurePreserving (MeasurableEquiv.mulLeft e) ((multHaar (Qv v)).restrict (unQ v))
      ((multHaar (Qv v)).restrict (unQ v)) := by
  have h := (measurePreserving_mul_left (multHaar (Qv v)) e).restrict_preimage_emb
    (MeasurableEquiv.mulLeft e).measurableEmbedding (unQ v)
  have hs : (fun x : (Qv v)ˣ => e * x) ⁻¹' unQ v = unQ v := by
    ext x
    have he0 := (mem_unQ_iff_ord_eq_zero e).1 he
    simp only [Set.mem_preimage, mem_unQ_iff_ord_eq_zero, ord_units_mul, he0, zero_add]
  rw [hs] at h
  exact h

/- English proof (translation)
Establish `h : p ^ b * p ^ (-b) = 1` using `by rw [← zpow_add]; simp`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[zpow_add]`. The two sides agree by associativity and commutativity. Use `_ = p ^ a * u * k := by rw [h, mul_one]`.
-/
theorem zpow_shift_mul_rearrange {G : Type*} [CommGroup G] (p k u : G) (a b : ℤ) :
    p ^ (a + b) * (k * p ^ (-b) * u) = p ^ a * u * k := by
  have h : p ^ b * p ^ (-b) = 1 := by rw [← zpow_add]; simp
  calc p ^ (a + b) * (k * p ^ (-b) * u) = p ^ a * u * k * (p ^ b * p ^ (-b)) := by
        rw [zpow_add]; ac_rfl
    _ = p ^ a * u * k := by rw [h, mul_one]

/- English proof (translation)
Simplify using `using (zpow_shift_mul_rearrange p k 1 a b).symm`.
-/
theorem zpow_shift_one_rearrange {G : Type*} [CommGroup G] (p k : G) (a b : ℤ) :
    p ^ a * k = p ^ (a + b) * (k * p ^ (-b)) := by
  simpa using (zpow_shift_mul_rearrange p k 1 a b).symm

def shiftEquiv (Sv : Finset Pl) (e : ∀ v : Pl, (Qv v)ˣ) :
    (∀ v : Sv, (Qv v.1)ˣ) ≃ᵐ (∀ v : Sv, (Qv v.1)ˣ) :=
  MeasurableEquiv.piCongrRight fun v => MeasurableEquiv.mulLeft (e v.1)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem shiftEquiv_apply (Sv : Finset Pl) (e : ∀ v : Pl, (Qv v)ˣ) (u : ∀ v : Sv, (Qv v.1)ˣ) (v : Sv) :
    shiftEquiv Sv e u v = e v.1 * u v := rfl

/- English proof (translation)
Establish `h` using `measurePreserving_pi (fun v : Sv => (multHaar (Qv v.1)).restrict (unQ v.1)) (fun v : Sv => (multHaar (Qv v.1)).restrict (unQ v.1)) (f := fun v : Sv => (MeasurableEquiv.mulLeft (e v.1) : (Qv v.1)ˣ → (Qv v.1)ˣ)) fun v => measurePreserving_mulLeft_unQ v.1 (e v.1) (he v.1)`. Conclude with `h`.
-/
theorem measurePreserving_shiftEquiv (Sv : Finset Pl) (e : ∀ v : Pl, (Qv v)ˣ) (he : ∀ v, e v ∈ unQ v) :
    MeasurePreserving (shiftEquiv Sv e) (muU Sv) (muU Sv) := by
  have h := measurePreserving_pi (fun v : Sv => (multHaar (Qv v.1)).restrict (unQ v.1))
    (fun v : Sv => (multHaar (Qv v.1)).restrict (unQ v.1))
    (f := fun v : Sv => (MeasurableEquiv.mulLeft (e v.1) : (Qv v.1)ˣ → (Qv v.1)ˣ))
    fun v => measurePreserving_mulLeft_unQ v.1 (e v.1) (he v.1)
  exact h

/- English proof (translation)
Establish `h0 : shiftEquiv Sv e u ⟨v, hv⟩ = e v * u ⟨v, hv⟩` using `shiftEquiv_apply Sv e u ⟨v, hv⟩`. Simplify using `only [tu, dif_pos hv, h0, Finsupp.add_apply, hek]`. Conclude with `zpow_shift_mul_rearrange _ _ _ _ _`.
-/
theorem tu_shift_mem (Sv : Finset Pl) (e k : ∀ v : Pl, (Qv v)ˣ) (m' m : Pl →₀ ℤ)
    (hek : ∀ v, e v = k v * unifUnit (Qv v) ^ (-(m' v))) (u : ∀ v : Sv, (Qv v.1)ˣ) {v : Pl} (hv : v ∈ Sv) :
    tu Sv (m + m') (shiftEquiv Sv e u) v = tu Sv m u v * k v := by
  have h0 : shiftEquiv Sv e u ⟨v, hv⟩ = e v * u ⟨v, hv⟩ := shiftEquiv_apply Sv e u ⟨v, hv⟩
  simp only [tu, dif_pos hv, h0, Finsupp.add_apply, hek]
  exact zpow_shift_mul_rearrange _ _ _ _ _

/- English proof (translation)
Simplify using `only [tu, dif_neg hv, mul_one, Finsupp.add_apply, hek]`. Conclude with `zpow_shift_one_rearrange _ _ _ _`.
-/
theorem tu_shift_not_mem (Sv : Finset Pl) (e k : ∀ v : Pl, (Qv v)ˣ) (m' m : Pl →₀ ℤ)
    (hek : ∀ v, e v = k v * unifUnit (Qv v) ^ (-(m' v))) (u : ∀ v : Sv, (Qv v.1)ˣ) {v : Pl} (hv : v ∉ Sv) :
    tu Sv m u v * k v = tu Sv (m + m') (shiftEquiv Sv e u) v * e v := by
  simp only [tu, dif_neg hv, mul_one, Finsupp.add_apply, hek]
  exact zpow_shift_one_rearrange _ _ _ _

/- English proof (translation)
Take `⟨e, hek⟩ : ∃ e : ∀ v : Pl, (Qv v)ˣ, ∀ v, e v = k v * unifUnit (Qv v) ^ (-(m' v))` from `⟨_, fun _ => rfl⟩`. Establish `heU : ∀ v, e v ∈ unQ v`. Introduce `v`. Rewrite using `[mem_unQ_iff_ord_eq_zero, hek, ord_units_mul, ord_unifUnit_zpow, hk]`. Use linear arithmetic over natural numbers and integers.

Establish `hΦ` using `measurePreserving_shiftEquiv Sv e heU`. Rewrite using `[← hΦ.integral_comp' (fun u => ∏ᶠ v, f v (tu Sv (m + m') u v))]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Use `finprod_congr fun v => ?_` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ Sv`.

Rewrite using `[tu_shift_mem Sv e k m' m hek u hv]`. Rewrite using `[tu_shift_not_mem Sv e k m' m hek u hv, hinv v hv _ _ (heU v)]`.
-/
theorem torusAverage_shift (Sv : Finset Pl) (f : ∀ v : Pl, (Qv v)ˣ → ℂ)
    (hinv : ∀ v ∉ Sv, ∀ x, ∀ e ∈ unQ v, f v (x * e) = f v x)
    (k : ∀ v : Pl, (Qv v)ˣ) (m' : Pl →₀ ℤ) (hk : ∀ v, ord ((k v : (Qv v)ˣ) : Qv v) = m' v)
    (m : Pl →₀ ℤ) :
    ∫ u, ∏ᶠ v, f v (tu Sv m u v * k v) ∂muU Sv = ∫ u, ∏ᶠ v, f v (tu Sv (m + m') u v) ∂muU Sv := by
  obtain ⟨e, hek⟩ : ∃ e : ∀ v : Pl, (Qv v)ˣ, ∀ v, e v = k v * unifUnit (Qv v) ^ (-(m' v)) := ⟨_, fun _ => rfl⟩
  have heU : ∀ v, e v ∈ unQ v := by
    intro v
    rw [mem_unQ_iff_ord_eq_zero, hek, ord_units_mul, ord_unifUnit_zpow, hk]
    omega
  have hΦ := measurePreserving_shiftEquiv Sv e heU
  rw [← hΦ.integral_comp' (fun u => ∏ᶠ v, f v (tu Sv (m + m') u v))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  refine finprod_congr fun v => ?_
  by_cases hv : v ∈ Sv
  · rw [tu_shift_mem Sv e k m' m hek u hv]
  · rw [tu_shift_not_mem Sv e k m' m hek u hv, hinv v hv _ _ (heU v)]

end GlobalTheory.CompanionTheory.FexTheta
