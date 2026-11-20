import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDerivWeierstrassPHalfPeriodsDiscriminantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotMemHalfLatticeOfOddMultiplierStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivWeierstrassPMulProdTranslateKernelStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

/- English proof (translation)
Introduce `L α S hα hst hS hev`. Take `⟨a, ha⟩ : ∃ a : ℂ, a = L.ω₁ / 2` from `⟨_, rfl⟩`. Take `⟨b, hb⟩ : ∃ b : ℂ, b = L.ω₂ / 2` from `⟨_, rfl⟩`. Take `⟨z, hz⟩ : ∃ z : ℂ, z = L.ω₁ / (4 * α)` from `⟨_, rfl⟩`. Establish `haL : a ∉ L.lattice` using `ha ▸ L.ω₁_div_two_notMem_lattice`.

Establish `hbL : b ∉ L.lattice` using `hb ▸ L.ω₂_div_two_notMem_lattice`. Establish `habL : a + b ∉ L.lattice`. Introduce `h`. Use `(PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice (L := L) (α := 1 / 2) (β := 1 / 2)).mp (by convert h using 1; rw [ha, hb]; push_cast; ring)` as an intermediate fact. Evaluate the numerical expressions using `at this`.

Establish `ha2 : 2 * a ∈ L.lattice`. Establish `: 2 * a = L.ω₁` using `by rw [ha]; ring`. Rewrite using `[this]`. Conclude with `L.ω₁_mem_lattice`. Establish `hb2 : 2 * b ∈ L.lattice`.

Establish `: 2 * b = L.ω₂` using `by rw [hb]; ring`. Rewrite using `[this]`. Conclude with `L.ω₂_mem_lattice`. Establish `hab2 : 2 * (a + b) ∈ L.lattice`. Rewrite using `[mul_add]`.

Conclude with `add_mem ha2 hb2`. Establish `hz2 : 2 * (α * z) ∉ L.lattice`. Establish `: 2 * (α * z) = L.ω₁ / 2` using `by rw [hz]; field_simp; ring`. Rewrite using `[this]`. Conclude with `L.ω₁_div_two_notMem_lattice`.

Establish `two : ∀ x, x ∈ L.lattice → 2 * x ∈ L.lattice` using `fun x hx => by`. Rewrite using `[two_mul]`. Conclude with `add_mem hx hx`. Establish `hshift : ∀ c, 2 * c ∈ L.lattice → α * (z + c) ∉ L.lattice`. Introduce `c hc h`.

Apply `hz2` to reduce the goal to its premises. Use `sub_mem (two _ h) (hst _ hc)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `hz1 : α * z ∉ L.lattice` using `fun h => hz2 (two _ h)`.

Establish `hαc : ∀ c, 2 * c ∈ L.lattice → 2 * (α * c) ∈ L.lattice` using `fun c hc => by`. Use `hst _ hc` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `h0` using `GlobalTheory.T.derivWeierstrassP_mul_prod_translate_of_kernel_reps L α S hα hst hS hev z hz1`.

Establish `h1` using `GlobalTheory.T.derivWeierstrassP_mul_prod_translate_of_kernel_reps L α S hα hst hS hev (z + a) (hshift a ha2)`. Establish `h2` using `GlobalTheory.T.derivWeierstrassP_mul_prod_translate_of_kernel_reps L α S hα hst hS hev (z + b) (hshift b hb2)`. Establish `h3` using `GlobalTheory.T.derivWeierstrassP_mul_prod_translate_of_kernel_reps L α S hα hst hS hev (z + (a + b)) (hshift _ hab2)`. Establish `hzz : 2 * z ∉ L.lattice` using `fun h => hz2 (hαc z h)`. Establish `hL0` using `GlobalTheory.T.product_derivWeierstrassP_half_periods_discriminant L a b z haL hbL habL ha2 hb2 hzz`.

Establish `hLt : ∀ t ∈ S, L.derivWeierstrassP (z + t) * L.derivWeierstrassP (z + a + t) * L.derivWeierstrassP (z + b + t) * L.derivWeierstrassP (z + (a + b) + t) = (latticeCurve L).Δ`. Introduce `t ht`. Establish `h2t : 2 * (z + t) ∉ L.lattice`. Introduce `h`. Apply `hz2` to reduce the goal to its premises.

Use `sub_mem (hαc _ h) (two _ (hS.1 t ht).1)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Use `GlobalTheory.T.product_derivWeierstrassP_half_periods_discriminant L a b (z + t) haL hbL habL ha2 hb2 h2t` as an intermediate fact. Rewrite using `[← this, add_right_comm z a t, add_right_comm z b t, add_right_comm z (a + b) t]`.

Establish `hR` using `GlobalTheory.T.product_derivWeierstrassP_half_periods_discriminant L (α * a) (α * b) (α * z) (fun h => haL (GlobalTheory.T.not_mem_half_lattice_of_odd_multiplier L α a S hα hst hS hev h ha2)) (fun h => hbL (GlobalTheory.T.not_mem_half_lattice_of_odd_multiplier L α b S hα hst hS h …`. Rewrite `hR` using `[← mul_add α a b, ← mul_add, ← mul_add, ← mul_add]`. Establish `hP : (∏ t ∈ S, L.derivWeierstrassP (z + t)) * (∏ t ∈ S, L.derivWeierstrassP (z + a + t)) * (∏ t ∈ S, L.derivWeierstrassP (z + b + t)) * (∏ t ∈ S, L.derivWeierstrassP (z + (a + b) + t)) = (latticeCurve L).Δ ^ S.card`. Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, Finset.prod_congr rfl hLt, Finset.prod_const]`. Apply `mul_left_cancel₀ (latticeCurve_Δ_ne_zero L)` to reduce the goal to its premises.

Establish `hall` using `congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) h0 h1) h2) h3`. Rewrite using `[← hP]`. Use `nth_rewrite 1 [← hR]`. Rewrite using `[← hL0]`. Take the linear combination `-hall`.
-/
theorem prod_derivWeierstrassP_kerReps_pow_four_mul :
    ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
      Even S.card →
      (∏ t ∈ S, L.derivWeierstrassP t) ^ 4 * α ^ 12 = (latticeCurve L).Δ ^ S.card := by
  intro L α S hα hst hS hev
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = L.ω₁ / 2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℂ, b = L.ω₂ / 2 := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = L.ω₁ / (4 * α) := ⟨_, rfl⟩
  have haL : a ∉ L.lattice := ha ▸ L.ω₁_div_two_notMem_lattice
  have hbL : b ∉ L.lattice := hb ▸ L.ω₂_div_two_notMem_lattice
  have habL : a + b ∉ L.lattice := by
    intro h
    have := (PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice (L := L) (α := 1 / 2) (β := 1 / 2)).mp
      (by convert h using 1; rw [ha, hb]; push_cast; ring)
    norm_num at this
  have ha2 : 2 * a ∈ L.lattice := by
    have : 2 * a = L.ω₁ := by rw [ha]; ring
    rw [this]; exact L.ω₁_mem_lattice
  have hb2 : 2 * b ∈ L.lattice := by
    have : 2 * b = L.ω₂ := by rw [hb]; ring
    rw [this]; exact L.ω₂_mem_lattice
  have hab2 : 2 * (a + b) ∈ L.lattice := by
    rw [mul_add]; exact add_mem ha2 hb2
  have hz2 : 2 * (α * z) ∉ L.lattice := by
    have : 2 * (α * z) = L.ω₁ / 2 := by rw [hz]; field_simp; ring
    rw [this]; exact L.ω₁_div_two_notMem_lattice
  have two : ∀ x, x ∈ L.lattice → 2 * x ∈ L.lattice := fun x hx => by
    rw [two_mul]; exact add_mem hx hx
  have hshift : ∀ c, 2 * c ∈ L.lattice → α * (z + c) ∉ L.lattice := by
    intro c hc h
    apply hz2
    have := sub_mem (two _ h) (hst _ hc)
    convert this using 1; ring
  have hz1 : α * z ∉ L.lattice := fun h => hz2 (two _ h)
  have hαc : ∀ c, 2 * c ∈ L.lattice → 2 * (α * c) ∈ L.lattice := fun c hc => by
    have := hst _ hc
    convert this using 1; ring
  have h0 := GlobalTheory.T.derivWeierstrassP_mul_prod_translate_of_kernel_reps L α S hα hst hS hev z hz1
  have h1 := GlobalTheory.T.derivWeierstrassP_mul_prod_translate_of_kernel_reps L α S hα hst hS hev (z + a) (hshift a ha2)
  have h2 := GlobalTheory.T.derivWeierstrassP_mul_prod_translate_of_kernel_reps L α S hα hst hS hev (z + b) (hshift b hb2)
  have h3 := GlobalTheory.T.derivWeierstrassP_mul_prod_translate_of_kernel_reps L α S hα hst hS hev (z + (a + b)) (hshift _ hab2)
  have hzz : 2 * z ∉ L.lattice := fun h => hz2 (hαc z h)
  have hL0 := GlobalTheory.T.product_derivWeierstrassP_half_periods_discriminant L a b z haL hbL habL ha2 hb2 hzz
  have hLt : ∀ t ∈ S, L.derivWeierstrassP (z + t) * L.derivWeierstrassP (z + a + t)
      * L.derivWeierstrassP (z + b + t) * L.derivWeierstrassP (z + (a + b) + t)
        = (latticeCurve L).Δ := by
    intro t ht
    have h2t : 2 * (z + t) ∉ L.lattice := by
      intro h
      apply hz2
      have := sub_mem (hαc _ h) (two _ (hS.1 t ht).1)
      convert this using 1; ring
    have := GlobalTheory.T.product_derivWeierstrassP_half_periods_discriminant L a b (z + t) haL hbL habL ha2 hb2 h2t
    rw [← this, add_right_comm z a t, add_right_comm z b t, add_right_comm z (a + b) t]
  have hR := GlobalTheory.T.product_derivWeierstrassP_half_periods_discriminant L (α * a) (α * b) (α * z)
    (fun h => haL (GlobalTheory.T.not_mem_half_lattice_of_odd_multiplier L α a S hα hst hS hev h ha2))
    (fun h => hbL (GlobalTheory.T.not_mem_half_lattice_of_odd_multiplier L α b S hα hst hS hev h hb2))
    (fun h => habL (GlobalTheory.T.not_mem_half_lattice_of_odd_multiplier L α (a + b) S hα hst hS hev (by rwa [mul_add]) hab2))
    (hαc a ha2) (hαc b hb2) hz2
  rw [← mul_add α a b, ← mul_add, ← mul_add, ← mul_add] at hR
  have hP : (∏ t ∈ S, L.derivWeierstrassP (z + t)) * (∏ t ∈ S, L.derivWeierstrassP (z + a + t))
      * (∏ t ∈ S, L.derivWeierstrassP (z + b + t))
      * (∏ t ∈ S, L.derivWeierstrassP (z + (a + b) + t)) = (latticeCurve L).Δ ^ S.card := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      Finset.prod_congr rfl hLt, Finset.prod_const]
  apply mul_left_cancel₀ (latticeCurve_Δ_ne_zero L)
  have hall := congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) h0 h1) h2) h3
  rw [← hP]
  nth_rewrite 1 [← hR]
  rw [← hL0]
  linear_combination -hall

end GlobalTheory.CMModel
