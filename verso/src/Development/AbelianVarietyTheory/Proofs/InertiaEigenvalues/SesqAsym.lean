import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAevalEqOfCharpolySeparableInvolutionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTraceMulOfSeparableGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitSigmaEqMulHilbert90InvAlgStatement
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.SesqAsym

/- English proof (translation)
Establish `h` using `Algebra.trace_eq_of_equiv_equiv K.c B.σ (by ext e; simp [B.σ_alg]) a`. Rewrite using `[h, RingEquiv.apply_symm_apply]`.
-/
theorem trace_σ {K : UQ} (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) = K.c (Algebra.trace K.E B.A a) := by
  have h := Algebra.trace_eq_of_equiv_equiv K.c B.σ (by ext e; simp [B.σ_alg]) a
  rw [h, RingEquiv.apply_symm_apply]

/- English proof (translation)
Introduce `K B hg hP ε hε`. Apply the tactic sequence `have hσε : B.σ ε = ε := by rcases hε with rfl | rfl <;> simp`. Apply the tactic sequence `have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp`. Use `set u := ε * B.g with hu_def`. Establish `hu : u * B.σ u = 1`.

Rewrite using `[hu_def, map_mul, hσε]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨GlobalTheory.T.exists_unit_sigma_eq_mul_invAlg K B u hu, ?_⟩` and prove the remaining obligations. Introduce `s hadd hlin hnd hsym`. Establish `hvu : B.σ u * u = 1` using `by rw [mul_comm]; exact hu`.

Establish `hsym' : ∀ y z, s y z = K.c (s z (B.σ u * y))`. Introduce `y z`. Rewrite using `[hsym, ← mul_assoc, hu, one_mul]`. Establish `hadd2 : ∀ y z z', s y (z + z') = s y z + s y z'`. Introduce `y z z'`.

Rewrite using `[hsym', hadd, map_add, ← hsym', ← hsym']`. Establish `hlin2 : ∀ (e : K.E) y z, s y (e • z) = K.c e * s y z`. Introduce `e y z`. Rewrite using `[hsym', hlin, map_mul, ← hsym']`. Establish `hsu : ∀ y z, s (u * y) (u * z) = s y z`.

Introduce `y z`. Rewrite using `[← hsym, ← hsym, K.c_c]`. Establish `hneg1 : ∀ y z, s (-y) z = - s y z`. Introduce `y z`. Use `hlin (-1) y z` as an intermediate fact.

Simplify using `using this`. Establish `hneg2 : ∀ y z, s y (-z) = - s y z`. Introduce `y z`. Use `hlin2 (-1) y z` as an intermediate fact. Simplify using `using this`.

Establish `hsg : ∀ y z, s (B.g * y) (B.g * z) = s y z`. Introduce `y z`. Break down `hε with rfl | rfl` into its components or cases. Simplify `hsu y z` using `[hu_def]`. Use `hsu y z` as an intermediate fact.

Simplify using `only [hu_def, neg_mul, one_mul] at this`. Rewrite `this` using `[hneg1, hneg2, neg_neg]`. Conclude with `this`. Establish `hadj_g : ∀ y z, s (B.g * y) z = s y (B.σ B.g * z)`. Introduce `y z`.

Use `conv_lhs => rw [show z = B.g * (B.σ B.g * z) by rw [← mul_assoc, hg, one_mul]]`. Conclude with `hsg _ _`. Establish `hadj : ∀ a y z, s (a * y) z = s y (B.σ a * z)`. Introduce `a`. Take `⟨f, rfl⟩` from `GlobalTheory.T.exists_aeval_eq_of_charpoly_separable_involution K B hP a`.

Proceed by induction on `f using Polynomial.induction_on with`. Consider the case `C e`. Introduce `y z`. Rewrite using `[aeval_C, ← Algebra.smul_def, B.σ_alg, ← Algebra.smul_def, hlin, hlin2, K.c_c]`. Consider the case `add p q hp hq`.

Introduce `y z`. Rewrite using `[map_add, add_mul, hadd, hp, hq, map_add, add_mul, hadd2]`. Consider the case `monomial n e ih`. Introduce `y z`. Rewrite using `[pow_succ, ← mul_assoc, map_mul, aeval_X, mul_assoc, ih, hadj_g]`.

Use `congr 1`. Rewrite using `[map_mul B.σ _ B.g]`. Expand and normalize the polynomial expressions, which then agree. Set `ℓ : Module.Dual K.E B.A` to `{ toFun := fun y => s y 1 map_add' := fun x y => hadd x y 1 map_smul' := fun c x => hlin c x 1 }`. Set `φ : B.A →ₗ[K.E] Module.Dual K.E B.A` to `Algebra.traceForm K.E B.A`.

Establish `hφi : Function.Injective φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `w hw`. Use `GlobalTheory.T.eq_zero_of_trace_mul_of_separable_generated K B hP (GlobalTheory.T.exists_aeval_eq_of_charpoly_separable_involution K B hP) w fun y => ?_` and prove the remaining obligations. Use `LinearMap.congr_fun hw y` as an intermediate fact.

Simplify `this` using `[φ, Algebra.traceForm_apply]`. Establish `hφs : Function.Surjective φ` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).mp hφi`. Take `⟨β, hβ⟩` from `hφs ℓ`. Establish `hβs : ∀ y, s y 1 = Algebra.trace K.E B.A (β * y)`. Introduce `y`.

Use `LinearMap.congr_fun hβ y` as an intermediate fact. Simplify `this.symm` using `[φ, ℓ, Algebra.traceForm_apply]`. Establish `hform : ∀ y z, s y z = B.herm β y z`. Introduce `y z`. Establish `h1` using `hadj (B.σ z) y 1`.

Rewrite `h1` using `[B.σ_σ, mul_one]`. Rewrite using `[← h1, hβs]`. Unfold `InvAlg.herm`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hβinj : Function.Injective (LinearMap.mulLeft K.E β)`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `y hy`. Establish `hy' : β * y = 0` using `hy`. Use `hnd y fun z => ?_` and prove the remaining obligations.

Rewrite using `[hform]`. Unfold `InvAlg.herm`. Rewrite using `[hy', zero_mul, map_zero]`. Take `⟨x, hx⟩` from `(LinearMap.injective_iff_surjective.mp hβinj) 1`. Establish `hxβ : β * x = 1` using `hx`.

Use `⟨⟨β, x, hxβ, by rw [mul_comm]; exact hxβ⟩, ?_, hform⟩` and prove the remaining obligations. Use `show B.σ β = β * u`. Rewrite using `[← sub_eq_zero]`. Use `GlobalTheory.T.eq_zero_of_trace_mul_of_separable_generated K B hP (GlobalTheory.T.exists_aeval_eq_of_charpoly_separable_involution K B hP) _ fun y => ?_` and prove the remaining obligations. Establish `h3 : Algebra.trace K.E B.A (B.σ β * y) = Algebra.trace K.E B.A (β * u * y)`.

Establish `h2` using `hsym y 1`. Rewrite `h2` using `[hform, hform]`. Unfold `InvAlg.herm at h2`. Rewrite `h2` using `[← trace_σ]`. Simplify using `only [map_mul B.σ, map_one, B.σ_σ, mul_one] at h2`.

Rewrite using `[h2]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[sub_mul, map_sub, h3, sub_self]`.
-/
theorem sesq_asym : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → (∃ β : B.Aˣ, B.σ (β : B.A) = β * (ε * B.g)) ∧ ∀ (s : B.A → B.A → K.E), (∀ x y z, s (x + y) z = s x z + s y z) → (∀ (c : K.E) x z, s (c • x) z = c * s x z) → (∀ y, (∀ z, s y z = 0) → y = 0) → (∀ y z, K.c (s z y) = s (ε * B.g * y) z) → ∃ β : B.Aˣ, B.σ (β : B.A) = β * (ε * B.g) ∧ ∀ y z, s y z = B.herm β y z := by
  intro K B hg hP ε hε
  have hσε : B.σ ε = ε := by rcases hε with rfl | rfl <;> simp
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  set u := ε * B.g with hu_def
  have hu : u * B.σ u = 1 := by
    rw [hu_def, map_mul, hσε]
    calc ε * B.g * (ε * B.σ B.g) = (ε * ε) * (B.g * B.σ B.g) := by ring
      _ = 1 := by rw [hεε, hg, one_mul]
  refine ⟨GlobalTheory.T.exists_unit_sigma_eq_mul_invAlg K B u hu, ?_⟩
  intro s hadd hlin hnd hsym
  have hvu : B.σ u * u = 1 := by rw [mul_comm]; exact hu

  have hsym' : ∀ y z, s y z = K.c (s z (B.σ u * y)) := by
    intro y z
    rw [hsym, ← mul_assoc, hu, one_mul]
  have hadd2 : ∀ y z z', s y (z + z') = s y z + s y z' := by
    intro y z z'
    rw [hsym', hadd, map_add, ← hsym', ← hsym']
  have hlin2 : ∀ (e : K.E) y z, s y (e • z) = K.c e * s y z := by
    intro e y z
    rw [hsym', hlin, map_mul, ← hsym']
  have hsu : ∀ y z, s (u * y) (u * z) = s y z := by
    intro y z
    rw [← hsym, ← hsym, K.c_c]
  have hneg1 : ∀ y z, s (-y) z = - s y z := by
    intro y z
    have := hlin (-1) y z
    simpa using this
  have hneg2 : ∀ y z, s y (-z) = - s y z := by
    intro y z
    have := hlin2 (-1) y z
    simpa using this
  have hsg : ∀ y z, s (B.g * y) (B.g * z) = s y z := by
    intro y z
    rcases hε with rfl | rfl
    · simpa [hu_def] using hsu y z
    · have := hsu y z
      simp only [hu_def, neg_mul, one_mul] at this
      rw [hneg1, hneg2, neg_neg] at this
      exact this
  have hadj_g : ∀ y z, s (B.g * y) z = s y (B.σ B.g * z) := by
    intro y z
    conv_lhs => rw [show z = B.g * (B.σ B.g * z) by rw [← mul_assoc, hg, one_mul]]
    exact hsg _ _
  have hadj : ∀ a y z, s (a * y) z = s y (B.σ a * z) := by
    intro a
    obtain ⟨f, rfl⟩ := GlobalTheory.T.exists_aeval_eq_of_charpoly_separable_involution K B hP a
    induction f using Polynomial.induction_on with
    | C e =>
      intro y z
      rw [aeval_C, ← Algebra.smul_def, B.σ_alg, ← Algebra.smul_def, hlin, hlin2, K.c_c]
    | add p q hp hq =>
      intro y z
      rw [map_add, add_mul, hadd, hp, hq, map_add, add_mul, hadd2]
    | monomial n e ih =>
      intro y z
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X, mul_assoc, ih, hadj_g]
      congr 1
      rw [map_mul B.σ _ B.g]
      ring

  let ℓ : Module.Dual K.E B.A :=
    { toFun := fun y => s y 1
      map_add' := fun x y => hadd x y 1
      map_smul' := fun c x => hlin c x 1 }
  let φ : B.A →ₗ[K.E] Module.Dual K.E B.A := Algebra.traceForm K.E B.A
  have hφi : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    refine GlobalTheory.T.eq_zero_of_trace_mul_of_separable_generated K B hP (GlobalTheory.T.exists_aeval_eq_of_charpoly_separable_involution K B hP) w fun y => ?_
    have := LinearMap.congr_fun hw y
    simpa [φ, Algebra.traceForm_apply] using this
  have hφs : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).mp hφi
  obtain ⟨β, hβ⟩ := hφs ℓ
  have hβs : ∀ y, s y 1 = Algebra.trace K.E B.A (β * y) := by
    intro y
    have := LinearMap.congr_fun hβ y
    simpa [φ, ℓ, Algebra.traceForm_apply] using this.symm
  have hform : ∀ y z, s y z = B.herm β y z := by
    intro y z
    have h1 := hadj (B.σ z) y 1
    rw [B.σ_σ, mul_one] at h1
    rw [← h1, hβs]
    unfold InvAlg.herm
    congr 1; ring

  have hβinj : Function.Injective (LinearMap.mulLeft K.E β) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hy' : β * y = 0 := hy
    refine hnd y fun z => ?_
    rw [hform]
    unfold InvAlg.herm
    rw [hy', zero_mul, map_zero]
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective.mp hβinj) 1
  have hxβ : β * x = 1 := hx
  refine ⟨⟨β, x, hxβ, by rw [mul_comm]; exact hxβ⟩, ?_, hform⟩
  show B.σ β = β * u
  rw [← sub_eq_zero]
  refine GlobalTheory.T.eq_zero_of_trace_mul_of_separable_generated K B hP (GlobalTheory.T.exists_aeval_eq_of_charpoly_separable_involution K B hP) _ fun y => ?_
  have h3 : Algebra.trace K.E B.A (B.σ β * y) = Algebra.trace K.E B.A (β * u * y) := by
    have h2 := hsym y 1
    rw [hform, hform] at h2
    unfold InvAlg.herm at h2
    rw [← trace_σ] at h2
    simp only [map_mul B.σ, map_one, B.σ_σ, mul_one] at h2
    rw [h2]; congr 1; ring
  rw [sub_mul, map_sub, h3, sub_self]

end GlobalTheory.SesqAsym
