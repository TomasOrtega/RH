import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Matrix

namespace GlobalTheory

/- English proof (translation)
Distinguish the cases in `hsq : ∃ s : K, d = s * s`. Use `right`. Take `⟨s, rfl⟩` from `hsq`. Establish `hs0 : s ≠ 0` using `fun h => hd (by simp [h])`. Use `set e : A := algebraMap K A (2⁻¹) + algebraMap K A (2⁻¹ * s⁻¹) * δ with he`.

Establish `h1 : algebraMap K A (2⁻¹) * 2 = 1`. Rewrite using `[show (2 : A) = algebraMap K A 2 from (map_ofNat _ 2).symm, ← map_mul, inv_mul_cancel₀ h2, map_one]`. Establish `h3 : algebraMap K A (s⁻¹) * algebraMap K A s = 1`. Rewrite using `[← map_mul, inv_mul_cancel₀ hs0, map_one]`. Rewrite `hδ`, `he` using `[map_mul]`.

Establish `hee : e * e = e`. Rewrite using `[he]`. Generalize the expression as in `algebraMap K A (2⁻¹) = p at *`. Generalize the expression as in `algebraMap K A (s⁻¹) = q at *`. Generalize the expression as in `algebraMap K A s = t at *`.

Take the linear combination `(p + p * q * δ) * h1 + p ^ 2 * q ^ 2 * hδ + p ^ 2 * (q * t + 1) * h3`. Establish `hτe : τ e = 1 - e`. Rewrite using `[he]`. Simplify using `only [map_add, map_mul, hτ, hs]`. Take the linear combination `h1`.

Establish `hτe' : τ (1 - e) = e`. Rewrite using `[map_sub, map_one, hτe]`. Expand and normalize the polynomial expressions, which then agree. Establish `hδe : δ = algebraMap K A s * e + algebraMap K A (-s) * (1 - e)`. Rewrite using `[he, map_neg]`.

Generalize the expression as in `algebraMap K A (2⁻¹) = p at *`. Generalize the expression as in `algebraMap K A (s⁻¹) = q at *`. Generalize the expression as in `algebraMap K A s = t at *`. Take the linear combination `(-t - t * q * δ) * h1 - δ * h3`. Establish `he0 : e ≠ 0`.

Introduce `h`. Rewrite `hτe` using `[h]`. Simplify using `at hτe`. Establish `he1 : 1 - e ≠ 0`. Introduce `h`.

Rewrite `hτe'` using `[h, map_zero]`. Conclude with `he0 hτe'.symm`. Set `ψ : K × K →+* A` to `{ toFun := fun x => algebraMap K A x.1 * e + algebraMap K A x.2 * (1 - e) map_one' := by simp map_zero' := by simp map_add' := by intro x y; simp only [Prod.fst_add, Prod.snd_add, map_add]; ring map_mul' := by`. Introduce `x y`. Simplify using `only [Prod.fst_mul, Prod.snd_mul, map_mul]`.

Generalize the expression as in `algebraMap K A x.1 = a`. Generalize the expression as in `algebraMap K A x.2 = b`. Generalize the expression as in `algebraMap K A y.1 = c`. Generalize the expression as in `algebraMap K A y.2 = f`. Take the linear combination `(-(a - b) * (c - f)) * hee }`.

Establish `hψ : ∀ x, ψ x = algebraMap K A x.1 * e + algebraMap K A x.2 * (1 - e)` using `fun _ => rfl`. Establish `hinj : Function.Injective ψ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Rewrite `hx` using `[hψ]`.

Establish `ha : algebraMap K A x.1 * e = 0`. Take the linear combination `e * hx - (algebraMap K A x.1 - algebraMap K A x.2) * hee`. Establish `hb : algebraMap K A x.2 * (1 - e) = 0`. Take the linear combination `hx - ha`. Rewrite `ha`, `hb` using `[← Algebra.smul_def, smul_eq_zero]`.

Conclude with `Prod.ext (ha.resolve_right he0) (hb.resolve_right he1)`. Establish `hsurj : Function.Surjective ψ`. Introduce `x`. Take `⟨a, b, rfl⟩` from `hsp x`. Use `⟨(a + b * s, a - b * s), ?_⟩` and prove the remaining obligations.

Rewrite using `[hψ]`. Simplify using `only [map_add, map_sub, map_mul]`. Rewrite `hδe` using `[map_neg]`. Take the linear combination `(-algebraMap K A b) * hδe`. Use `⟨(RingEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm, fun x => ?_⟩` and prove the remaining obligations.

Take `⟨y, rfl⟩` from `(RingEquiv.ofBijective ψ ⟨hinj, hsurj⟩).surjective x`. Rewrite using `[RingEquiv.symm_apply_apply, RingEquiv.symm_apply_eq]`. Express the relevant statement in the definitionally equal form `τ (ψ y) = ψ y.swap`. Simplify using `only [hψ, map_add, map_mul, hτ, hτe, hτe', Prod.fst_swap, Prod.snd_swap]`. Expand and normalize the polynomial expressions, which then agree.

Use `left`. Use `⟨exists_pair_ne A, mul_comm, fun {x} hx => ?_⟩` and prove the remaining obligations. Take `⟨a, b, rfl⟩` from `hsp x`. Establish `hn : a * a - d * (b * b) ≠ 0`. Introduce `h`.

Distinguish the cases in `hb : b = 0`. Substitute `hb` using the available equality. Establish `: a = 0` using `by simpa using h`. Substitute `this` using the available equality. Simplify using `at hx`.

Use `hsq ⟨a / b, ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Take the linear combination `-h`. Use `⟨(algebraMap K A a - algebraMap K A b * δ) * algebraMap K A (a * a - d * (b * b))⁻¹, ?_⟩` and prove the remaining obligations. Establish `h4 : algebraMap K A (a * a - d * (b * b)) * algebraMap K A (a * a - d * (b * b))⁻¹ = 1`.

Rewrite using `[← map_mul, mul_inv_cancel₀ hn, map_one]`. Generalize the expression as in `algebraMap K A (a * a - d * (b * b))⁻¹ = u at *`. Simplify using `only [map_sub, map_mul] at h4`. Take the linear combination `h4 - (algebraMap K A b) ^ 2 * u * hδ`.
-/
theorem quadAlg_isField_or_split {K A : Type} [Field K] [CommRing A] [Algebra K A] [Nontrivial A]
    (h2 : (2 : K) ≠ 0) (τ : A →+* A) (hτ : ∀ k, τ (algebraMap K A k) = algebraMap K A k)
    (δ : A) (d : K) (hd : d ≠ 0) (hδ : δ * δ = algebraMap K A d) (hs : τ δ = -δ)
    (hsp : ∀ x : A, ∃ a b : K, x = algebraMap K A a + algebraMap K A b * δ) :
    IsField A ∨ ∃ φ : A ≃+* K × K, ∀ x, φ (τ x) = (φ x).swap := by
  by_cases hsq : ∃ s : K, d = s * s
  · right
    obtain ⟨s, rfl⟩ := hsq
    have hs0 : s ≠ 0 := fun h => hd (by simp [h])
    set e : A := algebraMap K A (2⁻¹) + algebraMap K A (2⁻¹ * s⁻¹) * δ with he
    have h1 : algebraMap K A (2⁻¹) * 2 = 1 := by
      rw [show (2 : A) = algebraMap K A 2 from (map_ofNat _ 2).symm, ← map_mul,
        inv_mul_cancel₀ h2, map_one]
    have h3 : algebraMap K A (s⁻¹) * algebraMap K A s = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hs0, map_one]
    rw [map_mul] at hδ he
    have hee : e * e = e := by
      rw [he]
      generalize algebraMap K A (2⁻¹) = p at *
      generalize algebraMap K A (s⁻¹) = q at *
      generalize algebraMap K A s = t at *
      linear_combination (p + p * q * δ) * h1 + p ^ 2 * q ^ 2 * hδ + p ^ 2 * (q * t + 1) * h3
    have hτe : τ e = 1 - e := by
      rw [he]
      simp only [map_add, map_mul, hτ, hs]
      linear_combination h1
    have hτe' : τ (1 - e) = e := by
      rw [map_sub, map_one, hτe]; ring
    have hδe : δ = algebraMap K A s * e + algebraMap K A (-s) * (1 - e) := by
      rw [he, map_neg]
      generalize algebraMap K A (2⁻¹) = p at *
      generalize algebraMap K A (s⁻¹) = q at *
      generalize algebraMap K A s = t at *
      linear_combination (-t - t * q * δ) * h1 - δ * h3
    have he0 : e ≠ 0 := by
      intro h
      rw [h] at hτe
      simp at hτe
    have he1 : 1 - e ≠ 0 := by
      intro h
      rw [h, map_zero] at hτe'
      exact he0 hτe'.symm
    let ψ : K × K →+* A :=
      { toFun := fun x => algebraMap K A x.1 * e + algebraMap K A x.2 * (1 - e)
        map_one' := by simp
        map_zero' := by simp
        map_add' := by intro x y; simp only [Prod.fst_add, Prod.snd_add, map_add]; ring
        map_mul' := by
          intro x y
          simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
          generalize algebraMap K A x.1 = a
          generalize algebraMap K A x.2 = b
          generalize algebraMap K A y.1 = c
          generalize algebraMap K A y.2 = f
          linear_combination (-(a - b) * (c - f)) * hee }
    have hψ : ∀ x, ψ x = algebraMap K A x.1 * e + algebraMap K A x.2 * (1 - e) := fun _ => rfl
    have hinj : Function.Injective ψ := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      rw [hψ] at hx
      have ha : algebraMap K A x.1 * e = 0 := by
        linear_combination e * hx - (algebraMap K A x.1 - algebraMap K A x.2) * hee
      have hb : algebraMap K A x.2 * (1 - e) = 0 := by
        linear_combination hx - ha
      rw [← Algebra.smul_def, smul_eq_zero] at ha hb
      exact Prod.ext (ha.resolve_right he0) (hb.resolve_right he1)
    have hsurj : Function.Surjective ψ := by
      intro x
      obtain ⟨a, b, rfl⟩ := hsp x
      refine ⟨(a + b * s, a - b * s), ?_⟩
      rw [hψ]
      simp only [map_add, map_sub, map_mul]
      rw [map_neg] at hδe
      linear_combination (-algebraMap K A b) * hδe
    refine ⟨(RingEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm, fun x => ?_⟩
    obtain ⟨y, rfl⟩ := (RingEquiv.ofBijective ψ ⟨hinj, hsurj⟩).surjective x
    rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_eq]
    change τ (ψ y) = ψ y.swap
    simp only [hψ, map_add, map_mul, hτ, hτe, hτe', Prod.fst_swap,
      Prod.snd_swap]
    ring
  · left
    refine ⟨exists_pair_ne A, mul_comm, fun {x} hx => ?_⟩
    obtain ⟨a, b, rfl⟩ := hsp x
    have hn : a * a - d * (b * b) ≠ 0 := by
      intro h
      by_cases hb : b = 0
      · subst hb
        have : a = 0 := by simpa using h
        subst this
        simp at hx
      · refine hsq ⟨a / b, ?_⟩
        field_simp
        linear_combination -h
    refine ⟨(algebraMap K A a - algebraMap K A b * δ) * algebraMap K A (a * a - d * (b * b))⁻¹, ?_⟩
    have h4 : algebraMap K A (a * a - d * (b * b)) * algebraMap K A (a * a - d * (b * b))⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hn, map_one]
    generalize algebraMap K A (a * a - d * (b * b))⁻¹ = u at *
    simp only [map_sub, map_mul] at h4
    linear_combination h4 - (algebraMap K A b) ^ 2 * u * hδ

/- English proof (translation)
Take `⟨t, ht⟩` from `hne`. Establish `: CharZero E` using `charZero_of_injective_algebraMap (algebraMap F E).injective`. Use `set δ := t - σ t with hδ`. Establish `hδ0 : δ ≠ 0` using `fun h => ht (sub_eq_zero.mp h).symm`. Establish `hs : σ δ = -δ` using `by rw [hδ, map_sub, hσ]; ring`.

Establish `hli : LinearIndependent F ![(1 : E), δ]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `a b h`. Establish `h'` using `congrArg σ h`. Rewrite `h'` using `[map_add, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, σ.commutes, σ.commutes, hs, map_one, map_zero, ← Algebra.smul_def, ← Algebra.smul_def, smul_neg]`.

Establish `ha : (2 * a) • (1 : E) = 0`. Rewrite using `[two_mul, add_smul]`. Take the linear combination `h + h'`. Establish `hb : (2 * b) • δ = 0`. Rewrite using `[two_mul, add_smul]`.

Take the linear combination `h - h'`. Rewrite `ha`, `hb` using `[smul_eq_zero]`. Conclude with `⟨by simpa using ha, by simpa [hδ0] using hb⟩`. Establish `hsp : ∀ x : E, ∃ a b : F, x = algebraMap F E a + algebraMap F E b * δ`. Introduce `x`.

Set `B` to `basisOfLinearIndependentOfCardEqFinrank hli (by simp [hr])`. Use `⟨B.repr x 0, B.repr x 1, ?_⟩` and prove the remaining obligations. Establish `h` using `B.sum_repr x`. Rewrite `h` using `[Fin.sum_univ_two]`. Establish `h0 : B 0 = 1` using `by simp [B]`.

Establish `h1 : B 1 = δ` using `by simp [B]`. Rewrite `h` using `[h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one]`. Conclude with `h.symm`. Take `⟨a, b, hab⟩` from `hsp (δ * δ)`. Establish `h'` using `congrArg σ hab`.

Simplify using `only [map_add, map_mul, hs, AlgHom.commutes] at h'`. Establish `hd : δ * δ = algebraMap F E a`. Establish `h2 : (2 : E) ≠ 0` using `two_ne_zero`. Apply `mul_left_cancel₀ h2` to reduce the goal to its premises. Take the linear combination `hab + h'`.

Use `⟨δ, a, ?_, hd, hs, hsp⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Simplify using `[hδ0] at hd`.
-/
theorem quadExt_exists_skew {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) (hr : Module.finrank F E = 2) (hσ : ∀ a, σ (σ a) = a) (hne : ∃ a, σ a ≠ a) :
    ∃ (δ : E) (d : F), d ≠ 0 ∧ δ * δ = algebraMap F E d ∧ σ δ = -δ ∧
      ∀ x : E, ∃ a b : F, x = algebraMap F E a + algebraMap F E b * δ := by
  obtain ⟨t, ht⟩ := hne
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  set δ := t - σ t with hδ
  have hδ0 : δ ≠ 0 := fun h => ht (sub_eq_zero.mp h).symm
  have hs : σ δ = -δ := by rw [hδ, map_sub, hσ]; ring
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    have h' := congrArg σ h
    rw [map_add, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, σ.commutes, σ.commutes, hs,
      map_one, map_zero, ← Algebra.smul_def, ← Algebra.smul_def, smul_neg] at h'
    have ha : (2 * a) • (1 : E) = 0 := by
      rw [two_mul, add_smul]; linear_combination h + h'
    have hb : (2 * b) • δ = 0 := by
      rw [two_mul, add_smul]; linear_combination h - h'
    rw [smul_eq_zero] at ha hb
    exact ⟨by simpa using ha, by simpa [hδ0] using hb⟩
  have hsp : ∀ x : E, ∃ a b : F, x = algebraMap F E a + algebraMap F E b * δ := by
    intro x
    let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hr])
    refine ⟨B.repr x 0, B.repr x 1, ?_⟩
    have h := B.sum_repr x
    rw [Fin.sum_univ_two] at h
    have h0 : B 0 = 1 := by simp [B]
    have h1 : B 1 = δ := by simp [B]
    rw [h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one] at h
    exact h.symm
  obtain ⟨a, b, hab⟩ := hsp (δ * δ)
  have h' := congrArg σ hab
  simp only [map_add, map_mul, hs, AlgHom.commutes] at h'
  have hd : δ * δ = algebraMap F E a := by
    have h2 : (2 : E) ≠ 0 := two_ne_zero
    apply mul_left_cancel₀ h2
    linear_combination hab + h'
  refine ⟨δ, a, ?_, hd, hs, hsp⟩
  rintro rfl
  simp [hδ0] at hd

/- English proof (translation)
Introduce `F E K _ _ _ _ _ _ σ hr hσ hne`. Take `⟨δ, d, hd, hδ, hs, hsp⟩` from `quadExt_exists_skew σ hr hσ hne`. Establish `: CharZero K` using `charZero_of_injective_algebraMap (algebraMap F K).injective`. Establish `hd' : algebraMap F K d ≠ 0` using `by simpa using hd`. Establish `hδ' : ((1 : K) ⊗ₜ[F] δ) * ((1 : K) ⊗ₜ[F] δ) = algebraMap K (K ⊗[F] E) (algebraMap F K d)`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, hδ, one_mul, ← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']`. Establish `hsig : ∀ (k : K) (x : E), sigR K σ (k ⊗ₜ[F] x) = k ⊗ₜ[F] σ x` using `fun k x => by`. Simplify using `[sigR]`. Establish `hs' : sigR K σ ((1 : K) ⊗ₜ[F] δ) = -((1 : K) ⊗ₜ[F] δ)`. Rewrite using `[hsig, hs, TensorProduct.tmul_neg]`.

Establish `hsp' : ∀ x : K ⊗[F] E, ∃ a b : K, x = algebraMap K (K ⊗[F] E) a + algebraMap K (K ⊗[F] E) b * ((1 : K) ⊗ₜ[F] δ)`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `tmul k x`.

Take `⟨a, b, rfl⟩` from `hsp x`. Use `⟨a • k, b • k, ?_⟩` and prove the remaining obligations. Rewrite using `[← Algebra.smul_def, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul]`. Simplify using `[Algebra.TensorProduct.algebraMap_apply, TensorProduct.smul_tmul']`. Consider the case `add x y hx hy`.

Take `⟨a, b, rfl⟩` from `hx`. Take `⟨c, e, rfl⟩` from `hy`. Conclude with `⟨a + c, b + e, by simp only [map_add]; ring⟩`. Use `⟨quadAlg_isField_or_split two_ne_zero (sigR K σ) (fun k => ?_) _ _ hd' hδ' hs' hsp', _, _, hd', hδ', hs', hsp'⟩` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.algebraMap_apply, hsig, map_one]`.
-/
theorem quadBaseChange_isField_or_split :
    ∀ (F E K : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [Field K] [Algebra F K] (σ : E →ₐ[F] E), Module.finrank F E = 2 → (∀ a, σ (σ a) = a) → (∃ a, σ a ≠ a) → (IsField (K ⊗[F] E) ∨ ∃ φ : K ⊗[F] E ≃+* K × K, ∀ x, φ (sigR K σ x) = (φ x).swap) ∧ ∃ (δ : K ⊗[F] E) (d : K), d ≠ 0 ∧ δ * δ = algebraMap K (K ⊗[F] E) d ∧ sigR K σ δ = -δ ∧ ∀ x : K ⊗[F] E, ∃ a b : K, x = algebraMap K (K ⊗[F] E) a + algebraMap K (K ⊗[F] E) b * δ := by
  intro F E K _ _ _ _ _ _ σ hr hσ hne
  obtain ⟨δ, d, hd, hδ, hs, hsp⟩ := quadExt_exists_skew σ hr hσ hne
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have hd' : algebraMap F K d ≠ 0 := by simpa using hd
  have hδ' : ((1 : K) ⊗ₜ[F] δ) * ((1 : K) ⊗ₜ[F] δ) =
      algebraMap K (K ⊗[F] E) (algebraMap F K d) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, hδ, one_mul, ← IsScalarTower.algebraMap_apply,
      Algebra.TensorProduct.algebraMap_apply']
  have hsig : ∀ (k : K) (x : E), sigR K σ (k ⊗ₜ[F] x) = k ⊗ₜ[F] σ x := fun k x => by
    simp [sigR]
  have hs' : sigR K σ ((1 : K) ⊗ₜ[F] δ) = -((1 : K) ⊗ₜ[F] δ) := by
    rw [hsig, hs, TensorProduct.tmul_neg]
  have hsp' : ∀ x : K ⊗[F] E, ∃ a b : K, x = algebraMap K (K ⊗[F] E) a +
      algebraMap K (K ⊗[F] E) b * ((1 : K) ⊗ₜ[F] δ) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul k x =>
      obtain ⟨a, b, rfl⟩ := hsp x
      refine ⟨a • k, b • k, ?_⟩
      rw [← Algebra.smul_def, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_add,
        TensorProduct.tmul_smul, TensorProduct.tmul_smul]
      simp [Algebra.TensorProduct.algebraMap_apply, TensorProduct.smul_tmul']
    | add x y hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨c, e, rfl⟩ := hy
      exact ⟨a + c, b + e, by simp only [map_add]; ring⟩
  refine ⟨quadAlg_isField_or_split two_ne_zero (sigR K σ) (fun k => ?_) _ _ hd' hδ' hs' hsp',
    _, _, hd', hδ', hs', hsp'⟩
  rw [Algebra.TensorProduct.algebraMap_apply, hsig, map_one]

end GlobalTheory
