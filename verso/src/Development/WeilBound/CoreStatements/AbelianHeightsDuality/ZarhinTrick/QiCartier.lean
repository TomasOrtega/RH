import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiCoreDefs

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

variable {K H : Type} [Field K] [CommRing H] [Algebra K H]

/- English proof (translation)
Use `haveI : IsArtinianRing H := IsArtinianRing.of_finite K H`. Set `f : ℕ →o (Ideal H)ᵒᵈ` to `⟨fun n => OrderDual.toDual (I ^ n), fun _ _ hab => Ideal.pow_le_pow_right hab⟩`. Take `⟨n, hn⟩` from `IsArtinian.monotone_stabilizes f`. Conclude with `⟨n, fun j hj => congrArg OrderDual.ofDual (hn j hj).symm⟩`.
-/
theorem qc_stable [FiniteDimensional K H] (I : Ideal H) : ∃ k : ℕ, ∀ j, k ≤ j → I ^ j = I ^ k := by
  haveI : IsArtinianRing H := IsArtinianRing.of_finite K H
  let f : ℕ →o (Ideal H)ᵒᵈ := ⟨fun n => OrderDual.toDual (I ^ n), fun _ _ hab => Ideal.pow_le_pow_right hab⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes f
  exact ⟨n, fun j hj => congrArg OrderDual.ofDual (hn j hj).symm⟩

/- English proof (translation)
Set `W : Submodule K H` to `Submodule.span K {(1 : H)} ⊔ (RingHom.ker ε ^ 2).restrictScalars K`. Establish `hxW : x ∉ W`. Introduce `h`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.1 h`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hy`.

Establish `hz2 : z ∈ RingHom.ker ε ^ 2` using `hz`. Establish `hz' : z ∈ RingHom.ker ε` using `Ideal.pow_le_self two_ne_zero hz2`. Establish `hc : c = 0`. Establish `h1 : ε x = 0` using `hx`. Establish `h2 : ε z = 0` using `hz'`.

Rewrite `h1` using `[← hyz, map_add, map_smul, map_one, h2]`. Simplify using `using h1`. Substitute `hc` using the available equality. Apply `hx2` to reduce the goal to its premises. Rewrite using `[← hyz, zero_smul, zero_add]`.

Conclude with `hz2`. Take `⟨f, hf, hfW⟩` from `Submodule.exists_dual_map_eq_bot_of_notMem hxW inferInstance`. Establish `hW : ∀ w ∈ W, f w = 0` using `fun w hw => by`. Establish `: f w ∈ W.map f` using `Submodule.mem_map_of_mem hw`. Rewrite `this` using `[hfW]`.

Simplify using `using this`. Use `⟨(f x)⁻¹ • f, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[hW 1 (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))]`. Introduce `y hy`. Simplify using `[hW y (Submodule.mem_sup_right hy)]`.

Simplify using `[hf]`.
-/
theorem qc_functional (ε : H →ₐ[K] K) {x : H} (hx : x ∈ RingHom.ker ε) (hx2 : x ∉ RingHom.ker ε ^ 2) :
    ∃ l : H →ₗ[K] K, l 1 = 0 ∧ (∀ y ∈ RingHom.ker ε ^ 2, l y = 0) ∧ l x = 1 := by
  let W : Submodule K H := Submodule.span K {(1 : H)} ⊔ (RingHom.ker ε ^ 2).restrictScalars K
  have hxW : x ∉ W := by
    intro h
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hz2 : z ∈ RingHom.ker ε ^ 2 := hz
    have hz' : z ∈ RingHom.ker ε := Ideal.pow_le_self two_ne_zero hz2
    have hc : c = 0 := by
      have h1 : ε x = 0 := hx
      have h2 : ε z = 0 := hz'
      rw [← hyz, map_add, map_smul, map_one, h2] at h1
      simpa using h1
    subst hc
    apply hx2
    rw [← hyz, zero_smul, zero_add]
    exact hz2
  obtain ⟨f, hf, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxW inferInstance
  have hW : ∀ w ∈ W, f w = 0 := fun w hw => by
    have : f w ∈ W.map f := Submodule.mem_map_of_mem hw
    rw [hfW] at this
    simpa using this
  refine ⟨(f x)⁻¹ • f, ?_, ?_, ?_⟩
  · simp [hW 1 (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))]
  · intro y hy
    simp [hW y (Submodule.mem_sup_right hy)]
  · simp [hf]

/- English proof (translation)
Establish `ha : a - algebraMap K H (ε a) ∈ RingHom.ker ε` using `by simp [RingHom.mem_ker]`. Establish `hb : b - algebraMap K H (ε b) ∈ RingHom.ker ε` using `by simp [RingHom.mem_ker]`. Establish `hab : l ((a - algebraMap K H (ε a)) * (b - algebraMap K H (ε b))) = 0` using `h2 _ (by rw [pow_two]; exact Ideal.mul_mem_mul ha hb)`. Establish `e : a * b = (a - algebraMap K H (ε a)) * (b - algebraMap K H (ε b)) + ε a • b + ε b • a - (ε a * ε b) • (1 : H)`. Simplify using `only [Algebra.smul_def, map_mul, mul_one]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, map_sub, map_add, map_add, hab, map_smul, map_smul, map_smul, h1]`. Simplify using `only [smul_eq_mul, mul_zero, sub_zero, zero_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qc_leib (ε : H →ₐ[K] K) (l : H →ₗ[K] K) (h1 : l 1 = 0) (h2 : ∀ y ∈ RingHom.ker ε ^ 2, l y = 0)
    (a b : H) : l (a * b) = ε a * l b + l a * ε b := by
  have ha : a - algebraMap K H (ε a) ∈ RingHom.ker ε := by simp [RingHom.mem_ker]
  have hb : b - algebraMap K H (ε b) ∈ RingHom.ker ε := by simp [RingHom.mem_ker]
  have hab : l ((a - algebraMap K H (ε a)) * (b - algebraMap K H (ε b))) = 0 :=
    h2 _ (by rw [pow_two]; exact Ideal.mul_mem_mul ha hb)
  have e : a * b = (a - algebraMap K H (ε a)) * (b - algebraMap K H (ε b)) + ε a • b + ε b • a -
      (ε a * ε b) • (1 : H) := by
    simp only [Algebra.smul_def, map_mul, mul_one]
    ring
  rw [e, map_sub, map_add, map_add, hab, map_smul, map_smul, map_smul, h1]
  simp only [smul_eq_mul, mul_zero, sub_zero, zero_add]
  ring

/- English proof (translation)
Introduce `x hx`. Assume the negation of the conclusion as `hx2`. Take `⟨l, hl1, hl2, hlx⟩` from `qc_functional ε hx hx2`. Set `Φ : H ⊗[K] H →ₗ[K] H` to `(TensorProduct.rid K H).toLinearMap ∘ₗ LinearMap.lTensor H l`. Set `mR : H ⊗[K] H →ₐ[K] H` to `(Algebra.TensorProduct.lmul' K).comp (Algebra.TensorProduct.map (AlgHom.id K H) ((Algebra.ofId K H).comp ε))`.

Set `mL : H ⊗[K] H →ₐ[K] H` to `(Algebra.TensorProduct.lmul' K).comp (Algebra.TensorProduct.map ((Algebra.ofId K H).comp ε) (AlgHom.id K H))`. Establish `hΦ : ∀ s t : H ⊗[K] H, Φ (s * t) = mR s * Φ t + Φ s * mR t`. Introduce `s t`. Proceed by induction on `s using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a₁ a₂`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul b₁ b₂`. Simplify using `only [Φ, mR, Algebra.TensorProduct.tmul_mul_tmul, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Algebra.TensorProduct.lmul'_apply_tmul, Algebra.ofId_apply, qc_lei …`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `add t₁ t₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add s₁ s₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hεΦ : ∀ t : H ⊗[K] H, ε (Φ t) = l (mL t)`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b`.

Simplify using `only [Φ, mL, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Algebra.TensorProduct.lmul'_apply_tmul, Algebra.ofId_apply, map_smul, smul_eq_mul]`. Rewrite using `[← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]`. Consider the case `add s t h₁ h₂ => simp only [map_add, h₁, h₂]`. Establish `hRa : ∀ a, mR (Δ a) = a` using `fun a => DFunLike.congr_fun hR a`. Establish `hLa : ∀ a, mL (Δ a) = a` using `fun a => DFunLike.congr_fun hL a`.

Set `D : H →ₗ[K] H` to `Φ ∘ₗ Δ.toLinearMap`. Establish `hD : ∀ a b, D (a * b) = a * D b + D a * b`. Introduce `a b`. Simplify using `only [D, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, hΦ, hRa]`. Establish `hεD : ∀ a, ε (D a) = l a`.

Introduce `a`. Simplify using `only [D, LinearMap.comp_apply, AlgHom.toLinearMap_apply, hεΦ, hLa]`. Establish `hDpow : ∀ n : ℕ, D (x ^ (n + 1)) = ((n : H) + 1) * x ^ n * D x`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ, hD, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨k, hk⟩` from `qc_stable (K := K) (RingHom.ker ε)`. Establish `hJJ : RingHom.ker ε ^ (k + 2) * RingHom.ker ε ^ (k + 2) = RingHom.ker ε ^ (k + 2)`. Rewrite using `[← pow_add, hk (k + 2 + (k + 2)) (by omega), hk (k + 2) (by omega)]`. Establish `hDJ : ∀ y ∈ RingHom.ker ε ^ (k + 2), D y ∈ RingHom.ker ε ^ (k + 2)`. Introduce `y hy`.

Rewrite `hy` using `[← hJJ]`. Use `Submodule.mul_induction_on hy (fun a ha b hb => ?_) (fun a b ha hb => ?_)` and prove the remaining obligations. Rewrite using `[hD]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ hb)`. Rewrite using `[map_add]`.

Conclude with `Ideal.add_mem _ ha hb`. Establish `hJ2 : RingHom.ker ε ^ (k + 2) ≤ RingHom.ker ε ^ 2` using `Ideal.pow_le_pow_right (by omega)`. Establish `hJ1 : RingHom.ker ε ^ (k + 2) ≤ RingHom.ker ε` using `Ideal.pow_le_self (by omega)`. Establish `hex : ∃ n, x ^ n ∈ RingHom.ker ε ^ (k + 2)` using `⟨k + 2, Ideal.pow_mem_pow hx _⟩`. Establish `hN : x ^ Nat.find hex ∈ RingHom.ker ε ^ (k + 2)` using `Nat.find_spec hex`.

Establish `hmin : ∀ m < Nat.find hex, x ^ m ∉ RingHom.ker ε ^ (k + 2)` using `fun m hm => Nat.find_min hex hm`. Establish `hN0 : Nat.find hex ≠ 0`. Introduce `h0`. Rewrite `hN` using `[h0, pow_zero]`. Establish `: ε 1 = 0` using `hJ1 hN`.

Simplify using `at this`. Establish `hN1 : Nat.find hex ≠ 1`. Introduce `h1`. Rewrite `hN` using `[h1, pow_one]`. Conclude with `hx2 (hJ2 hN)`.

Take `⟨M, hM⟩ : ∃ M, Nat.find hex = M + 2` from `⟨Nat.find hex - 2, by omega⟩`. Establish `h1 : D (x ^ (M + 2)) ∈ RingHom.ker ε ^ (k + 2)` using `hDJ _ (hM ▸ hN)`. Rewrite `h1` using `[hDpow (M + 1)]`. Set `π` to `Ideal.Quotient.mk (RingHom.ker ε ^ (k + 2))`. Establish `hu1 : IsUnit (π ((((M + 1 : ℕ) : H)) + 1))`.

Establish `e : π ((((M + 1 : ℕ) : H)) + 1) = algebraMap K (H ⧸ RingHom.ker ε ^ (k + 2)) ((M + 2 : ℕ) : K)`. Simplify using `only [map_add, map_natCast, map_one]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `(IsUnit.mk0 _ (Nat.cast_ne_zero.2 (by omega))).map _`. Establish `hu2 : IsUnit (π (D x))`. Establish `hm : D x - 1 ∈ RingHom.ker ε`. Rewrite using `[RingHom.mem_ker, map_sub, hεD, hlx, map_one, sub_self]`. Establish `hnil : IsNilpotent (π (D x - 1))` using `⟨k + 2, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hm _⟩`.

Use `hnil.isUnit_one_add` as an intermediate fact. Rewrite `this` using `[map_sub, map_one, add_sub_cancel]`. Then use the resulting hypothesis. Establish `h0 : π ((((M + 1 : ℕ) : H) + 1) * x ^ (M + 1) * D x) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 h1`. Rewrite `h0` using `[map_mul, map_mul, hu2.mul_left_eq_zero, hu1.mul_right_eq_zero, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hmin (M + 1) (by omega) h0`.
-/
theorem aug_le_sq {K H : Type} [Field K] [CharZero K] [CommRing H] [Algebra K H] [FiniteDimensional K H]
    (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) (hL : CounitL Δ ε) (hR : CounitR Δ ε) :
    RingHom.ker ε ≤ RingHom.ker ε ^ 2 := by
  classical
  intro x hx
  by_contra hx2
  obtain ⟨l, hl1, hl2, hlx⟩ := qc_functional ε hx hx2
  let Φ : H ⊗[K] H →ₗ[K] H := (TensorProduct.rid K H).toLinearMap ∘ₗ LinearMap.lTensor H l
  let mR : H ⊗[K] H →ₐ[K] H :=
    (Algebra.TensorProduct.lmul' K).comp (Algebra.TensorProduct.map (AlgHom.id K H) ((Algebra.ofId K H).comp ε))
  let mL : H ⊗[K] H →ₐ[K] H :=
    (Algebra.TensorProduct.lmul' K).comp (Algebra.TensorProduct.map ((Algebra.ofId K H).comp ε) (AlgHom.id K H))
  have hΦ : ∀ s t : H ⊗[K] H, Φ (s * t) = mR s * Φ t + Φ s * mR t := by
    intro s t
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul a₁ a₂ =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul b₁ b₂ =>
        simp only [Φ, mR, Algebra.TensorProduct.tmul_mul_tmul, LinearMap.comp_apply, LinearMap.lTensor_tmul,
          LinearEquiv.coe_coe, TensorProduct.rid_tmul, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
          AlgHom.coe_id, id_eq, Algebra.TensorProduct.lmul'_apply_tmul, Algebra.ofId_apply,
          qc_leib ε l hl1 hl2, Algebra.smul_def, map_add, map_mul]
        ring
      | add t₁ t₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]; ring
    | add s₁ s₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂]; ring
  have hεΦ : ∀ t : H ⊗[K] H, ε (Φ t) = l (mL t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [Φ, mL, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul,
        AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
        Algebra.TensorProduct.lmul'_apply_tmul, Algebra.ofId_apply, map_smul, smul_eq_mul]
      rw [← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
    | add s t h₁ h₂ => simp only [map_add, h₁, h₂]
  have hRa : ∀ a, mR (Δ a) = a := fun a => DFunLike.congr_fun hR a
  have hLa : ∀ a, mL (Δ a) = a := fun a => DFunLike.congr_fun hL a
  let D : H →ₗ[K] H := Φ ∘ₗ Δ.toLinearMap
  have hD : ∀ a b, D (a * b) = a * D b + D a * b := by
    intro a b
    simp only [D, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, hΦ, hRa]
  have hεD : ∀ a, ε (D a) = l a := by
    intro a
    simp only [D, LinearMap.comp_apply, AlgHom.toLinearMap_apply, hεΦ, hLa]
  have hDpow : ∀ n : ℕ, D (x ^ (n + 1)) = ((n : H) + 1) * x ^ n * D x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, hD, ih]
      push_cast
      ring
  obtain ⟨k, hk⟩ := qc_stable (K := K) (RingHom.ker ε)
  have hJJ : RingHom.ker ε ^ (k + 2) * RingHom.ker ε ^ (k + 2) = RingHom.ker ε ^ (k + 2) := by
    rw [← pow_add, hk (k + 2 + (k + 2)) (by omega), hk (k + 2) (by omega)]
  have hDJ : ∀ y ∈ RingHom.ker ε ^ (k + 2), D y ∈ RingHom.ker ε ^ (k + 2) := by
    intro y hy
    rw [← hJJ] at hy
    refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [hD]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ hb)
    · rw [map_add]
      exact Ideal.add_mem _ ha hb
  have hJ2 : RingHom.ker ε ^ (k + 2) ≤ RingHom.ker ε ^ 2 := Ideal.pow_le_pow_right (by omega)
  have hJ1 : RingHom.ker ε ^ (k + 2) ≤ RingHom.ker ε := Ideal.pow_le_self (by omega)
  have hex : ∃ n, x ^ n ∈ RingHom.ker ε ^ (k + 2) := ⟨k + 2, Ideal.pow_mem_pow hx _⟩
  have hN : x ^ Nat.find hex ∈ RingHom.ker ε ^ (k + 2) := Nat.find_spec hex
  have hmin : ∀ m < Nat.find hex, x ^ m ∉ RingHom.ker ε ^ (k + 2) := fun m hm => Nat.find_min hex hm
  have hN0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hN
    have : ε 1 = 0 := hJ1 hN
    simp at this
  have hN1 : Nat.find hex ≠ 1 := by
    intro h1
    rw [h1, pow_one] at hN
    exact hx2 (hJ2 hN)
  obtain ⟨M, hM⟩ : ∃ M, Nat.find hex = M + 2 := ⟨Nat.find hex - 2, by omega⟩
  have h1 : D (x ^ (M + 2)) ∈ RingHom.ker ε ^ (k + 2) := hDJ _ (hM ▸ hN)
  rw [hDpow (M + 1)] at h1
  let π := Ideal.Quotient.mk (RingHom.ker ε ^ (k + 2))
  have hu1 : IsUnit (π ((((M + 1 : ℕ) : H)) + 1)) := by
    have e : π ((((M + 1 : ℕ) : H)) + 1) = algebraMap K (H ⧸ RingHom.ker ε ^ (k + 2)) ((M + 2 : ℕ) : K) := by
      simp only [map_add, map_natCast, map_one]
      push_cast
      ring
    rw [e]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (by omega))).map _
  have hu2 : IsUnit (π (D x)) := by
    have hm : D x - 1 ∈ RingHom.ker ε := by
      rw [RingHom.mem_ker, map_sub, hεD, hlx, map_one, sub_self]
    have hnil : IsNilpotent (π (D x - 1)) :=
      ⟨k + 2, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hm _⟩
    have := hnil.isUnit_one_add
    rwa [map_sub, map_one, add_sub_cancel] at this
  have h0 : π ((((M + 1 : ℕ) : H) + 1) * x ^ (M + 1) * D x) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h1
  rw [map_mul, map_mul, hu2.mul_left_eq_zero, hu1.mul_right_eq_zero, Ideal.Quotient.eq_zero_iff_mem] at h0
  exact hmin (M + 1) (by omega) h0

end PositivityTheory.PrwZar.Qi
