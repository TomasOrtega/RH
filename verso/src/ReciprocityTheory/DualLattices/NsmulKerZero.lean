import ReciprocityTheory.DualLattices.IsHeightUnique

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace ATower

variable {p : ℕ} (Tw : ATower R₀ p)

/- English proof (translation)
Introduce and unpack `⟨k, hk⟩`. Establish `hk' : k ∈ Ideal.span {Tw.ξ n}`. Rewrite using `[← Tw.ker_eq n]`. Simplify using `using hk`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.mp hk'`.

Use `⟨a, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show Tw.ξ n * a = k`. Rewrite using `[← ha, mul_comm]`.
-/
lemma ξmul_surj (n : ℕ) : Function.Surjective (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) := by
  rintro ⟨k, hk⟩
  have hk' : k ∈ Ideal.span {Tw.ξ n} := by
    rw [← Tw.ker_eq n]
    simpa using hk
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hk'
  refine ⟨a, Subtype.ext ?_⟩
  show Tw.ξ n * a = k
  rw [← ha, mul_comm]

/- English proof (translation)
Establish `hle : LinearMap.ker (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) ≤ LinearMap.ker (Tw.π n).1.toLinearMap`. Introduce `a ha`. Rewrite `ha`, the goal using `[LinearMap.mem_ker]`. Establish `h0 : Tw.ξ n * a = 0` using `congrArg Subtype.val ha`. Establish `hm : a ∈ Ideal.span {Tw.ξ n}` using `Tw.ann n a (by rw [mul_comm]; exact h0)`.

Rewrite `hm` using `[← Tw.ker_eq n, RingHom.mem_ker]`. Conclude with `hm`. Establish `hs` using `Tw.ξmul_surj n`. Use `⟨(LinearMap.ker _).liftQ _ hle ∘ₗ (LinearMap.quotKerEquivOfSurjective _ hs).symm.toLinearMap, ?_⟩` and prove the remaining obligations. Use `LinearMap.ext fun a => ?_` and prove the remaining obligations.

Establish `h1 : (LinearMap.quotKerEquivOfSurjective _ hs).symm (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n) a) = Submodule.Quotient.mk a`. Rewrite using `[LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, h1, Submodule.liftQ_apply]`.
-/
lemma exists_factor (n : ℕ) : ∃ g' : (Tw.π n).ker →ₗ[R₀] (Tw.R n : Type u),
    g' ∘ₗ ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n) = (Tw.π n).1.toLinearMap := by
  have hle : LinearMap.ker (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) ≤
      LinearMap.ker (Tw.π n).1.toLinearMap := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    have h0 : Tw.ξ n * a = 0 := congrArg Subtype.val ha
    have hm : a ∈ Ideal.span {Tw.ξ n} := Tw.ann n a (by rw [mul_comm]; exact h0)
    rw [← Tw.ker_eq n, RingHom.mem_ker] at hm
    exact hm
  have hs := Tw.ξmul_surj n
  refine ⟨(LinearMap.ker _).liftQ _ hle ∘ₗ
    (LinearMap.quotKerEquivOfSurjective _ hs).symm.toLinearMap, ?_⟩
  refine LinearMap.ext fun a => ?_
  have h1 : (LinearMap.quotKerEquivOfSurjective _ hs).symm (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n) a) =
      Submodule.Quotient.mk a := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h1, Submodule.liftQ_apply]

end ATower

namespace BX

variable (B : BX R₀) {p : ℕ}

/- English proof (translation)
Establish `hc : ((p : (Tw.R' n : Type u))) ^ (n + 1) = 0` using `by exact_mod_cast Tw.char n`. Proceed by induction on `V using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul g k`. Establish `hk : (p ^ (n + 1)) • k = 0`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[nsmul_eq_mul, hc]`. Rewrite using `[← TensorProduct.tmul_smul, hk, TensorProduct.tmul_zero]`. Consider the case `add x y hx hy => rw [smul_add, hx, hy, add_zero]`.
-/
lemma nsmul_ker_zero (Tw : ATower R₀ p) (n : ℕ) (V : B.gg ⊗[R₀] (Tw.π n).ker) :
    (p ^ (n + 1)) • V = 0 := by
  have hc : ((p : (Tw.R' n : Type u))) ^ (n + 1) = 0 := by exact_mod_cast Tw.char n
  induction V using TensorProduct.induction_on with
  | zero => simp
  | tmul g k =>
    have hk : (p ^ (n + 1)) • k = 0 := by
      apply Subtype.ext
      simp [nsmul_eq_mul, hc]
    rw [← TensorProduct.tmul_smul, hk, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

/- English proof (translation)
Take `⟨th, hth⟩` from `B.surj (Tw.π n) (Tw.sqZero n) y`. Establish `h0 : B.map (Tw.π n) ((p ^ (n + 1)) • th) = 0` using `by rw [map_nsmul, hth, hy]`. Take `⟨v, hv⟩` from `(B.tg_ker (Tw.π n) (Tw.sqZero n) _).1 h0`. Take `⟨w, hw⟩` from `LinearMap.lTensor_surjective B.gg (Tw.ξmul_surj n) v`. Conclude with `⟨th, w, hth, by rw [← hv, ← hw]; rfl⟩`.
-/
lemma exists_lift (Tw : ATower R₀ p) (n : ℕ) (y : B.G (Tw.R n)) (hy : (p ^ (n + 1)) • y = 0) :
    ∃ (th : B.G (Tw.R' n)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)), B.map (Tw.π n) th = y ∧
      (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
        (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) := by
  obtain ⟨th, hth⟩ := B.surj (Tw.π n) (Tw.sqZero n) y
  have h0 : B.map (Tw.π n) ((p ^ (n + 1)) • th) = 0 := by rw [map_nsmul, hth, hy]
  obtain ⟨v, hv⟩ := (B.tg_ker (Tw.π n) (Tw.sqZero n) _).1 h0
  obtain ⟨w, hw⟩ := LinearMap.lTensor_surjective B.gg (Tw.ξmul_surj n) v
  exact ⟨th, w, hth, by rw [← hv, ← hw]; rfl⟩

/- English proof (translation)
Establish `hd : B.map (Tw.π n) (th - th') = 0` using `by rw [map_sub, he, sub_self]`. Take `⟨v0, hv0⟩` from `(B.tg_ker (Tw.π n) (Tw.sqZero n) _).1 hd`. Establish `hp : (p ^ (n + 1)) • th = (p ^ (n + 1)) • th'`. Establish `h : (p ^ (n + 1)) • (th - th') = 0`. Rewrite using `[← hv0, ← map_nsmul, B.nsmul_ker_zero Tw n v0, map_zero]`.

Rewrite `h` using `[smul_sub, sub_eq_zero]`. Then use the resulting hypothesis. Rewrite `hp` using `[hw, hw']`. Establish `hx` using `B.tg_inj (Tw.π n) (Tw.sqZero n) hp`. Take `⟨g', hg'⟩` from `Tw.exists_factor n`. Rewrite using `[← hg', LinearMap.lTensor_comp, LinearMap.comp_apply, LinearMap.comp_apply]`.

Conclude with `congrArg (LinearMap.lTensor B.gg g') hx`.
-/
lemma lift_indep (Tw : ATower R₀ p) (n : ℕ) (th th' : B.G (Tw.R' n)) (w w' : B.gg ⊗[R₀] (Tw.R' n : Type u))
    (he : B.map (Tw.π n) th = B.map (Tw.π n) th')
    (hw : (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
      (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w))
    (hw' : (p ^ (n + 1)) • th' = B.tg (Tw.π n) (Tw.sqZero n)
      (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w')) :
    LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w = LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w' := by
  have hd : B.map (Tw.π n) (th - th') = 0 := by rw [map_sub, he, sub_self]
  obtain ⟨v0, hv0⟩ := (B.tg_ker (Tw.π n) (Tw.sqZero n) _).1 hd
  have hp : (p ^ (n + 1)) • th = (p ^ (n + 1)) • th' := by
    have h : (p ^ (n + 1)) • (th - th') = 0 := by
      rw [← hv0, ← map_nsmul, B.nsmul_ker_zero Tw n v0, map_zero]
    rwa [smul_sub, sub_eq_zero] at h
  rw [hw, hw'] at hp
  have hx := B.tg_inj (Tw.π n) (Tw.sqZero n) hp
  obtain ⟨g', hg'⟩ := Tw.exists_factor n
  rw [← hg', LinearMap.lTensor_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  exact congrArg (LinearMap.lTensor B.gg g') hx

end BX

end ReciprocityTheory.PGsh
