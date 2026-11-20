import Mathlib

open Module

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[← Nat.card_pi, ← Nat.card_congr (Equiv.subtypePiEquivPi (p := fun i (y : A) => a i • y = 0))]`. Use `symm`. Use `Nat.card_congr ((b.constr ℤ).toEquiv.subtypeEquiv fun y => ?_)` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `hy x hx`.

Establish `: (b.constr ℤ y) ∘ₗ N.subtype = 0` using `c.ext fun i => by`. Simplify using `[h, hy, -Basis.constr_apply_fintype]`. Conclude with `LinearMap.congr_fun this ⟨x, hx⟩`. Introduce `hy i`. Use `hy _ (c i).2` as an intermediate fact.

Simplify `this` using `[h, -Basis.constr_apply_fintype]`.
-/
theorem card_hom_vanishing_of_diag_basis {M A ι : Type} [AddCommGroup M] [AddCommGroup A]
    [Fintype ι] (N : Submodule ℤ M) (b : Basis ι ℤ M) (c : Basis ι ℤ N) (a : ι → ℤ)
    (h : ∀ i, (c i : M) = a i • b i) :
    Nat.card {f : M →ₗ[ℤ] A // ∀ x ∈ N, f x = 0} = ∏ i, Nat.card {y : A // a i • y = 0} := by
  rw [← Nat.card_pi, ← Nat.card_congr (Equiv.subtypePiEquivPi (p := fun i (y : A) => a i • y = 0))]
  symm
  refine Nat.card_congr ((b.constr ℤ).toEquiv.subtypeEquiv fun y => ?_)
  constructor
  · intro hy x hx
    have : (b.constr ℤ y) ∘ₗ N.subtype = 0 := c.ext fun i => by
      simp [h, hy, -Basis.constr_apply_fintype]
    exact LinearMap.congr_fun this ⟨x, hx⟩
  · intro hy i
    have := hy _ (c i).2
    simpa [h, -Basis.constr_apply_fintype] using this

/- English proof (translation)
Establish `hdet : al.det.natAbs = m ^ 2`. Establish `h1` using `congrArg Matrix.det hal`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]`. Establish `h2` using `congrArg Int.natAbs h1`. Rewrite `h2` using `[Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]`.

Conclude with `Nat.mul_self_inj.mp (by rw [h2]; ring)`. Establish `hdet0 : al.det ≠ 0`. Introduce `h0`. Rewrite `hdet` using `[h0]`. Establish `: 0 < m ^ 2` using `by positivity`.

Simplify using `at hdet`. Use linear arithmetic over natural numbers and integers. Establish `hal' : al * al.transpose = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)`. Establish `hreg` using `Matrix.isRegular_of_isLeftRegular_det (A := al) (IsRegular.of_ne_zero hdet0).left`. Apply `hreg.right` to reduce the goal to its premises.

Simplify using `only [Matrix.mul_assoc, hal]`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]`. Use `set f : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) := Matrix.toLin' al with hf`. Establish `hinj : Function.Injective f`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `v hv`. Conclude with `Matrix.eq_zero_of_mulVec_eq_zero hdet0 (by simpa [hf] using hv)`. Use `set N := LinearMap.range f with hN`. Establish `hrank : finrank ℤ N = finrank ℤ (Fin 4 → ℤ)` using `(LinearEquiv.ofInjective f hinj).finrank_eq.symm`. Set `b0` to `Pi.basisFun ℤ (Fin 4)`.

Set `a` to `Submodule.smithNormalFormCoeffs b0 hrank`. Set `b` to `Submodule.smithNormalFormTopBasis b0 hrank`. Set `c` to `Submodule.smithNormalFormBotBasis b0 hrank`. Establish `hc : ∀ i, (c i : Fin 4 → ℤ) = a i • b i` using `Submodule.smithNormalFormBotBasis_def b0 hrank`. Establish `hprod : ∏ i, (a i).natAbs = m ^ 2`.

Establish `h1` using `Submodule.natAbs_det_equiv N (LinearEquiv.ofInjective f hinj)`. Rewrite `h1` using `[Nat.card_congr (Submodule.quotientEquivPiZMod N b0 hrank).toEquiv, Nat.card_pi]`. Rewrite `h1` using `[Nat.card_zmod]`. Rewrite using `[← h1, ← hdet, ← LinearMap.det_toLin']`. Use `congr 2`.

Establish `hdvd : ∀ i, (a i).natAbs ∣ m`. Introduce `i`. Establish `hmem : (m : ℤ) • b i ∈ N` using `⟨al.transpose.mulVec (b i), by`. Simplify using `[hf, Matrix.mulVec_mulVec, hal', Matrix.smul_mulVec]⟩`. Establish `h1` using `congrArg (fun x : N => b.repr (x : Fin 4 → ℤ) i) (c.sum_repr ⟨_, hmem⟩)`.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, hc, map_sum, map_smul, Basis.repr_self, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1`. Conclude with `Int.natAbs_dvd_natAbs.mpr (Dvd.intro_left _ h1)`. Establish `key` using `card_hom_vanishing_of_diag_basis (A := Additive G) N b c a hc`. Establish `h3 : ∀ i, Nat.card {y : Additive G // a i • y = 0} = (a i).natAbs ^ r`. Introduce `i`.

Rewrite using `[← hG _ (hdvd i)]`. Use `Nat.card_congr (Additive.toMul.subtypeEquiv fun y => ?_)` and prove the remaining obligations. Rewrite using `[pow_natAbs_eq_one, ← toMul_zsmul, toMul_eq_one]`. Rewrite `key` using `[h3]`. Rewrite `key` using `[Finset.prod_pow, hprod, ← pow_mul]`.

Rewrite using `[← key]`. Use `Nat.card_congr (Equiv.subtypeEquiv ((Equiv.piCongrRight fun _ => Additive.ofMul).trans (b0.constr ℤ).toEquiv) fun ξ => ?_)` and prove the remaining obligations. Establish `h4 : ∀ j, (b0.constr ℤ (fun i => Additive.ofMul (ξ i))) (f (b0 j)) = Additive.ofMul (∏ r', ξ r' ^ al r' j)`. Introduce `j`. Rewrite using `[Basis.constr_apply_fintype, ofMul_prod]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[b0, hf, ofMul_zpow]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `hξ _ ⟨x, rfl⟩`. Establish `: (b0.constr ℤ (fun i => Additive.ofMul (ξ i))) ∘ₗ f = 0` using `b0.ext fun j => by`.

Rewrite using `[LinearMap.comp_apply, h4, hξ]`. Both sides reduce to the same expression. Conclude with `LinearMap.congr_fun this x`. Introduce `hξ j`. Use `hξ (f (b0 j)) ⟨_, rfl⟩` as an intermediate fact.

Conclude with `ofMul_eq_zero.mp ((h4 j).symm.trans this)`.
-/
theorem card_ker_int_matrix_four (G : Type) [CommGroup G] (m r : ℕ)
    (al : Matrix (Fin 4) (Fin 4) ℤ) (hm : 1 ≤ m)
    (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (hG : ∀ k : ℕ, k ∣ m → Nat.card {x : G // x ^ k = 1} = k ^ r) :
    Nat.card {ξ : Fin 4 → G // ∀ c, ∏ r', ξ r' ^ al r' c = 1} = m ^ (2 * r) := by
  classical
  have hdet : al.det.natAbs = m ^ 2 := by
    have h1 := congrArg Matrix.det hal
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin] at h1
    have h2 := congrArg Int.natAbs h1
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at h2
    exact Nat.mul_self_inj.mp (by rw [h2]; ring)
  have hdet0 : al.det ≠ 0 := by
    intro h0
    rw [h0] at hdet
    have : 0 < m ^ 2 := by positivity
    simp at hdet
    omega
  have hal' : al * al.transpose = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    have hreg := Matrix.isRegular_of_isLeftRegular_det (A := al)
      (IsRegular.of_ne_zero hdet0).left
    apply hreg.right
    simp only [Matrix.mul_assoc, hal]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  set f : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) := Matrix.toLin' al with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet0 (by simpa [hf] using hv)
  set N := LinearMap.range f with hN
  have hrank : finrank ℤ N = finrank ℤ (Fin 4 → ℤ) :=
    (LinearEquiv.ofInjective f hinj).finrank_eq.symm
  let b0 := Pi.basisFun ℤ (Fin 4)
  let a := Submodule.smithNormalFormCoeffs b0 hrank
  let b := Submodule.smithNormalFormTopBasis b0 hrank
  let c := Submodule.smithNormalFormBotBasis b0 hrank
  have hc : ∀ i, (c i : Fin 4 → ℤ) = a i • b i := Submodule.smithNormalFormBotBasis_def b0 hrank
  have hprod : ∏ i, (a i).natAbs = m ^ 2 := by
    have h1 := Submodule.natAbs_det_equiv N (LinearEquiv.ofInjective f hinj)
    rw [Nat.card_congr (Submodule.quotientEquivPiZMod N b0 hrank).toEquiv, Nat.card_pi] at h1
    simp_rw [Nat.card_zmod] at h1
    rw [← h1, ← hdet, ← LinearMap.det_toLin']
    congr 2
  have hdvd : ∀ i, (a i).natAbs ∣ m := by
    intro i
    have hmem : (m : ℤ) • b i ∈ N := ⟨al.transpose.mulVec (b i), by
      simp [hf, Matrix.mulVec_mulVec, hal', Matrix.smul_mulVec]⟩
    have h1 := congrArg (fun x : N => b.repr (x : Fin 4 → ℤ) i) (c.sum_repr ⟨_, hmem⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, hc, map_sum, map_smul, Basis.repr_self,
      Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    exact Int.natAbs_dvd_natAbs.mpr (Dvd.intro_left _ h1)
  have key := card_hom_vanishing_of_diag_basis (A := Additive G) N b c a hc
  have h3 : ∀ i, Nat.card {y : Additive G // a i • y = 0} = (a i).natAbs ^ r := by
    intro i
    rw [← hG _ (hdvd i)]
    refine Nat.card_congr (Additive.toMul.subtypeEquiv fun y => ?_)
    rw [pow_natAbs_eq_one, ← toMul_zsmul, toMul_eq_one]
  simp_rw [h3] at key
  rw [Finset.prod_pow, hprod, ← pow_mul] at key
  rw [← key]
  refine Nat.card_congr (Equiv.subtypeEquiv
    ((Equiv.piCongrRight fun _ => Additive.ofMul).trans (b0.constr ℤ).toEquiv) fun ξ => ?_)
  have h4 : ∀ j, (b0.constr ℤ (fun i => Additive.ofMul (ξ i))) (f (b0 j)) =
      Additive.ofMul (∏ r', ξ r' ^ al r' j) := by
    intro j
    rw [Basis.constr_apply_fintype, ofMul_prod]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [b0, hf, ofMul_zpow]
  constructor
  · rintro hξ _ ⟨x, rfl⟩
    have : (b0.constr ℤ (fun i => Additive.ofMul (ξ i))) ∘ₗ f = 0 :=
      b0.ext fun j => by
        rw [LinearMap.comp_apply, h4, hξ]; rfl
    exact LinearMap.congr_fun this x
  · intro hξ j
    have := hξ (f (b0 j)) ⟨_, rfl⟩
    exact ofMul_eq_zero.mp ((h4 j).symm.trans this)

end GlobalTheory
