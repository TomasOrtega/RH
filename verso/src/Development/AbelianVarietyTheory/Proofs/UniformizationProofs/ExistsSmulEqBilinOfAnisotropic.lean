import Mathlib

namespace GlobalTheory

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis ℤ X`. Take `⟨⟨d, hd⟩, hint⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) (S := ℚ) (fun i => l (b i))`. Establish `hd0 : d ≠ 0` using `nonZeroDivisors.ne_zero hd`. Use `choose c hc using hint`. Set `φ : Module.Dual ℤ X` to `b.constr ℤ c`.

Establish `hφ : ∀ m, (φ m : ℚ) = d * l m`. Establish `: (Algebra.linearMap ℤ ℚ).comp φ = d • l.toIntLinearMap`. Use `b.ext fun i => ?_` and prove the remaining obligations. Use `hc i` as an intermediate fact. Simplify `this` using `[φ]`.

Introduce `m`. Use `LinearMap.congr_fun this m` as an intermediate fact. Simplify using `using this`. Set `Bh : X →+ Module.Dual ℤ X` to `{ toFun := fun x => (B x).toIntLinearMap map_zero' := by ext; simp map_add' := by intro x y; ext; simp }`. Set `BL : X →ₗ[ℤ] Module.Dual ℤ X` to `Bh.toIntLinearMap`.

Establish `hBL : ∀ x m, BL x m = B x m` using `fun _ _ => rfl`. Establish `hinj : Function.Injective BL`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Apply `hB` to reduce the goal to its premises.

Rewrite using `[← hBL, ha]`. Both sides reduce to the same expression. Establish `hrk : Module.finrank ℤ (LinearMap.range BL) = Module.finrank ℤ (Module.Dual ℤ X)`. Rewrite using `[LinearMap.finrank_range_of_inj hinj]`. Conclude with `b.toDualEquiv.finrank_eq`.

Establish `hfin : Finite (Module.Dual ℤ X ⧸ LinearMap.range BL)` using `Submodule.finiteQuotientOfFreeOfRankEq _ hrk`. Take `⟨n, hn, hnφ⟩` from `(isOfFinAddOrder_of_finite (Submodule.Quotient.mk (p := LinearMap.range BL) φ)).exists_nsmul_eq_zero`. Rewrite `hnφ` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Take `⟨x, hx⟩` from `hnφ`. Use `⟨n * (d * d), d • x, mul_pos (by exact_mod_cast hn) (mul_self_pos.2 hd0), fun m => ?_⟩` and prove the remaining obligations.

Establish `h1 : B x m = n * φ m`. Rewrite using `[← hBL, hx]`. Simplify using the standard rewrite rules. Rewrite using `[map_zsmul, AddMonoidHom.zsmul_apply, h1]`. Simplify using `only [smul_eq_mul]`.

Use `push_cast`. Rewrite using `[hφ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_smul_eq_bilin_of_anisotropic {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (B : X →+ X →+ ℤ) (hB : ∀ a, B a a = 0 → a = 0) (l : X →+ ℚ) :
    ∃ (M : ℤ) (x : X), 0 < M ∧ ∀ m, (B x m : ℚ) = M * l m := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (S := ℚ) (fun i => l (b i))
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  choose c hc using hint
  let φ : Module.Dual ℤ X := b.constr ℤ c
  have hφ : ∀ m, (φ m : ℚ) = d * l m := by
    have : (Algebra.linearMap ℤ ℚ).comp φ = d • l.toIntLinearMap := by
      refine b.ext fun i => ?_
      have := hc i
      simpa [φ] using this
    intro m
    have := LinearMap.congr_fun this m
    simpa using this
  let Bh : X →+ Module.Dual ℤ X :=
    { toFun := fun x => (B x).toIntLinearMap
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  let BL : X →ₗ[ℤ] Module.Dual ℤ X := Bh.toIntLinearMap
  have hBL : ∀ x m, BL x m = B x m := fun _ _ => rfl
  have hinj : Function.Injective BL := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    apply hB
    rw [← hBL, ha]; rfl
  have hrk : Module.finrank ℤ (LinearMap.range BL) = Module.finrank ℤ (Module.Dual ℤ X) := by
    rw [LinearMap.finrank_range_of_inj hinj]
    exact b.toDualEquiv.finrank_eq
  have hfin : Finite (Module.Dual ℤ X ⧸ LinearMap.range BL) :=
    Submodule.finiteQuotientOfFreeOfRankEq _ hrk
  obtain ⟨n, hn, hnφ⟩ := (isOfFinAddOrder_of_finite
    (Submodule.Quotient.mk (p := LinearMap.range BL) φ)).exists_nsmul_eq_zero
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hnφ
  obtain ⟨x, hx⟩ := hnφ
  refine ⟨n * (d * d), d • x, mul_pos (by exact_mod_cast hn) (mul_self_pos.2 hd0), fun m => ?_⟩
  have h1 : B x m = n * φ m := by
    rw [← hBL, hx]; simp
  rw [map_zsmul, AddMonoidHom.zsmul_apply, h1]
  simp only [smul_eq_mul]
  push_cast
  rw [hφ]; ring

/- English proof (translation)
Introduce `X _ _ _ Q B hadd h2 hpos l k hk y`. Establish `hQ0 : ∀ a, 0 ≤ Q a`. Introduce `a`. Distinguish the cases in `ha : a = 0`. Use `h2 a` as an intermediate fact.

Rewrite `this`, the goal using `[ha]`. Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Use `hpos a ha` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hsm : ∀ (n : ℤ) a, Q (n • a) = n * n * Q a`. Introduce `n a`. Establish `e1` using `h2 (n • a)`. Establish `e2` using `h2 a`. Rewrite `e1` using `[map_zsmul, map_zsmul, AddMonoidHom.zsmul_apply, ← e2]`.

Simplify using `only [smul_eq_mul] at e1`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨M, x, hM, hx⟩` from `exists_smul_eq_bilin_of_anisotropic B (fun a ha => by`. Assume the negation of the conclusion as `h`. Use `hpos a h` as an intermediate fact.

Use `h2 a` as an intermediate fact. Use the proof step `omega) l`. Set `F : X → ℕ` to `fun z => (Q (M • (y + k • z) - x)).toNat`. Take `⟨z, hz⟩ : ∃ z, ∀ z', F z ≤ F z'` from `⟨Function.argmin F, fun z' => Function.argmin_le F z'⟩`. Use `⟨z, fun m => ?_⟩` and prove the remaining obligations.

Establish `hz' : ∀ z', Q (M • (y + k • z) - x) ≤ Q (M • (y + k • z') - x)`. Introduce `z'`. Use `hz z'` as an intermediate fact. Establish `a` using `hQ0 (M • (y + k • z) - x)`. Establish `b` using `hQ0 (M • (y + k • z') - x)`.

Simplify using `only [F] at this`. Use linear arithmetic over natural numbers and integers. Establish `key : ∀ s : ℤ, 0 ≤ (M * k * s) * (M * k * s) * Q m + (M * k * s) * (M * B (y + k • z) m - B x m)`. Introduce `s`. Establish `h` using `hz' (z + s • m)`.

Establish `e : M • (y + k • (z + s • m)) - x = (M • (y + k • z) - x) + (M * k * s) • m` using `by module`. Rewrite `h` using `[e, hadd, hsm, map_zsmul, map_sub, map_zsmul, AddMonoidHom.sub_apply, AddMonoidHom.zsmul_apply]`. Simplify using `only [smul_eq_mul] at h`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `k1 : (0 : ℚ) ≤ ((M * k * 1) * (M * k * 1) * Q m + (M * k * 1) * (M * B (y + k • z) m - B x m) : ℤ)` using `by exact_mod_cast key 1`.

Establish `k2 : (0 : ℚ) ≤ ((M * k * (-1)) * (M * k * (-1)) * Q m + (M * k * (-1)) * (M * B (y + k • z) m - B x m) : ℤ)` using `by exact_mod_cast key (-1)`. Move the coercions through the operations in `at k1 k2`. Rewrite `k1`, `k2` using `[hx]`. Establish `hMq : (0 : ℚ) < M` using `by exact_mod_cast hM`. Establish `hkq : (0 : ℚ) < k` using `by exact_mod_cast hk`.

Establish `hp : (0 : ℚ) < M * M * k` using `by positivity`. Use `set β : ℚ := ((B (y + k • z) m : ℤ) : ℚ)`. Rewrite using `[abs_le]`. Prove the components needed by the constructor for the conclusion. Establish `: (0 : ℚ) ≤ M * M * k * (k * Q m + (β - l m))` using `by linarith`.

Use `(mul_nonneg_iff_of_pos_left hp).1 this` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: (0 : ℚ) ≤ M * M * k * (k * Q m - (β - l m))` using `by linarith`. Use `(mul_nonneg_iff_of_pos_left hp).1 this` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_rep_mod_shifted_form_small :
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (Q : X → ℤ) (B : X →+ X →+ ℤ), (∀ a b, Q (a + b) = Q a + Q b + B a b) → (∀ a, 2 * Q a = B a a) → (∀ a, a ≠ 0 → 1 ≤ Q a) → ∀ (l : X →+ ℚ) (k : ℕ), 1 ≤ k → ∀ y : X, ∃ z : X, ∀ m : X, |(B (y + k • z) m : ℚ) - l m| ≤ k * Q m := by
  intro X _ _ _ Q B hadd h2 hpos l k hk y
  have hQ0 : ∀ a, 0 ≤ Q a := by
    intro a
    by_cases ha : a = 0
    · have := h2 a
      rw [ha] at this ⊢
      simp at this
      omega
    · have := hpos a ha
      omega
  have hsm : ∀ (n : ℤ) a, Q (n • a) = n * n * Q a := by
    intro n a
    have e1 := h2 (n • a)
    have e2 := h2 a
    rw [map_zsmul, map_zsmul, AddMonoidHom.zsmul_apply, ← e2] at e1
    simp only [smul_eq_mul] at e1
    linarith
  obtain ⟨M, x, hM, hx⟩ := exists_smul_eq_bilin_of_anisotropic B (fun a ha => by
    by_contra h
    have := hpos a h
    have := h2 a
    omega) l
  let F : X → ℕ := fun z => (Q (M • (y + k • z) - x)).toNat
  obtain ⟨z, hz⟩ : ∃ z, ∀ z', F z ≤ F z' :=
    ⟨Function.argmin F, fun z' => Function.argmin_le F z'⟩
  refine ⟨z, fun m => ?_⟩
  have hz' : ∀ z', Q (M • (y + k • z) - x) ≤ Q (M • (y + k • z') - x) := by
    intro z'
    have := hz z'
    have a := hQ0 (M • (y + k • z) - x)
    have b := hQ0 (M • (y + k • z') - x)
    simp only [F] at this
    omega
  have key : ∀ s : ℤ, 0 ≤ (M * k * s) * (M * k * s) * Q m
      + (M * k * s) * (M * B (y + k • z) m - B x m) := by
    intro s
    have h := hz' (z + s • m)
    have e : M • (y + k • (z + s • m)) - x = (M • (y + k • z) - x) + (M * k * s) • m := by
      module
    rw [e, hadd, hsm, map_zsmul, map_sub, map_zsmul, AddMonoidHom.sub_apply,
      AddMonoidHom.zsmul_apply] at h
    simp only [smul_eq_mul] at h
    linarith
  have k1 : (0 : ℚ) ≤ ((M * k * 1) * (M * k * 1) * Q m
      + (M * k * 1) * (M * B (y + k • z) m - B x m) : ℤ) := by exact_mod_cast key 1
  have k2 : (0 : ℚ) ≤ ((M * k * (-1)) * (M * k * (-1)) * Q m
      + (M * k * (-1)) * (M * B (y + k • z) m - B x m) : ℤ) := by exact_mod_cast key (-1)
  push_cast at k1 k2
  rw [hx] at k1 k2
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  have hp : (0 : ℚ) < M * M * k := by positivity
  set β : ℚ := ((B (y + k • z) m : ℤ) : ℚ)
  rw [abs_le]
  constructor
  · have : (0 : ℚ) ≤ M * M * k * (k * Q m + (β - l m)) := by linarith
    have := (mul_nonneg_iff_of_pos_left hp).1 this
    linarith
  · have : (0 : ℚ) ≤ M * M * k * (k * Q m - (β - l m)) := by linarith
    have := (mul_nonneg_iff_of_pos_left hp).1 this
    linarith

end GlobalTheory
