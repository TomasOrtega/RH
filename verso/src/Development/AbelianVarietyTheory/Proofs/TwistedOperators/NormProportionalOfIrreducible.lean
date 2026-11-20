import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC

noncomputable section
namespace GlobalTheory.FockTensor
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

/- English proof (translation)
Set `e : W ≃ₗ[ℂ] W.map E` to `Submodule.equivMapOfInjective E hE W`. Use `haveI : FiniteDimensional ℂ (W.map E) := LinearEquiv.finiteDimensional e`. Use `haveI : CompleteSpace (W.map E) := FiniteDimensional.complete ℂ (W.map E)`. Set `g : W.map E →ₗ[ℂ] ℂ` to `(f.comp W.subtype).comp e.symm.toLinearMap`. Set `v : W.map E` to `(InnerProductSpace.toDual ℂ (W.map E)).symm (LinearMap.toContinuousLinearMap g)`.

Use `⟨(e.symm v : V), (e.symm v).2, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1 : E (e.symm v : V) = (v : H)` using `congrArg Subtype.val (e.apply_symm_apply v)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, Submodule.coe_inner]`. Both sides reduce to the same expression.

Use `_ = g (e ⟨x, hx⟩) := InnerProductSpace.toDual_symm_apply`. Use `_ = f x := by simp [g]`.
-/
theorem exists_repr_on_finiteDimensional {V H : Type} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : V →ₗ[ℂ] H) (hE : Function.Injective E)
    (W : Submodule ℂ V) [FiniteDimensional ℂ W] (f : V →ₗ[ℂ] ℂ) :
    ∃ a ∈ W, ∀ x ∈ W, inner ℂ (E a) (E x) = f x := by
  classical
  let e : W ≃ₗ[ℂ] W.map E := Submodule.equivMapOfInjective E hE W
  haveI : FiniteDimensional ℂ (W.map E) := LinearEquiv.finiteDimensional e
  haveI : CompleteSpace (W.map E) := FiniteDimensional.complete ℂ (W.map E)
  let g : W.map E →ₗ[ℂ] ℂ := (f.comp W.subtype).comp e.symm.toLinearMap
  let v : W.map E := (InnerProductSpace.toDual ℂ (W.map E)).symm (LinearMap.toContinuousLinearMap g)
  refine ⟨(e.symm v : V), (e.symm v).2, fun x hx => ?_⟩
  have h1 : E (e.symm v : V) = (v : H) := congrArg Subtype.val (e.apply_symm_apply v)
  calc inner ℂ (E (e.symm v : V)) (E x) = inner ℂ v (e ⟨x, hx⟩) := by
          rw [h1, Submodule.coe_inner]; rfl
    _ = g (e ⟨x, hx⟩) := InnerProductSpace.toDual_symm_apply
    _ = f x := by simp [g]

/- English proof (translation)
Simplify using `only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, zero_smul]`.
-/
theorem mem_hwSub_iff_eigen {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) :
    v ∈ hwSub act μ ↔ (∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v) ∧
      ∀ a b, posC a b → act (Eab a b) v = (0 : ℂ) • v := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, zero_smul]

/- English proof (translation)
Take `⟨v₀s, hv₀s, hspan⟩` from `finrank_eq_one_iff'.mp hΛ`. Use `set v₀ : M.V := (v₀s : M.V) with hv₀def`. Establish `hv₀ : v₀ ≠ 0` using `fun h => hv₀s (Subtype.ext h)`. Establish `hE₁v₀ : E₁ v₀ ≠ 0` using `fun h => hv₀ (hE (by rw [h, map_zero]))`. Use `set r : ℝ := ‖E₂ v₀‖ ^ 2 / ‖E₁ v₀‖ ^ 2 with hr`.

Establish `hr0 : 0 ≤ r` using `by positivity`. Establish `hn1 : ‖E₁ v₀‖ ^ 2 ≠ 0` using `pow_ne_zero _ (norm_ne_zero_iff.mpr hE₁v₀)`. Establish `hrr : r * ‖E₁ v₀‖ ^ 2 = ‖E₂ v₀‖ ^ 2` using `div_mul_cancel₀ _ hn1`. Set `ψ : M.V → M.V →ₗ[ℂ] ℂ` to `fun x => (innerₛₗ ℂ (E₂ x)).comp E₂ - (r : ℂ) • (innerₛₗ ℂ (E₁ x)).comp E₁`. Establish `hψ : ∀ x y, ψ x y = inner ℂ (E₂ x) (E₂ y) - (r : ℂ) * inner ℂ (E₁ x) (E₁ y)`.

Introduce `x y`. Use `first`. Consider the case `rfl`. Consider the case `simp [ψ]`. Establish `hψinv : ∀ Z x y, ψ (M.act Z x) y = ψ x (M.act (adjZ Z) y)`.

Introduce `Z x y`. Rewrite using `[hψ, hψ, h₁, h₂]`. Establish `hψsmul : ∀ (c : ℂ) x y, ψ (c • x) y = (starRingEnd ℂ) c * ψ x y`. Introduce `c x y`. Rewrite using `[hψ, hψ, map_smul, map_smul, inner_smul_left, inner_smul_left]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hψconj : ∀ x y, ψ x y = (starRingEnd ℂ) (ψ y x)`. Introduce `x y`. Rewrite using `[hψ, hψ, map_sub, map_mul, inner_conj_symm, inner_conj_symm, Complex.conj_ofReal]`. Establish `hψ00 : ψ v₀ v₀ = 0`.

Rewrite using `[hψ, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]`. Establish `h` using `congrArg (fun t : ℝ => (t : ℂ)) hrr`. Move the coercions through the operations in `at h`. Take the linear combination `-h`. Establish `hkey : ∀ y, ψ v₀ y = 0`.

Introduce `y`. Take `⟨W₁, hW₁f, hyW₁, hW₁K⟩` from `M.kfin y`. Take `⟨W₀, hW₀f, hv₀W₀, hW₀K⟩` from `M.kfin v₀`. Use `haveI := hW₁f`. Use `haveI := hW₀f`.

Use `haveI : FiniteDimensional ℂ ↥(W₁ ⊔ W₀) := Submodule.finiteDimensional_sup W₁ W₀`. Establish `hWK : ∀ X, IsKC X → ∀ w ∈ W₁ ⊔ W₀, M.act X w ∈ W₁ ⊔ W₀`. Introduce `X hX w hw`. Take `⟨w₁, hw₁, w₀, hw₀, rfl⟩` from `Submodule.mem_sup.mp hw`. Rewrite using `[map_add]`.

Conclude with `Submodule.add_mem_sup (hW₁K X hX w₁ hw₁) (hW₀K X hX w₀ hw₀)`. Take `⟨a, haW, ha⟩` from `exists_repr_on_finiteDimensional E₁ hE (W₁ ⊔ W₀) (ψ v₀)`. Establish `heig : ∀ Z, IsKC Z → ∀ μ : ℝ, M.act Z v₀ = (μ : ℂ) • v₀ → M.act Z a = (μ : ℂ) • a`. Introduce `Z hZ μ hZv`. Establish `hmem : M.act Z a - (μ : ℂ) • a ∈ W₁ ⊔ W₀` using `Submodule.sub_mem _ (hWK Z hZ a haW) (Submodule.smul_mem _ _ haW)`.

Establish `h3 : ∀ x ∈ W₁ ⊔ W₀, inner ℂ (E₁ (M.act Z a - (μ : ℂ) • a)) (E₁ x) = 0`. Introduce `x hx`. Establish `hx' : M.act (adjZ Z) x ∈ W₁ ⊔ W₀` using `hWK _ (isKC_adjZ hZ) _ hx`. Rewrite using `[map_sub E₁, map_smul E₁, inner_sub_left, inner_smul_left, h₁, ha _ hx', ha _ hx, ← hψinv, hZv, hψsmul, sub_self]`. Establish `h4` using `h3 _ hmem`.

Rewrite `h4` using `[inner_self_eq_zero]`. Conclude with `sub_eq_zero.mp (hE (by rw [h4, map_zero]))`. Establish `hahw : a ∈ hwSub M.act Λ`. Rewrite using `[mem_hwSub_iff_eigen]`. Establish `hv₀hw` using `(mem_hwSub_iff_eigen M.act Λ v₀).mp v₀s.2`.

Use `⟨fun c => ?_, fun c d hcd => ?_⟩` and prove the remaining obligations. Establish `h` using `heig (Eab c c) (isKC_Eab (sameBlock_self c)) ((Λ c : ℚ) : ℝ) (by rw [hv₀hw.1 c]; push_cast; rfl)`. Rewrite using `[h]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `h` using `heig (Eab c d) (isKC_Eab (sameBlock_of_posC hcd)) 0 (by rw [hv₀hw.2 c d hcd]; simp)`. Rewrite using `[h]`. Simplify using the standard rewrite rules. Take `⟨t, ht⟩` from `hspan ⟨a, hahw⟩`. Establish `hat : a = t • v₀`.

Use `congrArg Subtype.val ht` as an intermediate fact. Simplify using `using this.symm`. Establish `hEa : E₁ a = 0`. Establish `h1` using `ha a haW`. Establish `h2 : ψ v₀ a = 0` using `by rw [hat, map_smul, hψ00, smul_zero]`.

Rewrite `h1` using `[h2, inner_self_eq_zero]`. Conclude with `h1`. Rewrite using `[← ha y (Submodule.mem_sup_left hyW₁), hEa, inner_zero_left]`. Establish `hall : ∀ x y, ψ x y = 0`. Set `N : Submodule ℂ M.V` to `⨅ x, LinearMap.ker (ψ x)`.

Establish `hmemN : ∀ y, y ∈ N ↔ ∀ x, ψ x y = 0`. Introduce `y`. Simplify using `only [N, Submodule.mem_iInf, LinearMap.mem_ker]`. Establish `hstab : ∀ Z, ∀ y ∈ N, M.act Z y ∈ N`. Introduce `Z y hy`.

Rewrite `hy`, the goal using `[hmemN]`. Introduce `x`. Rewrite using `[← adjZ_adjZ Z, ← hψinv]`. Conclude with `hy _`. Establish `hv₀N : v₀ ∈ N`.

Rewrite using `[hmemN]`. Introduce `x`. Rewrite using `[hψconj, hkey, map_zero]`. Establish `hirr' : Nontrivial M.V ∧ ∀ N : Submodule ℂ M.V, (∀ Z, ∀ y ∈ N, M.act Z y ∈ N) → N = ⊥ ∨ N = ⊤` using `hirr`. Break down `hirr'.2 N hstab with hN | hN` into its components or cases.

Conclude with `absurd (by rw [hN] at hv₀N; exact (Submodule.mem_bot ℂ).mp hv₀N) hv₀`. Introduce `x y`. Establish `hy : y ∈ N` using `by rw [hN]; exact Submodule.mem_top`. Conclude with `(hmemN y).mp hy x`. Use `⟨Real.sqrt r, fun y => ?_⟩` and prove the remaining obligations.

Establish `hsq : ‖E₂ y‖ ^ 2 = r * ‖E₁ y‖ ^ 2`. Establish `h` using `hall y y`. Rewrite `h` using `[hψ, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]`. Establish `h' : ((‖E₂ y‖ ^ 2 : ℝ) : ℂ) = ((r * ‖E₁ y‖ ^ 2 : ℝ) : ℂ)`. Use `push_cast`.

Take the linear combination `h`. Conclude with `h'` after adjusting the coercions. Rewrite using `[← Real.sqrt_sq (norm_nonneg (E₂ y)), hsq, Real.sqrt_mul hr0, Real.sqrt_sq (norm_nonneg _)]`.
-/
theorem norm_proportional_of_irreducible (p q : ℕ) (M : GKMod p q) (Λ : Ix p q → ℚ)
    (H₁ H₂ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂]
    [InnerProductSpace ℂ H₂] (E₁ : M.V →ₗ[ℂ] H₁) (E₂ : M.V →ₗ[ℂ] H₂) (hirr : IrrGK M)
    (hΛ : Module.finrank ℂ ↥(hwSub M.act Λ) = 1) (hE : Function.Injective E₁)
    (h₁ : ∀ Z x y, inner ℂ (E₁ (M.act Z x)) (E₁ y) = inner ℂ (E₁ x) (E₁ (M.act (adjZ Z) y)))
    (h₂ : ∀ Z x y, inner ℂ (E₂ (M.act Z x)) (E₂ y) = inner ℂ (E₂ x) (E₂ (M.act (adjZ Z) y))) :
    ∃ c : ℝ, ∀ y, ‖E₂ y‖ = c * ‖E₁ y‖ := by
  classical
  obtain ⟨v₀s, hv₀s, hspan⟩ := finrank_eq_one_iff'.mp hΛ
  set v₀ : M.V := (v₀s : M.V) with hv₀def
  have hv₀ : v₀ ≠ 0 := fun h => hv₀s (Subtype.ext h)
  have hE₁v₀ : E₁ v₀ ≠ 0 := fun h => hv₀ (hE (by rw [h, map_zero]))

  set r : ℝ := ‖E₂ v₀‖ ^ 2 / ‖E₁ v₀‖ ^ 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have hn1 : ‖E₁ v₀‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hE₁v₀)
  have hrr : r * ‖E₁ v₀‖ ^ 2 = ‖E₂ v₀‖ ^ 2 := div_mul_cancel₀ _ hn1

  let ψ : M.V → M.V →ₗ[ℂ] ℂ := fun x =>
    (innerₛₗ ℂ (E₂ x)).comp E₂ - (r : ℂ) • (innerₛₗ ℂ (E₁ x)).comp E₁
  have hψ : ∀ x y, ψ x y = inner ℂ (E₂ x) (E₂ y) - (r : ℂ) * inner ℂ (E₁ x) (E₁ y) := by
    intro x y
    first
      | rfl
      | simp [ψ]
  have hψinv : ∀ Z x y, ψ (M.act Z x) y = ψ x (M.act (adjZ Z) y) := by
    intro Z x y
    rw [hψ, hψ, h₁, h₂]
  have hψsmul : ∀ (c : ℂ) x y, ψ (c • x) y = (starRingEnd ℂ) c * ψ x y := by
    intro c x y
    rw [hψ, hψ, map_smul, map_smul, inner_smul_left, inner_smul_left]
    ring
  have hψconj : ∀ x y, ψ x y = (starRingEnd ℂ) (ψ y x) := by
    intro x y
    rw [hψ, hψ, map_sub, map_mul, inner_conj_symm, inner_conj_symm, Complex.conj_ofReal]
  have hψ00 : ψ v₀ v₀ = 0 := by
    rw [hψ, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
    have h := congrArg (fun t : ℝ => (t : ℂ)) hrr
    push_cast at h
    linear_combination -h

  have hkey : ∀ y, ψ v₀ y = 0 := by
    intro y
    obtain ⟨W₁, hW₁f, hyW₁, hW₁K⟩ := M.kfin y
    obtain ⟨W₀, hW₀f, hv₀W₀, hW₀K⟩ := M.kfin v₀
    haveI := hW₁f
    haveI := hW₀f
    haveI : FiniteDimensional ℂ ↥(W₁ ⊔ W₀) := Submodule.finiteDimensional_sup W₁ W₀
    have hWK : ∀ X, IsKC X → ∀ w ∈ W₁ ⊔ W₀, M.act X w ∈ W₁ ⊔ W₀ := by
      intro X hX w hw
      obtain ⟨w₁, hw₁, w₀, hw₀, rfl⟩ := Submodule.mem_sup.mp hw
      rw [map_add]
      exact Submodule.add_mem_sup (hW₁K X hX w₁ hw₁) (hW₀K X hX w₀ hw₀)
    obtain ⟨a, haW, ha⟩ := exists_repr_on_finiteDimensional E₁ hE (W₁ ⊔ W₀) (ψ v₀)

    have heig : ∀ Z, IsKC Z → ∀ μ : ℝ, M.act Z v₀ = (μ : ℂ) • v₀ → M.act Z a = (μ : ℂ) • a := by
      intro Z hZ μ hZv
      have hmem : M.act Z a - (μ : ℂ) • a ∈ W₁ ⊔ W₀ :=
        Submodule.sub_mem _ (hWK Z hZ a haW) (Submodule.smul_mem _ _ haW)
      have h3 : ∀ x ∈ W₁ ⊔ W₀, inner ℂ (E₁ (M.act Z a - (μ : ℂ) • a)) (E₁ x) = 0 := by
        intro x hx
        have hx' : M.act (adjZ Z) x ∈ W₁ ⊔ W₀ := hWK _ (isKC_adjZ hZ) _ hx
        rw [map_sub E₁, map_smul E₁, inner_sub_left, inner_smul_left, h₁, ha _ hx', ha _ hx,
          ← hψinv, hZv, hψsmul, sub_self]
      have h4 := h3 _ hmem
      rw [inner_self_eq_zero] at h4
      exact sub_eq_zero.mp (hE (by rw [h4, map_zero]))
    have hahw : a ∈ hwSub M.act Λ := by
      rw [mem_hwSub_iff_eigen]
      have hv₀hw := (mem_hwSub_iff_eigen M.act Λ v₀).mp v₀s.2
      refine ⟨fun c => ?_, fun c d hcd => ?_⟩
      · have h := heig (Eab c c) (isKC_Eab (sameBlock_self c)) ((Λ c : ℚ) : ℝ)
          (by rw [hv₀hw.1 c]; push_cast; rfl)
        rw [h]
        push_cast
        rfl
      · have h := heig (Eab c d) (isKC_Eab (sameBlock_of_posC hcd)) 0
          (by rw [hv₀hw.2 c d hcd]; simp)
        rw [h]
        simp
    obtain ⟨t, ht⟩ := hspan ⟨a, hahw⟩
    have hat : a = t • v₀ := by
      have := congrArg Subtype.val ht
      simpa using this.symm
    have hEa : E₁ a = 0 := by
      have h1 := ha a haW
      have h2 : ψ v₀ a = 0 := by rw [hat, map_smul, hψ00, smul_zero]
      rw [h2, inner_self_eq_zero] at h1
      exact h1
    rw [← ha y (Submodule.mem_sup_left hyW₁), hEa, inner_zero_left]

  have hall : ∀ x y, ψ x y = 0 := by
    let N : Submodule ℂ M.V := ⨅ x, LinearMap.ker (ψ x)
    have hmemN : ∀ y, y ∈ N ↔ ∀ x, ψ x y = 0 := by
      intro y
      simp only [N, Submodule.mem_iInf, LinearMap.mem_ker]
    have hstab : ∀ Z, ∀ y ∈ N, M.act Z y ∈ N := by
      intro Z y hy
      rw [hmemN] at hy ⊢
      intro x
      rw [← adjZ_adjZ Z, ← hψinv]
      exact hy _
    have hv₀N : v₀ ∈ N := by
      rw [hmemN]
      intro x
      rw [hψconj, hkey, map_zero]
    have hirr' : Nontrivial M.V ∧ ∀ N : Submodule ℂ M.V, (∀ Z, ∀ y ∈ N, M.act Z y ∈ N) →
        N = ⊥ ∨ N = ⊤ := hirr
    rcases hirr'.2 N hstab with hN | hN
    · exact absurd (by rw [hN] at hv₀N; exact (Submodule.mem_bot ℂ).mp hv₀N) hv₀
    · intro x y
      have hy : y ∈ N := by rw [hN]; exact Submodule.mem_top
      exact (hmemN y).mp hy x
  refine ⟨Real.sqrt r, fun y => ?_⟩
  have hsq : ‖E₂ y‖ ^ 2 = r * ‖E₁ y‖ ^ 2 := by
    have h := hall y y
    rw [hψ, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h' : ((‖E₂ y‖ ^ 2 : ℝ) : ℂ) = ((r * ‖E₁ y‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      linear_combination h
    exact_mod_cast h'
  rw [← Real.sqrt_sq (norm_nonneg (E₂ y)), hsq, Real.sqrt_mul hr0, Real.sqrt_sq (norm_nonneg _)]

end GlobalTheory.FockTensor
