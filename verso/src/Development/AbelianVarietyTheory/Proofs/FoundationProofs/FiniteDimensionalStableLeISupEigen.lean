import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InstSecondCountable
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.HolDS Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.HolDS

/- English proof (translation)
Establish `hpow : ∀ (n : ℕ) (v : V), φ ((T ^ n) v) = c ^ n * φ v`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro v`. Simplify using the standard rewrite rules.

Consider the case `succ n ih`. Introduce `v`. Rewrite using `[pow_succ, Module.End.mul_apply, ih, h]`. Expand and normalize the polynomial expressions, which then agree. Proceed by induction on `f using Polynomial.induction_on' with`.

Consider the case `add p q hp hq => simp [hp, hq, add_mul]`. Consider the case `monomial n a`. Rewrite using `[Polynomial.aeval_monomial, Polynomial.eval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul, hpow, smul_eq_mul, mul_assoc]`.
-/
theorem form_aeval_of_left_eigen {V : Type} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V)
    (φ : V →ₗ[ℂ] ℂ) (c : ℂ) (h : ∀ v, φ (T v) = c * φ v) (f : Polynomial ℂ) (v : V) :
    φ (Polynomial.aeval T f v) = f.eval c * φ v := by
  have hpow : ∀ (n : ℕ) (v : V), φ ((T ^ n) v) = c ^ n * φ v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, ih, h]; ring
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, add_mul]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, Module.End.mul_apply,
      Module.algebraMap_end_apply, map_smul, hpow, smul_eq_mul, mul_assoc]

/- English proof (translation)
Introduce `H _ _ _ U hU E lam hinj hfin heig hdense W hW hst`. Establish `hinner : ∀ a b : H, ⟪U a, U b⟫_ℂ = ⟪a, b⟫_ℂ` using `fun a b => (⟨(U : H →ₗ[ℂ] H), hU⟩ : H →ₗᵢ[ℂ] H).inner_map_map a b`. Establish `hleft : ∀ m, ∀ e ∈ E m, ∀ y, ⟪e, U y⟫_ℂ = lam m * ⟪e, y⟫_ℂ`. Introduce `m e he y`. Distinguish the cases in `h0 : e = 0`.

Simplify using `[h0]`. Establish `h1 : ‖lam m‖ = 1`. Use `hU e` as an intermediate fact. Rewrite `this` using `[heig m e he, norm_smul]`. Establish `hne : ‖e‖ ≠ 0` using `norm_ne_zero_iff.mpr h0`.

Conclude with `mul_right_cancel₀ hne (by rw [this, one_mul])`. Establish `h2 : lam m * (starRingEnd ℂ) (lam m) = 1`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]`. Simplify using the standard rewrite rules. Establish `h3` using `hinner e y`.

Rewrite `h3` using `[heig m e he, inner_smul_left]`. Rewrite using `[← h3, ← mul_assoc, h2, one_mul]`. Set `T : Module.End ℂ W` to `(U : H →ₗ[ℂ] H).restrict hst`. Set `f : Polynomial ℂ` to `LinearMap.charpoly T`. Establish `hf0 : f ≠ 0` using `(LinearMap.charpoly_monic T).ne_zero`.

Establish `hfT : Polynomial.aeval T f = 0` using `LinearMap.aeval_self_charpoly T`. Establish `hsfin : (lam ⁻¹' {z | f.IsRoot z}).Finite` using `(Polynomial.finite_setOf_isRoot hf0).preimage hinj.injOn`. Set `s : Finset ℕ` to `hsfin.toFinset`. Establish `hout : ∀ m, m ∉ s → ∀ e ∈ E m, ∀ y ∈ W, ⟪e, y⟫_ℂ = 0`. Introduce `m hm e he y hy`.

Establish `hne : f.eval (lam m) ≠ 0`. Introduce `h`. Conclude with `hm (hsfin.mem_toFinset.mpr h)`. Use `form_aeval_of_left_eigen T (((innerₛₗ ℂ e : H →ₗ[ℂ] ℂ)).comp W.subtype) (lam m) (fun v => hleft m e he v) f ⟨y, hy⟩` as an intermediate fact. Rewrite `this` using `[hfT]`.

Simplify using `only [LinearMap.zero_apply, map_zero] at this`. Conclude with `(mul_eq_zero.mp this.symm).resolve_left hne`. Set `F : Submodule ℂ H` to `⨆ m ∈ s, E m`. Use `haveI hF : FiniteDimensional ℂ F := by`. Establish `: F = s.sup E` using `by simp [F, Finset.sup_eq_iSup]`.

Rewrite using `[this]`. Use `infer_instance`. Establish `hFle : F ≤ ⨆ m, E m` using `iSup₂_le fun m _ => le_iSup E m`. Establish `hForth : ∀ m, m ∉ s → F ≤ (E m)ᗮ`. Introduce `m hm`.

Use `iSup₂_le fun k hk x hx => ?_` and prove the remaining obligations. Rewrite using `[Submodule.mem_orthogonal]`. Introduce `e he`. Establish `h1` using `hleft m e he x`. Rewrite `h1` using `[heig k x hx, inner_smul_right]`.

Establish `hne : lam k - lam m ≠ 0`. Introduce `h`. Use `hinj (sub_eq_zero.mp h)` as an intermediate fact. Conclude with `hm (this ▸ hk)`. Establish `: (lam k - lam m) * ⟪e, x⟫_ℂ = 0` using `by rw [sub_mul, h1, sub_self]`.

Conclude with `(mul_eq_zero.mp this).resolve_left hne`. Introduce `y hy`. Establish `hz : y - F.starProjection y ∈ (⨆ m, E m)ᗮ`. Rewrite using `[← Submodule.iInf_orthogonal, Submodule.mem_iInf]`. Introduce `m`.

Distinguish the cases in `hm : m ∈ s`. Establish `hle : E m ≤ F` using `le_iSup₂_of_le (f := fun m (_ : m ∈ s) => E m) m hm le_rfl`. Conclude with `Submodule.orthogonal_le hle (Submodule.sub_starProjection_mem_orthogonal y)`. Use `Submodule.sub_mem _ ?_ (hForth m hm (F.starProjection_apply_mem y))` and prove the remaining obligations. Rewrite using `[Submodule.mem_orthogonal]`.

Introduce `e he`. Conclude with `hout m hm e he y hy`. Establish `hz0 : y - F.starProjection y = 0`. Establish `htop : (⨆ m, E m : Submodule ℂ H).topologicalClosure = ⊤` using `Submodule.dense_iff_topologicalClosure_eq_top.mp hdense`. Rewrite `htop` using `[Submodule.topologicalClosure_eq_top_iff]`.

Rewrite `hz` using `[htop]`. Conclude with `(Submodule.mem_bot ℂ).mp hz`. Rewrite using `[sub_eq_zero.mp hz0]`. Conclude with `hFle (F.starProjection_apply_mem y)`.
-/
theorem finiteDimensional_stable_le_iSup_eigen :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (U : H →L[ℂ] H), (∀ v, ‖U v‖ = ‖v‖) → ∀ (E : ℕ → Submodule ℂ H) (lam : ℕ → ℂ), Function.Injective lam → (∀ m, FiniteDimensional ℂ (E m)) → (∀ m, ∀ e ∈ E m, U e = lam m • e) → Dense ((⨆ m, E m : Submodule ℂ H) : Set H) → ∀ (W : Submodule ℂ H), FiniteDimensional ℂ W → (∀ w ∈ W, U w ∈ W) → W ≤ ⨆ m, E m := by
  intro H _ _ _ U hU E lam hinj hfin heig hdense W hW hst
  classical
  have hinner : ∀ a b : H, ⟪U a, U b⟫_ℂ = ⟪a, b⟫_ℂ := fun a b =>
    (⟨(U : H →ₗ[ℂ] H), hU⟩ : H →ₗᵢ[ℂ] H).inner_map_map a b
  have hleft : ∀ m, ∀ e ∈ E m, ∀ y, ⟪e, U y⟫_ℂ = lam m * ⟪e, y⟫_ℂ := by
    intro m e he y
    by_cases h0 : e = 0
    · simp [h0]
    have h1 : ‖lam m‖ = 1 := by
      have := hU e
      rw [heig m e he, norm_smul] at this
      have hne : ‖e‖ ≠ 0 := norm_ne_zero_iff.mpr h0
      exact mul_right_cancel₀ hne (by rw [this, one_mul])
    have h2 : lam m * (starRingEnd ℂ) (lam m) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp
    have h3 := hinner e y
    rw [heig m e he, inner_smul_left] at h3
    rw [← h3, ← mul_assoc, h2, one_mul]
  let T : Module.End ℂ W := (U : H →ₗ[ℂ] H).restrict hst
  let f : Polynomial ℂ := LinearMap.charpoly T
  have hf0 : f ≠ 0 := (LinearMap.charpoly_monic T).ne_zero
  have hfT : Polynomial.aeval T f = 0 := LinearMap.aeval_self_charpoly T
  have hsfin : (lam ⁻¹' {z | f.IsRoot z}).Finite :=
    (Polynomial.finite_setOf_isRoot hf0).preimage hinj.injOn
  let s : Finset ℕ := hsfin.toFinset
  have hout : ∀ m, m ∉ s → ∀ e ∈ E m, ∀ y ∈ W, ⟪e, y⟫_ℂ = 0 := by
    intro m hm e he y hy
    have hne : f.eval (lam m) ≠ 0 := by
      intro h
      exact hm (hsfin.mem_toFinset.mpr h)
    have := form_aeval_of_left_eigen T (((innerₛₗ ℂ e : H →ₗ[ℂ] ℂ)).comp W.subtype) (lam m)
      (fun v => hleft m e he v) f ⟨y, hy⟩
    rw [hfT] at this
    simp only [LinearMap.zero_apply, map_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hne
  let F : Submodule ℂ H := ⨆ m ∈ s, E m
  haveI hF : FiniteDimensional ℂ F := by
    have : F = s.sup E := by simp [F, Finset.sup_eq_iSup]
    rw [this]; infer_instance
  have hFle : F ≤ ⨆ m, E m := iSup₂_le fun m _ => le_iSup E m
  have hForth : ∀ m, m ∉ s → F ≤ (E m)ᗮ := by
    intro m hm
    refine iSup₂_le fun k hk x hx => ?_
    rw [Submodule.mem_orthogonal]
    intro e he
    have h1 := hleft m e he x
    rw [heig k x hx, inner_smul_right] at h1
    have hne : lam k - lam m ≠ 0 := by
      intro h
      have := hinj (sub_eq_zero.mp h)
      exact hm (this ▸ hk)
    have : (lam k - lam m) * ⟪e, x⟫_ℂ = 0 := by rw [sub_mul, h1, sub_self]
    exact (mul_eq_zero.mp this).resolve_left hne
  intro y hy
  have hz : y - F.starProjection y ∈ (⨆ m, E m)ᗮ := by
    rw [← Submodule.iInf_orthogonal, Submodule.mem_iInf]
    intro m
    by_cases hm : m ∈ s
    · have hle : E m ≤ F := le_iSup₂_of_le (f := fun m (_ : m ∈ s) => E m) m hm le_rfl
      exact Submodule.orthogonal_le hle (Submodule.sub_starProjection_mem_orthogonal y)
    · refine Submodule.sub_mem _ ?_ (hForth m hm (F.starProjection_apply_mem y))
      rw [Submodule.mem_orthogonal]
      intro e he
      exact hout m hm e he y hy
  have hz0 : y - F.starProjection y = 0 := by
    have htop : (⨆ m, E m : Submodule ℂ H).topologicalClosure = ⊤ :=
      Submodule.dense_iff_topologicalClosure_eq_top.mp hdense
    rw [Submodule.topologicalClosure_eq_top_iff] at htop
    rw [htop] at hz
    exact (Submodule.mem_bot ℂ).mp hz
  rw [sub_eq_zero.mp hz0]
  exact hFle (F.starProjection_apply_mem y)

end GlobalTheory.HolDS
