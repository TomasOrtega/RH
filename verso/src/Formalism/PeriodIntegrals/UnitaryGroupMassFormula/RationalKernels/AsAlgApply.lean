import Mathlib
import Formalism.PeriodIntegrals.SameFormAllLevels

noncomputable section

namespace PI.Dv.RK

open MonoidAlgebra

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

/- English proof (translation)
Proceed by induction on `z using MonoidAlgebra.induction_on with`. Consider the case `of y`. Rewrite using `[Representation.asAlgebraHom_of, eS, Finset.mul_sum]`. Use `Fintype.sum_equiv (Equiv.mulLeft y) _ _ fun x => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, ← map_mul (MonoidAlgebra.of K G), ← map_mul (T.tau s)]`.

Simplify using `only [Equiv.coe_mulLeft, mul_inv_rev, inv_mul_cancel_right]`. Consider the case `add x y hx hy`. Rewrite using `[add_mul, hx, hy, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[map_add, mul_add, map_add, mul_add, add_smul]`.

Consider the case `smul r x hx`. Rewrite using `[smul_mul_assoc, hx, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, mul_smul_comm, map_smul, smul_smul, smul_eq_mul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma mul_eS (T : GoodSet K G) (s : T.S) (z : MonoidAlgebra K G) :
    z * eS T s = ∑ g : G, (((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
      LinearMap.trace K (T.W s) (T.tau s g⁻¹ * (T.tau s).asAlgebraHom z)) •
        MonoidAlgebra.of K G g := by
  induction z using MonoidAlgebra.induction_on with
  | of y =>
    rw [Representation.asAlgebraHom_of, eS, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft y) _ _ fun x => ?_
    rw [mul_smul_comm, ← map_mul (MonoidAlgebra.of K G), ← map_mul (T.tau s)]
    simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_mul_cancel_right]
  | add x y hx hy =>
    rw [add_mul, hx, hy, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_add, mul_add, map_add, mul_add, add_smul]
  | smul r x hx =>
    rw [smul_mul_assoc, hx, Finset.smul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, mul_smul_comm, map_smul, smul_smul, smul_eq_mul]
    congr 1
    ring

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, E v ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hE (LinearMap.ext h)`. Establish `hex : ¬ ∀ φ : Module.Dual K W, φ (E v) = 0` using `fun h => hv ((Module.forall_dual_apply_eq_zero_iff K _).mp h)`.

Use `push Not at hex`. Take `⟨f0, hf0⟩` from `hex`. Set `f : Module.Dual K W` to `(f0 (E v))⁻¹ • f0`. Establish `hf : f (E v) = 1` using `by simp [f, hf0]`. Set `b` to `Module.finBasis K W`.

Use `⟨Module.finrank K W, fun i => f.smulRight (b i), fun i => (b.coord i).smulRight v, ?_⟩` and prove the remaining obligations. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.sum_apply, Module.End.one_apply]`. Use `conv_rhs => rw [← b.sum_repr x]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Module.End.mul_apply, Module.End.mul_apply, LinearMap.smulRight_apply, LinearMap.smulRight_apply, map_smul, map_smul, hf, smul_eq_mul, mul_one, Module.Basis.coord_apply]`.
-/
lemma end_simple {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (E : Module.End K W) (hE : E ≠ 0) :
    ∃ (n : ℕ) (A B : Fin n → Module.End K W), ∑ i, A i * E * B i = 1 := by
  obtain ⟨v, hv⟩ : ∃ v, E v ≠ 0 := by
    by_contra h
    push Not at h
    exact hE (LinearMap.ext h)
  have hex : ¬ ∀ φ : Module.Dual K W, φ (E v) = 0 := fun h =>
    hv ((Module.forall_dual_apply_eq_zero_iff K _).mp h)
  push Not at hex
  obtain ⟨f0, hf0⟩ := hex
  let f : Module.Dual K W := (f0 (E v))⁻¹ • f0
  have hf : f (E v) = 1 := by simp [f, hf0]
  let b := Module.finBasis K W
  refine ⟨Module.finrank K W, fun i => f.smulRight (b i), fun i => (b.coord i).smulRight v, ?_⟩
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.sum_apply, Module.End.one_apply]
  conv_rhs => rw [← b.sum_repr x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, LinearMap.smulRight_apply,
    LinearMap.smulRight_apply, map_smul, map_smul, hf, smul_eq_mul, mul_one, Module.Basis.coord_apply]

/- English proof (translation)
Use `AddSubgroup.sum_mem _ fun s _ => ?_` and prove the remaining obligations. Take `⟨n, A, B, hAB⟩` from `end_simple _ (h s)`. Use `choose a ha using fun i => T.irr s (A i)`. Use `choose b hb using fun i => T.irr s (B i)`. Establish `hτ : (T.tau s).asAlgebraHom (∑ i, a i * eps P * b i) = (T.tau s).asAlgebraHom 1`.

Rewrite using `[map_one, map_sum]`. Simplify using `only [map_mul, ha, hb]`. Conclude with `hAB`. Establish `e1` using `mul_eS T s (∑ i, a i * eps P * b i)`. Establish `e2` using `mul_eS T s 1`.

Rewrite `e2` using `[one_mul]`. Establish `key : (∑ i, a i * eps P * b i) * eS T s = eS T s`. Rewrite using `[e1, e2, hτ]`. Rewrite using `[← key, Finset.sum_mul]`. Use `AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure ?_` and prove the remaining obligations.

Conclude with `⟨a i, b i * eS T s, mul_assoc _ _ _⟩`.
-/
theorem eG_mem (T : GoodSet K G) (P : Pair K G) (h : ∀ s, (T.tau s).asAlgebraHom (eps P) ≠ 0) :
    eG T ∈ AddSubgroup.closure {w | ∃ a b : MonoidAlgebra K G, w = a * eps P * b} := by
  refine AddSubgroup.sum_mem _ fun s _ => ?_
  obtain ⟨n, A, B, hAB⟩ := end_simple _ (h s)
  choose a ha using fun i => T.irr s (A i)
  choose b hb using fun i => T.irr s (B i)
  have hτ : (T.tau s).asAlgebraHom (∑ i, a i * eps P * b i) = (T.tau s).asAlgebraHom 1 := by
    rw [map_one, map_sum]
    simp only [map_mul, ha, hb]
    exact hAB
  have e1 := mul_eS T s (∑ i, a i * eps P * b i)
  have e2 := mul_eS T s 1
  rw [one_mul] at e2
  have key : (∑ i, a i * eps P * b i) * eS T s = eS T s := by
    rw [e1, e2, hτ]
  rw [← key, Finset.sum_mul]
  refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure ?_
  exact ⟨a i, b i * eS T s, mul_assoc _ _ _⟩

/- English proof (translation)
Introduce `h0`. Establish `h1 : nS T P s = 1` using `h s`. Unfold `nS at h1`. Rewrite `h1` using `[Submodule.finrank_eq_zero.mpr (by rw [h0]; exact LinearMap.range_zero)]`. Conclude with `zero_ne_one h1`.
-/
lemma tau_eps_ne (T : GoodSet K G) (P : Pair K G) (h : M1 T P) (s : T.S) :
    (T.tau s).asAlgebraHom (eps P) ≠ 0 := by
  intro h0
  have h1 : nS T P s = 1 := h s
  unfold nS at h1
  rw [Submodule.finrank_eq_zero.mpr (by rw [h0]; exact LinearMap.range_zero)] at h1
  exact zero_ne_one h1

end PI.Dv.RK
