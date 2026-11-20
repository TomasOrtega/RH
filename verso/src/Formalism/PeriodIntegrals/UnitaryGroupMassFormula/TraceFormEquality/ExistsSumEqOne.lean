import Mathlib
import Formalism.PeriodIntegrals.SameFormAllLevels

noncomputable section

namespace PI.Dv.HermitianFormEquivalence

open PI.Dv

section Ideal

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

/- English proof (translation)
Rewrite using `[Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (by intro g; simp)]`. Simplify using `[LinearMap.sum_apply]`.
-/
lemma asAlg_apply {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V)
    (a : MonoidAlgebra K G) (x : V) : ρ.asAlgebraHom a x = ∑ g : G, a.coeff g • ρ g x := by
  rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply,
    Finsupp.sum_fintype _ _ (by intro g; simp)]
  simp [LinearMap.sum_apply]

def phi (T : GoodSet K G) (s : T.S) : Module.End K (T.W s) →ₗ[K] MonoidAlgebra K G :=
  ∑ y : G, ((((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K)) •
    (LinearMap.trace K (T.W s) ∘ₗ LinearMap.mulRight K (T.tau s y⁻¹))).smulRight
      (MonoidAlgebra.of K G y)

/- English proof (translation)
Simplify using `[phi, LinearMap.sum_apply]`.
-/
lemma phi_apply (T : GoodSet K G) (s : T.S) (f : Module.End K (T.W s)) :
    phi T s f = ∑ y : G, ((((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K)) *
      LinearMap.trace K (T.W s) (f * T.tau s y⁻¹)) • MonoidAlgebra.of K G y := by
  simp [phi, LinearMap.sum_apply]

/- English proof (translation)
Proceed by induction on `a using MonoidAlgebra.induction_on with`. Consider the case `of z`. Rewrite using `[Representation.asAlgebraHom_of, phi_apply, eS, Finset.sum_mul]`. Use `Fintype.sum_equiv (Equiv.mulRight z) _ _ ?_` and prove the remaining obligations. Introduce `x`.

Simplify using `only [Equiv.coe_mulRight, smul_mul_assoc, ← map_mul, mul_inv_rev]`. Use `congr 2`. Rewrite using `[mul_inv_cancel_left]`. Consider the case `add a b ha hb => rw [mul_add, ha, hb, map_add, map_add]`. Consider the case `smul r a ha => rw [mul_smul_comm, ha, map_smul, map_smul]`.
-/
lemma eS_mul (T : GoodSet K G) (s : T.S) (a : MonoidAlgebra K G) :
    eS T s * a = phi T s ((T.tau s).asAlgebraHom a) := by
  induction a using MonoidAlgebra.induction_on with
  | of z =>
    rw [Representation.asAlgebraHom_of, phi_apply, eS, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulRight z) _ _ ?_
    intro x
    simp only [Equiv.coe_mulRight, smul_mul_assoc, ← map_mul, mul_inv_rev]
    congr 2
    rw [mul_inv_cancel_left]
  | add a b ha hb => rw [mul_add, ha, hb, map_add, map_add]
  | smul r a ha => rw [mul_smul_comm, ha, map_smul, map_smul]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, p v ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hp (LinearMap.ext h)`. Set `b` to `Module.finBasis K W`.

Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, b.coord k (p v) ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hv (b.ext_elem fun k => by simpa [Module.Basis.coord_apply] using h k)`. Set `ψ : Module.Dual K W` to `(b.coord k (p v))⁻¹ • b.coord k`.

Establish `hψ : ψ (p v) = 1`. Simplify using `only [ψ, LinearMap.smul_apply, smul_eq_mul]`. Conclude with `inv_mul_cancel₀ hk`. Use `⟨Module.finrank K W, fun i => ψ.smulRight (b i), fun i => (b.coord i).smulRight v, ?_⟩` and prove the remaining obligations. Use extensionality with `u`.

Simplify using `only [LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smulRight_apply, map_smul, hψ, Module.End.one_apply]`. Use `conv_rhs => rw [← b.sum_repr u]`. Simplify using `[Module.Basis.coord_apply]`.
-/
lemma exists_sum_eq_one {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (p : Module.End K W) (hp : p ≠ 0) :
    ∃ n : ℕ, ∃ f g : Fin n → Module.End K W, ∑ i, f i * p * g i = 1 := by
  obtain ⟨v, hv⟩ : ∃ v, p v ≠ 0 := by
    by_contra h
    push Not at h
    exact hp (LinearMap.ext h)
  let b := Module.finBasis K W
  obtain ⟨k, hk⟩ : ∃ k, b.coord k (p v) ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (b.ext_elem fun k => by simpa [Module.Basis.coord_apply] using h k)
  let ψ : Module.Dual K W := (b.coord k (p v))⁻¹ • b.coord k
  have hψ : ψ (p v) = 1 := by
    simp only [ψ, LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hk
  refine ⟨Module.finrank K W, fun i => ψ.smulRight (b i), fun i => (b.coord i).smulRight v, ?_⟩
  ext u
  simp only [LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smulRight_apply, map_smul,
    hψ, Module.End.one_apply]
  conv_rhs => rw [← b.sum_repr u]
  simp [Module.Basis.coord_apply]

/- English proof (translation)
Establish `hp : (T.tau s).asAlgebraHom (eps P0) ≠ 0`. Introduce `h`. Use `hM s` as an intermediate fact. Rewrite `this` using `[nS, h, LinearMap.range_zero, finrank_bot]`. Conclude with `zero_ne_one this`.

Take `⟨n, f, g, hfg⟩` from `exists_sum_eq_one _ hp`. Use `⟨n, fun i => Function.surjInv (T.irr s) (f i), fun i => Function.surjInv (T.irr s) (g i), ?_⟩` and prove the remaining obligations. Establish `h1 : (T.tau s).asAlgebraHom (∑ i, Function.surjInv (T.irr s) (f i) * eps P0 * Function.surjInv (T.irr s) (g i)) = 1`. Rewrite using `[map_sum]`. Simplify using `only [map_mul, Function.surjInv_eq (T.irr s)]`.

Conclude with `hfg`. Establish `h2` using `eS_mul T s (∑ i, Function.surjInv (T.irr s) (f i) * eps P0 * Function.surjInv (T.irr s) (g i))`. Rewrite `h2` using `[h1, ← map_one (T.tau s).asAlgebraHom, ← eS_mul, mul_one, Finset.mul_sum]`. Use `conv_lhs => rw [← h2]`. Simplify using `only [mul_assoc]`.
-/
lemma eS_mem (T : GoodSet K G) (P0 : Pair K G) (hM : M1 T P0) (s : T.S) :
    ∃ n : ℕ, ∃ a b : Fin n → MonoidAlgebra K G, eS T s = ∑ i, eS T s * a i * eps P0 * b i := by
  have hp : (T.tau s).asAlgebraHom (eps P0) ≠ 0 := by
    intro h
    have := hM s
    rw [nS, h, LinearMap.range_zero, finrank_bot] at this
    exact zero_ne_one this
  obtain ⟨n, f, g, hfg⟩ := exists_sum_eq_one _ hp
  refine ⟨n, fun i => Function.surjInv (T.irr s) (f i),
    fun i => Function.surjInv (T.irr s) (g i), ?_⟩
  have h1 : (T.tau s).asAlgebraHom
      (∑ i, Function.surjInv (T.irr s) (f i) * eps P0 * Function.surjInv (T.irr s) (g i)) = 1 := by
    rw [map_sum]
    simp only [map_mul, Function.surjInv_eq (T.irr s)]
    exact hfg
  have h2 := eS_mul T s (∑ i, Function.surjInv (T.irr s) (f i) * eps P0 *
    Function.surjInv (T.irr s) (g i))
  rw [h1, ← map_one (T.tau s).asAlgebraHom, ← eS_mul, mul_one, Finset.mul_sum] at h2
  conv_lhs => rw [← h2]
  simp only [mul_assoc]

/- English proof (translation)
Use `choose n a b h using eS_mem T P0 hM`. Set `ι` to `Σ s : T.S, Fin (n s)`. Set `e` to `(Fintype.equivFin ι)`. Use `⟨Fintype.card ι, fun i => eS T (e.symm i).1 * a _ (e.symm i).2, fun i => b _ (e.symm i).2, ?_⟩` and prove the remaining obligations. Rewrite using `[eG, Fintype.sum_equiv e.symm (fun i => eS T (e.symm i).1 * a _ (e.symm i).2 * eps P0 * b _ (e.symm i).2) (fun t : ι => eS T t.1 * a _ t.2 * eps P0 * b _ t.2) (fun _ => rfl), Fintype.sum_sigma]`.

Conclude with `Finset.sum_congr rfl fun s _ => h s`.
-/
lemma eG_mem (T : GoodSet K G) (P0 : Pair K G) (hM : M1 T P0) :
    ∃ n : ℕ, ∃ a b : Fin n → MonoidAlgebra K G, eG T = ∑ i, a i * eps P0 * b i := by
  classical
  choose n a b h using eS_mem T P0 hM
  let ι := Σ s : T.S, Fin (n s)
  let e := (Fintype.equivFin ι)
  refine ⟨Fintype.card ι, fun i => eS T (e.symm i).1 * a _ (e.symm i).2,
    fun i => b _ (e.symm i).2, ?_⟩
  rw [eG, Fintype.sum_equiv e.symm (fun i => eS T (e.symm i).1 * a _ (e.symm i).2 * eps P0 *
      b _ (e.symm i).2) (fun t : ι => eS T t.1 * a _ t.2 * eps P0 * b _ t.2) (fun _ => rfl),
    Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun s _ => h s

end Ideal

end PI.Dv.HermitianFormEquivalence
