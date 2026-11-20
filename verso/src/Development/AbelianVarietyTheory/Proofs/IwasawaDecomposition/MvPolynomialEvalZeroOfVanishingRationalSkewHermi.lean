import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

/- English proof (translation)
Use `set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc`. Establish `hcc : ∀ x, c (c x) = x` using `fun x => by simp [hc]`. Establish `hσc : ∀ (σ : L →+* ℂ) x, σ (c x) = ComplexEmbedding.conjugate σ x` using `fun σ x => by`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Conclude with `IsCMField.complexEmbedding_complexConj L σ x`.

Set `B` to `NumberField.canonicalEmbedding.latticeBasis L`. Set `b : Module.Free.ChooseBasisIndex ℤ (𝓞 L) → L` to `fun k => NumberField.integralBasis L k`. Establish `hB : ∀ k, B k = fun σ => σ (b k)` using `fun k => by`. Use function extensionality and compare the values at `σ`. Rewrite using `[NumberField.canonicalEmbedding.latticeBasis_apply, NumberField.canonicalEmbedding.apply_at]`.

Establish `H1 : ∀ σ₀ : L →+* ℂ, ∃ a : Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℂ, ∀ σ, ∑ k, a k * σ (b k) = if σ = σ₀ then 1 else 0`. Introduce `σ₀`. Use `⟨B.repr (Pi.single σ₀ 1), fun σ => ?_⟩` and prove the remaining obligations. Use `congrFun (B.sum_repr (Pi.single σ₀ 1)) σ` as an intermediate fact. Simplify `this` using `[Finset.sum_apply, hB, Pi.single_apply]`.

Use `choose a ha using H1`. Set `S : Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 L) → Matrix (Fin n) (Fin n) L` to `fun J => Matrix.of fun u v => (if u = J.1 ∧ v = J.2.1 then b J.2.2 else 0) - (if u = J.2.1 ∧ v = J.1 then c (b J.2.2) else 0)`. Set `r : Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 L) → (L →+* ℂ) × Fin n × Fin n → ℂ` to `fun J => upt (ratPt (S J))`. Establish `hSk : ∀ J u v, S J u v + c (S J v u) = 0`. Introduce `J u v`.

Simplify using `only [S, Matrix.of_apply, map_sub]`. Apply the tactic sequence `split_ifs <;> simp only [map_zero, hcc, sub_zero, zero_sub, add_zero, zero_add] <;> first | ring1 | (exfalso; tauto)`. Establish `hskew : ∀ t : Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℚ, (∑ J, (t J : L) • S J) + ((∑ J, (t J : L) • S J).map c)ᵀ = 0`. Introduce `t`. Use extensionality with `u v`.

Simplify using `only [Matrix.add_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, map_ratCast, Matrix.zero_apply]`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_eq_zero fun J _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_add, hSk, mul_zero]`. Establish `hrat : ∀ t : Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℚ, (fun p => ∑ J, (t J : ℂ) * r J p) = upt (ratPt (∑ J, (t J : L) • S J))`.

Introduce `t`. Use function extensionality and compare the values at `p`. Simplify using `only [r, upt, ratPt, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, map_ratCast]`. Set `Q'` to `MvPolynomial.bind₁ (fun p => ∑ J, MvPolynomial.X J * MvPolynomial.C (r J p)) Q`. Establish `heval : ∀ z, MvPolynomial.eval z Q' = MvPolynomial.eval (fun p => ∑ J, z J * r J p) Q`.

Introduce `z`. Express the relevant statement in the definitionally equal form `MvPolynomial.eval₂Hom (RingHom.id ℂ) z Q' = MvPolynomial.eval₂Hom (RingHom.id ℂ) _ Q`. Rewrite using `[MvPolynomial.eval₂Hom_bind₁]`. Use `congr 2`. Use function extensionality and compare the values at `p`.

Simplify using `[map_sum]`. Establish `hQ' : Q' = 0`. Use `MvPolynomial.funext_set (fun _ => Set.range (Rat.cast : ℚ → ℂ)) (fun _ => Set.infinite_range_of_injective Rat.cast_injective) fun z hz => ?_` and prove the remaining obligations. Use `choose t ht using fun J => hz J (Set.mem_univ _)`. Establish `hz' : z = fun J => (t J : ℂ)` using `by funext J; exact (ht J).symm`.

Rewrite using `[heval, hz', hrat, hQ _ (hskew t), map_zero]`. Set `z : Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℂ` to `fun J => (1 / 2) * ∑ σ₀, Y σ₀ J.1 J.2.1 * a σ₀ J.2.2`. Establish `key : ∀ u v (τ : L →+* ℂ), ∑ k, z (u, v, k) * τ (b k) = (1 / 2) * Y τ u v`. Introduce `u v τ`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [z, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun σ₀ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `_ = ∑ σ₀, (1 / 2) * (Y σ₀ u v * ∑ k, a σ₀ k * τ (b k)) := by`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun σ₀ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Use `_ = (1 / 2) * Y τ u v := by`. Simplify using `only [ha, mul_ite, mul_one, mul_zero]`.

Simplify using the standard rewrite rules. Establish `hcomb : upt Y = fun p => ∑ J, z J * r J p`. Use function extensionality and compare the values at `⟨σ, u, v⟩`. Establish `e1 : ∀ J, r J (σ, u, v) = (if u = J.1 ∧ v = J.2.1 then σ (b J.2.2) else 0) - (if u = J.2.1 ∧ v = J.1 then ComplexEmbedding.conjugate σ (b J.2.2) else 0)`. Introduce `J`.

Simplify using `only [r, upt, ratPt, S, Matrix.map_apply, Matrix.of_apply, map_sub]`. Simplify using `only [apply_ite σ, map_zero, hσc]`. Simplify using `only [e1, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero]`. Rewrite using `[Fintype.sum_prod_type, Fintype.sum_prod_type]`. Simplify using `only [Fintype.sum_prod_type, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Establish `e2 : ∀ (f : Fin n → Fin n → Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℂ) (p q : Fin n), (∑ x, ∑ x_1, ∑ x_2, if p = x then if q = x_1 then f x x_1 x_2 else 0 else 0) = ∑ k, f p q k`. Introduce `f p q`. Rewrite using `[Finset.sum_eq_single p (fun x _ hx => by simp [Ne.symm hx]) (by simp), Finset.sum_eq_single q (fun x _ hx => by simp [Ne.symm hx]) (by simp)]`. Simplify using the standard rewrite rules. Establish `e3 : ∀ (f : Fin n → Fin n → Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℂ) (p q : Fin n), (∑ x, ∑ x_1, ∑ x_2, if q = x_1 then if p = x then f x x_1 x_2 else 0 else 0) = ∑ k, f p q k`.

Introduce `f p q`. Rewrite using `[Finset.sum_eq_single p (fun x _ hx => by simp [Ne.symm hx]) (by simp), Finset.sum_eq_single q (fun x _ hx => by simp [Ne.symm hx]) (by simp)]`. Simplify using the standard rewrite rules. Rewrite using `[e2 (fun x x_1 x_2 => z (x, x_1, x_2) * σ (b x_2)), e3 (fun x x_1 x_2 => z (x, x_1, x_2) * (ComplexEmbedding.conjugate σ) (b x_2)), key, key, hY σ]`. Simplify using `only [upt, Matrix.neg_apply, Matrix.transpose_apply]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hcomb, ← heval, hQ', map_zero]`.
-/
theorem eval_upt_eq_zero_of_skew (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (Q : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (hQ : ∀ S : Matrix (Fin n) (Fin n) L, S + (S.map (IsCMField.complexConj L : L →+* L))ᵀ = 0 →
      MvPolynomial.eval (upt (ratPt S)) Q = 0)
    (Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (hY : ∀ σ, Y (ComplexEmbedding.conjugate σ) = -(Y σ)ᵀ) :
    MvPolynomial.eval (upt Y) Q = 0 := by
  classical
  set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc
  have hcc : ∀ x, c (c x) = x := fun x => by simp [hc]
  have hσc : ∀ (σ : L →+* ℂ) x, σ (c x) = ComplexEmbedding.conjugate σ x := fun σ x => by
    rw [ComplexEmbedding.conjugate_coe_eq]; exact IsCMField.complexEmbedding_complexConj L σ x

  let B := NumberField.canonicalEmbedding.latticeBasis L
  let b : Module.Free.ChooseBasisIndex ℤ (𝓞 L) → L := fun k => NumberField.integralBasis L k
  have hB : ∀ k, B k = fun σ => σ (b k) := fun k => by
    funext σ; rw [NumberField.canonicalEmbedding.latticeBasis_apply, NumberField.canonicalEmbedding.apply_at]
  have H1 : ∀ σ₀ : L →+* ℂ, ∃ a : Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℂ,
      ∀ σ, ∑ k, a k * σ (b k) = if σ = σ₀ then 1 else 0 := by
    intro σ₀
    refine ⟨B.repr (Pi.single σ₀ 1), fun σ => ?_⟩
    have := congrFun (B.sum_repr (Pi.single σ₀ 1)) σ
    simpa [Finset.sum_apply, hB, Pi.single_apply] using this
  choose a ha using H1

  let S : Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 L) → Matrix (Fin n) (Fin n) L := fun J =>
    Matrix.of fun u v => (if u = J.1 ∧ v = J.2.1 then b J.2.2 else 0) -
      (if u = J.2.1 ∧ v = J.1 then c (b J.2.2) else 0)
  let r : Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 L) → (L →+* ℂ) × Fin n × Fin n → ℂ :=
    fun J => upt (ratPt (S J))
  have hSk : ∀ J u v, S J u v + c (S J v u) = 0 := by
    intro J u v
    simp only [S, Matrix.of_apply, map_sub]
    split_ifs <;> simp only [map_zero, hcc, sub_zero, zero_sub, add_zero, zero_add] <;>
      first | ring1 | (exfalso; tauto)
  have hskew : ∀ t : Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℚ,
      (∑ J, (t J : L) • S J) + ((∑ J, (t J : L) • S J).map c)ᵀ = 0 := by
    intro t; ext u v
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, map_ratCast, Matrix.zero_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun J _ => ?_
    rw [← mul_add, hSk, mul_zero]
  have hrat : ∀ t : Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℚ,
      (fun p => ∑ J, (t J : ℂ) * r J p) = upt (ratPt (∑ J, (t J : L) • S J)) := by
    intro t; funext p
    simp only [r, upt, ratPt, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      map_sum, map_mul, map_ratCast]

  let Q' := MvPolynomial.bind₁ (fun p => ∑ J, MvPolynomial.X J * MvPolynomial.C (r J p)) Q
  have heval : ∀ z, MvPolynomial.eval z Q' = MvPolynomial.eval (fun p => ∑ J, z J * r J p) Q := by
    intro z
    change MvPolynomial.eval₂Hom (RingHom.id ℂ) z Q' = MvPolynomial.eval₂Hom (RingHom.id ℂ) _ Q
    rw [MvPolynomial.eval₂Hom_bind₁]
    congr 2
    funext p
    simp [map_sum]
  have hQ' : Q' = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range (Rat.cast : ℚ → ℂ))
      (fun _ => Set.infinite_range_of_injective Rat.cast_injective) fun z hz => ?_
    choose t ht using fun J => hz J (Set.mem_univ _)
    have hz' : z = fun J => (t J : ℂ) := by funext J; exact (ht J).symm
    rw [heval, hz', hrat, hQ _ (hskew t), map_zero]

  let z : Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℂ :=
    fun J => (1 / 2) * ∑ σ₀, Y σ₀ J.1 J.2.1 * a σ₀ J.2.2
  have key : ∀ u v (τ : L →+* ℂ), ∑ k, z (u, v, k) * τ (b k) = (1 / 2) * Y τ u v := by
    intro u v τ
    calc ∑ k, z (u, v, k) * τ (b k)
        = ∑ k, ∑ σ₀, (1 / 2) * (Y σ₀ u v * (a σ₀ k * τ (b k))) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [z, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun σ₀ _ => ?_
          ring
      _ = ∑ σ₀, (1 / 2) * (Y σ₀ u v * ∑ k, a σ₀ k * τ (b k)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun σ₀ _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
      _ = (1 / 2) * Y τ u v := by
          simp only [ha, mul_ite, mul_one, mul_zero]
          simp
  have hcomb : upt Y = fun p => ∑ J, z J * r J p := by
    funext ⟨σ, u, v⟩
    have e1 : ∀ J, r J (σ, u, v) = (if u = J.1 ∧ v = J.2.1 then σ (b J.2.2) else 0) -
        (if u = J.2.1 ∧ v = J.1 then ComplexEmbedding.conjugate σ (b J.2.2) else 0) := by
      intro J
      simp only [r, upt, ratPt, S, Matrix.map_apply, Matrix.of_apply, map_sub]
      simp only [apply_ite σ, map_zero, hσc]
    simp only [e1, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have e2 : ∀ (f : Fin n → Fin n → Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℂ) (p q : Fin n),
        (∑ x, ∑ x_1, ∑ x_2, if p = x then if q = x_1 then f x x_1 x_2 else 0 else 0) = ∑ k, f p q k := by
      intro f p q
      rw [Finset.sum_eq_single p (fun x _ hx => by simp [Ne.symm hx]) (by simp),
        Finset.sum_eq_single q (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      simp
    have e3 : ∀ (f : Fin n → Fin n → Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℂ) (p q : Fin n),
        (∑ x, ∑ x_1, ∑ x_2, if q = x_1 then if p = x then f x x_1 x_2 else 0 else 0) = ∑ k, f p q k := by
      intro f p q
      rw [Finset.sum_eq_single p (fun x _ hx => by simp [Ne.symm hx]) (by simp),
        Finset.sum_eq_single q (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      simp
    rw [e2 (fun x x_1 x_2 => z (x, x_1, x_2) * σ (b x_2)),
      e3 (fun x x_1 x_2 => z (x, x_1, x_2) * (ComplexEmbedding.conjugate σ) (b x_2)), key, key, hY σ]
    simp only [upt, Matrix.neg_apply, Matrix.transpose_apply]
    ring
  rw [hcomb, ← heval, hQ', map_zero]

end GlobalTheory.AlgWtHW
