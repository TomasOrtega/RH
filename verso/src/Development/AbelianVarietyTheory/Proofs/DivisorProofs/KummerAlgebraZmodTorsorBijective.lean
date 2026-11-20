import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapEqMk
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KummerTorsor

open GlobalTheory.KummerAlg

section
variable {B : Type} [CommRing B] {L : Type} [AddCommGroup L] [Module B L] {n : ℕ}
  (φ : MultilinearMap B (fun _ : Fin (n + 1) => L) B)

/- English proof (translation)
Rewrite using `[← prod_gen, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
-/
theorem gen_pow (f : L) : gen φ f ^ (n + 1) = algebraMap B (Alg φ) (φ fun _ => f) := by
  rw [← prod_gen, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/- English proof (translation)
Rewrite using `[Algebra.smul_def, Algebra.smul_def, ← gen_pow, ← prod_gen, Fin.prod_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem smul_gen (e f : L) :
    (φ fun _ => f) • gen φ e = φ (Fin.cons e (fun _ => f) : Fin (n + 1) → L) • gen φ f := by
  rw [Algebra.smul_def, Algebra.smul_def, ← gen_pow, ← prod_gen, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

/- English proof (translation)
Establish `: Ideal.span (Set.range fun f : L => (φ fun _ => f) ^ k) = ⊤`. Assume the negation of the conclusion as `h`. Take `⟨p, hp, hle⟩` from `Ideal.exists_le_maximal _ h`. Take `⟨f, hf⟩` from `hφ p hp.isPrime`. Conclude with `hf (hp.isPrime.mem_of_pow_mem _ (hle (Ideal.subset_span ⟨f, rfl⟩)))`.

Express the relevant statement in the definitionally equal form `(1 : B) ∈ Ideal.span _`. Rewrite using `[this]`. Conclude with `Submodule.mem_top`.
-/
theorem one_mem_span_pow (hφ : ∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) (k : ℕ) :
    (1 : B) ∈ Submodule.span B (Set.range fun f : L => (φ fun _ => f) ^ k) := by
  have : Ideal.span (Set.range fun f : L => (φ fun _ => f) ^ k) = ⊤ := by
    by_contra h
    obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf⟩ := hφ p hp.isPrime
    exact hf (hp.isPrime.mem_of_pow_mem _ (hle (Ideal.subset_span ⟨f, rfl⟩)))
  change (1 : B) ∈ Ideal.span _
  rw [this]; exact Submodule.mem_top

/- English proof (translation)
Establish `key : ∀ f a b : L, ((φ fun _ => f) ^ 2) • (gen φ a ⊗ₜ[B] gen φ b : Alg φ ⊗[B] Alg φ) = (φ (Fin.cons a (fun _ => f) : Fin (n + 1) → L) * φ (Fin.cons b (fun _ => f) : Fin (n + 1) → L)) • (gen φ f ⊗ₜ[B] gen φ f)`. Introduce `f a b`. Rewrite using `[pow_two, ← TensorProduct.smul_tmul_smul, smul_gen φ a f, smul_gen φ b f, TensorProduct.smul_tmul_smul]`. Take `⟨c, hc⟩` from `Finsupp.mem_span_range_iff_exists_finsupp.1 (one_mem_span_pow φ hφ 2)`. Rewrite using `[← sub_eq_zero, ← one_smul B (_ - _), ← hc, Finsupp.sum, Finset.sum_smul]`.

Use `Finset.sum_eq_zero fun f _ => ?_` and prove the remaining obligations. Rewrite using `[smul_assoc, smul_sub, key, key, mul_comm (φ _), sub_self, smul_zero]`.
-/
theorem swap (hφ : ∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) (e ℓ : L) :
    (gen φ e ⊗ₜ[B] gen φ ℓ : Alg φ ⊗[B] Alg φ) = gen φ ℓ ⊗ₜ gen φ e := by
  have key : ∀ f a b : L, ((φ fun _ => f) ^ 2) • (gen φ a ⊗ₜ[B] gen φ b : Alg φ ⊗[B] Alg φ) =
      (φ (Fin.cons a (fun _ => f) : Fin (n + 1) → L) *
        φ (Fin.cons b (fun _ => f) : Fin (n + 1) → L)) • (gen φ f ⊗ₜ[B] gen φ f) := by
    intro f a b
    rw [pow_two, ← TensorProduct.smul_tmul_smul, smul_gen φ a f, smul_gen φ b f,
      TensorProduct.smul_tmul_smul]
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (one_mem_span_pow φ hφ 2)
  rw [← sub_eq_zero, ← one_smul B (_ - _), ← hc, Finsupp.sum, Finset.sum_smul]
  refine Finset.sum_eq_zero fun f _ => ?_
  rw [smul_assoc, smul_sub, key, key, mul_comm (φ _), sub_self, smul_zero]

/- English proof (translation)
Rewrite using `[Algebra.algebraMap_eq_smul_one r, Algebra.algebraMap_eq_smul_one r, TensorProduct.tmul_smul, Algebra.TensorProduct.one_def]`.
-/
theorem one_tmul_algebraMap (r : B) :
    (1 : Alg φ) ⊗ₜ[B] algebraMap B (Alg φ) r = algebraMap B (Alg φ ⊗[B] Alg φ) r := by
  rw [Algebra.algebraMap_eq_smul_one r, Algebra.algebraMap_eq_smul_one r, TensorProduct.tmul_smul,
    Algebra.TensorProduct.one_def]

/- English proof (translation)
Rewrite using `[Algebra.algebraMap_eq_smul_one r, Algebra.algebraMap_eq_smul_one r, ← TensorProduct.smul_tmul', Algebra.TensorProduct.one_def]`.
-/
theorem algebraMap_tmul_one (r : B) :
    algebraMap B (Alg φ) r ⊗ₜ[B] (1 : Alg φ) = algebraMap B (Alg φ ⊗[B] Alg φ) r := by
  rw [Algebra.algebraMap_eq_smul_one r, Algebra.algebraMap_eq_smul_one r,
    ← TensorProduct.smul_tmul', Algebra.TensorProduct.one_def]

def T (c : L →₀ B) (j : ℕ) : Alg φ ⊗[B] Alg φ :=
  c.sum fun f a => a • ((gen φ f ^ (n + 1 - j)) ⊗ₜ[B] (gen φ f ^ j))

/- English proof (translation)
Rewrite using `[← map_one (algebraMap B (Alg φ ⊗[B] Alg φ)), ← hc, map_finsuppSum, T]`. Use `Finsupp.sum_congr fun f _ => ?_` and prove the remaining obligations. Rewrite using `[Nat.sub_zero, pow_zero, gen_pow, algebraMap_tmul_one, smul_eq_mul, map_mul, Algebra.smul_def]`.
-/
theorem T_zero (c : L →₀ B) (hc : (c.sum fun f a => a • φ fun _ => f) = 1) : T φ c 0 = 1 := by
  rw [← map_one (algebraMap B (Alg φ ⊗[B] Alg φ)), ← hc, map_finsuppSum, T]
  refine Finsupp.sum_congr fun f _ => ?_
  rw [Nat.sub_zero, pow_zero, gen_pow, algebraMap_tmul_one, smul_eq_mul, map_mul, Algebra.smul_def]

/- English proof (translation)
Rewrite using `[← map_one (algebraMap B (Alg φ ⊗[B] Alg φ)), ← hc, map_finsuppSum, T]`. Use `Finsupp.sum_congr fun f _ => ?_` and prove the remaining obligations. Rewrite using `[Nat.sub_self, pow_zero, gen_pow, one_tmul_algebraMap, smul_eq_mul, map_mul, Algebra.smul_def]`.
-/
theorem T_top (c : L →₀ B) (hc : (c.sum fun f a => a • φ fun _ => f) = 1) : T φ c (n + 1) = 1 := by
  rw [← map_one (algebraMap B (Alg φ ⊗[B] Alg φ)), ← hc, map_finsuppSum, T]
  refine Finsupp.sum_congr fun f _ => ?_
  rw [Nat.sub_self, pow_zero, gen_pow, one_tmul_algebraMap, smul_eq_mul, map_mul, Algebra.smul_def]

end

section
variable {B : Type} [CommRing B] {L : Type} [AddCommGroup L] [Module B L] {n : ℕ}
  (φ : MultilinearMap B (fun _ : Fin (n + 1) => L) B)

/- English proof (translation)
Simplify using `only [T, Finsupp.sum, Finset.sum_mul, smul_mul_assoc]`. Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Use `congr 1`. Establish `h1 : n + 1 - j = (n - j) + 1` using `by omega`. Establish `h2 : n + 1 - (j + 1) = n - j` using `by omega`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, pow_succ, mul_one]`. Use `_ = ((gen φ f ^ (n - j)) ⊗ₜ[B] (gen φ f ^ j)) * (gen φ ℓ ⊗ₜ[B] gen φ f) := by rw [hsw]`. Use `_ = _ := by`. Rewrite using `[h2, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, pow_succ, mul_one]`.
-/
theorem T_shift
    (hsw : ∀ e ℓ : L, (gen φ e ⊗ₜ[B] gen φ ℓ : Alg φ ⊗[B] Alg φ) = gen φ ℓ ⊗ₜ gen φ e)
    (c : L →₀ B) (ℓ : L) (j : ℕ) (hj : j ≤ n) :
    T φ c j * ((1 : Alg φ) ⊗ₜ[B] gen φ ℓ) = T φ c (j + 1) * (gen φ ℓ ⊗ₜ[B] (1 : Alg φ)) := by
  simp only [T, Finsupp.sum, Finset.sum_mul, smul_mul_assoc]
  refine Finset.sum_congr rfl fun f _ => ?_
  congr 1
  have h1 : n + 1 - j = (n - j) + 1 := by omega
  have h2 : n + 1 - (j + 1) = n - j := by omega
  calc (gen φ f ^ (n + 1 - j)) ⊗ₜ[B] (gen φ f ^ j) * ((1 : Alg φ) ⊗ₜ[B] gen φ ℓ)
      = ((gen φ f ^ (n - j)) ⊗ₜ[B] (gen φ f ^ j)) * (gen φ f ⊗ₜ[B] gen φ ℓ) := by
        rw [h1, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          pow_succ, mul_one]
    _ = ((gen φ f ^ (n - j)) ⊗ₜ[B] (gen φ f ^ j)) * (gen φ ℓ ⊗ₜ[B] gen φ f) := by rw [hsw]
    _ = _ := by
        rw [h2, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          pow_succ, mul_one]

def ev (ζ : B) (hζ : ζ ^ (n + 1) = 1) (g : Multiplicative (ZMod (n + 1))) :
    Alg φ ⊗[B] Alg φ →ₐ[B] Alg φ :=
  Algebra.TensorProduct.productMap (AlgHom.id B (Alg φ)) (act φ ζ hζ g).toAlgHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ev_tmul (ζ : B) (hζ : ζ ^ (n + 1) = 1) (g : Multiplicative (ZMod (n + 1))) (a b : Alg φ) :
    ev φ ζ hζ g (a ⊗ₜ b) = a * act φ ζ hζ g b := rfl

/- English proof (translation)
The claim follows from `act_gen φ ζ hζ g.toAdd f`.
-/
theorem act_gen' (ζ : B) (hζ : ζ ^ (n + 1) = 1) (g : Multiplicative (ZMod (n + 1))) (f : L) :
    act φ ζ hζ g (gen φ f) = tw ζ g.toAdd • gen φ f :=
  act_gen φ ζ hζ g.toAdd f

/- English proof (translation)
Rewrite using `[T, map_finsuppSum]`. Combine the equalities or inequalities in the displayed calculation. Use `Finsupp.sum_congr fun f _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, ev_tmul, map_pow, act_gen', smul_pow, mul_smul_comm, ← pow_add, Nat.sub_add_cancel hj, gen_pow, smul_eq_mul, map_mul, map_mul, Algebra.smul_def, Algebra.smul_def, mul_left_comm]`. Use `_ = algebraMap B (Alg φ) (tw ζ g.toAdd ^ j * c.sum fun f a => a • φ fun _ => f) := by`.

Rewrite using `[Finsupp.mul_sum, map_finsuppSum]`. Use `_ = _ := by rw [hc, mul_one]`.
-/
theorem kummerTensorEvalAction_powerRatio (c : L →₀ B) (hc : (c.sum fun f a => a • φ fun _ => f) = 1)
    (ζ : B) (hζ : ζ ^ (n + 1) = 1) (g : Multiplicative (ZMod (n + 1))) (j : ℕ) (hj : j ≤ n + 1) :
    ev φ ζ hζ g (T φ c j) = algebraMap B (Alg φ) (tw ζ g.toAdd ^ j) := by
  rw [T, map_finsuppSum]
  calc (c.sum fun f a => ev φ ζ hζ g (a • ((gen φ f ^ (n + 1 - j)) ⊗ₜ[B] (gen φ f ^ j))))
      = c.sum (fun f a => algebraMap B (Alg φ) (tw ζ g.toAdd ^ j * (a • φ fun _ => f))) := by
        refine Finsupp.sum_congr fun f _ => ?_
        rw [map_smul, ev_tmul, map_pow, act_gen', smul_pow, mul_smul_comm, ← pow_add,
          Nat.sub_add_cancel hj, gen_pow, smul_eq_mul, map_mul, map_mul, Algebra.smul_def,
          Algebra.smul_def, mul_left_comm]
    _ = algebraMap B (Alg φ) (tw ζ g.toAdd ^ j * c.sum fun f a => a • φ fun _ => f) := by
        rw [Finsupp.mul_sum, map_finsuppSum]
    _ = _ := by rw [hc, mul_one]

/- English proof (translation)
Establish `h` using `geom_sum_mul z (n + 1)`. Rewrite `h` using `[hz, sub_self]`. Establish `hu' : IsUnit (z - 1)` using `by rw [← neg_sub]; exact hu.neg`. Conclude with `hu'.mul_left_eq_zero.1 h`.
-/
theorem geom_zero (z : B) (hz : z ^ (n + 1) = 1) (hu : IsUnit (1 - z)) :
    ∑ i ∈ Finset.range (n + 1), z ^ i = 0 := by
  have h := geom_sum_mul z (n + 1)
  rw [hz, sub_self] at h
  have hu' : IsUnit (z - 1) := by rw [← neg_sub]; exact hu.neg
  exact hu'.mul_left_eq_zero.1 h

/- English proof (translation)
Rewrite using `[Finset.sum_range_succ, Finset.sum_range_succ' (fun j => (w ^ j * v) • A j), hA]`. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[pow_succ, mul_assoc, hvw, mul_one]`. Rewrite using `[pow_zero, one_mul]`.

Use `congr 1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem shift_sum {M : Type} [AddCommGroup M] [Module B M] (v w : B) (hvw : w * v = 1)
    (hw : w ^ (n + 1) = 1) (A : ℕ → M) (hA : A (n + 1) = A 0) :
    ∑ j ∈ Finset.range (n + 1), w ^ j • A (j + 1) =
      ∑ j ∈ Finset.range (n + 1), (w ^ j * v) • A j := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun j => (w ^ j * v) • A j), hA]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ, mul_assoc, hvw, mul_one]
  · rw [pow_zero, one_mul]
    congr 1
    calc w ^ n = w ^ n * (w * v) := by rw [hvw, mul_one]
      _ = w ^ (n + 1) * v := by ring
      _ = v := by rw [hw, one_mul]

def E (c : L →₀ B) (s w : B) : Alg φ ⊗[B] Alg φ :=
  s • ∑ j ∈ Finset.range (n + 1), w ^ j • T φ c j

/- English proof (translation)
Establish `hm : ∀ a d : Alg φ, (a * d) ⊗ₜ[B] (1 : Alg φ) = (a ⊗ₜ[B] (1 : Alg φ)) * (d ⊗ₜ[B] 1)`. Introduce `a d`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one]`. Establish `h1 : ∀ a d : Alg φ, (1 : Alg φ) ⊗ₜ[B] (a * d) = ((1 : Alg φ) ⊗ₜ[B] a) * (1 ⊗ₜ[B] d)`. Introduce `a d`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one]`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Proceed by induction on `p using MvPolynomial.induction_on`. Use `next r =>`. Rewrite using `[← algebraMap_eq_mk, AlgEquiv.commutes, one_tmul_algebraMap, algebraMap_tmul_one]`.

Use `next p p' hp hp' =>`. Rewrite using `[map_add, map_add, TensorProduct.tmul_add, TensorProduct.add_tmul, mul_add, mul_add, hp, hp']`. Use `next p ℓ hp =>`. Establish `: Ideal.Quotient.mk (ideal φ) (p * MvPolynomial.X ℓ) = Ideal.Quotient.mk (ideal φ) p * gen φ ℓ` using `by rw [map_mul]; rfl`. Rewrite using `[this, map_mul, hm, h1]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem ext_gen (ζ : B) (hζ : ζ ^ (n + 1) = 1) (g : Multiplicative (ZMod (n + 1)))
    (X : Alg φ ⊗[B] Alg φ)
    (hX : ∀ ℓ, X * ((1 : Alg φ) ⊗ₜ[B] gen φ ℓ) = X * (act φ ζ hζ g (gen φ ℓ) ⊗ₜ[B] (1 : Alg φ)))
    (b : Alg φ) : X * ((1 : Alg φ) ⊗ₜ[B] b) = X * (act φ ζ hζ g b ⊗ₜ[B] (1 : Alg φ)) := by
  have hm : ∀ a d : Alg φ, (a * d) ⊗ₜ[B] (1 : Alg φ) = (a ⊗ₜ[B] (1 : Alg φ)) * (d ⊗ₜ[B] 1) := by
    intro a d; rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have h1 : ∀ a d : Alg φ, (1 : Alg φ) ⊗ₜ[B] (a * d) = ((1 : Alg φ) ⊗ₜ[B] a) * (1 ⊗ₜ[B] d) := by
    intro a d; rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction p using MvPolynomial.induction_on
  next r =>
    rw [← algebraMap_eq_mk, AlgEquiv.commutes, one_tmul_algebraMap, algebraMap_tmul_one]
  next p p' hp hp' =>
    rw [map_add, map_add, TensorProduct.tmul_add, TensorProduct.add_tmul, mul_add, mul_add, hp, hp']
  next p ℓ hp =>
    have : Ideal.Quotient.mk (ideal φ) (p * MvPolynomial.X ℓ) =
        Ideal.Quotient.mk (ideal φ) p * gen φ ℓ := by rw [map_mul]; rfl
    rw [this, map_mul, hm, h1]
    calc X * (((1 : Alg φ) ⊗ₜ[B] Ideal.Quotient.mk (ideal φ) p) * (1 ⊗ₜ[B] gen φ ℓ))
        = (X * ((1 : Alg φ) ⊗ₜ[B] Ideal.Quotient.mk (ideal φ) p)) * (1 ⊗ₜ[B] gen φ ℓ) :=
          (mul_assoc _ _ _).symm
      _ = (X * (act φ ζ hζ g (Ideal.Quotient.mk (ideal φ) p) ⊗ₜ[B] (1 : Alg φ))) *
            (1 ⊗ₜ[B] gen φ ℓ) := by rw [hp]
      _ = (act φ ζ hζ g (Ideal.Quotient.mk (ideal φ) p) ⊗ₜ[B] (1 : Alg φ)) *
            (X * (1 ⊗ₜ[B] gen φ ℓ)) := by ring
      _ = (act φ ζ hζ g (Ideal.Quotient.mk (ideal φ) p) ⊗ₜ[B] (1 : Alg φ)) *
            (X * (act φ ζ hζ g (gen φ ℓ) ⊗ₜ[B] (1 : Alg φ))) := by rw [hX]
      _ = _ := by ring

end

section
variable {B : Type} [CommRing B] {L : Type} [AddCommGroup L] [Module B L] {n : ℕ}
  (φ : MultilinearMap B (fun _ : Fin (n + 1) => L) B)

/- English proof (translation)
Rewrite using `[← tw_add hζ, sub_eq_neg_add]`.
-/
theorem tw_neg_mul (ζ : B) (hζ : ζ ^ (n + 1) = 1) (g h : ZMod (n + 1)) :
    tw ζ (-h) * tw ζ g = tw ζ (g - h) := by
  rw [← tw_add hζ, sub_eq_neg_add]

/- English proof (translation)
Establish `hvw : tw ζ (-g.toAdd) * tw ζ g.toAdd = 1`. Rewrite using `[tw_neg_mul ζ hζ, sub_self, tw_zero]`. Rewrite using `[act_gen', ← TensorProduct.smul_tmul', E, smul_mul_assoc, smul_mul_assoc, mul_smul_comm]`. Use `congr 1`. Rewrite using `[Finset.sum_mul, Finset.sum_mul, Finset.smul_sum]`.

Establish `h1 : ∀ j ∈ Finset.range (n + 1), (tw ζ (-g.toAdd) ^ j • T φ c j) * ((1 : Alg φ) ⊗ₜ[B] gen φ ℓ) = tw ζ (-g.toAdd) ^ j • (T φ c (j + 1) * (gen φ ℓ ⊗ₜ[B] (1 : Alg φ)))`. Introduce `j hj`. Rewrite using `[smul_mul_assoc, T_shift φ hsw c ℓ j (by simp at hj; omega)]`. Rewrite using `[Finset.sum_congr rfl h1, shift_sum (tw ζ g.toAdd) (tw ζ (-g.toAdd)) hvw (tw_pow hζ _) (fun j => T φ c j * (gen φ ℓ ⊗ₜ[B] (1 : Alg φ))) (by simp only [T_top φ c hc, T_zero φ c hc])]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_mul_assoc, smul_smul, mul_comm]`.
-/
theorem E_gen
    (hsw : ∀ e ℓ : L, (gen φ e ⊗ₜ[B] gen φ ℓ : Alg φ ⊗[B] Alg φ) = gen φ ℓ ⊗ₜ gen φ e)
    (c : L →₀ B) (hc : (c.sum fun f a => a • φ fun _ => f) = 1) (s : B)
    (ζ : B) (hζ : ζ ^ (n + 1) = 1) (g : Multiplicative (ZMod (n + 1))) (ℓ : L) :
    E φ c s (tw ζ (-g.toAdd)) * ((1 : Alg φ) ⊗ₜ[B] gen φ ℓ) =
      E φ c s (tw ζ (-g.toAdd)) * (act φ ζ hζ g (gen φ ℓ) ⊗ₜ[B] (1 : Alg φ)) := by
  have hvw : tw ζ (-g.toAdd) * tw ζ g.toAdd = 1 := by
    rw [tw_neg_mul ζ hζ, sub_self, tw_zero]
  rw [act_gen', ← TensorProduct.smul_tmul', E, smul_mul_assoc, smul_mul_assoc, mul_smul_comm]
  congr 1
  rw [Finset.sum_mul, Finset.sum_mul, Finset.smul_sum]
  have h1 : ∀ j ∈ Finset.range (n + 1), (tw ζ (-g.toAdd) ^ j • T φ c j) * ((1 : Alg φ) ⊗ₜ[B] gen φ ℓ)
      = tw ζ (-g.toAdd) ^ j • (T φ c (j + 1) * (gen φ ℓ ⊗ₜ[B] (1 : Alg φ))) := by
    intro j hj
    rw [smul_mul_assoc, T_shift φ hsw c ℓ j (by simp at hj; omega)]
  rw [Finset.sum_congr rfl h1, shift_sum (tw ζ g.toAdd) (tw ζ (-g.toAdd)) hvw (tw_pow hζ _)
    (fun j => T φ c j * (gen φ ℓ ⊗ₜ[B] (1 : Alg φ))) (by simp only [T_top φ c hc, T_zero φ c hc])]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_assoc, smul_smul, mul_comm]

/- English proof (translation)
Rewrite using `[Fintype.sum_equiv (Multiplicative.toAdd.trans (Equiv.neg (ZMod (n + 1)))) (fun h => tw ζ (-h.toAdd) ^ j) (fun k => (ζ ^ j) ^ k.val) (fun h => by`. Simplify using `only [Equiv.trans_apply, Equiv.neg_apply, tw, ← pow_mul, mul_comm])]`. Establish `: ∑ k : ZMod (n + 1), (ζ ^ j) ^ k.val = ∑ i ∈ Finset.range (n + 1), (ζ ^ j) ^ i`. Rewrite using `[Finset.sum_range]`. Both sides reduce to the same expression.

Rewrite using `[this]`. Use `split_ifs with h0`. Substitute `h0` using the available equality. Simplify using the standard rewrite rules. Use `geom_zero (ζ ^ j) ?_ (hk j (Nat.pos_of_ne_zero h0) hj)` and prove the remaining obligations.

Rewrite using `[← pow_mul, mul_comm, pow_mul, hζ, one_pow]`.
-/
theorem sum_tw_pow (ζ : B) (hζ : ζ ^ (n + 1) = 1)
    (hk : ∀ k : ℕ, 0 < k → k < n + 1 → IsUnit (1 - ζ ^ k)) (j : ℕ) (hj : j < n + 1) :
    ∑ h : Multiplicative (ZMod (n + 1)), tw ζ (-h.toAdd) ^ j = if j = 0 then ((n + 1 : ℕ) : B) else 0 := by
  rw [Fintype.sum_equiv (Multiplicative.toAdd.trans (Equiv.neg (ZMod (n + 1))))
    (fun h => tw ζ (-h.toAdd) ^ j) (fun k => (ζ ^ j) ^ k.val) (fun h => by
      simp only [Equiv.trans_apply, Equiv.neg_apply, tw, ← pow_mul, mul_comm])]
  have : ∑ k : ZMod (n + 1), (ζ ^ j) ^ k.val = ∑ i ∈ Finset.range (n + 1), (ζ ^ j) ^ i := by
    rw [Finset.sum_range]; rfl
  rw [this]
  split_ifs with h0
  · subst h0; simp
  · refine geom_zero (ζ ^ j) ?_ (hk j (Nat.pos_of_ne_zero h0) hj)
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]

/- English proof (translation)
Simplify using `only [E]`. Rewrite using `[← Finset.smul_sum, Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.sum_smul]`. Rewrite using `[Finset.sum_eq_single 0]`. Rewrite using `[sum_tw_pow ζ hζ hk 0 (Nat.succ_pos n), if_pos rfl, T_zero φ c hc, smul_smul, hs, one_smul]`.

Introduce `j hj hj0`. Rewrite using `[sum_tw_pow ζ hζ hk j (Finset.mem_range.1 hj), if_neg hj0, zero_smul]`. Introduce `h`. Conclude with `absurd (Finset.mem_range.2 (Nat.succ_pos n)) h`.
-/
theorem sum_E (c : L →₀ B) (hc : (c.sum fun f a => a • φ fun _ => f) = 1) (s : B)
    (hs : s * ((n + 1 : ℕ) : B) = 1) (ζ : B) (hζ : ζ ^ (n + 1) = 1)
    (hk : ∀ k : ℕ, 0 < k → k < n + 1 → IsUnit (1 - ζ ^ k)) :
    ∑ h : Multiplicative (ZMod (n + 1)), E φ c s (tw ζ (-h.toAdd)) = 1 := by
  simp only [E]
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  rw [Finset.sum_eq_single 0]
  · rw [sum_tw_pow ζ hζ hk 0 (Nat.succ_pos n), if_pos rfl, T_zero φ c hc, smul_smul, hs, one_smul]
  · intro j hj hj0
    rw [sum_tw_pow ζ hζ hk j (Finset.mem_range.1 hj), if_neg hj0, zero_smul]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.succ_pos n)) h

/- English proof (translation)
Establish `h1 : ev φ ζ hζ g (E φ c s (tw ζ (-h.toAdd))) = algebraMap B (Alg φ) (s * ∑ j ∈ Finset.range (n + 1), tw ζ (g.toAdd - h.toAdd) ^ j)`. Rewrite using `[E, map_smul, map_sum, Finset.mul_sum, map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[map_smul, kummerTensorEvalAction_powerRatio φ c hc ζ hζ g j (by simp at hj; omega), ← tw_neg_mul ζ hζ, mul_pow, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul]`. Rewrite using `[h1]`.

Use `split_ifs with hgh`. Substitute `hgh` using the available equality. Simplify using `only [sub_self, tw_zero, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]`. Rewrite using `[hs, map_one]`. Establish `hne : g.toAdd - h.toAdd ≠ 0`.

Introduce `h0`. Conclude with `hgh (Multiplicative.toAdd.injective (sub_eq_zero.1 h0))`. Rewrite using `[geom_zero (tw ζ (g.toAdd - h.toAdd)) (tw_pow hζ _) (hk _ ((ZMod.val_pos).2 hne) (ZMod.val_lt _)), mul_zero, map_zero]`.
-/
theorem ev_E (c : L →₀ B) (hc : (c.sum fun f a => a • φ fun _ => f) = 1) (s : B)
    (hs : s * ((n + 1 : ℕ) : B) = 1) (ζ : B) (hζ : ζ ^ (n + 1) = 1)
    (hk : ∀ k : ℕ, 0 < k → k < n + 1 → IsUnit (1 - ζ ^ k))
    (g h : Multiplicative (ZMod (n + 1))) :
    ev φ ζ hζ g (E φ c s (tw ζ (-h.toAdd))) = if g = h then 1 else 0 := by
  have h1 : ev φ ζ hζ g (E φ c s (tw ζ (-h.toAdd))) = algebraMap B (Alg φ)
      (s * ∑ j ∈ Finset.range (n + 1), tw ζ (g.toAdd - h.toAdd) ^ j) := by
    rw [E, map_smul, map_sum, Finset.mul_sum, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [map_smul, kummerTensorEvalAction_powerRatio φ c hc ζ hζ g j (by simp at hj; omega), ← tw_neg_mul ζ hζ, mul_pow,
      Algebra.smul_def, Algebra.smul_def, map_mul, map_mul]
  rw [h1]
  split_ifs with hgh
  · subst hgh
    simp only [sub_self, tw_zero, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one]
    rw [hs, map_one]
  · have hne : g.toAdd - h.toAdd ≠ 0 := by
      intro h0; exact hgh (Multiplicative.toAdd.injective (sub_eq_zero.1 h0))
    rw [geom_zero (tw ζ (g.toAdd - h.toAdd)) (tw_pow hζ _)
      (hk _ ((ZMod.val_pos).2 hne) (ZMod.val_lt _)), mul_zero, map_zero]

end

section
variable {B : Type} [CommRing B] {L : Type} [AddCommGroup L] [Module B L] {n : ℕ}
  (φ : MultilinearMap B (fun _ : Fin (n + 1) => L) B)

/- English proof (translation)
Use `set Φ := Algebra.TensorProduct.productMap (Pi.algHom B (fun _ : Multiplicative (ZMod (n + 1)) => Alg φ) (fun _ => AlgHom.id B (Alg φ))) (Pi.algHom B (fun _ : Multiplicative (ZMod (n + 1)) => Alg φ) (fun g => (act φ ζ hζ g).toAlgHom)) with hΦ`. Establish `hΦev : ∀ t g, Φ t g = ev φ ζ hζ g t`. Introduce `t g`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a b => rfl`. Consider the case `add x y hx hy => rw [map_add, map_add, Pi.add_apply, hx, hy]`. Take `⟨c, hc⟩` from `Finsupp.mem_span_range_iff_exists_finsupp.1 (one_mem_span_pow φ hφ 1)`. Simplify using `only [pow_one] at hc`. Establish `hsw` using `swap φ hφ`.

Use `set s : B := ((hq.unit⁻¹ : Bˣ) : B) with hs_def`. Establish `hs : s * ((n + 1 : ℕ) : B) = 1` using `hq.val_inv_mul`. Use `set Eh : Multiplicative (ZMod (n + 1)) → Alg φ ⊗[B] Alg φ := fun h => E φ c s (tw ζ (-h.toAdd)) with hEh`. Establish `hsum : ∑ h, Eh h = 1` using `sum_E φ c hc s hs ζ hζ hk`. Establish `hEb : ∀ h b, Eh h * ((1 : Alg φ) ⊗ₜ[B] b) = Eh h * (act φ ζ hζ h b ⊗ₜ[B] (1 : Alg φ))` using `fun h b => ext_gen φ ζ hζ h (Eh h) (E_gen φ hsw c hc s ζ hζ h) b`.

Set `ψ : (Multiplicative (ZMod (n + 1)) → Alg φ) → Alg φ ⊗[B] Alg φ` to `fun d => ∑ h, Eh h * (d h ⊗ₜ[B] (1 : Alg φ))`. Establish `hψadd : ∀ d d', ψ (d + d') = ψ d + ψ d'`. Introduce `d d'`. Simplify using `only [ψ, Pi.add_apply, TensorProduct.add_tmul, mul_add, Finset.sum_add_distrib]`. Use `Function.bijective_iff_has_inverse.2 ⟨ψ, ?_, ?_⟩` and prove the remaining obligations.

Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp [ψ]`. Consider the case `tmul a b`. Establish `hab : ∀ h, Φ (a ⊗ₜ b) h = a * act φ ζ hζ h b` using `fun h => rfl`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [ψ, hab]`. Use `_ = ∑ h, (a ⊗ₜ[B] (1 : Alg φ)) * (Eh h * (act φ ζ hζ h b ⊗ₜ[B] (1 : Alg φ))) := by`. Use `Finset.sum_congr rfl fun h _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_one (1 : Alg φ), ← Algebra.TensorProduct.tmul_mul_tmul]`.

Put the polynomial expressions in normal form. Use `_ = ∑ h, (a ⊗ₜ[B] (1 : Alg φ)) * (Eh h * ((1 : Alg φ) ⊗ₜ[B] b)) := by`. Simplify using `only [hEb]`. Use `_ = (a ⊗ₜ[B] (1 : Alg φ)) * ((1 : Alg φ) ⊗ₜ[B] b) * ∑ h, Eh h := by`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun h _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `_ = a ⊗ₜ b := by rw [hsum, mul_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Consider the case `add x y hx hy => rw [map_add, hψadd, hx, hy]`. Introduce `d`.

Use function extensionality and compare the values at `g`. Rewrite using `[hΦev]`. Simplify using `only [ψ, map_sum, map_mul, ev_tmul, map_one, mul_one, hEh, ev_E φ c hc s hs ζ hζ hk, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
theorem bijective_succ (hq : IsUnit ((n + 1 : ℕ) : B))
    (hφ : ∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) (ζ : B) (hζ : ζ ^ (n + 1) = 1)
    (hk : ∀ k : ℕ, 0 < k → k < n + 1 → IsUnit (1 - ζ ^ k)) :
    Function.Bijective (Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod (n + 1)) => Alg φ) (fun _ => AlgHom.id B (Alg φ)))
      (Pi.algHom B (fun _ : Multiplicative (ZMod (n + 1)) => Alg φ)
        (fun g => (act φ ζ hζ g).toAlgHom))) := by
  set Φ := Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod (n + 1)) => Alg φ) (fun _ => AlgHom.id B (Alg φ)))
      (Pi.algHom B (fun _ : Multiplicative (ZMod (n + 1)) => Alg φ)
        (fun g => (act φ ζ hζ g).toAlgHom)) with hΦ
  have hΦev : ∀ t g, Φ t g = ev φ ζ hζ g t := by
    intro t g
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => rw [map_add, map_add, Pi.add_apply, hx, hy]
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (one_mem_span_pow φ hφ 1)
  simp only [pow_one] at hc
  have hsw := swap φ hφ
  set s : B := ((hq.unit⁻¹ : Bˣ) : B) with hs_def
  have hs : s * ((n + 1 : ℕ) : B) = 1 := hq.val_inv_mul
  set Eh : Multiplicative (ZMod (n + 1)) → Alg φ ⊗[B] Alg φ :=
    fun h => E φ c s (tw ζ (-h.toAdd)) with hEh
  have hsum : ∑ h, Eh h = 1 := sum_E φ c hc s hs ζ hζ hk
  have hEb : ∀ h b, Eh h * ((1 : Alg φ) ⊗ₜ[B] b) = Eh h * (act φ ζ hζ h b ⊗ₜ[B] (1 : Alg φ)) :=
    fun h b => ext_gen φ ζ hζ h (Eh h) (E_gen φ hsw c hc s ζ hζ h) b
  let ψ : (Multiplicative (ZMod (n + 1)) → Alg φ) → Alg φ ⊗[B] Alg φ :=
    fun d => ∑ h, Eh h * (d h ⊗ₜ[B] (1 : Alg φ))
  have hψadd : ∀ d d', ψ (d + d') = ψ d + ψ d' := by
    intro d d'
    simp only [ψ, Pi.add_apply, TensorProduct.add_tmul, mul_add, Finset.sum_add_distrib]
  refine Function.bijective_iff_has_inverse.2 ⟨ψ, ?_, ?_⟩
  · intro t
    induction t using TensorProduct.induction_on with
    | zero => simp [ψ]
    | tmul a b =>
      have hab : ∀ h, Φ (a ⊗ₜ b) h = a * act φ ζ hζ h b := fun h => rfl
      calc ψ (Φ (a ⊗ₜ b)) = ∑ h, Eh h * ((a * act φ ζ hζ h b) ⊗ₜ[B] (1 : Alg φ)) := by
            simp only [ψ, hab]
        _ = ∑ h, (a ⊗ₜ[B] (1 : Alg φ)) * (Eh h * (act φ ζ hζ h b ⊗ₜ[B] (1 : Alg φ))) := by
            refine Finset.sum_congr rfl fun h _ => ?_
            rw [← mul_one (1 : Alg φ), ← Algebra.TensorProduct.tmul_mul_tmul]; ring_nf
        _ = ∑ h, (a ⊗ₜ[B] (1 : Alg φ)) * (Eh h * ((1 : Alg φ) ⊗ₜ[B] b)) := by
            simp only [hEb]
        _ = (a ⊗ₜ[B] (1 : Alg φ)) * ((1 : Alg φ) ⊗ₜ[B] b) * ∑ h, Eh h := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun h _ => ?_; ring
        _ = a ⊗ₜ b := by rw [hsum, mul_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => rw [map_add, hψadd, hx, hy]
  · intro d
    funext g
    rw [hΦev]
    simp only [ψ, map_sum, map_mul, ev_tmul, map_one, mul_one, hEh,
      ev_E φ c hc s hs ζ hζ hk, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]

end

/- English proof (translation)
Introduce `B _ L _ _ _ q _ φ hq hφ ζ hζ hk`. Take `⟨n, rfl⟩ : ∃ n, q = n + 1` from `⟨q - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos q)).symm⟩`. Conclude with `bijective_succ φ hq hφ ζ hζ hk`.
-/
theorem bijective : ∀ (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L]
    [Module.Invertible B L] (q : ℕ) [NeZero q] (φ : MultilinearMap B (fun _ : Fin q => L) B),
    IsUnit (q : B) → (∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) →
    ∀ (ζ : B) (hζ : ζ ^ q = 1), (∀ k : ℕ, 0 < k → k < q → IsUnit (1 - ζ ^ k)) →
    Function.Bijective (Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => GlobalTheory.KummerAlg.Alg φ)
        (fun _ => AlgHom.id B (GlobalTheory.KummerAlg.Alg φ)))
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => GlobalTheory.KummerAlg.Alg φ)
        (fun g => (GlobalTheory.KummerAlg.act φ ζ hζ g).toAlgHom))) := by
  intro B _ L _ _ _ q _ φ hq hφ ζ hζ hk
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos q)).symm⟩
  exact bijective_succ φ hq hφ ζ hζ hk

end GlobalTheory.KummerTorsor
