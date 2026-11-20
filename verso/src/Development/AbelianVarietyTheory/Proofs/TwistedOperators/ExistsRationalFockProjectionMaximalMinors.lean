import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
open Classical MeasureTheory

noncomputable section

open MvPolynomial

namespace GlobalTheory.MinorFrame.RatProj

section Form

variable {σ : Type}

def fockQ (f g : MvPolynomial σ ℚ) : ℚ :=
  ∑ m ∈ f.support, f.coeff m * g.coeff m * (Formalism.L2.DIV.mfact m : ℚ)

/- English proof (translation)
Use `Finset.sum_subset hs ?_` and prove the remaining obligations. Introduce `m _ hm`. Rewrite using `[notMem_support_iff.mp hm]`. Simplify using the standard rewrite rules.
-/
theorem fockQ_eq_sum (f g : MvPolynomial σ ℚ) (s : Finset (σ →₀ ℕ)) (hs : f.support ⊆ s) :
    fockQ f g = ∑ m ∈ s, f.coeff m * g.coeff m * (Formalism.L2.DIV.mfact m : ℚ) := by
  refine Finset.sum_subset hs ?_
  intro m _ hm
  rw [notMem_support_iff.mp hm]
  simp

def fockQL : MvPolynomial σ ℚ →ₗ[ℚ] MvPolynomial σ ℚ →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ fockQ
    (by
      intro f f' g
      rw [fockQ_eq_sum (f + f') g (f.support ∪ f'.support) support_add,
        fockQ_eq_sum f g (f.support ∪ f'.support) Finset.subset_union_left,
        fockQ_eq_sum f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [coeff_add]; ring)
    (by
      intro c f g
      rw [fockQ_eq_sum (c • f) g f.support support_smul, fockQ, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [coeff_smul, smul_eq_mul]; ring)
    (by
      intro f g g'
      simp only [fockQ, coeff_add, mul_add, add_mul, Finset.sum_add_distrib])
    (by
      intro c f g
      simp only [fockQ, coeff_smul, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fockQL_apply (f g : MvPolynomial σ ℚ) : fockQL f g = fockQ f g := rfl

/- English proof (translation)
Rewrite using `[Formalism.L2.DIV.fockS_eq_sum _ _ f.support (support_map_subset _ _), fockQ]`. Use `push_cast`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `[coeff_map]`.
-/
theorem fockS_map (f g : MvPolynomial σ ℚ) :
    Formalism.L2.DIV.fockS (map (algebraMap ℚ ℂ) f) (map (algebraMap ℚ ℂ) g) = (fockQ f g : ℂ) := by
  rw [Formalism.L2.DIV.fockS_eq_sum _ _ f.support (support_map_subset _ _), fockQ]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [coeff_map]

/- English proof (translation)
Assume the negation of the conclusion as `hf`. Establish `hf' : map (algebraMap ℚ ℂ) f ≠ 0`. Introduce `h0`. Apply `hf` to reduce the goal to its premises. Conclude with `map_injective _ (algebraMap ℚ ℂ).injective (by rw [h0, map_zero])`.

Use `GlobalTheory.MinorFrame.fockS_self_re_pos hf'` as an intermediate fact. Rewrite `this` using `[fockS_map, h]`. Simplify using `at this`.
-/
theorem eq_zero_of_fockQ_self {f : MvPolynomial σ ℚ} (h : fockQ f f = 0) : f = 0 := by
  by_contra hf
  have hf' : map (algebraMap ℚ ℂ) f ≠ 0 := by
    intro h0
    apply hf
    exact map_injective _ (algebraMap ℚ ℂ).injective (by rw [h0, map_zero])
  have := GlobalTheory.MinorFrame.fockS_self_re_pos hf'
  rw [fockS_map, h] at this
  simp at this

end Form

variable {ι : Type} [Fintype ι]

def prodMinorsQ {a d : ℕ} {n : ι → ℕ} (T : Tup ι a d n) : MvPolynomial (Var ι d a) ℚ :=
  ∏ τ, ∏ j, (Matrix.of fun i i' : Fin a => (X (τ, (T τ j).1 i, i') : MvPolynomial (Var ι d a) ℚ)).det

/- English proof (translation)
Simplify using `only [prodMinorsQ, prodMinors, minorAt, map_prod]`. Use `Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `i i'`.

Simplify using the standard rewrite rules.
-/
theorem map_prodMinorsQ {a d : ℕ} {n : ι → ℕ} (T : Tup ι a d n) :
    map (algebraMap ℚ ℂ) (prodMinorsQ T) = prodMinors T := by
  simp only [prodMinorsQ, prodMinors, minorAt, map_prod]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun j _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext i i'
  simp

/- English proof (translation)
Introduce `ι _ a d n k`. Set `PQ : Tup ι a d n → MvPolynomial (Var ι d a) ℚ` to `fun T => prodMinorsQ T`. Set `W` to `Submodule.span ℚ (Set.range PQ)`. Use `haveI : FiniteDimensional ℚ W := FiniteDimensional.span_of_finite ℚ (Set.finite_range PQ)`. Set `ψ : W →ₗ[ℚ] Module.Dual ℚ W` to `(fockQL (σ := Var ι d a)).flip.compl₁₂ W.subtype W.subtype`.

Establish `hinj : Function.Injective ψ`. Rewrite using `[← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]`. Introduce `w hw`. Establish `h1 : ψ w w = 0` using `by rw [LinearMap.mem_ker.mp hw]; rfl`. Establish `h2 : fockQ (w : MvPolynomial (Var ι d a) ℚ) w = 0` using `h1`.

Conclude with `Subtype.ext (eq_zero_of_fockQ_self h2)`. Establish `hsurj : Function.Surjective ψ` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hinj`. Take `⟨w₀, hw₀⟩` from `hsurj ((fockQL.flip (monomial k (1 : ℚ))).comp W.subtype)`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℚ).1 w₀.2`. Set `e : Fin (Fintype.card (Tup ι a d n)) ≃ Tup ι a d n` to `(Fintype.equivFin _).symm`.

Use `⟨Fintype.card (Tup ι a d n), fun p => c (e p), fun p => e p, fun T => ?_⟩` and prove the remaining obligations. Establish `hsum : (∑ p, ((c (e p) : ℚ) : ℂ) • prodMinors (e p)) = map (algebraMap ℚ ℂ) (w₀ : MvPolynomial (Var ι d a) ℚ)`. Rewrite using `[e.sum_comp (fun T => ((c T : ℚ) : ℂ) • prodMinors T), ← hc, map_sum]`. Use `Finset.sum_congr rfl fun T _ => ?_` and prove the remaining obligations. Simplify using `only [PQ]`.

Rewrite using `[smul_eq_C_mul (prodMinorsQ T) (c T), map_mul, map_C, map_prodMinorsQ, smul_eq_C_mul]`. Simplify using the standard rewrite rules. Establish `hmon : (monomial k (1 : ℂ)) = map (algebraMap ℚ ℂ) (monomial k (1 : ℚ))` using `by simp [map_monomial]`. Rewrite using `[hsum, ← map_prodMinorsQ T, hmon, ← map_sub, fockS_map, ← fockQL_apply, map_sub]`. Establish `h3` using `LinearMap.congr_fun hw₀ ⟨PQ T, Submodule.subset_span ⟨T, rfl⟩⟩`.

Establish `h4 : fockQL (PQ T) (w₀ : MvPolynomial (Var ι d a) ℚ) = fockQL (PQ T) (monomial k 1)` using `h3`. Simplify using `only [PQ] at h4`. Rewrite using `[h4, sub_self, Rat.cast_zero]`.
-/
theorem exists_rat_proj : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (k : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
  ∃ (M : ℕ) (r : Fin M → ℚ) (U : Fin M → GlobalTheory.MinorFrame.Tup ι a d n), ∀ T : GlobalTheory.MinorFrame.Tup ι a d n,
    Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.prodMinors T)
      (MvPolynomial.monomial k 1 - ∑ p, ((r p : ℚ) : ℂ) • GlobalTheory.MinorFrame.prodMinors (U p)) = 0 := by
  intro ι _ a d n k
  let PQ : Tup ι a d n → MvPolynomial (Var ι d a) ℚ := fun T => prodMinorsQ T
  let W := Submodule.span ℚ (Set.range PQ)
  haveI : FiniteDimensional ℚ W := FiniteDimensional.span_of_finite ℚ (Set.finite_range PQ)
  let ψ : W →ₗ[ℚ] Module.Dual ℚ W := (fockQL (σ := Var ι d a)).flip.compl₁₂ W.subtype W.subtype
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    have h1 : ψ w w = 0 := by rw [LinearMap.mem_ker.mp hw]; rfl
    have h2 : fockQ (w : MvPolynomial (Var ι d a) ℚ) w = 0 := h1
    exact Subtype.ext (eq_zero_of_fockQ_self h2)
  have hsurj : Function.Surjective ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hinj
  obtain ⟨w₀, hw₀⟩ := hsurj ((fockQL.flip (monomial k (1 : ℚ))).comp W.subtype)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 w₀.2
  let e : Fin (Fintype.card (Tup ι a d n)) ≃ Tup ι a d n := (Fintype.equivFin _).symm
  refine ⟨Fintype.card (Tup ι a d n), fun p => c (e p), fun p => e p, fun T => ?_⟩
  have hsum : (∑ p, ((c (e p) : ℚ) : ℂ) • prodMinors (e p)) =
      map (algebraMap ℚ ℂ) (w₀ : MvPolynomial (Var ι d a) ℚ) := by
    rw [e.sum_comp (fun T => ((c T : ℚ) : ℂ) • prodMinors T), ← hc, map_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    simp only [PQ]
    rw [smul_eq_C_mul (prodMinorsQ T) (c T), map_mul, map_C, map_prodMinorsQ, smul_eq_C_mul]
    simp
  have hmon : (monomial k (1 : ℂ)) = map (algebraMap ℚ ℂ) (monomial k (1 : ℚ)) := by simp [map_monomial]
  rw [hsum, ← map_prodMinorsQ T, hmon, ← map_sub, fockS_map, ← fockQL_apply, map_sub]
  have h3 := LinearMap.congr_fun hw₀ ⟨PQ T, Submodule.subset_span ⟨T, rfl⟩⟩
  have h4 : fockQL (PQ T) (w₀ : MvPolynomial (Var ι d a) ℚ) = fockQL (PQ T) (monomial k 1) := h3
  simp only [PQ] at h4
  rw [h4, sub_self, Rat.cast_zero]

end GlobalTheory.MinorFrame.RatProj
