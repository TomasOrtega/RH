import Mathlib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open Polynomial

section Split

variable {K S M O ι : Type} [Field K] [CharZero K] [CommRing S] [Algebra K S] [AddCommGroup M] [Module S M]
  [CommRing O] [Fintype ι] [DecidableEq ι]

def IsEigV (ρ : O →+* Module.End S M) (χ : O →+* K) (m : M) : Prop := ∀ a, ρ a m = algebraMap K S (χ a) • m

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hm, smul_smul, pow_succ]`.
-/
theorem pow_eig (f : Module.End S M) {x : S} {m : M} (hm : f m = x • m) (n : ℕ) : (f ^ n) m = x ^ n • m := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hm, smul_smul, pow_succ]

/- English proof (translation)
Rewrite using `[aeval_eq_sum_range, aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, pow_eig f hm, smul_assoc]`.
-/
theorem aeval_eig (f : Module.End S M) {x : S} {m : M} (hm : f m = x • m) (P : ℤ[X]) :
    aeval f P m = aeval x P • m := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, pow_eig f hm, smul_assoc]

/- English proof (translation)
Rewrite using `[aeval_eq_sum_range, aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, pow_eig f hm, smul_assoc]`.
-/
theorem aevalS_eig (f : Module.End S M) {x : S} {m : M} (hm : f m = x • m) (P : S[X]) :
    aeval f P m = aeval x P • m := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, pow_eig f hm, smul_assoc]

def lagr (x : ι → K) (τ : ι) : K[X] := Lagrange.basis Finset.univ x τ

/- English proof (translation)
Unfold `lagr`. Rewrite using `[Lagrange.basis]`. Simplify using `only [Lagrange.basisDivisor, Finset.prod_mul_distrib]`. Rewrite using `[← map_prod, ← Finset.mul_prod_erase Finset.univ (fun τ' => X - C (x τ')) (Finset.mem_univ τ)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem X_sub_mul_lagr (x : ι → K) (hx : Function.Injective x) (τ : ι) :
    (X - C (x τ)) * lagr x τ = C (∏ τ' ∈ Finset.univ.erase τ, (x τ - x τ')⁻¹) * ∏ τ', (X - C (x τ')) := by
  unfold lagr
  rw [Lagrange.basis]
  simp only [Lagrange.basisDivisor, Finset.prod_mul_distrib]
  rw [← map_prod, ← Finset.mul_prod_erase Finset.univ (fun τ' => X - C (x τ')) (Finset.mem_univ τ)]
  ring

/- English proof (translation)
The claim follows from `Lagrange.sum_basis hx.injOn Finset.univ_nonempty`.
-/
theorem sum_lagr (x : ι → K) (hx : Function.Injective x) [Nonempty ι] : ∑ τ, lagr x τ = 1 :=
  Lagrange.sum_basis hx.injOn Finset.univ_nonempty

/- English proof (translation)
Unfold `lagr`. Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `Lagrange.eval_basis_self hx.injOn (Finset.mem_univ _)`. Conclude with `Lagrange.eval_basis_of_ne h (Finset.mem_univ _)`.
-/
theorem eval_lagr (x : ι → K) (hx : Function.Injective x) (τ τ' : ι) :
    (lagr x τ).eval (x τ') = if τ = τ' then 1 else 0 := by
  unfold lagr
  split_ifs with h
  · subst h; exact Lagrange.eval_basis_self hx.injOn (Finset.mem_univ _)
  · exact Lagrange.eval_basis_of_ne h (Finset.mem_univ _)

end Split

section Split2

variable {K S M O ι : Type} [Field K] [CharZero K] [CommRing S] [Algebra K S] [AddCommGroup M] [Module S M]
  [CommRing O] [Fintype ι] [DecidableEq ι] (ρ : O →+* Module.End S M) (χ : ι → O →+* K) (α : O)

def proj (τ : ι) : Module.End S M := aeval (ρ α) ((lagr (fun τ => χ τ α) τ).map (algebraMap K S))

/- English proof (translation)
Establish `h` using `sum_lagr (fun τ => χ τ α) hα`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [proj, Polynomial.map_sum, map_sum]`. Use `_ = 1 := by rw [h, Polynomial.map_one, map_one]`.
-/
theorem sum_proj [Nonempty ι] (hα : Function.Injective fun τ => χ τ α) : ∑ τ, proj ρ χ α τ = 1 := by
  have h := sum_lagr (fun τ => χ τ α) hα
  calc ∑ τ, proj ρ χ α τ
      = aeval (ρ α) ((∑ τ, lagr (fun τ => χ τ α) τ).map (algebraMap K S)) := by
        simp only [proj, Polynomial.map_sum, map_sum]
    _ = 1 := by rw [h, Polynomial.map_one, map_one]

/- English proof (translation)
Establish `hk` using `congrArg (Polynomial.map (algebraMap K S)) (X_sub_mul_lagr (fun τ => χ τ α) hα τ)`. Rewrite `hk` using `[← hfs]`. Rewrite `hk` using `[Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.map_C, Polynomial.map_map]`. Establish `hz : aeval (ρ α) (f.map ((algebraMap K S).comp (Int.castRingHom K))) = 0`. Rewrite using `[show (algebraMap K S).comp (Int.castRingHom K) = algebraMap ℤ S from RingHom.ext_int _ _, aeval_map_algebraMap]`.

Establish `e : aeval (ρ α) f = ρ (aeval α f)` using `aeval_algHom_apply ρ.toIntAlgHom α f`. Rewrite using `[e, hf, map_zero]`. Establish `h1` using `congrArg (aeval (ρ α)) hk`. Rewrite `h1` using `[map_mul, map_mul, hz, mul_zero, map_sub, aeval_X, aeval_C]`. Establish `h2` using `congrArg (fun g : Module.End S M => g m) h1`.

Simplify using `only [Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply, LinearMap.zero_apply] at h2`. Unfold `proj`. Conclude with `sub_eq_zero.mp h2`.
-/
theorem proj_eig_alpha (hα : Function.Injective fun τ => χ τ α) (f : ℤ[X]) (hf : aeval α f = 0)
    (hfs : f.map (Int.castRingHom K) = ∏ τ, (X - C (χ τ α))) (τ : ι) (m : M) :
    ρ α (proj ρ χ α τ m) = algebraMap K S (χ τ α) • proj ρ χ α τ m := by
  have hk := congrArg (Polynomial.map (algebraMap K S)) (X_sub_mul_lagr (fun τ => χ τ α) hα τ)
  rw [← hfs] at hk
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_C, Polynomial.map_map] at hk
  have hz : aeval (ρ α) (f.map ((algebraMap K S).comp (Int.castRingHom K))) = 0 := by
    rw [show (algebraMap K S).comp (Int.castRingHom K) = algebraMap ℤ S from RingHom.ext_int _ _,
      aeval_map_algebraMap]
    have e : aeval (ρ α) f = ρ (aeval α f) := aeval_algHom_apply ρ.toIntAlgHom α f
    rw [e, hf, map_zero]
  have h1 := congrArg (aeval (ρ α)) hk
  rw [map_mul, map_mul, hz, mul_zero, map_sub, aeval_X, aeval_C] at h1
  have h2 := congrArg (fun g : Module.End S M => g m) h1
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply,
    LinearMap.zero_apply] at h2
  unfold proj
  exact sub_eq_zero.mp h2

/- English proof (translation)
Introduce `a`. Take `⟨N, g, hN0, hg⟩` from `hN a`. Establish `h1` using `aeval_eig (ρ α) hm g`. Establish `hL : aeval (ρ α) g = ρ (aeval α g)` using `aeval_algHom_apply ρ.toIntAlgHom α g`. Establish `hR : aeval (algebraMap K S (χ τ α)) g = algebraMap K S (χ τ (aeval α g))` using `aeval_algHom_apply ((algebraMap K S).comp (χ τ)).toIntAlgHom α g`.

Rewrite `h1` using `[hL, hR, ← hg, map_mul, map_mul, map_intCast, map_intCast, map_mul, map_intCast, Module.End.mul_apply, mul_smul]`. Establish `hNK : (N : K) ≠ 0` using `Int.cast_ne_zero.mpr hN0`. Establish `cancel : ∀ y : M, algebraMap K S ((N : K)⁻¹) • ((N : S) • y) = y`. Introduce `y`. Rewrite using `[smul_smul, ← map_intCast (algebraMap K S) N, ← map_mul, inv_mul_cancel₀ hNK, map_one, one_smul]`.

Establish `hE : ((N : Module.End S M) (ρ a m)) = (N : S) • ρ a m`. Rewrite using `[Int.cast_smul_eq_zsmul S N (ρ a m)]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[hE]`. Rewrite using `[← cancel (ρ a m), h1, cancel]`.
-/
theorem eig_of_alpha (hN : ∀ a : O, ∃ (N : ℤ) (g : ℤ[X]), N ≠ 0 ∧ (N : O) * a = aeval α g) (τ : ι) {m : M}
    (hm : ρ α m = algebraMap K S (χ τ α) • m) : IsEigV ρ (χ τ) m := by
  intro a
  obtain ⟨N, g, hN0, hg⟩ := hN a
  have h1 := aeval_eig (ρ α) hm g
  have hL : aeval (ρ α) g = ρ (aeval α g) := aeval_algHom_apply ρ.toIntAlgHom α g
  have hR : aeval (algebraMap K S (χ τ α)) g = algebraMap K S (χ τ (aeval α g)) :=
    aeval_algHom_apply ((algebraMap K S).comp (χ τ)).toIntAlgHom α g
  rw [hL, hR, ← hg, map_mul, map_mul, map_intCast, map_intCast, map_mul, map_intCast,
    Module.End.mul_apply, mul_smul] at h1
  have hNK : (N : K) ≠ 0 := Int.cast_ne_zero.mpr hN0

  have cancel : ∀ y : M, algebraMap K S ((N : K)⁻¹) • ((N : S) • y) = y := by
    intro y
    rw [smul_smul, ← map_intCast (algebraMap K S) N, ← map_mul, inv_mul_cancel₀ hNK, map_one, one_smul]
  have hE : ((N : Module.End S M) (ρ a m)) = (N : S) • ρ a m := by
    rw [Int.cast_smul_eq_zsmul S N (ρ a m)]
    simp
  rw [hE] at h1
  rw [← cancel (ρ a m), h1, cancel]

/- English proof (translation)
Rewrite using `[map_sum]`. Establish `key : ∀ τ', proj ρ χ α τ (mm τ') = if τ = τ' then mm τ' else 0`. Introduce `τ'`. Establish `hm` using `hmm τ' α`. Unfold `proj`.

Rewrite using `[aevalS_eig (ρ α) hm, aeval_map_algebraMap, aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval, eval_lagr (fun τ => χ τ α) hα]`. Apply the tactic sequence `split_ifs <;> simp`. Simplify using `only [key, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
theorem proj_sum_eig (hα : Function.Injective fun τ => χ τ α) (mm : ι → M)
    (hmm : ∀ τ, IsEigV ρ (χ τ) (mm τ)) (τ : ι) : proj ρ χ α τ (∑ τ', mm τ') = mm τ := by
  rw [map_sum]
  have key : ∀ τ', proj ρ χ α τ (mm τ') = if τ = τ' then mm τ' else 0 := by
    intro τ'
    have hm := hmm τ' α
    unfold proj
    rw [aevalS_eig (ρ α) hm, aeval_map_algebraMap, aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval,
      eval_lagr (fun τ => χ τ α) hα]
    split_ifs <;> simp
  simp only [key, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end Split2

end ReciprocityTheory.ChartRestriction.G.PullbackSections
