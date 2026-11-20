import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy

noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock

open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GroundTheory.BlockD.FourierDecayAlt.GaugeExists (qdetPoly tmPoly evU evU_apply evU_qdetPoly natDegree_qdetPoly_le
  coeff_qdetPoly_top prod_linear sum_fin_cast)

section Poly

variable {A : Type} [Ring A] [Algebra ℂ A]

/- English proof (translation)
Use extensionality with `j`. Rewrite using `[coeff_zero]`. Use `(Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => ?_` and prove the remaining obligations. Set `R : ℂ[X]` to `∑ k ∈ range (Q.natDegree + 1), monomial k (φ (Q.coeff k))`. Establish `hR : R = 0`.

Use `Polynomial.funext fun u => ?_` and prove the remaining obligations. Establish `h1` using `congrArg φ (h u)`. Rewrite `h1` using `[evU_apply, eval₂_eq_sum_range, map_sum, map_zero]`. Rewrite using `[eval_zero, ← h1]`. Simplify using `only [R, eval_finset_sum, eval_monomial, RingHom.id_apply, ← map_pow]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]`. Establish `h2` using `congrArg (fun p => p.coeff j) hR`. Simplify using `only [R, finset_sum_coeff, coeff_monomial, coeff_zero, Finset.sum_ite_eq', mem_range] at h2`. Use `split_ifs at h2 with hj`.

Conclude with `h2`. Rewrite using `[coeff_eq_zero_of_natDegree_lt (by omega), map_zero]`.
-/
theorem poly_eq_zero_of_evU (Q : A[X]) (h : ∀ u : ℂ, evU u Q = 0) : Q = 0 := by
  ext j
  rw [coeff_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => ?_
  let R : ℂ[X] := ∑ k ∈ range (Q.natDegree + 1), monomial k (φ (Q.coeff k))
  have hR : R = 0 := by
    refine Polynomial.funext fun u => ?_
    have h1 := congrArg φ (h u)
    rw [evU_apply, eval₂_eq_sum_range, map_sum, map_zero] at h1
    rw [eval_zero, ← h1]
    simp only [R, eval_finset_sum, eval_monomial, RingHom.id_apply, ← map_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have h2 := congrArg (fun p => p.coeff j) hR
  simp only [R, finset_sum_coeff, coeff_monomial, coeff_zero, Finset.sum_ite_eq', mem_range] at h2
  split_ifs at h2 with hj
  · exact h2
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), map_zero]

/- English proof (translation)
Establish `hC : ∀ u : ℂ, evU u (C a) = a` using `fun u => by simp [evU_apply]`. Establish `hQ : P * C a - C a * P = 0` using `poly_eq_zero_of_evU _ fun u => by`. Rewrite using `[map_sub, map_mul, map_mul, hC, sub_eq_zero]`. Conclude with `h u`. Establish `h2` using `congrArg (fun p => p.coeff j) hQ`.

Simplify using `only [coeff_sub, coeff_mul_C, coeff_C_mul, coeff_zero] at h2`. Conclude with `sub_eq_zero.1 h2`.
-/
theorem commute_coeff_of_evU (P : A[X]) (a : A) (h : ∀ u : ℂ, Commute (evU u P) a) (j : ℕ) :
    Commute (P.coeff j) a := by
  have hC : ∀ u : ℂ, evU u (C a) = a := fun u => by simp [evU_apply]
  have hQ : P * C a - C a * P = 0 := poly_eq_zero_of_evU _ fun u => by
    rw [map_sub, map_mul, map_mul, hC, sub_eq_zero]
    exact h u
  have h2 := congrArg (fun p => p.coeff j) hQ
  simp only [coeff_sub, coeff_mul_C, coeff_C_mul, coeff_zero] at h2
  exact sub_eq_zero.1 h2

/- English proof (translation)
Set `f : S →+* A` to `S.val.toRingHom`. Establish `hC : ∀ a ∈ S, C a ∈ liftsRing f` using `fun a ha => by`. Rewrite using `[← lifts_iff_liftsRing]`. Conclude with `C_mem_lifts f ⟨a, ha⟩`. Establish `hX : (X : A[X]) ∈ liftsRing f`.

Rewrite using `[← lifts_iff_liftsRing]`. Conclude with `X_mem_lifts f`. Establish `hT : ∀ (k : ℕ) (a b : Fin n), tmPoly E k a b ∈ liftsRing f` using `fun k a b => by`. Unfold `tmPoly`. Use `add_mem ?_ (hC _ (hS a b))` and prove the remaining obligations.

Use `split_ifs`. Conclude with `sub_mem hX (hC _ (S.algebraMap_mem _))`. Conclude with `zero_mem _`. Establish `hP : qdetPoly E ∈ liftsRing f`. Unfold `qdetPoly`.

Use `sum_mem fun σ _ => mul_mem (hC _ (intCast_mem S _)) ?_` and prove the remaining obligations. Use `list_prod_mem fun x hx => ?_` and prove the remaining obligations. Take `⟨k, rfl⟩` from `(List.mem_ofFn' _ _).1 hx`. Conclude with `hT _ _ _`. Rewrite `hP` using `[← lifts_iff_liftsRing, lifts_iff_coeff_lifts]`.

Take `⟨y, hy⟩` from `hP j`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem coeff_qdetPoly_mem {n : ℕ} (E : Fin n → Fin n → A) (S : Subalgebra ℂ A)
    (hS : ∀ p q, E p q ∈ S) (j : ℕ) : (qdetPoly E).coeff j ∈ S := by
  let f : S →+* A := S.val.toRingHom
  have hC : ∀ a ∈ S, C a ∈ liftsRing f := fun a ha => by
    rw [← lifts_iff_liftsRing]
    exact C_mem_lifts f ⟨a, ha⟩
  have hX : (X : A[X]) ∈ liftsRing f := by
    rw [← lifts_iff_liftsRing]
    exact X_mem_lifts f
  have hT : ∀ (k : ℕ) (a b : Fin n), tmPoly E k a b ∈ liftsRing f := fun k a b => by
    unfold tmPoly
    refine add_mem ?_ (hC _ (hS a b))
    split_ifs
    · exact sub_mem hX (hC _ (S.algebraMap_mem _))
    · exact zero_mem _
  have hP : qdetPoly E ∈ liftsRing f := by
    unfold qdetPoly
    refine sum_mem fun σ _ => mul_mem (hC _ (intCast_mem S _)) ?_
    refine list_prod_mem fun x hx => ?_
    obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hx
    exact hT _ _ _
  rw [← lifts_iff_liftsRing, lifts_iff_coeff_lifts] at hP
  obtain ⟨y, hy⟩ := hP j
  rw [← hy]
  exact y.2

end Poly

/- English proof (translation)
Introduce `W _ _ M d X hgl hcomm`. Establish `hL : ∀ i a p q, Commute ((qdetPoly (X i)).coeff a) (X i p q)` using `fun i a p q => commute_coeff_of_evU _ _ (fun u => by`. Rewrite using `[evU_qdetPoly]`. Conclude with `Formalism.REAL.qDetCentral _ _ (X i) (hgl i) u p q) a`. Establish `hL2 : ∀ i j a r v, Commute ((qdetPoly (X i)).coeff a) (X j r v)`.

Introduce `i j a r v`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Conclude with `hL i a r v`. Establish `hm` using `coeff_qdetPoly_mem (X i) (Subalgebra.centralizer ℂ {X j r v}) (fun p q => by`.

Rewrite using `[Subalgebra.mem_centralizer_iff]`. Introduce and unpack `g rfl`. Conclude with `(hcomm i j hij p q r v).symm.eq) a`. Rewrite `hm` using `[Subalgebra.mem_centralizer_iff]`. Conclude with `(hm _ rfl).symm`.

Use `⟨fun i j => (qdetPoly (X i)).coeff j, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Take `⟨-, htop, -⟩` from `prod_linear (d i) fun k => X i k k - algebraMap ℂ (Module.End ℂ W) ((k : ℕ) : ℂ)`. Use `show (qdetPoly (X i)).coeff (d i) = 1`. Rewrite using `[coeff_qdetPoly_top _ _ (by omega), htop]`.

Introduce `i u`. Rewrite using `[← evU_qdetPoly (X i) u, evU_apply, eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (natDegree_qdetPoly_le (X i)))]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [RingHom.id_apply, ← map_pow]`. Rewrite using `[Algebra.smul_def]`.

Conclude with `(Algebra.commutes _ _).symm`. Introduce `i hi`. Take `⟨-, -, hsub⟩` from `prod_linear (d i) fun k => X i k k - algebraMap ℂ (Module.End ℂ W) ((k : ℕ) : ℂ)`. Use `show (qdetPoly (X i)).coeff (d i - 1) = _`. Rewrite using `[coeff_qdetPoly_top _ _ (by omega), hsub (d i - 1) (by omega), Finset.sum_sub_distrib, ← map_sum, sum_fin_cast, Algebra.algebraMap_eq_smul_one]`.

Introduce `i j a b`. Establish `hm` using `coeff_qdetPoly_mem (X j) (Subalgebra.centralizer ℂ {(qdetPoly (X i)).coeff a}) (fun p q => by`. Rewrite using `[Subalgebra.mem_centralizer_iff]`. Introduce and unpack `g rfl`. Conclude with `(hL2 i j a p q).eq) b`.

Rewrite `hm` using `[Subalgebra.mem_centralizer_iff]`. Conclude with `hm _ rfl`.
-/
theorem capelli_coef_commute : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (M : ℕ) (d : Fin M → ℕ) (X : ∀ i, Fin (d i) → Fin (d i) → Module.End ℂ W), (∀ i, GlRel (X i)) → (∀ i j, i ≠ j → ∀ p q r v, Commute (X i p q) (X j r v)) → ∃ c : Fin M → ℕ → Module.End ℂ W, (∀ i, c i (d i) = 1) ∧ (∀ i (u : ℂ), qdet (X i) u = ∑ j ∈ Finset.range (d i + 1), u ^ j • c i j) ∧ (∀ i, 1 ≤ d i → c i (d i - 1) = ∑ p, X i p p - (((d i : ℂ) * ((d i : ℂ) - 1) / 2)) • (1 : Module.End ℂ W)) ∧ ∀ i j a b, Commute (c i a) (c j b) := by
  intro W _ _ M d X hgl hcomm
  have hL : ∀ i a p q, Commute ((qdetPoly (X i)).coeff a) (X i p q) := fun i a p q =>
    commute_coeff_of_evU _ _ (fun u => by
      rw [evU_qdetPoly]
      exact Formalism.REAL.qDetCentral _ _ (X i) (hgl i) u p q) a
  have hL2 : ∀ i j a r v, Commute ((qdetPoly (X i)).coeff a) (X j r v) := by
    intro i j a r v
    by_cases hij : i = j
    · subst hij
      exact hL i a r v
    · have hm := coeff_qdetPoly_mem (X i) (Subalgebra.centralizer ℂ {X j r v}) (fun p q => by
        rw [Subalgebra.mem_centralizer_iff]
        rintro g rfl
        exact (hcomm i j hij p q r v).symm.eq) a
      rw [Subalgebra.mem_centralizer_iff] at hm
      exact (hm _ rfl).symm
  refine ⟨fun i j => (qdetPoly (X i)).coeff j, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨-, htop, -⟩ := prod_linear (d i) fun k => X i k k - algebraMap ℂ (Module.End ℂ W) ((k : ℕ) : ℂ)
    show (qdetPoly (X i)).coeff (d i) = 1
    rw [coeff_qdetPoly_top _ _ (by omega), htop]
  · intro i u
    rw [← evU_qdetPoly (X i) u, evU_apply,
      eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (natDegree_qdetPoly_le (X i)))]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [RingHom.id_apply, ← map_pow]
    rw [Algebra.smul_def]
    exact (Algebra.commutes _ _).symm
  · intro i hi
    obtain ⟨-, -, hsub⟩ := prod_linear (d i) fun k => X i k k - algebraMap ℂ (Module.End ℂ W) ((k : ℕ) : ℂ)
    show (qdetPoly (X i)).coeff (d i - 1) = _
    rw [coeff_qdetPoly_top _ _ (by omega), hsub (d i - 1) (by omega), Finset.sum_sub_distrib,
      ← map_sum, sum_fin_cast, Algebra.algebraMap_eq_smul_one]
  · intro i j a b
    have hm := coeff_qdetPoly_mem (X j) (Subalgebra.centralizer ℂ {(qdetPoly (X i)).coeff a})
      (fun p q => by
        rw [Subalgebra.mem_centralizer_iff]
        rintro g rfl
        exact (hL2 i j a p q).eq) b
    rw [Subalgebra.mem_centralizer_iff] at hm
    exact hm _ rfl

end GlobalTheory.CompanionTheory.RgCOBlock
