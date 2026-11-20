import Mathlib
import GroundTheory.Brauer.TensorSimple
open scoped TensorProduct

namespace GlobalTheory.CsaCharpoly
open Polynomial

/- English proof (translation)
Break down `eq_bot_or_eq_top (TwoSidedIdeal.ker f) with h | h` into its components or cases. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `: x ∈ TwoSidedIdeal.ker f` using `(TwoSidedIdeal.mem_ker f).2 hx`. Rewrite `this` using `[h]`.

Simplify using `using this`. It suffices to derive a contradiction. Establish `: (1 : R) ∈ TwoSidedIdeal.ker f` using `by rw [h]; trivial`. Rewrite `this` using `[TwoSidedIdeal.mem_ker, map_one]`. Conclude with `one_ne_zero this`.
-/
theorem injective_of_isSimpleRing {R S : Type} [Ring R] [IsSimpleRing R] [Ring S] [Nontrivial S]
    (f : R →+* S) : Function.Injective f := by
  rcases eq_bot_or_eq_top (TwoSidedIdeal.ker f) with h | h
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have : x ∈ TwoSidedIdeal.ker f := (TwoSidedIdeal.mem_ker f).2 hx
    rw [h] at this
    simpa using this
  · exfalso
    have : (1 : R) ∈ TwoSidedIdeal.ker f := by rw [h]; trivial
    rw [TwoSidedIdeal.mem_ker, map_one] at this
    exact one_ne_zero this

/- English proof (translation)
Use `set x : K ⊗[F] A := (1 : K) ⊗ₜ[F] g with hx`. Establish `hli : LinearIndependent K (fun j : Fin (minpoly F g).natDegree => x ^ (j : ℕ))`. Establish `h` using `Module.Flat.linearIndependent_one_tmul (S := K) (linearIndependent_pow (K := F) g)`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`.

Simplify using `[hx, Algebra.TensorProduct.tmul_pow]`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hsum` using `aeval_eq_sum_range' hlt x`. Rewrite `hsum` using `[minpoly.aeval, ← Fin.sum_univ_eq_sum_range (fun i => (minpoly K x).coeff i • x ^ i)]`.

Establish `hc` using `Fintype.linearIndependent_iff.mp hli (fun i => (minpoly K x).coeff i) hsum.symm`. Apply `minpoly.ne_zero hK` to reduce the goal to its premises. Use extensionality with `i`. Rewrite using `[coeff_zero]`. Distinguish the cases in `hi : i < (minpoly F g).natDegree`.

Conclude with `hc ⟨i, hi⟩`. Conclude with `coeff_eq_zero_of_natDegree_lt (by omega)`.
-/
theorem natDegree_minpoly_le_one_tmul {F A : Type} [Field F] [Ring A] [Algebra F A] (K : Type)
    [Field K] [Algebra F K] (g : A) (hK : IsIntegral K ((1 : K) ⊗ₜ[F] g)) :
    (minpoly F g).natDegree ≤ (minpoly K ((1 : K) ⊗ₜ[F] g)).natDegree := by
  set x : K ⊗[F] A := (1 : K) ⊗ₜ[F] g with hx
  have hli : LinearIndependent K (fun j : Fin (minpoly F g).natDegree => x ^ (j : ℕ)) := by
    have h := Module.Flat.linearIndependent_one_tmul (S := K) (linearIndependent_pow (K := F) g)
    convert h using 1
    funext j
    simp [hx, Algebra.TensorProduct.tmul_pow]
  by_contra hlt
  push_neg at hlt
  have hsum := aeval_eq_sum_range' hlt x
  rw [minpoly.aeval, ← Fin.sum_univ_eq_sum_range (fun i => (minpoly K x).coeff i • x ^ i)] at hsum
  have hc := Fintype.linearIndependent_iff.mp hli (fun i => (minpoly K x).coeff i) hsum.symm
  apply minpoly.ne_zero hK
  ext i
  rw [coeff_zero]
  by_cases hi : i < (minpoly F g).natDegree
  · exact hc ⟨i, hi⟩
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

end GlobalTheory.CsaCharpoly

namespace GlobalTheory
open Polynomial

/- English proof (translation)
Introduce `F L C _ _ _ _ _ _ _ _ n _ ι a hdeg`. Establish `ha : IsIntegral F a` using `IsIntegral.of_finite F a`. Establish `hn : 0 < n` using `hdeg ▸ minpoly.natDegree_pos ha`. Use `haveI : NeZero n := ⟨hn.ne'⟩`. Set `g : L ⊗[F] C →ₐ[L] Matrix (Fin n) (Fin n) L` to `Algebra.TensorProduct.lift (Algebra.ofId L _) ι (fun l y ↦ Algebra.commute_algebraMap_left l _)`.

Use `haveI : IsSimpleRing (L ⊗[F] C) := GroundTheory.Brauer.isSimpleRing_tensorProduct_of_right`. Establish `hg : Function.Injective g` using `GlobalTheory.CsaCharpoly.injective_of_isSimpleRing g.toRingHom`. Establish `eg : g ((1 : L) ⊗ₜ a) = ι a`. Simplify using `only [g]`. Use `erw [Algebra.TensorProduct.lift_tmul]`.

Simplify using the standard rewrite rules. Establish `hyi : IsIntegral L ((1 : L) ⊗ₜ[F] a)` using `IsIntegral.of_finite L _`. Establish `hxi : IsIntegral L (ι a)` using `IsIntegral.of_finite L _`. Establish `hmin : minpoly L (ι a) = minpoly L ((1 : L) ⊗ₜ[F] a)`. Rewrite using `[← eg]`.

Conclude with `minpoly.algHom_eq g hg _`. Establish `hge : n ≤ (minpoly L (ι a)).natDegree`. Rewrite using `[hmin, ← hdeg]`. Conclude with `GlobalTheory.CsaCharpoly.natDegree_minpoly_le_one_tmul L a hyi`. Establish `hdvd : minpoly L (ι a) ∣ (minpoly F a).map (algebraMap F L)`.

Apply `minpoly.dvd` to reduce the goal to its premises. Rewrite using `[aeval_map_algebraMap, aeval_algHom_apply, minpoly.aeval, map_zero]`. Establish `hmonic : ((minpoly F a).map (algebraMap F L)).Monic` using `(minpoly.monic ha).map _`. Establish `hdm : ((minpoly F a).map (algebraMap F L)).natDegree = n` using `by rw [natDegree_map, hdeg]`. Establish `e1 : (minpoly F a).map (algebraMap F L) = minpoly L (ι a)` using `eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxi) hmonic hdvd (by rw [hdm]; exact hge)`.

Establish `e2 : (ι a).charpoly = minpoly L (ι a)` using `eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxi) (Matrix.charpoly_monic _) (Matrix.minpoly_dvd_charpoly _) (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hge)`. Rewrite using `[e2, e1]`.
-/
theorem charpoly_algHom_eq_map_minpoly : ∀ (F L C : Type) [Field F] [Field L] [Algebra F L] [Ring C]
    [Algebra F C] [Algebra.IsCentral F C] [IsSimpleRing C] [FiniteDimensional F C] (n : ℕ),
    Module.finrank F C = n ^ 2 → ∀ (ι : C →ₐ[F] Matrix (Fin n) (Fin n) L) (y : C),
    (minpoly F y).natDegree = n → (ι y).charpoly = (minpoly F y).map (algebraMap F L) := by
  intro F L C _ _ _ _ _ _ _ _ n _ ι a hdeg
  have ha : IsIntegral F a := IsIntegral.of_finite F a
  have hn : 0 < n := hdeg ▸ minpoly.natDegree_pos ha
  haveI : NeZero n := ⟨hn.ne'⟩
  let g : L ⊗[F] C →ₐ[L] Matrix (Fin n) (Fin n) L :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) ι (fun l y ↦ Algebra.commute_algebraMap_left l _)
  haveI : IsSimpleRing (L ⊗[F] C) := GroundTheory.Brauer.isSimpleRing_tensorProduct_of_right
  have hg : Function.Injective g := GlobalTheory.CsaCharpoly.injective_of_isSimpleRing g.toRingHom
  have eg : g ((1 : L) ⊗ₜ a) = ι a := by
    simp only [g]; erw [Algebra.TensorProduct.lift_tmul]; simp
  have hyi : IsIntegral L ((1 : L) ⊗ₜ[F] a) := IsIntegral.of_finite L _
  have hxi : IsIntegral L (ι a) := IsIntegral.of_finite L _
  have hmin : minpoly L (ι a) = minpoly L ((1 : L) ⊗ₜ[F] a) := by
    rw [← eg]; exact minpoly.algHom_eq g hg _
  have hge : n ≤ (minpoly L (ι a)).natDegree := by
    rw [hmin, ← hdeg]; exact GlobalTheory.CsaCharpoly.natDegree_minpoly_le_one_tmul L a hyi
  have hdvd : minpoly L (ι a) ∣ (minpoly F a).map (algebraMap F L) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hmonic : ((minpoly F a).map (algebraMap F L)).Monic := (minpoly.monic ha).map _
  have hdm : ((minpoly F a).map (algebraMap F L)).natDegree = n := by rw [natDegree_map, hdeg]
  have e1 : (minpoly F a).map (algebraMap F L) = minpoly L (ι a) :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxi) hmonic hdvd (by rw [hdm]; exact hge)
  have e2 : (ι a).charpoly = minpoly L (ι a) :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxi) (Matrix.charpoly_monic _)
      (Matrix.minpoly_dvd_charpoly _) (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hge)
  rw [e2, e1]

end GlobalTheory
