import Mathlib
import Formalism.HermitianLattices.GenusCovolBound
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusBasic

open Module Matrix

noncomputable section

namespace Formalism.HermitianLatticesTheory

section Trace

variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Simplify using `only [map_add, LinearMap.add_apply]`.
-/
theorem classSetAssembly_tr_add_left (h : V →ₗ⋆[K] V →ₗ[K] K) (x y z : V) :
    Algebra.trace ℚ K (h (x + y) z) = Algebra.trace ℚ K (h x z) + Algebra.trace ℚ K (h y z) := by
  simp only [map_add, LinearMap.add_apply]

/- English proof (translation)
Simplify using `only [map_sub, LinearMap.sub_apply]`.
-/
theorem classSetAssembly_tr_sub_left (h : V →ₗ⋆[K] V →ₗ[K] K) (x y z : V) :
    Algebra.trace ℚ K (h (x - y) z) = Algebra.trace ℚ K (h x z) - Algebra.trace ℚ K (h y z) := by
  simp only [map_sub, LinearMap.sub_apply]

/- English proof (translation)
Simplify using `only [map_add]`.
-/
theorem classSetAssembly_tr_add_right (h : V →ₗ⋆[K] V →ₗ[K] K) (x y z : V) :
    Algebra.trace ℚ K (h z (x + y)) = Algebra.trace ℚ K (h z x) + Algebra.trace ℚ K (h z y) := by
  simp only [map_add]

/- English proof (translation)
Establish `e : (q : K) * a = q • a`. Rewrite using `[Algebra.smul_def, eq_ratCast]`. Rewrite using `[e, map_smul, smul_eq_mul]`.
-/
theorem classSetAssembly_ratCast_mul (q : ℚ) (a : K) :
    Algebra.trace ℚ K ((q : K) * a) = q * Algebra.trace ℚ K a := by
  have e : (q : K) * a = q • a := by
    rw [Algebra.smul_def, eq_ratCast]
  rw [e, map_smul, smul_eq_mul]

/- English proof (translation)
Establish `e : h ((q : K) • x) y = (q : K) * h x y`. Rewrite using `[map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_ratCast]`. Rewrite using `[e, classSetAssembly_ratCast_mul]`.
-/
theorem classSetAssembly_tr_qsmul_left (h : V →ₗ⋆[K] V →ₗ[K] K) (q : ℚ) (x y : V) :
    Algebra.trace ℚ K (h ((q : K) • x) y) = q * Algebra.trace ℚ K (h x y) := by
  have e : h ((q : K) • x) y = (q : K) * h x y := by
    rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_ratCast]
  rw [e, classSetAssembly_ratCast_mul]

/- English proof (translation)
Rewrite using `[map_smul, smul_eq_mul, classSetAssembly_ratCast_mul]`.
-/
theorem classSetAssembly_tr_qsmul_right (h : V →ₗ⋆[K] V →ₗ[K] K) (q : ℚ) (x y : V) :
    Algebra.trace ℚ K (h x ((q : K) • y)) = q * Algebra.trace ℚ K (h x y) := by
  rw [map_smul, smul_eq_mul, classSetAssembly_ratCast_mul]

/- English proof (translation)
Rewrite using `[map_sum, LinearMap.sum_apply, map_sum]`.
-/
theorem classSetAssembly_tr_sum_left (h : V →ₗ⋆[K] V →ₗ[K] K) {ι : Type*} (s : Finset ι)
    (f : ι → V) (y : V) :
    Algebra.trace ℚ K (h (∑ i ∈ s, f i) y) = ∑ i ∈ s, Algebra.trace ℚ K (h (f i) y) := by
  rw [map_sum, LinearMap.sum_apply, map_sum]

/- English proof (translation)
Rewrite using `[map_sum, map_sum]`.
-/
theorem classSetAssembly_tr_sum_right (h : V →ₗ⋆[K] V →ₗ[K] K) {ι : Type*} (s : Finset ι)
    (f : ι → V) (y : V) :
    Algebra.trace ℚ K (h y (∑ i ∈ s, f i)) = ∑ i ∈ s, Algebra.trace ℚ K (h y (f i)) := by
  rw [map_sum, map_sum]

/- English proof (translation)
Establish `hint_r : IsIntegral ℤ (algebraMap (NumberField.RingOfIntegers K) K o)`. Conclude with `(NumberField.RingOfIntegers.isIntegral o).algebraMap`. Establish `ht : IsIntegral ℤ (Algebra.trace ℚ K (algebraMap (NumberField.RingOfIntegers K) K o))` using `Algebra.isIntegral_trace hint_r`. Take `⟨z, hz⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp ht`. Conclude with `⟨z, hz.symm.trans (eq_intCast (algebraMap ℤ ℚ) z)⟩`.
-/
theorem classSetAssembly_trace_int (o : NumberField.RingOfIntegers K) :
    ∃ z : ℤ, Algebra.trace ℚ K (algebraMap (NumberField.RingOfIntegers K) K o) = z := by
  have hint_r : IsIntegral ℤ (algebraMap (NumberField.RingOfIntegers K) K o) := by
    exact (NumberField.RingOfIntegers.isIntegral o).algebraMap
  have ht : IsIntegral ℤ (Algebra.trace ℚ K (algebraMap (NumberField.RingOfIntegers K) K o)) :=
    Algebra.isIntegral_trace hint_r
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp ht
  exact ⟨z, hz.symm.trans (eq_intCast (algebraMap ℤ ℚ) z)⟩

/- English proof (translation)
Take `⟨o, ho⟩` from `Submodule.mem_one.mp hxy`. Take `⟨z, hz⟩` from `classSetAssembly_trace_int o`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[← hz, ho, ← classSetAssembly_ratCast_mul, Rat.cast_natCast]`.
-/
theorem classSetAssembly_dint [Module (NumberField.RingOfIntegers K) V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (d : ℕ) (x y : V)
    (hxy : (d : K) * h x y ∈ (1 : Submodule (NumberField.RingOfIntegers K) K)) :
    ∃ z : ℤ, (d : ℚ) * Algebra.trace ℚ K (h x y) = z := by
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp hxy
  obtain ⟨z, hz⟩ := classSetAssembly_trace_int o
  refine ⟨z, ?_⟩
  rw [← hz, ho, ← classSetAssembly_ratCast_mul, Rat.cast_natCast]

end Trace

section Real

variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Establish `hc : Fintype.card (Fin n) = Module.finrank ℝ (EuclideanSpace ℝ (Fin n))` using `by simp`. Conclude with `hw.span_eq_top_of_card_eq_finrank' hc`.
-/
private theorem span_eq_top_of_li_lemma {n : ℕ} (w : Fin n → EuclideanSpace ℝ (Fin n))
    (hw : LinearIndependent ℝ w) : Submodule.span ℝ (Set.range w) = ⊤ := by
  have hc : Fintype.card (Fin n) = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by simp
  exact hw.span_eq_top_of_card_eq_finrank' hc

/- English proof (translation)
Establish `hs` using `span_eq_top_of_li_lemma w hw`. Take `⟨b, hb⟩ : ∃ b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)), ∀ i, b i = w i` from `⟨Basis.mk hw (by rw [hs]), fun i => by simp [Basis.mk_apply]⟩`. Establish `key : inner ℝ v (∑ i, b.repr v i • b i) = 0`. Rewrite using `[inner_sum]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[inner_smul_right, hb i, hv i, mul_zero]`. Rewrite `key` using `[b.sum_repr v]`. Conclude with `inner_self_eq_zero.mp key`.
-/
private theorem eq_zero_of_inner_li_lemma_2 {n : ℕ} (w : Fin n → EuclideanSpace ℝ (Fin n))
    (hw : LinearIndependent ℝ w) (v : EuclideanSpace ℝ (Fin n))
    (hv : ∀ j, inner ℝ v (w j) = 0) : v = 0 := by
  have hs := span_eq_top_of_li_lemma w hw
  obtain ⟨b, hb⟩ : ∃ b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)), ∀ i, b i = w i :=
    ⟨Basis.mk hw (by rw [hs]), fun i => by simp [Basis.mk_apply]⟩
  have key : inner ℝ v (∑ i, b.repr v i • b i) = 0 := by
    rw [inner_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [inner_smul_right, hb i, hv i, mul_zero]
  rw [b.sum_repr v] at key
  exact inner_self_eq_zero.mp key

/- English proof (translation)
Establish `h0 : ι y = 0` using `eq_zero_of_inner_li_lemma_2 (ι ∘ u) hu (ι y) (fun j => by`. Rewrite using `[Function.comp_apply, hι, hy j, Rat.cast_zero])`. Assume the negation of the conclusion as `hne`. Establish `hp` using `hpos y hne`. Establish `h2 : ((Algebra.trace ℚ K (h y y) : ℚ) : ℝ) = 0` using `by rw [← hι, h0, inner_zero_left]`.

Establish `h3 : Algebra.trace ℚ K (h y y) = 0` using `by exact_mod_cast h2`. Rewrite `hp` using `[h3]`. Conclude with `lt_irrefl _ hp`.
-/
theorem classSetAssembly_nondeg {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (u : Fin n → V) (hu : LinearIndependent ℝ (ι ∘ u)) (y : V)
    (hy : ∀ j, Algebra.trace ℚ K (h y (u j)) = 0) : y = 0 := by
  have h0 : ι y = 0 := eq_zero_of_inner_li_lemma_2 (ι ∘ u) hu (ι y) (fun j => by
    rw [Function.comp_apply, hι, hy j, Rat.cast_zero])
  by_contra hne
  have hp := hpos y hne
  have h2 : ((Algebra.trace ℚ K (h y y) : ℚ) : ℝ) = 0 := by rw [← hι, h0, inner_zero_left]
  have h3 : Algebra.trace ℚ K (h y y) = 0 := by exact_mod_cast h2
  rw [h3] at hp
  exact lt_irrefl _ hp

/- English proof (translation)
Conclude with `map_ratCast_smul ι K ℝ q x`.
-/
private theorem addHom_ratCast_smul_lemma_3 {K V : Type*} [Field K] [CharZero K] [AddCommGroup V]
    [Module K V] {n : ℕ} (ι : V →+ EuclideanSpace ℝ (Fin n)) (q : ℚ) (x : V) :
    ι ((q : K) • x) = (q : ℝ) • ι x := by
  exact map_ratCast_smul ι K ℝ q x

/- English proof (translation)
Establish `hsum : ∑ i, ((g i : ℚ) : ℝ) • (ι ∘ u) i = 0`. Establish `e` using `congrArg ι hg`. Rewrite `e` using `[map_sum, map_zero]`. Rewrite using `[← e]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Function.comp_apply, addHom_ratCast_smul_lemma_3 ι (g i) (u i)]`. Use function extensionality and compare the values at `i`. Use `Fintype.linearIndependent_iff.mp hu (fun i => ((g i : ℚ) : ℝ)) hsum i` as an intermediate fact. Simplify using `using this`.
-/
theorem classSetAssembly_qindep {n : ℕ} (ι : V →+ EuclideanSpace ℝ (Fin n))
    (u : Fin n → V) (hu : LinearIndependent ℝ (ι ∘ u)) (g : Fin n → ℚ)
    (hg : ∑ i, (g i : K) • u i = 0) : g = 0 := by
  have hsum : ∑ i, ((g i : ℚ) : ℝ) • (ι ∘ u) i = 0 := by
    have e := congrArg ι hg
    rw [map_sum, map_zero] at e
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Function.comp_apply, addHom_ratCast_smul_lemma_3 ι (g i) (u i)]
  funext i
  have := Fintype.linearIndependent_iff.mp hu (fun i => ((g i : ℚ) : ℝ)) hsum i
  simpa using this

/- English proof (translation)
Establish `hty : ∀ j, Algebra.trace ℚ K (h (∑ i, (r i : K) • u i) (u j)) = 0`. Introduce `j`. Rewrite using `[classSetAssembly_tr_sum_left, ← hr j]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[classSetAssembly_tr_qsmul_left]`.

Establish `h0 : ∑ i, (r i : K) • u i = 0` using `classSetAssembly_nondeg h hpos ι hι u hu _ hty`. Conclude with `classSetAssembly_qindep (K := K) ι u hu r h0`.
-/
theorem classSetAssembly_coord_zero {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (u : Fin n → V) (hu : LinearIndependent ℝ (ι ∘ u)) (r : Fin n → ℚ)
    (hr : ∀ j, ∑ i, r i * Algebra.trace ℚ K (h (u i) (u j)) = 0) : r = 0 := by
  have hty : ∀ j, Algebra.trace ℚ K (h (∑ i, (r i : K) • u i) (u j)) = 0 := by
    intro j
    rw [classSetAssembly_tr_sum_left, ← hr j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [classSetAssembly_tr_qsmul_left]
  have h0 : ∑ i, (r i : K) • u i = 0 := classSetAssembly_nondeg h hpos ι hι u hu _ hty
  exact classSetAssembly_qindep (K := K) ι u hu r h0

/- English proof (translation)
Set `L : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ)` to `{ toFun := fun r j => ∑ i, r i * Algebra.trace ℚ K (h (u i) (u j)) map_add' := fun a b => by funext j; simp [add_mul, Finset.sum_add_distrib] map_smul' := fun c a => by funext j; simp [Finset.mul_sum, mul_assoc] }`. Establish `hinj : Function.Injective L`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `r hr0`. Conclude with `classSetAssembly_coord_zero h hpos ι hι u hu r (fun j => congrFun hr0 j)`.

Take `⟨t, ht⟩` from `(LinearMap.injective_iff_surjective.mp hinj) (fun j => Algebra.trace ℚ K (h x (u j)))`. Use `⟨t, ?_⟩` and prove the remaining obligations. Establish `hz : x - ∑ i, (t i : K) • u i = 0`. Apply `classSetAssembly_nondeg h hpos ι hι u hu` to reduce the goal to its premises. Introduce `j`.

Establish `e : ∑ i, t i * Algebra.trace ℚ K (h (u i) (u j)) = Algebra.trace ℚ K (h x (u j))` using `congrFun ht j`. Rewrite using `[classSetAssembly_tr_sub_left, classSetAssembly_tr_sum_left, ← e, sub_eq_zero]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[classSetAssembly_tr_qsmul_left]`. Conclude with `sub_eq_zero.mp hz`.
-/
theorem classSetAssembly_span {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (u : Fin n → V) (hu : LinearIndependent ℝ (ι ∘ u)) (x : V) :
    ∃ t : Fin n → ℚ, x = ∑ i, (t i : K) • u i := by
  classical
  let L : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ) :=
    { toFun := fun r j => ∑ i, r i * Algebra.trace ℚ K (h (u i) (u j))
      map_add' := fun a b => by funext j; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c a => by funext j; simp [Finset.mul_sum, mul_assoc] }
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro r hr0
    exact classSetAssembly_coord_zero h hpos ι hι u hu r (fun j => congrFun hr0 j)
  obtain ⟨t, ht⟩ := (LinearMap.injective_iff_surjective.mp hinj)
    (fun j => Algebra.trace ℚ K (h x (u j)))
  refine ⟨t, ?_⟩
  have hz : x - ∑ i, (t i : K) • u i = 0 := by
    apply classSetAssembly_nondeg h hpos ι hι u hu
    intro j
    have e : ∑ i, t i * Algebra.trace ℚ K (h (u i) (u j)) = Algebra.trace ℚ K (h x (u j)) :=
      congrFun ht j
    rw [classSetAssembly_tr_sub_left, classSetAssembly_tr_sum_left, ← e, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [classSetAssembly_tr_qsmul_left]
  exact sub_eq_zero.mp hz

/- English proof (translation)
Take `⟨M, hM⟩ : ∃ M : Fin n → Fin n → ℤ, ∀ i j, (d : ℚ) * Algebra.trace ℚ K (h (u i) (u j)) = M i j` from `by choose M hM using ‹∀ i j, ∃ z : ℤ, (d : ℚ) * Algebra.trace ℚ K (h (u i) (u j)) = z›`. Conclude with `⟨M, hM⟩`. Take `⟨A, hAdef⟩ : ∃ A : Matrix (Fin n) (Fin n) ℚ, A = (Int.castRingHom ℚ).mapMatrix (Matrix.of M)` from `⟨_, rfl⟩`. Establish `hA : ∀ i j, A i j = (d : ℚ) * Algebra.trace ℚ K (h (u i) (u j))` using `fun i j => by`. Rewrite using `[hAdef, hM i j]`.

Simplify using the standard rewrite rules. Establish `hdetA : A.det = (((Matrix.of M).det : ℤ) : ℚ)`. Rewrite using `[hAdef, ← RingHom.map_det]`. Simplify using the standard rewrite rules. Establish `hadj : A.adjugate = (Int.castRingHom ℚ).mapMatrix (Matrix.of M).adjugate`.

Rewrite using `[hAdef, RingHom.map_adjugate]`. Establish `hdet : (Matrix.of M).det ≠ 0`. Introduce `h0`. Establish `hA0 : A.det = 0` using `by rw [hdetA, h0, Int.cast_zero]`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_vecMul_eq_zero_iff.mpr hA0`.

Establish `hr` using `classSetAssembly_coord_zero h hpos ι hι u hu (fun i => (d : ℚ) * v i) (fun j => by`. Establish `e` using `congrFun hv j`. Simplify using `only [Matrix.vecMul, dotProduct, hA, Pi.zero_apply] at e`. Rewrite using `[← e]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use the proof step `ring)`. Apply `hv0` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Establish `e` using `congrFun hr i`. Simplify using `only [Pi.zero_apply] at e`.

Conclude with `(mul_eq_zero.mp e).resolve_left (by exact_mod_cast hd.ne')`. Use `⟨(Matrix.of M).det, hdet, fun x hx => ?_⟩` and prove the remaining obligations. Use `choose w hw using hx`. Take `⟨t, ht⟩` from `classSetAssembly_span h hpos ι hι u hu x`. Establish `hvec : Matrix.vecMul t A = fun j => ((w j : ℤ) : ℚ)`.

Use function extensionality and compare the values at `j`. Rewrite using `[← hw j, ht, classSetAssembly_tr_sum_left, Finset.mul_sum]`. Simplify using `only [Matrix.vecMul, dotProduct, hA]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[classSetAssembly_tr_qsmul_left]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hkey : A.det • t = Matrix.vecMul (fun j => ((w j : ℤ) : ℚ)) A.adjugate`. Rewrite using `[← hvec, Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one]`. Use `set z : Fin n → ℤ := Matrix.vecMul w (Matrix.of M).adjugate with hzdef`. Establish `hz : ∀ i, ((z i : ℤ) : ℚ) = (((Matrix.of M).det : ℤ) : ℚ) * t i`.

Introduce `i`. Establish `e` using `congrFun hkey i`. Rewrite `e` using `[Pi.smul_apply, smul_eq_mul, hdetA, hadj]`. Rewrite using `[e, hzdef]`. Simplify using `only [Matrix.vecMul, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply]`.

Use `push_cast`. Both sides reduce to the same expression. Establish `hx' : (Matrix.of M).det • x = ∑ i, z i • u i`. Rewrite using `[ht, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← Int.cast_smul_eq_zsmul K, ← Int.cast_smul_eq_zsmul K, smul_smul]`. Use `congr 1`. Establish `e` using `congrArg (fun q : ℚ => (q : K)) (hz i)`. Simplify using `only [Rat.cast_mul, Rat.cast_intCast] at e`. Conclude with `e.symm`.

Rewrite using `[hx']`. Conclude with `sum_mem fun i _ => zsmul_mem (AddSubgroup.subset_closure (Set.mem_range_self i)) _`.
-/
theorem classSetAssembly_denom {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (u : Fin n → V) (hu : LinearIndependent ℝ (ι ∘ u)) (d : ℕ) (hd : 0 < d)
    (hint : ∀ i j, ∃ z : ℤ, (d : ℚ) * Algebra.trace ℚ K (h (u i) (u j)) = z) :
    ∃ e : ℤ, e ≠ 0 ∧ ∀ x : V, (∀ j, ∃ z : ℤ, (d : ℚ) * Algebra.trace ℚ K (h x (u j)) = z) →
      e • x ∈ AddSubgroup.closure (Set.range u) := by
  obtain ⟨M, hM⟩ : ∃ M : Fin n → Fin n → ℤ,
      ∀ i j, (d : ℚ) * Algebra.trace ℚ K (h (u i) (u j)) = M i j := by
    choose M hM using ‹∀ i j, ∃ z : ℤ, (d : ℚ) * Algebra.trace ℚ K (h (u i) (u j)) = z›
    exact ⟨M, hM⟩
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix (Fin n) (Fin n) ℚ,
      A = (Int.castRingHom ℚ).mapMatrix (Matrix.of M) := ⟨_, rfl⟩
  have hA : ∀ i j, A i j = (d : ℚ) * Algebra.trace ℚ K (h (u i) (u j)) := fun i j => by
    rw [hAdef, hM i j]
    simp
  have hdetA : A.det = (((Matrix.of M).det : ℤ) : ℚ) := by
    rw [hAdef, ← RingHom.map_det]
    simp
  have hadj : A.adjugate = (Int.castRingHom ℚ).mapMatrix (Matrix.of M).adjugate := by
    rw [hAdef, RingHom.map_adjugate]
  have hdet : (Matrix.of M).det ≠ 0 := by
    intro h0
    have hA0 : A.det = 0 := by rw [hdetA, h0, Int.cast_zero]
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hA0
    have hr := classSetAssembly_coord_zero h hpos ι hι u hu (fun i => (d : ℚ) * v i)
      (fun j => by
        have e := congrFun hv j
        simp only [Matrix.vecMul, dotProduct, hA, Pi.zero_apply] at e
        rw [← e]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring)
    apply hv0
    funext i
    have e := congrFun hr i
    simp only [Pi.zero_apply] at e
    exact (mul_eq_zero.mp e).resolve_left (by exact_mod_cast hd.ne')
  refine ⟨(Matrix.of M).det, hdet, fun x hx => ?_⟩
  choose w hw using hx
  obtain ⟨t, ht⟩ := classSetAssembly_span h hpos ι hι u hu x
  have hvec : Matrix.vecMul t A = fun j => ((w j : ℤ) : ℚ) := by
    funext j
    rw [← hw j, ht, classSetAssembly_tr_sum_left, Finset.mul_sum]
    simp only [Matrix.vecMul, dotProduct, hA]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [classSetAssembly_tr_qsmul_left]
    ring
  have hkey : A.det • t = Matrix.vecMul (fun j => ((w j : ℤ) : ℚ)) A.adjugate := by
    rw [← hvec, Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul,
      Matrix.vecMul_one]
  set z : Fin n → ℤ := Matrix.vecMul w (Matrix.of M).adjugate with hzdef
  have hz : ∀ i, ((z i : ℤ) : ℚ) = (((Matrix.of M).det : ℤ) : ℚ) * t i := by
    intro i
    have e := congrFun hkey i
    rw [Pi.smul_apply, smul_eq_mul, hdetA, hadj] at e
    rw [e, hzdef]
    simp only [Matrix.vecMul, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply]
    push_cast
    rfl
  have hx' : (Matrix.of M).det • x = ∑ i, z i • u i := by
    rw [ht, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul K, ← Int.cast_smul_eq_zsmul K, smul_smul]
    congr 1
    have e := congrArg (fun q : ℚ => (q : K)) (hz i)
    simp only [Rat.cast_mul, Rat.cast_intCast] at e
    exact e.symm
  rw [hx']
  exact sum_mem fun i _ => zsmul_mem (AddSubgroup.subset_closure (Set.mem_range_self i)) _

end Real

section Finite

/- English proof (translation)
Use `set N : ℤ := ⌈(d : ℝ) * R⌉`. Use `((Set.finite_Icc (-N) N).image (fun z : ℤ => (z : ℚ) / d)).subset ?_` and prove the remaining obligations. Introduce and unpack `q ⟨⟨z, hz⟩, hq⟩`. Establish `hdq : (d : ℚ) ≠ 0` using `by exact_mod_cast hd.ne'`. Establish `hzR : ((z : ℚ) : ℝ) = (d : ℝ) * (q : ℝ)`.

Rewrite using `[← hz, Rat.cast_mul, Rat.cast_natCast]`. Establish `hzR' : (z : ℝ) = (d : ℝ) * (q : ℝ)` using `by exact_mod_cast hzR`. Establish `habs : |(z : ℝ)| ≤ (d : ℝ) * R`. Rewrite using `[hzR', abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ d)]`. Conclude with `mul_le_mul_of_nonneg_left hq (by positivity)`.

Establish `hN : (d : ℝ) * R ≤ (N : ℝ)` using `Int.le_ceil _`. Establish `h1 : (z : ℝ) ≤ N` using `le_trans (le_abs_self _) (habs.trans hN)`. Establish `h2 : -(N : ℝ) ≤ z`. Use `neg_abs_le (z : ℝ)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨z, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `h3 : ((-N : ℤ) : ℝ) ≤ (z : ℝ)` using `by push_cast; linarith`. Conclude with `h3` after adjusting the coercions. Conclude with `h1` after adjusting the coercions. Use `show (z : ℚ) / d = q`.

Rewrite using `[← hz]`. Clear the denominators using the available nonvanishing facts.
-/
theorem classSetAssembly_finite_rat (d : ℕ) (hd : 0 < d) (R : ℝ) :
    {q : ℚ | (∃ z : ℤ, (d : ℚ) * q = z) ∧ |(q : ℝ)| ≤ R}.Finite := by
  set N : ℤ := ⌈(d : ℝ) * R⌉
  refine ((Set.finite_Icc (-N) N).image (fun z : ℤ => (z : ℚ) / d)).subset ?_
  rintro q ⟨⟨z, hz⟩, hq⟩
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hzR : ((z : ℚ) : ℝ) = (d : ℝ) * (q : ℝ) := by
    rw [← hz, Rat.cast_mul, Rat.cast_natCast]
  have hzR' : (z : ℝ) = (d : ℝ) * (q : ℝ) := by exact_mod_cast hzR
  have habs : |(z : ℝ)| ≤ (d : ℝ) * R := by
    rw [hzR', abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ d)]
    exact mul_le_mul_of_nonneg_left hq (by positivity)
  have hN : (d : ℝ) * R ≤ (N : ℝ) := Int.le_ceil _
  have h1 : (z : ℝ) ≤ N := le_trans (le_abs_self _) (habs.trans hN)
  have h2 : -(N : ℝ) ≤ z := by
    have := neg_abs_le (z : ℝ)
    linarith
  refine ⟨z, ⟨?_, ?_⟩, ?_⟩
  · have h3 : ((-N : ℤ) : ℝ) ≤ (z : ℝ) := by push_cast; linarith
    exact_mod_cast h3
  · exact_mod_cast h1
  · show (z : ℚ) / d = q
    rw [← hz]
    field_simp

variable {V : Type*} [AddCommGroup V]

/- English proof (translation)
Establish `heK : (e : K) ≠ 0` using `Int.cast_ne_zero.mpr he`. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[SetLike.mem_coe, AddSubgroup.mem_comap]`. Establish `hx : (zsmulAddGroupHom e : V →+ V) (((e : K)⁻¹) • u i) = u i` using `by show e • (((e : K)⁻¹) • u i) = u i`.

Rewrite using `[← Int.cast_smul_eq_zsmul K, smul_smul, mul_inv_cancel₀ heK, one_smul]`. Rewrite using `[hx]`. Conclude with `AddSubgroup.subset_closure ⟨i, rfl⟩`.
-/
theorem classSetAssembly_torsion {K : Type*} [Field K] [CharZero K] [Module K V] {n : ℕ} (u : Fin n → V)
    (e : ℤ) (he : e ≠ 0) :
    AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i) ≤
      (AddSubgroup.closure (Set.range u)).comap (zsmulAddGroupHom e) := by
  have heK : (e : K) ≠ 0 := Int.cast_ne_zero.mpr he
  rw [AddSubgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_comap]
  have hx : (zsmulAddGroupHom e : V →+ V) (((e : K)⁻¹) • u i) = u i := by
    show e • (((e : K)⁻¹) • u i) = u i
    rw [← Int.cast_smul_eq_zsmul K, smul_smul, mul_inv_cancel₀ heK, one_smul]
  rw [hx]
  exact AddSubgroup.subset_closure ⟨i, rfl⟩

/- English proof (translation)
Establish `heK : (e : K) ≠ 0` using `Int.cast_ne_zero.mpr he`. Set `f : V →+ V` to `{ toFun := fun v => ((e : K)⁻¹) • v map_zero' := smul_zero _ map_add' := fun a b => smul_add _ a b }`. Establish `hfx : f (e • x) = x` using `by show ((e : K)⁻¹) • (e • x) = x`. Rewrite using `[← Int.cast_smul_eq_zsmul K, smul_smul, inv_mul_cancel₀ heK, one_smul]`. Establish `hle : AddSubgroup.closure (Set.range u) ≤ (AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i)).comap f`.

Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[SetLike.mem_coe, AddSubgroup.mem_comap]`. Establish `hm : ((e : K)⁻¹) • u i ∈ AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i)` using `AddSubgroup.subset_closure ⟨i, rfl⟩`. Conclude with `hm`.

Establish `h1` using `hle hx`. Rewrite `h1` using `[AddSubgroup.mem_comap, hfx]`. Conclude with `h1`.
-/
theorem classSetAssembly_le_Q {K : Type*} [Field K] [CharZero K] [Module K V] {n : ℕ} (u : Fin n → V)
    (e : ℤ) (he : e ≠ 0) (x : V) (hx : e • x ∈ AddSubgroup.closure (Set.range u)) :
    x ∈ AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i) := by
  have heK : (e : K) ≠ 0 := Int.cast_ne_zero.mpr he
  let f : V →+ V :=
    { toFun := fun v => ((e : K)⁻¹) • v
      map_zero' := smul_zero _
      map_add' := fun a b => smul_add _ a b }
  have hfx : f (e • x) = x := by
    show ((e : K)⁻¹) • (e • x) = x
    rw [← Int.cast_smul_eq_zsmul K, smul_smul, inv_mul_cancel₀ heK, one_smul]
  have hle : AddSubgroup.closure (Set.range u) ≤
      (AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i)).comap f := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    have hm : ((e : K)⁻¹) • u i ∈ AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i) :=
      AddSubgroup.subset_closure ⟨i, rfl⟩
    exact hm
  have h1 := hle hx
  rw [AddSubgroup.mem_comap, hfx] at h1
  exact h1

/- English proof (translation)
Establish `heK : (e : K) ≠ 0` using `Int.cast_ne_zero.mpr he`. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `hx : u i = e • (((e : K)⁻¹) • u i)`. Rewrite using `[← Int.cast_smul_eq_zsmul K, smul_smul, mul_inv_cancel₀ heK, one_smul]`.

Establish `hm : ((e : K)⁻¹) • u i ∈ AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i)` using `AddSubgroup.subset_closure ⟨i, rfl⟩`. Rewrite using `[SetLike.mem_coe, hx]`. Conclude with `AddSubgroup.zsmul_mem _ hm e`.
-/
theorem closure_range_le_closure_range_inv_smul {K : Type*} [Field K] [CharZero K] [Module K V] {n : ℕ} (u : Fin n → V)
    (e : ℤ) (he : e ≠ 0) :
    AddSubgroup.closure (Set.range u) ≤
      AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i) := by
  have heK : (e : K) ≠ 0 := Int.cast_ne_zero.mpr he
  rw [AddSubgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  have hx : u i = e • (((e : K)⁻¹) • u i) := by
    rw [← Int.cast_smul_eq_zsmul K, smul_smul, mul_inv_cancel₀ heK, one_smul]
  have hm : ((e : K)⁻¹) • u i ∈ AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i) :=
    AddSubgroup.subset_closure ⟨i, rfl⟩
  rw [SetLike.mem_coe, hx]
  exact AddSubgroup.zsmul_mem _ hm e

/- English proof (translation)
Set `S : AddSubgroup W` to `{ carrier := {q | ∃ c : Fin n → ℤ, ∑ i, c i • g i = q} zero_mem' := ⟨0, by simp⟩ add_mem' := by`. Introduce and unpack `_ _ ⟨a, rfl⟩ ⟨b, rfl⟩`. Conclude with `⟨a + b, by simp [add_smul, Finset.sum_add_distrib]⟩`. Use the proof step `neg_mem' := by`. Introduce and unpack `_ ⟨a, rfl⟩`.

Conclude with `⟨-a, by simp [neg_smul, Finset.sum_neg_distrib]⟩ }`. Establish `hle : AddSubgroup.closure (Set.range g) ≤ S`. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `⟨Pi.single j 1, by simp [Pi.single_apply]⟩`.

Conclude with `hle hq`.
-/
private theorem exists_coeffs_of_mem_closure_lemma_4 {W : Type*} [AddCommGroup W] {n : ℕ} (g : Fin n → W)
    (q : W) (hq : q ∈ AddSubgroup.closure (Set.range g)) :
    ∃ c : Fin n → ℤ, ∑ i, c i • g i = q := by
  classical
  let S : AddSubgroup W :=
    { carrier := {q | ∃ c : Fin n → ℤ, ∑ i, c i • g i = q}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a + b, by simp [add_smul, Finset.sum_add_distrib]⟩
      neg_mem' := by
        rintro _ ⟨a, rfl⟩
        exact ⟨-a, by simp [neg_smul, Finset.sum_neg_distrib]⟩ }
  have hle : AddSubgroup.closure (Set.range g) ≤ S := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨Pi.single j 1, by simp [Pi.single_apply]⟩
  exact hle hq

/- English proof (translation)
Unfold `FinIntermediate at hE`. Establish `hPQ` using `closure_range_le_closure_range_inv_smul (K := K) u e he`. Establish `hkill : ∀ q ∈ AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i), e • q ∈ AddSubgroup.closure (Set.range u)` using `fun q hq => classSetAssembly_torsion (K := K) u e he hq`. Use `hE W _ _ hPQ ?_` and prove the remaining obligations. Use `set P := AddSubgroup.closure (Set.range u) with hP`.

Use `set Q := AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i) with hQ`. Establish `hgQ : ∀ i, ((e : K)⁻¹) • u i ∈ Q` using `fun i => AddSubgroup.subset_closure ⟨i, rfl⟩`. Set `F : (Fin n → ℤ) → Q ⧸ P.addSubgroupOf Q` to `fun k => QuotientAddGroup.mk ⟨∑ i, k i • (((e : K)⁻¹) • u i), Q.sum_mem fun i _ => Q.zsmul_mem (hgQ i) (k i)⟩`. Establish `hsurj : (Set.univ : Set (Q ⧸ P.addSubgroupOf Q)) ⊆ F '' (Set.univ.pi fun _ => Set.Ico (0 : ℤ) (e.natAbs : ℤ))`. Introduce `z _`.

Take `⟨⟨q, hq⟩, rfl⟩` from `QuotientAddGroup.mk_surjective z`. Take `⟨c, hc⟩` from `exists_coeffs_of_mem_closure_lemma_4 (fun i => ((e : K)⁻¹) • u i) q hq`. Use `⟨fun i => c i % e, ?_, ?_⟩` and prove the remaining obligations. Introduce `i _`. Conclude with `Set.mem_Ico.mpr ⟨Int.emod_nonneg _ he, Int.emod_lt _ he⟩`.

Apply `QuotientAddGroup.eq.mpr` to reduce the goal to its premises. Rewrite using `[AddSubgroup.mem_addSubgroupOf]`. Use `show -(∑ i, (c i % e) • (((e : K)⁻¹) • u i)) + q ∈ P`. Establish `hsum : -(∑ i, (c i % e) • (((e : K)⁻¹) • u i)) + q = ∑ i, (c i / e) • (e • (((e : K)⁻¹) • u i))`. Rewrite using `[← hc, neg_add_eq_sub, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, ← sub_smul]`. Use `congr 1`. Establish `key : c i % e + e * (c i / e) = c i` using `by first`. Consider the case `exact Int.emod_add_ediv (c i) e`.

Consider the case `(have := Int.ediv_add_emod (c i) e; linarith)`. Consider the case `(rw [Int.emod_def]; ring)`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hsum]`. Conclude with `P.sum_mem fun i _ => P.zsmul_mem (hkill _ (hgQ i)) _`.

Establish `hfin : (Set.univ : Set (Q ⧸ P.addSubgroupOf Q)).Finite` using `((Set.Finite.pi fun _ => Set.finite_Ico _ _).image F).subset hsurj`. Conclude with `Set.finite_univ_iff.mp hfin`.
-/
theorem classSetAssembly_finite_between (hE : FinIntermediate) {K W : Type} [Field K] [CharZero K]
    [AddCommGroup W] [Module K W] {n : ℕ} (u : Fin n → W) (e : ℤ) (he : e ≠ 0) :
    {M : AddSubgroup W | AddSubgroup.closure (Set.range u) ≤ M ∧
      M ≤ AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i)}.Finite := by
  classical
  unfold FinIntermediate at hE
  have hPQ := closure_range_le_closure_range_inv_smul (K := K) u e he
  have hkill : ∀ q ∈ AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i),
      e • q ∈ AddSubgroup.closure (Set.range u) :=
    fun q hq => classSetAssembly_torsion (K := K) u e he hq
  refine hE W _ _ hPQ ?_
  set P := AddSubgroup.closure (Set.range u) with hP
  set Q := AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i) with hQ
  have hgQ : ∀ i, ((e : K)⁻¹) • u i ∈ Q := fun i => AddSubgroup.subset_closure ⟨i, rfl⟩
  let F : (Fin n → ℤ) → Q ⧸ P.addSubgroupOf Q := fun k =>
    QuotientAddGroup.mk ⟨∑ i, k i • (((e : K)⁻¹) • u i),
      Q.sum_mem fun i _ => Q.zsmul_mem (hgQ i) (k i)⟩
  have hsurj : (Set.univ : Set (Q ⧸ P.addSubgroupOf Q)) ⊆
      F '' (Set.univ.pi fun _ => Set.Ico (0 : ℤ) (e.natAbs : ℤ)) := by
    intro z _
    obtain ⟨⟨q, hq⟩, rfl⟩ := QuotientAddGroup.mk_surjective z
    obtain ⟨c, hc⟩ := exists_coeffs_of_mem_closure_lemma_4 (fun i => ((e : K)⁻¹) • u i) q hq
    refine ⟨fun i => c i % e, ?_, ?_⟩
    · intro i _
      exact Set.mem_Ico.mpr ⟨Int.emod_nonneg _ he, Int.emod_lt _ he⟩
    · apply QuotientAddGroup.eq.mpr
      rw [AddSubgroup.mem_addSubgroupOf]
      show -(∑ i, (c i % e) • (((e : K)⁻¹) • u i)) + q ∈ P
      have hsum : -(∑ i, (c i % e) • (((e : K)⁻¹) • u i)) + q =
          ∑ i, (c i / e) • (e • (((e : K)⁻¹) • u i)) := by
        rw [← hc, neg_add_eq_sub, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, ← sub_smul]
        congr 1
        have key : c i % e + e * (c i / e) = c i := by
          first
          | exact Int.emod_add_ediv (c i) e
          | (have := Int.ediv_add_emod (c i) e; linarith)
          | (rw [Int.emod_def]; ring)
        linarith
      rw [hsum]
      exact P.sum_mem fun i _ => P.zsmul_mem (hkill _ (hgQ i)) _
  have hfin : (Set.univ : Set (Q ⧸ P.addSubgroupOf Q)).Finite :=
    ((Set.Finite.pi fun _ => Set.finite_Ico _ _).image F).subset hsurj
  exact Set.finite_univ_iff.mp hfin

end Finite

section Isom

variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Establish `hz : y - y' = 0` using `classSetAssembly_nondeg h hpos ι hι w hw _ (fun l => by`. Rewrite using `[classSetAssembly_tr_sub_left, hyy l, sub_self])`. Conclude with `sub_eq_zero.mp hz`.
-/
private theorem eq_of_trace_apply_eq_lemma_5 {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (w : Fin n → V) (hw : LinearIndependent ℝ (ι ∘ w)) (y y' : V)
    (hyy : ∀ l, Algebra.trace ℚ K (h y (w l)) = Algebra.trace ℚ K (h y' (w l))) : y = y' := by
  have hz : y - y' = 0 := classSetAssembly_nondeg h hpos ι hι w hw _ (fun l => by
    rw [classSetAssembly_tr_sub_left, hyy l, sub_self])
  exact sub_eq_zero.mp hz

/- English proof (translation)
Rewrite using `[classSetAssembly_tr_sum_left]`. Conclude with `Finset.sum_congr rfl fun i _ => classSetAssembly_tr_qsmul_left h _ _ _`.
-/
private theorem trace_sum_coeffs_lemma_6 {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K) (t : Fin n → ℚ)
    (w : Fin n → V) (z : V) :
    Algebra.trace ℚ K (h (∑ i, (t i : K) • w i) z) =
      ∑ i, t i * Algebra.trace ℚ K (h (w i) z) := by
  rw [classSetAssembly_tr_sum_left]
  exact Finset.sum_congr rfl fun i _ => classSetAssembly_tr_qsmul_left h _ _ _

/- English proof (translation)
Rewrite using `[Finset.smul_sum, classSetAssembly_tr_sum_left]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, mul_comm a, ← smul_smul, classSetAssembly_tr_qsmul_left]`.
-/
private theorem trace_smul_sum_coeffs_lemma_7 {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K) (a : K) (t : Fin n → ℚ)
    (w : Fin n → V) (z : V) :
    Algebra.trace ℚ K (h (a • ∑ i, (t i : K) • w i) z) =
      ∑ i, t i * Algebra.trace ℚ K (h (a • w i) z) := by
  rw [Finset.smul_sum, classSetAssembly_tr_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, mul_comm a, ← smul_smul, classSetAssembly_tr_qsmul_left]

/- English proof (translation)
Establish `ha : a = ∑ k, ((ω.repr a k : ℚ) : K) * ω k` using `by conv_lhs => rw [← ω.sum_repr a]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, eq_ratCast]`. Use `conv_lhs => rw [ha]`. Rewrite using `[Finset.sum_smul, classSetAssembly_tr_sum_left]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul, classSetAssembly_tr_qsmul_left]`.
-/
private theorem trace_smul_left_basis_lemma_8 {κ : Type*} [Fintype κ] (ω : Basis κ ℚ K)
    (h : V →ₗ⋆[K] V →ₗ[K] K) (a : K) (y z : V) :
    Algebra.trace ℚ K (h (a • y) z) =
      ∑ k, ω.repr a k * Algebra.trace ℚ K (h (ω k • y) z) := by
  have ha : a = ∑ k, ((ω.repr a k : ℚ) : K) * ω k := by
    conv_lhs => rw [← ω.sum_repr a]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, eq_ratCast]
  conv_lhs => rw [ha]
  rw [Finset.sum_smul, classSetAssembly_tr_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul, classSetAssembly_tr_qsmul_left]

/- English proof (translation)
Use `choose t ht using classSetAssembly_span h hpos ι hι u hu`. Establish `hP : ∀ x l, Algebra.trace ℚ K (h (∑ i, (t x i : K) • u' i) (u' l)) = Algebra.trace ℚ K (h x (u l))`. Introduce `x l`. Use `conv_rhs => rw [ht x]`. Rewrite using `[trace_sum_coeffs_lemma_6, trace_sum_coeffs_lemma_6]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hG i l]`. Establish `hQ : ∀ (k : κ) x l, Algebra.trace ℚ K (h (ω k • ∑ i, (t x i : K) • u' i) (u' l)) = Algebra.trace ℚ K (h (ω k • x) (u l))`. Introduce `k x l`. Use `conv_rhs => rw [ht x]`.

Rewrite using `[trace_smul_sum_coeffs_lemma_7, trace_smul_sum_coeffs_lemma_7]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hA k i l]`. Take `⟨f, hf⟩ : ∃ f : V → V, ∀ x l, Algebra.trace ℚ K (h (f x) (u' l)) = Algebra.trace ℚ K (h x (u l)) ∧ ∀ k, Algebra.trace ℚ K (h (ω k • f x) (u' l)) = Algebra.trace ℚ K (h (ω k • x) (u l))` from `⟨fun x => ∑ i, (t x i : K) • u' i, fun x l => ⟨hP x l, fun k => hQ k x l⟩⟩`. Use `⟨{ toFun := f map_add' := fun x y => eq_of_trace_apply_eq_lemma_5 h hpos ι hι u' hu' _ _ (fun l => by` and prove the remaining obligations.

Rewrite using `[classSetAssembly_tr_add_left, (hf (x + y) l).1, (hf x l).1, (hf y l).1, classSetAssembly_tr_add_left])`. Use the proof step `map_smul' := fun a x => eq_of_trace_apply_eq_lemma_5 h hpos ι hι u' hu' _ _ (fun l => by`. Rewrite using `[(hf (a • x) l).1]`. Apply the tactic sequence `try rw [RingHom.id_apply]`. Rewrite using `[trace_smul_left_basis_lemma_8 ω h a x (u l), trace_smul_left_basis_lemma_8 ω h a (f x) (u' l)]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[(hf x l).2 k]) }, fun x l => (hf x l).1⟩`.
-/
private theorem exists_linearMap_of_gram_lemma_9 {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    {κ : Type*} [Fintype κ] (ω : Basis κ ℚ K)
    (u u' : Fin n → V) (hu : LinearIndependent ℝ (ι ∘ u)) (hu' : LinearIndependent ℝ (ι ∘ u'))
    (hG : ∀ i l, Algebra.trace ℚ K (h (u i) (u l)) = Algebra.trace ℚ K (h (u' i) (u' l)))
    (hA : ∀ k i l, Algebra.trace ℚ K (h (ω k • u i) (u l)) =
      Algebra.trace ℚ K (h (ω k • u' i) (u' l))) :
    ∃ φ : V →ₗ[K] V, ∀ x l,
      Algebra.trace ℚ K (h (φ x) (u' l)) = Algebra.trace ℚ K (h x (u l)) := by
  choose t ht using classSetAssembly_span h hpos ι hι u hu
  have hP : ∀ x l, Algebra.trace ℚ K (h (∑ i, (t x i : K) • u' i) (u' l)) =
      Algebra.trace ℚ K (h x (u l)) := by
    intro x l
    conv_rhs => rw [ht x]
    rw [trace_sum_coeffs_lemma_6, trace_sum_coeffs_lemma_6]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hG i l]
  have hQ : ∀ (k : κ) x l, Algebra.trace ℚ K (h (ω k • ∑ i, (t x i : K) • u' i) (u' l)) =
      Algebra.trace ℚ K (h (ω k • x) (u l)) := by
    intro k x l
    conv_rhs => rw [ht x]
    rw [trace_smul_sum_coeffs_lemma_7, trace_smul_sum_coeffs_lemma_7]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hA k i l]
  obtain ⟨f, hf⟩ : ∃ f : V → V, ∀ x l,
      Algebra.trace ℚ K (h (f x) (u' l)) = Algebra.trace ℚ K (h x (u l)) ∧
      ∀ k, Algebra.trace ℚ K (h (ω k • f x) (u' l)) = Algebra.trace ℚ K (h (ω k • x) (u l)) :=
    ⟨fun x => ∑ i, (t x i : K) • u' i, fun x l => ⟨hP x l, fun k => hQ k x l⟩⟩
  refine ⟨{ toFun := f
            map_add' := fun x y => eq_of_trace_apply_eq_lemma_5 h hpos ι hι u' hu' _ _ (fun l => by
              rw [classSetAssembly_tr_add_left, (hf (x + y) l).1, (hf x l).1, (hf y l).1,
                classSetAssembly_tr_add_left])
            map_smul' := fun a x => eq_of_trace_apply_eq_lemma_5 h hpos ι hι u' hu' _ _ (fun l => by
              rw [(hf (a • x) l).1]
              try rw [RingHom.id_apply]
              rw [trace_smul_left_basis_lemma_8 ω h a x (u l), trace_smul_left_basis_lemma_8 ω h a (f x) (u' l)]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [(hf x l).2 k]) }, fun x l => (hf x l).1⟩

/- English proof (translation)
Take `⟨φ, hφ⟩` from `exists_linearMap_of_gram_lemma_9 h hpos ι hι ω u u' hu hu' hG hA`. Take `⟨ψ, hψ⟩` from `exists_linearMap_of_gram_lemma_9 h hpos ι hι ω u' u hu' hu (fun i l => (hG i l).symm) (fun k i l => (hA k i l).symm)`. Establish `h1 : ∀ y, φ (ψ y) = y` using `fun y => eq_of_trace_apply_eq_lemma_5 h hpos ι hι u' hu' _ _ (fun l => by rw [hφ, hψ])`. Establish `h2 : ∀ x, ψ (φ x) = x` using `fun x => eq_of_trace_apply_eq_lemma_5 h hpos ι hι u hu _ _ (fun l => by rw [hψ, hφ])`. Establish `hφu : ∀ i, φ (u i) = u' i` using `fun i => eq_of_trace_apply_eq_lemma_5 h hpos ι hι u' hu' _ _ (fun l => by rw [hφ, hG i l])`.

Use `⟨LinearEquiv.ofLinear φ ψ (LinearMap.ext h1) (LinearMap.ext h2), ?_, hφu⟩` and prove the remaining obligations. Introduce `x y`. Use `show Algebra.trace ℚ K (h (φ x) (φ y)) = Algebra.trace ℚ K (h x y)`. Take `⟨s, hs⟩` from `classSetAssembly_span h hpos ι hι u hu y`. Establish `hφy : φ y = ∑ j, (s j : K) • u' j`.

Rewrite using `[hs, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hφu j]`. Rewrite using `[hφy, hs, classSetAssembly_tr_sum_right, classSetAssembly_tr_sum_right]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[classSetAssembly_tr_qsmul_right, classSetAssembly_tr_qsmul_right, hφ]`.
-/
theorem classSetAssembly_exists_isom {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    {κ : Type*} [Fintype κ] (ω : Basis κ ℚ K)
    (u u' : Fin n → V) (hu : LinearIndependent ℝ (ι ∘ u)) (hu' : LinearIndependent ℝ (ι ∘ u'))
    (hG : ∀ i l, Algebra.trace ℚ K (h (u i) (u l)) = Algebra.trace ℚ K (h (u' i) (u' l)))
    (hA : ∀ k i l, Algebra.trace ℚ K (h (ω k • u i) (u l)) =
      Algebra.trace ℚ K (h (ω k • u' i) (u' l))) :
    ∃ φ : V ≃ₗ[K] V, (∀ x y, Algebra.trace ℚ K (h (φ x) (φ y)) = Algebra.trace ℚ K (h x y)) ∧
      ∀ i, φ (u i) = u' i := by
  obtain ⟨φ, hφ⟩ := exists_linearMap_of_gram_lemma_9 h hpos ι hι ω u u' hu hu' hG hA
  obtain ⟨ψ, hψ⟩ := exists_linearMap_of_gram_lemma_9 h hpos ι hι ω u' u hu' hu
    (fun i l => (hG i l).symm) (fun k i l => (hA k i l).symm)
  have h1 : ∀ y, φ (ψ y) = y := fun y =>
    eq_of_trace_apply_eq_lemma_5 h hpos ι hι u' hu' _ _ (fun l => by rw [hφ, hψ])
  have h2 : ∀ x, ψ (φ x) = x := fun x =>
    eq_of_trace_apply_eq_lemma_5 h hpos ι hι u hu _ _ (fun l => by rw [hψ, hφ])
  have hφu : ∀ i, φ (u i) = u' i := fun i =>
    eq_of_trace_apply_eq_lemma_5 h hpos ι hι u' hu' _ _ (fun l => by rw [hφ, hG i l])
  refine ⟨LinearEquiv.ofLinear φ ψ (LinearMap.ext h1) (LinearMap.ext h2), ?_, hφu⟩
  intro x y
  show Algebra.trace ℚ K (h (φ x) (φ y)) = Algebra.trace ℚ K (h x y)
  obtain ⟨s, hs⟩ := classSetAssembly_span h hpos ι hι u hu y
  have hφy : φ y = ∑ j, (s j : K) • u' j := by
    rw [hs, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hφu j]
  rw [hφy, hs, classSetAssembly_tr_sum_right, classSetAssembly_tr_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [classSetAssembly_tr_qsmul_right, classSetAssembly_tr_qsmul_right, hφ]

end Isom

section Main

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]

/- English proof (translation)
Conclude with `Iff.rfl`.
-/
theorem classSetAssembly_mem_zmap {n : ℕ} (ι : V →+ EuclideanSpace ℝ (Fin n))
    (M : Submodule (NumberField.RingOfIntegers K) V) (v : EuclideanSpace ℝ (Fin n)) :
    v ∈ zmap ι M ↔ ∃ x ∈ M, ι x = v := by
  exact Iff.rfl

/- English proof (translation)
Take `⟨z, hz⟩` from `classSetAssembly_dint h d x x (hdM x hx x hx)`. Establish `hp` using `hpos x hx0`. Establish `hdQ : (0 : ℚ) < d` using `by exact_mod_cast hd`. Establish `hz0 : (0 : ℤ) < z`. Establish `: (0 : ℚ) < z` using `by rw [← hz]; exact mul_pos hdQ hp`.

Conclude with `this` after adjusting the coercions. Establish `hz1 : (1 : ℝ) ≤ z`. Establish `: (1 : ℤ) ≤ z` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `hn : ‖ι x‖ ^ 2 = ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ)`.

Rewrite using `[← real_inner_self_eq_norm_sq, hι]`. Establish `hzR : (d : ℝ) * ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) = (z : ℝ)`. Conclude with `hz` after adjusting the coercions. Establish `hdR : (0 : ℝ) < d` using `by exact_mod_cast hd`. Establish `hdR1 : (1 : ℝ) ≤ d` using `by exact_mod_cast hd`.

Establish `hN` using `norm_nonneg (ι x)`. Establish `key : 1 ≤ (‖ι x‖ * d) ^ 2`. Establish `e : (‖ι x‖ * d) ^ 2 = (z : ℝ) * d`. Rewrite using `[mul_pow, hn, ← hzR]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hNd : 0 ≤ ‖ι x‖ * d` using `mul_nonneg hN hdR.le`. Rewrite using `[div_le_iff₀ hdR]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem classSetAssembly_min {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (d : ℕ) (hd : 0 < d) (M : Submodule (NumberField.RingOfIntegers K) V)
    (hdM : ∀ x ∈ M, ∀ y ∈ M, (d : K) * h x y ∈ (1 : Submodule (NumberField.RingOfIntegers K) K))
    (x : V) (hx : x ∈ M) (hx0 : x ≠ 0) : 1 / (d : ℝ) ≤ ‖ι x‖ := by
  obtain ⟨z, hz⟩ := classSetAssembly_dint h d x x (hdM x hx x hx)
  have hp := hpos x hx0
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  have hz0 : (0 : ℤ) < z := by
    have : (0 : ℚ) < z := by rw [← hz]; exact mul_pos hdQ hp
    exact_mod_cast this
  have hz1 : (1 : ℝ) ≤ z := by
    have : (1 : ℤ) ≤ z := by omega
    exact_mod_cast this
  have hn : ‖ι x‖ ^ 2 = ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) := by
    rw [← real_inner_self_eq_norm_sq, hι]
  have hzR : (d : ℝ) * ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) = (z : ℝ) := by
    exact_mod_cast hz
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdR1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hN := norm_nonneg (ι x)
  have key : 1 ≤ (‖ι x‖ * d) ^ 2 := by
    have e : (‖ι x‖ * d) ^ 2 = (z : ℝ) * d := by
      rw [mul_pow, hn, ← hzR]; ring
    rw [e]
    nlinarith
  have hNd : 0 ≤ ‖ι x‖ * d := mul_nonneg hN hdR.le
  rw [div_le_iff₀ hdR]
  nlinarith

/- English proof (translation)
Consider the cases of `o with`. Consider the case `none => exact ⟨1, (map_one _).symm⟩`. Consider the case `some i`. Conclude with `⟨_, NumberField.integralBasis_apply K i⟩`.
-/
theorem classSetAssembly_w_mem (o : Option (Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K))) :
    ∃ r : NumberField.RingOfIntegers K,
      o.elim (1 : K) (NumberField.integralBasis K) = algebraMap _ K r := by
  cases o with
  | none => exact ⟨1, (map_one _).symm⟩
  | some i =>
    exact ⟨_, NumberField.integralBasis_apply K i⟩

/- English proof (translation)
Unfold `IsomOfTrace at hF`. Use `choose! u humem huli hubd using hgood`. Establish `hωmem : ∀ M : Submodule (NumberField.RingOfIntegers K) V, ∀ k x, x ∈ M → NumberField.integralBasis K k • x ∈ M`. Introduce `M k x hx`. Take `⟨r, hr⟩` from `classSetAssembly_w_mem (K := K) (some k)`.

Establish `hr' : NumberField.integralBasis K k = algebraMap (NumberField.RingOfIntegers K) K r` using `hr`. Rewrite using `[hr', algebraMap_smul]`. Conclude with `M.smul_mem r hx`. Take `⟨C, hC⟩ : ∃ C : Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) → ℝ, ∀ k x, ‖ι (NumberField.integralBasis K k • x)‖ ≤ C k * ‖ι x‖` from `⟨fun k => (hmul (NumberField.integralBasis K k)).choose, fun k => (hmul (NumberField.integralBasis K k)).choose_spec⟩`. Choose the witnesses or unpack the hypotheses as in `⟨R, hR1, hR2⟩ : ∃ R : ℝ, B * B ≤ R ∧ ∀ k, |C k| * B * B ≤ R := by`.

Establish `hs : 0 ≤ ∑ k, |C k|` using `Finset.sum_nonneg fun k _ => abs_nonneg (C k)`. Use `⟨B * B * (1 + ∑ k, |C k|), ?_, fun k => ?_⟩` and prove the remaining obligations. Conclude with `le_mul_of_one_le_right (mul_self_nonneg B) (by linarith)`. Establish `hk : |C k| ≤ 1 + ∑ k, |C k|`. Use `Finset.single_le_sum (fun k _ => abs_nonneg (C k)) (Finset.mem_univ k)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Establish `hT` using `classSetAssembly_finite_rat d hd R`. Establish `hbound : ∀ M ∈ S, ∀ x y : V, x ∈ M → y ∈ M → ∀ c : ℝ, ‖ι x‖ ≤ c → ‖ι y‖ ≤ B → c * B ≤ R → Algebra.trace ℚ K (h x y) ∈ {q : ℚ | (∃ z : ℤ, (d : ℚ) * q = z) ∧ |(q : ℝ)| ≤ R}`. Introduce `M hM x y hx hy c hc hyB hcR`.

Use `⟨classSetAssembly_dint h d x y (hdM M hM x hx y hy), ?_⟩` and prove the remaining obligations. Rewrite using `[← hι]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨D, hD⟩ : ∃ D : Submodule (NumberField.RingOfIntegers K) V → (Fin n → Fin n → ℚ) × (Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) → Fin n → Fin n → ℚ), ∀ M, D M = (fun i l => Algebra.trace ℚ K (h (u M i) (u M l)), fun k i l => Algebra.trace ℚ K (h (NumberField.integralBa …` from `⟨_, fun _ => rfl⟩`. Establish `hDfin : (D '' S).Finite`.

Use `((Set.Finite.pi fun i => Set.Finite.pi fun l => hT).prod (Set.Finite.pi fun k => Set.Finite.pi fun i => Set.Finite.pi fun l => hT)).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨M, hM, rfl⟩`. Rewrite using `[hD]`. Use `Set.mem_prod.mpr ⟨Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun l => ?_, Set.mem_univ_pi.mpr fun k => Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun l => ?_⟩` and prove the remaining obligations. Conclude with `hbound M hM _ _ (humem M hM i) (humem M hM l) B (hubd M hM i) (hubd M hM l) hR1`.

Use `hbound M hM _ _ (hωmem M k _ (humem M hM i)) (humem M hM l) (|C k| * B) ?_ (hubd M hM l) (hR2 k)` and prove the remaining obligations. Conclude with `(hC k _).trans (mul_le_mul (le_abs_self _) (hubd M hM i) (norm_nonneg _) (abs_nonneg _))`. Establish `hEprop : ∀ M ∈ S, ∃ e : ℤ, e ≠ 0 ∧ ∀ x : V, (∀ j, ∃ z : ℤ, (d : ℚ) * Algebra.trace ℚ K (h x (u M j)) = z) → x ∈ AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u M i)`. Introduce `M hM`. Take `⟨e, he, hx⟩` from `classSetAssembly_denom h hpos ι hι (u M) (huli M hM) d hd (fun i j => classSetAssembly_dint h d (u M i) (u M j) (hdM M hM _ (humem M hM i) _ (humem M hM j)))`.

Conclude with `⟨e, he, fun x hxj => classSetAssembly_le_Q (K := K) (u M) e he x (hx x hxj)⟩`. Use `choose! e he hemem using hEprop`. Establish `hφex : ∀ M : Submodule (NumberField.RingOfIntegers K) V, ∃ φ : V ≃ₗ[K] V, M ∈ S → (∀ x y, Algebra.trace ℚ K (h (φ x) (φ y)) = Algebra.trace ℚ K (h x y)) ∧ ∀ i, φ (u (Function.invFunOn D S (D M)) i) = u M i`. Introduce `M`. Distinguish the cases in `hM : M ∈ S`.

Take `⟨hRS, hRD⟩ : Function.invFunOn D S (D M) ∈ S ∧ D (Function.invFunOn D S (D M)) = D M` from `Function.invFunOn_pos ⟨M, hM, rfl⟩`. Generalize the expression as in `Function.invFunOn D S (D M) = M₀ at hRS hRD ⊢`. Establish `h1` using `congrArg Prod.fst hRD`. Establish `h2` using `congrArg Prod.snd hRD`. Rewrite `h1`, `h2` using `[hD M₀, hD M]`.

Take `⟨φ, h3, h4⟩` from `classSetAssembly_exists_isom h hpos ι hι (NumberField.integralBasis K) (u M₀) (u M) (huli M₀ hRS) (huli M hM) (fun i l => congrFun (congrFun h1 i) l) (fun k i l => congrFun (congrFun (congrFun h2 k) i) l)`. Conclude with `⟨φ, fun _ => ⟨h3, h4⟩⟩`. Conclude with `⟨LinearEquiv.refl K V, fun h' => absurd h' hM⟩`. Use `choose φ hφ using hφex`. Take `⟨Key, hKey⟩ : ∃ Key : Submodule (NumberField.RingOfIntegers K) V → ((Fin n → Fin n → ℚ) × (Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) → Fin n → Fin n → ℚ)) × AddSubgroup V, ∀ M, Key M = (D M, M.toAddSubgroup.comap (φ M).toLinearMap.toAddMonoidHom)` from `⟨_, fun _ => rfl⟩`.

Establish `hKfin : (Key '' S).Finite`. Use `(Set.Finite.biUnion hDfin fun δ hδ => ((classSetAssembly_finite_between (K := K) hE (u (Function.invFunOn D S δ)) (e (Function.invFunOn D S δ)) (he _ (Function.invFunOn_pos hδ).1)).image (Prod.mk δ))).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨M, hM, rfl⟩`. Rewrite using `[Set.mem_iUnion₂]`. Use `⟨D M, ⟨M, hM, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hKey]`. Establish `hRS : Function.invFunOn D S (D M) ∈ S` using `(Function.invFunOn_pos ⟨M, hM, rfl⟩).1`. Use `⟨_, ⟨?_, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Rewrite using `[SetLike.mem_coe, AddSubgroup.mem_comap]`. Use `show φ M (u (Function.invFunOn D S (D M)) i) ∈ M`. Rewrite using `[(hφ M hM).2 i]`. Conclude with `humem M hM i`. Introduce `x hx`.

Establish `hx' : φ M x ∈ M` using `hx`. Use `hemem _ hRS x (fun j => ?_)` and prove the remaining obligations. Rewrite using `[← (hφ M hM).1 x, (hφ M hM).2 j]`. Conclude with `classSetAssembly_dint h d _ _ (hdM M hM _ hx' _ (humem M hM j))`. Use `⟨hKfin.toFinset.image (Function.invFunOn Key S), ?_, ?_⟩` and prove the remaining obligations.

Introduce `N hN`. Take `⟨y, hy, rfl⟩` from `Finset.mem_image.mp hN`. Conclude with `(Function.invFunOn_pos (hKfin.mem_toFinset.mp hy)).1`. Introduce `M hM`. Establish `hy : Key M ∈ Key '' S` using `⟨M, hM, rfl⟩`.

Take `⟨hNS, hNK⟩` from `Function.invFunOn_pos hy`. Use `⟨Function.invFunOn Key S (Key M), Finset.mem_image.mpr ⟨Key M, hKfin.mem_toFinset.mpr hy, rfl⟩, ?_⟩` and prove the remaining obligations. Generalize the expression as in `Function.invFunOn Key S (Key M) = N at hNS hNK ⊢`. Rewrite `hNK` using `[hKey N, hKey M]`. Establish `hCN : N.toAddSubgroup.comap (φ N).toLinearMap.toAddMonoidHom = M.toAddSubgroup.comap (φ M).toLinearMap.toAddMonoidHom` using `congrArg Prod.snd hNK`.

Use `⟨(φ N).symm.trans (φ M), ?_, ?_⟩` and prove the remaining obligations. Apply `hF K V h` to reduce the goal to its premises. Introduce `x y`. Use `show Algebra.trace ℚ K (h (φ M ((φ N).symm x)) (φ M ((φ N).symm y))) = Algebra.trace ℚ K (h x y)`. Rewrite using `[(hφ M hM).1]`.

Establish `h5` using `(hφ N hNS).1 ((φ N).symm x) ((φ N).symm y)`. Rewrite `h5` using `[LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`. Conclude with `h5.symm`. Use extensionality with `x`. Rewrite using `[isomAct_mem_gmap]`.

Establish `hc : (φ M).symm x ∈ N.toAddSubgroup.comap (φ N).toLinearMap.toAddMonoidHom ↔ (φ M).symm x ∈ M.toAddSubgroup.comap (φ M).toLinearMap.toAddMonoidHom`. Rewrite using `[hCN]`. Express the relevant statement in the definitionally equal form `φ N ((φ M).symm x) ∈ N ↔ φ M ((φ M).symm x) ∈ M at hc`. Rewrite `hc` using `[LinearEquiv.apply_symm_apply]`. Conclude with `hc`.
-/
theorem classSetAssembly_main (hE : FinIntermediate) (hF : IsomOfTrace)
    (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    {n : ℕ} (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (hmul : ∀ a : K, ∃ C : ℝ, ∀ x : V, ‖ι (a • x)‖ ≤ C * ‖ι x‖)
    (d : ℕ) (hd : 0 < d) (S : Set (Submodule (NumberField.RingOfIntegers K) V))
    (hdM : ∀ M ∈ S, ∀ x ∈ M, ∀ y ∈ M,
      (d : K) * h x y ∈ (1 : Submodule (NumberField.RingOfIntegers K) K))
    (B : ℝ)
    (hgood : ∀ M ∈ S, ∃ u : Fin n → V, (∀ i, u i ∈ M) ∧ LinearIndependent ℝ (ι ∘ u) ∧
      ∀ i, ‖ι (u i)‖ ≤ B) :
    ∃ s : Finset (Submodule (NumberField.RingOfIntegers K) V), (∀ M ∈ s, M ∈ S) ∧
      ∀ M ∈ S, ∃ N ∈ s, ∃ g ∈ isom h, gmap g N = M := by
  classical
  unfold IsomOfTrace at hF
  choose! u humem huli hubd using hgood
  have hωmem : ∀ M : Submodule (NumberField.RingOfIntegers K) V, ∀ k x, x ∈ M →
      NumberField.integralBasis K k • x ∈ M := by
    intro M k x hx
    obtain ⟨r, hr⟩ := classSetAssembly_w_mem (K := K) (some k)
    have hr' : NumberField.integralBasis K k = algebraMap (NumberField.RingOfIntegers K) K r := hr
    rw [hr', algebraMap_smul]
    exact M.smul_mem r hx
  obtain ⟨C, hC⟩ : ∃ C : Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) → ℝ,
      ∀ k x, ‖ι (NumberField.integralBasis K k • x)‖ ≤ C k * ‖ι x‖ :=
    ⟨fun k => (hmul (NumberField.integralBasis K k)).choose,
      fun k => (hmul (NumberField.integralBasis K k)).choose_spec⟩
  obtain ⟨R, hR1, hR2⟩ : ∃ R : ℝ, B * B ≤ R ∧ ∀ k, |C k| * B * B ≤ R := by
    have hs : 0 ≤ ∑ k, |C k| := Finset.sum_nonneg fun k _ => abs_nonneg (C k)
    refine ⟨B * B * (1 + ∑ k, |C k|), ?_, fun k => ?_⟩
    · exact le_mul_of_one_le_right (mul_self_nonneg B) (by linarith)
    · have hk : |C k| ≤ 1 + ∑ k, |C k| := by
        have := Finset.single_le_sum (fun k _ => abs_nonneg (C k)) (Finset.mem_univ k)
        linarith
      calc |C k| * B * B = B * B * |C k| := by ring
        _ ≤ B * B * (1 + ∑ k, |C k|) := mul_le_mul_of_nonneg_left hk (mul_self_nonneg B)
  have hT := classSetAssembly_finite_rat d hd R
  have hbound : ∀ M ∈ S, ∀ x y : V, x ∈ M → y ∈ M → ∀ c : ℝ, ‖ι x‖ ≤ c → ‖ι y‖ ≤ B →
      c * B ≤ R → Algebra.trace ℚ K (h x y) ∈
        {q : ℚ | (∃ z : ℤ, (d : ℚ) * q = z) ∧ |(q : ℝ)| ≤ R} := by
    intro M hM x y hx hy c hc hyB hcR
    refine ⟨classSetAssembly_dint h d x y (hdM M hM x hx y hy), ?_⟩
    rw [← hι]
    calc |inner ℝ (ι x) (ι y)| ≤ ‖ι x‖ * ‖ι y‖ := abs_real_inner_le_norm _ _
      _ ≤ c * B := mul_le_mul hc hyB (norm_nonneg _) ((norm_nonneg _).trans hc)
      _ ≤ R := hcR
  obtain ⟨D, hD⟩ : ∃ D : Submodule (NumberField.RingOfIntegers K) V →
      (Fin n → Fin n → ℚ) × (Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) → Fin n → Fin n → ℚ),
      ∀ M, D M = (fun i l => Algebra.trace ℚ K (h (u M i) (u M l)),
        fun k i l => Algebra.trace ℚ K (h (NumberField.integralBasis K k • u M i) (u M l))) :=
    ⟨_, fun _ => rfl⟩
  have hDfin : (D '' S).Finite := by
    refine ((Set.Finite.pi fun i => Set.Finite.pi fun l => hT).prod
      (Set.Finite.pi fun k => Set.Finite.pi fun i => Set.Finite.pi fun l => hT)).subset ?_
    rintro _ ⟨M, hM, rfl⟩
    rw [hD]
    refine Set.mem_prod.mpr ⟨Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun l => ?_,
      Set.mem_univ_pi.mpr fun k => Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun l => ?_⟩
    · exact hbound M hM _ _ (humem M hM i) (humem M hM l) B (hubd M hM i) (hubd M hM l) hR1
    · refine hbound M hM _ _ (hωmem M k _ (humem M hM i)) (humem M hM l) (|C k| * B) ?_
        (hubd M hM l) (hR2 k)
      exact (hC k _).trans (mul_le_mul (le_abs_self _) (hubd M hM i) (norm_nonneg _) (abs_nonneg _))
  have hEprop : ∀ M ∈ S, ∃ e : ℤ, e ≠ 0 ∧ ∀ x : V,
      (∀ j, ∃ z : ℤ, (d : ℚ) * Algebra.trace ℚ K (h x (u M j)) = z) →
      x ∈ AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u M i) := by
    intro M hM
    obtain ⟨e, he, hx⟩ := classSetAssembly_denom h hpos ι hι (u M) (huli M hM) d hd
      (fun i j => classSetAssembly_dint h d (u M i) (u M j)
        (hdM M hM _ (humem M hM i) _ (humem M hM j)))
    exact ⟨e, he, fun x hxj => classSetAssembly_le_Q (K := K) (u M) e he x (hx x hxj)⟩
  choose! e he hemem using hEprop
  have hφex : ∀ M : Submodule (NumberField.RingOfIntegers K) V, ∃ φ : V ≃ₗ[K] V, M ∈ S →
      (∀ x y, Algebra.trace ℚ K (h (φ x) (φ y)) = Algebra.trace ℚ K (h x y)) ∧
      ∀ i, φ (u (Function.invFunOn D S (D M)) i) = u M i := by
    intro M
    by_cases hM : M ∈ S
    · obtain ⟨hRS, hRD⟩ : Function.invFunOn D S (D M) ∈ S ∧
          D (Function.invFunOn D S (D M)) = D M := Function.invFunOn_pos ⟨M, hM, rfl⟩
      generalize Function.invFunOn D S (D M) = M₀ at hRS hRD ⊢
      have h1 := congrArg Prod.fst hRD
      have h2 := congrArg Prod.snd hRD
      rw [hD M₀, hD M] at h1 h2
      obtain ⟨φ, h3, h4⟩ := classSetAssembly_exists_isom h hpos ι hι
        (NumberField.integralBasis K) (u M₀) (u M) (huli M₀ hRS) (huli M hM)
        (fun i l => congrFun (congrFun h1 i) l)
        (fun k i l => congrFun (congrFun (congrFun h2 k) i) l)
      exact ⟨φ, fun _ => ⟨h3, h4⟩⟩
    · exact ⟨LinearEquiv.refl K V, fun h' => absurd h' hM⟩
  choose φ hφ using hφex
  obtain ⟨Key, hKey⟩ : ∃ Key : Submodule (NumberField.RingOfIntegers K) V →
      ((Fin n → Fin n → ℚ) × (Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) → Fin n → Fin n → ℚ)) ×
        AddSubgroup V,
      ∀ M, Key M = (D M, M.toAddSubgroup.comap (φ M).toLinearMap.toAddMonoidHom) :=
    ⟨_, fun _ => rfl⟩
  have hKfin : (Key '' S).Finite := by
    refine (Set.Finite.biUnion hDfin fun δ hδ =>
      ((classSetAssembly_finite_between (K := K) hE (u (Function.invFunOn D S δ))
        (e (Function.invFunOn D S δ)) (he _ (Function.invFunOn_pos hδ).1)).image
          (Prod.mk δ))).subset ?_
    rintro _ ⟨M, hM, rfl⟩
    rw [Set.mem_iUnion₂]
    refine ⟨D M, ⟨M, hM, rfl⟩, ?_⟩
    rw [hKey]
    have hRS : Function.invFunOn D S (D M) ∈ S := (Function.invFunOn_pos ⟨M, hM, rfl⟩).1
    refine ⟨_, ⟨?_, ?_⟩, rfl⟩
    · rw [AddSubgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, AddSubgroup.mem_comap]
      show φ M (u (Function.invFunOn D S (D M)) i) ∈ M
      rw [(hφ M hM).2 i]
      exact humem M hM i
    · intro x hx
      have hx' : φ M x ∈ M := hx
      refine hemem _ hRS x (fun j => ?_)
      rw [← (hφ M hM).1 x, (hφ M hM).2 j]
      exact classSetAssembly_dint h d _ _ (hdM M hM _ hx' _ (humem M hM j))
  refine ⟨hKfin.toFinset.image (Function.invFunOn Key S), ?_, ?_⟩
  · intro N hN
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hN
    exact (Function.invFunOn_pos (hKfin.mem_toFinset.mp hy)).1
  · intro M hM
    have hy : Key M ∈ Key '' S := ⟨M, hM, rfl⟩
    obtain ⟨hNS, hNK⟩ := Function.invFunOn_pos hy
    refine ⟨Function.invFunOn Key S (Key M),
      Finset.mem_image.mpr ⟨Key M, hKfin.mem_toFinset.mpr hy, rfl⟩, ?_⟩
    generalize Function.invFunOn Key S (Key M) = N at hNS hNK ⊢
    rw [hKey N, hKey M] at hNK
    have hCN : N.toAddSubgroup.comap (φ N).toLinearMap.toAddMonoidHom =
        M.toAddSubgroup.comap (φ M).toLinearMap.toAddMonoidHom := congrArg Prod.snd hNK
    refine ⟨(φ N).symm.trans (φ M), ?_, ?_⟩
    · apply hF K V h
      intro x y
      show Algebra.trace ℚ K (h (φ M ((φ N).symm x)) (φ M ((φ N).symm y))) =
        Algebra.trace ℚ K (h x y)
      rw [(hφ M hM).1]
      have h5 := (hφ N hNS).1 ((φ N).symm x) ((φ N).symm y)
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h5
      exact h5.symm
    · ext x
      rw [isomAct_mem_gmap]
      have hc : (φ M).symm x ∈ N.toAddSubgroup.comap (φ N).toLinearMap.toAddMonoidHom ↔
          (φ M).symm x ∈ M.toAddSubgroup.comap (φ M).toLinearMap.toAddMonoidHom := by
        rw [hCN]
      change φ N ((φ M).symm x) ∈ N ↔ φ M ((φ M).symm x) ∈ M at hc
      rw [LinearEquiv.apply_symm_apply] at hc
      exact hc

end Main

/- English proof (translation)
Unfold `ShortVectors at hC`. Establish `hdR : (0 : ℝ) < 1 / (d : ℝ)` using `one_div_pos.mpr (by exact_mod_cast hd)`. Take `⟨B, hB⟩` from `hC n (1 / (d : ℝ)) C hdR`. Use `classSetAssembly_main hE hF h hpos ι hι hmul d hd S hSd B ?_` and prove the remaining obligations. Introduce `M hM`.

Take `⟨hdisc, hlat⟩` from `hSlat M hM`. Use `hdisc` as an intermediate fact. Use `hlat` as an intermediate fact. Take `⟨v, hvmem, hvli, hvB⟩` from `hB (zmap ι M) (fun w hw hw0 => by`. Take `⟨x, hx, rfl⟩` from `(classSetAssembly_mem_zmap ι M w).mp hw`.

Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Conclude with `hw0 (map_zero ι)`. Conclude with `classSetAssembly_min h hpos ι hι d hd M (hSd M hM) x hx hx0)`. Use the proof step `(hSC M hM)`.

Use `choose x hx using fun i => (classSetAssembly_mem_zmap ι M (v i)).mp (hvmem i)`. Establish `hxv : ι ∘ x = v` using `funext fun i => (hx i).2`. Use `⟨x, fun i => (hx i).1, ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hxv]`. Conclude with `hvli`.

Rewrite using `[(hx i).2]`. Conclude with `hvB i`.
-/
theorem classSetFinite_core (hC : ShortVectors) (hE : FinIntermediate) (hF : IsomOfTrace)
    {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (n : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (hmul : ∀ a : K, ∃ C : ℝ, ∀ x : V, ‖ι (a • x)‖ ≤ C * ‖ι x‖)
    (d : ℕ) (hd : 0 < d) (C : ℝ) (S : Set (Submodule (NumberField.RingOfIntegers K) V))
    (hSd : ∀ M ∈ S, ∀ x ∈ M, ∀ y ∈ M,
      (d : K) * h x y ∈ (1 : Submodule (NumberField.RingOfIntegers K) K))
    (hSlat : ∀ M ∈ S, ∃ _ : DiscreteTopology (zmap ι M), IsZLattice ℝ (zmap ι M))
    (hSC : ∀ M ∈ S, ∀ [DiscreteTopology (zmap ι M)] [IsZLattice ℝ (zmap ι M)],
      ZLattice.covolume (zmap ι M) ≤ C) :
    ∃ s : Finset (Submodule (NumberField.RingOfIntegers K) V), (∀ N ∈ s, N ∈ S) ∧
      ∀ M ∈ S, ∃ N ∈ s, ∃ g ∈ isom h, gmap g N = M := by
  unfold ShortVectors at hC
  have hdR : (0 : ℝ) < 1 / (d : ℝ) := one_div_pos.mpr (by exact_mod_cast hd)
  obtain ⟨B, hB⟩ := hC n (1 / (d : ℝ)) C hdR
  refine classSetAssembly_main hE hF h hpos ι hι hmul d hd S hSd B ?_
  intro M hM
  obtain ⟨hdisc, hlat⟩ := hSlat M hM
  have := hdisc
  have := hlat
  obtain ⟨v, hvmem, hvli, hvB⟩ := hB (zmap ι M) (fun w hw hw0 => by
      obtain ⟨x, hx, rfl⟩ := (classSetAssembly_mem_zmap ι M w).mp hw
      have hx0 : x ≠ 0 := by
        rintro rfl
        exact hw0 (map_zero ι)
      exact classSetAssembly_min h hpos ι hι d hd M (hSd M hM) x hx hx0)
    (hSC M hM)
  choose x hx using fun i => (classSetAssembly_mem_zmap ι M (v i)).mp (hvmem i)
  have hxv : ι ∘ x = v := funext fun i => (hx i).2
  refine ⟨x, fun i => (hx i).1, ?_, fun i => ?_⟩
  · rw [hxv]
    exact hvli
  · rw [(hx i).2]
    exact hvB i

/- English proof (translation)
Unfold `ClassSetFinite`. Unfold `TraceReal at hA`. Unfold `GenusCovolBound at hB`. Unfold `GenusScale at hD`. Introduce `K V _ _ _ _ _ _ _ _ h hsymm hpos L hL`.

Take `⟨N, ι, hι, hmul, hlat⟩` from `hA K V h hsymm hpos`. Take `⟨C, hCb⟩` from `hB K V h hsymm hpos N ι hι L hL`. Take `⟨d, hd, hdM⟩` from `hD K V h hsymm L hL`. Conclude with `classSetFinite_core hC hE hF h hpos N ι hι hmul d hd C (genus h L) hdM (fun M hM => hlat M hM.1) hCb`.
-/
theorem classSetFinite_of (hA : TraceReal) (hB : GenusCovolBound) (hC : ShortVectors)
    (hD : GenusScale) (hE : FinIntermediate) (hF : IsomOfTrace) : ClassSetFinite := by
  unfold ClassSetFinite
  unfold TraceReal at hA
  unfold GenusCovolBound at hB
  unfold GenusScale at hD
  intro K V _ _ _ _ _ _ _ _ h hsymm hpos L hL
  obtain ⟨N, ι, hι, hmul, hlat⟩ := hA K V h hsymm hpos
  obtain ⟨C, hCb⟩ := hB K V h hsymm hpos N ι hι L hL
  obtain ⟨d, hd, hdM⟩ := hD K V h hsymm L hL
  exact classSetFinite_core hC hE hF h hpos N ι hι hmul d hd C
    (genus h L) hdM (fun M hM => hlat M hM.1) hCb

end Formalism.HermitianLatticesTheory
