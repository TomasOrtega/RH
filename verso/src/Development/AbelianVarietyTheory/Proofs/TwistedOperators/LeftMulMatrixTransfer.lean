import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PlusPolynomialInclusion

noncomputable section

open Polynomial TensorProduct Matrix Formalism.UG

namespace GlobalTheory.ClassParam

section Cyclic

/- English proof (translation)
Distinguish the cases in `h0 : q = 0`. Simplify using `[h0]`. Set `Ω` to `AlgebraicClosure K`. Set `f` to `algebraMap K Ω`. Rewrite using `[← Polynomial.map_dvd_map' f]`.

Establish `hq0 : q.map f ≠ 0` using `Polynomial.map_ne_zero h0`. Use `(IsAlgClosed.splits _).dvd_of_roots_le_roots (Polynomial.map_ne_zero g.charpoly_monic.ne_zero) ?_` and prove the remaining obligations. Rewrite using `[Multiset.le_iff_subset (nodup_roots hs.map)]`. Introduce `μ hμ`. Rewrite using `[mem_roots hq0]`.

Establish `h1 : μ ∈ spectrum Ω (g.map f)`. Rewrite using `[Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_map]`. Conclude with `isRoot_of_mem_roots hμ`. Establish `h2` using `spectrum.subset_polynomial_aeval (g.map f) (q.map f) ⟨μ, h1, rfl⟩`. Establish `h3 : aeval (g.map f) (q.map f) = 0`.

Rewrite using `[aeval_map_algebraMap]`. Use `congrArg (AlgHom.mapMatrix (m := Fin r) (Algebra.ofId K Ω)) hq` as an intermediate fact. Rewrite `this` using `[← aeval_algHom_apply, map_zero]`. Conclude with `this`. Rewrite `h2` using `[h3]`.

Assume the negation of the conclusion as `hne`. Conclude with `(spectrum.mem_iff.1 h2) (by simpa using (IsUnit.mk0 _ hne).map (algebraMap Ω (Matrix (Fin r) (Fin r) Ω)))`.
-/
theorem charpoly_dvd_of_aeval {K : Type} [Field K] {r : ℕ} (g : Matrix (Fin r) (Fin r) K)
    (hs : g.charpoly.Separable) (q : K[X]) (hq : aeval g q = 0) : g.charpoly ∣ q := by
  classical
  by_cases h0 : q = 0
  · simp [h0]
  let Ω := AlgebraicClosure K
  let f := algebraMap K Ω
  rw [← Polynomial.map_dvd_map' f]
  have hq0 : q.map f ≠ 0 := Polynomial.map_ne_zero h0
  refine (IsAlgClosed.splits _).dvd_of_roots_le_roots (Polynomial.map_ne_zero g.charpoly_monic.ne_zero) ?_
  rw [Multiset.le_iff_subset (nodup_roots hs.map)]
  intro μ hμ
  rw [mem_roots hq0]
  have h1 : μ ∈ spectrum Ω (g.map f) := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_map]
    exact isRoot_of_mem_roots hμ
  have h2 := spectrum.subset_polynomial_aeval (g.map f) (q.map f) ⟨μ, h1, rfl⟩
  have h3 : aeval (g.map f) (q.map f) = 0 := by
    rw [aeval_map_algebraMap]
    have := congrArg (AlgHom.mapMatrix (m := Fin r) (Algebra.ofId K Ω)) hq
    rw [← aeval_algHom_apply, map_zero] at this
    exact this
  rw [h3] at h2
  by_contra hne
  exact (spectrum.mem_iff.1 h2) (by simpa using (IsUnit.mk0 _ hne).map (algebraMap Ω (Matrix (Fin r) (Fin r) Ω)))

def krylov {A : Type} [CommRing A] {r : ℕ} (g : Matrix (Fin r) (Fin r) A) (v : Fin r → A) :
    Matrix (Fin r) (Fin r) A := Matrix.of fun i j => ((g ^ (j : ℕ)) *ᵥ v) i

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [krylov, Matrix.map_apply, Matrix.of_apply]`. Rewrite using `[RingHom.map_mulVec, Matrix.map_pow]`.
-/
theorem krylov_map {A B : Type} [CommRing A] [CommRing B] {r : ℕ} (f : A →+* B)
    (g : Matrix (Fin r) (Fin r) A) (v : Fin r → A) :
    (krylov g v).map f = krylov (g.map f) (f ∘ v) := by
  ext i j
  simp only [krylov, Matrix.map_apply, Matrix.of_apply]
  rw [RingHom.map_mulVec, Matrix.map_pow]

/- English proof (translation)
Take `⟨x, hx⟩` from `Module.exists_ker_toSpanSingleton_eq_annihilator K[X] (Module.AEval' (Matrix.toLin' g))`. Use `⟨(Module.AEval'.of (Matrix.toLin' g)).symm x, fun h => ?_⟩` and prove the remaining obligations. Take `⟨w, hw0, hw⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h`. Use `set v := (Module.AEval'.of (Matrix.toLin' g)).symm x with hv`. Set `q : K[X]` to `∑ j : Fin r, monomial (j : ℕ) (w j)`.

Establish `ha : ∀ p : K[X], aeval (Matrix.toLin' g) p = Matrix.toLin' (aeval g p)` using `fun p => (aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := K) (n := Fin r)) g p)`. Establish `hqv : aeval g q *ᵥ v = 0`. Rewrite using `[← hw]`. Use extensionality with `i`. Simplify using `[q, krylov, map_sum, aeval_monomial, Matrix.sum_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.mulVec.eq_def (Matrix.of _), dotProduct, mul_comm]`.

Establish `hmem : q ∈ Module.annihilator K[X] (Module.AEval' (Matrix.toLin' g))`. Rewrite using `[← hx, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]`. Apply `(Module.AEval'.of (Matrix.toLin' g)).symm.injective` to reduce the goal to its premises. Rewrite using `[Module.AEval.of_symm_smul, map_zero, ha]`. Conclude with `hqv`.

Establish `hq : aeval g q = 0`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Rewrite using `[map_zero, ← ha]`. Use `LinearMap.ext fun u => ?_` and prove the remaining obligations. Use `Module.mem_annihilator.1 hmem (Module.AEval'.of (Matrix.toLin' g) u)` as an intermediate fact.

Establish `h2` using `congrArg (Module.AEval'.of (Matrix.toLin' g)).symm this`. Rewrite `h2` using `[Module.AEval.of_symm_smul, map_zero]`. Simplify using `using h2`. Establish `hd` using `charpoly_dvd_of_aeval g hs q hq`. Establish `hdeg : q.degree < g.charpoly.degree`.

Rewrite using `[Matrix.charpoly_degree_eq_dim, Fintype.card_fin]`. Use `lt_of_le_of_lt (degree_sum_le _ _) ?_` and prove the remaining obligations. Use `(Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j _ => lt_of_le_of_lt (degree_monomial_le _ _) ?_` and prove the remaining obligations. Conclude with `j.2` after adjusting the coercions. Establish `hq0` using `eq_zero_of_dvd_of_degree_lt hd hdeg`.

Apply `hw0` to reduce the goal to its premises. Use extensionality with `j`. Use `congrArg (fun p => p.coeff j) hq0` as an intermediate fact. Simplify `this` using `[q, finset_sum_coeff, coeff_monomial, Fin.val_inj]`.
-/
theorem exists_cyclic_field {K : Type} [Field K] {r : ℕ} (g : Matrix (Fin r) (Fin r) K)
    (hs : g.charpoly.Separable) : ∃ v, (krylov g v).det ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator K[X]
    (Module.AEval' (Matrix.toLin' g))
  refine ⟨(Module.AEval'.of (Matrix.toLin' g)).symm x, fun h => ?_⟩
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  set v := (Module.AEval'.of (Matrix.toLin' g)).symm x with hv
  let q : K[X] := ∑ j : Fin r, monomial (j : ℕ) (w j)
  have ha : ∀ p : K[X], aeval (Matrix.toLin' g) p = Matrix.toLin' (aeval g p) := fun p =>
    (aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := K) (n := Fin r)) g p)
  have hqv : aeval g q *ᵥ v = 0 := by
    rw [← hw]
    ext i
    simp [q, krylov, map_sum, aeval_monomial, Matrix.sum_mulVec, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, Matrix.mulVec.eq_def (Matrix.of _), dotProduct, mul_comm]
  have hmem : q ∈ Module.annihilator K[X] (Module.AEval' (Matrix.toLin' g)) := by
    rw [← hx, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    apply (Module.AEval'.of (Matrix.toLin' g)).symm.injective
    rw [Module.AEval.of_symm_smul, map_zero, ha]
    exact hqv
  have hq : aeval g q = 0 := by
    apply Matrix.toLin'.injective
    rw [map_zero, ← ha]
    refine LinearMap.ext fun u => ?_
    have := Module.mem_annihilator.1 hmem (Module.AEval'.of (Matrix.toLin' g) u)
    have h2 := congrArg (Module.AEval'.of (Matrix.toLin' g)).symm this
    rw [Module.AEval.of_symm_smul, map_zero] at h2
    simpa using h2
  have hd := charpoly_dvd_of_aeval g hs q hq
  have hdeg : q.degree < g.charpoly.degree := by
    rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j _ => lt_of_le_of_lt (degree_monomial_le _ _) ?_
    exact_mod_cast j.2
  have hq0 := eq_zero_of_dvd_of_degree_lt hd hdeg
  apply hw0
  ext j
  have := congrArg (fun p => p.coeff j) hq0
  simpa [q, finset_sum_coeff, coeff_monomial, Fin.val_inj] using this

/- English proof (translation)
Establish `hloc : ∀ m : MaximalSpectrum A, ∃ v : Fin r → A ⧸ m.asIdeal, (krylov (g.map (Ideal.Quotient.mk m.asIdeal)) v).det ≠ 0`. Introduce `m`. Use `m.isMaximal` as an intermediate fact. Use `letI := Ideal.Quotient.field m.asIdeal`. Conclude with `exists_cyclic_field _ (by rw [Matrix.charpoly_map]; exact hs.map)`.

Use `choose w hw using hloc`. Establish `hsurj : ∀ i : Fin r, ∃ a : A, ∀ m : MaximalSpectrum A, Ideal.Quotient.mk m.asIdeal a = w m i`. Introduce `i`. Take `⟨a, ha⟩` from `Ideal.pi_quotient_surjective (I := fun m : MaximalSpectrum A => m.asIdeal) (fun m m' h => MaximalSpectrum.isCoprime_of_ne h) (fun m => w m i)`. Conclude with `⟨a, ha⟩`.

Use `choose v hv using hsurj`. Use `⟨v, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Take `⟨m, hm, hmem⟩` from `exists_max_ideal_of_mem_nonunits hn`. Apply `hw ⟨m, hm⟩` to reduce the goal to its premises.

Establish `: w ⟨m, hm⟩ = Ideal.Quotient.mk m ∘ v` using `funext fun i => (hv i ⟨m, hm⟩).symm`. Rewrite using `[this, ← krylov_map]`. Rewrite `hmem` using `[← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det]`. Conclude with `hmem`.
-/
theorem exists_cyclic {A : Type} [CommRing A] [IsArtinianRing A] {r : ℕ}
    (g : Matrix (Fin r) (Fin r) A) (hs : g.charpoly.Separable) :
    ∃ v, IsUnit (krylov g v).det := by
  classical
  have hloc : ∀ m : MaximalSpectrum A, ∃ v : Fin r → A ⧸ m.asIdeal,
      (krylov (g.map (Ideal.Quotient.mk m.asIdeal)) v).det ≠ 0 := by
    intro m
    have := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    exact exists_cyclic_field _ (by rw [Matrix.charpoly_map]; exact hs.map)
  choose w hw using hloc
  have hsurj : ∀ i : Fin r, ∃ a : A, ∀ m : MaximalSpectrum A,
      Ideal.Quotient.mk m.asIdeal a = w m i := by
    intro i
    obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective (I := fun m : MaximalSpectrum A => m.asIdeal)
      (fun m m' h => MaximalSpectrum.isCoprime_of_ne h) (fun m => w m i)
    exact ⟨a, ha⟩
  choose v hv using hsurj
  refine ⟨v, ?_⟩
  by_contra hn
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hn
  apply hw ⟨m, hm⟩
  have : w ⟨m, hm⟩ = Ideal.Quotient.mk m ∘ v := funext fun i => (hv i ⟨m, hm⟩).symm
  rw [this, ← krylov_map]
  rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det] at hmem
  exact hmem

end Cyclic

section Transfer

variable {R S A B : Type} [CommRing R] [CommRing S] [CommRing A] [CommRing B] [Algebra R S]
  [Algebra A B] {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, ← hb, ← map_mul]`. Generalize the expression as in `x * b j = y`. Use `conv_lhs => rw [← b.sum_repr y]`. Simplify using `only [map_sum, Algebra.smul_def, map_mul, h, hb]`.

Simplify using `only [← Algebra.smul_def, map_smul, Module.Basis.repr_self]`. Simplify using `[Finsupp.finset_sum_apply, Finsupp.single_apply]`.
-/
theorem leftMulMatrix_transfer (f : R →+* A) (ψ : S →+* B)
    (h : ∀ a, ψ (algebraMap R S a) = algebraMap A B (f a)) (b : Module.Basis ι R S)
    (b' : Module.Basis ι A B) (hb : ∀ i, ψ (b i) = b' i) (x : S) :
    Algebra.leftMulMatrix b' (ψ x) = (Algebra.leftMulMatrix b x).map f := by
  ext i j
  rw [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    ← hb, ← map_mul]
  generalize x * b j = y
  conv_lhs => rw [← b.sum_repr y]
  simp only [map_sum, Algebra.smul_def, map_mul, h, hb]
  simp only [← Algebra.smul_def, map_smul, Module.Basis.repr_self]
  simp [Finsupp.finset_sum_apply, Finsupp.single_apply]

/- English proof (translation)
Rewrite using `[Algebra.trace_eq_matrix_trace b', Algebra.trace_eq_matrix_trace b, leftMulMatrix_transfer f ψ h b b' hb, AddMonoidHom.map_trace]`.
-/
theorem trace_transfer (f : R →+* A) (ψ : S →+* B)
    (h : ∀ a, ψ (algebraMap R S a) = algebraMap A B (f a)) (b : Module.Basis ι R S)
    (b' : Module.Basis ι A B) (hb : ∀ i, ψ (b i) = b' i) (x : S) :
    Algebra.trace A B (ψ x) = f (Algebra.trace R S x) := by
  rw [Algebra.trace_eq_matrix_trace b', Algebra.trace_eq_matrix_trace b,
    leftMulMatrix_transfer f ψ h b b' hb, AddMonoidHom.map_trace]

/- English proof (translation)
Rewrite using `[Algebra.norm_eq_matrix_det b', Algebra.norm_eq_matrix_det b, leftMulMatrix_transfer f ψ h b b' hb, RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem norm_transfer (f : R →+* A) (ψ : S →+* B)
    (h : ∀ a, ψ (algebraMap R S a) = algebraMap A B (f a)) (b : Module.Basis ι R S)
    (b' : Module.Basis ι A B) (hb : ∀ i, ψ (b i) = b' i) (x : S) :
    Algebra.norm A (ψ x) = f (Algebra.norm R x) := by
  rw [Algebra.norm_eq_matrix_det b', Algebra.norm_eq_matrix_det b,
    leftMulMatrix_transfer f ψ h b b' hb, RingHom.map_det]
  rfl

end Transfer

section Forms

variable {A : Type} [CommRing A] {r : ℕ} (σ : A →+* A)

/- English proof (translation)
Simplify using `[hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]`.
-/
theorem hform_eq (J : Matrix (Fin r) (Fin r) A) (x y : Fin r → A) :
    hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y) := by
  simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Establish `h2 : σ ∘ (g *ᵥ x) = (g.map σ) *ᵥ (σ ∘ x)`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct]`. Rewrite using `[hform_eq, hform_eq, h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cT, Matrix.dotProduct_mulVec _ (g.map σ)ᵀ, Matrix.vecMul_transpose]`.
-/
theorem hform_mulVec (J g : Matrix (Fin r) (Fin r) A) (x y : Fin r → A) :
    hform σ J (g *ᵥ x) (g *ᵥ y) = hform σ (cT σ g * J * g) x y := by
  have h2 : σ ∘ (g *ᵥ x) = (g.map σ) *ᵥ (σ ∘ x) := by
    funext i; simp [Matrix.mulVec, dotProduct]
  rw [hform_eq, hform_eq, h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cT,
    Matrix.dotProduct_mulVec _ (g.map σ)ᵀ, Matrix.vecMul_transpose]

/- English proof (translation)
Simplify using `[hform, Pi.single_apply, apply_ite σ]`.
-/
theorem hform_single (J : Matrix (Fin r) (Fin r) A) (i j : Fin r) :
    hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  simp [hform, Pi.single_apply, apply_ite σ]

/- English proof (translation)
Use `show cT σ (g : Matrix (Fin r) (Fin r) A) * J * g = J ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce `h x y`. Rewrite using `[hform_mulVec, h]`. Introduce `h`.

Use extensionality with `i j`. Rewrite using `[← hform_single σ (_ * J * _), ← hform_mulVec, h, hform_single]`.
-/
theorem mem_UJ_iff (J : Matrix (Fin r) (Fin r) A) (g : GL (Fin r) A) :
    g ∈ UJ σ J ↔ ∀ x y, hform σ J ((g : Matrix (Fin r) (Fin r) A) *ᵥ x)
      ((g : Matrix (Fin r) (Fin r) A) *ᵥ y) = hform σ J x y := by
  show cT σ (g : Matrix (Fin r) (Fin r) A) * J * g = J ↔ _
  constructor
  · intro h x y; rw [hform_mulVec, h]
  · intro h; ext i j
    rw [← hform_single σ (_ * J * _), ← hform_mulVec, h, hform_single]

/- English proof (translation)
Set `g : GL (Fin r) A` to `⟨LinearMap.toMatrix' t.toLinearMap, LinearMap.toMatrix' t.symm.toLinearMap, by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩`. Establish `hg : ∀ u, (g : Matrix (Fin r) (Fin r) A) *ᵥ u = t u` using `fun u => by`. Simplify using `[g, LinearMap.toMatrix'_mulVec]`. Conclude with `⟨⟨g, (mem_UJ_iff σ J g).2 fun x y => by rw [hg, hg, ht]⟩, hg⟩`.
-/
theorem exists_UJ (J : Matrix (Fin r) (Fin r) A) (t : (Fin r → A) ≃ₗ[A] (Fin r → A))
    (ht : ∀ x y, hform σ J (t x) (t y) = hform σ J x y) :
    ∃ g : UJ σ J, ∀ u, ((g : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) *ᵥ u = t u := by
  let g : GL (Fin r) A := ⟨LinearMap.toMatrix' t.toLinearMap, LinearMap.toMatrix' t.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  have hg : ∀ u, (g : Matrix (Fin r) (Fin r) A) *ᵥ u = t u := fun u => by
    simp [g, LinearMap.toMatrix'_mulVec]
  exact ⟨⟨g, (mem_UJ_iff σ J g).2 fun x y => by rw [hg, hg, ht]⟩, hg⟩

/- English proof (translation)
Establish `h : ∀ i j, σ (J i j) = J j i` using `fun i j => congrFun (congrFun hJ j) i`. Simplify using `only [hform, map_sum, map_mul, hσ, h]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.
-/
theorem hform_symm (hσ : ∀ a, σ (σ a) = a) {J : Matrix (Fin r) (Fin r) A} (hJ : IsHerm σ J)
    (x y : Fin r → A) : hform σ J y x = σ (hform σ J x y) := by
  have h : ∀ i j, σ (J i j) = J j i := fun i j => congrFun (congrFun hJ j) i
  simp only [hform, map_sum, map_mul, hσ, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

def hlin (J : Matrix (Fin r) (Fin r) A) (x : Fin r → A) : (Fin r → A) →ₗ[A] A where
  toFun y := hform σ J x y
  map_add' y z := by simp [hform_eq, Matrix.mulVec_add]
  map_smul' a y := by simp [hform_eq, Matrix.mulVec_smul]

/- English proof (translation)
Use `⟨σ ∘ ((fun i => f (Pi.single i 1)) ᵥ* J⁻¹), fun y => ?_⟩` and prove the remaining obligations. Establish `: σ ∘ σ ∘ ((fun i => f (Pi.single i 1)) ᵥ* J⁻¹) = (fun i => f (Pi.single i 1)) ᵥ* J⁻¹`. Use function extensionality and compare the values at `fun i => hσ _`. Rewrite using `[hform_eq, this, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hJ, Matrix.vecMul_one, LinearMap.pi_apply_eq_sum_univ f y]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Establish `: (fun j => if i = j then (1 : A) else 0) = Pi.single i 1`. Use extensionality with `j`. Simplify using `[Pi.single_apply, eq_comm]`. Rewrite using `[smul_eq_mul, mul_comm, this]`.
-/
theorem hlin_surj (hσ : ∀ a, σ (σ a) = a) {J : Matrix (Fin r) (Fin r) A} (hJ : IsUnit J.det)
    (f : (Fin r → A) →ₗ[A] A) : ∃ x, ∀ y, hform σ J x y = f y := by
  refine ⟨σ ∘ ((fun i => f (Pi.single i 1)) ᵥ* J⁻¹), fun y => ?_⟩
  have : σ ∘ σ ∘ ((fun i => f (Pi.single i 1)) ᵥ* J⁻¹) = (fun i => f (Pi.single i 1)) ᵥ* J⁻¹ :=
    funext fun i => hσ _
  rw [hform_eq, this, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hJ,
    Matrix.vecMul_one, LinearMap.pi_apply_eq_sum_univ f y]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (fun j => if i = j then (1 : A) else 0) = Pi.single i 1 := by
    ext j; simp [Pi.single_apply, eq_comm]
  rw [smul_eq_mul, mul_comm, this]

end Forms

section Core

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}

structure HidaSetting (σ : A →+* A) (τ : B →+* B) (α : B) (b : Module.Basis (Fin r) A B) : Prop where
  hσ : ∀ a, σ (σ a) = a
  hτ : ∀ y, τ (τ y) = y
  comp : ∀ a, τ (algebraMap A B a) = algebraMap A B (σ a)
  hα : α * τ α = 1
  pow : ∀ i, b i = α ^ (i : ℕ)
  perf : IsUnit (Algebra.traceMatrix A b).det

def tf (A : Type) [CommRing A] [Algebra A B] (τ : B →+* B) (x y y' : B) : A :=
  Algebra.trace A B (x * y * τ y')

def Iso (σ : A →+* A) (τ : B →+* B) (J : Matrix (Fin r) (Fin r) A) (x : B)
    (φ : B ≃ₗ[A] (Fin r → A)) : Prop :=
  ∀ y y', hform σ J (φ y') (φ y) = tf A τ x y y'

def Intw (α : B) (g : Matrix (Fin r) (Fin r) A) (φ : B ≃ₗ[A] (Fin r → A)) : Prop :=
  ∀ u, g *ᵥ u = φ (α * φ.symm u)

variable {σ : A →+* A} {τ : B →+* B} {α : B} {b : Module.Basis (Fin r) A B}
  {J : Matrix (Fin r) (Fin r) A}

def HidaSetting.pb (S : HidaSetting σ τ α b) : PowerBasis A B := ⟨α, r, b, S.pow⟩

/- English proof (translation)
Use `Algebra.trace_eq_of_equiv_equiv (RingEquiv.ofRingHom σ σ (RingHom.ext S.hσ) (RingHom.ext S.hσ)) (RingEquiv.ofRingHom τ τ (RingHom.ext S.hτ) (RingHom.ext S.hτ)) (RingHom.ext fun a => (S.comp a).symm) z` as an intermediate fact. Rewrite using `[this]`. Conclude with `(S.hσ _).symm`.
-/
theorem HidaSetting.trace_star (S : HidaSetting σ τ α b) (z : B) :
    Algebra.trace A B (τ z) = σ (Algebra.trace A B z) := by
  have := Algebra.trace_eq_of_equiv_equiv
    (RingEquiv.ofRingHom σ σ (RingHom.ext S.hσ) (RingHom.ext S.hσ))
    (RingEquiv.ofRingHom τ τ (RingHom.ext S.hτ) (RingHom.ext S.hτ))
    (RingHom.ext fun a => (S.comp a).symm) z
  rw [this]
  exact (S.hσ _).symm

/- English proof (translation)
Establish `h : IsUnit (LinearMap.toMatrix b b.dualBasis (Algebra.traceForm A B)).det`. Establish `: LinearMap.toMatrix b b.dualBasis (Algebra.traceForm A B) = (Algebra.traceMatrix A b)ᵀ`. Use extensionality with `i j`. Simplify using `[LinearMap.toMatrix_apply, Algebra.traceMatrix_apply]`. Rewrite using `[this, Matrix.det_transpose]`.

Conclude with `S.perf`. Use `(LinearEquiv.ofIsUnitDet h).bijective` as an intermediate fact. Rewrite `this` using `[← LinearEquiv.coe_coe, LinearEquiv.coe_ofIsUnitDet]`. Then use the resulting hypothesis.
-/
theorem HidaSetting.traceForm_bij (S : HidaSetting σ τ α b) :
    Function.Bijective (Algebra.traceForm A B) := by
  have h : IsUnit (LinearMap.toMatrix b b.dualBasis (Algebra.traceForm A B)).det := by
    have : LinearMap.toMatrix b b.dualBasis (Algebra.traceForm A B)
        = (Algebra.traceMatrix A b)ᵀ := by
      ext i j
      simp [LinearMap.toMatrix_apply, Algebra.traceMatrix_apply]
    rw [this, Matrix.det_transpose]; exact S.perf
  have := (LinearEquiv.ofIsUnitDet h).bijective
  rwa [← LinearEquiv.coe_coe, LinearEquiv.coe_ofIsUnitDet] at this

/- English proof (translation)
The claim follows from `S.traceForm_bij.1 (LinearMap.ext h)`.
-/
theorem HidaSetting.eq_of_trace (S : HidaSetting σ τ α b) {x x' : B}
    (h : ∀ y, Algebra.trace A B (x * y) = Algebra.trace A B (x' * y)) : x = x' :=
  S.traceForm_bij.1 (LinearMap.ext h)

/- English proof (translation)
Take `⟨x, hx⟩` from `S.traceForm_bij.2 f`. Conclude with `⟨x, fun y => by rw [← hx]; rfl⟩`.
-/
theorem HidaSetting.exists_trace (S : HidaSetting σ τ α b) (f : B →ₗ[A] A) :
    ∃ x, ∀ y, f y = Algebra.trace A B (x * y) := by
  obtain ⟨x, hx⟩ := S.traceForm_bij.2 f
  exact ⟨x, fun y => by rw [← hx]; rfl⟩

def mulUnit (A : Type) [CommRing A] [Algebra A B] (z : Bˣ) : B ≃ₗ[A] B :=
  LinearEquiv.ofLinear (LinearMap.mulLeft A (z : B)) (LinearMap.mulLeft A ((z⁻¹ : Bˣ) : B))
    (by ext; simp) (by ext; simp)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mulUnit_apply (z : Bˣ) (y : B) : mulUnit A z y = z * y := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mulUnit_symm_apply (z : Bˣ) (y : B) : (mulUnit A z).symm y = (z⁻¹ : Bˣ) * y := rfl

/- English proof (translation)
Introduce `y y'`. Simplify using `only [LinearEquiv.trans_apply, mulUnit_apply]`. Rewrite using `[h]`. Unfold `tf`. Use `congr 1`.

Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Iso.mul {x : B} {φ : B ≃ₗ[A] (Fin r → A)} (h : Iso σ τ J x φ) (z : Bˣ) :
    Iso σ τ J (x * (z * τ z)) (mulUnit A z ≪≫ₗ φ) := by
  intro y y'
  simp only [LinearEquiv.trans_apply, mulUnit_apply]
  rw [h]
  unfold tf
  congr 1
  rw [map_mul]; ring

/- English proof (translation)
Introduce `u`. Rewrite using `[h]`. Simplify using `only [LinearEquiv.trans_apply, mulUnit_apply, LinearEquiv.symm_trans_apply, mulUnit_symm_apply]`. Use `congr 1`. Rewrite using `[mul_left_comm α, Units.mul_inv_cancel_left]`.
-/
theorem Intw.mul {g : Matrix (Fin r) (Fin r) A} {φ : B ≃ₗ[A] (Fin r → A)} (h : Intw α g φ)
    (z : Bˣ) : Intw α g (mulUnit A z ≪≫ₗ φ) := by
  intro u
  rw [h]
  simp only [LinearEquiv.trans_apply, mulUnit_apply, LinearEquiv.symm_trans_apply,
    mulUnit_symm_apply]
  congr 1
  rw [mul_left_comm α, Units.mul_inv_cancel_left]

/- English proof (translation)
Set `a : Bˣ` to `⟨α, τ α, S.hα, by rw [mul_comm, S.hα]⟩`. Take `⟨g, hg⟩` from `exists_UJ σ J (φ.symm ≪≫ₗ (mulUnit A a ≪≫ₗ φ)) (by`. Introduce `u u'`. Establish `h1` using `h.mul a (φ.symm u') (φ.symm u)`. Establish `h2` using `h (φ.symm u') (φ.symm u)`.

Rewrite `h1` using `[show (a : B) = α from rfl, S.hα, mul_one, ← h2]`. Simplify using `using h1)`. Conclude with `⟨g, hg⟩`.
-/
theorem HidaSetting.exists_intw (S : HidaSetting σ τ α b) {x : B} {φ : B ≃ₗ[A] (Fin r → A)}
    (h : Iso σ τ J x φ) :
    ∃ g : UJ σ J, Intw α ((g : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) φ := by
  let a : Bˣ := ⟨α, τ α, S.hα, by rw [mul_comm, S.hα]⟩
  obtain ⟨g, hg⟩ := exists_UJ σ J (φ.symm ≪≫ₗ (mulUnit A a ≪≫ₗ φ)) (by
    intro u u'
    have h1 := h.mul a (φ.symm u') (φ.symm u)
    have h2 := h (φ.symm u') (φ.symm u)
    rw [show (a : B) = α from rfl, S.hα, mul_one, ← h2] at h1
    simpa using h1)
  exact ⟨g, hg⟩

/- English proof (translation)
Take `⟨t, ht⟩` from `exists_UJ σ J (φ.symm ≪≫ₗ φ') (by`. Introduce `u u'`. Establish `h2` using `h (φ.symm u') (φ.symm u)`. Rewrite `h2` using `[← h']`. Simplify using `using h2.symm)`.

Rewrite using `[isConj_iff]`. Use `⟨t, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_inv_eq_iff_eq_mul]`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Use `LinearMap.ext fun u => ?_` and prove the remaining obligations. Simplify using `only [Subgroup.coe_mul, Units.val_mul, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]`. Rewrite using `[ht, hg, hg', ht]`. Simplify using the standard rewrite rules.
-/
theorem isConj_of_iso {x : B} {φ φ' : B ≃ₗ[A] (Fin r → A)} (h : Iso σ τ J x φ)
    (h' : Iso σ τ J x φ') {g g' : UJ σ J}
    (hg : Intw α ((g : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) φ)
    (hg' : Intw α ((g' : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) φ') : IsConj g g' := by
  obtain ⟨t, ht⟩ := exists_UJ σ J (φ.symm ≪≫ₗ φ') (by
    intro u u'
    have h2 := h (φ.symm u') (φ.symm u)
    rw [← h'] at h2
    simpa using h2.symm)
  rw [isConj_iff]
  refine ⟨t, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  apply Units.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun u => ?_
  simp only [Subgroup.coe_mul, Units.val_mul, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
  rw [ht, hg, hg', ht]
  simp

/- English proof (translation)
Establish `hp : ∀ n : ℕ, ψ (α ^ n) = ψ 1 * α ^ n`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ', h, ih]`.

Expand and normalize the polynomial expressions, which then agree. Establish `: ψ = LinearMap.mulLeft A (ψ 1)` using `b.ext fun i => by rw [S.pow, hp]; rfl`. Conclude with `LinearMap.congr_fun this y`.
-/
theorem HidaSetting.map_mul_of_comm (S : HidaSetting σ τ α b) (ψ : B →ₗ[A] B)
    (h : ∀ y, ψ (α * y) = α * ψ y) (y : B) : ψ y = ψ 1 * y := by
  have hp : ∀ n : ℕ, ψ (α ^ n) = ψ 1 * α ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', h, ih]; ring
  have : ψ = LinearMap.mulLeft A (ψ 1) := b.ext fun i => by rw [S.pow, hp]; rfl
  exact LinearMap.congr_fun this y

/- English proof (translation)
Take `⟨t, ht⟩` from `isConj_iff.1 hc`. Rewrite `ht` using `[mul_inv_eq_iff_eq_mul]`. Establish `ht' : ((t : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) * (g' : GL (Fin r) A) = ((g : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) * (t : GL (Fin r) A)` using `congrArg (fun s : UJ σ J => ((s : GL (Fin r) A) : Matrix (Fin r) (Fin r) A)) ht`. Set `T : (Fin r → A) ≃ₗ[A] (Fin r → A)` to `Matrix.toLinearEquiv' ((t : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) (Units.invertible _)`. Establish `hT : ∀ u, T u = ((t : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) *ᵥ u` using `fun u => rfl`.

Set `ψ : B ≃ₗ[A] B` to `φ' ≪≫ₗ T ≪≫ₗ φ.symm`. Establish `hψ : ∀ y, φ (ψ y) = ((t : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) *ᵥ φ' y` using `fun y => by`. Simplify using `[ψ, hT]`. Establish `hcomm : ∀ y, ψ (α * y) = α * ψ y`. Introduce `y`.

Apply `φ.injective` to reduce the goal to its premises. Establish `e1` using `hg' (φ' y)`. Establish `e2` using `hg (φ (ψ y))`. Rewrite `e1`, `e2` using `[LinearEquiv.symm_apply_apply]`. Rewrite using `[hψ, ← e1, ← e2, hψ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ht']`.

Establish `hm : ∀ y, ψ y = ψ 1 * y` using `S.map_mul_of_comm ψ.toLinearMap hcomm`. Establish `hu : IsUnit (ψ 1)` using `IsUnit.of_mul_eq_one (ψ.symm 1) (by rw [← hm]; simp)`. Use `⟨hu.unit, S.eq_of_trace fun y => ?_⟩` and prove the remaining obligations. Establish `e1` using `h' y 1`. Establish `e2` using `h (ψ y) (ψ 1)`.

Rewrite `e2` using `[hψ, hψ, (mem_UJ_iff σ J _).1 t.2, e1, hm y]`. Unfold `tf at e2`. Rewrite `e2` using `[map_one, mul_one]`. Rewrite using `[e2, IsUnit.unit_spec]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem HidaSetting.norm_of_isConj (S : HidaSetting σ τ α b) {x x' : B} {φ φ' : B ≃ₗ[A] (Fin r → A)}
    (h : Iso σ τ J x φ) (h' : Iso σ τ J x' φ') {g g' : UJ σ J}
    (hg : Intw α ((g : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) φ)
    (hg' : Intw α ((g' : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) φ') (hc : IsConj g' g) :
    ∃ z : Bˣ, x' = x * (z * τ z) := by
  obtain ⟨t, ht⟩ := isConj_iff.1 hc
  rw [mul_inv_eq_iff_eq_mul] at ht
  have ht' : ((t : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) * (g' : GL (Fin r) A)
      = ((g : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) * (t : GL (Fin r) A) :=
    congrArg (fun s : UJ σ J => ((s : GL (Fin r) A) : Matrix (Fin r) (Fin r) A)) ht
  let T : (Fin r → A) ≃ₗ[A] (Fin r → A) := Matrix.toLinearEquiv' ((t : GL (Fin r) A) : Matrix (Fin r) (Fin r) A)
    (Units.invertible _)
  have hT : ∀ u, T u = ((t : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) *ᵥ u := fun u => rfl
  let ψ : B ≃ₗ[A] B := φ' ≪≫ₗ T ≪≫ₗ φ.symm
  have hψ : ∀ y, φ (ψ y) = ((t : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) *ᵥ φ' y := fun y => by
    simp [ψ, hT]
  have hcomm : ∀ y, ψ (α * y) = α * ψ y := by
    intro y
    apply φ.injective
    have e1 := hg' (φ' y)
    have e2 := hg (φ (ψ y))
    rw [LinearEquiv.symm_apply_apply] at e1 e2
    rw [hψ, ← e1, ← e2, hψ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ht']
  have hm : ∀ y, ψ y = ψ 1 * y := S.map_mul_of_comm ψ.toLinearMap hcomm
  have hu : IsUnit (ψ 1) := IsUnit.of_mul_eq_one (ψ.symm 1) (by rw [← hm]; simp)
  refine ⟨hu.unit, S.eq_of_trace fun y => ?_⟩
  have e1 := h' y 1
  have e2 := h (ψ y) (ψ 1)
  rw [hψ, hψ, (mem_UJ_iff σ J _).1 t.2, e1, hm y] at e2
  unfold tf at e2
  rw [map_one, mul_one] at e2
  rw [e2, IsUnit.unit_spec]
  congr 1; ring

/- English proof (translation)
Use `haveI := Module.Free.of_basis b`. Use `haveI := Module.Finite.of_basis b`. Establish `h1 : Matrix.toLin' g = φ.conj (Algebra.lmul A B α)` using `LinearMap.ext fun u => by`. Simplify `hg u` using `[LinearEquiv.conj_apply]`. Rewrite using `[← Matrix.charpoly_toLin', h1, LinearEquiv.charpoly_conj, Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]`.
-/
theorem charpoly_of_intw {g : Matrix (Fin r) (Fin r) A} {φ : B ≃ₗ[A] (Fin r → A)}
    (b : Module.Basis (Fin r) A B)
    (hg : Intw α g φ) : g.charpoly = (Algebra.leftMulMatrix b α).charpoly := by
  haveI := Module.Free.of_basis b
  haveI := Module.Finite.of_basis b
  have h1 : Matrix.toLin' g = φ.conj (Algebra.lmul A B α) := LinearMap.ext fun u => by
    simpa [LinearEquiv.conj_apply] using hg u
  rw [← Matrix.charpoly_toLin', h1, LinearEquiv.charpoly_conj, Algebra.leftMulMatrix_apply,
    LinearMap.charpoly_toMatrix]

/- English proof (translation)
Use `set G : Matrix (Fin r) (Fin r) A := ((g : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) with hG`. Take `⟨v, hv⟩` from `exists_cyclic G (hg ▸ hs)`. Establish `hmin : aeval G (minpoly A S.pb.gen) = 0`. Rewrite using `[← charpoly_leftMulMatrix S.pb]`. Use `show aeval G (Algebra.leftMulMatrix b α).charpoly = 0`.

Rewrite using `[← hg]`. Conclude with `Matrix.aeval_self_charpoly G`. Set `ρ` to `S.pb.lift G hmin`. Establish `hρ : ρ α = G` using `S.pb.lift_gen G hmin`. Set `φ₀ : B →ₗ[A] (Fin r → A)` to `{ toFun := fun y => ρ y *ᵥ v map_add' := fun y z => by rw [map_add, Matrix.add_mulVec] map_smul' := fun a y => by rw [map_smul, Matrix.smul_mulVec]; rfl }`.

Establish `hdet : IsUnit (LinearMap.toMatrix b (Pi.basisFun A (Fin r)) φ₀).det`. Use `hv using 2` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Simplify using `[LinearMap.toMatrix_apply, φ₀, S.pow, hρ, krylov]`. Set `φ` to `LinearEquiv.ofIsUnitDet hdet`.

Establish `hφ : ∀ y, φ y = ρ y *ᵥ v` using `fun y => LinearEquiv.ofIsUnitDet_apply hdet y`. Establish `hα : ∀ y, φ (α * y) = G *ᵥ φ y` using `fun y => by`. Rewrite using `[hφ, hφ, map_mul, hρ, Matrix.mulVec_mulVec]`. Establish `hadj1 : ∀ y y', hform σ J (φ y') (φ (α * y)) = hform σ J (φ (τ α * y')) (φ y)`. Introduce `y y'`.

Rewrite using `[← (mem_UJ_iff σ J _).1 g.2 (φ (τ α * y')), ← hα, ← hα, ← mul_assoc, S.hα, one_mul]`. Establish `hadjn : ∀ (n : ℕ) y y', hform σ J (φ y') (φ (α ^ n * y)) = hform σ J (φ (τ (α ^ n) * y')) (φ y)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`.

Consider the case `succ n ih`. Introduce `y y'`. Rewrite using `[pow_succ', mul_assoc, hadj1, ih, map_mul τ, ← mul_assoc, mul_comm (τ α)]`. Establish `hadj : ∀ l y y', hform σ J (φ y') (φ (l * y)) = hform σ J (φ (τ l * y')) (φ y)`. Introduce `l y y'`.

Establish `hl : l ∈ Submodule.span A (Set.range b)` using `b.mem_span l`. Proceed by induction on `hl using Submodule.span_induction with`. Consider the case `mem l hl => obtain ⟨i, rfl⟩ := hl`. Rewrite using `[S.pow, hadjn]`. Consider the case `zero => simp [hform]`.

Consider the case `add l m _ _ h1 h2`. Rewrite using `[add_mul, map_add, map_add, add_mul, map_add]`. Simplify using `only [hform, Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib] at h1 h2 ⊢`. Rewrite using `[h1, h2]`. Consider the case `smul a l _ h1`.

Establish `e : τ (a • l) * y' = σ a • (τ l * y')`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul, S.comp, mul_assoc]`. Rewrite using `[smul_mul_assoc, map_smul, e, map_smul]`. Establish `e1 : ∀ u u' : Fin r → A, hform σ J u (a • u') = a * hform σ J u u'` using `fun u u' => (hlin σ J u).map_smul a u'`. Establish `e2 : ∀ u u' : Fin r → A, hform σ J (σ a • u) u' = a * hform σ J u u'` using `fun u u' => by`.

Simplify using `[hform, S.hσ, Finset.mul_sum, mul_assoc]`. Rewrite using `[e1, e2, h1]`. Take `⟨x, hx⟩` from `S.exists_trace (hlin σ J (φ 1) ∘ₗ φ.toLinearMap)`. Establish `hiso : Iso σ τ J x φ`. Introduce `y y'`.

Use `hadj (τ y') y 1` as an intermediate fact. Rewrite `this` using `[S.hτ, mul_one]`. Rewrite using `[← this]`. Use `(hx (τ y' * y)).trans ?_` and prove the remaining obligations. Unfold `tf`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `⟨x, φ, ?_, ?_, hiso, fun u => by rw [hα]; simp⟩` and prove the remaining obligations. Take `⟨u, hu⟩` from `hlin_surj σ S.hσ hd (Algebra.trace A B ∘ₗ φ.symm.toLinearMap)`. Use `IsUnit.of_mul_eq_one (τ (φ.symm u)) (S.eq_of_trace fun y => ?_)` and prove the remaining obligations.

Establish `e1` using `hiso y (φ.symm u)`. Rewrite `e1` using `[LinearEquiv.apply_symm_apply, hu]`. Unfold `tf at e1`. Rewrite using `[mul_right_comm, ← e1]`. Simplify using the standard rewrite rules.

Use `S.eq_of_trace fun y => ?_` and prove the remaining obligations. Establish `e1` using `hiso y 1`. Rewrite `e1` using `[hform_symm σ S.hσ hJ, hiso]`. Unfold `tf at e1`. Rewrite `e1` using `[← S.trace_star]`.

Simplify `e1` using `[S.hτ]`.
-/
theorem HidaSetting.exists_of_charpoly [IsArtinianRing A] (S : HidaSetting σ τ α b) (hJ : IsHerm σ J)
    (hd : IsUnit J.det) (g : UJ σ J)
    (hg : ((g : GL (Fin r) A) : Matrix (Fin r) (Fin r) A).charpoly
      = (Algebra.leftMulMatrix b α).charpoly)
    (hs : (Algebra.leftMulMatrix b α).charpoly.Separable) :
    ∃ x φ, IsUnit x ∧ τ x = x ∧ Iso σ τ J x φ ∧
      Intw α ((g : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) φ := by
  set G : Matrix (Fin r) (Fin r) A := ((g : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) with hG
  obtain ⟨v, hv⟩ := exists_cyclic G (hg ▸ hs)
  have hmin : aeval G (minpoly A S.pb.gen) = 0 := by
    rw [← charpoly_leftMulMatrix S.pb]
    show aeval G (Algebra.leftMulMatrix b α).charpoly = 0
    rw [← hg]; exact Matrix.aeval_self_charpoly G
  let ρ := S.pb.lift G hmin
  have hρ : ρ α = G := S.pb.lift_gen G hmin
  let φ₀ : B →ₗ[A] (Fin r → A) :=
    { toFun := fun y => ρ y *ᵥ v
      map_add' := fun y z => by rw [map_add, Matrix.add_mulVec]
      map_smul' := fun a y => by rw [map_smul, Matrix.smul_mulVec]; rfl }
  have hdet : IsUnit (LinearMap.toMatrix b (Pi.basisFun A (Fin r)) φ₀).det := by
    convert hv using 2
    ext i j
    simp [LinearMap.toMatrix_apply, φ₀, S.pow, hρ, krylov]
  let φ := LinearEquiv.ofIsUnitDet hdet
  have hφ : ∀ y, φ y = ρ y *ᵥ v := fun y => LinearEquiv.ofIsUnitDet_apply hdet y
  have hα : ∀ y, φ (α * y) = G *ᵥ φ y := fun y => by
    rw [hφ, hφ, map_mul, hρ, Matrix.mulVec_mulVec]
  have hadj1 : ∀ y y', hform σ J (φ y') (φ (α * y)) = hform σ J (φ (τ α * y')) (φ y) := by
    intro y y'
    rw [← (mem_UJ_iff σ J _).1 g.2 (φ (τ α * y')), ← hα, ← hα, ← mul_assoc, S.hα, one_mul]
  have hadjn : ∀ (n : ℕ) y y',
      hform σ J (φ y') (φ (α ^ n * y)) = hform σ J (φ (τ (α ^ n) * y')) (φ y) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro y y'
      rw [pow_succ', mul_assoc, hadj1, ih, map_mul τ, ← mul_assoc, mul_comm (τ α)]
  have hadj : ∀ l y y', hform σ J (φ y') (φ (l * y)) = hform σ J (φ (τ l * y')) (φ y) := by
    intro l y y'
    have hl : l ∈ Submodule.span A (Set.range b) := b.mem_span l
    induction hl using Submodule.span_induction with
    | mem l hl => obtain ⟨i, rfl⟩ := hl; rw [S.pow, hadjn]
    | zero => simp [hform]
    | add l m _ _ h1 h2 =>
      rw [add_mul, map_add, map_add, add_mul, map_add]
      simp only [hform, Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib] at h1 h2 ⊢
      rw [h1, h2]
    | smul a l _ h1 =>
      have e : τ (a • l) * y' = σ a • (τ l * y') := by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, S.comp, mul_assoc]
      rw [smul_mul_assoc, map_smul, e, map_smul]
      have e1 : ∀ u u' : Fin r → A, hform σ J u (a • u') = a * hform σ J u u' := fun u u' =>
        (hlin σ J u).map_smul a u'
      have e2 : ∀ u u' : Fin r → A, hform σ J (σ a • u) u' = a * hform σ J u u' := fun u u' => by
        simp [hform, S.hσ, Finset.mul_sum, mul_assoc]
      rw [e1, e2, h1]
  obtain ⟨x, hx⟩ := S.exists_trace (hlin σ J (φ 1) ∘ₗ φ.toLinearMap)
  have hiso : Iso σ τ J x φ := by
    intro y y'
    have := hadj (τ y') y 1
    rw [S.hτ, mul_one] at this
    rw [← this]
    refine (hx (τ y' * y)).trans ?_
    unfold tf; congr 1; ring
  refine ⟨x, φ, ?_, ?_, hiso, fun u => by rw [hα]; simp⟩
  · obtain ⟨u, hu⟩ := hlin_surj σ S.hσ hd (Algebra.trace A B ∘ₗ φ.symm.toLinearMap)
    refine IsUnit.of_mul_eq_one (τ (φ.symm u)) (S.eq_of_trace fun y => ?_)
    have e1 := hiso y (φ.symm u)
    rw [LinearEquiv.apply_symm_apply, hu] at e1
    unfold tf at e1
    rw [mul_right_comm, ← e1]
    simp
  · refine S.eq_of_trace fun y => ?_
    have e1 := hiso y 1
    rw [hform_symm σ S.hσ hJ, hiso] at e1
    unfold tf at e1
    rw [← S.trace_star] at e1
    simpa [S.hτ] using e1

def gram (τ : B →+* B) (x : B) (e : Module.Basis (Fin r) A B) : Matrix (Fin r) (Fin r) A :=
  Matrix.of fun i j => tf A τ x (e i) (e j)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [gram, tf, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Algebra.leftMulMatrix_eq_repr_mul, one_mul]`. Use `conv_lhs => rw [← e.sum_repr (x * e i)]`. Simplify using `only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, smul_eq_mul]`.
-/
theorem gram_eq (x : B) (e : Module.Basis (Fin r) A B) :
    gram τ x e = (Algebra.leftMulMatrix e x)ᵀ * gram τ 1 e := by
  ext i j
  simp only [gram, tf, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Algebra.leftMulMatrix_eq_repr_mul, one_mul]
  conv_lhs => rw [← e.sum_repr (x * e i)]
  simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, smul_eq_mul]

/- English proof (translation)
Rewrite using `[gram_eq, Matrix.det_mul, Matrix.det_transpose, Algebra.norm_eq_matrix_det e]`.
-/
theorem det_gram (x : B) (e : Module.Basis (Fin r) A B) :
    (gram τ x e).det = Algebra.norm A x * (gram τ 1 e).det := by
  rw [gram_eq, Matrix.det_mul, Matrix.det_transpose, Algebra.norm_eq_matrix_det e]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [gram, tf, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Module.Basis.toMatrix_apply]`. Use `conv_lhs => rw [← e.sum_repr (e' i), ← e.sum_repr (e' j)]`. Simplify using `only [map_sum, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Establish `: x * (e.repr (e' i) q • e q) * τ (e.repr (e' j) p • e p) = (e.repr (e' i) q * σ (e.repr (e' j) p)) • (x * e q * τ (e p))`. Simplify using `only [Algebra.smul_def, map_mul, S.comp]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, map_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem HidaSetting.gram_change (S : HidaSetting σ τ α b) (x : B) (e e' : Module.Basis (Fin r) A B) :
    gram τ x e' = (e.toMatrix e')ᵀ * gram τ x e * (e.toMatrix e').map σ := by
  ext i j
  simp only [gram, tf, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Module.Basis.toMatrix_apply]
  conv_lhs => rw [← e.sum_repr (e' i), ← e.sum_repr (e' j)]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  have : x * (e.repr (e' i) q • e q) * τ (e.repr (e' j) p • e p)
      = (e.repr (e' i) q * σ (e.repr (e' j) p)) • (x * e q * τ (e p)) := by
    simp only [Algebra.smul_def, map_mul, S.comp]; ring
  rw [this, map_smul, smul_eq_mul]; ring

/- English proof (translation)
Establish `hu : IsUnit (e.toMatrix e').det` using `e.isUnit_det e'`. Use `⟨hu.unit, ?_⟩` and prove the remaining obligations. Rewrite using `[S.gram_change x e e', Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, IsUnit.unit_spec, RingHom.map_det]`. Simplify using `only [RingHom.mapMatrix_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem HidaSetting.det_gram_change (S : HidaSetting σ τ α b) (x : B) (e e' : Module.Basis (Fin r) A B) :
    ∃ z : Aˣ, (gram τ x e').det = (gram τ x e).det * (z * σ z) := by
  have hu : IsUnit (e.toMatrix e').det := e.isUnit_det e'
  refine ⟨hu.unit, ?_⟩
  rw [S.gram_change x e e', Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, IsUnit.unit_spec,
    RingHom.map_det]
  simp only [RingHom.mapMatrix_apply]; ring

/- English proof (translation)
Rewrite using `[det_gram]`. Use `(hx.map (Algebra.norm A)).mul ?_` and prove the remaining obligations. Set `N : Matrix (Fin r) (Fin r) A` to `Matrix.of fun i j => b.repr (τ (b j)) i`. Establish `hN : ∀ j, τ (b j) = ∑ i, N i j • b i` using `fun j => (b.sum_repr _).symm`. Establish `h1 : gram τ 1 b = Algebra.traceMatrix A b * N`.

Use extensionality with `i j`. Simplify using `[gram, tf, Matrix.mul_apply, hN, Finset.mul_sum, Algebra.traceMatrix_apply, mul_comm]`. Establish `h2 : N * N.map σ = 1`. Use extensionality with `i j`. Establish `e : b j = ∑ p, σ (N p j) • τ (b p)` using `by conv_lhs => rw [← S.hτ (b j), hN j]`.

Simplify using `only [map_sum, Algebra.smul_def, map_mul, S.comp]`. Establish `e2` using `congrArg (fun y => b.repr y i) e`. Simplify using `only [map_sum, map_smul, Module.Basis.repr_self] at e2`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify `e2.symm` using `[Finsupp.single_apply, eq_comm, N, mul_comm]`.

Rewrite using `[h1, Matrix.det_mul]`. Conclude with `S.perf.mul (Matrix.isUnit_det_of_right_inverse h2)`.
-/
theorem HidaSetting.isUnit_det_gram (S : HidaSetting σ τ α b) {x : B} (hx : IsUnit x) :
    IsUnit (gram τ x b).det := by
  rw [det_gram]
  refine (hx.map (Algebra.norm A)).mul ?_
  let N : Matrix (Fin r) (Fin r) A := Matrix.of fun i j => b.repr (τ (b j)) i
  have hN : ∀ j, τ (b j) = ∑ i, N i j • b i := fun j => (b.sum_repr _).symm
  have h1 : gram τ 1 b = Algebra.traceMatrix A b * N := by
    ext i j
    simp [gram, tf, Matrix.mul_apply, hN, Finset.mul_sum, Algebra.traceMatrix_apply, mul_comm]
  have h2 : N * N.map σ = 1 := by
    ext i j
    have e : b j = ∑ p, σ (N p j) • τ (b p) := by
      conv_lhs => rw [← S.hτ (b j), hN j]
      simp only [map_sum, Algebra.smul_def, map_mul, S.comp]
    have e2 := congrArg (fun y => b.repr y i) e
    simp only [map_sum, map_smul, Module.Basis.repr_self] at e2
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [Finsupp.single_apply, eq_comm, N, mul_comm] using e2.symm
  rw [h1, Matrix.det_mul]
  exact S.perf.mul (Matrix.isUnit_det_of_right_inverse h2)

/- English proof (translation)
Rewrite using `[RingHom.map_det, ← Matrix.det_transpose]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `only [gram, tf, Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, ← S.trace_star, map_mul, hx, S.hτ]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem HidaSetting.det_gram_fixed (S : HidaSetting σ τ α b) {x : B} (hx : τ x = x)
    (e : Module.Basis (Fin r) A B) : σ (gram τ x e).det = (gram τ x e).det := by
  rw [RingHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp only [gram, tf, Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.of_apply, ← S.trace_star, map_mul, hx, S.hτ]
  congr 1; ring

end Core

section Concrete

open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion

attribute [local instance] algLk

variable {F E : Type} [Field F] [Field E] [Algebra F E] {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}
  (k : Type) [Field k] [Algebra F k]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem algebraMap_tmul (e : E) (t : k) :
    algebraMap (E ⊗[F] k) (AdjoinRoot P ⊗[F] k) (e ⊗ₜ t) = AdjoinRoot.of P e ⊗ₜ t := rfl

/- English proof (translation)
Rewrite using `[Algebra.smul_def]`. Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add a a' h h' => rw [map_add, add_mul, map_add, h, h', add_mul]`. Consider the case `tmul e t`.

Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add y y' h h' => rw [mul_add, map_add, h, h', map_add, mul_add]`. Consider the case `tmul l s`. Establish `: AdjoinRoot.of P e * l = e • l` using `(Algebra.smul_def e l).symm`.

Simplify using `[algebraMap_tmul, this]`.
-/
theorem map_smul_tensor (f : AdjoinRoot P →ₗ[E] E) (a : E ⊗[F] k) (y : AdjoinRoot P ⊗[F] k) :
    TensorProduct.map (f.restrictScalars F) LinearMap.id (a • y)
      = a * TensorProduct.map (f.restrictScalars F) LinearMap.id y := by
  rw [Algebra.smul_def]
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add a a' h h' => rw [map_add, add_mul, map_add, h, h', add_mul]
  | tmul e t =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' h h' => rw [mul_add, map_add, h, h', map_add, mul_add]
    | tmul l s =>
      have : AdjoinRoot.of P e * l = e • l := (Algebra.smul_def e l).symm
      simp [algebraMap_tmul, this]

/- English proof (translation)
Use `⟨Module.Basis.mk (v := fun i => b i ⊗ₜ 1) ?_ ?_, fun i => Module.Basis.mk_apply _ _ _⟩` and prove the remaining obligations. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg j`. Use `congrArg (TensorProduct.map ((b.coord j).restrictScalars F) LinearMap.id) hg` as an intermediate fact. Simplify using `only [map_sum, map_smul_tensor, map_zero] at this`.

Rewrite `this` using `[Finset.sum_eq_single j]`. Simplify `this` using `[← Algebra.TensorProduct.one_def]`. Introduce `i _ hij`. Simplify using `[Finsupp.single_apply, hij]`. Simplify using the standard rewrite rules.

Introduce and unpack `y -`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add y y' h h' => exact add_mem h h'`. Consider the case `tmul l s`.

Rewrite using `[← b.sum_repr l, TensorProduct.sum_tmul]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `: (b.repr l i • b i) ⊗ₜ[F] s = (b.repr l i ⊗ₜ[F] s) • (b i ⊗ₜ[F] (1 : k))`. Rewrite using `[Algebra.smul_def (b.repr l i ⊗ₜ[F] s), algebraMap_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.smul_def]`. Both sides reduce to the same expression.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem exists_basis_tensor {ι : Type} [Fintype ι] (b : Module.Basis ι E (AdjoinRoot P)) :
    ∃ b' : Module.Basis ι (E ⊗[F] k) (AdjoinRoot P ⊗[F] k), ∀ i, b' i = b i ⊗ₜ 1 := by
  classical
  refine ⟨Module.Basis.mk (v := fun i => b i ⊗ₜ 1) ?_ ?_, fun i => Module.Basis.mk_apply _ _ _⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg j
    have := congrArg (TensorProduct.map ((b.coord j).restrictScalars F) LinearMap.id) hg
    simp only [map_sum, map_smul_tensor, map_zero] at this
    rw [Finset.sum_eq_single j] at this
    · simpa [← Algebra.TensorProduct.one_def] using this
    · intro i _ hij; simp [Finsupp.single_apply, hij]
    · simp
  · rintro y -
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' h h' => exact add_mem h h'
    | tmul l s =>
      rw [← b.sum_repr l, TensorProduct.sum_tmul]
      refine Submodule.sum_mem _ fun i _ => ?_
      have : (b.repr l i • b i) ⊗ₜ[F] s = (b.repr l i ⊗ₜ[F] s) • (b i ⊗ₜ[F] (1 : k)) := by
        rw [Algebra.smul_def (b.repr l i ⊗ₜ[F] s), algebraMap_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.smul_def]
        rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Take `⟨b', hb'⟩` from `exists_basis_tensor (F := F) k b`. Conclude with `trace_transfer (inclE (F := F) k) (inclE (F := F) k) (fun _ => rfl) b b' (fun i => (hb' i).symm) l`.
-/
theorem trace_tmul_one {ι : Type} [Fintype ι] (b : Module.Basis ι E (AdjoinRoot P))
    (l : AdjoinRoot P) : Algebra.trace (E ⊗[F] k) (AdjoinRoot P ⊗[F] k) (l ⊗ₜ 1)
      = Algebra.trace E (AdjoinRoot P) l ⊗ₜ 1 := by
  classical
  obtain ⟨b', hb'⟩ := exists_basis_tensor (F := F) k b
  exact trace_transfer (inclE (F := F) k) (inclE (F := F) k) (fun _ => rfl) b b'
    (fun i => (hb' i).symm) l

/- English proof (translation)
Take `⟨b', hb'⟩` from `exists_basis_tensor (F := F) k b`. Rewrite using `[← b'.sum_repr y, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[trLk, map_smul_tensor, map_smul, hb', trace_tmul_one k b]`. Simplify using the standard rewrite rules.
-/
theorem trLk_eq {ι : Type} [Fintype ι] (b : Module.Basis ι E (AdjoinRoot P))
    (y : AdjoinRoot P ⊗[F] k) : trLk k P y = Algebra.trace (E ⊗[F] k) (AdjoinRoot P ⊗[F] k) y := by
  obtain ⟨b', hb'⟩ := exists_basis_tensor (F := F) k b
  rw [← b'.sum_repr y, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [trLk, map_smul_tensor, map_smul, hb', trace_tmul_one k b]
  simp

/- English proof (translation)
Take `⟨h1, h2, rfl, -⟩` from `hP`. Use `⟨(AdjoinRoot.powerBasis' h1).basis, (AdjoinRoot.powerBasis' h1).basis_eq_pow, ?_⟩` and prove the remaining obligations. Use `(charpoly_leftMulMatrix (AdjoinRoot.powerBasis' h1)).trans ?_` and prove the remaining obligations. Use `show minpoly E (AdjoinRoot.root P) = P`. Rewrite using `[AdjoinRoot.minpoly_root h1.ne_zero, h1.leadingCoeff]`.

Simplify using the standard rewrite rules.
-/
theorem exists_pow_basis (hP : IsPPol c r P) : ∃ b : Module.Basis (Fin r) E (AdjoinRoot P),
    (∀ i, b i = AdjoinRoot.root P ^ (i : ℕ)) ∧
      (Algebra.leftMulMatrix b (AdjoinRoot.root P)).charpoly = P := by
  obtain ⟨h1, h2, rfl, -⟩ := hP
  refine ⟨(AdjoinRoot.powerBasis' h1).basis, (AdjoinRoot.powerBasis' h1).basis_eq_pow, ?_⟩
  refine (charpoly_leftMulMatrix (AdjoinRoot.powerBasis' h1)).trans ?_
  show minpoly E (AdjoinRoot.root P) = P
  rw [AdjoinRoot.minpoly_root h1.ne_zero, h1.leadingCoeff]
  simp

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add y y' h h' => rw [map_add, map_add, h, h']`. Consider the case `tmul l t => simp [sigR, hs]`.
-/
theorem sigR_invol {L : Type} [CommRing L] [Algebra F L] (s : L →ₐ[F] L) (hs : ∀ l, s (s l) = l)
    (y : L ⊗[F] k) : sigR s k (sigR s k y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y y' h h' => rw [map_add, map_add, h, h']
  | tmul l t => simp [sigR, hs]

/- English proof (translation)
Use `haveI : Fact (Irreducible P) := ⟨hP.2.1⟩`. Take `⟨b, hb, hch⟩` from `exists_pow_basis hP`. Take `⟨b', hb'⟩` from `exists_basis_tensor (F := F) k b`. Use `haveI := Module.Finite.of_basis b`. Use `⟨b', ⟨sigR_invol k _ hc, sigR_invol k _ (starL_starL hP hc), ?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `a`. Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add y y' h h' => simp only [map_add, h, h']`. Consider the case `tmul e t => simp [starLk, sigR, algebraMap_tmul, starL_of]`.

Establish `: AdjoinRoot.root P * (((alpha hP)⁻¹ : (AdjoinRoot P)ˣ) : AdjoinRoot P) = 1` using `(alpha hP).mul_inv show _ * (starL hP (AdjoinRoot.root P) ⊗ₜ[F] (1 : k)) = 1`. Rewrite using `[starL_root, Algebra.TensorProduct.tmul_mul_tmul, this, mul_one]`. Both sides reduce to the same expression. Introduce `i`. Rewrite using `[hb', hb, Algebra.TensorProduct.tmul_pow, one_pow]`.

Establish `: Algebra.traceMatrix (E ⊗[F] k) b' = (Algebra.traceMatrix E b).map (inclE (F` using `F) k) := by`. Use extensionality with `i j`. Simplify using `only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.map_apply, hb', Algebra.TensorProduct.tmul_mul_tmul, mul_one, trace_tmul_one k b]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Establish `h` using `(Algebra.discr_isUnit_of_basis E b).map (inclE (F := F) k)`. Rewrite `h` using `[Algebra.discr_def, RingHom.map_det]`. Conclude with `h`. Use `Eq.trans ?_ (congrArg (Polynomial.map (inclE (F := F) k)) hch)` and prove the remaining obligations. Rewrite using `[← Matrix.charpoly_map]`.

Use `congr 1`. Conclude with `leftMulMatrix_transfer (inclE (F := F) k) (inclE (F := F) k) (fun _ => rfl) b b' (fun i => (hb' i).symm) _`.
-/
theorem exists_setting [CharZero E] (hP : IsPPol c r P) (hc : ∀ e, c (c e) = e) :
    ∃ b : Module.Basis (Fin r) (E ⊗[F] k) (AdjoinRoot P ⊗[F] k),
      HidaSetting (sigR (c : E →ₐ[F] E) k) (starLk k hP) (AdjoinRoot.root P ⊗ₜ[F] (1 : k)) b ∧
      (Algebra.leftMulMatrix b (AdjoinRoot.root P ⊗ₜ[F] (1 : k))).charpoly
        = P.map (inclE (F := F) k) := by
  haveI : Fact (Irreducible P) := ⟨hP.2.1⟩
  obtain ⟨b, hb, hch⟩ := exists_pow_basis hP
  obtain ⟨b', hb'⟩ := exists_basis_tensor (F := F) k b
  haveI := Module.Finite.of_basis b
  refine ⟨b', ⟨sigR_invol k _ hc, sigR_invol k _ (starL_starL hP hc), ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add y y' h h' => simp only [map_add, h, h']
    | tmul e t => simp [starLk, sigR, algebraMap_tmul, starL_of]
  · have : AdjoinRoot.root P * (((alpha hP)⁻¹ : (AdjoinRoot P)ˣ) : AdjoinRoot P) = 1 :=
      (alpha hP).mul_inv
    show _ * (starL hP (AdjoinRoot.root P) ⊗ₜ[F] (1 : k)) = 1
    rw [starL_root, Algebra.TensorProduct.tmul_mul_tmul, this, mul_one]
    rfl
  · intro i; rw [hb', hb, Algebra.TensorProduct.tmul_pow, one_pow]
  · have : Algebra.traceMatrix (E ⊗[F] k) b' = (Algebra.traceMatrix E b).map (inclE (F := F) k) := by
      ext i j
      simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.map_apply, hb',
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, trace_tmul_one k b]
      rfl
    rw [this]
    have h := (Algebra.discr_isUnit_of_basis E b).map (inclE (F := F) k)
    rw [Algebra.discr_def, RingHom.map_det] at h
    exact h
  · refine Eq.trans ?_ (congrArg (Polynomial.map (inclE (F := F) k)) hch)
    rw [← Matrix.charpoly_map]
    congr 1
    exact leftMulMatrix_transfer (inclE (F := F) k) (inclE (F := F) k) (fun _ => rfl) b b'
      (fun i => (hb' i).symm) _

/- English proof (translation)
Establish `he : Function.Exact i (s - LinearMap.id : V →ₗ[F] V)` using `fun v => by`. Rewrite using `[LinearMap.sub_apply, sub_eq_zero]`. Conclude with `h v`. Use `Module.Flat.rTensor_exact k he z` as an intermediate fact. Simplify `this` using `[LinearMap.rTensor_sub, sub_eq_zero]`.
-/
theorem fixed_tensor {W V : Type} [AddCommGroup W] [AddCommGroup V] [Module F W] [Module F V]
    (i : W →ₗ[F] V) (s : V →ₗ[F] V) (h : ∀ v, s v = v ↔ ∃ w, i w = v) (z : V ⊗[F] k) :
    s.rTensor k z = z ↔ ∃ w, i.rTensor k w = z := by
  have he : Function.Exact i (s - LinearMap.id : V →ₗ[F] V) := fun v => by
    rw [LinearMap.sub_apply, sub_eq_zero]; exact h v
  have := Module.Flat.rTensor_exact k he z
  simpa [LinearMap.rTensor_sub, sub_eq_zero] using this

/- English proof (translation)
The claim follows from `Module.Flat.rTensor_preserves_injective_linearMap (M := k) (Lplus hP).val.toLinearMap Subtype.val_injective`.
-/
theorem inclPlus_injective (hP : IsPPol c r P) : Function.Injective (inclPlus k hP) :=
  Module.Flat.rTensor_preserves_injective_linearMap (M := k) (Lplus hP).val.toLinearMap
    Subtype.val_injective

/- English proof (translation)
The claim follows from `fixed_tensor k (Lplus hP).val.toLinearMap (starL hP).toLinearMap (fun v => ⟨fun h => ⟨⟨v, h⟩, rfl⟩, by rintro ⟨w, rfl⟩; exact w.2⟩) z`.
-/
theorem star_fixed_iff (hP : IsPPol c r P) (z : AdjoinRoot P ⊗[F] k) :
    starLk k hP z = z ↔ ∃ w, inclPlus k hP w = z :=
  fixed_tensor k (Lplus hP).val.toLinearMap (starL hP).toLinearMap
    (fun v => ⟨fun h => ⟨⟨v, h⟩, rfl⟩, by rintro ⟨w, rfl⟩; exact w.2⟩) z

/- English proof (translation)
Take `⟨w, rfl⟩` from `(fixed_tensor k (Algebra.linearMap F E) c.toLinearMap (fun v => ⟨hF v, by rintro ⟨w, rfl⟩; simp⟩) z).1 hz`. Use `⟨TensorProduct.lid F k w, ?_⟩` and prove the remaining obligations. Use `clear hz`. Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add y y' h h' => rw [map_add, map_add, tmul_add, h, h']`. Consider the case `tmul a t => simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`.
-/
theorem sig_fixed (hF : ∀ e, c e = e → ∃ a, algebraMap F E a = e) (z : E ⊗[F] k)
    (hz : sigR (c : E →ₐ[F] E) k z = z) : ∃ d : k, (1 : E) ⊗ₜ[F] d = z := by
  obtain ⟨w, rfl⟩ := (fixed_tensor k (Algebra.linearMap F E) c.toLinearMap
    (fun v => ⟨hF v, by rintro ⟨w, rfl⟩; simp⟩) z).1 hz
  refine ⟨TensorProduct.lid F k w, ?_⟩
  clear hz
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add y y' h h' => rw [map_add, map_add, tmul_add, h, h']
  | tmul a t => simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

/- English proof (translation)
Take `⟨u, rfl⟩` from `hu`. Take `⟨w, hw⟩` from `(star_fixed_iff k hP _).1 hx`. Establish `h2 : starLk k hP ((u⁻¹ : _ˣ) : AdjoinRoot P ⊗[F] k) = (u⁻¹ : _ˣ)`. Apply `Units.eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← hx, ← map_mul, Units.mul_inv, map_one]`.

Take `⟨w', hw'⟩` from `(star_fixed_iff k hP _).1 h2`. Establish `h3 : w * w' = 1` using `inclPlus_injective k hP (by rw [map_mul, hw, hw', map_one, Units.mul_inv])`. Conclude with `⟨Units.mkOfMulEqOne w w' h3, hw⟩`.
-/
theorem exists_unit_plus (hP : IsPPol c r P) {x : AdjoinRoot P ⊗[F] k} (hu : IsUnit x)
    (hx : starLk k hP x = x) : ∃ x₀ : (Lplus hP ⊗[F] k)ˣ, inclPlus k hP x₀ = x := by
  obtain ⟨u, rfl⟩ := hu
  obtain ⟨w, hw⟩ := (star_fixed_iff k hP _).1 hx
  have h2 : starLk k hP ((u⁻¹ : _ˣ) : AdjoinRoot P ⊗[F] k) = (u⁻¹ : _ˣ) := by
    apply Units.eq_inv_of_mul_eq_one_left
    rw [← hx, ← map_mul, Units.mul_inv, map_one]
  obtain ⟨w', hw'⟩ := (star_fixed_iff k hP _).1 h2
  have h3 : w * w' = 1 := inclPlus_injective k hP (by rw [map_mul, hw, hw', map_one, Units.mul_inv])
  exact ⟨Units.mkOfMulEqOne w w' h3, hw⟩

/- English proof (translation)
Rewrite using `[QuotientGroup.eq, normL, Subgroup.mem_comap, MonoidHom.mem_range]`. Use `exists_congr fun z => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_inv, eq_inv_mul_iff_mul_eq, eq_comm, Units.ext_iff]`. Both sides reduce to the same expression.
-/
theorem mk_eq_iff_normL (hP : IsPPol c r P) (x x' : (Lplus hP ⊗[F] k)ˣ) :
    (QuotientGroup.mk x : _ ⧸ normL k hP) = QuotientGroup.mk x' ↔
      ∃ z : (AdjoinRoot P ⊗[F] k)ˣ,
        inclPlus k hP x' = inclPlus k hP x * (z * starLk k hP z) := by
  rw [QuotientGroup.eq, normL, Subgroup.mem_comap, MonoidHom.mem_range]
  refine exists_congr fun z => ?_
  rw [map_mul, map_inv, eq_inv_mul_iff_mul_eq, eq_comm, Units.ext_iff]
  rfl

/- English proof (translation)
Rewrite using `[QuotientGroup.eq, normE, Subgroup.mem_comap, MonoidHom.mem_range]`. Use `exists_congr fun z => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_inv, eq_inv_mul_iff_mul_eq, eq_comm, Units.ext_iff]`. Both sides reduce to the same expression.
-/
theorem mk_eq_iff_normE (d d' : kˣ) :
    (QuotientGroup.mk d : _ ⧸ normE k c) = QuotientGroup.mk d' ↔
      ∃ z : (E ⊗[F] k)ˣ,
        (1 : E) ⊗ₜ[F] (d' : k) = (1 : E) ⊗ₜ[F] (d : k) * (z * sigR (c : E →ₐ[F] E) k z) := by
  rw [QuotientGroup.eq, normE, Subgroup.mem_comap, MonoidHom.mem_range]
  refine exists_congr fun z => ?_
  rw [map_mul, map_inv, eq_inv_mul_iff_mul_eq, eq_comm, Units.ext_iff]
  rfl

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨e₀, he₀⟩ : ∃ e, c e ≠ e := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hc1 (AlgEquiv.ext h)`. Use `set δ := e₀ - c e₀ with hδ`.

Establish `hδ0 : δ ≠ 0` using `sub_ne_zero.2 he₀.symm`. Establish `hcδ : c δ = -δ` using `by rw [hδ, map_sub, hc, neg_sub]`. Establish `hsm : ∀ (e : E) (l : AdjoinRoot P), starL hP (e • l) = c e • starL hP l` using `fun e l => by`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul]`. Conclude with `congrArg (· * _) (starL_of hP e)`.

Establish `hfix : ∀ i, starL hP (b i) = b i` using `fun i => (b i).2`. Use `⟨Module.Basis.mk (v := fun i => (b i : AdjoinRoot P)) ?_ ?_, fun i => Module.Basis.mk_apply _ _ _⟩` and prove the remaining obligations. Establish `key : ∀ g : ι → E, ∑ i, g i • (b i : AdjoinRoot P) = 0 → ∀ j, g j + c (g j) = 0`. Introduce `g hg j`. Establish `h1` using `congrArg (starL hP) hg`.

Simplify using `only [map_sum, hsm, hfix, map_zero] at h1`. Use `choose a ha using fun i => hF (g i + c (g i)) (by rw [map_add, hc, add_comm])`. Establish `h2 : ∑ i, a i • b i = 0`. Apply `Subtype.val_injective` to reduce the goal to its premises. Establish `: ∑ i, a i • (b i : AdjoinRoot P) = 0`.

Simplify using `only [← IsScalarTower.algebraMap_smul E (a _), ha, add_smul, Finset.sum_add_distrib, hg, h1, add_zero]`. Simplify using `using this`. Rewrite using `[← ha, Fintype.linearIndependent_iff.1 b.linearIndependent a h2 j, map_zero]`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg j`.

Establish `h1` using `key g hg j`. Establish `h2` using `key (fun i => δ * g i) (by`. Simplify using `only [mul_smul, ← Finset.smul_sum, hg, smul_zero]) j`. Rewrite `h2` using `[map_mul, hcδ]`. Establish `: (2 * δ) * g j = 0` using `by linear_combination δ * h1 + h2`.

Conclude with `(mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero hδ0)`. Establish `key : ∀ l, starL hP l = l → l ∈ Submodule.span E (Set.range fun i => (b i : AdjoinRoot P))`. Introduce `l hl`. Establish `h` using `congrArg Subtype.val (b.sum_repr ⟨l, hl⟩)`. Simplify using `only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at h`.

Rewrite using `[← h]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Introduce and unpack `l -`. Establish `h1` using `key (l + starL hP l) (by rw [map_add, starL_starL hP hc, add_comm])`. Establish `h2` using `key (δ • (l - starL hP l)) (by`.

Rewrite using `[hsm, hcδ, map_sub, starL_starL hP hc, neg_smul, ← smul_neg, neg_sub])`. Establish `: l = (2 : E)⁻¹ • ((l + starL hP l) + δ⁻¹ • δ • (l - starL hP l))`. Rewrite using `[inv_smul_smul₀ hδ0, add_add_sub_cancel, ← two_smul E l, inv_smul_smul₀ two_ne_zero]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (add_mem h1 (Submodule.smul_mem _ _ h2))`.
-/
theorem exists_basis_plus [CharZero E] (hP : IsPPol c r P) (hc : ∀ e, c (c e) = e) (hc1 : c ≠ 1)
    (hF : ∀ e, c e = e → ∃ a, algebraMap F E a = e) {ι : Type} [Fintype ι]
    (b : Module.Basis ι F (Lplus hP)) :
    ∃ b' : Module.Basis ι E (AdjoinRoot P), ∀ i, b' i = b i := by
  obtain ⟨e₀, he₀⟩ : ∃ e, c e ≠ e := by
    by_contra h
    push Not at h
    exact hc1 (AlgEquiv.ext h)
  set δ := e₀ - c e₀ with hδ
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 he₀.symm
  have hcδ : c δ = -δ := by rw [hδ, map_sub, hc, neg_sub]
  have hsm : ∀ (e : E) (l : AdjoinRoot P), starL hP (e • l) = c e • starL hP l := fun e l => by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    exact congrArg (· * _) (starL_of hP e)
  have hfix : ∀ i, starL hP (b i) = b i := fun i => (b i).2
  refine ⟨Module.Basis.mk (v := fun i => (b i : AdjoinRoot P)) ?_ ?_,
    fun i => Module.Basis.mk_apply _ _ _⟩
  · have key : ∀ g : ι → E, ∑ i, g i • (b i : AdjoinRoot P) = 0 → ∀ j, g j + c (g j) = 0 := by
      intro g hg j
      have h1 := congrArg (starL hP) hg
      simp only [map_sum, hsm, hfix, map_zero] at h1
      choose a ha using fun i => hF (g i + c (g i)) (by rw [map_add, hc, add_comm])
      have h2 : ∑ i, a i • b i = 0 := by
        apply Subtype.val_injective
        have : ∑ i, a i • (b i : AdjoinRoot P) = 0 := by
          simp only [← IsScalarTower.algebraMap_smul E (a _), ha, add_smul,
            Finset.sum_add_distrib, hg, h1, add_zero]
        simpa using this
      rw [← ha, Fintype.linearIndependent_iff.1 b.linearIndependent a h2 j, map_zero]
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 := key g hg j
    have h2 := key (fun i => δ * g i) (by
      simp only [mul_smul, ← Finset.smul_sum, hg, smul_zero]) j
    rw [map_mul, hcδ] at h2
    have : (2 * δ) * g j = 0 := by linear_combination δ * h1 + h2
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero hδ0)
  · have key : ∀ l, starL hP l = l →
        l ∈ Submodule.span E (Set.range fun i => (b i : AdjoinRoot P)) := by
      intro l hl
      have h := congrArg Subtype.val (b.sum_repr ⟨l, hl⟩)
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at h
      rw [← h]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rintro l -
    have h1 := key (l + starL hP l) (by rw [map_add, starL_starL hP hc, add_comm])
    have h2 := key (δ • (l - starL hP l)) (by
      rw [hsm, hcδ, map_sub, starL_starL hP hc, neg_smul, ← smul_neg, neg_sub])
    have : l = (2 : E)⁻¹ • ((l + starL hP l) + δ⁻¹ • δ • (l - starL hP l)) := by
      rw [inv_smul_smul₀ hδ0, add_add_sub_cancel, ← two_smul E l, inv_smul_smul₀ two_ne_zero]
    rw [this]
    exact Submodule.smul_mem _ _ (add_mem h1 (Submodule.smul_mem _ _ h2))

/- English proof (translation)
Take `⟨b₀, -⟩` from `exists_pow_basis hP`. Use `haveI := Module.Finite.of_basis b₀`. Use `haveI : Module.Finite F (AdjoinRoot P) := Module.Finite.trans E _`. Use `haveI : Module.Finite F (Lplus hP) := Module.Finite.of_injective (Lplus hP).val.toLinearMap Subtype.val_injective`. Set `b` to `Module.finBasis F (Lplus hP)`.

Take `⟨b1, hb1⟩` from `exists_basis_plus hP hc hc1 hF b`. Take `⟨b2, hb2⟩` from `exists_basis_tensor (F := F) k b1`. Use `norm_transfer (Algebra.TensorProduct.includeRight : k →ₐ[F] E ⊗[F] k).toRingHom ((inclPlus k hP).comp (Algebra.TensorProduct.comm F k (Lplus hP)).toAlgHom.toRingHom) (fun a => by simp [inclPlus, algebraMap_tmul]) (Algebra.TensorProduct.basis k b) b2 (fun i => by simp [inclPlus, h …` as an intermediate fact. Use `Eq.trans ?_ this` and prove the remaining obligations. Use `congr 1`.

Use `show _ = inclPlus k hP ((Algebra.TensorProduct.comm F (Lplus hP) k).symm _)`. Rewrite using `[AlgEquiv.symm_apply_apply]`.
-/
theorem norm_inclPlus [CharZero E] [FiniteDimensional F E] (hP : IsPPol c r P)
    (hc : ∀ e, c (c e) = e) (hc1 : c ≠ 1)
    (hF : ∀ e, c e = e → ∃ a, algebraMap F E a = e) (x : (Lplus hP ⊗[F] k)ˣ) :
    Algebra.norm (E ⊗[F] k) (inclPlus k hP x) = (1 : E) ⊗ₜ[F] (normPlus hP x : k) := by
  classical
  obtain ⟨b₀, -⟩ := exists_pow_basis hP
  haveI := Module.Finite.of_basis b₀
  haveI : Module.Finite F (AdjoinRoot P) := Module.Finite.trans E _
  haveI : Module.Finite F (Lplus hP) :=
    Module.Finite.of_injective (Lplus hP).val.toLinearMap Subtype.val_injective
  let b := Module.finBasis F (Lplus hP)
  obtain ⟨b1, hb1⟩ := exists_basis_plus hP hc hc1 hF b
  obtain ⟨b2, hb2⟩ := exists_basis_tensor (F := F) k b1
  have := norm_transfer (Algebra.TensorProduct.includeRight : k →ₐ[F] E ⊗[F] k).toRingHom
    ((inclPlus k hP).comp (Algebra.TensorProduct.comm F k (Lplus hP)).toAlgHom.toRingHom)
    (fun a => by simp [inclPlus, algebraMap_tmul]) (Algebra.TensorProduct.basis k b) b2
    (fun i => by simp [inclPlus, hb2, hb1])
    (Algebra.TensorProduct.comm F (Lplus hP) k x)
  refine Eq.trans ?_ this
  congr 1
  show _ = inclPlus k hP ((Algebra.TensorProduct.comm F (Lplus hP) k).symm _)
  rw [AlgEquiv.symm_apply_apply]

/- English proof (translation)
Introduce `J hJ hd`. Take `⟨b, S, hch⟩` from `exists_setting k hP hc`. Take `⟨b₀, -⟩` from `exists_pow_basis hP`. Use `haveI : IsArtinianRing (k ⊗[F] E) := IsArtinianRing.of_finite k _`. Use `haveI : IsArtinianRing (E ⊗[F] k) := (Algebra.TensorProduct.comm F k E).toRingEquiv.isArtinianRing`.

Apply the tactic sequence `have hiso : ∀ x φ, IsIsometry hP J x φ ↔ Iso (sigR (c : E →ₐ[F] E) k) (starLk k hP) J (inclPlus k hP x) φ := by`. Introduce `x φ`. Simplify using `only [IsIsometry, Iso, hU, hx, tf, trLk_eq k b₀]`. Apply the tactic sequence `let Rel : (Lplus hP ⊗[F] k)ˣ ⧸ normL k hP → UJ (sigR (c : E →ₐ[F] E) k) J → Prop := fun ξ g => ∃ x φ, QuotientGroup.mk x = ξ ∧ IsIsometry hP J x φ ∧ Intw (AdjoinRoot.root P ⊗ₜ[F] (1 : k)) ((g : GL (Fin r) (E ⊗[F] k)) : Matrix (Fin r) (Fin r) (E ⊗[F] k)) φ`. Establish `hRel : ∀ ξ ξ' g g', Rel ξ g → Rel ξ' g' → (ξ = ξ' ↔ ConjClasses.mk g = ConjClasses.mk g')`.

Introduce and unpack `_ _ g g' ⟨x, φ, rfl, h1, h2⟩ ⟨x', φ', rfl, h1', h2'⟩`. Rewrite using `[ConjClasses.mk_eq_mk_iff_isConj, mk_eq_iff_normL]`. Rewrite `h1`, `h1'` using `[hiso]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz⟩`.

Rewrite `h1'` using `[hz]`. Conclude with `isConj_of_iso (h1.mul z) h1' (h2.mul z) h2'`. Introduce `h`. Conclude with `S.norm_of_isConj h1 h1' h2 h2' h.symm`. Set `Φ : (Lplus hP ⊗[F] k)ˣ ⧸ normL k hP → ConjClasses (UJ (sigR (c : E →ₐ[F] E) k) J)` to `fun ξ => if h : ∃ g, Rel ξ g then ConjClasses.mk h.choose else ConjClasses.mk 1`.

Establish `hΦ : ∀ ξ g, Rel ξ g → Φ ξ = ConjClasses.mk g`. Introduce `ξ g h`. Establish `h' : ∃ g, Rel ξ g` using `⟨g, h⟩`. Simplify using `only [Φ, dif_pos h']`. Conclude with `(hRel _ _ _ _ h'.choose_spec h).1 rfl`.

Establish `hex : ∀ ξ ∈ Xk hP J, ∃ g, Rel ξ g`. Introduce and unpack `_ ⟨x, rfl, φ, h⟩`. Take `⟨g, hg⟩` from `S.exists_intw ((hiso x φ).1 h)`. Conclude with `⟨g, x, φ, rfl, h, hg⟩`. Use `⟨?_, Φ, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `x ⟨x', hx', φ, h⟩`. Take `⟨z, hz⟩` from `(mk_eq_iff_normL k hP _ _).1 hx'`. Conclude with `⟨_, (hiso _ _).2 (hz ▸ ((hiso _ _).1 h).mul z)⟩`. Introduce `x φ h`. Take `⟨g, hg⟩` from `S.exists_intw ((hiso x φ).1 h)`.

Conclude with `⟨g, hg, hΦ _ _ ⟨x, φ, rfl, h, hg⟩⟩`. Introduce `ξ hξ`. Take `⟨g, hg⟩` from `hex ξ hξ`. Use `⟨g, (hΦ _ _ hg).symm, ?_⟩` and prove the remaining obligations. Take `⟨x, φ, -, -, h⟩` from `hg`.

Rewrite using `[charpoly_of_intw b h, hch]`. Introduce `ξ hξ ξ' hξ' h`. Take `⟨g, hg⟩` from `hex ξ hξ`. Take `⟨g', hg'⟩` from `hex ξ' hξ'`. Rewrite `h` using `[hΦ _ _ hg, hΦ _ _ hg']`.

Conclude with `(hRel _ _ _ _ hg hg').2 h`. Introduce and unpack `_ ⟨g, rfl, hg⟩`. Take `⟨x, φ, hu, hx, h1, h2⟩` from `S.exists_of_charpoly hJ hd g (hg.trans hch.symm) (by rw [hch]; exact hP.2.1.separable.map)`. Take `⟨x₀, rfl⟩` from `exists_unit_plus k hP hu hx`. Establish `h3` using `(hiso _ _).2 h1`.

Conclude with `⟨QuotientGroup.mk x₀, ⟨x₀, rfl, φ, h3⟩, hΦ _ _ ⟨x₀, φ, rfl, h3, h2⟩⟩`.
-/
theorem classParamAt [CharZero E] [FiniteDimensional F E] (hP : IsPPol c r P)
    (hc : ∀ e, c (c e) = e) : ClassParamAt k hP := by
  classical
  intro J hJ hd
  obtain ⟨b, S, hch⟩ := exists_setting k hP hc
  obtain ⟨b₀, -⟩ := exists_pow_basis hP
  haveI : IsArtinianRing (k ⊗[F] E) := IsArtinianRing.of_finite k _
  haveI : IsArtinianRing (E ⊗[F] k) :=
    (Algebra.TensorProduct.comm F k E).toRingEquiv.isArtinianRing
  have hiso : ∀ x φ, IsIsometry hP J x φ ↔
      Iso (sigR (c : E →ₐ[F] E) k) (starLk k hP) J (inclPlus k hP x) φ := by
    intro x φ
    simp only [IsIsometry, Iso, hU, hx, tf, trLk_eq k b₀]
  let Rel : (Lplus hP ⊗[F] k)ˣ ⧸ normL k hP → UJ (sigR (c : E →ₐ[F] E) k) J → Prop := fun ξ g =>
    ∃ x φ, QuotientGroup.mk x = ξ ∧ IsIsometry hP J x φ ∧
      Intw (AdjoinRoot.root P ⊗ₜ[F] (1 : k))
        ((g : GL (Fin r) (E ⊗[F] k)) : Matrix (Fin r) (Fin r) (E ⊗[F] k)) φ
  have hRel : ∀ ξ ξ' g g', Rel ξ g → Rel ξ' g' →
      (ξ = ξ' ↔ ConjClasses.mk g = ConjClasses.mk g') := by
    rintro _ _ g g' ⟨x, φ, rfl, h1, h2⟩ ⟨x', φ', rfl, h1', h2'⟩
    rw [ConjClasses.mk_eq_mk_iff_isConj, mk_eq_iff_normL]
    rw [hiso] at h1 h1'
    constructor
    · rintro ⟨z, hz⟩
      rw [hz] at h1'
      exact isConj_of_iso (h1.mul z) h1' (h2.mul z) h2'
    · intro h
      exact S.norm_of_isConj h1 h1' h2 h2' h.symm
  let Φ : (Lplus hP ⊗[F] k)ˣ ⧸ normL k hP → ConjClasses (UJ (sigR (c : E →ₐ[F] E) k) J) :=
    fun ξ => if h : ∃ g, Rel ξ g then ConjClasses.mk h.choose else ConjClasses.mk 1
  have hΦ : ∀ ξ g, Rel ξ g → Φ ξ = ConjClasses.mk g := by
    intro ξ g h
    have h' : ∃ g, Rel ξ g := ⟨g, h⟩
    simp only [Φ, dif_pos h']
    exact (hRel _ _ _ _ h'.choose_spec h).1 rfl
  have hex : ∀ ξ ∈ Xk hP J, ∃ g, Rel ξ g := by
    rintro _ ⟨x, rfl, φ, h⟩
    obtain ⟨g, hg⟩ := S.exists_intw ((hiso x φ).1 h)
    exact ⟨g, x, φ, rfl, h, hg⟩
  refine ⟨?_, Φ, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨x', hx', φ, h⟩
    obtain ⟨z, hz⟩ := (mk_eq_iff_normL k hP _ _).1 hx'
    exact ⟨_, (hiso _ _).2 (hz ▸ ((hiso _ _).1 h).mul z)⟩
  · intro x φ h
    obtain ⟨g, hg⟩ := S.exists_intw ((hiso x φ).1 h)
    exact ⟨g, hg, hΦ _ _ ⟨x, φ, rfl, h, hg⟩⟩
  · intro ξ hξ
    obtain ⟨g, hg⟩ := hex ξ hξ
    refine ⟨g, (hΦ _ _ hg).symm, ?_⟩
    obtain ⟨x, φ, -, -, h⟩ := hg
    rw [charpoly_of_intw b h, hch]
  · intro ξ hξ ξ' hξ' h
    obtain ⟨g, hg⟩ := hex ξ hξ
    obtain ⟨g', hg'⟩ := hex ξ' hξ'
    rw [hΦ _ _ hg, hΦ _ _ hg'] at h
    exact (hRel _ _ _ _ hg hg').2 h
  · rintro _ ⟨g, rfl, hg⟩
    obtain ⟨x, φ, hu, hx, h1, h2⟩ := S.exists_of_charpoly hJ hd g (hg.trans hch.symm)
      (by rw [hch]; exact hP.2.1.separable.map)
    obtain ⟨x₀, rfl⟩ := exists_unit_plus k hP hu hx
    have h3 := (hiso _ _).2 h1
    exact ⟨QuotientGroup.mk x₀, ⟨x₀, rfl, φ, h3⟩, hΦ _ _ ⟨x₀, φ, rfl, h3, h2⟩⟩

/- English proof (translation)
Take `⟨b, S, -⟩` from `exists_setting k hP hc`. Take `⟨b₀, -⟩` from `exists_pow_basis hP`. Establish `hg : ∀ (x : (Lplus hP ⊗[F] k)ˣ) (e : Module.Basis (Fin r) (E ⊗[F] k) (AdjoinRoot P ⊗[F] k)), (Matrix.of fun i j => hx k hP x (e i) (e j)) = gram (starLk k hP) (inclPlus k hP x) e`. Introduce `x e`. Simplify using `only [gram, hx, tf, trLk_eq k b₀]`.

Establish `hmul : ∀ x δ δ₁, IsDisc hP x δ → IsDisc hP 1 δ₁ → δ = QuotientGroup.mk (normPlus (k` using `k) hP x) * δ₁ := by`. Introduce and unpack `x _ _ ⟨e, d, hd, rfl⟩ ⟨e₁, d₁, hd₁, rfl⟩`. Rewrite using `[← QuotientGroup.mk_mul, eq_comm, mk_eq_iff_normE]`. Take `⟨z, hz⟩` from `S.det_gram_change 1 e₁ e`. Use `⟨z, ?_⟩` and prove the remaining obligations.

Rewrite `hd₁` using `[hg, Units.val_one, map_one]`. Rewrite using `[hd, hg, det_gram, hz, ← hd₁, norm_inclPlus k hP hc hc1 hF, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Units.val_mul]`. Establish `hex : ∀ x : (Lplus hP ⊗[F] k)ˣ, ∃ δ, IsDisc hP x δ`. Introduce `x`. Take `⟨d, hd⟩` from `sig_fixed k hF _ (S.det_gram_fixed ((star_fixed_iff k hP _).2 ⟨(x : Lplus hP ⊗[F] k), rfl⟩) b)`.

Establish `hu` using `S.isUnit_det_gram (x.isUnit.map (inclPlus k hP))`. Establish `hd0 : d ≠ 0`. Introduce and unpack `rfl`. Rewrite `hu` using `[← hd, tmul_zero]`. Conclude with `not_isUnit_zero hu`.

Conclude with `⟨_, b, Units.mk0 d hd0, by rw [hg]; exact hd, rfl⟩`. Introduce `x`. Use `⟨?_, hmul x⟩` and prove the remaining obligations. Take `⟨δ, hδ⟩` from `hex x`. Take `⟨δ₁, hδ₁⟩` from `hex 1`.

Conclude with `⟨δ, hδ, fun δ' hδ' => (hmul x δ' δ₁ hδ' hδ₁).trans (hmul x δ δ₁ hδ hδ₁).symm⟩`.
-/
theorem discAt [CharZero E] [FiniteDimensional F E] (hP : IsPPol c r P)
    (hc : ∀ e, c (c e) = e) (hc1 : c ≠ 1) (hF : ∀ e, c e = e → ∃ a, algebraMap F E a = e) :
    DiscAt k hP := by
  obtain ⟨b, S, -⟩ := exists_setting k hP hc
  obtain ⟨b₀, -⟩ := exists_pow_basis hP
  have hg : ∀ (x : (Lplus hP ⊗[F] k)ˣ)
      (e : Module.Basis (Fin r) (E ⊗[F] k) (AdjoinRoot P ⊗[F] k)),
      (Matrix.of fun i j => hx k hP x (e i) (e j)) = gram (starLk k hP) (inclPlus k hP x) e := by
    intro x e
    simp only [gram, hx, tf, trLk_eq k b₀]
  have hmul : ∀ x δ δ₁, IsDisc hP x δ → IsDisc hP 1 δ₁ →
      δ = QuotientGroup.mk (normPlus (k := k) hP x) * δ₁ := by
    rintro x _ _ ⟨e, d, hd, rfl⟩ ⟨e₁, d₁, hd₁, rfl⟩
    rw [← QuotientGroup.mk_mul, eq_comm, mk_eq_iff_normE]
    obtain ⟨z, hz⟩ := S.det_gram_change 1 e₁ e
    refine ⟨z, ?_⟩
    rw [hg, Units.val_one, map_one] at hd₁
    rw [hd, hg, det_gram, hz, ← hd₁, norm_inclPlus k hP hc hc1 hF, ← mul_assoc,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, Units.val_mul]
  have hex : ∀ x : (Lplus hP ⊗[F] k)ˣ, ∃ δ, IsDisc hP x δ := by
    intro x
    obtain ⟨d, hd⟩ := sig_fixed k hF _
      (S.det_gram_fixed ((star_fixed_iff k hP _).2 ⟨(x : Lplus hP ⊗[F] k), rfl⟩) b)
    have hu := S.isUnit_det_gram (x.isUnit.map (inclPlus k hP))
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [← hd, tmul_zero] at hu
      exact not_isUnit_zero hu
    exact ⟨_, b, Units.mk0 d hd0, by rw [hg]; exact hd, rfl⟩
  intro x
  refine ⟨?_, hmul x⟩
  obtain ⟨δ, hδ⟩ := hex x
  obtain ⟨δ₁, hδ₁⟩ := hex 1
  exact ⟨δ, hδ, fun δ' hδ' => (hmul x δ' δ₁ hδ' hδ₁).trans (hmul x δ δ₁ hδ hδ₁).symm⟩

/- English proof (translation)
Use `haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩`. Establish `hcard : Nat.card (E ≃ₐ[F] E) = 2` using `by rw [IsGalois.card_aut_eq_finrank, h2]`. Take `⟨y, -, hy⟩` from `(Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard`. Use `⟨fun e => ?_, fun e he => ?_⟩` and prove the remaining obligations. Establish `: c ^ 2 = 1` using `hcard ▸ pow_card_eq_one'`.

Rewrite `this` using `[pow_two]`. Conclude with `AlgEquiv.congr_fun this e`. Use `(IsGalois.mem_range_algebraMap_iff_fixed e).2 fun f => ?_` and prove the remaining obligations. Distinguish the cases in `hf : f = 1`. Rewrite using `[hf]`.

Both sides reduce to the same expression. Rewrite using `[(hy f hf).trans (hy c hc1).symm, he]`.
-/
theorem quad_facts [CharZero F] (h2 : Module.finrank F E = 2) (hc1 : c ≠ 1) :
    (∀ e, c (c e) = e) ∧ ∀ e, c e = e → ∃ a, algebraMap F E a = e := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  refine ⟨fun e => ?_, fun e he => ?_⟩
  · have : c ^ 2 = 1 := hcard ▸ pow_card_eq_one'
    rw [pow_two] at this
    exact AlgEquiv.congr_fun this e
  · refine (IsGalois.mem_range_algebraMap_iff_fixed e).2 fun f => ?_
    by_cases hf : f = 1
    · rw [hf]; rfl
    · rw [(hy f hf).trans (hy c hc1).symm, he]

end Concrete

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ h2 c hc1 r P hP`. Take `⟨hc, hF⟩` from `quad_facts h2 hc1`. Conclude with `⟨⟨classParamAt _ hP hc, discAt _ hP hc hc1 hF⟩, fun _ => ⟨classParamAt _ hP hc, discAt _ hP hc hc1 hF⟩, fun _ => ⟨classParamAt _ hP hc, discAt _ hP hc hc1 hF⟩⟩`.
-/
theorem classParamCM : GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion.ClassParamCM := by
  intro F E _ _ _ _ _ _ _ h2 c hc1 r P hP
  obtain ⟨hc, hF⟩ := quad_facts h2 hc1
  exact ⟨⟨classParamAt _ hP hc, discAt _ hP hc hc1 hF⟩,
    fun _ => ⟨classParamAt _ hP hc, discAt _ hP hc hc1 hF⟩,
    fun _ => ⟨classParamAt _ hP hc, discAt _ hP hc hc1 hF⟩⟩

/- English proof (translation)
The claim follows from `GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion.classParam_of_CM classParamCM`.
-/
theorem classParam : GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion.ClassParam :=
  GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion.classParam_of_CM classParamCM

end GlobalTheory.ClassParam
