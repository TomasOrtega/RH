import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobeniusTwistedHilbertNinetyAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.InflFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FinAct
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.Descent
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalField

noncomputable section

open ValuativeRel Matrix GlobalTheory.DZA

namespace UpperTheory.Gal.InertialTypesAlt.L

section Alg

variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ}

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[pow_succ', Function.iterate_succ_apply']`.
-/
private theorem map_map_pow (τ : R →+* R) (M : Matrix (Fin n) (Fin n) R) (i : ℕ) :
    (M.map (τ ^ i)).map τ = M.map (τ ^ (i + 1)) := by
  ext a b
  simp [pow_succ', Function.iterate_succ_apply']

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[pow_succ]`.
-/
private theorem map_pow_map (τ : R →+* R) (M : Matrix (Fin n) (Fin n) R) (i : ℕ) :
    (M.map τ).map (τ ^ i) = M.map (τ ^ (i + 1)) := by
  ext a b
  simp [pow_succ]

private def cp (τ : R →+* R) (c : Matrix (Fin n) (Fin n) R) : ℕ → Matrix (Fin n) (Fin n) R
  | 0 => 1
  | i + 1 => cp τ c i * c.map (τ ^ i)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem cp_zero (τ : R →+* R) (c : Matrix (Fin n) (Fin n) R) : cp τ c 0 = 1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem cp_succ (τ : R →+* R) (c : Matrix (Fin n) (Fin n) R) (i : ℕ) :
    cp τ c (i + 1) = cp τ c i * c.map (τ ^ i) := rfl

/- English proof (translation)
Rewrite using `[pow_succ']`. Both sides reduce to the same expression.
-/
private theorem pow_succ_app (τ : R →+* R) (i : ℕ) (x : R) : (τ ^ (i + 1)) x = τ ((τ ^ i) x) := by
  rw [pow_succ']
  rfl

/- English proof (translation)
The claim follows from `Matrix.map_one _ (map_zero f) (map_one f)`.
-/
private theorem map_one' (f : R →+* S) : (1 : Matrix (Fin n) (Fin n) R).map f = 1 :=
  Matrix.map_one _ (map_zero f) (map_one f)

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simp [cp_succ, cp_zero, map_one']`. Consider the case `succ i ih => conv_lhs => rw [cp_succ τ c (i + 1), ih]`. Rewrite using `[Matrix.mul_assoc, cp_succ τ c i, Matrix.map_mul, map_map_pow]`.
-/
private theorem cp_succ' (τ : R →+* R) (c : Matrix (Fin n) (Fin n) R) (i : ℕ) :
    cp τ c (i + 1) = c * (cp τ c i).map τ := by
  induction i with
  | zero => simp [cp_succ, cp_zero, map_one']
  | succ i ih =>
    conv_lhs => rw [cp_succ τ c (i + 1), ih]
    rw [Matrix.mul_assoc, cp_succ τ c i, Matrix.map_mul, map_map_pow]

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih => rw [pow_succ_app, pow_succ_app, hf, ih]`.
-/
private theorem pow_intertwine (f : R →+* S) (τ : R →+* R) (t : S →+* S)
    (hf : ∀ x, f (τ x) = t (f x)) (i : ℕ) (x : R) : f ((τ ^ i) x) = (t ^ i) (f x) := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ_app, pow_succ_app, hf, ih]

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simp [cp_zero, map_one']`. Consider the case `succ i ih`. Rewrite using `[cp_succ, cp_succ, Matrix.map_mul, ih]`. Use `congr 1`.

Use extensionality with `a b`. Conclude with `pow_intertwine f τ t hf i _`.
-/
private theorem cp_map (f : R →+* S) (τ : R →+* R) (t : S →+* S) (hf : ∀ x, f (τ x) = t (f x))
    (c : Matrix (Fin n) (Fin n) R) (i : ℕ) : (cp τ c i).map f = cp t (c.map f) i := by
  induction i with
  | zero => simp [cp_zero, map_one']
  | succ i ih =>
    rw [cp_succ, cp_succ, Matrix.map_mul, ih]
    congr 1
    ext a b
    exact pow_intertwine f τ t hf i _

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simp [cp_zero]`. Consider the case `succ i ih`. Rewrite using `[cp_succ, ← Matrix.mul_assoc, ih, ← Matrix.map_mul, hc, map_pow_map]`.
-/
private theorem cp_tel (t : R →+* R) (G c : Matrix (Fin n) (Fin n) R) (hc : G * c = G.map t) (i : ℕ) :
    G * cp t c i = G.map (t ^ i) := by
  induction i with
  | zero => simp [cp_zero]
  | succ i ih =>
    rw [cp_succ, ← Matrix.mul_assoc, ih, ← Matrix.map_mul, hc, map_pow_map]

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simp [cp_zero]`. Consider the case `succ i ih`. Rewrite using `[cp_succ, Matrix.mul_assoc, ← map_pow_map, ← Matrix.map_mul, hb, ih]`.
-/
private theorem cp_fix (t : R →+* R) (c b : Matrix (Fin n) (Fin n) R) (hb : c * b.map t = b) (i : ℕ) :
    cp t c i * b.map (t ^ i) = b := by
  induction i with
  | zero => simp [cp_zero]
  | succ i ih =>
    rw [cp_succ, Matrix.mul_assoc, ← map_pow_map, ← Matrix.map_mul, hb, ih]

/- English proof (translation)
Establish `h1 : (∑ i ∈ Finset.range d, Y.map (t ^ i)).map t = ∑ i ∈ Finset.range d, Y.map (t ^ (i + 1))`. Rewrite using `[← RingHom.mapMatrix_apply, map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => map_map_pow t Y i`. Establish `h2` using `Finset.sum_range_succ (fun i => Y.map (t ^ i)) d`. Rewrite `h2` using `[Finset.sum_range_succ', ht, pow_zero]`.

Rewrite using `[h1]`. Conclude with `add_right_cancel h2`.
-/
private theorem sum_fix (t : R →+* R) (d : ℕ) (ht : t ^ d = 1) (Y : Matrix (Fin n) (Fin n) R) :
    (∑ i ∈ Finset.range d, Y.map (t ^ i)).map t = ∑ i ∈ Finset.range d, Y.map (t ^ i) := by
  have h1 : (∑ i ∈ Finset.range d, Y.map (t ^ i)).map t = ∑ i ∈ Finset.range d, Y.map (t ^ (i + 1)) := by
    rw [← RingHom.mapMatrix_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => map_map_pow t Y i
  have h2 := Finset.sum_range_succ (fun i => Y.map (t ^ i)) d
  rw [Finset.sum_range_succ', ht, pow_zero] at h2
  rw [h1]
  exact add_right_cancel h2

/- English proof (translation)
Rewrite using `[← RingHom.mapMatrix_apply, map_sum]`. Establish `h1 : ∀ i, r.mapMatrix (cp τ c i * x.map (τ ^ i)) = (t ^ i) a • b`. Introduce `i`. Establish `h2 : (x.map (τ ^ i)).map r = (t ^ i) a • b.map (t ^ i)`. Use extensionality with `p q`.

Use `congrFun (congrFun hx p) q` as an intermediate fact. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢`. Rewrite using `[pow_intertwine r τ t hr, this, map_mul]`. Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_mul, cp_map r τ t hr, h2, Matrix.mul_smul, cp_fix t _ b hb]`. Simplify using `only [h1]`.

Rewrite using `[← Finset.sum_smul, ha, one_smul]`.
-/
private theorem lift_red (r : R →+* S) (τ : R →+* R) (t : S →+* S) (hr : ∀ x, r (τ x) = t (r x))
    (c x : Matrix (Fin n) (Fin n) R) (b : Matrix (Fin n) (Fin n) S) (a : S) (d : ℕ)
    (hb : c.map r * b.map t = b) (ha : ∑ i ∈ Finset.range d, (t ^ i) a = 1) (hx : x.map r = a • b) :
    (∑ i ∈ Finset.range d, cp τ c i * x.map (τ ^ i)).map r = b := by
  rw [← RingHom.mapMatrix_apply, map_sum]
  have h1 : ∀ i, r.mapMatrix (cp τ c i * x.map (τ ^ i)) = (t ^ i) a • b := by
    intro i
    have h2 : (x.map (τ ^ i)).map r = (t ^ i) a • b.map (t ^ i) := by
      ext p q
      have := congrFun (congrFun hx p) q
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
      rw [pow_intertwine r τ t hr, this, map_mul]
    rw [RingHom.mapMatrix_apply, Matrix.map_mul, cp_map r τ t hr, h2, Matrix.mul_smul,
      cp_fix t _ b hb]
  simp only [h1]
  rw [← Finset.sum_smul, ha, one_smul]

end Alg

section Fin

variable {F₀ F₁ : Type} [Field F₀] [Field F₁] [Algebra F₀ F₁] {n : ℕ}

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih`. Rewrite using `[pow_succ_app, ih, pow_succ', AlgEquiv.mul_apply]`. Both sides reduce to the same expression.
-/
private theorem pow_coe (σ : F₁ ≃ₐ[F₀] F₁) (i : ℕ) (x : F₁) :
    ((σ : F₁ →+* F₁) ^ i) x = (σ ^ i) x := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ_app, ih, pow_succ', AlgEquiv.mul_apply]
    rfl

/- English proof (translation)
Take `⟨m, x, y, h⟩` from `hG.sep`. Set `T : F₁ → F₁` to `fun r => ∑ j ∈ Finset.range d, (σ ^ j) r`. Establish `hT1 : ∀ r, σ (T r) = T r`. Introduce `r`. Establish `h2` using `Finset.sum_range_succ (fun j => (σ ^ j) r) d`.

Rewrite `h2` using `[Finset.sum_range_succ', hG.pow, pow_zero]`. Establish `h3` using `add_right_cancel h2`. Simplify using `only [T, map_sum]`. Rewrite using `[← h3]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [pow_succ', AlgEquiv.mul_apply]`.

Establish `hTj : ∀ r j, (σ ^ j) (T r) = T r`. Introduce `r j`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hT1]`.

Establish `hs : ∑ i, x i * T (y i) = 1`. Simplify using `only [T, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm, Finset.sum_congr rfl fun j hj => h j (Finset.mem_range.1 hj)]`. Simplify using `[hG.pos]`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, T (y i) ≠ 0 := by`.

Assume the negation of the conclusion as `hn`. Use `push_neg at hn`. Simplify using `[hn] at hs`. Use `⟨y i * (T (y i))⁻¹, ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, map_inv₀, hTj]`.

Rewrite using `[← Finset.sum_mul]`. Conclude with `mul_inv_cancel₀ hi`.
-/
private theorem trace_one (σ : F₁ ≃ₐ[F₀] F₁) (d : ℕ) (hG : UpperTheory.ConvolutionTheory.D.IsGal σ d) :
    ∃ a : F₁, ∑ i ∈ Finset.range d, (σ ^ i) a = 1 := by
  obtain ⟨m, x, y, h⟩ := hG.sep
  let T : F₁ → F₁ := fun r => ∑ j ∈ Finset.range d, (σ ^ j) r
  have hT1 : ∀ r, σ (T r) = T r := by
    intro r
    have h2 := Finset.sum_range_succ (fun j => (σ ^ j) r) d
    rw [Finset.sum_range_succ', hG.pow, pow_zero] at h2
    have h3 := add_right_cancel h2
    simp only [T, map_sum]
    rw [← h3]
    exact Finset.sum_congr rfl fun j _ => by rw [pow_succ', AlgEquiv.mul_apply]
  have hTj : ∀ r j, (σ ^ j) (T r) = T r := by
    intro r j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hT1]
  have hs : ∑ i, x i * T (y i) = 1 := by
    simp only [T, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun j hj => h j (Finset.mem_range.1 hj)]
    simp [hG.pos]
  obtain ⟨i, hi⟩ : ∃ i, T (y i) ≠ 0 := by
    by_contra hn
    push_neg at hn
    simp [hn] at hs
  refine ⟨y i * (T (y i))⁻¹, ?_⟩
  simp only [map_mul, map_inv₀, hTj]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀ hi

/- English proof (translation)
Set `S : (Fin n → F₁) →ₗ[F₀] (Fin n → F₁)` to `{ toFun := fun v => c *ᵥ (fun i => σ (v i)) map_add' := fun v w => by`. Simplify using `only [Pi.add_apply, map_add]`. Conclude with `Matrix.mulVec_add c _ _`. Use the proof step `map_smul' := fun a v => by`. Simplify using `only [Pi.smul_apply, map_smul, RingHom.id_apply]`.

Conclude with `Matrix.mulVec_smul c a _ }`. Establish `hSv : ∀ v, S v = c *ᵥ (fun i => σ (v i))` using `fun _ => rfl`. Establish `hs : ∀ (r : F₁) (m : Fin n → F₁), S (r • m) = σ r • S m`. Introduce `r m`. Rewrite using `[hSv, hSv, ← Matrix.mulVec_smul]`.

Use `congr 1`. Use extensionality with `i`. Simplify using the standard rewrite rules. Establish `hSj : ∀ (j : ℕ) (v : Fin n → F₁), (S ^ j) v = cp (σ : F₁ →+* F₁) c j *ᵥ (fun i => (σ ^ j) (v i))`. Introduce `j`.

Proceed by induction on `j with`. Consider the case `zero => intro v`. Simplify using `[cp_zero]`. Consider the case `succ j ih`. Introduce `v`.

Rewrite using `[pow_succ', Module.End.mul_apply, ih, hSv, cp_succ', ← Matrix.mulVec_mulVec]`. Use `congr 1`. Use extensionality with `i`. Use `RingHom.map_mulVec (σ : F₁ →+* F₁) (cp (σ : F₁ →+* F₁) c j) (fun i => (σ ^ j) (v i)) i` as an intermediate fact. Use `Eq.trans this ?_` and prove the remaining obligations.

Use `congr 1`. Use extensionality with `p`. Simplify using `[pow_succ', AlgEquiv.mul_apply]`. Establish `hq : S ^ d = 1`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations.

Rewrite using `[hSj, hc, Matrix.one_mulVec, hG.pow]`. Both sides reduce to the same expression. Establish `hsurj` using `(UpperTheory.ConvolutionTheory.D.descent F₀ F₁ σ d hG (Fin n → F₁) S hs hq).2`. Establish `hspan : (⊤ : Submodule F₁ (Fin n → F₁)) ≤ Submodule.span F₁ (LinearMap.eqLocus S LinearMap.id : Set (Fin n → F₁))`. Introduce `m _`.

Take `⟨z, rfl⟩` from `hsurj m`. Proceed by induction on `z with`. Consider the case `zero => simp`. Consider the case `add a b ha hb`. Rewrite using `[map_add]`.

Conclude with `add_mem (ha (Submodule.mem_top)) (hb (Submodule.mem_top))`. Consider the case `tmul r w`. Simplify using `only [TensorProduct.lift.tmul]`. Conclude with `Submodule.smul_mem _ r (Submodule.subset_span w.2)`. Take `⟨B, hBt, -, hBspan, hli⟩` from `exists_linearIndepOn_id_extension (K := F₁) (linearIndepOn_empty F₁ id) (Set.empty_subset (LinearMap.eqLocus S LinearMap.id : Set (Fin n → F₁)))`.

Establish `htop : (⊤ : Submodule F₁ (Fin n → F₁)) ≤ Submodule.span F₁ (Set.range ((↑) : B → Fin n → F₁))`. Rewrite using `[Subtype.range_coe]`. Conclude with `hspan.trans (Submodule.span_le.2 hBspan)`. Set `e` to `Module.Basis.mk (v := ((↑) : B → Fin n → F₁)) hli htop`. Set `e'` to `e.reindex (e.indexEquiv (Pi.basisFun F₁ (Fin n)))`.

Establish `he' : ∀ j, S (e' j) = e' j`. Introduce `j`. Establish `hm : e' j ∈ B`. Establish `h1 : e' j = (((e.indexEquiv (Pi.basisFun F₁ (Fin n))).symm j : B) : Fin n → F₁)`. Simplify using `only [e', Module.Basis.reindex_apply]`.

Conclude with `congrFun (Module.Basis.coe_mk hli htop) _`. Rewrite using `[h1]`. Conclude with `Subtype.coe_prop _`. Conclude with `hBt hm`. Use `⟨(Pi.basisFun F₁ (Fin n)).toMatrix e', ?_, ?_⟩` and prove the remaining obligations.

Use `haveI := (Pi.basisFun F₁ (Fin n)).invertibleToMatrix e'`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_invertible _)`. Use extensionality with `i j`. Use `congrFun (he' j) i` as an intermediate fact. Rewrite `this` using `[hSv]`.

Simplify using `only [Matrix.mul_apply, Matrix.map_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr]`. Conclude with `this`.
-/
private theorem fin_desc (σ : F₁ ≃ₐ[F₀] F₁) (d : ℕ) (hG : UpperTheory.ConvolutionTheory.D.IsGal σ d)
    (c : Matrix (Fin n) (Fin n) F₁) (hc : cp (σ : F₁ →+* F₁) c d = 1) :
    ∃ b : Matrix (Fin n) (Fin n) F₁, IsUnit b.det ∧ c * b.map (σ : F₁ →+* F₁) = b := by
  let S : (Fin n → F₁) →ₗ[F₀] (Fin n → F₁) :=
    { toFun := fun v => c *ᵥ (fun i => σ (v i))
      map_add' := fun v w => by
        simp only [Pi.add_apply, map_add]
        exact Matrix.mulVec_add c _ _
      map_smul' := fun a v => by
        simp only [Pi.smul_apply, map_smul, RingHom.id_apply]
        exact Matrix.mulVec_smul c a _ }
  have hSv : ∀ v, S v = c *ᵥ (fun i => σ (v i)) := fun _ => rfl
  have hs : ∀ (r : F₁) (m : Fin n → F₁), S (r • m) = σ r • S m := by
    intro r m
    rw [hSv, hSv, ← Matrix.mulVec_smul]
    congr 1
    ext i
    simp
  have hSj : ∀ (j : ℕ) (v : Fin n → F₁),
      (S ^ j) v = cp (σ : F₁ →+* F₁) c j *ᵥ (fun i => (σ ^ j) (v i)) := by
    intro j
    induction j with
    | zero => intro v; simp [cp_zero]
    | succ j ih =>
      intro v
      rw [pow_succ', Module.End.mul_apply, ih, hSv, cp_succ', ← Matrix.mulVec_mulVec]
      congr 1
      ext i
      have := RingHom.map_mulVec (σ : F₁ →+* F₁) (cp (σ : F₁ →+* F₁) c j) (fun i => (σ ^ j) (v i)) i
      refine Eq.trans this ?_
      congr 1
      ext p
      simp [pow_succ', AlgEquiv.mul_apply]
  have hq : S ^ d = 1 := by
    refine LinearMap.ext fun v => ?_
    rw [hSj, hc, Matrix.one_mulVec, hG.pow]
    rfl
  have hsurj := (UpperTheory.ConvolutionTheory.D.descent F₀ F₁ σ d hG (Fin n → F₁) S hs hq).2
  have hspan : (⊤ : Submodule F₁ (Fin n → F₁)) ≤
      Submodule.span F₁ (LinearMap.eqLocus S LinearMap.id : Set (Fin n → F₁)) := by
    intro m _
    obtain ⟨z, rfl⟩ := hsurj m
    induction z with
    | zero => simp
    | add a b ha hb =>
      rw [map_add]
      exact add_mem (ha (Submodule.mem_top)) (hb (Submodule.mem_top))
    | tmul r w =>
      simp only [TensorProduct.lift.tmul]
      exact Submodule.smul_mem _ r (Submodule.subset_span w.2)
  obtain ⟨B, hBt, -, hBspan, hli⟩ := exists_linearIndepOn_id_extension (K := F₁)
    (linearIndepOn_empty F₁ id)
    (Set.empty_subset (LinearMap.eqLocus S LinearMap.id : Set (Fin n → F₁)))
  have htop : (⊤ : Submodule F₁ (Fin n → F₁)) ≤ Submodule.span F₁ (Set.range ((↑) : B → Fin n → F₁)) := by
    rw [Subtype.range_coe]
    exact hspan.trans (Submodule.span_le.2 hBspan)
  let e := Module.Basis.mk (v := ((↑) : B → Fin n → F₁)) hli htop
  let e' := e.reindex (e.indexEquiv (Pi.basisFun F₁ (Fin n)))
  have he' : ∀ j, S (e' j) = e' j := by
    intro j
    have hm : e' j ∈ B := by
      have h1 : e' j = (((e.indexEquiv (Pi.basisFun F₁ (Fin n))).symm j : B) : Fin n → F₁) := by
        simp only [e', Module.Basis.reindex_apply]
        exact congrFun (Module.Basis.coe_mk hli htop) _
      rw [h1]
      exact Subtype.coe_prop _
    exact hBt hm
  refine ⟨(Pi.basisFun F₁ (Fin n)).toMatrix e', ?_, ?_⟩
  · haveI := (Pi.basisFun F₁ (Fin n)).invertibleToMatrix e'
    exact (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_invertible _)
  · ext i j
    have := congrFun (he' j) i
    rw [hSv] at this
    simp only [Matrix.mul_apply, Matrix.map_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    exact this

/- English proof (translation)
Establish `hsb : sb = FiniteField.frobeniusAlgEquivOfAlgebraic F₀ F₁`. Use extensionality with `z`. Rewrite using `[FiniteField.coe_frobeniusAlgEquivOfAlgebraic]`. Conclude with `hf z`. Establish `ho : orderOf sb = Module.finrank F₀ F₁`.

Rewrite using `[hsb]`. Conclude with `FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F₀ F₁`. Establish `hc : Nat.card (F₁ ≃ₐ[F₀] F₁) = Module.finrank F₀ F₁` using `IsGalois.card_aut_eq_finrank F₀ F₁`. Establish `htop : Subgroup.zpowers sb = ⊤` using `Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, ho, hc])`. Conclude with `UpperTheory.ConvolutionTheory.D.galField F₀ F₁ sb fun τ => by rw [htop]; trivial`.
-/
private theorem isGal_frob [Fintype F₀] [Fintype F₁] (sb : F₁ ≃ₐ[F₀] F₁)
    (hf : ∀ z : F₁, sb z = z ^ Fintype.card F₀) : UpperTheory.ConvolutionTheory.D.IsGal sb (Module.finrank F₀ F₁) := by
  have hsb : sb = FiniteField.frobeniusAlgEquivOfAlgebraic F₀ F₁ := by
    ext z
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    exact hf z
  have ho : orderOf sb = Module.finrank F₀ F₁ := by
    rw [hsb]
    exact FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F₀ F₁
  have hc : Nat.card (F₁ ≃ₐ[F₀] F₁) = Module.finrank F₀ F₁ := IsGalois.card_aut_eq_finrank F₀ F₁
  have htop : Subgroup.zpowers sb = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, ho, hc])
  exact UpperTheory.ConvolutionTheory.D.galField F₀ F₁ sb fun τ => by rw [htop]; trivial

end Fin

section Loc

variable {k K : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K]

/- English proof (translation)
Establish `hx` using `x.2`. Rewrite `hx`, the goal using `[Valuation.mem_integer_iff]`. Rewrite using `[GroundTheory.LocalField.valuation_algEquiv_apply k K s (x : K)]` and apply the resulting hypothesis.
-/
private theorem int_mem (s : K ≃ₐ[k] K) (x : 𝒪[K]) : s (x : K) ∈ 𝒪[K] := by
  have hx := x.2
  rw [Valuation.mem_integer_iff] at hx ⊢
  rwa [GroundTheory.LocalField.valuation_algEquiv_apply k K s (x : K)]

private def rs (s : K ≃ₐ[k] K) : 𝒪[K] →+* 𝒪[K] :=
  (s.toAlgHom.toRingHom.comp (algebraMap 𝒪[K] K)).codRestrict 𝒪[K] fun x => int_mem s x

/- English proof (translation)
Use `haveI : IsLocalRing 𝒪[K] := (inferInstance : IsDiscreteValuationRing 𝒪[K]).toIsLocalRing`. Assume the negation of the conclusion as `hu`. Establish `hm : x ∈ IsLocalRing.maximalIdeal 𝒪[K]` using `hu`. Use `haveI : (RingHom.ker rd).IsMaximal := RingHom.ker_isMaximal_of_surjective rd hrd`. Rewrite `hm` using `[← IsLocalRing.eq_maximalIdeal (inferInstance : (RingHom.ker rd).IsMaximal)]`.

Conclude with `hx hm`.
-/
private theorem unit_of_red {F : Type} [Field F] (rd : 𝒪[K] →+* F) (hrd : Function.Surjective rd)
    {x : 𝒪[K]} (hx : rd x ≠ 0) : IsUnit x := by
  haveI : IsLocalRing 𝒪[K] := (inferInstance : IsDiscreteValuationRing 𝒪[K]).toIsLocalRing
  by_contra hu
  have hm : x ∈ IsLocalRing.maximalIdeal 𝒪[K] := hu
  haveI : (RingHom.ker rd).IsMaximal := RingHom.ker_isMaximal_of_surjective rd hrd
  rw [← IsLocalRing.eq_maximalIdeal (inferInstance : (RingHom.ker rd).IsMaximal)] at hm
  exact hx hm

/- English proof (translation)
Establish `hgen : ∀ τ : K ≃ₐ[k] K, τ ∈ Subgroup.zpowers s` using `(frobFacts k K F₀ F₁ rk rK s sb h).1`. Establish `hsd : s ^ Module.finrank k K = 1`. Rewrite using `[← IsGalois.card_aut_eq_finrank]`. Conclude with `pow_card_eq_one'`. Set `s' : K →+* K` to `(s : K →+* K)`.

Establish `hs'd : s' ^ Module.finrank k K = 1`. Use extensionality with `x`. Rewrite using `[pow_coe, hsd]`. Both sides reduce to the same expression. Establish `hGsb : UpperTheory.ConvolutionTheory.D.IsGal sb (Module.finrank k K)` using `h.deg ▸ isGal_frob sb h.frob`.

Take `⟨y, hy⟩` from `hg`. Set `ι : 𝒪[K] →+* K` to `algebraMap 𝒪[K] K`. Set `τ : 𝒪[K] →+* 𝒪[K]` to `rs s`. Set `t : F₁ →+* F₁` to `(sb : F₁ →+* F₁)`. Set `G : Matrix (Fin n) (Fin n) K` to `(g : Matrix (Fin n) (Fin n) K)`.

Set `c : Matrix (Fin n) (Fin n) 𝒪[K]` to `(y : Matrix (Fin n) (Fin n) 𝒪[K])`. Establish `hι : ∀ x, ι (τ x) = s' (ι x)` using `fun _ => rfl`. Establish `hrt : ∀ x, rK (τ x) = t (rK x)` using `fun x => h.gal x (τ x) rfl`. Establish `hcK : G * c.map ι = G.map s'`. Establish `h2 : g * GeneralLinearGroup.map ι y = GlobalTheory.LBC.galAct s n g`.

Express the relevant statement in the definitionally equal form `g * GeneralLinearGroup.map (algebraMap 𝒪[K] K) y = _`. Rewrite using `[hy]`. Use `group`. Conclude with `congrArg Units.val h2`. Establish `hcp : ∀ i, G * (cp τ c i).map ι = G.map (s' ^ i)` using `fun i => by`.

Rewrite using `[cp_map ι τ s' hι]`. Conclude with `cp_tel s' G _ hcK i`. Establish `hcd : cp τ c (Module.finrank k K) = 1`. Establish `h1 : (cp τ c (Module.finrank k K)).map ι = 1` using `(Units.mul_right_inj g).1 (by`. Use `(hcp _).trans ?_` and prove the remaining obligations.

Rewrite using `[hs'd]`. Simplify using `[G])`. Apply `Matrix.map_injective (f := ι) Subtype.val_injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(cp τ c (Module.finrank k K)).map ι = (1 : Matrix (Fin n) (Fin n) 𝒪[K]).map ι`. Rewrite using `[h1, map_one']`.

Establish `hcd' : cp t (c.map rK) (Module.finrank k K) = 1`. Rewrite using `[← cp_map rK τ t hrt, hcd, map_one']`. Take `⟨b, hbu, hb⟩` from `fin_desc sb _ hGsb (c.map rK) hcd'`. Take `⟨a, ha⟩` from `trace_one sb _ hGsb`. Establish `ha' : ∑ i ∈ Finset.range (Module.finrank k K), (t ^ i) a = 1`.

Rewrite using `[← ha]`. Conclude with `Finset.sum_congr rfl fun i _ => pow_coe sb i a`. Set `x : Matrix (Fin n) (Fin n) 𝒪[K]` to `(a • b).map (Function.surjInv h.onto₁)`. Establish `hx : x.map rK = a • b`. Use extensionality with `p q`.

Conclude with `Function.surjInv_eq h.onto₁ _`. Set `B : Matrix (Fin n) (Fin n) 𝒪[K]` to `∑ i ∈ Finset.range (Module.finrank k K), cp τ c i * x.map (τ ^ i)`. Establish `hB : B.map rK = b` using `lift_red rK τ t hrt c x b a _ hb ha' hx`. Establish `hBu : IsUnit B.det`. Use `unit_of_red rK h.onto₁ ?_` and prove the remaining obligations.

Establish `h1 : rK B.det = b.det`. Rewrite using `[RingHom.map_det]`. Conclude with `congrArg Matrix.det hB`. Rewrite using `[h1]`. Conclude with `hbu.ne_zero`.

Set `H : Matrix (Fin n) (Fin n) K` to `G * B.map ι`. Establish `hH : H = ∑ i ∈ Finset.range (Module.finrank k K), (G * x.map ι).map (s' ^ i)`. Simplify using `only [H, B]`. Rewrite using `[← RingHom.mapMatrix_apply, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_mul, ← Matrix.mul_assoc, hcp, Matrix.map_mul]`. Use `congr 1`. Use extensionality with `p q`. Conclude with `pow_intertwine ι τ s' hι i _`. Establish `hHs : H.map s' = H`.

Rewrite using `[hH]`. Conclude with `sum_fix s' _ hs'd _`. Establish `hfix : ∀ p q, ∃ m : k, algebraMap k K m = H p q` using `fun p q => by`. Establish `hf : s (H p q) = H p q` using `congrFun (congrFun hHs p) q`. Establish `hst : Subgroup.zpowers s ≤ MulAction.stabilizer (K ≃ₐ[k] K) (H p q)` using `Subgroup.zpowers_le.2 hf`.

Establish `hb' : H p q ∈ (⊥ : IntermediateField k K)` using `(IsGalois.mem_bot_iff_fixed _).2 fun f => hst (hgen f)`. Take `⟨m, hm⟩` from `IntermediateField.mem_bot.1 hb'`. Conclude with `⟨m, hm⟩`. Use `choose M hM using hfix`. Set `Mm : Matrix (Fin n) (Fin n) k` to `Matrix.of M`.

Establish `hMH : Mm.map (algebraMap k K) = H`. Use extensionality with `p q`. Conclude with `hM p q`. Establish `hHu : IsUnit H.det`. Simplify using `only [H]`.

Rewrite using `[Matrix.det_mul]`. Use `(Matrix.isUnits_det_units g).mul ?_` and prove the remaining obligations. Establish `h1 : (B.map ι).det = ι B.det`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression.

Rewrite using `[h1]`. Conclude with `hBu.map ι`. Establish `hMu : IsUnit Mm.det`. Establish `h1 : algebraMap k K Mm.det = H.det`. Rewrite using `[RingHom.map_det]`.

Conclude with `congrArg Matrix.det hMH`. Use `isUnit_iff_ne_zero.2 fun h0 => hHu.ne_zero ?_` and prove the remaining obligations. Rewrite using `[← h1, h0, map_zero]`. Use `⟨GeneralLinearGroup.mk'' Mm hMu, (GeneralLinearGroup.map ι (GeneralLinearGroup.mk'' B hBu))⁻¹, (KO K n).inv_mem ⟨_, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_mul_inv_iff_mul_eq]`.

Apply `Units.ext` to reduce the goal to its premises. Conclude with `hMH.symm`.
-/
private theorem lat_main [IsGalois k K] {F₀ F₁ : Type} [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁]
    [Algebra F₀ F₁] {rk : 𝒪[k] →+* F₀} {rK : 𝒪[K] →+* F₁} {s : K ≃ₐ[k] K} {sb : F₁ ≃ₐ[F₀] F₁}
    (h : IsRes rk rK s sb) {n : ℕ} (g : GL (Fin n) K) (hg : g⁻¹ * GlobalTheory.LBC.galAct s n g ∈ KO K n) :
    ∃ h : GL (Fin n) k, ∃ κ ∈ KO K n, g = GlobalTheory.LBC.incl K n h * κ := by
  have hgen : ∀ τ : K ≃ₐ[k] K, τ ∈ Subgroup.zpowers s :=
    (frobFacts k K F₀ F₁ rk rK s sb h).1
  have hsd : s ^ Module.finrank k K = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact pow_card_eq_one'
  let s' : K →+* K := (s : K →+* K)
  have hs'd : s' ^ Module.finrank k K = 1 := by
    ext x
    rw [pow_coe, hsd]
    rfl
  have hGsb : UpperTheory.ConvolutionTheory.D.IsGal sb (Module.finrank k K) := h.deg ▸ isGal_frob sb h.frob
  obtain ⟨y, hy⟩ := hg
  let ι : 𝒪[K] →+* K := algebraMap 𝒪[K] K
  let τ : 𝒪[K] →+* 𝒪[K] := rs s
  let t : F₁ →+* F₁ := (sb : F₁ →+* F₁)
  let G : Matrix (Fin n) (Fin n) K := (g : Matrix (Fin n) (Fin n) K)
  let c : Matrix (Fin n) (Fin n) 𝒪[K] := (y : Matrix (Fin n) (Fin n) 𝒪[K])
  have hι : ∀ x, ι (τ x) = s' (ι x) := fun _ => rfl
  have hrt : ∀ x, rK (τ x) = t (rK x) := fun x => h.gal x (τ x) rfl
  have hcK : G * c.map ι = G.map s' := by
    have h2 : g * GeneralLinearGroup.map ι y = GlobalTheory.LBC.galAct s n g := by
      change g * GeneralLinearGroup.map (algebraMap 𝒪[K] K) y = _
      rw [hy]
      group
    exact congrArg Units.val h2
  have hcp : ∀ i, G * (cp τ c i).map ι = G.map (s' ^ i) := fun i => by
    rw [cp_map ι τ s' hι]
    exact cp_tel s' G _ hcK i
  have hcd : cp τ c (Module.finrank k K) = 1 := by
    have h1 : (cp τ c (Module.finrank k K)).map ι = 1 :=
      (Units.mul_right_inj g).1 (by
        refine (hcp _).trans ?_
        rw [hs'd]
        simp [G])
    apply Matrix.map_injective (f := ι) Subtype.val_injective
    change (cp τ c (Module.finrank k K)).map ι = (1 : Matrix (Fin n) (Fin n) 𝒪[K]).map ι
    rw [h1, map_one']
  have hcd' : cp t (c.map rK) (Module.finrank k K) = 1 := by
    rw [← cp_map rK τ t hrt, hcd, map_one']
  obtain ⟨b, hbu, hb⟩ := fin_desc sb _ hGsb (c.map rK) hcd'
  obtain ⟨a, ha⟩ := trace_one sb _ hGsb
  have ha' : ∑ i ∈ Finset.range (Module.finrank k K), (t ^ i) a = 1 := by
    rw [← ha]
    exact Finset.sum_congr rfl fun i _ => pow_coe sb i a
  let x : Matrix (Fin n) (Fin n) 𝒪[K] := (a • b).map (Function.surjInv h.onto₁)
  have hx : x.map rK = a • b := by
    ext p q
    exact Function.surjInv_eq h.onto₁ _
  let B : Matrix (Fin n) (Fin n) 𝒪[K] :=
    ∑ i ∈ Finset.range (Module.finrank k K), cp τ c i * x.map (τ ^ i)
  have hB : B.map rK = b := lift_red rK τ t hrt c x b a _ hb ha' hx
  have hBu : IsUnit B.det := by
    refine unit_of_red rK h.onto₁ ?_
    have h1 : rK B.det = b.det := by
      rw [RingHom.map_det]
      exact congrArg Matrix.det hB
    rw [h1]
    exact hbu.ne_zero
  let H : Matrix (Fin n) (Fin n) K := G * B.map ι
  have hH : H = ∑ i ∈ Finset.range (Module.finrank k K), (G * x.map ι).map (s' ^ i) := by
    simp only [H, B]
    rw [← RingHom.mapMatrix_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_mul, ← Matrix.mul_assoc, hcp, Matrix.map_mul]
    congr 1
    ext p q
    exact pow_intertwine ι τ s' hι i _
  have hHs : H.map s' = H := by
    rw [hH]
    exact sum_fix s' _ hs'd _
  have hfix : ∀ p q, ∃ m : k, algebraMap k K m = H p q := fun p q => by
    have hf : s (H p q) = H p q := congrFun (congrFun hHs p) q
    have hst : Subgroup.zpowers s ≤ MulAction.stabilizer (K ≃ₐ[k] K) (H p q) :=
      Subgroup.zpowers_le.2 hf
    have hb' : H p q ∈ (⊥ : IntermediateField k K) :=
      (IsGalois.mem_bot_iff_fixed _).2 fun f => hst (hgen f)
    obtain ⟨m, hm⟩ := IntermediateField.mem_bot.1 hb'
    exact ⟨m, hm⟩
  choose M hM using hfix
  let Mm : Matrix (Fin n) (Fin n) k := Matrix.of M
  have hMH : Mm.map (algebraMap k K) = H := by
    ext p q
    exact hM p q
  have hHu : IsUnit H.det := by
    simp only [H]
    rw [Matrix.det_mul]
    refine (Matrix.isUnits_det_units g).mul ?_
    have h1 : (B.map ι).det = ι B.det := by
      rw [RingHom.map_det]
      rfl
    rw [h1]
    exact hBu.map ι
  have hMu : IsUnit Mm.det := by
    have h1 : algebraMap k K Mm.det = H.det := by
      rw [RingHom.map_det]
      exact congrArg Matrix.det hMH
    refine isUnit_iff_ne_zero.2 fun h0 => hHu.ne_zero ?_
    rw [← h1, h0, map_zero]
  refine ⟨GeneralLinearGroup.mk'' Mm hMu,
    (GeneralLinearGroup.map ι (GeneralLinearGroup.mk'' B hBu))⁻¹, (KO K n).inv_mem ⟨_, rfl⟩, ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  exact hMH.symm

end Loc

end UpperTheory.Gal.InertialTypesAlt.L

/- English proof (translation)
Introduce `k K _ _ _ _ _ _ _ _ _ _ _ _ _ F₀ F₁ _ _ _ _ _ rk rK s sb h n g hg`. Conclude with `UpperTheory.Gal.InertialTypesAlt.L.lat_main h g hg`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.L.latDesc :
    UpperTheory.Gal.InertialTypesAlt.L.LatDesc := by
  intro k K _ _ _ _ _ _ _ _ _ _ _ _ _ F₀ F₁ _ _ _ _ _ rk rK s sb h n g hg
  exact UpperTheory.Gal.InertialTypesAlt.L.lat_main h g hg
