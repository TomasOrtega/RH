import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective

namespace GlobalTheory.SignedLengthOrdFracDet

open Module Submodule

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.prod_insert hi, Finset.sum_insert hi, Ring.ord_mul' R (mem_nonZeroDivisors_of_ne_zero (hc i)), ih]`.
-/
theorem ord_prod {R : Type*} [CommRing R] [IsDomain R] {ι : Type*} (s : Finset ι) (c : ι → R)
    (hc : ∀ i, c i ≠ 0) : Ring.ord R (∏ i ∈ s, c i) = ∑ i ∈ s, Ring.ord R (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Ring.ord_mul' R (mem_nonZeroDivisors_of_ne_zero (hc i)), ih]

/- English proof (translation)
Establish `: Module.Finite R M` using `Module.Finite.of_basis e₀`. Establish `: Module.Free R M` using `Module.Free.of_basis e₀`. Set `N` to `LinearMap.range f`. Set `e : M ≃ₗ[R] N` to `LinearEquiv.ofInjective f hf`. Establish `h : Module.finrank R N = Module.finrank R M` using `e.symm.finrank_eq`.

Set `c` to `smithNormalFormCoeffs e₀ h`. Set `t` to `smithNormalFormTopBasis e₀ h`. Set `u` to `smithNormalFormBotBasis e₀ h`. Set `e' : M ≃ₗ[R] N` to `t.equiv u (Equiv.refl _)`. Establish `h1 : Associated (LinearMap.det f) (LinearMap.det (N.subtype ∘ₗ (e' : M →ₗ[R] N)))` using `LinearMap.associated_det_comp_equiv N.subtype e e'`.

Establish `h2 : LinearMap.toMatrix t t (N.subtype ∘ₗ (e' : M →ₗ[R] N)) = Matrix.diagonal c`. Use extensionality with `i j`. Establish `hj : (N.subtype ∘ₗ (e' : M →ₗ[R] N)) (t j) = c j • t j`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, e', Basis.equiv_apply, Equiv.refl_apply]`. Conclude with `smithNormalFormBotBasis_def e₀ h j`.

Rewrite using `[LinearMap.toMatrix_apply, hj, Matrix.diagonal_apply]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hij]`.

Rewrite using `[Ring.ord_eq_of_associated h1, ← LinearMap.det_toMatrix t, h2, Matrix.det_diagonal, ord_prod _ _ (smithNormalFormCoeffs_ne_zero e₀ h), (quotientEquivPiSpan N e₀ h).length_eq, Module.length_pi_of_fintype]`. Both sides reduce to the same expression.
-/
theorem length_coker {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {M : Type*} [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e₀ : Basis ι R M) (f : M →ₗ[R] M) (hf : Function.Injective f) :
    Module.length R (M ⧸ LinearMap.range f) = Ring.ord R (LinearMap.det f) := by
  have : Module.Finite R M := Module.Finite.of_basis e₀
  have : Module.Free R M := Module.Free.of_basis e₀
  let N := LinearMap.range f
  let e : M ≃ₗ[R] N := LinearEquiv.ofInjective f hf
  have h : Module.finrank R N = Module.finrank R M := e.symm.finrank_eq
  let c := smithNormalFormCoeffs e₀ h
  let t := smithNormalFormTopBasis e₀ h
  let u := smithNormalFormBotBasis e₀ h
  let e' : M ≃ₗ[R] N := t.equiv u (Equiv.refl _)
  have h1 : Associated (LinearMap.det f) (LinearMap.det (N.subtype ∘ₗ (e' : M →ₗ[R] N))) :=
    LinearMap.associated_det_comp_equiv N.subtype e e'
  have h2 : LinearMap.toMatrix t t (N.subtype ∘ₗ (e' : M →ₗ[R] N)) = Matrix.diagonal c := by
    ext i j
    have hj : (N.subtype ∘ₗ (e' : M →ₗ[R] N)) (t j) = c j • t j := by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e', Basis.equiv_apply,
        Equiv.refl_apply]
      exact smithNormalFormBotBasis_def e₀ h j
    rw [LinearMap.toMatrix_apply, hj, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  rw [Ring.ord_eq_of_associated h1, ← LinearMap.det_toMatrix t, h2, Matrix.det_diagonal,
    ord_prod _ _ (smithNormalFormCoeffs_ne_zero e₀ h),
    (quotientEquivPiSpan N e₀ h).length_eq, Module.length_pi_of_fintype]
  rfl

/- English proof (translation)
Rewrite using `[relLength_eq_length_map_mkQ A C, relLength_eq_length_map_mkQ D C, ← relLength_map_mkQ hC A, add_comm]`. Establish `hle : D.map C.mkQ ≤ A.map C.mkQ` using `Submodule.map_mono hD`. Rewrite using `[relLength_def, ← (Submodule.submoduleOfEquivOfLe hle).length_eq]`. Conclude with `Module.length_eq_add_of_exact (Submodule.subtype _) (Submodule.mkQ _) (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)`.
-/
theorem relLength_chain {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    {A D C : Submodule R V} (hD : D ≤ A) (hC : C ≤ D) :
    relLength A C = relLength A D + relLength D C := by
  rw [relLength_eq_length_map_mkQ A C, relLength_eq_length_map_mkQ D C,
    ← relLength_map_mkQ hC A, add_comm]
  have hle : D.map C.mkQ ≤ A.map C.mkQ := Submodule.map_mono hD
  rw [relLength_def, ← (Submodule.submoduleOfEquivOfLe hle).length_eq]
  exact Module.length_eq_add_of_exact (Submodule.subtype _) (Submodule.mkQ _)
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _)

/- English proof (translation)
Establish `h1` using `relLength_chain (inf_le_left : A ⊓ B ≤ A) (le_inf hA hB)`. Establish `h2` using `relLength_chain (inf_le_right : A ⊓ B ≤ B) (le_inf hA hB)`. Rewrite `h1` using `[relLength_inf_right, hm]`. Rewrite `h2` using `[relLength_inf_right', hn]`. Unfold `LengthCommensurable signedLength`.

Generalize the expression as in `relLength A B = x at *`. Generalize the expression as in `relLength B A = y at *`. Generalize the expression as in `relLength (A ⊓ B) C = z at *`. Consider the cases of `x with`. Consider the case `top => simp at h1`.

Consider the case `coe x`. Consider the cases of `y with`. Consider the case `top => simp at h2`. Consider the case `coe y`. Consider the cases of `z with`.

Consider the case `top => simp at h2`. Consider the case `coe z`. Normalize the coercions in `at h1 h2`. Use `⟨⟨by simp, by simp⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [ENat.toNat_natCast]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem signedLength_of_common {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    {A B C : Submodule R V} (hA : C ≤ A) (hB : C ≤ B) {m n : ℕ} (hm : relLength A C = m)
    (hn : relLength B C = n) :
    LengthCommensurable A B ∧ signedLength A B = (m : ℤ) - n := by
  have h1 := relLength_chain (inf_le_left : A ⊓ B ≤ A) (le_inf hA hB)
  have h2 := relLength_chain (inf_le_right : A ⊓ B ≤ B) (le_inf hA hB)
  rw [relLength_inf_right, hm] at h1
  rw [relLength_inf_right', hn] at h2
  unfold LengthCommensurable signedLength
  generalize relLength A B = x at *
  generalize relLength B A = y at *
  generalize relLength (A ⊓ B) C = z at *
  cases x with
  | top => simp at h1
  | coe x =>
  cases y with
  | top => simp at h2
  | coe y =>
  cases z with
  | top => simp at h2
  | coe z =>
  norm_cast at h1 h2
  refine ⟨⟨by simp, by simp⟩, ?_⟩
  simp only [ENat.toNat_natCast]
  omega

/- English proof (translation)
Set `φ : (ι → R) →ₗ[R] V` to `Fintype.linearCombination R a`. Establish `hφ : Function.Injective φ` using `ha.fintypeLinearCombination_injective`. Establish `h1 : span R (Set.range a) = (⊤ : Submodule R (ι → R)).map φ`. Rewrite using `[Submodule.map_top, Fintype.range_linearCombination]`. Establish `h2 : span R (Set.range c) = (LinearMap.range (Matrix.toLin' P)).map φ`.

Rewrite using `[Matrix.range_toLin', Submodule.map_span, ← Set.range_comp]`. Use `congr 2`. Use function extensionality and compare the values at `j`. Simplify using `[φ, hc j, Fintype.linearCombination_apply]`. Establish `hinj : Function.Injective (Matrix.toLin' P)`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `v hv`. Conclude with `Matrix.eq_zero_of_mulVec_eq_zero hP (by simpa using hv)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h1, h2]`.

Conclude with `Submodule.map_mono le_top`. Rewrite using `[h1, h2, relLength_map_of_injective φ hφ, relLength_top_left, length_coker (Pi.basisFun R ι) _ hinj, LinearMap.det_toLin']`.
-/
theorem relLength_span {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {V : Type*} [AddCommGroup V] [Module R V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a c : ι → V} (ha : LinearIndependent R a) (P : Matrix ι ι R) (hP : P.det ≠ 0)
    (hc : ∀ j, c j = ∑ i, P i j • a i) :
    span R (Set.range c) ≤ span R (Set.range a) ∧
      relLength (span R (Set.range a)) (span R (Set.range c)) = Ring.ord R P.det := by
  let φ : (ι → R) →ₗ[R] V := Fintype.linearCombination R a
  have hφ : Function.Injective φ := ha.fintypeLinearCombination_injective
  have h1 : span R (Set.range a) = (⊤ : Submodule R (ι → R)).map φ := by
    rw [Submodule.map_top, Fintype.range_linearCombination]
  have h2 : span R (Set.range c) = (LinearMap.range (Matrix.toLin' P)).map φ := by
    rw [Matrix.range_toLin', Submodule.map_span, ← Set.range_comp]
    congr 2
    funext j
    simp [φ, hc j, Fintype.linearCombination_apply]
  have hinj : Function.Injective (Matrix.toLin' P) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    exact Matrix.eq_zero_of_mulVec_eq_zero hP (by simpa using hv)
  refine ⟨?_, ?_⟩
  · rw [h1, h2]; exact Submodule.map_mono le_top
  · rw [h1, h2, relLength_map_of_injective φ hφ, relLength_top_left,
      length_coker (Pi.basisFun R ι) _ hinj, LinearMap.det_toLin']

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap R K)` using `IsFractionRing.injective R K`. Establish `hbK : LinearIndependent K b`. Rewrite `ha`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `v hv`. Establish `h0 : g.mulVec v = 0`.

Use function extensionality and compare the values at `i`. Use `ha (g.mulVec v) ?_ i` and prove the remaining obligations. Rewrite using `[← hv]`. Simplify using `only [hb, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`.

Simplify using `only [mul_comm]`. Introduce `i`. Conclude with `congrFun (Matrix.eq_zero_of_mulVec_eq_zero hg h0) i`. Establish `haR : LinearIndependent R a` using `ha.restrict_scalars' R`. Establish `hbR : LinearIndependent R b` using `hbK.restrict_scalars' R`.

Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) (fun p : ι × ι => g p.1 p.2)`. Use `choose P' hP' using hd`. Set `P : Matrix ι ι R` to `Matrix.of fun i j => P' (i, j)`. Establish `hP : ∀ i j, algebraMap R K (P i j) = algebraMap R K d * g i j` using `fun i j => by`. Rewrite using `[← Algebra.smul_def]`.

Conclude with `hP' (i, j)`. Set `D : Matrix ι ι R` to `Matrix.diagonal fun _ => (d : R)`. Establish `hD0 : D.det ≠ 0`. Rewrite using `[Matrix.det_diagonal]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun _ _ => nonZeroDivisors.coe_ne_zero d`.

Establish `hD0' : algebraMap R K D.det ≠ 0` using `fun h => hD0 (hinj (h.trans (map_zero _).symm))`. Establish `hdet : algebraMap R K P.det = algebraMap R K D.det * g.det`. Rewrite using `[RingHom.map_det, RingHom.map_det, ← Matrix.det_mul]`. Use `congr 1`. Use extensionality with `i j`.

Simplify using `[D, hP, Matrix.diagonal_map, Matrix.diagonal_mul]`. Establish `hP0 : P.det ≠ 0` using `fun h => mul_ne_zero hD0' hg (by rw [← hdet, h, map_zero])`. Take `⟨hCA, hlA⟩` from `relLength_span (c := fun j => (d : R) • b j) haR P hP0 (fun j => by`. Rewrite using `[hb, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← algebraMap_smul K (P i j), hP, mul_smul, algebraMap_smul])`. Take `⟨hCB, hlB⟩` from `relLength_span (c := fun j => (d : R) • b j) hbR D hD0 (fun j => by`. Simplify using `[D, Matrix.diagonal_apply, ite_smul])`. Establish `hPn` using `mem_nonZeroDivisors_of_ne_zero hP0`. Establish `hDn` using `mem_nonZeroDivisors_of_ne_zero hD0`.

Take `⟨m, hm⟩` from `ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hPn)`. Take `⟨n, hn⟩` from `ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hDn)`. Take `⟨hcomm, hs⟩` from `signedLength_of_common hCA hCB (hlA.trans hm.symm) (hlB.trans hn.symm)`. Use `⟨hcomm, ?_⟩` and prove the remaining obligations. Establish `hq : g.det = algebraMap R K P.det / algebraMap R K D.det`.

Rewrite using `[hdet, mul_div_cancel_left₀ _ hD0']`. Rewrite using `[hs, hq, map_div₀, Ring.ordFrac_eq_ord R hP0, Ring.ordFrac_eq_ord R hD0, Ring.ordMonoidWithZeroHom_eq_coe R hPn hm.symm, Ring.ordMonoidWithZeroHom_eq_coe R hDn hn.symm, WithZero.exp_sub]`. Both sides reduce to the same expression.
-/
theorem signedLength_span_eq_ordFrac_det {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ι → V} (ha : LinearIndependent K a)
    (g : Matrix ι ι K) (hg : g.det ≠ 0) (hb : ∀ j, b j = ∑ i, g i j • a i) :
    LengthCommensurable (span R (Set.range a)) (span R (Set.range b)) ∧
      Ring.ordFrac R g.det =
        WithZero.exp (signedLength (span R (Set.range a)) (span R (Set.range b))) := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K

  have hbK : LinearIndependent K b := by
    rw [Fintype.linearIndependent_iff] at ha ⊢
    intro v hv
    have h0 : g.mulVec v = 0 := by
      funext i
      refine ha (g.mulVec v) ?_ i
      rw [← hv]
      simp only [hb, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [mul_comm]
    intro i
    exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hg h0) i
  have haR : LinearIndependent R a := ha.restrict_scalars' R
  have hbR : LinearIndependent R b := hbK.restrict_scalars' R

  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun p : ι × ι => g p.1 p.2)
  choose P' hP' using hd
  let P : Matrix ι ι R := Matrix.of fun i j => P' (i, j)
  have hP : ∀ i j, algebraMap R K (P i j) = algebraMap R K d * g i j := fun i j => by
    rw [← Algebra.smul_def]; exact hP' (i, j)
  let D : Matrix ι ι R := Matrix.diagonal fun _ => (d : R)
  have hD0 : D.det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => nonZeroDivisors.coe_ne_zero d
  have hD0' : algebraMap R K D.det ≠ 0 := fun h => hD0 (hinj (h.trans (map_zero _).symm))
  have hdet : algebraMap R K P.det = algebraMap R K D.det * g.det := by
    rw [RingHom.map_det, RingHom.map_det, ← Matrix.det_mul]
    congr 1
    ext i j
    simp [D, hP, Matrix.diagonal_map, Matrix.diagonal_mul]
  have hP0 : P.det ≠ 0 := fun h => mul_ne_zero hD0' hg (by rw [← hdet, h, map_zero])
  obtain ⟨hCA, hlA⟩ := relLength_span (c := fun j => (d : R) • b j) haR P hP0 (fun j => by
    rw [hb, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K (P i j), hP, mul_smul, algebraMap_smul])
  obtain ⟨hCB, hlB⟩ := relLength_span (c := fun j => (d : R) • b j) hbR D hD0 (fun j => by
    simp [D, Matrix.diagonal_apply, ite_smul])
  have hPn := mem_nonZeroDivisors_of_ne_zero hP0
  have hDn := mem_nonZeroDivisors_of_ne_zero hD0
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hPn)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hDn)
  obtain ⟨hcomm, hs⟩ := signedLength_of_common hCA hCB (hlA.trans hm.symm) (hlB.trans hn.symm)
  refine ⟨hcomm, ?_⟩
  have hq : g.det = algebraMap R K P.det / algebraMap R K D.det := by
    rw [hdet, mul_div_cancel_left₀ _ hD0']
  rw [hs, hq, map_div₀, Ring.ordFrac_eq_ord R hP0, Ring.ordFrac_eq_ord R hD0,
    Ring.ordMonoidWithZeroHom_eq_coe R hPn hm.symm,
    Ring.ordMonoidWithZeroHom_eq_coe R hDn hn.symm, WithZero.exp_sub]
  rfl

end GlobalTheory.SignedLengthOrdFracDet
