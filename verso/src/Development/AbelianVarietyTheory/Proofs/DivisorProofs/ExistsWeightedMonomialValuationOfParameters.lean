import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdDFormUniformiserCons
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightedMonomialPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueCoordinatesOfLocalModelBelowPlaceStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.MonoVal

/- English proof (translation)
Introduce `L _ c Q hQ`. Use `letI := hQ.isLocalRing`. Introduce `r z hm hd`. Use `letI := (c.codRestrict Q hQ.const_mem).toAlgebra`. Use `haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType`.

Use `haveI : IsNoetherianRing Q := Algebra.EssFiniteType.isNoetherianRing ℂ Q`. Use `⟨inferInstance, isQuasiRegularSeq_of_isRegular ?_⟩` and prove the remaining obligations. Use `isRegular_of_ofList_eq_maximalIdeal ?_ ?_` and prove the remaining obligations. Rewrite using `[ofList_ofFn_eq_span_range, hm]`. Rewrite using `[List.length_ofFn, hd]`.

Use `norm_cast`.
-/
theorem isQuasiRegularSeq_of_locModel : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q),
    letI := hQ.isLocalRing; ∀ (r : ℕ) (z : Fin (r + 1) → Q),
    IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) → ringKrullDim Q = r + 1 →
    IsNoetherianRing Q ∧ IsQuasiRegularSeq Q z := by
  intro L _ c Q hQ
  letI := hQ.isLocalRing
  intro r z hm hd
  letI := (c.codRestrict Q hQ.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType
  haveI : IsNoetherianRing Q := Algebra.EssFiniteType.isNoetherianRing ℂ Q
  refine ⟨inferInstance, isQuasiRegularSeq_of_isRegular ?_⟩
  refine isRegular_of_ofList_eq_maximalIdeal ?_ ?_
  · rw [ofList_ofFn_eq_span_range, hm]
  · rw [List.length_ofFn, hd]
    norm_cast

def powCoeffMatrix {A : Type} [CommRing A] (n : ℕ) (t : A) (e : Fin n → ℕ) (w : Fin n → A) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) A :=
  fun i j => Fin.cases (if j = 0 then 1 else 0)
    (fun i' => Fin.cases (w i' * ((e i' : A) * t ^ (e i' - 1)))
      (fun j' => if j' = i' then t ^ e i' else 0) j) i

/- English proof (translation)
Rewrite using `[Matrix.det_of_lowerTriangular]`. Rewrite using `[Fin.prod_univ_succ]`. Simplify using `[powCoeffMatrix, Finset.prod_pow_eq_pow_sum]`. Introduce `i j hij`. Express the relevant statement in the definitionally equal form `i < j at hij`.

Proceed by induction on `i using Fin.cases with`. Consider the case `zero`. Establish `: j ≠ 0` using `(Fin.pos_iff_ne_zero.mp (lt_of_le_of_lt (Fin.zero_le _) hij))`. Simplify using `[powCoeffMatrix, this]`. Consider the case `succ i'`.

Proceed by induction on `j using Fin.cases with`. Consider the case `zero => exact absurd hij (by simp)`. Consider the case `succ j'`. Establish `: j' ≠ i'`. Introduce `h`.

Substitute `h` using the available equality. Conclude with `lt_irrefl _ hij`. Simplify using `[powCoeffMatrix, this]`.
-/
theorem powCoeffMatrix_det {A : Type} [CommRing A] (n : ℕ) (t : A) (e : Fin n → ℕ)
    (w : Fin n → A) : (powCoeffMatrix n t e w).det = t ^ (∑ i, e i) := by
  rw [Matrix.det_of_lowerTriangular]
  · rw [Fin.prod_univ_succ]
    simp [powCoeffMatrix, Finset.prod_pow_eq_pow_sum]
  · intro i j hij
    change i < j at hij
    induction i using Fin.cases with
    | zero =>
      have : j ≠ 0 := (Fin.pos_iff_ne_zero.mp (lt_of_le_of_lt (Fin.zero_le _) hij))
      simp [powCoeffMatrix, this]
    | succ i' =>
      induction j using Fin.cases with
      | zero => exact absurd hij (by simp)
      | succ j' =>
        have : j' ≠ i' := by
          intro h; subst h; exact lt_irrefl _ hij
        simp [powCoeffMatrix, this]

/- English proof (translation)
Introduce `k A _ _ α n t e w`. Rewrite using `[← powCoeffMatrix_det n t e w]`. Apply `dForm_eq_det_smul` to reduce the goal to its premises. Introduce `i`. Rewrite using `[Fin.sum_univ_succ]`.

Proceed by induction on `i using Fin.cases with`. Consider the case `zero => simp [powCoeffMatrix]`. Consider the case `succ i'`. Simplify using `only [powCoeffMatrix, Fin.cons_succ, Fin.cases_zero, Fin.cases_succ, Fin.cons_zero, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Use `letI := α.toAlgebra`.

Express the relevant statement in the definitionally equal form `KaehlerDifferential.D k A (t ^ e i' * w i') = _`. Rewrite using `[Derivation.leibniz, Derivation.leibniz_pow, add_comm]`. Use `congr 1`. Rewrite using `[mul_smul, mul_smul, ← Nat.cast_smul_eq_nsmul A]`.
-/
theorem dForm_cons_pow_mul : ∀ {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) (n : ℕ) (t : A)
    (e : Fin n → ℕ) (w : Fin n → A),
    dForm α (Fin.cons t (fun i => t ^ e i * w i) : Fin (n + 1) → A) =
      t ^ (∑ i, e i) • dForm α (Fin.cons t w : Fin (n + 1) → A) := by
  intro k A _ _ α n t e w
  rw [← powCoeffMatrix_det n t e w]
  apply dForm_eq_det_smul
  intro i
  rw [Fin.sum_univ_succ]
  induction i using Fin.cases with
  | zero => simp [powCoeffMatrix]
  | succ i' =>
    simp only [powCoeffMatrix, Fin.cons_succ, Fin.cases_zero, Fin.cases_succ, Fin.cons_zero,
      ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    letI := α.toAlgebra
    change KaehlerDifferential.D k A (t ^ e i' * w i') = _
    rw [Derivation.leibniz, Derivation.leibniz_pow, add_comm]
    congr 1
    rw [mul_smul, mul_smul, ← Nat.cast_smul_eq_nsmul A]

/- English proof (translation)
Introduce `L _ c Q hQ`. Use `letI := hQ.isLocalRing`. Introduce `r N z wt hm hdim hw0 hw1 hx`. Take `⟨hN, hqr⟩` from `isQuasiRegularSeq_of_locModel c Q hQ r z hm hdim`. Take `⟨V, hC, u, hu, hirr, hmV, hunit, hloc⟩` from `GlobalTheory.T.exists_weightedMonomialPlace_of_isLocModel c Q hQ r z wt hN hm.symm hqr hw0 hw1`.

Establish `ht0 : (z 0 : L) ≠ 0` using `fun h => hirr.ne_zero (Subtype.ext h)`. Establish `hordt : V.ord (z 0 : L) = 1`. Establish `h` using `V.ord_irreducible hirr`. Conclude with `h`. Establish `h1m : (1 : Q) ∉ IsLocalRing.maximalIdeal Q` using `fun h => (IsLocalRing.maximalIdeal.isMaximal Q).ne_top ((Ideal.eq_top_iff_one _).mpr h)`.

Establish `huu : ∀ i, IsUnit (u i)` using `fun i => by`. Establish `h` using `hunit (MvPolynomial.X i) ⟨Finsupp.single i 1, by rw [MvPolynomial.coeff_X, if_pos rfl]; exact h1m⟩`. Rewrite `h` using `[MvPolynomial.eval₂_X]`. Conclude with `h`. Establish `hu0 : ∀ i, (u i : L) ≠ 0` using `fun i h => (huu i).ne_zero (Subtype.ext h)`.

Establish `hordu : ∀ i, V.ord (u i : L) = 0` using `fun i => V.ord_eq_zero (huu i)`. Establish `hordz : ∀ i, V.ord (z i : L) = wt i`. Introduce `i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Rewrite using `[hordt, hw0]`.

Both sides reduce to the same expression. Rewrite using `[← hu i, V.ord_mul (hu0 i) (pow_ne_zero _ ht0), V.ord_pow, hordu i, hordt]`. Simplify using the standard rewrite rules. Take `⟨φ, hφ⟩ : ∃ φ : Q →+* V.ring, φ = Q.subtype.codRestrict V.ring fun q => hC _ q.2` from `⟨_, rfl⟩`. Establish `hφL : ∀ q : Q, ((φ q : V.ring) : L) = q` using `fun q => by rw [hφ]; rfl`.

Use `⟨V, hC, fun q hq => ?_, hordz, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `V.ord_eq_zero (hq.map φ)`. Rewrite `h` using `[hφL]`. Then use the resulting hypothesis. Introduce `d q hq0 hq`. Establish `hmap : Ideal.map φ (IsLocalRing.maximalIdeal Q) ≤ Ideal.span {(⟨z 0, hC _ (z 0).2⟩ : V.ring)}`.

Rewrite using `[← hirr.maximalIdeal_eq, Ideal.map_le_iff_le_comap]`. Introduce `q hq`. Establish `h` using `hmV q hq`. Rewrite using `[Ideal.mem_comap]`. Use `h using 1` and compare the differences between its conclusion and the goal.

Conclude with `Subtype.ext (hφL q)`. Establish `h2 : φ q ∈ Ideal.span {(⟨z 0, hC _ (z 0).2⟩ : V.ring) ^ d}`. Rewrite using `[← Ideal.span_singleton_pow]`. Use `(Ideal.pow_right_mono hmap d) ?_` and prove the remaining obligations. Rewrite using `[← Ideal.map_pow]`.

Conclude with `Ideal.mem_map_of_mem φ hq`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.1 h2`. Establish `haL : (q : L) = (a : L) * (z 0 : L) ^ d`. Rewrite using `[← hφL q, ← ha]`. Both sides reduce to the same expression.

Establish `ha0 : (a : L) ≠ 0` using `fun h => hq0 (by rw [haL, h, zero_mul])`. Rewrite using `[haL, V.ord_mul ha0 (pow_ne_zero _ ht0), V.ord_pow, hordt, mul_one]`. Use `(V.ord_nonneg_iff ha0).2 a.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce `y hy`.

Take `⟨xT, hxT⟩` from `hx`. Take `⟨j, s, hjN, hsu⟩` from `GlobalTheory.T.exists_residue_coordinates_of_localModel_below_place c Q hQ N r V hC u ⟨xT, hxT⟩ hmV hunit hloc`. Substitute `hjN` using the available equality. Take `⟨w, hw⟩ : ∃ w : Fin (r + j) → V.ring, w = Fin.append u fun i => (⟨s i, hC _ (s i).2⟩ : V.ring)` from `⟨_, rfl⟩`. Rewrite `hsu` using `[← hw]`.

Establish `hG : IsFreeGen V.ring (dForm V.const (Fin.cons ⟨z 0, hC _ (z 0).2⟩ w : Fin (r + j + 1) → V.ring))`. Use `letI := V.const.toAlgebra`. Use `letI := c.toAlgebra`. Use `haveI : IsScalarTower ℂ V.ring L := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI : Algebra.EssFiniteType ℂ V.ring := V.essFiniteType`.

Use `haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ V.ring`. Take `⟨m, z', b, -, hb⟩` from `exists_basis_kaehler_uniformiser ℂ hirr`. Establish `h1` using `trdeg_eq_of_basis_kaehler ℂ L b`. Establish `h2` using `IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hxT`. Rewrite `h2` using `[h1, Cardinal.mk_fin]`.

Choose the witnesses or unpack the hypotheses as in `rfl : r + j = m := by`. Establish `: r + j + 1 = m + 1` using `by exact_mod_cast h2`. Use linear arithmetic over natural numbers and integers. Conclude with `isFreeGen_dForm_uniformiser_cons ℂ V.ring V.const (r + j) _ w V.essFiniteType hirr ⟨b⟩ hsu`. Establish `e1 : dForm c (Fin.cons (z 0 : L) (fun i => (w i : L)) : Fin (r + j + 1) → L) = V.toRat (r + j + 1) (dForm V.const (Fin.cons ⟨z 0, hC _ (z 0).2⟩ w : Fin (r + j + 1) → V.ring))`.

Establish `h` using `TopForm.formMap_dForm (D := r + j + 1) (α := V.const) (β := c) V.ring.subtype rfl (Fin.cons ⟨z 0, hC _ (z 0).2⟩ w : Fin (r + j + 1) → V.ring)`. Use `Eq.trans ?_ h.symm` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `cases i using Fin.cases <;> rfl`.

Establish `hθ0 : dForm c (Fin.cons (z 0 : L) (fun i => (w i : L)) : Fin (r + j + 1) → L) ≠ 0`. Rewrite using `[e1]`. Conclude with `V.toRat_ne_zero hG`. Establish `hθ : V.formOrd (dForm c (Fin.cons (z 0 : L) (fun i => (w i : L)) : Fin (r + j + 1) → L)) = 0`. Rewrite using `[e1]`.

Conclude with `V.formOrd_toRat hG`. Take `⟨a, ha⟩` from `hy.2 (dForm (c.codRestrict Q hQ.const_mem) (Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) : Fin (r + j + 1) → Q))`. Establish `e2 : dForm c (fun i => ((Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) : Fin (r + j + 1) → Q) i : L)) = (a : L) • dForm c (fun i => (y i : L))`. Establish `h` using `congrArg (TopForm.formMap (r + j + 1) Q.subtype (α := c.codRestrict Q hQ.const_mem) (β := c) rfl) ha`. Establish `f1` using `TopForm.formMap_dForm (D := r + j + 1) (α := c.codRestrict Q hQ.const_mem) (β := c) Q.subtype rfl y`.

Establish `f2` using `TopForm.formMap_dForm (D := r + j + 1) (α := c.codRestrict Q hQ.const_mem) (β := c) Q.subtype rfl (Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) : Fin (r + j + 1) → Q)`. Rewrite `h` using `[map_smulₛₗ]`. Conclude with `f2.symm.trans (h.symm.trans (congrArg (Q.subtype a • ·) f1))`. Take `⟨e, he⟩ : ∃ e : Fin (r + j) → ℕ, e = Fin.append (fun i => wt i.succ) (fun _ : Fin j => 0)` from `⟨_, rfl⟩`. Establish `e3 : (fun i => ((Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) : Fin (r + j + 1) → Q) i : L)) = (Fin.cons (z 0 : L) (fun i => (z 0 : L) ^ e i * (w i : L)) : Fin (r + j + 1) → L)`.

Use function extensionality and compare the values at `i`. Use `Fin.cases rfl (fun i => ?_) i` and prove the remaining obligations. Simplify using `only [Fin.cons_succ]`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) i` and prove the remaining obligations. Simplify using `only [he, hw, Fin.append_left]`.

Rewrite using `[← hu i, mul_comm]`. Simplify using `only [he, hw, Fin.append_right, pow_zero, one_mul]`. Establish `hsum : ∑ i, e i = ∑ i : Fin r, wt i.succ`. Rewrite using `[he, Fin.sum_univ_add]`. Simplify using the standard rewrite rules.

Establish `e4 : dForm c (fun i => ((Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) : Fin (r + j + 1) → Q) i : L)) = (z 0 : L) ^ (∑ i : Fin r, wt i.succ) • dForm c (Fin.cons (z 0 : L) (fun i => (w i : L)) : Fin (r + j + 1) → L)`. Rewrite using `[e3, dForm_cons_pow_mul, hsum]`. Establish `hpow0 : ((z 0 : L) ^ (∑ i : Fin r, wt i.succ)) ≠ 0` using `pow_ne_zero _ ht0`. Establish `hne : dForm c (fun i => ((Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) : Fin (r + j + 1) → Q) i : L)) ≠ 0`. Rewrite using `[e4]`.

Conclude with `smul_ne_zero hpow0 hθ0`. Establish `ha0 : (a : L) ≠ 0` using `fun h => hne (by rw [e2, h, zero_smul])`. Establish `hy0 : dForm c (fun i => (y i : L)) ≠ 0` using `fun h => hne (by rw [e2, h, smul_zero])`. Establish `o1` using `V.formOrd_smul hxT hθ0 hpow0`. Establish `o2` using `V.formOrd_smul hxT hy0 ha0`.

Rewrite `o1` using `[← e4, hθ, V.ord_pow, hordt]`. Rewrite `o2` using `[← e2, o1]`. Establish `hnna` using `(V.ord_nonneg_iff ha0).2 (hC _ a.2)`. Rewrite using `[Fin.sum_univ_succ, hw0]`. Move the coercions through the operations in `at o2 ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem monomial_place : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q), letI := hQ.isLocalRing;
  ∀ (r N : ℕ) (z : Fin (r + 1) → Q) (wt : Fin (r + 1) → ℕ),
  IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) → ringKrullDim Q = r + 1 → wt 0 = 1 → (∀ i, 1 ≤ wt i) →
  (∃ x : Fin N → L, TrBasis c x) →
  ∃ V : Place c, V.Contains Q ∧ (∀ q : Q, IsUnit q → V.ord q = 0) ∧ (∀ i, V.ord (z i) = wt i) ∧
    (∀ (d : ℕ) (q : Q), (q : L) ≠ 0 → q ∈ IsLocalRing.maximalIdeal Q ^ d → (d : ℤ) ≤ V.ord q) ∧
    ∀ y : Fin N → Q, IsFreeGen Q (dForm (c.codRestrict Q hQ.const_mem) y) →
      V.formOrd (dForm c (fun i => (y i : L))) + 1 ≤ ∑ i, (wt i : ℤ) := by
  intro L _ c Q hQ
  letI := hQ.isLocalRing
  intro r N z wt hm hdim hw0 hw1 hx
  obtain ⟨hN, hqr⟩ := isQuasiRegularSeq_of_locModel c Q hQ r z hm hdim
  obtain ⟨V, hC, u, hu, hirr, hmV, hunit, hloc⟩ := GlobalTheory.T.exists_weightedMonomialPlace_of_isLocModel c Q hQ r z wt hN hm.symm hqr hw0 hw1
  have ht0 : (z 0 : L) ≠ 0 := fun h => hirr.ne_zero (Subtype.ext h)
  have hordt : V.ord (z 0 : L) = 1 := by
    have h := V.ord_irreducible hirr
    exact h
  have h1m : (1 : Q) ∉ IsLocalRing.maximalIdeal Q := fun h =>
    (IsLocalRing.maximalIdeal.isMaximal Q).ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have huu : ∀ i, IsUnit (u i) := fun i => by
    have h := hunit (MvPolynomial.X i) ⟨Finsupp.single i 1, by rw [MvPolynomial.coeff_X, if_pos rfl]; exact h1m⟩
    rw [MvPolynomial.eval₂_X] at h
    exact h
  have hu0 : ∀ i, (u i : L) ≠ 0 := fun i h => (huu i).ne_zero (Subtype.ext h)
  have hordu : ∀ i, V.ord (u i : L) = 0 := fun i => V.ord_eq_zero (huu i)
  have hordz : ∀ i, V.ord (z i : L) = wt i := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [hordt, hw0]; rfl
    · rw [← hu i, V.ord_mul (hu0 i) (pow_ne_zero _ ht0), V.ord_pow, hordu i, hordt]
      simp

  obtain ⟨φ, hφ⟩ : ∃ φ : Q →+* V.ring, φ = Q.subtype.codRestrict V.ring fun q => hC _ q.2 :=
    ⟨_, rfl⟩
  have hφL : ∀ q : Q, ((φ q : V.ring) : L) = q := fun q => by rw [hφ]; rfl
  refine ⟨V, hC, fun q hq => ?_, hordz, ?_, ?_⟩
  · have h := V.ord_eq_zero (hq.map φ)
    rwa [hφL] at h
  · intro d q hq0 hq
    have hmap : Ideal.map φ (IsLocalRing.maximalIdeal Q) ≤ Ideal.span {(⟨z 0, hC _ (z 0).2⟩ : V.ring)} := by
      rw [← hirr.maximalIdeal_eq, Ideal.map_le_iff_le_comap]
      intro q hq
      have h := hmV q hq
      rw [Ideal.mem_comap]
      convert h using 1
      exact Subtype.ext (hφL q)
    have h2 : φ q ∈ Ideal.span {(⟨z 0, hC _ (z 0).2⟩ : V.ring) ^ d} := by
      rw [← Ideal.span_singleton_pow]
      refine (Ideal.pow_right_mono hmap d) ?_
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem φ hq
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h2
    have haL : (q : L) = (a : L) * (z 0 : L) ^ d := by
      rw [← hφL q, ← ha]
      rfl
    have ha0 : (a : L) ≠ 0 := fun h => hq0 (by rw [haL, h, zero_mul])
    rw [haL, V.ord_mul ha0 (pow_ne_zero _ ht0), V.ord_pow, hordt, mul_one]
    have := (V.ord_nonneg_iff ha0).2 a.2
    omega

  · intro y hy
    obtain ⟨xT, hxT⟩ := hx
    obtain ⟨j, s, hjN, hsu⟩ := GlobalTheory.T.exists_residue_coordinates_of_localModel_below_place c Q hQ N r V hC u ⟨xT, hxT⟩ hmV hunit hloc
    subst hjN
    obtain ⟨w, hw⟩ : ∃ w : Fin (r + j) → V.ring,
        w = Fin.append u fun i => (⟨s i, hC _ (s i).2⟩ : V.ring) := ⟨_, rfl⟩
    rw [← hw] at hsu
    have hG : IsFreeGen V.ring
        (dForm V.const (Fin.cons ⟨z 0, hC _ (z 0).2⟩ w : Fin (r + j + 1) → V.ring)) := by
      letI := V.const.toAlgebra
      letI := c.toAlgebra
      haveI : IsScalarTower ℂ V.ring L := IsScalarTower.of_algebraMap_eq' rfl
      haveI : Algebra.EssFiniteType ℂ V.ring := V.essFiniteType
      haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ V.ring
      obtain ⟨m, z', b, -, hb⟩ := exists_basis_kaehler_uniformiser ℂ hirr
      have h1 := trdeg_eq_of_basis_kaehler ℂ L b
      have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hxT
      rw [h1, Cardinal.mk_fin] at h2
      obtain rfl : r + j = m := by
        have : r + j + 1 = m + 1 := by exact_mod_cast h2
        omega
      exact isFreeGen_dForm_uniformiser_cons ℂ V.ring V.const (r + j) _ w V.essFiniteType hirr
        ⟨b⟩ hsu
    have e1 : dForm c (Fin.cons (z 0 : L) (fun i => (w i : L)) : Fin (r + j + 1) → L) =
        V.toRat (r + j + 1)
          (dForm V.const (Fin.cons ⟨z 0, hC _ (z 0).2⟩ w : Fin (r + j + 1) → V.ring)) := by
      have h := TopForm.formMap_dForm (D := r + j + 1) (α := V.const) (β := c) V.ring.subtype rfl
        (Fin.cons ⟨z 0, hC _ (z 0).2⟩ w : Fin (r + j + 1) → V.ring)
      refine Eq.trans ?_ h.symm
      congr 1
      funext i
      cases i using Fin.cases <;> rfl
    have hθ0 : dForm c (Fin.cons (z 0 : L) (fun i => (w i : L)) : Fin (r + j + 1) → L) ≠ 0 := by
      rw [e1]; exact V.toRat_ne_zero hG
    have hθ : V.formOrd
        (dForm c (Fin.cons (z 0 : L) (fun i => (w i : L)) : Fin (r + j + 1) → L)) = 0 := by
      rw [e1]; exact V.formOrd_toRat hG
    obtain ⟨a, ha⟩ := hy.2 (dForm (c.codRestrict Q hQ.const_mem)
      (Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) : Fin (r + j + 1) → Q))
    have e2 : dForm c (fun i => ((Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) :
          Fin (r + j + 1) → Q) i : L)) = (a : L) • dForm c (fun i => (y i : L)) := by
      have h := congrArg (TopForm.formMap (r + j + 1) Q.subtype
        (α := c.codRestrict Q hQ.const_mem) (β := c) rfl) ha
      have f1 := TopForm.formMap_dForm (D := r + j + 1) (α := c.codRestrict Q hQ.const_mem) (β := c)
        Q.subtype rfl y
      have f2 := TopForm.formMap_dForm (D := r + j + 1) (α := c.codRestrict Q hQ.const_mem) (β := c)
        Q.subtype rfl (Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) : Fin (r + j + 1) → Q)
      rw [map_smulₛₗ] at h
      exact f2.symm.trans (h.symm.trans (congrArg (Q.subtype a • ·) f1))
    obtain ⟨e, he⟩ : ∃ e : Fin (r + j) → ℕ,
        e = Fin.append (fun i => wt i.succ) (fun _ : Fin j => 0) := ⟨_, rfl⟩
    have e3 : (fun i => ((Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) :
          Fin (r + j + 1) → Q) i : L)) =
        (Fin.cons (z 0 : L) (fun i => (z 0 : L) ^ e i * (w i : L)) : Fin (r + j + 1) → L) := by
      funext i
      refine Fin.cases rfl (fun i => ?_) i
      simp only [Fin.cons_succ]
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [he, hw, Fin.append_left]
        rw [← hu i, mul_comm]
      · simp only [he, hw, Fin.append_right, pow_zero, one_mul]
    have hsum : ∑ i, e i = ∑ i : Fin r, wt i.succ := by
      rw [he, Fin.sum_univ_add]
      simp
    have e4 : dForm c (fun i => ((Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) :
          Fin (r + j + 1) → Q) i : L)) =
        (z 0 : L) ^ (∑ i : Fin r, wt i.succ) •
          dForm c (Fin.cons (z 0 : L) (fun i => (w i : L)) : Fin (r + j + 1) → L) := by
      rw [e3, dForm_cons_pow_mul, hsum]
    have hpow0 : ((z 0 : L) ^ (∑ i : Fin r, wt i.succ)) ≠ 0 := pow_ne_zero _ ht0
    have hne : dForm c (fun i => ((Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) :
          Fin (r + j + 1) → Q) i : L)) ≠ 0 := by
      rw [e4]
      exact smul_ne_zero hpow0 hθ0
    have ha0 : (a : L) ≠ 0 := fun h => hne (by rw [e2, h, zero_smul])
    have hy0 : dForm c (fun i => (y i : L)) ≠ 0 := fun h => hne (by rw [e2, h, smul_zero])
    have o1 := V.formOrd_smul hxT hθ0 hpow0
    have o2 := V.formOrd_smul hxT hy0 ha0
    rw [← e4, hθ, V.ord_pow, hordt] at o1
    rw [← e2, o1] at o2
    have hnna := (V.ord_nonneg_iff ha0).2 (hC _ a.2)
    rw [Fin.sum_univ_succ, hw0]
    push_cast at o2 ⊢
    linarith

end GlobalTheory.MonoVal
