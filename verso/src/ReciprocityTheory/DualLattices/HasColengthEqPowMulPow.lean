import ReciprocityTheory.DualLattices.MemSupOfRestrictToSubgroupMemSq

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

/- English proof (translation)
Rewrite using `[QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', (QuotientAddGroup.eq_zero_iff (k : N)).mpr k.2, add_zero]`.
-/
theorem quotient_out_add_coe (K : AddSubgroup N) (q : N ⧸ K) (k : K) :
    ((q.out + k : N) : N ⧸ K) = q := by
  rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq',
    (QuotientAddGroup.eq_zero_iff (k : N)).mpr k.2, add_zero]

def quotientProdSubgroupEquiv (K : AddSubgroup N) : (N ⧸ K) × K ≃ N where
  toFun p := p.1.out + p.2
  invFun x := ((x : N ⧸ K),
    ⟨-((x : N ⧸ K).out) + x, QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)⟩)
  left_inv := by
    rintro ⟨q, k⟩
    refine Prod.ext (quotient_out_add_coe K q k) (Subtype.ext ?_)
    show -((((q.out + k : N)) : N ⧸ K).out) + (q.out + k) = k
    rw [quotient_out_add_coe K q k]
    abel
  right_inv := by
    intro x
    show (x : N ⧸ K).out + (-((x : N ⧸ K).out) + x) = x
    abel

/- English proof (translation)
Use `choose M hM using hE`. Establish `hEM : E = (Matrix.of M).map (algebraMap R C)`. Use extensionality with `i j`. Conclude with `(hM i j).symm`. Rewrite using `[hEM, det_map_algebraMap]`.

Conclude with `hv.map_le_one _`.
-/
private theorem valuation_det_le_one_of_integral_entries (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    (E : Matrix X X C) (hE : ∀ i j, ∃ r : R, algebraMap R C r = E i j) : v E.det ≤ 1 := by
  choose M hM using hE
  have hEM : E = (Matrix.of M).map (algebraMap R C) := by
    ext i j
    exact (hM i j).symm
  rw [hEM, det_map_algebraMap]
  exact hv.map_le_one _

/- English proof (translation)
Introduce `c cB cK hc hcB hcK`. Take `⟨β, hβ, hAK⟩` from `exists_basis_map_restrictToSubgroup hv AA K`. Take `⟨f, hfA, hfu⟩` from `exists_coset_basis hv AA K`. Take `⟨g, hgA, hgdet⟩` from `exists_family_valuation_det_eq_one hv AA K β hβ hAK`. Take `⟨P, hP, rfl⟩` from `hc`.

Take `⟨Q, hQ, rfl⟩` from `hcB`. Take `⟨β', hβ', rfl⟩` from `hcK`. Take `⟨P0, hP0, hAP0⟩` from `AA.lat`. Establish `hint : ∀ {F : N → C}, F ∈ AA.carrier → ∀ x, ∃ r : R, algebraMap R C r = F x` using `fun hF x => AA.le_int hF x`. Establish `hK : v β'.det = v β.det` using `valuation_det_eq_of_span_eq_alt hv hβ (hAK.symm.trans hβ')`.

Establish `hmm1 : ∀ x, v (h3mm K β f x).det = 1`. Introduce `x`. Establish `hdec : ∀ l, ∃ e : K → N ⧸ K → C, (∀ j, e j ∈ AA.carrier.comap (pullQ (R` using `R) K)) ∧ g l = ∑ j, pullQ (R := R) K (e j) * f j := by`. Introduce `l`. Take `⟨b, ⟨hb, hgb⟩, -⟩` from `hfu (g l) (hgA l)`.

Use `choose e he hbe using fun j => Submodule.mem_map.mp (hb j)`. Use `⟨e, he, ?_⟩` and prove the remaining obligations. Rewrite using `[hgb]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [hbe j]`. Use `choose e he hge using hdec`.

Set `Bx : Matrix K K C` to `Matrix.of fun l j => e l j (x : N ⧸ K)`. Establish `hmul : h3mm K β g x = Bx * h3mm K β f x`. Use extensionality with `l m`. Simplify using `only [h3mm, Matrix.of_apply, Matrix.mul_apply, Bx]`. Rewrite using `[hge l, cosetCoordinates_sum, Finset.sum_apply]`.

Simplify using `only [cosetCoordinates_pullbackQuotient_mul, Pi.smul_apply, smul_eq_mul]`. Establish `hB1 : v Bx.det ≤ 1` using `valuation_det_le_one_of_integral_entries hv Bx fun l j => by`. Take `⟨r, hr⟩` from `hint (Submodule.mem_comap.mp (he l j)) x`. Conclude with `⟨r, hr⟩`. Establish `hF1 : v (h3mm K β f x).det ≤ 1` using `valuation_det_le_one_of_integral_entries hv _ fun j m => hint (cosetCoordinates_mem AA K β hβ hAK (hfA j) m) x`.

Establish `h` using `hgdet x`. Rewrite `h` using `[hmul, Matrix.det_mul, map_mul, mul_comm]`. Conclude with `eq_one_of_le_one_of_mul_eq_one hF1 hB1 h`. Set `e : K × (N ⧸ K) ≃ N` to `(Equiv.prodComm _ _).trans (quotientProdSubgroupEquiv K)`. Establish `he_apply : ∀ p : K × (N ⧸ K), e p = p.2.out + p.1` using `fun p => rfl`.

Set `Φ : Matrix N N C` to `fun x n => Q (x : N ⧸ K) (e.symm n).2 * f (e.symm n).1 x`. Establish `hspan : AA.carrier = Submodule.span R (Set.range fun n x => Φ x n)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `G hG`. Take `⟨b, ⟨hb, hGb⟩, -⟩` from `hfu G hG`.

Rewrite using `[hGb]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Take `⟨b', hb', hbb'⟩` from `Submodule.mem_map.mp (hb j)`. Rewrite `hb'` using `[hQ]`. Take `⟨r, hr⟩` from `(Submodule.mem_span_range_iff_exists_fun R).mp hb'`.

Rewrite using `[← hbb', ← hr, map_sum, Finset.sum_mul]`. Use `sum_mem fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_mul_assoc]`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ⟨e (j, s), ?_⟩)` and prove the remaining obligations. Use function extensionality and compare the values at `x`.

Simplify using `only [Φ, Equiv.symm_apply_apply]`. Both sides reduce to the same expression. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨n, rfl⟩`. Establish `h1 : (fun q : N ⧸ K => Q q (e.symm n).2) ∈ AA.carrier.comap (pullQ (R` using `R) K) := by`.

Rewrite using `[hQ]`. Conclude with `Submodule.subset_span ⟨_, rfl⟩`. Conclude with `AA.mul_mem _ _ h1 (hfA _)`. Establish `hdetΦ : v Φ.det = v Q.det ^ Fintype.card K * v β.det ^ Fintype.card (N ⧸ K)`. Rewrite using `[← Matrix.det_submatrix_equiv_self e Φ]`.

Establish `hblk : Φ.submatrix e e = Matrix.blockDiagonal (fun q : N ⧸ K => β * (h3mm K β f q.out)ᵀ) * Matrix.kroneckerMap (· * ·) (1 : Matrix K K C) Q`. Use extensionality with `⟨k, q⟩ ⟨j, s⟩`. Use `show Q ((e (k, q) : N) : N ⧸ K) (e.symm (e (j, s))).2 * f (e.symm (e (j, s))).1 (e (k, q)) = _`. Rewrite using `[Equiv.symm_apply_apply, he_apply]`. Simplify using `only`.

Rewrite using `[quotient_out_add_coe K q k, cosetCoordinates_expand K β hβ (f j) q.out k, Matrix.mul_apply]`. Simplify using `only [Fintype.sum_prod_type, Matrix.blockDiagonal_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul, zero_mul, mul_ite, mul_one, mul_zero, one_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]`. Use `conv_rhs => rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]`. Simplify using `only [eq_self_iff_true, if_true, Finset.sum_ite_eq, Finset.mem_univ]`. Rewrite using `[mul_comm]`.

Both sides reduce to the same expression. Establish `hq : ∀ q : N ⧸ K, v (β * (h3mm K β f q.out)ᵀ).det = v β.det`. Introduce `q`. Rewrite using `[Matrix.det_mul, Matrix.det_transpose, map_mul, hmm1, mul_one]`. Rewrite using `[hblk, Matrix.det_mul, Matrix.det_blockDiagonal, Matrix.det_kronecker, Matrix.det_one, one_pow, one_mul, map_mul, map_prod, map_pow]`.

Simplify using `only [hq, Finset.prod_const, Finset.card_univ]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `valuation_det_eq_of_span_eq_alt hv hP0 (hAP0.symm.trans hP)`. Establish `h2` using `valuation_det_eq_of_span_eq_alt hv hP0 (hAP0.symm.trans hspan)`. Rewrite using `[h1, ← h2, hdetΦ, hK]`.
-/
theorem hasColength_eq_pow_mul_pow (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] [DecidableEq (N ⧸ K)] [Fintype (N ⧸ K)] :
    ∀ c cB cK, HasColen R v AA.carrier c →
      HasColen R v (AA.carrier.comap (pullQ (R := R) K)) cB →
      HasColen R v (AA.carrier.map (resK (R := R) K)) cK →
      c = cB ^ Fintype.card K * cK ^ Fintype.card (N ⧸ K) := by
  intro c cB cK hc hcB hcK
  obtain ⟨β, hβ, hAK⟩ := exists_basis_map_restrictToSubgroup hv AA K
  obtain ⟨f, hfA, hfu⟩ := exists_coset_basis hv AA K
  obtain ⟨g, hgA, hgdet⟩ := exists_family_valuation_det_eq_one hv AA K β hβ hAK
  obtain ⟨P, hP, rfl⟩ := hc
  obtain ⟨Q, hQ, rfl⟩ := hcB
  obtain ⟨β', hβ', rfl⟩ := hcK
  obtain ⟨P0, hP0, hAP0⟩ := AA.lat
  have hint : ∀ {F : N → C}, F ∈ AA.carrier → ∀ x, ∃ r : R, algebraMap R C r = F x :=
    fun hF x => AA.le_int hF x
  have hK : v β'.det = v β.det := valuation_det_eq_of_span_eq_alt hv hβ (hAK.symm.trans hβ')
  have hmm1 : ∀ x, v (h3mm K β f x).det = 1 := by
    intro x
    have hdec : ∀ l, ∃ e : K → N ⧸ K → C,
        (∀ j, e j ∈ AA.carrier.comap (pullQ (R := R) K)) ∧
          g l = ∑ j, pullQ (R := R) K (e j) * f j := by
      intro l
      obtain ⟨b, ⟨hb, hgb⟩, -⟩ := hfu (g l) (hgA l)
      choose e he hbe using fun j => Submodule.mem_map.mp (hb j)
      refine ⟨e, he, ?_⟩
      rw [hgb]
      exact Finset.sum_congr rfl fun j _ => by rw [hbe j]
    choose e he hge using hdec
    let Bx : Matrix K K C := Matrix.of fun l j => e l j (x : N ⧸ K)
    have hmul : h3mm K β g x = Bx * h3mm K β f x := by
      ext l m
      simp only [h3mm, Matrix.of_apply, Matrix.mul_apply, Bx]
      rw [hge l, cosetCoordinates_sum, Finset.sum_apply]
      simp only [cosetCoordinates_pullbackQuotient_mul, Pi.smul_apply, smul_eq_mul]
    have hB1 : v Bx.det ≤ 1 := valuation_det_le_one_of_integral_entries hv Bx fun l j => by
      obtain ⟨r, hr⟩ := hint (Submodule.mem_comap.mp (he l j)) x
      exact ⟨r, hr⟩
    have hF1 : v (h3mm K β f x).det ≤ 1 := valuation_det_le_one_of_integral_entries hv _ fun j m =>
      hint (cosetCoordinates_mem AA K β hβ hAK (hfA j) m) x
    have h := hgdet x
    rw [hmul, Matrix.det_mul, map_mul, mul_comm] at h
    exact eq_one_of_le_one_of_mul_eq_one hF1 hB1 h
  let e : K × (N ⧸ K) ≃ N := (Equiv.prodComm _ _).trans (quotientProdSubgroupEquiv K)
  have he_apply : ∀ p : K × (N ⧸ K), e p = p.2.out + p.1 := fun p => rfl
  let Φ : Matrix N N C := fun x n => Q (x : N ⧸ K) (e.symm n).2 * f (e.symm n).1 x
  have hspan : AA.carrier = Submodule.span R (Set.range fun n x => Φ x n) := by
    apply le_antisymm
    · intro G hG
      obtain ⟨b, ⟨hb, hGb⟩, -⟩ := hfu G hG
      rw [hGb]
      refine sum_mem fun j _ => ?_
      obtain ⟨b', hb', hbb'⟩ := Submodule.mem_map.mp (hb j)
      rw [hQ] at hb'
      obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hb'
      rw [← hbb', ← hr, map_sum, Finset.sum_mul]
      refine sum_mem fun s _ => ?_
      rw [map_smul, smul_mul_assoc]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨e (j, s), ?_⟩)
      funext x
      simp only [Φ, Equiv.symm_apply_apply]
      rfl
    · rw [Submodule.span_le]
      rintro _ ⟨n, rfl⟩
      have h1 : (fun q : N ⧸ K => Q q (e.symm n).2) ∈ AA.carrier.comap (pullQ (R := R) K) := by
        rw [hQ]
        exact Submodule.subset_span ⟨_, rfl⟩
      exact AA.mul_mem _ _ h1 (hfA _)
  have hdetΦ : v Φ.det = v Q.det ^ Fintype.card K * v β.det ^ Fintype.card (N ⧸ K) := by
    rw [← Matrix.det_submatrix_equiv_self e Φ]
    have hblk : Φ.submatrix e e = Matrix.blockDiagonal (fun q : N ⧸ K =>
        β * (h3mm K β f q.out)ᵀ) * Matrix.kroneckerMap (· * ·) (1 : Matrix K K C) Q := by
      ext ⟨k, q⟩ ⟨j, s⟩
      show Q ((e (k, q) : N) : N ⧸ K) (e.symm (e (j, s))).2 * f (e.symm (e (j, s))).1 (e (k, q)) = _
      rw [Equiv.symm_apply_apply, he_apply]
      dsimp only
      rw [quotient_out_add_coe K q k, cosetCoordinates_expand K β hβ (f j) q.out k, Matrix.mul_apply]
      simp only [Fintype.sum_prod_type, Matrix.blockDiagonal_apply, Matrix.kroneckerMap_apply,
        Matrix.one_apply, ite_mul, zero_mul, mul_ite, mul_one, mul_zero, one_mul,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]
      conv_rhs => rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
      simp only [eq_self_iff_true, if_true, Finset.sum_ite_eq, Finset.mem_univ]
      rw [mul_comm]
      rfl
    have hq : ∀ q : N ⧸ K, v (β * (h3mm K β f q.out)ᵀ).det = v β.det := by
      intro q
      rw [Matrix.det_mul, Matrix.det_transpose, map_mul, hmm1, mul_one]
    rw [hblk, Matrix.det_mul, Matrix.det_blockDiagonal, Matrix.det_kronecker, Matrix.det_one,
      one_pow, one_mul, map_mul, map_prod, map_pow]
    simp only [hq, Finset.prod_const, Finset.card_univ]
    ring
  have h1 := valuation_det_eq_of_span_eq_alt hv hP0 (hAP0.symm.trans hP)
  have h2 := valuation_det_eq_of_span_eq_alt hv hP0 (hAP0.symm.trans hspan)
  rw [h1, ← h2, hdetΦ, hK]

end ReciprocityTheory.PGsh.L2
