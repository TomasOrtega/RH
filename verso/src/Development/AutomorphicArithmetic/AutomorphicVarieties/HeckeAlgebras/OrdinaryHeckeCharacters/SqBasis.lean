import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BideterminantRowWeightDominance
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BideterminantAntidiagEvalWeightUnitSupport
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Branching Matrix

namespace UpperTheory.V.Hi

/- English proof (translation)
Establish `h : φ (detPow R n g lam.detShift) = detPow S n (GeneralLinearGroup.map φ g) lam.detShift`. Unfold `detPow`. Rewrite using `[GeneralLinearGroup.map_det, ← map_zpow (Units.map (φ : R →* S))]`. Both sides reduce to the same expression. Unfold `sqAct`.

Rewrite using `[smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul, h, ldtwist_map_rowAct, Matrix.transpose_map]`. Both sides reduce to the same expression.
-/
private theorem map_sqAct {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} (lam : DomWeight n)
    (g : GL (Fin n) R) (f : MvPolynomial (Fin n × Fin n) R) :
    MvPolynomial.map φ (sqAct R n lam g f) = sqAct S n lam (GeneralLinearGroup.map φ g) (MvPolynomial.map φ f) := by
  have h : φ (detPow R n g lam.detShift) = detPow S n (GeneralLinearGroup.map φ g) lam.detShift := by
    unfold detPow
    rw [GeneralLinearGroup.map_det, ← map_zpow (Units.map (φ : R →* S))]
    rfl
  unfold sqAct
  rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul, h, ldtwist_map_rowAct, Matrix.transpose_map]
  rfl

/- English proof (translation)
Set `π` to `Ideal.Quotient.mk (Ideal.span {c})`. Establish `h1 : GeneralLinearGroup.map π g = 1`. Use extensionality with `i j`. Use `(Ideal.Quotient.eq_zero_iff_dvd c _).2 (hg i j)` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, map_sub, sub_eq_zero]`.

Use `this.trans ?_` and prove the remaining obligations. Simplify using `only [Matrix.one_apply, Units.val_one]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `h2 : MvPolynomial.map π (sqAct O n lam g f - f.1) = 0`. Rewrite using `[map_sub, map_sqAct, h1, sub_eq_zero]`.

Conclude with `congrArg Subtype.val (LinearMap.congr_fun (sqRep _ n lam).map_one ⟨_, dualWeylMap _ _ π n n _ _ f.2⟩)`. Choose the witnesses or unpack the hypotheses as in `⟨h, hh⟩ : C c ∣ sqAct O n lam g f - f.1 := by`. Rewrite using `[C_dvd_iff_dvd_coeff]`. Introduce `m`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_dvd, ← coeff_map, h2, coeff_zero]`.

Rewrite `hh` using `[← smul_eq_C_mul]`. Use `⟨h, dualWeylSat O n n _ c h hc ?_, by rw [← hh]; abel⟩` and prove the remaining obligations. Rewrite using `[← hh]`. Conclude with `sub_mem (sqRep O n lam g f).2 f.2`.
-/
private theorem cong {O : Type} [CommRing O] [IsDomain O] {n : ℕ} (lam : DomWeight n) {c : O} (hc : c ≠ 0)
    (g : GL (Fin n) O) (hg : ∀ i j, c ∣ (g.val - 1) i j) (f : nablaSq O n lam) :
    ∃ h ∈ nablaSq O n lam, sqAct O n lam g f = f + c • h := by
  let π := Ideal.Quotient.mk (Ideal.span {c})
  have h1 : GeneralLinearGroup.map π g = 1 := by
    ext i j
    have := (Ideal.Quotient.eq_zero_iff_dvd c _).2 (hg i j)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    refine this.trans ?_
    simp only [Matrix.one_apply, Units.val_one]
    split_ifs <;> simp
  have h2 : MvPolynomial.map π (sqAct O n lam g f - f.1) = 0 := by
    rw [map_sub, map_sqAct, h1, sub_eq_zero]
    exact congrArg Subtype.val (LinearMap.congr_fun (sqRep _ n lam).map_one
      ⟨_, dualWeylMap _ _ π n n _ _ f.2⟩)
  obtain ⟨h, hh⟩ : C c ∣ sqAct O n lam g f - f.1 := by
    rw [C_dvd_iff_dvd_coeff]
    intro m
    rw [← Ideal.Quotient.eq_zero_iff_dvd, ← coeff_map, h2, coeff_zero]
  rw [← smul_eq_C_mul] at hh
  refine ⟨h, dualWeylSat O n n _ c h hc ?_, by rw [← hh]; abel⟩
  rw [← hh]
  exact sub_mem (sqRep O n lam g f).2 f.2

/- English proof (translation)
Rewrite using `[← Finset.prod_zpow, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun i _ => by rw [zpow_add₀ (ht i), zpow_natCast, mul_comm]`.
-/
private theorem prod_wt {K : Type} [Field K] {n : ℕ} (t : Fin n → K) (ht : ∀ i, t i ≠ 0) (s : ℤ) (μ : Fin n → ℕ) :
    (∏ i, t i) ^ s * ∏ i, t i ^ μ i = ∏ i, t i ^ ((μ i : ℤ) + s) := by
  rw [← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [zpow_add₀ (ht i), zpow_natCast, mul_comm]

/- English proof (translation)
Establish `h : g.val.det = ∏ i, g.val i i` using `det_of_upperTriangular fun i j h => hg i j h`. Use `⟨?_, fun i => Finset.prod_ne_zero_iff.1 (h.symm.trans_ne g.det_ne_zero) i (Finset.mem_univ _)⟩` and prove the remaining obligations. Unfold `detPow`. Rewrite using `[Units.val_zpow_eq_zpow_val, ← h]`. Both sides reduce to the same expression.
-/
private theorem detPow_eq {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) (hg : ∀ i j, j < i → g.val i j = 0) (s : ℤ) :
    detPow K n g s = (∏ i, g.val i i) ^ s ∧ ∀ i, g.val i i ≠ 0 := by
  have h : g.val.det = ∏ i, g.val i i := det_of_upperTriangular fun i j h => hg i j h
  refine ⟨?_, fun i => Finset.prod_ne_zero_iff.1 (h.symm.trans_ne g.det_ne_zero) i (Finset.mem_univ _)⟩
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, ← h]
  rfl

/- English proof (translation)
Take `⟨bO, hb, hb'⟩` from `sSBasis O n n lam.natW`. Use `haveI : Finite (ssIdx n n lam.natW) := (sSIdxFinite n n _).to_subtype`. Use `letI := Fintype.ofFinite (ssIdx n n lam.natW)`. Establish `hli` using `ldlat_linInd_base hinj hb.1`. Establish `hsp` using `span_map_weightBasis_eq_dualWeyl (K := K) hb`.

Set `b : Module.Basis (ssIdx n n lam.natW) K (nablaSq K n lam)` to `(Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hsp)`. Establish `hbc : ∀ j, (b j : MvPolynomial (Fin n × Fin n) K) = MvPolynomial.map (algebraMap O K) (bO j)` using `fun j => by`. Simplify using `only [b, Module.Basis.map_apply]`. Conclude with `congrArg Subtype.val (Module.Basis.span_apply hli j)`. Use `choose N sz hsz I hsh hI hbI using fun m => (hb' m).2.2`.

Establish `hexp : ∀ m, bidetExp (sz m) (hsz m) (I m) = m.1` using `fun m => by`. Rewrite using `[← (column_lex_bideterminant O n n _ _ (hsz m) _ (hI m)).1, ← hbI, (hb' m).1]`. Establish `hbK : ∀ j, (b j : MvPolynomial (Fin n × Fin n) K) = bideterminant K (sz j) (hsz j) (I j)` using `fun j => by`. Rewrite using `[hbc, hbI, ldlat_map_bidet]`. Set `J : Fin n × Fin n → K` to `fun v => if v.1 = Fin.rev v.2 then 1 else 0`.

Set `ℓ : nablaSq K n lam →ₗ[K] K` to `(aeval J).toLinearMap ∘ₗ (nablaSq K n lam).subtype`. Establish `hℓ : ∀ f, ℓ f = eval J f` using `fun f => by simp [ℓ, coe_aeval_eq_eval]`. Establish `hne : Nonempty (ssIdx n n lam.natW)`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nonempty_iff]`.

Establish `h1` using `hwMem O n n le_rfl _ (factNatW n lam).1`. Rewrite `h1` using `[← hb.2.1, Set.range_eq_empty, Submodule.span_empty]`. Conclude with `hwNe O n n le_rfl _ h1`. Choose the witnesses or unpack the hypotheses as in `⟨k0, hk0⟩ : ∃ k0, ℓ (b k0) ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Take `⟨m⟩` from `hne`. Set `I' : ∀ k, Fin (sz m k) → Fin n` to `fun k p => ⟨n - sz m k + p, by have := hsz m k; have := p.2; omega⟩`. Establish `h0 : ℓ = 0` using `b.ext h`. Establish `h1` using `(UpperTheory.bideterminant_antidiag_eval_weight_unit_support K n _ (sz m) (hsz m) I').2.1 fun k p => by have := hsz m k; simp only [I']; omega`.

Establish `h2` using `hℓ ⟨bideterminant K (sz m) (hsz m) I', by`. Use `bidetMem K n n _ (sz m) (hsz m) I'` as an intermediate fact. Rewrite using `[hsh] at this⟩` and apply the resulting hypothesis. Rewrite `h2` using `[h0]`. Conclude with `h1.ne_zero h2.symm`.

Establish `hbot : ∀ m, ℓ (b m) ≠ 0 → ∀ k p, (I m k p : ℕ) + sz m k = n + p` using `fun m hm => (UpperTheory.bideterminant_antidiag_eval_weight_unit_support K n _ (sz m) (hsz m) (I m)).2.2 (hI m) (by rwa [hℓ, hbK] at hm)`. Establish `hW` using `fun m => UpperTheory.bideterminant_row_weight_dominance n _ (sz m) (hsz m) (I m) (hI m)`. Establish `huniq : ∀ m, (∀ k p, (I m k p : ℕ) + sz m k = n + p) → m = k0` using `fun m hm => Subtype.ext (by`. Rewrite using `[← hexp, ← hexp]`. Conclude with `((hW k0).2.2 (hbot k0 hk0)).2 _ _ _ _ hm (by rw [hsh, hsh]))`.

Establish `hw0 : ∀ i, rowWt k0.1 i = lam.natW i.rev` using `fun i => by`. Rewrite using `[← hexp, ((hW k0).2.2 (hbot k0 hk0)).1, hsh]`. Establish `hco : ∀ f, b.repr f k0 = ℓ f / ℓ (b k0)` using `fun f => by`. Establish `: b.coord k0 = (ℓ (b k0))⁻¹ • ℓ` using `b.ext fun j => by`. Distinguish the cases in `hj : j = k0`.

Substitute `hj` using the available equality. Simplify using `[hk0]`. Establish `: ℓ (b j) = 0`. Assume the negation of the conclusion as `h`. Conclude with `hj (huniq j (hbot j h))`.

Simplify using `[this, hj]`. Rewrite using `[← Module.Basis.coord_apply, this, LinearMap.smul_apply, smul_eq_mul, div_eq_inv_mul]`. Use `⟨_, inferInstance, inferInstance, k0, b, fun m i => (rowWt m.1 i : ℤ) + lam.detShift, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `c hc g hg i j`. Take `⟨h, hh, e⟩` from `cong lam hc g hg ⟨bO j, by`.

Express the relevant statement in the definitionally equal form `_ ∈ dualWeyl _ _ _ _`. Rewrite using `[← hb.2.1]`. Conclude with `Submodule.subset_span ⟨j, rfl⟩⟩`. Express the relevant statement in the definitionally equal form `_ ∈ dualWeyl _ _ _ _ at hh`. Rewrite `hh` using `[← hb.2.1, Submodule.mem_span_range_iff_exists_fun]`.

Take `⟨x, rfl⟩` from `hh`. Use `⟨x i, ?_⟩` and prove the remaining obligations. Establish `: sqRep K n lam (GeneralLinearGroup.map (algebraMap O K) g) (b j) = b j + ∑ i, algebraMap O K (c * x i) • b i`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[sqRep_coe, hbc, ← map_sqAct, e]`.

Simplify using `[hbc, smul_eq_C_mul, Finset.mul_sum, mul_assoc]`. Rewrite using `[this, map_add, b.repr_self, Finsupp.add_apply, congrFun (b.repr_sum_self _) i, Finsupp.single_apply]`. Simplify using `only [eq_comm]`. Introduce `g hg j`. Establish `: ℓ (sqRep K n lam g (b j)) = (∏ i, g.val i i ^ ((rowWt k0.1 i : ℤ) + lam.detShift)) * ℓ (b j)`.

Rewrite using `[hℓ, hℓ, sqRep_coe, sqAct, smul_eval, hbK, (UpperTheory.bideterminant_antidiag_eval_weight_unit_support K n _ _ (hsz j) (I j)).1 _ hg, (detPow_eq g hg _).1, ← mul_assoc, hsh, ← prod_wt _ (detPow_eq g hg 0).2]`. Simplify using `only [hw0]`. Both sides reduce to the same expression. Rewrite using `[hco, this, mul_div_assoc, ← hco]`. Simplify using `[Finsupp.single_apply]`.

Introduce `g t hg j`. Establish `hu : ∀ i j, j < i → g.val i j = 0` using `fun i j h => by rw [hg, diagonal_apply_ne _ h.ne']`. Establish `hd` using `detPow_eq g hu lam.detShift`. Simplify using `only [hg, diagonal_apply_eq] at hd`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `hwt : IsWeightedHomogeneous (rowW n n) (b j : MvPolynomial (Fin n × Fin n) K) (rowWt j.1)`. Rewrite using `[hbc]`. Introduce `d hd`. Use `hb.2.2 j fun h0 => hd ?_` and prove the remaining obligations. Rewrite using `[coeff_map, h0, map_zero]`.

Rewrite using `[sqRep_coe, sqAct, hg, diagonal_transpose, rowActDiagWeight K n n t _ _ hwt, smul_smul, hd.1, prod_wt _ hd.2]`. Both sides reduce to the same expression. Introduce `i`. Simplify using `only [hw0]`. Conclude with `(factNatW n lam).2.1 _`.

Introduce `j a ha`. Use `(hW j).1 a ha` as an intermediate fact. Rewrite `this` using `[hexp, hsh]`. Simplify using `only [mul_add, Finset.sum_add_distrib, hw0]`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `j hj`. Assume the negation of the conclusion as `h`. Use `hj (huniq j ((hW j).2.1 ?_))` and prove the remaining obligations. Rewrite using `[hexp, hsh]`. Simplify using `only [mul_add, Finset.sum_add_distrib, hw0] at h`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sqBasis (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] (hinj : Function.Injective (algebraMap O K))
    (n : ℕ) (lam : DomWeight n) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (k0 : κ) (b : Module.Basis κ K (nablaSq K n lam)) (μ : κ → Fin n → ℤ),
      (∀ (c : O), c ≠ 0 → ∀ g : GL (Fin n) O, (∀ i j, c ∣ (g.val - 1) i j) → ∀ i j, ∃ x,
        b.repr (sqRep K n lam (GeneralLinearGroup.map (algebraMap O K) g) (b j)) i =
          (if i = j then 1 else 0) + algebraMap O K (c * x)) ∧
      (∀ g : GL (Fin n) K, (∀ i j, j < i → g.val i j = 0) → ∀ j,
        b.repr (sqRep K n lam g (b j)) k0 = if j = k0 then ∏ i, g.val i i ^ μ k0 i else 0) ∧
      (∀ (g : GL (Fin n) K) (t : Fin n → K), g.val = diagonal t → ∀ j, sqRep K n lam g (b j) = (∏ i, t i ^ μ j i) • b j) ∧
      (∀ i, μ k0 i = lam.w i.rev) ∧
      (∀ j (a : Fin n → ℤ), Antitone a → ∑ i, a i * μ k0 i ≤ ∑ i, a i * μ j i) ∧
      ∀ j, j ≠ k0 → ∑ i : Fin n, ((n : ℤ) - 1 - (i : ℕ)) * μ k0 i < ∑ i : Fin n, ((n : ℤ) - 1 - (i : ℕ)) * μ j i := by
  classical
  obtain ⟨bO, hb, hb'⟩ := sSBasis O n n lam.natW
  haveI : Finite (ssIdx n n lam.natW) := (sSIdxFinite n n _).to_subtype
  letI := Fintype.ofFinite (ssIdx n n lam.natW)
  have hli := ldlat_linInd_base hinj hb.1
  have hsp := span_map_weightBasis_eq_dualWeyl (K := K) hb
  let b : Module.Basis (ssIdx n n lam.natW) K (nablaSq K n lam) :=
    (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hsp)
  have hbc : ∀ j, (b j : MvPolynomial (Fin n × Fin n) K) = MvPolynomial.map (algebraMap O K) (bO j) := fun j => by
    simp only [b, Module.Basis.map_apply]
    exact congrArg Subtype.val (Module.Basis.span_apply hli j)
  choose N sz hsz I hsh hI hbI using fun m => (hb' m).2.2
  have hexp : ∀ m, bidetExp (sz m) (hsz m) (I m) = m.1 := fun m => by
    rw [← (column_lex_bideterminant O n n _ _ (hsz m) _ (hI m)).1, ← hbI, (hb' m).1]
  have hbK : ∀ j, (b j : MvPolynomial (Fin n × Fin n) K) = bideterminant K (sz j) (hsz j) (I j) := fun j => by
    rw [hbc, hbI, ldlat_map_bidet]
  let J : Fin n × Fin n → K := fun v => if v.1 = Fin.rev v.2 then 1 else 0
  let ℓ : nablaSq K n lam →ₗ[K] K := (aeval J).toLinearMap ∘ₗ (nablaSq K n lam).subtype
  have hℓ : ∀ f, ℓ f = eval J f := fun f => by simp [ℓ, coe_aeval_eq_eval]
  have hne : Nonempty (ssIdx n n lam.natW) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 := hwMem O n n le_rfl _ (factNatW n lam).1
    rw [← hb.2.1, Set.range_eq_empty, Submodule.span_empty] at h1
    exact hwNe O n n le_rfl _ h1
  obtain ⟨k0, hk0⟩ : ∃ k0, ℓ (b k0) ≠ 0 := by
    by_contra h
    push_neg at h
    obtain ⟨m⟩ := hne
    let I' : ∀ k, Fin (sz m k) → Fin n := fun k p => ⟨n - sz m k + p, by have := hsz m k; have := p.2; omega⟩
    have h0 : ℓ = 0 := b.ext h
    have h1 := (UpperTheory.bideterminant_antidiag_eval_weight_unit_support K n _ (sz m) (hsz m) I').2.1 fun k p => by have := hsz m k; simp only [I']; omega
    have h2 := hℓ ⟨bideterminant K (sz m) (hsz m) I', by
      have := bidetMem K n n _ (sz m) (hsz m) I'
      rwa [hsh] at this⟩
    rw [h0] at h2
    exact h1.ne_zero h2.symm
  have hbot : ∀ m, ℓ (b m) ≠ 0 → ∀ k p, (I m k p : ℕ) + sz m k = n + p := fun m hm =>
    (UpperTheory.bideterminant_antidiag_eval_weight_unit_support K n _ (sz m) (hsz m) (I m)).2.2 (hI m) (by rwa [hℓ, hbK] at hm)
  have hW := fun m => UpperTheory.bideterminant_row_weight_dominance n _ (sz m) (hsz m) (I m) (hI m)
  have huniq : ∀ m, (∀ k p, (I m k p : ℕ) + sz m k = n + p) → m = k0 := fun m hm => Subtype.ext (by
    rw [← hexp, ← hexp]
    exact ((hW k0).2.2 (hbot k0 hk0)).2 _ _ _ _ hm (by rw [hsh, hsh]))
  have hw0 : ∀ i, rowWt k0.1 i = lam.natW i.rev := fun i => by
    rw [← hexp, ((hW k0).2.2 (hbot k0 hk0)).1, hsh]
  have hco : ∀ f, b.repr f k0 = ℓ f / ℓ (b k0) := fun f => by
    have : b.coord k0 = (ℓ (b k0))⁻¹ • ℓ := b.ext fun j => by
      by_cases hj : j = k0
      · subst hj; simp [hk0]
      · have : ℓ (b j) = 0 := by
          by_contra h; exact hj (huniq j (hbot j h))
        simp [this, hj]
    rw [← Module.Basis.coord_apply, this, LinearMap.smul_apply, smul_eq_mul, div_eq_inv_mul]
  refine ⟨_, inferInstance, inferInstance, k0, b, fun m i => (rowWt m.1 i : ℤ) + lam.detShift, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc g hg i j
    obtain ⟨h, hh, e⟩ := cong lam hc g hg ⟨bO j, by
      change _ ∈ dualWeyl _ _ _ _
      rw [← hb.2.1]; exact Submodule.subset_span ⟨j, rfl⟩⟩
    change _ ∈ dualWeyl _ _ _ _ at hh
    rw [← hb.2.1, Submodule.mem_span_range_iff_exists_fun] at hh
    obtain ⟨x, rfl⟩ := hh
    refine ⟨x i, ?_⟩
    have : sqRep K n lam (GeneralLinearGroup.map (algebraMap O K) g) (b j) =
        b j + ∑ i, algebraMap O K (c * x i) • b i := by
      apply Subtype.ext
      rw [sqRep_coe, hbc, ← map_sqAct, e]
      simp [hbc, smul_eq_C_mul, Finset.mul_sum, mul_assoc]
    rw [this, map_add, b.repr_self, Finsupp.add_apply, congrFun (b.repr_sum_self _) i, Finsupp.single_apply]
    simp only [eq_comm]
  · intro g hg j
    have : ℓ (sqRep K n lam g (b j)) = (∏ i, g.val i i ^ ((rowWt k0.1 i : ℤ) + lam.detShift)) * ℓ (b j) := by
      rw [hℓ, hℓ, sqRep_coe, sqAct, smul_eval, hbK, (UpperTheory.bideterminant_antidiag_eval_weight_unit_support K n _ _ (hsz j) (I j)).1 _ hg, (detPow_eq g hg _).1,
        ← mul_assoc, hsh, ← prod_wt _ (detPow_eq g hg 0).2]
      simp only [hw0]
      rfl
    rw [hco, this, mul_div_assoc, ← hco]
    simp [Finsupp.single_apply]
  · intro g t hg j
    have hu : ∀ i j, j < i → g.val i j = 0 := fun i j h => by rw [hg, diagonal_apply_ne _ h.ne']
    have hd := detPow_eq g hu lam.detShift
    simp only [hg, diagonal_apply_eq] at hd
    apply Subtype.ext
    have hwt : IsWeightedHomogeneous (rowW n n) (b j : MvPolynomial (Fin n × Fin n) K) (rowWt j.1) := by
      rw [hbc]
      intro d hd
      refine hb.2.2 j fun h0 => hd ?_
      rw [coeff_map, h0, map_zero]
    rw [sqRep_coe, sqAct, hg, diagonal_transpose, rowActDiagWeight K n n t _ _ hwt, smul_smul, hd.1, prod_wt _ hd.2]
    rfl
  · intro i
    simp only [hw0]
    exact (factNatW n lam).2.1 _
  · intro j a ha
    have := (hW j).1 a ha
    rw [hexp, hsh] at this
    simp only [mul_add, Finset.sum_add_distrib, hw0]
    linarith
  · intro j hj
    by_contra h
    refine hj (huniq j ((hW j).2.1 ?_))
    rw [hexp, hsh]
    simp only [mul_add, Finset.sum_add_distrib, hw0] at h
    linarith

end UpperTheory.V.Hi
