import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteClsAndStab
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionLevelSupNormUniformInLatticeStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdmissibleLatticeFamilyHermitianWeilActionStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThHSiegelOperatorStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelOperatorHermitianEisensteinSeriesStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilDifferenceAutomorphyLinearityStatement

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}

omit [IsCMField E] in

/- English proof (translation)
Take `⟨y, hy0, hy⟩` from `exists_integral_multiples ℤ ℚ (Finset.univ.image fun p : α × β => γ p.1 p.2)`. Use `⟨y.natAbs, Int.natAbs_pos.2 hy0, fun i j => ?_⟩` and prove the remaining obligations. Establish `h` using `hy (γ i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)`. Rewrite using `[Matrix.smul_apply, smul_eq_mul, Nat.cast_natAbs]`. Rewrite `h` using `[zsmul_eq_mul]`.

Break down `abs_choice y with e | e` into its components or cases. Rewrite using `[e]`. Conclude with `h`. Rewrite using `[e, Int.cast_neg, neg_mul]`. Conclude with `h.neg`.
-/
theorem exists_den {α β : Type} [Fintype α] [Fintype β] (γ : Matrix α β E) :
    ∃ c : ℕ, 0 < c ∧ Den c γ := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : α × β => γ p.1 p.2)
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun i j => ?_⟩
  have h := hy (γ i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
  rw [Matrix.smul_apply, smul_eq_mul, Nat.cast_natAbs]
  rw [zsmul_eq_mul] at h
  rcases abs_choice y with e | e
  · rw [e]; exact h
  · rw [e, Int.cast_neg, neg_mul]; exact h.neg

omit [NumberField E] [IsCMField E] in

/- English proof (translation)
Take `⟨i, hi⟩` from `Function.ne_iff.1 hv`. Set `b : Matrix (Fin (N + 1)) (Fin (N + 1)) E` to `((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) E).updateCol i v).submatrix id (Equiv.swap 0 i)`. Establish `hd : ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) E).updateCol i v).det = v i`. Rewrite using `[← Matrix.cramer_apply, Matrix.cramer_one]`. Both sides reduce to the same expression.

Establish `hb : IsUnit b.det`. Rewrite using `[Matrix.det_permute', hd]`. Use `IsUnit.mul ?_ (isUnit_iff_ne_zero.2 hi)` and prove the remaining obligations. Conclude with `(Equiv.Perm.sign (Equiv.swap 0 i)).isUnit.map (Int.castRingHom E)`. Establish `hbv : b *ᵥ Pi.single 0 1 = v`.

Use extensionality with `k`. Simplify using `[b]`. Use `⟨b⁻¹, b, Matrix.mul_nonsing_inv b hb, ?_⟩` and prove the remaining obligations. Rewrite using `[← hbv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul b hb, Matrix.one_mulVec]`.
-/
theorem exists_inv (v : Fin (N + 1) → E) (hv : v ≠ 0) :
    ∃ a b : Matrix (Fin (N + 1)) (Fin (N + 1)) E, b * a = 1 ∧ a *ᵥ v = Pi.single 0 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  let b : Matrix (Fin (N + 1)) (Fin (N + 1)) E :=
    ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) E).updateCol i v).submatrix id (Equiv.swap 0 i)
  have hd : ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) E).updateCol i v).det = v i := by
    rw [← Matrix.cramer_apply, Matrix.cramer_one]; rfl
  have hb : IsUnit b.det := by
    rw [Matrix.det_permute', hd]
    refine IsUnit.mul ?_ (isUnit_iff_ne_zero.2 hi)
    exact (Equiv.Perm.sign (Equiv.swap 0 i)).isUnit.map (Int.castRingHom E)
  have hbv : b *ᵥ Pi.single 0 1 = v := by
    ext k; simp [b]
  refine ⟨b⁻¹, b, Matrix.mul_nonsing_inv b hb, ?_⟩
  rw [← hbv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul b hb, Matrix.one_mulVec]

omit [NumberField E] [IsCMField E] in

/- English proof (translation)
Introduce `τ`. Establish `e : imH (pushZ Ψ Z v t τ) = imH (Z τ) + (t : ℂ) • vecMulVec (fun a => τ.1 (v a)) (star fun a => τ.1 (v a))`. Use extensionality with `i j`. Simplify using `[imH, pushZ, vecMulVec_apply, Matrix.conjTranspose_apply]`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `(-2 * (t : ℂ) * τ.1 (v i) * conj (τ.1 (v j))) * I_sq`. Rewrite using `[e]`. Conclude with `(hZ τ).add_posSemidef ((Matrix.posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast ht))`.
-/
theorem pushZ_mem (Ψ : Finset (E →+* ℂ)) {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) (v : Fin N → E) {t : ℝ}
    (ht : 0 ≤ t) : pushZ Ψ Z v t ∈ Hn Ψ N := by
  intro τ
  have e : imH (pushZ Ψ Z v t τ) = imH (Z τ) +
      (t : ℂ) • vecMulVec (fun a => τ.1 (v a)) (star fun a => τ.1 (v a)) := by
    ext i j
    simp [imH, pushZ, vecMulVec_apply, Matrix.conjTranspose_apply]
    field_simp
    linear_combination (-2 * (t : ℂ) * τ.1 (v i) * conj (τ.1 (v j))) * I_sq
  rw [e]
  exact (hZ τ).add_posSemidef
    ((Matrix.posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast ht))

/- English proof (translation)
Establish `e : ccT (Matrix.fromBlocks a 0 0 (ccT b) : M2 E N) = Matrix.fromBlocks (ccT a) 0 0 b`. Apply the tactic sequence `ext (i | i) (j | j) <;> simp [ccT, cc]`. Establish `h' : ccT a * ccT b = 1` using `by rw [← Base.ccT_mul, h, Base.ccT_one]`. Express the relevant statement in the definitionally equal form `ccT _ * _ * _ = _`. Rewrite using `[e]`.

Simplify using `[Matrix.J, Matrix.fromBlocks_multiply, h, h']`.
-/
theorem levi_mem {a b : Matrix (Fin N) (Fin N) E} (h : b * a = 1) :
    (Matrix.fromBlocks a 0 0 (ccT b) : M2 E N) ∈ UU E N := by
  have e : ccT (Matrix.fromBlocks a 0 0 (ccT b) : M2 E N) = Matrix.fromBlocks (ccT a) 0 0 b := by
    ext (i | i) (j | j) <;> simp [ccT, cc]
  have h' : ccT a * ccT b = 1 := by rw [← Base.ccT_mul, h, Base.ccT_one]
  change ccT _ * _ * _ = _
  rw [e]
  simp [Matrix.J, Matrix.fromBlocks_multiply, h, h']

/- English proof (translation)
Establish `h1 : b.map τ.1 * a.map τ.1 = 1`. Rewrite using `[← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `h2 : ((b.map τ.1)ᴴ)⁻¹ = (a.map τ.1)ᴴ`. Use `Matrix.inv_eq_left_inv ?_` and prove the remaining obligations. Rewrite using `[← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]`.

Simplify using `[hAct, hDen, Base.ccT_map, h2]`.
-/
theorem hAct_levi (Ψ : Finset (E →+* ℂ)) {a b : Matrix (Fin N) (Fin N) E} (h : b * a = 1)
    (Z : CM Ψ N N) (τ : Ψ) :
    hAct Ψ (Matrix.fromBlocks a 0 0 (ccT b)) Z τ = a.map τ.1 * Z τ * (a.map τ.1)ᴴ := by
  have h1 : b.map τ.1 * a.map τ.1 = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : ((b.map τ.1)ᴴ)⁻¹ = (a.map τ.1)ᴴ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  simp [hAct, hDen, Base.ccT_map, h2]

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Unfold `pushZ`. Rewrite using `[hAct_levi Ψ h, hAct_levi Ψ h, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]`. Use `congr 3`. Use function extensionality and compare the values at `i`.

Simplify using `[Matrix.mulVec, dotProduct]`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]`.
-/
theorem hAct_pushZ (Ψ : Finset (E →+* ℂ)) {a b : Matrix (Fin N) (Fin N) E} (h : b * a = 1)
    (Z : CM Ψ N N) (v : Fin N → E) (t : ℝ) :
    hAct Ψ (Matrix.fromBlocks a 0 0 (ccT b)) (pushZ Ψ Z v t) =
      pushZ Ψ (hAct Ψ (Matrix.fromBlocks a 0 0 (ccT b)) Z) (a *ᵥ v) t := by
  funext τ
  unfold pushZ
  rw [hAct_levi Ψ h, hAct_levi Ψ h, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  congr 3
  · funext i; simp [Matrix.mulVec, dotProduct]
  · funext i; simp [Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]

/- English proof (translation)
Simplify using `[hFac, hDen]`.
-/
theorem hFac_levi (Ψ : Finset (E →+* ℂ)) (a b : Matrix (Fin N) (Fin N) E) (Z : CM Ψ N N) :
    hFac Ψ (Matrix.fromBlocks a 0 0 (ccT b)) Z (0 : CM Ψ n N) 0 =
      ∏ τ : Ψ, ((ccT b).map τ.1).det ^ n := by
  simp [hFac, hDen]

omit [IsCMField E] in

/- English proof (translation)
Unfold `ColsIn`. Rewrite using `[Fin.forall_fin_succ]`. Establish `: (c • (Matrix.of fun k => Fin.cons 0 (x k) : Matrix (Fin n) (Fin (N + 1)) E))ᵀ 0 = 0`. Use extensionality with `k`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `⟨fun h => h.2, fun h => ⟨Λ.zero_mem, h⟩⟩`.
-/
theorem colsIn_cons (Λ : Lt E n) (c : E) (x : Matrix (Fin n) (Fin N) E) :
    ColsIn Λ (c • (Matrix.of fun k => Fin.cons 0 (x k) : Matrix (Fin n) (Fin (N + 1)) E)) ↔
      ColsIn Λ (c • x) := by
  unfold ColsIn
  rw [Fin.forall_fin_succ]
  have : (c • (Matrix.of fun k => Fin.cons 0 (x k) : Matrix (Fin n) (Fin (N + 1)) E))ᵀ 0 = 0 := by
    ext k; simp
  rw [this]
  exact ⟨fun h => h.2, fun h => ⟨Λ.zero_mem, h⟩⟩

/- English proof (translation)
Use `⟨hφ.pos, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h hh Λ hΛ Λ' hΛ' m x`. Unfold `dropF`. Rewrite using `[← hφ.equiv h hh Λ hΛ Λ' hΛ' m]`. Use `congr 1`.

Use extensionality with `k j`. Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) j <;> simp [Matrix.mul_apply]`. Introduce `Λ hΛ x hx`. Conclude with `(colsIn_cons Λ _ x).1 (hφ.supp Λ hΛ _ hx)`. Introduce `Λ hΛ x y hy`.

Establish `hy'` using `(colsIn_cons Λ 1 y).2 (by rwa [one_smul])`. Rewrite `hy'` using `[one_smul]`. Unfold `dropF`. Rewrite using `[← hφ.per Λ hΛ (Matrix.of fun k => Fin.cons 0 (x k)) _ hy']`. Use `congr 1`.

Use extensionality with `k j`. Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) j <;> simp`. Introduce `Λ hΛ Λ' hΛ' ha x hx hx'`. Conclude with `hφ.loc Λ hΛ Λ' hΛ' ha _ ((colsIn_cons Λ _ x).2 hx) ((colsIn_cons Λ' _ x).2 hx')`.
-/
theorem admissibleLatticeFamily_restrictFirstColumnZero {M R : ℕ} {φ : Fam E n (N + 1)} (hφ : admitted M R φ) :
    admitted M R (fun Λ => dropF (φ Λ)) := by
  refine ⟨hφ.pos, ?_, ?_, ?_, ?_⟩
  · intro h hh Λ hΛ Λ' hΛ' m x
    unfold dropF
    rw [← hφ.equiv h hh Λ hΛ Λ' hΛ' m]
    congr 1
    ext k j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [Matrix.mul_apply]
  · intro Λ hΛ x hx
    exact (colsIn_cons Λ _ x).1 (hφ.supp Λ hΛ _ hx)
  · intro Λ hΛ x y hy
    have hy' := (colsIn_cons Λ 1 y).2 (by rwa [one_smul])
    rw [one_smul] at hy'
    unfold dropF
    rw [← hφ.per Λ hΛ (Matrix.of fun k => Fin.cons 0 (x k)) _ hy']
    congr 1
    ext k j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp
  · intro Λ hΛ Λ' hΛ' ha x hx hx'
    exact hφ.loc Λ hΛ Λ' hΛ' ha _ ((colsIn_cons Λ _ x).2 hx) ((colsIn_cons Λ' _ x).2 hx')

/- English proof (translation)
Introduce `Λ hΛ`. Take `⟨c, hc, hd⟩` from `exists_den (1 : M2 E N)`. Take `⟨_, _, -, h⟩` from `GlobalTheory.T.weil_action_level_supNorm_uniform_in_lattice E Ψ hΨ n N hn c R hc hφ.pos.2`. Conclude with `(h M Λ hΛ 1 Base.one_mem_UU hd (φ Λ) ⟨hφ.supp Λ hΛ, hφ.per Λ hΛ⟩).1`.
-/
theorem isSB_of_adm {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (hn : Even n) {M R : ℕ}
    {φ : Fam E n N} (hφ : admitted M R φ) : ∀ Λ ∈ Vset E n M, IsSB (φ Λ) := by
  intro Λ hΛ
  obtain ⟨c, hc, hd⟩ := exists_den (1 : M2 E N)
  obtain ⟨_, _, -, h⟩ := GlobalTheory.T.weil_action_level_supNorm_uniform_in_lattice E Ψ hΨ n N hn c R hc hφ.pos.2
  exact (h M Λ hΛ 1 Base.one_mem_UU hd (φ Λ) ⟨hφ.supp Λ hΛ, hφ.per Λ hΛ⟩).1

/- English proof (translation)
Establish `hsb` using `isSB_of_adm hΨ hn hφ`. Use `haveI : Finite (Cls E n M) := (finite_cls_and_stab E n M hφ.pos.1).1`. Use `letI : Fintype (Cls E n M) := Fintype.ofFinite _`. Establish `hZ' : dropZ Ψ Z ∈ Hn Ψ N` using `((GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N 0 isSB_zero).2 Z hZ).1`. Rewrite using `[← hsw M R _ (admissibleLatticeFamily_restrictFirstColumnZero hφ) _ hZ']`.

Unfold `swd classSum`. Simplify using `only [finsum_eq_sum_of_fintype]`. Use `tendsto_finset_sum _ fun c _ => Tendsto.const_mul _ (Tendsto.sub ?_ ?_)` and prove the remaining obligations. Conclude with `((GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N _ (hsb _ (Quot.out c).2)).2 Z hZ).2.2 0 0`. Conclude with `GlobalTheory.T.siegelOperator_hermitianEisensteinSeries E Ψ hΨ n N hn hN _ (hsb _ (Quot.out c).2) Z hZ`.
-/
theorem tendsto_first {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (hn : Even n)
    (hN : 4 * (N + 1) < n) (hsw : SWAt Ψ n N) {M R : ℕ} {φ : Fam E n (N + 1)} (hφ : admitted M R φ)
    {Z : CM Ψ (N + 1) (N + 1)} (hZ : Z ∈ Hn Ψ (N + 1)) :
    Tendsto (fun t : ℝ => swd Ψ M φ (pushZ Ψ Z (Pi.single 0 1) t) 0 0) atTop (𝓝 0) := by
  have hsb := isSB_of_adm hΨ hn hφ
  haveI : Finite (Cls E n M) := (finite_cls_and_stab E n M hφ.pos.1).1
  letI : Fintype (Cls E n M) := Fintype.ofFinite _
  have hZ' : dropZ Ψ Z ∈ Hn Ψ N := ((GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N 0 isSB_zero).2 Z hZ).1
  rw [← hsw M R _ (admissibleLatticeFamily_restrictFirstColumnZero hφ) _ hZ']
  unfold swd classSum
  simp only [finsum_eq_sum_of_fintype]
  refine tendsto_finset_sum _ fun c _ => Tendsto.const_mul _ (Tendsto.sub ?_ ?_)
  · exact ((GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N _ (hsb _ (Quot.out c).2)).2 Z hZ).2.2 0 0
  · exact GlobalTheory.T.siegelOperator_hermitianEisensteinSeries E Ψ hΨ n N hn hN _ (hsb _ (Quot.out c).2) Z hZ

end GlobalTheory.SW.Cusp

open GlobalTheory.SW.Cusp in

/- English proof (translation)
Introduce `E _ _ _ Ψ hΨ n N hn hN hsw M R φ hφ v hv Z hZ`. Take `⟨a, b, hba, hav⟩` from `exists_inv v hv`. Establish `hγ` using `levi_mem hba`. Take `⟨c, hc, hd⟩` from `exists_den (Matrix.fromBlocks a 0 0 (ccT b) : M2 E (N + 1))`. Take `⟨R', hR'⟩` from `GlobalTheory.T.admissibleLatticeFamily_hermitianWeilAction E Ψ hΨ n (N + 1) hn c R hc`.

Establish `hact` using `(unitary_act_halfSpace E Ψ (N + 1) _ hγ).2 Z hZ`. Establish `hlim` using `tendsto_first hΨ hn hN hsw (hR' M φ hφ _ hγ hd) hact.2.1`. Establish `hne : (∏ τ : Ψ, ((ccT b).map τ.1).det ^ n) ≠ 0`. Use `Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ ?_` and prove the remaining obligations. Simplify `(hact.1 τ).1` using `[hDen]`.

Establish `h2` using `hlim.const_mul (∏ τ : Ψ, ((ccT b).map τ.1).det ^ n)⁻¹`. Rewrite `h2` using `[mul_zero]`. Use `h2.congr' ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht`. Establish `h3` using `(GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n (N + 1) hn hN M φ hφ.pos.1 (isSB_of_adm hΨ hn hφ) _ (pushZ_mem Ψ hZ v ht)).1 _ hγ`.

Rewrite `h3` using `[hAct_pushZ Ψ hba, hav, hFac_levi]`. Rewrite using `[h3, inv_mul_cancel_left₀ hne]`.
-/
theorem GlobalTheory.SW.swd_tendsto_zero_at_cusps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N → ∀ (M R : ℕ) (φ : Fam E n (N + 1)), admitted M R φ → ∀ v : Fin (N + 1) → E, v ≠ 0 → ∀ Z ∈ Hn Ψ (N + 1), Tendsto (fun t : ℝ => swd Ψ M φ (pushZ Ψ Z v t) 0 0) atTop (𝓝 0) := by
  intro E _ _ _ Ψ hΨ n N hn hN hsw M R φ hφ v hv Z hZ
  obtain ⟨a, b, hba, hav⟩ := exists_inv v hv
  have hγ := levi_mem hba
  obtain ⟨c, hc, hd⟩ := exists_den (Matrix.fromBlocks a 0 0 (ccT b) : M2 E (N + 1))
  obtain ⟨R', hR'⟩ := GlobalTheory.T.admissibleLatticeFamily_hermitianWeilAction E Ψ hΨ n (N + 1) hn c R hc
  have hact := (unitary_act_halfSpace E Ψ (N + 1) _ hγ).2 Z hZ
  have hlim := tendsto_first hΨ hn hN hsw (hR' M φ hφ _ hγ hd) hact.2.1
  have hne : (∏ τ : Ψ, ((ccT b).map τ.1).det ^ n) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ ?_
    simpa [hDen] using (hact.1 τ).1
  have h2 := hlim.const_mul (∏ τ : Ψ, ((ccT b).map τ.1).det ^ n)⁻¹
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have h3 := (GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n (N + 1) hn hN M φ hφ.pos.1 (isSB_of_adm hΨ hn hφ) _
    (pushZ_mem Ψ hZ v ht)).1 _ hγ
  rw [hAct_pushZ Ψ hba, hav, hFac_levi] at h3
  rw [h3, inv_mul_cancel_left₀ hne]
