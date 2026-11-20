import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtDataPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.DimStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormFundamentalDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.HfRsmulRight
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointwiseNormSqPullbackTensorEqProd
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBasisSpanEqOfCommensurable
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TorusAtEpsIndep

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.ThetaRho

open MeasureTheory
open scoped ComplexConjugate

section Torus

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Take `⟨hfin, hle⟩` from `dim (Idx T.dim) (gtOf T 1) 1 le_rfl`. Rewrite `hle` using `[one_pow]`. Establish `hcol : ∀ w : Fin 1 → Vsp T.dim, w = fun _ => w 0` using `fun w =>`. Use function extensionality and compare the values at `fun j => by rw [Subsingleton.elim j 0]`. Set `S : (gtOf T 1).Sec 1` to `⟨_, ThetaBound.col_mem_Sec T hs⟩`.

Set `S' : (gtOf T 1).Sec 1` to `⟨_, ThetaBound.col_mem_Sec T ht⟩`. Establish `hS : S ≠ 0`. Introduce `h`. Apply `hs0` to reduce the goal to its premises. Use function extensionality and compare the values at `w`.

Rewrite using `[hcol w]`. Conclude with `congrFun (congrArg Subtype.val h) (w 0)`. Take `⟨g, hg⟩` from `(finrank_le_one_iff).1 hle`. Take `⟨a, ha⟩` from `hg S`. Take `⟨a', ha'⟩` from `hg S'`.

Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Conclude with `hS (by rw [← ha, zero_smul])`. Establish `h : S' = (a' * a⁻¹) • S`. Rewrite using `[← ha, ← ha', smul_smul, mul_assoc, inv_mul_cancel₀ ha0, mul_one]`.

Use `⟨a' * a⁻¹, funext fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[hcol w]`. Conclude with `congrFun (congrArg Subtype.val h) (w 0)`.
-/
theorem exists_eq_smul (T : PT E) {s t : (Fin 1 → Vsp T.dim) → ℂ} (hs : s ∈ T.Sec 1 1)
    (ht : t ∈ T.Sec 1 1) (hs0 : s ≠ 0) : ∃ c : ℂ, t = c • s := by
  obtain ⟨hfin, hle⟩ := dim (Idx T.dim) (gtOf T 1) 1 le_rfl
  rw [one_pow] at hle
  have hcol : ∀ w : Fin 1 → Vsp T.dim, w = fun _ => w 0 := fun w =>
    funext fun j => by rw [Subsingleton.elim j 0]
  let S : (gtOf T 1).Sec 1 := ⟨_, ThetaBound.col_mem_Sec T hs⟩
  let S' : (gtOf T 1).Sec 1 := ⟨_, ThetaBound.col_mem_Sec T ht⟩
  have hS : S ≠ 0 := by
    intro h
    apply hs0
    funext w
    rw [hcol w]
    exact congrFun (congrArg Subtype.val h) (w 0)
  obtain ⟨g, hg⟩ := (finrank_le_one_iff).1 hle
  obtain ⟨a, ha⟩ := hg S
  obtain ⟨a', ha'⟩ := hg S'
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hS (by rw [← ha, zero_smul])
  have h : S' = (a' * a⁻¹) • S := by
    rw [← ha, ← ha', smul_smul, mul_assoc, inv_mul_cancel₀ ha0, mul_one]
  refine ⟨a' * a⁻¹, funext fun w => ?_⟩
  rw [hcol w]
  exact congrFun (congrArg Subtype.val h) (w 0)

variable (T T' : PT E) (U : Vsp T.dim ≃ₗᵢ[ℂ] Vsp T'.dim)

/- English proof (translation)
Rewrite using `[ChA.Hf_eq_inner, ChA.Hf_eq_inner, U.inner_map_map]`.
-/
theorem hf_map (v w : Vsp T.dim) : Hf (U v) (U w) = Hf v w := by
  rw [ChA.Hf_eq_inner, ChA.Hf_eq_inner, U.inner_map_map]

/- English proof (translation)
Simplify using `only [PT.ptN2, HC, hf_map]`.
-/
theorem pointwiseNormSq_comp_isometry (s : (Fin 1 → Vsp T'.dim) → ℂ) (y : Vsp T.dim) :
    T.ptN2 1 (fun w => s fun k => U (w k)) (fun _ => y) = T'.ptN2 1 s fun _ => U y := by
  simp only [PT.ptN2, HC, hf_map]

/- English proof (translation)
Use `⟨hs.1.comp (differentiable_pi.2 fun k => U.toContinuousLinearEquiv.differentiable.comp (differentiable_apply k)), fun γ hγ v => ?_⟩` and prove the remaining obligations. Establish `h` using `hs.2 (fun k => U (γ k)) (fun k => (hL _).1 (hγ k)) (fun k => U (v k))`. Establish `e : (fun k => U ((v + γ) k)) = (fun k => U (v k)) + fun k => U (γ k)`. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules.

Simplify using `only [e]`. Rewrite using `[h]`. Simplify using `only [HC, hf_map, he _ (hγ _)]`.
-/
theorem comp_mem_Sec (hL : ∀ y, y ∈ T.L ↔ U y ∈ T'.L)
    (he : ∀ y ∈ T.L, T'.eps (U y) = T.eps y) {s : (Fin 1 → Vsp T'.dim) → ℂ}
    (hs : s ∈ T'.Sec 1 1) : (fun w => s fun k => U (w k)) ∈ T.Sec 1 1 := by
  refine ⟨hs.1.comp (differentiable_pi.2 fun k =>
    U.toContinuousLinearEquiv.differentiable.comp (differentiable_apply k)), fun γ hγ v => ?_⟩
  have h := hs.2 (fun k => U (γ k)) (fun k => (hL _).1 (hγ k)) (fun k => U (v k))
  have e : (fun k => U ((v + γ) k)) = (fun k => U (v k)) + fun k => U (γ k) := by
    funext k; simp
  simp only [e]
  rw [h]
  simp only [HC, hf_map, he _ (hγ _)]

/- English proof (translation)
Establish `hF` using `comp_mem_Sec T T' U hL he hs`. Set `e : Vsp T.dim ≃L[ℝ] Vsp T'.dim` to `(U.toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv`. Establish `hev : ∀ v, e v = U v` using `fun _ => rfl`. Set `b'` to `T'.b.map e.symm.toLinearEquiv`. Establish `hrepr : ∀ v i, b'.repr v i = T'.b.repr (U v) i` using `fun v i => by`.

Simplify using `only [b', Module.Basis.map_repr]`. Both sides reduce to the same expression. Establish `hfd : e ⁻¹' ZSpan.fundamentalDomain T'.b = ZSpan.fundamentalDomain b'`. Use extensionality with `v`. Simplify using `only [Set.mem_preimage, ZSpan.mem_fundamentalDomain, hrepr, hev]`.

Establish `hle : Submodule.span ℤ (Set.range b') ≤ Submodule.span ℤ (Set.range T.b)`. Introduce `v hv`. Use `(hL v).2 ?_` and prove the remaining obligations. Rewrite `hv`, the goal using `[Module.Basis.mem_span_iff_repr_mem]`. Simplify `hv` using `only [hrepr]`.

Establish `h` using `average_fundamentalDomain_eq_real volume T.b b' (fun y => T.ptN2 1 (fun w => s fun k => U (w k)) (fun _ => y)) ((TiledBoundaries.continuous_pointNormSq_quotient T 1 hF.1.continuous).comp (continuous_pi fun _ => continuous_id)) (fun γ hγ v => pointwiseNormSq_add_period T hF (γ := …`. Rewrite using `[l2_norm_fundamental_domain, l2_norm_fundamental_domain, TensorLat.setAverage_comp_equiv volume volume e, hfd, ← h]`. Simplify using `only [hev, pointwiseNormSq_comp_isometry, add_zero]`.
-/
theorem l2_comp_eq_of_preserves_lattice_eps (hL : ∀ y, y ∈ T.L ↔ U y ∈ T'.L)
    (he : ∀ y ∈ T.L, T'.eps (U y) = T.eps y) {s : (Fin 1 → Vsp T'.dim) → ℂ}
    (hs : s ∈ T'.Sec 1 1) : T.l2 1 (fun w => s fun k => U (w k)) = T'.l2 1 s := by
  have hF := comp_mem_Sec T T' U hL he hs
  let e : Vsp T.dim ≃L[ℝ] Vsp T'.dim :=
    (U.toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv
  have hev : ∀ v, e v = U v := fun _ => rfl
  let b' := T'.b.map e.symm.toLinearEquiv
  have hrepr : ∀ v i, b'.repr v i = T'.b.repr (U v) i := fun v i => by
    simp only [b', Module.Basis.map_repr]
    rfl
  have hfd : e ⁻¹' ZSpan.fundamentalDomain T'.b = ZSpan.fundamentalDomain b' := by
    ext v
    simp only [Set.mem_preimage, ZSpan.mem_fundamentalDomain, hrepr, hev]
  have hle : Submodule.span ℤ (Set.range b') ≤ Submodule.span ℤ (Set.range T.b) := by
    intro v hv
    refine (hL v).2 ?_
    rw [Module.Basis.mem_span_iff_repr_mem] at hv ⊢
    simpa only [hrepr] using hv
  have h := average_fundamentalDomain_eq_real volume T.b b'
    (fun y => T.ptN2 1 (fun w => s fun k => U (w k)) (fun _ => y))
    ((TiledBoundaries.continuous_pointNormSq_quotient T 1 hF.1.continuous).comp (continuous_pi fun _ => continuous_id))
    (fun γ hγ v => pointwiseNormSq_add_period T hF (γ := fun _ => γ) (fun _ => hγ) (fun _ => v)) hle 0
  rw [l2_norm_fundamental_domain, l2_norm_fundamental_domain, TensorLat.setAverage_comp_equiv volume volume e, hfd, ← h]
  simp only [hev, pointwiseNormSq_comp_isometry, add_zero]

/- English proof (translation)
Take `⟨c, hc⟩` from `exists_eq_smul T hs (comp_mem_Sec T T' U hL he hs') hs0`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Apply `hs0'` to reduce the goal to its premises. Use function extensionality and compare the values at `w`.

Use `congrFun hc fun k => U.symm (w k)` as an intermediate fact. Simplify using `using this`. Rewrite using `[← pointwiseNormSq_comp_isometry, ← l2_comp_eq_of_preserves_lattice_eps T T' U hL he hs', hc, l2_smul]`. Establish `: T.ptN2 1 (c • s) (fun _ => y) = ‖c‖ ^ 2 * T.ptN2 1 s (fun _ => y)`. Simplify using `only [PT.ptN2, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, mul_assoc]`.

Rewrite using `[this, mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.2 hc0))]`.
-/
theorem ratio_eq (hL : ∀ y, y ∈ T.L ↔ U y ∈ T'.L)
    (he : ∀ y ∈ T.L, T'.eps (U y) = T.eps y) {s : (Fin 1 → Vsp T.dim) → ℂ}
    {s' : (Fin 1 → Vsp T'.dim) → ℂ} (hs : s ∈ T.Sec 1 1) (hs0 : s ≠ 0)
    (hs' : s' ∈ T'.Sec 1 1) (hs0' : s' ≠ 0) (y : Vsp T.dim) :
    T'.ptN2 1 s' (fun _ => U y) / T'.l2 1 s' = T.ptN2 1 s (fun _ => y) / T.l2 1 s := by
  obtain ⟨c, hc⟩ := exists_eq_smul T hs (comp_mem_Sec T T' U hL he hs') hs0
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hs0'
    funext w
    have := congrFun hc fun k => U.symm (w k)
    simpa using this
  rw [← pointwiseNormSq_comp_isometry, ← l2_comp_eq_of_preserves_lattice_eps T T' U hL he hs', hc, l2_smul]
  have : T.ptN2 1 (c • s) (fun _ => y) = ‖c‖ ^ 2 * T.ptN2 1 s (fun _ => y) := by
    simp only [PT.ptN2, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, mul_assoc]
  rw [this, mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.2 hc0))]

end Torus

/- English proof (translation)
Establish `hw0 : ∀ i, w i ≠ 0` using `fun i h => by simpa [h] using hw i`. Use `⟨{ toFun := fun y => WithLp.toLp 2 fun i => w i * y (ε i) invFun := fun z => WithLp.toLp 2 fun j => (w (ε.symm j))⁻¹ * z (ε.symm j) map_add' := fun y z => ?_ map_smul' := fun c y => ?_ left_inv := fun y => ?_ right_inv := fun z => ?_ norm_map' := fun y => ?_ }, fun y i => rfl⟩` and prove the remaining obligations. Use extensionality with `i`. Simplify using `[mul_add]`. Use extensionality with `i`.

Simplify using `[mul_left_comm]`. Use extensionality with `j`. Simplify using `[hw0]`. Use extensionality with `i`. Simplify using `[hw0]`.

Rewrite using `[EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← ε.sum_comp]`. Simplify using `[hw]`.
-/
theorem exists_diag_isometry {ι ι' : Type} [Fintype ι] [Fintype ι'] (ε : ι' ≃ ι) (w : ι' → ℂ)
    (hw : ∀ i, ‖w i‖ = 1) :
    ∃ U : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι', ∀ y i, U y i = w i * y (ε i) := by
  have hw0 : ∀ i, w i ≠ 0 := fun i h => by simpa [h] using hw i
  refine ⟨{ toFun := fun y => WithLp.toLp 2 fun i => w i * y (ε i)
            invFun := fun z => WithLp.toLp 2 fun j => (w (ε.symm j))⁻¹ * z (ε.symm j)
            map_add' := fun y z => ?_
            map_smul' := fun c y => ?_
            left_inv := fun y => ?_
            right_inv := fun z => ?_
            norm_map' := fun y => ?_ }, fun y i => rfl⟩
  · ext i; simp [mul_add]
  · ext i; simp [mul_left_comm]
  · ext j; simp [hw0]
  · ext i; simp [hw0]
  · rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← ε.sum_comp]
    simp [hw]

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Establish `hx : ∀ (P : Matrix (Fin r) (Fin r) E) (u : Fin r → ℂ), (P.map τ).mulVec u = ∑ k, u k • Data.emb τ (P.mulVec (Pi.single k 1))`. Introduce `P u`. Use function extensionality and compare the values at `j`. Simplify using `[Data.emb, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm, apply_ite τ]`. Establish `hexp : ∀ P : Matrix (Fin r) (Fin r) E, hermC τ G ((P.map τ).mulVec u) ((P.map τ).mulVec w) = ∑ k, ∑ l, u k * (conj (w l) * τ (herm G (P.mulVec (Pi.single k 1)) (P.mulVec (Pi.single l 1))))`.

Introduce `P`. Rewrite using `[hx, hx, hermC_sum_left]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hermC_smul_left, hermC_sum_right, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[hermC_smul_right, hermC_emb]`. Establish `h1 : ((1 : Matrix (Fin r) (Fin r) E).map τ) = 1` using `Matrix.map_one τ τ.map_zero τ.map_one`. Use `conv_rhs => rw [← Matrix.one_mulVec u, ← Matrix.one_mulVec w, ← h1]`. Rewrite using `[hexp, hexp]`. Simplify using `only [hγ, Matrix.one_mulVec]`.
-/
theorem hermC_map_mulVec (G : Matrix (Fin r) (Fin r) E) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ x y, herm G (γ.mulVec x) (γ.mulVec y) = herm G x y) (τ : E →+* ℂ) (u w : Fin r → ℂ) :
    hermC τ G ((γ.map τ).mulVec u) ((γ.map τ).mulVec w) = hermC τ G u w := by
  have hx : ∀ (P : Matrix (Fin r) (Fin r) E) (u : Fin r → ℂ), (P.map τ).mulVec u =
      ∑ k, u k • Data.emb τ (P.mulVec (Pi.single k 1)) := by
    intro P u
    funext j
    simp [Data.emb, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm, apply_ite τ]
  have hexp : ∀ P : Matrix (Fin r) (Fin r) E,
      hermC τ G ((P.map τ).mulVec u) ((P.map τ).mulVec w) = ∑ k, ∑ l, u k * (conj (w l) *
        τ (herm G (P.mulVec (Pi.single k 1)) (P.mulVec (Pi.single l 1)))) := by
    intro P
    rw [hx, hx, hermC_sum_left]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hermC_smul_left, hermC_sum_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hermC_smul_right, hermC_emb]
  have h1 : ((1 : Matrix (Fin r) (Fin r) E).map τ) = 1 := Matrix.map_one τ τ.map_zero τ.map_one
  conv_rhs => rw [← Matrix.one_mulVec u, ← Matrix.one_mulVec w, ← h1]
  rw [hexp, hexp]
  simp only [hγ, Matrix.one_mulVec]

/- English proof (translation)
Take `⟨β, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).mp hy`. Rewrite using `[hermC_sum_left]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Rewrite using `[hermC_smul_left, he, if_neg, mul_zero]`. Introduce `h`.

Establish `h1` using `congrArg Fin.val h`. Establish `h2` using `a.2`. Simplify using `only [Fin.val_castLE] at h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem hermC_eq_zero_of_mem_span (X : Data E r) (τ : X.Ψ) (e : Fin r → Fin r → ℂ)
    (he : ∀ a b, hermC τ.1 X.Gm (e a) (e b) = if a = b then ((sgn X.p0 a : ℝ) : ℂ) else 0)
    {i : ℕ} (hi : i ≤ r) {y : Fin r → ℂ}
    (hy : y ∈ Submodule.span ℂ (Set.range fun a : Fin i => e (Fin.castLE hi a)))
    (c : Fin r) (hc : i ≤ c) : hermC τ.1 X.Gm y (e c) = 0 := by
  obtain ⟨β, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hy
  rw [hermC_sum_left]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [hermC_smul_left, he, if_neg, mul_zero]
  intro h
  have h1 := congrArg Fin.val h
  have h2 := a.2
  simp only [Fin.val_castLE] at h1
  omega

/- English proof (translation)
Establish `heq : ∀ (i : ℕ) (hi : i ≤ r), Submodule.span ℂ (Set.range fun a : Fin i => e' (Fin.castLE hi a)) = Submodule.span ℂ (Set.range fun a : Fin i => e (Fin.castLE hi a))`. Introduce `i hi`. Use `Submodule.eq_of_le_of_finrank_eq (hfl i hi) ?_` and prove the remaining obligations. Establish `h1` using `finrank_span_eq_card ((TorusAtDataPf.e_linInd X τ e he).comp _ (Fin.castLE_injective hi))`. Establish `h2` using `finrank_span_eq_card ((TorusAtDataPf.e_linInd X τ e' he').comp _ (Fin.castLE_injective hi))`.

Conclude with `h2.trans h1.symm`. Establish `h0 : ∀ c, c ≠ a → hermC τ.1 X.Gm (e' a) (e c) = 0`. Introduce `c hc`. Break down `lt_or_gt_of_ne hc with h | h` into its components or cases. Establish `hm : e c ∈ Submodule.span ℂ (Set.range fun k : Fin (c + 1) => e' (Fin.castLE c.2 k))`.

Rewrite using `[heq]`. Conclude with `Submodule.subset_span ⟨Fin.last c, rfl⟩`. Use `hermC_eq_zero_of_mem_span X τ e' he' _ hm a h` as an intermediate fact. Rewrite using `[← hermC_conj τ.1 X.Gm_herm, this, map_zero]`. Conclude with `hermC_eq_zero_of_mem_span X τ e he a.2 (hfl _ _ (Submodule.subset_span ⟨Fin.last a, rfl⟩)) c h`.

Establish `h1 : e' a = (((sgn X.p0 a : ℝ) : ℂ) * hermC τ.1 X.Gm (e' a) (e a)) • e a` using `by conv_lhs => rw [TorusAtDataPf.expand X τ e he (e' a)]`. Use `Finset.sum_eq_single a (fun c _ hc => ?_) (by simp)` and prove the remaining obligations. Rewrite using `[h0 c hc, mul_zero, zero_smul]`. Use `⟨_, ?_, h1⟩` and prove the remaining obligations. Generalize the expression as in `((sgn X.p0 a : ℝ) : ℂ) * hermC τ.1 X.Gm (e' a) (e a) = u at h1`.

Establish `h2` using `he' a a`. Rewrite `h2` using `[h1, hermC_smul_left, hermC_smul_right, he, if_pos rfl]`. Establish `h3 : u * conj u = 1`. Use `TorusAtDataPf.sgn_sq X a` as an intermediate fact. Take the linear combination `((sgn X.p0 a : ℝ) : ℂ) * h2 + (1 - u * conj u) * this`.

Rewrite `h3` using `[Complex.mul_conj']`. Establish `h4 : ‖u‖ ^ 2 = 1` using `by exact_mod_cast h3`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg u) two_ne_zero).1 h4`.
-/
theorem exists_unit_of_flag (X : Data E r) (τ : X.Ψ) (e e' : Fin r → Fin r → ℂ)
    (he : ∀ a b, hermC τ.1 X.Gm (e a) (e b) = if a = b then ((sgn X.p0 a : ℝ) : ℂ) else 0)
    (he' : ∀ a b, hermC τ.1 X.Gm (e' a) (e' b) = if a = b then ((sgn X.p0 a : ℝ) : ℂ) else 0)
    (hfl : ∀ (i : ℕ) (hi : i ≤ r),
      Submodule.span ℂ (Set.range fun a : Fin i => e' (Fin.castLE hi a)) ≤
        Submodule.span ℂ (Set.range fun a : Fin i => e (Fin.castLE hi a))) (a : Fin r) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ e' a = u • e a := by
  have heq : ∀ (i : ℕ) (hi : i ≤ r),
      Submodule.span ℂ (Set.range fun a : Fin i => e' (Fin.castLE hi a)) =
        Submodule.span ℂ (Set.range fun a : Fin i => e (Fin.castLE hi a)) := by
    intro i hi
    refine Submodule.eq_of_le_of_finrank_eq (hfl i hi) ?_
    have h1 := finrank_span_eq_card
      ((TorusAtDataPf.e_linInd X τ e he).comp _ (Fin.castLE_injective hi))
    have h2 := finrank_span_eq_card
      ((TorusAtDataPf.e_linInd X τ e' he').comp _ (Fin.castLE_injective hi))
    exact h2.trans h1.symm
  have h0 : ∀ c, c ≠ a → hermC τ.1 X.Gm (e' a) (e c) = 0 := by
    intro c hc
    rcases lt_or_gt_of_ne hc with h | h
    · have hm : e c ∈ Submodule.span ℂ
          (Set.range fun k : Fin (c + 1) => e' (Fin.castLE c.2 k)) := by
        rw [heq]
        exact Submodule.subset_span ⟨Fin.last c, rfl⟩
      have := hermC_eq_zero_of_mem_span X τ e' he' _ hm a h
      rw [← hermC_conj τ.1 X.Gm_herm, this, map_zero]
    · exact hermC_eq_zero_of_mem_span X τ e he a.2
        (hfl _ _ (Submodule.subset_span ⟨Fin.last a, rfl⟩)) c h
  have h1 : e' a = (((sgn X.p0 a : ℝ) : ℂ) * hermC τ.1 X.Gm (e' a) (e a)) • e a := by
    conv_lhs => rw [TorusAtDataPf.expand X τ e he (e' a)]
    refine Finset.sum_eq_single a (fun c _ hc => ?_) (by simp)
    rw [h0 c hc, mul_zero, zero_smul]
  refine ⟨_, ?_, h1⟩
  generalize ((sgn X.p0 a : ℝ) : ℂ) * hermC τ.1 X.Gm (e' a) (e a) = u at h1
  have h2 := he' a a
  rw [h1, hermC_smul_left, hermC_smul_right, he, if_pos rfl] at h2
  have h3 : u * conj u = 1 := by
    have := TorusAtDataPf.sgn_sq X a
    linear_combination ((sgn X.p0 a : ℝ) : ℂ) * h2 + (1 - u * conj u) * this
  rw [Complex.mul_conj'] at h3
  have h4 : ‖u‖ ^ 2 = 1 := by exact_mod_cast h3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg u) two_ne_zero).1 h4

/- English proof (translation)
Use `set g := (γ : Matrix (Fin r) (Fin r) E).map τ.1 with hg`. Establish `hst : ∀ u w, hermC τ.1 X.Gm (g.mulVec u) (g.mulVec w) = hermC τ.1 X.Gm u w` using `hermC_map_mulVec X.Gm hγ.1 τ.1`. Take `⟨u, hu, h⟩` from `exists_unit_of_flag X τ (fun a => g.mulVec (A.e τ a)) (A'.e τ) (fun a b => by rw [hst, A.e_orth]) (A'.e_orth τ) (fun i hi => by`. Rewrite using `[A'.e_flag τ i hi]`. Establish `hmap : Submodule.span ℂ (Set.range fun a : Fin i => g.mulVec (A.e τ (Fin.castLE hi a))) = (Submodule.span ℂ (Set.range fun a : Fin i => A.e τ (Fin.castLE hi a))).map g.mulVecLin`.

Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[hmap, A.e_flag τ i hi, Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Use `⟨∑ c, b τ c (Fin.castLE hi k) • col (mat x τ) c, ?_, ?_⟩` and prove the remaining obligations.

Use `Submodule.sum_mem _ fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : (c : ℕ) < i`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨c, hc⟩, rfl⟩)`. Rewrite using `[(hb τ).2 c (Fin.castLE hi k) (by`. Use `k.2` as an intermediate fact.

Rewrite using `[Fin.lt_def]`. Simplify using `only [Fin.val_castLE]`. Use the proof step `omega), zero_smul]`. Conclude with `Submodule.zero_mem _`. Use function extensionality and compare the values at `j`.

Simplify using `only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, col, mat, lact, rmul, Matrix.of_apply, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hg, mul_comm]`. Use the proof step `rfl) a`. Use `⟨conj u, by rw [Complex.norm_conj, hu], fun v => ?_⟩` and prove the remaining obligations. Establish `hemb : Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E).mulVec v) = g.mulVec (Data.emb τ.1 v)`. Use function extensionality and compare the values at `j`.

Simplify using `[Data.emb, hg, Matrix.mulVec, dotProduct]`. Rewrite using `[h, hermC_smul_right, hemb, hst]`.
-/
theorem exists_unit_frame (X : Data E r) {x b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ) (A : TorusAt X x)
    (A' : TorusAt X (lact γ (rmul x b))) (τ : X.Ψ) (a : Fin r) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ v : Fin r → E,
      hermC τ.1 X.Gm (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E).mulVec v)) (A'.e τ a) =
        u * hermC τ.1 X.Gm (Data.emb τ.1 v) (A.e τ a) := by
  set g := (γ : Matrix (Fin r) (Fin r) E).map τ.1 with hg
  have hst : ∀ u w, hermC τ.1 X.Gm (g.mulVec u) (g.mulVec w) = hermC τ.1 X.Gm u w :=
    hermC_map_mulVec X.Gm hγ.1 τ.1
  obtain ⟨u, hu, h⟩ := exists_unit_of_flag X τ (fun a => g.mulVec (A.e τ a)) (A'.e τ)
    (fun a b => by rw [hst, A.e_orth]) (A'.e_orth τ) (fun i hi => by
      rw [A'.e_flag τ i hi]
      have hmap : Submodule.span ℂ (Set.range fun a : Fin i => g.mulVec (A.e τ (Fin.castLE hi a))) =
          (Submodule.span ℂ (Set.range fun a : Fin i => A.e τ (Fin.castLE hi a))).map
            g.mulVecLin := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl
      rw [hmap, A.e_flag τ i hi, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      refine ⟨∑ c, b τ c (Fin.castLE hi k) • col (mat x τ) c, ?_, ?_⟩
      · refine Submodule.sum_mem _ fun c _ => ?_
        by_cases hc : (c : ℕ) < i
        · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨c, hc⟩, rfl⟩)
        · rw [(hb τ).2 c (Fin.castLE hi k) (by
            have := k.2
            rw [Fin.lt_def]
            simp only [Fin.val_castLE]
            omega), zero_smul]
          exact Submodule.zero_mem _
      · funext j
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, col, mat, lact, rmul,
          Matrix.of_apply, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hg,
          mul_comm]
        rfl) a
  refine ⟨conj u, by rw [Complex.norm_conj, hu], fun v => ?_⟩
  have hemb : Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E).mulVec v) =
      g.mulVec (Data.emb τ.1 v) := by
    funext j
    simp [Data.emb, hg, Matrix.mulVec, dotProduct]
  rw [h, hermC_smul_right, hemb, hst]

/- English proof (translation)
Establish `hcase : ∀ σ : E →+* ℂ, (∃ τ : X.Ψ, σ = τ.1) ∨ ∃ τ : X.Ψ, σ = ComplexEmbedding.conjugate τ.1`. Introduce `σ`. Distinguish the cases in `h : σ ∈ X.Ψ`. Conclude with `Or.inl ⟨⟨σ, h⟩, rfl⟩`. Use `Or.inr ⟨⟨ComplexEmbedding.conjugate σ, ?_⟩, (TorusAtDataPf.conj_conj_X σ).symm⟩` and prove the remaining obligations.

Rewrite using `[X.cmType, TorusAtDataPf.conj_conj_X]`. Conclude with `h`. Establish `hdim : ∀ σ, A'.T.dim σ = A.T.dim σ`. Introduce `σ`. Break down `hcase σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩` into its components or cases.

Rewrite using `[A.dim_pos, A'.dim_pos]`. Rewrite using `[A.dim_neg, A'.dim_neg]`. Set `ε : Idx A'.T.dim ≃ Idx A.T.dim` to `Equiv.sigmaCongrRight fun σ => finCongr (hdim σ)`. Establish `key : ∀ i : Idx A'.T.dim, ∃ w : ℂ, ‖w‖ = 1 ∧ ∀ v, A'.φ ((γ : Matrix (Fin r) (Fin r) E).mulVec v) i = w * A.φ v (ε i)`. Introduce and unpack `⟨σ, a⟩`.

Break down `hcase σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩` into its components or cases. Take `⟨u, hu, h⟩` from `exists_unit_frame X hb hγ A A' τ (Fin.castLE (by rw [A'.dim_pos τ]; exact X.p0_le) a)`. Use `⟨u, hu, fun v => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = u * A.φ v ⟨τ.1, Fin.cast (hdim _) a⟩`. Rewrite using `[A'.coord_pos, A.coord_pos, h, mul_left_comm]`.

Both sides reduce to the same expression. Take `⟨u, hu, h⟩` from `exists_unit_frame X hb hγ A A' τ ⟨X.p0 + a.1, by`. Establish `h1 : a.1 < r - X.p0` using `lt_of_lt_of_eq a.2 (A'.dim_neg τ)`. Use `X.p0_le` as an intermediate fact. Use the proof step `omega⟩`.

Use `⟨conj u, by rw [Complex.norm_conj, hu], fun v => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = conj u * A.φ v ⟨ComplexEmbedding.conjugate τ.1, Fin.cast (hdim _) a⟩`. Rewrite using `[A'.coord_neg, A.coord_neg, h, ← mul_neg, map_mul, mul_left_comm]`. Both sides reduce to the same expression. Use `choose w hw hkey using key`.

Apply the tactic sequence `obtain ⟨U, hU⟩ := exists_diag_isometry ε w hw`. Use `⟨U, fun v => ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Rewrite using `[hU, hkey]`.
-/
theorem exists_isometry (X : Data E r) {x b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ) (A : TorusAt X x)
    (A' : TorusAt X (lact γ (rmul x b))) :
    ∃ U : Vsp A.T.dim ≃ₗᵢ[ℂ] Vsp A'.T.dim,
      ∀ v, U (A.φ v) = A'.φ ((γ : Matrix (Fin r) (Fin r) E).mulVec v) := by
  have hcase : ∀ σ : E →+* ℂ, (∃ τ : X.Ψ, σ = τ.1) ∨
      ∃ τ : X.Ψ, σ = ComplexEmbedding.conjugate τ.1 := by
    intro σ
    by_cases h : σ ∈ X.Ψ
    · exact Or.inl ⟨⟨σ, h⟩, rfl⟩
    · refine Or.inr ⟨⟨ComplexEmbedding.conjugate σ, ?_⟩, (TorusAtDataPf.conj_conj_X σ).symm⟩
      rw [X.cmType, TorusAtDataPf.conj_conj_X]
      exact h
  have hdim : ∀ σ, A'.T.dim σ = A.T.dim σ := by
    intro σ
    rcases hcase σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
    · rw [A.dim_pos, A'.dim_pos]
    · rw [A.dim_neg, A'.dim_neg]
  let ε : Idx A'.T.dim ≃ Idx A.T.dim := Equiv.sigmaCongrRight fun σ => finCongr (hdim σ)
  have key : ∀ i : Idx A'.T.dim, ∃ w : ℂ, ‖w‖ = 1 ∧ ∀ v,
      A'.φ ((γ : Matrix (Fin r) (Fin r) E).mulVec v) i = w * A.φ v (ε i) := by
    rintro ⟨σ, a⟩
    rcases hcase σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
    · obtain ⟨u, hu, h⟩ := exists_unit_frame X hb hγ A A' τ
        (Fin.castLE (by rw [A'.dim_pos τ]; exact X.p0_le) a)
      refine ⟨u, hu, fun v => ?_⟩
      change _ = u * A.φ v ⟨τ.1, Fin.cast (hdim _) a⟩
      rw [A'.coord_pos, A.coord_pos, h, mul_left_comm]
      rfl
    · obtain ⟨u, hu, h⟩ := exists_unit_frame X hb hγ A A' τ
        ⟨X.p0 + a.1, by
          have h1 : a.1 < r - X.p0 := lt_of_lt_of_eq a.2 (A'.dim_neg τ)
          have := X.p0_le
          omega⟩
      refine ⟨conj u, by rw [Complex.norm_conj, hu], fun v => ?_⟩
      change _ = conj u * A.φ v ⟨ComplexEmbedding.conjugate τ.1, Fin.cast (hdim _) a⟩
      rw [A'.coord_neg, A.coord_neg, h, ← mul_neg, map_mul, mul_left_comm]
      rfl
  choose w hw hkey using key
  obtain ⟨U, hU⟩ := exists_diag_isometry ε w hw
  refine ⟨U, fun v => ?_⟩
  ext i
  rw [hU, hkey]

end Frames

/- English proof (translation)
Introduce `E _ _ _ r X hw x _ b hb γ hγ A A' v`. Use `⟨?_, fun u hu => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `obtain ⟨U, hU⟩ := exists_isometry X.toData hb hγ A A'`. Establish `hL : ∀ y, y ∈ A.T.L ↔ U y ∈ A'.T.L`. Introduce `y`.

Rewrite using `[A.lat, A'.lat]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Conclude with `⟨_, (hγ.2 w).1 hw, (hU w).symm⟩`. Introduce and unpack `⟨w, hw, h⟩`.

Establish `e : (γ : Matrix (Fin r) (Fin r) E).mulVec (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec w) = w`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Use `⟨_, (hγ.2 _).2 (e.symm ▸ hw), U.injective ?_⟩` and prove the remaining obligations. Rewrite using `[hU, e, h]`. Establish `he : ∀ y ∈ A.T.L, A'.T.eps (U y) = A.T.eps y`.

Introduce `y hy`. Take `⟨w, hw', rfl⟩` from `(A.lat y).1 hy`. Rewrite using `[hU]`. Conclude with `GlobalTheory.torusAt_eps_indep E r X hw x _ A A' γ hγ w hw'`. Rewrite using `[← hU]`.

Conclude with `ratio_eq A.T A'.T U hL he A.s_mem A.s_ne A'.s_mem A'.s_ne _`. Rewrite using `[map_add]`. Use `congr 1`. Conclude with `pointwiseNormSq_add_period A.T A.s_mem (γ := fun _ => A.φ u) (fun _ => (A.lat _).2 ⟨u, hu, rfl⟩) (fun _ => A.φ v)`.
-/
theorem normalised_theta_norm_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r), (∃ w0 : 𝓞 E, ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) - Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) → ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → ∀ (A : TorusAt X.toData x) (A' : TorusAt X.toData (lact γ (rmul x b))) (v : Fin r → E), A'.T.ptN2 1 A'.s (fun _ => A'.φ ((γ : Matrix (Fin r) (Fin r) E).mulVec v)) / A'.T.l2 1 A'.s = A.T.ptN2 1 A.s (fun _ => A.φ v) / A.T.l2 1 A.s ∧ ∀ u ∈ X.Λ, A.T.ptN2 1 A.s (fun _ => A.φ (v + u)) / A.T.l2 1 A.s = A.T.ptN2 1 A.s (fun _ => A.φ v) / A.T.l2 1 A.s := by
  intro E _ _ _ r X hw x _ b hb γ hγ A A' v
  refine ⟨?_, fun u hu => ?_⟩
  · obtain ⟨U, hU⟩ := exists_isometry X.toData hb hγ A A'
    have hL : ∀ y, y ∈ A.T.L ↔ U y ∈ A'.T.L := by
      intro y
      rw [A.lat, A'.lat]
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨_, (hγ.2 w).1 hw, (hU w).symm⟩
      · rintro ⟨w, hw, h⟩
        have e : (γ : Matrix (Fin r) (Fin r) E).mulVec
            (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec w) = w := by
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
            Matrix.one_mulVec]
        refine ⟨_, (hγ.2 _).2 (e.symm ▸ hw), U.injective ?_⟩
        rw [hU, e, h]
    have he : ∀ y ∈ A.T.L, A'.T.eps (U y) = A.T.eps y := by
      intro y hy
      obtain ⟨w, hw', rfl⟩ := (A.lat y).1 hy
      rw [hU]
      exact GlobalTheory.torusAt_eps_indep E r X hw x _ A A' γ hγ w hw'
    rw [← hU]
    exact ratio_eq A.T A'.T U hL he A.s_mem A.s_ne A'.s_mem A'.s_ne _
  · rw [map_add]
    congr 1
    exact pointwiseNormSq_add_period A.T A.s_mem (γ := fun _ => A.φ u)
      (fun _ => (A.lat _).2 ⟨u, hu, rfl⟩) (fun _ => A.φ v)

end GlobalTheory.ThetaRho
