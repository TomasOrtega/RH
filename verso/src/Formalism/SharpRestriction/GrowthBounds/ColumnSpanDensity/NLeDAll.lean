import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.InvariantSectionsTransportGL

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems

/- English proof (translation)
Establish `hcnt` using `restEdgeCountSrc`. Establish `hdnn` using `dL_nonneg R lam0`. Distinguish the cases in `hn0 : n = 0`. Substitute `hn0` using the available equality. Simplify using `using hdnn`.

Establish `hL : IsLattice R.W (colSpan R.W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Qq))` using `⟨1, by simp, rfl⟩`. Take `⟨Ne, es, hinj, hes, hNe⟩` from `hcnt p n' R (m + 1) (by omega) _ hL`. Establish `hc1 : 1 ≤ c`. Establish `: (0 : ℝ) < c` using `by linarith`. Conclude with `this` after adjusting the coercions.

Establish `hdata : ∀ i : Fin Ne, ∃ (x : Fin n → Vsp R.Kf lam0) (y : Fin n → Module.Dual R.Kf (Vsp R.Kf lam0)) (z z' : R.O), z ≠ 0 ∧ (∀ a, x a ∈ CCL R lam0 t c (es i)) ∧ (∀ a, y a ∈ Re' p R.ι R.σ R.w 1 lam0 (es i)) ∧ z' * z = R.w ^ (c - 1) ∧ ∀ a b, be p 1 lam0 (x a) (y b) = if a = b then alg …`. Introduce `i`. Break down `hfac (es i) (hes i).1 with h0 | ⟨x, y, hx, hy, z, Mx, hz, hv, hM⟩` into its components or cases. Conclude with `absurd h0 hn0`. Take `⟨z', hz'⟩` from `dvd_w_pow_of_vLEO R.std.2.1 R.std.1.w_sq hz hDc hv`.

Use `⟨x, fun b => ∑ l, Mx l b • y l, z, z', hz, hx, fun b => Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _ (hy l)), by rw [hz']; ring, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[be_sum]`. Conclude with `hM a b`. Use `choose x y z z' hz0 hx hy hzz hxy using hdata`. Establish `hβ : ∀ i l : Fin Ne × Fin n, ∃ β : R.O, β ∈ IsLocalRing.maximalIdeal R.O ∧ be p 1 lam0 (x i.1 i.2) (y l.1 l.2) = algebraMap R.O R.Kf (((1 : Matrix (Fin Ne × Fin n) (Fin Ne × Fin n) R.O) i l + β) * z l.1)`.

Introduce and unpack `⟨i, a⟩ ⟨l, b⟩`. Distinguish the cases in `hil : i = l`. Substitute `hil` using the available equality. Use `⟨0, Submodule.zero_mem _, ?_⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[hxy, Matrix.one_apply]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using the standard rewrite rules. Establish `: ((i, a) : Fin Ne × Fin n) ≠ (i, b)` using `fun h => hab (Prod.mk.inj h).2`.

Rewrite using `[if_neg hab, if_neg this]`. Simplify using the standard rewrite rules. Establish `hne : es l ≠ es i` using `fun h => hil (hinj h).symm`. Establish `hXs` using `CCL_other R lam0 t c (es i) (es l) (hes _).1 ((hes _).2.trans (hes _).2.symm) hne (hx i a)`. Take `⟨b', hb⟩` from `be_scale_Re R lam0 (es l) c hXs (hy l b)`.

Establish `h2 : ((i, a) : Fin Ne × Fin n) ≠ (l, b)` using `fun h => hil (Prod.mk.inj h).1`. Use `⟨R.w * b' * z' l, Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ R.w_mem), ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hb, Matrix.one_apply_ne h2, zero_add]`. Use `congr 1`.

Establish `h3 : R.w ^ c = R.w * R.w ^ (c - 1)`. Rewrite using `[← pow_succ']`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h3, ← hzz l]`.

Expand and normalize the polynomial expressions, which then agree. Use `choose β hβm hβe using hβ`. Set `P : Matrix (Fin Ne × Fin n) (Fin Ne × Fin n) R.O` to `Matrix.of fun i l => (1 : Matrix _ _ R.O) i l + β i l`. Establish `hP : IsUnit P.det`. Apply `isUnit_det_of_one_add'` to reduce the goal to its premises.

Introduce `i l`. Simplify `hβm i l` using `[P]`. Establish `hinjK : Function.Injective (algebraMap R.O R.Kf)`. Establish `hfr : IsFractionRing R.O R.Kf` using `R.std.1.frac_O`. Conclude with `IsFractionRing.injective R.O R.Kf`.

Establish `hPK : ((algebraMap R.O R.Kf).mapMatrix P).det ≠ 0`. Rewrite using `[← RingHom.map_det]`. Introduce `h0`. Establish `: P.det = 0` using `hinjK (by rw [h0, map_zero])`. Rewrite `hP` using `[this]`.

Conclude with `not_isUnit_zero hP`. Establish `hli : LinearIndependent R.Kf (fun i : Fin Ne × Fin n => x i.1 i.2)`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Establish `h1 : ∀ l : Fin Ne × Fin n, ∑ i, g i * algebraMap R.O R.Kf (P i l) = 0`.

Introduce `l`. Establish `h2 : be p 1 lam0 (∑ i, g i • x i.1 i.2) (y l.1 l.2) = 0`. Rewrite using `[hg]`. Simplify using `[be]`. Rewrite `h2` using `[be_sum_left]`.

Establish `h3 : (∑ i, g i * algebraMap R.O R.Kf (P i l)) * algebraMap R.O R.Kf (z l.1) = 0`. Rewrite using `[← h2, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hβe i l, map_mul, mul_assoc]`. Both sides reduce to the same expression.

Establish `hz : algebraMap R.O R.Kf (z l.1) ≠ 0` using `fun h => hz0 l.1 (hinjK (by rw [h, map_zero]))`. Conclude with `(mul_eq_zero.1 h3).resolve_right hz`. Establish `h4 : Matrix.vecMul g ((algebraMap R.O R.Kf).mapMatrix P) = 0`. Use function extensionality and compare the values at `l`. Simplify `h1 l` using `[Matrix.vecMul, dotProduct]`.

Establish `h5` using `Matrix.eq_zero_of_vecMul_eq_zero hPK h4`. Introduce `i`. Rewrite using `[h5]`. Both sides reduce to the same expression. Establish `hpos : 0 < dimV R.Kf lam0` using `Formalism.MainNotions.G.LatticeSystems.kp_dimV_pos R.Kf lam0 hDom`.

Establish `hfin : Module.Finite R.Kf (Vsp R.Kf lam0)` using `Module.finite_of_finrank_pos hpos`. Establish `hcard : Ne * n ≤ dimV R.Kf lam0`. Use `hli.fintype_card_le_finrank` as an intermediate fact. Simplify `this` using `[dimV]`. Establish `hNpos` using `gaussianNumber_prime_pow_pos R (m + 1) (by omega)`.

Unfold `dL`. Rewrite using `[le_div_iff₀ hNpos]`. Establish `h6 : ((Ne * n : ℕ) : ℝ) ≤ (dimV R.Kf lam0 : ℝ)` using `by exact_mod_cast hcard`. Establish `h7 : (n : ℝ) * gaussianNumber (p ^ n') (m + 1) ≤ (n : ℝ) * Ne` using `mul_le_mul_of_nonneg_left hNe (Nat.cast_nonneg _)`. Move the coercions through the operations in `at h6`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nLeD_all {p n' : ℕ} (R : RS p n') {m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hDom : IsDominant lam0)
    (t c n : ℕ) (D : ℝ) (hD0 : 0 ≤ D) (hDc : 2 * D < c)
    (hfac : ∀ e, IsEdge p n' 1 e →
      FactorsLE p (be (Kf := R.Kf) p 1 lam0) (CCL R lam0 t c e) (Re' p R.ι R.σ R.w 1 lam0 e) n D) :
    (n : ℝ) ≤ dL R lam0 := by
  classical
  have hcnt := restEdgeCountSrc
  have hdnn := dL_nonneg R lam0
  by_cases hn0 : n = 0
  · subst hn0; simpa using hdnn
  have hL : IsLattice R.W (colSpan R.W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Qq)) := ⟨1, by simp, rfl⟩
  obtain ⟨Ne, es, hinj, hes, hNe⟩ := hcnt p n' R (m + 1) (by omega) _ hL
  have hc1 : 1 ≤ c := by
    have : (0 : ℝ) < c := by linarith
    exact_mod_cast this
  have hdata : ∀ i : Fin Ne, ∃ (x : Fin n → Vsp R.Kf lam0)
      (y : Fin n → Module.Dual R.Kf (Vsp R.Kf lam0)) (z z' : R.O), z ≠ 0 ∧
      (∀ a, x a ∈ CCL R lam0 t c (es i)) ∧ (∀ a, y a ∈ Re' p R.ι R.σ R.w 1 lam0 (es i)) ∧
      z' * z = R.w ^ (c - 1) ∧
      ∀ a b, be p 1 lam0 (x a) (y b) = if a = b then algebraMap R.O R.Kf z else 0 := by
    intro i
    rcases hfac (es i) (hes i).1 with h0 | ⟨x, y, hx, hy, z, Mx, hz, hv, hM⟩
    · exact absurd h0 hn0
    · obtain ⟨z', hz'⟩ := dvd_w_pow_of_vLEO R.std.2.1 R.std.1.w_sq hz hDc hv
      refine ⟨x, fun b => ∑ l, Mx l b • y l, z, z', hz, hx,
        fun b => Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _ (hy l)), by rw [hz']; ring, fun a b => ?_⟩
      rw [be_sum]
      exact hM a b
  choose x y z z' hz0 hx hy hzz hxy using hdata
  have hβ : ∀ i l : Fin Ne × Fin n, ∃ β : R.O, β ∈ IsLocalRing.maximalIdeal R.O ∧
      be p 1 lam0 (x i.1 i.2) (y l.1 l.2) =
        algebraMap R.O R.Kf (((1 : Matrix (Fin Ne × Fin n) (Fin Ne × Fin n) R.O) i l + β) * z l.1) := by
    rintro ⟨i, a⟩ ⟨l, b⟩
    by_cases hil : i = l
    · subst hil
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      simp only
      rw [hxy, Matrix.one_apply]
      by_cases hab : a = b
      · subst hab; simp
      · have : ((i, a) : Fin Ne × Fin n) ≠ (i, b) := fun h => hab (Prod.mk.inj h).2
        rw [if_neg hab, if_neg this]; simp
    · have hne : es l ≠ es i := fun h => hil (hinj h).symm
      have hXs := CCL_other R lam0 t c (es i) (es l) (hes _).1 ((hes _).2.trans (hes _).2.symm) hne (hx i a)
      obtain ⟨b', hb⟩ := be_scale_Re R lam0 (es l) c hXs (hy l b)
      have h2 : ((i, a) : Fin Ne × Fin n) ≠ (l, b) := fun h => hil (Prod.mk.inj h).1
      refine ⟨R.w * b' * z' l, Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ R.w_mem), ?_⟩
      simp only
      rw [hb, Matrix.one_apply_ne h2, zero_add]
      congr 1
      have h3 : R.w ^ c = R.w * R.w ^ (c - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h3, ← hzz l]
      ring
  choose β hβm hβe using hβ
  let P : Matrix (Fin Ne × Fin n) (Fin Ne × Fin n) R.O := Matrix.of fun i l => (1 : Matrix _ _ R.O) i l + β i l
  have hP : IsUnit P.det := by
    apply isUnit_det_of_one_add'
    intro i l
    simpa [P] using hβm i l
  have hinjK : Function.Injective (algebraMap R.O R.Kf) := by
    have hfr : IsFractionRing R.O R.Kf := R.std.1.frac_O
    exact IsFractionRing.injective R.O R.Kf
  have hPK : ((algebraMap R.O R.Kf).mapMatrix P).det ≠ 0 := by
    rw [← RingHom.map_det]
    intro h0
    have : P.det = 0 := hinjK (by rw [h0, map_zero])
    rw [this] at hP
    exact not_isUnit_zero hP
  have hli : LinearIndependent R.Kf (fun i : Fin Ne × Fin n => x i.1 i.2) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : ∀ l : Fin Ne × Fin n, ∑ i, g i * algebraMap R.O R.Kf (P i l) = 0 := by
      intro l
      have h2 : be p 1 lam0 (∑ i, g i • x i.1 i.2) (y l.1 l.2) = 0 := by
        rw [hg]; simp [be]
      rw [be_sum_left] at h2
      have h3 : (∑ i, g i * algebraMap R.O R.Kf (P i l)) * algebraMap R.O R.Kf (z l.1) = 0 := by
        rw [← h2, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hβe i l, map_mul, mul_assoc]
        rfl
      have hz : algebraMap R.O R.Kf (z l.1) ≠ 0 := fun h => hz0 l.1 (hinjK (by rw [h, map_zero]))
      exact (mul_eq_zero.1 h3).resolve_right hz
    have h4 : Matrix.vecMul g ((algebraMap R.O R.Kf).mapMatrix P) = 0 := by
      funext l
      simpa [Matrix.vecMul, dotProduct] using h1 l
    have h5 := Matrix.eq_zero_of_vecMul_eq_zero hPK h4
    intro i
    rw [h5]; rfl
  have hpos : 0 < dimV R.Kf lam0 := Formalism.MainNotions.G.LatticeSystems.kp_dimV_pos R.Kf lam0 hDom
  have hfin : Module.Finite R.Kf (Vsp R.Kf lam0) := Module.finite_of_finrank_pos hpos
  have hcard : Ne * n ≤ dimV R.Kf lam0 := by
    have := hli.fintype_card_le_finrank
    simpa [dimV] using this
  have hNpos := gaussianNumber_prime_pow_pos R (m + 1) (by omega)
  unfold dL
  rw [le_div_iff₀ hNpos]
  have h6 : ((Ne * n : ℕ) : ℝ) ≤ (dimV R.Kf lam0 : ℝ) := by exact_mod_cast hcard
  have h7 : (n : ℝ) * gaussianNumber (p ^ n') (m + 1) ≤ (n : ℝ) * Ne := mul_le_mul_of_nonneg_left hNe (Nat.cast_nonneg _)
  push_cast at h6
  linarith

/- English proof (translation)
Establish `hFun` using `restFunct`. Establish `hfrW : IsFractionRing R.W R.Qq` using `R.std.1.frac_alt`. Take `⟨g, hg, hsrc, htgt⟩` from `lc_main p n' 1 (m + 1) R.std.1.p_unif R.std.1.res_card R.std.1.prime.two_le (by have := R.std.1.two_le; omega) e he`. Take `⟨g', hg', hsrc', htgt'⟩` from `lc_main p n' 1 (m + 1) R.std.1.p_unif R.std.1.res_card R.std.1.prime.two_le (by have := R.std.1.two_le; omega) e' he'`. Establish `hug : IsUnit g` using `(Matrix.isUnit_iff_isUnit_det _).2 hg`.

Establish `hug' : IsUnit g'` using `(Matrix.isUnit_iff_isUnit_det _).2 hg'`. Set `γ : GL (Fin (m + 1)) R.Qq` to `hug'.unit * hug.unit⁻¹`. Establish `hγg : (γ : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Qq) * g = g'`. Establish `: γ * hug.unit = hug'.unit` using `by simp [γ]`. Establish `h2` using `congrArg Units.val this`.

Simplify using `using h2`. Establish `hee : e' = mapE γ e`. Consider the cases of `e with`. Consider the case `mk s tg`. Consider the cases of `e' with`.

Consider the case `mk s' tg'`. Simplify using `only at hsrc htgt hsrc' htgt'`. Simplify using `only [mapE]`. Rewrite using `[hsrc, htgt, hsrc', htgt', map_colSpan, map_colSpan, ← Matrix.mul_assoc, hγg]`. Take `⟨T, hT1, hT2⟩` from `hFun p n' R m lam0 hDom γ`.

Establish `hedge : ∀ e'' : Edge R.W R.Qq (m + 1), IsEdge p n' 1 e'' → IsEdge p n' 1 (mapE γ⁻¹ e'')` using `fun e'' h => nt_edge_map p n' 1 γ⁻¹ _ _ h`. Establish `hsrcC : ∀ x, x ∈ CCL R lam0 t c e → T x ∈ CCL R lam0 t c (mapE γ e)`. Introduce `x hx`. Use `Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `scale_alt T _ (hT1 e.src he.1) hx.1.1`.

Conclude with `scale_alt T _ (hT2 e he) hx.1.2`. Rewrite using `[Submodule.mem_iInf]`. Introduce `e''`. Rewrite using `[Submodule.mem_iInf]`. Introduce and unpack `⟨h1, h2, h3⟩`.

Establish `h4 : (mapE γ⁻¹ e'').src = e.src` using `by show e''.src.map (nt_phi R.W γ⁻¹) = e.src`. Rewrite using `[h2]`. Conclude with `nt_map_inv γ e.src`. Establish `h5 : mapE γ⁻¹ e'' ≠ e`. Introduce `h`.

Apply `h3` to reduce the goal to its premises. Rewrite using `[← h, mapE_inv]`. Establish `h6` using `CCL_other R lam0 t c e (mapE γ⁻¹ e'') (hedge e'' h1) h4 h5 hx`. Establish `h7` using `apply_mem_scale_scale_of_mem_iff T _ _ (hT2 (mapE γ⁻¹ e'') (hedge e'' h1)) h6`. Rewrite `h7` using `[mapE_inv]`. Then use the resulting hypothesis.

Rewrite using `[hee]`. Break down `hfac with h0 | ⟨x, y, hx, hy, z, M, hz, hv, hM⟩` into its components or cases. Conclude with `Or.inl h0`. Use `Or.inr ⟨fun i => T (x i), fun l => (y l).comp T.symm.toLinearMap, fun i => hsrcC _ (hx i), fun l => comp_symm_mem_scale_dualLat_of_mem_iff T _ (hT2 e he) (hy l), z, M, hz, hv, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[← hM i j]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Use `congr 1`. Unfold `be`. Rewrite using `[LinearMap.comp_apply, ← map_smul]`. Simplify using the standard rewrite rules.
-/
theorem nEdge {p n' : ℕ} (R : RS p n') {m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hDom : IsDominant lam0)
    (t c n : ℕ) (D : ℝ) (e e' : Edge R.W R.Qq (m + 1)) (he : IsEdge p n' 1 e) (he' : IsEdge p n' 1 e')
    (hfac : FactorsLE p (be (Kf := R.Kf) p 1 lam0) (CCL R lam0 t c e) (Re' p R.ι R.σ R.w 1 lam0 e) n D) :
    FactorsLE p (be (Kf := R.Kf) p 1 lam0) (CCL R lam0 t c e') (Re' p R.ι R.σ R.w 1 lam0 e') n D := by
  classical
  have hFun := restFunct
  have hfrW : IsFractionRing R.W R.Qq := R.std.1.frac_alt
  obtain ⟨g, hg, hsrc, htgt⟩ := lc_main p n' 1 (m + 1) R.std.1.p_unif R.std.1.res_card R.std.1.prime.two_le
    (by have := R.std.1.two_le; omega) e he
  obtain ⟨g', hg', hsrc', htgt'⟩ := lc_main p n' 1 (m + 1) R.std.1.p_unif R.std.1.res_card R.std.1.prime.two_le
    (by have := R.std.1.two_le; omega) e' he'
  have hug : IsUnit g := (Matrix.isUnit_iff_isUnit_det _).2 hg
  have hug' : IsUnit g' := (Matrix.isUnit_iff_isUnit_det _).2 hg'
  let γ : GL (Fin (m + 1)) R.Qq := hug'.unit * hug.unit⁻¹
  have hγg : (γ : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Qq) * g = g' := by
    have : γ * hug.unit = hug'.unit := by simp [γ]
    have h2 := congrArg Units.val this
    simpa using h2
  have hee : e' = mapE γ e := by
    cases e with
    | mk s tg =>
      cases e' with
      | mk s' tg' =>
        simp only at hsrc htgt hsrc' htgt'
        simp only [mapE]
        rw [hsrc, htgt, hsrc', htgt', map_colSpan, map_colSpan, ← Matrix.mul_assoc, hγg]
  obtain ⟨T, hT1, hT2⟩ := hFun p n' R m lam0 hDom γ
  have hedge : ∀ e'' : Edge R.W R.Qq (m + 1), IsEdge p n' 1 e'' → IsEdge p n' 1 (mapE γ⁻¹ e'') :=
    fun e'' h => nt_edge_map p n' 1 γ⁻¹ _ _ h
  have hsrcC : ∀ x, x ∈ CCL R lam0 t c e → T x ∈ CCL R lam0 t c (mapE γ e) := by
    intro x hx
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · exact scale_alt T _ (hT1 e.src he.1) hx.1.1
    · exact scale_alt T _ (hT2 e he) hx.1.2
    · rw [Submodule.mem_iInf]
      intro e''
      rw [Submodule.mem_iInf]
      rintro ⟨h1, h2, h3⟩
      have h4 : (mapE γ⁻¹ e'').src = e.src := by
        show e''.src.map (nt_phi R.W γ⁻¹) = e.src
        rw [h2]
        exact nt_map_inv γ e.src
      have h5 : mapE γ⁻¹ e'' ≠ e := by
        intro h
        apply h3
        rw [← h, mapE_inv]
      have h6 := CCL_other R lam0 t c e (mapE γ⁻¹ e'') (hedge e'' h1) h4 h5 hx
      have h7 := apply_mem_scale_scale_of_mem_iff T _ _ (hT2 (mapE γ⁻¹ e'') (hedge e'' h1)) h6
      rwa [mapE_inv] at h7
  rw [hee]
  rcases hfac with h0 | ⟨x, y, hx, hy, z, M, hz, hv, hM⟩
  · exact Or.inl h0
  · refine Or.inr ⟨fun i => T (x i), fun l => (y l).comp T.symm.toLinearMap, fun i => hsrcC _ (hx i),
      fun l => comp_symm_mem_scale_dualLat_of_mem_iff T _ (hT2 e he) (hy l), z, M, hz, hv, fun i j => ?_⟩
    rw [← hM i j]
    refine Finset.sum_congr rfl fun l _ => ?_
    congr 1
    unfold be
    rw [LinearMap.comp_apply, ← map_smul]
    simp

/- English proof (translation)
The claim follows from `nLeD_all R lam0 hDom t c n D hD0 hDc fun e' he' => nEdge R lam0 hDom t c n D e e' he he' hfac`.
-/
theorem nLeD {p n' : ℕ} (R : RS p n') {m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hDom : IsDominant lam0)
    (t c n : ℕ) (D : ℝ) (hD0 : 0 ≤ D) (hDc : 2 * D < c) (e : Edge R.W R.Qq (m + 1)) (he : IsEdge p n' 1 e)
    (hfac : FactorsLE p (be (Kf := R.Kf) p 1 lam0) (CCL R lam0 t c e) (Re' p R.ι R.σ R.w 1 lam0 e) n D) :
    (n : ℝ) ≤ dL R lam0 :=
  nLeD_all R lam0 hDom t c n D hD0 hDc fun e' he' => nEdge R lam0 hDom t c n D e e' he he' hfac

end Formalism.MainNotions.flipOneThree.Pf

end
