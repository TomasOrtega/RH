import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.X1

/- English proof (translation)
Establish `e : adj X = Matrix.diagonal (fun i => (sgn i : k)) * ((Matrix.transpose X).submatrix Fin.rev Fin.rev) * Matrix.diagonal (fun i => (sgn i : k))`. Use extensionality with `i j`. Rewrite using `[adj_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.submatrix_apply, Matrix.transpose_apply, zsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.rank_transpose X]`. Conclude with `Matrix.rank_submatrix (Matrix.transpose X) Fin.revPerm Fin.revPerm`.
-/
private theorem rank_adj_le {k : Type} [Field k] (X : M4 k) : (adj X).rank ≤ X.rank := by
  have e : adj X = Matrix.diagonal (fun i => (sgn i : k)) * ((Matrix.transpose X).submatrix Fin.rev Fin.rev) * Matrix.diagonal (fun i => (sgn i : k)) := by
    ext i j
    rw [adj_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.submatrix_apply, Matrix.transpose_apply, zsmul_eq_mul]
    push_cast
    ring
  rw [e]
  calc _ ≤ (Matrix.diagonal (fun i => (sgn i : k)) * ((Matrix.transpose X).submatrix Fin.rev Fin.rev)).rank := Matrix.rank_mul_le_left _ _
    _ ≤ ((Matrix.transpose X).submatrix Fin.rev Fin.rev).rank := Matrix.rank_mul_le_right _ _
    _ = X.rank := by
      rw [← Matrix.rank_transpose X]
      exact Matrix.rank_submatrix (Matrix.transpose X) Fin.revPerm Fin.revPerm

private noncomputable def cmp {k : Type} [Field k] (p : M4 k) :
    M4 k →ₗ[k] (LinearMap.range p.mulVecLin →ₗ[k] LinearMap.range p.mulVecLin) where
  toFun X := p.mulVecLin.rangeRestrict ∘ₗ X.mulVecLin ∘ₗ (LinearMap.range p.mulVecLin).subtype
  map_add' X Y := by
    rw [Matrix.mulVecLin_add, LinearMap.add_comp, LinearMap.comp_add]
  map_smul' a X := by
    ext v i
    simp [Matrix.smul_mulVec, Matrix.mulVec_smul]

/- English proof (translation)
Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Use `LinearMap.ext fun w => ?_` and prove the remaining obligations. Simplify using `only [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply]`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Establish `h2` using `congrArg Subtype.val (LinearMap.congr_fun h ⟨Matrix.mulVec p w, w, rfl⟩)`.

Simplify `h2` using `[cmp]`.
-/
private theorem cmp_zero {k : Type} [Field k] (p X : M4 k) (h : cmp p X = 0) : p * X * p = 0 := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun w => ?_
  simp only [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have h2 := congrArg Subtype.val (LinearMap.congr_fun h ⟨Matrix.mulVec p w, w, rfl⟩)
  simpa [cmp] using h2

end UpperTheory.V.Ws.X1

/- English proof (translation)
Introduce `k Γ _ _ r h h2 s hss hs`. Use `set g := r s with hgdef`. Establish `adj_mul` using `(grp k).1`. Establish `adj_adj` using `(grp k).2.1`. Establish `adj_add` using `(grp k).2.2.1`.

Establish `adj_smul` using `(grp k).2.2.2.1`. Establish `adj_one` using `(grp k).2.2.2.2.1`. Establish `hg2 : g * g = 1` using `by rw [hgdef, ← r.map_mul, hss, r.map_one]`. Establish `hsi : s⁻¹ = s` using `(eq_inv_of_mul_eq_one_left hss).symm`. Establish `hadj : adj g = -g`.

Establish `e : adj g * g = (-1 : k) • 1` using `hs`. Combine the equalities or inequalities in the displayed calculation. Use `set c : k := (2 : k)⁻¹ with hc`. Establish `hc2 : c * 2 = 1` using `inv_mul_cancel₀ h2`. Use `set p : M4 k := c • (1 + g) with hp`.

Use `set q : M4 k := c • (1 - g) with hq`. Establish `hpq : p + q = 1`. Rewrite using `[hp, hq, ← smul_add]`. Establish `e : (1 + g) + (1 - g) = (2 : k) • (1 : M4 k)` using `by rw [two_smul]; abel`. Rewrite using `[e, smul_smul, hc2, one_smul]`.

Establish `hadjp : adj p = q`. Rewrite using `[hp, hq, adj_smul, adj_add, adj_one, hadj, sub_eq_add_neg]`. Establish `hadjq : adj q = p` using `by rw [← hadjp, adj_adj]`. Establish `hpq0 : p * q = 0`. Establish `e : (1 + g) * (1 - g) = 0`.

Rewrite using `[add_mul, mul_sub, mul_sub, hg2]`. Simplify using the standard rewrite rules. Rewrite using `[hp, hq, smul_mul_assoc, mul_smul_comm, e]`. Simplify using the standard rewrite rules. Establish `hpp : p * p = p`.

Establish `e : p * p = p * (p + q)` using `by rw [mul_add, hpq0, add_zero]`. Rewrite using `[e, hpq, mul_one]`. Establish `hrk : p.rank ≤ 2`. Establish `h1 : q.rank ≤ p.rank` using `by rw [← hadjp]; exact rank_adj_le p`. Establish `h1' : p.rank ≤ q.rank` using `by rw [← hadjq]; exact rank_adj_le q`.

Establish `hle : LinearMap.range q.mulVecLin ≤ LinearMap.ker p.mulVecLin`. Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hpq0, Matrix.zero_mulVec]`. Establish `hmono` using `Submodule.finrank_mono hle`. Establish `hsum` using `LinearMap.finrank_range_add_finrank_ker p.mulVecLin`.

Rewrite `hsum` using `[Module.finrank_fin_fun]`. Establish `eq1 : q.rank = Module.finrank k (LinearMap.range q.mulVecLin)` using `rfl`. Establish `eq2 : p.rank = Module.finrank k (LinearMap.range p.mulVecLin)` using `rfl`. Use linear arithmetic over natural numbers and integers. Set `K` to `LinearMap.ker (adSp r h s - 1)`.

Set `ψ : K →ₗ[k] (LinearMap.range p.mulVecLin →ₗ[k] LinearMap.range p.mulVecLin)` to `cmp p ∘ₗ (sp4 k).subtype ∘ₗ K.subtype`. Establish `hinj : Function.Injective ψ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce and unpack `⟨⟨Y, hYsp⟩, hYk⟩ hY`. Establish `hYa : adj Y = -Y` using `hYsp`.

Establish `hfix : g * Y * g = Y`. Establish `e` using `LinearMap.mem_ker.mp hYk`. Rewrite `e` using `[LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]`. Establish `e2` using `congrArg Subtype.val e`. Rewrite `e2` using `[adSp_val, hsi]`.

Conclude with `e2`. Establish `hcomm : g * Y = Y * g`. Combine the equalities or inequalities in the displayed calculation. Establish `hpY : p * Y = Y * p`. Rewrite using `[hp, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, hcomm]`.

Establish `hz : p * Y * p = 0` using `cmp_zero p Y hY`. Establish `hYp : Y * p = 0`. Rewrite `hz` using `[hpY, Matrix.mul_assoc, hpp]`. Conclude with `hz`. Establish `h0 : adj (0 : M4 k) = 0` using `by simpa using adj_smul 0 0`.

Establish `hqY : q * Y = 0`. Establish `e` using `congrArg adj hYp`. Rewrite `e` using `[adj_mul, hadjp, hYa, h0, Matrix.mul_neg, neg_eq_zero]`. Conclude with `e`. Establish `hq' : q = 1 - p` using `eq_sub_of_add_eq' hpq`.

Establish `hYq : Y * q = 0`. Rewrite `hqY`, the goal using `[hq']`. Rewrite using `[Matrix.mul_sub, Matrix.mul_one, ← hpY]`. Rewrite `hqY` using `[Matrix.sub_mul, Matrix.one_mul]`. Conclude with `hqY`.

Establish `hY0 : Y = 0`. Combine the equalities or inequalities in the displayed calculation. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `hY0`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.Ws.X1.ccDim :
    ∀ {k Γ : Type} [Field k] [Group Γ] (r : Γ →* M4 k) (h : ∀ g, ∃ x, IsGSp x (r g)), (2 : k) ≠ 0 → ∀ s : Γ, s * s = 1 → IsGSp (-1) (r s) → Module.finrank k (LinearMap.ker (adSp r h s - 1)) ≤ 4 := by
  intro k Γ _ _ r h h2 s hss hs
  set g := r s with hgdef
  have adj_mul := (grp k).1
  have adj_adj := (grp k).2.1
  have adj_add := (grp k).2.2.1
  have adj_smul := (grp k).2.2.2.1
  have adj_one := (grp k).2.2.2.2.1
  have hg2 : g * g = 1 := by rw [hgdef, ← r.map_mul, hss, r.map_one]
  have hsi : s⁻¹ = s := (eq_inv_of_mul_eq_one_left hss).symm
  have hadj : adj g = -g := by
    have e : adj g * g = (-1 : k) • 1 := hs
    calc adj g = adj g * g * g := by rw [Matrix.mul_assoc, hg2, Matrix.mul_one]
      _ = -g := by rw [e]; simp
  set c : k := (2 : k)⁻¹ with hc
  have hc2 : c * 2 = 1 := inv_mul_cancel₀ h2
  set p : M4 k := c • (1 + g) with hp
  set q : M4 k := c • (1 - g) with hq
  have hpq : p + q = 1 := by
    rw [hp, hq, ← smul_add]
    have e : (1 + g) + (1 - g) = (2 : k) • (1 : M4 k) := by rw [two_smul]; abel
    rw [e, smul_smul, hc2, one_smul]
  have hadjp : adj p = q := by
    rw [hp, hq, adj_smul, adj_add, adj_one, hadj, sub_eq_add_neg]
  have hadjq : adj q = p := by rw [← hadjp, adj_adj]
  have hpq0 : p * q = 0 := by
    have e : (1 + g) * (1 - g) = 0 := by
      rw [add_mul, mul_sub, mul_sub, hg2]
      simp
    rw [hp, hq, smul_mul_assoc, mul_smul_comm, e]
    simp
  have hpp : p * p = p := by
    have e : p * p = p * (p + q) := by rw [mul_add, hpq0, add_zero]
    rw [e, hpq, mul_one]
  have hrk : p.rank ≤ 2 := by
    have h1 : q.rank ≤ p.rank := by rw [← hadjp]; exact rank_adj_le p
    have h1' : p.rank ≤ q.rank := by rw [← hadjq]; exact rank_adj_le q
    have hle : LinearMap.range q.mulVecLin ≤ LinearMap.ker p.mulVecLin := by
      rintro _ ⟨w, rfl⟩
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hpq0, Matrix.zero_mulVec]
    have hmono := Submodule.finrank_mono hle
    have hsum := LinearMap.finrank_range_add_finrank_ker p.mulVecLin
    rw [Module.finrank_fin_fun] at hsum
    have eq1 : q.rank = Module.finrank k (LinearMap.range q.mulVecLin) := rfl
    have eq2 : p.rank = Module.finrank k (LinearMap.range p.mulVecLin) := rfl
    omega
  let K := LinearMap.ker (adSp r h s - 1)
  let ψ : K →ₗ[k] (LinearMap.range p.mulVecLin →ₗ[k] LinearMap.range p.mulVecLin) :=
    cmp p ∘ₗ (sp4 k).subtype ∘ₗ K.subtype
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨Y, hYsp⟩, hYk⟩ hY
    have hYa : adj Y = -Y := hYsp
    have hfix : g * Y * g = Y := by
      have e := LinearMap.mem_ker.mp hYk
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at e
      have e2 := congrArg Subtype.val e
      rw [adSp_val, hsi] at e2
      exact e2
    have hcomm : g * Y = Y * g := by
      calc g * Y = g * Y * (g * g) := by rw [hg2, Matrix.mul_one]
        _ = (g * Y * g) * g := by simp only [Matrix.mul_assoc]
        _ = Y * g := by rw [hfix]
    have hpY : p * Y = Y * p := by
      rw [hp, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, hcomm]
    have hz : p * Y * p = 0 := cmp_zero p Y hY
    have hYp : Y * p = 0 := by
      rw [hpY, Matrix.mul_assoc, hpp] at hz
      exact hz
    have h0 : adj (0 : M4 k) = 0 := by simpa using adj_smul 0 0
    have hqY : q * Y = 0 := by
      have e := congrArg adj hYp
      rw [adj_mul, hadjp, hYa, h0, Matrix.mul_neg, neg_eq_zero] at e
      exact e
    have hq' : q = 1 - p := eq_sub_of_add_eq' hpq
    have hYq : Y * q = 0 := by
      rw [hq'] at hqY ⊢
      rw [Matrix.mul_sub, Matrix.mul_one, ← hpY]
      rw [Matrix.sub_mul, Matrix.one_mul] at hqY
      exact hqY
    have hY0 : Y = 0 := by
      calc Y = Y * (p + q) := by rw [hpq, Matrix.mul_one]
        _ = 0 := by rw [Matrix.mul_add, hYp, hYq, add_zero]
    apply Subtype.ext
    apply Subtype.ext
    exact hY0
  calc Module.finrank k K ≤ Module.finrank k (LinearMap.range p.mulVecLin →ₗ[k] LinearMap.range p.mulVecLin) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = p.rank * p.rank := by rw [Module.finrank_linearMap]; rfl
    _ ≤ 2 * 2 := Nat.mul_le_mul hrk hrk
    _ = 4 := rfl
