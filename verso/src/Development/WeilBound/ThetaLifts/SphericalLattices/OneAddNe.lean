import Development.WeilBound.ThetaLifts.SphericalLattices.LocCommSt
import Development.WeilBound.ThetaLifts.SphericalLattices.DgPerm
import Development.WeilBound.ThetaLifts.SphericalLattices.MemIntGL

noncomputable section

namespace PositivityTheory.Sph.M2

open Matrix Formalism.UG GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

namespace GenC

open GenA GenB

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L} {m : ℕ}

/- English proof (translation)
Rewrite using `[lev_val, levM, ← map_inv, dg_val, dg_val]`. Use `congr 1`. Apply the tactic sequence `ext i j; by_cases h : i = j <;> simp [h]`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`.

Simplify using `[h]`. Simplify using `[h]`.
-/
theorem lev_sc_val (u : Lˣ) :
    ((lev L c m (dg fun _ => u) : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) =
      fromBlocks ((u : L) • 1) 0 0 (c ((u⁻¹ : Lˣ) : L) • 1) := by
  rw [lev_val, levM, ← map_inv, dg_val, dg_val]
  congr 1
  · ext i j; by_cases h : i = j <;> simp [h]
  · ext i j
    by_cases h : i = j
    · simp [h]
    · simp [h]

/- English proof (translation)
Establish `h1 : (u : L) ∈ intL L` using `hu.le`. Establish `h2 : c ((u⁻¹ : Lˣ) : L) ∈ intL L` using `by show Valued.v (c _) ≤ 1`. Rewrite using `[hv, Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]`. Rewrite using `[lev_sc_val]`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j`.

Rewrite using `[fromBlocks_apply₁₁, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] split_ifs`. Rewrite using `[mul_one]`. Conclude with `h1`. Rewrite using `[mul_zero]`. Conclude with `zero_mem _`.

Conclude with `zero_mem _`. Conclude with `zero_mem _`. Rewrite using `[fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] split_ifs`. Rewrite using `[mul_one]`. Conclude with `h2`.

Rewrite using `[mul_zero]`. Conclude with `zero_mem _`.
-/
theorem lev_sc_int (hv : ∀ x, Valued.v (c x) = Valued.v x) {u : Lˣ} (hu : Valued.v (u : L) = 1) (i j) :
    ((lev L c m (dg fun _ => u) : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) i j ∈ intL L := by
  have h1 : (u : L) ∈ intL L := hu.le
  have h2 : c ((u⁻¹ : Lˣ) : L) ∈ intL L := by
    show Valued.v (c _) ≤ 1
    rw [hv, Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  rw [lev_sc_val]
  rcases i with i | i <;> rcases j with j | j
  · rw [fromBlocks_apply₁₁, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one]; exact h1
    · rw [mul_zero]; exact zero_mem _
  · exact zero_mem _
  · exact zero_mem _
  · rw [fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one]; exact h2
    · rw [mul_zero]; exact zero_mem _

/- English proof (translation)
Use `⟨lev_mem hc _, (lev_mem hc _).1, mem_IntGL (lev_sc_int hv hu) ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv, ← map_inv]`. Conclude with `lev_sc_int (u := u⁻¹) hv (by rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one])`.
-/
theorem lev_sc_mem (hc : ∀ x, c (c x) = x) (hv : ∀ x, Valued.v (c x) = Valued.v x) {u : Lˣ}
    (hu : Valued.v (u : L) = 1) : lev L c m (dg fun _ => u) ∈ KPW L c m := by
  refine ⟨lev_mem hc _, (lev_mem hc _).1, mem_IntGL (lev_sc_int hv hu) ?_⟩
  rw [← map_inv, ← map_inv]
  exact lev_sc_int (u := u⁻¹) hv (by rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one])

/- English proof (translation)
Use `ext1`. Rewrite using `[lev_sc_val, zW_val, Units.val_inv_eq_inv_val, map_inv₀, hx]`.
-/
theorem lev_sc_eq {x : Lˣ} (hx : c x = x) : lev L c m (dg fun _ => x) = zW L m x := by
  ext1
  rw [lev_sc_val, zW_val, Units.val_inv_eq_inv_val, map_inv₀, hx]

/- English proof (translation)
Establish `h0 : Valued.v (u : L) ≠ 0` using `(Valuation.ne_zero_iff _).2 u.ne_zero`. Use `⟨WithZero.log (Valued.v (u : L)), ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hx, ← WithZero.exp_zsmul]`. Use `conv_lhs => lhs`. Rewrite using `[← WithZero.exp_log h0]`.

Rewrite using `[← WithZero.exp_add]`. Simplify using the standard rewrite rules.
-/
theorem exists_unit {x : Lˣ} (hx : Valued.v (x : L) = WithZero.exp (-1 : ℤ)) (u : Lˣ) :
    ∃ k : ℤ, Valued.v ((u * x ^ k : Lˣ) : L) = 1 := by
  have h0 : Valued.v (u : L) ≠ 0 := (Valuation.ne_zero_iff _).2 u.ne_zero
  refine ⟨WithZero.log (Valued.v (u : L)), ?_⟩
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hx, ← WithZero.exp_zsmul]
  conv_lhs => lhs; rw [← WithZero.exp_log h0]
  rw [← WithZero.exp_add]
  simp

/- English proof (translation)
Introduce `e` and use `by rw [eq_neg_of_add_eq_zero_right e, Valuation.map_neg, map_one] at hy exact lt_irrefl _ hy`.
-/
theorem one_add_ne {y : L} (hy : Valued.v y < 1) : 1 + y ≠ 0 := fun e => by
  rw [eq_neg_of_add_eq_zero_right e, Valuation.map_neg, map_one] at hy
  exact lt_irrefl _ hy

end GenC

open GenA GenB GenC in
/- English proof (translation)
Introduce `L _ _ ϖ c q h m χ hmul hpos hK hz a ha`. Take `⟨hc, hv, hϖ, hvϖ, -⟩` from `h`. Establish `hvϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ)` using `hvϖ`. Establish `hlt : Valued.v ϖ < 1`. Rewrite using `[hvϖ', ← WithZero.exp_zero, WithZero.exp_lt_exp]`.

Evaluate the numerical expressions. Establish `h0 : ϖ ≠ 0` using `fun e => by`. Rewrite `hvϖ'` using `[e, map_zero]`. Conclude with `WithZero.exp_ne_zero hvϖ'.symm`. Set `x : Lˣ` to `Units.mk0 ϖ h0`.

Establish `hzx : χ (zW L m x) = 1` using `hz x rfl`. Establish `hzm : zW L m x ∈ PW L c m` using `by rw [← lev_sc_eq (c := c) (x := x) hϖ]; exact lev_mem hc _`. Set `ψ : GL (Fin m) L →* ℝ` to `{ toFun := fun t => χ (lev L c m t) map_one' := by rw [map_one]; exact hK 1 (one_mem _) map_mul' := fun s t => by rw [map_mul]; exact hmul _ (lev_mem hc _) _ (lev_mem hc _) }`. Establish `hψ : ∀ t, ψ t = χ (lev L c m t)` using `fun _ => rfl`. Establish `hsc : ∀ u : Lˣ, ψ (dg fun _ => u) = 1`.

Set `φ : Lˣ →* ℝ` to `(ψ.comp dg).comp (Pi.constMonoidHom (Fin m) Lˣ)`. Establish `hφ : ∀ u, φ u = ψ (dg fun _ => u)` using `fun _ => rfl`. Introduce `u`. Take `⟨k, hk⟩` from `exists_unit (x := x) hvϖ' u`. Establish `e1 : φ (u * x ^ k) = 1` using `by rw [hφ, hψ]; exact hK _ (lev_sc_mem hc hv hk)`.

Establish `e2 : φ x = 1` using `by rw [hφ, hψ, lev_sc_eq (x := x) hϖ]; exact hzx`. Establish `e3 : φ (x ^ k) = 1` using `zpow_mem (show x ∈ φ.ker from e2) k`. Rewrite `e1` using `[map_mul, e3, mul_one]`. Conclude with `e1`. Establish `hall` using `all_one ψ (fun t => hpos _ (lev_mem hc t)) h0 (one_add_ne hlt) hsc`.

Take `⟨t, X, hX, rfl⟩` from `decomp hc ha`. Establish `hr : 1 + -(ϖ * ϖ) ≠ 0` using `one_add_ne (by`. Rewrite using `[Valuation.map_neg, map_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left zero_le hlt hlt.le)`. Establish `hs : ∀ r : L, c r = r → (r • X).map c = -(r • X)ᵀ` using `fun r hr => by`.

Use extensionality with `i j`. Establish `: c (X i j) = -X j i` using `congrFun (congrFun hX i) j`. Simplify using `[hr, this]`. Use `set r := (1 + -(ϖ * ϖ))⁻¹ with hrd`. Establish `hcr : c r = r` using `by simp [hrd, hϖ]`.

Establish `m1` using `un_mem (hs r hcr)`. Establish `m2` using `un_mem (hs (ϖ * ϖ * r) (by simp [hcr, hϖ]))`. Establish `m3` using `un_mem hX`. Establish `e1` using `congrArg χ (zW_un x (r • X))`. Rewrite `e1` using `[smul_smul]`.

Establish `e2 : un (r • X) = un ((ϖ * ϖ * r) • X) * un X`. Rewrite using `[un_mul]`. Use `congr 1`. Establish `: r = ϖ * ϖ * r + 1`. Use `mul_inv_cancel₀ hr` as an intermediate fact.

Rewrite `this` using `[← hrd]`. Take the linear combination `this`. Use `conv_lhs => rw [this, add_smul, one_smul]`. Establish `e3 : χ (un (r • X)) = χ (un ((ϖ * ϖ * r) • X))`. Rewrite `e1` using `[hmul _ hzm _ m1, hzx, one_mul]`.

Rewrite using `[e1]`. Conclude with `(hmul _ m2 _ hzm).trans (by rw [hzx, mul_one])`. Rewrite `e3` using `[e2, hmul _ m2 _ m3]`. Establish `e4 : χ (un X) = 1` using `mul_left_cancel₀ (hpos _ m2).ne' (e3.trans (mul_one _).symm)`. Rewrite using `[hmul _ (lev_mem hc t) _ m3, e4, mul_one]`.

Conclude with `hall t`.
-/
theorem gen : GenSt := by
  intro L _ _ ϖ c q h m χ hmul hpos hK hz a ha
  obtain ⟨hc, hv, hϖ, hvϖ, -⟩ := h
  have hvϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hvϖ
  have hlt : Valued.v ϖ < 1 := by
    rw [hvϖ', ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have h0 : ϖ ≠ 0 := fun e => by
    rw [e, map_zero] at hvϖ'; exact WithZero.exp_ne_zero hvϖ'.symm
  let x : Lˣ := Units.mk0 ϖ h0
  have hzx : χ (zW L m x) = 1 := hz x rfl
  have hzm : zW L m x ∈ PW L c m := by rw [← lev_sc_eq (c := c) (x := x) hϖ]; exact lev_mem hc _
  let ψ : GL (Fin m) L →* ℝ :=
    { toFun := fun t => χ (lev L c m t)
      map_one' := by rw [map_one]; exact hK 1 (one_mem _)
      map_mul' := fun s t => by rw [map_mul]; exact hmul _ (lev_mem hc _) _ (lev_mem hc _) }
  have hψ : ∀ t, ψ t = χ (lev L c m t) := fun _ => rfl
  have hsc : ∀ u : Lˣ, ψ (dg fun _ => u) = 1 := by
    let φ : Lˣ →* ℝ := (ψ.comp dg).comp (Pi.constMonoidHom (Fin m) Lˣ)
    have hφ : ∀ u, φ u = ψ (dg fun _ => u) := fun _ => rfl
    intro u
    obtain ⟨k, hk⟩ := exists_unit (x := x) hvϖ' u
    have e1 : φ (u * x ^ k) = 1 := by rw [hφ, hψ]; exact hK _ (lev_sc_mem hc hv hk)
    have e2 : φ x = 1 := by rw [hφ, hψ, lev_sc_eq (x := x) hϖ]; exact hzx
    have e3 : φ (x ^ k) = 1 := zpow_mem (show x ∈ φ.ker from e2) k
    rw [map_mul, e3, mul_one] at e1
    exact e1
  have hall := all_one ψ (fun t => hpos _ (lev_mem hc t)) h0 (one_add_ne hlt) hsc
  obtain ⟨t, X, hX, rfl⟩ := decomp hc ha
  have hr : 1 + -(ϖ * ϖ) ≠ 0 := one_add_ne (by
    rw [Valuation.map_neg, map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hlt hlt.le)
  have hs : ∀ r : L, c r = r → (r • X).map c = -(r • X)ᵀ := fun r hr => by
    ext i j
    have : c (X i j) = -X j i := congrFun (congrFun hX i) j
    simp [hr, this]
  set r := (1 + -(ϖ * ϖ))⁻¹ with hrd
  have hcr : c r = r := by simp [hrd, hϖ]
  have m1 := un_mem (hs r hcr)
  have m2 := un_mem (hs (ϖ * ϖ * r) (by simp [hcr, hϖ]))
  have m3 := un_mem hX
  have e1 := congrArg χ (zW_un x (r • X))
  rw [smul_smul] at e1
  have e2 : un (r • X) = un ((ϖ * ϖ * r) • X) * un X := by
    rw [un_mul]
    congr 1
    have : r = ϖ * ϖ * r + 1 := by
      have := mul_inv_cancel₀ hr
      rw [← hrd] at this
      linear_combination this
    conv_lhs => rw [this, add_smul, one_smul]
  have e3 : χ (un (r • X)) = χ (un ((ϖ * ϖ * r) • X)) := by
    rw [hmul _ hzm _ m1, hzx, one_mul] at e1
    rw [e1]
    exact (hmul _ m2 _ hzm).trans (by rw [hzx, mul_one])
  rw [e2, hmul _ m2 _ m3] at e3
  have e4 : χ (un X) = 1 := mul_left_cancel₀ (hpos _ m2).ne' (e3.trans (mul_one _).symm)
  rw [hmul _ (lev_mem hc t) _ m3, e4, mul_one]
  exact hall t

end PositivityTheory.Sph.M2

end
