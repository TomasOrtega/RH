import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupExpTwoSidedInverseUniqueStatement

namespace GlobalTheory.FGDepth.Coord

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

noncomputable section

variable {C : Type} [Field C]

/- English proof (translation)
The claim follows from `hasSubst_of_constantCoeff_zero h`.
-/
theorem hs0 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (h : ∀ s, constantCoeff (a s) = 0) : HasSubst a := hasSubst_of_constantCoeff_zero h

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem cX {σ : Type} (s : σ) : constantCoeff (X s : MvPowerSeries σ C) = 0 := by simp

open MvPowerSeries in
/- English proof (translation)
Rewrite using `[← coe_substAlgHom hb, map_sum]`. Simplify using `only [map_smul, coe_substAlgHom, subst_X hb]`.
-/
private lemma subst_sum_smul_X' {C : Type} [Field C] {σ τ ι : Type} [Fintype ι]
    {b : σ → MvPowerSeries τ C} (hb : HasSubst b) (c : ι → C) (g : ι → σ) :
    subst b (∑ a, c a • (X (g a) : MvPowerSeries σ C)) = ∑ a, c a • b (g a) := by
  rw [← coe_substAlgHom hb, map_sum]
  simp only [map_smul, coe_substAlgHom, subst_X hb]

open MvPowerSeries in
/- English proof (translation)
Introduce `α`. Use `show 0 ≤ v (coeff α (X s : MvPowerSeries σ C))`. Rewrite using `[coeff_X]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private lemma mvIsInt_X_divisor {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {σ : Type}
    (s : σ) : _root_.ReciprocityTheory.PGsh.MvIsInt v (X s : MvPowerSeries σ C) := by
  classical
  intro α
  show 0 ≤ v (coeff α (X s : MvPowerSeries σ C))
  rw [coeff_X]
  split_ifs <;> simp

open MvPowerSeries in
variable {C : Type} [Field C] in

/- English proof (translation)
Introduce `C _ _ v i d c G u Φ Ψ hΦΨ hinv t ht0 ht`. Establish `hΦ : HasSubst Φ` using `hasSubst_of_constantCoeff_zero fun a => (hΦΨ a).2.1`. Establish `hΨ : HasSubst Ψ` using `hasSubst_of_constantCoeff_zero fun a => (hΦΨ a).2.2.2`. Establish `htS : HasSubst t` using `hasSubst_of_constantCoeff_zero ht0`. Establish `hlg : HasSubst G.lg` using `hasSubst_of_constantCoeff_zero G.2`.

Establish `hex0 : ∀ a, constantCoeff (_root_.GlobalTheory.FGDepth.expOf G a) = 0` using `(_root_.GlobalTheory.FGDepth.isExp_expOf G).1`. Establish `hexS : HasSubst (_root_.GlobalTheory.FGDepth.expOf G)` using `hasSubst_of_constantCoeff_zero hex0`. Establish `hLin0 : ∀ e, constantCoeff (∑ a, u a e • (X a : MvPowerSeries (Fin i) C)) = 0`. Introduce `e`. Simplify using `[map_sum]`.

Establish `hLinS : HasSubst fun e => ∑ a, u a e • (X a : MvPowerSeries (Fin i) C)` using `hasSubst_of_constantCoeff_zero hLin0`. Establish `hΦtS : HasSubst fun a => subst t (Φ a)` using `hasSubst_of_constantCoeff_zero fun a => constantCoeff_subst_eq_zero htS ht0 (hΦΨ a).2.1`. Establish `hΦt : ∀ a, subst t (Φ a) =`. Substitute `(fun e => ∑ b, u b e • (X b : MvPowerSeries (Fin i) C)) (_root_.GlobalTheory.FGDepth.expOf G a) := by` using the available equality. Introduce `a`.

Establish `h1 : (fun e => ∑ b, u b e • (X b : MvPowerSeries (Fin i) C)) = fun e => subst (fun a => subst t (Φ a)) (G.lg e)`. Use function extensionality and compare the values at `e`. Rewrite using `[← subst_comp_subst_apply hΦ htS, ht]`. Rewrite using `[h1, ← subst_comp_subst_apply hlg hΦtS, _root_.GlobalTheory.FGDepth.subst_lg_expOf, subst_X hΦtS]`. Establish `ht_eq : ∀ e, t e = subst (fun e => ∑ b, u b e • (X b : MvPowerSeries (Fin i) C)) (subst (_root_.GlobalTheory.FGDepth.expOf G) (Ψ e))`.

Introduce `e`. Rewrite using `[subst_comp_subst_apply hexS hLinS]`. Combine the equalities or inequalities in the displayed calculation. Establish `hXb : ∀ b : Fin i, HasSubst fun a : Fin i => (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)` using `fun b => hasSubst_of_constantCoeff_zero fun a => constantCoeff_X _`. Establish `hXd : ∀ b : Fin i, HasSubst fun a : Fin d => (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)` using `fun b => hasSubst_of_constantCoeff_zero fun a => constantCoeff_X _`.

Establish `hLinB0 : ∀ (b : Fin i) (e : Fin d), constantCoeff (∑ a, u a e • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) = 0`. Introduce `b e`. Simplify using `[map_sum]`. Establish `hLinBS : ∀ b : Fin i, HasSubst fun e => ∑ a, u a e • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)` using `fun b => hasSubst_of_constantCoeff_zero (hLinB0 b)`. Establish `hE0 : ∀ x, constantCoeff (_root_.GlobalTheory.FGDepth.expAlong (fun _ : Fin i => G) (fun _ : Fin i => u) x) = 0` using `fun x => constantCoeff_subst_eq_zero (hLinBS x.1) (hLinB0 x.1) (hex0 x.2)`.

Establish `hES : HasSubst (_root_.GlobalTheory.FGDepth.expAlong (fun _ : Fin i => G) (fun _ : Fin i => u))` using `hasSubst_of_constantCoeff_zero hE0`. Establish `hΨ0 : ∀ x : (Σ _ : Fin i, Fin d), constantCoeff (subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Ψ x.2)) = 0` using `fun x => constantCoeff_subst_eq_zero (hXd x.1) (fun a => constantCoeff_X _) (hΦΨ x.2).2.2.2`. Establish `hΨS : HasSubst fun x : (Σ _ : Fin i, Fin d) =>`. Substitute `(fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Ψ x.2) :=` using the available equality. Use `hasSubst_of_constantCoeff_zero hΨ0`.

Establish `hΦ0 : ∀ x : (Σ _ : Fin i, Fin d), constantCoeff (subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Φ x.2)) = 0` using `fun x => constantCoeff_subst_eq_zero (hXd x.1) (fun a => constantCoeff_X _) (hΦΨ x.2).2.1`. Establish `hΦS : HasSubst fun x : (Σ _ : Fin i, Fin d) =>`. Substitute `(fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Φ x.2) :=` using the available equality. Use `hasSubst_of_constantCoeff_zero hΦ0`. Establish `key : ∀ x : (Σ _ : Fin i, Fin d),`.

Substitute `(fun a : Fin i => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2) =` using the available equality. Substitute `(_root_.GlobalTheory.FGDepth.expAlong (fun _ : Fin i => G) (fun _ : Fin i => u)) (subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Ψ x.2)) := by` using the available equality. Introduce and unpack `⟨b, e⟩`. Establish `hlin : (fun e' => subst (fun a : Fin i => (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (∑ a, u a e' • (X a : MvPowerSeries (Fin i) C))) = fun e' => ∑ a, u a e' • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)`. Use function extensionality and compare the values at `e'`.

Conclude with `subst_sum_smul_X' (hXb b) (fun a => u a e') id`. Rewrite using `[ht_eq e, subst_comp_subst_apply hLinS (hXb b), hlin, subst_comp_subst_apply hexS (hLinBS b), subst_comp_subst_apply (hXd b) hES]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Rewrite using `[subst_X hES]`.

Both sides reduce to the same expression. Establish `hround : (fun x : (Σ _ : Fin i, Fin d) => subst (fun x : (Σ _ : Fin i, Fin d) =>`. Substitute `(fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Ψ x.2))` using the available equality. Use the proof step `(subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Φ x.2))) =`. Use `X := by`.

Use function extensionality and compare the values at `x`. Rewrite using `[subst_comp_subst_apply (hXd x.1) hΨS]`. Repeatedly rewrite using `[subst_X hΨS]`. Rewrite using `[← subst_comp_subst_apply hΨ (hXd x.1), (hinv x.2).1, subst_X (hXd x.1)]`. Unfold `_root_.GlobalTheory.FGDepth.detDepth _root_.GlobalTheory.FGDepth.depth`.

Repeatedly rewrite using `[key]`. Apply `le_antisymm` to reduce the goal to its premises. Use `le_iInf fun f => ?_` and prove the remaining obligations. Rewrite using `[← subst_comp_subst_apply hΨS hES]`. Conclude with `iInf_le_of_le ⟨_, _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v f.2 (fun x => _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (hΦΨ x.2).2.2.1 (fun a => mvIsInt_X_divisor v _) (fun a => constantCoeff_X _)) hΨ0⟩ le_rfl`.

Use `le_iInf fun f => ?_` and prove the remaining obligations. Use `iInf_le_of_le ⟨_, _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v f.2 (fun x => _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (hΦΨ x.2).1 (fun a => mvIsInt_X_divisor v _) (fun a => constantCoeff_X _)) hΦ0⟩ ?_` and prove the remaining obligations. Rewrite using `[← subst_comp_subst_apply hΨS hES, subst_comp_subst_apply hΦS hΨS, hround, subst_self]`. Both sides reduce to the same expression.
-/
theorem _root_.GlobalTheory.FGDepth.Coord.depth_in_coords : ∀ (C : Type) [Field C] [CharZero C]
    (v : AddValuation C (WithTop ℝ)) (i d c : ℕ) (G : _root_.ReciprocityTheory.PGsh.LogFGL v d) (u : Fin i → Fin d → C)
    (Φ Ψ : Fin d → MvPowerSeries (Fin d) C),
    (∀ a, _root_.ReciprocityTheory.PGsh.MvIsInt v (Φ a) ∧ constantCoeff (Φ a) = 0 ∧ _root_.ReciprocityTheory.PGsh.MvIsInt v (Ψ a) ∧
      constantCoeff (Ψ a) = 0) →
    (∀ a, subst Ψ (Φ a) = X a ∧ subst Φ (Ψ a) = X a) →
    ∀ (t : Fin d → MvPowerSeries (Fin i) C), (∀ a, constantCoeff (t a) = 0) →
    (∀ e, subst t (subst Φ (G.lg e)) = ∑ a, u a e • X a) →
    _root_.GlobalTheory.FGDepth.detDepth G u c = ⨅ f : {f : MvPowerSeries (Σ _ : Fin i, Fin d) C //
      _root_.ReciprocityTheory.PGsh.MvIsInt v f}, _root_.GlobalTheory.FGDepth.toE (v (_root_.GlobalTheory.FGDepth.derivAt0
        (_root_.GlobalTheory.FGDepth.detPow C i c) (subst (fun x : (Σ _ : Fin i, Fin d) =>
          subst (fun a : Fin i => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2))
            f.1))) := by
  intro C _ _ v i d c G u Φ Ψ hΦΨ hinv t ht0 ht
  have hΦ : HasSubst Φ := hasSubst_of_constantCoeff_zero fun a => (hΦΨ a).2.1
  have hΨ : HasSubst Ψ := hasSubst_of_constantCoeff_zero fun a => (hΦΨ a).2.2.2
  have htS : HasSubst t := hasSubst_of_constantCoeff_zero ht0
  have hlg : HasSubst G.lg := hasSubst_of_constantCoeff_zero G.2
  have hex0 : ∀ a, constantCoeff (_root_.GlobalTheory.FGDepth.expOf G a) = 0 := (_root_.GlobalTheory.FGDepth.isExp_expOf G).1
  have hexS : HasSubst (_root_.GlobalTheory.FGDepth.expOf G) := hasSubst_of_constantCoeff_zero hex0
  have hLin0 : ∀ e, constantCoeff (∑ a, u a e • (X a : MvPowerSeries (Fin i) C)) = 0 := by
    intro e
    simp [map_sum]
  have hLinS : HasSubst fun e => ∑ a, u a e • (X a : MvPowerSeries (Fin i) C) :=
    hasSubst_of_constantCoeff_zero hLin0
  have hΦtS : HasSubst fun a => subst t (Φ a) :=
    hasSubst_of_constantCoeff_zero fun a => constantCoeff_subst_eq_zero htS ht0 (hΦΨ a).2.1

  have hΦt : ∀ a, subst t (Φ a) =
      subst (fun e => ∑ b, u b e • (X b : MvPowerSeries (Fin i) C))
        (_root_.GlobalTheory.FGDepth.expOf G a) := by
    intro a
    have h1 : (fun e => ∑ b, u b e • (X b : MvPowerSeries (Fin i) C)) =
        fun e => subst (fun a => subst t (Φ a)) (G.lg e) := by
      funext e
      rw [← subst_comp_subst_apply hΦ htS, ht]
    rw [h1, ← subst_comp_subst_apply hlg hΦtS, _root_.GlobalTheory.FGDepth.subst_lg_expOf, subst_X hΦtS]
  have ht_eq : ∀ e, t e = subst (fun e => ∑ b, u b e • (X b : MvPowerSeries (Fin i) C))
      (subst (_root_.GlobalTheory.FGDepth.expOf G) (Ψ e)) := by
    intro e
    rw [subst_comp_subst_apply hexS hLinS]
    calc t e = subst t (X e) := (subst_X htS e).symm
      _ = subst t (subst Φ (Ψ e)) := by rw [(hinv e).2]
      _ = subst (fun a => subst t (Φ a)) (Ψ e) := subst_comp_subst_apply hΦ htS _
      _ = _ := by simp_rw [hΦt]

  have hXb : ∀ b : Fin i, HasSubst fun a : Fin i =>
      (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C) :=
    fun b => hasSubst_of_constantCoeff_zero fun a => constantCoeff_X _
  have hXd : ∀ b : Fin i, HasSubst fun a : Fin d =>
      (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C) :=
    fun b => hasSubst_of_constantCoeff_zero fun a => constantCoeff_X _
  have hLinB0 : ∀ (b : Fin i) (e : Fin d),
      constantCoeff (∑ a, u a e • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) = 0 := by
    intro b e
    simp [map_sum]
  have hLinBS : ∀ b : Fin i, HasSubst fun e =>
      ∑ a, u a e • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C) :=
    fun b => hasSubst_of_constantCoeff_zero (hLinB0 b)
  have hE0 : ∀ x, constantCoeff
      (_root_.GlobalTheory.FGDepth.expAlong (fun _ : Fin i => G) (fun _ : Fin i => u) x) = 0 :=
    fun x => constantCoeff_subst_eq_zero (hLinBS x.1) (hLinB0 x.1) (hex0 x.2)
  have hES : HasSubst
      (_root_.GlobalTheory.FGDepth.expAlong (fun _ : Fin i => G) (fun _ : Fin i => u)) :=
    hasSubst_of_constantCoeff_zero hE0
  have hΨ0 : ∀ x : (Σ _ : Fin i, Fin d), constantCoeff
      (subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Ψ x.2)) = 0 :=
    fun x => constantCoeff_subst_eq_zero (hXd x.1) (fun a => constantCoeff_X _) (hΦΨ x.2).2.2.2
  have hΨS : HasSubst fun x : (Σ _ : Fin i, Fin d) =>
      subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Ψ x.2) :=
    hasSubst_of_constantCoeff_zero hΨ0
  have hΦ0 : ∀ x : (Σ _ : Fin i, Fin d), constantCoeff
      (subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Φ x.2)) = 0 :=
    fun x => constantCoeff_subst_eq_zero (hXd x.1) (fun a => constantCoeff_X _) (hΦΨ x.2).2.1
  have hΦS : HasSubst fun x : (Σ _ : Fin i, Fin d) =>
      subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Φ x.2) :=
    hasSubst_of_constantCoeff_zero hΦ0

  have key : ∀ x : (Σ _ : Fin i, Fin d),
      subst (fun a : Fin i => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2) =
      subst (_root_.GlobalTheory.FGDepth.expAlong (fun _ : Fin i => G) (fun _ : Fin i => u))
        (subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C))
          (Ψ x.2)) := by
    rintro ⟨b, e⟩
    have hlin : (fun e' => subst (fun a : Fin i =>
        (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C))
          (∑ a, u a e' • (X a : MvPowerSeries (Fin i) C))) =
        fun e' => ∑ a, u a e' • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C) := by
      funext e'
      exact subst_sum_smul_X' (hXb b) (fun a => u a e') id
    rw [ht_eq e, subst_comp_subst_apply hLinS (hXb b), hlin,
      subst_comp_subst_apply hexS (hLinBS b), subst_comp_subst_apply (hXd b) hES]
    congr 1
    funext a
    rw [subst_X hES]
    rfl

  have hround : (fun x : (Σ _ : Fin i, Fin d) => subst
      (fun x : (Σ _ : Fin i, Fin d) =>
        subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Ψ x.2))
      (subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Φ x.2))) =
      X := by
    funext x
    rw [subst_comp_subst_apply (hXd x.1) hΨS]
    simp_rw [subst_X hΨS]
    rw [← subst_comp_subst_apply hΨ (hXd x.1), (hinv x.2).1, subst_X (hXd x.1)]
  unfold _root_.GlobalTheory.FGDepth.detDepth _root_.GlobalTheory.FGDepth.depth
  simp_rw [key]
  apply le_antisymm
  · refine le_iInf fun f => ?_
    rw [← subst_comp_subst_apply hΨS hES]
    exact iInf_le_of_le ⟨_, _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v f.2
      (fun x => _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (hΦΨ x.2).2.2.1 (fun a => mvIsInt_X_divisor v _) (fun a => constantCoeff_X _))
      hΨ0⟩ le_rfl
  · refine le_iInf fun f => ?_
    refine iInf_le_of_le ⟨_, _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v f.2
      (fun x => _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (hΦΨ x.2).1 (fun a => mvIsInt_X_divisor v _) (fun a => constantCoeff_X _))
      hΦ0⟩ ?_
    rw [← subst_comp_subst_apply hΨS hES, subst_comp_subst_apply hΦS hΨS, hround, subst_self]
    rfl

end

end GlobalTheory.FGDepth.Coord
