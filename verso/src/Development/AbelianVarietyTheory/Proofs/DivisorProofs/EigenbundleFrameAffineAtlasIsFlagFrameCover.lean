import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

namespace GlobalTheory.FlagMod.FieldFlag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Use `h (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_))` and prove the remaining obligations. Use `congrArg Subtype.val (hc a)` as an intermediate fact. Simplify `this` using `[embK, embF]`.
-/
theorem exists_embK_ne {σ σ' : E →+* ℂ} (h : σ ≠ σ') : ∃ a : 𝓞 E, embK c σ a ≠ embK c σ' a := by
  by_contra hc
  push_neg at hc
  refine h (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_))
  have := congrArg Subtype.val (hc a)
  simpa [embK, embF] using this

/- English proof (translation)
Take `⟨ρ, hρ⟩` from `GlobalTheory.Reg.MChart.exists_ringHom_rho E H Dw l Xo c c.F (RingHom.id c.F) Y M`. Use `letI : Algebra c.F Γ(Y.X, M.U) := (str (tau M.hU)).toAlgebra`. Establish `hP : ∀ τ, LowRank.pm p M τ = ∑ k, algebraMap c.F Γ(Y.X, M.U) (RingHom.id c.F (p.κ τ k)) • ρ (p.a τ k)` using `fun τ => by simp only [LowRank.pm, hρ]; rfl`. Take `⟨a, ha⟩` from `exists_embK_ne (c := c) h`. Establish `h1` using `(p.spec σ Γ(Y.X, M.U) M.n ρ).1 a`.

Establish `h1'` using `(p.spec σ' Γ(Y.X, M.U) M.n ρ).1 a`. Rewrite `h1`, `h1'` using `[← hP]`. Establish `hc : ρ a * LowRank.pm p M σ = LowRank.pm p M σ * ρ a`. Rewrite using `[hP, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, ← map_mul, ← map_mul, mul_comm]`. Establish `e1 : ρ a * (LowRank.pm p M σ * LowRank.pm p M σ') = algebraMap c.F Γ(Y.X, M.U) (embK c σ a) • (LowRank.pm p M σ * LowRank.pm p M σ')`. Rewrite using `[← Matrix.mul_assoc, h1, Matrix.smul_mul]`. Establish `e2 : ρ a * (LowRank.pm p M σ * LowRank.pm p M σ') = algebraMap c.F Γ(Y.X, M.U) (embK c σ' a) • (LowRank.pm p M σ * LowRank.pm p M σ')`. Rewrite using `[← Matrix.mul_assoc, hc, Matrix.mul_assoc, h1', Matrix.mul_smul]`.

Establish `hd : embK c σ a - embK c σ' a ≠ 0` using `sub_ne_zero.2 ha`. Establish `e3 : algebraMap c.F Γ(Y.X, M.U) (embK c σ a - embK c σ' a) • (LowRank.pm p M σ * LowRank.pm p M σ') = 0`. Rewrite using `[map_sub, sub_smul, ← e1, ← e2, sub_self]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[inv_mul_cancel₀ hd, map_one, one_smul]`.

Use `_ = 0 := by rw [map_mul, mul_smul, e3, smul_zero]`.
-/
theorem pm_mul_pm {Y : Model Xo c (RingHom.id c.F)} (p : Proj (RingHom.id c.F)) (M : MChart Y) {σ σ' : E →+* ℂ}
    (h : σ ≠ σ') : LowRank.pm p M σ * LowRank.pm p M σ' = 0 := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.Reg.MChart.exists_ringHom_rho E H Dw l Xo c c.F (RingHom.id c.F) Y M
  letI : Algebra c.F Γ(Y.X, M.U) := (str (tau M.hU)).toAlgebra
  have hP : ∀ τ, LowRank.pm p M τ =
      ∑ k, algebraMap c.F Γ(Y.X, M.U) (RingHom.id c.F (p.κ τ k)) • ρ (p.a τ k) :=
    fun τ => by simp only [LowRank.pm, hρ]; rfl
  obtain ⟨a, ha⟩ := exists_embK_ne (c := c) h
  have h1 := (p.spec σ Γ(Y.X, M.U) M.n ρ).1 a
  have h1' := (p.spec σ' Γ(Y.X, M.U) M.n ρ).1 a
  rw [← hP] at h1 h1'
  have hc : ρ a * LowRank.pm p M σ = LowRank.pm p M σ * ρ a := by
    rw [hP, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, ← map_mul, ← map_mul, mul_comm]
  have e1 : ρ a * (LowRank.pm p M σ * LowRank.pm p M σ') =
      algebraMap c.F Γ(Y.X, M.U) (embK c σ a) • (LowRank.pm p M σ * LowRank.pm p M σ') := by
    rw [← Matrix.mul_assoc, h1, Matrix.smul_mul]
  have e2 : ρ a * (LowRank.pm p M σ * LowRank.pm p M σ') =
      algebraMap c.F Γ(Y.X, M.U) (embK c σ' a) • (LowRank.pm p M σ * LowRank.pm p M σ') := by
    rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc, h1', Matrix.mul_smul]
  have hd : embK c σ a - embK c σ' a ≠ 0 := sub_ne_zero.2 ha
  have e3 : algebraMap c.F Γ(Y.X, M.U) (embK c σ a - embK c σ' a) •
      (LowRank.pm p M σ * LowRank.pm p M σ') = 0 := by
    rw [map_sub, sub_smul, ← e1, ← e2, sub_self]
  calc LowRank.pm p M σ * LowRank.pm p M σ'
      = algebraMap c.F Γ(Y.X, M.U) ((embK c σ a - embK c σ' a)⁻¹ * (embK c σ a - embK c σ' a)) •
        (LowRank.pm p M σ * LowRank.pm p M σ') := by
        rw [inv_mul_cancel₀ hd, map_one, one_smul]
    _ = 0 := by rw [map_mul, mul_smul, e3, smul_zero]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[k.wu, k.wu, Matrix.one_mul, Matrix.mul_one]`. Use `_ = k.w σ * ((k.u σ * k.w σ) * (k.u σ' * k.w σ')) * k.u σ' := by simp only [Matrix.mul_assoc]`. Use `_ = 0 := by`. Rewrite using `[k.uw, k.uw, ← Matrix.map_mul, pm_mul_pm p _ h, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul]`.
-/
theorem eCh_w_mul_u {Y : Model Xo c (RingHom.id c.F)} {p : Proj (RingHom.id c.F)} (k : ECh Y p) {σ σ' : E →+* ℂ}
    (h : σ ≠ σ') : k.w σ * k.u σ' = 0 := by
  calc k.w σ * k.u σ' = (k.w σ * k.u σ) * k.w σ * (k.u σ' * (k.w σ' * k.u σ')) := by
        rw [k.wu, k.wu, Matrix.one_mul, Matrix.mul_one]
    _ = k.w σ * ((k.u σ * k.w σ) * (k.u σ' * k.w σ')) * k.u σ' := by simp only [Matrix.mul_assoc]
    _ = 0 := by
        rw [k.uw, k.uw, ← Matrix.map_mul, pm_mul_pm p _ h, Matrix.map_zero _ (map_zero _), Matrix.mul_zero,
          Matrix.zero_mul]

end GlobalTheory.FlagMod.FieldFlag

open GlobalTheory.FlagMod.FieldFlag MonoidalCategory CartesianMonoidalCategory MonObj in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c Y p A`. Use `⟨fun b => ?_, fun b => ?_, fun k _ b b' φ φ' hx => ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.comp_id]`. Conclude with `(spMap_ev_top (tau (A.aff b) ≫ Y.s)).symm`. Introduce and unpack `⟨σ, i⟩ ⟨σ', j⟩`.

Establish `e : ∑ r, A.Dv b ⟨σ, i⟩ r * A.cv b ⟨σ', j⟩ r = ((A.k b).w σ * (A.k b).u σ') i j`. Establish `: (A.k b).w σ * (A.k b).u σ' = ((A.k b).w σ * A.C b) * (A.A b * (A.k b).u σ')`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (A.C b), A.CA, Matrix.one_mul]`. Rewrite using `[this, Matrix.mul_apply]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Distinguish the cases in `hs : σ = σ'`. Substitute `hs` using the available equality. Rewrite using `[(A.k b).wu]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Matrix.one_apply_ne hij, if_neg]`. Introduce `h'`. Conclude with `hij (eq_of_heq (Sigma.mk.inj_iff.1 h').2)`.

Rewrite using `[eCh_w_mul_u _ hs, Matrix.zero_apply, if_neg]`. Introduce `h'`. Conclude with `hs (congrArg Sigma.fst h')`. Establish `h0 : ⊤ ≤ (spMap φ ≫ (A.V b).2.fromSpec) ⁻¹ᵁ (A.k b).V` using `le_preimage_comp _ (tau_le (A.aff b) le_rfl)`. Establish `h0' : ⊤ ≤ (spMap φ' ≫ (A.V b').2.fromSpec) ⁻¹ᵁ (A.k b').V` using `le_preimage_comp _ (tau_le (A.aff b') le_rfl)`.

Use `set x := spMap φ ≫ (A.V b).2.fromSpec with hxdef`. Establish `h : ⊤ ≤ x ⁻¹ᵁ (A.k b).V` using `h0`. Establish `h' : ⊤ ≤ x ⁻¹ᵁ (A.k b').V` using `hx ▸ h0'`. Establish `hφ : ev x _ h = φ` using `ev_spMap_tau (A.aff b) φ h`. Establish `hφ' : ev x _ h' = φ'` using `(ev_congr hx _ h' h0').trans (ev_spMap_tau (A.aff b') φ' h0')`.

Establish `hM : ⊤ ≤ x ⁻¹ᵁ (A.k b).M.U` using `le_preimage_mono (A.k b).le h`. Establish `hM' : ⊤ ≤ x ⁻¹ᵁ (A.k b').M.U` using `le_preimage_mono (A.k b').le h'`. Establish `hMM : ⊤ ≤ x ⁻¹ᵁ ((A.k b).M.U ⊓ (A.k b').M.U)` using `le_preimage_inf hM hM'`. Take `⟨a, ha⟩` from `A.tw k x b' b h' h hMM`. Introduce and unpack `⟨σ, j⟩`.

Use `set v : Fin (A.k b').M.n → k := (((A.k b').u σ).map (ev x _ h')).mulVec (Pi.single j 1) with hvdef`. Use `set y := ((chg (A.k b).M.toMChart (A.k b').M.toMChart).map (ev x _ hMM)).mulVec v with hydef`. Establish `hv : ((LowRank.pm p (A.k b').M.toMChart σ).map (ev x _ hM')).mulVec v = v` using `((A.k b').fix_iff σ x h' hM' v).2 ⟨_, rfl⟩`. Establish `hy : ((LowRank.pm p (A.k b).M.toMChart σ).map (ev x _ hM)).mulVec y = y`. Establish `h2` using `congrArg (vec (A.k b').M.toMChart x hM') hv`.

Rewrite `h2` using `[LowRank.vec_pm, ← vec_chg (A.k b).M.toMChart (A.k b').M.toMChart x hM hM' hMM, ← LowRank.vec_pm]`. Conclude with `(vec _ _ _).injective h2`. Take `⟨t, ht⟩` from `((A.k b).fix_iff σ x h hM y).1 hy`. Establish `key : φ' ∘ A.cv b' ⟨σ, j⟩ = ((a : k) • ((A.A b).map φ * ((A.k b).u σ).map φ)).mulVec t`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hφ']`. Use function extensionality and compare the values at `r`. Rewrite using `[Matrix.mulVec_single_one, ← Matrix.map_mul]`. Both sides reduce to the same expression. Use `_ = (a : k) • ((A.A b).map (ev x _ h)).mulVec y := by`.

Rewrite using `[← Matrix.mulVec_mulVec, ha, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]`. Use `_ = (a : k) • ((A.A b).map φ * ((A.k b).u σ).map φ).mulVec t := by`. Rewrite using `[← ht, Matrix.mulVec_mulVec, hφ]`. Use `_ = _ := (Matrix.smul_mulVec _ _ _).symm`. Establish `col : ∀ i, φ ∘ A.cv b ⟨σ, i⟩ = fun r => ((A.A b).map φ * ((A.k b).u σ).map φ) r i` using `fun i => by`.

Use function extensionality and compare the values at `r`. Rewrite using `[← Matrix.map_mul]`. Both sides reduce to the same expression. Establish `hsum : ((a : k) • ((A.A b).map φ * ((A.k b).u σ).map φ)).mulVec t = ∑ i, ((a : k) * t i) • fun r => ((A.A b).map φ * ((A.k b).u σ).map φ) r i`. Use function extensionality and compare the values at `r`.

Simplify using `only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun i _ => by ring` and prove the remaining obligations. Use `show φ' ∘ A.cv b' ⟨σ, j⟩ ∈ Submodule.span k (Set.range fun i => φ ∘ A.cv b ⟨σ, i⟩)`. Rewrite using `[key, hsum]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, col i⟩)`.
-/
theorem GlobalTheory.FlagMod.FieldFlag.atlas_isCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p), IsCover (RingHom.id c.F) Y.s A.V A.alpha A.cv A.Dv := by
  intro E _ _ _ H Dw l Xo c Y p A
  classical
  refine ⟨fun b => ?_, fun b => ?_, fun k _ b b' φ φ' hx => ?_⟩
  · rw [RingHom.comp_id]
    exact (spMap_ev_top (tau (A.aff b) ≫ Y.s)).symm
  · rintro ⟨σ, i⟩ ⟨σ', j⟩
    have e : ∑ r, A.Dv b ⟨σ, i⟩ r * A.cv b ⟨σ', j⟩ r = ((A.k b).w σ * (A.k b).u σ') i j := by
      have : (A.k b).w σ * (A.k b).u σ' = ((A.k b).w σ * A.C b) * (A.A b * (A.k b).u σ') := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A.C b), A.CA, Matrix.one_mul]
      rw [this, Matrix.mul_apply]
      rfl
    rw [e]
    by_cases hs : σ = σ'
    · subst hs
      rw [(A.k b).wu]
      by_cases hij : i = j
      · subst hij; simp
      · rw [Matrix.one_apply_ne hij, if_neg]
        intro h'
        exact hij (eq_of_heq (Sigma.mk.inj_iff.1 h').2)
    · rw [eCh_w_mul_u _ hs, Matrix.zero_apply, if_neg]
      intro h'
      exact hs (congrArg Sigma.fst h')
  · have h0 : ⊤ ≤ (spMap φ ≫ (A.V b).2.fromSpec) ⁻¹ᵁ (A.k b).V := le_preimage_comp _ (tau_le (A.aff b) le_rfl)
    have h0' : ⊤ ≤ (spMap φ' ≫ (A.V b').2.fromSpec) ⁻¹ᵁ (A.k b').V :=
      le_preimage_comp _ (tau_le (A.aff b') le_rfl)
    set x := spMap φ ≫ (A.V b).2.fromSpec with hxdef
    have h : ⊤ ≤ x ⁻¹ᵁ (A.k b).V := h0
    have h' : ⊤ ≤ x ⁻¹ᵁ (A.k b').V := hx ▸ h0'
    have hφ : ev x _ h = φ := ev_spMap_tau (A.aff b) φ h
    have hφ' : ev x _ h' = φ' := (ev_congr hx _ h' h0').trans (ev_spMap_tau (A.aff b') φ' h0')
    have hM : ⊤ ≤ x ⁻¹ᵁ (A.k b).M.U := le_preimage_mono (A.k b).le h
    have hM' : ⊤ ≤ x ⁻¹ᵁ (A.k b').M.U := le_preimage_mono (A.k b').le h'
    have hMM : ⊤ ≤ x ⁻¹ᵁ ((A.k b).M.U ⊓ (A.k b').M.U) := le_preimage_inf hM hM'
    obtain ⟨a, ha⟩ := A.tw k x b' b h' h hMM
    rintro ⟨σ, j⟩
    set v : Fin (A.k b').M.n → k := (((A.k b').u σ).map (ev x _ h')).mulVec (Pi.single j 1) with hvdef
    set y := ((chg (A.k b).M.toMChart (A.k b').M.toMChart).map (ev x _ hMM)).mulVec v with hydef
    have hv : ((LowRank.pm p (A.k b').M.toMChart σ).map (ev x _ hM')).mulVec v = v :=
      ((A.k b').fix_iff σ x h' hM' v).2 ⟨_, rfl⟩
    have hy : ((LowRank.pm p (A.k b).M.toMChart σ).map (ev x _ hM)).mulVec y = y := by
      have h2 := congrArg (vec (A.k b').M.toMChart x hM') hv
      rw [LowRank.vec_pm, ← vec_chg (A.k b).M.toMChart (A.k b').M.toMChart x hM hM' hMM, ← LowRank.vec_pm] at h2
      exact (vec _ _ _).injective h2
    obtain ⟨t, ht⟩ := ((A.k b).fix_iff σ x h hM y).1 hy
    have key : φ' ∘ A.cv b' ⟨σ, j⟩ = ((a : k) • ((A.A b).map φ * ((A.k b).u σ).map φ)).mulVec t := by
      calc φ' ∘ A.cv b' ⟨σ, j⟩
          = ((A.A b').map (ev x _ h') * ((A.k b').u σ).map (ev x _ h')).mulVec (Pi.single j 1) := by
            rw [hφ']
            funext r
            rw [Matrix.mulVec_single_one, ← Matrix.map_mul]
            rfl
        _ = (a : k) • ((A.A b).map (ev x _ h)).mulVec y := by
            rw [← Matrix.mulVec_mulVec, ha, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
        _ = (a : k) • ((A.A b).map φ * ((A.k b).u σ).map φ).mulVec t := by
            rw [← ht, Matrix.mulVec_mulVec, hφ]
        _ = _ := (Matrix.smul_mulVec _ _ _).symm
    have col : ∀ i, φ ∘ A.cv b ⟨σ, i⟩ = fun r => ((A.A b).map φ * ((A.k b).u σ).map φ) r i := fun i => by
      funext r
      rw [← Matrix.map_mul]
      rfl
    have hsum : ((a : k) • ((A.A b).map φ * ((A.k b).u σ).map φ)).mulVec t =
        ∑ i, ((a : k) * t i) • fun r => ((A.A b).map φ * ((A.k b).u σ).map φ) r i := by
      funext r
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => by ring
    show φ' ∘ A.cv b' ⟨σ, j⟩ ∈ Submodule.span k (Set.range fun i => φ ∘ A.cv b ⟨σ, i⟩)
    rw [key, hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, col i⟩)
