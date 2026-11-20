import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SameParahoric

open Filter Topology

/- English proof (translation)
Use `(s.v.denseRange_algebraMap (maximalRealSubfield L)).mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `⟨algebraMap (maximalRealSubfield L) L y, s.i.commutes y⟩`.
-/
theorem denseRange_i {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) :
    DenseRange (s.i : L → s.v.adicCompletion (maximalRealSubfield L)) := by
  refine (s.v.denseRange_algebraMap (maximalRealSubfield L)).mono ?_
  rintro _ ⟨y, rfl⟩
  exact ⟨algebraMap (maximalRealSubfield L) L y, s.i.commutes y⟩

/- English proof (translation)
Take `⟨z, hz⟩` from `s.v.valuedAdicCompletion_surjective (maximalRealSubfield L) (WithZero.exp (-(N : ℤ)))`. Establish `hξo : GlobalTheory.SmGL.IsSmoothChar ξ`. Establish `hU : IsOpen {x : (s.v.adicCompletion (maximalRealSubfield L))ˣ | Valued.v ((x : s.v.adicCompletion (maximalRealSubfield L)) - 1) < Valued.v z}`. Establish `h1` using `(Valued.isOpen_ball (s.v.adicCompletion (maximalRealSubfield L)) (Valued.v.restrict z)).preimage (Units.continuous_val.sub (continuous_const (y := (1 : s.v.adicCompletion (maximalRealSubfield L)))))`. Simplify `h1` using `only [Set.preimage_setOf_eq, Valuation.restrict_lt_iff, Pi.sub_apply]`.

Use `Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hU.mem_nhds ?_) fun x hx => ?_)` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, Units.val_one, sub_self, map_zero, hz]`. Conclude with `WithZero.exp_pos`. Establish `hx' : Valued.v ((x : s.v.adicCompletion (maximalRealSubfield L)) - 1) < Valued.v z` using `hx`. Conclude with `hN x (by rw [← hz]; exact hx'.le)`.

Establish `hcu : Continuous (Units.map c.toRingHom.toMonoidHom : (s.v.adicCompletion (maximalRealSubfield L))ˣ → (s.w.adicCompletion L)ˣ)`. Rewrite using `[Units.continuous_iff]`. Conclude with `⟨hc.comp Units.continuous_val, hc.comp Units.continuous_coe_inv⟩`. Establish `hs` using `hξo.mul (hμ.comp _ hcu).inv`. Establish `hcl` using `Subgroup.isClosed_of_isOpen _ hs`.

Use `mul_inv_eq_one.1 ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hy`. Take `⟨U, hU, hU'⟩` from `Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hcl.isOpen_compl`. Establish `hyU : (d : s.v.adicCompletion (maximalRealSubfield L)) ∈ U`. Establish `: d ∈ Units.val ⁻¹' U` using `by rw [hU']; exact hy`.

Conclude with `this`. Take `⟨k, hk1, hk2⟩` from `(denseRange_i s).exists_mem_open (hU.inter isOpen_ne (t := {z | z ≠ 0})) ⟨d, hyU, d.ne_zero⟩`. Establish `hk0 : k ≠ 0` using `fun e => hk2 (by rw [e, map_zero])`. Establish `h3 : Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) (Units.mk0 k hk0) ∈ Units.val ⁻¹' U` using `hk1`. Rewrite `h3` using `[hU']`.

Use `h3 ?_` and prove the remaining obligations. Establish `hm : Units.map c.toRingHom.toMonoidHom (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) (Units.mk0 k hk0)) = Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom (Units.mk0 k hk0)` using `Units.ext (hci k)`. Use `show ξ _ * (μ (Units.map c.toRingHom.toMonoidHom _))⁻¹ = 1`. Rewrite using `[hm, ← hglob]`. Conclude with `mul_inv_cancel _`.
-/
theorem eq_comp {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L)
    (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ) (μ : (s.w.adicCompletion L)ˣ →* ℂˣ)
    (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hc : Continuous c)
    (hci : ∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) (hμ : GlobalTheory.SmGL.IsSmoothChar μ) (N : ℕ)
    (hN : ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ,
      Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1)
    (hglob : ∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k) =
      μ (Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k))
    (d : (s.v.adicCompletion (maximalRealSubfield L))ˣ) :
    ξ d = μ (Units.map c.toRingHom.toMonoidHom d) := by
  obtain ⟨z, hz⟩ := s.v.valuedAdicCompletion_surjective (maximalRealSubfield L) (WithZero.exp (-(N : ℤ)))
  have hξo : GlobalTheory.SmGL.IsSmoothChar ξ := by
    have hU : IsOpen {x : (s.v.adicCompletion (maximalRealSubfield L))ˣ |
        Valued.v ((x : s.v.adicCompletion (maximalRealSubfield L)) - 1) < Valued.v z} := by
      have h1 := (Valued.isOpen_ball (s.v.adicCompletion (maximalRealSubfield L)) (Valued.v.restrict z)).preimage
        (Units.continuous_val.sub (continuous_const (y := (1 : s.v.adicCompletion (maximalRealSubfield L)))))
      simpa only [Set.preimage_setOf_eq, Valuation.restrict_lt_iff, Pi.sub_apply] using h1
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hU.mem_nhds ?_) fun x hx => ?_)
    · simp only [Set.mem_setOf_eq, Units.val_one, sub_self, map_zero, hz]
      exact WithZero.exp_pos
    · have hx' : Valued.v ((x : s.v.adicCompletion (maximalRealSubfield L)) - 1) < Valued.v z := hx
      exact hN x (by rw [← hz]; exact hx'.le)
  have hcu : Continuous (Units.map c.toRingHom.toMonoidHom :
      (s.v.adicCompletion (maximalRealSubfield L))ˣ → (s.w.adicCompletion L)ˣ) := by
    rw [Units.continuous_iff]
    exact ⟨hc.comp Units.continuous_val, hc.comp Units.continuous_coe_inv⟩
  have hs := hξo.mul (hμ.comp _ hcu).inv
  have hcl := Subgroup.isClosed_of_isOpen _ hs
  refine mul_inv_eq_one.1 ?_
  by_contra hy
  obtain ⟨U, hU, hU'⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hcl.isOpen_compl
  have hyU : (d : s.v.adicCompletion (maximalRealSubfield L)) ∈ U := by
    have : d ∈ Units.val ⁻¹' U := by rw [hU']; exact hy
    exact this
  obtain ⟨k, hk1, hk2⟩ := (denseRange_i s).exists_mem_open
    (hU.inter isOpen_ne (t := {z | z ≠ 0})) ⟨d, hyU, d.ne_zero⟩
  have hk0 : k ≠ 0 := fun e => hk2 (by rw [e, map_zero])
  have h3 : Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) (Units.mk0 k hk0) ∈ Units.val ⁻¹' U := hk1
  rw [hU'] at h3
  refine h3 ?_
  have hm : Units.map c.toRingHom.toMonoidHom
      (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) (Units.mk0 k hk0)) =
      Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom (Units.mk0 k hk0) := Units.ext (hci k)
  show ξ _ * (μ (Units.map c.toRingHom.toMonoidHom _))⁻¹ = 1
  rw [hm, ← hglob]
  exact mul_inv_cancel _

/- English proof (translation)
Introduce `L _ _ _ s r t W _ _ π ξ μ c hc hci hμ ⟨N, hN⟩ hglob u hvec`. Establish `hE` using `GlobalTheory.ConjParahoric.isEquiv_of_continuous c hc`. Establish `hlt : ∀ x, ValuativeRel.valuation _ x < 1 → Valued.v (c.symm x) < 1` using `fun x hx => (Valuation.isEquiv_iff_val_lt_one.1 hE).2 hx`. Establish `hle : ∀ x, ValuativeRel.valuation _ x ≤ 1 → c.symm x ∈ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring` using `fun x hx => (Valuation.isEquiv_iff_val_le_one.1 hE).2 hx`. Introduce `h hK hlow x hx`.

Take `⟨hi1, hi2⟩` from `(GlobalTheory.SplitFlip.mem_KO_iff h).1 hK`. Set `g` to `Matrix.GeneralLinearGroup.map c.symm.toRingHom h`. Establish `hg : ∀ a b, g.val a b = c.symm (h.val a b)` using `fun a b => rfl`. Establish `hg' : ∀ a b, (g⁻¹).val a b = c.symm ((h⁻¹).val a b)` using `fun a b => rfl`. Establish `hpara : NG.ParaRT s r g`.

Use `⟨GlobalTheory.ConjParahoric.mem_GLint_of_entries _ g (fun a b => hg a b ▸ hle _ (hi1 a b)) (fun a b => hg' a b ▸ hle _ (hi2 a b)), fun a b ha hb => ?_⟩` and prove the remaining obligations. Rewrite using `[hg]`. Establish `ea : Fin.natAdd r (⟨a.val - r, by omega⟩ : Fin t) = a` using `by ext; simp; omega`. Establish `eb : Fin.castAdd t (⟨b.val, hb⟩ : Fin r) = b` using `by ext; simp`. Use `hlow ⟨a.val - r, by omega⟩ ⟨b.val, hb⟩` as an intermediate fact.

Rewrite `this` using `[ea, eb]`. Conclude with `hlt _ this`. Establish `hDD : c.symm (x : s.w.adicCompletion L) = NG.detDD s r g`. Rewrite using `[NG.detDD, ← Matrix.det_submatrix_equiv_self (GlobalTheory.ConjParahoric.lowerEquiv r t), hx]`. Use `(RingHom.map_det c.symm.toRingHom _).trans ?_` and prove the remaining obligations.

Use `congr 1`. Establish `key` using `hvec g hpara (Units.map c.symm.toRingHom.toMonoidHom x) hDD`. Establish `hpp : Matrix.GeneralLinearGroup.map c.toRingHom g = h` using `Units.ext (Matrix.ext fun a b => c.apply_symm_apply _)`. Establish `hcc : Units.map c.toRingHom.toMonoidHom (Units.map c.symm.toRingHom.toMonoidHom x) = x` using `Units.ext (c.apply_symm_apply _)`. Rewrite `key` using `[hpp, GlobalTheory.SameParahoric.eq_comp s ξ μ c hc hci hμ N hN hglob, hcc]`.

Conclude with `key`.
-/
theorem isParahoricVec_of_eigen : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) (s.w.adicCompletion L)) W) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ) (μ : (s.w.adicCompletion L)ˣ →* ℂˣ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → GlobalTheory.SmGL.IsSmoothChar μ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → (∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k) = μ (Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k)) → ∀ u : W, (∀ g : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), NG.ParaRT s r g → ∀ d : (s.v.adicCompletion (maximalRealSubfield L))ˣ, (d : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r g → π (Matrix.GeneralLinearGroup.map c.toRingHom g) u = ((ξ d : ℂˣ) : ℂ) • u) → GlobalTheory.ThetaGL.IsParahoricVec μ π u := by
  intro L _ _ _ s r t W _ _ π ξ μ c hc hci hμ ⟨N, hN⟩ hglob u hvec
  have hE := GlobalTheory.ConjParahoric.isEquiv_of_continuous c hc
  have hlt : ∀ x, ValuativeRel.valuation _ x < 1 → Valued.v (c.symm x) < 1 := fun x hx =>
    (Valuation.isEquiv_iff_val_lt_one.1 hE).2 hx
  have hle : ∀ x, ValuativeRel.valuation _ x ≤ 1 →
      c.symm x ∈ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := fun x hx =>
    (Valuation.isEquiv_iff_val_le_one.1 hE).2 hx
  intro h hK hlow x hx
  obtain ⟨hi1, hi2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff h).1 hK
  let g := Matrix.GeneralLinearGroup.map c.symm.toRingHom h
  have hg : ∀ a b, g.val a b = c.symm (h.val a b) := fun a b => rfl
  have hg' : ∀ a b, (g⁻¹).val a b = c.symm ((h⁻¹).val a b) := fun a b => rfl
  have hpara : NG.ParaRT s r g := by
    refine ⟨GlobalTheory.ConjParahoric.mem_GLint_of_entries _ g (fun a b => hg a b ▸ hle _ (hi1 a b))
      (fun a b => hg' a b ▸ hle _ (hi2 a b)), fun a b ha hb => ?_⟩
    rw [hg]
    have ea : Fin.natAdd r (⟨a.val - r, by omega⟩ : Fin t) = a := by ext; simp; omega
    have eb : Fin.castAdd t (⟨b.val, hb⟩ : Fin r) = b := by ext; simp
    have := hlow ⟨a.val - r, by omega⟩ ⟨b.val, hb⟩
    rw [ea, eb] at this
    exact hlt _ this
  have hDD : c.symm (x : s.w.adicCompletion L) = NG.detDD s r g := by
    rw [NG.detDD, ← Matrix.det_submatrix_equiv_self (GlobalTheory.ConjParahoric.lowerEquiv r t), hx]
    refine (RingHom.map_det c.symm.toRingHom _).trans ?_
    congr 1
  have key := hvec g hpara (Units.map c.symm.toRingHom.toMonoidHom x) hDD
  have hpp : Matrix.GeneralLinearGroup.map c.toRingHom g = h :=
    Units.ext (Matrix.ext fun a b => c.apply_symm_apply _)
  have hcc : Units.map c.toRingHom.toMonoidHom (Units.map c.symm.toRingHom.toMonoidHom x) = x :=
    Units.ext (c.apply_symm_apply _)
  rw [hpp, GlobalTheory.SameParahoric.eq_comp s ξ μ c hc hci hμ N hN hglob, hcc] at key
  exact key

end GlobalTheory.SameParahoric
