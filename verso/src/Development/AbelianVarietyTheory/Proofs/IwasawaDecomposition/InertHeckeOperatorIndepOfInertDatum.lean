import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GEquivIntL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SatInd

section Field

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Use `show Formalism.UG.cT σ' (((M : Matrix (Fin n) (Fin n) K)).map (g : K →+* K)) * Formalism.UG.antiJ K n * ((M : Matrix (Fin n) (Fin n) K)).map (g : K →+* K) = Formalism.UG.antiJ K n ↔ Formalism.UG.cT σ (M : Matrix (Fin n) (Fin n) K) * Formalism.UG.antiJ K n * (M : Matrix (Fin n) (F …`. Establish `e : Formalism.UG.cT σ' (((M : Matrix (Fin n) (Fin n) K)).map (g : K →+* K)) * Formalism.UG.antiJ K n * ((M : Matrix (Fin n) (Fin n) K)).map (g : K →+* K) = (Formalism.UG.cT σ (M : Matrix (Fin n) (Fin n) K) * Formalism.UG.antiJ K n * (M : Matrix (Fin n) (Fin n) K)).map (g : K →+* …`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, antiJ_map, cT_map (g : K →+* K) σ σ' hg]`. Rewrite using `[e]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `Matrix.map_injective g.injective (h.trans (antiJ_map (g : K →+* K) n).symm)`. Introduce `h`. Rewrite using `[h, antiJ_map]`.
-/
theorem indepDatum_memGU_iff (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)) {n : ℕ}
    (M : GL (Fin n) K) :
    Formalism.UG.bc (n := Fin n) (g : K →+* K) M ∈ Formalism.UG.GU σ' n ↔ M ∈ Formalism.UG.GU σ n := by
  show Formalism.UG.cT σ' (((M : Matrix (Fin n) (Fin n) K)).map (g : K →+* K)) * Formalism.UG.antiJ K n *
      ((M : Matrix (Fin n) (Fin n) K)).map (g : K →+* K) = Formalism.UG.antiJ K n ↔
    Formalism.UG.cT σ (M : Matrix (Fin n) (Fin n) K) * Formalism.UG.antiJ K n * (M : Matrix (Fin n) (Fin n) K) =
      Formalism.UG.antiJ K n
  have e : Formalism.UG.cT σ' (((M : Matrix (Fin n) (Fin n) K)).map (g : K →+* K)) * Formalism.UG.antiJ K n *
      ((M : Matrix (Fin n) (Fin n) K)).map (g : K →+* K) =
      (Formalism.UG.cT σ (M : Matrix (Fin n) (Fin n) K) * Formalism.UG.antiJ K n * (M : Matrix (Fin n) (Fin n) K)).map
        (g : K →+* K) := by
    rw [Matrix.map_mul, Matrix.map_mul, antiJ_map, cT_map (g : K →+* K) σ σ' hg]
  rw [e]
  constructor
  · intro h
    exact Matrix.map_injective g.injective (h.trans (antiJ_map (g : K →+* K) n).symm)
  · intro h
    rw [h, antiJ_map]

/- English proof (translation)
Take `⟨p, rfl⟩` from `hM`. Use `⟨Formalism.UG.bc (n := Fin n) ((g : K →+* K).restrict (Formalism.UG.intL K) (Formalism.UG.intL K) (fun x hx => hint x hx)) p, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem indepDatum_intRange (g : K ≃+* K) (hint : ∀ x, x ∈ Formalism.UG.intL K → g x ∈ Formalism.UG.intL K) {n : ℕ}
    (M : GL (Fin n) K) (hM : M ∈ (Formalism.UG.bc (n := Fin n) (Formalism.UG.intL K).subtype).range) :
    Formalism.UG.bc (n := Fin n) (g : K →+* K) M ∈ (Formalism.UG.bc (n := Fin n) (Formalism.UG.intL K).subtype).range := by
  obtain ⟨p, rfl⟩ := hM
  refine ⟨Formalism.UG.bc (n := Fin n) ((g : K →+* K).restrict (Formalism.UG.intL K) (Formalism.UG.intL K)
    (fun x hx => hint x hx)) p, ?_⟩
  ext i j
  rfl

end Field

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

/- English proof (translation)
Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Conclude with `(gEquiv_e Dv Dv' _).symm`.
-/
theorem indepDatum_bc_e (Dv Dv' : InertDatum L n v w)
    (Y : GL (Fin n) (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L))) :
    Formalism.UG.bc (n := Fin n) (Dv'.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+*
              w.adicCompletion L) Y =
      Formalism.UG.bc (n := Fin n) ((gEquiv Dv Dv' : w.adicCompletion L ≃+* w.adicCompletion L) :
        w.adicCompletion L →+* w.adicCompletion L)
        (Formalism.UG.bc (n := Fin n) (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+*
          w.adicCompletion L) Y) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact (gEquiv_e Dv Dv' _).symm

def indepDatumK (Dv Dv' : InertDatum L n v w) : GL (Fin n) (w.adicCompletion L) :=
  (Formalism.UG.bc (n := Fin n) ((gEquiv Dv Dv' : w.adicCompletion L ≃+* w.adicCompletion L) :
    w.adicCompletion L →+* w.adicCompletion L) Dv.P)⁻¹ * Dv'.P

/- English proof (translation)
Simplify using `only [InertDatum.loc, indepDatumK, map_mul, map_inv, indepDatum_bc_e Dv Dv']`. Use `group`.
-/
theorem indepDatum_loc (Dv Dv' : InertDatum L n v w) (x : GAf L n) :
    Dv'.loc x = (indepDatumK Dv Dv')⁻¹ * Formalism.UG.bc (n := Fin n) ((gEquiv Dv Dv' :
      w.adicCompletion L ≃+* w.adicCompletion L) : w.adicCompletion L →+* w.adicCompletion L) (Dv.loc x) *
        indepDatumK Dv Dv' := by
  simp only [InertDatum.loc, indepDatumK, map_mul, map_inv, indepDatum_bc_e Dv Dv']
  group

/- English proof (translation)
Use `set g : w.adicCompletion L →+* w.adicCompletion L := ((gEquiv Dv Dv' : w.adicCompletion L ≃+* w.adicCompletion L) : w.adicCompletion L →+* w.adicCompletion L) with hgdef`. Use `set Q : Matrix (Fin n) (Fin n) (w.adicCompletion L) := ((Formalism.UG.bc (n := Fin n) g Dv.P : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) with hQdef`. Use `set Qi : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (((Formalism.UG.bc (n := Fin n) g Dv.P)⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) with hQidef`. Establish `hQ : Formalism.UG.cT Dv'.σw Q * Q = Formalism.UG.antiJ (w.adicCompletion L) n`. Establish `hmap : Q = (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)).map g` using `rfl`.

Rewrite using `[hmap, cT_map g Dv.σw Dv'.σw (gEquiv_comm Dv Dv'), ← Matrix.map_mul, Dv.Panti, antiJ_map]`. Establish `h1 : Q * Qi = 1` using `by rw [hQdef, hQidef, ← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `h2 : Formalism.UG.cT Dv'.σw Qi * Formalism.UG.cT Dv'.σw Q = 1` using `by rw [← Formalism.UG.cT_mul, h1, Formalism.UG.cT_one]`. Use `show Formalism.UG.cT Dv'.σw (Qi * (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L))) * Formalism.UG.antiJ (w.adicCompletion L) n * (Qi * (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L))) = Formalism.UG.antiJ (w.adicCompletion L) n`. Rewrite using `[← hQ, Formalism.UG.cT_mul]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Formalism.UG.cT Dv'.σw (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) * (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) := by`. Rewrite using `[h1, h2, Matrix.mul_one, Matrix.mul_one]`. Use `_ = Formalism.UG.cT Dv'.σw Q * Q := by rw [Dv'.Panti, hQ]`.
-/
theorem indepDatumK_memGU (Dv Dv' : InertDatum L n v w) : indepDatumK Dv Dv' ∈ Formalism.UG.GU Dv'.σw n := by
  set g : w.adicCompletion L →+* w.adicCompletion L := ((gEquiv Dv Dv' : w.adicCompletion L ≃+* w.adicCompletion L) :
    w.adicCompletion L →+* w.adicCompletion L) with hgdef
  set Q : Matrix (Fin n) (Fin n) (w.adicCompletion L) := ((Formalism.UG.bc (n := Fin n) g Dv.P :
    GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) with hQdef
  set Qi : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (((Formalism.UG.bc (n := Fin n) g Dv.P)⁻¹ :
    GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) with hQidef
  have hQ : Formalism.UG.cT Dv'.σw Q * Q = Formalism.UG.antiJ (w.adicCompletion L) n := by
    have hmap : Q = (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)).map g := rfl
    rw [hmap, cT_map g Dv.σw Dv'.σw (gEquiv_comm Dv Dv'), ← Matrix.map_mul, Dv.Panti, antiJ_map]
  have h1 : Q * Qi = 1 := by rw [hQdef, hQidef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : Formalism.UG.cT Dv'.σw Qi * Formalism.UG.cT Dv'.σw Q = 1 := by rw [← Formalism.UG.cT_mul, h1, Formalism.UG.cT_one]
  show Formalism.UG.cT Dv'.σw (Qi * (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L))) *
      Formalism.UG.antiJ (w.adicCompletion L) n * (Qi * (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L))) =
    Formalism.UG.antiJ (w.adicCompletion L) n
  rw [← hQ, Formalism.UG.cT_mul]
  calc Formalism.UG.cT Dv'.σw (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) * Formalism.UG.cT Dv'.σw Qi *
        (Formalism.UG.cT Dv'.σw Q * Q) * (Qi * (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)))
      = Formalism.UG.cT Dv'.σw (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
          (Formalism.UG.cT Dv'.σw Qi * Formalism.UG.cT Dv'.σw Q) * (Q * Qi) *
          (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT Dv'.σw (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
          (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) := by
        rw [h1, h2, Matrix.mul_one, Matrix.mul_one]
    _ = Formalism.UG.cT Dv'.σw Q * Q := by rw [Dv'.Panti, hQ]

/- English proof (translation)
Rewrite using `[Formalism.UG.KU, Subgroup.mem_subgroupOf]`. Use `⟨indepDatumK_memGU Dv Dv', ?_⟩` and prove the remaining obligations. Take `⟨p1, hp1⟩` from `indepDatum_intRange (gEquiv Dv Dv') (fun x hx => (gEquiv_intL Dv Dv' x).1 hx) _ Dv.Pint`. Take `⟨p2, hp2⟩` from `Dv'.Pint`. Use `⟨p1⁻¹ * p2, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, map_inv, hp1, hp2]`. Both sides reduce to the same expression.
-/
theorem indepDatumK_memKU (Dv Dv' : InertDatum L n v w) :
    (⟨indepDatumK Dv Dv', indepDatumK_memGU Dv Dv'⟩ : Formalism.UG.GU Dv'.σw n) ∈ Formalism.UG.KU Dv'.σw n := by
  rw [Formalism.UG.KU, Subgroup.mem_subgroupOf]
  refine ⟨indepDatumK_memGU Dv Dv', ?_⟩
  obtain ⟨p1, hp1⟩ := indepDatum_intRange (gEquiv Dv Dv') (fun x hx => (gEquiv_intL Dv Dv' x).1 hx) _ Dv.Pint
  obtain ⟨p2, hp2⟩ := Dv'.Pint
  refine ⟨p1⁻¹ * p2, ?_⟩
  rw [map_mul, map_inv, hp1, hp2]
  rfl

/- English proof (translation)
Establish `hk` using `indepDatumK_memGU Dv Dv'`. Establish `hloc` using `indepDatum_loc Dv Dv' x`. Use `set g : w.adicCompletion L →+* w.adicCompletion L := ((gEquiv Dv Dv' : w.adicCompletion L ≃+* w.adicCompletion L) : w.adicCompletion L →+* w.adicCompletion L) with hgdef`. Unfold `InertDatum.hval`. Distinguish the cases in `hy : Dv.loc x ∈ Formalism.UG.GU Dv.σw n`.

Establish `hgy : Formalism.UG.bc (n` using `Fin n) g (Dv.loc x) ∈ Formalism.UG.GU Dv'.σw n := (indepDatum_memGU_iff (gEquiv Dv Dv') (gEquiv_comm Dv Dv') _).2 hy`. Establish `hy' : Dv'.loc x ∈ Formalism.UG.GU Dv'.σw n`. Rewrite using `[hloc]`. Conclude with `mul_mem (mul_mem (inv_mem hk) hgy) hk`. Rewrite using `[dif_pos hy', dif_pos hy]`.

Establish `hb` using `hbi (⟨⟨indepDatumK Dv Dv', hk⟩, indepDatumK_memKU Dv Dv'⟩ : Formalism.UG.KU Dv'.σw n)⁻¹ ⟨⟨indepDatumK Dv Dv', hk⟩, indepDatumK_memKU Dv Dv'⟩ (guMap (gEquiv Dv Dv') (gEquiv_comm Dv Dv') n ⟨Dv.loc x, hy⟩)`. Use `Eq.trans (congrArg h' ?_) hb` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Dv'.loc x = _`. Rewrite using `[hloc]`.

Both sides reduce to the same expression. Establish `hy' : Dv'.loc x ∉ Formalism.UG.GU Dv'.σw n`. Introduce `h`. Apply `hy` to reduce the goal to its premises. Rewrite using `[← indepDatum_memGU_iff (gEquiv Dv Dv') (gEquiv_comm Dv Dv')]`.

Establish `he : Formalism.UG.bc (n` using `Fin n) g (Dv.loc x) = indepDatumK Dv Dv' * Dv'.loc x * (indepDatumK Dv Dv')⁻¹ := by`. Rewrite using `[hloc]`. Use `group`. Rewrite using `[he]`. Conclude with `mul_mem (mul_mem hk h) (inv_mem hk)`.

Rewrite using `[dif_neg hy', dif_neg hy]`.
-/
theorem indepDatum_hval (Dv Dv' : InertDatum L n v w) (h' : Formalism.UG.GU Dv'.σw n → ℂ)
    (hbi : IsBiInv (Formalism.UG.KU Dv'.σw n) h') (x : GAf L n) :
    Dv'.hval h' (Dv'.loc x) =
      Dv.hval (fun y => h' (guMap (gEquiv Dv Dv') (gEquiv_comm Dv Dv') n y)) (Dv.loc x) := by
  have hk := indepDatumK_memGU Dv Dv'
  have hloc := indepDatum_loc Dv Dv' x
  set g : w.adicCompletion L →+* w.adicCompletion L := ((gEquiv Dv Dv' : w.adicCompletion L ≃+* w.adicCompletion L) :
    w.adicCompletion L →+* w.adicCompletion L) with hgdef
  unfold InertDatum.hval
  by_cases hy : Dv.loc x ∈ Formalism.UG.GU Dv.σw n
  · have hgy : Formalism.UG.bc (n := Fin n) g (Dv.loc x) ∈ Formalism.UG.GU Dv'.σw n :=
      (indepDatum_memGU_iff (gEquiv Dv Dv') (gEquiv_comm Dv Dv') _).2 hy
    have hy' : Dv'.loc x ∈ Formalism.UG.GU Dv'.σw n := by
      rw [hloc]; exact mul_mem (mul_mem (inv_mem hk) hgy) hk
    rw [dif_pos hy', dif_pos hy]
    have hb := hbi (⟨⟨indepDatumK Dv Dv', hk⟩, indepDatumK_memKU Dv Dv'⟩ : Formalism.UG.KU Dv'.σw n)⁻¹
      ⟨⟨indepDatumK Dv Dv', hk⟩, indepDatumK_memKU Dv Dv'⟩
      (guMap (gEquiv Dv Dv') (gEquiv_comm Dv Dv') n ⟨Dv.loc x, hy⟩)
    refine Eq.trans (congrArg h' ?_) hb
    apply Subtype.ext
    change Dv'.loc x = _
    rw [hloc]
    rfl
  · have hy' : Dv'.loc x ∉ Formalism.UG.GU Dv'.σw n := by
      intro h
      apply hy
      rw [← indepDatum_memGU_iff (gEquiv Dv Dv') (gEquiv_comm Dv Dv')]
      have he : Formalism.UG.bc (n := Fin n) g (Dv.loc x) =
          indepDatumK Dv Dv' * Dv'.loc x * (indepDatumK Dv Dv')⁻¹ := by
        rw [hloc]; group
      rw [he]
      exact mul_mem (mul_mem hk h) (inv_mem hk)
    rw [dif_neg hy', dif_neg hy]

/- English proof (translation)
Introduce `L _ _ _ n v w Dv Dv' U W _ _ h' hbi f`. Use function extensionality and compare the values at `g`. Unfold `heckeFunI`. Use `finsum_congr fun c => ?_` and prove the remaining obligations. Distinguish the cases in `hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x`.

Rewrite using `[dif_pos hc, dif_pos hc, indepDatum_hval Dv Dv' h' hbi]`. Rewrite using `[dif_neg hc, dif_neg hc]`.
-/
theorem heckeFunI_indepDatum : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv Dv' : InertDatum L n v w) (U : Subgroup (GAf L n)) (W : Type) [AddCommGroup W] [Module ℂ W]
    (h' : GU Dv'.σw n → ℂ), IsBiInv (KU Dv'.σw n) h' → ∀ f : GAf L n → W,
    heckeFunI L n U Dv' h' f =
      heckeFunI L n U Dv (fun y => h' (guMap (gEquiv Dv Dv') (gEquiv_comm Dv Dv') n y)) f := by
  intro L _ _ _ n v w Dv Dv' U W _ _ h' hbi f
  funext g
  unfold heckeFunI
  refine finsum_congr fun c => ?_
  by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
  · rw [dif_pos hc, dif_pos hc, indepDatum_hval Dv Dv' h' hbi]
  · rw [dif_neg hc, dif_neg hc]

end GlobalTheory.SatInd
