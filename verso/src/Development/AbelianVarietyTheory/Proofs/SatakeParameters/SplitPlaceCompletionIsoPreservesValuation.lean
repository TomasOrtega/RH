import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjSPV
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitConjVal

/- English proof (translation)
Establish `ha0 : a ≠ 0` using `by rintro rfl; rw [map_zero] at ha; exact WithZero.exp_ne_zero ha.symm`. Establish `hb0 : b ≠ 0` using `by rintro rfl; rw [map_zero] at hb; exact WithZero.exp_ne_zero hb.symm`. Establish `hlt : ∀ r s : F, v1 r < v1 s ↔ v2 r < v2 s` using `fun r s => by`. Rewrite using `[← not_le, ← not_le, h s r]`. Establish `hval : ∀ y : F, y ≠ 0 → v2 y = WithZero.exp (WithZero.log (v2 y))` using `fun y hy => (WithZero.exp_log (by simpa using hy)).symm`.

Establish `hval1 : ∀ y : F, y ≠ 0 → v1 y = WithZero.exp (WithZero.log (v1 y))` using `fun y hy => (WithZero.exp_log (by simpa using hy)).symm`. Establish `ha2 : v2 a = WithZero.exp (-1)`. Establish `h1 : v2 a < 1`. Rewrite using `[← map_one v2, ← hlt, map_one, ha, ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Use linear arithmetic over natural numbers and integers.

Establish `h2 : v1 b < 1`. Rewrite using `[← map_one v1, hlt, map_one, hb, ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Use linear arithmetic over natural numbers and integers. Establish `h3 : ¬ v1 b < v1 a`. Introduce `h3`.

Rewrite `h3` using `[hlt, hb]`. Rewrite `h1` using `[hval a ha0, ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Rewrite `h3` using `[hval a ha0, WithZero.exp_lt_exp]`. Use linear arithmetic over natural numbers and integers. Establish `h4 : v1 b = v1 a`.

Rewrite `h2` using `[hval1 b hb0, ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Rewrite `h3` using `[hval1 b hb0, ha, WithZero.exp_lt_exp]`. Rewrite using `[hval1 b hb0, ha, WithZero.exp_inj]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← hb]`.

Conclude with `((h.eq_iff).1 h4).symm`. Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Simplify using the standard rewrite rules. Use `set k := WithZero.log (v1 x)`. Establish `e1 : v1 x = v1 (a ^ (-k))`.

Rewrite using `[map_zpow₀, ha, ← WithZero.exp_zsmul, hval1 x hx]`. Use `congr 1`. Simplify using `[k]`. Rewrite using `[e1, (h.eq_iff).1 e1, map_zpow₀, map_zpow₀, ha, ha2]`.
-/
theorem eq_of_isEquiv {F : Type} [Field F] (v1 v2 : Valuation F (WithZero (Multiplicative ℤ)))
    (h : v1.IsEquiv v2) (a b : F) (ha : v1 a = WithZero.exp (-1)) (hb : v2 b = WithZero.exp (-1))
    (x : F) : v1 x = v2 x := by
  have ha0 : a ≠ 0 := by rintro rfl; rw [map_zero] at ha; exact WithZero.exp_ne_zero ha.symm
  have hb0 : b ≠ 0 := by rintro rfl; rw [map_zero] at hb; exact WithZero.exp_ne_zero hb.symm
  have hlt : ∀ r s : F, v1 r < v1 s ↔ v2 r < v2 s := fun r s => by
    rw [← not_le, ← not_le, h s r]
  have hval : ∀ y : F, y ≠ 0 → v2 y = WithZero.exp (WithZero.log (v2 y)) := fun y hy =>
    (WithZero.exp_log (by simpa using hy)).symm
  have hval1 : ∀ y : F, y ≠ 0 → v1 y = WithZero.exp (WithZero.log (v1 y)) := fun y hy =>
    (WithZero.exp_log (by simpa using hy)).symm
  have ha2 : v2 a = WithZero.exp (-1) := by
    have h1 : v2 a < 1 := by
      rw [← map_one v2, ← hlt, map_one, ha, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have h2 : v1 b < 1 := by
      rw [← map_one v1, hlt, map_one, hb, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have h3 : ¬ v1 b < v1 a := by
      intro h3
      rw [hlt, hb] at h3
      rw [hval a ha0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
      rw [hval a ha0, WithZero.exp_lt_exp] at h3
      omega
    have h4 : v1 b = v1 a := by
      rw [hval1 b hb0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h2
      rw [hval1 b hb0, ha, WithZero.exp_lt_exp] at h3
      rw [hval1 b hb0, ha, WithZero.exp_inj]
      omega
    rw [← hb]
    exact ((h.eq_iff).1 h4).symm
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  set k := WithZero.log (v1 x)
  have e1 : v1 x = v1 (a ^ (-k)) := by
    rw [map_zpow₀, ha, ← WithZero.exp_zsmul, hval1 x hx]
    congr 1; simp [k]
  rw [e1, (h.eq_iff).1 e1, map_zpow₀, map_zpow₀, ha, ha2]

/- English proof (translation)
Introduce `L _ _ _ s c hc hci x`. Use `GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion (maximalRealSubfield L) s.v` as an intermediate fact. Establish `ho : IsOpenMap c` using `AddMonoidHom.isOpenMap_of_sigmaCompact c.toAddEquiv.toAddMonoidHom c.surjective hc`. Establish `hc' : Continuous c.symm` using `c.toEquiv.continuous_symm_iff.2 ho`. Set `v' : Valuation (s.v.adicCompletion (maximalRealSubfield L)) (WithZero (Multiplicative ℤ))` to `(Valued.v : Valuation (s.w.adicCompletion L) (WithZero (Multiplicative ℤ))).comap c.toRingHom`.

Establish `hE : v'.IsEquiv Valued.v`. Rewrite using `[Valuation.isEquiv_iff_val_lt_one]`. Introduce `y`. Use `⟨fun h => ?_, fun h => GlobalTheory.ConjParahoric.val_lt_one_map c.toRingHom hc h⟩` and prove the remaining obligations. Simplify using `using GlobalTheory.ConjParahoric.val_lt_one_map c.symm.toRingHom hc' h`.

Take `⟨π, hπ⟩` from `s.v.valuation_exists_uniformizer (maximalRealSubfield L)`. Take `⟨ϖ, hϖ⟩` from `s.w.valuation_exists_uniformizer L`. Establish `h1 : v' (s.i ϖ) = WithZero.exp (-1)` using `by show Valued.v (c (s.i ϖ)) = _`. Rewrite using `[hci, ReciprocityTheory.Aut.adic_valued_algebraMap, hϖ]`. Establish `h2 : Valued.v (algebraMap (maximalRealSubfield L) (s.v.adicCompletion (maximalRealSubfield L)) π) = WithZero.exp (-1)`.

Rewrite using `[ReciprocityTheory.Aut.adic_valued_algebraMap, hπ]`. Conclude with `eq_of_isEquiv v' Valued.v hE _ _ h1 h2 x`.
-/
theorem valuation_eq : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ x : s.v.adicCompletion (maximalRealSubfield L), Valued.v (c x) = Valued.v x := by
  intro L _ _ _ s c hc hci x
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion (maximalRealSubfield L) s.v
  have ho : IsOpenMap c :=
    AddMonoidHom.isOpenMap_of_sigmaCompact c.toAddEquiv.toAddMonoidHom c.surjective hc
  have hc' : Continuous c.symm := c.toEquiv.continuous_symm_iff.2 ho
  let v' : Valuation (s.v.adicCompletion (maximalRealSubfield L)) (WithZero (Multiplicative ℤ)) :=
    (Valued.v : Valuation (s.w.adicCompletion L) (WithZero (Multiplicative ℤ))).comap c.toRingHom
  have hE : v'.IsEquiv Valued.v := by
    rw [Valuation.isEquiv_iff_val_lt_one]
    intro y
    refine ⟨fun h => ?_, fun h => GlobalTheory.ConjParahoric.val_lt_one_map c.toRingHom hc h⟩
    simpa using GlobalTheory.ConjParahoric.val_lt_one_map c.symm.toRingHom hc' h
  obtain ⟨π, hπ⟩ := s.v.valuation_exists_uniformizer (maximalRealSubfield L)
  obtain ⟨ϖ, hϖ⟩ := s.w.valuation_exists_uniformizer L
  have h1 : v' (s.i ϖ) = WithZero.exp (-1) := by
    show Valued.v (c (s.i ϖ)) = _
    rw [hci, ReciprocityTheory.Aut.adic_valued_algebraMap, hϖ]
  have h2 : Valued.v (algebraMap (maximalRealSubfield L) (s.v.adicCompletion (maximalRealSubfield L)) π) =
      WithZero.exp (-1) := by
    rw [ReciprocityTheory.Aut.adic_valued_algebraMap, hπ]
  exact eq_of_isEquiv v' Valued.v hE _ _ h1 h2 x

end GlobalTheory.SplitConjVal
