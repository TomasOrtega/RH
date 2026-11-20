import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActLStmt
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiNCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictK

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.NormCut Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.SatGramActL

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ChiNBiAll : Prop := ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), ChiNBi X

namespace ChiLeft

/- English proof (translation)
Take `⟨hRL, -, hmap, -⟩` from `p.2`. Establish `hRL' : RatLink X p.1.1 p.1.2` using `hRL`. Establish `hmap' : Formalism.HermitianLatticesTheory.gmap p.1.2 Λ' = Λ` using `hmap`. Establish `hb0` using `(Y.cs u).base_lam Λ hΛ`. Establish `hb1` using `(Y.cs u').base_lam Λ' hΛ'`.

Establish `key : (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * (p.1.1.2 * (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u')) ∈ X.B.I.Kset`. Use `LatDictK.dict_K X _ _ {y | y ∈ Λ} (fun y => ?_) (fun y => ?_)` and prove the remaining obligations. Use `show y ∈ Λ ↔ _ conv_lhs => rw [← hb0]`. Conclude with `(Y.cs u).lat_eq _ y`. Use `show y ∈ Λ ↔ _`.

Establish `e1 : y ∈ Λ ↔ p.1.2.symm y ∈ Λ'`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Rewrite `hy` using `[← hmap']`. Take `⟨z, hz, hzy⟩` from `hy`.

Establish `: p.1.2.symm y = z` using `by rw [← hzy]; simp`. Rewrite using `[this]`. Conclude with `hz`. Introduce `h`. Rewrite using `[← hmap']`.

Conclude with `⟨p.1.2.symm y, h, by simp⟩`. Establish `hlat : ∀ w, w ∈ Λ' ↔ X.B.I.fmat (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u')⁻¹ *ᵥ incl X.B.I (X.crd w) ∈ X.B.I.Lf` using `fun w => by`. Use `(Y.cs u').lat_eq ((Y.cs u').base Λ') w` as an intermediate fact. Rewrite `this` using `[hb1]`. Conclude with `this`.

Rewrite using `[e1, hlat, show (p.1.1.2 * (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u'))⁻¹ = (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u')⁻¹ * p.1.1.2⁻¹ from _root_.mul_inv_rev _ _, LatDictK.fmatK_mul, ← Matrix.mulVec_mulVec, LatDictK.ratLink_incl_inv X hRL']`. Establish `e : kBB Y u u' Λ Λ' p.1.1 = (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * (p.1.1.2 * (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u'))`. Simplify using `only [kBB, kOf, mul_assoc]`. Rewrite using `[e]`. Conclude with `key`.
-/
theorem kBB_mem {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Λ ∈ Y.what₂ u) (hΛ' : Λ' ∈ Y.what₂ u')
    (p : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') : kBB Y u u' Λ Λ' p.1.1 ∈ X.B.I.Kset := by
  obtain ⟨hRL, -, hmap, -⟩ := p.2
  have hRL' : RatLink X p.1.1 p.1.2 := hRL
  have hmap' : Formalism.HermitianLatticesTheory.gmap p.1.2 Λ' = Λ := hmap
  have hb0 := (Y.cs u).base_lam Λ hΛ
  have hb1 := (Y.cs u').base_lam Λ' hΛ'
  have key : (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ *
      (p.1.1.2 * (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u')) ∈ X.B.I.Kset := by
    refine LatDictK.dict_K X _ _ {y | y ∈ Λ} (fun y => ?_) (fun y => ?_)
    · show y ∈ Λ ↔ _
      conv_lhs => rw [← hb0]
      exact (Y.cs u).lat_eq _ y
    · show y ∈ Λ ↔ _
      have e1 : y ∈ Λ ↔ p.1.2.symm y ∈ Λ' := by
        constructor
        · intro hy
          rw [← hmap'] at hy
          obtain ⟨z, hz, hzy⟩ := hy
          have : p.1.2.symm y = z := by rw [← hzy]; simp
          rw [this]; exact hz
        · intro h
          rw [← hmap']
          exact ⟨p.1.2.symm y, h, by simp⟩
      have hlat : ∀ w, w ∈ Λ' ↔ X.B.I.fmat (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u')⁻¹ *ᵥ
          incl X.B.I (X.crd w) ∈ X.B.I.Lf := fun w => by
        have := (Y.cs u').lat_eq ((Y.cs u').base Λ') w
        rw [hb1] at this
        exact this
      rw [e1, hlat, show (p.1.1.2 * (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u'))⁻¹ =
          (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u')⁻¹ * p.1.1.2⁻¹ from _root_.mul_inv_rev _ _,
        LatDictK.fmatK_mul, ← Matrix.mulVec_mulVec, LatDictK.ratLink_incl_inv X hRL']
  have e : kBB Y u u' Λ Λ' p.1.1 = (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ *
      (p.1.1.2 * (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u')) := by
    simp only [kBB, kOf, mul_assoc]
  rw [e]
  exact key

/- English proof (translation)
Establish `e : (((iotaF X w γ * c.h (c.base Λ) : Hfin X w) : X.B.I.Gf) * X.xu w)⁻¹ * ((c.h (c.base Λ) : X.B.I.Gf) * X.xu w) = (kB c Λ γ)⁻¹`. Unfold `kB`. Use `push_cast`. Use `group`. Establish `hK : (((iotaF X w γ * c.h (c.base Λ) : Hfin X w) : X.B.I.Gf) * X.xu w)⁻¹ * ((c.h (c.base Λ) : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset`.

Rewrite using `[e]`. Conclude with `mem_Kset_inv X hk`. Establish `h` using `(column_fixed_holds X w (iotaF X w γ * c.h (c.base Λ)) (c.h (c.base Λ)) hK).1`. Rewrite `h` using `[e]`. Conclude with `h`.
-/
theorem kB_inv_fix {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {w : D.what₂.Word}
    {rs : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (c : ColSys X w rs) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (γ : Gam X w) (hk : kB c Λ γ ∈ X.B.I.Kset) :
    ∀ a, CongG X (X.B.I.fmat (kB c Λ γ)⁻¹ *ᵥ X.f0 a) (X.f0 a) := by
  have e : (((iotaF X w γ * c.h (c.base Λ) : Hfin X w) : X.B.I.Gf) * X.xu w)⁻¹ *
      ((c.h (c.base Λ) : X.B.I.Gf) * X.xu w) = (kB c Λ γ)⁻¹ := by
    unfold kB
    push_cast
    group
  have hK : (((iotaF X w γ * c.h (c.base Λ) : Hfin X w) : X.B.I.Gf) * X.xu w)⁻¹ *
      ((c.h (c.base Λ) : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset := by
    rw [e]; exact mem_Kset_inv X hk
  have h := (column_fixed_holds X w (iotaF X w γ * c.h (c.base Λ)) (c.h (c.base Λ)) hK).1
  rw [e] at h
  exact h

/- English proof (translation)
Establish `hK : (((1 : Hfin X w) : X.B.I.Gf) * X.xu w)⁻¹ * (((1 : Hfin X w) : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset`. Rewrite using `[inv_mul_cancel]`. Conclude with `h1`. Establish `h` using `(column_fixed_holds X w 1 1 hK).2`. Simplify `h` using `only [inv_mul_cancel]`.
-/
theorem one_fix {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (w : D.what₂.Word) (h1 : (1 : X.B.I.Gf) ∈ X.B.I.Kset) :
    ∀ a, CongG X (X.B.I.fmat (1 : X.B.I.Gf) *ᵥ nxt X.e0 X.z0 a) (nxt X.e0 X.z0 a) := by
  have hK : (((1 : Hfin X w) : X.B.I.Gf) * X.xu w)⁻¹ * (((1 : Hfin X w) : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset := by
    rw [inv_mul_cancel]; exact h1
  have h := (column_fixed_holds X w 1 1 hK).2
  simpa only [inv_mul_cancel] using h

end ChiLeft

/- English proof (translation)
Introduce `D X Y u u' Λ Λ' hΛ hΛ' γ hk p`. Establish `hκ` using `ChiLeft.kBB_mem Y u u' hΛ hΛ' p`. Establish `h1 : (1 : X.B.I.Gf) ∈ X.B.I.Kset`. Establish `h` using `mem_Kset_mul X hk (mem_Kset_inv X hk)`. Rewrite `h` using `[mul_inv_cancel]`. Then use the resulting hypothesis.

Establish `h` using `hB D X (kBB Y u u' Λ Λ' p.1.1) (kB (Y.cs u) Λ γ) 1 hκ hk h1 (ChiLeft.kB_inv_fix (Y.cs u) Λ γ hk) (ChiLeft.one_fix u h1)`. Rewrite `h` using `[mul_one]`. Then use the resulting hypothesis.
-/
theorem chiNLeft_holds (hB : ChiNBiAll) : ChiNLeft := by
  intro D X Y u u' Λ Λ' hΛ hΛ' γ hk p
  have hκ := ChiLeft.kBB_mem Y u u' hΛ hΛ' p
  have h1 : (1 : X.B.I.Gf) ∈ X.B.I.Kset := by
    have h := mem_Kset_mul X hk (mem_Kset_inv X hk)
    rwa [mul_inv_cancel] at h
  have h := hB D X (kBB Y u u' Λ Λ' p.1.1) (kB (Y.cs u) Λ γ) 1 hκ hk h1
    (ChiLeft.kB_inv_fix (Y.cs u) Λ γ hk) (ChiLeft.one_fix u h1)
  rwa [mul_one] at h

end Formalism.L2.SG.Pf.SatGramActL
