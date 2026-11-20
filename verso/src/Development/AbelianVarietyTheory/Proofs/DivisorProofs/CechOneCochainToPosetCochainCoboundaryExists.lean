import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCapFBijective

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

namespace GlobalTheory.CechCmp

/- English proof (translation)
Introduce `I _ X R _ s U hU hinf c hc`. Take `⟨b, hb⟩` from `hc`. Use `⟨fun T => (cv s U hU hinf T).symm (rsT (b T.unop.pt) (cap U T.unop)), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `T T' φ`. Apply `(cv s U hU hinf T').injective` to reduce the goal to its premises.

Establish `hTT' : cap U T'.unop ≤ cap U T.unop` using `cap_mono U (leOfHom φ.unop)`. Establish `hp : cap U T.unop ≤ U T.unop.pt` using `cap_le U T.unop.pt_mem`. Establish `hp' : cap U T'.unop ≤ U T'.unop.pt` using `cap_le U T'.unop.pt_mem`. Establish `hle : cap U T'.unop ≤ U T.unop.pt ⊓ U T'.unop.pt` using `le_inf (hTT'.trans hp) hp'`. Rewrite using `[amitsur_d0_apply, map_sub, cv_mp, cv_toPos, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hb, GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_rsT inf_le_right hle, GlobalTheory.KS.rsT_rsT inf_le_left hle, GlobalTheory.KS.rsT_rsT hp hTT']`.
-/
theorem cechOneCochainToPosetCochain_coboundary_exists : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R)
    (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)),
    ∀ c : GlobalTheory.KS.C1 U, IsCob U c → ∃ g, d0 (capF s U hU hinf) g = toPos s U hU hinf c := by
  intro I _ X R _ s U hU hinf c hc
  obtain ⟨b, hb⟩ := hc
  refine ⟨fun T => (cv s U hU hinf T).symm (rsT (b T.unop.pt) (cap U T.unop)), ?_⟩
  funext T T' φ
  apply (cv s U hU hinf T').injective
  have hTT' : cap U T'.unop ≤ cap U T.unop := cap_mono U (leOfHom φ.unop)
  have hp : cap U T.unop ≤ U T.unop.pt := cap_le U T.unop.pt_mem
  have hp' : cap U T'.unop ≤ U T'.unop.pt := cap_le U T'.unop.pt_mem
  have hle : cap U T'.unop ≤ U T.unop.pt ⊓ U T'.unop.pt := le_inf (hTT'.trans hp) hp'
  rw [amitsur_d0_apply, map_sub, cv_mp, cv_toPos, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hb,
    GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_rsT inf_le_right hle, GlobalTheory.KS.rsT_rsT inf_le_left hle, GlobalTheory.KS.rsT_rsT hp hTT']

end GlobalTheory.CechCmp
