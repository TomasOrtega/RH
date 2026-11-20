import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCapFBijective
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechCmp

/- English proof (translation)
Introduce `I _ X R _ s U hU hinf f hf`. Establish `hm : ∀ {S T : NE I}, S.set ⊆ T.set → ((op S : (NE I)ᵒᵖ) ⟶ op T)` using `fun h => (homOfLE (NE.le_iff.2 h)).op`. Establish `hsg : ∀ T : NE I, (NE.single T.pt).set ⊆ T.set` using `fun T => by`. Rewrite using `[NE.set_single]`. Conclude with `Set.singleton_subset_iff.2 T.pt_mem`.

Establish `sub : ∀ {S T : (NE I)ᵒᵖ} (u v : S ⟶ T), u = v` using `fun u v => Quiver.Hom.unop_inj (Subsingleton.elim _ _)`. Use `⟨fun T => -f (op (NE.single T.unop.pt)) T (hm (hsg T.unop)), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `T T' φ`. Establish `hTT : T.unop.set ⊆ T'.unop.set` using `NE.le_iff.1 (leOfHom φ.unop)`. Establish `ha' : T.unop.pt ∈ T'.unop.set` using `hTT T.unop.pt_mem`.

Establish `hab : (NE.pair T.unop.pt T'.unop.pt).set ⊆ T'.unop.set`. Rewrite using `[NE.set_pair]`. Conclude with `Set.insert_subset ha' (Set.singleton_subset_iff.2 T'.unop.pt_mem)`. Set `χ : op (NE.pair T.unop.pt T'.unop.pt) ⟶ T'` to `hm hab`. Set `ψa : op (NE.single T.unop.pt) ⟶ op (NE.pair T.unop.pt T'.unop.pt)` to `(homOfLE (NE.pair_le_single_left T.unop.pt T'.unop.pt)).op`.

Set `ψb : op (NE.single T'.unop.pt) ⟶ op (NE.pair T.unop.pt T'.unop.pt)` to `(homOfLE (NE.pair_le_single_right T.unop.pt T'.unop.pt)).op`. Establish `c1` using `Z1.comp ⟨f, hf⟩ (hm (hsg T.unop)) φ`. Establish `c2` using `Z1.comp ⟨f, hf⟩ ψa χ`. Establish `c3` using `Z1.comp ⟨f, hf⟩ ψb χ`. Rewrite `c1` using `[sub (hm (hsg T.unop) ≫ φ) (ψa ≫ χ)]`.

Establish `e3 : (hm (hsg T'.unop) : op (NE.single T'.unop.pt) ⟶ T') = ψb ≫ χ` using `sub _ _`. Establish `key : toPos s U hU hinf (toCech s U hU hinf f) T T' φ = mp (capF s U hU hinf) χ (f _ _ ψa) - mp (capF s U hU hinf) χ (f _ _ ψb)`. Apply `(cv s U hU hinf T').injective` to reduce the goal to its premises. Establish `h1 : U T.unop.pt ⊓ U T'.unop.pt ≤ cap U (NE.pair T.unop.pt T'.unop.pt)` using `(cap_pair U _ _).ge`. Establish `h2 : cap U T'.unop ≤ U T.unop.pt ⊓ U T'.unop.pt` using `le_inf (cap_le U ha') (cap_le U T'.unop.pt_mem)`.

Rewrite using `[cv_toPos, toCech_apply, map_sub, cv_mp, cv_mp, GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_rsT h1 h2, GlobalTheory.KS.rsT_rsT h1 h2]`. Simplify using `only [amitsur_d0_apply, Pi.sub_apply, map_neg, key]`. Rewrite using `[e3]`. Simplify using `only at c1 c2 c3`. Take the linear combination `-c3 + c2 - c1`.
-/
theorem cechToPoset_posetToCech_sub_coboundary : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R]
    (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)),
    ∀ f : GlobalTheory.CatCoh.C1 (capF s U hU hinf), f ∈ Z1 (capF s U hU hinf) →
      ∃ g, d0 (capF s U hU hinf) g = toPos s U hU hinf (toCech s U hU hinf f) - f := by
  intro I _ X R _ s U hU hinf f hf
  have hm : ∀ {S T : NE I}, S.set ⊆ T.set → ((op S : (NE I)ᵒᵖ) ⟶ op T) :=
    fun h => (homOfLE (NE.le_iff.2 h)).op
  have hsg : ∀ T : NE I, (NE.single T.pt).set ⊆ T.set := fun T => by
    rw [NE.set_single]; exact Set.singleton_subset_iff.2 T.pt_mem
  have sub : ∀ {S T : (NE I)ᵒᵖ} (u v : S ⟶ T), u = v := fun u v =>
    Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  refine ⟨fun T => -f (op (NE.single T.unop.pt)) T (hm (hsg T.unop)), ?_⟩
  funext T T' φ
  have hTT : T.unop.set ⊆ T'.unop.set := NE.le_iff.1 (leOfHom φ.unop)
  have ha' : T.unop.pt ∈ T'.unop.set := hTT T.unop.pt_mem
  have hab : (NE.pair T.unop.pt T'.unop.pt).set ⊆ T'.unop.set := by
    rw [NE.set_pair]; exact Set.insert_subset ha' (Set.singleton_subset_iff.2 T'.unop.pt_mem)
  let χ : op (NE.pair T.unop.pt T'.unop.pt) ⟶ T' := hm hab
  let ψa : op (NE.single T.unop.pt) ⟶ op (NE.pair T.unop.pt T'.unop.pt) :=
    (homOfLE (NE.pair_le_single_left T.unop.pt T'.unop.pt)).op
  let ψb : op (NE.single T'.unop.pt) ⟶ op (NE.pair T.unop.pt T'.unop.pt) :=
    (homOfLE (NE.pair_le_single_right T.unop.pt T'.unop.pt)).op
  have c1 := Z1.comp ⟨f, hf⟩ (hm (hsg T.unop)) φ
  have c2 := Z1.comp ⟨f, hf⟩ ψa χ
  have c3 := Z1.comp ⟨f, hf⟩ ψb χ
  rw [sub (hm (hsg T.unop) ≫ φ) (ψa ≫ χ)] at c1
  have e3 : (hm (hsg T'.unop) : op (NE.single T'.unop.pt) ⟶ T') = ψb ≫ χ := sub _ _
  have key : toPos s U hU hinf (toCech s U hU hinf f) T T' φ =
      mp (capF s U hU hinf) χ (f _ _ ψa) - mp (capF s U hU hinf) χ (f _ _ ψb) := by
    apply (cv s U hU hinf T').injective
    have h1 : U T.unop.pt ⊓ U T'.unop.pt ≤ cap U (NE.pair T.unop.pt T'.unop.pt) :=
      (cap_pair U _ _).ge
    have h2 : cap U T'.unop ≤ U T.unop.pt ⊓ U T'.unop.pt :=
      le_inf (cap_le U ha') (cap_le U T'.unop.pt_mem)
    rw [cv_toPos, toCech_apply, map_sub, cv_mp, cv_mp, GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_rsT h1 h2,
      GlobalTheory.KS.rsT_rsT h1 h2]
  simp only [amitsur_d0_apply, Pi.sub_apply, map_neg, key]
  rw [e3]
  simp only at c1 c2 c3
  linear_combination -c3 + c2 - c1

end GlobalTheory.CechCmp
