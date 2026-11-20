import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartFin

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField TopologicalSpace

variable {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']

def secVal (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (h : genPt ξ ∈ U) : Γ(X, U) →+* Ω :=
  (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom

/- English proof (translation)
Establish `e` using `X.presheaf.germ_stalkSpecializes (U := U) hq hs`. Simplify using `only [genMap, secVal]`. Rewrite using `[← e]`. Both sides reduce to the same expression.
-/
theorem genMap_germ (ξ : Spec (CommRingCat.of Ω) ⟶ X) {U : X.Opens} (h : genPt ξ ∈ U) {q : X} (hq : q ∈ U)
    (hs : genPt ξ ⤳ q) (s : Γ(X, U)) :
    genMap ξ ⟨q, hs⟩ (X.presheaf.germ U q hq s) = secVal ξ U h s := by
  have e := X.presheaf.germ_stalkSpecializes (U := U) hq hs
  simp only [genMap, secVal]
  rw [← e]
  rfl

/- English proof (translation)
Establish `e : X.presheaf.map i.op ≫ X.presheaf.germ V (genPt ξ) hV = X.presheaf.germ U (genPt ξ) hU` using `X.presheaf.germ_res i _ hV`. Simplify using `only [secVal]`. Rewrite using `[← e]`. Both sides reduce to the same expression.
-/
theorem secVal_res (ξ : Spec (CommRingCat.of Ω) ⟶ X) {U V : X.Opens} (i : V ⟶ U) (hV : genPt ξ ∈ V)
    (hU : genPt ξ ∈ U) (s : Γ(X, U)) :
    secVal ξ V hV (X.presheaf.map i.op s) = secVal ξ U hU s := by
  have e : X.presheaf.map i.op ≫ X.presheaf.germ V (genPt ξ) hV = X.presheaf.germ U (genPt ξ) hU :=
    X.presheaf.germ_res i _ hV
  simp only [secVal]
  rw [← e]
  rfl

/- English proof (translation)
Introduce `s t e`. Use `TopCat.Presheaf.section_ext X.sheaf U s t fun q hq => ?_` and prove the remaining obligations. Apply `hinj ⟨q, hall q⟩` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `genMap ξ ⟨q, hall q⟩ (X.presheaf.germ U q hq s) = genMap ξ ⟨q, hall q⟩ (X.presheaf.germ U q hq t)`. Rewrite using `[genMap_germ ξ h hq, genMap_germ ξ h hq, e]`.
-/
theorem secVal_injective {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hall : ∀ q : X, genPt ξ ⤳ q)
    (hinj : ∀ p : Cpt ξ, Function.Injective (genMap ξ p)) (U : X.Opens) (h : genPt ξ ∈ U) :
    Function.Injective (secVal ξ U h) := by
  intro s t e
  refine TopCat.Presheaf.section_ext X.sheaf U s t fun q hq => ?_
  apply hinj ⟨q, hall q⟩
  change genMap ξ ⟨q, hall q⟩ (X.presheaf.germ U q hq s) = genMap ξ ⟨q, hall q⟩ (X.presheaf.germ U q hq t)
  rw [genMap_germ ξ h hq, genMap_germ ξ h hq, e]

/- English proof (translation)
Establish `key : ∀ q : U, ∃ (V : X.Opens) (_ : q.1 ∈ V) (i : V ⟶ U) (s : Γ(X, V)) (hV : genPt ξ ∈ V), secVal ξ V hV s = a`. Introduce `q`. Take `⟨g, hg⟩` from `ha q.1 q.2`. Take `⟨V, hqV, s, rfl⟩` from `X.presheaf.germ_exist g`. Establish `hV : genPt ξ ∈ V` using `(hall q.1).mem_open V.isOpen hqV`.

Establish `hVU : genPt ξ ∈ V ⊓ U` using `⟨hV, h⟩`. Use `⟨V ⊓ U, ⟨hqV, q.2⟩, homOfLE inf_le_right, X.presheaf.map (homOfLE inf_le_left).op s, hVU, ?_⟩` and prove the remaining obligations. Conclude with `(secVal_res ξ (homOfLE inf_le_left) hVU hV s).trans ((genMap_germ ξ hV hqV (hall q.1) s).symm.trans hg)`. Use `choose V hq i s hV hs using key`. Establish `hcomp : TopCat.Presheaf.IsCompatible X.sheaf.presheaf V s`.

Introduce `p q`. Establish `hpq : genPt ξ ∈ V p ⊓ V q` using `⟨hV p, hV q⟩`. Establish `hI` using `secVal_injective hall hinj (V p ⊓ V q) hpq`. Establish `e : secVal ξ (V p ⊓ V q) hpq (X.presheaf.map (Opens.infLELeft (V p) (V q)).op (s p)) = secVal ξ (V p ⊓ V q) hpq (X.presheaf.map (Opens.infLERight (V p) (V q)).op (s q))`. Rewrite using `[secVal_res ξ _ hpq (hV p), secVal_res ξ _ hpq (hV q), hs, hs]`.

Conclude with `hI e`. Take `⟨t, ht, -⟩` from `X.sheaf.existsUnique_gluing' V U i (fun q hq' => Opens.mem_iSup.2 ⟨⟨q, hq'⟩, hq ⟨q, hq'⟩⟩) s hcomp`. Use `⟨t, ?_⟩` and prove the remaining obligations. Establish `e` using `ht ⟨genPt ξ, h⟩`. Rewrite using `[← secVal_res ξ (i ⟨genPt ξ, h⟩) (hV ⟨genPt ξ, h⟩) h t]`.

Conclude with `(congrArg _ e).trans (hs _)`.
-/
theorem exists_secVal {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hall : ∀ q : X, genPt ξ ⤳ q)
    (hinj : ∀ p : Cpt ξ, Function.Injective (genMap ξ p)) (U : X.Opens) (h : genPt ξ ∈ U) (a : Ω)
    (ha : ∀ q (_ : q ∈ U), a ∈ regAt ξ ⟨q, hall q⟩) : ∃ s : Γ(X, U), secVal ξ U h s = a := by
  have key : ∀ q : U, ∃ (V : X.Opens) (_ : q.1 ∈ V) (i : V ⟶ U) (s : Γ(X, V)) (hV : genPt ξ ∈ V),
      secVal ξ V hV s = a := by
    intro q
    obtain ⟨g, hg⟩ := ha q.1 q.2
    obtain ⟨V, hqV, s, rfl⟩ := X.presheaf.germ_exist g
    have hV : genPt ξ ∈ V := (hall q.1).mem_open V.isOpen hqV
    have hVU : genPt ξ ∈ V ⊓ U := ⟨hV, h⟩
    refine ⟨V ⊓ U, ⟨hqV, q.2⟩, homOfLE inf_le_right, X.presheaf.map (homOfLE inf_le_left).op s, hVU, ?_⟩
    exact (secVal_res ξ (homOfLE inf_le_left) hVU hV s).trans ((genMap_germ ξ hV hqV (hall q.1) s).symm.trans hg)
  choose V hq i s hV hs using key
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.presheaf V s := by
    intro p q
    have hpq : genPt ξ ∈ V p ⊓ V q := ⟨hV p, hV q⟩
    have hI := secVal_injective hall hinj (V p ⊓ V q) hpq
    have e : secVal ξ (V p ⊓ V q) hpq (X.presheaf.map (Opens.infLELeft (V p) (V q)).op (s p)) =
        secVal ξ (V p ⊓ V q) hpq (X.presheaf.map (Opens.infLERight (V p) (V q)).op (s q)) := by
      rw [secVal_res ξ _ hpq (hV p), secVal_res ξ _ hpq (hV q), hs, hs]
    exact hI e
  obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing' V U i
    (fun q hq' => Opens.mem_iSup.2 ⟨⟨q, hq'⟩, hq ⟨q, hq'⟩⟩) s hcomp
  refine ⟨t, ?_⟩
  have e := ht ⟨genPt ξ, h⟩
  rw [← secVal_res ξ (i ⟨genPt ξ, h⟩) (hV ⟨genPt ξ, h⟩) h t]
  exact (congrArg _ e).trans (hs _)

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem secVal_congr {z w : Spec (CommRingCat.of Ω) ⟶ X} (e : z = w) (U : X.Opens) (hz : genPt z ∈ U)
    (hw : genPt w ∈ U) (s : Γ(X, U)) : secVal z U hz s = secVal w U hw s := by
  subst e
  rfl

/- English proof (translation)
Establish `e` using `f.germ_stalkMap U (genPt ξ') h'`. Establish `e2` using `Scheme.stalkClosedPointTo_comp ξ' f`. Simplify using `only [secVal]`. Rewrite using `[e2]`. Express the relevant statement in the definitionally equal form `((X.presheaf.germ U (f (genPt ξ')) h' ≫ f.stalkMap (genPt ξ')) ≫ Scheme.stalkClosedPointTo ξ').hom s = _`.

Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem secVal_comp (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (U : X.Opens)
    (h : genPt (ξ' ≫ f) ∈ U) (h' : genPt ξ' ∈ f ⁻¹ᵁ U) (s : Γ(X, U)) :
    secVal (ξ' ≫ f) U h s = secVal ξ' (f ⁻¹ᵁ U) h' (f.app U s) := by
  have e := f.germ_stalkMap U (genPt ξ') h'
  have e2 := Scheme.stalkClosedPointTo_comp ξ' f
  simp only [secVal]
  rw [e2]
  change ((X.presheaf.germ U (f (genPt ξ')) h' ≫ f.stalkMap (genPt ξ')) ≫ Scheme.stalkClosedPointTo ξ').hom s = _
  rw [e]
  rfl

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Establish `: IsLocalHom (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i).hom`. Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Establish `h1 : IsUnit ((Scheme.stalkClosedPointTo ξ).hom a)`. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`.

Establish `: (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i).hom a = 0`. Express the relevant statement in the definitionally equal form `i ((Scheme.stalkClosedPointTo ξ).hom a) = 0`. Rewrite using `[h0, map_zero]`. Rewrite `ha` using `[this]`. Conclude with `not_isUnit_zero ha`.

Conclude with `isUnit_of_map_unit (Scheme.stalkClosedPointTo ξ).hom a h1`. Establish `e0 : Spec.map (Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk (genPt ξ) = ξ` using `Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ`. Establish `e : Spec.map (CommRingCat.ofHom i) ≫ ξ = Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫ X.fromSpecStalk (genPt ξ)` using `by conv_lhs => rw [← e0]`. Rewrite using `[Spec.map_comp, Category.assoc]`. Establish `h2 : genPt (Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫ X.fromSpecStalk (genPt ξ)) ∈ U` using `e ▸ h`.

Rewrite using `[secVal_congr e U h h2]`. Establish `e3` using `Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) U h2`. Conclude with `congrArg (fun φ => φ.hom s) e3`.
-/
theorem secVal_spec (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω →+* Ω') (U : X.Opens)
    (h : genPt (Spec.map (CommRingCat.ofHom i) ≫ ξ) ∈ U) (h' : genPt ξ ∈ U) (s : Γ(X, U)) :
    secVal (Spec.map (CommRingCat.ofHom i) ≫ ξ) U h s = i (secVal ξ U h' s) := by
  have : IsLocalHom (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i).hom := by
    refine ⟨fun a ha => ?_⟩
    have h1 : IsUnit ((Scheme.stalkClosedPointTo ξ).hom a) := by
      rw [isUnit_iff_ne_zero]
      intro h0
      have : (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i).hom a = 0 := by
        change i ((Scheme.stalkClosedPointTo ξ).hom a) = 0
        rw [h0, map_zero]
      rw [this] at ha
      exact not_isUnit_zero ha
    exact isUnit_of_map_unit (Scheme.stalkClosedPointTo ξ).hom a h1
  have e0 : Spec.map (Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk (genPt ξ) = ξ :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have e : Spec.map (CommRingCat.ofHom i) ≫ ξ =
      Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫ X.fromSpecStalk (genPt ξ) := by
    conv_lhs => rw [← e0]
    rw [Spec.map_comp, Category.assoc]
  have h2 : genPt (Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫ X.fromSpecStalk (genPt ξ)) ∈ U :=
    e ▸ h
  rw [secVal_congr e U h h2]
  have e3 := Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk
    (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) U h2
  exact congrArg (fun φ => φ.hom s) e3

/- English proof (translation)
Establish `h1 : genPt (ξ' ≫ f) ∈ U` using `h'`. Establish `h2 : genPt (Spec.map (CommRingCat.ofHom i) ≫ ξ) ∈ U` using `hd ▸ h1`. Rewrite using `[← secVal_comp ξ' f U h1 h', secVal_congr hd U h1 h2, secVal_spec ξ i U h2 h]`.
-/
theorem secVal_app {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {f : X' ⟶ X}
    {i : Ω →+* Ω'} (hd : Dominates ξ' ξ f i) (U : X.Opens) (h : genPt ξ ∈ U) (h' : genPt ξ' ∈ f ⁻¹ᵁ U)
    (s : Γ(X, U)) : secVal ξ' (f ⁻¹ᵁ U) h' (f.app U s) = i (secVal ξ U h s) := by
  have h1 : genPt (ξ' ≫ f) ∈ U := h'
  have h2 : genPt (Spec.map (CommRingCat.ofHom i) ≫ ξ) ∈ U := hd ▸ h1
  rw [← secVal_comp ξ' f U h1 h', secVal_congr hd U h1 h2, secVal_spec ξ i U h2 h]

/- English proof (translation)
Use `choose! σ hσ using hs`. Use `letI := φ.toAlgebra`. Establish `hsm : ∀ a (b : B), a • b = φ a * b` using `fun a b => Algebra.smul_def a b`. Establish `key : ∀ z ∈ Submodule.span R₀ (s : Set Ω'), ∃ b ∈ Submodule.span A ((s.image σ : Finset B) : Set B), v' b = z`. Introduce `z hz`.

Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem t ht`. Conclude with `⟨σ t, Submodule.subset_span (by simpa using ⟨t, ht, rfl⟩), hσ t ht⟩`. Consider the case `zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨b, hb, rfl⟩` from `hx`. Take `⟨b', hb', rfl⟩` from `hy`. Conclude with `⟨b + b', Submodule.add_mem _ hb hb', map_add _ _ _⟩`. Consider the case `smul r x _ hx`. Take `⟨b, hb, rfl⟩` from `hx`.

Take `⟨a, ha⟩` from `hR r r.2`. Use `⟨a • b, Submodule.smul_mem _ a hb, ?_⟩` and prove the remaining obligations. Rewrite using `[hsm, map_mul, hc, ha]`. Both sides reduce to the same expression. Use `⟨⟨s.image σ, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[eq_top_iff]`. Introduce `b _`. Take `⟨b', hb', e⟩` from `key _ (hb b)`. Rewrite using `[← hv' e]` and apply the resulting hypothesis.
-/
theorem finite_of_values {o A B : Type} [CommRing o] [CommRing A] [CommRing B] [Algebra o Ω'] (φ : A →+* B)
    (v : A →+* Ω) (v' : B →+* Ω') (i : Ω →+* Ω') (hv' : Function.Injective v')
    (hc : ∀ a, v' (φ a) = i (v a)) (R₀ : Subalgebra o Ω') (hR : ∀ r ∈ R₀, ∃ a, i (v a) = r) (s : Finset Ω')
    (hs : ∀ t ∈ s, ∃ b, v' b = t) (hb : ∀ b, v' b ∈ Submodule.span R₀ (s : Set Ω')) : φ.Finite := by
  classical
  choose! σ hσ using hs
  letI := φ.toAlgebra
  have hsm : ∀ a (b : B), a • b = φ a * b := fun a b => Algebra.smul_def a b
  have key : ∀ z ∈ Submodule.span R₀ (s : Set Ω'),
      ∃ b ∈ Submodule.span A ((s.image σ : Finset B) : Set B), v' b = z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem t ht =>
      exact ⟨σ t, Submodule.subset_span (by simpa using ⟨t, ht, rfl⟩), hσ t ht⟩
    | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨b', hb', rfl⟩ := hy
      exact ⟨b + b', Submodule.add_mem _ hb hb', map_add _ _ _⟩
    | smul r x _ hx =>
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨a, ha⟩ := hR r r.2
      refine ⟨a • b, Submodule.smul_mem _ a hb, ?_⟩
      rw [hsm, map_mul, hc, ha]
      rfl
  refine ⟨⟨s.image σ, ?_⟩⟩
  rw [eq_top_iff]
  intro b _
  obtain ⟨b', hb', e⟩ := key _ (hb b)
  rwa [← hv' e]

/- English proof (translation)
Use `⟨hc, fun c' => ?_⟩` and prove the remaining obligations. Take `⟨g, hg'⟩` from `hg.bij.2 (x c' / x c)`. Use `⟨g, ?_⟩` and prove the remaining obligations. Simplify using `only [genMap]`. Rewrite using `[TopCat.Presheaf.stalkSpecializes_refl]`.

Conclude with `hg'`.
-/
theorem inChart_genPt {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hg : IsCptGen ξ) {κ : Type} {x : κ → Ω} {c : κ}
    (hc : x c ≠ 0) : InChart ξ x c ⟨genPt ξ, specializes_rfl⟩ := by
  refine ⟨hc, fun c' => ?_⟩
  obtain ⟨g, hg'⟩ := hg.bij.2 (x c' / x c)
  refine ⟨g, ?_⟩
  simp only [genMap]
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact hg'

/- English proof (translation)
Rewrite using `[chRing, M.tie.ring c hc a]`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Use `exists_secVal M.all M.tie.gen.inj U h a fun q hq => ?_` and prove the remaining obligations. Take `⟨h', hi⟩` from `(hU q).1 hq`.

Conclude with `H _ hi`. Introduce and unpack `⟨s, rfl⟩ p hp`. Establish `hq : p.1 ∈ U` using `(hU p.1).2 ⟨p.2, hp⟩`. Conclude with `⟨_, genMap_germ M.ξ h hq p.2 s⟩`.
-/
theorem mem_chRing_iff {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω} (M : PModel o x) {c : κ}
    (hc : x c ≠ 0) {U : M.X.Opens} (hU : ∀ q : M.X, q ∈ U ↔ ∃ h : genPt M.ξ ⤳ q, InChart M.ξ x c ⟨q, h⟩)
    (h : genPt M.ξ ∈ U) (a : Ω) : a ∈ chRing o x c ↔ ∃ s : Γ(M.X, U), secVal M.ξ U h s = a := by
  rw [chRing, M.tie.ring c hc a]
  constructor
  · intro H
    refine exists_secVal M.all M.tie.gen.inj U h a fun q hq => ?_
    obtain ⟨h', hi⟩ := (hU q).1 hq
    exact H _ hi
  · rintro ⟨s, rfl⟩ p hp
    have hq : p.1 ∈ U := (hU p.1).2 ⟨p.2, hp⟩
    exact ⟨_, genMap_germ M.ξ h hq p.2 s⟩

/- English proof (translation)
Take `⟨U', hU'a, hU'm⟩` from `M'.tie.affine (e c) hne`. Establish `hV : ∀ q : M'.X, q ∈ f ⁻¹ᵁ U ↔ ∃ h : genPt M'.ξ ⤳ q, InChart M'.ξ y (e c) ⟨q, h⟩`. Introduce `q`. Establish `hq` using `hpre ⟨q, M'.all q⟩`. Prove the components needed by the constructor for the conclusion.

Introduce `hfq`. Take `⟨h, hi⟩` from `(hUm (f q)).1 hfq`. Conclude with `⟨M'.all q, hq.2 ⟨⟨f q, h⟩, rfl, hi⟩⟩`. Introduce and unpack `⟨h₀, hi⟩`. Take `⟨⟨p, h⟩, hp, hpi⟩` from `hq.1 hi`.

Express the relevant statement in the definitionally equal form `p = f q at hp`. Substitute `hp` using the available equality. Conclude with `(hUm _).2 ⟨h, hpi⟩`. Establish `hEq : f ⁻¹ᵁ U = U'` using `Opens.ext (Set.ext fun q => (hV q).trans (hU'm q).symm)`. Use `⟨hEq ▸ hU'a, ?_⟩` and prove the remaining obligations.

Establish `hg : genPt M.ξ ∈ U` using `(hUm _).2 ⟨specializes_rfl, inChart_genPt M.tie.gen hc⟩`. Establish `hg' : genPt M'.ξ ∈ f ⁻¹ᵁ U` using `(hV _).2 ⟨specializes_rfl, inChart_genPt M'.tie.gen hne⟩`. Take `⟨s, hs⟩` from `hfin`. Establish `hmap : chRing o (fun k => algebraMap Ω Ω' (x k)) c = (chRing o x c).map (IsScalarTower.toAlgHom o Ω Ω')`. Simplify using `only [chRing]`.

Rewrite using `[AlgHom.map_adjoin, ← Set.range_comp]`. Use `congr 2`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Use `finite_of_values (o := o) (f.app U).hom (secVal M.ξ U hg) (secVal M'.ξ _ hg') (algebraMap Ω Ω') (secVal_injective M'.all M'.tie.gen.inj _ hg') (secVal_app hd U hg hg') (chRing o (fun k => algebraMap Ω Ω' (x k)) c) ?_ s ?_ ?_` and prove the remaining obligations.

Introduce `r hr`. Rewrite `hr` using `[hmap]`. Take `⟨r₀, h₀, rfl⟩` from `hr`. Take `⟨a, ha⟩` from `(mem_chRing_iff M hc hUm hg r₀).1 h₀`. Conclude with `⟨a, by rw [ha]; rfl⟩`.

Introduce `t ht`. Conclude with `(mem_chRing_iff M' hne hV hg' t).1 ((hs t).2 (Submodule.subset_span ht))`. Introduce `b`. Conclude with `(hs _).1 ((mem_chRing_iff M' hne hV hg' _).2 ⟨b, rfl⟩)`.
-/
theorem chart_step {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} {x : κ → Ω}
    (M : PModel o x) {Ω' : Type} [Field Ω'] [Algebra Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] {κ' : Type}
    {y : κ' → Ω'} (M' : PModel o y) (f : M'.X ⟶ M.X) (e : κ → κ') (hd : Dominates M'.ξ M.ξ f (algebraMap Ω Ω'))
    {c : κ} (hc : x c ≠ 0) (hne : y (e c) ≠ 0)
    (hpre : ∀ p' : Cpt M'.ξ, InChart M'.ξ y (e c) p' ↔ ∃ p : Cpt M.ξ, p.1 = f p'.1 ∧ InChart M.ξ x c p)
    (hfin : ∃ s : Finset Ω', ∀ a : Ω', a ∈ chRing o y (e c) ↔
      a ∈ Submodule.span (chRing o (fun k => algebraMap Ω Ω' (x k)) c) (s : Set Ω'))
    {U : M.X.Opens} (hUm : ∀ q : M.X, q ∈ U ↔ ∃ h : genPt M.ξ ⤳ q, InChart M.ξ x c ⟨q, h⟩) :
    IsAffineOpen (f ⁻¹ᵁ U) ∧ (f.app U).hom.Finite := by
  obtain ⟨U', hU'a, hU'm⟩ := M'.tie.affine (e c) hne
  have hV : ∀ q : M'.X, q ∈ f ⁻¹ᵁ U ↔ ∃ h : genPt M'.ξ ⤳ q, InChart M'.ξ y (e c) ⟨q, h⟩ := by
    intro q
    have hq := hpre ⟨q, M'.all q⟩
    constructor
    · intro hfq
      obtain ⟨h, hi⟩ := (hUm (f q)).1 hfq
      exact ⟨M'.all q, hq.2 ⟨⟨f q, h⟩, rfl, hi⟩⟩
    · rintro ⟨h₀, hi⟩
      obtain ⟨⟨p, h⟩, hp, hpi⟩ := hq.1 hi
      change p = f q at hp
      subst hp
      exact (hUm _).2 ⟨h, hpi⟩
  have hEq : f ⁻¹ᵁ U = U' := Opens.ext (Set.ext fun q => (hV q).trans (hU'm q).symm)
  refine ⟨hEq ▸ hU'a, ?_⟩
  have hg : genPt M.ξ ∈ U := (hUm _).2 ⟨specializes_rfl, inChart_genPt M.tie.gen hc⟩
  have hg' : genPt M'.ξ ∈ f ⁻¹ᵁ U := (hV _).2 ⟨specializes_rfl, inChart_genPt M'.tie.gen hne⟩
  obtain ⟨s, hs⟩ := hfin
  have hmap : chRing o (fun k => algebraMap Ω Ω' (x k)) c = (chRing o x c).map (IsScalarTower.toAlgHom o Ω Ω') := by
    simp only [chRing]
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    congr 2
    funext j
    simp
  refine finite_of_values (o := o) (f.app U).hom (secVal M.ξ U hg) (secVal M'.ξ _ hg') (algebraMap Ω Ω')
    (secVal_injective M'.all M'.tie.gen.inj _ hg') (secVal_app hd U hg hg')
    (chRing o (fun k => algebraMap Ω Ω' (x k)) c) ?_ s ?_ ?_
  · intro r hr
    rw [hmap] at hr
    obtain ⟨r₀, h₀, rfl⟩ := hr
    obtain ⟨a, ha⟩ := (mem_chRing_iff M hc hUm hg r₀).1 h₀
    exact ⟨a, by rw [ha]; rfl⟩
  · intro t ht
    exact (mem_chRing_iff M' hne hV hg' t).1 ((hs t).2 (Submodule.subset_span ht))
  · intro b
    exact (hs _).1 ((mem_chRing_iff M' hne hV hg' _).2 ⟨b, rfl⟩)

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Introduce `hd hne hpre hfin`. Use `choose U hUa hUm using fun c : {c // x c ≠ 0} => M.tie.affine c.1 c.2`. Establish `hcov : ⨆ i, ((⟨U i, hUa i⟩ : M.X.affineOpens) : M.X.Opens) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `q _`.

Take `⟨c, hc⟩` from `M.tie.cover ⟨q, M.all q⟩`. Conclude with `Opens.mem_iSup.2 ⟨⟨c, hc.1⟩, (hUm ⟨c, hc.1⟩ q).2 ⟨M.all q, hc⟩⟩`. Use `(HasAffineProperty.iff_of_iSup_eq_top (P := @IsFinite) (fun i => ⟨U i, hUa i⟩) hcov).2 fun i => ?_` and prove the remaining obligations. Take `⟨h1, h2⟩` from `chart_step M M' f e hd i.2 (hne i.1 i.2) (hpre i.1 i.2) (hfin i.1 i.2) (hUm i)`. Use `⟨h1, ?_⟩` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[morphismRestrict_appTop, CommRingCat.hom_comp, RingHom.finite_respectsIso.cancel_right_isIso]`. Express the relevant statement in the definitionally equal form `(Scheme.Hom.app f ((U i).ι ''ᵁ ⊤)).hom.Finite`. Rewrite using `[Scheme.Opens.ι_image_top]`. Conclude with `h2`.
-/
theorem isFinite_of_charts {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ]
    {x : κ → Ω} (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω']
    {κ' : Type} [Finite κ'] {y : κ' → Ω'} (M' : PModel o y) (f : M'.X ⟶ M.X) (e : κ → κ') :
    Dominates M'.ξ M.ξ f (algebraMap Ω Ω') → (∀ c, x c ≠ 0 → y (e c) ≠ 0) →
    (∀ c, x c ≠ 0 → ∀ p' : Cpt M'.ξ, InChart M'.ξ y (e c) p' ↔ ∃ p : Cpt M.ξ, p.1 = f p'.1 ∧ InChart M.ξ x c p) →
    (∀ c, x c ≠ 0 → ∃ s : Finset Ω', ∀ a : Ω', a ∈ chRing o y (e c) ↔
      a ∈ Submodule.span (chRing o (fun k => algebraMap Ω Ω' (x k)) c) (s : Set Ω')) → IsFinite f := by
  intro hd hne hpre hfin
  choose U hUa hUm using fun c : {c // x c ≠ 0} => M.tie.affine c.1 c.2
  have hcov : ⨆ i, ((⟨U i, hUa i⟩ : M.X.affineOpens) : M.X.Opens) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨c, hc⟩ := M.tie.cover ⟨q, M.all q⟩
    exact Opens.mem_iSup.2 ⟨⟨c, hc.1⟩, (hUm ⟨c, hc.1⟩ q).2 ⟨M.all q, hc⟩⟩
  refine (HasAffineProperty.iff_of_iSup_eq_top (P := @IsFinite) (fun i => ⟨U i, hUa i⟩) hcov).2 fun i => ?_
  obtain ⟨h1, h2⟩ := chart_step M M' f e hd i.2 (hne i.1 i.2) (hpre i.1 i.2) (hfin i.1 i.2) (hUm i)
  refine ⟨h1, ?_⟩
  dsimp only
  rw [morphismRestrict_appTop, CommRingCat.hom_comp, RingHom.finite_respectsIso.cancel_right_isIso]
  change (Scheme.Hom.app f ((U i).ι ''ᵁ ⊤)).hom.Finite
  rw [Scheme.Opens.ι_image_top]
  exact h2

end GlobalTheory.CompanionTheory.Ar.ChartFin
