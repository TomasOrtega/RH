import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.TopologicalKrullDimLeOfIrreducibleCloseds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NaturalDegreeZeroHomologyIsoStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinducedNerveAcyclicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinducedCechAcyclicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NerveCechDegreeZeroCompatibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CochainCohomologyNerveHomologyEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechStructureSheafComparisonStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.Hodge.Nerve

/- English proof (translation)
Use `HomologicalComplex.shortExact_of_degreewise_shortExact _ fun p ↦ ?_` and prove the remaining obligations. Use `ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Function.Exact ((nerveCx.map S.f).f p).hom ((nerveCx.map S.g).f p).hom`. Establish `h` using `fun a : C ↦ (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hS a).exact`. Introduce `y`.

Prove the components needed by the constructor for the conclusion. Introduce `hy choose x hx using fun c : Fin (p + 1) ⥤ C ↦ (h _ (y c)).1 (congrFun hy c)`. Conclude with `⟨x, funext hx⟩`. Introduce and unpack `⟨x, rfl⟩`. Conclude with `funext fun c ↦ (h _ _).2 ⟨x c, rfl⟩`.

Express the relevant statement in the definitionally equal form `Function.Injective ((nerveCx.map S.f).f p).hom`. Conclude with `fun x y hxy ↦ funext fun c ↦ (hS _).moduleCat_injective_f (congrFun hxy c)`. Express the relevant statement in the definitionally equal form `Function.Surjective ((nerveCx.map S.g).f p).hom`. Introduce `y`. Use `choose x hx using fun c : Fin (p + 1) ⥤ C ↦ (hS _).moduleCat_surjective_g (y c)`.

Conclude with `⟨x, funext hx⟩`.
-/
theorem nerveCx_shortExact {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (S : ShortComplex (C ⥤ ModuleCat.{0} R))
    (hS : ∀ a : C, (S.map ((evaluation _ _).obj a)).ShortExact) : (S.map nerveCx).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun p ↦ ?_
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · change Function.Exact ((nerveCx.map S.f).f p).hom ((nerveCx.map S.g).f p).hom
    have h := fun a : C ↦ (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hS a).exact
    intro y
    constructor
    · intro hy
      choose x hx using fun c : Fin (p + 1) ⥤ C ↦ (h _ (y c)).1 (congrFun hy c)
      exact ⟨x, funext hx⟩
    · rintro ⟨x, rfl⟩
      exact funext fun c ↦ (h _ _).2 ⟨x c, rfl⟩
  · change Function.Injective ((nerveCx.map S.f).f p).hom
    exact fun x y hxy ↦ funext fun c ↦ (hS _).moduleCat_injective_f (congrFun hxy c)
  · change Function.Surjective ((nerveCx.map S.g).f p).hom
    intro y
    choose x hx using fun c : Fin (p + 1) ⥤ C ↦ (hS _).moduleCat_surjective_g (y c)
    exact ⟨x, funext hx⟩

/- English proof (translation)
Use `(cechFunctor_shortExact (S.map (cubeOfFunctor e)) fun s hs ↦ ?_ : ((S.map (cubeOfFunctor e)).map (cechFunctor κ R)).ShortExact)` and prove the remaining obligations. Establish `hs' : ∀ (hs : PLift s.Nonempty), _` using `fun hs : PLift s.Nonempty ↦ hS (op (s.inf' hs.down e))`. Use `ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_` and prove the remaining obligations. Introduce `y`. Establish `h` using `(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hs' ⟨hs⟩).exact`.

Prove the components needed by the constructor for the conclusion. Introduce `hy`. Take `⟨x, hx⟩` from `(h (y ⟨hs⟩)).1 (congrFun hy ⟨hs⟩)`. Conclude with `⟨fun _ ↦ x, funext fun _ ↦ hx⟩`. Introduce and unpack `⟨x, rfl⟩`.

Conclude with `funext fun t ↦ (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hs' t).exact _ |>.2 ⟨x t, rfl⟩`. Conclude with `fun x y hxy ↦ funext fun t ↦ (hs' t).moduleCat_injective_f (congrFun hxy t)`. Introduce `y choose x hx using fun t : PLift s.Nonempty ↦ (hs' t).moduleCat_surjective_g (y t)`. Conclude with `⟨x, funext hx⟩`.
-/
theorem cechOf_shortExact {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] {κ : Type} [LinearOrder κ] (e : κ → P)
    (S : ShortComplex (Pᵒᵖ ⥤ ModuleCat.{0} R))
    (hS : ∀ a : Pᵒᵖ, (S.map ((evaluation _ _).obj a)).ShortExact) : (S.map (cechOf e)).ShortExact := by
  refine (cechFunctor_shortExact (S.map (cubeOfFunctor e)) fun s hs ↦ ?_ : ((S.map (cubeOfFunctor e)).map (cechFunctor κ R)).ShortExact)
  have hs' : ∀ (hs : PLift s.Nonempty), _ := fun hs : PLift s.Nonempty ↦ hS (op (s.inf' hs.down e))
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · intro y
    have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hs' ⟨hs⟩).exact
    constructor
    · intro hy
      obtain ⟨x, hx⟩ := (h (y ⟨hs⟩)).1 (congrFun hy ⟨hs⟩)
      exact ⟨fun _ ↦ x, funext fun _ ↦ hx⟩
    · rintro ⟨x, rfl⟩
      exact funext fun t ↦ (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hs' t).exact _ |>.2 ⟨x t, rfl⟩
  · exact fun x y hxy ↦ funext fun t ↦ (hs' t).moduleCat_injective_f (congrFun hxy t)
  · intro y
    choose x hx using fun t : PLift s.Nonempty ↦ (hs' t).moduleCat_surjective_g (y t)
    exact ⟨x, funext hx⟩

/- English proof (translation)
Establish `: Mono (toCoind G)`. Use `(NatTrans.mono_iff_mono_app _).2 fun a ↦ (ModuleCat.mono_iff_injective _).2 fun x y h ↦ ?_` and prove the remaining obligations. Establish `h1` using `congrFun h ⟨a.unop, le_rfl⟩`. Establish `e : ∀ z : G.obj a, (G.map (homOfLE (le_refl a.unop)).op).hom z = z` using `fun z ↦ by`. Establish `: (homOfLE (le_refl a.unop)).op = 𝟙 a` using `rfl`.

Rewrite using `[this, G.map_id]`. Both sides reduce to the same expression. Conclude with `(e x).symm.trans (h1.trans (e y))`. Establish `hS : (ShortComplex.mk _ _ (cokernel.condition (toCoind G))).ShortExact` using `{ exact := ShortComplex.exact_cokernel _ }`. Conclude with `⟨_, _, _, fun a ↦ hS.map_of_exact _⟩`.
-/
theorem exists_toCoind_shortExact {R : Type} [CommRing R] {P : Type} [SemilatticeInf P]
    (G : Pᵒᵖ ⥤ ModuleCat.{0} R) :
    ∃ (Q : Pᵒᵖ ⥤ ModuleCat.{0} R) (p : (coind fun b ↦ G.obj (op b)) ⟶ Q) (w : toCoind G ≫ p = 0),
      ∀ a : Pᵒᵖ, ((ShortComplex.mk _ _ w).map ((evaluation _ _).obj a)).ShortExact := by
  have : Mono (toCoind G) := by
    refine (NatTrans.mono_iff_mono_app _).2 fun a ↦ (ModuleCat.mono_iff_injective _).2 fun x y h ↦ ?_
    have h1 := congrFun h ⟨a.unop, le_rfl⟩
    have e : ∀ z : G.obj a, (G.map (homOfLE (le_refl a.unop)).op).hom z = z := fun z ↦ by
      have : (homOfLE (le_refl a.unop)).op = 𝟙 a := rfl
      rw [this, G.map_id]
      rfl
    exact (e x).symm.trans (h1.trans (e y))
  have hS : (ShortComplex.mk _ _ (cokernel.condition (toCoind G))).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  exact ⟨_, _, _, fun a ↦ hS.map_of_exact _⟩

/- English proof (translation)
Take `⟨ε, h1, h2⟩` from `GlobalTheory.T.nerve_cech_degree_zero_compatible (R := R) e he`. Use `GlobalTheory.T.natural_degree_zero_homology_iso nerveCx (cechOf e) ε h1 h2 (fun G ↦ ?_) n G` and prove the remaining obligations. Take `⟨Q, p, w, h⟩` from `exists_toCoind_shortExact G`. Conclude with `⟨_, Q, toCoind G, p, w, nerveCx_shortExact _ h, cechOf_shortExact e _ h, fun n ↦ ⟨GlobalTheory.T.coinduced_nerve_acyclic _ n, GlobalTheory.T.coinduced_cech_acyclic e he.2 _ n⟩⟩`.
-/
theorem nonempty_iso {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] {κ : Type} [LinearOrder κ] (e : κ → P)
    (he : Function.Bijective e) (n : ℕ) (G : Pᵒᵖ ⥤ ModuleCat.{0} R) :
    Nonempty ((nerveCx.obj G).homology n ≅ ((cechOf e).obj G).homology n) := by
  obtain ⟨ε, h1, h2⟩ := GlobalTheory.T.nerve_cech_degree_zero_compatible (R := R) e he
  refine GlobalTheory.T.natural_degree_zero_homology_iso nerveCx (cechOf e) ε h1 h2 (fun G ↦ ?_) n G
  obtain ⟨Q, p, w, h⟩ := exists_toCoind_shortExact G
  exact ⟨_, Q, toCoind G, p, w, nerveCx_shortExact _ h, cechOf_shortExact e _ h,
    fun n ↦ ⟨GlobalTheory.T.coinduced_nerve_acyclic _ n, GlobalTheory.T.coinduced_cech_acyclic e he.2 _ n⟩⟩

/- English proof (translation)
Introduce `_ R _ X s _ P _ _ S`. Use `letI := GlobalTheory.algebraΓOfHom s`. Take `⟨m, ⟨e⟩⟩` from `Finite.exists_equiv_fin P`. Set `e' : Fin m → P` to `e.symm`. Establish `he' : Function.Bijective e'` using `e.symm.bijective`.

Establish `hc : ⨆ i, (S.u (e' i)).1 = ⊤`. Rewrite using `[← S.cover]`. Conclude with `e.symm.iSup_comp (g := fun a ↦ (S.u a).1)`. Establish `hinf : ∀ (t : Finset (Fin m)) (ht : t.Nonempty), (⨅ i ∈ t, (S.u (e' i)).1) = (S.u (t.inf' ht e')).1`. Introduce `t ht`.

Proceed by induction on `ht using Finset.Nonempty.cons_induction with`. Consider the case `singleton i => simp`. Consider the case `cons i t hi ht ih`. Rewrite using `[Finset.inf'_cons ht, S.map_inf, Finset.cons_eq_insert, Finset.iInf_insert, ih]`. Establish `hD : ∀ t : Finset (Fin m), t.Nonempty → IsAffineOpen (⨅ i ∈ t, (S.u (e' i)).1)` using `fun t ht ↦ by`.

Rewrite using `[hinf t ht]`. Conclude with `(S.u _).2`. Establish `key : ∀ n, Nonempty ((nerveCx.obj (toMod (OSys s S))).homology n ≃ₗ[R] GlobalTheory.coh (GlobalTheory.structureModule X) n)`. Introduce `n`. Take `⟨i⟩` from `nonempty_iso e' he' n (toMod (OSys s S))`.

Take `⟨f⟩` from `GlobalTheory.T.cech_structure_sheaf_comparison R X s P S e' n`. Establish `: (GlobalTheory.structureModule X).IsQuasicoherent` using `GlobalTheory.QCoh.IsFiniteQC.isQuasicoherent`. Conclude with `⟨i.toLinearEquiv ≪≫ₗ f ≪≫ₗ GlobalTheory.cechHEquivCoh R hc hD (GlobalTheory.structureModule X) n⟩`. Take `⟨⟨a⟩, b⟩` from `GlobalTheory.T.cochain_cohomology_nerve_homology_equiv (OSys s S)`. Take `⟨k⟩` from `key 0`.

Use `⟨⟨a ≪≫ₗ k⟩, fun n ↦ ?_⟩` and prove the remaining obligations. Take `⟨b'⟩` from `b n`. Take `⟨k'⟩` from `key (n + 1)`. Conclude with `⟨b' ≪≫ₗ k'⟩`.
-/
theorem cmpSt_of_cxSt : CxSt → CmpSt := by
  intro _ R _ X s _ P _ _ S
  letI := GlobalTheory.algebraΓOfHom s
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin P
  let e' : Fin m → P := e.symm
  have he' : Function.Bijective e' := e.symm.bijective
  have hc : ⨆ i, (S.u (e' i)).1 = ⊤ := by
    rw [← S.cover]
    exact e.symm.iSup_comp (g := fun a ↦ (S.u a).1)
  have hinf : ∀ (t : Finset (Fin m)) (ht : t.Nonempty), (⨅ i ∈ t, (S.u (e' i)).1) = (S.u (t.inf' ht e')).1 := by
    intro t ht
    induction ht using Finset.Nonempty.cons_induction with
    | singleton i => simp
    | cons i t hi ht ih =>
      rw [Finset.inf'_cons ht, S.map_inf, Finset.cons_eq_insert, Finset.iInf_insert, ih]
  have hD : ∀ t : Finset (Fin m), t.Nonempty → IsAffineOpen (⨅ i ∈ t, (S.u (e' i)).1) := fun t ht ↦ by
    rw [hinf t ht]
    exact (S.u _).2
  have key : ∀ n, Nonempty ((nerveCx.obj (toMod (OSys s S))).homology n ≃ₗ[R] GlobalTheory.coh (GlobalTheory.structureModule X) n) := by
    intro n
    obtain ⟨i⟩ := nonempty_iso e' he' n (toMod (OSys s S))
    obtain ⟨f⟩ := GlobalTheory.T.cech_structure_sheaf_comparison R X s P S e' n
    have : (GlobalTheory.structureModule X).IsQuasicoherent := GlobalTheory.QCoh.IsFiniteQC.isQuasicoherent
    exact ⟨i.toLinearEquiv ≪≫ₗ f ≪≫ₗ GlobalTheory.cechHEquivCoh R hc hD (GlobalTheory.structureModule X) n⟩
  obtain ⟨⟨a⟩, b⟩ := GlobalTheory.T.cochain_cohomology_nerve_homology_equiv (OSys s S)
  obtain ⟨k⟩ := key 0
  refine ⟨⟨a ≪≫ₗ k⟩, fun n ↦ ?_⟩
  obtain ⟨b'⟩ := b n
  obtain ⟨k'⟩ := key (n + 1)
  exact ⟨b' ≪≫ₗ k'⟩

end GlobalTheory.CompanionTheory.Hodge.Nerve
