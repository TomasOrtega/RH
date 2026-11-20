import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartId
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFreeHom
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShearIsoActionProjectionStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemOrbitSelfStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.OrbitTransStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteSetBasicOpenAffineStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFlatLocallyFreeAffineStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFreePullbackAffineStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PullbackRestrictOpenStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormNotMemPrimeIffStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BasicOpenNormFibreIffStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

noncomputable section
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd

variable {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `⟨z, hz, rfl⟩`. Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `⟨z, hz, rfl⟩`.
-/
theorem mem_orbit_iff {x y : X.left} : y ∈ orbit G X x ↔
    ∃ z, (snd G X).left z = x ∧ (γ[G, X] : G ⊗ X ⟶ X).left z = y := by
  constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩

/- English proof (translation)
Take `⟨σ, -, h1, h2⟩` from `GlobalTheory.T.shear_iso_action_projection G X`. Take `⟨z, rfl, rfl⟩` from `(mem_orbit_iff G X).1 h`. Use `(mem_orbit_iff G X).2 ⟨σ.left z, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, ← Over.comp_left, h1]`. Rewrite using `[← Scheme.Hom.comp_apply, ← Over.comp_left, h2]`.
-/
theorem orbit_symm {x y : X.left} (h : y ∈ orbit G X x) : x ∈ orbit G X y := by
  obtain ⟨σ, -, h1, h2⟩ := GlobalTheory.T.shear_iso_action_projection G X
  obtain ⟨z, rfl, rfl⟩ := (mem_orbit_iff G X).1 h
  refine (mem_orbit_iff G X).2 ⟨σ.left z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h1]
  · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h2]

/- English proof (translation)
Take `⟨z, rfl, rfl⟩` from `(mem_orbit_iff G X).1 h`. Establish `e : (γ[G, X] : G ⊗ X ⟶ X).left ≫ X.hom = (snd G X).left ≫ X.hom` using `(Over.w _).trans (Over.w _).symm`. Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, e]`.
-/
theorem orbit_hom {x y : X.left} (h : y ∈ orbit G X x) : X.hom y = X.hom x := by
  obtain ⟨z, rfl, rfl⟩ := (mem_orbit_iff G X).1 h
  have e : (γ[G, X] : G ⊗ X ⟶ X).left ≫ X.hom = (snd G X).left ≫ X.hom := (Over.w _).trans (Over.w _).symm
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, e]

/- English proof (translation)
Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Conclude with `h _ hz (orbit_symm G X ((mem_orbit_iff G X).2 ⟨z, rfl, rfl⟩))`. Introduce `hz`.

Conclude with `h _ hz ((mem_orbit_iff G X).2 ⟨z, rfl, rfl⟩)`.
-/
theorem stable_of_forall (V : X.left.Opens) (h : ∀ y ∈ V, orbit G X y ⊆ V) :
    (γ[G, X] : G ⊗ X ⟶ X).left ⁻¹ᵁ V = (snd G X).left ⁻¹ᵁ V := by
  ext z
  constructor
  · intro hz
    exact h _ hz (orbit_symm G X ((mem_orbit_iff G X).2 ⟨z, rfl, rfl⟩))
  · intro hz
    exact h _ hz ((mem_orbit_iff G X).2 ⟨z, rfl, rfl⟩)

variable {G X} in
/- English proof (translation)
Use `hG.1` as an intermediate fact. Establish `h : IsFinite (pullback.snd G.hom X.hom)` using `inferInstance`. Conclude with `h`.
-/
theorem isFinite_snd (hG : IsFiniteLocallyFree G.hom) : IsFinite (snd G X).left := by
  have := hG.1
  have h : IsFinite (pullback.snd G.hom X.hom) := inferInstance
  exact h

variable {G X} in
/- English proof (translation)
Use `isFinite_snd (X := X) hG` as an intermediate fact. Conclude with `((snd G X).left.finite_preimage_singleton x).image _`.
-/
theorem orbit_finite (hG : IsFiniteLocallyFree G.hom) (x : X.left) : (orbit G X x).Finite := by
  have := isFinite_snd (X := X) hG
  exact ((snd G X).left.finite_preimage_singleton x).image _

variable {G X} in
/- English proof (translation)
Use `isFinite_snd (X := X) hG` as an intermediate fact. Establish `hc : IsClosed ((snd G X).left '' ((γ[G, X] : G ⊗ X ⟶ X).left ⁻¹' (O : Set X.left)ᶜ))` using `(snd G X).left.isClosedMap _ (O.isOpen.isClosed_compl.preimage (γ[G, X] : G ⊗ X ⟶ X).left.continuous)`. Use `hc.isOpen_compl using 1` and compare the differences between its conclusion and the goal. Use extensionality with `y`. Simplify using `only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, Set.mem_preimage, not_exists, not_and]`.

Prove the components needed by the constructor for the conclusion. Introduce `h z hz hy`. Conclude with `hz (h ((mem_orbit_iff G X).2 ⟨z, hy, rfl⟩))`. Introduce `h w hw`. Take `⟨z, hz, rfl⟩` from `(mem_orbit_iff G X).1 hw`.

Assume the negation of the conclusion as `hn`. Conclude with `h z hn hz`.
-/
theorem isOpen_saturated (hG : IsFiniteLocallyFree G.hom) (O : X.left.Opens) :
    IsOpen {y : X.left | orbit G X y ⊆ O} := by
  have := isFinite_snd (X := X) hG
  have hc : IsClosed ((snd G X).left '' ((γ[G, X] : G ⊗ X ⟶ X).left ⁻¹' (O : Set X.left)ᶜ)) :=
    (snd G X).left.isClosedMap _ (O.isOpen.isClosed_compl.preimage (γ[G, X] : G ⊗ X ⟶ X).left.continuous)
  convert hc.isOpen_compl using 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, Set.mem_preimage, not_exists, not_and]
  constructor
  · intro h z hz hy
    exact hz (h ((mem_orbit_iff G X).2 ⟨z, hy, rfl⟩))
  · intro h w hw
    obtain ⟨z, hz, rfl⟩ := (mem_orbit_iff G X).1 hw
    by_contra hn
    exact h z hn hz

/- English proof (translation)
Establish `key : P.basicOpen ((c.appLE U ⊤ hc).hom f) = c ⁻¹ᵁ Y.basicOpen f`. Rewrite using `[Scheme.preimage_basicOpen, Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res, top_inf_eq]`. Rewrite using `[key]`. Both sides reduce to the same expression.
-/
theorem mem_basicOpen_appLE' {P Y : Scheme.{0}} (c : P ⟶ Y) (U : Y.Opens) (hc : ⊤ ≤ c ⁻¹ᵁ U) (f : Γ(Y, U)) (z : P) :
    z ∈ P.basicOpen ((c.appLE U ⊤ hc).hom f) ↔ c z ∈ Y.basicOpen f := by
  have key : P.basicOpen ((c.appLE U ⊤ hc).hom f) = c ⁻¹ᵁ Y.basicOpen f := by
    rw [Scheme.preimage_basicOpen, Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res, top_inf_eq]
  rw [key]
  rfl

/- English proof (translation)
Use `letI := v.appTop.hom.toAlgebra`. Establish `h1 : Module.Free Γ(D, ⊤) Γ(P, ⊤)` using `hv.1`. Establish `h2 : Module.Finite Γ(D, ⊤) Γ(P, ⊤)` using `hv.2`. Use `⟨Algebra.norm Γ(D, ⊤) e, GlobalTheory.T.basic_open_norm_fibre_iff v _ e fun p => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.T.norm_not_mem_prime_iff e p.asIdeal p.isPrime]`.

Prove the components needed by the constructor for the conclusion. Introduce `h q hq`. Conclude with `h q.asIdeal q.isPrime hq`. Introduce `h q hq hq'`. Conclude with `h ⟨q, hq⟩ hq'`.
-/
theorem exists_norm {P D : Scheme.{0}} [IsAffine P] [IsAffine D] (v : P ⟶ D)
    (hv : FiniteFreeHom v.appTop.hom) (e : Γ(P, ⊤)) :
    ∃ N : Γ(D, ⊤), ∀ y : D, y ∈ D.basicOpen N ↔ ∀ z : P, v z = y → z ∈ P.basicOpen e := by
  letI := v.appTop.hom.toAlgebra
  have h1 : Module.Free Γ(D, ⊤) Γ(P, ⊤) := hv.1
  have h2 : Module.Finite Γ(D, ⊤) Γ(P, ⊤) := hv.2
  refine ⟨Algebra.norm Γ(D, ⊤) e, GlobalTheory.T.basic_open_norm_fibre_iff v _ e fun p => ?_⟩
  rw [GlobalTheory.T.norm_not_mem_prime_iff e p.asIdeal p.isPrime]
  constructor
  · intro h q hq
    exact h q.asIdeal q.isPrime hq
  · intro h q hq hq'
    exact h ⟨q, hq⟩ hq'

/- English proof (translation)
Introduce `S G X _ _ hG x U hU hxU`. Establish `hfl` using `hG.1`. Establish `hfl2` using `hG.2.1`. Establish `hfl3` using `hG.2.2`. Take `⟨W, hsW, hW, hfree⟩` from `GlobalTheory.T.finite_flat_locally_free_affine G.hom (X.hom x)`.

Establish `htrans : ∀ {y w : X.left}, y ∈ orbit G X x → w ∈ orbit G X y → w ∈ orbit G X x` using `fun {y w} => GlobalTheory.T.mem_orbit_trans G X x y w`. Set `O : X.left.Opens` to `U ⊓ X.hom ⁻¹ᵁ W`. Establish `hxO : orbit G X x ⊆ O` using `fun y hy => ⟨hxU hy, by show X.hom y ∈ W`. Rewrite using `[orbit_hom G X hy]`. Conclude with `hsW⟩`.

Set `V₀ : X.left.Opens` to `⟨{y | orbit G X y ⊆ O}, isOpen_saturated hG O⟩`. Establish `hV₀O : V₀ ≤ O` using `fun y hy => hy (GlobalTheory.T.mem_orbit_self' G X y)`. Establish `hV₀U : V₀ ≤ U` using `hV₀O.trans inf_le_left`. Establish `hxV₀ : orbit G X x ⊆ V₀` using `fun y hy w hw => hxO (htrans hy hw)`. Take `⟨f, hKf, hfV⟩` from `GlobalTheory.T.finite_set_basic_open_affine U V₀ hU hV₀U _ (orbit_finite hG x) hxV₀`.

Set `D : X.left.Opens` to `X.left.basicOpen f`. Establish `hD : IsAffineOpen D` using `hU.basicOpen f`. Establish `hDW : D ≤ X.hom ⁻¹ᵁ W` using `(hfV.trans hV₀O).trans inf_le_right`. Establish `hsq : IsPullback (fst G X).left (snd G X).left G.hom X.hom` using `IsPullback.of_hasPullback G.hom X.hom`. Take `⟨h, u, hpb⟩` from `GlobalTheory.T.pullback_restrict_open hsq W D hDW`.

Use `isFinite_snd (X := X) hG` as an intermediate fact. Use `haveI : IsAffine D.toScheme := hD`. Use `haveI : IsAffine W.toScheme := hW`. Use `haveI : IsAffine (G.hom ⁻¹ᵁ W).toScheme := hW.preimage G.hom`. Use `haveI : IsAffine ((snd G X).left ⁻¹ᵁ D).toScheme := hD.preimage (snd G X).left`.

Establish `hfree'` using `GlobalTheory.T.finite_free_pullback_affine hpb hfree`. Set `P' : (G ⊗ X).left.Opens` to `(snd G X).left ⁻¹ᵁ D`. Set `c : P'.toScheme ⟶ X.left` to `P'.ι ≫ (γ[G, X] : G ⊗ X ⟶ X).left`. Establish `hc : ⊤ ≤ c ⁻¹ᵁ U`. Introduce and unpack `z -`.

Establish `hz : (snd G X).left z.1 ∈ D` using `z.2`. Establish `h1 : (γ[G, X] : G ⊗ X ⟶ X).left z.1 ∈ orbit G X ((snd G X).left z.1)` using `(mem_orbit_iff G X).2 ⟨z.1, rfl, rfl⟩`. Conclude with `(hfV hz h1).1`. Take `⟨N, hN⟩` from `exists_norm ((snd G X).left ∣_ D) hfree' ((c.appLE U ⊤ hc).hom f)`. Set `V : X.left.Opens` to `D.ι ''ᵁ (D.toScheme.basicOpen N)`.

Establish `hVmem : ∀ y, y ∈ V ↔ y ∈ D ∧ orbit G X y ⊆ D`. Introduce `y`. Use `show y ∈ D.ι '' (D.toScheme.basicOpen N : Set D.toScheme) ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y', hy', rfl⟩`.

Use `⟨y'.2, fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨z, hz, rfl⟩` from `(mem_orbit_iff G X).1 hw`. Establish `hzP : z ∈ P'` using `by show (snd G X).left z ∈ D`. Rewrite using `[hz]`. Conclude with `y'.2`.

Establish `h1` using `(hN y').1 hy' ⟨z, hzP⟩ (Subtype.ext ((morphismRestrict_base_coe _ _ _).trans hz))`. Conclude with `(mem_basicOpen_appLE' c U hc f _).1 h1`. Introduce and unpack `⟨hyD, ho⟩`. Use `⟨⟨y, hyD⟩, (hN ⟨y, hyD⟩).2 fun z hz => ?_, rfl⟩` and prove the remaining obligations. Use `(mem_basicOpen_appLE' c U hc f _).2 ?_` and prove the remaining obligations.

Establish `h2 : (snd G X).left z.1 = y` using `(morphismRestrict_base_coe _ _ z).symm.trans (congrArg Subtype.val hz)`. Conclude with `ho ((mem_orbit_iff G X).2 ⟨z.1, h2, rfl⟩)`. Use `⟨V, W, (hVmem x).2 ⟨hKf (GlobalTheory.T.mem_orbit_self' G X x), fun y hy => hKf hy⟩, ?_, hW, ?_, ?_⟩` and prove the remaining obligations. Conclude with `((isAffineOpen_top D.toScheme).basicOpen N).image_of_isOpenImmersion D.ι`. Conclude with `fun y hy => hDW ((hVmem y).1 hy).1`.

Use `stable_of_forall G X V fun y hy w hw => (hVmem w).2 ⟨((hVmem y).1 hy).2 hw, fun t ht => ?_⟩` and prove the remaining obligations. Conclude with `((hVmem y).1 hy).2 (GlobalTheory.T.mem_orbit_trans G X y w t hw ht)`.
-/
theorem exists_stable_affine_nbhd : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X], IsFiniteLocallyFree G.hom → ∀ (x : X.left) (U : X.left.Opens), IsAffineOpen U → orbit G X x ⊆ U → ∃ (V : X.left.Opens) (W : S.Opens), x ∈ V ∧ IsAffineOpen V ∧ IsAffineOpen W ∧ V ≤ X.hom ⁻¹ᵁ W ∧ (γ[G, X] : G ⊗ X ⟶ X).left ⁻¹ᵁ V = (snd G X).left ⁻¹ᵁ V := by
  intro S G X _ _ hG x U hU hxU
  have hfl := hG.1
  have hfl2 := hG.2.1
  have hfl3 := hG.2.2
  obtain ⟨W, hsW, hW, hfree⟩ := GlobalTheory.T.finite_flat_locally_free_affine G.hom (X.hom x)
  have htrans : ∀ {y w : X.left}, y ∈ orbit G X x → w ∈ orbit G X y → w ∈ orbit G X x :=
    fun {y w} => GlobalTheory.T.mem_orbit_trans G X x y w
  let O : X.left.Opens := U ⊓ X.hom ⁻¹ᵁ W
  have hxO : orbit G X x ⊆ O := fun y hy => ⟨hxU hy, by
    show X.hom y ∈ W
    rw [orbit_hom G X hy]; exact hsW⟩
  let V₀ : X.left.Opens := ⟨{y | orbit G X y ⊆ O}, isOpen_saturated hG O⟩
  have hV₀O : V₀ ≤ O := fun y hy => hy (GlobalTheory.T.mem_orbit_self' G X y)
  have hV₀U : V₀ ≤ U := hV₀O.trans inf_le_left
  have hxV₀ : orbit G X x ⊆ V₀ := fun y hy w hw => hxO (htrans hy hw)
  obtain ⟨f, hKf, hfV⟩ := GlobalTheory.T.finite_set_basic_open_affine U V₀ hU hV₀U _ (orbit_finite hG x) hxV₀
  let D : X.left.Opens := X.left.basicOpen f
  have hD : IsAffineOpen D := hU.basicOpen f
  have hDW : D ≤ X.hom ⁻¹ᵁ W := (hfV.trans hV₀O).trans inf_le_right
  have hsq : IsPullback (fst G X).left (snd G X).left G.hom X.hom :=
    IsPullback.of_hasPullback G.hom X.hom
  obtain ⟨h, u, hpb⟩ := GlobalTheory.T.pullback_restrict_open hsq W D hDW
  have := isFinite_snd (X := X) hG
  haveI : IsAffine D.toScheme := hD
  haveI : IsAffine W.toScheme := hW
  haveI : IsAffine (G.hom ⁻¹ᵁ W).toScheme := hW.preimage G.hom
  haveI : IsAffine ((snd G X).left ⁻¹ᵁ D).toScheme := hD.preimage (snd G X).left
  have hfree' := GlobalTheory.T.finite_free_pullback_affine hpb hfree
  let P' : (G ⊗ X).left.Opens := (snd G X).left ⁻¹ᵁ D
  let c : P'.toScheme ⟶ X.left := P'.ι ≫ (γ[G, X] : G ⊗ X ⟶ X).left
  have hc : ⊤ ≤ c ⁻¹ᵁ U := by
    rintro z -
    have hz : (snd G X).left z.1 ∈ D := z.2
    have h1 : (γ[G, X] : G ⊗ X ⟶ X).left z.1 ∈ orbit G X ((snd G X).left z.1) :=
      (mem_orbit_iff G X).2 ⟨z.1, rfl, rfl⟩
    exact (hfV hz h1).1
  obtain ⟨N, hN⟩ := exists_norm ((snd G X).left ∣_ D) hfree' ((c.appLE U ⊤ hc).hom f)
  let V : X.left.Opens := D.ι ''ᵁ (D.toScheme.basicOpen N)
  have hVmem : ∀ y, y ∈ V ↔ y ∈ D ∧ orbit G X y ⊆ D := by
    intro y
    show y ∈ D.ι '' (D.toScheme.basicOpen N : Set D.toScheme) ↔ _
    constructor
    · rintro ⟨y', hy', rfl⟩
      refine ⟨y'.2, fun w hw => ?_⟩
      obtain ⟨z, hz, rfl⟩ := (mem_orbit_iff G X).1 hw
      have hzP : z ∈ P' := by
        show (snd G X).left z ∈ D
        rw [hz]; exact y'.2
      have h1 := (hN y').1 hy' ⟨z, hzP⟩ (Subtype.ext ((morphismRestrict_base_coe _ _ _).trans hz))
      exact (mem_basicOpen_appLE' c U hc f _).1 h1
    · rintro ⟨hyD, ho⟩
      refine ⟨⟨y, hyD⟩, (hN ⟨y, hyD⟩).2 fun z hz => ?_, rfl⟩
      refine (mem_basicOpen_appLE' c U hc f _).2 ?_
      have h2 : (snd G X).left z.1 = y :=
        (morphismRestrict_base_coe _ _ z).symm.trans (congrArg Subtype.val hz)
      exact ho ((mem_orbit_iff G X).2 ⟨z.1, h2, rfl⟩)
  refine ⟨V, W, (hVmem x).2 ⟨hKf (GlobalTheory.T.mem_orbit_self' G X x), fun y hy => hKf hy⟩, ?_, hW, ?_, ?_⟩
  · exact ((isAffineOpen_top D.toScheme).basicOpen N).image_of_isOpenImmersion D.ι
  · exact fun y hy => hDW ((hVmem y).1 hy).1
  · refine stable_of_forall G X V fun y hy w hw => (hVmem w).2 ⟨((hVmem y).1 hy).2 hw, fun t ht => ?_⟩
    exact ((hVmem y).1 hy).2 (GlobalTheory.T.mem_orbit_trans G X y w t hw ht)

end GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
