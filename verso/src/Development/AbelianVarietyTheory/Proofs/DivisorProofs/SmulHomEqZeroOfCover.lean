import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoRestrictPushforwardUnit

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.ChainPts GlobalTheory.LocFreeQuot
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LocFreeProj

variable {X : Scheme.{0}}

/- English proof (translation)
Use `Scheme.Modules.hom_ext _ _ fun W => ?_` and prove the remaining obligations. Use extensionality with `s`. Use `Twist.sec_ext_of_cover (fun U : {U : X.affineOpens // U.1 ≤ W} => U.1.1) (fun U => U.2) (fun x hW => ?_) fun U => ?_` and prove the remaining obligations. Take `⟨_, ⟨U, hU, rfl⟩, hx, hle⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open hW W.2`. Conclude with `Opens.mem_iSup.2 ⟨⟨⟨U, hU⟩, hle⟩, hx⟩`.

Rewrite using `[← Twist.app_resM, ← Twist.app_resM, h _ U.1.2]`. Both sides reduce to the same expression.
-/
theorem eq_zero_of_affine {F G : X.Modules} (φ : F ⟶ G)
    (h : ∀ W : X.Opens, IsAffineOpen W → ∀ s, φ.app W s = 0) : φ = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun W => ?_
  ext s
  refine Twist.sec_ext_of_cover (fun U : {U : X.affineOpens // U.1 ≤ W} => U.1.1) (fun U => U.2) (fun x hW => ?_) fun U => ?_
  · obtain ⟨_, ⟨U, hU, rfl⟩, hx, hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hW W.2
    exact Opens.mem_iSup.2 ⟨⟨⟨U, hU⟩, hle⟩, hx⟩
  · rw [← Twist.app_resM, ← Twist.app_resM, h _ U.1.2]
    rfl

/- English proof (translation)
Use `eq_zero_of_locally _ fun x => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `Opens.mem_iSup.1 (show x ∈ iSup V by rw [hc]; trivial)`. Use `⟨V i, hi, ?_⟩` and prove the remaining obligations. Rewrite using `[VB.pullback_map_smulHom]`. Use `eq_zero_of_affine _ fun W hW s => ?_` and prove the remaining obligations.

Establish `e : W ≤ (V i).ι ⁻¹ᵁ V i` using `fun y _ => y.2`. Rewrite using `[smulHom_app_apply]`. Establish `e₀ : restrictGlobal _ W ((V i).ι.appTop g) = (V i).ι.appLE (V i) W e (resG X (le_top : V i ≤ ⊤) g)`. Express the relevant statement in the definitionally equal form `((V i).ι.appTop ≫ (V i).toScheme.presheaf.map _) g = (X.presheaf.map _ ≫ (V i).ι.appLE (V i) W e) g`. Rewrite using `[Scheme.Hom.map_appLE]`.

Both sides reduce to the same expression. Rewrite using `[e₀]`. Use `letI := appLEAlgebra (V i).ι e`. Use `letI := appLEModule (V i).ι ((Scheme.Modules.pullback (V i).ι).obj F) e`. Use `haveI := appLE_isScalarTower (V i).ι ((Scheme.Modules.pullback (V i).ι).obj F) e`.

Proceed by induction on `s using (isBaseChange_pullbackSections (V i).ι F hW (hV i) e).inductionOn with`. Consider the case `zero => exact smul_zero _`. Consider the case `tmul m => rw [← pullbackSections_smul, h, map_zero]`. Consider the case `smul a m hm => rw [smul_comm, hm, smul_zero]`. Consider the case `add m n hm hn => rw [smul_add, hm, hn, add_zero]`.
-/
theorem smulHom_eq_zero_of_cover (F : X.Modules) [F.IsQuasicoherent] (g : Γ(X, ⊤)) {ι : Type} (V : ι → X.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hc : iSup V = ⊤)
    (h : ∀ i (s : Γ(F, V i)), resG X (le_top : V i ≤ ⊤) g • s = 0) : smulHom F g = 0 := by
  refine eq_zero_of_locally _ fun x => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show x ∈ iSup V by rw [hc]; trivial)
  refine ⟨V i, hi, ?_⟩
  rw [VB.pullback_map_smulHom]
  refine eq_zero_of_affine _ fun W hW s => ?_
  have e : W ≤ (V i).ι ⁻¹ᵁ V i := fun y _ => y.2
  rw [smulHom_app_apply]
  have e₀ : restrictGlobal _ W ((V i).ι.appTop g) = (V i).ι.appLE (V i) W e (resG X (le_top : V i ≤ ⊤) g) := by
    change ((V i).ι.appTop ≫ (V i).toScheme.presheaf.map _) g = (X.presheaf.map _ ≫ (V i).ι.appLE (V i) W e) g
    rw [Scheme.Hom.map_appLE]
    rfl
  rw [e₀]
  letI := appLEAlgebra (V i).ι e
  letI := appLEModule (V i).ι ((Scheme.Modules.pullback (V i).ι).obj F) e
  haveI := appLE_isScalarTower (V i).ι ((Scheme.Modules.pullback (V i).ι).obj F) e
  induction s using (isBaseChange_pullbackSections (V i).ι F hW (hV i) e).inductionOn with
  | zero => exact smul_zero _
  | tmul m => rw [← pullbackSections_smul, h, map_zero]
  | smul a m hm => rw [smul_comm, hm, smul_zero]
  | add m n hm hn => rw [smul_add, hm, hn, add_zero]

/- English proof (translation)
Use `letI : Algebra (A ⧸ I) B := (Ideal.Quotient.lift I (algebraMap A B) hI).toAlgebra`. Use `haveI : IsScalarTower A (A ⧸ I) B := .of_algebraMap_eq fun _ => rfl`. Conclude with `.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ I) B B M)`.
-/
theorem projective_of_quot {A B M : Type} [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M] (I : Ideal A)
    (hI : ∀ a ∈ I, algebraMap A B a = 0) [Module.Projective (A ⧸ I) ((A ⧸ I) ⊗[A] M)] :
    Module.Projective B (B ⊗[A] M) := by
  letI : Algebra (A ⧸ I) B := (Ideal.Quotient.lift I (algebraMap A B) hI).toAlgebra
  haveI : IsScalarTower A (A ⧸ I) B := .of_algebraMap_eq fun _ => rfl
  exact .of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ I) B B M)

/- English proof (translation)
Set `ι` to `(idl g).subschemeι`. Establish `e : ι ⁻¹ᵁ U ≤ ι ⁻¹ᵁ U` using `le_rfl`. Establish `hW : IsAffineOpen (ι ⁻¹ᵁ U)` using `hU.preimage ι`. Use `letI := appLEAlgebra ι e`. Use `letI := appLEModule ι ((Scheme.Modules.pullback ι).obj F) e`.

Use `haveI := appLE_isScalarTower ι ((Scheme.Modules.pullback ι).obj F) e`. Establish `hb` using `isBaseChange_pullbackSections ι F hW hU e`. Use `haveI := finite_sections_pullback ι F hW hU e`. Establish `h0 : ι.appLE U _ e (resG X (le_top : U ≤ ⊤) g) = 0`. Establish `e₀ : ι.appLE U _ e (resG X (le_top : U ≤ ⊤) g) = restrictGlobal _ (ι ⁻¹ᵁ U) (ι.appTop g)`.

Express the relevant statement in the definitionally equal form `(X.presheaf.map _ ≫ ι.appLE U _ e) g = (ι.appTop ≫ (idl g).subscheme.presheaf.map _) g`. Rewrite using `[Scheme.Hom.map_appLE]`. Both sides reduce to the same expression. Rewrite using `[e₀, appTop_idl, map_zero]`. Use `haveI := projective_of_quot (B := Γ((idl g).subscheme, ι ⁻¹ᵁ U)) (M := Γ(F, U)) (Ideal.span {resG X (le_top : U ≤ ⊤) g}) fun a ha => by`.

Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 ha`. Rewrite using `[map_mul]`. Conclude with `mul_eq_zero_of_right _ h0`. Use `haveI := Module.Projective.of_equiv hb.equiv`. Conclude with `VB.Summand.exists_frame_of_projective (G := (Scheme.Modules.pullback ι).obj F) hW ⟨z, hz⟩`.
-/
theorem exists_frame (F : X.Modules) [F.IsQuasicoherent] (g : Γ(X, ⊤)) {U : X.Opens} (hU : IsAffineOpen U)
    [Module.Finite Γ(X, U) Γ(F, U)]
    [Module.Projective (Γ(X, U) ⧸ Ideal.span {resG X (le_top : U ≤ ⊤) g})
      ((Γ(X, U) ⧸ Ideal.span {resG X (le_top : U ≤ ⊤) g}) ⊗[Γ(X, U)] Γ(F, U))]
    (z : (idl g).subscheme) (hz : (idl g).subschemeι z ∈ U) :
    ∃ (W : (idl g).subscheme.Opens) (n : ℕ) (e : Fin n → Γ((Scheme.Modules.pullback (idl g).subschemeι).obj F, W)),
      z ∈ W ∧ VB.IsFrame e := by
  let ι := (idl g).subschemeι
  have e : ι ⁻¹ᵁ U ≤ ι ⁻¹ᵁ U := le_rfl
  have hW : IsAffineOpen (ι ⁻¹ᵁ U) := hU.preimage ι
  letI := appLEAlgebra ι e
  letI := appLEModule ι ((Scheme.Modules.pullback ι).obj F) e
  haveI := appLE_isScalarTower ι ((Scheme.Modules.pullback ι).obj F) e
  have hb := isBaseChange_pullbackSections ι F hW hU e
  haveI := finite_sections_pullback ι F hW hU e
  have h0 : ι.appLE U _ e (resG X (le_top : U ≤ ⊤) g) = 0 := by
    have e₀ : ι.appLE U _ e (resG X (le_top : U ≤ ⊤) g) = restrictGlobal _ (ι ⁻¹ᵁ U) (ι.appTop g) := by
      change (X.presheaf.map _ ≫ ι.appLE U _ e) g = (ι.appTop ≫ (idl g).subscheme.presheaf.map _) g
      rw [Scheme.Hom.map_appLE]
      rfl
    rw [e₀, appTop_idl, map_zero]
  haveI := projective_of_quot (B := Γ((idl g).subscheme, ι ⁻¹ᵁ U)) (M := Γ(F, U))
    (Ideal.span {resG X (le_top : U ≤ ⊤) g}) fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul]
      exact mul_eq_zero_of_right _ h0
  haveI := Module.Projective.of_equiv hb.equiv
  exact VB.Summand.exists_frame_of_projective (G := (Scheme.Modules.pullback ι).obj F) hW ⟨z, hz⟩

/- English proof (translation)
Take `⟨e₁⟩` from `nonempty_iso_pushforward g F hk`. Set `ι` to `(idl g).subschemeι`. Establish `key (x : X) (U : X.Opens) (r : ℕ) (hx : x ∈ U) (T : Scheme.{0}) (j : T ⟶ (idl g).subscheme) [IsOpenImmersion j] (hj : ι ⁻¹ᵁ U ≤ j.opensRange) (e : (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback ι).obj F) ≅ (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback ι).ob …`. Take `⟨e₂⟩` from `nonempty_iso_pushforward g (quot r g) (smulHom_quot r g)`. Take `⟨e₃⟩` from `nonempty_pullback_pushforward ι j U hj e`.

Conclude with `⟨U, r, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso e₁ ≪≫ e₃ ≪≫ ((Scheme.Modules.pullback U.ι).mapIso e₂).symm⟩⟩`. Establish `hfree (r : ℕ) : Nonempty ((Scheme.Modules.pullback ι).obj (quot r g) ≅ freeModule _ (Fin r))`. Take `⟨e⟩` from `nonempty_pullback_quot ι r g 0 (appTop_idl g)`. Conclude with `⟨e ≪≫ cokernelIsoOfEq (smulHom_zero _) ≪≫ cokernelZeroIsoTarget⟩`. Introduce `x`.

Distinguish the cases in `hx : x ∈ Set.range ι`. Take `⟨z, rfl⟩` from `hx`. Take `⟨V, n, s, hzV, hs⟩` from `hf z`. Establish `e₄` using `hs.restrictIso ((VB.isFrame_freeFrame _ (Fin n)).res le_top) V.ι V.opensRange_ι.le`. Take `⟨e₅⟩` from `hfree n`.

Take `⟨W, hW, hWe⟩` from `ι.isClosedEmbedding.isInducing.isOpen_iff.1 V.ι.opensRange.isOpen`. Use `key _ ⟨W, hW⟩ n ?_ _ V.ι hWe.le ?_` and prove the remaining obligations. Establish `: z ∈ ι ⁻¹' W`. Rewrite using `[hWe]`. Conclude with `⟨⟨z, hzV⟩, rfl⟩`.

Conclude with `this`. Conclude with `((Scheme.Modules.restrictFunctorIsoPullback V.ι).app _).symm ≪≫ e₄ ≪≫ (Scheme.Modules.restrictFunctor V.ι).mapIso e₅.symm ≪≫ (Scheme.Modules.restrictFunctorIsoPullback V.ι).app _`. Establish `hz (G : (⊥ : (idl g).subscheme.Opens).toScheme.Modules) : IsZero G` using `support_eq_empty_iff.1 (Set.eq_empty_of_forall_notMem fun y _ => y.2)`. Use `key x ⟨(Set.range ι)ᶜ, ι.isClosedEmbedding.isClosed_range.isOpen_compl⟩ 0 hx _ (⊥ : (idl g).subscheme.Opens).ι (fun y hy => (hy ⟨y, rfl⟩).elim) ((hz _).iso (hz _))` and prove the remaining obligations.
-/
theorem locFreeMod_of_frame (F : X.Modules) [F.IsQuasicoherent] (g : Γ(X, ⊤)) (hk : smulHom F g = 0)
    (hf : ∀ z : (idl g).subscheme, ∃ (W : (idl g).subscheme.Opens) (n : ℕ)
      (e : Fin n → Γ((Scheme.Modules.pullback (idl g).subschemeι).obj F, W)), z ∈ W ∧ VB.IsFrame e) :
    LocFreeMod g F := by
  obtain ⟨e₁⟩ := nonempty_iso_pushforward g F hk
  let ι := (idl g).subschemeι
  have key (x : X) (U : X.Opens) (r : ℕ) (hx : x ∈ U) (T : Scheme.{0}) (j : T ⟶ (idl g).subscheme)
      [IsOpenImmersion j] (hj : ι ⁻¹ᵁ U ≤ j.opensRange)
      (e : (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback ι).obj F) ≅
        (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback ι).obj (quot r g))) :
      ∃ (U : X.Opens) (r : ℕ), x ∈ U ∧ Nonempty ((Scheme.Modules.pullback U.ι).obj F ≅
        (Scheme.Modules.pullback U.ι).obj (quot r g)) := by
    obtain ⟨e₂⟩ := nonempty_iso_pushforward g (quot r g) (smulHom_quot r g)
    obtain ⟨e₃⟩ := nonempty_pullback_pushforward ι j U hj e
    exact ⟨U, r, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso e₁ ≪≫ e₃ ≪≫
      ((Scheme.Modules.pullback U.ι).mapIso e₂).symm⟩⟩
  have hfree (r : ℕ) : Nonempty ((Scheme.Modules.pullback ι).obj (quot r g) ≅ freeModule _ (Fin r)) := by
    obtain ⟨e⟩ := nonempty_pullback_quot ι r g 0 (appTop_idl g)
    exact ⟨e ≪≫ cokernelIsoOfEq (smulHom_zero _) ≪≫ cokernelZeroIsoTarget⟩
  intro x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨z, rfl⟩ := hx
    obtain ⟨V, n, s, hzV, hs⟩ := hf z
    have e₄ := hs.restrictIso ((VB.isFrame_freeFrame _ (Fin n)).res le_top) V.ι V.opensRange_ι.le
    obtain ⟨e₅⟩ := hfree n
    obtain ⟨W, hW, hWe⟩ := ι.isClosedEmbedding.isInducing.isOpen_iff.1 V.ι.opensRange.isOpen
    refine key _ ⟨W, hW⟩ n ?_ _ V.ι hWe.le ?_
    · have : z ∈ ι ⁻¹' W := by
        rw [hWe]
        exact ⟨⟨z, hzV⟩, rfl⟩
      exact this
    · exact ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app _).symm ≪≫ e₄ ≪≫
        (Scheme.Modules.restrictFunctor V.ι).mapIso e₅.symm ≪≫ (Scheme.Modules.restrictFunctorIsoPullback V.ι).app _
  · have hz (G : (⊥ : (idl g).subscheme.Opens).toScheme.Modules) : IsZero G :=
      support_eq_empty_iff.1 (Set.eq_empty_of_forall_notMem fun y _ => y.2)
    refine key x ⟨(Set.range ι)ᶜ, ι.isClosedEmbedding.isClosed_range.isOpen_compl⟩ 0 hx _
      (⊥ : (idl g).subscheme.Opens).ι (fun y hy => (hy ⟨y, rfl⟩).elim) ((hz _).iso (hz _))

/- English proof (translation)
Introduce `X F _ g ι V hV hc h`. Use `locFreeMod_of_frame F g (smulHom_eq_zero_of_cover F g V hV hc fun i => (h i).2.1) fun z => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `Opens.mem_iSup.1 (show (idl g).subschemeι z ∈ iSup V by rw [hc]; trivial)`. Use `haveI := (h i).1`. Use `haveI := (h i).2.2`.

Conclude with `exists_frame F g (hV i) z hi`.
-/
theorem main : ∀ (X : Scheme.{0}) (F : X.Modules) [F.IsQuasicoherent] (g : Γ(X, ⊤)) (ι : Type) (V : ι → X.Opens), (∀ i, IsAffineOpen (V i)) → iSup V = ⊤ → (∀ i, Module.Finite Γ(X, V i) Γ(F, V i) ∧ (∀ s : Γ(F, V i), resG X (le_top : V i ≤ ⊤) g • s = 0) ∧ Module.Projective (Γ(X, V i) ⧸ Ideal.span {resG X (le_top : V i ≤ ⊤) g}) ((Γ(X, V i) ⧸ Ideal.span {resG X (le_top : V i ≤ ⊤) g}) ⊗[Γ(X, V i)] Γ(F, V i))) → LocFreeMod g F := by
  intro X F _ g ι V hV hc h
  refine locFreeMod_of_frame F g (smulHom_eq_zero_of_cover F g V hV hc fun i => (h i).2.1) fun z => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show (idl g).subschemeι z ∈ iSup V by rw [hc]; trivial)
  haveI := (h i).1
  haveI := (h i).2.2
  exact exists_frame F g (hV i) z hi

end GlobalTheory.LocFreeProj

end
