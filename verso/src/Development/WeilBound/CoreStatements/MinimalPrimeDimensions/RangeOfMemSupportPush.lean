import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberEqGenericRankMulProjCurve
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.VB

namespace ChowFormHeightComparison₂.CF.V

section Stalk

variable {X Y : Scheme.{0}} (i : Y ⟶ X) [IsClosedImmersion i] (G : Y.Modules)

def pushStalk (y : Y) :
    (((Scheme.Modules.pushforward i).obj G).presheaf.stalk (i y) :) →+ (G.presheaf.stalk y :) :=
  (TopCat.Presheaf.stalkPushforward Ab.{0} i.base G.presheaf y).hom

omit [IsClosedImmersion i] in
/- English proof (translation)
The claim follows from `TopCat.Presheaf.stalkPushforward_germ_apply Ab.{0} i.base G.presheaf U y h s`.
-/
theorem pushStalk_germ (y : Y) (U : X.Opens) (h : i y ∈ U) (s : Γ((Scheme.Modules.pushforward i).obj G, U)) :
    pushStalk i G y (((Scheme.Modules.pushforward i).obj G).presheaf.germ U (i y) h s) =
      G.presheaf.germ (i ⁻¹ᵁ U) y h s :=
  TopCat.Presheaf.stalkPushforward_germ_apply Ab.{0} i.base G.presheaf U y h s

/- English proof (translation)
The claim follows from `have := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing Ab.{0} (f := i.base) i.isClosedEmbedding.isInducing G.presheaf y ConcreteCategory.bijective_of_isIso (TopCat.Presheaf.stalkPushforward Ab.{0} i.base G.presheaf y)`.
-/
theorem pushStalk_bijective (y : Y) : Function.Bijective (pushStalk i G y) :=
  have := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing Ab.{0} (f := i.base)
    i.isClosedEmbedding.isInducing G.presheaf y
  ConcreteCategory.bijective_of_isIso (TopCat.Presheaf.stalkPushforward Ab.{0} i.base G.presheaf y)

omit [IsClosedImmersion i] in
/- English proof (translation)
Take `⟨U, hU, a, rfl⟩` from `X.presheaf.exists_germ_eq r`. Take `⟨V, hVU, hV, s, rfl⟩` from `Twist.exists_germ_eq_of_mem hU t`. Rewrite using `[← X.presheaf.germ_res_apply (homOfLE hVU) (i y) hV a, ← QCoh.germ_smul, pushStalk_germ, pushStalk_germ, Scheme.Hom.germ_stalkMap_apply]`. Conclude with `QCoh.germ_smul (F := G) (U := i ⁻¹ᵁ V) y hV _ s`.
-/
theorem pushStalk_smul (y : Y) (r : X.presheaf.stalk (i y))
    (t : (((Scheme.Modules.pushforward i).obj G).presheaf.stalk (i y) :)) :
    pushStalk i G y (r • t) = i.stalkMap y r • pushStalk i G y t := by
  obtain ⟨U, hU, a, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hVU, hV, s, rfl⟩ := Twist.exists_germ_eq_of_mem hU t
  rw [← X.presheaf.germ_res_apply (homOfLE hVU) (i y) hV a, ← QCoh.germ_smul, pushStalk_germ, pushStalk_germ,
    Scheme.Hom.germ_stalkMap_apply]
  exact QCoh.germ_smul (F := G) (U := i ⁻¹ᵁ V) y hV _ s

/- English proof (translation)
Use `letI := (i.stalkMap y).hom.toAlgebra`. Use `letI : Module (X.presheaf.stalk (i y)) (G.presheaf.stalk y :) := Module.compHom _ (i.stalkMap y).hom`. Use `haveI : IsScalarTower (X.presheaf.stalk (i y)) (Y.presheaf.stalk y) (G.presheaf.stalk y :) := .of_algebraMap_smul fun _ _ => rfl`. Set `l : (((Scheme.Modules.pushforward i).obj G).presheaf.stalk (i y) :) →ₗ[X.presheaf.stalk (i y)] (G.presheaf.stalk y :)` to `{ toFun := pushStalk i G y, map_add' := map_add _, map_smul' := pushStalk_smul i G y }`. Rewrite using `[(LinearEquiv.ofBijective l (pushStalk_bijective i G y)).length_eq]`.

Conclude with `Module.length_eq_of_surjective (S := X.presheaf.stalk (i y)) (i.stalkMap_surjective y)`.
-/
theorem length_push (y : Y) :
    Module.length (X.presheaf.stalk (i y)) (((Scheme.Modules.pushforward i).obj G).presheaf.stalk (i y) :) =
      Module.length (Y.presheaf.stalk y) (G.presheaf.stalk y :) := by
  letI := (i.stalkMap y).hom.toAlgebra
  letI : Module (X.presheaf.stalk (i y)) (G.presheaf.stalk y :) := Module.compHom _ (i.stalkMap y).hom
  haveI : IsScalarTower (X.presheaf.stalk (i y)) (Y.presheaf.stalk y) (G.presheaf.stalk y :) :=
    .of_algebraMap_smul fun _ _ => rfl
  let l : (((Scheme.Modules.pushforward i).obj G).presheaf.stalk (i y) :) →ₗ[X.presheaf.stalk (i y)]
      (G.presheaf.stalk y :) :=
    { toFun := pushStalk i G y, map_add' := map_add _, map_smul' := pushStalk_smul i G y }
  rw [(LinearEquiv.ofBijective l (pushStalk_bijective i G y)).length_eq]
  exact Module.length_eq_of_surjective (S := X.presheaf.stalk (i y)) (i.stalkMap_surjective y)

/- English proof (translation)
The claim follows from `(Equiv.ofBijective _ (pushStalk_bijective i G y)).nontrivial_congr`.
-/
theorem mem_support_push (y : Y) :
    i y ∈ support ((Scheme.Modules.pushforward i).obj G) ↔ y ∈ support G :=
  (Equiv.ofBijective _ (pushStalk_bijective i G y)).nontrivial_congr

/- English proof (translation)
Assume the negation of the conclusion as `hr`. Rewrite `hx` using `[mem_support_iff, ← not_subsingleton_iff_nontrivial]`. Use `hx (subsingleton_of_forall_eq 0 fun t => ?_)` and prove the remaining obligations. Set `W : X.Opens` to `⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩`. Take `⟨V, hVW, hV, s, rfl⟩` from `Twist.exists_germ_eq_of_mem (U := W) hr t`.

Establish `h0 : s = 0` using `section_eq_zero_of_germ (F := G) _ fun z hz => absurd ⟨z, rfl⟩ (hVW hz)`. Rewrite using `[h0, map_zero]`.
-/
theorem range_of_mem_support_push {x : X} (hx : x ∈ support ((Scheme.Modules.pushforward i).obj G)) :
    x ∈ Set.range i := by
  by_contra hr
  rw [mem_support_iff, ← not_subsingleton_iff_nontrivial] at hx
  refine hx (subsingleton_of_forall_eq 0 fun t => ?_)
  let W : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  obtain ⟨V, hVW, hV, s, rfl⟩ := Twist.exists_germ_eq_of_mem (U := W) hr t
  have h0 : s = 0 := section_eq_zero_of_germ (F := G) _ fun z hz => absurd ⟨z, rfl⟩ (hVW hz)
  rw [h0, map_zero]

end Stalk

variable {κ : Type} [Field κ]

/- English proof (translation)
Establish `hf` using `algebraMap_eq_strHom κ Z`. Establish `h1 : ∀ {F : Z.Modules} [QCoh.IsFiniteQC F], FiniteCohTwists κ F` using `fun {F} _ => finiteCohTwists_of_isProjOver hf F hp`. Take `⟨_, A, hA⟩` from `isProper_and_exists_isAmpleLB_of_isProjOver hp`. Proceed by induction on `r with`. Consider the case `zero`.

Introduce `G _ h`. Establish `h0` using `topologicalKrullDim_add_one_le (QCoh.isClosed_support G) isClosed_univ fun x _ => ⟨genericPoint Z, trivial, genRank_eq_zero_iff.1 h, genericPoint_specializes x⟩`. Establish `h2 : topologicalKrullDim (Set.univ : Set Z) = topologicalKrullDim Z` using `(Homeomorph.Set.univ Z).isHomeomorph.topologicalKrullDim_eq`. Establish `: QCoh.suppDim G < Fintype.card (Fin d)`. Rewrite using `[Fintype.card_fin]`.

Assume the negation of the conclusion as `hc`. Rewrite `hc` using `[not_lt]`. Establish `h3 : ((d : ℕ) : WithBot ℕ∞) + 1 ≤ d` using `(add_le_add_left hc 1).trans (h0.trans (h2.le.trans hd))`. Establish `h4 : d + 1 ≤ d` using `by exact_mod_cast h3`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[interNum_eq_zero_of_isProjOver hf G hp this hL]`. Simplify using the standard rewrite rules. Consider the case `succ r ih`. Introduce `G _ h`. Take `⟨n, hn⟩` from `(hA.eventually_isGloballyGenerated_twist G).exists`.

Establish `hM` using `isLB_lbPow hA.isLB n`. Use `Twist.isFiniteQC_twist (F := G) hM` as an intermediate fact. Establish `hr : genRank (twist G (lbPow A n)) = r + 1` using `(genRank_twist hM).trans h`. Take `⟨s, hs⟩` from `exists_germ_ne_zero hn (by omega)`. Use `mono_sectionHom s hs` as an intermediate fact.

Establish `e₁ : interNum κ (twist G (lbPow A n)) P = interNum κ G P` using `(diffVanish_chiPic_of_isProjOver (d := d) hf G hp ((QCoh.suppDim_le G).trans hd)).interNum_twist (by simp) hL hM`. Establish `e₂` using `interNum_cokernel (k := κ) (QCoh.sectionHom s) hL h1 h1`. Establish `e₃` using `genRank_cokernel (QCoh.sectionHom s)`. Rewrite `e₃` using `[(isVB_structureModule Z).genRank_eq, hr]`. Rewrite `e₂` using `[ih _ (by omega)]`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem interNum_of_genRank_eq {Z : Scheme.{0}} [IsIntegral Z] [Algebra κ Γ(Z, ⊤)] (hp : IsProjOver (strHom κ Z))
    {d : ℕ} (hd : topologicalKrullDim Z ≤ d) {P : Fin d → LB Z} (hL : ∀ j, (P j).IsLB) (r : ℕ) :
    ∀ (G : Z.Modules) [QCoh.IsFiniteQC G], genRank G = r →
      interNum κ G P = r * interNum κ (GlobalTheory.structureModule Z) P := by
  have hf := algebraMap_eq_strHom κ Z
  have h1 : ∀ {F : Z.Modules} [QCoh.IsFiniteQC F], FiniteCohTwists κ F :=
    fun {F} _ => finiteCohTwists_of_isProjOver hf F hp
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  induction r with
  | zero =>
    intro G _ h
    have h0 := topologicalKrullDim_add_one_le (QCoh.isClosed_support G) isClosed_univ
      fun x _ => ⟨genericPoint Z, trivial, genRank_eq_zero_iff.1 h, genericPoint_specializes x⟩
    have h2 : topologicalKrullDim (Set.univ : Set Z) = topologicalKrullDim Z :=
      (Homeomorph.Set.univ Z).isHomeomorph.topologicalKrullDim_eq
    have : QCoh.suppDim G < Fintype.card (Fin d) := by
      rw [Fintype.card_fin]
      by_contra hc
      rw [not_lt] at hc
      have h3 : ((d : ℕ) : WithBot ℕ∞) + 1 ≤ d := (add_le_add_left hc 1).trans (h0.trans (h2.le.trans hd))
      have h4 : d + 1 ≤ d := by exact_mod_cast h3
      omega
    rw [interNum_eq_zero_of_isProjOver hf G hp this hL]
    simp
  | succ r ih =>
    intro G _ h
    obtain ⟨n, hn⟩ := (hA.eventually_isGloballyGenerated_twist G).exists
    have hM := isLB_lbPow hA.isLB n
    have := Twist.isFiniteQC_twist (F := G) hM
    have hr : genRank (twist G (lbPow A n)) = r + 1 := (genRank_twist hM).trans h
    obtain ⟨s, hs⟩ := exists_germ_ne_zero hn (by omega)
    have := mono_sectionHom s hs
    have e₁ : interNum κ (twist G (lbPow A n)) P = interNum κ G P :=
      (diffVanish_chiPic_of_isProjOver (d := d) hf G hp
        ((QCoh.suppDim_le G).trans hd)).interNum_twist (by simp) hL hM
    have e₂ := interNum_cokernel (k := κ) (QCoh.sectionHom s) hL h1 h1
    have e₃ := genRank_cokernel (QCoh.sectionHom s)
    rw [(isVB_structureModule Z).genRank_eq, hr] at e₃
    rw [ih _ (by omega)] at e₂
    push_cast
    linarith

/- English proof (translation)
Use `isNoetherian_of_isProjOver hp` as an intermediate fact. Establish `hf` using `algebraMap_eq_strHom κ X`. Establish `hz : ∀ (E : X.Modules) (z : X), z ∉ support E → Module.length (X.presheaf.stalk z) (E.presheaf.stalk z :) = 0` using `fun E z h =>`. Use `notMem_support_iff.1 h` as an intermediate fact. Use the proof step `Module.length_eq_zero`.

Use `revert hFS`. Use `QCoh.devissage X (fun F => support F ⊆ S → (∀ z ∈ T, Module.length (X.presheaf.stalk z) (F.presheaf.stalk z :) ≠ ⊤) ∧ interNum κ F P = ∑ z ∈ T, ((Module.length (X.presheaf.stalk z) (F.presheaf.stalk z :)).toNat : ℤ) * deg z) (fun E hE _ => ?_) (fun C hC h₁ h₃ p₁ p₃ hs => ?_) (fun …` and prove the remaining obligations. Establish `h0 : ∀ z, Module.length (X.presheaf.stalk z) (E.presheaf.stalk z :) = 0` using `fun z => hz E z (by rw [support_eq_empty_iff.2 hE]; exact Set.notMem_empty _)`. Use `⟨fun z _ => by rw [h0]; simp, ?_⟩` and prove the remaining obligations. Rewrite using `[interNum_eq_zero_of_isZero κ hE hL]`.

Simplify using `[h0]`. Rewrite `hs` using `[support_eq_union_of_shortExact hC]`. Take `⟨a₁, b₁⟩` from `p₁ (Set.subset_union_left.trans hs)`. Take `⟨a₃, b₃⟩` from `p₃ (Set.subset_union_right.trans hs)`. Use `hC.mono_f` as an intermediate fact.

Use `hC.epi_g` as an intermediate fact. Establish `hl (z : X)` using `Module.length_eq_add_of_exact (stalkLinear C.f z) (stalkLinear C.g z) (stalkLinear_injective _ z) (stalkLinear_surjective _ z) ((exact_iff_stalkLinear C).1 hC.exact z)`. Use `⟨fun z h => by rw [hl]; exact WithTop.add_ne_top.2 ⟨a₁ z h, a₃ z h⟩ , ?_⟩` and prove the remaining obligations. Rewrite using `[interNum_shortExact hC hL (finiteCohTwists_of_isProjOver hf _ hp) (finiteCohTwists_of_isProjOver hf _ hp), b₁, b₃, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun z h => ?_` and prove the remaining obligations.

Rewrite using `[hl, ENat.toNat_add (a₁ z h) (a₃ z h)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `isIntegral_red hZ` as an intermediate fact. Use `letI := algebraΓAlong κ (redι Z)`.

Establish `hi` using `appTop_algebraMap_along κ (redι Z)`. Establish `hpZ : IsProjOver (strHom κ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)`. Rewrite using `[← comp_strHom hi]`. Conclude with `ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp`. Establish `hsub : support ((Scheme.Modules.pushforward (redι Z)).obj G) ⊆ Z` using `fun x hx => range_redι Z ▸ range_of_mem_support_push _ G hx`.

Use `set ξ := redι Z (genericPoint _) with hξ`. Establish `hcl : closure {ξ} = (Z : Set X)`. Establish `h₁` using `(genericPoint_spec _).image (redι Z).continuous`. Rewrite `h₁` using `[Set.image_univ, range_redι, Z.isClosed.closure_eq]`. Conclude with `h₁.def`.

Distinguish the cases in `hr : genRank G = 0`. Establish `hFQ : IsFiniteQC ((Scheme.Modules.pushforward (redι Z)).obj G)` using `⟨inferInstance, fun _ hV => QCoh.finite_sections_pushforward (redι Z) _ hV (hF := QCoh.finite_sections G (hV.preimage (redι Z)))⟩`. Use `ih _ hFQ ⟨hsub, fun hle => ?_⟩ hs` and prove the remaining obligations. Conclude with `genRank_eq_zero_iff.1 hr ((mem_support_push _ G _).1 (hle (hcl ▸ subset_closure rfl)))`. Establish `hξS : ξ ∈ S` using `hs ((mem_support_push _ G _).2 (by_contra fun h => hr (genRank_eq_zero_iff.2 h)))`.

Establish `hdZ` using `topologicalKrullDim_red Z`. Establish `hPZ : ∀ j, ((P j).pull (redι Z)).IsLB` using `fun j => LB.isLB_pull (hL j) _`. Establish `hle : topologicalKrullDim (Z : Set X) ≤ d`. Distinguish the cases in `h : ξ ∈ T`. Conclude with `(hcl ▸ hT ξ h).le`.

Conclude with `(hcl ▸ hS ξ hξS h).le`. Establish `hoff : ∀ z ∈ T, z ≠ ξ → z ∉ support ((Scheme.Modules.pushforward (redι Z)).obj G)`. Introduce `z hzT hne hzs`. Establish `hzZ` using `hsub hzs`. Establish `hsp : ξ ⤳ z` using `specializes_iff_mem_closure.2 (hcl ▸ hzZ)`.

Establish `h1` using `topologicalKrullDim_add_one_le (s := closure {z}) isClosed_closure Z.isClosed fun x hx => ⟨ξ, hcl ▸ subset_closure rfl, fun h => hne (hsp.antisymm (specializes_iff_mem_closure.2 h)).eq.symm, hsp.trans (specializes_iff_mem_closure.2 hx)⟩`. Rewrite `h1` using `[hT z hzT]`. Establish `h4 : d + 1 ≤ d` using `by exact_mod_cast h1.trans hle`. Use linear arithmetic over natural numbers and integers. Establish `hlen : Module.length (X.presheaf.stalk ξ) (((Scheme.Modules.pushforward (redι Z)).obj G).presheaf.stalk ξ :) = genRank G` using `(length_push _ G _).trans (Module.length_eq_finrank _ _)`.

Rewrite using `[interNum_pushforward_of_isClosedImmersion hi G hL]`. Use `⟨fun z h => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `e : z = ξ`. Substitute `e` using the available equality. Rewrite using `[hlen]`.

Conclude with `ENat.coe_ne_top _`. Rewrite using `[hz _ z (hoff z h e)]`. Simplify using the standard rewrite rules. Distinguish the cases in `h : ξ ∈ T`. Rewrite using `[Finset.sum_eq_single ξ (fun z hzT e => by rw [hz _ z (hoff z hzT e)]; simp) (fun h' => absurd h h'), hlen, interNum_of_genRank_eq hpZ (hdZ.le.trans hle) hPZ _ G rfl, hdeg _ (redι Z) hi h, ENat.toNat_coe]`.

Rewrite using `[Finset.sum_eq_zero fun z hzT => by rw [hz _ z (hoff z hzT fun e => h (e ▸ hzT))]; simp]`. Use `interNum_eq_zero_of_isProjOver (algebraMap_eq_strHom κ _) G hpZ ?_ hPZ` and prove the remaining obligations. Rewrite using `[Fintype.card_fin]`. Conclude with `(QCoh.suppDim_le G).trans_lt (hdZ.trans_lt (hcl ▸ hS ξ hξS h))`.
-/
theorem interNum_eq_sum {X : Scheme.{0}} [Algebra κ Γ(X, ⊤)] (hp : IsProjOver (strHom κ X)) {d : ℕ}
    {P : Fin d → LB X} (hL : ∀ j, (P j).IsLB) (S : Set X) (T : Finset X) (deg : X → ℤ)
    (hT : ∀ z ∈ T, topologicalKrullDim (closure {z} : Set X) = d)
    (hS : ∀ z ∈ S, z ∉ T → topologicalKrullDim (closure {z} : Set X) < d)
    (hdeg : ∀ (Y : Scheme.{0}) (i : Y ⟶ X) [IsClosedImmersion i] [IsIntegral Y] [Algebra κ Γ(Y, ⊤)],
      (∀ r : κ, i.appTop (algebraMap κ Γ(X, ⊤) r) = algebraMap κ Γ(Y, ⊤) r) → i (genericPoint Y) ∈ T →
      interNum κ (GlobalTheory.structureModule Y) (fun j => (P j).pull i) = deg (i (genericPoint Y)))
    (F : X.Modules) (hF : IsFiniteQC F) (hFS : support F ⊆ S) :
    (∀ z ∈ T, Module.length (X.presheaf.stalk z) (F.presheaf.stalk z :) ≠ ⊤) ∧
      interNum κ F P = ∑ z ∈ T, ((Module.length (X.presheaf.stalk z) (F.presheaf.stalk z :)).toNat : ℤ) * deg z := by
  classical
  have := isNoetherian_of_isProjOver hp
  have hf := algebraMap_eq_strHom κ X
  have hz : ∀ (E : X.Modules) (z : X), z ∉ support E →
      Module.length (X.presheaf.stalk z) (E.presheaf.stalk z :) = 0 := fun E z h =>
    have := notMem_support_iff.1 h
    Module.length_eq_zero
  revert hFS
  refine QCoh.devissage X (fun F => support F ⊆ S →
    (∀ z ∈ T, Module.length (X.presheaf.stalk z) (F.presheaf.stalk z :) ≠ ⊤) ∧
      interNum κ F P = ∑ z ∈ T, ((Module.length (X.presheaf.stalk z) (F.presheaf.stalk z :)).toNat : ℤ) * deg z)
    (fun E hE _ => ?_) (fun C hC h₁ h₃ p₁ p₃ hs => ?_) (fun Z hZ ih G hG hs => ?_) F hF
  · have h0 : ∀ z, Module.length (X.presheaf.stalk z) (E.presheaf.stalk z :) = 0 := fun z =>
      hz E z (by rw [support_eq_empty_iff.2 hE]; exact Set.notMem_empty _)
    refine ⟨fun z _ => by rw [h0]; simp, ?_⟩
    rw [interNum_eq_zero_of_isZero κ hE hL]
    simp [h0]
  · rw [support_eq_union_of_shortExact hC] at hs
    obtain ⟨a₁, b₁⟩ := p₁ (Set.subset_union_left.trans hs)
    obtain ⟨a₃, b₃⟩ := p₃ (Set.subset_union_right.trans hs)
    have := hC.mono_f
    have := hC.epi_g
    have hl (z : X) := Module.length_eq_add_of_exact (stalkLinear C.f z) (stalkLinear C.g z)
      (stalkLinear_injective _ z) (stalkLinear_surjective _ z) ((exact_iff_stalkLinear C).1 hC.exact z)
    refine ⟨fun z h => by rw [hl]; exact WithTop.add_ne_top.2 ⟨a₁ z h, a₃ z h⟩ , ?_⟩
    rw [interNum_shortExact hC hL (finiteCohTwists_of_isProjOver hf _ hp) (finiteCohTwists_of_isProjOver hf _ hp),
      b₁, b₃, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z h => ?_
    rw [hl, ENat.toNat_add (a₁ z h) (a₃ z h)]
    push_cast
    ring
  · have := isIntegral_red hZ
    letI := algebraΓAlong κ (redι Z)
    have hi := appTop_algebraMap_along κ (redι Z)
    have hpZ : IsProjOver (strHom κ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
      rw [← comp_strHom hi]
      exact ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp
    have hsub : support ((Scheme.Modules.pushforward (redι Z)).obj G) ⊆ Z := fun x hx =>
      range_redι Z ▸ range_of_mem_support_push _ G hx
    set ξ := redι Z (genericPoint _) with hξ
    have hcl : closure {ξ} = (Z : Set X) := by
      have h₁ := (genericPoint_spec _).image (redι Z).continuous
      rw [Set.image_univ, range_redι, Z.isClosed.closure_eq] at h₁
      exact h₁.def
    by_cases hr : genRank G = 0
    · have hFQ : IsFiniteQC ((Scheme.Modules.pushforward (redι Z)).obj G) :=
        ⟨inferInstance, fun _ hV => QCoh.finite_sections_pushforward (redι Z) _ hV
          (hF := QCoh.finite_sections G (hV.preimage (redι Z)))⟩
      refine ih _ hFQ ⟨hsub, fun hle => ?_⟩ hs
      exact genRank_eq_zero_iff.1 hr ((mem_support_push _ G _).1 (hle (hcl ▸ subset_closure rfl)))
    have hξS : ξ ∈ S := hs ((mem_support_push _ G _).2 (by_contra fun h => hr (genRank_eq_zero_iff.2 h)))
    have hdZ := topologicalKrullDim_red Z
    have hPZ : ∀ j, ((P j).pull (redι Z)).IsLB := fun j => LB.isLB_pull (hL j) _
    have hle : topologicalKrullDim (Z : Set X) ≤ d := by
      by_cases h : ξ ∈ T
      · exact (hcl ▸ hT ξ h).le
      · exact (hcl ▸ hS ξ hξS h).le
    have hoff : ∀ z ∈ T, z ≠ ξ → z ∉ support ((Scheme.Modules.pushforward (redι Z)).obj G) := by
      intro z hzT hne hzs
      have hzZ := hsub hzs
      have hsp : ξ ⤳ z := specializes_iff_mem_closure.2 (hcl ▸ hzZ)
      have h1 := topologicalKrullDim_add_one_le (s := closure {z}) isClosed_closure Z.isClosed fun x hx =>
        ⟨ξ, hcl ▸ subset_closure rfl, fun h => hne (hsp.antisymm (specializes_iff_mem_closure.2 h)).eq.symm,
          hsp.trans (specializes_iff_mem_closure.2 hx)⟩
      rw [hT z hzT] at h1
      have h4 : d + 1 ≤ d := by exact_mod_cast h1.trans hle
      omega
    have hlen : Module.length (X.presheaf.stalk ξ) (((Scheme.Modules.pushforward (redι Z)).obj G).presheaf.stalk ξ :) =
        genRank G := (length_push _ G _).trans (Module.length_eq_finrank _ _)
    rw [interNum_pushforward_of_isClosedImmersion hi G hL]
    refine ⟨fun z h => ?_, ?_⟩
    · by_cases e : z = ξ
      · subst e; rw [hlen]; exact ENat.coe_ne_top _
      · rw [hz _ z (hoff z h e)]; simp
    · by_cases h : ξ ∈ T
      · rw [Finset.sum_eq_single ξ (fun z hzT e => by rw [hz _ z (hoff z hzT e)]; simp) (fun h' => absurd h h'),
          hlen, interNum_of_genRank_eq hpZ (hdZ.le.trans hle) hPZ _ G rfl, hdeg _ (redι Z) hi h, ENat.toNat_coe]
      · rw [Finset.sum_eq_zero fun z hzT => by rw [hz _ z (hoff z hzT fun e => h (e ▸ hzT))]; simp]
        refine interNum_eq_zero_of_isProjOver (algebraMap_eq_strHom κ _) G hpZ ?_ hPZ
        rw [Fintype.card_fin]
        exact (QCoh.suppDim_le G).trans_lt (hdZ.trans_lt (hcl ▸ hS ξ hξS h))

end ChowFormHeightComparison₂.CF.V
