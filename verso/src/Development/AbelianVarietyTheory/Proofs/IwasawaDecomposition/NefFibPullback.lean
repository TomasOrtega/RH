import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberFinitePushforward
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.ArInt

/- English proof (translation)
Establish `le : ∀ j, L.U j ≤ L.U j ⊓ L.U i₀` using `fun j => le_inf le_rfl (h ▸ le_top)`. Establish `hm : ∀ y : Z, y ∈ L.U i₀` using `fun y => h ▸ Opens.mem_top y`. Establish `H : ∃ t : LB.Gen L, t.IsGen` using `⟨⟨fun j => res (le j) (L.g j i₀)⟩, fun i j => unit_ext fun y hy => by`. Rewrite using `[map_mul, gm_res (𝟙 Z) y _ hy, gm_res (𝟙 Z) y _ hy.1, gm_res (𝟙 Z) y _ hy, gm_res (𝟙 Z) y _ hy.2]`. Conclude with `(gm_cocycle hL (𝟙 Z) y hy.1 hy.2 (hm y)).symm⟩`.

Conclude with `(cls_eq_iff hL (LB.isLB_triv Z)).2 (LBIso.symm ((iso_triv_iff L).2 H))`.
-/
theorem cls_eq_zero_of_chart_eq_top {Z : Scheme.{0}} {L : LB Z} (hL : L.IsLB) (i₀ : L.ι)
    (h : L.U i₀ = ⊤) : cls L hL = 0 := by
  have le : ∀ j, L.U j ≤ L.U j ⊓ L.U i₀ := fun j => le_inf le_rfl (h ▸ le_top)
  have hm : ∀ y : Z, y ∈ L.U i₀ := fun y => h ▸ Opens.mem_top y
  have H : ∃ t : LB.Gen L, t.IsGen :=
    ⟨⟨fun j => res (le j) (L.g j i₀)⟩, fun i j => unit_ext fun y hy => by
      rw [map_mul, gm_res (𝟙 Z) y _ hy, gm_res (𝟙 Z) y _ hy.1, gm_res (𝟙 Z) y _ hy, gm_res (𝟙 Z) y _ hy.2]
      exact (gm_cocycle hL (𝟙 Z) y hy.1 hy.2 (hm y)).symm⟩
  exact (cls_eq_iff hL (LB.isLB_triv Z)).2 (LBIso.symm ((iso_triv_iff L).2 H))

/- English proof (translation)
Take `⟨i, hi⟩` from `exists_chart hM x`. Establish `h` using `cls_eq_zero_of_chart_eq_top (pull_isLB hM g) (fun _ => i) (top_le_iff.1 fun z _ => mem_pull.2 ((hg z).symm ▸ hi))`. Conclude with `interNum_eq_zero_of_cls_eq_zero κ _ (fun _ => pull_isLB hM g) 0 h`.
-/
theorem topSelf_pull_eq_zero_of_const {X Z : Scheme.{0}} (κ : Type) [Field κ] [Algebra κ Γ(Z, ⊤)]
    {M : LB X} (hM : M.IsLB) (g : Z ⟶ X) (x : X) (hg : ∀ z, g z = x) :
    topSelfIntersection κ (M.pull g) 1 = 0 := by
  obtain ⟨i, hi⟩ := exists_chart hM x
  have h := cls_eq_zero_of_chart_eq_top (pull_isLB hM g) (fun _ => i)
    (top_le_iff.1 fun z _ => mem_pull.2 ((hg z).symm ▸ hi))
  exact interNum_eq_zero_of_cls_eq_zero κ _ (fun _ => pull_isLB hM g) 0 h

/- English proof (translation)
Establish `e : strHom κ Z ≫ spMap (Int.castRingHom κ) = t` using `specZIsTerminal.hom_ext _ _`. Establish `: IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ))` using `by rw [e]; infer_instance`. Conclude with `IsProper.of_comp _ (spMap (Int.castRingHom κ))`.
-/
theorem isProper_strHom (κ : Type) [Field κ] {Z : Scheme.{0}} [Algebra κ Γ(Z, ⊤)] (t : Z ⟶ Sp ℤ)
    [IsProper t] : IsProper (strHom κ Z) := by
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = t := specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  exact IsProper.of_comp _ (spMap (Int.castRingHom κ))

/- English proof (translation)
Use `(injective_iff_map_eq_zero _).2 fun a ha => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne0`. Establish `hne : Z.basicOpen a ≠ ⊥` using `fun h0 => hne0 ((basicOpen_eq_bot_iff a).1 h0)`. Take `⟨w, hw⟩` from `h.exists_mem_open (Z.basicOpen a).isOpen (Set.nonempty_iff_ne_empty.2 fun e => hne (Opens.ext e))`. Establish `e : φ ⁻¹ᵁ Z.basicOpen a = W.basicOpen (φ.appTop.hom a)` using `Scheme.preimage_basicOpen_top φ a`.

Establish `hw' : w ∈ W.basicOpen (φ.appTop.hom a)` using `e ▸ hw`. Rewrite `hw'` using `[ha, Scheme.basicOpen_zero]`. Conclude with `hw'`.
-/
theorem appTop_injective_of_denseRange {Z W : Scheme.{0}} [IsReduced Z] (φ : W ⟶ Z)
    (h : DenseRange φ) : Function.Injective φ.appTop.hom := by
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  by_contra hne0
  have hne : Z.basicOpen a ≠ ⊥ := fun h0 => hne0 ((basicOpen_eq_bot_iff a).1 h0)
  obtain ⟨w, hw⟩ := h.exists_mem_open (Z.basicOpen a).isOpen
    (Set.nonempty_iff_ne_empty.2 fun e => hne (Opens.ext e))
  have e : φ ⁻¹ᵁ Z.basicOpen a = W.basicOpen (φ.appTop.hom a) := Scheme.preimage_basicOpen_top φ a
  have hw' : w ∈ W.basicOpen (φ.appTop.hom a) := e ▸ hw
  rw [ha, Scheme.basicOpen_zero] at hw'
  exact hw'

section

attribute [local instance low] specializationOrder

/- English proof (translation)
Rewrite using `[PosBaseChange.dim_eq_krullDim]`. Conclude with `Order.one_le_krullDim_iff.2 ⟨b, a, lt_of_le_of_ne h hne.symm⟩`.
-/
theorem one_le_dim {S : Type} [TopologicalSpace S] [QuasiSober S] [T0Space S] {a b : S} (h : a ⤳ b)
    (hne : a ≠ b) : 1 ≤ topologicalKrullDim S := by
  rw [PosBaseChange.dim_eq_krullDim]
  exact Order.one_le_krullDim_iff.2 ⟨b, a, lt_of_le_of_ne h hne.symm⟩

end

section Curve

variable {X W : Scheme.{0}} [IsIntegral W] (ℓ : ℕ) [Fact ℓ.Prime] [Algebra (ZMod ℓ) Γ(W, ⊤)]

/- English proof (translation)
Establish `: IsProper g` using `.of_comp g t`. Establish `hW : IsProper (strHom (ZMod ℓ) W)` using `isProper_strHom (ZMod ℓ) (g ≫ t)`. Establish `: CompactSpace W` using `QuasiCompact.compactSpace_of_compactSpace (strHom (ZMod ℓ) W)`. Use `isNoetherian_of_locallyOfFiniteType_field (strHom (ZMod ℓ) W)` as an intermediate fact. Distinguish the cases in `hc : ∀ w, g w = g (genericPoint W)`.

Conclude with `(topSelf_pull_eq_zero_of_const (ZMod ℓ) hM g _ hc).ge`. Use `push_neg at hc`. Take `⟨x₀, hx₀⟩` from `hc`. Set `φ : W ⟶ g.image` to `g.toImage`. Establish `e : φ ≫ g.imageι = g` using `g.toImage_imageι`.

Establish `: IsProper (φ ≫ g.imageι)` using `by rw [e]; infer_instance`. Establish `: IsProper φ` using `.of_comp φ g.imageι`. Establish `hne : φ x₀ ≠ φ (genericPoint W)` using `fun h => hx₀ (by`. Rewrite using `[← e, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h])`. Establish `: LocallyQuasiFinite φ` using `ProperCurve.locallyQuasiFinite_of_ne hd φ hne`.

Establish `: IsFinite φ` using `IsFinite.of_isProper_of_locallyQuasiFinite φ`. Establish `hdense : DenseRange φ` using `g.toImage.denseRange`. Establish `hsurj : Function.Surjective φ`. Rewrite using `[← Set.range_eq_univ, ← φ.isClosedMap.isClosed_range.closure_eq]`. Conclude with `hdense.closure_range`.

Establish `hgen : φ (genericPoint W) = genericPoint g.image`. Establish `h₁` using `(genericPoint_spec W).image φ.continuous`. Rewrite `h₁` using `[Set.image_univ, hdense.closure_range]`. Conclude with `h₁.eq (genericPoint_spec _)`. Establish `hdZ : topologicalKrullDim g.image = 1`.

Conclude with `le_antisymm ((PosBaseChange.dim_le_of_isClosedMap φ.isClosedMap hsurj).trans hd.le) (one_le_dim (genericPoint_specializes (φ x₀)) fun h => hne (h.symm.trans hgen.symm))`. Establish `hinj` using `appTop_injective_of_denseRange φ hdense`. Establish `: CharP Γ(W, ⊤) ℓ` using `charP_of_injective_algebraMap (algebraMap (ZMod ℓ) Γ(W, ⊤)).injective ℓ`. Establish `: CharP Γ(g.image, ⊤) ℓ` using `φ.appTop.hom.charP hinj ℓ`. Use `letI : Algebra (ZMod ℓ) Γ(g.image, ⊤) := ZMod.algebra _ ℓ`.

Establish `hf (r : ZMod ℓ) : φ.appTop (algebraMap (ZMod ℓ) Γ(g.image, ⊤) r) = algebraMap (ZMod ℓ) Γ(W, ⊤) r` using `RingHom.congr_fun (RingHom.ext_zmod (φ.appTop.hom.comp (algebraMap (ZMod ℓ) Γ(g.image, ⊤))) (algebraMap (ZMod ℓ) Γ(W, ⊤))) r`. Establish `: IsProper (g.imageι ≫ t)` using `inferInstance`. Establish `hZ : IsProper (strHom (ZMod ℓ) g.image)` using `isProper_strHom (ZMod ℓ) (g.imageι ≫ t)`. Establish `hproj : IsProjOver (strHom (ZMod ℓ) g.image)` using `ProperCurve.isProjOver_of_isProper _ hdZ`. Establish `hN` using `pull_isLB hM g.imageι`.

Establish `h₁` using `GlobalTheory.ProjFin.interNumOn_eq_residueDegree_mul (ZMod ℓ) g.image W φ hproj hdZ hgen (M.pull g.imageι) hN`. Establish `h₂` using `interNumOn_eq_interNum_pull (k := ZMod ℓ) (L := ![M.pull g.imageι]) hf (fun i => by fin_cases i; exact hN)`. Establish `h₃ : topSelfIntersection (ZMod ℓ) (M.pull g) 1 = interNum (ZMod ℓ) (structureModule W) fun i => (![M.pull g.imageι] i).pull φ`. Use `interNum_congr_cls _ _ (fun _ => pull_isLB hM g) (fun i => by fin_cases i; exact pull_isLB hN φ) fun i => ?_` and prove the remaining obligations. Use `fin_cases i`.

Use `(cls_pull hM g _).trans ?_` and prove the remaining obligations. Use `Eq.trans ?_ (cls_pull hN φ _).symm` and prove the remaining obligations. Conclude with `(congrArg (fun f => pull f (cls M hM)) e.symm).trans (pull_comp φ g.imageι _)`. Establish `h₄ : interNum (ZMod ℓ) (structureModule g.image) ![M.pull g.imageι] = topSelfIntersection (ZMod ℓ) (M.pull g.imageι) 1`. Use `congrArg _ (funext fun j => ?_)` and prove the remaining obligations.

Use `fin_cases j`. Both sides reduce to the same expression. Rewrite using `[h₃, ← h₂, h₁, h₄]`. Conclude with `mul_nonneg (Int.natCast_nonneg _) (H _ g.imageι hdZ)`.
-/
theorem topSelf_pull_nonneg (t : X ⟶ Sp ℤ) [IsProper t] (hd : topologicalKrullDim W = 1)
    {M : LB X} (hM : M.IsLB) (g : W ⟶ X) [IsProper (g ≫ t)]
    (H : ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      [Algebra (ZMod ℓ) Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod ℓ) (M.pull i) 1) :
    0 ≤ topSelfIntersection (ZMod ℓ) (M.pull g) 1 := by
  have : IsProper g := .of_comp g t
  have hW : IsProper (strHom (ZMod ℓ) W) := isProper_strHom (ZMod ℓ) (g ≫ t)
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (strHom (ZMod ℓ) W)
  have := isNoetherian_of_locallyOfFiniteType_field (strHom (ZMod ℓ) W)
  by_cases hc : ∀ w, g w = g (genericPoint W)
  · exact (topSelf_pull_eq_zero_of_const (ZMod ℓ) hM g _ hc).ge
  push_neg at hc
  obtain ⟨x₀, hx₀⟩ := hc
  let φ : W ⟶ g.image := g.toImage
  have e : φ ≫ g.imageι = g := g.toImage_imageι
  have : IsProper (φ ≫ g.imageι) := by rw [e]; infer_instance
  have : IsProper φ := .of_comp φ g.imageι
  have hne : φ x₀ ≠ φ (genericPoint W) := fun h => hx₀ (by
    rw [← e, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h])
  have : LocallyQuasiFinite φ := ProperCurve.locallyQuasiFinite_of_ne hd φ hne
  have : IsFinite φ := IsFinite.of_isProper_of_locallyQuasiFinite φ
  have hdense : DenseRange φ := g.toImage.denseRange
  have hsurj : Function.Surjective φ := by
    rw [← Set.range_eq_univ, ← φ.isClosedMap.isClosed_range.closure_eq]
    exact hdense.closure_range
  have hgen : φ (genericPoint W) = genericPoint g.image := by
    have h₁ := (genericPoint_spec W).image φ.continuous
    rw [Set.image_univ, hdense.closure_range] at h₁
    exact h₁.eq (genericPoint_spec _)
  have hdZ : topologicalKrullDim g.image = 1 := by
    exact le_antisymm ((PosBaseChange.dim_le_of_isClosedMap φ.isClosedMap hsurj).trans hd.le)
      (one_le_dim (genericPoint_specializes (φ x₀)) fun h => hne (h.symm.trans hgen.symm))
  have hinj := appTop_injective_of_denseRange φ hdense
  have : CharP Γ(W, ⊤) ℓ := charP_of_injective_algebraMap (algebraMap (ZMod ℓ) Γ(W, ⊤)).injective ℓ
  have : CharP Γ(g.image, ⊤) ℓ := φ.appTop.hom.charP hinj ℓ
  letI : Algebra (ZMod ℓ) Γ(g.image, ⊤) := ZMod.algebra _ ℓ
  have hf (r : ZMod ℓ) : φ.appTop (algebraMap (ZMod ℓ) Γ(g.image, ⊤) r) = algebraMap (ZMod ℓ) Γ(W, ⊤) r :=
    RingHom.congr_fun (RingHom.ext_zmod (φ.appTop.hom.comp (algebraMap (ZMod ℓ) Γ(g.image, ⊤)))
      (algebraMap (ZMod ℓ) Γ(W, ⊤))) r
  have : IsProper (g.imageι ≫ t) := inferInstance
  have hZ : IsProper (strHom (ZMod ℓ) g.image) := isProper_strHom (ZMod ℓ) (g.imageι ≫ t)
  have hproj : IsProjOver (strHom (ZMod ℓ) g.image) := ProperCurve.isProjOver_of_isProper _ hdZ
  have hN := pull_isLB hM g.imageι
  have h₁ := GlobalTheory.ProjFin.interNumOn_eq_residueDegree_mul (ZMod ℓ) g.image W φ hproj hdZ hgen (M.pull g.imageι) hN
  have h₂ := interNumOn_eq_interNum_pull (k := ZMod ℓ) (L := ![M.pull g.imageι]) hf
    (fun i => by fin_cases i; exact hN)
  have h₃ : topSelfIntersection (ZMod ℓ) (M.pull g) 1 =
      interNum (ZMod ℓ) (structureModule W) fun i => (![M.pull g.imageι] i).pull φ := by
    refine interNum_congr_cls _ _ (fun _ => pull_isLB hM g) (fun i => by fin_cases i; exact pull_isLB hN φ) fun i => ?_
    fin_cases i
    refine (cls_pull hM g _).trans ?_
    refine Eq.trans ?_ (cls_pull hN φ _).symm
    exact (congrArg (fun f => pull f (cls M hM)) e.symm).trans (pull_comp φ g.imageι _)
  have h₄ : interNum (ZMod ℓ) (structureModule g.image) ![M.pull g.imageι] =
      topSelfIntersection (ZMod ℓ) (M.pull g.imageι) 1 := by
    refine congrArg _ (funext fun j => ?_)
    fin_cases j
    rfl
  rw [h₃, ← h₂, h₁, h₄]
  exact mul_nonneg (Int.natCast_nonneg _) (H _ g.imageι hdZ)

end Curve

/- English proof (translation)
Introduce `k _ _ X Y p q hp hq π hπ L hL`. Use `nefFib_of_primeField k Y q _ fun W i _ _ ℓ _ _ hd => ?_` and prove the remaining obligations. Take `⟨N, j, _, hj⟩` from `hp`. Take `⟨N', j', _, hj'⟩` from `hq`. Use `isProper_str k N` as an intermediate fact.

Use `isProper_str k N'` as an intermediate fact. Establish `: IsProper p` using `hj ▸ inferInstance`. Establish `: IsProper q` using `hj' ▸ inferInstance`. Establish `: IsFinite (spMap (Int.castRingHom k))`. Rewrite using `[spMap, IsFinite.SpecMap_iff]`.

Conclude with `(RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance`. Establish `hp' : IsProper (π ≫ p)` using `by rw [hπ]; infer_instance`. Establish `: IsProper π` using `.of_comp π p`. Establish `hg : IsProper ((i ≫ π) ≫ p ≫ spMap (Int.castRingHom k))` using `inferInstance`. Establish `h` using `topSelf_pull_nonneg ℓ (p ≫ spMap (Int.castRingHom k)) hd L.isLB (i ≫ π) fun Z i' _ _ _ hd' => hL Z i' (ZMod ℓ) hd'`.

Establish `e : cls ((L.pull π hπ).B.pull i) (pull_isLB (L.pull π hπ).isLB i) = cls (L.B.pull (i ≫ π)) (pull_isLB L.isLB _)`. Use `(cls_pull (L.pull π hπ).isLB i _).trans ?_` and prove the remaining obligations. Use `Eq.trans ?_ (cls_pull L.isLB (i ≫ π) _).symm` and prove the remaining obligations. Conclude with `(pull_comp i π (cls L.B L.isLB)).symm`. Rewrite using `[topSelf_congr (ZMod ℓ) (pull_isLB (L.pull π hπ).isLB i) (pull_isLB L.isLB _) ((cls_eq_iff _ _).1 e)]` and apply the resulting hypothesis.
-/
theorem nefFib_pull : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X Y : Scheme.{0}) (p : X ⟶ Sp k)
    (q : Y ⟶ Sp k), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p),
    ArInt.NefFib L → ArInt.NefFib (L.pull π hπ) := by
  intro k _ _ X Y p q hp hq π hπ L hL
  refine nefFib_of_primeField k Y q _ fun W i _ _ ℓ _ _ hd => ?_
  obtain ⟨N, j, _, hj⟩ := hp
  obtain ⟨N', j', _, hj'⟩ := hq
  have := isProper_str k N
  have := isProper_str k N'
  have : IsProper p := hj ▸ inferInstance
  have : IsProper q := hj' ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have hp' : IsProper (π ≫ p) := by rw [hπ]; infer_instance
  have : IsProper π := .of_comp π p
  have hg : IsProper ((i ≫ π) ≫ p ≫ spMap (Int.castRingHom k)) := inferInstance
  have h := topSelf_pull_nonneg ℓ (p ≫ spMap (Int.castRingHom k)) hd L.isLB (i ≫ π)
    fun Z i' _ _ _ hd' => hL Z i' (ZMod ℓ) hd'
  have e : cls ((L.pull π hπ).B.pull i) (pull_isLB (L.pull π hπ).isLB i) =
      cls (L.B.pull (i ≫ π)) (pull_isLB L.isLB _) := by
    refine (cls_pull (L.pull π hπ).isLB i _).trans ?_
    refine Eq.trans ?_ (cls_pull L.isLB (i ≫ π) _).symm
    exact (pull_comp i π (cls L.B L.isLB)).symm
  rwa [topSelf_congr (ZMod ℓ) (pull_isLB (L.pull π hπ).isLB i) (pull_isLB L.isLB _)
    ((cls_eq_iff _ _).1 e)]

end GlobalTheory.ArInt
