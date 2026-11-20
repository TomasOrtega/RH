import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

/- English proof (translation)
Take `⟨W, hW, hyW, hWO⟩` from `exists_isAffineOpen_mem_and_subset hy`. Use `haveI := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩`. Establish `hN : NoetherianSpace W`. Use `NoetherianSpace.range hW.fromSpec hW.fromSpec.continuous` as an intermediate fact. Rewrite `this` using `[hW.range_fromSpec]`.

Conclude with `this`. Establish `hC : IsClosed ((Subtype.val : W → Y) ⁻¹' F)` using `hF.preimage continuous_subtype_val`. Take `⟨S, hS, hc, hi, hU⟩` from `@NoetherianSpace.exists_finite_set_isClosed_irreducible _ _ hN _ hC`. Set `y₀ : W` to `⟨y, hyW⟩`. Set `bad : Set W` to `⋃₀ {T ∈ S | y₀ ∉ T}`.

Establish `hS' : {T ∈ S | y₀ ∉ T}.Finite` using `hS.subset fun T hT => hT.1`. Establish `hbad : IsClosed bad`. Express the relevant statement in the definitionally equal form `IsClosed (⋃₀ {T ∈ S | y₀ ∉ T})`. Rewrite using `[Set.sUnion_eq_biUnion]`. Conclude with `hS'.isClosed_biUnion fun T hT => hc T hT.1`.

Use `⟨⟨Subtype.val '' badᶜ, W.isOpen.isOpenMap_subtype_val _ hbad.isOpen_compl⟩, ⟨y₀, ?_, rfl⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨T, ⟨-, hyT⟩, hyT'⟩`. Conclude with `hyT hyT'`. Introduce and unpack `_ ⟨x, -, rfl⟩`. Conclude with `hWO x.2`.

Introduce and unpack `_ ⟨x, hx, rfl⟩ v hv hcv hvF`. Establish `hvW : v ∈ W` using `hv.mem_open W.isOpen x.2`. Set `v' : W` to `⟨v, hvW⟩`. Establish `hv' : v' ⤳ x` using `Topology.IsInducing.subtypeVal.specializes_iff.1 hv`. Establish `hvS : v' ∈ ⋃₀ S` using `hU ▸ hvF`.

Take `⟨T, hT, hvT⟩` from `hvS`. Establish `hxT : x ∈ T` using `hv'.mem_closed (hc T hT) hvT`. Establish `hyT : y₀ ∈ T`. Assume the negation of the conclusion as `h`. Conclude with `hx ⟨T, ⟨hT, h⟩, hxT⟩`.

Take `⟨g, hg⟩` from `QuasiSober.sober (hi T hT) (hc T hT)`. Establish `hgF : g.1 ∈ F`. Establish `: g ∈ ⋃₀ S` using `⟨T, hT, hg.mem⟩`. Rewrite `this` using `[← hU]`. Conclude with `this`.

Establish `hgv : g.1 ⤳ v` using `Topology.IsInducing.subtypeVal.specializes_iff.2 (hg.specializes hvT)`. Establish `hgy : g.1 ⤳ y` using `Topology.IsInducing.subtypeVal.specializes_iff.2 (hg.specializes hyT)`. Establish `hgη : g.1 < genericPoint Y`. Use `lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_` and prove the remaining obligations. Establish `e' : g.1 = genericPoint Y` using `(Specializes.antisymm e (genericPoint_specializes _)).eq`.

Conclude with `hη (e' ▸ hgF)`. Establish `hvg : v = g.1`. Assume the negation of the conclusion as `hne`. Establish `h₃` using `Order.coheight_add_one_le (show v < g.1 from lt_of_le_not_ge hgv fun e => hne (Specializes.antisymm e hgv).eq)`. Establish `h₄` using `Order.coheight_add_one_le hgη`.

Rewrite `h₃` using `[hcv]`. Establish `h₅ : (1 : ℕ∞) + 1 ≤ 1` using `(add_le_add_left (le_add_self.trans h₄) 1).trans h₃`. Conclude with `absurd h₅ (by decide)`. Rewrite using `[hvg]`. Conclude with `hgy`.
-/
theorem exists_nbhd_specializes_of_isClosed {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (F : Set Y) (hF : IsClosed F) (hη : genericPoint Y ∉ F) {y : Y} {O : Y.Opens} (hy : y ∈ O) :
    ∃ V : Y.Opens, y ∈ V ∧ V ≤ O ∧
      ∀ y' ∈ V, ∀ v, v ⤳ y' → Order.coheight v = 1 → v ∈ F → v ⤳ y := by
  classical
  obtain ⟨W, hW, hyW, hWO⟩ := exists_isAffineOpen_mem_and_subset hy
  haveI := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hN : NoetherianSpace W := by
    have := NoetherianSpace.range hW.fromSpec hW.fromSpec.continuous
    rw [hW.range_fromSpec] at this
    exact this
  have hC : IsClosed ((Subtype.val : W → Y) ⁻¹' F) := hF.preimage continuous_subtype_val
  obtain ⟨S, hS, hc, hi, hU⟩ := @NoetherianSpace.exists_finite_set_isClosed_irreducible _ _ hN _ hC
  let y₀ : W := ⟨y, hyW⟩
  let bad : Set W := ⋃₀ {T ∈ S | y₀ ∉ T}
  have hS' : {T ∈ S | y₀ ∉ T}.Finite := hS.subset fun T hT => hT.1
  have hbad : IsClosed bad := by
    change IsClosed (⋃₀ {T ∈ S | y₀ ∉ T})
    rw [Set.sUnion_eq_biUnion]
    exact hS'.isClosed_biUnion fun T hT => hc T hT.1
  refine ⟨⟨Subtype.val '' badᶜ, W.isOpen.isOpenMap_subtype_val _ hbad.isOpen_compl⟩,
    ⟨y₀, ?_, rfl⟩, ?_, ?_⟩
  · rintro ⟨T, ⟨-, hyT⟩, hyT'⟩
    exact hyT hyT'
  · rintro _ ⟨x, -, rfl⟩
    exact hWO x.2
  · rintro _ ⟨x, hx, rfl⟩ v hv hcv hvF
    have hvW : v ∈ W := hv.mem_open W.isOpen x.2
    let v' : W := ⟨v, hvW⟩
    have hv' : v' ⤳ x := Topology.IsInducing.subtypeVal.specializes_iff.1 hv
    have hvS : v' ∈ ⋃₀ S := hU ▸ hvF
    obtain ⟨T, hT, hvT⟩ := hvS
    have hxT : x ∈ T := hv'.mem_closed (hc T hT) hvT
    have hyT : y₀ ∈ T := by
      by_contra h
      exact hx ⟨T, ⟨hT, h⟩, hxT⟩
    obtain ⟨g, hg⟩ := QuasiSober.sober (hi T hT) (hc T hT)
    have hgF : g.1 ∈ F := by
      have : g ∈ ⋃₀ S := ⟨T, hT, hg.mem⟩
      rw [← hU] at this
      exact this
    have hgv : g.1 ⤳ v := Topology.IsInducing.subtypeVal.specializes_iff.2 (hg.specializes hvT)
    have hgy : g.1 ⤳ y := Topology.IsInducing.subtypeVal.specializes_iff.2 (hg.specializes hyT)
    have hgη : g.1 < genericPoint Y := by
      refine lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_
      have e' : g.1 = genericPoint Y := (Specializes.antisymm e (genericPoint_specializes _)).eq
      exact hη (e' ▸ hgF)
    have hvg : v = g.1 := by
      by_contra hne
      have h₃ := Order.coheight_add_one_le (show v < g.1 from lt_of_le_not_ge hgv fun e =>
        hne (Specializes.antisymm e hgv).eq)
      have h₄ := Order.coheight_add_one_le hgη
      rw [hcv] at h₃
      have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
      exact absurd h₅ (by decide)
    rw [hvg]
    exact hgy

/- English proof (translation)
Introduce `Y _ _ q n _ B y U hy z J w u hη hc`. Establish `hηb : ∀ j ∈ J, genericPoint Y ∈ Y.basicOpen (z j)` using `fun j hj => (Y.mem_basicOpen (z j) _ (gen_mem hy)).2 (by`. Establish `: IsUnit (u j : Y.functionField)` using `(u j).isUnit`. Rewrite `this` using `[hc.val j hj]`. Conclude with `this)`.

Establish `hord0 : ∀ j ∈ J, ∀ v ∈ Y.basicOpen (z j), Scheme.ord (u j : Y.functionField) v = 0`. Introduce `j hj v hv`. Use `haveI : Nonempty (Y.basicOpen (z j)) := ⟨⟨v, hv⟩⟩`. Establish `h1` using `Scheme.ord_of_isUnit (U := Y.basicOpen (z j)) (Y.toRingedSpace.isUnit_res_basicOpen (z j)) hv`. Rewrite using `[hc.val j hj, ← h1]`.

Use `congr 1`. Conclude with `(Y.presheaf.germ_res_apply (homOfLE (Y.basicOpen_le (z j))) _ _ (z j)).symm`. Set `F : Set Y` to `(B : Set Y) ∪ ⋃ j ∈ J, ((Y.basicOpen (z j) : Set Y))ᶜ`. Establish `hF : IsClosed F` using `B.isClosed.union (isClosed_biUnion_finset fun j _ => (Y.basicOpen (z j)).isOpen.isClosed_compl)`. Establish `hηF : genericPoint Y ∉ F`.

Introduce and unpack `(h | h)`. Conclude with `hη h`. Take `⟨j, hj, h⟩` from `Set.mem_iUnion₂.1 h`. Conclude with `h (hηb j hj)`. Take `⟨V, hyV, hVU, hV⟩` from `exists_nbhd_specializes_of_isClosed F hF hηF hy`.

Use `⟨V, hyV, fun y' hy' => ?_⟩` and prove the remaining obligations. Establish `hy'U : y' ∈ U` using `hVU hy'`. Use `⟨hy'U, J.filter (fun j => w j ⤳ y'), Finset.filter_subset _ _, ⟨hc.frame, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `j hj`. Conclude with `hc.val j (Finset.mem_filter.1 hj).1`.

Introduce `j hj`. Conclude with `(Finset.mem_filter.1 hj).2`. Introduce `j hj`. Conclude with `hc.coheight j (Finset.mem_filter.1 hj).1`. Conclude with `hc.inj.mono fun j hj => (Finset.mem_filter.1 hj).1`.

Introduce `j hj`. Conclude with `hc.ord_self j (Finset.mem_filter.1 hj).1`. Introduce `j hj v hv hne`. Establish `hjJ` using `(Finset.mem_filter.1 hj).1`. Distinguish the cases in `hb : v ∈ Y.basicOpen (z j)`.

Conclude with `hord0 j hjJ v hb`. Distinguish the cases in `hcv : Order.coheight v = 1`. Conclude with `hc.ord_other j hjJ v (hV y' hy' v hv hcv (Or.inr (Set.mem_iUnion₂.2 ⟨j, hjJ, hb⟩))) hne`. Conclude with `Scheme.ord_eq_zero_of_coheight_neq_one hcv _`. Introduce `v hv hcv`.

Prove the components needed by the constructor for the conclusion. Introduce `hvB`. Take `⟨j, hj, rfl⟩` from `(hc.mem v (hV y' hy' v hv hcv (Or.inl hvB)) hcv).1 hvB`. Conclude with `⟨j, Finset.mem_filter.2 ⟨hj, hv⟩, rfl⟩`. Introduce and unpack `⟨j, hj, rfl⟩`.

Establish `hjJ` using `(Finset.mem_filter.1 hj).1`. Conclude with `(hc.mem _ (hc.spec j hjJ) hcv).2 ⟨j, hjJ, rfl⟩`. Introduce `j hj hb`. Establish `hjJ` using `(Finset.mem_filter.1 hj).1`. Establish `h0` using `hord0 j hjJ (w j) ((Finset.mem_filter.1 hj).2.mem_open (Y.basicOpen (z j)).isOpen hb)`.

Rewrite `h0` using `[hc.ord_self j hjJ]`. Conclude with `one_ne_zero h0`.
-/
theorem isSncChart_spread : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ)
    (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U)
    (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ),
    genericPoint Y ∉ B → IsSncChart q n B y U hy z J w u → ∃ V : Y.Opens, y ∈ V ∧ ∀ y' ∈ V,
      ∃ (hy' : y' ∈ U) (J' : Finset (Fin n)), J' ⊆ J ∧ IsSncChart q n B y' U hy' z J' w u ∧
        ∀ j ∈ J', y' ∉ Y.basicOpen (z j) := by
  intro Y _ _ q n _ B y U hy z J w u hη hc
  classical
  have hηb : ∀ j ∈ J, genericPoint Y ∈ Y.basicOpen (z j) := fun j hj =>
    (Y.mem_basicOpen (z j) _ (gen_mem hy)).2 (by
      have : IsUnit (u j : Y.functionField) := (u j).isUnit
      rw [hc.val j hj] at this
      exact this)
  have hord0 : ∀ j ∈ J, ∀ v ∈ Y.basicOpen (z j), Scheme.ord (u j : Y.functionField) v = 0 := by
    intro j hj v hv
    haveI : Nonempty (Y.basicOpen (z j)) := ⟨⟨v, hv⟩⟩
    have h1 := Scheme.ord_of_isUnit (U := Y.basicOpen (z j))
      (Y.toRingedSpace.isUnit_res_basicOpen (z j)) hv
    rw [hc.val j hj, ← h1]
    congr 1
    exact (Y.presheaf.germ_res_apply (homOfLE (Y.basicOpen_le (z j))) _ _ (z j)).symm
  let F : Set Y := (B : Set Y) ∪ ⋃ j ∈ J, ((Y.basicOpen (z j) : Set Y))ᶜ
  have hF : IsClosed F := B.isClosed.union
    (isClosed_biUnion_finset fun j _ => (Y.basicOpen (z j)).isOpen.isClosed_compl)
  have hηF : genericPoint Y ∉ F := by
    rintro (h | h)
    · exact hη h
    · obtain ⟨j, hj, h⟩ := Set.mem_iUnion₂.1 h
      exact h (hηb j hj)
  obtain ⟨V, hyV, hVU, hV⟩ := exists_nbhd_specializes_of_isClosed F hF hηF hy
  refine ⟨V, hyV, fun y' hy' => ?_⟩
  have hy'U : y' ∈ U := hVU hy'
  refine ⟨hy'U, J.filter (fun j => w j ⤳ y'), Finset.filter_subset _ _,
    ⟨hc.frame, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j hj
    exact hc.val j (Finset.mem_filter.1 hj).1
  · intro j hj
    exact (Finset.mem_filter.1 hj).2
  · intro j hj
    exact hc.coheight j (Finset.mem_filter.1 hj).1
  · exact hc.inj.mono fun j hj => (Finset.mem_filter.1 hj).1
  · intro j hj
    exact hc.ord_self j (Finset.mem_filter.1 hj).1
  · intro j hj v hv hne
    have hjJ := (Finset.mem_filter.1 hj).1
    by_cases hb : v ∈ Y.basicOpen (z j)
    · exact hord0 j hjJ v hb
    by_cases hcv : Order.coheight v = 1
    · exact hc.ord_other j hjJ v (hV y' hy' v hv hcv (Or.inr (Set.mem_iUnion₂.2 ⟨j, hjJ, hb⟩))) hne
    · exact Scheme.ord_eq_zero_of_coheight_neq_one hcv _
  · intro v hv hcv
    constructor
    · intro hvB
      obtain ⟨j, hj, rfl⟩ := (hc.mem v (hV y' hy' v hv hcv (Or.inl hvB)) hcv).1 hvB
      exact ⟨j, Finset.mem_filter.2 ⟨hj, hv⟩, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      have hjJ := (Finset.mem_filter.1 hj).1
      exact (hc.mem _ (hc.spec j hjJ) hcv).2 ⟨j, hjJ, rfl⟩
  · intro j hj hb
    have hjJ := (Finset.mem_filter.1 hj).1
    have h0 := hord0 j hjJ (w j) ((Finset.mem_filter.1 hj).2.mem_open (Y.basicOpen (z j)).isOpen hb)
    rw [hc.ord_self j hjJ] at h0
    exact one_ne_zero h0

end GlobalTheory.PairStep
