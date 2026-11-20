import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.AbsSumP
end PositivityTheory.Rg.BcB.G3.AbsSumP

/- English proof (translation)
Introduce `V C S L A o f D loc m N hA ho hf hD hN hcard`. Use `set T : Set V := {v | ¬ ∀ l ∈ A v, f v l = if l = o v then 1 else 0} with hTdef`. Establish `hT : T.Finite` using `Filter.eventually_cofinite.mp hf`. Set `_ : ∀ v, Fintype (A v)` to `fun v => (hA v).fintype`. Choose the witnesses or unpack the hypotheses as in `⟨U, hUS, hgood⟩ : ∃ U : Finset V, (∀ v ∈ U, v ∈ S) ∧ ∀ v, v ∈ S → v ∉ U → ∀ l ∈ A v, f v l = if l = o v then 1 else 0 := by`.

Use `⟨hT.toFinset.filter (fun v => v ∈ S), fun v hv => (Finset.mem_filter.mp hv).2, ?_⟩` and prove the remaining obligations. Introduce `v hvS hvU`. Assume the negation of the conclusion as `h`. Conclude with `hvU (Finset.mem_filter.mpr ⟨hT.mem_toFinset.mpr h, hvS⟩)`. Establish `hkey : ∀ c ∈ D, (∏ᶠ v ∈ S, f v (loc c v)) = if (∀ v ∈ S, v ∉ U → loc c v = o v) then ∏ v ∈ U, f v (loc c v) else 0`.

Introduce `c hc`. Take `⟨hcA, hcf⟩` from `hD c hc`. Establish `hW : {v | ¬ loc c v = o v}.Finite` using `Filter.eventually_cofinite.mp hcf`. Choose the witnesses or unpack the hypotheses as in `⟨F, hUF, hFS, hWF⟩ : ∃ F : Finset V, U ⊆ F ∧ (↑F : Set V) ⊆ S ∧ ∀ v ∈ S, ¬ loc c v = o v → v ∈ F := by`. Use `⟨U ∪ hW.toFinset.filter (fun v => v ∈ S), Finset.subset_union_left, ?_, ?_⟩` and prove the remaining obligations.

Introduce `v hv`. Break down `Finset.mem_union.mp (Finset.mem_coe.mp hv) with hv | hv` into its components or cases. Conclude with `hUS v hv`. Conclude with `(Finset.mem_filter.mp hv).2`. Introduce `v hvS hne`.

Conclude with `Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hW.mem_toFinset.mpr hne, hvS⟩)`. Establish `hsupp : S ∩ Function.mulSupport (fun v => f v (loc c v)) ⊆ ↑F`. Introduce and unpack `v ⟨hvS, hv1⟩`. Rewrite `hv1` using `[Function.mem_mulSupport]`. Rewrite using `[Finset.mem_coe]`.

Distinguish the cases in `hvU : v ∈ U`. Conclude with `hUF hvU`. Apply `hWF v hvS` to reduce the goal to its premises. Introduce `heq`. Apply `hv1` to reduce the goal to its premises.

Rewrite using `[hgood v hvS hvU _ (hcA v), if_pos heq]`. Rewrite using `[finprod_mem_eq_prod_of_subset _ hsupp hFS]`. Rewrite using `[← Finset.prod_sdiff hUF]`. Establish `hrest : ∀ v ∈ F \ U, f v (loc c v) = if loc c v = o v then 1 else 0`. Introduce `v hv`.

Rewrite `hv` using `[Finset.mem_sdiff]`. Conclude with `hgood v (hFS hv.1) hv.2 _ (hcA v)`. Rewrite using `[Finset.prod_congr rfl hrest, Finset.prod_boole]`. Establish `hiff : (∀ v ∈ F \ U, loc c v = o v) ↔ (∀ v ∈ S, v ∉ U → loc c v = o v)`. Prove the components needed by the constructor for the conclusion.

Introduce `h v hvS hvU`. Assume the negation of the conclusion as `hne`. Conclude with `hne (h v (Finset.mem_sdiff.mpr ⟨hWF v hvS hne, hvU⟩))`. Introduce `h v hv`. Rewrite `hv` using `[Finset.mem_sdiff]`.

Conclude with `h v (hFS hv.1) hv.2`. Distinguish the cases in `hc' : ∀ v ∈ S, v ∉ U → loc c v = o v`. Rewrite using `[if_pos (hiff.mpr hc'), if_pos hc', one_mul]`. Rewrite using `[if_neg (fun h => hc' (hiff.mp h)), if_neg hc', zero_mul]`. Set `zmap : C → ((v : U) → A v.1)` to `fun c v => if h : loc c v.1 ∈ A v.1 then ⟨loc c v.1, h⟩ else ⟨o v.1, ho v.1⟩`.

Set `yz : ((v : U) → A v.1) → (∀ v, L v)` to `fun z v => if h : v ∈ U then (z ⟨v, h⟩).1 else o v`. Establish `hyz_ok : ∀ z, (∀ v, yz z v ∈ A v) ∧ (∀ᶠ v in cofinite, yz z v = o v)`. Introduce `z`. Use `⟨fun v => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [yz] split_ifs with h`.

Conclude with `(z ⟨v, h⟩).2`. Conclude with `ho v`. Rewrite using `[Filter.eventually_cofinite]`. Apply `(U.finite_toSet).subset` to reduce the goal to its premises. Introduce `v hv`.

Assume the negation of the conclusion as `hvU`. Conclude with `hv (by dsimp only [yz]; rw [dif_neg (fun h => hvU (Finset.mem_coe.mpr h))])`. Establish `hfibfin : ∀ z, {c | c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v}.Finite`. Introduce `z`. Establish `h` using `hcard (yz z) (hyz_ok z).1 (hyz_ok z).2`.

Establish `hne : Nat.card {c : C // c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v} ≠ 0`. Introduce `h0`. Rewrite `h` using `[h0, zero_mul]`. Conclude with `hN h.symm`. Conclude with `Set.finite_coe_iff.mp (Nat.finite_of_card_ne_zero hne)`.

Use `set G : Set C := {c | c ∈ D ∧ ∀ v ∈ S, v ∉ U → loc c v = o v} with hGdef`. Establish `hGsub : G ⊆ ⋃ z, {c | c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v}`. Introduce and unpack `c ⟨hcD, hc⟩`. Use `Set.mem_iUnion.mpr ⟨zmap c, hcD, fun v hvS => ?_⟩` and prove the remaining obligations. Simplify using `only [yz, zmap]`.

Distinguish the cases in `hvU : v ∈ U`. Rewrite using `[dif_pos hvU, dif_pos ((hD c hcD).1 v)]`. Rewrite using `[dif_neg hvU]`. Conclude with `hc v hvS hvU`. Establish `hGfin : G.Finite` using `(Set.finite_iUnion hfibfin).subset hGsub`.

Establish `hsuppG : ∀ c, c ∈ D → (∏ᶠ v ∈ S, f v (loc c v)) ≠ 0 → c ∈ G`. Introduce `c hcD hne`. Rewrite `hne` using `[hkey c hcD]`. Assume the negation of the conclusion as `hcG`. Apply `hne` to reduce the goal to its premises.

Rewrite using `[if_neg]`. Introduce `h`. Conclude with `hcG ⟨hcD, h⟩`. Use `⟨hGfin.subset (fun c hc => hsuppG c hc.1 hc.2), ?_⟩` and prove the remaining obligations. Establish `hsum1 : (∑ᶠ c : C, if c ∈ D then ∏ᶠ v ∈ S, f v (loc c v) else 0) = ∑ c ∈ hGfin.toFinset, ∏ v : U, f v.1 (zmap c v).1`.

Rewrite using `[finsum_eq_sum_of_support_subset _ (s := hGfin.toFinset) ?_]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `c hc`. Rewrite `hc` using `[Set.Finite.mem_toFinset]`. Take `⟨hcD, hcG⟩` from `hc`.

Rewrite using `[if_pos hcD, hkey c hcD, if_pos hcG, ← Finset.prod_coe_sort U (fun v => f v (loc c v))]`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `v _`. Simplify using `only [zmap]`. Rewrite using `[dif_pos ((hD c hcD).1 v.1)]`.

Introduce `c hc`. Rewrite `hc` using `[Function.mem_support]`. Rewrite using `[Set.Finite.coe_toFinset]`. Distinguish the cases in `hcD : c ∈ D`. Rewrite `hc` using `[if_pos hcD]`.

Conclude with `hsuppG c hcD hc`. Rewrite `hc` using `[if_neg hcD]`. Conclude with `absurd rfl hc`. Establish `hmem : ∀ z c, (c ∈ hGfin.toFinset ∧ zmap c = z) ↔ (c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v)`. Introduce `z c`.

Rewrite using `[Set.Finite.mem_toFinset]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hcD, hcG⟩, hzc⟩`. Use `⟨hcD, fun v hvS => ?_⟩` and prove the remaining obligations. Simplify using `only [yz]`.

Distinguish the cases in `hvU : v ∈ U`. Rewrite using `[dif_pos hvU, ← hzc] dsimp only [zmap]`. Rewrite using `[dif_pos ((hD c hcD).1 v)]`. Rewrite using `[dif_neg hvU]`. Conclude with `hcG v hvS hvU`.

Introduce and unpack `⟨hcD, hc⟩`. Use `⟨⟨hcD, fun v hvS hvU => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hc v hvS]`. Simplify using `only [yz]`. Rewrite using `[dif_neg hvU]`.

Use function extensionality and compare the values at `v`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [zmap]`. Rewrite using `[dif_pos ((hD c hcD).1 v.1)]`. Use `show loc c v.1 = (z v).1`.

Rewrite using `[hc v.1 (hUS v.1 v.2)]`. Simplify using `only [yz]`. Rewrite using `[dif_pos v.2]`. Establish `hcardfib : ∀ z (s' : Finset C), (∀ c, c ∈ s' ↔ (c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v)) → s'.card = Nat.card {c : C // c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v}`. Introduce `z s' hs'`.

Rewrite using `[← Nat.card_eq_finsetCard]`. Conclude with `Nat.card_congr (Equiv.subtypeEquivRight hs')`. Rewrite using `[hsum1, ← Finset.sum_fiberwise hGfin.toFinset zmap (fun c => ∏ v : U, f v.1 (zmap c v).1), Finset.sum_mul]`. Rewrite using `[Finset.sum_congr rfl (g := fun z => (N : ℂ) * ∏ v : U, f v.1 (z v).1) ?_, ← Finset.mul_sum]`. Use `swap`.

Introduce `z _`. Rewrite using `[Finset.sum_congr rfl (g := fun _ => ∏ v : U, f v.1 (z v).1) ?_, Finset.sum_const, nsmul_eq_mul, mul_right_comm]`. Use `swap`. Introduce `c hc`. Rewrite using `[(Finset.mem_filter.mp hc).2]`.

Use `congr 1`. Rewrite using `[← hcard (yz z) (hyz_ok z).1 (hyz_ok z).2, Nat.cast_mul, hcardfib z _ (fun c => Finset.mem_filter.trans (hmem z c))]`. Use `congr 1`. Establish `hR : ∀ v, (∑ᶠ l : L v, if l ∈ A v then f v l else 0) = ∑ l : A v, f v l.1`. Introduce `v`.

Rewrite using `[finsum_eq_sum_of_support_subset _ (s := (A v).toFinset) ?_, Finset.sum_set_coe (f := fun l => f v l)]`. Conclude with `Finset.sum_congr rfl (fun l hl => if_pos (Set.mem_toFinset.mp hl))`. Introduce `l hl`. Rewrite `hl` using `[Function.mem_support]`. Rewrite using `[Set.coe_toFinset]`.

Assume the negation of the conclusion as `h`. Conclude with `hl (if_neg h)`. Establish `hR1 : ∀ v, v ∈ S → v ∉ U → (∑ᶠ l : L v, if l ∈ A v then f v l else 0) = 1`. Introduce `v hvS hvU`. Rewrite using `[hR, Finset.sum_set_coe (f := fun l => f v l), Finset.sum_congr rfl (fun l hl => hgood v hvS hvU l (Set.mem_toFinset.mp hl)), Finset.sum_ite_eq', if_pos (Set.mem_toFinset.mpr (ho v))]`.

Rewrite using `[← Fintype.prod_sum (fun (v : U) (l : A v.1) => f v.1 l.1)]`. Rewrite using `[finprod_mem_eq_prod_of_subset _ (t := U) ?_ ?_]`. Rewrite using `[← Finset.prod_coe_sort U]`. Conclude with `Finset.prod_congr rfl (fun v _ => (hR v.1).symm)`. Introduce and unpack `v ⟨hvS, hv1⟩`.

Assume the negation of the conclusion as `hvU`. Rewrite `hv1` using `[Function.mem_mulSupport]`. Conclude with `hv1 (hR1 v hvS hvU)`. Introduce `v hv`. Conclude with `hUS v hv`.
-/
theorem PositivityTheory.Rg.BcB.G3.absSum_pf : PositivityTheory.Rg.BcB.G3.AbsSum := by
  intro V C S L A o f D loc m N hA ho hf hD hN hcard
  set T : Set V := {v | ¬ ∀ l ∈ A v, f v l = if l = o v then 1 else 0} with hTdef
  have hT : T.Finite := Filter.eventually_cofinite.mp hf
  let _ : ∀ v, Fintype (A v) := fun v => (hA v).fintype
  obtain ⟨U, hUS, hgood⟩ : ∃ U : Finset V, (∀ v ∈ U, v ∈ S) ∧
      ∀ v, v ∈ S → v ∉ U → ∀ l ∈ A v, f v l = if l = o v then 1 else 0 := by
    refine ⟨hT.toFinset.filter (fun v => v ∈ S), fun v hv => (Finset.mem_filter.mp hv).2, ?_⟩
    intro v hvS hvU
    by_contra h
    exact hvU (Finset.mem_filter.mpr ⟨hT.mem_toFinset.mpr h, hvS⟩)
  have hkey : ∀ c ∈ D, (∏ᶠ v ∈ S, f v (loc c v)) =
      if (∀ v ∈ S, v ∉ U → loc c v = o v) then ∏ v ∈ U, f v (loc c v) else 0 := by
    intro c hc
    obtain ⟨hcA, hcf⟩ := hD c hc
    have hW : {v | ¬ loc c v = o v}.Finite := Filter.eventually_cofinite.mp hcf
    obtain ⟨F, hUF, hFS, hWF⟩ : ∃ F : Finset V, U ⊆ F ∧ (↑F : Set V) ⊆ S ∧
        ∀ v ∈ S, ¬ loc c v = o v → v ∈ F := by
      refine ⟨U ∪ hW.toFinset.filter (fun v => v ∈ S), Finset.subset_union_left, ?_, ?_⟩
      · intro v hv
        rcases Finset.mem_union.mp (Finset.mem_coe.mp hv) with hv | hv
        · exact hUS v hv
        · exact (Finset.mem_filter.mp hv).2
      · intro v hvS hne
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hW.mem_toFinset.mpr hne, hvS⟩)
    have hsupp : S ∩ Function.mulSupport (fun v => f v (loc c v)) ⊆ ↑F := by
      rintro v ⟨hvS, hv1⟩
      rw [Function.mem_mulSupport] at hv1
      rw [Finset.mem_coe]
      by_cases hvU : v ∈ U
      · exact hUF hvU
      · apply hWF v hvS
        intro heq
        apply hv1
        rw [hgood v hvS hvU _ (hcA v), if_pos heq]
    rw [finprod_mem_eq_prod_of_subset _ hsupp hFS]
    rw [← Finset.prod_sdiff hUF]
    have hrest : ∀ v ∈ F \ U, f v (loc c v) = if loc c v = o v then 1 else 0 := by
      intro v hv
      rw [Finset.mem_sdiff] at hv
      exact hgood v (hFS hv.1) hv.2 _ (hcA v)
    rw [Finset.prod_congr rfl hrest, Finset.prod_boole]
    have hiff : (∀ v ∈ F \ U, loc c v = o v) ↔ (∀ v ∈ S, v ∉ U → loc c v = o v) := by
      constructor
      · intro h v hvS hvU
        by_contra hne
        exact hne (h v (Finset.mem_sdiff.mpr ⟨hWF v hvS hne, hvU⟩))
      · intro h v hv
        rw [Finset.mem_sdiff] at hv
        exact h v (hFS hv.1) hv.2
    by_cases hc' : ∀ v ∈ S, v ∉ U → loc c v = o v
    · rw [if_pos (hiff.mpr hc'), if_pos hc', one_mul]
    · rw [if_neg (fun h => hc' (hiff.mp h)), if_neg hc', zero_mul]
  let zmap : C → ((v : U) → A v.1) := fun c v =>
    if h : loc c v.1 ∈ A v.1 then ⟨loc c v.1, h⟩ else ⟨o v.1, ho v.1⟩
  let yz : ((v : U) → A v.1) → (∀ v, L v) := fun z v => if h : v ∈ U then (z ⟨v, h⟩).1 else o v
  have hyz_ok : ∀ z, (∀ v, yz z v ∈ A v) ∧ (∀ᶠ v in cofinite, yz z v = o v) := by
    intro z
    refine ⟨fun v => ?_, ?_⟩
    · dsimp only [yz]
      split_ifs with h
      · exact (z ⟨v, h⟩).2
      · exact ho v
    · rw [Filter.eventually_cofinite]
      apply (U.finite_toSet).subset
      intro v hv
      by_contra hvU
      exact hv (by dsimp only [yz]; rw [dif_neg (fun h => hvU (Finset.mem_coe.mpr h))])
  have hfibfin : ∀ z, {c | c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v}.Finite := by
    intro z
    have h := hcard (yz z) (hyz_ok z).1 (hyz_ok z).2
    have hne : Nat.card {c : C // c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v} ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h; exact hN h.symm
    exact Set.finite_coe_iff.mp (Nat.finite_of_card_ne_zero hne)
  set G : Set C := {c | c ∈ D ∧ ∀ v ∈ S, v ∉ U → loc c v = o v} with hGdef
  have hGsub : G ⊆ ⋃ z, {c | c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v} := by
    rintro c ⟨hcD, hc⟩
    refine Set.mem_iUnion.mpr ⟨zmap c, hcD, fun v hvS => ?_⟩
    dsimp only [yz, zmap]
    by_cases hvU : v ∈ U
    · rw [dif_pos hvU, dif_pos ((hD c hcD).1 v)]
    · rw [dif_neg hvU]; exact hc v hvS hvU
  have hGfin : G.Finite := (Set.finite_iUnion hfibfin).subset hGsub
  have hsuppG : ∀ c, c ∈ D → (∏ᶠ v ∈ S, f v (loc c v)) ≠ 0 → c ∈ G := by
    intro c hcD hne
    rw [hkey c hcD] at hne
    by_contra hcG
    apply hne
    rw [if_neg]
    intro h; exact hcG ⟨hcD, h⟩
  refine ⟨hGfin.subset (fun c hc => hsuppG c hc.1 hc.2), ?_⟩
  have hsum1 : (∑ᶠ c : C, if c ∈ D then ∏ᶠ v ∈ S, f v (loc c v) else 0) =
      ∑ c ∈ hGfin.toFinset, ∏ v : U, f v.1 (zmap c v).1 := by
    rw [finsum_eq_sum_of_support_subset _ (s := hGfin.toFinset) ?_]
    · apply Finset.sum_congr rfl
      intro c hc
      rw [Set.Finite.mem_toFinset] at hc
      obtain ⟨hcD, hcG⟩ := hc
      rw [if_pos hcD, hkey c hcD, if_pos hcG, ← Finset.prod_coe_sort U (fun v => f v (loc c v))]
      apply Finset.prod_congr rfl
      intro v _
      dsimp only [zmap]
      rw [dif_pos ((hD c hcD).1 v.1)]
    · intro c hc
      rw [Function.mem_support] at hc
      rw [Set.Finite.coe_toFinset]
      by_cases hcD : c ∈ D
      · rw [if_pos hcD] at hc; exact hsuppG c hcD hc
      · rw [if_neg hcD] at hc; exact absurd rfl hc
  have hmem : ∀ z c, (c ∈ hGfin.toFinset ∧ zmap c = z) ↔ (c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v) := by
    intro z c
    rw [Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨hcD, hcG⟩, hzc⟩
      refine ⟨hcD, fun v hvS => ?_⟩
      dsimp only [yz]
      by_cases hvU : v ∈ U
      · rw [dif_pos hvU, ← hzc]
        dsimp only [zmap]
        rw [dif_pos ((hD c hcD).1 v)]
      · rw [dif_neg hvU]; exact hcG v hvS hvU
    · rintro ⟨hcD, hc⟩
      refine ⟨⟨hcD, fun v hvS hvU => ?_⟩, ?_⟩
      · rw [hc v hvS]; dsimp only [yz]; rw [dif_neg hvU]
      · funext v
        apply Subtype.ext
        dsimp only [zmap]
        rw [dif_pos ((hD c hcD).1 v.1)]
        show loc c v.1 = (z v).1
        rw [hc v.1 (hUS v.1 v.2)]
        dsimp only [yz]
        rw [dif_pos v.2]
  have hcardfib : ∀ z (s' : Finset C), (∀ c, c ∈ s' ↔ (c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v)) →
      s'.card = Nat.card {c : C // c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v} := by
    intro z s' hs'
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight hs')
  rw [hsum1, ← Finset.sum_fiberwise hGfin.toFinset zmap (fun c => ∏ v : U, f v.1 (zmap c v).1),
    Finset.sum_mul]
  rw [Finset.sum_congr rfl (g := fun z => (N : ℂ) * ∏ v : U, f v.1 (z v).1) ?_, ← Finset.mul_sum]
  swap
  · intro z _
    rw [Finset.sum_congr rfl (g := fun _ => ∏ v : U, f v.1 (z v).1) ?_, Finset.sum_const, nsmul_eq_mul,
      mul_right_comm]
    swap
    · intro c hc
      rw [(Finset.mem_filter.mp hc).2]
    congr 1
    rw [← hcard (yz z) (hyz_ok z).1 (hyz_ok z).2, Nat.cast_mul,
      hcardfib z _ (fun c => Finset.mem_filter.trans (hmem z c))]
  congr 1
  have hR : ∀ v, (∑ᶠ l : L v, if l ∈ A v then f v l else 0) = ∑ l : A v, f v l.1 := by
    intro v
    rw [finsum_eq_sum_of_support_subset _ (s := (A v).toFinset) ?_,
      Finset.sum_set_coe (f := fun l => f v l)]
    · exact Finset.sum_congr rfl (fun l hl => if_pos (Set.mem_toFinset.mp hl))
    · intro l hl
      rw [Function.mem_support] at hl
      rw [Set.coe_toFinset]
      by_contra h
      exact hl (if_neg h)
  have hR1 : ∀ v, v ∈ S → v ∉ U → (∑ᶠ l : L v, if l ∈ A v then f v l else 0) = 1 := by
    intro v hvS hvU
    rw [hR, Finset.sum_set_coe (f := fun l => f v l),
      Finset.sum_congr rfl (fun l hl => hgood v hvS hvU l (Set.mem_toFinset.mp hl)), Finset.sum_ite_eq',
      if_pos (Set.mem_toFinset.mpr (ho v))]
  rw [← Fintype.prod_sum (fun (v : U) (l : A v.1) => f v.1 l.1)]
  rw [finprod_mem_eq_prod_of_subset _ (t := U) ?_ ?_]
  · rw [← Finset.prod_coe_sort U]
    exact Finset.prod_congr rfl (fun v _ => (hR v.1).symm)
  · rintro v ⟨hvS, hv1⟩
    by_contra hvU
    rw [Function.mem_mulSupport] at hv1
    exact hv1 (hR1 v hvS hvU)
  · intro v hv
    exact hUS v hv
