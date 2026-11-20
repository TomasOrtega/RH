import Formalism.PolynomialDimension.MultinomialDepth.PartnerM
import Formalism.MahlerMeasure.MahlerMeasureProofs.WeightSpaceDimensionMonotone
import Formalism.MahlerMeasure.MahlerMeasureProofs.GamInt
import Formalism.MahlerMeasure.MahlerMeasureProofs.LieMat

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM.DimensionMonotonicity Finset

namespace GlX

variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

/- English proof (translation)
Establish `h'` using `h`. Unfold `Formalism.GM.DimensionMonotonicity.GlW.IsHW Formalism.GM.DimensionMonotonicity.GlW.IsWt at h'`. Take `⟨hw, hr⟩` from `h'`. Establish `hd : ∀ c, G.E c c x = ((μ c : ℤ) : K) • x` using `fun c => by`. Use `G.diag c μ x` as an intermediate fact.

Rewrite `this` using `[hw]`. Then use the resulting hypothesis. Establish `hterm : ∀ a b, G.E a b (G.E b a x) = (((if a = b then μ a * μ a else if a < b then μ a - μ b else 0 : ℤ)) : K) • x`. Introduce `a b`. Use `split_ifs with hab hlt`. Substitute `hab` using the available equality.

Rewrite using `[hd, map_smul, hd, smul_smul, Int.cast_mul]`. Establish `hc` using `G.comm a b b a x`. Simplify using `only [if_true, eq_self_iff_true] at hc`. Rewrite `hc` using `[hr a b hlt, map_zero, sub_zero]`. Rewrite using `[hc, hd, hd, ← sub_smul, Int.cast_sub]`.

Establish `hba : b < a` using `lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hab)`. Rewrite using `[hr b a hba, map_zero, Int.cast_zero, zero_smul]`. Establish `hC : G.Cas x = ∑ a, ∑ b, G.E a b (G.E b a x)`. Simplify using `only [Formalism.GM.DimensionMonotonicity.GlW.Cas, LinearMap.sum_apply, LinearMap.comp_apply]`. Rewrite using `[hC]`.

Simplify using `only [hterm, Formalism.GM.DimensionMonotonicity.GlW.casI, Int.cast_sum, Finset.sum_smul]`.
-/
theorem cas_hw {μ : Fin r → ℤ} {x : V} (h : G.IsHW μ x) : G.Cas x = ((GlW.casI μ : ℤ) : K) • x := by
  have h' := h
  unfold Formalism.GM.DimensionMonotonicity.GlW.IsHW Formalism.GM.DimensionMonotonicity.GlW.IsWt at h'
  obtain ⟨hw, hr⟩ := h'
  have hd : ∀ c, G.E c c x = ((μ c : ℤ) : K) • x := fun c => by
    have := G.diag c μ x
    rwa [hw] at this
  have hterm : ∀ a b, G.E a b (G.E b a x) =
      (((if a = b then μ a * μ a else if a < b then μ a - μ b else 0 : ℤ)) : K) • x := by
    intro a b
    split_ifs with hab hlt
    · subst hab
      rw [hd, map_smul, hd, smul_smul, Int.cast_mul]
    · have hc := G.comm a b b a x
      simp only [if_true, eq_self_iff_true] at hc
      rw [hr a b hlt, map_zero, sub_zero] at hc
      rw [hc, hd, hd, ← sub_smul, Int.cast_sub]
    · have hba : b < a := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hab)
      rw [hr b a hba, map_zero, Int.cast_zero, zero_smul]
  have hC : G.Cas x = ∑ a, ∑ b, G.E a b (G.E b a x) := by
    simp only [Formalism.GM.DimensionMonotonicity.GlW.Cas, LinearMap.sum_apply, LinearMap.comp_apply]
  rw [hC]
  simp only [hterm, Formalism.GM.DimensionMonotonicity.GlW.casI, Int.cast_sum, Finset.sum_smul]

/- English proof (translation)
Proceed by induction on `cs with`. Consider the case `nil => simp [Formalism.GM.DimensionMonotonicity.GlW.cprod]`. Consider the case `cons c cs ih`. Simplify using `only [Formalism.GM.DimensionMonotonicity.GlW.cprod, LinearMap.comp_apply, ih, List.map_cons, List.prod_cons]`. Rewrite using `[LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul, hx, smul_comm _ (((e : ℤ) : K)), ← sub_smul, smul_smul, Int.cast_sub]`.
-/
private theorem cprod_eig_lemma {x : V} {e : ℤ} (hx : G.Cas x = ((e : ℤ) : K) • x) (cs : List ℤ) :
    G.cprod cs x = (cs.map (fun c => (((e - c : ℤ)) : K))).prod • x := by
  induction cs with
  | nil => simp [Formalism.GM.DimensionMonotonicity.GlW.cprod]
  | cons c cs ih =>
    simp only [Formalism.GM.DimensionMonotonicity.GlW.cprod, LinearMap.comp_apply, ih, List.map_cons, List.prod_cons]
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul, hx, smul_comm _ (((e : ℤ) : K)),
      ← sub_smul, smul_smul, Int.cast_sub]

/- English proof (translation)
Rewrite using `[cprod_eig_lemma G hx cs]`. Establish `h0 : (cs.map (fun c => (((e - c : ℤ)) : K))).prod = 0` using `List.prod_eq_zero (List.mem_map.mpr ⟨e, he, by simp⟩)`. Rewrite using `[h0, zero_smul]`.
-/
theorem cprod_kill {x : V} {e : ℤ} (hx : G.Cas x = ((e : ℤ) : K) • x) (cs : List ℤ) (he : e ∈ cs) :
    G.cprod cs x = 0 := by
  rw [cprod_eig_lemma G hx cs]
  have h0 : (cs.map (fun c => (((e - c : ℤ)) : K))).prod = 0 :=
    List.prod_eq_zero (List.mem_map.mpr ⟨e, he, by simp⟩)
  rw [h0, zero_smul]

noncomputable def qlist (S : Finset (Fin r → ℤ)) (c : ℤ) : List ℤ := ((S.image GlW.casI).erase c).toList

/- English proof (translation)
Introduce `x hx`. Unfold `qlist at hx`. Rewrite `hx` using `[Finset.mem_toList]`. Conclude with `Finset.ne_of_mem_erase hx`.
-/
theorem qlist_ne (S : Finset (Fin r → ℤ)) (c : ℤ) : ∀ x ∈ qlist S c, x ≠ c := by
  intro x hx
  unfold qlist at hx
  rw [Finset.mem_toList] at hx
  exact Finset.ne_of_mem_erase hx

/- English proof (translation)
Unfold `qlist`. Rewrite using `[Finset.mem_toList]`. Conclude with `Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem _ hν⟩`.
-/
theorem mem_qlist {S : Finset (Fin r → ℤ)} {c : ℤ} {ν : Fin r → ℤ} (hν : ν ∈ S) (hne : GlW.casI ν ≠ c) :
    GlW.casI ν ∈ qlist S c := by
  unfold qlist
  rw [Finset.mem_toList]
  exact Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem _ hν⟩

/- English proof (translation)
Establish `hw` using `hv`. Unfold `Formalism.GM.DimensionMonotonicity.GlW.IsWt at hw`. Establish `hd : ∀ c, G.E c c v = ((μ c : ℤ) : K) • v` using `fun c => by`. Use `G.diag c μ v` as an intermediate fact. Rewrite `this` using `[hw]`. Then use the resulting hypothesis.

Establish `hterm : ∀ a b, G.E a b (G.E b a v) - (((if a = b then μ a * μ a else if a < b then μ a - μ b else 0 : ℤ)) : K) • v ∈ U`. Introduce `a b`. Use `split_ifs with hab hlt`. Substitute `hab` using the available equality. Rewrite using `[hd, map_smul, hd, smul_smul, Int.cast_mul, sub_self]`.

Conclude with `zero_mem _`. Establish `hc` using `G.comm a b b a v`. Simplify using `only [if_true, eq_self_iff_true] at hc`. Establish `e : G.E a b (G.E b a v) - (((μ a - μ b : ℤ)) : K) • v = G.E b a (G.E a b v)`. Rewrite using `[Int.cast_sub, sub_smul, ← hd a, ← hd b, ← hc]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `hU b a _ (hr a b hlt)`. Establish `hba : b < a` using `lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hab)`. Rewrite using `[Int.cast_zero, zero_smul, sub_zero]`.

Conclude with `hU a b _ (hr b a hba)`. Establish `e2 : G.Cas v - ((GlW.casI μ : ℤ) : K) • v = ∑ a, ∑ b, (G.E a b (G.E b a v) - (((if a = b then μ a * μ a else if a < b then μ a - μ b else 0 : ℤ)) : K) • v)`. Simplify using `only [Formalism.GM.DimensionMonotonicity.GlW.Cas, Formalism.GM.DimensionMonotonicity.GlW.casI, LinearMap.sum_apply, LinearMap.comp_apply, Int.cast_sum, Finset.sum_smul, Finset.sum_sub_distrib]`. Rewrite using `[e2]`. Conclude with `sum_mem fun a _ => sum_mem fun b _ => hterm a b`.
-/
private theorem cas_wt_lemma_2 {U : Submodule K V} (hU : G.Stable U) {μ : Fin r → ℤ} {v : V} (hv : G.IsWt μ v)
    (hr : ∀ a b, a < b → G.E a b v ∈ U) : G.Cas v - ((GlW.casI μ : ℤ) : K) • v ∈ U := by
  have hw := hv
  unfold Formalism.GM.DimensionMonotonicity.GlW.IsWt at hw
  have hd : ∀ c, G.E c c v = ((μ c : ℤ) : K) • v := fun c => by
    have := G.diag c μ v
    rwa [hw] at this
  have hterm : ∀ a b, G.E a b (G.E b a v) -
      (((if a = b then μ a * μ a else if a < b then μ a - μ b else 0 : ℤ)) : K) • v ∈ U := by
    intro a b
    split_ifs with hab hlt
    · subst hab
      rw [hd, map_smul, hd, smul_smul, Int.cast_mul, sub_self]
      exact zero_mem _
    · have hc := G.comm a b b a v
      simp only [if_true, eq_self_iff_true] at hc
      have e : G.E a b (G.E b a v) - (((μ a - μ b : ℤ)) : K) • v = G.E b a (G.E a b v) := by
        rw [Int.cast_sub, sub_smul, ← hd a, ← hd b, ← hc]
        abel
      rw [e]
      exact hU b a _ (hr a b hlt)
    · have hba : b < a := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hab)
      rw [Int.cast_zero, zero_smul, sub_zero]
      exact hU a b _ (hr b a hba)
  have e2 : G.Cas v - ((GlW.casI μ : ℤ) : K) • v = ∑ a, ∑ b, (G.E a b (G.E b a v) -
      (((if a = b then μ a * μ a else if a < b then μ a - μ b else 0 : ℤ)) : K) • v) := by
    simp only [Formalism.GM.DimensionMonotonicity.GlW.Cas, Formalism.GM.DimensionMonotonicity.GlW.casI, LinearMap.sum_apply, LinearMap.comp_apply,
      Int.cast_sum, Finset.sum_smul, Finset.sum_sub_distrib]
  rw [e2]
  exact sum_mem fun a _ => sum_mem fun b _ => hterm a b

/- English proof (translation)
Establish `hcas : ∀ y ∈ U, G.Cas y ∈ U` using `fun y hy => by`. Simplify using `only [Formalism.GM.DimensionMonotonicity.GlW.Cas, LinearMap.sum_apply, LinearMap.comp_apply]`. Conclude with `sum_mem fun a _ => sum_mem fun b _ => hU a b _ (hU b a y hy)`. Proceed by induction on `cs with`. Consider the case `nil => simp [Formalism.GM.DimensionMonotonicity.GlW.cprod]`.

Consider the case `cons c cs ih`. Establish `key : G.cprod (c :: cs) v - ((c :: cs).map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • v = (cs.map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • (G.Cas v - ((GlW.casI μ : ℤ) : K) • v) + (G.Cas (G.cprod cs v - (cs.map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • v) - ((c …`. Simplify using `only [Formalism.GM.DimensionMonotonicity.GlW.cprod, LinearMap.comp_apply, List.map_cons, List.prod_cons, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul, Int.cast_sub]`. Use `module`. Rewrite using `[key]`.

Conclude with `add_mem (U.smul_mem _ (cas_wt_lemma_2 G hU hv hr)) (sub_mem (hcas _ ih) (U.smul_mem _ ih))`.
-/
theorem cprod_mod {U : Submodule K V} (hU : G.Stable U) {μ : Fin r → ℤ} {v : V} (hv : G.IsWt μ v)
    (hr : ∀ a b, a < b → G.E a b v ∈ U) (cs : List ℤ) :
    G.cprod cs v - (cs.map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • v ∈ U := by
  have hcas : ∀ y ∈ U, G.Cas y ∈ U := fun y hy => by
    simp only [Formalism.GM.DimensionMonotonicity.GlW.Cas, LinearMap.sum_apply, LinearMap.comp_apply]
    exact sum_mem fun a _ => sum_mem fun b _ => hU a b _ (hU b a y hy)
  induction cs with
  | nil => simp [Formalism.GM.DimensionMonotonicity.GlW.cprod]
  | cons c cs ih =>
    have key : G.cprod (c :: cs) v - ((c :: cs).map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • v =
        (cs.map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • (G.Cas v - ((GlW.casI μ : ℤ) : K) • v) +
        (G.Cas (G.cprod cs v - (cs.map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • v) -
          ((c : ℤ) : K) • (G.cprod cs v - (cs.map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • v)) := by
      simp only [Formalism.GM.DimensionMonotonicity.GlW.cprod, LinearMap.comp_apply, List.map_cons, List.prod_cons,
        LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul, Int.cast_sub]
      module
    rw [key]
    exact add_mem (U.smul_mem _ (cas_wt_lemma_2 G hU hv hr)) (sub_mem (hcas _ ih) (U.smul_mem _ ih))

/- English proof (translation)
Unfold `Formalism.GM.DimensionMonotonicity.GlW.Stable at *`. Introduce `a b x hx`. Use `Submodule.iSup_induction U (motive := fun x => G.E a b x ∈ ⨆ i, U i) hx ?_ ?_ ?_` and prove the remaining obligations. Introduce `i y hy`. Conclude with `Submodule.mem_iSup_of_mem i (hU i a b y hy)`.

Simplify using the standard rewrite rules. Introduce `y z hy hz`. Rewrite using `[map_add]`. Conclude with `add_mem hy hz`.
-/
theorem iSup_stable {ι : Sort*} {U : ι → Submodule K V} (hU : ∀ i, G.Stable (U i)) : G.Stable (⨆ i, U i) := by
  unfold Formalism.GM.DimensionMonotonicity.GlW.Stable at *
  intro a b x hx
  refine Submodule.iSup_induction U (motive := fun x => G.E a b x ∈ ⨆ i, U i) hx ?_ ?_ ?_
  · intro i y hy
    exact Submodule.mem_iSup_of_mem i (hU i a b y hy)
  · simp
  · intro y z hy hz
    rw [map_add]
    exact add_mem hy hz

/- English proof (translation)
Unfold `Formalism.GM.DimensionMonotonicity.GlW.Stable at *`. Introduce `a b x hx`. Rewrite `hx`, the goal using `[Submodule.mem_inf]`. Conclude with `⟨hU a b x hx.1, hU' a b x hx.2⟩`.
-/
theorem inf_stable {U U' : Submodule K V} (hU : G.Stable U) (hU' : G.Stable U') : G.Stable (U ⊓ U') := by
  unfold Formalism.GM.DimensionMonotonicity.GlW.Stable at *
  intro a b x hx
  rw [Submodule.mem_inf] at hx ⊢
  exact ⟨hU a b x hx.1, hU' a b x hx.2⟩

/- English proof (translation)
Introduce `x hx`. Establish `hy : G.comp ν x ∈ G.gS {v}` using `G.graded_of (G.gS_stable _) ν x hx`. Distinguish the cases in `h0 : G.comp ν x = 0`. Rewrite using `[h0, map_zero]`. Establish `hνla : Dle ν la` using `G.wt_le_of_mem hv hx h0`.

Establish `hla : DomW la` using `G.dom_of_hwmod G.bot_stable hW ⟨S, hS⟩ hvW (by rwa [Submodule.mem_bot]) hv.1 (fun a b h => by rw [hv.2 a b h]; exact Submodule.zero_mem _)`. Establish `hlt` using `cas_lt hμ hla (Dle_trans hle hνla) (hne hνla).symm`. Establish `hlaS : la ∈ S`. Assume the negation of the conclusion as `hn`. Conclude with `hv0 (by have := hS v hvW la hn; rwa [hv.1] at this)`.

Conclude with `cprod_kill G (G.Cas_gS hv hy) _ (mem_qlist hlaS hlt.ne')`.
-/
theorem gen_kill {W : Submodule K V} (hW : G.Stable W) {S : Finset (Fin r → ℤ)}
    (hS : ∀ x ∈ W, ∀ μ ∉ S, G.comp μ x = 0) {la : Fin r → ℤ} {v : V} (hv : G.IsHW la v) (hvW : v ∈ W)
    (hv0 : v ≠ 0) {μ ν : Fin r → ℤ} (hμ : DomW μ) (hle : Dle μ ν) (hne : Dle ν la → la ≠ μ) :
    ∀ x ∈ G.gS {v}, G.cprod (qlist S (GlW.casI μ)) (G.comp ν x) = 0 := by
  intro x hx
  have hy : G.comp ν x ∈ G.gS {v} := G.graded_of (G.gS_stable _) ν x hx
  by_cases h0 : G.comp ν x = 0
  · rw [h0, map_zero]
  have hνla : Dle ν la := G.wt_le_of_mem hv hx h0
  have hla : DomW la := G.dom_of_hwmod G.bot_stable hW ⟨S, hS⟩ hvW (by rwa [Submodule.mem_bot])
      hv.1 (fun a b h => by rw [hv.2 a b h]; exact Submodule.zero_mem _)
  have hlt := cas_lt hμ hla (Dle_trans hle hνla) (hne hνla).symm
  have hlaS : la ∈ S := by
    by_contra hn
    exact hv0 (by have := hS v hvW la hn; rwa [hv.1] at this)
  exact cprod_kill G (G.Cas_gS hv hy) _ (mem_qlist hlaS hlt.ne')

end GlX

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM.DimensionMonotonicity Finset

namespace GlX

variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

/- English proof (translation)
Establish `hUs : G.Stable (⨆ i, G.gS {h i})` using `iSup_stable G (fun i => G.gS_stable _)`. Assume the negation of the conclusion as `hn`. Take `⟨v, hvW, hvU, μ, hvw, hr⟩` from `G.exists_hwmod (G.graded_of hW) (G.raising_of hW) ⟨S, hS⟩ hn`. Establish `hμ : DomW μ` using `G.dom_of_hwmod hUs hW ⟨S, hS⟩ hvW hvU hvw hr`. Establish `hs : (((qlist S (GlW.casI μ)).map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod) ≠ 0` using `cprod_ne (V := V) (GlW.casI μ) _ (qlist_ne S _)`.

Establish `hmod` using `cprod_mod G hUs hvw hr (qlist S (GlW.casI μ))`. Establish `hv'U : ((((qlist S (GlW.casI μ)).map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod)⁻¹ • G.cprod (qlist S (GlW.casI μ)) v) - v ∈ ⨆ i, G.gS {h i}`. Use `Submodule.smul_mem _ ((((qlist S (GlW.casI μ)).map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod)⁻¹) hmod` as an intermediate fact. Rewrite `this` using `[smul_sub, smul_smul, inv_mul_cancel₀ hs, one_smul]`. Then use the resulting hypothesis. Establish `hkill : ∀ a b, a < b → ∀ y ∈ ⨆ i, G.gS {h i}, G.cprod (qlist S (GlW.casI μ)) (G.comp (μ + dl a b) y) = 0`.

Introduce `a b hab y hy`. Use `Submodule.iSup_induction _ (motive := fun y => G.cprod (qlist S (GlW.casI μ)) (G.comp (μ + dl a b) y) = 0) hy (fun i x hx => gen_kill G hW hS (hh i) (hhW i) (hh0 i) hμ (Dle_raise μ hab) ?_ x hx) (by simp) ?_` and prove the remaining obligations. Introduce `hle hlaμ`. Rewrite `hle` using `[hlaμ]`. Use `Dle_antisymm hle (Dle_raise μ hab)` as an intermediate fact.

Conclude with `dl_ne_zero (ne_of_lt hab) (by simpa using this)`. Introduce `x y hx hy`. Rewrite using `[map_add, map_add, hx, hy, add_zero]`. Apply `hvU` to reduce the goal to its premises. Establish `hv'hw : G.IsHW μ ((((qlist S (GlW.casI μ)).map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod)⁻¹ • G.cprod (qlist S (GlW.casI μ)) v)`.

Use `⟨?_, fun a b hab => ?_⟩` and prove the remaining obligations. Use `show G.comp μ _ = _`. Rewrite using `[map_smul, G.comp_cprod, hvw]`. Rewrite using `[map_smul, G.E_cprod]`. Establish `hw` using `G.isWt_E hvw a b`.

Use `hkill a b hab _ (hr a b hab)` as an intermediate fact. Rewrite `this` using `[hw]`. Rewrite using `[this, smul_zero]`. Establish `hin` using `hsp μ _ (W.smul_mem _ (G.cprod_mem hW _ hvW)) hv'hw`. Establish `hin' : _ ∈ ⨆ i, G.gS {h i}` using `Submodule.span_le.mpr (by`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `Submodule.mem_iSup_of_mem i (G.subset_gS _ (Set.mem_singleton _))) hin`. Establish `hfin` using `Submodule.sub_mem _ hin' hv'U`. Rewrite `hfin` using `[sub_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem span_hw {W : Submodule K V} (hW : G.Stable W) {S : Finset (Fin r → ℤ)}
    (hS : ∀ x ∈ W, ∀ μ ∉ S, G.comp μ x = 0) {ι : Type*} (h : ι → V) (la : ι → Fin r → ℤ)
    (hh : ∀ i, G.IsHW (la i) (h i)) (hhW : ∀ i, h i ∈ W) (hh0 : ∀ i, h i ≠ 0)
    (hsp : ∀ μ v, v ∈ W → G.IsHW μ v → v ∈ Submodule.span K (Set.range h)) :
    W ≤ ⨆ i, G.gS {h i} := by
  classical
  have hUs : G.Stable (⨆ i, G.gS {h i}) := iSup_stable G (fun i => G.gS_stable _)
  by_contra hn
  obtain ⟨v, hvW, hvU, μ, hvw, hr⟩ := G.exists_hwmod (G.graded_of hW) (G.raising_of hW) ⟨S, hS⟩ hn
  have hμ : DomW μ := G.dom_of_hwmod hUs hW ⟨S, hS⟩ hvW hvU hvw hr
  have hs : (((qlist S (GlW.casI μ)).map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod) ≠ 0 :=
    cprod_ne (V := V) (GlW.casI μ) _ (qlist_ne S _)
  have hmod := cprod_mod G hUs hvw hr (qlist S (GlW.casI μ))
  have hv'U : ((((qlist S (GlW.casI μ)).map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod)⁻¹ •
      G.cprod (qlist S (GlW.casI μ)) v) - v ∈ ⨆ i, G.gS {h i} := by
    have := Submodule.smul_mem _ ((((qlist S (GlW.casI μ)).map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod)⁻¹) hmod
    rwa [smul_sub, smul_smul, inv_mul_cancel₀ hs, one_smul] at this
  have hkill : ∀ a b, a < b → ∀ y ∈ ⨆ i, G.gS {h i},
      G.cprod (qlist S (GlW.casI μ)) (G.comp (μ + dl a b) y) = 0 := by
    intro a b hab y hy
    refine Submodule.iSup_induction _ (motive := fun y => G.cprod (qlist S (GlW.casI μ)) (G.comp (μ + dl a b) y) = 0) hy
      (fun i x hx => gen_kill G hW hS (hh i) (hhW i) (hh0 i) hμ (Dle_raise μ hab) ?_ x hx) (by simp) ?_
    · intro hle hlaμ
      rw [hlaμ] at hle
      have := Dle_antisymm hle (Dle_raise μ hab)
      exact dl_ne_zero (ne_of_lt hab) (by simpa using this)
    · intro x y hx hy; rw [map_add, map_add, hx, hy, add_zero]
  apply hvU
  have hv'hw : G.IsHW μ ((((qlist S (GlW.casI μ)).map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod)⁻¹ •
      G.cprod (qlist S (GlW.casI μ)) v) := by
    refine ⟨?_, fun a b hab => ?_⟩
    · show G.comp μ _ = _
      rw [map_smul, G.comp_cprod, hvw]
    · rw [map_smul, G.E_cprod]
      have hw := G.isWt_E hvw a b
      have := hkill a b hab _ (hr a b hab)
      rw [hw] at this
      rw [this, smul_zero]
  have hin := hsp μ _ (W.smul_mem _ (G.cprod_mem hW _ hvW)) hv'hw
  have hin' : _ ∈ ⨆ i, G.gS {h i} := Submodule.span_le.mpr (by
    rintro _ ⟨i, rfl⟩; exact Submodule.mem_iSup_of_mem i (G.subset_gS _ (Set.mem_singleton _))) hin
  have hfin := Submodule.sub_mem _ hin' hv'U
  rwa [sub_sub_cancel] at hfin

/- English proof (translation)
Establish `hh0 : ∀ i, h i ≠ 0` using `fun i => hli.ne_zero i`. Introduce `i`. Rewrite using `[Submodule.disjoint_def]`. Introduce `x0 hx01 hx02`. Assume the negation of the conclusion as `hx00`.

Establish `hKs : G.Stable (G.gS {h i} ⊓ ⨆ (j) (_ : j ≠ i), G.gS {h j})` using `inf_stable G (G.gS_stable _) (iSup_stable G fun j => iSup_stable G fun _ => G.gS_stable _)`. Establish `hgW : G.gS {h i} ≤ W` using `G.gS_le (by simpa using hhW i) hW`. Establish `hn' : ¬ (G.gS {h i} ⊓ ⨆ (j) (_ : j ≠ i), G.gS {h j}) ≤ ⊥` using `fun h' => hx00 ((Submodule.mem_bot K).mp (h' ⟨hx01, hx02⟩))`. Take `⟨y, hyK, hy0, ν, hyw, hyr⟩` from `G.exists_hwmod (G.graded_of hKs) (G.raising_of hKs) ⟨S, fun x hx => hS x (hgW hx.1)⟩ hn'`. Establish `hyhw : G.IsHW ν y` using `⟨hyw, fun a b hab => (Submodule.mem_bot K).mp (hyr a b hab)⟩`.

Establish `hy0' : y ≠ 0` using `fun h' => hy0 (by rw [h']; exact Submodule.zero_mem _)`. Take `⟨-, c, hyc⟩` from `G.hw_in_gS (hh i) hW ⟨S, hS⟩ (hhW i) hyK.1 hyhw hy0'`. Establish `hc0 : c ≠ 0` using `by rintro rfl; exact hy0' (by rw [hyc, zero_smul])`. Establish `hiK : h i ∈ ⨆ (j) (_ : j ≠ i), G.gS {h j}`. Use `Submodule.smul_mem _ c⁻¹ hyK.2` as an intermediate fact.

Rewrite `this` using `[hyc, smul_smul, inv_mul_cancel₀ hc0, one_smul]`. Then use the resulting hypothesis. Establish `hμ : DomW (la i)` using `G.dom_of_hwmod G.bot_stable hW ⟨S, hS⟩ (hhW i) (by rw [Submodule.mem_bot]; exact hh0 i) (hh i).1 (fun a b hab => by rw [(hh i).2 a b hab]; exact Submodule.zero_mem _)`. Establish `hs : (((qlist S (GlW.casI (la i))).map (fun c => (((GlW.casI (la i) - c : ℤ)) : K))).prod) ≠ 0` using `cprod_ne (V := V) (GlW.casI (la i)) _ (qlist_ne S _)`. Establish `hQ : ∀ x ∈ ⨆ (j) (_ : j ≠ i), G.gS {h j}, G.cprod (qlist S (GlW.casI (la i))) (G.comp (la i) x) ∈ Submodule.span K (h '' {j | j ≠ i})`. Introduce `x hx`.

Use `Submodule.iSup_induction _ (motive := fun x => G.cprod (qlist S (GlW.casI (la i))) (G.comp (la i) x) ∈ Submodule.span K (h '' {j | j ≠ i})) hx (fun j x hx => ?_) (by simp) (fun x y hx hy => by rw [map_add, map_add]; exact Submodule.add_mem _ hx hy)` and prove the remaining obligations. Use `Submodule.iSup_induction _ (motive := fun x => G.cprod (qlist S (GlW.casI (la i))) (G.comp (la i) x) ∈ Submodule.span K (h '' {j | j ≠ i})) hx (fun hj x hx => ?_) (by simp) (fun x y hx hy => by rw [map_add, map_add]; exact Submodule.add_mem _ hx hy)` and prove the remaining obligations. Distinguish the cases in `hlj : la j = la i`. Take `⟨c', hc'⟩` from `G.comp_top_of_mem (hh j) hx`. Establish `e : G.comp (la i) x = c' • h j` using `by rw [← hlj]; exact hc'`.

Rewrite using `[e, map_smul, cprod_eig G (cas_hw G (hh j)) _, smul_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)`. Rewrite using `[gen_kill G hW hS (hh j) (hhW j) (hh0 j) hμ (Dle_refl _) (fun _ => hlj) x hx]`. Conclude with `Submodule.zero_mem _`. Establish `h1` using `hQ _ hiK`.

Rewrite `h1` using `[(hh i).1, cprod_eig G (cas_hw G (hh i)) _]`. Establish `h2` using `Submodule.smul_mem _ ((((qlist S (GlW.casI (la i))).map (fun c => (((GlW.casI (la i) - c : ℤ)) : K))).prod)⁻¹) h1`. Rewrite `h2` using `[smul_smul, inv_mul_cancel₀ hs, one_smul]`. Conclude with `hli.notMem_span_image (s := {j | j ≠ i}) (x := i) (by simp) h2`.
-/
theorem indep_hw {W : Submodule K V} (hW : G.Stable W) {S : Finset (Fin r → ℤ)}
    (hS : ∀ x ∈ W, ∀ μ ∉ S, G.comp μ x = 0) {ι : Type*} (h : ι → V) (la : ι → Fin r → ℤ)
    (hh : ∀ i, G.IsHW (la i) (h i)) (hhW : ∀ i, h i ∈ W) (hli : LinearIndependent K h) :
    iSupIndep (fun i => G.gS {h i}) := by
  classical
  have hh0 : ∀ i, h i ≠ 0 := fun i => hli.ne_zero i
  intro i
  rw [Submodule.disjoint_def]
  intro x0 hx01 hx02
  by_contra hx00
  have hKs : G.Stable (G.gS {h i} ⊓ ⨆ (j) (_ : j ≠ i), G.gS {h j}) :=
    inf_stable G (G.gS_stable _) (iSup_stable G fun j => iSup_stable G fun _ => G.gS_stable _)
  have hgW : G.gS {h i} ≤ W := G.gS_le (by simpa using hhW i) hW
  have hn' : ¬ (G.gS {h i} ⊓ ⨆ (j) (_ : j ≠ i), G.gS {h j}) ≤ ⊥ := fun h' =>
    hx00 ((Submodule.mem_bot K).mp (h' ⟨hx01, hx02⟩))
  obtain ⟨y, hyK, hy0, ν, hyw, hyr⟩ := G.exists_hwmod (G.graded_of hKs) (G.raising_of hKs)
    ⟨S, fun x hx => hS x (hgW hx.1)⟩ hn'
  have hyhw : G.IsHW ν y := ⟨hyw, fun a b hab => (Submodule.mem_bot K).mp (hyr a b hab)⟩
  have hy0' : y ≠ 0 := fun h' => hy0 (by rw [h']; exact Submodule.zero_mem _)
  obtain ⟨-, c, hyc⟩ := G.hw_in_gS (hh i) hW ⟨S, hS⟩ (hhW i) hyK.1 hyhw hy0'
  have hc0 : c ≠ 0 := by rintro rfl; exact hy0' (by rw [hyc, zero_smul])
  have hiK : h i ∈ ⨆ (j) (_ : j ≠ i), G.gS {h j} := by
    have := Submodule.smul_mem _ c⁻¹ hyK.2
    rwa [hyc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
  have hμ : DomW (la i) := G.dom_of_hwmod G.bot_stable hW ⟨S, hS⟩ (hhW i) (by rw [Submodule.mem_bot]; exact hh0 i)
    (hh i).1 (fun a b hab => by rw [(hh i).2 a b hab]; exact Submodule.zero_mem _)
  have hs : (((qlist S (GlW.casI (la i))).map (fun c => (((GlW.casI (la i) - c : ℤ)) : K))).prod) ≠ 0 :=
    cprod_ne (V := V) (GlW.casI (la i)) _ (qlist_ne S _)
  have hQ : ∀ x ∈ ⨆ (j) (_ : j ≠ i), G.gS {h j},
      G.cprod (qlist S (GlW.casI (la i))) (G.comp (la i) x) ∈ Submodule.span K (h '' {j | j ≠ i}) := by
    intro x hx
    refine Submodule.iSup_induction _ (motive := fun x =>
      G.cprod (qlist S (GlW.casI (la i))) (G.comp (la i) x) ∈ Submodule.span K (h '' {j | j ≠ i})) hx
      (fun j x hx => ?_) (by simp) (fun x y hx hy => by rw [map_add, map_add]; exact Submodule.add_mem _ hx hy)
    refine Submodule.iSup_induction _ (motive := fun x =>
      G.cprod (qlist S (GlW.casI (la i))) (G.comp (la i) x) ∈ Submodule.span K (h '' {j | j ≠ i})) hx
      (fun hj x hx => ?_) (by simp) (fun x y hx hy => by rw [map_add, map_add]; exact Submodule.add_mem _ hx hy)
    by_cases hlj : la j = la i
    · obtain ⟨c', hc'⟩ := G.comp_top_of_mem (hh j) hx
      have e : G.comp (la i) x = c' • h j := by rw [← hlj]; exact hc'
      rw [e, map_smul, cprod_eig G (cas_hw G (hh j)) _, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · rw [gen_kill G hW hS (hh j) (hhW j) (hh0 j) hμ (Dle_refl _) (fun _ => hlj) x hx]
      exact Submodule.zero_mem _
  have h1 := hQ _ hiK
  rw [(hh i).1, cprod_eig G (cas_hw G (hh i)) _] at h1
  have h2 := Submodule.smul_mem _ ((((qlist S (GlW.casI (la i))).map (fun c => (((GlW.casI (la i) - c : ℤ)) : K))).prod)⁻¹) h1
  rw [smul_smul, inv_mul_cancel₀ hs, one_smul] at h2
  exact hli.notMem_span_image (s := {j | j ≠ i}) (x := i) (by simp) h2

end GlX

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM.DimensionMonotonicity Finset

namespace GlX

variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

def act : List (Fin r × Fin r) → V →ₗ[K] V
  | [] => LinearMap.id
  | ab :: w => G.E ab.1 ab.2 ∘ₗ act w

noncomputable def Lv (v : V) : (List (Fin r × Fin r) →₀ K) →ₗ[K] V :=
  Finsupp.linearCombination K (fun w => act G w v)

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => simpa [act] using hx`. Consider the case `cons ab w ih`. Simplify using `only [act, LinearMap.comp_apply]`. Conclude with `hU _ _ _ ih`.
-/
theorem act_mem {U : Submodule K V} (hU : G.Stable U) (w : List (Fin r × Fin r)) {x : V} (hx : x ∈ U) :
    act G w x ∈ U := by
  induction w with
  | nil => simpa [act] using hx
  | cons ab w ih =>
    simp only [act, LinearMap.comp_apply]
    exact hU _ _ _ ih

/- English proof (translation)
Unfold `Lv`. Rewrite using `[Finsupp.linearCombination_mapDomain]`. Simplify using `only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, Function.comp_apply, act, LinearMap.comp_apply]`.
-/
theorem E_Lv (v : V) (a b : Fin r) (c : List (Fin r × Fin r) →₀ K) :
    G.E a b (Lv G v c) = Lv G v (Finsupp.mapDomain (List.cons (a, b)) c) := by
  unfold Lv
  rw [Finsupp.linearCombination_mapDomain]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    Function.comp_apply, act, LinearMap.comp_apply]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`. Take `⟨c, rfl⟩` from `LinearMap.mem_range.mp hy`. Unfold `Formalism.GM.DimensionMonotonicity.GlW.gS`. Rewrite using `[Submodule.mem_sInf]`.

Introduce and unpack `U ⟨hvU, hU⟩`. Unfold `Lv`. Rewrite using `[Finsupp.linearCombination_apply]`. Rewrite using `[Finsupp.sum]`. Conclude with `sum_mem fun w _ => U.smul_mem _ (act_mem G hU w (hvU (Set.mem_singleton v)))`.

Establish `h1 : ({v} : Set V) ⊆ LinearMap.range (Lv G v)`. Introduce `x hx`. Rewrite `hx` using `[Set.mem_singleton_iff]`. Rewrite using `[hx]`. Conclude with `LinearMap.mem_range.mpr ⟨Finsupp.single [] 1, by simp [Lv, act]⟩`.

Establish `h2 : G.Stable (LinearMap.range (Lv G v))`. Unfold `Formalism.GM.DimensionMonotonicity.GlW.Stable`. Introduce `a b y hy`. Take `⟨c, rfl⟩` from `LinearMap.mem_range.mp hy`. Conclude with `LinearMap.mem_range.mpr ⟨_, (E_Lv G v a b c).symm⟩`.

Unfold `Formalism.GM.DimensionMonotonicity.GlW.gS`. Conclude with `sInf_le (And.intro h1 h2)`.
-/
theorem range_Lv (v : V) : LinearMap.range (Lv G v) = G.gS {v} := by
  apply le_antisymm
  · intro y hy
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hy
    unfold Formalism.GM.DimensionMonotonicity.GlW.gS
    rw [Submodule.mem_sInf]
    rintro U ⟨hvU, hU⟩
    unfold Lv
    rw [Finsupp.linearCombination_apply]
    rw [Finsupp.sum]
    exact sum_mem fun w _ => U.smul_mem _ (act_mem G hU w (hvU (Set.mem_singleton v)))
  · have h1 : ({v} : Set V) ⊆ LinearMap.range (Lv G v) := by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact LinearMap.mem_range.mpr ⟨Finsupp.single [] 1, by simp [Lv, act]⟩
    have h2 : G.Stable (LinearMap.range (Lv G v)) := by
      unfold Formalism.GM.DimensionMonotonicity.GlW.Stable
      intro a b y hy
      obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hy
      exact LinearMap.mem_range.mpr ⟨_, (E_Lv G v a b c).symm⟩
    unfold Formalism.GM.DimensionMonotonicity.GlW.gS
    exact sInf_le (And.intro h1 h2)

/- English proof (translation)
Simplify using `[Lv, Finsupp.linearCombination_apply, map_add, smul_add, Finsupp.sum_add]`.
-/
theorem Lv_add (v v' : V) (c : List (Fin r × Fin r) →₀ K) : Lv G (v + v') c = Lv G v c + Lv G v' c := by
  simp [Lv, Finsupp.linearCombination_apply, map_add, smul_add, Finsupp.sum_add]

/- English proof (translation)
Simplify using `only [Lv, Finsupp.linearCombination_apply, Finsupp.sum, map_smul, Finset.smul_sum, smul_comm t]`.
-/
theorem Lv_smul (t : K) (v : V) (c : List (Fin r × Fin r) →₀ K) : Lv G (t • v) c = t • Lv G v c := by
  simp only [Lv, Finsupp.linearCombination_apply, Finsupp.sum, map_smul, Finset.smul_sum, smul_comm t]

/- English proof (translation)
Introduce `c hc`. Rewrite `hc`, the goal using `[LinearMap.mem_ker]`. Assume the negation of the conclusion as `hx`. Establish `hs : G.IsHW la (h + h')` using `⟨by show G.comp la (h + h') = h + h'; rw [map_add, hh.1, hh'.1], fun a b hab => by rw [map_add, hh.2 a b hab, hh'.2 a b hab, add_zero]⟩`. Establish `hxs : Lv G h' c ∈ G.gS {h + h'}` using `by rw [← range_Lv]; exact ⟨c, by rw [Lv_add, hc, zero_add]⟩`.

Establish `hxh : Lv G h' c ∈ G.gS {h'}` using `by rw [← range_Lv]; exact ⟨c, rfl⟩`. Establish `hKs : G.Stable (G.gS {h + h'} ⊓ G.gS {h'})` using `inf_stable G (G.gS_stable _) (G.gS_stable _)`. Establish `hgW : G.gS {h'} ≤ W` using `G.gS_le (by simpa using hh'W) hW`. Take `⟨S, hS⟩` from `hWf`. Establish `hn : ¬ (G.gS {h + h'} ⊓ G.gS {h'}) ≤ ⊥` using `fun hle => hx ((Submodule.mem_bot K).mp (hle ⟨hxs, hxh⟩))`.

Take `⟨y, hyK, hy0, ν, hyw, hyr⟩` from `G.exists_hwmod (G.graded_of hKs) (G.raising_of hKs) ⟨S, fun z hz => hS z (hgW hz.2)⟩ hn`. Establish `hyhw : G.IsHW ν y` using `⟨hyw, fun a b hab => (Submodule.mem_bot K).mp (hyr a b hab)⟩`. Establish `hy0' : y ≠ 0` using `fun e => hy0 (by rw [e]; exact Submodule.zero_mem _)`. Take `⟨-, c1, hc1⟩` from `G.hw_in_gS hh' hW ⟨S, hS⟩ hh'W hyK.2 hyhw hy0'`. Take `⟨-, c2, hc2⟩` from `G.hw_in_gS hs hW ⟨S, hS⟩ (W.add_mem hhW hh'W) hyK.1 hyhw hy0'`.

Distinguish the cases in `hc2z : c2 = 0`. Rewrite `hc2` using `[hc2z, zero_smul]`. Conclude with `hy0' hc2`. Establish `e0 : c2 • h = (c1 - c2) • h'` using `by rw [sub_smul, ← hc1, hc2, smul_add, add_sub_cancel_right]`. Establish `e : h = (c2⁻¹ * (c1 - c2)) • h'`.

Rewrite using `[mul_smul, ← e0, smul_smul, inv_mul_cancel₀ hc2z, one_smul]`. Establish `e2 : Lv G h c = (c2⁻¹ * (c1 - c2)) • Lv G h' c` using `by conv_lhs => rw [e]`. Rewrite using `[Lv_smul]`. Rewrite `e2` using `[hc]`. Establish `ht : c2⁻¹ * (c1 - c2) = 0`.

Break down `smul_eq_zero.mp e2.symm with h1 | h1` into its components or cases. Conclude with `h1`. Conclude with `absurd h1 hx`. Rewrite `e` using `[ht, zero_smul]`. Conclude with `h0 e`.
-/
theorem ker_le {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {la : Fin r → ℤ} {h h' : V}
    (hh : G.IsHW la h) (hh' : G.IsHW la h') (hhW : h ∈ W) (hh'W : h' ∈ W) (h0 : h ≠ 0) :
    LinearMap.ker (Lv G h) ≤ LinearMap.ker (Lv G h') := by
  intro c hc
  rw [LinearMap.mem_ker] at hc ⊢
  by_contra hx
  have hs : G.IsHW la (h + h') := ⟨by show G.comp la (h + h') = h + h'; rw [map_add, hh.1, hh'.1],
    fun a b hab => by rw [map_add, hh.2 a b hab, hh'.2 a b hab, add_zero]⟩
  have hxs : Lv G h' c ∈ G.gS {h + h'} := by rw [← range_Lv]; exact ⟨c, by rw [Lv_add, hc, zero_add]⟩
  have hxh : Lv G h' c ∈ G.gS {h'} := by rw [← range_Lv]; exact ⟨c, rfl⟩
  have hKs : G.Stable (G.gS {h + h'} ⊓ G.gS {h'}) := inf_stable G (G.gS_stable _) (G.gS_stable _)
  have hgW : G.gS {h'} ≤ W := G.gS_le (by simpa using hh'W) hW
  obtain ⟨S, hS⟩ := hWf
  have hn : ¬ (G.gS {h + h'} ⊓ G.gS {h'}) ≤ ⊥ := fun hle => hx ((Submodule.mem_bot K).mp (hle ⟨hxs, hxh⟩))
  obtain ⟨y, hyK, hy0, ν, hyw, hyr⟩ := G.exists_hwmod (G.graded_of hKs) (G.raising_of hKs)
    ⟨S, fun z hz => hS z (hgW hz.2)⟩ hn
  have hyhw : G.IsHW ν y := ⟨hyw, fun a b hab => (Submodule.mem_bot K).mp (hyr a b hab)⟩
  have hy0' : y ≠ 0 := fun e => hy0 (by rw [e]; exact Submodule.zero_mem _)
  obtain ⟨-, c1, hc1⟩ := G.hw_in_gS hh' hW ⟨S, hS⟩ hh'W hyK.2 hyhw hy0'
  obtain ⟨-, c2, hc2⟩ := G.hw_in_gS hs hW ⟨S, hS⟩ (W.add_mem hhW hh'W) hyK.1 hyhw hy0'
  by_cases hc2z : c2 = 0
  · rw [hc2z, zero_smul] at hc2; exact hy0' hc2
  · have e0 : c2 • h = (c1 - c2) • h' := by rw [sub_smul, ← hc1, hc2, smul_add, add_sub_cancel_right]
    have e : h = (c2⁻¹ * (c1 - c2)) • h' := by
      rw [mul_smul, ← e0, smul_smul, inv_mul_cancel₀ hc2z, one_smul]
    have e2 : Lv G h c = (c2⁻¹ * (c1 - c2)) • Lv G h' c := by
      conv_lhs => rw [e]
      rw [Lv_smul]
    rw [hc] at e2
    have ht : c2⁻¹ * (c1 - c2) = 0 := by
      rcases smul_eq_zero.mp e2.symm with h1 | h1
      · exact h1
      · exact absurd h1 hx
    rw [ht, zero_smul] at e
    exact h0 e

noncomputable def tr {h h' : V} (hk : LinearMap.ker (Lv G h) ≤ LinearMap.ker (Lv G h')) :
    LinearMap.range (Lv G h) →ₗ[K] V :=
  (LinearMap.ker (Lv G h)).liftQ (Lv G h') hk ∘ₗ (Lv G h).quotKerEquivRange.symm.toLinearMap

/- English proof (translation)
Simplify using `only [tr, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]`.
-/
theorem tr_apply {h h' : V} (hk : LinearMap.ker (Lv G h) ≤ LinearMap.ker (Lv G h'))
    (c : List (Fin r × Fin r) →₀ K) : tr G hk ⟨Lv G h c, LinearMap.mem_range_self _ c⟩ = Lv G h' c := by
  simp only [tr, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image,
    Submodule.mkQ_apply, Submodule.liftQ_apply]

end GlX

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM.DimensionMonotonicity Finset

namespace GlX

variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

/- English proof (translation)
Take `⟨y, hy⟩` from `y`. Take `⟨c, rfl⟩` from `LinearMap.mem_range.mp hy`. Rewrite using `[show tr G hk ⟨Lv G h c, hy⟩ = Lv G h' c from tr_apply G hk c]`. Conclude with `LinearMap.mem_range_self _ _`.
-/
theorem tr_mem {h h' : V} (hk : LinearMap.ker (Lv G h) ≤ LinearMap.ker (Lv G h')) (y : LinearMap.range (Lv G h)) :
    tr G hk y ∈ LinearMap.range (Lv G h') := by
  obtain ⟨y, hy⟩ := y
  obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hy
  rw [show tr G hk ⟨Lv G h c, hy⟩ = Lv G h' c from tr_apply G hk c]
  exact LinearMap.mem_range_self _ _

/- English proof (translation)
Unfold `Formalism.GM.DimensionMonotonicity.GlW.IsWt`. Take `⟨S, hS⟩` from `G.dec z`. Establish `hkill : ∀ ν, ν ≠ μ → G.comp ν z = 0`. Introduce `ν hne`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c, ν c ≠ μ c := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hne (funext h)`. Establish `h1` using `G.shift c c ν z`. Establish `hdl : Formalism.GM.DimensionMonotonicity.dl c c = (0 : Fin r → ℤ)` using `by simp [Formalism.GM.DimensionMonotonicity.dl]`.

Rewrite `h1` using `[hdl, sub_zero, G.diag c ν z, hz c, map_smul]`. Establish `h2 : (((ν c : ℤ) : K) - ((μ c : ℤ) : K)) • G.comp ν z = 0`. Rewrite using `[sub_smul, h1, sub_self]`. Establish `h3 : (((ν c : ℤ) : K) - ((μ c : ℤ) : K)) ≠ 0`. Rewrite using `[sub_ne_zero]`.

Conclude with `hc` after adjusting the coercions. Conclude with `(smul_eq_zero.mp h2).resolve_left h3`. Establish `hsum` using `G.sum_comp z S hS`. Rewrite `hsum` using `[Finset.sum_eq_single μ (fun ν _ hne => hkill ν hne) (fun hμ => hS μ hμ)]`. Conclude with `hsum`.
-/
theorem isWt_of_eig {μ : Fin r → ℤ} {z : V} (hz : ∀ c, G.E c c z = ((μ c : ℤ) : K) • z) : G.IsWt μ z := by
  unfold Formalism.GM.DimensionMonotonicity.GlW.IsWt
  obtain ⟨S, hS⟩ := G.dec z
  have hkill : ∀ ν, ν ≠ μ → G.comp ν z = 0 := by
    intro ν hne
    obtain ⟨c, hc⟩ : ∃ c, ν c ≠ μ c := by
      by_contra h
      push_neg at h
      exact hne (funext h)
    have h1 := G.shift c c ν z
    have hdl : Formalism.GM.DimensionMonotonicity.dl c c = (0 : Fin r → ℤ) := by simp [Formalism.GM.DimensionMonotonicity.dl]
    rw [hdl, sub_zero, G.diag c ν z, hz c, map_smul] at h1
    have h2 : (((ν c : ℤ) : K) - ((μ c : ℤ) : K)) • G.comp ν z = 0 := by
      rw [sub_smul, h1, sub_self]
    have h3 : (((ν c : ℤ) : K) - ((μ c : ℤ) : K)) ≠ 0 := by
      rw [sub_ne_zero]
      exact_mod_cast hc
    exact (smul_eq_zero.mp h2).resolve_left h3
  have hsum := G.sum_comp z S hS
  rw [Finset.sum_eq_single μ (fun ν _ hne => hkill ν hne) (fun hμ => hS μ hμ)] at hsum
  exact hsum

end GlX

section Proj

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Take `⟨D, hD⟩` from `Submodule.exists_isCompl W`. Establish `hc : ∀ i, IsCompl (R i) ((⨆ (j) (_ : j ≠ i), R j) ⊔ D)`. Introduce `i`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Submodule.disjoint_def]`.

Introduce `x hx hx2`. Take `⟨y, hy, d, hd, rfl⟩` from `Submodule.mem_sup.mp hx2`. Establish `hyW : y ∈ W` using `(iSup_le fun j => iSup_le fun _ => hRW j) hy`. Establish `hdW : d ∈ W`. Use `W.sub_mem (hRW i hx) hyW` as an intermediate fact.

Rewrite `this` using `[add_sub_cancel_left]`. Then use the resulting hypothesis. Establish `hd0 : d = 0` using `(Submodule.disjoint_def.mp hD.disjoint) d hdW hd`. Substitute `hd0` using the available equality. Rewrite `hx`, the goal using `[add_zero]`. Conclude with `(Submodule.disjoint_def.mp (hind i)) y hx hy`.

Rewrite using `[codisjoint_iff, eq_top_iff]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨fun i => (R i).subtype ∘ₗ (R i).projectionOnto _ (hc i), fun i x => by simp, fun i x hx => ?_, fun i j hji x hx => ?_⟩` and prove the remaining obligations. Use `Submodule.projectionOnto_apply_left (hc i) ⟨x, hx⟩` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply]`.

Rewrite using `[this]`. Establish `hxq : x ∈ (⨆ (j) (_ : j ≠ i), R j) ⊔ D` using `Submodule.mem_sup_left (Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hji hx))`. Use `Submodule.projectionOnto_apply_right (hc i) ⟨x, hxq⟩` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply]`. Rewrite using `[this]`.

Both sides reduce to the same expression.
-/
theorem proj_exists {W : Submodule K V} {ι : Type*} [DecidableEq ι] (R : ι → Submodule K V)
    (hind : iSupIndep R) (hRW : ∀ i, R i ≤ W) (hWR : W ≤ ⨆ i, R i) :
    ∃ π : ι → V →ₗ[K] V, (∀ i x, π i x ∈ R i) ∧ (∀ i, ∀ x ∈ R i, π i x = x) ∧
      (∀ i j, j ≠ i → ∀ x ∈ R j, π i x = 0) := by
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl W
  have hc : ∀ i, IsCompl (R i) ((⨆ (j) (_ : j ≠ i), R j) ⊔ D) := by
    intro i
    constructor
    · rw [Submodule.disjoint_def]
      intro x hx hx2
      obtain ⟨y, hy, d, hd, rfl⟩ := Submodule.mem_sup.mp hx2
      have hyW : y ∈ W := (iSup_le fun j => iSup_le fun _ => hRW j) hy
      have hdW : d ∈ W := by
        have := W.sub_mem (hRW i hx) hyW
        rwa [add_sub_cancel_left] at this
      have hd0 : d = 0 := (Submodule.disjoint_def.mp hD.disjoint) d hdW hd
      subst hd0
      rw [add_zero] at hx ⊢
      exact (Submodule.disjoint_def.mp (hind i)) y hx hy
    · rw [codisjoint_iff, eq_top_iff]
      calc ⊤ = W ⊔ D := hD.codisjoint.eq_top.symm
        _ ≤ (⨆ j, R j) ⊔ D := sup_le_sup_right hWR D
        _ = R i ⊔ ((⨆ (j) (_ : j ≠ i), R j) ⊔ D) := by rw [iSup_split_single R i, sup_assoc]
  refine ⟨fun i => (R i).subtype ∘ₗ (R i).projectionOnto _ (hc i), fun i x => by simp,
    fun i x hx => ?_, fun i j hji x hx => ?_⟩
  · have := Submodule.projectionOnto_apply_left (hc i) ⟨x, hx⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    rw [this]
  · have hxq : x ∈ (⨆ (j) (_ : j ≠ i), R j) ⊔ D :=
      Submodule.mem_sup_left (Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hji hx))
    have := Submodule.projectionOnto_apply_right (hc i) ⟨x, hxq⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    rw [this]; rfl

/- English proof (translation)
Introduce `i x hx`. Use `Submodule.iSup_induction R (motive := fun x => π i (A x) = A (π i x)) (hWR hx) ?_ ?_ ?_` and prove the remaining obligations. Introduce `j y hy`. Distinguish the cases in `hij : j = i`. Rewrite `hy` using `[hij]`.

Rewrite using `[h2 i _ (hA i y hy), h2 i y hy]`. Rewrite using `[h3 i j hij _ (hA j y hy), h3 i j hij y hy, map_zero]`. Simplify using the standard rewrite rules. Introduce `y z hy hz`. Simplify using `only [map_add, hy, hz]`.
-/
theorem proj_comm {W : Submodule K V} {ι : Type*} (R : ι → Submodule K V) (hWR : W ≤ ⨆ i, R i)
    (π : ι → V →ₗ[K] V) (h2 : ∀ i, ∀ x ∈ R i, π i x = x) (h3 : ∀ i j, j ≠ i → ∀ x ∈ R j, π i x = 0)
    (A : V →ₗ[K] V) (hA : ∀ j, ∀ x ∈ R j, A x ∈ R j) : ∀ i, ∀ x ∈ W, π i (A x) = A (π i x) := by
  intro i x hx
  refine Submodule.iSup_induction R (motive := fun x => π i (A x) = A (π i x)) (hWR hx) ?_ ?_ ?_
  · intro j y hy
    by_cases hij : j = i
    · rw [hij] at hy
      rw [h2 i _ (hA i y hy), h2 i y hy]
    · rw [h3 i j hij _ (hA j y hy), h3 i j hij y hy, map_zero]
  · simp
  · intro y z hy hz
    simp only [map_add, hy, hz]

end Proj

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open MvPolynomial Finset

section Ext

variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]

def frst (m : σ →₀ ℕ) : σ →₀ ℕ := m.filter fs

def ltr (m : σ →₀ ℕ) : σ →₀ ℕ := m.filter (fun v => ¬ fs v)

def IsF (g : MvPolynomial σ K) : Prop := ∀ m ∈ g.support, ∀ v, m v ≠ 0 → fs v

def IsL (q : MvPolynomial σ K) : Prop := ∀ m ∈ q.support, ∀ v, m v ≠ 0 → ¬ fs v

/- English proof (translation)
The claim follows from `Finsupp.filter_pos_add_filter_neg m fs`.
-/
theorem frst_add_ltr (m : σ →₀ ℕ) : frst fs m + ltr fs m = m := Finsupp.filter_pos_add_filter_neg m fs

/- English proof (translation)
Use extensionality with `v`. Unfold `frst`. Rewrite using `[Finsupp.filter_apply]`. Use `split_ifs with hv`. Both sides reduce to the same expression.

Assume the negation of the conclusion as `hne`. Conclude with `hv (h v (Ne.symm hne))`.
-/
theorem frst_of {m : σ →₀ ℕ} (h : ∀ v, m v ≠ 0 → fs v) : frst fs m = m := by
  ext v
  unfold frst
  rw [Finsupp.filter_apply]
  split_ifs with hv
  · rfl
  · by_contra hne
    exact hv (h v (Ne.symm hne))
/- English proof (translation)
Use extensionality with `v`. Unfold `ltr`. Rewrite using `[Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]`. Distinguish the cases in `hv : fs v`. Simplify using `[hv]`.

Establish `: m v = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hv (h v hne)`. Simplify using `[hv, this]`.
-/
theorem ltr_of {m : σ →₀ ℕ} (h : ∀ v, m v ≠ 0 → fs v) : ltr fs m = 0 := by
  ext v
  unfold ltr
  rw [Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
  by_cases hv : fs v
  · simp [hv]
  · have : m v = 0 := by
      by_contra hne
      exact hv (h v hne)
    simp [hv, this]
/- English proof (translation)
Use extensionality with `v`. Unfold `frst`. Rewrite using `[Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]`. Use `split_ifs with hv`. Assume the negation of the conclusion as `hne`.

Conclude with `h v hne hv`. Both sides reduce to the same expression.
-/
theorem frst_of' {m : σ →₀ ℕ} (h : ∀ v, m v ≠ 0 → ¬ fs v) : frst fs m = 0 := by
  ext v
  unfold frst
  rw [Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
  split_ifs with hv
  · by_contra hne
    exact h v hne hv
  · rfl
/- English proof (translation)
Use extensionality with `v`. Unfold `ltr`. Rewrite using `[Finsupp.filter_apply]`. Distinguish the cases in `hv : fs v`. Establish `: m v = 0`.

Assume the negation of the conclusion as `hne`. Conclude with `h v hne hv`. Simplify using `[hv, this]`. Simplify using `[hv]`.
-/
theorem ltr_of' {m : σ →₀ ℕ} (h : ∀ v, m v ≠ 0 → ¬ fs v) : ltr fs m = m := by
  ext v
  unfold ltr
  rw [Finsupp.filter_apply]
  by_cases hv : fs v
  · have : m v = 0 := by
      by_contra hne
      exact h v hne hv
    simp [hv, this]
  · simp [hv]
/- English proof (translation)
Unfold `frst`. Conclude with `Finsupp.filter_add`.
-/
theorem frst_add (m m' : σ →₀ ℕ) : frst fs (m + m') = frst fs m + frst fs m' := by
  unfold frst
  exact Finsupp.filter_add
/- English proof (translation)
Unfold `ltr`. Conclude with `Finsupp.filter_add`.
-/
theorem ltr_add (m m' : σ →₀ ℕ) : ltr fs (m + m') = ltr fs m + ltr fs m' := by
  unfold ltr
  exact Finsupp.filter_add
/- English proof (translation)
Introduce `v hv`. Unfold `frst at hv`. Rewrite `hv` using `[Finsupp.filter_apply]`. Assume the negation of the conclusion as `h`. Conclude with `hv (if_neg h)`.
-/
theorem frst_isF (m : σ →₀ ℕ) : ∀ v, frst fs m v ≠ 0 → fs v := by
  intro v hv
  unfold frst at hv
  rw [Finsupp.filter_apply] at hv
  by_contra h
  exact hv (if_neg h)
/- English proof (translation)
Introduce `v hv h`. Unfold `ltr at hv`. Simplify using `[Finsupp.filter_apply, h] at hv`.
-/
theorem ltr_isL (m : σ →₀ ℕ) : ∀ v, ltr fs m v ≠ 0 → ¬ fs v := by
  intro v hv h
  unfold ltr at hv
  simp [Finsupp.filter_apply, h] at hv

noncomputable def ext (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) : MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  (basisMonomials σ K).constr K (fun m => φ (monomial (frst fs m) 1) * monomial (ltr fs m) 1)

noncomputable def slc (m : σ →₀ ℕ) : MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  (basisMonomials σ K).constr K (fun m' => if ltr fs m' = m then monomial (frst fs m') 1 else 0)

/- English proof (translation)
Simplify using `only [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]`.
-/
theorem monomial_eq_basis (m : σ →₀ ℕ) (a : K) : monomial m a = a • (basisMonomials σ K) m := by
  simp only [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]

/- English proof (translation)
Rewrite using `[monomial_eq_basis m a, map_smul]`. Simplify using `only [ext, Module.Basis.constr_basis]`.
-/
theorem ext_monomial (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) (m : σ →₀ ℕ) (a : K) :
    ext fs φ (monomial m a) = a • (φ (monomial (frst fs m) 1) * monomial (ltr fs m) 1) := by
  rw [monomial_eq_basis m a, map_smul]
  simp only [ext, Module.Basis.constr_basis]

/- English proof (translation)
Rewrite using `[monomial_eq_basis m' a, map_smul]`. Simplify using `only [slc, Module.Basis.constr_basis]`. Apply the tactic sequence `split_ifs <;> simp [smul_monomial]`.
-/
theorem sl_monomial (m m' : σ →₀ ℕ) (a : K) :
    slc fs m (monomial m' a) = if ltr fs m' = m then monomial (frst fs m') a else 0 := by
  rw [monomial_eq_basis m' a, map_smul]
  simp only [slc, Module.Basis.constr_basis]
  split_ifs <;> simp [smul_monomial]

/- English proof (translation)
Use `(basisMonomials σ K).ext fun m => ?_` and prove the remaining obligations. Simplify using `only [coe_basisMonomials, ext_monomial, LinearMap.add_apply, add_mul, one_smul]`.
-/
theorem ext_add (φ ψ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) : ext fs (φ + ψ) = ext fs φ + ext fs ψ := by
  refine (basisMonomials σ K).ext fun m => ?_
  simp only [coe_basisMonomials, ext_monomial, LinearMap.add_apply, add_mul, one_smul]

/- English proof (translation)
Use `(basisMonomials σ K).ext fun m => ?_` and prove the remaining obligations. Simplify using `only [coe_basisMonomials, ext_monomial, LinearMap.sum_apply, Finset.sum_mul, one_smul]`.
-/
theorem ext_sum {ι : Type*} (s : Finset ι) (φ : ι → MvPolynomial σ K →ₗ[K] MvPolynomial σ K) :
    ext fs (∑ i ∈ s, φ i) = ∑ i ∈ s, ext fs (φ i) := by
  refine (basisMonomials σ K).ext fun m => ?_
  simp only [coe_basisMonomials, ext_monomial, LinearMap.sum_apply, Finset.sum_mul, one_smul]

/- English proof (translation)
Rewrite using `[g.as_sum, q.as_sum, Finset.sum_mul_sum, map_sum, map_sum, Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun b hb => ?_` and prove the remaining obligations. Rewrite using `[monomial_mul, ext_monomial, frst_add, ltr_add, frst_of fs (hg a ha), ltr_of fs (hg a ha), frst_of' fs (hq b hb), ltr_of' fs (hq b hb), add_zero, zero_add]`.

Establish `h1 : (monomial a (coeff a g) : MvPolynomial σ K) = coeff a g • monomial a 1`. Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`. Establish `h2 : (monomial b (coeff b q) : MvPolynomial σ K) = coeff b q • monomial b 1`. Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[h1, h2, map_smul, smul_mul_assoc, mul_smul_comm, smul_smul]`.
-/
theorem ext_mul (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) {g q : MvPolynomial σ K} (hg : IsF fs g)
    (hq : IsL fs q) : ext fs φ (g * q) = φ g * q := by
  classical
  rw [g.as_sum, q.as_sum, Finset.sum_mul_sum, map_sum, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [monomial_mul, ext_monomial, frst_add, ltr_add, frst_of fs (hg a ha), ltr_of fs (hg a ha),
    frst_of' fs (hq b hb), ltr_of' fs (hq b hb), add_zero, zero_add]
  have h1 : (monomial a (coeff a g) : MvPolynomial σ K) = coeff a g • monomial a 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  have h2 : (monomial b (coeff b q) : MvPolynomial σ K) = coeff b q • monomial b 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [h1, h2, map_smul, smul_mul_assoc, mul_smul_comm, smul_smul]

/- English proof (translation)
Use `conv_lhs => rw [g.as_sum, q.as_sum, Finset.sum_mul_sum, map_sum]`. Use `conv_rhs => rw [g.as_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Establish `key : ∀ b ∈ q.support, slc fs m (monomial a (coeff a g) * monomial b (coeff b q)) = if b = m then monomial a (coeff a g * coeff m q) else 0`.

Introduce `b hb`. Rewrite using `[monomial_mul, sl_monomial, frst_add, ltr_add, frst_of fs (hg a ha), ltr_of fs (hg a ha), frst_of' fs (hq b hb), ltr_of' fs (hq b hb), add_zero, zero_add]`. Use `split_ifs with h`. Rewrite using `[h]`. Both sides reduce to the same expression.

Rewrite using `[Finset.sum_congr rfl key, Finset.sum_ite_eq']`. Use `split_ifs with hm`. Rewrite using `[smul_monomial, smul_eq_mul, mul_comm (coeff a g)]`. Simplify using `only [mem_support_iff, not_not] at hm`. Rewrite using `[hm, zero_smul]`.
-/
theorem sl_mul (m : σ →₀ ℕ) {g q : MvPolynomial σ K} (hg : IsF fs g) (hq : IsL fs q) :
    slc fs m (g * q) = coeff m q • g := by
  classical
  conv_lhs => rw [g.as_sum, q.as_sum, Finset.sum_mul_sum, map_sum]
  conv_rhs => rw [g.as_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [map_sum]
  have key : ∀ b ∈ q.support, slc fs m (monomial a (coeff a g) * monomial b (coeff b q)) =
      if b = m then monomial a (coeff a g * coeff m q) else 0 := by
    intro b hb
    rw [monomial_mul, sl_monomial, frst_add, ltr_add, frst_of fs (hg a ha), ltr_of fs (hg a ha),
      frst_of' fs (hq b hb), ltr_of' fs (hq b hb), add_zero, zero_add]
    split_ifs with h
    · rw [h]
    · rfl
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq']
  split_ifs with hm
  · rw [smul_monomial, smul_eq_mul, mul_comm (coeff a g)]
  · simp only [mem_support_iff, not_not] at hm
    rw [hm, zero_smul]

/- English proof (translation)
Use `conv_lhs => rw [x.as_sum]`. Use `conv_rhs => rw [x.as_sum]`. Repeatedly rewrite using `[map_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations.

Repeatedly rewrite using `[sl_monomial, apply_ite φ, map_zero, ite_mul, zero_mul]`. Rewrite using `[Finset.sum_ite_eq S (ltr fs d), if_pos (hS d hd), ext_monomial]`. Establish `h1 : (monomial (frst fs d) (coeff d x) : MvPolynomial σ K) = coeff d x • monomial (frst fs d) 1`. Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[h1, map_smul, smul_mul_assoc]`.
-/
theorem ext_eq_sum (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) (x : MvPolynomial σ K) (S : Finset (σ →₀ ℕ))
    (hS : ∀ m ∈ x.support, ltr fs m ∈ S) : ext fs φ x = ∑ m ∈ S, φ (slc fs m x) * monomial m 1 := by
  conv_lhs => rw [x.as_sum]
  conv_rhs => rw [x.as_sum]
  simp_rw [map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp_rw [sl_monomial, apply_ite φ, map_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq S (ltr fs d), if_pos (hS d hd), ext_monomial]
  have h1 : (monomial (frst fs d) (coeff d x) : MvPolynomial σ K) = coeff d x • monomial (frst fs d) 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [h1, map_smul, smul_mul_assoc]

/- English proof (translation)
Use `conv_lhs => rw [x.as_sum]`. Use `conv_rhs => rw [x.as_sum]`. Repeatedly rewrite using `[map_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations.

Repeatedly rewrite using `[sl_monomial, ite_mul, zero_mul]`. Rewrite using `[Finset.sum_ite_eq S (ltr fs d), if_pos (hS d hd), monomial_mul, mul_one, frst_add_ltr]`.
-/
theorem eq_sum_sl (x : MvPolynomial σ K) (S : Finset (σ →₀ ℕ)) (hS : ∀ m ∈ x.support, ltr fs m ∈ S) :
    x = ∑ m ∈ S, slc fs m x * monomial m 1 := by
  conv_lhs => rw [x.as_sum]
  conv_rhs => rw [x.as_sum]
  simp_rw [map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp_rw [sl_monomial, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq S (ltr fs d), if_pos (hS d hd), monomial_mul, mul_one, frst_add_ltr]

/- English proof (translation)
Introduce `m' hm' v hv`. Rewrite `hm'` using `[x.as_sum, map_sum]`. Take `⟨d, -, hd⟩` from `Finset.mem_biUnion.mp (MvPolynomial.support_sum hm')`. Rewrite `hd` using `[sl_monomial]`. Use `split_ifs at hd`.

Use `support_monomial_subset hd` as an intermediate fact. Rewrite `this` using `[Finset.mem_singleton]`. Substitute `this` using the available equality. Conclude with `frst_isF fs d v hv`. Simplify using `at hd`.
-/
theorem sl_isF (m : σ →₀ ℕ) (x : MvPolynomial σ K) : IsF fs (slc fs m x) := by
  intro m' hm' v hv
  rw [x.as_sum, map_sum] at hm'
  obtain ⟨d, -, hd⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm')
  rw [sl_monomial] at hd
  split_ifs at hd
  · have := support_monomial_subset hd
    rw [Finset.mem_singleton] at this
    subst this
    exact frst_isF fs d v hv
  · simp at hd

/- English proof (translation)
Introduce `m' hm' v hv`. Use `support_monomial_subset hm'` as an intermediate fact. Rewrite `this` using `[Finset.mem_singleton]`. Substitute `this` using the available equality. Conclude with `ltr_isL fs m v hv`.
-/
theorem isL_monomial_ltr (m : σ →₀ ℕ) (a : K) : IsL fs (monomial (ltr fs m) a) := by
  intro m' hm' v hv
  have := support_monomial_subset hm'
  rw [Finset.mem_singleton] at this
  subst this
  exact ltr_isL fs m v hv

/- English proof (translation)
Introduce `m' hm' v hv`. Use `support_monomial_subset hm'` as an intermediate fact. Rewrite `this` using `[Finset.mem_singleton]`. Substitute `this` using the available equality. Conclude with `frst_isF fs m v hv`.
-/
theorem isF_monomial_frst (m : σ →₀ ℕ) (a : K) : IsF fs (monomial (frst fs m) a) := by
  intro m' hm' v hv
  have := support_monomial_subset hm'
  rw [Finset.mem_singleton] at this
  subst this
  exact frst_isF fs m v hv

/- English proof (translation)
Rewrite using `[monomial_mul, mul_one, frst_add_ltr]`.
-/
theorem monomial_split (m : σ →₀ ℕ) (a : K) :
    monomial m a = monomial (frst fs m) a * monomial (ltr fs m) 1 := by
  rw [monomial_mul, mul_one, frst_add_ltr]

end Ext

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

def fsj (N r j0 : ℕ) : Fin N × Fin r → Prop := fun v => (v.1 : ℕ) < j0

instance (N r j0 : ℕ) : DecidablePred (fsj N r j0) := fun v => Nat.decLt _ _

def wlat (N r j0 : ℕ) : Fin N × Fin r → ℤ := fun v => if (v.1 : ℕ) < j0 then 0 else 1

def wfir (N r j0 : ℕ) : Fin N × Fin r → ℤ := fun v => if (v.1 : ℕ) < j0 then 1 else 0

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero_iff_of_nonneg (fun v _ => nsmul_nonneg (hw v) _)]`. Prove the components needed by the constructor for the conclusion. Introduce `h v hv`. Use `h v (Finsupp.mem_support_iff.mpr hv)` as an intermediate fact. Rewrite `this` using `[nsmul_eq_mul]`.

Break down `mul_eq_zero.mp this with h0 | h0` into its components or cases. Conclude with `absurd (by exact_mod_cast h0 : m v = 0) hv`. Conclude with `h0`. Introduce `h v hv`. Rewrite using `[h v (Finsupp.mem_support_iff.mp hv), smul_zero]`.
-/
theorem weight_eq_zero_iff {σ : Type} (w : σ → ℤ) (hw : ∀ v, 0 ≤ w v) (m : σ →₀ ℕ) :
    Finsupp.weight w m = 0 ↔ ∀ v, m v ≠ 0 → w v = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero_iff_of_nonneg (fun v _ => nsmul_nonneg (hw v) _)]
  constructor
  · intro h v hv
    have := h v (Finsupp.mem_support_iff.mpr hv)
    rw [nsmul_eq_mul] at this
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (by exact_mod_cast h0 : m v = 0) hv
    · exact h0
  · intro h v hv
    rw [h v (Finsupp.mem_support_iff.mp hv), smul_zero]

/- English proof (translation)
Rewrite using `[mem_weightedHomogeneousSubmodule]`. Establish `hw : ∀ v, 0 ≤ wlat N r j0 v` using `fun v => by`. Unfold `wlat`. Apply the tactic sequence `split_ifs <;> norm_num`. Establish `key : ∀ d : Fin N × Fin r →₀ ℕ, Finsupp.weight (wlat N r j0) d = 0 ↔ ∀ v, d v ≠ 0 → fsj N r j0 v`.

Introduce `d`. Rewrite using `[weight_eq_zero_iff _ hw]`. Use `forall_congr' fun v => imp_congr_right fun _ => ?_` and prove the remaining obligations. Unfold `wlat fsj`. Apply the tactic sequence `split_ifs with h <;> simp [h]`.

Prove the components needed by the constructor for the conclusion. Introduce `h d hd`. Conclude with `(key d).mpr (h d (mem_support_iff.mpr hd))`. Introduce `h d hd v hv`. Conclude with `(key d).mp (h (mem_support_iff.mp hd)) v hv`.
-/
theorem isF_iff (j0 : ℕ) (g : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    IsF (fsj N r j0) g ↔ g ∈ weightedHomogeneousSubmodule ℚ_[p] (wlat N r j0) 0 := by
  rw [mem_weightedHomogeneousSubmodule]
  have hw : ∀ v, 0 ≤ wlat N r j0 v := fun v => by
    unfold wlat
    split_ifs <;> norm_num
  have key : ∀ d : Fin N × Fin r →₀ ℕ, Finsupp.weight (wlat N r j0) d = 0 ↔ ∀ v, d v ≠ 0 → fsj N r j0 v := by
    intro d
    rw [weight_eq_zero_iff _ hw]
    refine forall_congr' fun v => imp_congr_right fun _ => ?_
    unfold wlat fsj
    split_ifs with h <;> simp [h]
  constructor
  · intro h d hd
    exact (key d).mpr (h d (mem_support_iff.mpr hd))
  · intro h d hd v hv
    exact (key d).mp (h (mem_support_iff.mp hd)) v hv

/- English proof (translation)
Rewrite using `[mem_weightedHomogeneousSubmodule]`. Establish `hw : ∀ v, 0 ≤ wfir N r j0 v` using `fun v => by`. Unfold `wfir`. Apply the tactic sequence `split_ifs <;> norm_num`. Establish `key : ∀ d : Fin N × Fin r →₀ ℕ, Finsupp.weight (wfir N r j0) d = 0 ↔ ∀ v, d v ≠ 0 → ¬ fsj N r j0 v`.

Introduce `d`. Rewrite using `[weight_eq_zero_iff _ hw]`. Use `forall_congr' fun v => imp_congr_right fun _ => ?_` and prove the remaining obligations. Unfold `wfir fsj`. Apply the tactic sequence `split_ifs with h <;> simp [h]`.

Prove the components needed by the constructor for the conclusion. Introduce `h d hd`. Conclude with `(key d).mpr (h d (mem_support_iff.mpr hd))`. Introduce `h d hd v hv`. Conclude with `(key d).mp (h (mem_support_iff.mp hd)) v hv`.
-/
theorem isL_iff (j0 : ℕ) (g : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    IsL (fsj N r j0) g ↔ g ∈ weightedHomogeneousSubmodule ℚ_[p] (wfir N r j0) 0 := by
  rw [mem_weightedHomogeneousSubmodule]
  have hw : ∀ v, 0 ≤ wfir N r j0 v := fun v => by
    unfold wfir
    split_ifs <;> norm_num
  have key : ∀ d : Fin N × Fin r →₀ ℕ, Finsupp.weight (wfir N r j0) d = 0 ↔ ∀ v, d v ≠ 0 → ¬ fsj N r j0 v := by
    intro d
    rw [weight_eq_zero_iff _ hw]
    refine forall_congr' fun v => imp_congr_right fun _ => ?_
    unfold wfir fsj
    split_ifs with h <;> simp [h]
  constructor
  · intro h d hd
    exact (key d).mpr (h d (mem_support_iff.mpr hd))
  · intro h d hd v hv
    exact (key d).mp (h (mem_support_iff.mp hd)) v hv

/- English proof (translation)
Rewrite `hg`, the goal using `[isF_iff]`. Conclude with `glAct_lw L J c d (wlat N r j0) (fun i c c' => rfl) hg`.
-/
theorem glAct_isF (L : Letters N) (j0 J : ℕ) (c d : Fin r) {g : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hg : IsF (fsj N r j0) g) : IsF (fsj N r j0) (glAct p L J c d g) := by
  rw [isF_iff] at hg ⊢
  exact glAct_lw L J c d (wlat N r j0) (fun i c c' => rfl) hg

/- English proof (translation)
Rewrite `hg`, the goal using `[isL_iff]`. Conclude with `glAct_lw L J c d (wfir N r j0) (fun i c c' => rfl) hg`.
-/
theorem glAct_isL (L : Letters N) (j0 J : ℕ) (c d : Fin r) {g : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hg : IsL (fsj N r j0) g) : IsL (fsj N r j0) (glAct p L J c d g) := by
  rw [isL_iff] at hg ⊢
  exact glAct_lw L J c d (wfir N r j0) (fun i c c' => rfl) hg

/- English proof (translation)
Rewrite using `[midAct, LinearMap.sum_apply]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Rewrite using `[Formalism.GM.FrozenVariableComponents.top_apply]`. Establish `hz : ∀ e : Fin r, pderiv (i, e) g = 0` using `fun e => pderiv_eq_zero_of fun m hm => by`.

Assume the negation of the conclusion as `hne`. Use `hg m hm (i, e) hne` as an intermediate fact. Simplify using `[fsj] at this`. Use linear arithmetic over natural numbers and integers. Apply the tactic sequence `split_ifs <;> simp [hz]`.

Both sides reduce to the same expression.
-/
theorem midAct_isF (L : Letters N) (j0 J : ℕ) (c d : Fin r) {g : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hg : IsF (fsj N r j0) g) : midAct p L j0 J c d g = 0 := by
  rw [midAct, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs with h
  · rw [Formalism.GM.FrozenVariableComponents.top_apply]
    have hz : ∀ e : Fin r, pderiv (i, e) g = 0 := fun e => pderiv_eq_zero_of fun m hm => by
      by_contra hne; have := hg m hm (i, e) hne; simp [fsj] at this; omega
    split_ifs <;> simp [hz]
  · rfl

/- English proof (translation)
Introduce `m hm v hv`. Assume the negation of the conclusion as `hne`. Conclude with `hq m hm v hne (show fsj N r j0 v from lt_of_lt_of_le hv hJ)`.
-/
theorem killL_of_isL {j0 J : ℕ} (hJ : J ≤ j0) {q : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hq : IsL (fsj N r j0) q) :
    ∀ m ∈ q.support, ∀ v : Fin N × Fin r, (v.1 : ℕ) < J → m v = 0 := by
  intro m hm v hv
  by_contra hne
  exact hq m hm v hne (show fsj N r j0 v from lt_of_lt_of_le hv hJ)

/- English proof (translation)
Proceed by induction on `x using MvPolynomial.induction_on' with`. Consider the case `monomial m' a`. Rewrite using `[monomial_split (fsj N r j0) m' a, glAct_mul_kill L J c d _ (killL_of_isL hJ (isL_monomial_ltr _ m' 1)), sl_mul _ m (glAct_isF L j0 J c d (isF_monomial_frst _ m' a)) (isL_monomial_ltr _ m' 1), sl_mul _ m (isF_monomial_frst _ m' a) (isL_monomial_ltr _ m' 1), map_smul]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]`.
-/
theorem slc_glAct (L : Letters N) {j0 J : ℕ} (hJ : J ≤ j0) (c d : Fin r) (m : Fin N × Fin r →₀ ℕ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    slc (fsj N r j0) m (glAct p L J c d x) = glAct p L J c d (slc (fsj N r j0) m x) := by
  induction x using MvPolynomial.induction_on' with
  | monomial m' a =>
    rw [monomial_split (fsj N r j0) m' a,
      glAct_mul_kill L J c d _ (killL_of_isL hJ (isL_monomial_ltr _ m' 1)),
      sl_mul _ m (glAct_isF L j0 J c d (isF_monomial_frst _ m' a)) (isL_monomial_ltr _ m' 1),
      sl_mul _ m (isF_monomial_frst _ m' a) (isL_monomial_ltr _ m' 1), map_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum]`. Use `Finset.sum_eq_zero fun v hv => ?_` and prove the remaining obligations. Establish `h1` using `hm v (Finsupp.mem_support_iff.mp hv)`. Establish `h2 : ¬ ((v.1 : ℕ) < J)` using `fun h => h1 (show fsj N r j0 v from lt_of_lt_of_le h hJ)`. Simplify using `[Formalism.GM.DimensionMonotonicity.wv, h2]`.
-/
theorem weight_wv_zero (L : Letters N) {j0 J : ℕ} (hJ : J ≤ j0) (m : Fin N × Fin r →₀ ℕ)
    (hm : ∀ v, m v ≠ 0 → ¬ fsj N r j0 v) : Finsupp.weight (wv L J) m = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun v hv => ?_
  have h1 := hm v (Finsupp.mem_support_iff.mp hv)
  have h2 : ¬ ((v.1 : ℕ) < J) := fun h => h1 (show fsj N r j0 v from lt_of_lt_of_le h hJ)
  simp [Formalism.GM.DimensionMonotonicity.wv, h2]

/- English proof (translation)
Rewrite `hx`, the goal using `[mem_weightedHomogeneousSubmodule]`. Introduce `d hd`. Establish `hd' : d ∈ (slc (fsj N r j0) m x).support` using `mem_support_iff.mpr hd`. Rewrite `hd'` using `[x.as_sum, map_sum]`. Take `⟨e, he, hde⟩` from `Finset.mem_biUnion.mp (MvPolynomial.support_sum hd')`.

Rewrite `hde` using `[sl_monomial]`. Use `split_ifs at hde`. Use `support_monomial_subset hde` as an intermediate fact. Rewrite `this` using `[Finset.mem_singleton]`. Substitute `this` using the available equality.

Establish `hw` using `hx (mem_support_iff.mp he)`. Rewrite `hw` using `[← frst_add_ltr (fsj N r j0) e, map_add, weight_wv_zero L hJ _ (ltr_isL _ e), add_zero]`. Conclude with `hw`. Simplify using `at hde`.
-/
theorem slc_wh (L : Letters N) {j0 J : ℕ} (hJ : J ≤ j0) (m : Fin N × Fin r →₀ ℕ) {ν : Fin r → ℤ}
    {x : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) ν) :
    slc (fsj N r j0) m x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) ν := by
  rw [mem_weightedHomogeneousSubmodule] at hx ⊢
  intro d hd
  have hd' : d ∈ (slc (fsj N r j0) m x).support := mem_support_iff.mpr hd
  rw [x.as_sum, map_sum] at hd'
  obtain ⟨e, he, hde⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd')
  rw [sl_monomial] at hde
  split_ifs at hde
  · have := support_monomial_subset hde
    rw [Finset.mem_singleton] at this
    subst this
    have hw := hx (mem_support_iff.mp he)
    rw [← frst_add_ltr (fsj N r j0) e, map_add, weight_wv_zero L hJ _ (ltr_isL _ e), add_zero] at hw
    exact hw
  · simp at hde

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

/- English proof (translation)
The claim follows from `ycond_of_comm L J M (slc (fsj N r j0) m) (fun c d F => slc_glAct L hJ c d m F) (fun ν F hF => slc_wh L hJ m hF) F hF`.
-/
theorem slc_ycond [NeZero r] (L : Letters N) {j0 J : ℕ} (hJ : J ≤ j0) (M : WithTop ℤ) (m : Fin N × Fin r →₀ ℕ)
    {F : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hF : F ∈ YCond p L J M) : slc (fsj N r j0) m F ∈ YCond p L J M :=
  ycond_of_comm L J M (slc (fsj N r j0) m) (fun c d F => slc_glAct L hJ c d m F) (fun ν F hF => slc_wh L hJ m hF) F hF

/- English proof (translation)
Unfold `Formalism.GM.M.Pol at hx ⊢`. Rewrite `hx`, the goal using `[mem_restrictSupport_iff]`. Introduce `d hd`. Rewrite `hd` using `[Finset.mem_coe, x.as_sum, map_sum]`. Take `⟨e, he, hde⟩` from `Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)`.

Rewrite `hde` using `[sl_monomial]`. Use `split_ifs at hde`. Use `support_monomial_subset hde` as an intermediate fact. Rewrite `this` using `[Finset.mem_singleton]`. Substitute `this` using the available equality.

Establish `hme : Formalism.GM.M.MultiDeg L e` using `hx (Finset.mem_coe.mpr he)`. Introduce `i`. Simplify using `only [Formalism.GM.DimensionMonotonicity.Lz]`. Use `split_ifs with hi`. Rewrite using `[← hme i]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `[frst, Finsupp.filter_apply, fsj, hi]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Simplify using `[frst, Finsupp.filter_apply, fsj, hi]`. Simplify using `at hde`.
-/
theorem slc_pol (L : Letters N) (j0 : ℕ) (m : Fin N × Fin r →₀ ℕ) {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ Pol p r L) : slc (fsj N r j0) m x ∈ Pol p r (Lz L j0) := by
  unfold Formalism.GM.M.Pol at hx ⊢
  rw [mem_restrictSupport_iff] at hx ⊢
  intro d hd
  rw [Finset.mem_coe, x.as_sum, map_sum] at hd
  obtain ⟨e, he, hde⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  rw [sl_monomial] at hde
  split_ifs at hde
  · have := support_monomial_subset hde
    rw [Finset.mem_singleton] at this
    subst this
    have hme : Formalism.GM.M.MultiDeg L e := hx (Finset.mem_coe.mpr he)
    intro i
    simp only [Formalism.GM.DimensionMonotonicity.Lz]
    split_ifs with hi
    · rw [← hme i]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp [frst, Finsupp.filter_apply, fsj, hi]
    · refine Finset.sum_eq_zero fun c _ => ?_
      simp [frst, Finsupp.filter_apply, fsj, hi]
  · simp at hde

/- English proof (translation)
Introduce `m hm v hv`. Unfold `Formalism.GM.M.Pol at hy`. Rewrite `hy` using `[mem_restrictSupport_iff]`. Establish `hmd : Formalism.GM.M.MultiDeg (Lz L j0) m` using `hy (Finset.mem_coe.mpr hm)`. Assume the negation of the conclusion as `hv'`.

Establish `hv'' : ¬ ((v.1 : ℕ) < j0)` using `hv'`. Establish `h1` using `hmd v.1`. Simplify using `only [Formalism.GM.DimensionMonotonicity.Lz] at h1`. Rewrite `h1` using `[if_neg hv'']`. Establish `h2 : m (v.1, v.2) = 0` using `(Finset.sum_eq_zero_iff.mp h1) v.2 (Finset.mem_univ _)`.

Conclude with `hv h2`.
-/
theorem isF_of_polLz (L : Letters N) (j0 : ℕ) {y : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hy : y ∈ Pol p r (Lz L j0)) : IsF (fsj N r j0) y := by
  intro m hm v hv
  unfold Formalism.GM.M.Pol at hy
  rw [mem_restrictSupport_iff] at hy
  have hmd : Formalism.GM.M.MultiDeg (Lz L j0) m := hy (Finset.mem_coe.mpr hm)
  by_contra hv'
  have hv'' : ¬ ((v.1 : ℕ) < j0) := hv'
  have h1 := hmd v.1
  simp only [Formalism.GM.DimensionMonotonicity.Lz] at h1
  rw [if_neg hv''] at h1
  have h2 : m (v.1, v.2) = 0 := (Finset.sum_eq_zero_iff.mp h1) v.2 (Finset.mem_univ _)
  exact hv h2

/- English proof (translation)
Unfold `Formalism.GM.M.Pol at hg ⊢`. Rewrite `hg`, the goal using `[mem_restrictSupport_iff]`. Introduce `d hd`. Rewrite `hd` using `[Finset.mem_coe]`. Take `⟨a, ha, b, hb, rfl⟩` from `Finset.mem_add.mp (support_mul _ _ hd)`.

Establish `hb'` using `support_monomial_subset hb`. Rewrite `hb'` using `[Finset.mem_singleton]`. Substitute `hb'` using the available equality. Establish `hma : Formalism.GM.M.MultiDeg (Lz L j0) a` using `hg (Finset.mem_coe.mpr ha)`. Introduce `i`.

Establish `h1` using `hma i`. Establish `h2` using `hm i`. Simplify using `only [Formalism.GM.DimensionMonotonicity.Lz] at h1`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib]`. Use `split_ifs at h1 with hi`.

Rewrite using `[h1]`. Establish `h3 : ∑ c, ltr (fsj N r j0) m' (i, c) = 0` using `Finset.sum_eq_zero fun c _ => by simp [ltr, Finsupp.filter_apply, fsj, hi]`. Rewrite using `[h3, add_zero]`. Rewrite using `[h1, zero_add, ← h2]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Simplify using `[ltr, Finsupp.filter_apply, fsj, hi]`.
-/
theorem mul_ltr_pol (L : Letters N) (j0 : ℕ) {g : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hg : g ∈ Pol p r (Lz L j0))
    {m' : Fin N × Fin r →₀ ℕ} (hm : MultiDeg L m') : g * monomial (ltr (fsj N r j0) m') 1 ∈ Pol p r L := by
  unfold Formalism.GM.M.Pol at hg ⊢
  rw [mem_restrictSupport_iff] at hg ⊢
  intro d hd
  rw [Finset.mem_coe] at hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul _ _ hd)
  have hb' := support_monomial_subset hb
  rw [Finset.mem_singleton] at hb'
  subst hb'
  have hma : Formalism.GM.M.MultiDeg (Lz L j0) a := hg (Finset.mem_coe.mpr ha)
  intro i
  have h1 := hma i
  have h2 := hm i
  simp only [Formalism.GM.DimensionMonotonicity.Lz] at h1
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  split_ifs at h1 with hi
  · rw [h1]
    have h3 : ∑ c, ltr (fsj N r j0) m' (i, c) = 0 :=
      Finset.sum_eq_zero fun c _ => by simp [ltr, Finsupp.filter_apply, fsj, hi]
    rw [h3, add_zero]
  · rw [h1, zero_add, ← h2]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [ltr, Finsupp.filter_apply, fsj, hi]

/- English proof (translation)
Rewrite using `[glAct_split L hJ c d, LinearMap.add_apply]`. Normalize the expressions using the abelian group laws.
-/
theorem midAct_eq (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    midAct p L j0 J c d x = glAct p L J c d x - glAct p L j0 c d x := by
  rw [glAct_split L hJ c d, LinearMap.add_apply]; abel

/- English proof (translation)
Rewrite using `[midAct_eq L hJ, isL_iff]`. Conclude with `Submodule.sub_mem _ ((isL_iff _ _).mp (glAct_isL L j0 J c d hq)) ((isL_iff _ _).mp (glAct_isL L j0 j0 c d hq))`.
-/
theorem midAct_isL (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (c d : Fin r) {q : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hq : IsL (fsj N r j0) q) : IsL (fsj N r j0) (midAct p L j0 J c d q) := by
  rw [midAct_eq L hJ, isL_iff]
  exact Submodule.sub_mem _ ((isL_iff _ _).mp (glAct_isL L j0 J c d hq)) ((isL_iff _ _).mp (glAct_isL L j0 j0 c d hq))

/- English proof (translation)
Establish `h0` using `midAct_isF L j0 J c d hg`. Rewrite `h0`, the goal using `[midAct_eq L hJ]`. Rewrite using `[midAct_eq L hJ c d q, Formalism.GM.M.FB.glAct_mul, Formalism.GM.M.FB.glAct_mul]`. Establish `: q * glAct p L J c d g - q * glAct p L j0 c d g = 0` using `by rw [← mul_sub, h0, mul_zero]`. Take the linear combination `this`.
-/
theorem midAct_mul_F (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (c d : Fin r) {g q : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hg : IsF (fsj N r j0) g) : midAct p L j0 J c d (g * q) = g * midAct p L j0 J c d q := by
  have h0 := midAct_isF L j0 J c d hg
  rw [midAct_eq L hJ] at h0 ⊢
  rw [midAct_eq L hJ c d q, Formalism.GM.M.FB.glAct_mul, Formalism.GM.M.FB.glAct_mul]
  have : q * glAct p L J c d g - q * glAct p L j0 c d g = 0 := by rw [← mul_sub, h0, mul_zero]
  linear_combination this

/- English proof (translation)
Proceed by induction on `x using MvPolynomial.induction_on' with`. Consider the case `monomial m' a`. Establish `hg` using `isF_monomial_frst (fsj N r j0) m' a`. Establish `hq` using `isL_monomial_ltr (fsj N r j0) m' (1 : ℚ_[p])`. Rewrite using `[monomial_split (fsj N r j0) m' a, ext_mul _ φ hg hq, glAct_split L hJ c d, LinearMap.add_apply, LinearMap.add_apply, glAct_mul_kill L j0 c d _ (killL_of_isL le_rfl hq), midAct_mul_F L hJ c d hg, glAct_mul_kill L j0 c d _ (killL_of_isL le_rfl hq), midAct_mul_F L hJ c d (hφF _), m …`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem ext_glAct (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hφ1 : ∀ c d x, φ (glAct p L j0 c d x) = glAct p L j0 c d (φ x)) (hφF : ∀ x, IsF (fsj N r j0) (φ x))
    (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    ext (fsj N r j0) φ (glAct p L J c d x) = glAct p L J c d (ext (fsj N r j0) φ x) := by
  induction x using MvPolynomial.induction_on' with
  | monomial m' a =>
    have hg := isF_monomial_frst (fsj N r j0) m' a
    have hq := isL_monomial_ltr (fsj N r j0) m' (1 : ℚ_[p])
    rw [monomial_split (fsj N r j0) m' a, ext_mul _ φ hg hq, glAct_split L hJ c d, LinearMap.add_apply,
      LinearMap.add_apply, glAct_mul_kill L j0 c d _ (killL_of_isL le_rfl hq), midAct_mul_F L hJ c d hg,
      glAct_mul_kill L j0 c d _ (killL_of_isL le_rfl hq), midAct_mul_F L hJ c d (hφF _), map_add,
      ext_mul _ φ (glAct_isF L j0 j0 c d hg) hq, ext_mul _ φ hg (midAct_isL L hJ c d hq), hφ1]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]`. Use `Finset.sum_congr rfl fun v hv => ?_` and prove the remaining obligations. Establish `h1 : (v.1 : ℕ) < j0` using `hm v (Finsupp.mem_support_iff.mp hv)`. Establish `h2 : (v.1 : ℕ) < J` using `lt_of_lt_of_le h1 hJ`. Simplify using `[Formalism.GM.DimensionMonotonicity.wv, h1, h2]`.
-/
theorem weight_first (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (m : Fin N × Fin r →₀ ℕ)
    (hm : ∀ v, m v ≠ 0 → fsj N r j0 v) : Finsupp.weight (wv L J) m = Finsupp.weight (wv L j0) m := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have h1 : (v.1 : ℕ) < j0 := hm v (Finsupp.mem_support_iff.mp hv)
  have h2 : (v.1 : ℕ) < J := lt_of_lt_of_le h1 hJ
  simp [Formalism.GM.DimensionMonotonicity.wv, h1, h2]

/- English proof (translation)
Rewrite `hy`, the goal using `[mem_weightedHomogeneousSubmodule]`. Introduce `d hd`. Rewrite using `[weight_first L hJ d (hF d (mem_support_iff.mpr hd))]`. Conclude with `hy hd`.
-/
theorem wh_first (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) {ν : Fin r → ℤ} {y : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hF : IsF (fsj N r j0) y) (hy : y ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν) :
    y ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) ν := by
  rw [mem_weightedHomogeneousSubmodule] at hy ⊢
  intro d hd
  rw [weight_first L hJ d (hF d (mem_support_iff.mpr hd))]
  exact hy hd

/- English proof (translation)
Rewrite using `[x.as_sum, map_sum]`. Use `Submodule.sum_mem _ fun m' hm' => ?_` and prove the remaining obligations. Rewrite using `[ext_monomial]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `h1 : Finsupp.weight (wv L J) m' = ν` using `hx (mem_support_iff.mp hm')`.

Establish `hf : φ (monomial (frst (fsj N r j0) m') 1) ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) (Finsupp.weight (wv L J) (frst (fsj N r j0) m'))`. Rewrite using `[weight_first L hJ _ (frst_isF _ m')]`. Conclude with `wh_first L hJ (hφF _) (hφw _ _ (isWeightedHomogeneous_monomial _ _ _ rfl))`. Establish `hl : IsWeightedHomogeneous (wv L J) (monomial (ltr (fsj N r j0) m') (1 : ℚ_[p])) (Finsupp.weight (wv L J) (ltr (fsj N r j0) m'))` using `isWeightedHomogeneous_monomial _ _ _ rfl`. Rewrite `hf`, the goal using `[mem_weightedHomogeneousSubmodule]`.

Rewrite using `[← h1]`. Use `conv_rhs => rw [← frst_add_ltr (fsj N r j0) m']`. Rewrite using `[map_add]`. Conclude with `hf.mul hl`.
-/
theorem ext_wh (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hφw : ∀ ν x, x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν → φ x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν)
    (hφF : ∀ x, IsF (fsj N r j0) (φ x)) (ν : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) ν) :
    ext (fsj N r j0) φ x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) ν := by
  classical
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m' hm' => ?_
  rw [ext_monomial]
  refine Submodule.smul_mem _ _ ?_
  have h1 : Finsupp.weight (wv L J) m' = ν := hx (mem_support_iff.mp hm')
  have hf : φ (monomial (frst (fsj N r j0) m') 1) ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J)
      (Finsupp.weight (wv L J) (frst (fsj N r j0) m')) := by
    rw [weight_first L hJ _ (frst_isF _ m')]
    exact wh_first L hJ (hφF _) (hφw _ _ (isWeightedHomogeneous_monomial _ _ _ rfl))
  have hl : IsWeightedHomogeneous (wv L J) (monomial (ltr (fsj N r j0) m') (1 : ℚ_[p]))
      (Finsupp.weight (wv L J) (ltr (fsj N r j0) m')) := isWeightedHomogeneous_monomial _ _ _ rfl
  rw [mem_weightedHomogeneousSubmodule] at hf ⊢
  rw [← h1]
  conv_rhs => rw [← frst_add_ltr (fsj N r j0) m']
  rw [map_add]
  exact hf.mul hl

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

def Mup {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (j0 : ℕ) : Fin q → WithTop ℤ :=
  fun k => if J k < j0 then M k else ⊤

noncomputable def Cset (p : ℕ) [Fact p.Prime] [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  Pol p r (Lz L j0) ⊓ ⨅ k, YCond p L (J k) (Mup J M j0 k)

/- English proof (translation)
Take `⟨hxP, hxY⟩` from `Submodule.mem_inf.mp hx`. Use `Submodule.mem_inf.mpr ⟨slc_pol L j0 m hxP, (Submodule.mem_iInf _).mpr fun k => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hk : J k < j0`. Rewrite using `[Mup, if_pos hk]`. Conclude with `slc_ycond L (le_of_lt hk) (M k) m ((Submodule.mem_iInf _).mp hxY k)`.

Rewrite using `[Mup, if_neg hk, ycond_top]`. Conclude with `Submodule.mem_top`.
-/
theorem slc_C [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    {x : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hx : x ∈ Y p L J M) (m : Fin N × Fin r →₀ ℕ) :
    slc (fsj N r j0) m x ∈ Cset p L j0 J M := by
  obtain ⟨hxP, hxY⟩ := Submodule.mem_inf.mp hx
  refine Submodule.mem_inf.mpr ⟨slc_pol L j0 m hxP, (Submodule.mem_iInf _).mpr fun k => ?_⟩
  by_cases hk : J k < j0
  · rw [Mup, if_pos hk]
    exact slc_ycond L (le_of_lt hk) (M k) m ((Submodule.mem_iInf _).mp hxY k)
  · rw [Mup, if_neg hk, ycond_top]; exact Submodule.mem_top

/- English proof (translation)
Introduce `x hx`. Take `⟨hxP, hxY⟩` from `Submodule.mem_inf.mp hx`. Establish `hφF : ∀ x, IsF (fsj N r j0) (φ x)` using `fun x => isF_of_polLz L j0 (hφP x)`. Establish `hsum` using `ext_eq_sum (fsj N r j0) φ x (x.support.image (ltr (fsj N r j0))) (fun m hm => Finset.mem_image_of_mem _ hm)`. Use `Submodule.mem_inf.mpr ⟨?_, (Submodule.mem_iInf _).mpr fun k => ?_⟩` and prove the remaining obligations.

Rewrite using `[hsum]`. Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Take `⟨m', hm', rfl⟩` from `Finset.mem_image.mp hm`. Conclude with `mul_ltr_pol L j0 (hφP _) (((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hxP) hm')`. Distinguish the cases in `hk : J k < j0`.

Rewrite using `[hsum]`. Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Take `⟨m', hm', rfl⟩` from `Finset.mem_image.mp hm`. Establish `h1` using `(Submodule.mem_iInf _).mp (Submodule.mem_inf.mp (hφC _ (slc_C L j0 J M hx (ltr (fsj N r j0) m')))).2 k`. Rewrite `h1` using `[Mup, if_pos hk]`.

Rewrite using `[mul_comm]`. Conclude with `ycond_mul_B L (le_of_lt hk) (M k) (killL_of_isL le_rfl (isL_monomial_ltr _ m' 1)) _ h1`. Establish `hJ : j0 ≤ J k` using `by omega`. Conclude with `ycond_of_comm L (J k) (M k) (ext (fsj N r j0) φ) (ext_glAct L hJ φ hφ1 hφF) (fun ν F hF => ext_wh L hJ φ hφw hφF ν F hF) x ((Submodule.mem_iInf _).mp hxY k)`.
-/
theorem ext_Y [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hφ1 : ∀ c d x, φ (glAct p L j0 c d x) = glAct p L j0 c d (φ x))
    (hφw : ∀ ν x, x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν → φ x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν)
    (hφP : ∀ x, φ x ∈ Pol p r (Lz L j0)) (hφC : ∀ x ∈ Cset p L j0 J M, φ x ∈ Cset p L j0 J M) :
    ∀ x ∈ Y p L J M, ext (fsj N r j0) φ x ∈ Y p L J M := by
  classical
  intro x hx
  obtain ⟨hxP, hxY⟩ := Submodule.mem_inf.mp hx
  have hφF : ∀ x, IsF (fsj N r j0) (φ x) := fun x => isF_of_polLz L j0 (hφP x)
  have hsum := ext_eq_sum (fsj N r j0) φ x (x.support.image (ltr (fsj N r j0)))
    (fun m hm => Finset.mem_image_of_mem _ hm)
  refine Submodule.mem_inf.mpr ⟨?_, (Submodule.mem_iInf _).mpr fun k => ?_⟩
  · rw [hsum]
    refine Submodule.sum_mem _ fun m hm => ?_
    obtain ⟨m', hm', rfl⟩ := Finset.mem_image.mp hm
    exact mul_ltr_pol L j0 (hφP _) (((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hxP) hm')
  · by_cases hk : J k < j0
    · rw [hsum]
      refine Submodule.sum_mem _ fun m hm => ?_
      obtain ⟨m', hm', rfl⟩ := Finset.mem_image.mp hm
      have h1 := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp (hφC _ (slc_C L j0 J M hx (ltr (fsj N r j0) m')))).2 k
      rw [Mup, if_pos hk] at h1
      rw [mul_comm]
      exact ycond_mul_B L (le_of_lt hk) (M k) (killL_of_isL le_rfl (isL_monomial_ltr _ m' 1)) _ h1
    · have hJ : j0 ≤ J k := by omega
      exact ycond_of_comm L (J k) (M k) (ext (fsj N r j0) φ) (ext_glAct L hJ φ hφ1 hφF)
        (fun ν F hF => ext_wh L hJ φ hφw hφF ν F hF) x ((Submodule.mem_iInf _).mp hxY k)

noncomputable def psi (p : ℕ) [Fact p.Prime] (L : Letters N) (j0 : ℕ) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  weightedHomogeneousComponent (wL N r) (fun i => ((Lz L j0).deg i : ℤ))

/- English proof (translation)
Rewrite using `[pol_iff]`. Conclude with `weightedHomogeneousComponent_isWeightedHomogeneous _ _`.
-/
theorem psi_mem (L : Letters N) (j0 : ℕ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) : psi p L j0 x ∈ Pol p r (Lz L j0) := by
  rw [pol_iff]; exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

/- English proof (translation)
Rewrite `hx` using `[pol_iff]`. Rewrite using `[psi, weightedHomogeneousComponent_of_mem hx, if_pos rfl]`.
-/
theorem psi_id (L : Letters N) (j0 : ℕ) {x : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hx : x ∈ Pol p r (Lz L j0)) :
    psi p L j0 x = x := by
  rw [pol_iff] at hx
  rw [psi, weightedHomogeneousComponent_of_mem hx, if_pos rfl]

/- English proof (translation)
Rewrite `h` using `[mem_weightedHomogeneousSubmodule]`. Use extensionality with `d`. Rewrite using `[coeff_weightedHomogeneousComponent]`. Use `split_ifs with hd`. Both sides reduce to the same expression.

Assume the negation of the conclusion as `hne`. Conclude with `hd (h (Ne.symm hne))`.
-/
private theorem whc_same_lemma {σ M : Type} [AddCommMonoid M] (w : σ → M) {m : M} {φ : MvPolynomial σ ℚ_[p]}
    (h : φ ∈ weightedHomogeneousSubmodule ℚ_[p] w m) : weightedHomogeneousComponent w m φ = φ := by
  classical
  rw [mem_weightedHomogeneousSubmodule] at h
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with hd
  · rfl
  · by_contra hne
    exact hd (h (Ne.symm hne))

/- English proof (translation)
Rewrite `h` using `[mem_weightedHomogeneousSubmodule]`. Use extensionality with `d`. Rewrite using `[coeff_weightedHomogeneousComponent, coeff_zero]`. Use `split_ifs with hd`. Assume the negation of the conclusion as `hne`.

Conclude with `hnm (hd.symm.trans (h hne))`. Both sides reduce to the same expression.
-/
private theorem whc_ne_lemma_2 {σ M : Type} [AddCommMonoid M] (w : σ → M) {m n : M} {φ : MvPolynomial σ ℚ_[p]}
    (h : φ ∈ weightedHomogeneousSubmodule ℚ_[p] w m) (hnm : n ≠ m) : weightedHomogeneousComponent w n φ = 0 := by
  classical
  rw [mem_weightedHomogeneousSubmodule] at h
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_zero]
  split_ifs with hd
  · by_contra hne
    exact hnm (hd.symm.trans (h hne))
  · rfl

/- English proof (translation)
Use `MvPolynomial.induction_on' x (fun d a => ?_) (fun f g hf hg => ?_)` and prove the remaining obligations. Establish `h0 : monomial d a ∈ weightedHomogeneousSubmodule ℚ_[p] w (Finsupp.weight w d)` using `(mem_weightedHomogeneousSubmodule ..).mpr (isWeightedHomogeneous_monomial w d a rfl)`. Establish `h1` using `hA _ _ h0`. Distinguish the cases in `h : Finsupp.weight w d = D`. Substitute `h` using the available equality.

Rewrite using `[whc_same_lemma w h0, whc_same_lemma w h1]`. Rewrite using `[whc_ne_lemma_2 w h0 (Ne.symm h), whc_ne_lemma_2 w h1 (Ne.symm h), map_zero]`. Simplify using `only [map_add, hf, hg]`.
-/
theorem whc_comm {σ M : Type} [AddCommMonoid M] (w : σ → M) (A : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])
    (hA : ∀ D x, x ∈ weightedHomogeneousSubmodule ℚ_[p] w D → A x ∈ weightedHomogeneousSubmodule ℚ_[p] w D)
    (D : M) (x : MvPolynomial σ ℚ_[p]) :
    weightedHomogeneousComponent w D (A x) = A (weightedHomogeneousComponent w D x) := by
  classical
  refine MvPolynomial.induction_on' x (fun d a => ?_) (fun f g hf hg => ?_)
  · have h0 : monomial d a ∈ weightedHomogeneousSubmodule ℚ_[p] w (Finsupp.weight w d) :=
      (mem_weightedHomogeneousSubmodule ..).mpr (isWeightedHomogeneous_monomial w d a rfl)
    have h1 := hA _ _ h0
    by_cases h : Finsupp.weight w d = D
    · subst h
      rw [whc_same_lemma w h0, whc_same_lemma w h1]
    · rw [whc_ne_lemma_2 w h0 (Ne.symm h), whc_ne_lemma_2 w h1 (Ne.symm h), map_zero]
  · simp only [map_add, hf, hg]

/- English proof (translation)
Rewrite `hx`, the goal using `[mem_weightedHomogeneousSubmodule]`. Introduce `d hd`. Rewrite `hd` using `[coeff_weightedHomogeneousComponent]`. Use `split_ifs at hd with h`. Conclude with `hx hd`.

Conclude with `absurd rfl hd`.
-/
theorem whc_keep {σ M M' : Type} [AddCommMonoid M] [AddCommMonoid M'] (w : σ → M) (w' : σ → M') (ν : M')
    (D : M) {x : MvPolynomial σ ℚ_[p]} (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] w D) :
    weightedHomogeneousComponent w' ν x ∈ weightedHomogeneousSubmodule ℚ_[p] w D := by
  classical
  rw [mem_weightedHomogeneousSubmodule] at hx ⊢
  intro d hd
  rw [coeff_weightedHomogeneousComponent] at hd
  split_ifs at hd with h
  · exact hx hd
  · exact absurd rfl hd

/- English proof (translation)
The claim follows from `whc_comm _ _ (fun D x hx => glAct_wL L' j c d hx) _ x`.
-/
theorem psi_glAct (L L' : Letters N) (j0 j : ℕ) (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    psi p L j0 (glAct p L' j c d x) = glAct p L' j c d (psi p L j0 x) :=
  whc_comm _ _ (fun D x hx => glAct_wL L' j c d hx) _ x

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

/- English proof (translation)
Introduce `c d x hx`. Take `⟨hxP, hxY⟩` from `Submodule.mem_inf.mp hx`. Use `Submodule.mem_inf.mpr ⟨pol_stable L (Lz L j0) j0 c d x hxP, (Submodule.mem_iInf _).mpr fun k => ?_⟩` and prove the remaining obligations. Establish `h1` using `(Submodule.mem_iInf _).mp hxY k`. Distinguish the cases in `hk : J k < j0`.

Rewrite `h1`, the goal using `[Mup, if_pos hk]`. Conclude with `ycond_glAct_le L (le_of_lt hk) (M k) c d h1`. Rewrite using `[Mup, if_neg hk, Formalism.GM.DimensionMonotonicity.ycond_top]`. Conclude with `Submodule.mem_top`.
-/
theorem C_stable [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) :
    (GA p (r := r) L j0).Stable (Cset p L j0 J M) := by
  intro c d x hx
  obtain ⟨hxP, hxY⟩ := Submodule.mem_inf.mp hx
  refine Submodule.mem_inf.mpr ⟨pol_stable L (Lz L j0) j0 c d x hxP, (Submodule.mem_iInf _).mpr fun k => ?_⟩
  have h1 := (Submodule.mem_iInf _).mp hxY k
  by_cases hk : J k < j0
  · rw [Mup, if_pos hk] at h1 ⊢
    exact ycond_glAct_le L (le_of_lt hk) (M k) c d h1
  · rw [Mup, if_neg hk, Formalism.GM.DimensionMonotonicity.ycond_top]; exact Submodule.mem_top

/- English proof (translation)
The claim follows from `pol_finW (Lz L j0) j0`.
-/
theorem polynomial_finite_weights (L : Letters N) (j0 : ℕ) : (GA p L j0).FinW (Pol p r (Lz L j0)) :=
  pol_finW (Lz L j0) j0

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM.DimensionMonotonicity Finset

namespace GlX

variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

/- English proof (translation)
Simplify using `[Lv, act]`.
-/
theorem Lv_single_nil (v : V) : Lv G v (Finsupp.single [] 1) = v := by
  simp [Lv, act]

/- English proof (translation)
Use `first`. Consider the case `simp [Lv, Finsupp.linearCombination_apply]`. Consider the case `simp [Lv]`.
-/
theorem Lv_zero (c : List (Fin r × Fin r) →₀ K) : Lv G (0 : V) c = 0 := by
  first
    | simp [Lv, Finsupp.linearCombination_apply]
    | simp [Lv]

/- English proof (translation)
Establish `h0 : ∀ i, h i ≠ 0` using `fun i => hli.ne_zero i`. Establish `hk : ∀ i, LinearMap.ker (Lv G (h i)) ≤ LinearMap.ker (Lv G (g i))` using `fun i => ker_le G hW hWf (hh i) (hg i) (hhW i) (hgW i) (h0 i)`. Take `⟨S, hS⟩` from `hWf`. Establish `hind` using `indep_hw G hW hS h la hh hhW hli`. Establish `hRW : ∀ i, G.gS {h i} ≤ W` using `fun i => G.gS_le (by simpa using hhW i) hW`.

Take `⟨π, hπ1, hπ2, hπ3⟩` from `proj_exists (fun i => G.gS {h i}) hind hRW hsp`. Establish `hπr : ∀ i x, π i x ∈ LinearMap.range (Lv G (h i))` using `fun i x => by rw [range_Lv]; exact hπ1 i x`. Use `⟨∑ i, tr G (hk i) ∘ₗ (π i).codRestrict (LinearMap.range (Lv G (h i))) (hπr i), fun i c => ?_⟩` and prove the remaining obligations. Establish `hmem : Lv G (h i) c ∈ G.gS {h i}` using `by rw [← range_Lv]; exact LinearMap.mem_range_self _ c`. Rewrite using `[LinearMap.sum_apply, Finset.sum_eq_single i]`.

Rewrite using `[LinearMap.comp_apply]`. Establish `e : (π i).codRestrict (LinearMap.range (Lv G (h i))) (hπr i) (Lv G (h i) c) = ⟨Lv G (h i) c, LinearMap.mem_range_self _ c⟩` using `by ext; exact hπ2 i _ hmem`. Rewrite using `[e, tr_apply]`. Introduce `j _ hji`. Rewrite using `[LinearMap.comp_apply]`.

Establish `e : (π j).codRestrict (LinearMap.range (Lv G (h j))) (hπr j) (Lv G (h i) c) = 0` using `by ext; exact hπ3 j i (Ne.symm hji) _ hmem`. Rewrite using `[e, map_zero]`. Introduce `hi`. Conclude with `absurd (Finset.mem_univ i) hi`.
-/
theorem eqExt_core {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {ι : Type} [Fintype ι] [DecidableEq ι]
    (h g : ι → V) (la : ι → Fin r → ℤ) (hh : ∀ i, G.IsHW (la i) (h i)) (hhW : ∀ i, h i ∈ W)
    (hli : LinearIndependent K h) (hsp : W ≤ ⨆ i, G.gS {h i})
    (hg : ∀ i, G.IsHW (la i) (g i)) (hgW : ∀ i, g i ∈ W) :
    ∃ φ : V →ₗ[K] V, ∀ i c, φ (Lv G (h i) c) = Lv G (g i) c := by
  have h0 : ∀ i, h i ≠ 0 := fun i => hli.ne_zero i
  have hk : ∀ i, LinearMap.ker (Lv G (h i)) ≤ LinearMap.ker (Lv G (g i)) := fun i =>
    ker_le G hW hWf (hh i) (hg i) (hhW i) (hgW i) (h0 i)
  obtain ⟨S, hS⟩ := hWf
  have hind := indep_hw G hW hS h la hh hhW hli
  have hRW : ∀ i, G.gS {h i} ≤ W := fun i => G.gS_le (by simpa using hhW i) hW
  obtain ⟨π, hπ1, hπ2, hπ3⟩ := proj_exists (fun i => G.gS {h i}) hind hRW hsp
  have hπr : ∀ i x, π i x ∈ LinearMap.range (Lv G (h i)) := fun i x => by rw [range_Lv]; exact hπ1 i x
  refine ⟨∑ i, tr G (hk i) ∘ₗ (π i).codRestrict (LinearMap.range (Lv G (h i))) (hπr i), fun i c => ?_⟩
  have hmem : Lv G (h i) c ∈ G.gS {h i} := by rw [← range_Lv]; exact LinearMap.mem_range_self _ c
  rw [LinearMap.sum_apply, Finset.sum_eq_single i]
  · rw [LinearMap.comp_apply]
    have e : (π i).codRestrict (LinearMap.range (Lv G (h i))) (hπr i) (Lv G (h i) c) =
        ⟨Lv G (h i) c, LinearMap.mem_range_self _ c⟩ := by
      ext; exact hπ2 i _ hmem
    rw [e, tr_apply]
  · intro j _ hji
    rw [LinearMap.comp_apply]
    have e : (π j).codRestrict (LinearMap.range (Lv G (h j))) (hπr j) (Lv G (h i) c) = 0 := by
      ext; exact hπ3 j i (Ne.symm hji) _ hmem
    rw [e, map_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/- English proof (translation)
Take `⟨φ, hφ⟩` from `eqExt_core G hW hWf h g la hh hhW hli hsp hg hgW`. Establish `hrep : ∀ i, ∀ x ∈ G.gS {h i}, ∃ c, x = Lv G (h i) c`. Introduce `i x hx`. Rewrite `hx` using `[← range_Lv]`. Take `⟨c, rfl⟩` from `hx`.

Conclude with `⟨c, rfl⟩`. Establish `hgS : ∀ i c, Lv G (g i) c ∈ G.gS {g i}` using `fun i c => by`. Rewrite using `[← range_Lv]`. Conclude with `LinearMap.mem_range_self _ c`. Use `⟨φ, fun i => ?_, fun x hx a b => ?_, fun x hx => ?_, fun i x hx => ?_, fun i hgi x hx hx0 => ?_, fun i hgi x hx => ?_, fun i hgi x hx => ?_⟩` and prove the remaining obligations.

Use `hφ i (Finsupp.single [] 1)` as an intermediate fact. Rewrite `this` using `[Lv_single_nil, Lv_single_nil]`. Then use the resulting hypothesis. Use `Submodule.iSup_induction (fun i => G.gS {h i}) (motive := fun x => φ (G.E a b x) = G.E a b (φ x)) (hsp hx) (fun j y hy => ?_) (by simp) (fun x y hx hy => by simp only [map_add, hx, hy])` and prove the remaining obligations. Take `⟨c, rfl⟩` from `hrep j y hy`. Rewrite using `[E_Lv, hφ, hφ, E_Lv]`.

Use `Submodule.iSup_induction (fun i => G.gS {h i}) (motive := fun x => φ x ∈ W) (hsp hx) (fun j y hy => ?_) (by simp) (fun x y hx hy => by rw [map_add]; exact W.add_mem hx hy)` and prove the remaining obligations. Take `⟨c, rfl⟩` from `hrep j y hy`. Rewrite using `[hφ]`. Conclude with `(G.gS_le (by simpa using hgW j) hW) (hgS j c)`. Take `⟨c, rfl⟩` from `hrep i x hx`.

Rewrite using `[hφ]`. Conclude with `hgS i c`. Take `⟨c, rfl⟩` from `hrep i x hx`. Rewrite `hx0` using `[hφ]`. Conclude with `LinearMap.mem_ker.mp (ker_le G hW hWf (hg i) (hh i) (hgW i) (hhW i) hgi (LinearMap.mem_ker.mpr hx0))`.

Take `⟨c, rfl⟩` from `hrep i x hx`. Rewrite using `[hφ, hgi]`. Take `⟨c, rfl⟩` from `hrep i x hx`. Rewrite using `[hφ, hgi, Lv_zero]`.
-/
theorem eqExt {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {ι : Type} [Fintype ι] [DecidableEq ι]
    (h g : ι → V) (la : ι → Fin r → ℤ) (hh : ∀ i, G.IsHW (la i) (h i)) (hhW : ∀ i, h i ∈ W)
    (hli : LinearIndependent K h) (hsp : W ≤ ⨆ i, G.gS {h i})
    (hg : ∀ i, G.IsHW (la i) (g i)) (hgW : ∀ i, g i ∈ W) :
    ∃ φ : V →ₗ[K] V, (∀ i, φ (h i) = g i) ∧ (∀ x ∈ W, ∀ a b, φ (G.E a b x) = G.E a b (φ x)) ∧
      (∀ x ∈ W, φ x ∈ W) ∧ (∀ i, ∀ x ∈ G.gS {h i}, φ x ∈ G.gS {g i}) ∧
      (∀ i, g i ≠ 0 → ∀ x ∈ G.gS {h i}, φ x = 0 → x = 0) ∧
      (∀ i, g i = h i → ∀ x ∈ G.gS {h i}, φ x = x) ∧ (∀ i, g i = 0 → ∀ x ∈ G.gS {h i}, φ x = 0) := by
  obtain ⟨φ, hφ⟩ := eqExt_core G hW hWf h g la hh hhW hli hsp hg hgW
  have hrep : ∀ i, ∀ x ∈ G.gS {h i}, ∃ c, x = Lv G (h i) c := by
    intro i x hx
    rw [← range_Lv] at hx
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, rfl⟩
  have hgS : ∀ i c, Lv G (g i) c ∈ G.gS {g i} := fun i c => by
    rw [← range_Lv]; exact LinearMap.mem_range_self _ c
  refine ⟨φ, fun i => ?_, fun x hx a b => ?_, fun x hx => ?_, fun i x hx => ?_, fun i hgi x hx hx0 => ?_,
    fun i hgi x hx => ?_, fun i hgi x hx => ?_⟩
  · have := hφ i (Finsupp.single [] 1)
    rwa [Lv_single_nil, Lv_single_nil] at this
  · refine Submodule.iSup_induction (fun i => G.gS {h i}) (motive := fun x => φ (G.E a b x) = G.E a b (φ x))
      (hsp hx) (fun j y hy => ?_) (by simp) (fun x y hx hy => by simp only [map_add, hx, hy])
    obtain ⟨c, rfl⟩ := hrep j y hy
    rw [E_Lv, hφ, hφ, E_Lv]
  · refine Submodule.iSup_induction (fun i => G.gS {h i}) (motive := fun x => φ x ∈ W)
      (hsp hx) (fun j y hy => ?_) (by simp) (fun x y hx hy => by rw [map_add]; exact W.add_mem hx hy)
    obtain ⟨c, rfl⟩ := hrep j y hy
    rw [hφ]
    exact (G.gS_le (by simpa using hgW j) hW) (hgS j c)
  · obtain ⟨c, rfl⟩ := hrep i x hx
    rw [hφ]; exact hgS i c
  · obtain ⟨c, rfl⟩ := hrep i x hx
    rw [hφ] at hx0
    exact LinearMap.mem_ker.mp (ker_le G hW hWf (hg i) (hh i) (hgW i) (hhW i) hgi (LinearMap.mem_ker.mpr hx0))
  · obtain ⟨c, rfl⟩ := hrep i x hx
    rw [hφ, hgi]
  · obtain ⟨c, rfl⟩ := hrep i x hx
    rw [hφ, hgi, Lv_zero]

/- English proof (translation)
Establish `h1 : ∀ i j, B (h i) (h j) = 0`. Introduce `i j`. Distinguish the cases in `hij : la i = la j`. Conclude with `h0 i j hij`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c, la i c ≠ la j c := by`.

Assume the negation of the conclusion as `hcon; exact hij (funext fun c => by by_contra hc; exact hcon ⟨c, hc⟩)`. Establish `e` using `hB (h i) (hhW i) (h j) (hhW j) c c`. Rewrite `e` using `[G.E_diag_of_isWt (hh i).1, G.E_diag_of_isWt (hh j).1, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]`. Establish `e2 : (((la i c : ℤ) : K) - ((la j c : ℤ) : K)) * B (h i) (h j) = 0` using `by rw [sub_mul, e, sub_self]`. Break down `mul_eq_zero.mp e2 with h3 | h3` into its components or cases.

It suffices to derive a contradiction. Apply `hc` to reduce the goal to its premises. Establish `: ((la i c : ℤ) : K) = ((la j c : ℤ) : K)` using `sub_eq_zero.mp h3`. Conclude with `this` after adjusting the coercions. Conclude with `h3`.

Establish `h2 : ∀ i, ∀ y ∈ W, B (h i) y = 0`. Introduce `i y hy`. Establish `hle : ∀ j, G.gS {h j} ≤ W ⊓ LinearMap.ker (B (h i))`. Introduce `j`. Use `(G.gS_le_Lw (hh j)).trans (G.Lw_le (h j) ⟨hhW j, LinearMap.mem_ker.mpr (h1 i j)⟩ ?_)` and prove the remaining obligations.

Introduce `a b hba x hx`. Use `⟨hW a b x hx.1, LinearMap.mem_ker.mpr ?_⟩` and prove the remaining obligations. Rewrite using `[← hB (h i) (hhW i) x hx.1 b a, (hh i).2 b a hba, map_zero, LinearMap.zero_apply]`. Conclude with `LinearMap.mem_ker.mp ((iSup_le hle) (hsp hy)).2`. Set `U : Submodule K V` to `{ carrier := {x | x ∈ W ∧ ∀ y ∈ W, B x y = 0} add_mem' := fun {x x'} hx hx' => ⟨W.add_mem hx.1 hx'.1, fun y hy => by`.

Rewrite using `[map_add, LinearMap.add_apply, hx.2 y hy, hx'.2 y hy, add_zero]⟩`. Use the proof step `zero_mem' := ⟨W.zero_mem, fun y _ => by rw [map_zero, LinearMap.zero_apply]⟩`. Use the proof step `smul_mem' := fun t x hx => ⟨W.smul_mem t hx.1, fun y hy => by`. Rewrite using `[map_smul, LinearMap.smul_apply, hx.2 y hy, smul_zero]⟩ }`. Establish `hU : G.Stable U` using `fun a b x hx => ⟨hW a b x hx.1, fun y hy => by`.

Rewrite using `[hB x hx.1 y hy a b]`. Conclude with `hx.2 _ (hW b a y hy)⟩`. Establish `hle : ∀ i, G.gS {h i} ≤ U` using `fun i => G.gS_le (by intro z hz; rw [Set.mem_singleton_iff] at hz; subst hz; exact ⟨hhW i, h2 i⟩) hU`. Introduce `x hx y hy`. Conclude with `((iSup_le hle) (hsp hx)).2 y hy`.
-/
theorem form_zero {W : Submodule K V} (hW : G.Stable W) {ι : Type} (h : ι → V) (la : ι → Fin r → ℤ)
    (hh : ∀ i, G.IsHW (la i) (h i)) (hhW : ∀ i, h i ∈ W) (hsp : W ≤ ⨆ i, G.gS {h i})
    (B : V →ₗ[K] V →ₗ[K] K) (hB : ∀ x ∈ W, ∀ y ∈ W, ∀ a b, B (G.E a b x) y = B x (G.E b a y))
    (h0 : ∀ i j, la i = la j → B (h i) (h j) = 0) : ∀ x ∈ W, ∀ y ∈ W, B x y = 0 := by

  have h1 : ∀ i j, B (h i) (h j) = 0 := by
    intro i j
    by_cases hij : la i = la j
    · exact h0 i j hij
    · obtain ⟨c, hc⟩ : ∃ c, la i c ≠ la j c := by
        by_contra hcon; exact hij (funext fun c => by by_contra hc; exact hcon ⟨c, hc⟩)
      have e := hB (h i) (hhW i) (h j) (hhW j) c c
      rw [G.E_diag_of_isWt (hh i).1, G.E_diag_of_isWt (hh j).1, map_smul, map_smul, LinearMap.smul_apply,
        smul_eq_mul, smul_eq_mul] at e
      have e2 : (((la i c : ℤ) : K) - ((la j c : ℤ) : K)) * B (h i) (h j) = 0 := by rw [sub_mul, e, sub_self]
      rcases mul_eq_zero.mp e2 with h3 | h3
      · exfalso; apply hc
        have : ((la i c : ℤ) : K) = ((la j c : ℤ) : K) := sub_eq_zero.mp h3
        exact_mod_cast this
      · exact h3

  have h2 : ∀ i, ∀ y ∈ W, B (h i) y = 0 := by
    intro i y hy
    have hle : ∀ j, G.gS {h j} ≤ W ⊓ LinearMap.ker (B (h i)) := by
      intro j
      refine (G.gS_le_Lw (hh j)).trans (G.Lw_le (h j) ⟨hhW j, LinearMap.mem_ker.mpr (h1 i j)⟩ ?_)
      intro a b hba x hx
      refine ⟨hW a b x hx.1, LinearMap.mem_ker.mpr ?_⟩
      rw [← hB (h i) (hhW i) x hx.1 b a, (hh i).2 b a hba, map_zero, LinearMap.zero_apply]
    exact LinearMap.mem_ker.mp ((iSup_le hle) (hsp hy)).2

  let U : Submodule K V :=
    { carrier := {x | x ∈ W ∧ ∀ y ∈ W, B x y = 0}
      add_mem' := fun {x x'} hx hx' => ⟨W.add_mem hx.1 hx'.1, fun y hy => by
        rw [map_add, LinearMap.add_apply, hx.2 y hy, hx'.2 y hy, add_zero]⟩
      zero_mem' := ⟨W.zero_mem, fun y _ => by rw [map_zero, LinearMap.zero_apply]⟩
      smul_mem' := fun t x hx => ⟨W.smul_mem t hx.1, fun y hy => by
        rw [map_smul, LinearMap.smul_apply, hx.2 y hy, smul_zero]⟩ }
  have hU : G.Stable U := fun a b x hx => ⟨hW a b x hx.1, fun y hy => by
    rw [hB x hx.1 y hy a b]; exact hx.2 _ (hW b a y hy)⟩
  have hle : ∀ i, G.gS {h i} ≤ U := fun i =>
    G.gS_le (by intro z hz; rw [Set.mem_singleton_iff] at hz; subst hz; exact ⟨hhW i, h2 i⟩) hU
  intro x hx y hy
  exact ((iSup_le hle) (hsp hx)).2 y hy

end GlX

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

/- English proof (translation)
Use `show weightedHomogeneousComponent (wv L j) la x = x ↔ _`. Rewrite using `[WtSpC, mem_restrictSupport_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h m hm c _`. Establish `hw : IsWeightedHomogeneous (wv L j) x la`.

Rewrite using `[← h]`. Conclude with `weightedHomogeneousComponent_isWeightedHomogeneous la x`. Rewrite using `[← weight_wv, hw (mem_support_iff.mp (Finset.mem_coe.mp hm))]`. Introduce `h`. Apply `weightedHomogeneousComponent_eq_self` to reduce the goal to its premises.

Introduce `m hm`. Use function extensionality and compare the values at `c`. Rewrite using `[weight_wv]`. Conclude with `h (Finset.mem_coe.mpr (mem_support_iff.mpr hm)) c (mem_univ c)`.
-/
theorem isWt_iff (L : Letters N) (j : ℕ) (la : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    (GA p L j).IsWt la x ↔ x ∈ WtSpC p L j univ la := by
  show weightedHomogeneousComponent (wv L j) la x = x ↔ _
  rw [WtSpC, mem_restrictSupport_iff]
  constructor
  · intro h m hm c _
    have hw : IsWeightedHomogeneous (wv L j) x la := by
      rw [← h]; exact weightedHomogeneousComponent_isWeightedHomogeneous la x
    rw [← weight_wv, hw (mem_support_iff.mp (Finset.mem_coe.mp hm))]
  · intro h
    apply weightedHomogeneousComponent_eq_self
    intro m hm
    funext c
    rw [weight_wv]
    exact h (Finset.mem_coe.mpr (mem_support_iff.mpr hm)) c (mem_univ c)

/- English proof (translation)
Unfold `GlW.IsHW HWC`. Rewrite using `[isWt_iff, Submodule.mem_inf]`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨h1, fun c d hcd => h2 c d hcd.2.2⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨h1, fun a b hab => h2 a b ⟨mem_univ _, mem_univ _, hab⟩⟩`.
-/
theorem isHW_iff (L : Letters N) (j : ℕ) (la : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    (GA p L j).IsHW la x ↔ x ∈ HWC p L j univ la := by
  unfold GlW.IsHW HWC
  rw [isWt_iff, Submodule.mem_inf]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun c d hcd => h2 c d hcd.2.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a b hab => h2 a b ⟨mem_univ _, mem_univ _, hab⟩⟩

noncomputable def fockB (p : ℕ) [Fact p.Prime] (σ : Type) [Fintype σ] [DecidableEq σ] :
    MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p] :=
  LinearMap.mk₂ ℚ_[p] (fun F G => fock p F G)
    (fun F F' G => gammaIntegralityLemmas.fock_add_left F F' G)
    (fun c F G => by rw [gammaIntegralityLemmas.fock_smul_left, smul_eq_mul])
    (fun F G G' => by
      rw [gammaIntegralityLemmas.fock_symm F (G + G'), gammaIntegralityLemmas.fock_add_left, gammaIntegralityLemmas.fock_symm G F, gammaIntegralityLemmas.fock_symm G' F])
    (fun c F G => by rw [gammaIntegralityLemmas.fock_smul_right, smul_eq_mul])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fockB_apply {σ : Type} [Fintype σ] [DecidableEq σ] (F G : MvPolynomial σ ℚ_[p]) :
    fockB p σ F G = fock p F G := rfl

/- English proof (translation)
Rewrite using `[gammaIntegralityLemmas.fock_X_mul, gammaIntegralityLemmas.fock_symm, ← gammaIntegralityLemmas.fock_X_mul, gammaIntegralityLemmas.fock_symm]`.
-/
theorem fock_XD {σ : Type} [Fintype σ] [DecidableEq σ] (u v : σ) (x y : MvPolynomial σ ℚ_[p]) :
    fock p (X u * pderiv v x) y = fock p x (X v * pderiv u y) := by
  rw [gammaIntegralityLemmas.fock_X_mul, gammaIntegralityLemmas.fock_symm, ← gammaIntegralityLemmas.fock_X_mul, gammaIntegralityLemmas.fock_symm]

/- English proof (translation)
Simplify using `only [glAct, LinearMap.sum_apply]`. Rewrite using `[gammaIntegralityLemmas.fock_sum_left, gammaIntegralityLemmas.fock_sum_right]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← fockB_apply, ← fockB_apply]`. Use `split_ifs with h1 h2`.

Simplify using `only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, fockB_apply]`. Conclude with `fock_XD _ _ _ _`. Simplify using `only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, map_neg, fockB_apply]`. Conclude with `congrArg Neg.neg (fock_XD _ _ _ _)`. Simplify using the standard rewrite rules.
-/
theorem fock_glAct (L : Letters N) (j : ℕ) (c d : Fin r) (x y : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    fock p (glAct p L j c d x) y = fock p x (glAct p L j d c y) := by
  simp only [glAct, LinearMap.sum_apply]
  rw [gammaIntegralityLemmas.fock_sum_left, gammaIntegralityLemmas.fock_sum_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← fockB_apply, ← fockB_apply]
  split_ifs with h1 h2
  · simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, fockB_apply]
    exact fock_XD _ _ _ _
  · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe,
      map_neg, fockB_apply]
    exact congrArg Neg.neg (fock_XD _ _ _ _)
  · simp

/- English proof (translation)
Unfold `gammaIntegralityLemmas.wf`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Distinguish the cases in `hv : a v = 0`. Simplify using `[hv]`.

Establish `: m v = 0`. Assume the negation of the conclusion as `h`. Conclude with `hm v h (ha v hv)`. Simplify using `[this]`.
-/
theorem wf_add_disj (j0 : ℕ) (a m : Fin N × Fin r →₀ ℕ) (ha : ∀ v, a v ≠ 0 → fsj N r j0 v)
    (hm : ∀ v, m v ≠ 0 → ¬ fsj N r j0 v) :
    gammaIntegralityLemmas.wf (p := p) (a + m) = gammaIntegralityLemmas.wf a * gammaIntegralityLemmas.wf m := by
  unfold gammaIntegralityLemmas.wf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hv : a v = 0
  · simp [hv]
  · have : m v = 0 := by
      by_contra h
      exact hm v h (ha v hv)
    simp [this]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1` using `congrArg (frst (fsj N r j0)) h`. Establish `h2` using `congrArg (ltr (fsj N r j0)) h`. Rewrite `h1` using `[frst_add, frst_add, frst_of _ ha, frst_of _ hb, frst_of' _ hm, frst_of' _ hm', add_zero, add_zero]`.

Rewrite `h2` using `[ltr_add, ltr_add, ltr_of _ ha, ltr_of _ hb, ltr_of' _ hm, ltr_of' _ hm', zero_add, zero_add]`. Conclude with `⟨h1, h2⟩`. Introduce and unpack `⟨rfl, rfl⟩`. Both sides reduce to the same expression.
-/
theorem add_eq_add_iff_disj (j0 : ℕ) (a b m m' : Fin N × Fin r →₀ ℕ) (ha : ∀ v, a v ≠ 0 → fsj N r j0 v)
    (hb : ∀ v, b v ≠ 0 → fsj N r j0 v) (hm : ∀ v, m v ≠ 0 → ¬ fsj N r j0 v)
    (hm' : ∀ v, m' v ≠ 0 → ¬ fsj N r j0 v) : a + m = b + m' ↔ a = b ∧ m = m' := by
  constructor
  · intro h
    have h1 := congrArg (frst (fsj N r j0)) h
    have h2 := congrArg (ltr (fsj N r j0)) h
    rw [frst_add, frst_add, frst_of _ ha, frst_of _ hb, frst_of' _ hm, frst_of' _ hm', add_zero, add_zero] at h1
    rw [ltr_add, ltr_add, ltr_of _ ha, ltr_of _ hb, ltr_of' _ hm, ltr_of' _ hm', zero_add, zero_add] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/- English proof (translation)
Rewrite using `[Finset.sum_mul, Finset.sum_mul, gammaIntegralityLemmas.fock_sum_left, gammaIntegralityLemmas.fock_sum_left, gammaIntegralityLemmas.prod_eq_wf]`. Simplify using `only [gammaIntegralityLemmas.fock_sum_right, monomial_mul, mul_one, gammaIntegralityLemmas.fock_monomial]`. Distinguish the cases in `hmm : m = m'`. Rewrite using `[if_pos hmm, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun b hb => ?_` and prove the remaining obligations. Distinguish the cases in `hab : a = b`. Rewrite using `[if_pos hab, if_pos (by rw [hab, hmm]), wf_add_disj j0 a m (hs a ha) hm]; ring`. Rewrite using `[if_neg hab, if_neg (fun h => hab ((add_eq_add_iff_disj j0 a b m m' (hs a ha) (ht b hb) hm hm').mp h).1), zero_mul]`.

Rewrite using `[if_neg hmm]`. Use `Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_` and prove the remaining obligations. Rewrite using `[if_neg (fun h => hmm ((add_eq_add_iff_disj j0 a b m m' (hs a ha) (ht b hb) hm hm').mp h).2)]`.
-/
theorem fock_mul_monomial_orthogonal (j0 : ℕ) (s t : Finset (Fin N × Fin r →₀ ℕ)) (cg cg' : (Fin N × Fin r →₀ ℕ) → ℚ_[p])
    (hs : ∀ a ∈ s, ∀ v, a v ≠ 0 → fsj N r j0 v) (ht : ∀ b ∈ t, ∀ v, b v ≠ 0 → fsj N r j0 v)
    (m m' : Fin N × Fin r →₀ ℕ) (hm : ∀ v, m v ≠ 0 → ¬ fsj N r j0 v)
    (hm' : ∀ v, m' v ≠ 0 → ¬ fsj N r j0 v) :
    fock p ((∑ a ∈ s, monomial a (cg a)) * monomial m 1) ((∑ b ∈ t, monomial b (cg' b)) * monomial m' 1) =
      if m = m' then fock p (∑ a ∈ s, monomial a (cg a)) (∑ b ∈ t, monomial b (cg' b)) *
        (m.prod fun _ k => (k.factorial : ℚ_[p])) else 0 := by
  rw [Finset.sum_mul, Finset.sum_mul, gammaIntegralityLemmas.fock_sum_left, gammaIntegralityLemmas.fock_sum_left, gammaIntegralityLemmas.prod_eq_wf]
  simp only [gammaIntegralityLemmas.fock_sum_right, monomial_mul, mul_one, gammaIntegralityLemmas.fock_monomial]
  by_cases hmm : m = m'
  · rw [if_pos hmm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b hb => ?_
    by_cases hab : a = b
    · rw [if_pos hab, if_pos (by rw [hab, hmm]), wf_add_disj j0 a m (hs a ha) hm]; ring
    · rw [if_neg hab, if_neg (fun h => hab ((add_eq_add_iff_disj j0 a b m m' (hs a ha) (ht b hb) hm hm').mp h).1),
        zero_mul]
  · rw [if_neg hmm]
    refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
    rw [if_neg (fun h => hmm ((add_eq_add_iff_disj j0 a b m m' (hs a ha) (ht b hb) hm hm').mp h).2)]

/- English proof (translation)
Use `fock_mul_monomial_orthogonal j0 g.support g'.support (fun a => coeff a g) (fun b => coeff b g') (fun a ha => hg a ha) (fun b hb => hg' b hb) m m' hm hm'` as an intermediate fact. Rewrite `this` using `[← g.as_sum, ← g'.as_sum]`. Then use the resulting hypothesis.
-/
theorem fock_mul_mono (j0 : ℕ) {g g' : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hg : IsF (fsj N r j0) g)
    (hg' : IsF (fsj N r j0) g') (m m' : Fin N × Fin r →₀ ℕ) (hm : ∀ v, m v ≠ 0 → ¬ fsj N r j0 v)
    (hm' : ∀ v, m' v ≠ 0 → ¬ fsj N r j0 v) :
    fock p (g * monomial m 1) (g' * monomial m' 1) =
      if m = m' then fock p g g' * (m.prod fun _ k => (k.factorial : ℚ_[p])) else 0 := by
  have := fock_mul_monomial_orthogonal j0 g.support g'.support (fun a => coeff a g) (fun b => coeff b g')
    (fun a ha => hg a ha) (fun b hb => hg' b hb) m m' hm hm'
  rwa [← g.as_sum, ← g'.as_sum] at this

/- English proof (translation)
Use `set S : Finset (Fin N × Fin r →₀ ℕ) := (u.support ∪ u'.support).image (ltr (fsj N r j0)) with hS`. Establish `hSu : ∀ m ∈ u.support, ltr (fsj N r j0) m ∈ S` using `fun m hm => Finset.mem_image_of_mem _ (Finset.mem_union_left _ hm)`. Establish `hSu' : ∀ m ∈ u'.support, ltr (fsj N r j0) m ∈ S` using `fun m hm => Finset.mem_image_of_mem _ (Finset.mem_union_right _ hm)`. Establish `hSl : ∀ m ∈ S, ∀ v, m v ≠ 0 → ¬ fsj N r j0 v`. Introduce `m hm`.

Take `⟨m0, _, rfl⟩` from `Finset.mem_image.mp hm`. Conclude with `ltr_isL _ m0`. Establish `hSL : ∀ m ∈ S, IsL (fsj N r j0) (monomial m (1 : ℚ_[p]))`. Introduce `m hm`. Take `⟨m0, _, rfl⟩` from `Finset.mem_image.mp hm`.

Conclude with `isL_monomial_ltr _ m0 1`. Establish `hAu : A u = ∑ m ∈ S, A (slc (fsj N r j0) m u) * monomial m 1` using `by conv_lhs => rw [eq_sum_sl (fsj N r j0) u S hSu]`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun m hm => hA _ _ (hSL m hm)`. Rewrite using `[hAu, ext_eq_sum (fsj N r j0) φ1 u' S hSu', ext_eq_sum (fsj N r j0) φ2 u S hSu]`.

Use `conv_rhs => rw [eq_sum_sl (fsj N r j0) u' S hSu']`. Rewrite using `[gammaIntegralityLemmas.fock_sum_left, gammaIntegralityLemmas.fock_sum_left, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[gammaIntegralityLemmas.fock_sum_right, gammaIntegralityLemmas.fock_sum_right, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m' hm' => ?_` and prove the remaining obligations.

Rewrite using `[fock_mul_mono j0 (hAF _ (sl_isF _ m u)) (h1 _) m m' (hSl m hm) (hSl m' hm'), fock_mul_mono j0 (h2 _) (sl_isF _ m' u') m m' (hSl m hm) (hSl m' hm')]`. Use `split_ifs with h`. Rewrite using `[hcore _ (hu m) _ (hu' m')]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem fock_ext_reduce (j0 : ℕ)
    (A φ1 φ2 : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) (c : ℚ_[p])
    (Cs : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hA : ∀ g q, IsL (fsj N r j0) q → A (g * q) = A g * q)
    (hAF : ∀ g, IsF (fsj N r j0) g → IsF (fsj N r j0) (A g))
    (h1 : ∀ x, IsF (fsj N r j0) (φ1 x)) (h2 : ∀ x, IsF (fsj N r j0) (φ2 x))
    (hcore : ∀ g ∈ Cs, ∀ g' ∈ Cs, fock p (A g) (φ1 g') = c * fock p (φ2 g) g')
    (u u' : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hu : ∀ m, slc (fsj N r j0) m u ∈ Cs)
    (hu' : ∀ m, slc (fsj N r j0) m u' ∈ Cs) :
    fock p (A u) (ext (fsj N r j0) φ1 u') = c * fock p (ext (fsj N r j0) φ2 u) u' := by
  classical
  set S : Finset (Fin N × Fin r →₀ ℕ) := (u.support ∪ u'.support).image (ltr (fsj N r j0)) with hS
  have hSu : ∀ m ∈ u.support, ltr (fsj N r j0) m ∈ S := fun m hm =>
    Finset.mem_image_of_mem _ (Finset.mem_union_left _ hm)
  have hSu' : ∀ m ∈ u'.support, ltr (fsj N r j0) m ∈ S := fun m hm =>
    Finset.mem_image_of_mem _ (Finset.mem_union_right _ hm)
  have hSl : ∀ m ∈ S, ∀ v, m v ≠ 0 → ¬ fsj N r j0 v := by
    intro m hm
    obtain ⟨m0, _, rfl⟩ := Finset.mem_image.mp hm
    exact ltr_isL _ m0
  have hSL : ∀ m ∈ S, IsL (fsj N r j0) (monomial m (1 : ℚ_[p])) := by
    intro m hm
    obtain ⟨m0, _, rfl⟩ := Finset.mem_image.mp hm
    exact isL_monomial_ltr _ m0 1
  have hAu : A u = ∑ m ∈ S, A (slc (fsj N r j0) m u) * monomial m 1 := by
    conv_lhs => rw [eq_sum_sl (fsj N r j0) u S hSu]
    rw [map_sum]
    exact Finset.sum_congr rfl fun m hm => hA _ _ (hSL m hm)
  rw [hAu, ext_eq_sum (fsj N r j0) φ1 u' S hSu', ext_eq_sum (fsj N r j0) φ2 u S hSu]
  conv_rhs => rw [eq_sum_sl (fsj N r j0) u' S hSu']
  rw [gammaIntegralityLemmas.fock_sum_left, gammaIntegralityLemmas.fock_sum_left, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [gammaIntegralityLemmas.fock_sum_right, gammaIntegralityLemmas.fock_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m' hm' => ?_
  rw [fock_mul_mono j0 (hAF _ (sl_isF _ m u)) (h1 _) m m' (hSl m hm) (hSl m' hm'),
    fock_mul_mono j0 (h2 _) (sl_isF _ m' u') m m' (hSl m hm) (hSl m' hm')]
  split_ifs with h
  · rw [hcore _ (hu m) _ (hu' m')]; ring
  · simp

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

section OpsAux

variable {k σ : Type} [Field k]

/- English proof (translation)
Unfold `Formalism.GM.tiePhi`. Use `sum_mem fun j _ => Subalgebra.smul_mem _ ?_ _` and prove the remaining obligations. Rewrite using `[← Module.End.mul_eq_comp]`. Use `mul_mem (pow_mem ?_ _) (pow_mem ?_ _)` and prove the remaining obligations. Conclude with `FockB.mulLeft_mem (sum_mem fun c _ => mul_mem (FockB.X_mem (Or.inl ⟨c, rfl⟩)) (FockB.X_mem (Or.inr ⟨c, rfl⟩)))`.

Unfold `Formalism.GM.tieF`. Use `sum_mem fun c _ => ?_` and prove the remaining obligations. Rewrite using `[← Module.End.mul_eq_comp]`. Conclude with `mul_mem (FockB.pderiv_mem (Or.inl ⟨c, rfl⟩)) (FockB.pderiv_mem (Or.inr ⟨c, rfl⟩))`.
-/
theorem tiePhi_mem' {r : ℕ} (w e : Fin r → σ) (o n z : ℕ) :
    (Formalism.GM.tiePhi w e o n z : Module.End k (MvPolynomial σ k)) ∈ FockB.Ops (Set.range w ∪ Set.range e) := by
  unfold Formalism.GM.tiePhi
  refine sum_mem fun j _ => Subalgebra.smul_mem _ ?_ _
  rw [← Module.End.mul_eq_comp]
  refine mul_mem (pow_mem ?_ _) (pow_mem ?_ _)
  · exact FockB.mulLeft_mem (sum_mem fun c _ => mul_mem (FockB.X_mem (Or.inl ⟨c, rfl⟩))
      (FockB.X_mem (Or.inr ⟨c, rfl⟩)))
  · unfold Formalism.GM.tieF
    refine sum_mem fun c _ => ?_
    rw [← Module.End.mul_eq_comp]
    exact mul_mem (FockB.pderiv_mem (Or.inl ⟨c, rfl⟩)) (FockB.pderiv_mem (Or.inr ⟨c, rfl⟩))

/- English proof (translation)
Establish `hc : Commute (LinearMap.mulRight k q : Module.End k (MvPolynomial σ k)) T`. Use `Algebra.commute_of_mem_adjoin_of_forall_mem_commute hT (fun b hb => ?_)` and prove the remaining obligations. Take `⟨u, hu, rfl | rfl⟩` from `hb`. Rewrite using `[commute_iff_eq]`. Use `LinearMap.ext fun f => ?_` and prove the remaining obligations.

Simplify using `only [Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[commute_iff_eq]`. Use `LinearMap.ext fun f => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, LinearMap.mulRight_apply, Derivation.coeFn_coe]`.

Rewrite using `[pderiv_mul, ProjS.pderiv_of_free u q (fun m hm => hq m hm u hu), mul_zero, add_zero]`. Use `LinearMap.congr_fun hc.eq g` as an intermediate fact. Simplify using `only [Module.End.mul_apply, LinearMap.mulRight_apply] at this`. Conclude with `this.symm`.
-/
theorem ops_mul_free (S : Set σ) {T : Module.End k (MvPolynomial σ k)} (hT : T ∈ FockB.Ops S)
    (q : MvPolynomial σ k) (hq : ∀ m ∈ q.support, ∀ v ∈ S, m v = 0) (g : MvPolynomial σ k) :
    T (g * q) = T g * q := by
  have hc : Commute (LinearMap.mulRight k q : Module.End k (MvPolynomial σ k)) T := by
    refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hT (fun b hb => ?_)
    obtain ⟨u, hu, rfl | rfl⟩ := hb
    · rw [commute_iff_eq]
      refine LinearMap.ext fun f => ?_
      simp only [Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
      ring
    · rw [commute_iff_eq]
      refine LinearMap.ext fun f => ?_
      simp only [Module.End.mul_apply, LinearMap.mulRight_apply, Derivation.coeFn_coe]
      rw [pderiv_mul, ProjS.pderiv_of_free u q (fun m hm => hq m hm u hu), mul_zero, add_zero]
  have := LinearMap.congr_fun hc.eq g
  simp only [Module.End.mul_apply, LinearMap.mulRight_apply] at this
  exact this.symm

/- English proof (translation)
Establish `h1` using `ops_keep_supp S {m : σ →₀ ℕ | ∀ v, m v ≠ 0 → P v} (fun m m' h hm v hv => by`. Distinguish the cases in `hvS : v ∈ S`. Conclude with `hS v hvS`. Conclude with `hm v (by rw [h v hvS]; exact hv)) hT g (by`. Rewrite using `[mem_restrictSupport_iff]`.

Introduce `m hm`. Conclude with `hg m (Finset.mem_coe.mp hm))`. Rewrite `h1` using `[mem_restrictSupport_iff]`. Introduce `m hm`. Conclude with `h1 (Finset.mem_coe.mpr hm)`.
-/
theorem ops_keep_pred (S : Set σ) (P : σ → Prop) (hS : ∀ v ∈ S, P v) {T : Module.End k (MvPolynomial σ k)}
    (hT : T ∈ FockB.Ops S) (g : MvPolynomial σ k) (hg : ∀ m ∈ g.support, ∀ v, m v ≠ 0 → P v) :
    ∀ m ∈ (T g).support, ∀ v, m v ≠ 0 → P v := by
  have h1 := ops_keep_supp S {m : σ →₀ ℕ | ∀ v, m v ≠ 0 → P v} (fun m m' h hm v hv => by
    by_cases hvS : v ∈ S
    · exact hS v hvS
    · exact hm v (by rw [h v hvS]; exact hv)) hT g (by
      rw [mem_restrictSupport_iff]
      intro m hm
      exact hg m (Finset.mem_coe.mp hm))
  rw [mem_restrictSupport_iff] at h1
  intro m hm
  exact h1 (Finset.mem_coe.mpr hm)

/- English proof (translation)
Establish `hfree : ∀ g : MvPolynomial σ k, IsF fs g → ∀ m ∈ g.support, ∀ v ∈ S, m v = 0`. Introduce `g hg m hm v hv`. Assume the negation of the conclusion as `h`. Conclude with `hS v hv (hg m hm v h)`. Proceed by induction on `x using MvPolynomial.induction_on' with`.

Consider the case `monomial m a`. Rewrite using `[monomial_split fs m a]`. Establish `hg` using `isF_monomial_frst (K := k) fs m a`. Establish `hq` using `isL_monomial_ltr (K := k) fs m 1`. Establish `hTq : IsL fs (T (monomial (ltr fs m) 1))` using `ops_keep_pred S (fun v => ¬ fs v) hS hT _ hq`.

Establish `e1 : T (monomial (frst fs m) a * monomial (ltr fs m) 1) = monomial (frst fs m) a * T (monomial (ltr fs m) 1)`. Rewrite using `[mul_comm, ops_mul_free S hT _ (hfree _ hg), mul_comm]`. Establish `e2 : T (φ (monomial (frst fs m) a) * monomial (ltr fs m) 1) = φ (monomial (frst fs m) a) * T (monomial (ltr fs m) 1)`. Rewrite using `[mul_comm, ops_mul_free S hT _ (hfree _ (hφ _)), mul_comm]`. Rewrite using `[ext_mul fs φ hg hq, e1, ext_mul fs φ hg hTq, e2]`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem ext_ops_comm [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs] (S : Set σ) (hS : ∀ v ∈ S, ¬ fs v)
    {T : Module.End k (MvPolynomial σ k)} (hT : T ∈ FockB.Ops S)
    (φ : MvPolynomial σ k →ₗ[k] MvPolynomial σ k) (hφ : ∀ x, IsF fs (φ x)) (x : MvPolynomial σ k) :
    ext fs φ (T x) = T (ext fs φ x) := by
  have hfree : ∀ g : MvPolynomial σ k, IsF fs g → ∀ m ∈ g.support, ∀ v ∈ S, m v = 0 := by
    intro g hg m hm v hv
    by_contra h
    exact hS v hv (hg m hm v h)
  induction x using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [monomial_split fs m a]
    have hg := isF_monomial_frst (K := k) fs m a
    have hq := isL_monomial_ltr (K := k) fs m 1
    have hTq : IsL fs (T (monomial (ltr fs m) 1)) := ops_keep_pred S (fun v => ¬ fs v) hS hT _ hq
    have e1 : T (monomial (frst fs m) a * monomial (ltr fs m) 1) = monomial (frst fs m) a * T (monomial (ltr fs m) 1) := by
      rw [mul_comm, ops_mul_free S hT _ (hfree _ hg), mul_comm]
    have e2 : T (φ (monomial (frst fs m) a) * monomial (ltr fs m) 1) =
        φ (monomial (frst fs m) a) * T (monomial (ltr fs m) 1) := by
      rw [mul_comm, ops_mul_free S hT _ (hfree _ (hφ _)), mul_comm]
    rw [ext_mul fs φ hg hq, e1, ext_mul fs φ hg hTq, e2]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Simplify using `only [Formalism.GM.tieE, LinearMap.mulLeft_apply, map_mul, map_sum, rename_X]`.
-/
theorem tieE_rename {τ : Type} {r : ℕ} (ι : σ → τ) (w e : Fin r → σ) (F : MvPolynomial σ k) :
    Formalism.GM.tieE (fun c => ι (w c)) (fun c => ι (e c)) (rename ι F) = rename ι (Formalism.GM.tieE w e F) := by
  simp only [Formalism.GM.tieE, LinearMap.mulLeft_apply, map_mul, map_sum, rename_X]

/- English proof (translation)
Simplify using `only [Formalism.GM.tieF, LinearMap.sum_apply, LinearMap.comp_apply, Derivation.coeFn_coe, map_sum, pderiv_rename hι]`.
-/
theorem tieF_rename {τ : Type} {r : ℕ} (ι : σ → τ) (hι : Function.Injective ι) (w e : Fin r → σ)
    (F : MvPolynomial σ k) :
    Formalism.GM.tieF (fun c => ι (w c)) (fun c => ι (e c)) (rename ι F) = rename ι (Formalism.GM.tieF w e F) := by
  simp only [Formalism.GM.tieF, LinearMap.sum_apply, LinearMap.comp_apply, Derivation.coeFn_coe, map_sum,
    pderiv_rename hι]

/- English proof (translation)
Establish `hE : ∀ (j : ℕ) (G : MvPolynomial σ k), ((Formalism.GM.tieE (fun c => ι (w c)) (fun c => ι (e c))) ^ j) (rename ι G) = rename ι (((Formalism.GM.tieE w e) ^ j) G)`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro G`. Simplify using the standard rewrite rules.

Consider the case `succ j ih => intro G`. Rewrite using `[pow_succ, Module.End.mul_apply, tieE_rename, ih, pow_succ, Module.End.mul_apply]`. Establish `hF : ∀ (j : ℕ) (G : MvPolynomial σ k), ((Formalism.GM.tieF (fun c => ι (w c)) (fun c => ι (e c))) ^ j) (rename ι G) = rename ι (((Formalism.GM.tieF w e) ^ j) G)`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => intro G`. Simplify using the standard rewrite rules. Consider the case `succ j ih => intro G`. Rewrite using `[pow_succ, Module.End.mul_apply, tieF_rename ι hι, ih, pow_succ, Module.End.mul_apply]`. Simplify using `only [Formalism.GM.tiePhi, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum, hF, hE]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← AlgHom.toLinearMap_apply (rename ι), map_smul]`. Both sides reduce to the same expression.
-/
theorem tiePhi_rename {τ : Type} {r : ℕ} (ι : σ → τ) (hι : Function.Injective ι) (w e : Fin r → σ) (o n z : ℕ)
    (F : MvPolynomial σ k) :
    Formalism.GM.tiePhi (fun c => ι (w c)) (fun c => ι (e c)) o n z (rename ι F) =
      rename ι (Formalism.GM.tiePhi w e o n z F) := by
  have hE : ∀ (j : ℕ) (G : MvPolynomial σ k),
      ((Formalism.GM.tieE (fun c => ι (w c)) (fun c => ι (e c))) ^ j) (rename ι G) =
        rename ι (((Formalism.GM.tieE w e) ^ j) G) := by
    intro j
    induction j with
    | zero => intro G; simp
    | succ j ih => intro G; rw [pow_succ, Module.End.mul_apply, tieE_rename, ih, pow_succ, Module.End.mul_apply]
  have hF : ∀ (j : ℕ) (G : MvPolynomial σ k),
      ((Formalism.GM.tieF (fun c => ι (w c)) (fun c => ι (e c))) ^ j) (rename ι G) =
        rename ι (((Formalism.GM.tieF w e) ^ j) G) := by
    intro j
    induction j with
    | zero => intro G; simp
    | succ j ih => intro G; rw [pow_succ, Module.End.mul_apply, tieF_rename ι hι, ih, pow_succ, Module.End.mul_apply]
  simp only [Formalism.GM.tiePhi, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum, hF, hE]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← AlgHom.toLinearMap_apply (rename ι), map_smul]
  rfl

end OpsAux

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

/- English proof (translation)
Unfold `fock`. Rewrite using `[support_rename_of_injective hι, Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hι h)]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_rename_mapDomain ι hι, coeff_rename_mapDomain ι hι, Finsupp.prod_mapDomain_index_inj hι]`.
-/
theorem fock_rename {σ τ : Type} (ι : σ → τ) (hι : Function.Injective ι) (F F' : MvPolynomial σ ℚ_[p]) :
    fock p (rename ι F) (rename ι F') = fock p F F' := by
  classical
  unfold fock
  rw [support_rename_of_injective hι, Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hι h)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_rename_mapDomain ι hι, coeff_rename_mapDomain ι hι, Finsupp.prod_mapDomain_index_inj hι]

/- English proof (translation)
Assume the negation of the conclusion as `hz`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m, m ∈ z.support := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hz (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))`.

Establish `h1` using `Formalism.CountingSumsFrames.fock_monomial z m hm`. Rewrite `h1` using `[h]`. Establish `h2 : (m.prod fun _ k => (k.factorial : ℚ_[p])) ≠ 0`. Rewrite using `[Finsupp.prod]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun v _ => by exact_mod_cast Nat.factorial_ne_zero _`.

Conclude with `(mul_ne_zero (mem_support_iff.mp hm) h2) h1.symm`.
-/
theorem fock_nondeg {σ : Type} (z : MvPolynomial σ ℚ_[p]) (h : ∀ y, fock p z y = 0) : z = 0 := by
  by_contra hz
  obtain ⟨m, hm⟩ : ∃ m, m ∈ z.support := by
    by_contra hc; push Not at hc
    exact hz (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))
  have h1 := Formalism.CountingSumsFrames.fock_monomial z m hm
  rw [h] at h1
  have h2 : (m.prod fun _ k => (k.factorial : ℚ_[p])) ≠ 0 := by
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun v _ => by exact_mod_cast Nat.factorial_ne_zero _
  exact (mul_ne_zero (mem_support_iff.mp hm) h2) h1.symm

/- English proof (translation)
Unfold `TieData.phi`. Rewrite using `[dif_pos h]`. Unfold `tiePhiAt`. Use `FockB.ops_mono ?_ (tiePhi_mem' _ _ _ _ _)` and prove the remaining obligations. Introduce and unpack `v (⟨c, rfl⟩ | ⟨c, rfl⟩)`.

Use `left`. Both sides reduce to the same expression. Use `right`. Both sides reduce to the same expression.
-/
theorem phi_mem' (L : Letters N) (T : TieData) (j : Fin T.t) (h : T.pos j + 1 < N) :
    (T.phi p L j : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈
      FockB.Ops {v : Fin N × Fin r | (v.1 : ℕ) = T.pos j ∨ (v.1 : ℕ) = T.pos j + 1} := by
  unfold TieData.phi
  rw [dif_pos h]
  unfold tiePhiAt
  refine FockB.ops_mono ?_ (tiePhi_mem' _ _ _ _ _)
  rintro v (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · left; rfl
  · right; rfl

section Comparison₂

variable (L : Letters N) (T : TieData) (hadm : T.Admissible L) (i : Fin T.t)

include hadm

/- English proof (translation)
Establish `hK` using `hK_of_adm L T hadm i`. Use `ops_mul_free _ (phi_mem' L T i (by omega)) q (fun m hm v hv => ?_) g` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Use `hq m hm v h` as an intermediate fact. Simplify using `only [fsj] at this`.

Apply the tactic sequence `rcases hv with hv | hv <;> omega`.
-/
theorem phi_mul_later (g q : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hq : IsL (fsj N r (T.pos i + 1 + 1)) q) :
    T.phi p L i (g * q) = T.phi p L i g * q := by
  have hK := hK_of_adm L T hadm i
  refine ops_mul_free _ (phi_mem' L T i (by omega)) q (fun m hm v hv => ?_) g
  by_contra h
  have := hq m hm v h
  simp only [fsj] at this
  rcases hv with hv | hv <;> omega

/- English proof (translation)
Establish `hK` using `hK_of_adm L T hadm i`. Use `ops_keep_pred _ (fsj N r (T.pos i + 1 + 1)) (fun v hv => ?_) (phi_mem' L T i (by omega)) g hg` and prove the remaining obligations. Simplify using `only [fsj]`. Apply the tactic sequence `rcases hv with hv | hv <;> omega`.
-/
theorem phi_isF (g : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hg : IsF (fsj N r (T.pos i + 1 + 1)) g) :
    IsF (fsj N r (T.pos i + 1 + 1)) (T.phi p L i g) := by
  have hK := hK_of_adm L T hadm i
  refine ops_keep_pred _ (fsj N r (T.pos i + 1 + 1)) (fun v hv => ?_) (phi_mem' L T i (by omega)) g hg
  simp only [fsj]
  rcases hv with hv | hv <;> omega

/- English proof (translation)
Take `⟨h, hva, hvb⟩` from `hadm.2.1 i`. Use `set a : Fin N := ⟨T.pos i, by omega⟩ with ha`. Use `set b : Fin N := ⟨T.pos i + 1, h⟩ with hb`. Establish `hE : ∀ (c d : Fin r) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]), glAct p L (T.pos i + 1 + 1) c d (Formalism.GM.tieE (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) y) = Formalism.GM.tieE (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) (glAct p L (T.pos i + 1 + 1) c d y)`. Introduce `c d y`.

Simplify using `only [Formalism.GM.tieE, LinearMap.mulLeft_apply]`. Rewrite using `[Formalism.GM.M.FB.glAct_mul]`. Establish `h0 : glAct p L (T.pos i + 1 + 1) c d (∑ e : Fin r, X (a, e) * X (b, e)) = 0`. Rewrite using `[map_sum]`. Establish `: ∀ e : Fin r, glAct p L (T.pos i + 1 + 1) c d (X (a, e) * X (b, e)) = (if e = c then -(X (a, c) * X (b, d)) else 0) + (if e = d then X (a, c) * X (b, d) else 0)`.

Introduce `e`. Establish `hXa : glAct p L (T.pos i + 1 + 1) c d (X (a, e)) = if e = d then X (a, c) else 0`. Rewrite using `[glAct_X_gen, if_pos (show (a : ℕ) < T.pos i + 1 + 1 by show T.pos i < _; omega), hva]; simp`. Establish `hXb : glAct p L (T.pos i + 1 + 1) c d (X (b, e)) = if e = c then -X (b, d) else 0`. Rewrite using `[glAct_X_gen, if_pos (show (b : ℕ) < T.pos i + 1 + 1 by show T.pos i + 1 < _; omega), hvb]; simp`.

Rewrite using `[Formalism.GM.M.FB.glAct_mul, hXa, hXb]`. Use `split_ifs with h1 h2 h2`. Substitute `h1` using the available equality. Substitute `h2` using the available equality. Expand and normalize the polynomial expressions, which then agree.

Substitute `h1` using the available equality. Expand and normalize the polynomial expressions, which then agree. Substitute `h2` using the available equality. Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h0, mul_zero, add_zero]`. Establish `hF : ∀ (c d : Fin r) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]), glAct p L (T.pos i + 1 + 1) c d (Formalism.GM.tieF (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) y) = Formalism.GM.tieF (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) (glAct p L (T.pos i + 1 + 1) c d y)`. Introduce `c d y`.

Rewrite using `[← sub_eq_zero]`. Apply `fock_nondeg` to reduce the goal to its premises. Introduce `u`. Rewrite using `[gammaIntegralityLemmas.fock_symm, sub_eq_add_neg, gammaIntegralityLemmas.fock_symm, gammaIntegralityLemmas.fock_add_left, ← neg_one_smul ℚ_[p], gammaIntegralityLemmas.fock_smul_left, fock_glAct, gammaIntegralityLemmas.fock_symm _ (glAct p L (T.pos i + 1 + 1) d c u), ← gammaInteg …`. Expand and normalize the polynomial expressions, which then agree.

Establish `cE : Commute (glAct p L (T.pos i + 1 + 1) c d : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) (Formalism.GM.tieE (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)))`. Rewrite using `[commute_iff_eq]`. Conclude with `LinearMap.ext fun y => hE c d y`. Establish `cF : Commute (glAct p L (T.pos i + 1 + 1) c d : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) (Formalism.GM.tieF (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)))`. Rewrite using `[commute_iff_eq]`.

Conclude with `LinearMap.ext fun y => hF c d y`. Establish `cP : Commute (glAct p L (T.pos i + 1 + 1) c d : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) (T.phi p L i)`. Unfold `TieData.phi`. Rewrite using `[dif_pos h]`. Unfold `tiePhiAt Formalism.GM.tiePhi`.

Use `Commute.sum_right _ _ _ fun j _ => Commute.smul_right ?_ _` and prove the remaining obligations. Rewrite using `[← Module.End.mul_eq_comp]`. Conclude with `(cE.pow_right j).mul_right (cF.pow_right j)`. Conclude with `(LinearMap.congr_fun cP.eq x).symm`.
-/
theorem phi_glAct (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    T.phi p L i (glAct p L (T.pos i + 1 + 1) c d x) = glAct p L (T.pos i + 1 + 1) c d (T.phi p L i x) := by
  classical
  obtain ⟨h, hva, hvb⟩ := hadm.2.1 i
  set a : Fin N := ⟨T.pos i, by omega⟩ with ha
  set b : Fin N := ⟨T.pos i + 1, h⟩ with hb
  have hE : ∀ (c d : Fin r) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]),
      glAct p L (T.pos i + 1 + 1) c d (Formalism.GM.tieE (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) y) =
        Formalism.GM.tieE (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) (glAct p L (T.pos i + 1 + 1) c d y) := by
    intro c d y
    simp only [Formalism.GM.tieE, LinearMap.mulLeft_apply]
    rw [Formalism.GM.M.FB.glAct_mul]
    have h0 : glAct p L (T.pos i + 1 + 1) c d (∑ e : Fin r, X (a, e) * X (b, e)) = 0 := by
      rw [map_sum]
      have : ∀ e : Fin r, glAct p L (T.pos i + 1 + 1) c d (X (a, e) * X (b, e)) =
          (if e = c then -(X (a, c) * X (b, d)) else 0) + (if e = d then X (a, c) * X (b, d) else 0) := by
        intro e
        have hXa : glAct p L (T.pos i + 1 + 1) c d (X (a, e)) = if e = d then X (a, c) else 0 := by
          rw [glAct_X_gen, if_pos (show (a : ℕ) < T.pos i + 1 + 1 by show T.pos i < _; omega), hva]; simp
        have hXb : glAct p L (T.pos i + 1 + 1) c d (X (b, e)) = if e = c then -X (b, d) else 0 := by
          rw [glAct_X_gen, if_pos (show (b : ℕ) < T.pos i + 1 + 1 by show T.pos i + 1 < _; omega), hvb]; simp
        rw [Formalism.GM.M.FB.glAct_mul, hXa, hXb]
        split_ifs with h1 h2 h2
        · subst h1; subst h2; ring
        · subst h1; ring
        · subst h2; ring
        · ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    rw [h0, mul_zero, add_zero]
  have hF : ∀ (c d : Fin r) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]),
      glAct p L (T.pos i + 1 + 1) c d (Formalism.GM.tieF (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) y) =
        Formalism.GM.tieF (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) (glAct p L (T.pos i + 1 + 1) c d y) := by
    intro c d y
    rw [← sub_eq_zero]
    apply fock_nondeg
    intro u
    rw [gammaIntegralityLemmas.fock_symm, sub_eq_add_neg, gammaIntegralityLemmas.fock_symm, gammaIntegralityLemmas.fock_add_left, ← neg_one_smul ℚ_[p],
      gammaIntegralityLemmas.fock_smul_left, fock_glAct, gammaIntegralityLemmas.fock_symm _ (glAct p L (T.pos i + 1 + 1) d c u),
      ← gammaIntegralityLemmas.fock_E, ← hE, gammaIntegralityLemmas.fock_symm, ← fock_glAct,
      gammaIntegralityLemmas.fock_symm (Formalism.GM.tieF _ _ _) u, ← gammaIntegralityLemmas.fock_E, gammaIntegralityLemmas.fock_symm _ (Formalism.GM.tieE _ _ u)]
    ring
  have cE : Commute (glAct p L (T.pos i + 1 + 1) c d : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
      (Formalism.GM.tieE (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c))) := by
    rw [commute_iff_eq]; exact LinearMap.ext fun y => hE c d y
  have cF : Commute (glAct p L (T.pos i + 1 + 1) c d : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
      (Formalism.GM.tieF (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c))) := by
    rw [commute_iff_eq]; exact LinearMap.ext fun y => hF c d y
  have cP : Commute (glAct p L (T.pos i + 1 + 1) c d : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
      (T.phi p L i) := by
    unfold TieData.phi
    rw [dif_pos h]
    unfold tiePhiAt Formalism.GM.tiePhi
    refine Commute.sum_right _ _ _ fun j _ => Commute.smul_right ?_ _
    rw [← Module.End.mul_eq_comp]
    exact (cE.pow_right j).mul_right (cF.pow_right j)
  exact (LinearMap.congr_fun cP.eq x).symm

/- English proof (translation)
Establish `hK` using `hK_of_adm L T hadm j`. Establish `hlt : T.pos i < T.pos j` using `hadm.1 hij`. Establish `hne : T.pos j ≠ T.pos i + 1`. Introduce `he`. Take `⟨h1, -, hb⟩` from `hadm.2.1 i`.

Take `⟨h2, ha, -⟩` from `hadm.2.1 j`. Establish `: (⟨T.pos j, by omega⟩ : Fin N) = ⟨T.pos i + 1, h1⟩` using `Fin.ext he`. Rewrite `ha` using `[this, hb]`. Conclude with `Bool.false_ne_true ha`. Use `ext_ops_comm (fsj N r (T.pos i + 1 + 1)) _ (fun v hv => ?_) (phi_mem' L T j (by omega)) φ hφ x` and prove the remaining obligations.

Simplify using `only [fsj]`. Apply the tactic sequence `rcases hv with hv | hv <;> omega`.
-/
theorem phi_ext_comm (j : Fin T.t) (hij : i < j)
    (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hφ : ∀ x, IsF (fsj N r (T.pos i + 1 + 1)) (φ x)) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    ext (fsj N r (T.pos i + 1 + 1)) φ (T.phi p L j x) = T.phi p L j (ext (fsj N r (T.pos i + 1 + 1)) φ x) := by
  have hK := hK_of_adm L T hadm j
  have hlt : T.pos i < T.pos j := hadm.1 hij
  have hne : T.pos j ≠ T.pos i + 1 := by
    intro he
    obtain ⟨h1, -, hb⟩ := hadm.2.1 i
    obtain ⟨h2, ha, -⟩ := hadm.2.1 j
    have : (⟨T.pos j, by omega⟩ : Fin N) = ⟨T.pos i + 1, h1⟩ := Fin.ext he
    rw [this, hb] at ha
    exact Bool.false_ne_true ha
  refine ext_ops_comm (fsj N r (T.pos i + 1 + 1)) _ (fun v hv => ?_) (phi_mem' L T j (by omega)) φ hφ x
  simp only [fsj]
  rcases hv with hv | hv <;> omega

end Comparison₂

section Tie2

variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)

include hadm

/- English proof (translation)
Rewrite using `[Ffull_eq, Ffull_eq]`. Conclude with `fock_rename _ (inclusion_prodMap_injective (hK_of_adm LL T hadm i)) _ _`.
-/
theorem fock_Ffull (ρ : Fin r) (n : Fin T.t → ℕ) (f f' : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) :
    fock p (T.Ffull p (LL.setTies T n) i ρ (n i) f) (T.Ffull p (LL.setTies T n) i ρ (n i) f') =
      fock p (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) f)
        (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) f') := by
  rw [Ffull_eq, Ffull_eq]
  exact fock_rename _ (inclusion_prodMap_injective (hK_of_adm LL T hadm i)) _ _

/- English proof (translation)
Establish `hK` using `hK_of_adm LL T hadm i`. Establish `h : T.pos i + 1 < N` using `by omega`. Rewrite using `[Ffull_eq]`. Unfold `TieData.phi`. Rewrite using `[dif_pos h]`.

Unfold `tiePhiAt`. Rewrite using `[← tiePhi_rename _ (inclusion_prodMap_injective hK)]`. Establish `e1 : ιF N (T.pos i + 1) (Fin.castSucc (Fin.last (T.pos i))) = ⟨T.pos i, by omega⟩`. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[ιF_val hK]`.

Simplify using the standard rewrite rules. Establish `e2 : ιF N (T.pos i + 1) (Fin.last (T.pos i + 1)) = ⟨T.pos i + 1, h⟩`. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[ιF_val hK]`. Simplify using the standard rewrite rules.

Establish `d1 : (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)).deg (Fin.castSucc (Fin.last (T.pos i))) = (LL.setTies T n).deg ⟨T.pos i, by omega⟩`. Rewrite using `[Formalism.GM.FrozenVariableComponents.snoc_deg_castSucc]`. Simplify using `[Letters.takeD, (by omega : T.pos i < N)]`. Establish `d2 : (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)).deg (Fin.last (T.pos i + 1)) = (LL.setTies T n).deg ⟨T.pos i + 1, h⟩`. Rewrite using `[Formalism.GM.FrozenVariableComponents.snoc_deg_last, setTies_deg_eta LL T hadm i n h]`.

Rewrite using `[d1, d2]`. Simplify using `only [e1, e2]`.
-/
theorem phi_Ffull (ρ : Fin r) (n : Fin T.t → ℕ) (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) :
    T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) f) =
      rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2))
        (tiePhiAt p (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) (Fin.castSucc (Fin.last (T.pos i)))
          (Fin.last (T.pos i + 1)) (T.z i) (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) f)) := by
  have hK := hK_of_adm LL T hadm i
  have h : T.pos i + 1 < N := by omega
  rw [Ffull_eq]
  unfold TieData.phi
  rw [dif_pos h]
  unfold tiePhiAt
  rw [← tiePhi_rename _ (inclusion_prodMap_injective hK)]
  have e1 : ιF N (T.pos i + 1) (Fin.castSucc (Fin.last (T.pos i))) = ⟨T.pos i, by omega⟩ := by
    apply Fin.ext; rw [ιF_val hK]; simp
  have e2 : ιF N (T.pos i + 1) (Fin.last (T.pos i + 1)) = ⟨T.pos i + 1, h⟩ := by
    apply Fin.ext; rw [ιF_val hK]; simp
  have d1 : (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)).deg (Fin.castSucc (Fin.last (T.pos i))) =
      (LL.setTies T n).deg ⟨T.pos i, by omega⟩ := by
    rw [Formalism.GM.FrozenVariableComponents.snoc_deg_castSucc]
    simp [Letters.takeD, (by omega : T.pos i < N)]
  have d2 : (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)).deg (Fin.last (T.pos i + 1)) =
      (LL.setTies T n).deg ⟨T.pos i + 1, h⟩ := by
    rw [Formalism.GM.FrozenVariableComponents.snoc_deg_last, setTies_deg_eta LL T hadm i n h]
  rw [d1, d2]
  simp only [e1, e2]

/- English proof (translation)
Rewrite using `[phi_Ffull LL T hadm i ρ n f, Ffull_eq, fock_rename _ (inclusion_prodMap_injective (hK_of_adm LL T hadm i))]`. Both sides reduce to the same expression.
-/
theorem gam_eq (ρ : Fin r) (n : Fin T.t → ℕ) (f f' : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) :
    tieGam p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (T.z i) (n i) f f' =
      (((((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i)) + n i + r + T.z i - 1).choose
          (((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i))) : ℕ) : ℚ_[p]) *
        fock p (T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) f))
          (T.Ffull p (LL.setTies T n) i ρ (n i) f') /
        ((((n i - ((LL.setTies T n).takeD (T.pos i + 1)).total).factorial *
            ((LL.setTies T n).takeD (T.pos i + 1)).total.factorial : ℕ) : ℚ_[p]) *
          ∏ x, ((((LL.setTies T n).takeD (T.pos i + 1)).deg x).factorial : ℚ_[p])) := by
  rw [phi_Ffull LL T hadm i ρ n f, Ffull_eq, fock_rename _ (inclusion_prodMap_injective (hK_of_adm LL T hadm i))]
  rfl

end Tie2

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).one_lt`. Establish `hr1 : (1 : ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `ha0 : (0 : ℝ) ≤ a` using `Nat.cast_nonneg a`. Establish `hlog : (Nat.log p (2 * a) : ℝ) ≤ lgV2 p a r`. Unfold `lgV2`.

Establish `h0 : 0 ≤ Real.logb p (8 * a + r)` using `Real.logb_nonneg hp1 (by linarith)`. Distinguish the cases in `ha : a = 0`. Establish `hz : Nat.log p (2 * a) = 0` using `by rw [ha]; simp`. Rewrite using `[hz, Nat.cast_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1 : (Nat.log p (2 * a) : ℝ) ≤ Real.logb p ((2 * a : ℕ) : ℝ)` using `Real.natLog_le_logb _ _`. Establish `hapos : (0 : ℝ) < a` using `by exact_mod_cast Nat.pos_of_ne_zero ha`. Establish `h2 : Real.logb p ((2 * a : ℕ) : ℝ) ≤ Real.logb p (8 * a + r)`. Apply `Real.logb_le_logb_of_le hp1` to reduce the goal to its premises. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hl0 : (0 : ℝ) ≤ (Nat.log p (2 * a) : ℝ)` using `Nat.cast_nonneg _`.

Establish `hK0 : (0 : ℝ) ≤ K` using `Nat.cast_nonneg K`. Establish `h3 : (((K + 2) * (r * Nat.log p (2 * a)) : ℕ) : ℝ) ≤ κ`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul (by linarith) _ (by positivity) (by positivity)` to reduce the goal to its premises.

Apply `mul_le_mul _ hlog hl0 (by positivity)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Use `_ = ((K + 3) * r ^ 2 : ℝ) * lgV2 p a r := by ring`. Use `_ ≤ κ := hκ`. Conclude with `h3.trans (Nat.le_ceil κ)` after adjusting the coercions.
-/
theorem gamma_zero_exponent_le (K r a : ℕ) (hr : 1 ≤ r) (κ : ℝ) (hκ : ((K + 3) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ) :
    (K + 2) * (r * Nat.log p (2 * a)) ≤ ⌈κ⌉₊ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hlog : (Nat.log p (2 * a) : ℝ) ≤ lgV2 p a r := by
    unfold lgV2
    have h0 : 0 ≤ Real.logb p (8 * a + r) := Real.logb_nonneg hp1 (by linarith)
    by_cases ha : a = 0
    · have hz : Nat.log p (2 * a) = 0 := by rw [ha]; simp
      rw [hz, Nat.cast_zero]
      linarith
    · have h1 : (Nat.log p (2 * a) : ℝ) ≤ Real.logb p ((2 * a : ℕ) : ℝ) := Real.natLog_le_logb _ _
      have hapos : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha
      have h2 : Real.logb p ((2 * a : ℕ) : ℝ) ≤ Real.logb p (8 * a + r) := by
        apply Real.logb_le_logb_of_le hp1
        · push_cast; linarith
        · push_cast; linarith
      linarith
  have hl0 : (0 : ℝ) ≤ (Nat.log p (2 * a) : ℝ) := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h3 : (((K + 2) * (r * Nat.log p (2 * a)) : ℕ) : ℝ) ≤ κ := by
    push_cast
    calc ((K : ℝ) + 2) * ((r : ℝ) * (Nat.log p (2 * a) : ℝ))
        ≤ ((K : ℝ) + 3) * ((r : ℝ) ^ 2 * lgV2 p a r) := by
          apply mul_le_mul (by linarith) _ (by positivity) (by positivity)
          apply mul_le_mul _ hlog hl0 (by positivity)
          nlinarith
      _ = ((K + 3) * r ^ 2 : ℝ) * lgV2 p a r := by ring
      _ ≤ κ := hκ
  exact_mod_cast h3.trans (Nat.le_ceil κ)

/- English proof (translation)
Establish `hr : 1 ≤ r` using `Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact ρ.elim0)`. Take `⟨hfP, hfI⟩` from `Submodule.mem_inf.mp hf`. Take `⟨hfP', hfI'⟩` from `Submodule.mem_inf.mp hf'`. Take `⟨hFP, -, hFI⟩` from `Formalism.GM.extendMapsTo p (K + 1) r LLw ρ n hS f hfP`. Take `⟨-, -, hFI'⟩` from `Formalism.GM.extendMapsTo p (K + 1) r LLw ρ n hS f' hfP'`.

Use `set F := freeze p LLw ρ n f with hF`. Use `set F' := freeze p LLw ρ n f' with hF'`. Establish `hc` using `gammaIntegralityLemmas.intPol_coeff F (hFI hfI)`. Establish `hc'` using `gammaIntegralityLemmas.intPol_coeff F' (hFI' hfI')`. Use `set Den : ℕ := ((n - LLw.total).factorial * LLw.total.factorial) * ∏ i, (LLw.deg i).factorial with hDen`.

Establish `hDen0 : Den ≠ 0`. Rewrite using `[hDen]`. Conclude with `Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne') (Finset.prod_ne_zero_iff.mpr fun i _ => (Nat.factorial_pos _).ne')`. Establish `hDcast : ((((n - LLw.total).factorial * LLw.total.factorial : ℕ) : ℚ_[p]) * ∏ i, ((LLw.deg i).factorial : ℚ_[p])) = (Den : ℚ_[p])`. Rewrite using `[hDen]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hDcast, gammaIntegralityLemmas.fock_def', Finset.sum_div, Finset.mul_sum]`. Use `gammaIntegralityLemmas.norm_sum_le_bound _ _ 1 zero_le_one ?_` and prove the remaining obligations. Introduce `m hm`.

Establish `hmd : MultiDeg (LLw.snoc n) m`. Rewrite `hFP` using `[Pol, mem_restrictSupport_iff]`. Conclude with `hFP (Finset.mem_coe.mpr hm)`. Use `set Num : ℕ := ∏ v : Fin (K + 1 + 1) × Fin r, (m v).factorial with hNum`. Establish `hNum0 : Num ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun i _ => (Nat.factorial_pos _).ne'`.

Establish `hwf : gammaIntegralityLemmas.wf (p` using `p) m = (Num : ℚ_[p]) := by`. Rewrite using `[hNum, gammaIntegralityLemmas.wf]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[hwf]`.

Establish `hδ : ∀ i, gammaIntegralityLemmas.δv m i = (LLw.snoc n).deg i` using `fun i => hmd i`. Establish `hT : ∀ i, gammaIntegralityLemmas.δv m i ≤ 2 * a`. Introduce `i`. Rewrite using `[hδ]`. Use `Fin.lastCases ?_ (fun i => ?_) i` and prove the remaining obligations.

Rewrite using `[FrozenVariableComponents.snoc_deg_last]`. Conclude with `hn`. Rewrite using `[FrozenVariableComponents.snoc_deg_castSucc]`. Conclude with `(gammaIntegralityLemmas.deg_le_total LLw i).trans (hS.trans hn)`. Establish `h1` using `gammaIntegralityLemmas.vW_ge (p := p) m (T := 2 * a) (B := Nat.log p (2 * a)) le_rfl hT`.

Rewrite `h1` using `[Fin.sum_univ_castSucc]`. Simplify using `only [hδ, FrozenVariableComponents.snoc_deg_last, FrozenVariableComponents.snoc_deg_castSucc] at h1`. Establish `h2 : padicValNat p Den = padicValNat p (n - LLw.total).factorial + padicValNat p LLw.total.factorial + ∑ i, padicValNat p (LLw.deg i).factorial`. Rewrite using `[hDen, padicValNat.mul (Nat.mul_ne_zero (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne') (Finset.prod_ne_zero_iff.mpr fun i _ => (Nat.factorial_pos _).ne'), padicValNat.mul (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne', gammaIntegralityLemmas.v_prod _ _ (fun i _ => (Nat …`. Establish `h3 : padicValNat p (n - LLw.total).factorial + padicValNat p LLw.total.factorial ≤ padicValNat p n.factorial`.

Establish `e` using `Nat.choose_mul_factorial_mul_factorial hS`. Rewrite using `[← e, padicValNat.mul (Nat.mul_ne_zero (Nat.choose_pos hS).ne' (Nat.factorial_pos _).ne') (Nat.factorial_pos _).ne', padicValNat.mul (Nat.choose_pos hS).ne' (Nat.factorial_pos _).ne']`. Use linear arithmetic over natural numbers and integers. Establish `h4` using `gamma_zero_exponent_le (p := p) K r a hr κ hκ`. Establish `h5` using `gammaIntegralityLemmas.norm_K (p := p) ⌈κ⌉₊ (coeff m F) (coeff m F') 0 0 (by simpa using hc m) (by simpa using hc' m) Num Den hNum0 hDen0 1 norm_one (by`.

Establish `: (padicValNat p Den : ℤ) ≤ (padicValNat p Num : ℤ) + (⌈κ⌉₊ : ℤ)`. Establish `: padicValNat p Den ≤ padicValNat p Num + ⌈κ⌉₊`. Rewrite using `[h2]`. Establish `h1' : ∑ i, padicValNat p (LLw.deg i).factorial + padicValNat p n.factorial ≤ padicValNat p Num + (K + 2) * (r * Nat.log p (2 * a))` using `h1`. Use linear arithmetic over natural numbers and integers.

Conclude with `this` after adjusting the coercions. Use the proof step `omega)`. Rewrite `h5` using `[one_mul]`. Conclude with `h5`.
-/
theorem gamma_zero_integral_alt (K r : ℕ) (LLw : Letters (K + 1)) (ρ : Fin r) (n a : ℕ) (κ : ℝ)
    (hS : LLw.total ≤ n) (hn : n ≤ 2 * a) (hκ : ((K + 3) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ)
    (f f' : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hf : f ∈ PolZ p r LLw) (hf' : f' ∈ PolZ p r LLw) :
    ‖(p : ℚ_[p]) ^ ⌈κ⌉₊ * (fock p (freeze p LLw ρ n f) (freeze p LLw ρ n f') /
      ((((n - LLw.total).factorial * LLw.total.factorial : ℕ) : ℚ_[p]) *
        ∏ i, ((LLw.deg i).factorial : ℚ_[p])))‖ ≤ 1 := by
  classical
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact ρ.elim0)
  obtain ⟨hfP, hfI⟩ := Submodule.mem_inf.mp hf
  obtain ⟨hfP', hfI'⟩ := Submodule.mem_inf.mp hf'
  obtain ⟨hFP, -, hFI⟩ := Formalism.GM.extendMapsTo p (K + 1) r LLw ρ n hS f hfP
  obtain ⟨-, -, hFI'⟩ := Formalism.GM.extendMapsTo p (K + 1) r LLw ρ n hS f' hfP'
  set F := freeze p LLw ρ n f with hF
  set F' := freeze p LLw ρ n f' with hF'
  have hc := gammaIntegralityLemmas.intPol_coeff F (hFI hfI)
  have hc' := gammaIntegralityLemmas.intPol_coeff F' (hFI' hfI')
  set Den : ℕ := ((n - LLw.total).factorial * LLw.total.factorial) * ∏ i, (LLw.deg i).factorial with hDen
  have hDen0 : Den ≠ 0 := by
    rw [hDen]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne')
      (Finset.prod_ne_zero_iff.mpr fun i _ => (Nat.factorial_pos _).ne')
  have hDcast : ((((n - LLw.total).factorial * LLw.total.factorial : ℕ) : ℚ_[p]) *
        ∏ i, ((LLw.deg i).factorial : ℚ_[p])) = (Den : ℚ_[p]) := by
    rw [hDen]; push_cast; ring
  rw [hDcast, gammaIntegralityLemmas.fock_def', Finset.sum_div, Finset.mul_sum]
  refine gammaIntegralityLemmas.norm_sum_le_bound _ _ 1 zero_le_one ?_
  intro m hm
  have hmd : MultiDeg (LLw.snoc n) m := by
    rw [Pol, mem_restrictSupport_iff] at hFP
    exact hFP (Finset.mem_coe.mpr hm)
  set Num : ℕ := ∏ v : Fin (K + 1 + 1) × Fin r, (m v).factorial with hNum
  have hNum0 : Num ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (Nat.factorial_pos _).ne'
  have hwf : gammaIntegralityLemmas.wf (p := p) m = (Num : ℚ_[p]) := by
    rw [hNum, gammaIntegralityLemmas.wf]; push_cast; rfl
  rw [hwf]
  have hδ : ∀ i, gammaIntegralityLemmas.δv m i = (LLw.snoc n).deg i := fun i => hmd i
  have hT : ∀ i, gammaIntegralityLemmas.δv m i ≤ 2 * a := by
    intro i
    rw [hδ]
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [FrozenVariableComponents.snoc_deg_last]; exact hn
    · rw [FrozenVariableComponents.snoc_deg_castSucc]
      exact (gammaIntegralityLemmas.deg_le_total LLw i).trans (hS.trans hn)
  have h1 := gammaIntegralityLemmas.vW_ge (p := p) m (T := 2 * a) (B := Nat.log p (2 * a)) le_rfl hT
  rw [Fin.sum_univ_castSucc] at h1
  simp only [hδ, FrozenVariableComponents.snoc_deg_last, FrozenVariableComponents.snoc_deg_castSucc] at h1
  have h2 : padicValNat p Den = padicValNat p (n - LLw.total).factorial + padicValNat p LLw.total.factorial +
      ∑ i, padicValNat p (LLw.deg i).factorial := by
    rw [hDen, padicValNat.mul (Nat.mul_ne_zero (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne')
      (Finset.prod_ne_zero_iff.mpr fun i _ => (Nat.factorial_pos _).ne'),
      padicValNat.mul (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne',
      gammaIntegralityLemmas.v_prod _ _ (fun i _ => (Nat.factorial_pos _).ne')]
  have h3 : padicValNat p (n - LLw.total).factorial + padicValNat p LLw.total.factorial ≤
      padicValNat p n.factorial := by
    have e := Nat.choose_mul_factorial_mul_factorial hS
    rw [← e, padicValNat.mul (Nat.mul_ne_zero (Nat.choose_pos hS).ne' (Nat.factorial_pos _).ne')
      (Nat.factorial_pos _).ne', padicValNat.mul (Nat.choose_pos hS).ne' (Nat.factorial_pos _).ne']
    omega
  have h4 := gamma_zero_exponent_le (p := p) K r a hr κ hκ
  have h5 := gammaIntegralityLemmas.norm_K (p := p) ⌈κ⌉₊ (coeff m F) (coeff m F') 0 0 (by simpa using hc m) (by simpa using hc' m)
    Num Den hNum0 hDen0 1 norm_one (by
      have : (padicValNat p Den : ℤ) ≤ (padicValNat p Num : ℤ) + (⌈κ⌉₊ : ℤ) := by
        have : padicValNat p Den ≤ padicValNat p Num + ⌈κ⌉₊ := by
          rw [h2]
          have h1' : ∑ i, padicValNat p (LLw.deg i).factorial + padicValNat p n.factorial ≤
              padicValNat p Num + (K + 2) * (r * Nat.log p (2 * a)) := h1
          omega
        exact_mod_cast this
      omega)
  rw [one_mul] at h5
  exact h5

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

structure IsProjC [NeZero r] (L : Letters N) (j0 e : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (Pi : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) : Prop where
  comm : ∀ c d x, Pi (glAct p L j0 c d x) = glAct p L j0 c d (Pi x)
  wh : ∀ ν x, x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν →
    Pi x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν
  pol : ∀ L' : Letters N, L'.vec = L.vec → ∀ x ∈ Pol p r L', Pi x ∈ Pol p r L'
  ycond : ∀ x k, Pi x ∈ YCond p L (J k) (Mup J M j0 k)
  fix : ∀ L' : Letters N, L'.vec = L.vec → ∀ x ∈ Pol p r L', (∀ k, x ∈ YCond p L (J k) (Mup J M j0 k)) → Pi x = x
  int : ∀ x ∈ PolZ p r L, ((p : ℚ_[p]) ^ e) • Pi x ∈ IntPol p (Fin N × Fin r)
  mul : ∀ g q, IsL (fsj N r j0) q → Pi (g * q) = Pi g * q

/- English proof (translation)
Rewrite using `[WtSpC, mem_restrictSupport_iff, mem_weightedHomogeneousSubmodule]`. Prove the components needed by the constructor for the conclusion. Introduce `h m hm`. Use function extensionality and compare the values at `c`. Rewrite using `[weight_wv]`.

Conclude with `h (Finset.mem_coe.mpr (mem_support_iff.mpr hm)) c (Finset.mem_univ c)`. Introduce `h m hm c _`. Rewrite using `[← weight_wv, h (mem_support_iff.mp (Finset.mem_coe.mp hm))]`.
-/
theorem wtsp_iff_wh (L : Letters N) (j : ℕ) (μ : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    x ∈ WtSpC p L j univ μ ↔ x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j) μ := by
  rw [WtSpC, mem_restrictSupport_iff, mem_weightedHomogeneousSubmodule]
  constructor
  · intro h m hm
    funext c
    rw [weight_wv]
    exact h (Finset.mem_coe.mpr (mem_support_iff.mpr hm)) c (Finset.mem_univ c)
  · intro h m hm c _
    rw [← weight_wv, h (mem_support_iff.mp (Finset.mem_coe.mp hm))]

/- English proof (translation)
Introduce `x hx`. Take `⟨h1, h2⟩` from `Submodule.mem_inf.mp hx`. Use `Submodule.mem_inf.mpr ⟨comm_wtsp L j Q (fun c x => hc c c x) la x h1, ?_⟩` and prove the remaining obligations. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker] at h2 ⊢`. Introduce `c d hcd`.

Rewrite using `[← hc, h2 c d hcd, map_zero]`.
-/
theorem hwc_keep (L : Letters N) (j : ℕ) (la : Fin r → ℤ)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hc : ∀ c d x, Q (glAct p L j c d x) = glAct p L j c d (Q x)) :
    ∀ x ∈ HWC p L j univ la, Q x ∈ HWC p L j univ la := by
  intro x hx
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hx
  refine Submodule.mem_inf.mpr ⟨comm_wtsp L j Q (fun c x => hc c c x) la x h1, ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h2 ⊢
  intro c d hcd
  rw [← hc, h2 c d hcd, map_zero]

/- English proof (translation)
The claim follows from `isoC_keep L j la Q hc (hwc_keep L j la Q hc)`.
-/
theorem iso_keep_comm (L : Letters N) (j : ℕ)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hc : ∀ c d x, Q (glAct p L j c d x) = glAct p L j c d (Q x)) (la : Fin r → ℤ) :
    ∀ x ∈ IsoC p L j univ la, Q x ∈ IsoC p L j univ la :=
  isoC_keep L j la Q hc (hwc_keep L j la Q hc)

/- English proof (translation)
Introduce `x hx`. Rewrite using `[glAct_split L hj c d, LinearMap.add_apply]`. Conclude with `Submodule.add_mem _ (isoC_glStable L j la c d x hx) (iso_keep_comm L j (midAct p L j j0 c d) (fun c' d' y => midAct_comm L j j0 c d c' d' y) la x hx)`.
-/
theorem iso_keep_glAct (L : Letters N) {j j0 : ℕ} (hj : j ≤ j0) (c d : Fin r) (la : Fin r → ℤ) :
    ∀ x ∈ IsoC p L j univ la, glAct p L j0 c d x ∈ IsoC p L j univ la := by
  intro x hx
  rw [glAct_split L hj c d, LinearMap.add_apply]
  exact Submodule.add_mem _ (isoC_glStable L j la c d x hx)
    (iso_keep_comm L j (midAct p L j j0 c d) (fun c' d' y => midAct_comm L j j0 c d c' d' y) la x hx)

/- English proof (translation)
The claim follows from `iso_keep_comm L j (LinearMap.mulRight ℚ_[p] q) (fun c d x => by simp only [LinearMap.mulRight_apply] exact (glAct_mul_kill L j c d x (killL_of_isL hj hq)).symm) la`.
-/
theorem iso_keep_mul (L : Letters N) {j j0 : ℕ} (hj : j ≤ j0) {q : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hq : IsL (fsj N r j0) q) (la : Fin r → ℤ) :
    ∀ x ∈ IsoC p L j univ la, LinearMap.mulRight ℚ_[p] q x ∈ IsoC p L j univ la :=
  iso_keep_comm L j (LinearMap.mulRight ℚ_[p] q) (fun c d x => by
    simp only [LinearMap.mulRight_apply]
    exact (glAct_mul_kill L j c d x (killL_of_isL hj hq)).symm) la

/- English proof (translation)
Take `⟨v, d⟩` from `L`. Take `⟨v', d'⟩` from `L'`. Simplify using `only at h`. Substitute `h` using the available equality. Conclude with `hP`.
-/
theorem isTypeProj_congr (L L' : Letters N) (h : L'.vec = L.vec) (j : ℕ) (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p L j Cs T P) : IsTypeProj p L' j Cs T P := by
  obtain ⟨v, d⟩ := L
  obtain ⟨v', d'⟩ := L'
  simp only at h
  subst h
  exact hP

/- English proof (translation)
Take `⟨v, d⟩` from `L`. Take `⟨v', d'⟩` from `L'`. Simplify using `only at h`. Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem ycond_congr [NeZero r] (L L' : Letters N) (h : L'.vec = L.vec) (j : ℕ) (Mt : WithTop ℤ) :
    YCond p (r := r) L' j Mt = YCond p (r := r) L j Mt := by
  obtain ⟨v, d⟩ := L
  obtain ⟨v', d'⟩ := L'
  simp only at h
  subst h
  rfl

/- English proof (translation)
The claim follows from `| [] => rfl | a :: l => by rw [lcomp_cons, LinearMap.comp_apply, lcomp_fixed P x hx l, hx a]`.
-/
theorem lcomp_fixed {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [LinearOrder ι] (P : ι → V →ₗ[K] V)
    (x : V) (hx : ∀ j, P j x = x) : ∀ l : List ι, lcomp P l x = x
  | [] => rfl
  | a :: l => by rw [lcomp_cons, LinearMap.comp_apply, lcomp_fixed P x hx l, hx a]

/- English proof (translation)
The claim follows from `| [], _ => rfl | a :: l, x => by rw [lcomp_cons, LinearMap.comp_apply, LinearMap.comp_apply, lcomp_commQ P Q h l x, h a]`.
-/
theorem lcomp_commQ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [LinearOrder ι] (P : ι → V →ₗ[K] V)
    (Q : V →ₗ[K] V) (h : ∀ j x, P j (Q x) = Q (P j x)) : ∀ (l : List ι) (x : V), lcomp P l (Q x) = Q (lcomp P l x)
  | [], _ => rfl
  | a :: l, x => by
    rw [lcomp_cons, LinearMap.comp_apply, LinearMap.comp_apply, lcomp_commQ P Q h l x, h a]

/- English proof (translation)
Take `⟨hP1, hP2⟩` from `hHP`. Set `Tj : Fin j0 → Set (Fin r → ℤ)` to `fun j => {la | ∀ k, J k = (j : ℕ) → ((la 0 : ℤ) : WithTop ℤ) ≤ M k}`. Establish `hex : ∀ j : Fin j0, ∃ P, IsTypeProj p L j univ (Tj j) P ∧ (∀ F G, fock p (P F) G = fock p F (P G)) ∧ ∀ F ∈ PolZ p r L, ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin N × Fin r)` using `fun j => hP1 j (le_trans (le_of_lt j.isLt) hj0) univ (Or.inl rfl) (Tj j) (fun la la' h => by rw [show la = la' from funext fun c => h c (mem_univ c)])`. Use `choose P hPt _hPsa hPint using hex`. Establish `hPP : ∀ j x, P j (P j x) = P j x` using `fun j x => LinearMap.congr_fun (hPt j).1 x`.

Establish `hcomm : ∀ j j' x, P j (P j' x) = P j' (P j x)`. Introduce `j j' x`. Break down `le_total (j : ℕ) (j' : ℕ) with h | h` into its components or cases. Conclude with `LinearMap.congr_fun (hP2 j j' univ univ (Tj j) (Tj j') (P j) (P j') h subset_rfl (Or.inl rfl) (Or.inl rfl) (hPt j) (hPt j')) x`. Conclude with `(LinearMap.congr_fun (hP2 j' j univ univ (Tj j') (Tj j) (P j') (P j) h subset_rfl (Or.inl rfl) (Or.inl rfl) (hPt j') (hPt j)) x).symm`.

Establish `hPpol : ∀ L' : Letters N, L'.vec = L.vec → ∀ j, ∀ x ∈ Pol p r L', P j x ∈ Pol p r L'` using `fun L' hL' j => typeProj_pol L' j (Tj j) (P j) (isTypeProj_congr L L' hL' j univ (Tj j) (P j) (hPt j))`. Establish `hgl : ∀ c d x, lcomp P (List.finRange j0) (glAct p L j0 c d x) = glAct p L j0 c d (lcomp P (List.finRange j0) x)` using `fun c d x => lcomp_commQ P (glAct p L j0 c d) (fun j y => typeProj_comm L j (Tj j) (P j) (hPt j) (glAct p L j0 c d) (fun la => iso_keep_glAct L (le_of_lt j.isLt) c d la) y) _ x`. Use `⟨lcomp P (List.finRange j0), hgl, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `ν x hx`. Rewrite `hx`, the goal using `[← wtsp_iff_wh]`.

Conclude with `comm_wtsp L j0 _ (fun c y => hgl c c y) ν x hx`. Introduce `L' hL' x hx`. Conclude with `lcomp_keep P (Pol p r L' : Set _) _ (fun j _ u hu => hPpol L' hL' j u hu) x hx`. Introduce `x k`. Distinguish the cases in `hk : J k < j0`.

Rewrite using `[Mup, if_pos hk]`. Establish `hfix : P ⟨J k, hk⟩ (lcomp P (List.finRange j0) x) = lcomp P (List.finRange j0) x` using `lcomp_fix P hPP hcomm _ ⟨J k, hk⟩ (List.mem_finRange _) x`. Establish `h1 : lcomp P (List.finRange j0) x ∈ LinearMap.range (P ⟨J k, hk⟩)` using `⟨_, hfix⟩`. Rewrite `h1` using `[(hPt ⟨J k, hk⟩).2.1]`. Conclude with `(iSup₂_le fun la hla => isoC_le_ycond L (J k) la (M k) (hla k rfl)) h1`.

Rewrite using `[Mup, if_neg hk, Formalism.GM.DimensionMonotonicity.ycond_top]`. Conclude with `Submodule.mem_top`. Introduce `L' hL' x hxP hxY`. Use `lcomp_fixed P x (fun j => ?_) _` and prove the remaining obligations. Establish `hPt'` using `isTypeProj_congr L L' hL' j univ (Tj j) (P j) (hPt j)`.

Use `set S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) := Pol p r L' ⊓ ⨅ (k : Fin q) (_ : J k = (j : ℕ)), YCond p (r := r) L' j (M k) with hSdef`. Establish `hmemS : ∀ x, x ∈ S ↔ x ∈ Pol p r L' ∧ ∀ k, J k = (j : ℕ) → x ∈ YCond p (r` using `r) L' j (M k) := by`. Introduce `x`. Simplify using `only [hSdef, Submodule.mem_inf, Submodule.mem_iInf]`. Establish `hfix` using `proj_fix L' j (Tj j) (P j) hPt' S inf_le_left (fun c d x hx => by`.

Rewrite `hx`, the goal using `[hmemS]`. Conclude with `⟨Formalism.CountingSumsFrames.glAct_pol L' j c d x hx.1, fun k hk => ycond_glStable L' j (M k) c d x (hx.2 k hk)⟩)`. Use the proof step `(fun x hx => by`. Rewrite `hx`, the goal using `[hmemS]`. Conclude with `⟨hPpol L' hL' j x hx.1, fun k hk => typeProj_ycond L' j (Tj j) (P j) hPt' (M k) x (hx.2 k hk)⟩)`.

Use the proof step `(fun h hh hh0 μ hμ => by`. Rewrite `hh` using `[hmemS]`. Introduce `k hk`. Establish `h1` using `ycond_le_supp L' j (M k) (hh.2 k hk)`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m, m ∈ h.support := by`.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hh0 (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))`. Rewrite `h1` using `[mem_restrictSupport_iff]`. Establish `h2` using `h1 (Finset.mem_coe.mpr hm)`.

Establish `h3` using `(Submodule.mem_inf.mp hμ).1`. Rewrite `h3` using `[WtSpC, mem_restrictSupport_iff]`. Establish `h4` using `h3 (Finset.mem_coe.mpr hm) 0 (Finset.mem_univ _)`. Simplify using `only [Set.mem_ofPred_eq] at h2`. Rewrite `h2` using `[h4]`.

Conclude with `h2)`. Apply `hfix` to reduce the goal to its premises. Rewrite using `[hmemS]`. Use `⟨hxP, fun k hk => ?_⟩` and prove the remaining obligations. Use `hxY k` as an intermediate fact.

Rewrite `this` using `[Mup, if_pos (by rw [hk]; exact j.isLt), hk]`. Rewrite using `[ycond_congr L L' hL']`. Conclude with `this`. Introduce `x hx`. Use `lcomp_int L e1 P (hPpol L rfl) hPint (List.finRange j0) x hx` as an intermediate fact.

Rewrite `this` using `[List.length_finRange]`. Conclude with `(Submodule.mem_inf.mp this).2`. Introduce `g q hq`. Use `lcomp_commQ P (LinearMap.mulRight ℚ_[p] q) (fun j y => typeProj_comm L j (Tj j) (P j) (hPt j) (LinearMap.mulRight ℚ_[p] q) (fun la => iso_keep_mul L (le_of_lt j.isLt) hq la) y) (List.finRange j0) g` as an intermediate fact. Simplify `this` using `only [LinearMap.mulRight_apply]`.
-/
theorem projC [NeZero r] (L : Letters N) (ρ : Fin r) (e1 j0 : ℕ) (hj0 : j0 ≤ N) (hHP : HypP p L ρ e1) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) :
    ∃ Pi : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p],
      IsProjC L j0 (e1 * j0) J M Pi := by
  obtain ⟨hP1, hP2⟩ := hHP
  let Tj : Fin j0 → Set (Fin r → ℤ) := fun j => {la | ∀ k, J k = (j : ℕ) → ((la 0 : ℤ) : WithTop ℤ) ≤ M k}
  have hex : ∀ j : Fin j0, ∃ P, IsTypeProj p L j univ (Tj j) P ∧ (∀ F G, fock p (P F) G = fock p F (P G)) ∧
      ∀ F ∈ PolZ p r L, ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin N × Fin r) :=
    fun j => hP1 j (le_trans (le_of_lt j.isLt) hj0) univ (Or.inl rfl) (Tj j)
      (fun la la' h => by rw [show la = la' from funext fun c => h c (mem_univ c)])
  choose P hPt _hPsa hPint using hex
  have hPP : ∀ j x, P j (P j x) = P j x := fun j x => LinearMap.congr_fun (hPt j).1 x
  have hcomm : ∀ j j' x, P j (P j' x) = P j' (P j x) := by
    intro j j' x
    rcases le_total (j : ℕ) (j' : ℕ) with h | h
    · exact LinearMap.congr_fun (hP2 j j' univ univ (Tj j) (Tj j') (P j) (P j') h subset_rfl (Or.inl rfl)
        (Or.inl rfl) (hPt j) (hPt j')) x
    · exact (LinearMap.congr_fun (hP2 j' j univ univ (Tj j') (Tj j) (P j') (P j) h subset_rfl (Or.inl rfl)
        (Or.inl rfl) (hPt j') (hPt j)) x).symm
  have hPpol : ∀ L' : Letters N, L'.vec = L.vec → ∀ j, ∀ x ∈ Pol p r L', P j x ∈ Pol p r L' := fun L' hL' j =>
    typeProj_pol L' j (Tj j) (P j) (isTypeProj_congr L L' hL' j univ (Tj j) (P j) (hPt j))
  have hgl : ∀ c d x, lcomp P (List.finRange j0) (glAct p L j0 c d x) =
      glAct p L j0 c d (lcomp P (List.finRange j0) x) := fun c d x =>
    lcomp_commQ P (glAct p L j0 c d) (fun j y => typeProj_comm L j (Tj j) (P j) (hPt j) (glAct p L j0 c d)
      (fun la => iso_keep_glAct L (le_of_lt j.isLt) c d la) y) _ x
  refine ⟨lcomp P (List.finRange j0), hgl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ν x hx
    rw [← wtsp_iff_wh] at hx ⊢
    exact comm_wtsp L j0 _ (fun c y => hgl c c y) ν x hx
  · intro L' hL' x hx
    exact lcomp_keep P (Pol p r L' : Set _) _ (fun j _ u hu => hPpol L' hL' j u hu) x hx
  · intro x k
    by_cases hk : J k < j0
    · rw [Mup, if_pos hk]
      have hfix : P ⟨J k, hk⟩ (lcomp P (List.finRange j0) x) = lcomp P (List.finRange j0) x :=
        lcomp_fix P hPP hcomm _ ⟨J k, hk⟩ (List.mem_finRange _) x
      have h1 : lcomp P (List.finRange j0) x ∈ LinearMap.range (P ⟨J k, hk⟩) := ⟨_, hfix⟩
      rw [(hPt ⟨J k, hk⟩).2.1] at h1
      exact (iSup₂_le fun la hla => isoC_le_ycond L (J k) la (M k) (hla k rfl)) h1
    · rw [Mup, if_neg hk, Formalism.GM.DimensionMonotonicity.ycond_top]; exact Submodule.mem_top
  · intro L' hL' x hxP hxY
    refine lcomp_fixed P x (fun j => ?_) _
    have hPt' := isTypeProj_congr L L' hL' j univ (Tj j) (P j) (hPt j)
    set S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
      Pol p r L' ⊓ ⨅ (k : Fin q) (_ : J k = (j : ℕ)), YCond p (r := r) L' j (M k) with hSdef
    have hmemS : ∀ x, x ∈ S ↔ x ∈ Pol p r L' ∧ ∀ k, J k = (j : ℕ) → x ∈ YCond p (r := r) L' j (M k) := by
      intro x; simp only [hSdef, Submodule.mem_inf, Submodule.mem_iInf]
    have hfix := proj_fix L' j (Tj j) (P j) hPt' S inf_le_left
      (fun c d x hx => by
        rw [hmemS] at hx ⊢
        exact ⟨Formalism.CountingSumsFrames.glAct_pol L' j c d x hx.1, fun k hk => ycond_glStable L' j (M k) c d x (hx.2 k hk)⟩)
      (fun x hx => by
        rw [hmemS] at hx ⊢
        exact ⟨hPpol L' hL' j x hx.1, fun k hk => typeProj_ycond L' j (Tj j) (P j) hPt' (M k) x (hx.2 k hk)⟩)
      (fun h hh hh0 μ hμ => by
        rw [hmemS] at hh
        intro k hk
        have h1 := ycond_le_supp L' j (M k) (hh.2 k hk)
        obtain ⟨m, hm⟩ : ∃ m, m ∈ h.support := by
          by_contra hc; push Not at hc
          exact hh0 (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))
        rw [mem_restrictSupport_iff] at h1
        have h2 := h1 (Finset.mem_coe.mpr hm)
        have h3 := (Submodule.mem_inf.mp hμ).1
        rw [WtSpC, mem_restrictSupport_iff] at h3
        have h4 := h3 (Finset.mem_coe.mpr hm) 0 (Finset.mem_univ _)
        simp only [Set.mem_ofPred_eq] at h2
        rw [h4] at h2
        exact h2)
    apply hfix
    rw [hmemS]
    refine ⟨hxP, fun k hk => ?_⟩
    have := hxY k
    rw [Mup, if_pos (by rw [hk]; exact j.isLt), hk] at this
    rw [ycond_congr L L' hL']
    exact this
  · intro x hx
    have := lcomp_int L e1 P (hPpol L rfl) hPint (List.finRange j0) x hx
    rw [List.length_finRange] at this
    exact (Submodule.mem_inf.mp this).2
  · intro g q hq
    have := lcomp_commQ P (LinearMap.mulRight ℚ_[p] q) (fun j y => typeProj_comm L j (Tj j) (P j) (hPt j)
      (LinearMap.mulRight ℚ_[p] q) (fun la => iso_keep_mul L (le_of_lt j.isLt) hq la) y) (List.finRange j0) g
    simpa only [LinearMap.mulRight_apply] using this

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

section Leib

variable {σ : Type} (A : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])
  (hA : ∀ a b, A (a * b) = a * A b + b * A a)

include hA

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => intro f`. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `f`.

Rewrite using `[pow_succ A k, Module.End.mul_apply, Module.End.mul_apply, hA, hu', mul_zero, zero_add, mul_comm u', ih]`.
-/
theorem pow_mul_killed {u' : MvPolynomial σ ℚ_[p]} (hu' : A u' = 0) (k : ℕ) :
    ∀ f, (A ^ k) (f * u') = (A ^ k) f * u' := by
  induction k with
  | zero => intro f; simp
  | succ k ih =>
    intro f
    rw [pow_succ A k, Module.End.mul_apply, Module.End.mul_apply, hA, hu', mul_zero, zero_add, mul_comm u', ih]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `f`. Simplify using `only [zero_add, pow_one, pow_zero, Module.End.one_apply, hA, hu, Nat.cast_one, one_smul]`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `succ k ih`. Introduce `f`. Establish `e1 : (A ^ (k + 1 + 1)) (f * u) = (A ^ (k + 1)) (A (f * u))`. Rewrite using `[pow_succ A (k + 1), Module.End.mul_apply]`. Establish `e2 : (A ^ (k + 1 + 1)) f = (A ^ (k + 1)) (A f)`.

Rewrite using `[pow_succ A (k + 1), Module.End.mul_apply]`. Establish `e3 : (A ^ (k + 1)) f = (A ^ k) (A f)`. Rewrite using `[pow_succ A k, Module.End.mul_apply]`. Rewrite using `[e1, e2, hA, hu, map_add, pow_mul_killed A hA hu' (k + 1), mul_comm u, ih, ← e3, Nat.cast_succ (k + 1), add_smul, one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem pow_succ_mul_gen {u u' : MvPolynomial σ ℚ_[p]} (hu : A u = u') (hu' : A u' = 0) (k : ℕ) :
    ∀ f, (A ^ (k + 1)) (f * u) = (A ^ (k + 1)) f * u + ((k + 1 : ℕ) : ℚ_[p]) • ((A ^ k) f * u') := by
  induction k with
  | zero =>
    intro f
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, hA, hu, Nat.cast_one, one_smul]
    ring
  | succ k ih =>
    intro f
    have e1 : (A ^ (k + 1 + 1)) (f * u) = (A ^ (k + 1)) (A (f * u)) := by
      rw [pow_succ A (k + 1), Module.End.mul_apply]
    have e2 : (A ^ (k + 1 + 1)) f = (A ^ (k + 1)) (A f) := by
      rw [pow_succ A (k + 1), Module.End.mul_apply]
    have e3 : (A ^ (k + 1)) f = (A ^ k) (A f) := by
      rw [pow_succ A k, Module.End.mul_apply]
    rw [e1, e2, hA, hu, map_add, pow_mul_killed A hA hu' (k + 1), mul_comm u, ih, ← e3,
      Nat.cast_succ (k + 1), add_smul, one_smul]
    abel

end Leib

/- English proof (translation)
Rewrite using `[Formalism.GM.FrozenVariableComponents.glAct_apply]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem glAct_C' (L : Letters N) (j : ℕ) (c d : Fin r) (a : ℚ_[p]) :
    glAct p L j c d (C a) = 0 := by
  rw [Formalism.GM.FrozenVariableComponents.glAct_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Take `⟨i, a⟩` from `v`. Rewrite using `[glAct_X_gen]`. Use `split_ifs`. Conclude with `FrozenVariableLemmas.intPol_X p _`. Conclude with `Submodule.zero_mem _`.

Conclude with `Submodule.neg_mem _ (FrozenVariableLemmas.intPol_X p _)`. Conclude with `Submodule.zero_mem _`. Conclude with `Submodule.zero_mem _`.
-/
theorem glAct_X_int (L : Letters N) (j : ℕ) (c d : Fin r) (v : Fin N × Fin r) :
    glAct p L j c d (X v) ∈ IntPol p (Fin N × Fin r) := by
  obtain ⟨i, a⟩ := v
  rw [glAct_X_gen]
  split_ifs
  · exact FrozenVariableLemmas.intPol_X p _
  · exact Submodule.zero_mem _
  · exact Submodule.neg_mem _ (FrozenVariableLemmas.intPol_X p _)
  · exact Submodule.zero_mem _
  · exact Submodule.zero_mem _

/- English proof (translation)
Take `⟨i, a⟩` from `v`. Rewrite using `[glAct_X_gen]`. Use `split_ifs with h1 h2 h3 h3`. Rewrite using `[glAct_X_gen, if_pos h1, if_pos h2, if_neg hcd]`. Conclude with `map_zero _`.

Rewrite using `[map_neg, glAct_X_gen, if_pos h1, if_neg h2, if_neg (Ne.symm hcd), neg_zero]`. Conclude with `map_zero _`. Conclude with `map_zero _`.
-/
theorem glAct_glAct_X (L : Letters N) (j : ℕ) (c d : Fin r) (hcd : c ≠ d) (v : Fin N × Fin r) :
    glAct p L j c d (glAct p L j c d (X v)) = 0 := by
  obtain ⟨i, a⟩ := v
  rw [glAct_X_gen]
  split_ifs with h1 h2 h3 h3
  · rw [glAct_X_gen, if_pos h1, if_pos h2, if_neg hcd]
  · exact map_zero _
  · rw [map_neg, glAct_X_gen, if_pos h1, if_neg h2, if_neg (Ne.symm hcd), neg_zero]
  · exact map_zero _
  · exact map_zero _

/- English proof (translation)
Take `⟨x₀, rfl⟩` from `(FrozenVariableLemmas.intPol_iff p x).mp hx`. Use `clear hx`. Proceed by induction on `x₀ using MvPolynomial.induction_on generalizing k with`. Consider the case `C a`. Rewrite using `[map_C]`.

Consider the cases of `k with`. Consider the case `zero => simpa using (FrozenVariableLemmas.intPol_iff p _).mpr ⟨C a, map_C _ _⟩`. Consider the case `succ k`. Rewrite using `[pow_succ, Module.End.mul_apply, glAct_C', map_zero, smul_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add f g hf hg`. Rewrite using `[map_add, map_add, smul_add]`. Conclude with `Submodule.add_mem _ (hf k) (hg k)`. Consider the case `mul_X f v hf`. Rewrite using `[map_mul, map_X]`.

Consider the cases of `k with`. Consider the case `zero`. Use `hf 0` as an intermediate fact. Simplify using `only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, Module.End.one_apply, one_smul] at this ⊢`. Conclude with `FrozenVariableLemmas.intPol_mul p this (FrozenVariableLemmas.intPol_X p v)`.

Consider the case `succ k`. Rewrite using `[pow_succ_mul_gen (glAct p L j c d) (fun a b => Formalism.GM.M.FB.glAct_mul L j c d a b) rfl (glAct_glAct_X L j c d hcd v) k, smul_add, smul_smul]`. Establish `e : (((k + 1).factorial : ℚ_[p]))⁻¹ * ((k + 1 : ℕ) : ℚ_[p]) = ((k.factorial : ℚ_[p]))⁻¹`. Establish `h1 : ((k + 1 : ℕ) : ℚ_[p]) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero k`. Establish `h2 : ((k.factorial : ℕ) : ℚ_[p]) ≠ 0` using `by exact_mod_cast Nat.factorial_ne_zero k`.

Rewrite using `[Nat.factorial_succ, Nat.cast_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, ← smul_mul_assoc, ← smul_mul_assoc]`. Conclude with `Submodule.add_mem _ (FrozenVariableLemmas.intPol_mul p (hf (k + 1)) (FrozenVariableLemmas.intPol_X p v)) (FrozenVariableLemmas.intPol_mul p (hf k) (glAct_X_int L j c d v))`.
-/
theorem divpow_int (L : Letters N) (j : ℕ) (c d : Fin r) (hcd : c ≠ d) (k : ℕ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ IntPol p (Fin N × Fin r)) :
    (((k.factorial : ℚ_[p]))⁻¹) • ((glAct p L j c d) ^ k) x ∈ IntPol p (Fin N × Fin r) := by
  obtain ⟨x₀, rfl⟩ := (FrozenVariableLemmas.intPol_iff p x).mp hx
  clear hx
  induction x₀ using MvPolynomial.induction_on generalizing k with
  | C a =>
    rw [map_C]
    cases k with
    | zero => simpa using (FrozenVariableLemmas.intPol_iff p _).mpr ⟨C a, map_C _ _⟩
    | succ k =>
      rw [pow_succ, Module.End.mul_apply, glAct_C', map_zero, smul_zero]
      exact Submodule.zero_mem _
  | add f g hf hg =>
    rw [map_add, map_add, smul_add]
    exact Submodule.add_mem _ (hf k) (hg k)
  | mul_X f v hf =>
    rw [map_mul, map_X]
    cases k with
    | zero =>
      have := hf 0
      simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, Module.End.one_apply, one_smul] at this ⊢
      exact FrozenVariableLemmas.intPol_mul p this (FrozenVariableLemmas.intPol_X p v)
    | succ k =>
      rw [pow_succ_mul_gen (glAct p L j c d) (fun a b => Formalism.GM.M.FB.glAct_mul L j c d a b) rfl
        (glAct_glAct_X L j c d hcd v) k, smul_add, smul_smul]
      have e : (((k + 1).factorial : ℚ_[p]))⁻¹ * ((k + 1 : ℕ) : ℚ_[p]) = ((k.factorial : ℚ_[p]))⁻¹ := by
        have h1 : ((k + 1 : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
        have h2 : ((k.factorial : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
        rw [Nat.factorial_succ, Nat.cast_mul]
        field_simp
      rw [e, ← smul_mul_assoc, ← smul_mul_assoc]
      exact Submodule.add_mem _ (FrozenVariableLemmas.intPol_mul p (hf (k + 1)) (FrozenVariableLemmas.intPol_X p v))
        (FrozenVariableLemmas.intPol_mul p (hf k) (glAct_X_int L j c d v))

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => intro x`. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `x`.

Rewrite using `[pow_succ', Module.End.mul_apply, Module.End.mul_apply, hcomm, ih]`.
-/
theorem comm_pow (L : Letters N) (j0 : ℕ)
    (Tm : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hcomm : ∀ c d x, Tm (glAct p L j0 c d x) = glAct p L j0 c d (Tm x)) (c d : Fin r) (k : ℕ) :
    ∀ x, Tm (((glAct p L j0 c d) ^ k) x) = ((glAct p L j0 c d) ^ k) (Tm x) := by
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, hcomm, ih]

/- English proof (translation)
Take `⟨hP1, -⟩` from `hHP`. Establish `hsat : ∀ T : Set (Fin r → ℤ), CsSaturated (univ : Finset (Fin r)) T` using `fun T la la' h => by`. Rewrite using `[show la = la' from funext fun c => h c (mem_univ c)]`. Establish `htop : (⨆ la : Fin r → ℤ, IsoC p L j0 univ la) = ⊤`. Take `⟨P0, ⟨hPP, hran, hker⟩, -, -⟩` from `hP1 j0 hj0 univ (Or.inl rfl) Set.univ (hsat _)`.

Establish `hk : LinearMap.ker P0 = ⊥`. Rewrite using `[hker]`. Simplify using the standard rewrite rules. Establish `hid : ∀ x, P0 x = x`. Introduce `x`.

Establish `: P0 x - x ∈ LinearMap.ker P0`. Rewrite using `[LinearMap.mem_ker, map_sub, sub_eq_zero]`. Conclude with `LinearMap.congr_fun hPP x`. Rewrite `this` using `[hk, Submodule.mem_bot, sub_eq_zero]`. Conclude with `this`.

Establish `hr : LinearMap.range P0 = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Conclude with `⟨x, hid x⟩`. Rewrite using `[← hr, hran]`.

Simplify using the standard rewrite rules. Establish `hex : ∀ la : Fin r → ℤ, ∃ P, IsTypeProj p L j0 univ {la} P ∧ ∀ F ∈ PolZ p r L, ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin N × Fin r)` using `fun la => by`. Take `⟨P, h1, -, h3⟩` from `hP1 j0 hj0 univ (Or.inl rfl) {la} (hsat _)`. Conclude with `⟨P, h1, h3⟩`. Use `choose P hPt hPint using hex`.

Use `set S : Submodule ℤ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) := (IntPol p (Fin N × Fin r)).comap ((((p : ℚ_[p]) ^ K0) • Tm).restrictScalars ℤ_[p]) with hS`. Establish `hmemS : ∀ x, x ∈ S ↔ ((p : ℚ_[p]) ^ K0) • Tm x ∈ IntPol p (Fin N × Fin r)` using `fun x => Iff.rfl`. Establish `hWeyl : ∀ la : Fin r → ℤ, ∀ h, (h ∈ HWC p L j0 univ la ⊓ Pol p r L ∧ h ∈ IntPol p (Fin N × Fin r)) → WeylLat p L j0 h ≤ S`. Introduce `la h hh`. Use `sInf_le ⟨(hmemS h).mpr (hhw la h hh.1 hh.2), ?_⟩` and prove the remaining obligations.

Introduce `c d hcd k x hx`. Rewrite `hx`, the goal using `[hmemS]`. Rewrite using `[map_smul, comm_pow L j0 Tm hcomm c d k x, smul_comm, ← map_smul]`. Conclude with `divpow_int L j0 c d hcd k _ hx`. Introduce `y hy`.

Establish `hyP : y ∈ Pol p r L` using `(Submodule.mem_inf.mp hy).1`. Establish `hyT : y ∈ ⨆ la : Fin r → ℤ, IsoC p L j0 univ la` using `by rw [htop]; exact Submodule.mem_top`. Take `⟨f, hf, hsum⟩` from `(Submodule.mem_iSup_iff_exists_finsupp _ _).mp hyT`. Establish `hPfix : ∀ la, ∀ x ∈ IsoC p L j0 univ la, P la x = x`. Introduce `la x hx`.

Establish `: x ∈ LinearMap.range (P la)`. Rewrite using `[(hPt la).2.1]`. Conclude with `(le_iSup₂ (f := fun la' (_ : la' ∈ ({la} : Set (Fin r → ℤ))) => IsoC p L j0 univ la') la rfl) hx`. Take `⟨z, rfl⟩` from `this`. Conclude with `LinearMap.congr_fun (hPt la).1 z`.

Establish `hPkill : ∀ la mu, mu ≠ la → ∀ x ∈ IsoC p L j0 univ mu, P la x = 0`. Introduce `la mu hne x hx`. Establish `: x ∈ LinearMap.ker (P la)`. Rewrite using `[(hPt la).2.2]`. Conclude with `(le_iSup₂ (f := fun la' (_ : la' ∉ ({la} : Set (Fin r → ℤ))) => IsoC p L j0 univ la') mu hne) hx`.

Conclude with `this`. Establish `hPy : ∀ la, P la y = f la`. Introduce `la`. Rewrite using `[← hsum, Finsupp.sum, map_sum]`. Rewrite using `[Finset.sum_eq_single la]`.

Conclude with `hPfix la _ (hf la)`. Introduce `mu _ hne`. Conclude with `hPkill la mu hne _ (hf mu)`. Introduce `hla`. Rewrite using `[Finsupp.notMem_support_iff.mp hla, map_zero]`.

Establish `hterm : ∀ la, ((p : ℚ_[p]) ^ (K0 + 2 * e1)) • Tm (P la y) ∈ IntPol p (Fin N × Fin r)`. Introduce `la`. Establish `h1 : ((p : ℚ_[p]) ^ e1) • P la y ∈ IntPol p (Fin N × Fin r)` using `hPint la y hy`. Establish `h2 : ((p : ℚ_[p]) ^ e1) • P la y ∈ IsoC p L j0 univ la ⊓ Pol p r L` using `Submodule.smul_mem _ _ (Submodule.mem_inf.mpr ⟨by rw [hPy]; exact hf la, typeProj_pol L j0 {la} (P la) (hPt la) y hyP⟩)`. Establish `h3` using `hHW j0 hj0 la _ h2 h1`.

Establish `h4 : ((p : ℚ_[p]) ^ e1) • ((p : ℚ_[p]) ^ e1) • P la y ∈ S` using `(iSup₂_le fun h hh => hWeyl la h hh) h3`. Rewrite `h4` using `[hmemS, map_smul, map_smul, smul_smul, smul_smul]`. Establish `e : (p : ℚ_[p]) ^ (K0 + 2 * e1) = (p : ℚ_[p]) ^ K0 * (p : ℚ_[p]) ^ e1 * (p : ℚ_[p]) ^ e1`. Rewrite using `[pow_add, two_mul, pow_add, mul_assoc]`. Rewrite using `[e]`.

Conclude with `h4`. Establish `hy2 : y = ∑ la ∈ f.support, P la y` using `by conv_lhs => rw [← hsum, Finsupp.sum]`. Conclude with `Finset.sum_congr rfl fun la _ => (hPy la).symm`. Rewrite using `[hy2, map_sum, Finset.smul_sum]`. Conclude with `Submodule.sum_mem _ fun la _ => hterm la`.
-/
theorem int_main (L : Letters N) (ρ : Fin r) (e1 j0 : ℕ) (hj0 : j0 ≤ N) (hHP : HypP p L ρ e1) (hHW : HypW p (r := r) L e1)
    (Tm : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) (K0 : ℕ)
    (hcomm : ∀ c d x, Tm (glAct p L j0 c d x) = glAct p L j0 c d (Tm x))
    (hhw : ∀ la : Fin r → ℤ, ∀ h ∈ HWC p L j0 univ la ⊓ Pol p r L, h ∈ IntPol p (Fin N × Fin r) →
      ((p : ℚ_[p]) ^ K0) • Tm h ∈ IntPol p (Fin N × Fin r)) :
    ∀ y ∈ PolZ p r L, ((p : ℚ_[p]) ^ (K0 + 2 * e1)) • Tm y ∈ IntPol p (Fin N × Fin r) := by
  classical
  obtain ⟨hP1, -⟩ := hHP
  have hsat : ∀ T : Set (Fin r → ℤ), CsSaturated (univ : Finset (Fin r)) T := fun T la la' h => by
    rw [show la = la' from funext fun c => h c (mem_univ c)]

  have htop : (⨆ la : Fin r → ℤ, IsoC p L j0 univ la) = ⊤ := by
    obtain ⟨P0, ⟨hPP, hran, hker⟩, -, -⟩ := hP1 j0 hj0 univ (Or.inl rfl) Set.univ (hsat _)
    have hk : LinearMap.ker P0 = ⊥ := by
      rw [hker]; simp
    have hid : ∀ x, P0 x = x := by
      intro x
      have : P0 x - x ∈ LinearMap.ker P0 := by
        rw [LinearMap.mem_ker, map_sub, sub_eq_zero]; exact LinearMap.congr_fun hPP x
      rw [hk, Submodule.mem_bot, sub_eq_zero] at this
      exact this
    have hr : LinearMap.range P0 = ⊤ := by
      rw [eq_top_iff]; intro x _; exact ⟨x, hid x⟩
    rw [← hr, hran]; simp
  have hex : ∀ la : Fin r → ℤ, ∃ P, IsTypeProj p L j0 univ {la} P ∧
      ∀ F ∈ PolZ p r L, ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin N × Fin r) := fun la => by
    obtain ⟨P, h1, -, h3⟩ := hP1 j0 hj0 univ (Or.inl rfl) {la} (hsat _)
    exact ⟨P, h1, h3⟩
  choose P hPt hPint using hex

  set S : Submodule ℤ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
    (IntPol p (Fin N × Fin r)).comap ((((p : ℚ_[p]) ^ K0) • Tm).restrictScalars ℤ_[p]) with hS
  have hmemS : ∀ x, x ∈ S ↔ ((p : ℚ_[p]) ^ K0) • Tm x ∈ IntPol p (Fin N × Fin r) := fun x => Iff.rfl
  have hWeyl : ∀ la : Fin r → ℤ, ∀ h, (h ∈ HWC p L j0 univ la ⊓ Pol p r L ∧ h ∈ IntPol p (Fin N × Fin r)) →
      WeylLat p L j0 h ≤ S := by
    intro la h hh
    refine sInf_le ⟨(hmemS h).mpr (hhw la h hh.1 hh.2), ?_⟩
    intro c d hcd k x hx
    rw [hmemS] at hx ⊢
    rw [map_smul, comm_pow L j0 Tm hcomm c d k x, smul_comm, ← map_smul]
    exact divpow_int L j0 c d hcd k _ hx
  intro y hy
  have hyP : y ∈ Pol p r L := (Submodule.mem_inf.mp hy).1
  have hyT : y ∈ ⨆ la : Fin r → ℤ, IsoC p L j0 univ la := by rw [htop]; exact Submodule.mem_top
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hyT
  have hPfix : ∀ la, ∀ x ∈ IsoC p L j0 univ la, P la x = x := by
    intro la x hx
    have : x ∈ LinearMap.range (P la) := by
      rw [(hPt la).2.1]
      exact (le_iSup₂ (f := fun la' (_ : la' ∈ ({la} : Set (Fin r → ℤ))) => IsoC p L j0 univ la') la rfl) hx
    obtain ⟨z, rfl⟩ := this
    exact LinearMap.congr_fun (hPt la).1 z
  have hPkill : ∀ la mu, mu ≠ la → ∀ x ∈ IsoC p L j0 univ mu, P la x = 0 := by
    intro la mu hne x hx
    have : x ∈ LinearMap.ker (P la) := by
      rw [(hPt la).2.2]
      exact (le_iSup₂ (f := fun la' (_ : la' ∉ ({la} : Set (Fin r → ℤ))) => IsoC p L j0 univ la') mu hne) hx
    exact this
  have hPy : ∀ la, P la y = f la := by
    intro la
    rw [← hsum, Finsupp.sum, map_sum]
    rw [Finset.sum_eq_single la]
    · exact hPfix la _ (hf la)
    · intro mu _ hne; exact hPkill la mu hne _ (hf mu)
    · intro hla
      rw [Finsupp.notMem_support_iff.mp hla, map_zero]
  have hterm : ∀ la, ((p : ℚ_[p]) ^ (K0 + 2 * e1)) • Tm (P la y) ∈ IntPol p (Fin N × Fin r) := by
    intro la
    have h1 : ((p : ℚ_[p]) ^ e1) • P la y ∈ IntPol p (Fin N × Fin r) := hPint la y hy
    have h2 : ((p : ℚ_[p]) ^ e1) • P la y ∈ IsoC p L j0 univ la ⊓ Pol p r L :=
      Submodule.smul_mem _ _ (Submodule.mem_inf.mpr ⟨by rw [hPy]; exact hf la,
        typeProj_pol L j0 {la} (P la) (hPt la) y hyP⟩)
    have h3 := hHW j0 hj0 la _ h2 h1
    have h4 : ((p : ℚ_[p]) ^ e1) • ((p : ℚ_[p]) ^ e1) • P la y ∈ S :=
      (iSup₂_le fun h hh => hWeyl la h hh) h3
    rw [hmemS, map_smul, map_smul, smul_smul, smul_smul] at h4
    have e : (p : ℚ_[p]) ^ (K0 + 2 * e1) = (p : ℚ_[p]) ^ K0 * (p : ℚ_[p]) ^ e1 * (p : ℚ_[p]) ^ e1 := by
      rw [pow_add, two_mul, pow_add, mul_assoc]
    rw [e]; exact h4
  have hy2 : y = ∑ la ∈ f.support, P la y := by
    conv_lhs => rw [← hsum, Finsupp.sum]
    exact Finset.sum_congr rfl fun la _ => (hPy la).symm
  rw [hy2, map_sum, Finset.smul_sum]
  exact Submodule.sum_mem _ fun la _ => hterm la

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.GM.TM MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def FfL (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero N] (L : Letters N) (T : TieData) (i : Fin T.t) (ρ : Fin r)
    (n : ℕ) : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] where
  toFun := T.Ffull p L i ρ n
  map_add' := by
    intro f g
    simp only [TieData.Ffull, freeze, map_add, mul_add]
  map_smul' := by
    intro c f
    simp only [TieData.Ffull, freeze, map_smul, mul_smul_comm, RingHom.id_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem FfL_apply [NeZero N] (L : Letters N) (T : TieData) (i : Fin T.t) (ρ : Fin r) (n : ℕ)
    (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) : FfL p L T i ρ n f = T.Ffull p L i ρ n f := rfl

/- English proof (translation)
Rewrite using `[WtSpC, mem_restrictSupport_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h m hm`. Use function extensionality and compare the values at `c`. Rewrite using `[weight_wv]`.

Conclude with `h (Finset.mem_coe.mpr (mem_support_iff.mpr hm)) c (mem_univ c)`. Introduce `h m hm c _`. Rewrite using `[← weight_wv, h (mem_support_iff.mp (Finset.mem_coe.mp hm))]`.
-/
theorem wtsp_iff {M : ℕ} (L : Letters M) (j : ℕ) (la : Fin r → ℤ) (x : MvPolynomial (Fin M × Fin r) ℚ_[p]) :
    x ∈ WtSpC p L j univ la ↔ IsWeightedHomogeneous (wv L j) x la := by
  rw [WtSpC, mem_restrictSupport_iff]
  constructor
  · intro h m hm
    funext c
    rw [weight_wv]
    exact h (Finset.mem_coe.mpr (mem_support_iff.mpr hm)) c (mem_univ c)
  · intro h m hm c _
    rw [← weight_wv, h (mem_support_iff.mp (Finset.mem_coe.mp hm))]

/- English proof (translation)
Take `⟨P, rfl⟩` from `LinearMap.mem_range.mp hy`. Use `LinearMap.mem_range.mpr ⟨rename e P, ?_⟩` and prove the remaining obligations. Simplify using `only [AlgHom.toLinearMap_apply, mapAlgHom_apply, map_rename]`.
-/
theorem intPol_rename {σ τ : Type} (e : σ → τ) {y : MvPolynomial σ ℚ_[p]} (hy : y ∈ IntPol p σ) :
    rename e y ∈ IntPol p τ := by
  obtain ⟨P, rfl⟩ := LinearMap.mem_range.mp hy
  refine LinearMap.mem_range.mpr ⟨rename e P, ?_⟩
  simp only [AlgHom.toLinearMap_apply, mapAlgHom_apply, map_rename]

section Comparison₂

variable [NeZero N] [NeZero r] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t) (ρ : Fin r)
  (hρ : (ρ : ℕ) = r - 1) (n : Fin T.t → ℕ) (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i)

include hadm hS

/- English proof (translation)
Take `⟨hP, hI⟩` from `Submodule.mem_inf.mp hf`. Establish `h1` using `(Formalism.GM.extendMapsTo p (T.pos i + 1) r _ ρ (n i) hS f hP).2.2 hI`. Rewrite using `[Ffull_eq]`. Conclude with `intPol_rename _ h1`.
-/
theorem Ffull_int (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hf : f ∈ PolZ p r ((LL.setTies T n).takeD (T.pos i + 1))) :
    T.Ffull p (LL.setTies T n) i ρ (n i) f ∈ IntPol p (Fin N × Fin r) := by
  obtain ⟨hP, hI⟩ := Submodule.mem_inf.mp hf
  have h1 := (Formalism.GM.extendMapsTo p (T.pos i + 1) r _ ρ (n i) hS f hP).2.2 hI
  rw [Ffull_eq]
  exact intPol_rename _ h1

/- English proof (translation)
Establish `hP : f ∈ Pol p r ((LL.setTies T n).takeD (T.pos i + 1))` using `(Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).1).1`. Use `Submodule.mem_inf.mpr ⟨Ffull_pol LL T hadm i ρ n f hP hS, (Submodule.mem_iInf _).mpr fun k => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hk : T.J k < T.pos i + 1 + 1`. Rewrite using `[Mup, if_pos hk]`. Conclude with `Ffull_ycond LL T hadm i ρ n w f hf hS k (by omega)`.

Rewrite using `[Mup, if_neg hk, Formalism.GM.DimensionMonotonicity.ycond_top]`. Conclude with `Submodule.mem_top`.
-/
theorem Ffull_C (w : Fin r → ℤ) (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hf : f ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) :
    T.Ffull p (LL.setTies T n) i ρ (n i) f ∈ Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr := by
  have hP : f ∈ Pol p r ((LL.setTies T n).takeD (T.pos i + 1)) :=
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).1).1
  refine Submodule.mem_inf.mpr ⟨Ffull_pol LL T hadm i ρ n f hP hS, (Submodule.mem_iInf _).mpr fun k => ?_⟩
  by_cases hk : T.J k < T.pos i + 1 + 1
  · rw [Mup, if_pos hk]
    exact Ffull_ycond LL T hadm i ρ n w f hf hS k (by omega)
  · rw [Mup, if_neg hk, Formalism.GM.DimensionMonotonicity.ycond_top]; exact Submodule.mem_top

/- English proof (translation)
Establish `hK` using `hK_of_adm LL T hadm i`. Rewrite `h0` using `[Ffull_eq]`. Establish `h1 : freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) f = 0`. Apply `rename_injective _ (inclusion_prodMap_injective (r := r) hK)` to reduce the goal to its premises. Rewrite using `[h0, map_zero]`.

Conclude with `(Formalism.GM.extendBijOn p (T.pos i + 1) r ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) hS).1 f hP 0 (Submodule.zero_mem _) (by rw [h1, freeze_zero])`.
-/
theorem Ffull_inj (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hP : f ∈ Pol p r ((LL.setTies T n).takeD (T.pos i + 1)))
    (h0 : T.Ffull p (LL.setTies T n) i ρ (n i) f = 0) : f = 0 := by
  have hK := hK_of_adm LL T hadm i
  rw [Ffull_eq] at h0
  have h1 : freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) f = 0 := by
    apply rename_injective _ (inclusion_prodMap_injective (r := r) hK)
    rw [h0, map_zero]
  exact (Formalism.GM.extendBijOn p (T.pos i + 1) r ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) hS).1 f hP 0
    (Submodule.zero_mem _) (by rw [h1, freeze_zero])

omit hS in
/- English proof (translation)
Establish `hK` using `hK_of_adm LL T hadm i`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last`. Rewrite using `[Formalism.GM.M.FB.snoc_deg_last]`. Establish `: ιF N (T.pos i + 1) (Fin.last (T.pos i + 1)) = ⟨T.pos i + 1, by omega⟩`.

Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[ιF_val hK]`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `setTies_deg_eta LL T hadm i n _`.

Consider the case `cast a`. Rewrite using `[Formalism.GM.M.FB.snoc_deg_castSucc]`. Establish `: ιF N (T.pos i + 1) (Fin.castSucc a) = ⟨a, by omega⟩`. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[ιF_val hK]`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Simplify using `[Letters.takeD, (by omega : (a : ℕ) < N)]`.
-/
theorem deg_compat (a : Fin (T.pos i + 1 + 1)) :
    (LL.setTies T n).deg (ιF N (T.pos i + 1) a) = (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)).deg a := by
  have hK := hK_of_adm LL T hadm i
  induction a using Fin.lastCases with
  | last =>
    rw [Formalism.GM.M.FB.snoc_deg_last]
    have : ιF N (T.pos i + 1) (Fin.last (T.pos i + 1)) = ⟨T.pos i + 1, by omega⟩ := by
      apply Fin.ext; rw [ιF_val hK]; simp
    rw [this]; exact setTies_deg_eta LL T hadm i n _
  | cast a =>
    rw [Formalism.GM.M.FB.snoc_deg_castSucc]
    have : ιF N (T.pos i + 1) (Fin.castSucc a) = ⟨a, by omega⟩ := by
      apply Fin.ext; rw [ιF_val hK]; simp
    rw [this]
    simp [Letters.takeD, (by omega : (a : ℕ) < N)]

omit hS in

/- English proof (translation)
Establish `hK` using `hK_of_adm LL T hadm i`. Establish `hι` using `inclusion_prodMap_injective (N := N) (r := r) hK`. Use `set S : Submodule ℚ_[p] (MvPolynomial (Fin (T.pos i + 1 + 1) × Fin r) ℚ_[p]) := (YCond p LL J M).comap (rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2))).toLinearMap with hSd`. Establish `hle : S ≤ YCond p (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) J M`. Use `le_sSup ⟨?_, ?_⟩` and prove the remaining obligations.

Introduce `G hG`. Rewrite using `[mem_restrictSupport_iff]`. Introduce `m hm`. Establish `h1` using `Formalism.CountingSumsFrames.ycond_le_supp LL J M (Submodule.mem_comap.mp hG)`. Rewrite `h1` using `[mem_restrictSupport_iff]`.

Establish `h2 : Finsupp.mapDomain (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) m ∈ (rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) G).support`. Rewrite using `[support_rename_of_injective hι]`. Conclude with `Finset.mem_image_of_mem _ hm`. Establish `h3 : ((wt LL J 0 (Finsupp.mapDomain (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) m) : ℤ) : WithTop ℤ) ≤ M` using `h1 (Finset.mem_coe.mpr h2)`. Rewrite `h3` using `[← weight_wv, weight_mapDomain, wv_compat LL T hadm i n (n i), weight_wv]`.

Conclude with `h3`. Introduce `c d G hG`. Rewrite using `[hSd, Submodule.mem_comap, AlgHom.toLinearMap_apply, glAct_rename (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) LL (ιF N (T.pos i + 1)) (ιF_val hK) (fun a => vec_compat LL T hadm i n (n i) a) J c d G]`. Conclude with `Formalism.CountingSumsFrames.ycond_glStable LL J M c d _ (Submodule.mem_comap.mp hG)`. Conclude with `hle (Submodule.mem_comap.mpr h)`.
-/
theorem ycond_pull (J : ℕ) (M : WithTop ℤ) (F : MvPolynomial (Fin (T.pos i + 1 + 1) × Fin r) ℚ_[p])
    (h : rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) F ∈ YCond p LL J M) :
    F ∈ YCond p (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) J M := by
  classical
  have hK := hK_of_adm LL T hadm i
  have hι := inclusion_prodMap_injective (N := N) (r := r) hK
  set S : Submodule ℚ_[p] (MvPolynomial (Fin (T.pos i + 1 + 1) × Fin r) ℚ_[p]) := (YCond p LL J M).comap
    (rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2))).toLinearMap with hSd
  have hle : S ≤ YCond p (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) J M := by
    refine le_sSup ⟨?_, ?_⟩
    · intro G hG
      rw [mem_restrictSupport_iff]
      intro m hm
      have h1 := Formalism.CountingSumsFrames.ycond_le_supp LL J M (Submodule.mem_comap.mp hG)
      rw [mem_restrictSupport_iff] at h1
      have h2 : Finsupp.mapDomain (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) m ∈
          (rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) G).support := by
        rw [support_rename_of_injective hι]; exact Finset.mem_image_of_mem _ hm
      have h3 : ((wt LL J 0 (Finsupp.mapDomain (fun x : Fin (T.pos i + 1 + 1) × Fin r =>
          (ιF N (T.pos i + 1) x.1, x.2)) m) : ℤ) : WithTop ℤ) ≤ M := h1 (Finset.mem_coe.mpr h2)
      rw [← weight_wv, weight_mapDomain, wv_compat LL T hadm i n (n i), weight_wv] at h3
      exact h3
    · intro c d G hG
      rw [hSd, Submodule.mem_comap, AlgHom.toLinearMap_apply,
        glAct_rename (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) LL (ιF N (T.pos i + 1)) (ιF_val hK)
          (fun a => vec_compat LL T hadm i n (n i) a) J c d G]
      exact Formalism.CountingSumsFrames.ycond_glStable LL J M c d _ (Submodule.mem_comap.mp hG)
  exact hle (Submodule.mem_comap.mpr h)

include hρ

/- English proof (translation)
Establish `hK` using `hK_of_adm LL T hadm i`. Use `set LLK := (LL.setTies T n).takeD (T.pos i + 1) with hLLK`. Set `ι : Fin (T.pos i + 1 + 1) × Fin r → Fin N × Fin r` to `fun x => (ιF N (T.pos i + 1) x.1, x.2)`. Establish `hι : Function.Injective ι` using `inclusion_prodMap_injective (r := r) hK`. Take `⟨hvP, hvY⟩` from `Submodule.mem_inf.mp hv`.

Establish `hvF` using `isF_of_polLz _ _ hvP`. Choose the witnesses or unpack the hypotheses as in `⟨F, hF⟩ : ∃ F, rename ι F = v := by`. Apply `exists_rename_eq_of_vars_subset_range v ι hι` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx` using `[Finset.mem_coe, mem_vars]`.

Take `⟨m, hm, hxm⟩` from `hx`. Establish `hlt : (x.1 : ℕ) < T.pos i + 1 + 1` using `hvF m hm x (Finsupp.mem_support_iff.mp hxm)`. Conclude with `⟨(⟨x.1, hlt⟩, x.2), Prod.ext (Fin.ext (ιF_val hK _)) rfl⟩`. Establish `hsupp : ∀ m ∈ F.support, Finsupp.mapDomain ι m ∈ v.support`. Introduce `m hm`.

Rewrite using `[← hF, support_rename_of_injective hι]`. Conclude with `Finset.mem_image_of_mem _ hm`. Establish `hFP : F ∈ Pol p r (LLK.snoc (n i))`. Rewrite using `[Pol, mem_restrictSupport_iff]`. Introduce `m hm a`.

Establish `h1 : MultiDeg (Lz (LL.setTies T n) (T.pos i + 1 + 1)) (Finsupp.mapDomain ι m)` using `((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hvP) (Finset.mem_coe.mpr (hsupp m hm))`. Establish `h2` using `h1 (ιF N (T.pos i + 1) a)`. Establish `h3 : ∀ c, Finsupp.mapDomain ι m (ιF N (T.pos i + 1) a, c) = m (a, c)` using `fun c => Finsupp.mapDomain_apply hι m (a, c)`. Simplify using `only [h3] at h2`. Rewrite using `[h2]`.

Simplify using `only [Lz]`. Rewrite using `[if_pos (by rw [ιF_val hK]; exact a.isLt), deg_compat LL T hadm i n]`. Establish `hFI : F ∈ IntPol p (Fin (T.pos i + 1 + 1) × Fin r)` using `mem_intPol_of_norm _ fun m => by`. Use `Formalism.CountingSumsFrames.intPol_norm v hint (Finsupp.mapDomain ι m)` as an intermediate fact. Rewrite `this` using `[← hF, coeff_rename_mapDomain ι hι]`. Then use the resulting hypothesis.

Establish `hgl : ∀ J c d, rename ι (glAct p (LLK.snoc (n i)) J c d F) = glAct p LL J c d v`. Introduce `J c d`. Rewrite using `[← hF]`. Conclude with `glAct_rename (LLK.snoc (n i)) LL (ιF N (T.pos i + 1)) (ιF_val hK) (fun a => vec_compat LL T hadm i n (n i) a) J c d F`. Establish `hraise : ∀ a b, a < b → glAct p (LLK.snoc (n i)) (T.pos i + 1 + 1) a b F = 0`.

Introduce `a b hab`. Apply `rename_injective ι hι` to reduce the goal to its premises. Rewrite using `[hgl, map_zero]`. Conclude with `hw.2 a b hab`. Establish `hinv : IsFrozenInv p LLK ρ (n i) F` using `fun c hc => hraise c ρ (Fin.lt_def.mpr (by`.

Use `c.isLt` as an intermediate fact. Establish `: (c : ℕ) ≠ ρ` using `fun h => hc (Fin.ext h)`. Use the proof step `omega))`. Take `⟨f, hfZ, hfF⟩` from `(Formalism.GM.extendBijOn p (T.pos i + 1) r LLK ρ (n i) hS).2 F (Submodule.mem_inf.mpr ⟨hFP, hFI⟩) hinv`. Establish `hfP : f ∈ Pol p r LLK` using `(Submodule.mem_inf.mp hfZ).1`.

Set `J' : Fin T.q → ℕ` to `fun k => min (T.J k) (T.pos i + 1)`. Establish `hFY : freeze p LLK ρ (n i) f ∈ Y p (LLK.snoc (n i)) J' (T.thrUpTo i)`. Rewrite using `[hfF]`. Use `Submodule.mem_inf.mpr ⟨hFP, (Submodule.mem_iInf _).mpr fun k => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hk : T.J k ≤ T.pos i + 1`.

Establish `e1 : J' k = T.J k` using `min_eq_left hk`. Establish `e2 : T.thrUpTo i k = T.thr k` using `by simp [TieData.thrUpTo, hk]`. Rewrite using `[e1, e2]`. Apply `ycond_pull LL T hadm i n` to reduce the goal to its premises. Establish `h1` using `(Submodule.mem_iInf _).mp hvY k`.

Rewrite `h1` using `[Mup, if_pos (by omega)]`. Rewrite `h1` using `[← hF]`. Conclude with `h1`. Establish `ht : T.thrUpTo i k = ⊤` using `by simp [TieData.thrUpTo, hk]`. Rewrite using `[ht, Formalism.GM.DimensionMonotonicity.ycond_top]`.

Conclude with `Submodule.mem_top`. Establish `hfY'` using `(Formalism.GM.extendWeightBounded p (T.pos i + 1) r LLK ρ (n i) J' (T.thrUpTo i) hS (fun k => min_le_right _ _) f hfP).mpr hFY`. Establish `hfY : f ∈ Y p LLK T.J (T.thrUpTo i)`. Use `Submodule.mem_inf.mpr ⟨hfP, (Submodule.mem_iInf _).mpr fun k => ?_⟩` and prove the remaining obligations. Establish `h1` using `(Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hfY').2 k`.

Distinguish the cases in `hk : T.J k ≤ T.pos i + 1`. Simplify `h1` using `[J', min_eq_left hk]`. Establish `ht : T.thrUpTo i k = ⊤` using `by simp [TieData.thrUpTo, hk]`. Rewrite using `[ht, Formalism.GM.DimensionMonotonicity.ycond_top]`. Conclude with `Submodule.mem_top`.

Use `set w : Fin r → ℤ := μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1 with hwd`. Establish `hvW : IsWeightedHomogeneous (wv LL (T.pos i + 1 + 1)) v μ`. Establish `h1` using `weightedHomogeneousComponent_isWeightedHomogeneous (R := ℚ_[p]) (w := wv LL (T.pos i + 1 + 1)) μ v`. Establish `h2 : weightedHomogeneousComponent (wv LL (T.pos i + 1 + 1)) μ v = v` using `hw.1`. Rewrite `h1` using `[h2]`. Then use the resulting hypothesis.

Establish `hFw : IsWeightedHomogeneous (wv (LLK.snoc (n i)) (T.pos i + 1 + 1)) F μ`. Introduce `m hm`. Establish `h1` using `hvW (mem_support_iff.mp (hsupp m (mem_support_iff.mpr hm)))`. Rewrite `h1` using `[weight_mapDomain, wv_compat LL T hadm i n (n i)]`. Then use the resulting hypothesis. Establish `hcP : ∀ w', weightedHomogeneousComponent (wv LLK (T.pos i + 1)) w' f ∈ Pol p r LLK`.

Introduce `w'`. Rewrite `hfP`, the goal using `[pol_iff]`. Conclude with `(mem_weightedHomogeneousSubmodule _ _ _ _).mp (whc_keep _ _ w' _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hfP))`. Establish `hcW : ∀ w', IsWeightedHomogeneous (wv (LLK.snoc (n i)) (T.pos i + 1 + 1)) (freeze p LLK ρ (n i) (weightedHomogeneousComponent (wv LLK (T.pos i + 1)) w' f)) (w' - ((n i : ℕ) : ℤ) • Pi.single ρ 1)` using `fun w' => freeze_wh LLK ρ (n i) hS w' _ (hcP w') ((wtsp_iff LLK (T.pos i + 1) w' _).mpr (weightedHomogeneousComponent_isWeightedHomogeneous w' f))`. Establish `hcomp : f = weightedHomogeneousComponent (wv LLK (T.pos i + 1)) w f`.

Take `⟨S, hS0⟩` from `(GA p LLK (T.pos i + 1)).dec f`. Establish `hS' : ∀ μ' ∉ S, weightedHomogeneousComponent (wv LLK (T.pos i + 1)) μ' f = 0` using `hS0`. Establish `hsum : ∑ μ' ∈ S, weightedHomogeneousComponent (wv LLK (T.pos i + 1)) μ' f = f` using `(GA p LLK (T.pos i + 1)).sum_comp f S hS0`. Establish `hfr : freeze p LLK ρ (n i) f = ∑ w' ∈ S, freeze p LLK ρ (n i) (weightedHomogeneousComponent (wv LLK (T.pos i + 1)) w' f)` using `by conv_lhs => rw [← hsum]`. Simplify using `only [freeze, map_sum, Finset.mul_sum]`.

Establish `h5 : F = freeze p LLK ρ (n i) (weightedHomogeneousComponent (wv LLK (T.pos i + 1)) w f)`. Establish `h6 : weightedHomogeneousComponent (wv (LLK.snoc (n i)) (T.pos i + 1 + 1)) μ F = F`. Rewrite using `[weightedHomogeneousComponent_of_mem hFw, if_pos rfl]`. Rewrite using `[← h6, ← hfF, hfr, map_sum]`. Simplify using `only [weightedHomogeneousComponent_of_mem (hcW _)]`.

Establish `hiff : ∀ w', μ = w' - ((n i : ℕ) : ℤ) • Pi.single ρ 1 ↔ w' = w`. Introduce `w'`. Rewrite using `[hwd]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Rewrite using `[h]`. Normalize the expressions using the abelian group laws. Introduce `h`. Rewrite using `[h]`. Normalize the expressions using the abelian group laws.

Simplify using `only [hiff]`. Rewrite using `[Finset.sum_ite_eq' S w]`. Use `split_ifs with hwS`. Both sides reduce to the same expression. Rewrite using `[hS' w hwS, freeze_zero]`.

Conclude with `(Formalism.GM.extendBijOn p (T.pos i + 1) r LLK ρ (n i) hS).1 f hfP _ (hcP w) (by rw [hfF, ← h5])`. Establish `hfW : f ∈ WtSpC p LLK (T.pos i + 1) univ w`. Rewrite using `[wtsp_iff, hcomp]`. Conclude with `weightedHomogeneousComponent_isWeightedHomogeneous w f`. Establish `hfH : f ∈ HWC p LLK (T.pos i + 1) (univ.erase ρ) w`.

Use `Submodule.mem_inf.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite `hfW`, the goal using `[WtSpC, mem_restrictSupport_iff]`. Introduce `m hm c _`. Conclude with `hfW hm c (mem_univ c)`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker]`.

Introduce `a b hab`. Establish `ha : a ≠ ρ` using `(Finset.mem_erase.mp hab.1).1`. Establish `hb : b ≠ ρ` using `(Finset.mem_erase.mp hab.2.1).1`. Establish `h1` using `glAct_freeze_gen LLK (n i) ρ a b ha hb f`. Rewrite `h1` using `[hfF, hraise a b hab.2.2]`.

Conclude with `(Formalism.GM.extendBijOn p (T.pos i + 1) r LLK ρ (n i) hS).1 _ (Formalism.GM.DimensionMonotonicity.glAct_pol LLK LLK (T.pos i + 1) a b hfP) 0 (Submodule.zero_mem _) (by rw [← h1, freeze_zero])`. Use `⟨f, Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hfY, hfH⟩, hfW⟩, (Submodule.mem_inf.mp hfZ).2⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Ffull_eq, hfF]`. Conclude with `hF.symm`.
-/
theorem hw_is_Ffull (μ : Fin r → ℤ) (v : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hv : v ∈ Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr)
    (hw : (GA p (LL.setTies T n) (T.pos i + 1 + 1)).IsHW μ v) (hint : v ∈ IntPol p (Fin N × Fin r)) :
    ∃ f ∈ MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1),
      v = T.Ffull p (LL.setTies T n) i ρ (n i) f := by
  classical
  have hK := hK_of_adm LL T hadm i
  set LLK := (LL.setTies T n).takeD (T.pos i + 1) with hLLK
  let ι : Fin (T.pos i + 1 + 1) × Fin r → Fin N × Fin r := fun x => (ιF N (T.pos i + 1) x.1, x.2)
  have hι : Function.Injective ι := inclusion_prodMap_injective (r := r) hK
  obtain ⟨hvP, hvY⟩ := Submodule.mem_inf.mp hv
  have hvF := isF_of_polLz _ _ hvP
  obtain ⟨F, hF⟩ : ∃ F, rename ι F = v := by
    apply exists_rename_eq_of_vars_subset_range v ι hι
    intro x hx
    rw [Finset.mem_coe, mem_vars] at hx
    obtain ⟨m, hm, hxm⟩ := hx
    have hlt : (x.1 : ℕ) < T.pos i + 1 + 1 := hvF m hm x (Finsupp.mem_support_iff.mp hxm)
    exact ⟨(⟨x.1, hlt⟩, x.2), Prod.ext (Fin.ext (ιF_val hK _)) rfl⟩
  have hsupp : ∀ m ∈ F.support, Finsupp.mapDomain ι m ∈ v.support := by
    intro m hm; rw [← hF, support_rename_of_injective hι]; exact Finset.mem_image_of_mem _ hm
  have hFP : F ∈ Pol p r (LLK.snoc (n i)) := by
    rw [Pol, mem_restrictSupport_iff]
    intro m hm a
    have h1 : MultiDeg (Lz (LL.setTies T n) (T.pos i + 1 + 1)) (Finsupp.mapDomain ι m) :=
      ((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hvP) (Finset.mem_coe.mpr (hsupp m hm))
    have h2 := h1 (ιF N (T.pos i + 1) a)
    have h3 : ∀ c, Finsupp.mapDomain ι m (ιF N (T.pos i + 1) a, c) = m (a, c) :=
      fun c => Finsupp.mapDomain_apply hι m (a, c)
    simp only [h3] at h2
    rw [h2]
    simp only [Lz]
    rw [if_pos (by rw [ιF_val hK]; exact a.isLt), deg_compat LL T hadm i n]
  have hFI : F ∈ IntPol p (Fin (T.pos i + 1 + 1) × Fin r) := mem_intPol_of_norm _ fun m => by
    have := Formalism.CountingSumsFrames.intPol_norm v hint (Finsupp.mapDomain ι m)
    rwa [← hF, coeff_rename_mapDomain ι hι] at this
  have hgl : ∀ J c d, rename ι (glAct p (LLK.snoc (n i)) J c d F) = glAct p LL J c d v := by
    intro J c d
    rw [← hF]
    exact glAct_rename (LLK.snoc (n i)) LL (ιF N (T.pos i + 1)) (ιF_val hK)
      (fun a => vec_compat LL T hadm i n (n i) a) J c d F
  have hraise : ∀ a b, a < b → glAct p (LLK.snoc (n i)) (T.pos i + 1 + 1) a b F = 0 := by
    intro a b hab
    apply rename_injective ι hι
    rw [hgl, map_zero]
    exact hw.2 a b hab
  have hinv : IsFrozenInv p LLK ρ (n i) F := fun c hc => hraise c ρ (Fin.lt_def.mpr (by
    have := c.isLt
    have : (c : ℕ) ≠ ρ := fun h => hc (Fin.ext h)
    omega))
  obtain ⟨f, hfZ, hfF⟩ := (Formalism.GM.extendBijOn p (T.pos i + 1) r LLK ρ (n i) hS).2 F
    (Submodule.mem_inf.mpr ⟨hFP, hFI⟩) hinv
  have hfP : f ∈ Pol p r LLK := (Submodule.mem_inf.mp hfZ).1
  let J' : Fin T.q → ℕ := fun k => min (T.J k) (T.pos i + 1)
  have hFY : freeze p LLK ρ (n i) f ∈ Y p (LLK.snoc (n i)) J' (T.thrUpTo i) := by
    rw [hfF]
    refine Submodule.mem_inf.mpr ⟨hFP, (Submodule.mem_iInf _).mpr fun k => ?_⟩
    by_cases hk : T.J k ≤ T.pos i + 1
    · have e1 : J' k = T.J k := min_eq_left hk
      have e2 : T.thrUpTo i k = T.thr k := by simp [TieData.thrUpTo, hk]
      rw [e1, e2]
      apply ycond_pull LL T hadm i n
      have h1 := (Submodule.mem_iInf _).mp hvY k
      rw [Mup, if_pos (by omega)] at h1
      rw [← hF] at h1
      exact h1
    · have ht : T.thrUpTo i k = ⊤ := by simp [TieData.thrUpTo, hk]
      rw [ht, Formalism.GM.DimensionMonotonicity.ycond_top]; exact Submodule.mem_top
  have hfY' := (Formalism.GM.extendWeightBounded p (T.pos i + 1) r LLK ρ (n i) J' (T.thrUpTo i) hS
    (fun k => min_le_right _ _) f hfP).mpr hFY
  have hfY : f ∈ Y p LLK T.J (T.thrUpTo i) := by
    refine Submodule.mem_inf.mpr ⟨hfP, (Submodule.mem_iInf _).mpr fun k => ?_⟩
    have h1 := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hfY').2 k
    by_cases hk : T.J k ≤ T.pos i + 1
    · simpa [J', min_eq_left hk] using h1
    · have ht : T.thrUpTo i k = ⊤ := by simp [TieData.thrUpTo, hk]
      rw [ht, Formalism.GM.DimensionMonotonicity.ycond_top]; exact Submodule.mem_top

  set w : Fin r → ℤ := μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1 with hwd
  have hvW : IsWeightedHomogeneous (wv LL (T.pos i + 1 + 1)) v μ := by
    have h1 := weightedHomogeneousComponent_isWeightedHomogeneous (R := ℚ_[p]) (w := wv LL (T.pos i + 1 + 1)) μ v
    have h2 : weightedHomogeneousComponent (wv LL (T.pos i + 1 + 1)) μ v = v := hw.1
    rwa [h2] at h1
  have hFw : IsWeightedHomogeneous (wv (LLK.snoc (n i)) (T.pos i + 1 + 1)) F μ := by
    intro m hm
    have h1 := hvW (mem_support_iff.mp (hsupp m (mem_support_iff.mpr hm)))
    rwa [weight_mapDomain, wv_compat LL T hadm i n (n i)] at h1
  have hcP : ∀ w', weightedHomogeneousComponent (wv LLK (T.pos i + 1)) w' f ∈ Pol p r LLK := by
    intro w'
    rw [pol_iff] at hfP ⊢
    exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp
      (whc_keep _ _ w' _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hfP))
  have hcW : ∀ w', IsWeightedHomogeneous (wv (LLK.snoc (n i)) (T.pos i + 1 + 1))
      (freeze p LLK ρ (n i) (weightedHomogeneousComponent (wv LLK (T.pos i + 1)) w' f))
      (w' - ((n i : ℕ) : ℤ) • Pi.single ρ 1) := fun w' =>
    freeze_wh LLK ρ (n i) hS w' _ (hcP w')
      ((wtsp_iff LLK (T.pos i + 1) w' _).mpr (weightedHomogeneousComponent_isWeightedHomogeneous w' f))
  have hcomp : f = weightedHomogeneousComponent (wv LLK (T.pos i + 1)) w f := by
    obtain ⟨S, hS0⟩ := (GA p LLK (T.pos i + 1)).dec f
    have hS' : ∀ μ' ∉ S, weightedHomogeneousComponent (wv LLK (T.pos i + 1)) μ' f = 0 := hS0
    have hsum : ∑ μ' ∈ S, weightedHomogeneousComponent (wv LLK (T.pos i + 1)) μ' f = f :=
      (GA p LLK (T.pos i + 1)).sum_comp f S hS0
    have hfr : freeze p LLK ρ (n i) f =
        ∑ w' ∈ S, freeze p LLK ρ (n i) (weightedHomogeneousComponent (wv LLK (T.pos i + 1)) w' f) := by
      conv_lhs => rw [← hsum]
      simp only [freeze, map_sum, Finset.mul_sum]
    have h5 : F = freeze p LLK ρ (n i) (weightedHomogeneousComponent (wv LLK (T.pos i + 1)) w f) := by
      have h6 : weightedHomogeneousComponent (wv (LLK.snoc (n i)) (T.pos i + 1 + 1)) μ F = F := by
        rw [weightedHomogeneousComponent_of_mem hFw, if_pos rfl]
      rw [← h6, ← hfF, hfr, map_sum]
      simp only [weightedHomogeneousComponent_of_mem (hcW _)]
      have hiff : ∀ w', μ = w' - ((n i : ℕ) : ℤ) • Pi.single ρ 1 ↔ w' = w := by
        intro w'; rw [hwd]; constructor
        · intro h; rw [h]; abel
        · intro h; rw [h]; abel
      simp only [hiff]
      rw [Finset.sum_ite_eq' S w]
      split_ifs with hwS
      · rfl
      · rw [hS' w hwS, freeze_zero]
    exact (Formalism.GM.extendBijOn p (T.pos i + 1) r LLK ρ (n i) hS).1 f hfP _ (hcP w) (by rw [hfF, ← h5])
  have hfW : f ∈ WtSpC p LLK (T.pos i + 1) univ w := by
    rw [wtsp_iff, hcomp]
    exact weightedHomogeneousComponent_isWeightedHomogeneous w f
  have hfH : f ∈ HWC p LLK (T.pos i + 1) (univ.erase ρ) w := by
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [WtSpC, mem_restrictSupport_iff] at hfW ⊢
      intro m hm c _
      exact hfW hm c (mem_univ c)
    · simp only [Submodule.mem_iInf, LinearMap.mem_ker]
      intro a b hab
      have ha : a ≠ ρ := (Finset.mem_erase.mp hab.1).1
      have hb : b ≠ ρ := (Finset.mem_erase.mp hab.2.1).1
      have h1 := glAct_freeze_gen LLK (n i) ρ a b ha hb f
      rw [hfF, hraise a b hab.2.2] at h1
      exact (Formalism.GM.extendBijOn p (T.pos i + 1) r LLK ρ (n i) hS).1 _
        (Formalism.GM.DimensionMonotonicity.glAct_pol LLK LLK (T.pos i + 1) a b hfP) 0 (Submodule.zero_mem _) (by rw [← h1, freeze_zero])
  refine ⟨f, Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hfY, hfH⟩, hfW⟩,
    (Submodule.mem_inf.mp hfZ).2⟩, ?_⟩
  rw [Ffull_eq, hfF]
  exact hF.symm

omit hρ

/- English proof (translation)
Use `set LLK := (LL.setTies T n).takeD (T.pos i + 1) with hLLK`. Establish `hPf : ∀ w a, f w a ∈ Pol p r LLK` using `fun w a => (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp (hf w a)).1).1).1`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc x0`. Establish `h1 : T.Ffull p (LL.setTies T n) i ρ (n i) (∑ x : (Σ w : Ω, Fin (nb w.1)), c x • f x.1.1 x.2) = 0`.

Rewrite using `[← FfL_apply, map_sum, ← hc]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, FfL_apply]`. Establish `hsumP : (∑ x : (Σ w : Ω, Fin (nb w.1)), c x • f x.1.1 x.2) ∈ Pol p r LLK` using `Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (hPf _ _)`. Establish `h2` using `Ffull_inj LL T hadm i ρ n hS _ hsumP h1`.

Establish `h3` using `congrArg (weightedHomogeneousComponent (wv LLK (T.pos i + 1)) x0.1.1) h2`. Rewrite `h3` using `[map_sum, map_zero, Fintype.sum_sigma]`. Establish `h4 : ∀ (w : Ω) (a : Fin (nb w.1)), weightedHomogeneousComponent (wv LLK (T.pos i + 1)) x0.1.1 (c ⟨w, a⟩ • f w.1 a) = if x0.1 = w then c ⟨w, a⟩ • f w.1 a else 0`. Introduce `w a`. Establish `hW : IsWeightedHomogeneous (wv LLK (T.pos i + 1)) (f w.1 a) w.1` using `(wtsp_iff LLK (T.pos i + 1) w.1 _).mp (Submodule.mem_inf.mp (hf w.1 a)).2`.

Rewrite using `[map_smul, weightedHomogeneousComponent_of_mem hW]`. Distinguish the cases in `h : x0.1 = w`. Rewrite using `[if_pos h, if_pos (congrArg Subtype.val h)]`. Rewrite using `[if_neg h, if_neg (fun h' => h (Subtype.ext h')), smul_zero]`. Simplify using `only [h4] at h3`.

Rewrite `h3` using `[Finset.sum_eq_single x0.1 (fun w _ hw => by simp [Ne.symm hw]) (fun h => absurd (Finset.mem_univ _) h)]`. Simplify using `only [if_true] at h3`. Use `Fintype.linearIndependent_iff.mp (hli x0.1.1) (fun a => c ⟨x0.1, a⟩) h3 x0.2` as an intermediate fact. Simplify using `using this`.
-/
theorem Ffull_indep (Ω : Finset (Fin r → ℤ)) (nb : (Fin r → ℤ) → ℕ)
    (f : ∀ w, Fin (nb w) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hf : ∀ w a, f w a ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w)
    (hli : ∀ w, LinearIndependent ℚ_[p] (f w)) :
    LinearIndependent ℚ_[p] (fun x : (Σ w : Ω, Fin (nb w.1)) => T.Ffull p (LL.setTies T n) i ρ (n i) (f x.1.1 x.2)) := by
  classical
  set LLK := (LL.setTies T n).takeD (T.pos i + 1) with hLLK
  have hPf : ∀ w a, f w a ∈ Pol p r LLK := fun w a =>
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp (hf w a)).1).1).1
  rw [Fintype.linearIndependent_iff]
  intro c hc x0
  have h1 : T.Ffull p (LL.setTies T n) i ρ (n i) (∑ x : (Σ w : Ω, Fin (nb w.1)), c x • f x.1.1 x.2) = 0 := by
    rw [← FfL_apply, map_sum, ← hc]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_smul, FfL_apply]
  have hsumP : (∑ x : (Σ w : Ω, Fin (nb w.1)), c x • f x.1.1 x.2) ∈ Pol p r LLK :=
    Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (hPf _ _)
  have h2 := Ffull_inj LL T hadm i ρ n hS _ hsumP h1
  have h3 := congrArg (weightedHomogeneousComponent (wv LLK (T.pos i + 1)) x0.1.1) h2
  rw [map_sum, map_zero, Fintype.sum_sigma] at h3
  have h4 : ∀ (w : Ω) (a : Fin (nb w.1)),
      weightedHomogeneousComponent (wv LLK (T.pos i + 1)) x0.1.1 (c ⟨w, a⟩ • f w.1 a) =
        if x0.1 = w then c ⟨w, a⟩ • f w.1 a else 0 := by
    intro w a
    have hW : IsWeightedHomogeneous (wv LLK (T.pos i + 1)) (f w.1 a) w.1 :=
      (wtsp_iff LLK (T.pos i + 1) w.1 _).mp (Submodule.mem_inf.mp (hf w.1 a)).2
    rw [map_smul, weightedHomogeneousComponent_of_mem hW]
    by_cases h : x0.1 = w
    · rw [if_pos h, if_pos (congrArg Subtype.val h)]
    · rw [if_neg h, if_neg (fun h' => h (Subtype.ext h')), smul_zero]
  simp only [h4] at h3
  rw [Finset.sum_eq_single x0.1 (fun w _ hw => by simp [Ne.symm hw]) (fun h => absurd (Finset.mem_univ _) h)] at h3
  simp only [if_true] at h3
  have := Fintype.linearIndependent_iff.mp (hli x0.1.1) (fun a => c ⟨x0.1, a⟩) h3 x0.2
  simpa using this

omit hadm hS

/- English proof (translation)
Use `((pol_finite (r := r) ((LL.setTies T n).takeD (T.pos i + 1))).image (fun m => fun c => wt ((LL.setTies T n).takeD (T.pos i + 1)) (T.pos i + 1) c m)).subset ?_` and prove the remaining obligations. Introduce `w hw`. Take `⟨f, hf, hf0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hw`. Establish `hP : f ∈ Pol p r ((LL.setTies T n).takeD (T.pos i + 1))` using `(Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).1).1`. Establish `hW` using `(Submodule.mem_inf.mp hf).2`.

Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m, m ∈ f.support := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hf0 (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))`. Rewrite `hP` using `[Pol, mem_restrictSupport_iff]`.

Rewrite `hW` using `[WtSpC, mem_restrictSupport_iff]`. Conclude with `⟨m, hP (Finset.mem_coe.mpr hm), funext fun c => hW (Finset.mem_coe.mpr hm) c (mem_univ c)⟩`.
-/
theorem mmw_finite :
    {w : Fin r → ℤ | MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ≠ ⊥}.Finite := by
  classical
  refine ((pol_finite (r := r) ((LL.setTies T n).takeD (T.pos i + 1))).image
    (fun m => fun c => wt ((LL.setTies T n).takeD (T.pos i + 1)) (T.pos i + 1) c m)).subset ?_
  intro w hw
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hw
  have hP : f ∈ Pol p r ((LL.setTies T n).takeD (T.pos i + 1)) :=
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).1).1
  have hW := (Submodule.mem_inf.mp hf).2
  obtain ⟨m, hm⟩ : ∃ m, m ∈ f.support := by
    by_contra hc; push Not at hc
    exact hf0 (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))
  rw [Pol, mem_restrictSupport_iff] at hP
  rw [WtSpC, mem_restrictSupport_iff] at hW
  exact ⟨m, hP (Finset.mem_coe.mpr hm), funext fun c => hW (Finset.mem_coe.mpr hm) c (mem_univ c)⟩

end Comparison₂

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

structure IsEqC [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) : Prop where
  comm : ∀ x ∈ Cset p L j0 J M, ∀ a b, φ (glAct p L j0 a b x) = glAct p L j0 a b (φ x)
  mem : ∀ x ∈ Cset p L j0 J M, φ x ∈ Cset p L j0 J M

noncomputable def inOp (L : Letters N) (j0 : ℕ)
    (Pi φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  φ ∘ₗ Pi ∘ₗ psi p L j0

noncomputable def bigOp (L : Letters N) (j0 : ℕ)
    (Pi φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  ext (fsj N r j0) (inOp L j0 Pi φ)

section Gen

variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]

/- English proof (translation)
Proceed by induction on `x using MvPolynomial.induction_on' with`. Consider the case `monomial m' a`. Rewrite using `[ext_monomial, map_smul, sl_mul fs m (hφ _) (isL_monomial_ltr fs m' 1), sl_monomial, coeff_monomial]`. Use `split_ifs with h`. Rewrite using `[one_smul, ← map_smul, smul_monomial, smul_eq_mul, mul_one]`.

Rewrite using `[zero_smul, smul_zero, map_zero]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem slc_ext (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) (hφ : ∀ x, IsF fs (φ x)) (m : σ →₀ ℕ)
    (x : MvPolynomial σ K) : slc fs m (ext fs φ x) = φ (slc fs m x) := by
  classical
  induction x using MvPolynomial.induction_on' with
  | monomial m' a =>
    rw [ext_monomial, map_smul, sl_mul fs m (hφ _) (isL_monomial_ltr fs m' 1), sl_monomial, coeff_monomial]
    split_ifs with h
    · rw [one_smul, ← map_smul, smul_monomial, smul_eq_mul, mul_one]
    · rw [zero_smul, smul_zero, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]

end Gen

/- English proof (translation)
Rewrite using `[x.as_sum, map_sum]`. Use `Submodule.sum_mem _ fun m' _ => ?_` and prove the remaining obligations. Rewrite using `[sl_monomial]`. Use `split_ifs`. Use `TM.mem_intPol_of_norm _ fun k => ?_` and prove the remaining obligations.

Rewrite using `[coeff_monomial]`. Use `split_ifs`. Conclude with `intPol_norm x hx m'`. Simplify using the standard rewrite rules. Conclude with `Submodule.zero_mem _`.
-/
theorem slc_int (j0 : ℕ) (m : Fin N × Fin r →₀ ℕ) {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ IntPol p (Fin N × Fin r)) : slc (fsj N r j0) m x ∈ IntPol p (Fin N × Fin r) := by
  classical
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m' _ => ?_
  rw [sl_monomial]
  split_ifs
  · refine TM.mem_intPol_of_norm _ fun k => ?_
    rw [coeff_monomial]
    split_ifs
    · exact intPol_norm x hx m'
    · simp
  · exact Submodule.zero_mem _

/- English proof (translation)
Use `TM.mem_intPol_of_norm _ fun k => ?_` and prove the remaining obligations. Use `intPol_norm _ h (k + m)` as an intermediate fact. Rewrite `this` using `[coeff_mul_monomial, mul_one]`. Then use the resulting hypothesis.
-/
theorem int_of_mul_monomial {σ : Type} (g : MvPolynomial σ ℚ_[p]) (m : σ →₀ ℕ)
    (h : g * monomial m 1 ∈ IntPol p σ) : g ∈ IntPol p σ := by
  refine TM.mem_intPol_of_norm _ fun k => ?_
  have := intPol_norm _ h (k + m)
  rwa [coeff_mul_monomial, mul_one] at this

/- English proof (translation)
Unfold `Formalism.GM.M.IntPol`. Conclude with `LinearMap.mem_range.mpr ⟨monomial m 1, by simp [MvPolynomial.mapAlgHom_apply, MvPolynomial.map_monomial]⟩`.
-/
theorem int_monomial_one {σ : Type} (m : σ →₀ ℕ) : (monomial m 1 : MvPolynomial σ ℚ_[p]) ∈ IntPol p σ := by
  unfold Formalism.GM.M.IntPol
  exact LinearMap.mem_range.mpr ⟨monomial m 1, by simp [MvPolynomial.mapAlgHom_apply, MvPolynomial.map_monomial]⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : weightedHomogeneousComponent (wv L j) ν x = x` using `h`. Rewrite using `[← h']`. Conclude with `weightedHomogeneousComponent_mem _ _ _`.

Introduce `h show weightedHomogeneousComponent (wv L j) ν x = x`. Rewrite using `[weightedHomogeneousComponent_of_mem h, if_pos rfl]`.
-/
theorem isWt_iff_wh (L : Letters N) (j : ℕ) (ν : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    (GA p L j).IsWt ν x ↔ x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j) ν := by
  constructor
  · intro h
    have h' : weightedHomogeneousComponent (wv L j) ν x = x := h
    rw [← h']
    exact weightedHomogeneousComponent_mem _ _ _
  · intro h
    show weightedHomogeneousComponent (wv L j) ν x = x
    rw [weightedHomogeneousComponent_of_mem h, if_pos rfl]

section

variable [NeZero r] (L : Letters N) (j0 e : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
  (Pi φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
  (hPi : IsProjC L j0 e J M Pi) (hφ : IsEqC L j0 J M φ)

include hPi

/- English proof (translation)
The claim follows from `Submodule.mem_inf.mpr ⟨hPi.pol (Lz L j0) rfl _ (psi_mem L j0 x), (Submodule.mem_iInf _).mpr fun k => hPi.ycond _ k⟩`.
-/
theorem piPsi_mem (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) : Pi (psi p L j0 x) ∈ Cset p L j0 J M :=
  Submodule.mem_inf.mpr ⟨hPi.pol (Lz L j0) rfl _ (psi_mem L j0 x), (Submodule.mem_iInf _).mpr fun k => hPi.ycond _ k⟩

/- English proof (translation)
Take `⟨h1, h2⟩` from `Submodule.mem_inf.mp hg`. Simplify using `only [inOp, LinearMap.comp_apply]`. Rewrite using `[psi_id L j0 h1, hPi.fix (Lz L j0) rfl g h1 (fun k => (Submodule.mem_iInf _).mp h2 k)]`.
-/
theorem inOp_C (g : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hg : g ∈ Cset p L j0 J M) : inOp L j0 Pi φ g = φ g := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hg
  simp only [inOp, LinearMap.comp_apply]
  rw [psi_id L j0 h1, hPi.fix (Lz L j0) rfl g h1 (fun k => (Submodule.mem_iInf _).mp h2 k)]

include hφ

/- English proof (translation)
Conclude with `hφ.mem _ (piPsi_mem L j0 e J M Pi hPi x)`.
-/
theorem inOp_mem (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) : inOp L j0 Pi φ x ∈ Cset p L j0 J M := by
  exact hφ.mem _ (piPsi_mem L j0 e J M Pi hPi x)

/- English proof (translation)
Conclude with `isF_of_polLz L j0 (Submodule.mem_inf.mp (inOp_mem L j0 e J M Pi φ hPi hφ x)).1`.
-/
theorem inOp_isF (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) : IsF (fsj N r j0) (inOp L j0 Pi φ x) := by
  exact isF_of_polLz L j0 (Submodule.mem_inf.mp (inOp_mem L j0 e J M Pi φ hPi hφ x)).1

/- English proof (translation)
Simplify using `only [inOp, LinearMap.comp_apply]`. Rewrite using `[psi_glAct, hPi.comm, hφ.comm _ (piPsi_mem L j0 e J M Pi hPi x)]`.
-/
theorem inOp_glAct (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    inOp L j0 Pi φ (glAct p L j0 c d x) = glAct p L j0 c d (inOp L j0 Pi φ x) := by
  simp only [inOp, LinearMap.comp_apply]
  rw [psi_glAct, hPi.comm, hφ.comm _ (piPsi_mem L j0 e J M Pi hPi x)]

/- English proof (translation)
Rewrite `hw`, the goal using `[← isWt_iff_wh]`. Use `GlX.isWt_of_eig (GA p L j0) fun c => ?_` and prove the remaining obligations. Establish `h1 : glAct p L j0 c c y = ((ν c : ℤ) : ℚ_[p]) • y` using `(GA p L j0).E_diag_of_isWt hw c`. Use `show glAct p L j0 c c (φ y) = _`. Rewrite using `[← hφ.comm y hy, h1, map_smul]`.
-/
theorem eqC_wh (ν : Fin r → ℤ) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hy : y ∈ Cset p L j0 J M)
    (hw : y ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν) :
    φ y ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν := by
  rw [← isWt_iff_wh] at hw ⊢
  refine GlX.isWt_of_eig (GA p L j0) fun c => ?_
  have h1 : glAct p L j0 c c y = ((ν c : ℤ) : ℚ_[p]) • y := (GA p L j0).E_diag_of_isWt hw c
  show glAct p L j0 c c (φ y) = _
  rw [← hφ.comm y hy, h1, map_smul]

/- English proof (translation)
Simplify using `only [inOp, LinearMap.comp_apply]`. Conclude with `eqC_wh L j0 e J M Pi φ hPi hφ ν _ (piPsi_mem L j0 e J M Pi hPi x) (hPi.wh ν _ (whc_keep _ _ _ _ hx))`.
-/
theorem inOp_wh (ν : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν) :
    inOp L j0 Pi φ x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν := by
  simp only [inOp, LinearMap.comp_apply]
  exact eqC_wh L j0 e J M Pi φ hPi hφ ν _ (piPsi_mem L j0 e J M Pi hPi x) (hPi.wh ν _ (whc_keep _ _ _ _ hx))

/- English proof (translation)
Conclude with `ext_glAct L le_rfl _ (inOp_glAct L j0 e J M Pi φ hPi hφ) (inOp_isF L j0 e J M Pi φ hPi hφ) c d x`.
-/
theorem bigOp_glAct (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    bigOp L j0 Pi φ (glAct p L j0 c d x) = glAct p L j0 c d (bigOp L j0 Pi φ x) := by
  exact ext_glAct L le_rfl _ (inOp_glAct L j0 e J M Pi φ hPi hφ) (inOp_isF L j0 e J M Pi φ hPi hφ) c d x

/- English proof (translation)
Conclude with `ext_Y L j0 J M _ (inOp_glAct L j0 e J M Pi φ hPi hφ) (inOp_wh L j0 e J M Pi φ hPi hφ) (fun x => (Submodule.mem_inf.mp (inOp_mem L j0 e J M Pi φ hPi hφ x)).1) (fun x _ => inOp_mem L j0 e J M Pi φ hPi hφ x)`.
-/
theorem bigOp_Y : ∀ y ∈ Y p L J M, bigOp L j0 Pi φ y ∈ Y p L J M := by
  exact ext_Y L j0 J M _ (inOp_glAct L j0 e J M Pi φ hPi hφ) (inOp_wh L j0 e J M Pi φ hPi hφ)
    (fun x => (Submodule.mem_inf.mp (inOp_mem L j0 e J M Pi φ hPi hφ x)).1)
    (fun x _ => inOp_mem L j0 e J M Pi φ hPi hφ x)

/- English proof (translation)
Conclude with `slc_ext _ _ (inOp_isF L j0 e J M Pi φ hPi hφ) m x`.
-/
theorem bigOp_slc (m : Fin N × Fin r →₀ ℕ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    slc (fsj N r j0) m (bigOp L j0 Pi φ x) = inOp L j0 Pi φ (slc (fsj N r j0) m x) := by
  exact slc_ext _ _ (inOp_isF L j0 e J M Pi φ hPi hφ) m x

/- English proof (translation)
Rewrite using `[bigOp, ext_eq_sum (fsj N r j0) _ x (x.support.image (ltr (fsj N r j0))) (fun m hm => Finset.mem_image_of_mem _ hm)]`. Use `Submodule.sum_mem _ fun m hm => Submodule.subset_span ?_` and prove the remaining obligations. Take `⟨m', _, rfl⟩` from `Finset.mem_image.mp hm`. Use `⟨_, hVF _ (piPsi_mem L j0 e J M Pi hPi (slc (fsj N r j0) (ltr (fsj N r j0) m') x)), _, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[mem_supported, vars_monomial one_ne_zero]`.

Introduce `v hv`. Use `ltr_isL (fsj N r j0) m' v (Finsupp.mem_support_iff.mp (Finset.mem_coe.mp hv))` as an intermediate fact. Simplify using `only [fsj, not_lt] at this`. Conclude with `this`.
-/
theorem bigOp_span (VF : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hVF : ∀ g ∈ Cset p L j0 J M, φ g ∈ VF) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    bigOp L j0 Pi φ x ∈ Submodule.span ℚ_[p] {x | ∃ g ∈ VF,
      ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | j0 ≤ (v.1 : ℕ)}, x = g * q} := by
  classical
  rw [bigOp, ext_eq_sum (fsj N r j0) _ x (x.support.image (ltr (fsj N r j0)))
    (fun m hm => Finset.mem_image_of_mem _ hm)]
  refine Submodule.sum_mem _ fun m hm => Submodule.subset_span ?_
  obtain ⟨m', _, rfl⟩ := Finset.mem_image.mp hm
  refine ⟨_, hVF _ (piPsi_mem L j0 e J M Pi hPi (slc (fsj N r j0) (ltr (fsj N r j0) m') x)), _, ?_, rfl⟩
  rw [mem_supported, vars_monomial one_ne_zero]
  intro v hv
  have := ltr_isL (fsj N r j0) m' v (Finsupp.mem_support_iff.mp (Finset.mem_coe.mp hv))
  simp only [fsj, not_lt] at this
  exact this

/- English proof (translation)
Take `⟨hxH, hxP⟩` from `Submodule.mem_inf.mp hx`. Take `⟨hxW, hxE⟩` from `(isHW_iff L j0 la x).mpr hxH`. Rewrite using `[bigOp, ext_eq_sum (fsj N r j0) _ x (x.support.image (ltr (fsj N r j0))) (fun m hm => Finset.mem_image_of_mem _ hm), Finset.smul_sum]`. Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Take `⟨m', hm', rfl⟩` from `Finset.mem_image.mp hm`.

Use `set s := slc (fsj N r j0) (ltr (fsj N r j0) m') x with hs`. Establish `hsP : s ∈ Pol p r (Lz L j0)` using `slc_pol L j0 _ hxP`. Establish `hsI : s ∈ IntPol p (Fin N × Fin r)` using `slc_int j0 _ hxi`. Establish `hmd : MultiDeg L m'` using `((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hxP) hm'`. Establish `hsm : s * monomial (ltr (fsj N r j0) m') 1 ∈ PolZ p r L` using `Submodule.mem_inf.mpr ⟨mul_ltr_pol L j0 hsP hmd, FrozenVariableLemmas.intPol_mul p hsI (int_monomial_one _)⟩`.

Establish `h1` using `hPi.int _ hsm`. Rewrite `h1` using `[hPi.mul _ _ (isL_monomial_ltr (fsj N r j0) m' 1), ← smul_mul_assoc]`. Establish `hvI : ((p : ℚ_[p]) ^ e) • Pi s ∈ IntPol p (Fin N × Fin r)` using `int_of_mul_monomial _ _ h1`. Establish `hPs : Pi s ∈ Cset p L j0 J M`. Use `piPsi_mem L j0 e J M Pi hPi s` as an intermediate fact.

Rewrite `this` using `[psi_id L j0 hsP]`. Then use the resulting hypothesis. Establish `hvC : ((p : ℚ_[p]) ^ e) • Pi s ∈ Cset p L j0 J M` using `Submodule.smul_mem _ _ hPs`. Establish `hsW : s ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) la` using `slc_wh L le_rfl _ ((isWt_iff_wh L j0 la x).mp hxW)`. Establish `hvH : (GA p L j0).IsHW la (((p : ℚ_[p]) ^ e) • Pi s)`. Use `⟨(isWt_iff_wh L j0 la _).mpr (Submodule.smul_mem _ _ (hPi.wh la _ hsW)), fun a b hab => ?_⟩` and prove the remaining obligations.

Use `show glAct p L j0 a b _ = 0`. Establish `h0 : glAct p L j0 a b x = 0` using `hxE a b hab`. Rewrite using `[map_smul, ← hPi.comm, hs, ← slc_glAct L le_rfl a b, h0, map_zero, map_zero, smul_zero]`. Establish `h2` using `hint la _ hvC hvH hvI`. Rewrite `h2` using `[map_smul]`.

Establish `e3 : inOp L j0 Pi φ s = φ (Pi s)`. Simplify using `only [inOp, LinearMap.comp_apply]`. Rewrite using `[psi_id L j0 hsP]`. Rewrite using `[e3, ← smul_mul_assoc]`. Conclude with `FrozenVariableLemmas.intPol_mul p h2 (int_monomial_one _)`.
-/
theorem bigOp_int
    (hint : ∀ μ v, v ∈ Cset p L j0 J M → (GA p L j0).IsHW μ v → v ∈ IntPol p (Fin N × Fin r) →
      φ v ∈ IntPol p (Fin N × Fin r))
    (la : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ HWC p L j0 univ la ⊓ Pol p r L)
    (hxi : x ∈ IntPol p (Fin N × Fin r)) :
    ((p : ℚ_[p]) ^ e) • bigOp L j0 Pi φ x ∈ IntPol p (Fin N × Fin r) := by
  classical
  obtain ⟨hxH, hxP⟩ := Submodule.mem_inf.mp hx
  obtain ⟨hxW, hxE⟩ := (isHW_iff L j0 la x).mpr hxH
  rw [bigOp, ext_eq_sum (fsj N r j0) _ x (x.support.image (ltr (fsj N r j0)))
    (fun m hm => Finset.mem_image_of_mem _ hm), Finset.smul_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  obtain ⟨m', hm', rfl⟩ := Finset.mem_image.mp hm
  set s := slc (fsj N r j0) (ltr (fsj N r j0) m') x with hs
  have hsP : s ∈ Pol p r (Lz L j0) := slc_pol L j0 _ hxP
  have hsI : s ∈ IntPol p (Fin N × Fin r) := slc_int j0 _ hxi
  have hmd : MultiDeg L m' := ((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hxP) hm'
  have hsm : s * monomial (ltr (fsj N r j0) m') 1 ∈ PolZ p r L :=
    Submodule.mem_inf.mpr ⟨mul_ltr_pol L j0 hsP hmd, FrozenVariableLemmas.intPol_mul p hsI (int_monomial_one _)⟩
  have h1 := hPi.int _ hsm
  rw [hPi.mul _ _ (isL_monomial_ltr (fsj N r j0) m' 1), ← smul_mul_assoc] at h1
  have hvI : ((p : ℚ_[p]) ^ e) • Pi s ∈ IntPol p (Fin N × Fin r) := int_of_mul_monomial _ _ h1
  have hPs : Pi s ∈ Cset p L j0 J M := by
    have := piPsi_mem L j0 e J M Pi hPi s
    rwa [psi_id L j0 hsP] at this
  have hvC : ((p : ℚ_[p]) ^ e) • Pi s ∈ Cset p L j0 J M := Submodule.smul_mem _ _ hPs
  have hsW : s ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) la :=
    slc_wh L le_rfl _ ((isWt_iff_wh L j0 la x).mp hxW)
  have hvH : (GA p L j0).IsHW la (((p : ℚ_[p]) ^ e) • Pi s) := by
    refine ⟨(isWt_iff_wh L j0 la _).mpr (Submodule.smul_mem _ _ (hPi.wh la _ hsW)), fun a b hab => ?_⟩
    show glAct p L j0 a b _ = 0
    have h0 : glAct p L j0 a b x = 0 := hxE a b hab
    rw [map_smul, ← hPi.comm, hs, ← slc_glAct L le_rfl a b, h0, map_zero, map_zero, smul_zero]
  have h2 := hint la _ hvC hvH hvI
  rw [map_smul] at h2
  have e3 : inOp L j0 Pi φ s = φ (Pi s) := by
    simp only [inOp, LinearMap.comp_apply]; rw [psi_id L j0 hsP]
  rw [e3, ← smul_mul_assoc]
  exact FrozenVariableLemmas.intPol_mul p h2 (int_monomial_one _)

end

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def YYs [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (v : MvPolynomial (Fin N × Fin r) ℚ_[p]) : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  Y p L J M ⊓ Submodule.span ℚ_[p] {x | ∃ g ∈ (GA p L j0).gS {v},
      ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | j0 ≤ (v.1 : ℕ)}, x = g * q}

/- English proof (translation)
Establish `hx` using `eq_sum_sl fs x ((x.support ∪ y.support).image (ltr fs)) (fun m hm => Finset.mem_image_of_mem _ (Finset.mem_union_left _ hm))`. Establish `hy` using `eq_sum_sl fs y ((x.support ∪ y.support).image (ltr fs)) (fun m hm => Finset.mem_image_of_mem _ (Finset.mem_union_right _ hm))`. Conclude with `hx.trans ((Finset.sum_congr rfl fun m _ => by rw [hxy m]).trans hy.symm)`.
-/
theorem eq_of_slc {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]
    (x y : MvPolynomial σ K) (hxy : ∀ m, slc fs m x = slc fs m y) : x = y := by
  classical
  have hx := eq_sum_sl fs x ((x.support ∪ y.support).image (ltr fs))
    (fun m hm => Finset.mem_image_of_mem _ (Finset.mem_union_left _ hm))
  have hy := eq_sum_sl fs y ((x.support ∪ y.support).image (ltr fs))
    (fun m hm => Finset.mem_image_of_mem _ (Finset.mem_union_right _ hm))
  exact hx.trans ((Finset.sum_congr rfl fun m _ => by rw [hxy m]).trans hy.symm)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Establish `: (⨆ i ∈ (∅ : Finset ι), A i : Submodule K V) = ⊥` using `by simp`. Rewrite using `[this]`. Simplify using the standard rewrite rules.

Consider the case `insert a s ha ih`. Rewrite using `[Finset.iSup_insert, Finset.sum_insert ha]`. Establish `: FiniteDimensional K (A a)` using `Submodule.finiteDimensional_of_le (hA a)`. Establish `: FiniteDimensional K (⨆ i ∈ s, A i : Submodule K V)` using `Submodule.finiteDimensional_of_le (iSup₂_le fun i _ => hA i)`. Conclude with `(Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left ih _)`.
-/
theorem finrank_biSup_le {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] (Yv : Submodule K V)
    [FiniteDimensional K Yv] (A : ι → Submodule K V) (hA : ∀ i, A i ≤ Yv) (s : Finset ι) :
    Module.finrank K (⨆ i ∈ s, A i : Submodule K V) ≤ ∑ i ∈ s, Module.finrank K (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : (⨆ i ∈ (∅ : Finset ι), A i : Submodule K V) = ⊥ := by simp
    rw [this]; simp
  | insert a s ha ih =>
    rw [Finset.iSup_insert, Finset.sum_insert ha]
    have : FiniteDimensional K (A a) := Submodule.finiteDimensional_of_le (hA a)
    have : FiniteDimensional K (⨆ i ∈ s, A i : Submodule K V) :=
      Submodule.finiteDimensional_of_le (iSup₂_le fun i _ => hA i)
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left ih _)

/- English proof (translation)
Unfold `Formalism.GM.DimensionMonotonicity.GlW.IsHW Formalism.GM.DimensionMonotonicity.GlW.IsWt`. Conclude with `⟨map_zero _, fun a b _ => map_zero _⟩`.
-/
theorem isHW_zero {K V : Type} [Field K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r) (μ : Fin r → ℤ) :
    G.IsHW μ 0 := by
  unfold Formalism.GM.DimensionMonotonicity.GlW.IsHW Formalism.GM.DimensionMonotonicity.GlW.IsWt
  exact ⟨map_zero _, fun a b _ => map_zero _⟩

/- English proof (translation)
Take `⟨S, hS⟩` from `polynomial_finite_weights (p := p) (r := r) L j0`. Conclude with `⟨S, fun x hx => hS x (Submodule.mem_inf.mp hx).1⟩`.
-/
theorem C_finW [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) :
    (GA p (r := r) L j0).FinW (Cset p L j0 J M) := by
  obtain ⟨S, hS⟩ := polynomial_finite_weights (p := p) (r := r) L j0
  exact ⟨S, fun x hx => hS x (Submodule.mem_inf.mp hx).1⟩

/- English proof (translation)
Use `pol_fd (p := p) (r := r) L` as an intermediate fact. Conclude with `Submodule.finiteDimensional_of_le (inf_le_left : Y p (r := r) L J M ≤ Pol p r L)`.
-/
theorem Y_fd [NeZero r] (L : Letters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) :
    FiniteDimensional ℚ_[p] (Y p (r := r) L J M) := by
  have := pol_fd (p := p) (r := r) L
  exact Submodule.finiteDimensional_of_le (inf_le_left : Y p (r := r) L J M ≤ Pol p r L)

/- English proof (translation)
Take `⟨s, a, hs, ha, rfl⟩` from `rep_span VF j0 hz`. Rewrite using `[map_sum]`. Use `Submodule.sum_mem _ fun b hb => ?_` and prove the remaining obligations. Establish `hL : IsL (fsj N r j0) (monomial b (1 : ℚ_[p]))`. Introduce `m' hm' v hv hfs`.

Establish `: m' = b` using `Finset.mem_singleton.mp (support_monomial_subset hm')`. Substitute `this` using the available equality. Conclude with `hv (hs m' hb v hfs)`. Rewrite using `[sl_mul (fsj N r j0) m (isF_of_polLz L j0 (hVF (ha b))) hL]`. Conclude with `VF.smul_mem _ (ha b)`.
-/
theorem slc_span (L : Letters N) (j0 : ℕ) (VF : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hVF : VF ≤ Pol p r (Lz L j0)) {z : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hz : z ∈ Submodule.span ℚ_[p] {x | ∃ g ∈ VF,
      ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | j0 ≤ (v.1 : ℕ)}, x = g * q})
    (m : Fin N × Fin r →₀ ℕ) : slc (fsj N r j0) m z ∈ VF := by
  classical
  obtain ⟨s, a, hs, ha, rfl⟩ := rep_span VF j0 hz
  rw [map_sum]
  refine Submodule.sum_mem _ fun b hb => ?_
  have hL : IsL (fsj N r j0) (monomial b (1 : ℚ_[p])) := by
    intro m' hm' v hv hfs
    have : m' = b := Finset.mem_singleton.mp (support_monomial_subset hm')
    subst this
    exact hv (hs m' hb v hfs)
  rw [sl_mul (fsj N r j0) m (isF_of_polLz L j0 (hVF (ha b))) hL]
  exact VF.smul_mem _ (ha b)

section

variable [NeZero r] (L : Letters N) (j0 e : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
  (Pi : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
  (hPi : IsProjC L j0 e J M Pi)
  {ι : Type} [Fintype ι] [DecidableEq ι] (h : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]) (la : ι → Fin r → ℤ)
  (hh : ∀ i, (GA p L j0).IsHW (la i) (h i)) (hhC : ∀ i, h i ∈ Cset p L j0 J M)
  (hli : LinearIndependent ℚ_[p] h) (hsp : Cset p (r := r) L j0 J M ≤ ⨆ i, (GA p L j0).gS {h i})

include hPi hh hhC hli hsp

/- English proof (translation)
Establish `hex : ∀ i : ι, ∃ φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p], IsEqC L j0 J M φ ∧ (∀ x ∈ (GA p (r` using `r) L j0).gS {h i}, φ x = x) ∧ (∀ k, k ≠ i → ∀ x ∈ (GA p (r := r) L j0).gS {h k}, φ x = 0) := by`. Introduce `i`. Take `⟨φ, -, hφE, hφC, -, -, hφ1, hφ0⟩` from `GlX.eqExt (GA p (r := r) L j0) (C_stable L j0 J M) (C_finW L j0 J M) h (fun k => if k = i then h k else 0) la hh hhC hli hsp (fun k => by`. Distinguish the cases in `hk : k = i`. Simplify `hh i` using `[hk]`.

Simplify `isHW_zero (GA p (r := r) L j0) (la k))` using `[hk]`. Use the proof step `(fun k => by`. Distinguish the cases in `hk : k = i`. Simplify `hhC i` using `[hk]`. Simplify using `[hk])`.

Conclude with `⟨φ, ⟨hφE, hφC⟩, hφ1 i (by simp), fun k hk => hφ0 k (by simp [hk])⟩`. Use `choose π hπEq hπ1 hπ0 using hex`. Establish `hπVF : ∀ i, ∀ g ∈ Cset p L j0 J M, π i g ∈ (GA p (r` using `r) L j0).gS {h i} := by`. Introduce `i g hg`. Use `Submodule.iSup_induction _ (motive := fun x => π i x ∈ (GA p (r := r) L j0).gS {h i}) (hsp hg) ?_ (by simp) (fun x y hx hy => by rw [map_add]; exact add_mem hx hy)` and prove the remaining obligations.

Introduce `k x hx`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Rewrite using `[hπ1 k x hx]`. Conclude with `hx`.

Rewrite using `[hπ0 i k hk x hx]`. Conclude with `zero_mem _`. Establish `hdec : ∀ g ∈ Cset p L j0 J M, g - ϖ g = ∑ i ∈ univ.filter bad, π i g`. Introduce `g hg`. Use `Submodule.iSup_induction _ (motive := fun x => x - ϖ x = ∑ i ∈ univ.filter bad, π i x) (hsp hg) ?_ (by simp) (fun x y hx hy => by` and prove the remaining obligations.

Simplify using `only [map_add, Finset.sum_add_distrib, ← hx, ← hy]`. Use the proof step `abel)`. Introduce `k x hx`. Distinguish the cases in `hk : bad k`. Rewrite using `[hbad k hk x hx, sub_zero, Finset.sum_eq_single k (fun i _ hik => hπ0 i k (Ne.symm hik) x hx) (fun hk' => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩) hk'), hπ1 k x hx]`.

Rewrite using `[hgood k hk x hx, sub_self]`. Use `(Finset.sum_eq_zero fun i hi => hπ0 i k ?_ x hx).symm` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hk (Finset.mem_filter.mp hi).2`. Establish `hdecY : ∀ y ∈ Y p L J M, y - bigOp L j0 Pi ϖ y = ∑ i ∈ univ.filter bad, bigOp L j0 Pi (π i) y`.

Introduce `y hy`. Apply `eq_of_slc (fsj N r j0)` to reduce the goal to its premises. Introduce `m`. Establish `hc` using `slc_C L j0 J M hy m`. Rewrite using `[map_sub, map_sum, bigOp_slc L j0 e J M Pi ϖ hPi hϖ m y, inOp_C L j0 e J M Pi ϖ hPi _ hc, hdec _ hc]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[bigOp_slc L j0 e J M Pi (π i) hPi (hπEq i) m y, inOp_C L j0 e J M Pi (π i) hPi _ hc]`. Establish `hfd` using `Y_fd (p := p) (r := r) L J M`. Use `set Z : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) := ⨆ i ∈ univ.filter bad, YYs L j0 J M (h i) with hZ`. Establish `hZY : Z ≤ Y p L J M` using `iSup₂_le fun i _ => inf_le_left`.

Establish `hZfd : FiniteDimensional ℚ_[p] Z` using `Submodule.finiteDimensional_of_le hZY`. Use `set f : Y p (r := r) L J M →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] := (bigOp L j0 Pi ϖ - LinearMap.id) ∘ₗ (Y p (r := r) L J M).subtype with hf`. Establish `hran : LinearMap.range f ≤ Z`. Introduce and unpack `_ ⟨y, rfl⟩`. Establish `h1 : f y = -(∑ i ∈ univ.filter bad, bigOp L j0 Pi (π i) y.1)`.

Rewrite using `[← hdecY y.1 y.2]`. Simplify using `[hf]`. Rewrite using `[h1]`. Use `Z.neg_mem (Submodule.sum_mem _ fun i hi => ?_)` and prove the remaining obligations. Use `(le_iSup₂ (f := fun i (_ : i ∈ univ.filter bad) => YYs L j0 J M (h i)) i hi) ?_` and prove the remaining obligations.

Conclude with `Submodule.mem_inf.mpr ⟨bigOp_Y L j0 e J M Pi (π i) hPi (hπEq i) y.1 y.2, bigOp_span L j0 e J M Pi (π i) hPi (hπEq i) _ (hπVF i) y.1⟩`. Establish `hker : Module.finrank ℚ_[p] (LinearMap.ker f) = Module.finrank ℚ_[p] ((Y p L J M ⊓ LinearMap.ker (bigOp L j0 Pi ϖ - LinearMap.id) : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])))`. Rewrite using `[hf, LinearMap.ker_comp, ← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]`. Establish `hrn` using `LinearMap.finrank_range_add_finrank_ker f`. Establish `h1 : Module.finrank ℚ_[p] (LinearMap.range f) ≤ Module.finrank ℚ_[p] Z` using `Submodule.finrank_mono hran`.

Establish `h2 : Module.finrank ℚ_[p] Z ≤ ∑ i ∈ univ.filter bad, Module.finrank ℚ_[p] (YYs L j0 J M (h i))` using `finrank_biSup_le (Y p (r := r) L J M) (fun i => YYs L j0 J M (h i)) (fun i => inf_le_left) (univ.filter bad)`. Rewrite using `[← hker]`. Use linear arithmetic over natural numbers and integers.
-/
theorem count_le (bad : ι → Prop) [DecidablePred bad]
    (ϖ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hϖ : IsEqC L j0 J M ϖ) (hgood : ∀ i, ¬ bad i → ∀ x ∈ (GA p L j0).gS {h i}, ϖ x = x)
    (hbad : ∀ i, bad i → ∀ x ∈ (GA p L j0).gS {h i}, ϖ x = 0) :
    Module.finrank ℚ_[p] (Y p (r := r) L J M) -
      Module.finrank ℚ_[p] ((Y p L J M ⊓ LinearMap.ker (bigOp L j0 Pi ϖ - LinearMap.id) :
        Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))) ≤
      ∑ i ∈ univ.filter bad, Module.finrank ℚ_[p] (YYs L j0 J M (h i)) := by
  classical
  have hex : ∀ i : ι, ∃ φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p],
      IsEqC L j0 J M φ ∧ (∀ x ∈ (GA p (r := r) L j0).gS {h i}, φ x = x) ∧
        (∀ k, k ≠ i → ∀ x ∈ (GA p (r := r) L j0).gS {h k}, φ x = 0) := by
    intro i
    obtain ⟨φ, -, hφE, hφC, -, -, hφ1, hφ0⟩ := GlX.eqExt (GA p (r := r) L j0) (C_stable L j0 J M)
      (C_finW L j0 J M) h (fun k => if k = i then h k else 0) la hh hhC hli hsp
      (fun k => by
        by_cases hk : k = i
        · simpa [hk] using hh i
        · simpa [hk] using isHW_zero (GA p (r := r) L j0) (la k))
      (fun k => by
        by_cases hk : k = i
        · simpa [hk] using hhC i
        · simp [hk])
    exact ⟨φ, ⟨hφE, hφC⟩, hφ1 i (by simp), fun k hk => hφ0 k (by simp [hk])⟩
  choose π hπEq hπ1 hπ0 using hex

  have hπVF : ∀ i, ∀ g ∈ Cset p L j0 J M, π i g ∈ (GA p (r := r) L j0).gS {h i} := by
    intro i g hg
    refine Submodule.iSup_induction _ (motive := fun x => π i x ∈ (GA p (r := r) L j0).gS {h i}) (hsp hg) ?_
      (by simp) (fun x y hx hy => by rw [map_add]; exact add_mem hx hy)
    intro k x hx
    by_cases hk : k = i
    · subst hk; rw [hπ1 k x hx]; exact hx
    · rw [hπ0 i k hk x hx]; exact zero_mem _

  have hdec : ∀ g ∈ Cset p L j0 J M, g - ϖ g = ∑ i ∈ univ.filter bad, π i g := by
    intro g hg
    refine Submodule.iSup_induction _ (motive := fun x => x - ϖ x = ∑ i ∈ univ.filter bad, π i x) (hsp hg) ?_
      (by simp) (fun x y hx hy => by
        simp only [map_add, Finset.sum_add_distrib, ← hx, ← hy]; abel)
    intro k x hx
    by_cases hk : bad k
    · rw [hbad k hk x hx, sub_zero, Finset.sum_eq_single k (fun i _ hik => hπ0 i k (Ne.symm hik) x hx)
        (fun hk' => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩) hk'), hπ1 k x hx]
    · rw [hgood k hk x hx, sub_self]
      refine (Finset.sum_eq_zero fun i hi => hπ0 i k ?_ x hx).symm
      rintro rfl
      exact hk (Finset.mem_filter.mp hi).2

  have hdecY : ∀ y ∈ Y p L J M, y - bigOp L j0 Pi ϖ y = ∑ i ∈ univ.filter bad, bigOp L j0 Pi (π i) y := by
    intro y hy
    apply eq_of_slc (fsj N r j0)
    intro m
    have hc := slc_C L j0 J M hy m
    rw [map_sub, map_sum, bigOp_slc L j0 e J M Pi ϖ hPi hϖ m y, inOp_C L j0 e J M Pi ϖ hPi _ hc, hdec _ hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bigOp_slc L j0 e J M Pi (π i) hPi (hπEq i) m y, inOp_C L j0 e J M Pi (π i) hPi _ hc]
  have hfd := Y_fd (p := p) (r := r) L J M
  set Z : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) := ⨆ i ∈ univ.filter bad, YYs L j0 J M (h i) with hZ
  have hZY : Z ≤ Y p L J M := iSup₂_le fun i _ => inf_le_left
  have hZfd : FiniteDimensional ℚ_[p] Z := Submodule.finiteDimensional_of_le hZY
  set f : Y p (r := r) L J M →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
    (bigOp L j0 Pi ϖ - LinearMap.id) ∘ₗ (Y p (r := r) L J M).subtype with hf
  have hran : LinearMap.range f ≤ Z := by
    rintro _ ⟨y, rfl⟩
    have h1 : f y = -(∑ i ∈ univ.filter bad, bigOp L j0 Pi (π i) y.1) := by
      rw [← hdecY y.1 y.2]; simp [hf]
    rw [h1]
    refine Z.neg_mem (Submodule.sum_mem _ fun i hi => ?_)
    refine (le_iSup₂ (f := fun i (_ : i ∈ univ.filter bad) => YYs L j0 J M (h i)) i hi) ?_
    exact Submodule.mem_inf.mpr ⟨bigOp_Y L j0 e J M Pi (π i) hPi (hπEq i) y.1 y.2,
      bigOp_span L j0 e J M Pi (π i) hPi (hπEq i) _ (hπVF i) y.1⟩
  have hker : Module.finrank ℚ_[p] (LinearMap.ker f) =
      Module.finrank ℚ_[p] ((Y p L J M ⊓ LinearMap.ker (bigOp L j0 Pi ϖ - LinearMap.id) :
        Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))) := by
    rw [hf, LinearMap.ker_comp, ← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have h1 : Module.finrank ℚ_[p] (LinearMap.range f) ≤ Module.finrank ℚ_[p] Z := Submodule.finrank_mono hran
  have h2 : Module.finrank ℚ_[p] Z ≤ ∑ i ∈ univ.filter bad, Module.finrank ℚ_[p] (YYs L j0 J M (h i)) :=
    finrank_biSup_le (Y p (r := r) L J M) (fun i => YYs L j0 J M (h i)) (fun i => inf_le_left) (univ.filter bad)
  rw [← hker]
  omega

/- English proof (translation)
Take `⟨φ, -, hφE, hφC, hφg, hφinj, -, hφ0⟩` from `GlX.eqExt (GA p (r := r) L j0) (C_stable L j0 J M) (C_finW L j0 J M) h (fun k => if k = i0 then v else 0) la hh hhC hli hsp (fun k => by`. Distinguish the cases in `hk : k = i0`. Substitute `hk` using the available equality. Simplify using `using hv`. Simplify `isHW_zero (GA p (r := r) L j0) (la k))` using `[hk]`.

Use the proof step `(fun k => by`. Distinguish the cases in `hk : k = i0`. Simplify `hvC` using `[hk]`. Simplify using `[hk])`. Establish `hEq : IsEqC L j0 J M φ` using `⟨hφE, hφC⟩`.

Establish `hVF : ∀ g ∈ Cset p L j0 J M, φ g ∈ (GA p (r` using `r) L j0).gS {v} := by`. Introduce `g hg`. Use `Submodule.iSup_induction _ (motive := fun x => φ x ∈ (GA p (r := r) L j0).gS {v}) (hsp hg) ?_ (by simp) (fun x y hx hy => by rw [map_add]; exact add_mem hx hy)` and prove the remaining obligations. Introduce `k x hx`. Distinguish the cases in `hk : k = i0`.

Substitute `hk` using the available equality. Use `hφg k x hx` as an intermediate fact. Simplify using `using this`. Rewrite using `[hφ0 k (by simp [hk]) x hx]; exact zero_mem _`. Establish `hgSC : (GA p (r` using `r) L j0).gS {h i0} ≤ Cset p L j0 J M := (GA p (r := r) L j0).gS_le (by simpa using hhC i0) (C_stable L j0 J M)`.

Establish `hmap : ∀ z ∈ YYs L j0 J M (h i0), bigOp L j0 Pi φ z ∈ YYs L j0 J M v` using `fun z hz => Submodule.mem_inf.mpr ⟨bigOp_Y L j0 e J M Pi φ hPi hEq z (Submodule.mem_inf.mp hz).1, bigOp_span L j0 e J M Pi φ hPi hEq _ hVF z⟩`. Establish `hinj : ∀ z ∈ YYs L j0 J M (h i0), bigOp L j0 Pi φ z = 0 → z = 0`. Introduce `z hz h0`. Apply `eq_of_slc (fsj N r j0)` to reduce the goal to its premises. Introduce `m`.

Establish `h1 : slc (fsj N r j0) m z ∈ (GA p (r` using `r) L j0).gS {h i0} := slc_span L j0 _ (hgSC.trans inf_le_left) (Submodule.mem_inf.mp hz).2 m`. Establish `h2` using `bigOp_slc L j0 e J M Pi φ hPi hEq m z`. Rewrite `h2` using `[h0, map_zero, inOp_C L j0 e J M Pi φ hPi _ (hgSC h1)]`. Rewrite using `[map_zero]`. Conclude with `hφinj i0 (by simpa using hv0) _ h1 h2.symm`.

Establish `hfd` using `Y_fd (p := p) (r := r) L J M`. Establish `: FiniteDimensional ℚ_[p] (YYs L j0 J M v)` using `Submodule.finiteDimensional_of_le (inf_le_left : YYs L j0 J M v ≤ Y p L J M)`. Use `LinearMap.finrank_le_finrank_of_injective (f := (bigOp L j0 Pi φ).restrict hmap) ?_` and prove the remaining obligations. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `z hz`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `hinj z.1 z.2` to reduce the goal to its premises. Conclude with `congrArg Subtype.val hz`.
-/
theorem transport_le (i0 : ι) (v : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hv : (GA p L j0).IsHW (la i0) v)
    (hvC : v ∈ Cset p L j0 J M) (hv0 : v ≠ 0) :
    Module.finrank ℚ_[p] (YYs L j0 J M (h i0)) ≤ Module.finrank ℚ_[p] (YYs L j0 J M v) := by
  classical
  obtain ⟨φ, -, hφE, hφC, hφg, hφinj, -, hφ0⟩ := GlX.eqExt (GA p (r := r) L j0) (C_stable L j0 J M)
    (C_finW L j0 J M) h (fun k => if k = i0 then v else 0) la hh hhC hli hsp
    (fun k => by
      by_cases hk : k = i0
      · subst hk; simpa using hv
      · simpa [hk] using isHW_zero (GA p (r := r) L j0) (la k))
    (fun k => by
      by_cases hk : k = i0
      · simpa [hk] using hvC
      · simp [hk])
  have hEq : IsEqC L j0 J M φ := ⟨hφE, hφC⟩
  have hVF : ∀ g ∈ Cset p L j0 J M, φ g ∈ (GA p (r := r) L j0).gS {v} := by
    intro g hg
    refine Submodule.iSup_induction _ (motive := fun x => φ x ∈ (GA p (r := r) L j0).gS {v}) (hsp hg) ?_
      (by simp) (fun x y hx hy => by rw [map_add]; exact add_mem hx hy)
    intro k x hx
    by_cases hk : k = i0
    · subst hk
      have := hφg k x hx
      simpa using this
    · rw [hφ0 k (by simp [hk]) x hx]; exact zero_mem _
  have hgSC : (GA p (r := r) L j0).gS {h i0} ≤ Cset p L j0 J M :=
    (GA p (r := r) L j0).gS_le (by simpa using hhC i0) (C_stable L j0 J M)
  have hmap : ∀ z ∈ YYs L j0 J M (h i0), bigOp L j0 Pi φ z ∈ YYs L j0 J M v := fun z hz =>
    Submodule.mem_inf.mpr ⟨bigOp_Y L j0 e J M Pi φ hPi hEq z (Submodule.mem_inf.mp hz).1,
      bigOp_span L j0 e J M Pi φ hPi hEq _ hVF z⟩
  have hinj : ∀ z ∈ YYs L j0 J M (h i0), bigOp L j0 Pi φ z = 0 → z = 0 := by
    intro z hz h0
    apply eq_of_slc (fsj N r j0)
    intro m
    have h1 : slc (fsj N r j0) m z ∈ (GA p (r := r) L j0).gS {h i0} :=
      slc_span L j0 _ (hgSC.trans inf_le_left) (Submodule.mem_inf.mp hz).2 m
    have h2 := bigOp_slc L j0 e J M Pi φ hPi hEq m z
    rw [h0, map_zero, inOp_C L j0 e J M Pi φ hPi _ (hgSC h1)] at h2
    rw [map_zero]
    exact hφinj i0 (by simpa using hv0) _ h1 h2.symm
  have hfd := Y_fd (p := p) (r := r) L J M
  have : FiniteDimensional ℚ_[p] (YYs L j0 J M v) :=
    Submodule.finiteDimensional_of_le (inf_le_left : YYs L j0 J M v ≤ Y p L J M)
  refine LinearMap.finrank_le_finrank_of_injective (f := (bigOp L j0 Pi φ).restrict hmap) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  apply Subtype.ext
  apply hinj z.1 z.2
  exact congrArg Subtype.val hz

end

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Establish `h` using `S.smul_mem (⟨c, hc⟩ : ℤ_[p]) hx`. Use `first`. Consider the case `exact h`. Consider the case `(convert h using 1; ext m; simp [MvPolynomial.coeff_smul]; done)`. Consider the case `(convert h using 1; ext m; simp [MvPolynomial.coeff_smul, Algebra.smul_def]; done)`.
-/
theorem int_smul_mem {σ : Type} (S : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (c : ℚ_[p]) (hc : ‖c‖ ≤ 1)
    (x : MvPolynomial σ ℚ_[p]) (hx : x ∈ S) : c • x ∈ S := by
  have h := S.smul_mem (⟨c, hc⟩ : ℤ_[p]) hx
  first
    | exact h
    | (convert h using 1; ext m; simp [MvPolynomial.coeff_smul]; done)
    | (convert h using 1; ext m; simp [MvPolynomial.coeff_smul, Algebra.smul_def]; done)

/- English proof (translation)
Establish `hUu : IsUnit U.det`. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h`. Rewrite `hUd` using `[h, norm_zero]`. Conclude with `zero_ne_one hUd`.

Establish `hVu : IsUnit V.det`. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h`. Rewrite `hVd` using `[h, norm_zero]`. Conclude with `zero_ne_one hVd`.

Establish `hUi` using `fun x y => DetBound.norm_inv_entry_le U hU hUd x y`. Establish `hVi` using `fun x y => DetBound.norm_inv_entry_le V hV hVd x y`. Establish `hliQ : LinearIndependent ℚ_[p] f` using `(LinearIndependent.iff_fractionRing ℤ_[p] ℚ_[p]).mp hli`. Establish `hfL : ∀ x, f x ∈ Lat` using `fun x => hsp ▸ Submodule.subset_span ⟨x, rfl⟩`. Establish `hback : ∀ x, f x = ∑ a, U x a • ∑ y, U⁻¹ a y • f y`.

Introduce `x`. Simplify using `only [Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_smul]`. Establish `: ∀ y, ∑ a, U x a * U⁻¹ a y = (1 : Matrix (Fin nb) (Fin nb) ℚ_[p]) x y`.

Introduce `y`. Rewrite using `[← Matrix.mul_nonsing_inv U hUu, Matrix.mul_apply]`. Simplify using `only [this, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Use `⟨fun a => ∑ x, U⁻¹ a x • f x, fun b => ∑ y, V⁻¹ y b • f y, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `fun a => Lat.sum_mem fun x _ => int_smul_mem Lat _ (hUi a x) _ (hfL x)`.

Conclude with `fun b => Lat.sum_mem fun y _ => int_smul_mem Lat _ (hVi y b) _ (hfL y)`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Simplify using `only [Finset.smul_sum, smul_smul] at hg`. Rewrite `hg` using `[Finset.sum_comm]`.

Simplify using `only [← Finset.sum_smul] at hg`. Establish `h0` using `Fintype.linearIndependent_iff.mp hliQ _ hg`. Establish `h1 : Matrix.vecMul g U⁻¹ = 0`. Use function extensionality and compare the values at `x`. Simplify `h0 x` using `[Matrix.vecMul, dotProduct]`.

Establish `h2 : Matrix.vecMul (Matrix.vecMul g U⁻¹) U = g`. Rewrite using `[Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul U hUu, Matrix.vecMul_one]`. Introduce `a`. Rewrite using `[← h2, h1, Matrix.zero_vecMul]`. Both sides reduce to the same expression.

Rewrite using `[← hsp, Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[hback x]`. Conclude with `Submodule.sum_mem _ fun a _ => int_smul_mem _ _ (hU x a) _ (Submodule.subset_span ⟨a, rfl⟩)`. Introduce `a b`.

Establish `e : B (∑ x, U⁻¹ a x • f x) (∑ y, V⁻¹ y b • f y) = (U⁻¹ * (Matrix.of fun x y => B (f x) (f y)) * V⁻¹) a b`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, hfac]`.

Establish `: U⁻¹ * (U * Matrix.diagonal dg * V) * V⁻¹ = Matrix.diagonal dg`. Rewrite using `[Matrix.mul_assoc U, ← Matrix.mul_assoc U⁻¹, Matrix.nonsing_inv_mul U hUu, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv V hVu, Matrix.mul_one]`. Rewrite using `[this, Matrix.diagonal_apply]`.
-/
theorem smith_bases {σ : Type} (nb : ℕ) (f : Fin nb → MvPolynomial σ ℚ_[p])
    (Lat : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]))
    (hli : LinearIndependent ℤ_[p] f) (hsp : Submodule.span ℤ_[p] (Set.range f) = Lat)
    (B : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p])
    (U V : Matrix (Fin nb) (Fin nb) ℚ_[p]) (dg : Fin nb → ℚ_[p])
    (hU : ∀ x y, ‖U x y‖ ≤ 1) (hV : ∀ x y, ‖V x y‖ ≤ 1) (hUd : ‖U.det‖ = 1) (hVd : ‖V.det‖ = 1)
    (hfac : (Matrix.of fun x y => B (f x) (f y)) = U * Matrix.diagonal dg * V) :
    ∃ f' f'' : Fin nb → MvPolynomial σ ℚ_[p], (∀ a, f' a ∈ Lat) ∧ (∀ a, f'' a ∈ Lat) ∧
      LinearIndependent ℚ_[p] f' ∧ Lat ≤ Submodule.span ℤ_[p] (Set.range f') ∧
      ∀ a b, B (f' a) (f'' b) = if a = b then dg a else 0 := by
  classical
  have hUu : IsUnit U.det := by
    rw [isUnit_iff_ne_zero]; intro h; rw [h, norm_zero] at hUd; exact zero_ne_one hUd
  have hVu : IsUnit V.det := by
    rw [isUnit_iff_ne_zero]; intro h; rw [h, norm_zero] at hVd; exact zero_ne_one hVd
  have hUi := fun x y => DetBound.norm_inv_entry_le U hU hUd x y
  have hVi := fun x y => DetBound.norm_inv_entry_le V hV hVd x y
  have hliQ : LinearIndependent ℚ_[p] f := (LinearIndependent.iff_fractionRing ℤ_[p] ℚ_[p]).mp hli
  have hfL : ∀ x, f x ∈ Lat := fun x => hsp ▸ Submodule.subset_span ⟨x, rfl⟩
  have hback : ∀ x, f x = ∑ a, U x a • ∑ y, U⁻¹ a y • f y := by
    intro x
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have : ∀ y, ∑ a, U x a * U⁻¹ a y = (1 : Matrix (Fin nb) (Fin nb) ℚ_[p]) x y := by
      intro y
      rw [← Matrix.mul_nonsing_inv U hUu, Matrix.mul_apply]
    simp only [this, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine ⟨fun a => ∑ x, U⁻¹ a x • f x, fun b => ∑ y, V⁻¹ y b • f y, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun a => Lat.sum_mem fun x _ => int_smul_mem Lat _ (hUi a x) _ (hfL x)
  · exact fun b => Lat.sum_mem fun y _ => int_smul_mem Lat _ (hVi y b) _ (hfL y)
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Finset.smul_sum, smul_smul] at hg
    rw [Finset.sum_comm] at hg
    simp only [← Finset.sum_smul] at hg
    have h0 := Fintype.linearIndependent_iff.mp hliQ _ hg
    have h1 : Matrix.vecMul g U⁻¹ = 0 := by
      funext x
      simpa [Matrix.vecMul, dotProduct] using h0 x
    have h2 : Matrix.vecMul (Matrix.vecMul g U⁻¹) U = g := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul U hUu, Matrix.vecMul_one]
    intro a
    rw [← h2, h1, Matrix.zero_vecMul]; rfl
  · rw [← hsp, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [hback x]
    exact Submodule.sum_mem _ fun a _ => int_smul_mem _ _ (hU x a) _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro a b
    have e : B (∑ x, U⁻¹ a x • f x) (∑ y, V⁻¹ y b • f y) =
        (U⁻¹ * (Matrix.of fun x y => B (f x) (f y)) * V⁻¹) a b := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Matrix.mul_apply,
        Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [e, hfac]
    have : U⁻¹ * (U * Matrix.diagonal dg * V) * V⁻¹ = Matrix.diagonal dg := by
      rw [Matrix.mul_assoc U, ← Matrix.mul_assoc U⁻¹, Matrix.nonsing_inv_mul U hUu, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv V hVu, Matrix.mul_one]
    rw [this, Matrix.diagonal_apply]

/- English proof (translation)
Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).one_lt`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Establish `hd0 : d ≠ 0`. Introduce `h`. Apply `hd` to reduce the goal to its premises.

Rewrite using `[h, norm_zero]`. Conclude with `Real.rpow_pos_of_pos hp0 _`. Use `⟨?_, hd0⟩` and prove the remaining obligations. Rewrite `hd` using `[not_lt, Padic.norm_eq_zpow_neg_valuation hd0, ← Real.rpow_intCast, Real.rpow_le_rpow_left_iff hp1]`. Establish `hk : ((d.valuation : ℤ) : ℝ) ≤ E` using `by push_cast at hd; linarith`.

Establish `hk' : d.valuation ≤ (⌊E⌋₊ : ℤ)`. Distinguish the cases in `h0 : d.valuation ≤ 0`. Conclude with `h0.trans (Int.natCast_nonneg _)`. Use `push Not at h0`. Establish `h1 : ((d.valuation.toNat : ℕ) : ℝ) ≤ E`.

Establish `: ((d.valuation.toNat : ℕ) : ℤ) = d.valuation` using `Int.toNat_of_nonneg h0.le`. Combine the equalities or inequalities in the displayed calculation. Establish `h2` using `Nat.le_floor h1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[norm_div, norm_pow, Padic.norm_p, Padic.norm_eq_zpow_neg_valuation hd0, div_le_one (zpow_pos hp0 _), inv_pow, ← zpow_natCast, ← zpow_neg]`.

Conclude with `zpow_le_zpow_right₀ hp1.le (by omega)`.
-/
theorem good_norm (E : ℝ) (hE : 0 ≤ E) (d : ℚ_[p]) (hd : ¬ ‖d‖ < (p : ℝ) ^ (-E)) :
    ‖(p : ℚ_[p]) ^ ⌊E⌋₊ / d‖ ≤ 1 ∧ d ≠ 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hd0 : d ≠ 0 := by
    intro h
    apply hd
    rw [h, norm_zero]
    exact Real.rpow_pos_of_pos hp0 _
  refine ⟨?_, hd0⟩
  rw [not_lt, Padic.norm_eq_zpow_neg_valuation hd0, ← Real.rpow_intCast, Real.rpow_le_rpow_left_iff hp1] at hd
  have hk : ((d.valuation : ℤ) : ℝ) ≤ E := by push_cast at hd; linarith
  have hk' : d.valuation ≤ (⌊E⌋₊ : ℤ) := by
    by_cases h0 : d.valuation ≤ 0
    · exact h0.trans (Int.natCast_nonneg _)
    · push Not at h0
      have h1 : ((d.valuation.toNat : ℕ) : ℝ) ≤ E := by
        have : ((d.valuation.toNat : ℕ) : ℤ) = d.valuation := Int.toNat_of_nonneg h0.le
        calc ((d.valuation.toNat : ℕ) : ℝ) = (((d.valuation.toNat : ℕ) : ℤ) : ℝ) := by push_cast; rfl
          _ = ((d.valuation : ℤ) : ℝ) := by rw [this]
          _ ≤ E := hk
      have h2 := Nat.le_floor h1
      omega
  rw [norm_div, norm_pow, Padic.norm_p, Padic.norm_eq_zpow_neg_valuation hd0, div_le_one (zpow_pos hp0 _),
    inv_pow, ← zpow_natCast, ← zpow_neg]
  exact zpow_le_zpow_right₀ hp1.le (by omega)

/- English proof (translation)
Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).one_lt`. Establish `hlg1 : 1 ≤ lgV2 p a r`. Unfold `lgV2`. Establish `: (1 : ℝ) ≤ 8 * (a : ℝ) + r`. Establish `: (2 : ℝ) ≤ r` using `by exact_mod_cast hr`.

Establish `: (0 : ℝ) ≤ a` using `Nat.cast_nonneg a`. Combine the linear equalities and inequalities to obtain the conclusion. Use `Real.logb_nonneg hp1 this` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hr2 : (4 : ℝ) ≤ (r : ℝ) ^ 2`.

Establish `: (2 : ℝ) ≤ r` using `by exact_mod_cast hr`. Use the polynomial consequences of the given equalities and inequalities. Establish `hN : (0 : ℝ) ≤ N` using `Nat.cast_nonneg N`. Establish `hκN : ((N : ℝ) + 2) * 4 ≤ κ`. Establish `h1 : ((N : ℝ) + 2) * 4 ≤ ((N : ℝ) + 2) * (r : ℝ) ^ 2` using `mul_le_mul_of_nonneg_left hr2 (by positivity)`.

Establish `h2 : ((N : ℝ) + 2) * (r : ℝ) ^ 2 ≤ ((N : ℝ) + 2) * (r : ℝ) ^ 2 * lgV2 p a r` using `le_mul_of_one_le_right (by positivity) hlg1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hκ0 : 0 ≤ κ` using `by nlinarith`. Establish `hce : ((⌈κ / (N + 2)⌉₊ : ℕ) : ℝ) < κ / (N + 2) + 1` using `Nat.ceil_lt_add_one (by positivity)`. Establish `hj : (j0 : ℝ) ≤ N` using `by exact_mod_cast hj0`.

Establish `hj' : (0 : ℝ) ≤ j0` using `Nat.cast_nonneg j0`. Establish `h3 : κ / (N + 2) * (N + 2) = κ`. Clear the denominators using the available nonvanishing facts. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem K_bound (N r a j0 : ℕ) (κ : ℝ) (hr : 2 ≤ r) (hj0 : j0 ≤ N)
    (hκ : ((N + 2) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ) :
    ((⌈κ / (N + 2)⌉₊ * j0 + 2 * ⌈κ / (N + 2)⌉₊ : ℕ) : ℝ) ≤ 3 * κ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlg1 : 1 ≤ lgV2 p a r := by
    unfold lgV2
    have : (1 : ℝ) ≤ 8 * (a : ℝ) + r := by
      have : (2 : ℝ) ≤ r := by exact_mod_cast hr
      have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      linarith
    have := Real.logb_nonneg hp1 this
    linarith
  have hr2 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hκN : ((N : ℝ) + 2) * 4 ≤ κ := by
    have h1 : ((N : ℝ) + 2) * 4 ≤ ((N : ℝ) + 2) * (r : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hr2 (by positivity)
    have h2 : ((N : ℝ) + 2) * (r : ℝ) ^ 2 ≤ ((N : ℝ) + 2) * (r : ℝ) ^ 2 * lgV2 p a r :=
      le_mul_of_one_le_right (by positivity) hlg1
    linarith
  have hκ0 : 0 ≤ κ := by nlinarith
  have hce : ((⌈κ / (N + 2)⌉₊ : ℕ) : ℝ) < κ / (N + 2) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hj : (j0 : ℝ) ≤ N := by exact_mod_cast hj0
  have hj' : (0 : ℝ) ≤ j0 := Nat.cast_nonneg j0
  have h3 : κ / (N + 2) * (N + 2) = κ := by
    field_simp
  push_cast
  calc ((⌈κ / (N + 2)⌉₊ : ℕ) : ℝ) * j0 + 2 * ((⌈κ / (N + 2)⌉₊ : ℕ) : ℝ)
      = ((⌈κ / (N + 2)⌉₊ : ℕ) : ℝ) * (j0 + 2) := by ring
    _ ≤ (κ / (N + 2) + 1) * (j0 + 2) := mul_le_mul_of_nonneg_right hce.le (by positivity)
    _ ≤ (κ / (N + 2) + 1) * (N + 2) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = κ / (N + 2) * (N + 2) + (N + 2) := by ring
    _ ≤ 3 * κ := by rw [h3]; linarith

/- English proof (translation)
Set `F : ℕ → ℕ` to `fun k => if hk : k < N then L.deg ⟨k, hk⟩ else 0`. Establish `h1 : (L.takeD (T.pos i + 1)).total = ∑ k ∈ range (T.pos i + 1), F k`. Rewrite using `[← Fin.sum_univ_eq_sum_range]`. Both sides reduce to the same expression. Establish `h2 : T.S L i = ∑ k ∈ range N, if k ≤ T.pos i then F k else 0`.

Rewrite using `[← Fin.sum_univ_eq_sum_range (fun k => if k ≤ T.pos i then F k else 0) N]`. Unfold `TieData.S`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [F, a.isLt, dif_pos, Fin.eta]`. Rewrite using `[h1, h2, ← Finset.sum_filter]`.

Use `Finset.sum_congr ?_ fun _ _ => rfl` and prove the remaining obligations. Use extensionality with `k`. Simplify using `only [Finset.mem_range, Finset.mem_filter]`. Use linear arithmetic over natural numbers and integers.
-/
theorem S_eq_total {N : ℕ} (L : Letters N) (T : TieData) (i : Fin T.t) (h : T.pos i + 1 < N) :
    (L.takeD (T.pos i + 1)).total = T.S L i := by
  classical
  let F : ℕ → ℕ := fun k => if hk : k < N then L.deg ⟨k, hk⟩ else 0
  have h1 : (L.takeD (T.pos i + 1)).total = ∑ k ∈ range (T.pos i + 1), F k := by
    rw [← Fin.sum_univ_eq_sum_range]
    rfl
  have h2 : T.S L i = ∑ k ∈ range N, if k ≤ T.pos i then F k else 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => if k ≤ T.pos i then F k else 0) N]
    unfold TieData.S
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [F, a.isLt, dif_pos, Fin.eta]
  rw [h1, h2, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext k
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

/- English proof (translation)
The claim follows from `int_smul_mem (IntPol p σ) c hc x hx`.
-/
theorem smul_int {σ : Type} {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) {x : MvPolynomial σ ℚ_[p]} (hx : x ∈ IntPol p σ) :
    c • x ∈ IntPol p σ := int_smul_mem (IntPol p σ) c hc x hx

/- English proof (translation)
Rewrite using `[norm_pow]`. Conclude with `pow_le_one₀ (norm_nonneg _) (by rw [Padic.norm_p]; exact inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le))`.
-/
theorem norm_p_pow_le (k : ℕ) : ‖(p : ℚ_[p]) ^ k‖ ≤ 1 := by
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (by rw [Padic.norm_p]; exact inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le))

/- English proof (translation)
Proceed by induction on `v using MvPolynomial.induction_on' with`. Consider the case `monomial m a`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).one_lt`. Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt ‖a‖ hp1`. Use `⟨k, mem_intPol_of_norm _ fun m' => ?_⟩` and prove the remaining obligations.

Rewrite using `[coeff_smul, coeff_monomial, smul_eq_mul]`. Use `split_ifs`. Rewrite using `[norm_mul, norm_pow, Padic.norm_p, inv_pow]`. Rewrite using `[inv_mul_le_iff₀ (by positivity), mul_one]`. Conclude with `hk.le`.

Simplify using the standard rewrite rules. Consider the case `add x y hx hy`. Take `⟨k1, h1⟩` from `hx`. Take `⟨k2, h2⟩` from `hy`. Use `⟨k1 + k2, ?_⟩` and prove the remaining obligations.

Establish `e : ((p : ℚ_[p]) ^ (k1 + k2)) • (x + y) = ((p : ℚ_[p]) ^ k2) • (((p : ℚ_[p]) ^ k1) • x) + ((p : ℚ_[p]) ^ k1) • (((p : ℚ_[p]) ^ k2) • y)`. Rewrite using `[smul_add, smul_smul, smul_smul, pow_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `Submodule.add_mem _ (smul_int (norm_p_pow_le k2) h1) (smul_int (norm_p_pow_le k1) h2)`.
-/
theorem exists_pow_int {σ : Type} (v : MvPolynomial σ ℚ_[p]) : ∃ k : ℕ, ((p : ℚ_[p]) ^ k) • v ∈ IntPol p σ := by
  classical
  induction v using MvPolynomial.induction_on' with
  | monomial m a =>
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖a‖ hp1
    refine ⟨k, mem_intPol_of_norm _ fun m' => ?_⟩
    rw [coeff_smul, coeff_monomial, smul_eq_mul]
    split_ifs
    · rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
      rw [inv_mul_le_iff₀ (by positivity), mul_one]
      exact hk.le
    · simp
  | add x y hx hy =>
    obtain ⟨k1, h1⟩ := hx
    obtain ⟨k2, h2⟩ := hy
    refine ⟨k1 + k2, ?_⟩
    have e : ((p : ℚ_[p]) ^ (k1 + k2)) • (x + y) =
        ((p : ℚ_[p]) ^ k2) • (((p : ℚ_[p]) ^ k1) • x) + ((p : ℚ_[p]) ^ k1) • (((p : ℚ_[p]) ^ k2) • y) := by
      rw [smul_add, smul_smul, smul_smul, pow_add]
      congr 2; ring
    rw [e]
    exact Submodule.add_mem _ (smul_int (norm_p_pow_le k2) h1) (smul_int (norm_p_pow_le k1) h2)

/- English proof (translation)
Unfold `Cset`. Use `congr 1`. Use `iInf_congr fun k => ?_` and prove the remaining obligations. Unfold `Mup TieData.thrUpTo`. Distinguish the cases in `h : T.J k < T.pos i + 1 + 1`.

Rewrite using `[if_pos h, if_pos h, if_pos (by omega)]`. Rewrite using `[if_neg h, if_neg h]`.
-/
theorem Cset_thrUpTo [NeZero r] (L : Letters N) (T : TieData) (i : Fin T.t) :
    Cset p (r := r) L (T.pos i + 1 + 1) T.J (T.thrUpTo i) = Cset p L (T.pos i + 1 + 1) T.J T.thr := by
  unfold Cset
  congr 1
  refine iInf_congr fun k => ?_
  unfold Mup TieData.thrUpTo
  by_cases h : T.J k < T.pos i + 1 + 1
  · rw [if_pos h, if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg h]

/- English proof (translation)
Unfold `TieData.YYsp YYs`. Rewrite using `[gSpan_eq]`. Both sides reduce to the same expression.
-/
theorem YYsp_eq [NeZero N] [NeZero r] (LL : Letters N) (T : TieData) (i : Fin T.t) (ρ : Fin r) (n : Fin T.t → ℕ)
    (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) :
    T.YYsp p LL i ρ n f =
      YYs (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr (T.Ffull p (LL.setTies T n) i ρ (n i) f) := by
  unfold TieData.YYsp YYs
  rw [gSpan_eq]
  rfl

/- English proof (translation)
Rewrite `hx`, the goal using `[isHW_iff]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem isHW_smul (L : Letters N) (j : ℕ) (la : Fin r → ℤ) (c : ℚ_[p]) {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : (GA p L j).IsHW la x) : (GA p L j).IsHW la (c • x) := by
  rw [isHW_iff] at hx ⊢
  exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Rewrite using `[isHW_iff]`. Conclude with `Submodule.zero_mem _`.
-/
theorem isHW_zero' (L : Letters N) (j : ℕ) (la : Fin r → ℤ) :
    (GA p L j).IsHW la (0 : MvPolynomial (Fin N × Fin r) ℚ_[p]) := by
  rw [isHW_iff]
  exact Submodule.zero_mem _

/- English proof (translation)
Take `⟨Pi, hPi⟩` from `projC L ρ e1 (T.pos i + 1 + 1) hK hHP T.J T.thr`. Establish `hCst` using `C_stable (p := p) (r := r) L (T.pos i + 1 + 1) T.J T.thr`. Establish `hCf : (GA p L (T.pos i + 1 + 1)).FinW (Cset p (r` using `r) L (T.pos i + 1 + 1) T.J T.thr) := by`. Take `⟨S, hS⟩` from `polynomial_finite_weights (p := p) (r := r) L (T.pos i + 1 + 1)`. Conclude with `⟨S, fun x hx => hS x (Submodule.mem_inf.mp hx).1⟩`.

Establish `hp0 : (p : ℚ_[p]) ≠ 0` using `by exact_mod_cast (Fact.out : p.Prime).ne_zero`. Establish `hspQ : ∀ μ v, v ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr → (GA p L (T.pos i + 1 + 1)).IsHW μ v → v ∈ Submodule.span ℚ_[p] (Set.range h')`. Introduce `μ v hv hw`. Take `⟨k, hk⟩` from `exists_pow_int v`. Establish `h1` using `hspZ μ (((p : ℚ_[p]) ^ k) • v) (Submodule.smul_mem _ _ hv) (isHW_smul L _ μ _ hw) hk`.

Establish `h2 : ((p : ℚ_[p]) ^ k) • v ∈ Submodule.span ℚ_[p] (Set.range h')` using `Submodule.span_le_restrictScalars ℤ_[p] ℚ_[p] _ h1`. Conclude with `(Submodule.smul_mem_iff _ (pow_ne_zero _ hp0)).mp h2`. Establish `hsp : Cset p (r` using `r) L (T.pos i + 1 + 1) T.J T.thr ≤ ⨆ x, (GA p L (T.pos i + 1 + 1)).gS {h' x} := by`. Take `⟨S, hS⟩` from `hCf`. Conclude with `GlX.span_hw (GA p L (T.pos i + 1 + 1)) hCst hS h' la hh hhC (fun x => hli.ne_zero x) hspQ`.

Use `set c : ℚ_[p] := (p : ℚ_[p]) ^ ⌊E⌋₊ with hc`. Set `gϖ : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]` to `fun x => if ‖d x‖ < (p : ℝ) ^ (-E) then 0 else h' x`. Set `tc : ι → ι → ℚ_[p]` to `fun z y => if la z = la y ∧ ¬ ‖d z‖ < (p : ℝ) ^ (-E) then (c / d z) * (cst * fock p (h' z) (h' y)) else 0`. Set `gτ : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]` to `fun y => ∑ z, tc z y • h'' z`. Establish `hgϖ : ∀ x, (GA p L (T.pos i + 1 + 1)).IsHW (la x) (gϖ x)`.

Introduce `x`. Distinguish the cases in `hx : ‖d x‖ < (p : ℝ) ^ (-E)`. Simplify using `only [gϖ, if_pos hx]`. Conclude with `isHW_zero' L _ _`. Simplify using `only [gϖ, if_neg hx]`.

Conclude with `hh x`. Establish `hgϖC : ∀ x, gϖ x ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr`. Introduce `x`. Distinguish the cases in `hx : ‖d x‖ < (p : ℝ) ^ (-E)`. Simplify using `only [gϖ, if_pos hx]`.

Conclude with `Submodule.zero_mem _`. Simplify using `only [gϖ, if_neg hx]`. Conclude with `hhC x`. Establish `hgτ : ∀ y, (GA p L (T.pos i + 1 + 1)).IsHW (la y) (gτ y)`. Introduce `y`.

Rewrite using `[isHW_iff]`. Use `Submodule.sum_mem _ fun z _ => ?_` and prove the remaining obligations. Distinguish the cases in `hz : la z = la y ∧ ¬ ‖d z‖ < (p : ℝ) ^ (-E)`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Rewrite using `[← isHW_iff, ← hz.1]`.

Conclude with `hh2 z`. Simplify using `only [tc, if_neg hz, zero_smul]`. Conclude with `Submodule.zero_mem _`. Establish `hgτC : ∀ y, gτ y ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr` using `fun y => Submodule.sum_mem _ fun z _ => Submodule.smul_mem _ _ (hh2C z)`. Establish `htc : ∀ z y, ‖tc z y‖ ≤ 1`.

Introduce `z y`. Distinguish the cases in `hz : la z = la y ∧ ¬ ‖d z‖ < (p : ℝ) ^ (-E)`. Simplify using `only [tc, if_pos hz, norm_mul]`. Conclude with `mul_le_one₀ (good_norm E hE (d z) hz.2).1 (by positivity) (by rw [← norm_mul]; exact hG0 z y)`. Simplify using `only [tc, if_neg hz, norm_zero]`.

Conclude with `zero_le_one`. Establish `hgτi : ∀ y, gτ y ∈ IntPol p (Fin N × Fin r)` using `fun y => Submodule.sum_mem _ fun z _ => smul_int (htc z y) (hh2i z)`. Take `⟨ϖ, hϖ1, hϖ2, hϖ3, -, -, hϖ6, hϖ7⟩` from `GlX.eqExt (GA p L (T.pos i + 1 + 1)) hCst hCf h' gϖ la hh hhC hli hsp hgϖ hgϖC`. Take `⟨τ, hτ1, hτ2, hτ3, -, -, -, -⟩` from `GlX.eqExt (GA p L (T.pos i + 1 + 1)) hCst hCf h' gτ la hh hhC hli hsp hgτ hgτC`. Establish `hEϖ : IsEqC L (T.pos i + 1 + 1) T.J T.thr ϖ` using `⟨hϖ2, hϖ3⟩`.

Establish `hEτ : IsEqC L (T.pos i + 1 + 1) T.J T.thr τ` using `⟨hτ2, hτ3⟩`. Use `⟨bigOp L (T.pos i + 1 + 1) Pi τ, bigOp L (T.pos i + 1 + 1) Pi ϖ, bigOp_Y L (T.pos i + 1 + 1) _ T.J T.thr Pi τ hPi hEτ, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Establish `hint : ∀ μ v, v ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr → (GA p L (T.pos i + 1 + 1)).IsHW μ v → v ∈ IntPol p (Fin N × Fin r) → τ v ∈ IntPol p (Fin N × Fin r)`. Introduce `μ v hv hw hvi`.

Establish `h1` using `hspZ μ v hv hw hvi`. Use `Submodule.span_induction (p := fun v _ => τ v ∈ IntPol p (Fin N × Fin r)) ?_ ?_ ?_ ?_ h1` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[hτ1]`. Conclude with `hgτi x`.

Rewrite using `[map_zero]`. Conclude with `Submodule.zero_mem _`. Introduce `a b _ _ ha hb`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ ha hb`.

Introduce `a b _ hb`. Rewrite using `[LinearMap.map_smul_of_tower]`. Conclude with `Submodule.smul_mem _ a hb`. Conclude with `int_main L ρ e1 (T.pos i + 1 + 1) hK hHP hHW (bigOp L (T.pos i + 1 + 1) Pi τ) (e1 * (T.pos i + 1 + 1)) (bigOp_glAct L (T.pos i + 1 + 1) _ T.J T.thr Pi τ hPi hEτ) (fun la0 x hx hxi => bigOp_int L (T.pos i + 1 + 1) _ T.J T.thr Pi τ hPi hEτ hint la0 x hx hxi) y (Submodule.mem_inf.mp …`. Introduce `u hu u' hu'`.

Establish `hcore : ∀ g ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr, ∀ g' ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr, fock p (T.phi p L i g) (inOp L (T.pos i + 1 + 1) Pi τ g') = c * fock p (inOp L (T.pos i + 1 + 1) Pi ϖ g) g'`. Introduce `g hg g' hg'`. Rewrite using `[inOp_C L (T.pos i + 1 + 1) _ T.J T.thr Pi τ hPi g' hg', inOp_C L (T.pos i + 1 + 1) _ T.J T.thr Pi ϖ hPi g hg]`. Set `B : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p]` to `(fockB p (Fin N × Fin r)).compl₁₂ (T.phi p L i) τ - c • (fockB p (Fin N × Fin r)).compl₁₂ ϖ LinearMap.id`. Establish `hBa : ∀ x y, B x y = fock p (T.phi p L i x) (τ y) - c * fock p (ϖ x) y`.

Introduce `x y`. Simplify using `[B, fockB_apply]`. Establish `hBz` using `GlX.form_zero (GA p L (T.pos i + 1 + 1)) hCst h' la hh hhC hsp B ?_ ?_ g hg g' hg'`. Rewrite `hBz` using `[hBa]`. Conclude with `sub_eq_zero.mp hBz`.

Introduce `x hx y hy a b`. Rewrite using `[hBa, hBa]`. Express the relevant statement in the definitionally equal form `fock p (T.phi p L i (glAct p L (T.pos i + 1 + 1) a b x)) (τ y) - c * fock p (ϖ (glAct p L (T.pos i + 1 + 1) a b x)) y = fock p (T.phi p L i x) (τ (glAct p L (T.pos i + 1 + 1) b a y)) - c * fock p (ϖ x) (glAct p L (T.pos i + 1 + 1) b a y)`. Rewrite using `[phi_glAct L T hadm i a b x, fock_glAct, hEτ.comm y hy b a, hEϖ.comm x hx a b, fock_glAct]`. Introduce `x y hxy`.

Rewrite using `[hBa, hτ1, hϖ1]`. Establish `hterm : ∀ z, tc z y * fock p (T.phi p L i (h' x)) (h'' z) = if z = x then (if ‖d x‖ < (p : ℝ) ^ (-E) then 0 else c * fock p (h' x) (h' y)) else 0`. Introduce `z`. Distinguish the cases in `hz : la z = la y ∧ ¬ ‖d z‖ < (p : ℝ) ^ (-E)`. Establish `h1` using `hdiag x z (hxy.trans hz.1.symm)`.

Simplify using `only [tc, if_pos hz]`. Establish `h2 : c / d z * (cst * fock p (h' z) (h' y)) * fock p (T.phi p L i (h' x)) (h'' z) = c / d z * fock p (h' z) (h' y) * (cst * fock p (T.phi p L i (h' x)) (h'' z))` using `by ring`. Rewrite using `[h2, h1]`. Distinguish the cases in `hzx : z = x`. Substitute `hzx` using the available equality.

Rewrite using `[if_pos rfl, if_pos rfl, if_neg hz.2]`. Establish `hd0` using `(good_norm E hE (d z) hz.2).2`. Clear the denominators using the available nonvanishing facts. Rewrite using `[if_neg (Ne.symm hzx), if_neg hzx, mul_zero]`. Simplify using `only [tc, if_neg hz, zero_mul]`.

Distinguish the cases in `hzx : z = x`. Substitute `hzx` using the available equality. Rewrite using `[if_pos rfl]`. Establish `: ‖d z‖ < (p : ℝ) ^ (-E)`. Assume the negation of the conclusion as `h`.

Conclude with `hz ⟨hxy, h⟩`. Rewrite using `[if_pos this]`. Rewrite using `[if_neg hzx]`. Establish `hsum : fock p (T.phi p L i (h' x)) (gτ y) = if ‖d x‖ < (p : ℝ) ^ (-E) then 0 else c * fock p (h' x) (h' y)`. Simplify using `only [gτ]`.

Rewrite using `[gammaIntegralityLemmas.fock_sum_right]`. Simplify using `only [gammaIntegralityLemmas.fock_smul_right, hterm]`. Rewrite using `[Finset.sum_ite_eq']`. Simplify using the standard rewrite rules. Rewrite using `[hsum]`.

Distinguish the cases in `hx : ‖d x‖ < (p : ℝ) ^ (-E)`. Simplify using `only [gϖ, if_pos hx]`. Rewrite using `[gammaIntegralityLemmas.fock_zero_left]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [gϖ, if_neg hx]`.

Expand and normalize the polynomial expressions, which then agree. Establish `key` using `fock_ext_reduce (T.pos i + 1 + 1) (T.phi p L i) (inOp L (T.pos i + 1 + 1) Pi τ) (inOp L (T.pos i + 1 + 1) Pi ϖ) c (Cset p L (T.pos i + 1 + 1) T.J T.thr) (phi_mul_later L T hadm i) (phi_isF L T hadm i) (inOp_isF L (T.pos i + 1 + 1) _ T.J T.thr Pi τ hPi hEτ) (inOp_isF L (T.pos i + …`. Unfold `fockN`. Express the relevant statement in the definitionally equal form `fock p (T.phi p L i u) (ext (fsj N r (T.pos i + 1 + 1)) (inOp L (T.pos i + 1 + 1) Pi τ) u') / _ = c * (fock p (ext (fsj N r (T.pos i + 1 + 1)) (inOp L (T.pos i + 1 + 1) Pi ϖ) u) u' / _)`. Rewrite using `[key, mul_div_assoc]`.

Introduce `j hij u`. Conclude with `phi_ext_comm L T hadm i j hij _ (inOp_isF L (T.pos i + 1 + 1) _ T.J T.thr Pi ϖ hPi hEϖ) u`. Conclude with `(count_le L (T.pos i + 1 + 1) _ T.J T.thr Pi hPi h' la hh hhC hli hsp (fun x => ‖d x‖ < (p : ℝ) ^ (-E)) ϖ hEϖ (fun x hx => hϖ6 x (by simp only [gϖ, if_neg hx])) (fun x hx => hϖ7 x (by simp only [gϖ, if_pos hx]))).trans (Finset.sum_le_sum fun x _ => transport_le L (T.pos i + 1 + 1 …`.
-/
theorem tie_core [NeZero r] (L : Letters N) (T : TieData) (hadm : T.Admissible L) (i : Fin T.t) (ρ : Fin r) (e1 : ℕ)
    (hK : T.pos i + 1 + 1 ≤ N) (hHP : HypP p L ρ e1) (hHW : HypW p (r := r) L e1) (E : ℝ) (hE : 0 ≤ E)
    {ι : Type} [Fintype ι] [DecidableEq ι] (h' h'' : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]) (la : ι → Fin r → ℤ)
    (hh : ∀ x, (GA p L (T.pos i + 1 + 1)).IsHW (la x) (h' x))
    (hhC : ∀ x, h' x ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr)
    (hli : LinearIndependent ℚ_[p] h')
    (hspZ : ∀ μ v, v ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr → (GA p L (T.pos i + 1 + 1)).IsHW μ v →
      v ∈ IntPol p (Fin N × Fin r) → v ∈ Submodule.span ℤ_[p] (Set.range h'))
    (hh2 : ∀ x, (GA p L (T.pos i + 1 + 1)).IsHW (la x) (h'' x))
    (hh2C : ∀ x, h'' x ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr)
    (hh2i : ∀ x, h'' x ∈ IntPol p (Fin N × Fin r))
    (d : ι → ℚ_[p]) (cst : ℚ_[p])
    (hdiag : ∀ x y, la x = la y → cst * fock p (T.phi p L i (h' x)) (h'' y) = if x = y then d x else 0)
    (hG0 : ∀ x y, ‖cst * fock p (h' x) (h' y)‖ ≤ 1)
    (vv : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]) (hvv : ∀ x, (GA p L (T.pos i + 1 + 1)).IsHW (la x) (vv x))
    (hvvC : ∀ x, vv x ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr) (hvv0 : ∀ x, vv x ≠ 0) :
    ∃ Tm πm : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p],
      (∀ y ∈ Y p (r := r) L T.J T.thr, Tm y ∈ Y p (r := r) L T.J T.thr) ∧
      (∀ y ∈ YZ p (r := r) L T.J T.thr,
        ((p : ℚ_[p]) ^ (e1 * (T.pos i + 1 + 1) + 2 * e1)) • Tm y ∈ IntPol p (Fin N × Fin r)) ∧
      (∀ u ∈ Y p (r := r) L T.J (T.thrUpTo i), ∀ u' ∈ Y p (r := r) L T.J T.thr,
        fockN p L (T.phi p L i u) (Tm u') = (p : ℚ_[p]) ^ ⌊E⌋₊ * fockN p L (πm u) u') ∧
      (∀ j : Fin T.t, i < j → ∀ u, πm (T.phi p L j u) = T.phi p L j (πm u)) ∧
      Module.finrank ℚ_[p] (Y p (r := r) L T.J T.thr) -
        Module.finrank ℚ_[p] ((Y p (r := r) L T.J T.thr ⊓ LinearMap.ker (πm - LinearMap.id) :
          Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))) ≤
        ∑ x ∈ univ.filter (fun x => ‖d x‖ < (p : ℝ) ^ (-E)),
          Module.finrank ℚ_[p] (YYs L (T.pos i + 1 + 1) T.J T.thr (vv x)) := by
  classical
  obtain ⟨Pi, hPi⟩ := projC L ρ e1 (T.pos i + 1 + 1) hK hHP T.J T.thr
  have hCst := C_stable (p := p) (r := r) L (T.pos i + 1 + 1) T.J T.thr
  have hCf : (GA p L (T.pos i + 1 + 1)).FinW (Cset p (r := r) L (T.pos i + 1 + 1) T.J T.thr) := by
    obtain ⟨S, hS⟩ := polynomial_finite_weights (p := p) (r := r) L (T.pos i + 1 + 1)
    exact ⟨S, fun x hx => hS x (Submodule.mem_inf.mp hx).1⟩
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hspQ : ∀ μ v, v ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr → (GA p L (T.pos i + 1 + 1)).IsHW μ v →
      v ∈ Submodule.span ℚ_[p] (Set.range h') := by
    intro μ v hv hw
    obtain ⟨k, hk⟩ := exists_pow_int v
    have h1 := hspZ μ (((p : ℚ_[p]) ^ k) • v) (Submodule.smul_mem _ _ hv) (isHW_smul L _ μ _ hw) hk
    have h2 : ((p : ℚ_[p]) ^ k) • v ∈ Submodule.span ℚ_[p] (Set.range h') :=
      Submodule.span_le_restrictScalars ℤ_[p] ℚ_[p] _ h1
    exact (Submodule.smul_mem_iff _ (pow_ne_zero _ hp0)).mp h2
  have hsp : Cset p (r := r) L (T.pos i + 1 + 1) T.J T.thr ≤ ⨆ x, (GA p L (T.pos i + 1 + 1)).gS {h' x} := by
    obtain ⟨S, hS⟩ := hCf
    exact GlX.span_hw (GA p L (T.pos i + 1 + 1)) hCst hS h' la hh hhC (fun x => hli.ne_zero x) hspQ
  set c : ℚ_[p] := (p : ℚ_[p]) ^ ⌊E⌋₊ with hc
  let gϖ : ι → MvPolynomial (Fin N × Fin r) ℚ_[p] := fun x => if ‖d x‖ < (p : ℝ) ^ (-E) then 0 else h' x
  let tc : ι → ι → ℚ_[p] := fun z y =>
    if la z = la y ∧ ¬ ‖d z‖ < (p : ℝ) ^ (-E) then (c / d z) * (cst * fock p (h' z) (h' y)) else 0
  let gτ : ι → MvPolynomial (Fin N × Fin r) ℚ_[p] := fun y => ∑ z, tc z y • h'' z
  have hgϖ : ∀ x, (GA p L (T.pos i + 1 + 1)).IsHW (la x) (gϖ x) := by
    intro x
    by_cases hx : ‖d x‖ < (p : ℝ) ^ (-E)
    · simp only [gϖ, if_pos hx]; exact isHW_zero' L _ _
    · simp only [gϖ, if_neg hx]; exact hh x
  have hgϖC : ∀ x, gϖ x ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr := by
    intro x
    by_cases hx : ‖d x‖ < (p : ℝ) ^ (-E)
    · simp only [gϖ, if_pos hx]; exact Submodule.zero_mem _
    · simp only [gϖ, if_neg hx]; exact hhC x
  have hgτ : ∀ y, (GA p L (T.pos i + 1 + 1)).IsHW (la y) (gτ y) := by
    intro y
    rw [isHW_iff]
    refine Submodule.sum_mem _ fun z _ => ?_
    by_cases hz : la z = la y ∧ ¬ ‖d z‖ < (p : ℝ) ^ (-E)
    · refine Submodule.smul_mem _ _ ?_
      rw [← isHW_iff, ← hz.1]; exact hh2 z
    · simp only [tc, if_neg hz, zero_smul]; exact Submodule.zero_mem _
  have hgτC : ∀ y, gτ y ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr :=
    fun y => Submodule.sum_mem _ fun z _ => Submodule.smul_mem _ _ (hh2C z)
  have htc : ∀ z y, ‖tc z y‖ ≤ 1 := by
    intro z y
    by_cases hz : la z = la y ∧ ¬ ‖d z‖ < (p : ℝ) ^ (-E)
    · simp only [tc, if_pos hz, norm_mul]
      exact mul_le_one₀ (good_norm E hE (d z) hz.2).1 (by positivity) (by rw [← norm_mul]; exact hG0 z y)
    · simp only [tc, if_neg hz, norm_zero]; exact zero_le_one
  have hgτi : ∀ y, gτ y ∈ IntPol p (Fin N × Fin r) :=
    fun y => Submodule.sum_mem _ fun z _ => smul_int (htc z y) (hh2i z)
  obtain ⟨ϖ, hϖ1, hϖ2, hϖ3, -, -, hϖ6, hϖ7⟩ :=
    GlX.eqExt (GA p L (T.pos i + 1 + 1)) hCst hCf h' gϖ la hh hhC hli hsp hgϖ hgϖC
  obtain ⟨τ, hτ1, hτ2, hτ3, -, -, -, -⟩ :=
    GlX.eqExt (GA p L (T.pos i + 1 + 1)) hCst hCf h' gτ la hh hhC hli hsp hgτ hgτC
  have hEϖ : IsEqC L (T.pos i + 1 + 1) T.J T.thr ϖ := ⟨hϖ2, hϖ3⟩
  have hEτ : IsEqC L (T.pos i + 1 + 1) T.J T.thr τ := ⟨hτ2, hτ3⟩
  refine ⟨bigOp L (T.pos i + 1 + 1) Pi τ, bigOp L (T.pos i + 1 + 1) Pi ϖ,
    bigOp_Y L (T.pos i + 1 + 1) _ T.J T.thr Pi τ hPi hEτ, ?_, ?_, ?_, ?_⟩
  ·
    intro y hy
    have hint : ∀ μ v, v ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr → (GA p L (T.pos i + 1 + 1)).IsHW μ v →
        v ∈ IntPol p (Fin N × Fin r) → τ v ∈ IntPol p (Fin N × Fin r) := by
      intro μ v hv hw hvi
      have h1 := hspZ μ v hv hw hvi
      refine Submodule.span_induction (p := fun v _ => τ v ∈ IntPol p (Fin N × Fin r)) ?_ ?_ ?_ ?_ h1
      · rintro _ ⟨x, rfl⟩
        rw [hτ1]; exact hgτi x
      · rw [map_zero]; exact Submodule.zero_mem _
      · intro a b _ _ ha hb
        rw [map_add]; exact Submodule.add_mem _ ha hb
      · intro a b _ hb
        rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ a hb
    exact int_main L ρ e1 (T.pos i + 1 + 1) hK hHP hHW (bigOp L (T.pos i + 1 + 1) Pi τ) (e1 * (T.pos i + 1 + 1))
      (bigOp_glAct L (T.pos i + 1 + 1) _ T.J T.thr Pi τ hPi hEτ)
      (fun la0 x hx hxi => bigOp_int L (T.pos i + 1 + 1) _ T.J T.thr Pi τ hPi hEτ hint la0 x hx hxi)
      y (Submodule.mem_inf.mp hy).2
  ·
    intro u hu u' hu'
    have hcore : ∀ g ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr, ∀ g' ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr,
        fock p (T.phi p L i g) (inOp L (T.pos i + 1 + 1) Pi τ g') =
          c * fock p (inOp L (T.pos i + 1 + 1) Pi ϖ g) g' := by
      intro g hg g' hg'
      rw [inOp_C L (T.pos i + 1 + 1) _ T.J T.thr Pi τ hPi g' hg', inOp_C L (T.pos i + 1 + 1) _ T.J T.thr Pi ϖ hPi g hg]
      let B : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p] :=
        (fockB p (Fin N × Fin r)).compl₁₂ (T.phi p L i) τ - c • (fockB p (Fin N × Fin r)).compl₁₂ ϖ LinearMap.id
      have hBa : ∀ x y, B x y = fock p (T.phi p L i x) (τ y) - c * fock p (ϖ x) y := by
        intro x y
        simp [B, fockB_apply]
      have hBz := GlX.form_zero (GA p L (T.pos i + 1 + 1)) hCst h' la hh hhC hsp B ?_ ?_ g hg g' hg'
      · rw [hBa] at hBz; exact sub_eq_zero.mp hBz
      · intro x hx y hy a b
        rw [hBa, hBa]
        change fock p (T.phi p L i (glAct p L (T.pos i + 1 + 1) a b x)) (τ y) -
          c * fock p (ϖ (glAct p L (T.pos i + 1 + 1) a b x)) y =
          fock p (T.phi p L i x) (τ (glAct p L (T.pos i + 1 + 1) b a y)) -
          c * fock p (ϖ x) (glAct p L (T.pos i + 1 + 1) b a y)
        rw [phi_glAct L T hadm i a b x, fock_glAct, hEτ.comm y hy b a, hEϖ.comm x hx a b, fock_glAct]
      · intro x y hxy
        rw [hBa, hτ1, hϖ1]
        have hterm : ∀ z, tc z y * fock p (T.phi p L i (h' x)) (h'' z) =
            if z = x then (if ‖d x‖ < (p : ℝ) ^ (-E) then 0 else c * fock p (h' x) (h' y)) else 0 := by
          intro z
          by_cases hz : la z = la y ∧ ¬ ‖d z‖ < (p : ℝ) ^ (-E)
          · have h1 := hdiag x z (hxy.trans hz.1.symm)
            simp only [tc, if_pos hz]
            have h2 : c / d z * (cst * fock p (h' z) (h' y)) * fock p (T.phi p L i (h' x)) (h'' z) =
                c / d z * fock p (h' z) (h' y) * (cst * fock p (T.phi p L i (h' x)) (h'' z)) := by ring
            rw [h2, h1]
            by_cases hzx : z = x
            · subst hzx
              rw [if_pos rfl, if_pos rfl, if_neg hz.2]
              have hd0 := (good_norm E hE (d z) hz.2).2
              field_simp
            · rw [if_neg (Ne.symm hzx), if_neg hzx, mul_zero]
          · simp only [tc, if_neg hz, zero_mul]
            by_cases hzx : z = x
            · subst hzx
              rw [if_pos rfl]
              have : ‖d z‖ < (p : ℝ) ^ (-E) := by
                by_contra h; exact hz ⟨hxy, h⟩
              rw [if_pos this]
            · rw [if_neg hzx]
        have hsum : fock p (T.phi p L i (h' x)) (gτ y) =
            if ‖d x‖ < (p : ℝ) ^ (-E) then 0 else c * fock p (h' x) (h' y) := by
          simp only [gτ]
          rw [gammaIntegralityLemmas.fock_sum_right]
          simp only [gammaIntegralityLemmas.fock_smul_right, hterm]
          rw [Finset.sum_ite_eq']
          simp
        rw [hsum]
        by_cases hx : ‖d x‖ < (p : ℝ) ^ (-E)
        · simp only [gϖ, if_pos hx]
          rw [gammaIntegralityLemmas.fock_zero_left]; ring
        · simp only [gϖ, if_neg hx]
          ring
    have key := fock_ext_reduce (T.pos i + 1 + 1) (T.phi p L i) (inOp L (T.pos i + 1 + 1) Pi τ)
      (inOp L (T.pos i + 1 + 1) Pi ϖ) c (Cset p L (T.pos i + 1 + 1) T.J T.thr)
      (phi_mul_later L T hadm i) (phi_isF L T hadm i)
      (inOp_isF L (T.pos i + 1 + 1) _ T.J T.thr Pi τ hPi hEτ) (inOp_isF L (T.pos i + 1 + 1) _ T.J T.thr Pi ϖ hPi hEϖ)
      hcore u u'
      (fun m => by rw [← Cset_thrUpTo]; exact slc_C L (T.pos i + 1 + 1) T.J (T.thrUpTo i) hu m)
      (fun m => slc_C L (T.pos i + 1 + 1) T.J T.thr hu' m)
    unfold fockN
    change fock p (T.phi p L i u) (ext (fsj N r (T.pos i + 1 + 1)) (inOp L (T.pos i + 1 + 1) Pi τ) u') / _ =
      c * (fock p (ext (fsj N r (T.pos i + 1 + 1)) (inOp L (T.pos i + 1 + 1) Pi ϖ) u) u' / _)
    rw [key, mul_div_assoc]
  · intro j hij u
    exact phi_ext_comm L T hadm i j hij _ (inOp_isF L (T.pos i + 1 + 1) _ T.J T.thr Pi ϖ hPi hEϖ) u
  · exact (count_le L (T.pos i + 1 + 1) _ T.J T.thr Pi hPi h' la hh hhC hli hsp
      (fun x => ‖d x‖ < (p : ℝ) ^ (-E)) ϖ hEϖ
      (fun x hx => hϖ6 x (by simp only [gϖ, if_neg hx]))
      (fun x hx => hϖ7 x (by simp only [gϖ, if_pos hx]))).trans
      (Finset.sum_le_sum fun x _ => transport_le L (T.pos i + 1 + 1) _ T.J T.thr Pi hPi h' la hh hhC hli hsp x (vv x)
        (hvv x) (hvvC x) (hvv0 x))

/- English proof (translation)
The claim follows from `(Submodule.mem_inf.mp hg).1`.
-/
theorem mmwZ_mmw [NeZero r] {K : ℕ} (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) {g : MvPolynomial (Fin K × Fin r) ℚ_[p]} (hg : g ∈ MMwZ p LLw J M ρ w) :
    g ∈ MMw p LLw J M ρ w := (Submodule.mem_inf.mp hg).1

/- English proof (translation)
The claim follows from `Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hg).1).1).1).1, (Submodule.mem_inf.mp hg).2⟩`.
-/
theorem mmwZ_polZ [NeZero r] {K : ℕ} (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) {g : MvPolynomial (Fin K × Fin r) ℚ_[p]} (hg : g ∈ MMwZ p LLw J M ρ w) :
    g ∈ PolZ p r LLw :=
  Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp
    (Submodule.mem_inf.mp hg).1).1).1).1, (Submodule.mem_inf.mp hg).2⟩

/- English proof (translation)
Use `⟨3, by norm_num, ?_⟩` and prove the remaining obligations. Introduce `p _ N r _ _ LL T a E κ n ρ _hp2 hr hρ hadm hE hSn hdeg _hz hκ hHP hHW _hL4 nb f U V dg fw hf hUV hfw i`. Establish `hK : T.pos i + 1 + 1 ≤ N` using `hK_of_adm LL T hadm i`. Establish `hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i`. Rewrite using `[S_eq_total (LL.setTies T n) T i (by omega)]; exact hSn i`.

Establish `hni : n i ≤ 2 * a`. Use `hdeg ⟨T.pos i + 1, by omega⟩` as an intermediate fact. Rewrite `this` using `[setTies_deg_eta LL T hadm i n (by omega)]`. Then use the resulting hypothesis. Take `⟨coef, hcoef⟩ : ∃ coef : ℕ, coef = (((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i)) + n i + r + T.z i - 1).choose (((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i)))` from `⟨_, rfl⟩`. Take `⟨NN, hNN⟩ : ∃ NN : ℚ_[p], NN = ((((n i - ((LL.setTies T n).takeD (T.pos i + 1)).total).factorial * ((LL.setTies T n).takeD (T.pos i + 1)).total.factorial : ℕ) : ℚ_[p]) * ∏ x, ((((LL.setTies T n).takeD (T.pos i + 1)).deg x).factorial : ℚ_[p]))` from `⟨_, rfl⟩`.

Take `⟨cst, hcst⟩ : ∃ cst : ℚ_[p], cst = (p : ℚ_[p]) ^ ⌈κ⌉₊ * (coef : ℚ_[p]) / NN` from `⟨_, rfl⟩`. Establish `hgam : ∀ g g', (p : ℚ_[p]) ^ ⌈κ⌉₊ * tieGam p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (T.z i) (n i) g g' = cst * fock p (T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) g)) (T.Ffull p (LL.setTies T n) i ρ (n i) g')`. Introduce `g g'`. Rewrite using `[gam_eq LL T hadm i ρ n g g', ← hcoef, ← hNN, hcst]`. Expand and normalize the polynomial expressions, which then agree.

Set `B : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p]` to `cst • ((fockB p (Fin N × Fin r)).compl₁₂ ((T.phi p (LL.setTies T n) i) ∘ₗ FfL p (LL.setTies T n) T i ρ (n i)) (FfL p (LL.setTies T n) T i ρ (n i)))`. Establish `hB : ∀ g g', B g g' = cst * fock p (T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) g)) (T.Ffull p (LL.setTies T n) i ρ (n i) g')`. Introduce `g g'`. Simplify using `[B, fockB_apply, FfL_apply]`. Establish `hsm : ∀ w, ∃ f' f'' : Fin (nb i w) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p], (∀ a, f' a ∈ MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) ∧ (∀ a, f'' a ∈ MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) ∧ LinearIndependent ℚ_[p] f' …`.

Introduce `w`. Take `⟨hU1, hV1, hU2, hV2, hfac⟩` from `hUV i w`. Use `smith_bases (nb i w) (f i w) _ (hf i w).1 (hf i w).2 B (U i w) (V i w) (dg i w) hU1 hV1 hU2 hV2 ?_` and prove the remaining obligations. Rewrite using `[← hfac]`. Use extensionality with `x y`.

Simplify using `only [Matrix.of_apply]`. Rewrite using `[hB, hgam]`. Use `choose f' f'' hf'1 hf''1 hf'li hf'sp hf'diag using hsm`. Take `⟨Ω, hΩ⟩ : ∃ Ω : Finset (Fin r → ℤ), ∀ w, w ∈ Ω ↔ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ≠ ⊥` from `⟨(mmw_finite (p := p) LL T i ρ n).toFinset, fun w => by simp⟩`. Establish `hnb0 : ∀ w, w ∉ Ω → nb i w = 0`.

Introduce `w hw`. Assume the negation of the conclusion as `h0`. Establish `hbot : MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w = ⊥`. Assume the negation of the conclusion as `h`. Conclude with `hw ((hΩ w).mpr h)`.

Establish `hmem : f i w ⟨0, Nat.pos_of_ne_zero h0⟩ ∈ MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w`. Rewrite using `[← (hf i w).2]`. Conclude with `Submodule.subset_span ⟨_, rfl⟩`. Establish `h1` using `mmwZ_mmw _ _ _ _ _ hmem`. Rewrite `h1` using `[hbot, Submodule.mem_bot]`.

Conclude with `(hf i w).1.ne_zero _ h1`. Establish `hκ' : ((T.pos i + 3) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ`. Use `le_trans ?_ hκ` and prove the remaining obligations. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).one_lt`. Establish `hlg : 0 ≤ lgV2 p a r`.

Unfold `lgV2`. Establish `: (1 : ℝ) ≤ 8 * (a : ℝ) + r`. Establish `: (2 : ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `: (0 : ℝ) ≤ a` using `Nat.cast_nonneg a`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `Real.logb_nonneg hp1 this` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : ((T.pos i : ℝ) + 3) ≤ (N : ℝ) + 2`. Establish `: ((T.pos i + 1 + 1 : ℕ) : ℝ) ≤ (N : ℝ)` using `by exact_mod_cast hK`. Move the coercions through the operations in `at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity)) hlg`. Establish `hspZ : ∀ μ v, v ∈ Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr → (GA p (LL.setTies T n) (T.pos i + 1 + 1)).IsHW μ v → v ∈ IntPol p (Fin N × Fin r) → v ∈ Submodule.span ℤ_[p] (Set.range fun x : (Σ w : Ω, Fin (nb i w.1)) => T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2) …`. Introduce `μ v hv hw hvi`. Take `⟨g, hg, rfl⟩` from `hw_is_Ffull LL T hadm i ρ hρ n hS μ v hv hw hvi`.

Distinguish the cases in `hwΩ : (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1) ∈ Ω`. Establish `hg'` using `hf'sp _ hg`. Use `Submodule.span_induction (p := fun g _ => T.Ffull p (LL.setTies T n) i ρ (n i) g ∈ Submodule.span ℤ_[p] (Set.range fun x : (Σ w : Ω, Fin (nb i w.1)) => T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2))) ?_ ?_ ?_ ?_ hg'` and prove the remaining obligations. Introduce and unpack `_ ⟨b, rfl⟩`. Conclude with `Submodule.subset_span ⟨⟨⟨_, hwΩ⟩, b⟩, rfl⟩`.

Rewrite using `[← FfL_apply, map_zero]`. Conclude with `Submodule.zero_mem _`. Introduce `x y _ _ hx hy`. Rewrite using `[← FfL_apply, map_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Introduce `c x _ hx`. Rewrite using `[← FfL_apply, LinearMap.map_smul_of_tower]`. Conclude with `Submodule.smul_mem _ c hx`. Establish `hbot : MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1) = ⊥`. Assume the negation of the conclusion as `h`.

Conclude with `hwΩ ((hΩ _).mpr h)`. Establish `h1` using `mmwZ_mmw _ _ _ _ _ hg`. Rewrite `h1` using `[hbot, Submodule.mem_bot]`. Rewrite using `[h1, ← FfL_apply, map_zero]`. Conclude with `Submodule.zero_mem _`.

Establish `hdiag : ∀ x y : (Σ w : Ω, Fin (nb i w.1)), x.1.1 - ((n i : ℕ) : ℤ) • (Pi.single ρ 1 : Fin r → ℤ) = y.1.1 - ((n i : ℕ) : ℤ) • Pi.single ρ 1 → cst * fock p (T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2))) (T.Ffull p (LL.setTies T n) i ρ (n i) (f'' …`. Introduce and unpack `⟨⟨w, hw⟩, b⟩ ⟨⟨w', hw'⟩, b'⟩ hla`. Establish `hww : w = w'` using `sub_left_injective hla`. Substitute `hww` using the available equality. Use `hf'diag w b b'` as an intermediate fact.

Rewrite `this` using `[hB]`. Simplify using `only`. Rewrite using `[this]`. Distinguish the cases in `hbb : b = b'`. Substitute `hbb` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[if_neg hbb, if_neg]`. Introduce `h`. Apply `hbb` to reduce the goal to its premises. Simplify using `using h`.

Establish `hG0 : ∀ x y : (Σ w : Ω, Fin (nb i w.1)), ‖cst * fock p (T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2)) (T.Ffull p (LL.setTies T n) i ρ (n i) (f' y.1.1 y.2))‖ ≤ 1`. Introduce `x y`. Rewrite using `[fock_Ffull LL T hadm i ρ n]`. Establish `hg` using `gamma_zero_integral_alt (p := p) (T.pos i) r ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) a κ hS hni hκ' (f' x.1.1 x.2) (f' y.1.1 y.2) (mmwZ_polZ _ _ _ _ _ (hf'1 x.1.1 x.2)) (mmwZ_polZ _ _ _ _ _ (hf'1 y.1.1 y.2))`. Rewrite `hg` using `[← hNN]`.

Establish `e : cst * fock p (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) (f' x.1.1 x.2)) (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) (f' y.1.1 y.2)) = (coef : ℚ_[p]) * ((p : ℚ_[p]) ^ ⌈κ⌉₊ * (fock p (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) (f' x.1.1 x …`. Rewrite using `[hcst]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, norm_mul]`. Conclude with `mul_le_one₀ (gammaIntegralityLemmas.norm_natCast_le_one' coef) (norm_nonneg _) hg`.

Take `⟨Tm, πm, h1, h2, h3, h4, h5⟩` from `tie_core (LL.setTies T n) T hadm i ρ ⌈κ / (N + 2)⌉₊ hK hHP hHW E (by linarith) (ι := Σ w : Ω, Fin (nb i w.1)) (fun x => T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2)) (fun x => T.Ffull p (LL.setTies T n) i ρ (n i) (f'' x.1.1 x.2)) (fun x => x.1.1 - ((n i : ℕ) : ℤ) • Pi.sing …`. Use `⟨Tm, πm, ⌈κ / (N + 2)⌉₊ * (T.pos i + 1 + 1) + 2 * ⌈κ / (N + 2)⌉₊, K_bound N r a (T.pos i + 1 + 1) κ hr hK hκ, h1, h2, h3, fun j hij u _ => h4 j hij u, ?_⟩` and prove the remaining obligations. Establish `hsumN : ∑ x ∈ univ.filter (fun x : (Σ w : Ω, Fin (nb i w.1)) => ‖dg i x.1.1 x.2‖ < (p : ℝ) ^ (-E)), Module.finrank ℚ_[p] (YYs (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr (T.Ffull p (LL.setTies T n) i ρ (n i) (fw i x.1.1))) = ∑ w ∈ Ω, (univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ …`. Rewrite using `[Finset.sum_filter, Fintype.sum_sigma, ← Finset.sum_coe_sort Ω]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_filter, YYsp_eq]`. Conclude with `Finset.sum_const_nat (fun _ _ => rfl)`. Establish `hfs : ∑ᶠ w, ((univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card : ℝ) * (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) : ℝ) = ∑ w ∈ Ω, ((univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card : ℝ) * (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) : ℝ)`. Use `finsum_eq_sum_of_support_subset _ fun w hw => ?_` and prove the remaining obligations. Rewrite using `[Finset.mem_coe]`.

Assume the negation of the conclusion as `hwΩ`. Use `hw ?_` and prove the remaining obligations. Establish `hle : (univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card ≤ nb i w` using `(Finset.card_le_univ _).trans (by simp)`. Establish `hle0` using `Nat.le_zero.mp (hle.trans (hnb0 w hwΩ).le)`. Simplify using `only [hle0, Nat.cast_zero, zero_mul]`.

Rewrite using `[hfs]`. Rewrite `h5` using `[hsumN]`. Conclude with `h5` after adjusting the coercions.
-/
theorem tieOps_main : Formalism.CountingSumsFrames.TieOps := by
  refine ⟨3, by norm_num, ?_⟩
  intro p _ N r _ _ LL T a E κ n ρ _hp2 hr hρ hadm hE hSn hdeg _hz hκ hHP hHW _hL4 nb f U V dg fw hf hUV hfw i
  classical
  have hK : T.pos i + 1 + 1 ≤ N := hK_of_adm LL T hadm i
  have hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i := by
    rw [S_eq_total (LL.setTies T n) T i (by omega)]; exact hSn i
  have hni : n i ≤ 2 * a := by
    have := hdeg ⟨T.pos i + 1, by omega⟩
    rwa [setTies_deg_eta LL T hadm i n (by omega)] at this
  obtain ⟨coef, hcoef⟩ : ∃ coef : ℕ, coef =
      (((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i)) + n i + r + T.z i - 1).choose
          (((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i))) := ⟨_, rfl⟩
  obtain ⟨NN, hNN⟩ : ∃ NN : ℚ_[p], NN =
      ((((n i - ((LL.setTies T n).takeD (T.pos i + 1)).total).factorial *
            ((LL.setTies T n).takeD (T.pos i + 1)).total.factorial : ℕ) : ℚ_[p]) *
          ∏ x, ((((LL.setTies T n).takeD (T.pos i + 1)).deg x).factorial : ℚ_[p])) := ⟨_, rfl⟩
  obtain ⟨cst, hcst⟩ : ∃ cst : ℚ_[p], cst = (p : ℚ_[p]) ^ ⌈κ⌉₊ * (coef : ℚ_[p]) / NN := ⟨_, rfl⟩
  have hgam : ∀ g g', (p : ℚ_[p]) ^ ⌈κ⌉₊ * tieGam p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (T.z i) (n i) g g' =
      cst * fock p (T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) g))
        (T.Ffull p (LL.setTies T n) i ρ (n i) g') := by
    intro g g'
    rw [gam_eq LL T hadm i ρ n g g', ← hcoef, ← hNN, hcst]
    ring
  let B : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]]
      MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p] :=
    cst • ((fockB p (Fin N × Fin r)).compl₁₂ ((T.phi p (LL.setTies T n) i) ∘ₗ FfL p (LL.setTies T n) T i ρ (n i))
      (FfL p (LL.setTies T n) T i ρ (n i)))
  have hB : ∀ g g', B g g' = cst * fock p (T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) g))
        (T.Ffull p (LL.setTies T n) i ρ (n i) g') := by
    intro g g'
    simp [B, fockB_apply, FfL_apply]
  have hsm : ∀ w, ∃ f' f'' : Fin (nb i w) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p],
      (∀ a, f' a ∈ MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) ∧
      (∀ a, f'' a ∈ MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) ∧
      LinearIndependent ℚ_[p] f' ∧
      MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ≤ Submodule.span ℤ_[p] (Set.range f') ∧
      ∀ a b, B (f' a) (f'' b) = if a = b then dg i w a else 0 := by
    intro w
    obtain ⟨hU1, hV1, hU2, hV2, hfac⟩ := hUV i w
    refine smith_bases (nb i w) (f i w) _ (hf i w).1 (hf i w).2 B (U i w) (V i w) (dg i w) hU1 hV1 hU2 hV2 ?_
    rw [← hfac]
    ext x y
    simp only [Matrix.of_apply]
    rw [hB, hgam]
  choose f' f'' hf'1 hf''1 hf'li hf'sp hf'diag using hsm
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : Finset (Fin r → ℤ), ∀ w, w ∈ Ω ↔
      MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ≠ ⊥ :=
    ⟨(mmw_finite (p := p) LL T i ρ n).toFinset, fun w => by simp⟩
  have hnb0 : ∀ w, w ∉ Ω → nb i w = 0 := by
    intro w hw
    by_contra h0
    have hbot : MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w = ⊥ := by
      by_contra h; exact hw ((hΩ w).mpr h)
    have hmem : f i w ⟨0, Nat.pos_of_ne_zero h0⟩ ∈
        MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w := by
      rw [← (hf i w).2]; exact Submodule.subset_span ⟨_, rfl⟩
    have h1 := mmwZ_mmw _ _ _ _ _ hmem
    rw [hbot, Submodule.mem_bot] at h1
    exact (hf i w).1.ne_zero _ h1
  have hκ' : ((T.pos i + 3) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ := by
    refine le_trans ?_ hκ
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have hlg : 0 ≤ lgV2 p a r := by
      unfold lgV2
      have : (1 : ℝ) ≤ 8 * (a : ℝ) + r := by
        have : (2 : ℝ) ≤ r := by exact_mod_cast hr
        have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
        linarith
      have := Real.logb_nonneg hp1 this
      linarith
    have h1 : ((T.pos i : ℝ) + 3) ≤ (N : ℝ) + 2 := by
      have : ((T.pos i + 1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hK
      push_cast at this; linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity)) hlg
  have hspZ : ∀ μ v, v ∈ Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr →
      (GA p (LL.setTies T n) (T.pos i + 1 + 1)).IsHW μ v → v ∈ IntPol p (Fin N × Fin r) →
      v ∈ Submodule.span ℤ_[p] (Set.range fun x : (Σ w : Ω, Fin (nb i w.1)) =>
          T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2)) := by
    intro μ v hv hw hvi
    obtain ⟨g, hg, rfl⟩ := hw_is_Ffull LL T hadm i ρ hρ n hS μ v hv hw hvi
    by_cases hwΩ : (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1) ∈ Ω
    · have hg' := hf'sp _ hg
      refine Submodule.span_induction (p := fun g _ => T.Ffull p (LL.setTies T n) i ρ (n i) g ∈
        Submodule.span ℤ_[p] (Set.range fun x : (Σ w : Ω, Fin (nb i w.1)) =>
          T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2))) ?_ ?_ ?_ ?_ hg'
      · rintro _ ⟨b, rfl⟩
        exact Submodule.subset_span ⟨⟨⟨_, hwΩ⟩, b⟩, rfl⟩
      · rw [← FfL_apply, map_zero]; exact Submodule.zero_mem _
      · intro x y _ _ hx hy
        rw [← FfL_apply, map_add]; exact Submodule.add_mem _ hx hy
      · intro c x _ hx
        rw [← FfL_apply, LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ c hx
    · have hbot : MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ
          (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1) = ⊥ := by
        by_contra h; exact hwΩ ((hΩ _).mpr h)
      have h1 := mmwZ_mmw _ _ _ _ _ hg
      rw [hbot, Submodule.mem_bot] at h1
      rw [h1, ← FfL_apply, map_zero]; exact Submodule.zero_mem _
  have hdiag : ∀ x y : (Σ w : Ω, Fin (nb i w.1)),
      x.1.1 - ((n i : ℕ) : ℤ) • (Pi.single ρ 1 : Fin r → ℤ) = y.1.1 - ((n i : ℕ) : ℤ) • Pi.single ρ 1 →
      cst * fock p (T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2)))
        (T.Ffull p (LL.setTies T n) i ρ (n i) (f'' y.1.1 y.2)) = if x = y then dg i x.1.1 x.2 else 0 := by
    rintro ⟨⟨w, hw⟩, b⟩ ⟨⟨w', hw'⟩, b'⟩ hla
    have hww : w = w' := sub_left_injective hla
    subst hww
    have := hf'diag w b b'
    rw [hB] at this
    simp only
    rw [this]
    by_cases hbb : b = b'
    · subst hbb; simp
    · rw [if_neg hbb, if_neg]
      intro h
      apply hbb
      simpa using h
  have hG0 : ∀ x y : (Σ w : Ω, Fin (nb i w.1)),
      ‖cst * fock p (T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2))
        (T.Ffull p (LL.setTies T n) i ρ (n i) (f' y.1.1 y.2))‖ ≤ 1 := by
    intro x y
    rw [fock_Ffull LL T hadm i ρ n]
    have hg := gamma_zero_integral_alt (p := p) (T.pos i) r ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) a κ hS hni hκ'
      (f' x.1.1 x.2) (f' y.1.1 y.2) (mmwZ_polZ _ _ _ _ _ (hf'1 x.1.1 x.2)) (mmwZ_polZ _ _ _ _ _ (hf'1 y.1.1 y.2))
    rw [← hNN] at hg
    have e : cst * fock p (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) (f' x.1.1 x.2))
        (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) (f' y.1.1 y.2)) =
        (coef : ℚ_[p]) * ((p : ℚ_[p]) ^ ⌈κ⌉₊ *
          (fock p (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) (f' x.1.1 x.2))
        (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) (f' y.1.1 y.2)) / NN)) := by
      rw [hcst]; ring
    rw [e, norm_mul]
    exact mul_le_one₀ (gammaIntegralityLemmas.norm_natCast_le_one' coef) (norm_nonneg _) hg
  obtain ⟨Tm, πm, h1, h2, h3, h4, h5⟩ := tie_core (LL.setTies T n) T hadm i ρ ⌈κ / (N + 2)⌉₊ hK hHP hHW E (by linarith)
    (ι := Σ w : Ω, Fin (nb i w.1))
    (fun x => T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2))
    (fun x => T.Ffull p (LL.setTies T n) i ρ (n i) (f'' x.1.1 x.2))
    (fun x => x.1.1 - ((n i : ℕ) : ℤ) • Pi.single ρ 1)
    (fun x => Ffull_hw LL T hadm i ρ hρ n x.1.1 _ (mmwZ_mmw _ _ _ _ _ (hf'1 x.1.1 x.2)) hS)
    (fun x => Ffull_C LL T hadm i ρ n hS x.1.1 _ (mmwZ_mmw _ _ _ _ _ (hf'1 x.1.1 x.2)))
    (Ffull_indep LL T hadm i ρ n hS Ω (nb i) f' (fun w a => mmwZ_mmw _ _ _ _ _ (hf'1 w a)) hf'li)
    hspZ
    (fun x => Ffull_hw LL T hadm i ρ hρ n x.1.1 _ (mmwZ_mmw _ _ _ _ _ (hf''1 x.1.1 x.2)) hS)
    (fun x => Ffull_C LL T hadm i ρ n hS x.1.1 _ (mmwZ_mmw _ _ _ _ _ (hf''1 x.1.1 x.2)))
    (fun x => Ffull_int LL T hadm i ρ n hS _ (mmwZ_polZ _ _ _ _ _ (hf''1 x.1.1 x.2)))
    (fun x => dg i x.1.1 x.2) cst hdiag hG0
    (fun x => T.Ffull p (LL.setTies T n) i ρ (n i) (fw i x.1.1))
    (fun x => Ffull_hw LL T hadm i ρ hρ n x.1.1 _ (hfw i x.1.1).1 hS)
    (fun x => Ffull_C LL T hadm i ρ n hS x.1.1 _ (hfw i x.1.1).1)
    (fun x => Ffull_ne LL T hadm i ρ n x.1.1 _ (hfw i x.1.1).1 ((hfw i x.1.1).2 ((hΩ _).mp x.1.2)) hS)
  refine ⟨Tm, πm, ⌈κ / (N + 2)⌉₊ * (T.pos i + 1 + 1) + 2 * ⌈κ / (N + 2)⌉₊,
    K_bound N r a (T.pos i + 1 + 1) κ hr hK hκ, h1, h2, h3, fun j hij u _ => h4 j hij u, ?_⟩
  have hsumN : ∑ x ∈ univ.filter (fun x : (Σ w : Ω, Fin (nb i w.1)) => ‖dg i x.1.1 x.2‖ < (p : ℝ) ^ (-E)),
      Module.finrank ℚ_[p] (YYs (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr
        (T.Ffull p (LL.setTies T n) i ρ (n i) (fw i x.1.1))) =
      ∑ w ∈ Ω, (univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card *
        Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) := by
    rw [Finset.sum_filter, Fintype.sum_sigma, ← Finset.sum_coe_sort Ω]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.sum_filter, YYsp_eq]
    exact Finset.sum_const_nat (fun _ _ => rfl)
  have hfs : ∑ᶠ w, ((univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) : ℝ) =
      ∑ w ∈ Ω, ((univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) : ℝ) := by
    refine finsum_eq_sum_of_support_subset _ fun w hw => ?_
    rw [Finset.mem_coe]
    by_contra hwΩ
    refine hw ?_
    have hle : (univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card ≤ nb i w :=
      (Finset.card_le_univ _).trans (by simp)
    have hle0 := Nat.le_zero.mp (hle.trans (hnb0 w hwΩ).le)
    simp only [hle0, Nat.cast_zero, zero_mul]
  rw [hfs]
  rw [hsumN] at h5
  exact_mod_cast h5

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames

/- English proof (translation)
The claim follows from `TO.tieOps_main`.
-/
theorem level_operators_exist : Formalism.CountingSumsFrames.TieOps := TO.tieOps_main

end Formalism.CountingSumsFrames
