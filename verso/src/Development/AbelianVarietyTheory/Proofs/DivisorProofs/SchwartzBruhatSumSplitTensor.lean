import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.SBBlocks

/- English proof (translation)
Establish `: Function.support f = (f ⁻¹' {0})ᶜ` using `by ext; simp`. Rewrite using `[this]`. Conclude with `(hf.isOpen_fiber 0).isClosed_compl`.
-/
theorem isClosed_support_of_isLocallyConstant {Z : Type} [TopologicalSpace Z] {f : Z → ℂ}
    (hf : IsLocallyConstant f) : IsClosed (Function.support f) := by
  have : Function.support f = (f ⁻¹' {0})ᶜ := by ext; simp
  rw [this]; exact (hf.isOpen_fiber 0).isClosed_compl

/- English proof (translation)
Assemble the required witnesses or components as `⟨hf, HasCompactSupport.intro' (hC.of_isClosed_subset (isClosed_support_of_isLocallyConstant hf) hs) (isClosed_support_of_isLocallyConstant hf) fun _ hx => Function.notMem_support.1 hx⟩`.
-/
theorem mem_SB_of_support_subset {Z : Type} [TopologicalSpace Z] {f : Z → ℂ} {C : Set Z}
    (hf : IsLocallyConstant f) (hC : IsCompact C) (hs : Function.support f ⊆ C) : f ∈ SB Z :=
  ⟨hf, HasCompactSupport.intro' (hC.of_isClosed_subset (isClosed_support_of_isLocallyConstant hf) hs)
    (isClosed_support_of_isLocallyConstant hf) fun _ hx => Function.notMem_support.1 hx⟩

/- English proof (translation)
Take `⟨hlc, hcs⟩` from `hh`. Establish `hK : IsCompact (tsupport h)` using `hcs.isCompact`. Establish `hK1 : IsCompact (Prod.fst '' tsupport h)` using `hK.image continuous_fst`. Establish `hK2 : IsCompact (Prod.snd '' tsupport h)` using `hK.image continuous_snd`. Establish `hzero : ∀ x y, h (x, y) ≠ 0 → x ∈ Prod.fst '' tsupport h ∧ y ∈ Prod.snd '' tsupport h` using `fun x y hne => ⟨⟨(x, y), subset_tsupport h hne, rfl⟩, ⟨(x, y), subset_tsupport h hne, rfl⟩⟩`.

Set `s : Y → X → ℂ` to `fun y x => h (x, y)`. Establish `hs : IsLocallyConstant s`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `y₀`. Establish `key : ∀ᶠ y in 𝓝 y₀, ∀ x ∈ Prod.fst '' tsupport h, h (x, y) = h (x, y₀)`.

Use `hK1.eventually_forall_of_forall_eventually (P := fun y x => h (x, y) = h (x, y₀)) ?_` and prove the remaining obligations. Introduce `x _`. Establish `h1 : IsLocallyConstant (fun z : Y × X => h (z.2, z.1))` using `hlc.comp_continuous continuous_swap`. Establish `h2 : IsLocallyConstant (fun z : Y × X => h (z.2, y₀))` using `hlc.comp_continuous (continuous_snd.prodMk continuous_const)`. Use `filter_upwards [h1.eventually_eq (y₀, x), h2.eventually_eq (y₀, x)] with z hz1 hz2`.

Rewrite using `[hz1, hz2]`. Use `filter_upwards [key] with y hy`. Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : x ∈ Prod.fst '' tsupport h`. Conclude with `hy x hx`.

Use `show h (x, y) = h (x, y₀)`. Rewrite using `[image_eq_zero_of_notMem_tsupport (fun hm => hx ⟨_, hm, rfl⟩), image_eq_zero_of_notMem_tsupport (fun hm => hx ⟨_, hm, rfl⟩)]`. Establish `hsSB : ∀ y, s y ∈ SB X` using `fun y => mem_SB_of_support_subset (hlc.comp_continuous (continuous_id.prodMk continuous_const)) hK1 (fun x hx => (hzero x y hx).1)`. Establish `hsne : ∀ y, s y ≠ 0 → y ∈ Prod.snd '' tsupport h` using `fun y hy => by`. Take `⟨x, hx⟩` from `Function.ne_iff.1 hy`.

Conclude with `(hzero x y hx).2`. Take `⟨t, ht⟩` from `hK2.elim_finite_subcover (fun φ : X → ℂ => s ⁻¹' {φ}) (fun φ => hs.isOpen_fiber φ) (fun y _ => Set.mem_iUnion.2 ⟨s y, rfl⟩)`. Set `t'` to `t.filter (fun φ => φ ≠ 0 ∧ φ ∈ SB X)`. Set `bb : (X → ℂ) → Y → ℂ` to `fun φ y => if s y = φ then 1 else 0`. Establish `hbSB : ∀ φ ∈ t', bb φ ∈ SB Y`.

Introduce `φ hφ`. Establish `hφ0 : φ ≠ 0` using `(Finset.mem_filter.1 hφ).2.1`. Use `mem_SB_of_support_subset (hs.comp fun v => if v = φ then (1 : ℂ) else 0) hK2 ?_` and prove the remaining obligations. Introduce `y hy`. Establish `: s y = φ`.

Assume the negation of the conclusion as `hne`. Conclude with `hy (if_neg hne)`. Conclude with `hsne y (this ▸ hφ0)`. Establish `hsum : ∀ x y, h (x, y) = ∑ φ ∈ t', φ x * bb φ y`. Introduce `x y`.

Apply the tactic sequence `have e1 : ∑ φ ∈ t', φ x * bb φ y = ∑ φ ∈ t', if s y = φ then φ x else 0 := Finset.sum_congr rfl fun φ _ => by simp only [bb]; split_ifs <;> simp`. Rewrite using `[e1, Finset.sum_ite_eq]`. Use `split_ifs with hin`. Both sides reduce to the same expression. Use `show s y x = 0`.

Assume the negation of the conclusion as `hne`. Establish `hy0 : s y ≠ 0` using `fun h0 => hne (by rw [h0]; rfl)`. Apply `hin` to reduce the goal to its premises. Take `⟨φ, hφ, hyφ⟩` from `Set.mem_iUnion₂.1 (ht (hsne y hy0))`. Establish `: s y = φ` using `hyφ`.

Conclude with `Finset.mem_filter.2 ⟨this ▸ hφ, hy0, hsSB y⟩`. Use `⟨t'.card, fun j => (t'.equivFin.symm j : X → ℂ), fun j => bb (t'.equivFin.symm j), fun j => (Finset.mem_filter.1 (t'.equivFin.symm j).2).2.2, fun j => hbSB _ (t'.equivFin.symm j).2, ?_⟩` and prove the remaining obligations. Introduce `x y`. Rewrite using `[hsum x y, ← Finset.sum_coe_sort t']`. Conclude with `(Equiv.sum_comp t'.equivFin.symm (fun φ : t' => (φ : X → ℂ) x * bb φ y)).symm`.
-/
theorem prod_decomp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (h : X × Y → ℂ)
    (hh : h ∈ SB (X × Y)) :
    ∃ (m : ℕ) (a : Fin m → X → ℂ) (b : Fin m → Y → ℂ), (∀ j, a j ∈ SB X) ∧ (∀ j, b j ∈ SB Y) ∧
      ∀ x y, h (x, y) = ∑ j, a j x * b j y := by
  classical
  obtain ⟨hlc, hcs⟩ := hh
  have hK : IsCompact (tsupport h) := hcs.isCompact
  have hK1 : IsCompact (Prod.fst '' tsupport h) := hK.image continuous_fst
  have hK2 : IsCompact (Prod.snd '' tsupport h) := hK.image continuous_snd
  have hzero : ∀ x y, h (x, y) ≠ 0 → x ∈ Prod.fst '' tsupport h ∧ y ∈ Prod.snd '' tsupport h :=
    fun x y hne => ⟨⟨(x, y), subset_tsupport h hne, rfl⟩, ⟨(x, y), subset_tsupport h hne, rfl⟩⟩
  let s : Y → X → ℂ := fun y x => h (x, y)
  have hs : IsLocallyConstant s := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro y₀
    have key : ∀ᶠ y in 𝓝 y₀, ∀ x ∈ Prod.fst '' tsupport h, h (x, y) = h (x, y₀) := by
      refine hK1.eventually_forall_of_forall_eventually (P := fun y x => h (x, y) = h (x, y₀)) ?_
      intro x _
      have h1 : IsLocallyConstant (fun z : Y × X => h (z.2, z.1)) := hlc.comp_continuous continuous_swap
      have h2 : IsLocallyConstant (fun z : Y × X => h (z.2, y₀)) :=
        hlc.comp_continuous (continuous_snd.prodMk continuous_const)
      filter_upwards [h1.eventually_eq (y₀, x), h2.eventually_eq (y₀, x)] with z hz1 hz2
      rw [hz1, hz2]
    filter_upwards [key] with y hy
    funext x
    by_cases hx : x ∈ Prod.fst '' tsupport h
    · exact hy x hx
    · show h (x, y) = h (x, y₀)
      rw [image_eq_zero_of_notMem_tsupport (fun hm => hx ⟨_, hm, rfl⟩),
        image_eq_zero_of_notMem_tsupport (fun hm => hx ⟨_, hm, rfl⟩)]
  have hsSB : ∀ y, s y ∈ SB X := fun y =>
    mem_SB_of_support_subset (hlc.comp_continuous (continuous_id.prodMk continuous_const)) hK1
      (fun x hx => (hzero x y hx).1)
  have hsne : ∀ y, s y ≠ 0 → y ∈ Prod.snd '' tsupport h := fun y hy => by
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hy
    exact (hzero x y hx).2
  obtain ⟨t, ht⟩ := hK2.elim_finite_subcover (fun φ : X → ℂ => s ⁻¹' {φ}) (fun φ => hs.isOpen_fiber φ)
    (fun y _ => Set.mem_iUnion.2 ⟨s y, rfl⟩)
  let t' := t.filter (fun φ => φ ≠ 0 ∧ φ ∈ SB X)
  let bb : (X → ℂ) → Y → ℂ := fun φ y => if s y = φ then 1 else 0
  have hbSB : ∀ φ ∈ t', bb φ ∈ SB Y := by
    intro φ hφ
    have hφ0 : φ ≠ 0 := (Finset.mem_filter.1 hφ).2.1
    refine mem_SB_of_support_subset (hs.comp fun v => if v = φ then (1 : ℂ) else 0) hK2 ?_
    intro y hy
    have : s y = φ := by
      by_contra hne
      exact hy (if_neg hne)
    exact hsne y (this ▸ hφ0)
  have hsum : ∀ x y, h (x, y) = ∑ φ ∈ t', φ x * bb φ y := by
    intro x y
    have e1 : ∑ φ ∈ t', φ x * bb φ y = ∑ φ ∈ t', if s y = φ then φ x else 0 :=
      Finset.sum_congr rfl fun φ _ => by simp only [bb]; split_ifs <;> simp
    rw [e1, Finset.sum_ite_eq]
    split_ifs with hin
    · rfl
    · show s y x = 0
      by_contra hne
      have hy0 : s y ≠ 0 := fun h0 => hne (by rw [h0]; rfl)
      apply hin
      obtain ⟨φ, hφ, hyφ⟩ := Set.mem_iUnion₂.1 (ht (hsne y hy0))
      have : s y = φ := hyφ
      exact Finset.mem_filter.2 ⟨this ▸ hφ, hy0, hsSB y⟩
  refine ⟨t'.card, fun j => (t'.equivFin.symm j : X → ℂ), fun j => bb (t'.equivFin.symm j),
    fun j => (Finset.mem_filter.1 (t'.equivFin.symm j).2).2.2, fun j => hbSB _ (t'.equivFin.symm j).2, ?_⟩
  intro x y
  rw [hsum x y, ← Finset.sum_coe_sort t']
  exact (Equiv.sum_comp t'.equivFin.symm (fun φ : t' => (φ : X → ℂ) x * bb φ y)).symm

/- English proof (translation)
Set `e : (κ ⊕ κ' → Af F) ≃ₜ (κ → Af F) × (κ' → Af F)` to `Homeomorph.sumArrowHomeomorphProdArrow`. Establish `hh : g ∘ e.symm ∈ SB ((κ → Af F) × (κ' → Af F))` using `⟨hg.1.comp_continuous e.symm.continuous, hg.2.comp_homeomorph e.symm⟩`. Take `⟨m, a, b, ha, hb, hab⟩` from `prod_decomp _ hh`. Use `⟨m, a, b, ha, hb, fun x x' => ?_⟩` and prove the remaining obligations. Rewrite using `[← hab]`.

Use `show g _ = g (e.symm (x, x'))`. Use `congr 1`.
-/
theorem sum_prod_blocks {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (g : (κ ⊕ κ' → Af F) → ℂ) (hg : g ∈ SB (κ ⊕ κ' → Af F)) :
    ∃ (m : ℕ) (a : Fin m → (κ → Af F) → ℂ) (b : Fin m → (κ' → Af F) → ℂ), (∀ j, a j ∈ SB (κ → Af F)) ∧
      (∀ j, b j ∈ SB (κ' → Af F)) ∧ ∀ x x', g (Sum.elim x x') = ∑ j, a j x * b j x' := by
  let e : (κ ⊕ κ' → Af F) ≃ₜ (κ → Af F) × (κ' → Af F) := Homeomorph.sumArrowHomeomorphProdArrow
  have hh : g ∘ e.symm ∈ SB ((κ → Af F) × (κ' → Af F)) :=
    ⟨hg.1.comp_continuous e.symm.continuous, hg.2.comp_homeomorph e.symm⟩
  obtain ⟨m, a, b, ha, hb, hab⟩ := prod_decomp _ hh
  refine ⟨m, a, b, ha, hb, fun x x' => ?_⟩
  rw [← hab]
  show g _ = g (e.symm (x, x'))
  congr 1

end GlobalTheory.SBBlocks
