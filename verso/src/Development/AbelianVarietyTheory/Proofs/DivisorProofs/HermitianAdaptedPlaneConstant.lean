import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenSubgroupsStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixEvAdm

/- English proof (translation)
Introduce `F _ _ κ _ N hNo hNc hNcof a`. Establish `hS : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∀ c : κ → v.adicCompletion F, IsOpen {x : κ → v.adicCompletion F | ∀ i, x i - c i ∈ N v} ∧ IsClosed {x : κ → v.adicCompletion F | ∀ i, x i - c i ∈ N v} ∧ IsCompact {x : κ → v.adicCompletion F | ∀ i, x i - c i ∈ N v}`. Introduce `v c`. Establish `e : {x : κ → v.adicCompletion F | ∀ i, x i - c i ∈ N v} = (fun x => x - c) ⁻¹' Set.pi Set.univ fun _ => (N v : Set (v.adicCompletion F))`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Establish `hcl : IsClosed (N v : Set (v.adicCompletion F))` using `(N v).isClosed_of_isOpen (hNo v)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `(isOpen_set_pi Set.finite_univ fun _ _ => hNo v).preimage (continuous_sub_right c)`.

Rewrite using `[e]`. Conclude with `(isClosed_set_pi fun _ _ => hcl).preimage (continuous_sub_right c)`. Establish `e2 : {x : κ → v.adicCompletion F | ∀ i, x i - c i ∈ N v} = (Homeomorph.subRight c).symm '' Set.pi Set.univ fun _ => (N v : Set (v.adicCompletion F))`. Rewrite using `[e, Homeomorph.image_symm]`. Both sides reduce to the same expression.

Rewrite using `[e2]`. Conclude with `(isCompact_univ_pi fun _ => hNc v).image (Homeomorph.subRight c).symm.continuous`. Establish `hint : ∀ y : κ → FiniteAdeleRing (𝓞 F) F, ∀ᶠ v in Filter.cofinite, ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ v.adicCompletionIntegers F` using `fun y => Filter.eventually_all.2 fun i => (y i).2`. Use `⟨fun v => Set.indicator {x | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (a i) ∈ N v} 1, fun v => ?_, ?_, fun y => ?_⟩` and prove the remaining obligations. Take `⟨ho, hc, hk⟩` from `hS v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (a i)`.

Use `⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_, HasCompactSupport.intro hk fun y hy => Set.indicator_of_notMem hy _⟩` and prove the remaining obligations. Use `set Sx := {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (a i) ∈ N v} with hSx`. Distinguish the cases in `hx : x ∈ Sx`. Use `filter_upwards [ho.mem_nhds hx] with z hz`. Rewrite using `[Set.indicator_of_mem hx, Set.indicator_of_mem (show z ∈ Sx from hz)]`.

Both sides reduce to the same expression. Use `filter_upwards [hc.isOpen_compl.mem_nhds hx] with z hz`. Rewrite using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem (show z ∉ Sx from hz)]`. Use `filter_upwards [hNcof, hint a] with v hv ha`. Use `congr 1`.

Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq]`. Use `forall_congr' fun i => ?_` and prove the remaining obligations. Rewrite using `[← SetLike.mem_coe, hv, SetLike.mem_coe]`. Conclude with `⟨fun h => by simpa using add_mem h (ha i), fun h => sub_mem h (ha i)⟩`.

Distinguish the cases in `hy : y ∈ {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i - a i) ∈ N v}`. Rewrite using `[Set.indicator_of_mem hy, Pi.one_apply]`. Use `(finprod_eq_one_of_forall_eq_one fun v => ?_).symm` and prove the remaining obligations. Use `Set.indicator_of_mem (fun i => ?_) _` and prove the remaining obligations. Simplify `hy i v` using `[map_sub]`.

Rewrite using `[Set.indicator_of_notMem hy]`. Simplify using `only [Set.mem_setOf_eq, not_forall] at hy`. Take `⟨i, v, hv⟩` from `hy`. Use `(finprod_eq_zero _ v (Set.indicator_of_notMem (fun h => hv (by simpa [map_sub] using h i)) _) ?_).symm` and prove the remaining obligations. Use `(Filter.eventually_cofinite.1 ((hNcof.and (hint a)).and (hint y))).subset fun w hw h' => hw ?_` and prove the remaining obligations.

Use `Set.indicator_of_mem (fun j => ?_) _` and prove the remaining obligations. Rewrite using `[← SetLike.mem_coe, h'.1.1, SetLike.mem_coe]`. Conclude with `sub_mem (h'.2 j) (h'.1.2 j)`.
-/
theorem coset_indicator_finprod : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (N : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)),
    (∀ v, IsOpen (N v : Set (v.adicCompletion F))) → (∀ v, IsCompact (N v : Set (v.adicCompletion F))) →
    (∀ᶠ v in Filter.cofinite, (N v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) →
    ∀ a : κ → FiniteAdeleRing (𝓞 F) F, ∃ φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → v.adicCompletion F) → ℂ,
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) ∧
      (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      ∀ y : κ → FiniteAdeleRing (𝓞 F) F,
        Set.indicator {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i - a i) ∈ N v} 1 y =
          ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) := by
  intro F _ _ κ _ N hNo hNc hNcof a
  classical
  have hS : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∀ c : κ → v.adicCompletion F,
      IsOpen {x : κ → v.adicCompletion F | ∀ i, x i - c i ∈ N v} ∧
      IsClosed {x : κ → v.adicCompletion F | ∀ i, x i - c i ∈ N v} ∧
      IsCompact {x : κ → v.adicCompletion F | ∀ i, x i - c i ∈ N v} := by
    intro v c
    have e : {x : κ → v.adicCompletion F | ∀ i, x i - c i ∈ N v} =
        (fun x => x - c) ⁻¹' Set.pi Set.univ fun _ => (N v : Set (v.adicCompletion F)) := by
      ext x; simp
    have hcl : IsClosed (N v : Set (v.adicCompletion F)) := (N v).isClosed_of_isOpen (hNo v)
    refine ⟨?_, ?_, ?_⟩
    · rw [e]; exact (isOpen_set_pi Set.finite_univ fun _ _ => hNo v).preimage (continuous_sub_right c)
    · rw [e]; exact (isClosed_set_pi fun _ _ => hcl).preimage (continuous_sub_right c)
    · have e2 : {x : κ → v.adicCompletion F | ∀ i, x i - c i ∈ N v} =
          (Homeomorph.subRight c).symm '' Set.pi Set.univ fun _ => (N v : Set (v.adicCompletion F)) := by
        rw [e, Homeomorph.image_symm]; rfl
      rw [e2]
      exact (isCompact_univ_pi fun _ => hNc v).image (Homeomorph.subRight c).symm.continuous
  have hint : ∀ y : κ → FiniteAdeleRing (𝓞 F) F, ∀ᶠ v in Filter.cofinite,
      ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ v.adicCompletionIntegers F := fun y =>
    Filter.eventually_all.2 fun i => (y i).2
  refine ⟨fun v => Set.indicator {x | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (a i) ∈ N v} 1, fun v => ?_, ?_, fun y => ?_⟩
  · obtain ⟨ho, hc, hk⟩ := hS v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (a i)
    refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_,
      HasCompactSupport.intro hk fun y hy => Set.indicator_of_notMem hy _⟩
    set Sx := {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (a i) ∈ N v} with hSx
    by_cases hx : x ∈ Sx
    · filter_upwards [ho.mem_nhds hx] with z hz
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show z ∈ Sx from hz)]
      rfl
    · filter_upwards [hc.isOpen_compl.mem_nhds hx] with z hz
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show z ∉ Sx from hz)]
  · filter_upwards [hNcof, hint a] with v hv ha
    congr 1
    ext x
    simp only [Set.mem_setOf_eq]
    refine forall_congr' fun i => ?_
    rw [← SetLike.mem_coe, hv, SetLike.mem_coe]
    exact ⟨fun h => by simpa using add_mem h (ha i), fun h => sub_mem h (ha i)⟩
  · by_cases hy : y ∈ {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i - a i) ∈ N v}
    · rw [Set.indicator_of_mem hy, Pi.one_apply]
      refine (finprod_eq_one_of_forall_eq_one fun v => ?_).symm
      refine Set.indicator_of_mem (fun i => ?_) _
      simpa [map_sub] using hy i v
    · rw [Set.indicator_of_notMem hy]
      simp only [Set.mem_setOf_eq, not_forall] at hy
      obtain ⟨i, v, hv⟩ := hy
      refine (finprod_eq_zero _ v (Set.indicator_of_notMem (fun h => hv (by simpa [map_sub] using h i)) _) ?_).symm
      refine (Filter.eventually_cofinite.1 ((hNcof.and (hint a)).and (hint y))).subset fun w hw h' => hw ?_
      refine Set.indicator_of_mem (fun j => ?_) _
      rw [← SetLike.mem_coe, h'.1.1, SetLike.mem_coe]
      exact sub_mem (h'.2 j) (h'.1.2 j)

end GlobalTheory.MixEvAdm

namespace GlobalTheory.MixEvAdm

/- English proof (translation)
Introduce `F _ _ κ _ g hg`. Establish `h1 : ∀ᶠ t in 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F), ∀ z ∈ tsupport g, g (z + t) = g z`. Use `IsCompact.eventually_forall_of_forall_eventually hg.2 fun z _ => ?_` and prove the remaining obligations. Establish `h2 : IsLocallyConstant fun q : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) => (g (q.2 + q.1), g q.2)` using `(hg.1.comp_continuous (by fun_prop)).prodMk (hg.1.comp_continuous continuous_snd)`. Use `filter_upwards [h2.eventually_eq (0, z)] with q hq`.

Simplify using `only [Prod.mk.injEq, add_zero] at hq`. Rewrite using `[hq.1, hq.2]`. Take `⟨N, hNo, hNc, hNcof, hPn, hPV⟩` from `GlobalTheory.T.exists_compact_open_subgroups F κ _ h1`. Set `U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)` to `{ carrier := {y | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ N v} zero_mem' := fun i v => by simp add_mem' := fun ha hb i v => by simpa [map_add] using add_mem (ha i v) (hb i v) neg_mem' := fun ha i v => by simpa [map_neg] using neg_mem (ha …`. Establish `hinv : ∀ u ∈ U, ∀ z, g (z + u) = g z` using `fun u hu z => by`.

Distinguish the cases in `hz : z ∈ tsupport g`. Conclude with `hPV hu z hz`. Distinguish the cases in `hz' : z + u ∈ tsupport g`. Use `hPV (U.neg_mem hu) _ hz'` as an intermediate fact. Rewrite `this` using `[add_neg_cancel_right]`.

Conclude with `this.symm`. Rewrite using `[image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']`. Take `⟨t, -, ht⟩` from `hg.2.elim_nhds_subcover (fun a => (fun b => b - a) ⁻¹' (U : Set _)) (fun a _ => (continuous_sub_right a).continuousAt.preimage_mem_nhds (by show (U : Set _) ∈ 𝓝 (a - a); rw [sub_self]; exact hPn))`. Use `set Tq := t.image (QuotientAddGroup.mk : _ → _ ⧸ U)`. Establish `hind : ∀ (y : κ → FiniteAdeleRing (𝓞 F) F) (q : _ ⧸ U), Set.indicator {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i - q.out i) ∈ N v} 1 y = if (y : _ ⧸ U) = q then (1 : ℂ) else 0`.

Introduce `y q`. Establish `: (y : _ ⧸ U) = q ↔ y - q.out ∈ U` using `by conv_lhs => rw [← QuotientAddGroup.out_eq' q]`. Conclude with `QuotientAddGroup.eq_iff_sub_mem`. Distinguish the cases in `h : y - q.out ∈ U`. Rewrite using `[Set.indicator_of_mem (show y ∈ {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i - q.out i) ∈ N v} from h), if_pos (this.mpr h), Pi.one_apply]`.

Rewrite using `[Set.indicator_of_notMem (show y ∉ {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i - q.out i) ∈ N v} from h), if_neg (fun h' => h (this.mp h'))]`. Establish `key : ∀ y, g y = ∑ q ∈ Tq, g q.out * Set.indicator {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i - q.out i) ∈ N v} 1 y`. Introduce `y`. Simplify using `only [hind, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq']`. Use `split_ifs with h`.

Establish `h2 : -y + (y : _ ⧸ U).out ∈ U` using `QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' _).symm`. Use `hinv _ h2 y` as an intermediate fact. Rewrite `this` using `[add_neg_cancel_left]`. Conclude with `this.symm`. Assume the negation of the conclusion as `hne`.

Establish `hy : y ∈ tsupport g` using `subset_tsupport _ hne`. Take `⟨x, hx, hyx⟩` from `Set.mem_iUnion₂.mp (ht hy)`. Use `h (Finset.mem_image.mpr ⟨x, hx, ?_⟩)` and prove the remaining obligations. Conclude with `(QuotientAddGroup.eq_iff_sub_mem.mpr hyx).symm`. Use `choose φq hφSB hφstd hφeq using fun q : _ ⧸ U => coset_indicator_finprod F κ N hNo hNc hNcof q.out`.

Set `e` to `Tq.equivFin`. Use `⟨Tq.card, fun j => g (e.symm j).1.out, fun j => φq (e.symm j).1, fun j v => hφSB _ v, fun j => hφstd _, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `y`. Rewrite using `[key y]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hφeq]`.

Rewrite using `[← Finset.sum_coe_sort Tq]`. Conclude with `(Equiv.sum_comp e.symm (fun q : Tq => g q.1.out * ∏ᶠ v, φq q.1 v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i))).symm`.
-/
theorem sb_decomp : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ (m : ℕ) (c : Fin m → ℂ) (φ : Fin m → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → v.adicCompletion F) → ℂ),
      (∀ j v, φ j v ∈ GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) ∧
      (∀ j, ∀ᶠ v in Filter.cofinite, φ j v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      g = ∑ j, c j • fun y => ∏ᶠ v, φ j v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) := by
  intro F _ _ κ _ g hg
  classical
  have h1 : ∀ᶠ t in 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F), ∀ z ∈ tsupport g, g (z + t) = g z := by
    refine IsCompact.eventually_forall_of_forall_eventually hg.2 fun z _ => ?_
    have h2 : IsLocallyConstant fun q : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
        (g (q.2 + q.1), g q.2) :=
      (hg.1.comp_continuous (by fun_prop)).prodMk (hg.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, z)] with q hq
    simp only [Prod.mk.injEq, add_zero] at hq
    rw [hq.1, hq.2]
  obtain ⟨N, hNo, hNc, hNcof, hPn, hPV⟩ := GlobalTheory.T.exists_compact_open_subgroups F κ _ h1
  let U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) :=
    { carrier := {y | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ N v}
      zero_mem' := fun i v => by simp
      add_mem' := fun ha hb i v => by simpa [map_add] using add_mem (ha i v) (hb i v)
      neg_mem' := fun ha i v => by simpa [map_neg] using neg_mem (ha i v) }
  have hinv : ∀ u ∈ U, ∀ z, g (z + u) = g z := fun u hu z => by
    by_cases hz : z ∈ tsupport g
    · exact hPV hu z hz
    by_cases hz' : z + u ∈ tsupport g
    · have := hPV (U.neg_mem hu) _ hz'
      rw [add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']
  obtain ⟨t, -, ht⟩ := hg.2.elim_nhds_subcover (fun a => (fun b => b - a) ⁻¹' (U : Set _))
    (fun a _ => (continuous_sub_right a).continuousAt.preimage_mem_nhds (by show (U : Set _) ∈ 𝓝 (a - a); rw [sub_self]; exact hPn))
  set Tq := t.image (QuotientAddGroup.mk : _ → _ ⧸ U)
  have hind : ∀ (y : κ → FiniteAdeleRing (𝓞 F) F) (q : _ ⧸ U),
      Set.indicator {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i - q.out i) ∈ N v} 1 y =
        if (y : _ ⧸ U) = q then (1 : ℂ) else 0 := by
    intro y q
    have : (y : _ ⧸ U) = q ↔ y - q.out ∈ U := by
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      exact QuotientAddGroup.eq_iff_sub_mem
    by_cases h : y - q.out ∈ U
    · rw [Set.indicator_of_mem (show y ∈ {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v,
        Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i - q.out i) ∈ N v} from h), if_pos (this.mpr h), Pi.one_apply]
    · rw [Set.indicator_of_notMem (show y ∉ {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v,
        Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i - q.out i) ∈ N v} from h), if_neg (fun h' => h (this.mp h'))]
  have key : ∀ y, g y = ∑ q ∈ Tq, g q.out *
      Set.indicator {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i - q.out i) ∈ N v} 1 y := by
    intro y
    simp only [hind, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq']
    split_ifs with h
    · have h2 : -y + (y : _ ⧸ U).out ∈ U := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' _).symm
      have := hinv _ h2 y
      rw [add_neg_cancel_left] at this
      exact this.symm
    · by_contra hne
      have hy : y ∈ tsupport g := subset_tsupport _ hne
      obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (ht hy)
      refine h (Finset.mem_image.mpr ⟨x, hx, ?_⟩)
      exact (QuotientAddGroup.eq_iff_sub_mem.mpr hyx).symm
  choose φq hφSB hφstd hφeq using fun q : _ ⧸ U => coset_indicator_finprod F κ N hNo hNc hNcof q.out
  let e := Tq.equivFin
  refine ⟨Tq.card, fun j => g (e.symm j).1.out, fun j => φq (e.symm j).1, fun j v => hφSB _ v, fun j => hφstd _, ?_⟩
  funext y
  rw [key y]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hφeq]
  rw [← Finset.sum_coe_sort Tq]
  exact (Equiv.sum_comp e.symm (fun q : Tq => g q.1.out * ∏ᶠ v, φq q.1 v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i))).symm

end GlobalTheory.MixEvAdm

namespace GlobalTheory.MixEvAdm

/- English proof (translation)
Introduce `_ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ _ hP₁ e hE l hl`. Introduce `g hg`. Take `⟨m, c, φ, hφ, hstd, rfl⟩` from `sb_decomp F (Fin n × Fin d) g hg`. Take `⟨ei, ev, -, hev, hloc⟩` from `hE.loc`. Establish `hfam : ∀ j, ∀ᶠ v in Filter.cofinite, φ j v = M.vac v` using `fun j => ((hstd j).and hP.good.std).mono fun v hv => hv.1.trans hv.2.symm`.

Establish `hψSB : ∀ j v, ev v (φ j v) ∈ SB (Fin n₁ × Fin d → Fv F v)` using `fun j v => (hev v).2 ▸ Submodule.mem_map_of_mem (hφ j v)`. Establish `hψstd : ∀ j, ∀ᶠ v in Filter.cofinite, ev v (φ j v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1` using `fun j => ((hfam j).and hP₁.good.std).mono fun v hv => by rw [hv.1, (hev v).1, hv.2]`. Establish `hG : ∀ j, (fun y : Fin n₁ × Fin d → Af F => ∏ᶠ v, ev v (φ j v) fun i => evalV F v (y i)) ∈ SB (Fin n₁ × Fin d → Af F)` using `fun j => ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ (hψSB j) (hψstd j), GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ (hψSB j) (hψstd j)⟩`. Use `choose Tj hTj using fun j => hl _ (hG j)`. Use `⟨∑ j, c j • (Tj j).comp ei, fun f => ?_⟩` and prove the remaining obligations.

Establish `hsplit : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) (∑ j, c j • fun y => ∏ᶠ v, φ j v fun i => evalV F v (y i)) = ∑ j, c j • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j)`. Use function extensionality and compare the values at `x`. Simplify using `only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm]`.

Both sides reduce to the same expression. Rewrite using `[LinearMap.comp_apply, hsplit, map_sum, map_sum]`. Simplify using `only [map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hloc f (φ j) (hφ j) (hfam j)]`.

Conclude with `congrArg (c j • ·) (hTj j (ei f))`.
-/
theorem pullback_adm : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ _ hP₁ e hE l hl
  intro g hg
  obtain ⟨m, c, φ, hφ, hstd, rfl⟩ := sb_decomp F (Fin n × Fin d) g hg
  obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
  have hfam : ∀ j, ∀ᶠ v in Filter.cofinite, φ j v = M.vac v := fun j =>
    ((hstd j).and hP.good.std).mono fun v hv => hv.1.trans hv.2.symm
  have hψSB : ∀ j v, ev v (φ j v) ∈ SB (Fin n₁ × Fin d → Fv F v) := fun j v =>
    (hev v).2 ▸ Submodule.mem_map_of_mem (hφ j v)
  have hψstd : ∀ j, ∀ᶠ v in Filter.cofinite,
      ev v (φ j v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun j =>
    ((hfam j).and hP₁.good.std).mono fun v hv => by rw [hv.1, (hev v).1, hv.2]
  have hG : ∀ j, (fun y : Fin n₁ × Fin d → Af F => ∏ᶠ v, ev v (φ j v) fun i => evalV F v (y i)) ∈
      SB (Fin n₁ × Fin d → Af F) := fun j =>
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ (hψSB j) (hψstd j),
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ (hψSB j) (hψstd j)⟩
  choose Tj hTj using fun j => hl _ (hG j)
  refine ⟨∑ j, c j • (Tj j).comp ei, fun f => ?_⟩
  have hsplit : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
      (∑ j, c j • fun y => ∏ᶠ v, φ j v fun i => evalV F v (y i)) =
      ∑ j, c j • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) := by
    funext x
    simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_left_comm]
    rfl
  rw [LinearMap.comp_apply, hsplit, map_sum, map_sum]
  simp only [map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hloc f (φ j) (hφ j) (hfam j)]
  exact congrArg (c j • ·) (hTj j (ei f))

end GlobalTheory.MixEvAdm
