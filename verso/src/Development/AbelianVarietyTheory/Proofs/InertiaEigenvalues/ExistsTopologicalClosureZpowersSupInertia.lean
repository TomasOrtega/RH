import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgEquivRootOfUnityEqPow

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.FrobGen
open GlobalTheory.MemLoc GlobalTheory.MemLoc.FrobLaws

/- English proof (translation)
Set `π : G →* G ⧸ J` to `QuotientGroup.mk' J`. Set `S : AddSubgroup ℤ` to `{ carrier := {n | π g ^ n ∈ U.map π} add_mem' := fun {a b} ha hb => by show π g ^ (a + b) ∈ U.map π`. Rewrite using `[zpow_add]`. Conclude with `mul_mem ha hb`. Use the proof step `zero_mem' := by show π g ^ (0 : ℤ) ∈ U.map π`.

Rewrite using `[zpow_zero]`. Conclude with `one_mem _`. Use the proof step `neg_mem' := fun {a} ha => by show π g ^ (-a) ∈ U.map π`. Rewrite using `[zpow_neg]`. Conclude with `inv_mem ha }`.

Take `⟨f, hf⟩` from `Int.subgroup_cyclic S`. Establish `hfS : f ∈ S` using `by rw [hf]; exact AddSubgroup.subset_closure rfl`. Take `⟨φ, hφU, hφ⟩ : π g ^ f ∈ U.map π` from `hfS`. Use `⟨⟨φ, hφU⟩, ?_⟩` and prove the remaining obligations. Establish `hd : Dense ((Subgroup.zpowers g ⊔ J : Subgroup G) : Set G)`.

Rewrite using `[dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, hg, Subgroup.coe_top]`. Establish `hd2` using `hd.preimage (f := (Subtype.val : U → G)) hU.isOpenMap_subtype_val`. Apply `SetLike.coe_injective` to reduce the goal to its premises. Rewrite using `[Subgroup.topologicalClosure_coe, Subgroup.coe_top, ← dense_iff_closure_eq]`. Use `hd2.mono fun y hy => ?_` and prove the remaining obligations.

Establish `h1 : π y ∈ (Subgroup.zpowers g ⊔ J).map π` using `⟨y, hy, rfl⟩`. Establish `h2 : J.map π = ⊥`. Rewrite using `[Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']`. Rewrite `h1` using `[Subgroup.map_sup, h2, sup_bot_eq, MonoidHom.map_zpowers]`. Take `⟨n, hn⟩` from `Subgroup.mem_zpowers_iff.1 h1`.

Establish `hnS : n ∈ S` using `by show π g ^ n ∈ U.map π`. Rewrite using `[hn]`. Conclude with `⟨y, y.2, rfl⟩`. Rewrite `hnS` using `[hf, AddSubgroup.mem_closure_singleton]`. Take `⟨k, rfl⟩` from `hnS`.

Establish `h3 : π ((φ ^ k)⁻¹ * y) = 1`. Rewrite using `[map_mul, map_inv, map_zpow, hφ, ← hn, ← zpow_mul, smul_eq_mul, mul_comm f k, inv_mul_cancel]`. Establish `h4 : (φ ^ k)⁻¹ * (y : G) ∈ J`. Rewrite using `[← QuotientGroup.ker_mk' J]`. Conclude with `h3`.

Establish `h5 : y = (⟨φ, hφU⟩ : U) ^ k * ((((⟨φ, hφU⟩ : U) ^ k))⁻¹ * y)`. Rewrite using `[mul_inv_cancel_left]`. Rewrite using `[SetLike.mem_coe, h5]`. Use `Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers _ _) ?_` and prove the remaining obligations. Rewrite using `[Subgroup.mem_subgroupOf]`.

Simplify using `using h4`.
-/
theorem exists_gen_of_isOpen {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (J : Subgroup G) [J.Normal] (g : G) (U : Subgroup G) (hU : IsOpen (U : Set G))
    (hg : (Subgroup.zpowers g ⊔ J).topologicalClosure = ⊤) :
    ∃ φ : U, (Subgroup.zpowers φ ⊔ J.subgroupOf U).topologicalClosure = ⊤ := by
  let π : G →* G ⧸ J := QuotientGroup.mk' J
  let S : AddSubgroup ℤ :=
    { carrier := {n | π g ^ n ∈ U.map π}
      add_mem' := fun {a b} ha hb => by
        show π g ^ (a + b) ∈ U.map π
        rw [zpow_add]; exact mul_mem ha hb
      zero_mem' := by
        show π g ^ (0 : ℤ) ∈ U.map π
        rw [zpow_zero]; exact one_mem _
      neg_mem' := fun {a} ha => by
        show π g ^ (-a) ∈ U.map π
        rw [zpow_neg]; exact inv_mem ha }
  obtain ⟨f, hf⟩ := Int.subgroup_cyclic S
  have hfS : f ∈ S := by rw [hf]; exact AddSubgroup.subset_closure rfl
  obtain ⟨φ, hφU, hφ⟩ : π g ^ f ∈ U.map π := hfS
  refine ⟨⟨φ, hφU⟩, ?_⟩
  have hd : Dense ((Subgroup.zpowers g ⊔ J : Subgroup G) : Set G) := by
    rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, hg, Subgroup.coe_top]
  have hd2 := hd.preimage (f := (Subtype.val : U → G)) hU.isOpenMap_subtype_val
  apply SetLike.coe_injective
  rw [Subgroup.topologicalClosure_coe, Subgroup.coe_top, ← dense_iff_closure_eq]
  refine hd2.mono fun y hy => ?_
  have h1 : π y ∈ (Subgroup.zpowers g ⊔ J).map π := ⟨y, hy, rfl⟩
  have h2 : J.map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  rw [Subgroup.map_sup, h2, sup_bot_eq, MonoidHom.map_zpowers] at h1
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h1
  have hnS : n ∈ S := by
    show π g ^ n ∈ U.map π
    rw [hn]; exact ⟨y, y.2, rfl⟩
  rw [hf, AddSubgroup.mem_closure_singleton] at hnS
  obtain ⟨k, rfl⟩ := hnS
  have h3 : π ((φ ^ k)⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, map_zpow, hφ, ← hn, ← zpow_mul, smul_eq_mul, mul_comm f k, inv_mul_cancel]
  have h4 : (φ ^ k)⁻¹ * (y : G) ∈ J := by
    rw [← QuotientGroup.ker_mk' J]; exact h3
  have h5 : y = (⟨φ, hφU⟩ : U) ^ k * ((((⟨φ, hφU⟩ : U) ^ k))⁻¹ * y) := by
    rw [mul_inv_cancel_left]
  rw [SetLike.mem_coe, h5]
  refine Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers _ _) ?_
  rw [Subgroup.mem_subgroupOf]
  simpa using h4

variable {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
The claim follows from `IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, h⟩`.
-/
theorem root_mem_Kur {ζ : Om l} {m : ℕ} (hm : 0 < m) (hlm : ¬ l ∣ m) (h : ζ ^ m = 1) :
    ζ ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, h⟩

/- English proof (translation)
Use `⟨fun σ hσ h => ?_⟩` and prove the remaining obligations. Rewrite `hσ`, the goal using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Take `⟨m, hm, hlm, H⟩` from `exists_level hx`. Use `H _ 1 fun ζ hζ => ?_` and prove the remaining obligations.

Rewrite using `[AlgEquiv.mul_apply, AlgEquiv.mul_apply, hσ _ (root_mem_Kur hm hlm (by rw [← map_pow, hζ, map_one])), ← AlgEquiv.mul_apply, mul_inv_cancel]`.
-/
theorem normal_fix : (MaximalUnramifiedExtension l).fixingSubgroup.Normal := by
  refine ⟨fun σ hσ h => ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  intro x hx
  obtain ⟨m, hm, hlm, H⟩ := exists_level hx
  refine H _ 1 fun ζ hζ => ?_
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply,
    hσ _ (root_mem_Kur hm hlm (by rw [← map_pow, hζ, map_one])), ← AlgEquiv.mul_apply,
    mul_inv_cancel]

/- English proof (translation)
Rewrite `hσ` using `[IntermediateField.mem_fixingSubgroup_iff]`. Establish `key : ∀ y : Om l, ‖y‖ < 1 → ‖σ y - y‖ < 1` using `fun y hy => by`. Rewrite using `[sub_eq_add_neg]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_gal]`.

Conclude with `hy`. Rewrite using `[norm_neg]`. Conclude with `hy`. Break down `hx.lt_or_eq with h | h` into its components or cases. Conclude with `key x h`.

Take `⟨ζ, m, hm, hlm, hζ, hn⟩` from `FrobLaws.exists_root (l := l) x h`. Use `key _ hn` as an intermediate fact. Rewrite `this` using `[map_sub, hσ ζ (root_mem_Kur hm hlm hζ)]`. Simplify using `using this`.
-/
theorem norm_sub_lt {σ : GQ l} (hσ : σ ∈ (MaximalUnramifiedExtension l).fixingSubgroup) (x : Om l) (hx : ‖x‖ ≤ 1) :
    ‖σ x - x‖ < 1 := by
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
  have key : ∀ y : Om l, ‖y‖ < 1 → ‖σ y - y‖ < 1 := fun y hy => by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_gal]; exact hy
    · rw [norm_neg]; exact hy
  rcases hx.lt_or_eq with h | h
  · exact key x h
  · obtain ⟨ζ, m, hm, hlm, hζ, hn⟩ := FrobLaws.exists_root (l := l) x h
    have := key _ hn
    rw [map_sub, hσ ζ (root_mem_Kur hm hlm hζ)] at this
    simpa using this

/- English proof (translation)
Take `⟨σ, hσ⟩` from `exists_frobenius_Kur l`. Take `⟨g, hg⟩` from `exists_ext σ`. Use `⟨g, ?_⟩` and prove the remaining obligations. Set `H : ClosedSubgroup (GQ l)` to `⟨(Subgroup.zpowers g ⊔ (MaximalUnramifiedExtension l).fixingSubgroup).topologicalClosure, Subgroup.isClosed_topologicalClosure _⟩`. Establish `h1` using `InfiniteGalois.fixingSubgroup_fixedField H`.

Establish `h2 : IntermediateField.fixedField (H : Subgroup (GQ l)) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Rewrite `hx` using `[IntermediateField.mem_fixedField_iff]`. Establish `hK : x ∈ MaximalUnramifiedExtension l`.

Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l), IntermediateField.mem_fixedField_iff]`. Conclude with `fun f hf => hx f (Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right hf))`. Establish `hgx : g x = x` using `hx g (Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers g)))`. Take `⟨c, hc⟩` from `(frob_laws l σ hσ).2.2 ⟨x, hK⟩ (Subtype.ext (by rw [← hg]; exact hgx))`. Rewrite using `[IntermediateField.mem_bot]`.

Conclude with `⟨c, congrArg Subtype.val hc⟩`. Rewrite `h1` using `[h2, IntermediateField.fixingSubgroup_bot]`. Conclude with `h1.symm`.
-/
theorem exists_gen_top :
    ∃ g : GQ l, (Subgroup.zpowers g ⊔ (MaximalUnramifiedExtension l).fixingSubgroup).topologicalClosure = ⊤ := by
  obtain ⟨σ, hσ⟩ := exists_frobenius_Kur l
  obtain ⟨g, hg⟩ := exists_ext σ
  refine ⟨g, ?_⟩
  let H : ClosedSubgroup (GQ l) :=
    ⟨(Subgroup.zpowers g ⊔ (MaximalUnramifiedExtension l).fixingSubgroup).topologicalClosure,
      Subgroup.isClosed_topologicalClosure _⟩
  have h1 := InfiniteGalois.fixingSubgroup_fixedField H
  have h2 : IntermediateField.fixedField (H : Subgroup (GQ l)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hK : x ∈ MaximalUnramifiedExtension l := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l), IntermediateField.mem_fixedField_iff]
      exact fun f hf => hx f (Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right hf))
    have hgx : g x = x := hx g (Subgroup.le_topologicalClosure _
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers g)))
    obtain ⟨c, hc⟩ := (frob_laws l σ hσ).2.2 ⟨x, hK⟩ (Subtype.ext (by rw [← hg]; exact hgx))
    rw [IntermediateField.mem_bot]
    exact ⟨c, congrArg Subtype.val hc⟩
  rw [h2, IntermediateField.fixingSubgroup_bot] at h1
  exact h1.symm

end GlobalTheory.FrobGen

/- English proof (translation)
Take `⟨g, hg⟩` from `GlobalTheory.FrobGen.exists_gen_top (l := l)`. Use `haveI := GlobalTheory.FrobGen.normal_fix (l := l)`. Use `haveI := K.2`. Take `⟨φ, hφ⟩` from `GlobalTheory.FrobGen.exists_gen_of_isOpen _ g (GK K) K.1.fixingSubgroup_isOpen hg`. Use `⟨φ, eq_top_iff.2 (hφ ▸ ?_)⟩` and prove the remaining obligations.

Use `Subgroup.topologicalClosure_minimal _ ?_ (Subgroup.isClosed_topologicalClosure _)` and prove the remaining obligations. Use `le_trans (sup_le_sup_left (fun σ hσ => ?_) _) (Subgroup.le_topologicalClosure _)` and prove the remaining obligations. Conclude with `Subgroup.subset_closure fun x hx => GlobalTheory.FrobGen.norm_sub_lt hσ x hx`.
-/
theorem GlobalTheory.exists_topologicalClosure_zpowers_sup_inertia (l : ℕ) [Fact l.Prime] (K : FinExt l) :
    ∃ φ : ↥(GK K), (Subgroup.zpowers φ ⊔ IK K).topologicalClosure = ⊤ := by
  obtain ⟨g, hg⟩ := GlobalTheory.FrobGen.exists_gen_top (l := l)
  haveI := GlobalTheory.FrobGen.normal_fix (l := l)
  haveI := K.2
  obtain ⟨φ, hφ⟩ := GlobalTheory.FrobGen.exists_gen_of_isOpen _ g (GK K) K.1.fixingSubgroup_isOpen hg
  refine ⟨φ, eq_top_iff.2 (hφ ▸ ?_)⟩
  refine Subgroup.topologicalClosure_minimal _ ?_ (Subgroup.isClosed_topologicalClosure _)
  refine le_trans (sup_le_sup_left (fun σ hσ => ?_) _) (Subgroup.le_topologicalClosure _)
  exact Subgroup.subset_closure fun x hx => GlobalTheory.FrobGen.norm_sub_lt hσ x hx
