import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.OrthogonalFreeOfPerfectAltZmod
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.Weights

def eLeft (g n : ℕ) (x : Fin g ⊕ Fin g → ZMod n) : (Fin g ⊕ Fin g → ZMod n) →+ ZMod n :=
  AddMonoidHom.mk' (fun a => eStd g n a x) (by
    intro a b
    simp only [eStd, Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eLeft_apply (g n : ℕ) (x a : Fin g ⊕ Fin g → ZMod n) : eLeft g n x a = eStd g n a x := rfl

/- English proof (translation)
Simplify using `only [eStd, ← Finset.sum_neg_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem eStd_swap (g n : ℕ) (x a : Fin g ⊕ Fin g → ZMod n) : eStd g n a x = -eStd g n x a := by
  simp only [eStd, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Use `AddMonoidHom.functions_ext _ _ _ fun i z => ?_` and prove the remaining obligations. Establish `: (Pi.single i z : Fin d → ZMod n) = z.val • (Pi.single i 1 : Fin d → ZMod n)`. Rewrite using `[← Pi.single_nsmul]`. Simplify using the standard rewrite rules. Rewrite using `[this, map_nsmul, map_nsmul, h]`.
-/
theorem addHom_ext_single {d n : ℕ} [NeZero n] {A : Type*} [AddCommGroup A] (f f' : (Fin d → ZMod n) →+ A)
    (h : ∀ i, f (Pi.single i 1) = f' (Pi.single i 1)) : f = f' := by
  refine AddMonoidHom.functions_ext _ _ _ fun i z => ?_
  have : (Pi.single i z : Fin d → ZMod n) = z.val • (Pi.single i 1 : Fin d → ZMod n) := by
    rw [← Pi.single_nsmul]
    simp
  rw [this, map_nsmul, map_nsmul, h]

/- English proof (translation)
Take `⟨F, hF⟩` from `(GlobalTheory.ZModPerp.baer_zmod n).extension_property (φ.toZModLinearMap n) hφ (Fintype.linearCombination (ZMod n) a)`. Use `⟨Sum.elim (fun i => -F (Pi.single (.inr i) 1)) (fun i => F (Pi.single (.inl i) 1)), fun i => ?_⟩` and prove the remaining obligations. Establish `h1 : F (φ (Pi.single i 1)) = a i`. Use `LinearMap.congr_fun hF (Pi.single i 1)` as an intermediate fact. Simplify using `using this`.

Rewrite using `[← h1, LinearMap.pi_apply_eq_sum_univ F, Fintype.sum_sum_type, eStd, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `e : ∀ k : Fin g ⊕ Fin g, (fun j => if k = j then (1 : ZMod n) else 0) = Pi.single k 1`. Introduce `k`. Use function extensionality and compare the values at `j`.

Simplify using `[Pi.single_apply, eq_comm]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, smul_eq_mul, e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_eStd_eq {g d n : ℕ} [NeZero n]
    (φ : (Fin d → ZMod n) →+ (Fin g ⊕ Fin g → ZMod n)) (hφ : Function.Injective φ)
    (a : Fin d → ZMod n) : ∃ x, ∀ i, eStd g n (φ (Pi.single i 1)) x = a i := by
  obtain ⟨F, hF⟩ := (GlobalTheory.ZModPerp.baer_zmod n).extension_property (φ.toZModLinearMap n) hφ
    (Fintype.linearCombination (ZMod n) a)
  refine ⟨Sum.elim (fun i => -F (Pi.single (.inr i) 1)) (fun i => F (Pi.single (.inl i) 1)),
    fun i => ?_⟩
  have h1 : F (φ (Pi.single i 1)) = a i := by
    have := LinearMap.congr_fun hF (Pi.single i 1)
    simpa using this
  rw [← h1, LinearMap.pi_apply_eq_sum_univ F, Fintype.sum_sum_type, eStd, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : ∀ k : Fin g ⊕ Fin g, (fun j => if k = j then (1 : ZMod n) else 0) = Pi.single k 1 := by
    intro k
    funext j
    simp [Pi.single_apply, eq_comm]
  simp only [Sum.elim_inl, Sum.elim_inr, smul_eq_mul, e]
  ring

/- English proof (translation)
Set `s : Set X` to `Set.range fun v : X => β + N • v`. Establish `: Nonempty s` using `⟨⟨_, 0, rfl⟩⟩`. Take `⟨⟨_, v, rfl⟩, hv⟩` from `Filter.Tendsto.exists_forall_le (f := fun a : s => q a) (hq.comp Subtype.val_injective.tendsto_cofinite)`. Use `⟨v, fun v₀ => ?_⟩` and prove the remaining obligations. Use `hv ⟨_, v + v₀, rfl⟩` as an intermediate fact.

Simplify `this` using `[add_assoc]`.
-/
theorem exists_min {X : Type} [AddCommGroup X] (q : X → ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (N : ℕ) (β : X) :
    ∃ v : X, ∀ v₀ : X, q (β + N • v) ≤ q (β + N • v + N • v₀) := by
  let s : Set X := Set.range fun v : X => β + N • v
  have : Nonempty s := ⟨⟨_, 0, rfl⟩⟩
  obtain ⟨⟨_, v, rfl⟩, hv⟩ := Filter.Tendsto.exists_forall_le (f := fun a : s => q a)
    (hq.comp Subtype.val_injective.tendsto_cofinite)
  refine ⟨v, fun v₀ => ?_⟩
  have := hv ⟨_, v + v₀, rfl⟩
  simpa [add_assoc] using this

end GlobalTheory.ZH.Weights

namespace GlobalTheory.ZH

open Weights

/- English proof (translation)
Introduce `o Ω _ _ _ _ S p _ y₀ τ`. Establish `hN : S.N ≠ 0` using `by have := S.N_ge; omega`. Establish `hr : S.r ≠ 0` using `by have := S.r_pos; omega`. Establish `: NeZero (S.r * S.N)` using `⟨mul_ne_zero hr hN⟩`. Establish `: NeZero S.N` using `⟨hN⟩`.

Establish `hwt : ∀ v : τ.X, τ.wt (S.N • v) = 0` using `fun v => by`. Use extensionality with `t`. Rewrite using `[map_nsmul, AddMonoidHom.nsmul_apply]`. Simplify using the standard rewrite rules. Use `⟨fun c => ?_, fun T hT hle w hw I hI α => ⟨fun h => ?_, fun h t h₂ ht => ?_⟩⟩` and prove the remaining obligations.

Take `⟨-, d, ⟨E⟩⟩` from `τ.isoFree`. Take `⟨x, hx⟩` from `exists_eStd_eq ((S.perp τ.yy.ker).subtype.comp E.symm.toAddMonoidHom) (Subtype.val_injective.comp E.symm.injective) (fun i => ((c (E.symm (Pi.single i 1))).val : ZMod (S.r * S.N)))`. Take `⟨β, hβ⟩` from `QuotientAddGroup.mk_surjective (τ.yy x)`. Take `⟨v, hv⟩` from `exists_min τ.q τ.pos S.N β`. Use `⟨_, hv, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, hwt, add_zero]`. Use `addHom_ext_single ((τ.wt β).comp E.symm.toAddMonoidHom) (c.comp E.symm.toAddMonoidHom) fun i => by` as an intermediate fact. Establish `h1` using `τ.wt_eq x β hβ.symm (E.symm (Pi.single i 1))`. Establish `h2 : eStd S.g _ (E.symm (Pi.single i 1) : S.Gam) x = _` using `hx i`. Rewrite `h1` using `[h2, map_natCast, ZMod.natCast_zmod_val]`.

Conclude with `h1`. Use extensionality with `t`. Simplify using `using DFunLike.congr_fun this (E t)`. Take `⟨-, d, ⟨E⟩⟩` from `hT`. Take `⟨x, hx⟩` from `τ.yy_onto (QuotientAddGroup.mk α)`.

Establish `key : ∀ t : T, ∃ a : ZMod (S.r * S.N), eStd S.g _ (t : S.Gam) x = S.N • a` using `fun t => by`. Establish `h1` using `τ.wt_eq x α hx ⟨t, hle t.2⟩`. Rewrite `h1` using `[h t _ t.2, ZMod.castHom_apply, ZMod.cast_eq_val, eq_comm, ZMod.natCast_eq_zero_iff]`. Take `⟨k, hk⟩` from `h1`. Use `⟨k, ?_⟩` and prove the remaining obligations.

Rewrite using `[← ZMod.natCast_zmod_val (eStd S.g _ (t : S.Gam) x), hk]`. Simplify using the standard rewrite rules. Use `choose a ha using key`. Take `⟨b, hb⟩` from `exists_eStd_eq (T.subtype.comp E.symm.toAddMonoidHom) (Subtype.val_injective.comp E.symm.injective) (fun i => a (E.symm (Pi.single i 1)))`. Establish `h3` using `addHom_ext_single ((eLeft S.g _ x).comp (T.subtype.comp E.symm.toAddMonoidHom)) (S.N • (eLeft S.g _ b).comp (T.subtype.comp E.symm.toAddMonoidHom)) fun i => by`.

Conclude with `(ha _).trans (congrArg (S.N • ·) (hb i).symm)`. Establish `h4 : x - S.N • b ∈ S.perp T` using `fun t ht => by`. Establish `h5 : eStd S.g _ t x = S.N • eStd S.g _ t b`. Simplify `DFunLike.congr_fun h3 (E ⟨t, ht⟩)` using `[eLeft_apply]`. Rewrite using `[← eLeft_apply, map_sub, map_nsmul, eLeft_apply, eLeft_apply, eStd_swap, h5, eStd_swap _ _ t b]`.

Simplify using the standard rewrite rules. Use `set L := AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀) with hL`. Establish `hNL : ∀ v : τ.X, S.N • v ∈ L` using `fun v => AddSubgroup.subset_closure (Or.inr ⟨v, rfl⟩)`. Establish `h6 : S.perp T ≤ (L.map (QuotientAddGroup.mk' _)).comap τ.yy`. Rewrite using `[← hI, AddSubgroup.closure_le]`.

Introduce `i hi`. Conclude with `⟨w i, AddSubgroup.subset_closure (Or.inl ⟨i, hi, rfl⟩), (hw i).symm⟩`. Take `⟨l, hl, hl'⟩` from `h6 h4`. Rewrite `hl'` using `[map_sub, map_nsmul, hx, hw, QuotientAddGroup.mk'_apply, ← QuotientAddGroup.mk_nsmul, ← QuotientAddGroup.mk_sub, QuotientAddGroup.eq]`. Take `⟨u, hu⟩` from `hl'`.

Establish `h7 : α = l + S.N • w b + S.N • (S.r • u)`. Rewrite using `[← mul_nsmul, show (S.r * S.N) • u = _ from hu]`. Normalize the expressions using the abelian group laws. Rewrite using `[h7]`. Conclude with `L.add_mem (L.add_mem hl (hNL _)) (hNL _)`.

Proceed by induction on `h using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Break down `hx with ⟨i, hi, rfl⟩ | ⟨v, rfl⟩` into its components or cases. Establish `hi' : i ∈ S.perp T` using `hI ▸ AddSubgroup.subset_closure hi`. Rewrite using `[τ.wt_eq i _ (hw i), eStd_swap, hi' t ht]`.

Simplify using the standard rewrite rules. Rewrite using `[hwt]`. Both sides reduce to the same expression. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, AddMonoidHom.add_apply, hx, hy, add_zero]`.

Consider the case `neg x _ hx => rw [map_neg, AddMonoidHom.neg_apply, hx, neg_zero]`.
-/
theorem test_weights : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω), (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) := by
  intro o Ω _ _ _ _ S p _ y₀ τ
  have hN : S.N ≠ 0 := by have := S.N_ge; omega
  have hr : S.r ≠ 0 := by have := S.r_pos; omega
  have : NeZero (S.r * S.N) := ⟨mul_ne_zero hr hN⟩
  have : NeZero S.N := ⟨hN⟩
  have hwt : ∀ v : τ.X, τ.wt (S.N • v) = 0 := fun v => by
    ext t
    rw [map_nsmul, AddMonoidHom.nsmul_apply]
    simp
  refine ⟨fun c => ?_, fun T hT hle w hw I hI α => ⟨fun h => ?_, fun h t h₂ ht => ?_⟩⟩
  · obtain ⟨-, d, ⟨E⟩⟩ := τ.isoFree
    obtain ⟨x, hx⟩ := exists_eStd_eq ((S.perp τ.yy.ker).subtype.comp E.symm.toAddMonoidHom)
      (Subtype.val_injective.comp E.symm.injective)
      (fun i => ((c (E.symm (Pi.single i 1))).val : ZMod (S.r * S.N)))
    obtain ⟨β, hβ⟩ := QuotientAddGroup.mk_surjective (τ.yy x)
    obtain ⟨v, hv⟩ := exists_min τ.q τ.pos S.N β
    refine ⟨_, hv, ?_⟩
    rw [map_add, hwt, add_zero]
    have := addHom_ext_single ((τ.wt β).comp E.symm.toAddMonoidHom) (c.comp E.symm.toAddMonoidHom) fun i => by
      have h1 := τ.wt_eq x β hβ.symm (E.symm (Pi.single i 1))
      have h2 : eStd S.g _ (E.symm (Pi.single i 1) : S.Gam) x = _ := hx i
      rw [h2, map_natCast, ZMod.natCast_zmod_val] at h1
      exact h1
    ext t
    simpa using DFunLike.congr_fun this (E t)
  · obtain ⟨-, d, ⟨E⟩⟩ := hT
    obtain ⟨x, hx⟩ := τ.yy_onto (QuotientAddGroup.mk α)
    have key : ∀ t : T, ∃ a : ZMod (S.r * S.N), eStd S.g _ (t : S.Gam) x = S.N • a := fun t => by
      have h1 := τ.wt_eq x α hx ⟨t, hle t.2⟩
      rw [h t _ t.2, ZMod.castHom_apply, ZMod.cast_eq_val, eq_comm,
        ZMod.natCast_eq_zero_iff] at h1
      obtain ⟨k, hk⟩ := h1
      refine ⟨k, ?_⟩
      rw [← ZMod.natCast_zmod_val (eStd S.g _ (t : S.Gam) x), hk]
      simp
    choose a ha using key
    obtain ⟨b, hb⟩ := exists_eStd_eq (T.subtype.comp E.symm.toAddMonoidHom)
      (Subtype.val_injective.comp E.symm.injective) (fun i => a (E.symm (Pi.single i 1)))
    have h3 := addHom_ext_single ((eLeft S.g _ x).comp (T.subtype.comp E.symm.toAddMonoidHom))
      (S.N • (eLeft S.g _ b).comp (T.subtype.comp E.symm.toAddMonoidHom)) fun i => by
        exact (ha _).trans (congrArg (S.N • ·) (hb i).symm)
    have h4 : x - S.N • b ∈ S.perp T := fun t ht => by
      have h5 : eStd S.g _ t x = S.N • eStd S.g _ t b := by
        simpa [eLeft_apply] using DFunLike.congr_fun h3 (E ⟨t, ht⟩)
      rw [← eLeft_apply, map_sub, map_nsmul, eLeft_apply, eLeft_apply, eStd_swap, h5,
        eStd_swap _ _ t b]
      simp
    set L := AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀) with hL
    have hNL : ∀ v : τ.X, S.N • v ∈ L := fun v => AddSubgroup.subset_closure (Or.inr ⟨v, rfl⟩)
    have h6 : S.perp T ≤ (L.map (QuotientAddGroup.mk' _)).comap τ.yy := by
      rw [← hI, AddSubgroup.closure_le]
      intro i hi
      exact ⟨w i, AddSubgroup.subset_closure (Or.inl ⟨i, hi, rfl⟩), (hw i).symm⟩
    obtain ⟨l, hl, hl'⟩ := h6 h4
    rw [map_sub, map_nsmul, hx, hw, QuotientAddGroup.mk'_apply, ← QuotientAddGroup.mk_nsmul,
      ← QuotientAddGroup.mk_sub, QuotientAddGroup.eq] at hl'
    obtain ⟨u, hu⟩ := hl'
    have h7 : α = l + S.N • w b + S.N • (S.r • u) := by
      rw [← mul_nsmul, show (S.r * S.N) • u = _ from hu]
      abel
    rw [h7]
    exact L.add_mem (L.add_mem hl (hNL _)) (hNL _)
  · induction h using AddSubgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨i, hi, rfl⟩ | ⟨v, rfl⟩
      · have hi' : i ∈ S.perp T := hI ▸ AddSubgroup.subset_closure hi
        rw [τ.wt_eq i _ (hw i), eStd_swap, hi' t ht]
        simp
      · rw [hwt]
        rfl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, AddMonoidHom.add_apply, hx, hy, add_zero]
    | neg x _ hx => rw [map_neg, AddMonoidHom.neg_apply, hx, neg_zero]

end GlobalTheory.ZH
