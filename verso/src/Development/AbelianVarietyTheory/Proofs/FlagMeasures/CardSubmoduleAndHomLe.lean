import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.SubmoduleCount

section Abstract

variable {R : Type*} [CommRing R] {D : Type*} [AddCommGroup D] [Module R D]

end Abstract

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {R : Type*} [CommRing R] {D : Type*} [AddCommGroup D] [Module R D] in
/- English proof (translation)
Introduce `g`. Proceed by induction on `g with`. Consider the case `zero`. Introduce `M _ _ x hx N`. Use `⟨Fin.elim0, ?_⟩` and prove the remaining obligations.

Establish `hbot : (⊤ : Submodule R M) = ⊥`. Rewrite using `[← hx, Set.range_eq_empty, Submodule.span_empty]`. Rewrite using `[Set.range_eq_empty, Submodule.span_empty, eq_bot_iff, ← hbot]`. Conclude with `le_top`. Consider the case `succ g ih`.

Introduce `M _ _ x hx N`. Use `set P := Submodule.span R (Set.range (fun i : Fin g => x i.succ)) with hPdef`. Set `x' : Fin g → P` to `fun i => ⟨x i.succ, Submodule.subset_span ⟨i, rfl⟩⟩`. Establish `hx' : Submodule.span R (Set.range x') = ⊤`. Apply `Submodule.map_injective_of_injective (f := P.subtype) Subtype.val_injective` to reduce the goal to its premises.

Rewrite using `[Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]`. Both sides reduce to the same expression. Take `⟨w, hw⟩` from `ih P x' hx' (N.comap P.subtype)`. Use `set I : Ideal R := (N ⊔ P).comap (LinearMap.toSpanSingleton R M (x 0)) with hIdef`. Use `set a := Submodule.IsPrincipal.generator I`.

Establish `ha : a ∈ I` using `Submodule.IsPrincipal.generator_mem I`. Rewrite `ha` using `[hIdef, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Submodule.mem_sup]`. Take `⟨n, hn, p, hp, hnp⟩` from `ha`. Use `⟨Fin.cons n (fun i => (w i : M)), le_antisymm ?_ ?_⟩` and prove the remaining obligations. Introduce `m hm`.

Establish `hmtop : m ∈ Submodule.span R (Set.range x)` using `hx ▸ Submodule.mem_top`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun R).1 hmtop`. Rewrite `hm`, the goal using `[Fin.sum_univ_succ]`. Use `set q := ∑ i : Fin g, c i.succ • x i.succ with hqdef`. Establish `hq : q ∈ P` using `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Establish `hc0 : c 0 ∈ I`. Rewrite using `[hIdef, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]`. Use `sub_mem (Submodule.mem_sup_left hm : _ ∈ N ⊔ P) (Submodule.mem_sup_right hq : _ ∈ N ⊔ P)` as an intermediate fact. Simplify using `using this`. Rewrite `hc0` using `[← Submodule.IsPrincipal.span_singleton_generator I, Submodule.mem_span_singleton]`.

Take `⟨t, ht⟩` from `hc0`. Establish `hdiff : c 0 • x 0 + q - t • n = q + t • p`. Rewrite using `[← ht, smul_assoc, ← hnp, smul_add]`. Normalize the expressions using the abelian group laws. Establish `hdP : c 0 • x 0 + q - t • n ∈ P`.

Rewrite using `[hdiff]`. Conclude with `add_mem hq (Submodule.smul_mem _ _ hp)`. Establish `hdN : c 0 • x 0 + q - t • n ∈ N` using `sub_mem hm (Submodule.smul_mem _ _ hn)`. Establish `hmem : (⟨_, hdP⟩ : P) ∈ Submodule.span R (Set.range w)` using `hw ▸ hdN`. Establish `hle : Submodule.span R (Set.range w) ≤ (Submodule.span R (Set.range (Fin.cons n (fun i => (w i : M)) : Fin (g + 1) → M))).comap P.subtype`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `Submodule.subset_span ⟨i.succ, by simp⟩`. Establish `h1` using `hle hmem`. Rewrite `h1` using `[Submodule.mem_comap, Submodule.coe_subtype]`.

Establish `h2 : t • n ∈ Submodule.span R (Set.range (Fin.cons n (fun i => (w i : M)) : Fin (g + 1) → M))` using `Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp⟩)`. Simplify using `using add_mem h1 h2`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations.

Simplify using `using hn`. Establish `: w i ∈ N.comap P.subtype` using `hw ▸ Submodule.subset_span ⟨i, rfl⟩`. Simplify using `using this`.
-/
private theorem exists_finite_generators_of_isPrincipalIdealRing [IsPrincipalIdealRing R] :
    ∀ (g : ℕ) (M : Type) [AddCommGroup M] [Module R M] (x : Fin g → M),
      Submodule.span R (Set.range x) = ⊤ →
        ∀ N : Submodule R M, ∃ v : Fin g → M, N = Submodule.span R (Set.range v) := by
  intro g
  induction g with
  | zero =>
    intro M _ _ x hx N
    refine ⟨Fin.elim0, ?_⟩
    have hbot : (⊤ : Submodule R M) = ⊥ := by
      rw [← hx, Set.range_eq_empty, Submodule.span_empty]
    rw [Set.range_eq_empty, Submodule.span_empty, eq_bot_iff, ← hbot]
    exact le_top
  | succ g ih =>
    intro M _ _ x hx N
    set P := Submodule.span R (Set.range (fun i : Fin g => x i.succ)) with hPdef
    let x' : Fin g → P := fun i => ⟨x i.succ, Submodule.subset_span ⟨i, rfl⟩⟩
    have hx' : Submodule.span R (Set.range x') = ⊤ := by
      apply Submodule.map_injective_of_injective (f := P.subtype) Subtype.val_injective
      rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
      rfl
    obtain ⟨w, hw⟩ := ih P x' hx' (N.comap P.subtype)
    set I : Ideal R := (N ⊔ P).comap (LinearMap.toSpanSingleton R M (x 0)) with hIdef
    set a := Submodule.IsPrincipal.generator I
    have ha : a ∈ I := Submodule.IsPrincipal.generator_mem I
    rw [hIdef, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Submodule.mem_sup] at ha
    obtain ⟨n, hn, p, hp, hnp⟩ := ha
    refine ⟨Fin.cons n (fun i => (w i : M)), le_antisymm ?_ ?_⟩
    · intro m hm
      have hmtop : m ∈ Submodule.span R (Set.range x) := hx ▸ Submodule.mem_top
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hmtop
      rw [Fin.sum_univ_succ] at hm ⊢
      set q := ∑ i : Fin g, c i.succ • x i.succ with hqdef
      have hq : q ∈ P := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      have hc0 : c 0 ∈ I := by
        rw [hIdef, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
        have := sub_mem (Submodule.mem_sup_left hm : _ ∈ N ⊔ P) (Submodule.mem_sup_right hq : _ ∈ N ⊔ P)
        simpa using this
      rw [← Submodule.IsPrincipal.span_singleton_generator I, Submodule.mem_span_singleton] at hc0
      obtain ⟨t, ht⟩ := hc0
      have hdiff : c 0 • x 0 + q - t • n = q + t • p := by
        rw [← ht, smul_assoc, ← hnp, smul_add]; abel
      have hdP : c 0 • x 0 + q - t • n ∈ P := by
        rw [hdiff]; exact add_mem hq (Submodule.smul_mem _ _ hp)
      have hdN : c 0 • x 0 + q - t • n ∈ N := sub_mem hm (Submodule.smul_mem _ _ hn)
      have hmem : (⟨_, hdP⟩ : P) ∈ Submodule.span R (Set.range w) := hw ▸ hdN
      have hle : Submodule.span R (Set.range w) ≤ (Submodule.span R (Set.range (Fin.cons n (fun i => (w i : M)) : Fin (g + 1) → M))).comap P.subtype := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨i.succ, by simp⟩
      have h1 := hle hmem
      rw [Submodule.mem_comap, Submodule.coe_subtype] at h1
      have h2 : t • n ∈ Submodule.span R (Set.range (Fin.cons n (fun i => (w i : M)) : Fin (g + 1) → M)) :=
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp⟩)
      simpa using add_mem h1 h2
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hn
      · have : w i ∈ N.comap P.subtype := hw ▸ Submodule.subset_span ⟨i, rfl⟩
        simpa using this

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L D _ _ _ g x hx`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible (ValuativeRel.valuation F).integer`. Use `haveI : IsPrincipalIdealRing L.O := (_root_.GlobalTheory.UnramOrder.order_facts L ϖ hϖ).2.2.2.1`. Use `⟨?_, fun D' _ _ _ => ?_⟩` and prove the remaining obligations. Establish `hsurj : Function.Surjective (fun v : Fin g → D => Submodule.span L.O (Set.range v))`.

Introduce `N`. Take `⟨v, hv⟩` from `exists_finite_generators_of_isPrincipalIdealRing g D x hx N`. Conclude with `⟨v, hv.symm⟩`. Combine the equalities or inequalities in the displayed calculation. Establish `hinj : Function.Injective (fun f : D →ₗ[L.O] D' => fun i => f (x i))`.

Introduce `f f' h`. Conclude with `LinearMap.ext_on_range hx (fun i => congrFun h i)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem _root_.GlobalTheory.SubmoduleCount.card_submodule_and_hom_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (D : Type) [AddCommGroup D] [Module L.O D] [Finite D] (g : ℕ) (x : Fin g → D), Submodule.span L.O (Set.range x) = ⊤ → Nat.card (Submodule L.O D) ≤ Nat.card D ^ g ∧ ∀ (D' : Type) [AddCommGroup D'] [Module L.O D'] [Finite D'], Nat.card (D →ₗ[L.O] D') ≤ Nat.card D' ^ g := by
  intro F _ _ _ _ _ E _ _ _ L D _ _ _ g x hx
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (ValuativeRel.valuation F).integer
  haveI : IsPrincipalIdealRing L.O := (_root_.GlobalTheory.UnramOrder.order_facts L ϖ hϖ).2.2.2.1
  refine ⟨?_, fun D' _ _ _ => ?_⟩
  · have hsurj : Function.Surjective (fun v : Fin g → D => Submodule.span L.O (Set.range v)) := by
      intro N
      obtain ⟨v, hv⟩ := exists_finite_generators_of_isPrincipalIdealRing g D x hx N
      exact ⟨v, hv.symm⟩
    calc Nat.card (Submodule L.O D) ≤ Nat.card (Fin g → D) := Nat.card_le_card_of_surjective _ hsurj
      _ = Nat.card D ^ g := by simp [Nat.card_fun]
  · have hinj : Function.Injective (fun f : D →ₗ[L.O] D' => fun i => f (x i)) := by
      intro f f' h
      exact LinearMap.ext_on_range hx (fun i => congrFun h i)
    calc Nat.card (D →ₗ[L.O] D') ≤ Nat.card (Fin g → D') := Nat.card_le_card_of_injective _ hinj
      _ = Nat.card D' ^ g := by simp [Nat.card_fun]

end GlobalTheory.SubmoduleCount
