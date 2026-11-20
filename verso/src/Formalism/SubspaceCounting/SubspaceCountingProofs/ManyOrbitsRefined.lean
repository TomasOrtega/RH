import Formalism.SubspaceCounting.GoodOrbitIntervalTileCondition
import Formalism.SubspaceCounting.SubspaceCountingProofs.ManyOrbits

noncomputable section

open scoped BigOperators

namespace Formalism.G0

namespace CyclicSpanLengthLemmas

open ManyOrbitsP

/- English proof (translation)
The claim follows from `Module.length_eq_add_of_exact W.subtype W.mkQ Subtype.val_injective W.mkQ_surjective (LinearMap.exact_subtype_mkQ W)`.
-/
private theorem length_eq_length_add_length_quot {R Z : Type} [CommRing R] [AddCommGroup Z] [Module R Z]
    (W : Submodule R Z) : Module.length R Z = Module.length R W + Module.length R (Z ⧸ W) :=
  Module.length_eq_add_of_exact W.subtype W.mkQ Subtype.val_injective W.mkQ_surjective
    (LinearMap.exact_subtype_mkQ W)

/- English proof (translation)
Establish `hm : IsLocalRing.maximalIdeal R ≤ LinearMap.ker (LinearMap.toSpanSingleton R Q x)`. Rewrite using `[(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]`. Conclude with `h0`. Establish `hsurj : Function.Surjective ((IsLocalRing.maximalIdeal R).liftQ (LinearMap.toSpanSingleton R Q x) hm)`. Rewrite using `[← LinearMap.range_eq_top, Submodule.range_liftQ, ← LinearMap.span_singleton_eq_range, hx]`.

Establish `hs : IsSimpleModule R (R ⧸ IsLocalRing.maximalIdeal R)` using `isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal R).out`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem length_le_one_of_cyclic_smul_eq_zero {R Q : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup Q] [Module R Q] (π : R) (hπ : Irreducible π) (x : Q)
    (hx : Submodule.span R {x} = ⊤) (h0 : π • x = 0) : Module.length R Q ≤ 1 := by
  have hm : IsLocalRing.maximalIdeal R ≤ LinearMap.ker (LinearMap.toSpanSingleton R Q x) := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
      Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    exact h0
  have hsurj : Function.Surjective
      ((IsLocalRing.maximalIdeal R).liftQ (LinearMap.toSpanSingleton R Q x) hm) := by
    rw [← LinearMap.range_eq_top, Submodule.range_liftQ, ← LinearMap.span_singleton_eq_range, hx]
  have hs : IsSimpleModule R (R ⧸ IsLocalRing.maximalIdeal R) :=
    isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal R).out
  calc Module.length R Q ≤ Module.length R (R ⧸ IsLocalRing.maximalIdeal R) :=
        Module.length_le_of_surjective _ hsurj
    _ = 1 := Module.length_eq_one_iff.mpr hs

/- English proof (translation)
Establish `e : (Set.range fun i => F (g i)) = F '' Set.range g`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[e, ← Submodule.map_span, hg, Submodule.map_top, LinearMap.range_eq_top.mpr hF]`.
-/
private theorem span_range_map_eq_univ_of_surjective {R A B : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] {n : ℕ} (F : A →ₗ[R] B) (hF : Function.Surjective F)
    (g : Fin n → A) (hg : Submodule.span R (Set.range g) = ⊤) :
    Submodule.span R (Set.range (fun i => F (g i))) = ⊤ := by
  have e : (Set.range fun i => F (g i)) = F '' Set.range g := by
    rw [← Set.range_comp]
    rfl
  rw [e, ← Submodule.map_span, hg, Submodule.map_top, LinearMap.range_eq_top.mpr hF]

/- English proof (translation)
Apply `Submodule.map_injective_of_injective (f := (Submodule.span R {y}).subtype) Subtype.val_injective` to reduce the goal to its premises. Rewrite using `[Submodule.map_span, Set.image_singleton, Submodule.map_subtype_top]`. Both sides reduce to the same expression.
-/
private theorem span_singleton_self_subtype_eq_univ {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] (y : Q) :
    Submodule.span R {(⟨y, Submodule.mem_span_singleton_self y⟩ : Submodule.span R {y})} = ⊤ := by
  apply Submodule.map_injective_of_injective (f := (Submodule.span R {y}).subtype)
    Subtype.val_injective
  rw [Submodule.map_span, Set.image_singleton, Submodule.map_subtype_top]
  rfl

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `Q _ _ x hx h0`. Rewrite `h0` using `[pow_zero, one_smul]`. Substitute `h0` using the available equality.

Rewrite `hx` using `[Submodule.span_singleton_eq_bot.mpr rfl]`. Establish `h0 : ∀ z : Q, z = 0`. Introduce `z`. Establish `hz : z ∈ (⊥ : Submodule R Q)`. Rewrite using `[hx]`.

Conclude with `Submodule.mem_top`. Conclude with `(Submodule.mem_bot R).mp hz`. Establish `: Subsingleton Q` using `⟨fun a b => (h0 a).trans (h0 b).symm⟩`. Rewrite using `[Module.length_eq_zero_iff.mpr this]`. Simplify using the standard rewrite rules.

Consider the case `succ k ih`. Introduce `Q _ _ x hx h0`. Establish `hW : Module.length R (Submodule.span R {π • x}) ≤ k`. Use `ih (Submodule.span R {π • x}) ⟨π • x, Submodule.mem_span_singleton_self _⟩ (span_singleton_self_subtype_eq_univ _) ?_` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show π ^ k • π • x = 0`. Rewrite using `[smul_smul, ← pow_succ]`. Conclude with `h0`. Establish `hq : Module.length R (Q ⧸ Submodule.span R {π • x}) ≤ 1`. Use `length_le_one_of_cyclic_smul_eq_zero π hπ (Submodule.mkQ _ x) ?_ ?_` and prove the remaining obligations.

Establish `e : ({(Submodule.span R {π • x}).mkQ x} : Set (Q ⧸ Submodule.span R {π • x})) = (Submodule.span R {π • x}).mkQ '' {x}` using `Set.image_singleton.symm`. Rewrite using `[e, ← Submodule.map_span, hx, Submodule.map_top, Submodule.range_mkQ]`. Rewrite using `[← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `Submodule.mem_span_singleton_self _`. Rewrite using `[length_eq_length_add_length_quot (Submodule.span R {π • x})]`.

Combine the equalities or inequalities in the displayed calculation.
-/
private theorem length_le_of_cyclic_pow_smul_eq_zero {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) (k : ℕ) : ∀ (Q : Type) [AddCommGroup Q] [Module R Q] (x : Q),
    Submodule.span R {x} = ⊤ → π ^ k • x = 0 → Module.length R Q ≤ k := by
  induction k with
  | zero =>
    intro Q _ _ x hx h0
    rw [pow_zero, one_smul] at h0
    subst h0
    rw [Submodule.span_singleton_eq_bot.mpr rfl] at hx
    have h0 : ∀ z : Q, z = 0 := by
      intro z
      have hz : z ∈ (⊥ : Submodule R Q) := by
        rw [hx]
        exact Submodule.mem_top
      exact (Submodule.mem_bot R).mp hz
    have : Subsingleton Q := ⟨fun a b => (h0 a).trans (h0 b).symm⟩
    rw [Module.length_eq_zero_iff.mpr this]
    simp
  | succ k ih =>
    intro Q _ _ x hx h0
    have hW : Module.length R (Submodule.span R {π • x}) ≤ k := by
      refine ih (Submodule.span R {π • x}) ⟨π • x, Submodule.mem_span_singleton_self _⟩
        (span_singleton_self_subtype_eq_univ _) ?_
      apply Subtype.ext
      show π ^ k • π • x = 0
      rw [smul_smul, ← pow_succ]
      exact h0
    have hq : Module.length R (Q ⧸ Submodule.span R {π • x}) ≤ 1 := by
      refine length_le_one_of_cyclic_smul_eq_zero π hπ (Submodule.mkQ _ x) ?_ ?_
      · have e : ({(Submodule.span R {π • x}).mkQ x} : Set (Q ⧸ Submodule.span R {π • x})) =
            (Submodule.span R {π • x}).mkQ '' {x} := Set.image_singleton.symm
        rw [e, ← Submodule.map_span, hx, Submodule.map_top, Submodule.range_mkQ]
      · rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.mem_span_singleton_self _
    rw [length_eq_length_add_length_quot (Submodule.span R {π • x})]
    calc _ ≤ (k : ℕ∞) + 1 := add_le_add hW hq
      _ = ((k + 1 : ℕ) : ℕ∞) := (Nat.cast_succ k).symm

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `Q _ _ g hg _`. Rewrite `hg` using `[Set.range_eq_empty g, Submodule.span_empty]`.

Establish `h0 : ∀ z : Q, z = 0`. Introduce `z`. Establish `hz : z ∈ (⊥ : Submodule R Q)`. Rewrite using `[hg]`. Conclude with `Submodule.mem_top`.

Conclude with `(Submodule.mem_bot R).mp hz`. Establish `: Subsingleton Q` using `⟨fun a b => (h0 a).trans (h0 b).symm⟩`. Rewrite using `[Module.length_eq_zero_iff.mpr this]`. Simplify using the standard rewrite rules. Consider the case `succ n ih`.

Introduce `Q _ _ g hg hk`. Establish `hW : Module.length R (Submodule.span R {g 0}) ≤ k` using `length_le_of_cyclic_pow_smul_eq_zero π hπ k (Submodule.span R {g 0}) ⟨g 0, Submodule.mem_span_singleton_self _⟩ (span_singleton_self_subtype_eq_univ _) (Subtype.ext (hk (g 0)))`. Establish `hq : Module.length R (Q ⧸ Submodule.span R {g 0}) ≤ ((k * n : ℕ) : ℕ∞)`. Use `ih (Q ⧸ Submodule.span R {g 0}) (fun i => (Submodule.span R {g 0}).mkQ (g i.succ)) ?_ ?_` and prove the remaining obligations. Establish `htop` using `span_range_map_eq_univ_of_surjective (Submodule.span R {g 0}).mkQ (Submodule.span R {g 0}).mkQ_surjective g hg`.

Rewrite using `[eq_top_iff, ← htop, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero => show (Submodule.span R {g 0}).mkQ (g 0) ∈ _`. Rewrite using `[Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self _)]`.

Conclude with `Submodule.zero_mem _`. Consider the case `succ j => exact Submodule.subset_span ⟨j, rfl⟩`. Introduce `q`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Rewrite using `[← Submodule.Quotient.mk_smul, hk z, Submodule.Quotient.mk_zero]`.

Rewrite using `[length_eq_length_add_length_quot (Submodule.span R {g 0})]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem length_le_mul_of_span_fin_pow_smul_eq_zero {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) (k : ℕ) : ∀ (n : ℕ) (Q : Type) [AddCommGroup Q] [Module R Q]
    (g : Fin n → Q), Submodule.span R (Set.range g) = ⊤ → (∀ q : Q, π ^ k • q = 0) →
    Module.length R Q ≤ ((k * n : ℕ) : ℕ∞) := by
  intro n
  induction n with
  | zero =>
    intro Q _ _ g hg _
    rw [Set.range_eq_empty g, Submodule.span_empty] at hg
    have h0 : ∀ z : Q, z = 0 := by
      intro z
      have hz : z ∈ (⊥ : Submodule R Q) := by
        rw [hg]
        exact Submodule.mem_top
      exact (Submodule.mem_bot R).mp hz
    have : Subsingleton Q := ⟨fun a b => (h0 a).trans (h0 b).symm⟩
    rw [Module.length_eq_zero_iff.mpr this]
    simp
  | succ n ih =>
    intro Q _ _ g hg hk
    have hW : Module.length R (Submodule.span R {g 0}) ≤ k :=
      length_le_of_cyclic_pow_smul_eq_zero π hπ k (Submodule.span R {g 0}) ⟨g 0, Submodule.mem_span_singleton_self _⟩
        (span_singleton_self_subtype_eq_univ _) (Subtype.ext (hk (g 0)))
    have hq : Module.length R (Q ⧸ Submodule.span R {g 0}) ≤ ((k * n : ℕ) : ℕ∞) := by
      refine ih (Q ⧸ Submodule.span R {g 0}) (fun i => (Submodule.span R {g 0}).mkQ (g i.succ))
        ?_ ?_
      · have htop := span_range_map_eq_univ_of_surjective (Submodule.span R {g 0}).mkQ
          (Submodule.span R {g 0}).mkQ_surjective g hg
        rw [eq_top_iff, ← htop, Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        induction i using Fin.cases with
        | zero =>
          show (Submodule.span R {g 0}).mkQ (g 0) ∈ _
          rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr
            (Submodule.mem_span_singleton_self _)]
          exact Submodule.zero_mem _
        | succ j => exact Submodule.subset_span ⟨j, rfl⟩
      · intro q
        obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        rw [← Submodule.Quotient.mk_smul, hk z, Submodule.Quotient.mk_zero]
    rw [length_eq_length_add_length_quot (Submodule.span R {g 0})]
    calc _ ≤ (k : ℕ∞) + ((k * n : ℕ) : ℕ∞) := add_le_add hW hq
      _ = ((k * (n + 1) : ℕ) : ℕ∞) := by push_cast; ring

/- English proof (translation)
Introduce `V`. Proceed by induction on `V with`. Consider the case `zero`. Introduce `E b hV _ _`. Establish `h0 : ∀ z ∈ E 0, z = 0`.

Rewrite using `[hV]`. Introduce `z hz`. Conclude with `(Submodule.mem_bot R).mp hz`. Establish `: Subsingleton (E 0)` using `⟨fun a c => Subtype.ext ((h0 _ a.2).trans (h0 _ c.2).symm)⟩`. Rewrite using `[Module.length_eq_zero_iff.mpr this]`.

Simplify using the standard rewrite rules. Consider the case `succ V ih`. Introduce `E b hV hE hb`. Establish `h1` using `ih (fun j => E (j + 1)) (fun j => b (j + 1)) hV (fun j => hE (j + 1)) (fun j hj => hb (j + 1) (by omega))`. Establish `h2 : Module.length R ((E 1).comap (E 0).subtype) ≤ Module.length R (E 1)` using `Module.length_le_of_injective (Submodule.comapSubtypeEquivOfLe (hE 0)).toLinearMap (Submodule.comapSubtypeEquivOfLe (hE 0)).injective`.

Establish `h3` using `hb 0 (by omega)`. Rewrite using `[length_eq_length_add_length_quot ((E 1).comap (E 0).subtype), Finset.sum_range_succ', Nat.cast_add]`. Conclude with `add_le_add (h2.trans h1) h3`.
-/
private theorem length_le_sum_of_antitone_chain_quot_le {R Z : Type} [CommRing R] [AddCommGroup Z] [Module R Z] :
    ∀ (V : ℕ) (E : ℕ → Submodule R Z) (b : ℕ → ℕ), E V = ⊥ → (∀ j, E (j + 1) ≤ E j) →
    (∀ j < V, Module.length R (E j ⧸ (E (j + 1)).comap (E j).subtype) ≤ (b j : ℕ∞)) →
    Module.length R (E 0) ≤ ((∑ j ∈ Finset.range V, b j : ℕ) : ℕ∞) := by
  intro V
  induction V with
  | zero =>
    intro E b hV _ _
    have h0 : ∀ z ∈ E 0, z = 0 := by
      rw [hV]
      intro z hz
      exact (Submodule.mem_bot R).mp hz
    have : Subsingleton (E 0) := ⟨fun a c => Subtype.ext ((h0 _ a.2).trans (h0 _ c.2).symm)⟩
    rw [Module.length_eq_zero_iff.mpr this]
    simp
  | succ V ih =>
    intro E b hV hE hb
    have h1 := ih (fun j => E (j + 1)) (fun j => b (j + 1)) hV (fun j => hE (j + 1))
      (fun j hj => hb (j + 1) (by omega))
    have h2 : Module.length R ((E 1).comap (E 0).subtype) ≤ Module.length R (E 1) :=
      Module.length_le_of_injective (Submodule.comapSubtypeEquivOfLe (hE 0)).toLinearMap
        (Submodule.comapSubtypeEquivOfLe (hE 0)).injective
    have h3 := hb 0 (by omega)
    rw [length_eq_length_add_length_quot ((E 1).comap (E 0).subtype), Finset.sum_range_succ', Nat.cast_add]
    exact add_le_add (h2.trans h1) h3

/- English proof (translation)
Use `set ψ : (Fin n → R) →ₗ[R] Z := ∑ i, (LinearMap.proj i : (Fin n → R) →ₗ[R] R).smulRight (g i) with hψdef`. Establish `hψ : ∀ i, ψ (Pi.single i 1) = g i`. Introduce `i`. Simplify using `[hψdef, Pi.single_apply]`. Establish `hrange : E ≤ LinearMap.range ψ`.

Use `hg.trans (Submodule.span_le.mpr ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨Pi.single i 1, hψ i⟩`. Take `⟨m, b⟩` from `Submodule.basisOfPid (Pi.basisFun R (Fin n)) (E.comap ψ)`. Establish `hm : m ≤ n`.

Establish `h1` using `Submodule.finrank_le (E.comap ψ)`. Rewrite `h1` using `[Module.finrank_eq_card_basis b, Fintype.card_fin, Module.finrank_fin_fun]`. Conclude with `h1`. Use `set Ψ : (E.comap ψ) →ₗ[R] E := LinearMap.codRestrict E (ψ ∘ₗ (E.comap ψ).subtype) (fun p => p.2) with hΨdef`. Establish `hΨ : Function.Surjective Ψ`.

Introduce `e`. Take `⟨r, hr⟩` from `hrange e.2`. Use `⟨⟨r, ?_⟩, Subtype.ext hr⟩` and prove the remaining obligations. Use `show ψ r ∈ E`. Rewrite using `[hr]`.

Conclude with `e.2`. Establish `hF : Function.Surjective ((E'.comap E.subtype).mkQ ∘ₗ Ψ)` using `(Submodule.mkQ_surjective _).comp hΨ`. Establish `hsp` using `span_range_map_eq_univ_of_surjective ((E'.comap E.subtype).mkQ ∘ₗ Ψ) hF b b.span_eq`. Establish `hkill : ∀ q : (E ⧸ E'.comap E.subtype), π ^ S • q = 0`. Introduce `q`.

Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `hEE z.1 z.2`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem length_quot_comap_le_mul_of_pow_smul_mem {R Z : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup Z] [Module R Z] (π : R) (hπ : Irreducible π) (S n : ℕ) (E E' : Submodule R Z)
    (hEE : ∀ z ∈ E, π ^ S • z ∈ E') (g : Fin n → Z) (hg : E ≤ Submodule.span R (Set.range g)) :
    Module.length R (E ⧸ E'.comap E.subtype) ≤ ((S * n : ℕ) : ℕ∞) := by
  set ψ : (Fin n → R) →ₗ[R] Z :=
    ∑ i, (LinearMap.proj i : (Fin n → R) →ₗ[R] R).smulRight (g i) with hψdef
  have hψ : ∀ i, ψ (Pi.single i 1) = g i := by
    intro i
    simp [hψdef, Pi.single_apply]
  have hrange : E ≤ LinearMap.range ψ := by
    refine hg.trans (Submodule.span_le.mpr ?_)
    rintro _ ⟨i, rfl⟩
    exact ⟨Pi.single i 1, hψ i⟩
  obtain ⟨m, b⟩ := Submodule.basisOfPid (Pi.basisFun R (Fin n)) (E.comap ψ)
  have hm : m ≤ n := by
    have h1 := Submodule.finrank_le (E.comap ψ)
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin, Module.finrank_fin_fun] at h1
    exact h1
  set Ψ : (E.comap ψ) →ₗ[R] E := LinearMap.codRestrict E (ψ ∘ₗ (E.comap ψ).subtype)
    (fun p => p.2) with hΨdef
  have hΨ : Function.Surjective Ψ := by
    intro e
    obtain ⟨r, hr⟩ := hrange e.2
    refine ⟨⟨r, ?_⟩, Subtype.ext hr⟩
    show ψ r ∈ E
    rw [hr]
    exact e.2
  have hF : Function.Surjective ((E'.comap E.subtype).mkQ ∘ₗ Ψ) :=
    (Submodule.mkQ_surjective _).comp hΨ
  have hsp := span_range_map_eq_univ_of_surjective ((E'.comap E.subtype).mkQ ∘ₗ Ψ) hF b b.span_eq
  have hkill : ∀ q : (E ⧸ E'.comap E.subtype), π ^ S • q = 0 := by
    intro q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hEE z.1 z.2
  calc Module.length R (E ⧸ E'.comap E.subtype) ≤ ((S * m : ℕ) : ℕ∞) :=
        length_le_mul_of_span_fin_pow_smul_eq_zero π hπ S m _ _ hsp hkill
    _ ≤ ((S * n : ℕ) : ℕ∞) := by exact_mod_cast Nat.mul_le_mul_left S hm

/- English proof (translation)
Use `set K : Submodule R M := Submodule.comap M.subtype (N ⊓ (Ideal.span {π ^ τ}) • M) with hKdef`. Use `choose! C hCM hCcard hCx using h1`. Use `set A0 : Submodule R (M ⧸ K) := LinearMap.range ((π ^ τ) • (LinearMap.id : (M ⧸ K) →ₗ[R] (M ⧸ K))) with hA0def`. Use `set bas := Module.finBasisOfFinrankEq R M hd with hbas`. Establish `hQ : Module.length R ((M ⧸ K) ⧸ A0) ≤ ((τ * d : ℕ) : ℕ∞)`.

Use `length_le_mul_of_span_fin_pow_smul_eq_zero π hπ τ d ((M ⧸ K) ⧸ A0) (fun i => (A0.mkQ ∘ₗ K.mkQ) (bas i)) ?_ ?_` and prove the remaining obligations. Conclude with `span_range_map_eq_univ_of_surjective (A0.mkQ ∘ₗ K.mkQ) ((Submodule.mkQ_surjective A0).comp (Submodule.mkQ_surjective K)) bas bas.span_eq`. Introduce `q`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective A0 q`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`.

Conclude with `LinearMap.mem_range.mpr ⟨z, rfl⟩`. Establish `hKθ : K ≤ LinearMap.ker (N.mkQ ∘ₗ M.subtype)`. Introduce `x hx`. Rewrite using `[LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `(Submodule.mem_inf.mp (Submodule.mem_comap.mp hx)).1`.

Use `set θ : (M ⧸ K) →ₗ[R] X ⧸ N := K.liftQ (N.mkQ ∘ₗ M.subtype) hKθ with hθdef`. Establish `hθmk : ∀ x : M, θ (Submodule.Quotient.mk x) = N.mkQ (x : X)` using `fun x => rfl`. Use `set E : ℕ → Submodule R (X ⧸ N) := fun j => Submodule.map (N.mkQ ∘ₗ M.subtype) (LinearMap.range ((π ^ (τ + j * S)) • (LinearMap.id : M →ₗ[R] M))) with hEdef`. Establish `hEmem : ∀ j (x : M), N.mkQ (π ^ (τ + j * S) • (x : X)) ∈ E j` using `fun j x => Submodule.mem_map.mpr ⟨π ^ (τ + j * S) • x, LinearMap.mem_range.mpr ⟨x, rfl⟩, rfl⟩`. Establish `hEcases : ∀ j, ∀ w ∈ E j, ∃ x : M, w = N.mkQ (π ^ (τ + j * S) • (x : X))`.

Introduce `j w hw`. Simplify using `only [hEdef] at hw`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.mp hw`. Take `⟨x, rfl⟩` from `LinearMap.mem_range.mp hy`. Conclude with `⟨x, rfl⟩`.

Establish `hAx : ∀ a : M ⧸ K, a ∈ A0 → ∃ x : M, a = Submodule.Quotient.mk (π ^ τ • x)`. Introduce `a ha`. Take `⟨w, hw⟩` from `LinearMap.mem_range.mp ha`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective K w`. Conclude with `⟨x, by rw [← hw, LinearMap.smul_apply, LinearMap.id_apply, Submodule.Quotient.mk_smul]⟩`.

Establish `hθA : ∀ a : A0, (θ ∘ₗ A0.subtype) a ∈ E 0`. Introduce `a`. Take `⟨x, hx⟩` from `hAx a a.2`. Rewrite using `[LinearMap.comp_apply, Submodule.subtype_apply, hx, hθmk, Submodule.coe_smul]`. Simplify using `using hEmem 0 x`.

Use `set θA : A0 →ₗ[R] E 0 := LinearMap.codRestrict (E 0) (θ ∘ₗ A0.subtype) hθA with hθAdef`. Establish `hθinj : Function.Injective θA`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `a ha`. Establish `ha' : θ (a : M ⧸ K) = 0` using `congrArg Subtype.val ha`.

Take `⟨x, hx⟩` from `hAx a a.2`. Rewrite `ha'` using `[hx, hθmk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hx, Submodule.coe_zero, Submodule.Quotient.mk_eq_zero]`. Conclude with `Submodule.mem_comap.mpr (Submodule.mem_inf.mpr ⟨ha', Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) x.2⟩)`.

Take `⟨C0, -, hC0card, hC0⟩` from `h2`. Establish `hC0e : C0 = ∅` using `Finset.card_eq_zero.mp (Nat.le_zero.mp hC0card)`. Establish `hEV : E V = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `w hw`.

Take `⟨x, rfl⟩` from `hEcases V w hw`. Rewrite using `[Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Establish `hx' : π ^ (V * S) • (π ^ τ • (x : X)) ∈ N`. Establish `h` using `hC0 (π ^ τ • (x : X)) (M.smul_mem _ x.2)`. Rewrite `h` using `[hC0e, Finset.coe_empty, Submodule.span_empty, sup_bot_eq]`. Then use the resulting hypothesis.

Rewrite `hx'` using `[smul_smul, ← pow_add, add_comm (V * S) τ]`. Then use the resulting hypothesis. Establish `hEmono : ∀ j, E (j + 1) ≤ E j`. Introduce `j w hw`. Take `⟨x, rfl⟩` from `hEcases (j + 1) w hw`. Establish `e : π ^ (τ + (j + 1) * S) • (x : X) = π ^ (τ + j * S) • ((π ^ S • x : M) : X)`.

Rewrite using `[Submodule.coe_smul, smul_smul, ← pow_add]`. Put the polynomial expressions in normal form. Rewrite using `[e]`. Conclude with `hEmem j _`. Establish `hEstep : ∀ j, ∀ z ∈ E j, π ^ S • z ∈ E (j + 1)`.

Introduce `j z hz`. Take `⟨x, rfl⟩` from `hEcases j z hz`. Establish `e : π ^ S • N.mkQ (π ^ (τ + j * S) • (x : X)) = N.mkQ (π ^ (τ + (j + 1) * S) • (x : X))`. Rewrite using `[← map_smul, smul_smul, ← pow_add]`. Put the polynomial expressions in normal form.

Rewrite using `[e]`. Conclude with `hEmem (j + 1) x`. Establish `hEspan : ∀ j < V, E j ≤ Submodule.span R (Set.range (fun i : Fin (C j).card => N.mkQ (((C j).equivFin.symm i : C j) : X)))`. Introduce `j hj w hw`. Take `⟨x, rfl⟩` from `hEcases j w hw`.

Take `⟨n, hn, c, hc, hnc⟩` from `Submodule.mem_sup.mp (hCx j hj x x.2)`. Establish `hmk : N.mkQ (π ^ (τ + j * S) • (x : X)) = N.mkQ c`. Rewrite using `[← hnc, map_add, Submodule.mkQ_apply N n, (Submodule.Quotient.mk_eq_zero N).mpr hn, zero_add]`. Rewrite using `[hmk]`. Establish `hle : Submodule.map N.mkQ (Submodule.span R (↑(C j) : Set X)) ≤ Submodule.span R (Set.range (fun i : Fin (C j).card => N.mkQ (((C j).equivFin.symm i : C j) : X)))`.

Rewrite using `[Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `Submodule.subset_span ⟨(C j).equivFin ⟨y, hy⟩, by simp⟩`. Conclude with `hle ⟨c, hc, rfl⟩`. Establish `hE0 : Module.length R (E 0) ≤ ((∑ j ∈ Finset.range V, S * (C j).card : ℕ) : ℕ∞)` using `length_le_sum_of_antitone_chain_quot_le V E (fun j => S * (C j).card) hEV hEmono (fun j hj => length_quot_comap_le_mul_of_pow_smul_mem π hπ S _ (E j) (E (j + 1)) (hEstep j) _ (hEspan j hj))`.

Establish `hA0 : Module.length R A0 ≤ Module.length R (E 0)` using `Module.length_le_of_injective θA hθinj`. Establish `hL : Module.length R (M ⧸ K) ≤ ((τ * d + ∑ j ∈ Finset.range V, S * (C j).card : ℕ) : ℕ∞)`. Rewrite using `[length_eq_length_add_length_quot A0, Nat.cast_add]`. Conclude with `(add_le_add (hA0.trans hE0) hQ).trans (le_of_eq (add_comm _ _))`. Take `⟨ℓ, hℓ⟩` from `ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.coe_ne_top _) hL)`.

Use `⟨ℓ, hℓ.symm, ?_⟩` and prove the remaining obligations. Establish `hℓT : ℓ ≤ τ * d + ∑ j ∈ Finset.range V, S * (C j).card`. Rewrite `hL` using `[← hℓ]`. Conclude with `hL` after adjusting the coercions. Establish `hgeom : ∀ W : ℕ, ∑ j ∈ Finset.range W, s ^ (j + 1) ≤ 2 * s - 2 * s ^ (W + 1)`.

Introduce `W`. Proceed by induction on `W with`. Consider the case `zero => simp`. Consider the case `succ W ih`. Rewrite using `[Finset.sum_range_succ]`.

Establish `h3 : 0 ≤ s ^ (W + 1) * (1 - 2 * s)` using `mul_nonneg (pow_nonneg hs0 _) (by linarith)`. Establish `h4 : s ^ (W + 1 + 1) = s ^ (W + 1) * s` using `pow_succ s (W + 1)`. Use polynomial arithmetic with `[h3, h4]`. Establish `hsumC : ∑ j ∈ Finset.range V, (S : ℝ) * ((C j).card : ℝ) ≤ ∑ j ∈ Finset.range V, (S : ℝ) * (d * s ^ (j + 1))`. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `j hj`. Conclude with `mul_le_mul_of_nonneg_left (hCcard j (Finset.mem_range.mp hj)) (Nat.cast_nonneg _)`. Establish `e1 : ∑ j ∈ Finset.range V, (S : ℝ) * (d * s ^ (j + 1)) = ((S : ℝ) * d) * ∑ j ∈ Finset.range V, s ^ (j + 1)`. Rewrite using `[Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `j _`. Expand and normalize the polynomial expressions, which then agree. Establish `hSd : (0 : ℝ) ≤ (S : ℝ) * d` using `by positivity`. Establish `hg2 : ∑ j ∈ Finset.range V, s ^ (j + 1) ≤ 2 * s`. Establish `h5` using `hgeom V`.

Establish `h6` using `pow_nonneg hs0 (V + 1)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfin` using `mul_le_mul_of_nonneg_left hg2 hSd`. Establish `hcast : (ℓ : ℝ) ≤ (τ : ℝ) * d + ∑ j ∈ Finset.range V, (S : ℝ) * ((C j).card : ℝ)`. Establish `h7 : ((ℓ : ℕ) : ℝ) ≤ ((τ * d + ∑ j ∈ Finset.range V, S * (C j).card : ℕ) : ℝ)`.

Conclude with `hℓT` after adjusting the coercions. Move the coercions through the operations in `at h7`. Conclude with `h7`. Use polynomial arithmetic with `[hcast, hsumC, e1, hfin]`.
-/
theorem lengthPart2 {R X : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup X] [Module R X] (π : R) (hπ : Irreducible π) (M N : Submodule R X)
    [Module.Free R M] [Module.Finite R M] (d : ℕ) (hd : Module.finrank R M = d)
    (τ S V : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2)
    (h1 : ∀ β < V, ∃ C : Finset X, (↑C : Set X) ⊆ M ∧
      (C.card : ℝ) ≤ d * s ^ (β + 1) ∧
      ∀ x ∈ M, π ^ (τ + β * S) • x ∈ N ⊔ Submodule.span R (↑C : Set X))
    (h2 : AllButLE π M N 0 (V * S)) :
    ∃ ℓ : ℕ, Module.length R (M ⧸ Submodule.comap M.subtype
        (N ⊓ (Ideal.span {π ^ τ}) • M)) = ℓ ∧
      (ℓ : ℝ) ≤ d * ((τ : ℝ) + 2 * S * s) := by
  classical
  set K : Submodule R M := Submodule.comap M.subtype (N ⊓ (Ideal.span {π ^ τ}) • M) with hKdef
  choose! C hCM hCcard hCx using h1
  set A0 : Submodule R (M ⧸ K) :=
    LinearMap.range ((π ^ τ) • (LinearMap.id : (M ⧸ K) →ₗ[R] (M ⧸ K))) with hA0def
  set bas := Module.finBasisOfFinrankEq R M hd with hbas
  have hQ : Module.length R ((M ⧸ K) ⧸ A0) ≤ ((τ * d : ℕ) : ℕ∞) := by
    refine length_le_mul_of_span_fin_pow_smul_eq_zero π hπ τ d ((M ⧸ K) ⧸ A0) (fun i => (A0.mkQ ∘ₗ K.mkQ) (bas i)) ?_ ?_
    · exact span_range_map_eq_univ_of_surjective (A0.mkQ ∘ₗ K.mkQ)
        ((Submodule.mkQ_surjective A0).comp (Submodule.mkQ_surjective K)) bas bas.span_eq
    · intro q
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective A0 q
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact LinearMap.mem_range.mpr ⟨z, rfl⟩
  have hKθ : K ≤ LinearMap.ker (N.mkQ ∘ₗ M.subtype) := by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact (Submodule.mem_inf.mp (Submodule.mem_comap.mp hx)).1
  set θ : (M ⧸ K) →ₗ[R] X ⧸ N := K.liftQ (N.mkQ ∘ₗ M.subtype) hKθ with hθdef
  have hθmk : ∀ x : M, θ (Submodule.Quotient.mk x) = N.mkQ (x : X) := fun x => rfl
  set E : ℕ → Submodule R (X ⧸ N) := fun j => Submodule.map (N.mkQ ∘ₗ M.subtype)
    (LinearMap.range ((π ^ (τ + j * S)) • (LinearMap.id : M →ₗ[R] M))) with hEdef
  have hEmem : ∀ j (x : M), N.mkQ (π ^ (τ + j * S) • (x : X)) ∈ E j := fun j x =>
    Submodule.mem_map.mpr ⟨π ^ (τ + j * S) • x, LinearMap.mem_range.mpr ⟨x, rfl⟩, rfl⟩
  have hEcases : ∀ j, ∀ w ∈ E j, ∃ x : M, w = N.mkQ (π ^ (τ + j * S) • (x : X)) := by
    intro j w hw
    simp only [hEdef] at hw
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hw
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    exact ⟨x, rfl⟩
  have hAx : ∀ a : M ⧸ K, a ∈ A0 → ∃ x : M, a = Submodule.Quotient.mk (π ^ τ • x) := by
    intro a ha
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp ha
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective K w
    exact ⟨x, by rw [← hw, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.Quotient.mk_smul]⟩
  have hθA : ∀ a : A0, (θ ∘ₗ A0.subtype) a ∈ E 0 := by
    intro a
    obtain ⟨x, hx⟩ := hAx a a.2
    rw [LinearMap.comp_apply, Submodule.subtype_apply, hx, hθmk, Submodule.coe_smul]
    simpa using hEmem 0 x
  set θA : A0 →ₗ[R] E 0 := LinearMap.codRestrict (E 0) (θ ∘ₗ A0.subtype) hθA with hθAdef
  have hθinj : Function.Injective θA := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have ha' : θ (a : M ⧸ K) = 0 := congrArg Subtype.val ha
    obtain ⟨x, hx⟩ := hAx a a.2
    rw [hx, hθmk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at ha'
    apply Subtype.ext
    rw [hx, Submodule.coe_zero, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_comap.mpr (Submodule.mem_inf.mpr
      ⟨ha', Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) x.2⟩)
  obtain ⟨C0, -, hC0card, hC0⟩ := h2
  have hC0e : C0 = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hC0card)
  have hEV : E V = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨x, rfl⟩ := hEcases V w hw
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have hx' : π ^ (V * S) • (π ^ τ • (x : X)) ∈ N := by
      have h := hC0 (π ^ τ • (x : X)) (M.smul_mem _ x.2)
      rwa [hC0e, Finset.coe_empty, Submodule.span_empty, sup_bot_eq] at h
    rwa [smul_smul, ← pow_add, add_comm (V * S) τ] at hx'
  have hEmono : ∀ j, E (j + 1) ≤ E j := by
    intro j w hw
    obtain ⟨x, rfl⟩ := hEcases (j + 1) w hw
    have e : π ^ (τ + (j + 1) * S) • (x : X) = π ^ (τ + j * S) • ((π ^ S • x : M) : X) := by
      rw [Submodule.coe_smul, smul_smul, ← pow_add]
      ring_nf
    rw [e]
    exact hEmem j _
  have hEstep : ∀ j, ∀ z ∈ E j, π ^ S • z ∈ E (j + 1) := by
    intro j z hz
    obtain ⟨x, rfl⟩ := hEcases j z hz
    have e : π ^ S • N.mkQ (π ^ (τ + j * S) • (x : X)) =
        N.mkQ (π ^ (τ + (j + 1) * S) • (x : X)) := by
      rw [← map_smul, smul_smul, ← pow_add]
      ring_nf
    rw [e]
    exact hEmem (j + 1) x
  have hEspan : ∀ j < V, E j ≤ Submodule.span R
      (Set.range (fun i : Fin (C j).card => N.mkQ (((C j).equivFin.symm i : C j) : X))) := by
    intro j hj w hw
    obtain ⟨x, rfl⟩ := hEcases j w hw
    obtain ⟨n, hn, c, hc, hnc⟩ := Submodule.mem_sup.mp (hCx j hj x x.2)
    have hmk : N.mkQ (π ^ (τ + j * S) • (x : X)) = N.mkQ c := by
      rw [← hnc, map_add, Submodule.mkQ_apply N n, (Submodule.Quotient.mk_eq_zero N).mpr hn,
        zero_add]
    rw [hmk]
    have hle : Submodule.map N.mkQ (Submodule.span R (↑(C j) : Set X)) ≤ Submodule.span R
        (Set.range (fun i : Fin (C j).card => N.mkQ (((C j).equivFin.symm i : C j) : X))) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span ⟨(C j).equivFin ⟨y, hy⟩, by simp⟩
    exact hle ⟨c, hc, rfl⟩
  have hE0 : Module.length R (E 0) ≤ ((∑ j ∈ Finset.range V, S * (C j).card : ℕ) : ℕ∞) :=
    length_le_sum_of_antitone_chain_quot_le V E (fun j => S * (C j).card) hEV hEmono
      (fun j hj => length_quot_comap_le_mul_of_pow_smul_mem π hπ S _ (E j) (E (j + 1)) (hEstep j) _ (hEspan j hj))
  have hA0 : Module.length R A0 ≤ Module.length R (E 0) :=
    Module.length_le_of_injective θA hθinj
  have hL : Module.length R (M ⧸ K) ≤
      ((τ * d + ∑ j ∈ Finset.range V, S * (C j).card : ℕ) : ℕ∞) := by
    rw [length_eq_length_add_length_quot A0, Nat.cast_add]
    exact (add_le_add (hA0.trans hE0) hQ).trans (le_of_eq (add_comm _ _))
  obtain ⟨ℓ, hℓ⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.coe_ne_top _) hL)
  refine ⟨ℓ, hℓ.symm, ?_⟩
  have hℓT : ℓ ≤ τ * d + ∑ j ∈ Finset.range V, S * (C j).card := by
    rw [← hℓ] at hL
    exact_mod_cast hL
  have hgeom : ∀ W : ℕ, ∑ j ∈ Finset.range W, s ^ (j + 1) ≤ 2 * s - 2 * s ^ (W + 1) := by
    intro W
    induction W with
    | zero => simp
    | succ W ih =>
      rw [Finset.sum_range_succ]
      have h3 : 0 ≤ s ^ (W + 1) * (1 - 2 * s) := mul_nonneg (pow_nonneg hs0 _) (by linarith)
      have h4 : s ^ (W + 1 + 1) = s ^ (W + 1) * s := pow_succ s (W + 1)
      nlinarith [h3, h4]
  have hsumC : ∑ j ∈ Finset.range V, (S : ℝ) * ((C j).card : ℝ) ≤
      ∑ j ∈ Finset.range V, (S : ℝ) * (d * s ^ (j + 1)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (hCcard j (Finset.mem_range.mp hj)) (Nat.cast_nonneg _)
  have e1 : ∑ j ∈ Finset.range V, (S : ℝ) * (d * s ^ (j + 1)) =
      ((S : ℝ) * d) * ∑ j ∈ Finset.range V, s ^ (j + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hSd : (0 : ℝ) ≤ (S : ℝ) * d := by positivity
  have hg2 : ∑ j ∈ Finset.range V, s ^ (j + 1) ≤ 2 * s := by
    have h5 := hgeom V
    have h6 := pow_nonneg hs0 (V + 1)
    linarith
  have hfin := mul_le_mul_of_nonneg_left hg2 hSd
  have hcast : (ℓ : ℝ) ≤ (τ : ℝ) * d + ∑ j ∈ Finset.range V, (S : ℝ) * ((C j).card : ℝ) := by
    have h7 : ((ℓ : ℕ) : ℝ) ≤ ((τ * d + ∑ j ∈ Finset.range V, S * (C j).card : ℕ) : ℝ) := by
      exact_mod_cast hℓT
    push_cast at h7
    exact h7
  nlinarith [hcast, hsumC, e1, hfin]

end CyclicSpanLengthLemmas

/- English proof (translation)
Introduce `R X _ _ _ _ _ V π hπ L y m c₀ S d a b c Sv κ G _ _ hd hm hcomm hbb hdb ha hb hc hy hG hκ habc hSv hsum`. Establish `hGw : ∀ β : ℕ, ∀ B : Finset (Fin V), B.card = β + 1 → (↑(G B) : Set X) ⊆ L (vertexLabel B) ∧ (G B).card ≤ (fun B => (G B).card) B ∧ ∀ x ∈ L (vertexLabel B), π ^ c₀ • x ∈ (⨆ v ∈ B, (L (Function.update (vertexLabel B) v Slot.ball)).map (y v)) ⊔ Submodule.span R (↑(G B) : Set X)`. Introduce `β B hB`. Establish `h` using `hG B (by omega)`. Conclude with `⟨h.1, le_rfl, h.2.2⟩`.

Establish `hexp : ∑ v, (a v + b v + (m - 1) * c v + m * c₀) ≤ ∑ v, m * (c v + c₀)`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `v _`. Establish `e : m * (c v + c₀) = c v + (m - 1) * c v + m * c₀`. Take `⟨k, rfl⟩ : ∃ k, m = k + 1` from `⟨m - 1, by omega⟩`.

Rewrite using `[Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Nat.add_le_add_right (Nat.add_le_add_right (habc v) _) _`. Establish `hβ : ∀ β : ℕ, ∃ C : Finset X, (↑C : Set X) ⊆ L (fun _ => Slot.base) ∧ (C.card : ℝ) ≤ d * (m : ℝ) ^ (β + 1) * esymmR κ (β + 1) ∧ ∀ x ∈ L (fun _ => Slot.base), π ^ (∑ v, m * (c v + c₀) + β * S) • x ∈ prodIdealMap π y m Sv (L fun _ => Slot.base) ⊔ Submodule.span R (↑C : Set X)`.

Introduce `β`. Take `⟨h1, -⟩` from `hW V π L y m β c₀ S a b c Sv (fun B => (G B).card) G hm hcomm hbb hdb ha hb hc hy (hGw β) hSv`. Take `⟨C, hCM, hCcard, hCx⟩` from `h1`. Use `⟨C, hCM, ?_, ?_⟩` and prove the remaining obligations. Establish `hC' : C.card ≤ ∑ B ∈ (Finset.univ : Finset (Fin V)).powersetCard (β + 1), m ^ (β + 1) * (G B).card` using `hCcard`.

Establish `hcardG : ∀ B ∈ (Finset.univ : Finset (Fin V)).powersetCard (β + 1), ((G B).card : ℝ) ≤ (∏ v ∈ B, κ v) * d`. Introduce `B hB`. Conclude with `(hG B (by rw [(Finset.mem_powersetCard.mp hB).2]; omega)).2.1`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `B hB`. Conclude with `mul_le_mul_of_nonneg_left (hcardG B hB) (by positivity)`. Use `_ = d * (m : ℝ) ^ (β + 1) * esymmR κ (β + 1) := by`. Unfold `esymmR`. Rewrite using `[Finset.mul_sum]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `B _`. Expand and normalize the polynomial expressions, which then agree. Introduce `x hx`. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le (Nat.add_le_add_right hexp (β * S))`.

Rewrite using `[hk, pow_add, mul_smul]`. Conclude with `hCx _ (Submodule.smul_mem _ _ hx)`. Establish `h2 : AllButLE π (L fun _ => Slot.base) (prodIdealMap π y m Sv (L fun _ => Slot.base)) 0 (∑ v, Sv v)` using `(hW V π L y m 0 c₀ S a b c Sv (fun B => (G B).card) G hm hcomm hbb hdb ha hb hc hy (hGw 0) hSv).2`. Use `⟨hβ, h2, ?_⟩` and prove the remaining obligations. Establish `hs0 : (0 : ℝ) ≤ m * ∑ v, κ v` using `mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun v _ => hκ v)`.

Establish `hVS : ∑ v, Sv v ≤ V * S`. Combine the equalities or inequalities in the displayed calculation. Apply `CyclicSpanLengthLemmas.lengthPart2 π hπ _ _ d hd _ S V _ hs0 hsum` to reduce the goal to its premises. Introduce `β _`. Take `⟨C, hCM, hCcard, hCx⟩` from `hβ β`.

Use `⟨C, hCM, ?_, hCx⟩` and prove the remaining obligations. Establish `hE` using `ManyOrbitsP.esymmR_le κ hκ (m : ℝ) (Nat.cast_nonneg _) (β + 1)`. Establish `hP : (0 : ℝ) ≤ ((m : ℝ) * ∑ v, κ v) ^ (β + 1)` using `pow_nonneg hs0 _`. Establish `hF : ((m : ℝ) * ∑ v, κ v) ^ (β + 1) / ((β + 1).factorial : ℝ) ≤ ((m : ℝ) * ∑ v, κ v) ^ (β + 1)` using `div_le_self hP (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `ManyOrbitsP.allBut_mono h2 le_rfl hVS`.
-/
theorem many_orbits_refined_of (hW : WalkSharp) : ManyOrbitsRefined := by
  intro R X _ _ _ _ _ V π hπ L y m c₀ S d a b c Sv κ G _ _ hd hm hcomm hbb hdb ha hb hc hy hG hκ
    habc hSv hsum
  have hGw : ∀ β : ℕ, ∀ B : Finset (Fin V), B.card = β + 1 →
      (↑(G B) : Set X) ⊆ L (vertexLabel B) ∧ (G B).card ≤ (fun B => (G B).card) B ∧
      ∀ x ∈ L (vertexLabel B), π ^ c₀ • x ∈
        (⨆ v ∈ B, (L (Function.update (vertexLabel B) v Slot.ball)).map (y v)) ⊔
          Submodule.span R (↑(G B) : Set X) := by
    intro β B hB
    have h := hG B (by omega)
    exact ⟨h.1, le_rfl, h.2.2⟩
  have hexp : ∑ v, (a v + b v + (m - 1) * c v + m * c₀) ≤ ∑ v, m * (c v + c₀) := by
    apply Finset.sum_le_sum
    intro v _
    have e : m * (c v + c₀) = c v + (m - 1) * c v + m * c₀ := by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      ring
    rw [e]
    exact Nat.add_le_add_right (Nat.add_le_add_right (habc v) _) _
  have hβ : ∀ β : ℕ, ∃ C : Finset X, (↑C : Set X) ⊆ L (fun _ => Slot.base) ∧
      (C.card : ℝ) ≤ d * (m : ℝ) ^ (β + 1) * esymmR κ (β + 1) ∧
      ∀ x ∈ L (fun _ => Slot.base), π ^ (∑ v, m * (c v + c₀) + β * S) • x ∈
        prodIdealMap π y m Sv (L fun _ => Slot.base) ⊔ Submodule.span R (↑C : Set X) := by
    intro β
    obtain ⟨h1, -⟩ := hW V π L y m β c₀ S a b c Sv (fun B => (G B).card) G hm hcomm hbb hdb ha
      hb hc hy (hGw β) hSv
    obtain ⟨C, hCM, hCcard, hCx⟩ := h1
    refine ⟨C, hCM, ?_, ?_⟩
    · have hC' : C.card ≤ ∑ B ∈ (Finset.univ : Finset (Fin V)).powersetCard (β + 1),
          m ^ (β + 1) * (G B).card := hCcard
      have hcardG : ∀ B ∈ (Finset.univ : Finset (Fin V)).powersetCard (β + 1),
          ((G B).card : ℝ) ≤ (∏ v ∈ B, κ v) * d := by
        intro B hB
        exact (hG B (by rw [(Finset.mem_powersetCard.mp hB).2]; omega)).2.1
      calc (C.card : ℝ)
          ≤ ((∑ B ∈ (Finset.univ : Finset (Fin V)).powersetCard (β + 1),
              m ^ (β + 1) * (G B).card : ℕ) : ℝ) := by exact_mod_cast hC'
        _ = ∑ B ∈ (Finset.univ : Finset (Fin V)).powersetCard (β + 1),
              (m : ℝ) ^ (β + 1) * ((G B).card : ℝ) := by push_cast; rfl
        _ ≤ ∑ B ∈ (Finset.univ : Finset (Fin V)).powersetCard (β + 1),
              (m : ℝ) ^ (β + 1) * ((∏ v ∈ B, κ v) * d) := by
            apply Finset.sum_le_sum
            intro B hB
            exact mul_le_mul_of_nonneg_left (hcardG B hB) (by positivity)
        _ = d * (m : ℝ) ^ (β + 1) * esymmR κ (β + 1) := by
            unfold esymmR
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro B _
            ring
    · intro x hx
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.add_le_add_right hexp (β * S))
      rw [hk, pow_add, mul_smul]
      exact hCx _ (Submodule.smul_mem _ _ hx)
  have h2 : AllButLE π (L fun _ => Slot.base) (prodIdealMap π y m Sv (L fun _ => Slot.base)) 0
      (∑ v, Sv v) :=
    (hW V π L y m 0 c₀ S a b c Sv (fun B => (G B).card) G hm hcomm hbb hdb ha hb hc hy
      (hGw 0) hSv).2
  refine ⟨hβ, h2, ?_⟩
  have hs0 : (0 : ℝ) ≤ m * ∑ v, κ v :=
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun v _ => hκ v)
  have hVS : ∑ v, Sv v ≤ V * S := by
    calc ∑ v, Sv v ≤ ∑ _v : Fin V, S := Finset.sum_le_sum fun v _ => hSv v
      _ = V * S := by simp
  apply CyclicSpanLengthLemmas.lengthPart2 π hπ _ _ d hd _ S V _ hs0 hsum
  · intro β _
    obtain ⟨C, hCM, hCcard, hCx⟩ := hβ β
    refine ⟨C, hCM, ?_, hCx⟩
    have hE := ManyOrbitsP.esymmR_le κ hκ (m : ℝ) (Nat.cast_nonneg _) (β + 1)
    have hP : (0 : ℝ) ≤ ((m : ℝ) * ∑ v, κ v) ^ (β + 1) := pow_nonneg hs0 _
    have hF : ((m : ℝ) * ∑ v, κ v) ^ (β + 1) / ((β + 1).factorial : ℝ) ≤
        ((m : ℝ) * ∑ v, κ v) ^ (β + 1) :=
      div_le_self hP (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
    calc (C.card : ℝ) ≤ d * (m : ℝ) ^ (β + 1) * esymmR κ (β + 1) := hCcard
      _ = d * ((m : ℝ) ^ (β + 1) * esymmR κ (β + 1)) := by ring
      _ ≤ d * (((m : ℝ) * ∑ v, κ v) ^ (β + 1)) :=
          mul_le_mul_of_nonneg_left (hE.trans hF) (Nat.cast_nonneg _)
  · exact ManyOrbitsP.allBut_mono h2 le_rfl hVS

/- English proof (translation)
The claim follows from `many_orbits_refined_of walkSharp_true`.
-/
theorem many_orbits_refined_holds : ManyOrbitsRefined := many_orbits_refined_of walkSharp_true

end Formalism.G0
