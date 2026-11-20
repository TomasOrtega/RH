import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.DetColon

variable {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
  [IsScalarTower (𝓞 F) F V] {d : ℕ}

open NumberField MvPolynomial in
variable {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
  [IsScalarTower (𝓞 F) F V] {d : ℕ} in
/- English proof (translation)
Take `⟨a, ha⟩` from `Submodule.mem_span_singleton.mp hi`. Take `⟨b, hb⟩` from `Submodule.mem_span_singleton.mp hk`. Distinguish the cases in `hb0 : algebraMap (𝓞 F) F b = 0`. Establish `hwk : w k = 0`. Rewrite using `[← hb, ← algebraMap_smul F b u, hb0, zero_smul]`.

Conclude with `f.map_coord_zero k hwk`. Establish `hwi : w i = (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) • w k`. Rewrite using `[← ha, ← hb, ← algebraMap_smul F a u, ← algebraMap_smul F b u, smul_smul, div_mul_cancel₀ _ hb0]`. Establish `hfw : f w = f (Function.update w i ((algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) • w k))`. Rewrite using `[← hwi, Function.update_eq_self]`.

Rewrite using `[hfw, f.map_update_smul]`. Establish `h0 : f (Function.update w i (w k)) = 0` using `f.map_eq_zero_of_eq (Function.update w i (w k)) (i := i) (j := k) (by simp [Function.update_of_ne hik.symm]) hik`. Rewrite using `[h0, smul_zero]`.
-/
private lemma exterior_form_eq_zero_of_two_mem_span_singleton {ι : Type*} [DecidableEq ι]
    (f : V [⋀^ι]→ₗ[F] F) (u : V) (w : ι → V) {i k : ι} (hik : i ≠ k)
    (hi : w i ∈ Submodule.span (𝓞 F) {u}) (hk : w k ∈ Submodule.span (𝓞 F) {u}) :
    f w = 0 := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hi
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hk
  by_cases hb0 : algebraMap (𝓞 F) F b = 0
  · have hwk : w k = 0 := by
      rw [← hb, ← algebraMap_smul F b u, hb0, zero_smul]
    exact f.map_coord_zero k hwk
  · have hwi : w i = (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) • w k := by
      rw [← ha, ← hb, ← algebraMap_smul F a u, ← algebraMap_smul F b u, smul_smul,
        div_mul_cancel₀ _ hb0]
    have hfw : f w = f (Function.update w i
        ((algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) • w k)) := by
      rw [← hwi, Function.update_eq_self]
    rw [hfw, f.map_update_smul]
    have h0 : f (Function.update w i (w k)) = 0 :=
      f.map_eq_zero_of_eq (Function.update w i (w k)) (i := i) (j := k)
        (by simp [Function.update_of_ne hik.symm]) hik
    rw [h0, smul_zero]

open NumberField MvPolynomial in
variable {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
  [IsScalarTower (𝓞 F) F V] {d : ℕ} in
/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `i w _ _ hN _`. Conclude with `Submodule.subset_span ⟨w, fun j => hN j (by simp), rfl⟩`. Consider the case `@insert k s hks ih`.

Introduce `i w his hi hN hs`. Establish `hik : i ≠ k` using `fun h => his (h ▸ Finset.mem_insert_self k s)`. Establish `his' : i ∉ s` using `fun h => his (Finset.mem_insert_of_mem h)`. Take `⟨n, hn, z, hz, hnz⟩` from `Submodule.mem_sup.mp (hs k (Finset.mem_insert_self k s))`. Establish `hsplit : f w = f (Function.update w k n) + f (Function.update w k z)`.

Rewrite using `[← f.map_update_add, hnz, Function.update_eq_self]`. Rewrite using `[hsplit]`. Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Use `ih i _ his' ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne hik]` and apply the resulting hypothesis.

Introduce `j hj`. Distinguish the cases in `hjk : j = k`. Rewrite using `[hjk, Function.update_self]`. Conclude with `hn`. Rewrite using `[Function.update_of_ne hjk]`.

Conclude with `hN j (by simp [hjk, hj])`. Introduce `j hj`. Establish `hjk : j ≠ k` using `fun h => hks (h ▸ hj)`. Rewrite using `[Function.update_of_ne hjk]`. Conclude with `hs j (Finset.mem_insert_of_mem hj)`.

Rewrite using `[exterior_form_eq_zero_of_two_mem_span_singleton f u _ hik (by rwa [Function.update_of_ne hik]) (by rw [Function.update_self]; exact hz)]`. Conclude with `Submodule.zero_mem _`.
-/
private lemma multilinear_mem_span_of_entry_mem_span_singleton {ι : Type*} [DecidableEq ι]
    (f : V [⋀^ι]→ₗ[F] F) (N : Submodule (𝓞 F) V) (u : V) (s : Finset ι) :
    ∀ (i : ι) (w : ι → V), i ∉ s → w i ∈ Submodule.span (𝓞 F) {u} → (∀ j ∉ s, w j ∈ N) →
      (∀ j ∈ s, w j ∈ N ⊔ Submodule.span (𝓞 F) {u}) →
      f w ∈ Submodule.span (𝓞 F) {y | ∃ v : ι → V, (∀ j, v j ∈ N) ∧ y = f v} := by
  induction s using Finset.induction_on with
  | empty =>
    intro i w _ _ hN _
    exact Submodule.subset_span ⟨w, fun j => hN j (by simp), rfl⟩
  | @insert k s hks ih =>
    intro i w his hi hN hs
    have hik : i ≠ k := fun h => his (h ▸ Finset.mem_insert_self k s)
    have his' : i ∉ s := fun h => his (Finset.mem_insert_of_mem h)
    obtain ⟨n, hn, z, hz, hnz⟩ := Submodule.mem_sup.mp (hs k (Finset.mem_insert_self k s))
    have hsplit : f w = f (Function.update w k n) + f (Function.update w k z) := by
      rw [← f.map_update_add, hnz, Function.update_eq_self]
    rw [hsplit]
    refine Submodule.add_mem _ ?_ ?_
    · refine ih i _ his' ?_ ?_ ?_
      · rwa [Function.update_of_ne hik]
      · intro j hj
        by_cases hjk : j = k
        · rw [hjk, Function.update_self]
          exact hn
        · rw [Function.update_of_ne hjk]
          exact hN j (by simp [hjk, hj])
      · intro j hj
        have hjk : j ≠ k := fun h => hks (h ▸ hj)
        rw [Function.update_of_ne hjk]
        exact hs j (Finset.mem_insert_of_mem hj)
    · rw [exterior_form_eq_zero_of_two_mem_span_singleton f u _ hik
        (by rwa [Function.update_of_ne hik]) (by rw [Function.update_self]; exact hz)]
      exact Submodule.zero_mem _

open NumberField MvPolynomial in
variable {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
  [IsScalarTower (𝓞 F) F V] {d : ℕ} in
/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `w hN _`. Conclude with `Submodule.smul_mem _ π (Submodule.subset_span ⟨w, fun j => hN j (by simp), rfl⟩)`. Consider the case `@insert k s hks ih`.

Introduce `w hN hs`. Take `⟨n, hn, z, hz, hnz⟩` from `Submodule.mem_sup.mp (hs k (Finset.mem_insert_self k s))`. Establish `hsplit : f w = f (Function.update w k n) + f (Function.update w k z)`. Rewrite using `[← f.map_update_add, hnz, Function.update_eq_self]`. Rewrite using `[hsplit, smul_add]`.

Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Use `ih _ ?_ ?_` and prove the remaining obligations. Introduce `j hj`. Distinguish the cases in `hjk : j = k`. Rewrite using `[hjk, Function.update_self]`.

Conclude with `hn`. Rewrite using `[Function.update_of_ne hjk]`. Conclude with `hN j (by simp [hjk, hj])`. Introduce `j hj`. Establish `hjk : j ≠ k` using `fun h => hks (h ▸ hj)`.

Rewrite using `[Function.update_of_ne hjk]`. Conclude with `hs j (Finset.mem_insert_of_mem hj)`. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.mp hz`. Establish `key : π • f (Function.update w k (a • u)) = f (Function.update w k ((π * a) • u))`. Rewrite using `[mul_smul, ← algebraMap_smul F π (a • u), f.map_update_smul, algebraMap_smul]`.

Rewrite using `[key]`. Use `multilinear_mem_span_of_entry_mem_span_singleton f N u s k _ hks ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[Function.update_self]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)`. Introduce `j hj`.

Distinguish the cases in `hjk : j = k`. Rewrite using `[hjk, Function.update_self, mul_comm, mul_smul]`. Conclude with `N.smul_mem a hπ`. Rewrite using `[Function.update_of_ne hjk]`. Conclude with `hN j (by simp [hjk, hj])`.

Introduce `j hj`. Establish `hjk : j ≠ k` using `fun h => hks (h ▸ hj)`. Rewrite using `[Function.update_of_ne hjk]`. Conclude with `hs j (Finset.mem_insert_of_mem hj)`.
-/
private lemma smul_multilinear_mem_span {ι : Type*} [DecidableEq ι] (f : V [⋀^ι]→ₗ[F] F)
    (N : Submodule (𝓞 F) V) (u : V) (π : 𝓞 F) (hπ : π • u ∈ N) (s : Finset ι) :
    ∀ w : ι → V, (∀ j ∉ s, w j ∈ N) → (∀ j ∈ s, w j ∈ N ⊔ Submodule.span (𝓞 F) {u}) →
      π • f w ∈ Submodule.span (𝓞 F) {y | ∃ v : ι → V, (∀ j, v j ∈ N) ∧ y = f v} := by
  induction s using Finset.induction_on with
  | empty =>
    intro w hN _
    exact Submodule.smul_mem _ π (Submodule.subset_span ⟨w, fun j => hN j (by simp), rfl⟩)
  | @insert k s hks ih =>
    intro w hN hs
    obtain ⟨n, hn, z, hz, hnz⟩ := Submodule.mem_sup.mp (hs k (Finset.mem_insert_self k s))
    have hsplit : f w = f (Function.update w k n) + f (Function.update w k z) := by
      rw [← f.map_update_add, hnz, Function.update_eq_self]
    rw [hsplit, smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · refine ih _ ?_ ?_
      · intro j hj
        by_cases hjk : j = k
        · rw [hjk, Function.update_self]
          exact hn
        · rw [Function.update_of_ne hjk]
          exact hN j (by simp [hjk, hj])
      · intro j hj
        have hjk : j ≠ k := fun h => hks (h ▸ hj)
        rw [Function.update_of_ne hjk]
        exact hs j (Finset.mem_insert_of_mem hj)
    · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
      have key : π • f (Function.update w k (a • u)) = f (Function.update w k ((π * a) • u)) := by
        rw [mul_smul, ← algebraMap_smul F π (a • u), f.map_update_smul, algebraMap_smul]
      rw [key]
      refine multilinear_mem_span_of_entry_mem_span_singleton f N u s k _ hks ?_ ?_ ?_
      · rw [Function.update_self]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
      · intro j hj
        by_cases hjk : j = k
        · rw [hjk, Function.update_self, mul_comm, mul_smul]
          exact N.smul_mem a hπ
        · rw [Function.update_of_ne hjk]
          exact hN j (by simp [hjk, hj])
      · intro j hj
        have hjk : j ≠ k := fun h => hks (h ▸ hj)
        rw [Function.update_of_ne hjk]
        exact hs j (Finset.mem_insert_of_mem hj)

open NumberField MvPolynomial in
variable {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
  [IsScalarTower (𝓞 F) F V] {d : ℕ} in

/- English proof (translation)
Introduce `F V _ _ _ _ _ _ d b N u π hπ y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨v, hv, rfl⟩` from `hx`. Conclude with `smul_multilinear_mem_span b.det N u π hπ Finset.univ v (fun j hj => absurd (Finset.mem_univ j) hj) (fun j _ => hv j)`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`.

Rewrite using `[smul_comm]`. Conclude with `Submodule.smul_mem _ a hx`.
-/
theorem _root_.GlobalTheory.DetColon.smul_detSpan_sup_le :
    ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
      [IsScalarTower (𝓞 F) F V] (d : ℕ) (b : Module.Basis (Fin d) F V) (N : Submodule (𝓞 F) V)
      (u : V) (π : 𝓞 F), π • u ∈ N →
      ∀ y ∈ Submodule.span (𝓞 F)
          {y | ∃ v : Fin d → V, (∀ i, v i ∈ N ⊔ Submodule.span (𝓞 F) {u}) ∧ y = b.det v},
        π • y ∈ Submodule.span (𝓞 F) {y | ∃ v : Fin d → V, (∀ i, v i ∈ N) ∧ y = b.det v} := by
  intro F V _ _ _ _ _ _ d b N u π hπ y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    exact smul_multilinear_mem_span b.det N u π hπ Finset.univ v
      (fun j hj => absurd (Finset.mem_univ j) hj) (fun j _ => hv j)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_comm]
    exact Submodule.smul_mem _ a hx

end GlobalTheory.DetColon
