import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.LatticeGens

section Dedekind
variable {R V : Type*} [CommRing R] [IsDedekindDomain R] [AddCommGroup V] [Module R V]

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`. Introduce `_ L h1 h2`. Conclude with `⟨∅, le_rfl, le_antisymm h2 (by simpa using h1)⟩`. Consider the case `insert x t hx ih`.

Introduce `ht L h1 h2`. Take `⟨t', hc, ht'⟩` from `ih (fun y hy => ht y (Finset.mem_insert_of_mem hy)) (L ⊓ (A ⊔ Submodule.span R (t : Set V))) (le_inf h1 le_sup_left) inf_le_right`. Use `set I : Ideal R := (A ⊔ Submodule.span R (t : Set V)).comap (LinearMap.toSpanSingleton R V x) with hI`. Use `set J : Ideal R := (L ⊔ Submodule.span R (t : Set V)).comap (LinearMap.toSpanSingleton R V x) with hJ`. Establish `hIJ : I ≤ J` using `Submodule.comap_mono (sup_le_sup_right h1 _)`.

Establish `hI0 : I ≠ 0`. Introduce `h`. Establish `: m ∈ I` using `Submodule.mem_sup_left (ht x (Finset.mem_insert_self _ _))`. Rewrite `this` using `[h]`. Conclude with `hm (by simpa using this)`.

Take `⟨a, ha⟩` from `IsDedekindDomain.exists_sup_span_eq hIJ hI0`. Establish `haJ : a ∈ J`. Rewrite using `[← ha]`. Conclude with `Submodule.mem_sup_right (Ideal.mem_span_singleton_self a)`. Take `⟨l, hl, s, hs, hls⟩` from `Submodule.mem_sup.1 haJ`.

Establish `hls' : l + s = a • x` using `hls`. Use `⟨insert l t', ?_, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.card_insert_of_notMem hx]`. Conclude with `(Finset.card_insert_le _ _).trans (by omega)`. Introduce `y hy`.

Establish `hy2` using `h2 hy`. Rewrite `hy2` using `[Finset.coe_insert, Submodule.span_insert]`. Take `⟨a0, ha0, z, hz, rfl⟩` from `Submodule.mem_sup.1 hy2`. Take `⟨w, hw, s0, hs0, rfl⟩` from `Submodule.mem_sup.1 hz`. Take `⟨r, rfl⟩` from `Submodule.mem_span_singleton.1 hw`.

Establish `hr : r ∈ J`. Establish `: r • x = ((a0 + (r • x + s0)) - a0) - s0` using `by abel`. Express the relevant statement in the definitionally equal form `r • x ∈ L ⊔ Submodule.span R (t : Set V)`. Rewrite using `[this]`. Conclude with `sub_mem (Submodule.mem_sup_left (sub_mem hy (h1 ha0))) (Submodule.mem_sup_right hs0)`.

Rewrite `hr` using `[← ha]`. Take `⟨i, hi, j, hj, rfl⟩` from `Submodule.mem_sup.1 hr`. Take `⟨k, rfl⟩` from `Ideal.mem_span_singleton'.1 hj`. Establish `hi' : i • x ∈ A ⊔ Submodule.span R (t : Set V)` using `hi`. Establish `key : a0 + ((i + k * a) • x + s0) - k • l ∈ L ⊓ (A ⊔ Submodule.span R (t : Set V))`.

Use `⟨sub_mem hy (L.smul_mem _ hl), ?_⟩` and prove the remaining obligations. Establish `: a0 + ((i + k * a) • x + s0) - k • l = a0 + i • x + s0 + k • s`. Rewrite using `[add_smul, mul_smul, ← hls', smul_add]`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`.

Conclude with `add_mem (add_mem (add_mem (Submodule.mem_sup_left ha0) hi') (Submodule.mem_sup_right hs0)) (Submodule.mem_sup_right (Submodule.smul_mem _ _ hs))`. Rewrite `key` using `[ht']`. Establish `hle : A ⊔ Submodule.span R (t' : Set V) ≤ A ⊔ Submodule.span R ((insert l t' : Finset V) : Set V)` using `sup_le_sup_left (Submodule.span_mono (by simp)) _`. Establish `hl' : k • l ∈ A ⊔ Submodule.span R ((insert l t' : Finset V) : Set V)` using `Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))`. Simplify using `using add_mem (hle key) hl'`.

Rewrite using `[Finset.coe_insert, Submodule.span_insert]`. Use `sup_le h1 (sup_le ?_ ?_)` and prove the remaining obligations. Conclude with `(Submodule.span_singleton_le_iff_mem _ _).2 hl`. Conclude with `(le_sup_right.trans ht'.ge).trans inf_le_left`.
-/
theorem exists_gens_of_between (A : Submodule R V) (m : R) (hm : m ≠ 0) (t : Finset V) :
    (∀ x ∈ t, m • x ∈ A) → ∀ L : Submodule R V, A ≤ L → L ≤ A ⊔ Submodule.span R (t : Set V) →
      ∃ t' : Finset V, t'.card ≤ t.card ∧ L = A ⊔ Submodule.span R (t' : Set V) := by
  induction t using Finset.induction_on with
  | empty =>
    intro _ L h1 h2
    exact ⟨∅, le_rfl, le_antisymm h2 (by simpa using h1)⟩
  | insert x t hx ih =>
    intro ht L h1 h2
    obtain ⟨t', hc, ht'⟩ := ih (fun y hy => ht y (Finset.mem_insert_of_mem hy))
      (L ⊓ (A ⊔ Submodule.span R (t : Set V))) (le_inf h1 le_sup_left) inf_le_right
    set I : Ideal R := (A ⊔ Submodule.span R (t : Set V)).comap (LinearMap.toSpanSingleton R V x)
      with hI
    set J : Ideal R := (L ⊔ Submodule.span R (t : Set V)).comap (LinearMap.toSpanSingleton R V x)
      with hJ
    have hIJ : I ≤ J := Submodule.comap_mono (sup_le_sup_right h1 _)
    have hI0 : I ≠ 0 := by
      intro h
      have : m ∈ I := Submodule.mem_sup_left (ht x (Finset.mem_insert_self _ _))
      rw [h] at this
      exact hm (by simpa using this)
    obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq hIJ hI0
    have haJ : a ∈ J := by
      rw [← ha]; exact Submodule.mem_sup_right (Ideal.mem_span_singleton_self a)
    obtain ⟨l, hl, s, hs, hls⟩ := Submodule.mem_sup.1 haJ
    have hls' : l + s = a • x := hls
    refine ⟨insert l t', ?_, le_antisymm ?_ ?_⟩
    · rw [Finset.card_insert_of_notMem hx]
      exact (Finset.card_insert_le _ _).trans (by omega)
    · intro y hy
      have hy2 := h2 hy
      rw [Finset.coe_insert, Submodule.span_insert] at hy2
      obtain ⟨a0, ha0, z, hz, rfl⟩ := Submodule.mem_sup.1 hy2
      obtain ⟨w, hw, s0, hs0, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hw
      have hr : r ∈ J := by
        have : r • x = ((a0 + (r • x + s0)) - a0) - s0 := by abel
        change r • x ∈ L ⊔ Submodule.span R (t : Set V)
        rw [this]
        exact sub_mem (Submodule.mem_sup_left (sub_mem hy (h1 ha0))) (Submodule.mem_sup_right hs0)
      rw [← ha] at hr
      obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.1 hr
      obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.1 hj
      have hi' : i • x ∈ A ⊔ Submodule.span R (t : Set V) := hi
      have key : a0 + ((i + k * a) • x + s0) - k • l ∈
          L ⊓ (A ⊔ Submodule.span R (t : Set V)) := by
        refine ⟨sub_mem hy (L.smul_mem _ hl), ?_⟩
        have : a0 + ((i + k * a) • x + s0) - k • l = a0 + i • x + s0 + k • s := by
          rw [add_smul, mul_smul, ← hls', smul_add]; abel
        rw [this]
        exact add_mem (add_mem (add_mem (Submodule.mem_sup_left ha0) hi')
          (Submodule.mem_sup_right hs0)) (Submodule.mem_sup_right (Submodule.smul_mem _ _ hs))
      rw [ht'] at key
      have hle : A ⊔ Submodule.span R (t' : Set V) ≤
          A ⊔ Submodule.span R ((insert l t' : Finset V) : Set V) :=
        sup_le_sup_left (Submodule.span_mono (by simp)) _
      have hl' : k • l ∈ A ⊔ Submodule.span R ((insert l t' : Finset V) : Set V) :=
        Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      simpa using add_mem (hle key) hl'
    · rw [Finset.coe_insert, Submodule.span_insert]
      refine sup_le h1 (sup_le ?_ ?_)
      · exact (Submodule.span_singleton_le_iff_mem _ _).2 hl
      · exact (le_sup_right.trans ht'.ge).trans inf_le_left

end Dedekind

section Count
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/- English proof (translation)
Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `AddSubgroup.nsmul_relIndex_mem A.toAddSubgroup (K := B.toAddSubgroup) hx`.
-/
theorem idxN_smul_mem (A B : Submodule R V) {x : V} (hx : x ∈ B) :
    ((idxN B A : ℕ) : R) • x ∈ A := by
  rw [Nat.cast_smul_eq_nsmul]
  exact AddSubgroup.nsmul_relIndex_mem A.toAddSubgroup (K := B.toAddSubgroup) hx

/- English proof (translation)
Establish `h` using `AddSubgroup.relIndex_ker (K := B.toAddSubgroup) A.mkQ.toAddMonoidHom`. Establish `hk : A.mkQ.toAddMonoidHom.ker = A.toAddSubgroup`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite `h` using `[hk]`.

Unfold `idxN`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem card_map_mkQ (A B : Submodule R V) : Nat.card (B.map A.mkQ) = idxN B A := by
  have h := AddSubgroup.relIndex_ker (K := B.toAddSubgroup) A.mkQ.toAddMonoidHom
  have hk : A.mkQ.toAddMonoidHom.ker = A.toAddSubgroup := by
    ext x; simp
  rw [hk] at h
  unfold idxN
  rw [h]
  rfl

/- English proof (translation)
Establish `hfin : Finite (B.map A.mkQ)` using `Nat.finite_of_card_ne_zero (by rwa [card_map_mkQ])`. Set `Φ : (Fin e → B.map A.mkQ) → Submodule R V` to `fun f => (Submodule.span R (Set.range fun i => (f i : V ⧸ A))).comap A.mkQ`. Establish `hsub : {L | A ≤ L ∧ L ≤ B} ⊆ Φ '' Set.univ`. Introduce and unpack `L ⟨h1, h2⟩`. Take `⟨t, hc, ht⟩` from `h L h1 h2`.

Take `⟨emb⟩ : Nonempty (t ↪ Fin e)` from `Function.Embedding.nonempty_of_card_le (by simpa using hc)`. Set `g : Fin e → V` to `Function.extend emb (fun x => (x : V)) 0`. Establish `hg : ∀ i, g i ∈ Submodule.span R (t : Set V)`. Introduce `i`. Distinguish the cases in `hi : ∃ x, emb x = i`.

Take `⟨x, rfl⟩` from `hi`. Simplify using `only [g, emb.injective.extend_apply]`. Conclude with `Submodule.subset_span x.2`. Simplify using `only [g, Function.extend_apply' _ _ _ hi]`. Simplify using the standard rewrite rules.

Establish `hspan : Submodule.span R (Set.range g) = Submodule.span R (t : Set V)`. Use `le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hg i`. Introduce `x hx`.

Conclude with `⟨emb ⟨x, hx⟩, by simp only [g, emb.injective.extend_apply]⟩`. Establish `hgB : ∀ i, g i ∈ B` using `fun i => h2 (by rw [ht]; exact Submodule.mem_sup_right (hg i))`. Use `⟨fun i => ⟨A.mkQ (g i), Submodule.mem_map_of_mem (hgB i)⟩, trivial, ?_⟩` and prove the remaining obligations. Establish `: (Set.range fun i => A.mkQ (g i)) = A.mkQ '' Set.range g`. Rewrite using `[← Set.range_comp]`.

Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `(Submodule.span R (Set.range fun i => A.mkQ (g i))).comap A.mkQ = L`. Rewrite using `[this, ← Submodule.map_span, Submodule.comap_map_mkQ, hspan, ← ht]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Set.encard_univ, ENat.card_eq_coe_natCard, Nat.card_fun, card_map_mkQ]`.

Simplify using the standard rewrite rules.
-/
theorem encard_between_le (A B : Submodule R V) (hn : idxN B A ≠ 0) (e : ℕ)
    (h : ∀ L, A ≤ L → L ≤ B →
      ∃ t' : Finset V, t'.card ≤ e ∧ L = A ⊔ Submodule.span R (t' : Set V)) :
    {L | A ≤ L ∧ L ≤ B}.encard ≤ ((idxN B A ^ e : ℕ) : ℕ∞) := by
  have hfin : Finite (B.map A.mkQ) := Nat.finite_of_card_ne_zero (by rwa [card_map_mkQ])
  let Φ : (Fin e → B.map A.mkQ) → Submodule R V := fun f =>
    (Submodule.span R (Set.range fun i => (f i : V ⧸ A))).comap A.mkQ
  have hsub : {L | A ≤ L ∧ L ≤ B} ⊆ Φ '' Set.univ := by
    rintro L ⟨h1, h2⟩
    obtain ⟨t, hc, ht⟩ := h L h1 h2
    obtain ⟨emb⟩ : Nonempty (t ↪ Fin e) :=
      Function.Embedding.nonempty_of_card_le (by simpa using hc)
    let g : Fin e → V := Function.extend emb (fun x => (x : V)) 0
    have hg : ∀ i, g i ∈ Submodule.span R (t : Set V) := by
      intro i
      by_cases hi : ∃ x, emb x = i
      · obtain ⟨x, rfl⟩ := hi
        simp only [g, emb.injective.extend_apply]
        exact Submodule.subset_span x.2
      · simp only [g, Function.extend_apply' _ _ _ hi]
        simp
    have hspan : Submodule.span R (Set.range g) = Submodule.span R (t : Set V) := by
      refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
      · rintro _ ⟨i, rfl⟩; exact hg i
      · intro x hx
        exact ⟨emb ⟨x, hx⟩, by simp only [g, emb.injective.extend_apply]⟩
    have hgB : ∀ i, g i ∈ B := fun i => h2 (by rw [ht]; exact Submodule.mem_sup_right (hg i))
    refine ⟨fun i => ⟨A.mkQ (g i), Submodule.mem_map_of_mem (hgB i)⟩, trivial, ?_⟩
    have : (Set.range fun i => A.mkQ (g i)) = A.mkQ '' Set.range g := by
      rw [← Set.range_comp]; rfl
    change (Submodule.span R (Set.range fun i => A.mkQ (g i))).comap A.mkQ = L
    rw [this, ← Submodule.map_span, Submodule.comap_map_mkQ, hspan, ← ht]
  calc {L | A ≤ L ∧ L ≤ B}.encard ≤ (Φ '' Set.univ).encard := Set.encard_le_encard hsub
    _ ≤ (Set.univ : Set (Fin e → B.map A.mkQ)).encard := Set.encard_image_le _ _
    _ = _ := by
      rw [Set.encard_univ, ENat.card_eq_coe_natCard, Nat.card_fun, card_map_mkQ]
      simp

end Count

/- English proof (translation)
Take `⟨b, hbB, hspan, hli⟩` from `exists_linearIndependent K (B : Set V)`. Establish `hbf : b.Finite` using `hli.setFinite`. Take `⟨s, rfl⟩` from `hbf.exists_finset_coe`. Establish `hcard : s.card ≤ Module.finrank K V` using `LinearIndependent.finset_card_le_finrank hli`. Take `⟨G, rfl⟩` from `hB`.

Establish `h1 : ∀ x ∈ G, ∃ c : 𝓞 K, c ≠ 0 ∧ c • x ∈ Submodule.span (𝓞 K) (s : Set V)`. Introduce `x hx`. Establish `hx' : x ∈ Submodule.span K (s : Set V)`. Rewrite using `[hspan]`. Conclude with `Submodule.subset_span (Submodule.subset_span hx)`.

Take `⟨c, hc⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ _ hx'`. Conclude with `⟨c, nonZeroDivisors.coe_ne_zero c, hc⟩`. Use `choose! f hf0 hf using h1`. Use `set c : 𝓞 K := ∏ x ∈ G, f x with hc`. Establish `hc0 : c ≠ 0` using `Finset.prod_ne_zero_iff.2 hf0`.

Establish `hcK : algebraMap (𝓞 K) K c ≠ 0` using `by simpa using hc0`. Establish `hcG : ∀ x ∈ G, c • x ∈ Submodule.span (𝓞 K) (s : Set V)`. Introduce `x hx`. Rewrite using `[hc, ← Finset.prod_erase_mul _ _ hx, mul_smul]`. Conclude with `Submodule.smul_mem _ _ (hf x hx)`.

Set `φ : V →ₗ[𝓞 K] V` to `(LinearMap.lsmul K V (algebraMap (𝓞 K) K c)⁻¹).restrictScalars (𝓞 K)`. Establish `hφ : ∀ x, φ (c • x) = x`. Introduce `x`. Simplify using `only [φ, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]`. Rewrite using `[← algebraMap_smul K c x, smul_smul, inv_mul_cancel₀ hcK, one_smul]`.

Use `⟨c, s.image φ, hc0, Finset.card_image_le.trans hcard, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨y, hy, rfl⟩` from `Finset.mem_image.1 hx`. Rewrite using `[← map_smul, hφ]`. Conclude with `hbB hy`.

Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Rewrite using `[Finset.coe_image, ← Submodule.map_span, ← hφ x]`. Conclude with `Submodule.mem_map_of_mem (hcG x hx)`.
-/
theorem exists_scaled_span (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (B : Submodule (𝓞 K) V) (hB : B.FG) :
    ∃ (c : 𝓞 K) (t : Finset V), c ≠ 0 ∧ t.card ≤ Module.finrank K V ∧ (∀ x ∈ t, c • x ∈ B) ∧
      B ≤ Submodule.span (𝓞 K) (t : Set V) := by
  obtain ⟨b, hbB, hspan, hli⟩ := exists_linearIndependent K (B : Set V)
  have hbf : b.Finite := hli.setFinite
  obtain ⟨s, rfl⟩ := hbf.exists_finset_coe
  have hcard : s.card ≤ Module.finrank K V := LinearIndependent.finset_card_le_finrank hli
  obtain ⟨G, rfl⟩ := hB
  have h1 : ∀ x ∈ G, ∃ c : 𝓞 K, c ≠ 0 ∧ c • x ∈ Submodule.span (𝓞 K) (s : Set V) := by
    intro x hx
    have hx' : x ∈ Submodule.span K (s : Set V) := by
      rw [hspan]; exact Submodule.subset_span (Submodule.subset_span hx)
    obtain ⟨c, hc⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ _ hx'
    exact ⟨c, nonZeroDivisors.coe_ne_zero c, hc⟩
  choose! f hf0 hf using h1
  set c : 𝓞 K := ∏ x ∈ G, f x with hc
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 hf0
  have hcK : algebraMap (𝓞 K) K c ≠ 0 := by simpa using hc0
  have hcG : ∀ x ∈ G, c • x ∈ Submodule.span (𝓞 K) (s : Set V) := by
    intro x hx
    rw [hc, ← Finset.prod_erase_mul _ _ hx, mul_smul]
    exact Submodule.smul_mem _ _ (hf x hx)
  let φ : V →ₗ[𝓞 K] V := (LinearMap.lsmul K V (algebraMap (𝓞 K) K c)⁻¹).restrictScalars (𝓞 K)
  have hφ : ∀ x, φ (c • x) = x := by
    intro x
    simp only [φ, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]
    rw [← algebraMap_smul K c x, smul_smul, inv_mul_cancel₀ hcK, one_smul]
  refine ⟨c, s.image φ, hc0, Finset.card_image_le.trans hcard, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    rw [← map_smul, hφ]
    exact hbB hy
  · rw [Submodule.span_le]
    intro x hx
    rw [Finset.coe_image, ← Submodule.map_span, ← hφ x]
    exact Submodule.mem_map_of_mem (hcG x hx)

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ A B hAB hn`. Establish `hn' : ((idxN B A : ℕ) : 𝓞 K) ≠ 0` using `Nat.cast_ne_zero.2 hn`. Use `⟨fun hB => ?_, fun e t hc ht => ?_⟩` and prove the remaining obligations. Take `⟨c, t, hc0, hcard, hcB, hBt⟩` from `exists_scaled_span K V B hB`. Take `⟨t', h1, h2⟩` from `exists_gens_of_between A (((idxN B A : ℕ) : 𝓞 K) * c) (mul_ne_zero hn' hc0) t (fun x hx => by rw [mul_smul]; exact idxN_smul_mem A B (hcB x hx)) B hAB (hBt.trans le_sup_right)`.

Conclude with `⟨t', h1.trans hcard, h2⟩`. Establish `key : ∀ L, A ≤ L → L ≤ B → ∃ t' : Finset V, t'.card ≤ e ∧ L = A ⊔ Submodule.span (𝓞 K) (t' : Set V)`. Introduce `L h1 h2`. Take `⟨t', h3, h4⟩` from `exists_gens_of_between A _ hn' t (fun x hx => idxN_smul_mem A B (by rw [ht]; exact Submodule.mem_sup_right (Submodule.subset_span hx))) L h1 (h2.trans ht.le)`. Conclude with `⟨t', h3.trans hc, h4⟩`.

Conclude with `⟨encard_between_le A B hn e key, key⟩`.
-/
theorem gens_and_count : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (A B : Submodule (𝓞 K) V), A ≤ B → idxN B A ≠ 0 → (B.FG → ∃ t : Finset V, t.card ≤ Module.finrank K V ∧ B = A ⊔ Submodule.span (𝓞 K) (t : Set V)) ∧ ∀ (e : ℕ) (t : Finset V), t.card ≤ e → B = A ⊔ Submodule.span (𝓞 K) (t : Set V) → ({L | A ≤ L ∧ L ≤ B}.encard ≤ ((idxN B A ^ e : ℕ) : ℕ∞)) ∧ ∀ L, A ≤ L → L ≤ B → ∃ t' : Finset V, t'.card ≤ e ∧ L = A ⊔ Submodule.span (𝓞 K) (t' : Set V) := by
  intro K V _ _ _ _ _ _ _ A B hAB hn
  have hn' : ((idxN B A : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hn
  refine ⟨fun hB => ?_, fun e t hc ht => ?_⟩
  · obtain ⟨c, t, hc0, hcard, hcB, hBt⟩ := exists_scaled_span K V B hB
    obtain ⟨t', h1, h2⟩ := exists_gens_of_between A (((idxN B A : ℕ) : 𝓞 K) * c)
      (mul_ne_zero hn' hc0) t
      (fun x hx => by rw [mul_smul]; exact idxN_smul_mem A B (hcB x hx)) B hAB
      (hBt.trans le_sup_right)
    exact ⟨t', h1.trans hcard, h2⟩
  · have key : ∀ L, A ≤ L → L ≤ B →
        ∃ t' : Finset V, t'.card ≤ e ∧ L = A ⊔ Submodule.span (𝓞 K) (t' : Set V) := by
      intro L h1 h2
      obtain ⟨t', h3, h4⟩ := exists_gens_of_between A _ hn' t
        (fun x hx => idxN_smul_mem A B
          (by rw [ht]; exact Submodule.mem_sup_right (Submodule.subset_span hx))) L h1
        (h2.trans ht.le)
      exact ⟨t', h3.trans hc, h4⟩
    exact ⟨encard_between_le A B hn e key, key⟩

end GlobalTheory.Mass.LatticeGens
