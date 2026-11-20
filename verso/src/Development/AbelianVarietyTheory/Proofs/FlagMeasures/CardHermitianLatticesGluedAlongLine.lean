import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeQuotientGensAndIntermediateCount
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExtensionTotallyDefiniteHermitian
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.LineGlue

/- English proof (translation)
Establish `key : ∀ {y z : W}, y - z ∈ B → B ⊔ Submodule.span R {y} ≤ B ⊔ Submodule.span R {z}`. Introduce `y z hyz`. Use `sup_le le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).2 ?_)` and prove the remaining obligations. Use `add_mem (Submodule.mem_sup_left hyz : y - z ∈ B ⊔ Submodule.span R {z}) (Submodule.mem_sup_right (Submodule.mem_span_singleton_self z))` as an intermediate fact. Simplify using `using this`.

Conclude with `le_antisymm (key hyz) (key (by simpa using B.neg_mem hyz))`.
-/
theorem sup_span_congr {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (B : Submodule R W) {y z : W} (hyz : y - z ∈ B) :
    B ⊔ Submodule.span R {y} = B ⊔ Submodule.span R {z} := by
  have key : ∀ {y z : W}, y - z ∈ B → B ⊔ Submodule.span R {y} ≤ B ⊔ Submodule.span R {z} := by
    intro y z hyz
    refine sup_le le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).2 ?_)
    have := add_mem (Submodule.mem_sup_left hyz : y - z ∈ B ⊔ Submodule.span R {z})
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self z))
    simpa using this
  exact le_antisymm (key hyz) (key (by simpa using B.neg_mem hyz))

section Line

variable {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]

/- English proof (translation)
Take `⟨t, ht, e⟩` from `(LatticeGens.gens_and_count K W B C hBC (DiscOrder.idxN_ne_zero hB hC)).1 hC`. Rewrite `ht` using `[h1]`. Take `⟨y, hy⟩` from `Finset.card_le_one_iff_subset_singleton.1 ht`. Break down `Finset.subset_singleton_iff.1 hy with rfl | rfl` into its components or cases. Conclude with `⟨0, by simpa using e⟩`.

Conclude with `⟨y, by simpa using e⟩`.
-/
theorem exists_gen (h1 : Module.finrank K W = 1) {B C : Submodule (𝓞 K) W}
    (hB : Submodule.IsLattice K B) (hBC : B ≤ C) (hC : C.FG) :
    ∃ y, C = B ⊔ Submodule.span (𝓞 K) {y} := by
  obtain ⟨t, ht, e⟩ := (LatticeGens.gens_and_count K W B C hBC
    (DiscOrder.idxN_ne_zero hB hC)).1 hC
  rw [h1] at ht
  obtain ⟨y, hy⟩ := Finset.card_le_one_iff_subset_singleton.1 ht
  rcases Finset.subset_singleton_iff.1 hy with rfl | rfl
  · exact ⟨0, by simpa using e⟩
  · exact ⟨y, by simpa using e⟩

/- English proof (translation)
Use `set D : Submodule (𝓞 K) W := B.comap (LinearMap.lsmul (𝓞 K) W T) with hD`. Establish `hTK : algebraMap (𝓞 K) K T ≠ 0` using `by simpa using hT`. Establish `hinj : Function.Injective (LinearMap.lsmul (𝓞 K) W T)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`.

Establish `: algebraMap (𝓞 K) K T • x = 0` using `by rw [algebraMap_smul]; exact hx`. Conclude with `(smul_eq_zero.1 this).resolve_left hTK`. Establish `hDfg : D.FG` using `Submodule.fg_of_fg_map_injective _ hinj (hB.fg.of_le (Submodule.map_comap_le _ _))`. Take `⟨y, hy⟩` from `exists_gen h1 hB (fun x hx => B.smul_mem T hx : B ≤ D) hDfg`. Establish `hyD : T • y ∈ B`.

Establish `: y ∈ D`. Rewrite using `[hy]`. Conclude with `Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)`. Conclude with `this`. Set `Φ : (𝓞 K ⧸ Ideal.span {T}) → Submodule (𝓞 K) W` to `fun q => B ⊔ Submodule.span (𝓞 K) {(Quotient.out q : 𝓞 K) • y}`.

Establish `hsub : {C : Submodule (𝓞 K) W | B ≤ C ∧ ∀ x ∈ C, T • x ∈ B} ⊆ Φ '' Set.univ`. Introduce and unpack `C ⟨hBC, hC⟩`. Establish `hCD : C ≤ D` using `hC`. Take `⟨c, hc⟩` from `exists_gen h1 hB hBC (hDfg.of_le hCD)`. Establish `hcD : c ∈ B ⊔ Submodule.span (𝓞 K) {y}`.

Rewrite using `[← hy]`. Apply `hCD` to reduce the goal to its premises. Rewrite using `[hc]`. Conclude with `Submodule.mem_sup_right (Submodule.mem_span_singleton_self c)`. Take `⟨a, ha, z, hz, rfl⟩` from `Submodule.mem_sup.1 hcD`.

Take `⟨r, rfl⟩` from `Submodule.mem_span_singleton.1 hz`. Use `⟨Ideal.Quotient.mk _ r, trivial, ?_⟩` and prove the remaining obligations. Rewrite using `[hc]`. Apply `sup_span_congr` to reduce the goal to its premises. Establish `: Quotient.out (Ideal.Quotient.mk (Ideal.span {T}) r) - r ∈ Ideal.span {T}`.

Rewrite using `[← Ideal.Quotient.eq]`. Conclude with `Ideal.Quotient.mk_out _`. Take `⟨k, hk⟩` from `Ideal.mem_span_singleton'.1 this`. Establish `e : Quotient.out (Ideal.Quotient.mk (Ideal.span {T}) r) • y - (a + r • y) = k • (T • y) - a`. Rewrite using `[smul_smul, hk, sub_smul]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `sub_mem (B.smul_mem k hyD) ha`. Establish `hn : Ideal.absNorm (Ideal.span {T}) ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`.

Conclude with `hT`. Establish `hcard : Nat.card (𝓞 K ⧸ Ideal.span {T}) = Ideal.absNorm (Ideal.span {T})` using `rfl`. Establish `: Finite (𝓞 K ⧸ Ideal.span {T})` using `Nat.finite_of_card_ne_zero (by rwa [hcard])`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem encard_between (h1 : Module.finrank K W = 1) {B : Submodule (𝓞 K) W}
    (hB : Submodule.IsLattice K B) (T : 𝓞 K) (hT : T ≠ 0) :
    {C : Submodule (𝓞 K) W | B ≤ C ∧ ∀ x ∈ C, T • x ∈ B}.encard ≤
      ((Ideal.absNorm (Ideal.span {T}) : ℕ) : ℕ∞) := by
  set D : Submodule (𝓞 K) W := B.comap (LinearMap.lsmul (𝓞 K) W T) with hD
  have hTK : algebraMap (𝓞 K) K T ≠ 0 := by simpa using hT
  have hinj : Function.Injective (LinearMap.lsmul (𝓞 K) W T) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have : algebraMap (𝓞 K) K T • x = 0 := by rw [algebraMap_smul]; exact hx
    exact (smul_eq_zero.1 this).resolve_left hTK
  have hDfg : D.FG :=
    Submodule.fg_of_fg_map_injective _ hinj (hB.fg.of_le (Submodule.map_comap_le _ _))
  obtain ⟨y, hy⟩ := exists_gen h1 hB (fun x hx => B.smul_mem T hx : B ≤ D) hDfg
  have hyD : T • y ∈ B := by
    have : y ∈ D := by
      rw [hy]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)
    exact this
  let Φ : (𝓞 K ⧸ Ideal.span {T}) → Submodule (𝓞 K) W := fun q =>
    B ⊔ Submodule.span (𝓞 K) {(Quotient.out q : 𝓞 K) • y}
  have hsub : {C : Submodule (𝓞 K) W | B ≤ C ∧ ∀ x ∈ C, T • x ∈ B} ⊆ Φ '' Set.univ := by
    rintro C ⟨hBC, hC⟩
    have hCD : C ≤ D := hC
    obtain ⟨c, hc⟩ := exists_gen h1 hB hBC (hDfg.of_le hCD)
    have hcD : c ∈ B ⊔ Submodule.span (𝓞 K) {y} := by
      rw [← hy]
      apply hCD
      rw [hc]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self c)
    obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.1 hcD
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hz
    refine ⟨Ideal.Quotient.mk _ r, trivial, ?_⟩
    rw [hc]
    apply sup_span_congr
    have : Quotient.out (Ideal.Quotient.mk (Ideal.span {T}) r) - r ∈ Ideal.span {T} := by
      rw [← Ideal.Quotient.eq]
      exact Ideal.Quotient.mk_out _
    obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.1 this
    have e : Quotient.out (Ideal.Quotient.mk (Ideal.span {T}) r) • y - (a + r • y) =
        k • (T • y) - a := by
      rw [smul_smul, hk, sub_smul]; abel
    rw [e]
    exact sub_mem (B.smul_mem k hyD) ha
  have hn : Ideal.absNorm (Ideal.span {T}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hT
  have hcard : Nat.card (𝓞 K ⧸ Ideal.span {T}) = Ideal.absNorm (Ideal.span {T}) := rfl
  have : Finite (𝓞 K ⧸ Ideal.span {T}) := Nat.finite_of_card_ne_zero (by rwa [hcard])
  calc _ ≤ (Φ '' Set.univ).encard := Set.encard_le_encard hsub
    _ ≤ (Set.univ : Set (𝓞 K ⧸ Ideal.span {T})).encard := Set.encard_image_le _ _
    _ = _ := by rw [Set.encard_univ, ENat.card_eq_coe_natCard, hcard]

end Line

/- English proof (translation)
Establish `ha : ∀ x, h x x = 0 → x = 0`. Introduce `x hx`. Assume the negation of the conclusion as `h0`. Take `⟨τ⟩ : Nonempty (K →+* ℂ)` from `inferInstance`. Use `hpd τ x h0` as an intermediate fact.

Simplify using `[hx] at this`. Conclude with `⟨fun x hx => ha x (hx x), fun x hx => ha x (hx x)⟩`.
-/
theorem nondeg_of_pd {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (hpd : PD h) : h.Nondegenerate := by
  have ha : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra h0
    obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hpd τ x h0
    simp [hx] at this
  exact ⟨fun x hx => ha x (hx x), fun x hx => ha x (hx x)⟩

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ _ h hK hs hpd U A B T hT h1 hA hB`. Take `⟨hc, hsU, hpU, -⟩` from `(Witt.witt_definite K V h hK hs hpd).2 U`. Take `⟨-, hsW, hpW, -⟩` from `(Witt.witt_definite K V h hK hs hpd).2 (perp h U)`. Establish `hd0 : discN (hRes h U) A ≠ 0` using `(DiscOrder.main K U (hRes h U) hK hsU (nondeg_of_pd _ hpU) A hA).1`. Establish `dl` using `dualLattice (𝓞 K) K (perp h U) (hRes h (perp h U)) hsW (nondeg_of_pd _ hpW) star_algebraMap_ringOfIntegers_mem_range`.

Establish `horth : ∀ (u : U) (w : perp h U), h (u : V) (w : V) = 0` using `fun u w => (Witt.mem_perp h U w).1 w.2 u u.2`. Establish `hdec : ∀ v : V, ∃ (u : U) (w : perp h U), v = u + w`. Introduce `v`. Establish `hv : v ∈ U ⊔ perp h U` using `by rw [hc.sup_eq_top]; trivial`. Take `⟨u, hu, w, hw, e⟩` from `Submodule.mem_sup.1 hv`.

Conclude with `⟨⟨u, hu⟩, ⟨w, hw⟩, e.symm⟩`. Establish `hg : ∀ C : Submodule (𝓞 K) (perp h U), ∃ y : perp h U, B ≤ C → C.FG → C = B ⊔ Submodule.span (𝓞 K) {y}`. Introduce `C`. Distinguish the cases in `hh : B ≤ C ∧ C.FG`. Take `⟨y, hy⟩` from `exists_gen h1 hB.1 hh.1 hh.2`.

Conclude with `⟨y, fun _ _ => hy⟩`. Conclude with `⟨0, fun a b => absurd ⟨a, b⟩ hh⟩`. Use `choose g hg using hg`. Use `set Ad : Submodule (𝓞 K) U := dual (hRes h U) A with hAd`. Set `M : Submodule (𝓞 K) V` to `A.map (U.subtype.restrictScalars (𝓞 K)) ⊔ B.map ((perp h U).subtype.restrictScalars (𝓞 K))`.

Set `Φ : Submodule (𝓞 K) (perp h U) × (Ad ⧸ A.comap Ad.subtype) → Submodule (𝓞 K) V` to `fun p => M ⊔ Submodule.span (𝓞 K) {(((Quotient.out p.2 : Ad) : U) : V) + (g (dual (hRes h (perp h U)) p.1) : V)}`. Set `S : Set (Submodule (𝓞 K) (perp h U))` to `{C | B ≤ C ∧ ∀ x ∈ C, T • x ∈ B}`. Establish `hsub : {L : Submodule (𝓞 K) V | IsIntLat h L ∧ (∀ x ∈ dual h L, T • x ∈ L) ∧ latIn U L = A ∧ latIn (perp h U) L = B} ⊆ Φ '' (S ×ˢ Set.univ)`. Introduce and unpack `L ⟨hL, hTL, hLA, hLB⟩`. Establish `mA : ∀ u : U, u ∈ A ↔ (u : V) ∈ L` using `fun u => by rw [← hLA]; rfl`.

Establish `mB : ∀ w : perp h U, w ∈ B ↔ (w : V) ∈ L` using `fun w => by rw [← hLB]; rfl`. Set `π : V →ₗ[𝓞 K] perp h U` to `(Submodule.projectionOnto (perp h U) U hc.symm).restrictScalars (𝓞 K)`. Establish `hπ : ∀ (u : U) (w : perp h U), π ((u : V) + (w : V)) = w`. Introduce `u w`. Simplify using `only [π, LinearMap.restrictScalars_apply, map_add]`.

Rewrite using `[Submodule.projectionOnto_apply_right, Submodule.projectionOnto_apply_left, zero_add]`. Use `set B' := L.map π with hB'`. Establish `mB' : ∀ w : perp h U, w ∈ B' ↔ ∃ u : U, (u : V) + (w : V) ∈ L`. Introduce `w`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨v, hv, rfl⟩`. Take `⟨u, w, rfl⟩` from `hdec v`. Conclude with `⟨u, by rw [hπ]; exact hv⟩`. Introduce and unpack `⟨u, hu⟩`. Conclude with `⟨_, hu, hπ u w⟩`.

Establish `hBB' : B ≤ B'` using `fun w hw => (mB' w).2 ⟨0, by simpa using (mB w).1 hw⟩`. Establish `hB'fg : B'.FG` using `hL.1.fg.map π`. Establish `hB'l : Submodule.IsLattice K B'` using `haveI := hB.1 Submodule.IsLattice.of_le_of_isLattice_of_fg K hBB' hB'fg`. Establish `mC : ∀ x : perp h U, x ∈ dual (hRes h (perp h U)) B' ↔ (x : V) ∈ dual h L`. Introduce `x`.

Rewrite using `[dualBasic_mem_dual, dualBasic_mem_dual]`. Prove the components needed by the constructor for the conclusion. Introduce `H v hv`. Take `⟨u, w, rfl⟩` from `hdec v`. Use `H w ((mB' w).2 ⟨u, hv⟩)` as an intermediate fact.

Rewrite using `[map_add, LinearMap.add_apply, horth, zero_add]`. Conclude with `this`. Introduce `H w hw`. Take `⟨u, hu⟩` from `(mB' w).1 hw`. Use `H _ hu` as an intermediate fact.

Rewrite `this` using `[map_add, LinearMap.add_apply, horth, zero_add]`. Conclude with `this`. Establish `hgen` using `hg B' hBB' hB'fg`. Take `⟨a, ha⟩` from `(mB' (g B')).1 (hgen.ge (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))`. Establish `haA : a ∈ Ad`.

Rewrite using `[hAd, dualBasic_mem_dual]`. Introduce `u hu`. Use `hL.2 _ ((mA u).1 hu) _ ha` as an intermediate fact. Rewrite `this` using `[map_add, horth, add_zero]`. Conclude with `this`.

Use `⟨(dual (hRes h (perp h U)) B', Submodule.Quotient.mk ⟨a, haA⟩), ⟨⟨?_, ?_⟩, trivial⟩, ?_⟩` and prove the remaining obligations. Introduce `w hw`. Rewrite using `[mC, dualBasic_mem_dual]`. Conclude with `fun v hv => hL.2 v hv _ ((mB w).1 hw)`. Introduce `x hx`.

Rewrite using `[mB]`. Conclude with `hTL _ ((mC x).1 hx)`. Establish `hML : M ≤ L`. Use `sup_le ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, hu, rfl⟩`.

Conclude with `(mA u).1 hu`. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Conclude with `(mB u).1 hu`. Establish `e1 : L = M ⊔ Submodule.span (𝓞 K) {(a : V) + (g B' : V)}`. Use `le_antisymm ?_ (sup_le hML ((Submodule.span_singleton_le_iff_mem _ _).2 ha))` and prove the remaining obligations.

Introduce `v hv`. Take `⟨u, w, rfl⟩` from `hdec v`. Take `⟨b, hb, z, hz, rfl⟩` from `Submodule.mem_sup.1 (hgen.le ((mB' w).2 ⟨u, hv⟩))`. Take `⟨r, rfl⟩` from `Submodule.mem_span_singleton.1 hz`. Establish `e : (u : V) + ((b + r • g B' : perp h U) : V) = (((u - r • a : U) : V) + (b : V)) + r • ((a : V) + (g B' : V))`.

Simplify using `only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul_of_tower, smul_add]`. Normalize the expressions using the abelian group laws. Establish `hu : u - r • a ∈ A`. Rewrite using `[mA]`. Use `sub_mem (sub_mem hv (L.smul_mem r ha)) ((mB b).1 hb)` as an intermediate fact.

Rewrite `this` using `[e]`. Simplify using `using this`. Rewrite using `[e]`. Conclude with `add_mem (Submodule.mem_sup_left (add_mem (Submodule.mem_sup_left ⟨_, hu, rfl⟩) (Submodule.mem_sup_right ⟨_, hb, rfl⟩))) (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))`. Simplify using `only [Φ]`.

Rewrite using `[(dl B' hB'l).2.1, e1]`. Apply `sup_span_congr` to reduce the goal to its premises. Establish `hq : Quotient.out (Submodule.Quotient.mk ⟨a, haA⟩ : Ad ⧸ A.comap Ad.subtype) - ⟨a, haA⟩ ∈ A.comap Ad.subtype`. Rewrite using `[← Submodule.Quotient.eq]`. Conclude with `Submodule.Quotient.mk_out _`.

Rewrite using `[add_sub_add_right_eq_sub]`. Conclude with `Submodule.mem_sup_left ⟨_, hq, rfl⟩`. Establish `hcard : Nat.card (Ad ⧸ A.comap Ad.subtype) = discN (hRes h U) A` using `rfl`. Establish `: Finite (Ad ⧸ A.comap Ad.subtype)` using `Nat.finite_of_card_ne_zero (by rwa [hcard])`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Set.encard_prod, Set.encard_univ, ENat.card_eq_coe_natCard, hcard]`. Use `_ ≤ _ := by`. Rewrite using `[Nat.cast_mul]`. Use `gcongr`. Conclude with `encard_between h1 hB.1 T hT`.
-/
theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ (U : Submodule K V) (A : Submodule (𝓞 K) U) (B : Submodule (𝓞 K) (perp h U)) (T : 𝓞 K), T ≠ 0 → Module.finrank K (perp h U) = 1 → IsIntLat (hRes h U) A → IsIntLat (hRes h (perp h U)) B → {L : Submodule (𝓞 K) V | IsIntLat h L ∧ (∀ x ∈ dual h L, T • x ∈ L) ∧ latIn U L = A ∧ latIn (perp h U) L = B}.encard ≤ ((Ideal.absNorm (Ideal.span {T}) * discN (hRes h U) A : ℕ) : ℕ∞) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hpd U A B T hT h1 hA hB
  obtain ⟨hc, hsU, hpU, -⟩ := (Witt.witt_definite K V h hK hs hpd).2 U
  obtain ⟨-, hsW, hpW, -⟩ := (Witt.witt_definite K V h hK hs hpd).2 (perp h U)
  have hd0 : discN (hRes h U) A ≠ 0 :=
    (DiscOrder.main K U (hRes h U) hK hsU (nondeg_of_pd _ hpU) A hA).1
  have dl := dualLattice (𝓞 K) K (perp h U) (hRes h (perp h U)) hsW (nondeg_of_pd _ hpW)
    star_algebraMap_ringOfIntegers_mem_range
  have horth : ∀ (u : U) (w : perp h U), h (u : V) (w : V) = 0 :=
    fun u w => (Witt.mem_perp h U w).1 w.2 u u.2
  have hdec : ∀ v : V, ∃ (u : U) (w : perp h U), v = u + w := by
    intro v
    have hv : v ∈ U ⊔ perp h U := by rw [hc.sup_eq_top]; trivial
    obtain ⟨u, hu, w, hw, e⟩ := Submodule.mem_sup.1 hv
    exact ⟨⟨u, hu⟩, ⟨w, hw⟩, e.symm⟩

  have hg : ∀ C : Submodule (𝓞 K) (perp h U), ∃ y : perp h U, B ≤ C → C.FG →
      C = B ⊔ Submodule.span (𝓞 K) {y} := by
    intro C
    by_cases hh : B ≤ C ∧ C.FG
    · obtain ⟨y, hy⟩ := exists_gen h1 hB.1 hh.1 hh.2
      exact ⟨y, fun _ _ => hy⟩
    · exact ⟨0, fun a b => absurd ⟨a, b⟩ hh⟩
  choose g hg using hg
  set Ad : Submodule (𝓞 K) U := dual (hRes h U) A with hAd
  let M : Submodule (𝓞 K) V := A.map (U.subtype.restrictScalars (𝓞 K)) ⊔
    B.map ((perp h U).subtype.restrictScalars (𝓞 K))
  let Φ : Submodule (𝓞 K) (perp h U) × (Ad ⧸ A.comap Ad.subtype) → Submodule (𝓞 K) V := fun p =>
    M ⊔ Submodule.span (𝓞 K) {(((Quotient.out p.2 : Ad) : U) : V) +
      (g (dual (hRes h (perp h U)) p.1) : V)}
  let S : Set (Submodule (𝓞 K) (perp h U)) := {C | B ≤ C ∧ ∀ x ∈ C, T • x ∈ B}
  have hsub : {L : Submodule (𝓞 K) V | IsIntLat h L ∧ (∀ x ∈ dual h L, T • x ∈ L) ∧
      latIn U L = A ∧ latIn (perp h U) L = B} ⊆ Φ '' (S ×ˢ Set.univ) := by
    rintro L ⟨hL, hTL, hLA, hLB⟩
    have mA : ∀ u : U, u ∈ A ↔ (u : V) ∈ L := fun u => by rw [← hLA]; rfl
    have mB : ∀ w : perp h U, w ∈ B ↔ (w : V) ∈ L := fun w => by rw [← hLB]; rfl
    let π : V →ₗ[𝓞 K] perp h U :=
      (Submodule.projectionOnto (perp h U) U hc.symm).restrictScalars (𝓞 K)
    have hπ : ∀ (u : U) (w : perp h U), π ((u : V) + (w : V)) = w := by
      intro u w
      simp only [π, LinearMap.restrictScalars_apply, map_add]
      rw [Submodule.projectionOnto_apply_right, Submodule.projectionOnto_apply_left, zero_add]
    set B' := L.map π with hB'
    have mB' : ∀ w : perp h U, w ∈ B' ↔ ∃ u : U, (u : V) + (w : V) ∈ L := by
      intro w
      constructor
      · rintro ⟨v, hv, rfl⟩
        obtain ⟨u, w, rfl⟩ := hdec v
        exact ⟨u, by rw [hπ]; exact hv⟩
      · rintro ⟨u, hu⟩
        exact ⟨_, hu, hπ u w⟩
    have hBB' : B ≤ B' := fun w hw => (mB' w).2 ⟨0, by simpa using (mB w).1 hw⟩
    have hB'fg : B'.FG := hL.1.fg.map π
    have hB'l : Submodule.IsLattice K B' :=
      haveI := hB.1
      Submodule.IsLattice.of_le_of_isLattice_of_fg K hBB' hB'fg
    have mC : ∀ x : perp h U, x ∈ dual (hRes h (perp h U)) B' ↔ (x : V) ∈ dual h L := by
      intro x
      rw [dualBasic_mem_dual, dualBasic_mem_dual]
      constructor
      · intro H v hv
        obtain ⟨u, w, rfl⟩ := hdec v
        have := H w ((mB' w).2 ⟨u, hv⟩)
        rw [map_add, LinearMap.add_apply, horth, zero_add]
        exact this
      · intro H w hw
        obtain ⟨u, hu⟩ := (mB' w).1 hw
        have := H _ hu
        rw [map_add, LinearMap.add_apply, horth, zero_add] at this
        exact this
    have hgen := hg B' hBB' hB'fg
    obtain ⟨a, ha⟩ := (mB' (g B')).1
      (hgen.ge (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
    have haA : a ∈ Ad := by
      rw [hAd, dualBasic_mem_dual]
      intro u hu
      have := hL.2 _ ((mA u).1 hu) _ ha
      rw [map_add, horth, add_zero] at this
      exact this
    refine ⟨(dual (hRes h (perp h U)) B', Submodule.Quotient.mk ⟨a, haA⟩), ⟨⟨?_, ?_⟩, trivial⟩, ?_⟩
    · intro w hw
      rw [mC, dualBasic_mem_dual]
      exact fun v hv => hL.2 v hv _ ((mB w).1 hw)
    · intro x hx
      rw [mB]
      exact hTL _ ((mC x).1 hx)
    · have hML : M ≤ L := by
        refine sup_le ?_ ?_
        · rintro _ ⟨u, hu, rfl⟩; exact (mA u).1 hu
        · rintro _ ⟨u, hu, rfl⟩; exact (mB u).1 hu
      have e1 : L = M ⊔ Submodule.span (𝓞 K) {(a : V) + (g B' : V)} := by
        refine le_antisymm ?_ (sup_le hML ((Submodule.span_singleton_le_iff_mem _ _).2 ha))
        intro v hv
        obtain ⟨u, w, rfl⟩ := hdec v
        obtain ⟨b, hb, z, hz, rfl⟩ := Submodule.mem_sup.1 (hgen.le ((mB' w).2 ⟨u, hv⟩))
        obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hz
        have e : (u : V) + ((b + r • g B' : perp h U) : V) =
            (((u - r • a : U) : V) + (b : V)) + r • ((a : V) + (g B' : V)) := by
          simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul_of_tower, smul_add]
          abel
        have hu : u - r • a ∈ A := by
          rw [mA]
          have := sub_mem (sub_mem hv (L.smul_mem r ha)) ((mB b).1 hb)
          rw [e] at this
          simpa using this
        rw [e]
        exact add_mem (Submodule.mem_sup_left (add_mem (Submodule.mem_sup_left ⟨_, hu, rfl⟩)
          (Submodule.mem_sup_right ⟨_, hb, rfl⟩)))
          (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
      simp only [Φ]
      rw [(dl B' hB'l).2.1, e1]
      apply sup_span_congr
      have hq : Quotient.out (Submodule.Quotient.mk ⟨a, haA⟩ : Ad ⧸ A.comap Ad.subtype) - ⟨a, haA⟩ ∈
          A.comap Ad.subtype := by
        rw [← Submodule.Quotient.eq]
        exact Submodule.Quotient.mk_out _
      rw [add_sub_add_right_eq_sub]
      exact Submodule.mem_sup_left ⟨_, hq, rfl⟩
  have hcard : Nat.card (Ad ⧸ A.comap Ad.subtype) = discN (hRes h U) A := rfl
  have : Finite (Ad ⧸ A.comap Ad.subtype) := Nat.finite_of_card_ne_zero (by rwa [hcard])
  calc _ ≤ (Φ '' (S ×ˢ Set.univ)).encard := Set.encard_le_encard hsub
    _ ≤ (S ×ˢ (Set.univ : Set (Ad ⧸ A.comap Ad.subtype))).encard := Set.encard_image_le _ _
    _ = S.encard * (discN (hRes h U) A : ℕ) := by
      rw [Set.encard_prod, Set.encard_univ, ENat.card_eq_coe_natCard, hcard]
    _ ≤ _ := by
      rw [Nat.cast_mul]
      gcongr
      exact encard_between h1 hB.1 T hT

end GlobalTheory.Mass.LineGlue
