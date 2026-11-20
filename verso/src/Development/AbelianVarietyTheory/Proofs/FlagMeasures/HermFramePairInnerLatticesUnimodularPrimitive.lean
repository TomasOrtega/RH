import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocalizedModuleSubtype
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.InnerLat

open GlobalTheory.UnimodQuot

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] in

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_smul_mem hΛ v`. Use `⟨algebraMap (𝓞 K) K s, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2, ?_⟩` and prove the remaining obligations. Rewrite using `[algebraMap_smul]`. Conclude with `hs`.
-/
theorem exists_mult {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ) (v : V) :
    ∃ c : K, c ≠ 0 ∧ c • v ∈ Λ := by
  obtain ⟨s, hs⟩ := exists_smul_mem hΛ v
  refine ⟨algebraMap (𝓞 K) K s, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2, ?_⟩
  rw [algebraMap_smul]
  exact hs

/- English proof (translation)
Establish `hΛ` using `(isLatMod_top_bot_iff Λ).1 hU.1`. Take `⟨⟨⟨N, hN, hNe⟩, hsp⟩, hd⟩` from `isUnimodMod_quot H hU hX`. Establish `hXp : X ≤ perp H X` using `fun x hx => (mem_perp_iff H X x).2 (hX x hx)`. Use `set M := (Λ ⊓ rs (𝓞 K) (perp H X)) ⊔ rs (𝓞 K) X with hM`. Use `set L := rs (𝓞 K) U ⊓ (Λ ⊔ rs (𝓞 K) X) with hL`.

Establish `hMp : ∀ m ∈ M, m ∈ perp H X` using `fun m hm => hsp ▸ Submodule.subset_span hm`. Establish `hLM : L ≤ M`. Introduce and unpack `y ⟨hyU, hy⟩`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hy`. Use `Submodule.add_mem_sup ⟨ha, ?_⟩ hb` and prove the remaining obligations.

Use `(perp H X).sub_mem (hUX hyU) (hXp hb)` as an intermediate fact. Simplify using `using this`. Establish `hML : ∀ m ∈ M, m ∈ U → m ∈ L` using `fun m hm hmU => ⟨hmU, (sup_le_sup_right inf_le_left _ : M ≤ Λ ⊔ rs (𝓞 K) X) hm⟩`. Establish `hdec : ∀ m ∈ M, ∃ l ∈ L, m - l ∈ X`. Introduce `m hm`.

Take `⟨u, hu, x, hx, rfl⟩` from `Submodule.mem_sup.1 (h1 (hMp m hm))`. Use `⟨u, hML u ?_ hu, by simpa using hx⟩` and prove the remaining obligations. Use `M.sub_mem hm (Submodule.mem_sup_right (show x ∈ rs (𝓞 K) X from hx))` as an intermediate fact. Simplify using `using this`. Establish `hspan : Submodule.span K (L : Set V) = U`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Conclude with `fun y hy => hy.1`. Introduce `v hv`. Take `⟨c, hc, h⟩` from `exists_mult hΛ v`.

Rewrite using `[← Submodule.smul_mem_iff _ hc]`. Conclude with `Submodule.subset_span ⟨U.smul_mem c hv, Submodule.mem_sup_left h⟩`. Use `⟨⟨?_, hspan⟩, ?_⟩` and prove the remaining obligations. Take `⟨s, rfl⟩` from `hN`. Establish `hs : ∀ m : s, ∃ l ∈ L, (m : V) - l ∈ X` using `fun m => hdec m (hNe ▸ Submodule.mem_sup_left (Submodule.subset_span m.2))`.

Use `choose f hf hfX using hs`. Establish `hfL : Submodule.span (𝓞 K) (Set.range f) ≤ L`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨m, rfl⟩`. Conclude with `hf m`.

Establish `hle : M ≤ Submodule.span (𝓞 K) (Set.range f) ⊔ rs (𝓞 K) X`. Rewrite using `[hNe]`. Use `sup_le ?_ le_sup_right` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce `m hm`.

Conclude with `Submodule.mem_sup.2 ⟨f ⟨m, hm⟩, Submodule.subset_span ⟨_, rfl⟩, _, hfX ⟨m, hm⟩, by abel⟩`. Use `⟨Submodule.span (𝓞 K) (Set.range f), Submodule.fg_span (Set.finite_range f), le_antisymm ?_ ?_⟩` and prove the remaining obligations. Introduce `y hy`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 (hle (hLM hy))`. Use `Submodule.add_mem_sup ha (show b ∈ I from h2 ▸ ⟨?_, hb⟩)` and prove the remaining obligations.

Use `U.sub_mem hy.1 (hfL ha).1` as an intermediate fact. Simplify using `using this`. Use `sup_le hfL fun x hx => ?_` and prove the remaining obligations. Establish `hx' : x ∈ U ⊓ X` using `h2 ▸ hx`. Conclude with `⟨hx'.1, Submodule.mem_sup_right hx'.2⟩`.

Use extensionality with `y`. Rewrite using `[mem_dual_iff, hspan]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hy, h⟩`. Use `hML y ?_ hy` and prove the remaining obligations.

Rewrite using `[← hd, mem_dual_iff, hsp]`. Use `⟨hUX hy, fun m hm => ?_⟩` and prove the remaining obligations. Take `⟨l, hl, hx⟩` from `hdec m hm`. Establish `h0` using `(mem_perp_iff H X y).1 (hUX hy) _ hx`. Rewrite `h0` using `[map_sub, sub_eq_zero]`.

Rewrite using `[h0]`. Conclude with `h l hl`. Introduce `hy`. Use `hLM hy` as an intermediate fact. Rewrite `this` using `[← hd, mem_dual_iff]`.

Conclude with `⟨hy.1, fun x hx => this.2 x (hLM hx)⟩`.
-/
theorem unimod_transfer [FiniteDimensional K V] (H : HermSpace K V) {Λ : Submodule (𝓞 K) V} (hU : IsUnimod H Λ)
    {X U I : Submodule K V} (hX : ∀ x ∈ X, ∀ y ∈ X, H.B x y = 0) (hUX : U ≤ perp H X)
    (h1 : perp H X ≤ U ⊔ X) (h2 : U ⊓ X = I) :
    IsUnimodMod H (rs (𝓞 K) U ⊓ (Λ ⊔ rs (𝓞 K) X)) U I := by
  have hΛ := (isLatMod_top_bot_iff Λ).1 hU.1
  obtain ⟨⟨⟨N, hN, hNe⟩, hsp⟩, hd⟩ := isUnimodMod_quot H hU hX
  have hXp : X ≤ perp H X := fun x hx => (mem_perp_iff H X x).2 (hX x hx)
  set M := (Λ ⊓ rs (𝓞 K) (perp H X)) ⊔ rs (𝓞 K) X with hM
  set L := rs (𝓞 K) U ⊓ (Λ ⊔ rs (𝓞 K) X) with hL
  have hMp : ∀ m ∈ M, m ∈ perp H X := fun m hm => hsp ▸ Submodule.subset_span hm
  have hLM : L ≤ M := by
    rintro y ⟨hyU, hy⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
    refine Submodule.add_mem_sup ⟨ha, ?_⟩ hb
    have := (perp H X).sub_mem (hUX hyU) (hXp hb)
    simpa using this
  have hML : ∀ m ∈ M, m ∈ U → m ∈ L := fun m hm hmU =>
    ⟨hmU, (sup_le_sup_right inf_le_left _ : M ≤ Λ ⊔ rs (𝓞 K) X) hm⟩
  have hdec : ∀ m ∈ M, ∃ l ∈ L, m - l ∈ X := by
    intro m hm
    obtain ⟨u, hu, x, hx, rfl⟩ := Submodule.mem_sup.1 (h1 (hMp m hm))
    refine ⟨u, hML u ?_ hu, by simpa using hx⟩
    have := M.sub_mem hm (Submodule.mem_sup_right (show x ∈ rs (𝓞 K) X from hx))
    simpa using this
  have hspan : Submodule.span K (L : Set V) = U := by
    apply le_antisymm
    · rw [Submodule.span_le]
      exact fun y hy => hy.1
    · intro v hv
      obtain ⟨c, hc, h⟩ := exists_mult hΛ v
      rw [← Submodule.smul_mem_iff _ hc]
      exact Submodule.subset_span ⟨U.smul_mem c hv, Submodule.mem_sup_left h⟩
  refine ⟨⟨?_, hspan⟩, ?_⟩
  · obtain ⟨s, rfl⟩ := hN
    have hs : ∀ m : s, ∃ l ∈ L, (m : V) - l ∈ X := fun m =>
      hdec m (hNe ▸ Submodule.mem_sup_left (Submodule.subset_span m.2))
    choose f hf hfX using hs
    have hfL : Submodule.span (𝓞 K) (Set.range f) ≤ L := by
      rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      exact hf m
    have hle : M ≤ Submodule.span (𝓞 K) (Set.range f) ⊔ rs (𝓞 K) X := by
      rw [hNe]
      refine sup_le ?_ le_sup_right
      rw [Submodule.span_le]
      intro m hm
      exact Submodule.mem_sup.2 ⟨f ⟨m, hm⟩, Submodule.subset_span ⟨_, rfl⟩, _, hfX ⟨m, hm⟩, by abel⟩
    refine ⟨Submodule.span (𝓞 K) (Set.range f), Submodule.fg_span (Set.finite_range f), le_antisymm ?_ ?_⟩
    · intro y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hle (hLM hy))
      refine Submodule.add_mem_sup ha (show b ∈ I from h2 ▸ ⟨?_, hb⟩)
      have := U.sub_mem hy.1 (hfL ha).1
      simpa using this
    · refine sup_le hfL fun x hx => ?_
      have hx' : x ∈ U ⊓ X := h2 ▸ hx
      exact ⟨hx'.1, Submodule.mem_sup_right hx'.2⟩
  · ext y
    rw [mem_dual_iff, hspan]
    constructor
    · rintro ⟨hy, h⟩
      refine hML y ?_ hy
      rw [← hd, mem_dual_iff, hsp]
      refine ⟨hUX hy, fun m hm => ?_⟩
      obtain ⟨l, hl, hx⟩ := hdec m hm
      have h0 := (mem_perp_iff H X y).1 (hUX hy) _ hx
      rw [map_sub, sub_eq_zero] at h0
      rw [h0]
      exact h l hl
    · intro hy
      have := hLM hy
      rw [← hd, mem_dual_iff] at this
      exact ⟨hy.1, fun x hx => this.2 x (hLM hx)⟩

section Flag

variable {H : HermSpace K V} {r : ℕ}

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨a, a.2, rfl⟩`.
-/
theorem e_mem_X (F : FlagD H r) (a : Fin r) : F.e a.castSucc ∈ F.X :=
  Submodule.subset_span ⟨a, a.2, rfl⟩

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Establish `: F.X ≤ LinearMap.ker (H.B.flip w)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨b, -, rfl⟩`. Conclude with `hw b`. Conclude with `this`.
-/
theorem X_perp (F : FlagD H r) {w : V} (hw : ∀ a : Fin r, H.B (F.e a.castSucc) w = 0) :
    ∀ x ∈ F.X, H.B x w = 0 := by
  have : F.X ≤ LinearMap.ker (H.B.flip w) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, -, rfl⟩
    exact hw b
  exact this

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Introduce `x hx y hy` and use `X_perp F (fun a => by rw [← H.herm, X_perp F (fun b => F.iso b a) y hy, star_zero]) x hx`.
-/
theorem X_iso (F : FlagD H r) : ∀ x ∈ F.X, ∀ y ∈ F.X, H.B x y = 0 := fun x hx y hy =>
  X_perp F (fun a => by rw [← H.herm, X_perp F (fun b => F.iso b a) y hy, star_zero]) x hx

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Introduce `x hx` and use `by rw [← H.herm] exact star_eq_zero.2 (X_perp F F.zperp x hx)`.
-/
theorem z_X (F : FlagD H r) : ∀ x ∈ F.X, H.B F.z x = 0 := fun x hx => by
  rw [← H.herm]
  exact star_eq_zero.2 (X_perp F F.zperp x hx)

/- English proof (translation)
Use `⟨unimod_transfer H hU (X_iso F) (fun y hy => ?_) (fun w hw => ?_) ?_, fun t => ?_⟩` and prove the remaining obligations. Rewrite `hy`, the goal using `[mem_perp_iff]`. Conclude with `fun x hx => hy x (hXS hx)`. Rewrite `hw` using `[mem_perp_iff]`. Establish `hzz : H.B F.z F.z ≠ 0`.

Rewrite using `[show H.B F.z F.z = -F.T from F.zz]`. Conclude with `neg_ne_zero.2 F.hT`. Take `⟨x, hx, h⟩` from `hs (w - (H.B w F.z / H.B F.z F.z) • F.z) (fun a => by`. Rewrite using `[← H.herm, star_eq_zero, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]`. Use `Fin.lastCases ?_ (fun b => ?_) a` and prove the remaining obligations.

Use `show H.B w F.z - _ * H.B F.z F.z = 0`. Rewrite using `[div_mul_cancel₀ _ hzz, sub_self]`. Rewrite using `[hw _ (e_mem_X F b), z_X F _ (e_mem_X F b)] simp)`. Establish `h' : w - (H.B w F.z / H.B F.z F.z) • F.z - x ∈ perp H S`. Rewrite using `[mem_perp_iff]`.

Introduce `v hv`. Rewrite using `[← H.herm, h v (Submodule.mem_sup_left hv), star_zero]`. Use `Submodule.mem_sup.2 ⟨_, (perp H S).add_mem h' ((perp H S).smul_mem (H.B w F.z / H.B F.z F.z) hz), x, hx, by abel⟩` and prove the remaining obligations. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hp, hx⟩`. Use `(hI x hx).1 fun w hw => ?_` and prove the remaining obligations. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hw`. Establish `e1 : H.B a x = 0` using `by rw [← H.herm, (mem_perp_iff H S x).1 hp a ha, star_zero]`. Establish `e2 : H.B b x = 0` using `(mem_perp_iff H S b).1 (hZ b hb) x (hXS hx)`.

Rewrite using `[map_add, LinearMap.add_apply, e1, e2, add_zero]`. Introduce `hx`. Use `⟨(mem_perp_iff H S x).2 fun v hv => ?_, hIX hx⟩` and prove the remaining obligations. Rewrite using `[← H.herm, (hI x (hIX hx)).2 hx v (Submodule.mem_sup_left hv), star_zero]`. Rewrite using `[← hlead]`.

Conclude with `⟨fun h => h.2, fun h => ⟨(perp H S).smul_mem t hz, h⟩⟩`.
-/
theorem inner [FiniteDimensional K V] (F : FlagD H r) {Λ : Submodule (𝓞 K) V} (hU : IsUnimod H Λ)
    (hlead : lead F Λ (Fin.last r) = 1) {S Z I : Submodule K V} (hXS : F.X ≤ S) (hz : F.z ∈ perp H S)
    (hZ : ∀ z ∈ Z, z ∈ perp H S)
    (hI : ∀ x ∈ F.X, (∀ w ∈ S ⊔ Z, H.B w x = 0) ↔ x ∈ I) (hIX : I ≤ F.X)
    (hs : ∀ w : V, (∀ a : Fin (r + 1), H.B (F.e a) w = 0) → ∃ x ∈ F.X, ∀ v ∈ S ⊔ Z, H.B v (w - x) = 0) :
    IsUnimodMod H (rs (𝓞 K) (perp H S) ⊓ (Λ ⊔ rs (𝓞 K) F.X)) (perp H S) I ∧
      ∀ t : K, t • F.z ∈ rs (𝓞 K) (perp H S) ⊓ (Λ ⊔ rs (𝓞 K) F.X) ↔ t ∈ (1 : Submodule (𝓞 K) K) := by
  refine ⟨unimod_transfer H hU (X_iso F) (fun y hy => ?_) (fun w hw => ?_) ?_, fun t => ?_⟩
  · rw [mem_perp_iff] at hy ⊢
    exact fun x hx => hy x (hXS hx)
  · rw [mem_perp_iff] at hw
    have hzz : H.B F.z F.z ≠ 0 := by
      rw [show H.B F.z F.z = -F.T from F.zz]
      exact neg_ne_zero.2 F.hT
    obtain ⟨x, hx, h⟩ := hs (w - (H.B w F.z / H.B F.z F.z) • F.z) (fun a => by
      rw [← H.herm, star_eq_zero, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      refine Fin.lastCases ?_ (fun b => ?_) a
      · show H.B w F.z - _ * H.B F.z F.z = 0
        rw [div_mul_cancel₀ _ hzz, sub_self]
      · rw [hw _ (e_mem_X F b), z_X F _ (e_mem_X F b)]
        simp)
    have h' : w - (H.B w F.z / H.B F.z F.z) • F.z - x ∈ perp H S := by
      rw [mem_perp_iff]
      intro v hv
      rw [← H.herm, h v (Submodule.mem_sup_left hv), star_zero]
    refine Submodule.mem_sup.2 ⟨_, (perp H S).add_mem h' ((perp H S).smul_mem (H.B w F.z / H.B F.z F.z) hz), x, hx,
      by abel⟩
  · ext x
    constructor
    · rintro ⟨hp, hx⟩
      refine (hI x hx).1 fun w hw => ?_
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
      have e1 : H.B a x = 0 := by rw [← H.herm, (mem_perp_iff H S x).1 hp a ha, star_zero]
      have e2 : H.B b x = 0 := (mem_perp_iff H S b).1 (hZ b hb) x (hXS hx)
      rw [map_add, LinearMap.add_apply, e1, e2, add_zero]
    · intro hx
      refine ⟨(mem_perp_iff H S x).2 fun v hv => ?_, hIX hx⟩
      rw [← H.herm, (hI x (hIX hx)).2 hx v (Submodule.mem_sup_left hv), star_zero]
  · rw [← hlead]
    exact ⟨fun h => h.2, fun h => ⟨(perp H S).smul_mem t hz, h⟩⟩

omit [StarRing K] in
/- English proof (translation)
Simplify using `[line]`.
-/
theorem mem_line {A : Submodule (𝓞 K) K} {v x : V} : x ∈ line A v ↔ ∃ a ∈ A, a • v = x := by
  simp [line]

omit [StarRing K] in
/- English proof (translation)
Introduce `x hx`. Take `⟨a, -, rfl⟩` from `mem_line.1 hx`. Conclude with `S.smul_mem a hv`.
-/
theorem line_le {A : Submodule (𝓞 K) K} {v : V} {S : Submodule K V} (hv : v ∈ S) : line A v ≤ rs (𝓞 K) S := by
  intro x hx
  obtain ⟨a, -, rfl⟩ := mem_line.1 hx
  exact S.smul_mem a hv

omit [StarRing K] in
/- English proof (translation)
Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hA`. Rewrite using `[← Submodule.smul_mem_iff _ ha0]`. Conclude with `Submodule.subset_span (h (mem_line.2 ⟨a, ha, rfl⟩))`.
-/
theorem mem_span_of_line {A : Submodule (𝓞 K) K} (hA : A ≠ ⊥) {v : V} {P : Submodule (𝓞 K) V}
    (h : line A v ≤ P) : v ∈ Submodule.span K (P : Set V) := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA
  rw [← Submodule.smul_mem_iff _ ha0]
  exact Submodule.subset_span (h (mem_line.2 ⟨a, ha, rfl⟩))

omit [StarRing K] in
/- English proof (translation)
Unfold `ipow`. Rewrite using `[Ne, FractionalIdeal.coeToSubmodule_eq_bot]`. Conclude with `zpow_ne_zero n (FractionalIdeal.coeIdeal_ne_zero.2 h)`.
-/
theorem ipow_ne_bot {𝔡 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥) (n : ℤ) : ipow 𝔡 n ≠ ⊥ := by
  unfold ipow
  rw [Ne, FractionalIdeal.coeToSubmodule_eq_bot]
  exact zpow_ne_zero n (FractionalIdeal.coeIdeal_ne_zero.2 h)

omit [StarRing K] in
/- English proof (translation)
Unfold `ipow`. Conclude with `FractionalIdeal.fg_of_isNoetherianRing le_rfl _`.
-/
theorem ipow_fg (𝔡 : Ideal (𝓞 K)) (n : ℤ) : (ipow 𝔡 n).FG := by
  unfold ipow
  exact FractionalIdeal.fg_of_isNoetherianRing le_rfl _

/- English proof (translation)
Establish `h1 : (1 : Submodule (𝓞 K) K).FG`. Rewrite using `[Submodule.one_eq_span]`. Conclude with `Submodule.fg_span_singleton _`. Conclude with `(((Submodule.fg_iSup _ fun _ => (ipow_fg _ _).map _).sup (Submodule.fg_iSup _ fun _ => Submodule.fg_iSup _ fun _ => (ipow_fg _ _).map _)).sup (h1.map _)).sup (Submodule.fg_iSup _ fun _ => Submodule.fg_iSup _ fun _ => (ipow_fg _ _).map _)`.
-/
theorem hermFramePairNormalForm_baseLattice_fg (N : NF H r) : N.P0.FG := by
  have h1 : (1 : Submodule (𝓞 K) K).FG := by
    rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  exact (((Submodule.fg_iSup _ fun _ => (ipow_fg _ _).map _).sup
    (Submodule.fg_iSup _ fun _ => Submodule.fg_iSup _ fun _ => (ipow_fg _ _).map _)).sup (h1.map _)).sup
    (Submodule.fg_iSup _ fun _ => Submodule.fg_iSup _ fun _ => (ipow_fg _ _).map _)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Use `(show N.P0 ≤ rs (𝓞 K) (V0 N.F N.F' ⊔ N.Ist) from sup_le (sup_le (sup_le (iSup_le fun a => line_le ?_) (iSup_le fun a => iSup_le fun _ => line_le ?_)) (line_le ?_)) (iSup_le fun a => iSup_le fun ha => line_le ?_))` and prove the remaining obligations. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (e_mem_X _ a)))`. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right (e_mem_X _ a)))`.

Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span (by simp)))`. Conclude with `Submodule.mem_sup_right (Submodule.subset_span ⟨a, ha, rfl⟩)`. Establish `he : ∀ a : Fin r, N.F.e a.castSucc ∈ Submodule.span K (N.P0 : Set V)` using `fun a => mem_span_of_line (ipow_ne_bot N.𝔡_ne _) (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_iSup (fun a : Fin r => line (N.aa a) (N.F.e a.castSucc)) a))))`. Establish `hz : N.F.z ∈ Submodule.span K (N.P0 : Set V)` using `mem_span_of_line (A := 1) (fun h => one_ne_zero ((Submodule.mem_bot (𝓞 K)).1 (h ▸ Submodule.mem_one.2 ⟨1, map_one _⟩ : (1 : K) ∈ (⊥ : Submodule (𝓞 K) K)))) (le_sup_of_le_left le_sup_right)`. Use `sup_le (sup_le (sup_le ?_ ?_) ?_) ?_` and prove the remaining obligations.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, -, rfl⟩`. Conclude with `he a`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, -, rfl⟩`.

Distinguish the cases in `ha : a.val < N.j`. Conclude with `mem_span_of_line (ipow_ne_bot N.𝔡_ne _) (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right (le_iSup₂_of_le (f := fun (a : Fin r) (_ : a.val < N.j) => line (N.aa a) (N.F'.e a.castSucc)) a ha le_rfl))))`. Use `show N.F'.e a.castSucc ∈ _`. Rewrite using `[N.same _ (by simpa using ha)]`. Conclude with `Submodule.smul_mem _ _ (he a)`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ (rfl | rfl)`. Conclude with `hz`. Use `show N.F'.e (Fin.last r) ∈ _`. Rewrite using `[N.same _ (by simpa using N.j_le)]`.

Conclude with `Submodule.smul_mem _ _ hz`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Conclude with `mem_span_of_line (ipow_ne_bot N.𝔡_ne _) (le_sup_of_le_right (le_iSup₂_of_le (f := fun (a : Fin r) (_ : N.j ≤ a.val) => line (ipow N.𝔡 ((r : ℤ) - a.val)) (N.ist a)) a ha le_rfl))`.
-/
theorem span_hermFramePair_lattice_eq_sup (N : NF H r) : Submodule.span K (N.P0 : Set V) = V0 N.F N.F' ⊔ N.Ist := by
  apply le_antisymm
  · rw [Submodule.span_le]
    refine (show N.P0 ≤ rs (𝓞 K) (V0 N.F N.F' ⊔ N.Ist) from sup_le (sup_le (sup_le (iSup_le fun a => line_le ?_)
      (iSup_le fun a => iSup_le fun _ => line_le ?_)) (line_le ?_)) (iSup_le fun a => iSup_le fun ha => line_le ?_))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (e_mem_X _ a)))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right (e_mem_X _ a)))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, ha, rfl⟩)
  have he : ∀ a : Fin r, N.F.e a.castSucc ∈ Submodule.span K (N.P0 : Set V) := fun a =>
    mem_span_of_line (ipow_ne_bot N.𝔡_ne _) (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
      (le_iSup (fun a : Fin r => line (N.aa a) (N.F.e a.castSucc)) a))))
  have hz : N.F.z ∈ Submodule.span K (N.P0 : Set V) :=
    mem_span_of_line (A := 1) (fun h => one_ne_zero ((Submodule.mem_bot (𝓞 K)).1
      (h ▸ Submodule.mem_one.2 ⟨1, map_one _⟩ : (1 : K) ∈ (⊥ : Submodule (𝓞 K) K)))) (le_sup_of_le_left le_sup_right)
  refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, -, rfl⟩
    exact he a
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, -, rfl⟩
    by_cases ha : a.val < N.j
    · exact mem_span_of_line (ipow_ne_bot N.𝔡_ne _) (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right
        (le_iSup₂_of_le (f := fun (a : Fin r) (_ : a.val < N.j) => line (N.aa a) (N.F'.e a.castSucc)) a ha le_rfl))))
    · show N.F'.e a.castSucc ∈ _
      rw [N.same _ (by simpa using ha)]
      exact Submodule.smul_mem _ _ (he a)
  · refine Submodule.span_le.2 ?_
    rintro _ (rfl | rfl)
    · exact hz
    · show N.F'.e (Fin.last r) ∈ _
      rw [N.same _ (by simpa using N.j_le)]
      exact Submodule.smul_mem _ _ hz
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    exact mem_span_of_line (ipow_ne_bot N.𝔡_ne _) (le_sup_of_le_right
      (le_iSup₂_of_le (f := fun (a : Fin r) (_ : N.j ≤ a.val) => line (ipow N.𝔡 ((r : ℤ) - a.val)) (N.ist a)) a ha le_rfl))

omit [StarRing K] in

/- English proof (translation)
Take `⟨⟨N, hN, rfl⟩, -⟩` from `hL`. Use `Submodule.fg_of_fg_map_of_fg_inf_ker (rs (𝓞 K) I).mkQ ?_ ?_` and prove the remaining obligations. Use `(hN.map (rs (𝓞 K) I).mkQ).of_le ((Submodule.map_mono inf_le_left).trans ?_)` and prove the remaining obligations. Rewrite using `[Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]`. Establish `: (N ⊔ rs (𝓞 K) I) ⊓ rs (𝓞 K) T ⊓ LinearMap.ker (rs (𝓞 K) I).mkQ = ⊥`.

Rewrite using `[eq_bot_iff, Submodule.ker_mkQ]`. Introduce `x hx`. Conclude with `hT x hx.1.2 hx.2`. Rewrite using `[this]`. Conclude with `Submodule.fg_bot`.
-/
theorem fg_inf {L : Submodule (𝓞 K) V} {S I T : Submodule K V} (hL : IsLatMod L S I) (hT : ∀ x ∈ T, x ∈ I → x = 0) :
    (L ⊓ rs (𝓞 K) T).FG := by
  obtain ⟨⟨N, hN, rfl⟩, -⟩ := hL
  refine Submodule.fg_of_fg_map_of_fg_inf_ker (rs (𝓞 K) I).mkQ ?_ ?_
  · refine (hN.map (rs (𝓞 K) I).mkQ).of_le ((Submodule.map_mono inf_le_left).trans ?_)
    rw [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
  · have : (N ⊔ rs (𝓞 K) I) ⊓ rs (𝓞 K) T ⊓ LinearMap.ker (rs (𝓞 K) I).mkQ = ⊥ := by
      rw [eq_bot_iff, Submodule.ker_mkQ]
      intro x hx
      exact hT x hx.1.2 hx.2
    rw [this]
    exact Submodule.fg_bot

end Flag

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ _ H hK r N g Λ _ hT`. Take `⟨hNF, hL, hC, -, hWn, hUp, -, -, -, -, -, hPi⟩` from `GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N`. Take `⟨-, -, -, -, -, hI, hI', hs, hs'⟩` from `hNF`. Establish `hU : IsUnimod H Λ` using `hT.1.1`. Establish `hΛ` using `(isLatMod_top_bot_iff Λ).1 hU.1`.

Establish `hzW : N.F.z ∈ N.Wn`. Rewrite using `[hWn]`. Conclude with `Submodule.mem_sup_right (Submodule.subset_span rfl)`. Establish `hWU : N.Wn ≤ uPerp N.F N.F'` using `by rw [hUp]; exact le_sup_left`. Establish `hz : N.F.z ∈ uPerp N.F N.F'` using `hWU hzW`.

Establish `hz' : N.F'.z ∈ uPerp N.F N.F'` using `by show N.F'.e (Fin.last r) ∈ _`. Rewrite using `[N.same _ (by simpa using N.j_le)]`. Conclude with `Submodule.smul_mem _ _ hz`. Establish `hZ : Submodule.span K {N.F.z, N.F'.z} ≤ uPerp N.F N.F'`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ (rfl | rfl)`. Use `exacts [hz, hz']`. Take `⟨a1, a2⟩` from `inner N.F hU hT.1.2.1.2 le_sup_left hz hZ hI inf_le_left hs`. Take `⟨b1, b2⟩` from `inner N.F' hU hT.1.2.2.2 le_sup_right hz' hZ hI' inf_le_right hs'`. Establish `hsw : latL N.F' N.F Λ = rs (𝓞 K) (perp H (N.F.X ⊔ N.F'.X)) ⊓ (Λ ⊔ rs (𝓞 K) N.F'.X)`.

Rewrite using `[latL, uPerp, sup_comm N.F'.X]`. Establish `hzV : N.F.z ∈ V0 N.F N.F'` using `Submodule.mem_sup_right (Submodule.subset_span (by simp))`. Establish `hdec : ∀ x ∈ N.Wn, ∃ w ∈ N.Wt, ∃ t : K, x = w + t • N.F.z`. Introduce `x hx`. Rewrite `hx` using `[hWn]`.

Take `⟨w, hw, y, hy, rfl⟩` from `Submodule.mem_sup.1 hx`. Take `⟨t, rfl⟩` from `Submodule.mem_span_singleton.1 hy`. Conclude with `⟨w, hw, t, rfl⟩`. Use `⟨a1, hsw ▸ b1, a2, hsw ▸ b2, ⟨(hermFramePairNormalForm_baseLattice_fg N).sup (fg_inf a1.1 fun x hx hxI => ?_), ?_⟩, ?_⟩` and prove the remaining obligations. Take `⟨w, hw, t, rfl⟩` from `hdec x hx`.

Establish `h1` using `z_X N.F _ hxI.1`. Rewrite `h1` using `[map_add, hL.1 w hw _ hzV, zero_add, LinearMap.map_smulₛₗ, show H.B N.F.z N.F.z = -N.F.T from N.F.zz, smul_eq_mul, mul_eq_zero, neg_eq_zero, map_eq_zero]`. Establish `ht : t = 0` using `h1.resolve_right N.F.hT`. Substitute `ht` using the available equality. Rewrite `hxI`, the goal using `[zero_smul, add_zero]`.

Conclude with `(Submodule.mem_bot K).1 (hL.2.1 ▸ ⟨hw, hxI⟩)`. Rewrite using `[eq_top_iff, ← hC.sup_eq_top]`. Use `sup_le (fun w hw => ?_) ?_` and prove the remaining obligations. Take `⟨c, hc, h⟩` from `exists_mult hΛ w`. Establish `hwn : c • w ∈ N.Wn` using `by rw [hWn]; exact Submodule.mem_sup_left (N.Wt.smul_mem c hw)`.

Rewrite using `[← Submodule.smul_mem_iff _ hc]`. Conclude with `Submodule.subset_span (Submodule.mem_sup_right ⟨⟨hWU hwn, Submodule.mem_sup_left h⟩, hwn⟩)`. Rewrite using `[hPi, ← span_hermFramePair_lattice_eq_sup]`. Conclude with `Submodule.span_mono (le_sup_left : N.P0 ≤ N.Ref _)`. Use `le_antisymm ?_ (inf_le_inf_right _ le_sup_left)` and prove the remaining obligations.

Introduce and unpack `x ⟨hx, hxV⟩`. Use `⟨?_, hxV⟩` and prove the remaining obligations. Take `⟨p, hp, l, ⟨hl, hlW⟩, rfl⟩` from `Submodule.mem_sup.1 hx`. Take `⟨w, hw, t, rfl⟩` from `hdec l hlW`. Establish `hVP : V0 N.F N.F' ≤ N.Pi` using `by rw [hPi]; exact le_sup_left`.

Establish `hpP : p ∈ N.Pi` using `by rw [hPi, ← span_hermFramePair_lattice_eq_sup]; exact Submodule.subset_span hp`. Establish `hwP : w ∈ N.Pi`. Use `N.Pi.sub_mem (N.Pi.sub_mem (hVP hxV) hpP) (N.Pi.smul_mem t (hVP hzV))` as an intermediate fact. Simplify using `using this`. Establish `hw0 : w = 0` using `(Submodule.mem_bot K).1 (hC.inf_eq_bot ▸ ⟨hw, hwP⟩)`.

Substitute `hw0` using the available equality. Rewrite `hl`, the goal using `[zero_add]`. Conclude with `N.P0.add_mem hp (Submodule.mem_sup_left (Submodule.mem_sup_right (mem_line.2 ⟨t, (a2 t).1 hl, rfl⟩)))`.
-/
theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → IsUnimodMod H (latL N.F N.F' Λ) (uPerp N.F N.F') (II N.F N.F') ∧ IsUnimodMod H (latL N.F' N.F Λ) (uPerp N.F N.F') (II N.F N.F') ∧ (∀ t : K, t • N.F.z ∈ latL N.F N.F' Λ ↔ t ∈ (1 : Submodule (𝓞 K) K)) ∧ (∀ t : K, t • N.F'.z ∈ latL N.F' N.F Λ ↔ t ∈ (1 : Submodule (𝓞 K) K)) ∧ Submodule.IsLattice K (N.Ref (latL N.F N.F' Λ)) ∧ N.Ref (latL N.F N.F' Λ) ⊓ rs (𝓞 K) (V0 N.F N.F') = N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F') := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ _ hT
  obtain ⟨hNF, hL, hC, -, hWn, hUp, -, -, -, -, -, hPi⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  obtain ⟨-, -, -, -, -, hI, hI', hs, hs'⟩ := hNF
  have hU : IsUnimod H Λ := hT.1.1
  have hΛ := (isLatMod_top_bot_iff Λ).1 hU.1
  have hzW : N.F.z ∈ N.Wn := by
    rw [hWn]; exact Submodule.mem_sup_right (Submodule.subset_span rfl)
  have hWU : N.Wn ≤ uPerp N.F N.F' := by rw [hUp]; exact le_sup_left
  have hz : N.F.z ∈ uPerp N.F N.F' := hWU hzW
  have hz' : N.F'.z ∈ uPerp N.F N.F' := by
    show N.F'.e (Fin.last r) ∈ _
    rw [N.same _ (by simpa using N.j_le)]
    exact Submodule.smul_mem _ _ hz
  have hZ : Submodule.span K {N.F.z, N.F'.z} ≤ uPerp N.F N.F' := by
    refine Submodule.span_le.2 ?_
    rintro _ (rfl | rfl)
    exacts [hz, hz']
  obtain ⟨a1, a2⟩ := inner N.F hU hT.1.2.1.2 le_sup_left hz hZ hI inf_le_left hs
  obtain ⟨b1, b2⟩ := inner N.F' hU hT.1.2.2.2 le_sup_right hz' hZ hI' inf_le_right hs'
  have hsw : latL N.F' N.F Λ = rs (𝓞 K) (perp H (N.F.X ⊔ N.F'.X)) ⊓ (Λ ⊔ rs (𝓞 K) N.F'.X) := by
    rw [latL, uPerp, sup_comm N.F'.X]
  have hzV : N.F.z ∈ V0 N.F N.F' := Submodule.mem_sup_right (Submodule.subset_span (by simp))
  have hdec : ∀ x ∈ N.Wn, ∃ w ∈ N.Wt, ∃ t : K, x = w + t • N.F.z := by
    intro x hx
    rw [hWn] at hx
    obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
    exact ⟨w, hw, t, rfl⟩
  refine ⟨a1, hsw ▸ b1, a2, hsw ▸ b2, ⟨(hermFramePairNormalForm_baseLattice_fg N).sup (fg_inf a1.1 fun x hx hxI => ?_), ?_⟩, ?_⟩
  · obtain ⟨w, hw, t, rfl⟩ := hdec x hx
    have h1 := z_X N.F _ hxI.1
    rw [map_add, hL.1 w hw _ hzV, zero_add, LinearMap.map_smulₛₗ, show H.B N.F.z N.F.z = -N.F.T from N.F.zz,
      smul_eq_mul, mul_eq_zero, neg_eq_zero, map_eq_zero] at h1
    have ht : t = 0 := h1.resolve_right N.F.hT
    subst ht
    rw [zero_smul, add_zero] at hxI ⊢
    exact (Submodule.mem_bot K).1 (hL.2.1 ▸ ⟨hw, hxI⟩)
  · rw [eq_top_iff, ← hC.sup_eq_top]
    refine sup_le (fun w hw => ?_) ?_
    · obtain ⟨c, hc, h⟩ := exists_mult hΛ w
      have hwn : c • w ∈ N.Wn := by rw [hWn]; exact Submodule.mem_sup_left (N.Wt.smul_mem c hw)
      rw [← Submodule.smul_mem_iff _ hc]
      exact Submodule.subset_span (Submodule.mem_sup_right ⟨⟨hWU hwn, Submodule.mem_sup_left h⟩, hwn⟩)
    · rw [hPi, ← span_hermFramePair_lattice_eq_sup]
      exact Submodule.span_mono (le_sup_left : N.P0 ≤ N.Ref _)
  · refine le_antisymm ?_ (inf_le_inf_right _ le_sup_left)
    rintro x ⟨hx, hxV⟩
    refine ⟨?_, hxV⟩
    obtain ⟨p, hp, l, ⟨hl, hlW⟩, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨w, hw, t, rfl⟩ := hdec l hlW
    have hVP : V0 N.F N.F' ≤ N.Pi := by rw [hPi]; exact le_sup_left
    have hpP : p ∈ N.Pi := by rw [hPi, ← span_hermFramePair_lattice_eq_sup]; exact Submodule.subset_span hp
    have hwP : w ∈ N.Pi := by
      have := N.Pi.sub_mem (N.Pi.sub_mem (hVP hxV) hpP) (N.Pi.smul_mem t (hVP hzV))
      simpa using this
    have hw0 : w = 0 := (Submodule.mem_bot K).1 (hC.inf_eq_bot ▸ ⟨hw, hwP⟩)
    subst hw0
    rw [zero_add] at hl ⊢
    exact N.P0.add_mem hp (Submodule.mem_sup_left (Submodule.mem_sup_right (mem_line.2 ⟨t, (a2 t).1 hl, rfl⟩)))

end GlobalTheory.DegCnt.InnerLat
