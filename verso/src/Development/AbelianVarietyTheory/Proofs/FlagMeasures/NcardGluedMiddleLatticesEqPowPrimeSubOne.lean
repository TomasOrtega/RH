import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CyclicDiscriminantLatticesFormOneGenus
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfPerpPerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsForallHomEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace

noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.GlueCount

open Formalism.HermitianLatticesTheory GlobalTheory.Mass.RowPerp

section General

variable {K V W : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W]

def glue (ι : W →ₗ[K] V) (z : V) (T : ℕ) (L : Submodule (𝓞 K) W) (y : W) : Submodule (𝓞 K) V :=
  L.map (ι.restrictScalars (𝓞 K)) ⊔ Submodule.span (𝓞 K) {ι y - (T : K)⁻¹ • z}

def glued (h : V →ₗ⋆[K] V →ₗ[K] K) (ι : W →ₗ[K] V) (z : V) (B : Submodule K V) (L : Submodule (𝓞 K) W) :
    Set (Submodule (𝓞 K) V) :=
  {M | M.FG ∧ Submodule.span K (M : Set V) = B ∧
    dual h M ⊓ (Submodule.span K (M : Set V)).restrictScalars (𝓞 K) = M ∧ z ∈ M ∧
    (∀ c : K, c • z ∈ M → ∃ o : 𝓞 K, (o : K) = c) ∧ M.comap (ι.restrictScalars (𝓞 K)) = L}

omit [NumberField K] [StarRing K] in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨_, ⟨l, hl, rfl⟩, b, hb, rfl⟩` from `Submodule.mem_sup.1 hx`. Take `⟨s, rfl⟩` from `Submodule.mem_span_singleton.1 hb`. Conclude with `⟨l, hl, s, by rw [← algebraMap_smul K s]; rfl⟩`.

Introduce and unpack `⟨l, hl, s, rfl⟩`. Conclude with `Submodule.mem_sup.2 ⟨_, ⟨l, hl, rfl⟩, _, Submodule.mem_span_singleton.2 ⟨s, rfl⟩, by rw [← algebraMap_smul K s]; rfl⟩`.
-/
theorem mem_glue {ι : W →ₗ[K] V} {z : V} {T : ℕ} {L : Submodule (𝓞 K) W} {y : W} {x : V} :
    x ∈ glue ι z T L y ↔ ∃ l ∈ L, ∃ s : 𝓞 K, x = ι l + (s : K) • (ι y - (T : K)⁻¹ • z) := by
  constructor
  · intro hx
    obtain ⟨_, ⟨l, hl, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hb
    exact ⟨l, hl, s, by rw [← algebraMap_smul K s]; rfl⟩
  · rintro ⟨l, hl, s, rfl⟩
    exact Submodule.mem_sup.2 ⟨_, ⟨l, hl, rfl⟩, _, Submodule.mem_span_singleton.2 ⟨s, rfl⟩,
      by rw [← algebraMap_smul K s]; rfl⟩

omit [NumberField K] [StarRing K] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] [AddCommGroup W] [Module K W] in
/- English proof (translation)
Use `M.smul_mem s hx` as an intermediate fact. Rewrite `this` using `[← algebraMap_smul K s]`. Then use the resulting hypothesis.
-/
theorem smul_mem_int {M : Submodule (𝓞 K) V} (s : 𝓞 K) {x : V} (hx : x ∈ M) : (s : K) • x ∈ M := by
  have := M.smul_mem s hx
  rwa [← algebraMap_smul K s] at this

omit [StarRing K] [NumberField K] in
/- English proof (translation)
The claim follows from `smul_mem_int (V := K) s hx`.
-/
theorem int_mul (s : 𝓞 K) {x : K} (hx : x ∈ (1 : Submodule (𝓞 K) K)) : (s : K) * x ∈ (1 : Submodule (𝓞 K) K) :=
  smul_mem_int (V := K) s hx

/- English proof (translation)
Take `⟨t, ht⟩` from `star_algebraMap_ringOfIntegers_mem_range s`. Rewrite using `[← ht]`. Conclude with `int_mul t hx`.
-/
theorem star_int_mul (s : 𝓞 K) {x : K} (hx : x ∈ (1 : Submodule (𝓞 K) K)) :
    star (s : K) * x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨t, ht⟩ := star_algebraMap_ringOfIntegers_mem_range s
  rw [← ht]
  exact int_mul t hx

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h0 : W →ₗ⋆[K] W →ₗ[K] K} {ι : W →ₗ[K] V} {z : V} {T : ℕ}
  {B : Submodule K V} {L : Submodule (𝓞 K) W}

/- English proof (translation)
Take `⟨-, hsp, hd, hzM, hprim, hL⟩` from `hM`. Establish `inj` using `IsFractionRing.injective (𝓞 K) K`. Establish `hT' : (T : K) ≠ 0` using `Nat.cast_ne_zero.2 hT`. Establish `hint : ∀ x ∈ M, ∀ y ∈ M, h x y ∈ (1 : Submodule (𝓞 K) K)` using `fun x hx y hy => (dualBasic_mem_dual h M y).1 (hd.ge hy).1 x hx`. Establish `hLM : ∀ l, l ∈ L ↔ ι l ∈ M` using `fun l => by rw [← hL]; rfl`.

Set `g2 : M →ₗ[𝓞 K] K` to `((h z).restrictScalars (𝓞 K)) ∘ₗ M.subtype`. Establish `hg2 : ∀ y, g2 y ∈ LinearMap.range (Algebra.linearMap (𝓞 K) K)` using `fun y => Submodule.mem_one.1 (hint _ hzM _ y.2)`. Set `f2` to `g2.codRestrictOfInjective (Algebra.linearMap (𝓞 K) K) inj hg2`. Establish `hf2 : ∀ y, algebraMap (𝓞 K) K (f2 y) = h z y` using `fun y => g2.codRestrictOfInjective_comp_apply _ _ hg2 y`. Establish `s2 : Function.Surjective f2`.

Rewrite using `[← LinearMap.range_eq_top]`. Assume the negation of the conclusion as `hne`. Establish `hbot : (LinearMap.range f2 : Ideal (𝓞 K)) ≠ ⊥` using `fun e => by`. Establish `: f2 ⟨z, hzM⟩ = 0` using `(Submodule.eq_bot_iff _).1 e _ ⟨_, rfl⟩`. Establish `h2` using `hf2 ⟨z, hzM⟩`.

Rewrite `h2` using `[this, map_zero, hz]`. Conclude with `hT' (neg_eq_zero.1 h2.symm)`. Take `⟨γ, hγ, hγ1⟩` from `FractionalIdeal.exists_notMem_one_of_ne_bot (K := K) hbot hne`. Rewrite `hγ` using `[FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hbot)]`. Take `⟨o, ho⟩` from `hprim (star γ) (hd.le ⟨(dualBasic_mem_dual h M _).2 fun y hy => swap_mem hs (by`.

Use `hγ _ (FractionalIdeal.mem_coeIdeal_of_mem _ ⟨⟨y, hy⟩, rfl⟩)` as an intermediate fact. Rewrite `this` using `[hf2, FractionalIdeal.mem_one_iff]`. Rewrite using `[LinearMap.map_smulₛₗ, starRingEnd_apply, star_star, LinearMap.smul_apply, smul_eq_mul]`. Conclude with `Submodule.mem_one.2 this), Submodule.smul_mem _ _ (Submodule.subset_span hzM)⟩)`. Take `⟨t, ht⟩` from `star_algebraMap_ringOfIntegers_mem_range o`.

Use `hγ1 ((FractionalIdeal.mem_one_iff _).2 ⟨t, ?_⟩)` and prove the remaining obligations. Rewrite using `[ht]`. Express the relevant statement in the definitionally equal form `star (o : K) = γ`. Rewrite using `[ho, star_star]`. Take `⟨⟨v, hv⟩, hv1⟩` from `s2 1`.

Establish `hv2 : h z v = 1` using `by rw [← map_one (algebraMap (𝓞 K) K), ← hv1, hf2]`. Take `⟨y, c, rfl⟩` from `(hB v).1 (hsp.le (Submodule.subset_span hv))`. Establish `hιz : ∀ w, h (ι w) z = 0` using `fun w => swap_zero hs (hzι w)`. Establish `hc : c = -(T : K)⁻¹`. Rewrite `hv2` using `[map_add, map_smul, hzι, hz, smul_eq_mul]`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `-hv2`. Substitute `hc` using the available equality. Rewrite `hv` using `[neg_smul, ← sub_eq_add_neg]`. Use `⟨y, (dualBasic_mem_dual h0 L y).2 fun l hl => ?_, ?_, le_antisymm (fun x hx => ?_) (fun x hx => ?_)⟩` and prove the remaining obligations.

Simplify `hint _ ((hLM l).1 hl) _ hv` using `[hι, hιz]`. Use `hint _ hv _ hv using 1` and compare the differences between its conclusion and the goal. Simplify using `[hι, hιz, hzι, hz, LinearMap.map_smulₛₗ, hT']`. Take `⟨w, t, rfl⟩` from `(hB x).1 (hsp.le (Submodule.subset_span hx))`. Take `⟨s, hs'⟩` from `Submodule.mem_one.1 (hint _ hzM _ hx)`.

Establish `ht : t = -((s : K) * (T : K)⁻¹)`. Rewrite `hs'` using `[map_add, map_smul, hzι, hz, smul_eq_mul]`. Express the relevant statement in the definitionally equal form `(s : K) = _ at hs'`. Rewrite using `[hs']`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `e : ι w + t • z = ι (w - (s : K) • y) + (s : K) • (ι y - (T : K)⁻¹ • z)`. Rewrite using `[ht, map_sub, map_smul]`. Use `module`. Use `mem_glue.2 ⟨_, (hLM _).2 ?_, s, e⟩` and prove the remaining obligations.

Rewrite using `[← sub_eq_iff_eq_add.2 e]`. Conclude with `M.sub_mem hx (smul_mem_int s hv)`. Take `⟨l, hl, s, rfl⟩` from `mem_glue.1 hx`. Conclude with `M.add_mem ((hLM l).1 hl) (smul_mem_int s hv)`.
-/
theorem exists_eq_glue (hs : h.IsSymm) (hι : ∀ x y, h (ι x) (ι y) = h0 x y) (hT : T ≠ 0)
    (hz : h z z = -(T : K)) (hzι : ∀ w, h z (ι w) = 0) (hB : ∀ v, v ∈ B ↔ ∃ w, ∃ c : K, v = ι w + c • z)
    {M : Submodule (𝓞 K) V} (hM : M ∈ glued h ι z B L) :
    ∃ y ∈ dual h0 L, h0 y y - (T : K)⁻¹ ∈ (1 : Submodule (𝓞 K) K) ∧ M = glue ι z T L y := by
  obtain ⟨-, hsp, hd, hzM, hprim, hL⟩ := hM
  have inj := IsFractionRing.injective (𝓞 K) K
  have hT' : (T : K) ≠ 0 := Nat.cast_ne_zero.2 hT
  have hint : ∀ x ∈ M, ∀ y ∈ M, h x y ∈ (1 : Submodule (𝓞 K) K) := fun x hx y hy =>
    (dualBasic_mem_dual h M y).1 (hd.ge hy).1 x hx
  have hLM : ∀ l, l ∈ L ↔ ι l ∈ M := fun l => by rw [← hL]; rfl
  let g2 : M →ₗ[𝓞 K] K := ((h z).restrictScalars (𝓞 K)) ∘ₗ M.subtype
  have hg2 : ∀ y, g2 y ∈ LinearMap.range (Algebra.linearMap (𝓞 K) K) := fun y =>
    Submodule.mem_one.1 (hint _ hzM _ y.2)
  let f2 := g2.codRestrictOfInjective (Algebra.linearMap (𝓞 K) K) inj hg2
  have hf2 : ∀ y, algebraMap (𝓞 K) K (f2 y) = h z y := fun y =>
    g2.codRestrictOfInjective_comp_apply _ _ hg2 y
  have s2 : Function.Surjective f2 := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    have hbot : (LinearMap.range f2 : Ideal (𝓞 K)) ≠ ⊥ := fun e => by
      have : f2 ⟨z, hzM⟩ = 0 := (Submodule.eq_bot_iff _).1 e _ ⟨_, rfl⟩
      have h2 := hf2 ⟨z, hzM⟩
      rw [this, map_zero, hz] at h2
      exact hT' (neg_eq_zero.1 h2.symm)
    obtain ⟨γ, hγ, hγ1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := K) hbot hne
    rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hbot)] at hγ
    obtain ⟨o, ho⟩ := hprim (star γ) (hd.le ⟨(dualBasic_mem_dual h M _).2 fun y hy => swap_mem hs (by
      have := hγ _ (FractionalIdeal.mem_coeIdeal_of_mem _ ⟨⟨y, hy⟩, rfl⟩)
      rw [hf2, FractionalIdeal.mem_one_iff] at this
      rw [LinearMap.map_smulₛₗ, starRingEnd_apply, star_star, LinearMap.smul_apply, smul_eq_mul]
      exact Submodule.mem_one.2 this), Submodule.smul_mem _ _ (Submodule.subset_span hzM)⟩)
    obtain ⟨t, ht⟩ := star_algebraMap_ringOfIntegers_mem_range o
    refine hγ1 ((FractionalIdeal.mem_one_iff _).2 ⟨t, ?_⟩)
    rw [ht]
    change star (o : K) = γ
    rw [ho, star_star]
  obtain ⟨⟨v, hv⟩, hv1⟩ := s2 1
  have hv2 : h z v = 1 := by rw [← map_one (algebraMap (𝓞 K) K), ← hv1, hf2]
  obtain ⟨y, c, rfl⟩ := (hB v).1 (hsp.le (Submodule.subset_span hv))
  have hιz : ∀ w, h (ι w) z = 0 := fun w => swap_zero hs (hzι w)
  have hc : c = -(T : K)⁻¹ := by
    rw [map_add, map_smul, hzι, hz, smul_eq_mul] at hv2
    field_simp
    linear_combination -hv2
  subst hc
  rw [neg_smul, ← sub_eq_add_neg] at hv
  refine ⟨y, (dualBasic_mem_dual h0 L y).2 fun l hl => ?_, ?_, le_antisymm (fun x hx => ?_) (fun x hx => ?_)⟩
  · simpa [hι, hιz] using hint _ ((hLM l).1 hl) _ hv
  · convert hint _ hv _ hv using 1
    simp [hι, hιz, hzι, hz, LinearMap.map_smulₛₗ, hT']
  · obtain ⟨w, t, rfl⟩ := (hB x).1 (hsp.le (Submodule.subset_span hx))
    obtain ⟨s, hs'⟩ := Submodule.mem_one.1 (hint _ hzM _ hx)
    have ht : t = -((s : K) * (T : K)⁻¹) := by
      rw [map_add, map_smul, hzι, hz, smul_eq_mul] at hs'
      change (s : K) = _ at hs'
      rw [hs']
      field_simp
      ring
    have e : ι w + t • z = ι (w - (s : K) • y) + (s : K) • (ι y - (T : K)⁻¹ • z) := by
      rw [ht, map_sub, map_smul]; module
    refine mem_glue.2 ⟨_, (hLM _).2 ?_, s, e⟩
    rw [← sub_eq_iff_eq_add.2 e]
    exact M.sub_mem hx (smul_mem_int s hv)
  · obtain ⟨l, hl, s, rfl⟩ := mem_glue.1 hx
    exact M.add_mem ((hLM l).1 hl) (smul_mem_int s hv)

omit [StarRing K] in
/- English proof (translation)
Establish `key : ∀ y y' : W, y - y' ∈ L → glue ι z T L y ≤ glue ι z T L y'` using `fun y y' hy x hx => by`. Take `⟨l, hl, s, rfl⟩` from `mem_glue.1 hx`. Use `mem_glue.2 ⟨l + (s : K) • (y - y'), L.add_mem hl (smul_mem_int s hy), s, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_smul, map_sub]`. Use `module`.

Conclude with `le_antisymm (key _ _ hy) (key _ _ (by simpa using L.neg_mem hy))`.
-/
theorem glue_eq_of_sub_mem {y y' : W} (hy : y - y' ∈ L) : glue ι z T L y = glue ι z T L y' := by
  have key : ∀ y y' : W, y - y' ∈ L → glue ι z T L y ≤ glue ι z T L y' := fun y y' hy x hx => by
    obtain ⟨l, hl, s, rfl⟩ := mem_glue.1 hx
    refine mem_glue.2 ⟨l + (s : K) • (y - y'), L.add_mem hl (smul_mem_int s hy), s, ?_⟩
    rw [map_add, map_smul, map_sub]; module
  exact le_antisymm (key _ _ hy) (key _ _ (by simpa using L.neg_mem hy))

/- English proof (translation)
Establish `hT' : (T : K) ≠ 0` using `Nat.cast_ne_zero.2 hT`. Take `⟨l, hl, s, e1⟩` from `mem_glue.1 (e.le (mem_glue.2 ⟨0, L.zero_mem, 1, rfl⟩))`. Establish `e2 : (s : K) = 1`. Use `congrArg (h z) e1` as an intermediate fact. Simplify using `only [map_add, map_sub, map_smul, hzι, hz, smul_eq_mul, map_one] at this`.

Clear denominators, using `at this` for the nonvanishing conditions. Take the linear combination `-this`. Rewrite `e1` using `[e2]`. Establish `: y - y' = l` using `hinj (by`. Rewrite using `[map_sub]`.

Simplify using `only [map_zero, map_one, one_smul, zero_add] at e1`. Take the linear combination `(norm := module) e1)`. Rewrite using `[this]` and apply the resulting hypothesis.
-/
theorem sub_mem_of_glue_eq (hinj : Function.Injective ι) (hT : T ≠ 0)
    (hz : h z z = -(T : K)) (hzι : ∀ w, h z (ι w) = 0) {y y' : W} (e : glue ι z T L y = glue ι z T L y') :
    y - y' ∈ L := by
  have hT' : (T : K) ≠ 0 := Nat.cast_ne_zero.2 hT
  obtain ⟨l, hl, s, e1⟩ := mem_glue.1 (e.le (mem_glue.2 ⟨0, L.zero_mem, 1, rfl⟩))
  have e2 : (s : K) = 1 := by
    have := congrArg (h z) e1
    simp only [map_add, map_sub, map_smul, hzι, hz, smul_eq_mul, map_one] at this
    field_simp at this
    linear_combination -this
  rw [e2] at e1
  have : y - y' = l := hinj (by
    rw [map_sub]
    simp only [map_zero, map_one, one_smul, zero_add] at e1
    linear_combination (norm := module) e1)
  rwa [this]

/- English proof (translation)
Establish `hT' : (T : K) ≠ 0` using `Nat.cast_ne_zero.2 hT`. Establish `hιz : ∀ w, h (ι w) z = 0` using `fun w => swap_zero hs (hzι w)`. Establish `hs0 : h0.IsSymm` using `⟨fun a b => by rw [← hι, ← hι]; exact hs.eq _ _⟩`. Establish `hy1` using `(dualBasic_mem_dual h0 L y).1 hy`. Establish `hy2 : ∀ l ∈ L, h0 y l ∈ (1 : Submodule (𝓞 K) K)` using `fun l hl => swap_mem hs0 (hy1 l hl)`.

Establish `hzG : z ∈ glue ι z T L y` using `mem_glue.2 ⟨_, hTy, -(T : 𝓞 K), by`. Rewrite using `[map_smul]`. Simplify using `[smul_sub, smul_smul, hT']⟩`. Establish `hLG : ∀ l ∈ L, ι l ∈ glue ι z T L y` using `fun l hl => mem_glue.2 ⟨l, hl, 0, by simp⟩`. Establish `hvG : ι y - (T : K)⁻¹ • z ∈ glue ι z T L y` using `mem_glue.2 ⟨0, L.zero_mem, 1, by simp⟩`.

Establish `hsp : Submodule.span K (glue ι z T L y : Set V) = B`. Use `le_antisymm (Submodule.span_le.2 fun x hx => ?_) fun x hx => ?_` and prove the remaining obligations. Take `⟨l, hl, s, rfl⟩` from `mem_glue.1 hx`. Conclude with `(hB _).2 ⟨l + (s : K) • y, -((s : K) * (T : K)⁻¹), by rw [map_add, map_smul]; module⟩`. Take `⟨w, c, rfl⟩` from `(hB _).1 hx`.

Use `Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (Submodule.subset_span hzG))` and prove the remaining obligations. Establish `: Submodule.span K (L : Set W) ≤ (Submodule.span K (glue ι z T L y : Set V)).comap ι` using `Submodule.span_le.2 fun l hl => Submodule.subset_span (hLG l hl)`. Conclude with `this (hL.span_eq_top.ge trivial)`. Establish `hint : ∀ x ∈ glue ι z T L y, ∀ x' ∈ glue ι z T L y, h x x' ∈ (1 : Submodule (𝓞 K) K)`. Introduce `x hx x' hx'`.

Take `⟨l, hl, s, rfl⟩` from `mem_glue.1 hx`. Take `⟨l', hl', s', rfl⟩` from `mem_glue.1 hx'`. Use `Submodule.add_mem _ (Submodule.add_mem _ (hI l hl l' hl') (int_mul s' (hy1 l hl))) (Submodule.add_mem _ (star_int_mul s (hy2 l' hl')) (star_int_mul s (int_mul s' hn))) using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_add, map_sub, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, hι, hιz, hzι, hz, smul_eq_mul, starRingEnd_apply, RingHom.id_apply, star_inv₀, star_natCast]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `hdiv : ∀ b : 𝓞 K, h0 y ((b : K) • y) ∈ (1 : Submodule (𝓞 K) K) → (b : K) * (T : K)⁻¹ ∈ (1 : Submodule (𝓞 K) K)` using `fun b hb => by`. Use `Submodule.sub_mem _ hb (int_mul b hn) using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨(hL.fg.map _).sup (Submodule.fg_span_singleton _), hsp, le_antisymm ?_ fun x hx => ⟨(dualBasic_mem_dual _ _ _).2 fun x' hx' => hint _ hx' _ hx, Submodule.subset_span hx⟩, hzG, fun c hc => ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `x ⟨hx, hxB⟩`. Take `⟨w, t, rfl⟩` from `(hB x).1 (hsp.le hxB)`. Take `⟨s, hs'⟩` from `Submodule.mem_one.1 ((dualBasic_mem_dual _ _ _).1 hx _ hzG)`. Establish `ht : t = -((s : K) * (T : K)⁻¹)`.

Rewrite `hs'` using `[map_add, map_smul, hzι, hz, smul_eq_mul]`. Express the relevant statement in the definitionally equal form `(s : K) = _ at hs'`. Rewrite using `[hs']`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `e : ι w + t • z = ι (w - (s : K) • y) + (s : K) • (ι y - (T : K)⁻¹ • z)`. Rewrite using `[ht, map_sub, map_smul]`. Use `module`. Use `mem_glue.2 ⟨_, ?_, s, e⟩` and prove the remaining obligations. Establish `hw : ∀ x' ∈ glue ι z T L y, h x' (ι (w - (s : K) • y)) ∈ (1 : Submodule (𝓞 K) K)` using `fun x' hx' => by`.

Rewrite using `[← sub_eq_iff_eq_add.2 e, map_sub]`. Conclude with `Submodule.sub_mem _ ((dualBasic_mem_dual _ _ _).1 hx _ hx') (hint _ hx' _ (smul_mem_int s hvG))`. Take `⟨b, hb⟩` from `hgen (w - (s : K) • y) ((dualBasic_mem_dual _ _ _).2 fun l hl => by`. Rewrite using `[← hι]`. Conclude with `hw _ (hLG l hl))`.

Establish `h1 : h0 y (w - (s : K) • y) ∈ (1 : Submodule (𝓞 K) K)`. Use `hw _ hvG using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_sub h, LinearMap.sub_apply, hι, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hzι, smul_zero, sub_zero]`. Take `⟨o, ho⟩` from `Submodule.mem_one.1 (hdiv b (by`. Use `Submodule.sub_mem _ h1 (hy2 _ hb) using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[← map_sub, sub_sub_cancel]))`. Establish `h2 : (b : K) • y ∈ L`. Use `smul_mem_int o hTy using 1` and compare the differences between its conclusion and the goal. Express the relevant statement in the definitionally equal form `_ = (algebraMap (𝓞 K) K o) • _`. Rewrite using `[ho, smul_smul, inv_mul_cancel_right₀ hT']`.

Simplify using `using L.add_mem hb h2`. Take `⟨l, hl, s, e⟩` from `mem_glue.1 hc`. Establish `e1 : c = -((s : K) * (T : K)⁻¹)`. Use `congrArg (h z) e` as an intermediate fact. Simplify using `only [map_add, map_sub, map_smul, hzι, hz, smul_eq_mul] at this`.

Clear denominators, using `at this ⊢` for the nonvanishing conditions. Take the linear combination `-this`. Establish `e2 : (s : K) • y = -l` using `hinj (by`. Rewrite using `[map_smul, map_neg]`. Rewrite `e` using `[e1]`.

Take the linear combination `(norm := module) -e)`. Take `⟨o, ho⟩` from `Submodule.mem_one.1 (hdiv s (by rw [e2]; exact hy2 _ (L.neg_mem hl)))`. Conclude with `⟨-o, by rw [e1, ← ho]; simp⟩`. Use `le_antisymm (fun w hw => ?_) hLG` and prove the remaining obligations. Take `⟨l, hl, s, e⟩` from `mem_glue.1 hw`.

Express the relevant statement in the definitionally equal form `ι w = _ at e`. Establish `e1 : (s : K) = 0`. Use `congrArg (h z) e` as an intermediate fact. Simplify using `only [map_add, map_sub, map_smul, hzι, hz, smul_eq_mul] at this`. Clear denominators, using `at this` for the nonvanishing conditions.

Take the linear combination `-this`. Rewrite `e` using `[e1, zero_smul, add_zero]`. Rewrite using `[hinj e]` and apply the resulting hypothesis.
-/
theorem glue_mem (hs : h.IsSymm) (hι : ∀ x y, h (ι x) (ι y) = h0 x y) (hinj : Function.Injective ι) (hT : T ≠ 0)
    (hz : h z z = -(T : K)) (hzι : ∀ w, h z (ι w) = 0) (hB : ∀ v, v ∈ B ↔ ∃ w, ∃ c : K, v = ι w + c • z)
    (hL : Submodule.IsLattice K L) (hI : IsIntegralLat h0 L) {y : W} (hy : y ∈ dual h0 L)
    (hTy : (T : K) • y ∈ L) (hn : h0 y y - (T : K)⁻¹ ∈ (1 : Submodule (𝓞 K) K))
    (hgen : ∀ w ∈ dual h0 L, ∃ b : 𝓞 K, w - (b : K) • y ∈ L) : glue ι z T L y ∈ glued h ι z B L := by
  have hT' : (T : K) ≠ 0 := Nat.cast_ne_zero.2 hT
  have hιz : ∀ w, h (ι w) z = 0 := fun w => swap_zero hs (hzι w)
  have hs0 : h0.IsSymm := ⟨fun a b => by rw [← hι, ← hι]; exact hs.eq _ _⟩
  have hy1 := (dualBasic_mem_dual h0 L y).1 hy
  have hy2 : ∀ l ∈ L, h0 y l ∈ (1 : Submodule (𝓞 K) K) := fun l hl => swap_mem hs0 (hy1 l hl)
  have hzG : z ∈ glue ι z T L y := mem_glue.2 ⟨_, hTy, -(T : 𝓞 K), by
    rw [map_smul]
    simp [smul_sub, smul_smul, hT']⟩
  have hLG : ∀ l ∈ L, ι l ∈ glue ι z T L y := fun l hl => mem_glue.2 ⟨l, hl, 0, by simp⟩
  have hvG : ι y - (T : K)⁻¹ • z ∈ glue ι z T L y := mem_glue.2 ⟨0, L.zero_mem, 1, by simp⟩
  have hsp : Submodule.span K (glue ι z T L y : Set V) = B := by
    refine le_antisymm (Submodule.span_le.2 fun x hx => ?_) fun x hx => ?_
    · obtain ⟨l, hl, s, rfl⟩ := mem_glue.1 hx
      exact (hB _).2 ⟨l + (s : K) • y, -((s : K) * (T : K)⁻¹), by rw [map_add, map_smul]; module⟩
    · obtain ⟨w, c, rfl⟩ := (hB _).1 hx
      refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (Submodule.subset_span hzG))
      have : Submodule.span K (L : Set W) ≤ (Submodule.span K (glue ι z T L y : Set V)).comap ι :=
        Submodule.span_le.2 fun l hl => Submodule.subset_span (hLG l hl)
      exact this (hL.span_eq_top.ge trivial)
  have hint : ∀ x ∈ glue ι z T L y, ∀ x' ∈ glue ι z T L y, h x x' ∈ (1 : Submodule (𝓞 K) K) := by
    intro x hx x' hx'
    obtain ⟨l, hl, s, rfl⟩ := mem_glue.1 hx
    obtain ⟨l', hl', s', rfl⟩ := mem_glue.1 hx'
    convert Submodule.add_mem _ (Submodule.add_mem _ (hI l hl l' hl') (int_mul s' (hy1 l hl)))
      (Submodule.add_mem _ (star_int_mul s (hy2 l' hl')) (star_int_mul s (int_mul s' hn))) using 1
    simp only [map_add, map_sub, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, hι, hιz, hzι, hz, smul_eq_mul, starRingEnd_apply, RingHom.id_apply, star_inv₀,
      star_natCast]
    field_simp
    ring
  have hdiv : ∀ b : 𝓞 K, h0 y ((b : K) • y) ∈ (1 : Submodule (𝓞 K) K) →
      (b : K) * (T : K)⁻¹ ∈ (1 : Submodule (𝓞 K) K) := fun b hb => by
    convert Submodule.sub_mem _ hb (int_mul b hn) using 1
    rw [map_smul, smul_eq_mul]; ring
  refine ⟨(hL.fg.map _).sup (Submodule.fg_span_singleton _), hsp, le_antisymm ?_ fun x hx =>
    ⟨(dualBasic_mem_dual _ _ _).2 fun x' hx' => hint _ hx' _ hx, Submodule.subset_span hx⟩, hzG, fun c hc => ?_, ?_⟩
  · rintro x ⟨hx, hxB⟩
    obtain ⟨w, t, rfl⟩ := (hB x).1 (hsp.le hxB)
    obtain ⟨s, hs'⟩ := Submodule.mem_one.1 ((dualBasic_mem_dual _ _ _).1 hx _ hzG)
    have ht : t = -((s : K) * (T : K)⁻¹) := by
      rw [map_add, map_smul, hzι, hz, smul_eq_mul] at hs'
      change (s : K) = _ at hs'
      rw [hs']
      field_simp
      ring
    have e : ι w + t • z = ι (w - (s : K) • y) + (s : K) • (ι y - (T : K)⁻¹ • z) := by
      rw [ht, map_sub, map_smul]; module
    refine mem_glue.2 ⟨_, ?_, s, e⟩
    have hw : ∀ x' ∈ glue ι z T L y, h x' (ι (w - (s : K) • y)) ∈ (1 : Submodule (𝓞 K) K) := fun x' hx' => by
      rw [← sub_eq_iff_eq_add.2 e, map_sub]
      exact Submodule.sub_mem _ ((dualBasic_mem_dual _ _ _).1 hx _ hx') (hint _ hx' _ (smul_mem_int s hvG))
    obtain ⟨b, hb⟩ := hgen (w - (s : K) • y) ((dualBasic_mem_dual _ _ _).2 fun l hl => by
      rw [← hι]; exact hw _ (hLG l hl))
    have h1 : h0 y (w - (s : K) • y) ∈ (1 : Submodule (𝓞 K) K) := by
      convert hw _ hvG using 1
      rw [map_sub h, LinearMap.sub_apply, hι, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hzι, smul_zero, sub_zero]
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 (hdiv b (by
      convert Submodule.sub_mem _ h1 (hy2 _ hb) using 1
      rw [← map_sub, sub_sub_cancel]))
    have h2 : (b : K) • y ∈ L := by
      convert smul_mem_int o hTy using 1
      change _ = (algebraMap (𝓞 K) K o) • _
      rw [ho, smul_smul, inv_mul_cancel_right₀ hT']
    simpa using L.add_mem hb h2
  · obtain ⟨l, hl, s, e⟩ := mem_glue.1 hc
    have e1 : c = -((s : K) * (T : K)⁻¹) := by
      have := congrArg (h z) e
      simp only [map_add, map_sub, map_smul, hzι, hz, smul_eq_mul] at this
      field_simp at this ⊢
      linear_combination -this
    have e2 : (s : K) • y = -l := hinj (by
      rw [map_smul, map_neg]
      rw [e1] at e
      linear_combination (norm := module) -e)
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 (hdiv s (by rw [e2]; exact hy2 _ (L.neg_mem hl)))
    exact ⟨-o, by rw [e1, ← ho]; simp⟩
  · refine le_antisymm (fun w hw => ?_) hLG
    obtain ⟨l, hl, s, e⟩ := mem_glue.1 hw
    change ι w = _ at e
    have e1 : (s : K) = 0 := by
      have := congrArg (h z) e
      simp only [map_add, map_sub, map_smul, hzι, hz, smul_eq_mul] at this
      field_simp at this
      linear_combination -this
    rw [e1, zero_smul, add_zero] at e
    rwa [hinj e]

/- English proof (translation)
Establish `inj` using `IsFractionRing.injective (𝓞 K) K`. Establish `hT' : (T : K) ≠ 0` using `Nat.cast_ne_zero.2 hT`. Establish `hs0 : h0.IsSymm` using `⟨fun a b => by rw [← hι, ← hι]; exact hs.eq _ _⟩`. Establish `hinj : Function.Injective ι` using `(injective_iff_map_eq_zero ι).2 fun w hw => hn0.1 w fun y => by rw [← hι, hw, map_zero, LinearMap.zero_apply]`. Take `⟨x0, hx0, hgen, hann⟩` from `hc`.

Use `replace hgen : ∀ y ∈ dual h0 L, ∃ a : 𝓞 K, y - (a : K) • x0 ∈ L := fun y hy => by`. Take `⟨a, ha⟩` from `hgen y hy`. Conclude with `⟨a, by rwa [← algebraMap_smul K a] at ha⟩`. Use `replace hann : ∀ r : 𝓞 K, (r : K) • x0 ∈ L ↔ r ∈ Ideal.span {(T : 𝓞 K)} := fun r => by`. Rewrite using `[← hann, ← algebraMap_smul K r]`.

Establish `hx1` using `(dualBasic_mem_dual h0 L x0).1 hx0`. Establish `hx2 : ∀ l ∈ L, h0 x0 l ∈ (1 : Submodule (𝓞 K) K)` using `fun l hl => swap_mem hs0 (hx1 l hl)`. Establish `hTx : (T : K) • x0 ∈ L` using `by simpa using (hann T).2 (Ideal.mem_span_singleton_self _)`. Take `⟨c, hc⟩` from `Submodule.mem_one.1 (hx2 _ hTx)`. Rewrite `hc` using `[map_smul, smul_eq_mul]`.

Establish `hcs : star (c : K) = c`. Express the relevant statement in the definitionally equal form `star (algebraMap (𝓞 K) K c) = algebraMap (𝓞 K) K c`. Rewrite using `[hc, star_mul', star_natCast]`. Conclude with `congrArg _ (hs0.eq x0 x0)`. Establish `hx3 : h0 x0 x0 = (c : K) * (T : K)⁻¹`.

Express the relevant statement in the definitionally equal form `_ = algebraMap (𝓞 K) K c * _`. Rewrite using `[hc]`. Clear the denominators using the available nonvanishing facts. Establish `hdiv : ∀ a : 𝓞 K, (a : K) * (T : K)⁻¹ ∈ (1 : Submodule (𝓞 K) K) ↔ a ∈ Ideal.span {(T : 𝓞 K)}` using `fun a => by`. Rewrite using `[Submodule.mem_one, Ideal.mem_span_singleton']`.

Use `exists_congr fun o => ?_` and prove the remaining obligations. Rewrite using `[eq_mul_inv_iff_mul_eq₀ hT', ← inj.eq_iff, map_mul, map_natCast]`. Establish `hstarT : ∀ a a' : 𝓞 K, (a' : K) = star (a : K) → a ∈ Ideal.span {(T : 𝓞 K)} → a' ∈ Ideal.span {(T : 𝓞 K)}` using `fun a a' e ha => by`. Rewrite `ha`, the goal using `[← hdiv]`. Take `⟨o, ho⟩` from `Submodule.mem_one.1 ha`.

Use `star_int_mul o (Submodule.mem_one.2 ⟨1, rfl⟩)` as an intermediate fact. Express the relevant statement in the definitionally equal form `star (algebraMap (𝓞 K) K o) * _ ∈ _ at this`. Rewrite `this` using `[ho, map_one, mul_one, star_mul', star_inv₀, star_natCast, ← e]`. Then use the resulting hypothesis. Establish `: Finite (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})` using `Ideal.finiteQuotientOfFreeOfNeBot _ (by`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`.

Conclude with `Nat.cast_ne_zero.2 hT)`. Establish `hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {(T : 𝓞 K)}) c)`. Rewrite using `[isUnit_iff_mem_nonZeroDivisors_of_finite, mem_nonZeroDivisors_iff_right]`. Introduce `q hq`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective q`.

Rewrite `hq` using `[← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← hdiv]`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`. Take `⟨a', ha'⟩` from `star_algebraMap_ringOfIntegers_mem_range a`. Express the relevant statement in the definitionally equal form `(a' : K) = star (a : K) at ha'`. Use `hstarT a' a (by rw [ha', star_star]) ((hann _).1 ?_)` and prove the remaining obligations.

Rewrite using `[← (dualLattice (𝓞 K) K W h0 hs0 hn0 star_algebraMap_ringOfIntegers_mem_range L hL).2.1, dualBasic_mem_dual]`. Introduce `w hw`. Take `⟨b, hb⟩` from `hgen w hw`. Use `swap_mem hs0 ?_` and prove the remaining obligations. Use `Submodule.add_mem _ (int_mul b hq) (int_mul a (hx2 _ hb)) using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [map_sub, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply, hx3, ha', star_star, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨q, hq⟩` from `hunit.exists_right_inv`. Take `⟨d, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Rewrite `hq` using `[← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]`.

Take `⟨d', hd'⟩` from `star_algebraMap_ringOfIntegers_mem_range d`. Express the relevant statement in the definitionally equal form `(d' : K) = star (d : K) at hd'`. Establish `hq' : c * d' - 1 ∈ Ideal.span {(T : 𝓞 K)}` using `hstarT _ _ (by`. Simplify using `only [map_sub, map_mul, map_one, star_sub, star_mul', star_one, hcs, hd']) hq`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, k * (T : 𝓞 K) = c * (c * d * d') - 1 := by`.

Take `⟨e, he⟩` from `Ideal.mem_span_singleton'.1 hq`. Take `⟨e', he'⟩` from `Ideal.mem_span_singleton'.1 hq'`. Conclude with `⟨e * (c * d') + e', by linear_combination (c * d') * he + he'⟩`. Establish `hcnt` using `hcount (c * d * d') (by`. Simplify using `only [map_mul, star_mul', hcs, hd', star_star]; ring) ⟨c, -k, by linear_combination -hk⟩`.

Generalize the expression as in `c * d * d' = c' at hk hcnt`. Establish `hnorm : ∀ a a' : 𝓞 K, (a' : K) = star (a : K) → (h0 ((a : K) • x0) ((a : K) • x0) - (T : K)⁻¹ ∈ (1 : Submodule (𝓞 K) K) ↔ a * a' - c' ∈ Ideal.span {(T : 𝓞 K)})` using `fun a a' e => by`. Establish `: h0 ((a : K) • x0) ((a : K) • x0) - (T : K)⁻¹ = ((a * a' * c - 1 : 𝓞 K) : K) * (T : K)⁻¹`. Simplify using `only [map_sub, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply, hx3, e, map_mul, map_one]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, hdiv, Ideal.mem_span_singleton', Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨o, ho⟩`. Conclude with `⟨o * c' - a * a' * k, by linear_combination c' * ho - a * a' * hk⟩`. Introduce and unpack `⟨o, ho⟩`.

Conclude with `⟨o * c + k, by linear_combination c * ho + hk⟩`. Use `choose r hr using Ideal.Quotient.mk_surjective (I := Ideal.span {(T : 𝓞 K)})`. Establish `hg : ∀ a : 𝓞 K, glue ι z T L ((r (Ideal.Quotient.mk _ a) : K) • x0) = glue ι z T L ((a : K) • x0)` using `fun a => glue_eq_of_sub_mem (by`. Use `(hann _).2 (Ideal.Quotient.eq.1 (hr (Ideal.Quotient.mk _ a)))` as an intermediate fact. Simplify `this)` using `only [map_sub, sub_smul]`.

Establish `hbij : Set.BijOn (fun q => glue ι z T L ((r q : K) • x0)) {a : 𝓞 K ⧸ Ideal.span {(T : 𝓞 K)} | ∃ x y : 𝓞 K, Ideal.Quotient.mk _ x = a ∧ (y : K) = star (x : K) ∧ x * y - c' ∈ Ideal.span {(T : 𝓞 K)}} (glued h ι z B L)`. Use `⟨?_, fun q _ q' _ e => ?_, fun M hM => ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨a, a', rfl, e, ha⟩`. Express the relevant statement in the definitionally equal form `glue ι z T L _ ∈ _`. Rewrite using `[hg]`.

Use `glue_mem hs hι hinj hT hz hzι hB hL hI (smul_mem_int a hx0) ?_ ((hnorm a a' e).2 ha) fun w hw => ?_` and prove the remaining obligations. Rewrite using `[smul_comm]`. Conclude with `smul_mem_int a hTx`. Take `⟨b, hb⟩` from `hgen w hw`. Take `⟨o, ho⟩` from `Ideal.mem_span_singleton'.1 ha`.

Establish `h1` using `(hann (b * a' * c * a - b)).2 (Ideal.mem_span_singleton'.2 ⟨b * (o * c + k), by linear_combination b * c * ho + b * hk⟩)`. Use `⟨b * a' * c, ?_⟩` and prove the remaining obligations. Use `L.sub_mem hb h1 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_sub, map_mul]`. Use `module`.

Use `sub_mem_of_glue_eq hinj hT hz hzι e` as an intermediate fact. Establish `h1` using `(hann (r q - r q')).1 (by simpa only [map_sub, sub_smul] using this)`. Rewrite `h1` using `[← Ideal.Quotient.eq, hr, hr]`. Then use the resulting hypothesis. Take `⟨y, hy, hn, rfl⟩` from `exists_eq_glue hs hι hT hz hzι hB hM`. Take `⟨a, ha⟩` from `hgen y hy`.

Take `⟨a', ha'⟩` from `star_algebraMap_ringOfIntegers_mem_range a`. Establish `hy1` using `(dualBasic_mem_dual h0 L y).1 hy`. Use `⟨Ideal.Quotient.mk _ a, ⟨a, a', rfl, ha', (hnorm a a' ha').1 ?_⟩, (hg a).trans (glue_eq_of_sub_mem ha).symm⟩` and prove the remaining obligations. Use `Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ hn (hy1 _ ha)) (swap_mem hs0 (hy1 _ ha))) (hI _ ha _ ha) using 1` and compare the differences between its conclusion and the goal. Generalize the expression as in `(a : K) • x0 = y'`.

Simplify using `only [map_sub, LinearMap.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨(Set.toFinite _).of_surjOn _ hbij.surjOn, hbij.ncard_eq.symm.trans hcnt⟩`.
-/
theorem ncard_glued [FiniteDimensional K W] (hs : h.IsSymm) (hι : ∀ x y, h (ι x) (ι y) = h0 x y)
    (hn0 : h0.Nondegenerate) (hT : T ≠ 0)
    (hz : h z z = -(T : K)) (hzι : ∀ w, h z (ι w) = 0) (hB : ∀ v, v ∈ B ↔ ∃ w, ∃ c : K, v = ι w + c • z)
    (hL : Submodule.IsLattice K L) (hI : IsIntegralLat h0 L)
    (hc : GlobalTheory.Mass.CyclicGenus.Cyc (dual h0 L) L (Ideal.span {(T : 𝓞 K)})) (n : ℕ)
    (hcount : ∀ c : 𝓞 K, star (c : K) = (c : K) → IsCoprime c (T : 𝓞 K) →
      Nat.card {a : 𝓞 K ⧸ Ideal.span {(T : 𝓞 K)} // ∃ x y : 𝓞 K, Ideal.Quotient.mk _ x = a ∧
        (y : K) = star (x : K) ∧ x * y - c ∈ Ideal.span {(T : 𝓞 K)}} = n) :
    (glued h ι z B L).Finite ∧ (glued h ι z B L).ncard = n := by
  have inj := IsFractionRing.injective (𝓞 K) K
  have hT' : (T : K) ≠ 0 := Nat.cast_ne_zero.2 hT
  have hs0 : h0.IsSymm := ⟨fun a b => by rw [← hι, ← hι]; exact hs.eq _ _⟩
  have hinj : Function.Injective ι := (injective_iff_map_eq_zero ι).2 fun w hw =>
    hn0.1 w fun y => by rw [← hι, hw, map_zero, LinearMap.zero_apply]
  obtain ⟨x0, hx0, hgen, hann⟩ := hc
  replace hgen : ∀ y ∈ dual h0 L, ∃ a : 𝓞 K, y - (a : K) • x0 ∈ L := fun y hy => by
    obtain ⟨a, ha⟩ := hgen y hy
    exact ⟨a, by rwa [← algebraMap_smul K a] at ha⟩
  replace hann : ∀ r : 𝓞 K, (r : K) • x0 ∈ L ↔ r ∈ Ideal.span {(T : 𝓞 K)} := fun r => by
    rw [← hann, ← algebraMap_smul K r]
  have hx1 := (dualBasic_mem_dual h0 L x0).1 hx0
  have hx2 : ∀ l ∈ L, h0 x0 l ∈ (1 : Submodule (𝓞 K) K) := fun l hl => swap_mem hs0 (hx1 l hl)
  have hTx : (T : K) • x0 ∈ L := by simpa using (hann T).2 (Ideal.mem_span_singleton_self _)
  obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hx2 _ hTx)
  rw [map_smul, smul_eq_mul] at hc
  have hcs : star (c : K) = c := by
    change star (algebraMap (𝓞 K) K c) = algebraMap (𝓞 K) K c
    rw [hc, star_mul', star_natCast]
    exact congrArg _ (hs0.eq x0 x0)
  have hx3 : h0 x0 x0 = (c : K) * (T : K)⁻¹ := by
    change _ = algebraMap (𝓞 K) K c * _
    rw [hc]; field_simp
  have hdiv : ∀ a : 𝓞 K, (a : K) * (T : K)⁻¹ ∈ (1 : Submodule (𝓞 K) K) ↔ a ∈ Ideal.span {(T : 𝓞 K)} := fun a => by
    rw [Submodule.mem_one, Ideal.mem_span_singleton']
    refine exists_congr fun o => ?_
    rw [eq_mul_inv_iff_mul_eq₀ hT', ← inj.eq_iff, map_mul, map_natCast]
  have hstarT : ∀ a a' : 𝓞 K, (a' : K) = star (a : K) → a ∈ Ideal.span {(T : 𝓞 K)} →
      a' ∈ Ideal.span {(T : 𝓞 K)} := fun a a' e ha => by
    rw [← hdiv] at ha ⊢
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 ha
    have := star_int_mul o (Submodule.mem_one.2 ⟨1, rfl⟩)
    change star (algebraMap (𝓞 K) K o) * _ ∈ _ at this
    rwa [ho, map_one, mul_one, star_mul', star_inv₀, star_natCast, ← e] at this
  have : Finite (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)}) := Ideal.finiteQuotientOfFreeOfNeBot _ (by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact Nat.cast_ne_zero.2 hT)
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {(T : 𝓞 K)}) c) := by
    rw [isUnit_iff_mem_nonZeroDivisors_of_finite, mem_nonZeroDivisors_iff_right]
    intro q hq
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← hdiv] at hq
    rw [Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨a', ha'⟩ := star_algebraMap_ringOfIntegers_mem_range a
    change (a' : K) = star (a : K) at ha'
    refine hstarT a' a (by rw [ha', star_star]) ((hann _).1 ?_)
    rw [← (dualLattice (𝓞 K) K W h0 hs0 hn0 star_algebraMap_ringOfIntegers_mem_range L hL).2.1, dualBasic_mem_dual]
    intro w hw
    obtain ⟨b, hb⟩ := hgen w hw
    refine swap_mem hs0 ?_
    convert Submodule.add_mem _ (int_mul b hq) (int_mul a (hx2 _ hb)) using 1
    simp only [map_sub, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply,
      RingHom.id_apply, hx3, ha', star_star, map_mul]
    ring
  obtain ⟨q, hq⟩ := hunit.exists_right_inv
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq] at hq
  obtain ⟨d', hd'⟩ := star_algebraMap_ringOfIntegers_mem_range d
  change (d' : K) = star (d : K) at hd'
  have hq' : c * d' - 1 ∈ Ideal.span {(T : 𝓞 K)} := hstarT _ _ (by
    simp only [map_sub, map_mul, map_one, star_sub, star_mul', star_one, hcs, hd']) hq
  obtain ⟨k, hk⟩ : ∃ k, k * (T : 𝓞 K) = c * (c * d * d') - 1 := by
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 hq
    obtain ⟨e', he'⟩ := Ideal.mem_span_singleton'.1 hq'
    exact ⟨e * (c * d') + e', by linear_combination (c * d') * he + he'⟩
  have hcnt := hcount (c * d * d') (by
    simp only [map_mul, star_mul', hcs, hd', star_star]; ring) ⟨c, -k, by linear_combination -hk⟩
  generalize c * d * d' = c' at hk hcnt
  have hnorm : ∀ a a' : 𝓞 K, (a' : K) = star (a : K) →
      (h0 ((a : K) • x0) ((a : K) • x0) - (T : K)⁻¹ ∈ (1 : Submodule (𝓞 K) K) ↔
        a * a' - c' ∈ Ideal.span {(T : 𝓞 K)}) := fun a a' e => by
    have : h0 ((a : K) • x0) ((a : K) • x0) - (T : K)⁻¹ = ((a * a' * c - 1 : 𝓞 K) : K) * (T : K)⁻¹ := by
      simp only [map_sub, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply,
        RingHom.id_apply, hx3, e, map_mul, map_one]
      ring
    rw [this, hdiv, Ideal.mem_span_singleton', Ideal.mem_span_singleton']
    constructor
    · rintro ⟨o, ho⟩
      exact ⟨o * c' - a * a' * k, by linear_combination c' * ho - a * a' * hk⟩
    · rintro ⟨o, ho⟩
      exact ⟨o * c + k, by linear_combination c * ho + hk⟩
  choose r hr using Ideal.Quotient.mk_surjective (I := Ideal.span {(T : 𝓞 K)})
  have hg : ∀ a : 𝓞 K, glue ι z T L ((r (Ideal.Quotient.mk _ a) : K) • x0) = glue ι z T L ((a : K) • x0) :=
    fun a => glue_eq_of_sub_mem (by
      have := (hann _).2 (Ideal.Quotient.eq.1 (hr (Ideal.Quotient.mk _ a)))
      simpa only [map_sub, sub_smul] using this)
  have hbij : Set.BijOn (fun q => glue ι z T L ((r q : K) • x0))
      {a : 𝓞 K ⧸ Ideal.span {(T : 𝓞 K)} | ∃ x y : 𝓞 K, Ideal.Quotient.mk _ x = a ∧
        (y : K) = star (x : K) ∧ x * y - c' ∈ Ideal.span {(T : 𝓞 K)}} (glued h ι z B L) := by
    refine ⟨?_, fun q _ q' _ e => ?_, fun M hM => ?_⟩
    · rintro _ ⟨a, a', rfl, e, ha⟩
      change glue ι z T L _ ∈ _
      rw [hg]
      refine glue_mem hs hι hinj hT hz hzι hB hL hI (smul_mem_int a hx0) ?_ ((hnorm a a' e).2 ha) fun w hw => ?_
      · rw [smul_comm]; exact smul_mem_int a hTx
      · obtain ⟨b, hb⟩ := hgen w hw
        obtain ⟨o, ho⟩ := Ideal.mem_span_singleton'.1 ha
        have h1 := (hann (b * a' * c * a - b)).2 (Ideal.mem_span_singleton'.2
          ⟨b * (o * c + k), by linear_combination b * c * ho + b * hk⟩)
        refine ⟨b * a' * c, ?_⟩
        convert L.sub_mem hb h1 using 1
        simp only [map_sub, map_mul]
        module
    · have := sub_mem_of_glue_eq hinj hT hz hzι e
      have h1 := (hann (r q - r q')).1 (by simpa only [map_sub, sub_smul] using this)
      rwa [← Ideal.Quotient.eq, hr, hr] at h1
    · obtain ⟨y, hy, hn, rfl⟩ := exists_eq_glue hs hι hT hz hzι hB hM
      obtain ⟨a, ha⟩ := hgen y hy
      obtain ⟨a', ha'⟩ := star_algebraMap_ringOfIntegers_mem_range a
      have hy1 := (dualBasic_mem_dual h0 L y).1 hy
      refine ⟨Ideal.Quotient.mk _ a, ⟨a, a', rfl, ha', (hnorm a a' ha').1 ?_⟩,
        (hg a).trans (glue_eq_of_sub_mem ha).symm⟩
      convert Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ hn (hy1 _ ha))
        (swap_mem hs0 (hy1 _ ha))) (hI _ ha _ ha) using 1
      generalize (a : K) • x0 = y'
      simp only [map_sub, LinearMap.sub_apply]
      ring
  exact ⟨(Set.toFinite _).of_surjOn _ hbij.surjOn, hbij.ncard_eq.symm.trans hcnt⟩

end General

variable (D : D7)

/- English proof (translation)
Unfold `Wb`. Rewrite using `[Formalism.MainNotions.mem_orth_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨fun a => h _ (Submodule.subset_span (Or.inl ⟨a, rfl⟩)), fun a => h _ (Submodule.subset_span (Or.inr ⟨a, rfl⟩))⟩`.

Introduce and unpack `⟨h1, h2⟩ x hx`. Establish `: Submodule.span D.host.E (Set.range D.sp.hypE ∪ Set.range D.sp.hypF) ≤ LinearMap.ker ((hS D).hT.flip v)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨a, rfl⟩ | ⟨a, rfl⟩)`. Conclude with `h1 a`.

Conclude with `h2 a`. Conclude with `this hx`.
-/
theorem mem_Wb (v : (hS D).V) : v ∈ Wb D ↔
    (∀ a, (hS D).hT (D.sp.hypE a) v = 0) ∧ ∀ a, (hS D).hT (D.sp.hypF a) v = 0 := by
  unfold Wb
  rw [Formalism.MainNotions.mem_orth_iff]
  constructor
  · intro h
    exact ⟨fun a => h _ (Submodule.subset_span (Or.inl ⟨a, rfl⟩)),
      fun a => h _ (Submodule.subset_span (Or.inr ⟨a, rfl⟩))⟩
  · rintro ⟨h1, h2⟩ x hx
    have : Submodule.span D.host.E (Set.range D.sp.hypE ∪ Set.range D.sp.hypF) ≤
        LinearMap.ker ((hS D).hT.flip v) := by
      refine Submodule.span_le.2 ?_
      rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
      · exact h1 a
      · exact h2 a
    exact this hx

/- English proof (translation)
Unfold `FlagG.X at hx`. Rewrite `hx` using `[he]`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 hx`. Establish `h2` using `((mem_Wb D _).1 hw).2`. Establish `hc : ∀ b, c b = 0`.

Introduce `b`. Establish `h` using `Formalism.MainNotions.hT_swap_zero (h2 b)`. Simplify using `only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, D.sp.hyp_ef, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h`. Simplify using `using h`. Simplify using `[hc]`.
-/
theorem eq_zero_of_mem_X {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (he : F0.e = D.sp.hypE)
    {x : (hS D).V} (hx : x ∈ F0.X) (hw : x ∈ Wb D) : x = 0 := by
  unfold FlagG.X at hx
  rw [he] at hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
  have h2 := ((mem_Wb D _).1 hw).2
  have hc : ∀ b, c b = 0 := by
    intro b
    have h := Formalism.MainNotions.hT_swap_zero (h2 b)
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, D.sp.hyp_ef,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at h
    simpa using h
  simp [hc]

/- English proof (translation)
The claim follows from `(mem_Wb D _).2 ⟨fun a => Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthX a w).1, fun a => Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthX a w).2⟩`.
-/
theorem iXY_mem_Wb (w : (D.sp.X 0).V) : D.sp.iXY 0 w ∈ Wb D :=
  (mem_Wb D _).2 ⟨fun a => Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthX a w).1,
    fun a => Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthX a w).2⟩

/- English proof (translation)
The claim follows from `Submodule.smul_mem _ _ ((mem_Wb D _).2 ⟨fun a => Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthz a).1, fun a => Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthz a).2⟩)`.
-/
theorem zmOf_mem_Wb (u : D.what₂.Word) : D.zmOf u ∈ Wb D :=
  Submodule.smul_mem _ _ ((mem_Wb D _).2 ⟨fun a => Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthz a).1,
    fun a => Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthz a).2⟩)

/- English proof (translation)
Use `⟨fun hv => ?_, ?_⟩` and prove the remaining obligations. Use `swap`. Introduce and unpack `⟨w, c, rfl⟩`. Conclude with `(Wb D).add_mem (iXY_mem_Wb D _) ((Wb D).smul_mem _ (zmOf_mem_Wb D u))`. Establish `hW` using `(Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).1`.

Establish `hT' : ((Tu D u : ℕ) : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 hT`. Use `set c : D.host.E := -((hS D).hT F0.z v) / ((Tu D u : ℕ) : D.host.E) with hc`. Establish `hvz : v - c • D.zmOf u ∈ Wb D` using `(Wb D).sub_mem hv ((Wb D).smul_mem _ (zmOf_mem_Wb D u))`. Establish `h1 : v - c • D.zmOf u ∈ orth (hS D) (Xplus (lf D F0))`. Rewrite using `[Formalism.MainNotions.mem_orth_iff]`.

Use `Formalism.MainNotions.hT_zero_of_mem_Xplus F0 (fun a => ?_) ?_` and prove the remaining obligations. Rewrite using `[he]`. Conclude with `((mem_Wb D _).1 hvz).1 a`. Rewrite using `[← hz, map_sub, map_smul, F0.z_norm, smul_eq_mul, hc]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[← hW]`. Take `⟨_, ⟨w, rfl⟩, x, hx, hs⟩` from `Submodule.mem_sup.1 h1`. Establish `hx0 : x = 0`. Use `eq_zero_of_mem_X D F0 he hx ?_` and prove the remaining obligations.

Establish `: x = (v - c • D.zmOf u) - D.sp.iXY 0 w` using `by rw [← hs]; abel`. Rewrite using `[this]`. Conclude with `(Wb D).sub_mem hvz (iXY_mem_Wb D w)`. Use `⟨w, c, ?_⟩` and prove the remaining obligations. Rewrite `hs` using `[hx0, add_zero]`.

Rewrite using `[hs]`. Simplify using the standard rewrite rules.
-/
theorem mem_Wb_iff (u : D.what₂.Word) (F0 : Fb D u) (hT : Tu D u ≠ 0) (he : F0.e = D.sp.hypE)
    (hz : F0.z = D.zmOf u) (v : (hS D).V) :
    v ∈ Wb D ↔ ∃ w, ∃ c : D.host.E, v = D.sp.iXY 0 w + c • D.zmOf u := by
  refine ⟨fun hv => ?_, ?_⟩
  swap
  · rintro ⟨w, c, rfl⟩
    exact (Wb D).add_mem (iXY_mem_Wb D _) ((Wb D).smul_mem _ (zmOf_mem_Wb D u))
  have hW := (Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).1
  have hT' : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hT
  set c : D.host.E := -((hS D).hT F0.z v) / ((Tu D u : ℕ) : D.host.E) with hc
  have hvz : v - c • D.zmOf u ∈ Wb D := (Wb D).sub_mem hv ((Wb D).smul_mem _ (zmOf_mem_Wb D u))
  have h1 : v - c • D.zmOf u ∈ orth (hS D) (Xplus (lf D F0)) := by
    rw [Formalism.MainNotions.mem_orth_iff]
    refine Formalism.MainNotions.hT_zero_of_mem_Xplus F0 (fun a => ?_) ?_
    · rw [he]; exact ((mem_Wb D _).1 hvz).1 a
    · rw [← hz, map_sub, map_smul, F0.z_norm, smul_eq_mul, hc]
      field_simp
      ring
  rw [← hW] at h1
  obtain ⟨_, ⟨w, rfl⟩, x, hx, hs⟩ := Submodule.mem_sup.1 h1
  have hx0 : x = 0 := by
    refine eq_zero_of_mem_X D F0 he hx ?_
    have : x = (v - c • D.zmOf u) - D.sp.iXY 0 w := by rw [← hs]; abel
    rw [this]
    exact (Wb D).sub_mem hvz (iXY_mem_Wb D w)
  refine ⟨w, c, ?_⟩
  rw [hx0, add_zero] at hs
  rw [hs]
  simp

/- English proof (translation)
Introduce `D u F0 Λ hp _ hs ⟨he, hz⟩ hΛ L' hL'`. Establish `h` using `(GlobalTheory.Mass.RowPerp.main D u F0 he hz).2 Λ hΛ`. Take `⟨⟨h1, h2⟩, ⟨e⟩⟩` from `((GlobalTheory.Mass.CyclicGenus.main D.host.E (D.sp.X 0).V (D.sp.X 0).hT D.sp.cm.cmUnram (D.sp.X 0).herm (D.sp.X 0).nondeg (Tu D u) hp hs).2 _ _ h.1 h.2).1 hL'`. Establish `hm : 0 < D.R.m` using `lt_of_lt_of_le (by norm_num) D.R.two_le_m`. Use `ncard_glued (h := (hS D).hT) (ι := D.sp.iXY 0) (z := D.zmOf u) (B := Wb D) (hS D).herm (D.sp.iXY_isom 0 hm) (D.sp.X 0).nondeg hp.ne_zero (hz ▸ F0.z_norm) (fun w => ?_) (mem_Wb_iff D u F0 hp.ne_zero he hz) h1 h2 (GlobalTheory.Mass.CyclicGenus.cyc_of_equiv e) _ fun c h3 h4 => ?_` and prove the remaining obligations.

Use `Formalism.MainNotions.hT_swap_zero ?_` and prove the remaining obligations. Rewrite using `[D7.zmOf, map_smul, D.sp.zm_orth, smul_zero]`. Rewrite using `[← (GlobalTheory.real_places_facts D).2.2.1]`. Conclude with `GlobalTheory.NormOneSplit.card_norm_classes D.host.F D.host.E D.sp.cm _ hp hs c h3 h4`.
-/
theorem main : ∀ (D : D7) (u : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → IsBase D u F0 → IsRowLat D F0 Λ → ∀ L' ∈ Formalism.HermitianLatticesTheory.genus (D.sp.X 0).hT (L0X D Λ (lf D F0)), (glueSet D u L').Finite ∧ (glueSet D u L').ncard = (Tu D u - 1) ^ D.R.f := by
  intro D u F0 Λ hp _ hs ⟨he, hz⟩ hΛ L' hL'
  have h := (GlobalTheory.Mass.RowPerp.main D u F0 he hz).2 Λ hΛ
  obtain ⟨⟨h1, h2⟩, ⟨e⟩⟩ := ((GlobalTheory.Mass.CyclicGenus.main D.host.E (D.sp.X 0).V (D.sp.X 0).hT D.sp.cm.cmUnram
    (D.sp.X 0).herm (D.sp.X 0).nondeg (Tu D u) hp hs).2 _ _ h.1 h.2).1 hL'
  have hm : 0 < D.R.m := lt_of_lt_of_le (by norm_num) D.R.two_le_m
  refine ncard_glued (h := (hS D).hT) (ι := D.sp.iXY 0) (z := D.zmOf u) (B := Wb D) (hS D).herm
    (D.sp.iXY_isom 0 hm) (D.sp.X 0).nondeg hp.ne_zero (hz ▸ F0.z_norm) (fun w => ?_)
    (mem_Wb_iff D u F0 hp.ne_zero he hz) h1 h2 (GlobalTheory.Mass.CyclicGenus.cyc_of_equiv e) _ fun c h3 h4 => ?_
  · refine Formalism.MainNotions.hT_swap_zero ?_
    rw [D7.zmOf, map_smul, D.sp.zm_orth, smul_zero]
  · rw [← (GlobalTheory.real_places_facts D).2.2.1]
    exact GlobalTheory.NormOneSplit.card_norm_classes D.host.F D.host.E D.sp.cm _ hp hs c h3 h4

end GlobalTheory.LoopC.GlueCount

end
