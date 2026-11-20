import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicEmbeddingValuationNorm

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.FlatCM

namespace GlobalTheory.LieIndex

/- English proof (translation)
Use `choose c hc hs using fun k => (Finsupp.mem_span_iff_linearCombination R S (w k)).1 (hw k) |>.imp fun c h => And.intro trivial h`. Establish `: w = fun k => ∑ s ∈ (c k).support, c k s • (s : M)` using `funext fun k => by`. Rewrite using `[← hs k, Finsupp.linearCombination_apply, Finsupp.sum]`. Rewrite using `[this, f.map_sum_finset]`. Use `Submodule.sum_mem _ fun r _ => ?_` and prove the remaining obligations.

Rewrite using `[f.map_smul_univ]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun k => (r k).2, rfl⟩)`.
-/
theorem multilinear_mem_span {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {n : ℕ} (f : MultilinearMap R (fun _ : Fin n => M) N) {S : Set M} {w : Fin n → M}
    (hw : ∀ k, w k ∈ Submodule.span R S) :
    f w ∈ Submodule.span R {z | ∃ y : Fin n → M, (∀ k, y k ∈ S) ∧ z = f y} := by
  choose c hc hs using fun k => (Finsupp.mem_span_iff_linearCombination R S (w k)).1 (hw k) |>.imp fun c h =>
    And.intro trivial h
  have : w = fun k => ∑ s ∈ (c k).support, c k s • (s : M) := funext fun k => by
    rw [← hs k, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [this, f.map_sum_finset]
  refine Submodule.sum_mem _ fun r _ => ?_
  rw [f.map_smul_univ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun k => (r k).2, rfl⟩)

section Index

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Distinguish the cases in `h0 : B = ⊥`. Substitute `h0` using the available equality. Conclude with `hAB.trans bot_le`. Establish `hω0 : ω ≠ 0`. Introduce and unpack `rfl`.

Use `h0 (eq_bot_iff.2 fun b hb => ?_)` and prove the remaining obligations. Take `⟨c, rfl⟩` from `hω b hb`. Simplify using the standard rewrite rules. Set `f : K →ₗ[𝓞 K] V` to `(LinearMap.toSpanSingleton K V ω).restrictScalars (𝓞 K)`. Establish `hf : ∀ c, f c = c • ω` using `fun _ => rfl`.

Establish `hinj : Function.Injective f` using `smul_left_injective K hω0`. Establish `hmap : (B.comap f).map f = B` using `Submodule.map_comap_eq_self fun b hb => hω b hb`. Establish `hfg : (B.comap f).FG` using `Submodule.fg_of_fg_map_injective f hinj (hmap.symm ▸ hB)`. Set `I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K` to `⟨B.comap f, FractionalIdeal.isFractional_of_fg hfg⟩`. Establish `hI : I ≠ 0` using `fun h => h0 (by`.

Establish `: B.comap f = ⊥` using `(congrArg (fun J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K => (J : Submodule (𝓞 K) K)) h).trans FractionalIdeal.coe_zero`. Rewrite using `[← hmap, this, Submodule.map_bot])`. Establish `hint : ∀ b : K, b • ω ∈ B → ∀ c ∈ I⁻¹, ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = b * c` using `fun b hb c hc => by`. Use `FractionalIdeal.mul_mem_mul (show b ∈ I from hb) hc` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel₀ hI]`.

Conclude with `(FractionalIdeal.mem_one_iff _).1 this`. Introduce `a ha`. Take `⟨a, rfl⟩` from `hω a (hAB ha)`. Establish `h1 : (1 : K) ∈ I * I⁻¹`. Rewrite using `[mul_inv_cancel₀ hI]`.

Conclude with `FractionalIdeal.one_mem_one _`. Rewrite using `[← one_mul a]`. Use `FractionalIdeal.mul_induction_on (C := fun t => (t * a) • ω ∈ A.colon B • B) h1 (fun b hb c hc => ?_) fun x y hx hy => by rw [add_mul, add_smul]; exact add_mem hx hy` and prove the remaining obligations. Take `⟨r, hr⟩` from `hint a (hAB ha) c hc`. Establish `e : (b * c * a) • ω = r • b • ω`.

Rewrite using `[← algebraMap_smul K r, hr, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `Submodule.smul_mem_smul (Submodule.mem_colon.2 fun z hz => ?_) hb` and prove the remaining obligations.

Take `⟨z, rfl⟩` from `hω z hz`. Take `⟨s, hs⟩` from `hint z hz c hc`. Establish `e' : r • z • ω = s • a • ω`. Rewrite using `[← algebraMap_smul K r, ← algebraMap_smul K s, hr, hs, smul_smul, smul_smul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e']`. Conclude with `A.smul_mem _ ha`.
-/
theorem le_colon_smul {A B : Submodule (𝓞 K) V} (hAB : A ≤ B) (hB : B.FG) (ω : V) (hω : ∀ b ∈ B, ∃ c : K, c • ω = b) :
    A ≤ A.colon B • B := by
  by_cases h0 : B = ⊥
  · subst h0
    exact hAB.trans bot_le
  have hω0 : ω ≠ 0 := by
    rintro rfl
    refine h0 (eq_bot_iff.2 fun b hb => ?_)
    obtain ⟨c, rfl⟩ := hω b hb
    simp
  let f : K →ₗ[𝓞 K] V := (LinearMap.toSpanSingleton K V ω).restrictScalars (𝓞 K)
  have hf : ∀ c, f c = c • ω := fun _ => rfl
  have hinj : Function.Injective f := smul_left_injective K hω0
  have hmap : (B.comap f).map f = B := Submodule.map_comap_eq_self fun b hb => hω b hb
  have hfg : (B.comap f).FG := Submodule.fg_of_fg_map_injective f hinj (hmap.symm ▸ hB)
  let I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K := ⟨B.comap f, FractionalIdeal.isFractional_of_fg hfg⟩
  have hI : I ≠ 0 := fun h => h0 (by
    have : B.comap f = ⊥ := (congrArg (fun J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K =>
      (J : Submodule (𝓞 K) K)) h).trans FractionalIdeal.coe_zero
    rw [← hmap, this, Submodule.map_bot])
  have hint : ∀ b : K, b • ω ∈ B → ∀ c ∈ I⁻¹, ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = b * c := fun b hb c hc => by
    have := FractionalIdeal.mul_mem_mul (show b ∈ I from hb) hc
    rw [mul_inv_cancel₀ hI] at this
    exact (FractionalIdeal.mem_one_iff _).1 this
  intro a ha
  obtain ⟨a, rfl⟩ := hω a (hAB ha)
  have h1 : (1 : K) ∈ I * I⁻¹ := by
    rw [mul_inv_cancel₀ hI]
    exact FractionalIdeal.one_mem_one _
  rw [← one_mul a]
  refine FractionalIdeal.mul_induction_on (C := fun t => (t * a) • ω ∈ A.colon B • B) h1 (fun b hb c hc => ?_)
    fun x y hx hy => by rw [add_mul, add_smul]; exact add_mem hx hy
  obtain ⟨r, hr⟩ := hint a (hAB ha) c hc
  have e : (b * c * a) • ω = r • b • ω := by
    rw [← algebraMap_smul K r, hr, smul_smul]
    congr 1
    ring
  rw [e]
  refine Submodule.smul_mem_smul (Submodule.mem_colon.2 fun z hz => ?_) hb
  obtain ⟨z, rfl⟩ := hω z hz
  obtain ⟨s, hs⟩ := hint z hz c hc
  have e' : r • z • ω = s • a • ω := by
    rw [← algebraMap_smul K r, ← algebraMap_smul K s, hr, hs, smul_smul, smul_smul]
    congr 1
    ring
  rw [e']
  exact A.smul_mem _ ha

/- English proof (translation)
The claim follows from `Submodule.span_mono fun _ ⟨y, hy, e⟩ => ⟨y, fun k => h (hy k), e⟩`.
-/
theorem detSpan_mono (m : ℕ) {L N : Submodule (𝓞 K) V} (h : N ≤ L) : detSpan K m N ≤ detSpan K m L :=
  Submodule.span_mono fun _ ⟨y, hy, e⟩ => ⟨y, fun k => h (hy k), e⟩

/- English proof (translation)
Take `⟨S, rfl⟩` from `h`. Establish `hfin : {z | ∃ y : Fin m → V, (∀ k, y k ∈ (S : Set V)) ∧ z = exteriorPower.ιMulti K m y}.Finite` using `((Set.Finite.pi' fun _ : Fin m => S.finite_toSet).image (exteriorPower.ιMulti K m)).subset fun _ ⟨y, hy, e⟩ => ⟨y, hy, e.symm⟩`. Use `Submodule.fg_def.2 ⟨_, hfin, le_antisymm (Submodule.span_mono fun _ ⟨y, hy, e⟩ => ⟨y, fun k => Submodule.subset_span (hy k), e⟩) (Submodule.span_le.2 ?_)⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `multilinear_mem_span ((exteriorPower.ιMulti K m).toMultilinearMap.restrictScalars (𝓞 K)) hy`.
-/
theorem fg_detSpan (m : ℕ) {L : Submodule (𝓞 K) V} (h : L.FG) : (detSpan K m L).FG := by
  obtain ⟨S, rfl⟩ := h
  have hfin : {z | ∃ y : Fin m → V, (∀ k, y k ∈ (S : Set V)) ∧ z = exteriorPower.ιMulti K m y}.Finite :=
    ((Set.Finite.pi' fun _ : Fin m => S.finite_toSet).image (exteriorPower.ιMulti K m)).subset
      fun _ ⟨y, hy, e⟩ => ⟨y, hy, e.symm⟩
  refine Submodule.fg_def.2 ⟨_, hfin, le_antisymm (Submodule.span_mono fun _ ⟨y, hy, e⟩ =>
    ⟨y, fun k => Submodule.subset_span (hy k), e⟩) (Submodule.span_le.2 ?_)⟩
  rintro _ ⟨y, hy, rfl⟩
  exact multilinear_mem_span ((exteriorPower.ιMulti K m).toMultilinearMap.restrictScalars (𝓞 K)) hy

/- English proof (translation)
Use `haveI : Module.Finite K (Submodule.span K (L : Set V)) := by`. Take `⟨S, rfl⟩` from `hL`. Rewrite using `[Submodule.span_span_of_tower]`. Conclude with `Module.Finite.span_of_finite K S.finite_toSet`. Take `⟨ω, hω⟩` from `(finrank_le_one_iff (K := K) (V := ⋀[K]^m (Submodule.span K (L : Set V)))).1 (by`.

Rewrite using `[exteriorPower.finrank_eq]`. Break down `hr.eq_or_lt with e | e` into its components or cases. Rewrite using `[e, Nat.choose_self]`. Rewrite using `[Nat.choose_eq_zero_of_lt e]`. Conclude with `zero_le_one)`.

Use `le_colon_smul (detSpan_mono m h) (fg_detSpan m hL) (exteriorPower.map m (Submodule.span K (L : Set V)).subtype ω) fun b hb => ?_` and prove the remaining obligations. Establish `: detSpan K m L ≤ (LinearMap.range (exteriorPower.map m (Submodule.span K (L : Set V)).subtype)).restrictScalars (𝓞 K)` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `⟨exteriorPower.ιMulti K m fun k => ⟨y k, Submodule.subset_span (hy k)⟩, by`. Rewrite using `[exteriorPower.map_apply_ιMulti]`.

Use the proof step `rfl⟩)`. Take `⟨z, rfl⟩` from `this hb`. Take `⟨c, rfl⟩` from `hω z`. Conclude with `⟨c, (map_smul _ _ _).symm⟩`.
-/
theorem detSpan_le_idx_smul (m : ℕ) {L N : Submodule (𝓞 K) V} (h : N ≤ L) (hL : L.FG)
    (hr : Module.finrank K (Submodule.span K (L : Set V)) ≤ m) : detSpan K m N ≤ idx K m L N • detSpan K m L := by
  haveI : Module.Finite K (Submodule.span K (L : Set V)) := by
    obtain ⟨S, rfl⟩ := hL
    rw [Submodule.span_span_of_tower]
    exact Module.Finite.span_of_finite K S.finite_toSet
  obtain ⟨ω, hω⟩ := (finrank_le_one_iff (K := K) (V := ⋀[K]^m (Submodule.span K (L : Set V)))).1 (by
    rw [exteriorPower.finrank_eq]
    rcases hr.eq_or_lt with e | e
    · rw [e, Nat.choose_self]
    · rw [Nat.choose_eq_zero_of_lt e]
      exact zero_le_one)
  refine le_colon_smul (detSpan_mono m h) (fg_detSpan m hL)
    (exteriorPower.map m (Submodule.span K (L : Set V)).subtype ω) fun b hb => ?_
  have : detSpan K m L ≤ (LinearMap.range (exteriorPower.map m (Submodule.span K (L : Set V)).subtype)).restrictScalars
      (𝓞 K) := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨exteriorPower.ιMulti K m fun k => ⟨y k, Submodule.subset_span (hy k)⟩, by
      rw [exteriorPower.map_apply_ιMulti]; rfl⟩)
  obtain ⟨z, rfl⟩ := this hb
  obtain ⟨c, rfl⟩ := hω z
  exact ⟨c, (map_smul _ _ _).symm⟩

/- English proof (translation)
Take `⟨S, rfl⟩` from `hL`. Establish `h1 : ∀ s ∈ S, ∃ r : nonZeroDivisors (𝓞 K), r • s ∈ N` using `fun s hs => by`. Simplify using `using multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K (N : Set V) s (h (Submodule.subset_span hs))`. Use `choose! r hr using h1`. Establish `h2 : ∀ y ∈ Submodule.span (𝓞 K) (S : Set V), (∏ s ∈ S, (r s : 𝓞 K)) • y ∈ N` using `fun y hy => by classical`.

Establish `: Submodule.span (𝓞 K) (S : Set V) ≤ N.comap (LinearMap.lsmul (𝓞 K) V (∏ s ∈ S, (r s : 𝓞 K)))` using `Submodule.span_le.2 fun s hs => by`. Express the relevant statement in the definitionally equal form `(∏ s ∈ S, (r s : 𝓞 K)) • s ∈ N`. Rewrite using `[← Finset.prod_erase_mul _ _ hs, mul_smul]`. Conclude with `N.smul_mem _ (hr s hs)`. Conclude with `this hy`.

Use `(Submodule.ne_bot_iff _).2 ⟨(∏ s ∈ S, (r s : 𝓞 K)) ^ m, Submodule.mem_colon.2 fun z hz => ?_, pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun s _ => nonZeroDivisors.coe_ne_zero _)⟩` and prove the remaining obligations. Establish `: detSpan K m (Submodule.span (𝓞 K) (S : Set V)) ≤ (detSpan K m N).comap (LinearMap.lsmul (𝓞 K) _ ((∏ s ∈ S, (r s : 𝓞 K)) ^ m))` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Use `Submodule.subset_span ⟨_, fun k => h2 _ (hy k), ?_⟩` and prove the remaining obligations. Use `((exteriorPower.ιMulti K m).toMultilinearMap.restrictScalars (𝓞 K)).map_smul_univ (fun _ => ∏ s ∈ S, (r s : 𝓞 K)) y` as an intermediate fact.

Simplify using `using this.symm)`. Conclude with `this hz`.
-/
theorem idx_ne_bot (m : ℕ) {L N : Submodule (𝓞 K) V} (hL : L.FG) (h : (L : Set V) ⊆ Submodule.span K (N : Set V)) :
    idx K m L N ≠ ⊥ := by
  obtain ⟨S, rfl⟩ := hL
  have h1 : ∀ s ∈ S, ∃ r : nonZeroDivisors (𝓞 K), r • s ∈ N := fun s hs => by
    simpa using multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K (N : Set V) s
      (h (Submodule.subset_span hs))
  choose! r hr using h1
  have h2 : ∀ y ∈ Submodule.span (𝓞 K) (S : Set V), (∏ s ∈ S, (r s : 𝓞 K)) • y ∈ N := fun y hy => by
    classical
    have : Submodule.span (𝓞 K) (S : Set V) ≤ N.comap (LinearMap.lsmul (𝓞 K) V (∏ s ∈ S, (r s : 𝓞 K))) :=
      Submodule.span_le.2 fun s hs => by
        change (∏ s ∈ S, (r s : 𝓞 K)) • s ∈ N
        rw [← Finset.prod_erase_mul _ _ hs, mul_smul]
        exact N.smul_mem _ (hr s hs)
    exact this hy
  refine (Submodule.ne_bot_iff _).2 ⟨(∏ s ∈ S, (r s : 𝓞 K)) ^ m, Submodule.mem_colon.2 fun z hz => ?_,
    pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun s _ => nonZeroDivisors.coe_ne_zero _)⟩
  have : detSpan K m (Submodule.span (𝓞 K) (S : Set V)) ≤
      (detSpan K m N).comap (LinearMap.lsmul (𝓞 K) _ ((∏ s ∈ S, (r s : 𝓞 K)) ^ m)) := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    refine Submodule.subset_span ⟨_, fun k => h2 _ (hy k), ?_⟩
    have := ((exteriorPower.ιMulti K m).toMultilinearMap.restrictScalars (𝓞 K)).map_smul_univ
      (fun _ => ∏ s ∈ S, (r s : 𝓞 K)) y
    simpa using this.symm)
  exact this hz

variable {C O W : Type} [Field C] [CommRing O] [Algebra O C] [AddCommGroup W] [Module C W] [Module O W]
  [IsScalarTower O C W]

/- English proof (translation)
Take `⟨π, hπ⟩` from `(Fintype.linearCombination C y).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 (linearIndependent_iff_injective_fintypeLinearCombination.1 hy))`. Use `replace hπ : ∀ c : Fin n → C, π (∑ b, c b • y b) = c := fun c => LinearMap.congr_fun hπ c`. Set `D : W [⋀^Fin n]→ₗ[C] C` to `Matrix.detRowAlternating.compLinearMap π`. Establish `hD : ∀ w, D w = Matrix.det (Matrix.of fun a => π (w a))` using `fun _ => rfl`. Establish `hle : ∀ z w : Fin n → W, (∀ a, w a ∈ Submodule.span O (Set.range z)) → ∃ c : O, D w = c • D z` using `fun z w hw => by choose c hc using fun a => (Submodule.mem_span_range_iff_exists_fun O).1 (hw a)`.

Use `⟨(Matrix.of c).det, ?_⟩` and prove the remaining obligations. Rewrite using `[hD, hD, Algebra.smul_def, RingHom.map_det, ← Matrix.det_mul]`. Use `congr 1`. Use extensionality with `a t`. Rewrite using `[Matrix.of_apply, ← hc, map_sum, Finset.sum_apply, Matrix.mul_apply]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← algebraMap_smul C (c a b), map_smul]`. Both sides reduce to the same expression. Establish `hDy : D y = 1`. Rewrite using `[hD, ← Matrix.det_one (n := Fin n)]`.

Use `congr 1`. Use extensionality with `a t`. Use `hπ (Pi.single a 1)` as an intermediate fact. Simplify using `only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this`. Simplify using `[this, Pi.single_apply, Matrix.one_apply, eq_comm]`.

Establish `hDm : D (fun a => ∑ b, m a b • y b) = m.det`. Rewrite using `[hD]`. Use `congr 1`. Use extensionality with `a t`. Simplify using `only [Matrix.of_apply, hπ]`.

Use `letI : Algebra K C := i.toAlgebra`. Set `g : V →ₗ[K] (Fin n → C)` to `⟨⟨fun x => π (γ x), fun _ _ => by simp⟩, fun c x => by`. Express the relevant statement in the definitionally equal form `π (γ (c • x)) = i c • π (γ x)`. Rewrite using `[γ.map_smulₛₗ, map_smul]⟩`. Set `δ : (Fin n → C) [⋀^Fin n]→ₗ[K] C` to `⟨Matrix.detRowAlternating.toMultilinearMap.restrictScalars K, Matrix.detRowAlternating.map_eq_zero_of_eq'⟩`.

Set `Δ : ⋀[K]^n V →ₗ[K] C` to `exteriorPower.alternatingMapLinearEquiv (δ.compLinearMap g)`. Establish `hΔ : ∀ x, Δ (exteriorPower.ιMulti K n x) = D fun a => γ (x a)` using `fun x => exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _`. Establish `hΔs : ∀ (r : 𝓞 K) (z : ⋀[K]^n V), Δ (r • z) = j r • Δ z` using `fun r z => by`. Rewrite using `[show r • z = (r : K) • z from (algebraMap_smul K r z).symm, map_smul, Algebra.smul_def, Algebra.smul_def, hj]`. Both sides reduce to the same expression.

Establish `up : ∀ (M : Submodule (𝓞 K) V) (z : Fin n → W), Submodule.span O (Set.range z) = Submodule.span O (γ '' M) → Submodule.span O (Δ '' detSpan K n M) = Submodule.span O {D z}` using `fun M z hz => by`. Use `le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨t, ht, rfl⟩`. Proceed by induction on `ht using Submodule.span_induction with`. Consider the case `mem t ht`.

Take `⟨x, hx, rfl⟩` from `ht`. Take `⟨c, hc⟩` from `hle z (fun a => γ (x a)) fun a => hz.ge (Submodule.subset_span ⟨_, hx a, rfl⟩)`. Conclude with `Submodule.mem_span_singleton.2 ⟨c, by rw [hΔ, hc]⟩`. Consider the case `zero => simp`. Consider the case `add _ _ _ _ h₁ h₂ => rw [map_add]`.

Conclude with `add_mem h₁ h₂`. Consider the case `smul r _ _ h₁ => exact Set.mem_of_eq_of_mem (hΔs _ _) (Submodule.smul_mem _ _ h₁)`. Introduce and unpack `_ rfl`. Use `Submodule.span_mono ?_ (multilinear_mem_span (D.toMultilinearMap.restrictScalars O) fun a => hz.le (Submodule.subset_span ⟨a, rfl⟩))` and prove the remaining obligations. Introduce and unpack `_ ⟨w, hw, rfl⟩`.

Use `choose x hx e using hw`. Conclude with `⟨_, Submodule.subset_span ⟨x, hx, rfl⟩, by rw [hΔ, funext e]; rfl⟩`. Establish `hL'` using `up L y hyL`. Establish `hN'` using `up N _ hN`. Rewrite `hL'` using `[hDy]`.

Rewrite `hN'` using `[hDm]`. Establish `hone : ∀ t ∈ detSpan K n L, ∃ c : O, algebraMap O C c = Δ t` using `fun t ht => by`. Take `⟨c, hc⟩` from `Submodule.mem_span_singleton.1 (hL'.le (Submodule.subset_span ⟨t, ht, rfl⟩))`. Conclude with `⟨c, by rw [← hc, Algebra.smul_def, mul_one]⟩`. Establish `hm : m.det ∈ Submodule.map (Algebra.linearMap O C) ((idx K n L N).map j)`.

Use `(hN'.ge.trans (Submodule.span_le.2 ?_)) (Submodule.mem_span_singleton_self _)` and prove the remaining obligations. Introduce and unpack `_ ⟨t, ht, rfl⟩`. Use `Submodule.smul_induction_on (p := fun t => Δ t ∈ Submodule.map (Algebra.linearMap O C) ((idx K n L N).map j)) (detSpan_le_idx_smul n h hL hr ht) (fun r hr t ht => ?_) fun _ _ h₁ h₂ => by rw [map_add]; exact add_mem h₁ h₂` and prove the remaining obligations. Take `⟨c, hc⟩` from `hone t ht`. Conclude with `⟨j r * c, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem j hr), by`.

Use `Eq.trans ?_ (hΔs _ _).symm` and prove the remaining obligations. Rewrite using `[← hc, Algebra.smul_def, Algebra.linearMap_apply, map_mul]⟩`. Take `⟨d, hd, e⟩` from `hm`. Use `⟨d, e, le_antisymm (Ideal.map_le_iff_le_comap.2 fun r hr => ?_) ((Ideal.span_singleton_le_iff_mem _).2 hd)⟩` and prove the remaining obligations. Establish `: Submodule.span O (Δ '' detSpan K n L) ≤ (Submodule.span O {m.det}).comap (LinearMap.lsmul O C (j r))` using `Submodule.span_le.2 (by`.

Introduce and unpack `_ ⟨t, ht, rfl⟩`. Conclude with `hN'.le (Submodule.subset_span ⟨_, Submodule.mem_colon.1 hr t ht, hΔs r t⟩))`. Take `⟨c, hc⟩` from `Submodule.mem_span_singleton.1 (this (hL'.ge (Submodule.mem_span_singleton_self _)))`. Use `Ideal.mem_span_singleton'.2 ⟨c, hO ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, show algebraMap O C d = m.det from e, ← Algebra.smul_def, hc]`.

Simplify using `[Algebra.smul_def]`.
-/
theorem map_idx_eq (hO : Function.Injective (algebraMap O C)) {i : K →+* C} {j : 𝓞 K →+* O}
    (hj : ∀ a, algebraMap O C (j a) = i a) (γ : V →ₛₗ[i] W) {n : ℕ} {L N : Submodule (𝓞 K) V} (h : N ≤ L) (hL : L.FG)
    (hr : Module.finrank K (Submodule.span K (L : Set V)) ≤ n) {y : Fin n → W} (hy : LinearIndependent C y)
    (hyL : Submodule.span O (Set.range y) = Submodule.span O (γ '' L)) (m : Matrix (Fin n) (Fin n) C)
    (hN : Submodule.span O (Set.range fun a => ∑ b, m a b • y b) = Submodule.span O (γ '' N)) :
    ∃ d : O, algebraMap O C d = m.det ∧ (idx K n L N).map j = Ideal.span {d} := by
  obtain ⟨π, hπ⟩ := (Fintype.linearCombination C y).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (linearIndependent_iff_injective_fintypeLinearCombination.1 hy))
  replace hπ : ∀ c : Fin n → C, π (∑ b, c b • y b) = c := fun c => LinearMap.congr_fun hπ c
  let D : W [⋀^Fin n]→ₗ[C] C := Matrix.detRowAlternating.compLinearMap π
  have hD : ∀ w, D w = Matrix.det (Matrix.of fun a => π (w a)) := fun _ => rfl
  have hle : ∀ z w : Fin n → W, (∀ a, w a ∈ Submodule.span O (Set.range z)) → ∃ c : O, D w = c • D z := fun z w hw => by
    choose c hc using fun a => (Submodule.mem_span_range_iff_exists_fun O).1 (hw a)
    refine ⟨(Matrix.of c).det, ?_⟩
    rw [hD, hD, Algebra.smul_def, RingHom.map_det, ← Matrix.det_mul]
    congr 1
    ext a t
    rw [Matrix.of_apply, ← hc, map_sum, Finset.sum_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← algebraMap_smul C (c a b), map_smul]
    rfl
  have hDy : D y = 1 := by
    rw [hD, ← Matrix.det_one (n := Fin n)]
    congr 1
    ext a t
    have := hπ (Pi.single a 1)
    simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    simp [this, Pi.single_apply, Matrix.one_apply, eq_comm]
  have hDm : D (fun a => ∑ b, m a b • y b) = m.det := by
    rw [hD]
    congr 1
    ext a t
    simp only [Matrix.of_apply, hπ]
  letI : Algebra K C := i.toAlgebra
  let g : V →ₗ[K] (Fin n → C) := ⟨⟨fun x => π (γ x), fun _ _ => by simp⟩, fun c x => by
    change π (γ (c • x)) = i c • π (γ x)
    rw [γ.map_smulₛₗ, map_smul]⟩
  let δ : (Fin n → C) [⋀^Fin n]→ₗ[K] C :=
    ⟨Matrix.detRowAlternating.toMultilinearMap.restrictScalars K, Matrix.detRowAlternating.map_eq_zero_of_eq'⟩
  let Δ : ⋀[K]^n V →ₗ[K] C := exteriorPower.alternatingMapLinearEquiv (δ.compLinearMap g)
  have hΔ : ∀ x, Δ (exteriorPower.ιMulti K n x) = D fun a => γ (x a) := fun x =>
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _
  have hΔs : ∀ (r : 𝓞 K) (z : ⋀[K]^n V), Δ (r • z) = j r • Δ z := fun r z => by
    rw [show r • z = (r : K) • z from (algebraMap_smul K r z).symm, map_smul, Algebra.smul_def, Algebra.smul_def, hj]
    rfl
  have up : ∀ (M : Submodule (𝓞 K) V) (z : Fin n → W), Submodule.span O (Set.range z) = Submodule.span O (γ '' M) →
      Submodule.span O (Δ '' detSpan K n M) = Submodule.span O {D z} := fun M z hz => by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨t, ht, rfl⟩
      induction ht using Submodule.span_induction with
      | mem t ht =>
        obtain ⟨x, hx, rfl⟩ := ht
        obtain ⟨c, hc⟩ := hle z (fun a => γ (x a)) fun a => hz.ge (Submodule.subset_span ⟨_, hx a, rfl⟩)
        exact Submodule.mem_span_singleton.2 ⟨c, by rw [hΔ, hc]⟩
      | zero => simp
      | add _ _ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
      | smul r _ _ h₁ => exact Set.mem_of_eq_of_mem (hΔs _ _) (Submodule.smul_mem _ _ h₁)
    · rintro _ rfl
      refine Submodule.span_mono ?_ (multilinear_mem_span (D.toMultilinearMap.restrictScalars O)
        fun a => hz.le (Submodule.subset_span ⟨a, rfl⟩))
      rintro _ ⟨w, hw, rfl⟩
      choose x hx e using hw
      exact ⟨_, Submodule.subset_span ⟨x, hx, rfl⟩, by rw [hΔ, funext e]; rfl⟩
  have hL' := up L y hyL
  have hN' := up N _ hN
  rw [hDy] at hL'
  rw [hDm] at hN'
  have hone : ∀ t ∈ detSpan K n L, ∃ c : O, algebraMap O C c = Δ t := fun t ht => by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hL'.le (Submodule.subset_span ⟨t, ht, rfl⟩))
    exact ⟨c, by rw [← hc, Algebra.smul_def, mul_one]⟩
  have hm : m.det ∈ Submodule.map (Algebra.linearMap O C) ((idx K n L N).map j) := by
    refine (hN'.ge.trans (Submodule.span_le.2 ?_)) (Submodule.mem_span_singleton_self _)
    rintro _ ⟨t, ht, rfl⟩
    refine Submodule.smul_induction_on (p := fun t => Δ t ∈ Submodule.map (Algebra.linearMap O C) ((idx K n L N).map j))
      (detSpan_le_idx_smul n h hL hr ht) (fun r hr t ht => ?_) fun _ _ h₁ h₂ => by rw [map_add]; exact add_mem h₁ h₂
    obtain ⟨c, hc⟩ := hone t ht
    exact ⟨j r * c, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem j hr), by
      refine Eq.trans ?_ (hΔs _ _).symm
      rw [← hc, Algebra.smul_def, Algebra.linearMap_apply, map_mul]⟩
  obtain ⟨d, hd, e⟩ := hm
  refine ⟨d, e, le_antisymm (Ideal.map_le_iff_le_comap.2 fun r hr => ?_) ((Ideal.span_singleton_le_iff_mem _).2 hd)⟩
  have : Submodule.span O (Δ '' detSpan K n L) ≤ (Submodule.span O {m.det}).comap (LinearMap.lsmul O C (j r)) :=
    Submodule.span_le.2 (by
      rintro _ ⟨t, ht, rfl⟩
      exact hN'.le (Submodule.subset_span ⟨_, Submodule.mem_colon.1 hr t ht, hΔs r t⟩))
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (this (hL'.ge (Submodule.mem_span_singleton_self _)))
  refine Ideal.mem_span_singleton'.2 ⟨c, hO ?_⟩
  rw [map_mul, show algebraMap O C d = m.det from e, ← Algebra.smul_def, hc]
  simp [Algebra.smul_def]

end Index

/- English proof (translation)
Use `letI : Algebra (𝓞 K) O := j.toAlgebra`. Use `haveI : IsDomain O := hO.isDomain (algebraMap O C)`. Use `haveI : FaithfulSMul (𝓞 K) O := (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b h => by`. Use `congrArg (algebraMap O C) h` as an intermediate fact. Conclude with `RingOfIntegers.coe_injective (i.injective ((hj a).symm.trans (this.trans (hj b))))`.

Take `⟨m, s, g, hg⟩` from `Submodule.mem_span_set'.1 hw`. Use `choose l hl hlg using fun k => (g k).2`. Take `⟨k, a, y, h₁, h₂⟩` from `Module.Flat.exists_factorization_of_comp_eq_zero_of_free (R := 𝓞 K) (M := O) (f := (LinearMap.ker (Fintype.linearCombination (𝓞 K) s)).subtype) (x := Fintype.linearCombination (𝓞 K) s) (LinearMap.ext fun z => z.2)`. Establish `hs : ∀ t, algebraMap O C (s t) = ∑ u, i (a (Pi.single t 1) u : 𝓞 K) * algebraMap O C (y (Finsupp.single u 1))` using `fun t => by`. Use `LinearMap.congr_fun h₁ (Pi.single t 1)` as an intermediate fact.

Rewrite `this` using `[Fintype.linearCombination_apply_single, one_smul, LinearMap.comp_apply, ← Finsupp.univ_sum_single (a (Pi.single t 1)), map_sum]`. Rewrite using `[this, map_sum]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Rewrite using `[← Finsupp.smul_single_one, map_smul, Algebra.smul_def, map_mul, ← hj]`. Both sides reduce to the same expression.

Establish `rel : ∀ x : Fin m → K, ∑ t, algebraMap O C (s t) * i (x t) = 0 → ∀ u, ∑ t, ((a (Pi.single t 1) u : 𝓞 K) : K) * x t = 0` using `fun x hx u => by`. Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) x`. Use `choose z hz using hd`. Use `replace hz : ∀ t, (z t : K) = ((d : 𝓞 K) : K) * x t := fun t => (hz t).trans (Algebra.smul_def _ _)`. Establish `h₃ : a z = 0` using `LinearMap.congr_fun h₂ ⟨z, hO (by`.

Rewrite using `[Fintype.linearCombination_apply, map_sum, map_zero, ← mul_zero (i (d : 𝓞 K)), ← hx, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul, show algebraMap O C (algebraMap (𝓞 K) O (z t)) = i (z t) from hj _, hz, map_mul]`. Use the proof step `ring)⟩`. Rewrite `h₃` using `[← Finset.univ_sum_single z, map_sum]`.

Establish `h₄` using `congrArg (fun f : Fin k →₀ 𝓞 K => algebraMap (𝓞 K) K (f u)) h₃`. Simplify using `only [Finsupp.finset_sum_apply, map_sum, Finsupp.zero_apply, map_zero] at h₄`. Use `mul_left_cancel₀ (a := ((d : 𝓞 K) : K)) (RingOfIntegers.coe_ne_zero_iff.2 (nonZeroDivisors.coe_ne_zero d)) ?_` and prove the remaining obligations. Rewrite using `[mul_zero, Finset.mul_sum, ← h₄]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations.

Rewrite using `[show Pi.single t (z t) = z t • (Pi.single t 1 : Fin m → 𝓞 K) by rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, show algebraMap (𝓞 K) K (z t) = _ from hz t]`. Express the relevant statement in the definitionally equal form `_ = _ * ((a (Pi.single t 1) u : 𝓞 K) : K)`. Expand and normalize the polynomial expressions, which then agree. Establish `hc : ∀ b, w b = ∑ t, algebraMap O C (s t) * i (l t b)` using `fun b => by`. Rewrite using `[← hg, Finset.sum_apply]`.

Conclude with `Finset.sum_congr rfl fun t _ => by rw [← hlg t, Pi.smul_apply, Algebra.smul_def]; rfl`. Establish `hsum : ∀ u b, (∑ t, a (Pi.single t 1) u • l t) b = ∑ t, ((a (Pi.single t 1) u : 𝓞 K) : K) * l t b` using `fun u b => by`. Rewrite using `[Finset.sum_apply]`. Both sides reduce to the same expression. Establish `e : w = ∑ u, y (Finsupp.single u 1) • (i ∘ (∑ t, a (Pi.single t 1) u • l t))` using `funext fun b => by`.

Rewrite using `[hc, Finset.sum_apply]`. Simplify using `only [hs, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, Function.comp_apply, hsum, Algebra.smul_def, map_sum, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun t _ => by rw [map_mul]; ring`. Rewrite using `[e]`. Use `Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨Λ.sum_mem fun t _ => Λ.smul_mem _ (hl t), fun α => funext fun b => ?_⟩, rfl⟩)` and prove the remaining obligations. Establish `h₅` using `rel (fun t => (A α).mulVec (l t) b) (by`. Establish `h₆` using `congrFun (hA α) b`.

Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, hc, Finset.mul_sum, map_sum, map_mul, Pi.zero_apply] at h₆ ⊢`. Rewrite using `[← h₆, Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring) u`. Simplify using `only [Matrix.mulVec, dotProduct, hsum, Finset.mul_sum, Pi.zero_apply] at h₅ ⊢`. Rewrite using `[← h₅, Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem mem_span_solutions {K C O : Type} [Field K] [NumberField K] [Field C] [CommRing O] [Algebra O C]
    (hO : Function.Injective (algebraMap O C)) {i : K →+* C} {j : 𝓞 K →+* O} (hj : ∀ a, algebraMap O C (j a) = i a)
    {n : ℕ} (Λ : Submodule (𝓞 K) (Fin n → K)) {ι : Type} (A : ι → Matrix (Fin n) (Fin n) K) {w : Fin n → C}
    (hw : w ∈ Submodule.span O ((fun c => i ∘ c) '' (Λ : Set (Fin n → K)))) (hA : ∀ α, ((A α).map i).mulVec w = 0) :
    w ∈ Submodule.span O ((fun c => i ∘ c) '' {c | c ∈ Λ ∧ ∀ α, (A α).mulVec c = 0}) := by
  letI : Algebra (𝓞 K) O := j.toAlgebra
  haveI : IsDomain O := hO.isDomain (algebraMap O C)
  haveI : FaithfulSMul (𝓞 K) O := (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b h => by
    have := congrArg (algebraMap O C) h
    exact RingOfIntegers.coe_injective (i.injective ((hj a).symm.trans (this.trans (hj b))))
  obtain ⟨m, s, g, hg⟩ := Submodule.mem_span_set'.1 hw
  choose l hl hlg using fun k => (g k).2
  obtain ⟨k, a, y, h₁, h₂⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free (R := 𝓞 K) (M := O)
    (f := (LinearMap.ker (Fintype.linearCombination (𝓞 K) s)).subtype) (x := Fintype.linearCombination (𝓞 K) s)
    (LinearMap.ext fun z => z.2)
  have hs : ∀ t, algebraMap O C (s t) =
      ∑ u, i (a (Pi.single t 1) u : 𝓞 K) * algebraMap O C (y (Finsupp.single u 1)) := fun t => by
    have := LinearMap.congr_fun h₁ (Pi.single t 1)
    rw [Fintype.linearCombination_apply_single, one_smul, LinearMap.comp_apply,
      ← Finsupp.univ_sum_single (a (Pi.single t 1)), map_sum] at this
    rw [this, map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finsupp.smul_single_one, map_smul, Algebra.smul_def, map_mul, ← hj]
    rfl
  have rel : ∀ x : Fin m → K, ∑ t, algebraMap O C (s t) * i (x t) = 0 →
      ∀ u, ∑ t, ((a (Pi.single t 1) u : 𝓞 K) : K) * x t = 0 := fun x hx u => by
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) x
    choose z hz using hd
    replace hz : ∀ t, (z t : K) = ((d : 𝓞 K) : K) * x t := fun t => (hz t).trans (Algebra.smul_def _ _)
    have h₃ : a z = 0 := LinearMap.congr_fun h₂ ⟨z, hO (by
      rw [Fintype.linearCombination_apply, map_sum, map_zero, ← mul_zero (i (d : 𝓞 K)), ← hx, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Algebra.smul_def, map_mul, show algebraMap O C (algebraMap (𝓞 K) O (z t)) = i (z t) from hj _, hz, map_mul]
      ring)⟩
    rw [← Finset.univ_sum_single z, map_sum] at h₃
    have h₄ := congrArg (fun f : Fin k →₀ 𝓞 K => algebraMap (𝓞 K) K (f u)) h₃
    simp only [Finsupp.finset_sum_apply, map_sum, Finsupp.zero_apply, map_zero] at h₄
    refine mul_left_cancel₀ (a := ((d : 𝓞 K) : K))
      (RingOfIntegers.coe_ne_zero_iff.2 (nonZeroDivisors.coe_ne_zero d)) ?_
    rw [mul_zero, Finset.mul_sum, ← h₄]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [show Pi.single t (z t) = z t • (Pi.single t 1 : Fin m → 𝓞 K) by rw [← Pi.single_smul, smul_eq_mul, mul_one],
      map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, show algebraMap (𝓞 K) K (z t) = _ from hz t]
    change _ = _ * ((a (Pi.single t 1) u : 𝓞 K) : K)
    ring
  have hc : ∀ b, w b = ∑ t, algebraMap O C (s t) * i (l t b) := fun b => by
    rw [← hg, Finset.sum_apply]
    exact Finset.sum_congr rfl fun t _ => by rw [← hlg t, Pi.smul_apply, Algebra.smul_def]; rfl
  have hsum : ∀ u b, (∑ t, a (Pi.single t 1) u • l t) b = ∑ t, ((a (Pi.single t 1) u : 𝓞 K) : K) * l t b := fun u b => by
    rw [Finset.sum_apply]
    rfl
  have e : w = ∑ u, y (Finsupp.single u 1) • (i ∘ (∑ t, a (Pi.single t 1) u • l t)) := funext fun b => by
    rw [hc, Finset.sum_apply]
    simp only [hs, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Pi.smul_apply, Function.comp_apply, hsum, Algebra.smul_def, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by rw [map_mul]; ring
  rw [e]
  refine Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨_, ⟨Λ.sum_mem fun t _ => Λ.smul_mem _ (hl t), fun α => funext fun b => ?_⟩, rfl⟩)
  have h₅ := rel (fun t => (A α).mulVec (l t) b) (by
    have h₆ := congrFun (hA α) b
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hc, Finset.mul_sum, map_sum, map_mul, Pi.zero_apply] at h₆ ⊢
    rw [← h₆, Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring) u
  simp only [Matrix.mulVec, dotProduct, hsum, Finset.mul_sum, Pi.zero_apply] at h₅ ⊢
  rw [← h₅, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Establish `hℓ : (1 : ℝ) < ℓ` using `by exact_mod_cast (Fact.out : ℓ.Prime).one_lt`. Establish `he' : (0 : ℝ) < Formalism.BasicNotions.vAdd 𝔭 (ℓ : K)` using `by exact_mod_cast he`. Establish `hO : ∀ c : 𝓞_ℂ_[ℓ], ‖algebraMap 𝓞_ℂ_[ℓ] ℂ_[ℓ] c‖ ≤ 1` using `fun c => (GlobalTheory.PadicComplexHost.mem_iff_norm _ _).1 c.2`. Establish `hv : ∀ (z : 𝓞 K) (n : ℕ), z ≠ 0 → (z ∈ 𝔭.asIdeal ^ n ↔ (n : ℤ) ≤ Formalism.BasicNotions.vAdd 𝔭 (z : K))` using `fun z n hz => by`. Rewrite using `[← 𝔭.intValuation_le_pow_iff_mem, ← 𝔭.valuation_of_algebraMap (K := K), GlobalTheory.PrimeEmbedding.valuation_eq_exp 𝔭 (z := algebraMap (𝓞 K) K z) (RingOfIntegers.coe_ne_zero_iff.2 hz), WithZero.exp_le_exp, neg_le_neg_iff]`.

Establish `hfin : FiniteMultiplicity 𝔭.asIdeal I` using `FiniteMultiplicity.of_not_isUnit (by rw [Ideal.isUnit_iff]; exact 𝔭.isPrime.ne_top) hI`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Establish `hd : d ∈ Submodule.span 𝓞_ℂ_[ℓ] (j '' I)` using `h.ge (Ideal.mem_span_singleton_self d) clear h`. Proceed by induction on `hd using Submodule.span_induction with`. Consider the case `mem _ hx`.

Take `⟨z, hz, rfl⟩` from `hx`. Distinguish the cases in `h0 : z = 0`. Rewrite using `[h0, map_zero, map_zero, norm_zero]`. Check the signs of the components of the expression. Rewrite using `[hj, hi _ (RingOfIntegers.coe_ne_zero_iff.2 h0)]`.

Use `Real.rpow_le_rpow_of_exponent_le hℓ.le (neg_le_neg (div_le_div_of_nonneg_right ?_ he'.le))` and prove the remaining obligations. Conclude with `(hv z _ h0).1 (Ideal.le_of_dvd (pow_multiplicity_dvd _ _) hz)` after adjusting the coercions. Consider the case `zero`. Rewrite using `[map_zero, norm_zero]`. Check the signs of the components of the expression.

Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)`. Consider the case `smul c x _ hx`. Rewrite using `[smul_eq_mul, map_mul, norm_mul]`.

Conclude with `(mul_le_of_le_one_left (norm_nonneg _) (hO c)).trans hx`. Take `⟨z, hz, hz'⟩` from `SetLike.not_le_iff_exists.1 fun hle => hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _) (Ideal.dvd_iff_le.2 hle)`. Establish `h0 : z ≠ 0` using `fun e => hz' (e ▸ zero_mem _)`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 (h.le (Ideal.mem_map_of_mem j hz))`. Establish `h1 : ‖i z‖ ≤ ‖algebraMap 𝓞_ℂ_[ℓ] ℂ_[ℓ] d‖`.

Rewrite using `[← hj, ← hc, map_mul, norm_mul]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (hO c)`. Use `le_trans ?_ h1` and prove the remaining obligations. Rewrite using `[hi _ (RingOfIntegers.coe_ne_zero_iff.2 h0)]`. Use `Real.rpow_le_rpow_of_exponent_le hℓ.le (neg_le_neg (div_le_div_of_nonneg_right ?_ he'.le))` and prove the remaining obligations.

Use `(hv z _ h0).not.1 hz'` as an intermediate fact. Conclude with `(by omega : Formalism.BasicNotions.vAdd 𝔭 (z : K) ≤ (multiplicity 𝔭.asIdeal I : ℤ))` after adjusting the coercions.
-/
theorem norm_of_map_eq_span {K : Type} [Field K] [NumberField K] {ℓ : ℕ} [Fact ℓ.Prime] {𝔭 : HeightOneSpectrum (𝓞 K)}
    {i : K →+* ℂ_[ℓ]} (he : 0 < Formalism.BasicNotions.vAdd 𝔭 (ℓ : K))
    (hi : ∀ z : K, z ≠ 0 → ‖i z‖ = (ℓ : ℝ) ^ (-((Formalism.BasicNotions.vAdd 𝔭 z : ℝ) / (Formalism.BasicNotions.vAdd 𝔭 (ℓ : K) : ℝ))))
    {j : 𝓞 K →+* 𝓞_ℂ_[ℓ]} (hj : ∀ a, algebraMap 𝓞_ℂ_[ℓ] ℂ_[ℓ] (j a) = i a) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    {d : 𝓞_ℂ_[ℓ]} (h : I.map j = Ideal.span {d}) :
    ‖algebraMap 𝓞_ℂ_[ℓ] ℂ_[ℓ] d‖ =
      (ℓ : ℝ) ^ (-((multiplicity 𝔭.asIdeal I : ℝ) / (Formalism.BasicNotions.vAdd 𝔭 (ℓ : K) : ℝ))) := by
  have hℓ : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
  have he' : (0 : ℝ) < Formalism.BasicNotions.vAdd 𝔭 (ℓ : K) := by exact_mod_cast he
  have hO : ∀ c : 𝓞_ℂ_[ℓ], ‖algebraMap 𝓞_ℂ_[ℓ] ℂ_[ℓ] c‖ ≤ 1 := fun c => (GlobalTheory.PadicComplexHost.mem_iff_norm _ _).1 c.2
  have hv : ∀ (z : 𝓞 K) (n : ℕ), z ≠ 0 → (z ∈ 𝔭.asIdeal ^ n ↔ (n : ℤ) ≤ Formalism.BasicNotions.vAdd 𝔭 (z : K)) := fun z n hz => by
    rw [← 𝔭.intValuation_le_pow_iff_mem, ← 𝔭.valuation_of_algebraMap (K := K),
      GlobalTheory.PrimeEmbedding.valuation_eq_exp 𝔭 (z := algebraMap (𝓞 K) K z) (RingOfIntegers.coe_ne_zero_iff.2 hz),
      WithZero.exp_le_exp, neg_le_neg_iff]
  have hfin : FiniteMultiplicity 𝔭.asIdeal I :=
    FiniteMultiplicity.of_not_isUnit (by rw [Ideal.isUnit_iff]; exact 𝔭.isPrime.ne_top) hI
  refine le_antisymm ?_ ?_
  · have hd : d ∈ Submodule.span 𝓞_ℂ_[ℓ] (j '' I) := h.ge (Ideal.mem_span_singleton_self d)
    clear h
    induction hd using Submodule.span_induction with
    | mem _ hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      by_cases h0 : z = 0
      · rw [h0, map_zero, map_zero, norm_zero]
        positivity
      rw [hj, hi _ (RingOfIntegers.coe_ne_zero_iff.2 h0)]
      refine Real.rpow_le_rpow_of_exponent_le hℓ.le (neg_le_neg (div_le_div_of_nonneg_right ?_ he'.le))
      exact_mod_cast (hv z _ h0).1 (Ideal.le_of_dvd (pow_multiplicity_dvd _ _) hz)
    | zero =>
      rw [map_zero, norm_zero]
      positivity
    | add x y _ _ hx hy =>
      rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
    | smul c x _ hx =>
      rw [smul_eq_mul, map_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hO c)).trans hx
  · obtain ⟨z, hz, hz'⟩ := SetLike.not_le_iff_exists.1 fun hle =>
      hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _) (Ideal.dvd_iff_le.2 hle)
    have h0 : z ≠ 0 := fun e => hz' (e ▸ zero_mem _)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (h.le (Ideal.mem_map_of_mem j hz))
    have h1 : ‖i z‖ ≤ ‖algebraMap 𝓞_ℂ_[ℓ] ℂ_[ℓ] d‖ := by
      rw [← hj, ← hc, map_mul, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hO c)
    refine le_trans ?_ h1
    rw [hi _ (RingOfIntegers.coe_ne_zero_iff.2 h0)]
    refine Real.rpow_le_rpow_of_exponent_le hℓ.le (neg_le_neg (div_le_div_of_nonneg_right ?_ he'.le))
    have := (hv z _ h0).not.1 hz'
    exact_mod_cast (by omega : Formalism.BasicNotions.vAdd 𝔭 (z : K) ≤ (multiplicity 𝔭.asIdeal I : ℤ))

end GlobalTheory.LieIndex
