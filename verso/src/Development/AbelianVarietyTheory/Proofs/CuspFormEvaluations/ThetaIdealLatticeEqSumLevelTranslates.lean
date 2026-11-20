import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockHxDifferentiable
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelOneThetaEqSmulOfSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.AdditionLevelTwoMul

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ThetaEig

/- English proof (translation)
Use `haveI := Fintype.ofFinite (A ⧸ N)`. Use `haveI := Fintype.ofFinite H`. Set `T : A ⧸ N → W` to `fun q => S q.out f`. Establish `hT : ∀ u : A, T (u : A ⧸ N) = S u f`. Introduce `u`.

Take `⟨m, hm⟩` from `QuotientAddGroup.mk_out_eq_add N u`. Simplify using `only [T, hm]`. Rewrite using `[← hS, hf _ m.2]`. Establish `hST : ∀ (u : A) q, S u (T q) = T ((u : A ⧸ N) + q)`. Introduce `u q`.

Take `⟨v, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Rewrite using `[← QuotientAddGroup.mk_add, hT, hT, hS]`. Establish `h1 : ∀ ψ : H, ∑ q, ψ.1 (-q) • T q ∈ V`. Introduce `ψ`. Use `hV ψ ψ.2 _ (U.sum_mem fun q _ => U.smul_mem _ (hU _)) fun u => ?_` and prove the remaining obligations.

Rewrite using `[map_sum, Finset.smul_sum]`. Use `Fintype.sum_equiv (Equiv.addLeft (u : A ⧸ N)) _ _ fun q => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hST, smul_smul, ← AddChar.map_add_eq_mul]`. Simplify using the standard rewrite rules. Establish `h2 : ∀ q : A ⧸ N, q ≠ 0 → ∑ ψ : H, ψ.1 (-q) = 0`.

Introduce `q hq`. Take `⟨ψ, hψ, hne⟩` from `hH (-q) (neg_ne_zero.2 hq)`. Set `ev : AddChar H ℂ` to `{ toFun := fun ψ => ψ.1 (-q) map_zero_eq_one' := by simp map_add_eq_mul' := fun a b => by simp }`. Use `(AddChar.sum_eq_zero_iff_ne_zero (ψ := ev)).2 fun h => hne ?_` and prove the remaining obligations. Conclude with `DFunLike.congr_fun h ⟨ψ, hψ⟩`.

Establish `h3 : ∑ ψ : H, ∑ q, ψ.1 (-q) • T q = (Fintype.card H : ℂ) • f`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_smul]`. Rewrite using `[Finset.sum_eq_single 0 (fun q _ hq => by rw [h2 q hq, zero_smul]) (by simp)]`. Use `hT 0` as an intermediate fact.

Rewrite `this` using `[hf 0 N.zero_mem, QuotientAddGroup.mk_zero]`. Simplify using `[this]`. Establish `h4 : (Fintype.card H : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Rewrite using `[← V.smul_mem_iff h4, ← h3]`. Conclude with `V.sum_mem fun ψ _ => h1 ψ`.
-/
theorem mem_of_eigen_mem {A W : Type} [AddCommGroup A] [AddCommGroup W] [Module ℂ W] (N : AddSubgroup A)
    [Finite (A ⧸ N)] (S : A → W →ₗ[ℂ] W) (hS : ∀ u v f, S u (S v f) = S (u + v) f)
    (H : AddSubgroup (AddChar (A ⧸ N) ℂ)) (hH : ∀ q ≠ 0, ∃ ψ ∈ H, ψ q ≠ 1)
    (f : W) (hf : ∀ u ∈ N, S u f = f) (U V : Submodule ℂ W) (hU : ∀ u, S u f ∈ U)
    (hV : ∀ ψ ∈ H, ∀ h ∈ U, (∀ u : A, S u h = ψ (u : A ⧸ N) • h) → h ∈ V) : f ∈ V := by
  haveI := Fintype.ofFinite (A ⧸ N)
  haveI := Fintype.ofFinite H
  let T : A ⧸ N → W := fun q => S q.out f
  have hT : ∀ u : A, T (u : A ⧸ N) = S u f := by
    intro u
    obtain ⟨m, hm⟩ := QuotientAddGroup.mk_out_eq_add N u
    simp only [T, hm]
    rw [← hS, hf _ m.2]
  have hST : ∀ (u : A) q, S u (T q) = T ((u : A ⧸ N) + q) := by
    intro u q
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [← QuotientAddGroup.mk_add, hT, hT, hS]
  have h1 : ∀ ψ : H, ∑ q, ψ.1 (-q) • T q ∈ V := by
    intro ψ
    refine hV ψ ψ.2 _ (U.sum_mem fun q _ => U.smul_mem _ (hU _)) fun u => ?_
    rw [map_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.addLeft (u : A ⧸ N)) _ _ fun q => ?_
    rw [map_smul, hST, smul_smul, ← AddChar.map_add_eq_mul]
    simp
  have h2 : ∀ q : A ⧸ N, q ≠ 0 → ∑ ψ : H, ψ.1 (-q) = 0 := by
    intro q hq
    obtain ⟨ψ, hψ, hne⟩ := hH (-q) (neg_ne_zero.2 hq)
    let ev : AddChar H ℂ :=
      { toFun := fun ψ => ψ.1 (-q)
        map_zero_eq_one' := by simp
        map_add_eq_mul' := fun a b => by simp }
    refine (AddChar.sum_eq_zero_iff_ne_zero (ψ := ev)).2 fun h => hne ?_
    exact DFunLike.congr_fun h ⟨ψ, hψ⟩
  have h3 : ∑ ψ : H, ∑ q, ψ.1 (-q) • T q = (Fintype.card H : ℂ) • f := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    rw [Finset.sum_eq_single 0 (fun q _ hq => by rw [h2 q hq, zero_smul]) (by simp)]
    have := hT 0
    rw [hf 0 N.zero_mem, QuotientAddGroup.mk_zero] at this
    simp [this]
  have h4 : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [← V.smul_mem_iff h4, ← h3]
  exact V.sum_mem fun ψ _ => h1 ψ

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ (Submodule.span ℂ (φ '' Y)) := FiniteDimensional.span_of_finite ℂ (hY.image φ)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `F _`.

Establish `: F = F default • fun z : Fin 0 → Z => ∏ b, φ ((default : Fin 0 → J) b) (z b)`. Use function extensionality and compare the values at `z`. Simplify using `[Subsingleton.elim z default]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨default, fun b => b.elim0, rfl⟩)`.

Consider the case `succ n ih`. Introduce `F hF`. Take `⟨m, h, k, hhk, hF'⟩` from `ThetaAddition.exists_sum_mul (Submodule.span ℂ (φ '' Y)) _ (fun t (z : Fin n → Z) => F (Fin.cons t z)) (fun z => by`. Break down `isEmpty_or_nonempty Z with hZ | ⟨⟨t⟩⟩` into its components or cases. Rewrite using `[Subsingleton.elim (fun t => F (Fin.cons t z)) 0]`.

Conclude with `Submodule.zero_mem _`. Simplify `hF 0 (Fin.cons t z))` using `only [Fin.update_cons_zero]`. Use the proof step `(fun t => ih _ fun b z => by simpa only [Fin.cons_update] using hF b.succ (Fin.cons t z))`. Establish `: F = ∑ i, fun z : Fin (n + 1) → Z => h i (z 0) * k i (Fin.tail z)`. Use function extensionality and compare the values at `z`.

Rewrite using `[Finset.sum_apply, ← hF', Fin.cons_self_tail]`. Rewrite using `[this]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hhk i`. Generalize the expression as in `h i = a at h1`.

Generalize the expression as in `k i = c at h2`. Proceed by induction on `h1, h2 using Submodule.span_induction₂ with`. Consider the case `mem_mem a c ha hc`. Take `⟨j, hj, rfl⟩` from `ha`. Take `⟨y, hy, rfl⟩` from `hc`.

Use `Submodule.subset_span ⟨Fin.cons j y, fun b => Fin.cases hj hy b, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Simplify using `[Fin.prod_univ_succ, Fin.tail]`. Consider the case `zero_left c _ => simp only [Pi.zero_apply, zero_mul]`. Conclude with `Submodule.zero_mem _`.

Consider the case `zero_right c _ => simp only [Pi.zero_apply, mul_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add_left a a' c _ _ _ h1 h2 => simp only [Pi.add_apply, add_mul]`. Conclude with `Submodule.add_mem _ h1 h2`. Consider the case `add_right a c c' _ _ _ h1 h2 => simp only [Pi.add_apply, mul_add]`.

Conclude with `Submodule.add_mem _ h1 h2`. Consider the case `smul_left t a c _ _ h1`. Simplify using `only [Pi.smul_apply, smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ t h1`. Consider the case `smul_right t a c _ _ h1`.

Simplify using `only [Pi.smul_apply, mul_smul_comm]`. Conclude with `Submodule.smul_mem _ t h1`.
-/
theorem mem_span_prod {Z J : Type} (φ : J → Z → ℂ) (Y : Set J) (hY : Y.Finite) : ∀ (n : ℕ)
    (F : (Fin n → Z) → ℂ), (∀ b z, (fun t => F (Function.update z b t)) ∈ Submodule.span ℂ (φ '' Y)) →
    F ∈ Submodule.span ℂ ((fun (y : Fin n → J) (z : Fin n → Z) => ∏ b, φ (y b) (z b)) '' {y | ∀ b, y b ∈ Y}) := by
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (φ '' Y)) := FiniteDimensional.span_of_finite ℂ (hY.image φ)
  intro n
  induction n with
  | zero =>
    intro F _
    have : F = F default • fun z : Fin 0 → Z => ∏ b, φ ((default : Fin 0 → J) b) (z b) := by
      funext z
      simp [Subsingleton.elim z default]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨default, fun b => b.elim0, rfl⟩)
  | succ n ih =>
    intro F hF
    obtain ⟨m, h, k, hhk, hF'⟩ := ThetaAddition.exists_sum_mul (Submodule.span ℂ (φ '' Y)) _
      (fun t (z : Fin n → Z) => F (Fin.cons t z))
      (fun z => by
        rcases isEmpty_or_nonempty Z with hZ | ⟨⟨t⟩⟩
        · rw [Subsingleton.elim (fun t => F (Fin.cons t z)) 0]; exact Submodule.zero_mem _
        · simpa only [Fin.update_cons_zero] using hF 0 (Fin.cons t z))
      (fun t => ih _ fun b z => by simpa only [Fin.cons_update] using hF b.succ (Fin.cons t z))
    have : F = ∑ i, fun z : Fin (n + 1) → Z => h i (z 0) * k i (Fin.tail z) := by
      funext z
      rw [Finset.sum_apply, ← hF', Fin.cons_self_tail]
    rw [this]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨h1, h2⟩ := hhk i
    generalize h i = a at h1
    generalize k i = c at h2
    induction h1, h2 using Submodule.span_induction₂ with
    | mem_mem a c ha hc =>
      obtain ⟨j, hj, rfl⟩ := ha
      obtain ⟨y, hy, rfl⟩ := hc
      refine Submodule.subset_span ⟨Fin.cons j y, fun b => Fin.cases hj hy b, ?_⟩
      funext z
      simp [Fin.prod_univ_succ, Fin.tail]
    | zero_left c _ => simp only [Pi.zero_apply, zero_mul]; exact Submodule.zero_mem _
    | zero_right c _ => simp only [Pi.zero_apply, mul_zero]; exact Submodule.zero_mem _
    | add_left a a' c _ _ _ h1 h2 => simp only [Pi.add_apply, add_mul]; exact Submodule.add_mem _ h1 h2
    | add_right a c c' _ _ _ h1 h2 => simp only [Pi.add_apply, mul_add]; exact Submodule.add_mem _ h1 h2
    | smul_left t a c _ _ h1 =>
      simp only [Pi.smul_apply, smul_mul_assoc]; exact Submodule.smul_mem _ t h1
    | smul_right t a c _ _ h1 =>
      simp only [Pi.smul_apply, mul_smul_comm]; exact Submodule.smul_mem _ t h1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {X : Data E r}

/- English proof (translation)
Establish `h` using `(TensLat.epsW_semichar (Base.stdL_mem_Vset 1 1) hL hw hw1 (y := fun _ => u) ((TensLat.mem_tens_stdL L _).2 fun _ => hu)).2 (fun _ => v) ((TensLat.mem_tens_stdL L _).2 fun _ => hv)`. Simplify using `only [epsW, Finset.univ_unique, Finset.sum_singleton] at h`. Conclude with `h`.
-/
theorem thetaSignExpEF_add_selfDual_lattice {L : Lt E r} (hL : SelfD X L) {w : E} (hw : IsIntegral ℤ w) (hw1 : w + cc w = 1)
    {u v : Fin r → E} (hu : u ∈ L) (hv : v ∈ L) :
    eps1 X w (u + v) = eps1 X w u * eps1 X w v * cexp (-(Real.pi * I * ((EF X u v : ℚ) : ℂ))) := by
  have h := (TensLat.epsW_semichar (Base.stdL_mem_Vset 1 1) hL hw hw1 (y := fun _ => u)
    ((TensLat.mem_tens_stdL L _).2 fun _ => hu)).2 (fun _ => v) ((TensLat.mem_tens_stdL L _).2 fun _ => hv)
  simp only [epsW, Finset.univ_unique, Finset.sum_singleton] at h
  exact h

/- English proof (translation)
Rewrite using `[TensLat.EF_eq_bilin, map_zero, LinearMap.zero_apply]`.
-/
theorem EF_zero_left (u : Fin r → E) : EF X 0 u = 0 := by
  rw [TensLat.EF_eq_bilin, map_zero, LinearMap.zero_apply]

/- English proof (translation)
Rewrite using `[TensLat.EF_eq_bilin, map_zero]`.
-/
theorem EF_zero_right (u : Fin r → E) : EF X u 0 = 0 := by
  rw [TensLat.EF_eq_bilin, map_zero]

/- English proof (translation)
Establish `hM' : (M : E) ≠ 0` using `Nat.cast_ne_zero.2 hM`. Use `Submodule.smul_induction_on hu (fun a ha l hl => ?_) ?_` and prove the remaining obligations. Establish `h1 : Lev.bar a • ((M : E) • y) ∈ (Ideal.span {(M : 𝓞 E)}) • L`. Rewrite using `[← h𝔐, mul_comm, Submodule.mul_smul]`. Conclude with `Submodule.smul_mem_smul (Lev.mem_conjI.2 (by rwa [Lev.bar_bar])) hy`.

Rewrite `h1` using `[Submodule.ideal_span_singleton_smul]`. Take `⟨l', hl', e⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h1`. Establish `h2 : Lev.bar a • y = l'`. Use `smul_right_injective _ hM' ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(M : E) • (Lev.bar a • y) = (M : E) • l'`.

Rewrite using `[smul_comm, ← e, Lev.O_smul]`. Simplify using the standard rewrite rules. Establish `h3` using `Lev.EF_smul (X := X) (Lev.bar a) y l`. Rewrite `h3` using `[Lev.bar_bar, h2]`. Rewrite using `[← h3]`.

Conclude with `(hL.2 l').1 hl' l hl`. Introduce and unpack `u v ⟨k, hk⟩ ⟨k', hk'⟩`. Conclude with `⟨k + k', by rw [Lev.EF_add_right, hk, hk', Int.cast_add]⟩`.
-/
theorem EF_int_of_mem {L : Lt E r} (hL : SelfD X L) {𝔐 : Ideal (𝓞 E)} {M : ℕ} (hM : M ≠ 0)
    (h𝔐 : 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)}) {y u : Fin r → E} (hy : (M : E) • y ∈ 𝔐 • L)
    (hu : u ∈ 𝔐 • L) : ∃ k : ℤ, EF X y u = k := by
  have hM' : (M : E) ≠ 0 := Nat.cast_ne_zero.2 hM
  refine Submodule.smul_induction_on hu (fun a ha l hl => ?_) ?_
  · have h1 : Lev.bar a • ((M : E) • y) ∈ (Ideal.span {(M : 𝓞 E)}) • L := by
      rw [← h𝔐, mul_comm, Submodule.mul_smul]
      exact Submodule.smul_mem_smul (Lev.mem_conjI.2 (by rwa [Lev.bar_bar])) hy
    rw [Submodule.ideal_span_singleton_smul] at h1
    obtain ⟨l', hl', e⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h1
    have h2 : Lev.bar a • y = l' := by
      refine smul_right_injective _ hM' ?_
      change (M : E) • (Lev.bar a • y) = (M : E) • l'
      rw [smul_comm, ← e, Lev.O_smul]
      simp
    have h3 := Lev.EF_smul (X := X) (Lev.bar a) y l
    rw [Lev.bar_bar, h2] at h3
    rw [← h3]
    exact (hL.2 l').1 hl' l hl
  · rintro u v ⟨k, hk⟩ ⟨k', hk'⟩
    exact ⟨k + k', by rw [Lev.EF_add_right, hk, hk', Int.cast_add]⟩

/- English proof (translation)
Establish `hM' : (M : E) ≠ 0` using `Nat.cast_ne_zero.2 hM`. Establish `h1 : ∀ b ∈ conjI 𝔐, b • ((M : E)⁻¹ • u) ∈ L`. Introduce `b hb`. Use `(hL.2 _).2 fun l hl => ?_` and prove the remaining obligations. Take `⟨k, hk⟩` from `h ((M : E)⁻¹ • (Lev.bar b • l)) (by`.

Rewrite using `[smul_inv_smul₀ hM']`. Conclude with `Submodule.smul_mem_smul (Lev.mem_conjI.1 hb) hl)`. Rewrite `hk` using `[Lev.EF_smulE, Lev.EF_smul, Lev.bar_bar]`. Use `⟨-k, ?_⟩` and prove the remaining obligations. Rewrite using `[TensLat.EF_swap, Int.cast_neg, ← hk]`.

Simplify using `[cc]`. Establish `h2 : ∀ c ∈ 𝔐 * conjI 𝔐, c • ((M : E)⁻¹ • u) ∈ 𝔐 • L`. Introduce `c hc`. Use `Submodule.mul_induction_on hc (fun a ha b hb => ?_) fun a b ha hb => ?_` and prove the remaining obligations. Rewrite using `[mul_smul]`.

Conclude with `Submodule.smul_mem_smul ha (h1 b hb)`. Rewrite using `[add_smul]`. Conclude with `add_mem ha hb`. Establish `h3` using `h2 M (h𝔐 ▸ Ideal.mem_span_singleton_self _)`. Rewrite `h3` using `[Lev.O_smul]`.

Simplify `h3` using `[smul_smul, hM']`.
-/
theorem mem_of_EF_int {L : Lt E r} (hL : SelfD X L) {𝔐 : Ideal (𝓞 E)} {M : ℕ} (hM : M ≠ 0)
    (h𝔐 : 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)}) {u : Fin r → E}
    (h : ∀ y : Fin r → E, (M : E) • y ∈ 𝔐 • L → ∃ k : ℤ, EF X y u = k) : u ∈ 𝔐 • L := by
  have hM' : (M : E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have h1 : ∀ b ∈ conjI 𝔐, b • ((M : E)⁻¹ • u) ∈ L := by
    intro b hb
    refine (hL.2 _).2 fun l hl => ?_
    obtain ⟨k, hk⟩ := h ((M : E)⁻¹ • (Lev.bar b • l)) (by
      rw [smul_inv_smul₀ hM']
      exact Submodule.smul_mem_smul (Lev.mem_conjI.1 hb) hl)
    rw [Lev.EF_smulE, Lev.EF_smul, Lev.bar_bar] at hk
    refine ⟨-k, ?_⟩
    rw [TensLat.EF_swap, Int.cast_neg, ← hk]
    simp [cc]
  have h2 : ∀ c ∈ 𝔐 * conjI 𝔐, c • ((M : E)⁻¹ • u) ∈ 𝔐 • L := by
    intro c hc
    refine Submodule.mul_induction_on hc (fun a ha b hb => ?_) fun a b ha hb => ?_
    · rw [mul_smul]
      exact Submodule.smul_mem_smul ha (h1 b hb)
    · rw [add_smul]
      exact add_mem ha hb
  have h3 := h2 M (h𝔐 ▸ Ideal.mem_span_singleton_self _)
  rw [Lev.O_smul] at h3
  simpa [smul_smul, hM'] using h3

variable (X) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)

noncomputable def fockL (a : Fin g → ℂ) : ((Fin g → ℂ) → ℂ) →ₗ[ℂ] ((Fin g → ℂ) → ℂ) where
  toFun := fock X bas idx x 1 a
  map_add' f f' := by funext z; simp only [fock, Pi.add_apply, mul_add]
  map_smul' c f := by funext z; simp only [fock, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/- English proof (translation)
Unfold `pv`. Rewrite using `[per_add]`. Both sides reduce to the same expression.
-/
theorem pv_add (u v : Fin r → E) : pv X idx x (u + v) = pv X idx x u + pv X idx x v := by
  unfold pv; rw [per_add]; rfl

/- English proof (translation)
Unfold `pv`. Rewrite using `[per_zero]`. Both sides reduce to the same expression.
-/
theorem pv_zero : pv X idx x 0 = 0 := by
  unfold pv; rw [per_zero]; rfl

variable {X bas idx x}

/- English proof (translation)
Establish `h` using `(fock_laws E r X g bas idx 0 hs Even.zero x hd 1 f).1 (pv X idx x u) (pv X idx x v)`. Rewrite `h` using `[(hx_laws E r X g bas idx 0 hs Even.zero x hd).2.2.1, ← pv_add]`. Simplify using `only [Nat.cast_one, _root_.one_mul, ofReal_ratCast] at h`. Conclude with `h`.
-/
theorem fockL_fockL (hs : IsSympl X bas) (hd : x ∈ X.dom) (u v : Fin r → E) (f : (Fin g → ℂ) → ℂ) :
    fockL X bas idx x (pv X idx x u) (fockL X bas idx x (pv X idx x v) f) =
      cexp (-(Real.pi * I * ((EF X u v : ℚ) : ℂ))) • fockL X bas idx x (pv X idx x (u + v)) f := by
  have h := (fock_laws E r X g bas idx 0 hs Even.zero x hd 1 f).1 (pv X idx x u) (pv X idx x v)
  rw [(hx_laws E r X g bas idx 0 hs Even.zero x hd).2.2.1, ← pv_add] at h
  simp only [Nat.cast_one, _root_.one_mul, ofReal_ratCast] at h
  exact h

/- English proof (translation)
Set `N : AddSubgroup L` to `(𝔐 • L).toAddSubgroup.comap L.subtype.toAddMonoidHom`. Establish `hN : ∀ u : L, u ∈ N ↔ (u : Fin r → E) ∈ 𝔐 • L` using `fun _ => Iff.rfl`. Use `haveI : Finite (L ⧸ N) := by haveI : Module.Finite (𝓞 E) L := .of_fg hL.1 haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L haveI : AddGroup.FG L := Module.Finite.iff_addGroup_fg.1 inferInstance`. Use `AddCommGroup.finite_of_fg_isAddTorsion _ fun q => ?_` and prove the remaining obligations. Take `⟨u, rfl⟩` from `QuotientAddGroup.mk_surjective q`.

Use `isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨M, Nat.pos_of_ne_zero hM, ?_⟩` and prove the remaining obligations. Rewrite using `[← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, hN]`. Establish `: (M : 𝓞 E) ∈ 𝔐` using `Ideal.mul_le_left (h𝔐 ▸ Ideal.mem_span_singleton_self (M : 𝓞 E))`. Simplify `Submodule.smul_mem_smul this u.2` using `[Nat.cast_smul_eq_nsmul]`. Set `e : (Fin r → E) → (Fin r → E) → ℂ` to `fun y u => cexp (2 * Real.pi * I * ((EF X y u : ℚ) : ℂ))`.

Establish `he1 : ∀ y u, e y u = 1 ↔ ∃ k : ℤ, EF X y u = k`. Introduce `y u`. Rewrite using `[Complex.exp_eq_one_iff]`. Use `exists_congr fun k => ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_left_inj' Complex.two_pi_I_ne_zero]`.

Conclude with `Iff.rfl` after adjusting the coercions. Establish `hel : ∀ y y' u, e (y + y') u = e y u * e y' u`. Introduce `y y' u`. Simplify using `only [e, Lev.EF_add_left, Rat.cast_add, mul_add, Complex.exp_add]`. Establish `her : ∀ y u u', e y (u + u') = e y u * e y u'`.

Introduce `y u u'`. Simplify using `only [e, Lev.EF_add_right, Rat.cast_add, mul_add, Complex.exp_add]`. Establish `hen : ∀ y u, e (-y) u = e y (-u)`. Introduce `y u`. Simplify using `only [e, TensLat.EF_eq_bilin, map_neg, LinearMap.neg_apply]`.

Set `H : AddSubgroup (AddChar (L ⧸ N) ℂ)` to `{ carrier := {ψ | ∃ y : Fin r → E, (M : E) • y ∈ 𝔐 • L ∧ ∀ u : L, ψ (u : L ⧸ N) = e y u} zero_mem' := ⟨0, by simp, fun u => by simp [e, EF_zero_left]⟩ add_mem' := by`. Introduce and unpack `ψ ψ' ⟨y, hy, h⟩ ⟨y', hy', h'⟩`. Conclude with `⟨y + y', by rw [smul_add]; exact add_mem hy hy', fun u => by`. Rewrite using `[AddChar.add_apply, h, h', hel]⟩`. Use the proof step `neg_mem' := by`.

Introduce and unpack `ψ ⟨y, hy, h⟩`. Conclude with `⟨-y, by rw [smul_neg]; exact neg_mem hy, fun u => by`. Rewrite using `[AddChar.neg_apply, ← QuotientAddGroup.mk_neg, h, hen]`. Use the proof step `rfl⟩ }`. Establish `hH : ∀ q ≠ 0, ∃ ψ ∈ H, ψ q ≠ 1`.

Introduce `q hq`. Take `⟨u, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Use `hq ((QuotientAddGroup.eq_zero_iff _).2 (mem_of_EF_int hL hM h𝔐 fun y hy => ?_))` and prove the remaining obligations.

Set `χ : L →+ Additive ℂ` to `{ toFun := fun u => Additive.ofMul (e y u) map_zero' := by simp [e, EF_zero_right] map_add' := fun a b => by rw [Submodule.coe_add, her, ofMul_mul] }`. Establish `hχ : N ≤ χ.ker` using `fun a ha => congrArg Additive.ofMul ((he1 y a).2 (EF_int_of_mem hL hM h𝔐 hy ha))`. Conclude with `(he1 y u).1 (hcon (AddChar.toAddMonoidHomEquiv.symm (QuotientAddGroup.lift N χ hχ)) ⟨y, hy, fun _ => rfl⟩)`. Use `choose yy hyy hyy' using fun ψ : H => ψ.2`. Use `⟨Set.range yy, Set.finite_range _, by rintro _ ⟨ψ, rfl⟩; exact hyy ψ, fun f hf => ?_⟩` and prove the remaining obligations.

Set `U : Submodule ℂ ((Fin g → ℂ) → ℂ)` to `{ carrier := {f | Differentiable ℂ f} zero_mem' := differentiable_const 0 add_mem' := fun h h' => h.add h' smul_mem' := fun c _ h => h.const_smul c }`. Establish `hdiff` using `fun f => (fock_laws E r X g bas idx 0 hs Even.zero x hd 1 f).2.2.2.1`. Use `mem_of_eigen_mem N (fun u : L => eps1 X w u • fockL X bas idx x (pv X idx x u)) (fun u v f => ?_) H hH f (fun u hu => hf.2 u hu) U _ (fun u => U.smul_mem _ (hdiff f hf.1 _)) fun ψ hψ h hU hh => ?_` and prove the remaining obligations. Take `⟨k, hk⟩` from `(hL.2 u).1 u.2 v v.2`. Simplify using `only [LinearMap.smul_apply, map_smul, fockL_fockL hs hd, smul_smul, Submodule.coe_add, thetaSignExpEF_add_selfDual_lattice hL hw hw1 u.2 v.2]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `set y := yy ⟨ψ, hψ⟩`. Establish `h1 : IsTheta1 X bas idx w x L (fockL X bas idx x (pv X idx x (-y)) h)`. Use `⟨hdiff h hU _, fun u hu => ?_⟩` and prove the remaining obligations.

Establish `h2` using `congrArg (fockL X bas idx x (pv X idx x (-y))) (hh ⟨u, hu⟩)`. Rewrite `h2` using `[hyy' ⟨ψ, hψ⟩, LinearMap.smul_apply, map_smul, map_smul, fockL_fockL hs hd, add_comm]`. Express the relevant statement in the definitionally equal form `eps1 X w u • fockL X bas idx x (pv X idx x u) _ = _`. Use `smul_right_injective _ (show e y u ≠ 0 from Complex.exp_ne_zero _) ?_` and prove the remaining obligations. Simplify using `only []`.

Rewrite using `[← h2, fockL_fockL hs hd, smul_comm (e y u), smul_smul (e y u), ← Complex.exp_add]`. Establish `e1 : EF X u (-y) = -EF X y u * -1`. Rewrite using `[← TensLat.EF_swap]`. Simplify using `only [TensLat.EF_eq_bilin, map_neg, mul_neg, _root_.mul_one]`. Establish `e2 : EF X (-y) u = -EF X y u` using `by simp only [TensLat.EF_eq_bilin, map_neg, LinearMap.neg_apply]`.

Rewrite using `[e1, e2]`. Use `congr 3`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨a, ha⟩` from `ThetaOne.exists_eq_smul_of_isTheta1 E r X g bas idx 0 hs Even.zero w hw hw1 L hL x hd _ θ h1 hθ h0`.

Establish `h3` using `congrArg (fockL X bas idx x (pv X idx x y)) ha`. Establish `h4 : EF X y (-y) = 0`. Use `TensLat.EF_swap X y y` as an intermediate fact. Simplify using `only [TensLat.EF_eq_bilin, map_neg] at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h5 : fockL X bas idx x 0 h = h` using `(fock_laws E r X g bas idx 0 hs Even.zero x hd 1 h).2.1`. Rewrite `h3` using `[fockL_fockL hs hd, h4, add_neg_cancel, pv_zero, h5, map_smul]`. Simplify using `only [Rat.cast_zero, mul_zero, neg_zero, Complex.exp_zero, one_smul] at h3`. Rewrite using `[h3]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, ⟨_, rfl⟩, rfl⟩)`.
-/
theorem exists_span_one (hs : IsSympl X bas) (hd : x ∈ X.dom) {w : E} (hw : IsIntegral ℤ w)
    (hw1 : w + cc w = 1) {L : Lt E r} (hL : SelfD X L) {𝔐 : Ideal (𝓞 E)} {M : ℕ} (hM : M ≠ 0)
    (h𝔐 : 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)}) {θ : (Fin g → ℂ) → ℂ} (hθ : IsTheta1 X bas idx w x L θ)
    (h0 : θ ≠ 0) : ∃ Y : Set (Fin r → E), Y.Finite ∧ (∀ y ∈ Y, (M : E) • y ∈ 𝔐 • L) ∧
      ∀ f, IsTheta1 X bas idx w x (𝔐 • L) f →
        f ∈ Submodule.span ℂ ((fun y => fock X bas idx x 1 (pv X idx x y) θ) '' Y) := by
  let N : AddSubgroup L := (𝔐 • L).toAddSubgroup.comap L.subtype.toAddMonoidHom
  have hN : ∀ u : L, u ∈ N ↔ (u : Fin r → E) ∈ 𝔐 • L := fun _ => Iff.rfl
  haveI : Finite (L ⧸ N) := by
    haveI : Module.Finite (𝓞 E) L := .of_fg hL.1
    haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
    haveI : AddGroup.FG L := Module.Finite.iff_addGroup_fg.1 inferInstance
    refine AddCommGroup.finite_of_fg_isAddTorsion _ fun q => ?_
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective q
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨M, Nat.pos_of_ne_zero hM, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, hN]
    have : (M : 𝓞 E) ∈ 𝔐 := Ideal.mul_le_left (h𝔐 ▸ Ideal.mem_span_singleton_self (M : 𝓞 E))
    simpa [Nat.cast_smul_eq_nsmul] using Submodule.smul_mem_smul this u.2
  let e : (Fin r → E) → (Fin r → E) → ℂ := fun y u => cexp (2 * Real.pi * I * ((EF X y u : ℚ) : ℂ))
  have he1 : ∀ y u, e y u = 1 ↔ ∃ k : ℤ, EF X y u = k := by
    intro y u
    rw [Complex.exp_eq_one_iff]
    refine exists_congr fun k => ?_
    rw [mul_comm, mul_left_inj' Complex.two_pi_I_ne_zero]
    exact_mod_cast Iff.rfl
  have hel : ∀ y y' u, e (y + y') u = e y u * e y' u := by
    intro y y' u
    simp only [e, Lev.EF_add_left, Rat.cast_add, mul_add, Complex.exp_add]
  have her : ∀ y u u', e y (u + u') = e y u * e y u' := by
    intro y u u'
    simp only [e, Lev.EF_add_right, Rat.cast_add, mul_add, Complex.exp_add]
  have hen : ∀ y u, e (-y) u = e y (-u) := by
    intro y u
    simp only [e, TensLat.EF_eq_bilin, map_neg, LinearMap.neg_apply]
  let H : AddSubgroup (AddChar (L ⧸ N) ℂ) :=
    { carrier := {ψ | ∃ y : Fin r → E, (M : E) • y ∈ 𝔐 • L ∧ ∀ u : L, ψ (u : L ⧸ N) = e y u}
      zero_mem' := ⟨0, by simp, fun u => by simp [e, EF_zero_left]⟩
      add_mem' := by
        rintro ψ ψ' ⟨y, hy, h⟩ ⟨y', hy', h'⟩
        exact ⟨y + y', by rw [smul_add]; exact add_mem hy hy', fun u => by
          rw [AddChar.add_apply, h, h', hel]⟩
      neg_mem' := by
        rintro ψ ⟨y, hy, h⟩
        exact ⟨-y, by rw [smul_neg]; exact neg_mem hy, fun u => by
          rw [AddChar.neg_apply, ← QuotientAddGroup.mk_neg, h, hen]; rfl⟩ }
  have hH : ∀ q ≠ 0, ∃ ψ ∈ H, ψ q ≠ 1 := by
    intro q hq
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective q
    by_contra hcon
    push Not at hcon
    refine hq ((QuotientAddGroup.eq_zero_iff _).2 (mem_of_EF_int hL hM h𝔐 fun y hy => ?_))
    let χ : L →+ Additive ℂ :=
      { toFun := fun u => Additive.ofMul (e y u)
        map_zero' := by simp [e, EF_zero_right]
        map_add' := fun a b => by rw [Submodule.coe_add, her, ofMul_mul] }
    have hχ : N ≤ χ.ker := fun a ha =>
      congrArg Additive.ofMul ((he1 y a).2 (EF_int_of_mem hL hM h𝔐 hy ha))
    exact (he1 y u).1
      (hcon (AddChar.toAddMonoidHomEquiv.symm (QuotientAddGroup.lift N χ hχ)) ⟨y, hy, fun _ => rfl⟩)
  choose yy hyy hyy' using fun ψ : H => ψ.2
  refine ⟨Set.range yy, Set.finite_range _, by rintro _ ⟨ψ, rfl⟩; exact hyy ψ, fun f hf => ?_⟩
  let U : Submodule ℂ ((Fin g → ℂ) → ℂ) :=
    { carrier := {f | Differentiable ℂ f}
      zero_mem' := differentiable_const 0
      add_mem' := fun h h' => h.add h'
      smul_mem' := fun c _ h => h.const_smul c }
  have hdiff := fun f => (fock_laws E r X g bas idx 0 hs Even.zero x hd 1 f).2.2.2.1
  refine mem_of_eigen_mem N (fun u : L => eps1 X w u • fockL X bas idx x (pv X idx x u)) (fun u v f => ?_) H hH
    f (fun u hu => hf.2 u hu) U _ (fun u => U.smul_mem _ (hdiff f hf.1 _)) fun ψ hψ h hU hh => ?_
  · obtain ⟨k, hk⟩ := (hL.2 u).1 u.2 v v.2
    simp only [LinearMap.smul_apply, map_smul, fockL_fockL hs hd, smul_smul, Submodule.coe_add,
      thetaSignExpEF_add_selfDual_lattice hL hw hw1 u.2 v.2]
    congr 1
    ring
  · set y := yy ⟨ψ, hψ⟩
    have h1 : IsTheta1 X bas idx w x L (fockL X bas idx x (pv X idx x (-y)) h) := by
      refine ⟨hdiff h hU _, fun u hu => ?_⟩
      have h2 := congrArg (fockL X bas idx x (pv X idx x (-y))) (hh ⟨u, hu⟩)
      rw [hyy' ⟨ψ, hψ⟩, LinearMap.smul_apply, map_smul, map_smul, fockL_fockL hs hd, add_comm] at h2
      change eps1 X w u • fockL X bas idx x (pv X idx x u) _ = _
      refine smul_right_injective _ (show e y u ≠ 0 from Complex.exp_ne_zero _) ?_
      simp only []
      rw [← h2, fockL_fockL hs hd, smul_comm (e y u), smul_smul (e y u), ← Complex.exp_add]
      have e1 : EF X u (-y) = -EF X y u * -1 := by
        rw [← TensLat.EF_swap]; simp only [TensLat.EF_eq_bilin, map_neg, mul_neg, _root_.mul_one]
      have e2 : EF X (-y) u = -EF X y u := by simp only [TensLat.EF_eq_bilin, map_neg, LinearMap.neg_apply]
      rw [e1, e2]
      congr 3
      push_cast
      ring
    obtain ⟨a, ha⟩ := ThetaOne.exists_eq_smul_of_isTheta1 E r X g bas idx 0 hs Even.zero w hw hw1 L hL x hd
      _ θ h1 hθ h0
    have h3 := congrArg (fockL X bas idx x (pv X idx x y)) ha
    have h4 : EF X y (-y) = 0 := by
      have := TensLat.EF_swap X y y
      simp only [TensLat.EF_eq_bilin, map_neg] at this ⊢
      linarith
    have h5 : fockL X bas idx x 0 h = h := (fock_laws E r X g bas idx 0 hs Even.zero x hd 1 h).2.1
    rw [fockL_fockL hs hd, h4, add_neg_cancel, pv_zero, h5, map_smul] at h3
    simp only [Rat.cast_zero, mul_zero, neg_zero, Complex.exp_zero, one_smul] at h3
    rw [h3]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, ⟨_, rfl⟩, rfl⟩)

/- English proof (translation)
Introduce `E _ _ _ r X g q0 _ bas idx n hs hn w hw L hL x hd _ t _ _ 𝔐 M hM h𝔐 v hv θ κ hθ hmean hκ F hF hlaw`. Establish `h0 : θ ≠ 0`. Introduce and unpack `rfl`. Take `⟨_, _, -, -, h⟩` from `hmean`. Simplify using `at h`.

Take `⟨Y, hY, hYM, hspan⟩` from `exists_span_one hs hd w.2 hw hL hM.pos.ne' h𝔐 hθ h0`. Establish `h1` using `mem_span_prod (fun y => fock X bas idx x 1 (pv X idx x y) θ) Y hY n F fun b z => by`. Use `hspan _ ⟨hF.comp (fun s => (hasFDerivAt_update z s).differentiableAt), fun u hu => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `s`. Establish `h` using `hlaw (Pi.single b u) (fun b' => by`.

Break down `eq_or_ne b' b with rfl | hb` into its components or cases. Simplify using `using hu`. Simplify using `[Pi.single_eq_of_ne hb]) (Function.update z b s)`. Rewrite using `[h]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, fock, epsW, eps1]`.

Rewrite using `[Finset.sum_eq_single b, Finset.sum_eq_single b]`. Simplify using `only [Pi.single_eq_same, Function.update_self, Nat.cast_one, _root_.one_mul, _root_.mul_assoc]`. Use `congr 3`. Use function extensionality and compare the values at `b'`. Break down `eq_or_ne b' b with rfl | hb` into its components or cases.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne hb, pv_zero, hb]`. Introduce `b' _ hb`. Simplify using `[Pi.single_eq_of_ne hb, pv_zero, fock_hx_zero_right]`. Simplify using the standard rewrite rules.

Introduce `b' _ hb`. Simplify using `[Pi.single_eq_of_ne hb, EF_zero_left]`. Simplify using the standard rewrite rules. Take `⟨l, hl, e⟩` from `(Finsupp.mem_span_image_iff_linearCombination ℂ).1 h1`. Use `⟨l.support, l, fun y hy b => hYM _ (hl hy b), fun z => ?_⟩` and prove the remaining obligations.

Rewrite using `[← e, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul, (fock_laws E r X g bas idx n hs hn x hd 1 θ).2.2.2.2 (fun _ => θ) κ v hv.1 hκ y z]`.
-/
theorem theta_eq_sum_translates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : 𝓞 E, (w : E) + cc (w : E) = 1 → ∀ L : Lt E r, SelfD X L → ∀ x ∈ X.dom, X.IsOrtho x → ∀ t : ℝ, 0 < t → (∀ τ, X.c τ = t) → ∀ (𝔐 : Ideal (𝓞 E)) (M : ℕ), Odd M → 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)} → ∀ v : TF n g, IsVac X bas (w : E) (tens (stdL E n) L) v → ∀ (θ : (Fin g → ℂ) → ℂ) (κ : ℂ), IsTheta1 X bas idx (w : E) x L θ → MeanOne X bas idx x L θ → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ F : (Fin n → Fin g → ℂ) → ℂ, Differentiable ℂ F → (∀ u : Matrix (Fin n) (Fin r) E, (∀ b, u b ∈ 𝔐 • L) → ∀ z, F z = epsW X (w : E) u * cexp (-(Real.pi * ∑ b, hx X bas idx x (z b + (1 / 2 : ℂ) • pv X idx x (u b)) (pv X idx x (u b)))) * F (fun b => z b + pv X idx x (u b))) → ∃ (s : Finset (Matrix (Fin n) (Fin r) E)) (cf : Matrix (Fin n) (Fin r) E → ℂ), (∀ y ∈ s, ∀ b, (M : E) • y b ∈ 𝔐 • L) ∧ ∀ z, F z = ∑ y ∈ s, cf y * (κ * thA X bas idx (heisG X bas y v) x z) := by
  intro E _ _ _ r X g q0 _ bas idx n hs hn w hw L hL x hd _ t _ _ 𝔐 M hM h𝔐 v hv θ κ hθ hmean hκ F hF hlaw
  have h0 : θ ≠ 0 := by
    rintro rfl
    obtain ⟨_, _, -, -, h⟩ := hmean
    simp at h
  obtain ⟨Y, hY, hYM, hspan⟩ := exists_span_one hs hd w.2 hw hL hM.pos.ne' h𝔐 hθ h0
  have h1 := mem_span_prod (fun y => fock X bas idx x 1 (pv X idx x y) θ) Y hY n F fun b z => by
    refine hspan _ ⟨hF.comp (fun s => (hasFDerivAt_update z s).differentiableAt), fun u hu => ?_⟩
    funext s
    have h := hlaw (Pi.single b u) (fun b' => by
      rcases eq_or_ne b' b with rfl | hb
      · simpa using hu
      · simp [Pi.single_eq_of_ne hb]) (Function.update z b s)
    rw [h]
    simp only [Pi.smul_apply, smul_eq_mul, fock, epsW, eps1]
    rw [Finset.sum_eq_single b, Finset.sum_eq_single b]
    · simp only [Pi.single_eq_same, Function.update_self, Nat.cast_one, _root_.one_mul, _root_.mul_assoc]
      congr 3
      funext b'
      rcases eq_or_ne b' b with rfl | hb
      · simp
      · simp [Pi.single_eq_of_ne hb, pv_zero, hb]
    · intro b' _ hb
      simp [Pi.single_eq_of_ne hb, pv_zero, fock_hx_zero_right]
    · simp
    · intro b' _ hb
      simp [Pi.single_eq_of_ne hb, EF_zero_left]
    · simp
  obtain ⟨l, hl, e⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).1 h1
  refine ⟨l.support, l, fun y hy b => hYM _ (hl hy b), fun z => ?_⟩
  rw [← e, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Pi.smul_apply, smul_eq_mul,
    (fock_laws E r X g bas idx n hs hn x hd 1 θ).2.2.2.2 (fun _ => θ) κ v hv.1 hκ y z]

end GlobalTheory.Dict.ThetaEig
