import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta

noncomputable section

namespace GlobalTheory.InertZeta

open Formalism.UG

section DosetSwapProof

variable {G : Type} [Group G] {K : Subgroup G}

def dosetOf (K : Subgroup G) (x : G ⧸ K) : Set G :=
  DoubleCoset.doubleCoset x.out (K : Set G) (K : Set G)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `DoubleCoset.doubleCoset_eq_of_mem h`. Introduce `h`. Unfold `dosetOf at h`.

Rewrite using `[← h]`. Conclude with `DoubleCoset.mem_doubleCoset_self K K _`.
-/
theorem mem_dosetOf_iff {x y : G ⧸ K} :
    y.out ∈ DoubleCoset.doubleCoset x.out (K : Set G) (K : Set G) ↔ dosetOf K y = dosetOf K x := by
  constructor
  · intro h
    exact DoubleCoset.doubleCoset_eq_of_mem h
  · intro h
    unfold dosetOf at h
    rw [← h]
    exact DoubleCoset.mem_doubleCoset_self K K _

/- English proof (translation)
Take `⟨a, ha, b, hb, e⟩` from `DoubleCoset.mem_doubleCoset.1 (mem_dosetOf_iff.2 h)`. Conclude with `⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩`.
-/
theorem exists_of_dosetOf_eq {x y : G ⧸ K} (h : dosetOf K y = dosetOf K x) :
    ∃ a b : K, y.out = (a : G) * x.out * b := by
  obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.1 (mem_dosetOf_iff.2 h)
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩

/- English proof (translation)
Distinguish the cases in `h : ∃ x₀ : G ⧸ K, dosetOf K x₀ = S`. Take `⟨x₀, rfl⟩` from `h`. Establish `hf` using `Formalism.UG.P.finite_cosets_in_doset hK x₀.out`. Establish `hs : {x : G ⧸ K | dosetOf K x = dosetOf K x₀} ⊆ {x : G ⧸ K | ∃ a b : K, x.out = (a : G) * x₀.out * b}` using `fun y hy => exists_of_dosetOf_eq hy`. Conclude with `(hf.subset hs).to_subtype`.

Use `haveI : IsEmpty {x : G ⧸ K // dosetOf K x = S} := ⟨fun y => h ⟨y.1, y.2⟩⟩ infer_instance`.
-/
theorem finite_dosetOf_fibre (hK : IsCommensurated K) (S : Set G) :
    Finite {x : G ⧸ K // dosetOf K x = S} := by
  by_cases h : ∃ x₀ : G ⧸ K, dosetOf K x₀ = S
  · obtain ⟨x₀, rfl⟩ := h
    have hf := Formalism.UG.P.finite_cosets_in_doset hK x₀.out
    have hs : {x : G ⧸ K | dosetOf K x = dosetOf K x₀} ⊆ {x : G ⧸ K | ∃ a b : K, x.out = (a : G) * x₀.out * b} :=
      fun y hy => exists_of_dosetOf_eq hy
    exact (hf.subset hs).to_subtype
  · haveI : IsEmpty {x : G ⧸ K // dosetOf K x = S} := ⟨fun y => h ⟨y.1, y.2⟩⟩
    infer_instance

/- English proof (translation)
Take `⟨a, b, e⟩` from `exists_of_dosetOf_eq h`. Rewrite using `[e, hF a b]`.
-/
theorem biInv_of_dosetOf_eq {F : G → ℂ} (hF : IsBiInv K F) {x y : G ⧸ K} (h : dosetOf K y = dosetOf K x) :
    F y.out = F x.out := by
  obtain ⟨a, b, e⟩ := exists_of_dosetOf_eq h
  rw [e, hF a b]

/- English proof (translation)
Use `set s : Set (G ⧸ K) := {x | dosetOf K x = dosetOf K x₀} with hs`. Establish `e : ∀ x : G ⧸ K, dosetInd ℂ K x₀.out x.out • v (1 * x.out) = s.indicator (fun x => v x.out) x`. Introduce `x`. Distinguish the cases in `h : dosetOf K x = dosetOf K x₀`. Establish `h'` using `mem_dosetOf_iff.2 h`.

Establish `hx : x ∈ s` using `h`. Simplify using `[dosetInd, Set.indicator_of_mem h', Set.indicator_of_mem hx]`. Establish `h' : x.out ∉ DoubleCoset.doubleCoset x₀.out (K : Set G) (K : Set G)` using `fun h' => h (mem_dosetOf_iff.1 h')`. Establish `hx : x ∉ s` using `h`. Simplify using `[dosetInd, Set.indicator_of_notMem h', Set.indicator_of_notMem hx]`.

Establish `hfin : s.Finite` using `Set.finite_coe_iff.1 (finite_dosetOf_fibre hK (dosetOf K x₀))`. Rewrite using `[hAct, finsum_congr e, ← tsum_eq_finsum (L := SummationFilter.unconditional (G ⧸ K)) ((hfin.subset (Set.support_indicator_subset)))]`. Rewrite using `[← tsum_subtype]`. Both sides reduce to the same expression.
-/
theorem hAct_dosetInd_eq (hK : IsCommensurated K) (x₀ : G ⧸ K) (v : G → ℂ) :
    hAct K (dosetInd ℂ K x₀.out) v 1 = ∑' y : {x : G ⧸ K // dosetOf K x = dosetOf K x₀}, v y.1.out := by
  set s : Set (G ⧸ K) := {x | dosetOf K x = dosetOf K x₀} with hs
  have e : ∀ x : G ⧸ K, dosetInd ℂ K x₀.out x.out • v (1 * x.out) = s.indicator (fun x => v x.out) x := by
    intro x
    by_cases h : dosetOf K x = dosetOf K x₀
    · have h' := mem_dosetOf_iff.2 h
      have hx : x ∈ s := h
      simp [dosetInd, Set.indicator_of_mem h', Set.indicator_of_mem hx]
    · have h' : x.out ∉ DoubleCoset.doubleCoset x₀.out (K : Set G) (K : Set G) := fun h' => h (mem_dosetOf_iff.1 h')
      have hx : x ∉ s := h
      simp [dosetInd, Set.indicator_of_notMem h', Set.indicator_of_notMem hx]
  have hfin : s.Finite := Set.finite_coe_iff.1 (finite_dosetOf_fibre hK (dosetOf K x₀))
  rw [hAct, finsum_congr e, ← tsum_eq_finsum (L := SummationFilter.unconditional (G ⧸ K)) ((hfin.subset (Set.support_indicator_subset)))]
  rw [← tsum_subtype]
  rfl

end DosetSwapProof

/- English proof (translation)
Introduce `G _ K hK F w φ Z hF hw hH hZ`. Use `haveI : ∀ S : Set G, Finite {x : G ⧸ K // dosetOf K x = S} := finite_dosetOf_fibre hK`. Set `e` to `Equiv.sigmaFiberEquiv (dosetOf K)`. Set `f₁ : G ⧸ K → ℂ` to `fun x => F x.out * φ x.out`. Set `f₂ : G ⧸ K → ℂ` to `fun x => F x.out * w x.out`.

Establish `hs : ∀ S : Set G, ∑' y : {x : G ⧸ K // dosetOf K x = S}, f₂ y.1 = ∑' y : {x : G ⧸ K // dosetOf K x = S}, f₁ y.1`. Introduce `S`. Distinguish the cases in `h : ∃ x₀ : G ⧸ K, dosetOf K x₀ = S`. Take `⟨x₀, rfl⟩` from `h`. Establish `e₂ : ∀ y : {x : G ⧸ K // dosetOf K x = dosetOf K x₀}, f₂ y.1 = F x₀.out * w y.1.out` using `fun y => by simp only [f₂, biInv_of_dosetOf_eq hF y.2]`.

Establish `e₁ : ∀ y : {x : G ⧸ K // dosetOf K x = dosetOf K x₀}, f₁ y.1 = F x₀.out * φ y.1.out` using `fun y => by simp only [f₁, biInv_of_dosetOf_eq hF y.2]`. Rewrite using `[tsum_congr e₂, tsum_congr e₁, tsum_mul_left, tsum_mul_left, ← hAct_dosetInd_eq hK, ← hAct_dosetInd_eq hK, hH]`. Use `haveI : IsEmpty {x : G ⧸ K // dosetOf K x = S} := ⟨fun y => h ⟨y.1, y.2⟩⟩`. Simplify using `[tsum_empty]`. Establish `hn : ∀ S : Set G, ∑' y : {x : G ⧸ K // dosetOf K x = S}, ‖f₂ y.1‖ ≤ ∑' y : {x : G ⧸ K // dosetOf K x = S}, ‖f₁ y.1‖`.

Introduce `S`. Distinguish the cases in `h : ∃ x₀ : G ⧸ K, dosetOf K x₀ = S`. Take `⟨x₀, hx₀⟩` from `h`. Establish `c : ∀ y : {x : G ⧸ K // dosetOf K x = S}, f₂ y.1 = F x₀.out * w x₀.out` using `fun y => by`. Establish `hy : dosetOf K y.1 = dosetOf K x₀` using `y.2.trans hx₀.symm`.

Simplify using `only [f₂, biInv_of_dosetOf_eq hF hy, biInv_of_dosetOf_eq hw hy]`. Establish `key : ∑' y : {x : G ⧸ K // dosetOf K x = S}, ‖f₂ y.1‖ = ‖∑' y : {x : G ⧸ K // dosetOf K x = S}, f₂ y.1‖`. Rewrite using `[tsum_congr (fun y => congrArg norm (c y)), tsum_congr c, tsum_const, tsum_const, nsmul_eq_mul, nsmul_eq_mul]`. Simplify using `[norm_mul]`. Rewrite using `[key, hs]`.

Conclude with `norm_tsum_le_tsum_norm Summable.of_finite`. Use `haveI : IsEmpty {x : G ⧸ K // dosetOf K x = S} := ⟨fun y => h ⟨y.1, y.2⟩⟩`. Simplify using `[tsum_empty]`. Establish `h₁ : HasSum (f₁ ∘ e) Z` using `(e.hasSum_iff).2 hZ`. Establish `h₁n : Summable fun p => ‖(f₁ ∘ e) p‖` using `summable_norm_iff.2 h₁.summable`.

Establish `h₂n : Summable fun p => ‖(f₂ ∘ e) p‖`. Rewrite `h₁n`, the goal using `[summable_sigma_of_nonneg (fun _ => norm_nonneg _)]`. Use `⟨fun S => Summable.of_finite, ?_⟩` and prove the remaining obligations. Conclude with `h₁n.2.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _) hn`. Establish `h₂ : Summable (f₂ ∘ e)` using `summable_norm_iff.1 h₂n`.

Establish `A` using `h₂.hasSum.sigma (fun S => (Summable.of_finite).hasSum)`. Establish `B` using `h₁.sigma (fun S => (Summable.of_finite).hasSum)`. Establish `hZ' : ∑' p, (f₂ ∘ e) p = Z`. Use `A.unique ?_` and prove the remaining obligations. Establish `: (fun S => ∑' c : {x : G ⧸ K // dosetOf K x = S}, (f₂ ∘ e) ⟨S, c⟩) = fun S => ∑' c : {x : G ⧸ K // dosetOf K x = S}, (f₁ ∘ e) ⟨S, c⟩` using `funext hs`.

Rewrite using `[this]`. Conclude with `B`. Use `h₂.hasSum` as an intermediate fact. Rewrite `this` using `[hZ', e.hasSum_iff]`. Conclude with `this`.
-/
theorem dosetSwap : DosetSwap := by
  intro G _ K hK F w φ Z hF hw hH hZ
  haveI : ∀ S : Set G, Finite {x : G ⧸ K // dosetOf K x = S} := finite_dosetOf_fibre hK
  let e := Equiv.sigmaFiberEquiv (dosetOf K)
  let f₁ : G ⧸ K → ℂ := fun x => F x.out * φ x.out
  let f₂ : G ⧸ K → ℂ := fun x => F x.out * w x.out
  have hs : ∀ S : Set G, ∑' y : {x : G ⧸ K // dosetOf K x = S}, f₂ y.1 =
      ∑' y : {x : G ⧸ K // dosetOf K x = S}, f₁ y.1 := by
    intro S
    by_cases h : ∃ x₀ : G ⧸ K, dosetOf K x₀ = S
    · obtain ⟨x₀, rfl⟩ := h
      have e₂ : ∀ y : {x : G ⧸ K // dosetOf K x = dosetOf K x₀}, f₂ y.1 = F x₀.out * w y.1.out :=
        fun y => by simp only [f₂, biInv_of_dosetOf_eq hF y.2]
      have e₁ : ∀ y : {x : G ⧸ K // dosetOf K x = dosetOf K x₀}, f₁ y.1 = F x₀.out * φ y.1.out :=
        fun y => by simp only [f₁, biInv_of_dosetOf_eq hF y.2]
      rw [tsum_congr e₂, tsum_congr e₁, tsum_mul_left, tsum_mul_left, ← hAct_dosetInd_eq hK,
        ← hAct_dosetInd_eq hK, hH]
    · haveI : IsEmpty {x : G ⧸ K // dosetOf K x = S} := ⟨fun y => h ⟨y.1, y.2⟩⟩
      simp [tsum_empty]
  have hn : ∀ S : Set G, ∑' y : {x : G ⧸ K // dosetOf K x = S}, ‖f₂ y.1‖ ≤
      ∑' y : {x : G ⧸ K // dosetOf K x = S}, ‖f₁ y.1‖ := by
    intro S
    by_cases h : ∃ x₀ : G ⧸ K, dosetOf K x₀ = S
    · obtain ⟨x₀, hx₀⟩ := h
      have c : ∀ y : {x : G ⧸ K // dosetOf K x = S}, f₂ y.1 = F x₀.out * w x₀.out := fun y => by
        have hy : dosetOf K y.1 = dosetOf K x₀ := y.2.trans hx₀.symm
        simp only [f₂, biInv_of_dosetOf_eq hF hy, biInv_of_dosetOf_eq hw hy]
      have key : ∑' y : {x : G ⧸ K // dosetOf K x = S}, ‖f₂ y.1‖ =
          ‖∑' y : {x : G ⧸ K // dosetOf K x = S}, f₂ y.1‖ := by
        rw [tsum_congr (fun y => congrArg norm (c y)), tsum_congr c, tsum_const, tsum_const, nsmul_eq_mul,
          nsmul_eq_mul]
        simp [norm_mul]
      rw [key, hs]
      exact norm_tsum_le_tsum_norm Summable.of_finite
    · haveI : IsEmpty {x : G ⧸ K // dosetOf K x = S} := ⟨fun y => h ⟨y.1, y.2⟩⟩
      simp [tsum_empty]
  have h₁ : HasSum (f₁ ∘ e) Z := (e.hasSum_iff).2 hZ
  have h₁n : Summable fun p => ‖(f₁ ∘ e) p‖ := summable_norm_iff.2 h₁.summable
  have h₂n : Summable fun p => ‖(f₂ ∘ e) p‖ := by
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)] at h₁n ⊢
    refine ⟨fun S => Summable.of_finite, ?_⟩
    exact h₁n.2.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _) hn
  have h₂ : Summable (f₂ ∘ e) := summable_norm_iff.1 h₂n
  have A := h₂.hasSum.sigma (fun S => (Summable.of_finite).hasSum)
  have B := h₁.sigma (fun S => (Summable.of_finite).hasSum)
  have hZ' : ∑' p, (f₂ ∘ e) p = Z := by
    refine A.unique ?_
    have : (fun S => ∑' c : {x : G ⧸ K // dosetOf K x = S}, (f₂ ∘ e) ⟨S, c⟩) =
        fun S => ∑' c : {x : G ⧸ K // dosetOf K x = S}, (f₁ ∘ e) ⟨S, c⟩ := funext hs
    rw [this]
    exact B
  have := h₂.hasSum
  rw [hZ', e.hasSum_iff] at this
  exact this

end GlobalTheory.InertZeta

end
