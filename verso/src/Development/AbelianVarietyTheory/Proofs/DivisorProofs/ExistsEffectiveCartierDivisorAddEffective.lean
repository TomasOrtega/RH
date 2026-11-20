import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false
noncomputable section
open GlobalTheory.Cartier.CartierDiv
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.Cartier.EffDiff

variable {X : Scheme.{0}} [IsIntegral X]

/- English proof (translation)
Take `⟨b, hb⟩` from `exists_fnOf_eq hη hf`. Use `haveI := hV.isLocalization_basicOpen τ`. Take `⟨m, a, e⟩` from `IsLocalization.Away.surj τ b`. Use `⟨m, fun x hx => ?_⟩` and prove the remaining obligations. Establish `e'` using `congrArg (fnOf _ hη) e`.

Rewrite `e'` using `[map_mul, map_pow, hb]`. Establish `h1 : ∀ c : Γ(X, V), fnOf _ hη (algebraMap Γ(X, V) Γ(X, X.basicOpen τ) c) = fnOf V (X.basicOpen_le τ hη) c` using `fun c => fnOf_resG (X.basicOpen_le τ) hη c`. Rewrite `e'` using `[h1, h1]`. Rewrite using `[e']`. Conclude with `regAt_fnOf hx _ a`.
-/
theorem exists_pow_regAt {V : X.Opens} (hV : IsAffineOpen V) (τ : Γ(X, V))
    (hη : genericPoint X ∈ X.basicOpen τ) {f : X.functionField}
    (hf : ∀ x ∈ X.basicOpen τ, RegAt x f) :
    ∃ m : ℕ, ∀ x ∈ V, RegAt x (f * fnOf V (X.basicOpen_le τ hη) τ ^ m) := by
  obtain ⟨b, hb⟩ := exists_fnOf_eq hη hf
  haveI := hV.isLocalization_basicOpen τ
  obtain ⟨m, a, e⟩ := IsLocalization.Away.surj τ b
  refine ⟨m, fun x hx => ?_⟩
  have e' := congrArg (fnOf _ hη) e
  rw [map_mul, map_pow, hb] at e'
  have h1 : ∀ c : Γ(X, V), fnOf _ hη (algebraMap Γ(X, V) Γ(X, X.basicOpen τ) c) =
      fnOf V (X.basicOpen_le τ hη) c := fun c => fnOf_resG (X.basicOpen_le τ) hη c
  rw [h1, h1] at e'
  rw [e']
  exact regAt_fnOf hx _ a

/- English proof (translation)
Establish `key : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ m : ℕ, ∀ N, m ≤ N → ∀ y ∈ V, (D + N • divOfSec hL t ht).RegularAt y 1`. Introduce `x`. Take `⟨W, hxW, h, hh⟩` from `D.exists_isEqn_nhds x`. Take `⟨i, hi⟩` from `exists_chart hL x`. Take `⟨V, hVa, hxV, hVle⟩` from `Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (show x ∈ W ⊓ L.U i from ⟨hxW, hi⟩)`.

Establish `hVW : V ≤ W` using `hVle.trans inf_le_left`. Establish `hVi : V ≤ L.U i` using `hVle.trans inf_le_right`. Use `set τ : Γ(X, V) := resG X hVi (t.f i)`. Establish `hbo : ∀ y, y ∈ X.basicOpen τ ↔ y ∈ V ∧ y ∈ nonzeroLocus t` using `fun y => by`. Establish `hb : X.basicOpen τ = V ⊓ X.basicOpen (t.f i)` using `X.basicOpen_res _ _`.

Rewrite using `[hb]`. Conclude with `⟨fun hy => ⟨hy.1, (mem_nonzeroLocus_iff t i (hVi hy.1)).2 hy.2⟩, fun hy => ⟨hy.1, (mem_nonzeroLocus_iff t i (hVi hy.1)).1 hy.2⟩⟩`. Establish `hη : genericPoint X ∈ X.basicOpen τ` using `(hbo _).2 ⟨gen_mem hxV, ht⟩`. Take `⟨m, hm⟩` from `exists_pow_regAt hVa τ hη (f := h) fun y hy => by`. Take `⟨hyV, hyt⟩` from `(hbo y).1 hy`.

Use `(hh y (hVW hyV)).regularAt_iff.1 (hD y hyt)` as an intermediate fact. Rewrite `this` using `[one_mul]`. Then use the resulting hypothesis. Use `⟨V, hxV, m, fun N hN y hyV => ?_⟩` and prove the remaining obligations. Establish `hT` using `(presents_divOfRatSec hL (isRatSec_ratOfSec t ht)).isEqn i y (hVi hyV)`. Use `⟨_, (hh y (hVW hyV)).add (hT.nsmul N), ?_⟩` and prove the remaining obligations.

Establish `e : (ratOfSec t ht i : X.functionField) = fnOf V (X.basicOpen_le τ hη) τ`. Rewrite using `[val_ratOfSec (gen_mem (hVi hyV)), fnOf_resG]`. Rewrite using `[one_mul, Units.val_mul, Units.val_pow_eq_pow_val, e, ← Nat.add_sub_cancel' hN, pow_add, ← mul_assoc]`. Establish `hp` using `regAt_fnOf hyV (X.basicOpen_le τ hη) (τ ^ (N - m))`. Rewrite `hp` using `[map_pow]`.

Conclude with `(hm y hyV).mul hp`. Use `choose V hxV m hm using key`. Take `⟨S, hS⟩` from `exists_finset_iSup_eq_top V hxV`. Use `⟨S.sup m, fun N hN y => ?_⟩` and prove the remaining obligations. Take `⟨x, hy⟩` from `Opens.mem_iSup.1 (hS.ge (Set.mem_univ y))`.

Conclude with `hm x N ((Finset.le_sup x.2).trans hN) y hy`.
-/
theorem eventually_eff_add_nsmul [CompactSpace X] {L : LB X} (hL : L.IsLB) (t : L.Sec)
    (ht : genericPoint X ∈ nonzeroLocus t) (D : CartierDiv X)
    (hD : ∀ x ∈ nonzeroLocus t, D.RegularAt x 1) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → (D + N • divOfSec hL t ht).Eff := by
  have key : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ m : ℕ, ∀ N, m ≤ N → ∀ y ∈ V,
      (D + N • divOfSec hL t ht).RegularAt y 1 := by
    intro x
    obtain ⟨W, hxW, h, hh⟩ := D.exists_isEqn_nhds x
    obtain ⟨i, hi⟩ := exists_chart hL x
    obtain ⟨V, hVa, hxV, hVle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show x ∈ W ⊓ L.U i from ⟨hxW, hi⟩)
    have hVW : V ≤ W := hVle.trans inf_le_left
    have hVi : V ≤ L.U i := hVle.trans inf_le_right
    set τ : Γ(X, V) := resG X hVi (t.f i)
    have hbo : ∀ y, y ∈ X.basicOpen τ ↔ y ∈ V ∧ y ∈ nonzeroLocus t := fun y => by
      have hb : X.basicOpen τ = V ⊓ X.basicOpen (t.f i) := X.basicOpen_res _ _
      rw [hb]
      exact ⟨fun hy => ⟨hy.1, (mem_nonzeroLocus_iff t i (hVi hy.1)).2 hy.2⟩,
        fun hy => ⟨hy.1, (mem_nonzeroLocus_iff t i (hVi hy.1)).1 hy.2⟩⟩
    have hη : genericPoint X ∈ X.basicOpen τ := (hbo _).2 ⟨gen_mem hxV, ht⟩
    obtain ⟨m, hm⟩ := exists_pow_regAt hVa τ hη (f := h) fun y hy => by
      obtain ⟨hyV, hyt⟩ := (hbo y).1 hy
      have := (hh y (hVW hyV)).regularAt_iff.1 (hD y hyt)
      rwa [one_mul] at this
    refine ⟨V, hxV, m, fun N hN y hyV => ?_⟩
    have hT := (presents_divOfRatSec hL (isRatSec_ratOfSec t ht)).isEqn i y (hVi hyV)
    refine ⟨_, (hh y (hVW hyV)).add (hT.nsmul N), ?_⟩
    have e : (ratOfSec t ht i : X.functionField) = fnOf V (X.basicOpen_le τ hη) τ := by
      rw [val_ratOfSec (gen_mem (hVi hyV)), fnOf_resG]
    rw [one_mul, Units.val_mul, Units.val_pow_eq_pow_val, e, ← Nat.add_sub_cancel' hN, pow_add,
      ← mul_assoc]
    have hp := regAt_fnOf hyV (X.basicOpen_le τ hη) (τ ^ (N - m))
    rw [map_pow] at hp
    exact (hm y hyV).mul hp
  choose V hxV m hm using key
  obtain ⟨S, hS⟩ := exists_finset_iSup_eq_top V hxV
  refine ⟨S.sup m, fun N hN y => ?_⟩
  obtain ⟨x, hy⟩ := Opens.mem_iSup.1 (hS.ge (Set.mem_univ y))
  exact hm x N ((Finset.le_sup x.2).trans hN) y hy

end GlobalTheory.Cartier.EffDiff

/- English proof (translation)
Introduce `X _ _ H hH D`. Use `haveI := hH.compactSpace`. Take `⟨W, hηW, g, hg⟩` from `D.exists_isEqn_nhds (genericPoint X)`. Take `⟨n, -, t, hηt, htW, hU⟩` from `hH.exists_affine_le hηW`. Establish `hL` using `isLB_lbPow hH.isLB n`.

Use `haveI : Nonempty (nonzeroLocus t) := ⟨⟨_, hηt⟩⟩`. Use `haveI := functionField_isFractionRing_of_isAffineOpen X _ hU`. Take `⟨a, c, hc, e⟩` from `IsFractionRing.div_surjective (A := Γ(X, nonzeroLocus t)) (g : X.functionField)`. Establish `hfn : ∀ b : Γ(X, nonzeroLocus t), algebraMap Γ(X, nonzeroLocus t) X.functionField b = fnOf _ hηt b` using `fun _ => rfl`. Establish `hc0 : fnOf _ hηt c ≠ 0`.

Rewrite using `[← hfn]`. Conclude with `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hc`. Take `⟨N₁, h₁⟩` from `eventually_eff_add_nsmul hL t hηt (principal (Units.mk0 _ hc0)) fun x hx => ⟨_, isEqn_principal _ x, by rw [one_mul, Units.val_mk0]; exact regAt_fnOf hx hηt c⟩`. Take `⟨N₂, h₂⟩` from `eventually_eff_add_nsmul hL t hηt (D + principal (Units.mk0 _ hc0)) fun x hx => ⟨_, (hg x (htW hx)).add (isEqn_principal _ x), by`. Rewrite using `[one_mul, Units.val_mul, Units.val_mk0, ← e, hfn, hfn, div_mul_cancel₀ _ hc0]`.

Conclude with `regAt_fnOf hx hηt a⟩`. Use `⟨principal (Units.mk0 _ hc0) + max N₁ N₂ • divOfSec hL t hηt, h₁ _ (le_max_left _ _), ?_⟩` and prove the remaining obligations. Rewrite using `[← add_assoc]`. Conclude with `h₂ _ (le_max_right _ _)`.
-/
theorem GlobalTheory.Cartier.EffDiff.exists_eff_and_add_eff : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (H : LB X),
    IsAmpleLB H → ∀ D : CartierDiv X, ∃ E : CartierDiv X, E.Eff ∧ (D + E).Eff := by
  intro X _ _ H hH D
  haveI := hH.compactSpace
  obtain ⟨W, hηW, g, hg⟩ := D.exists_isEqn_nhds (genericPoint X)
  obtain ⟨n, -, t, hηt, htW, hU⟩ := hH.exists_affine_le hηW
  have hL := isLB_lbPow hH.isLB n
  haveI : Nonempty (nonzeroLocus t) := ⟨⟨_, hηt⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X _ hU
  obtain ⟨a, c, hc, e⟩ := IsFractionRing.div_surjective (A := Γ(X, nonzeroLocus t))
    (g : X.functionField)
  have hfn : ∀ b : Γ(X, nonzeroLocus t),
      algebraMap Γ(X, nonzeroLocus t) X.functionField b = fnOf _ hηt b := fun _ => rfl
  have hc0 : fnOf _ hηt c ≠ 0 := by
    rw [← hfn]; exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hc
  obtain ⟨N₁, h₁⟩ := eventually_eff_add_nsmul hL t hηt (principal (Units.mk0 _ hc0))
    fun x hx => ⟨_, isEqn_principal _ x, by rw [one_mul, Units.val_mk0]; exact regAt_fnOf hx hηt c⟩
  obtain ⟨N₂, h₂⟩ := eventually_eff_add_nsmul hL t hηt (D + principal (Units.mk0 _ hc0))
    fun x hx => ⟨_, (hg x (htW hx)).add (isEqn_principal _ x), by
      rw [one_mul, Units.val_mul, Units.val_mk0, ← e, hfn, hfn, div_mul_cancel₀ _ hc0]
      exact regAt_fnOf hx hηt a⟩
  refine ⟨principal (Units.mk0 _ hc0) + max N₁ N₂ • divOfSec hL t hηt, h₁ _ (le_max_left _ _), ?_⟩
  rw [← add_assoc]
  exact h₂ _ (le_max_right _ _)
