import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.ThetaTranslateCoef

/- English proof (translation)
Establish `li` using `linearIndependent_monoidHom G ℂ`. Rewrite `li` using `[linearIndependent_iff]`. Establish `h0` using `li (∑ i, Finsupp.single (κ i) (c i)) (by`. Rewrite using `[map_sum]`. Use function extensionality and compare the values at `y`.

Simplify using `only [Finsupp.linearCombination_single, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]`. Conclude with `h y)`. Establish `h1` using `congrArg (fun l : (G →* ℂ) →₀ ℂ => l 1) h0`. Simplify using `only [Finsupp.finset_sum_apply, Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply] at h1`. Rewrite using `[← h1]`.

Conclude with `Finset.sum_congr rfl fun i _ => by congr`.
-/
theorem sum_trivial_char_eq_zero {G ι : Type} [Monoid G] [Fintype ι] (κ : ι → (G →* ℂ)) (c : ι → ℂ)
    (h : ∀ y, ∑ i, c i * κ i y = 0) : ∑ i, (if κ i = 1 then c i else 0) = 0 := by
  have li := linearIndependent_monoidHom G ℂ
  rw [linearIndependent_iff] at li
  have h0 := li (∑ i, Finsupp.single (κ i) (c i)) (by
    rw [map_sum]
    funext y
    simp only [Finsupp.linearCombination_single, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact h y)
  have h1 := congrArg (fun l : (G →* ℂ) →₀ ℂ => l 1) h0
  simp only [Finsupp.finset_sum_apply, Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply] at h1
  rw [← h1]
  exact Finset.sum_congr rfl fun i _ => by congr

def kap (D : D7) (T : Tor D) {N N' : ℕ} (A : AddSubgroup (VC D N N')) (z : VC D N N') :
    Multiplicative A →* ℂ where
  toFun y := bc D T ((Multiplicative.toAdd y : A) : VC D N N') z / bc D T z ((Multiplicative.toAdd y : A) : VC D N N')
  map_one' := by
    simp only [toAdd_one, ZeroMemClass.coe_zero, bc_zero_left, bc_zero_right, div_one]
  map_mul' x y := by
    simp only [toAdd_mul, AddMemClass.coe_add, bc_add_left, bc_add_right, mul_div_mul_comm]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hk`. Use `h.2.2 z fun y hy => ?_` and prove the remaining obligations. Use `DFunLike.congr_fun hk (Multiplicative.ofAdd (⟨y, hy⟩ : A))` as an intermediate fact. Express the relevant statement in the definitionally equal form `bc D T y z / bc D T z y = 1 at this`.

Conclude with `((div_eq_one_iff_eq (bc_ne_zero D T z y)).1 this).symm`. Introduce `hz`. Use `MonoidHom.ext fun y => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `bc D T _ z / bc D T z _ = 1`. Rewrite using `[h.2.1 _ (Multiplicative.toAdd y).2 z hz, h.2.1 z hz _ (Multiplicative.toAdd y).2, div_one]`.
-/
theorem kap_eq_one_iff {D : D7} {T : Tor D} {N N' : ℕ} {A : AddSubgroup (VC D N N')} (h : Nice D T A)
    (z : VC D N N') : kap D T A z = 1 ↔ z ∈ A := by
  constructor
  · intro hk
    refine h.2.2 z fun y hy => ?_
    have := DFunLike.congr_fun hk (Multiplicative.ofAdd (⟨y, hy⟩ : A))
    change bc D T y z / bc D T z y = 1 at this
    exact ((div_eq_one_iff_eq (bc_ne_zero D T z y)).1 this).symm
  · intro hz
    refine MonoidHom.ext fun y => ?_
    change bc D T _ z / bc D T z _ = 1
    rw [h.2.1 _ (Multiplicative.toAdd y).2 z hz, h.2.1 z hz _ (Multiplicative.toAdd y).2, div_one]

/- English proof (translation)
Establish `h1` using `Wd_Wd D T z y e`. Rewrite `h1` using `[he, add_comm]`. Rewrite using `[Wd_Wd]`. Use `conv_rhs => rw [h1]`. Rewrite using `[smul_smul, div_mul_cancel₀ _ (bc_ne_zero D T z y)]`.
-/
theorem Wd_Wd_fixed (D : D7) (T : Tor D) {N N' : ℕ} (y z : VC D N N') (e : VC D N N' → ℂ)
    (he : Wd D T y e = e) : Wd D T y (Wd D T z e) = (bc D T y z / bc D T z y) • Wd D T z e := by
  have h1 := Wd_Wd D T z y e
  rw [he, add_comm] at h1
  rw [Wd_Wd]
  conv_rhs => rw [h1]
  rw [smul_smul, div_mul_cancel₀ _ (bc_ne_zero D T z y)]

def WdL (D : D7) (T : Tor D) {N N' : ℕ} (y : VC D N N') : (VC D N N' → ℂ) →ₗ[ℂ] (VC D N N' → ℂ) where
  toFun := Wd D T y
  map_add' := Wd_add D T y
  map_smul' := Wd_smul D T y

/- English proof (translation)
Introduce `D T N N' A hA e he hne ι _ a z hrel`. Establish `hfix` using `((hA.mem_ThSp e).1 he).2`. Take `⟨v, hv⟩` from `Function.ne_iff.1 hne`. Establish `hsum : ∑ i, a i • Wd D T (z i) e = 0`. Use function extensionality and compare the values at `w`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]`. Conclude with `hrel w`. Establish `key` using `sum_trivial_char_eq_zero (fun i => kap D T A (z i)) (fun i => a i * Wd D T (z i) e v) (by`. Introduce `y`. Establish `h1` using `congrArg (WdL D T ((Multiplicative.toAdd y : A) : VC D N N')) hsum`.

Rewrite `h1` using `[map_sum, map_zero]`. Establish `h2` using `congrFun h1 v`. Rewrite `h2` using `[Finset.sum_apply, Pi.zero_apply]`. Rewrite using `[← h2]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul]`. Express the relevant statement in the definitionally equal form `_ = a i * Wd D T _ (Wd D T (z i) e) v`. Rewrite using `[Wd_Wd_fixed D T _ _ e (hfix _ (Multiplicative.toAdd y).2)]`. Express the relevant statement in the definitionally equal form `a i * Wd D T (z i) e v * (bc D T _ _ / bc D T _ _) = a i * ((bc D T _ _ / bc D T _ _) * Wd D T (z i) e v)`. Use the proof step `ring)`.

Establish `h3 : (∑ i, (if z i ∈ A then a i else 0)) * e v = 0`. Use `Eq.trans ?_ key` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hz : z i ∈ A`.

Rewrite using `[if_pos hz, if_pos ((kap_eq_one_iff hA _).2 hz), hfix _ hz]`. Rewrite using `[if_neg hz, if_neg (fun h => hz ((kap_eq_one_iff hA _).1 h)), zero_mul]`. Conclude with `(mul_eq_zero.1 h3).resolve_right hv`.
-/
theorem coef_eq_zero : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N')), Nice D T A →
    ∀ e ∈ ThSp D T A, e ≠ 0 → ∀ (ι : Type) [Fintype ι] (a : ι → ℂ) (z : ι → VC D N N'),
      (∀ v, ∑ i, a i * Wd D T (z i) e v = 0) → ∑ i, (if z i ∈ A then a i else 0) = 0 := by
  intro D T N N' A hA e he hne ι _ a z hrel
  have hfix := ((hA.mem_ThSp e).1 he).2
  obtain ⟨v, hv⟩ := Function.ne_iff.1 hne
  have hsum : ∑ i, a i • Wd D T (z i) e = 0 := by
    funext w
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact hrel w
  have key := sum_trivial_char_eq_zero (fun i => kap D T A (z i)) (fun i => a i * Wd D T (z i) e v) (by
    intro y
    have h1 := congrArg (WdL D T ((Multiplicative.toAdd y : A) : VC D N N')) hsum
    rw [map_sum, map_zero] at h1
    have h2 := congrFun h1 v
    rw [Finset.sum_apply, Pi.zero_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    change _ = a i * Wd D T _ (Wd D T (z i) e) v
    rw [Wd_Wd_fixed D T _ _ e (hfix _ (Multiplicative.toAdd y).2)]
    change a i * Wd D T (z i) e v * (bc D T _ _ / bc D T _ _) = a i * ((bc D T _ _ / bc D T _ _) * Wd D T (z i) e v)
    ring)
  have h3 : (∑ i, (if z i ∈ A then a i else 0)) * e v = 0 := by
    refine Eq.trans ?_ key
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hz : z i ∈ A
    · rw [if_pos hz, if_pos ((kap_eq_one_iff hA _).2 hz), hfix _ hz]
    · rw [if_neg hz, if_neg (fun h => hz ((kap_eq_one_iff hA _).1 h)), zero_mul]
  exact (mul_eq_zero.1 h3).resolve_right hv

end GlobalTheory.ThetaTranslateCoef
