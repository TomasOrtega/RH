import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSAddLeft

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.MC

open Module Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section Cnt

variable {LL : Type} [Field LL] {E : Type} [AddCommGroup E] [Module LL E]

def sumAt {r : ℕ} (e : Fin r → ℤ → E) (j : ℤ) : (Fin r → LL) →ₗ[LL] E :=
  ∑ m, (LinearMap.proj m : (Fin r → LL) →ₗ[LL] LL).smulRight (e m j)

/- English proof (translation)
Simplify using `[sumAt, LinearMap.sum_apply]`.
-/
theorem sumAt_apply {r : ℕ} (e : Fin r → ℤ → E) (j : ℤ) (c : Fin r → LL) :
    sumAt e j c = ∑ m, c m • e m j := by
  simp [sumAt, LinearMap.sum_apply]

def Ub {r : ℕ} (Fil : ℤ → Submodule LL E) (e : Fin r → ℤ → E) (j : ℤ) :
    Submodule LL (Fin r → LL) :=
  ⨅ (i : ℤ) (_ : i < j), (Fil (-i + 1)).comap (sumAt e i)

/- English proof (translation)
Simplify using `only [Ub, Submodule.mem_iInf, Submodule.mem_comap, sumAt_apply]`.
-/
theorem mem_Ub {r : ℕ} (Fil : ℤ → Submodule LL E) (e : Fin r → ℤ → E) (j : ℤ) (c : Fin r → LL) :
    c ∈ Ub Fil e j ↔ ∀ i < j, ∑ m, c m • e m i ∈ Fil (-i + 1) := by
  simp only [Ub, Submodule.mem_iInf, Submodule.mem_comap, sumAt_apply]

/- English proof (translation)
Introduce `c hc` and use `(mem_Ub Fil e j c).2 fun i hi => (mem_Ub Fil e j' c).1 hc i (by omega)`.
-/
theorem Ub_anti {r : ℕ} (Fil : ℤ → Submodule LL E) (e : Fin r → ℤ → E) {j j' : ℤ} (h : j ≤ j') :
    Ub Fil e j' ≤ Ub Fil e j := fun c hc =>
  (mem_Ub Fil e j c).2 fun i hi => (mem_Ub Fil e j' c).1 hc i (by omega)

variable {r : ℕ} {Fil : ℤ → Submodule LL E} (hFa : Antitone Fil) (D : Submodule LL E)
  [FiniteDimensional LL D] {e : Fin r → ℤ → E}

include hFa in

/- English proof (translation)
Set `ψ : ↥(Ub Fil e j) →ₗ[LL] E ⧸ Fil (-j + 1)` to `(Fil (-j + 1)).mkQ ∘ₗ sumAt e j ∘ₗ (Ub Fil e j).subtype`. Establish `hle : Ub Fil e (j + 1) ≤ Ub Fil e j` using `Ub_anti Fil e (by omega)`. Establish `hker : LinearMap.ker ψ = (Ub Fil e (j + 1)).comap (Ub Fil e j).subtype`. Use extensionality with `⟨c, hc⟩`. Simplify using `only [ψ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, sumAt_apply]`.

Rewrite using `[mem_Ub]`. Prove the components needed by the constructor for the conclusion. Introduce `h i hi`. Break down `lt_or_eq_of_le (show i ≤ j by omega) with hi' | rfl` into its components or cases. Conclude with `(mem_Ub Fil e j c).1 hc i hi'`.

Conclude with `h`. Introduce `h`. Conclude with `h j (by omega)`. Establish `hrange : LinearMap.range ψ = (D ⊓ Fil (-j)).map (Fil (-j + 1)).mkQ`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce and unpack `_ ⟨⟨c, hc⟩, rfl⟩`. Use `⟨sumAt e j c, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[sumAt_apply]`. Conclude with `Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (he m j)`. Introduce and unpack `_ ⟨w, hw, rfl⟩`.

Take `⟨c, hlow, hk⟩` from `hS j w hw`. Use `⟨⟨c, (mem_Ub Fil e j c).2 hlow⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [ψ, LinearMap.comp_apply, Submodule.coe_subtype, Submodule.mkQ_apply]`. Rewrite using `[Submodule.Quotient.eq, sumAt_apply]`. Conclude with `hk`.

Establish `h1` using `LinearMap.finrank_range_add_finrank_ker ψ`. Rewrite `h1` using `[hker, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq, hrange]`. Establish `: FiniteDimensional LL ↥(D ⊓ Fil (-j))` using `Submodule.finiteDimensional_of_le inf_le_left`. Set `φ : ↥(D ⊓ Fil (-j)) →ₗ[LL] E ⧸ Fil (-j + 1)` to `(Fil (-j + 1)).mkQ ∘ₗ (D ⊓ Fil (-j)).subtype`. Establish `hle' : D ⊓ Fil (-j + 1) ≤ D ⊓ Fil (-j)` using `inf_le_inf_left _ (hFa (by omega))`.

Establish `hφr : LinearMap.range φ = (D ⊓ Fil (-j)).map (Fil (-j + 1)).mkQ`. Simplify using `only [φ, LinearMap.range_comp, Submodule.range_subtype]`. Establish `hφk : LinearMap.ker φ = (D ⊓ Fil (-j + 1)).comap (D ⊓ Fil (-j)).subtype`. Use extensionality with `⟨x, hx⟩`. Simplify using `only [φ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_inf]`.

Conclude with `⟨fun h => ⟨(Submodule.mem_inf.1 hx).1, h⟩, fun h => h.2⟩`. Establish `h2` using `LinearMap.finrank_range_add_finrank_ker φ`. Rewrite `h2` using `[hφr, hφk, (Submodule.comapSubtypeEquivOfLe hle').finrank_eq]`. Use linear arithmetic over natural numbers and integers.
-/
theorem count_step (he : ∀ m k, e m k ∈ D ⊓ Fil (-k))
    (hS : ∀ k : ℤ, ∀ w ∈ D ⊓ Fil (-k), ∃ c : Fin r → LL,
      (∀ j < k, ∑ m, c m • e m j ∈ Fil (-j + 1)) ∧ ∑ m, c m • e m k - w ∈ Fil (-k + 1))
    (j : ℤ) :
    finrank LL ↥(Ub Fil e (j + 1)) + finrank LL ↥(D ⊓ Fil (-j)) =
      finrank LL ↥(Ub Fil e j) + finrank LL ↥(D ⊓ Fil (-j + 1)) := by
  let ψ : ↥(Ub Fil e j) →ₗ[LL] E ⧸ Fil (-j + 1) :=
    (Fil (-j + 1)).mkQ ∘ₗ sumAt e j ∘ₗ (Ub Fil e j).subtype
  have hle : Ub Fil e (j + 1) ≤ Ub Fil e j := Ub_anti Fil e (by omega)
  have hker : LinearMap.ker ψ = (Ub Fil e (j + 1)).comap (Ub Fil e j).subtype := by
    ext ⟨c, hc⟩
    simp only [ψ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, sumAt_apply]
    rw [mem_Ub]
    constructor
    · intro h i hi
      rcases lt_or_eq_of_le (show i ≤ j by omega) with hi' | rfl
      · exact (mem_Ub Fil e j c).1 hc i hi'
      · exact h
    · intro h
      exact h j (by omega)
  have hrange : LinearMap.range ψ = (D ⊓ Fil (-j)).map (Fil (-j + 1)).mkQ := by
    apply le_antisymm
    · rintro _ ⟨⟨c, hc⟩, rfl⟩
      refine ⟨sumAt e j c, ?_, rfl⟩
      rw [sumAt_apply]
      exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (he m j)
    · rintro _ ⟨w, hw, rfl⟩
      obtain ⟨c, hlow, hk⟩ := hS j w hw
      refine ⟨⟨c, (mem_Ub Fil e j c).2 hlow⟩, ?_⟩
      simp only [ψ, LinearMap.comp_apply, Submodule.coe_subtype, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq, sumAt_apply]
      exact hk
  have h1 := LinearMap.finrank_range_add_finrank_ker ψ
  rw [hker, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq, hrange] at h1
  have : FiniteDimensional LL ↥(D ⊓ Fil (-j)) := Submodule.finiteDimensional_of_le inf_le_left
  let φ : ↥(D ⊓ Fil (-j)) →ₗ[LL] E ⧸ Fil (-j + 1) := (Fil (-j + 1)).mkQ ∘ₗ (D ⊓ Fil (-j)).subtype
  have hle' : D ⊓ Fil (-j + 1) ≤ D ⊓ Fil (-j) := inf_le_inf_left _ (hFa (by omega))
  have hφr : LinearMap.range φ = (D ⊓ Fil (-j)).map (Fil (-j + 1)).mkQ := by
    simp only [φ, LinearMap.range_comp, Submodule.range_subtype]
  have hφk : LinearMap.ker φ = (D ⊓ Fil (-j + 1)).comap (D ⊓ Fil (-j)).subtype := by
    ext ⟨x, hx⟩
    simp only [φ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_inf]
    exact ⟨fun h => ⟨(Submodule.mem_inf.1 hx).1, h⟩, fun h => h.2⟩
  have h2 := LinearMap.finrank_range_add_finrank_ker φ
  rw [hφr, hφk, (Submodule.comapSubtypeEquivOfLe hle').finrank_eq] at h2
  omega

include hFa in

/- English proof (translation)
Set `H : ℤ → ℕ` to `fun j => finrank LL ↥(Ub Fil e j) + finrank LL ↥(D ⊓ Fil (-j + 1))`. Establish `hstep : ∀ j, H (j + 1) = H j`. Introduce `j`. Use `count_step hFa D he hS j` as an intermediate fact. Simplify using `only [H]`.

Rewrite using `[show -(j + 1) + 1 = -j by ring]`. Conclude with `this`. Establish `hiter : ∀ (j : ℤ) (N : ℕ), H (j + N) = H j`. Introduce `j N`. Proceed by induction on `N with`.

Consider the case `zero => simp`. Consider the case `succ N ih`. Rewrite using `[show j + ((N + 1 : ℕ) : ℤ) = (j + N) + 1 by push_cast; ring, hstep, ih]`. Establish `hzero : ∀ m i, i < 1 - a₁ → e m i = 0`. Introduce `m i hi`.

Establish `h` using `he m i`. Establish `h' : e m i ∈ D ⊓ Fil a₁` using `⟨(Submodule.mem_inf.1 h).1, hFa (by omega) (Submodule.mem_inf.1 h).2⟩`. Rewrite `h'` using `[h₁]`. Conclude with `(Submodule.mem_bot LL).1 h'`. Establish `htop : Ub Fil e (1 - a₁) = ⊤`.

Use `eq_top_iff.2 fun c _ => (mem_Ub Fil e _ c).2 fun i hi => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_zero fun m _ => by rw [hzero m i hi, smul_zero]]`. Conclude with `Submodule.zero_mem _`. Establish `hUr : finrank LL ↥(Ub Fil e (1 - a₁)) = r`. Rewrite using `[htop, finrank_top, Module.finrank_fin_fun]`.

Establish `hH0 : H (1 - a₁) = r`. Simplify using `only [H]`. Rewrite using `[show -(1 - a₁) + 1 = a₁ by ring, h₁, finrank_bot, hUr, add_zero]`. Set `N : ℕ` to `(a₁ - a₀).toNat`. Establish `hJ : -((1 - a₁) + (N : ℤ)) + 1 ≤ a₀`.

Use `Int.self_le_toNat (a₁ - a₀)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hD : D ⊓ Fil (-((1 - a₁) + (N : ℤ)) + 1) = D` using `inf_eq_left.2 (h₀.trans (hFa hJ))`. Establish `hHJ` using `hiter (1 - a₁) N`. Rewrite `hHJ` using `[hH0]`.

Simplify using `only [H] at hHJ`. Rewrite `hHJ` using `[hD]`. Establish `hU : finrank LL ↥(Ub Fil e ((1 - a₁) + (N : ℤ))) = 0` using `by omega`. Rewrite `hU` using `[Submodule.finrank_eq_zero]`. Establish `hcU : c ∈ Ub Fil e ((1 - a₁) + (N : ℤ))` using `(mem_Ub Fil e _ c).2 fun i _ => hc i`.

Rewrite `hcU` using `[hU]`. Conclude with `(Submodule.mem_bot LL).1 hcU`.
-/
theorem indep_of_span (a₀ a₁ : ℤ) (h₀ : D ≤ Fil a₀) (h₁ : D ⊓ Fil a₁ = ⊥)
    (he : ∀ m k, e m k ∈ D ⊓ Fil (-k))
    (hS : ∀ k : ℤ, ∀ w ∈ D ⊓ Fil (-k), ∃ c : Fin r → LL,
      (∀ j < k, ∑ m, c m • e m j ∈ Fil (-j + 1)) ∧ ∑ m, c m • e m k - w ∈ Fil (-k + 1))
    (hr : r ≤ finrank LL ↥D) (c : Fin r → LL) (hc : ∀ j, ∑ m, c m • e m j ∈ Fil (-j + 1)) :
    c = 0 := by
  let H : ℤ → ℕ := fun j => finrank LL ↥(Ub Fil e j) + finrank LL ↥(D ⊓ Fil (-j + 1))
  have hstep : ∀ j, H (j + 1) = H j := by
    intro j
    have := count_step hFa D he hS j
    simp only [H]
    rw [show -(j + 1) + 1 = -j by ring]
    exact this
  have hiter : ∀ (j : ℤ) (N : ℕ), H (j + N) = H j := by
    intro j N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [show j + ((N + 1 : ℕ) : ℤ) = (j + N) + 1 by push_cast; ring, hstep, ih]
  have hzero : ∀ m i, i < 1 - a₁ → e m i = 0 := by
    intro m i hi
    have h := he m i
    have h' : e m i ∈ D ⊓ Fil a₁ := ⟨(Submodule.mem_inf.1 h).1, hFa (by omega) (Submodule.mem_inf.1 h).2⟩
    rw [h₁] at h'
    exact (Submodule.mem_bot LL).1 h'
  have htop : Ub Fil e (1 - a₁) = ⊤ := by
    refine eq_top_iff.2 fun c _ => (mem_Ub Fil e _ c).2 fun i hi => ?_
    rw [Finset.sum_eq_zero fun m _ => by rw [hzero m i hi, smul_zero]]
    exact Submodule.zero_mem _
  have hUr : finrank LL ↥(Ub Fil e (1 - a₁)) = r := by
    rw [htop, finrank_top, Module.finrank_fin_fun]
  have hH0 : H (1 - a₁) = r := by
    simp only [H]
    rw [show -(1 - a₁) + 1 = a₁ by ring, h₁, finrank_bot, hUr, add_zero]
  let N : ℕ := (a₁ - a₀).toNat
  have hJ : -((1 - a₁) + (N : ℤ)) + 1 ≤ a₀ := by
    have := Int.self_le_toNat (a₁ - a₀)
    omega
  have hD : D ⊓ Fil (-((1 - a₁) + (N : ℤ)) + 1) = D := inf_eq_left.2 (h₀.trans (hFa hJ))
  have hHJ := hiter (1 - a₁) N
  rw [hH0] at hHJ
  simp only [H] at hHJ
  rw [hD] at hHJ
  have hU : finrank LL ↥(Ub Fil e ((1 - a₁) + (N : ℤ))) = 0 := by omega
  rw [Submodule.finrank_eq_zero] at hU
  have hcU : c ∈ Ub Fil e ((1 - a₁) + (N : ℤ)) := (mem_Ub Fil e _ c).2 fun i _ => hc i
  rw [hU] at hcU
  exact (Submodule.mem_bot LL).1 hcU

include hFa in

/- English proof (translation)
Take `⟨N, hN⟩ : ∃ N : ℕ, j - M < (N + 1 : ℕ)` from `⟨(j - M).toNat, by have := Int.self_le_toNat (j - M); push_cast; omega⟩`. Rewrite using `[smulS_eq_sum hf g j (N + 1) hN, Finset.sum_range_succ']`. Simplify using `only [Nat.cast_zero, sub_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, add_sub_cancel_right]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Conclude with `hFa (show -j + 1 ≤ -(j - ((i + 1 : ℕ) : ℤ)) by push_cast; omega) (hfF _)`.
-/
theorem smulS_sub_cc {M : ℤ} {f : ℤ → E} (hf : LB M f) (hfF : ∀ k, f k ∈ Fil (-k))
    (g : PowerSeries LL) (j : ℤ) :
    smulS g f j - PowerSeries.constantCoeff g • f j ∈ Fil (-j + 1) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, j - M < (N + 1 : ℕ) :=
    ⟨(j - M).toNat, by have := Int.self_le_toNat (j - M); push_cast; omega⟩
  rw [smulS_eq_sum hf g j (N + 1) hN, Finset.sum_range_succ']
  simp only [Nat.cast_zero, sub_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    add_sub_cancel_right]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact hFa (show -j + 1 ≤ -(j - ((i + 1 : ℕ) : ℤ)) by push_cast; omega) (hfF _)

include hFa in

/- English proof (translation)
Establish `hLB : ∀ m, LB (1 - a₁) (e m)`. Introduce `m i hi`. Establish `h` using `he m i`. Establish `h' : e m i ∈ D ⊓ Fil a₁` using `⟨(Submodule.mem_inf.1 h).1, hFa (by omega) (Submodule.mem_inf.1 h).2⟩`. Rewrite `h'` using `[h₁]`.

Conclude with `(Submodule.mem_bot LL).1 h'`. Establish `hF : ∀ m k, e m k ∈ Fil (-k)` using `fun m k => (Submodule.mem_inf.1 (he m k)).2`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro g _ m`.

Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `g hg`. Establish `hcc : (fun m => PowerSeries.constantCoeff (g m)) = 0`. Apply `hind` to reduce the goal to its premises.

Introduce `j`. Establish `h1 : ∑ m, smulS (g m) (e m) j ∈ Fil (-j + 1)` using `hFa (show -j + 1 ≤ ((k + 1 : ℕ) : ℤ) - j by push_cast; omega) (hg j)`. Establish `h2 : ∑ m, (smulS (g m) (e m) j - PowerSeries.constantCoeff (g m) • e m j) ∈ Fil (-j + 1)` using `Submodule.sum_mem _ fun m _ => smulS_sub_cc hFa (hLB m) (hF m) (g m) j`. Use `Submodule.sub_mem _ h1 h2` as an intermediate fact. Rewrite `this` using `[← Finset.sum_sub_distrib, Finset.sum_congr rfl fun m _ => sub_sub_cancel _ _]`. Then use the resulting hypothesis.

Establish `hX : ∀ m, PowerSeries.X ∣ g m` using `fun m => (PowerSeries.X_dvd_iff).2 (congrFun hcc m)`. Use `choose g' hg' using hX`. Establish `hshift : ∀ m (j : ℤ), smulS (g m) (e m) (j + 1) = smulS (g' m) (e m) j`. Introduce `m j`. Rewrite using `[hg' m, smulS_mul (hLB m), show (PowerSeries.X : PowerSeries LL) = PowerSeries.X ^ 1 by`.

Rewrite using `[pow_one], smulS_X_pow (LB_smulS (hLB m) (g' m)) 1]`. Simplify using the standard rewrite rules. Establish `hg'd` using `ih g' fun j => by`. Use `hg (j + 1)` as an intermediate fact. Rewrite `this` using `[Finset.sum_congr rfl fun m _ => hshift m j]`.

Rewrite `this` using `[show ((k + 1 : ℕ) : ℤ) - (j + 1) = (k : ℤ) - j by push_cast; ring]`. Then use the resulting hypothesis. Introduce `m`. Rewrite using `[hg' m, pow_succ']`. Conclude with `mul_dvd_mul_left _ (hg'd m)`.
-/
theorem dvd_of_dg (a₁ : ℤ) (h₁ : D ⊓ Fil a₁ = ⊥) (he : ∀ m k, e m k ∈ D ⊓ Fil (-k))
    (hind : ∀ c : Fin r → LL, (∀ j, ∑ m, c m • e m j ∈ Fil (-j + 1)) → c = 0) :
    ∀ (k : ℕ) (g : Fin r → PowerSeries LL),
      (∀ j : ℤ, ∑ m, smulS (g m) (e m) j ∈ Fil ((k : ℤ) - j)) → ∀ m, PowerSeries.X ^ k ∣ g m := by
  have hLB : ∀ m, LB (1 - a₁) (e m) := by
    intro m i hi
    have h := he m i
    have h' : e m i ∈ D ⊓ Fil a₁ := ⟨(Submodule.mem_inf.1 h).1, hFa (by omega) (Submodule.mem_inf.1 h).2⟩
    rw [h₁] at h'
    exact (Submodule.mem_bot LL).1 h'
  have hF : ∀ m k, e m k ∈ Fil (-k) := fun m k => (Submodule.mem_inf.1 (he m k)).2
  intro k
  induction k with
  | zero => intro g _ m; simp
  | succ k ih =>
    intro g hg
    have hcc : (fun m => PowerSeries.constantCoeff (g m)) = 0 := by
      apply hind
      intro j
      have h1 : ∑ m, smulS (g m) (e m) j ∈ Fil (-j + 1) :=
        hFa (show -j + 1 ≤ ((k + 1 : ℕ) : ℤ) - j by push_cast; omega) (hg j)
      have h2 : ∑ m, (smulS (g m) (e m) j - PowerSeries.constantCoeff (g m) • e m j) ∈ Fil (-j + 1) :=
        Submodule.sum_mem _ fun m _ => smulS_sub_cc hFa (hLB m) (hF m) (g m) j
      have := Submodule.sub_mem _ h1 h2
      rwa [← Finset.sum_sub_distrib, Finset.sum_congr rfl fun m _ => sub_sub_cancel _ _] at this
    have hX : ∀ m, PowerSeries.X ∣ g m := fun m =>
      (PowerSeries.X_dvd_iff).2 (congrFun hcc m)
    choose g' hg' using hX
    have hshift : ∀ m (j : ℤ), smulS (g m) (e m) (j + 1) = smulS (g' m) (e m) j := by
      intro m j
      rw [hg' m, smulS_mul (hLB m), show (PowerSeries.X : PowerSeries LL) = PowerSeries.X ^ 1 by
        rw [pow_one], smulS_X_pow (LB_smulS (hLB m) (g' m)) 1]
      simp
    have hg'd := ih g' fun j => by
      have := hg (j + 1)
      rw [Finset.sum_congr rfl fun m _ => hshift m j] at this
      rwa [show ((k + 1 : ℕ) : ℤ) - (j + 1) = (k : ℤ) - j by push_cast; ring] at this
    intro m
    rw [hg' m, pow_succ']
    exact mul_dvd_mul_left _ (hg'd m)

end Cnt

end Formalism.MainNotions.N.Pv.LocalLengthBound.MC
