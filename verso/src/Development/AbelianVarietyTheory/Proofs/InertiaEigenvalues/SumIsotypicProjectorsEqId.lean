import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiagScaleApply

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.CokerL

/- English proof (translation)
Use `Finset.sum_bij (fun c _ => c.val) (fun c _ => Finset.mem_range.2 (ZMod.val_lt c)) (fun c _ d _ h => ZMod.val_injective e h) (fun i hi => ?_) (fun _ _ => rfl)` and prove the remaining obligations. Conclude with `⟨(i : ZMod e), Finset.mem_univ _, ZMod.val_cast_of_lt (Finset.mem_range.1 hi)⟩`.
-/
theorem sum_zmod_val_eq_sum_range {M : Type} [AddCommMonoid M] (e : ℕ) [NeZero e] (f : ℕ → M) :
    ∑ c : ZMod e, f c.val = ∑ i ∈ Finset.range e, f i := by
  refine Finset.sum_bij (fun c _ => c.val) (fun c _ => Finset.mem_range.2 (ZMod.val_lt c))
    (fun c _ d _ h => ZMod.val_injective e h) (fun i hi => ?_) (fun _ _ => rfl)
  exact ⟨(i : ZMod e), Finset.mem_univ _, ZMod.val_cast_of_lt (Finset.mem_range.1 hi)⟩

/- English proof (translation)
Rewrite using `[sum_zmod_val_eq_sum_range e (fun i => r ^ i), geom_sum_eq h1, hr, sub_self, zero_div]`.
-/
theorem sum_zmod_pow_eq_zero {K : Type} [Field K] (e : ℕ) [NeZero e] {r : K} (hr : r ^ e = 1)
    (h1 : r ≠ 1) : ∑ c : ZMod e, r ^ c.val = 0 := by
  rw [sum_zmod_val_eq_sum_range e (fun i => r ^ i), geom_sum_eq h1, hr, sub_self, zero_div]

/- English proof (translation)
Introduce `h1`. Apply `h` to reduce the goal to its premises. Establish `h2 : powL l (-τ) ζ = 1` using `Subtype.ext (Units.ext h1)`. Establish `h3` using `powL_add l τ (-τ) ζ`. Rewrite `h3` using `[h2, map_one, add_neg_cancel, powL_zero]`.

Conclude with `h3`.
-/
theorem root_inertia_ne_one {K : Type} [NormedField K] {l e a : ℕ} [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a] {ζ : rootsOfUnity e K} (h : ζ ≠ 1)
    (τ : ZMod a) : (TameGal.inertia ζ : TameGal K l e a).root τ ≠ 1 := by
  intro h1
  apply h
  have h2 : powL l (-τ) ζ = 1 := Subtype.ext (Units.ext h1)
  have h3 := powL_add l τ (-τ) ζ
  rw [h2, map_one, add_neg_cancel, powL_zero] at h3
  exact h3

/- English proof (translation)
Introduce `O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ P Δ v`. Use `letI := Fintype.ofFinite (rootsOfUnity e K)`. Use `haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective`. Establish `he : (e : K) ≠ 0` using `Nat.cast_ne_zero.2 (NeZero.ne e)`. Simplify using `only [isoProj, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]`.

Rewrite using `[← Finset.smul_sum, Finset.sum_comm]`. Rewrite using `[Finset.sum_eq_single (1 : rootsOfUnity e K)]`. Use `ext1 τ`. Simplify using `only [map_one, TameGal.root_one, inv_one, one_pow, Pi.smul_apply, Finset.sum_apply, diagScale_apply, one_smul, Module.End.one_apply, Finset.sum_const, Finset.card_univ, ZMod.card]`. Rewrite using `[← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ he, one_smul]`.

Introduce `ζ _ hζ ext1 τ`. Simplify using `only [Finset.sum_apply, diagScale_apply, Pi.zero_apply]`. Rewrite using `[← Finset.sum_smul, sum_zmod_pow_eq_zero e (by rw [inv_pow, TameGal.root_pow, inv_one]) (fun h => root_inertia_ne_one hζ τ (inv_eq_one.1 h)), zero_smul]`. Simplify using the standard rewrite rules.
-/
theorem sum_isoProj : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι)
    (Δ : Descent P) (v : Vec K a ι), ∑ c : ZMod e, GlobalTheory.CokerL.isoProj Δ c v = v := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ P Δ v
  letI := Fintype.ofFinite (rootsOfUnity e K)
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have he : (e : K) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne e)
  simp only [isoProj, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
  rw [← Finset.smul_sum, Finset.sum_comm]
  classical
  rw [Finset.sum_eq_single (1 : rootsOfUnity e K)]
  · ext1 τ
    simp only [map_one, TameGal.root_one, inv_one, one_pow, Pi.smul_apply, Finset.sum_apply,
      diagScale_apply, one_smul, Module.End.one_apply, Finset.sum_const, Finset.card_univ, ZMod.card]
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ he, one_smul]
  · intro ζ _ hζ
    ext1 τ
    simp only [Finset.sum_apply, diagScale_apply, Pi.zero_apply]
    rw [← Finset.sum_smul, sum_zmod_pow_eq_zero e (by rw [inv_pow, TameGal.root_pow, inv_one])
      (fun h => root_inertia_ne_one hζ τ (inv_eq_one.1 h)), zero_smul]
  · simp

end GlobalTheory.CokerL
