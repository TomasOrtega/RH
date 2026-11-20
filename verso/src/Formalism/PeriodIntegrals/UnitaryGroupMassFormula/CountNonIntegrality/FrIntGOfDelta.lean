import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.NGDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.LGDefs

noncomputable section

namespace PI.CntNotIntW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DiffG : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (p : PlF D), (D.s.atP p).split.isSome → ∀ t : D.host.F,
    (∀ a : 𝓞 D.host.F, ∃ n : ℤ, Algebra.trace ℚ D.host.F (t * a) = n) → (D.s.atP p).ιF t ∈ 𝒪[(D.s.atP p).Fp]

def DeltaInvG : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ p (g : Loc.SplitG (M p).L), (M p).split = some g → (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]

/- English proof (translation)
Establish `h` using `(hA p).2.2.2.2.2`. Rewrite `h` using `[hs]`. Consider the cases of `hsp : (D.s.atP p).split with`. Consider the case `none => rw [hsp] at h`. Conclude with `h.elim`.

Consider the case `some sg => rfl`.
-/
theorem split_isSome {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) (p : PlF D)
    (g : Loc.SplitG (M p).L) (hs : (M p).split = some g) : (D.s.atP p).split.isSome := by
  have h := (hA p).2.2.2.2.2
  rw [hs] at h
  cases hsp : (D.s.atP p).split with
  | none => rw [hsp] at h; exact h.elim
  | some sg => rfl

/- English proof (translation)
Introduce `D δ M hA p g hs`. Take `⟨t, ht, hne, -, hinv⟩` from `hL D δ M hA p`. Establish `hti : (D.s.atP p).ιF t ∈ 𝒪[(D.s.atP p).Fp]` using `hD D p (split_isSome hA p g hs) t ht`. Establish `hι : (D.s.atP p).ιF t ≠ 0`. Introduce `h0`.

Apply `hne` to reduce the goal to its premises. Rewrite using `[h0, mul_zero]`. Establish `e : (δ p)⁻¹ = (D.s.atP p).ιF t * (δ p * (D.s.atP p).ιF t)⁻¹`. Rewrite using `[mul_inv, mul_left_comm, mul_inv_cancel₀ hι, mul_one]`. Rewrite using `[e]`.

Conclude with `mul_mem hti hinv`.
-/
theorem deltaInvG_of (hL : LocDiff) (hD : DiffG) : DeltaInvG := by
  intro D δ M hA p g hs
  obtain ⟨t, ht, hne, -, hinv⟩ := hL D δ M hA p
  have hti : (D.s.atP p).ιF t ∈ 𝒪[(D.s.atP p).Fp] := hD D p (split_isSome hA p g hs) t ht
  have hι : (D.s.atP p).ιF t ≠ 0 := by
    intro h0; apply hne; rw [h0, mul_zero]
  have e : (δ p)⁻¹ = (D.s.atP p).ιF t * (δ p * (D.s.atP p).ιF t)⁻¹ := by
    rw [mul_inv, mul_left_comm, mul_inv_cancel₀ hι, mul_one]
  rw [e]
  exact mul_mem hti hinv

/- English proof (translation)
Unfold `Formalism.MainNotions.S.LocalSplitGroups.gpart Formalism.MainNotions.S.Lat.gS`. Use `split_ifs`. Conclude with `⟨D.host.g 1, rfl⟩`. Conclude with `⟨D.host.g 0, mul_comm _ _⟩`. Conclude with `⟨D.host.g 0 * D.host.g 1, (one_mul _).symm⟩`.
-/
theorem gS_gpart (D : Formalism.BasicNotions.D7) (p : PlF D) : ∃ k : ℕ, gS D = gpart p * k := by
  unfold Formalism.MainNotions.S.LocalSplitGroups.gpart Formalism.MainNotions.S.Lat.gS
  split_ifs
  · exact ⟨D.host.g 1, rfl⟩
  · exact ⟨D.host.g 0, mul_comm _ _⟩
  · exact ⟨D.host.g 0 * D.host.g 1, (one_mul _).symm⟩

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem ringInverse_eq {R : Type*} [MonoidWithZero R] (x y : R) (hxy : x * y = 1) (hu : IsUnit x) : Ring.inverse x = y := by
  calc Ring.inverse x = Ring.inverse x * (x * y) := by rw [hxy, mul_one]
    _ = Ring.inverse x * x * y := by rw [mul_assoc]
    _ = y := by rw [Ring.inverse_mul_cancel x hu, one_mul]

/- English proof (translation)
Introduce `D δ M hA p g hs a`. Establish `hδi : (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]` using `hΔ D δ M hA p g hs`. Establish `hδ0 : δ p ≠ 0` using `(hA p).2.1`. Take `⟨k, hk⟩` from `gS_gpart D p`. Unfold `Formalism.MainNotions.S.LocalSplitGroups.frFac`.

Distinguish the cases in `h0 : Formalism.MainNotions.S.Lat.gS D = 0`. Establish `hu : ((Formalism.MainNotions.S.LocalSplitGroups.uP p : ℚ) : D.host.E) = 0`. Simplify using `[Formalism.MainNotions.S.LocalSplitGroups.uP, h0]`. Rewrite using `[hu, map_zero, mul_zero]`. Break down `Nat.eq_zero_or_pos (D.R.rS - a.val) with hm0 | hm0` into its components or cases.

Rewrite using `[hm0, pow_zero, Ring.inverse_one, map_one]`. Conclude with `one_mem _`. Rewrite using `[zero_pow hm0.ne', Ring.inverse_zero, map_zero]`. Conclude with `zero_mem _`. Establish `hk0 : k ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hk` using `[mul_zero]`. Conclude with `h0 hk`. Establish `hgp : Formalism.MainNotions.S.LocalSplitGroups.gpart p ≠ 0`. Introduce `hg`.

Rewrite `hk` using `[hg, zero_mul]`. Conclude with `h0 hk`. Establish `huQ : (k : ℚ) * Formalism.MainNotions.S.LocalSplitGroups.uP p = 1`. Simplify using `only [Formalism.MainNotions.S.LocalSplitGroups.uP, hk]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Establish `hu : (k : D.host.E) * ((Formalism.MainNotions.S.LocalSplitGroups.uP p : ℚ) : D.host.E) = 1`. Establish `h1` using `congrArg (fun q : ℚ => (q : D.host.E)) huQ`. Move the coercions through the operations in `at h1`. Conclude with `h1`.

Establish `hbase : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE ((Formalism.MainNotions.S.LocalSplitGroups.uP p : ℚ) : D.host.E) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((δ p)⁻¹ * (k : (D.s.atP p).Fp)) = 1`. Rewrite using `[mul_right_comm, ← map_mul, ← mul_assoc, mul_inv_cancel₀ hδ0, one_mul, map_natCast, ← map_natCast (D.s.atP p).ιE k, ← map_mul, hu, map_one]`. Establish `hXY : (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE ((Formalism.MainNotions.S.LocalSplitGroups.uP p : ℚ) : D.host.E)) ^ (D.R.rS - a.val) * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((δ p)⁻¹ * (k : (D.s.atP p).Fp))) ^ (D.R.rS - a.val) = 1`. Rewrite using `[← mul_pow, hbase, one_pow]`. Rewrite using `[ringInverse_eq _ _ hXY (Units.mkOfMulEqOne _ _ hXY).isUnit]`.

Simplify using `only [map_pow, AlgEquiv.commutes, Prod.pow_fst, Prod.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]`. Conclude with `pow_mem (mul_mem hδi (natCast_mem _ k)) _`.
-/
theorem frIntG_of_delta (hΔ : DeltaInvG) : FrIntG := by
  intro D δ M hA p g hs a
  have hδi : (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp] := hΔ D δ M hA p g hs
  have hδ0 : δ p ≠ 0 := (hA p).2.1
  obtain ⟨k, hk⟩ := gS_gpart D p
  unfold Formalism.MainNotions.S.LocalSplitGroups.frFac
  by_cases h0 : Formalism.MainNotions.S.Lat.gS D = 0
  · have hu : ((Formalism.MainNotions.S.LocalSplitGroups.uP p : ℚ) : D.host.E) = 0 := by
      simp [Formalism.MainNotions.S.LocalSplitGroups.uP, h0]
    rw [hu, map_zero, mul_zero]
    rcases Nat.eq_zero_or_pos (D.R.rS - a.val) with hm0 | hm0
    · rw [hm0, pow_zero, Ring.inverse_one, map_one]
      exact one_mem _
    · rw [zero_pow hm0.ne', Ring.inverse_zero, map_zero]
      exact zero_mem _
  · have hk0 : k ≠ 0 := by
      rintro rfl; rw [mul_zero] at hk; exact h0 hk
    have hgp : Formalism.MainNotions.S.LocalSplitGroups.gpart p ≠ 0 := by
      intro hg; rw [hg, zero_mul] at hk; exact h0 hk
    have huQ : (k : ℚ) * Formalism.MainNotions.S.LocalSplitGroups.uP p = 1 := by
      simp only [Formalism.MainNotions.S.LocalSplitGroups.uP, hk]
      push_cast
      field_simp
    have hu : (k : D.host.E) * ((Formalism.MainNotions.S.LocalSplitGroups.uP p : ℚ) : D.host.E) = 1 := by
      have h1 := congrArg (fun q : ℚ => (q : D.host.E)) huQ
      push_cast at h1
      exact h1
    have hbase : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) *
        (D.s.atP p).ιE ((Formalism.MainNotions.S.LocalSplitGroups.uP p : ℚ) : D.host.E) *
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((δ p)⁻¹ * (k : (D.s.atP p).Fp)) = 1 := by
      rw [mul_right_comm, ← map_mul, ← mul_assoc, mul_inv_cancel₀ hδ0, one_mul, map_natCast,
        ← map_natCast (D.s.atP p).ιE k, ← map_mul, hu, map_one]
    have hXY : (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) *
        (D.s.atP p).ιE ((Formalism.MainNotions.S.LocalSplitGroups.uP p : ℚ) : D.host.E)) ^ (D.R.rS - a.val) *
        (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((δ p)⁻¹ * (k : (D.s.atP p).Fp))) ^ (D.R.rS - a.val) = 1 := by
      rw [← mul_pow, hbase, one_pow]
    rw [ringInverse_eq _ _ hXY (Units.mkOfMulEqOne _ _ hXY).isUnit]
    simp only [map_pow, AlgEquiv.commutes, Prod.pow_fst, Prod.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
    exact pow_mem (mul_mem hδi (natCast_mem _ k)) _

/- English proof (translation)
The claim follows from `frIntG_of_delta (deltaInvG_of hL hD)`.
-/
theorem frIntG_of (hL : LocDiff) (hD : DiffG) : FrIntG := frIntG_of_delta (deltaInvG_of hL hD)

end PI.CntNotIntW
