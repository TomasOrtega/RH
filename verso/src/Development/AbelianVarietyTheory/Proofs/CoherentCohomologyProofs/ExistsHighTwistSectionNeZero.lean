import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.VeryAmpleCompactQuasiSeparatedAffineCharts
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsTwExtendPowMul

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw.HighTwist

/- English proof (translation)
Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nontrivial_iff_subsingleton]`. Conclude with `not_subsingleton A (Module.Invertible.bijective (R := A) (M := L)).2.subsingleton`.
-/
theorem nontrivial_of_invertible (A L : Type) [CommRing A] [Nontrivial A] [AddCommGroup L]
    [Module A L] [Module.Invertible A L] : Nontrivial L := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact not_subsingleton A
    (Module.Invertible.bijective (R := A) (M := L)).2.subsingleton

variable {Y : Scheme.{0}} {H M : LB Y}

/- English proof (translation)
Establish `key : ∀ s t : LB.Sec M, s.f = t.f → s = t`. Introduce and unpack `⟨_, _⟩ ⟨_, _⟩ rfl`. Both sides reduce to the same expression. Conclude with `key _ _ (funext h)`.
-/
theorem sec_eq_zero (σ : LB.Sec M) (h : ∀ i, σ.f i = 0) : σ = 0 := by
  have key : ∀ s t : LB.Sec M, s.f = t.f → s = t := by
    rintro ⟨_, _⟩ ⟨_, _⟩ rfl
    rfl
  exact key _ _ (funext h)

def secPwOne (s : LB.Sec H) : LB.Sec (pw H 1) where
  f := s.f
  compat i j := (s.compat i j).trans (by
    change _ = (H.g i j ^ (1 : ℤ)).val * _
    rw [zpow_one]
    rfl)

/- English proof (translation)
Proceed by induction on `t, ht using Int.leInduction with`. Consider the case `base => exact ⟨a, ha⟩`. Consider the case `succ n _ ih`. Take `⟨b, hb⟩` from `ih`. Use `⟨SecOn.mulSec M n s ⊤ b, fun h => hb ?_⟩` and prove the remaining obligations.

Rewrite `h` using `[← SecOn.mulSec_restrict]`. Conclude with `(SecOn.mulSec_bijective s le_rfl).1 (h.trans (map_zero _).symm)`.
-/
theorem exists_restrict_ne_zero (s : LB.Sec H) {t₀ : ℤ} (a : SecOn (tw M H t₀) ⊤)
    (ha : SecOn.restrict _ (le_top : nonzeroLocus s ≤ ⊤) a ≠ 0) (t : ℤ) (ht : t₀ ≤ t) :
    ∃ b : SecOn (tw M H t) ⊤, SecOn.restrict _ (le_top : nonzeroLocus s ≤ ⊤) b ≠ 0 := by
  induction t, ht using Int.leInduction with
  | base => exact ⟨a, ha⟩
  | succ n _ ih =>
    obtain ⟨b, hb⟩ := ih
    refine ⟨SecOn.mulSec M n s ⊤ b, fun h => hb ?_⟩
    rw [← SecOn.mulSec_restrict] at h
    exact (SecOn.mulSec_bijective s le_rfl).1 (h.trans (map_zero _).symm)

end GlobalTheory.AbLaw.HighTwist

namespace GlobalTheory.AbLaw

open HighTwist

/- English proof (translation)
Introduce `R _ Y f hY H m s M hH hM hs`. Take `⟨x⟩` from `hY`. Establish `hx : x ∈ ⨆ i, nonzeroLocus (s i)` using `hs.1 ▸ trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 hx`. Establish `: Nonempty (nonzeroLocus (s i))` using `⟨⟨x, hi⟩⟩`.

Use `SecOn.invertible (isLB_tw hM hH 0) (hs.2 i).1` as an intermediate fact. Use `nontrivial_of_invertible Γ(Y, nonzeroLocus (s i)) (SecOn (tw M H 0) (nonzeroLocus (s i)))` as an intermediate fact. Take `⟨y, hy⟩` from `exists_ne (0 : SecOn (tw M H 0) (nonzeroLocus (s i)))`. Take `⟨hc, hq, -⟩` from `VeryAmpleCharts.compact_quasiSeparated_isAffineOpen R Y f H m s hH hs`. Take `⟨k, a, ha⟩` from `exists_tw_extend_pow_mul Y H M 1 (secPwOne (s i)) (nonzeroLocus (s i)) 0 hH hM rfl hc hq y`.

Establish `hne : SecOn.restrict _ (le_top : nonzeroLocus (s i) ≤ ⊤) a ≠ 0`. Use `fun h => hy (SecOn.tw_ext fun p l => ?_)` and prove the remaining obligations. Establish `e` using `ha p l`. Establish `h0 : SecOn.twCoord (SecOn.restrict _ (le_top : nonzeroLocus (s i) ≤ ⊤) a) p l = 0`. Rewrite using `[h]`.

Both sides reduce to the same expression. Rewrite `h0` using `[SecOn.twCoord_restrict]`. Establish `hu` using `(SecOn.isUnit_rs_of_le_nonzeroLocus (s i) l (inf_le_right.trans inf_le_right : nonzeroLocus (s i) ⊓ (M.U p ⊓ H.U l) ≤ H.U l) inf_le_left).pow k`. Conclude with `hu.mul_right_eq_zero.1 (e.symm.trans h0)`. Use `⟨0 + k * 1, fun t ht => ?_⟩` and prove the remaining obligations.

Take `⟨b, hb⟩` from `exists_restrict_ne_zero (s i) a hne t ht`. Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Establish `h0 : SecOn.topEquiv _ b = 0` using `sec_eq_zero _ (hn _)`. Rewrite `hb` using `[(SecOn.topEquiv _).map_eq_zero_iff.1 h0]`.

Conclude with `hb (map_zero _)`.
-/
theorem exists_sec_tw_ne_zero : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) [Nonempty Y] (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → ∃ (σ : LB.Sec (tw M H t)) (i : (tw M H t).ι), σ.f i ≠ 0 := by
  intro R _ Y f hY H m s M hH hM hs
  obtain ⟨x⟩ := hY
  have hx : x ∈ ⨆ i, nonzeroLocus (s i) := hs.1 ▸ trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have : Nonempty (nonzeroLocus (s i)) := ⟨⟨x, hi⟩⟩
  have := SecOn.invertible (isLB_tw hM hH 0) (hs.2 i).1
  have := nontrivial_of_invertible Γ(Y, nonzeroLocus (s i))
    (SecOn (tw M H 0) (nonzeroLocus (s i)))
  obtain ⟨y, hy⟩ := exists_ne (0 : SecOn (tw M H 0) (nonzeroLocus (s i)))
  obtain ⟨hc, hq, -⟩ := VeryAmpleCharts.compact_quasiSeparated_isAffineOpen R Y f H m s hH hs
  obtain ⟨k, a, ha⟩ := exists_tw_extend_pow_mul Y H M 1 (secPwOne (s i)) (nonzeroLocus (s i)) 0
    hH hM rfl hc hq y
  have hne : SecOn.restrict _ (le_top : nonzeroLocus (s i) ≤ ⊤) a ≠ 0 := by
    refine fun h => hy (SecOn.tw_ext fun p l => ?_)
    have e := ha p l
    have h0 : SecOn.twCoord (SecOn.restrict _ (le_top : nonzeroLocus (s i) ≤ ⊤) a) p l = 0 := by
      rw [h]; rfl
    rw [SecOn.twCoord_restrict] at h0
    have hu := (SecOn.isUnit_rs_of_le_nonzeroLocus (s i) l
      (inf_le_right.trans inf_le_right : nonzeroLocus (s i) ⊓ (M.U p ⊓ H.U l) ≤ H.U l)
      inf_le_left).pow k
    exact hu.mul_right_eq_zero.1 (e.symm.trans h0)
  refine ⟨0 + k * 1, fun t ht => ?_⟩
  obtain ⟨b, hb⟩ := exists_restrict_ne_zero (s i) a hne t ht
  by_contra hn
  push Not at hn
  have h0 : SecOn.topEquiv _ b = 0 := sec_eq_zero _ (hn _)
  rw [(SecOn.topEquiv _).map_eq_zero_iff.1 h0] at hb
  exact hb (map_zero _)

end GlobalTheory.AbLaw
