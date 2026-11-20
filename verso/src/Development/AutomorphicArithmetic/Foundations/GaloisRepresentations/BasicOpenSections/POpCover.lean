import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.OpCover
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.BTrPushQ

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt)
open UpperTheory.Gal.crystallineComparison (PtId fn)
open UpperTheory.Gal UpperTheory.Gal.Mod

/- English proof (translation)
Use function extensionality and compare the values at `Ω _ _ x`. Simplify using `only [Wt.push, Wt.const]`. Rewrite using `[← hδ Ω x]`. Take `hs | hs` from `(fib u x).infinite_or_finite`. Rewrite using `[hs.ncard, Nat.cast_zero]`.

Conclude with `finsum_mem_eq_zero_of_infinite (by simpa [Function.support_const one_ne_zero] using hs)`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hs, Set.ncard_eq_toFinset_card _ hs]`. Simplify using the standard rewrite rules.
-/
private theorem push_const_one {Z Z' : Scheme.{0}} (u : Z ⟶ Z') [IsFinite u] (δ : ℕ)
    (hδ : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ Z'), (fib u x).ncard = δ) :
    (Wt.const Z 1).push u = Wt.const Z' (δ : ℤ) := by
  funext Ω _ _ x
  simp only [Wt.push, Wt.const]
  rw [← hδ Ω x]
  obtain hs | hs := (fib u x).infinite_or_finite
  · rw [hs.ncard, Nat.cast_zero]
    exact finsum_mem_eq_zero_of_infinite (by simpa [Function.support_const one_ne_zero] using hs)
  · rw [finsum_mem_eq_finite_toFinset_sum _ hs, Set.ncard_eq_toFinset_card _ hs]
    simp

/- English proof (translation)
Introduce `l _ S S' c c' u _ δ hw hw' hp hf hl hδ k i`. Use `haveI := c.fin`. Use `haveI := c'.fin`. Establish `hadic` using `TranscendenceTraces.all_holds.2.2`. Establish `hwl` using `TranscendenceTraces.all_holds.1.2.2.1`.

Establish `hwc : IsWt (u ≫ c'.p) (Wt.const c.Z 1)`. Establish `h0` using `c.wt`. Rewrite `h0` using `[hw, ← hp]`. Conclude with `h0`. Establish `hwc' : IsWt c'.p (Wt.const c'.Z 1)`.

Establish `h0` using `c'.wt`. Rewrite `h0` using `[hw']`. Conclude with `h0`. Establish `hpush` using `TranscendenceTraces.trPushQ_of TranscendenceTraces.trPush_holds hadic.2.1 TranscendenceTraces.wtPush_holds l k i u c'.p (Wt.const c.Z 1) hwc hl`. Rewrite `hpush` using `[push_const_one u δ hδ]`.

Establish `hcomp` using `hadic.2.2.2.1 l k i c'.p (𝟙 S) (Wt.const c'.Z 1) (Wt.const S (δ : ℤ)) hwc' (hwl.2.2 (𝟙 S) (δ : ℤ)) hl`. Establish `hmul : Wt.mul c'.p (Wt.const c'.Z 1) (Wt.const S (δ : ℤ)) = Wt.const c'.Z (δ : ℤ)`. Use function extensionality and compare the values at `Ω _ _ z`. Simplify using `[Wt.mul, Wt.const]`. Rewrite `hcomp` using `[Category.comp_id, hmul, TranscendenceTraces.trIdQ_holds GlobalTheory.T.etaleCohomology_coefficientRing_invariance l k i S δ hl, LinearMap.smul_comp, LinearMap.id_comp]`.

Establish `hpull : pullHQ l (sch.map (u ≫ c'.f)) k i = pullHQ l (sch.map u) k i ∘ₗ pullHQ l (sch.map c'.f) k i`. Simplify using `only [pullHQ, Functor.map_comp, pullHl_comp, LinearMap.baseChange_comp]`. Unfold `TranscendenceTraces.Corr.opQ`. Rewrite using `[← hf, ← hp, hw, hw', hpull, ← LinearMap.comp_assoc, hpush, hcomp, LinearMap.smul_comp]`. Use `first`.

Consider the case `rfl`. Consider the case `simp only [Int.cast_natCast, Nat.cast_smul_eq_nsmul]`. Consider the case `(norm_cast; simp [Nat.cast_smul_eq_nsmul])`.
-/
theorem UpperTheory.Gal.Mod.opCover :
    OpCover := by
  intro l _ S S' c c' u _ δ hw hw' hp hf hl hδ k i
  haveI := c.fin
  haveI := c'.fin
  have hadic := TranscendenceTraces.all_holds.2.2
  have hwl := TranscendenceTraces.all_holds.1.2.2.1
  have hwc : IsWt (u ≫ c'.p) (Wt.const c.Z 1) := by
    have h0 := c.wt
    rw [hw, ← hp] at h0
    exact h0
  have hwc' : IsWt c'.p (Wt.const c'.Z 1) := by
    have h0 := c'.wt
    rw [hw'] at h0
    exact h0
  have hpush := TranscendenceTraces.trPushQ_of TranscendenceTraces.trPush_holds hadic.2.1 TranscendenceTraces.wtPush_holds l k i u c'.p
    (Wt.const c.Z 1) hwc hl
  rw [push_const_one u δ hδ] at hpush
  have hcomp := hadic.2.2.2.1 l k i c'.p (𝟙 S) (Wt.const c'.Z 1) (Wt.const S (δ : ℤ)) hwc'
    (hwl.2.2 (𝟙 S) (δ : ℤ)) hl
  have hmul : Wt.mul c'.p (Wt.const c'.Z 1) (Wt.const S (δ : ℤ)) = Wt.const c'.Z (δ : ℤ) := by
    funext Ω _ _ z
    simp [Wt.mul, Wt.const]
  rw [Category.comp_id, hmul, TranscendenceTraces.trIdQ_holds GlobalTheory.T.etaleCohomology_coefficientRing_invariance l k i S δ hl,
    LinearMap.smul_comp, LinearMap.id_comp] at hcomp
  have hpull : pullHQ l (sch.map (u ≫ c'.f)) k i =
      pullHQ l (sch.map u) k i ∘ₗ pullHQ l (sch.map c'.f) k i := by
    simp only [pullHQ, Functor.map_comp, pullHl_comp, LinearMap.baseChange_comp]
  unfold TranscendenceTraces.Corr.opQ
  rw [← hf, ← hp, hw, hw', hpull, ← LinearMap.comp_assoc, hpush, hcomp, LinearMap.smul_comp]
  first
    | rfl
    | simp only [Int.cast_natCast, Nat.cast_smul_eq_nsmul]
    | (norm_cast; simp [Nat.cast_smul_eq_nsmul])
