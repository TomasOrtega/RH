import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.LocalToGlobal.KernelLattices.ColumnData.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.KernelLattices.ColumnData.StdOKP
import Formalism.LocalToGlobal.KernelLattices.ColumnData.SelfDual
import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseExP
import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.RecursiveLatticeMembership.MemLamOfIff
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker.Cd

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Host Formalism.FrobeniusOrbits

section SeamLat

open Formalism.MainNotions

variable {D : Car} {X : Fields} (s : Seam D X)

def Seam.vec {n : ℕ} (x : Sp X.E n) : Fin n → D.host.E := fun i => s.iE (x i)

/- English proof (translation)
Establish `h1 : ∀ w : D.host.E, w ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ↔ IsIntegral ℤ w` using `fun w => (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).symm`. Establish `h2 : ∀ w : X.E, w ∈ (algebraMap (𝓞 X.E) X.E).range ↔ IsIntegral ℤ w` using `fun w => (IsIntegralClosure.isIntegral_iff (A := 𝓞 X.E)).symm`. Rewrite using `[h1, h2]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `map_isIntegral_int s.iE.symm.toRingHom h` as an intermediate fact. Simplify using `using this`. Introduce `h`. Conclude with `map_isIntegral_int s.iE.toRingHom h`.
-/
theorem Seam.int_iff (z : X.E) : s.iE z ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ↔ z ∈ (algebraMap (𝓞 X.E) X.E).range := by
  have h1 : ∀ w : D.host.E, w ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ↔ IsIntegral ℤ w := fun w =>
    (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).symm
  have h2 : ∀ w : X.E, w ∈ (algebraMap (𝓞 X.E) X.E).range ↔ IsIntegral ℤ w := fun w =>
    (IsIntegralClosure.isIntegral_iff (A := 𝓞 X.E)).symm
  rw [h1, h2]
  constructor
  · intro h
    have := map_isIntegral_int s.iE.symm.toRingHom h
    simpa using this
  · intro h
    exact map_isIntegral_int s.iE.toRingHom h

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Seam.vec]`.
-/
theorem Seam.vec_add {n : ℕ} (x y : Sp X.E n) : s.vec (x + y) = s.vec x + s.vec y := by
  funext i
  simp [Seam.vec]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Seam.vec]`.
-/
theorem Seam.vec_smulE {n : ℕ} (c : X.E) (x : Sp X.E n) : s.vec (c • x) = s.iE c • s.vec x := by
  funext i
  simp [Seam.vec]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show s.iE ((r • x) i) = (r' • s.vec x) i`. Rewrite using `[Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul]`. Use `show s.iE (r : X.E) * _ = (r' : D.host.E) * _`. Rewrite using `[h]`.

Both sides reduce to the same expression.
-/
theorem Seam.vec_smulO {n : ℕ} (r : 𝓞 X.E) (r' : 𝓞 D.host.E) (h : s.iE (r : X.E) = (r' : D.host.E)) (x : Sp X.E n) : s.vec (r • x) = r' • s.vec x := by
  funext i
  show s.iE ((r • x) i) = (r' • s.vec x) i
  rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
  show s.iE (r : X.E) * _ = (r' : D.host.E) * _
  rw [h]
  rfl

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h => exact Submodule.subset_span ⟨x, h, rfl⟩`. Consider the case `zero`. Establish `: s.vec (0 : Sp X.E n) = 0` using `by funext i; simp [Seam.vec]`. Rewrite using `[this]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [s.vec_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul r x _ hx`. Take `⟨r', hr'⟩` from `(s.int_iff (r : X.E)).2 ⟨r, rfl⟩`.

Rewrite using `[s.vec_smulO r r' hr'.symm]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem Seam.vec_span {n : ℕ} (T : Set (Sp X.E n)) {x : Sp X.E n} (hx : x ∈ Submodule.span (𝓞 X.E) T) :
    s.vec x ∈ Submodule.span (𝓞 D.host.E) (s.vec '' T) := by
  induction hx using Submodule.span_induction with
  | mem x h => exact Submodule.subset_span ⟨x, h, rfl⟩
  | zero =>
    have : s.vec (0 : Sp X.E n) = 0 := by funext i; simp [Seam.vec]
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [s.vec_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    obtain ⟨r', hr'⟩ := (s.int_iff (r : X.E)).2 ⟨r, rfl⟩
    rw [s.vec_smulO r r' hr'.symm]
    exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h => exact Submodule.subset_span ⟨x, h, rfl⟩`. Consider the case `zero`. Establish `: s.vec (0 : Sp X.E n) = 0` using `by funext i; simp [Seam.vec]`. Rewrite using `[this]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [s.vec_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [s.vec_smulE]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem Seam.vec_spanE {n : ℕ} (T : Set (Sp X.E n)) {x : Sp X.E n} (hx : x ∈ Submodule.span X.E T) :
    s.vec x ∈ Submodule.span D.host.E (s.vec '' T) := by
  induction hx using Submodule.span_induction with
  | mem x h => exact Submodule.subset_span ⟨x, h, rfl⟩
  | zero =>
    have : s.vec (0 : Sp X.E n) = 0 := by funext i; simp [Seam.vec]
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [s.vec_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [s.vec_smulE]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Seam.vec]`.
-/
theorem Seam.vec_surj {n : ℕ} (y : Fin n → D.host.E) : s.vec (fun i => s.iE.symm (y i) : Sp X.E n) = y := by
  funext i
  simp [Seam.vec]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y h => exact h`. Consider the case `zero => exact ⟨0, N.zero_mem, by funext i; simp [Seam.vec]⟩`.

Consider the case `add y y' _ _ hy hy'`. Take `⟨x, hx, rfl⟩` from `hy`. Take `⟨x', hx', rfl⟩` from `hy'`. Conclude with `⟨x + x', N.add_mem hx hx', s.vec_add x x'⟩`. Consider the case `smul r y _ hy`.

Take `⟨x, hx, rfl⟩` from `hy`. Take `⟨r₀, hr₀⟩` from `(s.int_iff (s.iE.symm (r : D.host.E))).1 ⟨r, by simp⟩`. Use `⟨r₀ • x, N.smul_mem _ hx, s.vec_smulO r₀ r ?_ x⟩` and prove the remaining obligations. Use `show s.iE (algebraMap (𝓞 X.E) X.E r₀) = _`. Rewrite using `[hr₀]`.

Simplify using the standard rewrite rules. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `Submodule.subset_span ⟨x, hx, rfl⟩`.
-/
theorem Seam.mem_lat {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (y : Fin n → D.host.E) : y ∈ s.lat N ↔ ∃ x ∈ N, s.vec x = y := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem y h => exact h
    | zero => exact ⟨0, N.zero_mem, by funext i; simp [Seam.vec]⟩
    | add y y' _ _ hy hy' =>
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨x', hx', rfl⟩ := hy'
      exact ⟨x + x', N.add_mem hx hx', s.vec_add x x'⟩
    | smul r y _ hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨r₀, hr₀⟩ := (s.int_iff (s.iE.symm (r : D.host.E))).1 ⟨r, by simp⟩
      refine ⟨r₀ • x, N.smul_mem _ hx, s.vec_smulO r₀ r ?_ x⟩
      show s.iE (algebraMap (𝓞 X.E) X.E r₀) = _
      rw [hr₀]
      simp
  · rintro ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨x, hx, rfl⟩

/- English proof (translation)
Rewrite using `[Formalism.L2.Ker.Cd.IntegralLatticeDensity.SD.stdH_eq]`. Use `show _ = s.iE (∑ i, star (x i) * y i)`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hok.2]`.

Both sides reduce to the same expression.
-/
theorem Seam.stdH_vec (hok : s.Ok) {n : ℕ} (x y : Sp X.E n) :
    (letI := D.host.cmStar; stdH D.host.E n (s.vec x) (s.vec y)) = s.iE (hStd X.E n x y) := by
  rw [Formalism.L2.Ker.Cd.IntegralLatticeDensity.SD.stdH_eq]
  show _ = s.iE (∑ i, star (x i) * y i)
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hok.2]
  rfl

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨S, hS⟩` from `hN.1.fg`. Establish `h : s.lat N = Submodule.span (𝓞 D.host.E) (s.vec '' (S : Set (Sp X.E n)))`. Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `s.vec_span _ (by rw [hS]; exact hx)`. Use `Submodule.span_mono (Set.image_mono ?_)` and prove the remaining obligations. Rewrite using `[← hS]`. Conclude with `Submodule.subset_span`.

Rewrite using `[h]`. Conclude with `Submodule.fg_span (S.finite_toSet.image _)`. Rewrite using `[eq_top_iff]`. Introduce `y _`. Establish `h1 : (fun i => s.iE.symm (y i) : Sp X.E n) ∈ Submodule.span X.E (N : Set (Sp X.E n))`.

Rewrite using `[hN.1.span_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Establish `h2` using `s.vec_spanE _ h1`. Rewrite `h2` using `[s.vec_surj]`. Conclude with `Submodule.span_mono (fun z hz => Submodule.subset_span hz) h2`.

Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy x hx`. Take `⟨y₀, hy₀, rfl⟩` from `(s.mem_lat N y).1 hy`. Take `⟨x₀, hx₀, rfl⟩` from `(s.mem_lat N x).1 hx`.

Rewrite using `[s.stdH_vec hok, s.int_iff]`. Establish `h1 : y₀ ∈ dual (hStd X.E n) N` using `by rw [hN.2]; exact hy₀`. Conclude with `Submodule.mem_one.1 ((mem_dual N y₀).1 h1 x₀ hx₀)`. Introduce `h`. Use `(s.mem_lat N y).2 ⟨fun i => s.iE.symm (y i), ?_, s.vec_surj y⟩` and prove the remaining obligations.

Establish `hd : IsUnimodular (hStd X.E n) N` using `hN.2`. Unfold `IsUnimodular at hd`. Rewrite using `[← hd, mem_dual]`. Introduce `x₀ hx₀`. Establish `h1` using `h (s.vec x₀) ((s.mem_lat N _).2 ⟨x₀, hx₀, rfl⟩)`.

Rewrite `h1` using `[← s.vec_surj y, s.stdH_vec hok, s.int_iff]`. Conclude with `Submodule.mem_one.2 h1`.
-/
theorem Seam.sd_lat (hok : s.Ok) {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} (hN : IsSdLat N) :
    (letI := D.host.cmStar; IsSDLat D.host.E n (s.lat N)) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨S, hS⟩ := hN.1.fg
    have h : s.lat N = Submodule.span (𝓞 D.host.E) (s.vec '' (S : Set (Sp X.E n))) := by
      apply le_antisymm
      · refine Submodule.span_le.2 ?_
        rintro _ ⟨x, hx, rfl⟩
        exact s.vec_span _ (by rw [hS]; exact hx)
      · refine Submodule.span_mono (Set.image_mono ?_)
        rw [← hS]
        exact Submodule.subset_span
    rw [h]
    exact Submodule.fg_span (S.finite_toSet.image _)
  · rw [eq_top_iff]
    intro y _
    have h1 : (fun i => s.iE.symm (y i) : Sp X.E n) ∈ Submodule.span X.E (N : Set (Sp X.E n)) := by
      rw [hN.1.span_eq_top]; trivial
    have h2 := s.vec_spanE _ h1
    rw [s.vec_surj] at h2
    exact Submodule.span_mono (fun z hz => Submodule.subset_span hz) h2
  · intro y
    constructor
    · intro hy x hx
      obtain ⟨y₀, hy₀, rfl⟩ := (s.mem_lat N y).1 hy
      obtain ⟨x₀, hx₀, rfl⟩ := (s.mem_lat N x).1 hx
      rw [s.stdH_vec hok, s.int_iff]
      have h1 : y₀ ∈ dual (hStd X.E n) N := by rw [hN.2]; exact hy₀
      exact Submodule.mem_one.1 ((mem_dual N y₀).1 h1 x₀ hx₀)
    · intro h
      refine (s.mem_lat N y).2 ⟨fun i => s.iE.symm (y i), ?_, s.vec_surj y⟩
      have hd : IsUnimodular (hStd X.E n) N := hN.2
      unfold IsUnimodular at hd
      rw [← hd, mem_dual]
      intro x₀ hx₀
      have h1 := h (s.vec x₀) ((s.mem_lat N _).2 ⟨x₀, hx₀, rfl⟩)
      rw [← s.vec_surj y, s.stdH_vec hok, s.int_iff] at h1
      exact Submodule.mem_one.2 h1

/- English proof (translation)
Assemble the required witnesses or components as `⟨ha, hb, s.sd_lat hok hN, s.sd_lat hok hN'⟩`.
-/
theorem Seam.admissible_of_selfDual_lattices (hok : s.Ok) {a b : ℕ} (ha : Even a) (hb : Even b) {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)}
    (hN : IsSdLat N) (hN' : IsSdLat N') : TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') :=
  ⟨ha, hb, s.sd_lat hok hN, s.sd_lat hok hN'⟩

end SeamLat

section Analytic

open Formalism.MainNotions

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

/- English proof (translation)
The claim follows from `(B.thMoved_mem (B.latAll hcc hδ h0) (B.thZeroMem (IntegralLatticeDensity.SO.stdOK B hcc hδ) N N') hA).1`.
-/
theorem Base.thMoved_analytic (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hA : TaylorLogMetric.admitted D N N' L L') :
    AnalyticOnNhd ℂ (B.thMoved N N' L L') Set.univ :=
  (B.thMoved_mem (B.latAll hcc hδ h0) (B.thZeroMem (IntegralLatticeDensity.SO.stdOK B hcc hδ) N N') hA).1

/- English proof (translation)
Establish `h` using `B.thMoved_analytic hcc hδ h0 hA`. Introduce `z hz`. Conclude with `analyticAt_const.mul (h z hz)`.
-/
theorem Base.eNat_analytic (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (χ : TaylorLogMetric.IdE D → ℂ) {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hA : TaylorLogMetric.admitted D N N' L L') :
    AnalyticOnNhd ℂ (B.eNat χ N N' L L') Set.univ := by
  have h := B.thMoved_analytic hcc hδ h0 hA
  intro z hz
  exact analyticAt_const.mul (h z hz)

/- English proof (translation)
The claim follows from `(B.eNat_analytic hcc hδ h0 χ hA).contDiff`.
-/
theorem Base.eNat_contDiff (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (χ : TaylorLogMetric.IdE D → ℂ) {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hA : TaylorLogMetric.admitted D N N' L L') (k : ℕ) :
    ContDiff ℂ k (B.eNat χ N N' L L') :=
  (B.eNat_analytic hcc hδ h0 χ hA).contDiff

end Analytic

section AmbE

open Formalism.MainNotions

variable {D : Car} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ambOf_e (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) :
    (ambOf s B χ cD : Amb X).e a b N N' = fun z => B.eNat χ a b (s.lat N) (s.lat N') fun τ => z (s.iT.symm τ) := rfl

/- English proof (translation)
Introduce `N N' hN hN' k`. Rewrite using `[ambOf_e]`. Establish `h` using `B.eNat_contDiff hcc hδ h0 χ (s.admissible_of_selfDual_lattices hok ha hb hN hN') k`. Use `h.comp ?_` and prove the remaining obligations. Conclude with `contDiff_pi.2 fun τ => contDiff_apply ℂ _ (s.iT.symm τ)`.
-/
theorem ambOf_eSmooth (hok : s.Ok) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) {a b : ℕ} (ha : Even a) (hb : Even b) :
    (ambOf s B χ cD : Amb X).ESmooth a b := by
  intro N N' hN hN' k
  rw [ambOf_e]
  have h := B.eNat_contDiff hcc hδ h0 χ (s.admissible_of_selfDual_lattices hok ha hb hN hN') k
  refine h.comp ?_
  exact contDiff_pi.2 fun τ => contDiff_apply ℂ _ (s.iT.symm τ)

/- English proof (translation)
The claim follows from `Base.chiFac_ne_zero χ hχ (s.admissible_of_selfDual_lattices hok ha hb hN hN')`.
-/
theorem ambOf_chiF_ne (hok : s.Ok) (hχ : TaylorLogMetric.IsChi D χ) {a b : ℕ} (ha : Even a) (hb : Even b) {N : Submodule (𝓞 X.E) (Sp X.E a)}
    {N' : Submodule (𝓞 X.E) (Sp X.E b)} (hN : IsSdLat N) (hN' : IsSdLat N') : (ambOf s B χ cD : Amb X).chiF a b N N' ≠ 0 :=
  Base.chiFac_ne_zero χ hχ (s.admissible_of_selfDual_lattices hok ha hb hN hN')

end AmbE

/- English proof (translation)
Assemble the required witnesses or components as `⟨D.host.ccK_ne_bot, Nat.Coprime.mul_right (D.host.ccK_coprime 2 (by simp)) (D.host.ccK_coprime D.host.d (by simp))⟩`.
-/
theorem isCurveIdeal_ccK (D : Car) : TaylorLogMetric.IsCurveIdeal D D.host.ccK :=
  ⟨D.host.ccK_ne_bot, Nat.Coprime.mul_right (D.host.ccK_coprime 2 (by simp)) (D.host.ccK_coprime D.host.d (by simp))⟩

/- English proof (translation)
Take `⟨L, hL⟩` from `periodExists D cc 1 hcc one_ne_zero`. Establish `hL' : ∀ w : ℂ, w ∈ TaylorLogMetric.lamOf D cc 1 ↔ w ∈ L.lattice`. Introduce `w`. Rewrite using `[← hL]`. Both sides reduce to the same expression.

Establish `h4` using `Formalism.L2.PairingIndexBounds.Rec.eisG_eq_G _ L hL' 2 (by norm_num)`. Establish `h6` using `Formalism.L2.PairingIndexBounds.Rec.eisG_eq_G _ L hL' 3 (by norm_num)`. Use `Formalism.L2.Th1.F.discNeZero L` as an intermediate fact. Unfold `Formalism.MainNotions.TaylorLogMetric.discr Formalism.MainNotions.TaylorLogMetric.g2 Formalism.MainNotions.TaylorLogMetric.g3`. Rewrite using `[h4, h6]`.

Simplify `this` using `[PeriodPair.g₂, PeriodPair.g₃]`.
-/
theorem discr_lamOf_ne (D : Car) (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) : Formalism.MainNotions.TaylorLogMetric.discr (TaylorLogMetric.lamOf D cc 1) ≠ 0 := by
  obtain ⟨L, hL⟩ := periodExists D cc 1 hcc one_ne_zero
  have hL' : ∀ w : ℂ, w ∈ TaylorLogMetric.lamOf D cc 1 ↔ w ∈ L.lattice := by
    intro w
    rw [← hL]
    rfl
  have h4 := Formalism.L2.PairingIndexBounds.Rec.eisG_eq_G _ L hL' 2 (by norm_num)
  have h6 := Formalism.L2.PairingIndexBounds.Rec.eisG_eq_G _ L hL' 3 (by norm_num)
  have := Formalism.L2.Th1.F.discNeZero L
  unfold Formalism.MainNotions.TaylorLogMetric.discr Formalism.MainNotions.TaylorLogMetric.g2 Formalism.MainNotions.TaylorLogMetric.g3
  rw [h4, h6]
  simpa [PeriodPair.g₂, PeriodPair.g₃] using this

/- English proof (translation)
Introduce `e`. Apply `discr_lamOf_ne D cc hcc` to reduce the goal to its premises. Rewrite using `[← (show δ ^ 12 = Formalism.MainNotions.TaylorLogMetric.discr (TaylorLogMetric.lamOf D cc 1) from hδ), e]`. Evaluate the numerical expressions.
-/
theorem twelfth_root_disc_ne_zero (D : Car) (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) {δ : ℂ} (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : δ ≠ 0 := by
  intro e
  apply discr_lamOf_ne D cc hcc
  rw [← (show δ ^ 12 = Formalism.MainNotions.TaylorLogMetric.discr (TaylorLogMetric.lamOf D cc 1) from hδ), e]
  norm_num

end Formalism.L2.Ker.Cd

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.Col Formalism.L2.GlobalTheoryTheory.Jets

section OverColDat

variable (d : ColDat)

/- English proof (translation)
Use `⟨fun τ x => ?_, fun x => Formalism.BasicNotions.Examples₂.star_eq_conj d.host x⟩` and prove the remaining obligations. Use `show d.what₂.embLL (d.embE (d.host.sigmaOf (d.eTau τ : d.R.GG) x)) = d.host.φ₀ (d.host.sigmaOf (d.eTau τ : d.R.GG) x)`. Rewrite using `[← h]`. Both sides reduce to the same expression.
-/
theorem seamD_ok (h : d.what₂.embLL.comp d.embE = d.host.φ₀) : (seamD d).Ok := by
  refine ⟨fun τ x => ?_, fun x => Formalism.BasicNotions.Examples₂.star_eq_conj d.host x⟩
  show d.what₂.embLL (d.embE (d.host.sigmaOf (d.eTau τ : d.R.GG) x)) = d.host.φ₀ (d.host.sigmaOf (d.eTau τ : d.R.GG) x)
  rw [← h]
  rfl

variable {d} (I : AmbIn d)

/- English proof (translation)
The claim follows from `I.K.delta_pow_twelve_eq_discr`.
-/
theorem AmbIn.ambient_isTwelfthRootDisc : Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice (carD d) d.host.ccK I.K.δ := I.K.delta_pow_twelve_eq_discr

/- English proof (translation)
The claim follows from `Cd.twelfth_root_disc_ne_zero (carD d) d.host.ccK d.host.ccK_ne_bot I.ambient_isTwelfthRootDisc`.
-/
theorem AmbIn.δ_ne : I.K.δ ≠ 0 := Cd.twelfth_root_disc_ne_zero (carD d) d.host.ccK d.host.ccK_ne_bot I.ambient_isTwelfthRootDisc

/- English proof (translation)
The claim follows from `Cd.IntegralLatticeDensity.SO.stdOK I.B (Cd.isCurveIdeal_ccK (carD d)) I.ambient_isTwelfthRootDisc`.
-/
theorem AmbIn.stdOK : I.B.StdOK := Cd.IntegralLatticeDensity.SO.stdOK I.B (Cd.isCurveIdeal_ccK (carD d)) I.ambient_isTwelfthRootDisc

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem AmbIn.amb_σ₀ : I.amb.σ₀ = d.σ₀ := rfl

/- English proof (translation)
The claim follows from `Cd.ambOf_eSmooth (seamD d) I.B I.χ I.cD (seamD_ok d h) (Cd.isCurveIdeal_ccK (carD d)) I.ambient_isTwelfthRootDisc I.δ_ne (factNEven d.R i) (factNEven d.R j)`.
-/
theorem AmbIn.eSmooth (h : d.what₂.embLL.comp d.embE = d.host.φ₀) (i j : ℕ) : I.amb.ESmooth (d.R.N i) (d.R.N j) :=
  Cd.ambOf_eSmooth (seamD d) I.B I.χ I.cD (seamD_ok d h) (Cd.isCurveIdeal_ccK (carD d)) I.ambient_isTwelfthRootDisc I.δ_ne (factNEven d.R i) (factNEven d.R j)

/- English proof (translation)
The claim follows from `Cd.ambOf_chiF_ne (seamD d) I.B I.χ I.cD (seamD_ok d h) hχ (factNEven d.R i) (factNEven d.R j) hN hN'`.
-/
theorem AmbIn.chiF_ne (h : d.what₂.embLL.comp d.embE = d.host.φ₀) (hχ : Cd.TaylorLogMetric.IsChi (carD d) I.χ) (i j : ℕ)
    {N : Submodule (𝓞 d.X.E) (Sp d.X.E (d.R.N i))} {N' : Submodule (𝓞 d.X.E) (Sp d.X.E (d.R.N j))} (hN : IsSdLat N) (hN' : IsSdLat N') :
    I.amb.chiF (d.R.N i) (d.R.N j) N N' ≠ 0 :=
  Cd.ambOf_chiF_ne (seamD d) I.B I.χ I.cD (seamD_ok d h) hχ (factNEven d.R i) (factNEven d.R j) hN hN'

end OverColDat

end Formalism.L2.Ker
