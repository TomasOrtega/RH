import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeLatIn

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S.Lat GlobalTheory.Mass GlobalTheory.Mass.DiscOrder Formalism.HermitianLatticesTheory
open scoped Classical

namespace GlobalTheory.Mass.DetNat

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] [FiniteDimensional K V] in

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `Y hY hXY hn hsq`. Distinguish the cases in `hYX : Y ≤ X`.

Rewrite using `[← hn, GlobalTheory.Mass.DiscOrder.idxN_eq_one.2 hYX]`. Conclude with `⟨1, rfl⟩`. Establish `hlt : X < Y` using `lt_of_le_of_ne hXY (fun h => hYX (h ▸ le_rfl))`. Take `⟨Z, hXZ, hZY⟩` from `GlobalTheory.Mass.DiscOrder.exists_covBy hY.fg hlt`. Establish `hZ : Submodule.IsLattice K Z` using `GlobalTheory.Mass.DiscOrder.lattice_between hX hY hXZ hZY.le`.

Establish `hmul : idxN Z X * idxN Y Z = idxN Y X` using `GlobalTheory.Mass.DiscOrder.idxN_mul hXZ hZY.le`. Establish `hne : idxN Y X ≠ 0` using `GlobalTheory.Mass.DiscOrder.idxN_ne_zero hX hY.fg`. Establish `h1 : idxN Y Z ≠ 1` using `fun h => not_le_of_gt hZY.lt (GlobalTheory.Mass.DiscOrder.idxN_eq_one.1 h)`. Establish `ha : idxN Z X ≠ 0` using `fun h0 => hne (by rw [← hmul, h0, zero_mul])`. Establish `hb : idxN Y Z ≠ 0` using `fun h0 => hne (by rw [← hmul, h0, mul_zero])`.

Establish `hlt' : idxN Z X < n`. Rewrite using `[← hn, ← hmul]`. Establish `ha1 : 1 ≤ idxN Z X` using `Nat.one_le_iff_ne_zero.2 ha`. Establish `hb2 : 2 ≤ idxN Y Z` using `by omega`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hsZ` using `ih _ hlt' Z hZ hXZ rfl (fun A B h1 h2 h3 => hsq A B h1 h2 (h3.trans hZY.le))`. Establish `hsY` using `hsq Z Y hXZ hZY le_rfl`. Rewrite using `[← hn, ← hmul]`. Conclude with `hsZ.mul hsY`.
-/
theorem isSquare_idxN_of_covBy {X : Submodule (𝓞 K) V} (hX : Submodule.IsLattice K X) : ∀ (n : ℕ)
    (Y : Submodule (𝓞 K) V), Submodule.IsLattice K Y → X ≤ Y → idxN Y X = n →
    (∀ Z Z' : Submodule (𝓞 K) V, X ≤ Z → Z ⋖ Z' → Z' ≤ Y → IsSquare (idxN Z' Z)) → IsSquare n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Y hY hXY hn hsq
    by_cases hYX : Y ≤ X
    · rw [← hn, GlobalTheory.Mass.DiscOrder.idxN_eq_one.2 hYX]
      exact ⟨1, rfl⟩
    · have hlt : X < Y := lt_of_le_of_ne hXY (fun h => hYX (h ▸ le_rfl))
      obtain ⟨Z, hXZ, hZY⟩ := GlobalTheory.Mass.DiscOrder.exists_covBy hY.fg hlt
      have hZ : Submodule.IsLattice K Z := GlobalTheory.Mass.DiscOrder.lattice_between hX hY hXZ hZY.le
      have hmul : idxN Z X * idxN Y Z = idxN Y X := GlobalTheory.Mass.DiscOrder.idxN_mul hXZ hZY.le
      have hne : idxN Y X ≠ 0 := GlobalTheory.Mass.DiscOrder.idxN_ne_zero hX hY.fg
      have h1 : idxN Y Z ≠ 1 := fun h => not_le_of_gt hZY.lt (GlobalTheory.Mass.DiscOrder.idxN_eq_one.1 h)
      have ha : idxN Z X ≠ 0 := fun h0 => hne (by rw [← hmul, h0, zero_mul])
      have hb : idxN Y Z ≠ 0 := fun h0 => hne (by rw [← hmul, h0, mul_zero])
      have hlt' : idxN Z X < n := by
        rw [← hn, ← hmul]
        have ha1 : 1 ≤ idxN Z X := Nat.one_le_iff_ne_zero.2 ha
        have hb2 : 2 ≤ idxN Y Z := by omega
        nlinarith
      have hsZ := ih _ hlt' Z hZ hXZ rfl (fun A B h1 h2 h3 => hsq A B h1 h2 (h3.trans hZY.le))
      have hsY := hsq Z Y hXZ hZY le_rfl
      rw [← hn, ← hmul]
      exact hsZ.mul hsY

omit [StarRing K] [FiniteDimensional K V] in

/- English proof (translation)
Take `⟨I, hmemI⟩ : ∃ I : Ideal (𝓞 K), ∀ r, r ∈ I ↔ r • y ∈ M` from `⟨M.comap (LinearMap.toSpanSingleton (𝓞 K) V y), fun r => by simp⟩`. Establish `hIP : I ≤ P` using `fun r hr => hy r ((hmemI r).1 hr)`. Establish `hI0 : I ≠ ⊥`. Establish `hy' : y ∈ Formalism.HermitianLatticesTheory.locS (nonZeroDivisors (𝓞 K)) M`. Rewrite using `[Formalism.HermitianLatticesTheory.indexBasic_locS_top (K := K) M hM.span_eq_top]`.

Conclude with `Submodule.mem_top`. Take `⟨s, hs, hsy⟩ : ∃ s ∈ nonZeroDivisors (𝓞 K), s • y ∈ M` from `hy'`. Introduce `hbot`. Establish `hsI : s ∈ I` using `(hmemI s).2 hsy`. Rewrite `hsI` using `[hbot, Ideal.mem_bot]`.

Conclude with `nonZeroDivisors.ne_zero hs hsI`. Take `⟨J, hJ⟩ : P ∣ I` from `Ideal.dvd_iff_le.2 hIP`. Establish `hIJ : I ≤ J`. Rewrite using `[hJ]`. Conclude with `Ideal.mul_le.2 fun p _ q hq => Ideal.mul_mem_left J p hq`.

Establish `hne : I ≠ J`. Introduce `hEq`. Apply `hP` to reduce the goal to its premises. Establish `h2 : P * I = 1 * I`. Rewrite using `[one_mul]`.

Use `conv_rhs => rw [hJ]`. Rewrite using `[← hEq]`. Establish `hI0' : I ≠ 0` using `by rwa [Ideal.zero_eq_bot]`. Establish `h3 : P = 1` using `mul_right_cancel₀ hI0' h2`. Rewrite `h3` using `[Ideal.one_eq_top]`. Then use the resulting hypothesis.

Take `⟨j, hjJ, hjI⟩` from `SetLike.exists_of_lt (lt_of_le_of_ne hIJ hne)`. Use `⟨j, fun hj => hjI ((hmemI j).2 hj), fun r hr => ?_⟩` and prove the remaining obligations. Establish `hrj : r * j ∈ I`. Rewrite using `[hJ]`. Conclude with `Ideal.mul_mem_mul (I := P) (J := J) hr hjJ`.

Rewrite using `[smul_smul]`. Conclude with `(hmemI _).1 hrj`.
-/
theorem exists_killed {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) {P : Ideal (𝓞 K)} (hP : P ≠ ⊤)
    (y : V) (hy : ∀ r : 𝓞 K, r • y ∈ M → r ∈ P) : ∃ j : 𝓞 K, j • y ∉ M ∧ ∀ r ∈ P, r • j • y ∈ M := by
  obtain ⟨I, hmemI⟩ : ∃ I : Ideal (𝓞 K), ∀ r, r ∈ I ↔ r • y ∈ M :=
    ⟨M.comap (LinearMap.toSpanSingleton (𝓞 K) V y), fun r => by simp⟩
  have hIP : I ≤ P := fun r hr => hy r ((hmemI r).1 hr)
  have hI0 : I ≠ ⊥ := by
    have hy' : y ∈ Formalism.HermitianLatticesTheory.locS (nonZeroDivisors (𝓞 K)) M := by
      rw [Formalism.HermitianLatticesTheory.indexBasic_locS_top (K := K) M hM.span_eq_top]
      exact Submodule.mem_top
    obtain ⟨s, hs, hsy⟩ : ∃ s ∈ nonZeroDivisors (𝓞 K), s • y ∈ M := hy'
    intro hbot
    have hsI : s ∈ I := (hmemI s).2 hsy
    rw [hbot, Ideal.mem_bot] at hsI
    exact nonZeroDivisors.ne_zero hs hsI
  obtain ⟨J, hJ⟩ : P ∣ I := Ideal.dvd_iff_le.2 hIP
  have hIJ : I ≤ J := by
    rw [hJ]
    exact Ideal.mul_le.2 fun p _ q hq => Ideal.mul_mem_left J p hq
  have hne : I ≠ J := by
    intro hEq
    apply hP
    have h2 : P * I = 1 * I := by
      rw [one_mul]
      conv_rhs => rw [hJ]
      rw [← hEq]
    have hI0' : I ≠ 0 := by rwa [Ideal.zero_eq_bot]
    have h3 : P = 1 := mul_right_cancel₀ hI0' h2
    rwa [Ideal.one_eq_top] at h3
  obtain ⟨j, hjJ, hjI⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hIJ hne)
  refine ⟨j, fun hj => hjI ((hmemI j).2 hj), fun r hr => ?_⟩
  have hrj : r * j ∈ I := by
    rw [hJ]
    exact Ideal.mul_mem_mul (I := P) (J := J) hr hjJ
  rw [smul_smul]
  exact (hmemI _).1 hrj

/- English proof (translation)
Establish `hi : IsIntegral ℤ (star (algebraMap (𝓞 K) K r))`. Use `(NumberField.RingOfIntegers.isIntegral_coe r).map (starRingEnd K).toIntAlgHom` as an intermediate fact. Simplify `this` using `[starRingEnd_apply]`. Conclude with `⟨⟨_, hi⟩, rfl⟩`.
-/
private theorem star_algebraMap_mem_range' (r : 𝓞 K) :
    star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) := by
  have hi : IsIntegral ℤ (star (algebraMap (𝓞 K) K r)) := by
    have := (NumberField.RingOfIntegers.isIntegral_coe r).map (starRingEnd K).toIntAlgHom
    simpa [starRingEnd_apply] using this
  exact ⟨⟨_, hi⟩, rfl⟩

/- English proof (translation)
Establish `hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K)` using `star_algebraMap_mem_range'`. Take `⟨hanti, -, -, hint, -⟩` from `Formalism.HermitianLatticesTheory.dualBasic (𝓞 K) K V h hs hstar`. Establish `hstar1 : ∀ k : K, k ∈ (1 : Submodule (𝓞 K) K) → star k ∈ (1 : Submodule (𝓞 K) K)`. Introduce `k hk`. Take `⟨r, rfl⟩` from `Submodule.mem_one.1 hk`.

Take `⟨t, ht⟩` from `hstar r`. Conclude with `Submodule.mem_one.2 ⟨t, ht⟩`. Establish `hsymm : ∀ x y : V, h y x = star (h x y)` using `fun x y => by`. Rewrite using `[← hs.eq x y, starRingEnd_apply]`. Introduce `n`.

Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `M hM hle hidx`. Establish `hD : Submodule.IsLattice K (dual h M)` using `(Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K V h hs hn hstar M hM).1`. Distinguish the cases in `hall : ∀ Z Z' : Submodule (𝓞 K) V, M ≤ Z → Z ⋖ Z' → Z' ≤ dual h M → IsSquare (idxN Z' Z)`.

Conclude with `isSquare_idxN_of_covBy hM n (dual h M) hD hle hidx hall`. Use `push_neg at hall`. Take `⟨Z, Z', hMZ, hcov, hZ'D, hnsq⟩` from `hall`. Establish `hZl : Submodule.IsLattice K Z` using `GlobalTheory.Mass.DiscOrder.lattice_between hM hD hMZ (hcov.le.trans hZ'D)`. Establish `hZ'l : Submodule.IsLattice K Z'` using `GlobalTheory.Mass.DiscOrder.lattice_between hM hD (hMZ.trans hcov.le) hZ'D`.

Take `⟨P, hPmax, hPiff, hPcard⟩` from `GlobalTheory.Mass.DiscOrder.exists_max_of_covBy hcov`. Establish `hcard : idxN Z' Z = Ideal.absNorm P`. Rewrite using `[hPcard, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Establish `hne0 : idxN Z' Z ≠ 0` using `GlobalTheory.Mass.DiscOrder.idxN_ne_zero hZl hZ'l.fg`. Establish `hPbot : P ≠ ⊥`.

Introduce and unpack `rfl`. Rewrite `hcard` using `[Ideal.absNorm_bot]`. Conclude with `hne0 hcard`. Establish `hconj : conjIdeal (K` using `K) P ≠ P := by`. Introduce `heq`.

Apply `hnsq` to reduce the goal to its premises. Rewrite using `[hcard]`. Conclude with `hP ⟨P, hPmax.isPrime, hPbot⟩ heq`. Take `⟨w, hwZ', hwZ⟩` from `SetLike.exists_of_lt hcov.lt`. Establish `hy : ∀ r : 𝓞 K, r • w ∈ M → r ∈ P`.

Introduce `r hr`. Assume the negation of the conclusion as `hrP`. Take `⟨s, p, hp, hsp⟩` from `hPmax.exists_inv hrP`. Apply `hwZ` to reduce the goal to its premises. Establish `hw : w = s • (r • w) + p • w` using `by rw [smul_smul, ← add_smul, hsp, one_smul]`.

Rewrite using `[hw]`. Conclude with `Z.add_mem (Z.smul_mem s (hMZ hr)) ((hPiff p).1 hp w hwZ')`. Take `⟨j, hjM, hjP⟩` from `GlobalTheory.Mass.DetNat.exists_killed hM hPmax.ne_top w hy`. Establish `hyD : j • w ∈ dual h M` using `(dual h M).smul_mem j (hZ'D hwZ')`. Establish `hyM : ∀ m ∈ M, h m (j • w) ∈ (1 : Submodule (𝓞 K) K)` using `(Formalism.HermitianLatticesTheory.dualBasic_mem_dual h M _).1 hyD`.

Establish `hyy : h (j • w) (j • w) ∈ (1 : Submodule (𝓞 K) K)`. Take `⟨T, hT⟩ : ∃ T : Ideal (𝓞 K), ∀ r, r ∈ T ↔ algebraMap (𝓞 K) K r * h (j • w) (j • w) ∈ (1 : Submodule (𝓞 K) K)` from `⟨(1 : Submodule (𝓞 K) K).comap (LinearMap.toSpanSingleton (𝓞 K) K (h (j • w) (j • w))), fun r => by simp [Algebra.smul_def]⟩`. Establish `hPT : P ≤ T`. Introduce `r hr`. Rewrite using `[hT]`.

Establish `h1 : h (j • w) (r • j • w) ∈ (1 : Submodule (𝓞 K) K)`. Rewrite using `[hsymm]`. Conclude with `hstar1 _ (hyM _ (hjP r hr))`. Rewrite `h1` using `[Formalism.HermitianLatticesTheory.locDual_h_smul_right]`. Then use the resulting hypothesis. Establish `hcT : conjIdeal (K` using `K) P ≤ T := by`.

Unfold `Formalism.HermitianLatticesTheory.conjIdeal`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `r ⟨s, hsP, hrs⟩`. Rewrite using `[SetLike.mem_coe, hT, hrs, ← Formalism.HermitianLatticesTheory.locDual_h_smul_left]`. Conclude with `hyM _ (hjP s hsP)`.

Establish `hsupT : P ⊔ conjIdeal (K` using `K) P = ⊤ := by`. Assume the negation of the conclusion as `hne`. Establish `h1 : P = P ⊔ conjIdeal (K` using `K) P := hPmax.eq_of_le hne le_sup_left`. Establish `h2 : conjIdeal (K` using `K) P ≤ P := le_sup_right.trans h1.symm.le`. Apply `hconj` to reduce the goal to its premises.

Use `le_antisymm h2 ?_` and prove the remaining obligations. Introduce `s hs'`. Take `⟨t, ht⟩` from `hstar s`. Establish `htc : t ∈ conjIdeal (K` using `K) P := Ideal.subset_span ⟨s, hs', ht⟩`. Conclude with `Ideal.subset_span ⟨t, h2 htc, by rw [ht, star_star]⟩`.

Establish `h1T : (1 : 𝓞 K) ∈ T`. Establish `hT' : (⊤ : Ideal (𝓞 K)) ≤ T`. Rewrite using `[← hsupT]`. Conclude with `sup_le hPT hcT`. Conclude with `hT' Submodule.mem_top`.

Establish `h1` using `(hT 1).1 h1T`. Rewrite `h1` using `[map_one, one_mul]`. Then use the resulting hypothesis. Use `set M' : Submodule (𝓞 K) V := M ⊔ Submodule.span (𝓞 K) {j • w} with hM'`. Establish `hMM' : M ≤ M'` using `le_sup_left`. Establish `hyM' : j • w ∈ M'` using `Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`.

Establish `hM'D : M' ≤ dual h M` using `sup_le hle ((Submodule.span_singleton_le_iff_mem _ _).2 hyD)`. Establish `hM'l : Submodule.IsLattice K M'` using `GlobalTheory.Mass.DiscOrder.lattice_between hM hD hMM' hM'D`. Establish `hM'int : M' ≤ dual h M'`. Use `(hint M').1 ?_` and prove the remaining obligations. Introduce `x hx z hz`.

Take `⟨m1, hm1, v1, hv1, rfl⟩` from `Submodule.mem_sup.1 hx`. Take `⟨m2, hm2, v2, hv2, rfl⟩` from `Submodule.mem_sup.1 hz`. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.1 hv1`. Take `⟨b, rfl⟩` from `Submodule.mem_span_singleton.1 hv2`. Establish `e1 : h m1 m2 ∈ (1 : Submodule (𝓞 K) K)` using `(Formalism.HermitianLatticesTheory.dualBasic_mem_dual h M m2).1 (hle hm2) m1 hm1`.

Establish `e2 : h m1 (b • j • w) ∈ (1 : Submodule (𝓞 K) K)`. Rewrite using `[Formalism.HermitianLatticesTheory.locDual_h_smul_right]`. Conclude with `Formalism.HermitianLatticesTheory.locDual_one_mul (Formalism.HermitianLatticesTheory.locDual_alg_mem b) (hyM m1 hm1)`. Establish `e3 : h (a • j • w) m2 ∈ (1 : Submodule (𝓞 K) K)`. Rewrite using `[Formalism.HermitianLatticesTheory.locDual_h_smul_left]`.

Use `Formalism.HermitianLatticesTheory.locDual_one_mul (hstar1 _ (Formalism.HermitianLatticesTheory.locDual_alg_mem a)) ?_` and prove the remaining obligations. Rewrite using `[hsymm]`. Conclude with `hstar1 _ (hyM m2 hm2)`. Establish `e4 : h (a • j • w) (b • j • w) ∈ (1 : Submodule (𝓞 K) K)`. Rewrite using `[Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right]`.

Conclude with `Formalism.HermitianLatticesTheory.locDual_one_mul (hstar1 _ (Formalism.HermitianLatticesTheory.locDual_alg_mem a)) (Formalism.HermitianLatticesTheory.locDual_one_mul (Formalism.HermitianLatticesTheory.locDual_alg_mem b) hyy)`. Simplify using `only [map_add, LinearMap.add_apply]`. Conclude with `add_mem (add_mem e1 e3) (add_mem e2 e4)`. Establish `hDM'le : dual h M' ≤ dual h M` using `hanti M M' hMM'`. Establish `hM'DM : M ≤ dual h M'` using `hMM'.trans hM'int`.

Establish `hk` using `GlobalTheory.Mass.DiscOrder.idxN_dual h hs hn hM (idxN M' M) M' hM'l hMM' rfl`. Establish `hm1` using `GlobalTheory.Mass.DiscOrder.idxN_mul hMM' hM'int`. Establish `hm2` using `GlobalTheory.Mass.DiscOrder.idxN_mul hM'DM hDM'le`. Establish `hn0 : n ≠ 0` using `hidx ▸ GlobalTheory.Mass.DiscOrder.idxN_ne_zero hM hD.fg`. Establish `hk0 : idxN M' M ≠ 0` using `GlobalTheory.Mass.DiscOrder.idxN_ne_zero hM hM'l.fg`.

Establish `hk1 : idxN M' M ≠ 1` using `fun h1 => hjM (GlobalTheory.Mass.DiscOrder.idxN_eq_one.1 h1 hyM')`. Establish `hnn : n = idxN M' M * idxN (dual h M') M' * idxN M' M`. Rewrite using `[← hidx, ← hm2, ← hm1, hk]`. Establish `hd0 : idxN (dual h M') M' ≠ 0`. Introduce `h0`.

Apply `hn0` to reduce the goal to its premises. Rewrite using `[hnn, h0, mul_zero, zero_mul]`. Establish `hd : idxN (dual h M') M' < n`. Establish `hk2 : 2 ≤ idxN M' M` using `by omega`. Establish `hkk : 4 ≤ idxN M' M * idxN M' M` using `by nlinarith`.

Establish `hd1 : 1 ≤ idxN (dual h M') M'` using `Nat.one_le_iff_ne_zero.2 hd0`. Combine the equalities or inequalities in the displayed calculation. Take `⟨r, hr⟩` from `ih _ hd M' hM'l hM'int rfl`. Conclude with `⟨r * idxN M' M, by rw [hnn, hr]; ring⟩`.
-/
theorem isSquare_disc (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hn : h.Nondegenerate)
    (hP : ∀ P : HeightOneSpectrum (𝓞 K), conjIdeal (K := K) P.asIdeal = P.asIdeal →
      IsSquare (Ideal.absNorm P.asIdeal)) : ∀ (n : ℕ) (M : Submodule (𝓞 K) V), Submodule.IsLattice K M →
      M ≤ dual h M → idxN (dual h M) M = n → IsSquare n := by
  have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
    star_algebraMap_mem_range'
  obtain ⟨hanti, -, -, hint, -⟩ := Formalism.HermitianLatticesTheory.dualBasic (𝓞 K) K V h hs hstar
  have hstar1 : ∀ k : K, k ∈ (1 : Submodule (𝓞 K) K) → star k ∈ (1 : Submodule (𝓞 K) K) := by
    intro k hk
    obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hk
    obtain ⟨t, ht⟩ := hstar r
    exact Submodule.mem_one.2 ⟨t, ht⟩
  have hsymm : ∀ x y : V, h y x = star (h x y) := fun x y => by
    rw [← hs.eq x y, starRingEnd_apply]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M hM hle hidx
  have hD : Submodule.IsLattice K (dual h M) :=
    (Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K V h hs hn hstar M hM).1
  by_cases hall : ∀ Z Z' : Submodule (𝓞 K) V, M ≤ Z → Z ⋖ Z' → Z' ≤ dual h M → IsSquare (idxN Z' Z)
  · exact isSquare_idxN_of_covBy hM n (dual h M) hD hle hidx hall
  push_neg at hall
  obtain ⟨Z, Z', hMZ, hcov, hZ'D, hnsq⟩ := hall
  have hZl : Submodule.IsLattice K Z :=
    GlobalTheory.Mass.DiscOrder.lattice_between hM hD hMZ (hcov.le.trans hZ'D)
  have hZ'l : Submodule.IsLattice K Z' :=
    GlobalTheory.Mass.DiscOrder.lattice_between hM hD (hMZ.trans hcov.le) hZ'D
  obtain ⟨P, hPmax, hPiff, hPcard⟩ := GlobalTheory.Mass.DiscOrder.exists_max_of_covBy hcov
  have hcard : idxN Z' Z = Ideal.absNorm P := by
    rw [hPcard, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hne0 : idxN Z' Z ≠ 0 := GlobalTheory.Mass.DiscOrder.idxN_ne_zero hZl hZ'l.fg
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hcard
    exact hne0 hcard
  have hconj : conjIdeal (K := K) P ≠ P := by
    intro heq
    apply hnsq
    rw [hcard]
    exact hP ⟨P, hPmax.isPrime, hPbot⟩ heq

  obtain ⟨w, hwZ', hwZ⟩ := SetLike.exists_of_lt hcov.lt
  have hy : ∀ r : 𝓞 K, r • w ∈ M → r ∈ P := by
    intro r hr
    by_contra hrP
    obtain ⟨s, p, hp, hsp⟩ := hPmax.exists_inv hrP
    apply hwZ
    have hw : w = s • (r • w) + p • w := by rw [smul_smul, ← add_smul, hsp, one_smul]
    rw [hw]
    exact Z.add_mem (Z.smul_mem s (hMZ hr)) ((hPiff p).1 hp w hwZ')
  obtain ⟨j, hjM, hjP⟩ := GlobalTheory.Mass.DetNat.exists_killed hM hPmax.ne_top w hy
  have hyD : j • w ∈ dual h M := (dual h M).smul_mem j (hZ'D hwZ')
  have hyM : ∀ m ∈ M, h m (j • w) ∈ (1 : Submodule (𝓞 K) K) :=
    (Formalism.HermitianLatticesTheory.dualBasic_mem_dual h M _).1 hyD

  have hyy : h (j • w) (j • w) ∈ (1 : Submodule (𝓞 K) K) := by
    obtain ⟨T, hT⟩ : ∃ T : Ideal (𝓞 K), ∀ r, r ∈ T ↔
        algebraMap (𝓞 K) K r * h (j • w) (j • w) ∈ (1 : Submodule (𝓞 K) K) :=
      ⟨(1 : Submodule (𝓞 K) K).comap (LinearMap.toSpanSingleton (𝓞 K) K (h (j • w) (j • w))),
        fun r => by simp [Algebra.smul_def]⟩
    have hPT : P ≤ T := by
      intro r hr
      rw [hT]
      have h1 : h (j • w) (r • j • w) ∈ (1 : Submodule (𝓞 K) K) := by
        rw [hsymm]
        exact hstar1 _ (hyM _ (hjP r hr))
      rwa [Formalism.HermitianLatticesTheory.locDual_h_smul_right] at h1
    have hcT : conjIdeal (K := K) P ≤ T := by
      unfold Formalism.HermitianLatticesTheory.conjIdeal
      rw [Ideal.span_le]
      rintro r ⟨s, hsP, hrs⟩
      rw [SetLike.mem_coe, hT, hrs, ← Formalism.HermitianLatticesTheory.locDual_h_smul_left]
      exact hyM _ (hjP s hsP)
    have hsupT : P ⊔ conjIdeal (K := K) P = ⊤ := by
      by_contra hne
      have h1 : P = P ⊔ conjIdeal (K := K) P := hPmax.eq_of_le hne le_sup_left
      have h2 : conjIdeal (K := K) P ≤ P := le_sup_right.trans h1.symm.le
      apply hconj
      refine le_antisymm h2 ?_
      intro s hs'
      obtain ⟨t, ht⟩ := hstar s
      have htc : t ∈ conjIdeal (K := K) P := Ideal.subset_span ⟨s, hs', ht⟩
      exact Ideal.subset_span ⟨t, h2 htc, by rw [ht, star_star]⟩
    have h1T : (1 : 𝓞 K) ∈ T := by
      have hT' : (⊤ : Ideal (𝓞 K)) ≤ T := by
        rw [← hsupT]
        exact sup_le hPT hcT
      exact hT' Submodule.mem_top
    have h1 := (hT 1).1 h1T
    rwa [map_one, one_mul] at h1

  set M' : Submodule (𝓞 K) V := M ⊔ Submodule.span (𝓞 K) {j • w} with hM'
  have hMM' : M ≤ M' := le_sup_left
  have hyM' : j • w ∈ M' := Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hM'D : M' ≤ dual h M := sup_le hle ((Submodule.span_singleton_le_iff_mem _ _).2 hyD)
  have hM'l : Submodule.IsLattice K M' := GlobalTheory.Mass.DiscOrder.lattice_between hM hD hMM' hM'D
  have hM'int : M' ≤ dual h M' := by
    refine (hint M').1 ?_
    intro x hx z hz
    obtain ⟨m1, hm1, v1, hv1, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨m2, hm2, v2, hv2, rfl⟩ := Submodule.mem_sup.1 hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv1
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hv2
    have e1 : h m1 m2 ∈ (1 : Submodule (𝓞 K) K) :=
      (Formalism.HermitianLatticesTheory.dualBasic_mem_dual h M m2).1 (hle hm2) m1 hm1
    have e2 : h m1 (b • j • w) ∈ (1 : Submodule (𝓞 K) K) := by
      rw [Formalism.HermitianLatticesTheory.locDual_h_smul_right]
      exact Formalism.HermitianLatticesTheory.locDual_one_mul (Formalism.HermitianLatticesTheory.locDual_alg_mem b) (hyM m1 hm1)
    have e3 : h (a • j • w) m2 ∈ (1 : Submodule (𝓞 K) K) := by
      rw [Formalism.HermitianLatticesTheory.locDual_h_smul_left]
      refine Formalism.HermitianLatticesTheory.locDual_one_mul (hstar1 _ (Formalism.HermitianLatticesTheory.locDual_alg_mem a)) ?_
      rw [hsymm]
      exact hstar1 _ (hyM m2 hm2)
    have e4 : h (a • j • w) (b • j • w) ∈ (1 : Submodule (𝓞 K) K) := by
      rw [Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right]
      exact Formalism.HermitianLatticesTheory.locDual_one_mul (hstar1 _ (Formalism.HermitianLatticesTheory.locDual_alg_mem a))
        (Formalism.HermitianLatticesTheory.locDual_one_mul (Formalism.HermitianLatticesTheory.locDual_alg_mem b) hyy)
    simp only [map_add, LinearMap.add_apply]
    exact add_mem (add_mem e1 e3) (add_mem e2 e4)

  have hDM'le : dual h M' ≤ dual h M := hanti M M' hMM'
  have hM'DM : M ≤ dual h M' := hMM'.trans hM'int
  have hk := GlobalTheory.Mass.DiscOrder.idxN_dual h hs hn hM (idxN M' M) M' hM'l hMM' rfl
  have hm1 := GlobalTheory.Mass.DiscOrder.idxN_mul hMM' hM'int
  have hm2 := GlobalTheory.Mass.DiscOrder.idxN_mul hM'DM hDM'le
  have hn0 : n ≠ 0 := hidx ▸ GlobalTheory.Mass.DiscOrder.idxN_ne_zero hM hD.fg
  have hk0 : idxN M' M ≠ 0 := GlobalTheory.Mass.DiscOrder.idxN_ne_zero hM hM'l.fg
  have hk1 : idxN M' M ≠ 1 := fun h1 => hjM (GlobalTheory.Mass.DiscOrder.idxN_eq_one.1 h1 hyM')
  have hnn : n = idxN M' M * idxN (dual h M') M' * idxN M' M := by
    rw [← hidx, ← hm2, ← hm1, hk]
  have hd0 : idxN (dual h M') M' ≠ 0 := by
    intro h0
    apply hn0
    rw [hnn, h0, mul_zero, zero_mul]
  have hd : idxN (dual h M') M' < n := by
    have hk2 : 2 ≤ idxN M' M := by omega
    have hkk : 4 ≤ idxN M' M * idxN M' M := by nlinarith
    have hd1 : 1 ≤ idxN (dual h M') M' := Nat.one_le_iff_ne_zero.2 hd0
    calc idxN (dual h M') M' < 4 * idxN (dual h M') M' := by omega
      _ ≤ (idxN M' M * idxN M' M) * idxN (dual h M') M' := Nat.mul_le_mul_right _ hkk
      _ = n := by rw [hnn]; ring
  obtain ⟨r, hr⟩ := ih _ hd M' hM'l hM'int rfl
  exact ⟨r * idxN M' M, by rw [hnn, hr]; ring⟩

/- English proof (translation)
Establish `hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K)` using `star_algebraMap_mem_range'`. Use `set U : Submodule K V := Submodule.span K (M : Set V) with hU`. Establish `hMU : ∀ m ∈ M, m ∈ U` using `fun m hm => Submodule.subset_span hm`. Set `φ : U →ₗ[𝓞 K] V` to `U.subtype.restrictScalars (𝓞 K)`. Establish `hφ : Function.Injective φ` using `fun a b hab => Subtype.ext hab`.

Set `g : U →ₗ⋆[K] U →ₗ[K] K` to `h.domRestrict₁₂ U U`. Establish `hgs : g.IsSymm` using `hs.domRestrict U`. Establish `hgn : g.Nondegenerate`. Unfold `LinearMap.Nondegenerate LinearMap.SeparatingLeft LinearMap.SeparatingRight`. Use `⟨fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations.

Conclude with `Submodule.coe_eq_zero.1 (ha _ (hx x))`. Conclude with `Submodule.coe_eq_zero.1 (ha _ (hx x))`. Use `set MU : Submodule (𝓞 K) U := M.comap φ with hMUdef`. Establish `hmapMU : MU.map φ = M`. Rewrite using `[hMUdef, Submodule.map_comap_eq]`.

Use `inf_eq_right.2 ?_` and prove the remaining obligations. Introduce `m hm`. Conclude with `LinearMap.mem_range.2 ⟨⟨m, hMU m hm⟩, rfl⟩`. Establish `hMUl : Submodule.IsLattice K MU`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Conclude with `Submodule.fg_of_fg_map_injective φ hφ (hmapMU ▸ hM)`. Apply `Submodule.map_injective_of_injective (f := U.subtype) Subtype.val_injective` to reduce the goal to its premises. Rewrite using `[Submodule.map_top, Submodule.range_subtype, Submodule.map_span]`. Use `conv_rhs => rw [hU]`. Use `congr 1`.

Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`. Conclude with `hu`. Introduce `hv`.

Conclude with `⟨⟨v, hMU v hv⟩, hv, rfl⟩`. Establish `hMUint : MU ≤ dual g MU`. Introduce `x hx`. Rewrite using `[Formalism.HermitianLatticesTheory.dualBasic_mem_dual]`. Introduce `y hy`.

Establish `hxD : (x : V) ∈ dualInH h M` using `hle hx`. Unfold `Formalism.MainNotions.S.Lat.dualInH at hxD`. Conclude with `(Formalism.HermitianLatticesTheory.dualBasic_mem_dual h M _).1 (Submodule.mem_inf.1 hxD).1 _ hy`. Establish `hDU` using `Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K U g hgs hgn hstar MU hMUl`. Establish `hsq` using `isSquare_disc (K := K) (V := U) g hgs hgn hP _ MU hMUl hMUint rfl`.

Establish `hidx : idxN (dual g MU) MU = idxN (dualInH h M) M`. Unfold `GlobalTheory.Mass.idxN`. Establish `h1 : MU.toAddSubgroup = M.toAddSubgroup.comap φ.toAddMonoidHom` using `AddSubgroup.ext fun _ => Iff.rfl`. Establish `h2 : (dual g MU).toAddSubgroup.map φ.toAddMonoidHom = (dualInH h M).toAddSubgroup`. Use extensionality with `v`.

Simplify using `only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, LinearMap.toAddMonoidHom_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`. Unfold `Formalism.MainNotions.S.Lat.dualInH`. Use `Submodule.mem_inf.2 ⟨?_, u.2⟩` and prove the remaining obligations.

Rewrite using `[Formalism.HermitianLatticesTheory.dualBasic_mem_dual]`. Introduce `m hm`. Conclude with `(Formalism.HermitianLatticesTheory.dualBasic_mem_dual g MU u).1 hu ⟨m, hMU m hm⟩ hm`. Introduce `hv`. Unfold `Formalism.MainNotions.S.Lat.dualInH at hv`.

Take `⟨hv1, hv2⟩` from `Submodule.mem_inf.1 hv`. Use `⟨⟨v, hv2⟩, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[Formalism.HermitianLatticesTheory.dualBasic_mem_dual]`. Introduce `y hy`. Conclude with `(Formalism.HermitianLatticesTheory.dualBasic_mem_dual h M v).1 hv1 y hy`.

Rewrite using `[h1, AddSubgroup.relIndex_comap, h2]`. Establish `hne : idxN (dual g MU) MU ≠ 0` using `GlobalTheory.Mass.DiscOrder.idxN_ne_zero hMUl hDU.1.fg`. Rewrite `hsq`, `hne` using `[hidx]`. Take `⟨r, hr⟩` from `hsq`. Establish `hgen` using `GlobalTheory.Mass.DetAgree.genIdxH_eq_idxN hle hne`.

Use `⟨r, Nat.one_le_iff_ne_zero.2 fun h0 => hne (by simp [hr, h0]), ?_⟩` and prove the remaining obligations. Unfold `Formalism.MainNotions.S.Lat.latDetH`. Rewrite using `[hgen, hr]`. Use `push_cast`. Conclude with `Real.sqrt_mul_self (Nat.cast_nonneg r)`.
-/
theorem latDetH_nat (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (ha : ∀ x, h x x = 0 → x = 0)
    (hP : ∀ P : HeightOneSpectrum (𝓞 K), conjIdeal (K := K) P.asIdeal = P.asIdeal →
      IsSquare (Ideal.absNorm P.asIdeal)) (M : Submodule (𝓞 K) V) (hM : M.FG) (hle : M ≤ dualInH h M) :
    ∃ de : ℕ, 1 ≤ de ∧ latDetH h M = de := by
  have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
    star_algebraMap_mem_range'

  set U : Submodule K V := Submodule.span K (M : Set V) with hU
  have hMU : ∀ m ∈ M, m ∈ U := fun m hm => Submodule.subset_span hm
  let φ : U →ₗ[𝓞 K] V := U.subtype.restrictScalars (𝓞 K)
  have hφ : Function.Injective φ := fun a b hab => Subtype.ext hab
  let g : U →ₗ⋆[K] U →ₗ[K] K := h.domRestrict₁₂ U U
  have hgs : g.IsSymm := hs.domRestrict U
  have hgn : g.Nondegenerate := by
    unfold LinearMap.Nondegenerate LinearMap.SeparatingLeft LinearMap.SeparatingRight
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · exact Submodule.coe_eq_zero.1 (ha _ (hx x))
    · exact Submodule.coe_eq_zero.1 (ha _ (hx x))
  set MU : Submodule (𝓞 K) U := M.comap φ with hMUdef
  have hmapMU : MU.map φ = M := by
    rw [hMUdef, Submodule.map_comap_eq]
    refine inf_eq_right.2 ?_
    intro m hm
    exact LinearMap.mem_range.2 ⟨⟨m, hMU m hm⟩, rfl⟩
  have hMUl : Submodule.IsLattice K MU := by
    refine ⟨?_, ?_⟩
    · exact Submodule.fg_of_fg_map_injective φ hφ (hmapMU ▸ hM)
    · apply Submodule.map_injective_of_injective (f := U.subtype) Subtype.val_injective
      rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span]
      conv_rhs => rw [hU]
      congr 1
      ext v
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact hu
      · intro hv
        exact ⟨⟨v, hMU v hv⟩, hv, rfl⟩
  have hMUint : MU ≤ dual g MU := by
    intro x hx
    rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    intro y hy
    have hxD : (x : V) ∈ dualInH h M := hle hx
    unfold Formalism.MainNotions.S.Lat.dualInH at hxD
    exact (Formalism.HermitianLatticesTheory.dualBasic_mem_dual h M _).1 (Submodule.mem_inf.1 hxD).1 _ hy
  have hDU := Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K U g hgs hgn hstar MU hMUl
  have hsq := isSquare_disc (K := K) (V := U) g hgs hgn hP _ MU hMUl hMUint rfl

  have hidx : idxN (dual g MU) MU = idxN (dualInH h M) M := by
    unfold GlobalTheory.Mass.idxN
    have h1 : MU.toAddSubgroup = M.toAddSubgroup.comap φ.toAddMonoidHom :=
      AddSubgroup.ext fun _ => Iff.rfl
    have h2 : (dual g MU).toAddSubgroup.map φ.toAddMonoidHom = (dualInH h M).toAddSubgroup := by
      ext v
      simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, LinearMap.toAddMonoidHom_coe]
      constructor
      · rintro ⟨u, hu, rfl⟩
        unfold Formalism.MainNotions.S.Lat.dualInH
        refine Submodule.mem_inf.2 ⟨?_, u.2⟩
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro m hm
        exact (Formalism.HermitianLatticesTheory.dualBasic_mem_dual g MU u).1 hu ⟨m, hMU m hm⟩ hm
      · intro hv
        unfold Formalism.MainNotions.S.Lat.dualInH at hv
        obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
        refine ⟨⟨v, hv2⟩, ?_, rfl⟩
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        exact (Formalism.HermitianLatticesTheory.dualBasic_mem_dual h M v).1 hv1 y hy
    rw [h1, AddSubgroup.relIndex_comap, h2]
  have hne : idxN (dual g MU) MU ≠ 0 := GlobalTheory.Mass.DiscOrder.idxN_ne_zero hMUl hDU.1.fg
  rw [hidx] at hsq hne
  obtain ⟨r, hr⟩ := hsq
  have hgen := GlobalTheory.Mass.DetAgree.genIdxH_eq_idxN hle hne
  refine ⟨r, Nat.one_le_iff_ne_zero.2 fun h0 => hne (by simp [hr, h0]), ?_⟩
  unfold Formalism.MainNotions.S.Lat.latDetH
  rw [hgen, hr]
  push_cast
  exact Real.sqrt_mul_self (Nat.cast_nonneg r)

/- English proof (translation)
Introduce `E _ _ _ S _ hP ha M hM hle`. Conclude with `latDetH_nat S.hT S.herm ha hP M hM hle`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E), (∀ (τ : E →+* ℂ) (x : E), τ (star x) = starRingEnd ℂ (τ x)) → (∀ P : HeightOneSpectrum (𝓞 E), Formalism.HermitianLatticesTheory.conjIdeal (K := E) P.asIdeal = P.asIdeal → IsSquare (Ideal.absNorm P.asIdeal)) → (∀ x : S.V, S.hT x x = 0 → x = 0) → ∀ M : Submodule (𝓞 E) S.V, M.FG → M ≤ dualIn S M → ∃ de : ℕ, 1 ≤ de ∧ latDet S M = de := by
  intro E _ _ _ S _ hP ha M hM hle
  exact latDetH_nat S.hT S.herm ha hP M hM hle

end GlobalTheory.Mass.DetNat
