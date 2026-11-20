import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveIsOrbit

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace CoverDenseAlt.Dense0

open GroundTheory.Heights₂.Heights (Coord Cone blockIdx ArithVariety BlockNonzero coordField coordVec evalCone coordDeg)

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : K → ℕ}
  (e : ∀ k, ι k ≃ Fin (n k + 1))

def E : (Σ k, ι k) ≃ Coord n := Equiv.sigmaCongrRight e

def φ : MRing ι ≃+* MvPolynomial (Coord n) ℤ := (renameEquiv ℤ (E e)).toRingEquiv

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem φ_apply (f : MRing ι) : φ e f = rename (E e) f := rfl

omit [Fintype K] [DecidableEq K] in
/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[φ_apply, support_rename_of_injective (E e).injective]`. Take `⟨m₀, hm₀, rfl⟩` from `Finset.mem_image.mp hm`. Rewrite using `[← hf m₀ hm₀ k]`. Use `(Fintype.sum_equiv (e k) _ _ fun i => ?_).symm` and prove the remaining obligations.

Conclude with `(Finsupp.mapDomain_apply (E e).injective m₀ ⟨k, i⟩).symm`.
-/
theorem homog_rename {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    IsMultiHomog (ι := blockIdx n) (φ e f) a := by
  classical
  intro m hm k
  rw [φ_apply, support_rename_of_injective (E e).injective] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := Finset.mem_image.mp hm
  rw [← hf m₀ hm₀ k]
  refine (Fintype.sum_equiv (e k) _ _ fun i => ?_).symm
  exact (Finsupp.mapDomain_apply (E e).injective m₀ ⟨k, i⟩).symm

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
/- English proof (translation)
The claim follows from `Ideal.apply_mem_of_equiv_iff`.
-/
theorem mem_map_iff (P : Ideal (MRing ι)) (f : MRing ι) : φ e f ∈ P.map (φ e) ↔ f ∈ P :=
  Ideal.apply_mem_of_equiv_iff

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
/- English proof (translation)
Establish `h1 : φ e (C a) = C a` using `rename_C (E e) a`. Rewrite `ha` using `[← h1, mem_map_iff]`. Establish `h : a ∈ P.comap (C : ℤ →+* MRing ι)` using `Ideal.mem_comap.mpr ha`. Rewrite `h` using `[hP]`. Conclude with `Ideal.mem_bot.mp h`.
-/
theorem horiz {P : Ideal (MRing ι)} (hP : IsHorizontal P) (a : ℤ)
    (ha : (C a : MvPolynomial (Coord n) ℤ) ∈ P.map (φ e)) : a = 0 := by
  have h1 : φ e (C a) = C a := rename_C (E e) a
  rw [← h1, mem_map_iff] at ha
  have h : a ∈ P.comap (C : ℤ →+* MRing ι) := Ideal.mem_comap.mpr ha
  rw [hP] at h
  exact Ideal.mem_bot.mp h

def var {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) : ArithVariety n where
  ideal := P.map (φ e)
  isPrime := by
    have := hP.2.1.1
    exact Ideal.map_isPrime_of_equiv (φ e)
  homogeneous f hf m := by
    refine GroundTheory.Heights₂.Heights.CurveIsOrbit.component_mem ?_ hf m
    obtain ⟨S, hS, rfl⟩ := hP.2.1.2.1
    refine ⟨φ e '' S, ?_, Ideal.map_span _ _⟩
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨a, ha⟩ := hS g hg
    exact ⟨a, homog_rename e ha⟩
  relevant k := by
    obtain ⟨i, hi⟩ := hP.2.1.2.2 k
    refine ⟨e k i, fun h => hi ?_⟩
    have h1 : φ e (X ⟨k, i⟩) = X ⟨k, e k i⟩ := by
      rw [φ_apply, rename_X]
      rfl
    rw [← h1] at h
    exact (mem_map_iff e P _).mp h
  horizontal a ha := horiz e hP.2.2.1 a ha

def back {F : Type} (z : Cone n F) : (Σ k, ι k) → F := fun p => z p.1 (e p.1 p.2)

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
/- English proof (translation)
Take `⟨i, hi⟩` from `Function.ne_iff.mp (hz k)`. Use `⟨(e k).symm i, ?_⟩` and prove the remaining obligations. Simplify `hi` using `[back]`.
-/
theorem back_nonzero {F : Type} [Zero F] {z : Cone n F} (hz : BlockNonzero z) (k : K) :
    ∃ i, back e z ⟨k, i⟩ ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp (hz k)
  refine ⟨(e k).symm i, ?_⟩
  simpa [back] using hi

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
/- English proof (translation)
Rewrite using `[φ_apply, evalCone, eval₂_rename, aeval_def]`. Use `congr 1`.
-/
theorem evalCone_φ {F : Type} [CommRing F] (z : Cone n F) (f : MRing ι) :
    evalCone z (φ e f) = aeval (back e z) f := by
  rw [φ_apply, evalCone, eval₂_rename, aeval_def]
  congr 1

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
/- English proof (translation)
Establish `h : τ (aeval (back e z) f) = evalCone (fun k i => τ (z k i)) (φ e f)`. Rewrite using `[evalCone_φ]`. Conclude with `comp_aeval_apply (R := ℤ) (back e z) τ.toIntAlgHom f`. Rewrite using `[← h]`. Conclude with `(map_eq_zero τ).symm`.
-/
theorem aeval_back_eq_zero_iff {L F : Type} [Field L] [Field F] (τ : L →+* F) (z : Cone n L) (f : MRing ι) :
    aeval (back e z) f = 0 ↔ evalCone (fun k i => τ (z k i)) (φ e f) = 0 := by
  have h : τ (aeval (back e z) f) = evalCone (fun k i => τ (z k i)) (φ e f) := by
    rw [evalCone_φ]
    exact comp_aeval_apply (R := ℤ) (back e z) τ.toIntAlgHom f
  rw [← h]
  exact (map_eq_zero τ).symm

def line (A : HermLine ι) (hA : IsSmoothHerm A) : GroundTheory.Heights₂.Heights.HermLine n where
  deg := A.a
  metric z := A.h (back e z)
  metric_pos z hz := A.pos _ (back_nonzero e hz)
  metric_smul c z hc _ := A.smul c (back e z) hc
  metric_smooth := by
    have hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Cone n ℂ => back e z) :=
      contDiff_pi.2 fun p => contDiff_pi.1 (contDiff_pi.1 contDiff_id p.1) (e p.1 p.2)
    exact ContDiffOn.comp hA hu.contDiffOn fun z hz => back_nonzero e hz

omit [DecidableEq K] in
/- English proof (translation)
Unfold `lineHt ptHt GroundTheory.Heights₂.Heights.height`. Establish `h1 : ∀ (v : FinitePlace (coordField x)) (k : K), (⨆ i, v (back e (coordVec x) ⟨k, i⟩)) = ⨆ i, v (coordVec x k i)` using `fun v k => (e k).iSup_comp (g := fun i => v (coordVec x k i))`. Simplify using `only [h1]`. Use `congr 1`.
-/
theorem height_eq (A : HermLine ι) (hA : IsSmoothHerm A) (x : Cone n (AlgebraicClosure ℚ)) :
    lineHt A (coordField x) (back e (coordVec x)) = GroundTheory.Heights₂.Heights.height (line e A hA) x := by
  unfold lineHt ptHt GroundTheory.Heights₂.Heights.height
  have h1 : ∀ (v : FinitePlace (coordField x)) (k : K),
      (⨆ i, v (back e (coordVec x) ⟨k, i⟩)) = ⨆ i, v (coordVec x k i) := fun v k =>
    (e k).iSup_comp (g := fun i => v (coordVec x k i))
  simp only [h1]
  congr 1

end CoverDenseAlt.Dense0

open CoverDenseAlt.Dense0 GroundTheory.Heights₂.Heights in
/- English proof (translation)
Introduce `K _ ι _ P d hP J _ A hA`. Establish `hcard : ∀ k, Fintype.card (ι k) = (Fintype.card (ι k) - 1) + 1` using `fun k => by`. Take `⟨i, -⟩` from `hP.2.1.2.2 k`. Establish `: 0 < Fintype.card (ι k)` using `Fintype.card_pos_iff.mpr ⟨i⟩`. Use linear arithmetic over natural numbers and integers.

Set `n : K → ℕ` to `fun k => Fintype.card (ι k) - 1`. Set `e : ∀ k, ι k ≃ Fin (n k + 1)` to `fun k => Fintype.equivFinOfCardEq (hcard k)`. Take `⟨S, C₀, hS, hdense, hC₀⟩` from `DenseBoundedHeight.main K n (var e hP)`. Use `choose m C hC using fun j => HeightComparison.main K n (var e hP) (line e (A j) (hA j))`. Use `⟨∑ j, |m j * C₀ + C j|, ?_⟩` and prove the remaining obligations.

Introduce and unpack `f ⟨a, ha⟩ hf`. Establish `hex : ∃ x ∈ S, evalCone x (φ e f) ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hf ((mem_map_iff e P _).mp (hdense a (φ e f) ((geoMultiHomog_iff _ _).mp (homog_rename e ha)) hcon))`.

Take `⟨x, hxS, hx⟩` from `hex`. Establish `hxP` using `hS hxS`. Establish `hval` using `aeval_back_eq_zero_iff e (algebraMap (coordField x) (AlgebraicClosure ℚ)) (coordVec x)`. Use `⟨coordField x, inferInstance, inferInstance, back e (coordVec x), ⟨fun k => ?_, fun g hg => ?_⟩, ?_, fun j => ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `back_nonzero e hxP.1 k`.

Conclude with `⟨i, fun h => hi (congrArg Subtype.val h)⟩`. Conclude with `(hval g).mpr (hxP.2 _ (Ideal.mem_map_of_mem _ hg))`. Conclude with `fun h => hx ((hval f).mp h)`. Rewrite using `[height_eq e (A j) (hA j)]`. Establish `h1` using `hC j x hxP`.

Establish `h2 : (m j : ℝ) * height (HermLine.standard n) x ≤ m j * C₀` using `mul_le_mul_of_nonneg_left (hC₀ x hxS) (Nat.cast_nonneg _)`. Establish `h3 : |m j * C₀ + C j| ≤ ∑ j, |m j * C₀ + C j|` using `Finset.single_le_sum (f := fun j => |m j * C₀ + C j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)`. Establish `h4` using `le_abs_self (m j * C₀ + C j)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem CoverDenseAlt.exists_points_bounded_line_heights : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ), IsArithVar P d → ∀ (J : Type) [Fintype J] (A : J → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι), (∀ j, IsSmoothHerm (A j)) → ∃ C : ℝ, ∀ f : MRing ι, (∃ a, IsMultiHomog f a) → f ∉ P → ∃ (L : Type) (_ : Field L) (_ : NumberField L), ∃ w ∈ ptsOver L P, aeval w f ≠ 0 ∧ ∀ j, |lineHt (A j) L w| ≤ C := by
  intro K _ ι _ P d hP J _ A hA
  classical
  have hcard : ∀ k, Fintype.card (ι k) = (Fintype.card (ι k) - 1) + 1 := fun k => by
    obtain ⟨i, -⟩ := hP.2.1.2.2 k
    have : 0 < Fintype.card (ι k) := Fintype.card_pos_iff.mpr ⟨i⟩
    omega
  let n : K → ℕ := fun k => Fintype.card (ι k) - 1
  let e : ∀ k, ι k ≃ Fin (n k + 1) := fun k => Fintype.equivFinOfCardEq (hcard k)
  obtain ⟨S, C₀, hS, hdense, hC₀⟩ := DenseBoundedHeight.main K n (var e hP)
  choose m C hC using fun j => HeightComparison.main K n (var e hP) (line e (A j) (hA j))
  refine ⟨∑ j, |m j * C₀ + C j|, ?_⟩
  rintro f ⟨a, ha⟩ hf
  have hex : ∃ x ∈ S, evalCone x (φ e f) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hf ((mem_map_iff e P _).mp
      (hdense a (φ e f) ((geoMultiHomog_iff _ _).mp (homog_rename e ha)) hcon))
  obtain ⟨x, hxS, hx⟩ := hex
  have hxP := hS hxS
  have hval := aeval_back_eq_zero_iff e (algebraMap (coordField x) (AlgebraicClosure ℚ)) (coordVec x)
  refine ⟨coordField x, inferInstance, inferInstance, back e (coordVec x), ⟨fun k => ?_, fun g hg => ?_⟩, ?_,
    fun j => ?_⟩
  · obtain ⟨i, hi⟩ := back_nonzero e hxP.1 k
    exact ⟨i, fun h => hi (congrArg Subtype.val h)⟩
  · exact (hval g).mpr (hxP.2 _ (Ideal.mem_map_of_mem _ hg))
  · exact fun h => hx ((hval f).mp h)
  · rw [height_eq e (A j) (hA j)]
    have h1 := hC j x hxP
    have h2 : (m j : ℝ) * height (HermLine.standard n) x ≤ m j * C₀ :=
      mul_le_mul_of_nonneg_left (hC₀ x hxS) (Nat.cast_nonneg _)
    have h3 : |m j * C₀ + C j| ≤ ∑ j, |m j * C₀ + C j| :=
      Finset.single_le_sum (f := fun j => |m j * C₀ + C j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have h4 := le_abs_self (m j * C₀ + C j)
    linarith
