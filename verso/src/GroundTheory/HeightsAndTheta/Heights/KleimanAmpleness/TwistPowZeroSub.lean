import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.NotTwistFiniteAtZero
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisAltAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

open MvPolynomial

section

variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}

/- English proof (translation)
Unfold `IndefiniteRowSideFullHecke.Kleiman.secs`. Conclude with `iInf_congr fun i => iInf_congr fun hi => h i hi`.
-/
theorem secs_congr {F F' : Fin (N + 1) → Submodule S Ω} (h : ∀ i, x i ≠ 0 → F i = F' i) :
    IndefiniteRowSideFullHecke.Kleiman.secs S x F = IndefiniteRowSideFullHecke.Kleiman.secs S x F' := by
  unfold IndefiniteRowSideFullHecke.Kleiman.secs
  exact iInf_congr fun i => iInf_congr fun hi => h i hi

/- English proof (translation)
Rewrite using `[← mul_eq_twist]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.mul_le]`. Introduce `g hg a ha`. Rewrite `ha` using `[Submodule.restrictScalars_mem, pow_zero_sub]`.

Rewrite `hg`, the goal using `[Submodule.restrictScalars_mem]`. Rewrite using `[mul_comm]`. Conclude with `Submodule.smul_mem _ (⟨a, ha⟩ : Kleiman.chartRing S x I) hg`. Introduce `g hg`. Establish `h1 : (1 : Ω) ∈ ((B.pow 0).sub I).restrictScalars S`.

Rewrite using `[Submodule.restrictScalars_mem, pow_zero_sub]`. Conclude with `one_mem _`. Simplify using `using Submodule.mul_mem_mul hg h1`.
-/
theorem twist_pow_zero_sub (G B : Kleiman.SubSystem S x Ω) (I : Kleiman.Chart x) :
    ((G.twist (B.pow 0)).sub I).restrictScalars S = (G.sub I).restrictScalars S := by
  rw [← mul_eq_twist]
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro g hg a ha
    rw [Submodule.restrictScalars_mem, pow_zero_sub] at ha
    rw [Submodule.restrictScalars_mem] at hg ⊢
    rw [mul_comm]
    exact Submodule.smul_mem _ (⟨a, ha⟩ : Kleiman.chartRing S x I) hg
  · intro g hg
    have h1 : (1 : Ω) ∈ ((B.pow 0).sub I).restrictScalars S := by
      rw [Submodule.restrictScalars_mem, pow_zero_sub]
      exact one_mem _
    simpa using Submodule.mul_mem_mul hg h1

/- English proof (translation)
Rewrite using `[← secs.equiv]`. Apply `secs_congr` to reduce the goal to its premises. Introduce `i hi`. Establish `e1 : IndefiniteRowSideFullHecke.Kleiman.lmul S G' (IndefiniteRowSideFullHecke.Kleiman.lpow S B' b) i = IndefiniteRowSideFullHecke.Kleiman.lmul S (toIndefiniteRowSideFullHecke G) (IndefiniteRowSideFullHecke.Kleiman.lpow S (toIndefiniteRowSideFullHecke B) b) i`. Simplify using `only [IndefiniteRowSideFullHecke.Kleiman.lmul, IndefiniteRowSideFullHecke.Kleiman.lpow, hG i hi, hB i hi]`.

Rewrite using `[e1]`. Break down `Nat.eq_zero_or_pos b with rfl | hb` into its components or cases. Rewrite using `[IndefiniteRowSideFullHecke.Kleiman.lmul, lpow_zero, mul_one, chartModule_of_ne_zero _ hi, chartModule_of_ne_zero _ hi, twist_pow_zero_sub]`. Rewrite using `[IndefiniteRowSideFullHecke.Kleiman.lmul, lpow.equiv B hb hi]`. Conclude with `lmul.equiv G (B.pow b) hi`.
-/
theorem secs_lmul_lpow (G B : Kleiman.SubSystem S x Ω) (G' B' : Fin (N + 1) → Submodule S Ω)
    (hG : ∀ i, x i ≠ 0 → G' i = toIndefiniteRowSideFullHecke G i) (hB : ∀ i, x i ≠ 0 → B' i = toIndefiniteRowSideFullHecke B i) (b : ℕ) :
    IndefiniteRowSideFullHecke.Kleiman.secs S x (IndefiniteRowSideFullHecke.Kleiman.lmul S G' (IndefiniteRowSideFullHecke.Kleiman.lpow S B' b)) = (G.twist (B.pow b)).secs := by
  rw [← secs.equiv]
  apply secs_congr
  intro i hi
  have e1 : IndefiniteRowSideFullHecke.Kleiman.lmul S G' (IndefiniteRowSideFullHecke.Kleiman.lpow S B' b) i =
      IndefiniteRowSideFullHecke.Kleiman.lmul S (toIndefiniteRowSideFullHecke G) (IndefiniteRowSideFullHecke.Kleiman.lpow S (toIndefiniteRowSideFullHecke B) b) i := by
    simp only [IndefiniteRowSideFullHecke.Kleiman.lmul, IndefiniteRowSideFullHecke.Kleiman.lpow, hG i hi, hB i hi]
  rw [e1]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [IndefiniteRowSideFullHecke.Kleiman.lmul, lpow_zero, mul_one, chartModule_of_ne_zero _ hi, chartModule_of_ne_zero _ hi, twist_pow_zero_sub]
  · rw [IndefiniteRowSideFullHecke.Kleiman.lmul, lpow.equiv B hb hi]
    exact lmul.equiv G (B.pow b) hi

/- English proof (translation)
Establish `hsecs : IndefiniteRowSideFullHecke.Kleiman.secs S x B' = B.secs`. Rewrite using `[← secs.equiv]`. Conclude with `secs_congr hB`. Establish `key : ∀ {i : Fin (N + 1)} (h : x i ≠ 0), Submodule.span S (Set.image2 (· • ·) (ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i : Set Ω) (Set.range η)) = (Submodule.span (Kleiman.chartRing S x (Kleiman.singleChart h)) (Set.range η)).restrictScalars S`. Introduce `i h`.

Rewrite using `[chartRing.equiv S x h]`. Conclude with `span_image2_eq _ _`. Unfold `IndefiniteRowSideFullHecke.Kleiman.IsGeneratedBy`. Rewrite using `[hsecs]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hη, hg⟩`. Use `⟨hη, fun I => ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `I.2.1`. Establish `hxi : x i ≠ 0` using `(Kleiman.mem_support x).mp (I.2.2 hi)`. Establish `hsub : {i} ⊆ I.1` using `Finset.singleton_subset_iff.mpr hi`.

Establish `hi' : B.sub (Kleiman.singleChart hxi) = Submodule.span (Kleiman.chartRing S x (Kleiman.singleChart hxi)) (Set.range η)`. Use `hg i hxi` as an intermediate fact. Rewrite `this` using `[key hxi, hB i hxi, chartModule_of_ne_zero _ hxi]`. Conclude with `Submodule.restrictScalars_injective S _ _ this`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Use `hη j` as an intermediate fact. Rewrite `this` using `[Kleiman.SubSystem.secs, Submodule.mem_iInf]`. Conclude with `this I`.

Introduce `y hy`. Take `⟨a, ⟨u, hu⟩, hay⟩` from `(B.mem_iff (Kleiman.singleChart hxi) I hsub y).mp hy`. Rewrite `hay` using `[hi']`. Establish `hmono : ∀ w ∈ Submodule.span (Kleiman.chartRing S x (Kleiman.singleChart hxi)) (Set.range η), w ∈ Submodule.span (Kleiman.chartRing S x I) (Set.range η)`. Introduce `w hw`.

Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem z hz => exact Submodule.subset_span hz`. Consider the case `zero => exact zero_mem _`. Consider the case `add p q _ _ hp hq => exact add_mem hp hq`. Consider the case `smul c w _ hw`.

Establish `: c • w = (Kleiman.chartIncl hsub c) • w` using `rfl`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hw`. Establish `hay'` using `hmono _ hay`. Establish `hinv : ((↑u⁻¹ : Kleiman.chartRing S x I) : Ω) * (a : Ω) = 1`.

Use `congrArg Subtype.val (Units.inv_mul u)` as an intermediate fact. Rewrite `this` using `[hu]`. Conclude with `this`. Establish `hy' : y = (↑u⁻¹ : Kleiman.chartRing S x I) • ((a : Ω) • y)`. Rewrite using `[Subalgebra.smul_def, ← mul_smul, hinv, one_smul]`.

Rewrite using `[hy']`. Conclude with `Submodule.smul_mem _ _ hay'`. Introduce and unpack `⟨hη, hg⟩`. Use `⟨hη, fun i hxi => ?_⟩` and prove the remaining obligations. Rewrite using `[key hxi, hB i hxi, chartModule_of_ne_zero _ hxi, hg]`.
-/
theorem isGeneratedBy_iff (B : Kleiman.SubFamily S x Ω) (B' : Fin (N + 1) → Submodule S Ω)
    (hB : ∀ i, x i ≠ 0 → B' i = toIndefiniteRowSideFullHecke B.toSubSystem i) {r : ℕ} (η : Fin (r + 1) → Ω) :
    IndefiniteRowSideFullHecke.Kleiman.IsGeneratedBy S x B' η ↔
      (∀ j, η j ∈ B.secs) ∧ ∀ I, Submodule.span (Kleiman.chartRing S x I) (Set.range η) = B.sub I := by
  have hsecs : IndefiniteRowSideFullHecke.Kleiman.secs S x B' = B.secs := by
    rw [← secs.equiv]
    exact secs_congr hB
  have key : ∀ {i : Fin (N + 1)} (h : x i ≠ 0),
      Submodule.span S (Set.image2 (· • ·) (ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i : Set Ω) (Set.range η)) =
      (Submodule.span (Kleiman.chartRing S x (Kleiman.singleChart h)) (Set.range η)).restrictScalars S := by
    intro i h
    rw [chartRing.equiv S x h]
    exact span_image2_eq _ _
  unfold IndefiniteRowSideFullHecke.Kleiman.IsGeneratedBy
  rw [hsecs]
  constructor
  · rintro ⟨hη, hg⟩
    refine ⟨hη, fun I => ?_⟩
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (Kleiman.mem_support x).mp (I.2.2 hi)
    have hsub : {i} ⊆ I.1 := Finset.singleton_subset_iff.mpr hi
    have hi' : B.sub (Kleiman.singleChart hxi) =
        Submodule.span (Kleiman.chartRing S x (Kleiman.singleChart hxi)) (Set.range η) := by
      have := hg i hxi
      rw [key hxi, hB i hxi, chartModule_of_ne_zero _ hxi] at this
      exact Submodule.restrictScalars_injective S _ _ this
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have := hη j
      rw [Kleiman.SubSystem.secs, Submodule.mem_iInf] at this
      exact this I
    · intro y hy
      obtain ⟨a, ⟨u, hu⟩, hay⟩ := (B.mem_iff (Kleiman.singleChart hxi) I hsub y).mp hy
      rw [hi'] at hay
      have hmono : ∀ w ∈ Submodule.span (Kleiman.chartRing S x (Kleiman.singleChart hxi)) (Set.range η),
          w ∈ Submodule.span (Kleiman.chartRing S x I) (Set.range η) := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem z hz => exact Submodule.subset_span hz
        | zero => exact zero_mem _
        | add p q _ _ hp hq => exact add_mem hp hq
        | smul c w _ hw =>
          have : c • w = (Kleiman.chartIncl hsub c) • w := rfl
          rw [this]
          exact Submodule.smul_mem _ _ hw
      have hay' := hmono _ hay
      have hinv : ((↑u⁻¹ : Kleiman.chartRing S x I) : Ω) * (a : Ω) = 1 := by
        have := congrArg Subtype.val (Units.inv_mul u)
        rw [hu] at this
        exact this
      have hy' : y = (↑u⁻¹ : Kleiman.chartRing S x I) • ((a : Ω) • y) := by
        rw [Subalgebra.smul_def, ← mul_smul, hinv, one_smul]
      rw [hy']
      exact Submodule.smul_mem _ _ hay'
  · rintro ⟨hη, hg⟩
    refine ⟨hη, fun i hxi => ?_⟩
    rw [key hxi, hB i hxi, chartModule_of_ne_zero _ hxi, hg]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[iSup_le_iff]`. Introduce `k`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, ha, _, rfl, rfl⟩`.

Rewrite `ha` using `[SetLike.mem_coe]`. Unfold `IndefiniteRowSideFullHecke.Kleiman.secZ at ha`. Use `split_ifs at ha with hd`. Take `⟨f, hf, rfl⟩` from `Submodule.mem_map.mp ha`. Conclude with `Submodule.subset_span ⟨k, f, ((b : ℤ) - bk k).toNat, (mem_homogeneousSubmodule _ _).mp hf, by omega, rfl⟩`.

Rewrite `ha` using `[Submodule.mem_bot]`. Simplify using `[ha]`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, f, e, hf, he, rfl⟩`. Use `Submodule.mem_iSup_of_mem k (Submodule.subset_span ⟨aeval η f, ?_, s k, rfl, rfl⟩)` and prove the remaining obligations.

Establish `hd : ((b : ℤ) - bk k) = (e : ℤ)` using `by omega`. Rewrite using `[hd, SetLike.mem_coe]`. Unfold `IndefiniteRowSideFullHecke.Kleiman.secZ`. Rewrite using `[if_pos (by positivity), Int.toNat_natCast]`. Conclude with `Submodule.mem_map.mpr ⟨f, (mem_homogeneousSubmodule _ _).mpr hf, rfl⟩`.
-/
theorem iSup_span_secZ_eq {r n : ℕ} (η : Fin (r + 1) → Ω) (bk : Fin n → ℕ) (s : Fin n → Ω) (b : ℕ) :
    (⨆ k, Submodule.span S (Set.image2 (· * ·) (IndefiniteRowSideFullHecke.Kleiman.secZ S η ((b : ℤ) - bk k) : Set Ω) {s k})) =
      Submodule.span S {z | ∃ (k : Fin n) (f : MvPolynomial (Fin (r + 1)) S) (e : ℕ), f.IsHomogeneous e ∧
        e + bk k = b ∧ z = aeval η f * s k} := by
  apply le_antisymm
  · rw [iSup_le_iff]
    intro k
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, _, rfl, rfl⟩
    rw [SetLike.mem_coe] at ha
    unfold IndefiniteRowSideFullHecke.Kleiman.secZ at ha
    split_ifs at ha with hd
    · obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp ha
      exact Submodule.subset_span
        ⟨k, f, ((b : ℤ) - bk k).toNat, (mem_homogeneousSubmodule _ _).mp hf, by omega, rfl⟩
    · rw [Submodule.mem_bot] at ha
      simp [ha]
  · rw [Submodule.span_le]
    rintro _ ⟨k, f, e, hf, he, rfl⟩
    refine Submodule.mem_iSup_of_mem k (Submodule.subset_span ⟨aeval η f, ?_, s k, rfl, rfl⟩)
    have hd : ((b : ℤ) - bk k) = (e : ℤ) := by omega
    rw [hd, SetLike.mem_coe]
    unfold IndefiniteRowSideFullHecke.Kleiman.secZ
    rw [if_pos (by positivity), Int.toNat_natCast]
    exact Submodule.mem_map.mpr ⟨f, (mem_homogeneousSubmodule _ _).mpr hf, rfl⟩

/- English proof (translation)
Establish `hmon : ∀ (d : Fin (r + 1) →₀ ℕ) (t : Finset (Fin (r + 1))), ∏ j ∈ t, η j ^ d j ∈ Q ^ (∑ j ∈ t, d j)`. Introduce `d t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.prod_empty, Finset.sum_empty, pow_zero]`.

Conclude with `Submodule.mem_one.mpr ⟨1, map_one _⟩`. Consider the case `insert j t hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.sum_insert hj, pow_add]`. Conclude with `Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (hη j) _) ih`. Rewrite using `[f.as_sum, map_sum]`.

Use `Submodule.sum_mem _ fun d hd => ?_` and prove the remaining obligations. Rewrite using `[aeval_monomial, ← Algebra.smul_def]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `hdeg : Finsupp.degree d = e`. Rewrite using `[Finsupp.degree_eq_weight_one]`.

Conclude with `hf (mem_support_iff.mp hd)`. Use `hmon d d.support` as an intermediate fact. Rewrite `this` using `[show (∑ j ∈ d.support, d j) = e from hdeg]`. Conclude with `this`.
-/
theorem aeval_mem_pow {r : ℕ} {Q : Submodule S Ω} {η : Fin (r + 1) → Ω} (hη : ∀ j, η j ∈ Q)
    {f : MvPolynomial (Fin (r + 1)) S} {e : ℕ} (hf : f.IsHomogeneous e) : aeval η f ∈ Q ^ e := by
  have hmon : ∀ (d : Fin (r + 1) →₀ ℕ) (t : Finset (Fin (r + 1))),
      ∏ j ∈ t, η j ^ d j ∈ Q ^ (∑ j ∈ t, d j) := by
    intro d t
    induction t using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty, pow_zero]
      exact Submodule.mem_one.mpr ⟨1, map_one _⟩
    | insert j t hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, pow_add]
      exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (hη j) _) ih
  rw [f.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [aeval_monomial, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have hdeg : Finsupp.degree d = e := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (mem_support_iff.mp hd)
  have := hmon d d.support
  rw [show (∑ j ∈ d.support, d j) = e from hdeg] at this
  exact this

end

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hA S _ _ N Ω _ _ x G' B' r η hx hgen`. Take `⟨G, hG⟩` from `(hL S N Ω x).2 G'`. Take `⟨B, hB⟩` from `(hL S N Ω x).2 B'`. Establish `hgen'` using `(isGeneratedBy_iff B.toSubFamily B'.mods hB η).mp hgen`.

Take `⟨n, deg, gen, hgen1, hle⟩` from `hA S Ω N x G B r η hx hgen'.1 hgen'.2`. Establish `hsecs` using `secs_lmul_lpow G.toSubSystem B.toSubSystem G'.mods B'.mods hG hB`. Use `⟨n, deg, gen, fun k => ?_, fun b => ?_⟩` and prove the remaining obligations. Rewrite using `[hsecs]`. Conclude with `hgen1 k`.

Rewrite using `[iSup_span_secZ_eq]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[hsecs]`. Conclude with `hle b`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨k, f, e, hf, he, rfl⟩`. Establish `hk` using `hgen1 k`. Rewrite `hk` using `[← hsecs]`. Simplify using `only [IndefiniteRowSideFullHecke.Kleiman.secs, SetLike.mem_coe, Submodule.mem_iInf] at hk ⊢`. Introduce `i hi`.

Establish `hη : ∀ j, η j ∈ B'.mods i`. Introduce `j`. Use `hgen.1 j` as an intermediate fact. Simplify using `only [IndefiniteRowSideFullHecke.Kleiman.secs, Submodule.mem_iInf] at this`. Conclude with `this i hi`.

Establish `ha` using `aeval_mem_pow hη hf`. Establish `hki` using `hk i hi`. Use `show aeval η f * gen k ∈ G'.mods i * B'.mods i ^ b`. Express the relevant statement in the definitionally equal form `gen k ∈ G'.mods i * B'.mods i ^ deg k at hki`. Establish `hmul : B'.mods i ^ e * (G'.mods i * B'.mods i ^ deg k) = G'.mods i * B'.mods i ^ (e + deg k)`.

Rewrite using `[pow_add, mul_left_comm]`. Rewrite using `[← he, ← hmul]`. Conclude with `Submodule.mul_mem_mul ha hki`. Introduce `hB' S _ _ Ω _ _ N x G B r η hx hη hspan`. Take `⟨G', hG⟩` from `(hL S N Ω x).1 G`.

Take `⟨B', hB⟩` from `(hL S N Ω x).1 B`. Establish `hgen : IndefiniteRowSideFullHecke.Kleiman.IsGeneratedBy S x B'.mods η` using `(isGeneratedBy_iff B.toSubFamily B'.mods (fun i _ => hB i) η).mpr ⟨hη, hspan⟩`. Take `⟨n, bk, s, hs, heq⟩` from `hB' S N Ω x G' B' r η hx hgen`. Establish `hsecs` using `secs_lmul_lpow G.toSubSystem B.toSubSystem G'.mods B'.mods (fun i _ => hG i) (fun i _ => hB i)`. Use `⟨n, bk, s, fun k => ?_, fun b => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hsecs]`. Conclude with `hs k`. Rewrite using `[← hsecs, heq b, iSup_span_secZ_eq]`.
-/
theorem TwistFinite.equiv_ne (hL : TranslateEq.LineBundle.Statement) :
    Kleiman.TwistFinite.Statement.{0, 0} ↔ TwistFiniteNe.Statement := by
  constructor
  · intro hA S _ _ N Ω _ _ x G' B' r η hx hgen
    obtain ⟨G, hG⟩ := (hL S N Ω x).2 G'
    obtain ⟨B, hB⟩ := (hL S N Ω x).2 B'
    have hgen' := (isGeneratedBy_iff B.toSubFamily B'.mods hB η).mp hgen
    obtain ⟨n, deg, gen, hgen1, hle⟩ := hA S Ω N x G B r η hx hgen'.1 hgen'.2
    have hsecs := secs_lmul_lpow G.toSubSystem B.toSubSystem G'.mods B'.mods hG hB
    refine ⟨n, deg, gen, fun k => ?_, fun b => ?_⟩
    · rw [hsecs]
      exact hgen1 k
    · rw [iSup_span_secZ_eq]
      apply le_antisymm
      · rw [hsecs]
        exact hle b
      · rw [Submodule.span_le]
        rintro _ ⟨k, f, e, hf, he, rfl⟩
        have hk := hgen1 k
        rw [← hsecs] at hk
        simp only [IndefiniteRowSideFullHecke.Kleiman.secs, SetLike.mem_coe, Submodule.mem_iInf] at hk ⊢
        intro i hi
        have hη : ∀ j, η j ∈ B'.mods i := by
          intro j
          have := hgen.1 j
          simp only [IndefiniteRowSideFullHecke.Kleiman.secs, Submodule.mem_iInf] at this
          exact this i hi
        have ha := aeval_mem_pow hη hf
        have hki := hk i hi
        show aeval η f * gen k ∈ G'.mods i * B'.mods i ^ b
        change gen k ∈ G'.mods i * B'.mods i ^ deg k at hki
        have hmul : B'.mods i ^ e * (G'.mods i * B'.mods i ^ deg k) = G'.mods i * B'.mods i ^ (e + deg k) := by
          rw [pow_add, mul_left_comm]
        rw [← he, ← hmul]
        exact Submodule.mul_mem_mul ha hki
  · intro hB' S _ _ Ω _ _ N x G B r η hx hη hspan
    obtain ⟨G', hG⟩ := (hL S N Ω x).1 G
    obtain ⟨B', hB⟩ := (hL S N Ω x).1 B
    have hgen : IndefiniteRowSideFullHecke.Kleiman.IsGeneratedBy S x B'.mods η :=
      (isGeneratedBy_iff B.toSubFamily B'.mods (fun i _ => hB i) η).mpr ⟨hη, hspan⟩
    obtain ⟨n, bk, s, hs, heq⟩ := hB' S N Ω x G' B' r η hx hgen
    have hsecs := secs_lmul_lpow G.toSubSystem B.toSubSystem G'.mods B'.mods
      (fun i _ => hG i) (fun i _ => hB i)
    refine ⟨n, bk, s, fun k => ?_, fun b => ?_⟩
    · rw [← hsecs]
      exact hs k
    · rw [← hsecs, heq b, iSup_span_secZ_eq]

end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
