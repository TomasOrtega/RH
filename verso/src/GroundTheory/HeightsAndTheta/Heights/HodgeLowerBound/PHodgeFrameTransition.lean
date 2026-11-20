import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFibreSteps
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

namespace HodgeFrameTransition

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [Fintype K] in

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[support_X, Finset.mem_singleton]`. Substitute `hm` using the available equality. Take `⟨a, i₀⟩` from `p`. Use `show ∑ i, (Finsupp.single (⟨a, i₀⟩ : Σ k, ι k) 1 : (Σ k, ι k) →₀ ℕ) ⟨k, i⟩ = if k = a then 1 else 0`.

Distinguish the cases in `hk : k = a`. Substitute `hk` using the available equality. Rewrite using `[if_pos rfl, Finset.sum_eq_single i₀]`. Simplify using the standard rewrite rules. Introduce `i _ hi classical`.

Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce `h`. Conclude with `hi (eq_of_heq (Sigma.mk.inj_iff.mp h).2).symm`. Simplify using the standard rewrite rules. Rewrite using `[if_neg hk]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce `h`. Conclude with `hk (congrArg Sigma.fst h).symm`.
-/
theorem isMultiHomog_X_single [DecidableEq K] (p : Σ k, ι k) :
    IsMultiHomog (X p : MRing ι) (fun k => if k = p.1 then 1 else 0) := by
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  obtain ⟨a, i₀⟩ := p
  show ∑ i, (Finsupp.single (⟨a, i₀⟩ : Σ k, ι k) 1 : (Σ k, ι k) →₀ ℕ) ⟨k, i⟩ = if k = a then 1 else 0
  by_cases hk : k = a
  · subst hk
    rw [if_pos rfl, Finset.sum_eq_single i₀]
    · simp
    · intro i _ hi
      classical
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hi (eq_of_heq (Sigma.mk.inj_iff.mp h).2).symm
    · simp
  · rw [if_neg hk]
    refine Finset.sum_eq_zero fun i _ => ?_
    classical
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hk (congrArg Sigma.fst h).symm

/- English proof (translation)
Establish `key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι)) (fun k => if k ∈ s then 1 else 0)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.prod_empty, Finset.notMem_empty, if_false]`.

Conclude with `isMultiHomog_one`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha]`. Use `isMultiHomog_mul (isMultiHomog_X_single (ι := ι) ⟨a, c a⟩) ih using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`.

Distinguish the cases in `hk : k = a`. Substitute `hk` using the available equality. Simplify using `[ha]`. Simplify using `[hk]`. Simplify using `using key Finset.univ`.
-/
theorem isMultiHomog_prod_X (c : (k : K) → ι k) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι)) (fun _ => 1) := by
  classical
  have key : ∀ s : Finset K,
      IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι)) (fun k => if k ∈ s then 1 else 0) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Finset.notMem_empty, if_false]
      exact isMultiHomog_one
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      convert isMultiHomog_mul (isMultiHomog_X_single (ι := ι) ⟨a, c a⟩) ih using 1
      funext k
      by_cases hk : k = a
      · subst hk; simp [ha]
      · simp [hk]
  simpa using key Finset.univ

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, C n, 1, isMultiHomog_C_zero n, isMultiHomog_one, by simp, by simp, by simp, by simp⟩`.
-/
theorem isValueAt_intCast (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (n : ℤ) :
    IsValueAt y (n : Ω) z (n : ℂ) :=
  ⟨0, C n, 1, isMultiHomog_C_zero n, isMultiHomog_one, by simp, by simp, by simp, by simp⟩

/- English proof (translation)
Proceed by induction on `hr using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨c', rfl⟩` from `hx`. Use `⟨(∏ k, z ⟨k, c' k⟩) / ∏ k, z ⟨k, c k⟩, fun _ => 1, ∏ k, X ⟨k, c' k⟩, ∏ k, X ⟨k, c k⟩, isMultiHomog_prod_X c', isMultiHomog_prod_X c, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify `hyc` using `[segreCoord]`.

Simplify using `only [map_prod, aeval_X]`. Conclude with `(div_mul_cancel₀ _ hyc).symm`. Simplify using `only [map_prod, map_X, eval_X]`. Conclude with `Finset.prod_ne_zero_iff.2 fun k _ => hz k`. Simplify using `[map_prod]`.

Consider the case `algebraMap n => exact ⟨n, by simpa using isValueAt_intCast y z n⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨v, hv⟩` from `ha`. Take `⟨w, hw⟩` from `hb`. Conclude with `⟨v + w, LineFlag.isValueAt_add hv hw⟩`.

Consider the case `mul a b _ _ ha hb`. Take `⟨v, hv⟩` from `ha`. Take `⟨w, hw⟩` from `hb`. Conclude with `⟨v * w, LineFlag.isValueAt_mul hv hw⟩`.
-/
theorem exists_value_of_mem_chartRing {y : (Σ k, ι k) → Ω} {c : (k : K) → ι k}
    {z : (Σ k, ι k) → ℂ} (hyc : segreCoord y c ≠ 0) (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) {r : Ω}
    (hr : r ∈ chartRing ℤ (segreCoord y) c) : ∃ v, IsValueAt y r z v := by
  classical
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨c', rfl⟩ := hx
    refine ⟨(∏ k, z ⟨k, c' k⟩) / ∏ k, z ⟨k, c k⟩, fun _ => 1, ∏ k, X ⟨k, c' k⟩, ∏ k, X ⟨k, c k⟩,
      isMultiHomog_prod_X c', isMultiHomog_prod_X c, ?_, ?_, ?_, ?_⟩
    · simpa [segreCoord] using hyc
    · simp only [map_prod, aeval_X]
      exact (div_mul_cancel₀ _ hyc).symm
    · simp only [map_prod, map_X, eval_X]
      exact Finset.prod_ne_zero_iff.2 fun k _ => hz k
    · simp [map_prod]
  | algebraMap n => exact ⟨n, by simpa using isValueAt_intCast y z n⟩
  | add a b _ _ ha hb =>
    obtain ⟨v, hv⟩ := ha
    obtain ⟨w, hw⟩ := hb
    exact ⟨v + w, LineFlag.isValueAt_add hv hw⟩
  | mul a b _ _ ha hb =>
    obtain ⟨v, hv⟩ := ha
    obtain ⟨w, hw⟩ := hb
    exact ⟨v * w, LineFlag.isValueAt_mul hv hw⟩

/- English proof (translation)
Take `⟨w, hw⟩` from `exists_value_of_mem_chartRing hyc hz ha`. Take `⟨u, hu, hu0⟩` from `hg`. Establish `hg0 : g ≠ 0`. Introduce and unpack `rfl`. Conclude with `hu0 (isValueAt_zero hzP hu)`.

Use `⟨u⁻¹ ^ n * w, ?_⟩` and prove the remaining obligations. Use `LineFlag.isValueAt_mul (LineFlag.isValueAt_pow (LineFlag.isValueAt_inv hzP hu hu0) n) hw` as an intermediate fact. Rewrite `this` using `[← mul_assoc, ← mul_pow, inv_mul_cancel₀ hg0, one_pow, one_mul]`. Then use the resulting hypothesis.
-/
theorem exists_value_of_pow_mul_mem {y : (Σ k, ι k) → Ω} {c : (k : K) → ι k} {z : (Σ k, ι k) → ℂ}
    (hzP : z ∈ mcPts (mCoordIdeal y)) (hyc : segreCoord y c ≠ 0) (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) {g a : Ω}
    (hg : IsUnitAt y g z) {n : ℕ} (ha : g ^ n * a ∈ chartRing ℤ (segreCoord y) c) :
    ∃ v, IsValueAt y a z v := by
  obtain ⟨w, hw⟩ := exists_value_of_mem_chartRing hyc hz ha
  obtain ⟨u, hu, hu0⟩ := hg
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hu0 (isValueAt_zero hzP hu)
  refine ⟨u⁻¹ ^ n * w, ?_⟩
  have := LineFlag.isValueAt_mul (LineFlag.isValueAt_pow (LineFlag.isValueAt_inv hzP hu hu0) n) hw
  rwa [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hg0, one_pow, one_mul] at this

end HodgeFrameTransition

open HodgeFrameTransition in

/- English proof (translation)
Introduce `II Ψ _ K _ ι _ Ω _ _ E _ _ D τ c f bfr z hz hfr hdom`. Take `⟨hyc, -, -, hli, hiff⟩` from `hfr`. Take `⟨hzc, hfu⟩` from `hdom`. Take `⟨m, fl, al, hfl, hal, hsum, hframe⟩` from `D.hodge τ c hyc`. Use `choose vf hvf using fun l => exists_value_of_mem_chartRing hyc hzc (hfl l)`.

Use `choose va hva using fun l => exists_value_of_mem_chartRing hyc hzc (hal l)`. Establish `h1 : ∑ l, va l * vf l = 1`. Use `LineFlag.isValueAt_sum _ _ fun l => LineFlag.isValueAt_mul (hva l) (hvf l)` as an intermediate fact. Rewrite `this` using `[hsum]`. Conclude with `isValueAt_one hz this`.

Choose the witnesses or unpack the hypotheses as in `⟨l, hl⟩ : ∃ l, vf l ≠ 0 := by`. Assume the negation of the conclusion as `h`. Simplify using `only [not_exists, not_not] at h`. Simplify using `[h] at h1`. Establish `hfl0 : fl l ≠ 0`.

Introduce `h0`. Use `hvf l` as an intermediate fact. Rewrite `this` using `[h0]`. Conclude with `hl (isValueAt_zero hz this)`. Take `⟨b', ⟨-, -, -, hli', hiff'⟩, hspan⟩` from `hframe l hfl0`.

Establish `hflu : IsUnitAt D.y (fl l) z` using `⟨vf l, hvf l, hl⟩`. Take `⟨uf, huf, huf0⟩` from `hfu`. Establish `hsec : ∀ {g : Ω} (b : Fin D.N → E τ), (∀ e, (∃ n : ℕ, g ^ n • e ∈ (D.W τ).lat c) ↔ ∃ a : Fin D.N → Ω, (∀ q, ∃ n : ℕ, g ^ n * a q ∈ chartRing ℤ (segreCoord D.y) c) ∧ e = ∑ q, a q • b q) → ∀ i, ∃ n : ℕ, g ^ n • b i ∈ (D.W τ).lat c`. Introduce `g b h i`. Use `(h (b i)).2 ⟨Pi.single i 1, fun q => ⟨0, ?_⟩, ?_⟩` and prove the remaining obligations.

Break down `eq_or_ne q i with rfl | hq` into its components or cases. Simplify using the standard rewrite rules. Simplify using `[hq]`. Simplify using `[Pi.single_apply, ite_smul]`. Use `choose n hn using hsec b' hiff'`.

Use `choose a ha hrep using fun i => (hiff (fl l ^ n i • b' i)).1 ⟨0, by simpa using hn i⟩`. Use `choose n' hn' using hsec bfr hiff`. Use `choose a' ha' hrep' using fun q => (hiff' (f ^ n' q • bfr q)).1 ⟨0, by simpa using hn' q⟩`. Establish `hf0 : f ≠ 0`. Introduce and unpack `rfl`.

Conclude with `huf0 (isValueAt_zero hz huf)`. Use `set R : Matrix (Fin D.N) (Fin D.N) Ω := fun q i => (fl l ^ n i)⁻¹ * a i q with hRdef`. Use `set R' : Matrix (Fin D.N) (Fin D.N) Ω := fun i q => (f ^ n' q)⁻¹ * a' q i with hR'def`. Establish `hR : ∀ i, b' i = ∑ q, R q i • bfr q`. Introduce `i`.

Establish `e` using `congrArg ((fl l ^ n i)⁻¹ • ·) (hrep i)`. Simplify using `only [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hfl0), one_smul, Finset.smul_sum] at e`. Conclude with `e`. Establish `hR' : ∀ q, bfr q = ∑ i, R' i q • b' i`. Introduce `q`.

Establish `e` using `congrArg ((f ^ n' q)⁻¹ • ·) (hrep' q)`. Simplify using `only [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hf0), one_smul, Finset.smul_sum] at e`. Conclude with `e`. Establish `hvR : ∀ p q, ∃ v, IsValueAt D.y (R p q) z v`. Introduce `q i`.

Take `⟨w, hw⟩` from `exists_value_of_pow_mul_mem hz hyc hzc ⟨uf, huf, huf0⟩ (ha i q).choose_spec`. Conclude with `⟨_, LineFlag.isValueAt_mul (LineFlag.isValueAt_inv hz (LineFlag.isValueAt_pow (hvf l) (n i)) (pow_ne_zero _ hl)) hw⟩`. Establish `hvR' : ∀ p q, ∃ v, IsValueAt D.y (R' p q) z v`. Introduce `i q`. Take `⟨w, hw⟩` from `exists_value_of_pow_mul_mem hz hyc hzc hflu (ha' q i).choose_spec`.

Conclude with `⟨_, LineFlag.isValueAt_mul (LineFlag.isValueAt_inv hz (LineFlag.isValueAt_pow huf (n' q)) (pow_ne_zero _ huf0)) hw⟩`. Take `⟨Rz, hRz⟩ : ∃ Rz : Matrix (Fin D.N) (Fin D.N) ℂ, ∀ p q, IsValueAt D.y (R p q) z (Rz p q)` from `⟨fun p q => (hvR p q).choose, fun p q => (hvR p q).choose_spec⟩`. Take `⟨R'z, hR'z⟩ : ∃ R'z : Matrix (Fin D.N) (Fin D.N) ℂ, ∀ p q, IsValueAt D.y (R' p q) z (R'z p q)` from `⟨fun p q => (hvR' p q).choose, fun p q => (hvR' p q).choose_spec⟩`. Establish `hRR' : R * R' = 1`. Use extensionality with `p q`.

Establish `hcomb : ∑ p, ((R * R') p q - (1 : Matrix (Fin D.N) (Fin D.N) Ω) p q) • bfr p = 0`. Simplify using `only [sub_smul, Finset.sum_sub_distrib, Matrix.mul_apply, Finset.sum_smul]`. Establish `e1 : ∑ p, ∑ i, (R p i * R' i q) • bfr p = bfr q`. Rewrite using `[Finset.sum_comm, hR' q]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hR i, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, mul_comm]`. Simplify using `[e1, Matrix.one_apply, ite_smul]`. Use `Fintype.linearIndependent_iff.1 hli _ hcomb p` as an intermediate fact.

Conclude with `sub_eq_zero.1 this`. Use `⟨b', R, R', Rz, R'z, hli', hspan, hR, hR', hRz, hR'z, ?_⟩` and prove the remaining obligations. Use extensionality with `p r`. Establish `hv` using `LineFlag.isValueAt_sum _ _ fun q => LineFlag.isValueAt_mul (hRz p q) (hR'z q r)`. Establish `e : ∑ q, R p q * R' q r = (1 : Matrix (Fin D.N) (Fin D.N) Ω) p r`.

Rewrite using `[← Matrix.mul_apply, hRR']`. Rewrite `hv` using `[e, Matrix.one_apply]`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Use `split_ifs at hv ⊢`. Conclude with `isValueAt_one hz hv`.

Conclude with `isValueAt_zero hz hv`.
-/
theorem HodgeFrameTransition.proof : HodgeFrameTransition.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D τ c f bfr z hz hfr hdom
  classical
  obtain ⟨hyc, -, -, hli, hiff⟩ := hfr
  obtain ⟨hzc, hfu⟩ := hdom
  obtain ⟨m, fl, al, hfl, hal, hsum, hframe⟩ := D.hodge τ c hyc
  choose vf hvf using fun l => exists_value_of_mem_chartRing hyc hzc (hfl l)
  choose va hva using fun l => exists_value_of_mem_chartRing hyc hzc (hal l)
  have h1 : ∑ l, va l * vf l = 1 := by
    have := LineFlag.isValueAt_sum _ _ fun l => LineFlag.isValueAt_mul (hva l) (hvf l)
    rw [hsum] at this
    exact isValueAt_one hz this
  obtain ⟨l, hl⟩ : ∃ l, vf l ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    simp [h] at h1
  have hfl0 : fl l ≠ 0 := by
    intro h0
    have := hvf l
    rw [h0] at this
    exact hl (isValueAt_zero hz this)
  obtain ⟨b', ⟨-, -, -, hli', hiff'⟩, hspan⟩ := hframe l hfl0
  have hflu : IsUnitAt D.y (fl l) z := ⟨vf l, hvf l, hl⟩
  obtain ⟨uf, huf, huf0⟩ := hfu

  have hsec : ∀ {g : Ω} (b : Fin D.N → E τ),
      (∀ e, (∃ n : ℕ, g ^ n • e ∈ (D.W τ).lat c) ↔ ∃ a : Fin D.N → Ω,
        (∀ q, ∃ n : ℕ, g ^ n * a q ∈ chartRing ℤ (segreCoord D.y) c) ∧ e = ∑ q, a q • b q) →
      ∀ i, ∃ n : ℕ, g ^ n • b i ∈ (D.W τ).lat c := by
    intro g b h i
    refine (h (b i)).2 ⟨Pi.single i 1, fun q => ⟨0, ?_⟩, ?_⟩
    · rcases eq_or_ne q i with rfl | hq
      · simp
      · simp [hq]
    · simp [Pi.single_apply, ite_smul]
  choose n hn using hsec b' hiff'
  choose a ha hrep using fun i => (hiff (fl l ^ n i • b' i)).1 ⟨0, by simpa using hn i⟩
  choose n' hn' using hsec bfr hiff
  choose a' ha' hrep' using fun q => (hiff' (f ^ n' q • bfr q)).1 ⟨0, by simpa using hn' q⟩
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact huf0 (isValueAt_zero hz huf)
  set R : Matrix (Fin D.N) (Fin D.N) Ω := fun q i => (fl l ^ n i)⁻¹ * a i q with hRdef
  set R' : Matrix (Fin D.N) (Fin D.N) Ω := fun i q => (f ^ n' q)⁻¹ * a' q i with hR'def
  have hR : ∀ i, b' i = ∑ q, R q i • bfr q := by
    intro i
    have e := congrArg ((fl l ^ n i)⁻¹ • ·) (hrep i)
    simp only [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hfl0), one_smul, Finset.smul_sum] at e
    exact e
  have hR' : ∀ q, bfr q = ∑ i, R' i q • b' i := by
    intro q
    have e := congrArg ((f ^ n' q)⁻¹ • ·) (hrep' q)
    simp only [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hf0), one_smul, Finset.smul_sum] at e
    exact e
  have hvR : ∀ p q, ∃ v, IsValueAt D.y (R p q) z v := by
    intro q i
    obtain ⟨w, hw⟩ := exists_value_of_pow_mul_mem hz hyc hzc ⟨uf, huf, huf0⟩ (ha i q).choose_spec
    exact ⟨_, LineFlag.isValueAt_mul (LineFlag.isValueAt_inv hz (LineFlag.isValueAt_pow (hvf l) (n i))
      (pow_ne_zero _ hl)) hw⟩
  have hvR' : ∀ p q, ∃ v, IsValueAt D.y (R' p q) z v := by
    intro i q
    obtain ⟨w, hw⟩ := exists_value_of_pow_mul_mem hz hyc hzc hflu (ha' q i).choose_spec
    exact ⟨_, LineFlag.isValueAt_mul (LineFlag.isValueAt_inv hz (LineFlag.isValueAt_pow huf (n' q))
      (pow_ne_zero _ huf0)) hw⟩
  obtain ⟨Rz, hRz⟩ : ∃ Rz : Matrix (Fin D.N) (Fin D.N) ℂ, ∀ p q, IsValueAt D.y (R p q) z (Rz p q) :=
    ⟨fun p q => (hvR p q).choose, fun p q => (hvR p q).choose_spec⟩
  obtain ⟨R'z, hR'z⟩ : ∃ R'z : Matrix (Fin D.N) (Fin D.N) ℂ, ∀ p q, IsValueAt D.y (R' p q) z (R'z p q) :=
    ⟨fun p q => (hvR' p q).choose, fun p q => (hvR' p q).choose_spec⟩
  have hRR' : R * R' = 1 := by
    ext p q
    have hcomb : ∑ p, ((R * R') p q - (1 : Matrix (Fin D.N) (Fin D.N) Ω) p q) • bfr p = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, Matrix.mul_apply, Finset.sum_smul]
      have e1 : ∑ p, ∑ i, (R p i * R' i q) • bfr p = bfr q := by
        rw [Finset.sum_comm, hR' q]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hR i, Finset.smul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [smul_smul, mul_comm]
      simp [e1, Matrix.one_apply, ite_smul]
    have := Fintype.linearIndependent_iff.1 hli _ hcomb p
    exact sub_eq_zero.1 this
  refine ⟨b', R, R', Rz, R'z, hli', hspan, hR, hR', hRz, hR'z, ?_⟩
  ext p r
  have hv := LineFlag.isValueAt_sum _ _ fun q => LineFlag.isValueAt_mul (hRz p q) (hR'z q r)
  have e : ∑ q, R p q * R' q r = (1 : Matrix (Fin D.N) (Fin D.N) Ω) p r := by
    rw [← Matrix.mul_apply, hRR']
  rw [e, Matrix.one_apply] at hv
  rw [Matrix.mul_apply, Matrix.one_apply]
  split_ifs at hv ⊢
  · exact isValueAt_one hz hv
  · exact isValueAt_zero hz hv

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
