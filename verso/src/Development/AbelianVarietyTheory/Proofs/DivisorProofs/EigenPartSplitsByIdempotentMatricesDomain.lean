import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.LieExtProj

open Matrix

variable {W : Type} [CommRing W] {n : ℕ} {R' : Type} [CommRing R'] (β : W →+* R') (v : Fin n → R')

/- English proof (translation)
Rewrite using `[Matrix.map_one _ (map_zero β) (map_one β), one_mulVec, one_smul]`.
-/
theorem act_one : ((1 : Matrix (Fin n) (Fin n) W).map β) *ᵥ v = (1 : R') • v := by
  rw [Matrix.map_one _ (map_zero β) (map_one β), one_mulVec, one_smul]

/- English proof (translation)
Rewrite using `[Matrix.map_add _ (map_add β), add_mulVec, hM, hN, add_smul]`.
-/
theorem act_add {M N : Matrix (Fin n) (Fin n) W} {s s' : R'} (hM : (M.map β) *ᵥ v = s • v)
    (hN : (N.map β) *ᵥ v = s' • v) : ((M + N).map β) *ᵥ v = (s + s') • v := by
  rw [Matrix.map_add _ (map_add β), add_mulVec, hM, hN, add_smul]

/- English proof (translation)
Rewrite using `[Matrix.map_sub _ (map_sub β), sub_mulVec, hM, hN, sub_smul]`.
-/
theorem act_sub {M N : Matrix (Fin n) (Fin n) W} {s s' : R'} (hM : (M.map β) *ᵥ v = s • v)
    (hN : (N.map β) *ᵥ v = s' • v) : ((M - N).map β) *ᵥ v = (s - s') • v := by
  rw [Matrix.map_sub _ (map_sub β), sub_mulVec, hM, hN, sub_smul]

/- English proof (translation)
Establish `: (r • M).map β = β r • M.map β` using `by ext; simp`. Rewrite using `[this, Matrix.smul_mulVec, hM, smul_smul]`.
-/
theorem act_smul {M : Matrix (Fin n) (Fin n) W} {s : R'} (r : W) (hM : (M.map β) *ᵥ v = s • v) :
    ((r • M).map β) *ᵥ v = (β r * s) • v := by
  have : (r • M).map β = β r • M.map β := by ext; simp
  rw [this, Matrix.smul_mulVec, hM, smul_smul]

/- English proof (translation)
Rewrite using `[Matrix.map_mul, ← mulVec_mulVec, hN, mulVec_smul, hM, smul_smul, mul_comm]`.
-/
theorem act_mul {M N : Matrix (Fin n) (Fin n) W} {s s' : R'} (hM : (M.map β) *ᵥ v = s • v)
    (hN : (N.map β) *ᵥ v = s' • v) : ((M * N).map β) *ᵥ v = (s * s') • v := by
  rw [Matrix.map_mul, ← mulVec_mulVec, hN, mulVec_smul, hM, smul_smul, mul_comm]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simpa using act_one β v`. Consider the case `cons j l ih => simpa using act_mul β v (h j) ih`.
-/
theorem act_list {κ : Type} (F : κ → Matrix (Fin n) (Fin n) W) (S : κ → R')
    (h : ∀ j, ((F j).map β) *ᵥ v = S j • v) (l : List κ) :
    (((l.map F).prod).map β) *ᵥ v = (l.map S).prod • v := by
  induction l with
  | nil => simpa using act_one β v
  | cons j l ih => simpa using act_mul β v (h j) ih

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj]`. Conclude with `act_add β v (h j) ih`.
-/
theorem act_finset {κ : Type} (F : κ → Matrix (Fin n) (Fin n) W) (S : κ → R')
    (h : ∀ j, ((F j).map β) *ᵥ v = S j • v) (s : Finset κ) :
    ((∑ j ∈ s, F j).map β) *ᵥ v = (∑ j ∈ s, S j) • v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj]; exact act_add β v (h j) ih

/- English proof (translation)
The claim follows from `act_finset β v _ _ (fun x => act_smul β v (f x) (h x)) f.support`.
-/
theorem act_finsupp {O : Type} (F : O → Matrix (Fin n) (Fin n) W) (S : O → R')
    (h : ∀ x, ((F x).map β) *ᵥ v = S x • v) (f : O →₀ W) :
    ((f.sum fun x r => r • F x).map β) *ᵥ v = (f.sum fun x r => β r * S x) • v :=
  act_finset β v _ _ (fun x => act_smul β v (f x) (h x)) f.support

/- English proof (translation)
The claim follows from `Matrix.toLin'.injective (LinearMap.ext fun x => by simpa [Matrix.toLin'_apply] using h x)`.
-/
theorem ext_mulVec {L : Type} [Field L] {M N : Matrix (Fin n) (Fin n) L} (h : ∀ x, M *ᵥ x = N *ᵥ x) : M = N :=
  Matrix.toLin'.injective (LinearMap.ext fun x => by simpa [Matrix.toLin'_apply] using h x)

end GlobalTheory.LieExtProj

namespace GlobalTheory.LieExtProj
open Matrix

/- English proof (translation)
Introduce `W L _ _ _ _ _ O _ n a A ω tr nm ρ t hω hρ htω hcop hdisc hsplit`. Establish `hu2 : (2 * ρ - tr) * (2 * ρ - tr) = ((tr ^ 2 - 4 * nm : ℤ) : W)` using `by push_cast; linear_combination 4 * hρ`. Establish `hu : IsUnit (2 * ρ - (tr : W))` using `isUnit_of_mul_isUnit_left (hu2 ▸ hdisc)`. Take `⟨ui, hui⟩` from `hu.exists_left_inv`. Use `set P : Matrix (Fin n) (Fin n) W := ui • (A ω + (ρ - tr) • 1) with hPdef`.

Establish `hf : ∀ i j, ∃ f : O →₀ W, i ≠ j → (f.sum fun x r => r * t i x) - (f.sum fun x r => r * t j x) = 1`. Introduce `i j`. Distinguish the cases in `hij : i = j`. Conclude with `⟨0, fun h => (h hij).elim⟩`. Establish `h1 : (1 : W) ∈ Ideal.span (Set.range fun x => t i x - t j x)`.

Rewrite using `[hcop i j hij]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨f, hf⟩` from `(Finsupp.mem_span_range_iff_exists_finsupp).1 h1`. Use `⟨f, fun _ => ?_⟩` and prove the remaining obligations. Rewrite using `[← hf, ← Finsupp.sum_sub]`.

Simplify using `[Finsupp.sum, smul_eq_mul, mul_sub]`. Use `choose f hf using hf`. Set `Z : Fin a → Fin a → Matrix (Fin n) (Fin n) W` to `fun i j => ((f i j).sum fun x r => r • A x) - ((f i j).sum fun x r => r * t j x) • (1 : Matrix (Fin n) (Fin n) W)`. Set `E : Fin a → Matrix (Fin n) (Fin n) W` to `fun i => ((List.finRange a).map fun j => if j = i then 1 else Z i j).prod`. Set `Q : Fin a → Matrix (Fin n) (Fin n) W` to `fun i => E i * P`.

Establish `hP : ∀ (R' : Type) [CommRing R'] (β : W →+* R') (v : Fin n → R'), ((A ω).map β) *ᵥ v = β ρ • v → (P.map β) *ᵥ v = v`. Introduce `R' _ β v hv`. Establish `h` using `act_smul β v ui (act_add β v hv (act_smul β v (ρ - tr) (act_one β v)))`. Rewrite using `[h]`. Establish `: β ui * (β ρ + β (ρ - tr) * 1) = β (ui * (2 * ρ - tr))`.

Simplify using `only [map_mul, map_sub, map_ofNat, _root_.mul_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, hui, map_one, one_smul]`. Establish `hE : ∀ (R' : Type) [CommRing R'] (β : W →+* R') (k i : Fin a) (v : Fin n → R'), (∀ c, ((A c).map β) *ᵥ v = β (t k c) • v) → ((E i).map β) *ᵥ v = (if k = i then (1 : R') else 0) • v`. Introduce `R' _ β k i v hv`.

Establish `hZ : ∀ j, ((if j = i then 1 else Z i j).map β) *ᵥ v = (if j = i then 1 else β ((f i j).sum fun x r => r * t k x) - β ((f i j).sum fun x r => r * t j x)) • v`. Introduce `j`. Use `split_ifs`. Conclude with `act_one β v`. Establish `h1` using `act_finsupp β v (fun x => A x) (fun x => β (t k x)) hv (f i j)`.

Establish `h2` using `act_sub β v h1 (act_smul β v ((f i j).sum fun x r => r * t j x) (act_one β v))`. Use `h2.trans ?_` and prove the remaining obligations. Use `congr 1`. Simplify using `[Finsupp.sum, map_sum, map_mul]`. Rewrite using `[act_list β v _ _ hZ]`.

Distinguish the cases in `hki : k = i`. Rewrite using `[if_pos hki]`. Substitute `hki` using the available equality. Use `congrArg (· • v) ?_` and prove the remaining obligations. Apply `List.prod_eq_one` to reduce the goal to its premises.

Introduce `x hx`. Take `⟨j, -, rfl⟩` from `List.mem_map.1 hx`. Use `split_ifs with hj`. Both sides reduce to the same expression. Rewrite using `[← map_sub, hf k j (Ne.symm hj), map_one]`.

Rewrite using `[if_neg hki]`. Use `congrArg (· • v) ?_` and prove the remaining obligations. Apply `List.prod_eq_zero` to reduce the goal to its premises. Use `List.mem_map.2 ⟨k, List.mem_finRange k, ?_⟩` and prove the remaining obligations. Rewrite using `[if_neg hki, sub_self]`.

Establish `hQ : ∀ (R' : Type) [CommRing R'] (β : W →+* R') (k i : Fin a) (v : Fin n → R'), (∀ c, ((A c).map β) *ᵥ v = β (t k c) • v) → ((Q i).map β) *ᵥ v = (if k = i then (1 : R') else 0) • v`. Introduce `R' _ β k i v hv`. Establish `h1 : (P.map β) *ᵥ v = (1 : R') • v`. Rewrite using `[one_smul]; exact hP R' β v (by rw [hv, htω])`. Establish `h2` using `hE R' β k i v hv`.

Establish `h3` using `act_mul β v h2 h1`. Rewrite `h3` using `[_root_.mul_one]`. Conclude with `h3`. Establish `hAP : A ω * P = ρ • P`. Establish `hω' : ω * ω = (tr : O) * ω - (nm : O)` using `by linear_combination hω`.

Establish `hA2 : A ω * A ω = (tr : W) • A ω - (nm : W) • (1 : Matrix (Fin n) (Fin n) W)`. Rewrite using `[← map_mul, hω', map_sub, map_mul, map_intCast, map_intCast]`. Rewrite using `[Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, zsmul_one, ← zsmul_eq_mul]`. Establish `hnm : (nm : W) = tr * ρ - ρ ^ 2` using `by linear_combination hρ`. Rewrite using `[hPdef, mul_smul_comm, mul_add, mul_smul_comm, _root_.mul_one, hA2, hnm]`.

Use `module`. Use `set βL := algebraMap W L`. Establish `hinj : Function.Injective fun M : Matrix (Fin n) (Fin n) W => M.map βL` using `Matrix.map_injective (IsFractionRing.injective W L)`. Establish `hdec : ∀ x : Fin n → L, ∃ w : Fin a → Fin n → L, (∀ i, ((Q i).map βL) *ᵥ x = w i) ∧ (∀ i c, ((A c).map βL) *ᵥ w i = βL (t i c) • w i) ∧ (P.map βL) *ᵥ x = ∑ i, w i`. Introduce `x`.

Establish `hy : ((A ω).map βL) *ᵥ ((P.map βL) *ᵥ x) = βL ρ • ((P.map βL) *ᵥ x)`. Rewrite using `[mulVec_mulVec, ← Matrix.map_mul, hAP]`. Establish `: (ρ • P).map βL = βL ρ • P.map βL` using `by ext; simp`. Rewrite using `[this, Matrix.smul_mulVec]`. Take `⟨w, hw, hsum⟩` from `hsplit _ hy`.

Use `⟨w, fun i => ?_, hw, hsum⟩` and prove the remaining obligations. Use `show ((E i * P).map βL) *ᵥ x = w i`. Rewrite using `[Matrix.map_mul, ← mulVec_mulVec, hsum, mulVec_sum]`. Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[hE L βL i i (w i) (hw i), if_pos rfl, one_smul]`.

Introduce `k _ hk`. Rewrite using `[hE L βL k i (w k) (hw k), if_neg hk, zero_smul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`. Use `choose w hwQ hwA hwP using hdec`.

Establish `hsumQ : ∑ i, Q i = P`. Apply `hinj` to reduce the goal to its premises. Apply `ext_mulVec` to reduce the goal to its premises. Introduce `x`. Simplify using `only`.

Rewrite using `[hwP x]`. Establish `: (∑ i, Q i).map βL = ∑ i, (Q i).map βL` using `by ext; simp [Matrix.sum_apply]`. Rewrite using `[this, Matrix.sum_mulVec]`. Conclude with `Finset.sum_congr rfl fun i _ => hwQ x i`. Use `⟨Q, fun i => ?_, fun i c => ?_, ?_, ?_⟩` and prove the remaining obligations.

Apply `hinj` to reduce the goal to its premises. Apply `ext_mulVec` to reduce the goal to its premises. Introduce `x`. Simplify using `only`. Rewrite using `[Matrix.map_mul, ← mulVec_mulVec, hwQ x i, hQ L βL i i _ (hwA x i), if_pos rfl, one_smul]`.

Apply `hinj` to reduce the goal to its premises. Apply `ext_mulVec` to reduce the goal to its premises. Introduce `x`. Simplify using `only`. Establish `: (t i c • Q i).map βL = βL (t i c) • (Q i).map βL` using `by ext; simp`.

Rewrite using `[Matrix.map_mul, ← mulVec_mulVec, hwQ x i, hwA x i c, this, Matrix.smul_mulVec, hwQ x i]`. Introduce `R' _ β v hv`. Establish `: (∑ i, Q i).map β = ∑ i, (Q i).map β` using `by ext; simp [Matrix.sum_apply]`. Rewrite using `[← Matrix.sum_mulVec, ← this, hsumQ, hP R' β v hv]`. Introduce `R' _ β i v hv`.

Rewrite using `[hQ R' β i i v hv, if_pos rfl, one_smul]`.
-/
theorem rhoPart_splits_by_idempotents : ∀ (W L : Type) [CommRing W] [IsDomain W] [Field L] [Algebra W L] [IsFractionRing W L] (O : Type) [CommRing O] (n a : ℕ) (A : O →+* Matrix (Fin n) (Fin n) W) (ω : O) (tr nm : ℤ) (ρ : W) (t : Fin a → (O →+* W)), ω ^ 2 - tr * ω + nm = 0 → ρ ^ 2 - tr * ρ + nm = 0 → (∀ i, t i ω = ρ) → (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → IsUnit ((tr ^ 2 - 4 * nm : ℤ) : W) → (∀ v : Fin n → L, ((A ω).map (algebraMap W L)).mulVec v = algebraMap W L ρ • v → ∃ w : Fin a → Fin n → L, (∀ i c, ((A c).map (algebraMap W L)).mulVec (w i) = algebraMap W L (t i c) • w i) ∧ v = ∑ i, w i) → ∃ Q : Fin a → Matrix (Fin n) (Fin n) W, (∀ i, Q i * Q i = Q i) ∧ (∀ i c, A c * Q i = t i c • Q i) ∧ (∀ (R' : Type) [CommRing R'] (β : W →+* R') (v : Fin n → R'), ((A ω).map β).mulVec v = β ρ • v → v = ∑ i, ((Q i).map β).mulVec v) ∧ ∀ (R' : Type) [CommRing R'] (β : W →+* R') (i : Fin a) (v : Fin n → R'), (∀ c, ((A c).map β).mulVec v = β (t i c) • v) → ((Q i).map β).mulVec v = v := by
  intro W L _ _ _ _ _ O _ n a A ω tr nm ρ t hω hρ htω hcop hdisc hsplit
  classical
  have hu2 : (2 * ρ - tr) * (2 * ρ - tr) = ((tr ^ 2 - 4 * nm : ℤ) : W) := by
    push_cast; linear_combination 4 * hρ
  have hu : IsUnit (2 * ρ - (tr : W)) := isUnit_of_mul_isUnit_left (hu2 ▸ hdisc)
  obtain ⟨ui, hui⟩ := hu.exists_left_inv
  set P : Matrix (Fin n) (Fin n) W := ui • (A ω + (ρ - tr) • 1) with hPdef

  have hf : ∀ i j, ∃ f : O →₀ W, i ≠ j →
      (f.sum fun x r => r * t i x) - (f.sum fun x r => r * t j x) = 1 := by
    intro i j
    by_cases hij : i = j
    · exact ⟨0, fun h => (h hij).elim⟩
    · have h1 : (1 : W) ∈ Ideal.span (Set.range fun x => t i x - t j x) := by
        rw [hcop i j hij]; trivial
      obtain ⟨f, hf⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 h1
      refine ⟨f, fun _ => ?_⟩
      rw [← hf, ← Finsupp.sum_sub]
      simp [Finsupp.sum, smul_eq_mul, mul_sub]
  choose f hf using hf
  let Z : Fin a → Fin a → Matrix (Fin n) (Fin n) W := fun i j =>
    ((f i j).sum fun x r => r • A x) - ((f i j).sum fun x r => r * t j x) • (1 : Matrix (Fin n) (Fin n) W)
  let E : Fin a → Matrix (Fin n) (Fin n) W := fun i =>
    ((List.finRange a).map fun j => if j = i then 1 else Z i j).prod
  let Q : Fin a → Matrix (Fin n) (Fin n) W := fun i => E i * P

  have hP : ∀ (R' : Type) [CommRing R'] (β : W →+* R') (v : Fin n → R'),
      ((A ω).map β) *ᵥ v = β ρ • v → (P.map β) *ᵥ v = v := by
    intro R' _ β v hv
    have h := act_smul β v ui (act_add β v hv (act_smul β v (ρ - tr) (act_one β v)))
    rw [h]
    have : β ui * (β ρ + β (ρ - tr) * 1) = β (ui * (2 * ρ - tr)) := by
      simp only [map_mul, map_sub, map_ofNat, _root_.mul_one]; ring
    rw [this, hui, map_one, one_smul]

  have hE : ∀ (R' : Type) [CommRing R'] (β : W →+* R') (k i : Fin a) (v : Fin n → R'),
      (∀ c, ((A c).map β) *ᵥ v = β (t k c) • v) → ((E i).map β) *ᵥ v = (if k = i then (1 : R') else 0) • v := by
    intro R' _ β k i v hv
    have hZ : ∀ j, ((if j = i then 1 else Z i j).map β) *ᵥ v =
        (if j = i then 1 else β ((f i j).sum fun x r => r * t k x) - β ((f i j).sum fun x r => r * t j x)) • v := by
      intro j
      split_ifs
      · exact act_one β v
      · have h1 := act_finsupp β v (fun x => A x) (fun x => β (t k x)) hv (f i j)
        have h2 := act_sub β v h1 (act_smul β v ((f i j).sum fun x r => r * t j x) (act_one β v))
        refine h2.trans ?_
        congr 1
        simp [Finsupp.sum, map_sum, map_mul]
    rw [act_list β v _ _ hZ]
    by_cases hki : k = i
    · rw [if_pos hki]
      subst hki
      refine congrArg (· • v) ?_
      apply List.prod_eq_one
      intro x hx
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
      split_ifs with hj
      · rfl
      · rw [← map_sub, hf k j (Ne.symm hj), map_one]
    · rw [if_neg hki]
      refine congrArg (· • v) ?_
      apply List.prod_eq_zero
      refine List.mem_map.2 ⟨k, List.mem_finRange k, ?_⟩
      rw [if_neg hki, sub_self]
  have hQ : ∀ (R' : Type) [CommRing R'] (β : W →+* R') (k i : Fin a) (v : Fin n → R'),
      (∀ c, ((A c).map β) *ᵥ v = β (t k c) • v) → ((Q i).map β) *ᵥ v = (if k = i then (1 : R') else 0) • v := by
    intro R' _ β k i v hv
    have h1 : (P.map β) *ᵥ v = (1 : R') • v := by
      rw [one_smul]; exact hP R' β v (by rw [hv, htω])
    have h2 := hE R' β k i v hv
    have h3 := act_mul β v h2 h1
    rw [_root_.mul_one] at h3
    exact h3

  have hAP : A ω * P = ρ • P := by
    have hω' : ω * ω = (tr : O) * ω - (nm : O) := by linear_combination hω
    have hA2 : A ω * A ω = (tr : W) • A ω - (nm : W) • (1 : Matrix (Fin n) (Fin n) W) := by
      rw [← map_mul, hω', map_sub, map_mul, map_intCast, map_intCast]
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, zsmul_one, ← zsmul_eq_mul]
    have hnm : (nm : W) = tr * ρ - ρ ^ 2 := by linear_combination hρ
    rw [hPdef, mul_smul_comm, mul_add, mul_smul_comm, _root_.mul_one, hA2, hnm]
    module

  set βL := algebraMap W L
  have hinj : Function.Injective fun M : Matrix (Fin n) (Fin n) W => M.map βL :=
    Matrix.map_injective (IsFractionRing.injective W L)
  have hdec : ∀ x : Fin n → L, ∃ w : Fin a → Fin n → L,
      (∀ i, ((Q i).map βL) *ᵥ x = w i) ∧ (∀ i c, ((A c).map βL) *ᵥ w i = βL (t i c) • w i) ∧
      (P.map βL) *ᵥ x = ∑ i, w i := by
    intro x
    have hy : ((A ω).map βL) *ᵥ ((P.map βL) *ᵥ x) = βL ρ • ((P.map βL) *ᵥ x) := by
      rw [mulVec_mulVec, ← Matrix.map_mul, hAP]
      have : (ρ • P).map βL = βL ρ • P.map βL := by ext; simp
      rw [this, Matrix.smul_mulVec]
    obtain ⟨w, hw, hsum⟩ := hsplit _ hy
    refine ⟨w, fun i => ?_, hw, hsum⟩
    show ((E i * P).map βL) *ᵥ x = w i
    rw [Matrix.map_mul, ← mulVec_mulVec, hsum, mulVec_sum]
    rw [Finset.sum_eq_single i]
    · rw [hE L βL i i (w i) (hw i), if_pos rfl, one_smul]
    · intro k _ hk; rw [hE L βL k i (w k) (hw k), if_neg hk, zero_smul]
    · intro h; exact absurd (Finset.mem_univ i) h
  choose w hwQ hwA hwP using hdec
  have hsumQ : ∑ i, Q i = P := by
    apply hinj
    apply ext_mulVec
    intro x
    simp only
    rw [hwP x]
    have : (∑ i, Q i).map βL = ∑ i, (Q i).map βL := by ext; simp [Matrix.sum_apply]
    rw [this, Matrix.sum_mulVec]
    exact Finset.sum_congr rfl fun i _ => hwQ x i
  refine ⟨Q, fun i => ?_, fun i c => ?_, ?_, ?_⟩
  · apply hinj
    apply ext_mulVec
    intro x
    simp only
    rw [Matrix.map_mul, ← mulVec_mulVec, hwQ x i, hQ L βL i i _ (hwA x i), if_pos rfl, one_smul]
  · apply hinj
    apply ext_mulVec
    intro x
    simp only
    have : (t i c • Q i).map βL = βL (t i c) • (Q i).map βL := by ext; simp
    rw [Matrix.map_mul, ← mulVec_mulVec, hwQ x i, hwA x i c, this, Matrix.smul_mulVec, hwQ x i]
  · intro R' _ β v hv
    have : (∑ i, Q i).map β = ∑ i, (Q i).map β := by ext; simp [Matrix.sum_apply]
    rw [← Matrix.sum_mulVec, ← this, hsumQ, hP R' β v hv]
  · intro R' _ β i v hv
    rw [hQ R' β i i v hv, if_pos rfl, one_smul]

end GlobalTheory.LieExtProj
