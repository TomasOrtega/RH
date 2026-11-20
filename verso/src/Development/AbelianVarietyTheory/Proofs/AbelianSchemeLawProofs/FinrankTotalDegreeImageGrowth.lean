import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace DegreeGrowth

variable {K B : Type} [Field K] [CommRing B] [Algebra K B]

def boxSpan (K : Type) {B : Type} [Field K] [CommRing B] [Algebra K B] {s n : ℕ}
    (y : Fin s → B) (b : Fin n → B) (D : ℕ) : Submodule K B :=
  Submodule.span K (Set.range fun al : (Fin s → Fin (D + 1)) × Fin n =>
    (∏ i, y i ^ (al.1 i : ℕ)) * b al.2)

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨(fun i => ⟨a i, Nat.lt_succ_of_le (ha i)⟩, l), rfl⟩`.
-/
theorem mem_boxSpan {s n : ℕ} (y : Fin s → B) (b : Fin n → B) (D : ℕ) (a : Fin s → ℕ)
    (ha : ∀ i, a i ≤ D) (l : Fin n) : (∏ i, y i ^ a i) * b l ∈ boxSpan K y b D :=
  Submodule.subset_span ⟨(fun i => ⟨a i, Nat.lt_succ_of_le (ha i)⟩, l), rfl⟩

/- English proof (translation)
Use `finrank_range_le_card (R := K) (fun al : (Fin s → Fin (D + 1)) × Fin n => (∏ i, y i ^ (al.1 i : ℕ)) * b al.2)` as an intermediate fact. Use `le_trans this ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem finrank_boxSpan_le {s n : ℕ} (y : Fin s → B) (b : Fin n → B) (D : ℕ) :
    Module.finrank K (boxSpan K y b D) ≤ (D + 1) ^ s * n := by
  have := finrank_range_le_card (R := K) (fun al : (Fin s → Fin (D + 1)) × Fin n =>
    (∏ i, y i ^ (al.1 i : ℕ)) * b al.2)
  refine le_trans this ?_
  simp

instance finite_boxSpan {s n : ℕ} (y : Fin s → B) (b : Fin n → B) (D : ℕ) :
    Module.Finite K (boxSpan K y b D) :=
  Module.Finite.span_of_finite K (Set.finite_range _)

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨⟨c, l⟩, rfl⟩` from `hx`. Establish `h` using `mem_boxSpan (K := K) y b (D + d) (fun i => (c i : ℕ) + a i) (fun i => add_le_add (Nat.le_of_lt_succ (c i).2) (ha i)) l`. Simplify using `only [pow_add, Finset.prod_mul_distrib] at h`.

Use `h using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => simp`. Consider the case `add x z _ _ hx hz => rw [mul_add]`. Conclude with `add_mem hx hz`.

Consider the case `smul c x _ hx => rw [mul_smul_comm]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem monomial_mul_mem {s n : ℕ} (y : Fin s → B) (b : Fin n → B) (D d : ℕ) (a : Fin s → ℕ)
    (ha : ∀ i, a i ≤ d) {x : B} (hx : x ∈ boxSpan K y b D) :
    (∏ i, y i ^ a i) * x ∈ boxSpan K y b (D + d) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨c, l⟩, rfl⟩ := hx
    have h := mem_boxSpan (K := K) y b (D + d) (fun i => (c i : ℕ) + a i)
      (fun i => add_le_add (Nat.le_of_lt_succ (c i).2) (ha i)) l
    simp only [pow_add, Finset.prod_mul_distrib] at h
    convert h using 1
    ring
  | zero => simp
  | add x z _ _ hx hz => rw [mul_add]; exact add_mem hx hz
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Introduce `x hx`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le h`. Simplify using `using monomial_mul_mem y b D d (fun _ => 0) (fun _ => Nat.zero_le _) hx`.
-/
theorem boxSpan_mono {s n : ℕ} (y : Fin s → B) (b : Fin n → B) {D E : ℕ} (h : D ≤ E) :
    boxSpan K y b D ≤ boxSpan K y b E := by
  intro x hx
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  simpa using monomial_mul_mem y b D d (fun _ => 0) (fun _ => Nat.zero_le _) hx

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on'' with`. Consider the case `C a`. Take `⟨D, hD⟩` from `hx`. Use `⟨D, ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.aeval_C, ← Algebra.smul_def]`.

Conclude with `Submodule.smul_mem _ _ hD`. Consider the case `monomial_add a c f _ _ h1' h2`. Take `⟨D1, h1⟩` from `h2`. Take `⟨D2, h2⟩` from `h1'`. Use `⟨max D1 D2, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, add_mul]`. Conclude with `add_mem (boxSpan_mono y b (le_max_left _ _) h1) (boxSpan_mono y b (le_max_right _ _) h2)`. Consider the case `mul_X p i h`. Take `⟨D, hD⟩` from `h`. Use `⟨D + 1, ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `have := monomial_mul_mem y b D 1 (Pi.single i 1) (fun j => by by_cases hj : j = i <;> simp [hj]) hD`. Establish `e : ∏ j, y j ^ (Pi.single i 1 : Fin s → ℕ) j = y i`. Apply the tactic sequence `rw [Finset.prod_eq_single i] <;> simp +contextual`. Rewrite `this` using `[e]`. Rewrite using `[map_mul, MvPolynomial.aeval_X]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_aeval_mul_mem {s n : ℕ} (y : Fin s → B) (b : Fin n → B)
    (p : MvPolynomial (Fin s) K) {x : B} (hx : ∃ D, x ∈ boxSpan K y b D) :
    ∃ D, MvPolynomial.aeval y p * x ∈ boxSpan K y b D := by
  induction p using MvPolynomial.induction_on'' with
  | C a =>
    obtain ⟨D, hD⟩ := hx
    refine ⟨D, ?_⟩
    rw [MvPolynomial.aeval_C, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hD
  | monomial_add a c f _ _ h1' h2 =>
    obtain ⟨D1, h1⟩ := h2
    obtain ⟨D2, h2⟩ := h1'
    refine ⟨max D1 D2, ?_⟩
    rw [map_add, add_mul]
    exact add_mem (boxSpan_mono y b (le_max_left _ _) h1) (boxSpan_mono y b (le_max_right _ _) h2)
  | mul_X p i h =>
    obtain ⟨D, hD⟩ := h
    refine ⟨D + 1, ?_⟩
    have := monomial_mul_mem y b D 1 (Pi.single i 1)
      (fun j => by by_cases hj : j = i <;> simp [hj]) hD
    have e : ∏ j, y j ^ (Pi.single i 1 : Fin s → ℕ) j = y i := by
      rw [Finset.prod_eq_single i] <;> simp +contextual
    rw [e] at this
    rw [map_mul, MvPolynomial.aeval_X]
    convert this using 1
    ring

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨⟨c, l⟩, rfl⟩` from `hx`. Establish `h` using `monomial_mul_mem y b d D (fun i => (c i : ℕ)) (fun i => Nat.le_of_lt_succ (c i).2) (hz l)`. Use `h using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => simp`. Consider the case `add x z _ _ hx hz => rw [mul_add]`. Conclude with `add_mem hx hz`. Consider the case `smul c x _ hx => rw [mul_smul_comm]`.

Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem mul_mem_boxSpan {s n : ℕ} (y : Fin s → B) (b : Fin n → B) (D d : ℕ) (z : B)
    (hz : ∀ l, z * b l ∈ boxSpan K y b d) {x : B} (hx : x ∈ boxSpan K y b D) :
    z * x ∈ boxSpan K y b (d + D) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨c, l⟩, rfl⟩ := hx
    have h := monomial_mul_mem y b d D (fun i => (c i : ℕ))
      (fun i => Nat.le_of_lt_succ (c i).2) (hz l)
    convert h using 1
    ring
  | zero => simp
  | add x z _ _ hx hz => rw [mul_add]; exact add_mem hx hz
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using hx`. Consider the case `succ k ih`. Use `mul_mem_boxSpan y b _ d z hz ih` as an intermediate fact. Rewrite using `[show (k + 1) * d + D = d + (k * d + D) by ring, show z ^ (k + 1) * x = z * (z ^ k * x) by ring]`.

Conclude with `this`.
-/
theorem pow_mul_mem_boxSpan {s n : ℕ} (y : Fin s → B) (b : Fin n → B) (D d : ℕ) (z : B)
    (hz : ∀ l, z * b l ∈ boxSpan K y b d) (k : ℕ) {x : B} (hx : x ∈ boxSpan K y b D) :
    z ^ k * x ∈ boxSpan K y b (k * d + D) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    have := mul_mem_boxSpan y b _ d z hz ih
    rw [show (k + 1) * d + D = d + (k * d + D) by ring, show z ^ (k + 1) * x = z * (z ^ k * x) by ring]
    exact this

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using hx`. Consider the case `insert i S hi ih`. Rewrite using `[Finset.prod_insert hi, Finset.sum_insert hi, _root_.mul_assoc, add_mul, add_assoc]`. Conclude with `pow_mul_mem_boxSpan y b _ d (r i) (hr i) (a i) ih`.
-/
theorem prod_mul_mem_boxSpan {s n : ℕ} (y : Fin s → B) (b : Fin n → B) (D d : ℕ) {I : Type}
    (r : I → B) (hr : ∀ i l, r i * b l ∈ boxSpan K y b d) (S : Finset I) (a : I → ℕ) {x : B}
    (hx : x ∈ boxSpan K y b D) :
    (∏ i ∈ S, r i ^ a i) * x ∈ boxSpan K y b ((∑ i ∈ S, a i) * d + D) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hx
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, _root_.mul_assoc, add_mul, add_assoc]
    exact pow_mul_mem_boxSpan y b _ d (r i) (hr i) (a i) ih

/- English proof (translation)
Use `choose f hf using hall`. Take `⟨d, hd⟩ : ∃ d, ∀ il : Fin m × Fin n, f (r il.1 * b il.2) ≤ d` from `(Set.finite_range fun il : Fin m × Fin n => f (r il.1 * b il.2)).bddAbove.imp fun d hd il => hd ⟨il, rfl⟩`. Establish `hr : ∀ i l, r i * b l ∈ boxSpan K y b d` using `fun i l => boxSpan_mono y b (hd (i, l)) (hf _)`. Use `⟨n * (d + f 1 + 1) ^ s, fun t ht => ?_⟩` and prove the remaining obligations. Establish `hle : (MvPolynomial.restrictTotalDegree (Fin m) K t).map (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap ≤ boxSpan K y b (t * d + f 1)`.

Introduce and unpack `_ ⟨p, hp, rfl⟩`. Establish `hp' : p.totalDegree ≤ t` using `(MvPolynomial.mem_restrictTotalDegree _ _ _).1 hp`. Rewrite using `[p.as_sum, map_sum]`. Use `Submodule.sum_mem _ fun a ha => ?_` and prove the remaining obligations. Establish `h1` using `prod_mul_mem_boxSpan y b (f 1) d r hr a.support a (hf 1)`.

Establish `h2 : ∑ i ∈ a.support, a i ≤ t` using `(MvPolynomial.le_totalDegree ha).trans hp'`. Rewrite using `[AlgHom.toLinearMap_apply, MvPolynomial.aeval_monomial, ← Algebra.smul_def]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Rewrite `h1` using `[_root_.mul_one]`. Conclude with `boxSpan_mono y b (by gcongr) h1`.

Use `(Submodule.finrank_mono hle).trans ((finrank_boxSpan_le y b _).trans ?_)` and prove the remaining obligations. Rewrite using `[mul_comm, _root_.mul_assoc, ← mul_pow]`. Use `gcongr`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem upper {s n m : ℕ} (y : Fin s → B) (b : Fin n → B)
    (hall : ∀ x : B, ∃ D, x ∈ boxSpan K y b D) (r : Fin m → B) :
    ∃ C : ℕ, ∀ t : ℕ, 1 ≤ t →
      Module.finrank K ((MvPolynomial.restrictTotalDegree (Fin m) K t).map
        (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap) ≤ C * t ^ s := by
  choose f hf using hall
  obtain ⟨d, hd⟩ : ∃ d, ∀ il : Fin m × Fin n, f (r il.1 * b il.2) ≤ d :=
    (Set.finite_range fun il : Fin m × Fin n => f (r il.1 * b il.2)).bddAbove.imp
      fun d hd il => hd ⟨il, rfl⟩
  have hr : ∀ i l, r i * b l ∈ boxSpan K y b d := fun i l =>
    boxSpan_mono y b (hd (i, l)) (hf _)
  refine ⟨n * (d + f 1 + 1) ^ s, fun t ht => ?_⟩
  have hle : (MvPolynomial.restrictTotalDegree (Fin m) K t).map
        (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap ≤
        boxSpan K y b (t * d + f 1) := by
    rintro _ ⟨p, hp, rfl⟩
    have hp' : p.totalDegree ≤ t := (MvPolynomial.mem_restrictTotalDegree _ _ _).1 hp
    rw [p.as_sum, map_sum]
    refine Submodule.sum_mem _ fun a ha => ?_
    have h1 := prod_mul_mem_boxSpan y b (f 1) d r hr a.support a (hf 1)
    have h2 : ∑ i ∈ a.support, a i ≤ t := (MvPolynomial.le_totalDegree ha).trans hp'
    rw [AlgHom.toLinearMap_apply, MvPolynomial.aeval_monomial, ← Algebra.smul_def]
    refine Submodule.smul_mem _ _ ?_
    rw [_root_.mul_one] at h1
    exact boxSpan_mono y b (by gcongr) h1
  refine (Submodule.finrank_mono hle).trans ((finrank_boxSpan_le y b _).trans ?_)
  rw [mul_comm, _root_.mul_assoc, ← mul_pow]
  gcongr
  nlinarith

/- English proof (translation)
Use `choose q hq using fun i => hr (φ (MvPolynomial.X i))`. Use `set E : ℕ := (∑ i, (q i).totalDegree) + 1 with hE`. Establish `hE0 : 0 < E` using `Nat.succ_pos _`. Use `⟨E ^ s, Nat.one_le_pow _ _ hE0, fun t => ?_⟩` and prove the remaining obligations. Use `set V := (MvPolynomial.restrictTotalDegree (Fin m) K t).map (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap with hV`.

Set `e : (Fin s → Fin (t / E + 1)) → (Fin s →₀ ℕ)` to `fun a => Finsupp.equivFunOnFinite.symm fun i => (a i : ℕ)`. Establish `he : Function.Injective e`. Introduce `a a' h`. Use function extensionality and compare the values at `i`. Use `congrArg (fun z : Fin s →₀ ℕ => z i) h` as an intermediate fact.

Conclude with `Fin.ext (by simpa [e] using this)`. Establish `hli : LinearIndependent K fun a => φ (MvPolynomial.monomial (e a) (1 : K))`. Establish `h1` using `((MvPolynomial.basisMonomials (Fin s) K).linearIndependent.comp e he).map' φ.toLinearMap (LinearMap.ker_eq_bot.2 hφ)`. Simplify `h1` using `[Function.comp_def]`. Establish `hmem : ∀ a, φ (MvPolynomial.monomial (e a) (1 : K)) ∈ V`.

Introduce `a`. Use `⟨∏ i, q i ^ (a i : ℕ), ?_, ?_⟩` and prove the remaining obligations. Use `(MvPolynomial.mem_restrictTotalDegree _ _ _).2 ?_` and prove the remaining obligations. Use `(MvPolynomial.totalDegree_finset_prod _ _).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Finset.mul_sum]`. Conclude with `Nat.mul_le_mul_left _ (Nat.le_succ _)`. Use `_ ≤ t := Nat.div_mul_le_self _ _`. Rewrite using `[MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp)]`. Simplify using `[hq, e]`.

Establish `hli' : LinearIndependent K fun a => (⟨_, hmem a⟩ : V)` using `LinearIndependent.of_comp V.subtype hli`. Establish `hc` using `hli'.fintype_card_le_finrank`. Simplify using `only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ] at hc`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lower {s m : ℕ} (φ : MvPolynomial (Fin s) K →ₐ[K] B) (hφ : Function.Injective φ)
    (r : Fin m → B)
    (hr : Function.Surjective (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B)) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ t : ℕ,
      t ^ s ≤ c * Module.finrank K ((MvPolynomial.restrictTotalDegree (Fin m) K t).map
        (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap) := by
  choose q hq using fun i => hr (φ (MvPolynomial.X i))
  set E : ℕ := (∑ i, (q i).totalDegree) + 1 with hE
  have hE0 : 0 < E := Nat.succ_pos _
  refine ⟨E ^ s, Nat.one_le_pow _ _ hE0, fun t => ?_⟩
  set V := (MvPolynomial.restrictTotalDegree (Fin m) K t).map
        (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap with hV
  let e : (Fin s → Fin (t / E + 1)) → (Fin s →₀ ℕ) := fun a =>
    Finsupp.equivFunOnFinite.symm fun i => (a i : ℕ)
  have he : Function.Injective e := by
    intro a a' h
    funext i
    have := congrArg (fun z : Fin s →₀ ℕ => z i) h
    exact Fin.ext (by simpa [e] using this)
  have hli : LinearIndependent K fun a => φ (MvPolynomial.monomial (e a) (1 : K)) := by
    have h1 := ((MvPolynomial.basisMonomials (Fin s) K).linearIndependent.comp e he).map'
      φ.toLinearMap (LinearMap.ker_eq_bot.2 hφ)
    simpa [Function.comp_def] using h1
  have hmem : ∀ a, φ (MvPolynomial.monomial (e a) (1 : K)) ∈ V := by
    intro a
    refine ⟨∏ i, q i ^ (a i : ℕ), ?_, ?_⟩
    · refine (MvPolynomial.mem_restrictTotalDegree _ _ _).2 ?_
      refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
      calc ∑ i, (q i ^ (a i : ℕ)).totalDegree ≤ ∑ i, (t / E) * (q i).totalDegree :=
            Finset.sum_le_sum fun i _ => (MvPolynomial.totalDegree_pow _ _).trans
              (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ (a i).2))
        _ ≤ (t / E) * E := by
            rw [← Finset.mul_sum]; exact Nat.mul_le_mul_left _ (Nat.le_succ _)
        _ ≤ t := Nat.div_mul_le_self _ _
    · rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
      simp [hq, e]
  have hli' : LinearIndependent K fun a => (⟨_, hmem a⟩ : V) :=
    LinearIndependent.of_comp V.subtype hli
  have hc := hli'.fintype_card_le_finrank
  simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ] at hc
  calc t ^ s ≤ (E * (t / E + 1)) ^ s := Nat.pow_le_pow_left (Nat.lt_mul_div_succ t hE0).le _
    _ ≤ _ := by rw [mul_pow]; exact Nat.mul_le_mul_left _ hc

end DegreeGrowth

/- English proof (translation)
Introduce `K B _ _ _ _ m g r hr hg`. Use `haveI : Algebra.FiniteType K B := Algebra.FiniteType.of_surjective _ hr`. Take `⟨s, φ, hinj, hfin⟩` from `exists_finite_inj_algHom_of_fg K B`. Use `letI : Algebra (MvPolynomial (Fin s) K) B := φ.toRingHom.toAlgebra`. Use `haveI : IsScalarTower K (MvPolynomial (Fin s) K) B := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm`.

Use `haveI : Module.Finite (MvPolynomial (Fin s) K) B := hfin`. Use `haveI : FaithfulSMul (MvPolynomial (Fin s) K) B := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj`. Establish `hs : s = g`. Establish `h` using `trdeg_add_eq K (MvPolynomial (Fin s) K) (A := B)`. Rewrite `h` using `[MvPolynomial.trdeg_of_isDomain, trdeg_eq_zero, hg]`.

Simplify using `using h`. Substitute `hs` using the available equality. Take `⟨n, b, hb⟩` from `Module.Finite.exists_fin (R := MvPolynomial (Fin s) K) (M := B)`. Establish `hall : ∀ x : B, ∃ D, x ∈ DegreeGrowth.boxSpan K (fun i => φ (MvPolynomial.X i)) b D`. Introduce `x`.

Establish `hx : x ∈ Submodule.span (MvPolynomial (Fin s) K) (Set.range b)` using `hb ▸ Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨l, rfl⟩` from `hx`. Conclude with `⟨0, by simpa using DegreeGrowth.mem_boxSpan (K := K) (fun i => φ (MvPolynomial.X i)) b 0 (fun _ => 0) (fun _ => le_rfl) l⟩`.

Consider the case `zero => exact ⟨0, zero_mem _⟩`. Consider the case `add x z _ _ h1 h2`. Take `⟨D1, h1⟩` from `h1`. Take `⟨D2, h2⟩` from `h2`. Conclude with `⟨max D1 D2, add_mem (DegreeGrowth.boxSpan_mono _ b (le_max_left _ _) h1) (DegreeGrowth.boxSpan_mono _ b (le_max_right _ _) h2)⟩`.

Consider the case `smul p x _ hx`. Establish `h` using `DegreeGrowth.exists_aeval_mul_mem _ b p hx`. Establish `e : MvPolynomial.aeval (fun i => φ (MvPolynomial.X i)) = φ` using `(MvPolynomial.aeval_unique φ).symm`. Rewrite `h` using `[e]`. Conclude with `h`.

Take `⟨C, hC⟩` from `DegreeGrowth.upper _ b hall r`. Take `⟨c, hc1, hc⟩` from `DegreeGrowth.lower φ hinj r hr`. Conclude with `⟨c, C, hc1, fun t ht => ⟨hc t, hC t ht⟩⟩`.
-/
theorem finrank_totalDegree_image_growth : ∀ (K B : Type) [Field K] [CommRing B] [IsDomain B] [Algebra K B] (m g : ℕ) (r : Fin m → B), Function.Surjective (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B) → Algebra.trdeg K B = g → ∃ c C : ℕ, 1 ≤ c ∧ ∀ t : ℕ, 1 ≤ t → t ^ g ≤ c * Module.finrank K ((MvPolynomial.restrictTotalDegree (Fin m) K t).map (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap) ∧ Module.finrank K ((MvPolynomial.restrictTotalDegree (Fin m) K t).map (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap) ≤ C * t ^ g := by
  intro K B _ _ _ _ m g r hr hg
  haveI : Algebra.FiniteType K B := Algebra.FiniteType.of_surjective _ hr
  obtain ⟨s, φ, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg K B
  letI : Algebra (MvPolynomial (Fin s) K) B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K (MvPolynomial (Fin s) K) B :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  haveI : Module.Finite (MvPolynomial (Fin s) K) B := hfin
  haveI : FaithfulSMul (MvPolynomial (Fin s) K) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have hs : s = g := by
    have h := trdeg_add_eq K (MvPolynomial (Fin s) K) (A := B)
    rw [MvPolynomial.trdeg_of_isDomain, trdeg_eq_zero, hg] at h
    simpa using h
  subst hs
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := MvPolynomial (Fin s) K) (M := B)
  have hall : ∀ x : B, ∃ D, x ∈ DegreeGrowth.boxSpan K (fun i => φ (MvPolynomial.X i)) b D := by
    intro x
    have hx : x ∈ Submodule.span (MvPolynomial (Fin s) K) (Set.range b) := hb ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      exact ⟨0, by simpa using DegreeGrowth.mem_boxSpan (K := K) (fun i => φ (MvPolynomial.X i)) b 0 (fun _ => 0) (fun _ => le_rfl) l⟩
    | zero => exact ⟨0, zero_mem _⟩
    | add x z _ _ h1 h2 =>
      obtain ⟨D1, h1⟩ := h1
      obtain ⟨D2, h2⟩ := h2
      exact ⟨max D1 D2, add_mem (DegreeGrowth.boxSpan_mono _ b (le_max_left _ _) h1)
        (DegreeGrowth.boxSpan_mono _ b (le_max_right _ _) h2)⟩
    | smul p x _ hx =>
      have h := DegreeGrowth.exists_aeval_mul_mem _ b p hx
      have e : MvPolynomial.aeval (fun i => φ (MvPolynomial.X i)) = φ :=
        (MvPolynomial.aeval_unique φ).symm
      rw [e] at h
      exact h
  obtain ⟨C, hC⟩ := DegreeGrowth.upper _ b hall r
  obtain ⟨c, hc1, hc⟩ := DegreeGrowth.lower φ hinj r hr
  exact ⟨c, C, hc1, fun t ht => ⟨hc t, hC t ht⟩⟩

end GlobalTheory
