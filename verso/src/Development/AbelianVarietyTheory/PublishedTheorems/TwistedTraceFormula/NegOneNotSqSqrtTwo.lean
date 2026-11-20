import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.QuadSymbol

namespace GlobalTheory.QuadSymbol.Model

section Quad
variable {K : Type} [Field K] (d : K) [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)]

open NumberField IsDedekindDomain in
variable {K : Type} [Field K] (d : K) [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨QuadraticAlgebra.finrank_eq_two d 0⟩`.
-/
theorem _root_.GlobalTheory.QuadSymbol.Model.isQuadratic :
    Algebra.IsQuadraticExtension K (QuadraticAlgebra K d 0) :=
  ⟨QuadraticAlgebra.finrank_eq_two d 0⟩

open NumberField IsDedekindDomain in
variable {K : Type} [Field K] (d : K) [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)] in
/- English proof (translation)
Use `haveI : Module.Finite ℚ (QuadraticAlgebra K d 0) := Module.Finite.trans K _`. Conclude with `⟨⟩`.
-/
theorem _root_.GlobalTheory.QuadSymbol.Model.numberField [NumberField K] :
    NumberField (QuadraticAlgebra K d 0) := by
  haveI : Module.Finite ℚ (QuadraticAlgebra K d 0) := Module.Finite.trans K _
  exact ⟨⟩

open NumberField IsDedekindDomain in
variable {K : Type} [Field K] (d : K) [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)] in

/- English proof (translation)
Use `_root_.GlobalTheory.QuadSymbol.mem_normGroup_iff_form (QuadraticAlgebra.basis d 0) ?_ ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [QuadraticAlgebra.basis] <;> rfl`. Apply the tactic sequence `ext <;> simp [QuadraticAlgebra.basis]`.
-/
theorem _root_.GlobalTheory.QuadSymbol.Model.mem_normGroup_sqrt {A : Type} [CommRing A] [Algebra K A] {x : Aˣ} :
    x ∈ _root_.GlobalTheory.QuadSymbol.normGroup K (QuadraticAlgebra K d 0) A ↔
      ∃ a b : A, (x : A) = a ^ 2 - algebraMap K A d * b ^ 2 := by
  refine _root_.GlobalTheory.QuadSymbol.mem_normGroup_iff_form (QuadraticAlgebra.basis d 0) ?_ ?_
  · ext <;> simp [QuadraticAlgebra.basis] <;> rfl
  · ext <;> simp [QuadraticAlgebra.basis]

/- English proof (translation)
Rewrite using `[eta_eq_one_iff, mem_normGroup_sqrt]`. Use `⟨(x + 1) / 2, (x - 1) / (2 * s), ?_⟩` and prove the remaining obligations. Rewrite using `[← hs]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eta_split {A : Type} [Field A] [Algebra K A] (h2 : (2 : A) ≠ 0) {s : A} (hs0 : s ≠ 0)
    (hs : s ^ 2 = algebraMap K A d) (x : Aˣ) : eta K (QuadraticAlgebra K d 0) A x = 1 := by
  rw [eta_eq_one_iff, mem_normGroup_sqrt]
  refine ⟨(x + 1) / 2, (x - 1) / (2 * s), ?_⟩
  rw [← hs]
  field_simp
  ring

end Quad

section Real
variable {K : Type} [Field K] [Fact (∀ r : K, r ^ 2 ≠ -1 + 0 * r)]

open NumberField IsDedekindDomain in
variable {K : Type} [Field K] [Fact (∀ r : K, r ^ 2 ≠ -1 + 0 * r)] in

/- English proof (translation)
Rewrite using `[_root_.GlobalTheory.QuadSymbol.eta_eq_neg_one_iff, _root_.GlobalTheory.QuadSymbol.Model.mem_normGroup_sqrt]`. Introduce and unpack `⟨a, b, h⟩`. Establish `h' : (-1 : w.Completion) = a ^ 2 + b ^ 2`. Rewrite `h` using `[map_neg, map_one]`. Simplify `h` using `[_root_.GlobalTheory.QuadSymbol.infDiag, _root_.GlobalTheory.QuadSymbol.toUnits, sub_eq_add_neg]`.

Use `congrArg (InfinitePlace.Completion.ringEquivRealOfIsReal hw) h'` as an intermediate fact. Simplify using `only [map_neg, map_one, map_add, map_pow] at this`. Use polynomial arithmetic with `[sq_nonneg (InfinitePlace.Completion.ringEquivRealOfIsReal hw a), sq_nonneg (InfinitePlace.Completion.ringEquivRealOfIsReal hw b)]`.
-/
theorem _root_.GlobalTheory.QuadSymbol.Model.eta_real_place (w : InfinitePlace K) (hw : w.IsReal) :
    _root_.GlobalTheory.QuadSymbol.eta K (QuadraticAlgebra K (-1) 0) w.Completion
      (_root_.GlobalTheory.QuadSymbol.infDiag K (-1) w) = -1 := by
  rw [_root_.GlobalTheory.QuadSymbol.eta_eq_neg_one_iff, _root_.GlobalTheory.QuadSymbol.Model.mem_normGroup_sqrt]
  rintro ⟨a, b, h⟩
  have h' : (-1 : w.Completion) = a ^ 2 + b ^ 2 := by
    rw [map_neg, map_one] at h
    simpa [_root_.GlobalTheory.QuadSymbol.infDiag, _root_.GlobalTheory.QuadSymbol.toUnits, sub_eq_add_neg] using h
  have := congrArg (InfinitePlace.Completion.ringEquivRealOfIsReal hw) h'
  simp only [map_neg, map_one, map_add, map_pow] at this
  nlinarith [sq_nonneg (InfinitePlace.Completion.ringEquivRealOfIsReal hw a),
    sq_nonneg (InfinitePlace.Completion.ringEquivRealOfIsReal hw b)]

/- English proof (translation)
Use `⟨1, Function.update 1 w (infDiag K (-1) w), ?_, ?_⟩` and prove the remaining obligations. Simplify using `[AlmostNorm, one_mem]`. Establish `h1 : ∀ (A : Type) [CommRing A] [Algebra K A], eta K (QuadraticAlgebra K (-1) 0) A 1 = 1` using `fun A _ _ => eta_eq_one_iff.2 (one_mem _)`. Unfold `etaProd`. Rewrite using `[Finset.prod_eq_single w]`.

Simplify using `[h1, eta_real_place w hw]`. Introduce `b _ hb`. Rewrite using `[Function.update_of_ne hb]`. Conclude with `h1 _`. Simplify using the standard rewrite rules.
-/
theorem exists_etaProd_neg_one [NumberField K] (w : InfinitePlace K) (hw : w.IsReal) :
    ∃ (x : FinFam K) (y : InfFam K), AlmostNorm K (QuadraticAlgebra K (-1) 0) x ∧
      etaProd K (QuadraticAlgebra K (-1) 0) x y = -1 := by
  classical
  refine ⟨1, Function.update 1 w (infDiag K (-1) w), ?_, ?_⟩
  · simp [AlmostNorm, one_mem]
  · have h1 : ∀ (A : Type) [CommRing A] [Algebra K A], eta K (QuadraticAlgebra K (-1) 0) A 1 = 1 :=
      fun A _ _ => eta_eq_one_iff.2 (one_mem _)
    unfold etaProd
    rw [Finset.prod_eq_single w]
    · simp [h1, eta_real_place w hw]
    · intro b _ hb
      rw [Function.update_of_ne hb]
      exact h1 _
    · simp

/- English proof (translation)
Use `isQuadratic (-1 : K)` as an intermediate fact. Use `numberField (-1 : K)` as an intermediate fact. Establish `h` using `((H.1 K (QuadraticAlgebra K (-1) 0)).2.2.2 (-1)).2`. Assume the negation of the conclusion as `hn`. Use `push Not at hn`.

Establish `h1 : ∀ v : HeightOneSpectrum (𝓞 K), eta K (QuadraticAlgebra K (-1) 0) (v.adicCompletion K) (finDiag K (-1) v) = 1` using `fun v => (Int.units_eq_one_or _).resolve_right (hn v)`. Unfold `etaProd at h`. Rewrite `h` using `[Finset.prod_eq_single w (fun b _ hb => absurd (hu b) hb) (by simp), eta_real_place w hw]`. Simplify using `only [h1, finprod_one, one_mul] at h`. Conclude with `absurd h (by decide)`.
-/
theorem exists_finite_place [NumberField K] (w : InfinitePlace K) (hw : w.IsReal)
    (hu : ∀ w', w' = w) (H : GlobalTheory.Published.QuadraticClassFieldTheory) :
    ∃ v : HeightOneSpectrum (𝓞 K),
      eta K (QuadraticAlgebra K (-1) 0) (v.adicCompletion K) (finDiag K (-1) v) = -1 := by
  have := isQuadratic (-1 : K)
  have := numberField (-1 : K)
  have h := ((H.1 K (QuadraticAlgebra K (-1) 0)).2.2.2 (-1)).2
  by_contra hn
  push Not at hn
  have h1 : ∀ v : HeightOneSpectrum (𝓞 K),
      eta K (QuadraticAlgebra K (-1) 0) (v.adicCompletion K) (finDiag K (-1) v) = 1 :=
    fun v => (Int.units_eq_one_or _).resolve_right (hn v)
  unfold etaProd at h
  rw [Finset.prod_eq_single w (fun b _ hb => absurd (hu b) hb) (by simp), eta_real_place w hw] at h
  simp only [h1, finprod_one, one_mul] at h
  exact absurd h (by decide)

end Real

section Tower
variable {F K : Type} [Field F] [Field K] [Algebra F K] (d : F)

def sqrtMap : QuadraticAlgebra F d 0 →ₐ[F] QuadraticAlgebra K (algebraMap F K d) 0 :=
  QuadraticAlgebra.lift ⟨QuadraticAlgebra.omega, by
    ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, Algebra.algebraMap_eq_smul_one]⟩

/- English proof (translation)
Use `isQuadratic d` as an intermediate fact. Use `numberField d` as an intermediate fact. Use `isQuadratic (algebraMap F K d)` as an intermediate fact. Use `numberField (algebraMap F K d)` as an intermediate fact. Use `letI : Algebra (QuadraticAlgebra F d 0) (QuadraticAlgebra K (algebraMap F K d) 0) := (sqrtMap (K := K) d).toRingHom.toAlgebra`.

Establish `: IsScalarTower F (QuadraticAlgebra F d 0) (QuadraticAlgebra K (algebraMap F K d) 0)` using `IsScalarTower.of_algebraMap_eq fun x => ((sqrtMap (K := K) d).commutes x).symm`. Use `H.2 F _ K _ ?_` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce and unpack `⟨x, y⟩ -`. Rewrite using `[QuadraticAlgebra.mk_eq_add_smul_omega]`.

Use `add_mem (Subalgebra.algebraMap_mem _ _) (Subalgebra.smul_mem _ (Algebra.subset_adjoin ?_) _)` and prove the remaining obligations. Use `⟨QuadraticAlgebra.omega, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `sqrtMap (K := K) d _ = _`. Simplify using `[sqrtMap]`.
-/
theorem baseChange_sqrt [NumberField F] [NumberField K] [Fact (∀ r : F, r ^ 2 ≠ d + 0 * r)]
    [Fact (∀ r : K, r ^ 2 ≠ algebraMap F K d + 0 * r)] (H : GlobalTheory.Published.QuadraticClassFieldTheory) :
    (∀ v : HeightOneSpectrum (𝓞 F), BaseChangeAt F (QuadraticAlgebra F d 0) K
      (QuadraticAlgebra K (algebraMap F K d) 0) (v.adicCompletion F)) ∧
    ∀ v : InfinitePlace F, BaseChangeAt F (QuadraticAlgebra F d 0) K
      (QuadraticAlgebra K (algebraMap F K d) 0) v.Completion := by
  have := isQuadratic d
  have := numberField d
  have := isQuadratic (algebraMap F K d)
  have := numberField (algebraMap F K d)
  letI : Algebra (QuadraticAlgebra F d 0) (QuadraticAlgebra K (algebraMap F K d) 0) :=
    (sqrtMap (K := K) d).toRingHom.toAlgebra
  have : IsScalarTower F (QuadraticAlgebra F d 0) (QuadraticAlgebra K (algebraMap F K d) 0) :=
    IsScalarTower.of_algebraMap_eq fun x => ((sqrtMap (K := K) d).commutes x).symm
  refine H.2 F _ K _ ?_
  rw [eq_top_iff]
  rintro ⟨x, y⟩ -
  rw [QuadraticAlgebra.mk_eq_add_smul_omega]
  refine add_mem (Subalgebra.algebraMap_mem _ _) (Subalgebra.smul_mem _ (Algebra.subset_adjoin ?_) _)
  refine ⟨QuadraticAlgebra.omega, ?_⟩
  change sqrtMap (K := K) d _ = _
  simp [sqrtMap]

end Tower

instance two_not_sq_rat : Fact (∀ r : ℚ, r ^ 2 ≠ 2 + 0 * r) := ⟨fun r h => by
  rw [zero_mul, add_zero] at h
  have h1 := congrArg (padicValRat 2) h
  have h2 : padicValRat 2 (2 : ℚ) = 1 := by exact_mod_cast padicValRat.self (p := 2) (by norm_num)
  rw [padicValRat.pow, h2] at h1
  omega⟩

instance neg_one_not_sq_rat : Fact (∀ r : ℚ, r ^ 2 ≠ -1 + 0 * r) := ⟨fun r h => by
  nlinarith [sq_nonneg r]⟩

/- English proof (translation)
Introduce `h`. Use `congrArg QuadraticAlgebra.re h` as an intermediate fact. Simplify using `[pow_two, QuadraticAlgebra.re_one] at this`. Use polynomial arithmetic with `[mul_self_nonneg r.re, mul_self_nonneg r.im]`.
-/
theorem neg_one_not_sq_sqrt_two (r : QuadraticAlgebra ℚ 2 0) : r ^ 2 ≠ -1 + 0 * r := by
  intro h
  have := congrArg QuadraticAlgebra.re h
  simp [pow_two, QuadraticAlgebra.re_one] at this
  nlinarith [mul_self_nonneg r.re, mul_self_nonneg r.im]

/- English proof (translation)
Use `numberField (2 : ℚ)` as an intermediate fact. Establish `hF : Fact (∀ r : QuadraticAlgebra ℚ 2 0, r ^ 2 ≠ algebraMap ℚ (QuadraticAlgebra ℚ 2 0) (-1) + 0 * r)` using `⟨fun r => by rw [map_neg, map_one]; exact neg_one_not_sq_sqrt_two r⟩`. Use `⟨hF, fun v => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `convert (baseChange_sqrt (F := ℚ) (K := QuadraticAlgebra ℚ 2 0) (-1) H).1 v <;>`. Conclude with `Subsingleton.elim _ _`.
-/
theorem baseChange_eight (H : GlobalTheory.Published.QuadraticClassFieldTheory) :
    ∃ _ : Fact (∀ r : QuadraticAlgebra ℚ 2 0,
        r ^ 2 ≠ algebraMap ℚ (QuadraticAlgebra ℚ 2 0) (-1) + 0 * r),
      ∀ v : HeightOneSpectrum (𝓞 ℚ), BaseChangeAt ℚ (QuadraticAlgebra ℚ (-1) 0) (QuadraticAlgebra ℚ 2 0)
        (QuadraticAlgebra (QuadraticAlgebra ℚ 2 0) (algebraMap ℚ (QuadraticAlgebra ℚ 2 0) (-1)) 0)
        (v.adicCompletion ℚ) := by
  have := numberField (2 : ℚ)
  have hF : Fact (∀ r : QuadraticAlgebra ℚ 2 0,
      r ^ 2 ≠ algebraMap ℚ (QuadraticAlgebra ℚ 2 0) (-1) + 0 * r) :=
    ⟨fun r => by rw [map_neg, map_one]; exact neg_one_not_sq_sqrt_two r⟩
  refine ⟨hF, fun v => ?_⟩
  convert (baseChange_sqrt (F := ℚ) (K := QuadraticAlgebra ℚ 2 0) (-1) H).1 v <;>
    exact Subsingleton.elim _ _

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_finite_place (K := ℚ) Rat.infinitePlace Rat.isReal_infinitePlace (fun _ => Subsingleton.elim _ _) H`. Use `⟨v, ?_⟩` and prove the remaining obligations. Use `eta_eq_neg_one_iff.1 hv` and compare the differences between its conclusion and the goal. Conclude with `Subsingleton.elim _ _`.
-/
theorem rat_finite_place (H : GlobalTheory.Published.QuadraticClassFieldTheory) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ), finDiag ℚ (-1) v ∉
      normGroup ℚ (QuadraticAlgebra ℚ (-1) 0) (v.adicCompletion ℚ) := by
  obtain ⟨v, hv⟩ := exists_finite_place (K := ℚ) Rat.infinitePlace Rat.isReal_infinitePlace
    (fun _ => Subsingleton.elim _ _) H
  refine ⟨v, ?_⟩
  convert eta_eq_neg_one_iff.1 hv
  exact Subsingleton.elim _ _

end GlobalTheory.QuadSymbol.Model

end
