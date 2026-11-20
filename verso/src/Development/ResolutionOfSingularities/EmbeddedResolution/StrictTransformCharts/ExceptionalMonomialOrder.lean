import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChartComputations
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ExceptionalDivisorChart
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Establish `h : closure C = C` using `hmax (closure C) hC.closure (hS.closure_subset_iff.mpr hCS) subset_closure`. Conclude with `closure_eq_iff_isClosed.mp h`.
-/
theorem isClosed_of_maximal_isIrreducible_subset {X : Scheme.{u}} {C S : Set X}
    (hC : IsIrreducible C) (hCS : C ⊆ S)
    (hmax : ∀ T : Set X, IsIrreducible T → T ⊆ S → C ⊆ T → T = C)
    (hS : IsClosed S) : IsClosed C := by
  have h : closure C = C :=
    hmax (closure C) hC.closure (hS.closure_subset_iff.mpr hCS) subset_closure
  exact closure_eq_iff_isClosed.mp h

/- English proof (translation)
Establish `hCclosed : IsClosed C` using `isClosed_of_maximal_isIrreducible_subset hC hCS hmax hS`. Take `⟨ξ, hξ⟩` from `QuasiSober.sober hC hCclosed`. Conclude with `⟨ξ, hξ⟩`.
-/
theorem exists_closure_singleton_eq_of_maximal_irreducible {X : Scheme.{u}} {C S : Set X}
    (hC : IsIrreducible C) (hCS : C ⊆ S)
    (hmax : ∀ T : Set X, IsIrreducible T → T ⊆ S → C ⊆ T → T = C)
    (hS : IsClosed S) : ∃ ξ : X, closure ({ξ} : Set X) = C := by
  have hCclosed : IsClosed C := isClosed_of_maximal_isIrreducible_subset hC hCS hmax hS
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hC hCclosed
  exact ⟨ξ, hξ⟩

/- English proof (translation)
Establish `hirr : IsIrreducible (closure ({ξ'} : Set X))` using `(isIrreducible_singleton (x := ξ')).closure`. Establish `hsub : closure ({ξ'} : Set X) ⊆ S` using `hS.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hξ')`. Establish `hCsub : C ⊆ closure ({ξ'} : Set X)`. Rewrite using `[← hξ]`. Conclude with `closure_minimal (Set.singleton_subset_iff.mpr hspec) isClosed_closure`.

Establish `heq : closure ({ξ'} : Set X) = C` using `hmax _ hirr hsub hCsub`. Establish `hcl : closure ({ξ'} : Set X) = closure ({ξ} : Set X)` using `by rw [heq, hξ]`. Conclude with `(inseparable_iff_closure_eq.mpr hcl).eq`.
-/
theorem eq_of_mem_closure_singleton_of_maximal_irreducible {X : Scheme.{u}} {C S : Set X}
    (_hC : IsIrreducible C) (_hCS : C ⊆ S)
    (hmax : ∀ T : Set X, IsIrreducible T → T ⊆ S → C ⊆ T → T = C)
    (hS : IsClosed S) {ξ ξ' : X} (hξ : closure ({ξ} : Set X) = C) (hξ' : ξ' ∈ S)
    (hspec : ξ ∈ closure ({ξ'} : Set X)) : ξ' = ξ := by
  have hirr : IsIrreducible (closure ({ξ'} : Set X)) :=
    (isIrreducible_singleton (x := ξ')).closure
  have hsub : closure ({ξ'} : Set X) ⊆ S :=
    hS.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hξ')
  have hCsub : C ⊆ closure ({ξ'} : Set X) := by
    rw [← hξ]
    exact closure_minimal (Set.singleton_subset_iff.mpr hspec) isClosed_closure
  have heq : closure ({ξ'} : Set X) = C := hmax _ hirr hsub hCsub
  have hcl : closure ({ξ'} : Set X) = closure ({ξ} : Set X) := by rw [heq, hξ]
  exact (inseparable_iff_closure_eq.mpr hcl).eq

def totalDegree {T : Type*} (f : T →₀ ℕ) : ℕ := f.sum fun _ n => n

/- English proof (translation)
Simplify using `[totalDegree]`.
-/
theorem totalDegree_zero {T : Type*} : totalDegree (0 : T →₀ ℕ) = 0 := by
  simp [totalDegree]

/- English proof (translation)
Use `show (f + g).sum (fun _ n => n) = f.sum (fun _ n => n) + g.sum (fun _ n => n)`. Conclude with `Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)`.
-/
theorem totalDegree_add {T : Type*} (f g : T →₀ ℕ) : totalDegree (f + g) = totalDegree f + totalDegree g := by
  show (f + g).sum (fun _ n => n) = f.sum (fun _ n => n) + g.sum (fun _ n => n)
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

/- English proof (translation)
Use `show (Finsupp.single t n).sum (fun _ m => m) = n`. Conclude with `Finsupp.sum_single_index rfl`.
-/
theorem totalDegree_single {T : Type*} [DecidableEq T] (t : T) (n : ℕ) :
    totalDegree (Finsupp.single t n) = n := by
  show (Finsupp.single t n).sum (fun _ m => m) = n
  exact Finsupp.sum_single_index rfl

def powProd {A : Type*} [CommRing A] {T : Type*} (x : T → A) (f : T →₀ ℕ) : A :=
  f.prod fun t n => x t ^ n

/- English proof (translation)
Simplify using `[powProd]`.
-/
theorem powProd_zero {A : Type*} [CommRing A] {T : Type*} (x : T → A) :
    powProd x (0 : T →₀ ℕ) = 1 := by
  simp [powProd]

/- English proof (translation)
Use `show (f + g).prod (fun t n => x t ^ n) = f.prod (fun t n => x t ^ n) * g.prod (fun t n => x t ^ n)`. Conclude with `Finsupp.prod_add_index' (fun a => pow_zero (x a)) (fun a b₁ b₂ => pow_add (x a) b₁ b₂)`.
-/
theorem powProd_add {A : Type*} [CommRing A] {T : Type*} (x : T → A) (f g : T →₀ ℕ) :
    powProd x (f + g) = powProd x f * powProd x g := by
  show (f + g).prod (fun t n => x t ^ n)
      = f.prod (fun t n => x t ^ n) * g.prod (fun t n => x t ^ n)
  exact Finsupp.prod_add_index' (fun a => pow_zero (x a)) (fun a b₁ b₂ => pow_add (x a) b₁ b₂)

/- English proof (translation)
Use `show (Finsupp.single t n).prod (fun t m => x t ^ m) = x t ^ n`. Conclude with `Finsupp.prod_single_index (pow_zero (x t))`.
-/
theorem powProd_single {A : Type*} [CommRing A] {T : Type*} [DecidableEq T] (x : T → A)
    (t : T) (n : ℕ) : powProd x (Finsupp.single t n) = x t ^ n := by
  show (Finsupp.single t n).prod (fun t m => x t ^ m) = x t ^ n
  exact Finsupp.prod_single_index (pow_zero (x t))

/- English proof (translation)
Simplify using `[powProd, Finsupp.prod, map_prod, map_pow]`.
-/
theorem map_powProd {A B : Type*} [CommRing A] [CommRing B] {T : Type*} (φ : A →+* B)
    (x : T → A) (f : T →₀ ℕ) : φ (powProd x f) = powProd (fun t => φ (x t)) f := by
  classical
  simp [powProd, Finsupp.prod, map_prod, map_pow]

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, pow_add]`. Conclude with `Ideal.mul_mem_mul (Ideal.pow_mem_pow (hx a) (g a)) ih`.
-/
private theorem prod_pow_mem_pow_sum {A : Type*} [CommRing A] {T : Type*}
    (x : T → A) (I : Ideal A) (hx : ∀ t : T, x t ∈ I) (g : T → ℕ) (s : Finset T) :
    (∏ t ∈ s, x t ^ g t) ∈ I ^ (∑ t ∈ s, g t) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (hx a) (g a)) ih

/- English proof (translation)
Establish `h1 : powProd x f = ∏ t ∈ f.support, x t ^ f t` using `rfl`. Establish `h2 : totalDegree f = ∑ t ∈ f.support, f t` using `rfl`. Rewrite using `[h1, h2]`. Conclude with `prod_pow_mem_pow_sum x I hx (fun t => f t) f.support`.
-/
theorem powProd_mem_pow_totalDegree {A : Type*} [CommRing A] {T : Type*} (x : T → A) (I : Ideal A)
    (hx : ∀ t : T, x t ∈ I) (f : T →₀ ℕ) : powProd x f ∈ I ^ totalDegree f := by
  have h1 : powProd x f = ∏ t ∈ f.support, x t ^ f t := rfl
  have h2 : totalDegree f = ∑ t ∈ f.support, f t := rfl
  rw [h1, h2]
  exact prod_pow_mem_pow_sum x I hx (fun t => f t) f.support

def chartMonomial {A : Type*} [CommRing A] {m : ℕ} (x : Fin m → A) (S : Finset (Fin m))
    (s : Fin m) (c : ℕ) (f : ↥(S.erase s) →₀ ℕ) : A :=
  x s ^ (c - totalDegree f) * powProd (fun t : ↥(S.erase s) => x t.1) f

/- English proof (translation)
Use `Finsupp.induction_linear f ?_ ?_ ?_` and prove the remaining obligations. Simplify using `only [powProd_zero, totalDegree_zero, pow_zero, mul_one, map_one]`. Introduce `p q hp hq`. Simplify using `only [powProd_add, totalDegree_add, map_mul, hp, hq, pow_add]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `t n`. Simplify using `only [powProd_single, totalDegree_single, map_pow, h, mul_pow]`.
-/
private theorem map_powProd_eq_powProd_mul_pow_totalDegree {A B : Type*} [CommRing A] [CommRing B]
    {T : Type*} (φ : A →+* B) (u : T → A) (v : T → B) (b : B)
    (h : ∀ t : T, φ (u t) = v t * b) (f : T →₀ ℕ) :
    φ (powProd u f) = powProd v f * b ^ totalDegree f := by
  classical
  refine Finsupp.induction_linear f ?_ ?_ ?_
  · simp only [powProd_zero, totalDegree_zero, pow_zero, mul_one, map_one]
  · intro p q hp hq
    simp only [powProd_add, totalDegree_add, map_mul, hp, hq, pow_add]
    ring
  · intro t n
    simp only [powProd_single, totalDegree_single, map_pow, h, mul_pow]

/- English proof (translation)
Establish `hfun : ∀ t : ↥(S.erase s), φ (x t.1) = y t.1 * y s`. Introduce `t`. Take `⟨hts, htS⟩` from `Finset.mem_erase.mp t.2`. Conclude with `hφ t.1 htS hts`. Establish `hmon : chartMonomial x S s c f = x s ^ (c - totalDegree f) * powProd (fun t : ↥(S.erase s) => x t.1) f` using `rfl`.

Establish `key` using `map_powProd_eq_powProd_mul_pow_totalDegree φ (fun t : ↥(S.erase s) => x t.1) (fun t : ↥(S.erase s) => y t.1) (y s) hfun f`. Rewrite using `[hmon, map_mul, map_pow, hφs, key]`. Establish `hc : y s ^ c = y s ^ (c - totalDegree f) * y s ^ totalDegree f`. Rewrite using `[← pow_add, Nat.sub_add_cancel hf]`. Rewrite using `[hc]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem map_chartMonomial {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) {m : ℕ}
    (x : Fin m → A) (y : Fin m → B) (S : Finset (Fin m)) (s : Fin m)
    (hφs : φ (x s) = y s)
    (hφ : ∀ i ∈ S, i ≠ s → φ (x i) = y i * y s)
    (c : ℕ) (f : ↥(S.erase s) →₀ ℕ) (hf : totalDegree f ≤ c) :
    φ (chartMonomial x S s c f) =
      y s ^ c * powProd (fun t : ↥(S.erase s) => y t.1) f := by
  have hfun : ∀ t : ↥(S.erase s), φ (x t.1) = y t.1 * y s := by
    intro t
    obtain ⟨hts, htS⟩ := Finset.mem_erase.mp t.2
    exact hφ t.1 htS hts
  have hmon : chartMonomial x S s c f
      = x s ^ (c - totalDegree f) * powProd (fun t : ↥(S.erase s) => x t.1) f := rfl
  have key := map_powProd_eq_powProd_mul_pow_totalDegree φ (fun t : ↥(S.erase s) => x t.1)
      (fun t : ↥(S.erase s) => y t.1) (y s) hfun f
  rw [hmon, map_mul, map_pow, hφs, key]
  have hc : y s ^ c = y s ^ (c - totalDegree f) * y s ^ totalDegree f := by
    rw [← pow_add, Nat.sub_add_cancel hf]
  rw [hc]
  ring

def chartMonomialIdeal {A : Type*} [CommRing A] {m : ℕ} (x : Fin m → A) (S : Finset (Fin m))
    (s : Fin m) (c : ℕ) : Ideal A :=
  Ideal.span {a : A | ∃ f : ↥(S.erase s) →₀ ℕ, totalDegree f ≤ c ∧ a = chartMonomial x S s c f}

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem chartMonomialIdeal_eq_span {A : Type*} [CommRing A] {m : ℕ} (x : Fin m → A)
    (S : Finset (Fin m)) (s : Fin m) (c : ℕ) :
    chartMonomialIdeal x S s c =
      Ideal.span {a : A | ∃ f : ↥(S.erase s) →₀ ℕ, totalDegree f ≤ c ∧
        a = chartMonomial x S s c f} := rfl

/- English proof (translation)
Rewrite using `[chartMonomialIdeal_eq_span x S s c]`. Conclude with `Ideal.subset_span ⟨f, hf, rfl⟩`.
-/
private theorem chartMonomial_mem_chartMonomialIdeal {A : Type*} [CommRing A] {m : ℕ}
    (x : Fin m → A) (S : Finset (Fin m)) (s : Fin m) (c : ℕ) (f : ↥(S.erase s) →₀ ℕ)
    (hf : totalDegree f ≤ c) :
    chartMonomial x S s c f ∈ chartMonomialIdeal x S s c := by
  rw [chartMonomialIdeal_eq_span x S s c]
  exact Ideal.subset_span ⟨f, hf, rfl⟩

/- English proof (translation)
Establish `h1 : c + 1 - totalDegree f = (c - totalDegree f) + 1` using `by omega`. Establish `h2 : chartMonomial x S s c f * x s = chartMonomial x S s (c + 1) f`. Simplify using `only [chartMonomial, h1, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`.

Conclude with `chartMonomial_mem_chartMonomialIdeal x S s (c + 1) f (hf.trans (Nat.le_succ c))`.
-/
private theorem chartMonomial_mul_coord_self_mem_chartMonomialIdeal_succ {A : Type*} [CommRing A] {m : ℕ} (x : Fin m → A)
    (S : Finset (Fin m)) (s : Fin m) (c : ℕ) (f : ↥(S.erase s) →₀ ℕ) (hf : totalDegree f ≤ c) :
    chartMonomial x S s c f * x s ∈ chartMonomialIdeal x S s (c + 1) := by
  have h1 : c + 1 - totalDegree f = (c - totalDegree f) + 1 := by omega
  have h2 : chartMonomial x S s c f * x s = chartMonomial x S s (c + 1) f := by
    simp only [chartMonomial, h1, pow_succ]
    ring
  rw [h2]
  exact chartMonomial_mem_chartMonomialIdeal x S s (c + 1) f (hf.trans (Nat.le_succ c))

/- English proof (translation)
Establish `hdeg : totalDegree (f + Finsupp.single t 1) = totalDegree f + 1`. Rewrite using `[totalDegree_add, totalDegree_single]`. Establish `h3 : c + 1 - (totalDegree f + 1) = c - totalDegree f` using `by omega`. Establish `h2 : chartMonomial x S s c f * x t.1 = chartMonomial x S s (c + 1) (f + Finsupp.single t 1)`. Simplify using `only [chartMonomial, hdeg, h3, powProd_add, powProd_single, pow_one]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`. Use `chartMonomial_mem_chartMonomialIdeal x S s (c + 1) (f + Finsupp.single t 1) ?_` and prove the remaining obligations. Rewrite using `[hdeg]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem chartMonomial_mul_coord_mem_chartMonomialIdeal_succ {A : Type*} [CommRing A] {m : ℕ} (x : Fin m → A)
    (S : Finset (Fin m)) (s : Fin m) (c : ℕ) (f : ↥(S.erase s) →₀ ℕ) (hf : totalDegree f ≤ c)
    (t : ↥(S.erase s)) :
    chartMonomial x S s c f * x t.1 ∈ chartMonomialIdeal x S s (c + 1) := by
  have hdeg : totalDegree (f + Finsupp.single t 1) = totalDegree f + 1 := by
    rw [totalDegree_add, totalDegree_single]
  have h3 : c + 1 - (totalDegree f + 1) = c - totalDegree f := by omega
  have h2 : chartMonomial x S s c f * x t.1
      = chartMonomial x S s (c + 1) (f + Finsupp.single t 1) := by
    simp only [chartMonomial, hdeg, h3, powProd_add, powProd_single, pow_one]
    ring
  rw [h2]
  refine chartMonomial_mem_chartMonomialIdeal x S s (c + 1) (f + Finsupp.single t 1) ?_
  rw [hdeg]
  omega

/- English proof (translation)
Establish `key : chartMonomialIdeal x S s c ≤ Submodule.comap (LinearMap.mulRight A (x i)) (chartMonomialIdeal x S s (c + 1))`. Rewrite using `[chartMonomialIdeal_eq_span x S s c]`. Use `Ideal.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `a ⟨f, hf, rfl⟩`. Simplify using `only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulRight_apply]`.

Distinguish the cases in `his : i = s`. Establish `hx : chartMonomial x S s c f * x i = chartMonomial x S s c f * x s` using `by rw [his]`. Rewrite using `[hx]`. Conclude with `chartMonomial_mul_coord_self_mem_chartMonomialIdeal_succ x S s c f hf`. Conclude with `chartMonomial_mul_coord_mem_chartMonomialIdeal_succ x S s c f hf ⟨i, Finset.mem_erase.mpr ⟨his, hi⟩⟩`.

Establish `h` using `key hr`. Rewrite `h` using `[Submodule.mem_comap, LinearMap.mulRight_apply]`. Conclude with `h`.
-/
private theorem mul_coord_mem_chartMonomialIdeal_succ {A : Type*} [CommRing A] {m : ℕ}
    (x : Fin m → A) (S : Finset (Fin m)) (s : Fin m) (c : ℕ) (i : Fin m) (hi : i ∈ S) (r : A)
    (hr : r ∈ chartMonomialIdeal x S s c) :
    r * x i ∈ chartMonomialIdeal x S s (c + 1) := by
  have key : chartMonomialIdeal x S s c ≤
      Submodule.comap (LinearMap.mulRight A (x i)) (chartMonomialIdeal x S s (c + 1)) := by
    rw [chartMonomialIdeal_eq_span x S s c]
    refine Ideal.span_le.mpr ?_
    rintro a ⟨f, hf, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulRight_apply]
    by_cases his : i = s
    · have hx : chartMonomial x S s c f * x i = chartMonomial x S s c f * x s := by rw [his]
      rw [hx]
      exact chartMonomial_mul_coord_self_mem_chartMonomialIdeal_succ x S s c f hf
    · exact chartMonomial_mul_coord_mem_chartMonomialIdeal_succ x S s c f hf ⟨i, Finset.mem_erase.mpr ⟨his, hi⟩⟩
  have h := key hr
  rw [Submodule.mem_comap, LinearMap.mulRight_apply] at h
  exact h

/- English proof (translation)
Establish `key : Ideal.span (x '' (S : Set (Fin m))) ≤ Submodule.comap (LinearMap.mulRight A r) (chartMonomialIdeal x S s (c + 1))`. Use `Ideal.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `a ⟨i, hi, rfl⟩`. Simplify using `only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulRight_apply]`. Rewrite using `[mul_comm (x i) r]`.

Conclude with `mul_coord_mem_chartMonomialIdeal_succ x S s c i (Finset.mem_coe.mp hi) r hr`. Establish `h` using `key hy`. Rewrite `h` using `[Submodule.mem_comap, LinearMap.mulRight_apply]`. Rewrite using `[mul_comm r y]`. Conclude with `h`.
-/
private theorem mul_mem_chartMonomialIdeal_succ {A : Type*} [CommRing A] {m : ℕ} (x : Fin m → A)
    (S : Finset (Fin m)) (s : Fin m) (c : ℕ) (r : A) (hr : r ∈ chartMonomialIdeal x S s c)
    (y : A) (hy : y ∈ Ideal.span (x '' (S : Set (Fin m)))) :
    r * y ∈ chartMonomialIdeal x S s (c + 1) := by
  have key : Ideal.span (x '' (S : Set (Fin m))) ≤
      Submodule.comap (LinearMap.mulRight A r) (chartMonomialIdeal x S s (c + 1)) := by
    refine Ideal.span_le.mpr ?_
    rintro a ⟨i, hi, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulRight_apply]
    rw [mul_comm (x i) r]
    exact mul_coord_mem_chartMonomialIdeal_succ x S s c i (Finset.mem_coe.mp hi) r hr
  have h := key hy
  rw [Submodule.mem_comap, LinearMap.mulRight_apply] at h
  rw [mul_comm r y]
  exact h

/- English proof (translation)
Proceed by induction on `c with`. Consider the case `zero`. Rewrite using `[pow_zero, Ideal.one_eq_top, top_le_iff, Ideal.eq_top_iff_one]`. Establish `h0 : (1 : A) = chartMonomial x S s 0 0`. Simplify using `[chartMonomial, totalDegree_zero, powProd_zero]`.

Rewrite using `[h0]`. Conclude with `chartMonomial_mem_chartMonomialIdeal x S s 0 0 totalDegree_zero.le`. Consider the case `succ c ih`. Rewrite using `[pow_succ]`. Use `Ideal.mul_le.mpr ?_` and prove the remaining obligations.

Introduce `r hr y hy`. Conclude with `mul_mem_chartMonomialIdeal_succ x S s c r (ih hr) y hy`.
-/
theorem pow_span_image_le_chartMonomialIdeal {A : Type*} [CommRing A] {m : ℕ} (x : Fin m → A)
    (S : Finset (Fin m)) (s : Fin m) (_hs : s ∈ S) (c : ℕ) :
    Ideal.span (x '' (S : Set (Fin m))) ^ c ≤ chartMonomialIdeal x S s c := by
  induction c with
  | zero =>
      rw [pow_zero, Ideal.one_eq_top, top_le_iff, Ideal.eq_top_iff_one]
      have h0 : (1 : A) = chartMonomial x S s 0 0 := by
        simp [chartMonomial, totalDegree_zero, powProd_zero]
      rw [h0]
      exact chartMonomial_mem_chartMonomialIdeal x S s 0 0 totalDegree_zero.le
  | succ c ih =>
      rw [pow_succ]
      refine Ideal.mul_le.mpr ?_
      intro r hr y hy
      exact mul_mem_chartMonomialIdeal_succ x S s c r (ih hr) y hy

/- English proof (translation)
Rewrite using `[MvPolynomial.ker_map, Ideal.mk_ker]`.
-/
private theorem map_C_eq_ker_map_quotientMk {R : Type*} [CommRing R] (P : Ideal R)
    (σ : Type*) :
    Ideal.map (MvPolynomial.C : R →+* MvPolynomial σ R) P =
      RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk P) :
        MvPolynomial σ R →+* MvPolynomial σ (R ⧸ P)) := by
  rw [MvPolynomial.ker_map, Ideal.mk_ker]

/- English proof (translation)
Establish `hdom : IsDomain (R ⧸ P)` using `inferInstance`. Establish `hdom2 : IsDomain (MvPolynomial σ (R ⧸ P))` using `inferInstance`. Rewrite using `[map_C_eq_ker_map_quotientMk P σ]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.ne_top_iff_one]`.

Introduce `hmem`. Establish `h1 : (MvPolynomial.map (Ideal.Quotient.mk P) : MvPolynomial σ R →+* MvPolynomial σ (R ⧸ P)) 1 = 0` using `RingHom.mem_ker.mp hmem`. Rewrite `h1` using `[map_one]`. Establish `h2` using `congrArg (fun f : MvPolynomial σ (R ⧸ P) => MvPolynomial.constantCoeff f) h1`. Simplify using `only [map_one, map_zero] at h2`.

Conclude with `one_ne_zero h2`. Introduce `x y hxy`. Rewrite `hxy` using `[RingHom.mem_ker, map_mul]`. Break down `mul_eq_zero.mp hxy with h | h` into its components or cases. Conclude with `Or.inl (RingHom.mem_ker.mpr h)`.

Conclude with `Or.inr (RingHom.mem_ker.mpr h)`.
-/
theorem isPrime_map_C {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] (σ : Type*) :
    (Ideal.map (MvPolynomial.C : R →+* MvPolynomial σ R) P).IsPrime := by
  have hdom : IsDomain (R ⧸ P) := inferInstance
  have hdom2 : IsDomain (MvPolynomial σ (R ⧸ P)) := inferInstance
  rw [map_C_eq_ker_map_quotientMk P σ]
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one]
    intro hmem
    have h1 : (MvPolynomial.map (Ideal.Quotient.mk P) :
        MvPolynomial σ R →+* MvPolynomial σ (R ⧸ P)) 1 = 0 := RingHom.mem_ker.mp hmem
    rw [map_one] at h1
    have h2 := congrArg (fun f : MvPolynomial σ (R ⧸ P) => MvPolynomial.constantCoeff f) h1
    simp only [map_one, map_zero] at h2
    exact one_ne_zero h2
  · intro x y hxy
    rw [RingHom.mem_ker, map_mul] at hxy
    rcases mul_eq_zero.mp hxy with h | h
    · exact Or.inl (RingHom.mem_ker.mpr h)
    · exact Or.inr (RingHom.mem_ker.mpr h)

/- English proof (translation)
Establish `hq : (Ideal.comap (MvPolynomial.C : R →+* MvPolynomial σ R) Pp).IsPrime` using `Ideal.comap_isPrime (MvPolynomial.C : R →+* MvPolynomial σ R) Pp`. Establish `hle : Ideal.map (MvPolynomial.C : R →+* MvPolynomial σ R) (Ideal.comap (MvPolynomial.C : R →+* MvPolynomial σ R) Pp) ≤ Pp` using `Ideal.map_le_iff_le_comap.mpr le_rfl`. Establish `hge` using `hmin _ (isPrime_map_C (Ideal.comap (MvPolynomial.C : R →+* MvPolynomial σ R) Pp) σ) hle`. Conclude with `Ideal.mem_comap.mp ((MvPolynomial.mem_map_C_iff.mp (hge hp)) d)`.
-/
private theorem C_coeff_mem_of_minimal_prime {R : Type*} [CommRing R] {σ : Type*}
    (Pp : Ideal (MvPolynomial σ R)) [Pp.IsPrime]
    (hmin : ∀ K : Ideal (MvPolynomial σ R), K.IsPrime → K ≤ Pp → Pp ≤ K)
    {p : MvPolynomial σ R} (hp : p ∈ Pp) (d : σ →₀ ℕ) :
    MvPolynomial.C (MvPolynomial.coeff d p) ∈ Pp := by
  have hq : (Ideal.comap (MvPolynomial.C : R →+* MvPolynomial σ R) Pp).IsPrime :=
    Ideal.comap_isPrime (MvPolynomial.C : R →+* MvPolynomial σ R) Pp
  have hle : Ideal.map (MvPolynomial.C : R →+* MvPolynomial σ R)
      (Ideal.comap (MvPolynomial.C : R →+* MvPolynomial σ R) Pp) ≤ Pp :=
    Ideal.map_le_iff_le_comap.mpr le_rfl
  have hge := hmin _
    (isPrime_map_C (Ideal.comap (MvPolynomial.C : R →+* MvPolynomial σ R) Pp) σ) hle
  exact Ideal.mem_comap.mp ((MvPolynomial.mem_map_C_iff.mp (hge hp)) d)

/- English proof (translation)
The claim follows from `MvPolynomial.monomial_eq.symm`.
-/
private theorem C_mul_powProd_X_eq_monomial {R : Type*} [CommRing R] {σ : Type*}
    (f : σ →₀ ℕ) (r : R) :
    MvPolynomial.C r * powProd (fun t : σ => (MvPolynomial.X t : MvPolynomial σ R)) f
      = MvPolynomial.monomial f r :=
  MvPolynomial.monomial_eq.symm

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨Ψ, hΨsurj, hΨ⟩ : ∃ Ψ : B →+* MvPolynomial ↥(S.erase s) (A ⧸ Ideal.span (x '' (S : Set (Fin m)))), Function.Surjective Ψ ∧ ∀ b : B, Ψ b = e (Ideal.Quotient.mk (Ideal.span {y s}) b) := by`. Use `⟨e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {y s})), ?_, ?_⟩` and prove the remaining obligations. Introduce `q`. Take `⟨z, hz⟩` from `e.surjective q`. Take `⟨b, hb⟩` from `Ideal.Quotient.mk_surjective z`.

Use `⟨b, ?_⟩` and prove the remaining obligations. Use `show e (Ideal.Quotient.mk (Ideal.span {y s}) b) = q`. Rewrite using `[hb, hz]`. Introduce `b`. Simplify using the standard rewrite rules.

Establish `hΨ0 : Ψ (y s) = 0`. Rewrite using `[hΨ, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (y s)), map_zero]`. Establish `hΨC : ∀ a : A, Ψ (φ a) = MvPolynomial.C (Ideal.Quotient.mk (Ideal.span (x '' (S : Set (Fin m)))) a)`. Introduce `a`. Rewrite using `[hΨ]`.

Conclude with `heC a`. Establish `hΨX : ∀ t : ↥(S.erase s), Ψ (y t.1) = MvPolynomial.X t`. Introduce `t`. Rewrite using `[hΨ]`. Conclude with `heX t`.

Establish `hfun : (fun t : ↥(S.erase s) => Ψ (y t.1)) = fun t : ↥(S.erase s) => (MvPolynomial.X t : MvPolynomial ↥(S.erase s) (A ⧸ Ideal.span (x '' (S : Set (Fin m)))))` using `funext hΨX`. Establish `hkerP : RingHom.ker Ψ ≤ P`. Introduce `b hb`. Establish `hb0 : Ψ b = 0` using `RingHom.mem_ker.mp hb`. Rewrite `hb0` using `[hΨ]`.

Establish `hb1 : (Ideal.Quotient.mk (Ideal.span {y s})) b = 0`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[hb0, map_zero]`. Conclude with `Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hyP) (Ideal.Quotient.eq_zero_iff_mem.mp hb1)`. Establish `hcomapP : Ideal.comap Ψ (Ideal.map Ψ P) ≤ P`.

Introduce `b hb`. Take `⟨p0, hp0P, hp0b⟩` from `(Ideal.mem_map_iff_of_surjective Ψ hΨsurj).mp (Ideal.mem_comap.mp hb)`. Establish `hkb : b - p0 ∈ RingHom.ker Ψ`. Rewrite using `[RingHom.mem_ker, map_sub, hp0b, sub_self]`. Establish `hsum2 : (b - p0) + p0 ∈ P` using `P.add_mem (hkerP hkb) hp0P`.

Simplify using `using hsum2`. Establish `hPprime : (Ideal.map Ψ P).IsPrime`. Prove the components needed by the constructor for the conclusion. Introduce `htop`. Establish `h1 : (1 : MvPolynomial ↥(S.erase s) (A ⧸ Ideal.span (x '' (S : Set (Fin m))))) ∈ Ideal.map Ψ P`.

Rewrite using `[htop]`. Conclude with `Submodule.mem_top`. Establish `h2 : (1 : B) ∈ Ideal.comap Ψ (Ideal.map Ψ P)`. Rewrite using `[Ideal.mem_comap, map_one]`. Conclude with `h1`.

Establish `hPtop : P = ⊤`. Rewrite using `[Ideal.eq_top_iff_one]`. Conclude with `hcomapP h2`. Conclude with `Ideal.IsPrime.ne_top ‹P.IsPrime› hPtop`. Introduce `p q hpq`.

Take `⟨b, rfl⟩` from `hΨsurj p`. Take `⟨b', rfl⟩` from `hΨsurj q`. Establish `hb : b * b' ∈ P`. Apply `hcomapP` to reduce the goal to its premises. Rewrite using `[Ideal.mem_comap, map_mul]`.

Conclude with `hpq`. Break down `Ideal.IsPrime.mem_or_mem ‹P.IsPrime› hb with h | h` into its components or cases. Conclude with `Or.inl (Ideal.mem_map_of_mem Ψ h)`. Conclude with `Or.inr (Ideal.mem_map_of_mem Ψ h)`. Establish `hmin : ∀ K : Ideal (MvPolynomial ↥(S.erase s) (A ⧸ Ideal.span (x '' (S : Set (Fin m))))), K.IsPrime → K ≤ Ideal.map Ψ P → Ideal.map Ψ P ≤ K`.

Introduce `K hK hle`. Use `hK` as an intermediate fact. Establish `h2 : Ideal.comap Ψ K ≤ P` using `le_trans (Ideal.comap_mono hle) hcomapP`. Establish `h3 : y s ∈ Ideal.comap Ψ K`. Rewrite using `[Ideal.mem_comap, hΨ0]`.

Conclude with `K.zero_mem`. Establish `h4` using `hPmin (Ideal.comap Ψ K) (Ideal.comap_isPrime Ψ K) h2 h3`. Conclude with `le_trans (Ideal.map_mono h4) (Ideal.map_le_iff_le_comap.mpr le_rfl)`. Establish `hxQ : ∀ i ∈ S, x i ∈ Ideal.comap φ P`. Introduce `i hi`.

Rewrite using `[Ideal.mem_comap]`. Distinguish the cases in `h : i = s`. Rewrite using `[h, hφs]`. Conclude with `hyP`. Rewrite using `[hφ i hi h]`.

Conclude with `Ideal.mul_mem_left _ _ hyP`. Establish `hmonQ : ∀ f : ↥(S.erase s) →₀ ℕ, totalDegree f ≤ c → chartMonomial x S s c f ∈ Ideal.comap φ P ^ c`. Introduce `f hf`. Establish `h1 : x s ^ (c - totalDegree f) ∈ Ideal.comap φ P ^ (c - totalDegree f)` using `Ideal.pow_mem_pow (hxQ s hs) _`. Establish `h2 : powProd (fun t : ↥(S.erase s) => x t.1) f ∈ Ideal.comap φ P ^ totalDegree f` using `powProd_mem_pow_totalDegree (fun t : ↥(S.erase s) => x t.1) (Ideal.comap φ P) (fun t => hxQ t.1 (Finset.mem_of_mem_erase t.2)) f`.

Establish `h3` using `Ideal.mul_mem_mul h1 h2`. Rewrite `h3` using `[← pow_add, Nat.sub_add_cancel hf]`. Conclude with `h3`. Introduce `a ha`. Establish `haM : a ∈ chartMonomialIdeal x S s c` using `pow_span_image_le_chartMonomialIdeal x S s hs c (hJ ha)`.

Establish `haspan : a ∈ Submodule.span A {b : A | ∃ f : ↥(S.erase s) →₀ ℕ, totalDegree f ≤ c ∧ b = chartMonomial x S s c f}` using `haM`. Take `⟨cf, hcfsupp, hcfsum⟩` from `Submodule.mem_span_set.mp haspan`. Establish `hex : ∀ g ∈ cf.support, ∃ f : ↥(S.erase s) →₀ ℕ, totalDegree f ≤ c ∧ g = chartMonomial x S s c f`. Introduce `g hg`. Conclude with `hcfsupp (Finset.mem_coe.mpr hg)`.

Use `choose! fsel hfdeg hfeq using hex`. Establish `hinj : ∀ g ∈ cf.support, ∀ g' ∈ cf.support, fsel g = fsel g' → g = g'`. Introduce `g hg g' hg' hgg`. Establish `e1` using `hfeq g hg`. Rewrite `e1` using `[hgg]`.

Conclude with `e1.trans (hfeq g' hg').symm`. Establish `hsum : a = ∑ i ∈ cf.support, cf i * i`. Rewrite using `[← hcfsum]`. Simplify using `[Finsupp.sum, smul_eq_mul]`. Establish `ha' : a = ∑ i ∈ cf.support, cf i * chartMonomial x S s c (fsel i)`.

Rewrite using `[hsum]`. Use `Finset.sum_congr rfl ?_` and prove the remaining obligations. Introduce `i hi`. Rewrite using `[← hfeq i hi]`. Establish `hφa : φ a = y s ^ c * ∑ i ∈ cf.support, φ (cf i) * powProd (fun t : ↥(S.erase s) => y t.1) (fsel i)`.

Rewrite using `[ha', map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl ?_` and prove the remaining obligations. Introduce `i hi`. Rewrite using `[map_mul, map_chartMonomial φ x y S s hφs hφ c (fsel i) (hfdeg i hi)]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hmemJ' : φ a ∈ Ideal.span {y s ^ c} * J'` using `hmap (Ideal.mem_map_of_mem φ ha)`. Take `⟨j, hjJ', hjeq⟩` from `Ideal.mem_span_singleton_mul.mp hmemJ'`. Establish `hueq : (∑ i ∈ cf.support, φ (cf i) * powProd (fun t : ↥(S.erase s) => y t.1) (fsel i)) = j`. Use `(mul_cancel_left_mem_nonZeroDivisors (pow_mem hy c)).mp ?_` and prove the remaining obligations. Rewrite using `[← hφa]`.

Conclude with `hjeq.symm`. Establish `huP : (∑ i ∈ cf.support, φ (cf i) * powProd (fun t : ↥(S.erase s) => y t.1) (fsel i)) ∈ P`. Rewrite using `[hueq]`. Conclude with `hJ'P hjJ'`. Establish `hΨu : Ψ (∑ i ∈ cf.support, φ (cf i) * powProd (fun t : ↥(S.erase s) => y t.1) (fsel i)) = ∑ i ∈ cf.support, MvPolynomial.monomial (fsel i) (Ideal.Quotient.mk (Ideal.span (x '' (S : Set (Fin m)))) (cf i))`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl ?_` and prove the remaining obligations. Introduce `i _`. Rewrite using `[map_mul, hΨC, map_powProd, hfun]`. Conclude with `C_mul_powProd_X_eq_monomial (fsel i) _`.

Establish `hcoeff : ∀ g₀ ∈ cf.support, MvPolynomial.coeff (fsel g₀) (∑ i ∈ cf.support, MvPolynomial.monomial (fsel i) (Ideal.Quotient.mk (Ideal.span (x '' (S : Set (Fin m)))) (cf i))) = Ideal.Quotient.mk (Ideal.span (x '' (S : Set (Fin m)))) (cf g₀)`. Introduce `g₀ hg₀`. Establish `hstep : ∀ g ∈ cf.support, g ≠ g₀ → MvPolynomial.coeff (fsel g₀) (MvPolynomial.monomial (fsel g) (Ideal.Quotient.mk (Ideal.span (x '' (S : Set (Fin m)))) (cf g))) = 0`. Introduce `g hg hne`. Establish `hne' : fsel g ≠ fsel g₀` using `fun hh => hne (hinj g hg g₀ hg₀ hh)`.

Rewrite using `[MvPolynomial.coeff_monomial, if_neg hne']`. Rewrite using `[MvPolynomial.coeff_sum, Finset.sum_eq_single_of_mem g₀ hg₀ hstep, MvPolynomial.coeff_monomial]`. Simplify using the standard rewrite rules. Establish `hcfQ : ∀ g ∈ cf.support, cf g ∈ Ideal.comap φ P`. Introduce `g hg`.

Establish `h1 : Ψ (∑ i ∈ cf.support, φ (cf i) * powProd (fun t : ↥(S.erase s) => y t.1) (fsel i)) ∈ Ideal.map Ψ P` using `Ideal.mem_map_of_mem Ψ huP`. Rewrite `h1` using `[hΨu]`. Establish `h2` using `C_coeff_mem_of_minimal_prime (Ideal.map Ψ P) hmin h1 (fsel g)`. Rewrite `h2` using `[hcoeff g hg]`. Establish `h3 : Ψ (φ (cf g)) ∈ Ideal.map Ψ P`.

Rewrite using `[hΨC]`. Conclude with `h2`. Conclude with `Ideal.mem_comap.mpr (hcomapP (Ideal.mem_comap.mpr h3))`. Rewrite using `[ha']`. Use `Ideal.sum_mem _ ?_` and prove the remaining obligations.

Introduce `i hi`. Establish `h3 : (Ideal.comap φ P) ^ (c + 1) = (Ideal.comap φ P) * (Ideal.comap φ P) ^ c`. Rewrite using `[pow_succ, mul_comm]`. Rewrite using `[h3]`. Conclude with `Ideal.mul_mem_mul (hcfQ i hi) (hmonQ (fsel i) (hfdeg i hi))`.
-/
theorem ideal_le_comap_pow_succ_of_map_le_span_pow_mul {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    {m : ℕ} (x : Fin m → A) (y : Fin m → B) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S)
    (hφs : φ (x s) = y s)
    (hφ : ∀ i ∈ S, i ≠ s → φ (x i) = y i * y s)
    (hy : y s ∈ nonZeroDivisors B)
    (e : (B ⧸ Ideal.span {y s}) ≃+*
      MvPolynomial ↥(S.erase s) (A ⧸ Ideal.span (x '' (S : Set (Fin m)))))
    (heC : ∀ a : A, e (Ideal.Quotient.mk (Ideal.span {y s}) (φ a)) =
      MvPolynomial.C (Ideal.Quotient.mk (Ideal.span (x '' (S : Set (Fin m)))) a))
    (heX : ∀ t : ↥(S.erase s),
      e (Ideal.Quotient.mk (Ideal.span {y s}) (y t.1)) = MvPolynomial.X t)
    (P : Ideal B) [P.IsPrime] (hyP : y s ∈ P)
    (hPmin : ∀ Q : Ideal B, Q.IsPrime → Q ≤ P → y s ∈ Q → P ≤ Q)
    (c : ℕ) (J : Ideal A) (hJ : J ≤ Ideal.span (x '' (S : Set (Fin m))) ^ c)
    (J' : Ideal B) (hJ'P : J' ≤ P)
    (hmap : Ideal.map φ J ≤ Ideal.span {y s ^ c} * J') :
    J ≤ Ideal.comap φ P ^ (c + 1) := by
  classical
  obtain ⟨Ψ, hΨsurj, hΨ⟩ :
      ∃ Ψ : B →+* MvPolynomial ↥(S.erase s) (A ⧸ Ideal.span (x '' (S : Set (Fin m)))),
        Function.Surjective Ψ ∧
          ∀ b : B, Ψ b = e (Ideal.Quotient.mk (Ideal.span {y s}) b) := by
    refine ⟨e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {y s})), ?_, ?_⟩
    · intro q
      obtain ⟨z, hz⟩ := e.surjective q
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective z
      refine ⟨b, ?_⟩
      show e (Ideal.Quotient.mk (Ideal.span {y s}) b) = q
      rw [hb, hz]
    · intro b
      simp
  have hΨ0 : Ψ (y s) = 0 := by
    rw [hΨ, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (y s)), map_zero]
  have hΨC : ∀ a : A, Ψ (φ a)
      = MvPolynomial.C (Ideal.Quotient.mk (Ideal.span (x '' (S : Set (Fin m)))) a) := by
    intro a
    rw [hΨ]
    exact heC a
  have hΨX : ∀ t : ↥(S.erase s), Ψ (y t.1) = MvPolynomial.X t := by
    intro t
    rw [hΨ]
    exact heX t
  have hfun : (fun t : ↥(S.erase s) => Ψ (y t.1))
      = fun t : ↥(S.erase s) => (MvPolynomial.X t :
        MvPolynomial ↥(S.erase s) (A ⧸ Ideal.span (x '' (S : Set (Fin m))))) := funext hΨX
  have hkerP : RingHom.ker Ψ ≤ P := by
    intro b hb
    have hb0 : Ψ b = 0 := RingHom.mem_ker.mp hb
    rw [hΨ] at hb0
    have hb1 : (Ideal.Quotient.mk (Ideal.span {y s})) b = 0 := by
      apply e.injective
      rw [hb0, map_zero]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hyP)
      (Ideal.Quotient.eq_zero_iff_mem.mp hb1)
  have hcomapP : Ideal.comap Ψ (Ideal.map Ψ P) ≤ P := by
    intro b hb
    obtain ⟨p0, hp0P, hp0b⟩ :=
      (Ideal.mem_map_iff_of_surjective Ψ hΨsurj).mp (Ideal.mem_comap.mp hb)
    have hkb : b - p0 ∈ RingHom.ker Ψ := by
      rw [RingHom.mem_ker, map_sub, hp0b, sub_self]
    have hsum2 : (b - p0) + p0 ∈ P := P.add_mem (hkerP hkb) hp0P
    simpa using hsum2
  have hPprime : (Ideal.map Ψ P).IsPrime := by
    constructor
    · intro htop
      have h1 : (1 : MvPolynomial ↥(S.erase s) (A ⧸ Ideal.span (x '' (S : Set (Fin m)))))
          ∈ Ideal.map Ψ P := by
        rw [htop]
        exact Submodule.mem_top
      have h2 : (1 : B) ∈ Ideal.comap Ψ (Ideal.map Ψ P) := by
        rw [Ideal.mem_comap, map_one]
        exact h1
      have hPtop : P = ⊤ := by
        rw [Ideal.eq_top_iff_one]
        exact hcomapP h2
      exact Ideal.IsPrime.ne_top ‹P.IsPrime› hPtop
    · intro p q hpq
      obtain ⟨b, rfl⟩ := hΨsurj p
      obtain ⟨b', rfl⟩ := hΨsurj q
      have hb : b * b' ∈ P := by
        apply hcomapP
        rw [Ideal.mem_comap, map_mul]
        exact hpq
      rcases Ideal.IsPrime.mem_or_mem ‹P.IsPrime› hb with h | h
      · exact Or.inl (Ideal.mem_map_of_mem Ψ h)
      · exact Or.inr (Ideal.mem_map_of_mem Ψ h)
  have hmin : ∀ K : Ideal (MvPolynomial ↥(S.erase s)
      (A ⧸ Ideal.span (x '' (S : Set (Fin m))))),
      K.IsPrime → K ≤ Ideal.map Ψ P → Ideal.map Ψ P ≤ K := by
    intro K hK hle
    have := hK
    have h2 : Ideal.comap Ψ K ≤ P := le_trans (Ideal.comap_mono hle) hcomapP
    have h3 : y s ∈ Ideal.comap Ψ K := by
      rw [Ideal.mem_comap, hΨ0]
      exact K.zero_mem
    have h4 := hPmin (Ideal.comap Ψ K) (Ideal.comap_isPrime Ψ K) h2 h3
    exact le_trans (Ideal.map_mono h4) (Ideal.map_le_iff_le_comap.mpr le_rfl)
  have hxQ : ∀ i ∈ S, x i ∈ Ideal.comap φ P := by
    intro i hi
    rw [Ideal.mem_comap]
    by_cases h : i = s
    · rw [h, hφs]
      exact hyP
    · rw [hφ i hi h]
      exact Ideal.mul_mem_left _ _ hyP
  have hmonQ : ∀ f : ↥(S.erase s) →₀ ℕ, totalDegree f ≤ c →
      chartMonomial x S s c f ∈ Ideal.comap φ P ^ c := by
    intro f hf
    have h1 : x s ^ (c - totalDegree f) ∈ Ideal.comap φ P ^ (c - totalDegree f) :=
      Ideal.pow_mem_pow (hxQ s hs) _
    have h2 : powProd (fun t : ↥(S.erase s) => x t.1) f ∈ Ideal.comap φ P ^ totalDegree f :=
      powProd_mem_pow_totalDegree (fun t : ↥(S.erase s) => x t.1) (Ideal.comap φ P)
        (fun t => hxQ t.1 (Finset.mem_of_mem_erase t.2)) f
    have h3 := Ideal.mul_mem_mul h1 h2
    rw [← pow_add, Nat.sub_add_cancel hf] at h3
    exact h3
  intro a ha
  have haM : a ∈ chartMonomialIdeal x S s c :=
    pow_span_image_le_chartMonomialIdeal x S s hs c (hJ ha)
  have haspan : a ∈ Submodule.span A
      {b : A | ∃ f : ↥(S.erase s) →₀ ℕ, totalDegree f ≤ c ∧ b = chartMonomial x S s c f} := haM
  obtain ⟨cf, hcfsupp, hcfsum⟩ := Submodule.mem_span_set.mp haspan
  have hex : ∀ g ∈ cf.support, ∃ f : ↥(S.erase s) →₀ ℕ,
      totalDegree f ≤ c ∧ g = chartMonomial x S s c f := by
    intro g hg
    exact hcfsupp (Finset.mem_coe.mpr hg)
  choose! fsel hfdeg hfeq using hex
  have hinj : ∀ g ∈ cf.support, ∀ g' ∈ cf.support, fsel g = fsel g' → g = g' := by
    intro g hg g' hg' hgg
    have e1 := hfeq g hg
    rw [hgg] at e1
    exact e1.trans (hfeq g' hg').symm
  have hsum : a = ∑ i ∈ cf.support, cf i * i := by
    rw [← hcfsum]
    simp [Finsupp.sum, smul_eq_mul]
  have ha' : a = ∑ i ∈ cf.support, cf i * chartMonomial x S s c (fsel i) := by
    rw [hsum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [← hfeq i hi]
  have hφa : φ a = y s ^ c *
      ∑ i ∈ cf.support, φ (cf i) * powProd (fun t : ↥(S.erase s) => y t.1) (fsel i) := by
    rw [ha', map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [map_mul, map_chartMonomial φ x y S s hφs hφ c (fsel i) (hfdeg i hi)]
    ring
  have hmemJ' : φ a ∈ Ideal.span {y s ^ c} * J' := hmap (Ideal.mem_map_of_mem φ ha)
  obtain ⟨j, hjJ', hjeq⟩ := Ideal.mem_span_singleton_mul.mp hmemJ'
  have hueq : (∑ i ∈ cf.support, φ (cf i) *
      powProd (fun t : ↥(S.erase s) => y t.1) (fsel i)) = j := by
    refine (mul_cancel_left_mem_nonZeroDivisors (pow_mem hy c)).mp ?_
    rw [← hφa]
    exact hjeq.symm
  have huP : (∑ i ∈ cf.support, φ (cf i) *
      powProd (fun t : ↥(S.erase s) => y t.1) (fsel i)) ∈ P := by
    rw [hueq]
    exact hJ'P hjJ'
  have hΨu : Ψ (∑ i ∈ cf.support, φ (cf i) *
        powProd (fun t : ↥(S.erase s) => y t.1) (fsel i))
      = ∑ i ∈ cf.support, MvPolynomial.monomial (fsel i)
          (Ideal.Quotient.mk (Ideal.span (x '' (S : Set (Fin m)))) (cf i)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [map_mul, hΨC, map_powProd, hfun]
    exact C_mul_powProd_X_eq_monomial (fsel i) _
  have hcoeff : ∀ g₀ ∈ cf.support,
      MvPolynomial.coeff (fsel g₀)
          (∑ i ∈ cf.support, MvPolynomial.monomial (fsel i)
            (Ideal.Quotient.mk (Ideal.span (x '' (S : Set (Fin m)))) (cf i)))
        = Ideal.Quotient.mk (Ideal.span (x '' (S : Set (Fin m)))) (cf g₀) := by
    intro g₀ hg₀
    have hstep : ∀ g ∈ cf.support, g ≠ g₀ →
        MvPolynomial.coeff (fsel g₀) (MvPolynomial.monomial (fsel g)
          (Ideal.Quotient.mk (Ideal.span (x '' (S : Set (Fin m)))) (cf g))) = 0 := by
      intro g hg hne
      have hne' : fsel g ≠ fsel g₀ := fun hh => hne (hinj g hg g₀ hg₀ hh)
      rw [MvPolynomial.coeff_monomial, if_neg hne']
    rw [MvPolynomial.coeff_sum, Finset.sum_eq_single_of_mem g₀ hg₀ hstep,
      MvPolynomial.coeff_monomial]
    simp
  have hcfQ : ∀ g ∈ cf.support, cf g ∈ Ideal.comap φ P := by
    intro g hg
    have h1 : Ψ (∑ i ∈ cf.support, φ (cf i) *
        powProd (fun t : ↥(S.erase s) => y t.1) (fsel i)) ∈ Ideal.map Ψ P :=
      Ideal.mem_map_of_mem Ψ huP
    rw [hΨu] at h1
    have h2 := C_coeff_mem_of_minimal_prime (Ideal.map Ψ P) hmin h1 (fsel g)
    rw [hcoeff g hg] at h2
    have h3 : Ψ (φ (cf g)) ∈ Ideal.map Ψ P := by
      rw [hΨC]
      exact h2
    exact Ideal.mem_comap.mpr (hcomapP (Ideal.mem_comap.mpr h3))
  rw [ha']
  refine Ideal.sum_mem _ ?_
  intro i hi
  have h3 : (Ideal.comap φ P) ^ (c + 1)
      = (Ideal.comap φ P) * (Ideal.comap φ P) ^ c := by
    rw [pow_succ, mul_comm]
  rw [h3]
  exact Ideal.mul_mem_mul (hcfQ i hi) (hmonQ (fsel i) (hfdeg i hi))

/- English proof (translation)
Use `hU.isLocalization_stalk x` as an intermediate fact. Use `Ideal.map_le_iff_le_comap.mpr fun a ha => ?_` and prove the remaining obligations. Rewrite using `[Ideal.mem_comap]`. Conclude with `(IsLocalization.AtPrime.to_map_mem_maximal_iff _ (hU.primeIdealOf x).asIdeal a).mpr ha`.
-/
private theorem map_germ_primeIdealOf_le_maximalIdeal {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (x : ↥U) :
    Ideal.map (CommRingCat.Hom.hom (X.presheaf.germ U x.1 x.2)) (hU.primeIdealOf x).asIdeal
      ≤ IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x.1) := by
  have := hU.isLocalization_stalk x
  refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
  rw [Ideal.mem_comap]
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ (hU.primeIdealOf x).asIdeal a).mpr ha

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `ideal_le_primeIdealOf I hU x.2 hx`. Introduce `hx`. Rewrite using `[mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_eq_map_germ I (x : X) ⟨U, hU⟩ x.2]`.

Conclude with `le_trans (Ideal.map_mono hx) (map_germ_primeIdealOf_le_maximalIdeal hU x)`.
-/
private theorem mem_support_iff_ideal_le_primeIdealOf {X : Scheme.{u}} (I : X.IdealSheafData)
    {U : X.Opens} (hU : IsAffineOpen U) (x : ↥U) :
    (x : X) ∈ I.support ↔ I.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf x).asIdeal := by
  constructor
  · intro hx
    exact ideal_le_primeIdealOf I hU x.2 hx
  · intro hx
    rw [mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_eq_map_germ I (x : X) ⟨U, hU⟩ x.2]
    exact le_trans (Ideal.map_mono hx) (map_germ_primeIdealOf_le_maximalIdeal hU x)

/- English proof (translation)
Rewrite using `[le_orderAt_iff, stalkIdeal_eq_map_germ J (x : X) ⟨U, hU⟩ x.2]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem le_orderAt_of_ideal_le_pow {X : Scheme.{u}} (J : X.IdealSheafData) {U : X.Opens}
    (hU : IsAffineOpen U) (x : ↥U) (n : ℕ)
    (h : J.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf x).asIdeal ^ n) :
    ((n : ℕ) : ℕ∞) ≤ orderAt J (x : X) := by
  rw [le_orderAt_iff, stalkIdeal_eq_map_germ J (x : X) ⟨U, hU⟩ x.2]
  calc Ideal.map (CommRingCat.Hom.hom (X.presheaf.germ U x.1 x.2)) (J.ideal ⟨U, hU⟩)
      ≤ Ideal.map (CommRingCat.Hom.hom (X.presheaf.germ U x.1 x.2))
          ((hU.primeIdealOf x).asIdeal ^ n) := Ideal.map_mono h
    _ = (Ideal.map (CommRingCat.Hom.hom (X.presheaf.germ U x.1 x.2))
          (hU.primeIdealOf x).asIdeal) ^ n := Ideal.map_pow _ _ _
    _ ≤ IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x.1) ^ n :=
        Ideal.pow_right_mono (map_germ_primeIdealOf_le_maximalIdeal hU x) n

/- English proof (translation)
Use `⟨hU.isoSpec.inv.base q, ?_⟩` and prove the remaining obligations. Establish `h0` using `congrArg (fun f : Spec Γ(X, U) ⟶ Spec Γ(X, U) => f.base q) hU.isoSpec.inv_hom_id`. Conclude with `h0`.
-/
private theorem exists_primeIdealOf_eq {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (q : PrimeSpectrum Γ(X, U)) :
    ∃ y : ↥U, hU.primeIdealOf y = q := by
  refine ⟨hU.isoSpec.inv.base q, ?_⟩
  have h0 := congrArg (fun f : Spec Γ(X, U) ⟶ Spec Γ(X, U) => f.base q) hU.isoSpec.inv_hom_id
  exact h0

/- English proof (translation)
Introduce `hCJ'`. Establish `hZsm : AlgebraicGeometry.Smooth (Z.subschemeι ≫ p)` using `smooth_subschemeι_comp_of_hasStrictNormalCrossingsWith Z E hE`. Establish `hclosed : IsClosed ((Blowup.exceptionalIdeal π Z).support : Set X₁)` using `(Blowup.exceptionalIdeal π Z).support.2`. Take `⟨ξ, hξ⟩` from `exists_closure_singleton_eq_of_maximal_irreducible hCirr hCsub hCmax hclosed`. Establish `hξC : ξ ∈ C`.

Rewrite using `[← hξ]`. Conclude with `subset_closure rfl`. Establish `hξE : ξ ∈ (Blowup.exceptionalIdeal π Z).support` using `hCsub hξC`. Establish `hξJ : ξ ∈ J'.support` using `hCJ' hξC`. Establish `hzZ : π.base ξ ∈ Z.support`.

Establish `h1 : ξ ∈ (Z.comap π).support`. Rewrite using `[← Blowup.exceptionalIdeal_eq_comap π Z]`. Conclude with `hξE`. Rewrite `h1` using `[AlgebraicGeometry.Scheme.IdealSheafData.support_comap]`. Conclude with `h1`.

Take `⟨U, hU, m, cc, S, hzU, hspan⟩` from `exists_chart_ideal_eq_span_coord p Z (π.base ξ) hzZ`. Establish `hZU : restrictIdeal Z U = cc.coordIdeal S` using `restrictIdeal_eq_coordIdeal_of_ideal_eq_span hU cc Z S hspan`. Establish `hξU : ξ ∈ (TopologicalSpace.Opens.map π.base).obj U` using `hzU`. Take `⟨s, hs, hξV⟩` from `exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π cc S hπ hZU ξ hξU`. Use `set B := blowupChartOfIsBlowup π cc S hπ hZU s hs with hBdef`.

Establish `hV : IsAffineOpen B.domain` using `isAffineOpen_blowupChart_domain hU hπ hZU hs`. Use `set φ := (π.appLE U B.domain B.domain_le).hom with hφdef`. Use `set P : Ideal Γ(X₁, B.domain) := (hV.primeIdealOf ⟨ξ, hξV⟩).asIdeal with hPdef`. Establish `hPprime : P.IsPrime` using `(hV.primeIdealOf ⟨ξ, hξV⟩).isPrime`. Establish `hexcid : (Blowup.exceptionalIdeal π Z).ideal ⟨B.domain, hV⟩ = Ideal.span {B.chart.coord s}` using `exceptionalIdeal_ideal_blowupChart_domain hU hπ hZU hs`.

Establish `hyP : B.chart.coord s ∈ P`. Establish `h` using `(mem_support_iff_ideal_le_primeIdealOf (Blowup.exceptionalIdeal π Z) hV ⟨ξ, hξV⟩).mp hξE`. Rewrite `h` using `[hexcid]`. Conclude with `h (Ideal.mem_span_singleton_self _)`. Establish `hJ'P : J'.ideal ⟨B.domain, hV⟩ ≤ P` using `(mem_support_iff_ideal_le_primeIdealOf J' hV ⟨ξ, hξV⟩).mp hξJ`.

Establish `hφs : φ (cc.coord s) = B.chart.coord s` using `B.appLE_coord_self`. Establish `hφ : ∀ i ∈ S, i ≠ s → φ (cc.coord i) = B.chart.coord i * B.chart.coord s`. Introduce `i hi his`. Conclude with `B.appLE_coord_of_mem i hi his`. Establish `hy : B.chart.coord s ∈ nonZeroDivisors Γ(X₁, B.domain)` using `coord_mem_nonZeroDivisors hV B.chart s`.

Use `set e0 := exceptionalQuotientEquivOfIsBlowup hU hπ hZU hs with he0`. Use `set e : (Γ(X₁, B.domain) ⧸ Ideal.span {B.chart.coord s}) ≃+* MvPolynomial ↥(S.erase s) (Γ(X, U) ⧸ Ideal.span (cc.coord '' (S : Set (Fin m)))) := e0.trans (MvPolynomial.mapEquiv (↥(S.erase s)) (Ideal.quotEquivOfEq hspan)) with hedef`. Establish `heC : ∀ a : Γ(X, U), e (Ideal.Quotient.mk (Ideal.span {B.chart.coord s}) (φ a)) = MvPolynomial.C (Ideal.Quotient.mk (Ideal.span (cc.coord '' (S : Set (Fin m)))) a)`. Introduce `a`. Establish `h1 : e0 (Ideal.Quotient.mk (Ideal.span {B.chart.coord s}) (φ a)) = MvPolynomial.C ((Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)) a)` using `exceptionalQuotientEquiv_mk_appLE hU hπ hZU hs a`.

Use `show MvPolynomial.map (Ideal.quotEquivOfEq hspan).toRingHom (e0 (Ideal.Quotient.mk (Ideal.span {B.chart.coord s}) (φ a))) = MvPolynomial.C (Ideal.Quotient.mk (Ideal.span (cc.coord '' (S : Set (Fin m)))) a)`. Rewrite using `[h1, MvPolynomial.map_C]`. Conclude with `congrArg MvPolynomial.C (Ideal.quotEquivOfEq_mk hspan a)`. Establish `heX : ∀ t : ↥(S.erase s), e (Ideal.Quotient.mk (Ideal.span {B.chart.coord s}) (B.chart.coord t.1)) = MvPolynomial.X t`. Introduce `t`.

Take `⟨hts, htS⟩` from `Finset.mem_erase.mp t.2`. Establish `h1 : e0 (Ideal.Quotient.mk (Ideal.span {B.chart.coord s}) (B.chart.coord t.1)) = MvPolynomial.X ⟨t.1, Finset.mem_erase.mpr ⟨hts, htS⟩⟩` using `exceptionalQuotientEquiv_mk_coord hU hπ hZU hs t.1 htS hts`. Use `show MvPolynomial.map (Ideal.quotEquivOfEq hspan).toRingHom (e0 (Ideal.Quotient.mk (Ideal.span {B.chart.coord s}) (B.chart.coord t.1))) = MvPolynomial.X t`. Rewrite using `[h1]`. Conclude with `MvPolynomial.map_X _ _`.

Establish `hPmin : ∀ Q : Ideal Γ(X₁, B.domain), Q.IsPrime → Q ≤ P → B.chart.coord s ∈ Q → P ≤ Q`. Introduce `Q hQ hQP hyQ`. Use `hQ` as an intermediate fact. Take `⟨pt, hpt⟩` from `exists_primeIdealOf_eq hV ⟨Q, hQ⟩`. Establish `hptE : (pt : X₁) ∈ (Blowup.exceptionalIdeal π Z).support`.

Rewrite using `[mem_support_iff_ideal_le_primeIdealOf (Blowup.exceptionalIdeal π Z) hV pt, hpt, hexcid]`. Conclude with `Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hyQ)`. Establish `hcont : Continuous (hV.fromSpec.base)` using `hV.fromSpec.base.hom.continuous`. Establish `hQP' : (⟨Q, hQ⟩ : PrimeSpectrum Γ(X₁, B.domain)) ≤ hV.primeIdealOf ⟨ξ, hξV⟩` using `hQP`. Establish `hmem : hV.primeIdealOf ⟨ξ, hξV⟩ ∈ closure ({(⟨Q, hQ⟩ : PrimeSpectrum Γ(X₁, B.domain))} : Set (PrimeSpectrum Γ(X₁, B.domain)))` using `(PrimeSpectrum.le_iff_mem_closure _ _).mp hQP'`.

Establish `hfξ : hV.fromSpec.base (hV.primeIdealOf ⟨ξ, hξV⟩) = ξ` using `hV.fromSpec_primeIdealOf ⟨ξ, hξV⟩`. Establish `hfQ : hV.fromSpec.base (⟨Q, hQ⟩ : PrimeSpectrum Γ(X₁, B.domain)) = (pt : X₁)`. Rewrite using `[← hpt]`. Conclude with `hV.fromSpec_primeIdealOf pt`. Establish `hpre : IsClosed (hV.fromSpec.base ⁻¹' (closure ({(pt : X₁)} : Set X₁)))` using `IsClosed.preimage hcont isClosed_closure`.

Establish `hQin : (⟨Q, hQ⟩ : PrimeSpectrum Γ(X₁, B.domain)) ∈ hV.fromSpec.base ⁻¹' (closure ({(pt : X₁)} : Set X₁))` using `by show hV.fromSpec.base (⟨Q, hQ⟩ : PrimeSpectrum Γ(X₁, B.domain)) ∈ closure ({(pt : X₁)} : Set X₁)`. Rewrite using `[hfQ]`. Conclude with `subset_closure rfl`. Establish `hmem2` using `closure_minimal (Set.singleton_subset_iff.mpr hQin) hpre hmem`. Establish `h2 : ξ ∈ closure ({(pt : X₁)} : Set X₁)`.

Establish `h3 : hV.fromSpec.base (hV.primeIdealOf ⟨ξ, hξV⟩) ∈ closure ({(pt : X₁)} : Set X₁)` using `hmem2`. Rewrite `h3` using `[hfξ]`. Then use the resulting hypothesis. Establish `hxx` using `eq_of_mem_closure_singleton_of_maximal_irreducible hCirr hCsub hCmax hclosed hξ hptE h2`. Establish `hpteq : pt = (⟨ξ, hξV⟩ : ↥(B.domain))` using `Subtype.ext hxx`. Rewrite `hpt` using `[hpteq]`.

Conclude with `le_of_eq (congrArg PrimeSpectrum.asIdeal hpt)`. Establish `hcosupp : ∀ x : X, x ∈ Z.support → x ∈ U → x ∈ orderAtLeastLocus J c`. Introduce `x hx _`. Rewrite using `[mem_orderAtLeastLocus_iff]`. Conclude with `le_of_eq (hord x hx).symm`.

Establish `hJpow : J.ideal ⟨U, hU⟩ ≤ Ideal.span (cc.coord '' (S : Set (Fin m))) ^ c`. Establish `h` using `ideal_le_pow_of_restrictIdeal_eq_coordIdeal p hU cc Z S hZU c J hcosupp`. Rewrite `h` using `[hspan]`. Conclude with `h`. Establish `hmap : Ideal.map φ (J.ideal ⟨U, hU⟩) ≤ Ideal.span {B.chart.coord s ^ c} * J'.ideal ⟨B.domain, hV⟩`.

Establish `h1 : (J.comap π).ideal ⟨B.domain, hV⟩ = Ideal.map φ (J.ideal ⟨U, hU⟩)` using `AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE J π ⟨U, hU⟩ ⟨B.domain, hV⟩ B.domain_le`. Establish `h2 : ((Blowup.exceptionalIdeal π Z) ^ c * J').ideal ⟨B.domain, hV⟩ = ((Blowup.exceptionalIdeal π Z).ideal ⟨B.domain, hV⟩) ^ c * J'.ideal ⟨B.domain, hV⟩`. Rewrite using `[show ((Blowup.exceptionalIdeal π Z) ^ c * J').ideal ⟨B.domain, hV⟩ = ((Blowup.exceptionalIdeal π Z) ^ c).ideal ⟨B.domain, hV⟩ * J'.ideal ⟨B.domain, hV⟩ from rfl, AlgebraicGeometry.Scheme.IdealSheafData.ideal_pow]`. Both sides reduce to the same expression. Rewrite using `[← h1, ← htr, h2, hexcid, ← Ideal.span_singleton_pow]`.

Establish `hle` using `ideal_le_comap_pow_succ_of_map_le_span_pow_mul φ cc.coord B.chart.coord S s hs hφs hφ hy e heC heX P hyP hPmin c (J.ideal ⟨U, hU⟩) hJpow (J'.ideal ⟨B.domain, hV⟩) hJ'P hmap`. Establish `hQcprime : (Ideal.comap φ P).IsPrime` using `Ideal.comap_isPrime φ P`. Take `⟨pt', hpt'q⟩` from `exists_primeIdealOf_eq hU ⟨Ideal.comap φ P, hQcprime⟩`. Establish `hz'Z : (pt' : X) ∈ Z.support`. Rewrite using `[mem_support_iff_ideal_le_primeIdealOf Z hU pt', hpt'q, hspan]`.

Use `Ideal.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `a ⟨i, hi, rfl⟩`. Establish `hiS : i ∈ S` using `hi`. Use `show cc.coord i ∈ Ideal.comap φ P`. Rewrite using `[Ideal.mem_comap]`.

Distinguish the cases in `his : i = s`. Substitute `his` using the available equality. Rewrite using `[hφs]`. Conclude with `hyP`. Rewrite using `[hφ i hiS his]`.

Conclude with `Ideal.mul_mem_left _ _ hyP`. Establish `horder : ((c + 1 : ℕ) : ℕ∞) ≤ orderAt J (pt' : X)`. Use `le_orderAt_of_ideal_le_pow J hU pt' (c + 1) ?_` and prove the remaining obligations. Rewrite using `[hpt'q]`. Conclude with `hle`.

Rewrite `horder` using `[hord _ hz'Z]`. Establish `hcc : c + 1 ≤ c` using `by exact_mod_cast horder`. Use linear arithmetic over natural numbers and integers.
-/
theorem controlledTransform_not_subset_support {k : Type u} [Field k] [CharZero k]
    {X X₁ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [IsLocallyNoetherian X] [IsLocallyNoetherian X₁]
    (Z : X.IdealSheafData) (E : List X.IdealSheafData) (hE : HasStrictNormalCrossingsWith p Z E)
    (π : X₁ ⟶ X) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (J : X.IdealSheafData) (c : ℕ)
    (hord : ∀ x : X, x ∈ Z.support → orderAt J x = (c : ℕ∞))
    (J' : X₁.IdealSheafData)
    (htr : Blowup.exceptionalIdeal π Z ^ c * J' = J.comap π)
    (C : Set X₁)
    (hCirr : IsIrreducible C)
    (hCsub : C ⊆ ((Blowup.exceptionalIdeal π Z).support : Set X₁))
    (hCmax : ∀ T : Set X₁, IsIrreducible T →
      T ⊆ ((Blowup.exceptionalIdeal π Z).support : Set X₁) → C ⊆ T → T = C) :
    ¬ (C ⊆ (J'.support : Set X₁)) := by
  classical
  intro hCJ'
  have hZsm : AlgebraicGeometry.Smooth (Z.subschemeι ≫ p) :=
    smooth_subschemeι_comp_of_hasStrictNormalCrossingsWith Z E hE
  have hclosed : IsClosed ((Blowup.exceptionalIdeal π Z).support : Set X₁) :=
    (Blowup.exceptionalIdeal π Z).support.2
  obtain ⟨ξ, hξ⟩ := exists_closure_singleton_eq_of_maximal_irreducible hCirr hCsub hCmax hclosed
  have hξC : ξ ∈ C := by
    rw [← hξ]
    exact subset_closure rfl
  have hξE : ξ ∈ (Blowup.exceptionalIdeal π Z).support := hCsub hξC
  have hξJ : ξ ∈ J'.support := hCJ' hξC
  have hzZ : π.base ξ ∈ Z.support := by
    have h1 : ξ ∈ (Z.comap π).support := by
      rw [← Blowup.exceptionalIdeal_eq_comap π Z]; exact hξE
    rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap] at h1
    exact h1
  obtain ⟨U, hU, m, cc, S, hzU, hspan⟩ :=
    exists_chart_ideal_eq_span_coord p Z (π.base ξ) hzZ
  have hZU : restrictIdeal Z U = cc.coordIdeal S :=
    restrictIdeal_eq_coordIdeal_of_ideal_eq_span hU cc Z S hspan
  have hξU : ξ ∈ (TopologicalSpace.Opens.map π.base).obj U := hzU
  obtain ⟨s, hs, hξV⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π cc S hπ hZU ξ hξU
  set B := blowupChartOfIsBlowup π cc S hπ hZU s hs with hBdef
  have hV : IsAffineOpen B.domain := isAffineOpen_blowupChart_domain hU hπ hZU hs
  set φ := (π.appLE U B.domain B.domain_le).hom with hφdef
  set P : Ideal Γ(X₁, B.domain) := (hV.primeIdealOf ⟨ξ, hξV⟩).asIdeal with hPdef
  have hPprime : P.IsPrime := (hV.primeIdealOf ⟨ξ, hξV⟩).isPrime
  have hexcid : (Blowup.exceptionalIdeal π Z).ideal ⟨B.domain, hV⟩
      = Ideal.span {B.chart.coord s} :=
    exceptionalIdeal_ideal_blowupChart_domain hU hπ hZU hs
  have hyP : B.chart.coord s ∈ P := by
    have h := (mem_support_iff_ideal_le_primeIdealOf (Blowup.exceptionalIdeal π Z) hV ⟨ξ, hξV⟩).mp hξE
    rw [hexcid] at h
    exact h (Ideal.mem_span_singleton_self _)
  have hJ'P : J'.ideal ⟨B.domain, hV⟩ ≤ P :=
    (mem_support_iff_ideal_le_primeIdealOf J' hV ⟨ξ, hξV⟩).mp hξJ
  have hφs : φ (cc.coord s) = B.chart.coord s := B.appLE_coord_self
  have hφ : ∀ i ∈ S, i ≠ s → φ (cc.coord i) = B.chart.coord i * B.chart.coord s := by
    intro i hi his
    exact B.appLE_coord_of_mem i hi his
  have hy : B.chart.coord s ∈ nonZeroDivisors Γ(X₁, B.domain) :=
    coord_mem_nonZeroDivisors hV B.chart s
  set e0 := exceptionalQuotientEquivOfIsBlowup hU hπ hZU hs with he0
  set e : (Γ(X₁, B.domain) ⧸ Ideal.span {B.chart.coord s}) ≃+*
      MvPolynomial ↥(S.erase s)
        (Γ(X, U) ⧸ Ideal.span (cc.coord '' (S : Set (Fin m)))) :=
    e0.trans (MvPolynomial.mapEquiv (↥(S.erase s)) (Ideal.quotEquivOfEq hspan)) with hedef
  have heC : ∀ a : Γ(X, U), e (Ideal.Quotient.mk (Ideal.span {B.chart.coord s}) (φ a)) =
      MvPolynomial.C (Ideal.Quotient.mk (Ideal.span (cc.coord '' (S : Set (Fin m)))) a) := by
    intro a
    have h1 : e0 (Ideal.Quotient.mk (Ideal.span {B.chart.coord s}) (φ a))
        = MvPolynomial.C ((Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)) a) :=
      exceptionalQuotientEquiv_mk_appLE hU hπ hZU hs a
    show MvPolynomial.map (Ideal.quotEquivOfEq hspan).toRingHom
        (e0 (Ideal.Quotient.mk (Ideal.span {B.chart.coord s}) (φ a)))
      = MvPolynomial.C (Ideal.Quotient.mk (Ideal.span (cc.coord '' (S : Set (Fin m)))) a)
    rw [h1, MvPolynomial.map_C]
    exact congrArg MvPolynomial.C (Ideal.quotEquivOfEq_mk hspan a)
  have heX : ∀ t : ↥(S.erase s),
      e (Ideal.Quotient.mk (Ideal.span {B.chart.coord s}) (B.chart.coord t.1))
        = MvPolynomial.X t := by
    intro t
    obtain ⟨hts, htS⟩ := Finset.mem_erase.mp t.2
    have h1 : e0 (Ideal.Quotient.mk (Ideal.span {B.chart.coord s}) (B.chart.coord t.1))
        = MvPolynomial.X ⟨t.1, Finset.mem_erase.mpr ⟨hts, htS⟩⟩ :=
      exceptionalQuotientEquiv_mk_coord hU hπ hZU hs t.1 htS hts
    show MvPolynomial.map (Ideal.quotEquivOfEq hspan).toRingHom
        (e0 (Ideal.Quotient.mk (Ideal.span {B.chart.coord s}) (B.chart.coord t.1)))
      = MvPolynomial.X t
    rw [h1]
    exact MvPolynomial.map_X _ _
  have hPmin : ∀ Q : Ideal Γ(X₁, B.domain), Q.IsPrime → Q ≤ P → B.chart.coord s ∈ Q → P ≤ Q := by
    intro Q hQ hQP hyQ
    have := hQ
    obtain ⟨pt, hpt⟩ := exists_primeIdealOf_eq hV ⟨Q, hQ⟩
    have hptE : (pt : X₁) ∈ (Blowup.exceptionalIdeal π Z).support := by
      rw [mem_support_iff_ideal_le_primeIdealOf (Blowup.exceptionalIdeal π Z) hV pt, hpt, hexcid]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hyQ)
    have hcont : Continuous (hV.fromSpec.base) := hV.fromSpec.base.hom.continuous
    have hQP' : (⟨Q, hQ⟩ : PrimeSpectrum Γ(X₁, B.domain)) ≤ hV.primeIdealOf ⟨ξ, hξV⟩ := hQP
    have hmem : hV.primeIdealOf ⟨ξ, hξV⟩ ∈
        closure ({(⟨Q, hQ⟩ : PrimeSpectrum Γ(X₁, B.domain))} :
          Set (PrimeSpectrum Γ(X₁, B.domain))) :=
      (PrimeSpectrum.le_iff_mem_closure _ _).mp hQP'
    have hfξ : hV.fromSpec.base (hV.primeIdealOf ⟨ξ, hξV⟩) = ξ :=
      hV.fromSpec_primeIdealOf ⟨ξ, hξV⟩
    have hfQ : hV.fromSpec.base (⟨Q, hQ⟩ : PrimeSpectrum Γ(X₁, B.domain)) = (pt : X₁) := by
      rw [← hpt]
      exact hV.fromSpec_primeIdealOf pt
    have hpre : IsClosed (hV.fromSpec.base ⁻¹' (closure ({(pt : X₁)} : Set X₁))) :=
      IsClosed.preimage hcont isClosed_closure
    have hQin : (⟨Q, hQ⟩ : PrimeSpectrum Γ(X₁, B.domain)) ∈
        hV.fromSpec.base ⁻¹' (closure ({(pt : X₁)} : Set X₁)) := by
      show hV.fromSpec.base (⟨Q, hQ⟩ : PrimeSpectrum Γ(X₁, B.domain))
        ∈ closure ({(pt : X₁)} : Set X₁)
      rw [hfQ]
      exact subset_closure rfl
    have hmem2 := closure_minimal (Set.singleton_subset_iff.mpr hQin) hpre hmem
    have h2 : ξ ∈ closure ({(pt : X₁)} : Set X₁) := by
      have h3 : hV.fromSpec.base (hV.primeIdealOf ⟨ξ, hξV⟩)
          ∈ closure ({(pt : X₁)} : Set X₁) := hmem2
      rwa [hfξ] at h3
    have hxx := eq_of_mem_closure_singleton_of_maximal_irreducible hCirr hCsub hCmax hclosed
      hξ hptE h2
    have hpteq : pt = (⟨ξ, hξV⟩ : ↥(B.domain)) := Subtype.ext hxx
    rw [hpteq] at hpt
    exact le_of_eq (congrArg PrimeSpectrum.asIdeal hpt)
  have hcosupp : ∀ x : X, x ∈ Z.support → x ∈ U → x ∈ orderAtLeastLocus J c := by
    intro x hx _
    rw [mem_orderAtLeastLocus_iff]
    exact le_of_eq (hord x hx).symm
  have hJpow : J.ideal ⟨U, hU⟩ ≤ Ideal.span (cc.coord '' (S : Set (Fin m))) ^ c := by
    have h := ideal_le_pow_of_restrictIdeal_eq_coordIdeal p hU cc Z S hZU c J hcosupp
    rw [hspan] at h
    exact h
  have hmap : Ideal.map φ (J.ideal ⟨U, hU⟩)
      ≤ Ideal.span {B.chart.coord s ^ c} * J'.ideal ⟨B.domain, hV⟩ := by
    have h1 : (J.comap π).ideal ⟨B.domain, hV⟩ = Ideal.map φ (J.ideal ⟨U, hU⟩) :=
      AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE J π ⟨U, hU⟩
        ⟨B.domain, hV⟩ B.domain_le
    have h2 : ((Blowup.exceptionalIdeal π Z) ^ c * J').ideal ⟨B.domain, hV⟩
        = ((Blowup.exceptionalIdeal π Z).ideal ⟨B.domain, hV⟩) ^ c * J'.ideal ⟨B.domain, hV⟩ := by
      rw [show ((Blowup.exceptionalIdeal π Z) ^ c * J').ideal ⟨B.domain, hV⟩
          = ((Blowup.exceptionalIdeal π Z) ^ c).ideal ⟨B.domain, hV⟩ * J'.ideal ⟨B.domain, hV⟩ from rfl,
        AlgebraicGeometry.Scheme.IdealSheafData.ideal_pow]
      rfl
    rw [← h1, ← htr, h2, hexcid, ← Ideal.span_singleton_pow]
  have hle := ideal_le_comap_pow_succ_of_map_le_span_pow_mul φ cc.coord B.chart.coord S s hs hφs hφ hy
    e heC heX P hyP hPmin c (J.ideal ⟨U, hU⟩) hJpow (J'.ideal ⟨B.domain, hV⟩) hJ'P hmap
  have hQcprime : (Ideal.comap φ P).IsPrime := Ideal.comap_isPrime φ P
  obtain ⟨pt', hpt'q⟩ :=
    exists_primeIdealOf_eq hU ⟨Ideal.comap φ P, hQcprime⟩
  have hz'Z : (pt' : X) ∈ Z.support := by
    rw [mem_support_iff_ideal_le_primeIdealOf Z hU pt', hpt'q, hspan]
    refine Ideal.span_le.mpr ?_
    rintro a ⟨i, hi, rfl⟩
    have hiS : i ∈ S := hi
    show cc.coord i ∈ Ideal.comap φ P
    rw [Ideal.mem_comap]
    by_cases his : i = s
    · subst his
      rw [hφs]
      exact hyP
    · rw [hφ i hiS his]
      exact Ideal.mul_mem_left _ _ hyP
  have horder : ((c + 1 : ℕ) : ℕ∞) ≤ orderAt J (pt' : X) := by
    refine le_orderAt_of_ideal_le_pow J hU pt' (c + 1) ?_
    rw [hpt'q]
    exact hle
  rw [hord _ hz'Z] at horder
  have hcc : c + 1 ≤ c := by exact_mod_cast horder
  omega

end FunctorialResolution.EmbeddedResolution

end
