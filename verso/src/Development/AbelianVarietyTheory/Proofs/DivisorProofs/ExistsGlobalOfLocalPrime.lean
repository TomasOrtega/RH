import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AlgPointsLocal

/- English proof (translation)
Introduce `R K _ _ _ A _ _ _ r f h`. Use `haveI := Fintype.ofFinite (A →ₐ[R] K)`. Set `J : Ideal A` to `{ carrier := {u | ∃ a : A, ∀ ψ : A →ₐ[R] K, ψ a = ψ u * f ψ} add_mem' := by`. Introduce and unpack `u v ⟨a, ha⟩ ⟨b, hb⟩`. Conclude with `⟨a + b, fun ψ => by rw [map_add, map_add, ha, hb, add_mul]⟩`.

Use the proof step `zero_mem' := ⟨0, fun ψ => by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c u ⟨a, ha⟩`. Conclude with `⟨c * a, fun ψ => by rw [smul_eq_mul, map_mul, map_mul, ha, _root_.mul_assoc]⟩ }`. Establish `memJ : ∀ u : A, u ∈ J ↔ ∃ a : A, ∀ ψ : A →ₐ[R] K, ψ a = ψ u * f ψ` using `fun u => Iff.rfl`.

Establish `key : ∀ (P : Ideal A), P.IsPrime → r ∉ P → ∃ u ∈ J, u ∉ P`. Introduce `P hP hr`. Take `⟨c, hc⟩` from `@h P hP hr`. Take `⟨⟨b, v⟩, hbv⟩` from `IsLocalization.surj P.primeCompl c`. Establish `hw : ∀ ψ : A →ₐ[R] K, ∃ w : A, w ∉ P ∧ ((∀ s : A, s ∉ P → ψ s ≠ 0) ∨ ψ w = 0)`.

Introduce `ψ`. Distinguish the cases in `hg : ∀ s : A, s ∉ P → ψ s ≠ 0`. Conclude with `⟨1, fun h1 => hP.ne_top ((Ideal.eq_top_iff_one P).2 h1), Or.inl hg⟩`. Use `push_neg at hg`. Take `⟨w, hwP, hw0⟩` from `hg`.

Conclude with `⟨w, hwP, Or.inr hw0⟩`. Use `choose w hwP hwor using hw`. Establish `hWP : (∏ ψ, w ψ) ∉ P`. Establish `: (∏ ψ, w ψ) ∈ P.primeCompl` using `Submonoid.prod_mem _ (fun ψ _ => hwP ψ)`. Conclude with `this`.

Use `⟨(v : A) * ∏ ψ, w ψ, (memJ _).2 ⟨b * ∏ ψ, w ψ, fun ψ => ?_⟩, ?_⟩` and prove the remaining obligations. Break down `hwor ψ with hg | h0` into its components or cases. Establish `hunit : ∀ y : P.primeCompl, IsUnit (ψ (y : A))` using `fun y => (hg y y.2).isUnit`. Set `ψ' : Localization.AtPrime P →ₐ[R] K` to `IsLocalization.liftAlgHom (M := P.primeCompl) (f := ψ) hunit`. Establish `e : ∀ x : A, ψ' (algebraMap A _ x) = ψ x` using `fun x => by`.

Simplify using `[ψ', IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]`. Establish `hcomp : ψ'.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime P)) = ψ`. Use extensionality with `x`. Conclude with `e x`. Establish `h1` using `hc ψ'`.

Rewrite `h1` using `[hcomp]`. Establish `h2` using `congrArg ψ' hbv`. Rewrite `h2` using `[map_mul, h1, e, e]`. Rewrite using `[map_mul, map_mul, ← h2]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h3 : ψ (∏ φ, w φ) = 0`. Rewrite using `[map_prod]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ ψ) h0`. Rewrite using `[map_mul, map_mul, h3]`. Simplify using the standard rewrite rules.

Conclude with `fun hm => (hP.mem_or_mem hm).elim v.2 hWP`. Establish `hr : r ∈ J.radical`. Rewrite using `[Ideal.radical_eq_sInf, Submodule.mem_sInf]`. Introduce and unpack `P ⟨hJP, hP⟩`. Assume the negation of the conclusion as `hrP`.

Take `⟨u, huJ, huP⟩` from `key P hP hrP`. Conclude with `huP (hJP huJ)`. Take `⟨k, hk⟩` from `hr`. Take `⟨a, ha⟩` from `(memJ _).1 hk`. Conclude with `⟨k, a, fun ψ => by rw [ha, map_pow]⟩`.
-/
theorem exists_pow_mul_of_locally_integral : ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (A : Type) [CommRing A] [Algebra R A] [Finite (A →ₐ[R] K)] (r : A) (f : (A →ₐ[R] K) → K), (∀ (P : Ideal A) [P.IsPrime], r ∉ P → ∃ c : Localization.AtPrime P, ∀ ψ : Localization.AtPrime P →ₐ[R] K, ψ c = f (ψ.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime P)))) → ∃ (k : ℕ) (a : A), ∀ ψ : A →ₐ[R] K, ψ a = ψ r ^ k * f ψ := by
  intro R K _ _ _ A _ _ _ r f h
  classical
  haveI := Fintype.ofFinite (A →ₐ[R] K)
  let J : Ideal A :=
    { carrier := {u | ∃ a : A, ∀ ψ : A →ₐ[R] K, ψ a = ψ u * f ψ}
      add_mem' := by
        rintro u v ⟨a, ha⟩ ⟨b, hb⟩
        exact ⟨a + b, fun ψ => by rw [map_add, map_add, ha, hb, add_mul]⟩
      zero_mem' := ⟨0, fun ψ => by simp⟩
      smul_mem' := by
        rintro c u ⟨a, ha⟩
        exact ⟨c * a, fun ψ => by rw [smul_eq_mul, map_mul, map_mul, ha, _root_.mul_assoc]⟩ }
  have memJ : ∀ u : A, u ∈ J ↔ ∃ a : A, ∀ ψ : A →ₐ[R] K, ψ a = ψ u * f ψ := fun u => Iff.rfl
  have key : ∀ (P : Ideal A), P.IsPrime → r ∉ P → ∃ u ∈ J, u ∉ P := by
    intro P hP hr
    obtain ⟨c, hc⟩ := @h P hP hr
    obtain ⟨⟨b, v⟩, hbv⟩ := IsLocalization.surj P.primeCompl c
    have hw : ∀ ψ : A →ₐ[R] K, ∃ w : A, w ∉ P ∧ ((∀ s : A, s ∉ P → ψ s ≠ 0) ∨ ψ w = 0) := by
      intro ψ
      by_cases hg : ∀ s : A, s ∉ P → ψ s ≠ 0
      · exact ⟨1, fun h1 => hP.ne_top ((Ideal.eq_top_iff_one P).2 h1), Or.inl hg⟩
      · push_neg at hg
        obtain ⟨w, hwP, hw0⟩ := hg
        exact ⟨w, hwP, Or.inr hw0⟩
    choose w hwP hwor using hw
    have hWP : (∏ ψ, w ψ) ∉ P := by
      have : (∏ ψ, w ψ) ∈ P.primeCompl := Submonoid.prod_mem _ (fun ψ _ => hwP ψ)
      exact this
    refine ⟨(v : A) * ∏ ψ, w ψ, (memJ _).2 ⟨b * ∏ ψ, w ψ, fun ψ => ?_⟩, ?_⟩
    · rcases hwor ψ with hg | h0
      · have hunit : ∀ y : P.primeCompl, IsUnit (ψ (y : A)) := fun y => (hg y y.2).isUnit
        let ψ' : Localization.AtPrime P →ₐ[R] K := IsLocalization.liftAlgHom (M := P.primeCompl) (f := ψ) hunit
        have e : ∀ x : A, ψ' (algebraMap A _ x) = ψ x := fun x => by
          simp [ψ', IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
        have hcomp : ψ'.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime P)) = ψ := by
          ext x; exact e x
        have h1 := hc ψ'
        rw [hcomp] at h1
        have h2 := congrArg ψ' hbv
        rw [map_mul, h1, e, e] at h2
        rw [map_mul, map_mul, ← h2]; ring
      · have h3 : ψ (∏ φ, w φ) = 0 := by
          rw [map_prod]
          exact Finset.prod_eq_zero (Finset.mem_univ ψ) h0
        rw [map_mul, map_mul, h3]; simp
    · exact fun hm => (hP.mem_or_mem hm).elim v.2 hWP
  have hr : r ∈ J.radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨hJP, hP⟩
    by_contra hrP
    obtain ⟨u, huJ, huP⟩ := key P hP hrP
    exact huP (hJP huJ)
  obtain ⟨k, hk⟩ := hr
  obtain ⟨a, ha⟩ := (memJ _).1 hk
  exact ⟨k, a, fun ψ => by rw [ha, map_pow]⟩

end GlobalTheory.AlgPointsLocal
