import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Establish `hx' : x ∈ Ideal.span (Set.range fun p : Fin r × Fin r => g p.1 * g p.2)` using `by open Pointwise in`. Establish `hset : Set.range g * Set.range g = Set.range fun p : Fin r × Fin r => g p.1 * g p.2`. Use extensionality with `y`. Simplify using `[Set.mem_mul]`. Use `open Pointwise in`.

Rewrite `hx` using `[Ideal.span_mul_span', hset]`. Then use the resulting hypothesis. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun S).1 hx'`. Use `⟨fun k l => c (k, l), ?_⟩` and prove the remaining obligations. Rewrite using `[← hc, Fintype.sum_prod_type]`. Simplify using `only [smul_eq_mul]`.
-/
theorem exists_sum_mul_of_mem_span_range_sq {S : Type} [CommRing S] {r : ℕ} (g : Fin r → S)
    (x : S) (hx : x ∈ Ideal.span (Set.range g) * Ideal.span (Set.range g)) :
    ∃ b : Fin r → Fin r → S, x = ∑ k, ∑ l, b k l * (g k * g l) := by

  have hx' : x ∈ Ideal.span (Set.range fun p : Fin r × Fin r => g p.1 * g p.2) := by
    open Pointwise in
    have hset : Set.range g * Set.range g =
        Set.range fun p : Fin r × Fin r => g p.1 * g p.2 := by
      ext y
      simp [Set.mem_mul]
    open Pointwise in
    rwa [Ideal.span_mul_span', hset] at hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 hx'
  refine ⟨fun k l => c (k, l), ?_⟩
  rw [← hc, Fintype.sum_prod_type]
  simp only [smul_eq_mul]

/- English proof (translation)
Introduce `ι _ R _ r g hs`. Use `set I : Ideal (MvPolynomial ι R) := Ideal.span (Set.range g) with hI`. Establish `hsurj : Function.Surjective (Ideal.Quotient.mkₐ R I)` using `Ideal.Quotient.mkₐ_surjective R I`. Take `⟨σ, hσ⟩` from `(Algebra.FormallySmooth.iff_split_surjection _ hsurj).1 hs`. Establish `hK : RingHom.ker (Ideal.Quotient.mkₐ R I).toRingHom = I`.

Use extensionality with `x`. Rewrite using `[RingHom.mem_ker]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem`. Establish `hlift : ∀ i : ι, ∃ y : MvPolynomial ι R, Ideal.Quotient.mk _ y = σ (Ideal.Quotient.mkₐ R I (X i))` using `fun i => Ideal.Quotient.mk_surjective _`. Use `choose y hy using hlift`.

Establish `hdiff : ∀ i, y i - X i ∈ I`. Introduce `i`. Establish `h1` using `congrArg (Ideal.Quotient.mkₐ R I).kerSquareLift (hy i)`. Rewrite `h1` using `[AlgHom.kerSquareLift_mk, ← AlgHom.comp_apply, hσ, AlgHom.id_apply]`. Conclude with `Ideal.Quotient.eq.1 h1`.

Use `choose a ha using fun i => (Submodule.mem_span_range_iff_exists_fun (MvPolynomial ι R)).1 (hdiff i)`. Establish `hy' : ∀ i, X i + ∑ k, a i k * g k = y i`. Introduce `i`. Use `ha i` as an intermediate fact. Simplify using `only [smul_eq_mul] at this`.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcomp : (Ideal.Quotient.mkₐ R _).comp (aeval fun i => X i + ∑ k, a i k * g k : MvPolynomial ι R →ₐ[R] MvPolynomial ι R) = σ.comp (Ideal.Quotient.mkₐ R I)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`.

Rewrite using `[AlgHom.comp_apply, aeval_X, hy', AlgHom.comp_apply, ← hy i]`. Both sides reduce to the same expression. Establish `hmem : ∀ j, aeval (fun i => X i + ∑ k, a i k * g k) (g j) ∈ I * I`. Introduce `j`. Establish `hgj : Ideal.Quotient.mkₐ R I (g j) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨j, rfl⟩)`.

Establish `h2` using `AlgHom.congr_fun hcomp (g j)`. Rewrite `h2` using `[AlgHom.comp_apply, AlgHom.comp_apply, hgj, map_zero, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, hK, pow_two]`. Conclude with `h2`. Use `choose b hb using fun j => exists_sum_mul_of_mem_span_range_sq g _ (hmem j)`. Conclude with `⟨a, b, hb⟩`.
-/
theorem exists_witnesses_of_formallySmooth_quotient :
    ∀ (ι : Type) [Fintype ι] (R : Type) [CommRing R] (r : ℕ) (g : Fin r → MvPolynomial ι R), Algebra.FormallySmooth R (MvPolynomial ι R ⧸ Ideal.span (Set.range g)) → ∃ (a : ι → Fin r → MvPolynomial ι R) (b : Fin r → Fin r → Fin r → MvPolynomial ι R), ∀ j, aeval (fun i => X i + ∑ k, a i k * g k) (g j) = ∑ k, ∑ l, b j k l * (g k * g l) := by
  intro ι _ R _ r g hs
  set I : Ideal (MvPolynomial ι R) := Ideal.span (Set.range g) with hI
  have hsurj : Function.Surjective (Ideal.Quotient.mkₐ R I) := Ideal.Quotient.mkₐ_surjective R I

  obtain ⟨σ, hσ⟩ := (Algebra.FormallySmooth.iff_split_surjection _ hsurj).1 hs
  have hK : RingHom.ker (Ideal.Quotient.mkₐ R I).toRingHom = I := by
    ext x
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem

  have hlift : ∀ i : ι, ∃ y : MvPolynomial ι R,
      Ideal.Quotient.mk _ y = σ (Ideal.Quotient.mkₐ R I (X i)) :=
    fun i => Ideal.Quotient.mk_surjective _
  choose y hy using hlift

  have hdiff : ∀ i, y i - X i ∈ I := by
    intro i
    have h1 := congrArg (Ideal.Quotient.mkₐ R I).kerSquareLift (hy i)
    rw [AlgHom.kerSquareLift_mk, ← AlgHom.comp_apply, hσ, AlgHom.id_apply] at h1
    exact Ideal.Quotient.eq.1 h1
  choose a ha using fun i => (Submodule.mem_span_range_iff_exists_fun (MvPolynomial ι R)).1 (hdiff i)
  have hy' : ∀ i, X i + ∑ k, a i k * g k = y i := by
    intro i
    have := ha i
    simp only [smul_eq_mul] at this
    rw [this]
    ring

  have hcomp : (Ideal.Quotient.mkₐ R _).comp
      (aeval fun i => X i + ∑ k, a i k * g k : MvPolynomial ι R →ₐ[R] MvPolynomial ι R) =
      σ.comp (Ideal.Quotient.mkₐ R I) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, aeval_X, hy', AlgHom.comp_apply, ← hy i]
    rfl

  have hmem : ∀ j, aeval (fun i => X i + ∑ k, a i k * g k) (g j) ∈ I * I := by
    intro j
    have hgj : Ideal.Quotient.mkₐ R I (g j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨j, rfl⟩)
    have h2 := AlgHom.congr_fun hcomp (g j)
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hgj, map_zero, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem, hK, pow_two] at h2
    exact h2
  choose b hb using fun j => exists_sum_mul_of_mem_span_range_sq g _ (hmem j)
  exact ⟨a, b, hb⟩

end GlobalTheory
