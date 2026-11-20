import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsNilpotentTmulSubTmulOfConstOnFibresStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCommonDenominatorNilpotentCoboundaryStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

/- English proof (translation)
Set `φ : MvPolynomial σ ℂ →ₐ[ℂ] (X → ℂ)` to `Pi.algHom ℂ (fun _ => ℂ) fun x => MvPolynomial.aeval (p x)`. Establish `hφ : ∀ f x, φ f x = MvPolynomial.aeval (p x) f` using `fun _ _ => rfl`. Set `A : Subalgebra ℂ (X → ℂ)` to `φ.range`. Set `π : MvPolynomial σ ℂ →ₐ[ℂ] A` to `φ.rangeRestrict`. Establish `hπ : Function.Surjective π` using `φ.rangeRestrict_surjective`.

Establish `hπv : ∀ f x, ((π f : A) : X → ℂ) x = MvPolynomial.aeval (p x) f` using `fun _ _ => rfl`. Set `B : Subalgebra ℂ A` to `(π.comp (MvPolynomial.aeval q)).range`. Use `haveI : Algebra.FiniteType ℂ A := Algebra.FiniteType.of_surjective π hπ`. Use `haveI : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType ℂ B A`. Use `haveI : IsReduced A := isReduced_of_injective A.val Subtype.val_injective`.

Use `letI : Algebra ℚ B := ((algebraMap ℂ B).comp (algebraMap ℚ ℂ)).toAlgebra`. Establish `hpt : ∀ χ : A →ₐ[ℂ] ℂ, ∃ x, ∀ f, χ (π f) = MvPolynomial.aeval (p x) f`. Introduce `χ`. Establish `h1 : χ.comp π = MvPolynomial.aeval (fun i => χ (π (MvPolynomial.X i)))`. Use extensionality with `i`.

Simplify using the standard rewrite rules. Establish `h2 : ∀ f, χ (π f) = MvPolynomial.aeval (fun i => χ (π (MvPolynomial.X i))) f` using `fun f => DFunLike.congr_fun h1 f`. Take `⟨x, hx⟩` from `hcl (fun i => χ (π (MvPolynomial.X i))) (by`. Introduce `f hf`. Establish `h0 : π f = 0` using `Subtype.ext (funext fun x => hf x)`.

Rewrite using `[← h2, h0, map_zero])`. Conclude with `⟨x, fun f => by rw [h2, hx]⟩`. Establish `hnil : ∀ g ∈ s.image π, IsNilpotent (g ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] g)`. Introduce `g hg`. Take `⟨f, hf, rfl⟩` from `Finset.mem_image.1 hg`.

Use `GlobalTheory.T.isNilpotent_tmul_sub_tmul_of_const_on_fibres' B A (π f) ?_` and prove the remaining obligations. Introduce `χ χ' h`. Take `⟨x, hx⟩` from `hpt χ`. Take `⟨x', hx'⟩` from `hpt χ'`. Rewrite using `[hx, hx']`.

Use `hs f hf x x' fun i => ?_` and prove the remaining obligations. Rewrite using `[← hx, ← hx']`. Conclude with `h ⟨π (q i), MvPolynomial.X i, by simp⟩`. Take `⟨b, hb, hbs⟩` from `GlobalTheory.T.exists_common_denominator_nilpotent_coboundary B A Subtype.val_injective (s.image π) hnil`. Take `⟨b, c, rfl⟩` from `b`.

Use `⟨c, ?_, fun f hf => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc push_neg at hc`. Conclude with `hb (Subtype.ext (Subtype.ext (funext fun x => hc x)))`. Take `⟨⟨b', c', rfl⟩, hb'⟩` from `hbs (π f) (Finset.mem_image_of_mem _ hf)`. Conclude with `⟨c', fun x => congrFun (congrArg Subtype.val hb') x⟩`.
-/
theorem exists_multiplier_descend_of_closed {σ X : Type} [Fintype σ] [Nonempty X] (p : X → σ → ℂ)
    (hcl : ∀ y : σ → ℂ, (∀ f : MvPolynomial σ ℂ, (∀ x, MvPolynomial.aeval (p x) f = 0) →
      MvPolynomial.aeval y f = 0) → ∃ x, p x = y)
    (q : σ → MvPolynomial σ ℂ) (s : Finset (MvPolynomial σ ℂ))
    (hs : ∀ f ∈ s, ∀ x x', (∀ i, MvPolynomial.aeval (p x) (q i) = MvPolynomial.aeval (p x') (q i)) →
      MvPolynomial.aeval (p x) f = MvPolynomial.aeval (p x') f) :
    ∃ b : MvPolynomial σ ℂ, (∃ x, MvPolynomial.aeval (p x) (MvPolynomial.aeval q b) ≠ 0) ∧
      ∀ f ∈ s, ∃ b' : MvPolynomial σ ℂ, ∀ x,
        MvPolynomial.aeval (p x) (MvPolynomial.aeval q b) * MvPolynomial.aeval (p x) f =
          MvPolynomial.aeval (p x) (MvPolynomial.aeval q b') := by
  classical
  let φ : MvPolynomial σ ℂ →ₐ[ℂ] (X → ℂ) := Pi.algHom ℂ (fun _ => ℂ) fun x => MvPolynomial.aeval (p x)
  have hφ : ∀ f x, φ f x = MvPolynomial.aeval (p x) f := fun _ _ => rfl
  let A : Subalgebra ℂ (X → ℂ) := φ.range
  let π : MvPolynomial σ ℂ →ₐ[ℂ] A := φ.rangeRestrict
  have hπ : Function.Surjective π := φ.rangeRestrict_surjective
  have hπv : ∀ f x, ((π f : A) : X → ℂ) x = MvPolynomial.aeval (p x) f := fun _ _ => rfl
  let B : Subalgebra ℂ A := (π.comp (MvPolynomial.aeval q)).range
  haveI : Algebra.FiniteType ℂ A := Algebra.FiniteType.of_surjective π hπ
  haveI : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType ℂ B A
  haveI : IsReduced A := isReduced_of_injective A.val Subtype.val_injective
  letI : Algebra ℚ B := ((algebraMap ℂ B).comp (algebraMap ℚ ℂ)).toAlgebra
  have hpt : ∀ χ : A →ₐ[ℂ] ℂ, ∃ x, ∀ f, χ (π f) = MvPolynomial.aeval (p x) f := by
    intro χ
    have h1 : χ.comp π = MvPolynomial.aeval (fun i => χ (π (MvPolynomial.X i))) := by
      ext i
      simp
    have h2 : ∀ f, χ (π f) = MvPolynomial.aeval (fun i => χ (π (MvPolynomial.X i))) f :=
      fun f => DFunLike.congr_fun h1 f
    obtain ⟨x, hx⟩ := hcl (fun i => χ (π (MvPolynomial.X i))) (by
      intro f hf
      have h0 : π f = 0 := Subtype.ext (funext fun x => hf x)
      rw [← h2, h0, map_zero])
    exact ⟨x, fun f => by rw [h2, hx]⟩
  have hnil : ∀ g ∈ s.image π, IsNilpotent (g ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] g) := by
    intro g hg
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hg
    refine GlobalTheory.T.isNilpotent_tmul_sub_tmul_of_const_on_fibres' B A (π f) ?_
    intro χ χ' h
    obtain ⟨x, hx⟩ := hpt χ
    obtain ⟨x', hx'⟩ := hpt χ'
    rw [hx, hx']
    refine hs f hf x x' fun i => ?_
    rw [← hx, ← hx']
    exact h ⟨π (q i), MvPolynomial.X i, by simp⟩
  obtain ⟨b, hb, hbs⟩ := GlobalTheory.T.exists_common_denominator_nilpotent_coboundary B A Subtype.val_injective (s.image π) hnil
  obtain ⟨b, c, rfl⟩ := b
  refine ⟨c, ?_, fun f hf => ?_⟩
  · by_contra hc
    push_neg at hc
    exact hb (Subtype.ext (Subtype.ext (funext fun x => hc x)))
  · obtain ⟨⟨b', c', rfl⟩, hb'⟩ := hbs (π f) (Finset.mem_image_of_mem _ hf)
    exact ⟨c', fun x => congrFun (congrArg Subtype.val hb') x⟩

/- English proof (translation)
Set `E : Matrix ι ι (MvPolynomial (ι × ι) ℂ)` to `(e.map (algebraMap ℚ ℂ)).map MvPolynomial.C`. Set `Y : Matrix ι ι (MvPolynomial (ι × ι) ℂ)` to `Matrix.of fun i j => MvPolynomial.X (i, j)`. Use `⟨fun ij => (E * Y * E + (1 - E) * Y * (1 - E)) ij.1 ij.2, fun x ij => ?_⟩` and prove the remaining obligations. Set `ψ : MvPolynomial (ι × ι) ℂ →ₐ[ℂ] ℂ` to `MvPolynomial.aeval (fun kl : ι × ι => x kl.1 kl.2)`. Establish `hE : ψ.mapMatrix E = e.map (algebraMap ℚ ℂ)`.

Use extensionality with `i j`. Simplify using `[E, ψ]`. Establish `hY : ψ.mapMatrix Y = x`. Use extensionality with `i j`. Simplify using `[Y, ψ]`.

Establish `h : ψ.mapMatrix (E * Y * E + (1 - E) * Y * (1 - E)) = blk e x`. Simplify using `only [map_add, map_mul, map_sub, map_one, hE, hY, blk]`. Rewrite using `[← h]`. Both sides reduce to the same expression.
-/
theorem exists_poly_blk_entries {ι : Type} [Fintype ι] [DecidableEq ι] (e : Matrix ι ι ℚ) :
    ∃ q : ι × ι → MvPolynomial (ι × ι) ℂ, ∀ (x : Matrix ι ι ℂ) (ij : ι × ι),
      MvPolynomial.aeval (fun kl : ι × ι => x kl.1 kl.2) (q ij) = blk e x ij.1 ij.2 := by
  let E : Matrix ι ι (MvPolynomial (ι × ι) ℂ) := (e.map (algebraMap ℚ ℂ)).map MvPolynomial.C
  let Y : Matrix ι ι (MvPolynomial (ι × ι) ℂ) := Matrix.of fun i j => MvPolynomial.X (i, j)
  refine ⟨fun ij => (E * Y * E + (1 - E) * Y * (1 - E)) ij.1 ij.2, fun x ij => ?_⟩
  let ψ : MvPolynomial (ι × ι) ℂ →ₐ[ℂ] ℂ := MvPolynomial.aeval (fun kl : ι × ι => x kl.1 kl.2)
  have hE : ψ.mapMatrix E = e.map (algebraMap ℚ ℂ) := by
    ext i j
    simp [E, ψ]
  have hY : ψ.mapMatrix Y = x := by
    ext i j
    simp [Y, ψ]
  have h : ψ.mapMatrix (E * Y * E + (1 - E) * Y * (1 - E)) = blk e x := by
    simp only [map_add, map_mul, map_sub, map_one, hE, hY, blk]
  rw [← h]
  rfl

/- English proof (translation)
Introduce `ι _ _ Γ e hΓ hne s hs`. Take `⟨q, hq⟩` from `exists_poly_blk_entries e`. Use `haveI : Nonempty Γ := hne.to_subtype`. Establish `hev : ∀ (f : MvPolynomial (ι × ι) ℂ) (x : Matrix ι ι ℂ), evC f x = MvPolynomial.aeval (fun kl : ι × ι => x kl.1 kl.2) f` using `fun f x => rfl`. Establish `hcomp : ∀ (b : MvPolynomial (ι × ι) ℂ) (x : Matrix ι ι ℂ), MvPolynomial.aeval (fun kl : ι × ι => x kl.1 kl.2) (MvPolynomial.aeval q b) = evC b (blk e x)`.

Introduce `b x`. Rewrite using `[hev, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]`. Simplify using `only [hq]`. Take `⟨b, ⟨x₀, hx₀⟩, hb⟩` from `exists_multiplier_descend_of_closed (fun (x : Γ) (kl : ι × ι) => x.1 kl.1 kl.2) (by`. Introduce `y hy`.

Use `⟨⟨Matrix.of fun i j => y (i, j), hΓ fun f hf => ?_⟩, rfl⟩` and prove the remaining obligations. Use `hy (MvPolynomial.map (algebraMap ℚ ℂ) f) (fun x => by` as an intermediate fact. Rewrite using `[MvPolynomial.aeval_map_algebraMap]`. Conclude with `hf x.1 x.2)`. Rewrite `this` using `[MvPolynomial.aeval_map_algebraMap]`.

Conclude with `this) q s (by`. Introduce `f hf x x' h`. Use `hs f hf x.1 x.2 x'.1 x'.2 ?_` and prove the remaining obligations. Use extensionality with `i j`. Use `h (i, j)` as an intermediate fact.

Rewrite using `[hq, hq] at this)` and apply the resulting hypothesis. Use `⟨b, ⟨x₀.1, x₀.2, by rwa [hcomp] at hx₀⟩, fun f hf => ?_⟩` and prove the remaining obligations. Take `⟨b', hb'⟩` from `hb f hf`. Use `⟨b', fun x hx => ?_⟩` and prove the remaining obligations. Use `hb' ⟨x, hx⟩` as an intermediate fact.

Rewrite `this` using `[hcomp, hcomp]`. Conclude with `this`.
-/
theorem exists_multiplier_descend_blk :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), pts Γ ℂ ⊆ Γ → Γ.Nonempty → ∀ s : Finset (MvPolynomial (ι × ι) ℂ), (∀ f ∈ s, ∀ x ∈ Γ, ∀ x' ∈ Γ, blk e x = blk e x' → evC f x = evC f x') → ∃ b : MvPolynomial (ι × ι) ℂ, (∃ x ∈ Γ, evC b (blk e x) ≠ 0) ∧ ∀ f ∈ s, ∃ b' : MvPolynomial (ι × ι) ℂ, ∀ x ∈ Γ, evC b (blk e x) * evC f x = evC b' (blk e x) := by
  intro ι _ _ Γ e hΓ hne s hs
  obtain ⟨q, hq⟩ := exists_poly_blk_entries e
  haveI : Nonempty Γ := hne.to_subtype
  have hev : ∀ (f : MvPolynomial (ι × ι) ℂ) (x : Matrix ι ι ℂ),
      evC f x = MvPolynomial.aeval (fun kl : ι × ι => x kl.1 kl.2) f := fun f x => rfl
  have hcomp : ∀ (b : MvPolynomial (ι × ι) ℂ) (x : Matrix ι ι ℂ),
      MvPolynomial.aeval (fun kl : ι × ι => x kl.1 kl.2) (MvPolynomial.aeval q b) = evC b (blk e x) := by
    intro b x
    rw [hev, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    simp only [hq]
  obtain ⟨b, ⟨x₀, hx₀⟩, hb⟩ := exists_multiplier_descend_of_closed
    (fun (x : Γ) (kl : ι × ι) => x.1 kl.1 kl.2) (by
      intro y hy
      refine ⟨⟨Matrix.of fun i j => y (i, j), hΓ fun f hf => ?_⟩, rfl⟩
      have := hy (MvPolynomial.map (algebraMap ℚ ℂ) f) (fun x => by
        rw [MvPolynomial.aeval_map_algebraMap]
        exact hf x.1 x.2)
      rw [MvPolynomial.aeval_map_algebraMap] at this
      exact this) q s (by
      intro f hf x x' h
      refine hs f hf x.1 x.2 x'.1 x'.2 ?_
      ext i j
      have := h (i, j)
      rwa [hq, hq] at this)
  refine ⟨b, ⟨x₀.1, x₀.2, by rwa [hcomp] at hx₀⟩, fun f hf => ?_⟩
  obtain ⟨b', hb'⟩ := hb f hf
  refine ⟨b', fun x hx => ?_⟩
  have := hb' ⟨x, hx⟩
  rw [hcomp, hcomp] at this
  exact this

end GlobalTheory.ClassFin
