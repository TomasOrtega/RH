import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedStandardAdelicLatticePropertiesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

/- English proof (translation)
Set `φ : T →+ (ι → κ → S ⧸ Ideal.span {((k * n : ℕ) : S)})` to `AddMonoidHom.mk' (fun ζ i j => Ideal.Quotient.mk _ ⟨(k : A) * ζ.1 i j, hT _ ζ.2 i j⟩) (fun x y => by`. Use function extensionality and compare the values at `i j`. Rewrite using `[Pi.add_apply, Pi.add_apply, ← map_add]`. Use `congr 1`. Conclude with `Subtype.ext (mul_add _ _ _))`.

Establish `hle : φ.ker ≤ L.addSubgroupOf T`. Introduce `ζ hζ`. Rewrite using `[AddSubgroup.mem_addSubgroupOf]`. Use `hL _ fun i j => ?_` and prove the remaining obligations. Establish `h0 : Ideal.Quotient.mk (Ideal.span {((k * n : ℕ) : S)}) ⟨(k : A) * ζ.1 i j, hT _ ζ.2 i j⟩ = 0` using `congrFun (congrFun ((AddMonoidHom.mem_ker).1 hζ) i) j`.

Take `⟨s, hs⟩` from `Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)`. Establish `h1 : (s : A) * (((k * n : ℕ) : S) : A) = (k : A) * ζ.1 i j` using `congrArg Subtype.val hs`. Establish `h2 : ζ.1 i j = (n : A) * s`. Apply `hk.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[← h1]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`. Conclude with `hn _ s.2`. Establish `: φ.ker.FiniteIndex` using `AddSubgroup.finiteIndex_ker φ`.

Conclude with `(AddSubgroup.finiteIndex_of_le hle).index_ne_zero`.
-/
theorem relIndex_ne_zero_of_denom {A ι κ : Type} [CommRing A] [Finite ι] [Finite κ] (S : Subring A) (I : AddSubgroup A) (k n : ℕ)
    (hk : IsUnit (k : A)) (hfin : Finite (S ⧸ Ideal.span {((k * n : ℕ) : S)})) (hn : ∀ s ∈ S, (n : A) * s ∈ I)
    (L T : AddSubgroup (Matrix ι κ A)) (hL : ∀ ζ : Matrix ι κ A, (∀ i j, ζ i j ∈ I) → ζ ∈ L)
    (hT : ∀ ζ ∈ T, ∀ i j, (k : A) * ζ i j ∈ S) : L.relIndex T ≠ 0 := by
  let φ : T →+ (ι → κ → S ⧸ Ideal.span {((k * n : ℕ) : S)}) :=
    AddMonoidHom.mk' (fun ζ i j => Ideal.Quotient.mk _ ⟨(k : A) * ζ.1 i j, hT _ ζ.2 i j⟩) (fun x y => by
      funext i j
      rw [Pi.add_apply, Pi.add_apply, ← map_add]
      congr 1
      exact Subtype.ext (mul_add _ _ _))
  have hle : φ.ker ≤ L.addSubgroupOf T := by
    intro ζ hζ
    rw [AddSubgroup.mem_addSubgroupOf]
    refine hL _ fun i j => ?_
    have h0 : Ideal.Quotient.mk (Ideal.span {((k * n : ℕ) : S)}) ⟨(k : A) * ζ.1 i j, hT _ ζ.2 i j⟩ = 0 :=
      congrFun (congrFun ((AddMonoidHom.mem_ker).1 hζ) i) j
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    have h1 : (s : A) * (((k * n : ℕ) : S) : A) = (k : A) * ζ.1 i j := congrArg Subtype.val hs
    have h2 : ζ.1 i j = (n : A) * s := by
      apply hk.mul_left_cancel
      rw [← h1]
      push_cast
      ring
    rw [h2]
    exact hn _ s.2
  have : φ.ker.FiniteIndex := AddSubgroup.finiteIndex_ker φ
  exact (AddSubgroup.finiteIndex_of_le hle).index_ne_zero

/- English proof (translation)
Introduce `D hD cc δ hc N N' m hm T hT`. Take `⟨-, -, -, -, ⟨m₁, hm₁, h₁⟩, m₂, hm₂, h₂⟩` from `GlobalTheory.T.completedStandardAdelicLattice_properties D hD cc δ hc N N'`. Establish `hk : 0 < m₁ * m` using `Nat.mul_pos hm₁ hm`. Establish `hu : IsUnit ((m₁ * m : ℕ) : AE D)`. Use `(IsUnit.mk0 ((m₁ * m : ℕ) : D.host.E) (Nat.cast_ne_zero.2 hk.ne')).map (inc D)` as an intermediate fact.

Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Use `relIndex_ne_zero_of_denom (OhE D) (IhE D cc) (m₁ * m) m₂ hu (GlobalTheory.HeckeVal.finite_quot D _ (Nat.mul_pos hk hm₂)) h₂ _ _ (fun ζ h => mem_latA.2 h) fun ζ hζ i j => ?_` and prove the remaining obligations. Establish `h` using `h₁ _ (mem_latA.1 (hT ζ hζ) i j)`. Rewrite `h` using `[Matrix.smul_apply, nsmul_eq_mul, ← mul_assoc]`. Rewrite using `[Nat.cast_mul]` and apply the resulting hypothesis.
-/
theorem idx_latA_ne_zero : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' m : ℕ), 0 < m → ∀ T : Submodule (𝓞 D.host.E) (XA D N N'), (∀ ζ ∈ T, m • ζ ∈ latA D cc N N') → idx (latA D cc N N') T ≠ 0 := by
  intro D hD cc δ hc N N' m hm T hT
  obtain ⟨-, -, -, -, ⟨m₁, hm₁, h₁⟩, m₂, hm₂, h₂⟩ := GlobalTheory.T.completedStandardAdelicLattice_properties D hD cc δ hc N N'
  have hk : 0 < m₁ * m := Nat.mul_pos hm₁ hm
  have hu : IsUnit ((m₁ * m : ℕ) : AE D) := by
    have := (IsUnit.mk0 ((m₁ * m : ℕ) : D.host.E) (Nat.cast_ne_zero.2 hk.ne')).map (inc D)
    rwa [map_natCast] at this
  refine relIndex_ne_zero_of_denom (OhE D) (IhE D cc) (m₁ * m) m₂ hu
    (GlobalTheory.HeckeVal.finite_quot D _ (Nat.mul_pos hk hm₂)) h₂ _ _ (fun ζ h => mem_latA.2 h) fun ζ hζ i j => ?_
  have h := h₁ _ (mem_latA.1 (hT ζ hζ) i j)
  rw [Matrix.smul_apply, nsmul_eq_mul, ← mul_assoc] at h
  rwa [Nat.cast_mul]

end GlobalTheory.FinWeil
