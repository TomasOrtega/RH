import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CurveSemiAbelianConjecture
import Development.AutomorphicSpectrum.Statements.GeometryStatements.SeparableFormGroupElementFixesUniquePositiveLine
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Conj.SplitDisc

open Module

/- English proof (translation)
Use `(injective_iff_map_eq_zero g).2 fun x hx => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Establish `hne` using `Ideal.comap_ne_bot_of_integral_mem (R := ℤ) (I := RingHom.ker g) h (RingHom.mem_ker.2 hx) (Algebra.IsIntegral.isIntegral x)`. Apply `hne` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`.

Introduce `n hn`. Establish `h0 : g (algebraMap ℤ (𝓞 E) n) = 0` using `RingHom.mem_ker.1 (Ideal.mem_comap.1 hn)`. Establish `h1 : (n : L) = 0` using `by simpa using h0`. Simplify using `using h1`.
-/
theorem injective_of_charZero (E : Type) [Field E] [NumberField E] {L : Type} [Field L] [CharZero L]
    (g : 𝓞 E →+* L) : Function.Injective g := by
  refine (injective_iff_map_eq_zero g).2 fun x hx => ?_
  by_contra h
  have hne := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) (I := RingHom.ker g) h
    (RingHom.mem_ker.2 hx) (Algebra.IsIntegral.isIntegral x)
  apply hne
  rw [eq_bot_iff]
  intro n hn
  have h0 : g (algebraMap ℤ (𝓞 E) n) = 0 := RingHom.mem_ker.1 (Ideal.mem_comap.1 hn)
  have h1 : (n : L) = 0 := by simpa using h0
  simpa using h1

/- English proof (translation)
Set `F` to `FractionRing R`. Set `Ω` to `AlgebraicClosure F`. Set `i₀ : R →+* Ω` to `(algebraMap F Ω).comp (algebraMap R F)`. Establish `hi₀ : Function.Injective i₀` using `(algebraMap F Ω).injective.comp (IsFractionRing.injective R F)`. Establish `: CharZero Ω` using `charZero_of_injective_ringHom hi₀`.

Set `ρ : S → (𝓞 E →+* Ω)` to `fun s => i₀.comp (σ s)`. Establish `hρ : ∀ s, Function.Injective (ρ s)` using `fun s => injective_of_charZero E (ρ s)`. Set `τ : S → (E →ₐ[ℚ] Ω)` to `fun s => (IsFractionRing.lift (hρ s)).toRatAlgHom`. Establish `hτ : ∀ s (a : 𝓞 E), τ s (algebraMap (𝓞 E) E a) = i₀ (σ s a)` using `fun s a => by`. Express the relevant statement in the definitionally equal form `IsFractionRing.lift (hρ s) (algebraMap (𝓞 E) E a) = _`.

Rewrite using `[IsFractionRing.lift_algebraMap]`. Both sides reduce to the same expression. Establish `hinj : Function.Injective τ`. Introduce `s t hst`. Apply `hσ` to reduce the goal to its premises.

Use extensionality with `a`. Apply `hi₀` to reduce the goal to its premises. Rewrite using `[← hτ, ← hτ, hst]`. Establish `hbij : Function.Bijective τ` using `(Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, by rw [AlgHom.card, hc]⟩`. Set `e' : Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →ₐ[ℚ] Ω)` to `e.trans (Equiv.ofBijective τ hbij)`.

Establish `key` using `Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ Ω (integralBasis E) e'`. Rewrite `key` using `[← coe_discr]`. Establish `hm : Algebra.embeddingsMatrixReindex ℚ Ω (integralBasis E) e' = (Matrix.of fun i j => σ (e j) (RingOfIntegers.basis E i)).map i₀`. Use extensionality with `i j`. Simplify using `only [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, Matrix.map_apply, integralBasis_apply]`.

Conclude with `hτ _ _`. Rewrite `key` using `[hm, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← map_pow]`. Apply `hi₀` to reduce the goal to its premises. Rewrite using `[← key]`. Simplify using the standard rewrite rules.
-/
theorem det_sq_eq_discr (E : Type) [Field E] [NumberField E] (R S : Type) [CommRing R] [IsDomain R] [CharZero R]
    [Fintype S] [DecidableEq S] (σ : S → (𝓞 E →+* R)) (hσ : Function.Injective σ)
    (hc : Fintype.card S = finrank ℚ E) (e : Free.ChooseBasisIndex ℤ (𝓞 E) ≃ S) :
    (Matrix.of fun i j => σ (e j) (RingOfIntegers.basis E i)).det ^ 2 = (NumberField.discr E : R) := by
  let F := FractionRing R
  let Ω := AlgebraicClosure F
  let i₀ : R →+* Ω := (algebraMap F Ω).comp (algebraMap R F)
  have hi₀ : Function.Injective i₀ :=
    (algebraMap F Ω).injective.comp (IsFractionRing.injective R F)
  have : CharZero Ω := charZero_of_injective_ringHom hi₀
  let ρ : S → (𝓞 E →+* Ω) := fun s => i₀.comp (σ s)
  have hρ : ∀ s, Function.Injective (ρ s) := fun s => injective_of_charZero E (ρ s)
  let τ : S → (E →ₐ[ℚ] Ω) := fun s => (IsFractionRing.lift (hρ s)).toRatAlgHom
  have hτ : ∀ s (a : 𝓞 E), τ s (algebraMap (𝓞 E) E a) = i₀ (σ s a) := fun s a => by
    change IsFractionRing.lift (hρ s) (algebraMap (𝓞 E) E a) = _
    rw [IsFractionRing.lift_algebraMap]
    rfl
  have hinj : Function.Injective τ := by
    intro s t hst
    apply hσ
    ext a
    apply hi₀
    rw [← hτ, ← hτ, hst]
  have hbij : Function.Bijective τ :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, by rw [AlgHom.card, hc]⟩
  let e' : Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →ₐ[ℚ] Ω) := e.trans (Equiv.ofBijective τ hbij)
  have key := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ Ω (integralBasis E) e'
  rw [← coe_discr] at key
  have hm : Algebra.embeddingsMatrixReindex ℚ Ω (integralBasis E) e' =
      (Matrix.of fun i j => σ (e j) (RingOfIntegers.basis E i)).map i₀ := by
    ext i j
    simp only [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.of_apply, Matrix.map_apply, integralBasis_apply]
    exact hτ _ _
  rw [hm, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← map_pow] at key
  apply hi₀
  rw [← key]
  simp

/- English proof (translation)
Unfold `IsSplit`. Set `B` to `Algebra.TensorProduct.basis k b`. Set `B'` to `(Pi.basisFun k S).reindex e.symm`. Set `f` to `(Algebra.TensorProduct.lift (Algebra.ofId k (S → k)) (AlgHom.pi fun s => (χ s).toIntAlgHom) (fun _ _ => Commute.all _ _))`. Establish `hm : LinearMap.toMatrix B B' f.toLinearMap = (Matrix.of fun i j => χ (e j) (b i)).transpose`.

Use extensionality with `i j`. Simplify using `[LinearMap.toMatrix_apply, B, B', f]`. Establish `hu : IsUnit (LinearMap.toMatrix B B' f.toLinearMap).det`. Rewrite using `[hm, Matrix.det_transpose]`. Conclude with `isUnit_iff_ne_zero.2 h`.

Conclude with `(LinearEquiv.ofIsUnitDet hu).bijective`.
-/
theorem isSplit_of_det {O k S ι : Type} [CommRing O] [Field k] [Fintype S] [DecidableEq S] [Fintype ι] [DecidableEq ι]
    (χ : S → (O →+* k)) (b : Basis ι ℤ O) (e : ι ≃ S)
    (h : (Matrix.of fun i j => χ (e j) (b i)).det ≠ 0) : IsSplit χ := by
  unfold IsSplit
  let B := Algebra.TensorProduct.basis k b
  let B' := (Pi.basisFun k S).reindex e.symm
  let f := (Algebra.TensorProduct.lift (Algebra.ofId k (S → k)) (AlgHom.pi fun s => (χ s).toIntAlgHom)
    (fun _ _ => Commute.all _ _))
  have hm : LinearMap.toMatrix B B' f.toLinearMap = (Matrix.of fun i j => χ (e j) (b i)).transpose := by
    ext i j
    simp [LinearMap.toMatrix_apply, B, B', f]
  have hu : IsUnit (LinearMap.toMatrix B B' f.toLinearMap).det := by
    rw [hm, Matrix.det_transpose]
    exact isUnit_iff_ne_zero.2 h
  exact (LinearEquiv.ofIsUnitDet hu).bijective

/- English proof (translation)
Establish `hchar : CharP K p` using `charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p`. Establish `hmem : ∀ s a, (π.comp (σ s)) a ∈ algebraicClosure (ZMod p) K` using `fun s a => by`. Establish `h1 : IsIntegral ℤ ((π.comp (σ s)) a)` using `(Algebra.IsIntegral.isIntegral (R := ℤ) a).map (π.comp (σ s)).toIntAlgHom`. Conclude with `mem_algebraicClosure_iff'.2 (h1.tower_top)`. Set `χ : S → (𝓞 E →+* algebraicClosure (ZMod p) K)` to `fun s => (π.comp (σ s)).codRestrict (algebraicClosure (ZMod p) K) (hmem s)`.

Use `⟨χ, ?_, fun s a => rfl⟩` and prove the remaining obligations. Establish `hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 E)) = Fintype.card S`. Rewrite using `[hc, finrank_eq_card_basis (integralBasis E)]`. Set `e : Free.ChooseBasisIndex ℤ (𝓞 E) ≃ S` to `Fintype.equivOfCardEq hcard`. Use `isSplit_of_det χ (RingOfIntegers.basis E) e fun h0 => hp ?_` and prove the remaining obligations.

Establish `hsq` using `congrArg π (det_sq_eq_discr E R S σ hσ hc e)`. Establish `hmap : (algebraMap (algebraicClosure (ZMod p) K) K).mapMatrix (Matrix.of fun i j => χ (e j) (RingOfIntegers.basis E i)) = π.mapMatrix (Matrix.of fun i j => σ (e j) (RingOfIntegers.basis E i))`. Use extensionality with `i j`. Both sides reduce to the same expression. Establish `hdet : π (Matrix.of fun i j => σ (e j) (RingOfIntegers.basis E i)).det = 0`.

Rewrite using `[RingHom.map_det, ← hmap, ← RingHom.map_det]`. Simplify using `[h0]`. Rewrite `hsq` using `[map_pow, hdet]`. Establish `hz : ((NumberField.discr E : ℤ) : K) = 0`. Simplify using `using hsq.symm`.

Conclude with `(CharP.intCast_eq_zero_iff K p _).1 hz`.
-/
theorem exists_isSplit (E : Type) [Field E] [NumberField E] (R K S : Type) [CommRing R] [IsDomain R] [CharZero R]
    [Field K] [Fintype S] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K] (σ : S → (𝓞 E →+* R)) (π : R →+* K)
    (hσ : Function.Injective σ) (hc : Fintype.card S = finrank ℚ E) (hp : ¬ (p : ℤ) ∣ NumberField.discr E) :
    ∃ χ : S → (𝓞 E →+* algebraicClosure (ZMod p) K), IsSplit χ ∧
      ∀ s a, ((χ s a : algebraicClosure (ZMod p) K) : K) = π (σ s a) := by
  classical
  have hchar : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  have hmem : ∀ s a, (π.comp (σ s)) a ∈ algebraicClosure (ZMod p) K := fun s a => by
    have h1 : IsIntegral ℤ ((π.comp (σ s)) a) :=
      (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (π.comp (σ s)).toIntAlgHom
    exact mem_algebraicClosure_iff'.2 (h1.tower_top)
  let χ : S → (𝓞 E →+* algebraicClosure (ZMod p) K) := fun s =>
    (π.comp (σ s)).codRestrict (algebraicClosure (ZMod p) K) (hmem s)
  refine ⟨χ, ?_, fun s a => rfl⟩
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 E)) = Fintype.card S := by
    rw [hc, finrank_eq_card_basis (integralBasis E)]
  let e : Free.ChooseBasisIndex ℤ (𝓞 E) ≃ S := Fintype.equivOfCardEq hcard
  refine isSplit_of_det χ (RingOfIntegers.basis E) e fun h0 => hp ?_
  have hsq := congrArg π (det_sq_eq_discr E R S σ hσ hc e)
  have hmap : (algebraMap (algebraicClosure (ZMod p) K) K).mapMatrix
      (Matrix.of fun i j => χ (e j) (RingOfIntegers.basis E i)) =
      π.mapMatrix (Matrix.of fun i j => σ (e j) (RingOfIntegers.basis E i)) := by
    ext i j
    rfl
  have hdet : π (Matrix.of fun i j => σ (e j) (RingOfIntegers.basis E i)).det = 0 := by
    rw [RingHom.map_det, ← hmap, ← RingHom.map_det]
    simp [h0]
  rw [map_pow, hdet] at hsq
  have hz : ((NumberField.discr E : ℤ) : K) = 0 := by
    simpa using hsq.symm
  exact (CharP.intCast_eq_zero_iff K p _).1 hz

end GlobalTheory.CompanionTheory.Ar.Conj.SplitDisc
