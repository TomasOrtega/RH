import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

/- English proof (translation)
Use `conv_lhs => rw [← b.sum_repr w]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h` using `map_ratCast_smul f ℚ ℝ (b.repr w i) (b i)`. Simplify using `using h`.
-/
private theorem add_expand {V A : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup A] [Module ℝ A]
    {n : ℕ} (b : Module.Basis (Fin n) ℚ V) (f : V →+ A) (w : V) :
    f w = ∑ i, ((b.repr w i : ℚ) : ℝ) • f (b i) := by
  conv_lhs => rw [← b.sum_repr w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := map_ratCast_smul f ℚ ℝ (b.repr w i) (b i)
  simpa using h

/- English proof (translation)
Rewrite using `[← hs]`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[add_expand b f w]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
private theorem span_basis {V A : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup A] [Module ℝ A]
    {n : ℕ} (b : Module.Basis (Fin n) ℚ V) (f : V →+ A)
    (hs : Submodule.span ℝ (Set.range f) = ⊤) :
    ⊤ ≤ Submodule.span ℝ (Set.range (fun i => f (b i))) := by
  rw [← hs]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨w, rfl⟩
  rw [add_expand b f w]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Set `b` to `Module.finBasis ℚ V`. Set `bA : Module.Basis (Fin (Module.finrank ℚ V)) ℝ A` to `basisOfTopLeSpanOfCardEqFinrank (fun i => th (b i)) (span_basis b th hA) (by simp [dA])`. Set `bB : Module.Basis (Fin (Module.finrank ℚ V)) ℝ B` to `basisOfTopLeSpanOfCardEqFinrank (fun i => Q (b i)) (span_basis b Q hB) (by simp [dB])`. Use `⟨bA.equiv bB (Equiv.refl _), fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[add_expand b th w, add_expand b Q w, map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`. Use `congr 1`. Establish `h1 : bA i = th (b i)` using `by simp [bA]`. Establish `h2 : bB i = Q (b i)` using `by simp [bB]`.

Rewrite using `[← h1, ← h2, Module.Basis.equiv_apply]`. Both sides reduce to the same expression.
-/
private theorem equiv_of_spans {V A B : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    [AddCommGroup A] [Module ℝ A] [FiniteDimensional ℝ A] [AddCommGroup B] [Module ℝ B]
    [FiniteDimensional ℝ B] (th : V →+ A) (Q : V →+ B)
    (hA : Submodule.span ℝ (Set.range th) = ⊤) (hB : Submodule.span ℝ (Set.range Q) = ⊤)
    (dA : Module.finrank ℝ A = Module.finrank ℚ V) (dB : Module.finrank ℝ B = Module.finrank ℚ V) :
    ∃ R : A ≃ₗ[ℝ] B, ∀ w, Q w = R (th w) := by
  let b := Module.finBasis ℚ V
  let bA : Module.Basis (Fin (Module.finrank ℚ V)) ℝ A :=
    basisOfTopLeSpanOfCardEqFinrank (fun i => th (b i)) (span_basis b th hA) (by simp [dA])
  let bB : Module.Basis (Fin (Module.finrank ℚ V)) ℝ B :=
    basisOfTopLeSpanOfCardEqFinrank (fun i => Q (b i)) (span_basis b Q hB) (by simp [dB])
  refine ⟨bA.equiv bB (Equiv.refl _), fun w => ?_⟩
  rw [add_expand b th w, add_expand b Q w, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  congr 1
  have h1 : bA i = th (b i) := by simp [bA]
  have h2 : bB i = Q (b i) := by simp [bB]
  rw [← h1, ← h2, Module.Basis.equiv_apply]
  rfl

/- English proof (translation)
Introduce `p _ D G L A β ρ Q hQ`. Use `haveI : Module.Finite ℤ D.La := D.finLa`. Use `haveI : Module.Finite ℚ (VQ D) := Module.Finite.base_change ℤ ℚ D.La`. Use `equiv_of_spans A.th Q A.span hQ.2.1 A.dim ?_` and prove the remaining obligations. Rewrite using `[← A.dim, A.dimg]`.

Simplify using `[Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]`.
-/
theorem UpperTheory.Gal.W2.perExt_of :
    UpperTheory.Gal.W2.PerExt := by
  intro p _ D G L A β ρ Q hQ
  haveI : Module.Finite ℤ D.La := D.finLa
  haveI : Module.Finite ℚ (VQ D) := Module.Finite.base_change ℤ ℚ D.La
  refine equiv_of_spans A.th Q A.span hQ.2.1 A.dim ?_
  rw [← A.dim, A.dimg]
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
