import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

/- English proof (translation)
Establish `hintF : IsIntegral ℤ (c : F)` using `NumberField.RingOfIntegers.isIntegral_coe c`. Use `⟨(minpoly ℤ c).map (algebraMap ℤ ℂ), ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : minpoly ℚ (c : F) = (minpoly ℤ (c : F)).map (algebraMap ℤ ℚ)` using `minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hintF`. Establish `h2 : (minpoly ℚ (c : F)).Separable` using `(minpoly.irreducible (hintF.tower_top (A := ℚ))).separable`. Establish `h3` using `h2.map (f := algebraMap ℚ ℂ)`.

Rewrite `h3` using `[h1, Polynomial.map_map, NumberField.RingOfIntegers.minpoly_coe]`. Establish `h4 : (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = algebraMap ℤ ℂ` using `RingHom.ext_int _ _`. Rewrite `h3` using `[h4]`. Then use the resulting hypothesis. Rewrite using `[aeval_map_algebraMap]`. Establish `h` using `aeval_algHom_apply f.toIntAlgHom c (minpoly ℤ c)`.

Rewrite `h` using `[minpoly.aeval, map_zero]`. Conclude with `h`.
-/
private theorem sep_kill {F : Type} [Field F] [NumberField F] {g : ℕ}
    (f : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (c : 𝓞 F) :
    ∃ p : ℂ[X], p.Separable ∧ aeval (f c) p = 0 := by
  have hintF : IsIntegral ℤ (c : F) := NumberField.RingOfIntegers.isIntegral_coe c
  refine ⟨(minpoly ℤ c).map (algebraMap ℤ ℂ), ?_, ?_⟩
  · have h1 : minpoly ℚ (c : F) = (minpoly ℤ (c : F)).map (algebraMap ℤ ℚ) :=
      minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hintF
    have h2 : (minpoly ℚ (c : F)).Separable :=
      (minpoly.irreducible (hintF.tower_top (A := ℚ))).separable
    have h3 := h2.map (f := algebraMap ℚ ℂ)
    rw [h1, Polynomial.map_map, NumberField.RingOfIntegers.minpoly_coe] at h3
    have h4 : (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = algebraMap ℤ ℂ := RingHom.ext_int _ _
    rwa [h4] at h3
  · rw [aeval_map_algebraMap]
    have h := aeval_algHom_apply f.toIntAlgHom c (minpoly ℤ c)
    rw [minpoly.aeval, map_zero] at h
    exact h

/- English proof (translation)
Take `⟨Sb, e, hdet, he⟩` from `hSim g (𝓞 F) (fun c => ρ (a c)) (fun c c' => (Commute.all c c').map (ρ.comp a)) (fun c => sep_kill (ρ.comp (a)) c)`. Establish `hu : IsUnit Sb.det` using `isUnit_iff_ne_zero.mpr hdet`. Establish `hinj : ∀ x y : Fin g → ℂ, Sb * Matrix.diagonal x = Sb * Matrix.diagonal y → x = y`. Introduce `x y h`. Establish `h' : Matrix.diagonal x = Matrix.diagonal y`.

Use `congrArg (fun m => Sb⁻¹ * m) h` as an intermediate fact. Rewrite `this` using `[← _root_.mul_assoc, ← _root_.mul_assoc, Matrix.nonsing_inv_mul _ hu, _root_.one_mul, _root_.one_mul]`. Then use the resulting hypothesis. Conclude with `Matrix.diagonal_injective h'`. Establish `hadd : ∀ c c', e (c + c') = e c + e c'`. Introduce `c c'`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[← he, map_add, map_add, add_mul, he, he, ← mul_add, Matrix.diagonal_add]`. Apply the tactic sequence `try rfl`. Establish `hmul : ∀ c c', e (c * c') = e c * e c'`. Introduce `c c'`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[← he, map_mul, map_mul, _root_.mul_assoc, he, ← _root_.mul_assoc, he, _root_.mul_assoc, Matrix.diagonal_mul_diagonal]`. Apply the tactic sequence `try rfl`. Establish `hone : e 1 = 1`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[← he, map_one, map_one, _root_.one_mul]`. Use `show Sb = Sb * Matrix.diagonal (fun _ => 1)`. Rewrite using `[Matrix.diagonal_one, _root_.mul_one]`. Establish `hzero : e 0 = 0`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[← he, map_zero, map_zero, zero_mul]`. Use `show 0 = Sb * Matrix.diagonal (fun _ => 0)`. Rewrite using `[Matrix.diagonal_zero, mul_zero]`. Set `φ : Fin g → (𝓞 F →+* ℂ)` to `fun i => { toFun := fun c => e c i map_one' := by rw [hone]; rfl map_mul' := fun c c' => by rw [hmul]; rfl map_zero' := by rw [hzero]; rfl map_add' := fun c c' => by rw [hadd]; rfl }`. Use `choose ty hty using fun i => hExt F (φ i)`.

Use `⟨Sb, ty, hdet, ?_, ?_⟩` and prove the remaining obligations. Introduce `c`. Establish `: (fun i => ty i (c : F)) = e c`. Use function extensionality and compare the values at `i`. Conclude with `(hty i c).symm`.

Rewrite using `[this]`. Conclude with `he c`. Simplify using the standard rewrite rules.
-/
private theorem diag_one {F : Type} [Field F] [NumberField F] {O : Type} [Ring O] {g : ℕ}
    (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (hSim : SimDiag) (hExt : ExtendEmb) :
    ∃ (Sb : Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (F →+* ℂ)), IsDiag a ρ 1 Sb ty (fun _ => 1) := by
  obtain ⟨Sb, e, hdet, he⟩ := hSim g (𝓞 F) (fun c => ρ (a c))
    (fun c c' => (Commute.all c c').map (ρ.comp a)) (fun c => sep_kill (ρ.comp (a)) c)
  have hu : IsUnit Sb.det := isUnit_iff_ne_zero.mpr hdet
  have hinj : ∀ x y : Fin g → ℂ, Sb * Matrix.diagonal x = Sb * Matrix.diagonal y → x = y := by
    intro x y h
    have h' : Matrix.diagonal x = Matrix.diagonal y := by
      have := congrArg (fun m => Sb⁻¹ * m) h
      rwa [← _root_.mul_assoc, ← _root_.mul_assoc, Matrix.nonsing_inv_mul _ hu, _root_.one_mul, _root_.one_mul] at this
    exact Matrix.diagonal_injective h'
  have hadd : ∀ c c', e (c + c') = e c + e c' := by
    intro c c'
    apply hinj
    rw [← he, map_add, map_add, add_mul, he, he, ← mul_add, Matrix.diagonal_add]
    try rfl
  have hmul : ∀ c c', e (c * c') = e c * e c' := by
    intro c c'
    apply hinj
    rw [← he, map_mul, map_mul, _root_.mul_assoc, he, ← _root_.mul_assoc, he, _root_.mul_assoc,
      Matrix.diagonal_mul_diagonal]
    try rfl
  have hone : e 1 = 1 := by
    apply hinj
    rw [← he, map_one, map_one, _root_.one_mul]
    show Sb = Sb * Matrix.diagonal (fun _ => 1)
    rw [Matrix.diagonal_one, _root_.mul_one]
  have hzero : e 0 = 0 := by
    apply hinj
    rw [← he, map_zero, map_zero, zero_mul]
    show 0 = Sb * Matrix.diagonal (fun _ => 0)
    rw [Matrix.diagonal_zero, mul_zero]
  let φ : Fin g → (𝓞 F →+* ℂ) := fun i =>
    { toFun := fun c => e c i
      map_one' := by rw [hone]; rfl
      map_mul' := fun c c' => by rw [hmul]; rfl
      map_zero' := by rw [hzero]; rfl
      map_add' := fun c c' => by rw [hadd]; rfl }
  choose ty hty using fun i => hExt F (φ i)
  refine ⟨Sb, ty, hdet, ?_, ?_⟩
  · intro c
    have : (fun i => ty i (c : F)) = e c := by
      funext i
      exact (hty i c).symm
    rw [this]
    exact he c
  · simp

/- English proof (translation)
Introduce `hSim hExt hTC _ hBall F _ _ O _ bar g ρ a n t₀ ε hS D P₀ M₀ hP hM`. Take `⟨Sb, ty, hD⟩` from `diag_one (F := F) ρ a hSim hExt`. Establish `hcard : (evAt ty (fun _ => (1 : ℂ)) t₀).card = 1`. Establish `h` using `(hTC F O bar g ρ a n t₀ ε hS 1 Sb ty (fun _ => 1) hD t₀).1`. Simplify `h` using `[typeMult]`.

Take `⟨mu, hmu⟩` from `Multiset.card_eq_one.mp hcard`. Set `B` to `Module.finBasis ℂ (Csp bar ρ M₀)`. Set `co : (Fin (Module.finrank ℂ (Csp bar ρ M₀)) → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ` to `(Csp bar ρ M₀).subtype ∘ₗ B.equivFun.symm.toLinearMap`. Establish `hco : IsCoordC bar ρ M₀ co`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Conclude with `(Submodule.injective_subtype _).comp B.equivFun.symm.injective`. Rewrite using `[LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]`. Establish `hd` using `(hBall F O bar g ρ a n t₀ ε hS D P₀ M₀ hP hM 1 (by simp) Sb ty (fun _ => 1) hD mu hmu _ co hco LinearMap.id (fun b => by simp)).1`. Rewrite using `[← hd]`. Conclude with `⟨co, hco⟩`.
-/
theorem UpperTheory.Gal.W2.cspDim_of :
    UpperTheory.Gal.W2.SimDiag → UpperTheory.Gal.W2.ExtendEmb → UpperTheory.Gal.W2.TypeCount → UpperTheory.Gal.W2.MarkDiag → UpperTheory.Gal.W2.BallChar → UpperTheory.Gal.W2.CspDim := by
  intro hSim hExt hTC _ hBall F _ _ O _ bar g ρ a n t₀ ε hS D P₀ M₀ hP hM
  obtain ⟨Sb, ty, hD⟩ := diag_one (F := F) ρ a hSim hExt
  have hcard : (evAt ty (fun _ => (1 : ℂ)) t₀).card = 1 := by
    have h := (hTC F O bar g ρ a n t₀ ε hS 1 Sb ty (fun _ => 1) hD t₀).1
    simpa [typeMult] using h
  obtain ⟨mu, hmu⟩ := Multiset.card_eq_one.mp hcard
  let B := Module.finBasis ℂ (Csp bar ρ M₀)
  let co : (Fin (Module.finrank ℂ (Csp bar ρ M₀)) → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ :=
    (Csp bar ρ M₀).subtype ∘ₗ B.equivFun.symm.toLinearMap
  have hco : IsCoordC bar ρ M₀ co := by
    refine ⟨?_, ?_⟩
    · exact (Submodule.injective_subtype _).comp B.equivFun.symm.injective
    · rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  have hd := (hBall F O bar g ρ a n t₀ ε hS D P₀ M₀ hP hM 1 (by simp) Sb ty (fun _ => 1) hD mu hmu
    _ co hco LinearMap.id (fun b => by simp)).1
  rw [← hd]
  exact ⟨co, hco⟩
