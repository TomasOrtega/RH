import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableLatticeDescentUnramified
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MatrixDescent

/- English proof (translation)
Use `choose f hf using h1`. Use `choose f' hf' using h2`. Establish `hl : Function.LeftInverse f' f`. Introduce `x`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[← hf', ← hf]`. Simplify using the standard rewrite rules. Establish `hr : Function.RightInverse f' f`. Introduce `x`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[← hf, ← hf']`. Simplify using the standard rewrite rules. Establish `hm : ∀ x y, f (x * y) = f x * f y`. Introduce `x y`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[map_mul, ← hf, ← hf, ← hf, map_mul, map_mul]`. Establish `ha : ∀ x y, f (x + y) = f x + f y`. Introduce `x y`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_add, ← hf, ← hf, ← hf, map_add, map_add]`.

Establish `hc : ∀ r : R, f (algebraMap R W r) = algebraMap R W r`. Introduce `r`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[← hf, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R K K', AlgEquiv.commutes]`. Set `τ : W ≃ₐ[R] W` to `{ toFun := f invFun := f' left_inv := hl right_inv := hr map_mul' := hm map_add' := ha commutes' := hc }`.

Conclude with `⟨τ, fun x => (hf x).symm⟩`.
-/
theorem exists_restrict (R K W K' : Type) [CommRing R] [Field K] [Algebra R K] [CommRing W]
    [Field K'] [Algebra W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K']
    [IsScalarTower R K K'] (hinj : Function.Injective (algebraMap W K')) (σ : K' ≃ₐ[K] K')
    (h1 : ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y)
    (h2 : ∀ x : W, ∃ y : W, σ.symm (algebraMap W K' x) = algebraMap W K' y) :
    ∃ τ : W ≃ₐ[R] W, ∀ x : W, algebraMap W K' (τ x) = σ (algebraMap W K' x) := by
  choose f hf using h1
  choose f' hf' using h2
  have hl : Function.LeftInverse f' f := by
    intro x; apply hinj; rw [← hf', ← hf]; simp
  have hr : Function.RightInverse f' f := by
    intro x; apply hinj; rw [← hf, ← hf']; simp
  have hm : ∀ x y, f (x * y) = f x * f y := by
    intro x y; apply hinj; rw [map_mul, ← hf, ← hf, ← hf, map_mul, map_mul]
  have ha : ∀ x y, f (x + y) = f x + f y := by
    intro x y; apply hinj; rw [map_add, ← hf, ← hf, ← hf, map_add, map_add]
  have hc : ∀ r : R, f (algebraMap R W r) = algebraMap R W r := by
    intro r; apply hinj; rw [← hf, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R K K', AlgEquiv.commutes]
  let τ : W ≃ₐ[R] W :=
    { toFun := f
      invFun := f'
      left_inv := hl
      right_inv := hr
      map_mul' := hm
      map_add' := ha
      commutes' := hc }
  exact ⟨τ, fun x => (hf x).symm⟩

/- English proof (translation)
Establish `: Matrix.vecMul v g ∈ LinearMap.range g.vecMulLinear` using `⟨v, rfl⟩`. Rewrite `this` using `[range_vecMulLinear]`. Conclude with `this`.
-/
theorem vecMul_mem_span {W : Type} [CommRing W] {n : ℕ} (g : Matrix (Fin n) (Fin n) W)
    (v : Fin n → W) : Matrix.vecMul v g ∈ Submodule.span W (Set.range g) := by
  have : Matrix.vecMul v g ∈ LinearMap.range g.vecMulLinear := ⟨v, rfl⟩
  rw [range_vecMulLinear] at this
  exact this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hv`. Establish `: v ∈ LinearMap.range g.vecMulLinear` using `by rw [range_vecMulLinear]; exact hv`. Take `⟨a, ha⟩` from `this`. Conclude with `⟨a, ha⟩`.

Introduce and unpack `⟨a, rfl⟩`. Conclude with `vecMul_mem_span g a`.
-/
theorem mem_span_iff_vecMul {W : Type} [CommRing W] {n : ℕ} (g : Matrix (Fin n) (Fin n) W)
    (v : Fin n → W) : v ∈ Submodule.span W (Set.range g) ↔ ∃ a, Matrix.vecMul a g = v := by
  constructor
  · intro hv
    have : v ∈ LinearMap.range g.vecMulLinear := by rw [range_vecMulLinear]; exact hv
    obtain ⟨a, ha⟩ := this
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩; exact vecMul_mem_span g a

/- English proof (translation)
Use `set N := Submodule.span W (Set.range g) with hNdef`. Set `φ : (Fin n → R) →ₗ[R] (Fin n → W)` to `{ toFun := fun a i => algebraMap R W (a i) map_add' := by intro a b; funext i; simp map_smul' := by intro c a; funext i; simp [Algebra.smul_def] }`. Establish `hφ : ∀ a i, φ a i = algebraMap R W (a i)` using `fun _ _ => rfl`. Set `N₀ : Submodule R (Fin n → R)` to `(N.restrictScalars R).comap φ`. Establish `hdN₀ : ∀ a : Fin n → R, d • a ∈ N₀`.

Introduce `a`. Use `show φ (d • a) ∈ N`. Rewrite using `[map_smul, ← algebraMap_smul W d (φ a)]`. Conclude with `hdN _`. Take `⟨m, b⟩` from `Submodule.basisOfPid (Pi.basisFun R (Fin n)) N₀`.

Establish `hmn : m = n`. Establish `e : Module.finrank R N₀ = m` using `by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← e]`. Conclude with `(Submodule.finrank_le N₀).trans (Module.finrank_fin_fun R).le`.

Use `haveI : Module.Finite R N₀ := Module.Finite.of_basis b`. Set `ψ : (Fin n → R) →ₗ[R] N₀` to `(d • LinearMap.id).codRestrict N₀ hdN₀`. Establish `hψ : Function.Injective ψ`. Introduce `a a' haa`. Use `congrArg Subtype.val haa` as an intermediate fact.

Conclude with `smul_right_injective (Fin n → R) hd this`. Use `LinearMap.finrank_le_finrank_of_injective hψ` as an intermediate fact. Rewrite `this` using `[Module.finrank_fin_fun, e]`. Then use the resulting hypothesis. Set `b' : Module.Basis (Fin n) R N₀` to `b.reindex (finCongr hmn)`. Set `A : Matrix (Fin n) (Fin n) R` to `Matrix.of fun i => (b' i : Fin n → R)`.

Use `set B := A.map (algebraMap R W) with hBdef`. Establish `hBφ : ∀ i, B i = φ (b' i)` using `fun i => rfl`. Establish `hBN : ∀ i, B i ∈ N` using `fun i => (b' i).2`. Use `choose h₀ hh using fun i => (mem_span_iff_vecMul g (B i)).mp (hBN i)`. Use `set h : Matrix (Fin n) (Fin n) W := Matrix.of h₀ with hhdef`.

Establish `hAh : A.map (algebraMap R W) = h * g`. Use extensionality with `i j`. Rewrite using `[← hBdef, ← hh i]`. Simplify using `[hhdef, Matrix.mul_apply, Matrix.vecMul, dotProduct]`. Establish `hN₀B : ∀ x : N₀, φ x ∈ Submodule.span W (Set.range B)`.

Introduce `x`. Establish `hx` using `congrArg Subtype.val (b'.sum_repr x)`. Rewrite using `[← hx, Submodule.coe_sum, map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, map_smul, ← hBφ]`.

Conclude with `Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `hNB : N ≤ Submodule.span W (Set.range B)`. Rewrite using `[hspan, Submodule.span_le]`. Introduce and unpack `v ⟨hvN, hvR⟩`. Use `choose a ha using hvR`.

Establish `hva : v = φ a` using `by funext i; rw [hφ, ha]`. Establish `haN : a ∈ N₀` using `by show φ a ∈ N; rw [← hva]; exact hvN`. Rewrite using `[hva]`. Conclude with `hN₀B ⟨a, haN⟩`. Use `choose h₁ hh' using fun i => (mem_span_iff_vecMul B (g i)).mp (hNB (Submodule.subset_span ⟨i, rfl⟩))`.

Use `set h' : Matrix (Fin n) (Fin n) W := Matrix.of h₁ with hh'def`. Establish `hgB : h' * B = g`. Use extensionality with `i j`. Rewrite using `[← hh' i]`. Simplify using `[hh'def, Matrix.mul_apply, Matrix.vecMul, dotProduct]`.

Establish `hinv : h' * h = 1`. Establish `e : (h' * h) * g = g` using `by rw [Matrix.mul_assoc, ← hAh, ← hBdef, hgB]`. Establish `e2 : g.det • (h' * h - 1) = 0`. Establish `: (h' * h - 1) * (g * g.adjugate) = 0`. Rewrite using `[← Matrix.mul_assoc, Matrix.sub_mul, e, Matrix.one_mul, sub_self, Matrix.zero_mul]`.

Rewrite `this` using `[Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]`. Then use the resulting hypothesis. Conclude with `sub_eq_zero.mp ((smul_eq_zero.mp e2).resolve_left hg)`. Conclude with `⟨A, h, Matrix.isUnit_det_of_left_inverse hinv, hAh⟩`.
-/
theorem rational_rows (R W : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing W] [IsDomain W] [Algebra R W] (hinj : Function.Injective (algebraMap R W))
    (n : ℕ) (g : Matrix (Fin n) (Fin n) W) (hg : g.det ≠ 0) (d : R) (hd : d ≠ 0)
    (hdN : ∀ w : Fin n → W, algebraMap R W d • w ∈ Submodule.span W (Set.range g))
    (hspan : Submodule.span W (Set.range g) = Submodule.span W
      {v | v ∈ Submodule.span W (Set.range g) ∧ ∀ i, v i ∈ Set.range (algebraMap R W)}) :
    ∃ (A : Matrix (Fin n) (Fin n) R) (h : Matrix (Fin n) (Fin n) W),
      IsUnit h.det ∧ A.map (algebraMap R W) = h * g := by
  classical
  set N := Submodule.span W (Set.range g) with hNdef
  let φ : (Fin n → R) →ₗ[R] (Fin n → W) :=
    { toFun := fun a i => algebraMap R W (a i)
      map_add' := by intro a b; funext i; simp
      map_smul' := by intro c a; funext i; simp [Algebra.smul_def] }
  have hφ : ∀ a i, φ a i = algebraMap R W (a i) := fun _ _ => rfl

  let N₀ : Submodule R (Fin n → R) := (N.restrictScalars R).comap φ
  have hdN₀ : ∀ a : Fin n → R, d • a ∈ N₀ := by
    intro a
    show φ (d • a) ∈ N
    rw [map_smul, ← algebraMap_smul W d (φ a)]
    exact hdN _
  obtain ⟨m, b⟩ := Submodule.basisOfPid (Pi.basisFun R (Fin n)) N₀
  have hmn : m = n := by
    have e : Module.finrank R N₀ = m := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
    apply le_antisymm
    · rw [← e]
      exact (Submodule.finrank_le N₀).trans (Module.finrank_fin_fun R).le
    · haveI : Module.Finite R N₀ := Module.Finite.of_basis b
      let ψ : (Fin n → R) →ₗ[R] N₀ := (d • LinearMap.id).codRestrict N₀ hdN₀
      have hψ : Function.Injective ψ := by
        intro a a' haa
        have := congrArg Subtype.val haa
        exact smul_right_injective (Fin n → R) hd this
      have := LinearMap.finrank_le_finrank_of_injective hψ
      rwa [Module.finrank_fin_fun, e] at this
  let b' : Module.Basis (Fin n) R N₀ := b.reindex (finCongr hmn)
  let A : Matrix (Fin n) (Fin n) R := Matrix.of fun i => (b' i : Fin n → R)
  set B := A.map (algebraMap R W) with hBdef
  have hBφ : ∀ i, B i = φ (b' i) := fun i => rfl
  have hBN : ∀ i, B i ∈ N := fun i => (b' i).2
  choose h₀ hh using fun i => (mem_span_iff_vecMul g (B i)).mp (hBN i)
  set h : Matrix (Fin n) (Fin n) W := Matrix.of h₀ with hhdef
  have hAh : A.map (algebraMap R W) = h * g := by
    ext i j
    rw [← hBdef, ← hh i]
    simp [hhdef, Matrix.mul_apply, Matrix.vecMul, dotProduct]

  have hN₀B : ∀ x : N₀, φ x ∈ Submodule.span W (Set.range B) := by
    intro x
    have hx := congrArg Subtype.val (b'.sum_repr x)
    rw [← hx, Submodule.coe_sum, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Submodule.coe_smul, map_smul, ← hBφ]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hNB : N ≤ Submodule.span W (Set.range B) := by
    rw [hspan, Submodule.span_le]
    rintro v ⟨hvN, hvR⟩
    choose a ha using hvR
    have hva : v = φ a := by funext i; rw [hφ, ha]
    have haN : a ∈ N₀ := by show φ a ∈ N; rw [← hva]; exact hvN
    rw [hva]
    exact hN₀B ⟨a, haN⟩
  choose h₁ hh' using fun i => (mem_span_iff_vecMul B (g i)).mp
    (hNB (Submodule.subset_span ⟨i, rfl⟩))
  set h' : Matrix (Fin n) (Fin n) W := Matrix.of h₁ with hh'def
  have hgB : h' * B = g := by
    ext i j
    rw [← hh' i]
    simp [hh'def, Matrix.mul_apply, Matrix.vecMul, dotProduct]
  have hinv : h' * h = 1 := by
    have e : (h' * h) * g = g := by rw [Matrix.mul_assoc, ← hAh, ← hBdef, hgB]
    have e2 : g.det • (h' * h - 1) = 0 := by
      have : (h' * h - 1) * (g * g.adjugate) = 0 := by
        rw [← Matrix.mul_assoc, Matrix.sub_mul, e, Matrix.one_mul, sub_self, Matrix.zero_mul]
      rwa [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at this
    exact sub_eq_zero.mp ((smul_eq_zero.mp e2).resolve_left hg)
  exact ⟨A, h, Matrix.isUnit_det_of_left_inverse hinv, hAh⟩

end GlobalTheory.MatrixDescent

namespace GlobalTheory

open GlobalTheory.MatrixDescent in

/- English proof (translation)
Use `set iW := algebraMap W K' with hiW`. Establish `hinjW : Function.Injective iW` using `IsFractionRing.injective W K'`. Establish `hRK' : ∀ r : R, algebraMap R K' r = iW (algebraMap R W r)` using `fun r => IsScalarTower.algebraMap_apply R W K' r`. Establish `hRK'' : ∀ r : R, algebraMap R K' r = algebraMap K K' (algebraMap R K r)` using `fun r => IsScalarTower.algebraMap_apply R K K' r`. Establish `hinjR : Function.Injective (algebraMap R W)`.

Introduce `a b hab`. Establish `h1 : algebraMap R K' a = algebraMap R K' b` using `by rw [hRK', hRK', hab]`. Rewrite `h1` using `[hRK'', hRK'']`. Conclude with `IsFractionRing.injective R K ((algebraMap K K').injective h1)`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible R`.

Establish `hmax : maximalIdeal W = Ideal.span {algebraMap R W ϖ}`. Rewrite using `[← hm, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span, Set.image_singleton]`. Establish `hirr : Irreducible (algebraMap R W ϖ)` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples (M := nonZeroDivisors W) (Finset.univ : Finset (Fin n × Fin n)) (fun p => g p.1 p.2)`. Establish `hb0 : (b : W) ≠ 0` using `nonZeroDivisors.coe_ne_zero b`.

Take `⟨k, u, hu⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hb0 hirr`. Use `set c : R := ϖ ^ k with hcdef`. Establish `hc0 : c ≠ 0` using `pow_ne_zero k hϖ.ne_zero`. Establish `hcW : algebraMap R W c = (b : W) * u` using `by rw [hu, hcdef, map_pow]`. Establish `hex : ∀ i j, ∃ w : W, iW w = algebraMap R K' c * g i j`.

Introduce `i j`. Take `⟨w, hw⟩` from `hb (i, j) (Finset.mem_univ _)`. Use `⟨u * w, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hw, hRK', hcW, Algebra.smul_def, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Use `choose g' hg' using hex`. Establish `hcK'0 : algebraMap R K' c ≠ 0`. Rewrite using `[hRK']; exact fun h => hc0 (hinjR (hinjW (by rw [h, map_zero, map_zero])))`. Establish `hdet' : (Matrix.of g').det ≠ 0`. Introduce `h0`.

Establish `: iW (Matrix.of g').det = (algebraMap R K' c) ^ n * g.det`. Rewrite using `[RingHom.map_det]`. Establish `e : iW.mapMatrix (Matrix.of g') = algebraMap R K' c • g`. Use extensionality with `i j`. Simplify using `[hg']`.

Rewrite using `[e, Matrix.det_smul, Fintype.card_fin]`. Rewrite `this` using `[h0, map_zero]`. Conclude with `(mul_ne_zero (pow_ne_zero n hcK'0) hg.ne_zero) this.symm`. Use `set G : Matrix (Fin n) (Fin n) W := Matrix.of g' with hGdef`. Establish `hGmap : ∀ i j, iW (G i j) = algebraMap R K' c * g i j` using `fun i j => hg' i j`.

Use `set N := Submodule.span W (Set.range G) with hNdef`. Take `⟨r, v, hv⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hdet' hirr`. Establish `hdN : ∀ w : Fin n → W, algebraMap R W (ϖ ^ r) • w ∈ N`. Introduce `w`. Establish `e : algebraMap R W (ϖ ^ r) • w = Matrix.vecMul ((v : W) • Matrix.vecMul w G.adjugate) G`.

Rewrite using `[Matrix.smul_vecMul, Matrix.vecMul_vecMul, Matrix.adjugate_mul, Matrix.vecMul_smul, Matrix.vecMul_one, smul_smul, map_pow, ← hv, mul_comm]`. Rewrite using `[e]`. Conclude with `vecMul_mem_span G _`. Establish `hlat : (maximalIdeal W) ^ r • (⊤ : Submodule W (Fin n → W)) ≤ N`. Rewrite using `[Submodule.smul_le]`.

Introduce `x hx w _`. Rewrite `hx` using `[hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Take `⟨t, rfl⟩` from `hx`. Rewrite using `[mul_smul, ← map_pow]`. Conclude with `hdN _`.

Establish `hτ : ∀ σ ∈ D, ∃ τ : W ≃ₐ[R] W, ∀ x : W, iW (τ x) = σ (iW x)` using `fun σ hσ => exists_restrict R K W K' hinjW σ (hD1 σ hσ) (hD2 σ hσ)`. Use `set D' : Set (W ≃ₐ[R] W) := {τ | ∃ σ ∈ D, ∀ x : W, iW (τ x) = σ (iW x)} with hD'def`. Establish `hres' : ∀ x : W, (∀ τ ∈ D', τ x - x ∈ maximalIdeal W) → ∃ r : R, x - algebraMap R W r ∈ maximalIdeal W`. Introduce `x hx`. Apply `hres x` to reduce the goal to its premises.

Introduce `σ hσ y hy`. Take `⟨τ, hτσ⟩` from `hτ σ hσ`. Establish `: τ x = y` using `hinjW (by rw [hτσ, hy])`. Rewrite using `[← this]`. Conclude with `hx τ ⟨σ, hσ, hτσ⟩`.

Establish `hstab' : ∀ τ ∈ D', ∀ w ∈ N, (fun i => τ (w i)) ∈ N`. Introduce and unpack `τ ⟨σ, hσ, hτσ⟩ w hw`. Take `⟨h, hh⟩` from `hstab σ hσ`. Establish `hGτ : G.map τ = h * G`. Use extensionality with `i j`.

Apply `hinjW` to reduce the goal to its premises. Rewrite using `[Matrix.map_apply, hτσ, hGmap, map_mul, Matrix.mul_apply, map_sum]`. Use `congrFun (congrFun hh i) j` as an intermediate fact. Rewrite `this` using `[Matrix.map_apply, Matrix.mul_apply]`. Rewrite using `[this, hRK'', AlgEquiv.commutes, ← hRK'', Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hGmap, Matrix.map_apply]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨a, rfl⟩` from `(mem_span_iff_vecMul G w).mp hw`. Establish `e : (fun i => τ (Matrix.vecMul a G i)) = Matrix.vecMul (Matrix.vecMul (fun i => τ (a i)) h) G`.

Rewrite using `[Matrix.vecMul_vecMul, ← hGτ]`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.vecMul, dotProduct, map_sum]`. Rewrite using `[e]`. Conclude with `vecMul_mem_span G _`.

Establish `hspan` using `stable_lattice_descent_unramified R W hm D' hres' n r N hlat hstab'`. Take `⟨A, h, hhu, hA⟩` from `rational_rows R W hinjR n G hdet' (ϖ ^ r) (pow_ne_zero r hϖ.ne_zero) hdN hspan`. Use `⟨h, (algebraMap R K c)⁻¹ • A.map (algebraMap R K), hhu, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Establish `e1` using `congrFun (congrFun hA i) j`.

Rewrite `e1` using `[Matrix.map_apply, Matrix.mul_apply]`. Establish `e2 : algebraMap R K' (A i j) = algebraMap R K' c * (h.map iW * g) i j`. Rewrite using `[hRK', e1, map_sum, Matrix.mul_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hGmap, Matrix.map_apply]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Matrix.map_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_inv₀, ← hRK'', ← hRK'', e2]`. Clear the denominators using the available nonvanishing facts.
-/
theorem matrix_descent_unramified (R K W K' : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W]
    [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K']
    [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K']
    (hm : (maximalIdeal R).map (algebraMap R W) = maximalIdeal W) (D : Set (K' ≃ₐ[K] K'))
    (hD1 : ∀ σ ∈ D, ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y)
    (hD2 : ∀ σ ∈ D, ∀ x : W, ∃ y : W, σ.symm (algebraMap W K' x) = algebraMap W K' y)
    (hres : ∀ x : W, (∀ σ ∈ D, ∀ y : W, σ (algebraMap W K' x) = algebraMap W K' y →
      y - x ∈ maximalIdeal W) → ∃ r : R, x - algebraMap R W r ∈ maximalIdeal W)
    (n : ℕ) (g : Matrix (Fin n) (Fin n) K') (hg : IsUnit g.det)
    (hstab : ∀ σ ∈ D, ∃ h : Matrix (Fin n) (Fin n) W, g.map σ = h.map (algebraMap W K') * g) :
    ∃ (h : Matrix (Fin n) (Fin n) W) (k : Matrix (Fin n) (Fin n) K),
      IsUnit h.det ∧ k.map (algebraMap K K') = h.map (algebraMap W K') * g := by
  set iW := algebraMap W K' with hiW
  have hinjW : Function.Injective iW := IsFractionRing.injective W K'
  have hRK' : ∀ r : R, algebraMap R K' r = iW (algebraMap R W r) := fun r =>
    IsScalarTower.algebraMap_apply R W K' r
  have hRK'' : ∀ r : R, algebraMap R K' r = algebraMap K K' (algebraMap R K r) := fun r =>
    IsScalarTower.algebraMap_apply R K K' r
  have hinjR : Function.Injective (algebraMap R W) := by
    intro a b hab
    have h1 : algebraMap R K' a = algebraMap R K' b := by rw [hRK', hRK', hab]
    rw [hRK'', hRK''] at h1
    exact IsFractionRing.injective R K ((algebraMap K K').injective h1)

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hmax : maximalIdeal W = Ideal.span {algebraMap R W ϖ} := by
    rw [← hm, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]
  have hirr : Irreducible (algebraMap R W ϖ) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax

  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (M := nonZeroDivisors W)
    (Finset.univ : Finset (Fin n × Fin n)) (fun p => g p.1 p.2)
  have hb0 : (b : W) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hirr
  set c : R := ϖ ^ k with hcdef
  have hc0 : c ≠ 0 := pow_ne_zero k hϖ.ne_zero
  have hcW : algebraMap R W c = (b : W) * u := by rw [hu, hcdef, map_pow]
  have hex : ∀ i j, ∃ w : W, iW w = algebraMap R K' c * g i j := by
    intro i j
    obtain ⟨w, hw⟩ := hb (i, j) (Finset.mem_univ _)
    refine ⟨u * w, ?_⟩
    rw [map_mul, hw, hRK', hcW, Algebra.smul_def, map_mul]
    ring
  choose g' hg' using hex
  have hcK'0 : algebraMap R K' c ≠ 0 := by
    rw [hRK']; exact fun h => hc0 (hinjR (hinjW (by rw [h, map_zero, map_zero])))
  have hdet' : (Matrix.of g').det ≠ 0 := by
    intro h0
    have : iW (Matrix.of g').det = (algebraMap R K' c) ^ n * g.det := by
      rw [RingHom.map_det]
      have e : iW.mapMatrix (Matrix.of g') = algebraMap R K' c • g := by
        ext i j; simp [hg']
      rw [e, Matrix.det_smul, Fintype.card_fin]
    rw [h0, map_zero] at this
    exact (mul_ne_zero (pow_ne_zero n hcK'0) hg.ne_zero) this.symm
  set G : Matrix (Fin n) (Fin n) W := Matrix.of g' with hGdef
  have hGmap : ∀ i j, iW (G i j) = algebraMap R K' c * g i j := fun i j => hg' i j
  set N := Submodule.span W (Set.range G) with hNdef

  obtain ⟨r, v, hv⟩ := IsDiscreteValuationRing.associated_pow_irreducible hdet' hirr
  have hdN : ∀ w : Fin n → W, algebraMap R W (ϖ ^ r) • w ∈ N := by
    intro w
    have e : algebraMap R W (ϖ ^ r) • w = Matrix.vecMul ((v : W) • Matrix.vecMul w G.adjugate) G := by
      rw [Matrix.smul_vecMul, Matrix.vecMul_vecMul, Matrix.adjugate_mul, Matrix.vecMul_smul,
        Matrix.vecMul_one, smul_smul, map_pow, ← hv, mul_comm]
    rw [e]; exact vecMul_mem_span G _
  have hlat : (maximalIdeal W) ^ r • (⊤ : Submodule W (Fin n → W)) ≤ N := by
    rw [Submodule.smul_le]
    intro x hx w _
    rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    obtain ⟨t, rfl⟩ := hx
    rw [mul_smul, ← map_pow]
    exact hdN _

  have hτ : ∀ σ ∈ D, ∃ τ : W ≃ₐ[R] W, ∀ x : W, iW (τ x) = σ (iW x) := fun σ hσ =>
    exists_restrict R K W K' hinjW σ (hD1 σ hσ) (hD2 σ hσ)
  set D' : Set (W ≃ₐ[R] W) := {τ | ∃ σ ∈ D, ∀ x : W, iW (τ x) = σ (iW x)} with hD'def
  have hres' : ∀ x : W, (∀ τ ∈ D', τ x - x ∈ maximalIdeal W) →
      ∃ r : R, x - algebraMap R W r ∈ maximalIdeal W := by
    intro x hx
    apply hres x
    intro σ hσ y hy
    obtain ⟨τ, hτσ⟩ := hτ σ hσ
    have : τ x = y := hinjW (by rw [hτσ, hy])
    rw [← this]; exact hx τ ⟨σ, hσ, hτσ⟩
  have hstab' : ∀ τ ∈ D', ∀ w ∈ N, (fun i => τ (w i)) ∈ N := by
    rintro τ ⟨σ, hσ, hτσ⟩ w hw
    obtain ⟨h, hh⟩ := hstab σ hσ
    have hGτ : G.map τ = h * G := by
      ext i j
      apply hinjW
      rw [Matrix.map_apply, hτσ, hGmap, map_mul, Matrix.mul_apply, map_sum]
      have := congrFun (congrFun hh i) j
      rw [Matrix.map_apply, Matrix.mul_apply] at this
      rw [this, hRK'', AlgEquiv.commutes, ← hRK'', Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, hGmap, Matrix.map_apply]; ring
    obtain ⟨a, rfl⟩ := (mem_span_iff_vecMul G w).mp hw
    have e : (fun i => τ (Matrix.vecMul a G i)) =
        Matrix.vecMul (Matrix.vecMul (fun i => τ (a i)) h) G := by
      rw [Matrix.vecMul_vecMul, ← hGτ]
      funext i
      simp [Matrix.vecMul, dotProduct, map_sum]
    rw [e]; exact vecMul_mem_span G _
  have hspan := stable_lattice_descent_unramified R W hm D' hres' n r N hlat hstab'
  obtain ⟨A, h, hhu, hA⟩ :=
    rational_rows R W hinjR n G hdet' (ϖ ^ r) (pow_ne_zero r hϖ.ne_zero) hdN hspan
  refine ⟨h, (algebraMap R K c)⁻¹ • A.map (algebraMap R K), hhu, ?_⟩
  ext i j
  have e1 := congrFun (congrFun hA i) j
  rw [Matrix.map_apply, Matrix.mul_apply] at e1
  have e2 : algebraMap R K' (A i j) = algebraMap R K' c * (h.map iW * g) i j := by
    rw [hRK', e1, map_sum, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, hGmap, Matrix.map_apply]; ring
  rw [Matrix.map_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_inv₀,
    ← hRK'', ← hRK'', e2]
  field_simp

end GlobalTheory
