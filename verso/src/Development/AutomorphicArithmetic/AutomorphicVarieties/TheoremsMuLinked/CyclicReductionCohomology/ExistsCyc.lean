import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.FixCnt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OmegaConstruction
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsCyclic

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

/- English proof (translation)
Establish `hk : ∀ k : ℕ, W *ᵥ (fun j => al j ^ k) = 0`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa using h1`. Consider the case `succ k ih`.

Establish `e : (fun j => al j ^ (k + 1)) = diagonal al *ᵥ (fun j => al j ^ k)`. Use function extensionality and compare the values at `j`. Rewrite using `[mulVec_diagonal, pow_succ']`. Rewrite using `[e, mulVec_mulVec, ← h, ← mulVec_mulVec, ih, mulVec_zero]`. Establish `hv : W * vandermonde al = 0`.

Use extensionality with `i k`. Use `congrFun (hk k) i` as an intermediate fact. Simplify `this` using `[mul_apply, vandermonde_apply, mulVec, dotProduct]`. Establish `hd : (vandermonde al).det ≠ 0` using `det_vandermonde_ne_zero_iff.mpr ha`. Establish `h2 : W * vandermonde al * adjugate (vandermonde al) = 0` using `by rw [hv, Matrix.zero_mul]`.

Rewrite `h2` using `[Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul, Matrix.mul_one]`. Conclude with `(smul_eq_zero.mp h2).resolve_left hd`.
-/
private theorem cols_zero {O : Type} [CommRing O] [IsDomain O] {n : ℕ} (A W : Matrix (Fin n) (Fin n) O) (al : Fin n → O)
    (ha : Function.Injective al) (h : A * W = W * diagonal al) (h1 : W *ᵥ (fun _ => 1) = 0) : W = 0 := by
  have hk : ∀ k : ℕ, W *ᵥ (fun j => al j ^ k) = 0 := by
    intro k
    induction k with
    | zero => simpa using h1
    | succ k ih =>
      have e : (fun j => al j ^ (k + 1)) = diagonal al *ᵥ (fun j => al j ^ k) := by
        funext j
        rw [mulVec_diagonal, pow_succ']
      rw [e, mulVec_mulVec, ← h, ← mulVec_mulVec, ih, mulVec_zero]
  have hv : W * vandermonde al = 0 := by
    ext i k
    have := congrFun (hk k) i
    simpa [mul_apply, vandermonde_apply, mulVec, dotProduct] using this
  have hd : (vandermonde al).det ≠ 0 := det_vandermonde_ne_zero_iff.mpr ha
  have h2 : W * vandermonde al * adjugate (vandermonde al) = 0 := by rw [hv, Matrix.zero_mul]
  rw [Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at h2
  exact (smul_eq_zero.mp h2).resolve_left hd

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.ExistsCyclic.exists_cyc A al ha hc`.
-/
private theorem exists_cyc {O : Type} [CommRing O] [IsDomain O] {n : ℕ} (A : Matrix (Fin n) (Fin n) O) (al : Fin n → O)
    (ha : Function.Injective al) (hc : A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i))) :
    ∃ v : Fin n → O, ∀ Y : Matrix (Fin n) (Fin n) O, A * Y = Y * A → Y *ᵥ v = 0 → Y = 0 :=
  _root_.UpperTheory.Reformulated.B.ExistsCyclic.exists_cyc A al ha hc

/- English proof (translation)
The claim follows from `Matrix.map_mul`.
-/
private theorem red_mul' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A * B) = red m A * red m B := Matrix.map_mul

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.OmegaConstruction.red_sub m A B`.
-/
private theorem red_sub' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A - B) = red m A - red m B :=
  _root_.UpperTheory.Reformulated.B.OmegaConstruction.red_sub m A B

/- English proof (translation)
Introduce `l _ L G0 O _ _ _ hO _ n y σ al ha hc`. Take `⟨v, hv⟩` from `exists_cyc _ al ha hc`. Set `Φ : Matrix (Fin n) (Fin n) O →ₗ[O] Matrix (Fin n) (Fin n) O` to `(LinearMap.mulRight O (mat y.ρ σ⁻¹)).comp (LinearMap.mulLeft O (mat y.ρ σ)) - LinearMap.id`. Establish `hΦ : ∀ Y, Φ Y = mat y.ρ σ * Y * mat y.ρ σ⁻¹ - Y` using `fun _ => rfl`. Take `⟨C, hC⟩` from `fixCnt l O n Unit (fun _ => Φ)`.

Establish `hinv : mat y.ρ σ⁻¹ * mat y.ρ σ = 1`. Rewrite using `[← map_mul, inv_mul_cancel, map_one]`. Establish `hr : Module.finrank O (⨅ _ : Unit, LinearMap.ker Φ : Submodule O (Matrix (Fin n) (Fin n) O)) ≤ n`. Set `f : (⨅ _ : Unit, LinearMap.ker Φ : Submodule O (Matrix (Fin n) (Fin n) O)) →ₗ[O] (Fin n → O)` to `{ toFun := fun Y => Y.1 *ᵥ v map_add' := fun a b => by simp [add_mulVec] map_smul' := fun c a => by simp [smul_mulVec] }`. Establish `hf : Function.Injective f`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `Y e`. Apply `Subtype.ext` to reduce the goal to its premises. Use `hv Y.1 ?_ e` and prove the remaining obligations. Establish `h1 : Φ Y.1 = 0` using `(Submodule.mem_iInf _).mp Y.2 ()`.

Rewrite `h1` using `[hΦ, sub_eq_zero]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc _ _ (mat y.ρ σ), hinv, Matrix.mul_one]`. Use `_ = _ := by rw [h1]`. Simplify using `using LinearMap.finrank_le_finrank_of_injective hf`.

Use `⟨C, fun m => ?_⟩` and prove the remaining obligations. Establish `hs : {Y : Mm O n m | y.ρ0 m σ * Y * y.ρ0 m σ⁻¹ = Y} = {Y : Mm O n m | ∃ Y', red m Y' = Y ∧ ∀ _ : Unit, red m (Φ Y') = 0}`. Use extensionality with `Y`. Prove the components needed by the constructor for the conclusion. Introduce `hY choose Y' hY' using fun i j => Ideal.Quotient.mk_surjective (Y i j)`.

Establish `e : red m (Matrix.of Y') = Y`. Use extensionality with `i j`. Conclude with `hY' i j`. Use `⟨Matrix.of Y', e, fun _ => ?_⟩` and prove the remaining obligations. Rewrite using `[hΦ, red_sub', red_mul', red_mul', e]`.

Conclude with `sub_eq_zero.mpr hY`. Introduce and unpack `⟨Y', e, h⟩`. Establish `h1` using `h ()`. Rewrite `h1` using `[hΦ, red_sub', red_mul', red_mul', e]`. Conclude with `sub_eq_zero.mp h1`.

Rewrite using `[hs]`. Use `(hC m).trans ?_` and prove the remaining obligations. Take `⟨-, hfin, -⟩` from `hO`. Conclude with `Nat.pow_le_pow_right Nat.card_pos (Nat.add_le_add_right (Nat.mul_le_mul_left m hr) C)`.
-/
theorem UpperTheory.V.Th.h0qO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (σ : G0.G₀) (al : Fin n → O), Function.Injective al → (mat y.ρ σ).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i)) → ∃ C : ℕ, ∀ m, {Y : Mm O n m | y.ρ0 m σ * Y * y.ρ0 m σ⁻¹ = Y}.ncard ≤ Nat.card (ResidueField O) ^ (m * n + C) := by
  intro l _ L G0 O _ _ _ hO _ n y σ al ha hc
  obtain ⟨v, hv⟩ := exists_cyc _ al ha hc
  let Φ : Matrix (Fin n) (Fin n) O →ₗ[O] Matrix (Fin n) (Fin n) O :=
    (LinearMap.mulRight O (mat y.ρ σ⁻¹)).comp (LinearMap.mulLeft O (mat y.ρ σ)) - LinearMap.id
  have hΦ : ∀ Y, Φ Y = mat y.ρ σ * Y * mat y.ρ σ⁻¹ - Y := fun _ => rfl
  obtain ⟨C, hC⟩ := fixCnt l O n Unit (fun _ => Φ)
  have hinv : mat y.ρ σ⁻¹ * mat y.ρ σ = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hr : Module.finrank O (⨅ _ : Unit, LinearMap.ker Φ : Submodule O (Matrix (Fin n) (Fin n) O)) ≤ n := by
    let f : (⨅ _ : Unit, LinearMap.ker Φ : Submodule O (Matrix (Fin n) (Fin n) O)) →ₗ[O] (Fin n → O) :=
      { toFun := fun Y => Y.1 *ᵥ v
        map_add' := fun a b => by simp [add_mulVec]
        map_smul' := fun c a => by simp [smul_mulVec] }
    have hf : Function.Injective f := by
      rw [injective_iff_map_eq_zero]
      intro Y e
      apply Subtype.ext
      refine hv Y.1 ?_ e
      have h1 : Φ Y.1 = 0 := (Submodule.mem_iInf _).mp Y.2 ()
      rw [hΦ, sub_eq_zero] at h1
      calc mat y.ρ σ * Y.1 = mat y.ρ σ * Y.1 * mat y.ρ σ⁻¹ * mat y.ρ σ := by
            rw [Matrix.mul_assoc _ _ (mat y.ρ σ), hinv, Matrix.mul_one]
        _ = _ := by rw [h1]
    simpa using LinearMap.finrank_le_finrank_of_injective hf
  refine ⟨C, fun m => ?_⟩
  have hs : {Y : Mm O n m | y.ρ0 m σ * Y * y.ρ0 m σ⁻¹ = Y} =
      {Y : Mm O n m | ∃ Y', red m Y' = Y ∧ ∀ _ : Unit, red m (Φ Y') = 0} := by
    ext Y
    constructor
    · intro hY
      choose Y' hY' using fun i j => Ideal.Quotient.mk_surjective (Y i j)
      have e : red m (Matrix.of Y') = Y := by
        ext i j
        exact hY' i j
      refine ⟨Matrix.of Y', e, fun _ => ?_⟩
      rw [hΦ, red_sub', red_mul', red_mul', e]
      exact sub_eq_zero.mpr hY
    · rintro ⟨Y', e, h⟩
      have h1 := h ()
      rw [hΦ, red_sub', red_mul', red_mul', e] at h1
      exact sub_eq_zero.mp h1
  rw [hs]
  refine (hC m).trans ?_
  obtain ⟨-, hfin, -⟩ := hO
  exact Nat.pow_le_pow_right Nat.card_pos (Nat.add_le_add_right (Nat.mul_le_mul_left m hr) C)
