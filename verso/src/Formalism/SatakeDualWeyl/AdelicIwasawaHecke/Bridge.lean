import Formalism.SatakeDualWeyl.StatementB

noncomputable section

open Matrix

namespace Formalism.UG.P

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `simp [LinearMap.GeneralLinearGroup.generalLinearEquiv, Matrix.GeneralLinearGroup.toLin, Matrix.toLin'_apply]`.
-/
theorem glEquiv_apply' {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
    (g : GL n K) (x : n → K) : Formalism.UG.glEquiv g x = (g : Matrix n n K) *ᵥ x := by
  first
  | rfl
  | simp [LinearMap.GeneralLinearGroup.generalLinearEquiv, Matrix.GeneralLinearGroup.toLin, Matrix.toLin'_apply]

/- English proof (translation)
Unfold `Formalism.UG.hform`. Use `first`. Consider the case `simp only [dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]`. Consider the case `simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]`.
-/
theorem hform_eq_dot {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (x y : n → A) : Formalism.UG.hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y) := by
  unfold Formalism.UG.hform
  first
  | simp only [dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]
  | simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Rewrite using `[hform_eq_dot, hform_eq_dot]`. Unfold `Formalism.UG.cT`. Establish `h1 : (⇑σ ∘ (M *ᵥ x)) = (M.map σ) *ᵥ (⇑σ ∘ x)`. Use function extensionality and compare the values at `i`. Use `first`.

Consider the case `exact RingHom.map_mulVec σ M x i`. Consider the case `simp [mulVec, dotProduct, map_sum, map_mul]`. Rewrite using `[h1, mulVec_mulVec, ← vecMul_transpose (M.map ⇑σ) (⇑σ ∘ x), ← dotProduct_mulVec, mulVec_mulVec, Matrix.mul_assoc]`.
-/
theorem hform_mulVec {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J M : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M) x y := by
  rw [hform_eq_dot, hform_eq_dot]
  unfold Formalism.UG.cT
  have h1 : (⇑σ ∘ (M *ᵥ x)) = (M.map σ) *ᵥ (⇑σ ∘ x) := by
    funext i
    first
    | exact RingHom.map_mulVec σ M x i
    | simp [mulVec, dotProduct, map_sum, map_mul]
  rw [h1, mulVec_mulVec, ← vecMul_transpose (M.map ⇑σ) (⇑σ ∘ x), ← dotProduct_mulVec, mulVec_mulVec,
    Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[hform_eq_dot]`. Establish `hs : (⇑σ ∘ Pi.single i (1 : A)) = Pi.single i 1`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hk]`. Rewrite using `[hs]`. Simplify using `[mulVec_single]`.
-/
theorem hform_single {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (σ : A →+* A) (J : Matrix n n A) (i j : n) :
    Formalism.UG.hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  rw [hform_eq_dot]
  have hs : (⇑σ ∘ Pi.single i (1 : A)) = Pi.single i 1 := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [Pi.single_apply, hk]
  rw [hs]
  simp [mulVec_single]

/- English proof (translation)
Establish `hx : ∀ v : n → K, v = ∑ i, v i • (Pi.single i 1 : n → K)`. Introduce `v`. Use function extensionality and compare the values at `k`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `conv_lhs => rw [hx x, hx y]`.

Simplify using `only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum]`. Unfold `Formalism.UG.hform Formalism.UG.gram`. Use `conv_lhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))` and prove the remaining obligations. Simplify using `only [RingHom.id_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_gram {K : Type} [Field K] [StarRing K] {n : Type} [Fintype n] [DecidableEq n]
    (h : (n → K) →ₗ⋆[K] (n → K) →ₗ[K] K) (x y : n → K) :
    h x y = Formalism.UG.hform (starRingEnd K) (Formalism.UG.gram h) x y := by
  have hx : ∀ v : n → K, v = ∑ i, v i • (Pi.single i 1 : n → K) := by
    intro v
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx x, hx y]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    Finset.mul_sum]
  unfold Formalism.UG.hform Formalism.UG.gram
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [RingHom.id_apply]
  ring

/- English proof (translation)
Introduce `K _ _ n _ _ h g`. Unfold `Formalism.UG.UJ HermitianLatticesTheory.isom`. Prove the components needed by the constructor for the conclusion. Introduce `hg x y`. Establish `hg' : Formalism.UG.cT (starRingEnd K) (g : Matrix n n K) * Formalism.UG.gram h * (g : Matrix n n K) = Formalism.UG.gram h` using `hg`.

Use `show h (Formalism.UG.glEquiv g x) (Formalism.UG.glEquiv g y) = h x y`. Rewrite using `[glEquiv_apply', glEquiv_apply', hform_gram h ((g : Matrix n n K) *ᵥ x) ((g : Matrix n n K) *ᵥ y), hform_gram h x y, hform_mulVec, hg']`. Introduce `hg`. Establish `hg' : ∀ x y : n → K, h (Formalism.UG.glEquiv g x) (Formalism.UG.glEquiv g y) = h x y` using `hg`. Use `show Formalism.UG.cT (starRingEnd K) (g : Matrix n n K) * Formalism.UG.gram h * (g : Matrix n n K) = Formalism.UG.gram h`.

Use extensionality with `i j`. Use `hg' (Pi.single i 1) (Pi.single j 1)` as an intermediate fact. Rewrite `this` using `[glEquiv_apply', glEquiv_apply', hform_gram h ((g : Matrix n n K) *ᵥ Pi.single i 1) ((g : Matrix n n K) *ᵥ Pi.single j 1), hform_gram h (Pi.single i 1) (Pi.single j 1), hform_mulVec, hform_single, hform_single]`. Conclude with `this`.
-/
theorem hermitian_lattice_correspondence_holds : Formalism.UG.HermBridge := by
  intro K _ _ n _ _ h g
  unfold Formalism.UG.UJ HermitianLatticesTheory.isom
  constructor
  · intro hg x y
    have hg' : Formalism.UG.cT (starRingEnd K) (g : Matrix n n K) * Formalism.UG.gram h * (g : Matrix n n K)
        = Formalism.UG.gram h := hg
    show h (Formalism.UG.glEquiv g x) (Formalism.UG.glEquiv g y) = h x y
    rw [glEquiv_apply', glEquiv_apply', hform_gram h ((g : Matrix n n K) *ᵥ x) ((g : Matrix n n K) *ᵥ y),
      hform_gram h x y, hform_mulVec, hg']
  · intro hg
    have hg' : ∀ x y : n → K, h (Formalism.UG.glEquiv g x) (Formalism.UG.glEquiv g y) = h x y := hg
    show Formalism.UG.cT (starRingEnd K) (g : Matrix n n K) * Formalism.UG.gram h * (g : Matrix n n K)
        = Formalism.UG.gram h
    ext i j
    have := hg' (Pi.single i 1) (Pi.single j 1)
    rw [glEquiv_apply', glEquiv_apply',
      hform_gram h ((g : Matrix n n K) *ᵥ Pi.single i 1) ((g : Matrix n n K) *ᵥ Pi.single j 1),
      hform_gram h (Pi.single i 1) (Pi.single j 1), hform_mulVec, hform_single, hform_single] at this
    exact this

/- English proof (translation)
Introduce `K _ _ n _ _ h u _`. Use `⟨Matrix.GeneralLinearGroup.toLin.symm ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (n → K)).symm u), ?_⟩` and prove the remaining obligations. Unfold `Formalism.UG.glEquiv`. Simplify using the standard rewrite rules.
-/
theorem hermitian_correspondence_surjective_holds : Formalism.UG.HermBridgeSurj := by
  intro K _ _ n _ _ h u _
  refine ⟨Matrix.GeneralLinearGroup.toLin.symm
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (n → K)).symm u), ?_⟩
  unfold Formalism.UG.glEquiv
  simp

/- English proof (translation)
Introduce `K _ R _ _ n _ _ Λ g`. Unfold `Formalism.UG.stabGL HermitianLatticesTheory.gmap`. Use `show (∀ x : n → K, x ∈ Λ ↔ (g : Matrix n n K) *ᵥ x ∈ Λ) ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce `hg`.

Use extensionality with `y`. Rewrite using `[Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩ show Formalism.UG.glEquiv g x ∈ Λ`. Rewrite using `[glEquiv_apply']`.

Conclude with `(hg x).mp hx`. Introduce `hy`. Use `⟨(Formalism.UG.glEquiv g).symm y, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hg, ← glEquiv_apply']`. Simplify using `using hy`.

Use `show Formalism.UG.glEquiv g ((Formalism.UG.glEquiv g).symm y) = y`. Simplify using the standard rewrite rules. Introduce `hg x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Rewrite using `[← hg, Submodule.mem_map]`. Conclude with `⟨x, hx, glEquiv_apply' g x⟩`. Introduce `hx`. Rewrite `hx` using `[← hg, Submodule.mem_map]`. Take `⟨z, hz, hzx⟩` from `hx`.

Establish `hzx' : Formalism.UG.glEquiv g z = (g : Matrix n n K) *ᵥ x` using `hzx`. Establish `hzx'' : Formalism.UG.glEquiv g z = Formalism.UG.glEquiv g x`. Rewrite using `[hzx', glEquiv_apply']`. Rewrite using `[← (Formalism.UG.glEquiv g).injective hzx'']`. Conclude with `hz`.
-/
theorem stabilizer_group_map_holds : Formalism.UG.StabGmap := by
  intro K _ R _ _ n _ _ Λ g
  unfold Formalism.UG.stabGL HermitianLatticesTheory.gmap
  show (∀ x : n → K, x ∈ Λ ↔ (g : Matrix n n K) *ᵥ x ∈ Λ) ↔ _
  constructor
  · intro hg
    ext y
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      show Formalism.UG.glEquiv g x ∈ Λ
      rw [glEquiv_apply']
      exact (hg x).mp hx
    · intro hy
      refine ⟨(Formalism.UG.glEquiv g).symm y, ?_, ?_⟩
      · rw [hg, ← glEquiv_apply']
        simpa using hy
      · show Formalism.UG.glEquiv g ((Formalism.UG.glEquiv g).symm y) = y
        simp
  · intro hg x
    constructor
    · intro hx
      rw [← hg, Submodule.mem_map]
      exact ⟨x, hx, glEquiv_apply' g x⟩
    · intro hx
      rw [← hg, Submodule.mem_map] at hx
      obtain ⟨z, hz, hzx⟩ := hx
      have hzx' : Formalism.UG.glEquiv g z = (g : Matrix n n K) *ᵥ x := hzx
      have hzx'' : Formalism.UG.glEquiv g z = Formalism.UG.glEquiv g x := by
        rw [hzx', glEquiv_apply']
      rw [← (Formalism.UG.glEquiv g).injective hzx'']
      exact hz

end Formalism.UG.P
