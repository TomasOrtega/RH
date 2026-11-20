import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Integr
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelWeilUnitaryConvergentOfSiegelWeilConvergen

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GReal

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.Gen
open scoped TensorProduct Matrix NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def hinv {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) : WR.E n := fun i j => (h i j).re + (h i j).im

def ybAll {n : ℕ} (σ : E →ₐ[F] E) {ι : Type} (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (g : ι → GL (Fin n) ℂ)
    (S : HermR (Ainf F) σ n) : ι → WR.E n :=
  fun i => hinv (((g i)⁻¹).1 * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (((g i)⁻¹).1)ᴴ)

def ygAll {n : ℕ} (σ : E →ₐ[F] E) {ι : Type} (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (g : ι → GL (Fin n) ℂ)
    (S : HermR (Ainf F) σ n) : ι → WR.E n :=
  fun i => hinv (((g i).1)ᴴ * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (g i).1)

def crdAll {M n : ℕ} {ι : Type} (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (fr : ι → GL (Fin M) ℂ) (g : ι → GL (Fin n) ℂ)
    (X : Fin n → Fin M → Ainf F ⊗[F] E) : ι → Fin M → Fin n → ℂ :=
  fun i => crd (θ i) (fr i) (g i) X

/- English proof (translation)
Use extensionality with `i j`. Establish `hji : h j i = star (h i j)`. Use `congrFun (congrFun hh j) i` as an intermediate fact. Simplify `this.symm` using `[Matrix.conjTranspose_apply]`. Apply `Complex.ext` to reduce the goal to its premises.

Simplify using `[herm, hinv, hji]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[herm, hinv, hji]`.
-/
theorem herm_hinv {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) : herm (hinv h) = h := by
  ext i j
  have hji : h j i = star (h i j) := by
    have := congrFun (congrFun hh j) i
    simpa [Matrix.conjTranspose_apply] using this.symm
  apply Complex.ext
  · simp [herm, hinv, hji]
    ring
  · simp [herm, hinv, hji]

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Simplify using `[herm, hinv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hinv_herm {n : ℕ} (y : WR.E n) : hinv (herm y) = y := by
  funext i j
  simp [herm, hinv]
  ring

/- English proof (translation)
Take `⟨k, e, -⟩` from `GlobalTheory.SiegelWeilConvCompare.exists_coord_tens F E`. Conclude with `e.secondCountableTopology`.
-/
theorem secondCountable_tens [IsTotallyReal F] : SecondCountableTopology (Ainf F ⊗[F] E) := by
  obtain ⟨k, e, -⟩ := GlobalTheory.SiegelWeilConvCompare.exists_coord_tens F E
  exact e.secondCountableTopology

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl⟩`.
-/
theorem borel_tens : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl⟩`.
-/
theorem borel_herm (σ : E →ₐ[F] E) (n : ℕ) : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx i`. Conclude with `((hx.map (θ i)).ne_zero)`. Introduce `hx`. Take `⟨y, hy⟩` from `hP.bij.2 (fun i => (θ i x)⁻¹)`.

Use `IsUnit.of_mul_eq_one y (hP.bij.1 ?_)` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Use `congrFun hy i` as an intermediate fact. Simplify using `only at this ⊢`. Rewrite using `[map_mul, map_one, this, mul_inv_cancel₀ (hx i)]`.
-/
theorem isUnit_iff_th (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) (x : Ainf F ⊗[F] E) :
    IsUnit x ↔ ∀ i, θ i x ≠ 0 := by
  constructor
  · intro hx i
    exact ((hx.map (θ i)).ne_zero)
  · intro hx
    obtain ⟨y, hy⟩ := hP.bij.2 (fun i => (θ i x)⁻¹)
    refine IsUnit.of_mul_eq_one y (hP.bij.1 ?_)
    funext i
    have := congrFun hy i
    simp only at this ⊢
    rw [map_mul, map_one, this, mul_inv_cancel₀ (hx i)]

/- English proof (translation)
Use `haveI : IsTotallyReal F := hCM.1`. Take `⟨k, e, he⟩` from `GlobalTheory.SiegelWeilConvCompare.exists_coord_tens F E`. Set `Θ : (Ainf F ⊗[F] E) →+ (ι → ℂ)` to `{ toFun := fun z i => θ i z map_zero' := by funext i; simp map_add' := by intro x y; funext i; simp }`. Establish `hΘc : Continuous Θ` using `continuous_pi fun i => hP.cont i`. Establish `hes : ∀ a b, e.symm (a + b) = e.symm a + e.symm b`.

Introduce `a b`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[he, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]`. Set `eA : (Fin k → ℝ) →+ (Ainf F ⊗[F] E)` to `{ toFun := e.symm map_zero' := by`. Establish `h0` using `hes 0 0`.

Rewrite `h0` using `[add_zero]`. Conclude with `(add_eq_left.1 h0.symm)`. Use the proof step `map_add' := hes }`. Set `f : (Fin k → ℝ) →+ (ι → ℂ)` to `Θ.comp eA`. Establish `hfc : Continuous f` using `hΘc.comp e.symm.continuous`.

Set `L` to `f.toRealLinearMap hfc`. Establish `hLb : Function.Bijective L`. Establish `h1 : Function.Bijective (e.symm : (Fin k → ℝ) → (Ainf F ⊗[F] E))` using `e.symm.bijective`. Conclude with `hP.bij.comp h1`. Set `Le` to `LinearEquiv.ofBijective (L : (Fin k → ℝ) →ₗ[ℝ] (ι → ℂ)) hLb`.

Set `Lc` to `Le.toContinuousLinearEquiv`. Set `A` to `AddEquiv.ofBijective Θ hP.bij`. Establish `hinvA : (A.symm : (ι → ℂ) → (Ainf F ⊗[F] E)) = e.symm ∘ Lc.symm`. Use function extensionality and compare the values at `w`. Apply `A.injective` to reduce the goal to its premises.

Rewrite using `[AddEquiv.apply_symm_apply]`. Establish `: Lc (Lc.symm w) = w` using `Lc.apply_symm_apply w`. Conclude with `this.symm`. Use `⟨{ toAddEquiv := A, continuous_toFun := hΘc, continuous_invFun := ?_ }, fun z i => rfl⟩` and prove the remaining obligations. Use `show Continuous (A.symm : (ι → ℂ) → (Ainf F ⊗[F] E))`.

Rewrite using `[hinvA]`. Conclude with `e.symm.continuous.comp Lc.symm.continuous`.
-/
theorem exists_thHomeo (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) :
    ∃ e : (Ainf F ⊗[F] E) ≃ₜ+ (ι → ℂ), ∀ z i, e z i = θ i z := by
  haveI : IsTotallyReal F := hCM.1
  obtain ⟨k, e, he⟩ := GlobalTheory.SiegelWeilConvCompare.exists_coord_tens F E
  let Θ : (Ainf F ⊗[F] E) →+ (ι → ℂ) :=
    { toFun := fun z i => θ i z
      map_zero' := by funext i; simp
      map_add' := by intro x y; funext i; simp }
  have hΘc : Continuous Θ := continuous_pi fun i => hP.cont i
  have hes : ∀ a b, e.symm (a + b) = e.symm a + e.symm b := by
    intro a b
    apply e.injective
    rw [he, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  let eA : (Fin k → ℝ) →+ (Ainf F ⊗[F] E) :=
    { toFun := e.symm
      map_zero' := by
        have h0 := hes 0 0
        rw [add_zero] at h0
        exact (add_eq_left.1 h0.symm)
      map_add' := hes }
  let f : (Fin k → ℝ) →+ (ι → ℂ) := Θ.comp eA
  have hfc : Continuous f := hΘc.comp e.symm.continuous
  let L := f.toRealLinearMap hfc
  have hLb : Function.Bijective L := by
    have h1 : Function.Bijective (e.symm : (Fin k → ℝ) → (Ainf F ⊗[F] E)) := e.symm.bijective
    exact hP.bij.comp h1
  let Le := LinearEquiv.ofBijective (L : (Fin k → ℝ) →ₗ[ℝ] (ι → ℂ)) hLb
  let Lc := Le.toContinuousLinearEquiv
  let A := AddEquiv.ofBijective Θ hP.bij
  have hinvA : (A.symm : (ι → ℂ) → (Ainf F ⊗[F] E)) = e.symm ∘ Lc.symm := by
    funext w
    apply A.injective
    rw [AddEquiv.apply_symm_apply]
    have : Lc (Lc.symm w) = w := Lc.apply_symm_apply w
    exact this.symm
  refine ⟨{ toAddEquiv := A, continuous_toFun := hΘc, continuous_invFun := ?_ }, fun z i => rfl⟩
  show Continuous (A.symm : (ι → ℂ) → (Ainf F ⊗[F] E))
  rw [hinvA]
  exact e.symm.continuous.comp Lc.symm.continuous

/- English proof (translation)
Simplify using `[Matrix.mul_assoc]`.
-/
theorem gl_sandwich {m k : ℕ} (A : GL (Fin m) ℂ) (B : GL (Fin k) ℂ) (X : Matrix (Fin m) (Fin k) ℂ) :
    A.1 * ((A⁻¹).1 * X * B.1) * (B⁻¹).1 = X := by
  simp [Matrix.mul_assoc]

/- English proof (translation)
Simplify using `[Matrix.mul_assoc]`.
-/
theorem gl_sandwich' {m k : ℕ} (A : GL (Fin m) ℂ) (B : GL (Fin k) ℂ) (X : Matrix (Fin m) (Fin k) ℂ) :
    (A⁻¹).1 * (A.1 * X * (B⁻¹).1) * B.1 = X := by
  simp [Matrix.mul_assoc]

/- English proof (translation)
Take `⟨eT, heT⟩` from `exists_thHomeo σ hCM ψ θ l hP`. Establish `hθinv : ∀ w i, θ i (eT.symm w) = w i` using `fun w i => by rw [← heT, ContinuousAddEquiv.apply_symm_apply]`. Set `cinv : (ι → Fin M → Fin n → ℂ) → (Fin n → Fin M → Ainf F ⊗[F] E)` to `fun x j a => eT.symm (fun i => ((fr i).1 * Matrix.of (x i) * ((g i)⁻¹).1) a j)`. Establish `hli : ∀ X, cinv (crdAll θ fr g X) = X`. Introduce `X`.

Use function extensionality and compare the values at `j a`. Simplify using `only [cinv, crdAll, crd]`. Rewrite using `[← ContinuousAddEquiv.symm_apply_apply eT (X j a)]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Rewrite using `[show ∀ Y : Matrix (Fin M) (Fin n) ℂ, Matrix.of Y = Y from fun _ => rfl, gl_sandwich, heT]`. Both sides reduce to the same expression. Establish `hri : ∀ x, crdAll θ fr g (cinv x) = x`. Introduce `x`. Use function extensionality and compare the values at `i`.

Simplify using `only [cinv, crdAll, crd]`. Establish `: (Matrix.of fun a j => θ i (eT.symm (fun i' => ((fr i').1 * Matrix.of (x i') * ((g i')⁻¹).1) a j))) = (fr i).1 * Matrix.of (x i) * ((g i)⁻¹).1`. Use extensionality with `a j`. Simplify using `[hθinv]`. Rewrite using `[this, gl_sandwich']`.

Both sides reduce to the same expression. Establish `hadd : ∀ X Y, crdAll θ fr g (X + Y) = crdAll θ fr g X + crdAll θ fr g Y`. Introduce `X Y`. Use function extensionality and compare the values at `i`. Simplify using `only [crdAll, crd, Pi.add_apply]`.

Establish `: (Matrix.of fun a j => θ i (X j a + Y j a)) = Matrix.of (fun a j => θ i (X j a)) + Matrix.of (fun a j => θ i (Y j a))`. Use extensionality with `a j`. Simplify using the standard rewrite rules. Rewrite using `[this, Matrix.mul_add, Matrix.add_mul]`. Both sides reduce to the same expression.

Establish `hc1 : Continuous (crdAll θ fr g)`. Use `continuous_pi fun i => ?_` and prove the remaining obligations. Simplify using `only [crdAll, crd]`. Use `(continuous_const.matrix_mul ?_).matrix_mul continuous_const` and prove the remaining obligations. Conclude with `continuous_pi fun a => continuous_pi fun j => (hP.cont i).comp ((continuous_apply a).comp (continuous_apply j))`.

Establish `hc2 : Continuous cinv`. Use `continuous_pi fun j => continuous_pi fun a => eT.symm.continuous.comp (continuous_pi fun i => ?_)` and prove the remaining obligations. Establish `hx : Continuous fun x : ι → Fin M → Fin n → ℂ => Matrix.of (x i)` using `continuous_apply i`. Conclude with `(continuous_apply j).comp ((continuous_apply a).comp (((continuous_const.matrix_mul hx).matrix_mul continuous_const)))`. Set `A : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (ι → Fin M → Fin n → ℂ)` to `{ toFun := crdAll θ fr g invFun := cinv left_inv := hli right_inv := hri map_add' := hadd }`.

Conclude with `⟨{ toAddEquiv := A, continuous_toFun := hc1, continuous_invFun := hc2 }, rfl⟩`.
-/
theorem exists_crdHomeo (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {M n : ℕ} (fr : ι → GL (Fin M) ℂ)
    (g : ι → GL (Fin n) ℂ) :
    ∃ e : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ+ (ι → Fin M → Fin n → ℂ), ⇑e = crdAll θ fr g := by
  obtain ⟨eT, heT⟩ := exists_thHomeo σ hCM ψ θ l hP
  have hθinv : ∀ w i, θ i (eT.symm w) = w i := fun w i => by rw [← heT, ContinuousAddEquiv.apply_symm_apply]
  let cinv : (ι → Fin M → Fin n → ℂ) → (Fin n → Fin M → Ainf F ⊗[F] E) :=
    fun x j a => eT.symm (fun i => ((fr i).1 * Matrix.of (x i) * ((g i)⁻¹).1) a j)
  have hli : ∀ X, cinv (crdAll θ fr g X) = X := by
    intro X; funext j a
    simp only [cinv, crdAll, crd]
    rw [← ContinuousAddEquiv.symm_apply_apply eT (X j a)]
    congr 1
    funext i
    rw [show ∀ Y : Matrix (Fin M) (Fin n) ℂ, Matrix.of Y = Y from fun _ => rfl, gl_sandwich, heT]
    rfl
  have hri : ∀ x, crdAll θ fr g (cinv x) = x := by
    intro x; funext i
    simp only [cinv, crdAll, crd]
    have : (Matrix.of fun a j => θ i (eT.symm (fun i' => ((fr i').1 * Matrix.of (x i') *
        ((g i')⁻¹).1) a j))) = (fr i).1 * Matrix.of (x i) * ((g i)⁻¹).1 := by
      ext a j; simp [hθinv]
    rw [this, gl_sandwich']
    rfl
  have hadd : ∀ X Y, crdAll θ fr g (X + Y) = crdAll θ fr g X + crdAll θ fr g Y := by
    intro X Y; funext i
    simp only [crdAll, crd, Pi.add_apply]
    have : (Matrix.of fun a j => θ i (X j a + Y j a)) =
        Matrix.of (fun a j => θ i (X j a)) + Matrix.of (fun a j => θ i (Y j a)) := by
      ext a j; simp
    rw [this, Matrix.mul_add, Matrix.add_mul]
    rfl
  have hc1 : Continuous (crdAll θ fr g) := by
    refine continuous_pi fun i => ?_
    simp only [crdAll, crd]
    refine (continuous_const.matrix_mul ?_).matrix_mul continuous_const
    exact continuous_pi fun a => continuous_pi fun j =>
      (hP.cont i).comp ((continuous_apply a).comp (continuous_apply j))
  have hc2 : Continuous cinv := by
    refine continuous_pi fun j => continuous_pi fun a => eT.symm.continuous.comp (continuous_pi fun i => ?_)
    have hx : Continuous fun x : ι → Fin M → Fin n → ℂ => Matrix.of (x i) := continuous_apply i
    exact (continuous_apply j).comp ((continuous_apply a).comp
      (((continuous_const.matrix_mul hx).matrix_mul continuous_const)))
  let A : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (ι → Fin M → Fin n → ℂ) :=
    { toFun := crdAll θ fr g
      invFun := cinv
      left_inv := hli
      right_inv := hri
      map_add' := hadd }
  exact ⟨{ toAddEquiv := A, continuous_toFun := hc1, continuous_invFun := hc2 }, rfl⟩

/- English proof (translation)
Use extensionality with `a c`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.map_apply]`. Rewrite using `[← hc]`. Conclude with `congrArg θ (b.2 a c)`.
-/
theorem isHerm_map (σ : E →ₐ[F] E) (θ : Ainf F ⊗[F] E →+* ℂ)
    (hc : ∀ z, θ (sigR (Ainf F) σ z) = star (θ z)) {n : ℕ} (b : HermR (Ainf F) σ n) :
    ((b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map θ).IsHermitian := by
  ext a c
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
  rw [← hc]
  exact congrArg θ (b.2 a c)

/- English proof (translation)
Establish `h1 : ((A⁻¹).1)ᴴ * (A.1)ᴴ = 1`. Rewrite using `[← Matrix.conjTranspose_mul]`. Simplify using the standard rewrite rules. Simplify using `only [← Matrix.mul_assoc]`. Rewrite using `[Matrix.mul_assoc _ _ (A.1)ᴴ, h1, Matrix.mul_one]`.

Simplify using the standard rewrite rules.
-/
theorem gl_sandwich2 {n : ℕ} (A : GL (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    A.1 * ((A⁻¹).1 * X * ((A⁻¹).1)ᴴ) * (A.1)ᴴ = X := by
  have h1 : ((A⁻¹).1)ᴴ * (A.1)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul]; simp
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc _ _ (A.1)ᴴ, h1, Matrix.mul_one]
  simp

/- English proof (translation)
Establish `h1 : (A.1)ᴴ * ((A⁻¹).1)ᴴ = 1`. Rewrite using `[← Matrix.conjTranspose_mul]`. Simplify using the standard rewrite rules. Simplify using `only [← Matrix.mul_assoc]`. Rewrite using `[Matrix.mul_assoc _ _ ((A⁻¹).1)ᴴ, h1, Matrix.mul_one]`.

Simplify using the standard rewrite rules.
-/
theorem gl_sandwich3 {n : ℕ} (A : GL (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    (A⁻¹).1 * (A.1 * X * (A.1)ᴴ) * ((A⁻¹).1)ᴴ = X := by
  have h1 : (A.1)ᴴ * ((A⁻¹).1)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul]; simp
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc _ _ ((A⁻¹).1)ᴴ, h1, Matrix.mul_one]
  simp

/- English proof (translation)
Take `⟨eT, heT⟩` from `exists_thHomeo σ hCM ψ θ l hP`. Establish `hθinv : ∀ w i, θ i (eT.symm w) = w i` using `fun w i => by rw [← heT, ContinuousAddEquiv.apply_symm_apply]`. Set `fwd : HermR (Ainf F) σ n → ι → WR.E n` to `fun S i => hinv ((A i).1 * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * ((A i).1)ᴴ)`. Set `w : (ι → WR.E n) → Fin n → Fin n → ι → ℂ` to `fun y a b i => (((A i)⁻¹).1 * herm (y i) * (((A i)⁻¹).1)ᴴ) a b`. Establish `hwH : ∀ y a b i, star (w y b a i) = w y a b i`.

Introduce `y a b i`. Establish `h` using `Matrix.isHermitian_mul_mul_conjTranspose (((A i)⁻¹).1) (WR.I.herm_isHermitian (y i))`. Use `congrFun (congrFun h a) b` as an intermediate fact. Simplify using `only [Matrix.conjTranspose_apply] at this`. Conclude with `this`.

Establish `hmem : ∀ y, (Matrix.of fun a b => eT.symm (w y a b)) ∈ HermR (Ainf F) σ n`. Introduce `y a b`. Apply `hP.bij.1` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.of_apply]`.

Rewrite using `[hP.conj, hθinv, hθinv, hwH]`. Set `bwd : (ι → WR.E n) → HermR (Ainf F) σ n` to `fun y => ⟨Matrix.of fun a b => eT.symm (w y a b), hmem y⟩`. Establish `hmapb : ∀ y i, ((bwd y : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))).map (θ i) = ((A i)⁻¹).1 * herm (y i) * (((A i)⁻¹).1)ᴴ`. Introduce `y i`. Use extensionality with `a b`.

Simplify using `[bwd, hθinv, w]`. Establish `hli : ∀ S, bwd (fwd S) = S`. Introduce `S`. Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `a b`.

Use `show eT.symm (w (fwd S) a b) = (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) a b`. Rewrite using `[← ContinuousAddEquiv.symm_apply_apply eT ((S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) a b)]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [w, fwd]`.

Rewrite using `[herm_hinv _ (Matrix.isHermitian_mul_mul_conjTranspose _ (isHerm_map σ (θ i) (hP.conj i) S)), gl_sandwich3, heT]`. Both sides reduce to the same expression. Establish `hri : ∀ y, fwd (bwd y) = y`. Introduce `y`. Use function extensionality and compare the values at `i`.

Simplify using `only [fwd]`. Rewrite using `[hmapb, gl_sandwich2, hinv_herm]`. Establish `hadd : ∀ S T, fwd (S + T) = fwd S + fwd T`. Introduce `S T`. Use function extensionality and compare the values at `i a b`.

Establish `hm : ((S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) + (T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))).map (θ i) = (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) + (T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i)` using `by ext; simp`. Simplify using `only [fwd, hinv, AddSubgroup.coe_add, hm, Matrix.mul_add, Matrix.add_mul, Pi.add_apply, Matrix.add_apply, Complex.add_re, Complex.add_im]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc1 : Continuous fwd`. Use `continuous_pi fun i => continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations.

Simplify using `only [fwd, hinv]`. Establish `hm : Continuous fun S : HermR (Ainf F) σ n => (A i).1 * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * ((A i).1)ᴴ` using `(continuous_const.matrix_mul ((continuous_subtype_val).matrix_map (hP.cont i))).matrix_mul continuous_const`. Establish `he : Continuous fun S : HermR (Ainf F) σ n => ((A i).1 * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * ((A i).1)ᴴ) a b` using `(continuous_apply b).comp ((continuous_apply a).comp hm)`. Conclude with `(Complex.continuous_re.comp he).add (Complex.continuous_im.comp he)`. Establish `hc2 : Continuous bwd`.

Use `Continuous.subtype_mk ?_ _` and prove the remaining obligations. Use `continuous_pi fun a => continuous_pi fun b => eT.symm.continuous.comp (continuous_pi fun i => ?_)` and prove the remaining obligations. Establish `hh : Continuous fun y : ι → WR.E n => herm (y i)` using `WR.I.continuous_herm.comp (continuous_apply i)`. Conclude with `(continuous_apply b).comp ((continuous_apply a).comp ((continuous_const.matrix_mul hh).matrix_mul continuous_const))`. Set `Ae : HermR (Ainf F) σ n ≃+ (ι → WR.E n)` to `{ toFun := fwd invFun := bwd left_inv := hli right_inv := hri map_add' := hadd }`.

Conclude with `⟨{ toAddEquiv := Ae, continuous_toFun := hc1, continuous_invFun := hc2 }, fun S i => rfl⟩`.
-/
theorem exists_hermHomeo (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ} (A : ι → GL (Fin n) ℂ) :
    ∃ e : HermR (Ainf F) σ n ≃ₜ+ (ι → WR.E n), ∀ S i,
      e S i = hinv ((A i).1 * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * ((A i).1)ᴴ) := by
  obtain ⟨eT, heT⟩ := exists_thHomeo σ hCM ψ θ l hP
  have hθinv : ∀ w i, θ i (eT.symm w) = w i := fun w i => by rw [← heT, ContinuousAddEquiv.apply_symm_apply]
  let fwd : HermR (Ainf F) σ n → ι → WR.E n := fun S i =>
    hinv ((A i).1 * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * ((A i).1)ᴴ)
  let w : (ι → WR.E n) → Fin n → Fin n → ι → ℂ := fun y a b i => (((A i)⁻¹).1 * herm (y i) * (((A i)⁻¹).1)ᴴ) a b
  have hwH : ∀ y a b i, star (w y b a i) = w y a b i := by
    intro y a b i
    have h := Matrix.isHermitian_mul_mul_conjTranspose (((A i)⁻¹).1) (WR.I.herm_isHermitian (y i))
    have := congrFun (congrFun h a) b
    simp only [Matrix.conjTranspose_apply] at this
    exact this
  have hmem : ∀ y, (Matrix.of fun a b => eT.symm (w y a b)) ∈ HermR (Ainf F) σ n := by
    intro y a b
    apply hP.bij.1
    funext i
    simp only [Matrix.of_apply]
    rw [hP.conj, hθinv, hθinv, hwH]
  let bwd : (ι → WR.E n) → HermR (Ainf F) σ n := fun y => ⟨Matrix.of fun a b => eT.symm (w y a b), hmem y⟩
  have hmapb : ∀ y i, ((bwd y : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))).map (θ i) =
      ((A i)⁻¹).1 * herm (y i) * (((A i)⁻¹).1)ᴴ := by
    intro y i; ext a b
    simp [bwd, hθinv, w]
  have hli : ∀ S, bwd (fwd S) = S := by
    intro S
    apply Subtype.ext
    ext a b
    show eT.symm (w (fwd S) a b) = (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) a b
    rw [← ContinuousAddEquiv.symm_apply_apply eT ((S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) a b)]
    congr 1
    funext i
    simp only [w, fwd]
    rw [herm_hinv _ (Matrix.isHermitian_mul_mul_conjTranspose _ (isHerm_map σ (θ i) (hP.conj i) S)),
      gl_sandwich3, heT]
    rfl
  have hri : ∀ y, fwd (bwd y) = y := by
    intro y; funext i
    simp only [fwd]
    rw [hmapb, gl_sandwich2, hinv_herm]
  have hadd : ∀ S T, fwd (S + T) = fwd S + fwd T := by
    intro S T; funext i a b
    have hm : ((S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) + (T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))).map (θ i) =
        (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) + (T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) := by
      ext; simp
    simp only [fwd, hinv, AddSubgroup.coe_add, hm, Matrix.mul_add, Matrix.add_mul, Pi.add_apply,
      Matrix.add_apply, Complex.add_re, Complex.add_im]
    ring
  have hc1 : Continuous fwd := by
    refine continuous_pi fun i => continuous_pi fun a => continuous_pi fun b => ?_
    simp only [fwd, hinv]
    have hm : Continuous fun S : HermR (Ainf F) σ n =>
        (A i).1 * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * ((A i).1)ᴴ :=
      (continuous_const.matrix_mul ((continuous_subtype_val).matrix_map (hP.cont i))).matrix_mul continuous_const
    have he : Continuous fun S : HermR (Ainf F) σ n =>
        ((A i).1 * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * ((A i).1)ᴴ) a b :=
      (continuous_apply b).comp ((continuous_apply a).comp hm)
    exact (Complex.continuous_re.comp he).add (Complex.continuous_im.comp he)
  have hc2 : Continuous bwd := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_pi fun a => continuous_pi fun b => eT.symm.continuous.comp (continuous_pi fun i => ?_)
    have hh : Continuous fun y : ι → WR.E n => herm (y i) := WR.I.continuous_herm.comp (continuous_apply i)
    exact (continuous_apply b).comp ((continuous_apply a).comp
      ((continuous_const.matrix_mul hh).matrix_mul continuous_const))
  let Ae : HermR (Ainf F) σ n ≃+ (ι → WR.E n) :=
    { toFun := fwd
      invFun := bwd
      left_inv := hli
      right_inv := hri
      map_add' := hadd }
  exact ⟨{ toAddEquiv := Ae, continuous_toFun := hc1, continuous_invFun := hc2 }, fun S i => rfl⟩

/- English proof (translation)
Take `⟨e, he⟩` from `exists_hermHomeo σ hCM ψ θ l hP (fun i => (g i)⁻¹)`. Conclude with `⟨e, funext fun S => funext fun i => he S i⟩`.
-/
theorem exists_ybHomeo (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ} (g : ι → GL (Fin n) ℂ) :
    ∃ e : HermR (Ainf F) σ n ≃ₜ+ (ι → WR.E n), ⇑e = ybAll σ θ g := by
  obtain ⟨e, he⟩ := exists_hermHomeo σ hCM ψ θ l hP (fun i => (g i)⁻¹)
  exact ⟨e, funext fun S => funext fun i => he S i⟩

/- English proof (translation)
Take `⟨e, he⟩` from `exists_hermHomeo σ hCM ψ θ l hP (fun i => star (g i))`. Use `⟨e, funext fun S => funext fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[he S i]`. Simplify using `[ygAll, Matrix.star_eq_conjTranspose]`.
-/
theorem exists_ygHomeo (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ} (g : ι → GL (Fin n) ℂ) :
    ∃ e : HermR (Ainf F) σ n ≃ₜ+ (ι → WR.E n), ⇑e = ygAll σ θ g := by
  obtain ⟨e, he⟩ := exists_hermHomeo σ hCM ψ θ l hP (fun i => star (g i))
  refine ⟨e, funext fun S => funext fun i => ?_⟩
  rw [he S i]
  simp [ygAll, Matrix.star_eq_conjTranspose]

/- English proof (translation)
Establish `h1 : (volume : Measure (WR.E n)).IsAddHaarMeasure`. Establish `: (volume : Measure (Fin n → Fin n → ℝ)) = Measure.pi (fun _ => volume)` using `rfl`. Rewrite using `[this]`. Conclude with `Measure.pi.isAddHaarMeasure _`. Establish `: (volume : Measure (ι → WR.E n)) = Measure.pi (fun _ => volume)` using `rfl`.

Rewrite using `[this]`. Conclude with `Measure.pi.isAddHaarMeasure _`.
-/
theorem haar_volE (ι : Type) [Fintype ι] (n : ℕ) : (volume : Measure (ι → WR.E n)).IsAddHaarMeasure := by
  have h1 : (volume : Measure (WR.E n)).IsAddHaarMeasure := by
    have : (volume : Measure (Fin n → Fin n → ℝ)) = Measure.pi (fun _ => volume) := rfl
    rw [this]; exact Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (ι → WR.E n)) = Measure.pi (fun _ => volume) := rfl
  rw [this]; exact Measure.pi.isAddHaarMeasure _

/- English proof (translation)
Establish `h0 : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure`. Establish `: (volume : Measure (Fin n → ℂ)) = Measure.pi (fun _ => volume)` using `rfl`. Rewrite using `[this]`. Conclude with `Measure.pi.isAddHaarMeasure _`. Establish `h1 : (volume : Measure (Fin M → Fin n → ℂ)).IsAddHaarMeasure`.

Establish `: (volume : Measure (Fin M → Fin n → ℂ)) = Measure.pi (fun _ => volume)` using `rfl`. Rewrite using `[this]`. Conclude with `Measure.pi.isAddHaarMeasure _`. Establish `: (volume : Measure (ι → Fin M → Fin n → ℂ)) = Measure.pi (fun _ => volume)` using `rfl`. Rewrite using `[this]`.

Conclude with `Measure.pi.isAddHaarMeasure _`.
-/
theorem haar_volW (ι : Type) [Fintype ι] (M n : ℕ) :
    (volume : Measure (ι → Fin M → Fin n → ℂ)).IsAddHaarMeasure := by
  have h0 : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := by
    have : (volume : Measure (Fin n → ℂ)) = Measure.pi (fun _ => volume) := rfl
    rw [this]; exact Measure.pi.isAddHaarMeasure _
  have h1 : (volume : Measure (Fin M → Fin n → ℂ)).IsAddHaarMeasure := by
    have : (volume : Measure (Fin M → Fin n → ℂ)) = Measure.pi (fun _ => volume) := rfl
    rw [this]; exact Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (ι → Fin M → Fin n → ℂ)) = Measure.pi (fun _ => volume) := rfl
  rw [this]; exact Measure.pi.isAddHaarMeasure _

/- English proof (translation)
Use `haveI : ContinuousAdd G := by`. Use `⟨?_⟩` and prove the remaining obligations. Establish `h : (fun p : G × G => p.1 + p.2) = fun p => e.symm (e p.1 + e p.2)`. Use function extensionality and compare the values at `p`. Rewrite using `[← map_add, ContinuousAddEquiv.symm_apply_apply]`.

Rewrite using `[h]`. Conclude with `e.symm.continuous.comp ((e.continuous.comp continuous_fst).add (e.continuous.comp continuous_snd))`. Use `haveI : (μ.map e).IsAddHaarMeasure := Measure.isAddHaarMeasure_map μ (e : G →+ W) e.continuous e.surjective e.toHomeomorph.isClosedEmbedding.tendsto_cocompact`. Use `⟨Measure.addHaarScalarFactor (μ.map e) vol, Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _, ?_⟩` and prove the remaining obligations. Conclude with `Measure.isAddLeftInvariant_eq_smul (μ.map e) vol`.
-/
theorem exists_map_eq_smul {G W : Type} [AddCommGroup G] [TopologicalSpace G]
    [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W] (vol : Measure W) [vol.IsAddHaarMeasure]
    (μ : Measure G) [μ.IsAddHaarMeasure] (e : G ≃ₜ+ W) :
    ∃ c : ℝ≥0, 0 < c ∧ μ.map e = c • vol := by
  haveI : ContinuousAdd G := by
    refine ⟨?_⟩
    have h : (fun p : G × G => p.1 + p.2) = fun p => e.symm (e p.1 + e p.2) := by
      funext p; rw [← map_add, ContinuousAddEquiv.symm_apply_apply]
    rw [h]
    exact e.symm.continuous.comp ((e.continuous.comp continuous_fst).add (e.continuous.comp continuous_snd))
  haveI : (μ.map e).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map μ (e : G →+ W) e.continuous e.surjective
      e.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  refine ⟨Measure.addHaarScalarFactor (μ.map e) vol,
    Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _, ?_⟩
  exact Measure.isAddLeftInvariant_eq_smul (μ.map e) vol

end PositivityTheory.SiegelWeilFormula.GReal
