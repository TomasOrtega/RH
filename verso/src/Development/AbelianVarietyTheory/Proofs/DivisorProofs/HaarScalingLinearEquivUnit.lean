import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCA
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddHaarLeftRightMulAdelicMatricesModule
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRestrictScalarsMatrixLeftRightMulAdeleTens
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LeviModulus
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.LeviModulus.CharVec

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Take `⟨hrs, A, hA⟩` from `hX.sig w`. Set `e : Fin n ≃ Fin r ⊕ Fin s` to `(finCongr hrs.symm).trans finSumFinEquiv.symm`. Use `set M := X.J.map (B.emb w).1 with hM`. Establish `h1 : (A.submatrix id e)ᵀ * M * (A.submatrix id e).map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e e`.

Rewrite using `[← hA]`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply]`. Establish `h2 : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).det ≠ 0`. Rewrite using `[Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]`.

Simplify using the standard rewrite rules. Establish `h3 : M.det ≠ 0`. Introduce `h0`. Apply `h2` to reduce the goal to its premises. Use `congrArg Matrix.det h1` as an intermediate fact.

Rewrite `this` using `[Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_mul, h0]`. Simplify using `using this.symm`. Introduce `hJ`. Apply `h3` to reduce the goal to its premises. Rewrite using `[hM, show X.J.map (B.emb w).1 = ((B.emb w).1 : E →+* ℂ).mapMatrix X.J from rfl, ← RingHom.map_det, hJ, map_zero]`.
-/
theorem det_ne_zero_of_isHerm (σ : E →ₐ[F] E) (B : Base F E) {n : ℕ} (X : Spc F E n) {r s : ℕ}
    (hX : X.IsHerm σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨hrs, A, hA⟩ := hX.sig w
  let e : Fin n ≃ Fin r ⊕ Fin s := (finCongr hrs.symm).trans finSumFinEquiv.symm
  set M := X.J.map (B.emb w).1 with hM
  have h1 : (A.submatrix id e)ᵀ * M * (A.submatrix id e).map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e e := by
    rw [← hA]
    ext i j
    simp [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply]
  have h2 : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]; simp
  have h3 : M.det ≠ 0 := by
    intro h0
    apply h2
    have := congrArg Matrix.det h1
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_mul, h0] at this
    simpa using this.symm
  intro hJ
  apply h3
  rw [hM, show X.J.map (B.emb w).1 = ((B.emb w).1 : E →+* ℂ).mapMatrix X.J from rfl, ← RingHom.map_det, hJ, map_zero]

/- English proof (translation)
Establish `hm : (g.1 : Matrix (Fin n) (Fin n) (AE F E))ᵀ * incM F J * (g.1 : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) = incM F J` using `g.2`. Establish `hd` using `congrArg Matrix.det hm`. Rewrite `hd` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]`. Establish `hmap : ((g.1 : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ)).det = cA σ (g.1 : Matrix (Fin n) (Fin n) (AE F E)).det` using `(RingHom.map_det (cA σ).toRingHom _).symm`. Establish `hJu : IsUnit (incM F J).det`.

Rewrite using `[show incM F J = (inclR (F := F) (AF F) : E →+* AE F E).mapMatrix J from rfl, ← RingHom.map_det]`. Conclude with `(isUnit_iff_ne_zero.2 hJ).map _`. Rewrite `hd` using `[hmap]`. Use `set dg := (g.1 : Matrix (Fin n) (Fin n) (AE F E)).det`. Establish `key : cA σ dg * dg = 1`.

Establish `e2 : cA σ dg * dg * (incM F J).det = 1 * (incM F J).det`. Rewrite using `[one_mul]`. Use `nth_rewrite 2 [← hd]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `hJu.mul_right_cancel e2`.

Establish `hu : GlobalTheory.Doubling.conjUnit σ (Matrix.GeneralLinearGroup.det g.1) * Matrix.GeneralLinearGroup.det g.1 = 1`. Use `ext`. Conclude with `key`. Establish `h2` using `congrArg (absE F E) hu`. Rewrite `h2` using `[map_mul, GlobalTheory.Doubling.absE_conjUnit, map_one, ← sq]`.

Conclude with `(pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).1 h2`.
-/
theorem absE_det_eq_one (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) (g : UA σ J) :
    absE F E (Matrix.GeneralLinearGroup.det g.1) = 1 := by
  have hm : (g.1 : Matrix (Fin n) (Fin n) (AE F E))ᵀ * incM F J * (g.1 : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) =
      incM F J := g.2
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have hmap : ((g.1 : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ)).det = cA σ (g.1 : Matrix (Fin n) (Fin n) (AE F E)).det :=
    (RingHom.map_det (cA σ).toRingHom _).symm
  have hJu : IsUnit (incM F J).det := by
    rw [show incM F J = (inclR (F := F) (AF F) : E →+* AE F E).mapMatrix J from rfl, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.2 hJ).map _
  rw [hmap] at hd
  set dg := (g.1 : Matrix (Fin n) (Fin n) (AE F E)).det
  have key : cA σ dg * dg = 1 := by
    have e2 : cA σ dg * dg * (incM F J).det = 1 * (incM F J).det := by
      rw [one_mul]; nth_rewrite 2 [← hd]; ring
    exact hJu.mul_right_cancel e2
  have hu : GlobalTheory.Doubling.conjUnit σ (Matrix.GeneralLinearGroup.det g.1) * Matrix.GeneralLinearGroup.det g.1 = 1 := by
    ext
    exact key
  have h2 := congrArg (absE F E) hu
  rw [map_mul, GlobalTheory.Doubling.absE_conjUnit, map_one, ← sq] at h2
  exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).1 h2

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n₁ X₁ r₁ s₁ hB hX _ _ _ _ l g₀ L hL`. Use `haveI : IsTotallyReal F := hB.cm.1`. Take `⟨-, -, hsc, -⟩` from `topAE F E`. Use `haveI := hsc`. Use `haveI : LocallyCompactSpace (Matrix (Fin n₁) (Fin 1) (AE F E)) := inferInstanceAs (LocallyCompactSpace (Fin n₁ → Fin 1 → AE F E))`.

Use `haveI : SecondCountableTopology (Matrix (Fin n₁) (Fin 1) (AE F E)) := inferInstanceAs (SecondCountableTopology (Fin n₁ → Fin 1 → AE F E))`. Use `letI : MeasurableSpace (Matrix (Fin n₁) (Fin 1) (AE F E)) := borel _`. Use `haveI : BorelSpace (Matrix (Fin n₁) (Fin 1) (AE F E)) := ⟨rfl⟩`. Set `c : (AE F E)ˣ` to `GlobalTheory.Doubling.conjUnit σ l`. Set `g : GL (Fin n₁) (AE F E)` to `Units.map (Matrix.scalar (Fin n₁) : AE F E →+* Matrix (Fin n₁) (Fin n₁) (AE F E)).toMonoidHom c * g₀.1`.

Establish `hg : (g : Matrix (Fin n₁) (Fin n₁) (AE F E)) = (c : AE F E) • mat g₀` using `by show Matrix.scalar (Fin n₁) (c : AE F E) * mat g₀ = _`. Rewrite using `[Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]`. Set `e : Matrix (Fin n₁) (Fin 1) (AE F E) ≃ₜ+ (Fin n₁ → AE F E)` to `{ toFun := fun u i => u i 0 invFun := fun a => Matrix.of fun i _ => a i left_inv := fun u => by`. Use extensionality with `i j`. Rewrite using `[Subsingleton.elim j 0]`.

Both sides reduce to the same expression. Use `right_inv := fun a => rfl`. Use the proof step `map_add' := fun u v => rfl`. Use `continuous_toFun := continuous_pi fun i => continuous_id.matrix_elem i 0`. Use `continuous_invFun := continuous_matrix fun i _ => continuous_apply i }`.

Establish `htr` using `GlobalTheory.ModuLR.addEquivAddHaarChar_transport e (GlobalTheory.ModuLR.lrCE g 1)`. Establish `hext : (e.symm.trans (GlobalTheory.ModuLR.lrCE g 1)).trans e = L`. Use extensionality with `a i`. Rewrite using `[hL]`. Use `show ((g : Matrix (Fin n₁) (Fin n₁) (AE F E)) * Matrix.of (fun i (_ : Fin 1) => a i) * ((1 : GL (Fin 1) (AE F E)) : Matrix (Fin 1) (Fin 1) (AE F E))) i 0 = ((c : AE F E) • (mat g₀ *ᵥ a)) i`.

Rewrite using `[hg, Units.val_one, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_apply, Pi.smul_apply]`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Rewrite `htr` using `[hext]`. Rewrite using `[htr, GlobalTheory.ModuLR.chi_lr F E n₁ 1 g 1, map_one, map_one, one_pow, mul_one, pow_one, map_mul, map_mul, absE_det_eq_one σ (det_ne_zero_of_isHerm σ B X₁ hX) g₀, mul_one]`. Establish `hdet : Matrix.GeneralLinearGroup.det (Units.map (Matrix.scalar (Fin n₁) : AE F E →+* Matrix (Fin n₁) (Fin n₁) (AE F E)).toMonoidHom c) = c ^ n₁`.

Use `ext`. Simplify using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_smul]`. Rewrite using `[hdet, map_pow, GlobalTheory.Doubling.absE_conjUnit]`.
-/
theorem haarChar_smul_mulVec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n₁ : ℕ) (X₁ : Spc F E n₁) (r₁ s₁ : ℕ), B.IsGood σ → X₁.IsHerm σ B r₁ s₁ →
    ∀ [IsTopologicalRing (AE F E)] [LocallyCompactSpace (AE F E)] [MeasurableSpace (Fin n₁ → AE F E)]
      [BorelSpace (Fin n₁ → AE F E)] (l : (AE F E)ˣ) (g₀ : UA σ X₁.J) (L : (Fin n₁ → AE F E) ≃ₜ+ (Fin n₁ → AE F E)),
      (∀ a, L a = cA σ l • (mat g₀ *ᵥ a)) → addEquivAddHaarChar L = absE F E l ^ n₁ := by
  intro F E _ _ _ _ _ σ B n₁ X₁ r₁ s₁ hB hX _ _ _ _ l g₀ L hL
  haveI : IsTotallyReal F := hB.cm.1
  obtain ⟨-, -, hsc, -⟩ := topAE F E
  haveI := hsc
  haveI : LocallyCompactSpace (Matrix (Fin n₁) (Fin 1) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n₁ → Fin 1 → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n₁) (Fin 1) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n₁ → Fin 1 → AE F E))
  letI : MeasurableSpace (Matrix (Fin n₁) (Fin 1) (AE F E)) := borel _
  haveI : BorelSpace (Matrix (Fin n₁) (Fin 1) (AE F E)) := ⟨rfl⟩
  let c : (AE F E)ˣ := GlobalTheory.Doubling.conjUnit σ l
  let g : GL (Fin n₁) (AE F E) :=
    Units.map (Matrix.scalar (Fin n₁) : AE F E →+* Matrix (Fin n₁) (Fin n₁) (AE F E)).toMonoidHom c * g₀.1
  have hg : (g : Matrix (Fin n₁) (Fin n₁) (AE F E)) = (c : AE F E) • mat g₀ := by
    show Matrix.scalar (Fin n₁) (c : AE F E) * mat g₀ = _
    rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  let e : Matrix (Fin n₁) (Fin 1) (AE F E) ≃ₜ+ (Fin n₁ → AE F E) :=
    { toFun := fun u i => u i 0
      invFun := fun a => Matrix.of fun i _ => a i
      left_inv := fun u => by
        ext i j
        rw [Subsingleton.elim j 0]
        rfl
      right_inv := fun a => rfl
      map_add' := fun u v => rfl
      continuous_toFun := continuous_pi fun i => continuous_id.matrix_elem i 0
      continuous_invFun := continuous_matrix fun i _ => continuous_apply i }
  have htr := GlobalTheory.ModuLR.addEquivAddHaarChar_transport e (GlobalTheory.ModuLR.lrCE g 1)
  have hext : (e.symm.trans (GlobalTheory.ModuLR.lrCE g 1)).trans e = L := by
    ext a i
    rw [hL]
    show ((g : Matrix (Fin n₁) (Fin n₁) (AE F E)) * Matrix.of (fun i (_ : Fin 1) => a i) *
      ((1 : GL (Fin 1) (AE F E)) : Matrix (Fin 1) (Fin 1) (AE F E))) i 0 = ((c : AE F E) • (mat g₀ *ᵥ a)) i
    rw [hg, Units.val_one, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_apply, Pi.smul_apply]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [hext] at htr
  rw [htr, GlobalTheory.ModuLR.chi_lr F E n₁ 1 g 1, map_one, map_one, one_pow, mul_one, pow_one, map_mul, map_mul,
    absE_det_eq_one σ (det_ne_zero_of_isHerm σ B X₁ hX) g₀, mul_one]
  have hdet : Matrix.GeneralLinearGroup.det
      (Units.map (Matrix.scalar (Fin n₁) : AE F E →+* Matrix (Fin n₁) (Fin n₁) (AE F E)).toMonoidHom c) = c ^ n₁ := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_smul]
  rw [hdet, map_pow, GlobalTheory.Doubling.absE_conjUnit]

end GlobalTheory.LeviModulus.CharVec
