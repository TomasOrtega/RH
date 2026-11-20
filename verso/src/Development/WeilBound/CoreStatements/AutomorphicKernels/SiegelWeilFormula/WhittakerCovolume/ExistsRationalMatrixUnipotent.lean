import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.FrameSignEqHermitianSign
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.RelAlg

noncomputable section

open scoped TensorProduct NNReal Matrix ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Introduce `x y h`. Use `congrArg Prod.fst h` as an intermediate fact. Conclude with `(algebraMap F (NumberField.InfiniteAdeleRing F)).injective this`.
-/
theorem rel_algebraMap_injective : Function.Injective (algebraMap F (AF F)) := by
  intro x y h
  have := congrArg Prod.fst h
  exact (algebraMap F (NumberField.InfiniteAdeleRing F)).injective this

/- English proof (translation)
The claim follows from `Algebra.TensorProduct.includeRight_injective rel_algebraMap_injective`.
-/
theorem rel_inclR_injective : Function.Injective (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective rel_algebraMap_injective

/- English proof (translation)
Introduce `X Y h`. Use extensionality with `i j`. Conclude with `rel_inclR_injective (congrFun (congrFun h i) j)`.
-/
theorem rel_incM_injective {a b : Type} : Function.Injective (incM F (E := E) (m := a) (n := b)) := by
  intro X Y h
  ext i j
  exact rel_inclR_injective (congrFun (congrFun h i) j)

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => simp [HeckeCharacterZeroLocus.SiegelWeilU.sigR, cA, Algebra.TensorProduct.map_tmul]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem rel_sigR_eq_cA (z : AE F E) : HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ z = cA σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [HeckeCharacterZeroLocus.SiegelWeilU.sigR, cA, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Take `⟨hrs, A, hA⟩` from `h`. Use `set S : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hS`. Establish `hSS : S * S = 1`. Simplify using `[S, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]`. Establish `hSu : IsUnit S` using `⟨⟨S, S, hSS, hSS⟩, rfl⟩`.

Establish `hrank : A.rank = m`. Apply `le_antisymm ((Matrix.rank_le_card_height A).trans (by simp))` to reduce the goal to its premises. Establish `h1 : S.rank = r + s`. Rewrite using `[Matrix.rank_of_isUnit S hSu]`. Simplify using the standard rewrite rules.

Establish `h2 : S.rank ≤ Aᵀ.rank`. Rewrite using `[← hA]`. Conclude with `(Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_left _ _)`. Rewrite `h2` using `[Matrix.rank_transpose]`. Use linear arithmetic over natural numbers and integers.

Establish `hsurj : ∃ w, A *ᵥ w = z`. Establish `: LinearMap.range A.mulVecLin = ⊤`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[← Matrix.rank, hrank]`. Simplify using the standard rewrite rules.

Conclude with `LinearMap.range_eq_top.mp this z`. Take `⟨w, rfl⟩` from `hsurj`. Establish `hw : w ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hz`.

Establish `hst : star (A *ᵥ w) = A.map star *ᵥ star w`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, star_sum, mul_comm]`. Establish `key : (A *ᵥ w) ⬝ᵥ M *ᵥ star (A *ᵥ w) = w ⬝ᵥ S *ᵥ star w`. Rewrite using `[hst, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc, hA]`.

Rewrite using `[key]`. Establish `hne : w ⬝ᵥ star w ≠ 0`. Rewrite using `[dotProduct_comm]`. Conclude with `fun h => hw (dotProduct_star_self_eq_zero.mp h)`. Break down `Nat.min_eq_zero_iff.mp h0 with hr | hs` into its components or cases.

Substitute `hr` using the available equality. Establish `: S *ᵥ star w = -star w`. Use extensionality with `k`. Break down `k with i | j` into its components or cases. Conclude with `i.elim0`.

Simplify using `[S, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type, Matrix.one_apply]`. Rewrite using `[this, dotProduct_neg]`. Conclude with `neg_ne_zero.mpr hne`. Substitute `hs` using the available equality. Establish `: S *ᵥ star w = star w`.

Use extensionality with `k`. Break down `k with i | j` into its components or cases. Simplify using `[S, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type, Matrix.one_apply]`. Conclude with `j.elim0`. Rewrite using `[this]`.

Conclude with `hne`.
-/
theorem rel_definite {m r s : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (h : HasSig M r s) (h0 : min r s = 0)
    (z : Fin m → ℂ) (hz : z ≠ 0) : z ⬝ᵥ M *ᵥ star z ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  set S : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hS
  have hSS : S * S = 1 := by
    simp [S, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hSu : IsUnit S := ⟨⟨S, S, hSS, hSS⟩, rfl⟩
  have hrank : A.rank = m := by
    apply le_antisymm ((Matrix.rank_le_card_height A).trans (by simp))
    have h1 : S.rank = r + s := by
      rw [Matrix.rank_of_isUnit S hSu]
      simp
    have h2 : S.rank ≤ Aᵀ.rank := by
      rw [← hA]
      exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_left _ _)
    rw [Matrix.rank_transpose] at h2
    omega
  have hsurj : ∃ w, A *ᵥ w = z := by
    have : LinearMap.range A.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [← Matrix.rank, hrank]
      simp
    exact LinearMap.range_eq_top.mp this z
  obtain ⟨w, rfl⟩ := hsurj
  have hw : w ≠ 0 := by
    rintro rfl
    simp at hz
  have hst : star (A *ᵥ w) = A.map star *ᵥ star w := by
    ext i
    simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]
  have key : (A *ᵥ w) ⬝ᵥ M *ᵥ star (A *ᵥ w) = w ⬝ᵥ S *ᵥ star w := by
    rw [hst, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
      ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc, hA]
  rw [key]
  have hne : w ⬝ᵥ star w ≠ 0 := by
    rw [dotProduct_comm]
    exact fun h => hw (dotProduct_star_self_eq_zero.mp h)
  rcases Nat.min_eq_zero_iff.mp h0 with hr | hs
  · subst hr
    have : S *ᵥ star w = -star w := by
      ext k
      rcases k with i | j
      · exact i.elim0
      · simp [S, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type, Matrix.one_apply]
    rw [this, dotProduct_neg]
    exact neg_ne_zero.mpr hne
  · subst hs
    have : S *ᵥ star w = star w := by
      ext k
      rcases k with i | j
      · simp [S, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type, Matrix.one_apply]
      · exact j.elim0
    rw [this]
    exact hne

/- English proof (translation)
Assume the negation of the conclusion as `hy0`. Set `w : InfinitePlace F` to `Classical.arbitrary _`. Set `τ : E →+* ℂ` to `(d.B.emb w).1`. Establish `hτ : ∀ x, τ (σ x) = star (τ x)` using `d.ok.good.cm.2.2.2 τ`. Set `z : Fin d.m → ℂ` to `fun i => τ (y i)`.

Establish `hz : z ≠ 0`. Introduce `h`. Apply `hy0` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Apply `τ.injective` to reduce the goal to its premises.

Simplify `congrFun h i` using `[z]`. Establish `key : τ (HeckeCharacterZeroLocus.SiegelWeilU.hE σ (Jd d η) y y) = τ η * (z ⬝ᵥ (d.A.J.map τ) *ᵥ star z)`. Simplify using `only [HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Jd, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Finset.mul_sum, Pi.star_apply]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [z]`. Rewrite using `[show ((σ : E →+* E) (y j)) = σ (y j) from rfl, hτ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[hy, map_zero]`. Establish `hQ : z ⬝ᵥ (d.A.J.map τ) *ᵥ star z ≠ 0`.

Break down `d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩` into its components or cases. Conclude with `rel_definite _ (hA.sig w) d.ok.aniso z hz`. Establish `h1` using `rel_definite _ (hA.sig w) d.ok.aniso z hz`. Introduce `h0`. Apply `h1` to reduce the goal to its premises.

Simplify using `only [Matrix.smul_mulVec, dotProduct_smul]`. Express the relevant statement in the definitionally equal form `Complex.I • (z ⬝ᵥ d.A.J.map τ *ᵥ star z) = 0`. Rewrite using `[h0, smul_zero]`. Establish `hτη : τ η ≠ 0` using `(map_ne_zero τ).mpr hη`. Conclude with `(mul_ne_zero hτη hQ) key.symm`.
-/
theorem rel_aniso (d : SD σ) (η : E) (hη : η ≠ 0) (y : Fin d.m → E)
    (hy : HeckeCharacterZeroLocus.SiegelWeilU.hE σ (Jd d η) y y = 0) : y = 0 := by
  by_contra hy0
  let w : InfinitePlace F := Classical.arbitrary _
  let τ : E →+* ℂ := (d.B.emb w).1
  have hτ : ∀ x, τ (σ x) = star (τ x) := d.ok.good.cm.2.2.2 τ
  let z : Fin d.m → ℂ := fun i => τ (y i)
  have hz : z ≠ 0 := by
    intro h
    apply hy0
    funext i
    apply τ.injective
    simpa [z] using congrFun h i
  have key : τ (HeckeCharacterZeroLocus.SiegelWeilU.hE σ (Jd d η) y y) = τ η * (z ⬝ᵥ (d.A.J.map τ) *ᵥ star z) := by
    simp only [HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Jd, Matrix.mulVec, dotProduct, map_sum, map_mul,
      Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Finset.mul_sum, Pi.star_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [z]
    rw [show ((σ : E →+* E) (y j)) = σ (y j) from rfl, hτ]
    ring
  rw [hy, map_zero] at key
  have hQ : z ⬝ᵥ (d.A.J.map τ) *ᵥ star z ≠ 0 := by
    rcases d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩
    · exact rel_definite _ (hA.sig w) d.ok.aniso z hz
    · have h1 := rel_definite _ (hA.sig w) d.ok.aniso z hz
      intro h0
      apply h1
      simp only [Matrix.smul_mulVec, dotProduct_smul]
      change Complex.I • (z ⬝ᵥ d.A.J.map τ *ᵥ star z) = 0
      rw [h0, smul_zero]
  have hτη : τ η ≠ 0 := (map_ne_zero τ).mpr hη
  exact (mul_ne_zero hτη hQ) key.symm

/- English proof (translation)
Take `⟨T, hT⟩` from `T`. Proceed by induction on `hT using AddSubgroup.closure_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `zero => exact ⟨0, by ext i j; simp [incM]⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨X, hX⟩` from `hx`. Take `⟨Y, hY⟩` from `hy`. Use `⟨X + Y, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x.1 + y.1 = _`. Rewrite using `[hX, hY]`.

Use extensionality with `i j`. Simplify using `[incM]`. Consider the case `neg x _ hx`. Take `⟨X, hX⟩` from `hx`. Use `⟨-X, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `-x.1 = _`. Rewrite using `[hX]`. Use extensionality with `i j`. Simplify using `[incM]`.
-/
theorem exists_rational_matrix_unipotent (d : SD σ) (T : nF σ d.Y d.b) : ∃ T₀ : Matrix (Fin d.n) (Fin d.n) E, T.1.1 = incM F T₀ := by
  obtain ⟨T, hT⟩ := T
  induction hT using AddSubgroup.closure_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, by ext i j; simp [incM]⟩
  | add x y _ _ hx hy =>
    obtain ⟨X, hX⟩ := hx
    obtain ⟨Y, hY⟩ := hy
    refine ⟨X + Y, ?_⟩
    change x.1 + y.1 = _
    rw [hX, hY]
    ext i j
    simp [incM]
  | neg x _ hx =>
    obtain ⟨X, hX⟩ := hx
    refine ⟨-X, ?_⟩
    change -x.1 = _
    rw [hX]
    ext i j
    simp [incM]

def relH (d : SD σ) (η : E) (β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  -(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η⁻¹ • β.1ᵀ)

/- English proof (translation)
Introduce `a b`. Establish `hn` using `congrFun (congrFun (rel_nA_cond d ε hε β) a) b`. Simplify using `only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply] at hn`. Establish `he2 : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1`. Rewrite using `[← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]`.

Simplify using the standard rewrite rules. Establish `hinv : σ η⁻¹ = -(((ε : ℤ) : E) * η⁻¹)`. Rewrite using `[map_inv₀, hση, inv_neg, mul_inv, inv_eq_of_mul_eq_one_right he2]`. Establish `hc : ∀ x : E, cA σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F` using `F) (AF F) x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (σ x) := by`. Introduce `x`.

Simplify using `[cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]`. Simplify using `only [relH, Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]`. Rewrite using `[map_neg, map_mul, rel_sigR_eq_cA, rel_sigR_eq_cA, hc, hinv, map_neg, map_mul, map_intCast]`. Take the linear combination `(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η⁻¹) * hn`.
-/
theorem relH_mem (d : SD σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (η : E) (hη : η ≠ 0)
    (hση : σ η = -(((ε : ℤ) : E) * η)) (β : nA σ d.Y d.b) :
    relH d η β ∈ HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n := by
  intro a b
  have hn := congrFun (congrFun (rel_nA_cond d ε hε β) a) b
  simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    Matrix.zero_apply] at hn
  have he2 : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  have hinv : σ η⁻¹ = -(((ε : ℤ) : E) * η⁻¹) := by
    rw [map_inv₀, hση, inv_neg, mul_inv, inv_eq_of_mul_eq_one_right he2]
  have hc : ∀ x : E, cA σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (σ x) := by
    intro x
    simp [cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]
  simp only [relH, Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
  rw [map_neg, map_mul, rel_sigR_eq_cA, rel_sigR_eq_cA, hc, hinv, map_neg, map_mul, map_intCast]
  linear_combination (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η⁻¹) * hn

/- English proof (translation)
Establish `h1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F` using `F) (E := E) (AF F) η * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) η⁻¹ = 1 := by`. Rewrite using `[← map_mul, mul_inv_cancel₀ hη, map_one]`. Use extensionality with `i j`. Simplify using `[relH, incM, Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, ← mul_assoc, h1]`. Rewrite using `[mul_comm (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η⁻¹), h1, one_mul]`.
-/
theorem relH_eq (d : SD σ) (η : E) (hη : η ≠ 0) (β : nA σ d.Y d.b) :
    β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * (relH d η β)ᵀ) := by
  have h1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) η⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hη, map_one]
  ext i j
  simp [relH, incM, Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, ← mul_assoc, h1]
  rw [mul_comm (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η⁻¹), h1, one_mul]

/- English proof (translation)
Establish `hn` using `rel_nA_cond d ε hε T.1`. Rewrite `hn` using `[h0, rel_cA_incM]`. Establish `hn' : incM F (T₀ᵀ + ((ε : ℤ) : E) • T₀.map σ) = incM F 0`. Establish `e0 : incM F (0 : Matrix (Fin d.n) (Fin d.n) E) = 0`. Use extensionality with `i j`.

Simplify using `[incM]`. Rewrite using `[e0, ← hn]`. Use extensionality with `i j`. Simplify using `[incM]`. Establish `hz` using `rel_incM_injective hn'`.

Use `⟨fun a b => ?_, ?_⟩` and prove the remaining obligations. Establish `he` using `congrFun (congrFun hz a) b`. Simplify using `only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply] at he`. Simplify using `only [Td, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[map_mul, map_mul, map_neg, map_ofNat, hση]`.

Take the linear combination `(2 * η) * he`. Establish `hdet : T₀.det ≠ 0`. Introduce `h`. Apply `hT` to reduce the goal to its premises. Use `show (T.1.1).det = 0`.

Rewrite using `[h0, incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]`. Simplify using `only [Td, Matrix.det_transpose, Matrix.det_smul]`. Conclude with `mul_ne_zero (pow_ne_zero _ (mul_ne_zero (neg_ne_zero.mpr two_ne_zero) hη)) hdet`.
-/
theorem rel_Td (d : SD σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (η : E) (hη : η ≠ 0)
    (hση : σ η = -(((ε : ℤ) : E) * η)) (T : nF σ d.Y d.b) (hT : IsND T) (T₀ : Matrix (Fin d.n) (Fin d.n) E)
    (h0 : T.1.1 = incM F T₀) : (∀ a b, σ (Td η T₀ b a) = Td η T₀ a b) ∧ (Td η T₀).det ≠ 0 := by
  have hn := rel_nA_cond d ε hε T.1
  rw [h0, rel_cA_incM] at hn
  have hn' : incM F (T₀ᵀ + ((ε : ℤ) : E) • T₀.map σ) = incM F 0 := by
    have e0 : incM F (0 : Matrix (Fin d.n) (Fin d.n) E) = 0 := by
      ext i j
      simp [incM]
    rw [e0, ← hn]
    ext i j
    simp [incM]
  have hz := rel_incM_injective hn'
  refine ⟨fun a b => ?_, ?_⟩
  · have he := congrFun (congrFun hz a) b
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Matrix.zero_apply] at he
    simp only [Td, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
    rw [map_mul, map_mul, map_neg, map_ofNat, hση]
    linear_combination (2 * η) * he
  · have hdet : T₀.det ≠ 0 := by
      intro h
      apply hT
      show (T.1.1).det = 0
      rw [h0, incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
    simp only [Td, Matrix.det_transpose, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero (neg_ne_zero.mpr two_ne_zero) hη)) hdet

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d`. Take `⟨⟨ε, hε⟩, -⟩` from `d.ok.frame`. Take `⟨η, hη, hση, hherm⟩` from `rel_eta d ε hε`. Use `⟨η, fun β => ⟨relH d η β, relH_mem d ε hε η hη hση β⟩, hη, hherm, fun β => relH_eq d η hη β, fun y hy => rel_aniso d η hη y hy, d.ok.good.cm, ⟨fun i j => ?_, ?_⟩, fun T hT => ?_⟩` and prove the remaining obligations. Simplify using `only [Jd, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]`.

Conclude with `hherm j i`. Introduce `h0`. Take `⟨y, hy0, hy⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr h0`. Apply `hy0` to reduce the goal to its premises. Apply `rel_aniso d η hη y` to reduce the goal to its premises.

Establish `h2 : HeckeCharacterZeroLocus.SiegelWeilU.hE σ (Jd d η) y y = ∑ i, σ (y i) * (Jd d η *ᵥ y) i`. Simplify using `only [HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]`. Both sides reduce to the same expression. Rewrite using `[h2, hy]`. Simplify using the standard rewrite rules.

Take `⟨T₀, h0⟩` from `exists_rational_matrix_unipotent d T`. Conclude with `⟨T₀, h0, rel_Td d ε hε η hη hση T hT T₀ h0⟩`.
-/
theorem relAlg_pf : RelAlg := by
  intro F E _ _ _ _ _ σ d
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨η, hη, hση, hherm⟩ := rel_eta d ε hε
  refine ⟨η, fun β => ⟨relH d η β, relH_mem d ε hε η hη hση β⟩, hη, hherm, fun β => relH_eq d η hη β,
    fun y hy => rel_aniso d η hη y hy, d.ok.good.cm, ⟨fun i j => ?_, ?_⟩, fun T hT => ?_⟩
  · simp only [Jd, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
    exact hherm j i
  · intro h0
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hy0
    apply rel_aniso d η hη y
    have h2 : HeckeCharacterZeroLocus.SiegelWeilU.hE σ (Jd d η) y y = ∑ i, σ (y i) * (Jd d η *ᵥ y) i := by
      simp only [HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      rfl
    rw [h2, hy]
    simp
  · obtain ⟨T₀, h0⟩ := exists_rational_matrix_unipotent d T
    exact ⟨T₀, h0, rel_Td d ε hε η hη hση T hT T₀ h0⟩

end PositivityTheory.SiegelWeilFormula.KWhit

end
