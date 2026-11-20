import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA

namespace PlaceMaps

section Lemmas

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]

open Classical in

/- English proof (translation)
Use `show Pi.single v x v = x`. Simplify using the standard rewrite rules.
-/
theorem evalAt_singleF_self (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    evalAt F v (singleF F v x) = x := by
  show Pi.single v x v = x
  simp

open Classical in

/- English proof (translation)
Use `show Pi.single v x w = 0`. Simplify using `[h]`.
-/
theorem evalAt_singleF_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (x : v.adicCompletion F) :
    evalAt F w (singleF F v x) = 0 := by
  show Pi.single v x w = 0
  simp [h]

open Classical in

/- English proof (translation)
Apply `FiniteAdeleRing.ext` to reduce the goal to its premises. Introduce `w`. Express the relevant statement in the definitionally equal form `Pi.single v (x * y) w = Pi.single v x w * Pi.single v y w`. Distinguish the cases in `h : w = v`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
theorem singleF_mul (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletion F) :
    singleF F v (x * y) = singleF F v x * singleF F v y := by
  apply FiniteAdeleRing.ext; intro w
  change Pi.single v (x * y) w = Pi.single v x w * Pi.single v y w
  by_cases h : w = v
  · subst h; simp
  · simp [h]

open Classical in

/- English proof (translation)
Apply `FiniteAdeleRing.ext` to reduce the goal to its premises. Introduce `u`. Express the relevant statement in the definitionally equal form `Pi.single v x u * Pi.single w y u = 0`. Distinguish the cases in `hu : u = v`. Substitute `hu` using the available equality.

Simplify using `[Ne.symm h]`. Simplify using `[hu]`.
-/
theorem singleF_mul_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (x : v.adicCompletion F)
    (y : w.adicCompletion F) : singleF F v x * singleF F w y = 0 := by
  apply FiniteAdeleRing.ext; intro u
  change Pi.single v x u * Pi.single w y u = 0
  by_cases hu : u = v
  · subst hu; simp [Ne.symm h]
  · simp [hu]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem compAt_tmul (v : HeightOneSpectrum (𝓞 F)) (a : FiniteAdeleRing (𝓞 F) F) (b : E) :
    compAt E v (a ⊗ₜ b) = evalAt F v a ⊗ₜ b := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem singleV_tmul (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F) (b : E) :
    singleV E v (a ⊗ₜ b) = singleF F v a ⊗ₜ b := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sigA_tmul (c : E ≃ₐ[F] E) (a : FiniteAdeleRing (𝓞 F) F) (b : E) :
    sigA c (a ⊗ₜ b) = a ⊗ₜ c b := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sigV_tmul (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F) (b : E) :
    sigV c v (a ⊗ₜ b) = a ⊗ₜ c b := rfl

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => rw [singleV_tmul, compAt_tmul, evalAt_singleF_self]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem compAt_singleV_self (v : HeightOneSpectrum (𝓞 F)) (x : Kv E v) :
    compAt E v (singleV E v x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [singleV_tmul, compAt_tmul, evalAt_singleF_self]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => rw [singleV_tmul, compAt_tmul, evalAt_singleF_ne h, zero_tmul]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]`.
-/
theorem compAt_singleV_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (x : Kv E v) :
    compAt E w (singleV E v x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [singleV_tmul, compAt_tmul, evalAt_singleF_ne h, zero_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x x' hx hx' => rw [add_mul, map_add, map_add, hx, hx', add_mul]`. Consider the case `tmul a b`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add y y' hy hy' => rw [mul_add, map_add, map_add, hy, hy', mul_add]`. Consider the case `tmul a' b'`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, singleV_tmul, singleV_tmul, singleV_tmul, Algebra.TensorProduct.tmul_mul_tmul, singleF_mul]`.
-/
theorem singleV_mul (v : HeightOneSpectrum (𝓞 F)) (x y : Kv E v) :
    singleV E v (x * y) = singleV E v x * singleV E v y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [add_mul, map_add, map_add, hx, hx', add_mul]
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => rw [mul_add, map_add, map_add, hy, hy', mul_add]
    | tmul a' b' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, singleV_tmul, singleV_tmul, singleV_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, singleF_mul]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x x' hx hx' => rw [map_add, add_mul, hx, hx', add_zero]`. Consider the case `tmul a b`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add y y' hy hy' => rw [map_add, mul_add, hy, hy', add_zero]`. Consider the case `tmul a' b'`. Rewrite using `[singleV_tmul, singleV_tmul, Algebra.TensorProduct.tmul_mul_tmul, singleF_mul_ne h, zero_tmul]`.
-/
theorem singleV_mul_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (x : Kv E v) (y : Kv E w) :
    singleV E v x * singleV E w y = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [map_add, add_mul, hx, hx', add_zero]
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => rw [map_add, mul_add, hy, hy', add_zero]
    | tmul a' b' =>
      rw [singleV_tmul, singleV_tmul, Algebra.TensorProduct.tmul_mul_tmul, singleF_mul_ne h,
        zero_tmul]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x x' hx hx' => rw [add_mul, map_add, map_add, hx, hx', add_mul]`. Consider the case `tmul a b => show singleV E v (a ⊗ₜ b * 1 ⊗ₜ y) = singleV E v (a ⊗ₜ b) * (1 ⊗ₜ y)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, singleV_tmul, singleV_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one]`.
-/
theorem singleV_mul_inclV (v : HeightOneSpectrum (𝓞 F)) (x : Kv E v) (y : E) :
    singleV E v (x * inclV E v y) = singleV E v x * inclA F E y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [add_mul, map_add, map_add, hx, hx', add_mul]
  | tmul a b =>
    show singleV E v (a ⊗ₜ b * 1 ⊗ₜ y) = singleV E v (a ⊗ₜ b) * (1 ⊗ₜ y)
    rw [Algebra.TensorProduct.tmul_mul_tmul, singleV_tmul, singleV_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]`. Consider the case `tmul a b => rw [singleV_tmul, sigA_tmul, sigV_tmul, singleV_tmul]`.
-/
theorem sigA_singleV (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : Kv E v) :
    sigA c (singleV E v x) = singleV E v (sigV c v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  | tmul a b => rw [singleV_tmul, sigA_tmul, sigV_tmul, singleV_tmul]

/- English proof (translation)
Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]`. Consider the case `tmul a b => rw [sigA_tmul, compAt_tmul, compAt_tmul, sigV_tmul]`.
-/
theorem compAt_sigA (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : AE F E) :
    compAt E v (sigA c a) = sigV c v (compAt E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  | tmul a b => rw [sigA_tmul, compAt_tmul, compAt_tmul, sigV_tmul]

/- English proof (translation)
Use `show compAt E v (1 ⊗ₜ x) = 1 ⊗ₜ x`. Rewrite using `[compAt_tmul, map_one]`.
-/
theorem compAt_inclA (v : HeightOneSpectrum (𝓞 F)) (x : E) :
    compAt E v (inclA F E x) = inclV E v x := by
  show compAt E v (1 ⊗ₜ x) = 1 ⊗ₜ x
  rw [compAt_tmul, map_one]

/- English proof (translation)
Set `𝒞` to `Module.Free.chooseBasis F E`. Establish `key : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : AE F E) k, equivFinsuppOfBasisRight 𝒞 (compAt E v x) k = evalAt F v (equivFinsuppOfBasisRight 𝒞 x k)`. Introduce `v x k`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a b`. Rewrite using `[compAt_tmul, equivFinsuppOfBasisRight_apply_tmul_apply, equivFinsuppOfBasisRight_apply_tmul_apply, map_smul]`. Consider the case `add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]`. Apply `(equivFinsuppOfBasisRight 𝒞).injective` to reduce the goal to its premises. Use `Finsupp.ext fun k => FiniteAdeleRing.ext _ fun w => ?_` and prove the remaining obligations.

Establish `hk` using `congrArg (fun z => equivFinsuppOfBasisRight 𝒞 z k) (h w)`. Simplify using `only [key] at hk`. Conclude with `hk`.
-/
theorem compAt_separates (a b : AE F E) (h : ∀ v, compAt E v a = compAt E v b) : a = b := by
  let 𝒞 := Module.Free.chooseBasis F E
  have key : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : AE F E) k,
      equivFinsuppOfBasisRight 𝒞 (compAt E v x) k =
        evalAt F v (equivFinsuppOfBasisRight 𝒞 x k) := by
    intro v x k
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [compAt_tmul, equivFinsuppOfBasisRight_apply_tmul_apply,
        equivFinsuppOfBasisRight_apply_tmul_apply, map_smul]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  apply (equivFinsuppOfBasisRight 𝒞).injective
  refine Finsupp.ext fun k => FiniteAdeleRing.ext _ fun w => ?_
  have hk := congrArg (fun z => equivFinsuppOfBasisRight 𝒞 z k) (h w)
  simp only [key] at hk
  exact hk

/- English proof (translation)
Use extensionality with `i j`. Conclude with `compAt_separates _ _ fun v => congrFun (congrFun (h v) i) j`.
-/
theorem matrix_separates {N : ℕ} (X Y : Matrix (Fin N) (Fin N) (AE F E))
    (h : ∀ v, X.map (compAt E v) = Y.map (compAt E v)) : X = Y := by
  ext i j
  exact compAt_separates _ _ fun v => congrFun (congrFun (h v) i) j

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [embed, hij, compAt_singleV_self]`.
-/
theorem embed_map_self (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (g : Matrix (Fin N) (Fin N) (Kv E v)) :
    (embed E v g).map (compAt E v) = g := by
  ext i j
  by_cases hij : i = j <;> simp [embed, hij, compAt_singleV_self]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [embed, Matrix.one_apply, hij, compAt_singleV_ne h]`.
-/
theorem embed_map_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) {N : ℕ}
    (g : Matrix (Fin N) (Fin N) (Kv E v)) : (embed E v g).map (compAt E w) = 1 := by
  ext i j
  by_cases hij : i = j <;> simp [embed, Matrix.one_apply, hij, compAt_singleV_ne h]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[compAt_inclA]`.
-/
theorem inclA_map_compAt (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) :
    (J.map (inclA F E)).map (compAt E v) = J.map (inclV E v) := by
  ext i j
  simp [compAt_inclA]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[compAt_sigA]`.
-/
theorem sigA_map_compAt (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {N : ℕ}
    (X : Matrix (Fin N) (Fin N) (AE F E)) :
    (X.map (sigA c)).map (compAt E v) = (X.map (compAt E v)).map (sigV c v).toRingHom := by
  ext i j
  simp [compAt_sigA]

/- English proof (translation)
Rewrite using `[Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, inclA_map_compAt, sigA_map_compAt]`.
-/
theorem form_map_compAt (c : E ≃ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (X : Matrix (Fin N) (Fin N) (AE F E)) :
    (Xᵀ * J.map (inclA F E) * X.map (sigA c)).map (compAt E w) =
      (X.map (compAt E w))ᵀ * J.map (inclV E w) * (X.map (compAt E w)).map (sigV c w).toRingHom := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, inclA_map_compAt, sigA_map_compAt]

end Lemmas

/- English proof (translation)
Introduce `F E _ _ _ _ _ c _ _`. Use `⟨compAt_separates, fun v => ⟨compAt_singleV_self v, fun w h => compAt_singleV_ne h, singleV_mul v, fun w h => singleV_mul_ne h, singleV_mul_inclV v, sigA_singleV c v, compAt_sigA c v, compAt_inclA v, fun N => ⟨?_, ?_, fun J => ⟨?_, ?_⟩⟩⟩⟩` and prove the remaining obligations. Apply `matrix_separates` to reduce the goal to its premises. Introduce `w`. Distinguish the cases in `hw : w = v`.

Substitute `hw` using the available equality. Rewrite using `[embed_map_self]`. Simplify using the standard rewrite rules. Rewrite using `[embed_map_ne hw]`. Simplify using the standard rewrite rules.

Introduce `g h`. Apply `matrix_separates` to reduce the goal to its premises. Introduce `w`. Rewrite using `[Matrix.map_mul]`. Distinguish the cases in `hw : w = v`.

Substitute `hw` using the available equality. Rewrite using `[embed_map_self, embed_map_self, embed_map_self]`. Rewrite using `[embed_map_ne hw, embed_map_ne hw, embed_map_ne hw, mul_one]`. Introduce and unpack `g ⟨hdet, hJ⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Apply `compAt_separates` to reduce the goal to its premises. Introduce `w`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, map_one]`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality.

Rewrite using `[embed_map_self, hdet]`. Rewrite using `[embed_map_ne hw, det_one]`. Apply `matrix_separates` to reduce the goal to its premises. Introduce `w`. Rewrite using `[form_map_compAt, inclA_map_compAt]`.

Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[embed_map_self]`. Conclude with `hJ`. Rewrite using `[embed_map_ne hw]`.

Simplify using the standard rewrite rules. Introduce and unpack `x ⟨hdet, hJ⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]`. Establish `: (xᵀ * J.map (inclA F E) * x.map (sigA c)).map (compAt E v) = (J.map (inclA F E)).map (compAt E v)` using `by rw [hJ]`.

Rewrite `this` using `[form_map_compAt, inclA_map_compAt]`. Conclude with `this`.
-/
theorem intersectionNumber_baseChange : PlaceMaps.Statement := by
  intro F E _ _ _ _ _ c _ _
  refine ⟨compAt_separates, fun v => ⟨compAt_singleV_self v, fun w h => compAt_singleV_ne h,
    singleV_mul v, fun w h => singleV_mul_ne h, singleV_mul_inclV v, sigA_singleV c v,
    compAt_sigA c v, compAt_inclA v, fun N => ⟨?_, ?_, fun J => ⟨?_, ?_⟩⟩⟩⟩
  · apply matrix_separates; intro w
    by_cases hw : w = v
    · subst hw; rw [embed_map_self]; simp
    · rw [embed_map_ne hw]; simp
  · intro g h
    apply matrix_separates; intro w
    rw [Matrix.map_mul]
    by_cases hw : w = v
    · subst hw; rw [embed_map_self, embed_map_self, embed_map_self]
    · rw [embed_map_ne hw, embed_map_ne hw, embed_map_ne hw, mul_one]
  · rintro g ⟨hdet, hJ⟩
    refine ⟨?_, ?_⟩
    · apply compAt_separates; intro w
      rw [RingHom.map_det, RingHom.mapMatrix_apply, map_one]
      by_cases hw : w = v
      · subst hw; rw [embed_map_self, hdet]
      · rw [embed_map_ne hw, det_one]
    · apply matrix_separates; intro w
      rw [form_map_compAt, inclA_map_compAt]
      by_cases hw : w = v
      · subst hw; rw [embed_map_self]; exact hJ
      · rw [embed_map_ne hw]; simp
  · rintro x ⟨hdet, hJ⟩
    refine ⟨?_, ?_⟩
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]
    · have : (xᵀ * J.map (inclA F E) * x.map (sigA c)).map (compAt E v) =
          (J.map (inclA F E)).map (compAt E v) := by rw [hJ]
      rw [form_map_compAt, inclA_map_compAt] at this
      exact this

/- English proof (translation)
The claim follows from `intersectionNumber_baseChange`.
-/
theorem proof (_h : LocalRingHypotheses.Statement) : PlaceMaps.Statement := intersectionNumber_baseChange

end PlaceMaps

end StrongApprox

end GroundTheory.Heights₂.Heights
