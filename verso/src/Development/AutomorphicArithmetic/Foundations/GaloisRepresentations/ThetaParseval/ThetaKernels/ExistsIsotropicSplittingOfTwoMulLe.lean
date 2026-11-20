import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.BumpLat
import Development.WeilBound.ThetaLifts.LatticeBasics.CompCA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseFrameB

set_option synthInstance.maxHeartbeats 200000

section
open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels UpperTheory.TP.BA
noncomputable section
/- English proof (translation)
Set `f₁ : Fin n → Fin d` to `fun i => ⟨i, by omega⟩`. Set `f₂ : Fin n → Fin d` to `fun i => ⟨i + n, by omega⟩`. Establish `i₁ : Function.Injective f₁` using `fun a b h => Fin.ext (by simpa [f₁] using h)`. Establish `i₂ : Function.Injective f₂` using `fun a b h => Fin.ext (by simpa [f₂] using h)`. Establish `dj : ∀ a b, f₁ a ≠ f₂ b` using `fun a b h => by`.

Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only [f₁, f₂] at this`. Use linear arithmetic over natural numbers and integers. Establish `key : ∀ f g : Fin n → Fin d, ((1 : Matrix (Fin d) (Fin d) A).submatrix id f)ᵀ * (1 : Matrix (Fin d) (Fin d) A).submatrix id g = (1 : Matrix (Fin d) (Fin d) A).submatrix f g` using `fun f g => by`. Rewrite using `[Matrix.transpose_submatrix, Matrix.transpose_one, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.one_mul]`.

Take `⟨E₁, hE₁⟩ : ∃ E₁, E₁ = (1 : Matrix (Fin d) (Fin d) A).submatrix id f₁` from `⟨_, rfl⟩`. Take `⟨E₂, hE₂⟩ : ∃ E₂, E₂ = (1 : Matrix (Fin d) (Fin d) A).submatrix id f₂` from `⟨_, rfl⟩`. Establish `p11 : E₁ᵀ * E₁ = 1` using `by rw [hE₁, key, Matrix.submatrix_one _ i₁]`. Establish `p22 : E₂ᵀ * E₂ = 1` using `by rw [hE₂, key, Matrix.submatrix_one _ i₂]`. Establish `p12 : E₁ᵀ * E₂ = 0`.

Rewrite using `[hE₁, hE₂, key]`. Conclude with `Matrix.ext fun a b => Matrix.one_apply_ne (dj a b)`. Establish `p21 : E₂ᵀ * E₁ = 0`. Rewrite using `[hE₁, hE₂, key]`. Conclude with `Matrix.ext fun a b => Matrix.one_apply_ne (dj b a).symm`.

Establish `intE : ∀ f : Fin n → Fin d, ∀ i j, ((1 : Matrix (Fin d) (Fin d) A).submatrix id f) i j ∈ S` using `fun f i j => by`. Simplify using `only [Matrix.submatrix_apply, id, Matrix.one_apply]`. Use `split_ifs`. Use `exacts [one_mem _, zero_mem _]`. Establish `mapE : ∀ f : Fin n → Fin d, ((1 : Matrix (Fin d) (Fin d) A).submatrix id f).map s = (1 : Matrix (Fin d) (Fin d) A).submatrix id f` using `fun f => Matrix.ext fun i j => by`.

Simplify using `only [Matrix.map_apply, Matrix.submatrix_apply, id, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hΓG : Γ * G' = 1` using `mul_eq_one_comm.1 hi`. Take `⟨T, hT⟩ : ∃ T, T = (G'.map s)ᵀ` from `⟨_, rfl⟩`. Take `⟨Q, hQ⟩ : ∃ Q, Q = (Γ.map s)ᵀ` from `⟨_, rfl⟩`.

Establish `hTQ : T * Q = 1`. Rewrite using `[hT, hQ, ← Matrix.transpose_mul, ← Matrix.map_mul, hΓG, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]`. Establish `hTΓ : T * Γ = -1`. Rewrite using `[← neg_neg (T * Γ), ← Matrix.mul_neg, ← hsk, ← hQ, hTQ]`. Establish `mapT : T.map s = G'ᵀ` using `Matrix.ext fun i j => by simp [hT, ss]`.

Establish `he2 : e * e = e`. Establish `: e * (e + s e) = e` using `by rw [h1, mul_one]`. Rewrite `this` using `[mul_add, h2, add_zero]`. Then use the resulting hypothesis. Establish `hs2 : s e * s e = s e`. Establish `: s e * (e + s e) = s e` using `by rw [h1, mul_one]`.

Rewrite `this` using `[mul_add, mul_comm, h2, zero_add]`. Then use the resulting hypothesis. Establish `h2' : s e * e = 0` using `by rw [mul_comm, h2]`. Establish `hsS : s e ∈ S` using `hS _ he`. Establish `iE₁ : ∀ i j, E₁ i j ∈ S` using `fun i j => hE₁ ▸ intE f₁ i j`. Establish `iE₂ : ∀ i j, E₂ i j ∈ S` using `fun i j => hE₂ ▸ intE f₂ i j`.

Establish `iT : ∀ i j, T i j ∈ S` using `fun i j => by rw [hT]; exact hS _ (hG' j i)`. Establish `iQ : ∀ i j, Q i j ∈ S` using `fun i j => by rw [hQ]; exact hS _ (hΓ j i)`. Use `⟨e • E₁ᵀ + s e • (E₂ᵀ * T), e • E₁ + s e • (Q * E₂), fun i j => ?_, fun i j => ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]`. Conclude with `add_mem (mul_mem he (iE₁ j i)) (mul_mem hsS (by rw [Matrix.mul_apply]; exact sum_mem fun k _ => mul_mem (iE₂ k i) (iT k j)))`.

Rewrite using `[Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]`. Conclude with `add_mem (mul_mem he (iE₁ i j)) (mul_mem hsS (by rw [Matrix.mul_apply]; exact sum_mem fun k _ => mul_mem (iQ i k) (iE₂ k j)))`. Establish `x1 : (e • E₁ᵀ + s e • (E₂ᵀ * T)) * (e • E₁ + s e • (Q * E₂)) = (e * e) • (E₁ᵀ * E₁) + (s e * e) • (E₁ᵀ * (Q * E₂)) + (e * s e) • (E₂ᵀ * T * E₁) + (s e * s e) • (E₂ᵀ * T * (Q * E₂))`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]`. Normalize the expressions using the abelian group laws.

Establish `x2 : E₂ᵀ * T * (Q * E₂) = 1`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc T, hTQ, Matrix.one_mul, p22]`. Rewrite using `[x1, he2, hs2, h2, h2', p11, x2, zero_smul, zero_smul, add_zero, add_zero, ← add_smul, h1, one_smul]`. Establish `mapE₁ : E₁ᵀ.map s = E₁ᵀ` using `by rw [Matrix.transpose_map, hE₁, mapE]`. Establish `mapE₂ : E₂ᵀ.map s = E₂ᵀ` using `by rw [Matrix.transpose_map, hE₂, mapE]`.

Establish `e3 : (E₂ᵀ * T).map s = E₂ᵀ * G'ᵀ` using `by rw [Matrix.map_mul, mapT, mapE₂]`. Establish `hcm : (e • E₁ᵀ + s e • (E₂ᵀ * T)).map s = s e • E₁ᵀ + e • (E₂ᵀ * G'ᵀ)` using `Matrix.ext fun i j => by`. Establish `a1` using `congrFun (congrFun mapE₁ i) j`. Establish `a2` using `congrFun (congrFun e3 i) j`. Simplify using `only [Matrix.map_apply] at a1 a2`.

Simplify using `only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, ss, a1, a2]`. Rewrite using `[hcm, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose]`. Establish `x1 : (e • E₁ᵀ + s e • (E₂ᵀ * T)) * Γ * (s e • E₁ + e • (G' * E₂)) = (s e * e) • (E₁ᵀ * Γ * E₁) + (e * e) • (E₁ᵀ * Γ * (G' * E₂)) + (s e * s e) • (E₂ᵀ * T * Γ * E₁) + (e * s e) • (E₂ᵀ * T * Γ * (G' * E₂))`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]`. Normalize the expressions using the abelian group laws.

Establish `x2 : E₁ᵀ * Γ * (G' * E₂) = 0`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc Γ, hΓG, Matrix.one_mul, p12]`. Establish `x3 : E₂ᵀ * T * Γ * E₁ = 0`. Rewrite using `[Matrix.mul_assoc E₂ᵀ, hTΓ, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, p21, neg_zero]`. Rewrite using `[x1, x2, x3, h2, h2', zero_smul, zero_smul, smul_zero, smul_zero, add_zero, add_zero, add_zero]`.
-/
private theorem core_pk {A : Type} [CommRing A] (S : Subring A) (s : A →+* A) (hS : ∀ x ∈ S, s x ∈ S)
    (ss : ∀ x, s (s x) = x) {e : A} (he : e ∈ S) (h1 : e + s e = 1) (h2 : e * s e = 0) {n d : ℕ} (hnd : 2 * n ≤ d)
    {Γ G' : Matrix (Fin d) (Fin d) A} (hΓ : ∀ i j, Γ i j ∈ S) (hG' : ∀ i j, G' i j ∈ S) (hi : G' * Γ = 1)
    (hsk : (Γ.map s)ᵀ = -Γ) :
    ∃ (c : Matrix (Fin n) (Fin d) A) (ρ : Matrix (Fin d) (Fin n) A), (∀ i j, c i j ∈ S) ∧ (∀ i j, ρ i j ∈ S) ∧
      c * ρ = 1 ∧ c * Γ * (c.map s)ᵀ = 0 := by
  classical
  let f₁ : Fin n → Fin d := fun i => ⟨i, by omega⟩
  let f₂ : Fin n → Fin d := fun i => ⟨i + n, by omega⟩
  have i₁ : Function.Injective f₁ := fun a b h => Fin.ext (by simpa [f₁] using h)
  have i₂ : Function.Injective f₂ := fun a b h => Fin.ext (by simpa [f₂] using h)
  have dj : ∀ a b, f₁ a ≠ f₂ b := fun a b h => by
    have := congrArg Fin.val h
    simp only [f₁, f₂] at this
    omega
  have key : ∀ f g : Fin n → Fin d, ((1 : Matrix (Fin d) (Fin d) A).submatrix id f)ᵀ * (1 : Matrix (Fin d) (Fin d) A).submatrix id g =
      (1 : Matrix (Fin d) (Fin d) A).submatrix f g := fun f g => by
    rw [Matrix.transpose_submatrix, Matrix.transpose_one, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.one_mul]
  obtain ⟨E₁, hE₁⟩ : ∃ E₁, E₁ = (1 : Matrix (Fin d) (Fin d) A).submatrix id f₁ := ⟨_, rfl⟩
  obtain ⟨E₂, hE₂⟩ : ∃ E₂, E₂ = (1 : Matrix (Fin d) (Fin d) A).submatrix id f₂ := ⟨_, rfl⟩
  have p11 : E₁ᵀ * E₁ = 1 := by rw [hE₁, key, Matrix.submatrix_one _ i₁]
  have p22 : E₂ᵀ * E₂ = 1 := by rw [hE₂, key, Matrix.submatrix_one _ i₂]
  have p12 : E₁ᵀ * E₂ = 0 := by
    rw [hE₁, hE₂, key]
    exact Matrix.ext fun a b => Matrix.one_apply_ne (dj a b)
  have p21 : E₂ᵀ * E₁ = 0 := by
    rw [hE₁, hE₂, key]
    exact Matrix.ext fun a b => Matrix.one_apply_ne (dj b a).symm
  have intE : ∀ f : Fin n → Fin d, ∀ i j, ((1 : Matrix (Fin d) (Fin d) A).submatrix id f) i j ∈ S := fun f i j => by
    simp only [Matrix.submatrix_apply, id, Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have mapE : ∀ f : Fin n → Fin d, ((1 : Matrix (Fin d) (Fin d) A).submatrix id f).map s = (1 : Matrix (Fin d) (Fin d) A).submatrix id f :=
    fun f => Matrix.ext fun i j => by
      simp only [Matrix.map_apply, Matrix.submatrix_apply, id, Matrix.one_apply]
      split_ifs <;> simp
  have hΓG : Γ * G' = 1 := mul_eq_one_comm.1 hi
  obtain ⟨T, hT⟩ : ∃ T, T = (G'.map s)ᵀ := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (Γ.map s)ᵀ := ⟨_, rfl⟩
  have hTQ : T * Q = 1 := by
    rw [hT, hQ, ← Matrix.transpose_mul, ← Matrix.map_mul, hΓG, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have hTΓ : T * Γ = -1 := by
    rw [← neg_neg (T * Γ), ← Matrix.mul_neg, ← hsk, ← hQ, hTQ]
  have mapT : T.map s = G'ᵀ := Matrix.ext fun i j => by simp [hT, ss]
  have he2 : e * e = e := by
    have : e * (e + s e) = e := by rw [h1, mul_one]
    rwa [mul_add, h2, add_zero] at this
  have hs2 : s e * s e = s e := by
    have : s e * (e + s e) = s e := by rw [h1, mul_one]
    rwa [mul_add, mul_comm, h2, zero_add] at this
  have h2' : s e * e = 0 := by rw [mul_comm, h2]
  have hsS : s e ∈ S := hS _ he
  have iE₁ : ∀ i j, E₁ i j ∈ S := fun i j => hE₁ ▸ intE f₁ i j
  have iE₂ : ∀ i j, E₂ i j ∈ S := fun i j => hE₂ ▸ intE f₂ i j
  have iT : ∀ i j, T i j ∈ S := fun i j => by rw [hT]; exact hS _ (hG' j i)
  have iQ : ∀ i j, Q i j ∈ S := fun i j => by rw [hQ]; exact hS _ (hΓ j i)
  refine ⟨e • E₁ᵀ + s e • (E₂ᵀ * T), e • E₁ + s e • (Q * E₂), fun i j => ?_, fun i j => ?_, ?_, ?_⟩
  · rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem he (iE₁ j i)) (mul_mem hsS (by rw [Matrix.mul_apply]; exact sum_mem fun k _ => mul_mem (iE₂ k i) (iT k j)))
  · rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem he (iE₁ i j)) (mul_mem hsS (by rw [Matrix.mul_apply]; exact sum_mem fun k _ => mul_mem (iQ i k) (iE₂ k j)))
  · have x1 : (e • E₁ᵀ + s e • (E₂ᵀ * T)) * (e • E₁ + s e • (Q * E₂)) = (e * e) • (E₁ᵀ * E₁) + (s e * e) • (E₁ᵀ * (Q * E₂)) +
        (e * s e) • (E₂ᵀ * T * E₁) + (s e * s e) • (E₂ᵀ * T * (Q * E₂)) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
      abel
    have x2 : E₂ᵀ * T * (Q * E₂) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc T, hTQ, Matrix.one_mul, p22]
    rw [x1, he2, hs2, h2, h2', p11, x2, zero_smul, zero_smul, add_zero, add_zero, ← add_smul, h1, one_smul]
  · have mapE₁ : E₁ᵀ.map s = E₁ᵀ := by rw [Matrix.transpose_map, hE₁, mapE]
    have mapE₂ : E₂ᵀ.map s = E₂ᵀ := by rw [Matrix.transpose_map, hE₂, mapE]
    have e3 : (E₂ᵀ * T).map s = E₂ᵀ * G'ᵀ := by rw [Matrix.map_mul, mapT, mapE₂]
    have hcm : (e • E₁ᵀ + s e • (E₂ᵀ * T)).map s = s e • E₁ᵀ + e • (E₂ᵀ * G'ᵀ) := Matrix.ext fun i j => by
      have a1 := congrFun (congrFun mapE₁ i) j
      have a2 := congrFun (congrFun e3 i) j
      simp only [Matrix.map_apply] at a1 a2
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, ss, a1, a2]
    rw [hcm, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_transpose]
    have x1 : (e • E₁ᵀ + s e • (E₂ᵀ * T)) * Γ * (s e • E₁ + e • (G' * E₂)) = (s e * e) • (E₁ᵀ * Γ * E₁) + (e * e) • (E₁ᵀ * Γ * (G' * E₂)) +
        (s e * s e) • (E₂ᵀ * T * Γ * E₁) + (e * s e) • (E₂ᵀ * T * Γ * (G' * E₂)) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
      abel
    have x2 : E₁ᵀ * Γ * (G' * E₂) = 0 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Γ, hΓG, Matrix.one_mul, p12]
    have x3 : E₂ᵀ * T * Γ * E₁ = 0 := by
      rw [Matrix.mul_assoc E₂ᵀ, hTΓ, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, p21, neg_zero]
    rw [x1, x2, x3, h2, h2', zero_smul, zero_smul, smul_zero, smul_zero, add_zero, add_zero, add_zero]
section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul a x => exact congrArg (a ⊗ₜ[F] ·) (h x)`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
private theorem sig_sig_pk (h : ∀ x, σ (σ x) = x) (y : Fv F v ⊗[F] E) : sigR (Fv F v) σ (sigR (Fv F v) σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (h x)
  | add x y hx hy => simp only [map_add, hx, hy]
/- English proof (translation)
The claim follows from `Matrix.ext fun i j => sub_eq_zero.1 (PositivityTheory.ThKH.Iwas.eq_zero_of_at (v := v) (fun u hu => congrFun (congrFun (PositivityTheory.ThKH.Iwas.at_sub h h' u hu) i) j) (by rw [map_sub, sub_eq_zero]; exact congrFun (congrFun e i) j))`.
-/
private theorem ext_at_pk {ι κ : Type} {M M' : Matrix ι κ (AE F E)} (h : At (evFin F v) M) (h' : At (evFin F v) M')
    (e : M.map (compFin F E v) = M'.map (compFin F E v)) : M = M' :=
  Matrix.ext fun i j => sub_eq_zero.1 (PositivityTheory.ThKH.Iwas.eq_zero_of_at (v := v)
    (fun u hu => congrFun (congrFun (PositivityTheory.ThKH.Iwas.at_sub h h' u hu) i) j)
    (by rw [map_sub, sub_eq_zero]; exact congrFun (congrFun e i) j))
/- English proof (translation)
Use `intLoc_induction (p := fun y => PositivityTheory.ThKH.Iwas.sgE E v y ∈ Oh E v) (fun a ha x => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) hy` and prove the remaining obligations. Use `AddSubgroup.subset_closure ⟨PositivityTheory.ThKH.Iwas.sg v a, PositivityTheory.ThKH.Iwas.at_sg a, by rwa [PositivityTheory.ThKH.Iwas.ev_sg], x, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(PositivityTheory.ThKH.Iwas.sg v a) ⊗ₜ[F] (x : E) = (PositivityTheory.ThKH.Iwas.sg v a * 1) ⊗ₜ[F] (x : E)`. Rewrite using `[mul_one]`. Rewrite using `[map_zero]`.

Conclude with `zero_mem _`. Rewrite using `[map_add]`. Conclude with `add_mem hy hz`. Rewrite using `[map_neg]`. Conclude with `neg_mem hy`.
-/
private theorem sgE_mem_Oh_pk {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) : PositivityTheory.ThKH.Iwas.sgE E v y ∈ Oh E v := by
  refine intLoc_induction (p := fun y => PositivityTheory.ThKH.Iwas.sgE E v y ∈ Oh E v) (fun a ha x => ?_) ?_ (fun y z hy hz => ?_)
    (fun y hy => ?_) hy
  · refine AddSubgroup.subset_closure ⟨PositivityTheory.ThKH.Iwas.sg v a, PositivityTheory.ThKH.Iwas.at_sg a, by rwa [PositivityTheory.ThKH.Iwas.ev_sg], x, ?_⟩
    change (PositivityTheory.ThKH.Iwas.sg v a) ⊗ₜ[F] (x : E) = (PositivityTheory.ThKH.Iwas.sg v a * 1) ⊗ₜ[F] (x : E)
    rw [mul_one]
  · rw [map_zero]; exact zero_mem _
  · rw [map_add]; exact add_mem hy hz
  · rw [map_neg]; exact neg_mem hy
/- English proof (translation)
Establish `h1` using `hx (1 - PositivityTheory.ThKH.Iwas.sg v 1) (by rw [map_sub, map_one, PositivityTheory.ThKH.Iwas.ev_sg, sub_self])`. Rewrite `h1` using `[sub_smul, one_smul, ← PositivityTheory.ThKH.Iwas.sgE_comp, sub_eq_zero]`. Rewrite using `[h1]`. Conclude with `sgE_mem_Oh_pk h`.
-/
private theorem mem_Oh_pk {x : AE F E} (hx : At (evFin F v) x) (h : compFin F E v x ∈ intLoc F E v) : x ∈ Oh E v := by
  have h1 := hx (1 - PositivityTheory.ThKH.Iwas.sg v 1) (by rw [map_sub, map_one, PositivityTheory.ThKH.Iwas.ev_sg, sub_self])
  rw [sub_smul, one_smul, ← PositivityTheory.ThKH.Iwas.sgE_comp, sub_eq_zero] at h1
  rw [h1]
  exact sgE_mem_Oh_pk h
/- English proof (translation)
Introduce `u hu` and use `Matrix.ext fun i j => PositivityTheory.ThKH.Iwas.at_sgE _ u hu`.
-/
private theorem at_sgEM_pk {ι κ : Type} (M : Matrix ι κ (Fv F v ⊗[F] E)) : At (evFin F v) (M.map (PositivityTheory.ThKH.Iwas.sgE E v)) :=
  fun u hu => Matrix.ext fun i j => PositivityTheory.ThKH.Iwas.at_sgE _ u hu
/- English proof (translation)
The claim follows from `Matrix.ext fun i j => PositivityTheory.ThKH.Iwas.comp_sgE _`.
-/
private theorem comp_sgEM_pk {ι κ : Type} (M : Matrix ι κ (Fv F v ⊗[F] E)) :
    (M.map (PositivityTheory.ThKH.Iwas.sgE E v)).map (compFin F E v) = M :=
  Matrix.ext fun i j => PositivityTheory.ThKH.Iwas.comp_sgE _
end
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d W r s hB hW hnd v t`. Establish `hc` using `hB.cm`. Establish `hσ` using `cm_conj_conj hc`. Take `⟨a, g, l, ha, hal, hΓ, G', hG', hi⟩` from `_root_.GlobalTheory.ThK.Dbl.Frame.exists_loc_k hB (Or.inr hW) (PositivityTheory.ThKH.Iwas.det_ne_zero hW) v`. Set `ι` to `inclR (F := F) (E := E) (Fv F v)`.

Set `c'` to `sigR (Fv F v) σ`. Establish `mJ : ((W.J.map ι).map c')ᵀ = -W.J.map ι` using `Matrix.ext fun i j => by`. Express the relevant statement in the definitionally equal form `c' (ι (W.J j i)) = -ι (W.J i j)`. Rewrite using `[show c' (ι (W.J j i)) = ι (σ (W.J j i)) from rfl, hW.skew i j, map_neg]`. Establish `mg : (g.1.map c').map c' = g.1` using `Matrix.ext fun i j => sig_sig_pk hσ _`.

Establish `sk : ((g.1ᵀ * W.J.map ι * g.1.map c').map c')ᵀ = -(g.1ᵀ * W.J.map ι * g.1.map c')`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, mg, mJ, Matrix.transpose_map, Matrix.transpose_transpose, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]`. Establish `idem` using `splitIdem_mul_self hc t`. Establish `sI` using `sigR_splitIdem hc t`. Take `⟨c, ρ, ic, iρ, hcρ, hgr⟩` from `core_pk (intLoc F E v) c' (fun x hx => sigR_mem_intLoc σ hx) (sig_sig_pk hσ) (splitIdem_mem hc t) (by change _ + sigR _ σ _ = 1; rw [sI]; ring) (by change _ * sigR _ σ _ = 0; rw [sI, mul_sub, mul_one, idem, sub_self]) hnd hΓ hG' hi sk`.

Take `⟨Y₀, hY₀⟩ : ∃ Y₀, Y₀ = c * a.1ᵀ` from `⟨_, rfl⟩`. Take `⟨R₀, hR₀⟩ : ∃ R₀, R₀ = (a⁻¹).1ᵀ * ρ` from `⟨_, rfl⟩`. Use `⟨Y₀.map (PositivityTheory.ThKH.Iwas.sgE E v), R₀.map (PositivityTheory.ThKH.Iwas.sgE E v), ⟨fun i => ?_, ?_, ?_, fun z hz j => ?_⟩⟩` and prove the remaining obligations. Use `(PositivityTheory.ThKG.Loc.Cone.Vf.mem_latW_loc W _).2 ⟨fun u hu => funext fun j => PositivityTheory.ThKH.Iwas.at_sgE _ u hu, ?_⟩` and prove the remaining obligations. Establish `h1` using `(ha (c i)).1 (ic i)`.

Use `h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Express the relevant statement in the definitionally equal form `compFin F E v (PositivityTheory.ThKH.Iwas.sgE E v (Y₀ i j)) = _`. Rewrite using `[PositivityTheory.ThKH.Iwas.comp_sgE, hY₀]`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, mul_comm]`.

Establish `atE : At (evFin F v) (eM v n : Matrix (Fin n) (Fin n) (AE F E))` using `fun u hu => by`. Rewrite using `[smul_smul, show u * PositivityTheory.ThKH.Iwas.sg v 1 = 0 from PositivityTheory.ThKH.Iwas.at_sg 1 u hu, zero_smul]`. Use `ext_at_pk (PositivityTheory.ThKH.Iwas.at_mul_left (at_sgEM_pk _) _) atE ?_` and prove the remaining obligations. Establish `e1 : (eM v n : Matrix (Fin n) (Fin n) (AE F E)).map (compFin F E v) = 1` using `Matrix.ext fun i j => by`. Express the relevant statement in the definitionally equal form `compFin F E v (PositivityTheory.ThKH.Iwas.sg v 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) = _`.

Rewrite using `[← PositivityTheory.ThKH.Iwas.sgE_comp, PositivityTheory.ThKH.Iwas.comp_sgE, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[Matrix.map_mul, comp_sgEM_pk, comp_sgEM_pk, e1, hY₀, hR₀, Matrix.mul_assoc, ← Matrix.mul_assoc a.1ᵀ, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.one_mul, hcρ]`. Use `ext_at_pk (PositivityTheory.ThKH.Iwas.at_mul_left (PositivityTheory.ThKH.Iwas.at_mul_left (at_sgEM_pk _) _) _) PositivityTheory.ThKH.Iwas.at_zero ?_` and prove the remaining obligations. Establish `e1 : (incM F W.J).map (compFin F E v) = W.J.map ι` using `Matrix.ext fun i k => congrArg (· ⊗ₜ[F] W.J i k) (map_one (evFin F v))`.

Establish `e2 : (((Y₀.map (PositivityTheory.ThKH.Iwas.sgE E v)).map (cA σ))ᵀ).map (compFin F E v) = (Y₀.map c')ᵀ` using `Matrix.ext fun i j => by`. Express the relevant statement in the definitionally equal form `compFin F E v (cA σ (PositivityTheory.ThKH.Iwas.sgE E v (Y₀ j i))) = c' (Y₀ j i)`. Rewrite using `[GlobalTheory.ThK.Dbl.Vf2.comp_cA, PositivityTheory.ThKH.Iwas.comp_sgE]`. Establish `e3 : a.1.map c' = c' l.1 • g.1.map c'` using `Matrix.ext fun i j => by`. Express the relevant statement in the definitionally equal form `c' (a.1 i j) = c' l.1 * c' (g.1 i j)`.

Rewrite using `[hal, Matrix.smul_apply, smul_eq_mul, map_mul]`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, comp_sgEM_pk, e1, e2, hY₀, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose, e3, hal]`. Establish `e4 : c * (l.1 • g.1)ᵀ * W.J.map ι * ((c' l.1 • g.1.map c') * (c.map c')ᵀ) = (l.1 * c' l.1) • (c * (g.1ᵀ * W.J.map ι * g.1.map c') * (c.map c')ᵀ)`. Simplify using `only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]`. Rewrite using `[mul_comm]`.

Rewrite using `[e4, hgr, smul_zero, Matrix.map_zero _ (map_zero _)]`. Take `⟨z1, z2⟩` from `(PositivityTheory.ThKG.Loc.Cone.Vf.mem_latW_loc W z).1 hz`. Establish `eT : z ᵥ* R₀.map (PositivityTheory.ThKH.Iwas.sgE E v) = (R₀.map (PositivityTheory.ThKH.Iwas.sgE E v))ᵀ *ᵥ z` using `(Matrix.mulVec_transpose _ _).symm`. Establish `hat : At (evFin F v) (z ᵥ* R₀.map (PositivityTheory.ThKH.Iwas.sgE E v))`. Rewrite using `[eT]`.

Conclude with `PositivityTheory.ThKH.Iwas.at_mulVec_right _ z1`. Use `mem_Oh_pk (fun u hu => congrFun (hat u hu) j) ?_` and prove the remaining obligations. Take `⟨y, hy⟩ : ∃ y, y = (a⁻¹).1 *ᵥ (compFin F E v ∘ z)` from `⟨_, rfl⟩`. Establish `iy` using `(ha y).2 (by rwa [hy, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec])`. Establish `e1 : compFin F E v ((z ᵥ* R₀.map (PositivityTheory.ThKH.Iwas.sgE E v)) j) = (y ᵥ* ρ) j`.

Rewrite using `[eT, RingHom.map_mulVec, Matrix.transpose_map, comp_sgEM_pk, hR₀, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mulVec_mulVec, ← hy, Matrix.mulVec_transpose]`. Rewrite using `[e1]`. Express the relevant statement in the definitionally equal form `∑ k, y k * ρ k j ∈ _`. Conclude with `sum_mem fun k _ => mul_mem (iy k) (iρ k j)`.
-/
theorem UpperTheory.exists_isotropic_splitting_of_two_mul_le :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (W : Spc F E d) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → W.IsSkew σ B r s → 2 * n ≤ d → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), ∃ Y R, IsIsoW σ W v (n := n) Y R := by
  intro F E _ _ _ _ _ σ B n d W r s hB hW hnd v t
  have hc := hB.cm
  have hσ := cm_conj_conj hc
  obtain ⟨a, g, l, ha, hal, hΓ, G', hG', hi⟩ :=
    _root_.GlobalTheory.ThK.Dbl.Frame.exists_loc_k hB (Or.inr hW) (PositivityTheory.ThKH.Iwas.det_ne_zero hW) v
  let ι := inclR (F := F) (E := E) (Fv F v)
  let c' := sigR (Fv F v) σ
  have mJ : ((W.J.map ι).map c')ᵀ = -W.J.map ι := Matrix.ext fun i j => by
    change c' (ι (W.J j i)) = -ι (W.J i j)
    rw [show c' (ι (W.J j i)) = ι (σ (W.J j i)) from rfl, hW.skew i j, map_neg]
  have mg : (g.1.map c').map c' = g.1 := Matrix.ext fun i j => sig_sig_pk hσ _
  have sk : ((g.1ᵀ * W.J.map ι * g.1.map c').map c')ᵀ = -(g.1ᵀ * W.J.map ι * g.1.map c') := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, mg, mJ, Matrix.transpose_map,
      Matrix.transpose_transpose, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  have idem := splitIdem_mul_self hc t
  have sI := sigR_splitIdem hc t
  obtain ⟨c, ρ, ic, iρ, hcρ, hgr⟩ := core_pk (intLoc F E v) c' (fun x hx => sigR_mem_intLoc σ hx) (sig_sig_pk hσ)
    (splitIdem_mem hc t) (by change _ + sigR _ σ _ = 1; rw [sI]; ring)
    (by change _ * sigR _ σ _ = 0; rw [sI, mul_sub, mul_one, idem, sub_self]) hnd hΓ hG' hi sk
  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀, Y₀ = c * a.1ᵀ := ⟨_, rfl⟩
  obtain ⟨R₀, hR₀⟩ : ∃ R₀, R₀ = (a⁻¹).1ᵀ * ρ := ⟨_, rfl⟩
  refine ⟨Y₀.map (PositivityTheory.ThKH.Iwas.sgE E v), R₀.map (PositivityTheory.ThKH.Iwas.sgE E v), ⟨fun i => ?_, ?_, ?_, fun z hz j => ?_⟩⟩
  · refine (PositivityTheory.ThKG.Loc.Cone.Vf.mem_latW_loc W _).2 ⟨fun u hu => funext fun j => PositivityTheory.ThKH.Iwas.at_sgE _ u hu, ?_⟩
    have h1 := (ha (c i)).1 (ic i)
    convert h1 using 1
    funext j
    change compFin F E v (PositivityTheory.ThKH.Iwas.sgE E v (Y₀ i j)) = _
    rw [PositivityTheory.ThKH.Iwas.comp_sgE, hY₀]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, mul_comm]
  · have atE : At (evFin F v) (eM v n : Matrix (Fin n) (Fin n) (AE F E)) := fun u hu => by
      rw [smul_smul, show u * PositivityTheory.ThKH.Iwas.sg v 1 = 0 from PositivityTheory.ThKH.Iwas.at_sg 1 u hu, zero_smul]
    refine ext_at_pk (PositivityTheory.ThKH.Iwas.at_mul_left (at_sgEM_pk _) _) atE ?_
    have e1 : (eM v n : Matrix (Fin n) (Fin n) (AE F E)).map (compFin F E v) = 1 := Matrix.ext fun i j => by
      change compFin F E v (PositivityTheory.ThKH.Iwas.sg v 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) = _
      rw [← PositivityTheory.ThKH.Iwas.sgE_comp, PositivityTheory.ThKH.Iwas.comp_sgE, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [Matrix.map_mul, comp_sgEM_pk, comp_sgEM_pk, e1, hY₀, hR₀, Matrix.mul_assoc, ← Matrix.mul_assoc a.1ᵀ, ← Matrix.transpose_mul,
      Units.inv_mul, Matrix.transpose_one, Matrix.one_mul, hcρ]
  · refine ext_at_pk (PositivityTheory.ThKH.Iwas.at_mul_left (PositivityTheory.ThKH.Iwas.at_mul_left (at_sgEM_pk _) _) _) PositivityTheory.ThKH.Iwas.at_zero ?_
    have e1 : (incM F W.J).map (compFin F E v) = W.J.map ι :=
      Matrix.ext fun i k => congrArg (· ⊗ₜ[F] W.J i k) (map_one (evFin F v))
    have e2 : (((Y₀.map (PositivityTheory.ThKH.Iwas.sgE E v)).map (cA σ))ᵀ).map (compFin F E v) = (Y₀.map c')ᵀ := Matrix.ext fun i j => by
      change compFin F E v (cA σ (PositivityTheory.ThKH.Iwas.sgE E v (Y₀ j i))) = c' (Y₀ j i)
      rw [GlobalTheory.ThK.Dbl.Vf2.comp_cA, PositivityTheory.ThKH.Iwas.comp_sgE]
    have e3 : a.1.map c' = c' l.1 • g.1.map c' := Matrix.ext fun i j => by
      change c' (a.1 i j) = c' l.1 * c' (g.1 i j)
      rw [hal, Matrix.smul_apply, smul_eq_mul, map_mul]
    rw [Matrix.map_mul, Matrix.map_mul, comp_sgEM_pk, e1, e2, hY₀, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_map,
      Matrix.transpose_transpose, e3, hal]
    have e4 : c * (l.1 • g.1)ᵀ * W.J.map ι * ((c' l.1 • g.1.map c') * (c.map c')ᵀ) =
        (l.1 * c' l.1) • (c * (g.1ᵀ * W.J.map ι * g.1.map c') * (c.map c')ᵀ) := by
      simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
      rw [mul_comm]
    rw [e4, hgr, smul_zero, Matrix.map_zero _ (map_zero _)]
  · obtain ⟨z1, z2⟩ := (PositivityTheory.ThKG.Loc.Cone.Vf.mem_latW_loc W z).1 hz
    have eT : z ᵥ* R₀.map (PositivityTheory.ThKH.Iwas.sgE E v) = (R₀.map (PositivityTheory.ThKH.Iwas.sgE E v))ᵀ *ᵥ z := (Matrix.mulVec_transpose _ _).symm
    have hat : At (evFin F v) (z ᵥ* R₀.map (PositivityTheory.ThKH.Iwas.sgE E v)) := by
      rw [eT]; exact PositivityTheory.ThKH.Iwas.at_mulVec_right _ z1
    refine mem_Oh_pk (fun u hu => congrFun (hat u hu) j) ?_
    obtain ⟨y, hy⟩ : ∃ y, y = (a⁻¹).1 *ᵥ (compFin F E v ∘ z) := ⟨_, rfl⟩
    have iy := (ha y).2 (by rwa [hy, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec])
    have e1 : compFin F E v ((z ᵥ* R₀.map (PositivityTheory.ThKH.Iwas.sgE E v)) j) = (y ᵥ* ρ) j := by
      rw [eT, RingHom.map_mulVec, Matrix.transpose_map, comp_sgEM_pk, hR₀, Matrix.transpose_mul, Matrix.transpose_transpose,
        ← Matrix.mulVec_mulVec, ← hy, Matrix.mulVec_transpose]
    rw [e1]
    change ∑ k, y k * ρ k j ∈ _
    exact sum_mem fun k _ => mul_mem (iy k) (iρ k j)
end
end
