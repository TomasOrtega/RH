import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

noncomputable section

open GlobalTheory.SplitPts (conjE)

namespace UpperTheory.Gal.W2.Seed

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n p : ℕ} [Fact p.Prime]

/- English proof (translation)
Rewrite using `[← A.bar_eq]`. Unfold `Arith.dg`. Apply the tactic sequence `split_ifs <;> simp [A.c_real]`.
-/
private theorem conj_dg (A : Arith E) (n : ℕ) (i : Fin n) :
    IsCMField.complexConj E (A.dg n i : E) = (A.dg n i : E) := by
  rw [← A.bar_eq]
  unfold Arith.dg
  split_ifs <;> simp [A.c_real]

private abbrev Dg (A : Arith E) (n : ℕ) : Matrix (Fin n) (Fin n) E := Matrix.diagonal fun i => (A.dg n i : E)

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[Arith.H, Arith.hd]`. Simplify using `[Arith.H, h]`.
-/
private theorem H_eq (A : Arith E) (n : ℕ) : A.H n = (-(A.c : E)) • Dg A n := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Arith.H, Arith.hd]
  · simp [Arith.H, h]

/- English proof (translation)
Rewrite using `[Matrix.diagonal_map (map_zero _)]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `conj_dg A n i`.
-/
private theorem Dg_map (A : Arith E) (n : ℕ) : (Dg A n).map (IsCMField.complexConj E : E →+* E) = Dg A n := by
  rw [Matrix.diagonal_map (map_zero _)]
  congr 1; funext i
  exact conj_dg A n i

/- English proof (translation)
Establish `h` using `A.herm n`. Establish `h2 : (A.H n)ᵀ = A.H n` using `by unfold Arith.H; simp`. Establish `h3` using `congrArg Matrix.transpose h`. Rewrite `h3` using `[Matrix.transpose_transpose, h2]`. Conclude with `h3`.
-/
private theorem H_map (A : Arith E) (n : ℕ) : (A.H n).map (IsCMField.complexConj E : E →+* E) = A.H n := by
  have h := A.herm n
  have h2 : (A.H n)ᵀ = A.H n := by unfold Arith.H; simp
  have h3 := congrArg Matrix.transpose h
  rw [Matrix.transpose_transpose, h2] at h3
  exact h3

/- English proof (translation)
The claim follows from `neg_ne_zero.2 A.c_ne`.
-/
private theorem c_ne' (A : Arith E) : -(A.c : E) ≠ 0 := neg_ne_zero.2 A.c_ne

/- English proof (translation)
Establish `hu : IsUnit (A.H n).det` using `(A.det_ne n).isUnit`. Establish `h1 : A.H n * (hermStar (A.H n) (A.det_ne n) x).unop = (x.map (IsCMField.complexConj E : E →+* E))ᵀ * A.H n`. Rewrite using `[hermStar_apply, H_map]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[Matrix.mul_nonsing_inv_cancel_left _ _ hu]`.

Generalize the expression as in `(hermStar (A.H n) (A.det_ne n) x).unop = Y at h1 ⊢`. Rewrite `h1` using `[H_eq A n, Matrix.smul_mul, Matrix.mul_smul]`. Conclude with `smul_right_injective _ (c_ne' A) h1`.
-/
private theorem Dg_star (A : Arith E) (n : ℕ) (x : Matrix (Fin n) (Fin n) E) :
    Dg A n * (hermStar (A.H n) (A.det_ne n) x).unop = (x.map (IsCMField.complexConj E : E →+* E))ᵀ * Dg A n := by
  have hu : IsUnit (A.H n).det := (A.det_ne n).isUnit
  have h1 : A.H n * (hermStar (A.H n) (A.det_ne n) x).unop = (x.map (IsCMField.complexConj E : E →+* E))ᵀ * A.H n := by
    rw [hermStar_apply, H_map]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  generalize (hermStar (A.H n) (A.det_ne n) x).unop = Y at h1 ⊢
  rw [H_eq A n, Matrix.smul_mul, Matrix.mul_smul] at h1
  exact smul_right_injective _ (c_ne' A) h1

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem baseMatrix_eq_diagonal (A : Arith E) (n : ℕ) : ((A.β₀ n : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E) = Dg A n := rfl

/- English proof (translation)
Apply `(Units.mul_right_inj (A.β₀ n)).1` to reduce the goal to its premises. Rewrite using `[baseMatrix_eq_diagonal, Dg_star, Dg_map]`. Simplify using the standard rewrite rules.
-/
private theorem hermStar_baseMatrix (A : Arith E) (n : ℕ) :
    (hermStar (A.H n) (A.det_ne n) ((A.β₀ n : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E)).unop = A.β₀ n := by
  apply (Units.mul_right_inj (A.β₀ n)).1
  rw [baseMatrix_eq_diagonal, Dg_star, Dg_map]
  simp

/- English proof (translation)
Establish `hs : algebraMap ℚ E (s : ℚ) ≠ 0` using `(map_ne_zero _).2 s.ne_zero`. Use `(mul_eq_smul_one_comm hs).1 ?_` and prove the remaining obligations. Rewrite `h` using `[Matrix.mul_assoc, baseMatrix_eq_diagonal, Dg_star, ← Matrix.mul_assoc, ← baseMatrix_eq_diagonal]`. Establish `h2` using `(Units.mul_left_inj (A.β₀ n)).1 h`. Rewrite using `[h2]`.

Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[Matrix.algebraMap_matrix_apply]`. Simplify using `[Matrix.algebraMap_matrix_apply, hij]`.
-/
private theorem sim_of (A : Arith E) (n : ℕ) (y : (Matrix (Fin n) (Fin n) E)ˣ) (s : ℚˣ)
    (h : (y : Matrix (Fin n) (Fin n) E) * (A.β₀ n : (Matrix (Fin n) (Fin n) E)ˣ) *
      (hermStar (A.H n) (A.det_ne n) y).unop = algebraMap ℚ (Matrix (Fin n) (Fin n) E) s * (A.β₀ n : (Matrix (Fin n) (Fin n) E)ˣ)) :
    ((y : Matrix (Fin n) (Fin n) E).map (IsCMField.complexConj E : E →+* E))ᵀ * (y : Matrix (Fin n) (Fin n) E) =
      algebraMap ℚ E s • (1 : Matrix (Fin n) (Fin n) E) := by
  have hs : algebraMap ℚ E (s : ℚ) ≠ 0 := (map_ne_zero _).2 s.ne_zero
  refine (mul_eq_smul_one_comm hs).1 ?_
  rw [Matrix.mul_assoc, baseMatrix_eq_diagonal, Dg_star, ← Matrix.mul_assoc, ← baseMatrix_eq_diagonal] at h
  have h2 := (Units.mul_left_inj (A.β₀ n)).1 h
  rw [h2]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Matrix.algebraMap_matrix_apply]
  · simp [Matrix.algebraMap_matrix_apply, hij]

/- English proof (translation)
Establish `e1 : gramAt (A.H n) τ = (-τ (A.c : E)) • (Dg A n).map τ`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[gramAt, Arith.H, Arith.hd]`.

Simplify using `[gramAt, Arith.H, h, Ne.symm h]`. Establish `e2 : (Dg A n).map τ * b.map τ = 1`. Rewrite using `[← Matrix.map_mul, hb, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[e1, Matrix.smul_mul, e2]`.
-/
private theorem gram_psi (A : Arith E) (n : ℕ) (τ : E →+* ℂ) (b : Matrix (Fin n) (Fin n) E) (hb : Dg A n * b = 1) :
    gramAt (A.H n) τ * b.map τ = (-τ (A.c : E)) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have e1 : gramAt (A.H n) τ = (-τ (A.c : E)) • (Dg A n).map τ := by
    ext i j
    by_cases h : i = j
    · subst h; simp [gramAt, Arith.H, Arith.hd]
    · simp [gramAt, Arith.H, h, Ne.symm h]
  have e2 : (Dg A n).map τ * b.map τ = 1 := by
    rw [← Matrix.map_mul, hb, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [e1, Matrix.smul_mul, e2]

/- English proof (translation)
Establish `h1 : τ (IsCMField.complexConj E (A.c : E)) = (starRingEnd ℂ) (τ (A.c : E))` using `IsCMField.complexEmbedding_complexConj E τ _`. Rewrite `h1` using `[← A.bar_eq, A.c_real]`. Conclude with `Complex.conj_eq_iff_im.1 h1.symm`.
-/
private theorem c_im (A : Arith E) (τ : E →+* ℂ) : (τ (A.c : E)).im = 0 := by
  have h1 : τ (IsCMField.complexConj E (A.c : E)) = (starRingEnd ℂ) (τ (A.c : E)) :=
    IsCMField.complexEmbedding_complexConj E τ _
  rw [← A.bar_eq, A.c_real] at h1
  exact Complex.conj_eq_iff_im.1 h1.symm

/- English proof (translation)
Use `open scoped ComplexOrder in`. Establish `h` using `Matrix.dotProduct_star_self_pos_iff.2 hx`. Use `⟨(star x ⬝ᵥ x).re, (Complex.pos_iff.1 h).1, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re, hr, zero_mul, sub_zero]`.
-/
private theorem form_val (r : ℂ) (hr : r.im = 0) (x : Fin n → ℂ) (hx : x ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ (star x ⬝ᵥ ((r • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ x)).re = r.re * t := by
  open scoped ComplexOrder in
  have h := Matrix.dotProduct_star_self_pos_iff.2 hx
  refine ⟨(star x ⬝ᵥ x).re, (Complex.pos_iff.1 h).1, ?_⟩
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re, hr, zero_mul, sub_zero]

/- English proof (translation)
Break down `InfinitePlace.mk_eq_iff.1 h with h | h` into its components or cases. Rewrite using `[h]`. Conclude with `A.c_neg`. Use `A.c_neg` as an intermediate fact. Rewrite `this` using `[← h]`.

Simplify `this` using `[ComplexEmbedding.conjugate_coe_eq]`.
-/
private theorem c_neg_of (A : Arith E) (τ : E →+* ℂ) (h : InfinitePlace.mk τ = InfinitePlace.mk A.τ₀) :
    (τ (A.c : E)).re < 0 := by
  rcases InfinitePlace.mk_eq_iff.1 h with h | h
  · rw [h]; exact A.c_neg
  · have := A.c_neg
    rw [← h] at this
    simpa [ComplexEmbedding.conjugate_coe_eq] using this

/- English proof (translation)
Rewrite using `[gram_psi A n _ b hb]`. Take `⟨t, ht, he⟩` from `form_val (-v.embedding (A.c : E)) (by simp [c_im]) x hx`. Rewrite using `[he]`. Establish `hm : InfinitePlace.mk v.embedding = v` using `InfinitePlace.mk_embedding v`. Prove the components needed by the constructor for the conclusion.

Introduce `h1`. Establish `hv : InfinitePlace.mk v.embedding = InfinitePlace.mk A.τ₀`. Assume the negation of the conclusion as `hne`. Use `((hs v.embedding).2 hne).1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `c_neg_of A _ hv` as an intermediate fact. Simplify using `only [Complex.neg_re]`. Use the polynomial consequences of the given equalities and inequalities. Introduce `h1`. Establish `hv : InfinitePlace.mk v.embedding ≠ InfinitePlace.mk A.τ₀` using `fun h => h1 ((hs v.embedding).1 h).1`.

Use `A.c_pos _ hv` as an intermediate fact. Simplify using `only [Complex.neg_re]`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem book_constants_pos_of_pos (A : Arith E) (n : ℕ) (hs : A.SigOK n) (v : InfinitePlace E) (b : Matrix (Fin n) (Fin n) E)
    (hb : Dg A n * b = 1) (x : Fin n → ℂ) (hx : x ≠ 0) :
    (sigPos (A.herm n) v.embedding = 1 → 0 < (star x ⬝ᵥ ((gramAt (A.H n) v.embedding * b.map v.embedding) *ᵥ x)).re) ∧
    (sigPos (A.herm n) v.embedding ≠ 1 → (star x ⬝ᵥ ((gramAt (A.H n) v.embedding * b.map v.embedding) *ᵥ x)).re < 0) := by
  rw [gram_psi A n _ b hb]
  obtain ⟨t, ht, he⟩ := form_val (-v.embedding (A.c : E)) (by simp [c_im]) x hx
  rw [he]
  have hm : InfinitePlace.mk v.embedding = v := InfinitePlace.mk_embedding v
  constructor
  · intro h1
    have hv : InfinitePlace.mk v.embedding = InfinitePlace.mk A.τ₀ := by
      by_contra hne
      have := ((hs v.embedding).2 hne).1
      omega
    have := c_neg_of A _ hv
    simp only [Complex.neg_re]
    nlinarith
  · intro h1
    have hv : InfinitePlace.mk v.embedding ≠ InfinitePlace.mk A.τ₀ := fun h => h1 ((hs v.embedding).1 h).1
    have := A.c_pos _ hv
    simp only [Complex.neg_re]
    nlinarith

variable {A : Arith E}

/- English proof (translation)
Establish `h` using `congrArg (fun M : Matrix (Fin n) (Fin n) (Af E) => M.map T.Φ) T.iso.1`. Simplify using `only [Matrix.map_mul] at h`. Rewrite `h` using `[Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `e1 : ((T.a.val.map (conjFin (conjE E)))ᵀ).map T.Φ = ((T.a.val.map T.Φ).map (conjT E (AfP p)))ᵀ`. Use extensionality with `i j`.

Conclude with `T.Φ_conj _`. Establish `e2 : (Matrix.diagonal (fun i => algebraMap E (Af E) (A.dg n i : E))).map T.Φ = Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] (A.dg n i : E))`. Rewrite using `[Matrix.diagonal_map (map_zero _)]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Conclude with `T.Φ_E _`. Rewrite `h` using `[e1, e2]`. Conclude with `h`.
-/
private theorem iso_map {S : Setup A n p} (T : Tr S) :
    ((T.a.val.map T.Φ).map (conjT E (AfP p)))ᵀ * Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] (A.dg n i : E)) * T.a.val.map T.Φ = 1 := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) (Af E) => M.map T.Φ) T.iso.1
  simp only [Matrix.map_mul] at h
  rw [Matrix.map_one _ (map_zero _) (map_one _)] at h
  have e1 : ((T.a.val.map (conjFin (conjE E)))ᵀ).map T.Φ = ((T.a.val.map T.Φ).map (conjT E (AfP p)))ᵀ := by
    ext i j
    exact T.Φ_conj _
  have e2 : (Matrix.diagonal (fun i => algebraMap E (Af E) (A.dg n i : E))).map T.Φ =
      Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] (A.dg n i : E)) := by
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1; funext i
    exact T.Φ_E _
  rw [e1, e2] at h
  exact h

private def xU {S : Setup A n p} (T : Tr S) : (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ :=
  Units.map (T.μ.symm : Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E) →* AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)
    (GeneralLinearGroup.map T.Φ T.a)

/- English proof (translation)
Use `show T.μ (T.μ.symm _) = _`. Rewrite using `[RingEquiv.apply_symm_apply]`. Both sides reduce to the same expression.
-/
private theorem traceMap_unipotent {S : Setup A n p} (T : Tr S) : T.μ (xU T) = T.a.val.map T.Φ := by
  show T.μ (T.μ.symm _) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

/- English proof (translation)
Use `show T.μ (T.μ.symm _) = _`. Rewrite using `[RingEquiv.apply_symm_apply]`. Both sides reduce to the same expression.
-/
private theorem mu_xi {S : Setup A n p} (T : Tr S) : T.μ ((xU T)⁻¹ : (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ) = (T.a⁻¹).val.map T.Φ := by
  show T.μ (T.μ.symm _) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

/- English proof (translation)
Use extensionality with `i k`. Conclude with `T.mu 1 y i k`.
-/
private theorem mu_b {S : Setup A n p} (T : Tr S) (y : Matrix (Fin n) (Fin n) E) :
    T.μ ((1 : AfP p) ⊗ₜ[ℚ] y) = y.map (fun z => (1 : AfP p) ⊗ₜ[ℚ] z) := by
  ext i k
  exact T.mu 1 y i k

/- English proof (translation)
Apply `T.μ.injective` to reduce the goal to its premises. Establish `h` using `hM (AfP p) E A n T.μ T.mu (xU T : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)`. Establish `h0` using `iso_map T`. Rewrite using `[map_mul, map_mul, map_one, mu_b, traceMap_unipotent, Matrix.mul_assoc]`. Rewrite `h` using `[traceMap_unipotent]`.

Establish `e : (Dg A n).map (fun z => (1 : AfP p) ⊗ₜ[ℚ] z) = Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] (A.dg n i : E))`. Rewrite using `[Matrix.diagonal_map (by simp)]`. Rewrite using `[e, h]`. Conclude with `mul_eq_one_comm.1 h0`.
-/
private theorem triv_mat (hM : MuStar) {S : Setup A n p} (T : Tr S) :
    (xU T : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E) * ((1 : AfP p) ⊗ₜ[ℚ] Dg A n) *
      (starT (hermStar (A.H n) (A.det_ne n)) (AfP p) (xU T)).unop = 1 := by
  apply T.μ.injective
  have h := hM (AfP p) E A n T.μ T.mu (xU T : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)
  have h0 := iso_map T
  rw [map_mul, map_mul, map_one, mu_b, traceMap_unipotent, Matrix.mul_assoc]
  rw [traceMap_unipotent] at h
  have e : (Dg A n).map (fun z => (1 : AfP p) ⊗ₜ[ℚ] z) =
      Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] (A.dg n i : E)) := by
    rw [Matrix.diagonal_map (by simp)]
  rw [e, h]
  exact mul_eq_one_comm.1 h0

private def similitudeToGammaZeroHom (S : Setup A n p) : GlobalTheory.LKCx.grp S.G (A.β₀ n) →* Gam0 E n where
  toFun y := ⟨y.1, Subgroup.mem_inf.2 ⟨sim_of A n y.1.1 y.1.2 y.2.1, y.2.2⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/- English proof (translation)
Use extensionality with `i k`. Conclude with `T.Φ_E _`.
-/
private theorem mat_rat {S : Setup A n p} (T : Tr S) (y : Gam0 E n) :
    (mat (rat y)).val.map T.Φ = (y.1.1.val).map (fun z => (1 : AfP p) ⊗ₜ[ℚ] z) := by
  ext i k
  exact T.Φ_E _

/- English proof (translation)
The claim follows from `RingHom.congr_fun (RingHom.ext_rat (T.ρ.comp (algebraMap ℚ AfQ)) (algebraMap ℚ (AfP p))) s`.
-/
private theorem rho_rat {S : Setup A n p} (T : Tr S) (s : ℚ) : T.ρ (algebraMap ℚ AfQ s) = algebraMap ℚ (AfP p) s :=
  RingHom.congr_fun (RingHom.ext_rat (T.ρ.comp (algebraMap ℚ AfQ)) (algebraMap ℚ (AfP p))) s

end UpperTheory.Gal.W2.Seed

/- English proof (translation)
Introduce `hM E _ _ _ A n p _ S T`. Set `β : S.G.Cˣ` to `A.β₀ n`. Establish `hx : Triv S.G (AfP p) (β : S.G.C) (xU T) 1` using `(triv_mat hM T).trans (map_one (algebraMap (AfP p) (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E))).symm`. Establish `hsym : sh S.G (β : S.G.C) = (β : S.G.C)` using `hermStar_baseMatrix A n`. Set `B : DForm S.G` to `⟨β, hsym, ⟨xU T, 1, hx⟩, fun v x h0 => book_constants_pos_of_pos A n S.sig v (((A.β₀ n)⁻¹ : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E) (Units.mul_inv (A.β₀ n)) x h0⟩`.

Use `⟨B, xU T, hx, similitudeToGammaZeroHom S, fun y => rfl, fun y => ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Prod.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Apply `T.μ.injective` to reduce the goal to its premises.

Establish `h1` using `T.j_mx (rat (similitudeToGammaZeroHom S y))`. Set `Y : (Matrix (Fin n) (Fin n) E)ˣ` to `y.1.1`. Establish `h2 : T.μ (S.mx (GlobalTheory.LKCx.toAfF S.G B.β (xU T) 1 hx y)) = T.a.val.map T.Φ * (Y : Matrix (Fin n) (Fin n) E).map (fun z => (1 : AfP p) ⊗ₜ[ℚ] z) * (T.a⁻¹).val.map T.Φ` using `by show T.μ ((xU T : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E) * ((1 : AfP p) ⊗ₜ[ℚ] (Y : Matrix (Fin n) (Fin n) E)) * (((xU T)⁻¹ : (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ) : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)) = _`. Rewrite using `[map_mul, map_mul, traceMap_unipotent, mu_xi, mu_b]`. Use `h2.trans (Eq.trans ?_ h1.symm)` and prove the remaining obligations.

Rewrite using `[Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, mat_rat]`. Both sides reduce to the same expression. Apply `Units.ext` to reduce the goal to its premises. Establish `h1` using `T.j_sim (rat (similitudeToGammaZeroHom S y))`. Conclude with `(rho_rat T _).symm.trans h1.symm`.
-/
theorem UpperTheory.Gal.W2.Seed.pStdForm :
    MuStar → StdForm := by
  intro hM E _ _ _ A n p _ S T
  let β : S.G.Cˣ := A.β₀ n
  have hx : Triv S.G (AfP p) (β : S.G.C) (xU T) 1 :=
    (triv_mat hM T).trans (map_one (algebraMap (AfP p) (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E))).symm
  have hsym : sh S.G (β : S.G.C) = (β : S.G.C) := hermStar_baseMatrix A n
  let B : DForm S.G := ⟨β, hsym, ⟨xU T, 1, hx⟩, fun v x h0 =>
    book_constants_pos_of_pos A n S.sig v (((A.β₀ n)⁻¹ : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E) (Units.mul_inv (A.β₀ n)) x h0⟩
  refine ⟨B, xU T, hx, similitudeToGammaZeroHom S, fun y => rfl, fun y => ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    apply T.μ.injective
    have h1 := T.j_mx (rat (similitudeToGammaZeroHom S y))
    let Y : (Matrix (Fin n) (Fin n) E)ˣ := y.1.1
    have h2 : T.μ (S.mx (GlobalTheory.LKCx.toAfF S.G B.β (xU T) 1 hx y)) =
        T.a.val.map T.Φ * (Y : Matrix (Fin n) (Fin n) E).map (fun z => (1 : AfP p) ⊗ₜ[ℚ] z) * (T.a⁻¹).val.map T.Φ := by
      show T.μ ((xU T : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E) * ((1 : AfP p) ⊗ₜ[ℚ] (Y : Matrix (Fin n) (Fin n) E)) *
        (((xU T)⁻¹ : (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ) : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)) = _
      rw [map_mul, map_mul, traceMap_unipotent, mu_xi, mu_b]
    refine h2.trans (Eq.trans ?_ h1.symm)
    rw [Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, mat_rat]
    rfl
  · apply Units.ext
    have h1 := T.j_sim (rat (similitudeToGammaZeroHom S y))
    exact (rho_rat T _).symm.trans h1.symm
