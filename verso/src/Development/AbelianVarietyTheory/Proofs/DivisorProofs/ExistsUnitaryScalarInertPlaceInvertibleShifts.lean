import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldCompletionTensorOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormVanishesLagrangianTest
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertScalarUnit

open GlobalTheory.LatVac

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hreal : NumberField.ComplexEmbedding.IsReal τ`. Rewrite using `[NumberField.ComplexEmbedding.isReal_iff]`.

Use extensionality with `x`. Establish `h1` using `hσ.2.2.2 τ x`. Rewrite `h1` using `[h x]`. Rewrite using `[NumberField.ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply]`. Conclude with `h1.symm`.

Conclude with `(NumberField.InfinitePlace.not_isReal_iff_isComplex.2 (hσ.2.1.isComplex (NumberField.InfinitePlace.mk τ))) ⟨τ, hreal, rfl⟩`.
-/
theorem exists_ne_of_cm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra h
  push_neg at h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hreal : NumberField.ComplexEmbedding.IsReal τ := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have h1 := hσ.2.2.2 τ x
    rw [h x] at h1
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply]
    exact h1.symm
  exact (NumberField.InfinitePlace.not_isReal_iff_isComplex.2
    (hσ.2.1.isComplex (NumberField.InfinitePlace.mk τ))) ⟨τ, hreal, rfl⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `h` using `hu (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, evFin_liftV, sub_self])`. Rewrite `h` using `[sub_smul, one_smul]`. Conclude with `(sub_eq_zero.1 h).symm`.
-/
theorem idem_smul_of_at {M : Type} [AddCommGroup M] [Module (AF F) M] (v : Pl F) (u : M)
    (hu : At (evFin F v) u) : GlobalTheory.LatVac.liftV v (1 : Fv F v) • u = u := by
  have h := hu (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, evFin_liftV, sub_self])
  rw [sub_smul, one_smul] at h
  exact (sub_eq_zero.1 h).symm

/- English proof (translation)
Establish `h` using `at_liftV v (1 : Fv F v) (x - GlobalTheory.LatVac.liftV v (evFin F v x)) (by rw [map_sub, evFin_liftV, sub_self])`. Establish `h2` using `idem_smul_of_at v _ (at_liftV v (evFin F v x))`. Rewrite `h`, `h2` using `[smul_eq_mul]`. Take the linear combination `h + h2`.
-/
theorem idem_mul (v : Pl F) (x : AF F) :
    GlobalTheory.LatVac.liftV v (1 : Fv F v) * x = GlobalTheory.LatVac.liftV v (evFin F v x) := by
  have h := at_liftV v (1 : Fv F v) (x - GlobalTheory.LatVac.liftV v (evFin F v x)) (by rw [map_sub, evFin_liftV, sub_self])
  have h2 := idem_smul_of_at v _ (at_liftV v (evFin F v x))
  rw [smul_eq_mul] at h h2
  linear_combination h + h2

/- English proof (translation)
Introduce `u hu`. Rewrite using `[smul_smul, ← smul_eq_mul, at_liftV v 1 u hu, zero_smul]`.
-/
theorem at_idem_smul {M : Type} [AddCommGroup M] [Module (AF F) M] (v : Pl F) (z : M) :
    At (evFin F v) (GlobalTheory.LatVac.liftV v (1 : Fv F v) • z) := by
  intro u hu
  rw [smul_smul, ← smul_eq_mul, at_liftV v 1 u hu, zero_smul]

/- English proof (translation)
Establish `key : ∀ a : AE F E, GlobalTheory.LatVac.liftV v (1 : Fv F v) • a = (GlobalTheory.LatVac.liftV v).rTensor E (compFin F E v a)`. Introduce `a`. Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x e`.

Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, idem_mul]`. Simplify using `[compFin]`. Consider the case `add x y hx hy => rw [smul_add, hx, hy, map_add, map_add]`. Rewrite using `[key, ha, map_zero]`.
-/
theorem idem_smul_eq_zero (v : Pl F) (a : AE F E) (ha : compFin F E v a = 0) :
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • a = 0 := by
  have key : ∀ a : AE F E, GlobalTheory.LatVac.liftV v (1 : Fv F v) • a =
      (GlobalTheory.LatVac.liftV v).rTensor E (compFin F E v a) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul x e =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, idem_mul]
      simp [compFin]
    | add x y hx hy => rw [smul_add, hx, hy, map_add, map_add]
  rw [key, ha, map_zero]

/- English proof (translation)
Proceed by induction on `q using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x e => simp [compFin, evFin_liftV]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem compFin_lift (v : Pl F) (q : Fv F v ⊗[F] E) :
    compFin F E v ((GlobalTheory.LatVac.liftV v).rTensor E q) = q := by
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul x e => simp [compFin, evFin_liftV]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Use `set Mv := M.map (compFin F E v) with hMv`. Use `set Q : Matrix (Fin n) (Fin n) (AE F E) := Mv⁻¹.map ((GlobalTheory.LatVac.liftV v).rTensor E) with hQdef`. Establish `hQ : Q.map (compFin F E v) = Mv⁻¹`. Use extensionality with `i j`. Simplify using `[hQdef, compFin_lift]`.

Establish `hz : ∀ N : Matrix (Fin n) (Fin n) (AE F E), N.map (compFin F E v) = 1 → GlobalTheory.LatVac.liftV v (1 : Fv F v) • N = GlobalTheory.LatVac.liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (AE F E))`. Introduce `N hN`. Establish `h0 : GlobalTheory.LatVac.liftV v (1 : Fv F v) • (N - 1) = 0`. Use extensionality with `i j`. Rewrite using `[Matrix.smul_apply, Matrix.zero_apply]`.

Apply `idem_smul_eq_zero` to reduce the goal to its premises. Use `congrFun (congrFun hN i) j` as an intermediate fact. Rewrite `this` using `[Matrix.map_apply]`. Rewrite using `[Matrix.sub_apply, map_sub, this]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne hij]`. Rewrite `h0` using `[smul_sub, sub_eq_zero]`. Then use the resulting hypothesis. Use `⟨GlobalTheory.LatVac.liftV v (1 : Fv F v) • Q, at_idem_smul v Q, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.smul_mul]`. Apply `hz` to reduce the goal to its premises. Rewrite using `[← RingHom.mapMatrix_apply, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hQ, ← hMv, Matrix.nonsing_inv_mul _ h]`. Rewrite using `[Matrix.mul_smul]`. Apply `hz` to reduce the goal to its premises.

Rewrite using `[← RingHom.mapMatrix_apply, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hQ, ← hMv, Matrix.mul_nonsing_inv _ h]`.
-/
theorem exists_inv_at (v : Pl F) {n : ℕ} (M : Matrix (Fin n) (Fin n) (AE F E))
    (h : IsUnit (M.map (compFin F E v)).det) :
    ∃ b : Matrix (Fin n) (Fin n) (AE F E), At (evFin F v) b ∧
      b * M = GlobalTheory.LatVac.liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧
      M * b = GlobalTheory.LatVac.liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
  set Mv := M.map (compFin F E v) with hMv
  set Q : Matrix (Fin n) (Fin n) (AE F E) := Mv⁻¹.map ((GlobalTheory.LatVac.liftV v).rTensor E) with hQdef
  have hQ : Q.map (compFin F E v) = Mv⁻¹ := by
    ext i j
    simp [hQdef, compFin_lift]
  have hz : ∀ N : Matrix (Fin n) (Fin n) (AE F E), N.map (compFin F E v) = 1 →
      GlobalTheory.LatVac.liftV v (1 : Fv F v) • N = GlobalTheory.LatVac.liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    intro N hN
    have h0 : GlobalTheory.LatVac.liftV v (1 : Fv F v) • (N - 1) = 0 := by
      ext i j
      rw [Matrix.smul_apply, Matrix.zero_apply]
      apply idem_smul_eq_zero
      have := congrFun (congrFun hN i) j
      rw [Matrix.map_apply] at this
      rw [Matrix.sub_apply, map_sub, this]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply_ne hij]
    rwa [smul_sub, sub_eq_zero] at h0
  refine ⟨GlobalTheory.LatVac.liftV v (1 : Fv F v) • Q, at_idem_smul v Q, ?_, ?_⟩
  · rw [Matrix.smul_mul]
    apply hz
    rw [← RingHom.mapMatrix_apply, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hQ, ← hMv,
      Matrix.nonsing_inv_mul _ h]
  · rw [Matrix.mul_smul]
    apply hz
    rw [← RingHom.mapMatrix_apply, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hQ, ← hMv,
      Matrix.mul_nonsing_inv _ h]

end GlobalTheory.InertScalarUnit

namespace GlobalTheory.InertScalarUnit

open GlobalTheory.LatVac

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB v w hw n J g`. Establish `hK` using `GlobalTheory.InertTensorField.isField_tensor_of_isInertAt F E σ B hB v w hw`. Use `haveI : IsDomain (Fv F v ⊗[F] E) := hK.isDomain`. Establish `hunit : ∀ x : Fv F v ⊗[F] E, x ≠ 0 → IsUnit x` using `fun x hx => by`. Take `⟨y, hy⟩` from `hK.mul_inv_cancel hx`.

Conclude with `⟨⟨x, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩`. Establish `hσσ` using `GlobalTheory.AdelicU.cm_conj_conj hB.cm`. Take `⟨x₀, hx₀⟩` from `exists_ne_of_cm σ hB.cm`. Take `⟨ξ, hξ, hξ0⟩ : ∃ ξ : E, σ ξ = -ξ ∧ ξ ≠ 0` from `⟨x₀ - σ x₀, by rw [map_sub, hσσ]; ring, sub_ne_zero.2 (Ne.symm hx₀)⟩`. Set `ι : E →+* Fv F v ⊗[F] E` to `(Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E).toRingHom`.

Establish `hι : Function.Injective ι` using `ι.injective`. Use `set gv := (mat g).map (compFin F E v) with hgv`. Establish `hp0 : gv.charpoly ≠ 0` using `(Matrix.charpoly_monic gv).ne_zero`. Establish `hfin` using `Polynomial.finite_setOf_isRoot hp0`. Establish `hden : ∀ m : ℕ, (m : E) - ξ ≠ 0`.

Introduce `m h`. Establish `h1 : ξ = m` using `(sub_eq_zero.1 h).symm`. Establish `h2 : σ ξ = m` using `by rw [h1, map_natCast]`. Rewrite `h2` using `[hξ, h1]`. Establish `h3 : (m : E) = 0` using `by linear_combination (-1/2 : E) * h2`.

Conclude with `hξ0 (h1.trans h3)`. Establish `hnum : ∀ m : ℕ, (m : E) + ξ ≠ 0`. Introduce `m h`. Establish `h2` using `congrArg σ h`. Rewrite `h2` using `[map_add, map_natCast, hξ, map_zero, ← sub_eq_add_neg]`.

Conclude with `hden m h2`. Set `lam : ℕ → E` to `fun m => ((m : E) + ξ) / ((m : E) - ξ)`. Establish `hlam : Function.Injective lam`. Introduce `a b hab`. Simplify using `only [lam] at hab`.

Rewrite `hab` using `[div_eq_div_iff (hden a) (hden b)]`. Establish `h1 : ((a : E) - b) * (2 * ξ) = 0` using `by linear_combination -hab`. Break down `mul_eq_zero.1 h1 with h | h` into its components or cases. Conclude with `sub_eq_zero.1 h` after adjusting the coercions. Conclude with `absurd h (mul_ne_zero two_ne_zero hξ0)`.

Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m : ℕ, ¬ gv.charpoly.IsRoot (ι (lam m)) := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `Set.infinite_range_of_injective (hι.comp hlam) (hfin.subset (by rintro _ ⟨m, rfl⟩; exact hcon m))`. Use `set l := lam m with hl`.

Establish `hl1 : l ≠ 1`. Introduce `h`. Rewrite `h` using `[hl, div_eq_one_iff_eq (hden m)]`. Conclude with `hξ0 (by linear_combination h / 2)`. Establish `hσl : σ l = ((m : E) - ξ) / ((m : E) + ξ)`.

Simplify using `only [hl, lam, map_div₀, map_add, map_sub, map_natCast, hξ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hlσl : l * σ l = 1`. Rewrite using `[hσl, hl]`. Simplify using `only [lam]`.

Rewrite using `[div_mul_div_comm, mul_comm ((m : E) - ξ), div_self (mul_ne_zero (hnum m) (hden m))]`. Use `set e : AF F := GlobalTheory.LatVac.liftV v (1 : Fv F v) with he`. Establish `hee : e * e = e` using `by rw [he, idem_mul, evFin_liftV]`. Establish `hev : evFin F v e = 1` using `evFin_liftV v 1`. Use `set c : AE F E := (1 - e) ⊗ₜ[F] (1 : E) + e ⊗ₜ[F] l with hc`.

Use `set c' : AE F E := (1 - e) ⊗ₜ[F] (1 : E) + e ⊗ₜ[F] σ l with hc'`. Establish `hcc : c * c' = 1`. Establish `h1 : (1 - e) * (1 - e) = 1 - e` using `by linear_combination hee`. Establish `h2 : (1 - e) * e = 0` using `by linear_combination -hee`. Establish `h3 : e * (1 - e) = 0` using `by linear_combination -hee`.

Rewrite using `[hc, hc', add_mul, mul_add, mul_add, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, h1, h2, h3, hee, hlσl]`. Simplify using `only [mul_one, TensorProduct.zero_tmul, add_zero, zero_add]`. Rewrite using `[← TensorProduct.add_tmul, sub_add_cancel, Algebra.TensorProduct.one_def]`. Establish `hcA : cA σ c = c'`. Simplify using `[hc, hc', cA, Algebra.TensorProduct.map_tmul]`.

Establish `hcv : compFin F E v c = ι l`. Simplify using `[hc, compFin, Algebra.TensorProduct.map_tmul, hev, ι]`. Establish `hc1 : c - 1 = e • ((1 : AF F) ⊗ₜ[F] (l - 1))`. Rewrite using `[hc, TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.tmul_sub, Algebra.TensorProduct.one_def, TensorProduct.sub_tmul]`. Normalize the expressions using the abelian group laws.

Set `kG : GL (Fin n) (AE F E)` to `⟨Matrix.scalar (Fin n) c, Matrix.scalar (Fin n) c', by rw [← map_mul, hcc, map_one], by rw [← map_mul, mul_comm, hcc, map_one]⟩`. Establish `hmem : kG ∈ UG (cA σ) (incM F J)` using `by show (Matrix.scalar (Fin n) c)ᵀ * incM F J * (Matrix.scalar (Fin n) c).map (cA σ) = incM F J`. Establish `hT : (Matrix.scalar (Fin n) c)ᵀ = Matrix.scalar (Fin n) c`. Simplify using `[Matrix.scalar_apply]`. Establish `hM : (Matrix.scalar (Fin n) c).map (cA σ) = Matrix.scalar (Fin n) c'`.

Rewrite using `[Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _), hcA]`. Rewrite using `[hT, hM, (Matrix.scalar_commute c (fun r => Commute.all c r) _).eq, Matrix.mul_assoc, ← map_mul, hcc, map_one, Matrix.mul_one]`. Set `k : UA σ J` to `⟨kG, hmem⟩`. Establish `hk : mat k = Matrix.scalar (Fin n) c` using `rfl`. Establish `hSv : (Matrix.scalar (Fin n) c).map (compFin F E v) = Matrix.scalar (Fin n) (ι l)`.

Rewrite using `[Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _), hcv]`. Establish `hAt : At (evFin F v) (mat k - 1)`. Establish `: mat k - 1 = e • Matrix.scalar (Fin n) ((1 : AF F) ⊗ₜ[F] (l - 1))`. Rewrite using `[hk]`. Use extensionality with `i j`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[Matrix.scalar_apply, hc1]`. Simplify using `[Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]`. Rewrite using `[this]`.

Conclude with `at_idem_smul v _`. Establish `hdeta : IsUnit ((1 - mat k).map (compFin F E v)).det`. Rewrite using `[← RingHom.mapMatrix_apply, map_sub, map_one, RingHom.mapMatrix_apply, hk, hSv, ← map_one (Matrix.scalar (Fin n) : Fv F v ⊗[F] E →+* _), ← map_sub, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const]`. Use `IsUnit.pow _ (hunit _ ?_)` and prove the remaining obligations. Rewrite using `[← map_one ι, ← map_sub]`.

Conclude with `(map_ne_zero_iff ι hι).2 (sub_ne_zero.2 hl1.symm)`. Establish `hgi : mat g⁻¹ * mat g = 1` using `by show ((↑(g⁻¹ * g) : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) = 1`. Rewrite using `[inv_mul_cancel]`. Both sides reduce to the same expression. Use `set hv := (mat g⁻¹).map (compFin F E v) with hhv`.

Establish `hhg : hv * gv = 1`. Rewrite using `[hhv, hgv, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul, hgi, map_one]`. Establish `hdetb : IsUnit ((1 - mat (g⁻¹ * k)).map (compFin F E v)).det`. Establish `hmk : mat (g⁻¹ * k) = mat g⁻¹ * mat k` using `rfl`. Rewrite using `[hmk, ← RingHom.mapMatrix_apply, map_sub, map_one, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← hhv, hk, hSv]`.

Establish `hfac : 1 - hv * Matrix.scalar (Fin n) (ι l) = hv * -(Matrix.scalar (Fin n) (ι l) - gv)`. Rewrite using `[neg_sub, Matrix.mul_sub, hhg]`. Rewrite using `[hfac, Matrix.det_mul, Matrix.det_neg, ← Matrix.eval_charpoly]`. Establish `hd1 : hv.det * gv.det = 1` using `by rw [← Matrix.det_mul, hhg, Matrix.det_one]`. Conclude with `IsUnit.mul ⟨⟨hv.det, gv.det, hd1, by rw [mul_comm]; exact hd1⟩, rfl⟩ (IsUnit.mul (IsUnit.pow _ isUnit_one.neg) (hunit _ hm))`.

Take `⟨a, ha, ha1, ha2⟩` from `exists_inv_at v (1 - mat k) hdeta`. Take `⟨b, hb, hb1, hb2⟩` from `exists_inv_at v (1 - mat (g⁻¹ * k)) hdetb`. Conclude with `⟨k, hAt, a, b, ha, hb, ha1, ha2, hb1, hb2⟩`.
-/
theorem exists_scalar_inv_at : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (g : UA σ J),
    ∃ k : UA σ J, At (evFin F v) (mat k - 1) ∧ ∃ a b : Matrix (Fin n) (Fin n) (AE F E), At (evFin F v) a ∧ At (evFin F v) b ∧
      a * (1 - mat k) = liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧
      (1 - mat k) * a = liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧
      b * (1 - mat (g⁻¹ * k)) = liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧
      (1 - mat (g⁻¹ * k)) * b = liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
  intro F E _ _ _ _ _ σ B hB v w hw n J g
  have hK := GlobalTheory.InertTensorField.isField_tensor_of_isInertAt F E σ B hB v w hw
  haveI : IsDomain (Fv F v ⊗[F] E) := hK.isDomain
  have hunit : ∀ x : Fv F v ⊗[F] E, x ≠ 0 → IsUnit x := fun x hx => by
    obtain ⟨y, hy⟩ := hK.mul_inv_cancel hx
    exact ⟨⟨x, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩
  have hσσ := GlobalTheory.AdelicU.cm_conj_conj hB.cm
  obtain ⟨x₀, hx₀⟩ := exists_ne_of_cm σ hB.cm
  obtain ⟨ξ, hξ, hξ0⟩ : ∃ ξ : E, σ ξ = -ξ ∧ ξ ≠ 0 :=
    ⟨x₀ - σ x₀, by rw [map_sub, hσσ]; ring, sub_ne_zero.2 (Ne.symm hx₀)⟩
  let ι : E →+* Fv F v ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E).toRingHom
  have hι : Function.Injective ι := ι.injective
  set gv := (mat g).map (compFin F E v) with hgv
  have hp0 : gv.charpoly ≠ 0 := (Matrix.charpoly_monic gv).ne_zero
  have hfin := Polynomial.finite_setOf_isRoot hp0
  have hden : ∀ m : ℕ, (m : E) - ξ ≠ 0 := by
    intro m h
    have h1 : ξ = m := (sub_eq_zero.1 h).symm
    have h2 : σ ξ = m := by rw [h1, map_natCast]
    rw [hξ, h1] at h2
    have h3 : (m : E) = 0 := by linear_combination (-1/2 : E) * h2
    exact hξ0 (h1.trans h3)
  have hnum : ∀ m : ℕ, (m : E) + ξ ≠ 0 := by
    intro m h
    have h2 := congrArg σ h
    rw [map_add, map_natCast, hξ, map_zero, ← sub_eq_add_neg] at h2
    exact hden m h2
  let lam : ℕ → E := fun m => ((m : E) + ξ) / ((m : E) - ξ)
  have hlam : Function.Injective lam := by
    intro a b hab
    simp only [lam] at hab
    rw [div_eq_div_iff (hden a) (hden b)] at hab
    have h1 : ((a : E) - b) * (2 * ξ) = 0 := by linear_combination -hab
    rcases mul_eq_zero.1 h1 with h | h
    · exact_mod_cast sub_eq_zero.1 h
    · exact absurd h (mul_ne_zero two_ne_zero hξ0)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ¬ gv.charpoly.IsRoot (ι (lam m)) := by
    by_contra hcon
    push_neg at hcon
    exact Set.infinite_range_of_injective (hι.comp hlam) (hfin.subset (by rintro _ ⟨m, rfl⟩; exact hcon m))
  set l := lam m with hl
  have hl1 : l ≠ 1 := by
    intro h
    rw [hl, div_eq_one_iff_eq (hden m)] at h
    exact hξ0 (by linear_combination h / 2)
  have hσl : σ l = ((m : E) - ξ) / ((m : E) + ξ) := by
    simp only [hl, lam, map_div₀, map_add, map_sub, map_natCast, hξ]
    ring
  have hlσl : l * σ l = 1 := by
    rw [hσl, hl]
    simp only [lam]
    rw [div_mul_div_comm, mul_comm ((m : E) - ξ), div_self (mul_ne_zero (hnum m) (hden m))]
  set e : AF F := GlobalTheory.LatVac.liftV v (1 : Fv F v) with he
  have hee : e * e = e := by rw [he, idem_mul, evFin_liftV]
  have hev : evFin F v e = 1 := evFin_liftV v 1
  set c : AE F E := (1 - e) ⊗ₜ[F] (1 : E) + e ⊗ₜ[F] l with hc
  set c' : AE F E := (1 - e) ⊗ₜ[F] (1 : E) + e ⊗ₜ[F] σ l with hc'
  have hcc : c * c' = 1 := by
    have h1 : (1 - e) * (1 - e) = 1 - e := by linear_combination hee
    have h2 : (1 - e) * e = 0 := by linear_combination -hee
    have h3 : e * (1 - e) = 0 := by linear_combination -hee
    rw [hc, hc', add_mul, mul_add, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      h1, h2, h3, hee, hlσl]
    simp only [mul_one, TensorProduct.zero_tmul, add_zero, zero_add]
    rw [← TensorProduct.add_tmul, sub_add_cancel, Algebra.TensorProduct.one_def]
  have hcA : cA σ c = c' := by
    simp [hc, hc', cA, Algebra.TensorProduct.map_tmul]
  have hcv : compFin F E v c = ι l := by
    simp [hc, compFin, Algebra.TensorProduct.map_tmul, hev, ι]
  have hc1 : c - 1 = e • ((1 : AF F) ⊗ₜ[F] (l - 1)) := by
    rw [hc, TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.tmul_sub, Algebra.TensorProduct.one_def,
      TensorProduct.sub_tmul]
    abel
  let kG : GL (Fin n) (AE F E) := ⟨Matrix.scalar (Fin n) c, Matrix.scalar (Fin n) c',
    by rw [← map_mul, hcc, map_one], by rw [← map_mul, mul_comm, hcc, map_one]⟩
  have hmem : kG ∈ UG (cA σ) (incM F J) := by
    show (Matrix.scalar (Fin n) c)ᵀ * incM F J * (Matrix.scalar (Fin n) c).map (cA σ) = incM F J
    have hT : (Matrix.scalar (Fin n) c)ᵀ = Matrix.scalar (Fin n) c := by
      simp [Matrix.scalar_apply]
    have hM : (Matrix.scalar (Fin n) c).map (cA σ) = Matrix.scalar (Fin n) c' := by
      rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _), hcA]
    rw [hT, hM, (Matrix.scalar_commute c (fun r => Commute.all c r) _).eq, Matrix.mul_assoc, ← map_mul, hcc,
      map_one, Matrix.mul_one]
  let k : UA σ J := ⟨kG, hmem⟩
  have hk : mat k = Matrix.scalar (Fin n) c := rfl
  have hSv : (Matrix.scalar (Fin n) c).map (compFin F E v) = Matrix.scalar (Fin n) (ι l) := by
    rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _), hcv]

  have hAt : At (evFin F v) (mat k - 1) := by
    have : mat k - 1 = e • Matrix.scalar (Fin n) ((1 : AF F) ⊗ₜ[F] (l - 1)) := by
      rw [hk]
      ext i j
      by_cases hij : i = j
      · subst hij; simp [Matrix.scalar_apply, hc1]
      · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    rw [this]
    exact at_idem_smul v _

  have hdeta : IsUnit ((1 - mat k).map (compFin F E v)).det := by
    rw [← RingHom.mapMatrix_apply, map_sub, map_one, RingHom.mapMatrix_apply, hk, hSv,
      ← map_one (Matrix.scalar (Fin n) : Fv F v ⊗[F] E →+* _), ← map_sub, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const]
    refine IsUnit.pow _ (hunit _ ?_)
    rw [← map_one ι, ← map_sub]
    exact (map_ne_zero_iff ι hι).2 (sub_ne_zero.2 hl1.symm)

  have hgi : mat g⁻¹ * mat g = 1 := by
    show ((↑(g⁻¹ * g) : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) = 1
    rw [inv_mul_cancel]
    rfl
  set hv := (mat g⁻¹).map (compFin F E v) with hhv
  have hhg : hv * gv = 1 := by
    rw [hhv, hgv, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul, hgi, map_one]
  have hdetb : IsUnit ((1 - mat (g⁻¹ * k)).map (compFin F E v)).det := by
    have hmk : mat (g⁻¹ * k) = mat g⁻¹ * mat k := rfl
    rw [hmk, ← RingHom.mapMatrix_apply, map_sub, map_one, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      ← hhv, hk, hSv]
    have hfac : 1 - hv * Matrix.scalar (Fin n) (ι l) = hv * -(Matrix.scalar (Fin n) (ι l) - gv) := by
      rw [neg_sub, Matrix.mul_sub, hhg]
    rw [hfac, Matrix.det_mul, Matrix.det_neg, ← Matrix.eval_charpoly]
    have hd1 : hv.det * gv.det = 1 := by rw [← Matrix.det_mul, hhg, Matrix.det_one]
    exact IsUnit.mul ⟨⟨hv.det, gv.det, hd1, by rw [mul_comm]; exact hd1⟩, rfl⟩
      (IsUnit.mul (IsUnit.pow _ isUnit_one.neg) (hunit _ hm))
  obtain ⟨a, ha, ha1, ha2⟩ := exists_inv_at v (1 - mat k) hdeta
  obtain ⟨b, hb, hb1, hb2⟩ := exists_inv_at v (1 - mat (g⁻¹ * k)) hdetb
  exact ⟨k, hAt, a, b, ha, hb, ha1, ha2, hb1, hb2⟩

end GlobalTheory.InertScalarUnit
