import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.KFinOfMem
import Development.WeilBound.ThetaLifts.LatticeBasics.ExistsIsGauss

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def jE (n : ℕ) (ε : ℤˣ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ := Matrix.fromBlocks 0 1 (((ε : ℤ) : ℂ) • 1) 0

def thB (d : SD σ) (ε : ℤˣ) (w : InfinitePlace F) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) ℂ :=
  d.b.1.map (d.B.emb w).1 * (jE d.n ε)ᵀ * (d.b⁻¹).1.map (d.B.emb w).1

def thA {d : SD σ} (R : RD d) (w : InfinitePlace F) : Matrix (Fin d.m) (Fin d.m) ℂ :=
  (-(Complex.I * ((((R.ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ)) * R.ζ))) • 1

/- English proof (translation)
Use extensionality with `i j`. Conclude with `(GlobalTheory.CompanionTheory.CMAdele.piInf_tmul τ 1 (J i j)).trans (by rw [show (1 : AF F).1 w = 1 from rfl, map_one, one_mul]; rfl)`.
-/
theorem map_incM' {w : InfinitePlace F} (τ : EmbOver E w) {ι ι' : Type} (J : Matrix ι ι' E) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  exact (GlobalTheory.CompanionTheory.CMAdele.piInf_tmul τ 1 (J i j)).trans (by rw [show (1 : AF F).1 w = 1 from rfl, map_one, one_mul]; rfl)

/- English proof (translation)
The claim follows from `Matrix.map_mul (f := starRingEnd ℂ)`.
-/
theorem map_star_mul' {ι : Type} [Fintype ι] (x y : Matrix ι ι ℂ) : (x * y).map star = x.map star * y.map star :=
  Matrix.map_mul (f := starRingEnd ℂ)

/- English proof (translation)
Establish `hMJ : Mᵀ * J * M.map star = J`. Rewrite using `[← hJ, hMk]`. Simplify using `only [Matrix.transpose_mul, map_star_mul']`. Establish `e1' : bw.map star * biw.map star = 1`. Rewrite using `[← map_star_mul', e1]`.

Use extensionality with `i j`. Simplify using `[Matrix.one_apply, apply_ite]`. Establish `e1t : biwᵀ * bwᵀ = 1` using `by rw [← Matrix.transpose_mul, e1, Matrix.transpose_one]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = bwᵀ * (kwᵀ * Dw * kw.map star) * bw.map star := by`. Rewrite using `[e1t, e1']`. Simplify using `only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]`. Use `_ = bwᵀ * Dw * bw.map star := by rw [hk2]`. Establish `hc1 : M.map star * Mᵀ = 1`.

Establish `: M.map star * Mᵀ = (M * Mᴴ)ᵀ` using `by rw [Matrix.transpose_mul]; rfl`. Rewrite using `[this, hu, Matrix.transpose_one]`. Establish `hcomm : Mᵀ * J = J * Mᵀ`. Combine the equalities or inequalities in the displayed calculation. Establish `hcomm' : Jᵀ * M = M * Jᵀ`.

Use `congrArg Matrix.transpose hcomm` as an intermediate fact. Simplify `this` using `only [Matrix.transpose_mul, Matrix.transpose_transpose]`. Establish `hkw : kw = bw * M * biw`. Rewrite using `[hMk]`. Simplify using `only [← Matrix.mul_assoc, e1, Matrix.one_mul]`.

Rewrite using `[Matrix.mul_assoc, e1, Matrix.mul_one]`. Use `show kw * (bw * Jᵀ * biw) = bw * Jᵀ * biw * kw`. Rewrite using `[hkw]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = bw * (Jᵀ * M) * biw := by rw [e2, Matrix.mul_one, hcomm']`. Use `_ = bw * Jᵀ * biw * (bw * M * biw) := by`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc biw bw, e2, Matrix.one_mul]`.
-/
theorem commute_of_unitary_conjugate {ι : Type} [Fintype ι] [DecidableEq ι] {bw biw kw M Dw J : Matrix ι ι ℂ} (e1 : bw * biw = 1)
    (e2 : biw * bw = 1) (hMk : M = biw * kw * bw) (hu : M * Mᴴ = 1) (hJ : bwᵀ * Dw * bw.map star = J)
    (hk2 : kwᵀ * Dw * kw.map star = Dw) : Commute kw (bw * Jᵀ * biw) := by
  have hMJ : Mᵀ * J * M.map star = J := by
    rw [← hJ, hMk]
    simp only [Matrix.transpose_mul, map_star_mul']
    have e1' : bw.map star * biw.map star = 1 := by
      rw [← map_star_mul', e1]; ext i j; simp [Matrix.one_apply, apply_ite]
    have e1t : biwᵀ * bwᵀ = 1 := by rw [← Matrix.transpose_mul, e1, Matrix.transpose_one]
    calc _ = bwᵀ * kwᵀ * (biwᵀ * bwᵀ) * Dw * (bw.map star * biw.map star) * kw.map star * bw.map star := by
          simp only [Matrix.mul_assoc]
      _ = bwᵀ * (kwᵀ * Dw * kw.map star) * bw.map star := by
          rw [e1t, e1']; simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
      _ = bwᵀ * Dw * bw.map star := by rw [hk2]
  have hc1 : M.map star * Mᵀ = 1 := by
    have : M.map star * Mᵀ = (M * Mᴴ)ᵀ := by rw [Matrix.transpose_mul]; rfl
    rw [this, hu, Matrix.transpose_one]
  have hcomm : Mᵀ * J = J * Mᵀ := by
    calc Mᵀ * J = Mᵀ * J * (M.map star * Mᵀ) := by rw [hc1, Matrix.mul_one]
      _ = (Mᵀ * J * M.map star) * Mᵀ := by simp only [Matrix.mul_assoc]
      _ = J * Mᵀ := by rw [hMJ]
  have hcomm' : Jᵀ * M = M * Jᵀ := by
    have := congrArg Matrix.transpose hcomm
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using this
  have hkw : kw = bw * M * biw := by
    rw [hMk]; simp only [← Matrix.mul_assoc, e1, Matrix.one_mul]; rw [Matrix.mul_assoc, e1, Matrix.mul_one]
  show kw * (bw * Jᵀ * biw) = bw * Jᵀ * biw * kw
  rw [hkw]
  calc bw * M * biw * (bw * Jᵀ * biw) = bw * (M * (biw * bw) * Jᵀ) * biw := by
        simp only [Matrix.mul_assoc]
    _ = bw * (Jᵀ * M) * biw := by rw [e2, Matrix.mul_one, hcomm']
    _ = bw * Jᵀ * biw * (bw * M * biw) := by
        simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc biw bw, e2, Matrix.one_mul]

/- English proof (translation)
Establish `h` using `d.ok.good.cm`. Establish `e1 : d.b.1.map (d.B.emb w).1 * (d.b⁻¹).1.map (d.B.emb w).1 = 1`. Rewrite using `[← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `e2 : (d.b⁻¹).1.map (d.B.emb w).1 * d.b.1.map (d.B.emb w).1 = 1`. Rewrite using `[← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]`.

Establish `hMk : (inFrame d.b k).map (piInf (d.B.emb w)) = (d.b⁻¹).1.map (d.B.emb w).1 * (mat2 k).map (piInf (d.B.emb w)) * d.b.1.map (d.B.emb w).1`. Rewrite using `[inFrame, Matrix.map_mul, Matrix.map_mul, map_incM', map_incM']`. Establish `hu` using `((d.ok.stdK k).1 hk).1 w`. Establish `cst : ∀ x : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E, (x.map σ).map (d.B.emb w).1 = (x.map (d.B.emb w).1).map star` using `fun x => by`. Use extensionality with `i j`.

Conclude with `h.2.2.2 (d.B.emb w).1 (x i j)`. Establish `cstA : ∀ x : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E), (x.map (cA σ)).map (piInf (d.B.emb w)) = (x.map (piInf (d.B.emb w))).map star` using `fun x => by ext i j; exact GlobalTheory.ThK.Dbl.Dense.piInf_cA h (d.B.emb w) (x i j)`. Establish `hDw : (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) = (dbl d.Y.J).map (d.B.emb w).1`. Rewrite using `[← map_incM']`. Use `congr 1`.

Apply the tactic sequence `ext (i | i) (j | j) <;> simp [dbl, incM, Matrix.fromBlocks]`. Establish `hJ : (d.b.1.map (d.B.emb w).1)ᵀ * (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) * (d.b.1.map (d.B.emb w).1).map star = jE d.n R.ε`. Use `congrArg (fun x => x.map (d.B.emb w).1) R.hε` as an intermediate fact. Simplify using `only [Matrix.map_mul, Matrix.transpose_map, cst] at this`. Rewrite using `[hDw, this]`.

Apply the tactic sequence `ext (i | i) (j | j) <;> by_cases hij : i = j <;> simp [jE, Matrix.fromBlocks, Matrix.smul_apply, Matrix.one_apply, hij]`. Establish `hk2 : ((mat2 k).map (piInf (d.B.emb w)))ᵀ * (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) * ((mat2 k).map (piInf (d.B.emb w))).map star = (dbl (incM F d.Y.J)).map (piInf (d.B.emb w))`. Establish `hk0 : (k.1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))ᵀ * dbl (incM F d.Y.J) * (k.1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).map (cA σ) = dbl (incM F d.Y.J)` using `k.2`. Use `congrArg (fun x => x.map (piInf (d.B.emb w))) hk0` as an intermediate fact. Simplify using `only [Matrix.map_mul, Matrix.transpose_map, cstA] at this`.

Conclude with `this`. Conclude with `commute_of_unitary_conjugate e1 e2 hMk hu hJ hk2`.
-/
theorem commute_thB {d : SD σ} (R : RD d) {k : d.G} (hk : k ∈ d.K) (w : InfinitePlace F) :
    Commute ((mat2 k).map (piInf (d.B.emb w))) (thB d R.ε w) := by
  have h := d.ok.good.cm
  have e1 : d.b.1.map (d.B.emb w).1 * (d.b⁻¹).1.map (d.B.emb w).1 = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : (d.b⁻¹).1.map (d.B.emb w).1 * d.b.1.map (d.B.emb w).1 = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hMk : (inFrame d.b k).map (piInf (d.B.emb w)) =
      (d.b⁻¹).1.map (d.B.emb w).1 * (mat2 k).map (piInf (d.B.emb w)) * d.b.1.map (d.B.emb w).1 := by
    rw [inFrame, Matrix.map_mul, Matrix.map_mul, map_incM', map_incM']
  have hu := ((d.ok.stdK k).1 hk).1 w
  have cst : ∀ x : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E, (x.map σ).map (d.B.emb w).1 =
      (x.map (d.B.emb w).1).map star := fun x => by
    ext i j; exact h.2.2.2 (d.B.emb w).1 (x i j)
  have cstA : ∀ x : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E),
      (x.map (cA σ)).map (piInf (d.B.emb w)) = (x.map (piInf (d.B.emb w))).map star :=
    fun x => by ext i j; exact GlobalTheory.ThK.Dbl.Dense.piInf_cA h (d.B.emb w) (x i j)
  have hDw : (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) = (dbl d.Y.J).map (d.B.emb w).1 := by
    rw [← map_incM']
    congr 1
    ext (i | i) (j | j) <;> simp [dbl, incM, Matrix.fromBlocks]
  have hJ : (d.b.1.map (d.B.emb w).1)ᵀ * (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) *
      (d.b.1.map (d.B.emb w).1).map star = jE d.n R.ε := by
    have := congrArg (fun x => x.map (d.B.emb w).1) R.hε
    simp only [Matrix.map_mul, Matrix.transpose_map, cst] at this
    rw [hDw, this]
    ext (i | i) (j | j) <;> by_cases hij : i = j <;> simp [jE, Matrix.fromBlocks, Matrix.smul_apply, Matrix.one_apply, hij]
  have hk2 : ((mat2 k).map (piInf (d.B.emb w)))ᵀ * (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) *
      ((mat2 k).map (piInf (d.B.emb w))).map star = (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) := by
    have hk0 : (k.1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))ᵀ * dbl (incM F d.Y.J) *
        (k.1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).map (cA σ) = dbl (incM F d.Y.J) := k.2
    have := congrArg (fun x => x.map (piInf (d.B.emb w))) hk0
    simp only [Matrix.map_mul, Matrix.transpose_map, cstA] at this
    exact this
  exact commute_of_unitary_conjugate e1 e2 hMk hu hJ hk2

end PositivityTheory.SiegelWeilFormula.KK

end
