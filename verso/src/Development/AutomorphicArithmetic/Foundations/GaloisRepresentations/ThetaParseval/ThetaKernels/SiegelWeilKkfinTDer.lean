import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.CharacterQuadraticDerivativeZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
abbrev dg_k : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := diagCols (Fin d.n)
abbrev secondFrameColumns : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := incM F d.b.1.toCols₂
abbrev sp_k (x y : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : AF F :=
  symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) x y
def mZ_k (Z X : Mx F E d.m d.n) : ℝ :=
  Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (_root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d (X * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ) (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)))
variable {d}
/- English proof (translation)
The claim follows from `d.dd.form x y`.
-/
theorem sp_eq_k (x y : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d x y = (d.dd.e x).1 ⬝ᵥ (d.dd.e y).2 - (d.dd.e y).1 ⬝ᵥ (d.dd.e x).2 := d.dd.form x y
/- English proof (translation)
Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KK.sp_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_eq_k]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sp_anti_k (x y : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d y x = -_root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d x y := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.sp_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_eq_k]; ring
/- English proof (translation)
Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KK.sp_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_eq_k, map_smul, Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, mul_sub]`.
-/
theorem sp_smul_right_k (c : AF F) (x y : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d x (c • y) = c * _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d x y := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.sp_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_eq_k, map_smul, Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    mul_sub]
/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, map_add, Prod.fst_add, Prod.snd_add, add_assoc, add_dotProduct, dotProduct_add, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_eq_k]`. Use `congr 2`. Take the linear combination `(-((d.dd.e v).1 ⬝ᵥ (d.dd.e w).2)) * invOf_mul_self (2 : AF F)`.
-/
theorem rho_rho_k (v w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) (Φ : d.Fn) :
    d.dd.rho d.B.ψ v (d.dd.rho d.B.ψ w Φ) = d.B.ψ (⅟(2 : AF F) * _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d v w) • d.dd.rho d.B.ψ (v + w) Φ := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, map_add, Prod.fst_add,
    Prod.snd_add, add_assoc, add_dotProduct, dotProduct_add, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_eq_k]
  congr 2
  linear_combination (-((d.dd.e v).1 ⬝ᵥ (d.dd.e w).2)) * invOf_mul_self (2 : AF F)
/- English proof (translation)
Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KK.rho_rho_k, _root_.PositivityTheory.SiegelWeilFormula.KK.rho_rho_k, smul_smul, add_comm w v, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_anti_k v w, ← AddChar.map_add_eq_mul]`. Use `congr 2`. Take the linear combination `(_root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d v w) * invOf_mul_self (2 : AF F)`.
-/
theorem rho_comm_k (v w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) (Φ : d.Fn) :
    d.dd.rho d.B.ψ v (d.dd.rho d.B.ψ w Φ) = d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d v w) • d.dd.rho d.B.ψ w (d.dd.rho d.B.ψ v Φ) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.rho_rho_k, _root_.PositivityTheory.SiegelWeilFormula.KK.rho_rho_k, smul_smul, add_comm w v, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_anti_k v w, ← AddChar.map_add_eq_mul]
  congr 2
  linear_combination (_root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d v w) * invOf_mul_self (2 : AF F)
/- English proof (translation)
Apply the tactic sequence `ext (i | i) (j | j) <;> simp [dbl, incM, Matrix.fromBlocks]`.
-/
theorem dbl_incM_k (J : Matrix (Fin d.n) (Fin d.n) E) : dbl (incM F J) = incM F (dbl J) := by
  ext (i | i) (j | j) <;> simp [dbl, incM, Matrix.fromBlocks]
/- English proof (translation)
Take `⟨ε, hε⟩` from `d.ok.frame.1`. Establish `h0 : d.b.1.toCols₂ᵀ * dbl d.Y.J * d.b.1.toCols₂.map σ = 0`. Use extensionality with `i j`. Use `congrFun₂ hε (Sum.inr i) (Sum.inr j)` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.toCols₂, Matrix.map_apply, Matrix.transpose_apply]`.

Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns, cA_incM, _root_.PositivityTheory.SiegelWeilFormula.KK.dbl_incM_k, incM_transpose, ← incM_mul', ← incM_mul', h0]`. Use extensionality with `i j`. Simplify using `[incM]`.
-/
theorem secondFrameColumns_isotropic : (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ * dbl (incM F d.Y.J) * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d).map (cA σ) = 0 := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have h0 : d.b.1.toCols₂ᵀ * dbl d.Y.J * d.b.1.toCols₂.map σ = 0 := by
    ext i j
    have := congrFun₂ hε (Sum.inr i) (Sum.inr j)
    simpa [Matrix.mul_apply, Matrix.toCols₂, Matrix.map_apply, Matrix.transpose_apply] using this
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns, cA_incM, _root_.PositivityTheory.SiegelWeilFormula.KK.dbl_incM_k, incM_transpose, ← incM_mul', ← incM_mul', h0]
  ext i j
  simp [incM]
/- English proof (translation)
Establish `h` using `_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns_isotropic (d := d)`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KK.sp_k, symp, Dense.hTens_tr]`. Establish `e : (X * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)ᵀ * incM F d.A.J * (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ).map (cA σ) * (dbl (incM F d.Y.J))ᵀ = _root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d * (Xᵀ …`. Rewrite using `[Matrix.transpose_mul, Matrix.transpose_transpose, map_cA_mul, ← Matrix.transpose_map]`. Simplify using `only [Matrix.mul_assoc]`.

Establish `e2 : (Xᵀ * incM F d.A.J * Z.map (cA σ) * ((_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d).map (cA σ))ᵀ * (dbl (incM F d.Y.J))ᵀ) * _root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d = Xᵀ * incM F d.A.J * Z.map (cA σ) * ((_root_.PositivityTheory.S …`. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]`. Rewrite using `[e, Matrix.trace_mul_comm, e2, h]`. Simplify using the standard rewrite rules.
-/
theorem symplectic_secondColumns_isotropic (X Z : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d (X * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ) (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ) = 0 := by
  have h := _root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns_isotropic (d := d)
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.sp_k, symp, Dense.hTens_tr]
  have e : (X * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)ᵀ * incM F d.A.J * (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ).map (cA σ) * (dbl (incM F d.Y.J))ᵀ =
      _root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d * (Xᵀ * incM F d.A.J * Z.map (cA σ) * ((_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d).map (cA σ))ᵀ * (dbl (incM F d.Y.J))ᵀ) := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, map_cA_mul, ← Matrix.transpose_map]
    simp only [Matrix.mul_assoc]
  have e2 : (Xᵀ * incM F d.A.J * Z.map (cA σ) * ((_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d).map (cA σ))ᵀ * (dbl (incM F d.Y.J))ᵀ) * _root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d =
      Xᵀ * incM F d.A.J * Z.map (cA σ) * ((_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ * dbl (incM F d.Y.J) * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d).map (cA σ))ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, e2, h]
  simp
/- English proof (translation)
Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T]`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KK.rho_rho_k, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_smul_right_k, _root_.PositivityTheory.SiegelWeilFormula.KK.symplectic_secondColumns_isotropic, mul_zero, mul_zero, AddChar.map_zero_eq_one, one_smul, ← Matrix.smul_mul, ← Matr …`.
-/
theorem weilAction_secondColumns_translate (Φ : d.Fn) (Z : Mx F E d.m d.n) (t : ℝ) (X : Mx F E d.m d.n) :
    d.T (d.dd.rho d.B.ψ (realAd F t • (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)) Φ) X = d.T Φ (X + realAd F t • Z) := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.rho_rho_k, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_smul_right_k, _root_.PositivityTheory.SiegelWeilFormula.KK.symplectic_secondColumns_isotropic, mul_zero, mul_zero, AddChar.map_zero_eq_one, one_smul, ← Matrix.smul_mul,
    ← Matrix.add_mul]
/- English proof (translation)
Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T]`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KK.rho_comm_k, map_smul, smul_eq_mul, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_smul_right_k, ← Matrix.smul_mul]`. Use `congr 1`. Conclude with `d.ok.dbl.kill _ _ (GlobalTheory.HeisSchA.schr_mem_schA _ d.ok.good.std _ Φ hΦ)`.
-/
theorem T_rho_dg_k {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (Z : Mx F E d.m d.n) (t : ℝ) (X : Mx F E d.m d.n) :
    d.T (d.dd.rho d.B.ψ (realAd F t • (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ) X =
      d.B.ψ (realAd F t * _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d (X * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ) (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) * d.T Φ X := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.rho_comm_k, map_smul, smul_eq_mul, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_smul_right_k, ← Matrix.smul_mul]
  congr 1
  exact d.ok.dbl.kill _ _ (GlobalTheory.HeisSchA.schr_mem_schA _ d.ok.good.std _ Φ hΦ)
/- English proof (translation)
Rewrite using `[d.ok.good.std.2.2 _ (at_realAd_mul t s), tr_realAd_mul]`.
-/
theorem psi_line_k (s : AF F) (t : ℝ) : d.B.ψ (realAd F t * s) =
    Complex.exp (-(2 * Real.pi * Complex.I) * ((t * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F s) : ℝ) : ℂ)) := by
  rw [d.ok.good.std.2.2 _ (at_realAd_mul t s), tr_realAd_mul]
/- English proof (translation)
Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.KK.psi_line_k]`. Use `set c := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F s)`. Establish `h1 : HasDerivAt (fun t : ℝ => ((t * c : ℝ) : ℂ)) (c : ℂ) 0`. Use `((hasDerivAt_id (0 : ℝ)).mul_const c).ofReal_comp` as an intermediate fact. Simplify using `using this`.

Establish `h2` using `(h1.const_mul (-(2 * Real.pi * Complex.I))).cexp`. Simplify using `using h2`.
-/
theorem psi_line_deriv_k (s : AF F) : HasDerivAt (fun t : ℝ => d.B.ψ (realAd F t * s))
    (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F s) : ℂ)) 0 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KK.psi_line_k]
  set c := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F s)
  have h1 : HasDerivAt (fun t : ℝ => ((t * c : ℝ) : ℂ)) (c : ℂ) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const c).ofReal_comp
    simpa using this
  have h2 := (h1.const_mul (-(2 * Real.pi * Complex.I))).cexp
  simpa using h2
/- English proof (translation)
The claim follows from `funext fun _ => mul_add _ _ _`.
-/
theorem rho_add_fn_k (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) (Φ Ψ : d.Fn) :
    d.dd.rho d.B.ψ w (Φ + Ψ) = d.dd.rho d.B.ψ w Φ + d.dd.rho d.B.ψ w Ψ := funext fun _ => mul_add _ _ _
/- English proof (translation)
The claim follows from `funext fun _ => mul_left_comm _ _ _`.
-/
theorem rho_smul_fn_k (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) (c : ℂ) (Φ : d.Fn) :
    d.dd.rho d.B.ψ w (c • Φ) = c • d.dd.rho d.B.ψ w Φ := funext fun _ => mul_left_comm _ _ _
/- English proof (translation)
The claim follows from `funext fun _ => mul_zero _`.
-/
theorem rho_zero_fn_k (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    d.dd.rho d.B.ψ w (0 : d.Fn) = 0 := funext fun _ => mul_zero _
/- English proof (translation)
Rewrite using `[Darboux.rho, map_smul]`.
-/
theorem rho_line_k (u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) (t : ℝ) (Φ : d.Fn) :
    d.dd.rho d.B.ψ (realAd F t • u) Φ = schr d.B.ψ (realAd F t • d.dd.e u) Φ := by
  rw [Darboux.rho, map_smul]
/- English proof (translation)
Introduce `s hs` and use `by rw [← map_smul, hu s hs, map_zero]`.
-/
theorem at_e'_k {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u) : At (evI F) (d.dd.e u) :=
  fun s hs => by rw [← map_smul, hu s hs, map_zero]
/- English proof (translation)
Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.KK.rho_line_k]`. Establish `hw` using `_root_.PositivityTheory.SiegelWeilFormula.KK.at_e'_k hu`. Use `set w := d.dd.e u`. Proceed by induction on `hΨ using Submodule.span_induction with`. Consider the case `mem Φ hm`.

Take `⟨f, g, hg, rfl⟩` from `hm`. Take `⟨G, hG, hD⟩` from `Dense.hl_line_deriv (Box.nf w.1) (Dense.linForm (Box.nf w.2)) f`. Take `⟨S, hS⟩` from `d.ok.dbl.adm g hg`. Establish `e : ∀ t : ℝ, schr d.B.ψ (realAd F t • w) (pureA F f g) = pureA F (G t) g` using `fun t => by`. Use function extensionality and compare the values at `z`.

Rewrite using `[← Box.pt_self z, Box.schr_pt d.ok.good.std hw, Dense.pureA_pt, hG]`. Simplify using `only [Dense.hl, Dense.pureA_pt, mul_assoc]`. Simplify using `only [e, hS]`. Rewrite using `[Box.D, Box.DP_pure, hS]`. Conclude with `hD ha S`.

Consider the case `zero`. Establish `: ∀ t : ℝ, schr d.B.ψ (realAd F t • w) (0 : d.Fn) = 0` using `fun t => funext fun _ => mul_zero _`. Simplify using `only [this, map_zero, Box.D, Box.DP_zero]`. Conclude with `hasDerivAt_const _ _`. Consider the case `add x y hx hy ix iy`.

Establish `: ∀ t : ℝ, schr d.B.ψ (realAd F t • w) (x + y) = schr d.B.ψ (realAd F t • w) x + schr d.B.ψ (realAd F t • w) y` using `fun t => funext fun _ => mul_add _ _ _`. Simplify using `only [this, map_add]`. Rewrite using `[Box.D, Box.DP_add hx hy, map_add]`. Conclude with `ix.add iy`. Consider the case `smul c x hx ix`.

Establish `: ∀ t : ℝ, schr d.B.ψ (realAd F t • w) (c • x) = c • schr d.B.ψ (realAd F t • w) x` using `fun t => funext fun _ => mul_left_comm _ _ _`. Simplify using `only [this, map_smul, smul_eq_mul]`. Rewrite using `[Box.D, Box.DP_smul hx, map_smul, smul_eq_mul]`. Conclude with `ix.const_mul c`.
-/
theorem l_D_k {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u)
    (ha : Box.nf (d.dd.e u).1 ≠ 0) :
    HasDerivAt (fun t : ℝ => d.l (d.dd.rho d.B.ψ (realAd F t • u) Ψ)) (d.l (Box.D (d.dd.e u) Ψ)) 0 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KK.rho_line_k]
  have hw := _root_.PositivityTheory.SiegelWeilFormula.KK.at_e'_k hu
  set w := d.dd.e u
  induction hΨ using Submodule.span_induction with
  | mem Φ hm =>
    obtain ⟨f, g, hg, rfl⟩ := hm
    obtain ⟨G, hG, hD⟩ := Dense.hl_line_deriv (Box.nf w.1) (Dense.linForm (Box.nf w.2)) f
    obtain ⟨S, hS⟩ := d.ok.dbl.adm g hg
    have e : ∀ t : ℝ, schr d.B.ψ (realAd F t • w) (pureA F f g) = pureA F (G t) g := fun t => by
      funext z
      rw [← Box.pt_self z, Box.schr_pt d.ok.good.std hw, Dense.pureA_pt, hG]
      simp only [Dense.hl, Dense.pureA_pt, mul_assoc]
    simp only [e, hS]
    rw [Box.D, Box.DP_pure, hS]
    exact hD ha S
  | zero =>
    have : ∀ t : ℝ, schr d.B.ψ (realAd F t • w) (0 : d.Fn) = 0 := fun t => funext fun _ => mul_zero _
    simp only [this, map_zero, Box.D, Box.DP_zero]
    exact hasDerivAt_const _ _
  | add x y hx hy ix iy =>
    have : ∀ t : ℝ, schr d.B.ψ (realAd F t • w) (x + y) = schr d.B.ψ (realAd F t • w) x + schr d.B.ψ (realAd F t • w) y :=
      fun t => funext fun _ => mul_add _ _ _
    simp only [this, map_add]
    rw [Box.D, Box.DP_add hx hy, map_add]
    exact ix.add iy
  | smul c x hx ix =>
    have : ∀ t : ℝ, schr d.B.ψ (realAd F t • w) (c • x) = c • schr d.B.ψ (realAd F t • w) x :=
      fun t => funext fun _ => mul_left_comm _ _ _
    simp only [this, map_smul, smul_eq_mul]
    rw [Box.D, Box.DP_smul hx, map_smul, smul_eq_mul]
    exact ix.const_mul c
/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `[td_realAd_zero, Darboux.rho, schr]`.
-/
theorem schr_zero_at_k (Ψ : d.Fn) (u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    d.dd.rho d.B.ψ (realAd F 0 • u) Ψ = Ψ := by
  funext z
  simp [td_realAd_zero, Darboux.rho, schr]
/- English proof (translation)
Rewrite using `[td_realAd_zero, zero_mul, AddChar.map_zero_eq_one]`.
-/
theorem psi_zero_line_k (s : AF F) : d.B.ψ (realAd F 0 * s) = 1 := by
  rw [td_realAd_zero, zero_mul, AddChar.map_zero_eq_one]
/- English proof (translation)
Establish `hw` using `_root_.PositivityTheory.SiegelWeilFormula.KK.at_e'_k hu`. Establish `hΨ : d.dd.rho d.B.ψ v Φ ∈ d.sch` using `GlobalTheory.HeisSchA.schr_mem_schA _ d.ok.good.std _ Φ hΦ`. Use function extensionality and compare the values at `z`. Establish `h1 : HasDerivAt (fun t : ℝ => d.dd.rho d.B.ψ v (d.dd.rho d.B.ψ (realAd F t • u) Φ) z) (d.dd.rho d.B.ψ v (Box.D (d.dd.e u) Φ) z) 0`. Simplify using `only [Darboux.rho, schr, map_smul]`.

Conclude with `(Box.hasD d.ok.good.std hw hΦ _).const_mul _`. Establish `h2 : HasDerivAt (fun t : ℝ => d.dd.rho d.B.ψ v (d.dd.rho d.B.ψ (realAd F t • u) Φ) z) ((-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (_root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d v u)) : ℂ)) * d.dd.rho d.B.ψ v Φ z + 1 * Box.D (d.dd.e u …`. Establish `e : (fun t : ℝ => d.dd.rho d.B.ψ v (d.dd.rho d.B.ψ (realAd F t • u) Φ) z) = fun t : ℝ => d.B.ψ (realAd F t * _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d v u) * d.dd.rho d.B.ψ (realAd F t • u) (d.dd.rho d.B.ψ v Φ) z`. Use function extensionality and compare the values at `t`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KK.rho_comm_k, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_smul_right_k]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Establish `h3` using `Box.hasD d.ok.good.std hw hΨ z`. Simplify using `only [← _root_.PositivityTheory.SiegelWeilFormula.KK.rho_line_k] at h3`. Establish `h4` using `(_root_.PositivityTheory.SiegelWeilFormula.KK.psi_line_deriv_k (d := d) (_root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d v u)).mul h3`.

Rewrite `h4` using `[_root_.PositivityTheory.SiegelWeilFormula.KK.schr_zero_at_k, _root_.PositivityTheory.SiegelWeilFormula.KK.psi_zero_line_k]`. Then use the resulting hypothesis. Rewrite using `[h1.unique h2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, add_comm]`.
-/
theorem rho_D_k {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u)
    (v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    d.dd.rho d.B.ψ v (Box.D (d.dd.e u) Φ) = Box.D (d.dd.e u) (d.dd.rho d.B.ψ v Φ) +
      (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (_root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d v u)) : ℂ)) •
        d.dd.rho d.B.ψ v Φ := by
  have hw := _root_.PositivityTheory.SiegelWeilFormula.KK.at_e'_k hu
  have hΨ : d.dd.rho d.B.ψ v Φ ∈ d.sch := GlobalTheory.HeisSchA.schr_mem_schA _ d.ok.good.std _ Φ hΦ
  funext z
  have h1 : HasDerivAt (fun t : ℝ => d.dd.rho d.B.ψ v (d.dd.rho d.B.ψ (realAd F t • u) Φ) z)
      (d.dd.rho d.B.ψ v (Box.D (d.dd.e u) Φ) z) 0 := by
    simp only [Darboux.rho, schr, map_smul]
    exact (Box.hasD d.ok.good.std hw hΦ _).const_mul _
  have h2 : HasDerivAt (fun t : ℝ => d.dd.rho d.B.ψ v (d.dd.rho d.B.ψ (realAd F t • u) Φ) z)
      ((-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (_root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d v u)) : ℂ)) *
        d.dd.rho d.B.ψ v Φ z + 1 * Box.D (d.dd.e u) (d.dd.rho d.B.ψ v Φ) z) 0 := by
    have e : (fun t : ℝ => d.dd.rho d.B.ψ v (d.dd.rho d.B.ψ (realAd F t • u) Φ) z) =
        fun t : ℝ => d.B.ψ (realAd F t * _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d v u) * d.dd.rho d.B.ψ (realAd F t • u) (d.dd.rho d.B.ψ v Φ) z := by
      funext t
      rw [_root_.PositivityTheory.SiegelWeilFormula.KK.rho_comm_k, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_smul_right_k]
      rfl
    rw [e]
    have h3 := Box.hasD d.ok.good.std hw hΨ z
    simp only [← _root_.PositivityTheory.SiegelWeilFormula.KK.rho_line_k] at h3
    have h4 := (_root_.PositivityTheory.SiegelWeilFormula.KK.psi_line_deriv_k (d := d) (_root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d v u)).mul h3
    rwa [_root_.PositivityTheory.SiegelWeilFormula.KK.schr_zero_at_k, _root_.PositivityTheory.SiegelWeilFormula.KK.psi_zero_line_k] at h4
  rw [h1.unique h2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, add_comm]
/- English proof (translation)
Use `set v := X * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ`. Establish `hΨ : d.dd.rho d.B.ψ v Φ ∈ d.sch` using `GlobalTheory.HeisSchA.schr_mem_schA _ d.ok.good.std _ Φ hΦ`. Establish `e : (fun t : ℝ => d.T (d.dd.rho d.B.ψ (realAd F t • u) Φ) X) = fun t : ℝ => d.B.ψ (realAd F t * _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d v u) * d.l (d.dd.rho d.B.ψ (realAd F t • u) (d.dd.rho d.B.ψ v Φ))`. Use function extensionality and compare the values at `t`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T]`.

Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KK.rho_comm_k, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_smul_right_k, map_smul, smul_eq_mul]`. Rewrite using `[e]`. Establish `h4` using `(_root_.PositivityTheory.SiegelWeilFormula.KK.psi_line_deriv_k (d := d) (_root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d v u)).mul (_root_.PositivityTheory.SiegelWeilFormula.KK.l_D_k hΨ hu ha)`. Rewrite `h4` using `[_root_.PositivityTheory.SiegelWeilFormula.KK.schr_zero_at_k, _root_.PositivityTheory.SiegelWeilFormula.KK.psi_zero_line_k]`. Use `h4.congr_deriv ?_` and prove the remaining obligations.

Rewrite using `[show d.T (Box.D (d.dd.e u) Φ) X = d.l (d.dd.rho d.B.ψ v (Box.D (d.dd.e u) Φ)) from rfl, _root_.PositivityTheory.SiegelWeilFormula.KK.rho_D_k hΦ hu, map_add, map_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem T_D_k {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u)
    (ha : Box.nf (d.dd.e u).1 ≠ 0) (X : Mx F E d.m d.n) :
    HasDerivAt (fun t : ℝ => d.T (d.dd.rho d.B.ψ (realAd F t • u) Φ) X) (d.T (Box.D (d.dd.e u) Φ) X) 0 := by
  set v := X * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ
  have hΨ : d.dd.rho d.B.ψ v Φ ∈ d.sch := GlobalTheory.HeisSchA.schr_mem_schA _ d.ok.good.std _ Φ hΦ
  have e : (fun t : ℝ => d.T (d.dd.rho d.B.ψ (realAd F t • u) Φ) X) =
      fun t : ℝ => d.B.ψ (realAd F t * _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d v u) * d.l (d.dd.rho d.B.ψ (realAd F t • u) (d.dd.rho d.B.ψ v Φ)) := by
    funext t
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T]
    rw [_root_.PositivityTheory.SiegelWeilFormula.KK.rho_comm_k, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_smul_right_k, map_smul, smul_eq_mul]
  rw [e]
  have h4 := (_root_.PositivityTheory.SiegelWeilFormula.KK.psi_line_deriv_k (d := d) (_root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d v u)).mul (_root_.PositivityTheory.SiegelWeilFormula.KK.l_D_k hΨ hu ha)
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.schr_zero_at_k, _root_.PositivityTheory.SiegelWeilFormula.KK.psi_zero_line_k] at h4
  refine h4.congr_deriv ?_
  rw [show d.T (Box.D (d.dd.e u) Φ) X = d.l (d.dd.rho d.B.ψ v (Box.D (d.dd.e u) Φ)) from rfl, _root_.PositivityTheory.SiegelWeilFormula.KK.rho_D_k hΦ hu, map_add,
    map_smul, smul_eq_mul]
  ring
/- English proof (translation)
Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KK.sp_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_eq_k, map_add, Prod.fst_add, Prod.snd_add, dotProduct_add, add_dotProduct]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sp_add_right_k (x y y' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d x (y + y') = _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d x y + _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d x y' := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.sp_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_eq_k, map_add, Prod.fst_add, Prod.snd_add, dotProduct_add, add_dotProduct]
  ring
/- English proof (translation)
Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KK.sp_anti_k, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_smul_right_k, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_anti_k y x]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sp_smul_left_k (c : AF F) (x y : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d (c • x) y = c * _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d x y := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.sp_anti_k, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_smul_right_k, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_anti_k y x]
  ring
/- English proof (translation)
Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k, Matrix.add_mul, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_add_right_k, evI_add', map_add]`.
-/
theorem mZ_add_k (Z Z' X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d (Z + Z') X = _root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d Z X + _root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d Z' X := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k, Matrix.add_mul, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_add_right_k, evI_add', map_add]
/- English proof (translation)
Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, _root_.PositivityTheory.SiegelWeilFormula.KK.rho_add_fn_k, map_add]`.
-/
theorem td_T_add_k (Φ Ψ : d.Fn) (X : Mx F E d.m d.n) : d.T (Φ + Ψ) X = d.T Φ X + d.T Ψ X := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, _root_.PositivityTheory.SiegelWeilFormula.KK.rho_add_fn_k, map_add]
/- English proof (translation)
Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, _root_.PositivityTheory.SiegelWeilFormula.KK.rho_smul_fn_k, map_smul, smul_eq_mul]`.
-/
theorem T_smul_k (c : ℂ) (Φ : d.Fn) (X : Mx F E d.m d.n) : d.T (c • Φ) X = c * d.T Φ X := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, _root_.PositivityTheory.SiegelWeilFormula.KK.rho_smul_fn_k, map_smul, smul_eq_mul]
/- English proof (translation)
Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, _root_.PositivityTheory.SiegelWeilFormula.KK.rho_zero_fn_k, map_zero]`.
-/
theorem T_zero_k (X : Mx F E d.m d.n) : d.T 0 X = 0 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, _root_.PositivityTheory.SiegelWeilFormula.KK.rho_zero_fn_k, map_zero]
/- English proof (translation)
Establish `h` using `Box.D_add_left (0 : (d.κ → AF F) × (d.κ → AF F)) 0 Φ`. Rewrite `h` using `[add_zero]`. Simplify using `using h`.
-/
theorem D_zero_k (Φ : d.Fn) : Box.D (0 : (d.κ → AF F) × (d.κ → AF F)) Φ = 0 := by
  have h := Box.D_add_left (0 : (d.κ → AF F) × (d.κ → AF F)) 0 Φ
  rw [add_zero] at h
  simpa using h
/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 (congrFun h0 i)) ?_` and prove the remaining obligations. Conclude with `Dense.snd_eq_zero hy i`.
-/
theorem vec_eq_zero_k {y : d.κ → AF F} (hy : At (evI F) y) (h0 : Box.nf y = 0) : y = 0 := by
  funext i
  refine Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 (congrFun h0 i)) ?_
  exact Dense.snd_eq_zero hy i
/- English proof (translation)
Introduce `c hc` and use `congrArg Prod.fst (_root_.PositivityTheory.SiegelWeilFormula.KK.at_e'_k hu c hc)`.
-/
theorem at_fst_k {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u) : At (evI F) (d.dd.e u).1 :=
  fun c hc => congrArg Prod.fst (_root_.PositivityTheory.SiegelWeilFormula.KK.at_e'_k hu c hc)
/- English proof (translation)
Introduce `c hc` and use `congrArg Prod.snd (_root_.PositivityTheory.SiegelWeilFormula.KK.at_e'_k hu c hc)`.
-/
theorem at_snd_k {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u) : At (evI F) (d.dd.e u).2 :=
  fun c hc => congrArg Prod.snd (_root_.PositivityTheory.SiegelWeilFormula.KK.at_e'_k hu c hc)
/- English proof (translation)
Establish `e : d.dd.e u = 0` using `Prod.ext (_root_.PositivityTheory.SiegelWeilFormula.KK.vec_eq_zero_k (_root_.PositivityTheory.SiegelWeilFormula.KK.at_fst_k hu) h1) (_root_.PositivityTheory.SiegelWeilFormula.KK.vec_eq_zero_k (_root_.PositivityTheory.SiegelWeilFormula.KK.at_snd_k hu) h2)`. Rewrite using `[← d.dd.e.map_eq_zero_iff]`. Conclude with `e`.
-/
theorem eq_zero_of_nf_k {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u)
    (h1 : Box.nf (d.dd.e u).1 = 0) (h2 : Box.nf (d.dd.e u).2 = 0) : u = 0 := by
  have e : d.dd.e u = 0 := Prod.ext (_root_.PositivityTheory.SiegelWeilFormula.KK.vec_eq_zero_k (_root_.PositivityTheory.SiegelWeilFormula.KK.at_fst_k hu) h1) (_root_.PositivityTheory.SiegelWeilFormula.KK.vec_eq_zero_k (_root_.PositivityTheory.SiegelWeilFormula.KK.at_snd_k hu) h2)
  rw [← d.dd.e.map_eq_zero_iff]
  exact e
/- English proof (translation)
Use `⟨d.dd.e.symm (Dense.pt ξ 0, 0), fun s hs => ?_, LinearEquiv.apply_symm_apply _ _⟩` and prove the remaining obligations. Rewrite using `[← map_smul, LinearEquiv.map_eq_zero_iff]`. Use `Prod.ext ?_ (by simp)` and prove the remaining obligations. Conclude with `Box.at_pt ξ s hs`.
-/
theorem exists_at'_k (ξ : d.κ → mixedEmbedding.mixedSpace F) :
    ∃ v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E), At (evI F) v ∧ d.dd.e v = (Dense.pt ξ 0, 0) := by
  refine ⟨d.dd.e.symm (Dense.pt ξ 0, 0), fun s hs => ?_, LinearEquiv.apply_symm_apply _ _⟩
  rw [← map_smul, LinearEquiv.map_eq_zero_iff]
  refine Prod.ext ?_ (by simp)
  exact Box.at_pt ξ s hs
/- English proof (translation)
Introduce `c hc` and use `by rw [← Matrix.smul_mul, hZ c hc, Matrix.zero_mul]`.
-/
theorem td_at_mul_k {p : Type} [Fintype p] {Z : Matrix (Fin d.m) p (AE F E)} (hZ : At (evI F) Z) {q : Type}
    (N : Matrix p q (AE F E)) : At (evI F) (Z * N) := fun c hc => by rw [← Matrix.smul_mul, hZ c hc, Matrix.zero_mul]
/- English proof (translation)
Apply the tactic sequence `ext (i | i) j <;> by_cases h : i = j <;> simp [incM, diagCols, Matrix.one_apply, h]`.
-/
theorem incM_diagCols_k : incM F (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) = _root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d := by
  ext (i | i) j <;> by_cases h : i = j <;> simp [incM, diagCols, Matrix.one_apply, h]
/- English proof (translation)
Take `⟨t, ht⟩` from `d.ok.frame.2`. Use `set W := u * (incM F (d.b⁻¹).1)ᵀ with hW`. Establish `hWa : At (evI F) W` using `_root_.PositivityTheory.SiegelWeilFormula.KK.td_at_mul_k hu _`. Use `⟨W.toCols₁ * (incM F t.1)ᵀ, W.toCols₂, fun c hc => ?_, fun c hc => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.smul_mul]`.

Establish `: c • W.toCols₁ = 0`. Use extensionality with `i j`. Conclude with `congrFun₂ (hWa c hc) i (Sum.inl j)`. Rewrite using `[this, Matrix.zero_mul]`. Use extensionality with `i j`.

Conclude with `congrFun₂ (hWa c hc) i (Sum.inr j)`. Establish `e1 : u = W * (incM F d.b.1)ᵀ`. Rewrite using `[hW, Matrix.mul_assoc, ← Matrix.transpose_mul, ← incM_mul', ← Units.val_mul, mul_inv_cancel]`. Use extensionality with `i j`. Simplify using `[incM]`.

Establish `e2 : incM F d.b.1 = Matrix.fromCols (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d * incM F t.1) (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)`. Rewrite using `[← _root_.PositivityTheory.SiegelWeilFormula.KK.incM_diagCols_k, ← incM_mul']`. Establish `hb : d.b.1 = Matrix.fromCols (diagCols (Fin d.n) * t.1) d.b.1.toCols₂`. Use `(Matrix.fromCols_toCols d.b.1).symm using 2` and compare the differences between its conclusion and the goal. Conclude with `ht.symm`.

Use `conv_lhs => rw [hb]`. Apply the tactic sequence `ext i (j | j) <;> rfl`. Rewrite using `[e1, e2, Matrix.transpose_fromCols, ← Matrix.fromCols_toCols W, Matrix.fromCols_mul_fromRows, Matrix.transpose_mul, Matrix.mul_assoc]`. Both sides reduce to the same expression.
-/
theorem split_arch_k {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u) :
    ∃ Z₁ Z₂ : Mx F E d.m d.n, At (evI F) Z₁ ∧ At (evI F) Z₂ ∧ u = Z₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ + Z₂ * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ := by
  obtain ⟨t, ht⟩ := d.ok.frame.2
  set W := u * (incM F (d.b⁻¹).1)ᵀ with hW
  have hWa : At (evI F) W := _root_.PositivityTheory.SiegelWeilFormula.KK.td_at_mul_k hu _
  refine ⟨W.toCols₁ * (incM F t.1)ᵀ, W.toCols₂, fun c hc => ?_, fun c hc => ?_, ?_⟩
  · rw [← Matrix.smul_mul]
    have : c • W.toCols₁ = 0 := by
      ext i j
      exact congrFun₂ (hWa c hc) i (Sum.inl j)
    rw [this, Matrix.zero_mul]
  · ext i j
    exact congrFun₂ (hWa c hc) i (Sum.inr j)
  · have e1 : u = W * (incM F d.b.1)ᵀ := by
      rw [hW, Matrix.mul_assoc, ← Matrix.transpose_mul, ← incM_mul', ← Units.val_mul, mul_inv_cancel]
      ext i j
      simp [incM]
    have e2 : incM F d.b.1 = Matrix.fromCols (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d * incM F t.1) (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d) := by
      rw [← _root_.PositivityTheory.SiegelWeilFormula.KK.incM_diagCols_k, ← incM_mul']
      have hb : d.b.1 = Matrix.fromCols (diagCols (Fin d.n) * t.1) d.b.1.toCols₂ := by
        convert (Matrix.fromCols_toCols d.b.1).symm using 2
        exact ht.symm
      conv_lhs => rw [hb]
      ext i (j | j) <;> rfl
    rw [e1, e2, Matrix.transpose_fromCols, ← Matrix.fromCols_toCols W, Matrix.fromCols_mul_fromRows, Matrix.transpose_mul,
      Matrix.mul_assoc]
    rfl
/- English proof (translation)
Establish `e : incM F (d.b⁻¹).1.toRows₂ * _root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d = 1`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns, ← incM_mul']`. Establish `: (d.b⁻¹).1.toRows₂ * d.b.1.toCols₂ = 1`. Use extensionality with `i j`. Use `congrFun₂ (show (d.b⁻¹).1 * d.b.1 = 1 by simp) (Sum.inr i) (Sum.inr j)` as an intermediate fact.

Simplify `this` using `[Matrix.mul_apply, Matrix.toRows₂, Matrix.toCols₂, Matrix.one_apply]`. Rewrite using `[this]`. Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [incM, Matrix.one_apply, h]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem secondColumns_mul_injective {Z : Mx F E d.m d.n} (h : Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ = 0) : Z = 0 := by
  have e : incM F (d.b⁻¹).1.toRows₂ * _root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d = 1 := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns, ← incM_mul']
    have : (d.b⁻¹).1.toRows₂ * d.b.1.toCols₂ = 1 := by
      ext i j
      have := congrFun₂ (show (d.b⁻¹).1 * d.b.1 = 1 by simp) (Sum.inr i) (Sum.inr j)
      simpa [Matrix.mul_apply, Matrix.toRows₂, Matrix.toCols₂, Matrix.one_apply] using this
    rw [this]
    ext i j
    by_cases h : i = j <;> simp [incM, Matrix.one_apply, h]
  calc Z = Z * (incM F (d.b⁻¹).1.toRows₂ * _root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ := by rw [e, Matrix.transpose_one, Matrix.mul_one]
    _ = Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ * (incM F (d.b⁻¹).1.toRows₂)ᵀ := by rw [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 0 := by rw [h, Matrix.zero_mul]
/- English proof (translation)
Use `set c := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F s)`. Establish `e : ∀ t : ℝ, d.B.ψ (realAd F t * (realAd F t * s)) = Complex.exp (-(2 * Real.pi * Complex.I) * ((t * (t * c) : ℝ) : ℂ))` using `fun t => by`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KK.psi_line_k, tr_realAd_mul]`. Simplify using `only [e]`. Establish `h1 : HasDerivAt (fun t : ℝ => ((t * (t * c) : ℝ) : ℂ)) 0 0`.

Use `((hasDerivAt_id (0 : ℝ)).mul ((hasDerivAt_id (0 : ℝ)).mul_const c)).ofReal_comp` as an intermediate fact. Simplify using `using this`. Establish `h2` using `(h1.const_mul (-(2 * Real.pi * Complex.I))).cexp`. Simplify using `using h2`.
-/
theorem hasDerivAt_character_quadratic (s : AF F) : HasDerivAt (fun t : ℝ => d.B.ψ (realAd F t * (realAd F t * s))) 0 0 := by
  set c := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F s)
  have e : ∀ t : ℝ, d.B.ψ (realAd F t * (realAd F t * s)) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * (t * c) : ℝ) : ℂ)) := fun t => by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KK.psi_line_k, tr_realAd_mul]
  simp only [e]
  have h1 : HasDerivAt (fun t : ℝ => ((t * (t * c) : ℝ) : ℂ)) 0 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul ((hasDerivAt_id (0 : ℝ)).mul_const c)).ofReal_comp
    simpa using this
  have h2 := (h1.const_mul (-(2 * Real.pi * Complex.I))).cexp
  simpa using h2
/- English proof (translation)
Rewrite using `[map_add, Prod.fst_add, Box.nf_add]`.
-/
theorem nfe_add_k (u v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    Box.nf (d.dd.e (u + v)).1 = Box.nf (d.dd.e u).1 + Box.nf (d.dd.e v).1 := by
  rw [map_add, Prod.fst_add, Box.nf_add]
/- English proof (translation)
Introduce `c hc` and use `by rw [smul_add, hu c hc, hv c hc, add_zero]`.
-/
theorem at_add'_k {u v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u) (hv : At (evI F) v) :
    At (evI F) (u + v) := fun c hc => by rw [smul_add, hu c hc, hv c hc, add_zero]
/- English proof (translation)
Introduce `c hc` and use `by rw [smul_add, hZ c hc, hZ' c hc, add_zero]`.
-/
theorem atZ_add_k {Z Z' : Mx F E d.m d.n} (hZ : At (evI F) Z) (hZ' : At (evI F) Z') : At (evI F) (Z + Z') :=
  fun c hc => by rw [smul_add, hZ c hc, hZ' c hc, add_zero]
/- English proof (translation)
Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KK.sp_eq_k, map_zero]`. Simplify using the standard rewrite rules.
-/
theorem sp_zero_right_k (x : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d x 0 = 0 := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.sp_eq_k, map_zero]; simp
/- English proof (translation)
Rewrite using `[dotProduct, Dense.evI_sum]`. Simplify using `only [Dense.evI_mul]`.
-/
theorem evI_dot_k (a b : d.κ → AF F) : evI F (a ⬝ᵥ b) = ∑ i, evI F (a i) * evI F (b i) := by
  rw [dotProduct, Dense.evI_sum]
  simp only [Dense.evI_mul]
/- English proof (translation)
Establish `h1` using `_root_.PositivityTheory.SiegelWeilFormula.KK.T_D_k hΦ (_root_.PositivityTheory.SiegelWeilFormula.KK.td_at_mul_k hZ _) ha X`. Establish `h2 : HasDerivAt (fun t : ℝ => d.T (d.dd.rho d.B.ψ (realAd F t • (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ) X) ((-(2 * Real.pi * Complex.I) * (_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d Z X : ℂ)) * d.T Φ X) 0`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.KK.T_rho_dg_k hΦ]`. Conclude with `(_root_.PositivityTheory.SiegelWeilFormula.KK.psi_line_deriv_k _).mul_const _`. Conclude with `h1.unique h2`.
-/
theorem T_D_dg_ne_k {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {Z : Mx F E d.m d.n} (hZ : At (evI F) Z)
    (ha : Box.nf (d.dd.e (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)).1 ≠ 0) (X : Mx F E d.m d.n) :
    d.T (Box.D (d.dd.e (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ) X = (-(2 * Real.pi * Complex.I) * (_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d Z X : ℂ)) * d.T Φ X := by
  have h1 := _root_.PositivityTheory.SiegelWeilFormula.KK.T_D_k hΦ (_root_.PositivityTheory.SiegelWeilFormula.KK.td_at_mul_k hZ _) ha X
  have h2 : HasDerivAt (fun t : ℝ => d.T (d.dd.rho d.B.ψ (realAd F t • (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ) X)
      ((-(2 * Real.pi * Complex.I) * (_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d Z X : ℂ)) * d.T Φ X) 0 := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KK.T_rho_dg_k hΦ]
    exact (_root_.PositivityTheory.SiegelWeilFormula.KK.psi_line_deriv_k _).mul_const _
  exact h1.unique h2
/- English proof (translation)
Establish `h1` using `_root_.PositivityTheory.SiegelWeilFormula.KK.T_D_k hΦ (_root_.PositivityTheory.SiegelWeilFormula.KK.td_at_mul_k hZ _) ha X`. Simplify `h1` using `only [_root_.PositivityTheory.SiegelWeilFormula.KK.weilAction_secondColumns_translate]`.
-/
theorem hasDerivAt_translate_nonzero {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {Z : Mx F E d.m d.n} (hZ : At (evI F) Z)
    (ha : Box.nf (d.dd.e (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)).1 ≠ 0) (X : Mx F E d.m d.n) :
    HasDerivAt (fun t : ℝ => d.T Φ (X + realAd F t • Z)) (d.T (Box.D (d.dd.e (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)) Φ) X) 0 := by
  have h1 := _root_.PositivityTheory.SiegelWeilFormula.KK.T_D_k hΦ (_root_.PositivityTheory.SiegelWeilFormula.KK.td_at_mul_k hZ _) ha X
  simpa only [_root_.PositivityTheory.SiegelWeilFormula.KK.weilAction_secondColumns_translate] using h1
/- English proof (translation)
The claim follows from `GlobalTheory.HeisSchA.schr_mem_schA _ d.ok.good.std _ Φ hΦ`.
-/
theorem rho_mem_k {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    d.dd.rho d.B.ψ v Φ ∈ d.sch := GlobalTheory.HeisSchA.schr_mem_schA _ d.ok.good.std _ Φ hΦ
/- English proof (translation)
Take `⟨v, hv, ev⟩` from `_root_.PositivityTheory.SiegelWeilFormula.KK.exists_at'_k (d := d) ξ`. Take `⟨Z₁, Z₂, h1, h2, rfl⟩` from `_root_.PositivityTheory.SiegelWeilFormula.KK.split_arch_k hv`. Establish `: Box.nf (d.dd.e (Z₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ + Z₂ * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)).1 = ξ` using `by rw [ev]; exact Dense.evI_pt ξ 0`. Rewrite using `[← this, _root_.PositivityTheory.SiegelWeilFormula.KK.nfe_add_k, hB Z₁ h1, hC Z₂ h2, add_zero]`.
-/
theorem all_zero_k (hB : ∀ Z₀ : Mx F E d.m d.n, At (evI F) Z₀ → Box.nf (d.dd.e (Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)).1 = 0)
    (hC : ∀ Z₀ : Mx F E d.m d.n, At (evI F) Z₀ → Box.nf (d.dd.e (Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)).1 = 0)
    (ξ : d.κ → mixedEmbedding.mixedSpace F) : ξ = 0 := by
  obtain ⟨v, hv, ev⟩ := _root_.PositivityTheory.SiegelWeilFormula.KK.exists_at'_k (d := d) ξ
  obtain ⟨Z₁, Z₂, h1, h2, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.KK.split_arch_k hv
  have : Box.nf (d.dd.e (Z₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ + Z₂ * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)).1 = ξ := by rw [ev]; exact Dense.evI_pt ξ 0
  rw [← this, _root_.PositivityTheory.SiegelWeilFormula.KK.nfe_add_k, hB Z₁ h1, hC Z₂ h2, add_zero]
/- English proof (translation)
Distinguish the cases in `ha : Box.nf (d.dd.e (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)).1 = 0`. Use `swap`. Conclude with `_root_.PositivityTheory.SiegelWeilFormula.KK.T_D_dg_ne_k hΦ hZ ha X`. Distinguish the cases in `hB : ∃ Z₀ : Mx F E d.m d.n, At (evI F) Z₀ ∧ Box.nf (d.dd.e (Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)).1 ≠ 0`. Take `⟨Z₀, h0, h0'⟩` from `hB`.

Establish `hs : Box.nf (d.dd.e ((Z + Z₀) * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)).1 ≠ 0` using `by rwa [Matrix.add_mul, _root_.PositivityTheory.SiegelWeilFormula.KK.nfe_add_k, ha, zero_add]`. Establish `e1` using `_root_.PositivityTheory.SiegelWeilFormula.KK.T_D_dg_ne_k hΦ (_root_.PositivityTheory.SiegelWeilFormula.KK.atZ_add_k hZ h0) hs X`. Establish `e2` using `_root_.PositivityTheory.SiegelWeilFormula.KK.T_D_dg_ne_k hΦ h0 h0' X`. Rewrite `e1` using `[Matrix.add_mul, map_add, Box.D_add_left, _root_.PositivityTheory.SiegelWeilFormula.KK.td_T_add_k, e2, _root_.PositivityTheory.SiegelWeilFormula.KK.mZ_add_k]`. Move the coercions through the operations in `at e1`.

Take the linear combination `e1`. Distinguish the cases in `hC : ∃ Z₀ : Mx F E d.m d.n, At (evI F) Z₀ ∧ Box.nf (d.dd.e (Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)).1 ≠ 0`. Take `⟨Z₀, h0, h0'⟩` from `hC`. Establish `hu` using `_root_.PositivityTheory.SiegelWeilFormula.KK.td_at_mul_k hZ (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ`. Establish `hu₀` using `_root_.PositivityTheory.SiegelWeilFormula.KK.td_at_mul_k h0 (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ`.

Establish `hs : Box.nf (d.dd.e (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ + Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)).1 ≠ 0` using `by rwa [_root_.PositivityTheory.SiegelWeilFormula.KK.nfe_add_k, ha, zero_add]`. Establish `h1` using `_root_.PositivityTheory.SiegelWeilFormula.KK.T_D_k hΦ (_root_.PositivityTheory.SiegelWeilFormula.KK.at_add'_k hu hu₀) hs X`. Establish `h0d` using `_root_.PositivityTheory.SiegelWeilFormula.KK.hasDerivAt_translate_nonzero hΦ h0 h0' X`. Establish `key : ∀ t : ℝ, d.B.ψ (realAd F t * (realAd F t * (⅟(2 : AF F) * _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ) (Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)))) * d.T (d.dd.rho d.B.ψ (r …` using `fun t => by`. Rewrite using `[← _root_.PositivityTheory.SiegelWeilFormula.KK.weilAction_secondColumns_translate Φ Z₀ t X, ← _root_.PositivityTheory.SiegelWeilFormula.KK.T_rho_dg_k (_root_.PositivityTheory.SiegelWeilFormula.KK.rho_mem_k hΦ _) Z t X, _root_.PositivityTheory.SiegelWeilFormula.KK.rho_rho_k, _roo …`.

Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `hL` using `(_root_.PositivityTheory.SiegelWeilFormula.KK.hasDerivAt_character_quadratic (d := d) (⅟(2 : AF F) * _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ) (Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameCol …`. Establish `hR` using `(_root_.PositivityTheory.SiegelWeilFormula.KK.psi_line_deriv_k (d := d) (_root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d (X * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ) (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ))).mul h0d`. Establish `hL' : HasDerivAt (fun t : ℝ => d.B.ψ (realAd F t * _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d (X * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ) (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) * d.T Φ (X + realAd F t • Z₀)) (0 * d.T …`.

Rewrite using `[← funext key]`. Conclude with `hL`. Establish `E` using `hL'.unique hR`. Rewrite `E` using `[_root_.PositivityTheory.SiegelWeilFormula.KK.schr_zero_at_k]`. Simplify using `only [td_realAd_zero, zero_mul, AddChar.map_zero_eq_one, zero_smul, add_zero, one_mul, zero_add] at E`.

Rewrite `E` using `[map_add, Box.D_add_left, _root_.PositivityTheory.SiegelWeilFormula.KK.td_T_add_k]`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k]`. Take the linear combination `E`. Use `push_neg at hB hC`. Establish `hz` using `_root_.PositivityTheory.SiegelWeilFormula.KK.all_zero_k (d := d) hB hC`.

Establish `hu` using `_root_.PositivityTheory.SiegelWeilFormula.KK.td_at_mul_k hZ (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ`. Establish `hu0 : Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ = 0` using `_root_.PositivityTheory.SiegelWeilFormula.KK.eq_zero_of_nf_k hu ha (hz _)`. Establish `hm : _root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d Z X = 0`. Establish `e0 : evI F (0 : AF F) = 0` using `map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k, hu0, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_zero_right_k, e0, map_zero]`.

Rewrite using `[hm, hu0, map_zero, _root_.PositivityTheory.SiegelWeilFormula.KK.D_zero_k, _root_.PositivityTheory.SiegelWeilFormula.KK.T_zero_k]`. Simplify using the standard rewrite rules.
-/
theorem T_D_dg_k {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {Z : Mx F E d.m d.n} (hZ : At (evI F) Z) (X : Mx F E d.m d.n) :
    d.T (Box.D (d.dd.e (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ) X = (-(2 * Real.pi * Complex.I) * (_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d Z X : ℂ)) * d.T Φ X := by
  by_cases ha : Box.nf (d.dd.e (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)).1 = 0
  swap
  · exact _root_.PositivityTheory.SiegelWeilFormula.KK.T_D_dg_ne_k hΦ hZ ha X
  by_cases hB : ∃ Z₀ : Mx F E d.m d.n, At (evI F) Z₀ ∧ Box.nf (d.dd.e (Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)).1 ≠ 0
  · obtain ⟨Z₀, h0, h0'⟩ := hB
    have hs : Box.nf (d.dd.e ((Z + Z₀) * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)).1 ≠ 0 := by rwa [Matrix.add_mul, _root_.PositivityTheory.SiegelWeilFormula.KK.nfe_add_k, ha, zero_add]
    have e1 := _root_.PositivityTheory.SiegelWeilFormula.KK.T_D_dg_ne_k hΦ (_root_.PositivityTheory.SiegelWeilFormula.KK.atZ_add_k hZ h0) hs X
    have e2 := _root_.PositivityTheory.SiegelWeilFormula.KK.T_D_dg_ne_k hΦ h0 h0' X
    rw [Matrix.add_mul, map_add, Box.D_add_left, _root_.PositivityTheory.SiegelWeilFormula.KK.td_T_add_k, e2, _root_.PositivityTheory.SiegelWeilFormula.KK.mZ_add_k] at e1
    push_cast at e1
    linear_combination e1
  by_cases hC : ∃ Z₀ : Mx F E d.m d.n, At (evI F) Z₀ ∧ Box.nf (d.dd.e (Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)).1 ≠ 0
  · obtain ⟨Z₀, h0, h0'⟩ := hC
    have hu := _root_.PositivityTheory.SiegelWeilFormula.KK.td_at_mul_k hZ (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ
    have hu₀ := _root_.PositivityTheory.SiegelWeilFormula.KK.td_at_mul_k h0 (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ
    have hs : Box.nf (d.dd.e (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ + Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)).1 ≠ 0 := by rwa [_root_.PositivityTheory.SiegelWeilFormula.KK.nfe_add_k, ha, zero_add]
    have h1 := _root_.PositivityTheory.SiegelWeilFormula.KK.T_D_k hΦ (_root_.PositivityTheory.SiegelWeilFormula.KK.at_add'_k hu hu₀) hs X
    have h0d := _root_.PositivityTheory.SiegelWeilFormula.KK.hasDerivAt_translate_nonzero hΦ h0 h0' X
    have key : ∀ t : ℝ, d.B.ψ (realAd F t * (realAd F t * (⅟(2 : AF F) * _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ) (Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)))) *
        d.T (d.dd.rho d.B.ψ (realAd F t • (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ + Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)) Φ) X =
          d.B.ψ (realAd F t * _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d (X * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ) (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) * d.T Φ (X + realAd F t • Z₀) := fun t => by
      rw [← _root_.PositivityTheory.SiegelWeilFormula.KK.weilAction_secondColumns_translate Φ Z₀ t X, ← _root_.PositivityTheory.SiegelWeilFormula.KK.T_rho_dg_k (_root_.PositivityTheory.SiegelWeilFormula.KK.rho_mem_k hΦ _) Z t X, _root_.PositivityTheory.SiegelWeilFormula.KK.rho_rho_k, _root_.PositivityTheory.SiegelWeilFormula.KK.T_smul_k, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_smul_left_k, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_smul_right_k, smul_add]
      congr 2
      ring
    have hL := (_root_.PositivityTheory.SiegelWeilFormula.KK.hasDerivAt_character_quadratic (d := d) (⅟(2 : AF F) * _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ) (Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ))).mul h1
    have hR := (_root_.PositivityTheory.SiegelWeilFormula.KK.psi_line_deriv_k (d := d) (_root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d (X * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ) (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ))).mul h0d
    have hL' : HasDerivAt (fun t : ℝ => d.B.ψ (realAd F t * _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d (X * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ) (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) * d.T Φ (X + realAd F t • Z₀))
        (0 * d.T (d.dd.rho d.B.ψ (realAd F 0 • (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ + Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)) Φ) X +
          d.B.ψ (realAd F 0 * (realAd F 0 * (⅟(2 : AF F) * _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ) (Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)))) *
            d.T (Box.D (d.dd.e (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ + Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)) Φ) X) 0 := by
      rw [← funext key]; exact hL
    have E := hL'.unique hR
    rw [_root_.PositivityTheory.SiegelWeilFormula.KK.schr_zero_at_k] at E
    simp only [td_realAd_zero, zero_mul, AddChar.map_zero_eq_one, zero_smul, add_zero, one_mul, zero_add] at E
    rw [map_add, Box.D_add_left, _root_.PositivityTheory.SiegelWeilFormula.KK.td_T_add_k] at E
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k]
    linear_combination E
  push_neg at hB hC
  have hz := _root_.PositivityTheory.SiegelWeilFormula.KK.all_zero_k (d := d) hB hC
  have hu := _root_.PositivityTheory.SiegelWeilFormula.KK.td_at_mul_k hZ (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ
  have hu0 : Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ = 0 := _root_.PositivityTheory.SiegelWeilFormula.KK.eq_zero_of_nf_k hu ha (hz _)
  have hm : _root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d Z X = 0 := by
    have e0 : evI F (0 : AF F) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k, hu0, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_zero_right_k, e0, map_zero]
  rw [hm, hu0, map_zero, _root_.PositivityTheory.SiegelWeilFormula.KK.D_zero_k, _root_.PositivityTheory.SiegelWeilFormula.KK.T_zero_k]
  simp
/- English proof (translation)
Distinguish the cases in `ha : Box.nf (d.dd.e (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)).1 = 0`. Use `swap`. Conclude with `_root_.PositivityTheory.SiegelWeilFormula.KK.hasDerivAt_translate_nonzero hΦ hZ ha X`. Establish `hu` using `_root_.PositivityTheory.SiegelWeilFormula.KK.td_at_mul_k hZ (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ`. Distinguish the cases in `hB : ∃ Z₀ : Mx F E d.m d.n, At (evI F) Z₀ ∧ Box.nf (d.dd.e (Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)).1 ≠ 0`.

Take `⟨Z₀, h0, h0'⟩` from `hB`. Establish `hu₀` using `_root_.PositivityTheory.SiegelWeilFormula.KK.td_at_mul_k h0 (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ`. Establish `hs : Box.nf (d.dd.e (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ + Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)).1 ≠ 0` using `by rwa [_root_.PositivityTheory.SiegelWeilFormula.KK.nfe_add_k, ha, zero_add]`. Establish `h1` using `_root_.PositivityTheory.SiegelWeilFormula.KK.T_D_k hΦ (_root_.PositivityTheory.SiegelWeilFormula.KK.at_add'_k hu hu₀) hs X`. Establish `key : ∀ t : ℝ, d.T Φ (X + realAd F t • Z) = d.B.ψ (realAd F t * -_root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d (X * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ) (Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) * (d.B.ψ (realAd F t * (r …`.

Introduce `t`. Establish `k1 : d.B.ψ (realAd F t * (realAd F t * (⅟(2 : AF F) * _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d (Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ) (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)))) * d.T (d.dd.rho d.B.ψ (realAd F t …`. Rewrite using `[← _root_.PositivityTheory.SiegelWeilFormula.KK.weilAction_secondColumns_translate Φ Z t X, ← _root_.PositivityTheory.SiegelWeilFormula.KK.T_rho_dg_k (_root_.PositivityTheory.SiegelWeilFormula.KK.rho_mem_k hΦ _) Z₀ t X, _root_.PositivityTheory.SiegelWeilFormula.KK.rho_rho_k, _roo …`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[k1, ← mul_assoc, ← AddChar.map_add_eq_mul, mul_neg, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]`. Establish `hR` using `(_root_.PositivityTheory.SiegelWeilFormula.KK.psi_line_deriv_k (d := d) (-_root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d (X * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ) (Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ))).mul ((_root_.Po …`. Rewrite using `[funext key]`. Use `hR.congr_deriv ?_` and prove the remaining obligations. Establish `e2` using `_root_.PositivityTheory.SiegelWeilFormula.KK.T_D_dg_ne_k hΦ h0 h0' X`.

Simplify using `only [Pi.mul_apply]`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KK.schr_zero_at_k]`. Simplify using `only [td_realAd_zero, zero_mul, AddChar.map_zero_eq_one, one_mul, zero_add]`. Rewrite using `[map_add, Box.D_add_left, _root_.PositivityTheory.SiegelWeilFormula.KK.td_T_add_k, e2, evI_neg', map_neg]`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `push_neg at hB`. Establish `hsp : ∀ v, At (evI F) v → _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ) v = 0`. Introduce `v hv`.

Take `⟨Z₁, Z₂, h1, h2, rfl⟩` from `_root_.PositivityTheory.SiegelWeilFormula.KK.split_arch_k hv`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KK.sp_add_right_k, _root_.PositivityTheory.SiegelWeilFormula.KK.symplectic_secondColumns_isotropic, add_zero, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KK.vec_eq_zero_k (_root_.Positi …`. Simplify using the standard rewrite rules. Establish `h2 : Box.nf (d.dd.e (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)).2 = 0`. Use function extensionality and compare the values at `j`.

Take `⟨v, hv, ev⟩` from `_root_.PositivityTheory.SiegelWeilFormula.KK.exists_at'_k (d := d) (Pi.single j 1)`. Use `hsp v hv` as an intermediate fact. Rewrite `this` using `[_root_.PositivityTheory.SiegelWeilFormula.KK.sp_eq_k, ev, _root_.PositivityTheory.SiegelWeilFormula.KK.vec_eq_zero_k (_root_.PositivityTheory.SiegelWeilFormula.KK.at_fst_k hu) ha]`. Simplify using `only [zero_dotProduct, dotProduct_zero, zero_sub, neg_eq_zero] at this`. Establish `e3` using `congrArg (evI F) this`.

Rewrite `e3` using `[_root_.PositivityTheory.SiegelWeilFormula.KK.evI_dot_k]`. Establish `e4 : ∀ i, evI F (Dense.pt (Pi.single j (1 : mixedEmbedding.mixedSpace F)) 0 i) = (Pi.single j (1 : mixedEmbedding.mixedSpace F) : d.κ → mixedEmbedding.mixedSpace F) i` using `fun i => congrFun (Dense.evI_pt (Pi.single j (1 : mixedEmbedding.mixedSpace F)) 0) i`. Simplify using `only [e4] at e3`. Rewrite `e3` using `[Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp)]`. Establish `e0 : evI F (0 : AF F) = 0` using `map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)`.

Simplify `e3` using `[Box.nf, e0]`. Establish `hu0 : Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ = 0` using `_root_.PositivityTheory.SiegelWeilFormula.KK.eq_zero_of_nf_k hu ha h2`. Establish `hZ0 : Z = 0` using `_root_.PositivityTheory.SiegelWeilFormula.KK.secondColumns_mul_injective hu0`. Substitute `hZ0` using the available equality. Simplify using `only [smul_zero, add_zero, Matrix.zero_mul, map_zero, _root_.PositivityTheory.SiegelWeilFormula.KK.D_zero_k, _root_.PositivityTheory.SiegelWeilFormula.KK.T_zero_k]`.

Conclude with `hasDerivAt_const _ _`.
-/
theorem hasDerivAt_translate_secondColumns {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {Z : Mx F E d.m d.n} (hZ : At (evI F) Z) (X : Mx F E d.m d.n) :
    HasDerivAt (fun t : ℝ => d.T Φ (X + realAd F t • Z)) (d.T (Box.D (d.dd.e (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)) Φ) X) 0 := by
  by_cases ha : Box.nf (d.dd.e (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)).1 = 0
  swap
  · exact _root_.PositivityTheory.SiegelWeilFormula.KK.hasDerivAt_translate_nonzero hΦ hZ ha X
  have hu := _root_.PositivityTheory.SiegelWeilFormula.KK.td_at_mul_k hZ (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ
  by_cases hB : ∃ Z₀ : Mx F E d.m d.n, At (evI F) Z₀ ∧ Box.nf (d.dd.e (Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)).1 ≠ 0
  · obtain ⟨Z₀, h0, h0'⟩ := hB
    have hu₀ := _root_.PositivityTheory.SiegelWeilFormula.KK.td_at_mul_k h0 (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ
    have hs : Box.nf (d.dd.e (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ + Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)).1 ≠ 0 := by rwa [_root_.PositivityTheory.SiegelWeilFormula.KK.nfe_add_k, ha, zero_add]
    have h1 := _root_.PositivityTheory.SiegelWeilFormula.KK.T_D_k hΦ (_root_.PositivityTheory.SiegelWeilFormula.KK.at_add'_k hu hu₀) hs X
    have key : ∀ t : ℝ, d.T Φ (X + realAd F t • Z) = d.B.ψ (realAd F t * -_root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d (X * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ) (Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) *
        (d.B.ψ (realAd F t * (realAd F t * (⅟(2 : AF F) * _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d (Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ) (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)))) *
          d.T (d.dd.rho d.B.ψ (realAd F t • (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ + Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ) X) := by
      intro t
      have k1 : d.B.ψ (realAd F t * (realAd F t * (⅟(2 : AF F) * _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d (Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ) (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)))) *
          d.T (d.dd.rho d.B.ψ (realAd F t • (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ + Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ) X =
            d.B.ψ (realAd F t * _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d (X * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ) (Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) * d.T Φ (X + realAd F t • Z) := by
        rw [← _root_.PositivityTheory.SiegelWeilFormula.KK.weilAction_secondColumns_translate Φ Z t X, ← _root_.PositivityTheory.SiegelWeilFormula.KK.T_rho_dg_k (_root_.PositivityTheory.SiegelWeilFormula.KK.rho_mem_k hΦ _) Z₀ t X, _root_.PositivityTheory.SiegelWeilFormula.KK.rho_rho_k, _root_.PositivityTheory.SiegelWeilFormula.KK.T_smul_k, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_smul_left_k, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_smul_right_k, smul_add,
          add_comm (realAd F t • (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ))]
        congr 2
        ring
      rw [k1, ← mul_assoc, ← AddChar.map_add_eq_mul, mul_neg, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
    have hR := (_root_.PositivityTheory.SiegelWeilFormula.KK.psi_line_deriv_k (d := d) (-_root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d (X * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ) (Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ))).mul
      ((_root_.PositivityTheory.SiegelWeilFormula.KK.hasDerivAt_character_quadratic (d := d) (⅟(2 : AF F) * _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d (Z₀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ) (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ))).mul h1)
    rw [funext key]
    refine hR.congr_deriv ?_
    have e2 := _root_.PositivityTheory.SiegelWeilFormula.KK.T_D_dg_ne_k hΦ h0 h0' X
    simp only [Pi.mul_apply]
    rw [_root_.PositivityTheory.SiegelWeilFormula.KK.schr_zero_at_k]
    simp only [td_realAd_zero, zero_mul, AddChar.map_zero_eq_one, one_mul, zero_add]
    rw [map_add, Box.D_add_left, _root_.PositivityTheory.SiegelWeilFormula.KK.td_T_add_k, e2, evI_neg', map_neg]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k]
    push_cast
    ring
  push_neg at hB
  have hsp : ∀ v, At (evI F) v → _root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ) v = 0 := by
    intro v hv
    obtain ⟨Z₁, Z₂, h1, h2, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.KK.split_arch_k hv
    rw [_root_.PositivityTheory.SiegelWeilFormula.KK.sp_add_right_k, _root_.PositivityTheory.SiegelWeilFormula.KK.symplectic_secondColumns_isotropic, add_zero, _root_.PositivityTheory.SiegelWeilFormula.KK.sp_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KK.vec_eq_zero_k (_root_.PositivityTheory.SiegelWeilFormula.KK.at_fst_k hu) ha, _root_.PositivityTheory.SiegelWeilFormula.KK.vec_eq_zero_k (_root_.PositivityTheory.SiegelWeilFormula.KK.at_fst_k (_root_.PositivityTheory.SiegelWeilFormula.KK.td_at_mul_k h1 _)) (hB Z₁ h1)]
    simp
  have h2 : Box.nf (d.dd.e (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)).2 = 0 := by
    funext j
    obtain ⟨v, hv, ev⟩ := _root_.PositivityTheory.SiegelWeilFormula.KK.exists_at'_k (d := d) (Pi.single j 1)
    have := hsp v hv
    rw [_root_.PositivityTheory.SiegelWeilFormula.KK.sp_eq_k, ev, _root_.PositivityTheory.SiegelWeilFormula.KK.vec_eq_zero_k (_root_.PositivityTheory.SiegelWeilFormula.KK.at_fst_k hu) ha] at this
    simp only [zero_dotProduct, dotProduct_zero, zero_sub, neg_eq_zero] at this
    have e3 := congrArg (evI F) this
    rw [_root_.PositivityTheory.SiegelWeilFormula.KK.evI_dot_k] at e3
    have e4 : ∀ i, evI F (Dense.pt (Pi.single j (1 : mixedEmbedding.mixedSpace F)) 0 i) =
        (Pi.single j (1 : mixedEmbedding.mixedSpace F) : d.κ → mixedEmbedding.mixedSpace F) i := fun i =>
      congrFun (Dense.evI_pt (Pi.single j (1 : mixedEmbedding.mixedSpace F)) 0) i
    simp only [e4] at e3
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp)] at e3
    have e0 : evI F (0 : AF F) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    simpa [Box.nf, e0] using e3
  have hu0 : Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ = 0 := _root_.PositivityTheory.SiegelWeilFormula.KK.eq_zero_of_nf_k hu ha h2
  have hZ0 : Z = 0 := _root_.PositivityTheory.SiegelWeilFormula.KK.secondColumns_mul_injective hu0
  subst hZ0
  simp only [smul_zero, add_zero, Matrix.zero_mul, map_zero, _root_.PositivityTheory.SiegelWeilFormula.KK.D_zero_k, _root_.PositivityTheory.SiegelWeilFormula.KK.T_zero_k]
  exact hasDerivAt_const _ _
/- English proof (translation)
Establish `h` using `d.ok.good.cm`. Rewrite using `[Dense.trace_evI h.1]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `e : (y.map (cA σ)).map (piInf (d.B.emb w)) = (y.map (piInf (d.B.emb w))).map star`. Use extensionality with `i j`.

Conclude with `Dense.piInf_cA h _ _`. Establish `eJ : (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) = dbl (d.Y.J.map (d.B.emb w).1)`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KK.dbl_incM_k, td_map_incM]`. Apply the tactic sequence `ext (i | i) (j | j) <;> simp [dbl]`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KK.sp_k, symp, Dense.ext_trace h (d.B.emb w), Dense.piInf_cA h, neg_one_mul, map_neg, Dense.hTens_tr, AddMonoidHom.map_trace (piInf (d.B.emb w)), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.transpose_map, …`.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem trace_sp_k (x y : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (_root_.PositivityTheory.SiegelWeilFormula.KK.sp_k d x y)) =
      ∑ w, -(2 * (Matrix.trace ((x.map (piInf (d.B.emb w)))ᵀ * d.A.J.map (d.B.emb w).1 *
        (y.map (piInf (d.B.emb w))).map star * (dbl (d.Y.J.map (d.B.emb w).1))ᵀ)).re) := by
  have h := d.ok.good.cm
  rw [Dense.trace_evI h.1]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : (y.map (cA σ)).map (piInf (d.B.emb w)) = (y.map (piInf (d.B.emb w))).map star := by
    ext i j
    exact Dense.piInf_cA h _ _
  have eJ : (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) = dbl (d.Y.J.map (d.B.emb w).1) := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KK.dbl_incM_k, td_map_incM]
    ext (i | i) (j | j) <;> simp [dbl]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.sp_k, symp, Dense.ext_trace h (d.B.emb w), Dense.piInf_cA h, neg_one_mul, map_neg, Dense.hTens_tr,
    AddMonoidHom.map_trace (piInf (d.B.emb w)), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
    Matrix.transpose_map, td_map_incM, eJ, e]
  simp
  ring
end PositivityTheory.SiegelWeilFormula.KK
end
end
