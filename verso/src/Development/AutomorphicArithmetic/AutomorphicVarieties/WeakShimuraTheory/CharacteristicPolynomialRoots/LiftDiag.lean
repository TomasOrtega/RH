import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.LeKerPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

/- English proof (translation)
Use `letI : Algebra B K[X] := ((algebraMap K K[X]).comp f).toAlgebra`. Set `φ : B[X] →ₐ[B] K[X]` to `{ Polynomial.mapRingHom f with commutes' := fun a => by simp [RingHom.algebraMap_toAlgebra] }`. Establish `e : (MonoidAlgebra.mapRingHom Γ (φ : B[X] →+* K[X])) (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom Γ C z) = MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom Γ C (MonoidAlgebra.mapRingHom Γ f z)`. Rewrite using `[map_sub, MonoidAlgebra.mapRingHom_single]`. Use `congr 1`.

Simplify using `[φ]`. Proceed by induction on `z using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `single g b => simp [φ, MonoidAlgebra.mapRingHom_single]`.

Establish `h` using `D.nat B[X] K[X] φ (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom Γ C z)`. Rewrite `h` using `[e]`. Conclude with `h.symm`.
-/
private theorem chi_map_eq_map_chi_mapRingHom {n : ℕ} {B K Γ : Type} [CommRing B] [CommRing K] [Group Γ]
    (D : W.GDet n B Γ) (f : B →+* K) (z : MonoidAlgebra B Γ) :
    (D.chi z).map f = (D.map f).chi (MonoidAlgebra.mapRingHom Γ f z) := by
  letI : Algebra B K[X] := ((algebraMap K K[X]).comp f).toAlgebra
  let φ : B[X] →ₐ[B] K[X] :=
    { Polynomial.mapRingHom f with
      commutes' := fun a => by simp [RingHom.algebraMap_toAlgebra] }
  have e : (MonoidAlgebra.mapRingHom Γ (φ : B[X] →+* K[X]))
      (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom Γ C z) =
      MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom Γ C (MonoidAlgebra.mapRingHom Γ f z) := by
    rw [map_sub, MonoidAlgebra.mapRingHom_single]
    congr 1
    · simp [φ]
    · induction z using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | single g b => simp [φ, MonoidAlgebra.mapRingHom_single]
  have h := D.nat B[X] K[X] φ (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom Γ C z)
  rw [e] at h
  exact h.symm

/- English proof (translation)
Establish `e : W.GDet.repAlg σ K[X] (MonoidAlgebra.mapRingHom Γ C w) = (C : K →+* K[X]).mapMatrix (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) Γ σ w)`. Proceed by induction on `w using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `single g b`.

Simplify using `only [W.GDet.repAlg, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.lift_single]`. Use extensionality with `i j`. Simplify using `[Polynomial.smul_eq_C_mul, Polynomial.algebraMap_apply]`. Establish `e1 : W.GDet.repAlg σ K[X] (MonoidAlgebra.single 1 X) = Matrix.scalar (Fin n) (X : K[X])`. Simplify using `only [W.GDet.repAlg, MonoidAlgebra.lift_single, map_one]`.

Use extensionality with `i j`. Simplify using `[Matrix.one_apply, Matrix.diagonal_apply]`. Use `show Matrix.det (W.GDet.repAlg σ K[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom Γ C w)) = _`. Rewrite using `[map_sub, e, e1]`. Both sides reduce to the same expression.
-/
private theorem chi_ofRep_eq_charpoly_lift {n : ℕ} {K Γ : Type} [CommRing K] [Group Γ]
    (σ : Γ →* Matrix (Fin n) (Fin n) K) (w : MonoidAlgebra K Γ) :
    (W.GDet.ofRep σ).chi w = (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) Γ σ w).charpoly := by
  have e : W.GDet.repAlg σ K[X] (MonoidAlgebra.mapRingHom Γ C w) =
      (C : K →+* K[X]).mapMatrix (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) Γ σ w) := by
    induction w using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single g b =>
      simp only [W.GDet.repAlg, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.lift_single]
      ext i j
      simp [Polynomial.smul_eq_C_mul, Polynomial.algebraMap_apply]
  have e1 : W.GDet.repAlg σ K[X] (MonoidAlgebra.single 1 X) = Matrix.scalar (Fin n) (X : K[X]) := by
    simp only [W.GDet.repAlg, MonoidAlgebra.lift_single, map_one]
    ext i j
    simp [Matrix.one_apply, Matrix.diagonal_apply]
  show Matrix.det (W.GDet.repAlg σ K[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom Γ C w)) = _
  rw [map_sub, e, e1]
  rfl

/- English proof (translation)
Rewrite using `[chi_map_eq_map_chi_mapRingHom, h, chi_ofRep_eq_charpoly_lift]`. Establish `e : MonoidAlgebra.mapRingHom Γ (f : B →+* K) (MonoidAlgebra.mapRingHom Γ (algebraMap O B) y) = MonoidAlgebra.mapRingHom Γ (algebraMap O K) y`. Proceed by induction on `y using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.

Consider the case `single g b => simp [MonoidAlgebra.mapRingHom_single]`. Rewrite using `[e, MonoidAlgebra.lift_mapRingHom_algebraMap]`.
-/
private theorem chi_map {n : ℕ} {O B K Γ : Type} [CommRing O] [CommRing B] [CommRing K] [Algebra O B] [Algebra O K]
    [Group Γ] (D : W.GDet n B Γ) (f : B →ₐ[O] K) (σ : Γ →* Matrix (Fin n) (Fin n) K)
    (h : D.map (f : B →+* K) = W.GDet.ofRep σ) (y : MonoidAlgebra O Γ) :
    (D.chi (MonoidAlgebra.mapRingHom Γ (algebraMap O B) y)).map (f : B →+* K) =
      (MonoidAlgebra.lift O (Matrix (Fin n) (Fin n) K) Γ σ y).charpoly := by
  rw [chi_map_eq_map_chi_mapRingHom, h, chi_ofRep_eq_charpoly_lift]
  have e : MonoidAlgebra.mapRingHom Γ (f : B →+* K) (MonoidAlgebra.mapRingHom Γ (algebraMap O B) y) =
      MonoidAlgebra.mapRingHom Γ (algebraMap O K) y := by
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single g b => simp [MonoidAlgebra.mapRingHom_single]
  rw [e, MonoidAlgebra.lift_mapRingHom_algebraMap]

/- English proof (translation)
Proceed by induction on `y using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb`. Rewrite using `[map_add, ha, hb, Matrix.diagonal_add]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Rewrite using `[map_add]`. Consider the case `single g b`. Use extensionality with `i j`. Simplify using `[W.diagRep, MonoidAlgebra.lift_single, Matrix.diagonal_apply]`.
-/
private theorem lift_diag {n : ℕ} {O K Γ : Type} [CommRing O] [CommRing K] [Algebra O K]
    [Group Γ] (χ : Fin n → Γ →* Kˣ) (y : MonoidAlgebra O Γ) :
    MonoidAlgebra.lift O (Matrix (Fin n) (Fin n) K) Γ (W.diagRep χ) y =
      Matrix.diagonal fun i => MonoidAlgebra.lift O K Γ ((Units.coeHom _).comp (χ i)) y := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, ha, hb, Matrix.diagonal_add]
    congr 1
    funext i
    rw [map_add]
  | single g b =>
    ext i j
    simp [W.diagRep, MonoidAlgebra.lift_single, Matrix.diagonal_apply]

/- English proof (translation)
Establish `hcoef : ∀ k, ‖(P.map x).coeff k‖ ≤ 1` using `fun k => by rw [Polynomial.coeff_map]; exact h1 _`. Establish `hz1 : ‖z‖ ≤ 1`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hev` using `hz.eq_zero`.

Rewrite `hev` using `[Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hP.coeff_natDegree, one_mul]`. Use `set d := (P.map x).natDegree`. Establish `hzd : z ^ d = -∑ i ∈ Finset.range d, (P.map x).coeff i * z ^ i`. Take the linear combination `hev`. Break down `Nat.eq_zero_or_pos d with hd | hd` into its components or cases.

Rewrite `hzd` using `[hd]`. Simplify using `at hzd`. Establish `hpos : 0 < ‖z‖ ^ (d - 1)` using `pow_pos (by linarith) _`. Establish `hle : ‖z‖ ^ d ≤ ‖z‖ ^ (d - 1)`. Rewrite using `[← norm_pow, hzd, norm_neg]`.

Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hpos.le fun i hi => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow]`. Establish `hi' : i ≤ d - 1`. Use `Finset.mem_range.mp hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Combine the equalities or inequalities in the displayed calculation. Establish `: ‖z‖ ^ d = ‖z‖ ^ (d - 1) * ‖z‖`. Rewrite using `[← pow_succ]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Rewrite `hle` using `[this]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hE : ‖((P - ∏ i, (X - C (a i))).map x).eval z‖ < 1`. Rewrite using `[Polynomial.eval_eq_sum_range]`. Take `⟨k, -, hle⟩` from `IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩ (fun i => ((P - ∏ i, (X - C (a i))).map x).coeff i * z ^ i)`.

Use `hle.trans_lt ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow, Polynomial.coeff_map]`. Combine the equalities or inequalities in the displayed calculation. Establish `hsum : (P.map x).eval z = (∏ i, (z - x (a i))) + ((P - ∏ i, (X - C (a i))).map x).eval z`. Rewrite using `[Polynomial.map_sub, Polynomial.eval_sub, Polynomial.map_prod, Polynomial.eval_prod]`.

Simplify using the standard rewrite rules. Establish `hprod : ‖∏ i, (z - x (a i))‖ < 1`. Establish `: ∏ i, (z - x (a i)) = -((P - ∏ i, (X - C (a i))).map x).eval z`. Rewrite `hsum` using `[hz.eq_zero]`. Take the linear combination `(-1 : K) * hsum`.

Rewrite using `[this, norm_neg]`. Conclude with `hE`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `: (1 : ℝ) ≤ ‖∏ i, (z - x (a i))‖`.

Rewrite using `[norm_prod]`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem near {n : ℕ} {B K : Type} [CommRing B] [NormedField K] [IsUltrametricDist K] (I : Ideal B)
    (x : B →+* K) (h1 : ∀ b, ‖x b‖ ≤ 1) (hm : ∀ b ∈ I, ‖x b‖ < 1) (P : B[X]) (hP : (P.map x).Monic) (a : Fin n → B)
    (ha : ∀ k, (P - ∏ i, (X - C (a i))).coeff k ∈ I) (z : K) (hz : (P.map x).IsRoot z) : ∃ i, ‖z - x (a i)‖ < 1 := by
  classical
  have hcoef : ∀ k, ‖(P.map x).coeff k‖ ≤ 1 := fun k => by rw [Polynomial.coeff_map]; exact h1 _
  have hz1 : ‖z‖ ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    have hev := hz.eq_zero
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hP.coeff_natDegree, one_mul] at hev
    set d := (P.map x).natDegree
    have hzd : z ^ d = -∑ i ∈ Finset.range d, (P.map x).coeff i * z ^ i := by
      linear_combination hev
    rcases Nat.eq_zero_or_pos d with hd | hd
    · rw [hd] at hzd
      simp at hzd
    have hpos : 0 < ‖z‖ ^ (d - 1) := pow_pos (by linarith) _
    have hle : ‖z‖ ^ d ≤ ‖z‖ ^ (d - 1) := by
      rw [← norm_pow, hzd, norm_neg]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hpos.le fun i hi => ?_
      rw [norm_mul, norm_pow]
      have hi' : i ≤ d - 1 := by
        have := Finset.mem_range.mp hi
        omega
      calc ‖(P.map x).coeff i‖ * ‖z‖ ^ i ≤ 1 * ‖z‖ ^ i :=
            mul_le_mul_of_nonneg_right (hcoef i) (by positivity)
        _ = ‖z‖ ^ i := one_mul _
        _ ≤ ‖z‖ ^ (d - 1) := pow_le_pow_right₀ hlt.le hi'
    have : ‖z‖ ^ d = ‖z‖ ^ (d - 1) * ‖z‖ := by
      rw [← pow_succ]
      congr 1
      omega
    rw [this] at hle
    nlinarith
  have hE : ‖((P - ∏ i, (X - C (a i))).map x).eval z‖ < 1 := by
    rw [Polynomial.eval_eq_sum_range]
    obtain ⟨k, -, hle⟩ :=
      IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
        (fun i => ((P - ∏ i, (X - C (a i))).map x).coeff i * z ^ i)
    refine hle.trans_lt ?_
    rw [norm_mul, norm_pow, Polynomial.coeff_map]
    calc ‖x ((P - ∏ i, (X - C (a i))).coeff k)‖ * ‖z‖ ^ k
        ≤ ‖x ((P - ∏ i, (X - C (a i))).coeff k)‖ * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hz1) (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hm _ (ha k)
  have hsum : (P.map x).eval z = (∏ i, (z - x (a i))) + ((P - ∏ i, (X - C (a i))).map x).eval z := by
    rw [Polynomial.map_sub, Polynomial.eval_sub, Polynomial.map_prod, Polynomial.eval_prod]
    simp
  have hprod : ‖∏ i, (z - x (a i))‖ < 1 := by
    have : ∏ i, (z - x (a i)) = -((P - ∏ i, (X - C (a i))).map x).eval z := by
      rw [hz.eq_zero] at hsum
      linear_combination (-1 : K) * hsum
    rw [this, norm_neg]
    exact hE
  by_contra hne
  push_neg at hne
  have : (1 : ℝ) ≤ ‖∏ i, (z - x (a i))‖ := by
    rw [norm_prod]
    calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
      _ ≤ ∏ i, ‖z - x (a i)‖ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => hne i)
  linarith

/- English proof (translation)
Introduce `l _ L Ω _ _ _ _ _ _ s V c n r B x ρ hx`. Introduce `y z hz`. Use `letI := B.ring`. Use `letI := B.alg`. Use `haveI := B.co`.

Use `set D := B.u.D.comap V.pr with hD`. Establish `hxD : D.map (x : B.B →+* PadicAlgCl l) = W.GDet.ofRep (W.mat ρ)` using `hx`. Establish `hrD : D.map (res c.O B.B : B.B →+* ResidueField c.O) = W.GDet.ofRep (W.diagRep fun i => (r.chib i).comp V.pr)`. Establish `h0 : (B.u.D.map (res c.O B.B : B.B →+* ResidueField c.O)).comap V.pr = (r.Dbar).comap V.pr` using `by rw [B.u.red]`. Use `h0.trans ?_` and prove the remaining obligations.

Rewrite using `[W.Resid.Dbar]`. Use `((AlgebraTools.Det.repApi (W.diagRep r.chib)).2.2.2.2.2.2.1 V.pr).trans ?_` and prove the remaining obligations. Conclude with `congrArg W.GDet.ofRep (MonoidHom.ext fun g => rfl)`. Use `set P := D.chi (MonoidAlgebra.mapRingHom _ (algebraMap c.O B.B) y) with hP`. Establish `hPx` using `chi_map D (x : B.B →ₐ[c.O] PadicAlgCl l) (W.mat ρ) hxD y`.

Establish `hPr` using `chi_map D (res c.O B.B) (W.diagRep fun i => (r.chib i).comp V.pr) hrD y`. Rewrite `hPr` using `[lift_diag, Matrix.charpoly_diagonal]`. Use `set d : Fin n → ResidueField c.O := fun i => MonoidAlgebra.lift c.O (ResidueField c.O) _ ((Units.coeHom _).comp ((r.chib i).comp V.pr)) y with hd`. Use `choose a' ha' using fun i => IsLocalRing.residue_surjective (d i)`. Establish `hco` using `(GradeZeroInterpolatingElement.coPt c B.B).1 x`.

Take `⟨-, e, he1, he0, hen⟩` from `hco`. Establish `h1 : ∀ b, ‖(x : B.B →+* PadicAlgCl l) b‖ ≤ 1` using `fun b => by`. Use `hen 0 b (by simp)` as an intermediate fact. Simplify using `using this`. Establish `hm : ∀ b ∈ IsLocalRing.maximalIdeal B.B, ‖(x : B.B →+* PadicAlgCl l) b‖ < 1` using `fun b hb => by`.

Use `hen 1 b (by simpa using hb)` as an intermediate fact. Simplify using `only [pow_one] at this`. Conclude with `lt_of_le_of_lt this he1`. Establish `hmon : (P.map (x : B.B →+* PadicAlgCl l)).Monic`. Rewrite using `[hPx]`.

Conclude with `Matrix.charpoly_monic _`. Establish `hroot : (P.map (x : B.B →+* PadicAlgCl l)).IsRoot z`. Rewrite using `[hPx]`. Conclude with `Polynomial.isRoot_of_mem_roots hz`. Establish `hres : ∀ i, (res c.O B.B) (algebraMap c.O B.B (a' i)) = d i` using `fun i => by`.

Rewrite using `[AlgHom.commutes, ← ha' i]`. Both sides reduce to the same expression. Establish `hcoef : ∀ k, (P - ∏ i, (X - C (algebraMap c.O B.B (a' i)))).coeff k ∈ IsLocalRing.maximalIdeal B.B`. Introduce `k`. Rewrite using `[← res_eq_zero_iff c.O B.B]`.

Use `show (res c.O B.B : B.B →+* ResidueField c.O) _ = 0`. Rewrite using `[← Polynomial.coeff_map]`. Establish `: (P - ∏ i, (X - C (algebraMap c.O B.B (a' i)))).map (res c.O B.B : B.B →+* ResidueField c.O) = 0`. Rewrite using `[Polynomial.map_sub, hPr, Polynomial.map_prod, sub_eq_zero]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]`. Use `congr 2`. Conclude with `(hres i).symm`. Rewrite using `[this, Polynomial.coeff_zero]`. Take `⟨i, hi⟩` from `near (IsLocalRing.maximalIdeal B.B) (x : B.B →+* PadicAlgCl l) h1 hm P hmon (fun i => algebraMap c.O B.B (a' i)) hcoef z hroot`.

Use `⟨i, a' i, ha' i, ?_⟩` and prove the remaining obligations. Establish `: (x : B.B →+* PadicAlgCl l) (algebraMap c.O B.B (a' i)) = (a' i : PadicAlgCl l)` using `by show x (algebraMap c.O B.B (a' i)) = _`. Rewrite using `[AlgHom.commutes]`. Both sides reduce to the same expression. Rewrite `hi` using `[this]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.Ws.Pu.ptRed :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} (B : W.UniversalOrdinaryDeterminantRing r) (x : B.Pt) (ρ : G L Ω →* GL (Fin n) (PadicAlgCl l)), x.IsRep ρ → RedTo c ρ fun i => (r.chib i).comp V.pr := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B x ρ hx
  intro y z hz
  letI := B.ring
  letI := B.alg
  haveI := B.co
  set D := B.u.D.comap V.pr with hD
  have hxD : D.map (x : B.B →+* PadicAlgCl l) = W.GDet.ofRep (W.mat ρ) := hx
  have hrD : D.map (res c.O B.B : B.B →+* ResidueField c.O) =
      W.GDet.ofRep (W.diagRep fun i => (r.chib i).comp V.pr) := by
    have h0 : (B.u.D.map (res c.O B.B : B.B →+* ResidueField c.O)).comap V.pr =
        (r.Dbar).comap V.pr := by rw [B.u.red]
    refine h0.trans ?_
    rw [W.Resid.Dbar]
    refine ((AlgebraTools.Det.repApi (W.diagRep r.chib)).2.2.2.2.2.2.1 V.pr).trans ?_
    exact congrArg W.GDet.ofRep (MonoidHom.ext fun g => rfl)
  set P := D.chi (MonoidAlgebra.mapRingHom _ (algebraMap c.O B.B) y) with hP
  have hPx := chi_map D (x : B.B →ₐ[c.O] PadicAlgCl l) (W.mat ρ) hxD y
  have hPr := chi_map D (res c.O B.B) (W.diagRep fun i => (r.chib i).comp V.pr) hrD y
  rw [lift_diag, Matrix.charpoly_diagonal] at hPr
  set d : Fin n → ResidueField c.O := fun i =>
    MonoidAlgebra.lift c.O (ResidueField c.O) _ ((Units.coeHom _).comp ((r.chib i).comp V.pr)) y with hd
  choose a' ha' using fun i => IsLocalRing.residue_surjective (d i)
  have hco := (GradeZeroInterpolatingElement.coPt c B.B).1 x
  obtain ⟨-, e, he1, he0, hen⟩ := hco
  have h1 : ∀ b, ‖(x : B.B →+* PadicAlgCl l) b‖ ≤ 1 := fun b => by
    have := hen 0 b (by simp)
    simpa using this
  have hm : ∀ b ∈ IsLocalRing.maximalIdeal B.B, ‖(x : B.B →+* PadicAlgCl l) b‖ < 1 := fun b hb => by
    have := hen 1 b (by simpa using hb)
    simp only [pow_one] at this
    exact lt_of_le_of_lt this he1
  have hmon : (P.map (x : B.B →+* PadicAlgCl l)).Monic := by
    rw [hPx]
    exact Matrix.charpoly_monic _
  have hroot : (P.map (x : B.B →+* PadicAlgCl l)).IsRoot z := by
    rw [hPx]
    exact Polynomial.isRoot_of_mem_roots hz
  have hres : ∀ i, (res c.O B.B) (algebraMap c.O B.B (a' i)) = d i := fun i => by
    rw [AlgHom.commutes, ← ha' i]
    rfl
  have hcoef : ∀ k, (P - ∏ i, (X - C (algebraMap c.O B.B (a' i)))).coeff k ∈ IsLocalRing.maximalIdeal B.B := by
    intro k
    rw [← res_eq_zero_iff c.O B.B]
    show (res c.O B.B : B.B →+* ResidueField c.O) _ = 0
    rw [← Polynomial.coeff_map]
    have : (P - ∏ i, (X - C (algebraMap c.O B.B (a' i)))).map (res c.O B.B : B.B →+* ResidueField c.O) = 0 := by
      rw [Polynomial.map_sub, hPr, Polynomial.map_prod, sub_eq_zero]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      congr 2
      exact (hres i).symm
    rw [this, Polynomial.coeff_zero]
  obtain ⟨i, hi⟩ := near (IsLocalRing.maximalIdeal B.B) (x : B.B →+* PadicAlgCl l) h1 hm P hmon
    (fun i => algebraMap c.O B.B (a' i)) hcoef z hroot
  refine ⟨i, a' i, ha' i, ?_⟩
  have : (x : B.B →+* PadicAlgCl l) (algebraMap c.O B.B (a' i)) = (a' i : PadicAlgCl l) := by
    show x (algebraMap c.O B.B (a' i)) = _
    rw [AlgHom.commutes]
    rfl
  rwa [this] at hi
