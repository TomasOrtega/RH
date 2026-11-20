import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.EmDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestAlg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbscissaConvergenceIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinedBlockFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousThetaKernelComponents

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em
open IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.OrbExist

variable {D : D7} {a b c n r t : ℕ}

/- English proof (translation)
Establish `hb` using `b₀.2`. Use extensionality with `i j`. Establish `h2 : D.sp.cm.sig (b₀.1 j i) = b₀.1 i j`. Use `congrFun (congrFun hb i) j` as an intermediate fact. Simplify using `using this`.

Express the relevant statement in the definitionally equal form `cA D (incA D (b₀.1 j i)) = incA D (b₀.1 i j)`. Rewrite using `[← h2]`. Both sides reduce to the same expression.
-/
theorem adj_rat_herm (b₀ : HermE D r) : adj (rat b₀.1) = rat b₀.1 := by
  have hb := b₀.2
  ext i j
  have h2 : D.sp.cm.sig (b₀.1 j i) = b₀.1 i j := by
    have := congrFun (congrFun hb i) j
    simpa using this
  change cA D (incA D (b₀.1 j i)) = incA D (b₀.1 i j)
  rw [← h2]
  rfl

/- English proof (translation)
Establish `h : b₀.1⁻¹ * b₀.1 = 1` using `Matrix.nonsing_inv_mul _ (Ne.isUnit hb)`. Use `congrArg (fun M : Matrix (Fin r) (Fin r) D.host.E => M.map (incA D)) h` as an intermediate fact. Simplify `this` using `[rat, mm, Matrix.map_mul]`.
-/
theorem rat_inv_mul (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) : mm (rat b₀.1⁻¹) (rat b₀.1) = (1 : Mx D r r) := by
  have h : b₀.1⁻¹ * b₀.1 = 1 := Matrix.nonsing_inv_mul _ (Ne.isUnit hb)
  have := congrArg (fun M : Matrix (Fin r) (Fin r) D.host.E => M.map (incA D)) h
  simpa [rat, mm, Matrix.map_mul] using this

/- English proof (translation)
Establish `h : b₀.1 * b₀.1⁻¹ = 1` using `Matrix.mul_nonsing_inv _ (Ne.isUnit hb)`. Use `congrArg (fun M : Matrix (Fin r) (Fin r) D.host.E => M.map (incA D)) h` as an intermediate fact. Simplify `this` using `[rat, mm, Matrix.map_mul]`.
-/
theorem rat_mul_inv (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) : mm (rat b₀.1) (rat b₀.1⁻¹) = (1 : Mx D r r) := by
  have h : b₀.1 * b₀.1⁻¹ = 1 := Matrix.mul_nonsing_inv _ (Ne.isUnit hb)
  have := congrArg (fun M : Matrix (Fin r) (Fin r) D.host.E => M.map (incA D)) h
  simpa [rat, mm, Matrix.map_mul] using this

/- English proof (translation)
Unfold `ip mm`. Rewrite using `[adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]`.
-/
theorem adj_ip (V : HSp D) (x : Mx D V.rank a) (y : Mx D V.rank b) : adj (ip V x y) = ip V y x := by
  unfold ip mm
  rw [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[adj]`.
-/
theorem adj_add_r (x y : Mx D a b) : adj (x + y) = adj x + adj y := by
  ext i j
  simp [adj]

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[adj]`. Establish `h' : j ≠ i` using `fun q => h q.symm`.

Simplify using `[adj, Matrix.one_apply, h, h']`.
-/
theorem adj_one_r : adj (1 : Mx D a a) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [adj]
  · have h' : j ≠ i := fun q => h q.symm
    simp [adj, Matrix.one_apply, h, h']

/- English proof (translation)
Establish `h1 : adj (mm (rat b₀.1⁻¹) (rat b₀.1)) = 1` using `by rw [rat_inv_mul b₀ hb, adj_one_r]`. Establish `h2 : mm (rat b₀.1) (adj (rat b₀.1⁻¹)) = 1`. Use `h1` as an intermediate fact. Simplify using `only [mm] at this ⊢`. Rewrite `this` using `[adj_mul, adj_rat_herm]`. Then use the resulting hypothesis.

Establish `h3` using `congrArg (fun M : Mx D r r => mm (rat b₀.1⁻¹) M) h2`. Simplify using `only [mm] at h3`. Establish `h4 : mm (rat b₀.1⁻¹) (rat b₀.1) = (1 : Mx D r r)` using `rat_inv_mul b₀ hb`. Simplify using `only [mm] at h4`. Rewrite `h3` using `[← Matrix.mul_assoc, h4, Matrix.one_mul, Matrix.mul_one]`. Then use the resulting hypothesis.
-/
theorem adj_rat_inv (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) : adj (rat b₀.1⁻¹) = rat b₀.1⁻¹ := by
  have h1 : adj (mm (rat b₀.1⁻¹) (rat b₀.1)) = 1 := by rw [rat_inv_mul b₀ hb, adj_one_r]
  have h2 : mm (rat b₀.1) (adj (rat b₀.1⁻¹)) = 1 := by
    have := h1
    simp only [mm] at this ⊢
    rwa [adj_mul, adj_rat_herm] at this
  have h3 := congrArg (fun M : Mx D r r => mm (rat b₀.1⁻¹) M) h2
  simp only [mm] at h3
  have h4 : mm (rat b₀.1⁻¹) (rat b₀.1) = (1 : Mx D r r) := rat_inv_mul b₀ hb
  simp only [mm] at h4
  rwa [← Matrix.mul_assoc, h4, Matrix.one_mul, Matrix.mul_one] at h3

/- English proof (translation)
Unfold `ip mm`. Rewrite using `[Matrix.mul_add, Matrix.mul_add]`.
-/
theorem ip_add_right (V : HSp D) (x : Mx D V.rank a) (y y' : Mx D V.rank b) :
    ip V x (y + y') = ip V x y + ip V x y' := by
  unfold ip mm
  rw [Matrix.mul_add, Matrix.mul_add]

/- English proof (translation)
Unfold `ip mm`. Rewrite using `[adj_add_r, Matrix.add_mul]`.
-/
theorem ip_add_left (V : HSp D) (x x' : Mx D V.rank a) (y : Mx D V.rank b) :
    ip V (x + x') y = ip V x y + ip V x' y := by
  unfold ip mm
  rw [adj_add_r, Matrix.add_mul]

/- English proof (translation)
Unfold `ip mm`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem ip_mul_right (V : HSp D) (x : Mx D V.rank a) (y : Mx D V.rank b) (w : Mx D b c) :
    ip V x (mm y w) = mm (ip V x y) w := by
  unfold ip mm
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Unfold `ip mm`. Rewrite using `[adj_mul, Matrix.mul_assoc]`.
-/
theorem ip_mul_left (V : HSp D) (x : Mx D V.rank a) (y : Mx D V.rank b) (w : Mx D a c) :
    ip V (mm x w) y = mm (adj w) (ip V x y) := by
  unfold ip mm
  rw [adj_mul, Matrix.mul_assoc]

/- English proof (translation)
Unfold `ip mm`. Rewrite using `[Matrix.mul_smul, Matrix.mul_smul]`.
-/
theorem ip_smul_right (V : HSp D) (e : AE D) (x : Mx D V.rank a) (y : Mx D V.rank b) :
    ip V x (e • y) = e • ip V x y := by
  unfold ip mm
  rw [Matrix.mul_smul, Matrix.mul_smul]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `adj (qv V b₀ z) = qv V b₀ z`. Establish `hp : adj (pr b₀ (yv V b₀ z) (yv V b₀ z)) = pr b₀ (yv V b₀ z) (yv V b₀ z)`. Establish `hr : (b₀.1.map (incA D)) = rat b₀.1` using `rfl`. Unfold `pr`. Rewrite using `[hr, adj_mul, adj_mul, adj_adj, adj_rat_herm, Matrix.mul_assoc]`.

Establish `hs : ∀ x y : Mx D t t, adj (x - y) = adj x - adj y`. Introduce `x y`. Use extensionality with `i j`. Simplify using `[adj]`. Unfold `qv`.

Rewrite using `[hs, hp, adj_ip]`.
-/
theorem qv_mem (V : HSp D) (b₀ : HermE D r) (z : Mx D V.rank r × Mx D V.rank t) : qv V b₀ z ∈ hermA D t := by
  change adj (qv V b₀ z) = qv V b₀ z
  have hp : adj (pr b₀ (yv V b₀ z) (yv V b₀ z)) = pr b₀ (yv V b₀ z) (yv V b₀ z) := by
    have hr : (b₀.1.map (incA D)) = rat b₀.1 := rfl
    unfold pr
    rw [hr, adj_mul, adj_mul, adj_adj, adj_rat_herm, Matrix.mul_assoc]
  have hs : ∀ x y : Mx D t t, adj (x - y) = adj x - adj y := by
    intro x y
    ext i j
    simp [adj]
  unfold qv
  rw [hs, hp, adj_ip]

/- English proof (translation)
Unfold `yv`. Use `conv_rhs => rw [← h, ip_smul_right]`. Simplify using `only [mm]`. Rewrite using `[Matrix.mul_smul]`.
-/
theorem yv_smul (V : HSp D) (b₀ : HermE D r) (e : AE D) (z : Mx D V.rank r × Mx D V.rank t) (h : e • z.2 = z.2) :
    e • yv V b₀ z = yv V b₀ z := by
  unfold yv
  conv_rhs => rw [← h, ip_smul_right]
  simp only [mm]
  rw [Matrix.mul_smul]

/- English proof (translation)
Establish `h1 : e • ip V z.2 z.2 = ip V z.2 z.2`. Use `ip_smul_right V e z.2 z.2` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `this.symm`. Establish `h2 : e • pr b₀ (yv V b₀ z) (yv V b₀ z) = pr b₀ (yv V b₀ z) (yv V b₀ z)`.

Unfold `pr`. Rewrite using `[← Matrix.mul_smul, ← Matrix.mul_smul, yv_smul V b₀ e z h]`. Unfold `qv`. Rewrite using `[smul_sub, h1, h2]`.
-/
theorem qv_smul (V : HSp D) (b₀ : HermE D r) (e : AE D) (z : Mx D V.rank r × Mx D V.rank t) (h : e • z.2 = z.2) :
    e • qv V b₀ z = qv V b₀ z := by
  have h1 : e • ip V z.2 z.2 = ip V z.2 z.2 := by
    have := ip_smul_right V e z.2 z.2
    rw [h] at this
    exact this.symm
  have h2 : e • pr b₀ (yv V b₀ z) (yv V b₀ z) = pr b₀ (yv V b₀ z) (yv V b₀ z) := by
    unfold pr
    rw [← Matrix.mul_smul, ← Matrix.mul_smul, yv_smul V b₀ e z h]
  unfold qv
  rw [smul_sub, h1, h2]

/- English proof (translation)
Unfold `pr`. Rewrite using `[adj_add_r, Matrix.mul_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]`.
-/
theorem pr_add (b₀ : HermE D r) (u u' w w' : Mx D r t) :
    pr b₀ (u + u') (w + w') = pr b₀ u w + pr b₀ u w' + (pr b₀ u' w + pr b₀ u' w') := by
  unfold pr
  rw [adj_add_r, Matrix.mul_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]

/- English proof (translation)
Normalize the expressions using the abelian group laws.
-/
theorem alg4 {M : Type} [AddCommGroup M] (c p a a' s : M) :
    c + a + (a' + s) - (p + a + (a' + s)) = c - p := by abel

/- English proof (translation)
Establish `hr : (b₀.1.map (incA D)) = rat b₀.1` using `rfl`. Establish `hGy : mm (ip V z₁ z₁) y = mm (rat b₀.1) y`. Rewrite using `[hG]`. Simplify using `only [mm]`. Rewrite using `[Matrix.smul_mul, ← Matrix.mul_smul, hy]`.

Establish `hyv : yv V b₀ (z₁, z₂ + mm z₁ y) = yv V b₀ (z₁, z₂) + y`. Unfold `yv`. Simplify using `only`. Rewrite using `[ip_add_right, ip_mul_right, hGy]`. Simplify using `only [mm]`.

Rewrite using `[Matrix.mul_add, ← Matrix.mul_assoc]`. Use `rat_inv_mul b₀ hb` as an intermediate fact. Simplify using `only [mm] at this`. Rewrite using `[this, Matrix.one_mul]`. Establish `hPi` using `rat_inv_mul b₀ hb`.

Establish `hPi'` using `rat_mul_inv b₀ hb`. Establish `hu : adj (yv V b₀ (z₁, z₂)) = mm (ip V z₂ z₁) (rat b₀.1⁻¹)`. Unfold `yv`. Simplify using `only [mm]`. Rewrite using `[adj_mul, adj_rat_inv b₀ hb, adj_ip]`.

Establish `hpu : ∀ w : Mx D r t, pr b₀ (yv V b₀ (z₁, z₂)) w = mm (ip V z₂ z₁) w`. Introduce `w`. Unfold `pr`. Rewrite using `[hu, hr]`. Simplify using `only [mm] at hPi ⊢`.

Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (rat b₀.1⁻¹), hPi, Matrix.one_mul]`. Establish `hpu' : ∀ w : Mx D r t, pr b₀ w (yv V b₀ (z₁, z₂)) = mm (adj w) (ip V z₁ z₂)`. Introduce `w`. Unfold `pr yv`. Rewrite using `[hr]`.

Simplify using `only [mm] at hPi' ⊢`. Rewrite using `[← Matrix.mul_assoc (rat b₀.1), hPi', Matrix.one_mul]`. Establish `hpyy : pr b₀ y y = mm (adj y) (mm (ip V z₁ z₁) y)`. Rewrite using `[hGy, pr, hr]`. Unfold `qv`.

Rewrite using `[hyv]`. Simplify using `only`. Rewrite using `[pr_add, hpu (yv V b₀ (z₁, z₂)), hpu y, hpu', hpyy, ip_add_left, ip_add_right, ip_add_right, ip_mul_left, ip_mul_left, ip_mul_right, ip_mul_right]`. Conclude with `alg4 _ _ _ _ _`.
-/
theorem qv_shear (V : HSp D) (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) (e : AE D) (z₁ : Mx D V.rank r) (z₂ : Mx D V.rank t)
    (y : Mx D r t) (hG : ip V z₁ z₁ = e • rat b₀.1) (hy : e • y = y) :
    qv V b₀ (z₁, z₂ + mm z₁ y) = qv V b₀ (z₁, z₂) := by
  have hr : (b₀.1.map (incA D)) = rat b₀.1 := rfl
  have hGy : mm (ip V z₁ z₁) y = mm (rat b₀.1) y := by
    rw [hG]
    simp only [mm]
    rw [Matrix.smul_mul, ← Matrix.mul_smul, hy]
  have hyv : yv V b₀ (z₁, z₂ + mm z₁ y) = yv V b₀ (z₁, z₂) + y := by
    unfold yv
    simp only
    rw [ip_add_right, ip_mul_right, hGy]
    simp only [mm]
    rw [Matrix.mul_add, ← Matrix.mul_assoc]
    have := rat_inv_mul b₀ hb
    simp only [mm] at this
    rw [this, Matrix.one_mul]
  have hPi := rat_inv_mul b₀ hb
  have hPi' := rat_mul_inv b₀ hb
  have hu : adj (yv V b₀ (z₁, z₂)) = mm (ip V z₂ z₁) (rat b₀.1⁻¹) := by
    unfold yv
    simp only [mm]
    rw [adj_mul, adj_rat_inv b₀ hb, adj_ip]
  have hpu : ∀ w : Mx D r t, pr b₀ (yv V b₀ (z₁, z₂)) w = mm (ip V z₂ z₁) w := by
    intro w
    unfold pr
    rw [hu, hr]
    simp only [mm] at hPi ⊢
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (rat b₀.1⁻¹), hPi, Matrix.one_mul]
  have hpu' : ∀ w : Mx D r t, pr b₀ w (yv V b₀ (z₁, z₂)) = mm (adj w) (ip V z₁ z₂) := by
    intro w
    unfold pr yv
    rw [hr]
    simp only [mm] at hPi' ⊢
    rw [← Matrix.mul_assoc (rat b₀.1), hPi', Matrix.one_mul]
  have hpyy : pr b₀ y y = mm (adj y) (mm (ip V z₁ z₁) y) := by
    rw [hGy, pr, hr]
  unfold qv
  rw [hyv]
  simp only
  rw [pr_add, hpu (yv V b₀ (z₁, z₂)), hpu y, hpu', hpyy, ip_add_left, ip_add_right, ip_add_right, ip_mul_left, ip_mul_left,
    ip_mul_right, ip_mul_right]
  exact alg4 _ _ _ _ _

/- English proof (translation)
Establish `hyv : yv V b₀ (z₁, mm z₂ g) = mm (yv V b₀ (z₁, z₂)) g`. Unfold `yv`. Simplify using `only`. Rewrite using `[ip_mul_right]`. Simplify using `only [mm]`.

Rewrite using `[Matrix.mul_assoc]`. Unfold `qv`. Rewrite using `[hyv]`. Simplify using `only`. Rewrite using `[ip_mul_left, ip_mul_right]`.

Unfold `pr`. Simplify using `only [mm]`. Rewrite using `[adj_mul, Matrix.mul_sub, Matrix.sub_mul]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem qv_col (V : HSp D) (b₀ : HermE D r) (z₁ : Mx D V.rank r) (z₂ : Mx D V.rank t) (g : Mx D t t) :
    qv V b₀ (z₁, mm z₂ g) = mm (mm (adj g) (qv V b₀ (z₁, z₂))) g := by
  have hyv : yv V b₀ (z₁, mm z₂ g) = mm (yv V b₀ (z₁, z₂)) g := by
    unfold yv
    simp only
    rw [ip_mul_right]
    simp only [mm]
    rw [Matrix.mul_assoc]
  unfold qv
  rw [hyv]
  simp only
  rw [ip_mul_left, ip_mul_right]
  unfold pr
  simp only [mm]
  rw [adj_mul, Matrix.mul_sub, Matrix.sub_mul]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Unfold `pch`. Use `congr 2`. Simplify using `only [mm]`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem pch_conj (ψ : AddChar (AF D.host.F) ℂ) (x q h : Mx D t t) :
    pch ψ x (mm (mm (adj h) q) h) = pch ψ (mm (mm h x) (adj h)) q := by
  unfold pch
  congr 2
  simp only [mm]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.OrbExist

end
