import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionEigenfunctionMaximalCompact

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp.B3

variable {D : D7} {n : ℕ} {v : Pl D}

/- English proof (translation)
Rewrite using `[blk4, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]`.
-/
theorem det_upper_triangular_block {A : Type} [CommRing A] {n : ℕ} (a b d : Matrix (Fin n) (Fin n) A) : (blk4 a b 0 d).det = a.det * d.det := by
  rw [blk4, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]

/- English proof (translation)
Rewrite using `[Formalism.UG.cT, Matrix.det_transpose]`. Conclude with `(RingHom.map_det s M).symm`.
-/
theorem det_cT {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (M : Matrix (Fin n) (Fin n) A) :
    (Formalism.UG.cT s M).det = s M.det := by
  rw [Formalism.UG.cT, Matrix.det_transpose]
  exact (RingHom.map_det s M).symm

/- English proof (translation)
Take `⟨a, b, c, d, e⟩` from `GlobalTheory.LocIntw.exists_blockMatrixTwoByTwoFin_eq (GlobalTheory.LocIntw.matR R σ p.1)`. Take `rfl : c = 0` from `Matrix.ext fun i j => by`. Use `GlobalTheory.LocIntw.lower_eq_zero p.2 i j` as an intermediate fact. Rewrite `this` using `[e, blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]`. Then use the resulting hypothesis. Establish `hu : Formalism.UG.cT (sigR R σ) (GlobalTheory.LocIntw.matR R σ p.1) * JR R Q * GlobalTheory.LocIntw.matR R σ p.1 = JR R Q` using `p.1.2`.

Rewrite `hu` using `[GlobalTheory.LocIntw.JR_eq R hQ, e, GlobalTheory.LocIntw.cT_blk4, GlobalTheory.LocIntw.cT_zero', StdUnn.Model.submatrix_fromBlocks_mul, StdUnn.Model.submatrix_fromBlocks_mul]`. Establish `hd : Formalism.UG.cT (sigR R σ) a * d = 1` using `by simpa using (StdUnn.Model.blockMatrixTwoByTwoFin_injective hu).2.1`. Establish `ha : (GlobalTheory.LocIntw.aUp R σ Q p : R ⊗[F] E) = a.det`. Rewrite using `[GlobalTheory.LocIntw.coe_aUp, e, GlobalTheory.LocIntw.upperLeft_blockMatrix]`. Use `⟨d.det, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[ha, e, det_upper_triangular_block]`. Establish `h5 : (Formalism.UG.cT (sigR R σ) a * d).det = 1` using `by rw [hd, Matrix.det_one]`. Rewrite `h5` using `[Matrix.det_mul, det_cT]`. Rewrite using `[ha]`. Conclude with `h5`.
-/
theorem exists_det_parabolic {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
    {σ : E →ₐ[F] E} {n : ℕ} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} (hQ : Q = blk4 0 1 (-1) 0)
    (p : GlobalTheory.LocIntw.upperParabolic R σ Q) : ∃ d : R ⊗[F] E,
      (GlobalTheory.LocIntw.matR R σ p.1).det = (GlobalTheory.LocIntw.aUp R σ Q p : R ⊗[F] E) * d ∧
      sigR R σ (GlobalTheory.LocIntw.aUp R σ Q p : R ⊗[F] E) * d = 1 := by
  obtain ⟨a, b, c, d, e⟩ := GlobalTheory.LocIntw.exists_blockMatrixTwoByTwoFin_eq (GlobalTheory.LocIntw.matR R σ p.1)
  obtain rfl : c = 0 := Matrix.ext fun i j => by
    have := GlobalTheory.LocIntw.lower_eq_zero p.2 i j
    rwa [e, blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
  have hu : Formalism.UG.cT (sigR R σ) (GlobalTheory.LocIntw.matR R σ p.1) * JR R Q * GlobalTheory.LocIntw.matR R σ p.1 = JR R Q := p.1.2
  rw [GlobalTheory.LocIntw.JR_eq R hQ, e, GlobalTheory.LocIntw.cT_blk4, GlobalTheory.LocIntw.cT_zero', StdUnn.Model.submatrix_fromBlocks_mul,
    StdUnn.Model.submatrix_fromBlocks_mul] at hu
  have hd : Formalism.UG.cT (sigR R σ) a * d = 1 := by simpa using (StdUnn.Model.blockMatrixTwoByTwoFin_injective hu).2.1
  have ha : (GlobalTheory.LocIntw.aUp R σ Q p : R ⊗[F] E) = a.det := by
    rw [GlobalTheory.LocIntw.coe_aUp, e, GlobalTheory.LocIntw.upperLeft_blockMatrix]
  refine ⟨d.det, ?_, ?_⟩
  · rw [ha, e, det_upper_triangular_block]
  · have h5 : (Formalism.UG.cT (sigR R σ) a * d).det = 1 := by rw [hd, Matrix.det_one]
    rw [Matrix.det_mul, det_cT] at h5
    rw [ha]
    exact h5

/- English proof (translation)
Establish `hc : c ≠ 0` using `right_ne_zero_of_mul_eq_one h1`. Conclude with `mul_right_cancel₀ hc (h1.trans h2.symm)`.
-/
theorem eq_of_mul_eq_one {a b c : ℝ} (h1 : a * c = 1) (h2 : b * c = 1) : a = b := by
  have hc : c ≠ 0 := right_ne_zero_of_mul_eq_one h1
  exact mul_right_cancel₀ hc (h1.trans h2.symm)

abbrev PV (D : D7) (n : ℕ) (v : Pl D) : Subgroup (GLoc D.sp.cm.sig (Jst D n) v) :=
  GlobalTheory.LocIntw.upperParabolic (Fv D.host.F v) D.sp.cm.sig (Jst D n)

abbrev aV (p : PV D n v) : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ :=
  GlobalTheory.LocIntw.aUp (Fv D.host.F v) D.sp.cm.sig (Jst D n) p

def lawV (χ : (AE D)ˣ →* Circle) (z : ℂ) (p : PV D n v) : ℂ :=
  (χ (ideleAt D.host.F D.host.E v (aV p)) : ℂ) * npow (absEv D.host.F D.host.E v (aV p)) (z + (n : ℂ) / 2)

/- English proof (translation)
Simplify using `only [lawV, aV, map_mul, Circle.coe_mul, npow_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lawV_mul (χ : (AE D)ˣ →* Circle) (z : ℂ) (p q : PV D n v) :
    lawV χ z (p * q) = lawV χ z p * lawV χ z q := by
  simp only [lawV, aV, map_mul, Circle.coe_mul, npow_mul]
  ring

/- English proof (translation)
Establish `h` using `hf (GlobalTheory.LocIntw.embUp v p).1 (GlobalTheory.LocIntw.embUp v p).2 (GlobalTheory.LocIntw.leviUp _ _ _ (GlobalTheory.LocIntw.embUp v p)) rfl g`. Establish `e : Matrix.GeneralLinearGroup.det (GlobalTheory.LocIntw.leviUp _ _ _ (GlobalTheory.LocIntw.embUp v p)) = ideleAt D.host.F D.host.E v (aV p)` using `GlobalTheory.LocIntw.aUp_embUp v p`. Establish `e2 : absA D (ideleAt D.host.F D.host.E v (aV p)) = absEv D.host.F D.host.E v (aV p)` using `absE_ideleAt v _`. Establish `e3 : (χ (Matrix.GeneralLinearGroup.det (GlobalTheory.LocIntw.leviUp _ _ _ (GlobalTheory.LocIntw.embUp v p))) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det (GlobalTheory.LocIntw.leviUp _ _ _ (GlobalTheory.LocIntw.embUp v p)))) (z + (n : ℂ) / 2) = lawV χ z p` using `(congrArg (fun y => (χ y : ℂ) * npow (absA D y) (z + (n : ℂ) / 2)) e).trans (congrArg (fun r => (χ (ideleAt D.host.F D.host.E v (aV p)) : ℂ) * npow r (z + (n : ℂ) / 2)) e2)`. Conclude with `h.trans (congrArg (· * f g) e3)`.
-/
theorem law_emb {χ : (AE D)ˣ →* Circle} {z : ℂ} {f : G D n → ℂ} (hf : IsLaw χ z f) (p : PV D n v) (g : G D n) :
    f (emb D.sp.cm.sig (Jst D n) v p * g) = lawV χ z p * f g := by
  have h := hf (GlobalTheory.LocIntw.embUp v p).1 (GlobalTheory.LocIntw.embUp v p).2
    (GlobalTheory.LocIntw.leviUp _ _ _ (GlobalTheory.LocIntw.embUp v p)) rfl g
  have e : Matrix.GeneralLinearGroup.det (GlobalTheory.LocIntw.leviUp _ _ _ (GlobalTheory.LocIntw.embUp v p)) =
      ideleAt D.host.F D.host.E v (aV p) := GlobalTheory.LocIntw.aUp_embUp v p
  have e2 : absA D (ideleAt D.host.F D.host.E v (aV p)) = absEv D.host.F D.host.E v (aV p) := absE_ideleAt v _
  have e3 : (χ (Matrix.GeneralLinearGroup.det (GlobalTheory.LocIntw.leviUp _ _ _ (GlobalTheory.LocIntw.embUp v p))) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det (GlobalTheory.LocIntw.leviUp _ _ _ (GlobalTheory.LocIntw.embUp v p)))) (z + (n : ℂ) / 2) =
      lawV χ z p :=
    (congrArg (fun y => (χ y : ℂ) * npow (absA D y) (z + (n : ℂ) / 2)) e).trans
      (congrArg (fun r => (χ (ideleAt D.host.F D.host.E v (aV p)) : ℂ) * npow r (z + (n : ℂ) / 2)) e2)
  exact h.trans (congrArg (· * f g) e3)

/- English proof (translation)
Establish `embK : ∀ {k : GLoc D.sp.cm.sig (Jst D n) v}, k ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v → emb D.sp.cm.sig (Jst D n) v k ∈ KAt D n v` using `fun hk => ⟨GlobalTheory.LocIntw.emb_mem_KUpAd hk, by rw [← range_emb]; exact ⟨_, rfl⟩⟩`. Choose the witnesses or unpack the hypotheses as in `⟨uv, rfl⟩ : ∃ uv, emb D.sp.cm.sig (Jst D n) v uv = u := by`. Rewrite `hu` using `[← range_emb]`. Conclude with `hu`. Rewrite `e₁` using `[proj_emb_self]`.

Take `⟨g', hg'⟩ : ∃ g' : G D n, g' = g * (emb D.sp.cm.sig (Jst D n) v (proj D.sp.cm.sig (Jst D n) v g))⁻¹` from `⟨_, rfl⟩`. Establish `h1 : proj D.sp.cm.sig (Jst D n) v g' = 1` using `by simp [hg']`. Establish `h2 : g = g' * emb D.sp.cm.sig (Jst D n) v p₀ * emb D.sp.cm.sig (Jst D n) v k₀`. Rewrite using `[mul_assoc, ← map_mul, ← e₀, hg', inv_mul_cancel_right]`. Establish `h3 : g * emb D.sp.cm.sig (Jst D n) v uv = g' * emb D.sp.cm.sig (Jst D n) v (p₀ * p₁) * emb D.sp.cm.sig (Jst D n) v k₁`.

Rewrite using `[h2]`. Simplify using `only [mul_assoc, ← map_mul, e₁]`. Establish `c : ∀ x : GLoc D.sp.cm.sig (Jst D n) v, g' * emb D.sp.cm.sig (Jst D n) v x = emb D.sp.cm.sig (Jst D n) v x * g'` using `fun x => (commute_emb D.sp.cm.sig (Jst D n) x h1).symm.eq`. Establish `h4 : f g = lawV χ z p₀ * f g'` using `by conv_lhs => rw [h2]`. Rewrite using `[hK _ (embK hk₀), c, law_emb hf]`.

Rewrite using `[h3, hK _ (embK hk₁), c, show ((p₀ : GLoc D.sp.cm.sig (Jst D n) v) * p₁) = ((p₀ * p₁ : PV D n v) : GLoc D.sp.cm.sig (Jst D n) v) from rfl, law_emb hf, lawV_mul, h4]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem shift {χ : (AE D)ˣ →* Circle} {z : ℂ} {f : G D n → ℂ} (hf : IsLaw χ z f)
    (hK : ∀ k ∈ KAt D n v, ∀ g, f (g * k) = f g) (g : G D n) (p₀ p₁ : PV D n v)
    {k₀ k₁ : GLoc D.sp.cm.sig (Jst D n) v} (hk₀ : k₀ ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v)
    (hk₁ : k₁ ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v)
    (e₀ : proj D.sp.cm.sig (Jst D n) v g = p₀ * k₀) {u : G D n} (hu : u ∈ atPts D.sp.cm.sig (Jst D n) {v})
    (e₁ : k₀ * proj D.sp.cm.sig (Jst D n) v u = p₁ * k₁) : f (g * u) = lawV χ z p₁ * f g := by
  have embK : ∀ {k : GLoc D.sp.cm.sig (Jst D n) v}, k ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v →
      emb D.sp.cm.sig (Jst D n) v k ∈ KAt D n v := fun hk =>
    ⟨GlobalTheory.LocIntw.emb_mem_KUpAd hk, by rw [← range_emb]; exact ⟨_, rfl⟩⟩
  obtain ⟨uv, rfl⟩ : ∃ uv, emb D.sp.cm.sig (Jst D n) v uv = u := by
    rw [← range_emb] at hu; exact hu
  rw [proj_emb_self] at e₁
  obtain ⟨g', hg'⟩ : ∃ g' : G D n, g' = g * (emb D.sp.cm.sig (Jst D n) v (proj D.sp.cm.sig (Jst D n) v g))⁻¹ := ⟨_, rfl⟩
  have h1 : proj D.sp.cm.sig (Jst D n) v g' = 1 := by simp [hg']
  have h2 : g = g' * emb D.sp.cm.sig (Jst D n) v p₀ * emb D.sp.cm.sig (Jst D n) v k₀ := by
    rw [mul_assoc, ← map_mul, ← e₀, hg', inv_mul_cancel_right]
  have h3 : g * emb D.sp.cm.sig (Jst D n) v uv =
      g' * emb D.sp.cm.sig (Jst D n) v (p₀ * p₁) * emb D.sp.cm.sig (Jst D n) v k₁ := by
    rw [h2]
    simp only [mul_assoc, ← map_mul, e₁]
  have c : ∀ x : GLoc D.sp.cm.sig (Jst D n) v, g' * emb D.sp.cm.sig (Jst D n) v x = emb D.sp.cm.sig (Jst D n) v x * g' :=
    fun x => (commute_emb D.sp.cm.sig (Jst D n) x h1).symm.eq
  have h4 : f g = lawV χ z p₀ * f g' := by
    conv_lhs => rw [h2]
    rw [hK _ (embK hk₀), c, law_emb hf]
  rw [h3, hK _ (embK hk₁), c, show ((p₀ : GLoc D.sp.cm.sig (Jst D n) v) * p₁) = ((p₀ * p₁ : PV D n v) : GLoc D.sp.cm.sig (Jst D n) v) from rfl,
    law_emb hf, lawV_mul, h4]
  ring

def dV (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (h : GLoc D.sp.cm.sig (Jst D n) v) : Fv D.host.F v :=
  splitProj τ (GlobalTheory.LocIntw.matR _ D.sp.cm.sig h).det

/- English proof (translation)
Rewrite using `[dV, dV, dV, GlobalTheory.LocIntw.matR_mul, Matrix.det_mul, map_mul]`.
-/
theorem dV_mul (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (h h' : GLoc D.sp.cm.sig (Jst D n) v) :
    dV τ (h * h') = dV τ h * dV τ h' := by
  rw [dV, dV, dV, GlobalTheory.LocIntw.matR_mul, Matrix.det_mul, map_mul]

/- English proof (translation)
Rewrite using `[dV, GlobalTheory.LocIntw.matR_one, Matrix.det_one, map_one]`.
-/
theorem dV_one (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : dV τ (1 : GLoc D.sp.cm.sig (Jst D n) v) = 1 := by
  rw [dV, GlobalTheory.LocIntw.matR_one, Matrix.det_one, map_one]

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Conclude with `S.sum_mem fun s _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)`.
-/
theorem det_mem_subring {R : Type} [CommRing R] (S : Subring R) {m : ℕ} {M : Matrix (Fin m) (Fin m) R}
    (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  exact S.sum_mem fun s _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)

/- English proof (translation)
Rewrite using `[GlobalTheory.LocIntw.blockMatrix_map, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _), show b.map φ = 0 from Matrix.ext h, StdUnn.Model.block_matrix_one]`.
-/
theorem map_blk_eq_one {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (b : Matrix (Fin n) (Fin n) A)
    (h : ∀ i j, φ (b i j) = 0) : (blk4 1 b 0 1).map φ = 1 := by
  rw [GlobalTheory.LocIntw.blockMatrix_map, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _),
    show b.map φ = 0 from Matrix.ext h, StdUnn.Model.block_matrix_one]

/- English proof (translation)
Take `⟨h1, h2⟩` from `mem_stabLoc_stdLattice_iff.1 hk`. Establish `a1 : ‖dV τ k‖₊ ≤ 1` using `nnnorm_le_one_iff_mem.2 (splitProj_mem τ (det_mem_subring _ h1))`. Establish `a2 : ‖dV τ k⁻¹‖₊ ≤ 1` using `nnnorm_le_one_iff_mem.2 (splitProj_mem τ (det_mem_subring _ h2))`. Establish `e : dV τ k * dV τ k⁻¹ = 1` using `by rw [← dV_mul, mul_inv_cancel, dV_one]`. Establish `b1 : ‖dV τ k‖ ≤ 1` using `by exact_mod_cast a1`.

Establish `b2 : ‖dV τ k⁻¹‖ ≤ 1` using `by exact_mod_cast a2`. Establish `e' : ‖dV τ k‖ * ‖dV τ k⁻¹‖ = 1` using `by rw [← norm_mul, e, norm_one]`. Use `le_antisymm b1 ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_dV_of_mem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) {k : GLoc D.sp.cm.sig (Jst D n) v}
    (hk : k ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v) : ‖dV τ k‖ = 1 := by
  obtain ⟨h1, h2⟩ := mem_stabLoc_stdLattice_iff.1 hk
  have a1 : ‖dV τ k‖₊ ≤ 1 := nnnorm_le_one_iff_mem.2 (splitProj_mem τ (det_mem_subring _ h1))
  have a2 : ‖dV τ k⁻¹‖₊ ≤ 1 := nnnorm_le_one_iff_mem.2 (splitProj_mem τ (det_mem_subring _ h2))
  have e : dV τ k * dV τ k⁻¹ = 1 := by rw [← dV_mul, mul_inv_cancel, dV_one]
  have b1 : ‖dV τ k‖ ≤ 1 := by exact_mod_cast a1
  have b2 : ‖dV τ k⁻¹‖ ≤ 1 := by exact_mod_cast a2
  have e' : ‖dV τ k‖ * ‖dV τ k⁻¹‖ = 1 := by rw [← norm_mul, e, norm_one]
  refine le_antisymm b1 ?_
  calc (1 : ℝ) = ‖dV τ k‖ * ‖dV τ k⁻¹‖ := e'.symm
    _ ≤ ‖dV τ k‖ * 1 := mul_le_mul_of_nonneg_left b2 (norm_nonneg _)
    _ = ‖dV τ k‖ := mul_one _

/- English proof (translation)
Use `mem_atPts.2 ⟨mem_finPts_iff_forall.2 fun w => GlobalTheory.LocIntw.ext_matR ?_, fun u hu => GlobalTheory.LocIntw.ext_matR ?_⟩` and prove the remaining obligations. Use `(GlobalTheory.LocIntw.matR_mapH (evInf D.host.F w) (nb x)).trans ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.LocIntw.matR_adele, hnb x, GlobalTheory.LocIntw.matR_one]`. Conclude with `map_blk_eq_one _ _ fun i j => C.inf x hx w i j`. Use `(GlobalTheory.LocIntw.matR_mapH (evFin D.host.F u) (nb x)).trans ?_` and prove the remaining obligations.

Rewrite using `[GlobalTheory.LocIntw.matR_adele, hnb x, GlobalTheory.LocIntw.matR_one]`. Conclude with `map_blk_eq_one _ _ fun i j => C.off x hx u (by simpa using hu) i j`.
-/
theorem nb_mem_atPts {nb : hermA D n → G D n} (hnb : IsNMap nb) (C : Cut D n v) {x : hermA D n} (hx : x ∈ C.s) :
    nb x ∈ atPts D.sp.cm.sig (Jst D n) {v} := by
  refine mem_atPts.2 ⟨mem_finPts_iff_forall.2 fun w => GlobalTheory.LocIntw.ext_matR ?_, fun u hu => GlobalTheory.LocIntw.ext_matR ?_⟩
  · refine (GlobalTheory.LocIntw.matR_mapH (evInf D.host.F w) (nb x)).trans ?_
    rw [GlobalTheory.LocIntw.matR_adele, hnb x, GlobalTheory.LocIntw.matR_one]
    exact map_blk_eq_one _ _ fun i j => C.inf x hx w i j
  · refine (GlobalTheory.LocIntw.matR_mapH (evFin D.host.F u) (nb x)).trans ?_
    rw [GlobalTheory.LocIntw.matR_adele, hnb x, GlobalTheory.LocIntw.matR_one]
    exact map_blk_eq_one _ _ fun i j => C.off x hx u (by simpa using hu) i j

/- English proof (translation)
Establish `h : GlobalTheory.LocIntw.matR _ D.sp.cm.sig (proj D.sp.cm.sig (Jst D n) v (nb x)) = _` using `GlobalTheory.LocIntw.matR_mapH (evFin D.host.F v) (nb x)`. Rewrite using `[dV, h, GlobalTheory.LocIntw.matR_adele, hnb x, GlobalTheory.LocIntw.blockMatrix_map, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _), det_upper_triangular_block, Matrix.det_one, mul_one, map_one]`.
-/
theorem dV_nb (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) {nb : hermA D n → G D n} (hnb : IsNMap nb) (x : hermA D n) :
    dV τ (proj D.sp.cm.sig (Jst D n) v (nb x)) = 1 := by
  have h : GlobalTheory.LocIntw.matR _ D.sp.cm.sig (proj D.sp.cm.sig (Jst D n) v (nb x)) = _ :=
    GlobalTheory.LocIntw.matR_mapH (evFin D.host.F v) (nb x)
  rw [dV, h, GlobalTheory.LocIntw.matR_adele, hnb x, GlobalTheory.LocIntw.blockMatrix_map, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_zero _ (map_zero _), det_upper_triangular_block, Matrix.det_one, mul_one, map_one]

/- English proof (translation)
Take `⟨d, h1, h2⟩` from `exists_det_parabolic (GlobalTheory.LocIntw.Jst_eq D n) p`. Establish `h3 : ‖splitProj τ ((aV p : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E)‖ * ‖splitProj τ d‖ = 1`. Rewrite using `[← norm_mul, ← map_mul]`. Conclude with `(congrArg (fun y => ‖splitProj τ y‖) h1.symm).trans hp`. Establish `h4 : ‖splitProj (τ.comp D.sp.cm.sig) ((aV p : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E)‖ * ‖splitProj τ d‖ = 1`.

Rewrite using `[splitProj_comp, ← norm_mul, ← map_mul]`. Conclude with `(congrArg (fun y => ‖splitProj τ y‖) h2).trans (by rw [map_one, norm_one])`. Conclude with `eq_of_mul_eq_one h3 h4`.
-/
theorem norm_split_eq (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (p : PV D n v) (hp : ‖dV τ p.1‖ = 1) :
    ‖splitProj τ ((aV p : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E)‖ =
      ‖splitProj (τ.comp D.sp.cm.sig) ((aV p : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E)‖ := by
  obtain ⟨d, h1, h2⟩ := exists_det_parabolic (GlobalTheory.LocIntw.Jst_eq D n) p
  have h3 : ‖splitProj τ ((aV p : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E)‖ * ‖splitProj τ d‖ = 1 := by
    rw [← norm_mul, ← map_mul]
    exact (congrArg (fun y => ‖splitProj τ y‖) h1.symm).trans hp
  have h4 : ‖splitProj (τ.comp D.sp.cm.sig) ((aV p : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E)‖ * ‖splitProj τ d‖ = 1 := by
    rw [splitProj_comp, ← norm_mul, ← map_mul]
    exact (congrArg (fun y => ‖splitProj τ y‖) h2).trans (by rw [map_one, norm_one])
  exact eq_of_mul_eq_one h3 h4

/- English proof (translation)
Use `hχ _ (norm_split_eq τ p₁ ?_)` and prove the remaining obligations. Establish `hk' : proj D.sp.cm.sig (Jst D n) v k ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v` using `(GlobalTheory.LocIntw.mem_KUpAd.1 hk.1).1 v`. Establish `h` using `congrArg (fun y => ‖dV τ y‖) e`. Simplify using `only [map_mul, dV_mul, dV_nb τ hnb, norm_mul, norm_one, norm_dV_of_mem τ hk₀, norm_dV_of_mem τ hk₁, norm_dV_of_mem τ hk', mul_one, one_mul] at h`. Conclude with `h.symm`.
-/
theorem chi_one {χ : (AE D)ˣ →* Circle} {τ : D.host.E →ₐ[D.host.F] Fv D.host.F v} (hχ : GoodChi D χ v τ)
    {nb : hermA D n → G D n} (hnb : IsNMap nb) {k₀ k₁ : GLoc D.sp.cm.sig (Jst D n) v}
    (hk₀ : k₀ ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v) (hk₁ : k₁ ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v)
    {k : G D n} (hk : k ∈ KAt D n v) (x : hermA D n) (p₁ : PV D n v)
    (e : k₀ * proj D.sp.cm.sig (Jst D n) v (k * nb x) = p₁ * k₁) :
    χ (ideleAt D.host.F D.host.E v (aV p₁)) = 1 := by
  refine hχ _ (norm_split_eq τ p₁ ?_)
  have hk' : proj D.sp.cm.sig (Jst D n) v k ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v :=
    (GlobalTheory.LocIntw.mem_KUpAd.1 hk.1).1 v
  have h := congrArg (fun y => ‖dV τ y‖) e
  simp only [map_mul, dV_mul, dV_nb τ hnb, norm_mul, norm_one, norm_dV_of_mem τ hk₀, norm_dV_of_mem τ hk₁,
    norm_dV_of_mem τ hk', mul_one, one_mul] at h
  exact h.symm

end GlobalTheory.CompanionTheory.Jp.B3

end
