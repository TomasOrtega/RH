import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDatumCarriedBackToBaseVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFixAndKillThetaOffSupportMove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceComapUnitarySupported
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCX
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.NormDetLeFactorialMulProd

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

noncomputable section
namespace GlobalTheory.CompanionTheory.Ipf.Bdd
variable {D : D7}

def _root_.GlobalTheory.CompanionTheory.Ipf.mul {a b c : ℕ} (x : Mx D a b) (y : Mx D b c) : Mx D a c :=
  HMul.hMul (x : Matrix (Fin a) (Fin b) (AE D)) (y : Matrix (Fin b) (Fin c) (AE D))

def _root_.GlobalTheory.CompanionTheory.Ipf.rat {a b : ℕ} (γ : Matrix (Fin a) (Fin b) D.host.E) : Mx D a b := γ.map (incA D)

/- English proof (translation)
Simplify using `[infPart, incA, inclR]`.
-/
theorem infPart_incA (c : D.host.E) : infPart D (incA D c) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] c := by
  simp [infPart, incA, inclR]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x => rfl`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem infPart_cA (z : AE D) : infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Unfold `compAt mul`. Conclude with `Matrix.map_mul (f := (θ τ).comp (infPart D))`.
-/
theorem compAt_mulM {m k n : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (A : Mx D m k) (B : Mx D k n) :
    compAt θ τ (mul A B) = compAt θ τ A * compAt θ τ B := by
  unfold compAt mul
  exact Matrix.map_mul (f := (θ τ).comp (infPart D))

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [compAt, rat, Matrix.map_apply]`. Rewrite using `[infPart_incA]`. Conclude with `(hθ τ).1 _`.
-/
theorem compAt_rat {m k : ℕ} {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (γ : Matrix (Fin m) (Fin k) D.host.E) :
    compAt θ τ (rat γ) = γ.map (tauE D τ) := by
  ext i j
  simp only [compAt, rat, Matrix.map_apply]
  rw [infPart_incA]
  exact (hθ τ).1 _

/- English proof (translation)
Establish `h : ((mt V g).map (cA D))ᵀ * V.gram.map (incA D) * mt V g = V.gram.map (incA D)` using `g.2`. Use `set ρ : AE D →+* ℂ := (θ τ).comp (infPart D) with hρ`. Establish `hc : ∀ z, ρ (cA D z) = starRingEnd ℂ (ρ z)` using `fun z => by`. Simplify using `only [hρ, RingHom.comp_apply]`. Rewrite using `[infPart_cA]`.

Conclude with `GlobalTheory.Mem.VolExists.infEmb_sigR (GlobalTheory.DefiniteQuotient.cmExt D) (hθ τ) _`. Establish `hd` using `congrArg (fun M => ρ M.det) h`. Simplify using `only [Matrix.det_mul, Matrix.det_transpose, map_mul] at hd`. Establish `e1 : ρ (((mt V g).map (cA D)).det) = starRingEnd ℂ (ρ (mt V g).det)`. Rewrite using `[← hc]`.

Use `congr 1`. Conclude with `((cA D).map_det _).symm`. Establish `e2 : ρ (V.gram.map (incA D)).det ≠ 0`. Establish `: (V.gram.map (incA D)).det = incA D V.gram.det` using `((incA D).map_det _).symm`. Rewrite using `[this]`.

Establish `: ρ (incA D V.gram.det) = tauE D τ V.gram.det`. Simplify using `only [hρ, RingHom.comp_apply]`. Rewrite using `[infPart_incA]`. Conclude with `(hθ τ).1 _`. Rewrite using `[this]`.

Conclude with `(map_ne_zero _).2 (GlobalTheory.StabCompact.det_gram_ne_zero V)`. Establish `e3 : (compAt θ τ (mt V g)).det = ρ (mt V g).det` using `(ρ.map_det _).symm`. Rewrite using `[e3]`. Rewrite `hd` using `[e1]`. Establish `h4 : starRingEnd ℂ (ρ (mt V g).det) * ρ (mt V g).det = 1`.

Use `mul_right_cancel₀ e2 ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite `h4` using `[Complex.conj_mul']`. Establish `h5 : (‖ρ (mt V g).det‖ : ℝ) ^ 2 = 1` using `by exact_mod_cast h4`. Establish `h6 : (0 : ℝ) ≤ ‖ρ (mt V g).det‖` using `norm_nonneg _`.

Use polynomial arithmetic with `[sq_nonneg (‖ρ (mt V g).det‖ - 1), sq_nonneg (‖ρ (mt V g).det‖ + 1)]`.
-/
theorem norm_det_compAt {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (V : HSp D) (g : GA D V) :
    ‖(compAt θ τ (mt V g)).det‖ = 1 := by
  have h : ((mt V g).map (cA D))ᵀ * V.gram.map (incA D) * mt V g = V.gram.map (incA D) := g.2
  set ρ : AE D →+* ℂ := (θ τ).comp (infPart D) with hρ
  have hc : ∀ z, ρ (cA D z) = starRingEnd ℂ (ρ z) := fun z => by
    simp only [hρ, RingHom.comp_apply]
    rw [infPart_cA]
    exact GlobalTheory.Mem.VolExists.infEmb_sigR (GlobalTheory.DefiniteQuotient.cmExt D) (hθ τ) _
  have hd := congrArg (fun M => ρ M.det) h
  simp only [Matrix.det_mul, Matrix.det_transpose, map_mul] at hd
  have e1 : ρ (((mt V g).map (cA D)).det) = starRingEnd ℂ (ρ (mt V g).det) := by
    rw [← hc]
    congr 1
    exact ((cA D).map_det _).symm
  have e2 : ρ (V.gram.map (incA D)).det ≠ 0 := by
    have : (V.gram.map (incA D)).det = incA D V.gram.det := ((incA D).map_det _).symm
    rw [this]
    have : ρ (incA D V.gram.det) = tauE D τ V.gram.det := by
      simp only [hρ, RingHom.comp_apply]
      rw [infPart_incA]
      exact (hθ τ).1 _
    rw [this]
    exact (map_ne_zero _).2 (GlobalTheory.StabCompact.det_gram_ne_zero V)
  have e3 : (compAt θ τ (mt V g)).det = ρ (mt V g).det := (ρ.map_det _).symm
  rw [e3]
  rw [e1] at hd
  have h4 : starRingEnd ℂ (ρ (mt V g).det) * ρ (mt V g).det = 1 := by
    refine mul_right_cancel₀ e2 ?_
    calc _ = starRingEnd ℂ (ρ (mt V g).det) * ρ (V.gram.map (incA D)).det * ρ (mt V g).det := by ring
      _ = ρ (V.gram.map (incA D)).det := hd
      _ = _ := by ring
  rw [Complex.conj_mul'] at h4
  have h5 : (‖ρ (mt V g).det‖ : ℝ) ^ 2 = 1 := by exact_mod_cast h4
  have h6 : (0 : ℝ) ≤ ‖ρ (mt V g).det‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖ρ (mt V g).det‖ - 1), sq_nonneg (‖ρ (mt V g).det‖ + 1)]

/- English proof (translation)
Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.StabFin.addGrpF (F := D.host.F) (E := D.host.E)` as an intermediate fact. Establish `h1 : IsOpen {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E | z ∈ intAE D}`. Use `GlobalTheory.IdeleParts.isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E 1 one_pos` as an intermediate fact. Rewrite `this` using `[← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]`. Establish `e : {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E | z ∈ intAE D} = {z | ∃ y ∈ intAE D, z = 1 • y}`.

Use extensionality with `z`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `this`. Conclude with `h1.preimage (continuous_nsmul N)`.
-/
theorem isOpen_nsmul_mem (N : ℕ) :
    IsOpen {y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E | N • y ∈ intAE D} := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.StabFin.addGrpF (F := D.host.F) (E := D.host.E)
  have h1 : IsOpen {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E | z ∈ intAE D} := by
    have := GlobalTheory.IdeleParts.isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E 1 one_pos
    rw [← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers] at this
    have e : {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E | z ∈ intAE D} = {z | ∃ y ∈ intAE D, z = 1 • y} := by
      ext z
      simp
    rw [e]
    exact this
  exact h1.preimage (continuous_nsmul N)

/- English proof (translation)
Take `⟨n, hn, h⟩` from `GlobalTheory.IwaPlace.SdComap.exists_natCast_mul_mem_intAE (D := D) z`. Conclude with `⟨n, hn, by rwa [nsmul_eq_mul]⟩`.
-/
theorem den_one (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) : ∃ N : ℕ, 0 < N ∧ N • z ∈ intAE D := by
  obtain ⟨n, hn, h⟩ := GlobalTheory.IwaPlace.SdComap.exists_natCast_mul_mem_intAE (D := D) z
  exact ⟨n, hn, by rwa [nsmul_eq_mul]⟩

/- English proof (translation)
Use `hK.induction_on (p := fun S => ∃ N : ℕ, 0 < N ∧ ∀ x ∈ S, N • x ∈ intAE D) ⟨1, one_pos, by simp⟩ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `s t hst ⟨N, hN, h⟩`. Conclude with `⟨N, hN, fun x hx => h x (hst hx)⟩`. Introduce and unpack `s t ⟨N, hN, h⟩ ⟨M, hM, h'⟩`. Use `⟨N * M, by positivity, ?_⟩` and prove the remaining obligations.

Introduce and unpack `x (hx | hx)`. Rewrite using `[mul_comm, mul_smul]`. Conclude with `AddSubgroup.nsmul_mem _ (h x hx) M`. Rewrite using `[mul_smul]`. Conclude with `AddSubgroup.nsmul_mem _ (h' x hx) N`.

Introduce `x _`. Take `⟨N, hN, hx⟩` from `den_one x`. Conclude with `⟨_, mem_nhdsWithin_of_mem_nhds ((isOpen_nsmul_mem N).mem_nhds hx), N, hN, fun y hy => hy⟩`.
-/
theorem exists_den {K : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)} (hK : IsCompact K) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ K, N • x ∈ intAE D := by
  refine hK.induction_on (p := fun S => ∃ N : ℕ, 0 < N ∧ ∀ x ∈ S, N • x ∈ intAE D)
    ⟨1, one_pos, by simp⟩ ?_ ?_ ?_
  · rintro s t hst ⟨N, hN, h⟩
    exact ⟨N, hN, fun x hx => h x (hst hx)⟩
  · rintro s t ⟨N, hN, h⟩ ⟨M, hM, h'⟩
    refine ⟨N * M, by positivity, ?_⟩
    rintro x (hx | hx)
    · rw [mul_comm, mul_smul]
      exact AddSubgroup.nsmul_mem _ (h x hx) M
    · rw [mul_smul]
      exact AddSubgroup.nsmul_mem _ (h' x hx) N
  · intro x _
    obtain ⟨N, hN, hx⟩ := den_one x
    exact ⟨_, mem_nhdsWithin_of_mem_nhds ((isOpen_nsmul_mem N).mem_nhds hx), N, hN, fun y hy => hy⟩

def intR (D : D7) : Subring D.host.E := (algebraMap (𝓞 D.host.E) D.host.E).range

/- English proof (translation)
Establish `h1` using `(GlobalTheory.SplitDec.rat_int_iff (D := D) a).1 ((GlobalTheory.SplitDec.int_iff _).1 h)`. Take `⟨y, hy⟩` from `Submodule.mem_one.1 h1`. Conclude with `⟨y, hy⟩`.
-/
theorem mem_intR_of_finPart {a : D.host.E} (h : finPart D (incA D a) ∈ intAE D) : a ∈ intR D := by
  have h1 := (GlobalTheory.SplitDec.rat_int_iff (D := D) a).1 ((GlobalTheory.SplitDec.int_iff _).1 h)
  obtain ⟨y, hy⟩ := Submodule.mem_one.1 h1
  exact ⟨y, hy⟩

/- English proof (translation)
Take `⟨r, rfl⟩` from `hz`. Establish `h1` using `NumberField.InfinitePlace.prod_eq_abs_norm (algebraMap (𝓞 D.host.E) D.host.E r)`. Establish `hb` using `Formalism.L2.Fam.ThC.plE_bij D`. Establish `h2 : ∏ w : InfinitePlace D.host.E, w (algebraMap (𝓞 D.host.E) D.host.E r) ^ w.mult = ∏ τ, ‖tauE D τ (algebraMap (𝓞 D.host.E) D.host.E r)‖ ^ 2`. Rewrite using `[← hb.prod_comp]`.

Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[InfinitePlace.mult, if_neg (by simpa [InfinitePlace.isComplex_iff] using Formalism.L2.Fam.ThC.plE_complex τ)]`. Both sides reduce to the same expression. Establish `hr : r ≠ 0` using `fun e => h0 (by rw [e, map_zero])`. Establish `h3 : (1 : ℝ) ≤ |((Algebra.norm ℚ (algebraMap (𝓞 D.host.E) D.host.E r) : ℚ) : ℝ)|`.

Establish `e` using `Algebra.coe_norm_int r`. Establish `hn : Algebra.norm ℤ r ≠ 0` using `Algebra.norm_ne_zero_iff.2 hr`. Establish `e' : (algebraMap (𝓞 D.host.E) D.host.E r) = (r : D.host.E)` using `rfl`. Rewrite using `[e', ← e]`. Establish `: (1 : ℤ) ≤ |Algebra.norm ℤ r|` using `Int.one_le_abs hn`.

Establish `h' : ((1 : ℤ) : ℝ) ≤ ((|Algebra.norm ℤ r| : ℤ) : ℝ)` using `by exact_mod_cast this`. Simplify using `using h'`. Establish `h4 : (1 : ℝ) ≤ (∏ τ, ‖tauE D τ (algebraMap (𝓞 D.host.E) D.host.E r)‖) ^ 2`. Rewrite using `[← Finset.prod_pow, ← h2, h1]`. Conclude with `h3` after adjusting the coercions.

Establish `h5 : (0 : ℝ) ≤ ∏ τ, ‖tauE D τ (algebraMap (𝓞 D.host.E) D.host.E r)‖` using `Finset.prod_nonneg fun _ _ => norm_nonneg _`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem one_le_prod_tauE (z : D.host.E) (hz : z ∈ intR D) (h0 : z ≠ 0) : 1 ≤ ∏ τ, ‖tauE D τ z‖ := by
  obtain ⟨r, rfl⟩ := hz
  have h1 := NumberField.InfinitePlace.prod_eq_abs_norm (algebraMap (𝓞 D.host.E) D.host.E r)
  have hb := Formalism.L2.Fam.ThC.plE_bij D
  have h2 : ∏ w : InfinitePlace D.host.E, w (algebraMap (𝓞 D.host.E) D.host.E r) ^ w.mult =
      ∏ τ, ‖tauE D τ (algebraMap (𝓞 D.host.E) D.host.E r)‖ ^ 2 := by
    rw [← hb.prod_comp]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [InfinitePlace.mult, if_neg (by simpa [InfinitePlace.isComplex_iff] using Formalism.L2.Fam.ThC.plE_complex τ)]
    rfl
  have hr : r ≠ 0 := fun e => h0 (by rw [e, map_zero])
  have h3 : (1 : ℝ) ≤ |((Algebra.norm ℚ (algebraMap (𝓞 D.host.E) D.host.E r) : ℚ) : ℝ)| := by
    have e := Algebra.coe_norm_int r
    have hn : Algebra.norm ℤ r ≠ 0 := Algebra.norm_ne_zero_iff.2 hr
    have e' : (algebraMap (𝓞 D.host.E) D.host.E r) = (r : D.host.E) := rfl
    rw [e', ← e]
    have : (1 : ℤ) ≤ |Algebra.norm ℤ r| := Int.one_le_abs hn
    have h' : ((1 : ℤ) : ℝ) ≤ ((|Algebra.norm ℤ r| : ℤ) : ℝ) := by exact_mod_cast this
    simpa using h'
  have h4 : (1 : ℝ) ≤ (∏ τ, ‖tauE D τ (algebraMap (𝓞 D.host.E) D.host.E r)‖) ^ 2 := by
    rw [← Finset.prod_pow, ← h2, h1]
    exact_mod_cast h3
  have h5 : (0 : ℝ) ≤ ∏ τ, ‖tauE D τ (algebraMap (𝓞 D.host.E) D.host.E r)‖ :=
    Finset.prod_nonneg fun _ _ => norm_nonneg _
  nlinarith

/- English proof (translation)
Rewrite `*` using `[GlobalTheory.IdemSupport.mem_intAE_iff]`. Rewrite using `[map_mul]`. Conclude with `mul_mem hx hy`.
-/
theorem mul_mem_int {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  rw [GlobalTheory.IdemSupport.mem_intAE_iff] at *
  rw [map_mul]
  exact mul_mem hx hy

/- English proof (translation)
Establish `h : ∀ p : Fin a × Fin b, ∃ N : ℕ, 0 < N ∧ ∀ x ∈ (fun m : Matrix (Fin a) (Fin b) _ => m p.1 p.2) '' K, N • x ∈ intAE D` using `fun p => exists_den (hK.image (continuous_id.matrix_elem p.1 p.2))`. Use `choose N hN h using h`. Use `⟨∏ p, N p, Finset.prod_pos fun p _ => hN p, fun m hm i j => ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ (i, j)), mul_comm, mul_smul]`. Conclude with `AddSubgroup.nsmul_mem _ (h (i, j) _ ⟨m, hm, rfl⟩) _`.
-/
theorem exists_den_matrix {a b : ℕ}
    {K : Set (Matrix (Fin a) (Fin b) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))} (hK : IsCompact K) :
    ∃ N : ℕ, 0 < N ∧ ∀ m ∈ K, ∀ i j, N • m i j ∈ intAE D := by
  have h : ∀ p : Fin a × Fin b, ∃ N : ℕ, 0 < N ∧ ∀ x ∈ (fun m : Matrix (Fin a) (Fin b) _ => m p.1 p.2) '' K, N • x ∈ intAE D :=
    fun p => exists_den (hK.image (continuous_id.matrix_elem p.1 p.2))
  choose N hN h using h
  refine ⟨∏ p, N p, Finset.prod_pos fun p _ => hN p, fun m hm i j => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (i, j)), mul_comm, mul_smul]
  exact AddSubgroup.nsmul_mem _ (h (i, j) _ ⟨m, hm, rfl⟩) _

/- English proof (translation)
Assemble the required witnesses or components as `⟨D.eTau.symm (Classical.arbitrary _)⟩`.
-/
theorem nonempty_tau (D : D7) : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩

end GlobalTheory.CompanionTheory.Ipf.Bdd

end
