import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCell
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicSumNondegenerateFrame
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StabInv

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

section Alg

variable {K : Type} [CommRing K] {M : ℕ}

def lowerB (U : Matrix (Fin (M + 2)) (Fin (M + 2)) K) : Matrix (Fin M) (Fin M) K :=
  Matrix.of fun i j => U i.succ.succ j.succ.succ

/- English proof (translation)
Use `congrFun h i` as an intermediate fact. Rewrite using `[← this]`. Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_succ]`.
-/
theorem col_zero {U : Matrix (Fin (M + 2)) (Fin (M + 2)) K}
    (h : U.mulVec (Fin.cons 1 fun _ => 0) = Fin.cons 1 fun _ => 0) (i : Fin (M + 2)) :
    U i 0 = (Fin.cons 1 (fun _ => 0) : Fin (M + 2) → K) i := by
  have := congrFun h i
  rw [← this]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/- English proof (translation)
Establish `h` using `congrFun (congrFun hU 0) j.succ.succ`. Establish `h1 : U 1 0 = 0` using `h0 1`. Establish `hr : ∀ i : Fin M, U i.succ.succ 0 = 0` using `fun i => h0 i.succ.succ`. Simplify using `only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, Fin.sum_univ_succ] at h`. Simplify `h` using `[hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest, hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest, h0 0, h1, hr]`.
-/
theorem row_one (s : K →+* K) (A : Matrix (Fin M) (Fin M) K)
    {U : Matrix (Fin (M + 2)) (Fin (M + 2)) K} (hU : cT s U * hypOne A * U = hypOne A)
    (h0 : ∀ i, U i 0 = (Fin.cons 1 (fun _ => 0) : Fin (M + 2) → K) i) (j : Fin M) :
    U 1 j.succ.succ = 0 := by
  have h := congrFun (congrFun hU 0) j.succ.succ
  have h1 : U 1 0 = 0 := h0 1
  have hr : ∀ i : Fin M, U i.succ.succ 0 = 0 := fun i => h0 i.succ.succ
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, Fin.sum_univ_succ] at h
  simpa [hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest,
      hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest, h0 0, h1, hr] using h

/- English proof (translation)
Use extensionality with `i j`. Establish `h` using `congrFun (congrFun hU i.succ.succ) j.succ.succ`. Establish `h1 : ∀ j : Fin M, U 1 j.succ.succ = 0` using `row_one s A hU h0`. Simplify using `only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, Fin.sum_univ_succ] at h ⊢`. Simplify `h` using `[lowerB, hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest, hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest, h1]`.
-/
theorem lowerB_isometry (s : K →+* K) (A : Matrix (Fin M) (Fin M) K)
    {U : Matrix (Fin (M + 2)) (Fin (M + 2)) K} (hU : cT s U * hypOne A * U = hypOne A)
    (h0 : ∀ i, U i 0 = (Fin.cons 1 (fun _ => 0) : Fin (M + 2) → K) i) :
    cT s (lowerB U) * A * lowerB U = A := by
  ext i j
  have h := congrFun (congrFun hU i.succ.succ) j.succ.succ
  have h1 : ∀ j : Fin M, U 1 j.succ.succ = 0 := row_one s A hU h0
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, Fin.sum_univ_succ] at h ⊢
  simpa [lowerB, hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest,
      hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest, h1] using h

/- English proof (translation)
Establish `e1 : U 1 0 = 0` using `h0 1`. Establish `er : ∀ i : Fin M, U i.succ.succ 0 = 0` using `fun i => h0 i.succ.succ`. Establish `e0 : U 0 0 = 1` using `h0 0`. Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i` and prove the remaining obligations.

Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_succ, e0]`. Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_succ, e1, h1]`. Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_succ, er, lowerB]`.
-/
theorem mulVec_cons (U : Matrix (Fin (M + 2)) (Fin (M + 2)) K)
    (h0 : ∀ i, U i 0 = (Fin.cons 1 (fun _ => 0) : Fin (M + 2) → K) i)
    (h1 : ∀ j : Fin M, U 1 j.succ.succ = 0) (a : K) (Y : Fin M → K) :
    U.mulVec (Fin.cons a (Fin.cons 0 Y)) =
      Fin.cons (a + ∑ i, U 0 i.succ.succ * Y i) (Fin.cons 0 ((lowerB U).mulVec Y)) := by
  have e1 : U 1 0 = 0 := h0 1
  have er : ∀ i : Fin M, U i.succ.succ 0 = 0 := fun i => h0 i.succ.succ
  have e0 : U 0 0 = 1 := h0 0
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, e0]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, e1, h1]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, er, lowerB]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Use `Fin.cases ?_ (fun j => ?_) k` and prove the remaining obligations. Simplify `hfix` using `[consA]`. Simplify `mulVec_cons U h0 h1 (a 0 j) (Y j)` using `[consA]`.
-/
theorem mulVec_consA {n : ℕ} (U : Matrix (Fin (M + 2)) (Fin (M + 2)) K)
    (hfix : U.mulVec (Fin.cons 1 fun _ => 0) = Fin.cons 1 fun _ => 0)
    (h0 : ∀ i, U i 0 = (Fin.cons 1 (fun _ => 0) : Fin (M + 2) → K) i)
    (h1 : ∀ j : Fin M, U 1 j.succ.succ = 0) (a : Fin 1 → Fin n → K) (Y : Fin n → Fin M → K) :
    (fun k => U.mulVec (consA a Y k)) =
      consA (a + fun _ j => ∑ i, U 0 i.succ.succ * Y j i) (fun j => (lowerB U).mulVec (Y j)) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simpa [consA] using hfix
  · simpa [consA] using mulVec_cons U h0 h1 (a 0 j) (Y j)

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>`. Use `Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j` and prove the remaining obligations. Use `all_goals`. Simplify using `[hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest, hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest]`.
-/
theorem map_hypOne {L : Type} [CommRing L] (f : K →+* L) (A : Matrix (Fin M) (Fin M) K) :
    (hypOne A).map f = hypOne (A.map f) := by
  ext i j
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
  all_goals
    simp [hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest,
      hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest]

end Alg

section Main

variable {F E : Type} [Field F] [Field E] [Algebra F E]

/- English proof (translation)
The claim follows from `map_hypOne (inclR R) J`.
-/
theorem JR_hypOne (R : Type) [CommRing R] [Algebra F R] {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    JR (F := F) R (hypOne J) = hypOne (JR (F := F) R J) :=
  map_hypOne (inclR R) J

/- English proof (translation)
Establish `hu : IsUnit J.det` using `isUnit_iff_ne_zero.mpr hJ`. Establish `hi : (J⁻¹).map (inclR (F` using `F) R) * JR (F := F) R J = 1 := by`. Establish `h1` using `congrArg (fun A : Matrix (Fin M) (Fin M) E => A.map (inclR (F := F) R)) (Matrix.nonsing_inv_mul J hu)`. Simplify `h1` using `[JR, Matrix.map_mul, Matrix.map_one]`. Establish `hl : ((J⁻¹).map (inclR (F` using `F) R) * cT (sigR R σ) κ * JR (F := F) R J) * κ = 1 := by`.

Combine the equalities or inequalities in the displayed calculation. Establish `hr` using `mul_eq_one_comm.mp hl`. Set `G : GL (Fin M) (R ⊗[F] E)` to `⟨κ, _, hr, hl⟩`. Establish `hG : G ∈ HR R σ J` using `hκ`. Conclude with `⟨(⟨G, hG⟩ : HR R σ J), rfl⟩`.
-/
theorem exists_HA (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : J.det ≠ 0) {κ : Matrix (Fin M) (Fin M) (R ⊗[F] E)}
    (hκ : cT (sigR R σ) κ * JR (F := F) R J * κ = JR (F := F) R J) :
    ∃ h : HA R σ J, ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = κ := by
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ
  have hi : (J⁻¹).map (inclR (F := F) R) * JR (F := F) R J = 1 := by
    have h1 := congrArg (fun A : Matrix (Fin M) (Fin M) E => A.map (inclR (F := F) R)) (Matrix.nonsing_inv_mul J hu)
    simpa [JR, Matrix.map_mul, Matrix.map_one] using h1
  have hl : ((J⁻¹).map (inclR (F := F) R) * cT (sigR R σ) κ * JR (F := F) R J) * κ = 1 := by
    calc ((J⁻¹).map (inclR (F := F) R) * cT (sigR R σ) κ * JR (F := F) R J) * κ
        = (J⁻¹).map (inclR (F := F) R) * (cT (sigR R σ) κ * JR (F := F) R J * κ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hκ, hi]
  have hr := mul_eq_one_comm.mp hl
  let G : GL (Fin M) (R ⊗[F] E) := ⟨κ, _, hr, hl⟩
  have hG : G ∈ HR R σ J := hκ
  exact ⟨(⟨G, hG⟩ : HR R σ J), rfl⟩

end Main

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm M J hJ R _ _ _ _ _ hL n d b lam hlam m₀ hm₀ φ hφ g g' hgg`. Use `haveI : IsTopologicalRing R := hL.1`. Use `haveI : LocallyCompactSpace R := hL.2.1`. Use `haveI : SecondCountableTopology R := hL.2.2.1`. Use `haveI : T2Space R := hL.2.2.2.1`.

Take `⟨tK1, tK2, tK3, tK4, -, -, -, tK8, -, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R`. Use `haveI := tK1`. Use `haveI := tK2`. Use `haveI := tK3`. Use `haveI := tK4`.

Use `haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩`. Use `haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := tK8 n M`. Use `haveI : BorelSpace (Fin 1 → Fin n → R ⊗[F] E) := tK8 1 n`. Use `haveI : BorelSpace (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) := tK8 (n + 1) (M + 2)`. Take `⟨-, hW, -⟩` from `GlobalTheory.T.coordinate_haar_measure F E σ hcm R d b lam hlam`.

Use `haveI := hW 1 n`. Take `⟨-, -, -, -, -, hA⟩` from `GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm (M + 2) (hypOne J) (isHermND_hypOne σ hJ) R`. Take `⟨-, -, -, -, -, hA'⟩` from `GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ R`. Take `⟨-, e1, em, -⟩` from `hA 1`. Take `⟨hc, -, hm, -⟩` from `hA (n + 1)`.

Take `⟨hc', -, -, -⟩` from `hA' n`. Use `set u : HA R σ (hypOne J) := g⁻¹ * g' with hu_def`. Establish `hg' : g' = g * u` using `by simp [hu_def]`. Establish `hfix : actW R σ (hypOne J) u (e0 _ M) = e0 _ M`. Rewrite using `[hu_def, em, ← hgg, ← em, inv_mul_cancel, e1]`.

Use `set U : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E) := (HA.mat R σ (hypOne J) u).val with hU_def`. Establish `hfixV : U.mulVec (Fin.cons 1 fun _ => 0) = Fin.cons 1 fun _ => 0` using `congrFun hfix 0`. Establish `h0` using `col_zero hfixV`. Establish `hUu : cT (sigR R σ) U * hypOne (JR (F` using `F) R J) * U = hypOne (JR (F := F) R J) := by`. Rewrite using `[← JR_hypOne]`.

Conclude with `(show HR R σ (hypOne J) from u).2`. Establish `h1` using `row_one _ _ hUu h0`. Apply the tactic sequence `obtain ⟨k, hk⟩ := exists_HA R σ hJ.2 (lowerB_isometry _ _ hUu h0)`. Establish `hact : ∀ (a : Fin 1 → Fin n → R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E), actW R σ (hypOne J) u (consA a Y) = consA (a + fun _ j => ∑ i, U 0 i.succ.succ * Y j i) (actW R σ J k Y)`. Introduce `a Y`.

Use `mulVec_consA U hfixV h0 h1 a Y` as an intermediate fact. Establish `e : actW R σ J k Y = fun j => (lowerB U).mulVec (Y j)`. Use function extensionality and compare the values at `j`. Simplify using `only [actW, actTup, hk]`. Rewrite using `[e, ← this]`.

Both sides reduce to the same expression. Set `G : (Fin n → Fin M → R ⊗[F] E) → ℝ≥0∞` to `fun Y => ∫⁻ a, φ (actW R σ (hypOne J) g (consA a Y)) ∂(coordW R b lam 1 n)`. Establish `hcons : Continuous fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) => (consA p.2 p.1 : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E)`. Use `continuous_pi fun k => continuous_pi fun i => ?_` and prove the remaining obligations. Use `Fin.cases ?_ (fun j => ?_) k` and prove the remaining obligations.

Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> simpa [consA] using continuous_const`. Use `Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i` and prove the remaining obligations. Simplify using `only [consA, Fin.cons_succ, Fin.cons_zero] fun_prop`. Simplify `continuous_const` using `[consA]`. Simplify using `only [consA, Fin.cons_succ] fun_prop`.

Establish `hGm : Measurable G`. Establish `hf : Measurable fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) => φ (actW R σ (hypOne J) g (consA p.2 p.1))` using `hφ.comp (hc.comp (continuous_const.prodMk hcons)).measurable`. Conclude with `hf.lintegral_prod_right'`. Establish `hkm : Measurable (actW R σ J k : (Fin n → Fin M → R ⊗[F] E) → _)` using `(hc'.comp (continuous_const.prodMk continuous_id)).measurable`. Establish `hinner : ∀ Y, (∫⁻ a, φ (actW R σ (hypOne J) g' (consA a Y)) ∂(coordW R b lam 1 n)) = G (actW R σ J k Y)`.

Introduce `Y`. Establish `: ∀ a, actW R σ (hypOne J) g' (consA a Y) = actW R σ (hypOne J) g (consA (a + fun _ j => ∑ i, U 0 i.succ.succ * Y j i) (actW R σ J k Y))`. Introduce `a`. Rewrite using `[hg', hm, hact]`. Simplify using `only [this]`.

Conclude with `lintegral_add_right_eq_self (fun a => φ (actW R σ (hypOne J) g (consA a (actW R σ J k Y)))) _`. Use `show (∫⁻ Y, G Y ∂m₀) = ∫⁻ Y, (∫⁻ a, φ (actW R σ (hypOne J) g' (consA a Y)) ∂(coordW R b lam 1 n)) ∂m₀`. Simplify using `only [hinner]`. Rewrite using `[← lintegral_map hGm hkm, hm₀ k]`.
-/
theorem stageInt_eq_of_e0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m₀ : Measure (Fin n → Fin M → R ⊗[F] E), (∀ h : HA R σ J, m₀.map (actW R σ J h) = m₀) → ∀ φ : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ g g' : HA R σ (hypOne J), actW R σ (hypOne J) g (e0 _ M) = actW R σ (hypOne J) g' (e0 _ M) → stageInt R σ J b lam m₀ φ g = stageInt R σ J b lam m₀ φ g' := by
  intro F E _ _ _ _ _ σ hcm M J hJ R _ _ _ _ _ hL n d b lam hlam m₀ hm₀ φ hφ g g' hgg
  haveI : IsTopologicalRing R := hL.1
  haveI : LocallyCompactSpace R := hL.2.1
  haveI : SecondCountableTopology R := hL.2.2.1
  haveI : T2Space R := hL.2.2.2.1
  obtain ⟨tK1, tK2, tK3, tK4, -, -, -, tK8, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  haveI := tK1
  haveI := tK2
  haveI := tK3
  haveI := tK4
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := tK8 n M
  haveI : BorelSpace (Fin 1 → Fin n → R ⊗[F] E) := tK8 1 n
  haveI : BorelSpace (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) := tK8 (n + 1) (M + 2)
  obtain ⟨-, hW, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm R d b lam hlam
  haveI := hW 1 n
  obtain ⟨-, -, -, -, -, hA⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm (M + 2) (hypOne J) (isHermND_hypOne σ hJ) R
  obtain ⟨-, -, -, -, -, hA'⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ R
  obtain ⟨-, e1, em, -⟩ := hA 1
  obtain ⟨hc, -, hm, -⟩ := hA (n + 1)
  obtain ⟨hc', -, -, -⟩ := hA' n

  set u : HA R σ (hypOne J) := g⁻¹ * g' with hu_def
  have hg' : g' = g * u := by simp [hu_def]
  have hfix : actW R σ (hypOne J) u (e0 _ M) = e0 _ M := by
    rw [hu_def, em, ← hgg, ← em, inv_mul_cancel, e1]
  set U : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E) :=
    (HA.mat R σ (hypOne J) u).val with hU_def
  have hfixV : U.mulVec (Fin.cons 1 fun _ => 0) = Fin.cons 1 fun _ => 0 := congrFun hfix 0
  have h0 := col_zero hfixV
  have hUu : cT (sigR R σ) U * hypOne (JR (F := F) R J) * U = hypOne (JR (F := F) R J) := by
    rw [← JR_hypOne]
    exact (show HR R σ (hypOne J) from u).2
  have h1 := row_one _ _ hUu h0
  obtain ⟨k, hk⟩ := exists_HA R σ hJ.2 (lowerB_isometry _ _ hUu h0)

  have hact : ∀ (a : Fin 1 → Fin n → R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E),
      actW R σ (hypOne J) u (consA a Y) =
        consA (a + fun _ j => ∑ i, U 0 i.succ.succ * Y j i) (actW R σ J k Y) := by
    intro a Y
    have := mulVec_consA U hfixV h0 h1 a Y
    have e : actW R σ J k Y = fun j => (lowerB U).mulVec (Y j) := by
      funext j
      simp only [actW, actTup, hk]
    rw [e, ← this]
    rfl

  let G : (Fin n → Fin M → R ⊗[F] E) → ℝ≥0∞ := fun Y =>
    ∫⁻ a, φ (actW R σ (hypOne J) g (consA a Y)) ∂(coordW R b lam 1 n)
  have hcons : Continuous fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) =>
      (consA p.2 p.1 : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) := by
    refine continuous_pi fun k => continuous_pi fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) k
    · refine Fin.cases ?_ (fun i => ?_) i <;> simpa [consA] using continuous_const
    · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
      · simp only [consA, Fin.cons_succ, Fin.cons_zero]
        fun_prop
      · simpa [consA] using continuous_const
      · simp only [consA, Fin.cons_succ]
        fun_prop
  have hGm : Measurable G := by
    have hf : Measurable fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) =>
        φ (actW R σ (hypOne J) g (consA p.2 p.1)) :=
      hφ.comp (hc.comp (continuous_const.prodMk hcons)).measurable
    exact hf.lintegral_prod_right'
  have hkm : Measurable (actW R σ J k : (Fin n → Fin M → R ⊗[F] E) → _) :=
    (hc'.comp (continuous_const.prodMk continuous_id)).measurable
  have hinner : ∀ Y, (∫⁻ a, φ (actW R σ (hypOne J) g' (consA a Y)) ∂(coordW R b lam 1 n)) =
      G (actW R σ J k Y) := by
    intro Y
    have : ∀ a, actW R σ (hypOne J) g' (consA a Y) =
        actW R σ (hypOne J) g (consA (a + fun _ j => ∑ i, U 0 i.succ.succ * Y j i) (actW R σ J k Y)) := by
      intro a
      rw [hg', hm, hact]
    simp only [this]
    exact lintegral_add_right_eq_self
      (fun a => φ (actW R σ (hypOne J) g (consA a (actW R σ J k Y)))) _
  show (∫⁻ Y, G Y ∂m₀) = ∫⁻ Y, (∫⁻ a, φ (actW R σ (hypOne J) g' (consA a Y)) ∂(coordW R b lam 1 n)) ∂m₀
  simp only [hinner]
  rw [← lintegral_map hGm hkm, hm₀ k]

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StabInv
