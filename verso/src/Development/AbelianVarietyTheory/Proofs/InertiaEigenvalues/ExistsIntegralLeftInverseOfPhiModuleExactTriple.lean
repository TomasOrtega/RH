import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

open PowerSeries GlobalTheory.BK Matrix

namespace GlobalTheory.BK.IntegralLeftInverseExactTriple

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/- English proof (translation)
Use `mem_tot.2 fun σ => mem_vecs.2 fun i => ?_` and prove the remaining obligations. Distinguish the cases in `h : σ = τ`. Substitute `h` using the available equality. Simplify using `using hu i`. Rewrite using `[Pi.single_eq_of_ne h]`.

Conclude with `zero_mem _`.
-/
theorem mem_M_single (P : PhiMod O K l e a ι) (τ : ZMod a) (u : ι → K⟦X⟧)
    (hu : ∀ i, u i ∈ A O K) : (Pi.single τ u : Vec K a ι) ∈ P.M := by
  refine mem_tot.2 fun σ => mem_vecs.2 fun i => ?_
  by_cases h : σ = τ
  · subst h; simpa using hu i
  · rw [Pi.single_eq_of_ne h]; exact zero_mem _

/- English proof (translation)
Use function extensionality and compare the values at `σ`. Rewrite using `[Hom.app_apply]`. Distinguish the cases in `h : σ = τ`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Pi.single_eq_of_ne h]`.
-/
theorem app_single {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q) (τ : ZMod a)
    (u : ι → K⟦X⟧) : F.app (Pi.single τ u) = Pi.single τ (F.mat τ *ᵥ u) := by
  funext σ
  rw [Hom.app_apply]
  by_cases h : σ = τ
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

/- English proof (translation)
Rewrite using `[Matrix.smul_apply, Matrix.one_apply]`. Use `split_ifs`. Rewrite using `[show ((l : K) ^ n) • (1 : K⟦X⟧) = ((l ^ n : ℕ) : K⟦X⟧) by simp [Algebra.smul_def]]`. Conclude with `natCast_mem _ _`. Rewrite using `[smul_zero]`.

Conclude with `zero_mem _`.
-/
theorem smul_one_mem (ν : Type) [Fintype ν] [DecidableEq ν] (n : ℕ) (i j : ν) :
    (((l : K) ^ n) • (1 : Matrix ν ν K⟦X⟧)) i j ∈ A O K := by
  rw [Matrix.smul_apply, Matrix.one_apply]
  split_ifs
  · rw [show ((l : K) ^ n) • (1 : K⟦X⟧) = ((l ^ n : ℕ) : K⟦X⟧) by simp [Algebra.smul_def]]
    exact natCast_mem _ _
  · rw [smul_zero]; exact zero_mem _

end GlobalTheory.BK.IntegralLeftInverseExactTriple

namespace GlobalTheory.BK

open IntegralLeftInverseExactTriple in

/- English proof (translation)
Introduce `O K _ _ _ _ _ _ l e a _ _ _ _ _ ι κ μ _ _ _ _ _ _ P Q T F G hFG n hG τ`. Establish `h1 : ∀ j : μ, ∃ x ∈ Q.M, G.app x = ((l : K) ^ n) • (Pi.single τ (Pi.single j 1) : Vec K a μ)` using `fun j => hG _ (mem_M_single T τ _ fun i => by`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[Pi.single_eq_same]`.

Conclude with `one_mem _`. Rewrite using `[Pi.single_eq_of_ne h]`. Conclude with `zero_mem _)`. Use `choose x hxM hx using h1`. Set `Xm : Matrix κ μ K⟦X⟧` to `Matrix.of fun k j => x j τ k`.

Establish `hXA : ∀ k j, Xm k j ∈ A O K` using `fun k j => mem_vecs.1 (mem_tot.1 (hxM j) τ) k`. Establish `hGX : G.mat τ * Xm = ((l : K) ^ n) • (1 : Matrix μ μ K⟦X⟧)`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Use `congrFun (congrFun (hx j) τ) i` as an intermediate fact. Rewrite `this` using `[Hom.app_apply, Pi.smul_apply, Pi.single_eq_same]`.

Rewrite using `[Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]`. Simplify `this` using `[Matrix.mulVec, dotProduct, Xm, Pi.single_apply, eq_comm]`. Establish `hGF : G.mat τ * F.mat τ = 0`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Establish `hs` using `mem_M_single P τ (Pi.single j 1) fun i' => by`.

Distinguish the cases in `h : i' = j`. Substitute `h` using the available equality. Rewrite using `[Pi.single_eq_same]`. Conclude with `one_mem _`. Rewrite using `[Pi.single_eq_of_ne h]`.

Conclude with `zero_mem _`. Establish `h0` using `(hFG.exact _ (F.app_mem_M hs)).2 ⟨_, hs, rfl⟩`. Use `congrFun (congrFun h0 τ) i` as an intermediate fact. Rewrite `this` using `[app_single, app_single, Pi.single_eq_same, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]`. Simplify using `using this`.

Set `Z : Matrix κ κ K⟦X⟧` to `((l : K) ^ n) • (1 : Matrix κ κ K⟦X⟧) - Xm * G.mat τ`. Establish `hZA : ∀ k k', Z k k' ∈ A O K` using `fun k k' => sub_mem (smul_one_mem κ n k k') (Subalgebra.sum_mem _ fun j _ => mul_mem (hXA _ _) (G.mem _ _ _))`. Establish `hGZ : G.mat τ * Z = 0`. Simplify using `only [Z, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, ← Matrix.mul_assoc, hGX, Matrix.smul_mul, Matrix.one_mul, sub_self]`. Establish `h2 : ∀ k : κ, ∃ w ∈ P.M, F.app w = Pi.single τ (fun k' => Z k' k)`.

Introduce `k`. Establish `hm` using `mem_M_single Q τ (fun k' => Z k' k) fun k' => hZA k' k`. Establish `hz : G.mat τ *ᵥ (fun k' => Z k' k) = 0`. Use function extensionality and compare the values at `i`. Use `congrFun (congrFun hGZ i) k` as an intermediate fact.

Simplify `this` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Take `⟨w, hw, h⟩` from `(hFG.exact _ hm).1 (by rw [app_single, hz, Pi.single_zero])`. Conclude with `⟨w, hw, h⟩`. Use `choose w hwM hw using h2`. Set `W : Matrix ι κ K⟦X⟧` to `Matrix.of fun i k => w k τ i`.

Establish `hWA : ∀ i k, W i k ∈ A O K` using `fun i k => mem_vecs.1 (mem_tot.1 (hwM k) τ) i`. Establish `hFW : F.mat τ * W = Z`. Use `Matrix.ext fun i k => ?_` and prove the remaining obligations. Use `congrFun (congrFun (hw k) τ) i` as an intermediate fact. Rewrite `this` using `[Hom.app_apply, Pi.single_eq_same]`.

Simplify `this` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, W]`. Use `⟨W, hWA, ?_⟩` and prove the remaining obligations. Establish `hFWF : F.mat τ * (W * F.mat τ - ((l : K) ^ n) • (1 : Matrix ι ι K⟦X⟧)) = 0`. Rewrite using `[Matrix.mul_sub, ← Matrix.mul_assoc, hFW]`. Simplify using `only [Z, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc, hGF, Matrix.mul_zero, sub_zero, Matrix.mul_smul, Matrix.mul_one, sub_self]`.

Rewrite using `[← sub_eq_zero]`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Use `set D := W * F.mat τ - ((l : K) ^ n) • (1 : Matrix ι ι K⟦X⟧) with hD`. Establish `hDm : Pi.single τ (fun i' => D i' j) ∈ P.M` using `mem_M_single P τ _ fun i' => sub_mem (Subalgebra.sum_mem _ fun k _ => mul_mem (hWA i' k) (F.mem _ _ _)) (smul_one_mem ι n i' j)`. Establish `hFD : F.mat τ *ᵥ (fun i' => D i' j) = 0`.

Use function extensionality and compare the values at `k`. Use `congrFun (congrFun hFWF k) j` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Establish `h0` using `hFG.inj _ hDm (by rw [app_single, hFD, Pi.single_zero])`. Use `congrFun (congrFun h0 τ) i` as an intermediate fact.

Simplify using `using this`.
-/
theorem exists_integral_leftInverse_of_exactTriple : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (ι κ μ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ) (F : GlobalTheory.BK.Hom P Q) (G : GlobalTheory.BK.Hom Q T), IsExactTriple F G → ∀ n : ℕ, (∀ y ∈ T.M, ∃ x ∈ Q.M, G.app x = (l : K) ^ n • y) → ∀ τ : ZMod a, ∃ Λ : Matrix ι κ K⟦X⟧, (∀ i k, Λ i k ∈ A O K) ∧ Λ * F.mat τ = (l : K) ^ n • (1 : Matrix ι ι K⟦X⟧) := by
  intro O K _ _ _ _ _ _ l e a _ _ _ _ _ ι κ μ _ _ _ _ _ _ P Q T F G hFG n hG τ
  have h1 : ∀ j : μ, ∃ x ∈ Q.M, G.app x = ((l : K) ^ n) • (Pi.single τ (Pi.single j 1) : Vec K a μ) :=
    fun j => hG _ (mem_M_single T τ _ fun i => by
      by_cases h : i = j
      · subst h; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _)
  choose x hxM hx using h1
  let Xm : Matrix κ μ K⟦X⟧ := Matrix.of fun k j => x j τ k
  have hXA : ∀ k j, Xm k j ∈ A O K := fun k j => mem_vecs.1 (mem_tot.1 (hxM j) τ) k
  have hGX : G.mat τ * Xm = ((l : K) ^ n) • (1 : Matrix μ μ K⟦X⟧) := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun (hx j) τ) i
    rw [Hom.app_apply, Pi.smul_apply, Pi.single_eq_same] at this
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
    simpa [Matrix.mulVec, dotProduct, Xm, Pi.single_apply, eq_comm] using this
  have hGF : G.mat τ * F.mat τ = 0 := by
    refine Matrix.ext fun i j => ?_
    have hs := mem_M_single P τ (Pi.single j 1) fun i' => by
      by_cases h : i' = j
      · subst h; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have h0 := (hFG.exact _ (F.app_mem_M hs)).2 ⟨_, hs, rfl⟩
    have := congrFun (congrFun h0 τ) i
    rw [app_single, app_single, Pi.single_eq_same, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
      at this
    simpa using this
  let Z : Matrix κ κ K⟦X⟧ := ((l : K) ^ n) • (1 : Matrix κ κ K⟦X⟧) - Xm * G.mat τ
  have hZA : ∀ k k', Z k k' ∈ A O K := fun k k' => sub_mem (smul_one_mem κ n k k')
    (Subalgebra.sum_mem _ fun j _ => mul_mem (hXA _ _) (G.mem _ _ _))
  have hGZ : G.mat τ * Z = 0 := by
    simp only [Z, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, ← Matrix.mul_assoc, hGX,
      Matrix.smul_mul, Matrix.one_mul, sub_self]
  have h2 : ∀ k : κ, ∃ w ∈ P.M, F.app w = Pi.single τ (fun k' => Z k' k) := by
    intro k
    have hm := mem_M_single Q τ (fun k' => Z k' k) fun k' => hZA k' k
    have hz : G.mat τ *ᵥ (fun k' => Z k' k) = 0 := by
      funext i
      have := congrFun (congrFun hGZ i) k
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    obtain ⟨w, hw, h⟩ := (hFG.exact _ hm).1 (by rw [app_single, hz, Pi.single_zero])
    exact ⟨w, hw, h⟩
  choose w hwM hw using h2
  let W : Matrix ι κ K⟦X⟧ := Matrix.of fun i k => w k τ i
  have hWA : ∀ i k, W i k ∈ A O K := fun i k => mem_vecs.1 (mem_tot.1 (hwM k) τ) i
  have hFW : F.mat τ * W = Z := by
    refine Matrix.ext fun i k => ?_
    have := congrFun (congrFun (hw k) τ) i
    rw [Hom.app_apply, Pi.single_eq_same] at this
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, W] using this
  refine ⟨W, hWA, ?_⟩
  have hFWF : F.mat τ * (W * F.mat τ - ((l : K) ^ n) • (1 : Matrix ι ι K⟦X⟧)) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hFW]
    simp only [Z, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc, hGF,
      Matrix.mul_zero, sub_zero, Matrix.mul_smul, Matrix.mul_one, sub_self]
  rw [← sub_eq_zero]
  refine Matrix.ext fun i j => ?_
  set D := W * F.mat τ - ((l : K) ^ n) • (1 : Matrix ι ι K⟦X⟧) with hD
  have hDm : Pi.single τ (fun i' => D i' j) ∈ P.M := mem_M_single P τ _ fun i' =>
    sub_mem (Subalgebra.sum_mem _ fun k _ => mul_mem (hWA i' k) (F.mem _ _ _)) (smul_one_mem ι n i' j)
  have hFD : F.mat τ *ᵥ (fun i' => D i' j) = 0 := by
    funext k
    have := congrFun (congrFun hFWF k) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have h0 := hFG.inj _ hDm (by rw [app_single, hFD, Pi.single_zero])
  have := congrFun (congrFun h0 τ) i
  simpa using this

end GlobalTheory.BK
