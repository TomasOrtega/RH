import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridCoreIffFirstRowExtByZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLatDlOfIsOrthCo
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ProjXCols

/- English proof (translation)
Take `⟨gens, hg⟩` from `hΛ.fg`. Establish `key : ∀ g : Fin n → E, ∃ z : ℤ, z ≠ 0 ∧ (z : E) • (A *ᵥ g) ∈ Λ` using `fun g => GlobalTheory.OrthDual.exists_int_smul_mem Λ (by rw [hΛ.span_eq_top]; trivial)`. Use `choose z hz0 hz using key`. Establish `hnat : ∀ g, ((z g).natAbs : E) • (A *ᵥ g) ∈ Λ`. Introduce `g`.

Break down `Int.natAbs_eq (z g) with h | h` into its components or cases. Establish `h1` using `hz g`. Rewrite `h1` using `[h, Int.cast_natCast]`. Conclude with `h1`. Establish `h1` using `hz g`.

Rewrite `h1` using `[h, Int.cast_neg, Int.cast_natCast, neg_smul, Submodule.neg_mem_iff]`. Conclude with `h1`. Use `⟨∏ g ∈ gens, (z g).natAbs, Finset.prod_pos fun g _ => Int.natAbs_pos.2 (hz0 g), ?_⟩` and prove the remaining obligations. Set `f : (Fin n → E) →ₗ[𝓞 E] (Fin n → E)` to `(((∏ g ∈ gens, (z g).natAbs : ℕ) : E) • Matrix.mulVecLin A).restrictScalars (𝓞 E)`. Establish `hle : Submodule.span (𝓞 E) (gens : Set (Fin n → E)) ≤ Λ.comap f`.

Rewrite using `[Submodule.span_le]`. Introduce `g hgm`. Take `⟨k, hk⟩` from `Finset.dvd_prod_of_mem (fun g => (z g).natAbs) hgm`. Establish `hk' : (∏ g ∈ gens, (z g).natAbs) = (z g).natAbs * k` using `hk`. Use `show ((∏ g ∈ gens, (z g).natAbs : ℕ) : E) • (A *ᵥ g) ∈ Λ`.

Rewrite using `[hk', Nat.cast_mul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]`. Conclude with `nsmul_mem (hnat g) k`. Rewrite `hle` using `[hg]`. Introduce `s hs`. Conclude with `hle hs`.
-/
theorem exists_nat_smul_mulVec_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsLattice E Λ) (A : Matrix (Fin n) (Fin n) E) :
    ∃ N : ℕ, 0 < N ∧ ∀ s ∈ Λ, (N : E) • (A *ᵥ s) ∈ Λ := by
  classical
  obtain ⟨gens, hg⟩ := hΛ.fg
  have key : ∀ g : Fin n → E, ∃ z : ℤ, z ≠ 0 ∧ (z : E) • (A *ᵥ g) ∈ Λ := fun g =>
    GlobalTheory.OrthDual.exists_int_smul_mem Λ (by rw [hΛ.span_eq_top]; trivial)
  choose z hz0 hz using key
  have hnat : ∀ g, ((z g).natAbs : E) • (A *ᵥ g) ∈ Λ := by
    intro g
    rcases Int.natAbs_eq (z g) with h | h
    · have h1 := hz g
      rw [h, Int.cast_natCast] at h1
      exact h1
    · have h1 := hz g
      rw [h, Int.cast_neg, Int.cast_natCast, neg_smul, Submodule.neg_mem_iff] at h1
      exact h1
  refine ⟨∏ g ∈ gens, (z g).natAbs, Finset.prod_pos fun g _ => Int.natAbs_pos.2 (hz0 g), ?_⟩
  let f : (Fin n → E) →ₗ[𝓞 E] (Fin n → E) :=
    (((∏ g ∈ gens, (z g).natAbs : ℕ) : E) • Matrix.mulVecLin A).restrictScalars (𝓞 E)
  have hle : Submodule.span (𝓞 E) (gens : Set (Fin n → E)) ≤ Λ.comap f := by
    rw [Submodule.span_le]
    intro g hgm
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun g => (z g).natAbs) hgm
    have hk' : (∏ g ∈ gens, (z g).natAbs) = (z g).natAbs * k := hk
    show ((∏ g ∈ gens, (z g).natAbs : ℕ) : E) • (A *ᵥ g) ∈ Λ
    rw [hk', Nat.cast_mul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]
    exact nsmul_mem (hnat g) k
  rw [hg] at hle
  intro s hs
  exact hle hs

variable {D : D7}

/- English proof (translation)
Establish `h : Matrix.vecMul (Matrix.vecMul (star s) S.gram) ((N : D.host.E) • Q) = Matrix.vecMul (star ((N : D.host.E) • (Mᴴ *ᵥ s))) S.gram`. Rewrite using `[Matrix.vecMul_vecMul, Matrix.mul_smul, hQM, star_smul, star_natCast, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, Matrix.vecMul_smul, Matrix.smul_vecMul, Matrix.vecMul_vecMul]`. Establish `hj` using `congrFun h j`. Simplify `hj` using `only [Matrix.vecMul, dotProduct, Pi.star_apply]`.
-/
theorem sum_mul_eq (S : HSp D) (N : ℕ) (Q M : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (hQM : S.gram * Q = M * S.gram)
    (s : Fin S.rank → D.host.E) (j : Fin S.rank) :
    ∑ l, (∑ k, star (s k) * S.gram k l) * ((N : D.host.E) • Q) l j =
      ∑ k, star (((N : D.host.E) • (Mᴴ *ᵥ s)) k) * S.gram k j := by
  have h : Matrix.vecMul (Matrix.vecMul (star s) S.gram) ((N : D.host.E) • Q) =
      Matrix.vecMul (star ((N : D.host.E) • (Mᴴ *ᵥ s))) S.gram := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_smul, hQM, star_smul, star_natCast, Matrix.star_mulVec,
      Matrix.conjTranspose_conjTranspose, Matrix.vecMul_smul, Matrix.smul_vecMul, Matrix.vecMul_vecMul]
  have hj := congrFun h j
  simpa only [Matrix.vecMul, dotProduct, Pi.star_apply] using hj

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[rat, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, nsmul_eq_mul]`.
-/
theorem rat_natCast_smul {m n : ℕ} (N : ℕ) (X : Matrix (Fin m) (Fin n) D.host.E) :
    (rat ((N : D.host.E) • X) : Mx D m n) = N • (rat X : Mx D m n) := by
  ext i j
  simp [rat, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, nsmul_eq_mul]

end GlobalTheory.ProjXCols

namespace GlobalTheory.ProjXCols

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `D hQ T L μ0 hL sc G W M hM F hF ρ h`. Establish `hi : 2 * ρ + 1 < D.R.m` using `by omega`. Establish `h0 : ∀ j, (Node.grid (2 * ρ + 1 + 1) 0 : Node) ≠ .grid 0 j` using `fun j hh => by injection hh with h'`. Use linear arithmetic over natural numbers and integers. Establish `hsd : IsSelfDualC (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.Λ (.grid (2 * ρ + 1 + 1) 0))` using `(G.isV (show (Node.grid (2 * ρ + 1 + 1) 0 : Node).InRange D.R.m from ⟨hi, Nat.zero_le _⟩) h0).sd`.

Take `⟨N, hN, hNs⟩` from `exists_nat_smul_mulVec_mem _ hsd.1 ((G.V (.grid (2 * ρ + 1 + 1) 0)).gram * (F.dB ρ h).e * (F.dB ρ h).e'ᴴ)ᴴ`. Use `⟨N, hN, fun u hu => ?_⟩` and prove the remaining obligations. Establish `e1 : N • (u ⬝ (F.dB ρ h).jX ⬝ (F.dB ρ h).pX) = u ⬝ (rat ((N : D.host.E) • ((F.dB ρ h).e * (F.dB ρ h).qX)) : Mx D (G.V (.grid (2 * ρ + 1 + 1) 0)).rank (G.V (.grid (2 * ρ + 1 + 1) 0)).rank)`. Rewrite using `[rat_natCast_smul, rat_mul, Matrix.mul_smul, Matrix.mul_assoc]`. Both sides reduce to the same expression.

Rewrite using `[e1]`. Use `GlobalTheory.CoreRowLat.latO_mul_right _ (fun s hs => ⟨_, hNs s hs, fun j => ?_⟩) hu` and prove the remaining obligations. Use `sum_mul_eq _ N _ _ ?_ s j` and prove the remaining obligations. Simplify using `only [HypDec.qX, Matrix.mul_assoc]`.
-/
theorem nsmul_projX_mem_latBig : OnStd fun {D} _ _ {sc} {G} _ F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latBig G (2 * ρ + 1), N • (u ⬝ (F.dB ρ h).jX ⬝ (F.dB ρ h).pX) ∈ latBig G (2 * ρ + 1) := by
  intro D hQ T L μ0 hL sc G W M hM F hF ρ h
  have hi : 2 * ρ + 1 < D.R.m := by omega
  have h0 : ∀ j, (Node.grid (2 * ρ + 1 + 1) 0 : Node) ≠ .grid 0 j := fun j hh => by
    injection hh with h'
    omega
  have hsd : IsSelfDualC (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) :=
    (G.isV (show (Node.grid (2 * ρ + 1 + 1) 0 : Node).InRange D.R.m from ⟨hi, Nat.zero_le _⟩) h0).sd
  obtain ⟨N, hN, hNs⟩ := exists_nat_smul_mulVec_mem _ hsd.1
    ((G.V (.grid (2 * ρ + 1 + 1) 0)).gram * (F.dB ρ h).e * (F.dB ρ h).e'ᴴ)ᴴ
  refine ⟨N, hN, fun u hu => ?_⟩
  have e1 : N • (u ⬝ (F.dB ρ h).jX ⬝ (F.dB ρ h).pX) =
      u ⬝ (rat ((N : D.host.E) • ((F.dB ρ h).e * (F.dB ρ h).qX)) :
        Mx D (G.V (.grid (2 * ρ + 1 + 1) 0)).rank (G.V (.grid (2 * ρ + 1 + 1) 0)).rank) := by
    rw [rat_natCast_smul, rat_mul, Matrix.mul_smul, Matrix.mul_assoc]
    rfl
  rw [e1]
  refine GlobalTheory.CoreRowLat.latO_mul_right _ (fun s hs => ⟨_, hNs s hs, fun j => ?_⟩) hu
  refine sum_mul_eq _ N _ _ ?_ s j
  simp only [HypDec.qX, Matrix.mul_assoc]

end GlobalTheory.ProjXCols
