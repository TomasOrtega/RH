import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBaseEqChain
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoRestrictPushforwardUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EAComm

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory.ChainParts

namespace GlobalTheory.ChainParts

/- English proof (translation)
Set `C : Matrix ι (Fin n) R` to `Matrix.of cf`. Set `E : Matrix (Fin n) ι R` to `Matrix.of fun k σ => ev σ (b k)`. Establish `hCE : C * E = 1`. Use extensionality with `τ' σ`. Simplify using `only [C, E, Matrix.mul_apply, Matrix.of_apply, hev, Matrix.one_apply, eq_comm]`.

Establish `hEC : E * C = 1` using `(Matrix.mul_eq_one_comm_of_equiv (Fintype.equivFinOfCardEq hn)).1 hCE`. Establish `inj : ∀ d d' : Fin n → R, Matrix.vecMul d E = Matrix.vecMul d' E → d = d'`. Introduce `d d' h`. Use `congrArg (fun v => Matrix.vecMul v C) h` as an intermediate fact. Simplify `this` using `only [Matrix.vecMul_vecMul, hEC, Matrix.vecMul_one]`.

Establish `hb : ∀ σ (x : Λ), ∑ m, ((b.repr x m : ℤ) : R) * ev σ (b m) = ev σ x`. Introduce `σ x`. Use `conv_rhs => rw [← b.sum_repr x]`. Simplify using `only [map_sum, zsmul_eq_mul, map_mul, map_intCast]`. Use `congrFun (inj (fun m => ∑ k, ∑ l, cf τ k * cf τ l * ((b.repr (b k * b l) m : ℤ) : R)) (cf τ) ?_) m` and prove the remaining obligations.

Use extensionality with `σ`. Simplify using `only [Matrix.vecMul, dotProduct, E, Matrix.of_apply]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.sum_mul, Finset.mul_sum, mul_assoc]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `_ = (∑ k, cf τ k * ev σ (b k)) * (∑ l, cf τ l * ev σ (b l)) := by`. Simplify using `only [hb, map_mul, Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring` and prove the remaining obligations.

Use `_ = ∑ m, cf τ m * ev σ (b m) := by`. Apply the tactic sequence `rw [hev]; split_ifs <;> simp`.
-/
theorem idem_coeff {Λ R : Type} [CommRing Λ] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (b : Module.Basis (Fin n) ℤ Λ) (ev : ι → (Λ →+* R)) (cf : ι → Fin n → R)
    (hev : ∀ τ σ, ∑ k, cf τ k * ev σ (b k) = if σ = τ then 1 else 0) (hn : Fintype.card ι = n) (τ : ι) (m : Fin n) :
    ∑ k, ∑ l, cf τ k * cf τ l * ((b.repr (b k * b l) m : ℤ) : R) = cf τ m := by
  let C : Matrix ι (Fin n) R := Matrix.of cf
  let E : Matrix (Fin n) ι R := Matrix.of fun k σ => ev σ (b k)
  have hCE : C * E = 1 := by
    ext τ' σ
    simp only [C, E, Matrix.mul_apply, Matrix.of_apply, hev, Matrix.one_apply, eq_comm]
  have hEC : E * C = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivFinOfCardEq hn)).1 hCE
  have inj : ∀ d d' : Fin n → R, Matrix.vecMul d E = Matrix.vecMul d' E → d = d' := by
    intro d d' h
    have := congrArg (fun v => Matrix.vecMul v C) h
    simpa only [Matrix.vecMul_vecMul, hEC, Matrix.vecMul_one] using this
  have hb : ∀ σ (x : Λ), ∑ m, ((b.repr x m : ℤ) : R) * ev σ (b m) = ev σ x := by
    intro σ x
    conv_rhs => rw [← b.sum_repr x]
    simp only [map_sum, zsmul_eq_mul, map_mul, map_intCast]
  refine congrFun (inj (fun m => ∑ k, ∑ l, cf τ k * cf τ l * ((b.repr (b k * b l) m : ℤ) : R)) (cf τ) ?_) m
  ext σ
  simp only [Matrix.vecMul, dotProduct, E, Matrix.of_apply]
  calc ∑ m, (∑ k, ∑ l, cf τ k * cf τ l * ((b.repr (b k * b l) m : ℤ) : R)) * ev σ (b m)
      = ∑ k, ∑ l, cf τ k * cf τ l * ∑ m, ((b.repr (b k * b l) m : ℤ) : R) * ev σ (b m) := by
        simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
    _ = (∑ k, cf τ k * ev σ (b k)) * (∑ l, cf τ l * ev σ (b l)) := by
        simp only [hb, map_mul, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    _ = ∑ m, cf τ m * ev σ (b m) := by
        rw [hev]; split_ifs <;> simp

/- English proof (translation)
Establish `hb : ∀ x : Λ, ρ x = ∑ m, ρ (b m) * s ((b.repr x m : ℤ) : R)`. Introduce `x`. Use `conv_lhs => rw [← b.sum_repr x]`. Simplify using `only [map_sum, zsmul_eq_mul, map_mul, map_intCast]`. Conclude with `Finset.sum_congr rfl fun m _ => Int.cast_comm _ _`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Establish `: ρ (b k) * s (cf τ k) * (ρ (b l) * s (cf τ l)) = ρ (b k * b l) * s (cf τ k * cf τ l)`. Rewrite using `[map_mul, map_mul, mul_assoc, ← mul_assoc (s _), hc, mul_assoc, mul_assoc]`.

Rewrite using `[this, hb (b k * b l), Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, ← map_mul, mul_comm ((b.repr (b k * b l) m : ℤ) : R)]`. Use `_ = ∑ m, ρ (b m) * s (∑ k, ∑ l, cf τ k * cf τ l * ((b.repr (b k * b l) m : ℤ) : R)) := by`. Simplify using `only [map_sum, Finset.mul_sum]`.

Use `symm`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `_ = _ := by simp only [idem_coeff b ev cf hev hn τ]`.
-/
theorem idem_ring {Λ R A : Type} [CommRing Λ] [CommRing R] [Ring A] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (b : Module.Basis (Fin n) ℤ Λ) (ev : ι → (Λ →+* R)) (cf : ι → Fin n → R)
    (hev : ∀ τ σ, ∑ k, cf τ k * ev σ (b k) = if σ = τ then 1 else 0) (hn : Fintype.card ι = n) (τ : ι)
    (s : R →+* A) (ρ : Λ →+* A) (hc : ∀ r a, s r * ρ a = ρ a * s r) :
    (∑ k, ρ (b k) * s (cf τ k)) * (∑ k, ρ (b k) * s (cf τ k)) = ∑ k, ρ (b k) * s (cf τ k) := by
  have hb : ∀ x : Λ, ρ x = ∑ m, ρ (b m) * s ((b.repr x m : ℤ) : R) := by
    intro x
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, zsmul_eq_mul, map_mul, map_intCast]
    exact Finset.sum_congr rfl fun m _ => Int.cast_comm _ _
  calc (∑ k, ρ (b k) * s (cf τ k)) * (∑ k, ρ (b k) * s (cf τ k))
      = ∑ k, ∑ l, ∑ m, ρ (b m) * s (cf τ k * cf τ l * ((b.repr (b k * b l) m : ℤ) : R)) := by
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        have : ρ (b k) * s (cf τ k) * (ρ (b l) * s (cf τ l)) = ρ (b k * b l) * s (cf τ k * cf τ l) := by
          rw [map_mul, map_mul, mul_assoc, ← mul_assoc (s _), hc, mul_assoc, mul_assoc]
        rw [this, hb (b k * b l), Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [mul_assoc, ← map_mul, mul_comm ((b.repr (b k * b l) m : ℤ) : R)]
    _ = ∑ m, ρ (b m) * s (∑ k, ∑ l, cf τ k * cf τ l * ((b.repr (b k * b l) m : ℤ) : R)) := by
        simp only [map_sum, Finset.mul_sum]
        symm
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
    _ = _ := by simp only [idem_coeff b ev cf hev hn τ]

/- English proof (translation)
Introduce `O _ _ _ B Λ _ R _ _ ι _ _ n b ev cf hev hn τ M hM`. Set `ρ : Λ →+* End M.V` to `{ M.ρ with map_zero' := by`. Use `hM 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `left_eq_add.1 this`.

Use the proof step `map_add' := hM }`. Set `s : R →+* End M.V` to `(smulEnd M.V).comp (algebraMap R Γ(B.X, ⊤))`. Establish `hc : ∀ r a, s r * ρ a = ρ a * s r` using `fun r a => (smulHom_comp (F := M.V) (G := M.V) (M.ρ a) (algebraMap R Γ(B.X, ⊤) r)).symm`. Conclude with `idem_ring b ev cf hev hn τ s ρ hc`.
-/
theorem eA_idem : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} {Λ : Type} [CommRing Λ] {R : Type} [CommRing R] [Algebra R Γ(B.X, ⊤)] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (b : Module.Basis (Fin n) ℤ Λ) (ev : ι → (Λ →+* R)) (cf : ι → Fin n → R) (hev : ∀ τ σ, ∑ k, cf τ k * ev σ (b k) = if σ = τ then 1 else 0) (hn : Fintype.card ι = n) (τ : ι) (M : AM B Λ) (hM : IsAdd M), eA M (fun k => algebraMap R Γ(B.X, ⊤) (cf τ k)) b ≫ eA M (fun k => algebraMap R Γ(B.X, ⊤) (cf τ k)) b =
      eA M (fun k => algebraMap R Γ(B.X, ⊤) (cf τ k)) b := by
  intro O _ _ _ B Λ _ R _ _ ι _ _ n b ev cf hev hn τ M hM
  let ρ : Λ →+* End M.V :=
    { M.ρ with
      map_zero' := by
        have := hM 0 0
        rw [add_zero] at this
        exact left_eq_add.1 this
      map_add' := hM }
  let s : R →+* End M.V := (smulEnd M.V).comp (algebraMap R Γ(B.X, ⊤))
  have hc : ∀ r a, s r * ρ a = ρ a * s r := fun r a =>
    (smulHom_comp (F := M.V) (G := M.V) (M.ρ a) (algebraMap R Γ(B.X, ⊤) r)).symm
  exact idem_ring b ev cf hev hn τ s ρ hc

end GlobalTheory.ChainParts
