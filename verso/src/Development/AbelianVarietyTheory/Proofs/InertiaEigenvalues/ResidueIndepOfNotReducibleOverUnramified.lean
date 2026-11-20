import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReducibleOfStableRationalRowSubspaceStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResIndep

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `e : (fr l m : ↥(MaximalUnramifiedExtension l) → ↥(MaximalUnramifiedExtension l)) = (frobUr l)^[m]`. Use function extensionality and compare the values at `c`. Simplify using `[fr, AlgHom.coe_pow]`. Rewrite using `[e]`. Conclude with `frobUr_bijective.iterate m`.
-/
theorem fr_bijective (l : ℕ) [Fact l.Prime] (m : ℕ) : Function.Bijective (fr l m) := by
  have e : (fr l m : ↥(MaximalUnramifiedExtension l) → ↥(MaximalUnramifiedExtension l)) = (frobUr l)^[m] := by
    funext c
    simp [fr, AlgHom.coe_pow]
  rw [e]
  exact frobUr_bijective.iterate m

variable (P : LocPrime l) {n : Type} [Fintype n] [DecidableEq n]

def resS (m : ℕ) (u : n → P.R.BdR) (d : n → ↥(MaximalUnramifiedExtension l)) : P.R.BdR := ∑ i, kd P (fr l m (d i)) * u i

/- English proof (translation)
Simplify using `[resS]`.
-/
theorem resS_zero (m : ℕ) (u : n → P.R.BdR) : resS P m u 0 = 0 := by simp [resS]

/- English proof (translation)
Simplify using `[resS, map_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem resS_add (m : ℕ) (u : n → P.R.BdR) (d e : n → ↥(MaximalUnramifiedExtension l)) :
    resS P m u (d + e) = resS P m u d + resS P m u e := by
  simp [resS, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[resS, map_neg, neg_mul, Finset.sum_neg_distrib]`.
-/
theorem resS_neg (m : ℕ) (u : n → P.R.BdR) (d : n → ↥(MaximalUnramifiedExtension l)) : resS P m u (-d) = -resS P m u d := by
  simp [resS, map_neg, neg_mul, Finset.sum_neg_distrib]

/- English proof (translation)
Simplify using `[resS, Finset.mul_sum, mul_assoc]`.
-/
theorem resS_smul (m : ℕ) (u : n → P.R.BdR) (e : ↥(MaximalUnramifiedExtension l)) (d : n → ↥(MaximalUnramifiedExtension l)) :
    resS P m u (e • d) = kd P (fr l m e) * resS P m u d := by
  simp [resS, Finset.mul_sum, mul_assoc]

def resW (r m : ℕ) (u : n → P.R.BdR) : AddSubgroup (n → ↥(MaximalUnramifiedExtension l)) where
  carrier := {d | (∀ i, fr l r (d i) = d i) ∧ resS P m u d ∈ Fil P 1}
  zero_mem' := ⟨fun i => by simp, by rw [resS_zero]; exact Fil_zero_mem 1⟩
  add_mem' := fun {x y} hx hy => ⟨fun i => by simp [hx.1 i, hy.1 i], by rw [resS_add]; exact Fil_add hx.2 hy.2⟩
  neg_mem' := fun {x} hx => ⟨fun i => by simp [hx.1 i], by rw [resS_neg]; exact Fil_neg hx.2⟩

/- English proof (translation)
Express the relevant statement in the definitionally equal form `fr l r (∑ i, d i * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) = ∑ i, d i * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [map_mul, hd, hR.rat]`.
-/
theorem rat_vecMul {K : FinExt l} {r : ℕ} {ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)} (hR : IsRat r ρ) (d : n → ↥(MaximalUnramifiedExtension l))
    (hd : ∀ i, fr l r (d i) = d i) (g : ↥(GK K)) (j : n) :
    fr l r (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j) = Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j := by
  change fr l r (∑ i, d i * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) = ∑ i, d i * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hd, hR.rat]

/- English proof (translation)
Use `set q : ℚ_[l]ˣ := P.χQ (g : GQ l) ^ a with hq`. Establish `hi : ∀ i, algebraMap ℚ_[l] P.R.BdR (q : ℚ_[l]) * u i = ∑ j, kd P (fr l m ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j)) * P.actQdR (g : GQ l) (u j)`. Introduce `i`. Use `congrFun hrel i` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, matD, Matrix.map_apply] at this`.

Conclude with `this.symm`. Establish `hfix : ∀ j, P.actQdR (g : GQ l) (kd P (fr l m (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j))) = kd P (fr l m (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j))` using `fun j => act_kd P g (hR.le _ (fr_comm (rat_vecMul hR d hd g j) m))`. Establish `e1 : algebraMap ℚ_[l] P.R.BdR (q : ℚ_[l]) * resS P m u d = P.actQdR (g : GQ l) (resS P m u (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l))))`. Establish `hR' : ∀ j, P.actQdR (g : GQ l) (kd P (fr l m (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j)) * u j) = ∑ i, kd P (fr l m (d i)) * (kd P (fr l m ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j)) * P.actQdR (g : GQ l) (u j))`. Introduce `j`.

Rewrite using `[map_mul, hfix j]`. Express the relevant statement in the definitionally equal form `kd P (fr l m (∑ i, d i * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j)) * _ = _`. Rewrite using `[map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, mul_assoc]`.

Establish `hL : ∀ i, algebraMap ℚ_[l] P.R.BdR (q : ℚ_[l]) * (kd P (fr l m (d i)) * u i) = ∑ j, kd P (fr l m (d i)) * (kd P (fr l m ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j)) * P.actQdR (g : GQ l) (u j))`. Introduce `i`. Rewrite using `[mul_left_comm, hi i, Finset.mul_sum]`. Rewrite using `[resS, resS, map_sum, Finset.mul_sum]`. Repeatedly rewrite using `[hR', hL]`.

Conclude with `Finset.sum_comm`. Establish `h1 : algebraMap ℚ_[l] P.R.BdR (q : ℚ_[l]) * resS P m u d ∈ Fil P 1` using `e1 ▸ Fil_act (g : GQ l) h`. Establish `h2` using `Fil_mul_left (q_mem_Fil P ((q⁻¹ : ℚ_[l]ˣ) : ℚ_[l])) h1`. Rewrite `h2` using `[← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]`. Then use the resulting hypothesis.
-/
theorem key {K : FinExt l} {r : ℕ} {ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)} (hR : IsRat r ρ) (m : ℕ) (u : n → P.R.BdR) (a : ℤ)
    (g : ↥(GK K))
    (hrel : (matD P ρ m g).mulVec (fun i => P.actQdR (g : GQ l) (u i)) =
      algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ a : ℚ_[l]ˣ) : ℚ_[l]) • u)
    (d : n → ↥(MaximalUnramifiedExtension l)) (hd : ∀ i, fr l r (d i) = d i)
    (h : resS P m u (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l))) ∈ Fil P 1) : resS P m u d ∈ Fil P 1 := by
  set q : ℚ_[l]ˣ := P.χQ (g : GQ l) ^ a with hq
  have hi : ∀ i, algebraMap ℚ_[l] P.R.BdR (q : ℚ_[l]) * u i =
      ∑ j, kd P (fr l m ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j)) * P.actQdR (g : GQ l) (u j) := by
    intro i
    have := congrFun hrel i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, matD, Matrix.map_apply] at this
    exact this.symm
  have hfix : ∀ j, P.actQdR (g : GQ l) (kd P (fr l m (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j))) =
      kd P (fr l m (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j)) := fun j =>
    act_kd P g (hR.le _ (fr_comm (rat_vecMul hR d hd g j) m))
  have e1 : algebraMap ℚ_[l] P.R.BdR (q : ℚ_[l]) * resS P m u d =
      P.actQdR (g : GQ l) (resS P m u (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)))) := by
    have hR' : ∀ j, P.actQdR (g : GQ l) (kd P (fr l m (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j)) * u j) =
        ∑ i, kd P (fr l m (d i)) * (kd P (fr l m ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j)) * P.actQdR (g : GQ l) (u j)) := by
      intro j
      rw [map_mul, hfix j]
      change kd P (fr l m (∑ i, d i * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j)) * _ = _
      rw [map_sum, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_mul, mul_assoc]
    have hL : ∀ i, algebraMap ℚ_[l] P.R.BdR (q : ℚ_[l]) * (kd P (fr l m (d i)) * u i) =
        ∑ j, kd P (fr l m (d i)) * (kd P (fr l m ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j)) * P.actQdR (g : GQ l) (u j)) := by
      intro i
      rw [mul_left_comm, hi i, Finset.mul_sum]
    rw [resS, resS, map_sum, Finset.mul_sum]
    simp_rw [hR', hL]
    exact Finset.sum_comm
  have h1 : algebraMap ℚ_[l] P.R.BdR (q : ℚ_[l]) * resS P m u d ∈ Fil P 1 := e1 ▸ Fil_act (g : GQ l) h
  have h2 := Fil_mul_left (q_mem_Fil P ((q⁻¹ : ℚ_[l]ˣ) : ℚ_[l])) h1
  rwa [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] at h2

end GlobalTheory.PMon.ResIndep

namespace GlobalTheory.PMon

open GlobalTheory.PMon.ResIndep in

/- English proof (translation)
Introduce `l _ P AI T n _ _ K r ρ m u a hR hNS _ hu1 hrel c hc hS`. Assume the negation of the conclusion as `hc0`. Apply `hNS` to reduce the goal to its premises. Establish `hbij` using `fr_bijective l m`. Use `GlobalTheory.T.reducible_of_stable_rational_rowSubspace l n K r ρ hR (resW P r m u) (fun d hd => hd.1) ?_ ?_ ?_ ?_` and prove the remaining obligations.

Introduce `e he d hd`. Use `⟨fun i => ?_, ?_⟩` and prove the remaining obligations. Simplify using `[Pi.smul_apply, smul_eq_mul, map_mul, he, hd.1 i]`. Rewrite using `[resS_smul]`. Conclude with `Fil_mul_left (kd_mem_Fil P _) hd.2`.

Introduce `g d hd`. Establish `hd1 : ∀ i, fr l r (d i) = d i` using `hd.1`. Establish `hd' : ∀ j, fr l r (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j) = Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j` using `rat_vecMul hR d hd1 g`. Use `⟨hd', key P hR m u a g⁻¹ (hrel g⁻¹) _ hd' ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.vecMul_vecMul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.vecMul_one]`.

Conclude with `hd.2`. Use `choose d hd using fun i => hbij.2 (c i)`. Establish `hdr : ∀ i, fr l r (d i) = d i` using `fun i => hbij.1 (by`. Rewrite using `[← fr_add, add_comm, fr_add, hd i, hc i])`. Introduce `hbot`.

Establish `hmem : d ∈ resW P r m u` using `⟨hdr, by`. Express the relevant statement in the definitionally equal form `∑ i, kd P (fr l m (d i)) * u i ∈ Fil P 1`. Simplify `hS⟩` using `only [hd]`. Rewrite `hmem` using `[hbot, AddSubgroup.mem_bot]`. Apply `hc0` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Rewrite using `[← hd i, hmem]`. Simplify using the standard rewrite rules. Take `⟨i0, hi0⟩` from `hu1`. Use `⟨Pi.single i0 1, fun i => ?_, fun hmem => hi0 ?_⟩` and prove the remaining obligations.

Distinguish the cases in `h : i = i0`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`. Establish `e : resS P m u (Pi.single i0 1) = u i0`.

Simplify using `[resS, Pi.single_apply]`. Rewrite using `[← e]`. Conclude with `hmem.2`.
-/
theorem residue_indep_of_not_splits : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (m : ℕ) (u : n → P.R.BdR) (a : ℤ), IsRat r ρ → ¬ Splits r ρ → (∀ i, u i ∈ Fil P 0) → (∃ i, u i ∉ Fil P 1) → (∀ g : ↥(GK K), (matD P ρ m g).mulVec (fun i => P.actQdR (g : GQ l) (u i)) = algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ a : ℚ_[l]ˣ) : ℚ_[l]) • u) → ∀ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) → ∑ i, kd P (c i) * u i ∈ Fil P 1 → c = 0 := by
  intro l _ P AI T n _ _ K r ρ m u a hR hNS _ hu1 hrel c hc hS
  by_contra hc0
  apply hNS
  have hbij := fr_bijective l m
  refine GlobalTheory.T.reducible_of_stable_rational_rowSubspace l n K r ρ hR (resW P r m u) (fun d hd => hd.1) ?_ ?_ ?_ ?_
  · intro e he d hd
    refine ⟨fun i => ?_, ?_⟩
    · simp [Pi.smul_apply, smul_eq_mul, map_mul, he, hd.1 i]
    · rw [resS_smul]
      exact Fil_mul_left (kd_mem_Fil P _) hd.2
  · intro g d hd
    have hd1 : ∀ i, fr l r (d i) = d i := hd.1
    have hd' : ∀ j, fr l r (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j) = Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j :=
      rat_vecMul hR d hd1 g
    refine ⟨hd', key P hR m u a g⁻¹ (hrel g⁻¹) _ hd' ?_⟩
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.vecMul_one]
    exact hd.2
  · choose d hd using fun i => hbij.2 (c i)
    have hdr : ∀ i, fr l r (d i) = d i := fun i => hbij.1 (by
      rw [← fr_add, add_comm, fr_add, hd i, hc i])
    intro hbot
    have hmem : d ∈ resW P r m u := ⟨hdr, by
      change ∑ i, kd P (fr l m (d i)) * u i ∈ Fil P 1
      simpa only [hd] using hS⟩
    rw [hbot, AddSubgroup.mem_bot] at hmem
    apply hc0
    funext i
    rw [← hd i, hmem]
    simp
  · obtain ⟨i0, hi0⟩ := hu1
    refine ⟨Pi.single i0 1, fun i => ?_, fun hmem => hi0 ?_⟩
    · by_cases h : i = i0
      · subst h; simp
      · simp [h]
    · have e : resS P m u (Pi.single i0 1) = u i0 := by
        simp [resS, Pi.single_apply]
      rw [← e]
      exact hmem.2

end GlobalTheory.PMon

end
