import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.CupCastRight
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PrimOfOver
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.TorsOfForall

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC TensorProduct

namespace CrystallineSemistableComparison.AdicCoh

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

/- English proof (translation)
Rewrite using `[← Nat.sub_add_cancel h, pow_add, mul_smul, hy, smul_zero]`.
-/
theorem pow_mono_tors {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (y : N) {m n : ℕ} (h : m ≤ n)
    (hy : (l : ℤ_[l]) ^ m • y = 0) : (l : ℤ_[l]) ^ n • y = 0 := by
  rw [← Nat.sub_add_cancel h, pow_add, mul_smul, hy, smul_zero]

/- English proof (translation)
Use `(Adic.tmul_eq_zero y).1 ?_` and prove the remaining obligations. Establish `e : (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y = c⁻¹ • (c ⊗ₜ[ℤ_[l]] y)`. Rewrite using `[smul_tmul', smul_eq_mul, inv_mul_cancel₀ hc]`. Rewrite using `[e, h, smul_zero]`.
-/
theorem tors_of_tmul {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (c : ℚ_[l]) (hc : c ≠ 0) (y : N)
    (h : c ⊗ₜ[ℤ_[l]] y = 0) : ∃ n : ℕ, (l : ℤ_[l]) ^ n • y = 0 := by
  refine (Adic.tmul_eq_zero y).1 ?_
  have e : (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y = c⁻¹ • (c ⊗ₜ[ℤ_[l]] y) := by
    rw [smul_tmul', smul_eq_mul, inv_mul_cancel₀ hc]
  rw [e, h, smul_zero]

/- English proof (translation)
Establish `h1 : (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y = 0` using `(Adic.tmul_eq_zero y).2 ⟨_, h⟩`. Rewrite using `[← mul_one c, ← smul_eq_mul, ← smul_tmul', h1, smul_zero]`.
-/
theorem tmul_zero_of {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (c : ℚ_[l]) (y : N) {n : ℕ}
    (h : (l : ℤ_[l]) ^ n • y = 0) : c ⊗ₜ[ℤ_[l]] y = 0 := by
  have h1 : (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y = 0 := (Adic.tmul_eq_zero y).2 ⟨_, h⟩
  rw [← mul_one c, ← smul_eq_mul, ← smul_tmul', h1, smul_zero]

/- English proof (translation)
Establish `: NeZero l` using `⟨(Fact.out : l.Prime).ne_zero⟩`. Conclude with `AdicGeo.unit_of_over (AdicGeo.str M) l`.
-/
theorem unit_geom (M : Model l K) : IsUnit ((l : ℕ) : Γ(GlobalTheory.Et.geom (PadicAlgCl l) M.q, ⊤)) := by
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  exact AdicGeo.unit_of_over (AdicGeo.str M) l

/- English proof (translation)
Use `AdicGeo.proper_str h` as an intermediate fact. Use `neZero_pow l k` as an intermediate fact. Establish `hu : IsUnit ((l ^ k : ℕ) : PadicAlgCl l)` using `(Nat.cast_ne_zero.2 (NeZero.ne _)).isUnit`. Conclude with `hI.e4 (l ^ k) (PadicAlgCl l) hu (AdicGeo.str M) n i`.
-/
theorem fin_levels (hI : ZIn) (M : Model l K) (h : M.Good) (n i : ℤ) (k : ℕ) :
    Finite (Ht (l ^ k) (sch.obj (GlobalTheory.Et.geom (PadicAlgCl l) M.q)) n i) := by
  have := AdicGeo.proper_str h
  have := neZero_pow l k
  have hu : IsUnit ((l ^ k : ℕ) : PadicAlgCl l) := (Nat.cast_ne_zero.2 (NeZero.ne _)).isUnit
  exact hI.e4 (l ^ k) (PadicAlgCl l) hu (AdicGeo.str M) n i

/- English proof (translation)
Establish `hS` using `isSys l hI _ (unit_geom M) (j : ℤ) 0 (fin_levels hI M h _ _)`. Establish `: Module.Finite ℤ_[l] (Hl l (sch.obj (GlobalTheory.Et.geom (PadicAlgCl l) M.q)) (j : ℤ) 0)` using `hS.finite (fun _ => Iff.rfl)`. Conclude with `Adic.fd`.
-/
theorem fin_of (hI : ZIn) (M : Model l K) (h : M.Good) (j : ℕ) : FiniteDimensional ℚ_[l] (M.V j) := by
  have hS := isSys l hI _ (unit_geom M) (j : ℤ) 0 (fin_levels hI M h _ _)
  have : Module.Finite ℤ_[l] (Hl l (sch.obj (GlobalTheory.Et.geom (PadicAlgCl l) M.q)) (j : ℤ) 0) :=
    hS.finite (fun _ => Iff.rfl)
  exact Adic.fd

/- English proof (translation)
Take `⟨r, P, d, u, hu, hsum, hP⟩` from `hC M hM`. Use `⟨r, P, d, u, hu, hP, fun j v hv => ?_⟩` and prove the remaining obligations. Establish `hs` using `AdicGeo.isSum_geom u hu hsum`. Take `⟨c, x, rfl⟩` from `Adic.tmul_surj v`. Distinguish the cases in `hc : c = 0`.

Rewrite using `[hc, zero_tmul]`. Establish `ht : ∀ a, ∃ n : ℕ, (l : ℤ_[l]) ^ n • pullHl l (sch.map (GlobalTheory.Et.geomMap (PadicAlgCl l) (P a).q (Model.genMap (u a) (hu a)) (Model.genMap_q (u a) (hu a)))) j 0 x = 0` using `fun a => tors_of_tmul c hc _ ((LinearMap.baseChange_tmul _ _ _).symm.trans (hv a))`. Use `choose n hn using ht`. Use `tmul_zero_of c x (n := ∑ a, n a) (sum_inj l hI _ hs j 0 _ fun a => ?_)` and prove the remaining obligations. Use `((pullHl l _ j 0).map_smul _ x).trans ?_` and prove the remaining obligations.

Conclude with `pow_mono_tors _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)) (hn a)`.
-/
theorem comp_of (hI : ZIn) (G : Model l K → Prop) (hG : ∀ M, G M → M.Good) (hC : CompM G) (M : Model l K) (hM : G M) :
    ∃ (r : ℕ) (P : Fin r → Model l K) (d : Fin r → ℕ) (u : ∀ a, (P a).X ⟶ M.X)
    (hu : ∀ a, u a ≫ M.p = (P a).p), (∀ a, G (P a) ∧ (P a).Conn (d a)) ∧
    ∀ (j : ℕ) (v : M.V j), (∀ a, Model.pullV (u a) (hu a) j v = 0) → v = 0 := by
  obtain ⟨r, P, d, u, hu, hsum, hP⟩ := hC M hM
  refine ⟨r, P, d, u, hu, hP, fun j v hv => ?_⟩
  have hs := AdicGeo.isSum_geom u hu hsum
  obtain ⟨c, x, rfl⟩ := Adic.tmul_surj v
  by_cases hc : c = 0
  · rw [hc, zero_tmul]
  have ht : ∀ a, ∃ n : ℕ, (l : ℤ_[l]) ^ n • pullHl l (sch.map (GlobalTheory.Et.geomMap (PadicAlgCl l) (P a).q
      (Model.genMap (u a) (hu a)) (Model.genMap_q (u a) (hu a)))) j 0 x = 0 := fun a =>
    tors_of_tmul c hc _ ((LinearMap.baseChange_tmul _ _ _).symm.trans (hv a))
  choose n hn using ht
  refine tmul_zero_of c x (n := ∑ a, n a) (sum_inj l hI _ hs j 0 _ fun a => ?_)
  refine ((pullHl l _ j 0).map_smul _ x).trans ?_
  exact pow_mono_tors _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)) (hn a)

end CrystallineSemistableComparison.AdicCoh
