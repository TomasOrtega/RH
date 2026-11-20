import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InflationBasic

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped Classical

namespace GlobalTheory.RowIndex

/- English proof (translation)
Take `⟨hQ, hpos, -, -, hfib, -⟩` from `GlobalTheory.InflBasic.inflation_basic I g Q ρ μf hg`. Establish `hS : S.Finite` using `Set.toFinite S`. Establish `hset : {x | x ∈ I.Kset ∧ ρ.toFun x ∈ S} = ⋃ q ∈ hS.toFinset, {x | x ∈ I.Kset ∧ ρ.toFun x = q}`. Use extensionality with `x`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.Finite.mem_toFinset, exists_prop]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, hq⟩`. Conclude with `⟨_, hq, hx, rfl⟩`. Introduce and unpack `⟨q, hq, hx, rfl⟩`. Conclude with `⟨hx, hq⟩`.

Rewrite using `[hset, measure_biUnion_finset]`. Rewrite using `[Finset.sum_congr rfl (fun q _ => (hfib q).1), Finset.sum_const, ENNReal.toReal_nsmul, nsmul_eq_mul, Nat.card_eq_card_finite_toFinset hS]`. Introduce `q _ q' _ hqq'`. Conclude with `Set.disjoint_left.mpr fun x hx hx' => hqq' (hx.2.symm.trans hx'.2)`. Introduce `q _`.

Conclude with `(hfib q).2.measurableSet`.
-/
theorem vol_preimage {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q) (μf : Measure I.Gf)
    [μf.IsHaarMeasure] (hg : 1 ≤ g) (S : Set Q) :
    (μf {x | x ∈ I.Kset ∧ ρ.toFun x ∈ S}).toReal = (Nat.card S : ℝ) * (μf (I.Kg g)).toReal := by
  obtain ⟨hQ, hpos, -, -, hfib, -⟩ := GlobalTheory.InflBasic.inflation_basic I g Q ρ μf hg
  have hS : S.Finite := Set.toFinite S

  have hset : {x | x ∈ I.Kset ∧ ρ.toFun x ∈ S} =
      ⋃ q ∈ hS.toFinset, {x | x ∈ I.Kset ∧ ρ.toFun x = q} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.Finite.mem_toFinset, exists_prop]
    constructor
    · rintro ⟨hx, hq⟩
      exact ⟨_, hq, hx, rfl⟩
    · rintro ⟨q, hq, hx, rfl⟩
      exact ⟨hx, hq⟩
  rw [hset, measure_biUnion_finset]
  · rw [Finset.sum_congr rfl (fun q _ => (hfib q).1), Finset.sum_const, ENNReal.toReal_nsmul,
      nsmul_eq_mul, Nat.card_eq_card_finite_toFinset hS]
  · intro q _ q' _ hqq'
    exact Set.disjoint_left.mpr fun x hx hx' => hqq' (hx.2.symm.trans hx'.2)
  · intro q _
    exact (hfib q).2.measurableSet

/- English proof (translation)
Take `⟨-, hpos, -⟩` from `GlobalTheory.InflBasic.inflation_basic I g Q ρ μf hg`. Establish `hK : {x | x ∈ I.Kset ∧ ρ.toFun x ∈ (Set.univ : Set Q)} = I.Kset`. Use extensionality with `x`. Simplify using the standard rewrite rules. Establish `h2` using `vol_preimage ρ μf hg Set.univ`.

Rewrite `h2` using `[hK, Nat.card_univ]`. Rewrite using `[h2, vol_preimage ρ μf hg S, mul_div_mul_right _ _ hpos.ne']`.
-/
theorem vol_ratio {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q) (μf : Measure I.Gf)
    [μf.IsHaarMeasure] (hg : 1 ≤ g) (S : Set Q) :
    (μf I.Kset).toReal / (μf {x | x ∈ I.Kset ∧ ρ.toFun x ∈ S}).toReal = (Nat.card Q : ℝ) / (Nat.card S : ℝ) := by
  obtain ⟨-, hpos, -⟩ := GlobalTheory.InflBasic.inflation_basic I g Q ρ μf hg
  have hK : {x | x ∈ I.Kset ∧ ρ.toFun x ∈ (Set.univ : Set Q)} = I.Kset := by
    ext x
    simp
  have h2 := vol_preimage ρ μf hg Set.univ
  rw [hK, Nat.card_univ] at h2
  rw [h2, vol_preimage ρ μf hg S, mul_div_mul_right _ _ hpos.ne']

/- English proof (translation)
Rewrite using `[Fintype.prod_sigma, Fin.prod_univ_two]`. Simplify using `[hPl]`.
-/
private lemma prod_sigma_fin_two_eq_pow_mul_pow {Pl : Fin 2 → Type} [∀ k, Fintype (Pl k)] (f : ℕ)
    (hPl : ∀ k, Fintype.card (Pl k) = f) (c : Fin 2 → ℕ) :
    ∏ kv : (Σ k : Fin 2, Pl k), c kv.1 = c 0 ^ f * c 1 ^ f := by
  rw [Fintype.prod_sigma, Fin.prod_univ_two]
  simp [hPl]

/- English proof (translation)
Set `S : Set (GProd N g Pl)` to `{h | ∀ k v, P k (h ⟨k, v⟩ : GL (Fin N) (ZMod (g k)))}`. Establish `hK2 : K₂ = {x | x ∈ I.Kset ∧ ρ.toFun x ∈ S}`. Use extensionality with `x`. Rewrite using `[hK]`. Both sides reduce to the same expression.

Rewrite using `[hK2, vol_ratio ρ μf hg S]`. Set `e : S ≃ ∀ kv : (Σ k : Fin 2, Pl k), {A : GL (Fin N) (ZMod (g kv.1)) // P kv.1 (A : Matrix (Fin N) (Fin N) (ZMod (g kv.1)))}` to `(Equiv.subtypeEquivRight (fun h => ⟨fun hh (kv : Σ k : Fin 2, Pl k) => hh kv.1 kv.2, fun hh k v => hh ⟨k, v⟩⟩)).trans (Equiv.subtypePiEquivPi)`. Establish `hc1 : Nat.card (GProd N g Pl) = Nat.card (GL (Fin N) (ZMod (g 0))) ^ f * Nat.card (GL (Fin N) (ZMod (g 1))) ^ f`. Rewrite using `[Nat.card_pi]`. Conclude with `prod_sigma_fin_two_eq_pow_mul_pow f hPl (fun k => Nat.card (GL (Fin N) (ZMod (g k))))`.

Establish `hc2 : Nat.card S = Nat.card {A : GL (Fin N) (ZMod (g 0)) // P 0 (A : Matrix (Fin N) (Fin N) (ZMod (g 0)))} ^ f * Nat.card {A : GL (Fin N) (ZMod (g 1)) // P 1 (A : Matrix (Fin N) (Fin N) (ZMod (g 1)))} ^ f`. Rewrite using `[Nat.card_congr e, Nat.card_pi]`. Conclude with `prod_sigma_fin_two_eq_pow_mul_pow f hPl (fun k => Nat.card {A : GL (Fin N) (ZMod (g k)) // P k (A : Matrix (Fin N) (Fin N) (ZMod (g k)))})`. Rewrite using `[hc1, hc2]`. Simplify using `only [Formalism.MainNotions.StandardLattice.idxLoc, div_pow]`.

Use `push_cast`. Rewrite using `[mul_div_mul_comm]`.
-/
theorem vol_ratio_prod {I : AutInst} {N f : ℕ} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type} [∀ k, Fintype (Pl k)]
    (hPl : ∀ k, Fintype.card (Pl k) = f) (ρ : Red I (g 0 * g 1) (GProd N g Pl))
    (μf : Measure I.Gf) [μf.IsHaarMeasure] (hg : 1 ≤ g 0 * g 1)
    (P : ∀ k, Matrix (Fin N) (Fin N) (ZMod (g k)) → Prop) (K₂ : Set I.Gf)
    (hK : ∀ x, x ∈ K₂ ↔ x ∈ I.Kset ∧ ∀ k v, P k (ρ.toFun x ⟨k, v⟩ : GL (Fin N) (ZMod (g k)))) :
    (μf I.Kset).toReal / (μf K₂).toReal =
      Formalism.MainNotions.StandardLattice.idxLoc (ZMod (g 0)) N (P 0) ^ f * Formalism.MainNotions.StandardLattice.idxLoc (ZMod (g 1)) N (P 1) ^ f := by

  let S : Set (GProd N g Pl) := {h | ∀ k v, P k (h ⟨k, v⟩ : GL (Fin N) (ZMod (g k)))}
  have hK2 : K₂ = {x | x ∈ I.Kset ∧ ρ.toFun x ∈ S} := by
    ext x
    rw [hK]
    rfl
  rw [hK2, vol_ratio ρ μf hg S]

  let e : S ≃ ∀ kv : (Σ k : Fin 2, Pl k),
      {A : GL (Fin N) (ZMod (g kv.1)) // P kv.1 (A : Matrix (Fin N) (Fin N) (ZMod (g kv.1)))} :=
    (Equiv.subtypeEquivRight (fun h => ⟨fun hh (kv : Σ k : Fin 2, Pl k) => hh kv.1 kv.2, fun hh k v => hh ⟨k, v⟩⟩)).trans
      (Equiv.subtypePiEquivPi)
  have hc1 : Nat.card (GProd N g Pl) =
      Nat.card (GL (Fin N) (ZMod (g 0))) ^ f * Nat.card (GL (Fin N) (ZMod (g 1))) ^ f := by
    rw [Nat.card_pi]
    exact prod_sigma_fin_two_eq_pow_mul_pow f hPl (fun k => Nat.card (GL (Fin N) (ZMod (g k))))
  have hc2 : Nat.card S =
      Nat.card {A : GL (Fin N) (ZMod (g 0)) // P 0 (A : Matrix (Fin N) (Fin N) (ZMod (g 0)))} ^ f *
        Nat.card {A : GL (Fin N) (ZMod (g 1)) // P 1 (A : Matrix (Fin N) (Fin N) (ZMod (g 1)))} ^ f := by
    rw [Nat.card_congr e, Nat.card_pi]
    exact prod_sigma_fin_two_eq_pow_mul_pow f hPl
      (fun k => Nat.card {A : GL (Fin N) (ZMod (g k)) // P k (A : Matrix (Fin N) (Fin N) (ZMod (g k)))})
  rw [hc1, hc2]
  simp only [Formalism.MainNotions.StandardLattice.idxLoc, div_pow]
  push_cast
  rw [mul_div_mul_comm]

end GlobalTheory.RowIndex
