import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open NumberField GlobalTheory.FinPl.FrameLat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.IwaPlace.LocSD

variable {D : D7}

/- English proof (translation)
Establish `hs` using `GlobalTheory.LatAlmostStd.intSupp_single_mul v (α := 1) (fun w => by rw [map_one]; exact one_mem _)`. Rewrite `hs` using `[mul_one]`. Establish `hp : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1))` using `⟨_, rfl, GlobalTheory.LatAlmostStd.evalV_single_same v 1, fun w hw => GlobalTheory.LatAlmostStd.evalV_single_ne v 1 hw⟩`. Use `⟨pairA D.host.F 0 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (1 : D.host.E), ?_, ⟨GlobalTheory.FinPl.LatMem.tmul_mem_idAt hs.2 _, AddSubgroup.subset_closure ⟨_, hs.1, 1, rfl⟩⟩, fun a ha => ((placeIdem_acts D v _ hp).1 a).1 ha⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `pairA D.host.F 0 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (D.sp.cm.sig (1 : D.host.E)) = _`.

Rewrite using `[map_one]`.
-/
theorem exists_idem (v : Pl D) :
    ∃ ε : AE D, cA D ε = ε ∧ ε ∈ intAt D (· = v) ∧ ∀ a, a ∈ idAt D (· = v) → ε * a = a := by
  have hs := GlobalTheory.LatAlmostStd.intSupp_single_mul v (α := 1) (fun w => by rw [map_one]; exact one_mem _)
  rw [mul_one] at hs
  have hp : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨_, rfl, GlobalTheory.LatAlmostStd.evalV_single_same v 1, fun w hw => GlobalTheory.LatAlmostStd.evalV_single_ne v 1 hw⟩
  refine ⟨pairA D.host.F 0 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (1 : D.host.E), ?_,
    ⟨GlobalTheory.FinPl.LatMem.tmul_mem_idAt hs.2 _, AddSubgroup.subset_closure ⟨_, hs.1, 1, rfl⟩⟩,
    fun a ha => ((placeIdem_acts D v _ hp).1 a).1 ha⟩
  change pairA D.host.F 0 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (D.sp.cm.sig (1 : D.host.E)) = _
  rw [map_one]

variable {S : HSp D}

/- English proof (translation)
Unfold `hermAt pairing FrameLat.row`. Rewrite using `[Finset.sum_comm, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[RingHom.map_mul, RingHom.map_mul, cA_incA, show gA S i j = incA D (S.gram i j) from rfl]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermAt_mul_inc (y : Fin S.rank → AE D) (a : AE D) (s : Fin S.rank → D.host.E) :
    hermAt S y (fun i => a * incA D (s i)) = cA D a * pairing S s y := by
  unfold hermAt pairing FrameLat.row
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.map_mul, RingHom.map_mul, cA_incA, show gA S i j = incA D (S.gram i j) from rfl]
  ring

/- English proof (translation)
Unfold `hermAt`. Simplify using `only [map_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm (s := Finset.univ (α := Fin m))]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.
-/
theorem hermAt_sum_right {m : ℕ} (y : Fin S.rank → AE D) (x : Fin m → Fin S.rank → AE D) :
    hermAt S y (fun i => ∑ l, x l i) = ∑ l, hermAt S y (x l) := by
  unfold hermAt
  simp only [map_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.univ (α := Fin m))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

/- English proof (translation)
The claim follows from `Ideal.sum_mem _ fun _ _ => Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)`.
-/
theorem hermAt_mem_idAt {P : Pl D → Prop} {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D P)
    (x : Fin S.rank → AE D) : hermAt S y x ∈ idAt D P :=
  Ideal.sum_mem _ fun _ _ => Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

variable {L : Lat S}

/- English proof (translation)
Take `⟨N, hN, -, h⟩` from `GlobalTheory.LatAlmostStd.exists_commensurable L hL.1`. Use `⟨N.natAbs, Int.natAbs_pos.2 hN, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h1 : (N : AE D) • y ∈ latV S L (· = v)`. Establish `e : (N : AE D) • y = ∑ i, fun k => y i * incA D ((Pi.single i (N • ((1 : 𝓞 D.host.E) : D.host.E)) : Fin S.rank → D.host.E) k)`. Use function extensionality and compare the values at `k`.

Rewrite using `[Finset.sum_apply, Finset.sum_eq_single k]`. Rewrite using `[Pi.single_eq_same, map_zsmul, show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, RingHom.map_one, zsmul_one, Pi.smul_apply, smul_eq_mul, mul_comm]`. Introduce `i _ hi`. Rewrite using `[Pi.single_eq_of_ne' hi, RingHom.map_zero, mul_zero]`. Introduce `hk`.

Conclude with `absurd (Finset.mem_univ k) hk`. Rewrite using `[e]`. Conclude with `sum_mem fun i _ => int_mul_mem (hy i) (h i 1)`. Break down `Int.natAbs_eq N with e | e` into its components or cases. Rewrite using `[← Int.cast_natCast, ← e]`.

Conclude with `h1`. Establish `e' : ((N.natAbs : ℕ) : ℤ) = -N` using `by omega`. Rewrite using `[← Int.cast_natCast, e', Int.cast_neg, neg_smul]`. Conclude with `neg_mem h1`.
-/
theorem exists_mul_mem (hL : IsSelfDualC S L) (v : Pl D) :
    ∃ m : ℕ, 0 < m ∧ ∀ y : Fin S.rank → AE D, (∀ i, y i ∈ intAt D (· = v)) → (m : AE D) • y ∈ latV S L (· = v) := by
  obtain ⟨N, hN, -, h⟩ := GlobalTheory.LatAlmostStd.exists_commensurable L hL.1
  refine ⟨N.natAbs, Int.natAbs_pos.2 hN, fun y hy => ?_⟩
  have h1 : (N : AE D) • y ∈ latV S L (· = v) := by
    have e : (N : AE D) • y = ∑ i, fun k => y i * incA D ((Pi.single i (N • ((1 : 𝓞 D.host.E) : D.host.E)) :
        Fin S.rank → D.host.E) k) := by
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · rw [Pi.single_eq_same, map_zsmul, show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, RingHom.map_one,
          zsmul_one, Pi.smul_apply, smul_eq_mul, mul_comm]
      · intro i _ hi
        rw [Pi.single_eq_of_ne' hi, RingHom.map_zero, mul_zero]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    rw [e]
    exact sum_mem fun i _ => int_mul_mem (hy i) (h i 1)
  rcases Int.natAbs_eq N with e | e
  · rw [← Int.cast_natCast, ← e]; exact h1
  · have e' : ((N.natAbs : ℕ) : ℤ) = -N := by omega
    rw [← Int.cast_natCast, e', Int.cast_neg, neg_smul]; exact neg_mem h1

/- English proof (translation)
Introduce `D S L v hL`. Use `⟨fun y hy i => latV_supp hy i, exists_mul_mem hL v, fun y hy => ⟨fun hyL x hx => ?_, fun h => ?_⟩⟩` and prove the remaining obligations. Use `⟨hermAt_mem_idAt hy x, ?_⟩` and prove the remaining obligations. Take `⟨m, s, s', hs, hs', hd⟩` from `exists_expansion hL`. Establish `e : x = fun i => ∑ l, (fun l i => pairing S (s' l) x * incA D (s l i)) l i` using `funext fun i => hd x i`.

Rewrite using `[e, hermAt_sum_right, map_sum]`. Use `sum_mem fun l _ => ?_` and prove the remaining obligations. Rewrite using `[hermAt_mul_inc, RingHom.map_mul]`. Conclude with `mul_mem_intAE ((cA_int_iff _).2 (pairing_int hL (hs' l) hx)) (pairing_int hL (hs l) hyL)`. Take `⟨ε, hc, hε, hact⟩` from `exists_idem v`.

Use `mem_of_pairing hL hy fun s hs => ?_` and prove the remaining obligations. Establish `h1` using `(h _ (int_mul_mem hε hs)).2`. Rewrite `h1` using `[hermAt_mul_inc, hc, hact (pairing S s y) (Ideal.sum_mem _ fun b _ => Ideal.mul_mem_left _ _ (hy b))]`. Then use the resulting hypothesis.
-/
theorem isSDAt_latV : ∀ (D : D7) (S : HSp D) (L : Lat S) (v : Pl D), IsSelfDualC S L → IsSDAt S v (latV S L (· = v)) := by
  intro D S L v hL
  refine ⟨fun y hy i => latV_supp hy i, exists_mul_mem hL v, fun y hy => ⟨fun hyL x hx => ?_, fun h => ?_⟩⟩
  · refine ⟨hermAt_mem_idAt hy x, ?_⟩
    obtain ⟨m, s, s', hs, hs', hd⟩ := exists_expansion hL
    have e : x = fun i => ∑ l, (fun l i => pairing S (s' l) x * incA D (s l i)) l i := funext fun i => hd x i
    rw [e, hermAt_sum_right, map_sum]
    refine sum_mem fun l _ => ?_
    rw [hermAt_mul_inc, RingHom.map_mul]
    exact mul_mem_intAE ((cA_int_iff _).2 (pairing_int hL (hs' l) hx)) (pairing_int hL (hs l) hyL)
  · obtain ⟨ε, hc, hε, hact⟩ := exists_idem v
    refine mem_of_pairing hL hy fun s hs => ?_
    have h1 := (h _ (int_mul_mem hε hs)).2
    rwa [hermAt_mul_inc, hc, hact (pairing S s y) (Ideal.sum_mem _ fun b _ => Ideal.mul_mem_left _ _ (hy b))] at h1

end GlobalTheory.IwaPlace.LocSD

end
