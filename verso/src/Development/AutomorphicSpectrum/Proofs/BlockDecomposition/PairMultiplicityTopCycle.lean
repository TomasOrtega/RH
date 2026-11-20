import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient
open GlobalTheory.CompanionTheory.PairMult

noncomputable section

open Finset
open CompanionTheory.D.LK (Pos)

namespace GlobalTheory.CompanionTheory.PairMult.TopCycQ

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem annq_app (l : Lt n) (x : Cq n V) (B : Finset (Lt n)) :
    annq l x B = if l ∈ B then 0 else sgL l B • x (insert l B) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem creq_app (l : Lt n) (x : Cq n V) (B : Finset (Lt n)) :
    creq l x B = if l ∈ B then sgL l B • x (B.erase l) else 0 := rfl

/- English proof (translation)
Simplify using `[omQ]`.
-/
theorem mem_omQ (lev : Fin n → ℕ) (l : Lt n) :
    l ∈ omQ lev ↔ l.1 = true ∧ lev l.2.1.1 < lev l.2.1.2 := by
  simp [omQ]

/- English proof (translation)
Introduce `e`. Establish `hi` using `(mem_omQ lev _).1 (e ▸ mem_insert_self _ _)`. Establish `hj` using `(mem_omQ lev _).1 (e ▸ mem_insert_of_mem (mem_insert_self _ _))`. Take `⟨t1, t2, t3⟩` from `ht`. Establish `hs : s = true` using `hi.1`.

Establish `htt : t = true` using `hj.1`. Substitute `hs htt` using the available equality. Establish `ck : ((true == true), k) ∈ omQ lev` using `(mem_omQ lev _).2 ⟨rfl, by rw [t2, t3]; exact (hi.2.trans_eq (congrArg lev t1)).trans hj.2⟩`. Rewrite `ck` using `[← e]`. Break down `mem_insert.1 ck with h | h` into its components or cases.

Establish `hk : k = i` using `congrArg Prod.snd h`. Substitute `hk` using the available equality. Establish `pj` using `j.2`. Rewrite `pj` using `[← t1, t3]`. Conclude with `lt_irrefl _ pj`.

Break down `mem_insert.1 h with h | h` into its components or cases. Establish `hk : k = j` using `congrArg Prod.snd h`. Substitute `hk` using the available equality. Establish `pi` using `i.2`. Rewrite `pi` using `[← t2, t1]`.

Conclude with `lt_irrefl _ pi`. Conclude with `notMem_erase _ _ h`.
-/
theorem insert_ne_omQ (lev : Fin n → ℕ) (s t : Bool) (i j k : Pos n)
    (ht : i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2) (C : Finset (Lt n)) :
    insert (s, i) (insert (t, j) (C.erase ((s == t), k))) ≠ omQ lev := by
  intro e
  have hi := (mem_omQ lev _).1 (e ▸ mem_insert_self _ _)
  have hj := (mem_omQ lev _).1 (e ▸ mem_insert_of_mem (mem_insert_self _ _))
  obtain ⟨t1, t2, t3⟩ := ht
  have hs : s = true := hi.1
  have htt : t = true := hj.1
  subst hs htt
  have ck : ((true == true), k) ∈ omQ lev := (mem_omQ lev _).2
    ⟨rfl, by rw [t2, t3]; exact (hi.2.trans_eq (congrArg lev t1)).trans hj.2⟩
  rw [← e] at ck
  rcases mem_insert.1 ck with h | h
  · have hk : k = i := congrArg Prod.snd h
    subst hk
    have pj := j.2
    rw [← t1, t3] at pj
    exact lt_irrefl _ pj
  · rcases mem_insert.1 h with h | h
    · have hk : k = j := congrArg Prod.snd h
      subst hk
      have pi := i.2
      rw [← t2, t1] at pi
      exact lt_irrefl _ pi
    · exact notMem_erase _ _ h

/- English proof (translation)
Introduce `n lev V _ _ E1 E2 _ v hv`. Use function extensionality and compare the values at `A`. Simplify using `only [bdq, LinearMap.add_apply, LinearMap.sum_apply, Pi.add_apply, Finset.sum_apply, Pi.zero_apply]`. Rewrite using `[Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]`. Introduce `s _`.

Use `Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Use `split_ifs with ht`. Rewrite using `[Module.End.mul_apply, Module.End.mul_apply, creq_app] split_ifs with hk`. Rewrite using `[annq_app] split_ifs with h1`. Conclude with `smul_zero _`.

Rewrite using `[annq_app] split_ifs with h2`. Simplify using the standard rewrite rules. Rewrite using `[topq, Pi.single_eq_of_ne (insert_ne_omQ lev s t i j k ht A), smul_zero, smul_zero, smul_zero]`. Both sides reduce to the same expression. Both sides reduce to the same expression.

Introduce `l _ show Tl E1 E2 l (annq l (topq lev v) A) = 0`. Rewrite using `[annq_app]`. Use `split_ifs with hl`. Conclude with `map_zero _`. Distinguish the cases in `e : insert l A = omQ lev`.

Establish `hlK` using `(mem_omQ lev l).1 (e ▸ mem_insert_self l A)`. Rewrite using `[topq, e, Pi.single_eq_same, map_smul, hv l hlK, smul_zero]`. Rewrite using `[topq, Pi.single_eq_of_ne e, smul_zero, map_zero]`.
-/
theorem topCyc : TopCyc := by
  intro n lev V _ _ E1 E2 _ v hv
  funext A
  simp only [bdq, LinearMap.add_apply, LinearMap.sum_apply, Pi.add_apply, Finset.sum_apply, Pi.zero_apply]
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · intro s _
    refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
      Finset.sum_eq_zero fun k _ => ?_
    split_ifs with ht
    · rw [Module.End.mul_apply, Module.End.mul_apply, creq_app]
      split_ifs with hk
      · rw [annq_app]
        split_ifs with h1
        · exact smul_zero _
        · rw [annq_app]
          split_ifs with h2
          · simp
          · rw [topq, Pi.single_eq_of_ne (insert_ne_omQ lev s t i j k ht A), smul_zero, smul_zero, smul_zero]
      · rfl
    · rfl
  · intro l _
    show Tl E1 E2 l (annq l (topq lev v) A) = 0
    rw [annq_app]
    split_ifs with hl
    · exact map_zero _
    · by_cases e : insert l A = omQ lev
      · have hlK := (mem_omQ lev l).1 (e ▸ mem_insert_self l A)
        rw [topq, e, Pi.single_eq_same, map_smul, hv l hlK, smul_zero]
      · rw [topq, Pi.single_eq_of_ne e, smul_zero, map_zero]

end GlobalTheory.CompanionTheory.PairMult.TopCycQ
