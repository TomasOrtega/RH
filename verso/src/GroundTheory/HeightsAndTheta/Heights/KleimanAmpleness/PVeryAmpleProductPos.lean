import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleProductPosSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PointDegreePosSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutComponentSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutMultPosSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

/- English proof (translation)
Introduce `k _ Ω _ _ N x e`. Proceed by induction on `e with`. Consider the case `zero`. Introduce `pp L hW _`. Establish `h0 : (fun i => (L i).toSubSystem) = (![] : Fin 0 → SubSystem k x Ω)`.

Use function extensionality and compare the values at `fun i => i.elim0`. Rewrite using `[h0, (hR k Ω N x).2.2.2.2 pp hW]`. Conclude with `hP k Ω N x pp hW` after adjusting the coercions. Consider the case `succ n ih`. Introduce `pp L hW hL`.

Take `⟨s, hs, hsI⟩` from `exists_sec_not_mem (L (Fin.last n)) (hL _) hW`. Establish `hsplit : (fun i => (L i).toSubSystem) = Fin.snoc (α` using `fun _ => SubSystem k x Ω) (fun i : Fin n => (L (Fin.castSucc i)).toSubSystem) (L (Fin.last n)).toSubSystem := (Fin.snoc_init_self _).symm`. Rewrite using `[hsplit, (hR k Ω N x).2.2.2.1 n pp (fun i => L (Fin.castSucc i)) (L (Fin.last n)) s hW hs hsI]`. Take `⟨q₀, hq₀, hq₀W⟩` from `hC k Ω N x n pp (L (Fin.last n)) s hW (hL _) hs hsI`. Establish `hterm : ∀ qq (h : qq ∈ (pp ⊔ zeroIdeal (L (Fin.last n)).toSubSystem s).minimalPrimes), IsSubvar x qq n → haveI : qq.IsPrime` using `h.1.1 0 < (((cutMult (pp ⊔ zeroIdeal (L (Fin.last n)).toSubSystem s) qq).toNat : ℤ) * interNum qq (fun i => (L (Fin.castSucc i)).toSubSystem)) := by`.

Introduce `qq h hqW`. Establish `hm` using `hM k N _ qq h`. Conclude with `mul_pos (by exact_mod_cast ENat.toNat_pos hm.1.ne' hm.2.ne) (ih qq _ hqW fun i => hL _)`. Use `lt_of_lt_of_le ?_ (single_le_finsum q₀ ?_ ?_)` and prove the remaining obligations. Rewrite using `[dif_pos ⟨hq₀, hq₀W⟩]`.

Conclude with `hterm q₀ hq₀ hq₀W`. Use `(Ideal.finite_minimalPrimes_of_isNoetherianRing _ (pp ⊔ zeroIdeal (L (Fin.last n)).toSubSystem s)).subset fun qq hqq => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Conclude with `hqq (dif_neg fun h => hn h.1)`. Introduce `qq split_ifs with h`.

Conclude with `(hterm qq h.1 h.2).le`. Conclude with `le_rfl`.
-/
theorem VeryAmpleProductPos.proof (hR : GenericPointSectionInput.Statement.{u, w}) (hP : PointDegreePos.Statement.{u, w})
    (hC : CutComponent.Statement.{u, w}) (hM : CutMultPos.Statement.{u}) :
    VeryAmpleProductPos.Statement.{u, w} := by
  intro k _ Ω _ _ N x e
  induction e with
  | zero =>
    intro pp L hW _
    have h0 : (fun i => (L i).toSubSystem) = (![] : Fin 0 → SubSystem k x Ω) :=
      funext fun i => i.elim0
    rw [h0, (hR k Ω N x).2.2.2.2 pp hW]
    exact_mod_cast hP k Ω N x pp hW
  | succ n ih =>
    intro pp L hW hL
    obtain ⟨s, hs, hsI⟩ := exists_sec_not_mem (L (Fin.last n)) (hL _) hW
    have hsplit : (fun i => (L i).toSubSystem) = Fin.snoc (α := fun _ => SubSystem k x Ω)
        (fun i : Fin n => (L (Fin.castSucc i)).toSubSystem) (L (Fin.last n)).toSubSystem :=
      (Fin.snoc_init_self _).symm
    rw [hsplit, (hR k Ω N x).2.2.2.1 n pp (fun i => L (Fin.castSucc i)) (L (Fin.last n)) s hW hs hsI]
    obtain ⟨q₀, hq₀, hq₀W⟩ := hC k Ω N x n pp (L (Fin.last n)) s hW (hL _) hs hsI

    have hterm : ∀ qq (h : qq ∈ (pp ⊔ zeroIdeal (L (Fin.last n)).toSubSystem s).minimalPrimes),
        IsSubvar x qq n → haveI : qq.IsPrime := h.1.1
        0 < (((cutMult (pp ⊔ zeroIdeal (L (Fin.last n)).toSubSystem s) qq).toNat : ℤ) *
          interNum qq (fun i => (L (Fin.castSucc i)).toSubSystem)) := by
      intro qq h hqW
      have hm := hM k N _ qq h
      exact mul_pos (by exact_mod_cast ENat.toNat_pos hm.1.ne' hm.2.ne) (ih qq _ hqW fun i => hL _)
    refine lt_of_lt_of_le ?_ (single_le_finsum q₀ ?_ ?_)
    · rw [dif_pos ⟨hq₀, hq₀W⟩]
      exact hterm q₀ hq₀ hq₀W
    · refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _
        (pp ⊔ zeroIdeal (L (Fin.last n)).toSubSystem s)).subset fun qq hqq => ?_
      by_contra hn
      exact hqq (dif_neg fun h => hn h.1)
    · intro qq
      split_ifs with h
      · exact (hterm qq h.1 h.2).le
      · exact le_rfl

end

end GroundTheory.Heights₂.Heights.Kleiman
