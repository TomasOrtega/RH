import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsDividedPowersAug
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.FilIsSubDPIdeal
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.RingTrunc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerPolynomialFiltrationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleLiftingOfNilIdealStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

namespace GlobalTheory.CompanionTheory.SiteTr

/- English proof (translation)
Introduce `B _ J δ l s δ' hδ' hs ht`. Take `⟨-, hanti, h0, crit⟩` from `GlobalTheory.T.divided_power_polynomial_filtration δ (pq B) (eta δ) (eta_std δ)`. Establish `hanti' : ∀ a c, a ≤ c → fil (eta δ) c ≤ fil (eta δ) a` using `fun a c h => GlobalTheory.Cris.ExpBij.dpFil_anti (eta δ) h`. Establish `hmap : ∀ r, fil δ' r = (fil (eta δ) r).map (Ideal.Quotient.mk (fil (eta δ) (max s 1)))` using `fun r => le_antisymm (FubiniStudyChowHeightFormula₂.Adr.Fil.fil_le_map_fil _ _ (eta δ) _ _ δ' _ hδ' rfl r) (FubiniStudyChowHeightFormula₂.Adr.Fil.map_fil_le (eta δ) δ' _ hδ' r)`. Establish `htop : fil δ' (max s 1) = ⊥` using `by rw [hmap, Ideal.map_quotient_self]`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos s with rfl | hpos` into its components or cases. Establish `h10 : (1 : B) = 0`. Establish `: (1 : B) ∈ fil δ 0` using `by rw [h0]; trivial`. Rewrite `this` using `[hs, Ideal.mem_bot]`. Then use the resulting hypothesis.

Use `haveI : Subsingleton B := subsingleton_of_zero_eq_one h10.symm`. Use `haveI : Subsingleton (pq B).P := Module.subsingleton B (pq B).P`. Use `haveI : Subsingleton ((pq B).P ⧸ fil (eta δ) (max 0 1)) := Ideal.Quotient.mk_surjective.subsingleton`. Conclude with `eq_bot_iff.2 fun x _ => (Ideal.mem_bot).2 (Subsingleton.elim x 0)`. Establish `e : fil (eta δ) s = fil (eta δ) (max s 1)` using `by rw [max_eq_left hpos]`.

Rewrite using `[hmap, e, Ideal.map_quotient_self]`. Introduce `r x hx`. Take `⟨z, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Establish `key : ∀ y : (pq B).P, Ideal.Quotient.mk (fil (eta δ) (max s 1)) y ∈ fil δ' r ↔ y ∈ fil (eta δ) (min r (max s 1))`. Introduce `y`.

Rewrite using `[hmap, Ideal.mem_quotient_iff_mem_sup]`. Break down `le_total r (max s 1) with h | h` into its components or cases. Rewrite using `[min_eq_left h, sup_eq_left.2 (hanti' _ _ h)]`. Rewrite using `[min_eq_right h, sup_eq_right.2 (hanti' _ _ h)]`. Establish `hz : (l : (pq B).P) * z ∈ fil (eta δ) (min r (max s 1))` using `(key _).1 (by simpa only [map_mul, map_natCast] using hx)`.

Use `(key z).2 ((crit _ z).2 fun k => ht _ _ ?_)` and prove the remaining obligations. Establish `h1` using `(crit _ _).1 hz k`. Establish `e : (pq B).e.repr ((l : (pq B).P) * z) k = (l : B) * (pq B).e.repr z k`. Rewrite using `[← nsmul_eq_mul, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]`. Rewrite `h1` using `[e]`. Then use the resulting hypothesis.

Establish `hp : ∀ n, (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1)))) ^ n ≤ fil δ' n`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `a _`.

Conclude with `GlobalTheory.Cris.ExpBij.mem_dpFil_zero δ' a`. Consider the case `succ n ih`. Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_le.2 fun a ha b hb => GlobalTheory.Cris.ExpBij.mul_mem_dpFil δ' (ih ha) (GlobalTheory.Cris.ExpBij.mem_dpFil_one δ' hb)`. Conclude with `⟨max s 1, le_bot_iff.1 ((hp _).trans htop.le)⟩`.
-/
theorem tr_tf : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (l s : ℕ) (δ' : DividedPowers (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))))), IsDPMorphism (eta δ) δ' (Ideal.Quotient.mk (fil (eta δ) (max s 1))) → fil δ s = ⊥ → (∀ (r : ℕ) (x : B), (l : B) * x ∈ fil δ r → x ∈ fil δ r) → fil δ' s = ⊥ ∧ (∀ (r : ℕ) (x : (pq B).P ⧸ fil (eta δ) (max s 1)), (l : (pq B).P ⧸ fil (eta δ) (max s 1)) * x ∈ fil δ' r → x ∈ fil δ' r) ∧ IsNilpotent (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1)))) := by
  intro B _ J δ l s δ' hδ' hs ht
  obtain ⟨-, hanti, h0, crit⟩ := GlobalTheory.T.divided_power_polynomial_filtration δ (pq B) (eta δ) (eta_std δ)
  have hanti' : ∀ a c, a ≤ c → fil (eta δ) c ≤ fil (eta δ) a := fun a c h =>
    GlobalTheory.Cris.ExpBij.dpFil_anti (eta δ) h
  have hmap : ∀ r, fil δ' r = (fil (eta δ) r).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))) := fun r =>
    le_antisymm (FubiniStudyChowHeightFormula₂.Adr.Fil.fil_le_map_fil _ _ (eta δ) _ _ δ' _ hδ' rfl r)
      (FubiniStudyChowHeightFormula₂.Adr.Fil.map_fil_le (eta δ) δ' _ hδ' r)
  have htop : fil δ' (max s 1) = ⊥ := by rw [hmap, Ideal.map_quotient_self]
  refine ⟨?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos s with rfl | hpos
    · have h10 : (1 : B) = 0 := by
        have : (1 : B) ∈ fil δ 0 := by rw [h0]; trivial
        rwa [hs, Ideal.mem_bot] at this
      haveI : Subsingleton B := subsingleton_of_zero_eq_one h10.symm
      haveI : Subsingleton (pq B).P := Module.subsingleton B (pq B).P
      haveI : Subsingleton ((pq B).P ⧸ fil (eta δ) (max 0 1)) :=
        Ideal.Quotient.mk_surjective.subsingleton
      exact eq_bot_iff.2 fun x _ => (Ideal.mem_bot).2 (Subsingleton.elim x 0)
    · have e : fil (eta δ) s = fil (eta δ) (max s 1) := by rw [max_eq_left hpos]
      rw [hmap, e, Ideal.map_quotient_self]
  · intro r x hx
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    have key : ∀ y : (pq B).P, Ideal.Quotient.mk (fil (eta δ) (max s 1)) y ∈ fil δ' r ↔
        y ∈ fil (eta δ) (min r (max s 1)) := by
      intro y
      rw [hmap, Ideal.mem_quotient_iff_mem_sup]
      rcases le_total r (max s 1) with h | h
      · rw [min_eq_left h, sup_eq_left.2 (hanti' _ _ h)]
      · rw [min_eq_right h, sup_eq_right.2 (hanti' _ _ h)]
    have hz : (l : (pq B).P) * z ∈ fil (eta δ) (min r (max s 1)) :=
      (key _).1 (by simpa only [map_mul, map_natCast] using hx)
    refine (key z).2 ((crit _ z).2 fun k => ht _ _ ?_)
    have h1 := (crit _ _).1 hz k
    have e : (pq B).e.repr ((l : (pq B).P) * z) k = (l : B) * (pq B).e.repr z k := by
      rw [← nsmul_eq_mul, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
    rwa [e] at h1
  · have hp : ∀ n, (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1)))) ^ n ≤ fil δ' n := by
      intro n
      induction n with
      | zero =>
        intro a _
        exact GlobalTheory.Cris.ExpBij.mem_dpFil_zero δ' a
      | succ n ih =>
        rw [pow_succ]
        exact Ideal.mul_le.2 fun a ha b hb =>
          GlobalTheory.Cris.ExpBij.mul_mem_dpFil δ' (ih ha) (GlobalTheory.Cris.ExpBij.mem_dpFil_one δ' hb)
    exact ⟨max s 1, le_bot_iff.1 ((hp _).trans htop.le)⟩

end GlobalTheory.CompanionTheory.SiteTr
