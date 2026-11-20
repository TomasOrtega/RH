import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGenAlt
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

/- English proof (translation)
Introduce `p _ n hn hdvd`. Establish `hp2 : 2 ≤ p` using `(Fact.out : p.Prime).two_le`. Take `⟨g, hg⟩` from `IsCyclic.exists_generator (α := (ZMod p)ˣ)`. Establish `hcard : Nat.card (ZMod p)ˣ = p - 1`. Rewrite using `[Nat.card_eq_fintype_card, ZMod.card_units]`.

Establish `hog : orderOf g = p - 1`. Rewrite using `[orderOf_eq_card_of_forall_mem_zpowers hg, hcard]`. Establish `hprim` using `Complex.isPrimitiveRoot_exp n hn.ne'`. Take `⟨ω, hωc⟩` from `hprim.isUnit hn.ne'`. Establish `hωp : IsPrimitiveRoot ω n`.

Rewrite using `[← IsPrimitiveRoot.coe_units_iff, hωc]`. Conclude with `hprim`. Establish `hωo : orderOf ω = n` using `hωp.eq_orderOf.symm`. Establish `hnd : n ∣ p - 1` using `Dvd.dvd.trans (Dvd.intro_left 2 rfl) hdvd`. Establish `hd : orderOf ω ∣ orderOf g` using `by rw [hωo, hog]; exact hnd`.

Set `lam : (ZMod p)ˣ →* ℂˣ` to `monoidHomOfForallMemZpowers hg hd`. Establish `hlg : lam g = ω` using `monoidHomOfForallMemZpowers_apply_gen hg hd`. Establish `hωn : ω ^ n = 1` using `hωp.pow_eq_one`. Establish `hpow : ∀ a, (lam a) ^ n = 1`. Introduce `a`.

Take `⟨k, rfl⟩` from `Subgroup.mem_zpowers_iff.mp (hg a)`. Rewrite using `[map_zpow, hlg, ← zpow_natCast, zpow_comm, zpow_natCast, hωn, one_zpow]`. Use `⟨lam, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `ext1 a`. Rewrite using `[MonoidHom.pow_apply, hpow, MonoidHom.one_apply]`.

Take `⟨c, hc⟩` from `hdvd`. Establish `hcpos : 0 < c`. Break down `Nat.eq_zero_or_pos c with h | h` into its components or cases. Substitute `h` using the available equality. Use linear arithmetic over natural numbers and integers.

Conclude with `h`. Establish `hx2 : (g ^ (n * c)) ^ 2 = 1`. Rewrite using `[← pow_mul, show n * c * 2 = p - 1 by rw [hc]; ring, ← hog, pow_orderOf_eq_one]`. Establish `hx1 : g ^ (n * c) ≠ 1`. Introduce `h`.

Establish `h1` using `orderOf_dvd_of_pow_eq_one h`. Rewrite `h1` using `[hog, hc]`. Establish `h2` using `Nat.le_of_dvd (Nat.mul_pos hn hcpos) h1`. Establish `h3 : 0 < n * c` using `Nat.mul_pos hn hcpos`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hxm : g ^ (n * c) = -1`. Establish `h4 : (((g ^ (n * c) : (ZMod p)ˣ)) : ZMod p) ^ 2 = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, hx2, Units.val_one]`. Rewrite `h4` using `[sq]`. Break down `mul_self_eq_one_iff.mp h4 with h | h` into its components or cases.

Conclude with `absurd (Units.ext (by rw [h, Units.val_one])) hx1`. Conclude with `Units.ext (by rw [h, Units.val_neg, Units.val_one])`. Rewrite using `[← hxm, map_pow, hlg, pow_mul, hωn, one_pow]`. Introduce `a ha`. Establish `htop : Subgroup.zpowers a = ⊤`.

Apply `Subgroup.eq_top_of_card_eq` to reduce the goal to its premises. Rewrite using `[Nat.card_zpowers, ha, hcard]`. Establish `hga : g ∈ Subgroup.zpowers a` using `by rw [htop]; trivial`. Take `⟨j, rfl⟩` from `Subgroup.mem_zpowers_iff.mp hga`. Establish `hωa : (lam a) ^ j = ω` using `by rw [← map_zpow, hlg]`.

Apply `Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one (hpow a))` to reduce the goal to its premises. Rewrite using `[← hωo]`. Apply `orderOf_dvd_of_pow_eq_one` to reduce the goal to its premises. Rewrite using `[← hωa, ← zpow_natCast, zpow_comm, zpow_natCast, pow_orderOf_eq_one, one_zpow]`.
-/
theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.powChar :
    PowChar := by
  intro p _ n hn hdvd
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hog : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hprim := Complex.isPrimitiveRoot_exp n hn.ne'
  obtain ⟨ω, hωc⟩ := hprim.isUnit hn.ne'
  have hωp : IsPrimitiveRoot ω n := by
    rw [← IsPrimitiveRoot.coe_units_iff, hωc]
    exact hprim
  have hωo : orderOf ω = n := hωp.eq_orderOf.symm
  have hnd : n ∣ p - 1 := Dvd.dvd.trans (Dvd.intro_left 2 rfl) hdvd
  have hd : orderOf ω ∣ orderOf g := by rw [hωo, hog]; exact hnd
  let lam : (ZMod p)ˣ →* ℂˣ := monoidHomOfForallMemZpowers hg hd
  have hlg : lam g = ω := monoidHomOfForallMemZpowers_apply_gen hg hd
  have hωn : ω ^ n = 1 := hωp.pow_eq_one
  have hpow : ∀ a, (lam a) ^ n = 1 := by
    intro a
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    rw [map_zpow, hlg, ← zpow_natCast, zpow_comm, zpow_natCast, hωn, one_zpow]
  refine ⟨lam, ?_, ?_, ?_⟩
  · ext1 a
    rw [MonoidHom.pow_apply, hpow, MonoidHom.one_apply]
  · obtain ⟨c, hc⟩ := hdvd
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h
        omega
      · exact h
    have hx2 : (g ^ (n * c)) ^ 2 = 1 := by
      rw [← pow_mul, show n * c * 2 = p - 1 by rw [hc]; ring, ← hog, pow_orderOf_eq_one]
    have hx1 : g ^ (n * c) ≠ 1 := by
      intro h
      have h1 := orderOf_dvd_of_pow_eq_one h
      rw [hog, hc] at h1
      have h2 := Nat.le_of_dvd (Nat.mul_pos hn hcpos) h1
      have h3 : 0 < n * c := Nat.mul_pos hn hcpos
      nlinarith
    have hxm : g ^ (n * c) = -1 := by
      have h4 : (((g ^ (n * c) : (ZMod p)ˣ)) : ZMod p) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, hx2, Units.val_one]
      rw [sq] at h4
      rcases mul_self_eq_one_iff.mp h4 with h | h
      · exact absurd (Units.ext (by rw [h, Units.val_one])) hx1
      · exact Units.ext (by rw [h, Units.val_neg, Units.val_one])
    rw [← hxm, map_pow, hlg, pow_mul, hωn, one_pow]
  · intro a ha
    have htop : Subgroup.zpowers a = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, ha, hcard]
    have hga : g ∈ Subgroup.zpowers a := by rw [htop]; trivial
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hga
    have hωa : (lam a) ^ j = ω := by rw [← map_zpow, hlg]
    apply Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one (hpow a))
    rw [← hωo]
    apply orderOf_dvd_of_pow_eq_one
    rw [← hωa, ← zpow_natCast, zpow_comm, zpow_natCast, pow_orderOf_eq_one, one_zpow]
