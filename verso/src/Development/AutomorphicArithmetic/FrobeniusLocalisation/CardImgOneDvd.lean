import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.RdArith

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

/- English proof (translation)
Establish `hAB : A.map a ≤ B.map a` using `Subgroup.map_mono h`. Establish `hc : Nat.card (B.map a) = Nat.card (A.map a) * (A.map a).relIndex (B.map a)`. Rewrite using `[Subgroup.relIndex, ← Subgroup.card_mul_index ((A.map a).subgroupOf (B.map a))]`. Use `congr 1`. Conclude with `Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv`.

Rewrite using `[hc]`. Apply `mul_dvd_mul_left` to reduce the goal to its premises. Rewrite using `[← Subgroup.relIndex_comap]`. Conclude with `Subgroup.relIndex_dvd_of_le_left B (Subgroup.le_comap_map a A)`.
-/
private theorem card_map_dvd {G G' : Type*} [Group G] [Group G'] (a : G →* G') {A B : Subgroup G} (h : A ≤ B) :
    Nat.card (B.map a) ∣ Nat.card (A.map a) * A.relIndex B := by
  have hAB : A.map a ≤ B.map a := Subgroup.map_mono h
  have hc : Nat.card (B.map a) = Nat.card (A.map a) * (A.map a).relIndex (B.map a) := by
    rw [Subgroup.relIndex, ← Subgroup.card_mul_index ((A.map a).subgroupOf (B.map a))]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
  rw [hc]
  apply mul_dvd_mul_left
  rw [← Subgroup.relIndex_comap]
  exact Subgroup.relIndex_dvd_of_le_left B (Subgroup.le_comap_map a A)

/- English proof (translation)
Establish `hN : H.condN ≠ 0` using `H.condN_ne_zero`. Establish `hf0 : f ≠ 0`. Introduce and unpack `rfl`. Conclude with `hN (zero_dvd_iff.1 hf)`. Establish `hg : Nat.gcd f H.condN = f` using `Nat.gcd_eq_left hf`.

Use `haveI : NeZero (Nat.gcd f H.condN) := ⟨by rw [hg]; exact hf0⟩`. Unfold `HostRaw.unitsOne`. Rewrite using `[Subgroup.index_ker, MonoidHom.range_eq_top.2 (ZMod.unitsMap_surjective _), Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, hg]`.
-/
private theorem index_unitsOne {φ : Frame} (H : HostRaw φ) {f : ℕ} (hf : f ∣ H.condN) :
    (H.unitsOne f).index = f.totient := by
  have hN : H.condN ≠ 0 := H.condN_ne_zero
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hN (zero_dvd_iff.1 hf)
  have hg : Nat.gcd f H.condN = f := Nat.gcd_eq_left hf
  haveI : NeZero (Nat.gcd f H.condN) := ⟨by rw [hg]; exact hf0⟩
  unfold HostRaw.unitsOne
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 (ZMod.unitsMap_surjective _), Subgroup.card_top,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, hg]

/- English proof (translation)
Introduce `φ H f g hfg hg`. Establish `hf : f ∣ H.condN` using `hfg.trans hg`. Establish `hle : H.unitsOne g ≤ H.unitsOne f`. Introduce `u hu`. Rewrite `hu` using `[H.mem_unitsOne hg]`.

Rewrite using `[H.mem_unitsOne hf]`. Conclude with `Nat.ModEq.of_dvd hfg hu`. Establish `hd` using `card_map_dvd H.art hle`. Establish `hidx` using `Subgroup.relIndex_mul_index hle`. Rewrite `hidx` using `[index_unitsOne H hf, index_unitsOne H hg]`.

Establish `hf0 : 0 < f`. Break down `Nat.eq_zero_or_pos f with h0 | h0` into its components or cases. It suffices to derive a contradiction. Substitute `h0` using the available equality. Conclude with `H.condN_ne_zero (zero_dvd_iff.1 hf)`.

Conclude with `h0`. Establish `htot : 0 < f.totient` using `Nat.totient_pos.2 hf0`. Establish `hr : g.totient / f.totient = (H.unitsOne g).relIndex (H.unitsOne f)`. Rewrite using `[← hidx, Nat.mul_div_cancel _ htot]`. Rewrite using `[hr]`.

Conclude with `hd`.
-/
theorem UpperTheory.HF.card_imgOne_dvd :
    ∀ {φ : Frame} (H : HostRaw φ) {f g : ℕ}, f ∣ g → g ∣ H.condN → Nat.card (H.imgOne f) ∣ Nat.card (H.imgOne g) * (g.totient / f.totient) := by
  intro φ H f g hfg hg
  have hf : f ∣ H.condN := hfg.trans hg
  have hle : H.unitsOne g ≤ H.unitsOne f := by
    intro u hu
    rw [H.mem_unitsOne hg] at hu
    rw [H.mem_unitsOne hf]
    exact Nat.ModEq.of_dvd hfg hu
  have hd := card_map_dvd H.art hle
  have hidx := Subgroup.relIndex_mul_index hle
  rw [index_unitsOne H hf, index_unitsOne H hg] at hidx
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exfalso
      subst h0
      exact H.condN_ne_zero (zero_dvd_iff.1 hf)
    · exact h0
  have htot : 0 < f.totient := Nat.totient_pos.2 hf0
  have hr : g.totient / f.totient = (H.unitsOne g).relIndex (H.unitsOne f) := by
    rw [← hidx, Nat.mul_div_cancel _ htot]
  rw [hr]
  exact hd
