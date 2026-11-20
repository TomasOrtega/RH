import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.PrincTop
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.NuBasic

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Introduce `u hu`. Use `mem_levelGroup.mpr ⟨1, H.one_mem, ?_⟩` and prove the remaining obligations. Rewrite using `[map_one]`. Conclude with `(MonoidHom.mem_ker.mp hu).symm`.
-/
private theorem lv_princ_le (N : ℕ) (H : Subgroup (ZMod N)ˣ) :
    princ l (N.factorization l) ≤ levelGroup l N H := by
  intro u hu
  refine mem_levelGroup.mpr ⟨1, H.one_mem, ?_⟩
  rw [map_one]
  exact (MonoidHom.mem_ker.mp hu).symm

/- English proof (translation)
Introduce `v`. Take `⟨k, hk⟩` from `ZMod.natCast_zmod_surjective (v : ZMod l)`. Establish `hx : PadicInt.toZMod (k : ℤ_[l]) = (v : ZMod l)`. Rewrite using `[map_natCast, hk]`. Establish `hu : IsUnit (k : ℤ_[l])`.

Assume the negation of the conclusion as `hne`. Establish `hm : (k : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l]` using `hne`. Rewrite `hm` using `[← PadicInt.ker_toZMod, RingHom.mem_ker, hx]`. Conclude with `v.ne_zero hm`. Use `⟨hu.unit, Units.ext ?_⟩` and prove the remaining obligations.

Simplify using `[red, hx]`.
-/
private theorem lv_red_surjective : Function.Surjective (red l) := by
  intro v
  obtain ⟨k, hk⟩ := ZMod.natCast_zmod_surjective (v : ZMod l)
  have hx : PadicInt.toZMod (k : ℤ_[l]) = (v : ZMod l) := by
    rw [map_natCast, hk]
  have hu : IsUnit (k : ℤ_[l]) := by
    by_contra hne
    have hm : (k : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := hne
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, hx] at hm
    exact v.ne_zero hm
  refine ⟨hu.unit, Units.ext ?_⟩
  simp [red, hx]

/- English proof (translation)
Assemble the required witnesses or components as `⟨lv_princ_le N H, Subgroup.isOpen_mono (lv_princ_le N H) (isOpen_princ _)⟩`.
-/
theorem princ_le_levelGroup (N : ℕ) (H : Subgroup (ZMod N)ˣ) :
    princ l (N.factorization l) ≤ levelGroup l N H ∧ IsOpen (levelGroup l N H : Set ℤ_[l]ˣ) :=
  ⟨lv_princ_le N H, Subgroup.isOpen_mono (lv_princ_le N H) (isOpen_princ _)⟩

/- English proof (translation)
Establish `h : levelGroup l N H = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `u _`. Apply `lv_princ_le N H` to reduce the goal to its premises. Rewrite using `[mem_princ, Nat.factorization_eq_zero_of_not_dvd hN, pow_zero]`.

Conclude with `one_dvd _`. Use `⟨h, ?_⟩` and prove the remaining obligations. Rewrite using `[h, resOrder, Subgroup.map_top_of_surjective _ lv_red_surjective, Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units]`.
-/
theorem levelGroup_eq_top {N : ℕ} (hN : ¬ l ∣ N) (H : Subgroup (ZMod N)ˣ) :
    levelGroup l N H = ⊤ ∧ resOrder l (levelGroup l N H) = l - 1 := by
  have h : levelGroup l N H = ⊤ := by
    rw [eq_top_iff]
    intro u _
    apply lv_princ_le N H
    rw [mem_princ, Nat.factorization_eq_zero_of_not_dvd hN, pow_zero]
    exact one_dvd _
  refine ⟨h, ?_⟩
  rw [h, resOrder, Subgroup.map_top_of_surjective _ lv_red_surjective, Subgroup.card_top,
    Nat.card_eq_fintype_card, ZMod.card_units]

end KStar.TotallyRealRoots
