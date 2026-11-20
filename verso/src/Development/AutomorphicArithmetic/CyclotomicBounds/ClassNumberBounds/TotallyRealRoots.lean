import Mathlib

namespace KStar

section Def

variable {R : Type*} [CommRing R]

noncomputable def nuStar (p : R) (U : Set R) (tr : ℕ) : ℕ∞ :=
  sInf ((fun u => emultiplicity p (u ^ tr - 1)) '' U)

/- English proof (translation)
Unfold `nuStar`. Rewrite using `[le_sInf_iff, Set.forall_mem_image]`. Conclude with `forall₂_congr fun u _ => pow_dvd_iff_le_emultiplicity.symm`.
-/
theorem le_nuStar_iff (p : R) (U : Set R) (tr n : ℕ) :
    (n : ℕ∞) ≤ nuStar p U tr ↔ ∀ u ∈ U, p ^ n ∣ u ^ tr - 1 := by
  unfold nuStar
  rw [le_sInf_iff, Set.forall_mem_image]
  exact forall₂_congr fun u _ => pow_dvd_iff_le_emultiplicity.symm

/- English proof (translation)
Establish `h` using `csInf_mem (hU.image (fun u => emultiplicity p (u ^ tr - 1)))`. Take `⟨u, hu, e⟩` from `h`. Conclude with `⟨u, hu, e⟩`.
-/
theorem exists_eq_nuStar {p : R} {U : Set R} (hU : U.Nonempty) (tr : ℕ) :
    ∃ u ∈ U, emultiplicity p (u ^ tr - 1) = nuStar p U tr := by
  have h := csInf_mem (hU.image (fun u => emultiplicity p (u ^ tr - 1)))
  obtain ⟨u, hu, e⟩ := h
  exact ⟨u, hu, e⟩

/- English proof (translation)
Break down `U.eq_empty_or_nonempty with hU | hU` into its components or cases. Substitute `hU` using the available equality. Simplify using `[nuStar] at h`. Take `⟨u, hu, e⟩` from `exists_eq_nuStar hU tr`. Rewrite `e` using `[h]`.

Use `⟨u, hu, pow_dvd_iff_le_emultiplicity.mpr e.ge, fun hd => ?_⟩` and prove the remaining obligations. Use `pow_dvd_iff_le_emultiplicity.mp hd` as an intermediate fact. Rewrite `this` using `[e]`. Normalize the coercions in `at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_exact_of_nuStar_eq {p : R} {U : Set R} {tr ν : ℕ} (h : nuStar p U tr = ν) :
    ∃ u ∈ U, p ^ ν ∣ u ^ tr - 1 ∧ ¬ p ^ (ν + 1) ∣ u ^ tr - 1 := by
  rcases U.eq_empty_or_nonempty with hU | hU
  · subst hU
    simp [nuStar] at h
  obtain ⟨u, hu, e⟩ := exists_eq_nuStar hU tr
  rw [h] at e
  refine ⟨u, hu, pow_dvd_iff_le_emultiplicity.mpr e.ge, fun hd => ?_⟩
  have := pow_dvd_iff_le_emultiplicity.mp hd
  rw [e] at this
  norm_cast at this
  omega

noncomputable def nuStarNat (p : R) (U : Set R) (tr : ℕ)
    [DecidablePred fun n : ℕ => ∃ u ∈ U, ¬ p ^ (n + 1) ∣ u ^ tr - 1]
    (h : ∃ n : ℕ, ∃ u ∈ U, ¬ p ^ (n + 1) ∣ u ^ tr - 1) : ℕ :=
  Nat.find h

/- English proof (translation)
Use `le_antisymm ?_ ?_` and prove the remaining obligations. Use `ENat.forall_natCast_le_iff_le.mp fun n hn => ?_` and prove the remaining obligations. Conclude with `(le_nuStar_iff p U tr n).mpr ((hm n).mp hn)`. Use `ENat.forall_natCast_le_iff_le.mp fun n hn => ?_` and prove the remaining obligations. Conclude with `(hm n).mpr ((le_nuStar_iff p U tr n).mp hn)`.
-/
theorem eq_nuStar_of_forall {p : R} {U : Set R} {tr : ℕ} (m : ℕ∞)
    (hm : ∀ n : ℕ, (n : ℕ∞) ≤ m ↔ ∀ u ∈ U, p ^ n ∣ u ^ tr - 1) : m = nuStar p U tr := by
  refine le_antisymm ?_ ?_
  · refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
    exact (le_nuStar_iff p U tr n).mpr ((hm n).mp hn)
  · refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
    exact (hm n).mpr ((le_nuStar_iff p U tr n).mp hn)

end Def

section Domain

variable {R : Type*} [CommRing R] [IsDomain R]

/- English proof (translation)
Establish `hx : ¬ p ∣ u`. Introduce `h`. Establish `: p ∣ u - (u - 1)` using `dvd_sub h hu`. Rewrite `this` using `[sub_sub_cancel]`. Conclude with `hp.not_isUnit (isUnit_of_dvd_one this)`.

Use `emultiplicity_pow_sub_pow_of_prime hp (y := 1) (by simpa using hu) hx hn` as an intermediate fact. Simplify using `using this`.
-/
theorem emultiplicity_pow_sub_one_of_not_dvd {p u : R} (hp : Prime p) (hu : p ∣ u - 1)
    {n : ℕ} (hn : ¬ p ∣ (n : R)) : emultiplicity p (u ^ n - 1) = emultiplicity p (u - 1) := by
  have hx : ¬ p ∣ u := by
    intro h
    have : p ∣ u - (u - 1) := dvd_sub h hu
    rw [sub_sub_cancel] at this
    exact hp.not_isUnit (isUnit_of_dvd_one this)
  have := emultiplicity_pow_sub_pow_of_prime hp (y := 1) (by simpa using hu) hx hn
  simpa using this

/- English proof (translation)
Unfold `nuStar`. Use `congr 1`. Use `Set.image_congr fun u hu => ?_` and prove the remaining obligations. Rewrite using `[pow_one]`. Conclude with `emultiplicity_pow_sub_one_of_not_dvd hp (hU u hu) htr`.
-/
theorem nuStar_eq_nuStar_one {p : R} (hp : Prime p) {U : Set R} (hU : ∀ u ∈ U, p ∣ u - 1)
    {tr : ℕ} (htr : ¬ p ∣ (tr : R)) : nuStar p U tr = nuStar p U 1 := by
  unfold nuStar
  congr 1
  refine Set.image_congr fun u hu => ?_
  rw [pow_one]
  exact emultiplicity_pow_sub_one_of_not_dvd hp (hU u hu) htr

end Domain

section Int

end Int

section Inhabitant

/- English proof (translation)
Use `(eq_nuStar_of_forall 1 fun n => ?_).symm` and prove the remaining obligations. Simplify using `only [Set.mem_singleton_iff, forall_eq, pow_one]`. Evaluate the numerical expressions. Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `intro hn interval_cases n <;> norm_num`.

Introduce `h`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Establish `: (2 : ℤ) ^ 2 ∣ 2` using `(pow_dvd_pow 2 (by omega : 2 ≤ n)).trans h`. Evaluate the numerical expressions using `at this`.
-/
example : nuStar (2 : ℤ) {3} 1 = 1 := by
  refine (eq_nuStar_of_forall 1 fun n => ?_).symm
  simp only [Set.mem_singleton_iff, forall_eq, pow_one]
  norm_num
  constructor
  · intro hn
    interval_cases n <;> norm_num
  · intro h
    by_contra hc
    push Not at hc
    have : (2 : ℤ) ^ 2 ∣ 2 := (pow_dvd_pow 2 (by omega : 2 ≤ n)).trans h
    norm_num at this

end Inhabitant

end KStar
