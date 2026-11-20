import Mathlib

namespace Formalism.BasicNotions.Examples₂.NZ

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {V : Type*} [AddCommGroup V] [Module R V]

def glue (A : HeightOneSpectrum R → Submodule R V) : Submodule R V := ⨅ w, A w

/- English proof (translation)
Introduce `h`. Take `⟨v, hv, hle⟩` from `(w.isPrime.prod_le).mp h`. Establish `h2 : v.asIdeal ≤ w.asIdeal` using `w.isPrime.le_of_pow_le hle`. Establish `h3 : v.asIdeal = w.asIdeal` using `(v.isMaximal).eq_of_le w.isPrime.ne_top h2`. Conclude with `hw (HeightOneSpectrum.ext h3 ▸ hv)`.
-/
theorem not_le_of_prod {S : Finset (HeightOneSpectrum R)} (m : HeightOneSpectrum R → ℕ) (w : HeightOneSpectrum R)
    (hw : w ∉ S) : ¬ (∏ v ∈ S, v.asIdeal ^ m v) ≤ w.asIdeal := by
  intro h
  obtain ⟨v, hv, hle⟩ := (w.isPrime.prod_le).mp h
  have h2 : v.asIdeal ≤ w.asIdeal := w.isPrime.le_of_pow_le hle
  have h3 : v.asIdeal = w.asIdeal := (v.isMaximal).eq_of_le w.isPrime.ne_top h2
  exact hw (HeightOneSpectrum.ext h3 ▸ hv)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, hx⟩`. Conclude with `hsat w s hs x ((Submodule.mem_iInf _).mp hx w)`. Introduce `hx classical choose m hm using fun v => habs v x`. Establish `hw : w ∉ (hfin x).toFinset` using `by simpa using hx`.

Take `⟨s, hsI, hsw⟩` from `SetLike.not_le_iff_exists.mp (not_le_of_prod m w hw)`. Use `⟨s, hsw, (Submodule.mem_iInf _).mpr fun v => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hv : x ∈ A v`. Conclude with `(A v).smul_mem s hv`. Conclude with `hm v s (Ideal.prod_le_inf.trans (Finset.inf_le ((hfin x).mem_toFinset.mpr hv)) hsI)`.
-/
theorem glue_loc (A : HeightOneSpectrum R → Submodule R V)
    (hsat : ∀ w (s : R), s ∉ w.asIdeal → ∀ x, s • x ∈ A w → x ∈ A w)
    (hfin : ∀ x : V, {w | x ∉ A w}.Finite)
    (habs : ∀ w (x : V), ∃ m : ℕ, ∀ a ∈ w.asIdeal ^ m, a • x ∈ A w)
    (w : HeightOneSpectrum R) (x : V) :
    (∃ s : R, s ∉ w.asIdeal ∧ s • x ∈ glue A) ↔ x ∈ A w := by
  constructor
  · rintro ⟨s, hs, hx⟩
    exact hsat w s hs x ((Submodule.mem_iInf _).mp hx w)
  · intro hx
    classical
    choose m hm using fun v => habs v x
    have hw : w ∉ (hfin x).toFinset := by simpa using hx
    obtain ⟨s, hsI, hsw⟩ := SetLike.not_le_iff_exists.mp (not_le_of_prod m w hw)
    refine ⟨s, hsw, (Submodule.mem_iInf _).mpr fun v => ?_⟩
    by_cases hv : x ∈ A v
    · exact (A v).smul_mem s hv
    · exact hm v s (Ideal.prod_le_inf.trans (Finset.inf_le ((hfin x).mem_toFinset.mpr hv)) hsI)

end Formalism.BasicNotions.Examples₂.NZ
