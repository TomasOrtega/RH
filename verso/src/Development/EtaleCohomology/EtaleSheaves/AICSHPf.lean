import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi

noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.E.AICSHPf

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `f hd hm hv`. Establish `: f = 1` using `Polynomial.eq_one_of_monic_natDegree_zero hm hd`.

Substitute `this` using the available equality. Simplify using `only [eval_one] at hv`. Conclude with `absurd ((Ideal.eq_top_iff_one P).2 hv) (Ideal.IsPrime.ne_top inferInstance)`. Consider the case `succ n ih`. Introduce `f hd hm hv`.

Take `⟨r, hr⟩` from `hA f hm (by omega)`. Establish `hroot : f.IsRoot r` using `hr`. Use `set q := f /ₘ (X - C r) with hq`. Establish `hfac : (X - C r) * q = f` using `(Polynomial.mul_divByMonic_eq_iff_isRoot).2 hroot`. Establish `hqm : q.Monic` using `Polynomial.Monic.of_mul_monic_left (monic_X_sub_C r) (by rw [hfac]; exact hm)`.

Establish `hdeg : q.natDegree = n`. Use `(monic_X_sub_C r).natDegree_mul hqm` as an intermediate fact. Rewrite `this` using `[hfac, natDegree_X_sub_C]`. Use linear arithmetic over natural numbers and integers. Establish `hv' : (a₀ - r) * q.eval a₀ ∈ P`.

Rewrite `hv` using `[← hfac]`. Simplify `hv` using `[eval_mul]`. Break down `(inferInstance : P.IsPrime).mem_or_mem hv' with h | h` into its components or cases. Use `⟨r, hroot, ?_⟩` and prove the remaining obligations. Use `P.neg_mem_iff.2 h` as an intermediate fact.

Simplify using `using this`. Take `⟨a, ha, ha'⟩` from `ih q hdeg hqm h`. Use `⟨a, ?_, ha'⟩` and prove the remaining obligations. Rewrite using `[← hfac]`. Simplify using `[IsRoot, eval_mul, ha.eq_zero]`.
-/
theorem root_near {T : Type} [CommRing T] [IsDomain T] (hA : ∀ p : Polynomial T, p.Monic → 0 < p.natDegree → ∃ a, p.eval a = 0)
    (P : Ideal T) [P.IsPrime] (a₀ : T) :
    ∀ (n : ℕ) (f : T[X]), f.natDegree = n → f.Monic → f.eval a₀ ∈ P → ∃ a, f.IsRoot a ∧ a - a₀ ∈ P := by
  intro n
  induction n with
  | zero =>
    intro f hd hm hv
    have : f = 1 := Polynomial.eq_one_of_monic_natDegree_zero hm hd
    subst this
    simp only [eval_one] at hv
    exact absurd ((Ideal.eq_top_iff_one P).2 hv) (Ideal.IsPrime.ne_top inferInstance)
  | succ n ih =>
    intro f hd hm hv
    obtain ⟨r, hr⟩ := hA f hm (by omega)
    have hroot : f.IsRoot r := hr
    set q := f /ₘ (X - C r) with hq
    have hfac : (X - C r) * q = f := (Polynomial.mul_divByMonic_eq_iff_isRoot).2 hroot
    have hqm : q.Monic := Polynomial.Monic.of_mul_monic_left (monic_X_sub_C r) (by rw [hfac]; exact hm)
    have hdeg : q.natDegree = n := by
      have := (monic_X_sub_C r).natDegree_mul hqm
      rw [hfac, natDegree_X_sub_C] at this; omega
    have hv' : (a₀ - r) * q.eval a₀ ∈ P := by
      rw [← hfac] at hv; simpa [eval_mul] using hv
    rcases (inferInstance : P.IsPrime).mem_or_mem hv' with h | h
    · refine ⟨r, hroot, ?_⟩
      have := P.neg_mem_iff.2 h; simpa using this
    · obtain ⟨a, ha, ha'⟩ := ih q hdeg hqm h
      refine ⟨a, ?_, ha'⟩
      rw [← hfac]; simp [IsRoot, eval_mul, ha.eq_zero]

/- English proof (translation)
The claim follows from `root_near hA (IsLocalRing.maximalIdeal T) a₀ _ f rfl hf h₀`.
-/
theorem henselian {T : Type} [CommRing T] [IsDomain T] [IsLocalRing T] (hA : AIC T) : HenselianLocalRing T where
  is_henselian f hf a₀ h₀ _ := root_near hA (IsLocalRing.maximalIdeal T) a₀ _ f rfl hf h₀

/- English proof (translation)
Use `IsAlgClosed.of_exists_root _ ?_` and prove the remaining obligations. Introduce `p hpm hirr`. Take `⟨P, hPl, hPd, hPm⟩` from `Polynomial.lifts_and_degree_eq_and_monic (Polynomial.lifts_iff_coeff_lifts p |>.2 fun n => IsLocalRing.residue_surjective _) hpm`. Establish `hpos : 0 < P.natDegree`. Rewrite using `[Polynomial.natDegree_eq_of_degree_eq hPd]`.

Conclude with `Irreducible.natDegree_pos hirr`. Take `⟨a, ha⟩` from `hA P hPm hpos`. Use `⟨IsLocalRing.residue T a, ?_⟩` and prove the remaining obligations. Rewrite using `[← hPl, Polynomial.eval_map, Polynomial.eval₂_at_apply, ha, map_zero]`.
-/
theorem algClosed {T : Type} [CommRing T] [IsDomain T] [IsLocalRing T] (hA : AIC T) :
    IsAlgClosed (IsLocalRing.ResidueField T) := by
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hpm hirr
  obtain ⟨P, hPl, hPd, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.lifts_iff_coeff_lifts p |>.2 fun n => IsLocalRing.residue_surjective _) hpm
  have hpos : 0 < P.natDegree := by
    rw [Polynomial.natDegree_eq_of_degree_eq hPd]; exact Irreducible.natDegree_pos hirr
  obtain ⟨a, ha⟩ := hA P hPm hpos
  refine ⟨IsLocalRing.residue T a, ?_⟩
  rw [← hPl, Polynomial.eval_map, Polynomial.eval₂_at_apply, ha, map_zero]

end LateralTheory.E.AICSHPf

namespace LateralTheory.E.t_E3Cut

/- English proof (translation)
Introduce `T _ _ _ hA`. Set `_` to `LateralTheory.E.AICSHPf.henselian hA`. Use `LateralTheory.E.AICSHPf.algClosed hA` as an intermediate fact. Conclude with `⟨inferInstance, inferInstance⟩`.
-/
theorem AICSH_of : AICSH := by
  intro T _ _ _ hA
  let _ := LateralTheory.E.AICSHPf.henselian hA
  have := LateralTheory.E.AICSHPf.algClosed hA
  exact ⟨inferInstance, inferInstance⟩

end LateralTheory.E.t_E3Cut
