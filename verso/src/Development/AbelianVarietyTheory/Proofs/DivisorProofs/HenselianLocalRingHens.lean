import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HensIsLocalRingAndIsLocalHomOfStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingToHenselisationInjectiveOfNbhdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeIsRootOfSimpleRootPointedEtaleNbhdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointedEtaleNeighbourhoodLocalRingIsDirectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingToHenselisationAlgebraMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubMemMaximalIdealPointedEtaleNeighbourhooStatement

open IsLocalRing GlobalTheory.Henselisation Polynomial

namespace GlobalTheory.Henselisation

/- English proof (translation)
Establish `h1 : (derivative (p.scaleRoots s)).natDegree < p.natDegree + 1`. Use `natDegree_derivative_le (p.scaleRoots s)` as an intermediate fact. Rewrite `this` using `[natDegree_scaleRoots]`. Use linear arithmetic over natural numbers and integers. Establish `h2 : (derivative p).natDegree < p.natDegree + 1`.

Use `natDegree_derivative_le p` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[eval_eq_sum_range' h1, eval_eq_sum_range' h2, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_derivative, coeff_derivative, coeff_scaleRoots]`.

Distinguish the cases in `hkd : k + 1 ≤ p.natDegree`. Establish `e : s ^ (p.natDegree - (k + 1)) * (s * x) ^ k = s ^ (p.natDegree - 1) * x ^ k`. Rewrite using `[mul_pow, ← mul_assoc, ← pow_add]`. Use `congr 2`. Use linear arithmetic over natural numbers and integers.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[coeff_eq_zero_of_natDegree_lt (by omega)]; ring`.
-/
theorem eval_derivative_scaleRoots_mul {S : Type*} [CommRing S] (p : S[X]) (s x : S) :
    (derivative (p.scaleRoots s)).eval (s * x) = s ^ (p.natDegree - 1) * (derivative p).eval x := by
  have h1 : (derivative (p.scaleRoots s)).natDegree < p.natDegree + 1 := by
    have := natDegree_derivative_le (p.scaleRoots s)
    rw [natDegree_scaleRoots] at this; omega
  have h2 : (derivative p).natDegree < p.natDegree + 1 := by
    have := natDegree_derivative_le p; omega
  rw [eval_eq_sum_range' h1, eval_eq_sum_range' h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_derivative, coeff_derivative, coeff_scaleRoots]
  by_cases hkd : k + 1 ≤ p.natDegree
  · have e : s ^ (p.natDegree - (k + 1)) * (s * x) ^ k = s ^ (p.natDegree - 1) * x ^ k := by
      rw [mul_pow, ← mul_assoc, ← pow_add]; congr 2; omega
    calc _ = p.coeff (k + 1) * (↑k + 1) * (s ^ (p.natDegree - (k + 1)) * (s * x) ^ k) := by ring
      _ = _ := by rw [e]; ring
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; ring

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Establish `hx' : x ∈ maximalIdeal S` using `(mem_maximalIdeal x).2 hx`. Establish `: u ∈ maximalIdeal S`. Use `Ideal.sub_mem _ hx' h` as an intermediate fact. Simplify using `using this`.

Conclude with `(mem_maximalIdeal u).1 this hu`.
-/
theorem isUnit_of_sub_mem_maximalIdeal {S : Type*} [CommRing S] [IsLocalRing S] {x u : S}
    (hu : IsUnit u) (h : x - u ∈ maximalIdeal S) : IsUnit x := by
  by_contra hx
  have hx' : x ∈ maximalIdeal S := (mem_maximalIdeal x).2 hx
  have : u ∈ maximalIdeal S := by
    have := Ideal.sub_mem _ hx' h; simpa using this
  exact (mem_maximalIdeal u).1 this hu

/- English proof (translation)
Introduce `R _ _`. Use `haveI : IsDirected (EtNbhd R) (· ≤ ·) := GlobalTheory.T.pointedEtaleNeighbourhoodLocalRing_isDirected R`. Take `⟨hloc, hofloc⟩` from `GlobalTheory.T.isLocalRing_hens_and_isLocalHom_of R`. Use `letI := hloc`. Use `{ toIsLocalRing := hloc, is_henselian := ?_ }` and prove the remaining obligations.

Introduce `f hf a₀ hfa₀ hf'a₀`. Take `⟨i', b₀, hb₀⟩ : ∃ (i : EtNbhd R) (b : i.B), Hens.of i b = a₀` from `Ring.DirectLimit.exists_of a₀`. Take `⟨r, hr⟩` from `GlobalTheory.T.exists_sub_mem_maximalIdeal_pointedEtaleNeighbourhood R i' b₀`. Use `set ρ := algebraMap R (Hens R) r with hρdef`. Establish `hρ : a₀ - ρ ∈ maximalIdeal (Hens R)` using `by haveI := hofloc i'`.

Rewrite using `[← hb₀, hρdef, ← GlobalTheory.T.etaleNbhdLocalRingToHenselisation_algebraMap R i' r, ← map_sub]`. Conclude with `map_nonunit _ _ hr`. Establish `hfρ : f.eval ρ ∈ maximalIdeal (Hens R)`. Establish `hd` using `sub_dvd_eval_sub ρ a₀ f`. Establish `: f.eval ρ - f.eval a₀ ∈ maximalIdeal (Hens R)`.

Take `⟨c, hc⟩` from `hd`. Rewrite using `[hc]`. Apply `Ideal.mul_mem_right` to reduce the goal to its premises. Use `(Ideal.neg_mem_iff _).2 hρ` as an intermediate fact. Simplify using `using this`.

Simplify using `using Ideal.add_mem _ this hfa₀`. Establish `hf'ρ : IsUnit (f.derivative.eval ρ)`. Use `isUnit_of_sub_mem_maximalIdeal hf'a₀ ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `sub_dvd_eval_sub ρ a₀ (derivative f)`. Rewrite using `[hc]`.

Apply `Ideal.mul_mem_right` to reduce the goal to its premises. Use `(Ideal.neg_mem_iff _).2 hρ` as an intermediate fact. Simplify using `using this`. Take `⟨i, g, hg⟩ : ∃ (i : EtNbhd R) (g : Polynomial i.B), g.map (Hens.of i) = f` from `Ring.DirectLimit.Polynomial.exists_of (f' := fun _ _ h => EtNbhd.trans h) f`. Use `haveI := hofloc i`.

Establish `hgm : g.Monic` using `monic_of_injective (GlobalTheory.T.etaleNbhdLocalRingToHenselisation_injective_of_nbhd R i) (hg ▸ hf)`. Set `M` to `i.q.primeCompl`. Set `ψ : i.A →+* i.B` to `algebraMap i.A i.B`. Set `s : M` to `IsLocalization.commonDenom M g.support g.coeff`. Establish `hl` using `IsLocalization.scaleRoots_commonDenom_mem_lifts M g (by rw [hgm.leadingCoeff]; exact ⟨1, map_one _⟩)`.

Take `⟨h, hhmap, -, hhm⟩` from `lifts_and_natDegree_eq_and_monic hl ((monic_scaleRoots_iff _).2 hgm)`. Set `Φ : i.A →+* Hens R` to `(Hens.of i).comp ψ`. Set `u : Hens R` to `Φ s`. Establish `hu : IsUnit u` using `(IsLocalization.map_units i.B s).map (Hens.of i)`. Establish `hΦr : Φ (algebraMap R i.A r) = ρ`.

Simplify using `only [Φ, ψ, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]`. Conclude with `GlobalTheory.T.etaleNbhdLocalRingToHenselisation_algebraMap R i r`. Set `a₀' : i.A` to `(s : i.A) * algebraMap R i.A r`. Establish `hΦa₀' : Φ a₀' = u * ρ` using `by simp only [a₀', map_mul, hΦr]; rfl`. Establish `hhΦ : h.map Φ = f.scaleRoots u`.

Rewrite using `[show Φ = (Hens.of i).comp ψ from rfl, ← Polynomial.map_map, hhmap, map_scaleRoots _ _ _ (by rw [hgm.leadingCoeff, map_one]; exact one_ne_zero), hg]`. Both sides reduce to the same expression. Establish `key1 : Φ (h.eval a₀') = u ^ f.natDegree * f.eval ρ`. Rewrite using `[← eval₂_at_apply, ← eval_map, hhΦ, hΦa₀']`. Conclude with `scaleRoots_eval₂_mul (RingHom.id _) ρ u`.

Establish `key2 : Φ (h.derivative.eval a₀') = u ^ (f.natDegree - 1) * f.derivative.eval ρ`. Rewrite using `[← eval₂_at_apply, ← eval_map, ← derivative_map, hhΦ, hΦa₀']`. Conclude with `eval_derivative_scaleRoots_mul f u ρ`. Establish `hpt1 : i.pt (h.eval a₀') = 0`. Establish `hm : ψ (h.eval a₀') ∈ maximalIdeal i.B`.

Introduce `hun`. Establish `: Φ (h.eval a₀') ∈ maximalIdeal (Hens R)`. Rewrite using `[key1]`. Conclude with `Ideal.mul_mem_left _ _ hfρ`. Conclude with `(mem_maximalIdeal _).1 this (hun.map (Hens.of i))`.

Use `(IsLocalization.AtPrime.to_map_mem_maximal_iff i.B i.q _).1 hm` as an intermediate fact. Conclude with `(RingHom.mem_ker).1 this`. Establish `hpt2 : i.pt (h.derivative.eval a₀') ≠ 0`. Introduce `h0`. Establish `hq : h.derivative.eval a₀' ∈ i.q` using `RingHom.mem_ker.2 h0`.

Establish `hm` using `(IsLocalization.AtPrime.to_map_mem_maximal_iff i.B i.q _).2 hq`. Establish `hΦm : Φ (h.derivative.eval a₀') ∈ maximalIdeal (Hens R)` using `map_nonunit (Hens.of i) _ hm`. Rewrite `hΦm` using `[key2]`. Conclude with `(mem_maximalIdeal _).1 hΦm ((hu.pow _).mul hf'ρ)`. Take `⟨j, hij, c, hc, hcm⟩` from `GlobalTheory.T.exists_le_isRoot_of_simpleRoot_pointedEtaleNbhd R i h a₀' hhm hpt1 hpt2`.

Use `haveI := hofloc j`. Establish `hofj : (Hens.of j).comp (EtNbhd.trans hij) = Hens.of i` using `RingHom.ext fun x => Ring.DirectLimit.of_f hij x`. Establish `hΦj : (Hens.of j).comp ((EtNbhd.trans hij).comp ψ) = Φ`. Rewrite using `[← RingHom.comp_assoc, hofj]`. Use `set c' := Hens.of j c`.

Establish `hroot : (f.scaleRoots u).eval c' = 0`. Rewrite using `[← hhΦ, ← hΦj, ← Polynomial.map_map, eval_map, eval₂_at_apply, hc.eq_zero, map_zero]`. Establish `hcm' : c' - u * ρ ∈ maximalIdeal (Hens R)`. Use `map_nonunit (Hens.of j) _ hcm` as an intermediate fact. Rewrite `this` using `[map_sub, ← RingHom.comp_apply (Hens.of j) (EtNbhd.trans hij), ← RingHom.comp_apply ((Hens.of j).comp (EtNbhd.trans hij)) ψ, hofj, show (Hens.of i).comp ψ = Φ from rfl, hΦa₀']`. Then use the resulting hypothesis.

Use `⟨↑hu.unit⁻¹ * c', ?_, ?_⟩` and prove the remaining obligations. Establish `hc' : c' = u * (↑hu.unit⁻¹ * c')`. Rewrite using `[← mul_assoc, hu.mul_val_inv, one_mul]`. Establish `e` using `scaleRoots_eval₂_mul (p := f) (RingHom.id _) (↑hu.unit⁻¹ * c') u`. Simplify using `only [RingHom.id_apply] at e`.

Express the relevant statement in the definitionally equal form `eval (u * _) _ = u ^ _ * eval _ f at e`. Rewrite `e` using `[← hc', hroot]`. Conclude with `(((hu.pow _).mul_right_eq_zero).1 e.symm)`. Establish `e1 : ↑hu.unit⁻¹ * c' - ρ = ↑hu.unit⁻¹ * (c' - u * ρ)`. Rewrite using `[mul_sub, ← mul_assoc, hu.val_inv_mul, one_mul]`.

Establish `e2 : ↑hu.unit⁻¹ * c' - a₀ = (↑hu.unit⁻¹ * c' - ρ) - (a₀ - ρ)` using `by ring`. Rewrite using `[e2, e1]`. Conclude with `Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hcm') hρ`.
-/
theorem henselianLocalRing_hens : ∀ (R : Type) [CommRing R] [IsLocalRing R],
    HenselianLocalRing (Hens R) := by
  intro R _ _
  haveI : IsDirected (EtNbhd R) (· ≤ ·) := GlobalTheory.T.pointedEtaleNeighbourhoodLocalRing_isDirected R
  obtain ⟨hloc, hofloc⟩ := GlobalTheory.T.isLocalRing_hens_and_isLocalHom_of R
  letI := hloc
  refine { toIsLocalRing := hloc, is_henselian := ?_ }
  intro f hf a₀ hfa₀ hf'a₀

  obtain ⟨i', b₀, hb₀⟩ : ∃ (i : EtNbhd R) (b : i.B), Hens.of i b = a₀ :=
    Ring.DirectLimit.exists_of a₀
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_sub_mem_maximalIdeal_pointedEtaleNeighbourhood R i' b₀
  set ρ := algebraMap R (Hens R) r with hρdef
  have hρ : a₀ - ρ ∈ maximalIdeal (Hens R) := by
    haveI := hofloc i'
    rw [← hb₀, hρdef, ← GlobalTheory.T.etaleNbhdLocalRingToHenselisation_algebraMap R i' r, ← map_sub]; exact map_nonunit _ _ hr
  have hfρ : f.eval ρ ∈ maximalIdeal (Hens R) := by
    have hd := sub_dvd_eval_sub ρ a₀ f
    have : f.eval ρ - f.eval a₀ ∈ maximalIdeal (Hens R) := by
      obtain ⟨c, hc⟩ := hd
      rw [hc]; apply Ideal.mul_mem_right
      have := (Ideal.neg_mem_iff _).2 hρ; simpa using this
    simpa using Ideal.add_mem _ this hfa₀
  have hf'ρ : IsUnit (f.derivative.eval ρ) := by
    refine isUnit_of_sub_mem_maximalIdeal hf'a₀ ?_
    obtain ⟨c, hc⟩ := sub_dvd_eval_sub ρ a₀ (derivative f)
    rw [hc]; apply Ideal.mul_mem_right
    have := (Ideal.neg_mem_iff _).2 hρ; simpa using this

  obtain ⟨i, g, hg⟩ : ∃ (i : EtNbhd R) (g : Polynomial i.B), g.map (Hens.of i) = f :=
    Ring.DirectLimit.Polynomial.exists_of (f' := fun _ _ h => EtNbhd.trans h) f
  haveI := hofloc i
  have hgm : g.Monic := monic_of_injective (GlobalTheory.T.etaleNbhdLocalRingToHenselisation_injective_of_nbhd R i) (hg ▸ hf)
  let M := i.q.primeCompl
  let ψ : i.A →+* i.B := algebraMap i.A i.B
  let s : M := IsLocalization.commonDenom M g.support g.coeff
  have hl := IsLocalization.scaleRoots_commonDenom_mem_lifts M g
    (by rw [hgm.leadingCoeff]; exact ⟨1, map_one _⟩)
  obtain ⟨h, hhmap, -, hhm⟩ := lifts_and_natDegree_eq_and_monic hl
    ((monic_scaleRoots_iff _).2 hgm)
  let Φ : i.A →+* Hens R := (Hens.of i).comp ψ
  let u : Hens R := Φ s
  have hu : IsUnit u := (IsLocalization.map_units i.B s).map (Hens.of i)
  have hΦr : Φ (algebraMap R i.A r) = ρ := by
    simp only [Φ, ψ, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
    exact GlobalTheory.T.etaleNbhdLocalRingToHenselisation_algebraMap R i r
  let a₀' : i.A := (s : i.A) * algebraMap R i.A r
  have hΦa₀' : Φ a₀' = u * ρ := by simp only [a₀', map_mul, hΦr]; rfl
  have hhΦ : h.map Φ = f.scaleRoots u := by
    rw [show Φ = (Hens.of i).comp ψ from rfl, ← Polynomial.map_map, hhmap, map_scaleRoots _ _ _
      (by rw [hgm.leadingCoeff, map_one]; exact one_ne_zero), hg]
    rfl
  have key1 : Φ (h.eval a₀') = u ^ f.natDegree * f.eval ρ := by
    rw [← eval₂_at_apply, ← eval_map, hhΦ, hΦa₀']
    exact scaleRoots_eval₂_mul (RingHom.id _) ρ u
  have key2 : Φ (h.derivative.eval a₀') = u ^ (f.natDegree - 1) * f.derivative.eval ρ := by
    rw [← eval₂_at_apply, ← eval_map, ← derivative_map, hhΦ, hΦa₀']
    exact eval_derivative_scaleRoots_mul f u ρ
  have hpt1 : i.pt (h.eval a₀') = 0 := by
    have hm : ψ (h.eval a₀') ∈ maximalIdeal i.B := by
      intro hun
      have : Φ (h.eval a₀') ∈ maximalIdeal (Hens R) := by
        rw [key1]; exact Ideal.mul_mem_left _ _ hfρ
      exact (mem_maximalIdeal _).1 this (hun.map (Hens.of i))
    have := (IsLocalization.AtPrime.to_map_mem_maximal_iff i.B i.q _).1 hm
    exact (RingHom.mem_ker).1 this
  have hpt2 : i.pt (h.derivative.eval a₀') ≠ 0 := by
    intro h0
    have hq : h.derivative.eval a₀' ∈ i.q := RingHom.mem_ker.2 h0
    have hm := (IsLocalization.AtPrime.to_map_mem_maximal_iff i.B i.q _).2 hq
    have hΦm : Φ (h.derivative.eval a₀') ∈ maximalIdeal (Hens R) := map_nonunit (Hens.of i) _ hm
    rw [key2] at hΦm
    exact (mem_maximalIdeal _).1 hΦm ((hu.pow _).mul hf'ρ)
  obtain ⟨j, hij, c, hc, hcm⟩ := GlobalTheory.T.exists_le_isRoot_of_simpleRoot_pointedEtaleNbhd R i h a₀' hhm hpt1 hpt2
  haveI := hofloc j
  have hofj : (Hens.of j).comp (EtNbhd.trans hij) = Hens.of i :=
    RingHom.ext fun x => Ring.DirectLimit.of_f hij x
  have hΦj : (Hens.of j).comp ((EtNbhd.trans hij).comp ψ) = Φ := by
    rw [← RingHom.comp_assoc, hofj]
  set c' := Hens.of j c
  have hroot : (f.scaleRoots u).eval c' = 0 := by
    rw [← hhΦ, ← hΦj, ← Polynomial.map_map, eval_map, eval₂_at_apply, hc.eq_zero, map_zero]
  have hcm' : c' - u * ρ ∈ maximalIdeal (Hens R) := by
    have := map_nonunit (Hens.of j) _ hcm
    rwa [map_sub, ← RingHom.comp_apply (Hens.of j) (EtNbhd.trans hij),
      ← RingHom.comp_apply ((Hens.of j).comp (EtNbhd.trans hij)) ψ, hofj,
      show (Hens.of i).comp ψ = Φ from rfl, hΦa₀'] at this
  refine ⟨↑hu.unit⁻¹ * c', ?_, ?_⟩
  · have hc' : c' = u * (↑hu.unit⁻¹ * c') := by
      rw [← mul_assoc, hu.mul_val_inv, one_mul]
    have e := scaleRoots_eval₂_mul (p := f) (RingHom.id _) (↑hu.unit⁻¹ * c') u
    simp only [RingHom.id_apply] at e
    change eval (u * _) _ = u ^ _ * eval _ f at e
    rw [← hc', hroot] at e
    exact (((hu.pow _).mul_right_eq_zero).1 e.symm)
  · have e1 : ↑hu.unit⁻¹ * c' - ρ = ↑hu.unit⁻¹ * (c' - u * ρ) := by
      rw [mul_sub, ← mul_assoc, hu.val_inv_mul, one_mul]
    have e2 : ↑hu.unit⁻¹ * c' - a₀ = (↑hu.unit⁻¹ * c' - ρ) - (a₀ - ρ) := by ring
    rw [e2, e1]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hcm') hρ

end GlobalTheory.Henselisation
