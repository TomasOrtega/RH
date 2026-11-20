import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

abbrev redMap (ι : K → Type*) (p : ℕ) : MRing ι →+* MRingOver (ZMod p) ι :=
  MvPolynomial.map (Int.castRingHom (ZMod p))

/- English proof (translation)
Conclude with `MvPolynomial.map_surjective _ ZMod.intCast_surjective`.
-/
theorem redMap_surjective (p : ℕ) : Function.Surjective (redMap ι p) := by
  exact MvPolynomial.map_surjective _ ZMod.intCast_surjective

/- English proof (translation)
Establish `hc : charOf W = (Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))).natAbs` using `rfl`. Rewrite using `[hc]`. Use `set g := Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) with hgdef`. Establish `hg : C g ∈ W` using `Ideal.mem_comap.mp (Submodule.IsPrincipal.generator_mem _)`. Establish `h : C (g.natAbs : ℤ) ∈ W`.

Break down `Int.natAbs_eq g with h | h` into its components or cases. Rewrite using `[← h]`. Conclude with `hg`. Establish `e : (g.natAbs : ℤ) = -g` using `by linarith`. Rewrite using `[e, map_neg]`.

Conclude with `W.neg_mem hg`. Rewrite using `[← map_natCast (C : ℤ →+* MRing ι) g.natAbs]`. Conclude with `h`.
-/
theorem natCast_charOf_mem (W : Ideal (MRing ι)) : ((charOf W : ℕ) : MRing ι) ∈ W := by
  have hc : charOf W = (Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))).natAbs := rfl
  rw [hc]
  set g := Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) with hgdef
  have hg : C g ∈ W := Ideal.mem_comap.mp (Submodule.IsPrincipal.generator_mem _)
  have h : C (g.natAbs : ℤ) ∈ W := by
    rcases Int.natAbs_eq g with h | h
    · rw [← h]; exact hg
    · have e : (g.natAbs : ℤ) = -g := by linarith
      rw [e, map_neg]; exact W.neg_mem hg
  rw [← map_natCast (C : ℤ →+* MRing ι) g.natAbs]
  exact h

/- English proof (translation)
Rewrite using `[redMap, MvPolynomial.ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]`. Simplify using `using hp`.
-/
theorem ker_redMap_le {p : ℕ} {W : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ W) :
    RingHom.ker (redMap ι p) ≤ W := by
  rw [redMap, MvPolynomial.ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton,
    Ideal.span_le, Set.singleton_subset_iff]
  simpa using hp

/- English proof (translation)
Rewrite using `[Ideal.comap_map_of_surjective _ (redMap_surjective p), ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr (ker_redMap_le hp)]`.
-/
theorem comap_map_redMap {p : ℕ} {W : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ W) :
    (W.map (redMap ι p)).comap (redMap ι p) = W := by
  rw [Ideal.comap_map_of_surjective _ (redMap_surjective p), ← RingHom.ker_eq_comap_bot,
    sup_eq_left.mpr (ker_redMap_le hp)]

/- English proof (translation)
Introduce `m hm k`. Use `h m ?_ k` and prove the remaining obligations. Rewrite `hm`, the goal using `[MvPolynomial.mem_support_iff]`. Introduce `h0`. Apply `hm` to reduce the goal to its premises.

Simplify using `[redMap, MvPolynomial.coeff_map, h0]`.
-/
theorem isMultiHomog_redMap {p : ℕ} {s : MRing ι} {a : K → ℕ} (h : IsMultiHomog s a) :
    IsMultiHomog (redMap ι p s) a := by
  intro m hm k
  refine h m ?_ k
  rw [MvPolynomial.mem_support_iff] at hm ⊢
  intro h0
  apply hm
  simp [redMap, MvPolynomial.coeff_map, h0]

/- English proof (translation)
Take `⟨S, hS, rfl⟩` from `h`. Use `⟨redMap ι p '' S, ?_, Ideal.map_span _ _⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Take `⟨a, ha⟩` from `hS f hf`. Conclude with `⟨a, isMultiHomog_redMap ha⟩`.
-/
theorem isMultiHomogIdeal_map_redMap {p : ℕ} {W : Ideal (MRing ι)} (h : IsMultiHomogIdeal W) :
    IsMultiHomogIdeal (W.map (redMap ι p)) := by
  obtain ⟨S, hS, rfl⟩ := h
  refine ⟨redMap ι p '' S, ?_, Ideal.map_span _ _⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨a, isMultiHomog_redMap ha⟩

/- English proof (translation)
Introduce `k`. Take `⟨i, hi⟩` from `h k`. Use `⟨i, fun hx => hi ?_⟩` and prove the remaining obligations. Rewrite using `[← comap_map_redMap hp, Ideal.mem_comap]`. Simplify `hx` using `[redMap]`.
-/
theorem isRelevant_map_redMap {p : ℕ} {W : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ W)
    (h : IsRelevant W) : IsRelevant (W.map (redMap ι p)) := by
  intro k
  obtain ⟨i, hi⟩ := h k
  refine ⟨i, fun hx => hi ?_⟩
  rw [← comap_map_redMap hp, Ideal.mem_comap]
  simpa [redMap] using hx

def quotRedEquiv {p : ℕ} {W : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ W) :
    (MRing ι ⧸ W) ≃+* (MRingOver (ZMod p) ι ⧸ W.map (redMap ι p)) :=
  (Ideal.quotEquivOfEq (by
      rw [← RingHom.comap_ker, Ideal.mk_ker, comap_map_redMap hp])).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := (Ideal.Quotient.mk (W.map (redMap ι p))).comp (redMap ι p))
      (Ideal.Quotient.mk_surjective.comp (redMap_surjective p)))

/- English proof (translation)
Take `⟨hWp, hWh, hWr⟩` from `hW`. Use `⟨⟨?_, isMultiHomogIdeal_map_redMap hWh, isRelevant_map_redMap hp hWr⟩, ?_⟩` and prove the remaining obligations. Conclude with `Ideal.map_isPrime_of_surjective (redMap_surjective p) (ker_redMap_le hp)`. Rewrite using `[← ringKrullDim_eq_of_ringEquiv (quotRedEquiv hp)]`. Conclude with `hdim`.
-/
theorem isProjVarF_map_redMap {p : ℕ} [Fact p.Prime] {W : Ideal (MRing ι)} {n : ℕ}
    (hp : ((p : ℕ) : MRing ι) ∈ W) (hW : IsMultiProjPrime W)
    (hdim : ringKrullDim (MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (W.map (redMap ι p)) n := by
  obtain ⟨hWp, hWh, hWr⟩ := hW
  refine ⟨⟨?_, isMultiHomogIdeal_map_redMap hWh, isRelevant_map_redMap hp hWr⟩, ?_⟩
  · exact Ideal.map_isPrime_of_surjective (redMap_surjective p) (ker_redMap_le hp)
  · rw [← ringKrullDim_eq_of_ringEquiv (quotRedEquiv hp)]
    exact hdim

/- English proof (translation)
Introduce `K _ ι _ P n A s W hP hs hW hv`. Take `⟨hmp, hp, hdim⟩` from `(divSuppArith K ι P n A s W hP hs hW).2 hv`. Use `⟨hp, natCast_charOf_mem W, hmp, ?_⟩` and prove the remaining obligations. Use `haveI : Fact (charOf W).Prime := ⟨hp⟩`. Conclude with `isProjVarF_map_redMap (natCast_charOf_mem W) hmp hdim`.
-/
theorem fibreComp : ReciprocityTheory.ChartRestriction.G.AI.I2.FibreCompStatement := by
  intro K _ ι _ P n A s W hP hs hW hv
  obtain ⟨hmp, hp, hdim⟩ := (divSuppArith K ι P n A s W hP hs hW).2 hv
  refine ⟨hp, natCast_charOf_mem W, hmp, ?_⟩
  haveI : Fact (charOf W).Prime := ⟨hp⟩
  exact isProjVarF_map_redMap (natCast_charOf_mem W) hmp hdim

end GlobalTheory.CompanionTheory.Ar.Pub
