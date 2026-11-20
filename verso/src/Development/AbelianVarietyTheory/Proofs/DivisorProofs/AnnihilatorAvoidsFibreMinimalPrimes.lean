import Mathlib
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

/- English proof (translation)
Set `p : PrimeSpectrum A` to `PrimeSpectrum.comap (algebraMap A B) u`. Set `I₀ : Ideal B` to `p.asIdeal.map (algebraMap A B)`. Set `T : Set (Ideal B)` to `{Q | Q ∈ I₀.minimalPrimes ∧ Q.comap (algebraMap A B) = p.asIdeal}`. Establish `hTfin : T.Finite`. Set `e` to `PrimeSpectrum.preimageOrderIsoFiber A B p`.

Use `haveI : IsNoetherianRing (p.asIdeal.Fiber B) := Algebra.FiniteType.isNoetherianRing p.asIdeal.ResidueField _`. Establish `hM : {j : PrimeSpectrum (p.asIdeal.Fiber B) | j.asIdeal ∈ minimalPrimes (p.asIdeal.Fiber B)}.Finite` using `(minimalPrimes.finite_of_isNoetherianRing _).preimage (fun x _ y _ h => PrimeSpectrum.ext h)`. Use `(hM.image fun j => (e.symm j).1.asIdeal).subset ?_` and prove the remaining obligations. Introduce and unpack `Q ⟨hQmin, hQp⟩`. Establish `hQprime : Q.IsPrime` using `hQmin.1.1`.

Set `Q' : PrimeSpectrum B` to `⟨Q, hQprime⟩`. Establish `hQ'mem : Q' ∈ PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}` using `by show PrimeSpectrum.comap (algebraMap A B) Q' = p ext1; exact hQp`. Take `⟨J, hJmin, hJle⟩` from `Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ (e ⟨Q', hQ'mem⟩).asIdeal)`. Establish `hJprime : J.IsPrime` using `hJmin.1.1`. Set `j : PrimeSpectrum (p.asIdeal.Fiber B)` to `⟨J, hJprime⟩`.

Use `⟨j, hJmin, ?_⟩` and prove the remaining obligations. Establish `hle : e.symm j ≤ ⟨Q', hQ'mem⟩`. Rewrite using `[← e.le_iff_le, e.apply_symm_apply]`. Conclude with `hJle`. Establish `hle' : (e.symm j).1.asIdeal ≤ Q` using `hle`.

Establish `hover : (e.symm j).1.asIdeal.comap (algebraMap A B) = p.asIdeal` using `congrArg PrimeSpectrum.asIdeal (e.symm j).2`. Establish `hge : I₀ ≤ (e.symm j).1.asIdeal`. Rewrite using `[Ideal.map_le_iff_le_comap, hover]`. Conclude with `le_antisymm hle' (hQmin.2 ⟨(e.symm j).1.isPrime, hge⟩ hle')`. Take `⟨s, hs⟩` from `hTfin.exists_finset_coe`.

Establish `hsT : ∀ i, i ∈ s ↔ i ∈ T` using `fun i => by rw [← hs]; rfl`. Set `K : Ideal B` to `LinearMap.ker (LinearMap.toSpanSingleton B B b)`. Establish `hK : ∀ x, x ∈ K ↔ x * b = 0` using `fun x => by`. Simplify using `[K, LinearMap.toSpanSingleton_apply, smul_eq_mul]`. Establish `key : ∀ Q ∈ T, ¬ K ≤ Q`.

Introduce `Q hQ hKQ`. Establish `hQprime : Q.IsPrime` using `hQ.1.1.1`. Establish `hnot : ¬ (∏ Q'' ∈ s.erase Q, Q'') ≤ Q`. Rewrite using `[hQprime.prod_le]`. Introduce and unpack `⟨i, hi, hiQ⟩`.

Establish `hiT : i ∈ T` using `(hsT i).1 (Finset.mem_of_mem_erase hi)`. Conclude with `Finset.ne_of_mem_erase hi (le_antisymm hiQ (hQ.1.2 hiT.1.1 hiQ))`. Take `⟨f, hfprod, hfQ⟩` from `SetLike.not_le_iff_exists.1 hnot`. Establish `hfo : ∀ Q'' ∈ T, Q'' ≠ Q → f ∈ Q''` using `fun Q'' hQ'' hne => (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_erase.2 ⟨hne, (hsT Q'').2 hQ''⟩))) hfprod`. Set `Qp : PrimeSpectrum B` to `⟨Q, hQprime⟩`.

Establish `hcl` using `hd Qp`. Rewrite `hcl` using `[mem_closure_iff]`. Take `⟨P, hPf, ⟨t, htP, htb⟩, hPfib⟩` from `hcl (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum B)) (PrimeSpectrum.basicOpen f).isOpen hfQ`. Establish `hPf' : f ∉ P.asIdeal` using `hPf`. Establish `hPover : P.asIdeal.comap (algebraMap A B) = p.asIdeal` using `(congrArg PrimeSpectrum.asIdeal hPfib).trans hQ.2`.

Establish `hI₀P : I₀ ≤ P.asIdeal` using `by rw [Ideal.map_le_iff_le_comap, hPover]`. Take `⟨Q', hQ'min, hQ'P⟩` from `Ideal.exists_minimalPrimes_le hI₀P`. Establish `hQ'T : Q' ∈ T` using `⟨hQ'min, le_antisymm ((Ideal.comap_mono hQ'P).trans hPover.le) (Ideal.map_le_iff_le_comap.1 hQ'min.1.2)⟩`. Distinguish the cases in `hQQ : Q' = Q`. Substitute `hQQ` using the available equality.

Conclude with `htP (hQ'P (hKQ ((hK t).2 htb)))`. Conclude with `hPf' (hQ'P (hfo Q' hQ'T hQQ))`. Establish `hprime : ∀ i ∈ s, i ≠ ⊥ → i ≠ ⊥ → (id i : Ideal B).IsPrime` using `fun i hi _ _ => ((hsT i).1 hi).1.1.1`. Establish `hnot` using `mt (Ideal.subset_union_prime (f := id) (I := K) ⊥ ⊥ hprime).1 (by`. Introduce and unpack `⟨i, hi, hKi⟩`.

Conclude with `key i ((hsT i).1 hi) hKi)`. Rewrite `hnot` using `[Set.not_subset]`. Take `⟨g, hgK, hgU⟩` from `hnot`. Use `⟨g, (hK g).1 hgK, fun Q hQ hQu hgQ => hgU ?_⟩` and prove the remaining obligations. Establish `hQT : Q ∈ T` using `⟨hQ, le_antisymm (Ideal.comap_mono hQu) (Ideal.map_le_iff_le_comap.1 hQ.1.2)⟩`.

Conclude with `Set.mem_biUnion (show Q ∈ (↑s : Set (Ideal B)) from (hsT Q).2 hQT) hgQ`.
-/
theorem annihilator_avoids_fibre_minimalPrimes
    (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B] (b : B)
    (hd : ∀ q : PrimeSpectrum B, q ∈ closure ({P : PrimeSpectrum B | ∃ s ∉ P.asIdeal, s * b = 0} ∩
      PrimeSpectrum.comap (algebraMap A B) ⁻¹' {PrimeSpectrum.comap (algebraMap A B) q}))
    (u : PrimeSpectrum B) : ∃ g : B, g * b = 0 ∧ ∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes,
      Q ≤ u.asIdeal → g ∉ Q := by
  classical
  let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) u
  let I₀ : Ideal B := p.asIdeal.map (algebraMap A B)
  let T : Set (Ideal B) := {Q | Q ∈ I₀.minimalPrimes ∧ Q.comap (algebraMap A B) = p.asIdeal}
  have hTfin : T.Finite := by
    let e := PrimeSpectrum.preimageOrderIsoFiber A B p
    haveI : IsNoetherianRing (p.asIdeal.Fiber B) :=
      Algebra.FiniteType.isNoetherianRing p.asIdeal.ResidueField _
    have hM : {j : PrimeSpectrum (p.asIdeal.Fiber B) | j.asIdeal ∈ minimalPrimes (p.asIdeal.Fiber B)}.Finite :=
      (minimalPrimes.finite_of_isNoetherianRing _).preimage (fun x _ y _ h => PrimeSpectrum.ext h)
    refine (hM.image fun j => (e.symm j).1.asIdeal).subset ?_
    rintro Q ⟨hQmin, hQp⟩
    have hQprime : Q.IsPrime := hQmin.1.1
    let Q' : PrimeSpectrum B := ⟨Q, hQprime⟩
    have hQ'mem : Q' ∈ PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p} := by
      show PrimeSpectrum.comap (algebraMap A B) Q' = p
      ext1; exact hQp
    obtain ⟨J, hJmin, hJle⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ (e ⟨Q', hQ'mem⟩).asIdeal)
    have hJprime : J.IsPrime := hJmin.1.1
    let j : PrimeSpectrum (p.asIdeal.Fiber B) := ⟨J, hJprime⟩
    refine ⟨j, hJmin, ?_⟩
    have hle : e.symm j ≤ ⟨Q', hQ'mem⟩ := by
      rw [← e.le_iff_le, e.apply_symm_apply]; exact hJle
    have hle' : (e.symm j).1.asIdeal ≤ Q := hle
    have hover : (e.symm j).1.asIdeal.comap (algebraMap A B) = p.asIdeal :=
      congrArg PrimeSpectrum.asIdeal (e.symm j).2
    have hge : I₀ ≤ (e.symm j).1.asIdeal := by
      rw [Ideal.map_le_iff_le_comap, hover]
    exact le_antisymm hle' (hQmin.2 ⟨(e.symm j).1.isPrime, hge⟩ hle')
  obtain ⟨s, hs⟩ := hTfin.exists_finset_coe
  have hsT : ∀ i, i ∈ s ↔ i ∈ T := fun i => by rw [← hs]; rfl
  let K : Ideal B := LinearMap.ker (LinearMap.toSpanSingleton B B b)
  have hK : ∀ x, x ∈ K ↔ x * b = 0 := fun x => by
    simp [K, LinearMap.toSpanSingleton_apply, smul_eq_mul]
  have key : ∀ Q ∈ T, ¬ K ≤ Q := by
    intro Q hQ hKQ
    have hQprime : Q.IsPrime := hQ.1.1.1
    have hnot : ¬ (∏ Q'' ∈ s.erase Q, Q'') ≤ Q := by
      rw [hQprime.prod_le]
      rintro ⟨i, hi, hiQ⟩
      have hiT : i ∈ T := (hsT i).1 (Finset.mem_of_mem_erase hi)
      exact Finset.ne_of_mem_erase hi (le_antisymm hiQ (hQ.1.2 hiT.1.1 hiQ))
    obtain ⟨f, hfprod, hfQ⟩ := SetLike.not_le_iff_exists.1 hnot
    have hfo : ∀ Q'' ∈ T, Q'' ≠ Q → f ∈ Q'' := fun Q'' hQ'' hne =>
      (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_erase.2 ⟨hne, (hsT Q'').2 hQ''⟩))) hfprod
    let Qp : PrimeSpectrum B := ⟨Q, hQprime⟩
    have hcl := hd Qp
    rw [mem_closure_iff] at hcl
    obtain ⟨P, hPf, ⟨t, htP, htb⟩, hPfib⟩ :=
      hcl (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum B)) (PrimeSpectrum.basicOpen f).isOpen hfQ
    have hPf' : f ∉ P.asIdeal := hPf
    have hPover : P.asIdeal.comap (algebraMap A B) = p.asIdeal :=
      (congrArg PrimeSpectrum.asIdeal hPfib).trans hQ.2
    have hI₀P : I₀ ≤ P.asIdeal := by rw [Ideal.map_le_iff_le_comap, hPover]
    obtain ⟨Q', hQ'min, hQ'P⟩ := Ideal.exists_minimalPrimes_le hI₀P
    have hQ'T : Q' ∈ T := ⟨hQ'min, le_antisymm ((Ideal.comap_mono hQ'P).trans hPover.le)
      (Ideal.map_le_iff_le_comap.1 hQ'min.1.2)⟩
    by_cases hQQ : Q' = Q
    · subst hQQ
      exact htP (hQ'P (hKQ ((hK t).2 htb)))
    · exact hPf' (hQ'P (hfo Q' hQ'T hQQ))
  have hprime : ∀ i ∈ s, i ≠ ⊥ → i ≠ ⊥ → (id i : Ideal B).IsPrime := fun i hi _ _ =>
    ((hsT i).1 hi).1.1.1
  have hnot := mt (Ideal.subset_union_prime (f := id) (I := K) ⊥ ⊥ hprime).1 (by
    rintro ⟨i, hi, hKi⟩; exact key i ((hsT i).1 hi) hKi)
  rw [Set.not_subset] at hnot
  obtain ⟨g, hgK, hgU⟩ := hnot
  refine ⟨g, (hK g).1 hgK, fun Q hQ hQu hgQ => hgU ?_⟩
  have hQT : Q ∈ T := ⟨hQ, le_antisymm (Ideal.comap_mono hQu) (Ideal.map_le_iff_le_comap.1 hQ.1.2)⟩
  exact Set.mem_biUnion (show Q ∈ (↑s : Set (Ideal B)) from (hsT Q).2 hQT) hgQ

end GlobalTheory
