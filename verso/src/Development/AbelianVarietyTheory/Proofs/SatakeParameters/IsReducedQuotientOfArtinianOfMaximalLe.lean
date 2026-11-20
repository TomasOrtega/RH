import Mathlib

namespace GlobalTheory

open scoped BigOperators

/- English proof (translation)
Establish `hsurj : Function.Surjective (Ideal.Quotient.mk I)` using `Ideal.Quotient.mk_surjective`. Use `set m := M.comap (Ideal.Quotient.mk I) with hm`. Establish `hmax : m.IsMaximal` using `Ideal.comap_isMaximal_of_surjective _ hsurj`. Establish `hIm : I ≤ m`. Introduce `x hx`.

Simplify using `[hm, Ideal.Quotient.eq_zero_iff_mem.mpr hx]`. Establish `key` using `Ideal.map_mono (f := Ideal.Quotient.mk I) (h m hmax hIm)`. Rewrite `key` using `[Ideal.map_sup, Ideal.map_pow, Ideal.map_quotient_self, bot_sup_eq, hm, Ideal.map_comap_of_surjective _ hsurj]`. Conclude with `key`.
-/
theorem quotient_maximal_le_sq {A : Type} [CommRing A] (I : Ideal A)
    (h : ∀ m : Ideal A, m.IsMaximal → I ≤ m → m ≤ I ⊔ m ^ 2)
    (M : Ideal (A ⧸ I)) (hM : M.IsMaximal) : M ≤ M ^ 2 := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  set m := M.comap (Ideal.Quotient.mk I) with hm
  have hmax : m.IsMaximal := Ideal.comap_isMaximal_of_surjective _ hsurj
  have hIm : I ≤ m := by
    intro x hx
    simp [hm, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have key := Ideal.map_mono (f := Ideal.Quotient.mk I) (h m hmax hIm)
  rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_quotient_self, bot_sup_eq,
    hm, Ideal.map_comap_of_surjective _ hsurj] at key
  exact key

/- English proof (translation)
Establish `h2 : M * M = M`. Rewrite using `[← sq]`. Conclude with `le_antisymm (Ideal.pow_le_self two_ne_zero) h`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ, ih, h2]`.
-/
theorem pow_eq_self_of_le_sq {R : Type} [CommRing R] (M : Ideal R) (h : M ≤ M ^ 2) :
    ∀ k : ℕ, M ^ (k + 1) = M := by
  have h2 : M * M = M := by
    rw [← sq]; exact le_antisymm (Ideal.pow_le_self two_ne_zero) h
  intro k
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, h2]

/- English proof (translation)
Use `set R := A ⧸ I`. Use `haveI : Finite (MaximalSpectrum R) := inferInstance`. Use `haveI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _`. Use `set J : Ideal R := ∏ M : MaximalSpectrum R, M.asIdeal with hJ`. Establish `hJinf : J = ⨅ M ∈ (Finset.univ : Finset (MaximalSpectrum R)), M.asIdeal`.

Rewrite using `[hJ]`. Apply `Ideal.prod_eq_iInf_of_pairwise_isCoprime` to reduce the goal to its premises. Introduce `a _ b _ hab`. Conclude with `Ideal.isCoprime_of_isMaximal (fun e => hab (MaximalSpectrum.ext e))`. Establish `hpow : ∀ k : ℕ, J ^ (k + 1) = J`.

Introduce `k`. Rewrite using `[hJ, ← Finset.prod_pow]`. Use `Finset.prod_congr rfl (fun M _ => ?_)` and prove the remaining obligations. Conclude with `pow_eq_self_of_le_sq _ (quotient_maximal_le_sq I h M.asIdeal M.isMaximal) k`. Establish `hJjac : J ≤ Ideal.jacobson ⊥`.

Rewrite using `[hJinf]`. Introduce `x hx`. Rewrite using `[Ideal.mem_jacobson_bot]`. Introduce `y`. Assume the negation of the conclusion as `hu`.

Take `⟨M, hMmax, hM⟩` from `Ideal.exists_le_maximal (Ideal.span {x * y + 1}) (by rwa [Ne, Ideal.span_singleton_eq_top])`. Establish `hxM : x ∈ M`. Use `(Submodule.mem_iInf _).mp hx ⟨M, hMmax⟩` as an intermediate fact. Simplify using `using this`. Establish `h1 : x * y + 1 ∈ M` using `hM (Ideal.subset_span rfl)`.

Establish `: (1 : R) ∈ M`. Use `M.sub_mem h1 (M.mul_mem_right y hxM)` as an intermediate fact. Simplify using `using this`. Conclude with `hMmax.ne_top ((Ideal.eq_top_iff_one _).mpr this)`. Take `⟨n, hn⟩` from `IsArtinianRing.isNilpotent_jacobson_bot (R := R)`.

Establish `hJbot : J = ⊥`. Rewrite using `[← hpow n]`. Use `le_bot_iff.mp ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `⟨fun x hx => ?_⟩` and prove the remaining obligations.

Establish `hxJ : x ∈ J`. Rewrite using `[hJinf]`. Use `(Submodule.mem_iInf _).mpr (fun M => (Submodule.mem_iInf _).mpr (fun _ => ?_))` and prove the remaining obligations. Conclude with `(hx.map (Ideal.Quotient.mk M.asIdeal)).eq_zero |> Ideal.Quotient.eq_zero_iff_mem.mp`. Rewrite `hxJ` using `[hJbot]`.

Conclude with `(Submodule.mem_bot R).mp hxJ`.
-/
theorem isReduced_quotient_of_artinian_of_maximal_le (A : Type) [CommRing A] (I : Ideal A)
    (hart : IsArtinianRing (A ⧸ I))
    (h : ∀ m : Ideal A, m.IsMaximal → I ≤ m → m ≤ I ⊔ m ^ 2) : IsReduced (A ⧸ I) := by
  classical
  set R := A ⧸ I
  haveI : Finite (MaximalSpectrum R) := inferInstance
  haveI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  set J : Ideal R := ∏ M : MaximalSpectrum R, M.asIdeal with hJ
  have hJinf : J = ⨅ M ∈ (Finset.univ : Finset (MaximalSpectrum R)), M.asIdeal := by
    rw [hJ]
    apply Ideal.prod_eq_iInf_of_pairwise_isCoprime
    intro a _ b _ hab
    exact Ideal.isCoprime_of_isMaximal (fun e => hab (MaximalSpectrum.ext e))
  have hpow : ∀ k : ℕ, J ^ (k + 1) = J := by
    intro k
    rw [hJ, ← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun M _ => ?_)
    exact pow_eq_self_of_le_sq _ (quotient_maximal_le_sq I h M.asIdeal M.isMaximal) k
  have hJjac : J ≤ Ideal.jacobson ⊥ := by
    rw [hJinf]
    intro x hx
    rw [Ideal.mem_jacobson_bot]
    intro y
    by_contra hu
    obtain ⟨M, hMmax, hM⟩ := Ideal.exists_le_maximal (Ideal.span {x * y + 1})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    have hxM : x ∈ M := by
      have := (Submodule.mem_iInf _).mp hx ⟨M, hMmax⟩
      simpa using this
    have h1 : x * y + 1 ∈ M := hM (Ideal.subset_span rfl)
    have : (1 : R) ∈ M := by
      have := M.sub_mem h1 (M.mul_mem_right y hxM)
      simpa using this
    exact hMmax.ne_top ((Ideal.eq_top_iff_one _).mpr this)
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  have hJbot : J = ⊥ := by
    rw [← hpow n]
    refine le_bot_iff.mp ?_
    calc J ^ (n + 1) ≤ (Ideal.jacobson ⊥) ^ (n + 1) := Ideal.pow_right_mono hJjac _
      _ ≤ (Ideal.jacobson ⊥) ^ n := Ideal.pow_le_pow_right (Nat.le_succ n)
      _ = ⊥ := hn
  refine ⟨fun x hx => ?_⟩
  have hxJ : x ∈ J := by
    rw [hJinf]
    refine (Submodule.mem_iInf _).mpr (fun M => (Submodule.mem_iInf _).mpr (fun _ => ?_))
    exact (hx.map (Ideal.Quotient.mk M.asIdeal)).eq_zero |> Ideal.Quotient.eq_zero_iff_mem.mp
  rw [hJbot] at hxJ
  exact (Submodule.mem_bot R).mp hxJ

end GlobalTheory
