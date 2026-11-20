import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplSpec

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

/- English proof (translation)
Introduce `Λ R σ _ _ _ _ s ii ann h d q o St Th hq hSt hkey E hE h0 p hp hpX hpq hpS`. Establish `hOver : ∀ (j : Fin (h + 1)) (P : Ideal (R ⧸ ii)), P.IsPrime → P.comap (Ideal.Quotient.mk ii) ≤ q j → ∃ Q : Ideal (o.B j), Q.IsPrime ∧ Q.comap (algebraMap (R ⧸ ii) (o.B j)) = P`. Introduce `j P hP hle`. Apply `(IsCplAt.exists_prime_over (R ⧸ ii) _ (o.B j) (o.cpl j)).1 P hP` to reduce the goal to its premises. Introduce `x hx`.

Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Conclude with `Ideal.mem_map_of_mem _ (hle hx)`. Establish `hInv : ∀ j : Fin (h + 1), ∃ Z : Ideal (o.B j), Z.IsPrime ∧ o.S j ≤ Z ∧ St (Z.comap (algebraMap (R ⧸ ii) (o.B j)))`. Introduce `j`. Proceed by induction on `j using Fin.induction with`.

Consider the case `zero`. Take `⟨p0, hp0, hp0X, hp0q, hp0St, hp0ann⟩` from `h0`. Take `⟨Q, hQ, hQc⟩` from `hOver 0 p0 hp0 hp0q`. Use `⟨Q, hQ, ?_, by rw [hQc]; exact hp0St⟩` and prove the remaining obligations. Use `(o.fib 0 Q hQ ?_).mpr ?_` and prove the remaining obligations.

Introduce `a`. Establish `hx` using `hp0X a`. Rewrite `hx` using `[← hQc]`. Conclude with `hx`. Rewrite using `[hQc]`.

Conclude with `hp0ann`. Consider the case `succ i ih`. Take `⟨Z, hZ, hSZ, hStZ⟩` from `ih`. Take `⟨hEp, hEX, hEc, hEs, hETh⟩` from `hE i`. Take `⟨Q, hQ, hQc⟩` from `hOver i.castSucc (E i) hEp hEc`.

Establish `hThQ` using `hETh Q hQ hQc`. Take `⟨Z0, hZ0, hZ0le⟩` from `Ideal.exists_minimalPrimes_le hSZ`. Establish `hStZ0` using `hSt _ _ (Ideal.comap_mono hZ0le) hStZ`. Establish `hZ0Q` using `hkey i.castSucc Z0 Q hZ0.1.1 hQ hStZ0 (o.dim _ Z0 hZ0) (Or.inr hThQ)`. Establish `hQX : ∀ a, algebraMap (R ⧸ ii) (o.B i.castSucc) (Ideal.Quotient.mk ii (s (MvPowerSeries.X a))) ∈ Q`.

Introduce `a`. Establish `hx` using `hEX a`. Rewrite `hx` using `[← hQc]`. Conclude with `hx`. Take `⟨Z', hZ', hSZ', hZ'c⟩` from `o.move i.castSucc i.succ Z0 Q hZ0.1.1 hQ hZ0.1.2 hZ0Q hQX (by rw [hQc]; exact hEs)`.

Conclude with `⟨Z', hZ', hSZ', by rw [hZ'c]; exact hStZ0⟩`. Take `⟨Z, hZ, hSZ, hStZ⟩` from `hInv (Fin.last h)`. Take `⟨Q, hQ, hQc⟩` from `hOver (Fin.last h) p hp hpq`. Establish `hQX : ∀ a, algebraMap (R ⧸ ii) (o.B (Fin.last h)) (Ideal.Quotient.mk ii (s (MvPowerSeries.X a))) ∈ Q`. Introduce `a`.

Establish `hx` using `hpX a`. Rewrite `hx` using `[← hQc]`. Conclude with `hx`. Take `⟨Z0, hZ0, hZ0le⟩` from `Ideal.exists_minimalPrimes_le hSZ`. Establish `hStZ0` using `hSt _ _ (Ideal.comap_mono hZ0le) hStZ`.

Establish `hQc' : St (Q.comap (algebraMap (R ⧸ ii) (o.B (Fin.last h)))) ∨ Th (Fin.last h) Q`. Break down `hpS with h1 | h1` into its components or cases. Use `left`. Rewrite using `[hQc]`. Conclude with `h1`.

Use `right`. Conclude with `h1 Q hQ hQc`. Establish `hZ0Q` using `hkey (Fin.last h) Z0 Q hZ0.1.1 hQ hStZ0 (o.dim _ Z0 hZ0) hQc'`. Establish `hann` using `(o.fib _ Q hQ hQX).mp (hZ0.1.2.trans hZ0Q)`. Rewrite `hann` using `[hQc]`.

Conclude with `hann`.
-/
theorem UpperTheory.V.Pa.Core.chainAbs :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [IsNoetherianRing R] (s : MvPowerSeries σ Λ →+* R) (ii ann : Ideal R) (h d : ℕ) (q : Fin (h + 1) → Ideal R) (o : PatchedSupportCompletions s ii ann q d) (St : Ideal (R ⧸ ii) → Prop) (Th : ∀ i, Ideal (o.B i) → Prop), (∀ i, (q i).IsPrime ∧ ii ≤ q i) → (∀ p p', p ≤ p' → St p' → St p) → (∀ i (Z Q : Ideal (o.B i)), Z.IsPrime → Q.IsPrime → St (Z.comap (algebraMap (R ⧸ ii) (o.B i))) → (d : WithBot ℕ∞) ≤ ringKrullDim (o.B i ⧸ Z) → St (Q.comap (algebraMap (R ⧸ ii) (o.B i))) ∨ Th i Q → Z ≤ Q) → ∀ E : Fin h → Ideal (R ⧸ ii), (∀ i, (E i).IsPrime ∧ (∀ a, Ideal.Quotient.mk ii (s (MvPowerSeries.X a)) ∈ E i) ∧ (E i).comap (Ideal.Quotient.mk ii) ≤ q i.castSucc ∧ (E i).comap (Ideal.Quotient.mk ii) ≤ q i.succ ∧ ∀ Q : Ideal (o.B i.castSucc), Q.IsPrime → Q.comap (algebraMap (R ⧸ ii) _) = E i → Th _ Q) → (∃ p : Ideal (R ⧸ ii), p.IsPrime ∧ (∀ a, Ideal.Quotient.mk ii (s (MvPowerSeries.X a)) ∈ p) ∧ p.comap (Ideal.Quotient.mk ii) ≤ q 0 ∧ St p ∧ ann ≤ p.comap (Ideal.Quotient.mk ii)) → ∀ p : Ideal (R ⧸ ii), p.IsPrime → (∀ a, Ideal.Quotient.mk ii (s (MvPowerSeries.X a)) ∈ p) → p.comap (Ideal.Quotient.mk ii) ≤ q (Fin.last h) → (St p ∨ ∀ Q : Ideal (o.B (Fin.last h)), Q.IsPrime → Q.comap (algebraMap (R ⧸ ii) _) = p → Th _ Q) → ann ≤ p.comap (Ideal.Quotient.mk ii) := by
  intro Λ R σ _ _ _ _ s ii ann h d q o St Th hq hSt hkey E hE h0 p hp hpX hpq hpS
  have hOver : ∀ (j : Fin (h + 1)) (P : Ideal (R ⧸ ii)), P.IsPrime →
      P.comap (Ideal.Quotient.mk ii) ≤ q j →
      ∃ Q : Ideal (o.B j), Q.IsPrime ∧ Q.comap (algebraMap (R ⧸ ii) (o.B j)) = P := by
    intro j P hP hle
    apply (IsCplAt.exists_prime_over (R ⧸ ii) _ (o.B j) (o.cpl j)).1 P hP
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.mem_map_of_mem _ (hle hx)
  have hInv : ∀ j : Fin (h + 1), ∃ Z : Ideal (o.B j), Z.IsPrime ∧ o.S j ≤ Z ∧
      St (Z.comap (algebraMap (R ⧸ ii) (o.B j))) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      obtain ⟨p0, hp0, hp0X, hp0q, hp0St, hp0ann⟩ := h0
      obtain ⟨Q, hQ, hQc⟩ := hOver 0 p0 hp0 hp0q
      refine ⟨Q, hQ, ?_, by rw [hQc]; exact hp0St⟩
      refine (o.fib 0 Q hQ ?_).mpr ?_
      · intro a
        have hx := hp0X a
        rw [← hQc] at hx
        exact hx
      · rw [hQc]
        exact hp0ann
    | succ i ih =>
      obtain ⟨Z, hZ, hSZ, hStZ⟩ := ih
      obtain ⟨hEp, hEX, hEc, hEs, hETh⟩ := hE i
      obtain ⟨Q, hQ, hQc⟩ := hOver i.castSucc (E i) hEp hEc
      have hThQ := hETh Q hQ hQc
      obtain ⟨Z0, hZ0, hZ0le⟩ := Ideal.exists_minimalPrimes_le hSZ
      have hStZ0 := hSt _ _ (Ideal.comap_mono hZ0le) hStZ
      have hZ0Q := hkey i.castSucc Z0 Q hZ0.1.1 hQ hStZ0 (o.dim _ Z0 hZ0) (Or.inr hThQ)
      have hQX : ∀ a, algebraMap (R ⧸ ii) (o.B i.castSucc)
          (Ideal.Quotient.mk ii (s (MvPowerSeries.X a))) ∈ Q := by
        intro a
        have hx := hEX a
        rw [← hQc] at hx
        exact hx
      obtain ⟨Z', hZ', hSZ', hZ'c⟩ := o.move i.castSucc i.succ Z0 Q hZ0.1.1 hQ hZ0.1.2 hZ0Q hQX
        (by rw [hQc]; exact hEs)
      exact ⟨Z', hZ', hSZ', by rw [hZ'c]; exact hStZ0⟩
  obtain ⟨Z, hZ, hSZ, hStZ⟩ := hInv (Fin.last h)
  obtain ⟨Q, hQ, hQc⟩ := hOver (Fin.last h) p hp hpq
  have hQX : ∀ a, algebraMap (R ⧸ ii) (o.B (Fin.last h))
      (Ideal.Quotient.mk ii (s (MvPowerSeries.X a))) ∈ Q := by
    intro a
    have hx := hpX a
    rw [← hQc] at hx
    exact hx
  obtain ⟨Z0, hZ0, hZ0le⟩ := Ideal.exists_minimalPrimes_le hSZ
  have hStZ0 := hSt _ _ (Ideal.comap_mono hZ0le) hStZ
  have hQc' : St (Q.comap (algebraMap (R ⧸ ii) (o.B (Fin.last h)))) ∨ Th (Fin.last h) Q := by
    rcases hpS with h1 | h1
    · left
      rw [hQc]
      exact h1
    · right
      exact h1 Q hQ hQc
  have hZ0Q := hkey (Fin.last h) Z0 Q hZ0.1.1 hQ hStZ0 (o.dim _ Z0 hZ0) hQc'
  have hann := (o.fib _ Q hQ hQX).mp (hZ0.1.2.trans hZ0Q)
  rw [hQc] at hann
  exact hann
