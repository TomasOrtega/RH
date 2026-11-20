import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IterCancel
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.Bridge

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

/- English proof (translation)
Rewrite using `[ringKrullDim_quotient, h]`. Conclude with `Order.krullDim_eq_of_orderIso OrderIso.Set.univ`.
-/
private theorem dim_of_univ {R : Type} [CommRing R] (I : Ideal R)
    (h : PrimeSpectrum.zeroLocus (I : Set R) = Set.univ) :
    ringKrullDim (R ⧸ I) = ringKrullDim R := by
  rw [ringKrullDim_quotient, h]
  exact Order.krullDim_eq_of_orderIso OrderIso.Set.univ

/- English proof (translation)
Introduce `I _ hI`. Rewrite using `[PrimeSpectrum.zeroLocus_bot, ← Set.compl_eq_univ_diff]`. Establish `hne : (PrimeSpectrum.zeroLocus (I : Set R))ᶜ.Nonempty`. Rewrite using `[Set.nonempty_compl]`. Introduce `h`.

Rewrite `hI` using `[dim_of_univ I h]`. Conclude with `absurd hj (not_le.mpr hI)`. Establish `ho : IsOpen (PrimeSpectrum.zeroLocus (I : Set R))ᶜ` using `(PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl`. Establish `hp : IsPreirreducible (PrimeSpectrum.zeroLocus (I : Set R))ᶜ` using `(PreirreducibleSpace.isPreirreducible_univ).open_subset ho (Set.subset_univ _)`. Conclude with `⟨hne, hp.isPreconnected⟩`.
-/
private theorem connOn_irr {R : Type} [CommRing R] [IrreducibleSpace (PrimeSpectrum R)]
    (j : WithBot ℕ∞) (hj : j ≤ ringKrullDim R) : ConnOn (⊥ : Ideal R) j := by
  intro I _ hI
  rw [PrimeSpectrum.zeroLocus_bot, ← Set.compl_eq_univ_diff]
  have hne : (PrimeSpectrum.zeroLocus (I : Set R))ᶜ.Nonempty := by
    rw [Set.nonempty_compl]
    intro h
    rw [dim_of_univ I h] at hI
    exact absurd hj (not_le.mpr hI)
  have ho : IsOpen (PrimeSpectrum.zeroLocus (I : Set R))ᶜ :=
    (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
  have hp : IsPreirreducible (PrimeSpectrum.zeroLocus (I : Set R))ᶜ :=
    (PreirreducibleSpace.isPreirreducible_univ).open_subset ho (Set.subset_univ _)
  exact ⟨hne, hp.isPreconnected⟩

/- English proof (translation)
Establish `hn : (nilradical R).IsPrime` using `PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp inferInstance`. Establish `hpp : p.IsPrime` using `hp.1.1`. Establish `hle : p ≤ nilradical R` using `hp.2 ⟨hn, bot_le⟩ (nilradical_le_prime p)`. Apply `dim_of_univ` to reduce the goal to its premises. Use `Set.eq_univ_of_forall fun q => ?_` and prove the remaining obligations.

Rewrite using `[PrimeSpectrum.mem_zeroLocus]`. Conclude with `hle.trans (nilradical_le_prime q.asIdeal)`.
-/
private theorem dim_min {R : Type} [CommRing R] [IrreducibleSpace (PrimeSpectrum R)]
    (p : Ideal R) (hp : p ∈ (⊥ : Ideal R).minimalPrimes) :
    ringKrullDim (R ⧸ p) = ringKrullDim R := by
  have hn : (nilradical R).IsPrime :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp inferInstance
  have hpp : p.IsPrime := hp.1.1
  have hle : p ≤ nilradical R := hp.2 ⟨hn, bot_le⟩ (nilradical_le_prime p)
  apply dim_of_univ
  refine Set.eq_univ_of_forall fun q => ?_
  rw [PrimeSpectrum.mem_zeroLocus]
  exact hle.trans (nilradical_le_prime q.asIdeal)

/- English proof (translation)
Introduce `I hbI hI`. Establish `hz : PrimeSpectrum.zeroLocus (a : Set R) = PrimeSpectrum.zeroLocus (b : Set R)`. Rewrite using `[← PrimeSpectrum.zeroLocus_radical a, hab, PrimeSpectrum.zeroLocus_radical]`. Establish `haI : a ≤ I.radical` using `Ideal.le_radical.trans (hab.le.trans (Ideal.radical_mono hbI))`. Establish `hd : ringKrullDim (R ⧸ I.radical) = ringKrullDim (R ⧸ I)`.

Rewrite using `[ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]`. Use `h I.radical haI (hd ▸ hI)` as an intermediate fact. Rewrite `this` using `[hz, PrimeSpectrum.zeroLocus_radical]`. Then use the resulting hypothesis.
-/
private theorem connOn_rad {R : Type} [CommRing R] (a b : Ideal R) (k : WithBot ℕ∞)
    (hab : a.radical = b.radical) (h : ConnOn a k) : ConnOn b k := by
  intro I hbI hI
  have hz : PrimeSpectrum.zeroLocus (a : Set R) = PrimeSpectrum.zeroLocus (b : Set R) := by
    rw [← PrimeSpectrum.zeroLocus_radical a, hab, PrimeSpectrum.zeroLocus_radical]
  have haI : a ≤ I.radical :=
    Ideal.le_radical.trans (hab.le.trans (Ideal.radical_mono hbI))
  have hd : ringKrullDim (R ⧸ I.radical) = ringKrullDim (R ⧸ I) := by
    rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]
  have := h I.radical haI (hd ▸ hI)
  rwa [hz, PrimeSpectrum.zeroLocus_radical] at this

/- English proof (translation)
Introduce `R _ _ _ _ hC a h k ha ⟨s, hs, hrad⟩ hdim`. Establish `h1 : ((k + s.card + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R` using `le_trans (by exact_mod_cast (by omega : k + s.card + 1 ≤ k + h + 1)) hdim`. Establish `h0 : ((k + s.card : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R` using `le_trans (by exact_mod_cast (by omega : k + s.card ≤ k + s.card + 1)) h1`. Establish `hm : ∀ f ∈ s, f ∈ maximalIdeal R`. Introduce `f hf`.

Establish `h2 : f ∈ a.radical` using `hrad ▸ Ideal.le_radical (Ideal.subset_span hf)`. Conclude with `le_maximalIdeal (fun ht => ha (Ideal.radical_eq_top.mp ht)) h2`. Establish `key` using `UpperTheory.V.AlgebraTools.Conn.iter hC ⊥ s k hm (connOn_irr _ h0) (fun p hp => (dim_min p hp).symm ▸ h1)`. Rewrite `key` using `[bot_sup_eq]`. Conclude with `(UpperTheory.V.AlgebraTools.Conn.bridge a k).mp (connOn_rad _ _ _ hrad key)`.
-/
theorem UpperTheory.V.AlgebraTools.Conn.main :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IrreducibleSpace (PrimeSpectrum R)], CohenType R →
      ∀ (a : Ideal R) (h k : ℕ), a ≠ ⊤ → ReciprocityTheory.CA.AraLE a h → ((k + h + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R →
        ReciprocityTheory.CA.ConnInDim (R ⧸ a) k := by
  intro R _ _ _ _ hC a h k ha ⟨s, hs, hrad⟩ hdim
  have h1 : ((k + s.card + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R :=
    le_trans (by exact_mod_cast (by omega : k + s.card + 1 ≤ k + h + 1)) hdim
  have h0 : ((k + s.card : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R :=
    le_trans (by exact_mod_cast (by omega : k + s.card ≤ k + s.card + 1)) h1
  have hm : ∀ f ∈ s, f ∈ maximalIdeal R := by
    intro f hf
    have h2 : f ∈ a.radical := hrad ▸ Ideal.le_radical (Ideal.subset_span hf)
    exact le_maximalIdeal (fun ht => ha (Ideal.radical_eq_top.mp ht)) h2
  have key := UpperTheory.V.AlgebraTools.Conn.iter hC ⊥ s k hm (connOn_irr _ h0)
    (fun p hp => (dim_min p hp).symm ▸ h1)
  rw [bot_sup_eq] at key
  exact (UpperTheory.V.AlgebraTools.Conn.bridge a k).mp (connOn_rad _ _ _ hrad key)
