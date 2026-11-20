import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicLocalizationStrictHenselisationNoTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocIndEtaleIsDomainIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicEqOneOfForallPrimeMaximalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndEtalePrimeComparison
open GlobalTheory.EtC

namespace GlobalTheory.QPic

/- English proof (translation)
The claim follows from `GlobalTheory.T.pic_eq_one_of_forall_prime_maximal`.
-/
theorem pic0 : ∀ (R : Type) [CommRing R], (∀ P : Ideal R, P.IsPrime → P.IsMaximal) → ∀ c : CommRing.Pic R, c = 1 := GlobalTheory.T.pic_eq_one_of_forall_prime_maximal

/- English proof (translation)
The claim follows from `GlobalTheory.T.ind_etale_prime_comparison`.
-/
theorem incomp : ∀ (B O : Type) [CommRing B] [CommRing O] [Algebra B O], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra B O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra B E) (_ : Algebra.Etale B E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[B] Si i)) → ∀ p p' : Ideal O, p.IsPrime → p'.IsPrime → p ≤ p' → p.comap (algebraMap B O) = p'.comap (algebraMap B O) → p = p' := GlobalTheory.T.ind_etale_prime_comparison

/- English proof (translation)
Introduce `T _ _ P P' hP hP' hle h0 hC`. Set `K` to `FractionRing T`. Use `letI : Algebra (Polynomial T) (Polynomial K) := Polynomial.algebra T K`. Use `haveI : IsLocalization (Submonoid.map Polynomial.C (nonZeroDivisors T)) (Polynomial K) := Polynomial.isLocalization (nonZeroDivisors T) K`. Use `set M := Submonoid.map Polynomial.C (nonZeroDivisors T) with hM`.

Establish `hdisj' : Disjoint (M : Set (Polynomial T)) (P' : Set (Polynomial T))`. Rewrite using `[Set.disjoint_left]`. Introduce and unpack `_ ⟨s, hs, rfl⟩ hsP`. Establish `: s ∈ P'.comap (algebraMap T (Polynomial T))`. Rewrite using `[Ideal.mem_comap, Polynomial.algebraMap_eq]`.

Conclude with `hsP`. Rewrite `this` using `[hC, Ideal.mem_bot]`. Conclude with `nonZeroDivisors.ne_zero hs this`. Establish `hdisj : Disjoint (M : Set (Polynomial T)) (P : Set (Polynomial T))` using `hdisj'.mono_right hle`. Establish `hPK` using `IsLocalization.isPrime_of_isPrime_disjoint M (Polynomial K) P hP hdisj`.

Establish `hP'K` using `IsLocalization.isPrime_of_isPrime_disjoint M (Polynomial K) P' hP' hdisj'`. Establish `hc` using `IsLocalization.comap_map_of_isPrime_disjoint M (Polynomial K) hP hdisj`. Establish `hc'` using `IsLocalization.comap_map_of_isPrime_disjoint M (Polynomial K) hP' hdisj'`. Establish `hM0 : (0 : Polynomial T) ∉ M`. Introduce `h`.

Take `⟨s, hs, hs0⟩` from `Submonoid.mem_map.mp h`. Conclude with `nonZeroDivisors.ne_zero hs (Polynomial.C_eq_zero.mp hs0)`. Establish `hne : P.map (algebraMap (Polynomial T) (Polynomial K)) ≠ ⊥`. Introduce `hb`. Apply `h0` to reduce the goal to its premises.

Rewrite using `[← hc, hb, eq_bot_iff]`. Introduce `x hx0`. Establish `hx : algebraMap (Polynomial T) (Polynomial K) x = 0` using `(Ideal.mem_bot).mp hx0`. Conclude with `(Ideal.mem_bot).mpr (IsLocalization.injective (Polynomial K) (le_nonZeroDivisors_of_noZeroDivisors hM0) (hx.trans (map_zero _).symm))`. Establish `hmax : (P.map (algebraMap (Polynomial T) (Polynomial K))).IsMaximal` using `hPK.isMaximal hne`.

Establish `heq` using `hmax.eq_of_le hP'K.ne_top (Ideal.map_mono hle)`. Rewrite using `[← hc, ← hc', heq]`.
-/
theorem poly : ∀ (T : Type) [CommRing T] [IsDomain T] (P P' : Ideal (Polynomial T)), P.IsPrime → P'.IsPrime → P ≤ P' → P ≠ ⊥ → P'.comap (algebraMap T (Polynomial T)) = ⊥ → P = P' := by
  intro T _ _ P P' hP hP' hle h0 hC
  let K := FractionRing T
  letI : Algebra (Polynomial T) (Polynomial K) := Polynomial.algebra T K
  haveI : IsLocalization (Submonoid.map Polynomial.C (nonZeroDivisors T)) (Polynomial K) :=
    Polynomial.isLocalization (nonZeroDivisors T) K
  set M := Submonoid.map Polynomial.C (nonZeroDivisors T) with hM
  have hdisj' : Disjoint (M : Set (Polynomial T)) (P' : Set (Polynomial T)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsP
    have : s ∈ P'.comap (algebraMap T (Polynomial T)) := by
      rw [Ideal.mem_comap, Polynomial.algebraMap_eq]; exact hsP
    rw [hC, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hs this
  have hdisj : Disjoint (M : Set (Polynomial T)) (P : Set (Polynomial T)) :=
    hdisj'.mono_right hle
  have hPK := IsLocalization.isPrime_of_isPrime_disjoint M (Polynomial K) P hP hdisj
  have hP'K := IsLocalization.isPrime_of_isPrime_disjoint M (Polynomial K) P' hP' hdisj'
  have hc := IsLocalization.comap_map_of_isPrime_disjoint M (Polynomial K) hP hdisj
  have hc' := IsLocalization.comap_map_of_isPrime_disjoint M (Polynomial K) hP' hdisj'
  have hM0 : (0 : Polynomial T) ∉ M := by
    intro h
    obtain ⟨s, hs, hs0⟩ := Submonoid.mem_map.mp h
    exact nonZeroDivisors.ne_zero hs (Polynomial.C_eq_zero.mp hs0)
  have hne : P.map (algebraMap (Polynomial T) (Polynomial K)) ≠ ⊥ := by
    intro hb
    apply h0
    rw [← hc, hb, eq_bot_iff]
    intro x hx0
    have hx : algebraMap (Polynomial T) (Polynomial K) x = 0 := (Ideal.mem_bot).mp hx0
    exact (Ideal.mem_bot).mpr (IsLocalization.injective (Polynomial K) (le_nonZeroDivisors_of_noZeroDivisors hM0)
      (hx.trans (map_zero _).symm))
  have hmax : (P.map (algebraMap (Polynomial T) (Polynomial K))).IsMaximal := hPK.isMaximal hne
  have heq := hmax.eq_of_le hP'K.ne_top (Ideal.map_mono hle)
  rw [← hc, ← hc', heq]

/- English proof (translation)
Establish `h1 : CommRing.Pic.mapRingHom e.toRingHom c = 1` using `h _ (by rw [← map_pow, hc, map_one])`. Establish `h2 : CommRing.Pic.mapRingHom e.symm.toRingHom (CommRing.Pic.mapRingHom e.toRingHom c) = c`. Rewrite using `[CommRing.Pic.mapRingHom_mapRingHom]`. Establish `: e.symm.toRingHom.comp e.toRingHom = RingHom.id R` using `by ext x; simp`. Rewrite using `[this, CommRing.Pic.mapRingHom_id_apply]`.

Rewrite using `[← h2, h1, map_one]`.
-/
theorem pic_transfer {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (q : ℕ)
    (h : ∀ c : CommRing.Pic S, c ^ q = 1 → c = 1) (c : CommRing.Pic R) (hc : c ^ q = 1) : c = 1 := by
  have h1 : CommRing.Pic.mapRingHom e.toRingHom c = 1 := h _ (by rw [← map_pow, hc, map_one])
  have h2 : CommRing.Pic.mapRingHom e.symm.toRingHom (CommRing.Pic.mapRingHom e.toRingHom c) = c := by
    rw [CommRing.Pic.mapRingHom_mapRingHom]
    have : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := by ext x; simp
    rw [this, CommRing.Pic.mapRingHom_id_apply]
  rw [← h2, h1, map_one]

/- English proof (translation)
Establish `hinc` using `incomp (Polynomial T) O hind`. Use `hinc p p' inferInstance inferInstance hle ?_` and prove the remaining obligations. Use `poly T _ _ (Ideal.comap_isPrime _ _) (Ideal.comap_isPrime _ _) (Ideal.comap_mono hle) ?_ ?_` and prove the remaining obligations. Introduce `hb`. Establish `: (⊥ : Ideal O).comap (algebraMap (Polynomial T) O) = p.comap (algebraMap (Polynomial T) O)`.

Apply `le_antisymm (Ideal.comap_mono bot_le)` to reduce the goal to its premises. Rewrite using `[hb]`. Conclude with `bot_le`. Conclude with `h0 (hinc ⊥ p Ideal.bot_prime inferInstance bot_le this).symm`. Rewrite using `[Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]`.

Conclude with `hT`.
-/
theorem primes_eq (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [IsDomain O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (hind : ∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i))
    (p p' : Ideal O) [p.IsPrime] [p'.IsPrime] (hle : p ≤ p') (h0 : p ≠ ⊥)
    (hT : p'.comap (algebraMap T O) = ⊥) : p = p' := by
  have hinc := incomp (Polynomial T) O hind
  refine hinc p p' inferInstance inferInstance hle ?_
  refine poly T _ _ (Ideal.comap_isPrime _ _) (Ideal.comap_isPrime _ _) (Ideal.comap_mono hle) ?_ ?_
  · intro hb
    have : (⊥ : Ideal O).comap (algebraMap (Polynomial T) O) = p.comap (algebraMap (Polynomial T) O) := by
      apply le_antisymm (Ideal.comap_mono bot_le); rw [hb]; exact bot_le
    exact h0 (hinc ⊥ p Ideal.bot_prime inferInstance bot_le this).symm
  · rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]; exact hT

end GlobalTheory.QPic

open GlobalTheory.QPic in

/- English proof (translation)
Introduce `q _ T _ _ _ hAIC hq O _ _ _ _ _ _ hind A _ _ _ _ π hπ c hc`. Use `haveI : IsIntegrallyClosed T := GlobalTheory.LocIndEtale.isIntegrallyClosed_of_forall_monic_root T hAIC`. Use `haveI : IsDomain O := (GlobalTheory.indEtale_isDomain_isIntegrallyClosed (Polynomial T) O hind).1`. Set `eA` to `Localization.tensorRightAlgEquiv (nonZeroDivisors T) A`. Distinguish the cases in `hI : RingHom.ker (π : O →+* A) = ⊥`.

Establish `hinj : Function.Injective π` using `(RingHom.injective_iff_ker_eq_bot _).mpr hI`. Set `eπ : O ≃ₐ[T] A` to `AlgEquiv.ofBijective (π.restrictScalars T) ⟨hinj, hπ⟩`. Set `e1 : TensorProduct T (FractionRing T) A ≃ₐ[T] TensorProduct T (FractionRing T) O` to `Algebra.TensorProduct.congr AlgEquiv.refl eπ.symm`. Set `e2` to `Localization.tensorRightAlgEquiv (nonZeroDivisors T) O`. Use `pic_transfer (e1.toRingEquiv.trans e2.toRingEquiv) q ?_ c hc` and prove the remaining obligations.

Conclude with `GlobalTheory.pic_localization_strictHenselisation_no_torsion T O q ⟨inferInstance, hAIC⟩ hq (Nat.pos_of_ne_zero (NeZero.ne q)) hind`. Use `pic_transfer eA.toRingEquiv q (fun c' _ => pic0 _ ?_ c') c hc` and prove the remaining obligations. Introduce `Q hQ`. Take `⟨Q', hQ'max, hle⟩` from `Ideal.exists_le_maximal Q hQ.ne_top`. It suffices to establish `hQQ : Q = Q' by rw [hQQ]; exact hQ'max`.

Use `set L := Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors T))`. Establish `hQ'p : Q'.IsPrime` using `hQ'max.isPrime`. Use `set p := (Q.comap (algebraMap A L)).comap (π : O →+* A) with hpdef`. Use `set p' := (Q'.comap (algebraMap A L)).comap (π : O →+* A) with hp'def`. Establish `hpp : p = p'`.

Use `primes_eq T O hind p p' (Ideal.comap_mono (Ideal.comap_mono hle)) ?_ ?_` and prove the remaining obligations. Introduce `hb`. Apply `hI` to reduce the goal to its premises. Rewrite using `[eq_bot_iff, ← hb]`. Introduce `x hx`.

Rewrite `hx` using `[RingHom.mem_ker]`. Simplify using `[hpdef, hx]`. Rewrite using `[eq_bot_iff]`. Introduce `t ht`. Rewrite `ht` using `[Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap]`.

Rewrite using `[Ideal.mem_bot]`. Assume the negation of the conclusion as `ht0`. Establish `hcomm : (π : O →+* A) (algebraMap T O t) = algebraMap T A t`. Rewrite using `[IsScalarTower.algebraMap_apply T (Polynomial T) O, IsScalarTower.algebraMap_apply T (Polynomial T) A]`. Conclude with `π.commutes _`.

Rewrite `ht` using `[hcomm]`. Establish `hu : IsUnit (algebraMap A L (algebraMap T A t))` using `IsLocalization.map_units L (⟨algebraMap T A t, t, mem_nonZeroDivisors_of_ne_zero ht0, rfl⟩ : Algebra.algebraMapSubmonoid A (nonZeroDivisors T))`. Conclude with `hQ'p.ne_top (Ideal.eq_top_of_isUnit_mem _ ht hu)`. Establish `hqq : Q.comap (algebraMap A L) = Q'.comap (algebraMap A L)`. Rewrite using `[← Ideal.map_comap_of_surjective (π : O →+* A) hπ (Q.comap (algebraMap A L)), ← Ideal.map_comap_of_surjective (π : O →+* A) hπ (Q'.comap (algebraMap A L))]`.

Conclude with `congrArg _ hpp`. Rewrite using `[← IsLocalization.map_comap (Algebra.algebraMapSubmonoid A (nonZeroDivisors T)) L Q, ← IsLocalization.map_comap (Algebra.algebraMapSubmonoid A (nonZeroDivisors T)) L Q']`. Conclude with `congrArg (Ideal.map (algebraMap A L)) hqq`.
-/
theorem GlobalTheory.pic_generic_fibre_quotient_strictHenselisation_no_torsion : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A] (π : O →ₐ[Polynomial T] A), Function.Surjective π → ∀ c : CommRing.Pic (TensorProduct T (FractionRing T) A), c ^ q = 1 → c = 1 := by
  intro q _ T _ _ _ hAIC hq O _ _ _ _ _ _ hind A _ _ _ _ π hπ c hc
  haveI : IsIntegrallyClosed T := GlobalTheory.LocIndEtale.isIntegrallyClosed_of_forall_monic_root T hAIC
  haveI : IsDomain O := (GlobalTheory.indEtale_isDomain_isIntegrallyClosed (Polynomial T) O hind).1
  let eA := Localization.tensorRightAlgEquiv (nonZeroDivisors T) A
  by_cases hI : RingHom.ker (π : O →+* A) = ⊥
  · have hinj : Function.Injective π := (RingHom.injective_iff_ker_eq_bot _).mpr hI
    let eπ : O ≃ₐ[T] A := AlgEquiv.ofBijective (π.restrictScalars T) ⟨hinj, hπ⟩
    let e1 : TensorProduct T (FractionRing T) A ≃ₐ[T] TensorProduct T (FractionRing T) O :=
      Algebra.TensorProduct.congr AlgEquiv.refl eπ.symm
    let e2 := Localization.tensorRightAlgEquiv (nonZeroDivisors T) O
    refine pic_transfer (e1.toRingEquiv.trans e2.toRingEquiv) q ?_ c hc
    exact GlobalTheory.pic_localization_strictHenselisation_no_torsion T O q ⟨inferInstance, hAIC⟩ hq
      (Nat.pos_of_ne_zero (NeZero.ne q)) hind
  · refine pic_transfer eA.toRingEquiv q (fun c' _ => pic0 _ ?_ c') c hc
    intro Q hQ
    obtain ⟨Q', hQ'max, hle⟩ := Ideal.exists_le_maximal Q hQ.ne_top
    suffices hQQ : Q = Q' by rw [hQQ]; exact hQ'max
    set L := Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors T))
    have hQ'p : Q'.IsPrime := hQ'max.isPrime
    set p := (Q.comap (algebraMap A L)).comap (π : O →+* A) with hpdef
    set p' := (Q'.comap (algebraMap A L)).comap (π : O →+* A) with hp'def
    have hpp : p = p' := by
      refine primes_eq T O hind p p' (Ideal.comap_mono (Ideal.comap_mono hle)) ?_ ?_
      · intro hb
        apply hI
        rw [eq_bot_iff, ← hb]
        intro x hx
        rw [RingHom.mem_ker] at hx
        simp [hpdef, hx]
      · rw [eq_bot_iff]
        intro t ht
        rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap] at ht
        rw [Ideal.mem_bot]
        by_contra ht0
        have hcomm : (π : O →+* A) (algebraMap T O t) = algebraMap T A t := by
          rw [IsScalarTower.algebraMap_apply T (Polynomial T) O, IsScalarTower.algebraMap_apply T (Polynomial T) A]
          exact π.commutes _
        rw [hcomm] at ht
        have hu : IsUnit (algebraMap A L (algebraMap T A t)) :=
          IsLocalization.map_units L (⟨algebraMap T A t, t, mem_nonZeroDivisors_of_ne_zero ht0, rfl⟩ :
            Algebra.algebraMapSubmonoid A (nonZeroDivisors T))
        exact hQ'p.ne_top (Ideal.eq_top_of_isUnit_mem _ ht hu)
    have hqq : Q.comap (algebraMap A L) = Q'.comap (algebraMap A L) := by
      rw [← Ideal.map_comap_of_surjective (π : O →+* A) hπ (Q.comap (algebraMap A L)),
        ← Ideal.map_comap_of_surjective (π : O →+* A) hπ (Q'.comap (algebraMap A L))]
      exact congrArg _ hpp
    rw [← IsLocalization.map_comap (Algebra.algebraMapSubmonoid A (nonZeroDivisors T)) L Q,
      ← IsLocalization.map_comap (Algebra.algebraMapSubmonoid A (nonZeroDivisors T)) L Q']
    exact congrArg (Ideal.map (algebraMap A L)) hqq
