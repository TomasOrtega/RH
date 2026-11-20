import Formalism.PieriBlockIdeals.LocalFaithfullyFlat
import Formalism.PieriBlockIdeals.PieriColumnMinors.SL2BinomialLattices
import Formalism.PieriBlockIdeals.PieriColumnMinors.ExactExponentLatticeIncl
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf

open MvPolynomial TensorProduct

noncomputable section

namespace Formalism.CohomologicalDescent.RealLocalDeltaNabla

open Formalism.GradedWeylDivisibility Formalism.UG Formalism.RankGapBounds.JumpSetsAlt Formalism.RankGapBounds.FormsTensorLocalization Formalism.CohomologicalDescent.LA Formalism.CohomologicalDescent.SL2BinomialLattices

/- English proof (translation)
Introduce `R O _ _ _ _ _ _ _ _ hinj`. Establish `: Module.IsTorsionFree R O` using `Module.isTorsionFree_iff_algebraMap_injective.2 hinj`. Establish `: Module.Flat R O` using `inferInstance`. Conclude with `Module.FaithfullyFlat.of_flat_of_isLocalHom`.
-/
theorem local_faithfully_flat_holds : LocalFaithfullyFlat := by
  intro R O _ _ _ _ _ _ _ _ hinj
  have : Module.IsTorsionFree R O := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  have : Module.Flat R O := inferInstance
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/- English proof (translation)
Introduce `O _ _ l hl hlO m hm`. Establish `hcop : Nat.Coprime l m` using `(Nat.Prime.coprime_iff_not_dvd hl).2 hm`. Establish `hb : ((l : ℤ) * Nat.gcdA l m + (m : ℤ) * Nat.gcdB l m) = 1`. Establish `h` using `Nat.gcd_eq_gcd_ab l m`. Rewrite `h` using `[hcop.gcd_eq_one, Nat.cast_one]`.

Conclude with `h.symm`. Establish `hO : ((l : O) * (Nat.gcdA l m : O) + (m : O) * (Nat.gcdB l m : O)) = 1`. Establish `h` using `congrArg (Int.cast : ℤ → O) hb`. Move the coercions through the operations in `at h`. Conclude with `h`.

Establish `hu : IsUnit ((l : O) * (Nat.gcdA l m : O) + (m : O) * (Nat.gcdB l m : O))`. Rewrite using `[hO]`. Conclude with `isUnit_one`. Break down `IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with h | h` into its components or cases. Conclude with `absurd (isUnit_of_mul_isUnit_left h) hlO`.

Conclude with `isUnit_of_mul_isUnit_left h`.
-/
theorem units_of_local_holds : UnitsOfLocal := by
  intro O _ _ l hl hlO m hm
  have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl).2 hm
  have hb : ((l : ℤ) * Nat.gcdA l m + (m : ℤ) * Nat.gcdB l m) = 1 := by
    have h := Nat.gcd_eq_gcd_ab l m
    rw [hcop.gcd_eq_one, Nat.cast_one] at h
    exact h.symm
  have hO : ((l : O) * (Nat.gcdA l m : O) + (m : O) * (Nat.gcdB l m : O)) = 1 := by
    have h := congrArg (Int.cast : ℤ → O) hb
    push_cast at h
    exact h
  have hu : IsUnit ((l : O) * (Nat.gcdA l m : O) + (m : O) * (Nat.gcdB l m : O)) := by
    rw [hO]; exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with h | h
  · exact absurd (isUnit_of_mul_isUnit_left h) hlO
  · exact isUnit_of_mul_isUnit_left h

/- English proof (translation)
Establish `hn : ¬ l ∣ z.natAbs` using `fun h => hz (Int.ofNat_dvd_left.mpr h)`. Break down `Int.natAbs_eq z with h | h` into its components or cases. Rewrite using `[h]`. Simplify using `using hu _ hn`. Rewrite using `[h]`.

Simplify using `using (hu _ hn).neg`.
-/
theorem isUnit_int_of_not_dvd (A : Type) [CommRing A] (l : ℕ) (hu : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : A))
    (z : ℤ) (hz : ¬ (l : ℤ) ∣ z) : IsUnit (z : A) := by
  have hn : ¬ l ∣ z.natAbs := fun h => hz (Int.ofNat_dvd_left.mpr h)
  rcases Int.natAbs_eq z with h | h
  · rw [h]; simpa using hu _ hn
  · rw [h]; simpa using (hu _ hn).neg

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Take `⟨m, hm, z, hz⟩` from `hd a`. Establish `h1 : ((z : ℤ) : O) = 0`. Establish `h` using `congrArg φ hz`.

Rewrite `h` using `[map_mul, ha, mul_zero, map_intCast]`. Conclude with `h.symm`. Establish `hz0 : z = 0` using `Int.cast_eq_zero.mp h1`. Establish `hma : (m : R) * a = 0` using `by rw [hz, hz0, Int.cast_zero]`. Conclude with `(hu m hm).mul_right_eq_zero.mp hma`.
-/
theorem injective_of_prime_to_units (R O : Type) [CommRing R] [CommRing O] [CharZero O] (φ : R →+* O) (l : ℕ)
    (hu : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R))
    (hd : ∀ a : R, ∃ m : ℕ, ¬ l ∣ m ∧ ∃ z : ℤ, (m : R) * a = z) : Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨m, hm, z, hz⟩ := hd a
  have h1 : ((z : ℤ) : O) = 0 := by
    have h := congrArg φ hz
    rw [map_mul, ha, mul_zero, map_intCast] at h
    exact h.symm
  have hz0 : z = 0 := Int.cast_eq_zero.mp h1
  have hma : (m : R) * a = 0 := by rw [hz, hz0, Int.cast_zero]
  exact (hu m hm).mul_right_eq_zero.mp hma

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `a ha`. Take `⟨m, hm, z, hz⟩` from `hd a`. Establish `hmO : IsUnit (m : O)` using `by simpa using (hu m hm).map φ`. Establish `hzO : IsUnit (z : O)`.

Establish `h` using `congrArg φ hz`. Rewrite `h` using `[map_mul, map_natCast, map_intCast]`. Rewrite using `[← h]`. Conclude with `hmO.mul ha`. Establish `hz' : ¬ (l : ℤ) ∣ z`.

Introduce and unpack `⟨k, rfl⟩`. Apply `hlO` to reduce the goal to its premises. Move the coercions through the operations in `at hzO`. Conclude with `isUnit_of_mul_isUnit_left hzO`. Establish `hzR : IsUnit (z : R)` using `isUnit_int_of_not_dvd R l hu z hz'`.

Rewrite `hzR` using `[← hz]`. Conclude with `isUnit_of_mul_isUnit_right hzR`.
-/
theorem isLocalHom_of_prime_to_units (R O : Type) [CommRing R] [CommRing O] (φ : R →+* O) (l : ℕ)
    (hlO : ¬ IsUnit (l : O)) (hu : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R))
    (hd : ∀ a : R, ∃ m : ℕ, ¬ l ∣ m ∧ ∃ z : ℤ, (m : R) * a = z) : IsLocalHom φ := by
  constructor
  intro a ha
  obtain ⟨m, hm, z, hz⟩ := hd a
  have hmO : IsUnit (m : O) := by simpa using (hu m hm).map φ
  have hzO : IsUnit (z : O) := by
    have h := congrArg φ hz
    rw [map_mul, map_natCast, map_intCast] at h
    rw [← h]; exact hmO.mul ha
  have hz' : ¬ (l : ℤ) ∣ z := by
    rintro ⟨k, rfl⟩
    apply hlO
    push_cast at hzO
    exact isUnit_of_mul_isUnit_left hzO
  have hzR : IsUnit (z : R) := isUnit_int_of_not_dvd R l hu z hz'
  rw [← hz] at hzR
  exact isUnit_of_mul_isUnit_right hzR

/- English proof (translation)
Introduce `O _ _ _ _ l hl hlO`. Establish `hl0 : (l : ℤ) ≠ 0` using `by exact_mod_cast hl.ne_zero`. Establish `hP : (Ideal.span {(l : ℤ)}).IsPrime` using `(Ideal.span_singleton_prime hl0).2 (Nat.prime_iff_prime_int.1 hl)`. Set `R` to `Localization.AtPrime (Ideal.span {(l : ℤ)})`. Establish `hinj : Function.Injective (algebraMap ℤ R)` using `IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {(l : ℤ)}))`.

Establish `hc0 : CharZero R` using `charZero_of_injective_algebraMap hinj`. Establish `hmem : ∀ t : ℤ, t ∈ (Ideal.span {(l : ℤ)}).primeCompl ↔ ¬ (l : ℤ) ∣ t`. Introduce `t`. Rewrite using `[Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton]`. Establish `hu : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)`.

Introduce `m hm`. Establish `h1 : (m : ℤ) ∈ (Ideal.span {(l : ℤ)}).primeCompl` using `(hmem _).2 (by exact_mod_cast hm)`. Establish `h2` using `IsLocalization.map_units R (⟨(m : ℤ), h1⟩ : (Ideal.span {(l : ℤ)}).primeCompl)`. Simplify using `using h2`. Establish `hd : ∀ a : R, ∃ m : ℕ, ¬ l ∣ m ∧ ∃ z : ℤ, (m : R) * a = z`.

Introduce `a`. Take `⟨⟨z, t⟩, h1⟩` from `IsLocalization.surj (Ideal.span {(l : ℤ)}).primeCompl a`. Establish `ht` using `(hmem _).1 t.2`. Simplify using `only [eq_intCast] at h1`. Use `⟨(t : ℤ).natAbs, fun h => ht (Int.natCast_dvd.2 h), ?_⟩` and prove the remaining obligations.

Break down `Int.natAbs_eq (t : ℤ) with h | h` into its components or cases. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[← h1, mul_comm]`. Use `congr 1`. Rewrite using `[← Int.cast_natCast, ← h]`.

Use `⟨-z, ?_⟩` and prove the remaining obligations. Establish `h2 : (((t : ℤ).natAbs : ℤ) : R) = -((t : ℤ) : R)`. Rewrite using `[← Int.cast_neg]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Establish `h3 : (((t : ℤ).natAbs : ℕ) : R) = -((t : ℤ) : R)`. Rewrite using `[← Int.cast_natCast]`. Conclude with `h2`. Rewrite using `[h3, Int.cast_neg, ← h1]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hdvr : IsDiscreteValuationRing R` using `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hl0) R`. Establish `huO` using `units_of_local_holds O l hl hlO`. Establish `hg : ∀ y : (Ideal.span {(l : ℤ)}).primeCompl, IsUnit (Int.castRingHom O y)`. Introduce `y`. Rewrite using `[eq_intCast]`.

Conclude with `isUnit_int_of_not_dvd O l huO _ ((hmem _).1 y.2)`. Set `φ : R →+* O` to `IsLocalization.lift hg`. Conclude with `⟨R, inferInstance, inferInstance, hdvr, hc0, φ.toAlgebra, isLocalHom_of_prime_to_units R O φ l hlO hu hd, injective_of_prime_to_units R O φ l hu hd, hu, hd⟩`.
-/
theorem int_localisation_in_ring : ZLocInO := by
  intro O _ _ _ _ l hl hlO
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hP : (Ideal.span {(l : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hl0).2 (Nat.prime_iff_prime_int.1 hl)
  let R := Localization.AtPrime (Ideal.span {(l : ℤ)})
  have hinj : Function.Injective (algebraMap ℤ R) :=
    IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {(l : ℤ)}))
  have hc0 : CharZero R := charZero_of_injective_algebraMap hinj
  have hmem : ∀ t : ℤ, t ∈ (Ideal.span {(l : ℤ)}).primeCompl ↔ ¬ (l : ℤ) ∣ t := by
    intro t
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton]
  have hu : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R) := by
    intro m hm
    have h1 : (m : ℤ) ∈ (Ideal.span {(l : ℤ)}).primeCompl :=
      (hmem _).2 (by exact_mod_cast hm)
    have h2 := IsLocalization.map_units R (⟨(m : ℤ), h1⟩ : (Ideal.span {(l : ℤ)}).primeCompl)
    simpa using h2
  have hd : ∀ a : R, ∃ m : ℕ, ¬ l ∣ m ∧ ∃ z : ℤ, (m : R) * a = z := by
    intro a
    obtain ⟨⟨z, t⟩, h1⟩ := IsLocalization.surj (Ideal.span {(l : ℤ)}).primeCompl a
    have ht := (hmem _).1 t.2
    simp only [eq_intCast] at h1
    refine ⟨(t : ℤ).natAbs, fun h => ht (Int.natCast_dvd.2 h), ?_⟩
    rcases Int.natAbs_eq (t : ℤ) with h | h
    · refine ⟨z, ?_⟩
      rw [← h1, mul_comm]
      congr 1
      rw [← Int.cast_natCast, ← h]
    · refine ⟨-z, ?_⟩
      have h2 : (((t : ℤ).natAbs : ℤ) : R) = -((t : ℤ) : R) := by
        rw [← Int.cast_neg]
        congr 1
        omega
      have h3 : (((t : ℤ).natAbs : ℕ) : R) = -((t : ℤ) : R) := by
        rw [← Int.cast_natCast]
        exact h2
      rw [h3, Int.cast_neg, ← h1]
      ring
  have hdvr : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hl0) R
  have huO := units_of_local_holds O l hl hlO
  have hg : ∀ y : (Ideal.span {(l : ℤ)}).primeCompl, IsUnit (Int.castRingHom O y) := by
    intro y
    rw [eq_intCast]
    exact isUnit_int_of_not_dvd O l huO _ ((hmem _).1 y.2)
  let φ : R →+* O := IsLocalization.lift hg
  exact ⟨R, inferInstance, inferInstance, hdvr, hc0, φ.toAlgebra,
    isLocalHom_of_prime_to_units R O φ l hlO hu hd, injective_of_prime_to_units R O φ l hu hd, hu, hd⟩

/- English proof (translation)
Introduce `R O _ _ _ _ _ _ _ _ _ hinj l hl h1 h2 r n hn ν e`. Use `local_faithfully_flat_holds R O hinj` as an intermediate fact. Establish `h` using `lattice_baseChange_alt R O r n hn ν (l : R) e`. Rewrite `h` using `[map_natCast]`. Rewrite using `[← h]`.

Conclude with `incl_z_iff_incl_r R l hl h1 h2 r n hn ν e`.
-/
theorem lattice_incl_iff_over_int : InclZIffOver := by
  intro R O _ _ _ _ _ _ _ _ _ hinj l hl h1 h2 r n hn ν e
  have := local_faithfully_flat_holds R O hinj
  have h := lattice_baseChange_alt R O r n hn ν (l : R) e
  rw [map_natCast] at h
  rw [← h]
  exact incl_z_iff_incl_r R l hl h1 h2 r n hn ν e

/- English proof (translation)
Introduce `O _ _ _ _ l hl hlO r n hn ν e`. Take `⟨R, _, _, _, _, _, hloc, hinj, hu, hd⟩` from `int_localisation_in_ring O l hl hlO`. Conclude with `lattice_incl_iff_over_int R O hinj l hl hu hd r n hn ν e`.
-/
theorem lattice_incl_iff_ring : InclZIffO := by
  intro O _ _ _ _ l hl hlO r n hn ν e
  obtain ⟨R, _, _, _, _, _, hloc, hinj, hu, hd⟩ := int_localisation_in_ring O l hl hlO
  exact lattice_incl_iff_over_int R O hinj l hl hu hd r n hn ν e

/- English proof (translation)
Introduce `O _ _ _ _ l hl hlO r n hn ν`. Unfold `exZ`. Use `congr 1`. Use extensionality with `e`. Conclude with `lattice_incl_iff_ring O l hl hlO r n hn ν e`.
-/
theorem exponent_eq_over_ring : ExZEqO := by
  intro O _ _ _ _ l hl hlO r n hn ν
  unfold exZ
  congr 1
  ext e
  exact lattice_incl_iff_ring O l hl hlO r n hn ν e

/- English proof (translation)
Introduce `O _ r n hn ν hν`. Unfold `deltaIn`. Rewrite using `[Submodule.map_comap_subtype]`. Conclude with `inf_eq_right.mpr (Formalism.GradedWeylDivisibility.weylLeDual O r n hn ν hν)`.
-/
theorem deltaIn_map_holds : DeltaInMap := by
  intro O _ r n hn ν hν
  unfold deltaIn
  rw [Submodule.map_comap_subtype]
  exact inf_eq_right.mpr (Formalism.GradedWeylDivisibility.weylLeDual O r n hn ν hν)

/- English proof (translation)
Unfold `LatIncl`. Conclude with `⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x.1 x.2⟩`.
-/
theorem latIncl_deltaIn_iff_dual_weyl (O : Type) [CommRing O] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (t : O)
    (e : ℕ) : LatIncl t (deltaIn O r n hn ν) e ↔
      ∀ x ∈ dualWeyl O r n ν, t ^ e • x ∈ weyl O r n hn ν := by
  unfold LatIncl
  exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x.1 x.2⟩

/- English proof (translation)
The claim follows from `(latIncl_deltaIn_iff_dual_weyl O r n hn ν (l : O) e).trans (lattice_incl_iff_ring O l hl hlO r n hn ν e).symm`.
-/
theorem latIncl_iff_int_incl (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ)
    (hl : l.Prime) (hlO : ¬ IsUnit (l : O)) (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (e : ℕ) :
    LatIncl (l : O) (deltaIn O r n hn ν) e ↔ InclZ r n hn ν l e := (latIncl_deltaIn_iff_dual_weyl O r n hn ν (l : O) e).trans (lattice_incl_iff_ring O l hl hlO r n hn ν e).symm

/- English proof (translation)
Introduce `O _ _ _ _ l hl hlO r n hn ν`. Rewrite using `[exponent_eq_over_ring O l hl hlO r n hn ν]`. Unfold `Formalism.CohomologicalDescent.exactExp`. Use `congr 1`. Use extensionality with `e`.

Conclude with `(latIncl_deltaIn_iff_dual_weyl O r n hn ν (l : O) e).symm`.
-/
theorem exponent_eq_exact_holds : ExZEqExact := by
  intro O _ _ _ _ l hl hlO r n hn ν
  rw [exponent_eq_over_ring O l hl hlO r n hn ν]
  unfold Formalism.CohomologicalDescent.exactExp
  congr 1
  ext e
  exact (latIncl_deltaIn_iff_dual_weyl O r n hn ν (l : O) e).symm

/- English proof (translation)
Introduce `O _ _ _ _ l hl hlO r n hn ν hν e`. Rewrite using `[latIncl_deltaIn_iff_dual_weyl, exponent_eq_over_ring O l hl hlO r n hn ν]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `Nat.sInf_le h`.

Introduce `he`. Establish `hne : (exZ r n hn ν l) ∈ {e : ℕ | ∀ x ∈ dualWeyl O r n ν, (l : O) ^ e • x ∈ weyl O r n hn ν}` using `(lattice_incl_iff_ring O l hl hlO r n hn ν _).1 (Formalism.CohomologicalDescent.LA.exact_z_specialization r n hn ν hν l hl)`. Establish `hmem` using `Nat.sInf_mem ⟨_, hne⟩`. Introduce `x hx`. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le he`.

Rewrite using `[hk, add_comm, pow_add, mul_smul]`. Conclude with `Submodule.smul_mem _ _ (hmem x hx)`.
-/
theorem least_exponent_over_ring : ExZLeastO := by
  intro O _ _ _ _ l hl hlO r n hn ν hν e
  rw [latIncl_deltaIn_iff_dual_weyl, exponent_eq_over_ring O l hl hlO r n hn ν]
  constructor
  · intro h
    exact Nat.sInf_le h
  · intro he
    have hne : (exZ r n hn ν l) ∈
        {e : ℕ | ∀ x ∈ dualWeyl O r n ν, (l : O) ^ e • x ∈ weyl O r n hn ν} :=
      (lattice_incl_iff_ring O l hl hlO r n hn ν _).1 (Formalism.CohomologicalDescent.LA.exact_z_specialization r n hn ν hν l hl)
    have hmem := Nat.sInf_mem ⟨_, hne⟩
    intro x hx
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le he
    rw [hk, add_comm, pow_add, mul_smul]
    exact Submodule.smul_mem _ _ (hmem x hx)

section core

variable (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ) (hl : l.Prime)
  (hlO : ¬ IsUnit (l : O)) (ι : Type) [Fintype ι] (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i)
  (ν : ∀ i, Fin (n i) → ℕ) (e : ι → ℕ) (he : ∀ i, InclZ (r i) (n i) (hn i) (ν i) l (e i))

include hl hlO he

/- English proof (translation)
The claim follows from `(latIncl_iff_int_incl O l hl hlO (r i) (n i) (hn i) (ν i) (e i)).2 (he i)`.
-/
theorem latIncl_deltaIn_of_int (i : ι) : LatIncl (l : O) (deltaIn O (r i) (n i) (hn i) (ν i)) (e i) := (latIncl_iff_int_incl O l hl hlO (r i) (n i) (hn i) (ν i) (e i)).2 (he i)

/- English proof (translation)
Unfold `Delta tensSub`. Proceed by induction on `y using PiTensorProduct.induction_on with`. Consider the case `smul_tprod c a`. Establish `hmem : ∀ i, (l : O) ^ e i • a i ∈ deltaIn O (r i) (n i) (hn i) (ν i)` using `fun i => latIncl_deltaIn_of_int O l hl hlO ι r n hn ν e he i (a i)`. Establish `key : (l : O) ^ (∑ i, e i) • PiTensorProduct.tprod O a = PiTensorProduct.map (fun i => (deltaIn O (r i) (n i) (hn i) (ν i)).subtype) (PiTensorProduct.tprod O (fun i => (⟨(l : O) ^ e i • a i, hmem i⟩ : deltaIn O (r i) (n i) (hn i) (ν i))))`.

Rewrite using `[PiTensorProduct.map_tprod]`. Simplify using `only [Submodule.coe_subtype]`. Rewrite using `[MultilinearMap.map_smul_univ, Finset.prod_pow_eq_pow_sum]`. Rewrite using `[smul_comm ((l : O) ^ (∑ i, e i)) c, key]`. Conclude with `Submodule.smul_mem _ c (LinearMap.mem_range_self _ _)`.

Consider the case `add x y hx hy`. Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem _ hx hy`.
-/
theorem pow_sum_smul_mem_delta_tensor (y : Nabla O r n ν) : (l : O) ^ (∑ i, e i) • y ∈ Delta O r n hn ν := by
  unfold Delta tensSub
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c a =>
    have hmem : ∀ i, (l : O) ^ e i • a i ∈ deltaIn O (r i) (n i) (hn i) (ν i) := fun i =>
      latIncl_deltaIn_of_int O l hl hlO ι r n hn ν e he i (a i)
    have key : (l : O) ^ (∑ i, e i) • PiTensorProduct.tprod O a =
        PiTensorProduct.map (fun i => (deltaIn O (r i) (n i) (hn i) (ν i)).subtype)
          (PiTensorProduct.tprod O (fun i =>
            (⟨(l : O) ^ e i • a i, hmem i⟩ : deltaIn O (r i) (n i) (hn i) (ν i)))) := by
      rw [PiTensorProduct.map_tprod]
      simp only [Submodule.coe_subtype]
      rw [MultilinearMap.map_smul_univ, Finset.prod_pow_eq_pow_sum]
    rw [smul_comm ((l : O) ^ (∑ i, e i)) c, key]
    exact Submodule.smul_mem _ c (LinearMap.mem_range_self _ _)
  | add x y hx hy =>
    rw [smul_add]
    exact Submodule.add_mem _ hx hy

/- English proof (translation)
Establish `h1 : ∀ f ∈ AMFK O Γ K ρK, (l : O) ^ (∑ i, e i) • f ∈ formsIn Γ K ρK (Delta O r n hn ν)`. Introduce `f hf`. Unfold `formsIn`. Conclude with `⟨(AMFK O Γ K ρK).smul_mem _ hf, fun g _ => pow_sum_smul_mem_delta_tensor O l hl hlO ι r n hn ν e he (f g)⟩`. Conclude with `⟨h1, Nat.sInf_le h1⟩`.
-/
theorem pow_sum_smul_mem_forms_and_min_le (G : Type) [Group G] (Γ K : Subgroup G)
    (ρK : Representation O K (Nabla O r n ν)) :
    (∀ f ∈ AMFK O Γ K ρK, (l : O) ^ (∑ i, e i) • f ∈ formsIn Γ K ρK (Delta O r n hn ν)) ∧
    sInf {J : ℕ | ∀ f ∈ AMFK O Γ K ρK, (l : O) ^ J • f ∈ formsIn Γ K ρK (Delta O r n hn ν)} ≤
      ∑ i, e i := by
  have h1 : ∀ f ∈ AMFK O Γ K ρK, (l : O) ^ (∑ i, e i) • f ∈ formsIn Γ K ρK (Delta O r n hn ν) := by
    intro f hf
    unfold formsIn
    exact ⟨(AMFK O Γ K ρK).smul_mem _ hf, fun g _ => pow_sum_smul_mem_delta_tensor O l hl hlO ι r n hn ν e he (f g)⟩
  exact ⟨h1, Nat.sInf_le h1⟩

/- English proof (translation)
Establish `h1 : ∀ y : LocalizedModule S (AMFK O Γ K ρK), (algebraMap O T (l : O)) ^ (∑ i, e i) • y ∈ locSet S {x : AMFK O Γ K ρK | (x : G → Nabla O r n ν) ∈ formsIn Γ K ρK (Delta O r n hn ν)}`. Introduce `y`. Proceed by induction on `y using LocalizedModule.induction_on with`. Consider the case `h m s`. Use `⟨((l : O) ^ (∑ i, e i)) • m, ?_, s, ?_⟩` and prove the remaining obligations.

Conclude with `(pow_sum_smul_mem_forms_and_min_le O l hl hlO ι r n hn ν e he G Γ K ρK).1 _ m.2`. Rewrite using `[LocalizedModule.smul'_mk, ← map_pow, algebraMap_smul]`. Conclude with `⟨h1, Nat.sInf_le h1⟩`.
-/
theorem pow_sum_smul_mem_localised_forms (G : Type) [Group G] (Γ K : Subgroup G)
    (ρK : Representation O K (Nabla O r n ν))
    (T : Type) [CommRing T] [Algebra O T] [Module T (AMFK O Γ K ρK)]
    [IsScalarTower O T (AMFK O Γ K ρK)] (S : Submonoid T) :
    (∀ y : LocalizedModule S (AMFK O Γ K ρK),
        (algebraMap O T (l : O)) ^ (∑ i, e i) • y ∈
          locSet S {x : AMFK O Γ K ρK | (x : G → Nabla O r n ν) ∈
            formsIn Γ K ρK (Delta O r n hn ν)}) ∧
    sInf {J : ℕ | ∀ y : LocalizedModule S (AMFK O Γ K ρK),
        (algebraMap O T (l : O)) ^ J • y ∈
          locSet S {x : AMFK O Γ K ρK | (x : G → Nabla O r n ν) ∈
            formsIn Γ K ρK (Delta O r n hn ν)}} ≤ ∑ i, e i := by
  have h1 : ∀ y : LocalizedModule S (AMFK O Γ K ρK),
        (algebraMap O T (l : O)) ^ (∑ i, e i) • y ∈
          locSet S {x : AMFK O Γ K ρK | (x : G → Nabla O r n ν) ∈
            formsIn Γ K ρK (Delta O r n hn ν)} := by
    intro y
    induction y using LocalizedModule.induction_on with
    | h m s =>
      refine ⟨((l : O) ^ (∑ i, e i)) • m, ?_, s, ?_⟩
      · exact (pow_sum_smul_mem_forms_and_min_le O l hl hlO ι r n hn ν e he G Γ K ρK).1 _ m.2
      · rw [LocalizedModule.smul'_mk, ← map_pow, algebraMap_smul]
  exact ⟨h1, Nat.sInf_le h1⟩

end core

/- English proof (translation)
Introduce `O _ _ _ _ l hl hlO ι _ r n hn ν hν y`. Establish `he : ∀ i, InclZ (r i) (n i) (hn i) (ν i) l (exZ (r i) (n i) (hn i) (ν i) l)` using `fun i => (latIncl_iff_int_incl O l hl hlO (r i) (n i) (hn i) (ν i) _).1 ((least_exponent_over_ring O l hl hlO (r i) (n i) (hn i) (ν i) (hν i) _).2 le_rfl)`. Establish `h` using `pow_sum_smul_mem_delta_tensor O l hl hlO ι r n hn ν (fun i => exZ (r i) (n i) (hn i) (ν i) l) he y`. Unfold `exSum`. Conclude with `h`.
-/
theorem tensor_real_bound : TensorReal := by
  intro O _ _ _ _ l hl hlO ι _ r n hn ν hν y
  have he : ∀ i, InclZ (r i) (n i) (hn i) (ν i) l (exZ (r i) (n i) (hn i) (ν i) l) := fun i =>
    (latIncl_iff_int_incl O l hl hlO (r i) (n i) (hn i) (ν i) _).1
      ((least_exponent_over_ring O l hl hlO (r i) (n i) (hn i) (ν i) (hν i) _).2 le_rfl)
  have h := pow_sum_smul_mem_delta_tensor O l hl hlO ι r n hn ν (fun i => exZ (r i) (n i) (hn i) (ν i) l) he y
  unfold exSum
  exact h

/- English proof (translation)
Introduce `O _ _ _ _ l hl hlO ι _ r n hn ν hν G _ Γ K ρK`. Establish `he : ∀ i, InclZ (r i) (n i) (hn i) (ν i) l (exZ (r i) (n i) (hn i) (ν i) l)` using `fun i => (latIncl_iff_int_incl O l hl hlO (r i) (n i) (hn i) (ν i) _).1 ((least_exponent_over_ring O l hl hlO (r i) (n i) (hn i) (ν i) (hν i) _).2 le_rfl)`. Establish `h` using `pow_sum_smul_mem_forms_and_min_le O l hl hlO ι r n hn ν (fun i => exZ (r i) (n i) (hn i) (ν i) l) he G Γ K ρK`. Unfold `exSum`. Conclude with `h`.
-/
theorem real_lattice_bound : TheoremAReal := by
  intro O _ _ _ _ l hl hlO ι _ r n hn ν hν G _ Γ K ρK
  have he : ∀ i, InclZ (r i) (n i) (hn i) (ν i) l (exZ (r i) (n i) (hn i) (ν i) l) := fun i =>
    (latIncl_iff_int_incl O l hl hlO (r i) (n i) (hn i) (ν i) _).1
      ((least_exponent_over_ring O l hl hlO (r i) (n i) (hn i) (ν i) (hν i) _).2 le_rfl)
  have h := pow_sum_smul_mem_forms_and_min_le O l hl hlO ι r n hn ν (fun i => exZ (r i) (n i) (hn i) (ν i) l) he G Γ K ρK
  unfold exSum
  exact h

/- English proof (translation)
Introduce `O _ _ _ _ l hl hlO ι _ r n hn ν hν G _ Γ K ρK T _ _ _ _ S`. Establish `he : ∀ i, InclZ (r i) (n i) (hn i) (ν i) l (exZ (r i) (n i) (hn i) (ν i) l)` using `fun i => (latIncl_iff_int_incl O l hl hlO (r i) (n i) (hn i) (ν i) _).1 ((least_exponent_over_ring O l hl hlO (r i) (n i) (hn i) (ν i) (hν i) _).2 le_rfl)`. Establish `h` using `pow_sum_smul_mem_localised_forms O l hl hlO ι r n hn ν (fun i => exZ (r i) (n i) (hn i) (ν i) l) he G Γ K ρK T S`. Unfold `exSum`. Conclude with `h`.
-/
theorem real_localisation_bound : TheoremARealLoc := by
  intro O _ _ _ _ l hl hlO ι _ r n hn ν hν G _ Γ K ρK T _ _ _ _ S
  have he : ∀ i, InclZ (r i) (n i) (hn i) (ν i) l (exZ (r i) (n i) (hn i) (ν i) l) := fun i =>
    (latIncl_iff_int_incl O l hl hlO (r i) (n i) (hn i) (ν i) _).1
      ((least_exponent_over_ring O l hl hlO (r i) (n i) (hn i) (ν i) (hν i) _).2 le_rfl)
  have h := pow_sum_smul_mem_localised_forms O l hl hlO ι r n hn ν (fun i => exZ (r i) (n i) (hn i) (ν i) l) he G Γ K ρK T S
  unfold exSum
  exact h

/- English proof (translation)
Introduce `hAZ ι _ r n hn ν hν l hl`. Unfold `exSum eSum`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i _`. Conclude with `Nat.sInf_le (hAZ (r i) (n i) (hn i) (ν i) (hν i) l hl)`.
-/
theorem exponent_sum_le_holds : ExSumLe := by
  intro hAZ ι _ r n hn ν hν l hl
  unfold exSum eSum
  apply Finset.sum_le_sum
  intro i _
  exact Nat.sInf_le (hAZ (r i) (n i) (hn i) (ν i) (hν i) l hl)

/- English proof (translation)
Introduce `hAZ O _ _ _ _ l hl hlO ι _ r n hn ν hν G _ Γ K ρK`. Establish `he` using `fun i => hAZ (r i) (n i) (hn i) (ν i) (hν i) l hl`. Establish `h` using `pow_sum_smul_mem_forms_and_min_le O l hl hlO ι r n hn ν _ he G Γ K ρK`. Unfold `eSum`. Conclude with `h`.
-/
theorem real_exponent_bound : TheoremARealE := by
  intro hAZ O _ _ _ _ l hl hlO ι _ r n hn ν hν G _ Γ K ρK
  have he := fun i => hAZ (r i) (n i) (hn i) (ν i) (hν i) l hl
  have h := pow_sum_smul_mem_forms_and_min_le O l hl hlO ι r n hn ν _ he G Γ K ρK
  unfold eSum
  exact h

/- English proof (translation)
Introduce `hAZ O _ _ _ _ l hl hlO ι _ r n hn ν hν G _ Γ K ρK T _ _ _ _ S`. Establish `he` using `fun i => hAZ (r i) (n i) (hn i) (ν i) (hν i) l hl`. Establish `h` using `pow_sum_smul_mem_localised_forms O l hl hlO ι r n hn ν _ he G Γ K ρK T S`. Unfold `eSum`. Conclude with `h`.
-/
theorem real_localisation_exponent_bound : TheoremARealLocE := by
  intro hAZ O _ _ _ _ l hl hlO ι _ r n hn ν hν G _ Γ K ρK T _ _ _ _ S
  have he := fun i => hAZ (r i) (n i) (hn i) (ν i) (hν i) l hl
  have h := pow_sum_smul_mem_localised_forms O l hl hlO ι r n hn ν _ he G Γ K ρK T S
  unfold eSum
  exact h

/- English proof (translation)
Introduce `O _ _ _ _ l hl hlO ι _ r n hn ν hr hν G _ Γ K ρK`. Establish `he` using `fun i => Formalism.CohomologicalDescent.LA.lattice_z_rank_le_two (r i) (n i) (hn i) (hr i) (ν i) (hν i) l hl`. Establish `h` using `pow_sum_smul_mem_forms_and_min_le O l hl hlO ι r n hn ν _ he G Γ K ρK`. Unfold `eSum`. Conclude with `h`.
-/
theorem real_lattice_bound_le_two : TheoremARealLe2 := by
  intro O _ _ _ _ l hl hlO ι _ r n hn ν hr hν G _ Γ K ρK
  have he := fun i =>
    Formalism.CohomologicalDescent.LA.lattice_z_rank_le_two (r i) (n i) (hn i) (hr i) (ν i) (hν i) l hl
  have h := pow_sum_smul_mem_forms_and_min_le O l hl hlO ι r n hn ν _ he G Γ K ρK
  unfold eSum
  exact h

/- English proof (translation)
Introduce `O _ _ _ _ l hl hlO ι _ r n hn ν hr hν G _ Γ K ρK T _ _ _ _ S`. Establish `he` using `fun i => Formalism.CohomologicalDescent.LA.lattice_z_rank_le_two (r i) (n i) (hn i) (hr i) (ν i) (hν i) l hl`. Establish `h` using `pow_sum_smul_mem_localised_forms O l hl hlO ι r n hn ν _ he G Γ K ρK T S`. Unfold `eSum`. Conclude with `h`.
-/
theorem real_localisation_bound_le_two : TheoremARealLocLe2 := by
  intro O _ _ _ _ l hl hlO ι _ r n hn ν hr hν G _ Γ K ρK T _ _ _ _ S
  have he := fun i =>
    Formalism.CohomologicalDescent.LA.lattice_z_rank_le_two (r i) (n i) (hn i) (hr i) (ν i) (hν i) l hl
  have h := pow_sum_smul_mem_localised_forms O l hl hlO ι r n hn ν _ he G Γ K ρK T S
  unfold eSum
  exact h

/- English proof (translation)
Introduce `p _`. Use `⟨inferInstance, inferInstance, inferInstance, ?_⟩` and prove the remaining obligations. Rewrite using `[PadicInt.isUnit_iff, PadicInt.norm_p, inv_eq_one]`. Conclude with `(Fact.out : p.Prime).one_lt.ne'` after adjusting the coercions.
-/
theorem padic_coefficient_bound : PadicCoeff := by
  intro p _
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  rw [PadicInt.isUnit_iff, PadicInt.norm_p, inv_eq_one]
  exact_mod_cast (Fact.out : p.Prime).one_lt.ne'

/- English proof (translation)
Introduce `O₀ O _ _ _ _ _ hinj l hl`. Use `⟨charZero_of_injective_algebraMap hinj, fun h => hl ?_⟩` and prove the remaining obligations. Establish `h' : IsUnit (algebraMap O₀ O (l : O₀))` using `by simpa using h`. Conclude with `IsUnit.of_map (algebraMap O₀ O) _ h'`.
-/
theorem coefficient_over_holds : CoeffOver := by
  intro O₀ O _ _ _ _ _ hinj l hl
  refine ⟨charZero_of_injective_algebraMap hinj, fun h => hl ?_⟩
  have h' : IsUnit (algebraMap O₀ O (l : O₀)) := by simpa using h
  exact IsUnit.of_map (algebraMap O₀ O) _ h'

/- English proof (translation)
Introduce `p _ O _ _ _ hinj`. Establish `hloc : IsLocalHom (algebraMap ℤ_[p] O)` using `(algebraMap_isIntegral_iff.mpr inferInstance).isLocalHom hinj`. Take `⟨h1, h2⟩` from `coefficient_over_holds ℤ_[p] O hinj p PadicInt.p_nonunit`. Conclude with `⟨hloc, h1, h2⟩`.
-/
theorem finite_over_padic_holds : FiniteOverPadic := by
  intro p _ O _ _ _ hinj
  have hloc : IsLocalHom (algebraMap ℤ_[p] O) :=
    (algebraMap_isIntegral_iff.mpr inferInstance).isLocalHom hinj
  obtain ⟨h1, h2⟩ := coefficient_over_holds ℤ_[p] O hinj p PadicInt.p_nonunit
  exact ⟨hloc, h1, h2⟩

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ hinj ι _ r n hn ν hν G _ Γ K ρK`. Take `⟨hloc, hchar, hlO⟩` from `finite_over_padic_holds l O hinj`. Establish `hl : l.Prime` using `Fact.out`. Conclude with `⟨fun i => exponent_eq_exact_holds O l hl hlO (r i) (n i) (hn i) (ν i), (real_lattice_bound O l hl hlO ι r n hn ν hν G Γ K ρK).1, fun hAZ => (real_exponent_bound hAZ O l hl hlO ι r n hn ν hν G Γ K ρK).1⟩`.
-/
theorem padic_lattice_bound : TheoremAPadic := by
  intro l _ O _ _ _ _ _ hinj ι _ r n hn ν hν G _ Γ K ρK
  obtain ⟨hloc, hchar, hlO⟩ := finite_over_padic_holds l O hinj
  have hl : l.Prime := Fact.out
  exact ⟨fun i => exponent_eq_exact_holds O l hl hlO (r i) (n i) (hn i) (ν i),
    (real_lattice_bound O l hl hlO ι r n hn ν hν G Γ K ρK).1,
    fun hAZ => (real_exponent_bound hAZ O l hl hlO ι r n hn ν hν G Γ K ρK).1⟩

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ hinj ι _ r n hn ν hν G _ Γ K ρK T _ _ _ _ S`. Take `⟨hloc, hchar, hlO⟩` from `finite_over_padic_holds l O hinj`. Establish `hl : l.Prime` using `Fact.out`. Conclude with `⟨(real_localisation_bound O l hl hlO ι r n hn ν hν G Γ K ρK T S).1, fun hAZ => (real_localisation_exponent_bound hAZ O l hl hlO ι r n hn ν hν G Γ K ρK T S).1⟩`.
-/
theorem padic_localisation_bound : TheoremAPadicLoc := by
  intro l _ O _ _ _ _ _ hinj ι _ r n hn ν hν G _ Γ K ρK T _ _ _ _ S
  obtain ⟨hloc, hchar, hlO⟩ := finite_over_padic_holds l O hinj
  have hl : l.Prime := Fact.out
  exact ⟨(real_localisation_bound O l hl hlO ι r n hn ν hν G Γ K ρK T S).1,
    fun hAZ => (real_localisation_exponent_bound hAZ O l hl hlO ι r n hn ν hν G Γ K ρK T S).1⟩

/- English proof (translation)
Proceed by induction on `z using PiTensorProduct.induction_on with`. Consider the case `smul_tprod c a`. Rewrite using `[map_smul, map_smul, PiTensorProduct.map_tprod, PiTensorProduct.subsingletonEquiv_apply_tprod]`. Conclude with `Submodule.smul_mem _ c (a ()).2`. Consider the case `add x y hx hy`.

Rewrite using `[map_add, map_add]`. Conclude with `Submodule.add_mem _ hx hy`.
-/
theorem unit_tensor_mem_deltaIn (O : Type) [CommRing O] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ)
    (z : ⨂[O] _ : Unit, ↥(deltaIn O r n hn ν)) :
    PiTensorProduct.subsingletonEquiv (R := O) (s := fun _ : Unit => ↥(dualWeyl O r n ν)) ()
      (PiTensorProduct.map (fun _ : Unit => (deltaIn O r n hn ν).subtype) z) ∈
        deltaIn O r n hn ν := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c a =>
    rw [map_smul, map_smul, PiTensorProduct.map_tprod, PiTensorProduct.subsingletonEquiv_apply_tprod]
    exact Submodule.smul_mem _ c (a ()).2
  | add x y hx hy =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ hx hy

/- English proof (translation)
Introduce `O _ _ _ _ l hl hlO r n hn ν hν`. Unfold `exZ`. Use `congr 1`. Use extensionality with `J`. Simplify using `only [Set.mem_ofPred_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce `H`. Rewrite using `[← latIncl_iff_int_incl O l hl hlO]`. Introduce `x`. Establish `hf : (fun _ : Unit => PiTensorProduct.tprod O (fun _ : Unit => x)) ∈ AMFK O (⊥ : Subgroup Unit) (⊥ : Subgroup Unit) (1 : Representation O (⊥ : Subgroup Unit) (Nabla O (ι` using `Unit) (fun _ => r) (fun _ => n) (fun _ => ν))) := by`.

Introduce `γ g κ`. Both sides reduce to the same expression. Take `⟨z, hz⟩` from `(H _ hf).2 () (Set.mem_univ _)`. Establish `h1` using `unit_tensor_mem_deltaIn O r n hn ν z`. Establish `h2 : PiTensorProduct.map (fun _ : Unit => (deltaIn O r n hn ν).subtype) z = (l : O) ^ J • PiTensorProduct.tprod O (fun _ : Unit => x)` using `hz`.

Rewrite `h1` using `[h2, map_smul, PiTensorProduct.subsingletonEquiv_apply_tprod]`. Conclude with `h1`. Introduce `H`. Establish `h` using `(pow_sum_smul_mem_forms_and_min_le O l hl hlO Unit (fun _ => r) (fun _ => n) (fun _ => hn) (fun _ => ν) (fun _ => J) (fun _ => H) Unit ⊥ ⊥ 1).1`. Simplify using `using h`.
-/
theorem sharp_bound_exponent_one : TheoremASharpOne := by
  intro O _ _ _ _ l hl hlO r n hn ν hν
  unfold exZ
  congr 1
  ext J
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro H
    rw [← latIncl_iff_int_incl O l hl hlO]
    intro x
    have hf : (fun _ : Unit => PiTensorProduct.tprod O (fun _ : Unit => x)) ∈
        AMFK O (⊥ : Subgroup Unit) (⊥ : Subgroup Unit)
          (1 : Representation O (⊥ : Subgroup Unit)
            (Nabla O (ι := Unit) (fun _ => r) (fun _ => n) (fun _ => ν))) := by
      intro γ g κ
      rfl
    obtain ⟨z, hz⟩ := (H _ hf).2 () (Set.mem_univ _)
    have h1 := unit_tensor_mem_deltaIn O r n hn ν z
    have h2 : PiTensorProduct.map (fun _ : Unit => (deltaIn O r n hn ν).subtype) z =
        (l : O) ^ J • PiTensorProduct.tprod O (fun _ : Unit => x) := hz
    rw [h2, map_smul, PiTensorProduct.subsingletonEquiv_apply_tprod] at h1
    exact h1
  · intro H
    have h := (pow_sum_smul_mem_forms_and_min_le O l hl hlO Unit (fun _ => r) (fun _ => n) (fun _ => hn) (fun _ => ν)
      (fun _ => J) (fun _ => H) Unit ⊥ ⊥ 1).1
    simpa using h

/- English proof (translation)
Unfold `Formalism.RankGapBounds.JumpSetsAlt.maxVal`. Apply `le_antisymm` to reduce the goal to its premises. Apply `Finset.sup_le` to reduce the goal to its premises. Introduce `i hi`. Establish `hi' : i < 4` using `Finset.mem_range.mp hi`.

Use `interval_cases i`. Simplify using `[show Nat.choose 3 0 = 1 by decide]`. Simplify using `[show Nat.choose 3 1 = 3 by decide, Nat.Prime.factorization_self Nat.prime_three]`. Simplify using `[show Nat.choose 3 2 = 3 by decide, Nat.Prime.factorization_self Nat.prime_three]`. Simplify using `[show Nat.choose 3 3 = 1 by decide]`.

Establish `h1 : (Nat.choose 3 1).factorization 3 = 1`. Rewrite using `[Nat.choose_one_right]`. Conclude with `Nat.Prime.factorization_self Nat.prime_three`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem maxVal_three_three : Formalism.RankGapBounds.JumpSetsAlt.maxVal 3 3 = 1 := by
  unfold Formalism.RankGapBounds.JumpSetsAlt.maxVal
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    have hi' : i < 4 := Finset.mem_range.mp hi
    interval_cases i
    · simp [show Nat.choose 3 0 = 1 by decide]
    · simp [show Nat.choose 3 1 = 3 by decide, Nat.Prime.factorization_self Nat.prime_three]
    · simp [show Nat.choose 3 2 = 3 by decide, Nat.Prime.factorization_self Nat.prime_three]
    · simp [show Nat.choose 3 3 = 1 by decide]
  · have h1 : (Nat.choose 3 1).factorization 3 = 1 := by
      rw [Nat.choose_one_right]; exact Nat.Prime.factorization_self Nat.prime_three
    calc 1 = (Nat.choose 3 1).factorization 3 := h1.symm
      _ ≤ _ := Finset.le_sup (f := fun i => (Nat.choose 3 i).factorization 3)
          (Finset.mem_range.mpr (by norm_num))

/- English proof (translation)
Establish `hp : Nat.Prime 3` using `Nat.prime_three`. Establish `hu : ¬ IsUnit ((3 : ℕ) : ℤ_[3])` using `PadicInt.p_nonunit`. Establish `he : eExp (lamU 2 1 (fun _ => 3)) 3 = 1` using `by rw [la_eExp_r2n1, maxVal_three_three]`. Establish `hx : exZ 2 1 (by norm_num) (fun _ => 3) 3 = 1` using `by rw [exact_z_rank_two_one_column _ _ 3 hp, he]`. Establish `ha : Antitone (fun _ : Fin 1 => 3)` using `antitone_const`.

Use `⟨hx, he, ?_, ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hcon push Not at hcon`. Establish `h0` using `(least_exponent_over_ring ℤ_[3] 3 hp hu 2 1 (by norm_num) (fun _ => 3) ha 0).1 (fun x => by`. Rewrite using `[pow_zero, one_smul]`. Conclude with `hcon x.1 x.2)`.

Use linear arithmetic over natural numbers and integers. Introduce `x hx'`. Establish `h1` using `(least_exponent_over_ring ℤ_[3] 3 hp hu 2 1 (by norm_num) (fun _ => 3) ha 1).2 hx.le ⟨x, hx'⟩`. Establish `h2 : ((3 : ℕ) : ℤ_[3]) ^ 1 • x ∈ weyl ℤ_[3] 2 1 (by norm_num) (fun _ => 3)` using `h1`. Simplify using `using h2`.

Introduce `y`. Establish `h` using `tensor_real_bound ℤ_[3] 3 hp hu (Fin 2) (fun _ => 2) (fun _ => 1) (fun _ => by norm_num) (fun _ _ => 3) (fun _ => ha) y`. Establish `hs : exSum (ι` using `Fin 2) (fun _ => 2) (fun _ => 1) (fun _ => by norm_num) (fun _ _ => 3) 3 = 2 := by`. Unfold `exSum`. Simplify using `[hx]`.

Rewrite `h` using `[hs]`. Simplify using `using h`.
-/
theorem tensor_instance_three : Instance3 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hu : ¬ IsUnit ((3 : ℕ) : ℤ_[3]) := PadicInt.p_nonunit
  have he : eExp (lamU 2 1 (fun _ => 3)) 3 = 1 := by rw [la_eExp_r2n1, maxVal_three_three]
  have hx : exZ 2 1 (by norm_num) (fun _ => 3) 3 = 1 := by rw [exact_z_rank_two_one_column _ _ 3 hp, he]
  have ha : Antitone (fun _ : Fin 1 => 3) := antitone_const
  refine ⟨hx, he, ?_, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    have h0 := (least_exponent_over_ring ℤ_[3] 3 hp hu 2 1 (by norm_num) (fun _ => 3) ha 0).1
      (fun x => by
        rw [pow_zero, one_smul]
        exact hcon x.1 x.2)
    omega
  · intro x hx'
    have h1 := (least_exponent_over_ring ℤ_[3] 3 hp hu 2 1 (by norm_num) (fun _ => 3) ha 1).2 hx.le ⟨x, hx'⟩
    have h2 : ((3 : ℕ) : ℤ_[3]) ^ 1 • x ∈ weyl ℤ_[3] 2 1 (by norm_num) (fun _ => 3) := h1
    simpa using h2
  · intro y
    have h := tensor_real_bound ℤ_[3] 3 hp hu (Fin 2) (fun _ => 2) (fun _ => 1)
      (fun _ => by norm_num) (fun _ _ => 3) (fun _ => ha) y
    have hs : exSum (ι := Fin 2) (fun _ => 2) (fun _ => 1) (fun _ => by norm_num) (fun _ _ => 3) 3
        = 2 := by
      unfold exSum
      simp [hx]
    rw [hs] at h
    simpa using h

/- English proof (translation)
Introduce `O _ ι r n ν g a`. Conclude with `⟨PiTensorProduct.map_tprod (fun i => dualWeylRep O (r i) (n i) (ν i) (g i)) a, fun i => rfl⟩`.
-/
theorem nabla_rep_tensor_product : NablaRepTprod := by
  intro O _ ι r n ν g a
  exact ⟨PiTensorProduct.map_tprod (fun i => dualWeylRep O (r i) (n i) (ν i) (g i)) a, fun i => rfl⟩

/- English proof (translation)
Introduce `O _ r n hn ν g x hx`. Conclude with `Formalism.UG.P.weyl_module_GL_stable O r n hn ν g _ hx`.
-/
theorem delta_lattice_stable_holds : DeltaInStable := by
  intro O _ r n hn ν g x hx
  exact Formalism.UG.P.weyl_module_GL_stable O r n hn ν g _ hx

/- English proof (translation)
Unfold `Delta tensSub at hx ⊢`. Take `⟨z, rfl⟩` from `LinearMap.mem_range.mp hx`. Use `clear hx`. Proceed by induction on `z using PiTensorProduct.induction_on with`. Consider the case `smul_tprod c a`.

Rewrite using `[map_smul, map_smul, PiTensorProduct.map_tprod, (nabla_rep_tensor_product O ι r n ν g _).1]`. Use `Submodule.smul_mem _ c (LinearMap.mem_range.mpr ⟨PiTensorProduct.tprod O (fun i => (⟨dualWeylRep O (r i) (n i) (ν i) (g i) (a i), delta_lattice_stable_holds O (r i) (n i) (hn i) (ν i) (g i) _ (a i).2⟩ : deltaIn O (r i) (n i) (hn i) (ν i))), ?_⟩)` and prove the remaining obligations. Rewrite using `[PiTensorProduct.map_tprod]`. Apply the tactic sequence `all_goals rfl`. Consider the case `add x y ihx ihy`.

Rewrite using `[map_add, map_add]`. Conclude with `Submodule.add_mem _ ihx ihy`.
-/
theorem nablaRep_mem_delta (O : Type) [CommRing O] (ι : Type) (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i)
    (ν : ∀ i, Fin (n i) → ℕ) (g : ∀ i, Matrix.GeneralLinearGroup (Fin (r i)) O)
    (x : Nabla O r n ν) (hx : x ∈ Delta O r n hn ν) : nablaRep O r n ν g x ∈ Delta O r n hn ν := by
  unfold Delta tensSub at hx ⊢
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hx
  clear hx
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c a =>
    rw [map_smul, map_smul, PiTensorProduct.map_tprod, (nabla_rep_tensor_product O ι r n ν g _).1]
    refine Submodule.smul_mem _ c (LinearMap.mem_range.mpr ⟨PiTensorProduct.tprod O (fun i =>
      (⟨dualWeylRep O (r i) (n i) (ν i) (g i) (a i),
        delta_lattice_stable_holds O (r i) (n i) (hn i) (ν i) (g i) _ (a i).2⟩ :
          deltaIn O (r i) (n i) (hn i) (ν i))), ?_⟩)
    rw [PiTensorProduct.map_tprod]
    all_goals rfl
  | add x y ihx ihy =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ ihx ihy

/- English proof (translation)
Introduce `O _ ι r n hn ν`. Use `⟨fun g x hx => nablaRep_mem_delta O ι r n hn ν g x hx, fun G _ K φ => ?_⟩` and prove the remaining obligations. Unfold `IsStable levelRep`. Introduce `k x hx`. Conclude with `nablaRep_mem_delta O ι r n hn ν (φ k) x hx`.
-/
theorem delta_stable_holds : DeltaStable := by
  intro O _ ι r n hn ν
  refine ⟨fun g x hx => nablaRep_mem_delta O ι r n hn ν g x hx, fun G _ K φ => ?_⟩
  unfold IsStable levelRep
  intro k x hx
  exact nablaRep_mem_delta O ι r n hn ν (φ k) x hx

/- English proof (translation)
Introduce `O _ _ _ _ l hl hlO ι _ r n hn ν hν G _ Γ K φ`. Establish `hU` using `(delta_stable_holds O ι r n hn ν).2 G K φ`. Conclude with `⟨⟨hU, forms_in_equivalence_holds G Γ K O _ (levelRep O r n ν K φ) (Delta O r n hn ν) hU⟩, (real_lattice_bound O l hl hlO ι r n hn ν hν G Γ K _).1, fun hA => (real_exponent_bound hA O l hl hlO ι r n hn ν hν G Γ K _).1⟩`.
-/
theorem general_linear_lattice_bound : TheoremAGL := by
  intro O _ _ _ _ l hl hlO ι _ r n hn ν hν G _ Γ K φ
  have hU := (delta_stable_holds O ι r n hn ν).2 G K φ
  exact ⟨⟨hU, forms_in_equivalence_holds G Γ K O _ (levelRep O r n ν K φ) (Delta O r n hn ν) hU⟩,
    (real_lattice_bound O l hl hlO ι r n hn ν hν G Γ K _).1,
    fun hA => (real_exponent_bound hA O l hl hlO ι r n hn ν hν G Γ K _).1⟩

/- English proof (translation)
Establish `h1 : Module.Finite ℤ (dualWeyl ℤ r n ν)` using `Module.Finite.iff_fg.2 (la_dualWeyl_fg r n ν)`. Establish `h2 : Module.Finite ℤ (weyl ℤ r n hn ν)` using `Module.Finite.of_injective (Submodule.inclusion (weylLeDual ℤ r n hn ν hν)) (Submodule.inclusion_injective _)`. Use `infer_instance`.
-/
theorem weyl_int_module_free (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    Module.Free ℤ (weyl ℤ r n hn ν) := by
  have h1 : Module.Finite ℤ (dualWeyl ℤ r n ν) := Module.Finite.iff_fg.2 (la_dualWeyl_fg r n ν)
  have h2 : Module.Finite ℤ (weyl ℤ r n hn ν) :=
    Module.Finite.of_injective (Submodule.inclusion (weylLeDual ℤ r n hn ν hν))
      (Submodule.inclusion_injective _)
  infer_instance

/- English proof (translation)
Introduce `O _ _ _ r n hn ν hν`. Use `weyl_int_module_free r n hn ν hν` as an intermediate fact. Establish `htf : Module.IsTorsionFree ℤ O` using `Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.injective_int (algebraMap ℤ O))`. Establish `hfl : Module.Flat ℤ O` using `inferInstance`. Establish `hinj` using `flat_baseChange_injective ℤ O _ (weyl ℤ r n hn ν)`.

Establish `e1 : (O ⊗[ℤ] ↥(weyl ℤ r n hn ν)) ≃ₗ[O] ↥((weyl ℤ r n hn ν).baseChange O)` using `LinearEquiv.ofInjective _ hinj`. Establish `e2 : ↥((weyl ℤ r n hn ν).baseChange O) ≃ₗ[O] ↥(((weyl ℤ r n hn ν).baseChange O).map (polyBC ℤ O r n).toLinearMap)` using `(polyBC ℤ O r n).submoduleMap _`. Rewrite `e2` using `[(lattice_tensor ℤ O r n hn ν).1]`. Establish `e3 : ↥(deltaIn O r n hn ν) ≃ₗ[O] ↥(weyl O r n hn ν)` using `Submodule.comapSubtypeEquivOfLe (weylLeDual O r n hn ν hν)`. Conclude with `Module.Free.of_equiv ((e1.trans e2).trans e3.symm)`.
-/
theorem delta_lattice_free : DeltaFree := by
  intro O _ _ _ r n hn ν hν
  have := weyl_int_module_free r n hn ν hν
  have htf : Module.IsTorsionFree ℤ O :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.injective_int (algebraMap ℤ O))
  have hfl : Module.Flat ℤ O := inferInstance
  have hinj := flat_baseChange_injective ℤ O _ (weyl ℤ r n hn ν)
  have e1 : (O ⊗[ℤ] ↥(weyl ℤ r n hn ν)) ≃ₗ[O] ↥((weyl ℤ r n hn ν).baseChange O) :=
    LinearEquiv.ofInjective _ hinj
  have e2 : ↥((weyl ℤ r n hn ν).baseChange O) ≃ₗ[O]
      ↥(((weyl ℤ r n hn ν).baseChange O).map (polyBC ℤ O r n).toLinearMap) :=
    (polyBC ℤ O r n).submoduleMap _
  rw [(lattice_tensor ℤ O r n hn ν).1] at e2
  have e3 : ↥(deltaIn O r n hn ν) ≃ₗ[O] ↥(weyl O r n hn ν) :=
    Submodule.comapSubtypeEquivOfLe (weylLeDual O r n hn ν hν)
  exact Module.Free.of_equiv ((e1.trans e2).trans e3.symm)

/- English proof (translation)
Introduce `O _ _ _ _ l hl hlO ι _ r n hn ν hν`. Establish `hfree : ∀ i, Module.Free O (deltaIn O (r i) (n i) (hn i) (ν i))` using `fun i => delta_lattice_free O (r i) (n i) (hn i) (ν i) (hν i)`. Establish `hF : Module.Free O (⨂[O] i, ↥(deltaIn O (r i) (n i) (hn i) (ν i)))` using `Module.Free.of_basis (Basis.piTensorProduct fun i => Module.Free.chooseBasis O (deltaIn O (r i) (n i) (hn i) (ν i)))`. Establish `hlat : ∀ i, LatIncl (l : O) (deltaIn O (r i) (n i) (hn i) (ν i)) (exZ (r i) (n i) (hn i) (ν i) l)` using `latIncl_deltaIn_of_int O l hl hlO ι r n hn ν _ (fun i => exact_z_specialization (r i) (n i) (hn i) (ν i) (hν i) l hl)`. Set `ψ : ∀ i, ↥(dualWeyl O (r i) (n i) (ν i)) →ₗ[O] ↥(deltaIn O (r i) (n i) (hn i) (ν i))` to `fun i => LinearMap.codRestrict _ ((l : O) ^ exZ (r i) (n i) (hn i) (ν i) l • LinearMap.id) (fun c => hlat i c)`.

Establish `key : ∀ z : ⨂[O] i, ↥(deltaIn O (r i) (n i) (hn i) (ν i)), PiTensorProduct.map ψ (PiTensorProduct.map (fun i => (deltaIn O (r i) (n i) (hn i) (ν i)).subtype) z) = (l : O) ^ exSum r n hn ν l • z`. Introduce `z`. Proceed by induction on `z using PiTensorProduct.induction_on with`. Consider the case `smul_tprod c a`. Rewrite using `[map_smul, map_smul, PiTensorProduct.map_tprod, PiTensorProduct.map_tprod, smul_comm]`.

Use `congr 1`. Establish `h2 : (fun i => ψ i ((deltaIn O (r i) (n i) (hn i) (ν i)).subtype (a i))) = fun i => (l : O) ^ exZ (r i) (n i) (hn i) (ν i) l • a i`. Use function extensionality and compare the values at `i`. Apply `Subtype.ext` to reduce the goal to its premises. Both sides reduce to the same expression.

Rewrite using `[h2, MultilinearMap.map_smul_univ, Finset.prod_pow_eq_pow_sum]`. Both sides reduce to the same expression. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `z hz`.

Establish `h3` using `key z`. Rewrite `h3` using `[hz, map_zero]`. Establish `hl0 : (l : O) ^ exSum r n hn ν l ≠ 0` using `pow_ne_zero _ (by exact_mod_cast hl.ne_zero)`. Conclude with `(smul_eq_zero.1 h3.symm).resolve_left hl0`.
-/
theorem tensor_injective_holds : TensorInj := by
  intro O _ _ _ _ l hl hlO ι _ r n hn ν hν
  classical
  have hfree : ∀ i, Module.Free O (deltaIn O (r i) (n i) (hn i) (ν i)) :=
    fun i => delta_lattice_free O (r i) (n i) (hn i) (ν i) (hν i)
  have hF : Module.Free O (⨂[O] i, ↥(deltaIn O (r i) (n i) (hn i) (ν i))) :=
    Module.Free.of_basis (Basis.piTensorProduct fun i =>
      Module.Free.chooseBasis O (deltaIn O (r i) (n i) (hn i) (ν i)))
  have hlat : ∀ i, LatIncl (l : O) (deltaIn O (r i) (n i) (hn i) (ν i))
      (exZ (r i) (n i) (hn i) (ν i) l) :=
    latIncl_deltaIn_of_int O l hl hlO ι r n hn ν _
      (fun i => exact_z_specialization (r i) (n i) (hn i) (ν i) (hν i) l hl)
  let ψ : ∀ i, ↥(dualWeyl O (r i) (n i) (ν i)) →ₗ[O] ↥(deltaIn O (r i) (n i) (hn i) (ν i)) :=
    fun i => LinearMap.codRestrict _
      ((l : O) ^ exZ (r i) (n i) (hn i) (ν i) l • LinearMap.id) (fun c => hlat i c)
  have key : ∀ z : ⨂[O] i, ↥(deltaIn O (r i) (n i) (hn i) (ν i)),
      PiTensorProduct.map ψ
        (PiTensorProduct.map (fun i => (deltaIn O (r i) (n i) (hn i) (ν i)).subtype) z) =
      (l : O) ^ exSum r n hn ν l • z := by
    intro z
    induction z using PiTensorProduct.induction_on with
    | smul_tprod c a =>
      rw [map_smul, map_smul, PiTensorProduct.map_tprod, PiTensorProduct.map_tprod, smul_comm]
      congr 1
      have h2 : (fun i => ψ i ((deltaIn O (r i) (n i) (hn i) (ν i)).subtype (a i))) =
          fun i => (l : O) ^ exZ (r i) (n i) (hn i) (ν i) l • a i := by
        funext i
        apply Subtype.ext
        rfl
      rw [h2, MultilinearMap.map_smul_univ, Finset.prod_pow_eq_pow_sum]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]
  rw [injective_iff_map_eq_zero]
  intro z hz
  have h3 := key z
  rw [hz, map_zero] at h3
  have hl0 : (l : O) ^ exSum r n hn ν l ≠ 0 := pow_ne_zero _ (by exact_mod_cast hl.ne_zero)
  exact (smul_eq_zero.1 h3.symm).resolve_left hl0

/- English proof (translation)
Introduce `ι _ r n ν hν l hl lo h hr`. Establish `hI` using `fun i => raising_exponent_interval l (r i) (h i) (lamU (r i) (n i) (ν i)) (lo i) hl (lambda_u_strict_anti (r i) (n i) (ν i) (hν i)) (hr i)`. Prove the components needed by the constructor for the conclusion. Unfold `eSum`. Use `push_cast`.

Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_le_sum fun i _ => nat_le_mul_log_real _ _ _ _ (hI i).1`. Introduce `hh`. Conclude with `Finset.sum_eq_zero fun i _ => (hI i).2 (hh i)`.
-/
theorem exponent_sum_log_bound : ESumLogBound := by
  intro ι _ r n ν hν l hl lo h hr
  have hI := fun i => raising_exponent_interval l (r i) (h i) (lamU (r i) (n i) (ν i)) (lo i) hl
    (lambda_u_strict_anti (r i) (n i) (ν i) (hν i)) (hr i)
  constructor
  · unfold eSum
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => nat_le_mul_log_real _ _ _ _ (hI i).1
  · intro hh
    exact Finset.sum_eq_zero fun i _ => (hI i).2 (hh i)

/- English proof (translation)
Introduce `hAZ O _ _ _ _ l hl hlO ι _ r n hn ν hν lo h hb`. Establish `hlog : 0 ≤ Real.log l` using `Real.log_nonneg (by exact_mod_cast hl.one_lt.le)`. Establish `hE` using `(exponent_sum_log_bound ι r n ν hν l hl lo h hb).1`. Establish `hle : exSum r n hn ν l ≤ eSum r n ν l` using `exponent_sum_le_holds hAZ ι r n hn ν hν l hl`. Establish `h1 : ((exSum r n hn ν l : ℕ) : ℝ) * Real.log l ≤ ∑ i, ((r i).choose 2 : ℝ) * Real.log (h i)` using `le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hlog) hE`.

Use `⟨h1, fun G _ Γ K ρK => le_trans (mul_le_mul_of_nonneg_right ?_ hlog) h1⟩` and prove the remaining obligations. Conclude with `(real_lattice_bound O l hl hlO ι r n hn ν hν G Γ K ρK).2` after adjusting the coercions.
-/
theorem real_lattice_log_bound : TheoremARealLog := by
  intro hAZ O _ _ _ _ l hl hlO ι _ r n hn ν hν lo h hb
  have hlog : 0 ≤ Real.log l := Real.log_nonneg (by exact_mod_cast hl.one_lt.le)
  have hE := (exponent_sum_log_bound ι r n ν hν l hl lo h hb).1
  have hle : exSum r n hn ν l ≤ eSum r n ν l := exponent_sum_le_holds hAZ ι r n hn ν hν l hl
  have h1 : ((exSum r n hn ν l : ℕ) : ℝ) * Real.log l ≤
      ∑ i, ((r i).choose 2 : ℝ) * Real.log (h i) :=
    le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hlog) hE
  refine ⟨h1, fun G _ Γ K ρK => le_trans (mul_le_mul_of_nonneg_right ?_ hlog) h1⟩
  exact_mod_cast (real_lattice_bound O l hl hlO ι r n hn ν hν G Γ K ρK).2

/- English proof (translation)
Introduce `hAZ O _ _ _ _ l hl hlO ι _ r n hn ν hν h0`. Establish `h0'` using `h0`. Unfold `eSum at h0'`. Establish `hz` using `fun i => (Finset.sum_eq_zero_iff.mp h0') i (Finset.mem_univ i)`. Establish `hinc` using `fun i => hAZ (r i) (n i) (hn i) (ν i) (hν i) l hl`.

Establish `hinc0 : ∀ i, InclZ (r i) (n i) (hn i) (ν i) l 0` using `fun i => (hz i) ▸ hinc i`. Establish `hdw : ∀ i, dualWeyl O (r i) (n i) (ν i) = weyl O (r i) (n i) (hn i) (ν i)`. Introduce `i`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`.

Establish `hx'` using `(lattice_incl_iff_ring O l hl hlO (r i) (n i) (hn i) (ν i) 0).1 (hinc0 i) x hx`. Simplify using `using hx'`. Rewrite using `[← deltaIn_map_holds O (r i) (n i) (hn i) (ν i) (hν i)]`. Conclude with `Submodule.map_subtype_le _ _`. Establish `htop : Delta O r n hn ν = ⊤`.

Rewrite using `[eq_top_iff]`. Introduce `y _`. Establish `hy` using `pow_sum_smul_mem_delta_tensor O l hl hlO ι r n hn ν (fun _ => 0) hinc0 y`. Simplify using `using hy`. Use `⟨hdw, htop, fun G _ Γ K ρK => ?_⟩` and prove the remaining obligations.

Establish `hA` using `real_exponent_bound hAZ O l hl hlO ι r n hn ν hν G Γ K ρK`. Rewrite `hA` using `[h0]`. Use `⟨le_antisymm ?_ ?_, Nat.le_zero.mp hA.2⟩` and prove the remaining obligations. Introduce `f hf`. Unfold `formsIn at hf`.

Conclude with `hf.1`. Introduce `f hf`. Simplify using `using hA.1 f hf`.
-/
theorem exponent_sum_zero_holds : ESumZero := by
  intro hAZ O _ _ _ _ l hl hlO ι _ r n hn ν hν h0
  have h0' := h0
  unfold eSum at h0'
  have hz := fun i => (Finset.sum_eq_zero_iff.mp h0') i (Finset.mem_univ i)
  have hinc := fun i => hAZ (r i) (n i) (hn i) (ν i) (hν i) l hl
  have hinc0 : ∀ i, InclZ (r i) (n i) (hn i) (ν i) l 0 := fun i => (hz i) ▸ hinc i
  have hdw : ∀ i, dualWeyl O (r i) (n i) (ν i) = weyl O (r i) (n i) (hn i) (ν i) := by
    intro i
    apply le_antisymm
    · intro x hx
      have hx' := (lattice_incl_iff_ring O l hl hlO (r i) (n i) (hn i) (ν i) 0).1 (hinc0 i) x hx
      simpa using hx'
    · rw [← deltaIn_map_holds O (r i) (n i) (hn i) (ν i) (hν i)]
      exact Submodule.map_subtype_le _ _
  have htop : Delta O r n hn ν = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy := pow_sum_smul_mem_delta_tensor O l hl hlO ι r n hn ν (fun _ => 0) hinc0 y
    simpa using hy
  refine ⟨hdw, htop, fun G _ Γ K ρK => ?_⟩
  have hA := real_exponent_bound hAZ O l hl hlO ι r n hn ν hν G Γ K ρK
  rw [h0] at hA
  refine ⟨le_antisymm ?_ ?_, Nat.le_zero.mp hA.2⟩
  · intro f hf
    unfold formsIn at hf
    exact hf.1
  · intro f hf
    simpa using hA.1 f hf

/- English proof (translation)
Introduce `O O' _ _ _ _ _ _ _ _ l hl hlO hlO' r n hn ν`. Rewrite using `[← exponent_eq_over_ring O l hl hlO r n hn ν, ← exponent_eq_over_ring O' l hl hlO' r n hn ν]`.
-/
theorem exponent_independent_of_ring : ExZIndep := by
  intro O O' _ _ _ _ _ _ _ _ l hl hlO hlO' r n hn ν
  rw [← exponent_eq_over_ring O l hl hlO r n hn ν, ← exponent_eq_over_ring O' l hl hlO' r n hn ν]

end Formalism.CohomologicalDescent.RealLocalDeltaNabla
