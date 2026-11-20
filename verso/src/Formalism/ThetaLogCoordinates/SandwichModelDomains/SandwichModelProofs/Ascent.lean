import Formalism.ThetaLogCoordinates.SandwichModelDomains.SpreadSquare
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDlatLemmas

open MvPolynomial

namespace Formalism.InvariantFactorPaths.INST

open Formalism.GradedWeylDivisibility

/- English proof (translation)
Use `set φ : ℤ →+* O := Int.castRingHom O with hφ`. Establish `hrow : ∀ (a b : Fin r) (g : MvPolynomial (Fin r × Fin n) ℤ), rowGen O a b (map φ g) = Polynomial.map (map φ) (rowGen ℤ a b g)`. Introduce `a b g`. Establish `key : ((rowGen O a b).toRingHom.comp (map φ) : MvPolynomial (Fin r × Fin n) ℤ →+* Polynomial (MvPolynomial (Fin r × Fin n) O)) = (Polynomial.mapRingHom (map φ)).comp (rowGen ℤ a b).toRingHom`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `c`. Rewrite using `[← RingHom.comp_apply, eq_intCast, ← RingHom.comp_apply, eq_intCast]`. Introduce `v`. Simplify using `only [RingHom.comp_apply]`. Apply the tactic sequence `(simp [rowGen]) <;> (try split_ifs) <;> (try simp)`.

Conclude with `RingHom.congr_fun key g`. Establish `hdiv : ∀ (a b : Fin r) (k : ℕ) (g : MvPolynomial (Fin r × Fin n) ℤ), map φ (rowDiv ℤ a b k g) = rowDiv O a b k (map φ g)`. Introduce `a b k g`. Unfold `rowDiv`. Rewrite using `[hrow, Polynomial.coeff_map]`.

Establish `hword : ∀ (w : List (Fin r × Fin r × ℕ)) (g : MvPolynomial (Fin r × Fin n) ℤ), map φ (applyWord ℤ w g) = applyWord O w (map φ g)`. Introduce `w g`. Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons x w ih => show map φ (rowDiv ℤ x.1 x.2.1 x.2.2 (applyWord ℤ w g)) = rowDiv O x.1 x.2.1 x.2.2 (applyWord O w (map φ g))`.

Rewrite using `[hdiv, ih]`. Establish `hhw : map φ (hw ℤ hn ν) = hw O hn ν`. Unfold `hw`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl (fun s _ => ?_)` and prove the remaining obligations.

Rewrite using `[map_pow]`. Use `congr 1`. Unfold `lpMinor`. Rewrite using `[RingHom.map_det]`. Use `congr 1`.

Use extensionality with `i j`. Simplify using `[RingHom.mapMatrix_apply, Matrix.map_apply]`. Unfold `weyl at hf ⊢`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨w, rfl⟩` from `hx`. Use `Submodule.subset_span ⟨w, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `try dsimp only`. Rewrite using `[hword, hhw]`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx`. Rewrite using `[map_zsmul]`.

Use `first`. Consider the case `exact zsmul_mem hx c`. Consider the case `exact Submodule.smul_of_tower_mem _ c hx`.
-/
theorem asc_map_weyl (O : Type) [CommRing O] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℤ) (hf : f ∈ weyl ℤ r n hn ν) :
    map (Int.castRingHom O) f ∈ weyl O r n hn ν := by
  set φ : ℤ →+* O := Int.castRingHom O with hφ
  have hrow : ∀ (a b : Fin r) (g : MvPolynomial (Fin r × Fin n) ℤ),
      rowGen O a b (map φ g) = Polynomial.map (map φ) (rowGen ℤ a b g) := by
    intro a b g
    have key : ((rowGen O a b).toRingHom.comp (map φ) :
          MvPolynomial (Fin r × Fin n) ℤ →+* Polynomial (MvPolynomial (Fin r × Fin n) O)) =
        (Polynomial.mapRingHom (map φ)).comp (rowGen ℤ a b).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        rw [← RingHom.comp_apply, eq_intCast, ← RingHom.comp_apply, eq_intCast]
      · intro v
        simp only [RingHom.comp_apply]
        (simp [rowGen]) <;> (try split_ifs) <;> (try simp)
    exact RingHom.congr_fun key g
  have hdiv : ∀ (a b : Fin r) (k : ℕ) (g : MvPolynomial (Fin r × Fin n) ℤ),
      map φ (rowDiv ℤ a b k g) = rowDiv O a b k (map φ g) := by
    intro a b k g
    unfold rowDiv
    rw [hrow, Polynomial.coeff_map]
  have hword : ∀ (w : List (Fin r × Fin r × ℕ)) (g : MvPolynomial (Fin r × Fin n) ℤ),
      map φ (applyWord ℤ w g) = applyWord O w (map φ g) := by
    intro w g
    induction w with
    | nil => rfl
    | cons x w ih =>
      show map φ (rowDiv ℤ x.1 x.2.1 x.2.2 (applyWord ℤ w g)) =
        rowDiv O x.1 x.2.1 x.2.2 (applyWord O w (map φ g))
      rw [hdiv, ih]
  have hhw : map φ (hw ℤ hn ν) = hw O hn ν := by
    unfold hw
    rw [map_prod]
    refine Finset.prod_congr rfl (fun s _ => ?_)
    rw [map_pow]
    congr 1
    unfold lpMinor
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.map_apply]
  unfold weyl at hf ⊢
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine Submodule.subset_span ⟨w, ?_⟩
    try dsimp only
    rw [hword, hhw]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [map_zsmul]
    first
      | exact zsmul_mem hx c
      | exact Submodule.smul_of_tower_mem _ c hx

/- English proof (translation)
Introduce `p r n hn ν e h O _ _ hO x hx`. Rewrite `hx` using `[standardMonomialSpanDomain O r n ν]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨K, sz, hsz, I, hsh, rfl⟩` from `hy`.

Establish `hZ : bideterminant ℤ sz hsz I ∈ dualWeyl ℤ r n ν`. Rewrite using `[← hsh]`. Conclude with `bidetMem ℤ r n K sz hsz I`. Take `⟨c, hc, hm⟩` from `h _ hZ`. Establish `h2` using `asc_map_weyl O hn ν _ hm`.

Establish `e2 : map (Int.castRingHom O) ((c * (p : ℤ) ^ e) • bideterminant ℤ sz hsz I) = ((c : ℤ) : O) • (((p : O) ^ e) • bideterminant O sz hsz I)`. Rewrite using `[smul_eq_C_mul, map_mul, map_C, ldlat_map_bidet, smul_smul, smul_eq_C_mul]`. Simplify using the standard rewrite rules. Rewrite `h2` using `[e2]`. Take `⟨u, hu⟩` from `hO c hc`.

Establish `h3` using `Submodule.smul_mem _ ((u⁻¹ : Oˣ) : O) h2`. Rewrite `h3` using `[smul_smul, ← hu, Units.inv_mul, one_smul]`. Then use the resulting hypothesis. Consider the case `zero => rw [smul_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add y z _ _ hy hz => rw [smul_add]`.

Conclude with `Submodule.add_mem _ hy hz`. Consider the case `smul c y _ hy => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem ascent_domain_holds : AscentDomain := by
  intro p r n hn ν e h O _ _ hO x hx
  rw [standardMonomialSpanDomain O r n ν] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨K, sz, hsz, I, hsh, rfl⟩ := hy
    have hZ : bideterminant ℤ sz hsz I ∈ dualWeyl ℤ r n ν := by
      rw [← hsh]; exact bidetMem ℤ r n K sz hsz I
    obtain ⟨c, hc, hm⟩ := h _ hZ
    have h2 := asc_map_weyl O hn ν _ hm
    have e2 : map (Int.castRingHom O) ((c * (p : ℤ) ^ e) • bideterminant ℤ sz hsz I) =
        ((c : ℤ) : O) • (((p : O) ^ e) • bideterminant O sz hsz I) := by
      rw [smul_eq_C_mul, map_mul, map_C, ldlat_map_bidet, smul_smul, smul_eq_C_mul]
      simp
    rw [e2] at h2
    obtain ⟨u, hu⟩ := hO c hc
    have h3 := Submodule.smul_mem _ ((u⁻¹ : Oˣ) : O) h2
    rwa [smul_smul, ← hu, Units.inv_mul, one_smul] at h3
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy

/- English proof (translation)
Unfold `UnitsOfLocal PrimeToPUnits`. Introduce `p hp O _ _ hpu c hc`. Establish `hpZ : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hp.out`. Establish `hcop : IsCoprime (p : ℤ) c` using `by first`. Consider the case `exact (Irreducible.coprime_iff_not_dvd hpZ.irreducible).mpr hc`.

Consider the case `exact (Prime.coprime_iff_not_dvd hpZ).mpr hc`. Consider the case `exact Int.isCoprime_iff_gcd_eq_one.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr (fun h => hc (Int.natCast_dvd.mpr h)))`. Take `⟨a, b, hab⟩` from `hcop`. Establish `h1 : (a : O) * (p : O) + (b : O) * (c : O) = 1`. Establish `h2` using `congrArg (fun z : ℤ => (z : O)) hab`.

Move the coercions through the operations in `at h2`. Conclude with `h2`. Break down `IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h | h` into its components or cases. Conclude with `absurd (isUnit_of_mul_isUnit_right h) hpu`. Conclude with `isUnit_of_mul_isUnit_right h`.
-/
theorem units_of_local_ring : UnitsOfLocal := by
  unfold UnitsOfLocal PrimeToPUnits
  intro p hp O _ _ hpu c hc
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hcop : IsCoprime (p : ℤ) c := by
    first
      | exact (Irreducible.coprime_iff_not_dvd hpZ.irreducible).mpr hc
      | exact (Prime.coprime_iff_not_dvd hpZ).mpr hc
      | exact Int.isCoprime_iff_gcd_eq_one.mpr
          ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr (fun h => hc (Int.natCast_dvd.mpr h)))
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (a : O) * (p : O) + (b : O) * (c : O) = 1 := by
    have h2 := congrArg (fun z : ℤ => (z : O)) hab
    push_cast at h2
    exact h2
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h | h
  · exact absurd (isUnit_of_mul_isUnit_right h) hpu
  · exact isUnit_of_mul_isUnit_right h

end Formalism.InvariantFactorPaths.INST
