import Mathlib
import GroundTheory.ArithmeticGeometry.ToricVarieties.Normal

namespace GroundTheory.Arith.Toric

universe u

open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry Algebra

section IntegralDim

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A]

/- English proof (translation)
The claim follows from `Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R A)) fun _ _ hpq => Ideal.IsIntegral.comap_lt_comap (R := R) hpq`.
-/
theorem ringKrullDim_le_of_isIntegral : ringKrullDim A ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R A)) fun _ _ hpq =>
    Ideal.IsIntegral.comap_lt_comap (R := R) hpq

/- English proof (translation)
Proceed by induction on `l using RelSeries.inductionOn' with`. Consider the case `singleton x`. Take `⟨Q, -, hQ, hQx⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal (⊥ : Ideal A) (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)`. Conclude with `⟨RelSeries.singleton _ ⟨Q, hQ⟩, rfl, PrimeSpectrum.ext hQx⟩`. Consider the case `snoc p x hx ih`.

Take `⟨l', hlen, hlast⟩` from `ih`. Establish `hle : l'.last.asIdeal.comap (algebraMap R A) ≤ x.asIdeal`. Use `congrArg PrimeSpectrum.asIdeal hlast` as an intermediate fact. Rewrite `this` using `[PrimeSpectrum.comap_asIdeal]`. Rewrite using `[this]`.

Conclude with `le_of_lt hx`. Take `⟨Q, hQle, hQ, hQx⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime x.asIdeal l'.last.asIdeal hle`. Establish `hlt : l'.last < ⟨Q, hQ⟩`. Use `lt_of_le_of_ne hQle fun h => ?_` and prove the remaining obligations. Establish `h1 : PrimeSpectrum.comap (algebraMap R A) l'.last = x`.

Rewrite using `[h]`. Conclude with `PrimeSpectrum.ext hQx`. Conclude with `(ne_of_lt hx) (hlast.symm.trans h1)`. Conclude with `⟨l'.snoc ⟨Q, hQ⟩ hlt, by simp [hlen], PrimeSpectrum.ext (by simpa using hQx)⟩`.
-/
theorem exists_ltSeries_lift (hinj : Function.Injective (algebraMap R A))
    (l : LTSeries (PrimeSpectrum R)) :
    ∃ l' : LTSeries (PrimeSpectrum A), l'.length = l.length ∧
      PrimeSpectrum.comap (algebraMap R A) l'.last = l.last := by
  induction l using RelSeries.inductionOn' with
  | singleton x =>
    obtain ⟨Q, -, hQ, hQx⟩ := Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal (⊥ : Ideal A)
      (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
    exact ⟨RelSeries.singleton _ ⟨Q, hQ⟩, rfl, PrimeSpectrum.ext hQx⟩
  | snoc p x hx ih =>
    obtain ⟨l', hlen, hlast⟩ := ih
    have hle : l'.last.asIdeal.comap (algebraMap R A) ≤ x.asIdeal := by
      have := congrArg PrimeSpectrum.asIdeal hlast
      rw [PrimeSpectrum.comap_asIdeal] at this
      rw [this]
      exact le_of_lt hx
    obtain ⟨Q, hQle, hQ, hQx⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime x.asIdeal l'.last.asIdeal hle
    have hlt : l'.last < ⟨Q, hQ⟩ := by
      refine lt_of_le_of_ne hQle fun h => ?_
      have h1 : PrimeSpectrum.comap (algebraMap R A) l'.last = x := by
        rw [h]; exact PrimeSpectrum.ext hQx
      exact (ne_of_lt hx) (hlast.symm.trans h1)
    exact ⟨l'.snoc ⟨Q, hQ⟩ hlt, by simp [hlen], PrimeSpectrum.ext (by simpa using hQx)⟩

/- English proof (translation)
Unfold `ringKrullDim Order.krullDim`. Use `iSup_le fun l => ?_` and prove the remaining obligations. Take `⟨l', hlen, -⟩` from `exists_ltSeries_lift hinj l`. Conclude with `le_iSup_of_le l' (by rw [hlen])`.
-/
theorem ringKrullDim_le_of_isIntegral_of_injective (hinj : Function.Injective (algebraMap R A)) :
    ringKrullDim R ≤ ringKrullDim A := by
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun l => ?_
  obtain ⟨l', hlen, -⟩ := exists_ltSeries_lift hinj l
  exact le_iSup_of_le l' (by rw [hlen])

/- English proof (translation)
The claim follows from `le_antisymm ringKrullDim_le_of_isIntegral (ringKrullDim_le_of_isIntegral_of_injective hinj)`.
-/
theorem ringKrullDim_eq_of_isIntegral (hinj : Function.Injective (algebraMap R A)) :
    ringKrullDim A = ringKrullDim R :=
  le_antisymm ringKrullDim_le_of_isIntegral (ringKrullDim_le_of_isIntegral_of_injective hinj)

end IntegralDim

section Trdeg

variable {k G : Type u} [CommRing k] [IsDomain k] [AddCommGroup G] [Module.Free ℤ G]

/- English proof (translation)
Set `` to `semigroupAlgebraAlgebra (k := k) (le_top : S ≤ ⊤)`. Establish `hloc` using `isLocalization_away_semigroupAlgebra (k := k) (le_top : S ≤ ⊤) hu (AddSubmonoid.mem_top _) fun m _ => hT m`. Establish `: IsScalarTower k (semigroupAlgebra k S) (semigroupAlgebra k (⊤ : AddSubmonoid G))` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `: FaithfulSMul (semigroupAlgebra k S) (semigroupAlgebra k (⊤ : AddSubmonoid G))` using `(faithfulSMul_iff_algebraMap_injective _ _).2 fun x y h => Subtype.ext (congrArg (fun z : semigroupAlgebra k (⊤ : AddSubmonoid G) => (z : AddMonoidAlgebra k G)) h)`. Establish `: FaithfulSMul k (semigroupAlgebra k S)` using `(faithfulSMul_iff_algebraMap_injective _ _).2 fun x y h => by`.

Use `congrArg (fun z : semigroupAlgebra k S => (z : AddMonoidAlgebra k G).coeff 0) h` as an intermediate fact. Simplify `this` using `[Algebra.algebraMap_eq_smul_one, AddMonoidAlgebra.one_def]`. Establish `halg` using `IsLocalization.isAlgebraic (semigroupAlgebra k (⊤ : AddSubmonoid G)) (Submonoid.powers (⟨single u 1, single_mem_semigroupAlgebra hu 1⟩ : semigroupAlgebra k S))`. Establish `h0 : trdeg (semigroupAlgebra k S) (semigroupAlgebra k (⊤ : AddSubmonoid G)) = 0` using `trdeg_eq_zero`. Rewrite using `[← trdeg_add_eq k (semigroupAlgebra k S) (A := semigroupAlgebra k (⊤ : AddSubmonoid G)), h0, add_zero]`.
-/
theorem trdeg_semigroupAlgebra_eq_top {S : AddSubmonoid G} {u : G} (hu : u ∈ S)
    (hT : ∀ m, ∃ j : ℕ, m + j • u ∈ S) :
    trdeg k (semigroupAlgebra k S) = trdeg k (semigroupAlgebra k (⊤ : AddSubmonoid G)) := by
  let := semigroupAlgebraAlgebra (k := k) (le_top : S ≤ ⊤)
  have hloc := isLocalization_away_semigroupAlgebra (k := k) (le_top : S ≤ ⊤) hu
    (AddSubmonoid.mem_top _) fun m _ => hT m
  have : IsScalarTower k (semigroupAlgebra k S) (semigroupAlgebra k (⊤ : AddSubmonoid G)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FaithfulSMul (semigroupAlgebra k S) (semigroupAlgebra k (⊤ : AddSubmonoid G)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 fun x y h =>
      Subtype.ext (congrArg (fun z : semigroupAlgebra k (⊤ : AddSubmonoid G) =>
        (z : AddMonoidAlgebra k G)) h)
  have : FaithfulSMul k (semigroupAlgebra k S) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 fun x y h => by
      have := congrArg (fun z : semigroupAlgebra k S => (z : AddMonoidAlgebra k G).coeff 0) h
      simpa [Algebra.algebraMap_eq_smul_one, AddMonoidAlgebra.one_def] using this
  have halg := IsLocalization.isAlgebraic (semigroupAlgebra k (⊤ : AddSubmonoid G))
    (Submonoid.powers (⟨single u 1, single_mem_semigroupAlgebra hu 1⟩ : semigroupAlgebra k S))
  have h0 : trdeg (semigroupAlgebra k S) (semigroupAlgebra k (⊤ : AddSubmonoid G)) = 0 :=
    trdeg_eq_zero
  rw [← trdeg_add_eq k (semigroupAlgebra k S) (A := semigroupAlgebra k (⊤ : AddSubmonoid G)),
    h0, add_zero]

variable [Module.Finite ℤ G]

/- English proof (translation)
Set `b` to `Module.finBasis ℤ G`. Set `P` to `AddMonoidHom.mrange (natCombination b)`. Set `one : Fin (Module.finrank ℤ G) →₀ ℕ` to `∑ i, Finsupp.single i 1`. Set `u` to `natCombination b one`. Establish `hu : u ∈ P` using `⟨one, rfl⟩`.

Establish `hrepr_u : ∀ i, b.repr u i = 1`. Introduce `i`. Rewrite using `[repr_natCombination]`. Simplify using `[one, Finsupp.finsetSum_apply, Finsupp.single_apply]`. Establish `hT : ∀ m, ∃ j : ℕ, m + j • u ∈ P`.

Introduce `m`. Set `j : ℕ` to `∑ i, (b.repr m i).natAbs`. Use `⟨j, ⟨Finsupp.equivFunOnFinite.symm fun i => (b.repr m i + j).toNat, ?_⟩⟩` and prove the remaining obligations. Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `i`.

Rewrite using `[repr_natCombination, map_add, map_nsmul, Finsupp.add_apply, Finsupp.smul_apply, hrepr_u, Finsupp.mapRange_apply, Finsupp.coe_equivFunOnFinite_symm]`. Establish `hle : (b.repr m i).natAbs ≤ j` using `Finset.single_le_sum (f := fun i => (b.repr m i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)`. Simplify using `only [nsmul_eq_mul, mul_one]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← trdeg_semigroupAlgebra_eq_top hu hT, ← (mvPolynomialEquiv k b).trdeg_eq, MvPolynomial.trdeg_of_isDomain]`.

Simplify using the standard rewrite rules.
-/
theorem trdeg_semigroupAlgebra_top :
    trdeg k (semigroupAlgebra k (⊤ : AddSubmonoid G)) = Module.finrank ℤ G := by
  classical
  let b := Module.finBasis ℤ G
  let P := AddMonoidHom.mrange (natCombination b)
  let one : Fin (Module.finrank ℤ G) →₀ ℕ := ∑ i, Finsupp.single i 1
  let u := natCombination b one
  have hu : u ∈ P := ⟨one, rfl⟩
  have hrepr_u : ∀ i, b.repr u i = 1 := by
    intro i
    rw [repr_natCombination]
    simp [one, Finsupp.finsetSum_apply, Finsupp.single_apply]
  have hT : ∀ m, ∃ j : ℕ, m + j • u ∈ P := by
    intro m
    let j : ℕ := ∑ i, (b.repr m i).natAbs
    refine ⟨j, ⟨Finsupp.equivFunOnFinite.symm fun i => (b.repr m i + j).toNat, ?_⟩⟩
    apply b.repr.injective
    ext i
    rw [repr_natCombination, map_add, map_nsmul, Finsupp.add_apply, Finsupp.smul_apply,
      hrepr_u, Finsupp.mapRange_apply, Finsupp.coe_equivFunOnFinite_symm]
    have hle : (b.repr m i).natAbs ≤ j :=
      Finset.single_le_sum (f := fun i => (b.repr m i).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    simp only [nsmul_eq_mul, mul_one]
    omega
  rw [← trdeg_semigroupAlgebra_eq_top hu hT, ← (mvPolynomialEquiv k b).trdeg_eq,
    MvPolynomial.trdeg_of_isDomain]
  simp

end Trdeg

section Dim

variable {k N : Type u} [Field k] [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]

/- English proof (translation)
Establish `hfin` using `finiteType_toricAlgebra (k := k) hσ`. Take `⟨u, hu, hτu⟩` from `exists_mem_dualMonoid_eq_exposedFace hσ (bot_isFaceOf_iff.2 hs)`. Establish `hbot : dualMonoid (⊥ : PointedCone ℝ (ℝ ⊗[ℤ] N)) = ⊤` using `eq_top_iff.2 fun m _ => mem_dualMonoid.2 fun x hx => by`. Rewrite using `[(Submodule.mem_bot _).1 hx, map_zero]`. Establish `hT : ∀ m : Dual ℤ N, ∃ j : ℕ, m + j • u ∈ dualMonoid σ`.

Introduce `m`. Establish `hm : m ∈ dualMonoid σ ⊔ AddSubmonoid.closure {-u}`. Rewrite using `[← dualMonoid_exposedFace hσ hu, ← hτu, hbot]`. Conclude with `AddSubmonoid.mem_top m`. Take `⟨y, hy, z, hz, rfl⟩` from `AddSubmonoid.mem_sup.1 hm`.

Take `⟨j, rfl⟩` from `AddSubmonoid.mem_closure_singleton.1 hz`. Conclude with `⟨j, by rwa [add_assoc, smul_neg, neg_add_cancel, add_zero]⟩`. Establish `hrank : Module.finrank ℤ (Dual ℤ N) = Module.finrank ℤ N` using `(Module.finBasis ℤ N).toDualEquiv.finrank_eq.symm`. Establish `htr : trdeg k (toricAlgebra k σ) = Module.finrank ℤ N`. Rewrite using `[trdeg_semigroupAlgebra_eq_top hu hT, trdeg_semigroupAlgebra_top, hrank]`.

Take `⟨s, g, hginj, hgint⟩` from `exists_integral_inj_algHom_of_fg k (toricAlgebra k σ)`. Set `` to `g.toRingHom.toAlgebra`. Establish `: Algebra.IsIntegral (MvPolynomial (Fin s) k) (toricAlgebra k σ)` using `⟨fun x => hgint x⟩`. Establish `hdim : ringKrullDim (toricAlgebra k σ) = s`. Rewrite using `[ringKrullDim_eq_of_isIntegral hginj, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]`.

Simplify using the standard rewrite rules. Establish `: IsScalarTower k (MvPolynomial (Fin s) k) (toricAlgebra k σ)` using `IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm`. Establish `: FaithfulSMul (MvPolynomial (Fin s) k) (toricAlgebra k σ)` using `(faithfulSMul_iff_algebraMap_injective _ _).2 hginj`. Establish `h0 : trdeg (MvPolynomial (Fin s) k) (toricAlgebra k σ) = 0` using `trdeg_eq_zero`. Establish `hsum` using `trdeg_add_eq k (MvPolynomial (Fin s) k) (A := toricAlgebra k σ)`.

Rewrite `hsum` using `[h0, add_zero, MvPolynomial.trdeg_of_isDomain, htr, Cardinal.mk_fin, Cardinal.lift_natCast]`. Establish `hsn : s = Module.finrank ℤ N` using `by exact_mod_cast hsum`. Rewrite using `[hdim, hsn]`.
-/
theorem ringKrullDim_toricAlgebra {σ : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (hσ : IsRationalPolyhedral (toRealSpan N) σ) (hs : (σ : ConvexCone ℝ (ℝ ⊗[ℤ] N)).Salient) :
    ringKrullDim (toricAlgebra k σ) = Module.finrank ℤ N := by
  have hfin := finiteType_toricAlgebra (k := k) hσ
  obtain ⟨u, hu, hτu⟩ := exists_mem_dualMonoid_eq_exposedFace hσ (bot_isFaceOf_iff.2 hs)
  have hbot : dualMonoid (⊥ : PointedCone ℝ (ℝ ⊗[ℤ] N)) = ⊤ :=
    eq_top_iff.2 fun m _ => mem_dualMonoid.2 fun x hx => by
      rw [(Submodule.mem_bot _).1 hx, map_zero]
  have hT : ∀ m : Dual ℤ N, ∃ j : ℕ, m + j • u ∈ dualMonoid σ := by
    intro m
    have hm : m ∈ dualMonoid σ ⊔ AddSubmonoid.closure {-u} := by
      rw [← dualMonoid_exposedFace hσ hu, ← hτu, hbot]
      exact AddSubmonoid.mem_top m
    obtain ⟨y, hy, z, hz, rfl⟩ := AddSubmonoid.mem_sup.1 hm
    obtain ⟨j, rfl⟩ := AddSubmonoid.mem_closure_singleton.1 hz
    exact ⟨j, by rwa [add_assoc, smul_neg, neg_add_cancel, add_zero]⟩
  have hrank : Module.finrank ℤ (Dual ℤ N) = Module.finrank ℤ N :=
    (Module.finBasis ℤ N).toDualEquiv.finrank_eq.symm
  have htr : trdeg k (toricAlgebra k σ) = Module.finrank ℤ N := by
    rw [trdeg_semigroupAlgebra_eq_top hu hT, trdeg_semigroupAlgebra_top, hrank]
  obtain ⟨s, g, hginj, hgint⟩ := exists_integral_inj_algHom_of_fg k (toricAlgebra k σ)
  let := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) (toricAlgebra k σ) := ⟨fun x => hgint x⟩
  have hdim : ringKrullDim (toricAlgebra k σ) = s := by
    rw [ringKrullDim_eq_of_isIntegral hginj, MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field]
    simp
  have : IsScalarTower k (MvPolynomial (Fin s) k) (toricAlgebra k σ) :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  have : FaithfulSMul (MvPolynomial (Fin s) k) (toricAlgebra k σ) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hginj
  have h0 : trdeg (MvPolynomial (Fin s) k) (toricAlgebra k σ) = 0 := trdeg_eq_zero
  have hsum := trdeg_add_eq k (MvPolynomial (Fin s) k) (A := toricAlgebra k σ)
  rw [h0, add_zero, MvPolynomial.trdeg_of_isDomain, htr, Cardinal.mk_fin,
    Cardinal.lift_natCast] at hsum
  have hsn : s = Module.finrank ℤ N := by exact_mod_cast hsum
  rw [hdim, hsn]

/- English proof (translation)
Rewrite using `[PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_toricAlgebra hσ hs]`.
-/
theorem topologicalKrullDim_affineToricVariety {σ : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (hσ : IsRationalPolyhedral (toRealSpan N) σ) (hs : (σ : ConvexCone ℝ (ℝ ⊗[ℤ] N)).Salient) :
    topologicalKrullDim (PrimeSpectrum (toricAlgebra k σ)) = Module.finrank ℤ N := by
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_toricAlgebra hσ hs]

end Dim

end GroundTheory.Arith.Toric
