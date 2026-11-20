import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.LocTwo

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.CentralScalarMap

/- English proof (translation)
Rewrite `h`, the goal using `[Subgroup.mem_center_iff]`. Introduce `δ`. Establish `e` using `h (Matrix.GeneralLinearGroup.map f δ)`. Rewrite `e` using `[← map_mul, ← map_mul]`. Apply `Units.ext` to reduce the goal to its premises.

Conclude with `Matrix.map_injective f.injective (congrArg Units.val e)`.
-/
theorem central_of_map {K L : Type} [Field K] [Field L] (f : K →+* L) {g : GL (Fin 2) K}
    (h : Matrix.GeneralLinearGroup.map f g ∈ Subgroup.center (GL (Fin 2) L)) :
    g ∈ Subgroup.center (GL (Fin 2) K) := by
  rw [Subgroup.mem_center_iff] at h ⊢
  intro δ
  have e := h (Matrix.GeneralLinearGroup.map f δ)
  rw [← map_mul, ← map_mul] at e
  apply Units.ext
  exact Matrix.map_injective f.injective (congrArg Units.val e)

/- English proof (translation)
Rewrite using `[Subgroup.mem_center_iff]`. Introduce `g`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]`.
-/
theorem map_scalar_center {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (z : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) z) ∈ Subgroup.center (GL (Fin 2) S) := by
  rw [Subgroup.mem_center_iff]
  intro g
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

end UpperTheory.Esk.CentralScalarMap

namespace UpperTheory.Esk

open CentralScalarMap in
/- English proof (translation)
Introduce `hA F _ _ _ c χ ⟨u, hu, hu2⟩ ω S hS hfin`. Take `⟨-, -, -, hH, -⟩` from `hA F`. Establish `hc0 : Nat.card S ≠ 0` using `Nat.card_pos.ne'`. Use `⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hc0 (p := 2) ?_⟩` and prove the remaining obligations. Introduce `p hp hd`.

Assume the negation of the conclusion as `hne`. Establish `: Fact p.Prime` using `⟨hp⟩`. Take `⟨γ, hγ⟩` from `exists_prime_orderOf_dvd_card' (G := S) p hd`. Use `set g : GL (Fin 2) F := (γ : PG F).out with hg`. Establish `hmk : ((g : PG F)) = (γ : PG F)` using `QuotientGroup.out_eq' _`.

Establish `hgp : g ^ p ∈ Subgroup.center (GL (Fin 2) F)`. Rewrite using `[← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hmk, ← Subgroup.coe_pow, ← hγ, pow_orderOf_eq_one, Subgroup.coe_one]`. Establish `hst : (γ : PG F) • ω = ω` using `hS γ.2`. Take `⟨x, hx⟩ : ∃ x : GF F, ((x : GF F ⧸ Hc c) : (mkDat c χ).Om) = ω` from `QuotientGroup.mk_surjective ω`. Establish `h1 : ((jF F g * x : GF F) : GF F ⧸ Hc c) = (x : GF F ⧸ Hc c)`.

Rewrite `hst` using `[← hmk, ← hx]`. Conclude with `hst`. Establish `h2 : x⁻¹ * (jF F g * x) ∈ Hc c` using `QuotientGroup.eq.1 h1.symm`. Take `⟨k, hk, z, hkz⟩` from `(hH c _).1 h2`. Take `⟨z0, hz0⟩` from `jF_center hgp`.

Establish `hzc : ∀ z, zc F z ∈ Subgroup.center (GF F)` using `zc_center`. Establish `hyp : (x⁻¹ * (jF F g * x)) ^ p = zc F z0`. Use `conj_pow (a := x⁻¹) (b := jF F g) (i := p)` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Rewrite using `[← mul_assoc, this, ← map_pow, hz0, Subgroup.mem_center_iff.1 (hzc _) x⁻¹, inv_mul_cancel_right]`.

Establish `hkp : k ^ p = zc F (z0 * (z ^ p)⁻¹)`. Establish `e1 : (k * zc F z) ^ p = k ^ p * zc F z ^ p` using `Commute.mul_pow (Subgroup.mem_center_iff.1 (hzc z) k) p`. Rewrite using `[map_mul, map_inv, map_pow, ← hyp, hkz, e1, mul_inv_cancel_right]`. Use `set P := Matrix.GeneralLinearGroup.map (n := Fin 2) (pLoc F u) with hP`. Establish `hPz : ∀ z, P (zc F z) ∈ Subgroup.center _` using `fun z => map_scalar_center _ z`.

Establish `hku : P k ∈ K1 u (c u)` using `Subgroup.mem_iInf.1 hk u`. Establish `hkc` using `locTwo F u (c u) hu hu2 _ hku p (hp.odd_of_ne_two hne) (by rw [← map_pow, hkp]; exact hPz _)`. Establish `hc2 : P (x⁻¹ * (jF F g * x)) ∈ Subgroup.center _`. Rewrite using `[hkz, map_mul]`. Conclude with `mul_mem hkc (hPz z)`.

Establish `hc3 : P (jF F g) ∈ Subgroup.center _`. Use `(Subgroup.normal_of_characteristic _).conj_mem _ hc2 (P x)` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Establish `hcen : g ∈ Subgroup.center (GL (Fin 2) F)` using `central_of_map ((pLoc F u).comp (algebraMap F (Af F))) hc3`. Establish `h1' : (γ : PG F) = 1`.

Rewrite using `[← hmk]`. Conclude with `(QuotientGroup.eq_one_iff _).2 hcen`. Establish `: γ = 1` using `Subtype.ext h1'`. Rewrite `hγ` using `[this, orderOf_one]`. Conclude with `hp.one_lt.ne hγ`.
-/
theorem dTwo : AMem → DTwo := by
  intro hA F _ _ _ c χ ⟨u, hu, hu2⟩ ω S hS hfin
  obtain ⟨-, -, -, hH, -⟩ := hA F
  have hc0 : Nat.card S ≠ 0 := Nat.card_pos.ne'
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hc0 (p := 2) ?_⟩
  intro p hp hd
  by_contra hne
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨γ, hγ⟩ := exists_prime_orderOf_dvd_card' (G := S) p hd
  set g : GL (Fin 2) F := (γ : PG F).out with hg
  have hmk : ((g : PG F)) = (γ : PG F) := QuotientGroup.out_eq' _
  have hgp : g ^ p ∈ Subgroup.center (GL (Fin 2) F) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hmk, ← Subgroup.coe_pow, ← hγ, pow_orderOf_eq_one,
      Subgroup.coe_one]
  have hst : (γ : PG F) • ω = ω := hS γ.2
  obtain ⟨x, hx⟩ : ∃ x : GF F, ((x : GF F ⧸ Hc c) : (mkDat c χ).Om) = ω := QuotientGroup.mk_surjective ω
  have h1 : ((jF F g * x : GF F) : GF F ⧸ Hc c) = (x : GF F ⧸ Hc c) := by
    rw [← hmk, ← hx] at hst
    exact hst
  have h2 : x⁻¹ * (jF F g * x) ∈ Hc c := QuotientGroup.eq.1 h1.symm
  obtain ⟨k, hk, z, hkz⟩ := (hH c _).1 h2
  obtain ⟨z0, hz0⟩ := jF_center hgp
  have hzc : ∀ z, zc F z ∈ Subgroup.center (GF F) := zc_center
  have hyp : (x⁻¹ * (jF F g * x)) ^ p = zc F z0 := by
    have := conj_pow (a := x⁻¹) (b := jF F g) (i := p)
    rw [inv_inv] at this
    rw [← mul_assoc, this, ← map_pow, hz0, Subgroup.mem_center_iff.1 (hzc _) x⁻¹, inv_mul_cancel_right]
  have hkp : k ^ p = zc F (z0 * (z ^ p)⁻¹) := by
    have e1 : (k * zc F z) ^ p = k ^ p * zc F z ^ p :=
      Commute.mul_pow (Subgroup.mem_center_iff.1 (hzc z) k) p
    rw [map_mul, map_inv, map_pow, ← hyp, hkz, e1, mul_inv_cancel_right]
  set P := Matrix.GeneralLinearGroup.map (n := Fin 2) (pLoc F u) with hP
  have hPz : ∀ z, P (zc F z) ∈ Subgroup.center _ := fun z => map_scalar_center _ z
  have hku : P k ∈ K1 u (c u) := Subgroup.mem_iInf.1 hk u
  have hkc := locTwo F u (c u) hu hu2 _ hku p (hp.odd_of_ne_two hne) (by rw [← map_pow, hkp]; exact hPz _)
  have hc2 : P (x⁻¹ * (jF F g * x)) ∈ Subgroup.center _ := by
    rw [hkz, map_mul]; exact mul_mem hkc (hPz z)
  have hc3 : P (jF F g) ∈ Subgroup.center _ := by
    have := (Subgroup.normal_of_characteristic _).conj_mem _ hc2 (P x)
    simpa [mul_assoc] using this
  have hcen : g ∈ Subgroup.center (GL (Fin 2) F) :=
    central_of_map ((pLoc F u).comp (algebraMap F (Af F))) hc3
  have h1' : (γ : PG F) = 1 := by
    rw [← hmk]; exact (QuotientGroup.eq_one_iff _).2 hcen
  have : γ = 1 := Subtype.ext h1'
  rw [this, orderOf_one] at hγ
  exact hp.one_lt.ne hγ

end UpperTheory.Esk
