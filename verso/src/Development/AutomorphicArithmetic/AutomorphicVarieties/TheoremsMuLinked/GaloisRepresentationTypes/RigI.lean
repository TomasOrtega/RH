import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.IsIrrOfMatIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.FreeCO
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.TriangularOfReducibleRankThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.MatIrrOpenGd
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.GdEndOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.GdEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsFlagCharactersOfUpperTriangular
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.IsPtOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtFinFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.DvrIntClosure

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

section SlopeTestRemainingChoices

open IsLocalRing UpperTheory.V UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

/- English proof (translation)
Establish `hi : IsIntegral ℚ_[l] x` using `Algebra.IsIntegral.isIntegral x`. Establish `h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x)` using `rfl`. Rewrite `h` using `[h0, spectralValue_le_one_iff (minpoly.monic hi)]`. Establish `hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l])` using `(Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩`. Take `⟨q, hq, -, hqm⟩` from `Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)`.

Conclude with `⟨q, hqm, by`. Rewrite using `[← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩`.
-/
private theorem int_of_norm {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) (h : ‖x‖ ≤ 1) : IsIntegral ℤ_[l] x := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)] at h
  have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
    (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
  exact ⟨q, hqm, by
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

/- English proof (translation)
Set `g : R →+* f.range` to `f.rangeRestrict`. Establish `hg : Function.Surjective g` using `f.rangeRestrict_surjective`. Use `haveI : IsLocalRing f.range := IsLocalRing.of_surjective' g hg`. Establish `hl : IsLocalHom g` using `IsLocalHom.of_surjective _ hg`. Use `haveI : Algebra.IsIntegral f.range A := Algebra.IsIntegral.tower_top (R := O)`.

Establish `h2 : IsLocalHom (algebraMap f.range A)` using `Algebra.IsIntegral.isLocalHom _ _`. Conclude with `⟨fun x hx => hl.map_nonunit x (h2.map_nonunit (g x) hx)⟩`.
-/
private theorem loc_of_int {O R A : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [CommRing A]
    [Nontrivial A] [Algebra O A] [Algebra.IsIntegral O A] (f : R →ₐ[O] A) : IsLocalHom f := by
  let g : R →+* f.range := f.rangeRestrict
  have hg : Function.Surjective g := f.rangeRestrict_surjective
  haveI : IsLocalRing f.range := IsLocalRing.of_surjective' g hg
  have hl : IsLocalHom g := IsLocalHom.of_surjective _ hg
  haveI : Algebra.IsIntegral f.range A := Algebra.IsIntegral.tower_top (R := O)
  have h2 : IsLocalHom (algebraMap f.range A) := Algebra.IsIntegral.isLocalHom _ _
  exact ⟨fun x hx => hl.map_nonunit x (h2.map_nonunit (g x) hx)⟩

/- English proof (translation)
Take `⟨-, -, hl, -⟩` from `UpperTheory.V.abelian₂.dvr_finite l c.O`. Establish `hz : (l : R) ∈ maximalIdeal R` using `fun h => by`. Establish `h1 : IsUnit (algebraMap c.O R (l : c.O))` using `by rwa [map_natCast]`. Conclude with `hl (IsLocalHom.map_nonunit _ h1)`. Establish `hp : 0 < ‖((l : ℕ) : PadicAlgCl l)‖` using `norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)`.

Assume the negation of the conclusion as `hx`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt (‖((l : ℕ) : PadicAlgCl l)‖⁻¹) (not_le.1 hx)`. Establish `h1` using `hf (x ^ n * l) (Ideal.mul_mem_left _ _ hz)`. Rewrite `h1` using `[map_mul, map_pow, map_natCast, norm_mul, norm_pow]`. Establish `h2` using `mul_lt_mul_of_pos_right hn hp`.

Rewrite `h2` using `[inv_mul_cancel₀ hp.ne']`. Conclude with `lt_asymm h1 h2`.
-/
private theorem norm_le {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R]
    {f : R →ₐ[c.O] PadicAlgCl l} (hf : IsLocPt f) (x : R) : ‖f x‖ ≤ 1 := by
  obtain ⟨-, -, hl, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  have hz : (l : R) ∈ maximalIdeal R := fun h => by
    have h1 : IsUnit (algebraMap c.O R (l : c.O)) := by rwa [map_natCast]
    exact hl (IsLocalHom.map_nonunit _ h1)
  have hp : 0 < ‖((l : ℕ) : PadicAlgCl l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  by_contra hx
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖((l : ℕ) : PadicAlgCl l)‖⁻¹) (not_le.1 hx)
  have h1 := hf (x ^ n * l) (Ideal.mul_mem_left _ _ hz)
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow] at h1
  have h2 := mul_lt_mul_of_pos_right hn hp
  rw [inv_mul_cancel₀ hp.ne'] at h2
  exact lt_asymm h1 h2

/- English proof (translation)
Use `haveI := (UpperTheory.V.abelian₂.dvr_finite l c.O).1`. Take `⟨E, hE⟩` from `Loc.ptFin (l := l) R ((TrivSqZeroExt.inlAlgHom c.O _ _).comp f) hf`. Establish `hE' : ∀ a, f a ∈ E.1` using `fun a => (hE a).1`. Use `haveI := E.2`. Take `⟨h1, h2, -⟩` from `UpperTheory.V.abelian₂.dvr_intClosure l E.1`.

Set `j : E.1 →ₐ[ℤ_[l]] PadicAlgCl l` to `E.1.val.restrictScalars ℤ_[l]`. Establish `hj : Function.Injective j` using `Subtype.val_injective`. Set `e` to `(integralClosure ℤ_[l] E.1).equivMapOfInjective j hj`. Set `B` to `(integralClosure ℤ_[l] E.1).map j`. Establish `hB : ∀ x, f x ∈ B` using `fun x => ⟨⟨f x, hE' x⟩, (isIntegral_algHom_iff j hj).1 (int_of_norm _ (norm_le hf x)), rfl⟩`.

Set `A : Subalgebra c.O (PadicAlgCl l)` to `{ B.toSubsemiring with algebraMap_mem' := fun a => f.commutes a ▸ hB _ }`. Establish `d1 : IsDiscreteValuationRing B` using `IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e`. Establish `d2 : Module.Finite ℤ_[l] B` using `Module.Finite.equiv e.toLinearEquiv`. Use `haveI : Module.Finite ℤ_[l] A := d2`. Use `haveI d3 : IsDiscreteValuationRing A := d1`.

Conclude with `⟨A, d3, Module.Finite.of_restrictScalars_finite ℤ_[l] c.O A, f.codRestrict A hB, (UpperTheory.V.abelian₂.dvr_finite l A).1, fun _ => rfl⟩`.
-/
private theorem factor {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R]
    (f : R →ₐ[c.O] PadicAlgCl l) (hf : IsLocPt f) :
    ∃ (A : Subalgebra c.O (PadicAlgCl l)) (h : IsDiscreteValuationRing A) (_ : Module.Finite c.O A) (f' : R →ₐ[c.O] A),
      IsAdicComplete (@maximalIdeal A _ h.toIsLocalRing) A ∧ ∀ x, (f' x : PadicAlgCl l) = f x := by
  haveI := (UpperTheory.V.abelian₂.dvr_finite l c.O).1
  obtain ⟨E, hE⟩ := Loc.ptFin (l := l) R ((TrivSqZeroExt.inlAlgHom c.O _ _).comp f) hf
  have hE' : ∀ a, f a ∈ E.1 := fun a => (hE a).1
  haveI := E.2
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l E.1
  let j : E.1 →ₐ[ℤ_[l]] PadicAlgCl l := E.1.val.restrictScalars ℤ_[l]
  have hj : Function.Injective j := Subtype.val_injective
  let e := (integralClosure ℤ_[l] E.1).equivMapOfInjective j hj
  let B := (integralClosure ℤ_[l] E.1).map j
  have hB : ∀ x, f x ∈ B := fun x =>
    ⟨⟨f x, hE' x⟩, (isIntegral_algHom_iff j hj).1 (int_of_norm _ (norm_le hf x)), rfl⟩
  let A : Subalgebra c.O (PadicAlgCl l) := { B.toSubsemiring with algebraMap_mem' := fun a => f.commutes a ▸ hB _ }
  have d1 : IsDiscreteValuationRing B := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have d2 : Module.Finite ℤ_[l] B := Module.Finite.equiv e.toLinearEquiv
  haveI : Module.Finite ℤ_[l] A := d2
  haveI d3 : IsDiscreteValuationRing A := d1
  exact ⟨A, d3, Module.Finite.of_restrictScalars_finite ℤ_[l] c.O A, f.codRestrict A hB, (UpperTheory.V.abelian₂.dvr_finite l A).1,
    fun _ => rfl⟩

end SlopeTestRemainingChoices

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th

open Formalism.GaloisCohomology UpperTheory.V.Base in
/- English proof (translation)
Introduce `hI hH hL Ω _ _ _ K _ _ _ _ l hl c N _ e ψ D U g₁ hM S f hf hr ι hT hA`. Establish `hN` using `hH.litN`. Establish `hσ : Sd.IsCC D.cc` using `D.conj`. Use `haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (dvrFacts l c.O).2.2.1`. Use `haveI : CharP (ResidueField c.O) l := by`.

Rewrite using `[CharP.charP_iff_prime_eq_zero hl.out, ← map_natCast (residue c.O), residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] c.O)]`. Introduce `hu`. Conclude with `PadicInt.prime_p.not_unit (isUnit_of_map_unit _ _ hu)`. Use `haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩`. Take `⟨B, hB, -, -, -, hB', -⟩` from `U3.dat_loc D`.

Establish `hF` using `Fr.gd_ex ⟨⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.pt⟩, hN.coh.uo, hN.coh.gw⟩ Ω K l c N e ψ D B hB`. Establish `hσ' : IsConjOm D.cc.toRingEquiv` using `hσ`. Establish `hΨ : Chr.Psi l e (Chr.dirG ℚ Ω ψ) D.cc = 1`. Establish `h1 : cycZ ℚ Ω l D.cc = -1` using `hσ'.cyc (E := ℚ)`. Establish `h2 : chiO ℚ Ω l c.O D.cc = -1` using `by show Units.map (algebraMap ℤ_[l] c.O).toMonoidHom (cycZ ℚ Ω l D.cc) = -1`.

Rewrite using `[h1]`. Apply `Units.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Establish `h3 : (Chr.dirG ℚ Ω ψ D.cc : c.O) = (-1) ^ e`. Rewrite using `[Chr.dirG, MonoidHom.comp_apply, (Chr.clsFacts ℚ Ω N).2.2.2.1 D.cc hσ', MulChar.coe_toUnitHom]`.

Conclude with `D.gd.par`. Apply `Units.ext` to reduce the goal to its premises. Use `show ((chiO ℚ Ω l c.O D.cc ^ (e : ℤ) * Chr.dirG ℚ Ω ψ D.cc : c.Oˣ) : c.O) = 1`. Rewrite using `[h2, zpow_natCast, Units.val_mul, h3, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, ← mul_pow]`. Simplify using the standard rewrite rules.

Establish `hram : ∀ B' : ValuationSubring Ω, ¬ Ine (F` using `ℚ) B' ≤ D.η.ker → B'.valuation ((l * N * (discr K).natAbs : ℕ) : Ω) < 1 := by`. Introduce `B' h`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Establish `hd : B'.valuation ((discr K : ℤ) : Ω) < 1`. Assume the negation of the conclusion as `h4`.

Use `h fun s hs => ?_` and prove the remaining obligations. Rewrite using `[D.η_ker]`. Establish `key` using `GlobalTheory.UnramDiscr.embedding_eq B' h4 ((s : Ω →+* Ω).comp (algebraMap K Ω)) (algebraMap K Ω) (fun x => by`. Use `hs.2 _ ((B'.valuation_le_one_iff _).mpr (GlobalTheory.UnramDiscr.mem_of_isIntegral B' ?_))` and prove the remaining obligations. Conclude with `(RingOfIntegers.isIntegral_coe x).map (algebraMap K Ω).toIntAlgHom)`.

Conclude with `fun x => DFunLike.congr_fun key x`. Establish `hd' : B'.valuation (((discr K).natAbs : ℕ) : Ω) < 1`. Break down `Int.natAbs_eq (discr K) with h1 | h1` into its components or cases. Rewrite `hd` using `[h1, Int.cast_natCast]`. Conclude with `hd`.

Rewrite `hd` using `[h1, Int.cast_neg, Int.cast_natCast, Valuation.map_neg]`. Conclude with `hd`. Rewrite using `[Nat.cast_mul, map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' ((B'.valuation_le_one_iff _).2 (natCast_mem B' _))) hd'`. Establish `hk : Pr.LinkHyp c N e D.η D.cc B (l * N * (discr K).natAbs)` using `⟨D.gd.e_pos, dvd_mul_right _ _, mul_ne_zero (mul_ne_zero hl.out.ne_zero (NeZero.ne N)) (Int.natAbs_ne_zero.2 (discr_ne_zero K)), hram, hB, hσ⟩`.

Take `⟨A, hA1, hA2, f', hA3, hf'⟩` from `factor f hf`. Use `haveI : IsLocalRing A := hA1.toIsLocalRing`. Establish `ho` using `Pr.ordPt_of_gd hI.loc D g₁ hM U S B hB' A f' (loc_of_int f')`. Establish `e1 : UnitaryThreeInertia.push A.val (U3.push f' S.r.hom) = U3.push f S.r.hom` using `MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext (Matrix.ext fun a b => hf' _)) rfl`. Establish `had` using `U3.admissible_rank_three_type_one hI D hM (U3.isPt_push D hM S f hf) ι hT hA`.

Establish `he` using `D.gd.e_pos`. Establish `hfr : FreeAt l (D.rhoK _ hr)` using `freeCO hH K Ω l D.gd.l_odd ι 3 (by decide) _ (-1) N _ had.level.cont (by rw [zpow_neg_one]; exact had.aut) (NeZero.one_le) (by`. Introduce `i j hij`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega) had.level.above`. Establish `key` using `rigEnd3 hH hL Ω l ι c N e ψ D.η D.cc g₁ B _ hk hΨ hF A _ ho (Pr.matIrr_open_gd D g₁ hM B hB A _ ho (by rw [e1]; exact hT)) K D.gd.quad D.η_ker (D.rhoK _ hr) (fun s => by rw [e1]; rfl) hA hfr`.

Rewrite `key` using `[e1]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.Th.rigI :
    U3.CohInp → Af.HypothesesH → AdL → RigI := by
  intro hI hH hL Ω _ _ _ K _ _ _ _ l hl c N _ e ψ D U g₁ hM S f hf hr ι hT hA
  have hN := hH.litN
  have hσ : Sd.IsCC D.cc := D.conj
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (dvrFacts l c.O).2.2.1
  haveI : CharP (ResidueField c.O) l := by
    rw [CharP.charP_iff_prime_eq_zero hl.out, ← map_natCast (residue c.O), residue_eq_zero_iff,
      mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] c.O)]
    intro hu
    exact PadicInt.prime_p.not_unit (isUnit_of_map_unit _ _ hu)
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  obtain ⟨B, hB, -, -, -, hB', -⟩ := U3.dat_loc D
  have hF := Fr.gd_ex ⟨⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.pt⟩, hN.coh.uo, hN.coh.gw⟩
    Ω K l c N e ψ D B hB
  have hσ' : IsConjOm D.cc.toRingEquiv := hσ
  have hΨ : Chr.Psi l e (Chr.dirG ℚ Ω ψ) D.cc = 1 := by
    have h1 : cycZ ℚ Ω l D.cc = -1 := hσ'.cyc (E := ℚ)
    have h2 : chiO ℚ Ω l c.O D.cc = -1 := by
      show Units.map (algebraMap ℤ_[l] c.O).toMonoidHom (cycZ ℚ Ω l D.cc) = -1
      rw [h1]
      apply Units.ext
      simp
    have h3 : (Chr.dirG ℚ Ω ψ D.cc : c.O) = (-1) ^ e := by
      rw [Chr.dirG, MonoidHom.comp_apply, (Chr.clsFacts ℚ Ω N).2.2.2.1 D.cc hσ', MulChar.coe_toUnitHom]
      exact D.gd.par
    apply Units.ext
    show ((chiO ℚ Ω l c.O D.cc ^ (e : ℤ) * Chr.dirG ℚ Ω ψ D.cc : c.Oˣ) : c.O) = 1
    rw [h2, zpow_natCast, Units.val_mul, h3, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, ← mul_pow]
    simp
  have hram : ∀ B' : ValuationSubring Ω, ¬ Ine (F := ℚ) B' ≤ D.η.ker →
      B'.valuation ((l * N * (discr K).natAbs : ℕ) : Ω) < 1 := by
    intro B' h
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    have hd : B'.valuation ((discr K : ℤ) : Ω) < 1 := by
      by_contra h4
      refine h fun s hs => ?_
      rw [D.η_ker]
      have key := GlobalTheory.UnramDiscr.embedding_eq B' h4 ((s : Ω →+* Ω).comp (algebraMap K Ω)) (algebraMap K Ω) (fun x => by
        refine hs.2 _ ((B'.valuation_le_one_iff _).mpr (GlobalTheory.UnramDiscr.mem_of_isIntegral B' ?_))
        exact (RingOfIntegers.isIntegral_coe x).map (algebraMap K Ω).toIntAlgHom)
      exact fun x => DFunLike.congr_fun key x
    have hd' : B'.valuation (((discr K).natAbs : ℕ) : Ω) < 1 := by
      rcases Int.natAbs_eq (discr K) with h1 | h1
      · rw [h1, Int.cast_natCast] at hd; exact hd
      · rw [h1, Int.cast_neg, Int.cast_natCast, Valuation.map_neg] at hd; exact hd
    rw [Nat.cast_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((B'.valuation_le_one_iff _).2 (natCast_mem B' _))) hd'
  have hk : Pr.LinkHyp c N e D.η D.cc B (l * N * (discr K).natAbs) :=
    ⟨D.gd.e_pos, dvd_mul_right _ _,
      mul_ne_zero (mul_ne_zero hl.out.ne_zero (NeZero.ne N)) (Int.natAbs_ne_zero.2 (discr_ne_zero K)), hram, hB, hσ⟩
  obtain ⟨A, hA1, hA2, f', hA3, hf'⟩ := factor f hf
  haveI : IsLocalRing A := hA1.toIsLocalRing
  have ho := Pr.ordPt_of_gd hI.loc D g₁ hM U S B hB' A f' (loc_of_int f')
  have e1 : UnitaryThreeInertia.push A.val (U3.push f' S.r.hom) = U3.push f S.r.hom :=
    MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext (Matrix.ext fun a b => hf' _)) rfl
  have had := U3.admissible_rank_three_type_one hI D hM (U3.isPt_push D hM S f hf) ι hT hA
  have he := D.gd.e_pos
  have hfr : FreeAt l (D.rhoK _ hr) :=
    freeCO hH K Ω l D.gd.l_odd ι 3 (by decide) _ (-1) N _ had.level.cont (by rw [zpow_neg_one]; exact had.aut)
      (NeZero.one_le) (by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega) had.level.above
  have key := rigEnd3 hH hL Ω l ι c N e ψ D.η D.cc g₁ B _ hk hΨ hF A _ ho
    (Pr.matIrr_open_gd D g₁ hM B hB A _ ho (by rw [e1]; exact hT)) K D.gd.quad D.η_ker (D.rhoK _ hr)
    (fun s => by rw [e1]; rfl) hA hfr
  rwa [e1] at key
