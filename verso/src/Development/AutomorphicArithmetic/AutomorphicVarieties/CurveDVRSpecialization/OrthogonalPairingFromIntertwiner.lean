import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RankTwoAutomorphyDescendsFromAbelianCMToRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ExistsNrep3
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.EqOneOfNear

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

/- English proof (translation)
The claim follows from `UpperTheory.V.Lib.Small.norm_le_one_of_isIntegral l x hx`.
-/
private theorem norm_le_one_of_integral_padic (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  UpperTheory.V.Lib.Small.norm_le_one_of_isIntegral l x hx

set_option linter.overlappingInstances false in
/- English proof (translation)
Establish `hl0 : ((l : ℕ) : PadicAlgCl l) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero`. Establish `hl : (l : A) ≠ 0` using `fun h => hl0 (by simpa using congrArg y h)`. Establish `hl1 : ‖((l : ℕ) : PadicAlgCl l)‖ < 1`. Rewrite using `[← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']`. Conclude with `Padic.norm_p_lt_one`.

Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible A`. Take `⟨e, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl hϖ`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one hε hl1`. Use `⟨e * n, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite `hz` using `[hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.

Establish `hd : (l : A) ^ n ∣ z`. Use `Dvd.dvd.trans ?_ hz` and prove the remaining obligations. Rewrite using `[pow_mul, hu]`. Conclude with `pow_dvd_pow_of_dvd (Units.mul_left_dvd.2 dvd_rfl) n`. Take `⟨w, rfl⟩` from `hd`.

Rewrite using `[map_mul, map_pow, map_natCast, norm_mul, norm_pow]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (hle w)) hn`.
-/
private theorem small_norm_on_maximal_ideal_power {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (y : A →+* PadicAlgCl l) (hle : ∀ x, ‖y x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ z ∈ maximalIdeal A ^ n, ‖y z‖ < ε := by
  have hl0 : ((l : ℕ) : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hl : (l : A) ≠ 0 := fun h => hl0 (by simpa using congrArg y h)
  have hl1 : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
    exact Padic.norm_p_lt_one
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl hϖ
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hl1
  refine ⟨e * n, fun z hz => ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hz
  have hd : (l : A) ^ n ∣ z := by
    refine Dvd.dvd.trans ?_ hz
    rw [pow_mul, hu]
    exact pow_dvd_pow_of_dvd (Units.mul_left_dvd.2 dvd_rfl) n
  obtain ⟨w, rfl⟩ := hd
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (hle w)) hn

set_option linter.overlappingInstances false in
/- English proof (translation)
Use `continuous_matrix fun a b => continuous_iff_continuousAt.2 fun g => Metric.tendsto_nhds.2 fun ε hε => ?_` and prove the remaining obligations. Take `⟨n, hn⟩` from `small_norm_on_maximal_ideal_power y hle hε`. Use `filter_upwards [(h n).eventually_eq g] with g' hg'`. Rewrite using `[dist_eq_norm, Matrix.map_apply, Matrix.map_apply, ← map_sub]`. Conclude with `hn _ (Ideal.Quotient.eq.1 (congrFun (congrFun hg' a) b))`.
-/
private theorem continuous_padic_embedding_rep {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (y : A →+* PadicAlgCl l) (hle : ∀ x, ‖y x‖ ≤ 1) {D : Type} [Group D] [TopologicalSpace D] (r : D →* GG 3 A)
    (h : UnitaryThreeInertia.AdicCont (maximalIdeal A) r) : Continuous fun g => (r g).mat.map y := by
  refine continuous_matrix fun a b => continuous_iff_continuousAt.2 fun g => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨n, hn⟩ := small_norm_on_maximal_ideal_power y hle hε
  filter_upwards [(h n).eventually_eq g] with g' hg'
  rw [dist_eq_norm, Matrix.map_apply, Matrix.map_apply, ← map_sub]
  exact hn _ (Ideal.Quotient.eq.1 (congrFun (congrFun hg' a) b))

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨h, ?_⟩` and prove the remaining obligations. Simplify using `only [← map_inv]`. Conclude with `h.comp continuous_inv`.
-/
private theorem continuous_units_of_continuous_coe {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

/- English proof (translation)
Establish `h1 : j.left = 1` using `Units.ext hj`. Establish `h2` using `congrArg SemidirectProduct.left h`. Simplify using `only [SemidirectProduct.mul_left, h1, hj', map_one, mul_one, one_mul, sgnAct_neg_one] at h2`. Rewrite using `[GG.mat, GG.mat, h2, theta_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (Jmat R 3) (Jmat R 3), Jmat_mul_Jmat, Matrix.mul_one, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel]`. Simplify using the standard rewrite rules.
-/
private theorem orthogonal_pairing_from_intertwiner {R : Type} [CommRing R] {x y j : GG 3 R} (hj : j.mat = 1) (hj' : j.right = -1)
    (hy : y.right = 1) (h : y * j = j * x) : x.mat.transpose * Jmat R 3 * y.mat = Jmat R 3 := by
  have h1 : j.left = 1 := Units.ext hj
  have h2 := congrArg SemidirectProduct.left h
  simp only [SemidirectProduct.mul_left, h1, hj', map_one, mul_one, one_mul, sgnAct_neg_one] at h2
  rw [GG.mat, GG.mat, h2, theta_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (Jmat R 3) (Jmat R 3),
    Jmat_mul_Jmat, Matrix.mul_one, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel]
  simp

/- English proof (translation)
Use `⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun W _ hi => h W fun g hg v hv => ?_⟩` and prove the remaining obligations. Take `⟨s, t, e⟩` from `hr g hg`. Rewrite using `[e, Matrix.smul_mulVec]`. Conclude with `W.smul_mem t (hi s v hv)`.
-/
private theorem irreducible_of_scalar_multiples {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] (U : Subgroup Γ) (a : Γ → Matrix (Fin 3) (Fin 3) k)
    (h : MatIrr U a) (r : Γ' →* GL (Fin 3) k) (hr : ∀ g ∈ U, ∃ s, ∃ t : k, a g = t • (r s).val) : Af.IsIrr r := by
  refine ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun W _ hi => h W fun g hg v hv => ?_⟩
  obtain ⟨s, t, e⟩ := hr g hg
  rw [e, Matrix.smul_mulVec]
  exact W.smul_mem t (hi s v hv)

/- English proof (translation)
Introduce `hD Ω _ _ _ l _ c η Ψ σ g₁ B M L _ _ _ _ Φ k _ C₀ hok hl hcc ι K _ _ _ hK hA A _ _ r hr hirr _ ρ hρ`. Use `haveI : Module.IsTorsionFree L Ω := DivisionSemiring.to_moduleIsTorsionFree`. Use `haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩`. Use `haveI : Module.IsTorsionFree K Ω := DivisionSemiring.to_moduleIsTorsionFree`. Use `haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩`.

Use `haveI : IsGalois L Ω := {}`. Establish `hσ : σ * σ = 1`. Take `⟨j, hj⟩` from `hcc`. Conclude with `AlgEquiv.ext fun x => j.injective (by simp [AlgEquiv.mul_apply, hj])`. Establish `hησ : η σ = -1`.

Take `⟨hc, ec⟩` from `k.c`. Establish `h` using `k.del ⟨σ, hc⟩`. Rewrite `h` using `[ec, hok.del_c]`. Conclude with `h.symm`. Establish `hLη : Base.galOf ℚ L Ω ≤ η.ker` using `k.gal ▸ inf_le_right`.

Establish `hKL : ∀ x : K, ∃ y : L, algebraMap L Ω y = algebraMap K Ω x` using `fun x => (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 fun f => (hK.ge (hLη (Base.galEmb_mem ℚ L Ω f))) x`. Use `choose f hf using hKL`. Establish `hinj` using `(algebraMap L Ω).injective`. Set `φ : K →+* L` to `{ toFun := f map_one' := hinj (by rw [hf, map_one, map_one]) map_mul' := fun x y => hinj (by rw [hf, map_mul, map_mul, hf, hf]) map_zero' := hinj (by rw [hf, map_zero, map_zero]) map_add' := fun x y => hinj (by rw [hf, map_add, map_add, hf, hf]) }`. Use `letI : Algebra K L := φ.toAlgebra`.

Use `haveI : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq fun x => (hf x).symm`. Use `haveI := k.ab`. Use `haveI : IsAbelianGalois K L := IsAbelianGalois.tower_top ℚ K L`. Use `haveI : Group.IsSolvable (L ≃ₐ[K] L) := Group.isSolvable_of_comm fun a b => mul_comm' a b`. Use `haveI : FaithfulSMul c.O A := (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b h => Subtype.ext (congrArg A.val h)`.

Use `haveI : IsLocalHom (algebraMap c.O A) := Algebra.IsIntegral.isLocalHom _ _`. Use `haveI : IsNoetherianRing A := PrincipalIdealRing.isNoetherianRing`. Take `⟨ρ', h1, h2, h3⟩` from `exists_nrep3 k hok hl hσ r hr`. Establish `hU` using `hirr (Base.galOf ℚ L Ω) (Base.galEmbTop ℚ L Ω).2.1 hLη`. Establish `hcomp : ∀ s : G L Ω, Base.galEmb ℚ K Ω (Base.galEmb K L Ω s) = Base.galEmb ℚ L Ω s` using `fun s => rfl`.

Establish `haut` using `hA A ρ' h1 (by`. Introduce `v i g hg`. Rewrite using `[h3 v i g hg, UnitaryThreeInertia.psi]`. Apply the tactic sequence `have h6 : Fr.w 3 i = wt1 i := by fin_cases i <;> rfl`. Rewrite using `[h6]) (ρ.comp (Base.galEmb K L Ω)) (by`.

Introduce `s`. Rewrite using `[h2, MonoidHom.comp_apply, hρ, hcomp]`. Use the proof step `rfl) (irreducible_of_scalar_multiples _ _ hU _ (by`. Introduce `g hg`. Take `⟨s, rfl⟩ : ∃ s, Base.galEmb ℚ L Ω s = g` from `(Base.range_galEmb ℚ L Ω).ge hg`.

Conclude with `⟨s, 1, by rw [one_smul, MonoidHom.comp_apply, hρ, hcomp]; rfl⟩))`. Establish `hle : ∀ x : A, ‖(x : PadicAlgCl l)‖ ≤ 1` using `fun x => norm_le_one_of_integral_padic l _ (isIntegral_trans (A := c.O) _ ((Algebra.IsIntegral.isIntegral (R := c.O) x).map A.val))`. Establish `hz : Continuous fun s : G K Ω => ((cycZ K Ω l s : ℤ_[l]ˣ) : ℤ_[l])` using `Units.continuous_val.comp (continuous_cycZ K Ω l)`. Establish `hcyc : Continuous fun s : G K Ω => (cycBar K Ω l s : Qbar l)` using `(continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp (continuous_subtype_val.comp hz)`. Establish `hχ : Continuous fun s : G K Ω => (cycBar K Ω l s)⁻¹` using `(continuous_units_of_continuous_coe _ hcyc).inv`.

Use `hD K L Ω l ι 3 (by norm_num) _ σ hcc ?_ ⟨Jgl _ 3, fun s s' hs => ?_⟩ ?_ haut` and prove the remaining obligations. Use `continuous_units_of_continuous_coe _ ?_` and prove the remaining obligations. Simplify using `only [Af.tw_val, hρ]`. Conclude with `(Units.continuous_val.comp hχ).smul ((continuous_padic_embedding_rep (A.val : A →+* PadicAlgCl l) hle r hr.cont).comp (Base.galEmbTop ℚ K Ω).1.continuous)`. Establish `hp` using `orthogonal_pairing_from_intertwiner (x := UnitaryThreeInertia.push A.val r (Base.galEmb ℚ K Ω s)) (y := UnitaryThreeInertia.push A.val r (Base.galEmb ℚ K Ω s')) (j := UnitaryThreeInertia.push A.val r σ) (by show (r σ).mat.map _ = 1`.

Rewrite using `[hr.norm.atc]`. Use the proof step `simp)`. Use the proof step `((hr.red.mult σ).trans hησ)`. Use the proof step `((hr.red.mult _).trans (hK.le (Base.galEmb_mem ℚ K Ω s')))`. Use the proof step `(by rw [← map_mul, ← map_mul, hs, inv_mul_cancel_right])`.

Establish `he : cycBar K Ω l s' = cycBar K Ω l s` using `by show cycBar ℚ Ω l (Base.galEmb ℚ K Ω s') = cycBar ℚ Ω l (Base.galEmb ℚ K Ω s)`. Rewrite using `[hs, map_mul, map_mul, map_inv, mul_inv_cancel_comm]`. Rewrite using `[Af.tw_val, Af.tw_val, hρ, hρ, Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]`. Use `show _ • (_ * Jmat _ 3 * _) = _ • Jmat _ 3`. Rewrite using `[hp, MonoidHom.inv_apply, MonoidHom.inv_apply, he, MonoidHom.zpow_apply, ← Units.val_mul]`.

Use `congr 2`. Rewrite using `[show (1 - ((3 : ℕ) : ℤ)) = -1 + -1 by norm_num, zpow_add, zpow_neg_one]`. Use `irreducible_of_scalar_multiples _ _ hU _ fun g hg => ?_` and prove the remaining obligations. Take `⟨s, rfl⟩ : ∃ s, Base.galEmb ℚ L Ω s = g` from `(Base.range_galEmb ℚ L Ω).ge hg`. Use `⟨s, (cycBar K Ω l (Base.galEmb K L Ω s) : Qbar l), ?_⟩` and prove the remaining obligations.

Rewrite using `[MonoidHom.comp_apply, Af.tw_val, smul_smul, MonoidHom.inv_apply, Units.mul_inv, one_smul, hρ, hcomp]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Pr.autEnd3_of_autPt :
    DownCsd → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
      {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] {Φ : Fr.Frame l (ResidueField c.O)} (k : GalLink η Ψ σ g₁ B M L Φ) [CharP (ResidueField c.O) l] {C₀ : ℕ}, Φ.Ok C₀ → l ∣ M → Sd.IsCC σ → ∀ (ι : Qbar l ≃+* ℂ),
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], (∀ [Algebra K Ω], Base.galOf ℚ K Ω = η.ker) → AutPt k 3 ι (cycBar L Ω l)⁻¹ → AutEnd3 c η Ψ σ g₁ B K ι := by
  intro hD Ω _ _ _ l _ c η Ψ σ g₁ B M L _ _ _ _ Φ k _ C₀ hok hl hcc ι K _ _ _ hK hA A _ _ r hr hirr _ ρ hρ
  haveI : Module.IsTorsionFree L Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
  haveI : Module.IsTorsionFree K Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  haveI : IsGalois L Ω := {}
  have hσ : σ * σ = 1 := by
    obtain ⟨j, hj⟩ := hcc
    exact AlgEquiv.ext fun x => j.injective (by simp [AlgEquiv.mul_apply, hj])
  have hησ : η σ = -1 := by
    obtain ⟨hc, ec⟩ := k.c
    have h := k.del ⟨σ, hc⟩
    rw [ec, hok.del_c] at h
    exact h.symm
  have hLη : Base.galOf ℚ L Ω ≤ η.ker := k.gal ▸ inf_le_right
  have hKL : ∀ x : K, ∃ y : L, algebraMap L Ω y = algebraMap K Ω x := fun x =>
    (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 fun f =>
      (hK.ge (hLη (Base.galEmb_mem ℚ L Ω f))) x
  choose f hf using hKL
  have hinj := (algebraMap L Ω).injective
  let φ : K →+* L :=
    { toFun := f
      map_one' := hinj (by rw [hf, map_one, map_one])
      map_mul' := fun x y => hinj (by rw [hf, map_mul, map_mul, hf, hf])
      map_zero' := hinj (by rw [hf, map_zero, map_zero])
      map_add' := fun x y => hinj (by rw [hf, map_add, map_add, hf, hf]) }
  letI : Algebra K L := φ.toAlgebra
  haveI : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq fun x => (hf x).symm
  haveI := k.ab
  haveI : IsAbelianGalois K L := IsAbelianGalois.tower_top ℚ K L
  haveI : Group.IsSolvable (L ≃ₐ[K] L) := Group.isSolvable_of_comm fun a b => mul_comm' a b
  haveI : FaithfulSMul c.O A := (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b h =>
    Subtype.ext (congrArg A.val h)
  haveI : IsLocalHom (algebraMap c.O A) := Algebra.IsIntegral.isLocalHom _ _
  haveI : IsNoetherianRing A := PrincipalIdealRing.isNoetherianRing
  obtain ⟨ρ', h1, h2, h3⟩ := exists_nrep3 k hok hl hσ r hr
  have hU := hirr (Base.galOf ℚ L Ω) (Base.galEmbTop ℚ L Ω).2.1 hLη
  have hcomp : ∀ s : G L Ω, Base.galEmb ℚ K Ω (Base.galEmb K L Ω s) = Base.galEmb ℚ L Ω s := fun s => rfl
  have haut := hA A ρ' h1 (by
    intro v i g hg
    rw [h3 v i g hg, UnitaryThreeInertia.psi]
    have h6 : Fr.w 3 i = wt1 i := by fin_cases i <;> rfl
    rw [h6]) (ρ.comp (Base.galEmb K L Ω)) (by
    intro s
    rw [h2, MonoidHom.comp_apply, hρ, hcomp]
    rfl) (irreducible_of_scalar_multiples _ _ hU _ (by
    intro g hg
    obtain ⟨s, rfl⟩ : ∃ s, Base.galEmb ℚ L Ω s = g := (Base.range_galEmb ℚ L Ω).ge hg
    exact ⟨s, 1, by rw [one_smul, MonoidHom.comp_apply, hρ, hcomp]; rfl⟩))
  have hle : ∀ x : A, ‖(x : PadicAlgCl l)‖ ≤ 1 := fun x =>
    norm_le_one_of_integral_padic l _ (isIntegral_trans (A := c.O) _ ((Algebra.IsIntegral.isIntegral (R := c.O) x).map A.val))
  have hz : Continuous fun s : G K Ω => ((cycZ K Ω l s : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.continuous_val.comp (continuous_cycZ K Ω l)
  have hcyc : Continuous fun s : G K Ω => (cycBar K Ω l s : Qbar l) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp (continuous_subtype_val.comp hz)
  have hχ : Continuous fun s : G K Ω => (cycBar K Ω l s)⁻¹ := (continuous_units_of_continuous_coe _ hcyc).inv
  refine hD K L Ω l ι 3 (by norm_num) _ σ hcc ?_ ⟨Jgl _ 3, fun s s' hs => ?_⟩ ?_ haut
  · refine continuous_units_of_continuous_coe _ ?_
    simp only [Af.tw_val, hρ]
    exact (Units.continuous_val.comp hχ).smul
      ((continuous_padic_embedding_rep (A.val : A →+* PadicAlgCl l) hle r hr.cont).comp (Base.galEmbTop ℚ K Ω).1.continuous)
  · have hp := orthogonal_pairing_from_intertwiner (x := UnitaryThreeInertia.push A.val r (Base.galEmb ℚ K Ω s)) (y := UnitaryThreeInertia.push A.val r (Base.galEmb ℚ K Ω s'))
      (j := UnitaryThreeInertia.push A.val r σ)
      (by
        show (r σ).mat.map _ = 1
        rw [hr.norm.atc]; simp)
      ((hr.red.mult σ).trans hησ)
      ((hr.red.mult _).trans (hK.le (Base.galEmb_mem ℚ K Ω s')))
      (by rw [← map_mul, ← map_mul, hs, inv_mul_cancel_right])
    have he : cycBar K Ω l s' = cycBar K Ω l s := by
      show cycBar ℚ Ω l (Base.galEmb ℚ K Ω s') = cycBar ℚ Ω l (Base.galEmb ℚ K Ω s)
      rw [hs, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    rw [Af.tw_val, Af.tw_val, hρ, hρ, Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    show _ • (_ * Jmat _ 3 * _) = _ • Jmat _ 3
    rw [hp, MonoidHom.inv_apply, MonoidHom.inv_apply, he, MonoidHom.zpow_apply, ← Units.val_mul]
    congr 2
    rw [show (1 - ((3 : ℕ) : ℤ)) = -1 + -1 by norm_num, zpow_add, zpow_neg_one]
  · refine irreducible_of_scalar_multiples _ _ hU _ fun g hg => ?_
    obtain ⟨s, rfl⟩ : ∃ s, Base.galEmb ℚ L Ω s = g := (Base.range_galEmb ℚ L Ω).ge hg
    refine ⟨s, (cycBar K Ω l (Base.galEmb K L Ω s) : Qbar l), ?_⟩
    rw [MonoidHom.comp_apply, Af.tw_val, smul_smul, MonoidHom.inv_apply, Units.mul_inv, one_smul, hρ, hcomp]
    rfl
