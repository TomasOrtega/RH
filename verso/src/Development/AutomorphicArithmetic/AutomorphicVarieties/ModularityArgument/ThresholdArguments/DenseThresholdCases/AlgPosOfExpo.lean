import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.AlgPosOfExpo
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SdAdAutQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Ws UpperTheory.V.Cu UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open scoped Matrix
open private charEig_cyc_inv algSat_eq from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymmetricAdjointFrobenius.AdAutQ
open private diagR infDiag_eqR diagR_mk ev_notMem from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.DenseRangeUnitsR
/- English proof (translation)
Take `⟨n, hn⟩` from `h default`. Use `⟨fun _ => n, fun k hk => ?_⟩` and prove the remaining obligations. Use `letI : Unique (ℚ →+* ℂ) := ⟨⟨Rat.castHom ℂ⟩, fun _ => Subsingleton.elim _ _⟩`. Establish `hk0 : (0 : ℝ) < ((k : ℚ) : ℝ)` using `hk (Rat.castHom ℝ)`. Establish `hv : ∀ v, diagR ℚ (k : ℚ) v = ((k : ℚ) : ℝ)` using `fun v => eq_ratCast ((Pi.evalRingHom (fun _ : InfinitePlace ℚ => ℝ) v).comp (diagR ℚ)) (k : ℚ)`.

Establish `e : Units.map (diagR ℚ).toMonoidHom k = TR.expU fun _ => Real.log ((k : ℚ) : ℝ)` using `Units.ext (funext fun v => (hv v).trans (Real.exp_log hk0).symm)`. Establish `e2` using `TR.chiInf_expU_eq ω fun _ => Real.log ((k : ℚ) : ℝ)`. Rewrite `e2` using `[← e, Fintype.sum_unique, hn, Complex.exp_int_mul, ← Complex.ofReal_exp, Real.exp_log hk0]`. Rewrite using `[HChar.inf, MonoidHom.comp_apply, infDiag_eqR, Fintype.prod_unique, eq_ratCast, ← Complex.ofReal_ratCast]`. Conclude with `e2`.
-/
private theorem algPos_of_expo (ω : HChar ℚ) (h : ∀ v, ∃ n : ℤ, TR.expo ω v = n) : ∃ a, IsAlgPos ω a := by
  obtain ⟨n, hn⟩ := h default
  refine ⟨fun _ => n, fun k hk => ?_⟩
  letI : Unique (ℚ →+* ℂ) := ⟨⟨Rat.castHom ℂ⟩, fun _ => Subsingleton.elim _ _⟩
  have hk0 : (0 : ℝ) < ((k : ℚ) : ℝ) := hk (Rat.castHom ℝ)
  have hv : ∀ v, diagR ℚ (k : ℚ) v = ((k : ℚ) : ℝ) := fun v =>
    eq_ratCast ((Pi.evalRingHom (fun _ : InfinitePlace ℚ => ℝ) v).comp (diagR ℚ)) (k : ℚ)
  have e : Units.map (diagR ℚ).toMonoidHom k = TR.expU fun _ => Real.log ((k : ℚ) : ℝ) :=
    Units.ext (funext fun v => (hv v).trans (Real.exp_log hk0).symm)
  have e2 := TR.chiInf_expU_eq ω fun _ => Real.log ((k : ℚ) : ℝ)
  rw [← e, Fintype.sum_unique, hn, Complex.exp_int_mul, ← Complex.ofReal_exp, Real.exp_log hk0] at e2
  rw [HChar.inf, MonoidHom.comp_apply, infDiag_eqR, Fintype.prod_unique, eq_ratCast, ← Complex.ofReal_ratCast]
  exact e2
/- English proof (translation)
Establish `hq : ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) * ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) = q`. Rewrite using `[← Real.rpow_add' (Nat.cast_nonneg q) (by norm_num)]`. Evaluate the numerical expressions. Establish `hq'` using `congrArg (fun x : ℝ => (x : ℂ)) hq`. Simplify using `only [Complex.ofReal_mul, Complex.ofReal_natCast] at hq'`.

Rewrite using `[Matrix.det_eq_prod_roots_charpoly, h, roots_multiset_prod_X_sub_C, algSat_eq, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, mul_mul_mul_comm, hq', Units.val_mul, mul_comm]`.
-/
private theorem det_sat (M : Matrix (Fin 2) (Fin 2) ℂ) (q : ℕ) (x y : ℂˣ)
    (h : M.charpoly = ((algSat 2 q {x, y}).map fun b => X - C b).prod) : M.det = ((x * y : ℂˣ) : ℂ) * q := by
  have hq : ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) * ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) = q := by
    rw [← Real.rpow_add' (Nat.cast_nonneg q) (by norm_num)]
    norm_num
  have hq' := congrArg (fun x : ℝ => (x : ℂ)) hq
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast] at hq'
  rw [Matrix.det_eq_prod_roots_charpoly, h, roots_multiset_prod_X_sub_C, algSat_eq, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, mul_mul_mul_comm, hq', Units.val_mul, mul_comm]
/- English proof (translation)
Take `⟨π, hreg, hatt⟩` from `ha`. Take `⟨ω, hω, hint⟩` from `_root_.central_character_of_regular_cusp P.toClassicalTheorems π hreg (hatt.2.mono fun w ⟨B, hB, _⟩ => ⟨B, hB⟩)`. Take `⟨a, hal⟩` from `algPos_of_expo ω hint`. Take `⟨art, hart⟩ : ∃ art : Ideles ℚ →* Gab ℚ Ω, IsGlobalArtin art` from `P.toClassicalTheorems.litN.aut.art _ Ω`. Take `⟨μ, hμ, hL⟩` from `hart.exists_isLAdicOf ι hal`.

Establish `hch : IsCharOf ι ω μ` using `⟨hμ, art, a, hart, hal, hL⟩`. Take `⟨hcc, χ, art', a', h'⟩` from `UpperTheory.exists_algebraic_heckeChar_cyclotomic P.toClassicalTheorems.litN.aut.art ℚ Ω l ι 1 (cycBar ℚ Ω l) ⟨1, 1, le_rfl, fun _ _ => rfl, by rw [zpow_one, mul_one]⟩`. Establish `H` using `(_root_.UpperTheory.V.Af.algOfCyc_s P ℚ Ω l ι).2.1`. Establish `h1 : Af.IsAlgChar ι (cycBar ℚ Ω l)` using `⟨χ, hcc, art', a', h'⟩`. Establish `h2` using `(H μ _ ⟨ω, hch⟩ (H _ _ h1 h1).2).1`.

Establish `key : (fun s : G ℚ Ω => (ρ s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det) = fun s => (((μ * (cycBar ℚ Ω l)⁻¹) s⁻¹ : (Qbar l)ˣ) : Qbar l)`. Use `GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob GlobalTheory.Published.chebotarevDegreeOne' (Filter.eventually_cofinite.1 ((hatt.2.and (UpperTheory.galois_character_frobenius_compatibility ℚ Ω l ι ω μ hch)).and (ev_notMem (K := ℚ) l))) (Units.continuous_val.comp (hc.comp co …` and prove the remaining obligations. Introduce `v hv _ A hA σ hσ`. Take `⟨⟨⟨B, hB, hF⟩, -, h3⟩, h4⟩` from `not_not.1 hv`. Take `⟨x, y, rfl⟩` from `Multiset.card_eq_two.1 hB.card`.

Establish `e2` using `(hF A hA).2 σ hσ`. Rewrite `e2` using `[← Matrix.charpoly_map]`. Apply `ι.injective` to reduce the goal to its premises. Rewrite using `[MonoidHom.mul_apply, Units.val_mul, map_mul, (h3 A hA).2 σ hσ, (charEig_cyc_inv ι v h4 A hA).2 σ hσ, ← hω v x y hB, ← det_sat _ _ _ _ e2]`. Conclude with `ι.toRingHom.map_det _`.

Establish `e : Matrix.GeneralLinearGroup.det.comp ρ = μ * (cycBar ℚ Ω l)⁻¹` using `MonoidHom.ext fun s => Units.ext (by`. Use `congrFun key s⁻¹` as an intermediate fact. Simplify using `only [inv_inv] at this`. Conclude with `this)`. Rewrite using `[e]`.

Conclude with `h2`.
-/
private theorem det_alg (P : _root_.UpperTheory.V.Af.HypothesesH') {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hc : Continuous ρ) (ha : IsAutR ι ρ) :
    Af.IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp ρ) := by
  obtain ⟨π, hreg, hatt⟩ := ha
  obtain ⟨ω, hω, hint⟩ := _root_.central_character_of_regular_cusp P.toClassicalTheorems π hreg (hatt.2.mono fun w ⟨B, hB, _⟩ => ⟨B, hB⟩)
  obtain ⟨a, hal⟩ := algPos_of_expo ω hint
  obtain ⟨art, hart⟩ : ∃ art : Ideles ℚ →* Gab ℚ Ω, IsGlobalArtin art := P.toClassicalTheorems.litN.aut.art _ Ω
  obtain ⟨μ, hμ, hL⟩ := hart.exists_isLAdicOf ι hal
  have hch : IsCharOf ι ω μ := ⟨hμ, art, a, hart, hal, hL⟩
  obtain ⟨hcc, χ, art', a', h'⟩ := UpperTheory.exists_algebraic_heckeChar_cyclotomic P.toClassicalTheorems.litN.aut.art ℚ Ω l ι 1 (cycBar ℚ Ω l)
    ⟨1, 1, le_rfl, fun _ _ => rfl, by rw [zpow_one, mul_one]⟩
  have H := (_root_.UpperTheory.V.Af.algOfCyc_s P ℚ Ω l ι).2.1
  have h1 : Af.IsAlgChar ι (cycBar ℚ Ω l) := ⟨χ, hcc, art', a', h'⟩
  have h2 := (H μ _ ⟨ω, hch⟩ (H _ _ h1 h1).2).1
  have key : (fun s : G ℚ Ω => (ρ s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det) =
      fun s => (((μ * (cycBar ℚ Ω l)⁻¹) s⁻¹ : (Qbar l)ˣ) : Qbar l) := by
    refine GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob GlobalTheory.Published.chebotarevDegreeOne'
      (Filter.eventually_cofinite.1 ((hatt.2.and (UpperTheory.galois_character_frobenius_compatibility ℚ Ω l ι ω μ hch)).and (ev_notMem (K := ℚ) l)))
      (Units.continuous_val.comp (hc.comp continuous_inv)).matrix_det
      (Units.continuous_val.comp ((hμ.mul hcc.inv).comp continuous_inv)) ?_
    intro v hv _ A hA σ hσ
    obtain ⟨⟨⟨B, hB, hF⟩, -, h3⟩, h4⟩ := not_not.1 hv
    obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hB.card
    have e2 := (hF A hA).2 σ hσ
    rw [← Matrix.charpoly_map] at e2
    apply ι.injective
    rw [MonoidHom.mul_apply, Units.val_mul, map_mul, (h3 A hA).2 σ hσ, (charEig_cyc_inv ι v h4 A hA).2 σ hσ,
      ← hω v x y hB, ← det_sat _ _ _ _ e2]
    exact ι.toRingHom.map_det _
  have e : Matrix.GeneralLinearGroup.det.comp ρ = μ * (cycBar ℚ Ω l)⁻¹ := MonoidHom.ext fun s => Units.ext (by
    have := congrFun key s⁻¹
    simp only [inv_inv] at this
    exact this)
  rw [e]
  exact h2
/- English proof (translation)
Use `haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Set `j : Ω →ₐ[ℚ] ℂ` to `IsAlgClosed.lift`. Use `letI : Algebra Ω ℂ := j.toRingHom.toAlgebra`. Use `haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm`.

Use `haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω`. Set `τ : ℂ ≃ₐ[ℚ] ℂ` to `AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp`. Conclude with `⟨τ.restrictNormal Ω, algebraMap Ω ℂ, fun x => AlgEquiv.restrictNormal_commutes τ Ω x⟩`.
-/
private theorem conj_ex (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] : ∃ c : G ℚ Ω, IsConjEl c := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  let j : Ω →ₐ[ℚ] ℂ := IsAlgClosed.lift
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let τ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp
  exact ⟨τ.restrictNormal Ω, algebraMap Ω ℂ, fun x => AlgEquiv.restrictNormal_commutes τ Ω x⟩
/- English proof (translation)
Introduce `h`. Take `⟨j, hj⟩` from `hc`. Use `InfinitePlace.not_isReal_iff_isComplex.2 (hK.isComplex (InfinitePlace.mk (j.comp (algebraMap K' Ω)))) (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))` and prove the remaining obligations. Conclude with `(hj x).symm.trans (congrArg j (h x))`.
-/
private theorem conj_off {Ω : Type} [Field Ω] [CharZero Ω] (K' : IntermediateField ℚ Ω) (hK : IsTotallyComplex K') {c : G ℚ Ω}
    (hc : IsConjEl c) : c ∉ K'.fixingSubgroup := by
  intro h
  obtain ⟨j, hj⟩ := hc
  refine InfinitePlace.not_isReal_iff_isComplex.2 (hK.isComplex (InfinitePlace.mk (j.comp (algebraMap K' Ω))))
    (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
  exact (hj x).symm.trans (congrArg j (h x))
/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring`.
-/
private theorem pair_plane {k : Type} [Field k] (A : Matrix (Fin 2) (Fin 2) k) :
    Aᵀ * !![0, 1; -1, 0] * A = A.det • (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring
/- English proof (translation)
Establish `hf : ∀ x, τ x 0 0 ^ 2 - τ x 1 0 ^ 2 = 1` using `fun x => by`. Establish `h` using `congrFun (congrFun (hτ.form x) 0) 0`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two] at h`. Take the linear combination `h`. Establish `hg : resQ K' g ∈ K'.fixingSubgroup` using `fun y => g.commutes y`.

Establish `e : τ (resQ K' g') * τ c = τ c * τ (resQ K' g)`. Rewrite using `[h, ← map_mul, ← map_mul, inv_mul_cancel_right]`. Establish `hg' : resQ K' g' ∈ K'.fixingSubgroup` using `fun y => g'.commutes y`. Establish `e0` using `congrFun (congrFun e 0) 0`. Establish `e1` using `congrFun (congrFun e 0) 1`.

Establish `f1` using `hf c`. Establish `f2` using `hf (resQ K' g)`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_two, (hτ.off c hc).1, (hτ.off c hc).2, (hτ.on _ hg).1, (hτ.on _ hg).2] at e0 e1 f1 f2`. Establish `key : (τ (resQ K' g) 0 0 + τ (resQ K' g) 0 1) * (τ (resQ K' g') 0 0 + τ (resQ K' g') 0 1) = 1`. Generalize the expression as in `τ (resQ K' g) 0 0 = a at *`.

Generalize the expression as in `τ (resQ K' g) 0 1 = b at *`. Generalize the expression as in `τ (resQ K' g') 0 0 = a' at *`. Generalize the expression as in `τ (resQ K' g') 0 1 = b' at *`. Generalize the expression as in `τ c 0 0 = p at *`. Generalize the expression as in `τ c 0 1 = q at *`.

Take the linear combination `(a + b) * (p + q) * (e0 - e1) + f2 - (a + b) * (a' + b' - a + b) * f1`. Rewrite using `[hτ.val g, hτ.val g']`. Conclude with `congrArg (fun z : c₁.O => (z : Qbar l)) key` after adjusting the coercions.
-/
private theorem kap_anti {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {K' : IntermediateField ℚ Ω} [NumberField K'] {g0 : G ℚ Ω} {m : ℕ} {c₁ : Coef l} {κ : G K' Ω →* (Qbar l)ˣ}
    {τ : G ℚ Ω →* Sd.S3.M2 c₁.O} {s} (hτ : TauDat ι K' g0 m c₁ τ s κ) {c : G ℚ Ω} (hc : c ∉ K'.fixingSubgroup) {g g' : G K' Ω}
    (h : resQ K' g' = c * resQ K' g * c⁻¹) : (κ g : Qbar l) * κ g' = 1 := by
  have hf : ∀ x, τ x 0 0 ^ 2 - τ x 1 0 ^ 2 = 1 := fun x => by
    have h := congrFun (congrFun (hτ.form x) 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h
    linear_combination h
  have hg : resQ K' g ∈ K'.fixingSubgroup := fun y => g.commutes y
  have e : τ (resQ K' g') * τ c = τ c * τ (resQ K' g) := by
    rw [h, ← map_mul, ← map_mul, inv_mul_cancel_right]
  have hg' : resQ K' g' ∈ K'.fixingSubgroup := fun y => g'.commutes y
  have e0 := congrFun (congrFun e 0) 0
  have e1 := congrFun (congrFun e 0) 1
  have f1 := hf c
  have f2 := hf (resQ K' g)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, (hτ.off c hc).1, (hτ.off c hc).2, (hτ.on _ hg).1, (hτ.on _ hg).2] at e0 e1 f1 f2
  have key : (τ (resQ K' g) 0 0 + τ (resQ K' g) 0 1) * (τ (resQ K' g') 0 0 + τ (resQ K' g') 0 1) = 1 := by
    generalize τ (resQ K' g) 0 0 = a at *
    generalize τ (resQ K' g) 0 1 = b at *
    generalize τ (resQ K' g') 0 0 = a' at *
    generalize τ (resQ K' g') 0 1 = b' at *
    generalize τ c 0 0 = p at *
    generalize τ c 0 1 = q at *
    linear_combination (a + b) * (p + q) * (e0 - e1) + f2 - (a + b) * (a' + b' - a + b) * f1
  rw [hτ.val g, hτ.val g']
  exact_mod_cast congrArg (fun z : c₁.O => (z : Qbar l)) key
/- English proof (translation)
Introduce `P Ω _ _ _ l _ ι K' _ _ hK ρ hρ ha g0 m c₁ κ τ s hτ`. Take `⟨c, hc⟩` from `conj_ex Ω`. Set `J : GL (Fin 2) (Qbar l)` to `Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two])`. Use `⟨ℚ, _, _, _, _, inferInstance, inferInstance, inferInstance, _, c, J * ρ c⁻¹, det_alg P ι ρ hρ ha, fun a b h h' => auSign _ a b h h', hc, fun g g' h => ?_⟩` and prove the remaining obligations. Establish `h' : resQ K' g' = c * resQ K' g * c⁻¹` using `h`.

Establish `hk` using `kap_anti hτ (conj_off K' hK hc) h'`. Establish `e : ρ c⁻¹ * ρ (resQ K' g') = ρ (resQ K' g) * ρ c⁻¹` using `by rw [h', ← map_mul, ← map_mul]; congr 1; group`. Establish `e' : (ρ c⁻¹).val * (ρ (resQ K' g')).val = (ρ (resQ K' g)).val * (ρ c⁻¹).val` using `congrArg Units.val e`. Establish `hp : (ρ (resQ K' g)).valᵀ * J.val * (ρ (resQ K' g)).val = (ρ (resQ K' g)).val.det • J.val` using `pair_plane _`. Establish `hd : (((Matrix.GeneralLinearGroup.det.comp ρ).comp (resG ℚ K' Ω) g : (Qbar l)ˣ) : Qbar l) = (ρ (resQ K' g)).val.det` using `rfl`.

Rewrite using `[hd, tw_val, tw_val, MonoidHom.comp_apply, MonoidHom.comp_apply, Units.val_mul, ← Matrix.smul_mul, ← hp, Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hk, one_smul]`. Simplify using `only [Matrix.mul_assoc, e']`.
-/
theorem UpperTheory.V.Cu.polOf4_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Cu.PolOf4 := by
  intro P Ω _ _ _ l _ ι K' _ _ hK ρ hρ ha g0 m c₁ κ τ s hτ
  obtain ⟨c, hc⟩ := conj_ex Ω
  let J : GL (Fin 2) (Qbar l) := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two])
  refine ⟨ℚ, _, _, _, _, inferInstance, inferInstance, inferInstance, _, c, J * ρ c⁻¹, det_alg P ι ρ hρ ha,
    fun a b h h' => auSign _ a b h h', hc, fun g g' h => ?_⟩
  have h' : resQ K' g' = c * resQ K' g * c⁻¹ := h
  have hk := kap_anti hτ (conj_off K' hK hc) h'
  have e : ρ c⁻¹ * ρ (resQ K' g') = ρ (resQ K' g) * ρ c⁻¹ := by rw [h', ← map_mul, ← map_mul]; congr 1; group
  have e' : (ρ c⁻¹).val * (ρ (resQ K' g')).val = (ρ (resQ K' g)).val * (ρ c⁻¹).val := congrArg Units.val e
  have hp : (ρ (resQ K' g)).valᵀ * J.val * (ρ (resQ K' g)).val = (ρ (resQ K' g)).val.det • J.val := pair_plane _
  have hd : (((Matrix.GeneralLinearGroup.det.comp ρ).comp (resG ℚ K' Ω) g : (Qbar l)ˣ) : Qbar l) = (ρ (resQ K' g)).val.det := rfl
  rw [hd, tw_val, tw_val, MonoidHom.comp_apply, MonoidHom.comp_apply, Units.val_mul, ← Matrix.smul_mul, ← hp,
    Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hk, one_smul]
  simp only [Matrix.mul_assoc, e']
end
end
