import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastAlt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemMIdealOverIff
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwinRestrictionPoints
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationPoint
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockEqChartRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver chartRingOver)
open IndefiniteRowSideFullHecke.Kleiman2 (locIn modelPts ResField)

noncomputable section

namespace SpecialCurvesLift

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[coeff_homogeneousComponent, coeff_map, coeff_map, coeff_homogeneousComponent]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem homogeneousComponent_map' {σ R R' : Type*} [CommSemiring R] [CommSemiring R'] (f : R →+* R')
    (d : ℕ) (p : MvPolynomial σ R) :
    homogeneousComponent d (map f p) = map f (homogeneousComponent d p) := by
  ext m
  rw [coeff_homogeneousComponent, coeff_map, coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[coeff_weightedHomogeneousComponent, coeff_map, coeff_map, coeff_weightedHomogeneousComponent]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem weightedHomogeneousComponent_map' {σ M R R' : Type*} [AddCommMonoid M] [CommSemiring R]
    [CommSemiring R'] (w : σ → M) (f : R →+* R') (b : M) (p : MvPolynomial σ R) :
    weightedHomogeneousComponent w b (map f p) = map f (weightedHomogeneousComponent w b p) := by
  classical
  ext m
  rw [coeff_weightedHomogeneousComponent, coeff_map, coeff_map, coeff_weightedHomogeneousComponent]
  split_ifs <;> simp

/- English proof (translation)
Establish `hw : ∀ e : (Σ _ : Unit, Fin (N + 1)) →₀ ℕ, Finsupp.weight (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1))) e = fun _ => e.degree`. Introduce `e`. Use function extensionality and compare the values at `u`. Rewrite using `[Finsupp.weight_apply, Finsupp.degree, Finsupp.sum, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations.

Simplify using `[NumbersDVR.blockWeight]`. Use extensionality with `e`. Rewrite using `[coeff_weightedHomogeneousComponent, coeff_homogeneousComponent, hw e]`. Use `congr 1`. Apply `propext` to reduce the goal to its premises.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `congrFun h ()`. Introduce `h`. Use function extensionality and compare the values at `u`.

Conclude with `h`.
-/
theorem weightedHomogeneousComponent_oneBlock {R : Type} [CommRing R] {N : ℕ} (d : ℕ)
    (q : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) R) :
    weightedHomogeneousComponent (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1))) (fun _ => d) q =
      homogeneousComponent d q := by
  have hw : ∀ e : (Σ _ : Unit, Fin (N + 1)) →₀ ℕ,
      Finsupp.weight (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1))) e = fun _ => e.degree := by
    intro e
    funext u
    rw [Finsupp.weight_apply, Finsupp.degree, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [NumbersDVR.blockWeight]
  ext e
  rw [coeff_weightedHomogeneousComponent, coeff_homogeneousComponent, hw e]
  congr 1
  apply propext
  constructor
  · intro h; exact congrFun h ()
  · intro h; funext u; exact h

/- English proof (translation)
Establish `key : ∀ (w : Fin (N + 1) → L) (s : L), Kleiman.cone (S` using `S) (fun i => w i * s) = ((Polynomial.aeval (Polynomial.C s * Polynomial.X)).restrictScalars S).comp (Kleiman.cone (S := S) w) := by`. Introduce `w s`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Simplify using `[Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap]`.

Expand and normalize the polynomial expressions, which then agree. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h2` using `congrArg (Polynomial.aeval (Polynomial.C t⁻¹ * Polynomial.X)) h`. Rewrite `h2` using `[map_zero]`.

Establish `e` using `AlgHom.congr_fun (key (fun i => v i * t) t⁻¹) g`. Rewrite `e` using `[AlgHom.comp_apply, AlgHom.restrictScalars_apply]`. Establish `hv : (fun i => (fun i => v i * t) i * t⁻¹) = v`. Use function extensionality and compare the values at `i`. Simplify using `[ht]`.

Rewrite `e` using `[hv]`. Rewrite using `[e]`. Conclude with `h2`. Introduce `h`. Rewrite using `[key, AlgHom.comp_apply, h, map_zero]`.
-/
theorem cone_mul_eq_zero_iff {S : Type*} [CommRing S] {L : Type*} [Field L] [Algebra S L] {N : ℕ}
    (v : Fin (N + 1) → L) {t : L} (ht : t ≠ 0) (g : Kleiman.Poly S N) :
    Kleiman.cone (S := S) (fun i => v i * t) g = 0 ↔ Kleiman.cone (S := S) v g = 0 := by
  have key : ∀ (w : Fin (N + 1) → L) (s : L), Kleiman.cone (S := S) (fun i => w i * s) =
      ((Polynomial.aeval (Polynomial.C s * Polynomial.X)).restrictScalars S).comp
        (Kleiman.cone (S := S) w) := by
    intro w s
    apply MvPolynomial.algHom_ext
    intro i
    simp [Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap]
    ring
  constructor
  · intro h
    have h2 := congrArg (Polynomial.aeval (Polynomial.C t⁻¹ * Polynomial.X)) h
    rw [map_zero] at h2
    have e := AlgHom.congr_fun (key (fun i => v i * t) t⁻¹) g
    rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at e
    have hv : (fun i => (fun i => v i * t) i * t⁻¹) = v := by
      funext i
      simp [ht]
    rw [hv] at e
    rw [e]
    exact h2
  · intro h
    rw [key, AlgHom.comp_apply, h, map_zero]

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `⟨p, inferInstance, rfl⟩`.
-/
theorem exists_locIn_eq_of_eq {S Ω : Type*} [CommRing S] [Field Ω] [Algebra S Ω] {A B : Subalgebra S Ω}
    (h : A = B) (p : Ideal A) [p.IsPrime] : ∃ q : Ideal B, q.IsPrime ∧ locIn A p = locIn B q := by
  subst h
  exact ⟨p, inferInstance, rfl⟩

/- English proof (translation)
Unfold `chartRingOver`. Use `congr 1`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨⟨⟩, a⟩, rfl⟩`.

Conclude with `⟨⟨(), e a⟩, rfl⟩`. Introduce and unpack `⟨⟨⟨⟩, a⟩, rfl⟩`. Use `⟨⟨(), e.symm a⟩, ?_⟩` and prove the remaining obligations. Simplify using `[IndefiniteRowSideFullHecke.Kleiman2.oneBlock]`.
-/
theorem chartRingOver_oneBlock_comp {S Ω : Type*} [CommRing S] [Field Ω] [Algebra S Ω] {κ κ' : Type}
    (w : κ' → Ω) (e : κ ≃ κ') (j : κ) :
    chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (w ∘ e)) (fun _ => j) =
      chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock w) (fun _ => e j) := by
  unfold chartRingOver
  congr 1
  ext z
  constructor
  · rintro ⟨⟨⟨⟩, a⟩, rfl⟩
    exact ⟨⟨(), e a⟩, rfl⟩
  · rintro ⟨⟨⟨⟩, a⟩, rfl⟩
    refine ⟨⟨(), e.symm a⟩, ?_⟩
    simp [IndefiniteRowSideFullHecke.Kleiman2.oneBlock]

end SpecialCurvesLift

open SpecialCurvesLift in

/- English proof (translation)
Introduce `O _ _ _ K _ _ ι _ Ω _ _ _ _ y k₀ N e x hx hy P hP hxP`. Set `σ : Fin (N + 1) → (Σ _ : Unit, Fin (N + 1))` to `fun i => ⟨(), i⟩`. Set `φ : Kleiman.Poly O N →+* NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) (IsLocalRing.ResidueField O)` to `(rename σ).toRingHom.comp (MvPolynomial.map (IsLocalRing.residue O))`. Establish `hφ : ∀ g, φ g = rename σ (MvPolynomial.map (IsLocalRing.residue O) g)` using `fun _ => rfl`. Set `pp : Ideal (Kleiman.Poly O N)` to `P.comap φ`.

Establish `: P.IsPrime` using `hP.isPrime`. Establish `hpp : pp.IsPrime` using `Ideal.comap_isPrime _ _`. Establish `hhom : ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp`. Introduce `p hp d`. Rewrite using `[Ideal.mem_comap, hφ, ← homogeneousComponent_map', rename_homogeneousComponent, ← weightedHomogeneousComponent_oneBlock]`.

Conclude with `hP.multiHomog _ hp _`. Establish `hle : Kleiman.primeOf (S` using `O) x ≤ pp := by`. Introduce `f hf`. Rewrite using `[Ideal.mem_comap, hφ, ← map_rename]`. Apply `hxP` to reduce the goal to its premises.

Apply `Ideal.mem_map_of_mem` to reduce the goal to its premises. Establish `hc : (mConeMapOver O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)).comp (rename σ) = ((Polynomial.toMvPolynomial ()).restrictScalars O).comp (Kleiman.cone (S` using `O) x) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Simplify using `[mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, σ]`.

Establish `h1` using `AlgHom.congr_fun hc f`. Rewrite `hf` using `[Kleiman.primeOf_eq, RingHom.mem_ker]`. Rewrite `h1` using `[AlgHom.comp_apply, AlgHom.comp_apply, hf, map_zero]`. Conclude with `h1`. Take `⟨j, hXj⟩` from `hP.relevant ()`.

Establish `hXj' : (X j : Kleiman.Poly O N) ∉ pp`. Rewrite using `[Ideal.mem_comap, hφ, map_X, rename_X]`. Conclude with `hXj`. Establish `hj : x j ≠ 0`. Introduce `h0`.

Apply `hXj'` to reduce the goal to its premises. Apply `hle` to reduce the goal to its premises. Rewrite using `[Kleiman.mem_primeOf_of_isHomogeneous x (isHomogeneous_X O j), aeval_X, h0]`. Take `⟨hcp, hpt⟩` from `Kleiman.PrimeFiltration.Point.proof O Ω N x pp hpp hhom hle j hj hXj'`. Use `hcp` as an intermediate fact.

Establish `hA : chartRingOver O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => j) = Kleiman.chartRing O x (Kleiman.singleChart hj)` using `chartRingOver_oneBlock_eq_chartRing x (fun _ => j) hj`. Set `A₂` to `chartRingOver O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => j)`. Set `τ : A₂ ≃ₐ[O] Kleiman.chartRing O x (Kleiman.singleChart hj)` to `Subalgebra.equivOfEq _ _ hA`. Set `p₂ : Ideal A₂` to `(Kleiman.chartPrime pp hj).comap τ`. Establish `hp₂ : p₂.IsPrime` using `Ideal.comap_isPrime _ _`.

Set `K'` to `ResField O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => j) p₂`. Set `ψ : Kleiman.chartRing O x (Kleiman.singleChart hj) →ₐ[O] K'` to `{ toRingHom := (algebraMap (A₂ ⧸ p₂) K').comp ((Ideal.Quotient.mk p₂).comp τ.symm.toRingEquiv.toRingHom) commutes' := fun a => by`. Express the relevant statement in the definitionally equal form `algebraMap (A₂ ⧸ p₂) (FractionRing (A₂ ⧸ p₂)) (Ideal.Quotient.mk p₂ (τ.symm (algebraMap O _ a))) = algebraMap O (FractionRing (A₂ ⧸ p₂)) a`. Rewrite using `[AlgEquiv.commutes]`. Conclude with `(IsScalarTower.algebraMap_apply O (A₂ ⧸ p₂) (FractionRing (A₂ ⧸ p₂)) a).symm }`.

Establish `hker : RingHom.ker ψ = Kleiman.chartPrime pp hj`. Use extensionality with `a`. Rewrite using `[RingHom.mem_ker]`. Express the relevant statement in the definitionally equal form `algebraMap (A₂ ⧸ p₂) (FractionRing (A₂ ⧸ p₂)) (Ideal.Quotient.mk p₂ (τ.symm a)) = 0 ↔ _`. Rewrite using `[IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap, AlgEquiv.apply_symm_apply]`.

Establish `hv` using `hpt K' ψ hker`. Set `z` to `locIn A₂ p₂`. Establish `hA' : A₂ = chartRingOver O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => e.symm j)`. Establish `h` using `chartRingOver_oneBlock_comp (S := O) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) e.symm j`. Rewrite `h` using `[← hx]`.

Conclude with `h`. Take `⟨p₃, hp₃, hz₃⟩` from `exists_locIn_eq_of_eq hA' p₂`. Establish `hxj : x j = y ⟨k₀, e.symm j⟩` using `by rw [hx]; rfl`. Establish `hzx : z ∈ modelPts O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀))` using `⟨fun _ => e.symm j, fun _ => by change y ⟨k₀, e.symm j⟩ ≠ 0; rw [← hxj]; exact hj, p₃, hp₃, hz₃⟩`. Establish `hSM : modelPts O y = modelPts O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀))` using `hy.2`.

Rewrite `hzx` using `[← hSM]`. Take `⟨c', hc', p', hp', hz'⟩` from `hzx`. Establish `hmem : ∀ q : Σ k, ι k, y q / y ⟨q.1, c' q.1⟩ ∈ z`. Introduce `q`. Rewrite using `[hz']`.

Conclude with `RestrictionPoints.mem_locIn_of_mem _ p' (RestrictionPoints.ratio_mem (S := O) y c' q)`. Establish `hmemA : ∀ a ∈ A₂, a ∈ z` using `fun a ha => RestrictionPoints.mem_locIn_of_mem A₂ p₂ ha`. Establish `hmemx : ∀ i, x i / x j ∈ z` using `fun i => hmemA _ (RestrictionPoints.ratio_mem (S := O) (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => j) ⟨(), i⟩)`. Set `R` to `resMap (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => j) p₂`. Set `yb : (Σ k, ι k) → K'` to `fun q => R ⟨_, hmem q⟩`.

Establish `hvR : ∀ i, ψ (Kleiman.ratio hj i) = R ⟨x i / x j, hmemx i⟩` using `fun i => (resMap_of_mem (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => j) p₂ (τ.symm (Kleiman.ratio hj i)) (hmemx i)).symm`. Establish `hyb1 : ∀ k, yb ⟨k, c' k⟩ = 1`. Introduce `k`. Establish `: (⟨_, hmem ⟨k, c' k⟩⟩ : z) = 1` using `Subtype.ext (div_self (hc' k))`. Express the relevant statement in the definitionally equal form `R _ = 1`.

Rewrite using `[this, map_one]`. Set `t : K'` to `yb ⟨k₀, e.symm j⟩`. Establish `ht : t ≠ 0`. Establish `hb : y ⟨k₀, c' k₀⟩ / x j ∈ z`. Establish `h` using `hmemx (e (c' k₀))`.

Establish `h2 : x (e (c' k₀)) = y ⟨k₀, c' k₀⟩` using `by rw [hx]; simp [IndefiniteRowSideFullHecke.Kleiman2.blockVec]`. Rewrite `h` using `[h2]`. Then use the resulting hypothesis. Establish `h1 : t * R ⟨_, hb⟩ = 1`. Express the relevant statement in the definitionally equal form `R _ * R _ = 1`. Rewrite using `[← map_mul, ← map_one R]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `y ⟨k₀, e.symm j⟩ / y ⟨k₀, c' k₀⟩ * (y ⟨k₀, c' k₀⟩ / x j) = 1`. Rewrite using `[hxj]`. Use `hc' k₀` as an intermediate fact.

Establish `hj' : y ⟨k₀, e.symm j⟩ ≠ 0` using `hxj ▸ hj`. Clear the denominators using the available nonvanishing facts. Conclude with `left_ne_zero_of_mul_eq_one h1`. Establish `hyv : ∀ i, yb ⟨k₀, e.symm i⟩ = ψ (Kleiman.ratio hj i) * t`. Introduce `i`.

Rewrite using `[hvR]`. Express the relevant statement in the definitionally equal form `R _ = R _ * R _`. Rewrite using `[← map_mul]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `y ⟨k₀, e.symm i⟩ / y ⟨k₀, c' k₀⟩ = x i / x j * (y ⟨k₀, e.symm j⟩ / y ⟨k₀, c' k₀⟩)`. Establish `hxi : x i = y ⟨k₀, e.symm i⟩` using `by rw [hx]; rfl`. Rewrite using `[hxi, ← hxj]`. Use `hc' k₀` as an intermediate fact. Clear the denominators using the available nonvanishing facts.

Establish `hmO : ∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O K' a = 0`. Introduce `a ha`. Establish `hC : (C a : Kleiman.Poly O N) ∈ pp`. Rewrite using `[Ideal.mem_comap, hφ, map_C, rename_C]`. Establish `h0 : IsLocalRing.residue O a = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr ha`.

Rewrite using `[h0, C_0]`. Conclude with `P.zero_mem`. Rewrite `hC` using `[← hv, Kleiman.mem_primeOf_of_isHomogeneous _ (isHomogeneous_C _ a), aeval_C]`. Conclude with `hC`. Set `lam : IsLocalRing.ResidueField O →+* K'` to `Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) (algebraMap O K') hmO`.

Set `_ : Algebra (IsLocalRing.ResidueField O) K'` to `lam.toAlgebra`. Establish `hlam : ∀ a : O, algebraMap (IsLocalRing.ResidueField O) K' (IsLocalRing.residue O a) = algebraMap O K' a` using `fun a => Ideal.Quotient.lift_mk _ _ _`. Use `⟨mIdealOver (IsLocalRing.ResidueField O) yb, isMultiProjPrime_mIdealOver yb (fun k => ⟨c' k, by rw [hyb1 k]; exact one_ne_zero⟩), ?_, ?_⟩` and prove the remaining obligations. Set `f0 : O →+* z` to `(algebraMap O Ω).codRestrict z (fun a => hmemA _ (A₂.algebraMap_mem a))`. Establish `hR : (algebraMap (IsLocalRing.ResidueField O) K').comp (IsLocalRing.residue O) = R.comp f0`.

Use extensionality with `a`. Rewrite using `[RingHom.comp_apply, hlam, RingHom.comp_apply]`. Conclude with `(resMap_algebraMap (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => j) p₂ a _).symm`. Rewrite using `[NumbersDVR.specialIdeal, Ideal.map_le_iff_le_comap]`. Introduce `f hf`.

Rewrite using `[Ideal.mem_comap, mem_mIdealOver_iff]`. Rewrite `hf` using `[mem_mIdealOver_iff]`. Introduce `b`. Establish `hg` using `weightedHomogeneousComponent_isWeightedHomogeneous (w := NumbersDVR.blockWeight ι) b f`. Establish `h0 : eval₂ f0 (fun q => (⟨_, hmem q⟩ : z)) (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f) = 0`.

Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `z.subtype _ = 0`. Rewrite using `[eval₂_comp_left]`. Establish `h1 : z.subtype.comp f0 = algebraMap O Ω` using `by ext a; rfl`. Establish `h2 : (z.subtype ∘ fun q => (⟨_, hmem q⟩ : z)) = fun q => y q * (fun k => (y ⟨k, c' k⟩)⁻¹) q.1`.

Use function extensionality and compare the values at `q`. Conclude with `div_eq_mul_inv _ _`. Rewrite using `[h1, h2, ← aeval_def]`. Conclude with `(aeval_mul_block y (fun k => (y ⟨k, c' k⟩)⁻¹) b _ hg).trans (by rw [hf b, zero_mul])`. Rewrite using `[weightedHomogeneousComponent_map', aeval_def, eval₂_map, hR]`.

Express the relevant statement in the definitionally equal form `eval₂ (R.comp f0) (R ∘ fun q => (⟨_, hmem q⟩ : z)) _ = 0`. Rewrite using `[← eval₂_comp_left, h0, map_zero]`. Use extensionality with `f`. Rewrite using `[baseComap, Ideal.mem_comap]`. Choose the witnesses or unpack the hypotheses as in `⟨g, rfl⟩ : ∃ g : Kleiman.Poly O N, φ g = f := by`.

Take `⟨g, hg⟩` from `MvPolynomial.map_surjective (IsLocalRing.residue O) Ideal.Quotient.mk_surjective (rename (fun v : Σ _ : Unit, Fin (N + 1) => v.2) f)`. Use `⟨g, ?_⟩` and prove the remaining obligations. Rewrite using `[hφ, hg, rename_rename]`. Establish `hid : (σ ∘ fun v : Σ _ : Unit, Fin (N + 1) => v.2) = id`. Use function extensionality and compare the values at `⟨⟨⟩, i⟩`.

Both sides reduce to the same expression. Rewrite using `[hid, rename_id]`. Both sides reduce to the same expression. Set `v'' : Fin (N + 1) → K'` to `fun i => yb ⟨k₀, e.symm i⟩`. Establish `hkey : ((mConeMapOver (IsLocalRing.ResidueField O) yb).toRingHom.comp ((rename fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)).toRingHom.comp φ)) = (Polynomial.toMvPolynomial k₀).toRingHom.comp (Kleiman.cone (S` using `O) v'').toRingHom := by`.

Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[hφ, mConeMapOver, Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, hlam, v'']`. Introduce `i`. Simplify using `[hφ, mConeMapOver, Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, v'', σ]`.

Establish `hk` using `RingHom.congr_fun hkey g`. Express the relevant statement in the definitionally equal form `mConeMapOver (IsLocalRing.ResidueField O) yb _ = 0 ↔ g ∈ pp`. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hk`. Rewrite using `[hk, map_eq_zero_iff _ (Polynomial.toMvPolynomial_injective k₀), ← hv, Kleiman.primeOf_eq, RingHom.mem_ker]`. Establish `hv'' : v'' = fun i => ψ (Kleiman.ratio hj i) * t` using `funext hyv`.

Rewrite using `[hv'']`. Conclude with `cone_mul_eq_zero_iff _ ht g`.
-/
theorem SpecialCurvesLift.proof : SpecialCurvesLift.Statement := by
  intro O _ _ _ K _ _ ι _ Ω _ _ _ _ y k₀ N e x hx hy P hP hxP
  classical
  let σ : Fin (N + 1) → (Σ _ : Unit, Fin (N + 1)) := fun i => ⟨(), i⟩
  let φ : Kleiman.Poly O N →+* NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) (IsLocalRing.ResidueField O) :=
    (rename σ).toRingHom.comp (MvPolynomial.map (IsLocalRing.residue O))
  have hφ : ∀ g, φ g = rename σ (MvPolynomial.map (IsLocalRing.residue O) g) := fun _ => rfl
  let pp : Ideal (Kleiman.Poly O N) := P.comap φ
  have : P.IsPrime := hP.isPrime
  have hpp : pp.IsPrime := Ideal.comap_isPrime _ _
  have hhom : ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp := by
    intro p hp d
    rw [Ideal.mem_comap, hφ, ← homogeneousComponent_map', rename_homogeneousComponent,
      ← weightedHomogeneousComponent_oneBlock]
    exact hP.multiHomog _ hp _
  have hle : Kleiman.primeOf (S := O) x ≤ pp := by
    intro f hf
    rw [Ideal.mem_comap, hφ, ← map_rename]
    apply hxP
    apply Ideal.mem_map_of_mem
    have hc : (mConeMapOver O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)).comp (rename σ) =
        ((Polynomial.toMvPolynomial ()).restrictScalars O).comp (Kleiman.cone (S := O) x) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, σ]
    have h1 := AlgHom.congr_fun hc f
    rw [Kleiman.primeOf_eq, RingHom.mem_ker] at hf
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hf, map_zero] at h1
    exact h1
  obtain ⟨j, hXj⟩ := hP.relevant ()
  have hXj' : (X j : Kleiman.Poly O N) ∉ pp := by
    rw [Ideal.mem_comap, hφ, map_X, rename_X]
    exact hXj
  have hj : x j ≠ 0 := by
    intro h0
    apply hXj'
    apply hle
    rw [Kleiman.mem_primeOf_of_isHomogeneous x (isHomogeneous_X O j), aeval_X, h0]
  obtain ⟨hcp, hpt⟩ := Kleiman.PrimeFiltration.Point.proof O Ω N x pp hpp hhom hle j hj hXj'
  have := hcp

  have hA : chartRingOver O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => j) = Kleiman.chartRing O x (Kleiman.singleChart hj) :=
    chartRingOver_oneBlock_eq_chartRing x (fun _ => j) hj
  let A₂ := chartRingOver O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => j)
  let τ : A₂ ≃ₐ[O] Kleiman.chartRing O x (Kleiman.singleChart hj) := Subalgebra.equivOfEq _ _ hA
  let p₂ : Ideal A₂ := (Kleiman.chartPrime pp hj).comap τ
  have hp₂ : p₂.IsPrime := Ideal.comap_isPrime _ _
  let K' := ResField O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => j) p₂
  let ψ : Kleiman.chartRing O x (Kleiman.singleChart hj) →ₐ[O] K' :=
    { toRingHom := (algebraMap (A₂ ⧸ p₂) K').comp ((Ideal.Quotient.mk p₂).comp τ.symm.toRingEquiv.toRingHom)
      commutes' := fun a => by
        change algebraMap (A₂ ⧸ p₂) (FractionRing (A₂ ⧸ p₂)) (Ideal.Quotient.mk p₂ (τ.symm (algebraMap O _ a))) =
          algebraMap O (FractionRing (A₂ ⧸ p₂)) a
        rw [AlgEquiv.commutes]
        exact (IsScalarTower.algebraMap_apply O (A₂ ⧸ p₂) (FractionRing (A₂ ⧸ p₂)) a).symm }
  have hker : RingHom.ker ψ = Kleiman.chartPrime pp hj := by
    ext a
    rw [RingHom.mem_ker]
    change algebraMap (A₂ ⧸ p₂) (FractionRing (A₂ ⧸ p₂)) (Ideal.Quotient.mk p₂ (τ.symm a)) = 0 ↔ _
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap,
      AlgEquiv.apply_symm_apply]
  have hv := hpt K' ψ hker

  let z := locIn A₂ p₂
  have hA' : A₂ = chartRingOver O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => e.symm j) := by
    have h := chartRingOver_oneBlock_comp (S := O) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) e.symm j
    rw [← hx] at h
    exact h
  obtain ⟨p₃, hp₃, hz₃⟩ := exists_locIn_eq_of_eq hA' p₂
  have hxj : x j = y ⟨k₀, e.symm j⟩ := by rw [hx]; rfl
  have hzx : z ∈ modelPts O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) :=
    ⟨fun _ => e.symm j, fun _ => by change y ⟨k₀, e.symm j⟩ ≠ 0; rw [← hxj]; exact hj, p₃, hp₃, hz₃⟩
  have hSM : modelPts O y = modelPts O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) := hy.2
  rw [← hSM] at hzx
  obtain ⟨c', hc', p', hp', hz'⟩ := hzx
  have hmem : ∀ q : Σ k, ι k, y q / y ⟨q.1, c' q.1⟩ ∈ z := by
    intro q
    rw [hz']
    exact RestrictionPoints.mem_locIn_of_mem _ p' (RestrictionPoints.ratio_mem (S := O) y c' q)
  have hmemA : ∀ a ∈ A₂, a ∈ z := fun a ha => RestrictionPoints.mem_locIn_of_mem A₂ p₂ ha
  have hmemx : ∀ i, x i / x j ∈ z := fun i =>
    hmemA _ (RestrictionPoints.ratio_mem (S := O) (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => j) ⟨(), i⟩)

  let R := resMap (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => j) p₂
  let yb : (Σ k, ι k) → K' := fun q => R ⟨_, hmem q⟩
  have hvR : ∀ i, ψ (Kleiman.ratio hj i) = R ⟨x i / x j, hmemx i⟩ :=
    fun i => (resMap_of_mem (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => j) p₂ (τ.symm (Kleiman.ratio hj i)) (hmemx i)).symm
  have hyb1 : ∀ k, yb ⟨k, c' k⟩ = 1 := by
    intro k
    have : (⟨_, hmem ⟨k, c' k⟩⟩ : z) = 1 := Subtype.ext (div_self (hc' k))
    change R _ = 1
    rw [this, map_one]
  let t : K' := yb ⟨k₀, e.symm j⟩
  have ht : t ≠ 0 := by
    have hb : y ⟨k₀, c' k₀⟩ / x j ∈ z := by
      have h := hmemx (e (c' k₀))
      have h2 : x (e (c' k₀)) = y ⟨k₀, c' k₀⟩ := by rw [hx]; simp [IndefiniteRowSideFullHecke.Kleiman2.blockVec]
      rwa [h2] at h
    have h1 : t * R ⟨_, hb⟩ = 1 := by
      change R _ * R _ = 1
      rw [← map_mul, ← map_one R]
      congr 1
      apply Subtype.ext
      change y ⟨k₀, e.symm j⟩ / y ⟨k₀, c' k₀⟩ * (y ⟨k₀, c' k₀⟩ / x j) = 1
      rw [hxj]
      have := hc' k₀
      have hj' : y ⟨k₀, e.symm j⟩ ≠ 0 := hxj ▸ hj
      field_simp
    exact left_ne_zero_of_mul_eq_one h1
  have hyv : ∀ i, yb ⟨k₀, e.symm i⟩ = ψ (Kleiman.ratio hj i) * t := by
    intro i
    rw [hvR]
    change R _ = R _ * R _
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    change y ⟨k₀, e.symm i⟩ / y ⟨k₀, c' k₀⟩ = x i / x j * (y ⟨k₀, e.symm j⟩ / y ⟨k₀, c' k₀⟩)
    have hxi : x i = y ⟨k₀, e.symm i⟩ := by rw [hx]; rfl
    rw [hxi, ← hxj]
    have := hc' k₀
    field_simp

  have hmO : ∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O K' a = 0 := by
    intro a ha
    have hC : (C a : Kleiman.Poly O N) ∈ pp := by
      rw [Ideal.mem_comap, hφ, map_C, rename_C]
      have h0 : IsLocalRing.residue O a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
      rw [h0, C_0]
      exact P.zero_mem
    rw [← hv, Kleiman.mem_primeOf_of_isHomogeneous _ (isHomogeneous_C _ a), aeval_C] at hC
    exact hC
  let lam : IsLocalRing.ResidueField O →+* K' :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) (algebraMap O K') hmO
  let _ : Algebra (IsLocalRing.ResidueField O) K' := lam.toAlgebra
  have hlam : ∀ a : O, algebraMap (IsLocalRing.ResidueField O) K' (IsLocalRing.residue O a) = algebraMap O K' a :=
    fun a => Ideal.Quotient.lift_mk _ _ _
  refine ⟨mIdealOver (IsLocalRing.ResidueField O) yb,
    isMultiProjPrime_mIdealOver yb (fun k => ⟨c' k, by rw [hyb1 k]; exact one_ne_zero⟩), ?_, ?_⟩
  ·
    let f0 : O →+* z := (algebraMap O Ω).codRestrict z (fun a => hmemA _ (A₂.algebraMap_mem a))
    have hR : (algebraMap (IsLocalRing.ResidueField O) K').comp (IsLocalRing.residue O) = R.comp f0 := by
      ext a
      rw [RingHom.comp_apply, hlam, RingHom.comp_apply]
      exact (resMap_algebraMap (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => j) p₂ a _).symm
    rw [NumbersDVR.specialIdeal, Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, mem_mIdealOver_iff]
    rw [mem_mIdealOver_iff] at hf
    intro b
    have hg := weightedHomogeneousComponent_isWeightedHomogeneous (w := NumbersDVR.blockWeight ι) b f
    have h0 : eval₂ f0 (fun q => (⟨_, hmem q⟩ : z)) (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f) = 0 := by
      apply Subtype.ext
      change z.subtype _ = 0
      rw [eval₂_comp_left]
      have h1 : z.subtype.comp f0 = algebraMap O Ω := by ext a; rfl
      have h2 : (z.subtype ∘ fun q => (⟨_, hmem q⟩ : z)) = fun q => y q * (fun k => (y ⟨k, c' k⟩)⁻¹) q.1 := by
        funext q
        exact div_eq_mul_inv _ _
      rw [h1, h2, ← aeval_def]
      exact (aeval_mul_block y (fun k => (y ⟨k, c' k⟩)⁻¹) b _ hg).trans (by rw [hf b, zero_mul])
    rw [weightedHomogeneousComponent_map', aeval_def, eval₂_map, hR]
    change eval₂ (R.comp f0) (R ∘ fun q => (⟨_, hmem q⟩ : z)) _ = 0
    rw [← eval₂_comp_left, h0, map_zero]
  ·
    ext f
    rw [baseComap, Ideal.mem_comap]
    obtain ⟨g, rfl⟩ : ∃ g : Kleiman.Poly O N, φ g = f := by
      obtain ⟨g, hg⟩ := MvPolynomial.map_surjective (IsLocalRing.residue O) Ideal.Quotient.mk_surjective
        (rename (fun v : Σ _ : Unit, Fin (N + 1) => v.2) f)
      refine ⟨g, ?_⟩
      rw [hφ, hg, rename_rename]
      have hid : (σ ∘ fun v : Σ _ : Unit, Fin (N + 1) => v.2) = id := by
        funext ⟨⟨⟩, i⟩
        rfl
      rw [hid, rename_id]
      rfl
    let v'' : Fin (N + 1) → K' := fun i => yb ⟨k₀, e.symm i⟩
    have hkey : ((mConeMapOver (IsLocalRing.ResidueField O) yb).toRingHom.comp
        ((rename fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)).toRingHom.comp φ)) =
        (Polynomial.toMvPolynomial k₀).toRingHom.comp (Kleiman.cone (S := O) v'').toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [hφ, mConeMapOver, Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, hlam, v'']
      · intro i
        simp [hφ, mConeMapOver, Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, v'', σ]
    have hk := RingHom.congr_fun hkey g
    change mConeMapOver (IsLocalRing.ResidueField O) yb _ = 0 ↔ g ∈ pp
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hk
    rw [hk, map_eq_zero_iff _ (Polynomial.toMvPolynomial_injective k₀), ← hv, Kleiman.primeOf_eq,
      RingHom.mem_ker]
    have hv'' : v'' = fun i => ψ (Kleiman.ratio hj i) * t := funext hyv
    rw [hv'']
    exact cone_mul_eq_zero_iff _ ht g

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
