import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.RepNewform
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.NewformOfAdmissibleTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.NewformFlagLocalOfIrreducible
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.UnramifiedAlgebraicWeights
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.SatakeRootsLocalCorrespondence
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.NewformUnitRootNotRootOfUnityOddWeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.AdmissibleTwistByDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

open Polynomial Pointwise

namespace GlobalTheory.Ord2.SrcForm

open TwDet

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h g v hv`. Use `W.smul_mem ((χ g : k)⁻¹) (h g v hv)` as an intermediate fact. Rewrite `this` using `[tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]`. Then use the resulting hypothesis. Introduce `h g v hv`.

Rewrite using `[tw_val, Matrix.smul_mulVec]`. Conclude with `W.smul_mem _ (h g v hv)`.
-/
theorem isInv_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (W : Submodule k (Fin n → k)) : IsInv (tw r χ) W ↔ IsInv r W := by
  constructor
  · intro h g v hv
    have := W.smul_mem ((χ g : k)⁻¹) (h g v hv)
    rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
  · intro h g v hv
    rw [tw_val, Matrix.smul_mulVec]
    exact W.smul_mem _ (h g v hv)

/- English proof (translation)
Introduce `W hW`. Take `⟨W', hW', hc⟩` from `h W ((isInv_tw r χ W).2 hW)`. Conclude with `⟨W', (isInv_tw r χ W').1 hW', hc⟩`.
-/
theorem ss_of_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (h : IsSSRep (tw r χ)) : IsSSRep r := by
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W ((isInv_tw r χ W).2 hW)
  exact ⟨W', (isInv_tw r χ W').1 hW', hc⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1, fun _ _ _ => trivial, fun W' hW' hi => h.2.2 W' hW' fun g v hv => (isInv_tw r χ W').1 hi g v hv⟩`.
-/
theorem irr_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (H : Subgroup Γ)
    (h : IsIrr (r.comp H.subtype)) : IsIrr (tw r χ) :=
  ⟨h.1, fun _ _ _ => trivial, fun W' hW' hi => h.2.2 W' hW' fun g v hv => (isInv_tw r χ W').1 hi g v hv⟩

/- English proof (translation)
Establish `h0 : Ideal.span {((N : ℕ) : 𝓞 ℚ)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hN` after adjusting the coercions. Use `Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, not_not] at hw`.

Conclude with `Ideal.dvd_span_singleton.2 hw`.
-/
theorem ev_not_mem (N : ℕ) (hN : N ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ((N : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  have h0 : Ideal.span {((N : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq, not_not] at hw
  exact Ideal.dvd_span_singleton.2 hw

/- English proof (translation)
Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Both sides reduce to the same expression.
-/
theorem normV_eq (w : HeightOneSpectrum (𝓞 ℚ)) : normV w = Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

/- English proof (translation)
Introduce and unpack `⟨c, hc⟩`. Apply `hwM` to reduce the goal to its premises. Rewrite using `[hc, Nat.cast_mul, normV_eq]`. Conclude with `w.asIdeal.mul_mem_right _ (Ideal.absNorm_mem _)`.
-/
theorem not_dvd_of_not_mem {M : ℕ} {w : Pl} (hwM : ((M : ℕ) : 𝓞 ℚ) ∉ w.asIdeal) : ¬ normV w ∣ M := by
  rintro ⟨c, hc⟩
  apply hwM
  rw [hc, Nat.cast_mul, normV_eq]
  exact w.asIdeal.mul_mem_right _ (Ideal.absNorm_mem _)

/- English proof (translation)
Establish `hpr : Prime (p : 𝓞 ℚ)`. Establish `e : (p : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (p : ℤ)` using `by simp`. Rewrite using `[e]`. Conclude with `(MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr (Nat.prime_iff_prime_int.1 hp)`. Establish `hm : (Ideal.span {(p : 𝓞 ℚ)}).IsMaximal` using `((Ideal.span_singleton_prime hpr.ne_zero).2 hpr).isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)`.

Conclude with `(hm.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)).symm`.
-/
theorem asIdeal_eq {p : ℕ} (hp : p.Prime) {w : Pl} (hw : ((p : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) :
    w.asIdeal = Ideal.span {((p : ℕ) : 𝓞 ℚ)} := by
  have hpr : Prime (p : 𝓞 ℚ) := by
    have e : (p : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (p : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr (Nat.prime_iff_prime_int.1 hp)
  have hm : (Ideal.span {(p : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpr.ne_zero).2 hpr).isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
  exact (hm.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)).symm

/- English proof (translation)
Rewrite using `[normV_eq, asIdeal_eq hp hw, Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]`.
-/
theorem normV_of_mem {p : ℕ} (hp : p.Prime) {w : Pl} (hw : ((p : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : normV w = p := by
  rw [normV_eq, asIdeal_eq hp hw, Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]

/- English proof (translation)
Establish `hc' : φ c ≠ 0` using `by simpa using hc`. Establish `hcard : B.card = 2`. Establish `h1` using `congrArg natDegree h`. Rewrite `h1` using `[natDegree_map, Matrix.charpoly_natDegree_eq_dim]`. Establish `h2` using `natDegree_multiset_prod_X_sub_C_eq_card (B.map (φ c * ·))`.

Rewrite `h2` using `[Multiset.map_map]`. Simplify using `only [Function.comp_def, Multiset.card_map] at h2`. Rewrite `h1` using `[h2]`. Simplify using `using h1.symm`. Take `⟨x, y, rfl⟩` from `Multiset.card_eq_two.1 hcard`.

Rewrite `h`, the goal using `[Matrix.charpoly_fin_two]`. Simplify using `only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, Matrix.trace_smul, Matrix.det_smul, smul_eq_mul, map_mul, map_pow, …`. Establish `e0` using `congrArg (eval 0) h`. Establish `e1` using `congrArg (eval 1) h`. Simplify using `only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at e0 e1`.

Establish `hd : φ M.det = x * y`. Apply `mul_left_cancel₀ (pow_ne_zero 2 hc')` to reduce the goal to its premises. Take the linear combination `e0`. Establish `ht : φ M.trace = x + y`. Apply `mul_left_cancel₀ hc'` to reduce the goal to its premises.

Take the linear combination `e0 - e1`. Rewrite using `[hd, ht, C_add, C_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem scale_charpoly {k : Type} [Field k] (φ : k →+* ℂ) (M : Matrix (Fin 2) (Fin 2) k) (c : k) (hc : c ≠ 0)
    (B : Multiset ℂ) (h : (c • M).charpoly.map φ = (B.map fun b => X - C (φ c * b)).prod) :
    M.charpoly.map φ = (B.map fun b => X - C b).prod := by
  have hc' : φ c ≠ 0 := by simpa using hc
  have hcard : B.card = 2 := by
    have h1 := congrArg natDegree h
    rw [natDegree_map, Matrix.charpoly_natDegree_eq_dim] at h1
    have h2 := natDegree_multiset_prod_X_sub_C_eq_card (B.map (φ c * ·))
    rw [Multiset.map_map] at h2
    simp only [Function.comp_def, Multiset.card_map] at h2
    rw [h2] at h1
    simpa using h1.symm
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hcard
  rw [Matrix.charpoly_fin_two] at h ⊢
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X,
    map_C, Matrix.trace_smul, Matrix.det_smul, smul_eq_mul, map_mul, map_pow, Fintype.card_fin] at h ⊢
  have e0 := congrArg (eval 0) h
  have e1 := congrArg (eval 1) h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at e0 e1
  have hd : φ M.det = x * y := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hc')
    linear_combination e0
  have ht : φ M.trace = x + y := by
    apply mul_left_cancel₀ hc'
    linear_combination e0 - e1
  rw [hd, ht, C_add, C_mul]
  ring

/- English proof (translation)
Establish `hl : Fact l.Prime` using `inferInstance`. Take `⟨π, hinf, hsat⟩` from `P.newform k hk f (-j)`. Use `⟨π, fun v => ⟨_, hinf v, ?_, ?_⟩, ⟨ss_of_tw _ _ hf.1, ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_singleton, Multiset.nodup_singleton, and_true]`. Introduce `h`.

Establish `h1 : (k : ℂ) = 1` using `by linear_combination h`. Establish `h2 : k = 1` using `by exact_mod_cast h1`. Use linear arithmetic over natural numbers and integers. Introduce `z hz`. Simplify using `only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz`.

Break down `hz with rfl | rfl` into its components or cases. Conclude with `⟨-j, by push_cast; ring⟩`. Conclude with `⟨1 - k - j, by push_cast; ring⟩`. Use `filter_upwards [hf.2, ev_not_mem l hl.out.ne_zero, ev_not_mem f.M f.pos.ne'] with w hw hwl hwM`. Take `⟨B, hB, hpoly⟩` from `hsat w (not_dvd_of_not_mem hwM)`.

Use `⟨B, hB, fun A hA => ⟨fun s hs => ?_, fun σ hσ => ?_⟩⟩` and prove the remaining obligations. Establish `h1` using `(hw A hA).1 s hs`. Establish `h2 : cycZ ℚ Ω l s = 1`. Use `Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)` and prove the remaining obligations. Rewrite using `[cycZ_toZModPow_eq (v := w) hwl hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]`.

Simplify using the standard rewrite rules. Establish `h3 : (cycBar ℚ Ω l ^ j) s = 1`. Rewrite using `[MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, h2, map_one, one_zpow]`. Apply `Units.ext` to reduce the goal to its premises. Establish `h4` using `congrArg Units.val h1`.

Rewrite `h4` using `[tw_val, h3, Units.val_one, one_smul]`. Then use the resulting hypothesis. Establish `h1` using `(hw A hA).2 σ hσ`. Rewrite `h1` using `[tw_val, ← hpoly]`. Use `scale_charpoly ι.toRingHom _ _ (Units.ne_zero ((cycBar ℚ Ω l ^ j) σ⁻¹)) _ ?_` and prove the remaining obligations. Rewrite using `[h1]`.

Establish `h2 : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ)`. Express the relevant statement in the definitionally equal form `algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _`. Rewrite using `[cycZ_of_isFrob hwl hA hσ, map_natCast, map_natCast]`. Establish `h3 : ι.toRingHom (((cycBar ℚ Ω l ^ j) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV w : ℂ) ^ (-j)`. Rewrite using `[MonoidHom.zpow_apply, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀, map_inv₀, map_natCast, inv_zpow']`.

Rewrite using `[h3]`. Use `filter_upwards [ev_not_mem f.M f.pos.ne'] with w hwM`. Conclude with `hsat w (not_dvd_of_not_mem hwM)`.
-/
theorem exists_rep (P : Af.Hypotheses₂) [IsAlgClosure ℚ Ω] {k : ℕ} (hk : 2 ≤ k) (f : Newform k) (ι : Qbar l ≃+* ℂ) (W : R2 Ω l) (j : ℤ)
    (hf : f.Att ι (tw W (cycBar ℚ Ω l ^ j))) :
    ∃ π : TR.CuspSub ℚ 2, π.IsRegAlg ∧ AttR ι W π ∧ ∀ᶠ w : Pl in Filter.cofinite, ∃ Bs, π.HasSat w Bs ∧
      ((algSat 2 (normV w) Bs).map fun b => X - C ((normV w : ℂ) ^ (-j) * b)).prod = f.heckePoly (normV w) := by
  have hl : Fact l.Prime := inferInstance
  obtain ⟨π, hinf, hsat⟩ := P.newform k hk f (-j)
  refine ⟨π, fun v => ⟨_, hinf v, ?_, ?_⟩, ⟨ss_of_tw _ _ hf.1, ?_⟩, ?_⟩
  · simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_singleton, Multiset.nodup_singleton, and_true]
    intro h
    have h1 : (k : ℂ) = 1 := by linear_combination h
    have h2 : k = 1 := by exact_mod_cast h1
    omega
  · intro z hz
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨-j, by push_cast; ring⟩
    · exact ⟨1 - k - j, by push_cast; ring⟩
  · filter_upwards [hf.2, ev_not_mem l hl.out.ne_zero, ev_not_mem f.M f.pos.ne'] with w hw hwl hwM
    obtain ⟨B, hB, hpoly⟩ := hsat w (not_dvd_of_not_mem hwM)
    refine ⟨B, hB, fun A hA => ⟨fun s hs => ?_, fun σ hσ => ?_⟩⟩
    · have h1 := (hw A hA).1 s hs
      have h2 : cycZ ℚ Ω l s = 1 := by
        refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
        rw [cycZ_toZModPow_eq (v := w) hwl hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]
        simp
      have h3 : (cycBar ℚ Ω l ^ j) s = 1 := by
        rw [MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, h2, map_one, one_zpow]
      apply Units.ext
      have h4 := congrArg Units.val h1
      rwa [tw_val, h3, Units.val_one, one_smul] at h4
    · have h1 := (hw A hA).2 σ hσ
      rw [tw_val, ← hpoly] at h1
      refine scale_charpoly ι.toRingHom _ _ (Units.ne_zero ((cycBar ℚ Ω l ^ j) σ⁻¹)) _ ?_
      rw [h1]
      have h2 : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
        change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
        rw [cycZ_of_isFrob hwl hA hσ, map_natCast, map_natCast]
      have h3 : ι.toRingHom (((cycBar ℚ Ω l ^ j) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV w : ℂ) ^ (-j) := by
        rw [MonoidHom.zpow_apply, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀,
          map_inv₀, map_natCast, inv_zpow']
      rw [h3]
  · filter_upwards [ev_not_mem f.M f.pos.ne'] with w hwM
    exact hsat w (not_dvd_of_not_mem hwM)

/- English proof (translation)
Use `haveI : NeZero N := ⟨hN.ne'⟩`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Take `⟨z, hz⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω N`. Use `⟨Fintype.card (ZMod N)ˣ, Fintype.card_pos, fun s => ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_pow]`. Use `h _ fun ζ hζ => ?_` and prove the remaining obligations. Take `⟨i, -, rfl⟩` from `hz.eq_pow_of_pow_eq_one hζ`. Establish `h1` using `hz.autToPow_spec ℚ (s ^ Fintype.card (ZMod N)ˣ)`. Rewrite `h1` using `[map_pow, pow_card_eq_one, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hz.pow_eq_one, pow_one]`.

Rewrite using `[map_pow, ← h1]`.
-/
theorem pow_eq_one_of_kills [IsAlgClosure ℚ Ω] {C : Type} [CommGroup C] {N : ℕ} (hN : 0 < N) {φ : G ℚ Ω →* C}
    (h : KillsMu N φ) : ∃ m : ℕ, 1 ≤ m ∧ ∀ s, φ s ^ m = 1 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
  refine ⟨Fintype.card (ZMod N)ˣ, Fintype.card_pos, fun s => ?_⟩
  rw [← map_pow]
  refine h _ fun ζ hζ => ?_
  obtain ⟨i, -, rfl⟩ := hz.eq_pow_of_pow_eq_one hζ
  have h1 := hz.autToPow_spec ℚ (s ^ Fintype.card (ZMod N)ˣ)
  rw [map_pow, pow_card_eq_one, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hz.pow_eq_one, pow_one] at h1
  rw [map_pow, ← h1]

/- English proof (translation)
Establish `hfin : {ζ : Ω | ζ ^ M = 1}.Finite` using `by classical`. Use `(Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_` and prove the remaining obligations. Simplify `hζ` using `[Polynomial.mem_nthRoots hM]`. Use `Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := ℚ) ζ).mem_nhds ?_) fun s hs => ?_)` and prove the remaining obligations. Simplify using `only [Set.mem_iInter]`.

Conclude with `fun ζ _ => Subgroup.one_mem _`. Simplify using `only [Set.mem_iInter] at hs`. Conclude with `hφ s fun ζ hζ => hs ζ hζ`.
-/
theorem isOpen_ker_kills [IsAlgClosure ℚ Ω] {C : Type} [Group C] {M : ℕ} (hM : 0 < M) {φ : G ℚ Ω →* C} (hφ : KillsMu M φ) :
    IsOpen (φ.ker : Set (G ℚ Ω)) := by
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hM] using hζ
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := ℚ) ζ).mem_nhds ?_) fun s hs => ?_)
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · simp only [Set.mem_iInter] at hs
    exact hφ s fun ζ hζ => hs ζ hζ

/- English proof (translation)
Use `Units.continuous_val.comp (continuous_of_continuousAt_one φ ?_)` and prove the remaining obligations. Use `(continuousAt_const (y := (1 : (Qbar l)ˣ))).congr ?_` and prove the remaining obligations. Use `filter_upwards [(isOpen_ker_kills hM hφ).mem_nhds (Subgroup.one_mem _)] with s hs`. Conclude with `(MonoidHom.mem_ker.1 hs).symm`.
-/
theorem cont_of_kills [IsAlgClosure ℚ Ω] {M : ℕ} (hM : 0 < M) {φ : G ℚ Ω →* (Qbar l)ˣ} (hφ : KillsMu M φ) :
    Continuous fun s => (φ s : Qbar l) := by
  refine Units.continuous_val.comp (continuous_of_continuousAt_one φ ?_)
  refine (continuousAt_const (y := (1 : (Qbar l)ˣ))).congr ?_
  filter_upwards [(isOpen_ker_kills hM hφ).mem_nhds (Subgroup.one_mem _)] with s hs
  exact (MonoidHom.mem_ker.1 hs).symm

/- English proof (translation)
Introduce `s hs`. Simplify using `[hφ s hs]`.
-/
theorem kills_inv {M : ℕ} {φ : G ℚ Ω →* (Qbar l)ˣ} (hφ : KillsMu M φ) : KillsMu M φ⁻¹ := by
  intro s hs
  simp [hφ s hs]

/- English proof (translation)
Establish `hl : Fact l.Prime` using `inferInstance`. Take `⟨v, hv, hlv⟩` from `hA`. Establish `hA : A.valuation (l : Ω) < 1` using `by simpa using (hv (l : 𝓞 ℚ)).2 hlv`. Establish `hu : IsUnit ((l + 1 : ℕ) : ℤ_[l])`. Rewrite using `[PadicInt.isUnit_iff]`.

Conclude with `PadicInt.norm_natCast_eq_one_iff.2 (by simp)`. Take `⟨s, hs, he⟩` from `GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA hu.unit`. Use `⟨s, hs, fun k hk h => ?_⟩` and prove the remaining obligations. Establish `h2 : ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) = (l + 1 : ℕ)`. Express the relevant statement in the definitionally equal form `algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])) = _`.

Rewrite using `[he, hu.unit_spec, map_natCast, map_natCast]`. Establish `h3` using `congrArg Units.val h`. Rewrite `h3` using `[Units.val_pow_eq_pow_val, h2, Units.val_one, ← Nat.cast_pow, Nat.cast_eq_one, Nat.pow_eq_one]`. Use `hl.out.pos` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem cyc_inf [IsAlgClosure ℚ Ω] {A : ValuationSubring Ω} (hA : OverL l A) :
    ∃ s ∈ Ine (F := ℚ) A, ∀ k : ℕ, k ≠ 0 → cycBar ℚ Ω l s ^ k ≠ 1 := by
  have hl : Fact l.Prime := inferInstance
  obtain ⟨v, hv, hlv⟩ := hA
  have hA : A.valuation (l : Ω) < 1 := by simpa using (hv (l : 𝓞 ℚ)).2 hlv
  have hu : IsUnit ((l + 1 : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 (by simp)
  obtain ⟨s, hs, he⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA hu.unit
  refine ⟨s, hs, fun k hk h => ?_⟩
  have h2 : ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) = (l + 1 : ℕ) := by
    change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])) = _
    rw [he, hu.unit_spec, map_natCast, map_natCast]
  have h3 := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, h2, Units.val_one, ← Nat.cast_pow, Nat.cast_eq_one, Nat.pow_eq_one] at h3
  have := hl.out.pos
  omega

/- English proof (translation)
Express the relevant statement in the definitionally equal form `‖algebraMap ℚ_[l] (Qbar l) (((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])‖ = 1`. Rewrite using `[PadicAlgCl.norm_extends, ← PadicInt.norm_def]`. Conclude with `PadicInt.norm_units _`.
-/
theorem norm_cyc (s : G ℚ Ω) : ‖((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
  change ‖algebraMap ℚ_[l] (Qbar l) (((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])‖ = 1
  rw [PadicAlgCl.norm_extends, ← PadicInt.norm_def]
  exact PadicInt.norm_units _

/- English proof (translation)
Use `haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω`. Use `haveI : CompactSpace (G ℚ Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[ℚ] Ω))`. Take `⟨g, hg⟩` from `h`. Establish `hc : Continuous fun t : G ℚ Ω => ‖(g * W t * g⁻¹ : GL (Fin 2) (Qbar l)) i i‖`. Use `Continuous.norm ?_` and prove the remaining obligations.

Establish `h1 : Continuous fun t : G ℚ Ω => (g * W t * g⁻¹ : GL (Fin 2) (Qbar l)).val` using `Units.continuous_val.comp ((continuous_const.mul hW).mul continuous_const)`. Conclude with `h1.matrix_elem i i`. Take `⟨C, hC⟩` from `(isCompact_range hc).bddAbove`. Establish `hb : ∀ t : ↥H, ‖(κ i t : Qbar l)‖ ≤ 1`. Introduce `t`.

Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt C hlt`. Use `hC ⟨((t ^ n : ↥H) : G ℚ Ω), rfl⟩` as an intermediate fact. Simplify using `only at this`.

Rewrite `this` using `[(hg (t ^ n)).2 i, map_pow, Units.val_pow_eq_pow_val, norm_pow]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `hb s`. Establish `h2` using `hb s⁻¹`. Rewrite `h2` using `[map_inv, Units.val_inv_eq_inv_val, norm_inv]`.

Establish `h0 : 0 < ‖(κ i s : Qbar l)‖` using `norm_pos_iff.2 (Units.ne_zero _)`. Conclude with `le_antisymm h1 ((inv_le_one₀ h0).1 h2)`.
-/
theorem norm_flag [IsAlgClosure ℚ Ω] {W : R2 Ω l} (hW : Continuous W) {H : Subgroup (G ℚ Ω)} {κ : Fin 2 → ↥H →* (Qbar l)ˣ}
    (h : IsFlagOn W H κ) (i : Fin 2) (s : ↥H) : ‖(κ i s : Qbar l)‖ = 1 := by
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI : CompactSpace (G ℚ Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[ℚ] Ω))
  obtain ⟨g, hg⟩ := h
  have hc : Continuous fun t : G ℚ Ω => ‖(g * W t * g⁻¹ : GL (Fin 2) (Qbar l)) i i‖ := by
    refine Continuous.norm ?_
    have h1 : Continuous fun t : G ℚ Ω => (g * W t * g⁻¹ : GL (Fin 2) (Qbar l)).val :=
      Units.continuous_val.comp ((continuous_const.mul hW).mul continuous_const)
    exact h1.matrix_elem i i
  obtain ⟨C, hC⟩ := (isCompact_range hc).bddAbove
  have hb : ∀ t : ↥H, ‖(κ i t : Qbar l)‖ ≤ 1 := by
    intro t
    by_contra hlt
    push Not at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hlt
    have := hC ⟨((t ^ n : ↥H) : G ℚ Ω), rfl⟩
    simp only at this
    rw [(hg (t ^ n)).2 i, map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
    linarith
  have h1 := hb s
  have h2 := hb s⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  have h0 : 0 < ‖(κ i s : Qbar l)‖ := norm_pos_iff.2 (Units.ne_zero _)
  exact le_antisymm h1 ((inv_le_one₀ h0).1 h2)

/- English proof (translation)
Take `⟨g, hg⟩` from `h`. Use `⟨g, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[conj_tw, Matrix.smul_apply, (hg s).1 i j hij, smul_zero]`. Rewrite using `[conj_tw, Matrix.smul_apply, (hg s).2 i]`. Simplify using `[mul_comm]`.
-/
theorem flag_twist {W : R2 Ω l} (φ : G ℚ Ω →* (Qbar l)ˣ) {H : Subgroup (G ℚ Ω)} {κ : Fin 2 → ↥H →* (Qbar l)ˣ}
    (h : IsFlagOn W H κ) : IsFlagOn (tw W φ) H (fun i => κ i * φ.comp H.subtype) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
  · rw [conj_tw, Matrix.smul_apply, (hg s).1 i j hij, smul_zero]
  · rw [conj_tw, Matrix.smul_apply, (hg s).2 i]
    simp [mul_comm]

/- English proof (translation)
Take `⟨g, hg⟩` from `h`. Use `⟨g, fun s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[conj_tw, hg s hs]`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using `[Matrix.diagonal_apply]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[Matrix.diagonal_apply, hij]`.
-/
theorem diag_twist {W : R2 Ω l} (φ : G ℚ Ω →* (Qbar l)ˣ) {H : Subgroup (G ℚ Ω)} {χ : Fin 2 → G ℚ Ω →* (Qbar l)ˣ}
    (h : IsDiagOn W H χ) : IsDiagOn (tw W φ) H (fun i => χ i * φ) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s hs => ?_⟩
  rw [conj_tw, hg s hs]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Matrix.diagonal_apply]; ring
  · simp [Matrix.diagonal_apply, hij]

/- English proof (translation)
Take `⟨g, hg⟩` from `h`. Establish `e : (mat W s).charpoly = (g * W s * g⁻¹ : GL (Fin 2) (Qbar l)).val.charpoly`. Rewrite using `[Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]`. Rewrite using `[e, Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two, (hg s).1 1 0 (by decide), (hg s).2, (hg s).2]`. Simplify using `only [mul_zero, sub_zero, C_add, C_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem charpoly_flag {W : R2 Ω l} {H : Subgroup (G ℚ Ω)} {κ : Fin 2 → ↥H →* (Qbar l)ˣ} (h : IsFlagOn W H κ) (s : ↥H) :
    (mat W s).charpoly = (X - C (κ 0 s : Qbar l)) * (X - C (κ 1 s : Qbar l)) := by
  obtain ⟨g, hg⟩ := h
  have e : (mat W s).charpoly = (g * W s * g⁻¹ : GL (Fin 2) (Qbar l)).val.charpoly := by
    rw [Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]
  rw [e, Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two, (hg s).1 1 0 (by decide), (hg s).2, (hg s).2]
  simp only [mul_zero, sub_zero, C_add, C_mul]
  ring

/- English proof (translation)
Simplify using `only [mat, map_mul, map_inv]`. Rewrite using `[Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]`.
-/
theorem charpoly_conj (W : R2 Ω l) (γ s : G ℚ Ω) : (mat W (γ * s * γ⁻¹)).charpoly = (mat W s).charpoly := by
  simp only [mat, map_mul, map_inv]
  rw [Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Take `⟨⟨s, hs⟩, t, ht⟩` from `hn`. Establish `h1` using `(h s).resolve_left hs`. Establish `h2` using `(h t).resolve_right ht`.

Break down `h (s * t) with h3 | h3` into its components or cases. Rewrite `h3` using `[map_mul, map_mul, h2]`. Conclude with `hs (mul_right_cancel h3)`. Rewrite `h3` using `[map_mul, map_mul, h1]`. Conclude with `ht (mul_left_cancel h3)`.
-/
theorem eq_or_eq {H C : Type} [Group H] [CommGroup C] (a b c : H →* C) (h : ∀ s, a s = b s ∨ a s = c s) :
    (∀ s, a s = b s) ∨ ∀ s, a s = c s := by
  by_contra hn
  push Not at hn
  obtain ⟨⟨s, hs⟩, t, ht⟩ := hn
  have h1 := (h s).resolve_left hs
  have h2 := (h t).resolve_right ht
  rcases h (s * t) with h3 | h3
  · rw [map_mul, map_mul, h2] at h3
    exact hs (mul_right_cancel h3)
  · rw [map_mul, map_mul, h1] at h3
    exact ht (mul_left_cancel h3)

/- English proof (translation)
Take `⟨v, hv, hlv⟩` from `hA`. Take `⟨v', hv', hlv'⟩` from `hA'`. Take `rfl : v = v'` from `HeightOneSpectrum.ext ((asIdeal_eq Fact.out hlv).trans (asIdeal_eq Fact.out hlv').symm)`. Take `⟨γ, hγ⟩` from `exists_smul_eq_of_isPlaceOver hv hv'`. Use `eq_or_eq ((cycBar ℚ Ω l).comp (Dec (F := ℚ) A).subtype) (κ 0) (κ 1) fun s => ?_` and prove the remaining obligations.

Establish `hs : γ * (s : G ℚ Ω) * γ⁻¹ ∈ Dec (F` using `ℚ) A' := by`. Establish `hs'` using `mem_Dec.1 s.2`. Rewrite using `[mem_Dec, mul_smul, mul_smul, ← hγ, inv_smul_smul, hs']`. Establish `h1` using `charpoly_flag h' ⟨_, hs⟩`. Rewrite `h1` using `[he]`.

Simplify using `only at h1`. Establish `hc : cycBar ℚ Ω l (γ * (s : G ℚ Ω) * γ⁻¹) = cycBar ℚ Ω l s`. Rewrite using `[map_mul, map_mul, map_inv, mul_inv_cancel_comm]`. Rewrite `h1` using `[charpoly_conj, charpoly_flag h s, hc]`. Establish `h2` using `congrArg (eval ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l)) h1`.

Simplify using `only [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, mul_eq_zero, sub_eq_zero] at h2`. Conclude with `h2.imp Units.ext Units.ext`.
-/
theorem eps_mem [IsAlgClosure ℚ Ω] {W : R2 Ω l} {A A' : ValuationSubring Ω} (hA : OverL l A) (hA' : OverL l A')
    {κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ} {κ' : Fin 2 → ↥(Dec (F := ℚ) A') →* (Qbar l)ˣ}
    (h : IsFlagOn W (Dec (F := ℚ) A) κ) (h' : IsFlagOn W (Dec (F := ℚ) A') κ')
    (he : ∀ s : ↥(Dec (F := ℚ) A'), κ' 0 s = cycBar ℚ Ω l s) :
    (∀ s : ↥(Dec (F := ℚ) A), cycBar ℚ Ω l s = κ 0 s) ∨ ∀ s : ↥(Dec (F := ℚ) A), cycBar ℚ Ω l s = κ 1 s := by
  obtain ⟨v, hv, hlv⟩ := hA
  obtain ⟨v', hv', hlv'⟩ := hA'
  obtain rfl : v = v' := HeightOneSpectrum.ext ((asIdeal_eq Fact.out hlv).trans (asIdeal_eq Fact.out hlv').symm)
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_isPlaceOver hv hv'
  refine eq_or_eq ((cycBar ℚ Ω l).comp (Dec (F := ℚ) A).subtype) (κ 0) (κ 1) fun s => ?_
  have hs : γ * (s : G ℚ Ω) * γ⁻¹ ∈ Dec (F := ℚ) A' := by
    have hs' := mem_Dec.1 s.2
    rw [mem_Dec, mul_smul, mul_smul, ← hγ, inv_smul_smul, hs']
  have h1 := charpoly_flag h' ⟨_, hs⟩
  rw [he] at h1
  simp only at h1
  have hc : cycBar ℚ Ω l (γ * (s : G ℚ Ω) * γ⁻¹) = cycBar ℚ Ω l s := by
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  rw [charpoly_conj, charpoly_flag h s, hc] at h1
  have h2 := congrArg (eval ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l)) h1
  simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, mul_eq_zero, sub_eq_zero] at h2
  exact h2.imp Units.ext Units.ext

end GlobalTheory.Ord2.SrcForm

namespace GlobalTheory.Ord2

open TwDet SrcForm

/- English proof (translation)
Introduce `P R l hl Ω _ _ _ ι e W hl2 he h`. Establish `hl0 : 0 < l` using `hl.out.pos`. Take `⟨N, hN, hNk⟩` from `UpperTheory.V.CF.kwAbs Ω (dt W).ker (ker_open h.cont h.det2) (Abelianization.commutator_subset_ker (dt W))`. Establish `hθN : KillsMu N (dt W)` using `fun s hs => hNk s hs`. Take `⟨A, χ, κ, hA, hχ, hfl, hine, hk⟩` from `h.flag`.

Use `set φ : G ℚ Ω →* (Qbar l)ˣ := (dt W)⁻¹ * χ⁻¹ with hφdef`. Establish `hNl : 0 < N * l` using `Nat.mul_pos hN hl0`. Establish `hφ : KillsMu (N * l) φ` using `killsMu_mul (killsMu_dvd (kills_inv hθN) (dvd_mul_right N l)) (killsMu_dvd (kills_inv hχ) (dvd_mul_left l N))`. Take `⟨g, hg⟩` from `GlobalTheory.T.newform_of_admissible_twist P R l Ω ι e W hl2 he h (N * l) φ hNl hφ`. Establish `hVc : Continuous (tw W φ)` using `tw_cont h.cont (cont_of_kills hNl hφ)`.

Establish `hVi : IsIrr (tw W φ)` using `irr_tw W φ _ h.irr`. Establish `hVa : ∃ M : ℕ, 1 ≤ M ∧ LevelAway l M (tw W φ)`. Take `⟨M, hM, hlev⟩` from `h.away`. Use `⟨M * (N * l), Nat.mul_pos hM hNl, fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨B, hB, ψ, hψ, hd⟩` from `hlev w hw`.

Conclude with `⟨B, hB, fun i => ψ i * φ, fun i => killsMu_mul (killsMu_dvd (hψ i) (dvd_mul_right _ _)) (killsMu_dvd hφ (dvd_mul_left _ _)), diag_twist φ hd⟩`. Establish `hVd : ∃ M : ℕ, 1 ≤ M ∧ KillsMu M (dt (tw W φ))`. Use `⟨N * l, hNl, ?_⟩` and prove the remaining obligations. Rewrite using `[dt_tw, pow_two]`. Conclude with `killsMu_mul (killsMu_mul hφ hφ) (killsMu_dvd hθN (dvd_mul_right N l))`.

Establish `hVf` using `flag_twist φ hfl`. Establish `hVk : ∀ s : ↥(Dec (F` using `ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → (κ 0 * φ.comp (Dec (F := ℚ) A).subtype) s = cycBar ℚ Ω l s ^ (e : ℤ) ∧ (κ 1 * φ.comp (Dec (F := ℚ) A).subtype) s = cycBar ℚ Ω l s ^ (-(e : ℤ)) := by`. Introduce `s hs`. Establish `h1 : dt W (s : G ℚ Ω) = 1` using `hine hs`. Take `⟨h0, h1'⟩` from `hk s hs`.

Simplify using `only [hφdef, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply, Subgroup.coe_subtype, h1, inv_one, one_mul, h0, h1', mul_inv_cancel_right, and_self]`. Take `⟨π, hreg, hatt, hsat⟩` from `exists_rep P.toClassicalTheorems (by omega) g ι (tw W φ) (-(e : ℤ)) hg`. Take `⟨v, hv, hlv⟩` from `id hA`. Establish `hnv : normV v = l` using `normV_of_mem hl.out hlv`. Take `⟨Bs, hBs⟩` from `GlobalTheory.T.newform_flag_local_of_irreducible P.toClassicalTheorems l Ω ι e (tw W φ) A _ g hl2 he hVc hVi hVa hVd hA hVf hVk hg π hreg hatt v hlv`.

Establish `hlev : ¬ l ∣ g.M` using `hnv ▸ GlobalTheory.NewLevel.newLevel P.toClassicalTheorems P.ssR _ (by omega) g _ π hsat v Bs hBs`. Take `⟨σ, hσ⟩` from `exists_isFrob (Ω := Ω) hv`. Rewrite `hσ` using `[hnv]`. Take `⟨α, hroot, hα⟩` from `GlobalTheory.T.newform_flag_local_of_level P.toClassicalTheorems l Ω ι e (tw W φ) A _ g hl2 he hVc hVi hVa hVd hA hVf hVk hg hlev ⟨σ, hσ.1⟩ hσ`. Use `set u : (Qbar l)ˣ := (κ 0 * φ.comp (Dec (F := ℚ) A).subtype) ⟨σ, hσ.1⟩ * cycBar ℚ Ω l σ ^ (-(e : ℤ)) with hu`.

Establish `hun : ‖(u : Qbar l)‖ = 1`. Rewrite using `[hu, Units.val_mul, norm_mul, norm_flag hVc hVf 0, Units.val_zpow_eq_zpow_val, norm_zpow, norm_cyc, one_zpow, one_mul]`. Establish `hα' : α = ι (u : Qbar l) ∨ α = (ι (u : Qbar l))⁻¹` using `hα.imp id fun h => by rw [← h, inv_inv]`. Establish `hαn : ‖ι.symm α‖ = 1`. Break down `hα' with h1 | h1` into its components or cases.

Rewrite using `[h1, RingEquiv.symm_apply_apply, hun]`. Rewrite using `[h1, map_inv₀, RingEquiv.symm_apply_apply, norm_inv, hun, inv_one]`. Take `⟨hal, hpow⟩` from `GlobalTheory.T.newform_unit_root_not_root_of_unity_odd_weight l ι e g α hl2 he hlev hroot hαn`. Use `⟨⟨g, hlev, hal, χ⁻¹, kills_inv hχ, ?_⟩, fun A' κ' hA' hfl' => ?_⟩` and prove the remaining obligations. Rewrite `hg` using `[tw_tw]`.

Rewrite using `[mul_assoc]`. Conclude with `hg`. Assume the negation of the conclusion as `hn push Not at hn`. Take `⟨m, hm, hχm⟩` from `pow_eq_one_of_kills hl0 hχ`. Take `⟨t, ht, htk⟩` from `cyc_inf hA`.

Take `⟨h0, h1⟩` from `hk ⟨t, Ine_le_Dec A ht⟩ ht`. Break down `eps_mem hA hA' hfl hfl' hn with hc | hc` into its components or cases. Rewrite `h0` using `[← hc]`. Simplify using `only at h0`. Establish `he1 : e = 1`.

Assume the negation of the conclusion as `hne`. Take `⟨d, rfl⟩ : ∃ d, e = d + 1` from `⟨e - 1, by omega⟩`. Use `htk (d * m) (Nat.mul_ne_zero (by omega) (by omega)) ?_` and prove the remaining obligations. Establish `h2 : cycBar ℚ Ω l t ^ d * χ t = 1`. Rewrite `h0` using `[zpow_natCast, pow_succ', mul_assoc]`.

Conclude with `(left_eq_mul.1 h0)`. Rewrite using `[pow_mul, eq_inv_of_mul_eq_one_left h2, inv_pow, hχm, inv_one]`. Take `⟨m', hm', hφm⟩` from `pow_eq_one_of_kills hNl hφ`. Establish `hu' : u = φ σ`. Rewrite using `[hu, MonoidHom.mul_apply, ← hc, he1]`.

Simplify using `[mul_inv_cancel_comm]`. Establish `hu1 : ι (u : Qbar l) ^ m' = 1`. Rewrite using `[← map_pow, ← Units.val_pow_eq_pow_val, hu', hφm, Units.val_one, map_one]`. Use `hpow m' hm' ?_` and prove the remaining obligations. Break down `hα' with h1 | h1` into its components or cases.

Rewrite using `[h1, hu1]`. Rewrite using `[h1, inv_pow, hu1, inv_one]`. Rewrite `h1` using `[← hc]`. Simplify using `only at h1`. Use `htk ((e + 1) * m) (Nat.mul_ne_zero (by omega) (by omega)) ?_` and prove the remaining obligations.

Establish `h2 : cycBar ℚ Ω l t ^ (e + 1) = χ t`. Rewrite using `[pow_succ]`. Use `nth_rewrite 2 [h1]`. Rewrite using `[zpow_neg, zpow_natCast, mul_inv_cancel_left]`. Rewrite using `[pow_mul, h2, hχm]`.
-/
theorem src_and_ne_cyc : Af.HypothesesH → Published.RepNewform → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l), l ≠ 2 → 1 ≤ e → admitted ι e W → (∃ g : Newform (2 * e + 1), FinalTheorems ι e W g) ∧ ∀ (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ), OverL l A → IsFlagOn W (Dec (F := ℚ) A) κ → ∃ s : ↥(Dec (F := ℚ) A), κ 0 s ≠ cycBar ℚ Ω l s := by
  intro P R l hl Ω _ _ _ ι e W hl2 he h
  have hl0 : 0 < l := hl.out.pos
  obtain ⟨N, hN, hNk⟩ := UpperTheory.V.CF.kwAbs Ω (dt W).ker (ker_open h.cont h.det2)
    (Abelianization.commutator_subset_ker (dt W))
  have hθN : KillsMu N (dt W) := fun s hs => hNk s hs
  obtain ⟨A, χ, κ, hA, hχ, hfl, hine, hk⟩ := h.flag
  set φ : G ℚ Ω →* (Qbar l)ˣ := (dt W)⁻¹ * χ⁻¹ with hφdef
  have hNl : 0 < N * l := Nat.mul_pos hN hl0
  have hφ : KillsMu (N * l) φ :=
    killsMu_mul (killsMu_dvd (kills_inv hθN) (dvd_mul_right N l)) (killsMu_dvd (kills_inv hχ) (dvd_mul_left l N))
  obtain ⟨g, hg⟩ := GlobalTheory.T.newform_of_admissible_twist P R l Ω ι e W hl2 he h (N * l) φ hNl hφ
  have hVc : Continuous (tw W φ) := tw_cont h.cont (cont_of_kills hNl hφ)
  have hVi : IsIrr (tw W φ) := irr_tw W φ _ h.irr
  have hVa : ∃ M : ℕ, 1 ≤ M ∧ LevelAway l M (tw W φ) := by
    obtain ⟨M, hM, hlev⟩ := h.away
    refine ⟨M * (N * l), Nat.mul_pos hM hNl, fun w hw => ?_⟩
    obtain ⟨B, hB, ψ, hψ, hd⟩ := hlev w hw
    exact ⟨B, hB, fun i => ψ i * φ, fun i => killsMu_mul (killsMu_dvd (hψ i) (dvd_mul_right _ _))
      (killsMu_dvd hφ (dvd_mul_left _ _)), diag_twist φ hd⟩
  have hVd : ∃ M : ℕ, 1 ≤ M ∧ KillsMu M (dt (tw W φ)) := by
    refine ⟨N * l, hNl, ?_⟩
    rw [dt_tw, pow_two]
    exact killsMu_mul (killsMu_mul hφ hφ) (killsMu_dvd hθN (dvd_mul_right N l))
  have hVf := flag_twist φ hfl
  have hVk : ∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
      (κ 0 * φ.comp (Dec (F := ℚ) A).subtype) s = cycBar ℚ Ω l s ^ (e : ℤ) ∧
      (κ 1 * φ.comp (Dec (F := ℚ) A).subtype) s = cycBar ℚ Ω l s ^ (-(e : ℤ)) := by
    intro s hs
    have h1 : dt W (s : G ℚ Ω) = 1 := hine hs
    obtain ⟨h0, h1'⟩ := hk s hs
    simp only [hφdef, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply, Subgroup.coe_subtype, h1, inv_one,
      one_mul, h0, h1', mul_inv_cancel_right, and_self]
  obtain ⟨π, hreg, hatt, hsat⟩ := exists_rep P.toClassicalTheorems (by omega) g ι (tw W φ) (-(e : ℤ)) hg
  obtain ⟨v, hv, hlv⟩ := id hA
  have hnv : normV v = l := normV_of_mem hl.out hlv
  obtain ⟨Bs, hBs⟩ := GlobalTheory.T.newform_flag_local_of_irreducible P.toClassicalTheorems l Ω ι e (tw W φ) A _ g hl2 he hVc hVi hVa hVd hA hVf hVk hg π hreg hatt v hlv
  have hlev : ¬ l ∣ g.M := hnv ▸ GlobalTheory.NewLevel.newLevel P.toClassicalTheorems P.ssR _ (by omega) g _ π hsat v Bs hBs
  obtain ⟨σ, hσ⟩ := exists_isFrob (Ω := Ω) hv
  rw [hnv] at hσ
  obtain ⟨α, hroot, hα⟩ := GlobalTheory.T.newform_flag_local_of_level P.toClassicalTheorems l Ω ι e (tw W φ) A _ g hl2 he hVc hVi hVa hVd hA hVf hVk hg hlev
    ⟨σ, hσ.1⟩ hσ
  set u : (Qbar l)ˣ := (κ 0 * φ.comp (Dec (F := ℚ) A).subtype) ⟨σ, hσ.1⟩ * cycBar ℚ Ω l σ ^ (-(e : ℤ)) with hu
  have hun : ‖(u : Qbar l)‖ = 1 := by
    rw [hu, Units.val_mul, norm_mul, norm_flag hVc hVf 0, Units.val_zpow_eq_zpow_val, norm_zpow, norm_cyc, one_zpow, one_mul]
  have hα' : α = ι (u : Qbar l) ∨ α = (ι (u : Qbar l))⁻¹ := hα.imp id fun h => by rw [← h, inv_inv]
  have hαn : ‖ι.symm α‖ = 1 := by
    rcases hα' with h1 | h1
    · rw [h1, RingEquiv.symm_apply_apply, hun]
    · rw [h1, map_inv₀, RingEquiv.symm_apply_apply, norm_inv, hun, inv_one]
  obtain ⟨hal, hpow⟩ := GlobalTheory.T.newform_unit_root_not_root_of_unity_odd_weight l ι e g α hl2 he hlev hroot hαn
  refine ⟨⟨g, hlev, hal, χ⁻¹, kills_inv hχ, ?_⟩, fun A' κ' hA' hfl' => ?_⟩
  · rw [tw_tw] at hg
    rw [mul_assoc]
    exact hg
  · by_contra hn
    push Not at hn
    obtain ⟨m, hm, hχm⟩ := pow_eq_one_of_kills hl0 hχ
    obtain ⟨t, ht, htk⟩ := cyc_inf hA
    obtain ⟨h0, h1⟩ := hk ⟨t, Ine_le_Dec A ht⟩ ht
    rcases eps_mem hA hA' hfl hfl' hn with hc | hc
    · rw [← hc] at h0
      simp only at h0
      have he1 : e = 1 := by
        by_contra hne
        obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
        refine htk (d * m) (Nat.mul_ne_zero (by omega) (by omega)) ?_
        have h2 : cycBar ℚ Ω l t ^ d * χ t = 1 := by
          rw [zpow_natCast, pow_succ', mul_assoc] at h0
          exact (left_eq_mul.1 h0)
        rw [pow_mul, eq_inv_of_mul_eq_one_left h2, inv_pow, hχm, inv_one]
      obtain ⟨m', hm', hφm⟩ := pow_eq_one_of_kills hNl hφ
      have hu' : u = φ σ := by
        rw [hu, MonoidHom.mul_apply, ← hc, he1]
        simp [mul_inv_cancel_comm]
      have hu1 : ι (u : Qbar l) ^ m' = 1 := by
        rw [← map_pow, ← Units.val_pow_eq_pow_val, hu', hφm, Units.val_one, map_one]
      refine hpow m' hm' ?_
      rcases hα' with h1 | h1
      · rw [h1, hu1]
      · rw [h1, inv_pow, hu1, inv_one]
    · rw [← hc] at h1
      simp only at h1
      refine htk ((e + 1) * m) (Nat.mul_ne_zero (by omega) (by omega)) ?_
      have h2 : cycBar ℚ Ω l t ^ (e + 1) = χ t := by
        rw [pow_succ]
        nth_rewrite 2 [h1]
        rw [zpow_neg, zpow_natCast, mul_inv_cancel_left]
      rw [pow_mul, h2, hχm]

end GlobalTheory.Ord2

end

end
