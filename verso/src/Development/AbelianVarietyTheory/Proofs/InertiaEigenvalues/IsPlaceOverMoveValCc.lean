import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CcSymmAlgebraMapHost

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.AntiRamConj
open scoped TensorProduct Pointwise

namespace GlobalTheory.TwistDet

section Places

variable {D : Formalism.BasicNotions.D7}

def conjInt (D : Formalism.BasicNotions.D7) : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjInt_coe (x : 𝓞 D.host.E) : ((conjInt D x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := rfl

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[conjInt_coe, conjInt_coe, host_conj_conj]`.
-/
theorem conjInt_conjInt (x : 𝓞 D.host.E) : conjInt D (conjInt D x) = x := by
  apply RingOfIntegers.ext
  rw [conjInt_coe, conjInt_coe, host_conj_conj]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h x`. Conclude with `h x _ rfl`. Introduce `h x y hxy`. Establish `e : y = conjInt D x` using `RingOfIntegers.ext hxy`.

Rewrite using `[e, h]`.
-/
theorem isConjPl_iff {P P' : PlE D.host} :
    IsConjPl D.host P P' ↔ ∀ x, x ∈ P.asIdeal ↔ conjInt D x ∈ P'.asIdeal := by
  constructor
  · intro h x
    exact h x _ rfl
  · intro h x y hxy
    have e : y = conjInt D x := RingOfIntegers.ext hxy
    rw [e, h]

/- English proof (translation)
Rewrite `h`, the goal using `[isConjPl_iff]`. Introduce `x`. Rewrite using `[h, conjInt_conjInt]`.
-/
theorem isConjPl_symm {P P' : PlE D.host} (h : IsConjPl D.host P P') : IsConjPl D.host P' P := by
  rw [isConjPl_iff] at h ⊢
  intro x
  rw [h, conjInt_conjInt]

/- English proof (translation)
Establish `a` using `isConjPl_iff.1 (isConjPl_symm h)`. Establish `b` using `isConjPl_iff.1 (isConjPl_symm h')`. Use extensionality with `x`. Rewrite using `[a, b]`.
-/
theorem isConjPl_unique {P P' P'' : PlE D.host} (h : IsConjPl D.host P P') (h' : IsConjPl D.host P P'') : P' = P'' := by
  have a := isConjPl_iff.1 (isConjPl_symm h)
  have b := isConjPl_iff.1 (isConjPl_symm h')
  ext x
  rw [a, b]

/- English proof (translation)
Use `⟨P.comap (conjInt D : 𝓞 D.host.E →+* 𝓞 D.host.E) (conjInt D).surjective, isConjPl_iff.2 fun x => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x ∈ P.asIdeal ↔ conjInt D (conjInt D x) ∈ P.asIdeal`. Rewrite using `[conjInt_conjInt]`.
-/
theorem exists_isConjPl (P : PlE D.host) : ∃ P', IsConjPl D.host P P' := by
  refine ⟨P.comap (conjInt D : 𝓞 D.host.E →+* 𝓞 D.host.E) (conjInt D).surjective, isConjPl_iff.2 fun x => ?_⟩
  change x ∈ P.asIdeal ↔ conjInt D (conjInt D x) ∈ P.asIdeal
  rw [conjInt_conjInt]

/- English proof (translation)
Introduce and unpack `rfl`. Take `⟨x, hx, hy⟩` from `hs`. Conclude with `hy (conjInt D x) rfl ((isConjPl_iff.1 h x).1 hx)`.
-/
theorem ne_of_isSplitPl {P P' : PlE D.host} (hs : IsSplitPl D.host P) (h : IsConjPl D.host P P') : P ≠ P' := by
  rintro rfl
  obtain ⟨x, hx, hy⟩ := hs
  exact hy (conjInt D x) rfl ((isConjPl_iff.1 h x).1 hx)

/- English proof (translation)
Establish `e : P'.asIdeal = P.asIdeal.map (conjInt D : 𝓞 D.host.E →+* 𝓞 D.host.E)`. Use extensionality with `y`. Take `⟨x, rfl⟩` from `(conjInt D).surjective y`. Rewrite using `[← isConjPl_iff.1 h]`. Conclude with `(Ideal.apply_mem_of_equiv_iff (f := conjInt D)).symm`.

Conclude with `(Nat.card_congr (Ideal.quotientEquiv _ _ (conjInt D) e).toEquiv).symm`.
-/
theorem normV_conj {P P' : PlE D.host} (h : IsConjPl D.host P P') : normV P' = normV P := by
  have e : P'.asIdeal = P.asIdeal.map (conjInt D : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
    ext y
    obtain ⟨x, rfl⟩ := (conjInt D).surjective y
    rw [← isConjPl_iff.1 h]
    exact (Ideal.apply_mem_of_equiv_iff (f := conjInt D)).symm
  exact (Nat.card_congr (Ideal.quotientEquiv _ _ (conjInt D) e).toEquiv).symm

/- English proof (translation)
Use `(isConjPl_iff.1 h (p : 𝓞 D.host.E)).1 hp` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.
-/
theorem mem_placesOver_conj {P P' : PlE D.host} (h : IsConjPl D.host P P') {p : ℕ}
    (hp : P ∈ placesOver D.host.E p) : P' ∈ placesOver D.host.E p := by
  have := (isConjPl_iff.1 h (p : 𝓞 D.host.E)).1 hp
  rwa [map_natCast] at this

/- English proof (translation)
The claim follows from `Or.inl rfl`.
-/
theorem over_refl (P : PlE D.host) : Over P P := Or.inl rfl

/- English proof (translation)
The claim follows from `h.elim (fun e => Or.inl e.symm) fun c => Or.inr (isConjPl_symm c)`.
-/
theorem over_symm {P v : PlE D.host} (h : Over P v) : Over v P :=
  h.elim (fun e => Or.inl e.symm) fun c => Or.inr (isConjPl_symm c)

/- English proof (translation)
Break down `h with rfl | h` into its components or cases. Conclude with `h'`. Break down `h' with rfl | h'` into its components or cases. Conclude with `Or.inr h`. Conclude with `Or.inl (isConjPl_unique h' (isConjPl_symm h))`.
-/
theorem over_trans {P v w : PlE D.host} (h : Over P v) (h' : Over v w) : Over P w := by
  rcases h with rfl | h
  · exact h'
  · rcases h' with rfl | h'
    · exact Or.inr h
    · exact Or.inl (isConjPl_unique h' (isConjPl_symm h))

end Places

section Galois

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

/- English proof (translation)
Take `⟨j, hj⟩` from `X.cc_cm.1`. Apply `j.injective` to reduce the goal to its premises. Rewrite using `[hj]`. Conclude with `(D.host.conjE_apply (j.comp (algebraMap D.host.E N.Om)) x).symm`.
-/
theorem cc_algebraMap (x : D.host.E) :
    X.cc (algebraMap D.host.E N.Om x) = algebraMap D.host.E N.Om (D.host.conj x) := by
  obtain ⟨j, hj⟩ := X.cc_cm.1
  apply j.injective
  rw [hj]
  exact (D.host.conjE_apply (j.comp (algebraMap D.host.E N.Om)) x).symm

/- English proof (translation)
Take `⟨j, hj⟩` from `X.cc_cm.1`. Apply `j.injective` to reduce the goal to its premises. Rewrite using `[hj, hj, Complex.conj_conj]`.
-/
theorem cc_cc (x : N.Om) : X.cc (X.cc x) = x := by
  obtain ⟨j, hj⟩ := X.cc_cm.1
  apply j.injective
  rw [hj, hj, Complex.conj_conj]

/- English proof (translation)
Rewrite using `[RingEquiv.symm_apply_eq, cc_cc]`.
-/
theorem cc_symm (x : N.Om) : X.cc.symm x = X.cc x := by
  rw [RingEquiv.symm_apply_eq, cc_cc]

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, by rw [cc_symm, cc_algebraMap]⟩`.
-/
theorem cc_symm_mem (x : D.host.E) : ∃ y : D.host.E,
    X.cc.symm (algebraMap D.host.E N.Om x) = algebraMap D.host.E N.Om y :=
  ⟨_, by rw [cc_symm, cc_algebraMap]⟩

def cConj : GE N →* GE N where
  toFun := conjAut X.cc (cc_symm_mem X)
  map_one' := by
    ext x
    exact X.cc.apply_symm_apply x
  map_mul' g h := by
    ext x
    change X.cc (g (h (X.cc.symm x))) = X.cc (g (X.cc.symm (X.cc (h (X.cc.symm x)))))
    rw [RingEquiv.symm_apply_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cConj_apply (g : GE N) (x : N.Om) : cConj X g x = X.cc (g (X.cc.symm x)) := rfl

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[cConj_apply, cConj_apply, cc_cc, cc_symm, cc_symm, cc_cc]`.
-/
theorem cConj_cConj (g : GE N) : cConj X (cConj X g) = g := by
  ext x
  rw [cConj_apply, cConj_apply, cc_cc, cc_symm, cc_symm, cc_cc]

/- English proof (translation)
The claim follows from `h g _ (cConj_apply X g)`.
-/
theorem antiHom_cConj {A : Type} [CommGroup A] {φ : GE N →* A} (h : AntiHom X.cc φ) (g : GE N) :
    φ (cConj X g) = (φ g)⁻¹ := h g _ (cConj_apply X g)

/- English proof (translation)
Introduce `y`. Rewrite using `[moveVal_lt_one, cc_symm, cc_algebraMap, ← conjInt_coe, hB]`. Conclude with `(isConjPl_iff.1 (isConjPl_symm h) y).symm`.
-/
theorem isPlaceOver_moveVal_cc {P P' : PlE D.host} (h : IsConjPl D.host P P') {B : ValuationSubring N.Om}
    (hB : IsPlaceOver B P) : IsPlaceOver (moveVal X.cc B) P' := by
  intro y
  rw [moveVal_lt_one, cc_symm, cc_algebraMap, ← conjInt_coe, hB]
  exact (isConjPl_iff.1 (isConjPl_symm h) y).symm

/- English proof (translation)
The claim follows from `conjAut_mem_ine X.cc (cc_symm_mem X) hσ`.
-/
theorem cConj_mem_ine {B : ValuationSubring N.Om} {σ : GE N} (hσ : σ ∈ Ine (F := D.host.E) B) :
    cConj X σ ∈ Ine (F := D.host.E) (moveVal X.cc B) := conjAut_mem_ine X.cc (cc_symm_mem X) hσ

/- English proof (translation)
Establish `hd : σ ∈ Dec (F` using `D.host.E) B := hσ.1`. Use `⟨?_, fun x hx => ?_⟩` and prove the remaining obligations. Use `show cConj X σ ∈ Dec (F := D.host.E) (moveVal X.cc B)`. Rewrite using `[mem_Dec]`. Use extensionality with `x`.

Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]`. Take `⟨z, rfl⟩` from `(cConj X σ).surjective x`. Establish `h1 : ((cConj X σ)⁻¹ : GE N) (cConj X σ z) = z` using `(cConj X σ).symm_apply_apply z`. Rewrite using `[h1, mem_moveVal, mem_moveVal, cConj_apply, RingEquiv.symm_apply_apply, apply_mem_iff_of_mem_Dec hd]`. Rewrite using `[moveVal_lt_one, map_sub, cConj_apply, RingEquiv.symm_apply_apply, map_pow]`.

Apply `hσ.2` to reduce the goal to its premises. Rewrite `hx`, the goal using `[ValuationSubring.valuation_le_one_iff]`. Conclude with `hx`.
-/
theorem isFrob_cConj {B : ValuationSubring N.Om} {q : ℕ} {σ : GE N} (hσ : IsFrob B q σ) :
    IsFrob (moveVal X.cc B) q (cConj X σ) := by
  have hd : σ ∈ Dec (F := D.host.E) B := hσ.1
  refine ⟨?_, fun x hx => ?_⟩
  · show cConj X σ ∈ Dec (F := D.host.E) (moveVal X.cc B)
    rw [mem_Dec]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    obtain ⟨z, rfl⟩ := (cConj X σ).surjective x
    have h1 : ((cConj X σ)⁻¹ : GE N) (cConj X σ z) = z := (cConj X σ).symm_apply_apply z
    rw [h1, mem_moveVal, mem_moveVal, cConj_apply, RingEquiv.symm_apply_apply, apply_mem_iff_of_mem_Dec hd]
  · rw [moveVal_lt_one, map_sub, cConj_apply, RingEquiv.symm_apply_apply, map_pow]
    apply hσ.2
    rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
    exact hx

/- English proof (translation)
Establish `hd : σ • B = B` using `hσ.1`. Establish `hm : ∀ y : N.Om, y ∈ g • B ↔ (g⁻¹ : GE N) y ∈ B` using `fun y => by`. Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]`. Use `⟨?_, fun x hx => ?_⟩` and prove the remaining obligations. Use `show (g * σ * g⁻¹) • g • B = g • B`.

Rewrite using `[← mul_smul, inv_mul_cancel_right, mul_smul, hd]`. Rewrite `hx` using `[ValuationSubring.valuation_le_one_iff, hm]`. Establish `h2` using `hσ.2 _ ((B.valuation_le_one_iff _).2 hx)`. Establish `e : (g⁻¹ : GE N) ((g * σ * g⁻¹) x - x ^ q) = σ ((g⁻¹ : GE N) x) - ((g⁻¹ : GE N) x) ^ q`. Rewrite using `[map_sub, map_pow, ← AlgEquiv.mul_apply, mul_assoc, inv_mul_cancel_left, AlgEquiv.mul_apply]`.

Rewrite `h2`, the goal using `[valuation_lt_one_iff']`. Rewrite using `[hm, hm, map_inv₀, ← map_eq_zero_iff (g⁻¹ : GE N) (g⁻¹ : GE N).injective, e]`. Conclude with `h2`.
-/
theorem isFrob_smul {B : ValuationSubring N.Om} {q : ℕ} {σ : GE N} (hσ : IsFrob B q σ) (g : GE N) :
    IsFrob (g • B) q (g * σ * g⁻¹) := by
  have hd : σ • B = B := hσ.1
  have hm : ∀ y : N.Om, y ∈ g • B ↔ (g⁻¹ : GE N) y ∈ B := fun y => by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  refine ⟨?_, fun x hx => ?_⟩
  · show (g * σ * g⁻¹) • g • B = g • B
    rw [← mul_smul, inv_mul_cancel_right, mul_smul, hd]
  · rw [ValuationSubring.valuation_le_one_iff, hm] at hx
    have h2 := hσ.2 _ ((B.valuation_le_one_iff _).2 hx)
    have e : (g⁻¹ : GE N) ((g * σ * g⁻¹) x - x ^ q) = σ ((g⁻¹ : GE N) x) - ((g⁻¹ : GE N) x) ^ q := by
      rw [map_sub, map_pow, ← AlgEquiv.mul_apply, mul_assoc, inv_mul_cancel_left, AlgEquiv.mul_apply]
    rw [valuation_lt_one_iff'] at h2 ⊢
    rw [hm, hm, map_inv₀, ← map_eq_zero_iff (g⁻¹ : GE N) (g⁻¹ : GE N).injective, e]
    exact h2

/- English proof (translation)
Establish `h1` using `isFrob_cConj X hσ`. Establish `h2` using `isPlaceOver_moveVal_cc X (isConjPl_symm h) (N.plOm.2 P')`. Take `⟨g, hg⟩` from `exists_smul_eq_of_isPlaceOver (F := D.host.E) h2 (N.plOm.2 P)`. Establish `h3` using `isFrob_smul h1 g`. Rewrite `h3` using `[hg, normV_conj h]`.

Use `⟨_, (cConj X g)⁻¹, h3, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_inv, cConj_cConj]`. Use `group`.
-/
theorem exists_frob_of_conj {P P' : PlE D.host} (h : IsConjPl D.host P P') {σ : GE N}
    (hσ : IsFrob (N.plOm.1 P') (normV P') σ) :
    ∃ σ₀ g : GE N, IsFrob (N.plOm.1 P) (normV P) σ₀ ∧ σ = g * cConj X σ₀ * g⁻¹ := by
  have h1 := isFrob_cConj X hσ
  have h2 := isPlaceOver_moveVal_cc X (isConjPl_symm h) (N.plOm.2 P')
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := D.host.E) h2 (N.plOm.2 P)
  have h3 := isFrob_smul h1 g
  rw [hg, normV_conj h] at h3
  refine ⟨_, (cConj X g)⁻¹, h3, ?_⟩
  rw [map_mul, map_mul, map_inv, cConj_cConj]
  group

/- English proof (translation)
Take `⟨L, hL, hLH⟩` from `(krullTopology_mem_nhds_one_iff D.host.E N.Om (H : Set (GE N))).1 (hH.mem_nhds H.one_mem)`. Take `⟨S, hS⟩` from `IntermediateField.fg_of_fg_toSubalgebra L (Subalgebra.fg_of_fg_toSubmodule ((Submodule.fg_iff_finiteDimensional L.toSubalgebra.toSubmodule).2 hL))`. Set `L'` to `IntermediateField.adjoin D.host.E ((S.image X.cc.symm : Finset N.Om) : Set N.Om)`. Establish `hL' : FiniteDimensional D.host.E L'` using `IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x`. Use `Subgroup.isOpen_mono (H₁ := L'.fixingSubgroup) (fun g hg => ?_) (IntermediateField.fixingSubgroup_isOpen L')` and prove the remaining obligations.

Apply `hLH` to reduce the goal to its premises. Rewrite `hg` using `[IntermediateField.mem_fixingSubgroup_iff]`. Establish `: L ≤ IntermediateField.fixedField (Subgroup.zpowers (cConj X g))`. Rewrite using `[← hS, IntermediateField.adjoin_le_iff]`. Introduce `x hx`.

Rewrite using `[SetLike.mem_coe, IntermediateField.mem_fixedField_iff]`. Introduce `f hf`. Establish `h1 : cConj X g x = x`. Rewrite using `[cConj_apply, hg _ (IntermediateField.subset_adjoin _ _ (by simpa using hx)), RingEquiv.apply_symm_apply]`. Conclude with `(Subgroup.zpowers_le (H := MulAction.stabilizer (GE N) x)).2 h1 hf`.

Rewrite using `[SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Conclude with `(IntermediateField.mem_fixedField_iff _ _).1 (this hx) _ (Subgroup.mem_zpowers _)`.
-/
theorem isOpen_comap_cConj {H : Subgroup (GE N)} (hH : IsOpen (H : Set (GE N))) :
    IsOpen ((H.comap (cConj X) : Subgroup (GE N)) : Set (GE N)) := by
  obtain ⟨L, hL, hLH⟩ := (krullTopology_mem_nhds_one_iff D.host.E N.Om (H : Set (GE N))).1 (hH.mem_nhds H.one_mem)
  obtain ⟨S, hS⟩ := IntermediateField.fg_of_fg_toSubalgebra L (Subalgebra.fg_of_fg_toSubmodule
    ((Submodule.fg_iff_finiteDimensional L.toSubalgebra.toSubmodule).2 hL))
  classical
  let L' := IntermediateField.adjoin D.host.E ((S.image X.cc.symm : Finset N.Om) : Set N.Om)
  have hL' : FiniteDimensional D.host.E L' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine Subgroup.isOpen_mono (H₁ := L'.fixingSubgroup) (fun g hg => ?_) (IntermediateField.fixingSubgroup_isOpen L')
  apply hLH
  rw [IntermediateField.mem_fixingSubgroup_iff] at hg
  have : L ≤ IntermediateField.fixedField (Subgroup.zpowers (cConj X g)) := by
    rw [← hS, IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    have h1 : cConj X g x = x := by
      rw [cConj_apply, hg _ (IntermediateField.subset_adjoin _ _ (by simpa using hx)), RingEquiv.apply_symm_apply]
    exact (Subgroup.zpowers_le (H := MulAction.stabilizer (GE N) x)).2 h1 hf
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact (IntermediateField.mem_fixedField_iff _ _).1 (this hx) _ (Subgroup.mem_zpowers _)

end Galois

end GlobalTheory.TwistDet

end
