import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GlueExists

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem glEquiv_apply_lemma {n : ℕ} (γ : GL (Fin n) E) (x : Sp E n) :
    Formalism.UG.glEquiv γ x = (γ : Matrix (Fin n) (Fin n) E) *ᵥ x := rfl

/- English proof (translation)
Simplify using `only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Rewrite using `[glEquiv_apply_lemma, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`. Conclude with `hx`.

Introduce `h`. Use `⟨_, h, ?_⟩` and prove the remaining obligations. Rewrite using `[glEquiv_apply_lemma, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`.
-/
theorem asm_mem_gmap {n : ℕ} (γ : GL (Fin n) E) (L : Submodule (𝓞 E) (Sp E n)) (y : Sp E n) :
    y ∈ Formalism.HermitianLatticesTheory.gmap (Formalism.UG.glEquiv γ) L ↔ ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y ∈ L := by
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [glEquiv_apply_lemma, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact hx
  · intro h
    refine ⟨_, h, ?_⟩
    rw [glEquiv_apply_lemma, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

/- English proof (translation)
Rewrite using `[(hI F E).2.1 P P]`. Simplify using `only [and_self]`.
-/
theorem placeIndicator_mul_self (hI : IdemCalc) (P : HeightOneSpectrum (𝓞 F) → Prop) : eP E P * eP E P = eP E P := by
  rw [(hI F E).2.1 P P]
  simp only [and_self]

/- English proof (translation)
Establish `he` using `placeIndicator_mul_self (E := E) hI P`. Express the relevant statement in the definitionally equal form `eP E P * (∑ j, M i j * w j) ∈ Formalism.L2.Herm.intAf F E`. Rewrite using `[Finset.mul_sum]`. Use `sum_mem (fun j _ => ?_)` and prove the remaining obligations. Establish `hj : eP E P * (M i j * w j) = (eP E P * M i j) * (eP E P * w j)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hj]`. Conclude with `mul_mem (hM i j) (hw j)`.
-/
theorem asm_mulVec_int {n : ℕ} (hI : IdemCalc) (P : HeightOneSpectrum (𝓞 F) → Prop)
    (M : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (w : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hM : ∀ i j, eP E P * M i j ∈ Formalism.L2.Herm.intAf F E) (hw : ∀ j, eP E P * w j ∈ Formalism.L2.Herm.intAf F E)
    (i : Fin n) : eP E P * (M *ᵥ w) i ∈ Formalism.L2.Herm.intAf F E := by
  have he := placeIndicator_mul_self (E := E) hI P
  change eP E P * (∑ j, M i j * w j) ∈ Formalism.L2.Herm.intAf F E
  rw [Finset.mul_sum]
  refine sum_mem (fun j _ => ?_)
  have hj : eP E P * (M i j * w j) = (eP E P * M i j) * (eP E P * w j) := by
    calc eP E P * (M i j * w j) = (eP E P * eP E P) * (M i j * w j) := by rw [he]
      _ = (eP E P * M i j) * (eP E P * w j) := by ring
  rw [hj]
  exact mul_mem (hM i j) (hw j)

/- English proof (translation)
Establish `hij : ∀ j, f * M i j = f * M' i j` using `fun j => by`. Establish `hh` using `congrFun (congrFun h i) j`. Simplify `hh` using `[Matrix.smul_apply, smul_eq_mul]`. Express the relevant statement in the definitionally equal form `f * (∑ j, M i j * w j) = f * (∑ j, M' i j * w j)`. Simplify using `only [Finset.mul_sum, ← mul_assoc, hij]`.
-/
theorem asm_smul_mulVec {n : ℕ} (f : E ⊗[F] Formalism.L2.Herm.Af F) (M M' : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (h : f • M = f • M') (w : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (i : Fin n) :
    f * (M *ᵥ w) i = f * (M' *ᵥ w) i := by
  have hij : ∀ j, f * M i j = f * M' i j := fun j => by
    have hh := congrFun (congrFun h i) j
    simpa [Matrix.smul_apply, smul_eq_mul] using hh
  change f * (∑ j, M i j * w j) = f * (∑ j, M' i j * w j)
  simp only [Finset.mul_sum, ← mul_assoc, hij]

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `rw [IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E r]`.
-/
theorem asm_iota_OF (r : 𝓞 F) :
    iA F E (algebraMap (𝓞 F) E r) = iA F E (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r)) := by
  first
    | rfl
    | rw [IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E r]

/- English proof (translation)
Apply `Subring.subset_closure` to reduce the goal to its premises. Use `Or.inl ⟨⟨algebraMap (𝓞 E) E b, b, rfl⟩, ?_⟩` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem asm_iota_OE_mem (b : 𝓞 E) : iA F E (algebraMap (𝓞 E) E b) ∈ Formalism.L2.Herm.intAf F E := by
  apply Subring.subset_closure
  refine Or.inl ⟨⟨algebraMap (𝓞 E) E b, b, rfl⟩, ?_⟩
  rfl

/- English proof (translation)
Rewrite using `[asm_iota_OF]`. Conclude with `asm_iota_OE_mem _`.
-/
theorem asm_iota_OF_mem (r : 𝓞 F) : iA F E (algebraMap (𝓞 F) E r) ∈ Formalism.L2.Herm.intAf F E := by
  rw [asm_iota_OF]
  exact asm_iota_OE_mem _

/- English proof (translation)
Use `show c • y i = _`. Conclude with `Algebra.smul_def c (y i)`.
-/
theorem asm_smul_apply {n : ℕ} (c : 𝓞 E) (y : Sp E n) (i : Fin n) : (c • y) i = algebraMap (𝓞 E) E c * y i := by
  show c • y i = _
  exact Algebra.smul_def c (y i)

/- English proof (translation)
Simplify using `[Formalism.L2.Col.stdLat, Submodule.mem_pi, Submodule.mem_one]`.
-/
theorem asm_mem_std {n : ℕ} (y : Sp E n) :
    y ∈ stdLat E n ↔ ∀ i, ∃ b : 𝓞 E, algebraMap (𝓞 E) E b = y i := by
  simp [Formalism.L2.Col.stdLat, Submodule.mem_pi, Submodule.mem_one]

/- English proof (translation)
Take `⟨b, hb⟩` from `(asm_mem_std y).1 hy i`. Rewrite using `[← hb]`. Conclude with `asm_iota_OE_mem b`.
-/
theorem asm_iota_std {n : ℕ} {y : Sp E n} (hy : y ∈ stdLat E n) (i : Fin n) : iA F E (y i) ∈ Formalism.L2.Herm.intAf F E := by
  obtain ⟨b, hb⟩ := (asm_mem_std y).1 hy i
  rw [← hb]
  exact asm_iota_OE_mem b

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[RingHom.map_mulVec]`. Both sides reduce to the same expression.
-/
theorem asm_bc_mulVec {n : ℕ} (γ : GL (Fin n) E) (y : Sp E n) :
    ((Formalism.UG.bc (iA F E) γ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ
      (fun i => iA F E (y i)) = fun i => iA F E (((γ : Matrix (Fin n) (Fin n) E) *ᵥ y) i) := by
  funext i
  rw [RingHom.map_mulVec]
  rfl

/- English proof (translation)
Unfold `complF`. Conclude with `Submonoid.mem_map_of_mem _ hr`.
-/
theorem asm_mem_complF (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) (hr : r ∉ v.asIdeal) :
    algebraMap (𝓞 F) (𝓞 E) r ∈ complF E v := by
  unfold complF
  exact Submonoid.mem_map_of_mem _ hr

/- English proof (translation)
Unfold `complF at hs`. Take `⟨r, hr, rfl⟩` from `Submonoid.mem_map.1 hs`. Conclude with `⟨r, hr, rfl⟩`.
-/
theorem asm_of_mem_complF {v : HeightOneSpectrum (𝓞 F)} {s : 𝓞 E} (hs : s ∈ complF E v) :
    ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) r = s := by
  unfold complF at hs
  obtain ⟨r, hr, rfl⟩ := Submonoid.mem_map.1 hs
  exact ⟨r, hr, rfl⟩

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hc n hL N hN hU`. Conclude with `hG F E hc n N hN (hL hc.cmUnram N hN hU)`.
-/
theorem locToAd_of (hG : GenusToPoint) : LocToAd := by
  intro F E _ _ _ _ _ _ hc n hL N hN hU
  exact hG F E hc n N hN (hL hc.cmUnram N hN hU)

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hc n hW hU _ N hN hUni`. Take `⟨x, hx, rfl⟩` from `hU N hN hUni`. Conclude with `hP F E hc n hW x hx`.
-/
theorem adToLoc_of (hP : PointToGenus) : AdToLoc := by
  intro F E _ _ _ _ _ _ hc n hW hU _ N hN hUni
  obtain ⟨x, hx, rfl⟩ := hU N hN hUni
  exact hP F E hc n hW x hx

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hc n hW`. Conclude with `⟨h1 F E hc n, h2 F E hc n hW⟩`.
-/
theorem bridge_of (h1 : LocToAd) (h2 : AdToLoc) : Bridge := by
  intro F E _ _ _ _ _ _ hc n hW
  exact ⟨h1 F E hc n, h2 F E hc n hW⟩

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (y j))) ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) ↔ _`. Generalize the expression as in `(((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (y j))) = w`. Prove the components needed by the constructor for the conclusion. Introduce `hw i`. Set `Q : Submodule (Formalism.L2.Herm.intAf F E) (Fin n → E ⊗[F] Formalism.L2.Herm.Af F)` to `{ carrier := {w | ∀ i, w i ∈ Formalism.L2.Herm.intAf F E} add_mem' := by`.

Introduce `a b ha hb k`. Conclude with `add_mem (ha k) (hb k)`. Use the proof step `zero_mem' := by`. Introduce `k`. Conclude with `zero_mem _`.

Use the proof step `smul_mem' := by`. Introduce `c a ha k`. Conclude with `mul_mem c.2 (ha k) }`. Establish `hle : Formalism.UG.latS (F` using `F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) ≤ Q := by`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨z, hz, rfl⟩ j`. Conclude with `asm_iota_std hz j`. Conclude with `(hle hw : ∀ k, w k ∈ Formalism.L2.Herm.intAf F E) i`. Introduce `hw`. Establish `hsum : w = ∑ i, (⟨w i, hw i⟩ : Formalism.L2.Herm.intAf F E) • (fun j => iA F E ((Pi.single i (1 : E) : Fin n → E) j))`.

Use function extensionality and compare the values at `j`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single j]`. Simplify using `[Subring.smul_def]`. Introduce `b _ hb`. Simplify using `[Subring.smul_def, Pi.single_apply, Ne.symm hb]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ j) h`. Rewrite using `[hsum]`. Use `Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Pi.single i (1 : E), ?_, rfl⟩))` and prove the remaining obligations. Use `(asm_mem_std _).2 (fun k => ⟨(Pi.single i (1 : 𝓞 E) : Fin n → 𝓞 E) k, ?_⟩)` and prove the remaining obligations.

Break down `eq_or_ne k i with rfl | h` into its components or cases. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h]`.
-/
private theorem glob_lemma_2 {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {n : ℕ} (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : Sp E n) :
    y ∈ Formalism.UG.CS.globLat x (stdLat E n) ↔
      ∀ i, (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (y j))) i ∈ Formalism.L2.Herm.intAf F E := by
  change (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (y j))) ∈
    Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) ↔ _
  generalize (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (y j))) = w
  constructor
  · intro hw i
    let Q : Submodule (Formalism.L2.Herm.intAf F E) (Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :=
      { carrier := {w | ∀ i, w i ∈ Formalism.L2.Herm.intAf F E}
        add_mem' := by
          intro a b ha hb k
          exact add_mem (ha k) (hb k)
        zero_mem' := by
          intro k
          exact zero_mem _
        smul_mem' := by
          intro c a ha k
          exact mul_mem c.2 (ha k) }
    have hle : Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) ≤ Q := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨z, hz, rfl⟩ j
      exact asm_iota_std hz j
    exact (hle hw : ∀ k, w k ∈ Formalism.L2.Herm.intAf F E) i
  · intro hw
    have hsum : w = ∑ i, (⟨w i, hw i⟩ : Formalism.L2.Herm.intAf F E) •
        (fun j => iA F E ((Pi.single i (1 : E) : Fin n → E) j)) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · simp [Subring.smul_def]
      · intro b _ hb
        simp [Subring.smul_def, Pi.single_apply, Ne.symm hb]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [hsum]
    refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨Pi.single i (1 : E), ?_, rfl⟩))
    refine (asm_mem_std _).2 (fun k => ⟨(Pi.single i (1 : 𝓞 E) : Fin n → 𝓞 E) k, ?_⟩)
    rcases eq_or_ne k i with rfl | h
    · simp
    · simp [Pi.single_apply, h]

/- English proof (translation)
Use `set γ : GL (Fin n) E := Matrix.GeneralLinearGroup.toLin.symm ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E)).symm g) with hγdef`. Establish `hγg : Formalism.UG.glEquiv γ = g`. Simplify using `only [Formalism.UG.glEquiv, hγdef, MulEquiv.apply_symm_apply]`. Use `⟨γ, ?_, hγg⟩` and prove the remaining obligations. Use `show Formalism.UG.cT (hc.sig : E →+* E) (γ : Matrix (Fin n) (Fin n) E) * 1 * (γ : Matrix (Fin n) (Fin n) E) = 1`.

Rewrite using `[Matrix.mul_one]`. Express the relevant statement in the definitionally equal form `(γ : Matrix (Fin n) (Fin n) E)ᴴ * (γ : Matrix (Fin n) (Fin n) E) = 1`. Use extensionality with `j k`. Establish `h` using `hg (Pi.single j 1) (Pi.single k 1)`. Rewrite `h` using `[← hγg]`.

Simplify using `only [hStd, LinearMap.mk₂'ₛₗ_apply, glEquiv_apply_lemma] at h`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `only [Matrix.conjTranspose_apply]`. Use `h using 1` and compare the differences between its conclusion and the goal. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.

Simplify using `[Pi.single_apply, apply_ite star, ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq]`. Conclude with `if_congr eq_comm rfl rfl`.
-/
private theorem unit_lemma_5 {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} (g : Sp E n ≃ₗ[E] Sp E n)
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom (hStd E n)) : ∃ γ ∈ URat hc n, Formalism.UG.glEquiv γ = g := by
  set γ : GL (Fin n) E := Matrix.GeneralLinearGroup.toLin.symm
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E)).symm g) with hγdef
  have hγg : Formalism.UG.glEquiv γ = g := by
    simp only [Formalism.UG.glEquiv, hγdef, MulEquiv.apply_symm_apply]
  refine ⟨γ, ?_, hγg⟩
  show Formalism.UG.cT (hc.sig : E →+* E) (γ : Matrix (Fin n) (Fin n) E) * 1 * (γ : Matrix (Fin n) (Fin n) E) = 1
  rw [Matrix.mul_one]
  change (γ : Matrix (Fin n) (Fin n) E)ᴴ * (γ : Matrix (Fin n) (Fin n) E) = 1
  ext j k
  have h := hg (Pi.single j 1) (Pi.single k 1)
  rw [← hγg] at h
  simp only [hStd, LinearMap.mk₂'ₛₗ_apply, glEquiv_apply_lemma] at h
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply]
  convert h using 1
  · simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  · simp [Pi.single_apply, apply_ite star, ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq]
    exact if_congr eq_comm rfl rfl

/- English proof (translation)
Use `haveI := v.isMaximal`. Use `haveI : Algebra.IsIntegral (𝓞 F) (𝓞 E) := by first`. Consider the case `infer_instance`. Consider the case `exact ⟨fun x => (Algebra.IsIntegral.isIntegral (R := ℤ) x).tower_top⟩`. Establish `hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 E)) ≤ v.asIdeal`.

Introduce `a ha`. Rewrite `ha` using `[RingHom.mem_ker]`. Establish `e : algebraMap (𝓞 F) E a = algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a)` using `by first`. Consider the case `rfl`. Consider the case `exact IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E a`.

Rewrite `e` using `[ha, map_zero]`. Establish `e2 : algebraMap (𝓞 F) E a = algebraMap F E (algebraMap (𝓞 F) F a)` using `by first`. Consider the case `rfl`. Consider the case `exact IsScalarTower.algebraMap_apply (𝓞 F) F E a`. Rewrite `e` using `[e2, map_eq_zero_iff _ (algebraMap F E).injective, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]`.

Rewrite using `[e]`. Conclude with `zero_mem _`. Take `⟨Q, hQ, hQv⟩ : ∃ Q : Ideal (𝓞 E), Q.IsMaximal ∧ Q.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal` from `by first`. Consider the case `exact Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal hker`. Consider the case `exact Ideal.exists_ideal_over_maximal_of_isIntegral inferInstance v.asIdeal hker`.

Establish `hQ0 : Q ≠ ⊥` using `by first`. Consider the case `exact Ring.ne_bot_of_isMaximal_of_not_isField hQ (NumberField.RingOfIntegers.not_isField (K := E))`. Consider the case `exact Ring.ne_bot_of_isMaximal_of_not_isField hQ (NumberField.RingOfIntegers.not_isField E)`. Consider the case `exact Ideal.IsMaximal.ne_bot_of_isIntegral_int hQ`. Conclude with `⟨⟨Q, hQ.isPrime, hQ0⟩, IsDedekindDomain.HeightOneSpectrum.ext hQv⟩`.
-/
private theorem over_lemma_6 {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ PP : HeightOneSpectrum (𝓞 E), Formalism.L2.DIV.underPl F PP = v := by
  haveI := v.isMaximal
  haveI : Algebra.IsIntegral (𝓞 F) (𝓞 E) := by
    first
      | infer_instance
      | exact ⟨fun x => (Algebra.IsIntegral.isIntegral (R := ℤ) x).tower_top⟩
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 E)) ≤ v.asIdeal := by
    intro a ha
    rw [RingHom.mem_ker] at ha
    have e : algebraMap (𝓞 F) E a = algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a) := by
      first
        | rfl
        | exact IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E a
    rw [ha, map_zero] at e
    have e2 : algebraMap (𝓞 F) E a = algebraMap F E (algebraMap (𝓞 F) F a) := by
      first
        | rfl
        | exact IsScalarTower.algebraMap_apply (𝓞 F) F E a
    rw [e2, map_eq_zero_iff _ (algebraMap F E).injective,
      map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)] at e
    rw [e]
    exact zero_mem _
  obtain ⟨Q, hQ, hQv⟩ : ∃ Q : Ideal (𝓞 E), Q.IsMaximal ∧ Q.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal := by
    first
      | exact Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal hker
      | exact Ideal.exists_ideal_over_maximal_of_isIntegral inferInstance v.asIdeal hker
  have hQ0 : Q ≠ ⊥ := by
    first
      | exact Ring.ne_bot_of_isMaximal_of_not_isField hQ (NumberField.RingOfIntegers.not_isField (K := E))
      | exact Ring.ne_bot_of_isMaximal_of_not_isField hQ (NumberField.RingOfIntegers.not_isField E)
      | exact Ideal.IsMaximal.ne_bot_of_isIntegral_int hQ
  exact ⟨⟨Q, hQ.isPrime, hQ0⟩, IsDedekindDomain.HeightOneSpectrum.ext hQv⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hu`. Conclude with `⟨fun v _ => mul_mem ((hI F E).1 _) hu, mul_mem ((hI F E).1 _) hu⟩`. Introduce and unpack `⟨h1, h2⟩`. Establish `e : u = ∑ v ∈ T, eAt E v * u + eP E (fun v => v ∉ T) * u`.

Rewrite using `[← Finset.sum_mul, ← add_mul, (hI F E).2.2 T, one_mul]`. Rewrite using `[e]`. Conclude with `add_mem (sum_mem fun v hv => h1 v hv) h2`.
-/
private theorem split_lemma_8 {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hI : IdemCalc) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (u : E ⊗[F] Formalism.L2.Herm.Af F) :
    u ∈ Formalism.L2.Herm.intAf F E ↔ (∀ v ∈ T, eAt E v * u ∈ Formalism.L2.Herm.intAf F E) ∧ eP E (fun v => v ∉ T) * u ∈ Formalism.L2.Herm.intAf F E := by
  constructor
  · intro hu
    exact ⟨fun v _ => mul_mem ((hI F E).1 _) hu, mul_mem ((hI F E).1 _) hu⟩
  · rintro ⟨h1, h2⟩
    have e : u = ∑ v ∈ T, eAt E v * u + eP E (fun v => v ∉ T) * u := by
      rw [← Finset.sum_mul, ← add_mul, (hI F E).2.2 T, one_mul]
    rw [e]
    exact add_mem (sum_mem fun v hv => h1 v hv) h2

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hc n N hN hG`. Take `⟨D, hD, hD1, hD2⟩` from `hCm F E n N hN`. Establish `hfin : {v : HeightOneSpectrum (𝓞 F) | D ∈ v.asIdeal}.Finite`. Establish `h0 : Ideal.span ({D} : Set (𝓞 F)) ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`.

Conclude with `hD`. Conclude with `(Ideal.finite_factors h0).subset (fun v hv => Ideal.dvd_span_singleton.2 hv)`. Use `set T := hfin.toFinset with hT`. Establish `memT : ∀ v, v ∈ T ↔ D ∈ v.asIdeal` using `fun v => hfin.mem_toFinset`. Establish `hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ γ ∈ URat hc n, Formalism.HermitianLatticesTheory.gmap (Formalism.UG.glEquiv γ) (locF v (stdLat E n)) = locF v N`.

Introduce `v`. Take `⟨PP, hPP⟩` from `over_lemma_6 (E := E) v`. Take `⟨g, hg, hgl⟩` from `hG PP.asIdeal PP.isMaximal`. Take `⟨γ, hγ, rfl⟩` from `unit_lemma_5 hc g hg`. Use `⟨γ, hγ, ?_⟩` and prove the remaining obligations.

Rewrite `hgl` using `[hLoc F E hc n PP, hLoc F E hc n PP, hPP]`. Conclude with `hgl`. Use `choose γ hγ hγl using hloc`. Take `⟨x, hx, hx1, hx2⟩` from `hGl F E hc n T (fun v => ⟨γ v, hγ v⟩)`. Establish `hx1' : ∀ v ∈ T, eAt E v • ((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = eAt E v • ((Formalism.UG.bc (iA F E) ((γ v)⁻¹) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Her …` using `hx1`.

Establish `hx2' : eP E (fun v => v ∉ T) • ((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = eP E (fun v => v ∉ T) • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))` using `hx2`. Use `⟨x, hx, ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Rewrite using `[glob_lemma_2]`. Establish `hTv : ∀ v ∈ T, ((∀ i, eAt E v * (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (y j))) i ∈ Formalism.L2.Herm.intAf F E) ↔ y ∈ locF v N)`.

Introduce `v hv`. Rewrite using `[← hγl v, asm_mem_gmap, hMem F E n v]`. Use `forall_congr' fun i => ?_` and prove the remaining obligations. Rewrite using `[asm_smul_mulVec _ _ _ (hx1' v hv), asm_bc_mulVec]`. Establish `hout : ∀ i, eP E (fun v => v ∉ T) * (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (y j))) i = eP E (fun v => v ∉ T) * iA F E (y i)`.

Introduce `i`. Rewrite using `[asm_smul_mulVec _ _ _ hx2', Matrix.one_mulVec]`. Establish `hPT : eP E (fun v => v ∉ T) = eP E (fun v : HeightOneSpectrum (𝓞 F) => D ∉ v.asIdeal)`. Use `congr 1`. Use function extensionality and compare the values at `v`.

Rewrite using `[memT]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Establish `hloc' : ∀ v ∈ T, y ∈ locF v N` using `fun v hv => (hTv v hv).1 (fun i => ((split_lemma_8 hI T _).1 (hy i)).1 v hv)`. Establish `hout' : ∀ i, eP E (fun v => v ∉ T) * iA F E (y i) ∈ Formalism.L2.Herm.intAf F E` using `fun i => by`.

Rewrite using `[← hout i]`. Conclude with `((split_lemma_8 hI T _).1 (hy i)).2`. Set `J : Ideal (𝓞 F)` to `{ carrier := {a | algebraMap (𝓞 F) (𝓞 E) a • y ∈ N} add_mem' := by`. Introduce `a b ha hb`. Use `show algebraMap (𝓞 F) (𝓞 E) (a + b) • y ∈ N`.

Rewrite using `[map_add, add_smul]`. Conclude with `N.add_mem ha hb`. Use the proof step `zero_mem' := by show algebraMap (𝓞 F) (𝓞 E) 0 • y ∈ N`. Rewrite using `[map_zero, zero_smul]`. Conclude with `N.zero_mem`.

Use the proof step `smul_mem' := by`. Introduce `c a ha`. Use `show algebraMap (𝓞 F) (𝓞 E) (c • a) • y ∈ N`. Rewrite using `[smul_eq_mul, map_mul, mul_smul]`. Conclude with `N.smul_mem _ ha }`.

Establish `hJ : J = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨Mx, hM, hJM⟩` from `Ideal.exists_le_maximal J hne`. Establish `hM0 : Mx ≠ ⊥` using `by first`. Consider the case `exact Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField (K := F))`.

Consider the case `exact Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)`. Consider the case `exact Ideal.IsMaximal.ne_bot_of_isIntegral_int hM`. Set `w : HeightOneSpectrum (𝓞 F)` to `⟨Mx, hM.isPrime, hM0⟩`. Distinguish the cases in `hw : w ∈ T`. Take `⟨s, hs, hsy⟩ : ∃ s ∈ complF E w, s • y ∈ N` from `hloc' w hw`.

Take `⟨r, hr, rfl⟩` from `asm_of_mem_complF hs`. Conclude with `hr (hJM (show r ∈ J from hsy))`. Establish `hyw : y ∈ locF w (stdLat E n)`. Rewrite using `[hMem F E n w]`. Introduce `i`.

Establish `hh` using `mul_mem ((hI F E).1 (fun u => u = w)) (hout' i)`. Rewrite `hh` using `[← mul_assoc, (hI F E).2.1]`. Establish `e : (fun u : HeightOneSpectrum (𝓞 F) => u = w ∧ u ∉ T) = (fun u => u = w)`. Use function extensionality and compare the values at `u`. Apply `propext` to reduce the goal to its premises.

Prove the components needed by the constructor for the conclusion. Conclude with `fun h => h.1`. Introduce `h`. Use `⟨h, ?_⟩` and prove the remaining obligations. Rewrite using `[h]`.

Conclude with `hw`. Rewrite `hh` using `[e]`. Conclude with `hh`. Take `⟨s, hs, hsy⟩ : ∃ s ∈ complF E w, s • y ∈ stdLat E n` from `hyw`. Take `⟨r, hr, rfl⟩` from `asm_of_mem_complF hs`.

Establish `hDw : D ∉ w.asIdeal` using `fun h => hw ((memT w).2 h)`. Establish `hmem : D * r ∈ J` using `by show algebraMap (𝓞 F) (𝓞 E) (D * r) • y ∈ N`. Rewrite using `[map_mul, mul_smul]`. Conclude with `hD2 _ hsy`. Conclude with `(w.isPrime.mem_or_mem (hJM hmem)).elim hDw hr`.

Establish `h1 : (1 : 𝓞 F) ∈ J` using `hJ ▸ Submodule.mem_top`. Establish `h1' : algebraMap (𝓞 F) (𝓞 E) 1 • y ∈ N` using `h1`. Rewrite `h1'` using `[map_one, one_smul]`. Then use the resulting hypothesis. Introduce `hy i`. Rewrite using `[split_lemma_8 hI T]`.

Use `⟨fun v hv => ?_, ?_⟩` and prove the remaining obligations. Conclude with `(hTv v hv).2 (⟨1, (complF E v).one_mem, by rwa [one_smul]⟩ : ∃ s ∈ complF E v, s • y ∈ N) i`. Rewrite using `[hout i, hPT]`. Apply `hCof F E D hD` to reduce the goal to its premises. Establish `hh` using `asm_iota_std (F := F) (hD1 y hy) i`.

Rewrite `hh` using `[asm_smul_apply, map_mul, ← asm_iota_OF]`. Conclude with `hh`.
-/
theorem genusToPoint_of (hLoc : LocEq) (hMem : MemLocFStd) (hCof : IdemCof) (hI : IdemCalc) (hGl : GlueExists)
    (hCm : Commens) : GenusToPoint := by
  intro F E _ _ _ _ _ _ hc n N hN hG
  obtain ⟨D, hD, hD1, hD2⟩ := hCm F E n N hN
  have hfin : {v : HeightOneSpectrum (𝓞 F) | D ∈ v.asIdeal}.Finite := by
    have h0 : Ideal.span ({D} : Set (𝓞 F)) ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hD
    exact (Ideal.finite_factors h0).subset (fun v hv => Ideal.dvd_span_singleton.2 hv)
  set T := hfin.toFinset with hT
  have memT : ∀ v, v ∈ T ↔ D ∈ v.asIdeal := fun v => hfin.mem_toFinset
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ γ ∈ URat hc n,
      Formalism.HermitianLatticesTheory.gmap (Formalism.UG.glEquiv γ) (locF v (stdLat E n)) = locF v N := by
    intro v
    obtain ⟨PP, hPP⟩ := over_lemma_6 (E := E) v
    obtain ⟨g, hg, hgl⟩ := hG PP.asIdeal PP.isMaximal
    obtain ⟨γ, hγ, rfl⟩ := unit_lemma_5 hc g hg
    refine ⟨γ, hγ, ?_⟩
    rw [hLoc F E hc n PP, hLoc F E hc n PP, hPP] at hgl
    exact hgl
  choose γ hγ hγl using hloc
  obtain ⟨x, hx, hx1, hx2⟩ := hGl F E hc n T (fun v => ⟨γ v, hγ v⟩)
  have hx1' : ∀ v ∈ T, eAt E v • ((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      eAt E v • ((Formalism.UG.bc (iA F E) ((γ v)⁻¹) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := hx1
  have hx2' : eP E (fun v => v ∉ T) • ((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = eP E (fun v => v ∉ T) • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := hx2
  refine ⟨x, hx, ?_⟩
  ext y
  rw [glob_lemma_2]
  have hTv : ∀ v ∈ T, ((∀ i, eAt E v * (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (y j))) i ∈ Formalism.L2.Herm.intAf F E) ↔
      y ∈ locF v N) := by
    intro v hv
    rw [← hγl v, asm_mem_gmap, hMem F E n v]
    refine forall_congr' fun i => ?_
    rw [asm_smul_mulVec _ _ _ (hx1' v hv), asm_bc_mulVec]
  have hout : ∀ i, eP E (fun v => v ∉ T) * (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (y j))) i =
      eP E (fun v => v ∉ T) * iA F E (y i) := by
    intro i
    rw [asm_smul_mulVec _ _ _ hx2', Matrix.one_mulVec]
  have hPT : eP E (fun v => v ∉ T) = eP E (fun v : HeightOneSpectrum (𝓞 F) => D ∉ v.asIdeal) := by
    congr 1
    funext v
    rw [memT]
  constructor
  · intro hy
    have hloc' : ∀ v ∈ T, y ∈ locF v N := fun v hv =>
      (hTv v hv).1 (fun i => ((split_lemma_8 hI T _).1 (hy i)).1 v hv)
    have hout' : ∀ i, eP E (fun v => v ∉ T) * iA F E (y i) ∈ Formalism.L2.Herm.intAf F E := fun i => by
      rw [← hout i]
      exact ((split_lemma_8 hI T _).1 (hy i)).2
    let J : Ideal (𝓞 F) :=
      { carrier := {a | algebraMap (𝓞 F) (𝓞 E) a • y ∈ N}
        add_mem' := by
          intro a b ha hb
          show algebraMap (𝓞 F) (𝓞 E) (a + b) • y ∈ N
          rw [map_add, add_smul]
          exact N.add_mem ha hb
        zero_mem' := by
          show algebraMap (𝓞 F) (𝓞 E) 0 • y ∈ N
          rw [map_zero, zero_smul]
          exact N.zero_mem
        smul_mem' := by
          intro c a ha
          show algebraMap (𝓞 F) (𝓞 E) (c • a) • y ∈ N
          rw [smul_eq_mul, map_mul, mul_smul]
          exact N.smul_mem _ ha }
    have hJ : J = ⊤ := by
      by_contra hne
      obtain ⟨Mx, hM, hJM⟩ := Ideal.exists_le_maximal J hne
      have hM0 : Mx ≠ ⊥ := by
        first
      | exact Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField (K := F))
      | exact Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)
      | exact Ideal.IsMaximal.ne_bot_of_isIntegral_int hM
      let w : HeightOneSpectrum (𝓞 F) := ⟨Mx, hM.isPrime, hM0⟩
      by_cases hw : w ∈ T
      · obtain ⟨s, hs, hsy⟩ : ∃ s ∈ complF E w, s • y ∈ N := hloc' w hw
        obtain ⟨r, hr, rfl⟩ := asm_of_mem_complF hs
        exact hr (hJM (show r ∈ J from hsy))
      · have hyw : y ∈ locF w (stdLat E n) := by
          rw [hMem F E n w]
          intro i
          have hh := mul_mem ((hI F E).1 (fun u => u = w)) (hout' i)
          rw [← mul_assoc, (hI F E).2.1] at hh
          have e : (fun u : HeightOneSpectrum (𝓞 F) => u = w ∧ u ∉ T) = (fun u => u = w) := by
            funext u
            apply propext
            constructor
            · exact fun h => h.1
            · intro h
              refine ⟨h, ?_⟩
              rw [h]
              exact hw
          rw [e] at hh
          exact hh
        obtain ⟨s, hs, hsy⟩ : ∃ s ∈ complF E w, s • y ∈ stdLat E n := hyw
        obtain ⟨r, hr, rfl⟩ := asm_of_mem_complF hs
        have hDw : D ∉ w.asIdeal := fun h => hw ((memT w).2 h)
        have hmem : D * r ∈ J := by
          show algebraMap (𝓞 F) (𝓞 E) (D * r) • y ∈ N
          rw [map_mul, mul_smul]
          exact hD2 _ hsy
        exact (w.isPrime.mem_or_mem (hJM hmem)).elim hDw hr
    have h1 : (1 : 𝓞 F) ∈ J := hJ ▸ Submodule.mem_top
    have h1' : algebraMap (𝓞 F) (𝓞 E) 1 • y ∈ N := h1
    rwa [map_one, one_smul] at h1'
  · intro hy i
    rw [split_lemma_8 hI T]
    refine ⟨fun v hv => ?_, ?_⟩
    · exact (hTv v hv).2 (⟨1, (complF E v).one_mem, by rwa [one_smul]⟩ : ∃ s ∈ complF E v, s • y ∈ N) i
    · rw [hout i, hPT]
      apply hCof F E D hD
      have hh := asm_iota_std (F := F) (hD1 y hy) i
      rw [asm_smul_apply, map_mul, ← asm_iota_OF] at hh
      exact hh

/- English proof (translation)
Establish `h : Formalism.UG.cT (hc.sig : E →+* E) (γ : Matrix (Fin n) (Fin n) E) * 1 * (γ : Matrix (Fin n) (Fin n) E) = 1` using `hγ`. Rewrite `h` using `[Matrix.mul_one]`. Establish `hU : (γ : Matrix (Fin n) (Fin n) E)ᴴ * (γ : Matrix (Fin n) (Fin n) E) = 1` using `h`. Introduce `a b`. Simplify using `only [hStd, LinearMap.mk₂'ₛₗ_apply, glEquiv_apply_lemma]`.

Express the relevant statement in the definitionally equal form `star ((γ : Matrix (Fin n) (Fin n) E) *ᵥ a) ⬝ᵥ ((γ : Matrix (Fin n) (Fin n) E) *ᵥ b) = star a ⬝ᵥ b`. Rewrite using `[Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hU, Matrix.vecMul_one]`.
-/
private theorem isom_lemma_3 {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} (γ : GL (Fin n) E) (hγ : γ ∈ URat hc n) :
    Formalism.UG.glEquiv γ ∈ Formalism.HermitianLatticesTheory.isom (hStd E n) := by
  have h : Formalism.UG.cT (hc.sig : E →+* E) (γ : Matrix (Fin n) (Fin n) E) * 1 * (γ : Matrix (Fin n) (Fin n) E) = 1 := hγ
  rw [Matrix.mul_one] at h
  have hU : (γ : Matrix (Fin n) (Fin n) E)ᴴ * (γ : Matrix (Fin n) (Fin n) E) = 1 := h
  intro a b
  simp only [hStd, LinearMap.mk₂'ₛₗ_apply, glEquiv_apply_lemma]
  change star ((γ : Matrix (Fin n) (Fin n) E) *ᵥ a) ⬝ᵥ ((γ : Matrix (Fin n) (Fin n) E) *ᵥ b) = star a ⬝ᵥ b
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hU, Matrix.vecMul_one]

/- English proof (translation)
Establish `K1 : ∀ z : Sp E n, (((Formalism.UG.bc (iA F E) γ)⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (z j)) = fun i => iA F E (((((γ⁻¹ : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E) *ᵥ z) i)`. Introduce `z`. Rewrite using `[← map_inv (Formalism.UG.bc (iA F E)) γ]`. Conclude with `asm_bc_mulVec γ⁻¹ z`. Use extensionality with `y`.

Rewrite using `[asm_mem_gmap]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Establish `hy'` using `(hMem F E n v _).1 hy`. Establish `hu : ∀ i, eAt E v * (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (y j))) i ∈ Formalism.L2.Herm.intAf F E`.

Introduce `i`. Establish `e : ((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (y j)) = ((x⁻¹ * Formalism.UG.bc (iA F E) γ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) …`. Rewrite using `[← K1 y, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right]`. Rewrite using `[e]`. Conclude with `asm_mulVec_int hI (fun w => w = v) _ _ h2 hy' i`.

Use `choose r hr hru using fun i => hDen F E v _ (hu i)`. Establish `hR : (∏ i, r i) ∈ v.asIdeal.primeCompl` using `prod_mem fun i _ => hr i`. Use `show ∃ s ∈ complF E v, s • y ∈ Formalism.UG.CS.globLat x (stdLat E n)`. Use `⟨algebraMap (𝓞 F) (𝓞 E) (∏ i, r i), asm_mem_complF v _ hR, ?_⟩` and prove the remaining obligations. Rewrite using `[glob_lemma_2]`.

Introduce `i`. Establish `es : (fun j => iA F E ((algebraMap (𝓞 F) (𝓞 E) (∏ i, r i) • y) j)) = iA F E (algebraMap (𝓞 F) E (∏ i, r i)) • (fun j => iA F E (y j))`. Use function extensionality and compare the values at `j`. Rewrite using `[asm_smul_apply, map_mul, asm_iota_OF]`. Both sides reduce to the same expression.

Rewrite using `[es, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_prod, map_prod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), mul_right_comm]`. Conclude with `mul_mem (hru i) (prod_mem fun j _ => asm_iota_OF_mem (r j))`. Introduce `hy`. Take `⟨s, hs, hsy⟩ : ∃ s ∈ complF E v, s • y ∈ Formalism.UG.CS.globLat x (stdLat E n)` from `hy`. Rewrite `hsy` using `[glob_lemma_2]`.

Establish `hw' : ∀ j, eP E (fun w => w = v) * (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E ((s • y) j))) j ∈ Formalism.L2.Herm.intAf F E` using `fun j => mul_mem ((hI F E).1 _) (hsy j)`. Establish `hz : s • ((((γ⁻¹ : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E) *ᵥ y) ∈ locF v (stdLat E n)`. Rewrite using `[hMem F E n v]`. Introduce `i`. Establish `e : (fun j => iA F E ((s • ((((γ⁻¹ : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E) *ᵥ y)) j)) = (((Formalism.UG.bc (iA F E) γ)⁻¹ * x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.He …`.

Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right, K1, Matrix.mulVec_smul]`. Establish `hh` using `asm_mulVec_int hI (fun w => w = v) _ _ h1 hw' i`. Rewrite `hh` using `[← e]`. Conclude with `hh`. Take `⟨t, ht, htz⟩ : ∃ t ∈ complF E v, t • (s • ((((γ⁻¹ : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E) *ᵥ y)) ∈ stdLat E n` from `hz`.

Conclude with `(⟨t * s, (complF E v).mul_mem ht hs, by rw [mul_smul]; exact htz⟩ : ∃ t ∈ complF E v, t • ((((γ⁻¹ : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E) *ᵥ y) ∈ stdLat E n)`.
-/
private theorem pt_loc_lemma_4 {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hMem : MemLocFStd) (hDen : IdemDenom) (hI : IdemCalc) {n : ℕ}
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (γ : GL (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (h1 : Formalism.L2.GenusGluing.Gen.IntAt v (((Formalism.UG.bc (iA F E) γ)⁻¹ * x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))
    (h2 : Formalism.L2.GenusGluing.Gen.IntAt v ((x⁻¹ * Formalism.UG.bc (iA F E) γ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) :
    Formalism.HermitianLatticesTheory.gmap (Formalism.UG.glEquiv γ) (locF v (stdLat E n)) = locF v (Formalism.UG.CS.globLat x (stdLat E n)) := by
  have K1 : ∀ z : Sp E n, (((Formalism.UG.bc (iA F E) γ)⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (z j)) =
      fun i => iA F E (((((γ⁻¹ : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E) *ᵥ z) i) := by
    intro z
    rw [← map_inv (Formalism.UG.bc (iA F E)) γ]
    exact asm_bc_mulVec γ⁻¹ z
  ext y
  rw [asm_mem_gmap]
  constructor
  · intro hy
    have hy' := (hMem F E n v _).1 hy
    have hu : ∀ i, eAt E v * (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (y j))) i ∈ Formalism.L2.Herm.intAf F E := by
      intro i
      have e : ((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (y j)) =
          ((x⁻¹ * Formalism.UG.bc (iA F E) γ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ
            (fun j => iA F E (((((γ⁻¹ : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E) *ᵥ y) j)) := by
        rw [← K1 y, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right]
      rw [e]
      exact asm_mulVec_int hI (fun w => w = v) _ _ h2 hy' i
    choose r hr hru using fun i => hDen F E v _ (hu i)
    have hR : (∏ i, r i) ∈ v.asIdeal.primeCompl := prod_mem fun i _ => hr i
    show ∃ s ∈ complF E v, s • y ∈ Formalism.UG.CS.globLat x (stdLat E n)
    refine ⟨algebraMap (𝓞 F) (𝓞 E) (∏ i, r i), asm_mem_complF v _ hR, ?_⟩
    rw [glob_lemma_2]
    intro i
    have es : (fun j => iA F E ((algebraMap (𝓞 F) (𝓞 E) (∏ i, r i) • y) j)) =
        iA F E (algebraMap (𝓞 F) E (∏ i, r i)) • (fun j => iA F E (y j)) := by
      funext j
      rw [asm_smul_apply, map_mul, asm_iota_OF]
      rfl
    rw [es, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_prod, map_prod,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), mul_right_comm]
    exact mul_mem (hru i) (prod_mem fun j _ => asm_iota_OF_mem (r j))
  · intro hy
    obtain ⟨s, hs, hsy⟩ : ∃ s ∈ complF E v, s • y ∈ Formalism.UG.CS.globLat x (stdLat E n) := hy
    rw [glob_lemma_2] at hsy
    have hw' : ∀ j, eP E (fun w => w = v) *
        (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E ((s • y) j))) j ∈ Formalism.L2.Herm.intAf F E :=
      fun j => mul_mem ((hI F E).1 _) (hsy j)
    have hz : s • ((((γ⁻¹ : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E) *ᵥ y) ∈ locF v (stdLat E n) := by
      rw [hMem F E n v]
      intro i
      have e : (fun j => iA F E ((s • ((((γ⁻¹ : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E) *ᵥ y)) j)) =
          (((Formalism.UG.bc (iA F E) γ)⁻¹ * x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ
            (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E ((s • y) j))) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right, K1, Matrix.mulVec_smul]
      have hh := asm_mulVec_int hI (fun w => w = v) _ _ h1 hw' i
      rw [← e] at hh
      exact hh
    obtain ⟨t, ht, htz⟩ : ∃ t ∈ complF E v, t • (s • ((((γ⁻¹ : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E) *ᵥ y)) ∈ stdLat E n := hz
    exact (⟨t * s, (complF E v).mul_mem ht hs, by rw [mul_smul]; exact htz⟩ :
      ∃ t ∈ complF E v, t • ((((γ⁻¹ : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E) *ᵥ y) ∈ stdLat E n)

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hc n hW x hx p hp`. Establish `hne : p ≠ ⊥` using `by first`. Consider the case `exact Ring.ne_bot_of_isMaximal_of_not_isField hp (NumberField.RingOfIntegers.not_isField (K := E))`. Consider the case `exact Ring.ne_bot_of_isMaximal_of_not_isField hp (NumberField.RingOfIntegers.not_isField E)`. Consider the case `exact Ideal.IsMaximal.ne_bot_of_isIntegral_int hp`.

Take `⟨γ, hγ, h1, h2⟩` from `hW x hx (Formalism.L2.DIV.underPl F ⟨p, hp.isPrime, hne⟩)`. Use `⟨Formalism.UG.glEquiv γ, isom_lemma_3 hc γ hγ, ?_⟩` and prove the remaining obligations. Establish `e1` using `hLoc F E hc n ⟨p, hp.isPrime, hne⟩ (stdLat E n)`. Establish `e2` using `hLoc F E hc n ⟨p, hp.isPrime, hne⟩ (Formalism.UG.CS.globLat x (stdLat E n))`. Simplify using `only at e1 e2`.

Rewrite using `[e1, e2]`. Conclude with `pt_loc_lemma_4 hMem hDen hI x γ _ h1 h2`.
-/
theorem pointToGenus_of (hLoc : LocEq) (hMem : MemLocFStd) (hDen : IdemDenom) (hI : IdemCalc) : PointToGenus := by
  intro F E _ _ _ _ _ _ hc n hW x hx p hp
  have hne : p ≠ ⊥ := by
    first
      | exact Ring.ne_bot_of_isMaximal_of_not_isField hp (NumberField.RingOfIntegers.not_isField (K := E))
      | exact Ring.ne_bot_of_isMaximal_of_not_isField hp (NumberField.RingOfIntegers.not_isField E)
      | exact Ideal.IsMaximal.ne_bot_of_isIntegral_int hp
  obtain ⟨γ, hγ, h1, h2⟩ := hW x hx (Formalism.L2.DIV.underPl F ⟨p, hp.isPrime, hne⟩)
  refine ⟨Formalism.UG.glEquiv γ, isom_lemma_3 hc γ hγ, ?_⟩
  have e1 := hLoc F E hc n ⟨p, hp.isPrime, hne⟩ (stdLat E n)
  have e2 := hLoc F E hc n ⟨p, hp.isPrime, hne⟩ (Formalism.UG.CS.globLat x (stdLat E n))
  dsimp only at e1 e2
  rw [e1, e2]
  exact pt_loc_lemma_4 hMem hDen hI x γ _ h1 h2

end Formalism.L2.GenusGluing.Gen
