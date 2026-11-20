import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HeightLattices.FinAlg
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HeightLattices.VolImageMulVec
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HeightLattices.IsModuleTopologyTens

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace PositivityTheory.SiegelWeilFormula.HeightDict

open PositivityTheory.SiegelWeilFormula.KWhit.Ht

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Take `⟨ho, hc⟩` from `lat_isCO (E := E) v n`. Conclude with `⟨ho.measure_ne_zero lam ⟨0, zero_mem _⟩, hc.measure_lt_top.ne⟩`.
-/
theorem lat_vol (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (lam : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    [lam.IsAddHaarMeasure] : lam (lat E v n : Set (Fin n → v.adicCompletion F ⊗[F] E)) ≠ 0 ∧
      lam (lat E v n : Set (Fin n → v.adicCompletion F ⊗[F] E)) ≠ ⊤ := by
  obtain ⟨ho, hc⟩ := lat_isCO (E := E) v n
  exact ⟨ho.measure_ne_zero lam ⟨0, zero_mem _⟩, hc.measure_lt_top.ne⟩

/- English proof (translation)
Use `GlobalTheory.LocTateInt.finite_FE (F := F) (E := E)` as an intermediate fact. Use `GlobalTheory.LocTateInt.isTopologicalRing_Ev (F := F) (E := E) v` as an intermediate fact. Use `GlobalTheory.LocTateInt.t2Space_Fv_tensor (F := F) (E := E) v` as an intermediate fact. Use `GlobalTheory.LocTateInt.locallyCompactSpace_Ev (F := F) (E := E) v` as an intermediate fact. Use `GlobalTheory.LocTateInt.secondCountable_Ev (F := F) (E := E) v` as an intermediate fact.

Use `GlobalTheory.LocTateInt.isModuleTopology_Ev (F := F) (E := E) v` as an intermediate fact. Establish `: BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)` using `⟨rfl⟩`. Use `set sg := HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ with hsg`. Set `Lsg : (v.adicCompletion F ⊗[F] E) →ₗ[v.adicCompletion F] (v.adicCompletion F ⊗[F] E)` to `(Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion F) (v.adicCompletion F)) σ).toLinearMap`. Establish `hL : ∀ z, Lsg z = sg z`.

Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [Lsg, hsg, HeckeCharacterZeroLocus.SiegelWeilU.sigR]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.

Establish `hc : Continuous sg`. Use `IsModuleTopology.continuous_of_linearMap Lsg` as an intermediate fact. Conclude with `(funext hL : ⇑Lsg = ⇑sg) ▸ this`. Establish `hcv : Continuous fun y : Fin n → v.adicCompletion F ⊗[F] E => fun i => sg (y i)` using `continuous_pi fun i => hc.comp (continuous_apply i)`. Set `φ : (Fin n → v.adicCompletion F ⊗[F] E) ≃ₜ+ (Fin n → v.adicCompletion F ⊗[F] E)` to `{ toFun := fun y i => sg (y i) invFun := fun y i => sg (y i) left_inv := fun y => funext fun i => sgv_sgv hcm v (y i) right_inv := fun y => funext fun i => sgv_sgv hcm v (y i) map_add' := fun y y' => funext fun i => map_add sg _ _ continuous_toFun := hcv continuous_invFun := hcv …`.

Establish `hsymm : φ.symm = φ` using `rfl`. Establish `hχ : addEquivAddHaarChar φ = 1`. Establish `h1` using `addEquivAddHaarChar_symm (φ := φ)`. Rewrite `h1` using `[hsymm]`. Establish `hpos` using `addEquivAddHaarChar_pos φ`.

Establish `h2 : addEquivAddHaarChar φ * addEquivAddHaarChar φ = 1` using `by conv_lhs => arg 1; rw [h1]`. Conclude with `inv_mul_cancel₀ hpos.ne'`. Establish `h3 : ((addEquivAddHaarChar φ : ℝ≥0) : ℝ) * (addEquivAddHaarChar φ : ℝ) = 1` using `by exact_mod_cast h2`. Break down `mul_self_eq_one_iff.1 h3 with h | h` into its components or cases. Conclude with `h` after adjusting the coercions.

Combine the linear relations using `[NNReal.coe_nonneg (addEquivAddHaarChar φ)]`. Establish `h1` using `addEquivAddHaarChar_smul_map lam φ`. Establish `himg : (fun y i => sg (y i)) '' S = φ.toHomeomorph.toMeasurableEquiv '' S` using `rfl`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1]`.

Use `_ = _ := by`. Rewrite using `[Measure.smul_apply, himg, hχ, one_smul]`. Establish `: Measure.map φ lam = Measure.map φ.toHomeomorph.toMeasurableEquiv lam` using `rfl`. Rewrite using `[this, MeasurableEquiv.map_apply, MeasurableEquiv.preimage_image]`.
-/
theorem vol_sig (hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    (lam : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) [lam.IsAddHaarMeasure]
    (S : Set (Fin n → v.adicCompletion F ⊗[F] E)) :
    lam ((fun y i => HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ (y i)) '' S) = lam S := by
  have := GlobalTheory.LocTateInt.finite_FE (F := F) (E := E)
  have := GlobalTheory.LocTateInt.isTopologicalRing_Ev (F := F) (E := E) v
  have := GlobalTheory.LocTateInt.t2Space_Fv_tensor (F := F) (E := E) v
  have := GlobalTheory.LocTateInt.locallyCompactSpace_Ev (F := F) (E := E) v
  have := GlobalTheory.LocTateInt.secondCountable_Ev (F := F) (E := E) v
  have := GlobalTheory.LocTateInt.isModuleTopology_Ev (F := F) (E := E) v
  have : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) := ⟨rfl⟩
  set sg := HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ with hsg
  let Lsg : (v.adicCompletion F ⊗[F] E) →ₗ[v.adicCompletion F] (v.adicCompletion F ⊗[F] E) :=
    (Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion F) (v.adicCompletion F)) σ).toLinearMap
  have hL : ∀ z, Lsg z = sg z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Lsg, hsg, HeckeCharacterZeroLocus.SiegelWeilU.sigR]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hc : Continuous sg := by
    have := IsModuleTopology.continuous_of_linearMap Lsg
    exact (funext hL : ⇑Lsg = ⇑sg) ▸ this
  have hcv : Continuous fun y : Fin n → v.adicCompletion F ⊗[F] E => fun i => sg (y i) :=
    continuous_pi fun i => hc.comp (continuous_apply i)
  let φ : (Fin n → v.adicCompletion F ⊗[F] E) ≃ₜ+ (Fin n → v.adicCompletion F ⊗[F] E) :=
    { toFun := fun y i => sg (y i)
      invFun := fun y i => sg (y i)
      left_inv := fun y => funext fun i => sgv_sgv hcm v (y i)
      right_inv := fun y => funext fun i => sgv_sgv hcm v (y i)
      map_add' := fun y y' => funext fun i => map_add sg _ _
      continuous_toFun := hcv
      continuous_invFun := hcv }
  have hsymm : φ.symm = φ := rfl
  have hχ : addEquivAddHaarChar φ = 1 := by
    have h1 := addEquivAddHaarChar_symm (φ := φ)
    rw [hsymm] at h1
    have hpos := addEquivAddHaarChar_pos φ
    have h2 : addEquivAddHaarChar φ * addEquivAddHaarChar φ = 1 := by
      conv_lhs => arg 1; rw [h1]
      exact inv_mul_cancel₀ hpos.ne'
    have h3 : ((addEquivAddHaarChar φ : ℝ≥0) : ℝ) * (addEquivAddHaarChar φ : ℝ) = 1 := by exact_mod_cast h2
    rcases mul_self_eq_one_iff.1 h3 with h | h
    · exact_mod_cast h
    · linarith [NNReal.coe_nonneg (addEquivAddHaarChar φ)]
  have h1 := addEquivAddHaarChar_smul_map lam φ
  have himg : (fun y i => sg (y i)) '' S = φ.toHomeomorph.toMeasurableEquiv '' S := rfl
  calc lam ((fun y i => sg (y i)) '' S) = (addEquivAddHaarChar φ • lam.map φ) ((fun y i => sg (y i)) '' S) := by
        rw [h1]
    _ = _ := by
      rw [Measure.smul_apply, himg, hχ, one_smul]
      have : Measure.map φ lam = Measure.map φ.toHomeomorph.toMeasurableEquiv lam := rfl
      rw [this, MeasurableEquiv.map_apply, MeasurableEquiv.preimage_image]

/- English proof (translation)
The claim follows from `GlobalTheory.Doubling.norm_sigR σ z`.
-/
theorem norm_sig (v : HeightOneSpectrum (𝓞 F)) (z : v.adicCompletion F ⊗[F] E) :
    Algebra.norm (v.adicCompletion F) (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ z) =
      Algebra.norm (v.adicCompletion F) z :=
  GlobalTheory.Doubling.norm_sigR σ z

/- English proof (translation)
Use `set sg := HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ with hsg`. Use `set O : Set (Fin n → v.adicCompletion F ⊗[F] E) := ((lat E v n : AddSubgroup _) : Set (Fin n → v.adicCompletion F ⊗[F] E)) with hO`. Use `set sv : (Fin n → v.adicCompletion F ⊗[F] E) → (Fin n → v.adicCompletion F ⊗[F] E) := fun y i => sg (y i) with hsv`. Establish `hsvO : ∀ y ∈ O, sv y ∈ O` using `fun y hy => (mem_lat v _).2 fun i => OE_sig v ((mem_lat v y).1 hy i)`. Establish `hsvsv : ∀ y, sv (sv y) = y` using `fun y => funext fun i => sgv_sgv hcm v (y i)`.

Establish `hsvM : ∀ (M : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E)) y, sv (M *ᵥ y) = M.map sg *ᵥ sv y` using `fun M y => funext fun i => RingHom.map_mulVec sg M y i`. Establish `hsvadd : ∀ y y', sv (y + y') = sv y + sv y'` using `fun y y' => funext fun i => map_add sg _ _`. Establish `hsvneg : ∀ y, sv (-y) = -sv y` using `fun y => funext fun i => map_neg sg _`. Establish `hsvsmul : ∀ (c : v.adicCompletion F ⊗[F] E) y, sv (c • y) = sg c • sv y` using `fun c y => funext fun i => map_mul sg _ _`. Establish `hkO : ∀ (M : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E)), (∀ i j, M i j ∈ OE E v) → ∀ y ∈ O, M *ᵥ y ∈ O` using `fun M hM y hy => (mem_lat v _).2 fun i => by`.

Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `sum_mem fun j _ => OE_mul v (hM i j) ((mem_lat v y).1 hy j)`. Establish `hk21 : ∀ i j, k.toBlocks₂₁ i j ∈ OE E v` using `fun i j => hk _ _`. Establish `hk22 : ∀ i j, k.toBlocks₂₂ i j ∈ OE E v` using `fun i j => hk _ _`. Establish `hβs : β.map sg = -(sg η • h)`.

Use extensionality with `a b`. Simplify using `[hβ, Matrix.transpose_apply, hh]`. Establish `hD1 : ∀ y, D *ᵥ (k.toBlocks₂₁ *ᵥ y) = e • (t *ᵥ y)` using `fun y => by`. Rewrite using `[Matrix.mulVec_mulVec, ← h1, Matrix.smul_mulVec]`. Establish `hD2 : ∀ y, D *ᵥ (k.toBlocks₂₂ *ᵥ y) = e • (β *ᵥ (u *ᵥ y))` using `fun y => by`.

Rewrite using `[Matrix.mulVec_mulVec, ← h2, Matrix.smul_mulVec, Matrix.mulVec_mulVec]`. Establish `hηu : (η • u).map sg = sg η • u.map sg`. Use extensionality with `a b`. Simplify using the standard rewrite rules. Use `set X : Set (Fin n → v.adicCompletion F ⊗[F] E) := {x | ∃ y ∈ latM v (t.map sg), ∃ y' ∈ latM v ((η • u).map sg), x = y + h *ᵥ y'} with hX`.

Establish `hset : (fun x => (sg e • (1 : Matrix (Fin n) (Fin n) _)) *ᵥ x) '' X = sv '' ((fun y => D *ᵥ y) '' O)`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, ⟨y, hy, y', hy', rfl⟩, rfl⟩`. Take `⟨a, ha, rfl⟩` from `hy`.

Take `⟨b, hb, rfl⟩` from `hy'`. Use `⟨D *ᵥ (k.toBlocks₂₁ *ᵥ sv a + k.toBlocks₂₂ *ᵥ (-sv b)), ⟨_, add_mem (hkO _ hk21 _ (hsvO _ ha)) (hkO _ hk22 _ (neg_mem (hsvO _ hb))), rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply]`. Rewrite using `[Matrix.mulVec_add, hD1, hD2, hsvadd, hsvsmul, hsvsmul, hsvM, hsvM, hsvM, hsvsv, hβs, hsvneg, hsvsv, Matrix.smul_mulVec, Matrix.one_mulVec, hηu]`. Simplify using `only [Matrix.neg_mulVec, Matrix.mulVec_neg, neg_neg, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_add, smul_neg]`.

Introduce and unpack `⟨_, ⟨z, hz, rfl⟩, rfl⟩`. Take `⟨y₁, y₂, hy₁, hy₂, hyz⟩` from `bottom_onto (OEsub E v) k k' hkk hk hk' z ((mem_lat v z).1 hz)`. Use `⟨t.map sg *ᵥ sv y₁ + h *ᵥ ((η • u).map sg *ᵥ (-sv y₂)), ⟨_, ⟨sv y₁, hsvO _ ((mem_lat v _).2 hy₁), rfl⟩, _, ⟨-sv y₂, neg_mem (hsvO _ ((mem_lat v _).2 hy₂)), rfl⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← hyz, Matrix.mulVec_add D, hD1, hD2, hsvadd, hsvsmul, hsvsmul, hsvM, hsvM, hsvM, hβs, hηu]`.

Simplify using `only [Matrix.mulVec_add, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec, Matrix.mulVec_neg, Matrix.mulVec_smul, smul_add, smul_neg, neg_neg, Matrix.mulVec_mulVec, Matrix.mul_smul, Matrix.smul_mul]`. Rewrite using `[Matrix.one_mul, Matrix.one_mul, Matrix.neg_mul, Matrix.smul_mul, Matrix.neg_mulVec, smul_neg, smul_comm (sg η) (sg e)]`. Simplify using `only [Matrix.smul_mulVec]`. Establish `hsc : IsUnit ((sg e • (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E))).det)`. Rewrite using `[Matrix.det_smul, Matrix.det_one, mul_one]`.

Conclude with `(he.map sg).pow _`. Establish `hnsc : ‖Algebra.norm (v.adicCompletion F) ((sg e • (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E))).det)‖₊ = 1`. Rewrite using `[Matrix.det_smul, Matrix.det_one, mul_one, map_pow, norm_sig, nnnorm_pow]`. Establish `: ‖Algebra.norm (v.adicCompletion F) e‖₊ = 1` using `by ext; simpa using he1`. Rewrite using `[this, one_pow]`.

Establish `hvX : lam X = ((‖Algebra.norm (v.adicCompletion F) D.det‖₊ : ℝ≥0) : ℝ≥0∞) * lam O`. Establish `e1` using `vol_image_mulVec' v lam (sg e • (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E))) hsc X`. Rewrite `e1` using `[hset, vol_sig hcm v lam, vol_image_mulVec' v lam D hD O, hnsc, ENNReal.coe_one, one_mul]`. Conclude with `e1.symm`. Establish `hdet : (t.map sg).det = sg t.det` using `(RingHom.map_det sg t).symm`.

Establish `htu' : IsUnit (t.map sg).det` using `by rw [hdet]; exact ht.map sg`. Establish `hvL1 : lam (latM v (t.map sg) : Set (Fin n → v.adicCompletion F ⊗[F] E)) = ((‖Algebra.norm (v.adicCompletion F) t.det‖₊ : ℝ≥0) : ℝ≥0∞) * lam O`. Establish `e2` using `vol_image_mulVec' v lam (t.map sg) htu' O`. Rewrite `e2` using `[hdet, norm_sig]`. Rewrite using `[← e2]`.

Both sides reduce to the same expression. Take `⟨hO0, hOT⟩` from `lat_vol (E := E) v lam`. Establish `hnt : (‖Algebra.norm (v.adicCompletion F) t.det‖₊ : ℝ≥0∞) ≠ 0`. Establish `: Algebra.norm (v.adicCompletion F) t.det ≠ 0` using `(ht.map (Algebra.norm (v.adicCompletion F))).ne_zero`. Simplify using `using this`.

Use `show _ = _ * (lam X / lam (latM v (t.map sg) : Set (Fin n → v.adicCompletion F ⊗[F] E))).toReal`. Rewrite using `[hvX, hvL1, ENNReal.mul_div_mul_right _ _ hO0 hOT, ENNReal.toReal_div, ENNReal.coe_toReal, ENNReal.coe_toReal, coe_nnnorm, coe_nnnorm]`. Establish `: ‖Algebra.norm (v.adicCompletion F) t.det‖ ≠ 0` using `by simpa using hnt`. Clear the denominators using the available nonvanishing facts.
-/
theorem fin_index (hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (t u D β h : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E)) (η e : v.adicCompletion F ⊗[F] E)
    (k k' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (v.adicCompletion F ⊗[F] E))
    (ht : IsUnit t.det) (hD : IsUnit D.det) (htu : tᵀ * u.map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) = 1)
    (hη : IsUnit η) (he : IsUnit e) (he1 : ‖Algebra.norm (v.adicCompletion F) e‖ = 1) (hβ : β = -(η • hᵀ))
    (hh : ∀ a b, HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ (h b a) = h a b) (hkk : k * k' = 1)
    (hk : ∀ i j, k i j ∈ OE E v) (hk' : ∀ i j, k' i j ∈ OE E v)
    (h1 : e • t = D * k.toBlocks₂₁) (h2 : e • (β * u) = D * k.toBlocks₂₂)
    (lam : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) [lam.IsAddHaarMeasure] :
    ‖Algebra.norm (v.adicCompletion F) D.det‖ = ‖Algebra.norm (v.adicCompletion F) t.det‖ *
      Gen.nu2 lam (latM v (t.map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ)))
        (latM v ((η • u).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ))) h := by
  set sg := HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ with hsg
  set O : Set (Fin n → v.adicCompletion F ⊗[F] E) := ((lat E v n : AddSubgroup _) : Set (Fin n → v.adicCompletion F ⊗[F] E)) with hO
  set sv : (Fin n → v.adicCompletion F ⊗[F] E) → (Fin n → v.adicCompletion F ⊗[F] E) := fun y i => sg (y i) with hsv
  have hsvO : ∀ y ∈ O, sv y ∈ O := fun y hy => (mem_lat v _).2 fun i => OE_sig v ((mem_lat v y).1 hy i)
  have hsvsv : ∀ y, sv (sv y) = y := fun y => funext fun i => sgv_sgv hcm v (y i)
  have hsvM : ∀ (M : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E)) y, sv (M *ᵥ y) = M.map sg *ᵥ sv y :=
    fun M y => funext fun i => RingHom.map_mulVec sg M y i
  have hsvadd : ∀ y y', sv (y + y') = sv y + sv y' := fun y y' => funext fun i => map_add sg _ _
  have hsvneg : ∀ y, sv (-y) = -sv y := fun y => funext fun i => map_neg sg _
  have hsvsmul : ∀ (c : v.adicCompletion F ⊗[F] E) y, sv (c • y) = sg c • sv y := fun c y => funext fun i => map_mul sg _ _
  have hkO : ∀ (M : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E)), (∀ i j, M i j ∈ OE E v) → ∀ y ∈ O, M *ᵥ y ∈ O :=
    fun M hM y hy => (mem_lat v _).2 fun i => by
      simp only [Matrix.mulVec, dotProduct]
      exact sum_mem fun j _ => OE_mul v (hM i j) ((mem_lat v y).1 hy j)
  have hk21 : ∀ i j, k.toBlocks₂₁ i j ∈ OE E v := fun i j => hk _ _
  have hk22 : ∀ i j, k.toBlocks₂₂ i j ∈ OE E v := fun i j => hk _ _

  have hβs : β.map sg = -(sg η • h) := by
    ext a b
    simp [hβ, Matrix.transpose_apply, hh]
  have hD1 : ∀ y, D *ᵥ (k.toBlocks₂₁ *ᵥ y) = e • (t *ᵥ y) := fun y => by
    rw [Matrix.mulVec_mulVec, ← h1, Matrix.smul_mulVec]
  have hD2 : ∀ y, D *ᵥ (k.toBlocks₂₂ *ᵥ y) = e • (β *ᵥ (u *ᵥ y)) := fun y => by
    rw [Matrix.mulVec_mulVec, ← h2, Matrix.smul_mulVec, Matrix.mulVec_mulVec]
  have hηu : (η • u).map sg = sg η • u.map sg := by
    ext a b; simp

  set X : Set (Fin n → v.adicCompletion F ⊗[F] E) :=
    {x | ∃ y ∈ latM v (t.map sg), ∃ y' ∈ latM v ((η • u).map sg), x = y + h *ᵥ y'} with hX
  have hset : (fun x => (sg e • (1 : Matrix (Fin n) (Fin n) _)) *ᵥ x) '' X = sv '' ((fun y => D *ᵥ y) '' O) := by
    ext w
    constructor
    · rintro ⟨x, ⟨y, hy, y', hy', rfl⟩, rfl⟩
      obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨b, hb, rfl⟩ := hy'
      refine ⟨D *ᵥ (k.toBlocks₂₁ *ᵥ sv a + k.toBlocks₂₂ *ᵥ (-sv b)), ⟨_, add_mem (hkO _ hk21 _ (hsvO _ ha))
        (hkO _ hk22 _ (neg_mem (hsvO _ hb))), rfl⟩, ?_⟩
      simp only [LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply]
      rw [Matrix.mulVec_add, hD1, hD2, hsvadd, hsvsmul, hsvsmul, hsvM, hsvM, hsvM, hsvsv, hβs, hsvneg, hsvsv,
        Matrix.smul_mulVec, Matrix.one_mulVec, hηu]
      simp only [Matrix.neg_mulVec, Matrix.mulVec_neg, neg_neg, Matrix.smul_mulVec, Matrix.mulVec_smul,
        smul_add, smul_neg]
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      obtain ⟨y₁, y₂, hy₁, hy₂, hyz⟩ := bottom_onto (OEsub E v) k k' hkk hk hk' z ((mem_lat v z).1 hz)
      refine ⟨t.map sg *ᵥ sv y₁ + h *ᵥ ((η • u).map sg *ᵥ (-sv y₂)),
        ⟨_, ⟨sv y₁, hsvO _ ((mem_lat v _).2 hy₁), rfl⟩, _, ⟨-sv y₂, neg_mem (hsvO _ ((mem_lat v _).2 hy₂)), rfl⟩, rfl⟩, ?_⟩
      dsimp only
      rw [← hyz, Matrix.mulVec_add D, hD1, hD2, hsvadd, hsvsmul, hsvsmul, hsvM, hsvM, hsvM, hβs, hηu]
      simp only [Matrix.mulVec_add, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec, Matrix.mulVec_neg,
        Matrix.mulVec_smul, smul_add, smul_neg, neg_neg, Matrix.mulVec_mulVec, Matrix.mul_smul, Matrix.smul_mul]
      rw [Matrix.one_mul, Matrix.one_mul, Matrix.neg_mul, Matrix.smul_mul, Matrix.neg_mulVec, smul_neg,
        smul_comm (sg η) (sg e)]
      simp only [Matrix.smul_mulVec]
  have hsc : IsUnit ((sg e • (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E))).det) := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact (he.map sg).pow _
  have hnsc : ‖Algebra.norm (v.adicCompletion F) ((sg e • (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E))).det)‖₊
      = 1 := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, map_pow, norm_sig, nnnorm_pow]
    have : ‖Algebra.norm (v.adicCompletion F) e‖₊ = 1 := by ext; simpa using he1
    rw [this, one_pow]
  have hvX : lam X = ((‖Algebra.norm (v.adicCompletion F) D.det‖₊ : ℝ≥0) : ℝ≥0∞) * lam O := by
    have e1 := vol_image_mulVec' v lam (sg e • (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E))) hsc X
    rw [hset, vol_sig hcm v lam, vol_image_mulVec' v lam D hD O, hnsc, ENNReal.coe_one, one_mul] at e1
    exact e1.symm
  have hdet : (t.map sg).det = sg t.det := (RingHom.map_det sg t).symm
  have htu' : IsUnit (t.map sg).det := by rw [hdet]; exact ht.map sg
  have hvL1 : lam (latM v (t.map sg) : Set (Fin n → v.adicCompletion F ⊗[F] E)) =
      ((‖Algebra.norm (v.adicCompletion F) t.det‖₊ : ℝ≥0) : ℝ≥0∞) * lam O := by
    have e2 := vol_image_mulVec' v lam (t.map sg) htu' O
    rw [hdet, norm_sig] at e2
    rw [← e2]
    rfl
  obtain ⟨hO0, hOT⟩ := lat_vol (E := E) v lam
  have hnt : (‖Algebra.norm (v.adicCompletion F) t.det‖₊ : ℝ≥0∞) ≠ 0 := by
    have : Algebra.norm (v.adicCompletion F) t.det ≠ 0 := (ht.map (Algebra.norm (v.adicCompletion F))).ne_zero
    simpa using this
  show _ = _ * (lam X / lam (latM v (t.map sg) : Set (Fin n → v.adicCompletion F ⊗[F] E))).toReal
  rw [hvX, hvL1, ENNReal.mul_div_mul_right _ _ hO0 hOT, ENNReal.toReal_div, ENNReal.coe_toReal, ENNReal.coe_toReal,
    coe_nnnorm, coe_nnnorm]
  have : ‖Algebra.norm (v.adicCompletion F) t.det‖ ≠ 0 := by simpa using hnt
  field_simp

end PositivityTheory.SiegelWeilFormula.HeightDict
