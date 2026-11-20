import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspForm
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NumFieldHosCountable

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

namespace GlobalTheory.CompanionTheory.CTFin

section Abstract

variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Establish `: MeasurableConstVAdd Γ G` using `⟨fun γ => (continuous_const.add continuous_id : Continuous fun x : G => (γ : G) + x).measurable⟩`. Establish `: VAddInvariantMeasure Γ G μ` using `⟨fun γ s _ => measure_preimage_add μ (γ : G) s⟩`. Set `e : G ≃ᵐ G` to `(Homeomorph.mk T.toEquiv hc hc').toMeasurableEquiv`. Establish `hH : (μ.map T).IsAddHaarMeasure` using `AddEquiv.isAddHaarMeasure_map μ T hc hc'`. Establish `hmapE : μ.map T = μ.map e` using `rfl`.

Set `eΓ : Γ ≃ Γ` to `{ toFun := fun γ => ⟨T.symm γ, (hΓ _).1 (by simp)⟩ invFun := fun γ => ⟨T γ, (hΓ _).2 γ.2⟩ left_inv := fun γ => by simp right_inv := fun γ => by simp }`. Establish `hfd : IsAddFundamentalDomain Γ (T '' 𝓕) (μ.map T)`. Use `IsAddFundamentalDomain.image_of_equiv h𝓕 T.toEquiv ?_ eΓ ?_` and prove the remaining obligations. Rewrite using `[hmapE]`. Conclude with `(MeasurePreserving.symm e (e.measurable.measurePreserving μ)).quasiMeasurePreserving`.

Introduce `γ x`. Express the relevant statement in the definitionally equal form `T ((T.symm (γ : G)) + x) = (γ : G) + T x`. Simplify using the standard rewrite rules. Take `⟨c, hc0, hcμ⟩ : ∃ c : NNReal, c ≠ 0 ∧ μ.map T = c • μ` from `⟨_, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map T) μ).ne', Measure.isAddLeftInvariant_eq_smul (μ.map T) μ⟩`. Establish `hfd' : IsAddFundamentalDomain Γ (T '' 𝓕) μ`.

Use `hfd.mono ?_` and prove the remaining obligations. Rewrite using `[hcμ]`. Conclude with `Measure.absolutelyContinuous_smul (ENNReal.coe_ne_zero.2 hc0)`. Establish `hm : μ 𝓕 = μ (T '' 𝓕)` using `h𝓕.measure_eq hfd'`. Establish `hne : μ 𝓕 ≠ 0` using `h𝓕.measure_ne_zero (NeZero.ne μ)`.

Establish `hpre : e ⁻¹' (T '' 𝓕) = 𝓕`. Use extensionality with `x`. Conclude with `T.injective.mem_set_image`. Establish `h1 : (c : ENNReal) * μ 𝓕 = 1 * μ 𝓕`. Establish `h2 : (μ.map T) (T '' 𝓕) = μ 𝓕` using `by rw [hmapE, e.map_apply, hpre]`.

Rewrite `h2` using `[hcμ, Measure.smul_apply, ← hm, ENNReal.smul_def, smul_eq_mul]`. Rewrite using `[h2, one_mul]`. Establish `hc1 : c = 1`. Establish `h3 : (c : ENNReal) = 1` using `(ENNReal.mul_left_inj hne hfin.ne).1 h1`. Conclude with `h3` after adjusting the coercions.

Establish `hmp : MeasurePreserving e μ μ` using `⟨e.measurable, by rw [← hmapE, hcμ, hc1, one_smul]⟩`. Establish `h4` using `hmp.setIntegral_image_emb e.measurableEmbedding f 𝓕`. Establish `h5 : ∫ y in T '' 𝓕, f y ∂μ = ∫ x in 𝓕, f x ∂μ` using `hfd'.setIntegral_eq h𝓕 fun γ x => hf γ γ.2 x`. Conclude with `h4.symm.trans h5`.
-/
theorem setIntegral_comp_addEquiv_of_fundamentalDomain (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G)
    [μ.IsAddHaarMeasure] (𝓕 : Set G) (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (hfin : μ 𝓕 < ⊤)
    (T : G ≃+ G) (hc : Continuous T) (hc' : Continuous T.symm) (hΓ : ∀ x, T x ∈ Γ ↔ x ∈ Γ)
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (f : G → X)
    (hf : ∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) : ∫ x in 𝓕, f (T x) ∂μ = ∫ x in 𝓕, f x ∂μ := by
  have : MeasurableConstVAdd Γ G :=
    ⟨fun γ => (continuous_const.add continuous_id : Continuous fun x : G => (γ : G) + x).measurable⟩
  have : VAddInvariantMeasure Γ G μ := ⟨fun γ s _ => measure_preimage_add μ (γ : G) s⟩
  let e : G ≃ᵐ G := (Homeomorph.mk T.toEquiv hc hc').toMeasurableEquiv
  have hH : (μ.map T).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ T hc hc'
  have hmapE : μ.map T = μ.map e := rfl
  let eΓ : Γ ≃ Γ :=
    { toFun := fun γ => ⟨T.symm γ, (hΓ _).1 (by simp)⟩
      invFun := fun γ => ⟨T γ, (hΓ _).2 γ.2⟩
      left_inv := fun γ => by simp
      right_inv := fun γ => by simp }
  have hfd : IsAddFundamentalDomain Γ (T '' 𝓕) (μ.map T) := by
    refine IsAddFundamentalDomain.image_of_equiv h𝓕 T.toEquiv ?_ eΓ ?_
    · rw [hmapE]
      exact (MeasurePreserving.symm e (e.measurable.measurePreserving μ)).quasiMeasurePreserving
    · intro γ x
      change T ((T.symm (γ : G)) + x) = (γ : G) + T x
      simp
  obtain ⟨c, hc0, hcμ⟩ : ∃ c : NNReal, c ≠ 0 ∧ μ.map T = c • μ :=
    ⟨_, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map T) μ).ne',
      Measure.isAddLeftInvariant_eq_smul (μ.map T) μ⟩
  have hfd' : IsAddFundamentalDomain Γ (T '' 𝓕) μ := by
    refine hfd.mono ?_
    rw [hcμ]
    exact Measure.absolutelyContinuous_smul (ENNReal.coe_ne_zero.2 hc0)
  have hm : μ 𝓕 = μ (T '' 𝓕) := h𝓕.measure_eq hfd'
  have hne : μ 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne μ)
  have hpre : e ⁻¹' (T '' 𝓕) = 𝓕 := by
    ext x
    exact T.injective.mem_set_image
  have h1 : (c : ENNReal) * μ 𝓕 = 1 * μ 𝓕 := by
    have h2 : (μ.map T) (T '' 𝓕) = μ 𝓕 := by rw [hmapE, e.map_apply, hpre]
    rw [hcμ, Measure.smul_apply, ← hm, ENNReal.smul_def, smul_eq_mul] at h2
    rw [h2, one_mul]
  have hc1 : c = 1 := by
    have h3 : (c : ENNReal) = 1 := (ENNReal.mul_left_inj hne hfin.ne).1 h1
    exact_mod_cast h3
  have hmp : MeasurePreserving e μ μ := ⟨e.measurable, by rw [← hmapE, hcμ, hc1, one_smul]⟩
  have h4 := hmp.setIntegral_image_emb e.measurableEmbedding f 𝓕
  have h5 : ∫ y in T '' 𝓕, f y ∂μ = ∫ x in 𝓕, f x ∂μ :=
    hfd'.setIntegral_eq h𝓕 fun γ x => hf γ γ.2 x
  exact h4.symm.trans h5

end Abstract

section Block

variable {a r : ℕ} {R : Type} [CommRing R]

def BlockDiag (r : ℕ) (M : Matrix (Fin a) (Fin a) R) : Prop :=
  ∀ i j : Fin a, ¬ ((i : ℕ) < r ↔ (j : ℕ) < r) → M i j = 0

def upperRightBlockConj (B C : Matrix (Fin a) (Fin a) R) (x : BlockIx a r → R) : BlockIx a r → R :=
  fun p => (B * nilM x * C) p.1.1 p.1.2

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [nilM, Matrix.of_apply, Matrix.add_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem nilM_add' (x y : BlockIx a r → R) : nilM (x + y) = nilM x + nilM y := by
  ext i j
  simp only [nilM, Matrix.of_apply, Matrix.add_apply]
  split_ifs <;> simp

/- English proof (translation)
Introduce `x y h`. Use function extensionality and compare the values at `p`. Use `congrFun (congrFun h p.1.1) p.1.2` as an intermediate fact. Simplify `this` using `only [nilM, Matrix.of_apply, dif_pos p.2]`.
-/
theorem nilM_injective : Function.Injective (nilM : (BlockIx a r → R) → Matrix (Fin a) (Fin a) R) := by
  intro x y h
  funext p
  have := congrFun (congrFun h p.1.1) p.1.2
  simpa only [nilM, Matrix.of_apply, dif_pos p.2] using this

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `h : (i : ℕ) < r ∧ r ≤ (j : ℕ)`. Simplify using `only [nilM, Matrix.of_apply, dif_pos h, upperRightBlockConj]`. Rewrite using `[nilM, Matrix.of_apply, dif_neg h, Matrix.mul_apply]`. Use `(Finset.sum_eq_zero fun l _ => ?_).symm` and prove the remaining obligations.

Rewrite using `[Matrix.mul_apply, Finset.sum_mul]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : (k : ℕ) < r ∧ r ≤ (l : ℕ)`. Distinguish the cases in `hik : (i : ℕ) < r`. Rewrite using `[hC l j (by omega), mul_zero]`.

Rewrite using `[hB i k (by omega), zero_mul, zero_mul]`. Simplify using `[nilM, dif_neg hk]`.
-/
theorem nil_matrix_conj_block {B C : Matrix (Fin a) (Fin a) R} (hB : BlockDiag r B) (hC : BlockDiag r C)
    (x : BlockIx a r → R) : nilM (upperRightBlockConj B C x) = B * nilM x * C := by
  ext i j
  by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
  · simp only [nilM, Matrix.of_apply, dif_pos h, upperRightBlockConj]
  · rw [nilM, Matrix.of_apply, dif_neg h, Matrix.mul_apply]
    refine (Finset.sum_eq_zero fun l _ => ?_).symm
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : (k : ℕ) < r ∧ r ≤ (l : ℕ)
    · by_cases hik : (i : ℕ) < r
      · rw [hC l j (by omega), mul_zero]
      · rw [hB i k (by omega), zero_mul, zero_mul]
    · simp [nilM, dif_neg hk]

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `[upperRightBlockConj, nilM_add', mul_add, add_mul]`.
-/
theorem conj_block_add (B C : Matrix (Fin a) (Fin a) R) (x y : BlockIx a r → R) :
    upperRightBlockConj B C (x + y) = upperRightBlockConj B C x + upperRightBlockConj B C y := by
  funext p
  simp [upperRightBlockConj, nilM_add', mul_add, add_mul]

def conjE (m : GL (Fin a) R) (hm : BlockDiag r m.val) (hm' : BlockDiag r (m⁻¹).val) :
    (BlockIx a r → R) ≃+ (BlockIx a r → R) where
  toFun := upperRightBlockConj (m⁻¹).val m.val
  invFun := upperRightBlockConj m.val (m⁻¹).val
  left_inv x := nilM_injective <| by
    rw [nil_matrix_conj_block hm hm', nil_matrix_conj_block hm' hm]
    simp [Matrix.mul_assoc]
  right_inv x := nilM_injective <| by
    rw [nil_matrix_conj_block hm' hm, nil_matrix_conj_block hm hm']
    simp [Matrix.mul_assoc]
  map_add' := conj_block_add _ _

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(1 + nilM x) * m.val = m.val * (1 + nilM (upperRightBlockConj (m⁻¹).val m.val x))`. Rewrite using `[nil_matrix_conj_block hm' hm]`. Simplify using `[mul_add, add_mul, Matrix.mul_assoc]`.
-/
theorem unip_mul_eq (m : GL (Fin a) R) (hm : BlockDiag r m.val) (hm' : BlockDiag r (m⁻¹).val)
    (x : BlockIx a r → R) : unip x * m = m * unip (conjE m hm hm' x) := by
  apply Units.ext
  change (1 + nilM x) * m.val = m.val * (1 + nilM (upperRightBlockConj (m⁻¹).val m.val x))
  rw [nil_matrix_conj_block hm' hm]
  simp [mul_add, add_mul, Matrix.mul_assoc]

/- English proof (translation)
Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Distinguish the cases in `h : (i : ℕ) < r ∧ r ≤ (j : ℕ)`. Simplify `continuous_apply _` using `only [nilM, Matrix.of_apply, dif_pos h]`. Simplify `continuous_const` using `only [nilM, Matrix.of_apply, dif_neg h]`.
-/
theorem continuous_nilM {S : Type} [CommRing S] [TopologicalSpace S] :
    Continuous (nilM : (BlockIx a r → S) → Matrix (Fin a) (Fin a) S) := by
  refine continuous_matrix fun i j => ?_
  by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
  · simpa only [nilM, Matrix.of_apply, dif_pos h] using continuous_apply _
  · simpa only [nilM, Matrix.of_apply, dif_neg h] using continuous_const

/- English proof (translation)
The claim follows from `continuous_pi fun p => ((continuous_const.matrix_mul continuous_nilM).matrix_mul continuous_const).matrix_elem _ _`.
-/
theorem continuous_conj_block {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    (B C : Matrix (Fin a) (Fin a) S) : Continuous (upperRightBlockConj B C : (BlockIx a r → S) → _) :=
  continuous_pi fun p =>
    ((continuous_const.matrix_mul continuous_nilM).matrix_mul continuous_const).matrix_elem _ _

/- English proof (translation)
Establish `h : nilM (fun p => f (q p)) = (nilM q : Matrix (Fin a) (Fin a) R).map f`. Use extensionality with `i j`. Simplify using `only [nilM, Matrix.of_apply, Matrix.map_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Use function extensionality and compare the values at `p`.

Simplify using `only [upperRightBlockConj, h]`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul]`. Both sides reduce to the same expression.
-/
theorem conj_block_map {S : Type} [CommRing S] (f : R →+* S) (B C : Matrix (Fin a) (Fin a) R)
    (q : BlockIx a r → R) :
    upperRightBlockConj (B.map f) (C.map f) (fun p => f (q p)) = fun p => f (upperRightBlockConj B C q p) := by
  have h : nilM (fun p => f (q p)) = (nilM q : Matrix (Fin a) (Fin a) R).map f := by
    ext i j
    simp only [nilM, Matrix.of_apply, Matrix.map_apply]
    split_ifs <;> simp
  funext p
  simp only [upperRightBlockConj, h]
  rw [← Matrix.map_mul, ← Matrix.map_mul]
  rfl

end Block

section Levi

variable {R S : Type} [CommRing R] [CommRing S] {r s : ℕ}

/- English proof (translation)
Introduce `i j hij`. Rewrite using `[lev, GlobalTheory.SmGL.val_emb₂]`. Take `⟨u, rfl⟩` from `(GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i`. Take `⟨v, rfl⟩` from `(GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j`. Apply the tactic sequence `rcases u with u | u <;> rcases v with v | v`.

Conclude with `absurd (by simp [u.2, v.2]) hij`. Simplify using `[Matrix.reindex_apply]`. Simplify using `[Matrix.reindex_apply]`. Conclude with `absurd (by simp) hij`.
-/
theorem blockDiag_lev (g : GL (Fin r) R × GL (Fin s) R) : BlockDiag r (lev R r s g).val := by
  intro i j hij
  rw [lev, GlobalTheory.SmGL.val_emb₂]
  obtain ⟨u, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
  obtain ⟨v, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
  rcases u with u | u <;> rcases v with v | v
  · exact absurd (by simp [u.2, v.2]) hij
  · simp [Matrix.reindex_apply]
  · simp [Matrix.reindex_apply]
  · exact absurd (by simp) hij

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[lev, GlobalTheory.SmGL.val_emb₂]`. Express the relevant statement in the definitionally equal form `_ = (lev R r s g).val.map f`. Rewrite using `[lev, GlobalTheory.SmGL.val_emb₂]`. Use extensionality with `i j`.

Take `⟨u, rfl⟩` from `(GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i`. Take `⟨v, rfl⟩` from `(GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j`. Apply the tactic sequence `rcases u with u | u <;> rcases v with v | v <;> simp [Matrix.reindex_apply]`. Apply the tactic sequence `all_goals rfl`.
-/
theorem map_lev (f : R →+* S) (g : GL (Fin r) R × GL (Fin s) R) :
    lev S r s (Matrix.GeneralLinearGroup.map f g.1, Matrix.GeneralLinearGroup.map f g.2) =
      Matrix.GeneralLinearGroup.map f (lev R r s g) := by
  apply Units.ext
  rw [lev, GlobalTheory.SmGL.val_emb₂]
  change _ = (lev R r s g).val.map f
  rw [lev, GlobalTheory.SmGL.val_emb₂]
  ext i j
  obtain ⟨u, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
  obtain ⟨v, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
  rcases u with u | u <;> rcases v with v | v <;> simp [Matrix.reindex_apply]
  all_goals rfl

end Levi

section Main

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Take `⟨q, rfl⟩` from `hx`. Conclude with `⟨upperRightBlockConj b c q, (conj_block_map (algebraMap E (Ad E)) b c q).symm⟩`.
-/
theorem conj_block_mem_rational_nilradical {a r : ℕ} (b c : Matrix (Fin a) (Fin a) E) {x : BlockIx a r → Ad E}
    (hx : x ∈ ratN E a r) :
    upperRightBlockConj (b.map (algebraMap E (Ad E))) (c.map (algebraMap E (Ad E))) x ∈ ratN E a r := by
  obtain ⟨q, rfl⟩ := hx
  exact ⟨upperRightBlockConj b c q, (conj_block_map (algebraMap E (Ad E)) b c q).symm⟩

end Main

/- English proof (translation)
Introduce `E _ _ _ r s φ hl _ _ _ μ 𝓕 hμ h𝓕 γ g`. Use `haveI := hμ`. Take `⟨t2, lc, sc⟩` from `Formalism.IndefR.Eqv.G5.af_facts E`. Use `haveI : T2Space (Ad E) := t2`. Use `haveI : LocallyCompactSpace (Ad E) := lc`.

Use `haveI : SecondCountableTopology (Ad E) := sc`. Use `haveI := countable_ratN (E := E) (a := r + s) r`. Establish `hfin` using `covol_lt_top μ 𝓕 h𝓕`. Use `set ℓ := lev E r s γ with hℓ`. Use `set m := lev (Ad E) r s (ratGL E r γ.1, ratGL E s γ.2) with hmdef`.

Establish `hmℓ : m = ratGL E (r + s) ℓ` using `map_lev (algebraMap E (Ad E)) γ`. Establish `hm : BlockDiag r m.val` using `blockDiag_lev _`. Establish `hm' : BlockDiag r (m⁻¹).val`. Establish `e : m⁻¹ = lev (Ad E) r s ((ratGL E r γ.1)⁻¹, (ratGL E s γ.2)⁻¹)`. Rewrite using `[← Prod.inv_mk, map_inv]`.

Rewrite using `[e]`. Conclude with `blockDiag_lev _`. Establish `hval : m.val = ℓ.val.map (algebraMap E (Ad E))` using `by rw [hmℓ]; rfl`. Establish `hval' : (m⁻¹).val = (ℓ⁻¹).val.map (algebraMap E (Ad E))` using `by rw [hmℓ, ← map_inv]; rfl`. Establish `hΓ : ∀ x, conjE m hm hm' x ∈ ratN E (r + s) r ↔ x ∈ ratN E (r + s) r`.

Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1` using `conj_block_mem_rational_nilradical ℓ.val (ℓ⁻¹).val h`. Rewrite `h1` using `[← hval, ← hval']`.

Establish `h2 : (conjE m hm hm').symm (conjE m hm hm' x) ∈ ratN E (r + s) r` using `h1`. Simplify using `using h2`. Introduce `h`. Establish `h1` using `conj_block_mem_rational_nilradical (ℓ⁻¹).val ℓ.val h`. Rewrite `h1` using `[← hval, ← hval']`.

Conclude with `h1`. Establish `hper : ∀ y ∈ ratN E (r + s) r, ∀ x, φ.1 (unip (y + x) * g) = φ.1 (unip x * g)`. Introduce and unpack `_ ⟨q, rfl⟩ x`. Express the relevant statement in the definitionally equal form `φ.1 (unip ((fun p => algebraMap E (Ad E) (q p)) + x) * g) = _`. Rewrite using `[unip_add, unip_algebraMap, mul_assoc, hl]`.

Establish `key` using `setIntegral_comp_addEquiv_of_fundamentalDomain (ratN E (r + s) r) μ 𝓕 h𝓕 hfin (conjE m hm hm') (continuous_conj_block _ _) (continuous_conj_block _ _) hΓ (fun x => φ.1 (unip x * g)) hper`. Establish `e : ∀ x, φ.1 (unip x * (m * g)) = φ.1 (unip (conjE m hm hm' x) * g)`. Introduce `x`. Rewrite using `[← mul_assoc, unip_mul_eq m hm hm' x, mul_assoc]`. Establish `h` using `hl ℓ (unip (conjE m hm hm' x) * g)`.

Rewrite `h` using `[← hmℓ]`. Then use the resulting hypothesis. Simplify using `only [e]`. Conclude with `key`.
-/
theorem integral_unip_lev_mul : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (φ : Sm E (r + s)), (∀ (γ : GL (Fin (r + s)) E) (g : GA E (r + s)), φ.1 (ratGL E (r + s) γ * g) = φ.1 g) → IsOpen {k | finRep E (r + s) k φ = φ} → ∀ [MeasurableSpace (BlockIx (r + s) r → Ad E)] [BorelSpace (BlockIx (r + s) r → Ad E)] (μ : Measure (BlockIx (r + s) r → Ad E)) (𝓕 : Set (BlockIx (r + s) r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E (r + s) r) 𝓕 μ → ∀ (γ : GL (Fin r) E × GL (Fin s) E) (g : GA E (r + s)), ∫ x in 𝓕, φ.1 (unip x * (lev (Ad E) r s (ratGL E r γ.1, ratGL E s γ.2) * g)) ∂μ = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ := by
  intro E _ _ _ r s φ hl _ _ _ μ 𝓕 hμ h𝓕 γ g
  haveI := hμ
  obtain ⟨t2, lc, sc⟩ := Formalism.IndefR.Eqv.G5.af_facts E
  haveI : T2Space (Ad E) := t2
  haveI : LocallyCompactSpace (Ad E) := lc
  haveI : SecondCountableTopology (Ad E) := sc
  haveI := countable_ratN (E := E) (a := r + s) r
  have hfin := covol_lt_top μ 𝓕 h𝓕
  set ℓ := lev E r s γ with hℓ
  set m := lev (Ad E) r s (ratGL E r γ.1, ratGL E s γ.2) with hmdef
  have hmℓ : m = ratGL E (r + s) ℓ := map_lev (algebraMap E (Ad E)) γ
  have hm : BlockDiag r m.val := blockDiag_lev _
  have hm' : BlockDiag r (m⁻¹).val := by
    have e : m⁻¹ = lev (Ad E) r s ((ratGL E r γ.1)⁻¹, (ratGL E s γ.2)⁻¹) := by
      rw [← Prod.inv_mk, map_inv]
    rw [e]
    exact blockDiag_lev _
  have hval : m.val = ℓ.val.map (algebraMap E (Ad E)) := by rw [hmℓ]; rfl
  have hval' : (m⁻¹).val = (ℓ⁻¹).val.map (algebraMap E (Ad E)) := by rw [hmℓ, ← map_inv]; rfl
  have hΓ : ∀ x, conjE m hm hm' x ∈ ratN E (r + s) r ↔ x ∈ ratN E (r + s) r := by
    intro x
    constructor
    · intro h
      have h1 := conj_block_mem_rational_nilradical ℓ.val (ℓ⁻¹).val h
      rw [← hval, ← hval'] at h1
      have h2 : (conjE m hm hm').symm (conjE m hm hm' x) ∈ ratN E (r + s) r := h1
      simpa using h2
    · intro h
      have h1 := conj_block_mem_rational_nilradical (ℓ⁻¹).val ℓ.val h
      rw [← hval, ← hval'] at h1
      exact h1
  have hper : ∀ y ∈ ratN E (r + s) r, ∀ x, φ.1 (unip (y + x) * g) = φ.1 (unip x * g) := by
    rintro _ ⟨q, rfl⟩ x
    change φ.1 (unip ((fun p => algebraMap E (Ad E) (q p)) + x) * g) = _
    rw [unip_add, unip_algebraMap, mul_assoc, hl]
  have key := setIntegral_comp_addEquiv_of_fundamentalDomain (ratN E (r + s) r) μ 𝓕 h𝓕 hfin (conjE m hm hm')
    (continuous_conj_block _ _) (continuous_conj_block _ _) hΓ (fun x => φ.1 (unip x * g)) hper
  have e : ∀ x, φ.1 (unip x * (m * g)) = φ.1 (unip (conjE m hm hm' x) * g) := by
    intro x
    rw [← mul_assoc, unip_mul_eq m hm hm' x, mul_assoc]
    have h := hl ℓ (unip (conjE m hm hm' x) * g)
    rwa [← hmℓ] at h
  simp only [e]
  exact key

end GlobalTheory.CompanionTheory.CTFin
