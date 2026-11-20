import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.SumSatUnit
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele

open UpperTheory.ConvolutionTheory.R
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Published PositivityTheory.RgJS

/- English proof (translation)
Rewrite using `[normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]`.
-/
private theorem normV_eq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    normV v = Ideal.absNorm v.asIdeal := by
  rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

/- English proof (translation)
Rewrite using `[normV_eq]`. Conclude with `NumberField.HeightOneSpectrum.one_lt_absNorm v`.
-/
private theorem one_lt_normV {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : 1 < normV v := by
  rw [normV_eq]
  exact NumberField.HeightOneSpectrum.one_lt_absNorm v

/- English proof (translation)
Introduce `hD K M _ _ _ _ _ _ _ _ hl η hη S₀ T₀`. Establish `hD'` using `hD K M hl`. Take `⟨⟨-, -, hN⟩, hG⟩` from `hη`. Establish `hNG` using `hN.and hG`. Use `beta_reduce at hD'`.

Rewrite `hD'`, `hNG` using `[Filter.eventually_cofinite]`. Establish `hten : Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K)) Filter.cofinite Filter.cofinite` using `GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M`. Use `set S : Finset (HeightOneSpectrum (𝓞 K)) := S₀ ∪ hD'.toFinset ∪ (T₀ ∪ hNG.toFinset).image (fun w => w.under (𝓞 K)) with hS`. Establish `hTfin : {w : HeightOneSpectrum (𝓞 M) | w.under (𝓞 K) ∈ S}.Finite`. Use `hten.eventually S.eventually_cofinite_notMem` as an intermediate fact.

Rewrite `this` using `[Filter.eventually_cofinite]`. Simplify using `using this`. Use `set T := hTfin.toFinset with hT`. Establish `hmemT : ∀ w, w ∈ T ↔ w.under (𝓞 K) ∈ S` using `fun w => by simp [hT]`. Establish `hgood : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) ∉ S → (∀ f : ℕ, normV w = normV (w.under (𝓞 K)) ^ f → η.val (w.under (𝓞 K)) ^ f = 1) ∧ η.UnrAt (w.under (𝓞 K)) ∧ (normV w = normV (w.under (𝓞 K)) ∨ IsPrimitiveRoot (η.val (w.under (𝓞 K))) (Module.finrank K M))`.

Introduce `w hw`. Assume the negation of the conclusion as `h`. Conclude with `hw (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_union_right _ (hNG.mem_toFinset.2 h))))`. Establish `hdec : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → (Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v} = Module.finrank K M ∧ ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v → normV w = normV v) ∨ (Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v} = 1 ∧ ∀ w : Heigh …`. Introduce `v hv`.

Assume the negation of the conclusion as `h`. Conclude with `hv (Finset.mem_union_left _ (Finset.mem_union_right _ (hD'.mem_toFinset.2 h)))`. Establish `hex : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∃ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v`. Introduce `v hv`. Establish `: Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v} ≠ 0`.

Break down `hdec v hv with h | h` into its components or cases. Rewrite using `[h.1]`. Conclude with `hl.ne_zero`. Rewrite using `[h.1]`. Conclude with `one_ne_zero`.

Take `⟨⟨w, hw⟩⟩` from `(Nat.card_ne_zero.1 this).1`. Conclude with `⟨w, hw⟩`. Establish `hne : ∀ v : HeightOneSpectrum (𝓞 K), normV v ^ Module.finrank K M ≠ normV v`. Introduce `v`. Use `Nat.pow_lt_pow_right (one_lt_normV v) hl.one_lt` as an intermediate fact.

Rewrite `this` using `[pow_one]`. Conclude with `this.ne'`. Set `u : Off M T → Off K S` to `fun w => ⟨w.1.under (𝓞 K), fun h => w.2 ((hmemT _).2 h)⟩`. Set `f : Off M T → ℕ` to `fun w => if normV w.1 = normV (w.1.under (𝓞 K)) then 1 else Module.finrank K M`. Establish `hnorm : ∀ w, normV w.1 = normV (u w).1 ^ f w`.

Introduce `w`. Distinguish the cases in `h : normV w.1 = normV (w.1.under (𝓞 K))`. Simplify using `only [f, if_pos h, pow_one]`. Conclude with `h`. Simplify using `only [f, if_neg h]`.

Break down `hdec _ (u w).2 with h' | h'` into its components or cases. Conclude with `absurd (h'.2 _ rfl) h`. Conclude with `h'.2 _ rfl`. Establish `hcard : ∀ v : Off K S, Nat.card {w // u w = v} = Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v.1}`. Introduce `v`.

Conclude with `Nat.card_congr { toFun := fun w => ⟨w.1.1, congrArg Subtype.val w.2⟩ invFun := fun w => ⟨⟨w.1, fun h => v.2 (w.2 ▸ (hmemT _).1 h)⟩, Subtype.ext w.2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl }`. Use `⟨S, T, u, f, fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ hv), fun w hw => (hmemT w).2 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_union_left _ hw))), fun _ => rfl, ?_, hnorm, ?_, ?_⟩` and prove the remaining obligations. Introduce `v`. Take `⟨w, hw⟩` from `hex v.1 v.2`. Conclude with `hw ▸ (hgood w (hw ▸ v.2)).2.1`.

Introduce `w`. Simplify `hnorm w` using `only [nq, normV_eq]`. Introduce `v`. Take `⟨w₀, hw₀⟩` from `hex v.1 v.2`. Establish `hg` using `hgood w₀ (hw₀ ▸ v.2)`.

Rewrite `hg` using `[hw₀]`. Break down `hdec v.1 v.2 with h | h` into its components or cases. Use `Or.inl ⟨(hcard v).trans h.1, fun w hw => ?_, ?_⟩` and prove the remaining obligations. Establish `hw' : w.1.under (𝓞 K) = v.1` using `congrArg Subtype.val hw`. Conclude with `if_pos (hw' ▸ h.2 _ hw')`.

Use `hg.1 1 (by rw [pow_one]; exact h.2 _ hw₀)` as an intermediate fact. Rewrite `this` using `[pow_one]`. Simplify using `[this]`. Use `Or.inr ⟨(hcard v).trans h.1, fun w hw => ?_, ?_⟩` and prove the remaining obligations. Establish `hw' : w.1.under (𝓞 K) = v.1` using `congrArg Subtype.val hw`.

Use `if_neg ?_` and prove the remaining obligations. Rewrite using `[h.2 _ hw', hw']`. Conclude with `hne _`. Break down `hg.2.2 with h' | h'` into its components or cases. Conclude with `absurd ((h.2 _ hw₀).symm.trans h') (hne _)`.

Conclude with `IsPrimitiveRoot.coe_units_iff.2 h'`.
-/
theorem UpperTheory.ConvolutionTheory.R.coverEx :
    Decomp → CoverEx := by
  classical
  intro hD K M _ _ _ _ _ _ _ _ hl η hη S₀ T₀
  have hD' := hD K M hl
  obtain ⟨⟨-, -, hN⟩, hG⟩ := hη
  have hNG := hN.and hG
  beta_reduce at hD'
  rw [Filter.eventually_cofinite] at hD' hNG
  have hten : Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K)) Filter.cofinite Filter.cofinite :=
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M
  set S : Finset (HeightOneSpectrum (𝓞 K)) :=
    S₀ ∪ hD'.toFinset ∪ (T₀ ∪ hNG.toFinset).image (fun w => w.under (𝓞 K)) with hS
  have hTfin : {w : HeightOneSpectrum (𝓞 M) | w.under (𝓞 K) ∈ S}.Finite := by
    have := hten.eventually S.eventually_cofinite_notMem
    rw [Filter.eventually_cofinite] at this
    simpa using this
  set T := hTfin.toFinset with hT
  have hmemT : ∀ w, w ∈ T ↔ w.under (𝓞 K) ∈ S := fun w => by simp [hT]
  have hgood : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) ∉ S →
      (∀ f : ℕ, normV w = normV (w.under (𝓞 K)) ^ f → η.val (w.under (𝓞 K)) ^ f = 1) ∧ η.UnrAt (w.under (𝓞 K)) ∧
      (normV w = normV (w.under (𝓞 K)) ∨ IsPrimitiveRoot (η.val (w.under (𝓞 K))) (Module.finrank K M)) := by
    intro w hw
    by_contra h
    exact hw (Finset.mem_union_right _ (Finset.mem_image_of_mem _
      (Finset.mem_union_right _ (hNG.mem_toFinset.2 h))))
  have hdec : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      (Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v} = Module.finrank K M ∧
        ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v → normV w = normV v) ∨
      (Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v} = 1 ∧
        ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v → normV w = normV v ^ Module.finrank K M) := by
    intro v hv
    by_contra h
    exact hv (Finset.mem_union_left _ (Finset.mem_union_right _ (hD'.mem_toFinset.2 h)))
  have hex : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∃ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v := by
    intro v hv
    have : Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v} ≠ 0 := by
      rcases hdec v hv with h | h
      · rw [h.1]; exact hl.ne_zero
      · rw [h.1]; exact one_ne_zero
    obtain ⟨⟨w, hw⟩⟩ := (Nat.card_ne_zero.1 this).1
    exact ⟨w, hw⟩
  have hne : ∀ v : HeightOneSpectrum (𝓞 K), normV v ^ Module.finrank K M ≠ normV v := by
    intro v
    have := Nat.pow_lt_pow_right (one_lt_normV v) hl.one_lt
    rw [pow_one] at this
    exact this.ne'
  let u : Off M T → Off K S := fun w => ⟨w.1.under (𝓞 K), fun h => w.2 ((hmemT _).2 h)⟩
  let f : Off M T → ℕ := fun w => if normV w.1 = normV (w.1.under (𝓞 K)) then 1 else Module.finrank K M
  have hnorm : ∀ w, normV w.1 = normV (u w).1 ^ f w := by
    intro w
    by_cases h : normV w.1 = normV (w.1.under (𝓞 K))
    · simp only [f, if_pos h, pow_one]; exact h
    · simp only [f, if_neg h]
      rcases hdec _ (u w).2 with h' | h'
      · exact absurd (h'.2 _ rfl) h
      · exact h'.2 _ rfl
  have hcard : ∀ v : Off K S, Nat.card {w // u w = v} =
      Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v.1} := by
    intro v
    exact Nat.card_congr
      { toFun := fun w => ⟨w.1.1, congrArg Subtype.val w.2⟩
        invFun := fun w => ⟨⟨w.1, fun h => v.2 (w.2 ▸ (hmemT _).1 h)⟩, Subtype.ext w.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  refine ⟨S, T, u, f, fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ hv), fun w hw => (hmemT w).2
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_union_left _ hw))), fun _ => rfl, ?_, hnorm, ?_, ?_⟩
  · intro v
    obtain ⟨w, hw⟩ := hex v.1 v.2
    exact hw ▸ (hgood w (hw ▸ v.2)).2.1
  · intro w
    simpa only [nq, normV_eq] using hnorm w
  · intro v
    obtain ⟨w₀, hw₀⟩ := hex v.1 v.2
    have hg := hgood w₀ (hw₀ ▸ v.2)
    rw [hw₀] at hg
    rcases hdec v.1 v.2 with h | h
    · refine Or.inl ⟨(hcard v).trans h.1, fun w hw => ?_, ?_⟩
      · have hw' : w.1.under (𝓞 K) = v.1 := congrArg Subtype.val hw
        exact if_pos (hw' ▸ h.2 _ hw')
      · have := hg.1 1 (by rw [pow_one]; exact h.2 _ hw₀)
        rw [pow_one] at this
        simp [this]
    · refine Or.inr ⟨(hcard v).trans h.1, fun w hw => ?_, ?_⟩
      · have hw' : w.1.under (𝓞 K) = v.1 := congrArg Subtype.val hw
        refine if_neg ?_
        rw [h.2 _ hw', hw']
        exact hne _
      · rcases hg.2.2 with h' | h'
        · exact absurd ((h.2 _ hw₀).symm.trans h') (hne _)
        · exact IsPrimitiveRoot.coe_units_iff.2 h'
