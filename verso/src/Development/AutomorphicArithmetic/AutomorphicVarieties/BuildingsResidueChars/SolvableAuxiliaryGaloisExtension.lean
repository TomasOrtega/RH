import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

/- English proof (translation)
Introduce `M Ω _ _ _ _ _ L _ _ _ hp hlt`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed M`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap M Ω).injective`. Take `⟨α, hα⟩` from `Field.exists_primitive_element ℚ L`. Establish `hαi : IsIntegral ℚ α` using `Algebra.IsIntegral.isIntegral α`.

Use `set P := minpoly ℚ α with hPdef`. Establish `hPdeg : P.natDegree = Module.finrank ℚ L`. Rewrite using `[← IntermediateField.adjoin.finrank hαi, hα, IntermediateField.finrank_top']`. Set `φ : L →ₐ[ℚ] Ω` to `IsAlgClosed.lift`. Use `set β := φ α with hβdef`.

Establish `hβP : minpoly ℚ β = P` using `minpoly.algHom_eq φ φ.injective α`. Use `set Q : Polynomial M := P.map (algebraMap ℚ M) with hQdef`. Establish `hQ0 : Q ≠ 0` using `Polynomial.map_ne_zero (minpoly.ne_zero hαi)`. Establish `hsplit : (Q.map (algebraMap M Ω)).Splits` using `IsAlgClosed.splits _`. Establish `hSF` using `IntermediateField.adjoin_rootSet_isSplittingField hsplit`.

Establish `hsep : Q.Separable` using `Polynomial.Separable.map (Algebra.IsSeparable.isSeparable ℚ α)`. Establish `hroot : ∀ y : Ω, y ∈ Q.rootSet Ω ↔ y ∈ P.rootSet Ω`. Introduce `y`. Rewrite using `[Polynomial.mem_rootSet, Polynomial.mem_rootSet, hQdef, Polynomial.aeval_map_algebraMap]`. Conclude with `and_congr_left fun _ => ⟨fun _ => minpoly.ne_zero hαi, fun _ => hQ0⟩`.

Establish `hβroot : β ∈ P.rootSet Ω`. Rewrite using `[Polynomial.mem_rootSet]`. Conclude with `⟨minpoly.ne_zero hαi, hβP ▸ minpoly.aeval ℚ β⟩`. Establish `hrange : ∀ x : L, φ x ∈ IntermediateField.adjoin M {β}`. Introduce `x`.

Establish `h1 : φ x ∈ (⊤ : IntermediateField ℚ L).map φ` using `⟨x, trivial, rfl⟩`. Rewrite `h1` using `[← hα, IntermediateField.adjoin_map, Set.image_singleton]`. Establish `h2 : IntermediateField.adjoin ℚ {φ α} ≤ (IntermediateField.adjoin M {β}).restrictScalars ℚ` using `IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.mem_adjoin_simple_self M β)`. Conclude with `h2 h1`. Establish `hPs : (P.map (algebraMap ℚ L)).Splits` using `Normal.splits inferInstance α`.

Establish `hroots : ∀ y ∈ P.rootSet Ω, y ∈ Set.range φ`. Introduce `y hy`. Rewrite `hy` using `[← hPs.image_rootSet φ]`. Take `⟨x, -, rfl⟩` from `hy`. Conclude with `⟨x, rfl⟩`.

Establish `heq : IntermediateField.adjoin M (Q.rootSet Ω) = IntermediateField.adjoin M {β}`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce `y hy`. Take `⟨x, rfl⟩` from `hroots y ((hroot y).1 hy)`.

Conclude with `hrange x`. Rewrite using `[IntermediateField.adjoin_simple_le_iff]`. Conclude with `IntermediateField.subset_adjoin M _ ((hroot β).2 hβroot)`. Establish `hgal0 : IsGalois M (IntermediateField.adjoin M (Q.rootSet Ω))` using `by haveI := hSF`. Conclude with `IsGalois.of_separable_splitting_field hsep`.

Establish `hgal : IsGalois M (IntermediateField.adjoin M {β})` using `heq ▸ hgal0`. Establish `hβQ : IsIntegral ℚ β` using `hαi.map φ`. Establish `hβM : IsIntegral M β` using `hβQ.tower_top`. Use `haveI hfdM : FiniteDimensional M (IntermediateField.adjoin M {β}) := IntermediateField.adjoin.finiteDimensional hβM`. Use `haveI hfdQ : FiniteDimensional ℚ (IntermediateField.adjoin M {β}) := Module.Finite.trans M (IntermediateField.adjoin M {β})`.

Use `haveI hnf : NumberField (IntermediateField.adjoin M {β}) := {}`. Set `f : L →+* IntermediateField.adjoin M {β}` to `(φ : L →+* Ω).codRestrict _ hrange`. Establish `hfin : Module.finrank M (IntermediateField.adjoin M {β}) = (minpoly M β).natDegree` using `IntermediateField.adjoin.finrank hβM`. Establish `hle : (minpoly M β).natDegree ≤ Module.finrank ℚ L`. Rewrite using `[← hPdeg, ← Polynomial.natDegree_map (algebraMap ℚ M) (p := P)]`.

Use `Polynomial.natDegree_le_of_dvd ?_ hQ0` and prove the remaining obligations. Establish `h4` using `minpoly.dvd_map_of_isScalarTower ℚ M β`. Rewrite `h4` using `[hβP]`. Then use the resulting hypothesis. Establish `hx : minpoly ℚ (⟨β, IntermediateField.mem_adjoin_simple_self M β⟩ : IntermediateField.adjoin M {β}) = P`. Rewrite using `[← minpoly.algHom_eq (IsScalarTower.toAlgHom ℚ (IntermediateField.adjoin M {β}) Ω) (algebraMap (IntermediateField.adjoin M {β}) Ω).injective]`.

Conclude with `hβP`. Establish `hdvd : Module.finrank ℚ L ∣ Module.finrank ℚ (IntermediateField.adjoin M {β})`. Establish `h5` using `minpoly.degree_dvd (Algebra.IsIntegral.isIntegral (R := ℚ) (⟨β, IntermediateField.mem_adjoin_simple_self M β⟩ : IntermediateField.adjoin M {β}))`. Rewrite `h5` using `[hx, hPdeg]`. Then use the resulting hypothesis. Establish `hMpos : 0 < Module.finrank ℚ M` using `Module.finrank_pos`.

Establish `hEpos : 0 < Module.finrank M (IntermediateField.adjoin M {β})` using `Module.finrank_pos`. Establish `hdeg : Module.finrank M (IntermediateField.adjoin M {β}) = Module.finrank ℚ L`. Rewrite `hdvd` using `[← Module.finrank_mul_finrank ℚ M (IntermediateField.adjoin M {β})]`. Break down `(Nat.Prime.dvd_mul hp).mp hdvd with h3 | h3` into its components or cases. Conclude with `absurd h3 (Nat.not_dvd_of_pos_of_lt hMpos hlt)`.

Conclude with `le_antisymm (hfin ▸ hle) (Nat.le_of_dvd hEpos h3)`. Establish `htop : Algebra.adjoin M (Set.range f) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce and unpack `z -`. Establish `hz : (z : Ω) ∈ Algebra.adjoin M {β}`.

Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hβM.isAlgebraic]`. Conclude with `z.2`. Establish `hsub : Algebra.adjoin M {β} ≤ (Algebra.adjoin M (Set.range f)).map (IntermediateField.adjoin M {β}).val`. Rewrite using `[AlgHom.map_adjoin]`. Apply `Algebra.adjoin_mono` to reduce the goal to its premises.

Introduce and unpack `_ rfl`. Conclude with `⟨f α, ⟨α, rfl⟩, rfl⟩`. Take `⟨w, hw, hwz⟩` from `hsub hz`. Establish `hwz' : w = z` using `Subtype.ext hwz`. Conclude with `hwz' ▸ hw`.

Conclude with `⟨IntermediateField.adjoin M {β}, inferInstance, hnf, inferInstance, inferInstance, inferInstance, f, hgal, hdeg, htop⟩`.
-/
theorem UpperTheory.solvable_auxiliary_galois_extension :
    UpperTheory.V.Af.Sol.ExistsCompositumWithPrimeDegreeGalois := by
  intro M Ω _ _ _ _ _ L _ _ _ hp hlt
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed M
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap M Ω).injective
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ L
  have hαi : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  set P := minpoly ℚ α with hPdef
  have hPdeg : P.natDegree = Module.finrank ℚ L := by
    rw [← IntermediateField.adjoin.finrank hαi, hα, IntermediateField.finrank_top']
  let φ : L →ₐ[ℚ] Ω := IsAlgClosed.lift
  set β := φ α with hβdef
  have hβP : minpoly ℚ β = P := minpoly.algHom_eq φ φ.injective α
  set Q : Polynomial M := P.map (algebraMap ℚ M) with hQdef
  have hQ0 : Q ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero hαi)
  have hsplit : (Q.map (algebraMap M Ω)).Splits := IsAlgClosed.splits _
  have hSF := IntermediateField.adjoin_rootSet_isSplittingField hsplit
  have hsep : Q.Separable := Polynomial.Separable.map (Algebra.IsSeparable.isSeparable ℚ α)
  have hroot : ∀ y : Ω, y ∈ Q.rootSet Ω ↔ y ∈ P.rootSet Ω := by
    intro y
    rw [Polynomial.mem_rootSet, Polynomial.mem_rootSet, hQdef, Polynomial.aeval_map_algebraMap]
    exact and_congr_left fun _ => ⟨fun _ => minpoly.ne_zero hαi, fun _ => hQ0⟩
  have hβroot : β ∈ P.rootSet Ω := by
    rw [Polynomial.mem_rootSet]
    exact ⟨minpoly.ne_zero hαi, hβP ▸ minpoly.aeval ℚ β⟩
  have hrange : ∀ x : L, φ x ∈ IntermediateField.adjoin M {β} := by
    intro x
    have h1 : φ x ∈ (⊤ : IntermediateField ℚ L).map φ := ⟨x, trivial, rfl⟩
    rw [← hα, IntermediateField.adjoin_map, Set.image_singleton] at h1
    have h2 : IntermediateField.adjoin ℚ {φ α} ≤ (IntermediateField.adjoin M {β}).restrictScalars ℚ :=
      IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.mem_adjoin_simple_self M β)
    exact h2 h1
  have hPs : (P.map (algebraMap ℚ L)).Splits := Normal.splits inferInstance α
  have hroots : ∀ y ∈ P.rootSet Ω, y ∈ Set.range φ := by
    intro y hy
    rw [← hPs.image_rootSet φ] at hy
    obtain ⟨x, -, rfl⟩ := hy
    exact ⟨x, rfl⟩
  have heq : IntermediateField.adjoin M (Q.rootSet Ω) = IntermediateField.adjoin M {β} := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro y hy
      obtain ⟨x, rfl⟩ := hroots y ((hroot y).1 hy)
      exact hrange x
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.subset_adjoin M _ ((hroot β).2 hβroot)
  have hgal0 : IsGalois M (IntermediateField.adjoin M (Q.rootSet Ω)) := by
    haveI := hSF
    exact IsGalois.of_separable_splitting_field hsep
  have hgal : IsGalois M (IntermediateField.adjoin M {β}) := heq ▸ hgal0
  have hβQ : IsIntegral ℚ β := hαi.map φ
  have hβM : IsIntegral M β := hβQ.tower_top
  haveI hfdM : FiniteDimensional M (IntermediateField.adjoin M {β}) :=
    IntermediateField.adjoin.finiteDimensional hβM
  haveI hfdQ : FiniteDimensional ℚ (IntermediateField.adjoin M {β}) :=
    Module.Finite.trans M (IntermediateField.adjoin M {β})
  haveI hnf : NumberField (IntermediateField.adjoin M {β}) := {}
  let f : L →+* IntermediateField.adjoin M {β} := (φ : L →+* Ω).codRestrict _ hrange
  have hfin : Module.finrank M (IntermediateField.adjoin M {β}) = (minpoly M β).natDegree :=
    IntermediateField.adjoin.finrank hβM
  have hle : (minpoly M β).natDegree ≤ Module.finrank ℚ L := by
    rw [← hPdeg, ← Polynomial.natDegree_map (algebraMap ℚ M) (p := P)]
    refine Polynomial.natDegree_le_of_dvd ?_ hQ0
    have h4 := minpoly.dvd_map_of_isScalarTower ℚ M β
    rwa [hβP] at h4
  have hx : minpoly ℚ (⟨β, IntermediateField.mem_adjoin_simple_self M β⟩ : IntermediateField.adjoin M {β}) = P := by
    rw [← minpoly.algHom_eq (IsScalarTower.toAlgHom ℚ (IntermediateField.adjoin M {β}) Ω)
      (algebraMap (IntermediateField.adjoin M {β}) Ω).injective]
    exact hβP
  have hdvd : Module.finrank ℚ L ∣ Module.finrank ℚ (IntermediateField.adjoin M {β}) := by
    have h5 := minpoly.degree_dvd (Algebra.IsIntegral.isIntegral (R := ℚ)
      (⟨β, IntermediateField.mem_adjoin_simple_self M β⟩ : IntermediateField.adjoin M {β}))
    rwa [hx, hPdeg] at h5
  have hMpos : 0 < Module.finrank ℚ M := Module.finrank_pos
  have hEpos : 0 < Module.finrank M (IntermediateField.adjoin M {β}) := Module.finrank_pos
  have hdeg : Module.finrank M (IntermediateField.adjoin M {β}) = Module.finrank ℚ L := by
    rw [← Module.finrank_mul_finrank ℚ M (IntermediateField.adjoin M {β})] at hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h3 | h3
    · exact absurd h3 (Nat.not_dvd_of_pos_of_lt hMpos hlt)
    · exact le_antisymm (hfin ▸ hle) (Nat.le_of_dvd hEpos h3)
  have htop : Algebra.adjoin M (Set.range f) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    have hz : (z : Ω) ∈ Algebra.adjoin M {β} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hβM.isAlgebraic]
      exact z.2
    have hsub : Algebra.adjoin M {β} ≤
        (Algebra.adjoin M (Set.range f)).map (IntermediateField.adjoin M {β}).val := by
      rw [AlgHom.map_adjoin]
      apply Algebra.adjoin_mono
      rintro _ rfl
      exact ⟨f α, ⟨α, rfl⟩, rfl⟩
    obtain ⟨w, hw, hwz⟩ := hsub hz
    have hwz' : w = z := Subtype.ext hwz
    exact hwz' ▸ hw
  exact ⟨IntermediateField.adjoin M {β}, inferInstance, hnf, inferInstance, inferInstance,
    inferInstance, f, hgal, hdeg, htop⟩
