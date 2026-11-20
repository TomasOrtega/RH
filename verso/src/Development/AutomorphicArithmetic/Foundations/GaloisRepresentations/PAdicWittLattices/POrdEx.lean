import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace UpperTheory.Gal.G3

/- English proof (translation)
Use `haveI := hcf`. Use `haveI := hce`. Set `P` to `pullback s c`. Establish `hsq : ∀ j, σ j ≫ s = 𝟙 W ≫ c` using `fun j => by rw [hσ j, Category.id_comp]`. Set `sec : Fin d → (W ⟶ P)` to `fun j => pullback.lift (σ j) (𝟙 W) (hsq j)`.

Establish `hsec1 : ∀ j, sec j ≫ pullback.fst s c = σ j` using `fun j => pullback.lift_fst _ _ _`. Establish `hsec2 : ∀ j, sec j ≫ pullback.snd s c = 𝟙 W` using `fun j => pullback.lift_snd _ _ _`. Use `haveI hOP : MorphismProperty.HasOfPostcompProperty (@IsOpenImmersion : MorphismProperty Scheme) (@Etale : MorphismProperty Scheme) := by`. Apply `MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.2` to reduce the goal to its premises. Introduce `X Y f hf`.

Use `haveI : Etale f := hf`. Conclude with `inferInstanceAs <| IsOpenImmersion (pullback.diagonal f)`. Establish `hopen : ∀ j, IsOpenImmersion (sec j)` using `fun j => MorphismProperty.of_postcomp (W := (@IsOpenImmersion : MorphismProperty Scheme)) (W' := (@Etale : MorphismProperty Scheme)) (sec j) (pullback.snd s c) (inferInstanceAs (Etale (pullback.snd s c))) (by rw [hsec2]; exact inferInstanceAs (IsOpenImmersion (𝟙 W)))`. Establish `hclosed : ∀ j, IsClosedImmersion (sec j)` using `fun j => by haveI : IsClosedImmersion (sec j ≫ pullback.snd s c) := by`. Rewrite using `[hsec2]`.

Use `infer_instance`. Conclude with `IsClosedImmersion.of_comp (sec j) (pullback.snd s c)`. Set `S : Set P` to `⋃ j, Set.range (sec j).base`. Establish `hSc : IsClosed S` using `isClosed_iUnion_of_finite fun j => (hclosed j).isClosedEmbedding.isClosed_range`. Establish `hSo : IsOpen S` using `isOpen_iUnion fun j => (hopen j).base_open.isOpen_range`.

Set `O : P.Opens` to `⟨Sᶜ, hSc.isOpen_compl⟩`. Establish `hOr : Set.range O.ι.base = Sᶜ` using `O.range_ι`. Use `haveI : IsClosedImmersion O.ι := .of_isPreimmersion _ (by rw [hOr]; exact hSo.isClosed_compl)`. Establish `hpt : ∀ (j : Fin d) (Ω : Type) [Field Ω] (x : sp Ω ⟶ P), x.base (IsLocalRing.closedPoint Ω) ∈ Set.range (sec j).base → x ≫ pullback.fst s c = x ≫ pullback.snd s c ≫ σ j`. Introduce `j Ω _ x hx`.

Establish `hr : Set.range x.base ⊆ Set.range (sec j).base`. Introduce and unpack `_ ⟨p, rfl⟩`. Rewrite using `[Subsingleton.elim p (IsLocalRing.closedPoint Ω)]` and apply the resulting hypothesis. Use `haveI := hopen j`. Establish `hf` using `IsOpenImmersion.lift_fac (sec j) x hr`.

Rewrite using `[← hf, Category.assoc, Category.assoc, hsec1, reassoc_of% hsec2]`. Establish `hback : ∀ (j : Fin d) {T : Scheme.{0}} (x : T ⟶ P), x ≫ pullback.fst s c = x ≫ pullback.snd s c ≫ σ j → x = (x ≫ pullback.snd s c) ≫ sec j`. Introduce `j T x hx`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hsec1, hx, Category.assoc]`.

Rewrite using `[Category.assoc, hsec2, Category.comp_id]`. Use `⟨O, O.ι ≫ pullback.snd s c ≫ c, Fin.snoc (α := fun _ => ((O : Scheme) ⟶ Y)) (fun j => O.ι ≫ pullback.snd s c ≫ σ j) (O.ι ≫ pullback.fst s c), inferInstance, inferInstance, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k`. Use `Fin.lastCases ?_ (fun j => ?_) k` and prove the remaining obligations. Simplify using `only [Fin.snoc_last, Category.assoc, pullback.condition]`.

Simplify using `only [Fin.snoc_castSucc, Category.assoc, hσ j]`. Introduce `Ω _ x`. Establish `key : ∀ j : Fin d, x ≫ O.ι ≫ pullback.fst s c ≠ x ≫ O.ι ≫ pullback.snd s c ≫ σ j`. Introduce `j h`. Establish `h2` using `hback j (x ≫ O.ι) (by simpa only [Category.assoc] using h)`.

Establish `hin : (x ≫ O.ι).base (IsLocalRing.closedPoint Ω) ∈ S`. Rewrite using `[h2]`. Conclude with `Set.mem_iUnion.2 ⟨j, _, rfl⟩`. Establish `hO : (x ≫ O.ι).base (IsLocalRing.closedPoint Ω) ∈ Set.range O.ι.base` using `⟨x.base (IsLocalRing.closedPoint Ω), rfl⟩`. Rewrite `hO` using `[hOr]`.

Conclude with `hO hin`. Introduce `a b hab`. Simplify using `only at hab`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last`.

Proceed by induction on `b using Fin.lastCases with`. Consider the case `last => rfl`. Consider the case `cast j`. Simplify using `only [Fin.snoc_last, Fin.snoc_castSucc] at hab`. Conclude with `absurd hab (key j)`.

Consider the case `cast i`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last`. Simplify using `only [Fin.snoc_last, Fin.snoc_castSucc] at hab`. Conclude with `absurd hab.symm (key i)`.

Consider the case `cast j`. Simplify using `only [Fin.snoc_castSucc] at hab`. Conclude with `congrArg Fin.castSucc (hinj Ω (x ≫ O.ι ≫ pullback.snd s c) (by simpa only [Category.assoc] using hab))`. Introduce `U z y hy hinjU`. Take `⟨w0, ⟨hw0c, hw0σ⟩, hw0u⟩` from `huniv U z (fun j => y j.castSucc) (fun j => hy _) (fun Ω _ x a b h => Fin.castSucc_injective _ (hinjU Ω x h))`.

Set `φ : U ⟶ P` to `pullback.lift (y (Fin.last d)) w0 (by rw [hy, hw0c])`. Establish `hφ1 : φ ≫ pullback.fst s c = y (Fin.last d)` using `pullback.lift_fst _ _ _`. Establish `hφ2 : φ ≫ pullback.snd s c = w0` using `pullback.lift_snd _ _ _`. Establish `hrange : Set.range φ.base ⊆ Set.range O.ι.base`. Introduce and unpack `_ ⟨u, rfl⟩`.

Rewrite using `[hOr]`. Introduce `hu`. Take `⟨j, hj⟩` from `Set.mem_iUnion.1 hu`. Set `x` to `U.fromSpecResidueField u`. Establish `hxu : x.base (IsLocalRing.closedPoint (U.residueField u)) = u` using `U.fromSpecResidueField_apply u _`.

Use `hpt j (U.residueField u) (x ≫ φ) (by show φ.base (x.base _) ∈ _` as an intermediate fact. Rewrite using `[hxu]`. Conclude with `hj)`. Rewrite `this` using `[Category.assoc, Category.assoc, hφ1, reassoc_of% hφ2, hw0σ]`. Conclude with `(Fin.castSucc_lt_last j).ne (hinjU _ x this).symm`.

Use `⟨IsOpenImmersion.lift O.ι φ hrange, ⟨?_, fun k => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[IsOpenImmersion.lift_fac_assoc, reassoc_of% hφ2, hw0c]`. Use `Fin.lastCases ?_ (fun j => ?_) k` and prove the remaining obligations. Rewrite using `[Fin.snoc_last, IsOpenImmersion.lift_fac_assoc, hφ1]`. Rewrite using `[Fin.snoc_castSucc, IsOpenImmersion.lift_fac_assoc, reassoc_of% hφ2, hw0σ]`.

Introduce and unpack `w' ⟨hw'c, hw'σ⟩`. Rewrite using `[← cancel_mono O.ι, IsOpenImmersion.lift_fac]`. Establish `e2 : w' ≫ O.ι ≫ pullback.snd s c = w0`. Use `hw0u _ ⟨by simpa only [Category.assoc] using hw'c, fun j => ?_⟩` and prove the remaining obligations. Use `hw'σ j.castSucc` as an intermediate fact.

Rewrite `this` using `[Fin.snoc_castSucc]`. Simplify `this` using `only [Category.assoc]`. Apply `pullback.hom_ext` to reduce the goal to its premises. Use `hw'σ (Fin.last d)` as an intermediate fact. Rewrite `this` using `[Fin.snoc_last]`.

Rewrite using `[Category.assoc, this, hφ1]`. Rewrite using `[Category.assoc, e2, hφ2]`.
-/
private theorem ordExStep (hS : OrdStep) {Z Y W : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] [Etale s] (d : ℕ)
    (c : W ⟶ Z) (σ : Fin d → (W ⟶ Y)) (hcf : IsFinite c) (hce : Etale c) (hσ : ∀ j, σ j ≫ s = c)
    (hinj : ∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ W), Function.Injective fun j => x ≫ σ j)
    (huniv : ∀ (U : Scheme.{0}) (z : U ⟶ Z) (y : Fin d → (U ⟶ Y)), (∀ j, y j ≫ s = z) →
      (∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ U), Function.Injective fun j => x ≫ y j) →
      ∃! w : U ⟶ W, w ≫ c = z ∧ ∀ j, w ≫ σ j = y j) :
    ∃ (W' : Scheme.{0}) (c' : W' ⟶ Z) (σ' : Fin (d + 1) → (W' ⟶ Y)), IsFinite c' ∧ Etale c' ∧
      (∀ j, σ' j ≫ s = c') ∧
      (∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ W'), Function.Injective fun j => x ≫ σ' j) ∧
      ∀ (U : Scheme.{0}) (z : U ⟶ Z) (y : Fin (d + 1) → (U ⟶ Y)), (∀ j, y j ≫ s = z) →
        (∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ U), Function.Injective fun j => x ≫ y j) →
        ∃! w : U ⟶ W', w ≫ c' = z ∧ ∀ j, w ≫ σ' j = y j := by
  haveI := hcf
  haveI := hce
  let P := pullback s c
  have hsq : ∀ j, σ j ≫ s = 𝟙 W ≫ c := fun j => by rw [hσ j, Category.id_comp]
  let sec : Fin d → (W ⟶ P) := fun j => pullback.lift (σ j) (𝟙 W) (hsq j)
  have hsec1 : ∀ j, sec j ≫ pullback.fst s c = σ j := fun j => pullback.lift_fst _ _ _
  have hsec2 : ∀ j, sec j ≫ pullback.snd s c = 𝟙 W := fun j => pullback.lift_snd _ _ _
  haveI hOP : MorphismProperty.HasOfPostcompProperty (@IsOpenImmersion : MorphismProperty Scheme)
      (@Etale : MorphismProperty Scheme) := by
    apply MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.2
    intro X Y f hf
    haveI : Etale f := hf
    exact inferInstanceAs <| IsOpenImmersion (pullback.diagonal f)
  have hopen : ∀ j, IsOpenImmersion (sec j) := fun j =>
    MorphismProperty.of_postcomp (W := (@IsOpenImmersion : MorphismProperty Scheme))
      (W' := (@Etale : MorphismProperty Scheme)) (sec j) (pullback.snd s c)
      (inferInstanceAs (Etale (pullback.snd s c)))
      (by rw [hsec2]; exact inferInstanceAs (IsOpenImmersion (𝟙 W)))
  have hclosed : ∀ j, IsClosedImmersion (sec j) := fun j => by
    haveI : IsClosedImmersion (sec j ≫ pullback.snd s c) := by
      rw [hsec2]; infer_instance
    exact IsClosedImmersion.of_comp (sec j) (pullback.snd s c)
  let S : Set P := ⋃ j, Set.range (sec j).base
  have hSc : IsClosed S := isClosed_iUnion_of_finite fun j => (hclosed j).isClosedEmbedding.isClosed_range
  have hSo : IsOpen S := isOpen_iUnion fun j => (hopen j).base_open.isOpen_range
  let O : P.Opens := ⟨Sᶜ, hSc.isOpen_compl⟩
  have hOr : Set.range O.ι.base = Sᶜ := O.range_ι
  haveI : IsClosedImmersion O.ι := .of_isPreimmersion _ (by rw [hOr]; exact hSo.isClosed_compl)
  have hpt : ∀ (j : Fin d) (Ω : Type) [Field Ω] (x : sp Ω ⟶ P),
      x.base (IsLocalRing.closedPoint Ω) ∈ Set.range (sec j).base →
      x ≫ pullback.fst s c = x ≫ pullback.snd s c ≫ σ j := by
    intro j Ω _ x hx
    have hr : Set.range x.base ⊆ Set.range (sec j).base := by
      rintro _ ⟨p, rfl⟩
      rwa [Subsingleton.elim p (IsLocalRing.closedPoint Ω)]
    haveI := hopen j
    have hf := IsOpenImmersion.lift_fac (sec j) x hr
    rw [← hf, Category.assoc, Category.assoc, hsec1, reassoc_of% hsec2]
  have hback : ∀ (j : Fin d) {T : Scheme.{0}} (x : T ⟶ P),
      x ≫ pullback.fst s c = x ≫ pullback.snd s c ≫ σ j → x = (x ≫ pullback.snd s c) ≫ sec j := by
    intro j T x hx
    apply pullback.hom_ext
    · rw [Category.assoc, hsec1, hx, Category.assoc]
    · rw [Category.assoc, hsec2, Category.comp_id]
  refine ⟨O, O.ι ≫ pullback.snd s c ≫ c,
    Fin.snoc (α := fun _ => ((O : Scheme) ⟶ Y)) (fun j => O.ι ≫ pullback.snd s c ≫ σ j)
      (O.ι ≫ pullback.fst s c), inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simp only [Fin.snoc_last, Category.assoc, pullback.condition]
    · simp only [Fin.snoc_castSucc, Category.assoc, hσ j]
  · intro Ω _ x
    have key : ∀ j : Fin d, x ≫ O.ι ≫ pullback.fst s c ≠ x ≫ O.ι ≫ pullback.snd s c ≫ σ j := by
      intro j h
      have h2 := hback j (x ≫ O.ι) (by simpa only [Category.assoc] using h)
      have hin : (x ≫ O.ι).base (IsLocalRing.closedPoint Ω) ∈ S := by
        rw [h2]
        exact Set.mem_iUnion.2 ⟨j, _, rfl⟩
      have hO : (x ≫ O.ι).base (IsLocalRing.closedPoint Ω) ∈ Set.range O.ι.base :=
        ⟨x.base (IsLocalRing.closedPoint Ω), rfl⟩
      rw [hOr] at hO
      exact hO hin
    intro a b hab
    simp only at hab
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => rfl
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
        exact absurd hab (key j)
    | cast i =>
      induction b using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
        exact absurd hab.symm (key i)
      | cast j =>
        simp only [Fin.snoc_castSucc] at hab
        exact congrArg Fin.castSucc (hinj Ω (x ≫ O.ι ≫ pullback.snd s c) (by simpa only [Category.assoc] using hab))
  · intro U z y hy hinjU
    obtain ⟨w0, ⟨hw0c, hw0σ⟩, hw0u⟩ := huniv U z (fun j => y j.castSucc) (fun j => hy _)
      (fun Ω _ x a b h => Fin.castSucc_injective _ (hinjU Ω x h))
    let φ : U ⟶ P := pullback.lift (y (Fin.last d)) w0 (by rw [hy, hw0c])
    have hφ1 : φ ≫ pullback.fst s c = y (Fin.last d) := pullback.lift_fst _ _ _
    have hφ2 : φ ≫ pullback.snd s c = w0 := pullback.lift_snd _ _ _
    have hrange : Set.range φ.base ⊆ Set.range O.ι.base := by
      rintro _ ⟨u, rfl⟩
      rw [hOr]
      intro hu
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hu
      let x := U.fromSpecResidueField u
      have hxu : x.base (IsLocalRing.closedPoint (U.residueField u)) = u :=
        U.fromSpecResidueField_apply u _
      have := hpt j (U.residueField u) (x ≫ φ) (by
        show φ.base (x.base _) ∈ _
        rw [hxu]
        exact hj)
      rw [Category.assoc, Category.assoc, hφ1, reassoc_of% hφ2, hw0σ] at this
      exact (Fin.castSucc_lt_last j).ne (hinjU _ x this).symm
    refine ⟨IsOpenImmersion.lift O.ι φ hrange, ⟨?_, fun k => ?_⟩, ?_⟩
    · rw [IsOpenImmersion.lift_fac_assoc, reassoc_of% hφ2, hw0c]
    · refine Fin.lastCases ?_ (fun j => ?_) k
      · rw [Fin.snoc_last, IsOpenImmersion.lift_fac_assoc, hφ1]
      · rw [Fin.snoc_castSucc, IsOpenImmersion.lift_fac_assoc, reassoc_of% hφ2, hw0σ]
    · rintro w' ⟨hw'c, hw'σ⟩
      rw [← cancel_mono O.ι, IsOpenImmersion.lift_fac]
      have e2 : w' ≫ O.ι ≫ pullback.snd s c = w0 := by
        refine hw0u _ ⟨by simpa only [Category.assoc] using hw'c, fun j => ?_⟩
        have := hw'σ j.castSucc
        rw [Fin.snoc_castSucc] at this
        simpa only [Category.assoc] using this
      apply pullback.hom_ext
      · have := hw'σ (Fin.last d)
        rw [Fin.snoc_last] at this
        rw [Category.assoc, this, hφ1]
      · rw [Category.assoc, e2, hφ2]

/- English proof (translation)
Introduce `hS Z Y s _ _ d`. Proceed by induction on `d with`. Consider the case `zero`. Use `⟨Z, 𝟙 Z, Fin.elim0, inferInstance, inferInstance, fun j => j.elim0, ?_, ?_⟩` and prove the remaining obligations. Introduce `Ω _ x a`.

Conclude with `a.elim0`. Introduce `U z y _ _`. Conclude with `⟨z, ⟨Category.comp_id _, fun j => j.elim0⟩, fun w hw => by simpa using hw.1⟩`. Consider the case `succ d ih`. Take `⟨W, c, σ, hcf, hce, hσ, hinj, huniv⟩` from `ih`.

Conclude with `ordExStep hS s d c σ hcf hce hσ hinj huniv`.
-/
theorem pOrdEx : OrdStep → OrdEx := by
  intro hS Z Y s _ _ d
  induction d with
  | zero =>
    refine ⟨Z, 𝟙 Z, Fin.elim0, inferInstance, inferInstance, fun j => j.elim0, ?_, ?_⟩
    · intro Ω _ x a
      exact a.elim0
    · intro U z y _ _
      exact ⟨z, ⟨Category.comp_id _, fun j => j.elim0⟩, fun w hw => by simpa using hw.1⟩
  | succ d ih =>
    obtain ⟨W, c, σ, hcf, hce, hσ, hinj, huniv⟩ := ih
    exact ordExStep hS s d c σ hcf hce hσ hinj huniv

end UpperTheory.Gal.G3

end
