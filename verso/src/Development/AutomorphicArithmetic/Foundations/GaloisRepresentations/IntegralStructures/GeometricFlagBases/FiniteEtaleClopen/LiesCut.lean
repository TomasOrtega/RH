import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.ClopenExtAlt

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Cut

/- English proof (translation)
Set `K` to `AlgebraicClosure (X.residueField x)`. Set `b : Spec (CommRingCat.of K) ⟶ Spec (X.residueField x)` to `Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K))`. Set `a : Spec (CommRingCat.of K) ⟶ X` to `b ≫ X.fromSpecResidueField x`. Establish `hc` using `hf.2.2 K a`. Establish `hne : Nonempty {y : Spec (CommRingCat.of K) ⟶ Y // y ≫ f = a}`.

Assume the negation of the conclusion as `hem`. Rewrite `hem` using `[not_nonempty_iff]`. Rewrite `hc` using `[Nat.card_of_isEmpty]`. Use linear arithmetic over natural numbers and integers. Take `⟨⟨y, hy⟩⟩` from `hne`.

Take `⟨pt⟩ : Nonempty (Spec (CommRingCat.of K))` from `inferInstance`. Use `⟨y pt, ?_⟩` and prove the remaining obligations. Establish `h1 : a pt ∈ Set.range (X.fromSpecResidueField x)` using `⟨b pt, by simp [a]⟩`. Rewrite `h1` using `[X.range_fromSpecResidueField]`. Rewrite using `[← Scheme.Hom.comp_apply, hy]`.

Conclude with `h1`.
-/
private theorem fEt_surj {Y X : Scheme.{0}} {f : Y ⟶ X} {d : ℕ} (hf : FEt f d) (hd : 0 < d) (x : X) :
    ∃ y : Y, f y = x := by
  let K := AlgebraicClosure (X.residueField x)
  let b : Spec (CommRingCat.of K) ⟶ Spec (X.residueField x) :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K))
  let a : Spec (CommRingCat.of K) ⟶ X := b ≫ X.fromSpecResidueField x
  have hc := hf.2.2 K a
  have hne : Nonempty {y : Spec (CommRingCat.of K) ⟶ Y // y ≫ f = a} := by
    by_contra hem
    rw [not_nonempty_iff] at hem
    rw [Nat.card_of_isEmpty] at hc
    omega
  obtain ⟨⟨y, hy⟩⟩ := hne
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  refine ⟨y pt, ?_⟩
  have h1 : a pt ∈ Set.range (X.fromSpecResidueField x) := ⟨b pt, by simp [a]⟩
  rw [X.range_fromSpecResidueField] at h1
  rw [← Scheme.Hom.comp_apply, hy]
  exact h1

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hf`. Use `⟨inferInstance, inferInstance, fun K _ _ x => ?_⟩` and prove the remaining obligations. Rewrite using `[← h3 K (x ≫ inv e)]`. Use `Nat.card_congr ⟨fun y => ⟨y.1, ?_⟩, fun y => ⟨y.1, ?_⟩, fun _ => rfl, fun _ => rfl⟩` and prove the remaining obligations. Rewrite using `[← cancel_mono e]`.

Simplify using `[y.2]`. Rewrite using `[← Category.assoc, y.2]`. Simplify using the standard rewrite rules.
-/
private theorem fEt_comp_iso {Y X X' : Scheme.{0}} {f : Y ⟶ X} (e : X ⟶ X') [IsIso e] {d : ℕ}
    (hf : FEt f d) : FEt (f ≫ e) d := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨inferInstance, inferInstance, fun K _ _ x => ?_⟩
  rw [← h3 K (x ≫ inv e)]
  refine Nat.card_congr ⟨fun y => ⟨y.1, ?_⟩, fun y => ⟨y.1, ?_⟩, fun _ => rfl, fun _ => rfl⟩
  · rw [← cancel_mono e]; simp [y.2]
  · rw [← Category.assoc, y.2]; simp

/- English proof (translation)
Introduce `k L O _ _ _ _ H θ C C' j hj hπ g T s t m hL`. Take `⟨hm, κ, h, ht, hF⟩` from `hL`. Establish `first : ∀ x : T, s x ∈ Set.range C.π → t x ∈ Set.range C.π`. Introduce and unpack `x ⟨z, hz⟩`. Take `⟨w, hw1, hw2⟩` from `Scheme.Pullback.exists_preimage_pullback z x hz`.

Take `⟨y, rfl⟩` from `fEt_surj hF hm w`. Use `⟨H.t g y, ?_⟩` and prove the remaining obligations. Establish `hx : κ y = x`. Rewrite using `[← hw2, ← Scheme.Hom.comp_apply, pullback.lift_snd]`. Rewrite using `[← hx, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ht]`.

Use `⟨first, ?_⟩` and prove the remaining obligations. Introduce `T' i s' t' hR`. Establish `: IsOpenImmersion i` using `hR.op`. Establish `: IsOpenImmersion j` using `hj.op`. Establish `hrj : ∀ z, C.π z ∈ Set.range j` using `fun z => ⟨C'.π z, by rw [← hπ, Scheme.Hom.comp_apply]⟩`.

Establish `hκ : Set.range κ ⊆ Set.range i`. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[hR.rng]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show s (κ y) ∈ Set.range j`.

Rewrite using `[← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply]`. Conclude with `hrj _`. Use `show t (κ y) ∈ Set.range j`. Rewrite using `[← Scheme.Hom.comp_apply, ht, Scheme.Hom.comp_apply]`. Conclude with `hrj _`.

Set `κ' : H.Y g ⟶ T'` to `IsOpenImmersion.lift i κ hκ`. Establish `hκ' : κ' ≫ i = κ` using `IsOpenImmersion.lift_fac i κ hκ`. Establish `hs' : H.s g ≫ C'.π = κ' ≫ s'`. Rewrite using `[← cancel_mono j, Category.assoc, Category.assoc, hπ, hR.es, ← Category.assoc, hκ', h]`. Establish `ht' : κ' ≫ t' = H.t g ≫ C'.π`.

Rewrite using `[← cancel_mono j, Category.assoc, Category.assoc, hπ, hR.et, ← Category.assoc, hκ', ht]`. Use `⟨hm, κ', hs', ht', ?_⟩` and prove the remaining obligations. Establish `hσ : Set.range (pullback.snd C.π s) ⊆ Set.range i`. Introduce and unpack `_ ⟨w, rfl⟩`. Establish `hs1 : s (pullback.snd C.π s w) = C.π (pullback.fst C.π s w)`.

Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]`. Establish `hmem : s (pullback.snd C.π s w) ∈ Set.range C.π` using `⟨_, hs1.symm⟩`. Rewrite using `[hR.rng]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show s (pullback.snd C.π s w) ∈ Set.range j`.

Rewrite using `[hs1]`. Conclude with `hrj _`. Use `show t (pullback.snd C.π s w) ∈ Set.range j`. Take `⟨z, hz⟩` from `first _ hmem`. Rewrite using `[← hz]`.

Conclude with `hrj _`. Set `σ : pullback C.π s ⟶ T'` to `IsOpenImmersion.lift i (pullback.snd C.π s) hσ`. Establish `hσ' : σ ≫ i = pullback.snd C.π s` using `IsOpenImmersion.lift_fac i _ hσ`. Establish `hc : pullback.fst C.π s ≫ C'.π = σ ≫ s'`. Rewrite using `[← cancel_mono j, Category.assoc, Category.assoc, hπ, hR.es, ← Category.assoc, hσ', pullback.condition]`.

Set `ψ : pullback C.π s ⟶ pullback C'.π s'` to `pullback.lift (pullback.fst C.π s) σ hc`. Establish `hc' : pullback.fst C'.π s' ≫ C.π = (pullback.snd C'.π s' ≫ i) ≫ s`. Rewrite using `[← hπ, Category.assoc, ← hR.es, ← Category.assoc, ← Category.assoc, pullback.condition]`. Set `φ : pullback C'.π s' ⟶ pullback C.π s` to `pullback.lift (pullback.fst C'.π s') (pullback.snd C'.π s' ≫ i) hc'`. Establish `ψ1 : ψ ≫ pullback.fst C'.π s' = pullback.fst C.π s` using `pullback.lift_fst _ _ _`.

Establish `ψ2 : ψ ≫ pullback.snd C'.π s' = σ` using `pullback.lift_snd _ _ _`. Establish `φ1 : φ ≫ pullback.fst C.π s = pullback.fst C'.π s'` using `pullback.lift_fst _ _ _`. Establish `φ2 : φ ≫ pullback.snd C.π s = pullback.snd C'.π s' ≫ i` using `pullback.lift_snd _ _ _`. Establish `hψφ : ψ ≫ φ = 𝟙 _`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, φ1, ψ1, Category.id_comp]`. Rewrite using `[Category.assoc, φ2, ← Category.assoc, ψ2, hσ', Category.id_comp]`. Establish `hφψ : φ ≫ ψ = 𝟙 _`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, ψ1, φ1, Category.id_comp]`.

Rewrite using `[Category.assoc, ψ2, Category.id_comp, ← cancel_mono i, Category.assoc, hσ', φ2]`. Establish `: IsIso ψ` using `⟨φ, hψφ, hφψ⟩`. Establish `hfac : pullback.lift (H.s g) κ' hs' = pullback.lift (H.s g) κ h ≫ ψ`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[pullback.lift_fst, Category.assoc, ψ1, pullback.lift_fst]`.

Rewrite using `[pullback.lift_snd, Category.assoc, ψ2, ← cancel_mono i, hκ', Category.assoc, hσ', pullback.lift_snd]`. Rewrite using `[hfac]`. Conclude with `fEt_comp_iso ψ hF`.
-/
theorem UpperTheory.Gal.Int.Geo.Cut.liesCut :
    UpperTheory.Gal.Int.Geo.Cut.LiesCut := by
  intro k L O _ _ _ _ H θ C C' j hj hπ g T s t m hL
  obtain ⟨hm, κ, h, ht, hF⟩ := hL
  have first : ∀ x : T, s x ∈ Set.range C.π → t x ∈ Set.range C.π := by
    rintro x ⟨z, hz⟩
    obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback z x hz
    obtain ⟨y, rfl⟩ := fEt_surj hF hm w
    refine ⟨H.t g y, ?_⟩
    have hx : κ y = x := by
      rw [← hw2, ← Scheme.Hom.comp_apply, pullback.lift_snd]
    rw [← hx, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ht]
  refine ⟨first, ?_⟩
  intro T' i s' t' hR
  have : IsOpenImmersion i := hR.op
  have : IsOpenImmersion j := hj.op
  have hrj : ∀ z, C.π z ∈ Set.range j := fun z =>
    ⟨C'.π z, by rw [← hπ, Scheme.Hom.comp_apply]⟩
  have hκ : Set.range κ ⊆ Set.range i := by
    rintro _ ⟨y, rfl⟩
    rw [hR.rng]
    refine ⟨?_, ?_⟩
    · show s (κ y) ∈ Set.range j
      rw [← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply]
      exact hrj _
    · show t (κ y) ∈ Set.range j
      rw [← Scheme.Hom.comp_apply, ht, Scheme.Hom.comp_apply]
      exact hrj _
  let κ' : H.Y g ⟶ T' := IsOpenImmersion.lift i κ hκ
  have hκ' : κ' ≫ i = κ := IsOpenImmersion.lift_fac i κ hκ
  have hs' : H.s g ≫ C'.π = κ' ≫ s' := by
    rw [← cancel_mono j, Category.assoc, Category.assoc, hπ, hR.es, ← Category.assoc, hκ', h]
  have ht' : κ' ≫ t' = H.t g ≫ C'.π := by
    rw [← cancel_mono j, Category.assoc, Category.assoc, hπ, hR.et, ← Category.assoc, hκ', ht]
  refine ⟨hm, κ', hs', ht', ?_⟩
  have hσ : Set.range (pullback.snd C.π s) ⊆ Set.range i := by
    rintro _ ⟨w, rfl⟩
    have hs1 : s (pullback.snd C.π s w) = C.π (pullback.fst C.π s w) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    have hmem : s (pullback.snd C.π s w) ∈ Set.range C.π := ⟨_, hs1.symm⟩
    rw [hR.rng]
    refine ⟨?_, ?_⟩
    · show s (pullback.snd C.π s w) ∈ Set.range j
      rw [hs1]; exact hrj _
    · show t (pullback.snd C.π s w) ∈ Set.range j
      obtain ⟨z, hz⟩ := first _ hmem
      rw [← hz]; exact hrj _
  let σ : pullback C.π s ⟶ T' := IsOpenImmersion.lift i (pullback.snd C.π s) hσ
  have hσ' : σ ≫ i = pullback.snd C.π s := IsOpenImmersion.lift_fac i _ hσ
  have hc : pullback.fst C.π s ≫ C'.π = σ ≫ s' := by
    rw [← cancel_mono j, Category.assoc, Category.assoc, hπ, hR.es, ← Category.assoc, hσ',
      pullback.condition]
  let ψ : pullback C.π s ⟶ pullback C'.π s' := pullback.lift (pullback.fst C.π s) σ hc
  have hc' : pullback.fst C'.π s' ≫ C.π = (pullback.snd C'.π s' ≫ i) ≫ s := by
    rw [← hπ, Category.assoc, ← hR.es, ← Category.assoc, ← Category.assoc, pullback.condition]
  let φ : pullback C'.π s' ⟶ pullback C.π s :=
    pullback.lift (pullback.fst C'.π s') (pullback.snd C'.π s' ≫ i) hc'
  have ψ1 : ψ ≫ pullback.fst C'.π s' = pullback.fst C.π s := pullback.lift_fst _ _ _
  have ψ2 : ψ ≫ pullback.snd C'.π s' = σ := pullback.lift_snd _ _ _
  have φ1 : φ ≫ pullback.fst C.π s = pullback.fst C'.π s' := pullback.lift_fst _ _ _
  have φ2 : φ ≫ pullback.snd C.π s = pullback.snd C'.π s' ≫ i := pullback.lift_snd _ _ _
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, φ1, ψ1, Category.id_comp]
    · rw [Category.assoc, φ2, ← Category.assoc, ψ2, hσ', Category.id_comp]
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, ψ1, φ1, Category.id_comp]
    · rw [Category.assoc, ψ2, Category.id_comp, ← cancel_mono i, Category.assoc, hσ', φ2]
  have : IsIso ψ := ⟨φ, hψφ, hφψ⟩
  have hfac : pullback.lift (H.s g) κ' hs' = pullback.lift (H.s g) κ h ≫ ψ := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, ψ1, pullback.lift_fst]
    · rw [pullback.lift_snd, Category.assoc, ψ2, ← cancel_mono i, hκ', Category.assoc, hσ',
        pullback.lift_snd]
  rw [hfac]
  exact fEt_comp_iso ψ hF
