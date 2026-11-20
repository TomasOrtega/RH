import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCptBase

/- English proof (translation)
Set `K` to `AlgebraicClosure (S.residueField s)`. Take `⟨t⟩ : Nonempty (Sp K)` from `inferInstance`. Use `⟨K, inferInstance, inferInstance, spMap (algebraMap (S.residueField s) K) ≫ S.fromSpecResidueField s, t, ?_⟩` and prove the remaining obligations. Establish `h : S.fromSpecResidueField s (spMap (algebraMap (S.residueField s) K) t) ∈ Set.range (S.fromSpecResidueField s)` using `⟨_, rfl⟩`. Rewrite `h` using `[Scheme.range_fromSpecResidueField]`.

Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `h`.
-/
theorem exists_geomPt (S : Scheme.{0}) (s : S) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (q : Sp K ⟶ S), s ∈ Set.range q := by
  let K := AlgebraicClosure (S.residueField s)
  obtain ⟨t⟩ : Nonempty (Sp K) := inferInstance
  refine ⟨K, inferInstance, inferInstance, spMap (algebraMap (S.residueField s) K) ≫ S.fromSpecResidueField s, t, ?_⟩
  have h : S.fromSpecResidueField s (spMap (algebraMap (S.residueField s) K) t) ∈
      Set.range (S.fromSpecResidueField s) := ⟨_, rfl⟩
  rw [Scheme.range_fromSpecResidueField] at h
  rw [Scheme.Hom.comp_apply]
  exact h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

/- English proof (translation)
Establish `hZ : IsProper Z.s` using `projProper O Z.X Z.s Z.proj`. Establish `: IsProper (genStr Z)` using `inferInstance`. Establish `: IsSeparated (genStr Z ≫ spMap e.toRingHom)` using `inferInstance`. Establish `: IsProper (C.π ≫ genStr Z ≫ spMap e.toRingHom)` using `by rw [C.π_str]; infer_instance`. Establish `: IsProper C.π` using `IsProper.of_comp C.π (genStr Z ≫ spMap e.toRingHom)`.

Conclude with `C.π.isClosedMap.isClosed_range`.
-/
theorem isClosed_range_π (C : FlagCpt Z e) : IsClosed (Set.range C.π) := by
  have hZ : IsProper Z.s := projProper O Z.X Z.s Z.proj
  have : IsProper (genStr Z) := inferInstance
  have : IsSeparated (genStr Z ≫ spMap e.toRingHom) := inferInstance
  have : IsProper (C.π ≫ genStr Z ≫ spMap e.toRingHom) := by rw [C.π_str]; infer_instance
  have : IsProper C.π := IsProper.of_comp C.π (genStr Z ≫ spMap e.toRingHom)
  exact C.π.isClosedMap.isClosed_range

end GlobalTheory.FlagCptBase

namespace GlobalTheory.FlagCptBase

open CategoryTheory.Limits

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F} {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N}

/- English proof (translation)
Take `⟨K, _, _, q, t, hq⟩` from `exists_geomPt _ w`. Set `χ : c.F →+* K` to `(Spec.preimage (q ≫ genStr Z)).hom`. Establish `hχ : q ≫ genStr Z = spMap χ` using `(Spec.map_preimage _).symm`. Take `⟨g⟩` from `GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β Z K χ q hχ`. Take `⟨⟨i, p⟩, ⟨hp, -⟩, -⟩` from `Φ.lifts K χ q hχ g`.

Use `⟨i, p t, ?_⟩` and prove the remaining obligations. Rewrite using `[← hq, ← Scheme.Hom.comp_apply]`. Conclude with `congrArg (fun m : Sp K ⟶ gen Z => m t) hp`.
-/
theorem exists_mem_range (Φ : FlagTor Z e U) (w : gen Z) : ∃ i, w ∈ Set.range (Φ.C i).π := by
  obtain ⟨K, _, _, q, t, hq⟩ := exists_geomPt _ w
  let χ : c.F →+* K := (Spec.preimage (q ≫ genStr Z)).hom
  have hχ : q ≫ genStr Z = spMap χ := (Spec.map_preimage _).symm
  obtain ⟨g⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β Z K χ q hχ
  obtain ⟨⟨i, p⟩, ⟨hp, -⟩, -⟩ := Φ.lifts K χ q hχ g
  refine ⟨i, p t, ?_⟩
  rw [← hq, ← Scheme.Hom.comp_apply]
  exact congrArg (fun m : Sp K ⟶ gen Z => m t) hp

/- English proof (translation)
Take `⟨z, -, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := (Φ.C i).π) (g := (Φ.C i').π) y y' h`. Take `⟨K, _, _, q, -⟩` from `exists_geomPt _ z`. Set `p` to `q ≫ pullback.fst (Φ.C i).π (Φ.C i').π`. Set `p'` to `q ≫ pullback.snd (Φ.C i).π (Φ.C i').π`. Set `w` to `p ≫ (Φ.C i).π`.

Establish `hw' : p' ≫ (Φ.C i').π = w`. Simplify using `only [p, p', w, Category.assoc, pullback.condition]`. Set `χ : c.F →+* K` to `(Spec.preimage (w ≫ genStr Z)).hom`. Establish `hχ : w ≫ genStr Z = spMap χ` using `(Spec.map_preimage _).symm`. Establish `hB' : ∀ (i : U.Comp) (p : Sp K ⟶ (Φ.C i).Y.X) (x : Sp K ⟶ gen Z), p ≫ (Φ.C i).π = x → x ≫ genStr Z = spMap χ → ∃ g : EigFrame Z χ (x ≫ genι Z), (Φ.C i).Carries p g`.

Introduce `i p x hx hxχ`. Substitute `hx` using the available equality. Rewrite `hxχ`, the goal using `[Category.assoc]`. Conclude with `hB i K χ p hxχ`. Take `⟨g, hg⟩` from `hB' i p w rfl hχ`.

Take `⟨g', hg'⟩` from `hB' i' p' w hw' hχ`. Take `⟨p'', hp'', hc''⟩` from `hA i K χ w hχ g g' p rfl hg`. Take `⟨_, -, huniq⟩` from `Φ.lifts K χ w hχ g'`. Establish `h1` using `huniq ⟨i, p''⟩ ⟨hp'', hc''⟩`. Establish `h2` using `huniq ⟨i', p'⟩ ⟨hw', hg'⟩`.

Conclude with `congrArg Sigma.fst (h1.trans h2.symm)`.
-/
theorem eq_of_apply_eq (Φ : FlagTor Z e U)
    (hA : ∀ (i : U.Comp) (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z),
      x ≫ genStr Z = spMap χ → ∀ (g g' : EigFrame Z χ (x ≫ genι Z)) (p : Sp K ⟶ (Φ.C i).Y.X), p ≫ (Φ.C i).π = x →
      (Φ.C i).Carries p g → ∃ p' : Sp K ⟶ (Φ.C i).Y.X, p' ≫ (Φ.C i).π = x ∧ (Φ.C i).Carries p' g')
    (hB : ∀ (i : U.Comp) (K : Type) [Field K] (χ : c.F →+* K) (p : Sp K ⟶ (Φ.C i).Y.X),
      p ≫ (Φ.C i).π ≫ genStr Z = spMap χ → ∃ g : EigFrame Z χ (p ≫ (Φ.C i).π ≫ genι Z), (Φ.C i).Carries p g)
    {i i' : U.Comp} (y : (Φ.C i).Y.X) (y' : (Φ.C i').Y.X) (h : (Φ.C i).π y = (Φ.C i').π y') : i = i' := by
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := (Φ.C i).π) (g := (Φ.C i').π) y y' h
  obtain ⟨K, _, _, q, -⟩ := exists_geomPt _ z
  let p := q ≫ pullback.fst (Φ.C i).π (Φ.C i').π
  let p' := q ≫ pullback.snd (Φ.C i).π (Φ.C i').π
  let w := p ≫ (Φ.C i).π
  have hw' : p' ≫ (Φ.C i').π = w := by
    simp only [p, p', w, Category.assoc, pullback.condition]
  let χ : c.F →+* K := (Spec.preimage (w ≫ genStr Z)).hom
  have hχ : w ≫ genStr Z = spMap χ := (Spec.map_preimage _).symm
  have hB' : ∀ (i : U.Comp) (p : Sp K ⟶ (Φ.C i).Y.X) (x : Sp K ⟶ gen Z), p ≫ (Φ.C i).π = x →
      x ≫ genStr Z = spMap χ → ∃ g : EigFrame Z χ (x ≫ genι Z), (Φ.C i).Carries p g := by
    intro i p x hx hxχ
    subst hx
    rw [Category.assoc] at hxχ ⊢
    exact hB i K χ p hxχ
  obtain ⟨g, hg⟩ := hB' i p w rfl hχ
  obtain ⟨g', hg'⟩ := hB' i' p' w hw' hχ
  obtain ⟨p'', hp'', hc''⟩ := hA i K χ w hχ g g' p rfl hg
  obtain ⟨_, -, huniq⟩ := Φ.lifts K χ w hχ g'
  have h1 := huniq ⟨i, p''⟩ ⟨hp'', hc''⟩
  have h2 := huniq ⟨i', p'⟩ ⟨hw', hg'⟩
  exact congrArg Sigma.fst (h1.trans h2.symm)

end GlobalTheory.FlagCptBase

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U Φ k X j hj _ f hf hA hB K _ _ χ x hx`. Set `W : U.Comp → Set X.X` to `fun i => j ⁻¹' Set.range (Φ.C i).π`. Establish `hcl : ∀ i, IsClosed (W i)` using `fun i => (GlobalTheory.FlagCptBase.isClosed_range_π (Φ.C i)).preimage j.continuous`. Establish `hdis : ∀ i i' z, z ∈ W i → z ∈ W i' → i = i'`. Introduce and unpack `i i' z ⟨y, hy⟩ ⟨y', hy'⟩`.

Conclude with `GlobalTheory.FlagCptBase.eq_of_apply_eq Φ hA hB y y' (hy.trans hy'.symm)`. Establish `hcov : ∀ z, ∃ i, z ∈ W i` using `fun z => GlobalTheory.FlagCptBase.exists_mem_range Φ (j z)`. Establish `hWk : W k = Set.univ`. Establish `hc : (W k)ᶜ = ⋃ i ∈ ({k}ᶜ : Set U.Comp), W i`. Use extensionality with `z`.

Simplify using `only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Take `⟨i, hi⟩` from `hcov z`. Conclude with `⟨i, fun h => hz (h ▸ hi), hi⟩`.

Introduce and unpack `⟨i, hik, hi⟩ hz`. Conclude with `hik (hdis i k z hi hz)`. Establish `hopen : IsOpen (W k)`. Rewrite using `[← isClosed_compl_iff, hc]`. Conclude with `Set.Finite.isClosed_biUnion (Set.toFinite _) (fun i _ => hcl i)`.

Take `⟨y⟩ : Nonempty (Φ.C k).Y.X` from `inferInstance`. Establish `hne : (W k).Nonempty` using `⟨f y, y, by rw [← hf, Scheme.Hom.comp_apply]⟩`. Conclude with `IsClopen.eq_univ ⟨hcl k, hopen⟩ hne`. Establish `hx' : (x ≫ j) ≫ genStr Z = spMap χ` using `by rw [Category.assoc]; exact hx`. Take `⟨g⟩` from `GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β Z K χ (x ≫ j) hx'`.

Take `⟨⟨i, p⟩, ⟨hp, -⟩, -⟩` from `Φ.lifts K χ (x ≫ j) hx' g`. Take `⟨t⟩ : Nonempty (Sp K)` from `inferInstance`. Establish `hi : i = k`. Establish `h1 : x t ∈ W i` using `⟨p t, by`. Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]`.

Conclude with `congrArg (fun m : Sp K ⟶ gen Z => m t) hp⟩`. Establish `h2 : x t ∈ W k` using `hWk ▸ Set.mem_univ _`. Conclude with `hdis _ _ _ h1 h2`. Substitute `hi` using the available equality. Use `⟨p, ?_⟩` and prove the remaining obligations.

Rewrite using `[← cancel_mono j, Category.assoc, hf]`. Conclude with `hp`.
-/
theorem GlobalTheory.FlagCptBase.exists_pt_over_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U) (k : U.Comp) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : (Φ.C k).Y.X ⟶ X.X), f ≫ j = (Φ.C k).π → (∀ (i : U.Comp) (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z), x ≫ genStr Z = spMap χ → ∀ (g g' : EigFrame Z χ (x ≫ genι Z)) (p : Sp K ⟶ (Φ.C i).Y.X), p ≫ (Φ.C i).π = x → (Φ.C i).Carries p g → ∃ p' : Sp K ⟶ (Φ.C i).Y.X, p' ≫ (Φ.C i).π = x ∧ (Φ.C i).Carries p' g') → (∀ (i : U.Comp) (K : Type) [Field K] (χ : c.F →+* K) (p : Sp K ⟶ (Φ.C i).Y.X), p ≫ (Φ.C i).π ≫ genStr Z = spMap χ → ∃ g : EigFrame Z χ (p ≫ (Φ.C i).π ≫ genι Z), (Φ.C i).Carries p g) → ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∃ p : Sp K ⟶ (Φ.C k).Y.X, p ≫ f = x := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U Φ k X j hj _ f hf hA hB K _ _ χ x hx
  let W : U.Comp → Set X.X := fun i => j ⁻¹' Set.range (Φ.C i).π
  have hcl : ∀ i, IsClosed (W i) := fun i => (GlobalTheory.FlagCptBase.isClosed_range_π (Φ.C i)).preimage j.continuous
  have hdis : ∀ i i' z, z ∈ W i → z ∈ W i' → i = i' := by
    rintro i i' z ⟨y, hy⟩ ⟨y', hy'⟩
    exact GlobalTheory.FlagCptBase.eq_of_apply_eq Φ hA hB y y' (hy.trans hy'.symm)
  have hcov : ∀ z, ∃ i, z ∈ W i := fun z => GlobalTheory.FlagCptBase.exists_mem_range Φ (j z)
  have hWk : W k = Set.univ := by
    have hc : (W k)ᶜ = ⋃ i ∈ ({k}ᶜ : Set U.Comp), W i := by
      ext z
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
      constructor
      · intro hz
        obtain ⟨i, hi⟩ := hcov z
        exact ⟨i, fun h => hz (h ▸ hi), hi⟩
      · rintro ⟨i, hik, hi⟩ hz
        exact hik (hdis i k z hi hz)
    have hopen : IsOpen (W k) := by
      rw [← isClosed_compl_iff, hc]
      exact Set.Finite.isClosed_biUnion (Set.toFinite _) (fun i _ => hcl i)
    obtain ⟨y⟩ : Nonempty (Φ.C k).Y.X := inferInstance
    have hne : (W k).Nonempty := ⟨f y, y, by rw [← hf, Scheme.Hom.comp_apply]⟩
    exact IsClopen.eq_univ ⟨hcl k, hopen⟩ hne
  have hx' : (x ≫ j) ≫ genStr Z = spMap χ := by rw [Category.assoc]; exact hx
  obtain ⟨g⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β Z K χ (x ≫ j) hx'
  obtain ⟨⟨i, p⟩, ⟨hp, -⟩, -⟩ := Φ.lifts K χ (x ≫ j) hx' g
  obtain ⟨t⟩ : Nonempty (Sp K) := inferInstance
  have hi : i = k := by
    have h1 : x t ∈ W i := ⟨p t, by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      exact congrArg (fun m : Sp K ⟶ gen Z => m t) hp⟩
    have h2 : x t ∈ W k := hWk ▸ Set.mem_univ _
    exact hdis _ _ _ h1 h2
  subst hi
  refine ⟨p, ?_⟩
  rw [← cancel_mono j, Category.assoc, hf]
  exact hp
