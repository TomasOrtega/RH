import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafChartRing
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut

/- English proof (translation)
Introduce `hP a1 R _ F c Z ι O j _ disj cov W h`. Establish `hsq : ∀ a, sch.map (j a ∣_ W) ≫ sch.map W.ι = sch.map (j a ⁻¹ᵁ W).ι ≫ sch.map (j a)` using `fun a => by`. Rewrite using `[← Functor.map_comp, ← Functor.map_comp, morphismRestrict_ι]`. Establish `hval : ∀ a (y : (j a ⁻¹ᵁ W).toScheme), W.ι ((j a ∣_ W) y) = j a ((j a ⁻¹ᵁ W).ι y)` using `fun a y => by`. Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, morphismRestrict_ι]`.

Establish `disjW : ∀ a b, a ≠ b → Disjoint (Set.range (j a ∣_ W)) (Set.range (j b ∣_ W))`. Introduce `a b hab`. Rewrite using `[Set.disjoint_left]`. Introduce and unpack `_ ⟨x, rfl⟩ ⟨y, hy⟩`. Use `Set.disjoint_left.1 (disj a b hab) ⟨(j a ⁻¹ᵁ W).ι x, (hval a x).symm⟩ ⟨(j b ⁻¹ᵁ W).ι y, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hval b y, hy]`. Establish `covW : ∀ y : W.toScheme, ∃ a, y ∈ Set.range (j a ∣_ W)`. Introduce `y`. Take `⟨a, x, hx⟩` from `cov (W.ι y)`. Establish `hxW : x ∈ j a ⁻¹ᵁ W`.

Express the relevant statement in the definitionally equal form `j a x ∈ W`. Rewrite using `[hx]`. Conclude with `y.2`. Choose the witnesses or unpack the hypotheses as in `⟨x', rfl⟩ : x ∈ Set.range (j a ⁻¹ᵁ W).ι := by`. Rewrite using `[Scheme.Opens.range_ι]`.

Conclude with `hxW`. Conclude with `⟨a, x', W.ι.isOpenEmbedding.injective ((hval a x').trans hx)⟩`. Establish `key : ∀ (n : ℤ) (x : H R (sch.obj Z) F n) (a : ι), pull R (sch.map (j a ∣_ W)) F n (pull R (sch.map W.ι) F n x) = pull R (sch.map (j a ⁻¹ᵁ W).ι) F n (pull R (sch.map (j a)) F n x)`. Introduce `n x a`. Rewrite using `[← pull_comp, ← pull_comp, hsq]`.

Introduce `n`. Establish `PZ` using `hP a1 R F O j disj cov n`. Establish `PW` using `hP a1 R F (fun a => (j a ⁻¹ᵁ W).toScheme) (fun a => j a ∣_ W) disjW covW n`. Establish `hinj : n < c → Function.Injective (pull R (sch.map W.ι) F n)`. Introduce `hn x y hxy`.

Apply `PZ.1` to reduce the goal to its premises. Use function extensionality and compare the values at `a`. Establish `ha : Function.Injective (pull R (sch.map (j a ⁻¹ᵁ W).ι) F n)` using `(h a n).2 hn`. Apply `ha` to reduce the goal to its premises. Rewrite using `[← key, ← key, hxy]`.

Use `⟨fun hn => ⟨hinj (by omega), ?_⟩, hinj⟩` and prove the remaining obligations. Introduce `y`. Establish `hs : ∀ a, ∃ z, pull R (sch.map (j a ⁻¹ᵁ W).ι) F n z = pull R (sch.map (j a ∣_ W)) F n y`. Introduce `a`. Establish `ha : Function.Bijective (pull R (sch.map (j a ⁻¹ᵁ W).ι) F n)` using `(h a n).1 hn`.

Conclude with `ha.2 _`. Use `choose z hz using hs`. Take `⟨x, hx⟩` from `PZ.2 z`. Use `⟨x, ?_⟩` and prove the remaining obligations. Apply `PW.1` to reduce the goal to its premises.

Use function extensionality and compare the values at `a`. Establish `hxa : pull R (sch.map (j a)) F n x = z a` using `congrFun hx a`. Express the relevant statement in the definitionally equal form `pull R (sch.map (j a ∣_ W)) F n (pull R (sch.map W.ι) F n x) = pull R (sch.map (j a ∣_ W)) F n y`. Rewrite using `[key, hxa, hz]`.
-/
theorem UpperTheory.connectivity_of_disjoint_open_cover :
    LeafProd → A1 → ∀ (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {Z : Scheme.{0}} {ι : Type} (O : ι → Scheme.{0}) (j : ∀ a, O a ⟶ Z) [∀ a, IsOpenImmersion (j a)],
      (∀ a b, a ≠ b → Disjoint (Set.range (j a)) (Set.range (j b))) → (∀ y : Z, ∃ a, y ∈ Set.range (j a)) → ∀ W : Z.Opens,
      (∀ a, Conn R F c (sch.map (j a ⁻¹ᵁ W).ι)) → Conn R F c (sch.map W.ι) := by
  intro hP a1 R _ F c Z ι O j _ disj cov W h
  have hsq : ∀ a, sch.map (j a ∣_ W) ≫ sch.map W.ι = sch.map (j a ⁻¹ᵁ W).ι ≫ sch.map (j a) := fun a => by
    rw [← Functor.map_comp, ← Functor.map_comp, morphismRestrict_ι]
  have hval : ∀ a (y : (j a ⁻¹ᵁ W).toScheme), W.ι ((j a ∣_ W) y) = j a ((j a ⁻¹ᵁ W).ι y) := fun a y => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, morphismRestrict_ι]
  have disjW : ∀ a b, a ≠ b → Disjoint (Set.range (j a ∣_ W)) (Set.range (j b ∣_ W)) := by
    intro a b hab
    rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    refine Set.disjoint_left.1 (disj a b hab) ⟨(j a ⁻¹ᵁ W).ι x, (hval a x).symm⟩ ⟨(j b ⁻¹ᵁ W).ι y, ?_⟩
    rw [← hval b y, hy]
  have covW : ∀ y : W.toScheme, ∃ a, y ∈ Set.range (j a ∣_ W) := by
    intro y
    obtain ⟨a, x, hx⟩ := cov (W.ι y)
    have hxW : x ∈ j a ⁻¹ᵁ W := by
      change j a x ∈ W
      rw [hx]
      exact y.2
    obtain ⟨x', rfl⟩ : x ∈ Set.range (j a ⁻¹ᵁ W).ι := by
      rw [Scheme.Opens.range_ι]
      exact hxW
    exact ⟨a, x', W.ι.isOpenEmbedding.injective ((hval a x').trans hx)⟩
  have key : ∀ (n : ℤ) (x : H R (sch.obj Z) F n) (a : ι),
      pull R (sch.map (j a ∣_ W)) F n (pull R (sch.map W.ι) F n x) =
        pull R (sch.map (j a ⁻¹ᵁ W).ι) F n (pull R (sch.map (j a)) F n x) := by
    intro n x a
    rw [← pull_comp, ← pull_comp, hsq]
  intro n
  have PZ := hP a1 R F O j disj cov n
  have PW := hP a1 R F (fun a => (j a ⁻¹ᵁ W).toScheme) (fun a => j a ∣_ W) disjW covW n
  have hinj : n < c → Function.Injective (pull R (sch.map W.ι) F n) := by
    intro hn x y hxy
    apply PZ.1
    funext a
    have ha : Function.Injective (pull R (sch.map (j a ⁻¹ᵁ W).ι) F n) := (h a n).2 hn
    apply ha
    rw [← key, ← key, hxy]
  refine ⟨fun hn => ⟨hinj (by omega), ?_⟩, hinj⟩
  intro y
  have hs : ∀ a, ∃ z, pull R (sch.map (j a ⁻¹ᵁ W).ι) F n z = pull R (sch.map (j a ∣_ W)) F n y := by
    intro a
    have ha : Function.Bijective (pull R (sch.map (j a ⁻¹ᵁ W).ι) F n) := (h a n).1 hn
    exact ha.2 _
  choose z hz using hs
  obtain ⟨x, hx⟩ := PZ.2 z
  refine ⟨x, ?_⟩
  apply PW.1
  funext a
  have hxa : pull R (sch.map (j a)) F n x = z a := congrFun hx a
  change pull R (sch.map (j a ∣_ W)) F n (pull R (sch.map W.ι) F n x) = pull R (sch.map (j a ∣_ W)) F n y
  rw [key, hxa, hz]

end
