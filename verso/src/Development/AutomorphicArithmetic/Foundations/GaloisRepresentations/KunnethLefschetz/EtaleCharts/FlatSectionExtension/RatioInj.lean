import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.USelf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GvChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartInj

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

/- English proof (translation)
Establish `h1 : V.basicOpen (uV B β m y h l) = ⊤` using `Scheme.basicOpen_of_isUnit V hu`. Establish `h2 : V.basicOpen (uV B β m y h l) ≤ y ⁻¹ᵁ (Y.basicOpen ((B.c β).u m l))`. Unfold `uV`. Rewrite using `[Scheme.Hom.appLE]`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply]`.

Rewrite using `[Scheme.basicOpen_res, Scheme.preimage_basicOpen]`. Conclude with `inf_le_right`. Introduce `x hx`. Establish `h3 : x ∈ y ⁻¹ᵁ (Y.basicOpen ((B.c β).u m l))` using `h2 (h1.ge hx)`. Establish `h4 : y x ∈ Y.basicOpen ((B.c β).u m l)` using `h3`.

Rewrite `h4` using `[← (B.c β).inter m l]`. Conclude with `h4.2`.
-/
private theorem mem_of_unit {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (β : B.ι) (m l : Fin d) {V : Scheme.{0}} (y : V ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ (B.c β).C m) (hu : IsUnit (uV B β m y h l)) : ⊤ ≤ y ⁻¹ᵁ (B.c β).C l := by
  have h1 : V.basicOpen (uV B β m y h l) = ⊤ := Scheme.basicOpen_of_isUnit V hu
  have h2 : V.basicOpen (uV B β m y h l) ≤ y ⁻¹ᵁ (Y.basicOpen ((B.c β).u m l)) := by
    unfold uV
    rw [Scheme.Hom.appLE]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    rw [Scheme.basicOpen_res, Scheme.preimage_basicOpen]
    exact inf_le_right
  intro x hx
  have h3 : x ∈ y ⁻¹ᵁ (Y.basicOpen ((B.c β).u m l)) := h2 (h1.ge hx)
  have h4 : y x ∈ Y.basicOpen ((B.c β).u m l) := h3
  rw [← (B.c β).inter m l] at h4
  exact h4.2

/- English proof (translation)
Introduce `K _ W Z Y q i π D d B β m l V y y' p h h' s hy hy' e`. Establish `hl : uV B β m y h l = (s : Γ(V, ⊤))`. Use `congrFun e l` as an intermediate fact. Simplify `this` using `[uSelf B β l y' h']`. Establish `h'' : ⊤ ≤ y ⁻¹ᵁ (B.c β).C l` using `mem_of_unit B β m l y h (hl ▸ s.isUnit)`.

Establish `hV : ∀ x : V, (p ≫ i) x ∈ B.V β`. Introduce `x`. Rewrite using `[← hy, Scheme.Hom.comp_apply]`. Conclude with `(B.c β).C_le m (h (Set.mem_univ x))`. Establish `hg` using `gvChart B y p hy β β m l h h'' 1 (locMatOne B β p hV)`.

Rewrite `hg` using `[Matrix.one_mulVec]`. Take `⟨c, hc⟩ : ∃ c : (Γ(V, ⊤))ˣ, uV B β m y h = (c : Γ(V, ⊤)) • uV B β l y h''` from `⟨_, hg⟩`. Establish `hcs : (c : Γ(V, ⊤)) = s`. Use `congrFun hc l` as an intermediate fact. Rewrite `this` using `[hl, Pi.smul_apply, uSelf B β l y h'', smul_eq_mul, mul_one]`.

Conclude with `this.symm`. Establish `hvv : uV B β l y h'' = uV B β l y' h'`. Use function extensionality and compare the values at `j`. Establish `h1` using `congrFun hc j`. Establish `h2` using `congrFun e j`.

Rewrite `h1`, `h2` using `[Pi.smul_apply, smul_eq_mul]`. Rewrite `h1` using `[hcs]`. Conclude with `s.isUnit.mul_left_cancel (h1.symm.trans h2)`. Conclude with `chartInj B β l y y' h'' h' (hy.trans hy'.symm) hvv`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.G.PX.ratioInj :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (β : B.ι) (m l : Fin d) {V : Scheme.{0}} (y y' : V ⟶ Y) (p : V ⟶ W) (h : ⊤ ≤ y ⁻¹ᵁ (B.c β).C m) (h' : ⊤ ≤ y' ⁻¹ᵁ (B.c β).C l) (s : (Γ(V, ⊤))ˣ), y ≫ π = p ≫ i → y' ≫ π = p ≫ i → uV B β m y h = (s : Γ(V, ⊤)) • uV B β l y' h' → y = y' := by
  intro K _ W Z Y q i π D d B β m l V y y' p h h' s hy hy' e
  have hl : uV B β m y h l = (s : Γ(V, ⊤)) := by
    have := congrFun e l
    simpa [uSelf B β l y' h'] using this
  have h'' : ⊤ ≤ y ⁻¹ᵁ (B.c β).C l := mem_of_unit B β m l y h (hl ▸ s.isUnit)
  have hV : ∀ x : V, (p ≫ i) x ∈ B.V β := by
    intro x
    rw [← hy, Scheme.Hom.comp_apply]
    exact (B.c β).C_le m (h (Set.mem_univ x))
  have hg := gvChart B y p hy β β m l h h'' 1 (locMatOne B β p hV)
  rw [Matrix.one_mulVec] at hg
  obtain ⟨c, hc⟩ : ∃ c : (Γ(V, ⊤))ˣ, uV B β m y h = (c : Γ(V, ⊤)) • uV B β l y h'' := ⟨_, hg⟩
  have hcs : (c : Γ(V, ⊤)) = s := by
    have := congrFun hc l
    rw [hl, Pi.smul_apply, uSelf B β l y h'', smul_eq_mul, mul_one] at this
    exact this.symm
  have hvv : uV B β l y h'' = uV B β l y' h' := by
    funext j
    have h1 := congrFun hc j
    have h2 := congrFun e j
    rw [Pi.smul_apply, smul_eq_mul] at h1 h2
    rw [hcs] at h1
    exact s.isUnit.mul_left_cancel (h1.symm.trans h2)
  exact chartInj B β l y y' h'' h' (hy.trans hy'.symm) hvv
