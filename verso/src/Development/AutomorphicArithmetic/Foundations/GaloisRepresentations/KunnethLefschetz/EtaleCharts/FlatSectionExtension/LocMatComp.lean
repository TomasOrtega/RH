import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

namespace UpperTheory.Gal.KunnethLefschetz.G.PX

/- English proof (translation)
Establish `e1 : U₂.ι.appTop = U.ι.appTop ≫ (V.homOfLE hUU).appTop`. Rewrite using `[← Scheme.Hom.comp_appTop, Scheme.homOfLE_ι]`. Establish `hT : (⊤ : (U₂ : Scheme.{0}).Opens) ≤ (V.homOfLE hUU) ⁻¹ᵁ ⊤` using `fun _ _ => trivial`. Establish `e0 : (V.homOfLE hUU).appLE ⊤ ⊤ hT = (V.homOfLE hUU).appTop` using `(Scheme.Hom.app_eq_appLE (V.homOfLE hUU)).symm`. Establish `e2 : Z.presheaf.map (homOfLE hN).op ≫ (U₂.ι ≫ f).appLE N₂ ⊤ hU₂ = (U.ι ≫ f).appLE N ⊤ hU ≫ (V.homOfLE hUU).appTop`.

Rewrite using `[← e0, Scheme.Hom.map_appLE, Scheme.Hom.appLE_comp_appLE]`. Simplify using `only [← Category.assoc, Scheme.homOfLE_ι]`. Establish `e3` using `congrArg (fun φ => φ.hom g) e2`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at e3`. Rewrite using `[e1, CommRingCat.hom_comp, RingHom.comp_apply, h, ← e3]`.
-/
private lemma restr_sec {V Z : Scheme.{0}} (f : V ⟶ Z) {U U₂ : V.Opens} {N N₂ : Z.Opens}
    (hN : N₂ ≤ N) (hUU : U₂ ≤ U) (hU : ⊤ ≤ (U.ι ≫ f) ⁻¹ᵁ N) (hU₂ : ⊤ ≤ (U₂.ι ≫ f) ⁻¹ᵁ N₂)
    (s : Γ(V, ⊤)) (g : Γ(Z, N))
    (h : U.ι.appTop.hom s = ((U.ι ≫ f).appLE N ⊤ hU).hom g) :
    U₂.ι.appTop.hom s =
      ((U₂.ι ≫ f).appLE N₂ ⊤ hU₂).hom ((Z.presheaf.map (homOfLE hN).op).hom g) := by
  have e1 : U₂.ι.appTop = U.ι.appTop ≫ (V.homOfLE hUU).appTop := by
    rw [← Scheme.Hom.comp_appTop, Scheme.homOfLE_ι]
  have hT : (⊤ : (U₂ : Scheme.{0}).Opens) ≤ (V.homOfLE hUU) ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have e0 : (V.homOfLE hUU).appLE ⊤ ⊤ hT = (V.homOfLE hUU).appTop :=
    (Scheme.Hom.app_eq_appLE (V.homOfLE hUU)).symm
  have e2 : Z.presheaf.map (homOfLE hN).op ≫ (U₂.ι ≫ f).appLE N₂ ⊤ hU₂ =
      (U.ι ≫ f).appLE N ⊤ hU ≫ (V.homOfLE hUU).appTop := by
    rw [← e0, Scheme.Hom.map_appLE, Scheme.Hom.appLE_comp_appLE]
    simp only [← Category.assoc, Scheme.homOfLE_ι]
  have e3 := congrArg (fun φ => φ.hom g) e2
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e3
  rw [e1, CommRingCat.hom_comp, RingHom.comp_apply, h, ← e3]

variable {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)}
  {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ}

/- English proof (translation)
Simplify using `only [tN]`. Rewrite using `[← CommRingCat.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
private lemma tN_res (B : Blow q i π D d) (α : B.ι) {N N₂ : Z.Opens} (h : N ≤ B.V α)
    (hN : N₂ ≤ N) (m : Fin d) :
    tN B α (hN.trans h) m = (Z.presheaf.map (homOfLE hN).op).hom (tN B α h m) := by
  simp only [tN]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/- English proof (translation)
Introduce `m`. Rewrite using `[tN_res B β h₂ hN, hG m, map_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, tN_res B α h₁ hN]`. Both sides reduce to the same expression.
-/
private lemma isTr_res (B : Blow q i π D d) (α β : B.ι) {N N₂ : Z.Opens} (h₁ : N ≤ B.V α)
    (h₂ : N ≤ B.V β) (hN : N₂ ≤ N) (G : Matrix (Fin d) (Fin d) Γ(Z, N))
    (hG : IsTr B α β h₁ h₂ G) :
    IsTr B α β (hN.trans h₁) (hN.trans h₂) (G.map (Z.presheaf.map (homOfLE hN).op).hom) := by
  intro m
  rw [tN_res B β h₂ hN, hG m, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, tN_res B α h₁ hN]
  rfl

/- English proof (translation)
Introduce `m`. Rewrite using `[hG' m]`. Simplify using `only [hG _, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]`. Conclude with `Finset.sum_comm`.
-/
private lemma isTr_comp (B : Blow q i π D d) (α β γ : B.ι) {N : Z.Opens} (h₁ : N ≤ B.V α)
    (h₂ : N ≤ B.V β) (h₃ : N ≤ B.V γ) (G G' : Matrix (Fin d) (Fin d) Γ(Z, N))
    (hG : IsTr B α β h₁ h₂ G) (hG' : IsTr B β γ h₂ h₃ G') :
    IsTr B α γ h₁ h₃ (G' * G) := by
  intro m
  rw [hG' m]
  simp only [hG _, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

end UpperTheory.Gal.KunnethLefschetz.G.PX

/- English proof (translation)
Introduce `K _ W Z Y q i π D d B α β γ V p M M' h h' x`. Take `⟨U, N, hx, hNa, h₁, h₂, hU, G, hG, hM⟩` from `h x`. Take `⟨U', N', hx', hNa', h₁', h₂', hU', G', hG', hM'⟩` from `h' x`. Establish `hxN : (p ≫ i) x ∈ N` using `hU (Set.mem_univ (⟨x, hx⟩ : (U : Scheme.{0})))`. Establish `hxN' : (p ≫ i) x ∈ N'` using `hU' (Set.mem_univ (⟨x, hx'⟩ : (U' : Scheme.{0})))`.

Take `⟨N₂, hA, hxN₂, hle⟩` from `exists_isAffineOpen_mem_and_subset (U := N ⊓ N') ⟨hxN, hxN'⟩`. Establish `hl₁ : N₂ ≤ N` using `fun y hy => (hle hy).1`. Establish `hl₂ : N₂ ≤ N'` using `fun y hy => (hle hy).2`. Set `U₂ : V.Opens` to `U ⊓ U' ⊓ (p ≫ i) ⁻¹ᵁ N₂`. Establish `hUl : U₂ ≤ U` using `fun y hy => hy.1.1`.

Establish `hUl' : U₂ ≤ U'` using `fun y hy => hy.1.2`. Establish `hU₂ : ⊤ ≤ (U₂.ι ≫ p ≫ i) ⁻¹ᵁ N₂`. Introduce `y _`. Conclude with `y.2.2`. Use `⟨U₂, N₂, ⟨⟨hx, hx'⟩, hxN₂⟩, hA, hl₁.trans h₁, hl₂.trans h₂', hU₂, G'.map (Z.presheaf.map (homOfLE hl₂).op).hom * G.map (Z.presheaf.map (homOfLE hl₁).op).hom, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `isTr_comp B α β γ _ (hl₁.trans h₂) _ _ _ (isTr_res B α β h₁ h₂ hl₁ G hG) (isTr_res B β γ h₁' h₂' hl₂ G' hG')`. Rewrite using `[Matrix.map_mul, Matrix.map_mul]`. Use `congr 1`. Use extensionality with `a b`. Conclude with `restr_sec (p ≫ i) hl₂ hUl' hU' hU₂ _ _ (congrFun (congrFun hM' a) b)`.

Use extensionality with `a b`. Conclude with `restr_sec (p ≫ i) hl₁ hUl hU hU₂ _ _ (congrFun (congrFun hM a) b)`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.G.PX.locMatComp :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β γ : B.ι) {V : Scheme.{0}} (p : V ⟶ W) (M M' : Matrix (Fin d) (Fin d) Γ(V, ⊤)), LocMat B α β p M → LocMat B β γ p M' → LocMat B α γ p (M' * M) := by
  intro K _ W Z Y q i π D d B α β γ V p M M' h h' x
  obtain ⟨U, N, hx, hNa, h₁, h₂, hU, G, hG, hM⟩ := h x
  obtain ⟨U', N', hx', hNa', h₁', h₂', hU', G', hG', hM'⟩ := h' x
  have hxN : (p ≫ i) x ∈ N := hU (Set.mem_univ (⟨x, hx⟩ : (U : Scheme.{0})))
  have hxN' : (p ≫ i) x ∈ N' := hU' (Set.mem_univ (⟨x, hx'⟩ : (U' : Scheme.{0})))
  obtain ⟨N₂, hA, hxN₂, hle⟩ := exists_isAffineOpen_mem_and_subset (U := N ⊓ N') ⟨hxN, hxN'⟩
  have hl₁ : N₂ ≤ N := fun y hy => (hle hy).1
  have hl₂ : N₂ ≤ N' := fun y hy => (hle hy).2
  let U₂ : V.Opens := U ⊓ U' ⊓ (p ≫ i) ⁻¹ᵁ N₂
  have hUl : U₂ ≤ U := fun y hy => hy.1.1
  have hUl' : U₂ ≤ U' := fun y hy => hy.1.2
  have hU₂ : ⊤ ≤ (U₂.ι ≫ p ≫ i) ⁻¹ᵁ N₂ := by
    intro y _
    exact y.2.2
  refine ⟨U₂, N₂, ⟨⟨hx, hx'⟩, hxN₂⟩, hA, hl₁.trans h₁, hl₂.trans h₂', hU₂,
    G'.map (Z.presheaf.map (homOfLE hl₂).op).hom * G.map (Z.presheaf.map (homOfLE hl₁).op).hom,
    ?_, ?_⟩
  · exact isTr_comp B α β γ _ (hl₁.trans h₂) _ _ _ (isTr_res B α β h₁ h₂ hl₁ G hG)
      (isTr_res B β γ h₁' h₂' hl₂ G' hG')
  · rw [Matrix.map_mul, Matrix.map_mul]
    congr 1
    · ext a b
      exact restr_sec (p ≫ i) hl₂ hUl' hU' hU₂ _ _ (congrFun (congrFun hM' a) b)
    · ext a b
      exact restr_sec (p ≫ i) hl₁ hUl hU hU₂ _ _ (congrFun (congrFun hM a) b)
