import Development.EtaleCohomology.KummerTheory.FinalTheorems

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

/- English proof (translation)
Set `𝒰` to `X.affineCover`. Establish `h2 : IsOpenImmersion (𝒰.f (𝒰.idx x))` using `inferInstance`. Conclude with `⟨_, 𝒰.f (𝒰.idx x), h2, 𝒰.covers x⟩`.
-/
lemma lk_aff (X : Scheme.{0}) (x : X) :
    ∃ (B : CommRingCat.{0}) (f : Spec B ⟶ X), IsOpenImmersion f ∧ x ∈ Set.range f :=
  by
  let 𝒰 := X.affineCover
  have h2 : IsOpenImmersion (𝒰.f (𝒰.idx x)) := inferInstance
  exact ⟨_, 𝒰.f (𝒰.idx x), h2, 𝒰.covers x⟩

/- English proof (translation)
The claim follows from `(HasRingHomProperty.Spec_iff (P := @Etale)).mpr h`.
-/
lemma lk_etale {A B : CommRingCat.{0}} (f : A ⟶ B) (h : f.hom.Etale) : Etale (Spec.map f) :=
  (HasRingHomProperty.Spec_iff (P := @Etale)).mpr h

/- English proof (translation)
Use `Fintype.ofFinite ι` as an intermediate fact. It suffices to establish `H : ∀ s : Finset ι, ∃ (k : J) (f : j₀ ⟶ k), ∀ t ∈ s, P t f by`. Take `⟨k, f, hf⟩` from `H Finset.univ`. Conclude with `⟨k, f, fun t => hf t (Finset.mem_univ t)⟩`. Introduce `s`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨j₀, 𝟙 _, by simp⟩`. Consider the case `insert a s _ ih`. Take `⟨k, f, hf⟩` from `ih`. Take `⟨k', f', hf'⟩` from `h a`.

Take `⟨k'', g, g', hg⟩` from `IsFiltered.span f f'`. Use `⟨k'', f ≫ g, fun t ht => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 ht with rfl | ht` into its components or cases. Rewrite using `[hg]`. Conclude with `hP _ _ _ hf'`.

Conclude with `hP _ _ _ (hf t ht)`.
-/
lemma lk_fin {J : Type} [SmallCategory J] [IsFiltered J] (j₀ : J) {ι : Type} [Finite ι]
    (P : ι → ∀ {k : J}, (j₀ ⟶ k) → Prop)
    (hP : ∀ t {k k' : J} (f : j₀ ⟶ k) (g : k ⟶ k'), P t f → P t (f ≫ g))
    (h : ∀ t, ∃ (k : J) (f : j₀ ⟶ k), P t f) : ∃ (k : J) (f : j₀ ⟶ k), ∀ t, P t f := by
  classical
  have := Fintype.ofFinite ι
  suffices H : ∀ s : Finset ι, ∃ (k : J) (f : j₀ ⟶ k), ∀ t ∈ s, P t f by
    obtain ⟨k, f, hf⟩ := H Finset.univ
    exact ⟨k, f, fun t => hf t (Finset.mem_univ t)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨j₀, 𝟙 _, by simp⟩
  | insert a s _ ih =>
    obtain ⟨k, f, hf⟩ := ih
    obtain ⟨k', f', hf'⟩ := h a
    obtain ⟨k'', g, g', hg⟩ := IsFiltered.span f f'
    refine ⟨k'', f ≫ g, fun t ht => ?_⟩
    rcases Finset.mem_insert.1 ht with rfl | ht
    · rw [hg]; exact hP _ _ _ hf'
    · exact hP _ _ _ (hf t ht)

/- English proof (translation)
Simplify using `only [spMap, CommRingCat.ofHom_hom]`. Rewrite using `[Spec.map_comp, Functor.map_comp, pull_comp]`.
-/
lemma lk_pull_spMap {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) {n i : ℤ} {q : ℕ} (x : Ht q (sp A) n i) :
    pull _ (spMap (f ≫ g).hom) _ _ x = pull _ (spMap g.hom) _ _ (pull _ (spMap f.hom) _ _ x) := by
  simp only [spMap, CommRingCat.ofHom_hom]
  rw [Spec.map_comp, Functor.map_comp, pull_comp]

/- English proof (translation)
Introduce `hA hB q _ X R p hq i r c M N n hiso U u y hy`. Take `⟨B, ι, hι, b, hb⟩` from `lk_aff U.left u`. Take `⟨J, _, _, D, cc, hc, w, hSH, hw⟩` from `hS B b`. Take `⟨j₀⟩` from `IsFiltered.nonempty (C := J)`. Set `φ : Spec cc.pt ⟶ U.left` to `Spec.map (w.app j₀ ≫ cc.ι.app j₀) ≫ ι`.

Set `V' : Over (Spec R)` to `Over.mk (Spec.map (Spec.preimage (φ ≫ U.hom)))`. Set `g' : V' ⟶ U` to `Over.homMk φ (Spec.map_preimage (φ ≫ U.hom)).symm`. Establish `h1` using `hL hA q p i r c M n g' y`. Rewrite `h1` using `[hy, map_zero]`. Establish `h2` using `(hiso cc.pt (Spec.preimage (φ ≫ U.hom)) hSH).1 _ h1.symm`.

Set `ψ : Spec (D.obj j₀) ⟶ U.left` to `Spec.map (w.app j₀) ≫ ι`. Establish `hunit : ∀ j, IsUnit ((q : ℕ) : D.obj j)`. Introduce `j`. Use `hq.map (Spec.preimage (Spec.map (w.app j) ≫ ι ≫ U.hom)).hom` as an intermediate fact. Simplify using `using this`.

Set `z : ∀ t : (Σ a : Fin (M + 1), Fin (r a)), Ht q (sp (D.obj j₀)) (n - ((t.1 : ℕ) : ℤ)) 0` to `fun t => N • pull _ (sch.map ψ) _ _ (y t.1 t.2)`. Establish `e1 : spMap (cc.ι.app j₀).hom ≫ sch.map ψ = sch.map φ`. Simplify using `only [spMap, CommRingCat.ofHom_hom, ψ, φ, ← Functor.map_comp, Spec.map_comp, Category.assoc]`. Establish `hz : ∀ t, pull _ (spMap (cc.ι.app j₀).hom) _ _ (z t) = 0`. Introduce `t`.

Use `congrFun (congrFun h2 t.1) t.2` as an intermediate fact. Simplify using `only [Pi.smul_apply] at this`. Simplify using `only [z, map_nsmul]`. Rewrite using `[← pull_comp, e1]`. Conclude with `this`.

Establish `hk : ∀ t, ∃ (k : J) (f : j₀ ⟶ k), pull _ (spMap (D.map f).hom) _ _ (z t) = 0` using `fun t => (hB q D cc hc _ _).2 j₀ (z t) (hunit j₀) (hz t)`. Take `⟨k, F, hF⟩` from `lk_fin j₀ (fun t {k} (f : j₀ ⟶ k) => pull _ (spMap (D.map f).hom) _ _ (z t) = 0) (fun t k k' f g hf => by simp only [Functor.map_comp, lk_pull_spMap, hf, map_zero]) hk`. Set `gl : Spec (D.obj k) ⟶ U.left` to `Spec.map (w.app k) ≫ ι`. Establish `hwk : w.app k = w.app j₀ ≫ D.map F` using `by simpa using (w.naturality F)`. Use `lk_etale _ (hw k).1` as an intermediate fact.

Take `⟨𝔮, h𝔮⟩` from `(hw k).2`. Use `⟨Over.mk (gl ≫ U.hom), Over.homMk gl rfl, ⟨?_, 𝔮, ?_⟩, fun a s => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Etale gl`. Use `infer_instance`. Express the relevant statement in the definitionally equal form `ι (Spec.map (w.app k) 𝔮) = u`.

Rewrite using `[← hb]`. Use `congr 1`. Conclude with `PrimeSpectrum.ext h𝔮`. Use `hF ⟨a, s⟩` as an intermediate fact. Establish `e2 : sch.map gl = spMap (D.map F).hom ≫ sch.map ψ`.

Simplify using `only [gl, ψ, hwk, spMap, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Functor.map_comp]`. Express the relevant statement in the definitionally equal form `N • pull _ (sch.map gl) _ _ (y a s) = 0`. Rewrite using `[e2, pull_comp, ← map_nsmul]`. Conclude with `this`.
-/
theorem locKer_of (hS : StrictHenselization) (hL : LhNat) : LocKer := by
  intro hA hB q _ X R p hq i r c M N n hiso U u y hy
  obtain ⟨B, ι, hι, b, hb⟩ := lk_aff U.left u
  obtain ⟨J, _, _, D, cc, hc, w, hSH, hw⟩ := hS B b
  obtain ⟨j₀⟩ := IsFiltered.nonempty (C := J)
  let φ : Spec cc.pt ⟶ U.left := Spec.map (w.app j₀ ≫ cc.ι.app j₀) ≫ ι
  let V' : Over (Spec R) := Over.mk (Spec.map (Spec.preimage (φ ≫ U.hom)))
  let g' : V' ⟶ U := Over.homMk φ (Spec.map_preimage (φ ≫ U.hom)).symm
  have h1 := hL hA q p i r c M n g' y
  rw [hy, map_zero] at h1
  have h2 := (hiso cc.pt (Spec.preimage (φ ≫ U.hom)) hSH).1 _ h1.symm
  let ψ : Spec (D.obj j₀) ⟶ U.left := Spec.map (w.app j₀) ≫ ι
  have hunit : ∀ j, IsUnit ((q : ℕ) : D.obj j) := by
    intro j
    have := hq.map (Spec.preimage (Spec.map (w.app j) ≫ ι ≫ U.hom)).hom
    simpa using this
  let z : ∀ t : (Σ a : Fin (M + 1), Fin (r a)), Ht q (sp (D.obj j₀)) (n - ((t.1 : ℕ) : ℤ)) 0 :=
    fun t => N • pull _ (sch.map ψ) _ _ (y t.1 t.2)
  have e1 : spMap (cc.ι.app j₀).hom ≫ sch.map ψ = sch.map φ := by
    simp only [spMap, CommRingCat.ofHom_hom, ψ, φ, ← Functor.map_comp, Spec.map_comp, Category.assoc]
  have hz : ∀ t, pull _ (spMap (cc.ι.app j₀).hom) _ _ (z t) = 0 := by
    intro t
    have := congrFun (congrFun h2 t.1) t.2
    simp only [Pi.smul_apply] at this
    simp only [z, map_nsmul]
    rw [← pull_comp, e1]
    exact this
  have hk : ∀ t, ∃ (k : J) (f : j₀ ⟶ k), pull _ (spMap (D.map f).hom) _ _ (z t) = 0 := fun t =>
    (hB q D cc hc _ _).2 j₀ (z t) (hunit j₀) (hz t)
  obtain ⟨k, F, hF⟩ := lk_fin j₀ (fun t {k} (f : j₀ ⟶ k) => pull _ (spMap (D.map f).hom) _ _ (z t) = 0)
    (fun t k k' f g hf => by simp only [Functor.map_comp, lk_pull_spMap, hf, map_zero]) hk
  let gl : Spec (D.obj k) ⟶ U.left := Spec.map (w.app k) ≫ ι
  have hwk : w.app k = w.app j₀ ≫ D.map F := by simpa using (w.naturality F)
  have := lk_etale _ (hw k).1
  obtain ⟨𝔮, h𝔮⟩ := (hw k).2
  refine ⟨Over.mk (gl ≫ U.hom), Over.homMk gl rfl, ⟨?_, 𝔮, ?_⟩, fun a s => ?_⟩
  · change Etale gl; infer_instance
  · change ι (Spec.map (w.app k) 𝔮) = u
    rw [← hb]; congr 1; exact PrimeSpectrum.ext h𝔮
  · have := hF ⟨a, s⟩
    have e2 : sch.map gl = spMap (D.map F).hom ≫ sch.map ψ := by
      simp only [gl, ψ, hwk, spMap, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Functor.map_comp]
    change N • pull _ (sch.map gl) _ _ (y a s) = 0
    rw [e2, pull_comp, ← map_nsmul]
    exact this

end LateralTheory.KummerTheory.LHCut
