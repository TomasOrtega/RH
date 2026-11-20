import Mathlib
import Formalism.HermitianLattices.StatementMass
import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic

noncomputable section

namespace Formalism.MainNotions.J

open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

section Transport

variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

def latMap (φ : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V) : Submodule (𝓞 K) V' :=
  M.map ((φ : V →ₗ[K] V').restrictScalars (𝓞 K))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Simplify using `using hx`. Introduce `h`. Conclude with `⟨φ.symm y, h, by simp⟩`.
-/
theorem mem_tr (φ : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V) (y : V') : y ∈ latMap φ M ↔ φ.symm y ∈ M := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨φ.symm y, h, by simp⟩

/- English proof (translation)
Use extensionality with `x`. Simplify using `[mem_tr]`.
-/
theorem tr_symm_tr (φ : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V) : latMap φ.symm (latMap φ M) = M := by
  ext x; simp [mem_tr]

/- English proof (translation)
Use extensionality with `x`. Simplify using `[mem_tr]`.
-/
theorem tr_tr_symm (φ : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V') : latMap φ (latMap φ.symm M) = M := by
  ext x; simp [mem_tr]

/- English proof (translation)
Introduce `a b h` and use `by rw [← tr_symm_tr φ a, h, tr_symm_tr]`.
-/
theorem tr_injective (φ : V ≃ₗ[K] V') : Function.Injective (latMap (K := K) φ) := fun a b h => by
  rw [← tr_symm_tr φ a, h, tr_symm_tr]

def cj (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) : V' ≃ₗ[K] V' := (φ.symm.trans g).trans φ

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cj_apply (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) (y : V') : cj φ g y = φ (g (φ.symm y)) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cj_symm_apply (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) (y : V') :
    (cj φ g).symm y = φ (g.symm (φ.symm y)) := rfl

/- English proof (translation)
Use extensionality with `x`. Simplify using `[cj_apply]`.
-/
theorem cj_symm_cj (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) : cj φ.symm (cj φ g) = g := by
  ext x; simp [cj_apply]

/- English proof (translation)
Use extensionality with `x`. Simplify using `[cj_apply]`.
-/
theorem cj_cj_symm (φ : V ≃ₗ[K] V') (g : V' ≃ₗ[K] V') : cj φ (cj φ.symm g) = g := by
  ext x; simp [cj_apply]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Simplify using `using hx`. Introduce `h`. Conclude with `⟨g.symm y, h, by simp⟩`.
-/
theorem mem_gmap (g : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) (y : V) : y ∈ gmap g M ↔ g.symm y ∈ M := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨g.symm y, h, by simp⟩

/- English proof (translation)
Use extensionality with `y`. Simplify using `[mem_gmap, mem_tr, cj_symm_apply]`.
-/
theorem gmap_cj (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) :
    gmap (cj φ g) (latMap φ M) = latMap φ (gmap g M) := by
  ext y
  simp [mem_gmap, mem_tr, cj_symm_apply]

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[mem_tr]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, h⟩`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations.

Rewrite `h` using `[mem_tr]`. Establish `e : φ.symm (s • y) = s • φ.symm y`. Rewrite using `[← algebraMap_smul K s y, map_smul, algebraMap_smul]`. Rewrite `h` using `[e]`. Then use the resulting hypothesis. Introduce and unpack `⟨s, hs, h⟩`.

Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_tr]`. Establish `e : φ.symm (s • y) = s • φ.symm y`. Rewrite using `[← algebraMap_smul K s y, map_smul, algebraMap_smul]`. Rewrite using `[e]` and apply the resulting hypothesis.
-/
theorem loc_tr (φ : V ≃ₗ[K] V') (p : Ideal (𝓞 K)) (M : Submodule (𝓞 K) V) :
    loc (K := K) p (latMap φ M) = latMap φ (loc (K := K) p M) := by
  ext y
  rw [mem_tr]
  constructor
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    rw [mem_tr] at h
    have e : φ.symm (s • y) = s • φ.symm y := by
      rw [← algebraMap_smul K s y, map_smul, algebraMap_smul]
    rwa [e] at h
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    rw [mem_tr]
    have e : φ.symm (s • y) = s • φ.symm y := by
      rw [← algebraMap_smul K s y, map_smul, algebraMap_smul]
    rwa [e]

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

/- English proof (translation)
Introduce `x y` and use `by rw [← hφ]; simp`.
-/
theorem isom_symm {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) :
    ∀ x y, h (φ.symm x) (φ.symm y) = h' x y := fun x y => by
  rw [← hφ]; simp

/- English proof (translation)
Introduce `x y`. Rewrite using `[cj_apply, cj_apply, hφ, hg, isom_symm hφ]`.
-/
theorem cj_mem_isom {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) {g : V ≃ₗ[K] V}
    (hg : g ∈ isom h) : cj φ g ∈ isom h' := by
  intro x y
  rw [cj_apply, cj_apply, hφ, hg, isom_symm hφ]

/- English proof (translation)
The claim follows from `hM.fg.map _ span_eq_top := by have h1 : ((latMap φ M : Submodule (𝓞 K) V') : Set V') = (φ : V →ₗ[K] V') '' (M : Set V) := rfl rw [h1, Submodule.span_image, hM.span_eq_top, Submodule.map_top, LinearEquiv.range]`.
-/
theorem isLattice_tr (φ : V ≃ₗ[K] V') {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) :
    Submodule.IsLattice K (latMap φ M) where
  fg := hM.fg.map _
  span_eq_top := by
    have h1 : ((latMap φ M : Submodule (𝓞 K) V') : Set V') = (φ : V →ₗ[K] V') '' (M : Set V) := rfl
    rw [h1, Submodule.span_image, hM.span_eq_top, Submodule.map_top, LinearEquiv.range]

/- English proof (translation)
Use `⟨isLattice_tr φ hM.1, fun p hp => ?_⟩` and prove the remaining obligations. Take `⟨g, hg, e⟩` from `hM.2 p hp`. Conclude with `⟨cj φ g, cj_mem_isom hφ hg, by rw [loc_tr, gmap_cj, e, loc_tr]⟩`.
-/
theorem genus_tr {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) {L M : Submodule (𝓞 K) V}
    (hM : M ∈ genus h L) : latMap φ M ∈ genus h' (latMap φ L) := by
  refine ⟨isLattice_tr φ hM.1, fun p hp => ?_⟩
  obtain ⟨g, hg, e⟩ := hM.2 p hp
  exact ⟨cj φ g, cj_mem_isom hφ hg, by rw [loc_tr, gmap_cj, e, loc_tr]⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `M hM`. Take `⟨N, hN, rfl⟩` from `Finset.mem_map.1 hM`. Conclude with `genus_tr hφ (hs.1 N hN)`. Introduce `M hM`.

Establish `hM' : latMap φ.symm M ∈ genus h L`. Use `genus_tr (isom_symm hφ) hM` as an intermediate fact. Rewrite `this` using `[tr_symm_tr]`. Then use the resulting hypothesis. Take `⟨N, ⟨hN, g, hg, e⟩, huniq⟩` from `hs.2 _ hM'`. Use `⟨latMap φ N, ⟨Finset.mem_map.2 ⟨N, hN, rfl⟩, cj φ g, cj_mem_isom hφ hg, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[gmap_cj, e, tr_tr_symm]`. Introduce and unpack `N' ⟨hN', g', hg', e'⟩`. Take `⟨N₀, hN₀, rfl⟩` from `Finset.mem_map.1 hN'`. Establish `: N₀ = N`. Use `huniq N₀ ⟨hN₀, cj φ.symm g', cj_mem_isom (isom_symm hφ) hg', ?_⟩` and prove the remaining obligations.

Establish `h2` using `gmap_cj φ.symm g' (latMap φ N₀)`. Rewrite `h2` using `[tr_symm_tr]`. Express the relevant statement in the definitionally equal form `gmap g' (latMap φ N₀) = M at e'`. Rewrite using `[h2, e']`. Rewrite using `[this]`.

Both sides reduce to the same expression.
-/
theorem classReps_tr {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) {L : Submodule (𝓞 K) V}
    {s : Finset (Submodule (𝓞 K) V)} (hs : IsClassReps h L s) :
    IsClassReps h' (latMap φ L) (s.map ⟨latMap φ, tr_injective φ⟩) := by
  constructor
  · intro M hM
    obtain ⟨N, hN, rfl⟩ := Finset.mem_map.1 hM
    exact genus_tr hφ (hs.1 N hN)
  · intro M hM
    have hM' : latMap φ.symm M ∈ genus h L := by
      have := genus_tr (isom_symm hφ) hM
      rwa [tr_symm_tr] at this
    obtain ⟨N, ⟨hN, g, hg, e⟩, huniq⟩ := hs.2 _ hM'
    refine ⟨latMap φ N, ⟨Finset.mem_map.2 ⟨N, hN, rfl⟩, cj φ g, cj_mem_isom hφ hg, ?_⟩, ?_⟩
    · rw [gmap_cj, e, tr_tr_symm]
    · rintro N' ⟨hN', g', hg', e'⟩
      obtain ⟨N₀, hN₀, rfl⟩ := Finset.mem_map.1 hN'
      have : N₀ = N := by
        refine huniq N₀ ⟨hN₀, cj φ.symm g', cj_mem_isom (isom_symm hφ) hg', ?_⟩
        have h2 := gmap_cj φ.symm g' (latMap φ N₀)
        rw [tr_symm_tr] at h2
        change gmap g' (latMap φ N₀) = M at e'
        rw [h2, e']
      rw [this]; rfl

/- English proof (translation)
Establish `a1 : ∀ g : autL h M, gmap (cj φ g.1) (latMap φ M) = latMap φ M` using `fun g => by`. Rewrite using `[gmap_cj, g.2.2]`. Establish `a2 : ∀ g : autL h' (latMap φ M), gmap (cj φ.symm g.1) M = M` using `fun g => by`. Establish `h2` using `gmap_cj φ.symm g.1 (latMap φ M)`. Rewrite `h2` using `[tr_symm_tr]`.

Rewrite using `[h2, g.2.2, tr_symm_tr]`. Conclude with `(Nat.card_congr ⟨fun g => ⟨cj φ g.1, cj_mem_isom hφ g.2.1, a1 g⟩, fun g => ⟨cj φ.symm g.1, cj_mem_isom (isom_symm hφ) g.2.1, a2 g⟩, fun g => Subtype.ext (cj_symm_cj φ g.1), fun g => Subtype.ext (cj_cj_symm φ g.1)⟩).symm`.
-/
theorem card_autL_tr {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) (M : Submodule (𝓞 K) V) :
    Nat.card (autL h' (latMap φ M)) = Nat.card (autL h M) := by
  have a1 : ∀ g : autL h M, gmap (cj φ g.1) (latMap φ M) = latMap φ M := fun g => by
    rw [gmap_cj, g.2.2]
  have a2 : ∀ g : autL h' (latMap φ M), gmap (cj φ.symm g.1) M = M := fun g => by
    have h2 := gmap_cj φ.symm g.1 (latMap φ M)
    rw [tr_symm_tr] at h2
    rw [h2, g.2.2, tr_symm_tr]
  exact (Nat.card_congr ⟨fun g => ⟨cj φ g.1, cj_mem_isom hφ g.2.1, a1 g⟩,
    fun g => ⟨cj φ.symm g.1, cj_mem_isom (isom_symm hφ) g.2.1, a2 g⟩,
    fun g => Subtype.ext (cj_symm_cj φ g.1), fun g => Subtype.ext (cj_cj_symm φ g.1)⟩).symm

/- English proof (translation)
Rewrite using `[massBasic_mass_eq h L ⟨s, hs⟩]`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[massBasic_sum_cast, massBasic_sum_cast]`. Conclude with `latLiftIndep K V h L _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) _ _ (Exists.choose_spec (⟨s, hs⟩ : ∃ s, IsClassReps h L s)) hs`.
-/
theorem mass_eq_sum (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    (s : Finset (Submodule (𝓞 K) V)) (hs : IsClassReps h L s) :
    mass h L = ∑ M ∈ s, ((Nat.card (autL h M) : ℕ) : ℝ)⁻¹ := by
  rw [massBasic_mass_eq h L ⟨s, hs⟩]
  apply Complex.ofReal_injective
  rw [massBasic_sum_cast, massBasic_sum_cast]
  exact latLiftIndep K V h L _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) _ _
    (Exists.choose_spec (⟨s, hs⟩ : ∃ s, IsClassReps h L s)) hs

/- English proof (translation)
Distinguish the cases in `hs : ∃ s, IsClassReps h L s`. Take `⟨s, hs⟩` from `hs`. Rewrite using `[mass_eq_sum h L s hs, mass_eq_sum h' _ _ (classReps_tr hφ hs), Finset.sum_map]`. Conclude with `Finset.sum_congr rfl fun M _ => by`. Rewrite using `[Function.Embedding.coeFn_mk, card_autL_tr hφ]`.

Establish `hs' : ¬ ∃ s, IsClassReps h' (latMap φ L) s`. Introduce and unpack `⟨s, hs'⟩`. Apply `hs` to reduce the goal to its premises. Use `classReps_tr (isom_symm hφ) hs'` as an intermediate fact. Rewrite `this` using `[tr_symm_tr]`.

Conclude with `⟨_, this⟩`. Unfold `mass`. Rewrite using `[dif_neg hs, dif_neg hs']`.
-/
theorem mass_tr {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) (L : Submodule (𝓞 K) V) :
    mass h' (latMap φ L) = mass h L := by
  by_cases hs : ∃ s, IsClassReps h L s
  · obtain ⟨s, hs⟩ := hs
    rw [mass_eq_sum h L s hs, mass_eq_sum h' _ _ (classReps_tr hφ hs), Finset.sum_map]
    exact Finset.sum_congr rfl fun M _ => by
      rw [Function.Embedding.coeFn_mk, card_autL_tr hφ]
  · have hs' : ¬ ∃ s, IsClassReps h' (latMap φ L) s := by
      rintro ⟨s, hs'⟩
      apply hs
      have := classReps_tr (isom_symm hφ) hs'
      rw [tr_symm_tr] at this
      exact ⟨_, this⟩
    unfold mass
    rw [dif_neg hs, dif_neg hs']

/- English proof (translation)
Take `⟨e, he1, he2, rfl, he⟩` from `hL`. Take `⟨e', he1', he2', rfl, he'⟩` from `hL'`. Set `b : Module.Basis (Fin n) K V` to `Module.Basis.mk he1 he2.ge`. Set `b' : Module.Basis (Fin n) K V'` to `Module.Basis.mk he1' he2'.ge`. Set `φ : V ≃ₗ[K] V'` to `b.equiv b' (Equiv.refl _)`.

Establish `hφe : ∀ i, φ (e i) = e' i` using `fun i => by`. Use `b.equiv_apply i b' (Equiv.refl _)` as an intermediate fact. Simplify `this` using `[b, b', φ]`. Establish `hφ : ∀ x y, h' (φ x) (φ y) = h x y`. Introduce `x y`.

Establish `hx` using `b.sum_repr x`. Establish `hy` using `b.sum_repr y`. Rewrite using `[← hx, ← hy]`. Simplify using `only [map_sum, map_smul, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, b, Module.Basis.mk_apply, hφe, he, he']`. Rewrite using `[← mass_tr hφ]`.

Use `congr 1`. Unfold `latMap`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Use `congr 2`. Use function extensionality and compare the values at `i`.

Conclude with `hφe i`.
-/
theorem mass_ortho_eq {n : ℕ} {L : Submodule (𝓞 K) V} {L' : Submodule (𝓞 K) V'}
    (hL : IsOrthoLattice h L n) (hL' : IsOrthoLattice h' L' n) : mass h L = mass h' L' := by
  obtain ⟨e, he1, he2, rfl, he⟩ := hL
  obtain ⟨e', he1', he2', rfl, he'⟩ := hL'
  let b : Module.Basis (Fin n) K V := Module.Basis.mk he1 he2.ge
  let b' : Module.Basis (Fin n) K V' := Module.Basis.mk he1' he2'.ge
  let φ : V ≃ₗ[K] V' := b.equiv b' (Equiv.refl _)
  have hφe : ∀ i, φ (e i) = e' i := fun i => by
    have := b.equiv_apply i b' (Equiv.refl _)
    simpa [b, b', φ] using this
  have hφ : ∀ x y, h' (φ x) (φ y) = h x y := by
    intro x y
    have hx := b.sum_repr x
    have hy := b.sum_repr y
    rw [← hx, ← hy]
    simp only [map_sum, map_smul, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, b,
      Module.Basis.mk_apply, hφe, he, he']
  rw [← mass_tr hφ]
  congr 1
  unfold latMap
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext i
  exact hφe i

end Transport

end Formalism.MainNotions.J

end
