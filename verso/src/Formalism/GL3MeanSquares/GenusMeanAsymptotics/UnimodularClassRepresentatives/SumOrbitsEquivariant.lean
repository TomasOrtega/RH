import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsVecOfHermRep
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteRepSetOfOrtho
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsClassReps

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

def fibG (S : VecSplit h h') (L : Submodule (𝓞 K) V) (Λ' : Submodule (𝓞 K) V') :
    Set (Submodule (𝓞 K) V) :=
  {Λ | Λ ∈ Formalism.HermitianLatticesTheory.genus h L ∧ S.x₀ ∈ Λ ∧ S.cut Λ = Λ'}

def IsFibReps (S : VecSplit h h') (L : Submodule (𝓞 K) V) (s' : Finset (Submodule (𝓞 K) V')) :
    Prop :=
  (∀ Λ' ∈ s', (fibG S L Λ').Nonempty) ∧
  ∀ Λ' : Submodule (𝓞 K) V', (fibG S L Λ').Nonempty →
    ∃! Λ₀, Λ₀ ∈ s' ∧ ∃ g ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g Λ₀ = Λ'

namespace StabilizerLattices

open SplitBAux

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨hΛ.1, hΛ.2.1, rfl⟩, Prod.ext (by rw [← hΛ.2.2]; exact inf_perpO S Λ) rfl⟩`.
-/
theorem pair_mem_of_fibG (S : VecSplit h h') {L : Submodule (𝓞 K) V} {Λ' : Submodule (𝓞 K) V'}
    {Λ : Submodule (𝓞 K) V} (hΛ : Λ ∈ fibG S L Λ') :
    (Λ, S.x₀) ∈ pairs h L (h S.x₀ S.x₀) ∧ proj h (Λ, S.x₀) = (emb S Λ', S.x₀) :=
  ⟨⟨hΛ.1, hΛ.2.1, rfl⟩, Prod.ext (by rw [← hΛ.2.2]; exact inf_perpO S Λ) rfl⟩

/- English proof (translation)
Take `⟨Λ, x⟩` from `p`. Take `⟨e1, e2⟩` from `Prod.ext_iff.mp e`. Express the relevant statement in the definitionally equal form `Λ ⊓ perpO h x = emb S Λ' at e1`. Express the relevant statement in the definitionally equal form `x = S.x₀ at e2`. Substitute `e2` using the available equality.

Rewrite `e1` using `[inf_perpO]`. Conclude with `⟨⟨hp.1, hp.2.1, emb_injective S e1⟩, rfl⟩`.
-/
theorem fibG_of_pair_mem (S : VecSplit h h') {L : Submodule (𝓞 K) V} {Λ' : Submodule (𝓞 K) V'}
    {p : Submodule (𝓞 K) V × V} (hp : p ∈ pairs h L (h S.x₀ S.x₀))
    (e : proj h p = (emb S Λ', S.x₀)) : p.1 ∈ fibG S L Λ' ∧ p.2 = S.x₀ := by
  obtain ⟨Λ, x⟩ := p
  obtain ⟨e1, e2⟩ := Prod.ext_iff.mp e
  change Λ ⊓ perpO h x = emb S Λ' at e1
  change x = S.x₀ at e2
  subst e2
  rw [inf_perpO] at e1
  exact ⟨⟨hp.1, hp.2.1, emb_injective S e1⟩, rfl⟩

/- English proof (translation)
Distinguish the cases in `hp : p ∈ pairs h L (h S.x₀ S.x₀)`. Establish `hne : p.2 ≠ 0`. Introduce `h0`. Use `hp.2.2` as an intermediate fact. Rewrite `this` using `[h0]`.

Conclude with `S.hx₀ (by simpa using this.symm)`. Take `⟨g, hg, hgx⟩` from `exists_isom_map_of_eq hK hs hd hne hp.2.2`. Use `⟨⟨g, hg⟩, fun _ => ⟨Prod.ext rfl hgx, OrbitRepresentatives.gmap_mem_genus hs hp.1 hg, ?_, rfl⟩⟩` and prove the remaining obligations. Rewrite using `[← hgx]`. Conclude with `apply_mem_gmap g hp.2.1`.

Conclude with `⟨1, fun h => absurd h hp⟩`.
-/
theorem exists_move (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') (L : Submodule (𝓞 K) V) (p : Submodule (𝓞 K) V × V) :
    ∃ g : Formalism.HermitianLatticesTheory.isom h, p ∈ pairs h L (h S.x₀ S.x₀) →
      g • p = (Formalism.HermitianLatticesTheory.gmap g.1 p.1, S.x₀) ∧
      Formalism.HermitianLatticesTheory.gmap g.1 p.1 ∈ fibG S L (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1)) := by
  by_cases hp : p ∈ pairs h L (h S.x₀ S.x₀)
  · have hne : p.2 ≠ 0 := by
      intro h0
      have := hp.2.2
      rw [h0] at this
      exact S.hx₀ (by simpa using this.symm)
    obtain ⟨g, hg, hgx⟩ := exists_isom_map_of_eq hK hs hd hne hp.2.2
    refine ⟨⟨g, hg⟩, fun _ => ⟨Prod.ext rfl hgx, OrbitRepresentatives.gmap_mem_genus hs hp.1 hg, ?_, rfl⟩⟩
    rw [← hgx]
    exact apply_mem_gmap g hp.2.1
  · exact ⟨1, fun h => absurd h hp⟩

/- English proof (translation)
Use `⟨OrbitRepresentatives.gmap_mem_genus hs hΛ.1 (extOf_mem_isom hs S hg'), ?_, ?_⟩` and prove the remaining obligations. Use `apply_mem_gmap (extOf S g') hΛ.2.1` as an intermediate fact. Rewrite `this` using `[extOf_x₀]`. Then use the resulting hypothesis. Rewrite using `[cut_gmap_extOf, hΛ.2.2]`.
-/
theorem fibG_smul (hs : h.IsSymm) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    {Λ' : Submodule (𝓞 K) V'} {Λ : Submodule (𝓞 K) V} (hΛ : Λ ∈ fibG S L Λ')
    {g' : V' ≃ₗ[K] V'} (hg' : g' ∈ Formalism.HermitianLatticesTheory.isom h') :
    Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ ∈ fibG S L (Formalism.HermitianLatticesTheory.gmap g' Λ') := by
  refine ⟨OrbitRepresentatives.gmap_mem_genus hs hΛ.1 (extOf_mem_isom hs S hg'), ?_, ?_⟩
  · have := apply_mem_gmap (extOf S g') hΛ.2.1
    rwa [extOf_x₀] at this
  · rw [cut_gmap_extOf, hΛ.2.2]

/- English proof (translation)
Take `⟨g, hg⟩` from `exists_move hK hs hd S L p`. Take `⟨hg1, hg2⟩` from `hg hp`. Establish `e : g • proj h p = (emb S (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1)), S.x₀)`. Rewrite using `[← proj_smul, hg1]`. Conclude with `(pair_mem_of_fibG S hg2).2`.

Establish `hlat : Submodule.IsLattice K (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1))` using `isLattice_cut S hg2.1.1`. Establish `f1 : Finite (Formalism.ThetaLiftIndependence.autL h' (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1)))` using `(Formalism.HermitianLatticesTheory.autFinite K V' h' (S.isSymm hs) (trace_pos (S.isTotPosDef hd)) _ hlat).to_subtype`. Establish `f2 : Finite (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) (g • proj h p))`. Rewrite using `[e]`. Conclude with `Finite.of_equiv _ (stabPairEquiv hs S _).symm`.

Establish `f3 : Finite (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) (proj h p))` using `Finite.of_equiv _ (MulAction.stabilizerEquivStabilizer (g := g) (a := proj h p) rfl).symm.toEquiv`. Conclude with `Set.toFinite _`.
-/
theorem finite_stab_proj (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') (L : Submodule (𝓞 K) V) {p : Submodule (𝓞 K) V × V}
    (hp : p ∈ pairs h L (h S.x₀ S.x₀)) :
    (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) (proj h p) : Set (Formalism.HermitianLatticesTheory.isom h)).Finite := by
  obtain ⟨g, hg⟩ := exists_move hK hs hd S L p
  obtain ⟨hg1, hg2⟩ := hg hp
  have e : g • proj h p = (emb S (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1)), S.x₀) := by
    rw [← proj_smul, hg1]
    exact (pair_mem_of_fibG S hg2).2
  have hlat : Submodule.IsLattice K (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1)) := isLattice_cut S hg2.1.1
  have f1 : Finite (Formalism.ThetaLiftIndependence.autL h' (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1))) :=
    (Formalism.HermitianLatticesTheory.autFinite K V' h' (S.isSymm hs) (trace_pos (S.isTotPosDef hd)) _ hlat).to_subtype
  have f2 : Finite (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) (g • proj h p)) := by
    rw [e]
    exact Finite.of_equiv _ (stabPairEquiv hs S _).symm
  have f3 : Finite (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) (proj h p)) :=
    Finite.of_equiv _ (MulAction.stabilizerEquivStabilizer (g := g) (a := proj h p) rfl).symm.toEquiv
  exact Set.toFinite _

end StabilizerLattices

open StabilizerLattices SplitBAux in
/- English proof (translation)
Take `⟨sX, hsX, hX⟩` from `exists_pairReps hs hd hL (h S.x₀ S.x₀)`. Use `choose γ hγ using exists_move hK hs hd S L`. Take `⟨T, hT1, hT2⟩` from `OrbSum.exists_reps_of_cover (G := Formalism.HermitianLatticesTheory.isom h') {Λ' : Submodule (𝓞 K) V' | (fibG S L Λ').Nonempty} (fun g' Λ' ⟨Λ, hΛ⟩ => ⟨_, fibG_smul hs S hΛ g'.2⟩) ((fun p => S.cut (Formalism.HermitianLatticesTheory.gmap (γ p).1 p.1)) '' (sX : Set (Submodule (𝓞 K) …`. Introduce and unpack `_ ⟨p, hp, rfl⟩`. Conclude with `⟨_, (hγ p (hsX p hp)).2⟩)`.

Use the proof step `(by`. Introduce and unpack `Λ' ⟨Λ, hΛ⟩`. Take `⟨t, ⟨ht, k, hk⟩, -⟩` from `hX _ (pair_mem_of_fibG S hΛ).1`. Use `⟨_, ⟨t, ht, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `e : (k * (γ t)⁻¹) • (Formalism.HermitianLatticesTheory.gmap (γ t).1 t.1, S.x₀) = (Λ, S.x₀)`.

Rewrite using `[← (hγ t (hsX t ht)).1, mul_smul, inv_smul_smul, hk]`. Take `⟨e1, e2⟩` from `Prod.ext_iff.mp e`. Use `gmap_res S (k * (γ t)⁻¹).1 (k * (γ t)⁻¹).2 e2 e1` as an intermediate fact. Rewrite `this` using `[hΛ.2.2]`. Conclude with `⟨⟨res S (k * (γ t)⁻¹).1 (k * (γ t)⁻¹).2 e2, res_mem_isom S _ _ _⟩, this⟩)`.

Use `⟨T, hT1, fun Λ' hΛ' => ?_⟩` and prove the remaining obligations. Use `hT2 Λ' hΛ'` as an intermediate fact. Rewrite `this` using `[exists_smul_iff]`. Conclude with `this`.
-/
theorem exists_fibReps (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L)
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) : ∃ s', IsFibReps S L s' := by
  classical
  obtain ⟨sX, hsX, hX⟩ := exists_pairReps hs hd hL (h S.x₀ S.x₀)
  choose γ hγ using exists_move hK hs hd S L
  obtain ⟨T, hT1, hT2⟩ := OrbSum.exists_reps_of_cover (G := Formalism.HermitianLatticesTheory.isom h')
    {Λ' : Submodule (𝓞 K) V' | (fibG S L Λ').Nonempty}
    (fun g' Λ' ⟨Λ, hΛ⟩ => ⟨_, fibG_smul hs S hΛ g'.2⟩)
    ((fun p => S.cut (Formalism.HermitianLatticesTheory.gmap (γ p).1 p.1)) '' (sX : Set (Submodule (𝓞 K) V × V)))
    (sX.finite_toSet.image _)
    (by
      rintro _ ⟨p, hp, rfl⟩
      exact ⟨_, (hγ p (hsX p hp)).2⟩)
    (by
      rintro Λ' ⟨Λ, hΛ⟩
      obtain ⟨t, ⟨ht, k, hk⟩, -⟩ := hX _ (pair_mem_of_fibG S hΛ).1
      refine ⟨_, ⟨t, ht, rfl⟩, ?_⟩
      have e : (k * (γ t)⁻¹) • (Formalism.HermitianLatticesTheory.gmap (γ t).1 t.1, S.x₀) = (Λ, S.x₀) := by
        rw [← (hγ t (hsX t ht)).1, mul_smul, inv_smul_smul, hk]
      obtain ⟨e1, e2⟩ := Prod.ext_iff.mp e
      have := gmap_res S (k * (γ t)⁻¹).1 (k * (γ t)⁻¹).2 e2 e1
      rw [hΛ.2.2] at this
      exact ⟨⟨res S (k * (γ t)⁻¹).1 (k * (γ t)⁻¹).2 e2, res_mem_isom S _ _ _⟩, this⟩)
  refine ⟨T, hT1, fun Λ' hΛ' => ?_⟩
  have := hT2 Λ' hΛ'
  simp_rw [exists_smul_iff] at this
  exact this

open StabilizerLattices SplitBAux in
/- English proof (translation)
Take `⟨sX, hsX, hX⟩` from `exists_pairReps hs hd hL (h S.x₀ S.x₀)`. Establish `hex` using `exists_classReps hs hd hL`. Unfold `repMass`. Rewrite using `[dif_pos hex, ← sum_pairs_eq_rep hs hd (h S.x₀ S.x₀) hex.choose_spec hsX hX]`. Establish `key` using `OrbSum.sum_orbits_on (G := Formalism.HermitianLatticesTheory.isom h) (proj h) proj_smul (pairs h L (h S.x₀ S.x₀)) (proj h '' pairs h L (h S.x₀ S.x₀)) (pairs_stable hs L _) (fun p hp => Set.mem_image_of_mem _ hp) sX (s'.image fun Λ' => (emb S Λ', S.x₀)) hsX (by`.

Introduce `u hu`. Take `⟨Λ', hΛ', rfl⟩` from `Finset.mem_image.mp hu`. Take `⟨Λ, hΛ⟩` from `hs'.1 Λ' hΛ'`. Conclude with `⟨_, (pair_mem_of_fibG S hΛ).1, (pair_mem_of_fibG S hΛ).2⟩)`. Use `hX`.

Use the proof step `(by`. Introduce and unpack `_ ⟨p, hp, rfl⟩`. Take `⟨g, hg⟩` from `exists_move hK hs hd S L p`. Take `⟨hg1, hg2⟩` from `hg hp`. Establish `hgy : g • proj h p = (emb S (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1)), S.x₀)`.

Rewrite using `[← proj_smul, hg1]`. Conclude with `(pair_mem_of_fibG S hg2).2`. Take `⟨Λ₀, ⟨h₀, g', hg', e'⟩, huniq⟩` from `hs'.2 _ ⟨_, hg2⟩`. Use `⟨(emb S Λ₀, S.x₀), ⟨Finset.mem_image.mpr ⟨Λ₀, h₀, rfl⟩, g⁻¹ * ⟨extOf S g', extOf_mem_isom hs S hg'⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `e0 : (⟨extOf S g', extOf_mem_isom hs S hg'⟩ : Formalism.HermitianLatticesTheory.isom h) • (emb S Λ₀, S.x₀) = g • proj h p`.

Rewrite using `[hgy, ← e', ← gmap_extOf_emb]`. Conclude with `Prod.ext rfl (extOf_x₀ S g')`. Rewrite using `[mul_smul, e0, inv_smul_smul]`. Introduce and unpack `t ⟨ht, k, hk⟩`. Take `⟨Λ₁, h₁, rfl⟩` from `Finset.mem_image.mp ht`.

Establish `e : (g * k) • (emb S Λ₁, S.x₀) = (emb S (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1)), S.x₀)`. Rewrite using `[mul_smul, hk, hgy]`. Take `⟨e1, e2⟩` from `Prod.ext_iff.mp e`. Use `gmap_res S (g * k).1 (g * k).2 e2 e1` as an intermediate fact. Rewrite `this` using `[cut_emb, cut_emb]`.

Rewrite using `[huniq Λ₁ ⟨h₁, _, res_mem_isom S _ _ _, this⟩])`. Use the proof step `(by`. Introduce and unpack `_ ⟨p, hp, rfl⟩`. Conclude with `finite_stab_proj hK hs hd S L hp)`. Rewrite using `[key, Finset.sum_image (fun A _ B _ e => emb_injective S (Prod.ext_iff.mp e).1)]`.

Use `Finset.sum_congr rfl fun Λ' _ => ?_` and prove the remaining obligations. Establish `e1 : Nat.card {p : Submodule (𝓞 K) V × V // p ∈ pairs h L (h S.x₀ S.x₀) ∧ proj h p = (emb S Λ', S.x₀)} = Nat.card (fibG S L Λ')` using `Nat.card_congr { toFun := fun p => ⟨p.1.1, (fibG_of_pair_mem S p.2.1 p.2.2).1⟩ invFun := fun Λ => ⟨(Λ.1, S.x₀), pair_mem_of_fibG S Λ.2⟩ left_inv := fun p => Subtype.ext (Prod.ext rfl (fibG_of_pair_mem S p.2.1 p.2.2).2.symm) right_inv := fun _ => rfl }`. Rewrite using `[e1, Nat.card_congr (stabPairEquiv hs S Λ')]`.
-/
theorem repMass_eq_sum_fib (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L)
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {s' : Finset (Submodule (𝓞 K) V')}
    (hs' : IsFibReps S L s') :
    repMass h L (h S.x₀ S.x₀) =
      ∑ Λ' ∈ s', (Nat.card (fibG S L Λ') : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℝ) := by
  classical
  obtain ⟨sX, hsX, hX⟩ := exists_pairReps hs hd hL (h S.x₀ S.x₀)
  have hex := exists_classReps hs hd hL
  unfold repMass
  rw [dif_pos hex, ← sum_pairs_eq_rep hs hd (h S.x₀ S.x₀) hex.choose_spec hsX hX]
  have key := OrbSum.sum_orbits_on (G := Formalism.HermitianLatticesTheory.isom h) (proj h) proj_smul
    (pairs h L (h S.x₀ S.x₀)) (proj h '' pairs h L (h S.x₀ S.x₀))
    (pairs_stable hs L _) (fun p hp => Set.mem_image_of_mem _ hp) sX
    (s'.image fun Λ' => (emb S Λ', S.x₀)) hsX
    (by
      intro u hu
      obtain ⟨Λ', hΛ', rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨Λ, hΛ⟩ := hs'.1 Λ' hΛ'
      exact ⟨_, (pair_mem_of_fibG S hΛ).1, (pair_mem_of_fibG S hΛ).2⟩)
    hX
    (by
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨g, hg⟩ := exists_move hK hs hd S L p
      obtain ⟨hg1, hg2⟩ := hg hp
      have hgy : g • proj h p = (emb S (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1)), S.x₀) := by
        rw [← proj_smul, hg1]
        exact (pair_mem_of_fibG S hg2).2
      obtain ⟨Λ₀, ⟨h₀, g', hg', e'⟩, huniq⟩ := hs'.2 _ ⟨_, hg2⟩
      refine ⟨(emb S Λ₀, S.x₀), ⟨Finset.mem_image.mpr ⟨Λ₀, h₀, rfl⟩,
        g⁻¹ * ⟨extOf S g', extOf_mem_isom hs S hg'⟩, ?_⟩, ?_⟩
      · have e0 : (⟨extOf S g', extOf_mem_isom hs S hg'⟩ : Formalism.HermitianLatticesTheory.isom h) • (emb S Λ₀, S.x₀) =
            g • proj h p := by
          rw [hgy, ← e', ← gmap_extOf_emb]
          exact Prod.ext rfl (extOf_x₀ S g')
        rw [mul_smul, e0, inv_smul_smul]
      · rintro t ⟨ht, k, hk⟩
        obtain ⟨Λ₁, h₁, rfl⟩ := Finset.mem_image.mp ht
        have e : (g * k) • (emb S Λ₁, S.x₀) =
            (emb S (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1)), S.x₀) := by
          rw [mul_smul, hk, hgy]
        obtain ⟨e1, e2⟩ := Prod.ext_iff.mp e
        have := gmap_res S (g * k).1 (g * k).2 e2 e1
        rw [cut_emb, cut_emb] at this
        rw [huniq Λ₁ ⟨h₁, _, res_mem_isom S _ _ _, this⟩])
    (by
      rintro _ ⟨p, hp, rfl⟩
      exact finite_stab_proj hK hs hd S L hp)
  rw [key, Finset.sum_image (fun A _ B _ e => emb_injective S (Prod.ext_iff.mp e).1)]
  refine Finset.sum_congr rfl fun Λ' _ => ?_
  have e1 : Nat.card {p : Submodule (𝓞 K) V × V //
      p ∈ pairs h L (h S.x₀ S.x₀) ∧ proj h p = (emb S Λ', S.x₀)} = Nat.card (fibG S L Λ') :=
    Nat.card_congr
      { toFun := fun p => ⟨p.1.1, (fibG_of_pair_mem S p.2.1 p.2.2).1⟩
        invFun := fun Λ => ⟨(Λ.1, S.x₀), pair_mem_of_fibG S Λ.2⟩
        left_inv := fun p => Subtype.ext (Prod.ext rfl (fibG_of_pair_mem S p.2.1 p.2.2).2.symm)
        right_inv := fun _ => rfl }
  rw [e1, Nat.card_congr (stabPairEquiv hs S Λ')]

end Formalism.HermitianLattices.Ext.L3
