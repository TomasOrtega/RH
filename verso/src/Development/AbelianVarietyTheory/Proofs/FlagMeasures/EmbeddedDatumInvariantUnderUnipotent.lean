import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AdaptSelf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegAsm.DatMove
open AdaptInv

/- English proof (translation)
Simplify using `only [Submodule.mem_sup]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, b, hb, hab⟩`. Use `⟨t.symm a, (h _).1 (by simpa using ha), t.symm b, (h' _).1 (by simpa using hb), ?_⟩` and prove the remaining obligations. Apply `t.injective` to reduce the goal to its premises.

Simplify using `[hab]`. Introduce and unpack `⟨a, ha, b, hb, rfl⟩`. Conclude with `⟨t a, (h _).2 ha, t b, (h' _).2 hb, by simp⟩`.
-/
theorem sup_iff {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (t : M ≃+ M)
    {A B A' B' : Submodule R M} (h : ∀ y, t y ∈ A ↔ y ∈ B) (h' : ∀ y, t y ∈ A' ↔ y ∈ B') (y : M) :
    t y ∈ A ⊔ A' ↔ y ∈ B ⊔ B' := by
  simp only [Submodule.mem_sup]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨t.symm a, (h _).1 (by simpa using ha), t.symm b, (h' _).1 (by simpa using hb), ?_⟩
    apply t.injective
    simp [hab]
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨t a, (h _).2 ha, t b, (h' _).2 hb, by simp⟩

/- English proof (translation)
Rewrite using `[← sup_iff t h h' y]`. Establish `h1 : t y - y ∈ A ⊔ C` using `Submodule.mem_sup_right hy`. Rewrite using `[← Submodule.add_mem_iff_right _ h1]`. Simplify using the standard rewrite rules.
-/
theorem sup_iff_of_sub {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (t : M ≃+ M)
    {A B C : Submodule R M} (h : ∀ y, t y ∈ A ↔ y ∈ B) (h' : ∀ y, t y ∈ C ↔ y ∈ C) {y : M}
    (hy : t y - y ∈ C) : y ∈ A ⊔ C ↔ y ∈ B ⊔ C := by
  rw [← sup_iff t h h' y]
  have h1 : t y - y ∈ A ⊔ C := Submodule.mem_sup_right hy
  rw [← Submodule.add_mem_iff_right _ h1]
  simp

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

def push (s : V ≃ₗ[K] V) (hs : ∀ x y, H.B (s x) (s y) = H.B x y) (F : FlagD H r) : FlagD H r where
  e a := s (F.e a)
  T := F.T
  indep := F.indep.map' (s : V →ₗ[K] V) s.ker
  iso a b := by rw [hs]; exact F.iso a b
  zperp a := by rw [hs]; exact F.zperp a
  zz := by rw [hs]; exact F.zz
  hT := F.hT

variable (s : V ≃ₗ[K] V) (hs : ∀ x y, H.B (s x) (s y) = H.B x y)

/- English proof (translation)
Unfold `FlagD.X FlagD.Xa`. Rewrite using `[Submodule.map_span, Set.image_image]`. Both sides reduce to the same expression.
-/
theorem push_X (F : FlagD H r) : (push s hs F).X = F.X.map (s : V →ₗ[K] V) := by
  unfold FlagD.X FlagD.Xa
  rw [Submodule.map_span, Set.image_image]
  rfl

/- English proof (translation)
Unfold `V0`. Rewrite using `[push_X, push_X, Submodule.map_sup, Submodule.map_sup, Submodule.map_span, Set.image_pair]`. Both sides reduce to the same expression.
-/
theorem hermFrameMapIsometry_frameSpan (F G : FlagD H r) : V0 (push s hs F) (push s hs G) = (V0 F G).map (s : V →ₗ[K] V) := by
  unfold V0
  rw [push_X, push_X, Submodule.map_sup, Submodule.map_sup, Submodule.map_span, Set.image_pair]
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, h⟩`. Conclude with `s.injective h ▸ hx`. Conclude with `fun h => ⟨y, h, rfl⟩`.
-/
theorem mem_map_iff (S : Submodule K V) (y : V) : s y ∈ S.map (s : V →ₗ[K] V) ↔ y ∈ S := by
  constructor
  · rintro ⟨x, hx, h⟩
    exact s.injective h ▸ hx
  · exact fun h => ⟨y, h, rfl⟩

include hs in
/- English proof (translation)
Simplify using `only [mem_perp_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Rewrite using `[← hs]`. Conclude with `h _ ⟨x, hx, rfl⟩`.

Introduce and unpack `h _ ⟨x, hx, rfl⟩`. Conclude with `(hs _ _).trans (h x hx)`.
-/
theorem perp_map_iff (S : Submodule K V) (y : V) : s y ∈ perp H (S.map (s : V →ₗ[K] V)) ↔ y ∈ perp H S := by
  simp only [mem_perp_iff]
  constructor
  · intro h x hx
    rw [← hs]; exact h _ ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    exact (hs _ _).trans (h x hx)

/- English proof (translation)
Rewrite using `[push_X, mem_map_iff]`.
-/
theorem push_X_iff (F : FlagD H r) (y : V) : s y ∈ (push s hs F).X ↔ y ∈ F.X := by
  rw [push_X, mem_map_iff]

variable {R : Type} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V]

/- English proof (translation)
Establish `h1` using `sup_iff s.toAddEquiv (A' := rs R (push s hs F).X) (B' := rs R F.X) h (push_X_iff s hs F) y`. Simplify using `only [flagPairDefinitePartLattice, latL, uPerp, wSp, Submodule.mem_inf, Submodule.restrictScalars_mem]`. Rewrite using `[hermFrameMapIsometry_frameSpan, perp_map_iff s hs]`. Use `and_congr (and_congr ?_ h1) Iff.rfl` and prove the remaining obligations. Rewrite using `[push_X, push_X, ← Submodule.map_sup, perp_map_iff s hs]`.
-/
theorem hermIsometry_mem_flagPairDefinitePartLattice_iff (F G : FlagD H r) {Λ Λ' : Submodule R V} (h : ∀ y, s y ∈ Λ' ↔ y ∈ Λ) (y : V) :
    s y ∈ flagPairDefinitePartLattice (push s hs F) (push s hs G) Λ' ↔ y ∈ flagPairDefinitePartLattice F G Λ := by
  have h1 := sup_iff s.toAddEquiv (A' := rs R (push s hs F).X) (B' := rs R F.X) h (push_X_iff s hs F) y
  simp only [flagPairDefinitePartLattice, latL, uPerp, wSp, Submodule.mem_inf, Submodule.restrictScalars_mem]
  rw [hermFrameMapIsometry_frameSpan, perp_map_iff s hs]
  refine and_congr (and_congr ?_ h1) Iff.rfl
  rw [push_X, push_X, ← Submodule.map_sup, perp_map_iff s hs]

/- English proof (translation)
Establish `hg : ∀ x, s (g • x) = g • s x` using `fun x => (s : V →ₗ[K] V).map_smul_of_tower g x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, h1⟩`. Use `⟨s.symm x, (h _).1 (by simpa using hx), s.injective ?_⟩` and prove the remaining obligations. Rewrite using `[← h1]`.

Simplify using `using hg (s.symm x)`. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨s x, (h _).2 hx, (hg x).symm⟩`.
-/
theorem smulLat_iff {Λ Λ' : Submodule R V} (h : ∀ y, s y ∈ Λ' ↔ y ∈ Λ) (g : R) (y : V) :
    s y ∈ smulLat g Λ' ↔ y ∈ smulLat g Λ := by
  have hg : ∀ x, s (g • x) = g • s x := fun x => (s : V →ₗ[K] V).map_smul_of_tower g x
  constructor
  · rintro ⟨x, hx, h1⟩
    refine ⟨s.symm x, (h _).1 (by simpa using hx), s.injective ?_⟩
    rw [← h1]
    simpa using hg (s.symm x)
  · rintro ⟨x, hx, rfl⟩
    exact ⟨s x, (h _).2 hx, (hg x).symm⟩

/- English proof (translation)
Simplify using `only [iotaGraph, Submodule.mem_inf]`. Use `and_congr (and_congr (hermIsometry_mem_flagPairDefinitePartLattice_iff s hs G F h y.1) (hermIsometry_mem_flagPairDefinitePartLattice_iff s hs F G h y.2)) ?_` and prove the remaining obligations. Use `sup_iff _ (fun p => ?_) (fun p => and_congr (push_X_iff s hs G p.1) (push_X_iff s hs F p.2)) y` and prove the remaining obligations. Use `and_congr (and_congr (h p.1) (h p.2)) ?_` and prove the remaining obligations. Use `sup_iff s.toAddEquiv (A' := Λ' ⊓ rs R (push s hs F).X) (B' := Λ ⊓ rs R F.X) (smulLat_iff s h g) (fun y => and_congr (h y) (push_X_iff s hs F y)) (p.2 - p.1)` as an intermediate fact.

Rewrite `this` using `[map_sub]`. Conclude with `this`.
-/
theorem push_graph (F G : FlagD H r) {Λ Λ' : Submodule R V} (h : ∀ y, s y ∈ Λ' ↔ y ∈ Λ) (g : R) (y : V × V) :
    (s.toAddEquiv.prodCongr s.toAddEquiv) y ∈ iotaGraph (push s hs F) (push s hs G) Λ' g ↔
      y ∈ iotaGraph F G Λ g := by
  simp only [iotaGraph, Submodule.mem_inf]
  refine and_congr (and_congr (hermIsometry_mem_flagPairDefinitePartLattice_iff s hs G F h y.1) (hermIsometry_mem_flagPairDefinitePartLattice_iff s hs F G h y.2)) ?_
  refine sup_iff _ (fun p => ?_) (fun p => and_congr (push_X_iff s hs G p.1) (push_X_iff s hs F p.2)) y
  refine and_congr (and_congr (h p.1) (h p.2)) ?_
  have := sup_iff s.toAddEquiv (A' := Λ' ⊓ rs R (push s hs F).X) (B' := Λ ⊓ rs R F.X) (smulLat_iff s h g)
    (fun y => and_congr (h y) (push_X_iff s hs F y)) (p.2 - p.1)
  rw [map_sub] at this
  exact this

/- English proof (translation)
Introduce `a`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last => exact hN.2.2.2 _ F.zperp`. Consider the case `cast a => exact hN.2.2.1 a`.
-/
theorem sameGr_push (F : FlagD H r) (hN : F.InN (s : V →ₗ[K] V)) : SameGr F (push s hN.1 F) := by
  intro a
  induction a using Fin.lastCases with
  | last => exact hN.2.2.2 _ F.zperp
  | cast a => exact hN.2.2.1 a

/- English proof (translation)
Proceed by induction on `a using Fin.lastCases with`. Consider the case `last => exact Submodule.mem_sup_right (Submodule.subset_span (Or.inl rfl))`. Consider the case `cast a => exact Submodule.mem_sup_left (Submodule.mem_sup_left (e_mem_xa F a a.2))`.
-/
theorem flag_vector_mem_base_lattice (F G : FlagD H r) (a : Fin (r + 1)) : F.e a ∈ V0 F G := by
  induction a using Fin.lastCases with
  | last => exact Submodule.mem_sup_right (Submodule.subset_span (Or.inl rfl))
  | cast a => exact Submodule.mem_sup_left (Submodule.mem_sup_left (e_mem_xa F a a.2))

/- English proof (translation)
Unfold `V0`. Rewrite using `[sup_comm F.X, Set.pair_comm]`.
-/
theorem jointSpan_comm (F G : FlagD H r) : V0 F G = V0 G F := by
  unfold V0
  rw [sup_comm F.X, Set.pair_comm]

/- English proof (translation)
Rewrite using `[← H.herm, h, star_zero]`.
-/
theorem herm_zero {x y : V} (h : H.B x y = 0) : H.B y x = 0 := by
  rw [← H.herm, h, star_zero]

/- English proof (translation)
Use `⟨⟨?_, Submodule.mem_sup_right hx.1⟩, ?_⟩` and prove the remaining obligations. Conclude with `(mem_perp_iff _ _ _).2 fun w hw => herm_zero (hI x hx w (Submodule.mem_sup_left hw))`. Conclude with `(mem_perp_iff _ _ _).2 fun w hw => herm_zero (hI x hx w hw)`.
-/
theorem commonIsotropic_le_flagPairDefinitePartLattice {F G : FlagD H r} (hI : ∀ x ∈ II F G, ∀ w ∈ V0 F G, H.B w x = 0) (Λ : Submodule R V)
    {x : V} (hx : x ∈ II F G) : x ∈ flagPairDefinitePartLattice F G Λ := by
  refine ⟨⟨?_, Submodule.mem_sup_right hx.1⟩, ?_⟩
  · exact (mem_perp_iff _ _ _).2 fun w hw => herm_zero (hI x hx w (Submodule.mem_sup_left hw))
  · exact (mem_perp_iff _ _ _).2 fun w hw => herm_zero (hI x hx w hw)

end GlobalTheory.DegAsm.DatMove

namespace GlobalTheory.DegAsm
open AdaptInv DatMove

/- English proof (translation)
Introduce `K V W _ _ _ _ _ _ _ _ _ _ _ _ _ H HW e hK r F G G' 𝔡 N g hE hA`. Use `⟨fun s Λ hN hG => ?_, ?_⟩` and prove the remaining obligations. Establish `hs : ∀ x y, H.B (s x) (s y) = H.B x y` using `hN.1`. Establish `hF : SameGr F (push s hs F)` using `sameGr_push s F hN`. Establish `hG' : SameGr G' (push s hs G)` using `hG`.

Establish `hΛ : ∀ y, s y ∈ s • Λ ↔ y ∈ Λ` using `fun y => by`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, h⟩`. Conclude with `s.injective h ▸ hx`. Conclude with `fun h => ⟨y, h, rfl⟩`.

Establish `hX : ∀ y, s y ∈ F.X ↔ y ∈ F.X` using `fun y => by`. Use `push_X_iff s hs F y` as an intermediate fact. Rewrite `this` using `[x_eq hF]`. Then use the resulting hypothesis. Establish `he : ∀ w, s (e w) - e w ∈ F.X` using `fun w => hN.2.2.2 _ fun a => (hE.2 (e w)).2 (Submodule.mem_sup_left ⟨w, rfl⟩) _`. Use `⟨Prod.ext ?_ ?_, ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `w`. Use `sup_iff_of_sub s.toAddEquiv (C := rs (𝓞 K) F.X) (fun y => ?_) hX (he w)` and prove the remaining obligations. Rewrite using `[← flagFramesSameGraded_definitePartLattice_eq hG' hF]`. Conclude with `hermIsometry_mem_flagPairDefinitePartLattice_iff s hs G F hΛ y`. Use extensionality with `w`.

Use `sup_iff_of_sub (s.toAddEquiv.prodCongr s.toAddEquiv) (C := (rs (𝓞 K) F.X).prod (rs (𝓞 K) F.X)) (fun y => ?_) (fun p => and_congr (hX p.1) (hX p.2)) ⟨he w.1, he w.2⟩` and prove the remaining obligations. Rewrite using `[← iotaGraph_eq hF hG']`. Conclude with `push_graph s hs F G hΛ _ y`. Use extensionality with `w`. Conclude with `sup_iff_of_sub s.toAddEquiv (C := rs (𝓞 K) F.X) hΛ hX (he w)`.

Use extensionality with `y`. Use `and_congr_right fun hy => sup_iff_of_sub s.toAddEquiv (C := rs (𝓞 K) F.X) hΛ hX ?_` and prove the remaining obligations. Conclude with `hN.2.2.2 y fun a => herm_zero ((mem_perp_iff _ _ _).1 hy _ (Submodule.mem_sup_left (e_mem_xa F a a.2)))`. Take `⟨-, h, h'⟩` from `hA`. Apply the tactic sequence `have h0 := (GlobalTheory.DegCnt.NF.geometry K V H hK r N).1.2.2.2.2.2.1`.

Establish `h1 : II N.F N.F' = II F G` using `by simp only [II, x_eq h, x_eq h']`. Rewrite `h0` using `[h1, x_eq h, sitesCommonSpace_v0_eq_Vp h h']`. Establish `hI : ∀ x ∈ II F G, ∀ w ∈ V0 F G, H.B w x = 0` using `fun x hx => (h0 x hx.1).2 hx`. Establish `hI' : ∀ x ∈ II G F, ∀ w ∈ V0 G F, H.B w x = 0` using `fun x hx w hw => hI x ⟨hx.2, hx.1⟩ w (jointSpan_comm G F ▸ hw)`. Establish `hdec : ∀ y ∈ wSp F G, ∃ w, y - e w ∈ F.X` using `fun y hy => by`.

Use `(hE.2 y).1 fun a => herm_zero ((mem_perp_iff _ _ _).1 hy _ (flag_vector_mem_base_lattice F G a))` as an intermediate fact. Take `⟨_, ⟨w, rfl⟩, x, hx, rfl⟩` from `Submodule.mem_sup.1 this`. Conclude with `⟨w, by simpa using hx⟩`. Establish `hker : ∀ y ∈ wSp F G, ∀ y' ∈ wSp F G, y - y' ∈ F.X → y - y' ∈ II F G` using `fun y hy y' hy' hx => (h0 _ hx).1 fun w hw => herm_zero ((mem_perp_iff _ _ _).1 (Submodule.sub_mem _ hy hy') w hw)`. Establish `hw : wSp G F = wSp F G` using `by rw [wSp, jointSpan_comm]; rfl`.

Establish `hL : ∀ Λ : Submodule (𝓞 K) V, ∀ y ∈ flagPairDefinitePartLattice G F Λ, y ∈ wSp F G` using `fun Λ y hy => hw ▸ hy.2`. Establish `key : ∀ Λ Λ' : Submodule (𝓞 K) V, datOf F G e g Λ = datOf F G e g Λ' → flagPairDefinitePartLattice G F Λ ≤ flagPairDefinitePartLattice G F Λ' ∧ iotaGraph F G Λ (g : 𝓞 K) ≤ iotaGraph F G Λ' (g : 𝓞 K)`. Introduce `Λ Λ' hd`. Use `⟨fun y hy => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨w, hx⟩` from `hdec y (hL _ y hy)`.

Establish `a1 : w ∈ (datOf F G e g Λ).1`. Use `Submodule.sub_mem (flagPairDefinitePartLattice G F Λ ⊔ rs (𝓞 K) F.X) (Submodule.mem_sup_left hy) (Submodule.mem_sup_right hx)` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Conclude with `this`. Rewrite `a1` using `[hd]`.

Take `⟨m, hm, x, hx', hmx⟩` from `Submodule.mem_sup.1 a1`. Establish `hmx : m + x = e w` using `hmx`. Establish `a2 : y - m ∈ F.X`. Use `F.X.add_mem hx hx'` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[← hmx]`. Normalize the expressions using the abelian group laws. Establish `a3` using `hker y (hL _ y hy) m (hL _ m hm) a2`. Use `Submodule.add_mem _ (commonIsotropic_le_flagPairDefinitePartLattice hI' Λ' ⟨a3.2, a3.1⟩) hm` as an intermediate fact. Simplify using `using this`.

Take `⟨w, hx⟩` from `hdec y.1 (hL _ _ hy.1.1)`. Take `⟨w', hx'⟩` from `hdec y.2 hy.1.2.2`. Establish `a1 : (w, w') ∈ (datOf F G e g Λ).2`. Use `Submodule.sub_mem (iotaGraph F G Λ (g : 𝓞 K) ⊔ (rs (𝓞 K) F.X).prod (rs (𝓞 K) F.X)) (Submodule.mem_sup_left hy) (Submodule.mem_sup_right (x := y - (e w, e w')) ⟨hx, hx'⟩)` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`.

Conclude with `this`. Rewrite `a1` using `[hd]`. Take `⟨m, hm, x, hx2, hmx⟩` from `Submodule.mem_sup.1 a1`. Establish `hmx1 : m.1 + x.1 = e w` using `congrArg Prod.fst hmx`. Establish `hmx2 : m.2 + x.2 = e w'` using `congrArg Prod.snd hmx`.

Establish `a2 : y.1 - m.1 ∈ F.X`. Use `F.X.add_mem hx hx2.1` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← hmx1]`. Normalize the expressions using the abelian group laws.

Establish `a2' : y.2 - m.2 ∈ F.X`. Use `F.X.add_mem hx' hx2.2` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← hmx2]`. Normalize the expressions using the abelian group laws.

Establish `a3` using `hker _ (hL _ _ hy.1.1) _ (hL _ _ hm.1.1) a2`. Establish `a3'` using `hker _ hy.1.2.2 _ hm.1.2.2 a2'`. Establish `a4 : y - m ∈ iotaGraph F G Λ' (g : 𝓞 K)` using `⟨⟨commonIsotropic_le_flagPairDefinitePartLattice hI' Λ' ⟨a3.2, a3.1⟩, commonIsotropic_le_flagPairDefinitePartLattice hI Λ' a3'⟩, Submodule.mem_sup_right ⟨a3.2, a3'.1⟩⟩`. Use `Submodule.add_mem _ a4 hm` as an intermediate fact. Simplify using `using this`.

Conclude with `fun Λ Λ' hd => ⟨le_antisymm (key _ _ hd).1 (key _ _ hd.symm).1, le_antisymm (key _ _ hd).2 (key _ _ hd.symm).2⟩`.
-/
theorem datOf_move : ∀ (K V W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (H : HermSpace K V) (HW : HermSpace K W) (e : W →ₗ[K] V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F G G' : FlagD H r) (𝔡 : Ideal (𝓞 K)) (N : NF H r) (g : ℕ), IsEmb F HW e → Adapt F G 𝔡 N → (∀ (s : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V), F.InN (s : V →ₗ[K] V) → (∀ a, s (G.e a) - G'.e a ∈ G'.Xa a.val) → datOf F G' e g (s • Λ) = datOf F G e g Λ ∧ lat0 F e (s • Λ) = lat0 F e Λ ∧ latL F G (s • Λ) = latL F G Λ) ∧ ∀ Λ Λ' : Submodule (𝓞 K) V, datOf F G e g Λ = datOf F G e g Λ' → flagPairDefinitePartLattice G F Λ = flagPairDefinitePartLattice G F Λ' ∧ iotaGraph F G Λ (g : 𝓞 K) = iotaGraph F G Λ' (g : 𝓞 K) := by
  intro K V W _ _ _ _ _ _ _ _ _ _ _ _ _ H HW e hK r F G G' 𝔡 N g hE hA
  refine ⟨fun s Λ hN hG => ?_, ?_⟩
  · have hs : ∀ x y, H.B (s x) (s y) = H.B x y := hN.1
    have hF : SameGr F (push s hs F) := sameGr_push s F hN
    have hG' : SameGr G' (push s hs G) := hG
    have hΛ : ∀ y, s y ∈ s • Λ ↔ y ∈ Λ := fun y => by
      constructor
      · rintro ⟨x, hx, h⟩
        exact s.injective h ▸ hx
      · exact fun h => ⟨y, h, rfl⟩
    have hX : ∀ y, s y ∈ F.X ↔ y ∈ F.X := fun y => by
      have := push_X_iff s hs F y
      rwa [x_eq hF] at this
    have he : ∀ w, s (e w) - e w ∈ F.X := fun w =>
      hN.2.2.2 _ fun a => (hE.2 (e w)).2 (Submodule.mem_sup_left ⟨w, rfl⟩) _
    refine ⟨Prod.ext ?_ ?_, ?_, ?_⟩
    · ext w
      refine sup_iff_of_sub s.toAddEquiv (C := rs (𝓞 K) F.X) (fun y => ?_) hX (he w)
      rw [← flagFramesSameGraded_definitePartLattice_eq hG' hF]
      exact hermIsometry_mem_flagPairDefinitePartLattice_iff s hs G F hΛ y
    · ext w
      refine sup_iff_of_sub (s.toAddEquiv.prodCongr s.toAddEquiv)
        (C := (rs (𝓞 K) F.X).prod (rs (𝓞 K) F.X)) (fun y => ?_)
        (fun p => and_congr (hX p.1) (hX p.2)) ⟨he w.1, he w.2⟩
      rw [← iotaGraph_eq hF hG']
      exact push_graph s hs F G hΛ _ y
    · ext w
      exact sup_iff_of_sub s.toAddEquiv (C := rs (𝓞 K) F.X) hΛ hX (he w)
    · ext y
      refine and_congr_right fun hy => sup_iff_of_sub s.toAddEquiv (C := rs (𝓞 K) F.X) hΛ hX ?_
      exact hN.2.2.2 y fun a => herm_zero
        ((mem_perp_iff _ _ _).1 hy _ (Submodule.mem_sup_left (e_mem_xa F a a.2)))
  · obtain ⟨-, h, h'⟩ := hA
    have h0 := (GlobalTheory.DegCnt.NF.geometry K V H hK r N).1.2.2.2.2.2.1
    have h1 : II N.F N.F' = II F G := by simp only [II, x_eq h, x_eq h']
    rw [h1, x_eq h, sitesCommonSpace_v0_eq_Vp h h'] at h0
    have hI : ∀ x ∈ II F G, ∀ w ∈ V0 F G, H.B w x = 0 := fun x hx => (h0 x hx.1).2 hx
    have hI' : ∀ x ∈ II G F, ∀ w ∈ V0 G F, H.B w x = 0 := fun x hx w hw =>
      hI x ⟨hx.2, hx.1⟩ w (jointSpan_comm G F ▸ hw)
    have hdec : ∀ y ∈ wSp F G, ∃ w, y - e w ∈ F.X := fun y hy => by
      have := (hE.2 y).1 fun a => herm_zero ((mem_perp_iff _ _ _).1 hy _ (flag_vector_mem_base_lattice F G a))
      obtain ⟨_, ⟨w, rfl⟩, x, hx, rfl⟩ := Submodule.mem_sup.1 this
      exact ⟨w, by simpa using hx⟩
    have hker : ∀ y ∈ wSp F G, ∀ y' ∈ wSp F G, y - y' ∈ F.X → y - y' ∈ II F G := fun y hy y' hy' hx =>
      (h0 _ hx).1 fun w hw => herm_zero ((mem_perp_iff _ _ _).1 (Submodule.sub_mem _ hy hy') w hw)
    have hw : wSp G F = wSp F G := by rw [wSp, jointSpan_comm]; rfl
    have hL : ∀ Λ : Submodule (𝓞 K) V, ∀ y ∈ flagPairDefinitePartLattice G F Λ, y ∈ wSp F G := fun Λ y hy => hw ▸ hy.2
    have key : ∀ Λ Λ' : Submodule (𝓞 K) V, datOf F G e g Λ = datOf F G e g Λ' →
        flagPairDefinitePartLattice G F Λ ≤ flagPairDefinitePartLattice G F Λ' ∧ iotaGraph F G Λ (g : 𝓞 K) ≤ iotaGraph F G Λ' (g : 𝓞 K) := by
      intro Λ Λ' hd
      refine ⟨fun y hy => ?_, fun y hy => ?_⟩
      · obtain ⟨w, hx⟩ := hdec y (hL _ y hy)
        have a1 : w ∈ (datOf F G e g Λ).1 := by
          have := Submodule.sub_mem (flagPairDefinitePartLattice G F Λ ⊔ rs (𝓞 K) F.X) (Submodule.mem_sup_left hy)
            (Submodule.mem_sup_right hx)
          rw [sub_sub_cancel] at this
          exact this
        rw [hd] at a1
        obtain ⟨m, hm, x, hx', hmx⟩ := Submodule.mem_sup.1 a1
        have hmx : m + x = e w := hmx
        have a2 : y - m ∈ F.X := by
          have := F.X.add_mem hx hx'
          convert this using 1
          rw [← hmx]; abel
        have a3 := hker y (hL _ y hy) m (hL _ m hm) a2
        have := Submodule.add_mem _ (commonIsotropic_le_flagPairDefinitePartLattice hI' Λ' ⟨a3.2, a3.1⟩) hm
        simpa using this
      · obtain ⟨w, hx⟩ := hdec y.1 (hL _ _ hy.1.1)
        obtain ⟨w', hx'⟩ := hdec y.2 hy.1.2.2
        have a1 : (w, w') ∈ (datOf F G e g Λ).2 := by
          have := Submodule.sub_mem (iotaGraph F G Λ (g : 𝓞 K) ⊔ (rs (𝓞 K) F.X).prod (rs (𝓞 K) F.X))
            (Submodule.mem_sup_left hy) (Submodule.mem_sup_right (x := y - (e w, e w')) ⟨hx, hx'⟩)
          rw [sub_sub_cancel] at this
          exact this
        rw [hd] at a1
        obtain ⟨m, hm, x, hx2, hmx⟩ := Submodule.mem_sup.1 a1
        have hmx1 : m.1 + x.1 = e w := congrArg Prod.fst hmx
        have hmx2 : m.2 + x.2 = e w' := congrArg Prod.snd hmx
        have a2 : y.1 - m.1 ∈ F.X := by
          have := F.X.add_mem hx hx2.1
          convert this using 1
          rw [← hmx1]; abel
        have a2' : y.2 - m.2 ∈ F.X := by
          have := F.X.add_mem hx' hx2.2
          convert this using 1
          rw [← hmx2]; abel
        have a3 := hker _ (hL _ _ hy.1.1) _ (hL _ _ hm.1.1) a2
        have a3' := hker _ hy.1.2.2 _ hm.1.2.2 a2'
        have a4 : y - m ∈ iotaGraph F G Λ' (g : 𝓞 K) :=
          ⟨⟨commonIsotropic_le_flagPairDefinitePartLattice hI' Λ' ⟨a3.2, a3.1⟩, commonIsotropic_le_flagPairDefinitePartLattice hI Λ' a3'⟩, Submodule.mem_sup_right ⟨a3.2, a3'.1⟩⟩
        have := Submodule.add_mem _ a4 hm
        simpa using this
    exact fun Λ Λ' hd => ⟨le_antisymm (key _ _ hd).1 (key _ _ hd.symm).1, le_antisymm (key _ _ hd).2 (key _ _ hd.symm).2⟩

end GlobalTheory.DegAsm
