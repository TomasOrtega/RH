import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AdaptSelf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open Formalism.HermitianLatticeCounting.P
namespace GlobalTheory.DegAsm.IndIsom
variable {K V W : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {H : HermSpace K V} {r : ℕ}

/- English proof (translation)
Establish `h : F.X ≤ LinearMap.ker (H.B.flip v)`. Rewrite using `[FlagD.X, FlagD.Xa, Submodule.span_le]`. Introduce and unpack `_ ⟨b, -, rfl⟩`. Simplify using `using hv b.castSucc`. Introduce `x hx`.

Simplify using `using h hx`.
-/
theorem perpX (F : FlagD H r) {v : V} (hv : ∀ a : Fin (r + 1), H.B (F.e a) v = 0) :
    ∀ x ∈ F.X, H.B x v = 0 := by
  have h : F.X ≤ LinearMap.ker (H.B.flip v) := by
    rw [FlagD.X, FlagD.Xa, Submodule.span_le]
    rintro _ ⟨b, -, rfl⟩
    simpa using hv b.castSucc
  intro x hx
  simpa using h hx

/- English proof (translation)
Establish `h : F.X.map (γ : V →ₗ[K] V) = G.X`. Simplify using `only [FlagD.X, FlagD.Xa, Submodule.map_span, Set.image_image, hG, LinearEquiv.coe_coe]`. Rewrite using `[← h]`. Conclude with `Submodule.mem_map_of_mem hx`.
-/
theorem map_mem {F G : FlagD H r} {γ : V ≃ₗ[K] V} (hG : ∀ a, G.e a = γ (F.e a)) {x : V} (hx : x ∈ F.X) :
    γ x ∈ G.X := by
  have h : F.X.map (γ : V →ₗ[K] V) = G.X := by
    simp only [FlagD.X, FlagD.Xa, Submodule.map_span, Set.image_image, hG, LinearEquiv.coe_coe]
  rw [← h]
  exact Submodule.mem_map_of_mem hx

/- English proof (translation)
Establish `h` using `map_mem (F := G) (G := F) (γ := γ.symm) (fun a => by rw [hG a, LinearEquiv.symm_apply_apply]) hx`. Rewrite `h` using `[LinearEquiv.symm_apply_apply]`. Then use the resulting hypothesis.
-/
theorem mem_of_map {F G : FlagD H r} {γ : V ≃ₗ[K] V} (hG : ∀ a, G.e a = γ (F.e a)) {x : V} (hx : γ x ∈ G.X) :
    x ∈ F.X := by
  have h := map_mem (F := G) (G := F) (γ := γ.symm)
    (fun a => by rw [hG a, LinearEquiv.symm_apply_apply]) hx
  rwa [LinearEquiv.symm_apply_apply] at h

/- English proof (translation)
Establish `h1 : H.B (y - u) y' = 0` using `hy' _ h`. Establish `h2 : H.B (y' - u') u = 0` using `hu _ h'`. Establish `h3 : H.B u (y' - u') = 0` using `by rw [← H.herm, h2, star_zero]`. Rewrite `h1` using `[map_sub, LinearMap.sub_apply, sub_eq_zero]`. Rewrite `h3` using `[map_sub, sub_eq_zero]`.

Rewrite using `[h1, h3]`.
-/
theorem B_mod {S : Submodule K V} {u u' y y' : V} (hu : ∀ x ∈ S, H.B x u = 0) (hy' : ∀ x ∈ S, H.B x y' = 0)
    (h : y - u ∈ S) (h' : y' - u' ∈ S) : H.B y y' = H.B u u' := by
  have h1 : H.B (y - u) y' = 0 := hy' _ h
  have h2 : H.B (y' - u') u = 0 := hu _ h'
  have h3 : H.B u (y' - u') = 0 := by rw [← H.herm, h2, star_zero]
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at h1
  rw [map_sub, sub_eq_zero] at h3
  rw [h1, h3]

end GlobalTheory.DegAsm.IndIsom

namespace GlobalTheory.DegAsm
open IndIsom
/- English proof (translation)
Establish `h' : a - b ∈ M ⊔ S.restrictScalars R` using `Submodule.mem_sup_right h`. Prove the components needed by the constructor for the conclusion. Introduce `ha`. Simplify using `using sub_mem ha h'`. Introduce `hb`.

Simplify using `using add_mem hb h'`.
-/
private lemma sup_iff_lemma {K V : Type} [Field K] [AddCommGroup V] [Module K V] {R : Type} [CommRing R]
    [Algebra R K] [Module R V] [IsScalarTower R K V] (M : Submodule R V) (S : Submodule K V) {a b : V}
    (h : a - b ∈ S) : a ∈ M ⊔ S.restrictScalars R ↔ b ∈ M ⊔ S.restrictScalars R := by
  have h' : a - b ∈ M ⊔ S.restrictScalars R := Submodule.mem_sup_right h
  constructor
  · intro ha
    simpa using sub_mem ha h'
  · intro hb
    simpa using add_mem hb h'

/- English proof (translation)
Introduce `K V W _ _ _ _ _ _ _ _ _ _ _ _ _ H HW e hCM r F G 𝔡 N γ hE hAd hγ hG`. Take `⟨-, hXF, hXG, hV0, -⟩` from `adapt_invariants K V H hCM r F G 𝔡 N hAd`. Apply the tactic sequence `obtain ⟨hfull, -⟩ := NF.geometry K V H hCM r N`. Take `⟨-, -, -, -, -, hIF, hIG, -, hexG⟩` from `hfull`. Simplify using `only [II, hXF, hXG, hV0] at hIF hIG hexG`.

Establish `hW : ∀ y, y ∈ wSp F G ↔ ∀ v ∈ V0 F G, H.B v y = 0` using `fun y => GlobalTheory.DegCnt.NFGeom.mem_perp' (H := H) (V0 F G) y`. Establish `hFV0 : F.X ≤ V0 F G` using `le_sup_left.trans le_sup_left`. Establish `hGV0 : G.X ≤ V0 F G` using `le_sup_right.trans le_sup_left`. Establish `hzF : F.z ∈ V0 F G` using `Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert _ _))`. Establish `feV0 : ∀ a : Fin (r + 1), F.e a ∈ V0 F G`.

Introduce `a`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last => exact hzF`. Consider the case `cast b => exact hFV0 (Submodule.subset_span ⟨b, b.isLt, rfl⟩)`. Establish `hA : ∀ x ∈ F.X, (∀ v ∈ V0 F G, H.B v x = 0) → x ∈ G.X` using `fun x hx hv => (Submodule.mem_inf.mp ((hIF x hx).1 hv)).2`.

Establish `hB : ∀ x ∈ G.X, (∀ v ∈ V0 F G, H.B v x = 0) → x ∈ F.X` using `fun x hx hv => (Submodule.mem_inf.mp ((hIG x hx).1 hv)).1`. Establish `hSG : SameGr G N.F'` using `hAd.2.2`. Establish `hC : ∀ w, (∀ a, H.B (G.e a) w = 0) → ∃ x ∈ G.X, ∀ v ∈ V0 F G, H.B v (w - x) = 0`. Introduce `w hw`. Apply `hexG` to reduce the goal to its premises.

Introduce `a`. Establish `h1 : N.F'.e a - G.e a ∈ G.X` using `AdaptInv.xa_mono G (Nat.lt_succ_iff.mp a.isLt) (hSG a)`. Establish `h2` using `perpX G hw _ h1`. Rewrite `h2` using `[map_sub, LinearMap.sub_apply, hw a, sub_zero]`. Conclude with `h2`.

Establish `hEperp : ∀ u : W, ∀ a, H.B (F.e a) (e u) = 0` using `fun u => (hE.2 (e u)).2 (Submodule.mem_sup_left (LinearMap.mem_range_self e u))`. Establish `hEX : ∀ u : W, ∀ x ∈ F.X, H.B x (e u) = 0` using `fun u => perpX F (hEperp u)`. Establish `hγB` using `(mem_isomGrp H γ).1 hγ`. Establish `hγperp : ∀ u : W, ∀ a, H.B (G.e a) (γ (e u)) = 0` using `fun u a => by`. Rewrite using `[hG a, hγB]`.

Conclude with `hEperp u a`. Establish `hγX : ∀ u : W, ∀ x ∈ G.X, H.B x (γ (e u)) = 0` using `fun u => perpX G (hγperp u)`. Establish `heX : ∀ u : W, e u ∈ F.X → u = 0`. Introduce `u hu`. Apply `HW.nondeg u` to reduce the goal to its premises.

Introduce `u'`. Rewrite using `[← hE.1]`. Conclude with `hEX u' _ hu`. Establish `hex : ∀ w : W, ∃ u : W, ∃ y ∈ wSp F G, y - e u ∈ F.X ∧ y - γ (e w) ∈ G.X`. Introduce `w`.

Take `⟨x, hxG, hx⟩` from `hC (γ (e w)) (hγperp w)`. Establish `hy : γ (e w) - x ∈ wSp F G` using `(hW _).2 hx`. Establish `hyF : ∀ a, H.B (F.e a) (γ (e w) - x) = 0` using `fun a => hx _ (feV0 a)`. Take `⟨y1, hy1, z, hz, hyz⟩` from `Submodule.mem_sup.mp ((hE.2 _).1 hyF)`. Take `⟨u, rfl⟩` from `LinearMap.mem_range.mp hy1`.

Use `⟨u, γ (e w) - x, hy, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hyz]`. Simplify using `using hz`. Simplify using `using neg_mem hxG`. Establish `huniq : ∀ w u₁ u₂, (∃ y ∈ wSp F G, y - e u₁ ∈ F.X ∧ y - γ (e w) ∈ G.X) → (∃ y ∈ wSp F G, y - e u₂ ∈ F.X ∧ y - γ (e w) ∈ G.X) → u₁ = u₂`.

Introduce and unpack `w u₁ u₂ ⟨y₁, hy₁, hF₁, hG₁⟩ ⟨y₂, hy₂, hF₂, hG₂⟩`. Establish `hdG : y₁ - y₂ ∈ G.X`. Use `sub_mem hG₁ hG₂ using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws. Establish `hdF : y₁ - y₂ ∈ F.X` using `hB _ hdG ((hW _).1 (sub_mem hy₁ hy₂))`.

Establish `he : e (u₁ - u₂) ∈ F.X`. Use `add_mem (sub_mem hdF hF₁) hF₂ using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_sub]`. Normalize the expressions using the abelian group laws. Conclude with `sub_eq_zero.mp (heX _ he)`.

Use `choose f hf using hex`. Establish `hchar : ∀ w u, (∃ y ∈ wSp F G, y - e u ∈ F.X ∧ y - γ (e w) ∈ G.X) → f w = u` using `fun w u hu => huniq w _ _ (hf w) hu`. Establish `hadd : ∀ w₁ w₂, f (w₁ + w₂) = f w₁ + f w₂`. Introduce `w₁ w₂`. Apply `hchar` to reduce the goal to its premises.

Take `⟨y₁, hy₁, hF₁, hG₁⟩` from `hf w₁`. Take `⟨y₂, hy₂, hF₂, hG₂⟩` from `hf w₂`. Use `⟨y₁ + y₂, add_mem hy₁ hy₂, ?_, ?_⟩` and prove the remaining obligations. Use `add_mem hF₁ hF₂ using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_add]`.

Normalize the expressions using the abelian group laws. Use `add_mem hG₁ hG₂ using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_add, map_add]`. Normalize the expressions using the abelian group laws. Establish `hsmul : ∀ (c : K) (w : W), f (c • w) = c • f w`.

Introduce `c w`. Apply `hchar` to reduce the goal to its premises. Take `⟨y, hy, hF, hGG⟩` from `hf w`. Use `⟨c • y, Submodule.smul_mem _ c hy, ?_, ?_⟩` and prove the remaining obligations. Use `Submodule.smul_mem _ c hF using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[map_smul, smul_sub]`. Use `Submodule.smul_mem _ c hGG using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_smul, map_smul, smul_sub]`. Set `fl : W →ₗ[K] W` to `{ toFun := f map_add' := hadd map_smul' := fun c w => by rw [RingHom.id_apply]; exact hsmul c w }`. Establish `hiso : ∀ w₁ w₂, HW.B (f w₁) (f w₂) = HW.B w₁ w₂`.

Introduce `w₁ w₂`. Take `⟨y₁, hy₁, hF₁, hG₁⟩` from `hf w₁`. Take `⟨y₂, hy₂, hF₂, hG₂⟩` from `hf w₂`. Rewrite using `[← hE.1, ← hE.1]`. Establish `e₁ : H.B y₁ y₂ = H.B (e (f w₁)) (e (f w₂))` using `B_mod (S := F.X) (hEX (f w₁)) (fun x hx => (hW y₂).1 hy₂ x (hFV0 hx)) hF₁ hF₂`.

Establish `e₂ : H.B y₁ y₂ = H.B (γ (e w₁)) (γ (e w₂))` using `B_mod (S := G.X) (hγX w₁) (fun x hx => (hW y₂).1 hy₂ x (hGV0 hx)) hG₁ hG₂`. Rewrite using `[← e₁, e₂, hγB]`. Establish `hinj : Function.Injective fl`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `w hw`.

Apply `HW.nondeg w` to reduce the goal to its premises. Introduce `w'`. Establish `hw0 : f w = 0` using `hw`. Rewrite using `[← hiso w w', hw0, map_zero, LinearMap.zero_apply]`. Use `set h := LinearEquiv.ofInjectiveEndo fl hinj with hh`.

Establish `hcoe : ∀ w, h w = f w` using `fun w => by`. Rewrite using `[hh, LinearEquiv.coe_ofInjectiveEndo]`. Both sides reduce to the same expression. Use `⟨h, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_isomGrp]`.

Introduce `x y`. Rewrite using `[hcoe, hcoe, hiso]`. Introduce `w`. Rewrite using `[hcoe]`. Conclude with `hf w`.

Introduce `h' hh'`. Use extensionality with `w`. Rewrite using `[hcoe]`. Conclude with `(hchar w (h' w) (hh' w)).symm`. Introduce `g Λ'`.

Use extensionality with `u`. Take `⟨w, rfl⟩ : ∃ w, h w = u` from `⟨h.symm u, h.apply_symm_apply u⟩`. Take `⟨y, hy, hF, hGG⟩` from `hf w`. Rewrite `hF` using `[← hcoe]`. Establish `hR : h w ∈ imLat h (lat0 F e Λ') ↔ e w ∈ Λ' ⊔ rs (𝓞 K) F.X`.

Simplify using `only [imLat, Formalism.HermitianLatticesTheory.gmap, lat0, Submodule.mem_map, Submodule.mem_comap, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w', hw', hww⟩`. Rewrite `hw'` using `[h.injective hww]`. Then use the resulting hypothesis. Introduce `hw`.

Conclude with `⟨w, hw, rfl⟩`. Establish `hL : h w ∈ (datOf F G e g (γ • Λ')).1 ↔ e (h w) ∈ flagPairDefinitePartLattice G F (γ • Λ') ⊔ rs (𝓞 K) F.X` using `Iff.rfl`. Rewrite using `[hL, hR, ← sup_iff_lemma _ _ hF]`. Establish `hV0c : V0 G F = V0 F G`. Simplify using `only [V0]`.

Rewrite using `[sup_comm G.X F.X, Set.pair_comm]`. Establish `hWc : ∀ v, v ∈ wSp G F ↔ v ∈ wSp F G` using `fun v => by`. Simplify using `only [wSp, hV0c]`. Establish `hS2 : y ∈ flagPairDefinitePartLattice G F (γ • Λ') ⊔ rs (𝓞 K) F.X ↔ y ∈ γ • Λ' ⊔ rs (𝓞 K) G.X`. Prove the components needed by the constructor for the conclusion.

Introduce `hy'`. Take `⟨l, hl, x, hx, hlx⟩` from `Submodule.mem_sup.mp hy'`. Establish `hl1 : l ∈ γ • Λ' ⊔ rs (𝓞 K) G.X` using `(Submodule.mem_inf.mp (Submodule.mem_inf.mp hl).1).2`. Establish `hl2 : l ∈ wSp F G` using `(hWc l).1 (Submodule.mem_inf.mp hl).2`. Establish `hx' : x ∈ G.X`.

Establish `hxy : x = y - l` using `by rw [← hlx]; abel`. Apply `hA x hx` to reduce the goal to its premises. Rewrite using `[hxy]`. Conclude with `(hW _).1 (sub_mem hy hl2)`. Rewrite using `[← hlx]`.

Conclude with `add_mem hl1 (Submodule.mem_sup_right hx')`. Introduce `hy'`. Apply `Submodule.mem_sup_left` to reduce the goal to its premises. Use `Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, hy'⟩, (hWc y).2 hy⟩` and prove the remaining obligations. Use `show y ∈ uPerp G F`.

Rewrite using `[uPerp, GlobalTheory.DegCnt.NFGeom.mem_perp']`. Introduce `x hx`. Apply `(hW y).1 hy` to reduce the goal to its premises. Conclude with `sup_le hGV0 hFV0 hx`. Rewrite using `[hS2, sup_iff_lemma _ _ hGG]`.

Prove the components needed by the constructor for the conclusion. Introduce `h1`. Take `⟨m, hm, x, hx, hmx⟩` from `Submodule.mem_sup.mp h1`. Take `⟨l, hl, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hm`. Rewrite `hmx` using `[LinearEquiv.smul_def]`.

Establish `hx' : γ (e w - l) ∈ G.X`. Rewrite using `[map_sub, ← hmx]`. Simplify using `using hx`. Establish `: e w - l ∈ F.X` using `IndIsom.mem_of_map hG hx'`. Establish `hsum : e w = l + (e w - l)` using `by abel`.

Rewrite using `[hsum]`. Conclude with `add_mem (Submodule.mem_sup_left hl) (Submodule.mem_sup_right this)`. Introduce `h1`. Take `⟨l, hl, x, hx, hlx⟩` from `Submodule.mem_sup.mp h1`. Rewrite using `[← hlx, map_add]`.

Use `add_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (IndIsom.map_mem hG hx))` and prove the remaining obligations. Rewrite using `[← LinearEquiv.smul_def]`. Conclude with `Submodule.smul_mem_pointwise_smul _ _ _ hl`.
-/
theorem exists_isH : ∀ (K V W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (H : HermSpace K V) (HW : HermSpace K W) (e : W →ₗ[K] V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F G : FlagD H r) (𝔡 : Ideal (𝓞 K)) (N : NF H r) (γ : V ≃ₗ[K] V), IsEmb F HW e → Adapt F G 𝔡 N → γ ∈ isomGrp H → (∀ a, G.e a = γ (F.e a)) → ∃ h : W ≃ₗ[K] W, h ∈ isomGrp HW ∧ IsH F G e γ h ∧ (∀ h' : W ≃ₗ[K] W, IsH F G e γ h' → h' = h) ∧ ∀ (g : ℕ) (Λ' : Submodule (𝓞 K) V), (datOf F G e g (γ • Λ')).1 = imLat h (lat0 F e Λ') := by
  intro K V W _ _ _ _ _ _ _ _ _ _ _ _ _ H HW e hCM r F G 𝔡 N γ hE hAd hγ hG
  classical
  obtain ⟨-, hXF, hXG, hV0, -⟩ := adapt_invariants K V H hCM r F G 𝔡 N hAd
  obtain ⟨hfull, -⟩ := NF.geometry K V H hCM r N
  obtain ⟨-, -, -, -, -, hIF, hIG, -, hexG⟩ := hfull
  simp only [II, hXF, hXG, hV0] at hIF hIG hexG
  have hW : ∀ y, y ∈ wSp F G ↔ ∀ v ∈ V0 F G, H.B v y = 0 := fun y =>
    GlobalTheory.DegCnt.NFGeom.mem_perp' (H := H) (V0 F G) y
  have hFV0 : F.X ≤ V0 F G := le_sup_left.trans le_sup_left
  have hGV0 : G.X ≤ V0 F G := le_sup_right.trans le_sup_left
  have hzF : F.z ∈ V0 F G := Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert _ _))
  have feV0 : ∀ a : Fin (r + 1), F.e a ∈ V0 F G := by
    intro a
    induction a using Fin.lastCases with
    | last => exact hzF
    | cast b => exact hFV0 (Submodule.subset_span ⟨b, b.isLt, rfl⟩)
  have hA : ∀ x ∈ F.X, (∀ v ∈ V0 F G, H.B v x = 0) → x ∈ G.X := fun x hx hv =>
    (Submodule.mem_inf.mp ((hIF x hx).1 hv)).2
  have hB : ∀ x ∈ G.X, (∀ v ∈ V0 F G, H.B v x = 0) → x ∈ F.X := fun x hx hv =>
    (Submodule.mem_inf.mp ((hIG x hx).1 hv)).1
  have hSG : SameGr G N.F' := hAd.2.2
  have hC : ∀ w, (∀ a, H.B (G.e a) w = 0) → ∃ x ∈ G.X, ∀ v ∈ V0 F G, H.B v (w - x) = 0 := by
    intro w hw
    apply hexG
    intro a
    have h1 : N.F'.e a - G.e a ∈ G.X := AdaptInv.xa_mono G (Nat.lt_succ_iff.mp a.isLt) (hSG a)
    have h2 := perpX G hw _ h1
    rw [map_sub, LinearMap.sub_apply, hw a, sub_zero] at h2
    exact h2
  have hEperp : ∀ u : W, ∀ a, H.B (F.e a) (e u) = 0 := fun u =>
    (hE.2 (e u)).2 (Submodule.mem_sup_left (LinearMap.mem_range_self e u))
  have hEX : ∀ u : W, ∀ x ∈ F.X, H.B x (e u) = 0 := fun u => perpX F (hEperp u)
  have hγB := (mem_isomGrp H γ).1 hγ
  have hγperp : ∀ u : W, ∀ a, H.B (G.e a) (γ (e u)) = 0 := fun u a => by
    rw [hG a, hγB]; exact hEperp u a
  have hγX : ∀ u : W, ∀ x ∈ G.X, H.B x (γ (e u)) = 0 := fun u => perpX G (hγperp u)
  have heX : ∀ u : W, e u ∈ F.X → u = 0 := by
    intro u hu
    apply HW.nondeg u
    intro u'
    rw [← hE.1]
    exact hEX u' _ hu
  have hex : ∀ w : W, ∃ u : W, ∃ y ∈ wSp F G, y - e u ∈ F.X ∧ y - γ (e w) ∈ G.X := by
    intro w
    obtain ⟨x, hxG, hx⟩ := hC (γ (e w)) (hγperp w)
    have hy : γ (e w) - x ∈ wSp F G := (hW _).2 hx
    have hyF : ∀ a, H.B (F.e a) (γ (e w) - x) = 0 := fun a => hx _ (feV0 a)
    obtain ⟨y1, hy1, z, hz, hyz⟩ := Submodule.mem_sup.mp ((hE.2 _).1 hyF)
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hy1
    refine ⟨u, γ (e w) - x, hy, ?_, ?_⟩
    · rw [← hyz]; simpa using hz
    · simpa using neg_mem hxG
  have huniq : ∀ w u₁ u₂, (∃ y ∈ wSp F G, y - e u₁ ∈ F.X ∧ y - γ (e w) ∈ G.X) →
      (∃ y ∈ wSp F G, y - e u₂ ∈ F.X ∧ y - γ (e w) ∈ G.X) → u₁ = u₂ := by
    rintro w u₁ u₂ ⟨y₁, hy₁, hF₁, hG₁⟩ ⟨y₂, hy₂, hF₂, hG₂⟩
    have hdG : y₁ - y₂ ∈ G.X := by
      convert sub_mem hG₁ hG₂ using 1; abel
    have hdF : y₁ - y₂ ∈ F.X := hB _ hdG ((hW _).1 (sub_mem hy₁ hy₂))
    have he : e (u₁ - u₂) ∈ F.X := by
      convert add_mem (sub_mem hdF hF₁) hF₂ using 1
      rw [map_sub]; abel
    exact sub_eq_zero.mp (heX _ he)
  choose f hf using hex
  have hchar : ∀ w u, (∃ y ∈ wSp F G, y - e u ∈ F.X ∧ y - γ (e w) ∈ G.X) → f w = u :=
    fun w u hu => huniq w _ _ (hf w) hu
  have hadd : ∀ w₁ w₂, f (w₁ + w₂) = f w₁ + f w₂ := by
    intro w₁ w₂
    apply hchar
    obtain ⟨y₁, hy₁, hF₁, hG₁⟩ := hf w₁
    obtain ⟨y₂, hy₂, hF₂, hG₂⟩ := hf w₂
    refine ⟨y₁ + y₂, add_mem hy₁ hy₂, ?_, ?_⟩
    · convert add_mem hF₁ hF₂ using 1; rw [map_add]; abel
    · convert add_mem hG₁ hG₂ using 1; rw [map_add, map_add]; abel
  have hsmul : ∀ (c : K) (w : W), f (c • w) = c • f w := by
    intro c w
    apply hchar
    obtain ⟨y, hy, hF, hGG⟩ := hf w
    refine ⟨c • y, Submodule.smul_mem _ c hy, ?_, ?_⟩
    · convert Submodule.smul_mem _ c hF using 1; rw [map_smul, smul_sub]
    · convert Submodule.smul_mem _ c hGG using 1; rw [map_smul, map_smul, smul_sub]
  let fl : W →ₗ[K] W :=
    { toFun := f
      map_add' := hadd
      map_smul' := fun c w => by rw [RingHom.id_apply]; exact hsmul c w }
  have hiso : ∀ w₁ w₂, HW.B (f w₁) (f w₂) = HW.B w₁ w₂ := by
    intro w₁ w₂
    obtain ⟨y₁, hy₁, hF₁, hG₁⟩ := hf w₁
    obtain ⟨y₂, hy₂, hF₂, hG₂⟩ := hf w₂
    rw [← hE.1, ← hE.1]
    have e₁ : H.B y₁ y₂ = H.B (e (f w₁)) (e (f w₂)) :=
      B_mod (S := F.X) (hEX (f w₁)) (fun x hx => (hW y₂).1 hy₂ x (hFV0 hx)) hF₁ hF₂
    have e₂ : H.B y₁ y₂ = H.B (γ (e w₁)) (γ (e w₂)) :=
      B_mod (S := G.X) (hγX w₁) (fun x hx => (hW y₂).1 hy₂ x (hGV0 hx)) hG₁ hG₂
    rw [← e₁, e₂, hγB]
  have hinj : Function.Injective fl := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    apply HW.nondeg w
    intro w'
    have hw0 : f w = 0 := hw
    rw [← hiso w w', hw0, map_zero, LinearMap.zero_apply]
  set h := LinearEquiv.ofInjectiveEndo fl hinj with hh
  have hcoe : ∀ w, h w = f w := fun w => by
    rw [hh, LinearEquiv.coe_ofInjectiveEndo]; rfl
  refine ⟨h, ?_, ?_, ?_, ?_⟩
  · rw [mem_isomGrp]
    intro x y
    rw [hcoe, hcoe, hiso]
  · intro w
    rw [hcoe]
    exact hf w
  · intro h' hh'
    ext w
    rw [hcoe]
    exact (hchar w (h' w) (hh' w)).symm
  · intro g Λ'
    ext u
    obtain ⟨w, rfl⟩ : ∃ w, h w = u := ⟨h.symm u, h.apply_symm_apply u⟩
    obtain ⟨y, hy, hF, hGG⟩ := hf w
    rw [← hcoe] at hF
    have hR : h w ∈ imLat h (lat0 F e Λ') ↔ e w ∈ Λ' ⊔ rs (𝓞 K) F.X := by
      simp only [imLat, Formalism.HermitianLatticesTheory.gmap, lat0, Submodule.mem_map, Submodule.mem_comap,
        LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
      constructor
      · rintro ⟨w', hw', hww⟩
        rwa [h.injective hww] at hw'
      · intro hw
        exact ⟨w, hw, rfl⟩
    have hL : h w ∈ (datOf F G e g (γ • Λ')).1 ↔
        e (h w) ∈ flagPairDefinitePartLattice G F (γ • Λ') ⊔ rs (𝓞 K) F.X := Iff.rfl
    rw [hL, hR, ← sup_iff_lemma _ _ hF]
    have hV0c : V0 G F = V0 F G := by
      simp only [V0]
      rw [sup_comm G.X F.X, Set.pair_comm]
    have hWc : ∀ v, v ∈ wSp G F ↔ v ∈ wSp F G := fun v => by
      simp only [wSp, hV0c]
    have hS2 : y ∈ flagPairDefinitePartLattice G F (γ • Λ') ⊔ rs (𝓞 K) F.X ↔ y ∈ γ • Λ' ⊔ rs (𝓞 K) G.X := by
      constructor
      · intro hy'
        obtain ⟨l, hl, x, hx, hlx⟩ := Submodule.mem_sup.mp hy'
        have hl1 : l ∈ γ • Λ' ⊔ rs (𝓞 K) G.X := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hl).1).2
        have hl2 : l ∈ wSp F G := (hWc l).1 (Submodule.mem_inf.mp hl).2
        have hx' : x ∈ G.X := by
          have hxy : x = y - l := by rw [← hlx]; abel
          apply hA x hx
          rw [hxy]
          exact (hW _).1 (sub_mem hy hl2)
        rw [← hlx]
        exact add_mem hl1 (Submodule.mem_sup_right hx')
      · intro hy'
        apply Submodule.mem_sup_left
        refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, hy'⟩, (hWc y).2 hy⟩
        show y ∈ uPerp G F
        rw [uPerp, GlobalTheory.DegCnt.NFGeom.mem_perp']
        intro x hx
        apply (hW y).1 hy
        exact sup_le hGV0 hFV0 hx
    rw [hS2, sup_iff_lemma _ _ hGG]
    constructor
    · intro h1
      obtain ⟨m, hm, x, hx, hmx⟩ := Submodule.mem_sup.mp h1
      obtain ⟨l, hl, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hm
      rw [LinearEquiv.smul_def] at hmx
      have hx' : γ (e w - l) ∈ G.X := by
        rw [map_sub, ← hmx]; simpa using hx
      have : e w - l ∈ F.X := IndIsom.mem_of_map hG hx'
      have hsum : e w = l + (e w - l) := by abel
      rw [hsum]
      exact add_mem (Submodule.mem_sup_left hl) (Submodule.mem_sup_right this)
    · intro h1
      obtain ⟨l, hl, x, hx, hlx⟩ := Submodule.mem_sup.mp h1
      rw [← hlx, map_add]
      refine add_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (IndIsom.map_mem hG hx))
      rw [← LinearEquiv.smul_def]
      exact Submodule.smul_mem_pointwise_smul _ _ _ hl

end GlobalTheory.DegAsm
