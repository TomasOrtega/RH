import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.CoeffCongFactor
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsMoveMarked
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetFrameNeZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatchStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkingsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ComponentEqOfMatchedLatticesMarkingsStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.Setup

open GlobalTheory.SW.Lev

section Algebra

variable {O : Type} [CommRing O] {M V : Type} [AddCommGroup M] [Module O M] [AddCommGroup V] [Module O V]
  {r : ℕ} {𝔞 𝔟 : Ideal O} {L : Submodule O V} {δ : M →ₗ[O] V}

/- English proof (translation)
Establish `h (i) : ∃ b, v i - δ b ∈ 𝔞 • L`. Take `⟨_, ⟨b, rfl⟩, w, hw, e⟩` from `Submodule.mem_sup.1 (hon (hv i))`. Conclude with `⟨b, by rw [← e, add_sub_cancel_left]; exact hw⟩`. Use `choose b hb using h`. Use `⟨b, eq_top_iff.2 fun a _ => ?_⟩` and prove the remaining obligations.

Establish `h1 : L ≤ (Submodule.span O (Set.range b)).map δ ⊔ 𝔞 • L`. Use `hs.trans (sup_le (Submodule.span_le.2 ?_) le_sup_right)` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[← add_sub_cancel (δ (b i)) (v i)]`. Conclude with `Submodule.add_mem_sup ⟨b i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩ (hb i)`.

Take `⟨_, ⟨s, hs, rfl⟩, w, hw, e⟩` from `Submodule.mem_sup.1 (h1 (hδ a))`. Rewrite using `[← add_sub_cancel s a]`. Use `Submodule.add_mem_sup hs (hin _ ?_)` and prove the remaining obligations. Rewrite using `[map_sub, ← e, add_sub_cancel_left]`. Conclude with `hw`.
-/
theorem exists_lift_gens (hδ : ∀ a, δ a ∈ L) (hon : L ≤ LinearMap.range δ ⊔ 𝔞 • L)
    (hin : ∀ a, δ a ∈ 𝔞 • L → a ∈ 𝔞 • (⊤ : Submodule O M)) {v : Fin r → V} (hv : ∀ i, v i ∈ L)
    (hs : L ≤ Submodule.span O (Set.range v) ⊔ 𝔞 • L) :
    ∃ b : Fin r → M, Submodule.span O (Set.range b) ⊔ 𝔞 • (⊤ : Submodule O M) = ⊤ := by
  have h (i) : ∃ b, v i - δ b ∈ 𝔞 • L := by
    obtain ⟨_, ⟨b, rfl⟩, w, hw, e⟩ := Submodule.mem_sup.1 (hon (hv i))
    exact ⟨b, by rw [← e, add_sub_cancel_left]; exact hw⟩
  choose b hb using h
  refine ⟨b, eq_top_iff.2 fun a _ => ?_⟩
  have h1 : L ≤ (Submodule.span O (Set.range b)).map δ ⊔ 𝔞 • L := by
    refine hs.trans (sup_le (Submodule.span_le.2 ?_) le_sup_right)
    rintro _ ⟨i, rfl⟩
    rw [← add_sub_cancel (δ (b i)) (v i)]
    exact Submodule.add_mem_sup ⟨b i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩ (hb i)
  obtain ⟨_, ⟨s, hs, rfl⟩, w, hw, e⟩ := Submodule.mem_sup.1 (h1 (hδ a))
  rw [← add_sub_cancel s a]
  refine Submodule.add_mem_sup hs (hin _ ?_)
  rw [map_sub, ← e, add_sub_cancel_left]; exact hw

/- English proof (translation)
Establish `: (⊤ : Submodule O M) ≤ N.comap δ`. Rewrite using `[← hb]`. Use `sup_le (Submodule.span_le.2 ?_) fun x hx => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `h i`.

Use `Submodule.smul_induction_on hx (fun c hc y _ => ?_) fun y z hy hz => add_mem hy hz` and prove the remaining obligations. Rewrite using `[Submodule.mem_comap, map_smul]`. Conclude with `hN (Submodule.smul_mem_smul hc (hδ y))`. Conclude with `this trivial`.
-/
theorem mem_of_gens {N : Submodule O V} (hδ : ∀ a, δ a ∈ L) (hN : 𝔞 • L ≤ N) {b : Fin r → M}
    (hb : Submodule.span O (Set.range b) ⊔ 𝔞 • (⊤ : Submodule O M) = ⊤) (h : ∀ i, δ (b i) ∈ N) (a : M) :
    δ a ∈ N := by
  have : (⊤ : Submodule O M) ≤ N.comap δ := by
    rw [← hb]
    refine sup_le (Submodule.span_le.2 ?_) fun x hx => ?_
    · rintro _ ⟨i, rfl⟩; exact h i
    · refine Submodule.smul_induction_on hx (fun c hc y _ => ?_) fun y z hy hz => add_mem hy hz
      rw [Submodule.mem_comap, map_smul]
      exact hN (Submodule.smul_mem_smul hc (hδ y))
  exact this trivial

/- English proof (translation)
Take `⟨e, he, f, hf, hef⟩` from `Ideal.isCoprime_iff_exists.1 hc`. Set `u : Fin r → V` to `fun i => f • v i + e • w i`. Establish `e1 (i) : v i - u i = e • (v i - w i)`. Rewrite using `[show e = 1 - f from eq_sub_of_add_eq hef]`. Simplify using `only [u, show e = 1 - f from eq_sub_of_add_eq hef]`.

Use `module`. Establish `e2 (i) : w i - u i = f • (w i - v i)`. Simplify using `only [u, show e = 1 - f from eq_sub_of_add_eq hef]`. Use `module`. Establish `h1 (i) : v i - u i ∈ 𝔞 • L` using `e1 i ▸ Submodule.smul_mem_smul he (sub_mem (hv i) (hw i))`.

Establish `h2 (i) : w i - u i ∈ 𝔟 • L` using `e2 i ▸ Submodule.smul_mem_smul hf (sub_mem (hw i) (hv i))`. Establish `ha : L ≤ Submodule.span O (Set.range u) ⊔ 𝔞 • L` using `hv' _ le_sup_right fun i => by`. Rewrite using `[← add_sub_cancel (u i) (v i)]`. Conclude with `Submodule.add_mem_sup (Submodule.subset_span ⟨i, rfl⟩) (h1 i)`. Establish `hb : L ≤ Submodule.span O (Set.range u) ⊔ 𝔟 • L`.

Use `hw'.trans (sup_le (Submodule.span_le.2 ?_) le_sup_right)` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[← add_sub_cancel (u i) (w i)]`. Conclude with `Submodule.add_mem_sup (Submodule.subset_span ⟨i, rfl⟩) (h2 i)`. Use `⟨u, fun i => add_mem (L.smul_mem _ (hv i)) (L.smul_mem _ (hw i)), h1, fun x hx => ?_⟩` and prove the remaining obligations.

Take `⟨s, hs, y, hy, ey⟩` from `Submodule.mem_sup.1 (ha hx)`. Take `⟨t, ht, z, hz, ez⟩` from `Submodule.mem_sup.1 (hb hx)`. Establish `: x = (e • t + f • s) + (e • z + f • y)` using `by conv_lhs => rw [← one_smul O x, ← hef, add_smul] conv_lhs => enter [1]; rw [← ez] conv_lhs => enter [2]; rw [← ey] module`. Rewrite using `[this]`. Use `Submodule.add_mem_sup (add_mem (Submodule.smul_mem _ _ ht) (Submodule.smul_mem _ _ hs)) (add_mem ?_ ?_)` and prove the remaining obligations.

Rewrite using `[Submodule.mul_smul]`. Conclude with `Submodule.smul_mem_smul he hz`. Rewrite using `[mul_comm, Submodule.mul_smul]`. Conclude with `Submodule.smul_mem_smul hf hy`.
-/
theorem exists_glue_gens (hc : IsCoprime 𝔞 𝔟) {v w : Fin r → V} (hv : ∀ i, v i ∈ L) (hw : ∀ i, w i ∈ L)
    (hv' : ∀ N, 𝔞 • L ≤ N → (∀ i, v i ∈ N) → L ≤ N) (hw' : L ≤ Submodule.span O (Set.range w) ⊔ 𝔟 • L) :
    ∃ u : Fin r → V, (∀ i, u i ∈ L) ∧ (∀ i, v i - u i ∈ 𝔞 • L) ∧
      L ≤ Submodule.span O (Set.range u) ⊔ (𝔞 * 𝔟) • L := by
  obtain ⟨e, he, f, hf, hef⟩ := Ideal.isCoprime_iff_exists.1 hc
  let u : Fin r → V := fun i => f • v i + e • w i
  have e1 (i) : v i - u i = e • (v i - w i) := by
    rw [show e = 1 - f from eq_sub_of_add_eq hef]
    simp only [u, show e = 1 - f from eq_sub_of_add_eq hef]
    module
  have e2 (i) : w i - u i = f • (w i - v i) := by
    simp only [u, show e = 1 - f from eq_sub_of_add_eq hef]
    module
  have h1 (i) : v i - u i ∈ 𝔞 • L := e1 i ▸ Submodule.smul_mem_smul he (sub_mem (hv i) (hw i))
  have h2 (i) : w i - u i ∈ 𝔟 • L := e2 i ▸ Submodule.smul_mem_smul hf (sub_mem (hw i) (hv i))
  have ha : L ≤ Submodule.span O (Set.range u) ⊔ 𝔞 • L := hv' _ le_sup_right fun i => by
    rw [← add_sub_cancel (u i) (v i)]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨i, rfl⟩) (h1 i)
  have hb : L ≤ Submodule.span O (Set.range u) ⊔ 𝔟 • L := by
    refine hw'.trans (sup_le (Submodule.span_le.2 ?_) le_sup_right)
    rintro _ ⟨i, rfl⟩
    rw [← add_sub_cancel (u i) (w i)]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨i, rfl⟩) (h2 i)
  refine ⟨u, fun i => add_mem (L.smul_mem _ (hv i)) (L.smul_mem _ (hw i)), h1, fun x hx => ?_⟩
  obtain ⟨s, hs, y, hy, ey⟩ := Submodule.mem_sup.1 (ha hx)
  obtain ⟨t, ht, z, hz, ez⟩ := Submodule.mem_sup.1 (hb hx)
  have : x = (e • t + f • s) + (e • z + f • y) := by
    conv_lhs => rw [← one_smul O x, ← hef, add_smul]
    conv_lhs => enter [1]; rw [← ez]
    conv_lhs => enter [2]; rw [← ey]
    module
  rw [this]
  refine Submodule.add_mem_sup (add_mem (Submodule.smul_mem _ _ ht) (Submodule.smul_mem _ _ hs)) (add_mem ?_ ?_)
  · rw [Submodule.mul_smul]; exact Submodule.smul_mem_smul he hz
  · rw [mul_comm, Submodule.mul_smul]; exact Submodule.smul_mem_smul hf hy

end Algebra

end GlobalTheory.Dict.Setup

namespace GlobalTheory.Dict.Setup

open GlobalTheory.SW.Lev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X X' : Data E r}

/- English proof (translation)
Use function extensionality and compare the values at `u v`. Unfold `GlobalTheory.ThFr.EF`. Rewrite using `[h.ka, h.gm]`.
-/
theorem ef_eq (h : SameSp X X') : EF X = EF X' := by
  funext u v
  unfold GlobalTheory.ThFr.EF
  rw [h.ka, h.gm]

/- English proof (translation)
Unfold `SelfD at hL ⊢`. Rewrite using `[← ef_eq h]` and apply the resulting hypothesis.
-/
theorem selfD_of_same (h : SameSp X X') {L : Lt E r} (hL : SelfD X L) : SelfD X' L := by
  unfold SelfD at hL ⊢
  rwa [← ef_eq h]

/- English proof (translation)
Unfold `IsUn at hu ⊢`. Rewrite using `[h.gm]` and apply the resulting hypothesis.
-/
theorem isUn_of_same (h : SameSp X X') {ga : GL (Fin r) E} (hu : IsUn X' ga) : IsUn X ga := by
  unfold IsUn at hu ⊢
  rwa [h.gm]

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.psi.trans h'.psi.symm, h.gm.trans h'.gm.symm, h.p0.trans h'.p0.symm, h.xi.trans h'.xi.symm, h.ka.trans h'.ka.symm⟩`.
-/
theorem sameSp_trans_symm {X'' : Data E r} (h : SameSp X X'') (h' : SameSp X' X'') : SameSp X X' :=
  ⟨h.psi.trans h'.psi.symm, h.gm.trans h'.gm.symm, h.p0.trans h'.p0.symm, h.xi.trans h'.xi.symm,
    h.ka.trans h'.ka.symm⟩

variable {M : Type} [AddCommGroup M] [Module (𝓞 E) M] {𝔞 𝔟 : Ideal (𝓞 E)}

/- English proof (translation)
Establish `hle : D.𝔪 ≤ 𝔞` using `hm.le.trans Ideal.mul_le_left`. Establish `h0 : 𝔟 ≠ ⊥` using `fun e => D.ne_bot (by rw [hm, e, Ideal.mul_bot])`. Take `⟨w, hw, hw'⟩` from `TieModel.exists_gens h0 r L hL.1`. Take `⟨u, hu, h1, h2⟩` from `exists_glue_gens hc (v := fun i => p • δ (b i)) (fun i => L.smul_mem _ (hδ _)) hw (fun N hN h => hon.trans (sup_le (by`. Introduce and unpack `_ ⟨a, rfl⟩`.

Conclude with `mem_of_gens hδ hN hb (fun i => mem_of_loc (hδ _) hN ⟨p, hp, h i⟩) a) hN)) hw'`. Take `⟨ga, hun, hl, hcg⟩` from `exists_move_marked E r X D L u hΛ hL hu (hm ▸ h2)`. Use `⟨ga, hun, hl, fun i => cong_trans ?_ (TieModel.cong_mono hle (hcg i))⟩` and prove the remaining obligations. Take `⟨-, s, hs, hLΛ, -⟩` from `hl`. Use `⟨s, Stab.cop_mono hle hs.of_mul_right_left, ?_⟩` and prove the remaining obligations.

Rewrite using `[← lin_apply, ← map_smul, ← map_sub]`. Conclude with `smul_map_mem (lin ga) (fun v hv => hLΛ _ ⟨v, hv, rfl⟩) (h1 i)`.
-/
theorem exists_move (D : SW.Level X) (hm : D.𝔪 = 𝔞 * 𝔟) (hc : IsCoprime 𝔞 𝔟) (hΛ : SelfD X X.Λ) {L : Lt E r}
    (hL : SelfD X L) {δ : M →ₗ[𝓞 E] (Fin r → E)} (hδ : ∀ a, δ a ∈ L) (hon : L ≤ LinearMap.range δ ⊔ 𝔞 • L)
    {b : Fin r → M} (hb : Submodule.span (𝓞 E) (Set.range b) ⊔ 𝔞 • (⊤ : Submodule (𝓞 E) M) = ⊤)
    {p : 𝓞 E} (hp : IsCoprime (Ideal.span {p}) 𝔞) :
    ∃ ga : GL (Fin r) E, IsUn X ga ∧ mapL ga L ∈ D.lats ∧ ∀ i, Cong X 𝔞 (p • lin ga (δ (b i))) (D.β i) := by
  have hle : D.𝔪 ≤ 𝔞 := hm.le.trans Ideal.mul_le_left
  have h0 : 𝔟 ≠ ⊥ := fun e => D.ne_bot (by rw [hm, e, Ideal.mul_bot])
  obtain ⟨w, hw, hw'⟩ := TieModel.exists_gens h0 r L hL.1
  obtain ⟨u, hu, h1, h2⟩ := exists_glue_gens hc (v := fun i => p • δ (b i)) (fun i => L.smul_mem _ (hδ _)) hw
    (fun N hN h => hon.trans (sup_le (by
      rintro _ ⟨a, rfl⟩
      exact mem_of_gens hδ hN hb (fun i => mem_of_loc (hδ _) hN ⟨p, hp, h i⟩) a) hN)) hw'
  obtain ⟨ga, hun, hl, hcg⟩ := exists_move_marked E r X D L u hΛ hL hu (hm ▸ h2)
  refine ⟨ga, hun, hl, fun i => cong_trans ?_ (TieModel.cong_mono hle (hcg i))⟩
  obtain ⟨-, s, hs, hLΛ, -⟩ := hl
  refine ⟨s, Stab.cop_mono hle hs.of_mul_right_left, ?_⟩
  rw [← lin_apply, ← map_smul, ← map_sub]
  exact smul_map_mem (lin ga) (fun v hv => hLΛ _ ⟨v, hv, rfl⟩) (h1 i)

/- English proof (translation)
Take `⟨-, s, hs, -, hΛL⟩` from `hL`. Use `mem_of_gens (δ := δ - δ') (fun a => sub_mem (hδ a) (hδ' a)) le_rfl hb (fun i => ?_) a` and prove the remaining obligations. Use `mem_of_loc (sub_mem (hδ _) (hδ' _)) le_rfl (loc_loc hp ?_)` and prove the remaining obligations. Take `⟨t, ht, h⟩` from `h i`. Use `loc_loc ht ⟨s, Stab.cop_mono hle hs.of_mul_right_left, ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.sub_apply, smul_sub p]`. Conclude with `smul_map_mem LinearMap.id hΛL h`.
-/
theorem sub_mem_of_cong (D : SW.Level X) (hle : D.𝔪 ≤ 𝔞) {L : Lt E r} (hL : L ∈ D.lats)
    {δ δ' : M →ₗ[𝓞 E] (Fin r → E)} (hδ : ∀ a, δ a ∈ L) (hδ' : ∀ a, δ' a ∈ L)
    {b : Fin r → M} (hb : Submodule.span (𝓞 E) (Set.range b) ⊔ 𝔞 • (⊤ : Submodule (𝓞 E) M) = ⊤)
    {p : 𝓞 E} (hp : IsCoprime (Ideal.span {p}) 𝔞) (h : ∀ i, Cong X 𝔞 (p • δ (b i)) (p • δ' (b i))) (a : M) :
    δ a - δ' a ∈ 𝔞 • L := by
  obtain ⟨-, s, hs, -, hΛL⟩ := hL
  refine mem_of_gens (δ := δ - δ') (fun a => sub_mem (hδ a) (hδ' a)) le_rfl hb (fun i => ?_) a
  refine mem_of_loc (sub_mem (hδ _) (hδ' _)) le_rfl (loc_loc hp ?_)
  obtain ⟨t, ht, h⟩ := h i
  refine loc_loc ht ⟨s, Stab.cop_mono hle hs.of_mul_right_left, ?_⟩
  rw [LinearMap.sub_apply, smul_sub p]
  exact smul_map_mem LinearMap.id hΛL h

end GlobalTheory.Dict.Setup

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c n d σ r U hσ hU hr hA hd W k₀ hs ph D hn hT`. Establish `hζ : IsPrimitiveRoot (σ (zetaM c)) l.M` using `(GlobalTheory.LevelPairing.zetaM_prim c).map_of_injective σ.injective`. Establish `hL (k) : SelfD (U.X k₀) (U.X k).Λ` using `Setup.selfD_of_same (hs k) (GlobalTheory.T.uniformisation_component_lattices_markings E H Dw l Xo c σ r U hσ hU hr W k).2.1`. Establish `hmk (k) : IsMark l (U.X k).Λ (W.mark k)` using `(GlobalTheory.T.uniformisation_component_lattices_markings E H Dw l Xo c σ r U hσ hU hr W k).2.2.1`. Establish `hdual (k)` using `GlobalTheory.T.dual_half_level_marking_exists_and_match E H Dw l r (U.X k₀) _ _ _ (hL k) (hmk k) hζ`.

Use `choose δ hδ using fun k => (hdual k).1`. Establish `hle : D.𝔪 ≤ Mfr l` using `hT.prod.le.trans Ideal.mul_le_left`. Establish `hp : IsCoprime (Ideal.span {(d.pd : 𝓞 E)}) (Mfr l)`. Take `⟨a, b, e⟩` from `(Nat.isCoprime_iff_coprime.2 hd.2.2.1).map (Int.castRingHom (𝓞 E))`. Conclude with `Lev.cop_iff.2 ⟨a, _, Ideal.mul_mem_left _ b (TieModel.m_mem l), by simpa using e⟩`.

Take `⟨b, hb⟩` from `Setup.exists_lift_gens (hδ k₀).mem ((hdual k₀).2.1 _ (hδ k₀)).1 (fun a => (((hdual k₀).2.1 _ (hδ k₀)).2.1 a).1) D.β_mem (D.β_span.trans (sup_le_sup_left (Submodule.smul_mono hle le_rfl) _))`. Use `choose ga hun hl hcg using fun k => Setup.exists_move D hT.prod hT.cop (hL k₀) (hL k) (hδ k).mem ((hdual k).2.1 _ (hδ k)).1 hb hp`. Establish `hmv (k)` using `((hdual k).2.1 _ (hδ k)).2.2.1 (ga k) (hun k)`. Use `⟨fun j => if h : (j : ℕ) < r then b ⟨j, h⟩ else 0, ga, fun k => mvMap (ga k) (δ k), fun rk => ?_, fun k => ⟨hun k, hl k, (hmv k).1, (hmv k).2, fun i => ?_, fun j hj => ?_⟩, fun k k' g' hg' e => ?_⟩` and prove the remaining obligations. Rewrite using `[AdmX, eq_top_iff]`.

Use `hb.ge.trans (sup_le_sup_right (Submodule.span_mono ?_) _)` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨Fin.castLE hn i, Or.inr (hU.1 ▸ i.2), dif_pos i.2⟩`. Establish `e : (if h : ((Fin.castLE hn i : Fin n) : ℕ) < r then b ⟨Fin.castLE hn i, h⟩ else 0) = b i` using `dif_pos i.2 beta_reduce`. Rewrite using `[e, ← Nat.cast_smul_eq_nsmul (𝓞 E)]`.

Conclude with `hcg k i`. Use `beta_reduce`. Rewrite using `[dif_neg (not_lt.2 hj)]`. Conclude with `zero_mem _`. Take `⟨hu', kk, -, hred⟩` from `(Lev.mem_grp g').1 hg'`.

Take `⟨s, hs', hk, -⟩` from `Lev.keeps hred`. Establish `h1` using `((GlobalTheory.T.dual_half_level_marking_exists_and_match E H Dw l r (U.X k₀) _ _ _ (hl k).1 (hmv k).1 hζ).2.1 _ (hmv k).2).2.2.1 g' hu'`. Rewrite `h1` using `[e]`. Establish `h2` using `Setup.sub_mem_of_cong D hle (hl k') h1.2.mem (hmv k').2.mem hb hp fun i => by`. Use `Lev.cong_trans ?_ (Lev.cong_symm (hcg k' i))` and prove the remaining obligations.

Use `Lev.cong_trans ?_ (Stab.cong_frame hle (fun k hk => (hT.grp k).1 hk) hg' i)` and prove the remaining obligations. Use `Lev.cong_lin (Stab.cop_mono hle hs') hk (hcg k i)` as an intermediate fact. Rewrite `this` using `[map_smul]`. Then use the resulting hypothesis. Establish `h3` using `((GlobalTheory.T.dual_half_level_marking_exists_and_match E H Dw l r (U.X k₀) _ _ _ (hl k').1 h1.1 hζ).2.1 _ h1.2).2.2.2 _ _ (hmv k').1 (hmv k').2 h2`. Use `GlobalTheory.T.component_eq_of_matched_lattices_markings E H Dw l Xo c σ r U hσ hU hr hA W k k' (Setup.sameSp_trans_symm (hs k) (hs k')) ((ga k')⁻¹ * (g' * ga k)) (Setup.isUn_of_same (hs k) (Lev.isUn_mul (Lev.isUn_inv (hun k')) (Lev.isUn_mul hu' (hun k)))) ?_ fun a ha => ?_` and prove the remaining obligations.

Use extensionality with `v`. Use `SetLike.ext_iff.1 e (Lev.lin (ga k') v)` as an intermediate fact. Rewrite `this` using `[Lev.mem_mapL, Lev.mem_mapL, Lev.mem_mapL, Lev.lin_inv]`. Rewrite using `[← this, Lev.mem_mapL, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, Lev.lin_mul, Lev.lin_mul]`. Take `⟨u, hu, e'⟩` from `h3 a ha`.

Use `⟨_, Lev.mem_mapL.1 hu, ?_⟩` and prove the remaining obligations. Rewrite using `[← Lev.lin_apply, Lev.lin_mul, Lev.lin_mul]`. Establish `e'' : Lev.lin g' (Lev.lin (ga k) (W.mark k a)) = Lev.lin (ga k') (W.mark k' a) + l.M • u` using `e'`. Rewrite using `[e'', map_add, Lev.lin_inv, map_nsmul]`.
-/
theorem GlobalTheory.Dict.exists_components_tied : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → l.A = 1 → d.IsLev → ∀ (W : UW U) (k₀ : U.Comp), (∀ k, SameSp (U.X k) (U.X k₀)) → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (D : SW.Level (U.X k₀)) (hn : r ≤ n), LevTie d σ ph D hn → ∃ (x0 : Fin n → Dw.La) (ga : U.Comp → GL (Fin r) E) (δ : U.Comp → (Dw.La →ₗ[𝓞 E] (Fin r → E))), (∀ rk, AdmX (l := l) rk x0) ∧ (∀ k, IsUn (U.X k₀) (ga k) ∧ mapL (ga k) (U.X k).Λ ∈ D.lats ∧ IsMark l (mapL (ga k) (U.X k).Λ) (mvMap (ga k) (W.mark k)) ∧ IsDual (U.X k₀) l (σ (zetaM c)) (mapL (ga k) (U.X k).Λ) (mvMap (ga k) (W.mark k)) (δ k) ∧ IsBaseClassLevelAdapted d D hn x0 (δ k)) ∧ ∀ k k', ∀ g' ∈ D.grp, mapL g' (mapL (ga k) (U.X k).Λ) = mapL (ga k') (U.X k').Λ → k = k' := by
  intro E _ _ _ H Dw l Xo c n d σ r U hσ hU hr hA hd W k₀ hs ph D hn hT
  have hζ : IsPrimitiveRoot (σ (zetaM c)) l.M :=
    (GlobalTheory.LevelPairing.zetaM_prim c).map_of_injective σ.injective
  have hL (k) : SelfD (U.X k₀) (U.X k).Λ :=
    Setup.selfD_of_same (hs k) (GlobalTheory.T.uniformisation_component_lattices_markings E H Dw l Xo c σ r U hσ hU hr W k).2.1
  have hmk (k) : IsMark l (U.X k).Λ (W.mark k) := (GlobalTheory.T.uniformisation_component_lattices_markings E H Dw l Xo c σ r U hσ hU hr W k).2.2.1
  have hdual (k) := GlobalTheory.T.dual_half_level_marking_exists_and_match E H Dw l r (U.X k₀) _ _ _ (hL k) (hmk k) hζ
  choose δ hδ using fun k => (hdual k).1
  have hle : D.𝔪 ≤ Mfr l := hT.prod.le.trans Ideal.mul_le_left
  have hp : IsCoprime (Ideal.span {(d.pd : 𝓞 E)}) (Mfr l) := by
    obtain ⟨a, b, e⟩ := (Nat.isCoprime_iff_coprime.2 hd.2.2.1).map (Int.castRingHom (𝓞 E))
    exact Lev.cop_iff.2 ⟨a, _, Ideal.mul_mem_left _ b (TieModel.m_mem l), by simpa using e⟩
  obtain ⟨b, hb⟩ := Setup.exists_lift_gens (hδ k₀).mem ((hdual k₀).2.1 _ (hδ k₀)).1
    (fun a => (((hdual k₀).2.1 _ (hδ k₀)).2.1 a).1) D.β_mem
    (D.β_span.trans (sup_le_sup_left (Submodule.smul_mono hle le_rfl) _))
  choose ga hun hl hcg using fun k => Setup.exists_move D hT.prod hT.cop (hL k₀) (hL k) (hδ k).mem
    ((hdual k).2.1 _ (hδ k)).1 hb hp
  have hmv (k) := ((hdual k).2.1 _ (hδ k)).2.2.1 (ga k) (hun k)
  refine ⟨fun j => if h : (j : ℕ) < r then b ⟨j, h⟩ else 0, ga, fun k => mvMap (ga k) (δ k), fun rk => ?_,
    fun k => ⟨hun k, hl k, (hmv k).1, (hmv k).2, fun i => ?_, fun j hj => ?_⟩, fun k k' g' hg' e => ?_⟩
  · rw [AdmX, eq_top_iff]
    refine hb.ge.trans (sup_le_sup_right (Submodule.span_mono ?_) _)
    rintro _ ⟨i, rfl⟩
    exact ⟨Fin.castLE hn i, Or.inr (hU.1 ▸ i.2), dif_pos i.2⟩
  · have e : (if h : ((Fin.castLE hn i : Fin n) : ℕ) < r then b ⟨Fin.castLE hn i, h⟩ else 0) = b i := dif_pos i.2
    beta_reduce
    rw [e, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact hcg k i
  · beta_reduce
    rw [dif_neg (not_lt.2 hj)]
    exact zero_mem _
  · obtain ⟨hu', kk, -, hred⟩ := (Lev.mem_grp g').1 hg'
    obtain ⟨s, hs', hk, -⟩ := Lev.keeps hred
    have h1 := ((GlobalTheory.T.dual_half_level_marking_exists_and_match E H Dw l r (U.X k₀) _ _ _ (hl k).1 (hmv k).1 hζ).2.1 _ (hmv k).2).2.2.1 g' hu'
    rw [e] at h1
    have h2 := Setup.sub_mem_of_cong D hle (hl k') h1.2.mem (hmv k').2.mem hb hp fun i => by
      refine Lev.cong_trans ?_ (Lev.cong_symm (hcg k' i))
      refine Lev.cong_trans ?_ (Stab.cong_frame hle (fun k hk => (hT.grp k).1 hk) hg' i)
      have := Lev.cong_lin (Stab.cop_mono hle hs') hk (hcg k i)
      rwa [map_smul] at this
    have h3 := ((GlobalTheory.T.dual_half_level_marking_exists_and_match E H Dw l r (U.X k₀) _ _ _ (hl k').1 h1.1 hζ).2.1 _ h1.2).2.2.2 _ _
      (hmv k').1 (hmv k').2 h2
    refine GlobalTheory.T.component_eq_of_matched_lattices_markings E H Dw l Xo c σ r U hσ hU hr hA W k k' (Setup.sameSp_trans_symm (hs k) (hs k'))
      ((ga k')⁻¹ * (g' * ga k))
      (Setup.isUn_of_same (hs k) (Lev.isUn_mul (Lev.isUn_inv (hun k')) (Lev.isUn_mul hu' (hun k)))) ?_
      fun a ha => ?_
    · ext v
      have := SetLike.ext_iff.1 e (Lev.lin (ga k') v)
      rw [Lev.mem_mapL, Lev.mem_mapL, Lev.mem_mapL, Lev.lin_inv] at this
      rw [← this, Lev.mem_mapL, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, Lev.lin_mul, Lev.lin_mul]
    · obtain ⟨u, hu, e'⟩ := h3 a ha
      refine ⟨_, Lev.mem_mapL.1 hu, ?_⟩
      rw [← Lev.lin_apply, Lev.lin_mul, Lev.lin_mul]
      have e'' : Lev.lin g' (Lev.lin (ga k) (W.mark k a)) = Lev.lin (ga k') (W.mark k' a) + l.M • u := e'
      rw [e'', map_add, Lev.lin_inv, map_nsmul]
