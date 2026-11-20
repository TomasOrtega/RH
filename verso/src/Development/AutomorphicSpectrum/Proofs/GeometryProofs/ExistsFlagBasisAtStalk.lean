import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSubFibreSubFib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinrankFiniteFlatTorsionSubschemeEqCardPoints
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsConstStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceDecompositionInternalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFrames

/- English proof (translation)
Establish `hact : ∀ (t : I) (a : O) (e : Li), e ∈ eigSp ρ (σ t) → ρ a e = σ t a • e`. Introduce `t a e he`. Use `(Submodule.mem_iInf _).1 he a` as an intermediate fact. Simplify `this` using `[sub_eq_zero]`. Establish `hRs : ∀ (r : Ω), r ∈ R → ∀ e ∈ Λ, r • e ∈ Λ` using `fun r hr e he => Λ.smul_mem ⟨r, hr⟩ he`.

Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert u T hu ih`. Introduce `x hx hs`. Rewrite `hs` using `[Finset.sum_insert hu]`.

Establish `hT : ∀ t ∈ T, x t ∈ Λ`. Introduce `t ht`. Establish `hne : t ≠ u` using `fun h => hu (h ▸ ht)`. Take `⟨a, ha⟩` from `hsep t u hne`. Establish `h1 : ρ a (x u + ∑ t ∈ T, x t) - σ u a • (x u + ∑ t ∈ T, x t) ∈ Λ` using `Λ.sub_mem (hst a _ hs) (hRs _ (hval u a) _ hs)`.

Establish `h2 : ρ a (x u + ∑ t ∈ T, x t) - σ u a • (x u + ∑ t ∈ T, x t) = ∑ t ∈ T, (σ t a - σ u a) • x t`. Rewrite using `[map_add, map_sum, hact u a _ (hx u), smul_add, Finset.smul_sum]`. Rewrite using `[add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[hact t a _ (hx t), sub_smul]`.

Rewrite `h1` using `[h2]`. Establish `h3` using `ih (fun t => (σ t a - σ u a) • x t) (fun t => (eigSp ρ (σ t)).smul_mem _ (hx t)) h1 t ht`. Establish `h4` using `hRs _ (hinv t u a ha) _ h3`. Rewrite `h4` using `[smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 ha), one_smul]`. Then use the resulting hypothesis. Establish `hu' : x u ∈ Λ`.

Use `Λ.sub_mem hs (Λ.sum_mem hT)` as an intermediate fact. Simplify using `using this`. Introduce `t ht`. Break down `Finset.mem_insert.1 ht with rfl | ht` into its components or cases. Conclude with `hu'`.

Conclude with `hT t ht`.
-/
theorem mem_of_sum_mem {Ω : Type} [Field Ω] (R : Subring Ω) {Li : Type} [AddCommGroup Li] [Module Ω Li]
    {O : Type} [CommRing O] (ρ : O →+* Module.End Ω Li) {I : Type} [DecidableEq I] (σ : I → (O →+* Ω))
    (Λ : Submodule R Li) (hst : ∀ a, ∀ e ∈ Λ, ρ a e ∈ Λ) (hval : ∀ s a, σ s a ∈ R)
    (hinv : ∀ s s' a, σ s a ≠ σ s' a → (σ s a - σ s' a)⁻¹ ∈ R)
    (hsep : ∀ s s', s ≠ s' → ∃ a, σ s a ≠ σ s' a) (T : Finset I) :
    ∀ x : I → Li, (∀ t, x t ∈ eigSp ρ (σ t)) → ∑ t ∈ T, x t ∈ Λ → ∀ t ∈ T, x t ∈ Λ := by
  have hact : ∀ (t : I) (a : O) (e : Li), e ∈ eigSp ρ (σ t) → ρ a e = σ t a • e := by
    intro t a e he
    have := (Submodule.mem_iInf _).1 he a
    simpa [sub_eq_zero] using this
  have hRs : ∀ (r : Ω), r ∈ R → ∀ e ∈ Λ, r • e ∈ Λ := fun r hr e he => Λ.smul_mem ⟨r, hr⟩ he
  induction T using Finset.induction_on with
  | empty => simp
  | insert u T hu ih =>
    intro x hx hs
    rw [Finset.sum_insert hu] at hs
    have hT : ∀ t ∈ T, x t ∈ Λ := by
      intro t ht
      have hne : t ≠ u := fun h => hu (h ▸ ht)
      obtain ⟨a, ha⟩ := hsep t u hne
      have h1 : ρ a (x u + ∑ t ∈ T, x t) - σ u a • (x u + ∑ t ∈ T, x t) ∈ Λ :=
        Λ.sub_mem (hst a _ hs) (hRs _ (hval u a) _ hs)
      have h2 : ρ a (x u + ∑ t ∈ T, x t) - σ u a • (x u + ∑ t ∈ T, x t) =
          ∑ t ∈ T, (σ t a - σ u a) • x t := by
        rw [map_add, map_sum, hact u a _ (hx u), smul_add, Finset.smul_sum]
        rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [hact t a _ (hx t), sub_smul]
      rw [h2] at h1
      have h3 := ih (fun t => (σ t a - σ u a) • x t)
        (fun t => (eigSp ρ (σ t)).smul_mem _ (hx t)) h1 t ht
      have h4 := hRs _ (hinv t u a ha) _ h3
      rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 ha), one_smul] at h4
    have hu' : x u ∈ Λ := by
      have := Λ.sub_mem hs (Λ.sum_mem hT)
      simpa using this
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact hu'
    · exact hT t ht

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `e he`. Establish `hm : e ∈ ⨆ s, eigSp ρ (σ s)` using `hspan ▸ Submodule.mem_top`. Take `⟨f, hf, rfl⟩` from `(Submodule.mem_iSup_iff_exists_finsupp _ _).1 hm`. Use `Submodule.sum_mem _ fun t ht => ?_` and prove the remaining obligations.

Establish `h1` using `mem_of_sum_mem R ρ σ Λ hst hval hinv hsep f.support f hf he t ht`. Establish `h2 : f t ∈ Submodule.span R (Set.range (b t))`. Rewrite using `[← hb t]`. Conclude with `⟨h1, hf t⟩`. Use `Submodule.span_mono ?_ h2` and prove the remaining obligations.

Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `⟨⟨t, k⟩, rfl⟩`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨s, k⟩, rfl⟩`. Establish `: b s k ∈ Λ ⊓ (eigSp ρ (σ s)).restrictScalars R`.

Rewrite using `[hb s]`. Conclude with `Submodule.subset_span ⟨k, rfl⟩`. Conclude with `this.1`.
-/
theorem eq_span_sigma {Ω : Type} [Field Ω] (R : Subring Ω) {Li : Type} [AddCommGroup Li] [Module Ω Li]
    {O : Type} [CommRing O] (ρ : O →+* Module.End Ω Li) {I : Type} [DecidableEq I] (σ : I → (O →+* Ω))
    (Λ : Submodule R Li) (hst : ∀ a, ∀ e ∈ Λ, ρ a e ∈ Λ) (hval : ∀ s a, σ s a ∈ R)
    (hinv : ∀ s s' a, σ s a ≠ σ s' a → (σ s a - σ s' a)⁻¹ ∈ R)
    (hsep : ∀ s s', s ≠ s' → ∃ a, σ s a ≠ σ s' a)
    (hspan : ⨆ s, eigSp ρ (σ s) = ⊤) {r : I → ℕ} (b : ∀ s, Fin (r s) → Li)
    (hb : ∀ s, Λ ⊓ (eigSp ρ (σ s)).restrictScalars R = Submodule.span R (Set.range (b s))) :
    Λ = Submodule.span R (Set.range fun q : Σ s, Fin (r s) => b q.1 q.2) := by
  apply le_antisymm
  · intro e he
    have hm : e ∈ ⨆ s, eigSp ρ (σ s) := hspan ▸ Submodule.mem_top
    obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hm
    refine Submodule.sum_mem _ fun t ht => ?_
    have h1 := mem_of_sum_mem R ρ σ Λ hst hval hinv hsep f.support f hf he t ht
    have h2 : f t ∈ Submodule.span R (Set.range (b t)) := by
      rw [← hb t]
      exact ⟨h1, hf t⟩
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨t, k⟩, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨s, k⟩, rfl⟩
    have : b s k ∈ Λ ⊓ (eigSp ρ (σ s)).restrictScalars R := by
      rw [hb s]
      exact Submodule.subset_span ⟨k, rfl⟩
    exact this.1

/- English proof (translation)
Take `⟨w, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun R).1 h2`. Take `⟨l, hl, hle⟩` from `(Finsupp.mem_span_image_iff_linearCombination Ω).1 h1`. Establish `hc : l = Finsupp.equivFunOnFinite.symm (fun k => (w k : Ω))`. Apply `hli` to reduce the goal to its premises. Rewrite using `[hle, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]`.

Conclude with `Finset.sum_congr rfl fun k _ => rfl`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : (k : ℕ) < i`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)`. Establish `h0 : l k = 0`.

Assume the negation of the conclusion as `h`. Conclude with `hk (hl (Finsupp.mem_support_iff.2 h))`. Establish `hw : w k = 0`. Rewrite `h0` using `[hc]`. Conclude with `Subtype.ext h0`.

Rewrite using `[hw, zero_smul]`. Conclude with `Submodule.zero_mem _`.
-/
theorem mem_span_image_of_mem_flagStep {Ω : Type} [Field Ω] (R : Subring Ω) {Li : Type} [AddCommGroup Li]
    [Module Ω Li] {r : ℕ} (b : Fin r → Li) (hli : LinearIndependent Ω b) (i : ℕ) {e : Li}
    (h1 : e ∈ flagStep Ω b i) (h2 : e ∈ Submodule.span R (Set.range b)) :
    e ∈ Submodule.span R (b '' {k | (k : ℕ) < i}) := by
  obtain ⟨w, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 h2
  obtain ⟨l, hl, hle⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).1 h1
  have hc : l = Finsupp.equivFunOnFinite.symm (fun k => (w k : Ω)) := by
    apply hli
    rw [hle, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
    exact Finset.sum_congr rfl fun k _ => rfl
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : (k : ℕ) < i
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
  · have h0 : l k = 0 := by
      by_contra h
      exact hk (hl (Finsupp.mem_support_iff.2 h))
    have hw : w k = 0 := by
      rw [hc] at h0
      exact Subtype.ext h0
    rw [hw, zero_smul]
    exact Submodule.zero_mem _

section Geo

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

/- English proof (translation)
Take `⟨u, hu⟩` from `hu n hn`. Establish `h1 : genMap ξ p u = (n : Ω)` using `by rw [hu, map_natCast]`. Establish `h0 : (n : Ω) ≠ 0` using `Nat.cast_ne_zero.2 hn`. Use `⟨h0, RingHom.mem_range.2 ⟨u, h1⟩, RingHom.mem_range.2 ⟨(↑u⁻¹ : X.presheaf.stalk p.1), ?_⟩⟩` and prove the remaining obligations. Establish `h2 : genMap ξ p (↑u⁻¹ : X.presheaf.stalk p.1) * (n : Ω) = 1`.

Rewrite using `[← h1, ← map_mul, Units.inv_mul, map_one]`. Conclude with `eq_inv_of_mul_eq_one_left h2`.
-/
theorem unitAt_natCast [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ)
    (hu : ∀ n : ℕ, n ≠ 0 → IsUnit ((n : X.presheaf.stalk p.1))) (n : ℕ) (hn : n ≠ 0) : unitAt ξ p (n : Ω) := by
  obtain ⟨u, hu⟩ := hu n hn
  have h1 : genMap ξ p u = (n : Ω) := by rw [hu, map_natCast]
  have h0 : (n : Ω) ≠ 0 := Nat.cast_ne_zero.2 hn
  refine ⟨h0, RingHom.mem_range.2 ⟨u, h1⟩, RingHom.mem_range.2 ⟨(↑u⁻¹ : X.presheaf.stalk p.1), ?_⟩⟩
  have h2 : genMap ξ p (↑u⁻¹ : X.presheaf.stalk p.1) * (n : Ω) = 1 := by
    rw [← h1, ← map_mul, Units.inv_mul, map_one]
  exact eq_inv_of_mul_eq_one_left h2

/- English proof (translation)
The claim follows from `not_not.2 (unitAt_natCast ξ p hu n hn)`.
-/
theorem not_inFibre [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ)
    (hu : ∀ n : ℕ, n ≠ 0 → IsUnit ((n : X.presheaf.stalk p.1))) (n : ℕ) (hn : n ≠ 0) : ¬ InFibre ξ n p :=
  not_not.2 (unitAt_natCast ξ p hu n hn)

variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {Li : Type} [AddCommGroup Li] [Module Ω Li]

open LieTangent in

/- English proof (translation)
Take `⟨v, hv⟩` from `(M.mem_lat_iff p e).1 he`. Use `(M.mem_lat_iff p _).2 ⟨v ≫ f, ?_⟩` and prove the remaining obligations. Rewrite `hv`, the goal using `[LieModel.extends_iff]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h` using `hv.1`.

Rewrite `h`, the goal using `[isTanAt_iff]`. Rewrite using `[← Category.assoc, h, one_comp]`. Rewrite using `[hA e, hv.2, Category.assoc]`.
-/
theorem lat_stable (M : LieModel G ξ Li) (p : Cpt ξ) (f : G ⟶ G) [IsMonHom f] (A : Li →ₗ[Ω] Li)
    (hA : M.IsDiffOf f A) (e : Li) (he : e ∈ M.lat p) : A e ∈ M.lat p := by
  obtain ⟨v, hv⟩ := (M.mem_lat_iff p e).1 he
  refine (M.mem_lat_iff p _).2 ⟨v ≫ f, ?_⟩
  rw [LieModel.extends_iff] at hv ⊢
  refine ⟨?_, ?_⟩
  · have h := hv.1
    rw [isTanAt_iff] at h ⊢
    rw [← Category.assoc, h, one_comp]
  · rw [hA e, hv.2, Category.assoc]

end Geo

open HodgeCpt in

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 _ Fl p hu`. Use `haveI : CharZero c.F := charZero_of_injective_algebraMap (algebraMap ℚ c.F).injective`. Use `haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective`. Establish `hVd : ∀ s, 𝔐.V s p = 𝔐.dR s p` using `fun s => Lat.patch_of_not S _ _ fun n hn => not_inFibre 𝔐.ξ p hu n (𝔐.S_prime n hn).ne_zero`. Use `choose U hU b hflag hfr using fun s => Fl.sub s p (Set.mem_univ p)`.

Establish `hF : ∀ s, (𝔐.V s).IsFrameAt (b s) p` using `fun s => hfr s p (Set.mem_univ p) (hU s)`. Establish `hli : ∀ s, LinearIndependent Ω (b s)` using `fun s => (hF s).1`. Establish `hst : ∀ s, 𝔐.M.lat p ⊓ (eigSp 𝔐.ρ (𝔐.emb s)).restrictScalars (regAt 𝔐.ξ p) = Submodule.span (regAt 𝔐.ξ p) (Set.range (b s))` using `fun s => (hVd s).symm.trans (hF s).2`. Establish `hΩ : ∀ s, Submodule.span Ω (Set.range (b s)) = 𝔐.Vgen s`. Introduce `s`.

Take `⟨U', hU', b', hb', hfr'⟩` from `𝔐.vb s p (Set.mem_univ p)`. Establish `h' : 𝔐.V s p = Submodule.span (regAt 𝔐.ξ p) (Set.range b')` using `(hfr' p (Set.mem_univ p) hU').2`. Establish `e1` using `Submodule.span_span_of_tower (regAt 𝔐.ξ p) Ω (Set.range (b s))`. Establish `e2` using `Submodule.span_span_of_tower (regAt 𝔐.ξ p) Ω (Set.range b')`. Rewrite using `[← e1, ← (hF s).2, h', e2]`.

Conclude with `hb'`. Establish `hlab` using `GlobalTheory.CompanionTheory.Ar.LabelCount.labels_injective_card E H l c Ω 𝔐.cst`. Establish `hinj : Function.Injective 𝔐.emb` using `hlab.1`. Establish `hint : DirectSum.IsInternal fun s => eigSp 𝔐.ρ (𝔐.emb s)` using `GlobalTheory.T.eigenspace_decomposition_internal Ω 𝔐.Li E 𝔐.ρ (CMType H ⊕ CMType H) 𝔐.emb hinj hlab.2`. Set `v : ∀ s, Module.Basis (Fin (labelRk D s)) Ω (eigSp 𝔐.ρ (𝔐.emb s))` to `fun s => (Module.Basis.span (hli s)).map (LinearEquiv.ofEq _ _ (hΩ s))`.

Establish `hB : ⇑(hint.collectedBasis v) = fun q : Σ s, Fin (labelRk D s) => b q.1 q.2`. Rewrite using `[hint.collectedBasis_coe]`. Use function extensionality and compare the values at `q`. Simplify using `[v, Module.Basis.span_apply]`. Take `⟨g₀, hg₀⟩` from `GlobalTheory.CompanionTheory.Ar.Flat.KonstReg.exists_const_stalk E H D l Xo c Y S Ω K J y 𝔐 p hu`.

Establish `hcst : ∀ x : c.F, 𝔐.cst x ∈ regAt 𝔐.ξ p` using `fun x => RingHom.mem_range.2 ⟨g₀ x, by rw [← hg₀]; rfl⟩`. Establish `hval : ∀ s a, 𝔐.emb s a ∈ regAt 𝔐.ξ p` using `fun s a => hcst _`. Establish `hinv : ∀ s s' a, 𝔐.emb s a ≠ 𝔐.emb s' a → (𝔐.emb s a - 𝔐.emb s' a)⁻¹ ∈ regAt 𝔐.ξ p`. Introduce `s s' a _`. Establish `: (𝔐.emb s a - 𝔐.emb s' a)⁻¹ = 𝔐.cst (labelEmb c s a - labelEmb c s' a)⁻¹`.

Rewrite using `[map_inv₀, map_sub]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `hcst _`. Establish `hsep : ∀ s s', s ≠ s' → ∃ a, 𝔐.emb s a ≠ 𝔐.emb s' a`.

Introduce `s s' h`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `h (hinj (RingHom.ext hc))`. Establish `hstab : ∀ a, ∀ e ∈ 𝔐.M.lat p, 𝔐.ρ a e ∈ 𝔐.M.lat p` using `fun a e he => haveI := 𝔐.t.act.hom a lat_stable 𝔐.M p (𝔐.t.act.act a) (𝔐.ρ a) (𝔐.act a) e he`.

Use `⟨b, fun s i => hflag s i, ?_, ?_, ?_, ?_, hΩ⟩` and prove the remaining obligations. Introduce `s i e he hl`. Use `mem_span_image_of_mem_flagStep _ (b s) (hli s) i he ?_` and prove the remaining obligations. Rewrite using `[← hst s]`. Use `⟨hl, ?_⟩` and prove the remaining obligations.

Establish `h1 : flagStep Ω (b s) i ≤ Submodule.span Ω (Set.range (b s))` using `Submodule.span_mono (Set.image_subset_range _ _)`. Establish `h2` using `h1 he`. Rewrite `h2` using `[hΩ s]`. Conclude with `h2`. Rewrite using `[← hB]`.

Conclude with `(hint.collectedBasis v).linearIndependent`. Rewrite using `[← hB]`. Conclude with `(hint.collectedBasis v).span_eq`. Conclude with `eq_span_sigma (regAt 𝔐.ξ p) 𝔐.ρ 𝔐.emb (𝔐.M.lat p) hstab hval hinv hsep hint.submodule_iSup_eq_top b hst`.
-/
theorem exists_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] (Fl : 𝔐.Flag) (p : Cpt 𝔐.ξ), (∀ n : ℕ, n ≠ 0 → IsUnit ((n : 𝔐.X.presheaf.stalk p.1))) → ∃ b : ∀ s, Fin (labelRk D s) → 𝔐.Li, (∀ s (i : ℕ), flagStep Ω (b s) i = flagStep Ω (Fl.b s) i) ∧ (∀ s (i : ℕ), ∀ e ∈ flagStep Ω (b s) i, e ∈ 𝔐.M.lat p → e ∈ Submodule.span (regAt 𝔐.ξ p) (b s '' {k | (k : ℕ) < i})) ∧ LinearIndependent Ω (fun q : Σ s, Fin (labelRk D s) => b q.1 q.2) ∧ Submodule.span Ω (Set.range fun q : Σ s, Fin (labelRk D s) => b q.1 q.2) = ⊤ ∧ 𝔐.M.lat p = Submodule.span (regAt 𝔐.ξ p) (Set.range fun q : Σ s, Fin (labelRk D s) => b q.1 q.2) ∧ ∀ s, Submodule.span Ω (Set.range (b s)) = 𝔐.Vgen s := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 _ Fl p hu
  classical
  haveI : CharZero c.F := charZero_of_injective_algebraMap (algebraMap ℚ c.F).injective
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective

  have hVd : ∀ s, 𝔐.V s p = 𝔐.dR s p := fun s =>
    Lat.patch_of_not S _ _ fun n hn => not_inFibre 𝔐.ξ p hu n (𝔐.S_prime n hn).ne_zero
  choose U hU b hflag hfr using fun s => Fl.sub s p (Set.mem_univ p)
  have hF : ∀ s, (𝔐.V s).IsFrameAt (b s) p := fun s => hfr s p (Set.mem_univ p) (hU s)
  have hli : ∀ s, LinearIndependent Ω (b s) := fun s => (hF s).1
  have hst : ∀ s, 𝔐.M.lat p ⊓ (eigSp 𝔐.ρ (𝔐.emb s)).restrictScalars (regAt 𝔐.ξ p) =
      Submodule.span (regAt 𝔐.ξ p) (Set.range (b s)) := fun s => (hVd s).symm.trans (hF s).2

  have hΩ : ∀ s, Submodule.span Ω (Set.range (b s)) = 𝔐.Vgen s := by
    intro s
    obtain ⟨U', hU', b', hb', hfr'⟩ := 𝔐.vb s p (Set.mem_univ p)
    have h' : 𝔐.V s p = Submodule.span (regAt 𝔐.ξ p) (Set.range b') := (hfr' p (Set.mem_univ p) hU').2
    have e1 := Submodule.span_span_of_tower (regAt 𝔐.ξ p) Ω (Set.range (b s))
    have e2 := Submodule.span_span_of_tower (regAt 𝔐.ξ p) Ω (Set.range b')
    rw [← e1, ← (hF s).2, h', e2]
    exact hb'

  have hlab := GlobalTheory.CompanionTheory.Ar.LabelCount.labels_injective_card E H l c Ω 𝔐.cst
  have hinj : Function.Injective 𝔐.emb := hlab.1
  have hint : DirectSum.IsInternal fun s => eigSp 𝔐.ρ (𝔐.emb s) :=
    GlobalTheory.T.eigenspace_decomposition_internal Ω 𝔐.Li E 𝔐.ρ (CMType H ⊕ CMType H) 𝔐.emb hinj hlab.2
  let v : ∀ s, Module.Basis (Fin (labelRk D s)) Ω (eigSp 𝔐.ρ (𝔐.emb s)) := fun s =>
    (Module.Basis.span (hli s)).map (LinearEquiv.ofEq _ _ (hΩ s))
  have hB : ⇑(hint.collectedBasis v) = fun q : Σ s, Fin (labelRk D s) => b q.1 q.2 := by
    rw [hint.collectedBasis_coe]
    funext q
    simp [v, Module.Basis.span_apply]

  obtain ⟨g₀, hg₀⟩ := GlobalTheory.CompanionTheory.Ar.Flat.KonstReg.exists_const_stalk E H D l Xo c Y S Ω K J y 𝔐 p hu
  have hcst : ∀ x : c.F, 𝔐.cst x ∈ regAt 𝔐.ξ p := fun x =>
    RingHom.mem_range.2 ⟨g₀ x, by rw [← hg₀]; rfl⟩
  have hval : ∀ s a, 𝔐.emb s a ∈ regAt 𝔐.ξ p := fun s a => hcst _
  have hinv : ∀ s s' a, 𝔐.emb s a ≠ 𝔐.emb s' a → (𝔐.emb s a - 𝔐.emb s' a)⁻¹ ∈ regAt 𝔐.ξ p := by
    intro s s' a _
    have : (𝔐.emb s a - 𝔐.emb s' a)⁻¹ = 𝔐.cst (labelEmb c s a - labelEmb c s' a)⁻¹ := by
      rw [map_inv₀, map_sub]; rfl
    rw [this]
    exact hcst _
  have hsep : ∀ s s', s ≠ s' → ∃ a, 𝔐.emb s a ≠ 𝔐.emb s' a := by
    intro s s' h
    by_contra hc
    push_neg at hc
    exact h (hinj (RingHom.ext hc))
  have hstab : ∀ a, ∀ e ∈ 𝔐.M.lat p, 𝔐.ρ a e ∈ 𝔐.M.lat p := fun a e he =>
    haveI := 𝔐.t.act.hom a
    lat_stable 𝔐.M p (𝔐.t.act.act a) (𝔐.ρ a) (𝔐.act a) e he
  refine ⟨b, fun s i => hflag s i, ?_, ?_, ?_, ?_, hΩ⟩
  · intro s i e he hl
    refine mem_span_image_of_mem_flagStep _ (b s) (hli s) i he ?_
    rw [← hst s]
    refine ⟨hl, ?_⟩
    have h1 : flagStep Ω (b s) i ≤ Submodule.span Ω (Set.range (b s)) :=
      Submodule.span_mono (Set.image_subset_range _ _)
    have h2 := h1 he
    rw [hΩ s] at h2
    exact h2
  · rw [← hB]
    exact (hint.collectedBasis v).linearIndependent
  · rw [← hB]
    exact (hint.collectedBasis v).span_eq
  · exact eq_span_sigma (regAt 𝔐.ξ p) 𝔐.ρ 𝔐.emb (𝔐.M.lat p) hstab hval hinv hsep
      hint.submodule_iSup_eq_top b hst

end GlobalTheory.CompanionTheory.Ar.FlagFrames
