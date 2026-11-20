import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedIdealFgNeBot
import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.HnStepEqOfNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

namespace GlobalTheory.LieSmooth

/- English proof (translation)
Establish `hx : _root_.IsIntegral ℤ (j (algebraMap (𝓞 K) K a))` using `map_isIntegral_int j a.isIntegral_coe`. Establish `h : _root_.IsIntegral (NormedField.valuation (K` using `C)).integer (j (algebraMap (𝓞 K) K a)) := hx.tower_top`. Establish `h2` using `(Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral h`. Establish `h3 : NormedField.valuation (K` using `C) (j (algebraMap (𝓞 K) K a)) ≤ 1 := h2`. Conclude with `h3` after adjusting the coercions.
-/
theorem grSup_norm_int_le {K : Type} [Field K] {C : Type} [NormedField C] [IsUltrametricDist C] (j : K →+* C)
    (a : 𝓞 K) : ‖j (algebraMap (𝓞 K) K a)‖ ≤ 1 := by
  have hx : _root_.IsIntegral ℤ (j (algebraMap (𝓞 K) K a)) := map_isIntegral_int j a.isIntegral_coe
  have h : _root_.IsIntegral (NormedField.valuation (K := C)).integer (j (algebraMap (𝓞 K) K a)) := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral h
  have h3 : NormedField.valuation (K := C) (j (algebraMap (𝓞 K) K a)) ≤ 1 := h2
  exact_mod_cast h3

/- English proof (translation)
Take `⟨s, rfl⟩` from `hfg`. Establish `hs : s.Nonempty`. Rewrite using `[Finset.nonempty_iff_ne_empty]`. Introduce and unpack `rfl`. Conclude with `hne (by simp)`.

Take `⟨a, ha, hmax⟩` from `s.exists_max_image (fun b => ‖j b‖) hs`. Establish `hle : ∀ b ∈ Submodule.span (𝓞 K) (s : Set K), ‖j b‖ ≤ ‖j a‖`. Introduce `b hb`. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem y hy => exact hmax y hy`.

Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz`. Rewrite using `[map_add]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy hz)`. Consider the case `smul c y _ hy`.

Rewrite using `[Algebra.smul_def, map_mul, norm_mul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) (grSup_norm_int_le j c)).trans hy`. Use `⟨a, Submodule.subset_span ha, ?_, hle⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Apply `hne` to reduce the goal to its premises.

Rewrite using `[eq_bot_iff]`. Introduce `b hb`. Establish `h` using `hle b hb`. Rewrite `h` using `[map_zero, norm_zero, norm_le_zero_iff, map_eq_zero]`. Simplify using `[h]`.
-/
theorem grSup_exists_max {K : Type} [Field K] {C : Type} [NormedField C] [IsUltrametricDist C] (j : K →+* C)
    (I : Submodule (𝓞 K) K) (hfg : I.FG) (hne : I ≠ ⊥) :
    ∃ a ∈ I, a ≠ 0 ∧ ∀ b ∈ I, ‖j b‖ ≤ ‖j a‖ := by
  obtain ⟨s, rfl⟩ := hfg
  have hs : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    exact hne (by simp)
  obtain ⟨a, ha, hmax⟩ := s.exists_max_image (fun b => ‖j b‖) hs
  have hle : ∀ b ∈ Submodule.span (𝓞 K) (s : Set K), ‖j b‖ ≤ ‖j a‖ := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem y hy => exact hmax y hy
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy hz)
    | smul c y _ hy =>
      rw [Algebra.smul_def, map_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (grSup_norm_int_le j c)).trans hy
  refine ⟨a, Submodule.subset_span ha, ?_, hle⟩
  rintro rfl
  apply hne
  rw [eq_bot_iff]
  intro b hb
  have h := hle b hb
  rw [map_zero, norm_zero, norm_le_zero_iff, map_eq_zero] at h
  simp [h]

/- English proof (translation)
Take `⟨g, hg⟩` from `LinearMap.exists_extend ((Module.Basis.span hv).coord i)`. Establish `hgv : ∀ k, g (v k) = if k = i then 1 else 0`. Introduce `k`. Establish `h1 : g (v k) = (Module.Basis.span hv).coord i (Module.Basis.span hv k)`. Rewrite using `[← hg, LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.span_apply]`.

Rewrite using `[h1, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]`. Set `S : Submodule K (Fin r → K)` to `Submodule.pi {k | i < k} (fun _ => ⊥)`. Set `W₀ : Submodule K V` to `S.map (Fintype.linearCombination K v)`. Take `⟨Cm, -, hdec, hCW⟩` from `Formalism.L2.Geo.ExtensionFiltration.ExtInvS7cd.exists_compl_inf L hL W₀`. Establish `hdis : Disjoint (Submodule.span K (Cm : Set V)) W₀` using `Submodule.disjoint_def.2 hCW`.

Take `⟨U, hU, hc⟩` from `hdis.exists_isCompl`. Use `⟨LinearMap.ofIsCompl hc 0 (g.comp W₀.subtype), fun k hk => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hmem : v k ∈ W₀`. Use `⟨Pi.single k 1, fun m hm => ?_, by simp⟩` and prove the remaining obligations. Establish `hm' : i < m` using `hm`.

Establish `: m ≠ k` using `(lt_of_le_of_lt hk hm').ne'`. Simplify using `[this]`. Use `LinearMap.ofIsCompl_apply_right hc (φ := 0) (ψ := g.comp W₀.subtype) ⟨v k, hmem⟩` as an intermediate fact. Conclude with `this.trans (hgv k)`. Take `⟨a, ⟨haL, haW⟩, c, hcC, rfl⟩` from `hdec x hx`.

Establish `h1` using `LinearMap.ofIsCompl_apply_right hc (φ := 0) (ψ := g.comp W₀.subtype) ⟨a, haW⟩`. Establish `h2` using `LinearMap.ofIsCompl_apply_left hc (φ := 0) (ψ := g.comp W₀.subtype) ⟨c, hU (Submodule.subset_span hcC)⟩`. Rewrite using `[map_add]`. Use `erw [h1, h2]`. Take `⟨d, hdS, rfl⟩` from `haW`.

Rewrite `haL` using `[Fintype.linearCombination_apply]`. Use `⟨d, ?_, fun k hk => hdS k hk, haL⟩` and prove the remaining obligations. Simplify using `[Fintype.linearCombination_apply, hgv]`.
-/
theorem grSup_exists_form {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) {r : ℕ} (v : Fin r → V) (i : Fin r)
    (hL : L.FG) (hv : LinearIndependent K v) :
    ∃ f : V →ₗ[K] K, (∀ k, k ≤ i → f (v k) = if k = i then 1 else 0) ∧ ∀ x ∈ L, f x ∈ grIdeal L v i := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span hv).coord i)
  have hgv : ∀ k, g (v k) = if k = i then 1 else 0 := by
    intro k
    have h1 : g (v k) = (Module.Basis.span hv).coord i (Module.Basis.span hv k) := by
      rw [← hg, LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.span_apply]
    rw [h1, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  let S : Submodule K (Fin r → K) := Submodule.pi {k | i < k} (fun _ => ⊥)
  let W₀ : Submodule K V := S.map (Fintype.linearCombination K v)
  obtain ⟨Cm, -, hdec, hCW⟩ := Formalism.L2.Geo.ExtensionFiltration.ExtInvS7cd.exists_compl_inf L hL W₀
  have hdis : Disjoint (Submodule.span K (Cm : Set V)) W₀ :=
    Submodule.disjoint_def.2 hCW
  obtain ⟨U, hU, hc⟩ := hdis.exists_isCompl
  refine ⟨LinearMap.ofIsCompl hc 0 (g.comp W₀.subtype), fun k hk => ?_, fun x hx => ?_⟩
  · have hmem : v k ∈ W₀ := by
      refine ⟨Pi.single k 1, fun m hm => ?_, by simp⟩
      have hm' : i < m := hm
      have : m ≠ k := (lt_of_le_of_lt hk hm').ne'
      simp [this]
    have := LinearMap.ofIsCompl_apply_right hc (φ := 0) (ψ := g.comp W₀.subtype) ⟨v k, hmem⟩
    exact this.trans (hgv k)
  · obtain ⟨a, ⟨haL, haW⟩, c, hcC, rfl⟩ := hdec x hx
    have h1 := LinearMap.ofIsCompl_apply_right hc (φ := 0) (ψ := g.comp W₀.subtype) ⟨a, haW⟩
    have h2 := LinearMap.ofIsCompl_apply_left hc (φ := 0) (ψ := g.comp W₀.subtype)
      ⟨c, hU (Submodule.subset_span hcC)⟩
    rw [map_add]
    erw [h1, h2]
    obtain ⟨d, hdS, rfl⟩ := haW
    rw [Fintype.linearCombination_apply] at haL
    refine ⟨d, ?_, fun k hk => hdS k hk, haL⟩
    simp [Fintype.linearCombination_apply, hgv]

/- English proof (translation)
Introduce `K _ _ C _ _ j n r L v i hL hv`. Take `⟨hfg, hne⟩` from `grIdeal_fg_ne_bot K (Fin n → K) L r v i hL.1 hv (by rw [hL.2]; exact le_top)`. Take `⟨a, haI, ha0, hmax⟩` from `grSup_exists_max j _ hfg hne`. Establish `hja : j a ≠ 0` using `by simpa using ha0`. Establish `hpos : 0 < ‖j a‖` using `norm_pos_iff.2 hja`.

Establish `hsup : (⨆ a : grIdeal L v i, ‖j a‖) = ‖j a‖`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `ciSup_le fun b => hmax b b.2`. Conclude with `le_ciSup (f := fun b : grIdeal L v i => ‖j b‖) ⟨‖j a‖, by rintro _ ⟨b, rfl⟩; exact hmax b b.2⟩ ⟨a, haI⟩`. Rewrite using `[hsup]`.

Use `⟨hpos, IsLeast.csInf_eq ⟨?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨c, rfl, hc0, hcL⟩` from `haI`. Use `⟨fun k => j (c k), hja, fun k hk => by simp [hc0 k hk], Submodule.subset_span ⟨_, hcL, ?_⟩, rfl⟩` and prove the remaining obligations. Use function extensionality and compare the values at `m`. Simplify using `[map_sum]`.

Introduce and unpack `_ ⟨d, hdi, hd0, hdL, rfl⟩`. Take `⟨f, hf1, hf2⟩` from `grSup_exists_form L v i hL.1 hv`. Set `F : (Fin n → C) →ₗ[C] C` to `Fintype.linearCombination C (fun m => j (f (Pi.single m 1)))`. Establish `hF : ∀ x : Fin n → K, F (fun m => j (x m)) = j (f x)`. Introduce `x`.

Use `conv_rhs => rw [pi_eq_sum_univ' x]`. Simplify using `[F, Fintype.linearCombination_apply, map_sum]`. Establish `hb : ∀ y ∈ latC j L, ‖F y‖ ≤ ‖j a‖`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨x, hx, rfl⟩` from `hy`. Rewrite using `[hF]`. Conclude with `hmax _ (hf2 x hx)`. Consider the case `zero => simp`.

Consider the case `add y z _ _ hy hz`. Rewrite using `[map_add]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy hz)`. Consider the case `smul c y _ hy`. Establish `hc : ‖(c : C)‖ ≤ 1` using `c.2`.

Rewrite using `[Subring.smul_def, map_smul, smul_eq_mul, norm_mul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) hc).trans hy`. Establish `hval : F (∑ k, d k • fun m => j (v k m)) = d i`. Rewrite using `[map_sum, Finset.sum_eq_single i]`. Rewrite using `[map_smul, hF, hf1 i le_rfl]`.

Simplify using the standard rewrite rules. Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with h | h` into its components or cases. Rewrite using `[map_smul, hF, hf1 k h.le]`. Simplify using `[hk]`.

Simplify using `[hd0 k h]`. Simplify using the standard rewrite rules. Use `hb _ hdL` as an intermediate fact. Rewrite `this` using `[hval]`. Conclude with `inv_anti₀ (norm_pos_iff.2 hdi) this`.
-/
theorem grNorm_latC_eq_inv_iSup : ∀ {K : Type} [Field K] [NumberField K] {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (j : K →+* C) {n r : ℕ} (L : Submodule (𝓞 K) (Fin n → K)) (v : Fin r → Fin n → K) (i : Fin r), Full L → LinearIndependent K v → 0 < (⨆ a : grIdeal L v i, ‖j a‖) ∧ sInf {ρ : ℝ | ∃ d : Fin r → C, d i ≠ 0 ∧ (∀ k, i < k → d k = 0) ∧ (∑ k, d k • fun m => j (v k m)) ∈ latC j L ∧ ρ = ‖d i‖⁻¹} = (⨆ a : grIdeal L v i, ‖j a‖)⁻¹ := by
  intro K _ _ C _ _ j n r L v i hL hv
  obtain ⟨hfg, hne⟩ := grIdeal_fg_ne_bot K (Fin n → K) L r v i hL.1 hv (by rw [hL.2]; exact le_top)
  obtain ⟨a, haI, ha0, hmax⟩ := grSup_exists_max j _ hfg hne
  have hja : j a ≠ 0 := by simpa using ha0
  have hpos : 0 < ‖j a‖ := norm_pos_iff.2 hja
  have hsup : (⨆ a : grIdeal L v i, ‖j a‖) = ‖j a‖ := by
    apply le_antisymm
    · exact ciSup_le fun b => hmax b b.2
    · exact le_ciSup (f := fun b : grIdeal L v i => ‖j b‖) ⟨‖j a‖, by rintro _ ⟨b, rfl⟩; exact hmax b b.2⟩ ⟨a, haI⟩
  rw [hsup]
  refine ⟨hpos, IsLeast.csInf_eq ⟨?_, ?_⟩⟩
  · obtain ⟨c, rfl, hc0, hcL⟩ := haI
    refine ⟨fun k => j (c k), hja, fun k hk => by simp [hc0 k hk], Submodule.subset_span ⟨_, hcL, ?_⟩, rfl⟩
    funext m
    simp [map_sum]
  · rintro _ ⟨d, hdi, hd0, hdL, rfl⟩
    obtain ⟨f, hf1, hf2⟩ := grSup_exists_form L v i hL.1 hv
    let F : (Fin n → C) →ₗ[C] C := Fintype.linearCombination C (fun m => j (f (Pi.single m 1)))
    have hF : ∀ x : Fin n → K, F (fun m => j (x m)) = j (f x) := by
      intro x
      conv_rhs => rw [pi_eq_sum_univ' x]
      simp [F, Fintype.linearCombination_apply, map_sum]
    have hb : ∀ y ∈ latC j L, ‖F y‖ ≤ ‖j a‖ := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        rw [hF]
        exact hmax _ (hf2 x hx)
      | zero => simp
      | add y z _ _ hy hz =>
        rw [map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy hz)
      | smul c y _ hy =>
        have hc : ‖(c : C)‖ ≤ 1 := c.2
        rw [Subring.smul_def, map_smul, smul_eq_mul, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans hy
    have hval : F (∑ k, d k • fun m => j (v k m)) = d i := by
      rw [map_sum, Finset.sum_eq_single i]
      · rw [map_smul, hF, hf1 i le_rfl]
        simp
      · intro k _ hk
        rcases lt_or_gt_of_ne hk with h | h
        · rw [map_smul, hF, hf1 k h.le]
          simp [hk]
        · simp [hd0 k h]
      · simp
    have := hb _ hdL
    rw [hval] at this
    exact inv_anti₀ (norm_pos_iff.2 hdi) this

end GlobalTheory.LieSmooth
