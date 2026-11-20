import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

noncomputable section

open GlobalTheory.PRep

namespace PositivityTheory.RgUd.Form.U.Asm

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(∀ h : K, ρ (h : G) v = ((1 : K →* ℂˣ) h : ℂ) • v) ↔ _`. Simplify using the standard rewrite rules.
-/
theorem mem_fixed_iff_irr {G D : Type} [Group G] [AddCommGroup D] [Module ℂ D] (ρ : Representation ℂ G D)
    (K : Subgroup G) (v : D) : v ∈ fixed ρ K ↔ ∀ h : K, ρ (h : G) v = v := by
  change (∀ h : K, ρ (h : G) v = ((1 : K →* ℂˣ) h : ℂ) • v) ↔ _
  simp

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `u`. Use `⟨0, Submodule.zero_mem _, ?_⟩` and prove the remaining obligations. Introduce `m hm`.

Simplify using `only [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hm`. Simplify using `[hm]`. Consider the case `insert a s ha ih`. Introduce `u`. Take `⟨wa, hwa, hwa'⟩` from `ih a`.

Take `⟨wu, hwu, hwu'⟩` from `ih u`. Take `⟨a', ha'⟩ : ∃ a' : D, a' = a - wa` from `⟨_, rfl⟩`. Take `⟨c, hc⟩ : ∃ c : ℂ, c = B (u - wu) a' / B a' a'` from `⟨_, rfl⟩`. Establish `hsub : Submodule.span ℂ (s : Set D) ≤ Submodule.span ℂ ((insert a s : Finset D) : Set D)` using `Submodule.span_mono (by rw [Finset.coe_insert]; exact Set.subset_insert _ _)`. Establish `hamem : a ∈ Submodule.span ℂ ((insert a s : Finset D) : Set D)` using `Submodule.subset_span (by simp)`.

Use `⟨wu + c • a', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ha']`. Conclude with `Submodule.add_mem _ (hsub hwu) (Submodule.smul_mem _ _ (Submodule.sub_mem _ hamem (hsub hwa)))`. Establish `hexp : ∀ m, B (u - (wu + c • a')) m = B (u - wu) m - c * B a' m`. Introduce `m`.

Rewrite using `[show u - (wu + c • a') = (u - wu) - c • a' by abel, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]`. Establish `hs : ∀ m ∈ Submodule.span ℂ (s : Set D), B (u - (wu + c • a')) m = 0`. Introduce `m hm`. Rewrite using `[hexp, hwu' m hm, ha', hwa' m hm, mul_zero, sub_zero]`. Establish `key : ∀ m ∈ ((insert a s : Finset D) : Set D), B (u - (wu + c • a')) m = 0`.

Introduce `m hm`. Rewrite `hm` using `[Finset.coe_insert, Set.mem_insert_iff]`. Break down `hm with hm | hm` into its components or cases. Establish `hsplit : m = a' + wa` using `by rw [hm, ha']; abel`. Rewrite using `[hsplit, map_add, hs wa hwa, add_zero, hexp]`.

Distinguish the cases in `h0 : B a' a' = 0`. Establish `h0' : a' = 0`. Assume the negation of the conclusion as `hne`. Use `hBp a' hne` as an intermediate fact. Rewrite `this` using `[h0]`.

Simplify using `at this`. Simplify using `[h0']`. Rewrite using `[hc, div_mul_cancel₀ _ h0, sub_self]`. Conclude with `hs m (Submodule.subset_span hm)`. Introduce `m hm`.

Establish `hle : Submodule.span ℂ ((insert a s : Finset D) : Set D) ≤ LinearMap.ker (B (u - (wu + c • a')))` using `Submodule.span_le.2 (fun m hm => LinearMap.mem_ker.2 (key m hm))`. Conclude with `LinearMap.mem_ker.1 (hle hm)`.
-/
theorem exists_orth_of_finset {D : Type} [AddCommGroup D] [Module ℂ D] (B : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ)
    (hBp : ∀ x, x ≠ 0 → 0 < (B x x).re) (s : Finset D) :
    ∀ u : D, ∃ w ∈ Submodule.span ℂ (s : Set D), ∀ m ∈ Submodule.span ℂ (s : Set D), B (u - w) m = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro u
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    intro m hm
    simp only [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hm
    simp [hm]
  | insert a s ha ih =>
    intro u
    obtain ⟨wa, hwa, hwa'⟩ := ih a
    obtain ⟨wu, hwu, hwu'⟩ := ih u
    obtain ⟨a', ha'⟩ : ∃ a' : D, a' = a - wa := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : ℂ, c = B (u - wu) a' / B a' a' := ⟨_, rfl⟩
    have hsub : Submodule.span ℂ (s : Set D) ≤ Submodule.span ℂ ((insert a s : Finset D) : Set D) :=
      Submodule.span_mono (by rw [Finset.coe_insert]; exact Set.subset_insert _ _)
    have hamem : a ∈ Submodule.span ℂ ((insert a s : Finset D) : Set D) :=
      Submodule.subset_span (by simp)
    refine ⟨wu + c • a', ?_, ?_⟩
    · rw [ha']
      exact Submodule.add_mem _ (hsub hwu) (Submodule.smul_mem _ _ (Submodule.sub_mem _ hamem (hsub hwa)))
    · have hexp : ∀ m, B (u - (wu + c • a')) m = B (u - wu) m - c * B a' m := by
        intro m
        rw [show u - (wu + c • a') = (u - wu) - c • a' by abel, map_sub, map_smul,
          LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      have hs : ∀ m ∈ Submodule.span ℂ (s : Set D), B (u - (wu + c • a')) m = 0 := by
        intro m hm
        rw [hexp, hwu' m hm, ha', hwa' m hm, mul_zero, sub_zero]
      have key : ∀ m ∈ ((insert a s : Finset D) : Set D), B (u - (wu + c • a')) m = 0 := by
        intro m hm
        rw [Finset.coe_insert, Set.mem_insert_iff] at hm
        rcases hm with hm | hm
        · have hsplit : m = a' + wa := by rw [hm, ha']; abel
          rw [hsplit, map_add, hs wa hwa, add_zero, hexp]
          by_cases h0 : B a' a' = 0
          · have h0' : a' = 0 := by
              by_contra hne
              have := hBp a' hne
              rw [h0] at this
              simp at this
            simp [h0']
          · rw [hc, div_mul_cancel₀ _ h0, sub_self]
        · exact hs m (Submodule.subset_span hm)
      intro m hm
      have hle : Submodule.span ℂ ((insert a s : Finset D) : Set D) ≤ LinearMap.ker (B (u - (wu + c • a'))) :=
        Submodule.span_le.2 (fun m hm => LinearMap.mem_ker.2 (key m hm))
      exact LinearMap.mem_ker.1 (hle hm)

/- English proof (translation)
Distinguish the cases in `hu : u = 0`. Conclude with `⟨0, W.zero_mem, fun w' _ => by simp [hu]⟩`. Set `S : Subgroup G` to `{ carrier := {g | ρ g u = u} mul_mem' := by`. Introduce `a b (ha : ρ a u = u) (hb : ρ b u = u)`. Use `show ρ (a * b) u = u`.

Rewrite using `[map_mul, Module.End.mul_apply, hb, ha]`. Use the proof step `one_mem' := by show ρ 1 u = u`. Simplify using the standard rewrite rules. Use the proof step `inv_mem' := by`. Introduce `a (ha : ρ a u = u)`.

Use `show ρ a⁻¹ u = u`. Use `conv_lhs => rw [← ha]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }`. Establish `hSo : IsOpen (S : Set G)` using `hA.1 u`. Set `K : Subgroup G` to `K₁ ⊓ S`.

Establish `hKo : IsOpen (K : Set G)`. Rewrite using `[Subgroup.coe_inf]`. Conclude with `hK₁o.inter hSo`. Establish `hKc : IsCompact (K : Set G)`. Rewrite using `[Subgroup.coe_inf]`.

Conclude with `hK₁c.inter_right (Subgroup.isClosed_of_isOpen S hSo)`. Establish `hKS : ∀ k : K, ρ (k : G) u = u` using `fun k => (Subgroup.mem_inf.1 k.2).2`. Establish `hBu : B u u ≠ 0`. Introduce `h`. Use `hBp u hu` as an intermediate fact.

Rewrite `this` using `[h]`. Simplify using `at this`. Establish `hχ : ∀ k : K, (χ k : ℂ) = 1`. Introduce `k`. Establish `h` using `hBe k u u`.

Rewrite `h` using `[hKS k]`. Establish `h2 : ((χ k : ℂ) - 1) * B u u = 0` using `by rw [sub_mul, ← h]; ring`. Break down `mul_eq_zero.1 h2 with h1 | h1` into its components or cases. Conclude with `sub_eq_zero.1 h1`. Conclude with `absurd h1 hBu`.

Establish `hBK : ∀ (k : K) x y, B (ρ (k : G) x) (ρ (k : G) y) = B x y`. Introduce `k x y`. Rewrite using `[hBe, hχ, one_mul]`. Establish `: FiniteDimensional ℂ (fixed ρ K)` using `hA.2 K hKo hKc`. Set `M : Submodule ℂ D` to `W ⊓ fixed ρ K`.

Establish `: FiniteDimensional ℂ M` using `Submodule.finiteDimensional_of_le inf_le_right`. Take `⟨s, hs⟩ : M.FG` from `Module.Finite.iff_fg.1 inferInstance`. Take `⟨w, hwM, hw⟩` from `exists_orth_of_finset B hBp s u`. Rewrite `hwM`, `hw` using `[hs]`. Use `⟨w, (Submodule.mem_inf.1 hwM).1, ?_⟩` and prove the remaining obligations.

Establish `huF : u - w ∈ fixed ρ K` using `Submodule.sub_mem _ ((mem_fixed_iff_irr ρ K u).2 hKS) (Submodule.mem_inf.1 hwM).2`. Establish `hfix` using `(mem_fixed_iff_irr ρ K _).1 huF`. Introduce `w' hw'`. Establish `: CompactSpace K` using `isCompact_iff_compactSpace.mp hKc`. Set `f : K → D` to `fun k => ρ (k : G) w'`.

Establish `hf : IsLocallyConstant f`. Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `k0`. Use `⟨(fun k : K => (k0 : G)⁻¹ * (k : G)) ⁻¹' {g | ρ g w' = w'}, (hA.1 w').preimage (continuous_const.mul continuous_subtype_val), ?_, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.

Introduce `k hk`. Simplify using `only [Set.mem_preimage, Set.mem_ofPred_eq] at hk`. Simplify using `only [f]`. Use `conv_lhs => rw [show (k : G) = (k0 : G) * ((k0 : G)⁻¹ * (k : G)) by group]`. Rewrite using `[map_mul, Module.End.mul_apply, hk]`.

Take `⟨T, hTmem⟩ : ∃ T : Finset D, ∀ v, v ∈ T ↔ ∃ k : K, ρ (k : G) w' = v` from `⟨hf.range_finite.toFinset, fun v => by simp only [Set.Finite.mem_toFinset, Set.mem_range, f]⟩`. Establish `hTst : ∀ h : K, ∀ v ∈ T, ρ (h : G) v ∈ T`. Introduce `h v hv`. Take `⟨k, rfl⟩` from `(hTmem v).1 hv`. Conclude with `(hTmem _).2 ⟨h * k, by rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]⟩`.

Establish `hinv : ∀ h : K, ∀ v, ρ ((h⁻¹ : K) : G) (ρ (h : G) v) = v`. Introduce `h v`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Simplify using the standard rewrite rules. Establish `hinv' : ∀ h : K, ∀ v, ρ (h : G) (ρ ((h⁻¹ : K) : G) v) = v`.

Introduce `h v`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Simplify using the standard rewrite rules. Establish `hsumF : ∑ v ∈ T, v ∈ M`. Use `Submodule.mem_inf.2 ⟨Submodule.sum_mem _ (fun v hv => ?_), ?_⟩` and prove the remaining obligations.

Take `⟨k, rfl⟩` from `(hTmem v).1 hv`. Conclude with `hW _ _ hw'`. Rewrite using `[mem_fixed_iff_irr]`. Introduce `h`. Rewrite using `[map_sum]`.

Conclude with `Finset.sum_nbij' (fun v => ρ (h : G) v) (fun v => ρ ((h⁻¹ : K) : G) v) (hTst h) (hTst h⁻¹) (fun v _ => hinv h v) (fun v _ => hinv' h v) (fun v _ => rfl)`. Establish `h0` using `hw _ hsumF`. Rewrite `h0` using `[map_sum]`. Establish `hterm : ∀ v ∈ T, B (u - w) v = B (u - w) w'`. Introduce `v hv`.

Take `⟨k, rfl⟩` from `(hTmem v).1 hv`. Use `conv_lhs => rw [← hfix k]`. Conclude with `hBK k _ _`. Rewrite `h0` using `[Finset.sum_congr rfl hterm, Finset.sum_const]`. Establish `hcard : T.card ≠ 0` using `Finset.card_ne_zero_of_mem ((hTmem w').2 ⟨1, by simp⟩)`.

Break down `smul_eq_zero.1 h0 with h1 | h1` into its components or cases. Conclude with `absurd h1 hcard`. Conclude with `h1`.
-/
theorem exists_orth_decomp {G D : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup D]
    [Module ℂ D] (ρ : Representation ℂ G D) (hA : IsAdmissible ρ) (K₁ : Subgroup G) (hK₁o : IsOpen (K₁ : Set G))
    (hK₁c : IsCompact (K₁ : Set G)) (χ : G → ℝ) (B : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ)
    (hBp : ∀ x, x ≠ 0 → 0 < (B x x).re)
    (hBe : ∀ g x y, B (ρ g x) (ρ g y) = (χ g : ℂ) * B x y) (W : Submodule ℂ D)
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) (u : D) :
    ∃ w ∈ W, ∀ w' ∈ W, B (u - w) w' = 0 := by
  classical
  by_cases hu : u = 0
  · exact ⟨0, W.zero_mem, fun w' _ => by simp [hu]⟩
  let S : Subgroup G :=
    { carrier := {g | ρ g u = u}
      mul_mem' := by
        intro a b (ha : ρ a u = u) (hb : ρ b u = u)
        show ρ (a * b) u = u
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by
        show ρ 1 u = u
        simp
      inv_mem' := by
        intro a (ha : ρ a u = u)
        show ρ a⁻¹ u = u
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hSo : IsOpen (S : Set G) := hA.1 u
  let K : Subgroup G := K₁ ⊓ S
  have hKo : IsOpen (K : Set G) := by
    rw [Subgroup.coe_inf]; exact hK₁o.inter hSo
  have hKc : IsCompact (K : Set G) := by
    rw [Subgroup.coe_inf]; exact hK₁c.inter_right (Subgroup.isClosed_of_isOpen S hSo)
  have hKS : ∀ k : K, ρ (k : G) u = u := fun k => (Subgroup.mem_inf.1 k.2).2
  have hBu : B u u ≠ 0 := by
    intro h; have := hBp u hu; rw [h] at this; simp at this
  have hχ : ∀ k : K, (χ k : ℂ) = 1 := by
    intro k
    have h := hBe k u u
    rw [hKS k] at h
    have h2 : ((χ k : ℂ) - 1) * B u u = 0 := by rw [sub_mul, ← h]; ring
    rcases mul_eq_zero.1 h2 with h1 | h1
    · exact sub_eq_zero.1 h1
    · exact absurd h1 hBu
  have hBK : ∀ (k : K) x y, B (ρ (k : G) x) (ρ (k : G) y) = B x y := by
    intro k x y; rw [hBe, hχ, one_mul]
  have : FiniteDimensional ℂ (fixed ρ K) := hA.2 K hKo hKc
  let M : Submodule ℂ D := W ⊓ fixed ρ K
  have : FiniteDimensional ℂ M := Submodule.finiteDimensional_of_le inf_le_right
  obtain ⟨s, hs⟩ : M.FG := Module.Finite.iff_fg.1 inferInstance
  obtain ⟨w, hwM, hw⟩ := exists_orth_of_finset B hBp s u
  rw [hs] at hwM hw
  refine ⟨w, (Submodule.mem_inf.1 hwM).1, ?_⟩
  have huF : u - w ∈ fixed ρ K :=
    Submodule.sub_mem _ ((mem_fixed_iff_irr ρ K u).2 hKS) (Submodule.mem_inf.1 hwM).2
  have hfix := (mem_fixed_iff_irr ρ K _).1 huF
  intro w' hw'
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  let f : K → D := fun k => ρ (k : G) w'
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_exists_open]
    intro k0
    refine ⟨(fun k : K => (k0 : G)⁻¹ * (k : G)) ⁻¹' {g | ρ g w' = w'},
      (hA.1 w').preimage (continuous_const.mul continuous_subtype_val), ?_, ?_⟩
    · simp
    · intro k hk
      simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hk
      simp only [f]
      conv_lhs => rw [show (k : G) = (k0 : G) * ((k0 : G)⁻¹ * (k : G)) by group]
      rw [map_mul, Module.End.mul_apply, hk]
  obtain ⟨T, hTmem⟩ : ∃ T : Finset D, ∀ v, v ∈ T ↔ ∃ k : K, ρ (k : G) w' = v :=
    ⟨hf.range_finite.toFinset, fun v => by simp only [Set.Finite.mem_toFinset, Set.mem_range, f]⟩
  have hTst : ∀ h : K, ∀ v ∈ T, ρ (h : G) v ∈ T := by
    intro h v hv
    obtain ⟨k, rfl⟩ := (hTmem v).1 hv
    exact (hTmem _).2 ⟨h * k, by rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]⟩
  have hinv : ∀ h : K, ∀ v, ρ ((h⁻¹ : K) : G) (ρ (h : G) v) = v := by
    intro h v
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  have hinv' : ∀ h : K, ∀ v, ρ (h : G) (ρ ((h⁻¹ : K) : G) v) = v := by
    intro h v
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  have hsumF : ∑ v ∈ T, v ∈ M := by
    refine Submodule.mem_inf.2 ⟨Submodule.sum_mem _ (fun v hv => ?_), ?_⟩
    · obtain ⟨k, rfl⟩ := (hTmem v).1 hv; exact hW _ _ hw'
    · rw [mem_fixed_iff_irr]
      intro h
      rw [map_sum]
      exact Finset.sum_nbij' (fun v => ρ (h : G) v) (fun v => ρ ((h⁻¹ : K) : G) v) (hTst h) (hTst h⁻¹)
        (fun v _ => hinv h v) (fun v _ => hinv' h v) (fun v _ => rfl)
  have h0 := hw _ hsumF
  rw [map_sum] at h0
  have hterm : ∀ v ∈ T, B (u - w) v = B (u - w) w' := by
    intro v hv
    obtain ⟨k, rfl⟩ := (hTmem v).1 hv
    conv_lhs => rw [← hfix k]
    exact hBK k _ _
  rw [Finset.sum_congr rfl hterm, Finset.sum_const] at h0
  have hcard : T.card ≠ 0 := Finset.card_ne_zero_of_mem ((hTmem w').2 ⟨1, by simp⟩)
  rcases smul_eq_zero.1 h0 with h1 | h1
  · exact absurd h1 hcard
  · exact h1

/- English proof (translation)
Establish `key : ∀ W : Subrepresentation ρ, W ≠ ⊥ → W = ⊤`. Introduce `W hWb`. Set `Wm : Submodule ℂ D` to `W.toSubmodule`. Establish `hWs : ∀ g, ∀ w ∈ Wm, ρ g w ∈ Wm` using `fun g w hw => W.apply_mem_toSubmodule g hw`. Set `Wp : Submodule ℂ D` to `{ carrier := {x | ∀ w ∈ Wm, B x w = 0} add_mem' := by`.

Introduce `a b ha hb w hw`. Rewrite using `[map_add, LinearMap.add_apply, ha w hw, hb w hw, add_zero]`. Use the proof step `zero_mem' := by intro w _; simp`. Use the proof step `smul_mem' := by`. Introduce `c x hx w hw`.

Rewrite using `[map_smul, LinearMap.smul_apply, hx w hw, smul_zero] }`. Establish `hWp : ∀ x, x ∈ Wp ↔ ∀ w ∈ Wm, B x w = 0` using `fun x => Iff.rfl`. Establish `hWps : ∀ g, ∀ x ∈ Wp, ρ g x ∈ Wp`. Introduce `g x hx`. Rewrite using `[hWp]`.

Introduce `w hw`. Establish `h1 : ρ g (ρ g⁻¹ w) = w`. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Rewrite using `[← h1, hBe, (hWp x).1 hx _ (hWs _ _ hw), mul_zero]`. Establish `hdec` using `fun u => exists_orth_decomp ρ hA K₁ hK₁o hK₁c χ B hBp hBe Wm hWs u`.

Establish `hcompl : IsCompl Wm Wp`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Submodule.disjoint_def]`. Introduce `x hx hxp`. Assume the negation of the conclusion as `hne`.

Use `hBp x hne` as an intermediate fact. Rewrite `this` using `[(hWp x).1 hxp x hx]`. Simplify using `at this`. Rewrite using `[codisjoint_iff, eq_top_iff]`. Introduce `u _`.

Take `⟨w, hw, hw'⟩` from `hdec u`. Rewrite using `[show u = w + (u - w) by abel]`. Conclude with `Submodule.add_mem_sup hw ((hWp _).2 hw')`. Set `P : D →ₗ[ℂ] D` to `Wm.projection Wp hcompl`. Establish `hPW : ∀ x, P x ∈ Wm` using `fun x => Submodule.projection_apply_mem hcompl x`.

Establish `hPw : ∀ w ∈ Wm, P w = w` using `fun w hw => Submodule.projection_apply_of_mem_left hcompl hw`. Establish `hPq : ∀ x, x - P x ∈ Wp` using `fun x => Submodule.sub_projection_mem hcompl x`. Establish `hP0 : ∀ q ∈ Wp, P q = 0` using `fun q hq => Submodule.projection_apply_of_mem_right hcompl hq`. Establish `hPρ : ∀ g x, P (ρ g x) = ρ g (P x)`. Introduce `g x`.

Establish `hx : ρ g x = ρ g (P x) + ρ g (x - P x)`. Rewrite using `[← map_add]`. Use `congr 1`. Normalize the expressions using the abelian group laws. Rewrite using `[hx, map_add, hPw _ (hWs g _ (hPW x)), hP0 _ (hWps g _ (hPq x)), add_zero]`.

Set `C : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ` to `(B ∘ₗ P).compl₂ P`. Establish `hCapp : ∀ x y, C x y = B (P x) (P y)` using `fun x y => rfl`. Establish `hBsplit : ∀ x, B x x = B (P x) (P x) + B (x - P x) (x - P x)`. Introduce `x`. Establish `h1 : B (x - P x) (P x) = 0` using `(hWp _).1 (hPq x) _ (hPW x)`.

Establish `h2 : B (P x) (x - P x) = 0` using `by rw [hBh (x - P x) (P x), h1, map_zero]`. Use `conv_lhs => rw [show x = P x + (x - P x) by abel]`. Simplify using `only [map_add, LinearMap.add_apply, h1, h2, add_zero, zero_add]`. Establish `hnn : ∀ x, 0 ≤ (B x x).re`. Introduce `x`.

Distinguish the cases in `h : x = 0`. Rewrite using `[h]`. Simplify using the standard rewrite rules. Conclude with `(hBp _ h).le`. Take `⟨c, hc⟩` from `hC C (fun x y => by rw [hCapp, hCapp, hBh]) (fun x => by rw [hCapp]; exact hnn _) (fun x => by`.

Rewrite using `[hCapp, hBsplit x, Complex.add_re]`. Use `hnn (x - P x)` as an intermediate fact. Use the proof step `linarith)`. Use the proof step `(fun g x y => by rw [hCapp, hCapp, hPρ, hPρ, hBe])`. Choose the witnesses or unpack the hypotheses as in `⟨w0, hw0, hw0ne⟩ : ∃ w ∈ Wm, w ≠ 0 := by`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `hWb` to reduce the goal to its premises. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Use `show Wm = ⊥`.

Conclude with `(Submodule.eq_bot_iff _).2 hcon`. Establish `hc1 : c = 1`. Establish `h` using `hc w0 w0`. Rewrite `h` using `[hCapp, hPw w0 hw0]`. Establish `hB0 : B w0 w0 ≠ 0`.

Introduce `h0`. Use `hBp w0 hw0ne` as an intermediate fact. Rewrite `this` using `[h0]`. Simplify using `at this`. Establish `h2 : (c - 1) * B w0 w0 = 0` using `by rw [sub_mul, ← h]; ring`.

Break down `mul_eq_zero.1 h2 with h1 | h1` into its components or cases. Conclude with `sub_eq_zero.1 h1`. Conclude with `absurd h1 hB0`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Use `show Wm = ⊤`.

Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `hq : x - P x = 0`. Assume the negation of the conclusion as `hne`. Establish `h` using `hc (x - P x) (x - P x)`.

Rewrite `h` using `[hCapp, hc1, one_mul, hP0 _ (hPq x), map_zero]`. Use `hBp _ hne` as an intermediate fact. Rewrite `this` using `[← h]`. Simplify using `at this`. Establish `hx : x = P x` using `sub_eq_zero.1 hq`.

Rewrite using `[hx]`. Conclude with `hPW x`. Establish `hne : (⊥ : Subrepresentation ρ) ≠ ⊤`. Introduce `h`. Take `⟨x, hx⟩` from `exists_ne (0 : D)`.

Establish `h1 : x ∈ (⊤ : Subrepresentation ρ).toSubmodule` using `(Submodule.mem_top : x ∈ (⊤ : Submodule ℂ D))`. Rewrite `h1` using `[← h]`. Conclude with `hx ((Submodule.mem_bot ℂ).1 (h1 : x ∈ (⊥ : Submodule ℂ D)))`. Conclude with `{ exists_pair_ne := ⟨⊥, ⊤, hne⟩ eq_bot_or_eq_top := fun W => by`. Distinguish the cases in `h : W = ⊥`.

Conclude with `Or.inl h`. Conclude with `Or.inr (key W h) }`.
-/
theorem irr_of_forms {G D : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup D] [Module ℂ D]
    [Nontrivial D] (ρ : Representation ℂ G D) (hA : IsAdmissible ρ) (K₁ : Subgroup G) (hK₁o : IsOpen (K₁ : Set G))
    (hK₁c : IsCompact (K₁ : Set G)) (χ : G → ℝ) (B : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ)
    (hBh : ∀ x y, B y x = starRingEnd ℂ (B x y)) (hBp : ∀ x, x ≠ 0 → 0 < (B x x).re)
    (hBe : ∀ g x y, B (ρ g x) (ρ g y) = (χ g : ℂ) * B x y)
    (hC : ∀ C : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ, (∀ x y, C y x = starRingEnd ℂ (C x y)) → (∀ x, 0 ≤ (C x x).re) →
      (∀ x, (C x x).re ≤ (B x x).re) → (∀ g x y, C (ρ g x) (ρ g y) = (χ g : ℂ) * C x y) →
      ∃ c : ℂ, ∀ x y, C x y = c * B x y) :
    ρ.IsIrreducible := by
  classical
  have key : ∀ W : Subrepresentation ρ, W ≠ ⊥ → W = ⊤ := by
    intro W hWb
    let Wm : Submodule ℂ D := W.toSubmodule
    have hWs : ∀ g, ∀ w ∈ Wm, ρ g w ∈ Wm := fun g w hw => W.apply_mem_toSubmodule g hw
    let Wp : Submodule ℂ D :=
      { carrier := {x | ∀ w ∈ Wm, B x w = 0}
        add_mem' := by
          intro a b ha hb w hw
          rw [map_add, LinearMap.add_apply, ha w hw, hb w hw, add_zero]
        zero_mem' := by intro w _; simp
        smul_mem' := by
          intro c x hx w hw
          rw [map_smul, LinearMap.smul_apply, hx w hw, smul_zero] }
    have hWp : ∀ x, x ∈ Wp ↔ ∀ w ∈ Wm, B x w = 0 := fun x => Iff.rfl
    have hWps : ∀ g, ∀ x ∈ Wp, ρ g x ∈ Wp := by
      intro g x hx
      rw [hWp]
      intro w hw
      have h1 : ρ g (ρ g⁻¹ w) = w := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      rw [← h1, hBe, (hWp x).1 hx _ (hWs _ _ hw), mul_zero]
    have hdec := fun u => exists_orth_decomp ρ hA K₁ hK₁o hK₁c χ B hBp hBe Wm hWs u
    have hcompl : IsCompl Wm Wp := by
      constructor
      · rw [Submodule.disjoint_def]
        intro x hx hxp
        by_contra hne
        have := hBp x hne
        rw [(hWp x).1 hxp x hx] at this
        simp at this
      · rw [codisjoint_iff, eq_top_iff]
        intro u _
        obtain ⟨w, hw, hw'⟩ := hdec u
        rw [show u = w + (u - w) by abel]
        exact Submodule.add_mem_sup hw ((hWp _).2 hw')
    let P : D →ₗ[ℂ] D := Wm.projection Wp hcompl
    have hPW : ∀ x, P x ∈ Wm := fun x => Submodule.projection_apply_mem hcompl x
    have hPw : ∀ w ∈ Wm, P w = w := fun w hw => Submodule.projection_apply_of_mem_left hcompl hw
    have hPq : ∀ x, x - P x ∈ Wp := fun x => Submodule.sub_projection_mem hcompl x
    have hP0 : ∀ q ∈ Wp, P q = 0 := fun q hq => Submodule.projection_apply_of_mem_right hcompl hq
    have hPρ : ∀ g x, P (ρ g x) = ρ g (P x) := by
      intro g x
      have hx : ρ g x = ρ g (P x) + ρ g (x - P x) := by
        rw [← map_add]; congr 1; abel
      rw [hx, map_add, hPw _ (hWs g _ (hPW x)), hP0 _ (hWps g _ (hPq x)), add_zero]
    let C : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ := (B ∘ₗ P).compl₂ P
    have hCapp : ∀ x y, C x y = B (P x) (P y) := fun x y => rfl
    have hBsplit : ∀ x, B x x = B (P x) (P x) + B (x - P x) (x - P x) := by
      intro x
      have h1 : B (x - P x) (P x) = 0 := (hWp _).1 (hPq x) _ (hPW x)
      have h2 : B (P x) (x - P x) = 0 := by rw [hBh (x - P x) (P x), h1, map_zero]
      conv_lhs => rw [show x = P x + (x - P x) by abel]
      simp only [map_add, LinearMap.add_apply, h1, h2, add_zero, zero_add]
    have hnn : ∀ x, 0 ≤ (B x x).re := by
      intro x
      by_cases h : x = 0
      · rw [h]; simp
      · exact (hBp _ h).le
    obtain ⟨c, hc⟩ := hC C (fun x y => by rw [hCapp, hCapp, hBh]) (fun x => by rw [hCapp]; exact hnn _)
      (fun x => by
        rw [hCapp, hBsplit x, Complex.add_re]
        have := hnn (x - P x)
        linarith)
      (fun g x y => by rw [hCapp, hCapp, hPρ, hPρ, hBe])
    obtain ⟨w0, hw0, hw0ne⟩ : ∃ w ∈ Wm, w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hWb
      apply Subrepresentation.toSubmodule_injective
      show Wm = ⊥
      exact (Submodule.eq_bot_iff _).2 hcon
    have hc1 : c = 1 := by
      have h := hc w0 w0
      rw [hCapp, hPw w0 hw0] at h
      have hB0 : B w0 w0 ≠ 0 := by
        intro h0; have := hBp w0 hw0ne; rw [h0] at this; simp at this
      have h2 : (c - 1) * B w0 w0 = 0 := by rw [sub_mul, ← h]; ring
      rcases mul_eq_zero.1 h2 with h1 | h1
      · exact sub_eq_zero.1 h1
      · exact absurd h1 hB0
    apply Subrepresentation.toSubmodule_injective
    show Wm = ⊤
    rw [eq_top_iff]
    intro x _
    have hq : x - P x = 0 := by
      by_contra hne
      have h := hc (x - P x) (x - P x)
      rw [hCapp, hc1, one_mul, hP0 _ (hPq x), map_zero] at h
      have := hBp _ hne
      rw [← h] at this
      simp at this
    have hx : x = P x := sub_eq_zero.1 hq
    rw [hx]
    exact hPW x
  have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : D)
    have h1 : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ D))
    rw [← h] at h1
    exact hx ((Submodule.mem_bot ℂ).1 (h1 : x ∈ (⊥ : Submodule ℂ D)))
  exact { exists_pair_ne := ⟨⊥, ⊤, hne⟩
          eq_bot_or_eq_top := fun W => by
            by_cases h : W = ⊥
            · exact Or.inl h
            · exact Or.inr (key W h) }

end PositivityTheory.RgUd.Form.U.Asm
