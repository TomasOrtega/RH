import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
open scoped Topology

namespace GlobalTheory

/- English proof (translation)
Establish `hadd2 : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, B x (y + z) = B x y + B x z`. Introduce `x hx y hy z hz`. Rewrite using `[hherm (y + z) (D.add_mem hy hz) x hx, hadd y hy z hz x hx, map_add, ← hherm y hy x hx, ← hherm z hz x hx]`. Establish `hsmul2 : ∀ c : ℂ, ∀ x ∈ D, ∀ y ∈ D, B x (c • y) = starRingEnd ℂ c * B x y`. Introduce `c x hx y hy`.

Rewrite using `[hherm (c • y) (D.smul_mem c hy) x hx, hsmul c y hy x hx, map_mul, ← hherm y hy x hx]`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`. Introduce `u hu`. Use `⟨0, Submodule.zero_mem _, ?_⟩` and prove the remaining obligations.

Introduce `w hw`. Establish `hw0 : w = 0` using `by simpa using hw`. Establish `h` using `hsmul 0 0 D.zero_mem (u - 0) (by simpa using hu)`. Rewrite using `[hw0]`. Simplify using `using h`.

Consider the case `insert e t _ ih`. Rewrite `ht`, the goal using `[Finset.coe_insert]`. Establish `he : e ∈ D` using `ht (Set.mem_insert _ _)`. Establish `ht' : (↑t : Set V) ⊆ (D : Set V)` using `fun x hx => ht (Set.mem_insert_of_mem _ hx)`. Establish `hle : Submodule.span ℂ (t : Set V) ≤ D` using `Submodule.span_le.mpr ht'`.

Establish `hmono : Submodule.span ℂ (t : Set V) ≤ Submodule.span ℂ (insert e (t : Set V))` using `Submodule.span_mono (Set.subset_insert _ _)`. Introduce `u hu`. Take `⟨b, hb, hbo⟩` from `ih ht' e he`. Take `⟨a, ha, hao⟩` from `ih ht' u hu`. Establish `hf : e - b ∈ D` using `D.sub_mem he (hle hb)`.

Establish `hv : u - a ∈ D` using `D.sub_mem hu (hle ha)`. Establish `hfs : e - b ∈ Submodule.span ℂ (insert e (t : Set V))` using `Submodule.sub_mem _ (Submodule.subset_span (Set.mem_insert _ _)) (hmono hb)`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : ℂ, B (e - b) (u - a) + starRingEnd ℂ c * B (e - b) (e - b) = 0 := by`. Distinguish the cases in `h0 : B (e - b) (e - b) = 0`. Use `⟨0, ?_⟩` and prove the remaining obligations.

Rewrite using `[hherm (u - a) hv (e - b) hf, hrad (e - b) hf h0 (u - a) hv]`. Simplify using the standard rewrite rules. Use `⟨starRingEnd ℂ (-(B (e - b) (u - a) / B (e - b) (e - b))), ?_⟩` and prove the remaining obligations. Rewrite using `[Complex.conj_conj]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Use `⟨a - c • (e - b), Submodule.sub_mem _ (hmono ha) (Submodule.smul_mem _ c hfs), ?_⟩` and prove the remaining obligations. Introduce `w hw`. Take `⟨k, z, hz, rfl⟩` from `Submodule.mem_span_insert.mp hw`. Establish `hz' : k • b + z ∈ Submodule.span ℂ (t : Set V)` using `Submodule.add_mem _ (Submodule.smul_mem _ k hb) hz`.

Establish `e1 : u - (a - c • (e - b)) = (u - a) + c • (e - b)` using `by abel`. Establish `e2 : k • e + z = k • (e - b) + (k • b + z)` using `by rw [smul_sub]; abel`. Establish `hx : (u - a) + c • (e - b) ∈ D` using `D.add_mem hv (D.smul_mem c hf)`. Rewrite using `[e1, e2, hadd _ (D.smul_mem k hf) _ (hle hz') _ hx, hsmul k _ hf _ hx, hadd2 _ hf _ hv _ (D.smul_mem c hf), hsmul2 c _ hf _ hf, hc, hadd2 _ (hle hz') _ hv _ (D.smul_mem c hf), hsmul2 c _ (hle hz') _ hf, hao _ hz', hbo _ hz']`. Simplify using the standard rewrite rules.
-/
theorem exists_orthogonal_proj_span_finset_of_isotropic_radical
    {V : Type} [AddCommGroup V] [Module ℂ V] (B : V → V → ℂ) (D : Submodule ℂ V)
    (hadd : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, B (x + y) z = B x z + B y z)
    (hsmul : ∀ c : ℂ, ∀ x ∈ D, ∀ y ∈ D, B (c • x) y = c * B x y)
    (hherm : ∀ x ∈ D, ∀ y ∈ D, B y x = starRingEnd ℂ (B x y))
    (hrad : ∀ x ∈ D, B x x = 0 → ∀ y ∈ D, B y x = 0)
    (t : Finset V) (ht : (↑t : Set V) ⊆ (D : Set V)) :
    ∀ u ∈ D, ∃ a ∈ Submodule.span ℂ (t : Set V),
      ∀ w ∈ Submodule.span ℂ (t : Set V), B w (u - a) = 0 := by
  classical
  have hadd2 : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, B x (y + z) = B x y + B x z := by
    intro x hx y hy z hz
    rw [hherm (y + z) (D.add_mem hy hz) x hx, hadd y hy z hz x hx, map_add,
      ← hherm y hy x hx, ← hherm z hz x hx]
  have hsmul2 : ∀ c : ℂ, ∀ x ∈ D, ∀ y ∈ D, B x (c • y) = starRingEnd ℂ c * B x y := by
    intro c x hx y hy
    rw [hherm (c • y) (D.smul_mem c hy) x hx, hsmul c y hy x hx, map_mul, ← hherm y hy x hx]
  induction t using Finset.induction_on with
  | empty =>
    intro u hu
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    intro w hw
    have hw0 : w = 0 := by simpa using hw
    have h := hsmul 0 0 D.zero_mem (u - 0) (by simpa using hu)
    rw [hw0]
    simpa using h
  | insert e t _ ih =>
    rw [Finset.coe_insert] at ht ⊢
    have he : e ∈ D := ht (Set.mem_insert _ _)
    have ht' : (↑t : Set V) ⊆ (D : Set V) := fun x hx => ht (Set.mem_insert_of_mem _ hx)
    have hle : Submodule.span ℂ (t : Set V) ≤ D := Submodule.span_le.mpr ht'
    have hmono : Submodule.span ℂ (t : Set V) ≤ Submodule.span ℂ (insert e (t : Set V)) :=
      Submodule.span_mono (Set.subset_insert _ _)
    intro u hu
    obtain ⟨b, hb, hbo⟩ := ih ht' e he
    obtain ⟨a, ha, hao⟩ := ih ht' u hu
    have hf : e - b ∈ D := D.sub_mem he (hle hb)
    have hv : u - a ∈ D := D.sub_mem hu (hle ha)
    have hfs : e - b ∈ Submodule.span ℂ (insert e (t : Set V)) :=
      Submodule.sub_mem _ (Submodule.subset_span (Set.mem_insert _ _)) (hmono hb)
    obtain ⟨c, hc⟩ : ∃ c : ℂ, B (e - b) (u - a) + starRingEnd ℂ c * B (e - b) (e - b) = 0 := by
      by_cases h0 : B (e - b) (e - b) = 0
      · refine ⟨0, ?_⟩
        rw [hherm (u - a) hv (e - b) hf, hrad (e - b) hf h0 (u - a) hv]
        simp
      · refine ⟨starRingEnd ℂ (-(B (e - b) (u - a) / B (e - b) (e - b))), ?_⟩
        rw [Complex.conj_conj]
        field_simp
        ring
    refine ⟨a - c • (e - b), Submodule.sub_mem _ (hmono ha) (Submodule.smul_mem _ c hfs), ?_⟩
    intro w hw
    obtain ⟨k, z, hz, rfl⟩ := Submodule.mem_span_insert.mp hw
    have hz' : k • b + z ∈ Submodule.span ℂ (t : Set V) :=
      Submodule.add_mem _ (Submodule.smul_mem _ k hb) hz
    have e1 : u - (a - c • (e - b)) = (u - a) + c • (e - b) := by abel
    have e2 : k • e + z = k • (e - b) + (k • b + z) := by rw [smul_sub]; abel
    have hx : (u - a) + c • (e - b) ∈ D := D.add_mem hv (D.smul_mem c hf)
    rw [e1, e2, hadd _ (D.smul_mem k hf) _ (hle hz') _ hx, hsmul k _ hf _ hx,
      hadd2 _ hf _ hv _ (D.smul_mem c hf), hsmul2 c _ hf _ hf, hc,
      hadd2 _ (hle hz') _ hv _ (D.smul_mem c hf), hsmul2 c _ (hle hz') _ hf,
      hao _ hz', hbo _ hz']
    simp

/- English proof (translation)
Introduce `V _ _ B D hadd hsmul hherm hrad W hW s hs hfin u hu`. Set `R : Submodule ℂ V` to `{ carrier := {x | x ∈ D ∧ ∀ y ∈ D, B x y = 0} add_mem' := by`. Introduce and unpack `x y ⟨hx, hx'⟩ ⟨hy, hy'⟩`. Use `⟨D.add_mem hx hy, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[hadd x hx y hy z hz, hx' z hz, hy' z hz, add_zero]`.

Use the proof step `zero_mem' := by`. Use `⟨D.zero_mem, fun z hz => ?_⟩` and prove the remaining obligations. Simplify using `using hsmul 0 0 D.zero_mem z hz`. Use the proof step `smul_mem' := by`. Introduce and unpack `c x ⟨hx, hx'⟩`.

Use `⟨D.smul_mem c hx, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[hsmul c x hx z hz, hx' z hz, mul_zero] }`. Establish `hsD : Submodule.span ℂ (s : Set V) ≤ D` using `Submodule.span_le.mpr hs`. Establish `hle : W.map R.mkQ ≤ (Submodule.span ℂ (s : Set V)).map R.mkQ`. Introduce and unpack `_ ⟨w, hw, rfl⟩`.

Take `⟨z, hz, h0⟩` from `hfin w hw`. Establish `hd : w - z ∈ D` using `D.sub_mem (hW hw) (hsD hz)`. Use `⟨z, hz, ?_⟩` and prove the remaining obligations. Use `symm`. Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]`.

Use `⟨hd, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[hherm y hy (w - z) hd, hrad _ hd h0 y hy, map_zero]`. Establish `hfg : ((Submodule.span ℂ (s : Set V)).map R.mkQ).FG` using `Submodule.FG.map _ ⟨s, rfl⟩`. Use `haveI : FiniteDimensional ℂ ((Submodule.span ℂ (s : Set V)).map R.mkQ) := Module.Finite.iff_fg.mpr hfg`. Establish `hfg' : (W.map R.mkQ).FG` using `Module.Finite.iff_fg.mp (Submodule.finiteDimensional_of_le hle)`.

Take `⟨S, hS⟩` from `hfg'`. Establish `hsub : (↑S : Set (V ⧸ R)) ⊆ R.mkQ '' (W : Set V)`. Introduce `x hx`. Establish `: x ∈ W.map R.mkQ` using `hS ▸ Submodule.subset_span hx`. Conclude with `this`.

Take `⟨t, htW, htS⟩` from `Finset.subset_set_image_iff.mp hsub`. Establish `htW' : Submodule.span ℂ (t : Set V) ≤ W` using `Submodule.span_le.mpr htW`. Take `⟨a, ha, hao⟩` from `exists_orthogonal_proj_span_finset_of_isotropic_radical B D hadd hsmul hherm hrad t (fun x hx => hW (htW hx)) u hu`. Use `⟨a, htW' ha, fun w hw => ?_⟩` and prove the remaining obligations. Establish `hw' : R.mkQ w ∈ (Submodule.span ℂ (t : Set V)).map R.mkQ`.

Rewrite using `[Submodule.map_span, ← Finset.coe_image, htS, hS]`. Conclude with `Submodule.mem_map_of_mem hw`. Take `⟨z, hz, hzw⟩` from `hw'`. Rewrite `hzw` using `[Submodule.mkQ_apply, Submodule.mkQ_apply, eq_comm, Submodule.Quotient.eq]`. Establish `hv : u - a ∈ D` using `D.sub_mem hu (hW (htW' ha))`.

Establish `e1 : w = (w - z) + z` using `by abel`. Rewrite using `[e1, hadd _ hzw.1 _ (hW (htW' hz)) _ hv, hzw.2 _ hv, hao z hz, add_zero]`.
-/
theorem exists_orthogonal_proj_of_finite_mod_radical :
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (B : V → V → ℂ) (D : Submodule ℂ V),
    (∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, B (x + y) z = B x z + B y z) →
    (∀ c : ℂ, ∀ x ∈ D, ∀ y ∈ D, B (c • x) y = c * B x y) →
    (∀ x ∈ D, ∀ y ∈ D, B y x = starRingEnd ℂ (B x y)) →
    (∀ x ∈ D, B x x = 0 → ∀ y ∈ D, B y x = 0) →
    ∀ (W : Submodule ℂ V), W ≤ D → ∀ (s : Finset V), (↑s ⊆ (D : Set V)) →
    (∀ w ∈ W, ∃ z ∈ Submodule.span ℂ (s : Set V), B (w - z) (w - z) = 0) →
    ∀ u ∈ D, ∃ a ∈ W, ∀ w ∈ W, B w (u - a) = 0 := by
  intro V _ _ B D hadd hsmul hherm hrad W hW s hs hfin u hu
  classical
  let R : Submodule ℂ V :=
    { carrier := {x | x ∈ D ∧ ∀ y ∈ D, B x y = 0}
      add_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨D.add_mem hx hy, fun z hz => ?_⟩
        rw [hadd x hx y hy z hz, hx' z hz, hy' z hz, add_zero]
      zero_mem' := by
        refine ⟨D.zero_mem, fun z hz => ?_⟩
        simpa using hsmul 0 0 D.zero_mem z hz
      smul_mem' := by
        rintro c x ⟨hx, hx'⟩
        refine ⟨D.smul_mem c hx, fun z hz => ?_⟩
        rw [hsmul c x hx z hz, hx' z hz, mul_zero] }
  have hsD : Submodule.span ℂ (s : Set V) ≤ D := Submodule.span_le.mpr hs
  have hle : W.map R.mkQ ≤ (Submodule.span ℂ (s : Set V)).map R.mkQ := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨z, hz, h0⟩ := hfin w hw
    have hd : w - z ∈ D := D.sub_mem (hW hw) (hsD hz)
    refine ⟨z, hz, ?_⟩
    symm
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    refine ⟨hd, fun y hy => ?_⟩
    rw [hherm y hy (w - z) hd, hrad _ hd h0 y hy, map_zero]
  have hfg : ((Submodule.span ℂ (s : Set V)).map R.mkQ).FG :=
    Submodule.FG.map _ ⟨s, rfl⟩
  haveI : FiniteDimensional ℂ ((Submodule.span ℂ (s : Set V)).map R.mkQ) :=
    Module.Finite.iff_fg.mpr hfg
  have hfg' : (W.map R.mkQ).FG :=
    Module.Finite.iff_fg.mp (Submodule.finiteDimensional_of_le hle)
  obtain ⟨S, hS⟩ := hfg'
  have hsub : (↑S : Set (V ⧸ R)) ⊆ R.mkQ '' (W : Set V) := by
    intro x hx
    have : x ∈ W.map R.mkQ := hS ▸ Submodule.subset_span hx
    exact this
  obtain ⟨t, htW, htS⟩ := Finset.subset_set_image_iff.mp hsub
  have htW' : Submodule.span ℂ (t : Set V) ≤ W := Submodule.span_le.mpr htW
  obtain ⟨a, ha, hao⟩ := exists_orthogonal_proj_span_finset_of_isotropic_radical B D hadd hsmul
    hherm hrad t (fun x hx => hW (htW hx)) u hu
  refine ⟨a, htW' ha, fun w hw => ?_⟩
  have hw' : R.mkQ w ∈ (Submodule.span ℂ (t : Set V)).map R.mkQ := by
    rw [Submodule.map_span, ← Finset.coe_image, htS, hS]
    exact Submodule.mem_map_of_mem hw
  obtain ⟨z, hz, hzw⟩ := hw'
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, eq_comm, Submodule.Quotient.eq] at hzw
  have hv : u - a ∈ D := D.sub_mem hu (hW (htW' ha))
  have e1 : w = (w - z) + z := by abel
  rw [e1, hadd _ hzw.1 _ (hW (htW' hz)) _ hv, hzw.2 _ hv, hao z hz, add_zero]

end GlobalTheory
