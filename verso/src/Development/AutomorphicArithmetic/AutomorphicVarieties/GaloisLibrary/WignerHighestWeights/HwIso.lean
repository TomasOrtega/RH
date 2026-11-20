import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.LowStab
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.LowLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

/- English proof (translation)
Introduce `ι V _ _ _ n F V' _ _ F' hF hF' hS hS' ν v v' hv0 hv0' hv hv'`. Set `P : ι → Fin n → Fin n → Module.End ℂ (V × V')` to `fun t i j => (F t i j).prodMap (F' t i j)`. Establish `hPa : ∀ t i j (x : V) (y : V'), P t i j (x, y) = (F t i j x, F' t i j y)` using `fun _ _ _ _ _ => rfl`. Establish `hP : IsMultiGl P`. Use `⟨fun t i j k l => ?_, fun s t hst i j k l => ?_⟩` and prove the remaining obligations.

Use `LinearMap.ext fun z => ?_` and prove the remaining obligations. Establish `e` using `LinearMap.congr_fun (hF.1 t i j k l) z.1`. Establish `e'` using `LinearMap.congr_fun (hF'.1 t i j k l) z.2`. Use `Prod.ext (e.trans ?_) (e'.trans ?_)` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> rfl`.

Apply the tactic sequence `split_ifs <;> rfl`. Use `LinearMap.ext fun z => ?_` and prove the remaining obligations. Conclude with `Prod.ext (LinearMap.congr_fun (hF.2 s t hst i j k l) z.1) (LinearMap.congr_fun (hF'.2 s t hst i j k l) z.2)`. Establish `hvv : ∀ t, Formalism.REAL.IsHW (P t) (ν t) (v, v')` using `fun t => ⟨fun i => Prod.ext ((hv t).1 i) ((hv' t).1 i), fun i j h => Prod.ext ((hv t).2 i j h) ((hv' t).2 i j h)⟩`. Take `⟨hm, hst⟩` from `lowStab ι (V × V') n P hP ν (v, v') hvv`.

Establish `hl` using `lowLine ι (V × V') n P hP ν (v, v') hvv`. Generalize the expression as in `low P (v, v') = W at hm hst hl`. Establish `hA : ∀ y : V', ((0 : V), y) ∈ W → y = 0`. Break down `hS' (W.comap (LinearMap.inr ℂ V V')) (fun t i j w hw => by` into its components or cases. Use `hst t i j _ hw` as an intermediate fact.

Rewrite using `[LinearMap.inr_apply, hPa, map_zero] at this) with h | h` and apply the resulting hypothesis. Conclude with `fun y hy => (Submodule.eq_bot_iff _).1 h y hy`. Establish `h1 : ((0 : V), v') ∈ W` using `(Submodule.eq_top_iff'.1 h v' :)`. Take `⟨c, hc⟩` from `hl _ h1 fun t k => by`. Rewrite using `[hPa, map_zero, (hv' t).1 k, Prod.smul_mk, smul_zero]`.

Establish `h2 : c = 0` using `(smul_eq_zero.1 (congrArg Prod.fst hc).symm).resolve_right hv0`. Rewrite `hc` using `[h2, zero_smul]`. Conclude with `absurd (congrArg Prod.snd hc) hv0'`. Establish `hB : ∀ x : V, (x, (0 : V')) ∈ W → x = 0`. Break down `hS (W.comap (LinearMap.inl ℂ V V')) (fun t i j w hw => by` into its components or cases.

Use `hst t i j _ hw` as an intermediate fact. Rewrite using `[LinearMap.inl_apply, hPa, map_zero] at this) with h | h` and apply the resulting hypothesis. Conclude with `fun y hy => (Submodule.eq_bot_iff _).1 h y hy`. Establish `h1 : (v, (0 : V')) ∈ W` using `(Submodule.eq_top_iff'.1 h v :)`. Take `⟨c, hc⟩` from `hl _ h1 fun t k => by`.

Rewrite using `[hPa, map_zero, (hv t).1 k, Prod.smul_mk, smul_zero]`. Establish `h2 : c = 0` using `(smul_eq_zero.1 (congrArg Prod.snd hc).symm).resolve_right hv0'`. Rewrite `hc` using `[h2, zero_smul]`. Conclude with `absurd (congrArg Prod.fst hc) hv0`. Establish `hC : W.map (LinearMap.fst ℂ V V') = ⊤`.

Use `(hS _ ?_).resolve_left fun h => hv0 ((Submodule.eq_bot_iff _).1 h v ⟨_, hm, rfl⟩)` and prove the remaining obligations. Introduce and unpack `t i j _ ⟨z, hz, rfl⟩`. Conclude with `⟨_, hst t i j z hz, rfl⟩`. Establish `hD : W.map (LinearMap.snd ℂ V V') = ⊤`. Use `(hS' _ ?_).resolve_left fun h => hv0' ((Submodule.eq_bot_iff _).1 h v' ⟨_, hm, rfl⟩)` and prove the remaining obligations.

Introduce and unpack `t i j _ ⟨z, hz, rfl⟩`. Conclude with `⟨_, hst t i j z hz, rfl⟩`. Establish `b1 : Function.Bijective ((LinearMap.fst ℂ V V').comp W.subtype)`. Use `⟨(injective_iff_map_eq_zero _).2 ?_, fun x => ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨⟨x, y⟩, hz⟩ (rfl : x = 0)`.

Conclude with `Subtype.ext (Prod.ext rfl (hA y hz))`. Take `⟨z, hz, rfl⟩` from `Submodule.eq_top_iff'.1 hC x`. Conclude with `⟨⟨z, hz⟩, rfl⟩`. Establish `b2 : Function.Bijective ((LinearMap.snd ℂ V V').comp W.subtype)`. Use `⟨(injective_iff_map_eq_zero _).2 ?_, fun x => ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨⟨x, y⟩, hz⟩ (rfl : y = 0)`. Conclude with `Subtype.ext (Prod.ext (hB x hz) rfl)`. Take `⟨z, hz, rfl⟩` from `Submodule.eq_top_iff'.1 hD x`. Conclude with `⟨⟨z, hz⟩, rfl⟩`. Establish `key : ∀ z : W, ((LinearEquiv.ofBijective _ b1).symm.trans (LinearEquiv.ofBijective _ b2)) z.1.1 = z.1.2`.

Introduce `z`. Establish `: (LinearEquiv.ofBijective _ b1).symm z.1.1 = z` using `(LinearEquiv.ofBijective _ b1).symm_apply_apply z`. Rewrite using `[LinearEquiv.trans_apply, this]`. Both sides reduce to the same expression. Use `⟨(LinearEquiv.ofBijective _ b1).symm.trans (LinearEquiv.ofBijective _ b2), fun t i j x => ?_⟩` and prove the remaining obligations.

Take `⟨z, rfl⟩` from `b1.2 x`. Conclude with `(key ⟨_, hst t i j z.1 z.2⟩).trans (congrArg (F' t i j) (key z).symm)`.
-/
theorem UpperTheory.V.AlgRepEndIrreducible.hwIso :
    ∀ (ι V : Type) [Fintype ι] [AddCommGroup V] [Module ℂ V] (n : ℕ) (F : ι → Fin n → Fin n → Module.End ℂ V) (V' : Type) [AddCommGroup V'] [Module ℂ V'] (F' : ι → Fin n → Fin n → Module.End ℂ V'),
      IsMultiGl F → IsMultiGl F' → (∀ W, Stab F W → W = ⊥ ∨ W = ⊤) → (∀ W, Stab F' W → W = ⊥ ∨ W = ⊤) →
      ∀ (ν : ι → Fin n → ℂ) (v : V) (v' : V'), v ≠ 0 → v' ≠ 0 → (∀ t, Formalism.REAL.IsHW (F t) (ν t) v) →
        (∀ t, Formalism.REAL.IsHW (F' t) (ν t) v') → ∃ T : V ≃ₗ[ℂ] V', ∀ t i j x, T (F t i j x) = F' t i j (T x) := by
  intro ι V _ _ _ n F V' _ _ F' hF hF' hS hS' ν v v' hv0 hv0' hv hv'
  let P : ι → Fin n → Fin n → Module.End ℂ (V × V') := fun t i j => (F t i j).prodMap (F' t i j)
  have hPa : ∀ t i j (x : V) (y : V'), P t i j (x, y) = (F t i j x, F' t i j y) := fun _ _ _ _ _ => rfl
  have hP : IsMultiGl P := by
    refine ⟨fun t i j k l => ?_, fun s t hst i j k l => ?_⟩
    · refine LinearMap.ext fun z => ?_
      have e := LinearMap.congr_fun (hF.1 t i j k l) z.1
      have e' := LinearMap.congr_fun (hF'.1 t i j k l) z.2
      refine Prod.ext (e.trans ?_) (e'.trans ?_)
      · split_ifs <;> rfl
      · split_ifs <;> rfl
    · refine LinearMap.ext fun z => ?_
      exact Prod.ext (LinearMap.congr_fun (hF.2 s t hst i j k l) z.1)
        (LinearMap.congr_fun (hF'.2 s t hst i j k l) z.2)
  have hvv : ∀ t, Formalism.REAL.IsHW (P t) (ν t) (v, v') := fun t =>
    ⟨fun i => Prod.ext ((hv t).1 i) ((hv' t).1 i),
      fun i j h => Prod.ext ((hv t).2 i j h) ((hv' t).2 i j h)⟩
  obtain ⟨hm, hst⟩ := lowStab ι (V × V') n P hP ν (v, v') hvv
  have hl := lowLine ι (V × V') n P hP ν (v, v') hvv
  generalize low P (v, v') = W at hm hst hl
  have hA : ∀ y : V', ((0 : V), y) ∈ W → y = 0 := by
    rcases hS' (W.comap (LinearMap.inr ℂ V V')) (fun t i j w hw => by
      have := hst t i j _ hw
      rwa [LinearMap.inr_apply, hPa, map_zero] at this) with h | h
    · exact fun y hy => (Submodule.eq_bot_iff _).1 h y hy
    · have h1 : ((0 : V), v') ∈ W := (Submodule.eq_top_iff'.1 h v' :)
      obtain ⟨c, hc⟩ := hl _ h1 fun t k => by
        rw [hPa, map_zero, (hv' t).1 k, Prod.smul_mk, smul_zero]
      have h2 : c = 0 := (smul_eq_zero.1 (congrArg Prod.fst hc).symm).resolve_right hv0
      rw [h2, zero_smul] at hc
      exact absurd (congrArg Prod.snd hc) hv0'
  have hB : ∀ x : V, (x, (0 : V')) ∈ W → x = 0 := by
    rcases hS (W.comap (LinearMap.inl ℂ V V')) (fun t i j w hw => by
      have := hst t i j _ hw
      rwa [LinearMap.inl_apply, hPa, map_zero] at this) with h | h
    · exact fun y hy => (Submodule.eq_bot_iff _).1 h y hy
    · have h1 : (v, (0 : V')) ∈ W := (Submodule.eq_top_iff'.1 h v :)
      obtain ⟨c, hc⟩ := hl _ h1 fun t k => by
        rw [hPa, map_zero, (hv t).1 k, Prod.smul_mk, smul_zero]
      have h2 : c = 0 := (smul_eq_zero.1 (congrArg Prod.snd hc).symm).resolve_right hv0'
      rw [h2, zero_smul] at hc
      exact absurd (congrArg Prod.fst hc) hv0
  have hC : W.map (LinearMap.fst ℂ V V') = ⊤ := by
    refine (hS _ ?_).resolve_left fun h => hv0 ((Submodule.eq_bot_iff _).1 h v ⟨_, hm, rfl⟩)
    rintro t i j _ ⟨z, hz, rfl⟩
    exact ⟨_, hst t i j z hz, rfl⟩
  have hD : W.map (LinearMap.snd ℂ V V') = ⊤ := by
    refine (hS' _ ?_).resolve_left fun h => hv0' ((Submodule.eq_bot_iff _).1 h v' ⟨_, hm, rfl⟩)
    rintro t i j _ ⟨z, hz, rfl⟩
    exact ⟨_, hst t i j z hz, rfl⟩
  have b1 : Function.Bijective ((LinearMap.fst ℂ V V').comp W.subtype) := by
    refine ⟨(injective_iff_map_eq_zero _).2 ?_, fun x => ?_⟩
    · rintro ⟨⟨x, y⟩, hz⟩ (rfl : x = 0)
      exact Subtype.ext (Prod.ext rfl (hA y hz))
    · obtain ⟨z, hz, rfl⟩ := Submodule.eq_top_iff'.1 hC x
      exact ⟨⟨z, hz⟩, rfl⟩
  have b2 : Function.Bijective ((LinearMap.snd ℂ V V').comp W.subtype) := by
    refine ⟨(injective_iff_map_eq_zero _).2 ?_, fun x => ?_⟩
    · rintro ⟨⟨x, y⟩, hz⟩ (rfl : y = 0)
      exact Subtype.ext (Prod.ext (hB x hz) rfl)
    · obtain ⟨z, hz, rfl⟩ := Submodule.eq_top_iff'.1 hD x
      exact ⟨⟨z, hz⟩, rfl⟩
  have key : ∀ z : W, ((LinearEquiv.ofBijective _ b1).symm.trans (LinearEquiv.ofBijective _ b2)) z.1.1 = z.1.2 := by
    intro z
    have : (LinearEquiv.ofBijective _ b1).symm z.1.1 = z := (LinearEquiv.ofBijective _ b1).symm_apply_apply z
    rw [LinearEquiv.trans_apply, this]
    rfl
  refine ⟨(LinearEquiv.ofBijective _ b1).symm.trans (LinearEquiv.ofBijective _ b2), fun t i j x => ?_⟩
  obtain ⟨z, rfl⟩ := b1.2 x
  exact (key ⟨_, hst t i j z.1 z.2⟩).trans (congrArg (F' t i j) (key z).symm)
