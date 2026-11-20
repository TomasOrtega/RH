import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerDatumOfIsotropicSaturated
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoprimeScaledIsometrySameSignature
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianLatticeSignatureSplitOfIndefinite

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt.IsoSat

open ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Distinguish the cases in `h3 : 3 ≤ D.p + D.q`. Establish `hξ` using `GlobalTheory.OneSpace.cc_rt H`. Establish `hξ0` using `GlobalTheory.OneSpace.rt_ne H`. Take `⟨G, φ, hM⟩` from `GlobalTheory.exists_herm_coord_of_datum E H D (H.rt : E) hξ hξ0 (D.p + D.q) rfl`. Establish `hind` using `GlobalTheory.SplitGenus.indefinite D hp hq G φ hM`.

Take `⟨inj, span, hG, hdet, hEF⟩` from `hM`. Establish `hh : GlobalTheory.UTrans.IsHerm (IsCMField.complexConj E : E →+* E) G`. Use `⟨fun a => IsCMField.complexConj_apply_apply E a, ⟨(H.rt : E), fun h => hξ0 ?_⟩, hG, hdet⟩` and prove the remaining obligations. Establish `h2 : (H.rt : E) = -(H.rt : E)` using `h.symm.trans hξ`. Take the linear combination `(1 / 2 : E) * h2`.

Take `⟨z, hz0, hz⟩` from `GlobalTheory.UTrans.exists_isotropic_of_indefinite E _ _ G (fun _ => rfl) hh h3 hind`. Establish `hz' : FD.herm G z z = 0` using `hz`. Take `⟨N, g, hN, hg⟩` from `GlobalTheory.SplitGenus.exists_scaled_map (LinearMap.toSpanSingleton (𝓞 E) _ z) φ inj span`. Establish `h1 : φ (g 1) = (N : E) • z` using `by rw [hg, LinearMap.toSpanSingleton_apply, one_smul]`. Use `⟨g 1, fun h => ?_, fun a => ?_⟩` and prove the remaining obligations.

Rewrite `h1` using `[h, map_zero, eq_comm, smul_eq_zero]`. Conclude with `h1.elim (Nat.cast_ne_zero.2 hN.ne') hz0`. Establish `h2` using `hEF (a • g 1) (g 1)`. Rewrite `h2` using `[map_smul φ, h1, show a • (N : E) • z = (a : E) • (N : E) • z from rfl, GlobalTheory.HermModel.herm_smul_left, GlobalTheory.HermModel.herm_smul_left, GlobalTheory.HermModel.herm_smul_right, hz']`. Simplify using `only [zero_mul, mul_zero, map_zero] at h2`.

Conclude with `h2` after adjusting the coercions. Apply the tactic sequence `obtain ⟨k, f, hk, hf⟩ := GlobalTheory.LocalIsomAt.exists_coprime_scaled_isometry E H (GlobalTheory.HostModel.hypDatum H) D (by change D.p = 1; omega) (by change D.q = 1; omega) 2 two_pos`. Establish `hk0 : (k : ℤ) ^ 2 ≠ 0`. Establish `: k ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at hk`. Check the signs of the components of the expression. Use `⟨f (1, 0), fun h => ?_, fun a => ?_⟩` and prove the remaining obligations. Establish `: ((1, 0) : (GlobalTheory.HostModel.hypDatum H).La) = 0` using `(GlobalTheory.HostModel.hypDatum H).unimod.1 (LinearMap.ext fun y => by`. Use `hf (1, 0) y` as an intermediate fact.

Rewrite `this` using `[h, map_zero, LinearMap.zero_apply]`. Rewrite using `[map_zero, LinearMap.zero_apply]`. Conclude with `(mul_eq_zero.1 this.symm).resolve_left hk0)`. Conclude with `one_ne_zero (congrArg Prod.fst this)`. Rewrite using `[← map_smul, hf, GlobalTheory.HostModel.hypDatum_smul, smul_zero, GlobalTheory.HostModel.hypDatum_EF_inl_inl, mul_zero]`.
-/
theorem exists_isotropic_vector (D : Datum H) (hp : 1 ≤ D.p) (hq : 1 ≤ D.q) :
    ∃ x : D.La, x ≠ 0 ∧ ∀ a : 𝓞 E, D.EF (a • x) x = 0 := by
  by_cases h3 : 3 ≤ D.p + D.q
  · have hξ := GlobalTheory.OneSpace.cc_rt H
    have hξ0 := GlobalTheory.OneSpace.rt_ne H
    obtain ⟨G, φ, hM⟩ := GlobalTheory.exists_herm_coord_of_datum E H D (H.rt : E) hξ hξ0 (D.p + D.q) rfl
    have hind := GlobalTheory.SplitGenus.indefinite D hp hq G φ hM
    obtain ⟨inj, span, hG, hdet, hEF⟩ := hM
    have hh : GlobalTheory.UTrans.IsHerm (IsCMField.complexConj E : E →+* E) G := by
      refine ⟨fun a => IsCMField.complexConj_apply_apply E a, ⟨(H.rt : E), fun h => hξ0 ?_⟩, hG, hdet⟩
      have h2 : (H.rt : E) = -(H.rt : E) := h.symm.trans hξ
      linear_combination (1 / 2 : E) * h2
    obtain ⟨z, hz0, hz⟩ := GlobalTheory.UTrans.exists_isotropic_of_indefinite E _ _ G (fun _ => rfl) hh h3 hind
    have hz' : FD.herm G z z = 0 := hz
    obtain ⟨N, g, hN, hg⟩ := GlobalTheory.SplitGenus.exists_scaled_map (LinearMap.toSpanSingleton (𝓞 E) _ z) φ inj span
    have h1 : φ (g 1) = (N : E) • z := by rw [hg, LinearMap.toSpanSingleton_apply, one_smul]
    refine ⟨g 1, fun h => ?_, fun a => ?_⟩
    · rw [h, map_zero, eq_comm, smul_eq_zero] at h1
      exact h1.elim (Nat.cast_ne_zero.2 hN.ne') hz0
    · have h2 := hEF (a • g 1) (g 1)
      rw [map_smul φ, h1, show a • (N : E) • z = (a : E) • (N : E) • z from rfl, GlobalTheory.HermModel.herm_smul_left,
        GlobalTheory.HermModel.herm_smul_left, GlobalTheory.HermModel.herm_smul_right, hz'] at h2
      simp only [zero_mul, mul_zero, map_zero] at h2
      exact_mod_cast h2
  · obtain ⟨k, f, hk, hf⟩ := GlobalTheory.LocalIsomAt.exists_coprime_scaled_isometry E H (GlobalTheory.HostModel.hypDatum H) D
      (by change D.p = 1; omega) (by change D.q = 1; omega) 2 two_pos
    have hk0 : (k : ℤ) ^ 2 ≠ 0 := by
      have : k ≠ 0 := by
        rintro rfl
        simp at hk
      positivity
    refine ⟨f (1, 0), fun h => ?_, fun a => ?_⟩
    · have : ((1, 0) : (GlobalTheory.HostModel.hypDatum H).La) = 0 := (GlobalTheory.HostModel.hypDatum H).unimod.1 (LinearMap.ext fun y => by
        have := hf (1, 0) y
        rw [h, map_zero, LinearMap.zero_apply] at this
        rw [map_zero, LinearMap.zero_apply]
        exact (mul_eq_zero.1 this.symm).resolve_left hk0)
      exact one_ne_zero (congrArg Prod.fst this)
    · rw [← map_smul, hf, GlobalTheory.HostModel.hypDatum_smul, smul_zero, GlobalTheory.HostModel.hypDatum_EF_inl_inl, mul_zero]

/- English proof (translation)
Use `D.fin` as an intermediate fact. Set `Z : Submodule (𝓞 E) D.La` to `{ carrier := {x | ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ W} zero_mem' := ⟨1, one_ne_zero, by simp⟩ add_mem' := by`. Introduce and unpack `x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩`. Use `⟨n * m, mul_ne_zero hn hm, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`.

Use `add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `nsmul_mem hx m`. Rewrite using `[mul_smul]`. Conclude with `nsmul_mem hy n`.

Use the proof step `smul_mem' := by`. Introduce and unpack `a x ⟨n, hn, hx⟩`. Conclude with `⟨n, hn, by rw [smul_comm]; exact W.smul_mem a hx⟩ }`. Establish `hle : W ≤ Z` using `fun x hx => ⟨1, one_ne_zero, by rwa [one_smul]⟩`. Use `⟨Z, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `x ⟨n, hn, hx⟩ y ⟨m, hm, hy⟩`. Use `hW hx _ hy` as an intermediate fact. Simplify `this` using `[hn, hm]`. Introduce and unpack `n x hn ⟨m, hm, hx⟩`. Conclude with `⟨m * n, mul_ne_zero hm hn, by rwa [mul_smul]⟩`.

Establish `h1` using `Submodule.finrank_quotient_add_finrank (W.comap Z.subtype)`. Establish `h2 : Module.finrank (𝓞 E) (Z ⧸ W.comap Z.subtype) = 0`. Rewrite using `[Module.finrank_eq_zero_iff]`. Introduce `x`. Take `⟨⟨x, n, hn, hx⟩, rfl⟩` from `Submodule.mkQ_surjective _ x`.

Use `⟨(n : 𝓞 E), Nat.cast_ne_zero.2 hn, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Nat.cast_smul_eq_nsmul]`. Conclude with `hx`. Rewrite using `[← h1, h2, zero_add, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq]`.
-/
theorem exists_saturation (D : Datum H) (W : Submodule (𝓞 E) D.La) (hW : W ≤ perp D W) :
    ∃ Z : Submodule (𝓞 E) D.La, IsIsoSat D Z ∧ Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) W := by
  have := D.fin
  let Z : Submodule (𝓞 E) D.La :=
    { carrier := {x | ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ W}
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      add_mem' := by
        rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
        refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
        rw [smul_add]
        refine add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact nsmul_mem hx m
        · rw [mul_smul]; exact nsmul_mem hy n
      smul_mem' := by
        rintro a x ⟨n, hn, hx⟩
        exact ⟨n, hn, by rw [smul_comm]; exact W.smul_mem a hx⟩ }
  have hle : W ≤ Z := fun x hx => ⟨1, one_ne_zero, by rwa [one_smul]⟩
  refine ⟨Z, ⟨?_, ?_⟩, ?_⟩
  · rintro x ⟨n, hn, hx⟩ y ⟨m, hm, hy⟩
    have := hW hx _ hy
    simpa [hn, hm] using this
  · rintro n x hn ⟨m, hm, hx⟩
    exact ⟨m * n, mul_ne_zero hm hn, by rwa [mul_smul]⟩
  · have h1 := Submodule.finrank_quotient_add_finrank (W.comap Z.subtype)
    have h2 : Module.finrank (𝓞 E) (Z ⧸ W.comap Z.subtype) = 0 := by
      rw [Module.finrank_eq_zero_iff]
      intro x
      obtain ⟨⟨x, n, hn, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ x
      refine ⟨(n : 𝓞 E), Nat.cast_ne_zero.2 hn, ?_⟩
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Nat.cast_smul_eq_nsmul]
      exact hx
    rw [← h1, h2, zero_add, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq]

/- English proof (translation)
Use `D.fin` as an intermediate fact. Take `⟨D', f, ⟨hs, hk, hE⟩, hp, hq⟩` from `exists_lowerDatum D Z hZ`. Take `⟨x', hx0, hx⟩` from `exists_isotropic_vector D' (by omega) (by omega)`. Take `⟨x, rfl⟩` from `hs x'`. Use `D'.proj` as an intermediate fact.

Establish `hnot : ∀ a : 𝓞 E, a • (x : D.La) ∈ Z → a = 0` using `fun a ha => by`. Establish `h` using `(hk (a • x)).2 ha`. Rewrite `h` using `[map_smul, smul_eq_zero]`. Conclude with `h.resolve_right hx0`. Set `g : (Z × 𝓞 E) →ₗ[𝓞 E] D.La` to `Z.subtype.coprod (LinearMap.toSpanSingleton (𝓞 E) _ (x : D.La))`.

Establish `hg : ∀ u, g u = u.1 + u.2 • (x : D.La)` using `fun u => rfl`. Establish `hinj : Function.Injective g` using `(injective_iff_map_eq_zero g).2 fun u hu => by`. Rewrite `hu` using `[hg]`. Establish `h2 : u.2 = 0` using `hnot _ (by rw [eq_neg_of_add_eq_zero_right hu]; exact neg_mem u.1.2)`. Rewrite `hu` using `[h2, zero_smul, add_zero]`.

Conclude with `Prod.ext (Subtype.ext hu) h2`. Take `⟨Z', h1, h2⟩` from `exists_saturation D (LinearMap.range g) (by`. Introduce and unpack `_ ⟨u, rfl⟩ _ ⟨v, rfl⟩`. Establish `e1 : D.EF u.1 v.1 = 0` using `hZ.1 u.1.2 _ v.1.2`. Establish `e2 : ∀ (a : 𝓞 E) (z : Z), D.EF (a • (x : D.La)) z = 0` using `fun a z => (a • x).2 _ z.2`.

Establish `e3 : D.EF (u.2 • (x : D.La)) (v.2 • (x : D.La)) = 0`. Establish `h` using `hx (H.bar v.2 * u.2)`. Rewrite `h` using `[← map_smul, hE, Submodule.coe_smul, mul_smul, D.adj, bar_bar]`. Conclude with `h`. Rewrite using `[hg, hg]`.

Simplify using `only [map_add, LinearMap.add_apply]`. Rewrite using `[e1, e2, e3, ef_swap, e2]`. Use the proof step `simp)`. Use `⟨Z', h1, ?_⟩` and prove the remaining obligations. Rewrite using `[h2, ← (LinearEquiv.ofInjective g hinj).finrank_eq]`.

Establish `h3` using `Submodule.finrank_quotient_add_finrank (LinearMap.ker (LinearMap.snd (𝓞 E) Z (𝓞 E)))`. Rewrite `h3` using `[((LinearMap.snd (𝓞 E) Z (𝓞 E)).quotKerEquivOfSurjective LinearMap.snd_surjective).finrank_eq, Module.finrank_self, ← LinearMap.range_inl, ← (LinearEquiv.ofInjective _ LinearMap.inl_injective).finrank_eq]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_succ (D : Datum H) (Z : Submodule (𝓞 E) D.La) (hZ : IsIsoSat D Z)
    (hr : Module.finrank (𝓞 E) Z + 1 ≤ min D.p D.q) :
    ∃ Z' : Submodule (𝓞 E) D.La, IsIsoSat D Z' ∧ Module.finrank (𝓞 E) Z' = Module.finrank (𝓞 E) Z + 1 := by
  have := D.fin
  obtain ⟨D', f, ⟨hs, hk, hE⟩, hp, hq⟩ := exists_lowerDatum D Z hZ
  obtain ⟨x', hx0, hx⟩ := exists_isotropic_vector D' (by omega) (by omega)
  obtain ⟨x, rfl⟩ := hs x'
  have := D'.proj
  have hnot : ∀ a : 𝓞 E, a • (x : D.La) ∈ Z → a = 0 := fun a ha => by
    have h := (hk (a • x)).2 ha
    rw [map_smul, smul_eq_zero] at h
    exact h.resolve_right hx0
  let g : (Z × 𝓞 E) →ₗ[𝓞 E] D.La := Z.subtype.coprod (LinearMap.toSpanSingleton (𝓞 E) _ (x : D.La))
  have hg : ∀ u, g u = u.1 + u.2 • (x : D.La) := fun u => rfl
  have hinj : Function.Injective g := (injective_iff_map_eq_zero g).2 fun u hu => by
    rw [hg] at hu
    have h2 : u.2 = 0 := hnot _ (by rw [eq_neg_of_add_eq_zero_right hu]; exact neg_mem u.1.2)
    rw [h2, zero_smul, add_zero] at hu
    exact Prod.ext (Subtype.ext hu) h2
  obtain ⟨Z', h1, h2⟩ := exists_saturation D (LinearMap.range g) (by
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    have e1 : D.EF u.1 v.1 = 0 := hZ.1 u.1.2 _ v.1.2
    have e2 : ∀ (a : 𝓞 E) (z : Z), D.EF (a • (x : D.La)) z = 0 := fun a z => (a • x).2 _ z.2
    have e3 : D.EF (u.2 • (x : D.La)) (v.2 • (x : D.La)) = 0 := by
      have h := hx (H.bar v.2 * u.2)
      rw [← map_smul, hE, Submodule.coe_smul, mul_smul, D.adj, bar_bar] at h
      exact h
    rw [hg, hg]
    simp only [map_add, LinearMap.add_apply]
    rw [e1, e2, e3, ef_swap, e2]
    simp)
  refine ⟨Z', h1, ?_⟩
  rw [h2, ← (LinearEquiv.ofInjective g hinj).finrank_eq]
  have h3 := Submodule.finrank_quotient_add_finrank (LinearMap.ker (LinearMap.snd (𝓞 E) Z (𝓞 E)))
  rw [((LinearMap.snd (𝓞 E) Z (𝓞 E)).quotKerEquivOfSurjective LinearMap.snd_surjective).finrank_eq,
    Module.finrank_self, ← LinearMap.range_inl,
    ← (LinearEquiv.ofInjective _ LinearMap.inl_injective).finrank_eq] at h3
  omega

end GlobalTheory.LowFilt.IsoSat

namespace GlobalTheory.LowFilt

/- English proof (translation)
Introduce `E _ _ _ H D r`. Proceed by induction on `r with`. Consider the case `zero => exact fun _ => ⟨⊥, (isOpp_bot D).isIsoSat, finrank_bot _ _⟩`. Consider the case `succ r ih`. Introduce `hr`.

Take `⟨Z, hZ, rfl⟩` from `ih (by omega)`. Conclude with `IsoSat.exists_succ D Z hZ hr`.
-/
theorem exists_isIsoSat_finrank : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (r : ℕ),
    r ≤ min D.p D.q → ∃ Z : Submodule (𝓞 E) D.La, IsIsoSat D Z ∧ Module.finrank (𝓞 E) Z = r := by
  intro E _ _ _ H D r
  induction r with
  | zero => exact fun _ => ⟨⊥, (isOpp_bot D).isIsoSat, finrank_bot _ _⟩
  | succ r ih =>
    intro hr
    obtain ⟨Z, hZ, rfl⟩ := ih (by omega)
    exact IsoSat.exists_succ D Z hZ hr

end GlobalTheory.LowFilt
