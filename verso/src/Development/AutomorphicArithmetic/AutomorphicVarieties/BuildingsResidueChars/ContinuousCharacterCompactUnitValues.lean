import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilGroupDenseInGaloisGroup

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.Pst.DpstMap GlobalTheory.GalOfCusp

/- English proof (translation)
Take `⟨C, hC⟩` from `(isCompact_range hψ.norm).bddAbove`. Assume the negation of the conclusion as `hlt`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt C (not_le.1 hlt)`. Use `hC ⟨s ^ n, rfl⟩` as an intermediate fact. Simplify using `only [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this`.

Conclude with `absurd hn (not_lt.2 this)`.
-/
private theorem norm_le_one {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField K]
    (ψ : Γ →* Kˣ) (hψ : Continuous fun s => (ψ s : K)) (s : Γ) : ‖(ψ s : K)‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := (isCompact_range hψ.norm).bddAbove
  by_contra hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (not_le.1 hlt)
  have := hC ⟨s ^ n, rfl⟩
  simp only [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
  exact absurd hn (not_lt.2 this)

/- English proof (translation)
Use `le_antisymm (norm_le_one ψ hψ s) ?_` and prove the remaining obligations. Establish `h` using `norm_le_one ψ hψ s⁻¹`. Rewrite `h` using `[map_inv, Units.val_inv_eq_inv_val, norm_inv]`. Conclude with `(inv_le_one₀ (norm_pos_iff.2 (ψ s).ne_zero)).1 h`.
-/
private theorem norm_eq_one {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField K]
    (ψ : Γ →* Kˣ) (hψ : Continuous fun s => (ψ s : K)) (s : Γ) : ‖(ψ s : K)‖ = 1 := by
  refine le_antisymm (norm_le_one ψ hψ s) ?_
  have h := norm_le_one ψ hψ s⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h
  exact (inv_le_one₀ (norm_pos_iff.2 (ψ s).ne_zero)).1 h

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l hl ι w A h hw ψ a hψ hσ`. Use `haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact`. Establish `hq1 : 1 < normV w` using `GlobalTheory.WeilDeligne.one_lt_normV w`. Establish `hpow` using `normV_eq_pow (l := l) hw`. Establish `hf : resDeg l w ≠ 0`.

Introduce `h0`. Rewrite `hq1` using `[hpow, h0, pow_zero]`. Conclude with `lt_irrefl _ hq1`. Establish `hl1 : ‖(l : Qbar l)‖ < 1`. Rewrite using `[← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]`.

Conclude with `Padic.norm_p_lt_one`. Establish `hlt : ‖((normV w : ℕ) : Qbar l)‖ < 1`. Rewrite using `[hpow, Nat.cast_pow, norm_pow]`. Conclude with `pow_lt_one₀ (norm_nonneg _) hl1 hf`. Establish `hpos : 0 < ‖((normV w : ℕ) : Qbar l)‖` using `norm_pos_iff.2 (Nat.cast_ne_zero.2 (by omega))`.

Establish `ha : a = 0`. Establish `h1` using `hσ (frob h)`. Rewrite `h1` using `[deg_frob, mul_one, ← map_natCast ι, ← map_zpow₀]`. Establish `h2` using `norm_eq_one ψ hψ (Subgroup.inclusion (Weil_le_Dec h) (frob h))`. Rewrite `h2` using `[ι.injective h1, norm_zpow]`.

Conclude with `(zpow_eq_one_iff_right₀ hpos.le hlt.ne).1 h2`. Use `⟨ha, ?_⟩` and prove the remaining obligations. Establish `hd` using `UpperTheory.weil_group_dense_in_galois_group F Ω w A h`. Establish `he : (fun s => (ψ s : Qbar l)) = fun _ => 1`. Use `hd.equalizer hψ continuous_const (funext fun σ => ?_)` and prove the remaining obligations.

Establish `h1` using `hσ σ`. Rewrite `h1` using `[ha, zero_mul, zpow_zero, ← map_one ι]`. Conclude with `ι.injective h1`. Use extensionality with `s`. Simplify using `using congrFun he s`.
-/
theorem UpperTheory.continuous_character_compact_unit_values :
    UpperTheory.V.Af.Wd.CharEnd := by
  intro F Ω _ _ _ _ _ l hl ι w A h hw ψ a hψ hσ
  haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  have hq1 : 1 < normV w := GlobalTheory.WeilDeligne.one_lt_normV w
  have hpow := normV_eq_pow (l := l) hw
  have hf : resDeg l w ≠ 0 := by
    intro h0
    rw [hpow, h0, pow_zero] at hq1
    exact lt_irrefl _ hq1
  have hl1 : ‖(l : Qbar l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have hlt : ‖((normV w : ℕ) : Qbar l)‖ < 1 := by
    rw [hpow, Nat.cast_pow, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hl1 hf
  have hpos : 0 < ‖((normV w : ℕ) : Qbar l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (by omega))
  have ha : a = 0 := by
    have h1 := hσ (frob h)
    rw [deg_frob, mul_one, ← map_natCast ι, ← map_zpow₀] at h1
    have h2 := norm_eq_one ψ hψ (Subgroup.inclusion (Weil_le_Dec h) (frob h))
    rw [ι.injective h1, norm_zpow] at h2
    exact (zpow_eq_one_iff_right₀ hpos.le hlt.ne).1 h2
  refine ⟨ha, ?_⟩
  have hd := UpperTheory.weil_group_dense_in_galois_group F Ω w A h
  have he : (fun s => (ψ s : Qbar l)) = fun _ => 1 := by
    refine hd.equalizer hψ continuous_const (funext fun σ => ?_)
    have h1 := hσ σ
    rw [ha, zero_mul, zpow_zero, ← map_one ι] at h1
    exact ι.injective h1
  ext s
  simpa using congrFun he s
