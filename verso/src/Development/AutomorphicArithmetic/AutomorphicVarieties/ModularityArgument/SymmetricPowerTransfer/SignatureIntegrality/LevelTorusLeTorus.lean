import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.UnitaryDoubleCosetIndicator

noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Z.Sym.Sig

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem val_ord (x : kˣ) : valuation k (x : k) = uniformizer k ^ ord k x := by
  have h := GlAx.val_div_ord x
  rw [Units.val_div_eq_div_val, map_div₀, GlAx.val_zpow] at h
  exact (div_eq_one_iff_eq (zpow_pos GlAx.unif_pos _).ne').1 h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_Uc {c : ℕ} {u : kˣ} : u ∈ Uc k c ↔ valuation k (u : k) = 1 ∧ valuation k ((u : k) - 1) ≤ uniformizer k ^ (c : ℤ) := by
  constructor
  · intro h
    refine ⟨Uc_le_Uo k c h, ?_⟩
    obtain ⟨v, hv, rfl⟩ := h
    have h1 : Ideal.Quotient.mk _ (v : 𝒪[k]) = 1 := congrArg Units.val hv
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq, GlAx.mem_pow] at h1
    exact h1
  · rintro ⟨h1, h2⟩
    obtain ⟨v, hv⟩ := (Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers (valuation k))
      (x := (⟨u, h1.le⟩ : 𝒪[k]))).2 h1
    refine ⟨v, Units.ext ?_, Units.ext (congrArg Subtype.val hv)⟩
    change Ideal.Quotient.mk _ (v : 𝒪[k]) = Ideal.Quotient.mk _ 1
    rw [Ideal.Quotient.eq, GlAx.mem_pow, hv]
    exact h2

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem mem_Kc_of {c : ℕ} {g : GL (Fin n) k} (h : g ∈ KO k (Fin n)) (h' : GlAx.Bd c g) : g ∈ Kc k n c := by
  obtain ⟨y, rfl⟩ := h
  exact ⟨y, (GlAx.map_eq_one c y).2 h', rfl⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem Kc_conj {c : ℕ} {g x : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) (hx : x ∈ Kc k n c) : g * x * g⁻¹ ∈ Kc k n c := by
  obtain ⟨y, rfl⟩ := hg
  obtain ⟨z, hz, rfl⟩ := hx
  exact ⟨y * z * y⁻¹, (MonoidHom.normal_ker _).conj_mem z hz y, by simp⟩

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem dg_mem_KO {s : Fin n → kˣ} (h : ∀ i, s i ∈ Uo k) : dg s ∈ KO k (Fin n) := by
  have H : ∀ s : Fin n → kˣ, (∀ i, s i ∈ Uo k) → GlAx.Bd 0 (dg s) := fun s h => GlAx.bd_zero.2 fun i j => by
    rw [dg, val_diagT, diagonal_apply]
    split_ifs
    exacts [(show valuation k (s i : k) = 1 from h i).le, zero_mem _]
  exact GlAx.mem_KO.2 ⟨H s h, by rw [dg, ← map_inv]; exact H _ fun i => inv_mem (h i)⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem dg_mem_Kc {c : ℕ} {s : Fin n → kˣ} : dg s ∈ Kc k n c ↔ ∀ i, s i ∈ Uc k c := by
  constructor
  · intro h i
    have a := (GlAx.mem_Kc.1 h).1 i i
    have b := GlAx.bd_zero.1 (GlAx.mem_KO.1 (GlAx.Kc_le c h)).1 i i
    have b' := GlAx.bd_zero.1 (GlAx.mem_KO.1 (GlAx.Kc_le c h)).2 i i
    rw [dg, ← map_inv] at b'
    simp only [dg, Matrix.sub_apply, val_diagT, diagonal_apply_eq, one_apply_eq] at a b b'
    refine mem_Uc.2 ⟨le_antisymm b ?_, a⟩
    have b2 : valuation k ((s i : k)⁻¹) ≤ 1 := by rw [← Units.val_inv_eq_inv_val]; exact b'
    rw [map_inv₀] at b2
    exact (inv_le_one₀ (zero_lt_iff.2 (by simp))).1 b2
  · intro h
    refine mem_Kc_of (dg_mem_KO fun i => Uc_le_Uo k c (h i)) fun i j => ?_
    rw [dg, Matrix.sub_apply, val_diagT, diagonal_apply, one_apply]
    split_ifs
    exacts [(mem_Uc.1 (h i)).2, by simp]

namespace Lev

variable (V : Lev k)

/- English proof (translation)
Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem levelTorus_le_torus : V.TH n ≤ (glIwa k n).T := by
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨s, fun i => V.H_le (hs i trivial), rfl⟩

/- English proof (translation)
Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem Tc_le_TH : (glIwa k n).Tc V.c ≤ V.TH n := by
  rintro _ ⟨⟨s, -, rfl⟩, h⟩
  exact ⟨s, fun i _ => V.le (dg_mem_Kc.1 h i), rfl⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem N_le : (glIwa k n).N ≤ V.J n := le_sup_left.trans le_sup_left

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TH_le : V.TH n ≤ V.J n := le_sup_right.trans le_sup_left

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Nm_le : (glIwa k n).Nm V.c ≤ V.J n := le_sup_right

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dg_mem {s : Fin n → kˣ} (h : ∀ i, s i ∈ V.H) : dg s ∈ V.J n := V.TH_le ⟨s, fun i _ => h i, rfl⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem J_le_KO : V.J n ≤ KO k (Fin n) := by
  refine sup_le (sup_le (fun _ h => h.2) ?_) fun _ h => GlAx.Kc_le _ h.2
  rintro _ ⟨s, hs, rfl⟩
  exact dg_mem_KO fun i => V.H_le (hs i trivial)

end Lev

end UpperTheory.V.Z.Sym.Sig

end
