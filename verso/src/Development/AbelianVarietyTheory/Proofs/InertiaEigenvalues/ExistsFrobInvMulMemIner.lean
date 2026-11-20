import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtE
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsD

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.BKGal GlobalTheory.Per

noncomputable section

namespace GlobalTheory.FrobLiftUnr

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hK : FiniteDimensional ℚ_[l] (⊥ : IntermediateField ℚ_[l] (Om l))` using `inferInstance`. Establish `h` using `ReciprocityTheory.DiscreteGroups.LocalClassField.eK_mul_fK l ⊥ hK`. Rewrite `h` using `[IntermediateField.finrank_bot]`. Rewrite using `[ReciprocityTheory.DiscreteGroups.LocalClassField.qK_eq_pow_fK l ⊥ hK, Nat.eq_one_of_mul_eq_one_left h, pow_one]`.
-/
theorem qK_bot : ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (⊥ : IntermediateField ℚ_[l] (Om l)) = l := by
  have hK : FiniteDimensional ℚ_[l] (⊥ : IntermediateField ℚ_[l] (Om l)) := inferInstance
  have h := ReciprocityTheory.DiscreteGroups.LocalClassField.eK_mul_fK l ⊥ hK
  rw [IntermediateField.finrank_bot] at h
  rw [ReciprocityTheory.DiscreteGroups.LocalClassField.qK_eq_pow_fK l ⊥ hK, Nat.eq_one_of_mul_eq_one_left h, pow_one]

/- English proof (translation)
Take `⟨σ, hσ⟩` from `ReciprocityTheory.DiscreteGroups.LocalClassField.exists_isFrob (p := l) (K := (⊥ : IntermediateField ℚ_[l] (Om l))) inferInstance`. Use `⟨σ.restrictScalars ℚ_[l], fun x hx => ?_⟩` and prove the remaining obligations. Establish `h` using `hσ x hx`. Rewrite `h` using `[qK_bot]`. Conclude with `h`.
-/
theorem exists_frob : ∃ Φ : GQ l, ∀ x : Om l, ‖x‖ ≤ 1 → ‖Φ x - x ^ l‖ < 1 := by
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_isFrob (p := l) (K := (⊥ : IntermediateField ℚ_[l] (Om l)))
    inferInstance
  refine ⟨σ.restrictScalars ℚ_[l], fun x hx => ?_⟩
  have h := hσ x hx
  rw [qK_bot] at h
  exact h

/- English proof (translation)
Unfold `GK`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Take `⟨r, rfl⟩` from `IntermediateField.mem_bot.mp hx`. Conclude with `Φ.commutes r`.
-/
theorem mem_GK_qlExt (Φ : GQ l) : Φ ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
  unfold GK
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.mp hx
  exact Φ.commutes r

/- English proof (translation)
Use `(inf_le_right : K0 K' ≤ MaximalUnramifiedExtension l).trans ?_` and prove the remaining obligations. Unfold `MaximalUnramifiedExtension`. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `x ⟨m, -, hm, hx⟩`. Conclude with `ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Kur_of_pow inferInstance hm hx`.
-/
theorem max_unramified_le_unramified_ext (K' : FinExt l) :
    K0 K' ≤ ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension l ((⊥ : IntermediateField ℚ_[l] (Om l))) := by
  refine (inf_le_right : K0 K' ≤ MaximalUnramifiedExtension l).trans ?_
  unfold MaximalUnramifiedExtension
  rw [IntermediateField.adjoin_le_iff]
  rintro x ⟨m, -, hm, hx⟩
  exact ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Kur_of_pow inferInstance hm hx

/- English proof (translation)
Establish `hQ : FiniteDimensional ℚ_[l] ((⊥ : IntermediateField ℚ_[l] (Om l)))` using `inferInstance`. Establish `hK' : FiniteDimensional ℚ_[l] K'.1` using `K'.2`. Establish `hM : FiniteDimensional ℚ_[l] (K0 K')` using `ReciprocityTheory.DiscreteGroups.LocalClassField.finDim_of_le l hK' (inf_le_left : K0 K' ≤ K'.1)`. Take `⟨N, hN, hMN⟩` from `ReciprocityTheory.DiscreteGroups.LocalClassField.exists_le_Kn_of_le_Kur hQ hM (max_unramified_le_unramified_ext K')`. Establish `hbot : (⊥ : IntermediateField ℚ_[l] (Om l)) ≤ K0 K'` using `bot_le`.

Establish `hd` using `ReciprocityTheory.DiscreteGroups.LocalClassField.degLK_pos (p := l) (K := (⊥ : IntermediateField ℚ_[l] (Om l))) hM`. Establish `heq` using `ReciprocityTheory.DiscreteGroups.LocalClassField.eq_Kn_of_norm l ((⊥ : IntermediateField ℚ_[l] (Om l))) hQ hbot hd (ReciprocityTheory.DiscreteGroups.LocalClassField.finrank_eq_degLK_mul hbot hM) (fun x hx => ReciprocityTheory.DiscreteGroups.LocalClassField.norm_Kn l ((⊥ : Interme …`. Use `⟨_, hd, heq.trans ?_⟩` and prove the remaining obligations. Unfold `ReciprocityTheory.DiscreteGroups.LocalClassField.Kn`. Rewrite using `[qK_bot]`.

Conclude with `bot_sup_eq _`.
-/
theorem max_unramified_eq_adjoin_roots (K' : FinExt l) : ∃ d : ℕ, 0 < d ∧
    K0 K' = IntermediateField.adjoin ℚ_[l] {ζ : Om l | ζ ^ (l ^ d - 1) = 1} := by
  have hQ : FiniteDimensional ℚ_[l] ((⊥ : IntermediateField ℚ_[l] (Om l))) := inferInstance
  have hK' : FiniteDimensional ℚ_[l] K'.1 := K'.2
  have hM : FiniteDimensional ℚ_[l] (K0 K') :=
    ReciprocityTheory.DiscreteGroups.LocalClassField.finDim_of_le l hK' (inf_le_left : K0 K' ≤ K'.1)
  obtain ⟨N, hN, hMN⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_le_Kn_of_le_Kur hQ hM (max_unramified_le_unramified_ext K')
  have hbot : (⊥ : IntermediateField ℚ_[l] (Om l)) ≤ K0 K' := bot_le
  have hd := ReciprocityTheory.DiscreteGroups.LocalClassField.degLK_pos (p := l) (K := (⊥ : IntermediateField ℚ_[l] (Om l))) hM
  have heq := ReciprocityTheory.DiscreteGroups.LocalClassField.eq_Kn_of_norm l ((⊥ : IntermediateField ℚ_[l] (Om l))) hQ hbot hd
    (ReciprocityTheory.DiscreteGroups.LocalClassField.finrank_eq_degLK_mul hbot hM)
    (fun x hx => ReciprocityTheory.DiscreteGroups.LocalClassField.norm_Kn l ((⊥ : IntermediateField ℚ_[l] (Om l))) hQ hN (hMN hx))
  refine ⟨_, hd, heq.trans ?_⟩
  unfold ReciprocityTheory.DiscreteGroups.LocalClassField.Kn
  rw [qK_bot]
  exact bot_sup_eq _

/- English proof (translation)
Introduce `h`. Establish `hp : l.Prime` using `Fact.out`. Establish `h1 : l ∣ l ^ d` using `dvd_pow_self l hd.ne'`. Establish `h2 : 1 ≤ l ^ d` using `Nat.one_le_pow _ _ hp.pos`. Establish `h3` using `Nat.dvd_sub h1 h`.

Rewrite `h3` using `[Nat.sub_sub_self h2]`. Conclude with `hp.one_lt.ne' (Nat.dvd_one.mp h3)`.
-/
theorem not_dvd_pow_sub_one {d : ℕ} (hd : 0 < d) : ¬ l ∣ l ^ d - 1 := by
  intro h
  have hp : l.Prime := Fact.out
  have h1 : l ∣ l ^ d := dvd_pow_self l hd.ne'
  have h2 : 1 ≤ l ^ d := Nat.one_le_pow _ _ hp.pos
  have h3 := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self h2] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.mp h3)

/- English proof (translation)
Take `⟨d, hd, hM⟩` from `max_unramified_eq_adjoin_roots K'`. Establish `hm` using `not_dvd_pow_sub_one (l := l) hd`. Establish `hm0 : l ^ d - 1 ≠ 0` using `fun h0 => hm (h0 ▸ dvd_zero l)`. Establish `key : ((Φ.toAlgHom.restrictScalars ℚ_[l]).comp (K0 K').val : ↥(K0 K') →ₐ[ℚ_[l]] Om l) = (K0 K').val.comp σ`. Use `IntermediateField.algHom_ext_of_eq_adjoin ℚ_[l] hM fun ζ hζ => ?_` and prove the remaining obligations.

Use `set z : ↥(K0 K') := ⟨ζ, hM ▸ IntermediateField.subset_adjoin ℚ_[l] _ hζ⟩ with hz`. Express the relevant statement in the definitionally equal form `Φ ζ = ((σ z : ↥(K0 K')) : Om l)`. Establish `hζ' : ζ ^ (l ^ d - 1) = 1` using `hζ`. Establish `hn : ‖ζ‖ = 1` using `ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ'`. Establish `h1 : (Φ ζ) ^ (l ^ d - 1) = 1` using `by rw [← map_pow, hζ', map_one]`.

Establish `hz1 : z ^ (l ^ d - 1) = 1` using `Subtype.ext hζ'`. Establish `h2 : ((σ z : ↥(K0 K')) : Om l) ^ (l ^ d - 1) = 1`. Rewrite using `[← IntermediateField.coe_pow, ← map_pow, hz1, map_one]`. Both sides reduce to the same expression. Assume the negation of the conclusion as `hne`.

Establish `e` using `ReciprocityTheory.DiscreteGroups.LocalClassField.norm_sub_eq_one_of_pow_eq_one l hm h1 h2 hne`. Establish `a1` using `hΦ ζ hn.le`. Establish `a2` using `hσ z hn.le`. Establish `: ‖Φ ζ - ((σ z : ↥(K0 K')) : Om l)‖ < 1`. Establish `eq : Φ ζ - ((σ z : ↥(K0 K')) : Om l) = (Φ ζ - ζ ^ l) + (ζ ^ l - ((σ z : ↥(K0 K')) : Om l))` using `by ring`.

Rewrite using `[eq]`. Use `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt a1 ?_)` and prove the remaining obligations. Rewrite using `[norm_sub_rev]`. Conclude with `a2`. Conclude with `absurd e this.ne`.

Conclude with `congrArg (fun f : ↥(K0 K') →ₐ[ℚ_[l]] Om l => f c) key`.
-/
theorem frobenius_lift_eq_on_maxUnramifiedSubfield (K' : FinExt l) (Φ : GQ l) (hΦ : ∀ x : Om l, ‖x‖ ≤ 1 → ‖Φ x - x ^ l‖ < 1)
    (σ : ↥(K0 K') →ₐ[ℚ_[l]] ↥(K0 K'))
    (hσ : ∀ x : ↥(K0 K'), ‖((x : ↥(K0 K')) : Om l)‖ ≤ 1 →
      ‖((σ x : ↥(K0 K')) : Om l) - ((x : ↥(K0 K')) : Om l) ^ l‖ < 1)
    (c : ↥(K0 K')) : Φ (c : Om l) = ((σ c : ↥(K0 K')) : Om l) := by
  obtain ⟨d, hd, hM⟩ := max_unramified_eq_adjoin_roots K'
  have hm := not_dvd_pow_sub_one (l := l) hd
  have hm0 : l ^ d - 1 ≠ 0 := fun h0 => hm (h0 ▸ dvd_zero l)
  have key : ((Φ.toAlgHom.restrictScalars ℚ_[l]).comp (K0 K').val : ↥(K0 K') →ₐ[ℚ_[l]] Om l) =
      (K0 K').val.comp σ := by
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ_[l] hM fun ζ hζ => ?_
    set z : ↥(K0 K') := ⟨ζ, hM ▸ IntermediateField.subset_adjoin ℚ_[l] _ hζ⟩ with hz
    change Φ ζ = ((σ z : ↥(K0 K')) : Om l)
    have hζ' : ζ ^ (l ^ d - 1) = 1 := hζ
    have hn : ‖ζ‖ = 1 := ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ'
    have h1 : (Φ ζ) ^ (l ^ d - 1) = 1 := by rw [← map_pow, hζ', map_one]
    have hz1 : z ^ (l ^ d - 1) = 1 := Subtype.ext hζ'
    have h2 : ((σ z : ↥(K0 K')) : Om l) ^ (l ^ d - 1) = 1 := by
      rw [← IntermediateField.coe_pow, ← map_pow, hz1, map_one]; rfl
    by_contra hne
    have e := ReciprocityTheory.DiscreteGroups.LocalClassField.norm_sub_eq_one_of_pow_eq_one l hm h1 h2 hne
    have a1 := hΦ ζ hn.le
    have a2 := hσ z hn.le
    have : ‖Φ ζ - ((σ z : ↥(K0 K')) : Om l)‖ < 1 := by
      have eq : Φ ζ - ((σ z : ↥(K0 K')) : Om l) =
          (Φ ζ - ζ ^ l) + (ζ ^ l - ((σ z : ↥(K0 K')) : Om l)) := by ring
      rw [eq]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt a1 ?_)
      rw [norm_sub_rev]; exact a2
    exact absurd e this.ne
  exact congrArg (fun f : ↥(K0 K') →ₐ[ℚ_[l]] Om l => f c) key

end GlobalTheory.FrobLiftUnr

namespace GlobalTheory.FrobLiftUnr

/- English proof (translation)
Introduce `l _ Pl AI _ K' h hN hF hS Fr hFr`. Take `⟨Φ, hΦ⟩` from `exists_frob (l := l)`. Use `⟨⟨Φ, mem_GK_qlExt Φ⟩, fun x _ hx => hΦ x hx, ?_⟩` and prove the remaining obligations. Introduce `c`. Establish `hc` using `hFr c`.

Establish `key` using `frobenius_lift_eq_on_maxUnramifiedSubfield K' Φ hΦ (Pl.PD K').σ (Pl.PD_σ K') c`. Establish `hc' : Pl.actQ Φ (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B ((Pl.PD K').σ c)` using `Pl.actQ_Kur Φ ⟨(c : Om l), (inf_le_right : K0 K' ≤ MaximalUnramifiedExtension l) c.2⟩ ⟨(((Pl.PD K').σ c : ↥(K0 K')) : Om l), (inf_le_right : K0 K' ≤ MaximalUnramifiedExtension l) ((Pl.PD K').σ c).2⟩ key`. Express the relevant statement in the definitionally equal form `(Pl.PD _).actB Fr _ = algebraMap ↥(K0 K') Pl.R.B ((Pl.PD K').σ c) at hc`. Express the relevant statement in the definitionally equal form `(Pl.PD _).actB _ _ = _`. Rewrite `hc`, the goal using `[Pl.PD_actB]`.

Rewrite using `[Subgroup.coe_mul, Subgroup.coe_inv, map_mul, AlgEquiv.mul_apply]`. Express the relevant statement in the definitionally equal form `Pl.actQ Φ⁻¹ (Pl.actQ (Fr : GQ l) _) = _`. Rewrite using `[hc, ← hc', ← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply]`.
-/
theorem exists_frob_inv_mul_mem_iner : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (Fr : Gl l), (pc Pl h hN hF hS).IsFrob Fr → ∃ Φ : Gl l, (∀ x : Om l, x ∈ MaximalUnramifiedExtension l → ‖x‖ ≤ 1 → ‖(Φ : GQ l) x - x ^ l‖ < 1) ∧ Φ⁻¹ * Fr ∈ (pc Pl h hN hF hS).Iner := by
  intro l _ Pl AI _ K' h hN hF hS Fr hFr
  obtain ⟨Φ, hΦ⟩ := exists_frob (l := l)
  refine ⟨⟨Φ, mem_GK_qlExt Φ⟩, fun x _ hx => hΦ x hx, ?_⟩
  intro c
  have hc := hFr c
  have key := frobenius_lift_eq_on_maxUnramifiedSubfield K' Φ hΦ (Pl.PD K').σ (Pl.PD_σ K') c
  have hc' : Pl.actQ Φ (algebraMap ↥(K0 K') Pl.R.B c) =
      algebraMap ↥(K0 K') Pl.R.B ((Pl.PD K').σ c) :=
    Pl.actQ_Kur Φ ⟨(c : Om l), (inf_le_right : K0 K' ≤ MaximalUnramifiedExtension l) c.2⟩
      ⟨(((Pl.PD K').σ c : ↥(K0 K')) : Om l), (inf_le_right : K0 K' ≤ MaximalUnramifiedExtension l) ((Pl.PD K').σ c).2⟩ key
  change (Pl.PD _).actB Fr _ = algebraMap ↥(K0 K') Pl.R.B ((Pl.PD K').σ c) at hc
  change (Pl.PD _).actB _ _ = _
  rw [Pl.PD_actB] at hc ⊢
  rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, AlgEquiv.mul_apply]
  change Pl.actQ Φ⁻¹ (Pl.actQ (Fr : GQ l) _) = _
  rw [hc, ← hc', ← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply]

end GlobalTheory.FrobLiftUnr
