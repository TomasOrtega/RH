import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevG
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.DeterminantTwistRowActionMem

open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.G.Model Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf) (hp : (p : Kf) ≠ 0)

/- English proof (translation)
Use `jd_natAct_mul P A⁻¹ A` as an intermediate fact. Establish `h2 : (fun v => (A⁻¹) v * A v) = (fun _ => (1 : GL (Fin (P.m + 1)) _))`. Use function extensionality and compare the values at `v`. Rewrite using `[Pi.inv_apply, inv_mul_cancel]`. Rewrite `this` using `[h2, jd_natAct_one]`.

Conclude with `(LinearMap.congr_fun this x).symm`.
-/
theorem natAct_inv_self (A : ∀ v, GL (Fin (P.m + 1)) (P.Qq v)) (x : P.Xsp) : P.natAct A⁻¹ (P.natAct A x) = x := by
  have := jd_natAct_mul P A⁻¹ A
  have h2 : (fun v => (A⁻¹) v * A v) = (fun _ => (1 : GL (Fin (P.m + 1)) _)) := by
    funext v; rw [Pi.inv_apply, inv_mul_cancel]
  rw [h2, jd_natAct_one] at this
  exact (LinearMap.congr_fun this x).symm

/- English proof (translation)
Use `natAct_inv_self P A⁻¹ x` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis.
-/
theorem natAct_self_inv (A : ∀ v, GL (Fin (P.m + 1)) (P.Qq v)) (x : P.Xsp) : P.natAct A (P.natAct A⁻¹ x) = x := by
  have := natAct_inv_self P A⁻¹ x
  rwa [inv_inv] at this

include hp in

def Γsub : Subgroup ((∀ v, GL (Fin (P.m + 1)) (P.Qq v)) × Oˣ) where
  carrier := {γ | ∃ z : ℤ, P.natAct γ.1 (EV P) = ((p : Kf) ^ z * algebraMap O Kf ((γ.2⁻¹ : Oˣ) : O)) • EV P}
  mul_mem' := by
    rintro ⟨A, u⟩ ⟨B, w⟩ ⟨z, hz⟩ ⟨z', hz'⟩
    refine ⟨z + z', ?_⟩
    show P.natAct (fun v => A v * B v) (EV P) = _
    rw [jd_natAct_mul, LinearMap.comp_apply]
    simp only at hz hz'
    rw [hz', LinearMap.map_smul, hz, smul_smul]
    congr 1
    simp only [Prod.snd_mul, mul_inv_rev, Units.val_mul, map_mul, zpow_add₀ hp]
    ring
  one_mem' := ⟨0, by
    show P.natAct (fun _ => 1) (EV P) = _
    rw [jd_natAct_one]; simp⟩
  inv_mem' := by
    rintro ⟨A, u⟩ ⟨z, hz⟩
    simp only at hz
    refine ⟨-z, ?_⟩
    have hu : algebraMap O Kf ((u⁻¹ : Oˣ) : O) * algebraMap O Kf (u : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hc : (p : Kf) ^ z * algebraMap O Kf ((u⁻¹ : Oˣ) : O) ≠ 0 := by
      refine mul_ne_zero (zpow_ne_zero _ hp) fun h => ?_
      rw [h, zero_mul] at hu; exact zero_ne_one hu
    show P.natAct A⁻¹ (EV P) = _
    have h1 : EV P = P.natAct A (((p : Kf) ^ z * algebraMap O Kf ((u⁻¹ : Oˣ) : O))⁻¹ • EV P) := by
      rw [LinearMap.map_smul, hz, smul_smul, inv_mul_cancel₀ hc, one_smul]
    conv_lhs => rw [h1, natAct_inv_self]
    congr 1
    simp only [Prod.snd_inv, inv_inv, zpow_neg]
    rw [mul_inv, inv_eq_of_mul_eq_one_right hu]

include hp in

def levB : Level P where
  Γ := Γsub P hp
  act v := (Pi.evalMonoidHom (fun v => GL (Fin (P.m + 1)) (P.Qq v)) v).comp ((MonoidHom.fst _ _).comp (Γsub P hp).subtype)
  χ := (MonoidHom.snd _ _).comp (Γsub P hp).subtype

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem levB_actX (γ : ↥(Γsub P hp)) : (levB P hp).actX γ = P.natAct γ.1.1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem levB_chi (γ : ↥(Γsub P hp)) : ((levB P hp).χ γ : O) = (γ.1.2 : O) := rfl

/- English proof (translation)
Take `⟨z, hz⟩` from `γ.2`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[levB_actX, hz, levB_chi, ← algebraMap_smul Kf, smul_smul]`. Use `congr 1`. Rewrite using `[mul_comm, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one]`.
-/
theorem levB_EV (γ : ↥(Γsub P hp)) : ∃ z : ℤ, ((levB P hp).χ γ : O) • (levB P hp).actX γ (EV P) = (p : Kf) ^ z • EV P := by
  obtain ⟨z, hz⟩ := γ.2
  refine ⟨z, ?_⟩
  rw [levB_actX, hz, levB_chi, ← algebraMap_smul Kf, smul_smul]
  congr 1
  rw [mul_comm, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one]

def gatU : GAtP p where
  O := O
  Kf := Kf
  P := P
  comp := Unit
  lev := fun _ => levB P hp
  e := 0

abbrev standardTuple : P.Tup := L0 P

/- English proof (translation)
Introduce `v` and use `⟨1, by simp, rfl⟩`.
-/
theorem standardTuple_isLattice : P.IsLatTup (standardTuple P) := fun v => ⟨1, by simp, rfl⟩

/- English proof (translation)
Establish `hmem : ∀ g : (levB P hp).Γ, (levB P hp).smul g (standardTuple P) = standardTuple P → ∃ z : ℤ, ((levB P hp).χ g : O) • (levB P hp).actX g (EV P) = (p : Kf) ^ z • EV P ∧ (p : Kf) ^ z ∈ (algebraMap O Kf).range`. Introduce `g hg`. Take `⟨z, hz⟩` from `levB_EV P hp g`. Use `⟨z, hz, ?_⟩` and prove the remaining obligations. Establish `h1` using `Formalism.L2.G.Cmp.equivSys_HtupW (gatU P hp) () g (standardTuple P) (standardTuple_isLattice P) (EV P) (EV_mem P)`.

Establish `h1' : ((levB P hp).χ g : O) • (levB P hp).actX g (EV P) ∈ P.HtupW (standardTuple P)`. Establish `: (gatU P hp).P.HtupW ((gatU P hp).lev () |>.smul g (standardTuple P)) = P.HtupW (standardTuple P)` using `by show P.HtupW ((levB P hp).smul g (standardTuple P)) = _`. Rewrite using `[hg]`. Rewrite using `[← this]`. Conclude with `h1`.

Rewrite `h1'` using `[hz]`. Establish `h2` using `eval_int P _ (htupW_int P _ h1')`. Rewrite `h2` using `[smul_eval, eval_EV, mul_one]`. Then use the resulting hypothesis. Take `⟨z, hz, ha⟩` from `hmem γ hγ`. Establish `hγ' : (levB P hp).smul γ⁻¹ (standardTuple P) = L0 P` using `by conv_lhs => rw [← hγ, ← jd_smul_mul, inv_mul_cancel, jd_smul_one]`.

Take `⟨z', hz', hb⟩` from `hmem γ⁻¹ hγ'`. Establish `e1 : ((levB P hp).χ γ⁻¹ : O) • (levB P hp).actX γ⁻¹ (((levB P hp).χ γ : O) • (levB P hp).actX γ (EV P)) = EV P`. Rewrite using `[LinearMap.map_smul_of_tower, smul_comm, ← LinearMap.comp_apply, ← jd_actX_mul, inv_mul_cancel, jd_actX_one, LinearMap.id_apply, smul_smul, ← Units.val_mul, ← map_mul]`. Simplify using the standard rewrite rules. Rewrite `e1` using `[hz, LinearMap.map_smul_of_tower, smul_comm, hz', smul_smul]`.

Establish `e2` using `congrArg (eval (idPt P)) e1`. Rewrite `e2` using `[smul_eval, eval_EV, mul_one]`. Take `⟨a, ha⟩` from `ha`. Take `⟨b, hb⟩` from `hb`. Establish `hpn : ¬ IsUnit (p : (gatU P hp).O)` using `ja_p_nonunit (gatU P hp) v0`.

Use `haveI := (P.setting v0).frac_O`. Establish `hab : a * b = 1` using `IsFractionRing.injective O Kf (by rw [map_mul, ha, hb, e2, map_one])`. Establish `hzero : z = 0`. Assume the negation of the conclusion as `hne`. Break down `lt_or_gt_of_ne hne with hlt | hgt` into its components or cases.

Take `⟨n, hn'⟩ : ∃ n : ℕ, -z = (n : ℤ) + 1` from `⟨(-z - 1).toNat, by omega⟩`. Establish `h3 : (p : Kf) ^ z' = (p : Kf) ^ ((n : ℤ) + 1)`. Rewrite using `[← hn', zpow_neg]`. Conclude with `eq_inv_of_mul_eq_one_right e2`. Rewrite `h3` using `[zpow_add_one₀ hp, zpow_natCast, ← pow_succ]`.

Establish `hb' : b = (p : O) ^ (n + 1)` using `IsFractionRing.injective O Kf (by rw [hb, h3, map_pow, map_natCast])`. Establish `hub : IsUnit b` using `IsUnit.of_mul_eq_one a (by rw [mul_comm]; exact hab)`. Rewrite `hub` using `[hb']`. Conclude with `hpn ((isUnit_pow_iff (by omega)).mp hub)`. Take `⟨n, hn'⟩ : ∃ n : ℕ, z = (n : ℤ) + 1` from `⟨(z - 1).toNat, by omega⟩`.

Establish `h3 : (p : Kf) ^ z = (p : Kf) ^ (n + 1)` using `by rw [hn', zpow_add_one₀ hp, zpow_natCast, ← pow_succ]`. Establish `ha' : a = (p : O) ^ (n + 1)` using `IsFractionRing.injective O Kf (by rw [ha, h3, map_pow, map_natCast])`. Establish `hua : IsUnit a` using `IsUnit.of_mul_eq_one b hab`. Rewrite `hua` using `[ha']`. Conclude with `hpn ((isUnit_pow_iff (by omega)).mp hua)`.

Rewrite using `[hz, hzero, zpow_zero, one_smul]`.
-/
theorem stab_EV (v0 : Fin P.nV) (γ : (levB P hp).Γ) (hγ : (levB P hp).smul γ (standardTuple P) = standardTuple P) :
    ((levB P hp).χ γ : O) • (levB P hp).actX γ (EV P) = EV P := by
  have hmem : ∀ g : (levB P hp).Γ, (levB P hp).smul g (standardTuple P) = standardTuple P →
      ∃ z : ℤ, ((levB P hp).χ g : O) • (levB P hp).actX g (EV P) = (p : Kf) ^ z • EV P ∧
        (p : Kf) ^ z ∈ (algebraMap O Kf).range := by
    intro g hg
    obtain ⟨z, hz⟩ := levB_EV P hp g
    refine ⟨z, hz, ?_⟩
    have h1 := Formalism.L2.G.Cmp.equivSys_HtupW (gatU P hp) () g (standardTuple P) (standardTuple_isLattice P) (EV P) (EV_mem P)
    have h1' : ((levB P hp).χ g : O) • (levB P hp).actX g (EV P) ∈ P.HtupW (standardTuple P) := by
      have : (gatU P hp).P.HtupW ((gatU P hp).lev () |>.smul g (standardTuple P)) = P.HtupW (standardTuple P) := by
        show P.HtupW ((levB P hp).smul g (standardTuple P)) = _
        rw [hg]
      rw [← this]; exact h1
    rw [hz] at h1'
    have h2 := eval_int P _ (htupW_int P _ h1')
    rwa [smul_eval, eval_EV, mul_one] at h2
  obtain ⟨z, hz, ha⟩ := hmem γ hγ
  have hγ' : (levB P hp).smul γ⁻¹ (standardTuple P) = L0 P := by
    conv_lhs => rw [← hγ, ← jd_smul_mul, inv_mul_cancel, jd_smul_one]
  obtain ⟨z', hz', hb⟩ := hmem γ⁻¹ hγ'
  have e1 : ((levB P hp).χ γ⁻¹ : O) • (levB P hp).actX γ⁻¹ (((levB P hp).χ γ : O) • (levB P hp).actX γ (EV P)) =
      EV P := by
    rw [LinearMap.map_smul_of_tower, smul_comm, ← LinearMap.comp_apply, ← jd_actX_mul, inv_mul_cancel, jd_actX_one,
      LinearMap.id_apply, smul_smul, ← Units.val_mul, ← map_mul]
    simp
  rw [hz, LinearMap.map_smul_of_tower, smul_comm, hz', smul_smul] at e1
  have e2 := congrArg (eval (idPt P)) e1
  rw [smul_eval, eval_EV, mul_one] at e2
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  have hpn : ¬ IsUnit (p : (gatU P hp).O) := ja_p_nonunit (gatU P hp) v0
  haveI := (P.setting v0).frac_O
  have hab : a * b = 1 := IsFractionRing.injective O Kf (by rw [map_mul, ha, hb, e2, map_one])
  have hzero : z = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨n, hn'⟩ : ∃ n : ℕ, -z = (n : ℤ) + 1 := ⟨(-z - 1).toNat, by omega⟩
      have h3 : (p : Kf) ^ z' = (p : Kf) ^ ((n : ℤ) + 1) := by
        rw [← hn', zpow_neg]; exact eq_inv_of_mul_eq_one_right e2
      rw [zpow_add_one₀ hp, zpow_natCast, ← pow_succ] at h3
      have hb' : b = (p : O) ^ (n + 1) := IsFractionRing.injective O Kf (by rw [hb, h3, map_pow, map_natCast])
      have hub : IsUnit b := IsUnit.of_mul_eq_one a (by rw [mul_comm]; exact hab)
      rw [hb'] at hub
      exact hpn ((isUnit_pow_iff (by omega)).mp hub)
    · obtain ⟨n, hn'⟩ : ∃ n : ℕ, z = (n : ℤ) + 1 := ⟨(z - 1).toNat, by omega⟩
      have h3 : (p : Kf) ^ z = (p : Kf) ^ (n + 1) := by rw [hn', zpow_add_one₀ hp, zpow_natCast, ← pow_succ]
      have ha' : a = (p : O) ^ (n + 1) := IsFractionRing.injective O Kf (by rw [ha, h3, map_pow, map_natCast])
      have hua : IsUnit a := IsUnit.of_mul_eq_one b hab
      rw [ha'] at hua
      exact hpn ((isUnit_pow_iff (by omega)).mp hua)
  rw [hz, hzero, zpow_zero, one_smul]

end Formalism.BasicNotions.Examples₂.NZ
