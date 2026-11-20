import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.XdualExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RestrMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.LiftEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ActFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.HomKill
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.FixLev
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ContinuousToTorsionBounded

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ l _ D e N _ ρ hρ a ha hac x hx`. Take `⟨r, hr⟩` from `(Z1_H1_qz_twist_l_power_torsion E Ω l D (e : ℤ)).2 x`. Establish `hφ : resInf D (e : ℤ) x ∈ XDual l (cycU l (⊤ : Subgroup (G E Ω))) ℤ_[l] (QZ l)` using `(Submodule.mem_inf.1 (resInfMem E Ω l D (e : ℤ) ⟨x, hx, rfl⟩)).1`. Establish `hcl : IsClosed ((⊤ : Subgroup (G E Ω)) : Set (G E Ω))`. Rewrite using `[Subgroup.coe_top]`.

Conclude with `isClosed_univ`. Take `⟨n, ψ, hψ, hres⟩` from `xdualExt E Ω l l ⊤ ℤ_[l] (QZ l) (Fact.out : l.Prime).ne_zero hcl _ hφ`. Use `⟨max n r + 2, fun m hm M _ h hM u hu => ?_⟩` and prove the remaining obligations. Establish `key : ∀ b : (ZMod M)ˣ, (actRep D (↑e) ρ).asAlgebraHom (((MonoidAlgebra.lift ℤ (MonoidAlgebra ℤ_[l] (Gq ρ)) (Gq ρ)) (MonoidAlgebra.of ℤ_[l] (Gq ρ))).toRingHom (MonoidAlgebra.single (((piQ ρ)⁻¹.comp (ZMod.unitsMap h)) b)⁻¹ (↑(↑b : ZMod M).val ^ e * Eone M a ↑b))) = (((↑(↑b : ZMod M …`. Introduce `b`.

Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidHom.comp_apply, MonoidHom.inv_apply, inv_inv, MonoidAlgebra.of_apply, MonoidAlgebra.smul_single, map_zsmul]`. Rewrite using `[Representation.asAlgebraHom_single, zsmul_eq_mul, mul_one]`. Both sides reduce to the same expression. Simplify using `only [ytEl, sumEl, map_neg, map_sum, coefMap, key]`. Rewrite using `[LinearMap.neg_apply, map_neg, Pi.neg_apply, neg_eq_zero, LinearMap.sum_apply, map_sum, Finset.sum_apply]`.

Simplify using `only [LinearMap.smul_apply, map_smul, Pi.smul_apply]`. Establish `hm2 : 2 ≤ m` using `le_trans (Nat.le_add_left 2 _) hm`. Establish `hnm : n ≤ m` using `le_trans (le_trans (le_max_left n r) (Nat.le_add_right _ 2)) hm`. Establish `hrm : r ≤ m` using `le_trans (le_trans (le_max_right n r) (Nat.le_add_right _ 2)) hm`. Use `choose σ hσ using (liftEx E Ω M).1`.

Establish `hcycM : IsCycAct Ω M (ρ.comp (ZMod.unitsMap h))` using `(actFacts E Ω N ρ hρ).2.2.2.2 M h`. Establish `hlift : ∀ b : (ZMod M)ˣ, IsLift (ρ (ZMod.unitsMap h b)).toRingEquiv (σ b)` using `fun b => hcycM b (σ b) (hσ b)`. Establish `hfixM : u.1 ∈ fixMu E Ω M`. Rewrite using `[hM]`. Conclude with `(fixLev E Ω l N m).2.1 (Subgroup.mem_inf.2 ⟨u.2, hu⟩)`.

Set `w : (ZMod M)ˣ → G E Ω` to `fun b => AlgEquiv.ofRingEquiv (f := ((σ b).trans (u.1 : Ω ≃ₐ[E] Ω).toRingEquiv).trans (σ b).symm) (by`. Introduce `y`. Establish `h1` using `hlift b y`. Simplify using `only [RingEquiv.trans_apply, AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv]`. Rewrite using `[h1, AlgEquiv.commutes, ← h1, RingEquiv.symm_apply_apply])`.

Establish `hw : ∀ b y, w b y = (σ b).symm (u.1 (σ b y))` using `fun _ _ => rfl`. Establish `wInf : ∀ b, w b ∈ Uinf E Ω l`. Introduce `b`. Establish `hu1 : cycZ E Ω l u.1 = 1` using `(Subgroup.mem_inf.1 u.2).2`. Use `Subgroup.mem_inf.2 ⟨Subgroup.mem_top _, ?_⟩` and prove the remaining obligations.

Use `show cycZ E Ω l (w b) = 1`. Establish `hra : MulSemiringAction.toRingAut (G E Ω) Ω (w b) = (σ b)⁻¹ * MulSemiringAction.toRingAut (G E Ω) Ω u.1 * σ b`. Use extensionality with `y`. Both sides reduce to the same expression. Establish `hcz : ∀ g : G E Ω, cycZ E Ω l g = cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G E Ω) Ω g)` using `fun _ => rfl`.

Rewrite using `[hcz, hra, map_mul, map_mul, map_inv, ← hcz, hu1, mul_one, inv_mul_cancel]`. Establish `wFix : ∀ b, w b ∈ fixMu E Ω M`. Introduce `b y hy`. Establish `hy' : (σ b y) ^ M = 1` using `by rw [← map_pow, hy, map_one]`. Rewrite using `[hw, hfixM _ hy', RingEquiv.symm_apply_apply]`.

Establish `hconj : ∀ b, resInf D (e : ℤ) (galoisActionOnCohomology D (e : ℤ) (ρ (ZMod.unitsMap h b)).toRingEquiv x) u = twScal l (σ b) (e : ℤ) • resInf D (e : ℤ) x ⟨w b, wInf b⟩` using `fun b => resInfConj E Ω l D (e : ℤ) _ (σ b) (hlift b) x ⟨w b, wInf b⟩ u (fun y => by show u.1 (σ b y) = σ b (w b y)`. Rewrite using `[hw, RingEquiv.apply_symm_apply])`. Establish `hle : fixMu E Ω M ≤ levU l ⊤ n`. Introduce `g hg`. Use `show g ∈ Un E Ω l n`.

Rewrite using `[← (fixLev E Ω l N n).1]`. Introduce `y hy`. Apply `hg` to reduce the goal to its premises. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : l ^ n ∣ M := by`. Rewrite using `[hM]`.

Conclude with `dvd_mul_of_dvd_right (pow_dvd_pow l hnm) N`. Rewrite using `[hk, pow_mul, hy, one_pow]`. Establish `hφ' : restr ℤ_[l] (QZ l) hle ψ ∈ XDual l (fixMu E Ω M) ℤ_[l] (QZ l)` using `(restrMem E Ω l (fixMu E Ω M) (levU l ⊤ n) hle ℤ_[l] (QZ l) (qzG E Ω l (e : ℤ))).1 ⟨ψ, hψ, rfl⟩`. Establish `h2M : 2 < M`. Establish `hl2 : 2 ≤ l` using `(Fact.out : l.Prime).two_le`.

Establish `h4 : 4 ≤ l ^ 2` using `by nlinarith [pow_two l]`. Establish `h4m : 4 ≤ l ^ m` using `le_trans h4 (Nat.pow_le_pow_right (by omega) hm2)`. Establish `hN : 1 ≤ N` using `NeZero.one_le`. Rewrite using `[hM]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hacM : a.Coprime M`. Rewrite using `[hM]`. Conclude with `Nat.Coprime.mul_right hac.coprime_mul_right_right (Nat.Coprime.pow_right m hac.coprime_mul_left_right)`. Establish `hK` using `homKill E Ω M (ρ.comp (ZMod.unitsMap h)) hcycM h2M a ha hacM ℤ_[l] (QZ l) l _ hφ' σ hσ ⟨u.1, hfixM⟩ (fun b => ⟨w b, wFix b⟩) (fun b y => by show u.1 (σ b y) = σ b (w b y)`. Rewrite using `[hw, RingEquiv.apply_symm_apply])`.

Establish `hv : ∀ g, (l : ℤ_[l]) ^ m • resInf D (e : ℤ) x g = 0`. Introduce `g`. Establish `h0 : (l : ℤ_[l]) ^ r • resInf D (e : ℤ) x = 0` using `by rw [← map_smul, hr, map_zero]`. Rewrite using `[← Nat.sub_add_cancel hrm, pow_add, mul_smul]`. Establish `h1` using `congrFun h0 g`.

Simplify using `only [Pi.smul_apply, Pi.zero_apply] at h1`. Rewrite using `[h1, smul_zero]`. Establish `alg : ∀ (c E1 : ℤ) (B : ℤ_[l]) (X : ℤ_[l]ˣ) (v : QZ l), (c : ℤ_[l]) = B ^ e * (E1 : ℤ_[l]) → (l : ℤ_[l]) ^ m ∣ (X : ℤ_[l]) - B → (l : ℤ_[l]) ^ m • v = 0 → (c : ℤ_[l]) • (((X ^ (-(e : ℤ)) : ℤ_[l]ˣ) : ℤ_[l]) • v) = E1 • v`. Introduce `c E1 B X v hc hX hv0`. Take `⟨t, ht⟩ : (l : ℤ_[l]) ^ m ∣ B ^ e - (X : ℤ_[l]) ^ e` from `dvd_trans (dvd_sub_comm.1 hX) (sub_dvd_pow_sub_pow _ _ _)`.

Establish `hX' : ((X ^ (-(e : ℤ)) : ℤ_[l]ˣ) : ℤ_[l]) * (X : ℤ_[l]) ^ e = 1`. Rewrite using `[zpow_neg, zpow_natCast, ← Units.val_pow_eq_pow_val, Units.inv_mul]`. Establish `hB : B ^ e = (X : ℤ_[l]) ^ e + (l : ℤ_[l]) ^ m * t` using `by rw [← ht]; ring`. Establish `h3 : B ^ e * (E1 : ℤ_[l]) * ((X ^ (-(e : ℤ)) : ℤ_[l]ˣ) : ℤ_[l]) = (E1 : ℤ_[l]) + ((E1 : ℤ_[l]) * t * ((X ^ (-(e : ℤ)) : ℤ_[l]ˣ) : ℤ_[l])) * (l : ℤ_[l]) ^ m`. Rewrite using `[hB]`.

Take the linear combination `(E1 : ℤ_[l]) * hX'`. Rewrite using `[smul_smul, hc, h3, add_smul, mul_smul, hv0, smul_zero, add_zero, Int.cast_smul_eq_zsmul]`. Rewrite using `[← hK]`. Use `Finset.sum_congr rfl (fun b _ => ?_)` and prove the remaining obligations. Establish `hφeq : restr ℤ_[l] (QZ l) hle ψ ⟨w b, wFix b⟩ = resInf D (e : ℤ) x ⟨w b, wInf b⟩`.

Rewrite using `[← hres]`. Both sides reduce to the same expression. Rewrite using `[hconj b, hφeq]`. Conclude with `alg _ _ _ _ _ (by push_cast; ring) ((fixLev E Ω l N m).2.2 M b (σ b) (by rw [hM]; exact dvd_mul_left _ _) (hσ b)) (hv _)`.
-/
theorem UpperTheory.V.Odd.resKill :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℕ) (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), IsCycAct Ω N ρ → ∀ a : ℕ, Odd a → a.Coprime (N * l) → ∀ x ∈ Sha D (e : ℤ), ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ (M : ℕ) [NeZero M] (h : N ∣ M), M = N * l ^ m → ∀ u : Uinf E Ω l, u.1 ∈ fixMu E Ω N → resInf D (e : ℤ) ((actRep D (e : ℤ) ρ).asAlgebraHom (coefMap ℤ_[l] (Gq ρ) (ytEl e a ((piQ ρ)⁻¹.comp (ZMod.unitsMap h)))) x) u = 0 := by
  intro E Ω _ _ _ _ _ l _ D e N _ ρ hρ a ha hac x hx
  obtain ⟨r, hr⟩ := (Z1_H1_qz_twist_l_power_torsion E Ω l D (e : ℤ)).2 x
  have hφ : resInf D (e : ℤ) x ∈ XDual l (cycU l (⊤ : Subgroup (G E Ω))) ℤ_[l] (QZ l) :=
    (Submodule.mem_inf.1 (resInfMem E Ω l D (e : ℤ) ⟨x, hx, rfl⟩)).1
  have hcl : IsClosed ((⊤ : Subgroup (G E Ω)) : Set (G E Ω)) := by
    rw [Subgroup.coe_top]
    exact isClosed_univ
  obtain ⟨n, ψ, hψ, hres⟩ := xdualExt E Ω l l ⊤ ℤ_[l] (QZ l) (Fact.out : l.Prime).ne_zero hcl _ hφ
  refine ⟨max n r + 2, fun m hm M _ h hM u hu => ?_⟩
  have key : ∀ b : (ZMod M)ˣ, (actRep D (↑e) ρ).asAlgebraHom (((MonoidAlgebra.lift ℤ (MonoidAlgebra ℤ_[l] (Gq ρ)) (Gq ρ)) (MonoidAlgebra.of ℤ_[l] (Gq ρ))).toRingHom (MonoidAlgebra.single (((piQ ρ)⁻¹.comp (ZMod.unitsMap h)) b)⁻¹ (↑(↑b : ZMod M).val ^ e * Eone M a ↑b))) = (((↑(↑b : ZMod M).val ^ e * Eone M a ↑b : ℤ) : ℤ_[l])) • galoisActionOnCohomology D (↑e) (ρ (ZMod.unitsMap h b)).toRingEquiv := by
    intro b
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidHom.comp_apply, MonoidHom.inv_apply, inv_inv, MonoidAlgebra.of_apply, MonoidAlgebra.smul_single, map_zsmul]
    rw [Representation.asAlgebraHom_single, zsmul_eq_mul, mul_one]
    rfl
  simp only [ytEl, sumEl, map_neg, map_sum, coefMap, key]
  rw [LinearMap.neg_apply, map_neg, Pi.neg_apply, neg_eq_zero, LinearMap.sum_apply, map_sum, Finset.sum_apply]
  simp only [LinearMap.smul_apply, map_smul, Pi.smul_apply]
  have hm2 : 2 ≤ m := le_trans (Nat.le_add_left 2 _) hm
  have hnm : n ≤ m := le_trans (le_trans (le_max_left n r) (Nat.le_add_right _ 2)) hm
  have hrm : r ≤ m := le_trans (le_trans (le_max_right n r) (Nat.le_add_right _ 2)) hm
  choose σ hσ using (liftEx E Ω M).1
  have hcycM : IsCycAct Ω M (ρ.comp (ZMod.unitsMap h)) := (actFacts E Ω N ρ hρ).2.2.2.2 M h
  have hlift : ∀ b : (ZMod M)ˣ, IsLift (ρ (ZMod.unitsMap h b)).toRingEquiv (σ b) := fun b => hcycM b (σ b) (hσ b)
  have hfixM : u.1 ∈ fixMu E Ω M := by
    rw [hM]
    exact (fixLev E Ω l N m).2.1 (Subgroup.mem_inf.2 ⟨u.2, hu⟩)
  let w : (ZMod M)ˣ → G E Ω := fun b =>
    AlgEquiv.ofRingEquiv (f := ((σ b).trans (u.1 : Ω ≃ₐ[E] Ω).toRingEquiv).trans (σ b).symm) (by
      intro y
      have h1 := hlift b y
      simp only [RingEquiv.trans_apply, AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv]
      rw [h1, AlgEquiv.commutes, ← h1, RingEquiv.symm_apply_apply])
  have hw : ∀ b y, w b y = (σ b).symm (u.1 (σ b y)) := fun _ _ => rfl
  have wInf : ∀ b, w b ∈ Uinf E Ω l := by
    intro b
    have hu1 : cycZ E Ω l u.1 = 1 := (Subgroup.mem_inf.1 u.2).2
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_top _, ?_⟩
    show cycZ E Ω l (w b) = 1
    have hra : MulSemiringAction.toRingAut (G E Ω) Ω (w b) = (σ b)⁻¹ * MulSemiringAction.toRingAut (G E Ω) Ω u.1 * σ b := by
      ext y
      rfl
    have hcz : ∀ g : G E Ω, cycZ E Ω l g = cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G E Ω) Ω g) := fun _ => rfl
    rw [hcz, hra, map_mul, map_mul, map_inv, ← hcz, hu1, mul_one, inv_mul_cancel]
  have wFix : ∀ b, w b ∈ fixMu E Ω M := by
    intro b y hy
    have hy' : (σ b y) ^ M = 1 := by rw [← map_pow, hy, map_one]
    rw [hw, hfixM _ hy', RingEquiv.symm_apply_apply]
  have hconj : ∀ b, resInf D (e : ℤ) (galoisActionOnCohomology D (e : ℤ) (ρ (ZMod.unitsMap h b)).toRingEquiv x) u = twScal l (σ b) (e : ℤ) • resInf D (e : ℤ) x ⟨w b, wInf b⟩ := fun b =>
    resInfConj E Ω l D (e : ℤ) _ (σ b) (hlift b) x ⟨w b, wInf b⟩ u (fun y => by
      show u.1 (σ b y) = σ b (w b y)
      rw [hw, RingEquiv.apply_symm_apply])
  have hle : fixMu E Ω M ≤ levU l ⊤ n := by
    intro g hg
    show g ∈ Un E Ω l n
    rw [← (fixLev E Ω l N n).1]
    intro y hy
    apply hg
    obtain ⟨k, hk⟩ : l ^ n ∣ M := by
      rw [hM]
      exact dvd_mul_of_dvd_right (pow_dvd_pow l hnm) N
    rw [hk, pow_mul, hy, one_pow]
  have hφ' : restr ℤ_[l] (QZ l) hle ψ ∈ XDual l (fixMu E Ω M) ℤ_[l] (QZ l) :=
    (restrMem E Ω l (fixMu E Ω M) (levU l ⊤ n) hle ℤ_[l] (QZ l) (qzG E Ω l (e : ℤ))).1 ⟨ψ, hψ, rfl⟩
  have h2M : 2 < M := by
    have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
    have h4 : 4 ≤ l ^ 2 := by nlinarith [pow_two l]
    have h4m : 4 ≤ l ^ m := le_trans h4 (Nat.pow_le_pow_right (by omega) hm2)
    have hN : 1 ≤ N := NeZero.one_le
    rw [hM]
    nlinarith
  have hacM : a.Coprime M := by
    rw [hM]
    exact Nat.Coprime.mul_right hac.coprime_mul_right_right (Nat.Coprime.pow_right m hac.coprime_mul_left_right)
  have hK := homKill E Ω M (ρ.comp (ZMod.unitsMap h)) hcycM h2M a ha hacM ℤ_[l] (QZ l) l _ hφ' σ hσ ⟨u.1, hfixM⟩ (fun b => ⟨w b, wFix b⟩) (fun b y => by
    show u.1 (σ b y) = σ b (w b y)
    rw [hw, RingEquiv.apply_symm_apply])
  have hv : ∀ g, (l : ℤ_[l]) ^ m • resInf D (e : ℤ) x g = 0 := by
    intro g
    have h0 : (l : ℤ_[l]) ^ r • resInf D (e : ℤ) x = 0 := by rw [← map_smul, hr, map_zero]
    rw [← Nat.sub_add_cancel hrm, pow_add, mul_smul]
    have h1 := congrFun h0 g
    simp only [Pi.smul_apply, Pi.zero_apply] at h1
    rw [h1, smul_zero]
  have alg : ∀ (c E1 : ℤ) (B : ℤ_[l]) (X : ℤ_[l]ˣ) (v : QZ l), (c : ℤ_[l]) = B ^ e * (E1 : ℤ_[l]) → (l : ℤ_[l]) ^ m ∣ (X : ℤ_[l]) - B → (l : ℤ_[l]) ^ m • v = 0 → (c : ℤ_[l]) • (((X ^ (-(e : ℤ)) : ℤ_[l]ˣ) : ℤ_[l]) • v) = E1 • v := by
    intro c E1 B X v hc hX hv0
    obtain ⟨t, ht⟩ : (l : ℤ_[l]) ^ m ∣ B ^ e - (X : ℤ_[l]) ^ e := dvd_trans (dvd_sub_comm.1 hX) (sub_dvd_pow_sub_pow _ _ _)
    have hX' : ((X ^ (-(e : ℤ)) : ℤ_[l]ˣ) : ℤ_[l]) * (X : ℤ_[l]) ^ e = 1 := by
      rw [zpow_neg, zpow_natCast, ← Units.val_pow_eq_pow_val, Units.inv_mul]
    have hB : B ^ e = (X : ℤ_[l]) ^ e + (l : ℤ_[l]) ^ m * t := by rw [← ht]; ring
    have h3 : B ^ e * (E1 : ℤ_[l]) * ((X ^ (-(e : ℤ)) : ℤ_[l]ˣ) : ℤ_[l]) = (E1 : ℤ_[l]) + ((E1 : ℤ_[l]) * t * ((X ^ (-(e : ℤ)) : ℤ_[l]ˣ) : ℤ_[l])) * (l : ℤ_[l]) ^ m := by
      rw [hB]
      linear_combination (E1 : ℤ_[l]) * hX'
    rw [smul_smul, hc, h3, add_smul, mul_smul, hv0, smul_zero, add_zero, Int.cast_smul_eq_zsmul]
  rw [← hK]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have hφeq : restr ℤ_[l] (QZ l) hle ψ ⟨w b, wFix b⟩ = resInf D (e : ℤ) x ⟨w b, wInf b⟩ := by
    rw [← hres]
    rfl
  rw [hconj b, hφeq]
  exact alg _ _ _ _ _ (by push_cast; ring) ((fixLev E Ω l N m).2.2 M b (σ b) (by rw [hM]; exact dvd_mul_left _ _) (hσ b)) (hv _)
