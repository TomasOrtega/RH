import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CoboundaryLemmaNoColumn
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtInertiaAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtIneL
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.MemGalOfQuadraticOfFixesDiscrRootsOfUnity
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsIsDiagOnOfIsDiagOnInfKerSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DiagonalOnSubgroupOfConjugate
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsIsFlagOnOfEigenvectorNormalSubgroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.DecCyc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω N`. Establish `h1` using `Chr.cls_spec (k := ℚ) N g ζ hζ.pow_eq_one`. Rewrite `h1` using `[hg ζ hζ.pow_eq_one]`. Establish `h2 : ζ ^ 1 = ζ ^ ((Chr.cls ℚ Ω N g : ZMod N)).val` using `by rw [pow_one]; exact h1`.

Establish `hfin : IsOfFinOrder ζ` using `isOfFinOrder_iff_pow_eq_one.mpr ⟨N, Nat.pos_of_ne_zero (NeZero.ne N), hζ.pow_eq_one⟩`. Rewrite `h2` using `[hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf]`. Use `ext`. Rewrite using `[Units.val_one]`. Use `(ZMod.natCast_eq_natCast_iff _ _ _).mpr h2` as an intermediate fact.

Rewrite `this` using `[ZMod.natCast_val, ZMod.cast_id', id, Nat.cast_one]`. Conclude with `this.symm`.
-/
private theorem cls_eq_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (g : G ℚ Ω)
    (hg : ∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ) : Chr.cls ℚ Ω N g = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
  have h1 := Chr.cls_spec (k := ℚ) N g ζ hζ.pow_eq_one
  rw [hg ζ hζ.pow_eq_one] at h1
  have h2 : ζ ^ 1 = ζ ^ ((Chr.cls ℚ Ω N g : ZMod N)).val := by rw [pow_one]; exact h1
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.mpr ⟨N, Nat.pos_of_ne_zero (NeZero.ne N), hζ.pow_eq_one⟩
  rw [hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h2
  ext
  rw [Units.val_one]
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2
  rw [ZMod.natCast_val, ZMod.cast_id', id, Nat.cast_one] at this
  exact this.symm

/- English proof (translation)
Substitute `hY` using the available equality. Establish `e01` using `hb 0 1 (by decide)`. Establish `e10` using `hb 1 0 (by decide)`. Establish `e12` using `hb 1 2 (by decide)`. Establish `e21` using `hb 2 1 (by decide)`.

Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [corner, e01, e10, e12, e21, h1]`.
-/
private theorem block_form {k : Type} [Field k] (X : Matrix (Fin 3) (Fin 3) k) (Y : Matrix (Fin 2) (Fin 2) k)
    (hb : ∀ a b, Odd (wt a b) → X a b = 0) (h1 : X 1 1 = 1) (hY : Y = corner X) :
    X = !![Y 0 0, 0, Y 0 1; 0, 1, 0; Y 1 0, 0, Y 1 1] := by
  subst hY
  have e01 := hb 0 1 (by decide)
  have e10 := hb 1 0 (by decide)
  have e12 := hb 1 2 (by decide)
  have e21 := hb 2 1 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [corner, e01, e10, e12, e21, h1]

/- English proof (translation)
Establish `e : (conjBy M r g) = GG.ofGL M * r g * (GG.ofGL M)⁻¹` using `rfl`. Rewrite using `[e, GG.mat, ← map_inv]`. Simplify using `[SemidirectProduct.mul_left, SemidirectProduct.mul_right, hg, GG.mat, Units.val_mul]`.
-/
private theorem conj_mat {Γ k : Type} [Group Γ] [Field k] (M : GL (Fin 3) k) (r : Γ →* GG 3 k) (g : Γ)
    (hg : (r g).right = 1) : (conjBy M r g).mat = (M : Matrix (Fin 3) (Fin 3) k) * (r g).mat * ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
  have e : (conjBy M r g) = GG.ofGL M * r g * (GG.ofGL M)⁻¹ := rfl
  rw [e, GG.mat, ← map_inv]
  simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right, hg, GG.mat, Units.val_mul]

/- English proof (translation)
Use `set A := (M : Matrix (Fin 3) (Fin 3) k) * X * ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) with hA`. Use `set Mi := ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)`. Establish `hMi : Mi * (M : Matrix (Fin 3) (Fin 3) k) = 1`. Simplify using `[Mi, ← Units.val_mul]`. Establish `hXM : X * Mi = Mi * A`.

Rewrite using `[hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hMi, Matrix.one_mul]`. Establish `hcol : A *ᵥ Pi.single 0 1 = a • Pi.single 0 1`. Establish `h10 : A 1 0 = 0` using `h 1 0 (by simp [wt, wt1])`. Establish `h20 : A 2 0 = 0` using `h 2 0 (by simp [wt, wt1])`. Use extensionality with `i`.

Apply the tactic sequence `fin_cases i <;> simp [Matrix.mulVec_single, h0, h10, h20]`. Rewrite using `[Matrix.mulVec_mulVec, hXM, ← Matrix.mulVec_mulVec, hcol, Matrix.mulVec_smul]`.
-/
private theorem eigvec {k : Type} [Field k] (M : GL (Fin 3) k) (X : Matrix (Fin 3) (Fin 3) k) (a : k)
    (h0 : ((M : Matrix (Fin 3) (Fin 3) k) * X * ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) 0 0 = a)
    (h : ∀ i j, wt i j < 0 → ((M : Matrix (Fin 3) (Fin 3) k) * X * ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) i j = 0) :
    X *ᵥ (((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ Pi.single 0 1) =
      a • (((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ Pi.single 0 1) := by
  set A := (M : Matrix (Fin 3) (Fin 3) k) * X * ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) with hA
  set Mi := ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)
  have hMi : Mi * (M : Matrix (Fin 3) (Fin 3) k) = 1 := by
    simp [Mi, ← Units.val_mul]
  have hXM : X * Mi = Mi * A := by
    rw [hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hMi, Matrix.one_mul]
  have hcol : A *ᵥ Pi.single 0 1 = a • Pi.single 0 1 := by
    have h10 : A 1 0 = 0 := h 1 0 (by simp [wt, wt1])
    have h20 : A 2 0 = 0 := h 2 0 (by simp [wt, wt1])
    ext i
    fin_cases i <;> simp [Matrix.mulVec_single, h0, h10, h20]
  rw [Matrix.mulVec_mulVec, hXM, ← Matrix.mulVec_mulVec, hcol, Matrix.mulVec_smul]

/- English proof (translation)
Establish `hnd : ¬ ((l : ℤ) ∣ 2)`. Introduce `hd`. Use `Int.le_of_dvd (by norm_num) hd` as an intermediate fact. Establish `hle : l ≤ 2` using `by exact_mod_cast this`. Use `hl.out.two_le` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hu : IsUnit (2 : ℤ_[l])`. Rewrite using `[PadicInt.isUnit_iff]`. Establish `a1` using `PadicInt.norm_le_one (2 : ℤ_[l])`. Establish `a2 : ¬ ‖((2 : ℤ) : ℤ_[l])‖ < 1` using `by rw [PadicInt.norm_int_lt_one_iff_dvd]; exact hnd`.

Move the coercions through the operations in `at a2`. Conclude with `le_antisymm a1 (not_lt.mp a2)`. Take `⟨s, hs, hsv⟩` from `GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA hu.unit`. Use `⟨s, hs, fun n hn => ?_⟩` and prove the remaining obligations. Establish `hinj : Function.Injective ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom)` using `(algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective`.

Establish `hpow : hu.unit ^ n = 1`. Apply `Units.map_injective (f := ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom) hinj` to reduce the goal to its premises. Rewrite using `[map_zpow, map_one, ← hsv]`. Conclude with `hn`. Establish `hq : ((2 : ℚ) : ℚ_[l]) ^ n = 1`.

Use `congrArg (fun x : ℤ_[l]ˣ => ((Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom x : ℚ_[l]ˣ) : ℚ_[l])) hpow` as an intermediate fact. Simplify using `only [map_zpow, map_one, Units.val_one, Units.val_zpow_eq_zpow_val, Units.coe_map, IsUnit.unit_spec] at this`. Establish `e : (PadicInt.Coe.ringHom (p` using `l)) (2 : ℤ_[l]) = 2 := map_ofNat _ 2`. Express the relevant statement in the definitionally equal form `(PadicInt.Coe.ringHom (p := l)) 2 ^ n = 1 at this`. Rewrite `this` using `[e]`.

Simplify using `using this`. Establish `hq' : (2 : ℚ) ^ n = 1`. Use `hq` as an intermediate fact. Rewrite `this` using `[← Rat.cast_zpow, ← Rat.cast_one]`. Conclude with `this` after adjusting the coercions.

Conclude with `(zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)).mp hq'`.
-/
private theorem exists_two {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] (h2 : l ≠ 2)
    (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) :
    ∃ s ∈ Ine (F := ℚ) A, ∀ n : ℤ, cycBar ℚ Ω l s ^ n = 1 → n = 0 := by
  have hnd : ¬ ((l : ℤ) ∣ 2) := by
    intro hd
    have := Int.le_of_dvd (by norm_num) hd
    have hle : l ≤ 2 := by exact_mod_cast this
    have := hl.out.two_le
    omega
  have hu : IsUnit (2 : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    have a1 := PadicInt.norm_le_one (2 : ℤ_[l])
    have a2 : ¬ ‖((2 : ℤ) : ℤ_[l])‖ < 1 := by rw [PadicInt.norm_int_lt_one_iff_dvd]; exact hnd
    push_cast at a2
    exact le_antisymm a1 (not_lt.mp a2)
  obtain ⟨s, hs, hsv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA hu.unit
  refine ⟨s, hs, fun n hn => ?_⟩
  have hinj : Function.Injective ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) :=
    (algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective
  have hpow : hu.unit ^ n = 1 := by
    apply Units.map_injective (f := ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom) hinj
    rw [map_zpow, map_one, ← hsv]
    exact hn
  have hq : ((2 : ℚ) : ℚ_[l]) ^ n = 1 := by
    have := congrArg (fun x : ℤ_[l]ˣ => ((Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom x : ℚ_[l]ˣ) : ℚ_[l])) hpow
    simp only [map_zpow, map_one, Units.val_one, Units.val_zpow_eq_zpow_val, Units.coe_map, IsUnit.unit_spec] at this
    have e : (PadicInt.Coe.ringHom (p := l)) (2 : ℤ_[l]) = 2 := map_ofNat _ 2
    change (PadicInt.Coe.ringHom (p := l)) 2 ^ n = 1 at this
    rw [e] at this
    simpa using this
  have hq' : (2 : ℚ) ^ n = 1 := by
    have := hq
    rw [← Rat.cast_zpow, ← Rat.cast_one] at this
    exact_mod_cast this
  exact (zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)).mp hq'

/- English proof (translation)
Introduce `hC Ω _ _ _ K _ _ _ l hl c N _ e ψ D U g₁ hM r h ι hII hmod`. Take `⟨h11, -, W, hext, hcont, hirr, -, hdet⟩` from `typeII_facts hC D hM h hII`. Take `⟨-, -, -, -, -, -, -, -, -, -, hl1⟩` from `dat_facts D`. Set `ψQ : G ℚ Ω →* (Qbar l)ˣ` to `(Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω ψ)`. Establish `hΨ : ∀ g, D.ΨQ g = cycBar ℚ Ω l g ^ (e : ℤ) * ψQ g` using `fun g => by show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (chiO ℚ Ω l c.O g ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g) = _`.

Rewrite using `[map_mul, map_zpow]`. Both sides reduce to the same expression. Establish `hfin : ∀ g, ψQ g ^ Nat.card (ZMod N)ˣ = 1` using `fun g => by show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N g)) ^ _ = 1`. Rewrite using `[← map_pow, ← map_pow, pow_card_eq_one', map_one, map_one]`. Establish `hodd : Odd (discr K).natAbs` using `Nat.coprime_two_right.1 (D.gd.cop.coprime_dvd_right D.gd.N_even.two_dvd)`.

Establish `hkill : ∀ g : G ℚ Ω, (∀ ζ : Ω, ζ ^ (N * (discr K).natAbs) = 1 → g ζ = ζ) → ψQ g = 1 ∧ D.η g = 1` using `fun g hg => by`. Prove the components needed by the constructor for the conclusion. Use `show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N g)) = 1`. Rewrite using `[cls_eq_one N g fun ζ hζ => hg ζ (by rw [pow_mul, hζ, one_pow]), map_one, map_one]`. Rewrite using `[← MonoidHom.mem_ker, D.η_ker]`.

Conclude with `UpperTheory.mem_galOf_quadratic_of_fixes_discr_roots_of_unity Ω K D.gd.quad hodd g fun ζ hζ => hg ζ (by rw [pow_mul', hζ, one_pow])`. Establish `hblk : ∀ g ∈ D.η.ker, (r g).mat = !![W g 0 0, 0, W g 0 1; 0, 1, 0; W g 1 0, 0, W g 1 1]` using `fun g hg => block_form _ _ (hII.1 g hg) (h11 g hg) (hext.1 g hg)`. Use `⟨W, hirr, hmod W hext, ⟨hcont, fun w hw => ?_, fun w hw => ?_⟩, ?_, 1, fun s => ?_⟩` and prove the remaining obligations. Take `⟨A, hA⟩` from `exists_isPlaceOver Ω w`. Establish `hAl : ¬ A.valuation (l : Ω) < 1` using `fun h' => hw (((places ℚ Ω l A).2.2.1 w hA).1 h')`.

Take `⟨M, hMM⟩` from `pt_inertia_away D hM h A hAl`. Establish `h1` using `UpperTheory.diagonal_on_subgroup_of_conjugate (Ine (F := ℚ) A ⊓ D.η.ker) W ψQ M fun g hg => by`. Establish `hc : cycZ ℚ Ω l g = 1` using `(places ℚ Ω l A).2.2.2 hAl hg.1`. Establish `hc' : cycBar ℚ Ω l g = 1`. Rewrite using `[cycBar, MonoidHom.comp_apply, hc, map_one]`.

Rewrite using `[← hblk g hg.2, hMM g hg.1 hg.2, GG.mat, unitaryThreeReflection_left, tor_val, hΨ, hc', _root_.one_zpow, one_mul]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [wt1]`. Take `⟨χ, hχ, hd⟩` from `UpperTheory.exists_isDiagOn_of_isDiagOn_inf_ker_sign _ _ W ψQ h1`.

Conclude with `⟨A, hA, χ, fun i s hs => hχ i s (hkill s hs).1 (hkill s hs).2, hd⟩`. Take `⟨A, hA⟩` from `exists_isPlaceOver Ω w`. Establish `hAl : A.valuation (l : Ω) < 1` using `((places ℚ Ω l A).2.2.1 w hA).2 hw`. Take `⟨-, M, hup, hdiag⟩` from `pt_inertia_above hC D hM h A hAl`. Take `⟨hIk, s₀, hs₀, hu⟩` from `hl1 A hAl`.

Take `⟨hnorm, hID, -⟩` from `Chr.decCyc Ω l A hl.out hAl`. Establish `hs₀' : (D.ΨQ s₀ : Qbar l) ^ 2 ≠ 1`. Use `(hu.map (algebraMap c.O (PadicAlgCl l))).ne_zero` as an intermediate fact. Rewrite `this` using `[map_sub, map_pow, map_one, sub_ne_zero]`. Conclude with `this`.

Use `set v : Fin 3 → Qbar l := ((M⁻¹ : GL (Fin 3) (Qbar l)) : Matrix (Fin 3) (Fin 3) (Qbar l)) *ᵥ Pi.single 0 1 with hv`. Establish `hv0 : v ≠ 0` using `fun h0 => by`. Use `congrArg (fun x => ((M : Matrix (Fin 3) (Fin 3) (Qbar l)) *ᵥ x) 0) (hv.symm.trans h0)` as an intermediate fact. Simplify using `only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at this`. Simplify using `at this`.

Establish `hev : ∀ s ∈ Ine (F` using `ℚ) A, !![W s 0 0, 0, W s 0 1; 0, 1, 0; W s 1 0, 0, W s 1 1] *ᵥ v = (D.ΨQ s : Qbar l) • v := fun s hs => by`. Establish `hr : (r s).right = 1` using `(h.mult s).trans (hIk hs)`. Rewrite using `[← hblk s (hIk hs)]`. Use `eigvec M _ _ ?_ fun i j hij => ?_` and prove the remaining obligations. Rewrite using `[← conj_mat M r s hr, hdiag s hs 0]`.

Simplify using `[GG.mat, tor_val, wt1]`. Rewrite using `[← conj_mat M r s hr]`. Conclude with `hup s (hID hs) (hIk hs) i j hij`. Establish `hv1 : v 1 = 0`. Use `congrFun (hev s₀ hs₀) 1` as an intermediate fact.

Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this`. Assume the negation of the conclusion as `hne`. Establish `h3 : (D.ΨQ s₀ : Qbar l) = 1` using `(mul_right_cancel₀ hne ((one_mul _).trans this)).symm`. Conclude with `hs₀' (by rw [h3, one_pow])`. Take `⟨κ, hflag, hκ⟩` from `UpperTheory.exists_isFlagOn_of_eigenvector_normal_subgroup (Dec (F := ℚ) A) (Ine (F := ℚ) A) W D.ΨQ ![v 0, v 2] (fun d hd s hs => hnorm.conj_mem' ⟨s, hID hs⟩ hs ⟨d, hd⟩) (fun h0 => hv0 (by`.

Use function extensionality and compare the values at `i`. Use `fin_cases i`. Conclude with `congrFun h0 0`. Conclude with `hv1`. Conclude with `congrFun h0 1))`.

Use the proof step `(fun s hs => by`. Establish `a0` using `congrFun (hev s hs) 0`. Establish `a2` using `congrFun (hev s hs) 2`. Use function extensionality and compare the values at `i`. Use `fin_cases i`.

Simplify `a0` using `[Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]`. Simplify `a2)` using `[Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]`. Use the proof step `(fun s hs => by rw [hdet, show D.η s = 1 from hIk hs]; simp)`. Use the proof step `⟨s₀, hs₀, hs₀'⟩`. Establish `hκ' : ∀ i (s : ↥(Dec (F` using `ℚ) A)), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ i s = cycBar ℚ Ω l s ^ (![(e : ℤ), -(e : ℤ)] i) * (![ψQ, ψQ⁻¹] i) s := fun i s hs => by fin_cases i`.

Conclude with `(hκ s hs).1.trans (hΨ s)`. Use `(hκ s hs).2.trans ?_` and prove the remaining obligations. Rewrite using `[hΨ, mul_inv, ← _root_.zpow_neg]`. Both sides reduce to the same expression. Use `⟨A, hA, ![ψQ, ψQ⁻¹], κ, fun i s hs => ?_, hflag, hκ', Or.inl fun i j hij => ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `fin_cases i <;> simp [(hkill s hs).1]`. Take `⟨s, hs, hn⟩` from `exists_two D.gd.l_odd A hAl`. Establish `h1` using `DFunLike.congr_fun hij ⟨s, hID hs⟩`. Rewrite `h1` using `[MonoidHom.mul_apply, hκ' i _ hs, hκ' j _ hs]`. Establish `hf : ∀ i, ((![ψQ, ψQ⁻¹] i) s) ^ Nat.card (ZMod N)ˣ = 1` using `fun i => by fin_cases i`.

Conclude with `hfin s`. Use `show (ψQ s)⁻¹ ^ _ = 1`. Rewrite using `[inv_pow, hfin, inv_one]`. Establish `h2` using `congrArg (· ^ Nat.card (ZMod N)ˣ) h1`. Simplify using `only [mul_pow, hf, mul_one] at h2`.

Express the relevant statement in the definitionally equal form `(cycBar ℚ Ω l s ^ _) ^ _ = (cycBar ℚ Ω l s ^ _) ^ _ * cycBar ℚ Ω l s ^ _ at h2`. Rewrite `h2` using `[← mul_pow, ← _root_.zpow_add_one, ← mul_inv_eq_one, ← inv_pow, ← mul_pow, ← _root_.zpow_sub, ← _root_.zpow_natCast, ← _root_.zpow_mul]`. Establish `h3` using `(mul_eq_zero.1 (hn _ h2)).resolve_right (by exact_mod_cast Nat.card_pos.ne')`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp at h3 <;> omega`. Use `⟨N * (discr K).natAbs, Matrix.GeneralLinearGroup.det.comp W, Nat.mul_pos (NeZero.pos N) hodd.pos, fun s hs => Units.ext ?_, by simp⟩` and prove the remaining obligations.

Use `hdet s` as an intermediate fact. Rewrite `this` using `[(hkill s hs).2]`. Simplify using `using this`. Rewrite using `[one_mul, inv_one, mul_one, D.rhoK_apply]`. Conclude with `hblk _ (D.η_ker ▸ galEmb_mem ℚ K Ω s)`.
-/
theorem UpperTheory.V.U3.admissible_of_typeII :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG 3 (PadicAlgCl l)} (h : D.IsPt U g₁ r), ∀ (ι : Qbar l ≃+* ℂ),
      TypeII D.η r → (∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l), D.IsExt r W → D.IsModular ι W) →
      Af.Adm2 ι e (N * (discr K).natAbs) (D.rhoK r h.mult) := by
  intro hC Ω _ _ _ K _ _ _ l hl c N _ e ψ D U g₁ hM r h ι hII hmod
  obtain ⟨h11, -, W, hext, hcont, hirr, -, hdet⟩ := typeII_facts hC D hM h hII
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hl1⟩ := dat_facts D
  let ψQ : G ℚ Ω →* (Qbar l)ˣ := (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω ψ)
  have hΨ : ∀ g, D.ΨQ g = cycBar ℚ Ω l g ^ (e : ℤ) * ψQ g := fun g => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (chiO ℚ Ω l c.O g ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g) = _
    rw [map_mul, map_zpow]
    rfl
  have hfin : ∀ g, ψQ g ^ Nat.card (ZMod N)ˣ = 1 := fun g => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N g)) ^ _ = 1
    rw [← map_pow, ← map_pow, pow_card_eq_one', map_one, map_one]
  have hodd : Odd (discr K).natAbs := Nat.coprime_two_right.1 (D.gd.cop.coprime_dvd_right D.gd.N_even.two_dvd)
  have hkill : ∀ g : G ℚ Ω, (∀ ζ : Ω, ζ ^ (N * (discr K).natAbs) = 1 → g ζ = ζ) → ψQ g = 1 ∧ D.η g = 1 := fun g hg => by
    constructor
    · show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N g)) = 1
      rw [cls_eq_one N g fun ζ hζ => hg ζ (by rw [pow_mul, hζ, one_pow]), map_one, map_one]
    · rw [← MonoidHom.mem_ker, D.η_ker]
      exact UpperTheory.mem_galOf_quadratic_of_fixes_discr_roots_of_unity Ω K D.gd.quad hodd g fun ζ hζ => hg ζ (by rw [pow_mul', hζ, one_pow])
  have hblk : ∀ g ∈ D.η.ker, (r g).mat = !![W g 0 0, 0, W g 0 1; 0, 1, 0; W g 1 0, 0, W g 1 1] := fun g hg =>
    block_form _ _ (hII.1 g hg) (h11 g hg) (hext.1 g hg)
  refine ⟨W, hirr, hmod W hext, ⟨hcont, fun w hw => ?_, fun w hw => ?_⟩, ?_, 1, fun s => ?_⟩
  · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    have hAl : ¬ A.valuation (l : Ω) < 1 := fun h' => hw (((places ℚ Ω l A).2.2.1 w hA).1 h')
    obtain ⟨M, hMM⟩ := pt_inertia_away D hM h A hAl
    have h1 := UpperTheory.diagonal_on_subgroup_of_conjugate (Ine (F := ℚ) A ⊓ D.η.ker) W ψQ M fun g hg => by
      have hc : cycZ ℚ Ω l g = 1 := (places ℚ Ω l A).2.2.2 hAl hg.1
      have hc' : cycBar ℚ Ω l g = 1 := by
        rw [cycBar, MonoidHom.comp_apply, hc, map_one]
      rw [← hblk g hg.2, hMM g hg.1 hg.2, GG.mat, unitaryThreeReflection_left, tor_val, hΨ, hc', _root_.one_zpow, one_mul]
      congr 2
      funext i
      fin_cases i <;> simp [wt1]
    obtain ⟨χ, hχ, hd⟩ := UpperTheory.exists_isDiagOn_of_isDiagOn_inf_ker_sign _ _ W ψQ h1
    exact ⟨A, hA, χ, fun i s hs => hχ i s (hkill s hs).1 (hkill s hs).2, hd⟩
  · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    have hAl : A.valuation (l : Ω) < 1 := ((places ℚ Ω l A).2.2.1 w hA).2 hw
    obtain ⟨-, M, hup, hdiag⟩ := pt_inertia_above hC D hM h A hAl
    obtain ⟨hIk, s₀, hs₀, hu⟩ := hl1 A hAl
    obtain ⟨hnorm, hID, -⟩ := Chr.decCyc Ω l A hl.out hAl
    have hs₀' : (D.ΨQ s₀ : Qbar l) ^ 2 ≠ 1 := by
      have := (hu.map (algebraMap c.O (PadicAlgCl l))).ne_zero
      rw [map_sub, map_pow, map_one, sub_ne_zero] at this
      exact this
    set v : Fin 3 → Qbar l := ((M⁻¹ : GL (Fin 3) (Qbar l)) : Matrix (Fin 3) (Fin 3) (Qbar l)) *ᵥ Pi.single 0 1 with hv
    have hv0 : v ≠ 0 := fun h0 => by
      have := congrArg (fun x => ((M : Matrix (Fin 3) (Fin 3) (Qbar l)) *ᵥ x) 0) (hv.symm.trans h0)
      simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at this
      simp at this
    have hev : ∀ s ∈ Ine (F := ℚ) A,
        !![W s 0 0, 0, W s 0 1; 0, 1, 0; W s 1 0, 0, W s 1 1] *ᵥ v = (D.ΨQ s : Qbar l) • v := fun s hs => by
      have hr : (r s).right = 1 := (h.mult s).trans (hIk hs)
      rw [← hblk s (hIk hs)]
      refine eigvec M _ _ ?_ fun i j hij => ?_
      · rw [← conj_mat M r s hr, hdiag s hs 0]
        simp [GG.mat, tor_val, wt1]
      · rw [← conj_mat M r s hr]
        exact hup s (hID hs) (hIk hs) i j hij
    have hv1 : v 1 = 0 := by
      have := congrFun (hev s₀ hs₀) 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this
      by_contra hne
      have h3 : (D.ΨQ s₀ : Qbar l) = 1 := (mul_right_cancel₀ hne ((one_mul _).trans this)).symm
      exact hs₀' (by rw [h3, one_pow])
    obtain ⟨κ, hflag, hκ⟩ := UpperTheory.exists_isFlagOn_of_eigenvector_normal_subgroup (Dec (F := ℚ) A) (Ine (F := ℚ) A) W D.ΨQ ![v 0, v 2]
      (fun d hd s hs => hnorm.conj_mem' ⟨s, hID hs⟩ hs ⟨d, hd⟩)
      (fun h0 => hv0 (by
        funext i
        fin_cases i
        · exact congrFun h0 0
        · exact hv1
        · exact congrFun h0 1))
      (fun s hs => by
        have a0 := congrFun (hev s hs) 0
        have a2 := congrFun (hev s hs) 2
        funext i
        fin_cases i
        · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two] using a0
        · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two] using a2)
      (fun s hs => by rw [hdet, show D.η s = 1 from hIk hs]; simp)
      ⟨s₀, hs₀, hs₀'⟩
    have hκ' : ∀ i (s : ↥(Dec (F := ℚ) A)), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
        κ i s = cycBar ℚ Ω l s ^ (![(e : ℤ), -(e : ℤ)] i) * (![ψQ, ψQ⁻¹] i) s := fun i s hs => by
      fin_cases i
      · exact (hκ s hs).1.trans (hΨ s)
      · refine (hκ s hs).2.trans ?_
        rw [hΨ, mul_inv, ← _root_.zpow_neg]
        rfl
    refine ⟨A, hA, ![ψQ, ψQ⁻¹], κ, fun i s hs => ?_, hflag, hκ', Or.inl fun i j hij => ?_⟩
    · fin_cases i <;> simp [(hkill s hs).1]
    · obtain ⟨s, hs, hn⟩ := exists_two D.gd.l_odd A hAl
      have h1 := DFunLike.congr_fun hij ⟨s, hID hs⟩
      rw [MonoidHom.mul_apply, hκ' i _ hs, hκ' j _ hs] at h1
      have hf : ∀ i, ((![ψQ, ψQ⁻¹] i) s) ^ Nat.card (ZMod N)ˣ = 1 := fun i => by
        fin_cases i
        · exact hfin s
        · show (ψQ s)⁻¹ ^ _ = 1
          rw [inv_pow, hfin, inv_one]
      have h2 := congrArg (· ^ Nat.card (ZMod N)ˣ) h1
      simp only [mul_pow, hf, mul_one] at h2
      change (cycBar ℚ Ω l s ^ _) ^ _ = (cycBar ℚ Ω l s ^ _) ^ _ * cycBar ℚ Ω l s ^ _ at h2
      rw [← mul_pow, ← _root_.zpow_add_one, ← mul_inv_eq_one, ← inv_pow, ← mul_pow, ← _root_.zpow_sub, ← _root_.zpow_natCast,
        ← _root_.zpow_mul] at h2
      have h3 := (mul_eq_zero.1 (hn _ h2)).resolve_right (by exact_mod_cast Nat.card_pos.ne')
      fin_cases i <;> fin_cases j <;> simp at h3 <;> omega
  · refine ⟨N * (discr K).natAbs, Matrix.GeneralLinearGroup.det.comp W,
      Nat.mul_pos (NeZero.pos N) hodd.pos, fun s hs => Units.ext ?_, by simp⟩
    have := hdet s
    rw [(hkill s hs).2] at this
    simpa using this
  · rw [one_mul, inv_one, mul_one, D.rhoK_apply]
    exact hblk _ (D.η_ker ▸ galEmb_mem ℚ K Ω s)
