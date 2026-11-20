import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta

namespace Formalism.IndefR.Eqv.Act

open Formalism.IndefR.Lev

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}

/- English proof (translation)
Establish `h1 : (1 : GL (Fin V.rank) (EAf D)) ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flagL L)` using `Subgroup.one_mem _`. Conclude with `(Formalism.L2.DIV.levChar D.sp.cm V.gram β (flagL L)).map_one`.
-/
theorem levFn_flag_one : Formalism.L2.DIV.levFn β (flagL L) 1 = 1 := by
  have h1 : (1 : GL (Fin V.rank) (EAf D)) ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flagL L) := Subgroup.one_mem _
  exact (Formalism.L2.DIV.levChar D.sp.cm V.gram β (flagL L)).map_one

/- English proof (translation)
Establish `hxi : x⁻¹ ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L` using `Subgroup.inv_mem _ hx`. Establish `hxy : x⁻¹ * y ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L` using `Subgroup.mul_mem _ hxi hy`. Rewrite using `[levFn_flag_mul hxy hx, levFn_flag_mul hxi hy]`. Establish `e : Formalism.L2.DIV.levFn β (flagL L) x⁻¹ * Formalism.L2.DIV.levFn β (flagL L) x = 1`. Rewrite using `[← levFn_flag_mul hxi hx, inv_mul_cancel, levFn_flag_one]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_comm (Formalism.L2.DIV.levFn β (flagL L) x⁻¹), mul_assoc]`. Use `_ = Formalism.L2.DIV.levFn β (flagL L) y := by rw [e, mul_one]`.
-/
theorem levFn_conj {x y : GL (Fin V.rank) (EAf D)} (hx : x ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L)
    (hy : y ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L) :
    Formalism.L2.DIV.levFn β (flagL L) (x⁻¹ * y * x) = Formalism.L2.DIV.levFn β (flagL L) y := by
  have hxi : x⁻¹ ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := Subgroup.inv_mem _ hx
  have hxy : x⁻¹ * y ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := Subgroup.mul_mem _ hxi hy
  rw [levFn_flag_mul hxy hx, levFn_flag_mul hxi hy]
  have e : Formalism.L2.DIV.levFn β (flagL L) x⁻¹ * Formalism.L2.DIV.levFn β (flagL L) x = 1 := by
    rw [← levFn_flag_mul hxi hx, inv_mul_cancel, levFn_flag_one]
  calc Formalism.L2.DIV.levFn β (flagL L) x⁻¹ * Formalism.L2.DIV.levFn β (flagL L) y * Formalism.L2.DIV.levFn β (flagL L) x
      = Formalism.L2.DIV.levFn β (flagL L) y * (Formalism.L2.DIV.levFn β (flagL L) x⁻¹ * Formalism.L2.DIV.levFn β (flagL L) x) := by
        rw [mul_comm (Formalism.L2.DIV.levFn β (flagL L) x⁻¹), mul_assoc]
    _ = Formalism.L2.DIV.levFn β (flagL L) y := by rw [e, mul_one]

/- English proof (translation)
Use `show (k ∈ GfC V ∧ (finE V k ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L ∧ Formalism.L2.DIV.rTup β L (finE V k) ∈ (⊥ : Subgroup (Formalism.L2.DIV.G0 L.Pg L.r)))) ↔ _`. Rewrite using `[Subgroup.mem_bot]`.
-/
theorem mem_levG_flag1 {k : GA D V} :
    k ∈ levG V β (flag1L L) ↔ k ∈ GfC V ∧ finE V k ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L ∧
      Formalism.L2.DIV.rTup β L (finE V k) = 1 := by
  show (k ∈ GfC V ∧ (finE V k ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L ∧
      Formalism.L2.DIV.rTup β L (finE V k) ∈ (⊥ : Subgroup (Formalism.L2.DIV.G0 L.Pg L.r)))) ↔ _
  rw [Subgroup.mem_bot]

/- English proof (translation)
Unfold `levChi`. Rewrite using `[levFn_flag1]`.
-/
theorem levChi_flag1 (k : GA D V) : levChi V β (flag1L L) k = levChi V β (flagL L) k := by
  unfold levChi; rw [levFn_flag1]

/- English proof (translation)
Introduce `k hk h`. Take `⟨hk1, hk2, hk3⟩` from `mem_levG_flag1.1 hk`. Establish `hki : (finE V κ)⁻¹ ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L` using `Subgroup.inv_mem _ hκ'`. Establish `hm1 : (finE V κ)⁻¹ * finE V k ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L` using `Subgroup.mul_mem _ hki hk2`. Establish `hk' : κ⁻¹ * k * κ ∈ levG V β (flag1L L)`.

Use `mem_levG_flag1.2 ⟨?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hκ) hk1) hκ`. Rewrite using `[map_mul, map_mul, map_inv]`. Conclude with `Subgroup.mul_mem _ hm1 hκ'`. Rewrite using `[map_mul, map_mul, map_inv, Formalism.L2.DIV.rTup_mul hm1 hκ', Formalism.L2.DIV.rTup_mul hki hk2, Formalism.L2.DIV.rTup_inv hκ', hk3, mul_one, inv_mul_cancel]`.

Establish `e1` using `hF _ hk' (h * κ)`. Rewrite `e1` using `[show h * κ * (κ⁻¹ * k * κ) = h * k * κ by group]`. Establish `e2 : levChi V β (flag1L L) (κ⁻¹ * k * κ) = levChi V β (flag1L L) k`. Rewrite using `[levChi_flag1, levChi_flag1]`. Unfold `levChi`.

Rewrite using `[map_mul, map_mul, map_inv, levFn_conj hκ' hk2]`. Use `show c * F (h * k * κ) = levChi V β (flag1L L) k * (c * F (h * κ))`. Rewrite using `[e1, e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasType_rTrc {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) {κ : GA D V} (hκ : κ ∈ GfC V)
    (hκ' : finE V κ ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L) (c : ℂ) :
    HasType V β (flag1L L) (fun h => c * F (h * κ)) := by
  intro k hk h
  obtain ⟨hk1, hk2, hk3⟩ := mem_levG_flag1.1 hk
  have hki : (finE V κ)⁻¹ ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := Subgroup.inv_mem _ hκ'
  have hm1 : (finE V κ)⁻¹ * finE V k ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := Subgroup.mul_mem _ hki hk2
  have hk' : κ⁻¹ * k * κ ∈ levG V β (flag1L L) := by
    refine mem_levG_flag1.2 ⟨?_, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hκ) hk1) hκ
    · rw [map_mul, map_mul, map_inv]; exact Subgroup.mul_mem _ hm1 hκ'
    · rw [map_mul, map_mul, map_inv, Formalism.L2.DIV.rTup_mul hm1 hκ', Formalism.L2.DIV.rTup_mul hki hk2,
        Formalism.L2.DIV.rTup_inv hκ', hk3, mul_one, inv_mul_cancel]
  have e1 := hF _ hk' (h * κ)
  rw [show h * κ * (κ⁻¹ * k * κ) = h * k * κ by group] at e1
  have e2 : levChi V β (flag1L L) (κ⁻¹ * k * κ) = levChi V β (flag1L L) k := by
    rw [levChi_flag1, levChi_flag1]
    unfold levChi
    rw [map_mul, map_mul, map_inv, levFn_conj hκ' hk2]
  show c * F (h * k * κ) = levChi V β (flag1L L) k * (c * F (h * κ))
  rw [e1, e2]; ring

/- English proof (translation)
Use function extensionality and compare the values at `h`. Conclude with `level_action_spec hF ⟨κ, hκ⟩ κ hκ h`.
-/
theorem level_action_eq_lift {g0 : Formalism.L2.DIV.G0 L.Pg L.r} {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) {κ : GA D V}
    (hκ : IsLevelLift V β L g0 κ) : actG0 V β L g0 F = fun h => (levChi V β (flagL L) κ)⁻¹ * F (h * κ) := by
  funext h
  exact level_action_spec hF ⟨κ, hκ⟩ κ hκ h

/- English proof (translation)
Take `⟨κ, hκ⟩` from `hL g0`. Rewrite using `[level_action_eq_lift hF hκ]`. Conclude with `hasType_rTrc hF hκ.1 hκ.2.1 _`.
-/
theorem has_type_of_level_action (hL : LiftsExist V β L) (g0 : Formalism.L2.DIV.G0 L.Pg L.r) {F : GA D V → ℂ}
    (hF : HasType V β (flag1L L) F) : HasType V β (flag1L L) (actG0 V β L g0 F) := by
  obtain ⟨κ, hκ⟩ := hL g0
  rw [level_action_eq_lift hF hκ]
  exact hasType_rTrc hF hκ.1 hκ.2.1 _

/- English proof (translation)
Take `⟨κ1, hκ1⟩` from `hL g1`. Take `⟨κ2, hκ2⟩` from `hL g2`. Establish `h12 : IsLevelLift V β L (g1 * g2) (κ1 * κ2)`. Use `⟨Subgroup.mul_mem _ hκ1.1 hκ2.1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`.

Conclude with `Subgroup.mul_mem _ hκ1.2.1 hκ2.2.1`. Rewrite using `[map_mul, Formalism.L2.DIV.rTup_mul hκ1.2.1 hκ2.2.1, hκ1.2.2, hκ2.2.2]`. Establish `hF2` using `has_type_of_level_action hL g2 hF`. Rewrite using `[level_action_eq_lift hF2 hκ1, level_action_eq_lift hF h12, level_action_eq_lift hF hκ2]`. Use function extensionality and compare the values at `h`.

Establish `e : levChi V β (flagL L) (κ1 * κ2) = levChi V β (flagL L) κ1 * levChi V β (flagL L) κ2`. Unfold `levChi`. Rewrite using `[map_mul, levFn_flag_mul hκ1.2.1 hκ2.2.1, Units.val_mul]`. Establish `ha` using `levChi_ne_zero (β := β) (flagL L) κ1`. Establish `hb` using `levChi_ne_zero (β := β) (flagL L) κ2`.

Simplify using `only [e, mul_assoc]`. Clear the denominators using the available nonvanishing facts.
-/
theorem levelGroupAction_mul_of_lifts (hL : LiftsExist V β L) (g1 g2 : Formalism.L2.DIV.G0 L.Pg L.r) {F : GA D V → ℂ}
    (hF : HasType V β (flag1L L) F) : actG0 V β L g1 (actG0 V β L g2 F) = actG0 V β L (g1 * g2) F := by
  obtain ⟨κ1, hκ1⟩ := hL g1
  obtain ⟨κ2, hκ2⟩ := hL g2
  have h12 : IsLevelLift V β L (g1 * g2) (κ1 * κ2) := by
    refine ⟨Subgroup.mul_mem _ hκ1.1 hκ2.1, ?_, ?_⟩
    · rw [map_mul]; exact Subgroup.mul_mem _ hκ1.2.1 hκ2.2.1
    · rw [map_mul, Formalism.L2.DIV.rTup_mul hκ1.2.1 hκ2.2.1, hκ1.2.2, hκ2.2.2]
  have hF2 := has_type_of_level_action hL g2 hF
  rw [level_action_eq_lift hF2 hκ1, level_action_eq_lift hF h12, level_action_eq_lift hF hκ2]
  funext h
  have e : levChi V β (flagL L) (κ1 * κ2) = levChi V β (flagL L) κ1 * levChi V β (flagL L) κ2 := by
    unfold levChi; rw [map_mul, levFn_flag_mul hκ1.2.1 hκ2.2.1, Units.val_mul]
  have ha := levChi_ne_zero (β := β) (flagL L) κ1
  have hb := levChi_ne_zero (β := β) (flagL L) κ2
  simp only [e, mul_assoc]
  field_simp

end Formalism.IndefR.Eqv.Act

end
