import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLatBack
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetEqChartPointCoset
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU

/- English proof (translation)
Take `⟨w, hw1, hw⟩` from `H.chain.2.1 c`. Establish `hwm : w ∈ A.yb c`. Rewrite using `[hw, Set.mem_setOf_eq, sub_self]`. Conclude with `zero_mem _`. Establish `hmem : repY (A.yb c) ∈ A.yb c` using `Classical.epsilon_spec (p := fun y => y ∈ A.yb c) ⟨w, hwm⟩`.

Use `⟨H.coset c _ hmem P, ?_⟩` and prove the remaining obligations. Establish `hd` using `(Set.ext_iff.1 hw (repY (A.yb c))).1 hmem`. Rewrite `hd` using `[Set.mem_setOf_eq]`. Establish `h0` using `(Submodule.mem_iInf _).1 hd P`. Establish `h1` using `(Submodule.mem_iInf _).1 hw1 P`.

Rewrite `h0`, `h1` using `[Submodule.mem_comap]`. Establish `hf` using `GlobalTheory.ColPeriod.isFrames_frsF (A.pt _ (cpl_lt t μ).le c)`. Use `set fr := frsF t.sel (t.tup μ) (A.pt (t.m2 + 1) (cpl_lt t μ).le c) with hfr`. Establish `toStd : ∀ v, v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (A.pt (t.m2 + 1) (cpl_lt t μ).le c).deco.1.N → ∀ l, IntAt P.1 ((fr P).symm v l)`. Introduce `v hv`.

Use `GlobalTheory.TopStep.mem_stdAt.1 ((hf P _).1 ?_)` and prove the remaining obligations. Rewrite using `[LinearEquiv.apply_symm_apply]` and apply the resulting hypothesis. Establish `k0` using `toStd _ h0`. Establish `k1` using `toStd _ h1`. Simplify using `only [LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at k0 k1`.

Introduce `l`. Establish `hq : (qOf P.1 : t.X.E) ≠ 0` using `Nat.cast_ne_zero.2 fun h => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`. Establish `ipow : ∀ n : ℕ, IntAt P.1 ((qOf P.1 : t.X.E) ^ n)` using `fun n => by`. Simplify using `using IntAt.coe P.1 ((qOf P.1 : 𝓞 t.X.E) ^ n)`. Establish `a0` using `k0 l`.

Establish `a1` using `k1 l`. Distinguish the cases in `hP : P.1 ∈ t.Pr.vGs`. Simplify using `only [hP, if_true] at a0 a1 ⊢`. Establish `e : (qOf P.1 : t.X.E) ^ 1 * (fr P).symm (repY (A.yb c)) l = (qOf P.1 : t.X.E) ^ 1 * (((qOf P.1 : t.X.E) ^ (0 : ℤ))⁻¹ * (fr P).symm (repY (A.yb c)) l - ((qOf P.1 : t.X.E) ^ (0 : ℤ))⁻¹ * (fr P).symm w l) + ((qOf P.1 : t.X.E) ^ (-1 : ℤ))⁻¹ * (fr P).symm w l`. Simplify using `only [zpow_zero, inv_one, one_mul, _root_.zpow_neg, zpow_one, inv_inv, pow_one]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `IntAt.add (IntAt.mul (ipow 1) a0) a1`. Simplify using `only [hP, if_false] at a0 a1 ⊢`. Establish `e : (qOf P.1 : t.X.E) ^ (t.cst μ).M * (fr P).symm (repY (A.yb c)) l = (qOf P.1 : t.X.E) ^ (2 * (t.cst μ).M) * (((qOf P.1 : t.X.E) ^ ((t.cst μ).M : ℤ))⁻¹ * (fr P).symm (repY (A.yb c)) l - ((qOf P.1 : t.X.E) ^ ((t.cst μ).M : ℤ))⁻¹ * (fr P).symm w l) + ((qOf P.1 : t.X.E) ^ (-((t.cst …`.

Simplify using `only [_root_.zpow_neg, inv_inv, zpow_natCast]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `IntAt.add (IntAt.mul (ipow _) a0) a1`.
-/
theorem repY_yb_coset_bdd {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E} (H : AdTie A dtU a)
    (c : (D.chTw u μ).cls (t.m2 + 1)) (P : SB t μ) :
    SameCoset t.sel (t.tup μ) (t.cst μ) P ((frsF t.sel (t.tup μ) (A.pt (t.m2 + 1) (cpl_lt t μ).le c) P).symm (repY (A.yb c)))
        (A.y0 ((St (t.m2 + 1) (cpl_lt t μ).le).chOf c) P) ∧
      ∀ l, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ (if P.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M)) *
        (frsF t.sel (t.tup μ) (A.pt (t.m2 + 1) (cpl_lt t μ).le c) P).symm (repY (A.yb c)) l) := by
  obtain ⟨w, hw1, hw⟩ := H.chain.2.1 c
  have hwm : w ∈ A.yb c := by
    rw [hw, Set.mem_setOf_eq, sub_self]
    exact zero_mem _
  have hmem : repY (A.yb c) ∈ A.yb c := Classical.epsilon_spec (p := fun y => y ∈ A.yb c) ⟨w, hwm⟩
  refine ⟨H.coset c _ hmem P, ?_⟩
  have hd := (Set.ext_iff.1 hw (repY (A.yb c))).1 hmem
  rw [Set.mem_setOf_eq] at hd
  have h0 := (Submodule.mem_iInf _).1 hd P
  have h1 := (Submodule.mem_iInf _).1 hw1 P
  rw [Submodule.mem_comap] at h0 h1
  have hf := GlobalTheory.ColPeriod.isFrames_frsF (A.pt _ (cpl_lt t μ).le c)
  set fr := frsF t.sel (t.tup μ) (A.pt (t.m2 + 1) (cpl_lt t μ).le c) with hfr
  have toStd : ∀ v, v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (A.pt (t.m2 + 1) (cpl_lt t μ).le c).deco.1.N → ∀ l, IntAt P.1 ((fr P).symm v l) := by
    intro v hv
    refine GlobalTheory.TopStep.mem_stdAt.1 ((hf P _).1 ?_)
    rwa [LinearEquiv.apply_symm_apply]
  have k0 := toStd _ h0
  have k1 := toStd _ h1
  simp only [LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at k0 k1
  intro l
  have hq : (qOf P.1 : t.X.E) ≠ 0 := Nat.cast_ne_zero.2 fun h => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have ipow : ∀ n : ℕ, IntAt P.1 ((qOf P.1 : t.X.E) ^ n) := fun n => by
    simpa using IntAt.coe P.1 ((qOf P.1 : 𝓞 t.X.E) ^ n)
  have a0 := k0 l
  have a1 := k1 l
  by_cases hP : P.1 ∈ t.Pr.vGs
  · simp only [hP, if_true] at a0 a1 ⊢
    have e : (qOf P.1 : t.X.E) ^ 1 * (fr P).symm (repY (A.yb c)) l =
        (qOf P.1 : t.X.E) ^ 1 * (((qOf P.1 : t.X.E) ^ (0 : ℤ))⁻¹ * (fr P).symm (repY (A.yb c)) l - ((qOf P.1 : t.X.E) ^ (0 : ℤ))⁻¹ * (fr P).symm w l) +
          ((qOf P.1 : t.X.E) ^ (-1 : ℤ))⁻¹ * (fr P).symm w l := by
      simp only [zpow_zero, inv_one, one_mul, _root_.zpow_neg, zpow_one, inv_inv, pow_one]
      ring
    rw [e]
    exact IntAt.add (IntAt.mul (ipow 1) a0) a1
  · simp only [hP, if_false] at a0 a1 ⊢
    have e : (qOf P.1 : t.X.E) ^ (t.cst μ).M * (fr P).symm (repY (A.yb c)) l =
        (qOf P.1 : t.X.E) ^ (2 * (t.cst μ).M) * (((qOf P.1 : t.X.E) ^ ((t.cst μ).M : ℤ))⁻¹ * (fr P).symm (repY (A.yb c)) l -
          ((qOf P.1 : t.X.E) ^ ((t.cst μ).M : ℤ))⁻¹ * (fr P).symm w l) +
          ((qOf P.1 : t.X.E) ^ (-((t.cst μ).M : ℤ)))⁻¹ * (fr P).symm w l := by
      simp only [_root_.zpow_neg, inv_inv, zpow_natCast]
      field_simp
      ring
    rw [e]
    exact IntAt.add (IntAt.mul (ipow _) a0) a1

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Y cX ex t u μ St A dtU a H β x Q l`. Take `⟨⟨c, hc⟩, -⟩` from `((St _ (cpl_lt t μ).le).K β).y_bij.2 (Quotient.mk'' x)`. Substitute `hc` using the available equality. Take `⟨hs, hb⟩` from `repY_yb_coset_bdd H c Q`. Use `set w := (frsF t.sel (t.tup μ) (A.pt (t.m2 + 1) (cpl_lt t μ).le c) Q).symm (repY (A.yb c)) with hw`.

Establish `hsl` using `hs l`. Establish `hbl` using `hb l`. Simplify using `only [Pi.sub_apply] at hsl`. Establish `hq : (qOf Q.1 : t.X.E) ≠ 0` using `Nat.cast_ne_zero.2 fun h => Q.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`. Establish `ineg : ∀ n : ℕ, IntAt Q.1 (-((qOf Q.1 : t.X.E) ^ n))` using `fun n => by`.

Simplify using `using IntAt.coe Q.1 (-((qOf Q.1 : 𝓞 t.X.E) ^ n))`. Distinguish the cases in `hP : Q.1 ∈ t.Pr.vGs`. Simplify using `only [hP, if_true] at hsl hbl ⊢`. Establish `e : (qOf Q.1 : t.X.E) ^ 1 * A.y0 ((St (t.m2 + 1) (cpl_lt t μ).le).chOf c) Q l = (qOf Q.1 : t.X.E) ^ 1 * w l + (-((qOf Q.1 : t.X.E) ^ 1)) * (((qOf Q.1 : t.X.E) ^ 0)⁻¹ * (w l - A.y0 ((St (t.m2 + 1) (cpl_lt t μ).le).chOf c) Q l))`. Simplify using `only [pow_zero, inv_one, one_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `IntAt.add hbl (IntAt.mul (ineg 1) hsl)`. Simplify using `only [hP, if_false] at hsl hbl ⊢`. Establish `e : (qOf Q.1 : t.X.E) ^ (t.cst μ).M * A.y0 ((St (t.m2 + 1) (cpl_lt t μ).le).chOf c) Q l = (qOf Q.1 : t.X.E) ^ (t.cst μ).M * w l + (-((qOf Q.1 : t.X.E) ^ (2 * (t.cst μ).M))) * (((qOf Q.1 : t.X.E) ^ (t.cst μ).M)⁻¹ * (w l - A.y0 ((St (t.m2 + 1) (cpl_lt t μ).le).chOf c) Q l))`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `IntAt.add hbl (IntAt.mul (ineg _) hsl)`.
-/
theorem baseCosetRepresentative_bounded_at_bad_primes : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ} (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E), AdTie A dtU a → ∀ (β : (St (t.m2 + 1) (cpl_lt t μ).le).Ch) (x : UA D (t.m2 + 1) (cpl_lt t μ).le) (Q : SB t μ) (l : Fin (D.R.N (t.m2 + 1))), IntAt Q.1 ((qOf Q.1 : t.X.E) ^ (if Q.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) * A.y0 β Q l) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a H β x Q l
  obtain ⟨⟨c, hc⟩, -⟩ := ((St _ (cpl_lt t μ).le).K β).y_bij.2 (Quotient.mk'' x)
  subst hc
  obtain ⟨hs, hb⟩ := repY_yb_coset_bdd H c Q
  set w := (frsF t.sel (t.tup μ) (A.pt (t.m2 + 1) (cpl_lt t μ).le c) Q).symm (repY (A.yb c)) with hw
  have hsl := hs l
  have hbl := hb l
  simp only [Pi.sub_apply] at hsl
  have hq : (qOf Q.1 : t.X.E) ≠ 0 := Nat.cast_ne_zero.2 fun h => Q.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have ineg : ∀ n : ℕ, IntAt Q.1 (-((qOf Q.1 : t.X.E) ^ n)) := fun n => by
    simpa using IntAt.coe Q.1 (-((qOf Q.1 : 𝓞 t.X.E) ^ n))
  by_cases hP : Q.1 ∈ t.Pr.vGs
  · simp only [hP, if_true] at hsl hbl ⊢
    have e : (qOf Q.1 : t.X.E) ^ 1 * A.y0 ((St (t.m2 + 1) (cpl_lt t μ).le).chOf c) Q l =
        (qOf Q.1 : t.X.E) ^ 1 * w l + (-((qOf Q.1 : t.X.E) ^ 1)) *
          (((qOf Q.1 : t.X.E) ^ 0)⁻¹ * (w l - A.y0 ((St (t.m2 + 1) (cpl_lt t μ).le).chOf c) Q l)) := by
      simp only [pow_zero, inv_one, one_mul]
      ring
    rw [e]
    exact IntAt.add hbl (IntAt.mul (ineg 1) hsl)
  · simp only [hP, if_false] at hsl hbl ⊢
    have e : (qOf Q.1 : t.X.E) ^ (t.cst μ).M * A.y0 ((St (t.m2 + 1) (cpl_lt t μ).le).chOf c) Q l =
        (qOf Q.1 : t.X.E) ^ (t.cst μ).M * w l + (-((qOf Q.1 : t.X.E) ^ (2 * (t.cst μ).M))) *
          (((qOf Q.1 : t.X.E) ^ (t.cst μ).M)⁻¹ * (w l - A.y0 ((St (t.m2 + 1) (cpl_lt t μ).le).chOf c) Q l)) := by
      field_simp
      ring
    rw [e]
    exact IntAt.add hbl (IntAt.mul (ineg _) hsl)

end GlobalTheory.TwU
