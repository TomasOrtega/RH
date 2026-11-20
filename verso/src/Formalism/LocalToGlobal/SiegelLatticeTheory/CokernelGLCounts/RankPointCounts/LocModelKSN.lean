import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModelKS

noncomputable section

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.FourierDecayAlt Formalism.L2.SG.DataInst
open Classical ValuativeRel

namespace Formalism.L2.SG.Pf.LMK

variable {D : Formalism.BasicNotions.D7}

def DeltaProd (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) →
      (Function.mulSupport fun p => A5.modK (M p).R (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p))).Finite ∧
      ∏ᶠ p, A5.modK (M p).R (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)) = (D.host.rdE ^ (2 * D.R.f))⁻¹

/- English proof (translation)
Establish `hu : IsUnit (Ring.inverse x)` using `hx.ringInverse`. Establish `h1 : A5.modK R (Ring.inverse x) * A5.modK R x = 1`. Rewrite using `[← Formalism.FourierDecayAlt.P.A5x5.modK_mul' hd hu hx, Ring.inverse_mul_cancel x hx]`. Simplify using `only [A5.modK, A5.mulR]`. Establish `hm : AddSubgroup.map (AddMonoidHom.mulLeft (1 : K)) R.toAddSubgroup = R.toAddSubgroup`.

Use extensionality with `y`. Simplify using the standard rewrite rules. Rewrite using `[hm, AddSubgroup.relIndex_self]`. Simplify using the standard rewrite rules. Conclude with `eq_inv_of_mul_eq_one_left h1`.
-/
theorem modK_inv_unit {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
    {ψ : AddChar K ℂ} (hd : A5.LocalDatum K R ψ) {x : K} (hx : IsUnit x) :
    A5.modK R (Ring.inverse x) = (A5.modK R x)⁻¹ := by
  have hu : IsUnit (Ring.inverse x) := hx.ringInverse
  have h1 : A5.modK R (Ring.inverse x) * A5.modK R x = 1 := by
    rw [← Formalism.FourierDecayAlt.P.A5x5.modK_mul' hd hu hx, Ring.inverse_mul_cancel x hx]
    simp only [A5.modK, A5.mulR]
    have hm : AddSubgroup.map (AddMonoidHom.mulLeft (1 : K)) R.toAddSubgroup = R.toAddSubgroup := by
      ext y
      simp
    rw [hm, AddSubgroup.relIndex_self]
    simp
  exact eq_inv_of_mul_eq_one_left h1

/- English proof (translation)
Establish `hOK` using `(hA p).1`. Use `haveI := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) hOK`. Establish `hd` using `Formalism.MainNotions.LocalModelPeriodLattices.datum_of_OK (M p) hOK`. Establish `h1 : A5.modK (M p).R 1 = 1`. Simplify using `only [A5.modK, A5.mulR]`.

Establish `hm1 : AddSubgroup.map (AddMonoidHom.mulLeft (1 : (D.s.atP p).Ep)) (M p).R.toAddSubgroup = (M p).R.toAddSubgroup`. Use extensionality with `y`. Simplify using the standard rewrite rules. Rewrite using `[hm1, AddSubgroup.relIndex_self]`. Simplify using the standard rewrite rules.

Establish `htw1 : twist p s 1 * twist p s 1 = 1`. Break down `hsp : (D.s.atP p).split with _ | sg` into its components or cases. Simplify using `[twist, hsp]`. Simplify using `only [twist, hsp]`. Apply `sg.e.injective` to reduce the goal to its premises.

Rewrite using `[map_mul, map_one]`. Simplify using `only [map_one, RingEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]`. Apply the tactic sequence `refine Prod.ext ?_ ?_ <;> first | (simp; done) | (simp [← mul_pow]; done) | (simp; rw [← mul_pow]; norm_num)`. Establish `hu : IsUnit (twist p s 1)` using `⟨⟨twist p s 1, twist p s 1, htw1, htw1⟩, rfl⟩`. Establish `hsq : A5.modK (M p).R (twist p s 1) * A5.modK (M p).R (twist p s 1) = 1`.

Rewrite using `[← Formalism.FourierDecayAlt.P.A5x5.modK_mul' hd hu hu, htw1, h1]`. Establish `hnn : 0 ≤ A5.modK (M p).R (twist p s 1)`. Unfold `A5.modK`. Check the signs of the components of the expression. Break down `mul_self_eq_one_iff.mp hsq with h | h` into its components or cases.

Conclude with `h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem modK_twist {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Agree δ M p) (p : PlF D) (s : ℕ) : A5.modK (M p).R (twist p s (1 : (D.s.atP p).Ep)) = 1 := by
  have hOK := (hA p).1
  haveI := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) hOK
  have hd := Formalism.MainNotions.LocalModelPeriodLattices.datum_of_OK (M p) hOK
  have h1 : A5.modK (M p).R 1 = 1 := by
    simp only [A5.modK, A5.mulR]
    have hm1 : AddSubgroup.map (AddMonoidHom.mulLeft (1 : (D.s.atP p).Ep)) (M p).R.toAddSubgroup =
        (M p).R.toAddSubgroup := by
      ext y
      simp
    rw [hm1, AddSubgroup.relIndex_self]
    simp
  have htw1 : twist p s 1 * twist p s 1 = 1 := by
    rcases hsp : (D.s.atP p).split with _ | sg
    · simp [twist, hsp]
    · simp only [twist, hsp]
      apply sg.e.injective
      rw [map_mul, map_one]
      simp only [map_one, RingEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
      refine Prod.ext ?_ ?_ <;> first | (simp; done) | (simp [← mul_pow]; done) | (simp; rw [← mul_pow]; norm_num)
  have hu : IsUnit (twist p s 1) := ⟨⟨twist p s 1, twist p s 1, htw1, htw1⟩, rfl⟩
  have hsq : A5.modK (M p).R (twist p s 1) * A5.modK (M p).R (twist p s 1) = 1 := by
    rw [← Formalism.FourierDecayAlt.P.A5x5.modK_mul' hd hu hu, htw1, h1]
  have hnn : 0 ≤ A5.modK (M p).R (twist p s 1) := by
    unfold A5.modK
    positivity
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exact h
  · linarith

/- English proof (translation)
Break down `hsp : (M p).split with _ | g` into its components or cases. Simplify using `only [Loc.Model.R, hsp]`. Rewrite using `[(M p).L.O_def]`. Use `first`. Consider the case `exact (isIntegral_algebraMap (x := (⟨b, hb⟩ : 𝒪[(D.s.atP p).Fp])) :)`.

Consider the case `(rw [show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b = algebraMap 𝒪[(D.s.atP p).Fp] (D.s.atP p).Ep ⟨b, hb⟩ from rfl]`. Conclude with `isIntegral_algebraMap)`. Consider the case `(rw [show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b = algebraMap 𝒪[(D.s.atP p).Fp] (D.s.atP p).Ep ⟨b, hb⟩ from (IsScalarTower.algebraMap_apply 𝒪[(D.s.atP p).Fp] (D.s.atP p).Fp (D.s.atP p).Ep ⟨b, hb⟩)]`. Conclude with `isIntegral_algebraMap)`. Simplify using `only [Loc.Model.R, hsp]`.

Rewrite using `[Subring.mem_comap, Subring.mem_map]`. Use `⟨(⟨b, hb⟩, ⟨b, hb⟩), ?_, ?_⟩` and prove the remaining obligations. Both sides reduce to the same expression. Simplify using the standard rewrite rules.
-/
theorem alg_mem_R {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (p : PlF D) {b : (D.s.atP p).Fp} (hb : b ∈ 𝒪[(D.s.atP p).Fp]) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b ∈ (M p).R := by
  rcases hsp : (M p).split with _ | g
  · simp only [Loc.Model.R, hsp]
    rw [(M p).L.O_def]
    first
    | exact (isIntegral_algebraMap (x := (⟨b, hb⟩ : 𝒪[(D.s.atP p).Fp])) :)
    | (rw [show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b =
          algebraMap 𝒪[(D.s.atP p).Fp] (D.s.atP p).Ep ⟨b, hb⟩ from rfl]
       exact isIntegral_algebraMap)
    | (rw [show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b =
          algebraMap 𝒪[(D.s.atP p).Fp] (D.s.atP p).Ep ⟨b, hb⟩ from
          (IsScalarTower.algebraMap_apply 𝒪[(D.s.atP p).Fp] (D.s.atP p).Fp (D.s.atP p).Ep ⟨b, hb⟩)]
       exact isIntegral_algebraMap)
  · simp only [Loc.Model.R, hsp]
    rw [Subring.mem_comap, Subring.mem_map]
    refine ⟨(⟨b, hb⟩, ⟨b, hb⟩), ?_, ?_⟩
    · rfl
    · simp

/- English proof (translation)
Establish `hv` using `Formalism.MainNotions.BridgeLemma.v_nat p n hn`. Establish `hn0 : ((n : ℕ) : (D.s.atP p).Fp) ≠ 0`. Introduce `h0`. Rewrite `hv` using `[h0, map_zero]`. Conclude with `zero_ne_one hv`.

Establish `hinv : (((n : ℕ) : (D.s.atP p).Fp))⁻¹ ∈ 𝒪[(D.s.atP p).Fp]` using `by first`. Consider the case `(rw [Valuation.mem_integer_iff, map_inv₀, hv, inv_one])`. Consider the case `(show valuation _ _ ≤ 1`. Rewrite using `[map_inv₀, hv, inv_one])`. Consider the case `(simp only [Valuation.mem_integer_iff, map_inv₀, hv, inv_one, le_refl])`.

Take `⟨w, hw⟩ : ∃ w : 𝒪[(D.s.atP p).Fp], (w : (D.s.atP p).Fp) * ((n : ℕ) : (D.s.atP p).Fp) = 1` from `⟨⟨_, hinv⟩, inv_mul_cancel₀ hn0⟩`. Establish `hnO : ((n : ℕ) : (D.s.atP p).Fp) ∈ 𝒪[(D.s.atP p).Fp]` using `by first`. Consider the case `exact natCast_mem _ n`. Consider the case `exact Subring.natCast_mem _ n`. Consider the case `simpa using (n : 𝒪[(D.s.atP p).Fp]).2`.

Establish `hxR` using `alg_mem_R (M := M) p hnO`. Establish `hyR` using `alg_mem_R (M := M) p w.2`. Establish `hxy : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (w : (D.s.atP p).Fp) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((n : ℕ) : (D.s.atP p).Fp) = 1`. Rewrite using `[← map_mul, hw, map_one]`. Simplify using `only [A5.modK, A5.mulR]`.

Establish `hmap : AddSubgroup.map (AddMonoidHom.mulLeft (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((n : ℕ) : (D.s.atP p).Fp))) (M p).R.toAddSubgroup = (M p).R.toAddSubgroup`. Use extensionality with `z`. Simplify using `only [AddSubgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`.

Conclude with `(M p).R.mul_mem hxR hy`. Introduce `hz`. Use `⟨_, (M p).R.mul_mem hyR hz, ?_⟩` and prove the remaining obligations. Use `show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((n : ℕ) : (D.s.atP p).Fp) * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (w : (D.s.atP p).Fp) * z) = z`. Rewrite using `[← mul_assoc, mul_comm (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((n : ℕ) : (D.s.atP p).Fp)), hxy, one_mul]`.

Rewrite using `[hmap, AddSubgroup.relIndex_self]`. Simplify using the standard rewrite rules.
-/
theorem modK_natUnit {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Agree δ M p) (p : PlF D) (n : ℕ) (hn : ¬ Loc.resChar p ∣ n) :
    A5.modK (M p).R (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((n : ℕ) : (D.s.atP p).Fp)) = 1 := by
  have hv := Formalism.MainNotions.BridgeLemma.v_nat p n hn
  have hn0 : ((n : ℕ) : (D.s.atP p).Fp) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  have hinv : (((n : ℕ) : (D.s.atP p).Fp))⁻¹ ∈ 𝒪[(D.s.atP p).Fp] := by
    first
    | (rw [Valuation.mem_integer_iff, map_inv₀, hv, inv_one])
    | (show valuation _ _ ≤ 1
       rw [map_inv₀, hv, inv_one])
    | (simp only [Valuation.mem_integer_iff, map_inv₀, hv, inv_one, le_refl])
  obtain ⟨w, hw⟩ : ∃ w : 𝒪[(D.s.atP p).Fp], (w : (D.s.atP p).Fp) * ((n : ℕ) : (D.s.atP p).Fp) = 1 :=
    ⟨⟨_, hinv⟩, inv_mul_cancel₀ hn0⟩
  have hnO : ((n : ℕ) : (D.s.atP p).Fp) ∈ 𝒪[(D.s.atP p).Fp] := by
    first
    | exact natCast_mem _ n
    | exact Subring.natCast_mem _ n
    | simpa using (n : 𝒪[(D.s.atP p).Fp]).2
  have hxR := alg_mem_R (M := M) p hnO
  have hyR := alg_mem_R (M := M) p w.2
  have hxy : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (w : (D.s.atP p).Fp) *
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((n : ℕ) : (D.s.atP p).Fp) = 1 := by
    rw [← map_mul, hw, map_one]
  simp only [A5.modK, A5.mulR]
  have hmap : AddSubgroup.map (AddMonoidHom.mulLeft (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
      ((n : ℕ) : (D.s.atP p).Fp))) (M p).R.toAddSubgroup = (M p).R.toAddSubgroup := by
    ext z
    simp only [AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (M p).R.mul_mem hxR hy
    · intro hz
      refine ⟨_, (M p).R.mul_mem hyR hz, ?_⟩
      show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((n : ℕ) : (D.s.atP p).Fp) *
        (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (w : (D.s.atP p).Fp) * z) = z
      rw [← mul_assoc, mul_comm (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((n : ℕ) : (D.s.atP p).Fp)), hxy,
        one_mul]
  rw [hmap, AddSubgroup.relIndex_self]
  simp

/- English proof (translation)
Rewrite using `[map_natCast, map_natCast]`.
-/
theorem ιE_nat (p : PlF D) (n : ℕ) :
    (D.s.atP p).ιE ((n : ℕ) : D.host.E) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((n : ℕ) : (D.s.atP p).Fp) := by
  rw [map_natCast, map_natCast]

/- English proof (translation)
Use `Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) (hA p).1` as an intermediate fact. Establish `hv` using `Formalism.MainNotions.BridgeLemma.v_nat p _ (Formalism.MainNotions.BridgeLemma.oth_not_dvd p)`. Use `set b : (D.s.atP p).Fp := ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : (D.s.atP p).Fp) with hbdef`. Establish `hb0 : b ≠ 0` using `by intro h0; rw [h0, map_zero] at hv; exact zero_ne_one hv`. Establish `hb1 : b ∈ 𝒪[(D.s.atP p).Fp]` using `by rw [Valuation.mem_integer_iff, hv]`.

Establish `hb2 : b⁻¹ ∈ 𝒪[(D.s.atP p).Fp]` using `by rw [Valuation.mem_integer_iff, map_inv₀, hv, inv_one]`. Establish `hoE : ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) ≠ 0` using `by exact_mod_cast Formalism.MainNotions.BridgeLemma.oth_ne_zero p`. Establish `huo : (uP p : D.host.E) * ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) = 1`. Rewrite using `[Formalism.MainNotions.BridgeLemma.unitAt_eq]`. Use `push_cast`.

Conclude with `inv_mul_cancel₀ hoE`. Establish `e1 : (D.s.atP p).ιE (uP p : D.host.E) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b⁻¹`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← map_mul, mul_inv_cancel₀ hb0, map_one, mul_one]`. Use `_ = (D.s.atP p).ιE ((uP p : D.host.E) * ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E)) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b⁻¹ := by`.

Rewrite using `[map_mul, ιE_nat, ← hbdef]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [huo, map_one, one_mul]`. Rewrite using `[e1]`. Conclude with `Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.modK_unitR (alg_mem_R (M := M) p hb2) (alg_mem_R (M := M) p hb1) (by rw [← map_mul, inv_mul_cancel₀ hb0, map_one])`.
-/
theorem modK_uP {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Agree δ M p) (p : PlF D) : A5.modK (M p).R ((D.s.atP p).ιE (uP p : D.host.E)) = 1 := by
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) (hA p).1
  have hv := Formalism.MainNotions.BridgeLemma.v_nat p _ (Formalism.MainNotions.BridgeLemma.oth_not_dvd p)
  set b : (D.s.atP p).Fp := ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : (D.s.atP p).Fp) with hbdef
  have hb0 : b ≠ 0 := by intro h0; rw [h0, map_zero] at hv; exact zero_ne_one hv
  have hb1 : b ∈ 𝒪[(D.s.atP p).Fp] := by rw [Valuation.mem_integer_iff, hv]
  have hb2 : b⁻¹ ∈ 𝒪[(D.s.atP p).Fp] := by rw [Valuation.mem_integer_iff, map_inv₀, hv, inv_one]
  have hoE : ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast Formalism.MainNotions.BridgeLemma.oth_ne_zero p
  have huo : (uP p : D.host.E) * ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) = 1 := by
    rw [Formalism.MainNotions.BridgeLemma.unitAt_eq]
    push_cast
    exact inv_mul_cancel₀ hoE
  have e1 : (D.s.atP p).ιE (uP p : D.host.E) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b⁻¹ := by
    calc (D.s.atP p).ιE (uP p : D.host.E)
        = (D.s.atP p).ιE (uP p : D.host.E) * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b *
            algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b⁻¹) := by
          rw [← map_mul, mul_inv_cancel₀ hb0, map_one, mul_one]
      _ = (D.s.atP p).ιE ((uP p : D.host.E) * ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E)) *
            algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b⁻¹ := by
          rw [map_mul, ιE_nat, ← hbdef]; ring
      _ = _ := by rw [huo, map_one, one_mul]
  rw [e1]
  exact Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.modK_unitR (alg_mem_R (M := M) p hb2) (alg_mem_R (M := M) p hb1)
    (by rw [← map_mul, inv_mul_cancel₀ hb0, map_one])

/- English proof (translation)
Use `Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) (hA p).1` as an intermediate fact. Establish `hd` using `Formalism.MainNotions.LocalModelPeriodLattices.datum_of_OK (M p) (hA p).1`. Establish `hg : ((Formalism.MainNotions.S.LocalSplitGroups.gpart p : ℕ) : (D.s.atP p).Fp) ≠ 0` using `Formalism.MainNotions.BridgeLemma.natFp_ne_zero p _ (Formalism.MainNotions.BridgeLemma.gpart_ne_zero p)`. Establish `ho : ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : (D.s.atP p).Fp) ≠ 0` using `Formalism.MainNotions.BridgeLemma.natFp_ne_zero p _ (Formalism.MainNotions.BridgeLemma.oth_ne_zero p)`. Rewrite using `[Formalism.MainNotions.BridgeLemma.qE_eq, ιE_nat, ← Formalism.MainNotions.BridgeLemma.gpart_mul_oth p, Nat.cast_mul, map_mul, Formalism.FourierDecayAlt.P.A5x5.modK_mul' hd ((isUnit_iff_ne_zero.2 hg).map _) ((isUnit_iff_ne_zero.2 ho).map _), modK_natUnit hA p _ (Formalism.MainNoti …`.
-/
theorem modK_qE {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Agree δ M p) (p : PlF D) :
    A5.modK (M p).R (qE p) = A5.modK (M p).R ((D.s.atP p).ιE ((Lat.gS D : ℕ) : D.host.E)) := by
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) (hA p).1
  have hd := Formalism.MainNotions.LocalModelPeriodLattices.datum_of_OK (M p) (hA p).1
  have hg : ((Formalism.MainNotions.S.LocalSplitGroups.gpart p : ℕ) : (D.s.atP p).Fp) ≠ 0 :=
    Formalism.MainNotions.BridgeLemma.natFp_ne_zero p _ (Formalism.MainNotions.BridgeLemma.gpart_ne_zero p)
  have ho : ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : (D.s.atP p).Fp) ≠ 0 :=
    Formalism.MainNotions.BridgeLemma.natFp_ne_zero p _ (Formalism.MainNotions.BridgeLemma.oth_ne_zero p)
  rw [Formalism.MainNotions.BridgeLemma.qE_eq, ιE_nat, ← Formalism.MainNotions.BridgeLemma.gpart_mul_oth p, Nat.cast_mul, map_mul,
    Formalism.FourierDecayAlt.P.A5x5.modK_mul' hd ((isUnit_iff_ne_zero.2 hg).map _) ((isUnit_iff_ne_zero.2 ho).map _),
    modK_natUnit hA p _ (Formalism.MainNotions.BridgeLemma.oth_not_dvd p), mul_one]

/- English proof (translation)
Establish `hOK` using `(hA p).1`. Use `haveI := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) hOK`. Establish `hd` using `Formalism.MainNotions.LocalModelPeriodLattices.datum_of_OK (M p) hOK`. Establish `hm : ∀ x y : (D.s.atP p).Ep, IsUnit x → IsUnit y → A5.modK (M p).R (x * y) = A5.modK (M p).R x * A5.modK (M p).R y` using `fun x y hx hy => Formalism.FourierDecayAlt.P.A5x5.modK_mul' hd hx hy`. Establish `h1 : A5.modK (M p).R 1 = 1`.

Simplify using `only [A5.modK, A5.mulR]`. Establish `hm1 : AddSubgroup.map (AddMonoidHom.mulLeft (1 : (D.s.atP p).Ep)) (M p).R.toAddSubgroup = (M p).R.toAddSubgroup`. Use extensionality with `y`. Simplify using the standard rewrite rules. Rewrite using `[hm1, AddSubgroup.relIndex_self]`.

Simplify using the standard rewrite rules. Establish `hpow : ∀ x : (D.s.atP p).Ep, IsUnit x → ∀ n : ℕ, A5.modK (M p).R (x ^ n) = (A5.modK (M p).R x) ^ n`. Introduce `x hx n`. Proceed by induction on `n with`. Consider the case `zero => simp [h1]`.

Consider the case `succ n ih => rw [pow_succ, hm _ _ (hx.pow n) hx, ih, pow_succ]`. Establish `htw : ∀ y : (D.s.atP p).Ep, twist p s y = twist p s 1 * y`. Introduce `y`. Break down `hsp : (D.s.atP p).split with _ | sg` into its components or cases. Simplify using `[twist, hsp]`.

Simplify using `only [twist, hsp]`. Apply `sg.e.injective` to reduce the goal to its premises. Rewrite using `[map_mul]`. Simplify using `only [map_one, RingEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]`. Apply the tactic sequence `refine Prod.ext ?_ ?_ <;> first | (simp; done) | (simp; ring) | ring`.

Establish `htw1 : twist p s 1 * twist p s 1 = 1`. Break down `hsp : (D.s.atP p).split with _ | sg` into its components or cases. Simplify using `[twist, hsp]`. Simplify using `only [twist, hsp]`. Apply `sg.e.injective` to reduce the goal to its premises.

Rewrite using `[map_mul, map_one]`. Simplify using `only [map_one, RingEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]`. Apply the tactic sequence `refine Prod.ext ?_ ?_ <;> first | (simp; done) | (simp [← mul_pow]; done) | (simp; rw [← mul_pow]; norm_num)`. Establish `htw1u : IsUnit (twist p s 1)` using `⟨⟨twist p s 1, twist p s 1, htw1, htw1⟩, rfl⟩`. Establish `hδu : IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p))` using `(isUnit_iff_ne_zero.mpr (hA p).2.1).map _`.

Establish `huu : IsUnit ((D.s.atP p).ιE (uP p : D.host.E))`. Apply `IsUnit.map` to reduce the goal to its premises. Rewrite using `[isUnit_iff_ne_zero]`. Conclude with `Formalism.L2.SG.Pf.LocModel.unitAt_ne_zero₂ p` after adjusting the coercions. Establish `htu : IsUnit ((D.s.atP p).ιE t)` using `(isUnit_iff_ne_zero.mpr ht).map _`.

Establish `hqu : IsUnit (qE p)`. Break down `hsp : (D.s.atP p).split with _ | sg` into its components or cases. Simplify using `[qE, hsp]`. Simplify using `only [qE, hsp]`. Apply `IsUnit.map` to reduce the goal to its premises.

Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`. Conclude with `sg.q_irr.ne_zero (by exact_mod_cast h0)`. Establish `hAU : IsUnit ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^ ν)` using `(hδu.mul huu).pow ν`. Establish `hY : IsUnit (twist p s ((D.s.atP p).ιE t))`.

Rewrite using `[htw]`. Conclude with `htw1u.mul htu`. Establish `hX` using `hAU.ringInverse`. Establish `hZ` using `hqu.ringInverse`. Simplify using `only [tMod]`.

Rewrite using `[hm _ _ (hX.mul hY) hZ, hm _ _ hX hY, modK_inv_unit hd hAU, modK_inv_unit hd hqu, hpow _ (hδu.mul huu), hm _ _ hδu huu, modK_uP hA p, mul_one, modK_qE hA p, htw, hm _ _ htw1u htu, modK_twist hA p s, one_mul]`.
-/
theorem modK_tMod {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Agree δ M p) (p : PlF D) (ν s : ℕ) {t : D.host.E} (ht : t ≠ 0) :
    A5.modK (M p).R (tMod δ p ν s t) =
      ((A5.modK (M p).R (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p))) ^ ν)⁻¹ *
        A5.modK (M p).R ((D.s.atP p).ιE t) *
        (A5.modK (M p).R ((D.s.atP p).ιE ((Lat.gS D : ℕ) : D.host.E)))⁻¹ := by
  have hOK := (hA p).1
  haveI := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) hOK
  have hd := Formalism.MainNotions.LocalModelPeriodLattices.datum_of_OK (M p) hOK
  have hm : ∀ x y : (D.s.atP p).Ep, IsUnit x → IsUnit y →
      A5.modK (M p).R (x * y) = A5.modK (M p).R x * A5.modK (M p).R y :=
    fun x y hx hy => Formalism.FourierDecayAlt.P.A5x5.modK_mul' hd hx hy
  have h1 : A5.modK (M p).R 1 = 1 := by
    simp only [A5.modK, A5.mulR]
    have hm1 : AddSubgroup.map (AddMonoidHom.mulLeft (1 : (D.s.atP p).Ep)) (M p).R.toAddSubgroup =
        (M p).R.toAddSubgroup := by
      ext y
      simp
    rw [hm1, AddSubgroup.relIndex_self]
    simp
  have hpow : ∀ x : (D.s.atP p).Ep, IsUnit x → ∀ n : ℕ,
      A5.modK (M p).R (x ^ n) = (A5.modK (M p).R x) ^ n := by
    intro x hx n
    induction n with
    | zero => simp [h1]
    | succ n ih => rw [pow_succ, hm _ _ (hx.pow n) hx, ih, pow_succ]
  have htw : ∀ y : (D.s.atP p).Ep, twist p s y = twist p s 1 * y := by
    intro y
    rcases hsp : (D.s.atP p).split with _ | sg
    · simp [twist, hsp]
    · simp only [twist, hsp]
      apply sg.e.injective
      rw [map_mul]
      simp only [map_one, RingEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
      refine Prod.ext ?_ ?_ <;> first | (simp; done) | (simp; ring) | ring
  have htw1 : twist p s 1 * twist p s 1 = 1 := by
    rcases hsp : (D.s.atP p).split with _ | sg
    · simp [twist, hsp]
    · simp only [twist, hsp]
      apply sg.e.injective
      rw [map_mul, map_one]
      simp only [map_one, RingEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
      refine Prod.ext ?_ ?_ <;> first | (simp; done) | (simp [← mul_pow]; done) | (simp; rw [← mul_pow]; norm_num)
  have htw1u : IsUnit (twist p s 1) := ⟨⟨twist p s 1, twist p s 1, htw1, htw1⟩, rfl⟩
  have hδu : IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)) :=
    (isUnit_iff_ne_zero.mpr (hA p).2.1).map _
  have huu : IsUnit ((D.s.atP p).ιE (uP p : D.host.E)) := by
    apply IsUnit.map
    rw [isUnit_iff_ne_zero]
    exact_mod_cast Formalism.L2.SG.Pf.LocModel.unitAt_ne_zero₂ p
  have htu : IsUnit ((D.s.atP p).ιE t) := (isUnit_iff_ne_zero.mpr ht).map _
  have hqu : IsUnit (qE p) := by
    rcases hsp : (D.s.atP p).split with _ | sg
    · simp [qE, hsp]
    · simp only [qE, hsp]
      apply IsUnit.map
      rw [isUnit_iff_ne_zero]
      intro h0
      exact sg.q_irr.ne_zero (by exact_mod_cast h0)
  have hAU : IsUnit ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^ ν) :=
    (hδu.mul huu).pow ν
  have hY : IsUnit (twist p s ((D.s.atP p).ιE t)) := by
    rw [htw]
    exact htw1u.mul htu
  have hX := hAU.ringInverse
  have hZ := hqu.ringInverse
  simp only [tMod]
  rw [hm _ _ (hX.mul hY) hZ, hm _ _ hX hY, modK_inv_unit hd hAU, modK_inv_unit hd hqu,
    hpow _ (hδu.mul huu), hm _ _ hδu huu, modK_uP hA p, mul_one, modK_qE hA p, htw,
    hm _ _ htw1u htu, modK_twist hA p s, one_mul]

/- English proof (translation)
Establish `h2 : Module.finrank D.host.F D.host.E = 2` using `Formalism.MainNotions.BridgeLemma.szf_finrankFE D`. Establish `h` using `(product_formula_e D.host.F D.host.E D.conjF h2 (fun p => D.s.atP p)).1 M (fun p => (hA p).1) x hx`. Establish `hu : ∀ p, IsUnit ((D.s.atP p).ιE x)` using `fun p => (isUnit_iff_ne_zero.mpr hx).map (D.s.atP p).ιE`. Establish `heq : ∀ p, A5.modK (M p).R ((D.s.atP p).ιE x) = (M p).modK ((D.s.atP p).ιE x)`. Introduce `p`.

Establish `h'` using `Formalism.MainNotions.LocalModelPeriodLattices.modK_of_OK (M p) (hA p).1 (hu p).unit`. Rewrite `h'` using `[IsUnit.unit_spec]`. Conclude with `h'.symm`. Simplify using `only [heq]`. Conclude with `h`.
-/
theorem pf_E {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Agree δ M p) {x : D.host.E} (hx : x ≠ 0) :
    (Function.mulSupport fun p => A5.modK (M p).R ((D.s.atP p).ιE x)).Finite ∧
      ∏ᶠ p, A5.modK (M p).R ((D.s.atP p).ιE x) = |((Algebra.norm ℚ x : ℚ) : ℝ)|⁻¹ := by
  have h2 : Module.finrank D.host.F D.host.E = 2 := Formalism.MainNotions.BridgeLemma.szf_finrankFE D
  have h := (product_formula_e D.host.F D.host.E D.conjF h2 (fun p => D.s.atP p)).1 M (fun p => (hA p).1) x hx
  have hu : ∀ p, IsUnit ((D.s.atP p).ιE x) := fun p => (isUnit_iff_ne_zero.mpr hx).map (D.s.atP p).ιE
  have heq : ∀ p, A5.modK (M p).R ((D.s.atP p).ιE x) = (M p).modK ((D.s.atP p).ιE x) := by
    intro p
    have h' := Formalism.MainNotions.LocalModelPeriodLattices.modK_of_OK (M p) (hA p).1 (hu p).unit
    rw [IsUnit.unit_spec] at h'
    exact h'.symm
  simp only [heq]
  exact h

/- English proof (translation)
Establish `h : ((n : ℕ) : D.host.E) = algebraMap ℚ D.host.E (n : ℚ)` using `by simp`. Rewrite using `[h, Algebra.norm_algebraMap]`. Use `congr 1`. Use `first`. Consider the case `exact Formalism.L2.Pj.hostSize_finrank D`.

Consider the case `exact Formalism.MainNotions.TwistedPlaces.finrank_E_host D`. Consider the case `exact Formalism.MainNotions.LatticeGluingRadicals.j_finrank D`. Consider the case `exact Formalism.MainNotions.BridgeLemma.szf_finrankE D`. Consider the case `exact Formalism.L2.SG.Pf.AllRowsRedKer.finrank_cmField D`. Consider the case `exact Formalism.L2.Geo.Rec.StarEmbeddingNorm.finrank_E_eq`.

Consider the case `exact Formalism.MainNotions.BridgeLemma.sza_finrank_host D`.
-/
theorem norm_nat (n : ℕ) : Algebra.norm ℚ ((n : ℕ) : D.host.E) = (n : ℚ) ^ (2 * D.R.f) := by
  have h : ((n : ℕ) : D.host.E) = algebraMap ℚ D.host.E (n : ℚ) := by simp
  rw [h, Algebra.norm_algebraMap]
  congr 1
  first
  | exact Formalism.L2.Pj.hostSize_finrank D
  | exact Formalism.MainNotions.TwistedPlaces.finrank_E_host D
  | exact Formalism.MainNotions.LatticeGluingRadicals.j_finrank D
  | exact Formalism.MainNotions.BridgeLemma.szf_finrankE D
  | exact Formalism.L2.SG.Pf.AllRowsRedKer.finrank_cmField D
  | exact Formalism.L2.Geo.Rec.StarEmbeddingNorm.finrank_E_eq
  | exact Formalism.MainNotions.BridgeLemma.sza_finrank_host D

/- English proof (translation)
Introduce `δ M hA ν s t ht`. Take `⟨f1, p1⟩` from `hDP δ M hA`. Establish `hg0 : ((Lat.gS D : ℕ) : D.host.E) ≠ 0` using `by exact_mod_cast (Formalism.MainNotions.LocalModelPeriodLattices.gS_pos D).ne'`. Take `⟨f2, p2⟩` from `pf_E hA ht`. Take `⟨f3, p3⟩` from `pf_E hA hg0`.

Establish `hfun : (fun p => A5.modK (M p).R (tMod δ p ν s t)) = fun p => ((A5.modK (M p).R (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p))) ^ ν)⁻¹ * A5.modK (M p).R ((D.s.atP p).ιE t) * (A5.modK (M p).R ((D.s.atP p).ιE ((Lat.gS D : ℕ) : D.host.E)))⁻¹` using `funext fun p => modK_tMod hA p ν s ht`. Establish `g1 : (Function.mulSupport fun p => ((A5.modK (M p).R (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p))) ^ ν)⁻¹).Finite`. Use `f1.subset fun p hp => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Apply `hp` to reduce the goal to its premises.

Simplify using `only [Function.mem_mulSupport, not_not] at hn ⊢`. Rewrite using `[hn, one_pow, inv_one]`. Establish `g3 : (Function.mulSupport fun p => (A5.modK (M p).R ((D.s.atP p).ιE ((Lat.gS D : ℕ) : D.host.E)))⁻¹).Finite`. Use `f3.subset fun p hp => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`.

Apply `hp` to reduce the goal to its premises. Simplify using `only [Function.mem_mulSupport, not_not] at hn ⊢`. Rewrite using `[hn, inv_one]`. Rewrite using `[hfun]`. Use `⟨((g1.union f2).union g3).subset ?_, ?_⟩` and prove the remaining obligations.

Introduce `p hp`. Assume the negation of the conclusion as `hn`. Simplify using `only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at hn`. Apply `hp` to reduce the goal to its premises. Simplify using `only [hn.1.1, hn.1.2, hn.2, mul_one]`.

Rewrite using `[finprod_mul_distrib (g1.union f2 |>.subset (Function.mulSupport_mul _ _)) g3, finprod_mul_distrib g1 f2, finprod_inv_distrib, finprod_inv_distrib, ← finprod_pow f1, p1, p2, p3, norm_nat]`. Unfold `nrm gNorm`. Use `push_cast`. Establish `hrd` using `Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D`. Establish `hgs : (0 : ℝ) < (Lat.gS D : ℝ)` using `by exact_mod_cast Formalism.MainNotions.LocalModelPeriodLattices.gS_pos D`.

Establish `hN : (0 : ℝ) < |((Algebra.norm ℚ t : ℚ) : ℝ)|`. Establish `: Algebra.norm ℚ t ≠ 0` using `(Algebra.norm_ne_zero_iff).2 ht`. Conclude with `abs_pos.2 (by exact_mod_cast this)`. Rewrite using `[pow_mul D.host.rdE (2 * D.R.f) ν]`. Rewrite using `[abs_of_pos (pow_pos hgs _)]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[← mul_pow, one_div, inv_mul_cancel₀ (pow_pos hrd _).ne', one_pow]`.
-/
theorem modNorm_of (hDP : DeltaProd D) : ModNorm D := by
  intro δ M hA ν s t ht
  obtain ⟨f1, p1⟩ := hDP δ M hA
  have hg0 : ((Lat.gS D : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast (Formalism.MainNotions.LocalModelPeriodLattices.gS_pos D).ne'
  obtain ⟨f2, p2⟩ := pf_E hA ht
  obtain ⟨f3, p3⟩ := pf_E hA hg0
  have hfun : (fun p => A5.modK (M p).R (tMod δ p ν s t)) = fun p =>
      ((A5.modK (M p).R (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p))) ^ ν)⁻¹ *
        A5.modK (M p).R ((D.s.atP p).ιE t) *
        (A5.modK (M p).R ((D.s.atP p).ιE ((Lat.gS D : ℕ) : D.host.E)))⁻¹ := funext fun p => modK_tMod hA p ν s ht
  have g1 : (Function.mulSupport fun p =>
      ((A5.modK (M p).R (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p))) ^ ν)⁻¹).Finite := by
    refine f1.subset fun p hp => ?_
    by_contra hn
    apply hp
    simp only [Function.mem_mulSupport, not_not] at hn ⊢
    rw [hn, one_pow, inv_one]
  have g3 : (Function.mulSupport fun p =>
      (A5.modK (M p).R ((D.s.atP p).ιE ((Lat.gS D : ℕ) : D.host.E)))⁻¹).Finite := by
    refine f3.subset fun p hp => ?_
    by_contra hn
    apply hp
    simp only [Function.mem_mulSupport, not_not] at hn ⊢
    rw [hn, inv_one]
  rw [hfun]
  refine ⟨((g1.union f2).union g3).subset ?_, ?_⟩
  · intro p hp
    by_contra hn
    simp only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at hn
    apply hp
    simp only [hn.1.1, hn.1.2, hn.2, mul_one]
  · rw [finprod_mul_distrib (g1.union f2 |>.subset (Function.mulSupport_mul _ _)) g3, finprod_mul_distrib g1 f2,
      finprod_inv_distrib, finprod_inv_distrib, ← finprod_pow f1, p1, p2, p3, norm_nat]
    unfold nrm gNorm
    push_cast
    have hrd := Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D
    have hgs : (0 : ℝ) < (Lat.gS D : ℝ) := by exact_mod_cast Formalism.MainNotions.LocalModelPeriodLattices.gS_pos D
    have hN : (0 : ℝ) < |((Algebra.norm ℚ t : ℚ) : ℝ)| := by
      have : Algebra.norm ℚ t ≠ 0 := (Algebra.norm_ne_zero_iff).2 ht
      exact abs_pos.2 (by exact_mod_cast this)
    rw [pow_mul D.host.rdE (2 * D.R.f) ν]
    rw [abs_of_pos (pow_pos hgs _)]
    field_simp
    rw [← mul_pow, one_div, inv_mul_cancel₀ (pow_pos hrd _).ne', one_pow]

end Formalism.L2.SG.Pf.LMK

namespace Formalism.L2.SG.Pf

/- English proof (translation)
Use `first`. Consider the case `exact localModelS_of (LMK.modNorm_of hDP)`. Consider the case `exact Formalism.L2.SG.Pf.localModelS_of (LMK.modNorm_of hDP)`. Consider the case `exact Formalism.L2.SG.localModelS_of (LMK.modNorm_of hDP)`. Consider the case `exact Formalism.L2.SG.DataCut.localModelS_of (LMK.modNorm_of hDP)`.
-/
theorem localModelS_of_delta {D : Formalism.BasicNotions.D7} (hDP : LMK.DeltaProd D) : Formalism.L2.SG.DataCut.LocalModelS D := by
  first
  | exact localModelS_of (LMK.modNorm_of hDP)
  | exact Formalism.L2.SG.Pf.localModelS_of (LMK.modNorm_of hDP)
  | exact Formalism.L2.SG.localModelS_of (LMK.modNorm_of hDP)
  | exact Formalism.L2.SG.DataCut.localModelS_of (LMK.modNorm_of hDP)

end Formalism.L2.SG.Pf
