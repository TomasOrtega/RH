import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntegralOffPrimesMatrixStepEntryData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrecedingStepDatumIntegralAwayFromLevels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepKernelDataIntegralAwayFromLevels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCastMemOfPrimeDvdAbsNorm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainLocalDataIntegralOffLevels

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.TwV.AdInt

/- English proof (translation)
Establish `h : x ∈ (NormedField.valuation (K` using `C)).integer := (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top`. Rewrite `h` using `[Valuation.mem_integer_iff, NormedField.valuation_apply]`. Conclude with `h` after adjusting the coercions.
-/
theorem norm_le_one_of_isIntegral' {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : @IsIntegral ℤ C _ _ (Ring.toIntAlgebra C) x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

/- English proof (translation)
Establish `hx' : IsIntegral ℤ (σ x)` using `map_isIntegral_int σ hx`. Establish `h : σ x ∈ TaylorLogMetric.Qbar` using `mem_algebraicClosure_iff'.2 hx'.tower_top`. Use `⟨h, fun p _ lam _ => ?_⟩` and prove the remaining obligations. Rewrite using `[lamC_of_mem lam h]`. Establish `h1 : IsIntegral ℤ (⟨σ x, h⟩ : TaylorLogMetric.Qbar)` using `(isIntegral_algHom_iff ((algebraMap TaylorLogMetric.Qbar ℂ).toIntAlgHom) Subtype.val_injective).1 hx'`.

Conclude with `norm_le_one_of_isIntegral' (map_isIntegral_int lam h1)`.
-/
theorem intOff_of_isIntegral {K : Type} [Field K] (σ : K →+* ℂ) (S : Finset ℕ) {x : K} (hx : IsIntegral ℤ x) :
    IntOff S (σ x) := by
  have hx' : IsIntegral ℤ (σ x) := map_isIntegral_int σ hx
  have h : σ x ∈ TaylorLogMetric.Qbar := mem_algebraicClosure_iff'.2 hx'.tower_top
  refine ⟨h, fun p _ lam _ => ?_⟩
  rw [lamC_of_mem lam h]
  have h1 : IsIntegral ℤ (⟨σ x, h⟩ : TaylorLogMetric.Qbar) :=
    (isIntegral_algHom_iff ((algebraMap TaylorLogMetric.Qbar ℂ).toIntAlgHom) Subtype.val_injective).1 hx'
  exact norm_le_one_of_isIntegral' (map_isIntegral_int lam h1)

end GlobalTheory.TwV.AdInt

namespace GlobalTheory.TwV.AdInt

section Ft

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

/- English proof (translation)
Unfold `ftY`. Use `split_ifs`. Conclude with `intOff_of_isIntegral σ B (hpsi _)`. Simplify using `using (IntOff.zero : IntOff B 0)`. Rewrite using `[map_mul, map_inv₀, map_pow, map_natCast]`.

Use `IntOff.mul ?_ (intOff_of_isIntegral σ B (hpsi _))` and prove the remaining obligations. Establish `hB' : SNum B (qOf P.1 ^ (cst.M * n))` using `⟨pow_pos hB.1 _, fun q hq hd => hB.2 q hq (hq.dvd_of_dvd_pow hd)⟩`. Simplify `IntOff.inv_nat hB'` using `[Nat.cast_pow]`. Simplify using `using (IntOff.zero : IntOff B 0)`.
-/
theorem ftY_intOff_of_psi (P : rowSG Pr sel mu) (hpsi : ∀ a, IsIntegral ℤ (cst.psi P a)) (σ : X.K →+* ℂ) {B : Finset ℕ}
    (hB : SNum B (qOf P.1)) {n : ℕ} (η : Sp X.E n →ₗ[X.E] X.E) (y : Sp X.E n) :
    IntOff B (σ (ftY sel mu cst P η y)) := by
  unfold ftY
  split_ifs
  · exact intOff_of_isIntegral σ B (hpsi _)
  · simpa using (IntOff.zero : IntOff B 0)
  · rw [map_mul, map_inv₀, map_pow, map_natCast]
    refine IntOff.mul ?_ (intOff_of_isIntegral σ B (hpsi _))
    have hB' : SNum B (qOf P.1 ^ (cst.M * n)) :=
      ⟨pow_pos hB.1 _, fun q hq hd => hB.2 q hq (hq.dvd_of_dvd_pow hd)⟩
    simpa [Nat.cast_pow] using IntOff.inv_nat hB'
  · simpa using (IntOff.zero : IntOff B 0)

end Ft

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX}

/- English proof (translation)
Unfold `XiTop XiTopG`. Rewrite using `[map_mul, map_prod]`. Use `IntOff.mul ?_ (GlobalTheory.intOff_finset_prod _ _ fun P _ => ?_)` and prove the remaining obligations. Unfold `phiT split_ifs`. Simplify using `using (IntOff.one : IntOff (t.O u μ).S 1)`.

Simplify using `using (IntOff.zero : IntOff (t.O u μ).S 0)`. Rewrite using `[map_mul]`. Use `IntOff.mul ((GlobalTheory.TopInt.phiTopG_root _ _ _ _ _ _ _ _).intOff _ _) ?_` and prove the remaining obligations. Conclude with `ftY_intOff_of_psi t.sel (t.tup μ) (t.cst μ) P (hpsi P) _ (GlobalTheory.KerTie.sNum_qOf_rowSG D L hT Gi Gl Kc Y cX ex t u μ P) _ _`.
-/
theorem xiTop_intOff_of_psi (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (hpsi : ∀ P x, IsIntegral ℤ ((t.cst μ).psi P x)) (i : ℕ) (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i)
    (Yb : Set (Sp t.X.E (D.R.N i))) (p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (i + 1))
    (x : HomE t.X.E (D.R.N i) (D.R.N (i + 1))) :
    IntOff (t.O u μ).S (t.seam.σ₀ (XiTop t.Ch t.sel (t.tup μ) (t.cst μ) i p Yb p' x)) := by
  unfold XiTop XiTopG
  rw [map_mul, map_prod]
  refine IntOff.mul ?_ (GlobalTheory.intOff_finset_prod _ _ fun P _ => ?_)
  · unfold phiT
    split_ifs
    · simpa using (IntOff.one : IntOff (t.O u μ).S 1)
    · simpa using (IntOff.zero : IntOff (t.O u μ).S 0)
  · rw [map_mul]
    refine IntOff.mul ((GlobalTheory.TopInt.phiTopG_root _ _ _ _ _ _ _ _).intOff _ _) ?_
    exact ftY_intOff_of_psi t.sel (t.tup μ) (t.cst μ) P (hpsi P) _
      (GlobalTheory.KerTie.sNum_qOf_rowSG D L hT Gi Gl Kc Y cX ex t u μ P) _ _

/- English proof (translation)
Unfold `Formalism.EigenvalueLevelCeiling.plc`. Rewrite using `[← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]`.
-/
theorem plc_dvd_iff {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    Formalism.EigenvalueLevelCeiling.plc v ∣ n ↔ (n : 𝓞 F) ∈ v.asIdeal := by
  unfold Formalism.EigenvalueLevelCeiling.plc
  rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]

/- English proof (translation)
Introduce `hk`. Take `⟨hp, P, hPQ, hgP⟩` from `(t.Q_rec μ (D.host.g k)).1 hk`. Unfold `QE at hPQ`. Use `split_ifs at hPQ with h`. Take `⟨v, hv, rfl⟩` from `Finset.mem_image.1 hPQ`.

Rewrite `hv` using `[Set.Finite.mem_toFinset]`. Establish `hgood : GoodPl t.X.E t.S v`. Assume the negation of the conclusion as `hg'`. Apply `hv` to reduce the goal to its premises. Establish `h2` using `(Subgroup.mem_inf.1 (t.tup μ).2).2`.

Conclude with `Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 v) hg'`. Establish `hvF : ((D.host.g k : ℕ) : 𝓞 t.X.F) ∈ v.asIdeal`. Rewrite using `[← hsel v]`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 t.X.F) (𝓞 t.X.E) _ ∈ (t.sel v).asIdeal`. Rewrite using `[map_natCast]`.

Conclude with `hgP`. Establish `hd` using `(plc_dvd_iff v _).2 hvF`. Establish `hpl : Formalism.EigenvalueLevelCeiling.plc v = D.host.g k` using `((Nat.dvd_prime hp).1 hd).resolve_left fun e => by`. Establish `h1` using `(plc_dvd_iff v 1).1 (by rw [e])`. Rewrite `h1` using `[Nat.cast_one]`.

Conclude with `v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)`. Apply `hgood.2.2` to reduce the goal to its premises. Rewrite using `[hpl, ← t.g_rec k]`. Conclude with `hg k`. Simplify using `at hPQ`.
-/
theorem g_not_mem_Qp (t : KerEntTied ex) (hsel : IsSel t.X t.sel) (hg : ∀ k, t.Pr.g k ∈ t.S) (μ : D.what₂.Tup) (k : Fin 2) :
    D.host.g k ∉ Y.Qp μ := by
  classical
  intro hk
  obtain ⟨hp, P, hPQ, hgP⟩ := (t.Q_rec μ (D.host.g k)).1 hk
  unfold QE at hPQ
  split_ifs at hPQ with h
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hPQ
    rw [Set.Finite.mem_toFinset] at hv
    have hgood : GoodPl t.X.E t.S v := by
      by_contra hg'
      apply hv
      have h2 := (Subgroup.mem_inf.1 (t.tup μ).2).2
      exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 v) hg'
    have hvF : ((D.host.g k : ℕ) : 𝓞 t.X.F) ∈ v.asIdeal := by
      rw [← hsel v]
      change algebraMap (𝓞 t.X.F) (𝓞 t.X.E) _ ∈ (t.sel v).asIdeal
      rw [map_natCast]
      exact hgP
    have hd := (plc_dvd_iff v _).2 hvF
    have hpl : Formalism.EigenvalueLevelCeiling.plc v = D.host.g k :=
      ((Nat.dvd_prime hp).1 hd).resolve_left fun e => by
        have h1 := (plc_dvd_iff v 1).1 (by rw [e])
        rw [Nat.cast_one] at h1
        exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    apply hgood.2.2
    rw [hpl, ← t.g_rec k]
    exact hg k
  · simp at hPQ

end GlobalTheory.TwV.AdInt

namespace GlobalTheory.TwV

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP _ _ i hi β β' x x' z`. Establish `hmu : ∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)` using `fun j => ⟨_, hP.mu0 j⟩`. Establish `hval : ∀ (j : Fin D.R.m) (v : HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)` using `fun j v hv => by`. Establish `h` using `hP.ch.muVal j v hv`. Rewrite `h` using `[t.glob_σ]`. Then use the resulting hypothesis.

Establish `hg : ∀ k, D.host.g k ∉ Y.Qp μ` using `AdInt.g_not_mem_Qp t hP.sel hP.avoid.1 μ`. Unfold `xiAd`. Use `split_ifs with h`. Unfold `xiPt split_ifs with h1 h2`. Apply the tactic sequence `exact GlobalTheory.KerTie.intOff_xiEntry D L hT Gi Gl Kc Y cX ex t hmu hval u μ hg i h1 _ _ _ _ _`.

Substitute `h2` using the available equality. Conclude with `GlobalTheory.xiCpl1_intOff D L hT Gi Gl Kc Y cX ex t hmu hval u μ hg _ _ _ _ _`. Conclude with `AdInt.xiTop_intOff_of_psi t u μ hP.psi _ _ _ _ _`. Conclude with `IntOff.zero`.
-/
theorem xiAd_intOff : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → ∀ i hi β β' x x' z,
    IntOff (t.O u μ).S (xiAd A a i hi β β' x x' z)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP _ _ i hi β β' x x' z
  have hmu : ∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j) := fun j => ⟨_, hP.mu0 j⟩
  have hval : ∀ (j : Fin D.R.m) (v : HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) →
      t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ) := fun j v hv => by
    have h := hP.ch.muVal j v hv
    rwa [t.glob_σ] at h
  have hg : ∀ k, D.host.g k ∉ Y.Qp μ := AdInt.g_not_mem_Qp t hP.sel hP.avoid.1 μ
  unfold xiAd
  split_ifs with h
  · unfold xiPt
    split_ifs with h1 h2
    · exact GlobalTheory.KerTie.intOff_xiEntry D L hT Gi Gl Kc Y cX ex t hmu hval u μ hg i h1 _ _ _ _ _
    · subst h2
      exact GlobalTheory.xiCpl1_intOff D L hT Gi Gl Kc Y cX ex t hmu hval u μ hg _ _ _ _ _
    · exact AdInt.xiTop_intOff_of_psi t u μ hP.psi _ _ _ _ _
  · exact IntOff.zero

end GlobalTheory.TwV
