import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleUnif
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLinearModelLatticeVacuumBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryGroupCharacterOfHeckeChar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceChartOfSplitIdempotent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdicCompletionValuationMapUniformiserStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardResidueFieldOfRingEquivAdicCompletionStatement

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LinExactAt
open GlobalTheory.SplitLinAt GlobalTheory.SplitLinear

/- English proof (translation)
Take `⟨hsS, hsT, hV, hΨ, hth⟩` from `hO`. Establish `he : IsSplitIdem D p.e` using `p.split`. Establish `hec : IsSplitIdem D (cA D p.e)` using `GlobalTheory.SplitScalar.isSplitIdem_conj he`. Establish `hA : ∀ u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (fun _ => True), IsHalf p.e u → u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)` using `fun u hu hh => latHalf D k p S T LS LT u hu (Or.inl hh)`. Establish `hle` using `latO_le (S := S) (T := T) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)`.

Establish `hfix : ∀ u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (fun _ => True), IsHalf p.e u ∨ IsHalf (cA D p.e) u → heisO ψ S T u f₀ = f₀` using `fun u hu hh => hh.elim (fun h1 => hV.2.2 p.e he u (latHalf D k p S T LS LT u hu hh) h1) fun h1 => hV.2.2 _ hec u (latHalf D k p S T LS LT u hu hh) h1`. Use `⟨hsS, hsT, hV, sbSubst hΨ g h _, hth.1, fun Tm hTm => ?_⟩` and prove the remaining obligations. Establish `hTm'` using `(placeModel_congr hA hle).1 hTm`. Establish `hSB` using `(sbHalf_congr hA hle).1 (sbHalf D k p S T n n' α β LS LT hsS hsT Ψ hΨ)`. Rewrite using `[hth.2 Tm hTm, lawAt D ψ S T χS χT om LS LT p.e f₀ Tm hW hsS hsT he hV.1 hfix hTm' (α.gl g) (β.gl h) (α.gl_supp g) (β.gl_supp h) _ _ (detFrame α g) (detFrame β h) _ hSB, ← map_smul, fac_lam]`.

Use `congr 1`. Use function extensionality and compare the values at `t`. Rewrite using `[Pi.smul_apply, smul_eq_mul, extFunAct D k p S T n n' α β Ψ g h t, ← extFun_smul]`.
-/
theorem linFirst (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T)
    (hW : IsWeilDatumO ψ S T χS χT om) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T) (f₀ : WO S T → ℂ) (Ψ : Matrix n n' k → ℂ)
    (f : WO S T → ℂ) (hO : Over ψ α β LS LT f₀ Ψ f) (g : GL n' k) (h : GL n k) :
    Over ψ α β LS LT f₀ (fun x => (lam p χT⁻¹ ((T.rank : ℝ) / 2) (Matrix.GeneralLinearGroup.det g) : ℂ) *
      (lam p χS (-(S.rank : ℝ) / 2) (Matrix.GeneralLinearGroup.det h) : ℂ) * Ψ ((h⁻¹ : GL n k).val * x * g.val))
      (om (α.gl g, β.gl h) f) := by
  obtain ⟨hsS, hsT, hV, hΨ, hth⟩ := hO
  have he : IsSplitIdem D p.e := p.split
  have hec : IsSplitIdem D (cA D p.e) := GlobalTheory.SplitScalar.isSplitIdem_conj he
  have hA : ∀ u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      IsHalf p.e u → u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v) :=
    fun u hu hh => latHalf D k p S T LS LT u hu (Or.inl hh)
  have hle := latO_le (S := S) (T := T) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)
  have hfix : ∀ u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      IsHalf p.e u ∨ IsHalf (cA D p.e) u → heisO ψ S T u f₀ = f₀ := fun u hu hh =>
    hh.elim (fun h1 => hV.2.2 p.e he u (latHalf D k p S T LS LT u hu hh) h1)
      fun h1 => hV.2.2 _ hec u (latHalf D k p S T LS LT u hu hh) h1
  refine ⟨hsS, hsT, hV, sbSubst hΨ g h _, hth.1, fun Tm hTm => ?_⟩
  have hTm' := (placeModel_congr hA hle).1 hTm
  have hSB := (sbHalf_congr hA hle).1 (sbHalf D k p S T n n' α β LS LT hsS hsT Ψ hΨ)
  rw [hth.2 Tm hTm, lawAt D ψ S T χS χT om LS LT p.e f₀ Tm hW hsS hsT he hV.1 hfix hTm' (α.gl g) (β.gl h)
    (α.gl_supp g) (β.gl_supp h) _ _ (detFrame α g) (detFrame β h) _ hSB, ← map_smul, fac_lam]
  congr 1
  funext t
  rw [Pi.smul_apply, smul_eq_mul, extFunAct D k p S T n n' α β Ψ g h t, ← extFun_smul]

/- English proof (translation)
Use `ext`. Rewrite using `[idl_val, p.idele_val]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem idl_eq {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (a : kˣ) : idl p a = p.idele a := by
  ext
  rw [idl_val, p.idele_val]
  ring

end GlobalTheory.LinExactAt

namespace GlobalTheory.LinExactAt

/- English proof (translation)
The claim follows from `Algebra.TensorProduct.includeLeft_injective (S := AF D.host.F) (algebraMap D.host.F D.host.E).injective`.
-/
theorem algebraMap_inj (D : D7) : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
  Algebra.TensorProduct.includeLeft_injective (S := AF D.host.F) (algebraMap D.host.F D.host.E).injective

/- English proof (translation)
Establish `h1 : (1 - E + s) * (1 - C + t) = 1 - E - C + s + t`. Take the linear combination `(1 - t - s + s * t) * hc + (E - s) * hcs + (C - C * t) * hs`. Establish `h2 : (1 - E - C + s + t) * (1 - (E + C)) = 1 - (E + C)`. Take the linear combination `he + hcc + (2 - s - t) * hc + (C - 1) * hs + (E - 1) * hcs`. Rewrite using `[h1, h2]`.
-/
theorem idem_calc {R : Type} [CommRing R] (E C s t : R) (he : E * E = E) (hcc : C * C = C) (hc : E * C = 0)
    (hs : E * s = s) (hcs : C * t = t) : (1 - E + s) * (1 - C + t) * (1 - (E + C)) = 1 - (E + C) := by
  have h1 : (1 - E + s) * (1 - C + t) = 1 - E - C + s + t := by
    linear_combination (1 - t - s + s * t) * hc + (E - s) * hcs + (C - C * t) * hs
  have h2 : (1 - E - C + s + t) * (1 - (E + C)) = 1 - (E + C) := by
    linear_combination he + hcc + (2 - s - t) * hc + (C - 1) * hs + (E - 1) * hcs
  rw [h1, h2]

/- English proof (translation)
Apply `algebraMap_inj D` to reduce the goal to its premises. Rewrite using `[map_mul, GlobalTheory.SplitDetCharacter.algebraMap_norm, map_sub, map_one, ← hε, p.idele_val]`. Establish `he : p.e * p.e = p.e` using `p.split.1`. Establish `hc : p.e * cA D p.e = 0` using `p.split.2.1`. Establish `hcc : cA D p.e * cA D p.e = cA D p.e` using `by rw [← map_mul, he]`.

Establish `hs : p.e * p.sec a = p.sec a` using `by rw [← p.sec_pr, p.pr_sec]`. Establish `hcs : cA D p.e * cA D (p.sec a) = cA D (p.sec a)` using `by rw [← map_mul, hs]`. Establish `hx : cA D (1 - p.e + p.sec a) = 1 - cA D p.e + cA D (p.sec a)`. Rewrite using `[map_add, map_sub, map_one]`. Rewrite using `[hx]`.

Conclude with `idem_calc _ _ _ _ he hcc hc hs hcs`.
-/
theorem norm_idele_mul {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (a : kˣ) (ε : AF D.host.F) (hε : p.e + cA D p.e = algebraMap (AF D.host.F) (AE D) ε) :
    Algebra.norm (AF D.host.F) (p.idele a : AE D) * (1 - ε) = 1 - ε := by
  apply algebraMap_inj D
  rw [map_mul, GlobalTheory.SplitDetCharacter.algebraMap_norm, map_sub, map_one, ← hε, p.idele_val]
  have he : p.e * p.e = p.e := p.split.1
  have hc : p.e * cA D p.e = 0 := p.split.2.1
  have hcc : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, he]
  have hs : p.e * p.sec a = p.sec a := by rw [← p.sec_pr, p.pr_sec]
  have hcs : cA D p.e * cA D (p.sec a) = cA D (p.sec a) := by rw [← map_mul, hs]
  have hx : cA D (1 - p.e + p.sec a) = 1 - cA D p.e + cA D (p.sec a) := by
    rw [map_add, map_sub, map_one]
  rw [hx]
  exact idem_calc _ _ _ _ he hcc hc hs hcs

/- English proof (translation)
Introduce `D k _ _ _ _ p a w hw`. Take `⟨ε, ⟨α, rfl, -, hα⟩, hsum⟩` from `p.above`. Establish `h` using `congrArg (fun y => evalV D.host.F w (sndA D.host.F y)) (norm_idele_mul p a _ hsum)`. Simplify using `only [map_mul, map_sub, map_one] at h`. Establish `h0 : evalV D.host.F w (sndA D.host.F (pairA D.host.F 0 α)) = 0` using `hα w hw`.

Rewrite `h` using `[h0, sub_zero, mul_one]`. Conclude with `Units.ext h`.
-/
theorem normOff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (a : kˣ) (w : Pl D), w ≠ p.v → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.normV D w (p.idele a) = 1 := by
  intro D k _ _ _ _ p a w hw
  obtain ⟨ε, ⟨α, rfl, -, hα⟩, hsum⟩ := p.above
  have h := congrArg (fun y => evalV D.host.F w (sndA D.host.F y)) (norm_idele_mul p a _ hsum)
  simp only [map_mul, map_sub, map_one] at h
  have h0 : evalV D.host.F w (sndA D.host.F (pairA D.host.F 0 α)) = 0 := hα w hw
  rw [h0, sub_zero, mul_one] at h
  exact Units.ext h

end GlobalTheory.LinExactAt

namespace GlobalTheory.LinExactAt

/- English proof (translation)
Establish `hs : p.e * p.sec a = p.sec a` using `by rw [← p.sec_pr, p.pr_sec]`. Establish `key : evalV D.host.F p.v (sndA D.host.F (Algebra.norm (AF D.host.F) (p.idele a : AE D))) = π (p.sec a)`. Rewrite using `[← halg, GlobalTheory.SplitDetCharacter.algebraMap_norm, map_mul, p.idele_val]`. Establish `hcs : cA D (p.sec a) = cA D p.e * cA D (p.sec a)` using `by rw [← map_mul, hs]`. Rewrite using `[map_add, map_sub, map_one, map_add, map_sub, map_one, map_add, map_sub, map_one, πe, hcs, map_mul, πce, zero_mul]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `key`.
-/
theorem norm_idele_chart {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (π : AE D →+* Fv D.host.F p.v)
    (halg : ∀ y : AF D.host.F, π (algebraMap (AF D.host.F) (AE D) y) = evalV D.host.F p.v (sndA D.host.F y))
    (πe : π p.e = 1) (πce : π (cA D p.e) = 0) (a : kˣ) :
    ((GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.normV D p.v (p.idele a) : (Fv D.host.F p.v)ˣ) : Fv D.host.F p.v) = π (p.sec a) := by
  have hs : p.e * p.sec a = p.sec a := by rw [← p.sec_pr, p.pr_sec]
  have key : evalV D.host.F p.v (sndA D.host.F (Algebra.norm (AF D.host.F) (p.idele a : AE D))) = π (p.sec a) := by
    rw [← halg, GlobalTheory.SplitDetCharacter.algebraMap_norm, map_mul, p.idele_val]
    have hcs : cA D (p.sec a) = cA D p.e * cA D (p.sec a) := by rw [← map_mul, hs]
    rw [map_add, map_sub, map_one, map_add, map_sub, map_one, map_add, map_sub, map_one, πe, hcs, map_mul, πce, zero_mul]
    ring
  exact key

open GlobalTheory.SplitHecke

/- English proof (translation)
Introduce `D k _ _ _ _ p`. Take `⟨v', π, hsurj, hker, halg, hint⟩` from `GlobalTheory.SplitChart.exists_chart p.e p.split`. Establish `he : p.e * p.e = p.e` using `p.split.1`. Establish `hce : p.e * cA D p.e = 0` using `p.split.2.1`. Establish `hs : ∀ a, p.e * p.sec a = p.sec a` using `fun a => by rw [← p.sec_pr, p.pr_sec]`.

Establish `πe : π p.e = 1`. Take `⟨c, hc⟩` from `hsurj 1`. Establish `h0 : π (p.e * c - c) = 0` using `(hker _).2 (by rw [mul_sub, ← mul_assoc, he, sub_self])`. Rewrite `h0` using `[map_sub, map_mul, hc, mul_one, sub_eq_zero]`. Conclude with `h0`.

Establish `πce : π (cA D p.e) = 0` using `(hker _).2 hce`. Establish `hv : v' = p.v`. Take `⟨ε, ⟨α, rfl, h1, hα⟩, hsum⟩` from `p.above`. Assume the negation of the conclusion as `hne`. Establish `h2` using `halg (pairA D.host.F 0 α)`.

Rewrite `h2` using `[← hsum, map_add, πe, πce, add_zero]`. Establish `h3 : evalV D.host.F v' (sndA D.host.F (pairA D.host.F 0 α)) = 0` using `hα v' hne`. Rewrite `h2` using `[h3]`. Conclude with `one_ne_zero h2`. Substitute `hv` using the available equality.

Set `f : k →+* Fv D.host.F p.v` to `{ toFun := fun a => π (p.sec a) map_one' := by rw [SplitPt.sec_one, πe] map_mul' := fun a b => by rw [SplitPt.sec_mul, map_mul] map_zero' := by rw [map_zero, map_zero] map_add' := fun a b => by rw [map_add, map_add] }`. Establish `hsurjf : Function.Surjective f` using `fun b => by`. Take `⟨c, rfl⟩` from `hsurj b`. Use `⟨p.pr c, ?_⟩` and prove the remaining obligations. Use `show π (p.sec (p.pr c)) = π c`.

Rewrite using `[p.sec_pr, map_mul, πe, one_mul]`. Use `⟨RingEquiv.ofBijective f ⟨f.injective, hsurjf⟩, fun a => ?_, fun a => ?_⟩` and prove the remaining obligations. Use `show Valued.v (π (p.sec a)) ≤ 1 ↔ a ∈ 𝒪[k]`. Rewrite using `[p.int_iff, ← IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ← isInt_Ov, ← hint, hs]`. Conclude with `norm_idele_chart p π halg πe πce a`.
-/
theorem chartAt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k), ∃ φ : k ≃+* Fv D.host.F p.v, (∀ a, Valued.v (φ a) ≤ 1 ↔ a ∈ 𝒪[k]) ∧
      ∀ a : kˣ, ((GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.normV D p.v (p.idele a) : (Fv D.host.F p.v)ˣ) : Fv D.host.F p.v) = φ a := by
  intro D k _ _ _ _ p
  obtain ⟨v', π, hsurj, hker, halg, hint⟩ := GlobalTheory.SplitChart.exists_chart p.e p.split
  have he : p.e * p.e = p.e := p.split.1
  have hce : p.e * cA D p.e = 0 := p.split.2.1
  have hs : ∀ a, p.e * p.sec a = p.sec a := fun a => by rw [← p.sec_pr, p.pr_sec]
  have πe : π p.e = 1 := by
    obtain ⟨c, hc⟩ := hsurj 1
    have h0 : π (p.e * c - c) = 0 := (hker _).2 (by rw [mul_sub, ← mul_assoc, he, sub_self])
    rw [map_sub, map_mul, hc, mul_one, sub_eq_zero] at h0
    exact h0
  have πce : π (cA D p.e) = 0 := (hker _).2 hce
  have hv : v' = p.v := by
    obtain ⟨ε, ⟨α, rfl, h1, hα⟩, hsum⟩ := p.above
    by_contra hne
    have h2 := halg (pairA D.host.F 0 α)
    rw [← hsum, map_add, πe, πce, add_zero] at h2
    have h3 : evalV D.host.F v' (sndA D.host.F (pairA D.host.F 0 α)) = 0 := hα v' hne
    rw [h3] at h2
    exact one_ne_zero h2
  subst hv
  let f : k →+* Fv D.host.F p.v :=
    { toFun := fun a => π (p.sec a)
      map_one' := by rw [SplitPt.sec_one, πe]
      map_mul' := fun a b => by rw [SplitPt.sec_mul, map_mul]
      map_zero' := by rw [map_zero, map_zero]
      map_add' := fun a b => by rw [map_add, map_add] }
  have hsurjf : Function.Surjective f := fun b => by
    obtain ⟨c, rfl⟩ := hsurj b
    refine ⟨p.pr c, ?_⟩
    show π (p.sec (p.pr c)) = π c
    rw [p.sec_pr, map_mul, πe, one_mul]
  refine ⟨RingEquiv.ofBijective f ⟨f.injective, hsurjf⟩, fun a => ?_, fun a => ?_⟩
  · show Valued.v (π (p.sec a)) ≤ 1 ↔ a ∈ 𝒪[k]
    rw [p.int_iff, ← IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ← isInt_Ov, ← hint, hs]
  · exact norm_idele_chart p π halg πe πce a

end GlobalTheory.LinExactAt

namespace GlobalTheory.LinExactAt

/- English proof (translation)
Introduce `D k _ _ _ _ p q`. Take `⟨φ, hφ, hn⟩` from `chartAt D k p`. Establish `h1` using `GlobalTheory.T.valued_v_map_irreducible_eq_ofAdd_neg_one D.host.F p.v k φ hφ q.1 q.2`. Establish `h2` using `GlobalTheory.T.card_residueField_of_ringEquiv_adicCompletion D.host.F p.v k φ hφ`. Apply the tactic sequence `have h3 : (((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))).log = -1 := by first | rfl | simp [WithZero.log] | exact WithZero.log_coe _`.

Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV, hn, GlobalTheory.LatPair.Unif.unit, Units.val_mk0, h1, resCard, h2, h3, zpow_neg_one]`.
-/
theorem absAt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (q : GlobalTheory.LatPair.Unif k),
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV D.host.F p.v (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.normV D p.v (p.idele q.unit)) = ((resCard k : ℕ) : ℝ)⁻¹ := by
  intro D k _ _ _ _ p q
  obtain ⟨φ, hφ, hn⟩ := chartAt D k p
  have h1 := GlobalTheory.T.valued_v_map_irreducible_eq_ofAdd_neg_one D.host.F p.v k φ hφ q.1 q.2
  have h2 := GlobalTheory.T.card_residueField_of_ringEquiv_adicCompletion D.host.F p.v k φ hφ
  have h3 : (((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))).log = -1 := by
    first | rfl | simp [WithZero.log] | exact WithZero.log_coe _
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV, hn, GlobalTheory.LatPair.Unif.unit, Units.val_mk0, h1, resCard, h2, h3, zpow_neg_one]

open GlobalTheory.SplitLinAt GlobalTheory.SplitLinear

/- English proof (translation)
Rewrite using `[idl_eq, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, finprod_eq_single _ p.v, absAt D k p q]`. Introduce `w hw`. Rewrite using `[normOff D k p _ w hw, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]`. Simplify using the standard rewrite rules.
-/
theorem absFin_unif {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (q : GlobalTheory.LatPair.Unif k) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (idl p q.unit) = ((resCard k : ℕ) : ℝ)⁻¹ := by
  rw [idl_eq, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, finprod_eq_single _ p.v, absAt D k p q]
  intro w hw
  rw [normOff D k p _ w hw, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
  simp

/- English proof (translation)
Rewrite using `[lam_val, absFin_unif, idl_eq, Real.inv_rpow (Nat.cast_nonneg _), ← Real.rpow_neg (Nat.cast_nonneg _), mul_comm]`.
-/
theorem lam_unif {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (q : GlobalTheory.LatPair.Unif k) (χ : (AE D)ˣ →* Circle) (r : ℝ) :
    ((lam p χ r q.unit : ℂˣ) : ℂ) = (((resCard k : ℝ) ^ (-r) : ℝ) : ℂ) * (χ (p.idele q.unit) : ℂ) := by
  rw [lam_val, absFin_unif, idl_eq, Real.inv_rpow (Nat.cast_nonneg _), ← Real.rpow_neg (Nat.cast_nonneg _), mul_comm]

end GlobalTheory.LinExactAt

namespace GlobalTheory.LinExactAt
open GlobalTheory.SplitLinAt GlobalTheory.SplitLinear

/- English proof (translation)
Introduce `D k _ _ _ _ p q ψ S T χS χT om hW`. Use `⟨lam p χT⁻¹ ((T.rank : ℝ) / 2), lam p χS (-(S.rank : ℝ) / 2), fun h => lamUnram D k p _ _ (unram_inv h), fun h => lamUnram D k p _ _ h, ?_, ?_, fun n n' _ _ _ _ α β LS LT f₀ Ψ f hO g h => linFirst D k p ψ S T χS χT om hW n n' α β LS LT f₀ Ψ f hO g h⟩` and prove the remaining obligations. Rewrite using `[lam_unif, MonoidHom.inv_apply, chrPow, zpow_neg, zpow_one, neg_div]`. Rewrite using `[lam_unif, chrPow, zpow_one, neg_div, neg_neg]`.
-/
theorem linExact : ∀ D : D7, GlobalTheory.FinPl.LinExact D := by
  intro D k _ _ _ _ p q ψ S T χS χT om hW
  refine ⟨lam p χT⁻¹ ((T.rank : ℝ) / 2), lam p χS (-(S.rank : ℝ) / 2),
    fun h => lamUnram D k p _ _ (unram_inv h), fun h => lamUnram D k p _ _ h, ?_, ?_,
    fun n n' _ _ _ _ α β LS LT f₀ Ψ f hO g h => linFirst D k p ψ S T χS χT om hW n n' α β LS LT f₀ Ψ f hO g h⟩
  · rw [lam_unif, MonoidHom.inv_apply, chrPow, zpow_neg, zpow_one, neg_div]
  · rw [lam_unif, chrPow, zpow_one, neg_div, neg_neg]

end GlobalTheory.LinExactAt

end
