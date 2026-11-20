import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchOperatorUnitaryWSeesaw
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergCommutingOperatorBlindToArchimedeanFibStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzArchimedeanSliceAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteWeightComplementaryArchimedeanSchwarStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

open GlobalTheory.ArchFactor in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ _ n d X W M ψ χX χW om hstd _ _ _ _ _ _ _ _ hweil h hh`. Establish `hW` using `GlobalTheory.WeilM.IsUWeilPair.isUSplitting hweil`. Establish `hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), om (1, h) Φ ∈ GlobalTheory.WeilM.schA F _` using `fun Φ hΦ => hW.pres (1, h) Φ hΦ`. Establish `h1 : (1 : UA σ X.J) ∈ UAt σ X (evI F)`. Introduce `u _`.

Simplify using `[mat]`. Establish `hcomm` using `comm_offI hweil (1, h) h1 hh`. Take `⟨R, hR0, hR⟩` from `GlobalTheory.T.exists_finiteWeight_complementary_archimedeanSchwartz (F := F) (Fin n × Fin d)`. Establish `hB : ∀ f : SInf F (Fin n × Fin d), ∃ g : SInf F (Fin n × Fin d), ∀ t, g t = (R 0)⁻¹ * om (1, h) (tens (evI F) (⇑f) R) (liftI t)`. Introduce `f`.

Take `⟨g, hg⟩` from `GlobalTheory.T.exists_schwartz_archimedeanSlice_adelicSchwartz _ (Submodule.smul_mem _ (R 0)⁻¹ (hkeep _ (hR f).2))`. Conclude with `⟨g, fun t => by rw [hg]; rfl⟩`. Use `choose Tf hTf using hB`. Establish `htens_add : ∀ f g : SInf F (Fin n × Fin d), tens (evI F) (⇑(f + g)) R = tens (evI F) (⇑f) R + tens (evI F) (⇑g) R`. Introduce `f g`.

Use function extensionality and compare the values at `x`. Simplify using `only [tens, SchwartzMap.add_apply, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `htens_smul : ∀ (c : ℂ) (f : SInf F (Fin n × Fin d)), tens (evI F) (⇑(c • f)) R = c • tens (evI F) (⇑f) R`. Introduce `c f`.

Use function extensionality and compare the values at `x`. Simplify using `only [tens, SchwartzMap.smul_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Set `T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)` to `{ toFun := Tf map_add' := fun f g => by`. Use extensionality with `t`.

Rewrite using `[SchwartzMap.add_apply, hTf, hTf, hTf, htens_add, map_add, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `map_smul' := fun c f => by`. Use extensionality with `t`. Rewrite using `[SchwartzMap.smul_apply, hTf, hTf, htens_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul, RingHom.id_apply]`.

Use `ring }`. Use `⟨T, fun f r hr => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `y`. Use `set T0 := om (1, h) with hT0`. Use `set u : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) with hudef`.

Establish `hu : evI F u = 0` using `by show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0`. Conclude with `map_zero _`. Use `set p : Fin n × Fin d → AF F := liftI (fun i => evI F (y i)) with hpdef`. Establish `hyp : y + u • (-y) = p`. Use function extensionality and compare the values at `i`.

Simplify using `only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef, liftI, evI, RingEquiv.symm_apply_apply]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show (y i).1 + 0 * (-(y i)).1 = (y i).1`. Simplify using the standard rewrite rules. Use `show (y i).2 + 1 * (-(y i)).2 = 0`.

Rewrite using `[one_mul]`. Conclude with `add_neg_cancel ((y i).2)`. Establish `hpat : At (evI F) p`. Introduce `u' hu'`. Establish `h0 : u'.1 = 0` using `(InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu')`.

Use function extensionality and compare the values at `i`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show u'.1 * (p i).1 = 0`. Rewrite using `[h0, zero_mul]`. Use `show u'.2 * (p i).2 = 0`.

Simplify using `[hpdef, liftI]`. Use `set Φ₀ := tens (evI F) (⇑f) R with hΦ₀`. Use `set Φ₁ := tens (evI F) (⇑f) r with hΦ₁`. Use `set Φ₂ : (Fin n × Fin d → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂`. Establish `hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _` using `(hR f).2`.

Establish `hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _` using `Submodule.smul_mem _ _ (GlobalTheory.SchwartzTranslation.schA_add_const _ _ hm₀)`. Establish `hfz : ∀ z, At (evI F) z → (Φ₁ - Φ₂) (y + z) = 0`. Introduce `z hz`. Establish `e1 : r (y + z) = r y` using `hr.1 y z hz`. Establish `e2 : y + z + u • (-y) = p + z` using `by rw [← hyp]; abel`.

Establish `hpz : At (evI F) (p + z)` using `fun u' hu' => by`. Rewrite using `[smul_add, hpat u' hu', hz u' hu', add_zero]`. Establish `e3 : R (p + z) = R 0` using `by simpa using (hR f).1 0 (p + z) hpz`. Establish `e4 : (fun i => evI F ((y + z + u • (-y)) i)) = fun i => evI F ((y + z) i)`. Use function extensionality and compare the values at `i`.

Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add', evI_mul', hu, zero_mul, add_zero]`. Simplify using `only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]`. Rewrite using `[e4, e2, e3, e1]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `h0` using `GlobalTheory.T.heisenbergCommuting_operator_independent_of_archimedeanFibres ψ T0 hstd hkeep (fun u hu p q Φ hΦ => hcomm u hu p q Φ hΦ) (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz`. Rewrite `h0` using `[map_sub, Pi.sub_apply, sub_eq_zero]`. Establish `htr : T0 (fun w => Φ₀ (w + u • (-y))) = fun w => T0 Φ₀ (w + u • (-y))`. Establish `h` using `hcomm u hu (-y) 0 Φ₀ hm₀`. Rewrite `h` using `[smul_zero, schr_trans', schr_trans']`.

Conclude with `h`. Establish `h2 : T0 Φ₂ y = (r y / R 0) * T0 Φ₀ p`. Rewrite using `[hΦ₂, map_smul, htr, Pi.smul_apply, smul_eq_mul, hyp]`. Use `show T0 Φ₁ y = tens (evI F) (⇑(Tf f)) r y`. Rewrite using `[h0, h2]`.

Use `show r y / R 0 * T0 Φ₀ p = (Tf f) (fun i => evI F (y i)) * r y`. Rewrite using `[hTf]`. Use `show r y / R 0 * T0 Φ₀ p = (R 0)⁻¹ * T0 Φ₀ p * r y`. Rewrite using `[div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.ArchFactorPair.exists_archOperator_pair :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ h ∈ UAt σ W (evI F), ∃ T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) f (T f) := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om hstd _ _ _ _ _ _ _ _ hweil h hh
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hweil
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), om (1, h) Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres (1, h) Φ hΦ
  have h1 : (1 : UA σ X.J) ∈ UAt σ X (evI F) := by
    intro u _
    simp [mat]
  have hcomm := comm_offI hweil (1, h) h1 hh
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_finiteWeight_complementary_archimedeanSchwartz (F := F) (Fin n × Fin d)
  have hB : ∀ f : SInf F (Fin n × Fin d), ∃ g : SInf F (Fin n × Fin d),
      ∀ t, g t = (R 0)⁻¹ * om (1, h) (tens (evI F) (⇑f) R) (liftI t) := by
    intro f
    obtain ⟨g, hg⟩ := GlobalTheory.T.exists_schwartz_archimedeanSlice_adelicSchwartz _ (Submodule.smul_mem _ (R 0)⁻¹ (hkeep _ (hR f).2))
    exact ⟨g, fun t => by rw [hg]; rfl⟩
  choose Tf hTf using hB
  have htens_add : ∀ f g : SInf F (Fin n × Fin d),
      tens (evI F) (⇑(f + g)) R = tens (evI F) (⇑f) R + tens (evI F) (⇑g) R := by
    intro f g; funext x; simp only [tens, SchwartzMap.add_apply, Pi.add_apply]; ring
  have htens_smul : ∀ (c : ℂ) (f : SInf F (Fin n × Fin d)),
      tens (evI F) (⇑(c • f)) R = c • tens (evI F) (⇑f) R := by
    intro c f; funext x; simp only [tens, SchwartzMap.smul_apply, Pi.smul_apply, smul_eq_mul]; ring
  let T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) :=
    { toFun := Tf
      map_add' := fun f g => by
        ext t
        rw [SchwartzMap.add_apply, hTf, hTf, hTf, htens_add, map_add, Pi.add_apply]; ring
      map_smul' := fun c f => by
        ext t
        rw [SchwartzMap.smul_apply, hTf, hTf, htens_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
          RingHom.id_apply]; ring }
  refine ⟨T, fun f r hr => ?_⟩
  funext y
  set T0 := om (1, h) with hT0
  set u : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) with hudef
  have hu : evI F u = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
    exact map_zero _
  set p : Fin n × Fin d → AF F := liftI (fun i => evI F (y i)) with hpdef
  have hyp : y + u • (-y) = p := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef, liftI, evI,
      RingEquiv.symm_apply_apply]
    refine Prod.ext ?_ ?_
    · show (y i).1 + 0 * (-(y i)).1 = (y i).1
      simp
    · show (y i).2 + 1 * (-(y i)).2 = 0
      rw [one_mul]
      exact add_neg_cancel ((y i).2)
  have hpat : At (evI F) p := by
    intro u' hu'
    have h0 : u'.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu')
    funext i
    refine Prod.ext ?_ ?_
    · show u'.1 * (p i).1 = 0
      rw [h0, zero_mul]
    · show u'.2 * (p i).2 = 0
      simp [hpdef, liftI]
  set Φ₀ := tens (evI F) (⇑f) R with hΦ₀
  set Φ₁ := tens (evI F) (⇑f) r with hΦ₁
  set Φ₂ : (Fin n × Fin d → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
  have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR f).2
  have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (GlobalTheory.SchwartzTranslation.schA_add_const _ _ hm₀)
  have hfz : ∀ z, At (evI F) z → (Φ₁ - Φ₂) (y + z) = 0 := by
    intro z hz
    have e1 : r (y + z) = r y := hr.1 y z hz
    have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
    have hpz : At (evI F) (p + z) := fun u' hu' => by
      rw [smul_add, hpat u' hu', hz u' hu', add_zero]
    have e3 : R (p + z) = R 0 := by simpa using (hR f).1 0 (p + z) hpz
    have e4 : (fun i => evI F ((y + z + u • (-y)) i)) = fun i => evI F ((y + z) i) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add', evI_mul', hu, zero_mul, add_zero]
    simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]
    rw [e4, e2, e3, e1]
    field_simp
    ring
  have h0 := GlobalTheory.T.heisenbergCommuting_operator_independent_of_archimedeanFibres ψ T0 hstd hkeep (fun u hu p q Φ hΦ => hcomm u hu p q Φ hΦ) (Φ₁ - Φ₂)
    (sub_mem hr.2 hm₂) y hfz
  rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
  have htr : T0 (fun w => Φ₀ (w + u • (-y))) = fun w => T0 Φ₀ (w + u • (-y)) := by
    have h := hcomm u hu (-y) 0 Φ₀ hm₀
    rw [smul_zero, schr_trans', schr_trans'] at h
    exact h
  have h2 : T0 Φ₂ y = (r y / R 0) * T0 Φ₀ p := by
    rw [hΦ₂, map_smul, htr, Pi.smul_apply, smul_eq_mul, hyp]
  show T0 Φ₁ y = tens (evI F) (⇑(Tf f)) r y
  rw [h0, h2]
  show r y / R 0 * T0 Φ₀ p = (Tf f) (fun i => evI F (y i)) * r y
  rw [hTf]
  show r y / R 0 * T0 Φ₀ p = (R 0)⁻¹ * T0 Φ₀ p * r y
  rw [div_eq_mul_inv]
  ring
