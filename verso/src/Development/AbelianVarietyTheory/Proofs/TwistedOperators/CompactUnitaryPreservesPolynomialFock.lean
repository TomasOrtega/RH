import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergCommutingOperatorBlindToArchimedeanFibStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzArchimedeanSliceAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteWeightComplementaryArchimedeanSchwar

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.FockCompactW

open GlobalTheory.RealLift

section Lift

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def liftI (t : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i), (0 : FiniteAdeleRing (𝓞 F) F)) : AF F)

end Lift

section Local

open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
The claim follows from `map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1`.
-/
theorem evI_add' (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

/- English proof (translation)
The claim follows from `map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1`.
-/
theorem evI_mul' (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

/- English proof (translation)
Establish `hW` using `GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw`. Use `set w := M.co.e.symm (p, q) with hw'`. Establish `he : M.co.e (u • w) = (u • p, u • q)`. Rewrite using `[LinearEquiv.map_smul, hw', LinearEquiv.apply_symm_apply, Prod.smul_mk]`. Establish `h1 : u • (mat x.1 - 1) = 0` using `hx1 u hu`.

Establish `h2 : u • (mat x.2 - 1) = 0` using `hx2 u hu`. Establish `e1 : mat x.1 * (u • w) = u • w`. Establish `: mat x.1 * (u • w) - u • w = (u • (mat x.1 - 1)) * w`. Rewrite using `[Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul, smul_sub]`. Rewrite `this` using `[h1, Matrix.zero_mul, sub_eq_zero]`.

Conclude with `this`. Establish `e2 : (u • w) * (mat x.2)ᵀ = u • w`. Establish `: (u • w) * (mat x.2)ᵀ - u • w = w * (u • (mat x.2 - 1))ᵀ`. Rewrite using `[Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one, smul_sub]`. Rewrite `this` using `[h2, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero]`.

Conclude with `this`. Establish `hact : GlobalTheory.WeilM.actAB (cA σ) x (u • w) = u • w`. Simplify using `only [GlobalTheory.WeilM.actAB]`. Use `e1` as an intermediate fact. Simplify using `only [mat] at this e2`.

Rewrite using `[this, e2]`. Establish `h3` using `hW.impl x (u • w) Φ hΦ`. Simplify using `only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h3`. Conclude with `h3`.
-/
theorem comm_offI {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ}
    {χX χW : Chr F E} {om : Rep σ X W} (hw : M.IsWeil ψ χX χW om) (x : UA σ X.J × UA σ W.J)
    (hx1 : x.1 ∈ UAt σ X (evI F)) (hx2 : x.2 ∈ UAt σ W (evI F))
    (u : AF F) (hu : evI F u = 0) (p q : Fin n × Fin d → AF F) (Φ : (Fin n × Fin d → AF F) → ℂ)
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d)) :
    om x (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (om x Φ) := by
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw
  set w := M.co.e.symm (p, q) with hw'
  have he : M.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw', LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h1 : u • (mat x.1 - 1) = 0 := hx1 u hu
  have h2 : u • (mat x.2 - 1) = 0 := hx2 u hu
  have e1 : mat x.1 * (u • w) = u • w := by
    have : mat x.1 * (u • w) - u • w = (u • (mat x.1 - 1)) * w := by
      rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul, smul_sub]
    rw [h1, Matrix.zero_mul, sub_eq_zero] at this
    exact this
  have e2 : (u • w) * (mat x.2)ᵀ = u • w := by
    have : (u • w) * (mat x.2)ᵀ - u • w = w * (u • (mat x.2 - 1))ᵀ := by
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.mul_sub, Matrix.mul_one, smul_sub]
    rw [h2, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
    exact this
  have hact : GlobalTheory.WeilM.actAB (cA σ) x (u • w) = u • w := by
    simp only [GlobalTheory.WeilM.actAB]
    have := e1
    simp only [mat] at this e2
    rw [this, e2]
  have h3 := hW.impl x (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h3
  exact h3

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `[GlobalTheory.WeilM.schr]`.
-/
theorem schr_trans' (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] (w : κ → AF F) (Φ : (κ → AF F) → ℂ) :
    GlobalTheory.WeilM.schr ψ (w, 0) Φ = fun y => Φ (y + w) := by
  funext y
  simp [GlobalTheory.WeilM.schr]

end Local

open scoped Classical in

/- English proof (translation)
Establish `hW` using `GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw`. Establish `hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), om x Φ ∈ GlobalTheory.WeilM.schA F _` using `fun Φ hΦ => hW.pres x Φ hΦ`. Establish `hcomm` using `comm_offI hw x hx1 hx2`. Take `⟨R, hR0, hR⟩` from `GlobalTheory.ArchRest.exists_rest_arch (F := F) (Fin n × Fin d)`. Establish `hB : ∀ f : SInf F (Fin n × Fin d), ∃ g : SInf F (Fin n × Fin d), ∀ t, g t = (R 0)⁻¹ * om x (tens (evI F) (⇑f) R) (liftI t)`.

Introduce `f`. Take `⟨g, hg⟩` from `GlobalTheory.ArchSlice.exists_schwartz_slice _ (Submodule.smul_mem _ (R 0)⁻¹ (hkeep _ (hR f).2))`. Conclude with `⟨g, fun t => by rw [hg]; rfl⟩`. Use `choose Tf hTf using hB`. Establish `htens_add : ∀ f g : SInf F (Fin n × Fin d), tens (evI F) (⇑(f + g)) R = tens (evI F) (⇑f) R + tens (evI F) (⇑g) R`.

Introduce `f g`. Use function extensionality and compare the values at `x`. Simplify using `only [tens, SchwartzMap.add_apply, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `htens_smul : ∀ (c : ℂ) (f : SInf F (Fin n × Fin d)), tens (evI F) (⇑(c • f)) R = c • tens (evI F) (⇑f) R`.

Introduce `c f`. Use function extensionality and compare the values at `x`. Simplify using `only [tens, SchwartzMap.smul_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Set `T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)` to `{ toFun := Tf map_add' := fun f g => by`.

Use extensionality with `t`. Rewrite using `[SchwartzMap.add_apply, hTf, hTf, hTf, htens_add, map_add, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `map_smul' := fun c f => by`. Use extensionality with `t`.

Rewrite using `[SchwartzMap.smul_apply, hTf, hTf, htens_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul, RingHom.id_apply]`. Use `ring }`. Use `⟨T, fun f r hr => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `y`. Use `set T0 := om x with hT0`.

Use `set u : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) with hudef`. Establish `hu : evI F u = 0` using `by show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0`. Conclude with `map_zero _`. Use `set p : Fin n × Fin d → AF F := liftI (fun i => evI F (y i)) with hpdef`. Establish `hyp : y + u • (-y) = p`.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef, liftI, evI, RingEquiv.symm_apply_apply]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show (y i).1 + 0 * (-(y i)).1 = (y i).1`. Simplify using the standard rewrite rules.

Use `show (y i).2 + 1 * (-(y i)).2 = 0`. Rewrite using `[one_mul]`. Conclude with `add_neg_cancel ((y i).2)`. Establish `hpat : At (evI F) p`. Introduce `u' hu'`.

Establish `h0 : u'.1 = 0` using `(InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu')`. Use function extensionality and compare the values at `i`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show u'.1 * (p i).1 = 0`. Rewrite using `[h0, zero_mul]`.

Use `show u'.2 * (p i).2 = 0`. Simplify using `[hpdef, liftI]`. Use `set Φ₀ := tens (evI F) (⇑f) R with hΦ₀`. Use `set Φ₁ := tens (evI F) (⇑f) r with hΦ₁`. Use `set Φ₂ : (Fin n × Fin d → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂`.

Establish `hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _` using `(hR f).2`. Establish `hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _` using `Submodule.smul_mem _ _ (GlobalTheory.SchwartzTranslation.schA_add_const _ _ hm₀)`. Establish `hfz : ∀ z, At (evI F) z → (Φ₁ - Φ₂) (y + z) = 0`. Introduce `z hz`. Establish `e1 : r (y + z) = r y` using `hr.1 y z hz`.

Establish `e2 : y + z + u • (-y) = p + z` using `by rw [← hyp]; abel`. Establish `hpz : At (evI F) (p + z)` using `fun u' hu' => by`. Rewrite using `[smul_add, hpat u' hu', hz u' hu', add_zero]`. Establish `e3 : R (p + z) = R 0` using `by simpa using (hR f).1 0 (p + z) hpz`. Establish `e4 : (fun i => evI F ((y + z + u • (-y)) i)) = fun i => evI F ((y + z) i)`.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add', evI_mul', hu, zero_mul, add_zero]`. Simplify using `only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]`. Rewrite using `[e4, e2, e3, e1]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `h0` using `GlobalTheory.T.heisenbergCommuting_operator_independent_of_archimedeanFibres ψ T0 hψ hkeep (fun u hu p q Φ hΦ => hcomm u hu p q Φ hΦ) (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz`. Rewrite `h0` using `[map_sub, Pi.sub_apply, sub_eq_zero]`. Establish `htr : T0 (fun w => Φ₀ (w + u • (-y))) = fun w => T0 Φ₀ (w + u • (-y))`. Establish `h` using `hcomm u hu (-y) 0 Φ₀ hm₀`.

Rewrite `h` using `[smul_zero, schr_trans', schr_trans']`. Conclude with `h`. Establish `h2 : T0 Φ₂ y = (r y / R 0) * T0 Φ₀ p`. Rewrite using `[hΦ₂, map_smul, htr, Pi.smul_apply, smul_eq_mul, hyp]`. Use `show T0 Φ₁ y = tens (evI F) (⇑(Tf f)) r y`.

Rewrite using `[h0, h2]`. Use `show r y / R 0 * T0 Φ₀ p = (Tf f) (fun i => evI F (y i)) * r y`. Rewrite using `[hTf]`. Use `show r y / R 0 * T0 Φ₀ p = (R 0)⁻¹ * T0 Φ₀ p * r y`. Rewrite using `[div_eq_mul_inv]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_op_of_UAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ}
    {χX χW : Chr F E} {om : Rep σ X W} (hψ : IsStd ψ) (hw : M.IsWeil ψ χX χW om) (x : UA σ X.J × UA σ W.J)
    (hx1 : x.1 ∈ UAt σ X (evI F)) (hx2 : x.2 ∈ UAt σ W (evI F)) :
    ∃ T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ f : SInf F (Fin n × Fin d),
      Acts (evI F) (om x) (⇑f) (⇑(T f)) := by
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), om x Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres x Φ hΦ
  have hcomm := comm_offI hw x hx1 hx2
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) (Fin n × Fin d)
  have hB : ∀ f : SInf F (Fin n × Fin d), ∃ g : SInf F (Fin n × Fin d),
      ∀ t, g t = (R 0)⁻¹ * om x (tens (evI F) (⇑f) R) (liftI t) := by
    intro f
    obtain ⟨g, hg⟩ := GlobalTheory.ArchSlice.exists_schwartz_slice _ (Submodule.smul_mem _ (R 0)⁻¹ (hkeep _ (hR f).2))
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
  set T0 := om x with hT0
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
  have h0 := GlobalTheory.T.heisenbergCommuting_operator_independent_of_archimedeanFibres ψ T0 hψ hkeep (fun u hu p q Φ hΦ => hcomm u hu p q Φ hΦ) (Φ₁ - Φ₂)
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

section Der

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

/- English proof (translation)
Introduce `u hu`. Rewrite using `[← Matrix.smul_mul, hz u hu, Matrix.zero_mul]`.
-/
theorem at_mul_right {m p q : Type} [Fintype p] {z : Matrix m p (AE F E)} (hz : At (evI F) z)
    (A : Matrix p q (AE F E)) : At (evI F) (z * A) := by
  intro u hu; rw [← Matrix.smul_mul, hz u hu, Matrix.zero_mul]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[Model.heisLine, Darboux.rho, schr]`.
-/
theorem heisLine_zero (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (AE F E)) (t : ℝ) :
    M.heisLine ψ u t 0 = 0 := by
  funext x
  simp [Model.heisLine, Darboux.rho, schr]

/- English proof (translation)
Introduce `g hg`. Use `h (fun x => g (fun i => (x i).2)) ⟨fun x z hz => ?_, Submodule.subset_span ⟨f, g, hg, rfl⟩⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `g (fun i => (x i + z i).2) = g (fun i => (x i).2)`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Express the relevant statement in the definitionally equal form `(x i).2 + (z i).2 = (x i).2`. Rewrite using `[fin_eq_zero_of_at hz, add_zero]`.
-/
theorem sa_of_acts {κ : Type} [Fintype κ] {T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ : SInf F κ}
    (h : Acts (evI F) T f f₁) : SA T f f₁ := by
  intro g hg
  refine h (fun x => g (fun i => (x i).2)) ⟨fun x z hz => ?_, Submodule.subset_span ⟨f, g, hg, rfl⟩⟩
  change g (fun i => (x i + z i).2) = g (fun i => (x i).2)
  congr 1
  funext i
  change (x i).2 + (z i).2 = (x i).2
  rw [fin_eq_zero_of_at hz, add_zero]

/- English proof (translation)
Establish `hS` using `IsUWeilPair.isUSplitting hw`. Introduce `r hr l hl`. Establish `h1` using `hD r hr _ (hS.adm (1, h) l hl)`. Simplify using `only [LinearMap.comp_apply] at h1`. Rewrite `h1` using `[sa_of_acts hf₁ r hr]`.

Use `h1.congr_of_eventuallyEq (.of_forall fun t => ?_)` and prove the remaining obligations. Establish `h2` using `hS.impl (1, h) (realAd F t • u) (pureA F f r) (Submodule.subset_span ⟨f, r, hr, rfl⟩)`. Establish `h3 : actAB (cA σ) ((1, h) : UA σ Y.J × UA σ W.J) (realAd F t • u) = realAd F t • (u * (mat h)ᵀ)`. Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin n) (Fin n) (AE F E)) * (realAd F t • u) * (mat h)ᵀ = _`. Rewrite using `[Matrix.one_mul, Matrix.smul_mul]`.

Rewrite `h2` using `[h3, sa_of_acts hf r hr]`. Conclude with `congrArg l h2.symm`.
-/
theorem sd_intertwine {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} {χ₁ χ₂ : Chr F E} {om : Rep σ Y W}
    (hw : M.IsWeil ψ χ₁ χ₂ om) (h : UA σ W.J) {f f₁ g g₁ : SInf F (Fin n × Fin d)}
    (hf : Acts (evI F) (om (1, h)) f g) (hf₁ : Acts (evI F) (om (1, h)) f₁ g₁) {u : Matrix (Fin n) (Fin d) (AE F E)}
    (hD : SD (M.heisLine ψ u) f f₁) : SD (M.heisLine ψ (u * (mat h)ᵀ)) g g₁ := by
  have hS := IsUWeilPair.isUSplitting hw
  intro r hr l hl
  have h1 := hD r hr _ (hS.adm (1, h) l hl)
  simp only [LinearMap.comp_apply] at h1
  rw [sa_of_acts hf₁ r hr] at h1
  refine h1.congr_of_eventuallyEq (.of_forall fun t => ?_)
  have h2 := hS.impl (1, h) (realAd F t • u) (pureA F f r) (Submodule.subset_span ⟨f, r, hr, rfl⟩)
  have h3 : actAB (cA σ) ((1, h) : UA σ Y.J × UA σ W.J) (realAd F t • u) = realAd F t • (u * (mat h)ᵀ) := by
    change (1 : Matrix (Fin n) (Fin n) (AE F E)) * (realAd F t • u) * (mat h)ᵀ = _
    rw [Matrix.one_mul, Matrix.smul_mul]
  rw [h3, sa_of_acts hf r hr] at h2
  exact congrArg l h2.symm

end Der

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ _ n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ hw τ _ _ k hk f hf`. Establish `h1 : (1 : UA σ X.J) ∈ UAt σ X (evI F)`. Introduce `u _`. Simplify using `[mat]`. Take `⟨A, hA⟩` from `exists_op_of_UAt hψ hw (1, k) h1 hk.1`.

Take `⟨D, hD⟩` from `GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ ψ _ _ M.co hψ`. Establish `hL` using `actsLaws F (Fin n × Fin d)`. Establish `hSD : ∀ u, At (evI F) u → ∀ φ, SD (M.heisLine ψ u) φ (D u φ)` using `fun u hu φ => (hD u hu φ).1`. Establish `hAD : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) φ (D u φ)` using `fun u hu φ => (hL φ _ φ).1 _ (heisLine_zero M ψ u) (hSD u hu φ)`. Establish `hint : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ (u * (mat k)ᵀ)) (A φ) (A (D u φ))` using `fun u hu φ => (hL _ _ φ).1 _ (heisLine_zero M ψ _) (sd_intertwine hw k (hA φ) (hA _) (hSD u hu φ))`.

Establish `hkk : (mat k⁻¹)ᵀ * (mat k)ᵀ = 1`. Rewrite using `[← Matrix.transpose_mul]`. Express the relevant statement in the definitionally equal form `(mat (k * k⁻¹))ᵀ = 1`. Rewrite using `[mul_inv_cancel]`. Conclude with `Matrix.transpose_one`.

Establish `hcan : ∀ u : Matrix (Fin n) (Fin d) (AE F E), u * (mat k⁻¹)ᵀ * (mat k)ᵀ = u` using `fun u => by`. Rewrite using `[Matrix.mul_assoc, hkk, Matrix.mul_one]`. Establish `hle : M.Pol ψ τ ≤ (M.Pol ψ τ).comap A`. Use `sInf_le ⟨fun f₀ hf₀ => ?_, fun u hu φ hφ φ₁ hφ₁ => ?_⟩` and prove the remaining obligations. Use `Submodule.mem_sInf.2 fun N hN => hN.1 _ ?_` and prove the remaining obligations.

Take `⟨ε, hε⟩` from `hf₀`. Use `⟨ε, fun u u' hu hu' huu g g' hg hg' => ?_⟩` and prove the remaining obligations. Establish `hv` using `at_mul_right hu (mat k⁻¹)ᵀ`. Establish `hv'` using `at_mul_right hu' (mat k⁻¹)ᵀ`. Establish `h1` using `hint _ hv f₀`.

Establish `h2` using `hint _ hv' f₀`. Rewrite `h1`, `h2` using `[hcan]`. Establish `e1` using `(hL _ _ _).2.2.1 _ hg h1`. Establish `e2` using `(hL _ _ _).2.2.1 _ hg' h2`. Establish `key` using `hε _ _ hv hv' (fun w => ?_) _ _ (hAD _ hv f₀) (hAD _ hv' f₀)`.

Rewrite using `[e1, e2, key, map_smul]`. Establish `hm : (mat k⁻¹).map (piInf (τ w)) * (mat k).map (piInf (τ w)) = 1`. Rewrite using `[← Matrix.map_mul]`. Express the relevant statement in the definitionally equal form `(mat (k⁻¹ * k)).map _ = 1`. Rewrite using `[inv_mul_cancel]`.

Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `hm' : (mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w)) = 1` using `mul_eq_one_comm.1 hm`. Establish `hc : (mat k⁻¹).map (piInf (τ w)) * W.θ w = W.θ w * (mat k⁻¹).map (piInf (τ w))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.map_mul, Matrix.map_mul, huu w, Matrix.transpose_map, Matrix.smul_mul]`.

Use `congr 1`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.transpose_mul, ← Matrix.transpose_mul, hc]`. Establish `e : φ₁ = D u φ` using `(hL _ _ _).2.2.1 _ hφ₁ (hAD u hu φ)`. Rewrite using `[e]`.

Conclude with `Submodule.mem_sInf.2 fun N hN => hN.2 _ (at_mul_right hu _) _ (Submodule.mem_sInf.1 hφ N hN) _ (hint u hu φ)`. Use `⟨⟨A f, hA f⟩, fun f₁ hf₁ => ?_⟩` and prove the remaining obligations. Rewrite using `[(hL f f₁ (A f)).2.2.2.1 _ hf₁ (hA f)]`. Conclude with `hle hf`.
-/
theorem pol_stable_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ k ∈ KInf σ W τ, ∀ f ∈ M.Pol ψ τ,
          (∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁) ∧
          ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ → f₁ ∈ M.Pol ψ τ := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ hw τ _ _ k hk f hf
  have h1 : (1 : UA σ X.J) ∈ UAt σ X (evI F) := by
    intro u _
    simp [mat]
  obtain ⟨A, hA⟩ := exists_op_of_UAt hψ hw (1, k) h1 hk.1
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ ψ _ _ M.co hψ
  have hL := actsLaws F (Fin n × Fin d)
  have hSD : ∀ u, At (evI F) u → ∀ φ, SD (M.heisLine ψ u) φ (D u φ) := fun u hu φ => (hD u hu φ).1
  have hAD : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) φ (D u φ) :=
    fun u hu φ => (hL φ _ φ).1 _ (heisLine_zero M ψ u) (hSD u hu φ)
  have hint : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ (u * (mat k)ᵀ)) (A φ) (A (D u φ)) :=
    fun u hu φ => (hL _ _ φ).1 _ (heisLine_zero M ψ _) (sd_intertwine hw k (hA φ) (hA _) (hSD u hu φ))
  have hkk : (mat k⁻¹)ᵀ * (mat k)ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    change (mat (k * k⁻¹))ᵀ = 1
    rw [mul_inv_cancel]
    exact Matrix.transpose_one
  have hcan : ∀ u : Matrix (Fin n) (Fin d) (AE F E), u * (mat k⁻¹)ᵀ * (mat k)ᵀ = u := fun u => by
    rw [Matrix.mul_assoc, hkk, Matrix.mul_one]
  have hle : M.Pol ψ τ ≤ (M.Pol ψ τ).comap A := by
    refine sInf_le ⟨fun f₀ hf₀ => ?_, fun u hu φ hφ φ₁ hφ₁ => ?_⟩
    · refine Submodule.mem_sInf.2 fun N hN => hN.1 _ ?_
      obtain ⟨ε, hε⟩ := hf₀
      refine ⟨ε, fun u u' hu hu' huu g g' hg hg' => ?_⟩
      have hv := at_mul_right hu (mat k⁻¹)ᵀ
      have hv' := at_mul_right hu' (mat k⁻¹)ᵀ
      have h1 := hint _ hv f₀
      have h2 := hint _ hv' f₀
      rw [hcan] at h1 h2
      have e1 := (hL _ _ _).2.2.1 _ hg h1
      have e2 := (hL _ _ _).2.2.1 _ hg' h2
      have key := hε _ _ hv hv' (fun w => ?_) _ _ (hAD _ hv f₀) (hAD _ hv' f₀)
      · rw [e1, e2, key, map_smul]
      · have hm : (mat k⁻¹).map (piInf (τ w)) * (mat k).map (piInf (τ w)) = 1 := by
          rw [← Matrix.map_mul]
          change (mat (k⁻¹ * k)).map _ = 1
          rw [inv_mul_cancel]
          exact Matrix.map_one _ (map_zero _) (map_one _)
        have hm' : (mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w)) = 1 := mul_eq_one_comm.1 hm
        have hc : (mat k⁻¹).map (piInf (τ w)) * W.θ w = W.θ w * (mat k⁻¹).map (piInf (τ w)) := by
          calc _ = (mat k⁻¹).map (piInf (τ w)) * W.θ w *
                ((mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w))) := by rw [hm', Matrix.mul_one]
            _ = (mat k⁻¹).map (piInf (τ w)) * (W.θ w * (mat k).map (piInf (τ w))) *
                (mat k⁻¹).map (piInf (τ w)) := by simp only [Matrix.mul_assoc]
            _ = _ := by rw [← (hk.2 w).eq, ← Matrix.mul_assoc, hm, Matrix.one_mul]
        rw [Matrix.map_mul, Matrix.map_mul, huu w, Matrix.transpose_map, Matrix.smul_mul]
        congr 1
        simp only [Matrix.mul_assoc]
        rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, hc]
    · have e : φ₁ = D u φ := (hL _ _ _).2.2.1 _ hφ₁ (hAD u hu φ)
      rw [e]
      exact Submodule.mem_sInf.2 fun N hN =>
        hN.2 _ (at_mul_right hu _) _ (Submodule.mem_sInf.1 hφ N hN) _ (hint u hu φ)
  refine ⟨⟨A f, hA f⟩, fun f₁ hf₁ => ?_⟩
  rw [(hL f f₁ (A f)).2.2.2.1 _ hf₁ (hA f)]
  exact hle hf

end GlobalTheory.FockCompactW

end
