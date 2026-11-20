import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCRadSpSmooth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferKAsm

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSTr

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def hsL : (Wq →L[ℂ] Wp) →ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) where
  toFun := B.hsVec
  map_add' := VLem.hsV_add
  map_smul' := VLem.hsV_smul

/- English proof (translation)
The claim follows from `map_sum (hsL (Wp := Wp) (Wq := Wq)) f s`.
-/
theorem hsVec_sum {ι : Type} (s : Finset ι) (f : ι → (Wq →L[ℂ] Wp)) :
    B.hsVec (∑ i ∈ s, f i) = ∑ i ∈ s, B.hsVec (f i) := map_sum (hsL (Wp := Wp) (Wq := Wq)) f s

/- English proof (translation)
Introduce `p hp`. Use extensionality with `v`. Simplify using `only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, map_sum]`. Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Establish `h` using `congrArg (fun L : Wq →L[ℂ] Wp => L v) (hX ρ p hp)`.

Simplify using `only [ContinuousLinearMap.comp_apply] at h`. Simplify using `only [ContinuousLinearMap.smul_apply, map_smul, h]`.
-/
theorem fib_sum_smul (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (ζ : ℂ) (a : M.Ty P → ℂ)
    (X : M.Ty P → (Wq →L[ℂ] Wp)) (hX : ∀ ρ, X ρ ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ) :
    ∑ ρ, a ρ • X ρ ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ := by
  intro p hp
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have h := congrArg (fun L : Wq →L[ℂ] Wp => L v) (hX ρ p hp)
  simp only [ContinuousLinearMap.comp_apply] at h
  simp only [ContinuousLinearMap.smul_apply, map_smul, h]

/- English proof (translation)
Unfold `wR`. Conclude with `Real.sqrt_pos.2 (pow_pos (sub_pos.2 hζ) _)`.
-/
theorem wR_pos (P : M.Par) {ζ : ℂ} (hζ : P.TT < Complex.normSq ζ) : 0 < wR P.k P.TT ζ := by
  unfold wR
  exact Real.sqrt_pos.2 (pow_pos (sub_pos.2 hζ) _)

/- English proof (translation)
Establish `h` using `radial_space_smoothness Wp Wq P Bs hpl hk e he Φ ρ`. Use `show (MA.toSm P (rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ) : MA.Qp P.r P.TT → ℂ) q = _`. Rewrite using `[Gauge.toSm_of_mem P h]`.
-/
theorem trR_apply (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) [FiniteDimensional ℂ Wp]
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (he : IsFrameB P Bs e) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ) q = rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q := by
  have h := radial_space_smoothness Wp Wq P Bs hpl hk e he Φ ρ
  show (MA.toSm P (rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ) : MA.Qp P.r P.TT → ℂ) q = _
  rw [Gauge.toSm_of_mem P h]

/- English proof (translation)
Assemble the required witnesses or components as `⟨hpl.1.k_pos, hpl.2.1, hpl.2.2.1, by rw [hpl.2.2.2.1]; exact hpl.1.T_pos, by rw [hpl.2.2.2.2.1]; exact hpl.1.T'_pos, Bs.sec, hpl.2.2.2.2.2.1.2.1, hpl.2.2.2.2.2.2.2.1, hpl.2.2.2.2.2.1.2.2.1, hpl.2.2.2.2.2.2.2.2.1⟩`.
-/
theorem radBase (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') :
    NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' :=
  ⟨hpl.1.k_pos, hpl.2.1, hpl.2.2.1, by rw [hpl.2.2.2.1]; exact hpl.1.T_pos,
    by rw [hpl.2.2.2.2.1]; exact hpl.1.T'_pos, Bs.sec, hpl.2.2.2.2.2.1.2.1, hpl.2.2.2.2.2.2.2.1,
    hpl.2.2.2.2.2.1.2.2.1, hpl.2.2.2.2.2.2.2.2.1⟩

/- English proof (translation)
Rewrite using `[hpl.2.2.2.1, hpl.2.2.2.2.1]`. Both sides reduce to the same expression.
-/
theorem tz_eq (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') :
    Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by
  rw [hpl.2.2.2.1, hpl.2.2.2.2.1]
  rfl

/- English proof (translation)
Use `show (x.1 ∈ OmX P.r ∧ _) ↔ ((∀ l, x.1 l ≠ 0) ∧ _)`. Rewrite using `[tz_eq P Bs hpl]`. Both sides reduce to the same expression.
-/
theorem qr_iff (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (x : (Fin P.r → ℂ) × ℂ) : x ∈ NF.QR P.k P.r Bs.z Bs.z' ↔ x ∈ MA.Qset P.r P.TT := by
  show (x.1 ∈ OmX P.r ∧ _) ↔ ((∀ l, x.1 l ≠ 0) ∧ _)
  rw [tz_eq P Bs hpl]
  rfl

/- English proof (translation)
Set `g : (Fin P.r → ℂ) × ℂ → (Wq →L[ℂ] Wp)` to `fun x => ∑ ρ, ((((wR P.k P.TT x.2)⁻¹ : ℝ) : ℂ) * MA.ext (F ρ : MA.Qp P.r P.TT → ℂ) x) • e ρ x.2`. Set `φ` to `(NF.QR P.k P.r Bs.z Bs.z').indicator g`. Establish `hQR : NF.QR P.k P.r Bs.z Bs.z' = MA.Qset P.r P.TT` using `Set.ext (qr_iff P Bs hpl)`. Establish `hg : ContDiffOn ℝ ∞ g (MA.Qset P.r P.TT)`. Use `ContDiffOn.sum fun ρ _ => ?_` and prove the remaining obligations.

Establish `hw : ContDiffOn ℝ ∞ (fun x : MA.E P.r => (((wR P.k P.TT x.2)⁻¹ : ℝ) : ℂ)) (MA.Qset P.r P.TT)`. Use `Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_ofReal ?_` and prove the remaining obligations. Use `ContDiffOn.inv ?_ fun x hx => (wR_pos P hx.2).ne'` and prove the remaining obligations. Unfold `wR`. Use `(((Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_normSq.comp contDiff_snd).sub contDiff_const).pow _).contDiffOn.sqrt fun x hx => ?_` and prove the remaining obligations.

Establish `h2 : P.TT < Complex.normSq x.2` using `hx.2`. Conclude with `(pow_pos (show (0 : ℝ) < Complex.normSq x.2 - P.TT by linarith) _).ne'`. Establish `hF : ContDiffOn ℝ ∞ (MA.ext (F ρ : MA.Qp P.r P.TT → ℂ)) (MA.Qset P.r P.TT)` using `(F ρ).2`. Establish `he' : ContDiffOn ℝ ∞ (fun x : MA.E P.r => e ρ x.2) (MA.Qset P.r P.TT)` using `(he.1 ρ).comp contDiff_snd.contDiffOn fun x hx => hx.2`. Conclude with `(hw.mul hF).smul he'`.

Establish `hφ : φ ∈ NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π'`. Use `⟨?_, fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[hQR]`. Conclude with `hg.congr fun x hx => by simp only [φ, hQR, Set.indicator_of_mem hx]`. Simplify using `only [φ, Set.indicator_of_mem hx]`.

Establish `hx' : P.TT < Complex.normSq x.2` using `((qr_iff P Bs hpl x).1 hx).2`. Conclude with `fib_sum_smul P Bs x.2 _ _ fun ρ => (he.2 x.2 hx').1 ρ`. Simplify using `[φ, Set.indicator_of_notMem hx]`. Take `⟨Φ, hΦ, hrad⟩` from `Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' (radBase P Bs hpl) φ hφ`. Establish `hval : ∀ q : MA.Qp P.r P.TT, Φ q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2) = ∑ ρ, ((((wR P.k P.TT q.1.2)⁻¹ : ℝ) : ℂ) * (F ρ : MA.Qp P.r P.TT → ℂ) q) • e ρ q.1.2`.

Introduce `q`. Establish `hq : q.1 ∈ NF.QR P.k P.r Bs.z Bs.z'` using `(qr_iff P Bs hpl q.1).2 q.2`. Establish `h` using `congrFun hrad q.1`. Simplify using `only [NF.radR, Set.indicator_of_mem hq, φ] at h`. Rewrite using `[h]`.

Simplify using `only [g]`. Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Use `congr 2`. Simplify using `[MA.ext, q.2]`. Use `⟨⟨Φ, hΦ⟩, ?_, hval⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `ρ`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `q`. Rewrite using `[trR_apply P Bs hpl hk e he]`. Simplify using `only [rawR]`.

Rewrite using `[hval q, hsVec_sum, inner_sum]`. Establish `hζ : P.TT < Complex.normSq q.1.2` using `q.2.2`. Establish `horth` using `(he.2 q.1.2 hζ).2.1`. Simplify using `only [VLem.hsV_smul, inner_smul_right, horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Establish `hw : ((wR P.k P.TT q.1.2 : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (wR_pos P hζ).ne'`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_tr (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) [FiniteDimensional ℂ Wp]
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (he : IsFrameB P Bs e) (F : M.Ty P → MA.SmQ P.r P.TT) :
    ∃ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', trR P Bs e Φ = F ∧
      ∀ q : MA.Qp P.r P.TT, (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2) =
        ∑ ρ, ((((wR P.k P.TT q.1.2)⁻¹ : ℝ) : ℂ) * (F ρ : MA.Qp P.r P.TT → ℂ) q) • e ρ q.1.2 := by
  classical
  let g : (Fin P.r → ℂ) × ℂ → (Wq →L[ℂ] Wp) := fun x =>
    ∑ ρ, ((((wR P.k P.TT x.2)⁻¹ : ℝ) : ℂ) * MA.ext (F ρ : MA.Qp P.r P.TT → ℂ) x) • e ρ x.2
  let φ := (NF.QR P.k P.r Bs.z Bs.z').indicator g
  have hQR : NF.QR P.k P.r Bs.z Bs.z' = MA.Qset P.r P.TT := Set.ext (qr_iff P Bs hpl)
  have hg : ContDiffOn ℝ ∞ g (MA.Qset P.r P.TT) := by
    refine ContDiffOn.sum fun ρ _ => ?_
    have hw : ContDiffOn ℝ ∞ (fun x : MA.E P.r => (((wR P.k P.TT x.2)⁻¹ : ℝ) : ℂ)) (MA.Qset P.r P.TT) := by
      refine Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_ofReal ?_
      refine ContDiffOn.inv ?_ fun x hx => (wR_pos P hx.2).ne'
      unfold wR
      refine (((Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_normSq.comp contDiff_snd).sub contDiff_const).pow _).contDiffOn.sqrt
        fun x hx => ?_
      have h2 : P.TT < Complex.normSq x.2 := hx.2
      exact (pow_pos (show (0 : ℝ) < Complex.normSq x.2 - P.TT by linarith) _).ne'
    have hF : ContDiffOn ℝ ∞ (MA.ext (F ρ : MA.Qp P.r P.TT → ℂ)) (MA.Qset P.r P.TT) := (F ρ).2
    have he' : ContDiffOn ℝ ∞ (fun x : MA.E P.r => e ρ x.2) (MA.Qset P.r P.TT) :=
      (he.1 ρ).comp contDiff_snd.contDiffOn fun x hx => hx.2
    exact (hw.mul hF).smul he'
  have hφ : φ ∈ NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    refine ⟨?_, fun x hx => ?_, fun x hx => ?_⟩
    · rw [hQR]
      exact hg.congr fun x hx => by simp only [φ, hQR, Set.indicator_of_mem hx]
    · simp only [φ, Set.indicator_of_mem hx]
      have hx' : P.TT < Complex.normSq x.2 := ((qr_iff P Bs hpl x).1 hx).2
      exact fib_sum_smul P Bs x.2 _ _ fun ρ => (he.2 x.2 hx').1 ρ
    · simp [φ, Set.indicator_of_notMem hx]
  obtain ⟨Φ, hΦ, hrad⟩ := Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π'
    (radBase P Bs hpl) φ hφ
  have hval : ∀ q : MA.Qp P.r P.TT, Φ q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2) =
        ∑ ρ, ((((wR P.k P.TT q.1.2)⁻¹ : ℝ) : ℂ) * (F ρ : MA.Qp P.r P.TT → ℂ) q) • e ρ q.1.2 := by
    intro q
    have hq : q.1 ∈ NF.QR P.k P.r Bs.z Bs.z' := (qr_iff P Bs hpl q.1).2 q.2
    have h := congrFun hrad q.1
    simp only [NF.radR, Set.indicator_of_mem hq, φ] at h
    rw [h]
    simp only [g]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    congr 2
    simp [MA.ext, q.2]
  refine ⟨⟨Φ, hΦ⟩, ?_, hval⟩
  funext ρ
  apply Subtype.ext
  funext q
  rw [trR_apply P Bs hpl hk e he]
  simp only [rawR]
  rw [hval q, hsVec_sum, inner_sum]
  have hζ : P.TT < Complex.normSq q.1.2 := q.2.2
  have horth := (he.2 q.1.2 hζ).2.1
  simp only [VLem.hsV_smul, inner_smul_right, horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  have hw : ((wR P.k P.TT q.1.2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (wR_pos P hζ).ne'
  push_cast
  field_simp

/- English proof (translation)
Establish `hRB` using `radBase P Bs hpl`. Apply `Subtype.ext` to reduce the goal to its premises. Use `Formalism.FourierDecayAlt.P.radical_reduction_injective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ Φ.2 _ Ψ.2 ?_` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : x ∈ NF.QR P.k P.r Bs.z Bs.z'`.

Establish `hxQ : x ∈ MA.Qset P.r P.TT` using `(qr_iff P Bs hpl x).1 hx`. Set `q : MA.Qp P.r P.TT` to `⟨x, hxQ⟩`. Establish `hζ : P.TT < Complex.normSq x.2` using `hxQ.2`. Simplify using `only [NF.radR, Set.indicator_of_mem hx]`. Establish `hmΦ` using `(Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ Φ.2).2.1 x hx`.

Establish `hmΨ` using `(Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ Ψ.2).2.1 x hx`. Simplify using `only [NF.radR, Set.indicator_of_mem hx] at hmΦ hmΨ`. Rewrite using `[(he.2 x.2 hζ).2.2 _ hmΦ, (he.2 x.2 hζ).2.2 _ hmΨ]`. Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Use `congr 1`.

Establish `h1` using `trR_apply P Bs hpl hk e he Φ ρ q`. Establish `h2` using `trR_apply P Bs hpl hk e he Ψ ρ q`. Rewrite `h1` using `[h]`. Rewrite `h2` using `[h1]`. Simplify using `only [rawR, q] at h2`.

Establish `hw : ((wR P.k P.TT x.2 : ℝ) : ℂ) ≠ 0`. Conclude with `(wR_pos P hζ).ne'` after adjusting the coercions. Conclude with `mul_left_cancel₀ hw h2`. Simplify using `[NF.radR, Set.indicator_of_notMem hx]`.
-/
theorem trR_inj (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) [FiniteDimensional ℂ Wp]
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (he : IsFrameB P Bs e) {Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'} (h : trR P Bs e Φ = trR P Bs e Ψ) :
    Φ = Ψ := by
  have hRB := radBase P Bs hpl
  apply Subtype.ext
  refine Formalism.FourierDecayAlt.P.radical_reduction_injective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ Φ.2 _ Ψ.2 ?_
  funext x
  by_cases hx : x ∈ NF.QR P.k P.r Bs.z Bs.z'
  · have hxQ : x ∈ MA.Qset P.r P.TT := (qr_iff P Bs hpl x).1 hx
    let q : MA.Qp P.r P.TT := ⟨x, hxQ⟩
    have hζ : P.TT < Complex.normSq x.2 := hxQ.2
    simp only [NF.radR, Set.indicator_of_mem hx]
    have hmΦ := (Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ Φ.2).2.1 x hx
    have hmΨ := (Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ Ψ.2).2.1 x hx
    simp only [NF.radR, Set.indicator_of_mem hx] at hmΦ hmΨ
    rw [(he.2 x.2 hζ).2.2 _ hmΦ, (he.2 x.2 hζ).2.2 _ hmΨ]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    congr 1
    have h1 := trR_apply P Bs hpl hk e he Φ ρ q
    have h2 := trR_apply P Bs hpl hk e he Ψ ρ q
    rw [h] at h1
    rw [h1] at h2
    simp only [rawR, q] at h2
    have hw : ((wR P.k P.TT x.2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (wR_pos P hζ).ne'
    exact mul_left_cancel₀ hw h2
  · simp [NF.radR, Set.indicator_of_notMem hx]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSTr
