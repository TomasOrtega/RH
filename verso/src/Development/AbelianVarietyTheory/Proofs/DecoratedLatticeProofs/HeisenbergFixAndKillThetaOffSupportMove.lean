import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTranslateOrthogonalOfSupportMovedOff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfSep

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.zero_apply]`. Rewrite using `[← hy i j, map_mul, hb, zero_mul]`.
-/
theorem map_infPart_eq_zero {D : D7} {S T : HSp D} {b : AE D} (hb : infPart D b = 0) {y : WO S T}
    (hy : IsHalf b y) : y.map (infPart D) = 0 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.zero_apply]
  rw [← hy i j, map_mul, hb, zero_mul]

/- English proof (translation)
Introduce `D ψ S T hψ ΛS ΛT hS hT Z e he f₀ Φ f hΦ hth g hsupp`. Take `⟨⟨Tm, hTm⟩, hall⟩` from `hth`. Establish `hfT : f = Tm Φ` using `hall Tm hTm`. Establish `ho` using `GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he`. Establish `hinfc : infPart D (cA D e) = 0` using `ho.conj.infPart_eq`.

Take `⟨k, hk, hinv, hsup⟩` from `hΦ.2`. Take `⟨M, hM, hMact⟩` from `(GlobalTheory.LatLevel.level_of_generators D S T ΛS ΛT hS hT (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT)).2 g 1`. Use `set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛ`. Use `set N : ℕ := M * k with hN`. Establish `hNpos : 0 < N` using `Nat.mul_pos hM hk`.

Set `Ψ : WO S T → ℂ` to `fun u => if ∃ t, Φ t ≠ 0 ∧ N • t = u then 1 else 0`. Establish `hNt : ∀ t, Φ t ≠ 0 → N • t ∈ Λ` using `fun t ht => by`. Rewrite using `[hN, mul_smul]`. Conclude with `Λ.nsmul_mem (hsup t ht) M`. Establish `hΨ : IsSBHalf e Λ Ψ`.

Use `⟨fun u hu => ?_, N * k, Nat.mul_pos hNpos hk, fun v hv hvh u => ?_, fun u hu => ?_⟩` and prove the remaining obligations. Establish `: ∃ t, Φ t ≠ 0 ∧ N • t = u`. Assume the negation of the conclusion as `h`. Conclude with `hu (if_neg h)`. Take `⟨t, ht, rfl⟩` from `this`.

Conclude with `GlobalTheory.ThetaOrth.isHalf_nsmul (hΦ.1 t ht) N`. Establish `key : (∃ t, Φ t ≠ 0 ∧ N • t = u + (N * k) • v) ↔ ∃ t, Φ t ≠ 0 ∧ N • t = u`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, h⟩`. Use `⟨t + k • (-v), by rwa [hinv (-v) (Λ.neg_mem hv) (GlobalTheory.ThetaOrth.isHalf_neg hvh) t], ?_⟩` and prove the remaining obligations.

Conclude with `GlobalTheory.ThetaOrth.nsmul_add_neg N k t u v h`. Introduce and unpack `⟨t, ht, rfl⟩`. Use `⟨t + k • v, by rwa [hinv v hv hvh t], ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.ThetaOrth.nsmul_add_mul N k t v`. Use `show (if _ then _ else _) = (if _ then _ else _)`.

Simplify using `only [key]`. Establish `: ∃ t, Φ t ≠ 0 ∧ N • t = u`. Assume the negation of the conclusion as `h`. Conclude with `hu (if_neg h)`. Take `⟨t, ht, rfl⟩` from `this`.

Conclude with `Λ.nsmul_mem (hNt t ht) _`. Establish `hspan` using `(GlobalTheory.PlaceTensor.halfWaves_span D ψ S T ΛS ΛT hψ hS hT e ho.idem he.2 ho.infPart_eq).2 Ψ hΨ`. Take `⟨q, hq, hqΨ⟩` from `GlobalTheory.ThetaOrth.exists_char_of_wave N hspan`. Establish `hq1 : ∀ t, Φ t ≠ 0 → q t = 1` using `fun t ht => by`. Rewrite using `[← hqΨ t (hΦ.1 t ht) (hNt t ht)]`.

Conclude with `if_pos ⟨t, ht, rfl⟩`. Establish `hq0 : ∀ t, Φ t ≠ 0 → q (actO S T g 1 t) = 0` using `fun t ht => by`. Establish `h1 : N • actO S T g 1 t ∈ Λ`. Use `hMact (k • t) (hsup t ht)` as an intermediate fact. Establish `e : actO S T g 1 (k • t) = k • actO S T g 1 t` using `map_nsmul (GlobalTheory.LatLevel.actHom S T g 1) k t`.

Rewrite `this` using `[e, ← mul_smul]`. Then use the resulting hypothesis. Rewrite using `[← hqΨ _ (GlobalTheory.SplitHecke.isHalf_actO _ _ (hΦ.1 t ht)) h1]`. Use `if_neg ?_` and prove the remaining obligations. Introduce and unpack `⟨t', ht', h⟩`. Establish `: t' = actO S T g 1 t` using `GlobalTheory.ThetaOrth.nsmul_inj hNpos h`.

Conclude with `ht' (this ▸ hsupp t ht)`. Take `⟨n, a, yy, hqs⟩` from `(Submodule.mem_span_set' (R := ℂ)).1 hq`. Use `choose y hy hyq using fun i => (yy i).2`. Establish `hqt : ∀ t, q t = ∑ i, a i * ψ (symplO S T t (y i))` using `fun t => by`. Rewrite using `[← hqs, Finset.sum_apply]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, hyq i, smul_eq_mul]`. Use `set w : Fin n → WO S T := fun i => actO S T g⁻¹ 1 (-(y i)) with hw`. Establish `hwh : ∀ i, IsHalf (cA D e) (w i)` using `fun i => GlobalTheory.SplitHecke.isHalf_actO _ _ (GlobalTheory.ThetaOrth.isHalf_neg (hy i))`. Establish `hact : ∀ i, actO S T g 1 (w i) = -(y i)` using `fun i => by`.

Use `GlobalTheory.AdelicLatMove.actO_actO_inv S T g 1 (-(y i))` as an intermediate fact. Rewrite `this` using `[inv_one]`. Then use the resulting hypothesis. Use `⟨n, a, y, fun i => ⟨map_infPart_eq_zero hinfc (hy i), map_infPart_eq_zero hinfc (hwh i)⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `e1 : (fun t => q t * Φ t) = Φ`. Use function extensionality and compare the values at `t`.

Distinguish the cases in `h : Φ t = 0`. Rewrite using `[h, mul_zero]`. Rewrite using `[hq1 t h, one_mul]`. Establish `e2 : (fun t => q t * Φ t) = ∑ i, a i • fun t => ψ (symplO S T t (y i)) * Φ t`. Use function extensionality and compare the values at `t`.

Rewrite using `[hqt, Finset.sum_mul, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul, mul_assoc]`. Establish `e3` using `congrArg Tm e2`. Rewrite `e3` using `[e1, map_sum, ← hfT]`.

Use `(Finset.sum_congr rfl fun i _ => ?_).trans e3.symm` and prove the remaining obligations. Rewrite using `[map_smul, hTm.modul Φ hΦ (y i) (hy i), ← hfT]`. Establish `e1 : (fun t => conj (q (actO S T g 1 t)) * Φ t) = 0`. Use function extensionality and compare the values at `t`. Distinguish the cases in `h : Φ t = 0`.

Simplify using `[h]`. Simplify using `[hq0 t h]`. Establish `e2 : (fun t => conj (q (actO S T g 1 t)) * Φ t) = ∑ i, conj (a i) • fun t => ψ (symplO S T t (w i)) * Φ t`. Use function extensionality and compare the values at `t`. Rewrite using `[hqt, map_sum, Finset.sum_mul, Finset.sum_apply]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul, map_mul, GlobalTheory.ThetaOrth.conj_psi hψ, ← GlobalTheory.ThetaOrth.symplO_neg_right, ← hact i, GlobalTheory.SymplOInv.symplO_actO D S T g 1 t (w i), mul_assoc]`. Establish `e3` using `congrArg Tm e2`. Rewrite `e3` using `[e1, map_zero, map_sum]`. Rewrite using `[e3]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hfT, hTm.modul Φ hΦ (w i) (hwh i)]`.
-/
theorem sep : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ f₀ Φ f : WO S T → ℂ, IsSBHalf e (latO S T ΛS ΛT fun _ => True) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Φ f → ∀ g : GA D S, (∀ x, Φ x ≠ 0 → Φ (actO S T g 1 x) = 0) → ∃ (n : ℕ) (a : Fin n → ℂ) (y : Fin n → WO S T), (∀ i, (y i).map (infPart D) = 0 ∧ (actO S T g⁻¹ 1 (-(y i))).map (infPart D) = 0) ∧ ∑ i, a i • heisO ψ S T (y i) f = f ∧ ∑ i, conj (a i) • heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) f = 0 := by
  classical
  intro D ψ S T hψ ΛS ΛT hS hT Z e he f₀ Φ f hΦ hth g hsupp
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
  have hfT : f = Tm Φ := hall Tm hTm
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hinfc : infPart D (cA D e) = 0 := ho.conj.infPart_eq
  obtain ⟨k, hk, hinv, hsup⟩ := hΦ.2
  obtain ⟨M, hM, hMact⟩ := (GlobalTheory.LatLevel.level_of_generators D S T ΛS ΛT hS hT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT)).2 g 1
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛ
  set N : ℕ := M * k with hN
  have hNpos : 0 < N := Nat.mul_pos hM hk
  let Ψ : WO S T → ℂ := fun u => if ∃ t, Φ t ≠ 0 ∧ N • t = u then 1 else 0
  have hNt : ∀ t, Φ t ≠ 0 → N • t ∈ Λ := fun t ht => by
    rw [hN, mul_smul]; exact Λ.nsmul_mem (hsup t ht) M
  have hΨ : IsSBHalf e Λ Ψ := by
    refine ⟨fun u hu => ?_, N * k, Nat.mul_pos hNpos hk, fun v hv hvh u => ?_, fun u hu => ?_⟩
    · have : ∃ t, Φ t ≠ 0 ∧ N • t = u := by
        by_contra h; exact hu (if_neg h)
      obtain ⟨t, ht, rfl⟩ := this
      exact GlobalTheory.ThetaOrth.isHalf_nsmul (hΦ.1 t ht) N
    · have key : (∃ t, Φ t ≠ 0 ∧ N • t = u + (N * k) • v) ↔ ∃ t, Φ t ≠ 0 ∧ N • t = u := by
        constructor
        · rintro ⟨t, ht, h⟩
          refine ⟨t + k • (-v), by rwa [hinv (-v) (Λ.neg_mem hv) (GlobalTheory.ThetaOrth.isHalf_neg hvh) t], ?_⟩
          exact GlobalTheory.ThetaOrth.nsmul_add_neg N k t u v h
        · rintro ⟨t, ht, rfl⟩
          refine ⟨t + k • v, by rwa [hinv v hv hvh t], ?_⟩
          exact GlobalTheory.ThetaOrth.nsmul_add_mul N k t v
      show (if _ then _ else _) = (if _ then _ else _)
      simp only [key]
    · have : ∃ t, Φ t ≠ 0 ∧ N • t = u := by
        by_contra h; exact hu (if_neg h)
      obtain ⟨t, ht, rfl⟩ := this
      exact Λ.nsmul_mem (hNt t ht) _
  have hspan := (GlobalTheory.PlaceTensor.halfWaves_span D ψ S T ΛS ΛT hψ hS hT e ho.idem he.2 ho.infPart_eq).2 Ψ hΨ
  obtain ⟨q, hq, hqΨ⟩ := GlobalTheory.ThetaOrth.exists_char_of_wave N hspan
  have hq1 : ∀ t, Φ t ≠ 0 → q t = 1 := fun t ht => by
    rw [← hqΨ t (hΦ.1 t ht) (hNt t ht)]
    exact if_pos ⟨t, ht, rfl⟩
  have hq0 : ∀ t, Φ t ≠ 0 → q (actO S T g 1 t) = 0 := fun t ht => by
    have h1 : N • actO S T g 1 t ∈ Λ := by
      have := hMact (k • t) (hsup t ht)
      have e : actO S T g 1 (k • t) = k • actO S T g 1 t := map_nsmul (GlobalTheory.LatLevel.actHom S T g 1) k t
      rwa [e, ← mul_smul] at this
    rw [← hqΨ _ (GlobalTheory.SplitHecke.isHalf_actO _ _ (hΦ.1 t ht)) h1]
    refine if_neg ?_
    rintro ⟨t', ht', h⟩
    have : t' = actO S T g 1 t := GlobalTheory.ThetaOrth.nsmul_inj hNpos h
    exact ht' (this ▸ hsupp t ht)

  obtain ⟨n, a, yy, hqs⟩ := (Submodule.mem_span_set' (R := ℂ)).1 hq
  choose y hy hyq using fun i => (yy i).2
  have hqt : ∀ t, q t = ∑ i, a i * ψ (symplO S T t (y i)) := fun t => by
    rw [← hqs, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, hyq i, smul_eq_mul]
  set w : Fin n → WO S T := fun i => actO S T g⁻¹ 1 (-(y i)) with hw
  have hwh : ∀ i, IsHalf (cA D e) (w i) := fun i =>
    GlobalTheory.SplitHecke.isHalf_actO _ _ (GlobalTheory.ThetaOrth.isHalf_neg (hy i))
  have hact : ∀ i, actO S T g 1 (w i) = -(y i) := fun i => by
    have := GlobalTheory.AdelicLatMove.actO_actO_inv S T g 1 (-(y i))
    rwa [inv_one] at this
  refine ⟨n, a, y, fun i => ⟨map_infPart_eq_zero hinfc (hy i), map_infPart_eq_zero hinfc (hwh i)⟩, ?_, ?_⟩
  · have e1 : (fun t => q t * Φ t) = Φ := by
      funext t
      by_cases h : Φ t = 0
      · rw [h, mul_zero]
      · rw [hq1 t h, one_mul]
    have e2 : (fun t => q t * Φ t) = ∑ i, a i • fun t => ψ (symplO S T t (y i)) * Φ t := by
      funext t
      rw [hqt, Finset.sum_mul, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
    have e3 := congrArg Tm e2
    rw [e1, map_sum, ← hfT] at e3
    refine (Finset.sum_congr rfl fun i _ => ?_).trans e3.symm
    rw [map_smul, hTm.modul Φ hΦ (y i) (hy i), ← hfT]
  · have e1 : (fun t => conj (q (actO S T g 1 t)) * Φ t) = 0 := by
      funext t
      by_cases h : Φ t = 0
      · simp [h]
      · simp [hq0 t h]
    have e2 : (fun t => conj (q (actO S T g 1 t)) * Φ t) =
        ∑ i, conj (a i) • fun t => ψ (symplO S T t (w i)) * Φ t := by
      funext t
      rw [hqt, map_sum, Finset.sum_mul, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, map_mul, GlobalTheory.ThetaOrth.conj_psi hψ,
        ← GlobalTheory.ThetaOrth.symplO_neg_right, ← hact i, GlobalTheory.SymplOInv.symplO_actO D S T g 1 t (w i), mul_assoc]
    have e3 := congrArg Tm e2
    rw [e1, map_zero, map_sum] at e3
    rw [e3]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hfT, hTm.modul Φ hΦ (w i) (hwh i)]

end GlobalTheory.HalfSep

end
