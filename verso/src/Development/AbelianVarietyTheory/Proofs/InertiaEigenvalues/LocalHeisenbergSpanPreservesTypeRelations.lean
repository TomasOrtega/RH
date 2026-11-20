import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasShape
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

namespace GlobalTheory.DownLift.PlaceTranslate

variable {D : D7}

/- English proof (translation)
Simplify using `[Formalism.L2.Theta.mt]`.
-/
theorem mt_mul' (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := by simp [Formalism.L2.Theta.mt]

/- English proof (translation)
Simplify using `[Formalism.L2.Theta.mt]`.
-/
theorem mt_one' (V : HSp D) : mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]

/- English proof (translation)
Establish `hM : ∀ k j, e * mt S g k j = e * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j`. Introduce `k j`. Establish `h` using `hg k j`. Rewrite `h` using `[Matrix.sub_apply, mul_sub, sub_eq_zero]`. Conclude with `h`.

Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply]`. Use `conv_rhs => rw [← Matrix.mul_one (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)), Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mul_mt_eq {S T : HSp D} {e : AE D} {g : GA D S} (hg : ∀ i j, e * (mt S g - 1) i j = 0) {u : WO S T}
    (hu : IsHalf e u) : HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g) = u := by
  have hM : ∀ k j, e * mt S g k j = e * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j := by
    intro k j
    have h := hg k j
    rw [Matrix.sub_apply, mul_sub, sub_eq_zero] at h
    exact h
  ext i j
  rw [Matrix.mul_apply]
  conv_rhs => rw [← Matrix.mul_one (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)), Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  calc u i k * mt S g k j = (e * u i k) * mt S g k j := by rw [hu i k]
    _ = u i k * (e * mt S g k j) := by ring
    _ = u i k * (e * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j) := by rw [hM k j]
    _ = (e * u i k) * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j := by ring
    _ = u i k * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j := by rw [hu i k]

/- English proof (translation)
Establish `h1` using `mul_mt_eq (T := T) hg hu`. Establish `h2 : HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g⁻¹) = u` using `by conv_lhs => rw [← h1]`. Rewrite using `[Matrix.mul_assoc, ← mt_mul', mul_inv_cancel, mt_one', Matrix.mul_one]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [actO, mt_one', Matrix.one_mul]`.

Conclude with `h2`. Simplify using `only [actO, mt_one', Matrix.one_mul, inv_inv]`. Conclude with `h1`.
-/
theorem actO_fix {S T : HSp D} {e : AE D} {g : GA D S} (hg : ∀ i j, e * (mt S g - 1) i j = 0) {u : WO S T}
    (hu : IsHalf e u) : actO S T g 1 u = u ∧ actO S T g⁻¹ 1 u = u := by
  have h1 := mul_mt_eq (T := T) hg hu
  have h2 : HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g⁻¹) = u := by
    conv_lhs => rw [← h1]
    rw [Matrix.mul_assoc, ← mt_mul', mul_inv_cancel, mt_one', Matrix.mul_one]
  refine ⟨?_, ?_⟩
  · simp only [actO, mt_one', Matrix.one_mul]; exact h2
  · simp only [actO, mt_one', Matrix.one_mul, inv_inv]; exact h1

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

/- English proof (translation)
Simplify using `only [avgW, map_add, smul_add, Finset.sum_add_distrib]`.
-/
theorem avgW_add (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool)
    (ε : ℤ) (κ : G → GA D (Vc D i)) (f g : WO (Vc D i) (Wc D i) → ℂ) :
    avgW R i t PP a tr ε κ (f + g) = avgW R i t PP a tr ε κ f + avgW R i t PP a tr ε κ g := by
  simp only [avgW, map_add, smul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [avgW, map_smul, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun g _ => smul_comm _ _ _` and prove the remaining obligations.
-/
theorem avgW_smul (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool)
    (ε : ℤ) (κ : G → GA D (Vc D i)) (c : ℂ) (f : WO (Vc D i) (Wc D i) → ℂ) :
    avgW R i t PP a tr ε κ (c • f) = c • avgW R i t PP a tr ε κ f := by
  simp only [avgW, map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun g _ => smul_comm _ _ _

/- English proof (translation)
Simplify using `only [avgW, map_zero, smul_zero, Finset.sum_const_zero]`.
-/
theorem avgW_zero (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool)
    (ε : ℤ) (κ : G → GA D (Vc D i)) : avgW R i t PP a tr ε κ 0 = 0 := by
  simp only [avgW, map_zero, smul_zero, Finset.sum_const_zero]

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `[heisO]`.
-/
theorem heisO_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T' : HSp D) (u : WO S T') : heisO ψ S T' u 0 = 0 := by
  funext w; simp [heisO]

/- English proof (translation)
Introduce `D G _ _ Pl0 T A Ks _ _ _ R hω i t Sb v hv ε a hε hae f hT hC hL f' hf'`. Use `set E' := algebraMap (AF D.host.F) (AE D) ε with hE'`. Establish `hW` using `hω i t`. Establish `hψ` using `hW.std`. Establish `hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) f` using `hT.1`.

Establish `hvd : v ∉ dropPl Sb v` using `by classical`. Unfold `dropPl`. Simplify using the standard rewrite rules. Establish `hsub : ∀ w, w ∈ dropPl Sb v → w ∈ Sb` using `by classical`. Introduce `w hw`.

Unfold `dropPl at hw`. Conclude with `Finset.mem_of_mem_erase hw`. Establish `hsupp : ∀ κ : GA D (Vc D i), SuppIn (dropPl Sb v) (Vc D i) κ → SuppIn Sb (Vc D i) κ ∧ ∀ i' j', E' * (mt (Vc D i) κ - 1) i' j' = 0`. Introduce `κ hκ`. Conclude with `⟨⟨hκ.1, fun w hw => hκ.2 w fun h => hw (hsub w h)⟩, hκ.2 v hvd ε hε⟩`.

Establish `hcE : cA D E' = E'`. Rewrite using `[← hae, map_add, GlobalTheory.DualPairCheck.cA_cA, add_comm]`. Set `P : (WO (Vc D i) (Wc D i) → ℂ) → Prop` to `fun φ => TypeIn R i t (dropPl Sb v) φ ∧ CleanIn R i t (dropPl Sb v) φ ∧ LikeOff R i t Sb φ`. Establish `hgen : ∀ u : WO (Vc D i) (Wc D i), IsHalf E' u → P (heisO R.ψ (Vc D i) (Wc D i) u f)`. Introduce `u hu`.

Establish `hthu` using `GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hth u`. Use `⟨⟨hthu, fun κ hκ hκs => ?_⟩, ?_, ⟨hthu, ?_⟩⟩` and prove the remaining obligations. Take `⟨hκS, hκv⟩` from `hsupp κ hκs`. Rewrite using `[hW.om_heis κ 1 u f hth, (actO_fix hκv hu).1, hT.2 κ hκ hκS, GlobalTheory.SplitScalar.heisO_smul]`. Introduce `PP a' ha' tr e he hex κ hκ hκs`.

Establish `hex' : ∃ w ∈ Sb, Over PP.1 w`. Take `⟨w, hw, hO⟩` from `hex`. Conclude with `⟨w, hsub w hw, hO⟩`. Establish `hκs' : ∀ g, mirC R i PP a' tr e g ≠ 0 → SuppIn Sb (Vc D i) (κ g)` using `fun g hg => (hsupp _ (hκs g hg)).1`. Establish `key : avgW R i t PP a' tr e κ (heisO R.ψ (Vc D i) (Wc D i) u f) = heisO R.ψ (Vc D i) (Wc D i) u (avgW R i t PP a' tr e κ f)`.

Simplify using `only [avgW]`. Rewrite using `[GlobalTheory.SplitScalar.heisO_sum]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : mirC R i PP a' tr e g = 0`. Rewrite using `[hc, zero_mul, zero_smul, zero_smul, heisO_zero']`.

Rewrite using `[hW.om_heis (κ g)⁻¹ 1 u f hth, (actO_fix (hsupp _ (hκs g hc)).2 hu).2, GlobalTheory.SplitScalar.heisO_smul]`. Rewrite using `[key, hC PP a' ha' tr e he hex' κ hκ hκs', heisO_zero']`. Introduce `c hc h0`. Establish `hcomm : ∀ w ∈ c.support, heisO R.ψ (Vc D i) (Wc D i) w (heisO R.ψ (Vc D i) (Wc D i) u f) = heisO R.ψ (Vc D i) (Wc D i) u (heisO R.ψ (Vc D i) (Wc D i) w f)`. Introduce `w hw`.

Establish `hw0 : E' • w = 0`. Use extensionality with `i' j'`. Conclude with `(hc w hw).2 v hv ε hε i' j'`. Establish `hs : symplO (Vc D i) (Wc D i) w u = 0`. Establish `hu' : E' • u = u` using `(GlobalTheory.SplitScalar.isHalf_iff _ _).1 hu`.

Rewrite using `[← hu', ← hcE, ← GlobalTheory.SplitScalar.symplO_smul, hw0, GlobalTheory.SplitScalar.symplO_zero_left]`. Rewrite using `[GlobalTheory.SplitScalar.heisO_comm, hs, AddChar.map_zero_eq_one, one_smul]`. Establish `e1 : (c.sum fun w z => z • heisO R.ψ (Vc D i) (Wc D i) w (heisO R.ψ (Vc D i) (Wc D i) u f)) = heisO R.ψ (Vc D i) (Wc D i) u (c.sum fun w z => z • heisO R.ψ (Vc D i) (Wc D i) w f)`. Unfold `Finsupp.sum`. Rewrite using `[GlobalTheory.SplitScalar.heisO_sum]`.

Use `Finset.sum_congr rfl fun w hw => ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hcomm w hw, GlobalTheory.SplitScalar.heisO_smul]`. Rewrite using `[e1, hL.2 c hc h0, heisO_zero']`. Establish `h0 : P 0`.

Establish `hz : IsThetaFunO R.ψ (Vc D i) (Wc D i) 0` using `by simpa using theta_smul (0 : ℂ) hth`. Use `⟨⟨hz, fun κ _ _ => by rw [map_zero, smul_zero]⟩, fun _ _ _ _ _ _ _ _ _ _ => avgW_zero _ _ _ _ _ _ _ _, ⟨hz, fun c _ _ => ?_⟩⟩` and prove the remaining obligations. Simplify using `[heisO_zero']`. Establish `hadd : ∀ φ₁ φ₂, P φ₁ → P φ₂ → P (φ₁ + φ₂)`. Introduce and unpack `φ₁ φ₂ ⟨⟨t1, T1⟩, C1, ⟨l1, L1⟩⟩ ⟨⟨t2, T2⟩, C2, ⟨l2, L2⟩⟩`.

Use `⟨⟨theta_add t1 t2, fun κ hκ hκs => ?_⟩, fun PP a' ha' tr e he hex κ hκ hκs => ?_, ⟨theta_add l1 l2, fun c hc h0 => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[map_add, T1 κ hκ hκs, T2 κ hκ hκs, smul_add]`. Rewrite using `[avgW_add, C1 PP a' ha' tr e he hex κ hκ hκs, C2 PP a' ha' tr e he hex κ hκ hκs, add_zero]`. Simplify using `only [heisO_add', smul_add]`. Rewrite using `[Finsupp.sum_add, L1 c hc h0, L2 c hc h0, add_zero]`.

Establish `hsmul : ∀ (r : ℂ) φ, P φ → P (r • φ)`. Introduce and unpack `r φ ⟨⟨t1, T1⟩, C1, ⟨l1, L1⟩⟩`. Use `⟨⟨theta_smul r t1, fun κ hκ hκs => ?_⟩, fun PP a' ha' tr e he hex κ hκ hκs => ?_, ⟨theta_smul r l1, fun c hc h0 => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[map_smul, T1 κ hκ hκs, smul_comm]`. Rewrite using `[avgW_smul, C1 PP a' ha' tr e he hex κ hκ hκs, smul_zero]`.

Establish `e1 : (c.sum fun w z => z • heisO R.ψ (Vc D i) (Wc D i) w (r • φ)) = r • (c.sum fun w z => z • heisO R.ψ (Vc D i) (Wc D i) w φ)`. Rewrite using `[Finsupp.smul_sum]`. Use `Finsupp.sum_congr fun w _ => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.SplitScalar.heisO_smul, smul_comm]`. Rewrite using `[e1, L1 c hc h0, smul_zero]`.

Use `Submodule.span_induction (p := fun φ _ => P φ) ?_ h0 (fun x y _ _ hx hy => hadd x y hx hy) (fun r x _ hx => hsmul r x hx) hf'` and prove the remaining obligations. Introduce and unpack `φ ⟨u, hu, rfl⟩`. Rewrite `hu` using `[hae]`. Conclude with `hgen u hu`.
-/
theorem locSpan_pres : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.thP_ωP →
    ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)),
    v ∈ Sb → ∀ (ε : AF D.host.F) (a : AE D), IsPlaceIdem D v ε → a + cA D a = algebraMap (AF D.host.F) (AE D) ε →
    ∀ f : WO (Vc D i) (Wc D i) → ℂ, TypeIn R i t Sb f → CleanIn R i t Sb f → LikeOff R i t Sb f →
    ∀ f' ∈ locSpan R.ψ (Vc D i) (Wc D i) a f,
      TypeIn R i t (dropPl Sb v) f' ∧ CleanIn R i t (dropPl Sb v) f' ∧ LikeOff R i t Sb f' := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hω i t Sb v hv ε a hε hae f hT hC hL f' hf'
  set E' := algebraMap (AF D.host.F) (AE D) ε with hE'
  have hW := hω i t
  have hψ := hW.std
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) f := hT.1
  have hvd : v ∉ dropPl Sb v := by
    classical
    unfold dropPl
    simp
  have hsub : ∀ w, w ∈ dropPl Sb v → w ∈ Sb := by
    classical
    intro w hw
    unfold dropPl at hw
    exact Finset.mem_of_mem_erase hw

  have hsupp : ∀ κ : GA D (Vc D i), SuppIn (dropPl Sb v) (Vc D i) κ →
      SuppIn Sb (Vc D i) κ ∧ ∀ i' j', E' * (mt (Vc D i) κ - 1) i' j' = 0 := by
    intro κ hκ
    exact ⟨⟨hκ.1, fun w hw => hκ.2 w fun h => hw (hsub w h)⟩, hκ.2 v hvd ε hε⟩
  have hcE : cA D E' = E' := by
    rw [← hae, map_add, GlobalTheory.DualPairCheck.cA_cA, add_comm]

  let P : (WO (Vc D i) (Wc D i) → ℂ) → Prop := fun φ =>
    TypeIn R i t (dropPl Sb v) φ ∧ CleanIn R i t (dropPl Sb v) φ ∧ LikeOff R i t Sb φ
  have hgen : ∀ u : WO (Vc D i) (Wc D i), IsHalf E' u → P (heisO R.ψ (Vc D i) (Wc D i) u f) := by
    intro u hu
    have hthu := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hth u
    refine ⟨⟨hthu, fun κ hκ hκs => ?_⟩, ?_, ⟨hthu, ?_⟩⟩
    · obtain ⟨hκS, hκv⟩ := hsupp κ hκs
      rw [hW.om_heis κ 1 u f hth, (actO_fix hκv hu).1, hT.2 κ hκ hκS, GlobalTheory.SplitScalar.heisO_smul]
    · intro PP a' ha' tr e he hex κ hκ hκs
      have hex' : ∃ w ∈ Sb, Over PP.1 w := by
        obtain ⟨w, hw, hO⟩ := hex; exact ⟨w, hsub w hw, hO⟩
      have hκs' : ∀ g, mirC R i PP a' tr e g ≠ 0 → SuppIn Sb (Vc D i) (κ g) := fun g hg => (hsupp _ (hκs g hg)).1
      have key : avgW R i t PP a' tr e κ (heisO R.ψ (Vc D i) (Wc D i) u f) =
          heisO R.ψ (Vc D i) (Wc D i) u (avgW R i t PP a' tr e κ f) := by
        simp only [avgW]
        rw [GlobalTheory.SplitScalar.heisO_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        by_cases hc : mirC R i PP a' tr e g = 0
        · rw [hc, zero_mul, zero_smul, zero_smul, heisO_zero']
        · rw [hW.om_heis (κ g)⁻¹ 1 u f hth, (actO_fix (hsupp _ (hκs g hc)).2 hu).2, GlobalTheory.SplitScalar.heisO_smul]
      rw [key, hC PP a' ha' tr e he hex' κ hκ hκs', heisO_zero']
    · intro c hc h0
      have hcomm : ∀ w ∈ c.support, heisO R.ψ (Vc D i) (Wc D i) w (heisO R.ψ (Vc D i) (Wc D i) u f) =
          heisO R.ψ (Vc D i) (Wc D i) u (heisO R.ψ (Vc D i) (Wc D i) w f) := by
        intro w hw
        have hw0 : E' • w = 0 := by
          ext i' j'; exact (hc w hw).2 v hv ε hε i' j'
        have hs : symplO (Vc D i) (Wc D i) w u = 0 := by
          have hu' : E' • u = u := (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hu
          rw [← hu', ← hcE, ← GlobalTheory.SplitScalar.symplO_smul, hw0, GlobalTheory.SplitScalar.symplO_zero_left]
        rw [GlobalTheory.SplitScalar.heisO_comm, hs, AddChar.map_zero_eq_one, one_smul]
      have e1 : (c.sum fun w z => z • heisO R.ψ (Vc D i) (Wc D i) w (heisO R.ψ (Vc D i) (Wc D i) u f)) =
          heisO R.ψ (Vc D i) (Wc D i) u (c.sum fun w z => z • heisO R.ψ (Vc D i) (Wc D i) w f) := by
        unfold Finsupp.sum
        rw [GlobalTheory.SplitScalar.heisO_sum]
        refine Finset.sum_congr rfl fun w hw => ?_
        dsimp only
        rw [hcomm w hw, GlobalTheory.SplitScalar.heisO_smul]
      rw [e1, hL.2 c hc h0, heisO_zero']
  have h0 : P 0 := by
    have hz : IsThetaFunO R.ψ (Vc D i) (Wc D i) 0 := by simpa using theta_smul (0 : ℂ) hth
    refine ⟨⟨hz, fun κ _ _ => by rw [map_zero, smul_zero]⟩, fun _ _ _ _ _ _ _ _ _ _ => avgW_zero _ _ _ _ _ _ _ _,
      ⟨hz, fun c _ _ => ?_⟩⟩
    simp [heisO_zero']
  have hadd : ∀ φ₁ φ₂, P φ₁ → P φ₂ → P (φ₁ + φ₂) := by
    rintro φ₁ φ₂ ⟨⟨t1, T1⟩, C1, ⟨l1, L1⟩⟩ ⟨⟨t2, T2⟩, C2, ⟨l2, L2⟩⟩
    refine ⟨⟨theta_add t1 t2, fun κ hκ hκs => ?_⟩, fun PP a' ha' tr e he hex κ hκ hκs => ?_,
      ⟨theta_add l1 l2, fun c hc h0 => ?_⟩⟩
    · rw [map_add, T1 κ hκ hκs, T2 κ hκ hκs, smul_add]
    · rw [avgW_add, C1 PP a' ha' tr e he hex κ hκ hκs, C2 PP a' ha' tr e he hex κ hκ hκs, add_zero]
    · simp only [heisO_add', smul_add]
      rw [Finsupp.sum_add, L1 c hc h0, L2 c hc h0, add_zero]
  have hsmul : ∀ (r : ℂ) φ, P φ → P (r • φ) := by
    rintro r φ ⟨⟨t1, T1⟩, C1, ⟨l1, L1⟩⟩
    refine ⟨⟨theta_smul r t1, fun κ hκ hκs => ?_⟩, fun PP a' ha' tr e he hex κ hκ hκs => ?_,
      ⟨theta_smul r l1, fun c hc h0 => ?_⟩⟩
    · rw [map_smul, T1 κ hκ hκs, smul_comm]
    · rw [avgW_smul, C1 PP a' ha' tr e he hex κ hκ hκs, smul_zero]
    · have e1 : (c.sum fun w z => z • heisO R.ψ (Vc D i) (Wc D i) w (r • φ)) =
          r • (c.sum fun w z => z • heisO R.ψ (Vc D i) (Wc D i) w φ) := by
        rw [Finsupp.smul_sum]
        refine Finsupp.sum_congr fun w _ => ?_
        rw [GlobalTheory.SplitScalar.heisO_smul, smul_comm]
      rw [e1, L1 c hc h0, smul_zero]
  refine Submodule.span_induction (p := fun φ _ => P φ) ?_ h0 (fun x y _ _ hx hy => hadd x y hx hy)
    (fun r x _ hx => hsmul r x hx) hf'
  rintro φ ⟨u, hu, rfl⟩
  rw [hae] at hu
  exact hgen u hu

end GlobalTheory.DownLift.PlaceTranslate

end
