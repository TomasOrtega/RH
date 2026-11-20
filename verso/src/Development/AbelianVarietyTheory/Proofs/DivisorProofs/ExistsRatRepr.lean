import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactors
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
open GlobalTheory.SqTop

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.CMVal
open Formalism.L2.Host (HChar)

namespace GlobalTheory.ToricExist

/- English proof (translation)
Use `set bb : D.host.E := D.host.sqd with hbb`. Establish `hb : bb ^ 2 = -(D.host.d : D.host.E)` using `D.host.sqd_sq`. Establish `hbK : bb ∈ D.host.K` using `IntermediateField.mem_adjoin_simple_self ℚ _`. Establish `hwb : w = bb ∨ w = -bb`. Establish `h0 : (w - bb) * (w + bb) = 0`.

Establish `: (w - bb) * (w + bb) = w ^ 2 - bb ^ 2` using `by ring`. Rewrite using `[this, hw, hb, sub_self]`. Break down `mul_eq_zero.1 h0 with h | h` into its components or cases. Conclude with `Or.inl (sub_eq_zero.1 h)`. Conclude with `Or.inr (eq_neg_of_add_eq_zero_left h)`.

Establish `hwK : w ∈ D.host.K`. Break down `hwb with h | h` into its components or cases. Rewrite using `[h]`. Conclude with `hbK`. Rewrite using `[h]`.

Conclude with `neg_mem hbK`. Use `⟨hwK, fun y => ?_⟩` and prove the remaining obligations. Set `wK : D.host.K` to `⟨w, hwK⟩`. Establish `hli : LinearIndependent ℚ ![(1 : D.host.K), wK]`. Rewrite using `[LinearIndependent.pair_iff]`.

Introduce `s t hst`. Establish `h0 : (s : D.host.E) + (t : D.host.E) * w = 0`. Use `congrArg Subtype.val hst` as an intermediate fact. Simplify `this` using `[Rat.smul_def, wK]`. Establish `h1` using `congrArg σ h0`.

Simplify using `only [map_add, map_mul, map_ratCast, map_zero, hσ] at h1`. Establish `hre` using `congrArg Complex.re h1`. Establish `him` using `congrArg Complex.im h1`. Simplify using `at hre him`. Use `⟨by exact_mod_cast hre, ?_⟩` and prove the remaining obligations.

Break down `him with h | h` into its components or cases. Conclude with `h` after adjusting the coercions. Conclude with `absurd h hd.ne'`. Establish `hcard : Fintype.card (Fin 2) = Module.finrank ℚ D.host.K`. Rewrite using `[GlobalTheory.CurveLattice.finrank_hostK]`.

Both sides reduce to the same expression. Set `B` to `basisOfLinearIndependentOfCardEqFinrank hli hcard`. Establish `hB : ∀ i, B i = ![(1 : D.host.K), wK] i` using `fun i => by`. Simplify using `[B, coe_basisOfLinearIndependentOfCardEqFinrank]`. Use `⟨B.repr y 0, B.repr y 1, ?_⟩` and prove the remaining obligations.

Establish `e` using `B.sum_repr y`. Rewrite `e` using `[Fin.sum_univ_two, hB, hB]`. Establish `e2` using `congrArg (fun z : D.host.K => (z : D.host.E)) e`. Simplify using `only [IntermediateField.coe_add, IntermediateField.coe_smul, Matrix.cons_val_zero, Matrix.cons_val_one, IntermediateField.coe_one, Rat.smul_def, mul_one] at e2`. Rewrite using `[← e2]`.

Both sides reduce to the same expression.
-/
theorem exists_rat_repr (D : D7) {w : D.host.E} (hw : w ^ 2 = -(D.host.d : D.host.E)) (hd : 0 < D.host.d)
    (σ : D.host.E →+* ℂ) (hσ : σ w = Complex.I * (Real.sqrt D.host.d : ℝ)) :
    w ∈ D.host.K ∧ ∀ y : D.host.K, ∃ a b : ℚ, (y : D.host.E) = (a : D.host.E) + (b : D.host.E) * w := by
  set bb : D.host.E := D.host.sqd with hbb
  have hb : bb ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  have hbK : bb ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ _
  have hwb : w = bb ∨ w = -bb := by
    have h0 : (w - bb) * (w + bb) = 0 := by
      have : (w - bb) * (w + bb) = w ^ 2 - bb ^ 2 := by ring
      rw [this, hw, hb, sub_self]
    rcases mul_eq_zero.1 h0 with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hwK : w ∈ D.host.K := by
    rcases hwb with h | h
    · rw [h]; exact hbK
    · rw [h]; exact neg_mem hbK
  refine ⟨hwK, fun y => ?_⟩
  let wK : D.host.K := ⟨w, hwK⟩
  have hli : LinearIndependent ℚ ![(1 : D.host.K), wK] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h0 : (s : D.host.E) + (t : D.host.E) * w = 0 := by
      have := congrArg Subtype.val hst
      simpa [Rat.smul_def, wK] using this
    have h1 := congrArg σ h0
    simp only [map_add, map_mul, map_ratCast, map_zero, hσ] at h1
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp at hre him
    refine ⟨by exact_mod_cast hre, ?_⟩
    rcases him with h | h
    · exact_mod_cast h
    · exact absurd h hd.ne'
  have hcard : Fintype.card (Fin 2) = Module.finrank ℚ D.host.K := by
    rw [GlobalTheory.CurveLattice.finrank_hostK]; rfl
  let B := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hB : ∀ i, B i = ![(1 : D.host.K), wK] i := fun i => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]
  refine ⟨B.repr y 0, B.repr y 1, ?_⟩
  have e := B.sum_repr y
  rw [Fin.sum_univ_two, hB, hB] at e
  have e2 := congrArg (fun z : D.host.K => (z : D.host.E)) e
  simp only [IntermediateField.coe_add, IntermediateField.coe_smul, Matrix.cons_val_zero, Matrix.cons_val_one,
    IntermediateField.coe_one, Rat.smul_def, mul_one] at e2
  rw [← e2]
  rfl

/- English proof (translation)
Take `⟨-, hd4, -, -, -, hcard, -, w, hw, hwφ⟩` from `hFD`. Establish `hne : Nonempty D.what₂.Tau` using `Fintype.card_pos_iff.1 (by omega)`. Take `⟨τ₀⟩` from `hne`. Take `⟨hwK, hrep⟩` from `exists_rat_repr D hw (by omega) (cmPhi D τ₀) (hwφ τ₀)`. Set `φK : D.host.K →+* ℂ` to `(cmPhi D τ₀).comp (algebraMap D.host.K D.host.E)`.

Establish `hval : ∀ (τ : D.what₂.Tau) (y : D.host.K) (a b : ℚ), (y : D.host.E) = (a : D.host.E) + (b : D.host.E) * w → cmPhi D τ (y : D.host.E) = (a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℝ))`. Introduce `τ y a b h`. Rewrite using `[h, map_add, map_mul, map_ratCast, map_ratCast, hwφ τ]`. Establish `hcomp : ∀ τ, (cmPhi D τ).comp (algebraMap D.host.K D.host.E) = φK` using `fun τ => by`. Use extensionality with `y`.

Take `⟨a, b, h⟩` from `hrep y`. Use `show cmPhi D τ (y : D.host.E) = cmPhi D τ₀ (y : D.host.E)`. Rewrite using `[hval τ y a b h, hval τ₀ y a b h]`. Use `⟨φK, hcomp, fun Λ hΛ => ?_⟩` and prove the remaining obligations. Establish `hinj : Function.Injective φK` using `φK.injective`.

Use extensionality with `x`. Simplify using `only [Set.mem_image, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨hint, a, b, rfl⟩` from `(hΛ x).1 hx`.

Set `y : D.host.K` to `(a : D.host.K) + (b : D.host.K) * ⟨w, hwK⟩`. Establish `hy : φK y = (a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℝ))` using `by show cmPhi D τ₀ (y : D.host.E) = _`. Conclude with `hval τ₀ y a b (by simp [y])`. Use `⟨y, ?_, hy⟩` and prove the remaining obligations. Establish `hyi : IsIntegral ℤ y` using `(isIntegral_algHom_iff φK.toIntAlgHom hinj).1 (by rw [← hy] at hint; exact hint)`.

Conclude with `(FractionalIdeal.mem_one_iff _).2 ⟨⟨y, hyi⟩, rfl⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Take `⟨y', rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 hy`. Take `⟨a, b, h⟩` from `hrep (algebraMap (𝓞 D.host.K) D.host.K y')`. Use `(hΛ _).2 ⟨?_, a, b, hval τ₀ _ a b h⟩` and prove the remaining obligations.

Conclude with `(RingOfIntegers.isIntegral_coe y').map φK.toIntAlgHom`.
-/
theorem exists_phiK (D : D7) (hFD : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (cmPhi D)) :
    ∃ φK : D.host.K →+* ℂ, (∀ τ, (cmPhi D τ).comp (algebraMap D.host.K D.host.E) = φK) ∧
      ∀ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf φK 1 Λ := by
  obtain ⟨-, hd4, -, -, -, hcard, -, w, hw, hwφ⟩ := hFD
  have hne : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨τ₀⟩ := hne
  obtain ⟨hwK, hrep⟩ := exists_rat_repr D hw (by omega) (cmPhi D τ₀) (hwφ τ₀)
  let φK : D.host.K →+* ℂ := (cmPhi D τ₀).comp (algebraMap D.host.K D.host.E)
  have hval : ∀ (τ : D.what₂.Tau) (y : D.host.K) (a b : ℚ), (y : D.host.E) = (a : D.host.E) + (b : D.host.E) * w →
      cmPhi D τ (y : D.host.E) = (a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℝ)) := by
    intro τ y a b h
    rw [h, map_add, map_mul, map_ratCast, map_ratCast, hwφ τ]
  have hcomp : ∀ τ, (cmPhi D τ).comp (algebraMap D.host.K D.host.E) = φK := fun τ => by
    ext y
    obtain ⟨a, b, h⟩ := hrep y
    show cmPhi D τ (y : D.host.E) = cmPhi D τ₀ (y : D.host.E)
    rw [hval τ y a b h, hval τ₀ y a b h]
  refine ⟨φK, hcomp, fun Λ hΛ => ?_⟩
  have hinj : Function.Injective φK := φK.injective
  ext x
  simp only [Set.mem_image, SetLike.mem_coe]
  constructor
  · intro hx
    obtain ⟨hint, a, b, rfl⟩ := (hΛ x).1 hx
    let y : D.host.K := (a : D.host.K) + (b : D.host.K) * ⟨w, hwK⟩
    have hy : φK y = (a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℝ)) := by
      show cmPhi D τ₀ (y : D.host.E) = _
      exact hval τ₀ y a b (by simp [y])
    refine ⟨y, ?_, hy⟩
    have hyi : IsIntegral ℤ y := (isIntegral_algHom_iff φK.toIntAlgHom hinj).1 (by rw [← hy] at hint; exact hint)
    exact (FractionalIdeal.mem_one_iff _).2 ⟨⟨y, hyi⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨y', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy
    obtain ⟨a, b, h⟩ := hrep (algebraMap (𝓞 D.host.K) D.host.K y')
    refine (hΛ _).2 ⟨?_, a, b, hval τ₀ _ a b h⟩
    exact (RingOfIntegers.isIntegral_coe y').map φK.toIntAlgHom

/- English proof (translation)
Take `⟨CF0, h1⟩` from `hP`. Use `⟨CF0, fun ε CF hCF => ?_⟩` and prove the remaining obligations. Take `⟨C0, x0, h2⟩` from `h1 ε CF hCF`. Conclude with `⟨C0, x0, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _ hμ (h2 C hC D large₂ he hx hr T Lc μ₀ hμ G)⟩`.
-/
theorem gBig_of {P R : GP} (hP : GBig P)
    (h : ∀ {D : D7} {T : Type} {Lc : Formalism.IndefR.Links.LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → P G μ₀ C x b → R G μ₀ C x b) : GBig R := by
  obtain ⟨CF0, h1⟩ := hP
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h2⟩ := h1 ε CF hCF
  exact ⟨C0, x0, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _ hμ (h2 C hC D large₂ he hx hr T Lc μ₀ hμ G)⟩

/- English proof (translation)
Take `⟨CF1, h1⟩` from `hP`. Take `⟨CF2, h2⟩` from `hQ`. Use `⟨max CF1 CF2, fun ε CF hCF => ?_⟩` and prove the remaining obligations. Take `⟨C1, x1, k1⟩` from `h1 ε CF (le_trans (le_max_left _ _) hCF)`. Take `⟨C2, x2, k2⟩` from `h2 ε CF (le_trans (le_max_right _ _) hCF)`.

Use `⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `k1 C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hr T Lc μ₀ hμ G`. Conclude with `k2 C (le_trans (le_max_right _ _) hC) D large₂ he (le_trans (le_max_right _ _) hx) hr T Lc μ₀ hμ G`.
-/
theorem gBig_and {P Q : GP} (hP : GBig P) (hQ : GBig Q) :
    GBig fun {_ _ _ _} G μ₀ C x b => P G μ₀ C x b ∧ Q G μ₀ C x b := by
  obtain ⟨CF1, h1⟩ := hP
  obtain ⟨CF2, h2⟩ := hQ
  refine ⟨max CF1 CF2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, k1⟩ := h1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, x2, k2⟩ := h2 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => ⟨?_, ?_⟩⟩
  · exact k1 C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hr T Lc μ₀ hμ G
  · exact k2 C (le_trans (le_max_right _ _) hC) D large₂ he (le_trans (le_max_right _ _) hx) hr T Lc μ₀ hμ G

/- English proof (translation)
Take `⟨M, hM, hfM⟩` from `Ideal.exists_le_maximal 𝔣 h.2.1`. Set `v : HeightOneSpectrum (OF E)` to `⟨M, hM.isPrime, fun e => h.1 (eq_bot_iff.2 (e ▸ hfM))⟩`. Take `⟨P, -⟩` from `(h.2.2 v (Ideal.dvd_iff_le.2 hfM)).1`. Conclude with `⟨P⟩`.
-/
theorem exists_prime {E : Type} [Field E] [NumberField E] {𝔣 : Ideal (OF E)} (h : IsBaseCond 𝔣) :
    Nonempty (HeightOneSpectrum (𝓞 E)) := by
  obtain ⟨M, hM, hfM⟩ := Ideal.exists_le_maximal 𝔣 h.2.1
  let v : HeightOneSpectrum (OF E) := ⟨M, hM.isPrime, fun e => h.1 (eq_bot_iff.2 (e ▸ hfM))⟩
  obtain ⟨P, -⟩ := (h.2.2 v (Ideal.dvd_iff_le.2 hfM)).1
  exact ⟨P⟩

/- English proof (translation)
Introduce `hT hF hL`. Use `gBig_of (gBig_and hF hL) ?_` and prove the remaining obligations. Introduce `D T Lc sc G μ₀ C x b hμ ⟨hf, hl⟩ i j s hs1 hs2 c`. Take `⟨hCM, hAb, hFD, hBC, -⟩` from `hf`. Establish `hFD'` using `hFD`.

Take `⟨-, hd4, hU, -, -, hcard, hφ, -⟩` from `hFD`. Establish `hV : IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) ∅ (fam G μ₀ i j c)`. Consider the cases of `c with`. Consider the case `none => exact (GlobalTheory.FunObj.SqNum.Model.isValChar_nu hμ G i j hs2).1`. Consider the case `some c => exact (GlobalTheory.FunObj.SqNum.Model.isValChar_nu hμ G i j hs2).2 c`.

Take `⟨P⟩` from `exists_prime hBC`. Establish `hAux : IsFinSetSplitPlacesCoprimeConductor (condF G.pl) ∅` using `fun q hq => absurd hq (Finset.notMem_empty q)`. Establish `hTS : ∀ Λ, IsHeckeL (fam G μ₀ i j c) Λ → IsToricSum (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) (fam G μ₀ i j c) (Λ s)` using `fun Λ hΛ => by`. Use `GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.Published.HeckeEntire_holds D.host.E D.what₂.Tau (cmPhi D) hφ s (kap D sc.cGap i j s) (condF G.pl) ∅ (fam G μ₀ i j c) (fun _ => P) Λ hU hs1 hBC hAux hV (fun q hq => absurd hq (Finset.notMem_empty q)) hΛ` as an intermediate fact. Simplify `this` using `[condQ]`.

Take `⟨Λ, hΛ, hne⟩` from `(hl i j).2 c`. Use `⟨Λ s, ⟨hV, hTS Λ hΛ⟩, hne s hs1, fun Λ' h => by rw [hΛ.unique h], fun Λ₁ hΛ₁ => ?_⟩` and prove the remaining obligations. Take `⟨φK, hcomp, hlat⟩` from `exists_phiK D hFD'`. Use `haveI := hCM`. Use `haveI := hAb`.

Take `⟨t, 𝔞, Λσ, -, -, hTr⟩` from `hT D.host.K D.host.d hd4 (GlobalTheory.CurveLattice.finrank_hostK D) (GlobalTheory.CurveLattice.discr_hostK D) φK Λ₁ (hlat Λ₁ hΛ₁)`. Establish `hk` using `hTr D.host.E hU D.what₂.Tau (cmPhi D) hcard hφ hcomp s (kap D sc.cGap i j s) (condF G.pl) hs1 (fun τ => (GlobalTheory.FunObj.SqNum.Model.kap_add D sc.cGap i j τ hs2).2) hBC`. Conclude with `(hk.1 ∅ _ _ ⟨hAux, hV, by simpa [condQ] using hTS Λ hΛ⟩).1`.
-/
theorem torEx : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport → FieldDat → LNe → TorEx := by
  intro hT hF hL
  refine gBig_of (gBig_and hF hL) ?_
  intro D T Lc sc G μ₀ C x b hμ ⟨hf, hl⟩ i j s hs1 hs2 c
  obtain ⟨hCM, hAb, hFD, hBC, -⟩ := hf
  have hFD' := hFD
  obtain ⟨-, hd4, hU, -, -, hcard, hφ, -⟩ := hFD
  have hV : IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) ∅ (fam G μ₀ i j c) := by
    cases c with
    | none => exact (GlobalTheory.FunObj.SqNum.Model.isValChar_nu hμ G i j hs2).1
    | some c => exact (GlobalTheory.FunObj.SqNum.Model.isValChar_nu hμ G i j hs2).2 c
  obtain ⟨P⟩ := exists_prime hBC
  have hAux : IsFinSetSplitPlacesCoprimeConductor (condF G.pl) ∅ := fun q hq => absurd hq (Finset.notMem_empty q)
  have hTS : ∀ Λ, IsHeckeL (fam G μ₀ i j c) Λ →
      IsToricSum (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) (fam G μ₀ i j c) (Λ s) := fun Λ hΛ => by
    have := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.Published.HeckeEntire_holds D.host.E D.what₂.Tau (cmPhi D) hφ s
      (kap D sc.cGap i j s) (condF G.pl) ∅ (fam G μ₀ i j c) (fun _ => P) Λ hU hs1 hBC hAux hV
      (fun q hq => absurd hq (Finset.notMem_empty q)) hΛ
    simpa [condQ] using this
  obtain ⟨Λ, hΛ, hne⟩ := (hl i j).2 c
  refine ⟨Λ s, ⟨hV, hTS Λ hΛ⟩, hne s hs1, fun Λ' h => by rw [hΛ.unique h], fun Λ₁ hΛ₁ => ?_⟩
  obtain ⟨φK, hcomp, hlat⟩ := exists_phiK D hFD'
  haveI := hCM
  haveI := hAb
  obtain ⟨t, 𝔞, Λσ, -, -, hTr⟩ := hT D.host.K D.host.d hd4 (GlobalTheory.CurveLattice.finrank_hostK D)
    (GlobalTheory.CurveLattice.discr_hostK D) φK Λ₁ (hlat Λ₁ hΛ₁)
  have hk := hTr D.host.E hU D.what₂.Tau (cmPhi D) hcard hφ hcomp s (kap D sc.cGap i j s) (condF G.pl) hs1
    (fun τ => (GlobalTheory.FunObj.SqNum.Model.kap_add D sc.cGap i j τ hs2).2) hBC
  exact (hk.1 ∅ _ _ ⟨hAux, hV, by simpa [condQ] using hTS Λ hΛ⟩).1

end GlobalTheory.ToricExist

/- English proof (translation)
The claim follows from `GlobalTheory.ToricExist.torEx`.
-/
example : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport → GlobalTheory.SqTop.FieldDat → GlobalTheory.SqTop.LNe → GlobalTheory.SqTop.TorEx := GlobalTheory.ToricExist.torEx
