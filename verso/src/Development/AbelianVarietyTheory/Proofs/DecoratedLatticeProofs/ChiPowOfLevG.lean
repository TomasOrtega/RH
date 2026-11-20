import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopLevExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StpTopIdxEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtMMulVecFix
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelElt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

noncomputable section

namespace GlobalTheory.AdForm.LevChiTop

section Mat
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open GlobalTheory.Mem.Col2.TilX
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

def Deep {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (N : ℕ) (w : GL (Fin n) (AfE F E)) : Prop :=
  (∀ P', P' ≠ P → P' ≠ conjPrime₂ P → ∀ i j, adAt F P' (w.1 i j) = if i = j then 1 else 0) ∧
    ∀ r s, Valued.v (adAt F P (w.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ))

/- English proof (translation)
Assemble the required witnesses or components as `⟨hw.1, fun r s => (hw.2 r s).trans (WithZero.exp_le_exp.2 (by omega))⟩`.
-/
theorem Deep.mono {n : ℕ} {P : HeightOneSpectrum (𝓞 E)} {N N' : ℕ} (h : N ≤ N') {w : GL (Fin n) (AfE F E)} (hw : Deep P N' w) :
    Deep P N w :=
  ⟨hw.1, fun r s => (hw.2 r s).trans (WithZero.exp_le_exp.2 (by omega))⟩

/- English proof (translation)
Substitute `hM` using the available equality. Use `⟨fun P' h1 h2 a b => ?_, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[extGL_val]`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b`. Simplify using `[extM_last_last]`.

Rewrite using `[extM_last_castSucc, if_neg (Fin.castSucc_lt_last j).ne', map_zero]`. Rewrite using `[extM_castSucc_last, if_neg (Fin.castSucc_lt_last i).ne, map_zero]`. Rewrite using `[extM_castSucc, hw.1 P' h1 h2]`. Simplify using `[Fin.castSucc_inj]`. Rewrite using `[extGL_val]`.

Apply the tactic sequence `refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b`. Simplify using `[extM_last_last]`. Rewrite using `[extM_last_castSucc, Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne']`. Simplify using the standard rewrite rules. Rewrite using `[extM_castSucc_last, Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne]`.

Simplify using the standard rewrite rules. Use `hw.2 i j` as an intermediate fact. Rewrite using `[extM_castSucc]`. Simplify `this` using `[Matrix.one_apply, Fin.castSucc_inj]`.
-/
theorem Deep.ext {n M : ℕ} (hM : M = n + 1) {P : HeightOneSpectrum (𝓞 E)} {N : ℕ} {w : GL (Fin n) (AfE F E)} (hw : Deep P N w) :
    Deep P N (extGL hM w) := by
  subst hM
  refine ⟨fun P' h1 h2 a b => ?_, fun a b => ?_⟩
  · rw [extGL_val]
    refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
    · simp [extM_last_last]
    · rw [extM_last_castSucc, if_neg (Fin.castSucc_lt_last j).ne', map_zero]
    · rw [extM_castSucc_last, if_neg (Fin.castSucc_lt_last i).ne, map_zero]
    · rw [extM_castSucc, hw.1 P' h1 h2]
      simp [Fin.castSucc_inj]
  · rw [extGL_val]
    refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
    · simp [extM_last_last]
    · rw [extM_last_castSucc, Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne']
      simp
    · rw [extM_castSucc_last, Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne]
      simp
    · have := hw.2 i j
      rw [extM_castSucc]
      simpa [Matrix.one_apply, Fin.castSucc_inj] using this

/- English proof (translation)
Take `⟨N, hN⟩` from `Opn.exists_depth_step hc hJ S P (P.under (𝓞 F)) rfl`. Substitute `hJ` using the available equality. Use `⟨N, fun w hw hd => hN w hw (fun v' hv' => ?_) fun r s => (AdelicValuationDictionary.entry_iff P hq N w r s).2 (hd.2 r s)⟩` and prove the remaining obligations. Use `AdPlace.bc_prV_eq_one_of_adAt _ _ _ v' w fun P' hP' => hd.1 P' (fun e => hv' ?_) fun e => hv' ?_` and prove the remaining obligations. Rewrite using `[← hP', e]`.

Rewrite using `[← hP', e, hu]`.
-/
theorem exists_deep (hc : CMData F E) {n T f : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1)
    {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E hc.sig J T f bad) (P : HeightOneSpectrum (𝓞 E))
    (hq : Valued.v ((qOf P : ℕ) : P.adicCompletion E) = WithZero.exp (-1 : ℤ))
    (hu : (conjPrime₂ P).under (𝓞 F) = P.under (𝓞 F)) :
    ∃ N : ℕ, ∀ w ∈ UAd hc n, Deep P N w → w ∈ S.U := by
  obtain ⟨N, hN⟩ := Opn.exists_depth_step hc hJ S P (P.under (𝓞 F)) rfl
  subst hJ
  refine ⟨N, fun w hw hd => hN w hw (fun v' hv' => ?_) fun r s => (AdelicValuationDictionary.entry_iff P hq N w r s).2 (hd.2 r s)⟩
  refine AdPlace.bc_prV_eq_one_of_adAt _ _ _ v' w fun P' hP' => hd.1 P' (fun e => hv' ?_) fun e => hv' ?_
  · rw [← hP', e]
  · rw [← hP', e, hu]

/- English proof (translation)
It suffices to establish `h : ∀ S : Finset (HeightOneSpectrum (𝓞 E)), S ⊆ Q → ∃ z ∈ H, ∀ P ∈ S, ∃ γ : GL (Fin n) E, Matrix.GeneralLinearGroup.map (adAt F P) (g * z) = Matrix.GeneralLinearGroup.map (algebraMap E (P.adicCompletion E)) γ by`. Take `⟨z, hz, h⟩` from `h Q subset_rfl`. Use `⟨z, hz, fun P hP => ?_⟩` and prove the remaining obligations. Take `⟨γ, hγ⟩` from `h P hP`. Conclude with `⟨γ, fun r s => congrArg (fun x : GL (Fin n) (P.adicCompletion E) => x.1 r s) hγ⟩`.

Introduce `S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact fun _ => ⟨1, H.one_mem, fun P hP => absurd hP (Finset.notMem_empty _)⟩`. Consider the case `insert P S hPS ih`. Introduce `hS`.

Take `⟨z, hz, hzS⟩` from `ih ((Finset.subset_insert _ _).trans hS)`. Establish `hPQ : P ∈ Q` using `hS (Finset.mem_insert_self _ _)`. Take `⟨N, hN⟩` from `hH P hPQ`. Take `⟨π, hπ⟩` from `HeightOneSpectrum.valuation_exists_uniformizer (K := E) P`. Take `⟨M, γ, hM1, -, hM3⟩` from `OnePrime.exists_root_rat E P n m N hm (algebraMap E _ π) ((AdelicValuationDictionary.vAlg P π).trans hπ) (Matrix.GeneralLinearGroup.map (adAt F P) (g * z)) 1`.

Establish `hne : conjPrime₂ P ≠ P` using `fun e => hQ P hPQ (by rw [e]; exact hPQ)`. Take `⟨w, hw, hw1, hw2⟩` from `AdLift.exists_unitary hc hne M`. Establish `hd : Deep P N w` using `⟨hw1, fun r s => by rw [hw2]; exact hM1 r s⟩`. Use `⟨z * w ^ m, H.mul_mem hz (hN w hw hd), fun P' hP' => ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, map_mul, map_pow]`.

Break down `Finset.mem_insert.1 hP' with rfl | hP'S` into its components or cases. Establish `e : Matrix.GeneralLinearGroup.map (adAt F P') w = M` using `Units.ext (Matrix.ext hw2)`. Rewrite using `[e]`. Conclude with `⟨γ, (mul_one _).symm.trans hM3⟩`. Establish `e : Matrix.GeneralLinearGroup.map (adAt F P') w = 1` using `Units.ext (Matrix.ext fun i j => by`.

Rewrite using `[Units.val_one, Matrix.one_apply]`. Conclude with `hw1 P' (fun e => hPS (e ▸ hP'S)) (fun e => hQ P hPQ (e ▸ hS (Finset.mem_insert_of_mem hP'S))) i j)`. Rewrite using `[e, one_pow, mul_one]`. Conclude with `hzS P' hP'S`.
-/
theorem exists_rat (hc : CMData F E) {n m : ℕ} (hm : 0 < m) (Q : Finset (HeightOneSpectrum (𝓞 E))) (hQ : ∀ P ∈ Q, conjPrime₂ P ∉ Q)
    (H : Subgroup (GL (Fin n) (AfE F E))) (hH : ∀ P ∈ Q, ∃ N : ℕ, ∀ w ∈ UAd hc n, Deep P N w → w ^ m ∈ H)
    (g : GL (Fin n) (AfE F E)) :
    ∃ z ∈ H, ∀ P ∈ Q, ∃ γ : GL (Fin n) E, ∀ r s, adAt F P ((g * z).1 r s) = algebraMap E (P.adicCompletion E) (γ.1 r s) := by
  classical
  suffices h : ∀ S : Finset (HeightOneSpectrum (𝓞 E)), S ⊆ Q → ∃ z ∈ H, ∀ P ∈ S, ∃ γ : GL (Fin n) E,
      Matrix.GeneralLinearGroup.map (adAt F P) (g * z) = Matrix.GeneralLinearGroup.map (algebraMap E (P.adicCompletion E)) γ by
    obtain ⟨z, hz, h⟩ := h Q subset_rfl
    refine ⟨z, hz, fun P hP => ?_⟩
    obtain ⟨γ, hγ⟩ := h P hP
    exact ⟨γ, fun r s => congrArg (fun x : GL (Fin n) (P.adicCompletion E) => x.1 r s) hγ⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact fun _ => ⟨1, H.one_mem, fun P hP => absurd hP (Finset.notMem_empty _)⟩
  | insert P S hPS ih =>
    intro hS
    obtain ⟨z, hz, hzS⟩ := ih ((Finset.subset_insert _ _).trans hS)
    have hPQ : P ∈ Q := hS (Finset.mem_insert_self _ _)
    obtain ⟨N, hN⟩ := hH P hPQ
    obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer (K := E) P
    obtain ⟨M, γ, hM1, -, hM3⟩ := OnePrime.exists_root_rat E P n m N hm (algebraMap E _ π) ((AdelicValuationDictionary.vAlg P π).trans hπ)
      (Matrix.GeneralLinearGroup.map (adAt F P) (g * z)) 1
    have hne : conjPrime₂ P ≠ P := fun e => hQ P hPQ (by rw [e]; exact hPQ)
    obtain ⟨w, hw, hw1, hw2⟩ := AdLift.exists_unitary hc hne M
    have hd : Deep P N w := ⟨hw1, fun r s => by rw [hw2]; exact hM1 r s⟩
    refine ⟨z * w ^ m, H.mul_mem hz (hN w hw hd), fun P' hP' => ?_⟩
    rw [← mul_assoc, map_mul, map_pow]
    rcases Finset.mem_insert.1 hP' with rfl | hP'S
    · have e : Matrix.GeneralLinearGroup.map (adAt F P') w = M := Units.ext (Matrix.ext hw2)
      rw [e]
      exact ⟨γ, (mul_one _).symm.trans hM3⟩
    · have e : Matrix.GeneralLinearGroup.map (adAt F P') w = 1 := Units.ext (Matrix.ext fun i j => by
        rw [Units.val_one, Matrix.one_apply]
        exact hw1 P' (fun e => hPS (e ▸ hP'S)) (fun e => hQ P hPQ (e ▸ hS (Finset.mem_insert_of_mem hP'S))) i j)
      rw [e, one_pow, mul_one]
      exact hzS P' hP'S

end Gen

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Establish `hp' : PtOf (ratAd B.host.F (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹ * (g * k (chOf c))) _` using `isPtOf_rat hp (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹`. Set `κ0 : (I.stp u a B.R.m).G c.1` to `(1, m.2.1, m.2.2)`. Establish `hgam : (I.stp u a B.R.m).gam c.1 κ0 = 1` using `map_one (ufGL B.fields.E (B.R.N B.R.m))`. Establish `hact : ((I.stp u a B.R.m).act c.1 κ0 ((I.stp u a B.R.m).rep c)).1.1 = (((m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹, 1, 1) : UF B.fields.E (B.R.N B.R.m) × GLG B.fields.E (B.R.N B.R.m) (B.primes X).vGs × GLQ B.fields.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).act c.1 m ((I.stp u a B. …`. Establish `e1 : FrmG.incl _ _ m • ((I.stp u a B.R.m).rep c).1.1 = ((I.stp u a B.R.m).act c.1 m ((I.stp u a B.R.m).rep c)).1.1` using `rfl`.

Rewrite using `[← e1]`. Use `Eq.trans ?_ (smul_smul _ _ _).symm` and prove the remaining obligations. Establish `e2 : FrmG.incl (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) B.R.m c.1) (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) B.R.m c.1) κ0 = (((m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹, 1, 1) : UF B.fields.E (B.R.N B.R.m) × GLG B.fields.E (B.R.N B.R.m) (B.primes X).vGs × GLQ B.fields.E (B.R.N B.R …`. Use `Prod.ext ?_ (Prod.ext ?_ ?_)` and prove the remaining obligations. Conclude with `(inv_mul_cancel _).symm`.

Conclude with `(one_mul _).symm`. Conclude with `(one_mul _).symm`. Conclude with `congrArg (fun t => t • ((I.stp u a B.R.m).rep c).1.1) e2`. Establish `hcos : cosetIn ((I.stp u a B.R.m).act c.1 κ0 ((I.stp u a B.R.m).rep c)) = cosetIn ((I.stp u a B.R.m).rep c)` using `GlobalTheory.Mem.Col2.ChEx.cos_of_neT I (by omega) _ _`. Take `⟨x, hx⟩ : ∃ x : GA B (B.R.N B.R.m), x = (y c)⁻¹ * ratAd B.host.F (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹ * g` from `⟨_, rfl⟩`.

Establish `hxk : y c * x * k (chOf c) = ratAd B.host.F (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹ * (g * k (chOf c))`. Rewrite using `[hx]`. Use `group`. Establish `hq : PtOf (y c * x * k (chOf c)) ((I.stp u a B.R.m).act c.1 κ0 ((I.stp u a B.R.m).rep c)).1.1`. Rewrite using `[hxk, hact]`.

Conclude with `hp'`. Establish `hxU : x ∈ U (chOf c)` using `(hR.lev c x _ hq).2 ⟨κ0, hgam, rfl, hcos⟩`. Establish `hchr` using `hR.chr c ⟨x, hxU⟩ κ0 hgam hq`. Use `⟨⟨x, hxU⟩⁻¹, ?_, ?_⟩` and prove the remaining obligations. Establish `e : ratAd B.host.F (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹ = (bc (inclE (F` using `B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stp u a B.R.m).gam c.1 m))⁻¹ := by`.

Unfold `ratAd`. Rewrite using `[map_inv, map_inv]`. Both sides reduce to the same expression. Use `show _ = g * x⁻¹`. Rewrite using `[hx, e]`.

Use `group`. Rewrite using `[map_inv, inv_inv]`. Conclude with `hchr`.
-/
theorem exists_ka (u : B.Word) (a : I.ι) {Ch : Type} {chOf : (I.stp u a B.R.m).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E)}
    {U : Ch → Subgroup (GA B (B.R.N B.R.m))} {chi : ∀ β, U β →* ℂˣ} {y : (I.stp u a B.R.m).Cl → GA B (B.R.N B.R.m)}
    {st : ∀ c, (I.stp u a B.R.m).Stab c → GL (Fin (B.R.N B.R.m)) B.host.E} {k : Ch → GA B (B.R.N B.R.m)}
    (hR : I.Reads u a B.R.m chOf Lb U chi y st k) (c : (I.stp u a B.R.m).Cl) (g : GA B (B.R.N B.R.m))
    (m : (I.stp u a B.R.m).G c.1)
    (hp : PtOf (g * k (chOf c)) ((I.stp u a B.R.m).act c.1 m ((I.stp u a B.R.m).rep c)).1.1) :
    ∃ κ : U (chOf c),
      bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stp u a B.R.m).gam _ m) * y c = g * κ.1 ∧
      (((chi _ κ)⁻¹ : ℂˣ) : ℂ) = B.embLL (((I.stp u a B.R.m).chr _ m : B.LLˣ) : B.LL) := by
  have hp' : PtOf (ratAd B.host.F (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹ * (g * k (chOf c))) _ :=
    isPtOf_rat hp (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹
  let κ0 : (I.stp u a B.R.m).G c.1 := (1, m.2.1, m.2.2)
  have hgam : (I.stp u a B.R.m).gam c.1 κ0 = 1 := map_one (ufGL B.fields.E (B.R.N B.R.m))
  have hact : ((I.stp u a B.R.m).act c.1 κ0 ((I.stp u a B.R.m).rep c)).1.1 =
      (((m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹, 1, 1) :
        UF B.fields.E (B.R.N B.R.m) × GLG B.fields.E (B.R.N B.R.m) (B.primes X).vGs × GLQ B.fields.E (B.R.N B.R.m) (I.Q a)) •
        ((I.stp u a B.R.m).act c.1 m ((I.stp u a B.R.m).rep c)).1.1 := by
    have e1 : FrmG.incl _ _ m • ((I.stp u a B.R.m).rep c).1.1 = ((I.stp u a B.R.m).act c.1 m ((I.stp u a B.R.m).rep c)).1.1 := rfl
    rw [← e1]
    refine Eq.trans ?_ (smul_smul _ _ _).symm
    have e2 : FrmG.incl (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) B.R.m c.1)
        (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) B.R.m c.1) κ0 =
        (((m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹, 1, 1) :
        UF B.fields.E (B.R.N B.R.m) × GLG B.fields.E (B.R.N B.R.m) (B.primes X).vGs × GLQ B.fields.E (B.R.N B.R.m) (I.Q a)) *
        FrmG.incl _ _ m := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · exact (inv_mul_cancel _).symm
      · exact (one_mul _).symm
      · exact (one_mul _).symm
    exact congrArg (fun t => t • ((I.stp u a B.R.m).rep c).1.1) e2
  have hcos : cosetIn ((I.stp u a B.R.m).act c.1 κ0 ((I.stp u a B.R.m).rep c)) = cosetIn ((I.stp u a B.R.m).rep c) :=
    GlobalTheory.Mem.Col2.ChEx.cos_of_neT I (by omega) _ _
  obtain ⟨x, hx⟩ : ∃ x : GA B (B.R.N B.R.m), x = (y c)⁻¹ * ratAd B.host.F (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹ * g := ⟨_, rfl⟩
  have hxk : y c * x * k (chOf c) = ratAd B.host.F (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹ * (g * k (chOf c)) := by
    rw [hx]; group
  have hq : PtOf (y c * x * k (chOf c)) ((I.stp u a B.R.m).act c.1 κ0 ((I.stp u a B.R.m).rep c)).1.1 := by
    rw [hxk, hact]
    exact hp'
  have hxU : x ∈ U (chOf c) := (hR.lev c x _ hq).2 ⟨κ0, hgam, rfl, hcos⟩
  have hchr := hR.chr c ⟨x, hxU⟩ κ0 hgam hq
  refine ⟨⟨x, hxU⟩⁻¹, ?_, ?_⟩
  · have e : ratAd B.host.F (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹ =
        (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stp u a B.R.m).gam c.1 m))⁻¹ := by
      unfold ratAd
      rw [map_inv, map_inv]
      rfl
    show _ = g * x⁻¹
    rw [hx, e]
    group
  · rw [map_inv, inv_inv]
    exact hchr

set_option maxHeartbeats 3200000 in

/- English proof (translation)
Take `⟨κ', hg, hact⟩` from `(hK.lev c x.1 q hq).1 x.2`. Establish `hchr` using `hK.chr c x κ' hg (hact ▸ hq)`. Establish `hm` using `(I.stp u a B.R.m).mv_smul (I.perIn u a).b0 ((I.perIn u a).tilPt c)`. Take `⟨m, hmm⟩ : ∃ m, m = (I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)` from `⟨_, rfl⟩`. Rewrite `hm` using `[← hmm]`.

Establish `hm1 : ((I.stp u a B.R.m).act (I.perIn u a).b0 m ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c))).1.1 = tilF (Pr` using `B.primes X) (R := B.R) I.sel (I.tup a) u ((I.stX a).rep c).1.1 := congrArg (fun d : (I.stp u a B.R.m).D (I.perIn u a).b0 => d.1.1) hm`. Establish `hts` using `(l.per u a).til_smul c.1 κ' ((I.stX a).rep c)`. Establish `hm2' : (I.stp u a B.R.m).act (I.perIn u a).b0 ((I.perIn u a).ext c.1 κ' * m) ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c)) = (I.perIn u a).til c.1 ((I.stX a).act c.1 κ' ((I.stX a).rep c))`. Use `Eq.trans ?_ hts.symm` and prove the remaining obligations. Use `(@mul_smul _ _ _ ((I.stp u a B.R.m).actD (I.perIn u a).b0).toSemigroupAction _ _ _).trans ?_` and prove the remaining obligations.

Conclude with `congrArg ((I.stp u a B.R.m).act (I.perIn u a).b0 ((I.perIn u a).ext c.1 κ')) hm`. Establish `hm2 : ((I.stp u a B.R.m).act (I.perIn u a).b0 ((I.perIn u a).ext c.1 κ' * m) ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c))).1.1 = tilF (Pr` using `B.primes X) (R := B.R) I.sel (I.tup a) u q := by`. Rewrite using `[hm2', ← hact]`. Both sides reduce to the same expression. Take `⟨κ₁, e₁, c₁⟩` from `exists_ka I u a hR ((I.perIn u a).tilC c) (extGL (N_m_succ B.R) (y' c)) m (by have h := hT (chOf ((I.perIn u a).tilC c)) _ _ (hK.pt c); rw [← hm1] at h; exact h)`.

Take `⟨κ₂, e₂, c₂⟩` from `exists_ka I u a hR ((I.perIn u a).tilC c) (extGL (N_m_succ B.R) (y' c * x.1)) ((I.perIn u a).ext c.1 κ' * m) (by have h := hT (chOf ((I.perIn u a).tilC c)) _ _ hq; rw [← hm2] at h; exact h)`. Establish `hg1 : (I.stp u a B.R.m).gam (I.perIn u a).b0 ((I.perIn u a).ext c.1 κ') = 1`. Establish `h1` using `TwP.eq_extM_of_laws (N_m_succ B.R) _ _ (fun z => (l.per u a).gam_ini c.1 κ' z) (fun z => (l.per u a).gam_last c.1 κ' z)`. Establish `h2 : ((I.perIn u a).S'.gam c.1 κ').1 = 1` using `congrArg Units.val hg`. Rewrite `h1` using `[h2, extM_one]`.

Conclude with `Units.ext h1`. Establish `hg2 : (I.stp u a B.R.m).gam (I.perIn u a).b0 ((I.perIn u a).ext c.1 κ' * m) = (I.stp u a B.R.m).gam (I.perIn u a).b0 m`. Rewrite using `[map_mul, hg1, one_mul]`. Establish `e₃ : extGL (N_m_succ B.R) (y' c) * κ₁.1 = extGL (N_m_succ B.R) (y' c * x.1) * κ₂.1` using `e₁.symm.trans ((congrArg (fun t => bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) t * y ((I.perIn u a).tilC c)) hg2).symm.trans e₂)`. Establish `e₄ : extGL (N_m_succ B.R) x.1 = (κ₁ * κ₂⁻¹).1`.

Rewrite `e₃` using `[map_mul, mul_assoc]`. Use `show _ = κ₁.1 * κ₂.1⁻¹`. Rewrite using `[mul_left_cancel e₃, mul_inv_cancel_right]`. Establish `c₃ : (I.stp u a B.R.m).chr (I.perIn u a).b0 ((I.perIn u a).ext c.1 κ' * m) = (I.stX a).chr c.1 κ' * (I.stp u a B.R.m).chr (I.perIn u a).b0 m`. Rewrite using `[map_mul]`.

Conclude with `congrArg (· * (I.stp u a B.R.m).chr (I.perIn u a).b0 m) ((l.per u a).chr_ext c.1 κ')`. Establish `c₄ : (chi _ κ₂)⁻¹ = chi' x * (chi _ κ₁)⁻¹`. Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul, c₁, c₂, hchr, ← map_mul, ← Units.val_mul]`. Conclude with `congrArg (fun t : B.LLˣ => B.embLL (t : B.LL)) c₃`.

Use `⟨e₄ ▸ (κ₁ * κ₂⁻¹).2, ?_⟩` and prove the remaining obligations. Establish `e₅ : (⟨extGL (N_m_succ B.R) x.1, e₄ ▸ (κ₁ * κ₂⁻¹).2⟩ : U (chOf ((I.perIn u a).tilC c))) = κ₁ * κ₂⁻¹` using `Subtype.ext e₄`. Rewrite using `[e₅, map_mul, map_inv, c₄, mul_comm (chi' x), mul_inv_cancel_left]`.
-/
theorem ext_mem_of_pt (l : I.Laws) (u : B.Word) (a : I.ι) {Ch : Type} {chOf : (I.stp u a B.R.m).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E)}
    {U : Ch → Subgroup (GA B (B.R.N B.R.m))} {chi : ∀ β, U β →* ℂˣ} {y : (I.stp u a B.R.m).Cl → GA B (B.R.N B.R.m)}
    {st : ∀ c, (I.stp u a B.R.m).Stab c → GL (Fin (B.R.N B.R.m)) B.host.E} {k : Ch → GA B (B.R.N B.R.m)}
    (hR : I.Reads u a B.R.m chOf Lb U chi y st k)
    (hT : ∀ β (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)), PtOf g' d →
      PtOf (extGL (N_m_succ B.R) g' * k β) (tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d))
    {Lb' U' chi' y' lat' st'} (hK : I.ReadsP a Lb' U' chi' y' lat' st') (c : (I.stX a).Cl) (x : U')
    (q : XPt (B.primes X) B.R I.sel (I.tup a)) (hq : PtOf (y' c * x.1) q) :
    ∃ h : extGL (N_m_succ B.R) x.1 ∈ U (chOf ((I.perIn u a).tilC c)), chi _ ⟨_, h⟩ = chi' x := by
  obtain ⟨κ', hg, hact⟩ := (hK.lev c x.1 q hq).1 x.2
  have hchr := hK.chr c x κ' hg (hact ▸ hq)
  have hm := (I.stp u a B.R.m).mv_smul (I.perIn u a).b0 ((I.perIn u a).tilPt c)
  obtain ⟨m, hmm⟩ : ∃ m, m = (I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c) := ⟨_, rfl⟩
  rw [← hmm] at hm
  have hm1 : ((I.stp u a B.R.m).act (I.perIn u a).b0 m ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c))).1.1 =
      tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u ((I.stX a).rep c).1.1 :=
    congrArg (fun d : (I.stp u a B.R.m).D (I.perIn u a).b0 => d.1.1) hm
  have hts := (l.per u a).til_smul c.1 κ' ((I.stX a).rep c)
  have hm2' : (I.stp u a B.R.m).act (I.perIn u a).b0 ((I.perIn u a).ext c.1 κ' * m) ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c)) =
      (I.perIn u a).til c.1 ((I.stX a).act c.1 κ' ((I.stX a).rep c)) := by
    refine Eq.trans ?_ hts.symm
    refine (@mul_smul _ _ _ ((I.stp u a B.R.m).actD (I.perIn u a).b0).toSemigroupAction _ _ _).trans ?_
    exact congrArg ((I.stp u a B.R.m).act (I.perIn u a).b0 ((I.perIn u a).ext c.1 κ')) hm
  have hm2 : ((I.stp u a B.R.m).act (I.perIn u a).b0 ((I.perIn u a).ext c.1 κ' * m) ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c))).1.1 =
      tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u q := by
    rw [hm2', ← hact]
    rfl
  obtain ⟨κ₁, e₁, c₁⟩ := exists_ka I u a hR ((I.perIn u a).tilC c) (extGL (N_m_succ B.R) (y' c)) m
    (by have h := hT (chOf ((I.perIn u a).tilC c)) _ _ (hK.pt c); rw [← hm1] at h; exact h)
  obtain ⟨κ₂, e₂, c₂⟩ := exists_ka I u a hR ((I.perIn u a).tilC c) (extGL (N_m_succ B.R) (y' c * x.1)) ((I.perIn u a).ext c.1 κ' * m)
    (by have h := hT (chOf ((I.perIn u a).tilC c)) _ _ hq; rw [← hm2] at h; exact h)
  have hg1 : (I.stp u a B.R.m).gam (I.perIn u a).b0 ((I.perIn u a).ext c.1 κ') = 1 := by
    have h1 := TwP.eq_extM_of_laws (N_m_succ B.R) _ _ (fun z => (l.per u a).gam_ini c.1 κ' z) (fun z => (l.per u a).gam_last c.1 κ' z)
    have h2 : ((I.perIn u a).S'.gam c.1 κ').1 = 1 := congrArg Units.val hg
    rw [h2, extM_one] at h1
    exact Units.ext h1
  have hg2 : (I.stp u a B.R.m).gam (I.perIn u a).b0 ((I.perIn u a).ext c.1 κ' * m) = (I.stp u a B.R.m).gam (I.perIn u a).b0 m := by
    rw [map_mul, hg1, one_mul]
  have e₃ : extGL (N_m_succ B.R) (y' c) * κ₁.1 = extGL (N_m_succ B.R) (y' c * x.1) * κ₂.1 :=
    e₁.symm.trans ((congrArg (fun t => bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) t *
      y ((I.perIn u a).tilC c)) hg2).symm.trans e₂)
  have e₄ : extGL (N_m_succ B.R) x.1 = (κ₁ * κ₂⁻¹).1 := by
    rw [map_mul, mul_assoc] at e₃
    show _ = κ₁.1 * κ₂.1⁻¹
    rw [mul_left_cancel e₃, mul_inv_cancel_right]
  have c₃ : (I.stp u a B.R.m).chr (I.perIn u a).b0 ((I.perIn u a).ext c.1 κ' * m) =
      (I.stX a).chr c.1 κ' * (I.stp u a B.R.m).chr (I.perIn u a).b0 m := by
    rw [map_mul]
    exact congrArg (· * (I.stp u a B.R.m).chr (I.perIn u a).b0 m) ((l.per u a).chr_ext c.1 κ')
  have c₄ : (chi _ κ₂)⁻¹ = chi' x * (chi _ κ₁)⁻¹ := by
    refine Units.ext ?_
    rw [Units.val_mul, c₁, c₂, hchr, ← map_mul, ← Units.val_mul]
    exact congrArg (fun t : B.LLˣ => B.embLL (t : B.LL)) c₃
  refine ⟨e₄ ▸ (κ₁ * κ₂⁻¹).2, ?_⟩
  have e₅ : (⟨extGL (N_m_succ B.R) x.1, e₄ ▸ (κ₁ * κ₂⁻¹).2⟩ : U (chOf ((I.perIn u a).tilC c))) = κ₁ * κ₂⁻¹ := Subtype.ext e₄
  rw [e₅, map_mul, map_inv, c₄, mul_comm (chi' x), mul_inv_cancel_left]

/- English proof (translation)
Use `show P ∈ uSG _ _`. Conclude with `Finset.mem_union_right _ hP`.
-/
theorem mem_sb {a : I.ι} {P : HeightOneSpectrum (𝓞 B.fields.E)} (hP : P ∈ I.Q a) : P ∈ SBof I a := by
  classical
  show P ∈ uSG _ _
  exact Finset.mem_union_right _ hP

set_option maxHeartbeats 3200000 in

/- English proof (translation)
Take `⟨n, hn0, hn⟩` from `hn`. Take `⟨n', hn0', hn'⟩` from `hn'`. Use `haveI : NeZero (B.R.N B.R.m - 1) := ⟨by`. Use `Formalism.L2.Col.rank_X'_eq B.R` as an intermediate fact. Use `B.R.m_add_three_le_k` as an intermediate fact.

Unfold `Ranks.r at *`. Use the proof step `omega⟩`. Set `c : (I.stX a).Cl` to `⟨(), Quotient.mk'' ⟨(DecoF.base _ _ _ _ _, ∅), Set.mem_singleton _⟩⟩`. Set `H : Subgroup (GA B (B.R.N B.R.m - 1))` to `(chi'.ker.map U'.subtype) ⊓ ((chi β).ker.map (U β).subtype).comap (extGL (N_m_succ B.R))`. Establish `hQ : ∀ P ∈ I.Q a, conjPrime₂ P ∉ I.Q a` using `fun P hP hP' => GlobalTheory.Proof.NarrowJetMoments.conjP_notMem_rowSG (base_fields_primes_ok B X).1 (base_fields_primes_ok B X).2.1 hI.sel_ok hI.g_mem (mem_sb I hP) (mem_sb I hP')`.

Establish `hH : ∀ P ∈ I.Q a, ∃ N : ℕ, ∀ w ∈ UAd B.sp.cm (B.R.N B.R.m - 1), Deep (F` using `B.host.F) P N w → w ^ (n * n') ∈ H := by`. Introduce `P hP`. Take `⟨N, hN⟩` from `hd P hP`. Take `⟨N', hN'⟩` from `hd' P hP`. Use `⟨N + N', fun w hw hw' => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Use `⟨(⟨w, hN' w hw (hw'.mono (by omega))⟩ : U') ^ (n * n'), ?_, rfl⟩ show chi' _ = 1` and prove the remaining obligations. Rewrite using `[map_pow, mul_comm, pow_mul, hn', one_pow]`. Use `⟨(⟨extGL (N_m_succ B.R) w, hN _ (extGL_mem_ustd _ hw) ((hw'.mono (by omega)).ext _)⟩ : U β) ^ (n * n'), ?_, (map_pow (extGL (N_m_succ B.R)) w (n * n')).symm⟩ show chi β _ = 1` and prove the remaining obligations. Rewrite using `[map_pow, pow_mul, hn, one_pow]`. Take `⟨z, ⟨⟨z₁, hz₁, e₁⟩, ⟨z₂, hz₂, e₂⟩⟩, hz⟩` from `exists_rat B.sp.cm (Nat.mul_pos hn0 hn0') (I.Q a) hQ H hH (y' c * κ.1)`.

Establish `e₁' : z₁.1 = z` using `e₁`. Establish `e₂' : z₂.1 = extGL (N_m_succ B.R) z` using `e₂`. Establish `hz₁' : chi' z₁ = 1` using `hz₁`. Establish `hz₂' : chi β z₂ = 1` using `hz₂`. Establish `hun : y' c * (κ * z₁).1 ∈ UAd B.sp.cm (B.R.N B.R.m - 1)` using `mul_mem (hK.pt c).uni (hU' (κ * z₁).2)`.

Establish `e₃ : y' c * (κ * z₁).1 = y' c * κ.1 * z` using `by rw [← e₁', mul_assoc]; rfl`. Take `⟨q, hq⟩ : ∃ q : XPt (B.primes X) B.R I.sel (I.tup a), PtOf (y' c * (κ * z₁).1) q` from `RatFrPt.exists_isPtOf_of_rat B.sp.cm _ _ _ _ hun (by rw [e₃]; exact hz)`. Establish `key` using `ext_mem_of_pt I l u a hR hT hK c (κ * z₁) q hq`. Rewrite `key` using `[hβ]`. Take `⟨h, hc⟩` from `key`.

Establish `e₄ : extGL (N_m_succ B.R) κ.1 = ((⟨_, h⟩ : U β) * z₂⁻¹).1` using `by show _ = extGL (N_m_succ B.R) (κ.1 * z₁.1) * z₂.1⁻¹`. Rewrite using `[map_mul, e₁', e₂', mul_inv_cancel_right]`. Use `⟨e₄ ▸ ((⟨_, h⟩ : U β) * z₂⁻¹).2, ?_⟩` and prove the remaining obligations. Establish `e₅ : (⟨extGL (N_m_succ B.R) κ.1, e₄ ▸ ((⟨_, h⟩ : U β) * z₂⁻¹).2⟩ : U β) = (⟨_, h⟩ : U β) * z₂⁻¹` using `Subtype.ext e₄`. Rewrite using `[e₅, map_mul, map_inv, hc, hz₂', map_mul, hz₁', inv_one, mul_one, mul_one]`.
-/
theorem ext_mem (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) {Ch : Type} {chOf : (I.stp u a B.R.m).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E)}
    {U : Ch → Subgroup (GA B (B.R.N B.R.m))} {chi : ∀ β, U β →* ℂˣ} {y : (I.stp u a B.R.m).Cl → GA B (B.R.N B.R.m)}
    {st : ∀ c, (I.stp u a B.R.m).Stab c → GL (Fin (B.R.N B.R.m)) B.host.E} {k : Ch → GA B (B.R.N B.R.m)}
    (hR : I.Reads u a B.R.m chOf Lb U chi y st k)
    (hT : ∀ β (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)), PtOf g' d →
      PtOf (extGL (N_m_succ B.R) g' * k β) (tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d))
    {Lb' U' chi' y' lat' st'} (hK : I.ReadsP a Lb' U' chi' y' lat' st') (β : Ch) (hβ : ∀ c, chOf c = β)
    (hU' : U' ≤ UAd B.sp.cm (B.R.N B.R.m - 1))
    (hd : ∀ P ∈ I.Q a, ∃ N : ℕ, ∀ w ∈ UAd B.sp.cm (B.R.N B.R.m), Deep (F := B.host.F) P N w → w ∈ U β)
    (hd' : ∀ P ∈ I.Q a, ∃ N : ℕ, ∀ w ∈ UAd B.sp.cm (B.R.N B.R.m - 1), Deep (F := B.host.F) P N w → w ∈ U')
    (hn : ∃ n : ℕ, 0 < n ∧ ∀ κ, chi β κ ^ n = 1) (hn' : ∃ n : ℕ, 0 < n ∧ ∀ κ, chi' κ ^ n = 1) (κ : U') :
    ∃ h : extGL (N_m_succ B.R) κ.1 ∈ U β, chi β ⟨_, h⟩ = chi' κ := by
  obtain ⟨n, hn0, hn⟩ := hn
  obtain ⟨n', hn0', hn'⟩ := hn'
  haveI : NeZero (B.R.N B.R.m - 1) := ⟨by
    have := Formalism.L2.Col.rank_X'_eq B.R; have := B.R.m_add_three_le_k; unfold Ranks.r at *; omega⟩
  let c : (I.stX a).Cl := ⟨(), Quotient.mk'' ⟨(DecoF.base _ _ _ _ _, ∅), Set.mem_singleton _⟩⟩
  let H : Subgroup (GA B (B.R.N B.R.m - 1)) :=
    (chi'.ker.map U'.subtype) ⊓ ((chi β).ker.map (U β).subtype).comap (extGL (N_m_succ B.R))
  have hQ : ∀ P ∈ I.Q a, conjPrime₂ P ∉ I.Q a := fun P hP hP' =>
    GlobalTheory.Proof.NarrowJetMoments.conjP_notMem_rowSG (base_fields_primes_ok B X).1 (base_fields_primes_ok B X).2.1 hI.sel_ok hI.g_mem
      (mem_sb I hP) (mem_sb I hP')
  have hH : ∀ P ∈ I.Q a, ∃ N : ℕ, ∀ w ∈ UAd B.sp.cm (B.R.N B.R.m - 1), Deep (F := B.host.F) P N w → w ^ (n * n') ∈ H := by
    intro P hP
    obtain ⟨N, hN⟩ := hd P hP
    obtain ⟨N', hN'⟩ := hd' P hP
    refine ⟨N + N', fun w hw hw' => ⟨?_, ?_⟩⟩
    · refine ⟨(⟨w, hN' w hw (hw'.mono (by omega))⟩ : U') ^ (n * n'), ?_, rfl⟩
      show chi' _ = 1
      rw [map_pow, mul_comm, pow_mul, hn', one_pow]
    · refine ⟨(⟨extGL (N_m_succ B.R) w, hN _ (extGL_mem_ustd _ hw) ((hw'.mono (by omega)).ext _)⟩ : U β) ^ (n * n'), ?_,
        (map_pow (extGL (N_m_succ B.R)) w (n * n')).symm⟩
      show chi β _ = 1
      rw [map_pow, pow_mul, hn, one_pow]
  obtain ⟨z, ⟨⟨z₁, hz₁, e₁⟩, ⟨z₂, hz₂, e₂⟩⟩, hz⟩ := exists_rat B.sp.cm (Nat.mul_pos hn0 hn0') (I.Q a) hQ H hH (y' c * κ.1)
  have e₁' : z₁.1 = z := e₁
  have e₂' : z₂.1 = extGL (N_m_succ B.R) z := e₂
  have hz₁' : chi' z₁ = 1 := hz₁
  have hz₂' : chi β z₂ = 1 := hz₂
  have hun : y' c * (κ * z₁).1 ∈ UAd B.sp.cm (B.R.N B.R.m - 1) := mul_mem (hK.pt c).uni (hU' (κ * z₁).2)
  have e₃ : y' c * (κ * z₁).1 = y' c * κ.1 * z := by rw [← e₁', mul_assoc]; rfl
  obtain ⟨q, hq⟩ : ∃ q : XPt (B.primes X) B.R I.sel (I.tup a), PtOf (y' c * (κ * z₁).1) q :=
    RatFrPt.exists_isPtOf_of_rat B.sp.cm _ _ _ _ hun (by rw [e₃]; exact hz)
  have key := ext_mem_of_pt I l u a hR hT hK c (κ * z₁) q hq
  rw [hβ] at key
  obtain ⟨h, hc⟩ := key
  have e₄ : extGL (N_m_succ B.R) κ.1 = ((⟨_, h⟩ : U β) * z₂⁻¹).1 := by
    show _ = extGL (N_m_succ B.R) (κ.1 * z₁.1) * z₂.1⁻¹
    rw [map_mul, e₁', e₂', mul_inv_cancel_right]
  refine ⟨e₄ ▸ ((⟨_, h⟩ : U β) * z₂⁻¹).2, ?_⟩
  have e₅ : (⟨extGL (N_m_succ B.R) κ.1, e₄ ▸ ((⟨_, h⟩ : U β) * z₂⁻¹).2⟩ : U β) = (⟨_, h⟩ : U β) * z₂⁻¹ := Subtype.ext e₄
  rw [e₅, map_mul, map_inv, hc, hz₂', map_mul, hz₁', inv_one, mul_one, mul_one]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [extM, Matrix.map_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem extM_map {A A' : Type} [CommRing A] [CommRing A'] {N n : ℕ} (hN : N = n + 1) (f : A →+* A') (g : Matrix (Fin n) (Fin n) A) :
    (extM hN g).map f = extM hN (g.map f) := by
  ext a b
  simp only [extM, Matrix.map_apply]
  split_ifs <;> simp

/- English proof (translation)
Take `⟨-, -, hiX, -⟩` from `spaces_in_coordinates I hI hP l Z`. Establish `hN` using `N_m_succ B.R`. Establish `hPr` using `(base_fields_primes_ok B X).2.1`. Establish `hpi0 : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0`. Introduce `h0`.

Establish `h1 : X.piT u = 0` using `RingOfIntegers.ext h0`. Establish `h2` using `hPr.piT_norm u`. Establish `h3 : (B.primes X).piT u = 0` using `h1`. Rewrite `h2` using `[h3, zero_mul]`. Conclude with `(hPr.T_prime u).ne_zero (by exact_mod_cast h2.symm)`.

Establish `e : TC.z0 X u = z0v B X u` using `rfl`. Prove the components needed by the constructor for the conclusion. Introduce `hg'`. Use `TilX.eq_extM_of_ext hN φ hpi0 (TilX.iXm_apply hiX hN) hg'.1 ?_` and prove the remaining obligations. Establish `h2` using `hg'.2`.

Rewrite `h2` using `[e, lastCoordinateUniformizerVector_eq_single u]`. Conclude with `h2`. Introduce and unpack `rfl`. Use `⟨TwP.extM_mul_incl hN g' _ fun b j => ?_, TwP.extM_mulVec_fix hN g' _ fun b hb => ?_⟩` and prove the remaining obligations. Use `(congrArg φ (TilX.iXm_apply hiX hN b j)).trans ?_` and prove the remaining obligations.

Distinguish the cases in `h : b = Br.iC hN j`. Rewrite using `[if_pos h]`. Conclude with `(congrArg φ (if_pos h)).trans φ.map_one`. Rewrite using `[if_neg h]`. Conclude with `(congrArg φ (if_neg h)).trans φ.map_zero`.

Use `show φ (TC.z0 X u b) = 0`. Rewrite using `[e, lastCoordinateUniformizerVector_eq_single, Pi.single_eq_of_ne hb]`. Conclude with `φ.map_zero`.
-/
theorem isExt_iff (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {R' : Type} [CommRing R']
    (φ : (I.rec7 l Z).host.E →+* R') (g' : Matrix (Fin (B.R.N B.R.m - 1)) (Fin (B.R.N B.R.m - 1)) R')
    (g : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) R') :
    IsExt (I.rec7 l Z) (z0 X u) φ g' g ↔ g = extM (N_m_succ B.R) g' := by
  obtain ⟨-, -, hiX, -⟩ := spaces_in_coordinates I hI hP l Z
  have hN := N_m_succ B.R
  have hPr := (base_fields_primes_ok B X).2.1
  have hpi0 : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := by
    intro h0
    have h1 : X.piT u = 0 := RingOfIntegers.ext h0
    have h2 := hPr.piT_norm u
    have h3 : (B.primes X).piT u = 0 := h1
    rw [h3, zero_mul] at h2
    exact (hPr.T_prime u).ne_zero (by exact_mod_cast h2.symm)
  have e : TC.z0 X u = z0v B X u := rfl
  constructor
  · intro hg'
    refine TilX.eq_extM_of_ext hN φ hpi0 (TilX.iXm_apply hiX hN) hg'.1 ?_
    have h2 := hg'.2
    rw [e, lastCoordinateUniformizerVector_eq_single u] at h2
    exact h2
  · rintro rfl
    refine ⟨TwP.extM_mul_incl hN g' _ fun b j => ?_, TwP.extM_mulVec_fix hN g' _ fun b hb => ?_⟩
    · refine (congrArg φ (TilX.iXm_apply hiX hN b j)).trans ?_
      by_cases h : b = Br.iC hN j
      · rw [if_pos h]
        exact (congrArg φ (if_pos h)).trans φ.map_one
      · rw [if_neg h]
        exact (congrArg φ (if_neg h)).trans φ.map_zero
    · show φ (TC.z0 X u b) = 0
      rw [e, lastCoordinateUniformizerVector_eq_single, Pi.single_eq_of_ne hb]
      exact φ.map_zero

/- English proof (translation)
Introduce `P hP` and use `exists_deep (I.rec7 l Z).sp.cm hJ S P (AdelicValuationDictionary.main I hI l Z a n 0 ⟨P, mem_sb I hP⟩ 1).2.1 ((under_eq_iff B.host P _).2 (Or.inr rfl))`.
-/
theorem deep_twist (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) {n T f : ℕ}
    {J : Matrix (Fin n) (Fin n) (I.rec7 l Z).host.E} (hJ : J = 1) {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))}
    (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) J T f bad) :
    ∀ P ∈ I.Q a, ∃ N : ℕ, ∀ w ∈ UAd B.sp.cm n, Deep (F := B.host.F) P N w → w ∈ S.U := fun P hP =>
  exists_deep (I.rec7 l Z).sp.cm hJ S P (AdelicValuationDictionary.main I hI l Z a n 0 ⟨P, mem_sb I hP⟩ 1).2.1
    ((under_eq_iff B.host P _).2 (Or.inr rfl))

end Mat

section Main
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Substitute `hn` using the available equality. Conclude with `Units.ext_iff`.
-/
theorem mem_GfC_iff {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) :
    g ∈ GfC V ↔ ((mt V g).reindex (finCongr hn) (finCongr hn)).map (infPart D) = 1 := by
  subst hn
  exact Units.ext_iff

/- English proof (translation)
Use extensionality with `i j`. Establish `a` using `hy.2 ((finCongr (rankP D)).symm i) ((finCongr (rankP D)).symm j)`. Simplify using `only [Equiv.apply_symm_apply] at a`. Conclude with `a`.
-/
theorem finM_of_hasMat {D : D7} {h : GA D D.sp.X'} {y} (hy : GlobalTheory.Core.Rk.Top.HasMat h y) :
    ((mt _ h).reindex (finCongr (rankP D)) (finCongr (rankP D))).map (toEAf D) = y.1 := by
  ext i j
  have a := hy.2 ((finCongr (rankP D)).symm i) ((finCongr (rankP D)).symm j)
  simp only [Equiv.apply_symm_apply] at a
  exact a

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `B X I hI hP l Z u a Ch₀ A hA emb hemb bad K hK hfin β h κ hh`. Take `⟨-, gP, -, hsp⟩` from `TC.spaces_in_coordinates I hI hP l Z`. Establish `gN` using `(hsp B.R.m le_rfl).1`. Establish `hU' : K.lev.U ≤ Formalism.L2.Col.UAd B.sp.cm (B.R.N B.R.m - 1)` using `fun x hx => by`. Establish `h1` using `((K.lev.U_eq x).1 hx).1`.

Rewrite `h1` using `[gP]`. Conclude with `h1`. Take `⟨hm, hc⟩` from `ext_mem I hI l u a (hA.reads B.R.m le_rfl) (fun b d g' hd => hA.top b d g' _ hd ((isExt_iff I hI hP l Z u _ _ _).2 rfl)) hK β (fun c => TwDat.Is.chOf_top_eq I hI hP l Z u a Ch₀ A hA c β) hU' (deep_twist I hI l Z a gN (A.K B.R.m le_rfl β).lev) (deep_twist I hI l Z a gP K.lev) (hA. …`. Establish `he` using `(isExt_iff I hI hP l Z u _ _ _).1 (hemb h)`. Establish `hG : emb h ∈ GfC _`.

Use `(mem_GfC_iff _ (rankN (I.rec7 l Z) B.R.m le_rfl) _).2 ?_` and prove the remaining obligations. Use `(congrArg (fun M => Matrix.map M (infPart (I.rec7 l Z))) he).trans ((extM_map _ _ _).trans ?_)` and prove the remaining obligations. Conclude with `(congrArg (TilX.extM _) ((mem_GfC_iff _ (rankP (I.rec7 l Z)) _).1 hh.1)).trans (TilX.extM_one _)`. Establish `hF : (TilX.extGL (Formalism.L2.Col.N_m_succ B.R) κ.1).1 = finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb h)`. Use `Eq.symm ((congrArg (fun M => Matrix.map M (toEAf (I.rec7 l Z))) he).trans ((extM_map _ _ _).trans ?_))` and prove the remaining obligations.

Conclude with `congrArg (TilX.extM _) (finM_of_hasMat hh)`. Establish `hU : emb h ∈ A.U B.R.m β` using `(hA.U B.R.m le_rfl β _).2 ⟨hG, ⟨_, hm⟩, hF⟩`. Establish `e : A.chi B.R.m β ⟨emb h, hU⟩ = K.lev.chi κ` using `(hA.chi B.R.m le_rfl β ⟨emb h, hU⟩ ⟨_, hm⟩ hF).trans hc`. Conclude with `⟨hU, e, e ▸ hA.norm_chi B.R.m le_rfl β _⟩`.
-/
theorem emb_mem_chi : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → ∀ emb : GA (I.rec7 l Z) (I.rec7 l Z).sp.X' →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m), IsEmbTop (D := (I.rec7 l Z)) (TC.z0 X u) emb → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∃ n : ℕ, 0 < n ∧ ∀ κ, K.lev.chi κ ^ n = 1) → ∀ β h (κ : K.lev.U), GlobalTheory.Core.Rk.Top.HasMat h κ.1 → ∃ hU : emb h ∈ A.U B.R.m β, A.chi B.R.m β ⟨emb h, hU⟩ = K.lev.chi κ ∧ ‖((K.lev.chi κ : ℂˣ) : ℂ)‖ = 1 := by
  intro B X I hI hP l Z u a Ch₀ A hA emb hemb bad K hK hfin β h κ hh
  obtain ⟨-, gP, -, hsp⟩ := TC.spaces_in_coordinates I hI hP l Z
  have gN := (hsp B.R.m le_rfl).1
  have hU' : K.lev.U ≤ Formalism.L2.Col.UAd B.sp.cm (B.R.N B.R.m - 1) := fun x hx => by
    have h1 := ((K.lev.U_eq x).1 hx).1
    rw [gP] at h1
    exact h1
  obtain ⟨hm, hc⟩ := ext_mem I hI l u a (hA.reads B.R.m le_rfl)
    (fun b d g' hd => hA.top b d g' _ hd ((isExt_iff I hI hP l Z u _ _ _).2 rfl)) hK β
    (fun c => TwDat.Is.chOf_top_eq I hI hP l Z u a Ch₀ A hA c β) hU'
    (deep_twist I hI l Z a gN (A.K B.R.m le_rfl β).lev) (deep_twist I hI l Z a gP K.lev) (hA.fin B.R.m le_rfl β) hfin κ
  have he := (isExt_iff I hI hP l Z u _ _ _).1 (hemb h)
  have hG : emb h ∈ GfC _ := by
    refine (mem_GfC_iff _ (rankN (I.rec7 l Z) B.R.m le_rfl) _).2 ?_
    refine (congrArg (fun M => Matrix.map M (infPart (I.rec7 l Z))) he).trans ((extM_map _ _ _).trans ?_)
    exact (congrArg (TilX.extM _) ((mem_GfC_iff _ (rankP (I.rec7 l Z)) _).1 hh.1)).trans (TilX.extM_one _)
  have hF : (TilX.extGL (Formalism.L2.Col.N_m_succ B.R) κ.1).1 = finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb h) := by
    refine Eq.symm ((congrArg (fun M => Matrix.map M (toEAf (I.rec7 l Z))) he).trans ((extM_map _ _ _).trans ?_))
    exact congrArg (TilX.extM _) (finM_of_hasMat hh)
  have hU : emb h ∈ A.U B.R.m β := (hA.U B.R.m le_rfl β _).2 ⟨hG, ⟨_, hm⟩, hF⟩
  have e : A.chi B.R.m β ⟨emb h, hU⟩ = K.lev.chi κ := (hA.chi B.R.m le_rfl β ⟨emb h, hU⟩ ⟨_, hm⟩ hF).trans hc
  exact ⟨hU, e, e ▸ hA.norm_chi B.R.m le_rfl β _⟩

/- English proof (translation)
Set `m` to `Nat.card L.P.H * ∏ PP ∈ L.Pg ∪ L.Q, Nat.card (kP PP)ˣ`. Establish `hk : ∀ PP ∈ L.Pg ∪ L.Q, ∀ (φ : (kP PP)ˣ →* LLˣ) z, φ z ^ m = 1` using `fun PP hPP φ z => by`. Take `⟨d, hd⟩ : Nat.card (kP PP)ˣ ∣ m` from `Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hPP) _`. Rewrite using `[hd, pow_mul, ← map_pow, pow_card_eq_one', map_one, one_pow]`. Use `⟨m, Nat.mul_pos Nat.card_pos (Finset.prod_pos fun _ _ => Nat.card_pos), fun x => ?_⟩` and prove the remaining obligations.

Unfold `levFn`. Rewrite using `[mul_pow, mul_pow, ← Finset.prod_pow, ← Finset.prod_pow, Finset.prod_eq_one, Finset.prod_eq_one, mul_one, mul_one]`. Unfold `ext1 split_ifs`. Rewrite using `[pow_mul, ← map_pow, pow_card_eq_one', map_one, one_pow]`. Conclude with `one_pow _`.

Conclude with `fun PP hPP => hk PP (Finset.mem_union_right _ hPP) _ _`. Introduce `PP hPP`. Rewrite using `[← Finset.prod_pow]`. Conclude with `Finset.prod_eq_one fun c _ => hk PP (Finset.mem_union_left _ hPP) _ _`.
-/
theorem levFn_pow {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {LL : Type} [CommRing LL]
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : LevDat E LL n) : ∃ m : ℕ, 0 < m ∧ ∀ x, levFn β L x ^ m = 1 := by
  let m := Nat.card L.P.H * ∏ PP ∈ L.Pg ∪ L.Q, Nat.card (kP PP)ˣ
  have hk : ∀ PP ∈ L.Pg ∪ L.Q, ∀ (φ : (kP PP)ˣ →* LLˣ) z, φ z ^ m = 1 := fun PP hPP φ z => by
    obtain ⟨d, hd⟩ : Nat.card (kP PP)ˣ ∣ m := Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hPP) _
    rw [hd, pow_mul, ← map_pow, pow_card_eq_one', map_one, one_pow]
  refine ⟨m, Nat.mul_pos Nat.card_pos (Finset.prod_pos fun _ _ => Nat.card_pos), fun x => ?_⟩
  unfold levFn
  rw [mul_pow, mul_pow, ← Finset.prod_pow, ← Finset.prod_pow, Finset.prod_eq_one, Finset.prod_eq_one, mul_one, mul_one]
  · unfold ext1
    split_ifs
    · rw [pow_mul, ← map_pow, pow_card_eq_one', map_one, one_pow]
    · exact one_pow _
  · exact fun PP hPP => hk PP (Finset.mem_union_right _ hPP) _ _
  · intro PP hPP
    rw [← Finset.prod_pow]
    exact Finset.prod_eq_one fun c _ => hk PP (Finset.mem_union_left _ hPP) _ _

/- English proof (translation)
Take `⟨m, hm, H⟩` from `levFn_pow (F := D.host.F) β L`. Use `⟨m, hm, fun κ => ?_⟩` and prove the remaining obligations. Take `⟨g, hg⟩` from `GlobalTheory.Core.Rk.Top.Model.hasMat_exists (D := D) ⟨κ.1, ((K.lev.U_eq _).1 κ.2).1⟩`. Establish `e` using `h.2 g κ hg`. Establish `e2 : levChi _ β L (x⁻¹ * g * x) ^ m = 1`.

Unfold `levChi`. Rewrite using `[← Units.val_pow_eq_pow_val, H, Units.val_one]`. Rewrite `e2` using `[e, ← star_pow, star_eq_iff_star_eq, star_one]`. Conclude with `Units.ext (by rw [Units.val_pow_eq_pow_val, ← e2, Units.val_one])`.
-/
theorem chi_pow_of_levG {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C}
    {Pm : PeriodMap D.R C} {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm}
    {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (K : ClassesAtPrimes M bad) {x : GA D D.sp.X'} {J : Set (GA D D.sp.X')}
    {β : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ D.sp.X'.rank} (h : LevG K x J (levChi _ β L)) :
    ∃ n : ℕ, 0 < n ∧ ∀ κ, K.lev.chi κ ^ n = 1 := by
  obtain ⟨m, hm, H⟩ := levFn_pow (F := D.host.F) β L
  refine ⟨m, hm, fun κ => ?_⟩
  obtain ⟨g, hg⟩ := GlobalTheory.Core.Rk.Top.Model.hasMat_exists (D := D) ⟨κ.1, ((K.lev.U_eq _).1 κ.2).1⟩
  have e := h.2 g κ hg
  have e2 : levChi _ β L (x⁻¹ * g * x) ^ m = 1 := by
    unfold levChi
    rw [← Units.val_pow_eq_pow_val, H, Units.val_one]
  rw [e, ← star_pow, star_eq_iff_star_eq, star_one] at e2
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, ← e2, Units.val_one])

end Main

end GlobalTheory.AdForm.LevChiTop

end
