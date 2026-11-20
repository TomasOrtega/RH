import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivSupOfIsotypicPartsInternalDirectSum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HeckePin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ZeroDegreeOfPinFor
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ExistsIsHeckeSetting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
import Formalism.SharpRestriction.LevelLetterCocycles.LatticeVariant

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.NX
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SupLaw

section Coset

open GlobalTheory.HeckeParts

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

/- English proof (translation)
Use `⟨hso.1, ?_, fun PP hPP => ?_⟩` and prove the remaining obligations. Rewrite using `[one_pow, Nat.cast_one]`. Conclude with `(Ideal.ne_top_iff_one _).1 P.isPrime.ne_top`. Establish `hPP' : PP ∈ R.Pg` using `hPP.elim id fun h => absurd h (Finset.notMem_empty _)`. Establish `hS : PP ∈ (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E))` using `hSb hPP'`.

Use `⟨fun h => hso.2.1 (h ▸ hS), fun h => hso.2.2 PP hS ?_⟩` and prove the remaining obligations. Rewrite using `[Formalism.L2.Col.conjIdeal_asIdeal]`. Use `PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_` and prove the remaining obligations. Take `⟨a', ha', e⟩` from `h a ha`. Rewrite using `[Formalism.L2.Col.mem_conjP]`.

Establish `: Formalism.L2.Col.cO D.host.E a = a'` using `RingOfIntegers.ext e.symm`. Rewrite using `[this]` and apply the resulting hypothesis.
-/
theorem offPrincipalLevel (hSb : R.fam_Sb) (i : Fin D.R.m) {P : Formalism.L2.DIV.Pl D.host.E}
    (hso : Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E))) (c : ℕ) :
    OffLevel (R.datWp i R.triv) (1 ^ c) P := by
  refine ⟨hso.1, ?_, fun PP hPP => ?_⟩
  · rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  · have hPP' : PP ∈ R.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
    have hS : PP ∈ (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := hSb hPP'
    refine ⟨fun h => hso.2.1 (h ▸ hS), fun h => hso.2.2 PP hS ?_⟩
    rw [Formalism.L2.Col.conjIdeal_asIdeal]
    refine PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_
    obtain ⟨a', ha', e⟩ := h a ha
    rw [Formalism.L2.Col.mem_conjP]
    have : Formalism.L2.Col.cO D.host.E a = a' := RingOfIntegers.ext e.symm
    rwa [this]

/- English proof (translation)
Take `⟨c, hβ⟩` from `hL.βW i`. Establish `hP` using `offPrincipalLevel hSb i hso c`. Establish `hP'` using `offPrincipalLevel hSb i hso' c`. Take `⟨e, ϖ, he, -, -, hα⟩` from `ha`. Take `⟨e', ϖ', he', -, -, hα'⟩` from `ha'`.

Take `⟨⟨A₀, hA⟩, -⟩` from `exists_locRep hβ hP he hα.2.1`. Take `⟨⟨B₀, hB⟩, -⟩` from `exists_locRep hβ hP' he' hα'.2.1`. Establish `e1 : ∀ {F : GA D (Wc D i) → ℂ}, RInv (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) F → heckeLin (Wc D i) Rc F = heckeLin (Wc D i) A₀ F` using `fun hF => (dcOp_eq_rInv hR hA.2 ⟨1, 1, by simp⟩ hF).1`. Establish `e2 : ∀ {F : GA D (Wc D i) → ℂ}, RInv (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) F → heckeLin (Wc D i) Rc' F = heckeLin (Wc D i) B₀ F` using `fun hF => (dcOp_eq_rInv hR' hB.2 ⟨1, 1, by simp⟩ hF).1`. Establish `i1 : RInv (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) (heckeLin (Wc D i) A₀ F)` using `dcOp_rInv hA.2 hF`.

Establish `i2 : RInv (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) (heckeLin (Wc D i) B₀ F)` using `dcOp_rInv hB.2 hF`. Rewrite using `[e2 hF, e1 hF, e1 i2, e2 i1]`. Conclude with `hA.comm hβ hP hB hF`.
-/
theorem cosetSum_comm (hL : R.toLevCh.Is A.μ0) (hSb : R.fam_Sb) (i : Fin D.R.m) {P P' : Formalism.L2.DIV.Pl D.host.E}
    (hso : Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)))
    (hso' : Bridge.SplitOff P' (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E))) {k k' : ℕ} {α α' : GA D (Wc D i)}
    {Rc Rc' : Finset (GA D (Wc D i))} (ha : IsHeckeAt (Wc D i) P k α) (ha' : IsHeckeAt (Wc D i) P' k' α')
    (hR : Bridge.IsDC (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc)
    (hR' : Bridge.IsDC (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α' Rc') {F : GA D (Wc D i) → ℂ}
    (hF : RInv (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) F) :
    heckeLin (Wc D i) Rc (heckeLin (Wc D i) Rc' F) = heckeLin (Wc D i) Rc' (heckeLin (Wc D i) Rc F) := by
  obtain ⟨c, hβ⟩ := hL.βW i
  have hP := offPrincipalLevel hSb i hso c
  have hP' := offPrincipalLevel hSb i hso' c
  obtain ⟨e, ϖ, he, -, -, hα⟩ := ha
  obtain ⟨e', ϖ', he', -, -, hα'⟩ := ha'
  obtain ⟨⟨A₀, hA⟩, -⟩ := exists_locRep hβ hP he hα.2.1
  obtain ⟨⟨B₀, hB⟩, -⟩ := exists_locRep hβ hP' he' hα'.2.1
  have e1 : ∀ {F : GA D (Wc D i) → ℂ}, RInv (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) F →
      heckeLin (Wc D i) Rc F = heckeLin (Wc D i) A₀ F := fun hF =>
    (dcOp_eq_rInv hR hA.2 ⟨1, 1, by simp⟩ hF).1
  have e2 : ∀ {F : GA D (Wc D i) → ℂ}, RInv (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) F →
      heckeLin (Wc D i) Rc' F = heckeLin (Wc D i) B₀ F := fun hF =>
    (dcOp_eq_rInv hR' hB.2 ⟨1, 1, by simp⟩ hF).1
  have i1 : RInv (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) (heckeLin (Wc D i) A₀ F) := dcOp_rInv hA.2 hF
  have i2 : RInv (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) (heckeLin (Wc D i) B₀ F) := dcOp_rInv hB.2 hF
  rw [e2 hF, e1 hF, e1 i2, e2 i1]
  exact hA.comm hβ hP hB hF

end Coset

section Tied

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (Rl : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS Rl cG S)

/- English proof (translation)
Use `LinearMap.ext fun x => (Y.fi i).e.injective (hinj ((hW i _).1 ?_))` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) ((Y.fi i).e (t (t' x)))) = (Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) ((Y.fi i).e (t' (t x))))`. Rewrite using `[ht, ht', ht', ht, map_smul, map_smul, smul_comm]`. Use `congrArg (fun z : MMap (Rl.MW i (sg0 D A3.A)) => c' • c • z) ?_` and prove the remaining obligations. Conclude with `MultilinearMap.ext fun v => cosetSum_comm hL hSb i hso hso' ha ha' hR hR' (fun k hk h => GlobalTheory.HeckeSup.model_inv_cl hW i _ _ v k hk h)`.
-/
theorem commute_of_read (hL : Rl.toRealDat.toLevCh.Is A3.A.μ0) (hSb : Rl.toRealDat.fam_Sb) (hW : Rl.toRealDat.models_HW)
    (i : Fin D.R.m) (hinj : Function.Injective ((Rl.FW i).j (sg0 D A3.A))) {P P' : Formalism.L2.DIV.Pl D.host.E}
    (hso : Bridge.SplitOff P (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)))
    (hso' : Bridge.SplitOff P' (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E))) {k k' : ℕ} {α α' : GA D (Wc D i)}
    {Rc Rc' : Finset (GA D (Wc D i))} (ha : IsHeckeAt (Wc D i) P k α) (ha' : IsHeckeAt (Wc D i) P' k' α')
    (hR : Bridge.IsDC (levG (Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α Rc)
    (hR' : Bridge.IsDC (levG (Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α' Rc')
    {t t' : Module.End D.what₂.LL (S.WL ((i : ℕ) + 1))} {c c' : ℂ}
    (ht : ∀ x, (Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) ((Y.fi i).e (t x))) =
      c • heckeOn (Rl.MW i (sg0 D A3.A)) Rc ((Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) ((Y.fi i).e x))))
    (ht' : ∀ x, (Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) ((Y.fi i).e (t' x))) =
      c' • heckeOn (Rl.MW i (sg0 D A3.A)) Rc' ((Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) ((Y.fi i).e x)))) :
    Commute t t' := by
  refine LinearMap.ext fun x => (Y.fi i).e.injective (hinj ((hW i _).1 ?_))
  change (Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) ((Y.fi i).e (t (t' x)))) =
    (Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) ((Y.fi i).e (t' (t x))))
  rw [ht, ht', ht', ht, map_smul, map_smul, smul_comm]
  refine congrArg (fun z : MMap (Rl.MW i (sg0 D A3.A)) => c' • c • z) ?_
  exact MultilinearMap.ext fun v => cosetSum_comm hL hSb i hso hso' ha ha' hR hR'
    (fun k hk h => GlobalTheory.HeckeSup.model_inv_cl hW i _ _ v k hk h)

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Set `r : ℕ → PlE D.host → Module.End S.Ks (FmK S j)` to `fun k P => ((f k P).restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) fun x hx => hs k P x hx`. Establish `hr : r k P * r k' P' = r k' P' * r k P` using `LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun h.eq x.1)`. Unfold `hkFR Commute SemiconjBy`. Express the relevant statement in the definitionally equal form `(Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (r k P)) * (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (r k' P')) = (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (r k' P')) * (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (r k P))`. Rewrite using `[← map_mul, ← map_mul, hr]`.
-/
theorem baseChange_comm (i : D.ntw.Tw) (j : ℕ) (b : Bool) {f : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)}
    (hs : HeckeStabR S j f) (k k' : ℕ) (P P' : PlE D.host) (h : Commute (f k P) (f k' P')) :
    Commute (hkFR S i j b f hs k P) (hkFR S i j b f hs k' P') := by
  let r : ℕ → PlE D.host → Module.End S.Ks (FmK S j) := fun k P =>
    ((f k P).restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) fun x hx => hs k P x hx
  have hr : r k P * r k' P' = r k' P' * r k P := LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun h.eq x.1)
  unfold hkFR Commute SemiconjBy
  change (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (r k P)) * (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (r k' P')) =
    (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (r k' P')) * (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (r k P))
  rw [← map_mul, ← map_mul, hr]

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `i _ j hj b k P k' P' hk hk'`. Take `⟨h1, h2⟩` from `Finset.mem_Icc.1 hj`. Establish `hF` using `baseChange_comm S i j b (hs j h1 h2) k k' P P' (hc i j h1 h2 k P k' P' hk hk')`. Use `LinearMap.ext fun x => (Y.eF i j b h1 h2).injective ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Y.eF i j b h1 h2 (D.nexp.hkF i j b k P (D.nexp.hkF i j b k' P' x)) = Y.eF i j b h1 h2 (D.nexp.hkF i j b k' P' (D.nexp.hkF i j b k P x))`.

Rewrite using `[hEq i j b h1 h2 k P _ hk.2.2.2 hk.2.2.1 hk.2.1, hEq i j b h1 h2 k' P' _ hk'.2.2.2 hk'.2.2.1 hk'.2.1, hEq i j b h1 h2 k' P' _ hk'.2.2.2 hk'.2.2.1 hk'.2.1, hEq i j b h1 h2 k P _ hk.2.2.2 hk.2.2.1 hk.2.1, map_smul, map_smul, smul_comm]`. Conclude with `congrArg (fun z => c i b k' P' • c i b k P • z) (LinearMap.congr_fun hF.eq (Y.eF i j b h1 h2 x))`.
-/
theorem hkComm_of_family (f : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hs : ∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (f j))
    (c : ∀ i : D.ntw.Tw, Bool → ℕ → PlE D.host → FractionRing (D.ntw.O i))
    (hEq : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (k : ℕ) (P : PlE D.host) (x : D.nexp.Fm i j b), P ∉ D.ntw.S0 i →
      Formalism.BasicNotions.IsSplitPl D.host P → k ≤ D.R.r →
      Y.eF i j b h1 h2 (D.nexp.hkF i j b k P x) = c i b k P • hkFR S i j b (f j) (hs j h1 h2) k P (Y.eF i j b h1 h2 x))
    (hc : ∀ (i : D.ntw.Tw) j, 1 ≤ j → j ≤ D.R.m → ∀ k P k' P', Formalism.MainNotions.IntegralHeckeForms.HkIdx i k P → Formalism.MainNotions.IntegralHeckeForms.HkIdx i k' P' →
      Commute (f j k P) (f j k' P')) : HkComm D := by
  intro i _ j hj b k P k' P' hk hk'
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  have hF := baseChange_comm S i j b (hs j h1 h2) k k' P P' (hc i j h1 h2 k P k' P' hk hk')
  refine LinearMap.ext fun x => (Y.eF i j b h1 h2).injective ?_
  change Y.eF i j b h1 h2 (D.nexp.hkF i j b k P (D.nexp.hkF i j b k' P' x)) =
    Y.eF i j b h1 h2 (D.nexp.hkF i j b k' P' (D.nexp.hkF i j b k P x))
  rw [hEq i j b h1 h2 k P _ hk.2.2.2 hk.2.2.1 hk.2.1, hEq i j b h1 h2 k' P' _ hk'.2.2.2 hk'.2.2.1 hk'.2.1,
    hEq i j b h1 h2 k' P' _ hk'.2.2.2 hk'.2.2.1 hk'.2.1, hEq i j b h1 h2 k P _ hk.2.2.2 hk.2.2.1 hk.2.1, map_smul, map_smul,
    smul_comm]
  exact congrArg (fun z => c i b k' P' • c i b k P • z) (LinearMap.congr_fun hF.eq (Y.eF i j b h1 h2 x))

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n, j = n + 1` from `⟨j - 1, by omega⟩`. Set `m : Fin D.R.m` to `⟨n, h2⟩`. Establish `so` using `hC i P hk.2.2.2 hk.2.2.1`. Establish `so'` using `hC i P' hk'.2.2.2 hk'.2.2.1`. Take `⟨α, Rc, ha, hR⟩` from `GlobalTheory.HeckeSupSt.exists_heckeElt hL hF m so hk.2.1`.

Take `⟨α', Rc', ha', hR'⟩` from `GlobalTheory.HeckeSupSt.exists_heckeElt hL hF m so' hk'.2.1`. Take `⟨c, hc⟩` from `hr i m k P hk α Rc ha hR`. Take `⟨c', hc'⟩` from `hr i m k' P' hk' α' Rc' ha' hR'`. Conclude with `commute_of_read Rl cG S Y hL hF.Sb hW m (hinj m) so so' ha ha' hR hR' hc hc'`.
-/
theorem family_comm (hL : Rl.toRealDat.toLevCh.Is A3.A.μ0) (hF : Rl.toRealDat.IsFam) (hW : Rl.toRealDat.models_HW)
    (hinj : ∀ i, Function.Injective ((Rl.FW i).j (sg0 D A3.A))) (hC : GlobalTheory.ExportPin.Model.Covered Rl)
    (f : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hr : ∀ (i : D.ntw.Tw) (n : Fin D.R.m) (k : ℕ) (P : PlE D.host), Formalism.MainNotions.IntegralHeckeForms.HkIdx i k P →
      ∀ (α : GA D (Wc D n)) (R : Finset (GA D (Wc D n))), IsHeckeAt (Wc D n) P k α →
        Bridge.IsDC (levG (Wc D n) (Rl.βW n) (Rl.datWp n Rl.triv)) α R → ∃ c : ℂ, ∀ x : S.WL ((n : ℕ) + 1),
          (Rl.HW n (sg0 D A3.A)).e ((Rl.FW n).j (sg0 D A3.A) ((Y.fi n).e (f ((n : ℕ) + 1) k P x))) =
            c • heckeOn (Rl.MW n (sg0 D A3.A)) R ((Rl.HW n (sg0 D A3.A)).e ((Rl.FW n).j (sg0 D A3.A) ((Y.fi n).e x))))
    (i : D.ntw.Tw) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (k : ℕ) (P : PlE D.host) (k' : ℕ) (P' : PlE D.host)
    (hk : Formalism.MainNotions.IntegralHeckeForms.HkIdx i k P) (hk' : Formalism.MainNotions.IntegralHeckeForms.HkIdx i k' P') : Commute (f j k P) (f j k' P') := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  let m : Fin D.R.m := ⟨n, h2⟩
  have so := hC i P hk.2.2.2 hk.2.2.1
  have so' := hC i P' hk'.2.2.2 hk'.2.2.1
  obtain ⟨α, Rc, ha, hR⟩ := GlobalTheory.HeckeSupSt.exists_heckeElt hL hF m so hk.2.1
  obtain ⟨α', Rc', ha', hR'⟩ := GlobalTheory.HeckeSupSt.exists_heckeElt hL hF m so' hk'.2.1
  obtain ⟨c, hc⟩ := hr i m k P hk α Rc ha hR
  obtain ⟨c', hc'⟩ := hr i m k' P' hk' α' Rc' ha' hR'
  exact commute_of_read Rl cG S Y hL hF.Sb hW m (hinj m) so so' ha ha' hR hR' hc hc'

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
The claim follows from `hkComm_of_family Rl cG S Y H.hL H.hs H.cHk H.hkEq fun i j a b k P k' P' hk hk' => family_comm Rl cG S Y hL hF hW hinj hC H.hL (fun i n k P hk α R ha hR => ⟨_, fun x => X.tie n k P hk.2.2.1 (hC i P hk.2.2.2 hk.2.2.1) ⟨i, hk.2.2.2⟩ (fun h => hk.2.2.2 (h2 i h)) hk.2.1 α R ha hR x rf …`.
-/
theorem hkComm_of_row (hL : Rl.toRealDat.toLevCh.Is A3.A.μ0) (hF : Rl.toRealDat.IsFam) (hW : Rl.toRealDat.models_HW)
    (hinj : ∀ i, Function.Injective ((Rl.FW i).j (sg0 D A3.A))) (hC : GlobalTheory.ExportPin.Model.Covered Rl)
    (h2 : ∀ i, placesOver D.host.E 2 ⊆ ↑(D.ntw.S0 i))
    (H : NExpRealH Rl cG S Y) (X : NExpHeckeRowX Rl cG S Y H fun _ => 1) : HkComm D :=
  hkComm_of_family Rl cG S Y H.hL H.hs H.cHk H.hkEq fun i j a b k P k' P' hk hk' =>
    family_comm Rl cG S Y hL hF hW hinj hC H.hL
      (fun i n k P hk α R ha hR => ⟨_, fun x => X.tie n k P hk.2.2.1 (hC i P hk.2.2.2 hk.2.2.1) ⟨i, hk.2.2.2⟩
        (fun h => hk.2.2.2 (h2 i h)) hk.2.1 α R ha hR x rfl⟩)
      i j a b k P k' P' hk hk'

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Take `⟨u, hu⟩` from `hp f hs hf`. Conclude with `hkComm_of_family Rl cG S Y f hs (fun i b k P => algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P) ^ k) hu fun i j a b k P k' P' hk hk' => family_comm Rl cG S Y hL hF hW hinj hC f (fun i n k P hk α R ha hR => ⟨_, fun x => hf n k P hk.2.2.1 (hC i P hk.2.2.2 hk.2.2.1) hk.2 …`.
-/
theorem hkComm_of_pin (hL : Rl.toRealDat.toLevCh.Is A3.A.μ0) (hF : Rl.toRealDat.IsFam) (hW : Rl.toRealDat.models_HW)
    (hinj : ∀ i, Function.Injective ((Rl.FW i).j (sg0 D A3.A))) (hC : GlobalTheory.ExportPin.Model.Covered Rl)
    (hp : GlobalTheory.ExportPin.HeckePin Rl cG S Y) (f : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hs : ∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (f j)) (hf : GlobalTheory.ExportPin.Reads Rl cG S Y f) : HkComm D := by
  obtain ⟨u, hu⟩ := hp f hs hf
  exact hkComm_of_family Rl cG S Y f hs (fun i b k P => algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P) ^ k) hu
    fun i j a b k P k' P' hk hk' => family_comm Rl cG S Y hL hF hW hinj hC f
      (fun i n k P hk α R ha hR => ⟨_, fun x => hf n k P hk.2.2.1 (hC i P hk.2.2.2 hk.2.2.1) hk.2.1 α R ha hR x⟩)
      i j a b k P k' P' hk hk'

end Tied

/- English proof (translation)
Introduce `i hi j b k k' P P' hk hk'` and use `((GlobalTheory.SupLaw.Model.heckeLaws_of D hC hO) i hi).1 j b k P k' P' hk hk'`.
-/
theorem commute_all_lifts (D : D7) (hC : HkComm D) (hO : OffRange D) : Formalism.MainNotions.LatticeVariant.adm13 D := fun i hi j b k k' P P' hk hk' =>
  ((GlobalTheory.SupLaw.Model.heckeLaws_of D hC hO) i hi).1 j b k P k' P' hk hk'

end GlobalTheory.SupLaw
