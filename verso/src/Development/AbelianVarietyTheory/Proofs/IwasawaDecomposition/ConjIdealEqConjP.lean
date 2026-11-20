import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffFieldRootsOfUnityTypePrimesHermitianStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.Brg

open Formalism.L2.Col in

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `Ideal.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `r ⟨s, hs, e⟩`. Use `show r ∈ (conjPrime₂ P).asIdeal`. Rewrite using `[mem_conjP]`.

Establish `: cO E r = s` using `RingOfIntegers.ext (by show star (r : E) = (s : E)`. Establish `e' : (r : E) = star (s : E)` using `e`. Rewrite using `[e', star_star])`. Rewrite using `[this]`. Conclude with `hs`.

Introduce `r hr`. Rewrite `hr` using `[mem_conjP]`. Use `Ideal.subset_span ⟨cO E r, hr, ?_⟩` and prove the remaining obligations. Use `show (r : E) = star (star (r : E))`. Rewrite using `[star_star]`.
-/
theorem conjIdeal_eq_conjP {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := E) P.asIdeal = (conjPrime₂ P).asIdeal := by
  apply le_antisymm
  · refine Ideal.span_le.2 ?_
    rintro r ⟨s, hs, e⟩
    show r ∈ (conjPrime₂ P).asIdeal
    rw [mem_conjP]
    have : cO E r = s := RingOfIntegers.ext (by
      show star (r : E) = (s : E)
      have e' : (r : E) = star (s : E) := e
      rw [e', star_star])
    rw [this]; exact hs
  · intro r hr
    rw [mem_conjP] at hr
    refine Ideal.subset_span ⟨cO E r, hr, ?_⟩
    show (r : E) = star (star (r : E))
    rw [star_star]

open Formalism.L2.Col in

/- English proof (translation)
Use `letI := X.starE`. Introduce `hk`. Establish `h0 : X.conjO (Pr.piG k) ≠ 0`. Use `right_ne_zero_of_mul (a := Pr.piG k) ?_` and prove the remaining obligations. Rewrite using `[hPr.piG_norm k]`.

Conclude with `(hPr.g_prime k).ne_zero` after adjusting the coercions. Establish `hsub : ∀ Q, Q ∈ Pr.vG k → Q ∈ Pr.vGs` using `fun Q hQ => by`. Unfold `Primes.vGs`. Rewrite using `[Finset.mem_union]`. Use `fin_cases k`.

Use `exacts [Or.inl hQ, Or.inr hQ]`. Rewrite `hk` using `[← hPr.piG_norm k]`. Break down `P.1.isPrime.mem_or_mem hk with h | h` into its components or cases. Establish `hc : conjPrime₂ P.1 ∈ Pr.vG k`. Use `(mem_divs h0 _).2 ?_` and prove the remaining obligations.

Rewrite using `[mem_conjP]`. Use `show cO X.E (X.conjO (Pr.piG k)) ∈ P.1.asIdeal`. Conclude with `(cO_cO (Pr.piG k)).symm ▸ h`. Conclude with `P.2.2.2 (conjPrime₂ P.1) (Or.inr (hsub _ hc)) (conjIdeal_eq_conjP P.1).symm`. Conclude with `P.2.2.1 (Or.inr (hsub _ ((mem_divs h0 _).2 h)))`.
-/
theorem g_notMem_of_levOff {X : Fields} {Pr : Primes X} (hPr : Pr.Ok)
    (P : letI := X.starE; LevOff (E := X.E) ∅ Pr.vGs ∅) (k : Fin 2) :
    ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal := by
  classical
  letI := X.starE
  intro hk
  have h0 : X.conjO (Pr.piG k) ≠ 0 := by
    refine right_ne_zero_of_mul (a := Pr.piG k) ?_
    rw [hPr.piG_norm k]
    exact_mod_cast (hPr.g_prime k).ne_zero
  have hsub : ∀ Q, Q ∈ Pr.vG k → Q ∈ Pr.vGs := fun Q hQ => by
    unfold Primes.vGs
    rw [Finset.mem_union]
    fin_cases k
    exacts [Or.inl hQ, Or.inr hQ]
  rw [← hPr.piG_norm k] at hk
  rcases P.1.isPrime.mem_or_mem hk with h | h
  · have hc : conjPrime₂ P.1 ∈ Pr.vG k := by
      refine (mem_divs h0 _).2 ?_
      rw [mem_conjP]
      show cO X.E (X.conjO (Pr.piG k)) ∈ P.1.asIdeal
      exact (cO_cO (Pr.piG k)).symm ▸ h
    exact P.2.2.2 (conjPrime₂ P.1) (Or.inr (hsub _ hc)) (conjIdeal_eq_conjP P.1).symm
  · exact P.2.2.1 (Or.inr (hsub _ ((mem_divs h0 _).2 h)))

end GlobalTheory.Mem.R3.Brg

namespace GlobalTheory.Mem.R3.Brg

/- English proof (translation)
Substitute `hτ` using the available equality. Rewrite using `[Formalism.L2.Host.HChar.val_mul, Units.val_mul, Units.val_mul, map_mul, hV.embLL_xiValOf a P hu]`. Use `congr 1`. Conclude with `hI.ch_tied.muVal i P hg`.
-/
theorem muVal_eq {B : Base} {px : PreX B.toPre} (I : ColIn B px) (hI : I.Ok) (hV : ValsIn I) (i : Fin B.R.m) {a : I.ι}
    {τ : Tup B.fields.F B.fields.E B.fields.K I.S} (hτ : I.tup a = τ) (P : HeightOneSpectrum (𝓞 B.fields.E))
    (hg : ∀ k, ((B.host.g k : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal) (hu : (I.xi a).UnrAt P) :
    B.embLL ((I.Ch.muVal i P * xiValOf I τ P : B.LLˣ) : B.LL) = (((I.C.mu0 i * I.xi a).val P : ℂˣ) : ℂ) := by
  subst hτ
  rw [Formalism.L2.Host.HChar.val_mul, Units.val_mul, Units.val_mul, map_mul, hV.embLL_xiValOf a P hu]
  congr 1
  exact hI.ch_tied.muVal i P hg

/- English proof (translation)
Introduce `X px I hX U Xg tr L eG hI hV hL _`. Use `letI := X.B.fields.starE`. Establish `hPr : (X.B.primes px).Ok` using `(GlobalTheory.Mem.Col2.base_fields_primes_ok X.B px).2.1`. Use `⟨fun i t P hP => ?_, fun P _ => ?_, fun t PP hPP => ?_⟩` and prove the remaining obligations. Establish `hP' : P.1 ∈ Formalism.L2.DIV.offSet (E` using `X.B.fields.E) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ∅ := hP`.

Establish `hQ : ∀ PP, PP ∈ I.Q (ixOf I U t) → PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1` using `fun PP h => Finset.mem_union_right _ (by rw [← tup_ixOf I t]; exact h)`. Establish `hg : ∀ k, ((X.B.host.g k : ℕ) : 𝓞 X.B.fields.E) ∉ P.1.asIdeal` using `g_notMem_of_levOff hPr P`. Establish `hunr : (I.xi (ixOf I U t)).UnrAt P.1`. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[← hL.xiH t]`.

Break down `(hL.is.Q_ram t P.1).1 hn with h | ⟨PP', h, hc⟩` into its components or cases. Rewrite `h` using `[hL.Q t]`. Conclude with `hP'.2.1 (Or.inr (Finset.mem_coe.2 (hQ _ h)))`. Rewrite `h` using `[hL.Q t]`. Establish `hle : PP'.asIdeal ≤ (Formalism.L2.Col.conjPrime₂ P.1).asIdeal` using `fun c hcm => by`.

Take `⟨c', hc', e⟩` from `hc c hcm`. Use `(Formalism.L2.Col.mem_conjP (E := X.B.fields.E) P.1 c).2 ?_` and prove the remaining obligations. Establish `: Formalism.L2.Col.cO X.B.fields.E c = c'` using `RingOfIntegers.ext e.symm`. Rewrite using `[this]`. Conclude with `hc'`.

Establish `heq : PP'.asIdeal = (Formalism.L2.Col.conjPrime₂ P.1).asIdeal` using `PP'.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P.1).isPrime.ne_top hle`. Conclude with `hP'.2.2 PP' (Or.inr (Finset.mem_coe.2 (hQ _ h))) (heq.trans (conjIdeal_eq_conjP P.1).symm)`. Rewrite using `[hL.C, hL.xiH t]`. Conclude with `muVal_eq I hI hV i (tup_ixOf I t) P.1 hg hunr`. Use `show X.B.embLL (I.Ch.etaVal P.1 : X.B.LL) = _`.

Rewrite using `[hL.C]`. Conclude with `hI.ch_tied.etaVal P.1`. Break down `hPP with h | h` into its components or cases. Rewrite `h` using `[hL.Pg]`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, PP ∈ (X.B.primes px).vG k := by`.

Break down `Finset.mem_union.1 h with h | h` into its components or cases. Use `exacts [⟨0, h⟩, ⟨1, h⟩]`. Establish `hn : Ideal.absNorm PP.asIdeal = X.B.host.g k` using `hPr.vG_norm k PP hk`. Establish `hcard : Nat.card (kP PP) = X.B.host.g k`. Rewrite using `[← hn, Ideal.absNorm_apply, Submodule.cardQuot_apply]`.

Rewrite using `[hcard]`. Conclude with `(GlobalTheory.Core.Cls.coeffField_rootsOfUnity_typePrimes_hermitianStages X k).1`. Rewrite `h` using `[hL.Q t]`. Conclude with `hV.2 _ PP h`.
-/
theorem values : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    (∀ (i : Fin X.toD7.R.m) t, ∀ P ∈ (famR X I hX U Xg tr).A.ok t,
      X.toD7.what₂.embLL ((famR X I hX U Xg tr).A.muVal i t P : X.toD7.what₂.LL) =
        (((L.C.mu0 i * L.xiH t).val (P.1 : Pl X.toD7.host.E) : ℂˣ) : ℂ)) ∧
    (∀ P ∈ (famR X I hX U Xg tr).A.ok (famR X I hX U Xg tr).A.μ0,
      X.toD7.what₂.embLL ((famR X I hX U Xg tr).A.etaVal P : X.toD7.what₂.LL) =
        Formalism.L2.Host.etaAlg X.toD7.host L.C.eta (P.1 : Pl X.toD7.host.E)) ∧
    ∀ t PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → ∃ z : X.toD7.what₂.LL, IsPrimitiveRoot z (Nat.card (kP PP)) := by
  intro X px I hX U Xg tr L eG hI hV hL _
  classical
  letI := X.B.fields.starE
  have hPr : (X.B.primes px).Ok := (GlobalTheory.Mem.Col2.base_fields_primes_ok X.B px).2.1
  refine ⟨fun i t P hP => ?_, fun P _ => ?_, fun t PP hPP => ?_⟩
  · have hP' : P.1 ∈ Formalism.L2.DIV.offSet (E := X.B.fields.E) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ∅ := hP
    have hQ : ∀ PP, PP ∈ I.Q (ixOf I U t) → PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := fun PP h =>
      Finset.mem_union_right _ (by rw [← tup_ixOf I t]; exact h)
    have hg : ∀ k, ((X.B.host.g k : ℕ) : 𝓞 X.B.fields.E) ∉ P.1.asIdeal := g_notMem_of_levOff hPr P
    have hunr : (I.xi (ixOf I U t)).UnrAt P.1 := by
      by_contra hn
      rw [← hL.xiH t] at hn
      rcases (hL.is.Q_ram t P.1).1 hn with h | ⟨PP', h, hc⟩
      · rw [hL.Q t] at h
        exact hP'.2.1 (Or.inr (Finset.mem_coe.2 (hQ _ h)))
      · rw [hL.Q t] at h
        have hle : PP'.asIdeal ≤ (Formalism.L2.Col.conjPrime₂ P.1).asIdeal := fun c hcm => by
          obtain ⟨c', hc', e⟩ := hc c hcm
          refine (Formalism.L2.Col.mem_conjP (E := X.B.fields.E) P.1 c).2 ?_
          have : Formalism.L2.Col.cO X.B.fields.E c = c' := RingOfIntegers.ext e.symm
          rw [this]; exact hc'
        have heq : PP'.asIdeal = (Formalism.L2.Col.conjPrime₂ P.1).asIdeal :=
          PP'.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P.1).isPrime.ne_top hle
        exact hP'.2.2 PP' (Or.inr (Finset.mem_coe.2 (hQ _ h))) (heq.trans (conjIdeal_eq_conjP P.1).symm)
    rw [hL.C, hL.xiH t]
    exact muVal_eq I hI hV i (tup_ixOf I t) P.1 hg hunr
  · show X.B.embLL (I.Ch.etaVal P.1 : X.B.LL) = _
    rw [hL.C]
    exact hI.ch_tied.etaVal P.1
  · rcases hPP with h | h
    · rw [hL.Pg] at h
      obtain ⟨k, hk⟩ : ∃ k, PP ∈ (X.B.primes px).vG k := by
        rcases Finset.mem_union.1 h with h | h
        exacts [⟨0, h⟩, ⟨1, h⟩]
      have hn : Ideal.absNorm PP.asIdeal = X.B.host.g k := hPr.vG_norm k PP hk
      have hcard : Nat.card (kP PP) = X.B.host.g k := by
        rw [← hn, Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rw [hcard]
      exact (GlobalTheory.Core.Cls.coeffField_rootsOfUnity_typePrimes_hermitianStages X k).1
    · rw [hL.Q t] at h
      exact hV.2 _ PP h

end GlobalTheory.Mem.R3.Brg
