import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ExistsNotInduces

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne TensorProduct CompanionTheory.PRW.ACWD

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PY.LTTest

open Classical in

def LTCrysAll : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw → ∀ (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a →
      ∀ (π : (w.adicCompletion E)ˣ), IsUnifAt w π →
      ∀ (j₀ : {j : w.adicCompletion E →+* Qbar l // Continuous j}) (LL : FinExt l)
        (ψ : ↥(Dec (F := E) A) →* GL (Fin 1) ↥LL.1), Continuous (ent ψ) →
      (∀ σ : Weil h, ent ψ ⟨σ, Weil_le_Dec h σ.2⟩ = j₀.1 (((a σ : (w.adicCompletion E)ˣ) : w.adicCompletion E) * ((π : w.adicCompletion E) ^ deg σ))) →
      Bw.IsCrysE P LL ψ ∧
      (∀ x ∈ Dcris (P.PD Bw.Kw) (Bw.repE LL ψ), ∃ c : ↥LL.1, (c : Qbar l) = (j₀.1 (π : w.adicCompletion E))⁻¹ ∧
            (phiVB P (LL := ↥LL.1) ^ GlobalTheory.Pst.resDeg l w) x = c • x) ∧
      ∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL.1) (j : {j : w.adicCompletion E →+* Qbar l // Continuous j}),
        (∀ x : E, j.1 (algebraMap E (w.adicCompletion E) x) = ((τ' ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩ : ↥LL.1) : Qbar l)) →
        ∀ n : ℤ, Bw.multE P LL ψ τ' n = if n = (if j = j₀ then -1 else 0) then 1 else 0

/- English proof (translation)
The claim follows from `LTInh.ltCrys_iff_emb.2 H`.
-/
theorem ltCrys_of_all (H : LTCrysAll) : LTCrys := LTInh.ltCrys_iff_emb.2 H

/- English proof (translation)
The claim follows from `LTInh.emb_of_conrad H`.
-/
theorem all_of_conrad (H : ConradLocalTied) : LTCrysAll := LTInh.emb_of_conrad H

def JumpAt (k : ℤ) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw → ∀ (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a →
      ∀ (π : (w.adicCompletion E)ˣ), IsUnifAt w π →
      ∀ (j₀ : {j : w.adicCompletion E →+* Qbar l // Continuous j}) (LL : FinExt l)
        (ψ : ↥(Dec (F := E) A) →* GL (Fin 1) ↥LL.1), Continuous (ent ψ) →
      (∀ σ : Weil h, ent ψ ⟨σ, Weil_le_Dec h σ.2⟩ = j₀.1 (((a σ : (w.adicCompletion E)ˣ) : w.adicCompletion E) * ((π : w.adicCompletion E) ^ deg σ))) →
      ∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL.1), (∀ x : E, j₀.1 (algebraMap E (w.adicCompletion E) x) = ((τ' ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩ : ↥LL.1) : Qbar l)) →
        ∀ n : ℤ, Bw.multE P LL ψ τ' n = if n = k then 1 else 0

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ l _ P AI hT w A h O _ _ _ Bw hB a ha π hπ j₀ LL ψ hc hψ`. Conclude with `(H E Ω l P AI hT w A h O Bw hB a ha π hπ j₀ LL ψ hc hψ).2.2.1`.
-/
theorem jumpAt_of_ltCrys (H : LTCrys) : JumpAt (-1) := by
  intro E Ω _ _ _ _ _ l _ P AI hT w A h O _ _ _ Bw hB a ha π hπ j₀ LL ψ hc hψ
  exact (H E Ω l P AI hT w A h O Bw hB a ha π hπ j₀ LL ψ hc hψ).2.2.1

/- English proof (translation)
Set `Ω` to `AlgebraicClosure ℚ`. Establish `: Fact (Nat.Prime 2)` using `⟨Nat.prime_two⟩`. Choose the witnesses or unpack the hypotheses as in `⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 ℚ), w ∈ placesOver ℚ 2 := by`. Establish `hne : Ideal.span {((2 : ℕ) : 𝓞 ℚ)} ≠ ⊤`. Introduce `e`.

Establish `h2 : Ideal.absNorm (Ideal.span {((2 : ℕ) : 𝓞 ℚ)}) = 2`. Rewrite using `[Ideal.absNorm_span_singleton]`. Establish `: ((2 : ℕ) : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) ((2 : ℕ) : ℤ)` using `by simp`. Rewrite using `[this, Algebra.norm_algebraMap, RingOfIntegers.rank]`. Simplify using the standard rewrite rules.

Rewrite `h2` using `[e]`. Simplify using `at h2`. Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal _ hne`. Establish `hm : ((2 : ℕ) : 𝓞 ℚ) ∈ M` using `hle (Ideal.mem_span_singleton_self _)`. Conclude with `⟨⟨M, hM.isPrime, fun e => by rw [e] at hm; simp at hm⟩, hm⟩`.

Take `⟨P, AI, hT⟩` from `GlobalTheory.MemLoc.exists_locPrime_tied 2`. Take `⟨A, h⟩` from `exists_isPlaceOver Ω w`. Take `⟨j, L₀, hj, H'⟩` from `GlobalTheory.PlaceBridge.exists_locBridge 2 ℚ Ω w A hw h`. Take `⟨Bw, e, -⟩` from `H' L₀ le_rfl`. Establish `hB : GlobalTheory.Pst.Induces Bw` using `fun x => by rw [e]; exact hj x`.

Take `⟨a, ha⟩` from `GlobalTheory.localArtinExists_holds ℚ Ω A w h`. Take `⟨j₀, hj₀⟩` from `LTInh.exists_emb Bw h hB (AlgHom.id ℚ_[2] ↥Bw.Kw.1)`. Take `⟨π, hπ, hπl⟩` from `LTInh.exists_unif_rat (l := 2) hw`. Take `⟨LL, ψ, hL, h1, h2, -⟩` from `LTInh.exists_char h a ha π hπ j₀ Bw.LL`. Set `τ' : ↥Bw.Kw.1 →ₐ[ℚ_[2]] ↥LL.1` to `IntermediateField.inclusion fun x hx => hL (Bw.LL_split Bw.Kw.1.val ⟨x, hx⟩)`.

Establish `e1` using `H ℚ Ω 2 P AI hT w A h _ Bw hB a ha π hπ j₀ LL ψ h1 h2 τ' hj₀ (-1)`. Apply the tactic sequence `have e2 := (LTInh.holds_rat P AI hT h Bw hB a ha π hπl j₀ LL ψ h1 h2).2.2.1 τ' (fun x => by convert hj₀ x using 1 <;> first | rfl | simp) (-1)`. Rewrite `e1` using `[e2]`. Assume the negation of the conclusion as `hk`. Simplify using `[Ne.symm hk] at e1`.
-/
theorem eq_neg_one_of_jumpAt {k : ℤ} (H : JumpAt k) : k = -1 := by
  let Ω := AlgebraicClosure ℚ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 ℚ), w ∈ placesOver ℚ 2 := by
    have hne : Ideal.span {((2 : ℕ) : 𝓞 ℚ)} ≠ ⊤ := by
      intro e
      have h2 : Ideal.absNorm (Ideal.span {((2 : ℕ) : 𝓞 ℚ)}) = 2 := by
        rw [Ideal.absNorm_span_singleton]
        have : ((2 : ℕ) : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) ((2 : ℕ) : ℤ) := by simp
        rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
        simp
      rw [e] at h2
      simp at h2
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hm : ((2 : ℕ) : 𝓞 ℚ) ∈ M := hle (Ideal.mem_span_singleton_self _)
    exact ⟨⟨M, hM.isPrime, fun e => by rw [e] at hm; simp at hm⟩, hm⟩
  obtain ⟨P, AI, hT⟩ := GlobalTheory.MemLoc.exists_locPrime_tied 2
  obtain ⟨A, h⟩ := exists_isPlaceOver Ω w
  obtain ⟨j, L₀, hj, H'⟩ := GlobalTheory.PlaceBridge.exists_locBridge 2 ℚ Ω w A hw h
  obtain ⟨Bw, e, -⟩ := H' L₀ le_rfl
  have hB : GlobalTheory.Pst.Induces Bw := fun x => by rw [e]; exact hj x
  obtain ⟨a, ha⟩ := GlobalTheory.localArtinExists_holds ℚ Ω A w h
  obtain ⟨j₀, hj₀⟩ := LTInh.exists_emb Bw h hB (AlgHom.id ℚ_[2] ↥Bw.Kw.1)
  obtain ⟨π, hπ, hπl⟩ := LTInh.exists_unif_rat (l := 2) hw
  obtain ⟨LL, ψ, hL, h1, h2, -⟩ := LTInh.exists_char h a ha π hπ j₀ Bw.LL
  let τ' : ↥Bw.Kw.1 →ₐ[ℚ_[2]] ↥LL.1 :=
    IntermediateField.inclusion fun x hx => hL (Bw.LL_split Bw.Kw.1.val ⟨x, hx⟩)
  have e1 := H ℚ Ω 2 P AI hT w A h _ Bw hB a ha π hπ j₀ LL ψ h1 h2 τ' hj₀ (-1)
  have e2 := (LTInh.holds_rat P AI hT h Bw hB a ha π hπl j₀ LL ψ h1 h2).2.2.1 τ'
    (fun x => by convert hj₀ x using 1 <;> first | rfl | simp) (-1)
  rw [e2] at e1
  by_contra hk
  simp [Ne.symm hk] at e1

end GlobalTheory.PY.LTTest

end
