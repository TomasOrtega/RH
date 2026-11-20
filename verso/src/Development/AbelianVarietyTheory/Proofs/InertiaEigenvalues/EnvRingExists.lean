import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureAdicCompletionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeltaRingHomOfDenseDeltaCommuteLocusStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsAdicCompletionMapOfFgStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRingHomExtendIsAdicCompletionMapStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureQuotientSpanStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DigitMonomialsBasisEnvelopeModPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticEnvelopeRelationTriangularStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdicTopologicalBasisOfLevelBasesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.EnvExist

variable {l : ℕ}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rfl`. Consider the case `succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hg, ih]`.
-/
theorem iter_map {A B : Type} [CommRing A] [CommRing B] {D : Delta l A} {D' : Delta l B} {g : A →+* B}
    (hg : IsδMap D D' g) (n : ℕ) (x : A) : g (D.δ^[n] x) = D'.δ^[n] (g x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hg, ih]

/- English proof (translation)
Introduce `x`. Establish `: x ∈ δLocus (polyDelta D) DC (MvPolynomial.eval₂Hom f fun k => DC.δ^[k] v)`. Use `MvPolynomial.induction_on x ?_ ?_ ?_` and prove the remaining obligations. Introduce `a`. Rewrite using `[mem_δLocus, polyDelta_C, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]`.

Conclude with `hf a`. Introduce `p q hp hq`. Conclude with `add_mem hp hq`. Introduce `p k hp`. Use `mul_mem hp ?_` and prove the remaining obligations.

Rewrite using `[mem_δLocus, polyDelta_X, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', Function.iterate_succ_apply']`. Conclude with `mem_δLocus.1 this`.
-/
theorem polyEval_isδ [Fact l.Prime] {A C : Type} [CommRing A] [CommRing C] (D : Delta l A) (DC : Delta l C)
    (f : A →+* C) (hf : IsδMap D DC f) (v : C) :
    IsδMap (polyDelta D) DC (MvPolynomial.eval₂Hom f fun k => DC.δ^[k] v) := by
  intro x
  have : x ∈ δLocus (polyDelta D) DC (MvPolynomial.eval₂Hom f fun k => DC.δ^[k] v) := by
    refine MvPolynomial.induction_on x ?_ ?_ ?_
    · intro a
      rw [mem_δLocus, polyDelta_C, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
      exact hf a
    · intro p q hp hq
      exact add_mem hp hq
    · intro p k hp
      refine mul_mem hp ?_
      rw [mem_δLocus, polyDelta_X, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X',
        Function.iterate_succ_apply']
  exact mem_δLocus.1 this

end GlobalTheory.BSP.EnvExist

open GlobalTheory.BSP.EnvExist in

/- English proof (translation)
Introduce `l _ A _ D J d p hfg hl hd hδ hc`. Establish `hstab : ∀ x ∈ Set.range (envRel D d p), (polyDelta D).δ x ∈ Ideal.span (Set.range (envRel D d p))`. Introduce and unpack `_ ⟨k, rfl⟩`. Use `Ideal.subset_span ⟨k + 1, ?_⟩` and prove the remaining obligations. Unfold `envRel`.

Conclude with `Function.iterate_succ_apply' _ _ _`. Take `⟨DL, hDL⟩` from `GlobalTheory.T.exists_deltaRingStructure_quotient_span l (MvPolynomial ℕ A) (polyDelta D) _ hstab`. Use `set mk := Ideal.Quotient.mk (Ideal.span (Set.range (envRel D d p))) with hmk`. Use `set s : A →+* MvPolynomial ℕ A ⧸ Ideal.span (Set.range (envRel D d p)) := mk.comp MvPolynomial.C with hs`. Take `⟨Q, _, iQ, hQ⟩` from `GlobalTheory.T.exists_isAdicCompletionMap_of_fg _ (J.map s) (hfg.map s)`.

Establish `hlL : ((l : ℕ) : MvPolynomial ℕ A ⧸ Ideal.span (Set.range (envRel D d p))) ∈ J.map s`. Rewrite using `[← map_natCast s]`. Conclude with `Ideal.mem_map_of_mem s hl`. Take `⟨DQ, hDQ⟩` from `GlobalTheory.T.exists_deltaRingStructure_adicCompletion l _ Q iQ (J.map s) hQ hlL DL`. Establish `hX : ∀ k, iQ (mk (MvPolynomial.X k)) = DQ.δ^[k] (iQ (mk (MvPolynomial.X 0)))`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => rfl`. Consider the case `succ k ih => rw [← polyDelta_X D k, hDL, hDQ, ih, Function.iterate_succ_apply']`. Establish `hshape` using `GlobalTheory.T.prismaticEnvelopeRelation_triangular l A D J d p hl hd hδ`.

Establish `hlev` using `GlobalTheory.T.digitMonomials_basis_envelope_mod_pow l A J (envRel D d p) hshape`. Establish `hmono : ∀ (α : ℕ →₀ ℕ) (a : A), mk (MvPolynomial.monomial α a) = s a * mk (MvPolynomial.monomial α 1)`. Introduce `α a`. Rewrite using `[hs, RingHom.comp_apply, ← map_mul, MvPolynomial.C_mul_monomial, mul_one]`. Establish `hsum : ∀ c : Digits l →₀ A, mk (c.sum fun α a => MvPolynomial.monomial α.1 a) = c.sum fun α a => s a * mk (MvPolynomial.monomial α.1 1)` using `fun c => by`.

Rewrite using `[map_finsuppSum]`. Conclude with `Finsupp.sum_congr fun α _ => hmono α.1 (c α)`. Establish `hmapmem : ∀ (n : ℕ) (y : MvPolynomial ℕ A), y ∈ Ideal.span (Set.range (envRel D d p)) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A) → mk y ∈ (J ^ n).map s`. Introduce `n y hy`. Establish `h` using `Ideal.mem_map_of_mem mk hy`.

Rewrite `h` using `[Ideal.map_sup, hmk, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_map]`. Then use the resulting hypothesis. Establish `hcomap : ∀ (n : ℕ) (y : MvPolynomial ℕ A), mk y ∈ (J ^ n).map s → y ∈ Ideal.span (Set.range (envRel D d p)) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A)`. Introduce `n y hy`. Rewrite `hy` using `[hs, ← Ideal.map_map]`. Establish `h` using `Ideal.mem_comap.2 hy`.

Rewrite `h` using `[Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_comm]`. Then use the resulting hypothesis. Take `⟨tb, htb⟩` from `GlobalTheory.T.exists_adicTopologicalBasis_of_level_bases A (MvPolynomial ℕ A ⧸ Ideal.span (Set.range (envRel D d p))) Q s iQ J (Digits l) (fun α => mk (MvPolynomial.monomial α.1 1)) ⟨0, fun _ => by simpa using (Fact.out : l.Prime).pos⟩ (by simp) hc hQ (fun n x => by`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Take `⟨c, hc'⟩` from `(hlev n).1 y`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Establish `h` using `hmapmem n _ hc'`. Rewrite using `[map_sub, hsum] at h)` and apply the resulting hypothesis. Use the proof step `(fun n c hcs => (hlev n).2 c (hcomap n _ (by rw [hsum]; exact hcs)))`. Establish `hiδ : IsδMap D DQ (iQ.comp s)`. Introduce `a`.

Use `show iQ (mk (MvPolynomial.C (D.δ a))) = DQ.δ (iQ (mk (MvPolynomial.C a)))`. Rewrite using `[← polyDelta_C, hDL, hDQ]`. Establish `hrel : DQ.δ ((iQ.comp s) p + (iQ.comp s) d * iQ (mk (MvPolynomial.X 0))) = 0` using `by show DQ.δ (iQ (mk (MvPolynomial.C p)) + iQ (mk (MvPolynomial.C d)) * iQ (mk (MvPolynomial.X 0))) = 0`. Establish `h0 : mk (envRel D d p 0) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨0, rfl⟩)`. Rewrite using `[← map_mul, ← map_mul, ← map_add, ← map_add, ← hDQ, ← hDL]`.

Express the relevant statement in the definitionally equal form `iQ (mk (envRel D d p 0)) = 0`. Rewrite using `[h0, map_zero]`. Establish `htbb : ∀ α, tb.b α = α.1.prod fun k n => (DQ.δ^[k] (iQ (mk (MvPolynomial.X 0)))) ^ n`. Introduce `α`. Rewrite using `[htb α]`.

Use `show (iQ.comp mk) (MvPolynomial.monomial α.1 1) = _`. Rewrite using `[MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, map_finsuppProd]`. Use `Finsupp.prod_congr fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, RingHom.comp_apply, hX]`. Establish `hlift : ∀ (C : Type) [CommRing C] (DC : Delta l C) (JC : Ideal C), IsAdicComplete JC C → ∀ f : A →+* C, IsδMap D DC f → J.map f ≤ JC → ∀ v : C, DC.δ (f p + f d * v) = 0 → ∃ h : Q →+* C, IsδMap DQ DC h ∧ h.comp (iQ.comp s) = f ∧ h (iQ (mk (MvPolynomial.X 0))) = v`.

Introduce `C _ DC JC hC f hf hJ v hv`. Establish `hg₀` using `polyEval_isδ D DC f hf v`. Use `set g₀ := MvPolynomial.eval₂Hom f fun k => DC.δ^[k] v with hg₀def`. Establish `hle : Ideal.span (Set.range (envRel D d p)) ≤ RingHom.ker g₀`. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `_ ⟨k, rfl⟩`. Establish `hz : g₀ (MvPolynomial.C p + MvPolynomial.C d * MvPolynomial.X 0) = f p + f d * v`. Simplify using `[g₀]`. Use `show g₀ (envRel D d p k) = 0`. Rewrite using `[envRel, iter_map hg₀, Function.iterate_succ_apply, hz, hv]`.

Conclude with `Function.iterate_fixed DC.δ_zero k`. Use `set g₁ := Ideal.Quotient.lift (Ideal.span (Set.range (envRel D d p))) g₀ (fun a ha => hle ha) with hg₁def`. Establish `hg₁C : g₁.comp s = f` using `RingHom.ext fun a => by show g₀ (MvPolynomial.C a) = f a`. Conclude with `MvPolynomial.eval₂Hom_C _ _ _`. Take `⟨h, hh⟩` from `GlobalTheory.T.exists_ringHom_extend_isAdicCompletionMap _ Q C iQ (J.map s) JC hQ hC g₁ (by rw [Ideal.map_map, hg₁C]; exact hJ)`.

Establish `e : ∀ z, h (iQ z) = g₁ z` using `fun z => RingHom.congr_fun hh z`. Establish `hlQ : ((l : ℕ) : Q) ∈ (J.map s).map iQ`. Rewrite using `[← map_natCast iQ]`. Conclude with `Ideal.mem_map_of_mem iQ hlL`. Establish `hJQ : ((J.map s).map iQ).map h ≤ JC`.

Rewrite using `[Ideal.map_map, hh, Ideal.map_map, hg₁C]`. Conclude with `hJ`. Establish `hhδ : IsδMap DQ DC h` using `GlobalTheory.T.isDeltaRingHom_of_dense_deltaCommuteLocus l Q C DQ DC ((J.map s).map iQ) JC h hlQ hJQ inferInstance (fun x n => by`. Take `⟨b, hb⟩` from `hQ.surj x n`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective b`.

Use `⟨iQ (mk y), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_δLocus, ← hDQ, ← hDL, e, e]`. Conclude with `hg₀ y`. Rewrite using `[← Ideal.map_pow]`. Conclude with `hb)`.

Use `⟨h, hhδ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← RingHom.comp_assoc, hh, hg₁C]`. Use `show h (iQ (mk (MvPolynomial.X 0))) = v`. Rewrite using `[e]`. Use `show g₀ (MvPolynomial.X 0) = v`.

Rewrite using `[hg₀def, MvPolynomial.eval₂Hom_X']`. Both sides reduce to the same expression. Conclude with `⟨{ Q := Q, DQ := DQ, i := iQ.comp s, i_δ := hiδ, w := iQ (mk (MvPolynomial.X 0)), rel := hrel, tb := tb, tb_b := htbb, lift := hlift }⟩`.
-/
theorem GlobalTheory.BSP.envRing_exists : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A)
    (d p : A), J.FG → (l : A) ∈ J → d ∈ J → IsUnit (D.δ d) → IsAdicComplete J A →
    Nonempty (EnvRing D J d p) := by
  intro l _ A _ D J d p hfg hl hd hδ hc
  have hstab : ∀ x ∈ Set.range (envRel D d p), (polyDelta D).δ x ∈ Ideal.span (Set.range (envRel D d p)) := by
    rintro _ ⟨k, rfl⟩
    refine Ideal.subset_span ⟨k + 1, ?_⟩
    unfold envRel
    exact Function.iterate_succ_apply' _ _ _
  obtain ⟨DL, hDL⟩ := GlobalTheory.T.exists_deltaRingStructure_quotient_span l (MvPolynomial ℕ A) (polyDelta D) _ hstab
  set mk := Ideal.Quotient.mk (Ideal.span (Set.range (envRel D d p))) with hmk
  set s : A →+* MvPolynomial ℕ A ⧸ Ideal.span (Set.range (envRel D d p)) := mk.comp MvPolynomial.C with hs
  obtain ⟨Q, _, iQ, hQ⟩ := GlobalTheory.T.exists_isAdicCompletionMap_of_fg _ (J.map s) (hfg.map s)
  have hlL : ((l : ℕ) : MvPolynomial ℕ A ⧸ Ideal.span (Set.range (envRel D d p))) ∈ J.map s := by
    rw [← map_natCast s]; exact Ideal.mem_map_of_mem s hl
  obtain ⟨DQ, hDQ⟩ := GlobalTheory.T.exists_deltaRingStructure_adicCompletion l _ Q iQ (J.map s) hQ hlL DL
  have hX : ∀ k, iQ (mk (MvPolynomial.X k)) = DQ.δ^[k] (iQ (mk (MvPolynomial.X 0))) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [← polyDelta_X D k, hDL, hDQ, ih, Function.iterate_succ_apply']

  have hshape := GlobalTheory.T.prismaticEnvelopeRelation_triangular l A D J d p hl hd hδ
  have hlev := GlobalTheory.T.digitMonomials_basis_envelope_mod_pow l A J (envRel D d p) hshape
  have hmono : ∀ (α : ℕ →₀ ℕ) (a : A), mk (MvPolynomial.monomial α a) = s a * mk (MvPolynomial.monomial α 1) := by
    intro α a
    rw [hs, RingHom.comp_apply, ← map_mul, MvPolynomial.C_mul_monomial, mul_one]
  have hsum : ∀ c : Digits l →₀ A, mk (c.sum fun α a => MvPolynomial.monomial α.1 a) =
      c.sum fun α a => s a * mk (MvPolynomial.monomial α.1 1) := fun c => by
    rw [map_finsuppSum]; exact Finsupp.sum_congr fun α _ => hmono α.1 (c α)
  have hmapmem : ∀ (n : ℕ) (y : MvPolynomial ℕ A), y ∈ Ideal.span (Set.range (envRel D d p)) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A) →
      mk y ∈ (J ^ n).map s := by
    intro n y hy
    have h := Ideal.mem_map_of_mem mk hy
    rwa [Ideal.map_sup, hmk, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_map] at h
  have hcomap : ∀ (n : ℕ) (y : MvPolynomial ℕ A), mk y ∈ (J ^ n).map s →
      y ∈ Ideal.span (Set.range (envRel D d p)) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
    intro n y hy
    rw [hs, ← Ideal.map_map] at hy
    have h := Ideal.mem_comap.2 hy
    rwa [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_comm] at h
  obtain ⟨tb, htb⟩ := GlobalTheory.T.exists_adicTopologicalBasis_of_level_bases A (MvPolynomial ℕ A ⧸ Ideal.span (Set.range (envRel D d p))) Q s iQ J (Digits l)
    (fun α => mk (MvPolynomial.monomial α.1 1)) ⟨0, fun _ => by simpa using (Fact.out : l.Prime).pos⟩
    (by simp) hc hQ
    (fun n x => by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨c, hc'⟩ := (hlev n).1 y
      refine ⟨c, ?_⟩
      have h := hmapmem n _ hc'
      rwa [map_sub, hsum] at h)
    (fun n c hcs => (hlev n).2 c (hcomap n _ (by rw [hsum]; exact hcs)))
  have hiδ : IsδMap D DQ (iQ.comp s) := by
    intro a
    show iQ (mk (MvPolynomial.C (D.δ a))) = DQ.δ (iQ (mk (MvPolynomial.C a)))
    rw [← polyDelta_C, hDL, hDQ]
  have hrel : DQ.δ ((iQ.comp s) p + (iQ.comp s) d * iQ (mk (MvPolynomial.X 0))) = 0 := by
    show DQ.δ (iQ (mk (MvPolynomial.C p)) + iQ (mk (MvPolynomial.C d)) * iQ (mk (MvPolynomial.X 0))) = 0
    have h0 : mk (envRel D d p 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨0, rfl⟩)
    rw [← map_mul, ← map_mul, ← map_add, ← map_add, ← hDQ, ← hDL]
    change iQ (mk (envRel D d p 0)) = 0
    rw [h0, map_zero]
  have htbb : ∀ α, tb.b α = α.1.prod fun k n => (DQ.δ^[k] (iQ (mk (MvPolynomial.X 0)))) ^ n := by
    intro α
    rw [htb α]
    show (iQ.comp mk) (MvPolynomial.monomial α.1 1) = _
    rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, map_finsuppProd]
    refine Finsupp.prod_congr fun k _ => ?_
    rw [map_pow, RingHom.comp_apply, hX]
  have hlift : ∀ (C : Type) [CommRing C] (DC : Delta l C) (JC : Ideal C), IsAdicComplete JC C → ∀ f : A →+* C,
      IsδMap D DC f → J.map f ≤ JC → ∀ v : C, DC.δ (f p + f d * v) = 0 →
      ∃ h : Q →+* C, IsδMap DQ DC h ∧ h.comp (iQ.comp s) = f ∧ h (iQ (mk (MvPolynomial.X 0))) = v := by
    intro C _ DC JC hC f hf hJ v hv
    have hg₀ := polyEval_isδ D DC f hf v
    set g₀ := MvPolynomial.eval₂Hom f fun k => DC.δ^[k] v with hg₀def
    have hle : Ideal.span (Set.range (envRel D d p)) ≤ RingHom.ker g₀ := by
      rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      have hz : g₀ (MvPolynomial.C p + MvPolynomial.C d * MvPolynomial.X 0) = f p + f d * v := by
        simp [g₀]
      show g₀ (envRel D d p k) = 0
      rw [envRel, iter_map hg₀, Function.iterate_succ_apply, hz, hv]
      exact Function.iterate_fixed DC.δ_zero k
    set g₁ := Ideal.Quotient.lift (Ideal.span (Set.range (envRel D d p))) g₀ (fun a ha => hle ha) with hg₁def
    have hg₁C : g₁.comp s = f := RingHom.ext fun a => by
      show g₀ (MvPolynomial.C a) = f a
      exact MvPolynomial.eval₂Hom_C _ _ _
    obtain ⟨h, hh⟩ := GlobalTheory.T.exists_ringHom_extend_isAdicCompletionMap _ Q C iQ (J.map s) JC hQ hC g₁ (by rw [Ideal.map_map, hg₁C]; exact hJ)
    have e : ∀ z, h (iQ z) = g₁ z := fun z => RingHom.congr_fun hh z
    have hlQ : ((l : ℕ) : Q) ∈ (J.map s).map iQ := by
      rw [← map_natCast iQ]; exact Ideal.mem_map_of_mem iQ hlL
    have hJQ : ((J.map s).map iQ).map h ≤ JC := by
      rw [Ideal.map_map, hh, Ideal.map_map, hg₁C]; exact hJ
    have hhδ : IsδMap DQ DC h := GlobalTheory.T.isDeltaRingHom_of_dense_deltaCommuteLocus l Q C DQ DC ((J.map s).map iQ) JC h hlQ hJQ inferInstance
      (fun x n => by
        obtain ⟨b, hb⟩ := hQ.surj x n
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
        refine ⟨iQ (mk y), ?_, ?_⟩
        · rw [mem_δLocus, ← hDQ, ← hDL, e, e]
          exact hg₀ y
        · rw [← Ideal.map_pow]; exact hb)
    refine ⟨h, hhδ, ?_, ?_⟩
    · rw [← RingHom.comp_assoc, hh, hg₁C]
    · show h (iQ (mk (MvPolynomial.X 0))) = v
      rw [e]
      show g₀ (MvPolynomial.X 0) = v
      rw [hg₀def, MvPolynomial.eval₂Hom_X']
      rfl
  exact ⟨{ Q := Q, DQ := DQ, i := iQ.comp s, i_δ := hiδ, w := iQ (mk (MvPolynomial.X 0)), rel := hrel, tb := tb, tb_b := htbb, lift := hlift }⟩
