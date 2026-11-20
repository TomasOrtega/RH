import Development.EtaleCohomology.EtaleSheaves.EtaleDegreeZeroCohomologyEquivLocallyConstantFun

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.EqvQAPf

/- English proof (translation)
Break down `subsingleton_or_nontrivial S with hs | hs` into its components or cases. Conclude with `⟨⟨0, hq, Subsingleton.elim _ _⟩⟩`. Establish `hm : ((Polynomial.cyclotomic q ℤ).map (Int.castRingHom S)).Monic` using `(Polynomial.cyclotomic.monic q ℤ).map _`. Establish `hd : 0 < ((Polynomial.cyclotomic q ℤ).map (Int.castRingHom S)).natDegree`. Rewrite using `[(Polynomial.cyclotomic.monic q ℤ).natDegree_map, Polynomial.natDegree_cyclotomic]`.

Conclude with `Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))`. Take `⟨a, ha⟩` from `hS _ hm hd`. Conclude with `⟨⟨a, hq, by rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]; simpa using ha⟩⟩`.
-/
theorem prim_of_aic (q : ℕ) [NeZero q] (S : Type) [CommRing S] (hS : AIC S) (hq : IsUnit (q : S)) :
    Nonempty (Prim q S) := by
  rcases subsingleton_or_nontrivial S with hs | hs
  · exact ⟨⟨0, hq, Subsingleton.elim _ _⟩⟩
  have hm : ((Polynomial.cyclotomic q ℤ).map (Int.castRingHom S)).Monic :=
    (Polynomial.cyclotomic.monic q ℤ).map _
  have hd : 0 < ((Polynomial.cyclotomic q ℤ).map (Int.castRingHom S)).natDegree := by
    rw [(Polynomial.cyclotomic.monic q ℤ).natDegree_map, Polynomial.natDegree_cyclotomic]
    exact Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  obtain ⟨a, ha⟩ := hS _ hm hd
  exact ⟨⟨a, hq, by rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]; simpa using ha⟩⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun x y _ => Subsingleton.elim x y, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩`.
-/
theorem bij_of_sub {A B : Type*} [AddZeroClass A] [AddZeroClass B] [Subsingleton A] [Subsingleton B] (f : A →+ B) :
    Function.Bijective f :=
  ⟨fun x y _ => Subsingleton.elim x y, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

end LateralTheory.E.EqvQAPf

open LateralTheory.E.t_E1Cut in
/- English proof (translation)
Introduce `h1 h9 hb1 hb2 q _ S _ J hS hJ hq i n`. Establish `hqJ : IsUnit (q : S ⧸ J)` using `by simpa using hq.map (Ideal.Quotient.mk J)`. Establish `hSJ : QA (S ⧸ J)` using `(hQA S hS).2.2 J`. Break down `lt_trichotomy n 0 with hn | rfl | hn` into its components or cases. Use `haveI := (h9 (ZMod q) (tw q i)).1 (sp S) n hn haveI := (h9 (ZMod q) (tw q i)).1 (sp (S ⧸ J)) n hn`.

Conclude with `LateralTheory.E.EqvQAPf.bij_of_sub _`. Take `⟨ζ⟩` from `LateralTheory.E.EqvQAPf.prim_of_aic q S (hQA S hS).1 hq`. Take `⟨e, he⟩` from `hH0 h9 q i`. Establish `key : ∀ φ, pull _ (spMap (Ideal.Quotient.mk J)) (tw q i) 0 (e S ζ φ) = e (S ⧸ J) (ζ.map (Ideal.Quotient.mk J)) (lcMap (Ideal.Quotient.mk J) φ)` using `fun φ => he S (S ⧸ J) (Ideal.Quotient.mk J) ζ φ`. Establish `hcomp : (pull _ (spMap (Ideal.Quotient.mk J)) (tw q i) 0) = (e (S ⧸ J) (ζ.map (Ideal.Quotient.mk J))) ∘ (fun φ => lcMap (Ideal.Quotient.mk J) φ) ∘ (e S ζ).symm`.

Use function extensionality and compare the values at `x`. Take `⟨φ, rfl⟩` from `(e S ζ).surjective x`. Simplify using `only [Function.comp_apply, AddEquiv.symm_apply_apply]`. Conclude with `key φ`. Rewrite using `[hcomp]`.

Conclude with `(e _ _).bijective.comp ((hLC S J hJ (ZMod q)).comp (e S ζ).symm.bijective)`. Use `haveI := hAcyc h1 h9 hb1 hb2 q S hS hq n i hn haveI := hAcyc h1 h9 hb1 hb2 q (S ⧸ J) hSJ hqJ n i hn`. Conclude with `LateralTheory.E.EqvQAPf.bij_of_sub _`.
-/
theorem LateralTheory.E.t_E1Cut.EqvQA_of (hAcyc : AcycQA) (hQA : QAClosed) (hH0 : EtaleDegreeZeroCohomologyEquivLocallyConstantFunctions) (hLC : LCGood) : EqvQA := by
  intro h1 h9 hb1 hb2 q _ S _ J hS hJ hq i n
  have hqJ : IsUnit (q : S ⧸ J) := by simpa using hq.map (Ideal.Quotient.mk J)
  have hSJ : QA (S ⧸ J) := (hQA S hS).2.2 J
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · haveI := (h9 (ZMod q) (tw q i)).1 (sp S) n hn
    haveI := (h9 (ZMod q) (tw q i)).1 (sp (S ⧸ J)) n hn
    exact LateralTheory.E.EqvQAPf.bij_of_sub _
  · obtain ⟨ζ⟩ := LateralTheory.E.EqvQAPf.prim_of_aic q S (hQA S hS).1 hq
    obtain ⟨e, he⟩ := hH0 h9 q i
    have key : ∀ φ, pull _ (spMap (Ideal.Quotient.mk J)) (tw q i) 0 (e S ζ φ) =
        e (S ⧸ J) (ζ.map (Ideal.Quotient.mk J)) (lcMap (Ideal.Quotient.mk J) φ) :=
      fun φ => he S (S ⧸ J) (Ideal.Quotient.mk J) ζ φ
    have hcomp : (pull _ (spMap (Ideal.Quotient.mk J)) (tw q i) 0) =
        (e (S ⧸ J) (ζ.map (Ideal.Quotient.mk J))) ∘
          (fun φ => lcMap (Ideal.Quotient.mk J) φ) ∘ (e S ζ).symm := by
      funext x
      obtain ⟨φ, rfl⟩ := (e S ζ).surjective x
      simp only [Function.comp_apply, AddEquiv.symm_apply_apply]
      exact key φ
    rw [hcomp]
    exact (e _ _).bijective.comp ((hLC S J hJ (ZMod q)).comp (e S ζ).symm.bijective)
  · haveI := hAcyc h1 h9 hb1 hb2 q S hS hq n i hn
    haveI := hAcyc h1 h9 hb1 hb2 q (S ⧸ J) hSJ hqJ n i hn
    exact LateralTheory.E.EqvQAPf.bij_of_sub _
