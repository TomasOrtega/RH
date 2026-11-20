import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.AffRelOf

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

namespace ZariskiRelativeForms

open AffineRelativeForms

section Gen

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)

def incl (U : ObjectProperty C) {Q : ObjectProperty C} (hQ : Cosieve Q) :
    Cx.Hom (RC F U hQ) (CH.cx (U.ι ⋙ F)) (RingHom.id R) where
  f n := (relS (U.ι ⋙ F) (fun T => Q T.obj) n).subtype
  comm _ _ := rfl

/- English proof (translation)
The claim follows from `(CrystallineSemistableComparison.P.upTo_alg f (LinearMap.id : N →ₗ[R] N) 1 1).2.2.2.2`.
-/
theorem upTo_one {M N : Type 1} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N) :
    CrystallineSemistableComparison.UpTo (1 : R) f ↔ Function.Bijective f :=
  (CrystallineSemistableComparison.P.upTo_alg f (LinearMap.id : N →ₗ[R] N) 1 1).2.2.2.2

/- English proof (translation)
Establish `hle : U ⊓ Q ≤ U` using `fun T hT => And.left hT`. Establish `hle' : U' ⊓ Q ≤ U'` using `fun T hT => And.left hT`. Establish `hcc : U' ⊓ Q ≤ U ⊓ Q` using `fun T hT => And.intro (h T (And.left hT)) (And.right hT)`. Establish `key` using `(CrystallineSemistableComparison.P.five (incl F U hQ) (resU F hle).hom (fun n => Subtype.val_injective) (res_exact F U Q hQ hle (incl F U hQ) (fun _ _ => rfl)) (res_surj F U Q hQ hle) (incl F U' hQ) (resU F hle').hom (fun n => Subtype.val_injective) (res_exact F U' Q hQ hle' (inc …`. Rewrite `key` using `[one_pow]`.

Conclude with `(upTo_one _).1 key`.
-/
theorem rc_bij {U U' Q : ObjectProperty C} (hQ : Cosieve Q) (h : U' ≤ U)
    (hb : ∀ n, Function.Bijective ((resU F h).pull n))
    (hc : ∀ n, Function.Bijective ((resU F (U := U ⊓ Q) (V := U' ⊓ Q) fun T hT => And.intro (h T (And.left hT))
      (And.right hT)).pull n)) (n : ℕ) :
    Function.Bijective ((RC.res F hQ h).mapH n) := by
  have hle : U ⊓ Q ≤ U := fun T hT => And.left hT
  have hle' : U' ⊓ Q ≤ U' := fun T hT => And.left hT
  have hcc : U' ⊓ Q ≤ U ⊓ Q := fun T hT => And.intro (h T (And.left hT)) (And.right hT)
  have key := (CrystallineSemistableComparison.P.five (incl F U hQ) (resU F hle).hom (fun n => Subtype.val_injective)
    (res_exact F U Q hQ hle (incl F U hQ) (fun _ _ => rfl)) (res_surj F U Q hQ hle)
    (incl F U' hQ) (resU F hle').hom (fun n => Subtype.val_injective)
    (res_exact F U' Q hQ hle' (incl F U' hQ) (fun _ _ => rfl)) (res_surj F U' Q hQ hle')
    (RC.res F hQ h) (resU F h).hom (resU F hcc).hom (fun _ _ => rfl) (fun _ _ => rfl) 1).2.1
    (fun n => (upTo_one _).2 (hb n)) (fun n => (upTo_one _).2 (hc n)) n
  rw [one_pow] at key
  exact (upTo_one _).1 key

end Gen

end ZariskiRelativeForms

open ZariskiRelativeForms in
/- English proof (translation)
Introduce `hSite hOn hZar K _ W Z q i _ hQ ι V U hV h a n`. Use `rc_bij (G q a) hQ h (fun n => hZar K Z q ι V U hV h a n) (fun n => ?_) n` and prove the remaining obligations. Establish `hS` using `hSite K W Z W q i i`. Establish `hOnW : ∀ T, On q i ((smS i rfl).G.obj T)`. Introduce `T`.

Use `(hS.2.2.2.2.2 T).1 ?_` and prove the remaining obligations. Take `⟨w, hw⟩ : ∃ w, w = pt (γ` from `dividedPowersBot K) (p := 0) (q := i ≫ q) (κ := Ideal.Quotient.mk ⊥) T := ⟨_, rfl⟩`. Conclude with `⟨pullback.lift w w rfl, by rw [pullback.lift_snd, hw]⟩`. Set `UW : ObjectProperty (Thick (smFun W (i ≫ q)))` to `fun T => ∃ α, inU (i ≫ q) (i ⁻¹ᵁ U α) T`. Establish `hW : UW ≤ inU (i ≫ q) (i ⁻¹ᵁ V)` using `fun T hT => by`.

Take `⟨α, hα⟩` from `hT`. Conclude with `(hS.2.2.2.2.1 V T).2 (h _ ⟨α, (hS.2.2.2.2.1 (U α) T).1 hα⟩)`. Establish `h1 : ∀ T, inU (i ≫ q) (i ⁻¹ᵁ V) T → (inU q V ⊓ On q i) ((smS i rfl).G.obj T)` using `fun T hT => And.intro ((hS.2.2.2.2.1 V T).1 hT) (hOnW T)`. Establish `h2 : ∀ T, UW T → ((fun T => ∃ α, inU q (U α) T) ⊓ On q i) ((smS i rfl).G.obj T)`. Introduce `T hT`.

Take `⟨α, hα⟩` from `hT`. Conclude with `And.intro ⟨α, (hS.2.2.2.2.1 (U α) T).1 hα⟩ (hOnW T)`. Establish `hm1` using `hOn K W Z q i (inU q V) (inU (i ≫ q) (i ⁻¹ᵁ V)) h1 (fun T hT => (hS.2.2.2.2.1 V T).2 hT) a n`. Establish `hm2` using `hOn K W Z q i (fun T => ∃ α, inU q (U α) T) UW h2 (fun T hT => by`. Take `⟨α, hα⟩` from `hT`.

Conclude with `⟨α, (hS.2.2.2.2.1 (U α) T).2 hα⟩) a n`. Establish `hpre : (⨆ α, i ⁻¹ᵁ U α) = i ⁻¹ᵁ V`. Rewrite using `[← hV, Scheme.Hom.preimage_iSup]`. Establish `hB` using `hZar K W (i ≫ q) ι (i ⁻¹ᵁ V) (fun α => i ⁻¹ᵁ U α) hpre hW a n`. Establish `hcc : (fun T => ∃ α, inU q (U α) T) ⊓ On q i ≤ inU q V ⊓ On q i` using `fun T hT => And.intro (h T (And.left hT)) (And.right hT)`.

Establish `hcomm : ∀ x, (morV i rfl a h2).pull n ((resU (G q a) hcc).pull n x) = (resU (G (i ≫ q) a) hW).pull n ((morV i rfl a h1).pull n x)`. Introduce `x`. Take `⟨z, hz, rfl⟩` from `(CrystallineSemistableComparison.P.cls_surj _ n).1 x`. Both sides reduce to the same expression. Establish `key : (morV i rfl a h2).pull n ∘ (resU (G q a) hcc).pull n = (resU (G (i ≫ q) a) hW).pull n ∘ (morV i rfl a h1).pull n` using `funext hcomm`.

Conclude with `(Function.Bijective.of_comp_iff' hm2 _).1 (key ▸ hB.comp hm1)`.
-/
theorem zarRelOf_pf : ZarRelOf := by
  intro hSite hOn hZar K _ W Z q i _ hQ ι V U hV h a n
  refine rc_bij (G q a) hQ h (fun n => hZar K Z q ι V U hV h a n) (fun n => ?_) n
  have hS := hSite K W Z W q i i
  have hOnW : ∀ T, On q i ((smS i rfl).G.obj T) := by
    intro T
    refine (hS.2.2.2.2.2 T).1 ?_
    obtain ⟨w, hw⟩ : ∃ w, w = pt (γ := dividedPowersBot K) (p := 0) (q := i ≫ q) (κ := Ideal.Quotient.mk ⊥) T := ⟨_, rfl⟩
    exact ⟨pullback.lift w w rfl, by rw [pullback.lift_snd, hw]⟩
  let UW : ObjectProperty (Thick (smFun W (i ≫ q))) := fun T => ∃ α, inU (i ≫ q) (i ⁻¹ᵁ U α) T
  have hW : UW ≤ inU (i ≫ q) (i ⁻¹ᵁ V) := fun T hT => by
    obtain ⟨α, hα⟩ := hT
    exact (hS.2.2.2.2.1 V T).2 (h _ ⟨α, (hS.2.2.2.2.1 (U α) T).1 hα⟩)
  have h1 : ∀ T, inU (i ≫ q) (i ⁻¹ᵁ V) T → (inU q V ⊓ On q i) ((smS i rfl).G.obj T) :=
    fun T hT => And.intro ((hS.2.2.2.2.1 V T).1 hT) (hOnW T)
  have h2 : ∀ T, UW T → ((fun T => ∃ α, inU q (U α) T) ⊓ On q i) ((smS i rfl).G.obj T) := by
    intro T hT
    obtain ⟨α, hα⟩ := hT
    exact And.intro ⟨α, (hS.2.2.2.2.1 (U α) T).1 hα⟩ (hOnW T)
  have hm1 := hOn K W Z q i (inU q V) (inU (i ≫ q) (i ⁻¹ᵁ V)) h1 (fun T hT => (hS.2.2.2.2.1 V T).2 hT) a n
  have hm2 := hOn K W Z q i (fun T => ∃ α, inU q (U α) T) UW h2 (fun T hT => by
    obtain ⟨α, hα⟩ := hT
    exact ⟨α, (hS.2.2.2.2.1 (U α) T).2 hα⟩) a n
  have hpre : (⨆ α, i ⁻¹ᵁ U α) = i ⁻¹ᵁ V := by
    rw [← hV, Scheme.Hom.preimage_iSup]
  have hB := hZar K W (i ≫ q) ι (i ⁻¹ᵁ V) (fun α => i ⁻¹ᵁ U α) hpre hW a n
  have hcc : (fun T => ∃ α, inU q (U α) T) ⊓ On q i ≤ inU q V ⊓ On q i :=
    fun T hT => And.intro (h T (And.left hT)) (And.right hT)
  have hcomm : ∀ x, (morV i rfl a h2).pull n ((resU (G q a) hcc).pull n x) =
      (resU (G (i ≫ q) a) hW).pull n ((morV i rfl a h1).pull n x) := by
    intro x
    obtain ⟨z, hz, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ n).1 x
    rfl
  have key : (morV i rfl a h2).pull n ∘ (resU (G q a) hcc).pull n =
      (resU (G (i ≫ q) a) hW).pull n ∘ (morV i rfl a h1).pull n := funext hcomm
  exact (Function.Bijective.of_comp_iff' hm2 _).1 (key ▸ hB.comp hm1)

end CrystallineSemistableComparison.Onto

end
