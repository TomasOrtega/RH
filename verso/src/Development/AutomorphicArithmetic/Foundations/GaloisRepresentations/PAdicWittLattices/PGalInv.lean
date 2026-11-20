import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
private theorem pull_congr {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {X Y : Scheme.{0}}
    {p : X ⟶ B} {q : Y ⟶ B} {f f' : Y ⟶ X} (e : f = f') (h : f ≫ p = q) (h' : f' ≫ p = q) (x : T.H p) :
    T.pull f h x = T.pull f' h' x := by
  subst e; rfl

/- English proof (translation)
Introduce `B R _ _ T hT Z W p r c hc G _ _ a ha hgal y`. Take `⟨hac, -⟩` from `hgal.2.2.2.2.2`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩ g`. Establish `hcomp : (a g ≫ c) ≫ p = r` using `by rw [hac g, hc]`.

Rewrite using `[← T.pull_comp (a g) c (ha g) hc hcomp x]`. Conclude with `pull_congr T (hac g) hcomp hc x`. Introduce `hy haveI := hgal.1 haveI := hgal.2.1 haveI := Fintype.ofFinite G`. Take `⟨tr, htr⟩` from `hT.tr p r c hc`. Establish `key` using `htr W r c hc G a ha hgal.2.2.2.2.2 y`.

Establish `hsum : ∑ g, T.pull (a g) (ha g) y = (Fintype.card G : R) • y`. Rewrite using `[Finset.sum_congr rfl fun g _ => hy g, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul R]`. Use `⟨(Fintype.card G : R)⁻¹ • tr y, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, key, hsum, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_smul]`.
-/
theorem UpperTheory.Gal.G3.pGalInv :
    GalInv.{u} := by
  intro B R _ _ T hT Z W p r c hc G _ _ a ha hgal y
  obtain ⟨hac, -⟩ := hgal.2.2.2.2.2
  constructor
  · rintro ⟨x, rfl⟩ g
    have hcomp : (a g ≫ c) ≫ p = r := by rw [hac g, hc]
    rw [← T.pull_comp (a g) c (ha g) hc hcomp x]
    exact pull_congr T (hac g) hcomp hc x
  · intro hy
    haveI := hgal.1
    haveI := hgal.2.1
    haveI := Fintype.ofFinite G
    obtain ⟨tr, htr⟩ := hT.tr p r c hc
    have key := htr W r c hc G a ha hgal.2.2.2.2.2 y
    have hsum : ∑ g, T.pull (a g) (ha g) y = (Fintype.card G : R) • y := by
      rw [Finset.sum_congr rfl fun g _ => hy g, Finset.sum_const, Finset.card_univ,
        ← Nat.cast_smul_eq_nsmul R]
    refine ⟨(Fintype.card G : R)⁻¹ • tr y, ?_⟩
    rw [map_smul, key, hsum, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_smul]
