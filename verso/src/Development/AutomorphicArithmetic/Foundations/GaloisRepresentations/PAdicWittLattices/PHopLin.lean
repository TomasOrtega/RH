import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

/- English proof (translation)
Use `hf.2.2.subset ?_` and prove the remaining obligations. Introduce `y hy h0`. Conclude with `hy (by simp only [h0, zero_smul])`.
-/
private lemma supp_fin {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R] (T : Th.{u} B R)
    {j m : X.ι} {f : G → R} (hf : X.IsFn j f) (x : T.H (X.q j)) :
    (Function.support fun y : G ⧸ X.K j => f y.out • X.pl T m j y.out⁻¹ x).Finite := by
  refine hf.2.2.subset ?_
  intro y hy h0
  exact hy (by simp only [h0, zero_smul])

/- English proof (translation)
Introduce `hR hD hE B G _ X R _ _ T hT j f f' c hf hf'`. Take `⟨⟨m1, hm1, ha1⟩, -⟩` from `hD X T hT j f hf`. Take `⟨⟨m2, hm2, ha2⟩, -⟩` from `hD X T hT j f' hf'`. Take `⟨m, hmm1, -, hS⟩` from `X.deep m1 {(m2, 1)}`. Establish `hmm2 : X.K m ≤ X.K m2`.

Introduce `u hu`. Simplify using `using hS (m2, 1) (by simp) u hu`. Establish `hmj : X.K m ≤ X.K j` using `hmm1.trans hm1`. Establish `hA1 : ∀ g, f g ≠ 0 → X.admitted m j g⁻¹` using `fun g hg => by`. Simplify using `using (X.isAdmissibleIntegralBasisChange_one hmm1).mul (ha1 g hg)`.

Establish `hA2 : ∀ g, f' g ≠ 0 → X.admitted m j g⁻¹` using `fun g hg => by`. Simplify using `using (X.isAdmissibleIntegralBasisChange_one hmm2).mul (ha2 g hg)`. Establish `e1` using `(hE X T hT j f hf).1 m hmj hA1`. Establish `e2` using `(hE X T hT j f' hf').1 m hmj hA2`. Establish `hsum` using `((hR X R j).2.2.1 f f' hf hf').1`.

Establish `hc` using `(hR X R j).2.2.2 c f hf`. Prove the components needed by the constructor for the conclusion. Use `symm`. Apply `(hE X T hT j (f + f') hsum).2` to reduce the goal to its premises. Apply `(hD X T hT j (f + f') hsum).2 _ m hmj` to reduce the goal to its premises.

Introduce `g hg`. Distinguish the cases in `h1 : f g = 0`. Apply `hA2 g` to reduce the goal to its premises. Introduce `h2`. Apply `hg` to reduce the goal to its premises.

Simplify using `[h1, h2]`. Conclude with `hA1 g h1`. Introduce `x`. Rewrite using `[LinearMap.add_apply, map_add, e1 x, e2 x, ← finsum_add_distrib (supp_fin (m := m) X T hf x) (supp_fin (m := m) X T hf' x)]`. Apply `finsum_congr` to reduce the goal to its premises.

Introduce `y`. Simplify using `[add_smul]`. Use `symm`. Apply `(hE X T hT j (c • f) hc).2` to reduce the goal to its premises. Apply `(hD X T hT j (c • f) hc).2 _ m hmj` to reduce the goal to its premises.

Introduce `g hg`. Apply `hA1 g` to reduce the goal to its premises. Introduce `h`. Apply `hg` to reduce the goal to its premises. Simplify using `[h]`.

Introduce `x`. Rewrite using `[LinearMap.smul_apply, map_smul, e1 x, smul_finsum]`. Apply `finsum_congr` to reduce the goal to its premises. Introduce `y`. Simplify using `[smul_smul]`.
-/
theorem UpperTheory.Gal.G3.pHopLin :
    FnRing → HopDeep.{u} → HopEx.{u} → HopLin.{u} := by
  intro hR hD hE B G _ X R _ _ T hT j f f' c hf hf'
  obtain ⟨⟨m1, hm1, ha1⟩, -⟩ := hD X T hT j f hf
  obtain ⟨⟨m2, hm2, ha2⟩, -⟩ := hD X T hT j f' hf'
  obtain ⟨m, hmm1, -, hS⟩ := X.deep m1 {(m2, 1)}
  have hmm2 : X.K m ≤ X.K m2 := by
    intro u hu
    simpa using hS (m2, 1) (by simp) u hu
  have hmj : X.K m ≤ X.K j := hmm1.trans hm1
  have hA1 : ∀ g, f g ≠ 0 → X.admitted m j g⁻¹ := fun g hg => by
    simpa using (X.isAdmissibleIntegralBasisChange_one hmm1).mul (ha1 g hg)
  have hA2 : ∀ g, f' g ≠ 0 → X.admitted m j g⁻¹ := fun g hg => by
    simpa using (X.isAdmissibleIntegralBasisChange_one hmm2).mul (ha2 g hg)
  have e1 := (hE X T hT j f hf).1 m hmj hA1
  have e2 := (hE X T hT j f' hf').1 m hmj hA2
  have hsum := ((hR X R j).2.2.1 f f' hf hf').1
  have hc := (hR X R j).2.2.2 c f hf
  constructor
  · symm
    apply (hE X T hT j (f + f') hsum).2
    apply (hD X T hT j (f + f') hsum).2 _ m hmj
    · intro g hg
      by_cases h1 : f g = 0
      · apply hA2 g
        intro h2
        apply hg
        simp [h1, h2]
      · exact hA1 g h1
    · intro x
      rw [LinearMap.add_apply, map_add, e1 x, e2 x,
        ← finsum_add_distrib (supp_fin (m := m) X T hf x) (supp_fin (m := m) X T hf' x)]
      apply finsum_congr
      intro y
      simp [add_smul]
  · symm
    apply (hE X T hT j (c • f) hc).2
    apply (hD X T hT j (c • f) hc).2 _ m hmj
    · intro g hg
      apply hA1 g
      intro h
      apply hg
      simp [h]
    · intro x
      rw [LinearMap.smul_apply, map_smul, e1 x, smul_finsum]
      apply finsum_congr
      intro y
      simp [smul_smul]
