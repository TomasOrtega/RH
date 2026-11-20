import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

/- English proof (translation)
Introduce `hPl B G _ X R _ _ T hT j f hf`. Establish `hfin` using `hf.2.2`. Establish `hpush : ∀ (n n' : X.ι), X.K n' ≤ X.K n → (∀ g, f g ≠ 0 → X.admitted n j g⁻¹) → ∀ x : T.H (X.q j), X.pl T n' n 1 (∑ᶠ z : G ⧸ X.K j, f z.out • X.pl T n j z.out⁻¹ x) = ∑ᶠ z : G ⧸ X.K j, f z.out • X.pl T n' j z.out⁻¹ x`. Introduce `n n' hn'n hadn x`. Rewrite using `[map_finsum _ (hfin.subset ?_)]`.

Use `finsum_congr fun z => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`. Distinguish the cases in `h0 : f z.out = 0`. Simplify using `[h0]`. Rewrite using `[X.pl_pl T (X.isAdmissibleIntegralBasisChange_one hn'n) (hadn _ h0), mul_one]`.

Introduce `z hz`. Simplify using `only [Set.mem_setOf_eq]`. Introduce `h0`. Conclude with `hz (by simp [h0])`. Prove the components needed by the constructor for the conclusion.

Take `⟨m, hmj, -, hS⟩` from `X.deep j (hfin.toFinset.image fun z => (j, (Quotient.out z)⁻¹))`. Use `⟨m, hmj, fun g hg => ⟨hf.2.1 g hg, fun u hu => ?_⟩⟩` and prove the remaining obligations. Take `⟨⟨h, hh⟩, hheq⟩` from `QuotientGroup.mk_out_eq_mul (X.K j) g`. Establish `hz : (g : G ⧸ X.K j) ∈ hfin.toFinset`. Rewrite using `[Set.Finite.mem_toFinset, Set.mem_setOf_eq, hheq, (hf.1 h hh g).2]`.

Conclude with `hg`. Establish `hc` using `hS (j, (Quotient.out (g : G ⧸ X.K j))⁻¹) (Finset.mem_image_of_mem _ hz) u hu`. Simplify using `only [hheq] at hc`. Establish `hmem` using `mul_mem (mul_mem hh hc) (inv_mem hh)`. Use `hmem using 1` and compare the differences between its conclusion and the goal.

Use `group`. Introduce `A m hmj hadm hA m' hm'j hadm' x`. Take `⟨n, -, -, hS⟩` from `X.deep j {(m, 1), (m', 1)}`. Establish `hnm : X.K n ≤ X.K m` using `fun u hu => by simpa using hS (m, 1) (by simp) u hu`. Establish `hnm' : X.K n ≤ X.K m'` using `fun u hu => by simpa using hS (m', 1) (by simp) u hu`.

Apply `(hPl X T hT n m' hnm').1` to reduce the goal to its premises. Rewrite using `[hpush m' n hnm' hadm', X.pl_pl T (X.isAdmissibleIntegralBasisChange_one hnm') (X.isAdmissibleIntegralBasisChange_one hm'j), ← hpush m n hnm hadm, ← hA, X.pl_pl T (X.isAdmissibleIntegralBasisChange_one hnm) (X.isAdmissibleIntegralBasisChange_one hmj)]`.
-/
theorem UpperTheory.Gal.G3.pHopDeep :
    PlInv.{u} → HopDeep.{u} := by
  classical
  intro hPl B G _ X R _ _ T hT j f hf
  have hfin := hf.2.2
  have hpush : ∀ (n n' : X.ι), X.K n' ≤ X.K n → (∀ g, f g ≠ 0 → X.admitted n j g⁻¹) → ∀ x : T.H (X.q j),
      X.pl T n' n 1 (∑ᶠ z : G ⧸ X.K j, f z.out • X.pl T n j z.out⁻¹ x) =
        ∑ᶠ z : G ⧸ X.K j, f z.out • X.pl T n' j z.out⁻¹ x := by
    intro n n' hn'n hadn x
    rw [map_finsum _ (hfin.subset ?_)]
    · refine finsum_congr fun z => ?_
      rw [map_smul]
      by_cases h0 : f z.out = 0
      · simp [h0]
      · rw [X.pl_pl T (X.isAdmissibleIntegralBasisChange_one hn'n) (hadn _ h0), mul_one]
    · intro z hz
      simp only [Set.mem_setOf_eq]
      intro h0
      exact hz (by simp [h0])
  constructor
  · obtain ⟨m, hmj, -, hS⟩ := X.deep j (hfin.toFinset.image fun z => (j, (Quotient.out z)⁻¹))
    refine ⟨m, hmj, fun g hg => ⟨hf.2.1 g hg, fun u hu => ?_⟩⟩
    obtain ⟨⟨h, hh⟩, hheq⟩ := QuotientGroup.mk_out_eq_mul (X.K j) g
    have hz : (g : G ⧸ X.K j) ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, hheq, (hf.1 h hh g).2]
      exact hg
    have hc := hS (j, (Quotient.out (g : G ⧸ X.K j))⁻¹) (Finset.mem_image_of_mem _ hz) u hu
    simp only [hheq] at hc
    have hmem := mul_mem (mul_mem hh hc) (inv_mem hh)
    convert hmem using 1
    group
  · intro A m hmj hadm hA m' hm'j hadm' x
    obtain ⟨n, -, -, hS⟩ := X.deep j {(m, 1), (m', 1)}
    have hnm : X.K n ≤ X.K m := fun u hu => by simpa using hS (m, 1) (by simp) u hu
    have hnm' : X.K n ≤ X.K m' := fun u hu => by simpa using hS (m', 1) (by simp) u hu
    apply (hPl X T hT n m' hnm').1
    rw [hpush m' n hnm' hadm', X.pl_pl T (X.isAdmissibleIntegralBasisChange_one hnm') (X.isAdmissibleIntegralBasisChange_one hm'j), ← hpush m n hnm hadm, ← hA,
      X.pl_pl T (X.isAdmissibleIntegralBasisChange_one hnm) (X.isAdmissibleIntegralBasisChange_one hmj)]
