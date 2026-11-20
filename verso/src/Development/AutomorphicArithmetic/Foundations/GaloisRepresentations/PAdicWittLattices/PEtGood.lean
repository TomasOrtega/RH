import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

/- English proof (translation)
Introduce `hE l _ B hl`. Establish `hn` using `fun n => hE l B hl n 0`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `Z W p r c hc G _ _ a hgal x y hxy`. Use `DFinsupp.ext fun n => ?_` and prove the remaining obligations.

Establish `h1` using `congrArg (fun v : Htot l (sch.obj W) => v n) hxy`. Conclude with `(hn n).inj p r c hc G a hgal h1`. Introduce `Z Y p q s _ _ hs choose tr htr using fun n => (hn n).tr p q s hs`. Set `tr' : ∀ n, HQ l (sch.obj Y) n 0 →ₗ[ℚ_[l]] HQ l (sch.obj Z) n 0` to `fun n => tr n`. Use `⟨DirectSum.lmap tr', ?_⟩` and prove the remaining obligations.

Introduce `W r c hc J _ σ hσ hsp`. Use `fun (x : Htot l (sch.obj Y)) => DFinsupp.ext fun n => ?_` and prove the remaining obligations. Establish `h1` using `htr n W r c hc J σ hσ hsp (x n)`. Conclude with `h1.trans (DFinsupp.finset_sum_apply Finset.univ (fun j => ((et l B).pull (σ j) (hσ j)) x) n).symm`.
-/
theorem UpperTheory.Gal.G3.pEtGood :
    EtnGood → EtGood := by
  intro hE l _ B hl
  have hn := fun n => hE l B hl n 0
  refine ⟨?_, ?_⟩
  · intro Z W p r c hc G _ _ a hgal x y hxy
    refine DFinsupp.ext fun n => ?_
    have h1 := congrArg (fun v : Htot l (sch.obj W) => v n) hxy
    exact (hn n).inj p r c hc G a hgal h1
  · intro Z Y p q s _ _ hs
    choose tr htr using fun n => (hn n).tr p q s hs
    let tr' : ∀ n, HQ l (sch.obj Y) n 0 →ₗ[ℚ_[l]] HQ l (sch.obj Z) n 0 := fun n => tr n
    refine ⟨DirectSum.lmap tr', ?_⟩
    intro W r c hc J _ σ hσ hsp
    refine fun (x : Htot l (sch.obj Y)) => DFinsupp.ext fun n => ?_
    have h1 := htr n W r c hc J σ hσ hsp (x n)
    exact h1.trans (DFinsupp.finset_sum_apply Finset.univ
      (fun j => ((et l B).pull (σ j) (hσ j)) x) n).symm
