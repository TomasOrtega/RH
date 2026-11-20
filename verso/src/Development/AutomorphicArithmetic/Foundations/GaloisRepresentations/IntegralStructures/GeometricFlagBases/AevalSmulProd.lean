import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PCpFacts

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Proceed by induction on `S using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons z S ih`. Rewrite using `[Multiset.card_cons, Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, map_mul (aeval (c • M)), map_mul (aeval M), ih]`. Simplify using `only [map_sub, aeval_X, aeval_C]`.

Establish `e : (algebraMap K (Matrix (Fin n) (Fin n) K)) (z * c) = c • (algebraMap K (Matrix (Fin n) (Fin n) K)) z`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul, mul_comm]`. Rewrite using `[e, ← smul_sub, smul_mul_smul_comm, pow_succ']`.
-/
private theorem aeval_smul_prod {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (c : K) (S : Multiset K) :
    aeval (c • M) ((S.map fun b => X - C (b * c)).prod) =
      c ^ Multiset.card S • aeval M ((S.map fun b => X - C b).prod) := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons z S ih =>
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, map_mul (aeval (c • M)), map_mul (aeval M), ih]
    simp only [map_sub, aeval_X, aeval_C]
    have e : (algebraMap K (Matrix (Fin n) (Fin n) K)) (z * c) = c • (algebraMap K (Matrix (Fin n) (Fin n) K)) z := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul, mul_comm]
    rw [e, ← smul_sub, smul_mul_smul_comm, pow_succ']

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ l _ ι dd ρ χ _ _ w c m hCl hw R hES A hA`. Establish `hχ` using `hCl.1 hw A hA`. Take `⟨hi, hf⟩` from `hES A hA`. Use `⟨fun s hs => ?_, fun σ hσ => ?_⟩` and prove the remaining obligations. Establish `h1` using `(hχ.1 s hs)`.

Establish `h2 : (χ s : Qbar l) = 1`. Establish `h3 : ((GlobalTheory.TripleGal.rk1 χ s : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar l)) 0 0 = (χ s : Qbar l)`. Simplify using `[GlobalTheory.TripleGal.rk1]`. Rewrite `h3` using `[h1]`. Simplify using `using h3.symm`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[UpperTheory.V.Af.tw_val, hi s hs, h2]`. Simplify using the standard rewrite rules. Establish `hk : ι ((χ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = c`. Establish `h1` using `(hχ.2 σ hσ)`.

Establish `h2` using `(UpperTheory.Gal.TP.Sub.cpFacts_holds (G E Ω) (Qbar l) 0 0).2.1 χ σ⁻¹`. Simplify using `only [UpperTheory.Gal.TP.Sub.cp] at h2`. Rewrite `h1` using `[h2]`. Simplify using `only [Multiset.map_singleton, Multiset.prod_singleton, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at h1`. Conclude with `C_injective (sub_right_injective h1)`.

Establish `hs : ∀ T : Multiset ℂ, ((T.map fun b => X - C b).prod).map ι.symm.toRingHom = ((T.map ι.symm).map fun b => X - C b).prod`. Introduce `T`. Rewrite using `[Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]`. Use `congrArg _ (Multiset.map_congr rfl fun x _ => ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules.

Establish `hc : ι.symm c = ((χ σ⁻¹ : (Qbar l)ˣ) : Qbar l)`. Rewrite using `[← hk]`. Simplify using the standard rewrite rules. Establish `hfin` using `hf σ hσ`. Rewrite `hfin` using `[hs]`.

Establish `hR : (R.map (· * c)).map ι.symm = (R.map ι.symm).map (· * ((χ σ⁻¹ : (Qbar l)ˣ) : Qbar l))`. Rewrite using `[Multiset.map_map, Multiset.map_map]`. Use `Multiset.map_congr rfl fun x _ => ?_` and prove the remaining obligations. Simplify using `[map_mul, hc]`. Rewrite using `[UpperTheory.V.Af.tw_val, hs, hR, Multiset.map_map]`.

Use `aeval_smul_prod (ρ σ⁻¹ : Matrix (Fin dd) (Fin dd) (Qbar l)) ((χ σ⁻¹ : (Qbar l)ˣ) : Qbar l) (R.map ι.symm)` as an intermediate fact. Rewrite `this` using `[hfin, smul_zero]`. Conclude with `this`.
-/
theorem UpperTheory.Gal.Int.Geo.twES :
    UpperTheory.Gal.Int.Geo.TwES := by
  intro E Ω _ _ _ _ _ l _ ι dd ρ χ _ _ w c m hCl hw R hES A hA
  have hχ := hCl.1 hw A hA
  obtain ⟨hi, hf⟩ := hES A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h1 := (hχ.1 s hs)
    have h2 : (χ s : Qbar l) = 1 := by
      have h3 : ((GlobalTheory.TripleGal.rk1 χ s : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar l)) 0 0 = (χ s : Qbar l) := by
        simp [GlobalTheory.TripleGal.rk1]
      rw [h1] at h3
      simpa using h3.symm
    apply Units.ext
    rw [UpperTheory.V.Af.tw_val, hi s hs, h2]
    simp
  · have hk : ι ((χ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = c := by
      have h1 := (hχ.2 σ hσ)
      have h2 := (UpperTheory.Gal.TP.Sub.cpFacts_holds (G E Ω) (Qbar l) 0 0).2.1 χ σ⁻¹
      simp only [UpperTheory.Gal.TP.Sub.cp] at h2
      rw [h2] at h1
      simp only [Multiset.map_singleton, Multiset.prod_singleton, Polynomial.map_sub, Polynomial.map_X,
        Polynomial.map_C] at h1
      exact C_injective (sub_right_injective h1)
    have hs : ∀ T : Multiset ℂ, ((T.map fun b => X - C b).prod).map ι.symm.toRingHom =
        ((T.map ι.symm).map fun b => X - C b).prod := by
      intro T
      rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
      refine congrArg _ (Multiset.map_congr rfl fun x _ => ?_)
      simp
    have hc : ι.symm c = ((χ σ⁻¹ : (Qbar l)ˣ) : Qbar l) := by
      rw [← hk]; simp
    have hfin := hf σ hσ
    rw [hs] at hfin
    have hR : (R.map (· * c)).map ι.symm = (R.map ι.symm).map (· * ((χ σ⁻¹ : (Qbar l)ˣ) : Qbar l)) := by
      rw [Multiset.map_map, Multiset.map_map]
      refine Multiset.map_congr rfl fun x _ => ?_
      simp [map_mul, hc]
    rw [UpperTheory.V.Af.tw_val, hs, hR, Multiset.map_map]
    have := aeval_smul_prod (ρ σ⁻¹ : Matrix (Fin dd) (Fin dd) (Qbar l)) ((χ σ⁻¹ : (Qbar l)ˣ) : Qbar l) (R.map ι.symm)
    rw [hfin, smul_zero] at this
    exact this
