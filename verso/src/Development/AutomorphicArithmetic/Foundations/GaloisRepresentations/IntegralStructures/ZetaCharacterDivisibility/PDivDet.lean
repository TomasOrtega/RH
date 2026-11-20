import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

/- English proof (translation)
Introduce `hD hF E Ω _ _ _ _ _ _ l _ ι a d hd U hU ψ hψ r hr g`. Take `⟨hrc, -, V, X, hVo, hVd, hV⟩` from `hr`. Establish `hc1 : Continuous fun g : G E Ω => (r g : Matrix (Fin a) (Fin a) (Qbar l)).det` using `Continuous.matrix_det (Units.continuous_val.comp hrc)`. Establish `hc2 : Continuous fun g : G E Ω => ((ψ g : (Qbar l)ˣ) : Qbar l)` using `Units.continuous_val.comp hψ.1`. Establish `hdense` using `((hD E Ω l a d hd U hU X).inter_of_isOpen_right hVd hVo).preimage (Homeomorph.inv (G E Ω)).isOpenMap`.

Use `congrFun (Continuous.ext_on hdense hc1 hc2 ?_) g` and prove the remaining obligations. Introduce and unpack `x ⟨⟨w, hwX, hUs, hl, ⟨B, hB⟩, A, hA, hFr⟩, hxV⟩`. Establish `hx : (x⁻¹)⁻¹ = x` using `inv_inv x`. Establish `hch` using `(hV w hwX hUs hl B hB A hA).2 x⁻¹ hFr hxV`. Rewrite `hch` using `[hx]`.

Establish `hψv` using `(hF E Ω l ι a U ψ hψ w hUs.1 hl B hB A hA).2 x⁻¹ hFr`. Rewrite `hψv` using `[hx]`. Apply `ι.injective` to reduce the goal to its premises. Rewrite using `[hψv]`. Establish `hcard : (algSat a (normV w) B).card = a`.

Establish `h1` using `congrArg Polynomial.natDegree hch`. Rewrite `h1` using `[Polynomial.natDegree_map, Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]`. Simplify using `using h1.symm`. Establish `h0` using `congrArg (fun p => Polynomial.coeff p 0) hch`. Simplify using `only [Polynomial.coeff_map] at h0`.

Establish `hdet : (r x : Matrix (Fin a) (Fin a) (Qbar l)).det = (-1) ^ a * (r x : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.coeff 0`. Simplify using `using Matrix.det_eq_sign_charpoly_coeff (r x : Matrix (Fin a) (Fin a) (Qbar l))`. Establish `h1 : ι ((r x : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.coeff 0) = (Multiset.map (fun b => Polynomial.X - C b) (algSat a (normV w) B)).prod.coeff 0` using `h0`. Establish `h2 : (Multiset.map (fun b => Polynomial.X - C b) (algSat a (normV w) B)).prod.coeff 0 = (-1) ^ a * (algSat a (normV w) B).prod`. Rewrite using `[Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_multiset_prod, Multiset.map_map]`.

Establish `: (Multiset.map (Polynomial.eval 0 ∘ fun b : ℂ => Polynomial.X - C b) (algSat a (normV w) B)) = Multiset.map Neg.neg (algSat a (normV w) B)` using `Multiset.map_congr rfl fun b _ => by simp`. Rewrite using `[this, Multiset.prod_map_neg, hcard]`. Use `show ι (r x : Matrix (Fin a) (Fin a) (Qbar l)).det = _`. Rewrite using `[hdet, map_mul, h1, h2, map_pow, map_neg, map_one, ← mul_assoc, ← mul_pow]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.Gal.Int.Div.divDet_of :
    DenseUs → DetFrob → DivDet := by
  intro hD hF E Ω _ _ _ _ _ _ l _ ι a d hd U hU ψ hψ r hr g
  obtain ⟨hrc, -, V, X, hVo, hVd, hV⟩ := hr
  have hc1 : Continuous fun g : G E Ω => (r g : Matrix (Fin a) (Fin a) (Qbar l)).det :=
    Continuous.matrix_det (Units.continuous_val.comp hrc)
  have hc2 : Continuous fun g : G E Ω => ((ψ g : (Qbar l)ˣ) : Qbar l) :=
    Units.continuous_val.comp hψ.1
  have hdense := ((hD E Ω l a d hd U hU X).inter_of_isOpen_right hVd hVo).preimage
    (Homeomorph.inv (G E Ω)).isOpenMap
  refine congrFun (Continuous.ext_on hdense hc1 hc2 ?_) g
  rintro x ⟨⟨w, hwX, hUs, hl, ⟨B, hB⟩, A, hA, hFr⟩, hxV⟩
  have hx : (x⁻¹)⁻¹ = x := inv_inv x
  have hch := (hV w hwX hUs hl B hB A hA).2 x⁻¹ hFr hxV
  rw [hx] at hch
  have hψv := (hF E Ω l ι a U ψ hψ w hUs.1 hl B hB A hA).2 x⁻¹ hFr
  rw [hx] at hψv
  apply ι.injective
  rw [hψv]
  have hcard : (algSat a (normV w) B).card = a := by
    have h1 := congrArg Polynomial.natDegree hch
    rw [Polynomial.natDegree_map, Matrix.charpoly_natDegree_eq_dim,
      Polynomial.natDegree_multiset_prod_X_sub_C_eq_card] at h1
    simpa using h1.symm
  have h0 := congrArg (fun p => Polynomial.coeff p 0) hch
  simp only [Polynomial.coeff_map] at h0
  have hdet : (r x : Matrix (Fin a) (Fin a) (Qbar l)).det =
      (-1) ^ a * (r x : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.coeff 0 := by
    simpa using Matrix.det_eq_sign_charpoly_coeff (r x : Matrix (Fin a) (Fin a) (Qbar l))
  have h1 : ι ((r x : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.coeff 0) =
      (Multiset.map (fun b => Polynomial.X - C b) (algSat a (normV w) B)).prod.coeff 0 := h0
  have h2 : (Multiset.map (fun b => Polynomial.X - C b) (algSat a (normV w) B)).prod.coeff 0 =
      (-1) ^ a * (algSat a (normV w) B).prod := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_multiset_prod, Multiset.map_map]
    have : (Multiset.map (Polynomial.eval 0 ∘ fun b : ℂ => Polynomial.X - C b) (algSat a (normV w) B)) =
        Multiset.map Neg.neg (algSat a (normV w) B) :=
      Multiset.map_congr rfl fun b _ => by simp
    rw [this, Multiset.prod_map_neg, hcard]
  show ι (r x : Matrix (Fin a) (Fin a) (Qbar l)).det = _
  rw [hdet, map_mul, h1, h2, map_pow, map_neg, map_one, ← mul_assoc, ← mul_pow]
  simp
