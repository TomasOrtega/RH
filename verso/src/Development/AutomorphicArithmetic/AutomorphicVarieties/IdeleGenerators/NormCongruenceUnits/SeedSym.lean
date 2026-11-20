import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.NormOneOfFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisReg
import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.IsIntegralOfNormLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.SelfTwGal
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Ad0IrrMulVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.QuadraticCharpolyCoeffDifference
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.SymmetricCubePreservesSymplecticForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SchurTwistHolds

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd

/- English proof (translation)
Establish `ho : IsOpen (φ.ker : Set (G F Ω))`. Establish `hfin : {ζ : Ω | ζ ^ M = 1}.Finite` using `by classical`. Use `(Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_` and prove the remaining obligations. Simplify `hζ` using `[Polynomial.mem_nthRoots hM]`. Use `Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := F) ζ).mem_nhds ?_) fun s hs => ?_)` and prove the remaining obligations.

Simplify using `only [Set.mem_iInter]`. Conclude with `fun ζ _ => Subgroup.one_mem _`. Simplify using `only [Set.mem_iInter] at hs`. Conclude with `hφ s fun ζ hζ => hs ζ hζ`. Establish `: IsGalois F Ω` using `IsAlgClosure.isGalois F Ω`.

Establish `hfi : Finite (G F Ω ⧸ φ.ker)` using `Subgroup.quotient_finite_of_isOpen _ ho`. Establish `hpos : 0 < φ.ker.index` using `Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite`. Use `isOfFinOrder_iff_pow_eq_one.2 ⟨_, hpos, MonoidHom.ext fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.pow_apply, ← map_pow]`. Conclude with `φ.ker.pow_index_mem s`.
-/
private theorem finOrd_kills {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {M : ℕ} (hM : 1 ≤ M) {φ : G F Ω →* (Qbar l)ˣ} (hφ : KillsMu M φ) : IsOfFinOrder φ := by
  have ho : IsOpen (φ.ker : Set (G F Ω)) := by
    have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
      classical
      refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
      simpa [Polynomial.mem_nthRoots hM] using hζ
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
      ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := F) ζ).mem_nhds ?_) fun s hs => ?_)
    · simp only [Set.mem_iInter]
      exact fun ζ _ => Subgroup.one_mem _
    · simp only [Set.mem_iInter] at hs
      exact hφ s fun ζ hζ => hs ζ hζ
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have hfi : Finite (G F Ω ⧸ φ.ker) := Subgroup.quotient_finite_of_isOpen _ ho
  have hpos : 0 < φ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨_, hpos, MonoidHom.ext fun s => ?_⟩
  rw [MonoidHom.pow_apply, ← map_pow]
  exact φ.ker.pow_index_mem s
