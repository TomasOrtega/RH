import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularSmooth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.IsPrecompleteOfBasis

open IsLocalRing Polynomial

namespace GlobalTheory.MonicRootExtension

section
variable {A : Type} [CommRing A] [IsLocalRing A] (M : A[X]) (hM : M.Monic)
  (hirr : Irreducible (M.map (residue A)))

include hM hirr

/- English proof (translation)
Use `haveI : Fact (Irreducible (M.map (residue A))) := ⟨hirr⟩`. Establish `hR : IsField (AdjoinRoot (M.map (residue A)))` using `Field.toIsField _`. Rewrite using `[AdjoinRoot.algebraMap_eq]`. Conclude with `Ideal.Quotient.maximal_of_isField _ (MulEquiv.isField hR (AdjoinRoot.quotEquivQuotMap M (maximalIdeal A)).toRingEquiv.toMulEquiv)`.
-/
theorem map_maximalIdeal_isMaximal :
    ((maximalIdeal A).map (algebraMap A (AdjoinRoot M))).IsMaximal := by
  haveI : Fact (Irreducible (M.map (residue A))) := ⟨hirr⟩
  have hR : IsField (AdjoinRoot (M.map (residue A))) := Field.toIsField _
  rw [AdjoinRoot.algebraMap_eq]
  exact Ideal.Quotient.maximal_of_isField _
    (MulEquiv.isField hR (AdjoinRoot.quotEquivQuotMap M (maximalIdeal A)).toRingEquiv.toMulEquiv)

/- English proof (translation)
Establish `: Module.Finite A (AdjoinRoot M)` using `.of_basis (AdjoinRoot.powerBasis' hM).basis`. Use `IsLocalRing.of_unique_max_ideal ⟨_, map_maximalIdeal_isMaximal M hM hirr, fun P hP => ?_⟩` and prove the remaining obligations. Establish `hc : (P.comap (algebraMap A (AdjoinRoot M))).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P`. Establish `h1 : P.comap (algebraMap A (AdjoinRoot M)) = maximalIdeal A` using `IsLocalRing.eq_maximalIdeal hc`. Establish `hle : (maximalIdeal A).map (algebraMap A (AdjoinRoot M)) ≤ P` using `Ideal.map_le_iff_le_comap.2 h1.ge`.

Conclude with `((map_maximalIdeal_isMaximal M hM hirr).eq_of_le hP.ne_top hle).symm`.
-/
theorem isLocalRing : IsLocalRing (AdjoinRoot M) := by
  have : Module.Finite A (AdjoinRoot M) := .of_basis (AdjoinRoot.powerBasis' hM).basis
  refine IsLocalRing.of_unique_max_ideal ⟨_, map_maximalIdeal_isMaximal M hM hirr, fun P hP => ?_⟩
  have hc : (P.comap (algebraMap A (AdjoinRoot M))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have h1 : P.comap (algebraMap A (AdjoinRoot M)) = maximalIdeal A := IsLocalRing.eq_maximalIdeal hc
  have hle : (maximalIdeal A).map (algebraMap A (AdjoinRoot M)) ≤ P :=
    Ideal.map_le_iff_le_comap.2 h1.ge
  exact ((map_maximalIdeal_isMaximal M hM hirr).eq_of_le hP.ne_top hle).symm

/- English proof (translation)
The claim follows from `IsLocalRing.eq_maximalIdeal (map_maximalIdeal_isMaximal M hM hirr)`.
-/
theorem maximalIdeal_eq [IsLocalRing (AdjoinRoot M)] :
    (maximalIdeal A).map (algebraMap A (AdjoinRoot M)) = maximalIdeal (AdjoinRoot M) :=
  IsLocalRing.eq_maximalIdeal (map_maximalIdeal_isMaximal M hM hirr)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x hx`. Assume the negation of the conclusion as `h`. Establish `h2 : algebraMap A (AdjoinRoot M) x ∈ maximalIdeal (AdjoinRoot M)`. Rewrite using `[← maximalIdeal_eq M hM hirr]`.

Conclude with `Ideal.mem_map_of_mem _ h`. Conclude with `h2 hx`.
-/
theorem isLocalHom [IsLocalRing (AdjoinRoot M)] : IsLocalHom (algebraMap A (AdjoinRoot M)) := by
  constructor
  intro x hx
  by_contra h
  have h2 : algebraMap A (AdjoinRoot M) x ∈ maximalIdeal (AdjoinRoot M) := by
    rw [← maximalIdeal_eq M hM hirr]; exact Ideal.mem_map_of_mem _ h
  exact h2 hx

end

section
variable {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  (M : A[X]) (hM : M.Monic) (hirr : Irreducible (M.map (residue A)))
include hM hirr

/- English proof (translation)
Establish `: Module.Finite A (AdjoinRoot M)` using `.of_basis (AdjoinRoot.powerBasis' hM).basis`. Rewrite using `[← maximalIdeal_eq M hM hirr, IsAdicComplete.map_algebraMap_iff]`. Use `haveI : IsPrecomplete (maximalIdeal A) (AdjoinRoot M) := ReciprocityTheory.ChartRestriction.G.Semi.Nb.isPrecomplete_of_basis _ (AdjoinRoot.powerBasis' hM).basis`. Conclude with `{ toIsHausdorff := inferInstance, toIsPrecomplete := inferInstance }`.
-/
theorem isAdicComplete [IsLocalRing (AdjoinRoot M)] [IsAdicComplete (maximalIdeal A) A] :
    IsAdicComplete (maximalIdeal (AdjoinRoot M)) (AdjoinRoot M) := by
  have : Module.Finite A (AdjoinRoot M) := .of_basis (AdjoinRoot.powerBasis' hM).basis
  rw [← maximalIdeal_eq M hM hirr, IsAdicComplete.map_algebraMap_iff]
  haveI : IsPrecomplete (maximalIdeal A) (AdjoinRoot M) :=
    ReciprocityTheory.ChartRestriction.G.Semi.Nb.isPrecomplete_of_basis _ (AdjoinRoot.powerBasis' hM).basis
  exact { toIsHausdorff := inferInstance, toIsPrecomplete := inferInstance }

end

/- English proof (translation)
Introduce `A Ω _ _ _ u p α hker hcpl hp hroot _`. Set `ub : ResidueField A →+* Ω` to `Ideal.Quotient.lift (maximalIdeal A) u (fun x hx => (RingHom.mem_ker).1 (hker ▸ hx))`. Establish `hub : ∀ x, ub (residue A x) = u x` using `fun x => rfl`. Use `letI : Algebra (ResidueField A) Ω := ub.toAlgebra`. Establish `hpu : p.map u = (p.map (residue A)).map ub`.

Rewrite using `[Polynomial.map_map]`. Use `congr 1`. Establish `hint : IsIntegral (ResidueField A) α`. Use `⟨p.map (residue A), hp.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.eval_map]`.

Express the relevant statement in the definitionally equal form `eval α ((p.map (residue A)).map ub) = 0`. Rewrite using `[← hpu]`. Conclude with `hroot`. Use `set m := minpoly (ResidueField A) α`. Take `⟨q, hq⟩` from `Polynomial.map_surjective _ (residue_surjective (R := A)) m`.

Take `⟨M, hMm, -, hM⟩` from `lifts_and_natDegree_eq_and_monic ((mem_lifts _).2 ⟨q, hq⟩) (minpoly.monic hint)`. Establish `hirr : Irreducible (M.map (residue A))` using `hMm ▸ minpoly.irreducible hint`. Use `haveI := isLocalRing M hM hirr`. Use `haveI : Module.Finite A (AdjoinRoot M) := .of_basis (AdjoinRoot.powerBasis' hM).basis`. Use `haveI : Module.Free A (AdjoinRoot M) := .of_basis (AdjoinRoot.powerBasis' hM).basis`.

Use `haveI : IsNoetherianRing (AdjoinRoot M) := isNoetherian_of_tower A inferInstance`. Use `haveI := isLocalHom M hM hirr`. Use `haveI : IsRegularLocalRing (AdjoinRoot M) := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.of_flat_of_map_maximalIdeal (maximalIdeal_eq M hM hirr)`. Establish `hev : M.eval₂ u α = 0`. Establish `h1 : M.eval₂ u α = (M.map (residue A)).eval₂ ub α`.

Rewrite using `[Polynomial.eval₂_map]`. Both sides reduce to the same expression. Rewrite using `[h1, hMm]`. Conclude with `minpoly.aeval (ResidueField A) α`. Set `v : AdjoinRoot M →+* Ω` to `AdjoinRoot.lift u α hev`.

Establish `hva : v.comp (algebraMap A (AdjoinRoot M)) = u`. Use extensionality with `x`. Simplify using `[v, AdjoinRoot.algebraMap_eq]`. Use `⟨AdjoinRoot M, inferInstance, inferInstance, algebraMap A (AdjoinRoot M), v, ?_, maximalIdeal_eq M hM hirr, isAdicComplete M hM hirr, ?_, hva, ⟨AdjoinRoot.root M, by simp [v]⟩⟩` and prove the remaining obligations. Rewrite using `[RingHom.flat_algebraMap_iff]`.

Use `infer_instance`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top v)`. Rewrite using `[← maximalIdeal_eq M hM hirr, Ideal.map_le_iff_le_comap]`. Introduce `x hx`.

Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hva, ← RingHom.mem_ker, hker]`. Conclude with `hx`.
-/
theorem exists_extension : ∀ (A Ω : Type) [CommRing A] [IsRegularLocalRing A] [Field Ω]
    (u : A →+* Ω) (p : Polynomial A) (α : Ω),
    RingHom.ker u = maximalIdeal A → IsAdicComplete (maximalIdeal A) A → p.Monic →
    (p.map u).eval α = 0 → (p.map u).derivative.eval α ≠ 0 →
    ∃ (E : Type) (_ : CommRing E) (_ : IsRegularLocalRing E) (a : A →+* E) (v : E →+* Ω),
      a.Flat ∧ (maximalIdeal A).map a = maximalIdeal E ∧ IsAdicComplete (maximalIdeal E) E ∧
      RingHom.ker v = maximalIdeal E ∧ v.comp a = u ∧ α ∈ v.range := by
  intro A Ω _ _ _ u p α hker hcpl hp hroot _

  let ub : ResidueField A →+* Ω := Ideal.Quotient.lift (maximalIdeal A) u
    (fun x hx => (RingHom.mem_ker).1 (hker ▸ hx))
  have hub : ∀ x, ub (residue A x) = u x := fun x => rfl
  letI : Algebra (ResidueField A) Ω := ub.toAlgebra
  have hpu : p.map u = (p.map (residue A)).map ub := by
    rw [Polynomial.map_map]; congr 1
  have hint : IsIntegral (ResidueField A) α := by
    refine ⟨p.map (residue A), hp.map _, ?_⟩
    rw [← Polynomial.eval_map]; change eval α ((p.map (residue A)).map ub) = 0
    rw [← hpu]; exact hroot
  set m := minpoly (ResidueField A) α
  obtain ⟨q, hq⟩ := Polynomial.map_surjective _ (residue_surjective (R := A)) m
  obtain ⟨M, hMm, -, hM⟩ := lifts_and_natDegree_eq_and_monic ((mem_lifts _).2 ⟨q, hq⟩)
    (minpoly.monic hint)
  have hirr : Irreducible (M.map (residue A)) := hMm ▸ minpoly.irreducible hint
  haveI := isLocalRing M hM hirr
  haveI : Module.Finite A (AdjoinRoot M) := .of_basis (AdjoinRoot.powerBasis' hM).basis
  haveI : Module.Free A (AdjoinRoot M) := .of_basis (AdjoinRoot.powerBasis' hM).basis
  haveI : IsNoetherianRing (AdjoinRoot M) := isNoetherian_of_tower A inferInstance
  haveI := isLocalHom M hM hirr
  haveI : IsRegularLocalRing (AdjoinRoot M) :=
    GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.of_flat_of_map_maximalIdeal (maximalIdeal_eq M hM hirr)
  have hev : M.eval₂ u α = 0 := by
    have h1 : M.eval₂ u α = (M.map (residue A)).eval₂ ub α := by
      rw [Polynomial.eval₂_map]; rfl
    rw [h1, hMm]; exact minpoly.aeval (ResidueField A) α
  let v : AdjoinRoot M →+* Ω := AdjoinRoot.lift u α hev
  have hva : v.comp (algebraMap A (AdjoinRoot M)) = u := by
    ext x; simp [v, AdjoinRoot.algebraMap_eq]
  refine ⟨AdjoinRoot M, inferInstance, inferInstance, algebraMap A (AdjoinRoot M), v, ?_,
    maximalIdeal_eq M hM hirr, isAdicComplete M hM hirr, ?_, hva, ⟨AdjoinRoot.root M, by simp [v]⟩⟩
  · rw [RingHom.flat_algebraMap_iff]; infer_instance
  · apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top v)
    · rw [← maximalIdeal_eq M hM hirr, Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hva, ← RingHom.mem_ker, hker]
      exact hx

end GlobalTheory.MonicRootExtension
