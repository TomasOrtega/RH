import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsE8WeightedBundle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsE8IsSharpBasis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticTorsionSystemIsGeometricBasis
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSharpBasisSharpBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingE8PowerDependsOnFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBasisE8FactorTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ProductTorsionSectionBoundStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.Sep.E8Fibration.Lab

/- English proof (translation)
Introduce `W hW gQ`. Use `⟨E8Fibration.Lab.labMat W hW.2 gQ, ?_⟩` and prove the remaining obligations. Introduce `l hl hlo j hj K _ _ k₀ hk₀ hlK P' hg B _ _ M pr hPP hP hE act hact hacts`. Take `⟨L1, -⟩` from `GlobalTheory.abelianSchemeLaws_all`. Establish `hNK : (((l ^ j) ^ 2 : ℕ) : K) ≠ 0` using `by push_cast; exact pow_ne_zero _ (pow_ne_zero _ hlK)`.

Establish `hNodd : Odd ((l ^ j) ^ 2)` using `(hlo.pow).pow`. Establish `hNpos : 0 < (l ^ j) ^ 2` using `hNodd.pos`. Establish `hN0 : (((l ^ j) ^ 2 : ℕ) : k₀) ≠ 0` using `fun h => hNK (by simpa using congrArg k₀.subtype h)`. Use `haveI : NeZero (((l ^ j) ^ 2 : ℕ) : k₀) := ⟨hN0⟩`. Take `⟨ζ, hζ⟩` from `IsAlgClosed.exists_root (Polynomial.cyclotomic ((l ^ j) ^ 2) k₀) (Polynomial.degree_cyclotomic_pos _ k₀ hNpos).ne'`.

Establish `hp : IsPrimitiveRoot ζ ((l ^ j) ^ 2)` using `(Polynomial.isRoot_cyclotomic_iff).1 hζ`. Set `bT : TBase k₀ ((l ^ j) ^ 2)` to `⟨(hp.isUnit hNpos.ne').unit, hN0.isUnit, fun K' _ β => hp.map_of_injective β.injective⟩`. Set `z : Kˣ` to `Units.map k₀.subtype.toMonoidHom bT.ζ`. Establish `hz : IsPrimitiveRoot z ((l ^ j) ^ 2)` using `IsPrimitiveRoot.coe_units_iff.1 (bT.prim K k₀.subtype)`. Establish `hu : unitS (spMap k₀.subtype) bT.ζ = unitOn z`.

Use `ext`. Simplify using `only [unitS, unitOn, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, z]`. Use `Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom k₀.subtype)` as an intermediate fact. Conclude with `(congrArg (fun f => f.hom (bT.ζ : k₀)) this).symm`. Take `⟨b, hb, hpair⟩` from `GlobalTheory.T.exists_symplecticBasis_e8Factor_torsion W hW gQ _ hNodd K hNK z hz P' hg B pr hP (GlobalTheory.T.weilPairing_e8Power_depends_on_form W hW gQ K P' B M pr hPP hP hE _ hNpos)`.

Use `P'.isAb.comm` as an intermediate fact. Take `⟨htor, hactc⟩` from `GlobalTheory.T.e8_prod_torsion_section_bound W hW gQ P'.A B pr hP ((l ^ j) ^ 2) b hb`. Establish `hpt : ∀ i i', Out.WeilIs P'.A P'.L ((l ^ j) ^ 2 : ℕ) (E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1))) (E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i' 1))) (unitOn z ^ Out.stdSymp (8 * gQ) i i')`. Introduce `i i'`. Establish `h1` using `hpair (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)) (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i' 1)) _ _ (E8Fibration.Lab.ptOf_pr hP b _) (E8Fibration.Lab.ptOf_pr hP b _)`.

Establish `h2` using `E8Fibration.Lab.isSharpBasis_sharpBasis W hW.2 gQ i i'`. Simplify using `only [E8Fibration.e8] at h1`. Rewrite `h1` using `[h2]`. Conclude with `h1` after adjusting the coercions. Use `⟨bT, fun i => E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)), htor, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `K' _ _ x y hy`. Establish `key` using `GlobalTheory.symplectic_system_torsion_basis L1 K P' ((l ^ j) ^ 2) z`. Use `revert key`. Generalize the expression as in `P'.g = g' at hg ⊢`. Substitute `hg` using the available equality.

Introduce `key`. Conclude with `key _ hNK hz htor hpt K' x y hy`. Introduce `i i'`. Rewrite using `[hu]`. Conclude with `hpt i i'`.

Introduce `a i`. Conclude with `hactc act hacts a i`.
-/
theorem exists_symplectic_labels : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ),
  ∃ Mat : Fin 2 → Matrix (Fin (2 * (8 * gQ))) (Fin (2 * (8 * gQ))) ℤ,
  ∀ (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ → (l : K) ≠ 0 →
  ∀ (P' : PolAV (Sp K)), P'.g = 8 * gQ →
  ∀ (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
  E8Fibration.IsPPFib B gQ M → E8Fibration.IsProd pr → E8Fibration.IsE8WeightedBundle W pr P'.L M.L →
  ∀ act : Fin 2 → (P'.A ⟶ P'.A), (∀ i, IsMonHom (act i)) → (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) →
  ∃ (bT : TBase k₀ ((l ^ j) ^ 2)) (pt : Fin (2 * (8 * gQ)) → (Out.baseOver (Sp K) ⟶ P'.A)),
    (∀ i, pt i ^ ((l ^ j) ^ 2) = 1) ∧
    (∀ (K' : Type) [Field K'] [IsAlgClosed K'] (x : Sp K' ⟶ Sp K) (y : Over.mk x ⟶ P'.A), y ^ ((l ^ j) ^ 2) = 1 →
      ∃! c : Ix (8 * gQ) ((l ^ j) ^ 2), Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp K)) ≫ pt i)
        (fun i => (c i).val) = y) ∧
    (∀ i i', Out.WeilIs P'.A P'.L (((l ^ j) ^ 2 : ℕ) : ℤ) (pt i) (pt i')
      (unitS (spMap k₀.subtype) bT.ζ ^ Out.stdSymp (8 * gQ) i i')) ∧
    ∀ (a : Fin 2) i, pt i ≫ act a = Out.linComb pt (fun i' => ((Mat a i' i : ZMod ((l ^ j) ^ 2))).val) := by
  intro W hW gQ
  refine ⟨E8Fibration.Lab.labMat W hW.2 gQ, ?_⟩
  intro l hl hlo j hj K _ _ k₀ hk₀ hlK P' hg B _ _ M pr hPP hP hE act hact hacts
  obtain ⟨L1, -⟩ := GlobalTheory.abelianSchemeLaws_all
  have hNK : (((l ^ j) ^ 2 : ℕ) : K) ≠ 0 := by push_cast; exact pow_ne_zero _ (pow_ne_zero _ hlK)
  have hNodd : Odd ((l ^ j) ^ 2) := (hlo.pow).pow
  have hNpos : 0 < (l ^ j) ^ 2 := hNodd.pos
  have hN0 : (((l ^ j) ^ 2 : ℕ) : k₀) ≠ 0 := fun h => hNK (by simpa using congrArg k₀.subtype h)
  haveI : NeZero (((l ^ j) ^ 2 : ℕ) : k₀) := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic ((l ^ j) ^ 2) k₀)
    (Polynomial.degree_cyclotomic_pos _ k₀ hNpos).ne'
  have hp : IsPrimitiveRoot ζ ((l ^ j) ^ 2) := (Polynomial.isRoot_cyclotomic_iff).1 hζ
  let bT : TBase k₀ ((l ^ j) ^ 2) := ⟨(hp.isUnit hNpos.ne').unit, hN0.isUnit, fun K' _ β => hp.map_of_injective β.injective⟩
  let z : Kˣ := Units.map k₀.subtype.toMonoidHom bT.ζ
  have hz : IsPrimitiveRoot z ((l ^ j) ^ 2) := IsPrimitiveRoot.coe_units_iff.1 (bT.prim K k₀.subtype)
  have hu : unitS (spMap k₀.subtype) bT.ζ = unitOn z := by
    ext
    simp only [unitS, unitOn, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, z]
    have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom k₀.subtype)
    exact (congrArg (fun f => f.hom (bT.ζ : k₀)) this).symm
  obtain ⟨b, hb, hpair⟩ := GlobalTheory.T.exists_symplecticBasis_e8Factor_torsion W hW gQ _ hNodd K hNK z hz P' hg B pr hP
    (GlobalTheory.T.weilPairing_e8Power_depends_on_form W hW gQ K P' B M pr hPP hP hE _ hNpos)
  have := P'.isAb.comm
  obtain ⟨htor, hactc⟩ := GlobalTheory.T.e8_prod_torsion_section_bound W hW gQ P'.A B pr hP ((l ^ j) ^ 2) b hb
  have hpt : ∀ i i', Out.WeilIs P'.A P'.L ((l ^ j) ^ 2 : ℕ)
      (E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)))
      (E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i' 1))) (unitOn z ^ Out.stdSymp (8 * gQ) i i') := by
    intro i i'
    have h1 := hpair (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)) (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i' 1))
      _ _ (E8Fibration.Lab.ptOf_pr hP b _) (E8Fibration.Lab.ptOf_pr hP b _)
    have h2 := E8Fibration.Lab.isSharpBasis_sharpBasis W hW.2 gQ i i'
    simp only [E8Fibration.e8] at h1
    rw [h2] at h1
    exact_mod_cast h1
  refine ⟨bT, fun i => E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)), htor, ?_, ?_, ?_⟩
  · intro K' _ _ x y hy
    have key := GlobalTheory.symplectic_system_torsion_basis L1 K P' ((l ^ j) ^ 2) z
    revert key
    generalize P'.g = g' at hg ⊢
    subst hg
    intro key
    exact key _ hNK hz htor hpt K' x y hy
  · intro i i'
    rw [hu]
    exact hpt i i'
  · intro a i
    exact hactc act hacts a i

end GlobalTheory.Poinc.Sep.E8Fibration.Lab
end
