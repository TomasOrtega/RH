import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IsometryCarriesCharacter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MonotoneTwoBlockIndicator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEqMapDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTameCharactersSeriesIdempotentsTameLabelleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapRangeAdjointLeBlockSum
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.GoodProjHypH

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.factPrime

/- English proof (translation)
Set `P : W →ₗ[ℂ] W` to `∑ g, emb ((Formalism.L2.DIV.idemOf X).coeff g) • τ g`. Establish `hPz : ∀ z, P z = ∑ g, emb ((Formalism.L2.DIV.idemOf X).coeff g) • τ g z` using `fun z => by`. Simplify using `[P, LinearMap.sum_apply]`. Establish `hPx : P x = x` using `(hPz x).trans hx`. Establish `hidem : IsIdempotentElem P`.

Use `LinearMap.ext fun z => ?_` and prove the remaining obligations. Use `show P (P z) = P z`. Rewrite using `[hPz, hPz z]`. Conclude with `GlobalTheory.AdjBlock.idem_idem emb hX τ z`. Establish `htr : LinearMap.trace ℂ W P ≠ 0`.

Introduce `h0`. Establish `h1` using `LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hidem h0`. Conclude with `hx0 (by rw [← hPx, h1, LinearMap.zero_apply])`. Establish `htr' : LinearMap.trace ℂ W P = ∑ χ ∈ X, ∑ g, emb (χ 1 / (Fintype.card G : K) * χ g⁻¹) * τ.character g`. Simplify using `only [P, map_sum, map_smul, smul_eq_mul, Formalism.L2.DIV.coeff_idemOf, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Both sides reduce to the same expression. Rewrite `htr` using `[htr']`. Take `⟨χ, hχ, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero htr`. Use `⟨χ, hχ, ?_⟩` and prove the remaining obligations.

Take `⟨n, ρ, hρi, hρ⟩` from `GlobalTheory.GoodTypeGeneric.isIrrChar_of_isAbsIrrChar emb (hX χ hχ)`. Use `beta_reduce at hρ`. Establish `hpair` using `GlobalTheory.BI.pair_character_eq_finrank ℂ ℂ G (Fin n → ℂ) W ρ τ`. Establish `hfin : Module.finrank ℂ (ρ.IntertwiningMap τ) ≠ 0`. Introduce `h0`.

Rewrite `hpair` using `[h0, Nat.cast_zero]`. Apply `hne` to reduce the goal to its premises. Unfold `GlobalTheory.BI.pair at hpair`. Rewrite `hpair` using `[finsum_eq_sum_of_fintype]`. Establish `hc : (Nat.card G : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`.

Establish `hs : ∑ g, τ.character g * ρ.character g⁻¹ = 0`. Simplify `hpair` using `[hc]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_div₀, map_natCast, hρ g⁻¹]`. Simplify using `only [Algebra.algebraMap_self, RingHom.id_apply]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = 0 := by rw [hs, mul_zero]`. Use `haveI : ρ.IsIrreducible := hρi`.

Use `haveI : τ.IsIrreducible := hτ`. Use `haveI := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hfin)`. Take `⟨f, hf⟩` from `exists_ne (0 : ρ.IntertwiningMap τ)`. Break down `Representation.IsIrreducible.bijective_or_eq_zero f with hb | h0` into its components or cases. Introduce `g`.

Rewrite using `[hρ g, ← Representation.char_iso (Representation.IntertwiningMap.ofBijective f hb)]`. Simplify using the standard rewrite rules. Conclude with `absurd h0 hf`.
-/
theorem exists_char_of_fixed {K G W : Type} [Field K] [CharZero K] [Group G] [Fintype G] (emb : K →+* ℂ)
    (X : Finset (G → K)) (hX : ∀ χ ∈ X, Formalism.L2.DIV.IsAbsIrrChar χ) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (τ : Representation ℂ G W) (hτ : τ.IsIrreducible) (x : W) (hx0 : x ≠ 0)
    (hx : ∑ g, emb ((Formalism.L2.DIV.idemOf X).coeff g) • τ g x = x) : ∃ χ ∈ X, ∀ g, τ.character g = emb (χ g) := by
  classical
  let P : W →ₗ[ℂ] W := ∑ g, emb ((Formalism.L2.DIV.idemOf X).coeff g) • τ g
  have hPz : ∀ z, P z = ∑ g, emb ((Formalism.L2.DIV.idemOf X).coeff g) • τ g z := fun z => by
    simp [P, LinearMap.sum_apply]
  have hPx : P x = x := (hPz x).trans hx
  have hidem : IsIdempotentElem P := by
    refine LinearMap.ext fun z => ?_
    show P (P z) = P z
    rw [hPz, hPz z]
    exact GlobalTheory.AdjBlock.idem_idem emb hX τ z
  have htr : LinearMap.trace ℂ W P ≠ 0 := by
    intro h0
    have h1 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hidem h0
    exact hx0 (by rw [← hPx, h1, LinearMap.zero_apply])
  have htr' : LinearMap.trace ℂ W P =
      ∑ χ ∈ X, ∑ g, emb (χ 1 / (Fintype.card G : K) * χ g⁻¹) * τ.character g := by
    simp only [P, map_sum, map_smul, smul_eq_mul, Formalism.L2.DIV.coeff_idemOf, Finset.sum_mul]
    rw [Finset.sum_comm]
    rfl
  rw [htr'] at htr
  obtain ⟨χ, hχ, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero htr
  refine ⟨χ, hχ, ?_⟩
  obtain ⟨n, ρ, hρi, hρ⟩ := GlobalTheory.GoodTypeGeneric.isIrrChar_of_isAbsIrrChar emb (hX χ hχ)
  beta_reduce at hρ
  have hpair := GlobalTheory.BI.pair_character_eq_finrank ℂ ℂ G (Fin n → ℂ) W ρ τ
  have hfin : Module.finrank ℂ (ρ.IntertwiningMap τ) ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hpair
    apply hne
    unfold GlobalTheory.BI.pair at hpair
    rw [finsum_eq_sum_of_fintype] at hpair
    have hc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    have hs : ∑ g, τ.character g * ρ.character g⁻¹ = 0 := by
      simpa [hc] using hpair
    calc ∑ g, emb (χ 1 / (Fintype.card G : K) * χ g⁻¹) * τ.character g =
        emb (χ 1) / (Fintype.card G : ℂ) * ∑ g, τ.character g * ρ.character g⁻¹ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [map_mul, map_div₀, map_natCast, hρ g⁻¹]
          simp only [Algebra.algebraMap_self, RingHom.id_apply]
          ring
      _ = 0 := by rw [hs, mul_zero]
  haveI : ρ.IsIrreducible := hρi
  haveI : τ.IsIrreducible := hτ
  haveI := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hfin)
  obtain ⟨f, hf⟩ := exists_ne (0 : ρ.IntertwiningMap τ)
  rcases Representation.IsIrreducible.bijective_or_eq_zero f with hb | h0
  · intro g
    rw [hρ g, ← Representation.char_iso (Representation.IntertwiningMap.ofBijective f hb)]
    simp
  · exact absurd h0 hf

open GlobalTheory.BI Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.FiniteGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel GlobalTheory.GoodTypeGeneric in

/- English proof (translation)
Use `haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩`. Set `b₀ : Fin r → ℕ` to `fun i => (s.1 i : ℕ)`. Set `w` to `Tuple.sort b₀`. Set `e` to `(cycEquiv s.1).trans w.symm`. Establish `he : ∀ x y, (b₀ ∘ w) (e x) = (b₀ ∘ w) (e y) ↔ x.1 = y.1`.

Introduce `x y`. Simplify using `only [e, b₀, Function.comp, Equiv.trans_apply, Equiv.apply_symm_apply, apply_cycEquiv, Fin.val_inj, Subtype.ext_iff]`. Take `⟨n, σ, hσ, hch⟩` from `exists_isCuspDatum (F := ZMod p) (Tuple.monotone_sort b₀) e he (fun c => cuspOn (s.2 c)) (fun c => (irr_and_sum_of_isCusp (isCusp_cuspOn hs c)).1) fun c => (irr_and_sum_of_isCusp (isCusp_cuspOn hs c)).2`. Establish `hchar : ∀ x, typeChar s x = (parInd (b₀ ∘ w) σ).character x`. Introduce `x`.

Establish `hm : ∀ z : GL (Fin r) (ZMod p), ((permGL (ZMod p) w * z * (permGL (ZMod p) w)⁻¹ : GL (Fin r) (ZMod p)) : Matrix (Fin r) (Fin r) (ZMod p)).BlockTriangular s.1 ↔ z ∈ blockTri (κ` using `ZMod p) (b₀ ∘ w) := fun z => Iff.trans Iff.rfl (conj_mem_blockTri (b := b₀))`. Rewrite using `[character_coind_eq_ind]`. Unfold `typeChar ind`. Use `congr 1`. Use `congr 2`.

Conclude with `(Nat.card_congr ((MulAut.conj (permGL (ZMod p) w)).toEquiv.subtypeEquiv fun z => (hm z).symm)).symm`. Use `letI := Fintype.ofFinite (GL (Fin r) (ZMod p))`. Rewrite using `[finsum_eq_sum_of_fintype]`. Use `symm`. Use `Fintype.sum_equiv (Equiv.mulRight (permGL (ZMod p) w)⁻¹) _ _ fun y => ?_` and prove the remaining obligations.

Establish `h1 : (Equiv.mulRight (permGL (ZMod p) w)⁻¹ y)⁻¹ * x * Equiv.mulRight (permGL (ZMod p) w)⁻¹ y = permGL (ZMod p) w * (y⁻¹ * x * y) * (permGL (ZMod p) w)⁻¹`. Simplify using `only [Equiv.coe_mulRight]`. Use `group`. Rewrite using `[h1]`. Unfold `ext0`.

Distinguish the cases in `hz : y⁻¹ * x * y ∈ blockTri (κ := ZMod p) (b₀ ∘ w)`. Rewrite using `[dif_pos hz, if_pos ((hm _).2 hz), hch]`. Use `Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations. Unfold `cuspOn`. Use `congr 1`.

Use extensionality with `i j`. Rewrite using `[Matrix.submatrix_apply, blocksHom_apply]`. Simplify using `only [e, Equiv.trans_apply, cycEquiv_apply]`. Rewrite using `[← conj_permGL_apply w, Equiv.apply_symm_apply, Equiv.apply_symm_apply]`. Both sides reduce to the same expression.

Rewrite using `[dif_neg hz, if_neg (mt (hm _).1 hz)]`. Establish `hnf : GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.NoFixed (parInd (b₀ ∘ w) σ) (GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical (ZMod p) r a)`. Assume the negation of the conclusion as `hfix`. Take `⟨J, hJ, hJa⟩` from `GlobalTheory.GoodNoFixed.fixedVectorBlocks (ZMod p) r (b₀ ∘ w) _ σ hσ _ (parInd (b₀ ∘ w) σ) ⟨LinearMap.id, Function.injective_id, fun _ => rfl⟩ a h0 ha hfix`. Use `set Af := Finset.univ.filter fun c : Cyc s.1 => (c.1 : ℕ) ∈ J with hAf`.

Apply `hA Af` to reduce the goal to its premises. Establish `hJim : J = Af.image fun c => (c.1 : ℕ)`. Use extensionality with `j`. Simplify using `only [hAf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion.

Introduce `hj`. Take `⟨i, -, hi⟩` from `Finset.mem_image.1 (hJ hj)`. Conclude with `⟨⟨s.1 (w i), w i, rfl⟩, by rw [← hi] at hj; exact hj, hi⟩`. Introduce and unpack `⟨c, hc, rfl⟩`. Conclude with `hc`.

Rewrite using `[hJa, hJim, Finset.sum_image fun c _ c' _ h => Subtype.ext (Fin.ext h)]`. Use `Finset.sum_congr rfl fun c _ => Fintype.card_congr (w.symm.subtypeEquiv fun i => ?_)` and prove the remaining obligations. Simplify using `only [b₀, Function.comp, Fin.val_inj, Equiv.apply_symm_apply]`. Establish `h1` using `(GlobalTheory.GoodNoFixed.noFixed_iff_sum (parInd (b₀ ∘ w) σ) (MonoidHom.id _)).1 (by rwa [MonoidHom.coe_id, Set.image_id])`. Simplify `h1` using `only [hchar, MonoidHom.id_apply]`.
-/
theorem sum_typeChar_radical {p : ℕ} [Fact p.Prime] {r : ℕ} (s : GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.SSParam p ℂ r)
    (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.IsRegularParam s) {a : ℕ} (h0 : 0 < a) (ha : a < r)
    (hA : ∀ A : Finset (GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.Cyc s.1), ∑ c ∈ A, GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.cycLen s.1 c ≠ a)
    [Fintype (unipRadical (ZMod p) (Formalism.L2.DIV.blk2 (n := r) a))] :
    ∑ u : unipRadical (ZMod p) (Formalism.L2.DIV.blk2 (n := r) a), GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.typeChar s (u : GL (Fin r) (ZMod p)) = 0 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let b₀ : Fin r → ℕ := fun i => (s.1 i : ℕ)
  let w := Tuple.sort b₀
  let e := (cycEquiv s.1).trans w.symm
  have he : ∀ x y, (b₀ ∘ w) (e x) = (b₀ ∘ w) (e y) ↔ x.1 = y.1 := by
    intro x y
    simp only [e, b₀, Function.comp, Equiv.trans_apply, Equiv.apply_symm_apply, apply_cycEquiv, Fin.val_inj,
      Subtype.ext_iff]
  obtain ⟨n, σ, hσ, hch⟩ := exists_isCuspDatum (F := ZMod p) (Tuple.monotone_sort b₀) e he (fun c => cuspOn (s.2 c))
    (fun c => (irr_and_sum_of_isCusp (isCusp_cuspOn hs c)).1) fun c => (irr_and_sum_of_isCusp (isCusp_cuspOn hs c)).2
  have hchar : ∀ x, typeChar s x = (parInd (b₀ ∘ w) σ).character x := by
    intro x
    have hm : ∀ z : GL (Fin r) (ZMod p),
        ((permGL (ZMod p) w * z * (permGL (ZMod p) w)⁻¹ : GL (Fin r) (ZMod p)) :
          Matrix (Fin r) (Fin r) (ZMod p)).BlockTriangular s.1 ↔ z ∈ blockTri (κ := ZMod p) (b₀ ∘ w) := fun z =>
      Iff.trans Iff.rfl (conj_mem_blockTri (b := b₀))
    rw [character_coind_eq_ind]
    unfold typeChar ind
    congr 1
    · congr 2
      exact (Nat.card_congr ((MulAut.conj (permGL (ZMod p) w)).toEquiv.subtypeEquiv fun z => (hm z).symm)).symm
    · letI := Fintype.ofFinite (GL (Fin r) (ZMod p))
      rw [finsum_eq_sum_of_fintype]
      symm
      refine Fintype.sum_equiv (Equiv.mulRight (permGL (ZMod p) w)⁻¹) _ _ fun y => ?_
      have h1 : (Equiv.mulRight (permGL (ZMod p) w)⁻¹ y)⁻¹ * x * Equiv.mulRight (permGL (ZMod p) w)⁻¹ y =
          permGL (ZMod p) w * (y⁻¹ * x * y) * (permGL (ZMod p) w)⁻¹ := by
        simp only [Equiv.coe_mulRight]
        group
      rw [h1]
      unfold ext0
      by_cases hz : y⁻¹ * x * y ∈ blockTri (κ := ZMod p) (b₀ ∘ w)
      · rw [dif_pos hz, if_pos ((hm _).2 hz), hch]
        refine Finset.prod_congr rfl fun c _ => ?_
        unfold cuspOn
        congr 1
        ext i j
        rw [Matrix.submatrix_apply, blocksHom_apply]
        simp only [e, Equiv.trans_apply, cycEquiv_apply]
        rw [← conj_permGL_apply w, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        rfl
      · rw [dif_neg hz, if_neg (mt (hm _).1 hz)]
  have hnf : GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.NoFixed (parInd (b₀ ∘ w) σ) (GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical (ZMod p) r a) := by
    by_contra hfix
    obtain ⟨J, hJ, hJa⟩ := GlobalTheory.GoodNoFixed.fixedVectorBlocks (ZMod p) r (b₀ ∘ w) _ σ hσ _ (parInd (b₀ ∘ w) σ)
      ⟨LinearMap.id, Function.injective_id, fun _ => rfl⟩ a h0 ha hfix
    set Af := Finset.univ.filter fun c : Cyc s.1 => (c.1 : ℕ) ∈ J with hAf
    apply hA Af
    have hJim : J = Af.image fun c => (c.1 : ℕ) := by
      ext j
      simp only [hAf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hj
        obtain ⟨i, -, hi⟩ := Finset.mem_image.1 (hJ hj)
        exact ⟨⟨s.1 (w i), w i, rfl⟩, by rw [← hi] at hj; exact hj, hi⟩
      · rintro ⟨c, hc, rfl⟩
        exact hc
    rw [hJa, hJim, Finset.sum_image fun c _ c' _ h => Subtype.ext (Fin.ext h)]
    refine Finset.sum_congr rfl fun c _ => Fintype.card_congr (w.symm.subtypeEquiv fun i => ?_)
    simp only [b₀, Function.comp, Fin.val_inj, Equiv.apply_symm_apply]
  have h1 := (GlobalTheory.GoodNoFixed.noFixed_iff_sum (parInd (b₀ ∘ w) σ) (MonoidHom.id _)).1
    (by rwa [MonoidHom.coe_id, Set.image_id])
  simpa only [hchar, MonoidHom.id_apply] using h1

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.DimPartsCompare GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.FiniteGL in

/- English proof (translation)
Introduce `hG D G _ _ Pl0 T A Ks _ _ _ R F hR W _ _ _ τ hτ hx a h0 ha`. Take `⟨x, hx0, hx⟩` from `hx`. Take `⟨om, hT⟩` from `GlobalTheory.T.exists_tameCharacters_seriesIdempotentsTameLabelled R F hR`. Establish `hI` using `GlobalTheory.GoodIdemTie.idemTie_of_tameTie hG D om hT`. Take `⟨χ, hχ, hτχ⟩` from `exists_char_of_fixed D.what₂.embLL A.X hR.irr (τ.comp R.eG.toMonoidHom) (GlobalTheory.FinGL.Transport.isIrreducible_comp τ _ R.eG.surjective hτ) x hx0 hx`.

Take `⟨eR, plg, iso, h1, -, h2⟩` from `hR.core.grp.record`. Set `π : LevelCuspCharacters.LevelGroup D.host ≃* G0g D.nd` to `MulEquiv.ofBijective (⟨⟨pull, rfl⟩, fun _ _ => rfl⟩ : LevelCuspCharacters.LevelGroup D.host →* G0g D.nd) pull_bijective`. Set `φ : G ≃* LevelCuspCharacters.LevelGroup D.host` to `eR.trans π.symm`. Establish `hφ : ∀ g, pull (φ g) = eR g` using `fun g => π.apply_symm_apply (eR g)`. Establish `hreg : ∀ s : ∀ v : LevelCuspCharacters.Sq D.host, LevelCuspCharacters.SSParam (D.host.g v.1) ℂ D.R.r, LevelCuspCharacters.IsGoodParam om s → ∀ v, CuspidalProductMultiplicity.IsCuspProdChar (LevelCuspCharacters.typeChar (s v))` using `fun s hs v => GlobalTheory.GoodTypeGeneric.isCuspProdChar_typeChar ((hs v.1).1 v.2)`.

Take `⟨θ, hθ, hχθ⟩` from `GlobalTheory.GoodTypeGeneric.exists_eq_of_idemOf D.what₂.embLL A.X hR.irr (LevelCuspCharacters.goodTypes_finite (H := D.host) om).toFinset (fun θ g => θ (φ g)) (fun θ hθ => by`. Take `⟨s, hs, rfl⟩` from `(Set.Finite.mem_toFinset _).1 hθ`. Use `letI := Fintype.ofFinite (LevelCuspCharacters.Sq D.host)`. Use `GlobalTheory.GoodTypeGeneric.isChar_prod (χ := fun v g => LevelCuspCharacters.typeChar (s v) (φ g v)) fun v => ?_` and prove the remaining obligations. Take `⟨n, ρ, hρ⟩` from `GlobalTheory.GoodTypeGeneric.isChar_of_isCuspProdChar (hreg s hs v)`.

Conclude with `⟨n, ρ.comp ((Pi.evalMonoidHom _ v).comp φ.toMonoidHom), fun g => hρ _⟩) (fun g => by`. Rewrite using `[h1, ← hφ, hI, Nat.card_congr φ.toEquiv]`. Simplify using `only [LevelCuspCharacters.goodIdem, LevelCuspCharacters.centralIdem, MonoidAlgebra.coeff_sum, Finset.sum_apply', map_one, map_inv]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Simplify using `[Finsupp.single_apply]) hχ`.

Take `⟨s, hs, rfl⟩` from `(Set.Finite.mem_toFinset _).1 hθ`. Establish `hchar : ∀ g, τ.character (R.eG g) = LevelCuspCharacters.tupleChar s (φ g)` using `fun g => (hτχ g).trans (hχθ g)`. Establish `htot : ∀ v : LevelCuspCharacters.Sq D.host, ∑ c : LevelCuspCharacters.Cyc (s v).1, LevelCuspCharacters.cycLen (s v).1 c = D.R.r` using `fun v => by`. Use `Fintype.card_congr (GlobalTheory.GoodTypeGeneric.cycEquiv (s v).1)` as an intermediate fact. Simplify `this` using `[Fintype.card_sigma]`.

Choose the witnesses or unpack the hypotheses as in `⟨w, hw⟩ : ∃ w : LevelCuspCharacters.PlOver D.host 0, ∀ A : Finset (LevelCuspCharacters.Cyc (s ⟨0, w⟩).1), ∑ c ∈ A, LevelCuspCharacters.cycLen (s ⟨0, w⟩).1 c ≠ a := by`. Establish `hiv` using `(hs 0).2.2.2.1`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Distinguish the cases in `h2 : 2 * a ≤ D.R.r`.

Conclude with `hiv ⟨a, h0, h2, hne⟩`. Use `hiv ⟨D.R.r - a, by omega, by omega, fun v => ?_⟩` and prove the remaining obligations. Take `⟨A', hA'⟩` from `hne v`. Use `⟨A'ᶜ, ?_⟩` and prove the remaining obligations. Use `Finset.sum_add_sum_compl A' (fun c => LevelCuspCharacters.cycLen (s ⟨0, v⟩).1 c)` as an intermediate fact.

Rewrite `this` using `[htot]`. Use `beta_reduce at hA' ⊢`. Use linear arithmetic over natural numbers and integers. Take `⟨kv, hkv⟩` from `(sqEquiv D).surjective ⟨0, w⟩`. Rewrite `hw` using `[← hkv]`.

Use `⟨plg kv, ?_⟩` and prove the remaining obligations. Use `letI : Field (kP (plg kv).1) := Ideal.Quotient.field _`. Use `haveI : Finite (kP (plg kv).1) := CuspidalProductMultiplicity.finite_kP _`. Use `letI := Fintype.ofFinite (unipRadical (kP (plg kv).1) (blk2 (n := D.R.r) a))`. Set `ι : GL (Fin D.R.r) (kP (plg kv).1) →* G0 R.Pg D.R.r` to `MonoidHom.mulSingle (fun PP : ↥R.Pg => GL (Fin D.R.r) (kP PP.1)) (plg kv)`.

Establish `hset : {g : G0 R.Pg D.R.r | (∀ PP' : R.Pg, PP' ≠ plg kv → g PP' = 1) ∧ g (plg kv) ∈ GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical (kP (plg kv).1) D.R.r a} = ι '' GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical _ D.R.r a`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hg1, hg2⟩`. Use `⟨g (plg kv), hg2, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `PP'`. Distinguish the cases in `h : PP' = plg kv`. Substitute `h` using the available equality. Conclude with `Pi.mulSingle_eq_same (M := fun PP : ↥R.Pg => GL (Fin D.R.r) (kP PP.1)) _ _`. Rewrite using `[hg1 PP' h]`.

Conclude with `Pi.mulSingle_eq_of_ne (M := fun PP : ↥R.Pg => GL (Fin D.R.r) (kP PP.1)) h _`. Introduce and unpack `⟨u, hu, rfl⟩`. Use `⟨fun PP' h => Pi.mulSingle_eq_of_ne (M := fun PP : ↥R.Pg => GL (Fin D.R.r) (kP PP.1)) h _, ?_⟩` and prove the remaining obligations. Rewrite using `[show ι u (plg kv) = u from Pi.mulSingle_eq_same (M := fun PP : ↥R.Pg => GL (Fin D.R.r) (kP PP.1)) _ _]`. Conclude with `hu`.

Rewrite using `[hset, GlobalTheory.GoodNoFixed.noFixed_iff_sum τ ι]`. Establish `hbc : ∀ {k k' : Type} [CommRing k] [CommRing k'] (e : k ≃+* k') (y : GL (Fin D.R.r) k), Formalism.UG.bc (e.symm : k' →+* k) (Formalism.UG.bc (e : k →+* k') y) = y`. Introduce `k k' _ _ e y`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`.

Simplify using `[Formalism.UG.bc]`. Establish `hval : ∀ u : GL (Fin D.R.r) (kP (plg kv).1), τ.character (ι u) = LevelCuspCharacters.typeChar (s (sqEquiv D kv)) (Formalism.UG.bc ((iso kv).symm : kP (plg kv).1 →+* ZMod (D.host.g kv.1)) u) * ∏ PP ∈ Finset.univ.erase (plg kv), LevelCuspCharacters.typeChar (s (sqEquiv D (plg.symm …`. Introduce `u`. Take `⟨g', hg'⟩` from `R.eG.surjective (ι u)`. Establish `key : ∀ kv', φ g' (sqEquiv D kv') = Formalism.UG.bc ((iso kv').symm : kP (plg kv').1 →+* ZMod (D.host.g kv'.1)) (ι u (plg kv'))`.

Introduce `kv'`. Rewrite using `[← hg', h2 g' kv', hbc]`. Conclude with `congrFun (hφ g') kv'`. Rewrite using `[← hg', hchar, LevelCuspCharacters.tupleChar]`. Use `letI := Fintype.ofFinite (LevelCuspCharacters.Sq D.host)`.

Rewrite using `[← Fintype.prod_equiv (plg.symm.trans (sqEquiv D)) (fun PP => LevelCuspCharacters.typeChar (s (sqEquiv D (plg.symm PP))) (φ g' (sqEquiv D (plg.symm PP)))) _ (fun _ => rfl), ← Finset.mul_prod_erase _ _ (Finset.mem_univ (plg kv))]`. Use `congrArg₂ (· * ·) ?_ (Finset.prod_congr rfl fun PP hPP => ?_)` and prove the remaining obligations. Rewrite using `[Equiv.symm_apply_apply, key, show ι u (plg kv) = u from Pi.mulSingle_eq_same (M := fun PP : ↥R.Pg => GL (Fin D.R.r) (kP PP.1)) _ _]`. Rewrite using `[key (plg.symm PP), show ι u (plg (plg.symm PP)) = 1 from Pi.mulSingle_eq_of_ne (M := fun PP : ↥R.Pg => GL (Fin D.R.r) (kP PP.1)) (by rw [Equiv.apply_symm_apply]; exact Finset.ne_of_mem_erase hPP) _, map_one]`. Both sides reduce to the same expression.

Simplify using `only [hval]`. Rewrite using `[← Finset.sum_mul]`. Use `mul_eq_zero_of_left ?_ _` and prove the remaining obligations. Use `haveI : NeZero (D.host.g kv.1) := ⟨(Fact.out : (D.host.g kv.1).Prime).ne_zero⟩`. Use `letI := Fintype.ofFinite (unipRadical (ZMod (D.host.g kv.1)) (blk2 (n := D.R.r) a))`.

Set `E : unipRadical (ZMod (D.host.g kv.1)) (blk2 (n` to `D.R.r) a) ≃ unipRadical (kP (plg kv).1) (blk2 (n := D.R.r) a) := { toFun := fun u => ⟨Formalism.UG.bc ((iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1)) u, GlobalTheory.GoodNoFixed.mem_radical_iff.1 (GlobalTheory.GoodNoFixed.map_mem_radical _ (GlobalTheory.GoodNoFixed.mem_radica …`. Establish `hreg0 : LevelCuspCharacters.IsRegularParam (s (sqEquiv D kv))` using `(hs (sqEquiv D kv).1).1 (sqEquiv D kv).2`. Establish `hB` using `sum_typeChar_radical (p := D.host.g kv.1) (r := D.R.r) (s (sqEquiv D kv)) hreg0 h0 ha hw`. Establish `hS : ∑ u : unipRadical (kP (plg kv).1) (blk2 (n` using `D.R.r) a), LevelCuspCharacters.typeChar (s (sqEquiv D kv)) (Formalism.UG.bc ((iso kv).symm : kP (plg kv).1 →+* ZMod (D.host.g kv.1)) (u : GL (Fin D.R.r) (kP (plg kv).1))) = ∑ u : unipRadical (ZMod (D.host.g kv.1)) (blk2 (n := D.R.r) a), LevelCuspCharacters.typeChar (s (sqEquiv D …`. Use `(Fintype.sum_equiv E _ _ fun u => ?_).symm` and prove the remaining obligations.

Conclude with `congrArg _ (hbc (iso kv) (u : GL (Fin D.R.r) (ZMod (D.host.g kv.1)))).symm`. Conclude with `hS.trans hB`.
-/
theorem hypH_of_goodProj : GlobalTheory.Published.GreenCuspidal → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), Given R F → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (τ : Representation ℂ (G0 R.Pg D.R.r) W), τ.IsIrreducible →
    (∃ x : W, x ≠ 0 ∧ ∑ g, RealDat.eC (A := A) D.what₂.embLL g • τ (R.eG g) x = x) →
    ∀ a : ℕ, 0 < a → a < D.R.r → ∃ PP : R.Pg, GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.NoFixed τ
      {g | (∀ PP' : R.Pg, PP' ≠ PP → g PP' = 1) ∧ g PP ∈ GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical (kP PP.1) D.R.r a} := by
  intro hG D G _ _ Pl0 T A Ks _ _ _ R F hR W _ _ _ τ hτ hx a h0 ha
  classical
  obtain ⟨x, hx0, hx⟩ := hx
  obtain ⟨om, hT⟩ := GlobalTheory.T.exists_tameCharacters_seriesIdempotentsTameLabelled R F hR
  have hI := GlobalTheory.GoodIdemTie.idemTie_of_tameTie hG D om hT
  obtain ⟨χ, hχ, hτχ⟩ := exists_char_of_fixed D.what₂.embLL A.X hR.irr (τ.comp R.eG.toMonoidHom)
    (GlobalTheory.FinGL.Transport.isIrreducible_comp τ _ R.eG.surjective hτ) x hx0 hx
  obtain ⟨eR, plg, iso, h1, -, h2⟩ := hR.core.grp.record
  let π : LevelCuspCharacters.LevelGroup D.host ≃* G0g D.nd :=
    MulEquiv.ofBijective (⟨⟨pull, rfl⟩, fun _ _ => rfl⟩ : LevelCuspCharacters.LevelGroup D.host →* G0g D.nd) pull_bijective
  let φ : G ≃* LevelCuspCharacters.LevelGroup D.host := eR.trans π.symm
  have hφ : ∀ g, pull (φ g) = eR g := fun g => π.apply_symm_apply (eR g)
  have hreg : ∀ s : ∀ v : LevelCuspCharacters.Sq D.host, LevelCuspCharacters.SSParam (D.host.g v.1) ℂ D.R.r, LevelCuspCharacters.IsGoodParam om s →
      ∀ v, CuspidalProductMultiplicity.IsCuspProdChar (LevelCuspCharacters.typeChar (s v)) := fun s hs v =>
    GlobalTheory.GoodTypeGeneric.isCuspProdChar_typeChar ((hs v.1).1 v.2)
  obtain ⟨θ, hθ, hχθ⟩ := GlobalTheory.GoodTypeGeneric.exists_eq_of_idemOf D.what₂.embLL A.X hR.irr
    (LevelCuspCharacters.goodTypes_finite (H := D.host) om).toFinset (fun θ g => θ (φ g)) (fun θ hθ => by
      obtain ⟨s, hs, rfl⟩ := (Set.Finite.mem_toFinset _).1 hθ
      letI := Fintype.ofFinite (LevelCuspCharacters.Sq D.host)
      refine GlobalTheory.GoodTypeGeneric.isChar_prod (χ := fun v g => LevelCuspCharacters.typeChar (s v) (φ g v)) fun v => ?_
      obtain ⟨n, ρ, hρ⟩ := GlobalTheory.GoodTypeGeneric.isChar_of_isCuspProdChar (hreg s hs v)
      exact ⟨n, ρ.comp ((Pi.evalMonoidHom _ v).comp φ.toMonoidHom), fun g => hρ _⟩) (fun g => by
      rw [h1, ← hφ, hI, Nat.card_congr φ.toEquiv]
      simp only [LevelCuspCharacters.goodIdem, LevelCuspCharacters.centralIdem, MonoidAlgebra.coeff_sum, Finset.sum_apply', map_one, map_inv]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp [Finsupp.single_apply]) hχ
  obtain ⟨s, hs, rfl⟩ := (Set.Finite.mem_toFinset _).1 hθ
  have hchar : ∀ g, τ.character (R.eG g) = LevelCuspCharacters.tupleChar s (φ g) := fun g => (hτχ g).trans (hχθ g)

  have htot : ∀ v : LevelCuspCharacters.Sq D.host, ∑ c : LevelCuspCharacters.Cyc (s v).1, LevelCuspCharacters.cycLen (s v).1 c = D.R.r := fun v => by
    have := Fintype.card_congr (GlobalTheory.GoodTypeGeneric.cycEquiv (s v).1)
    simpa [Fintype.card_sigma] using this
  obtain ⟨w, hw⟩ : ∃ w : LevelCuspCharacters.PlOver D.host 0, ∀ A : Finset (LevelCuspCharacters.Cyc (s ⟨0, w⟩).1),
      ∑ c ∈ A, LevelCuspCharacters.cycLen (s ⟨0, w⟩).1 c ≠ a := by
    have hiv := (hs 0).2.2.2.1
    by_contra hne
    push_neg at hne
    by_cases h2 : 2 * a ≤ D.R.r
    · exact hiv ⟨a, h0, h2, hne⟩
    · refine hiv ⟨D.R.r - a, by omega, by omega, fun v => ?_⟩
      obtain ⟨A', hA'⟩ := hne v
      refine ⟨A'ᶜ, ?_⟩
      have := Finset.sum_add_sum_compl A' (fun c => LevelCuspCharacters.cycLen (s ⟨0, v⟩).1 c)
      rw [htot] at this
      beta_reduce at hA' ⊢
      omega
  obtain ⟨kv, hkv⟩ := (sqEquiv D).surjective ⟨0, w⟩
  rw [← hkv] at hw
  refine ⟨plg kv, ?_⟩
  letI : Field (kP (plg kv).1) := Ideal.Quotient.field _
  haveI : Finite (kP (plg kv).1) := CuspidalProductMultiplicity.finite_kP _
  letI := Fintype.ofFinite (unipRadical (kP (plg kv).1) (blk2 (n := D.R.r) a))
  let ι : GL (Fin D.R.r) (kP (plg kv).1) →* G0 R.Pg D.R.r :=
    MonoidHom.mulSingle (fun PP : ↥R.Pg => GL (Fin D.R.r) (kP PP.1)) (plg kv)
  have hset : {g : G0 R.Pg D.R.r | (∀ PP' : R.Pg, PP' ≠ plg kv → g PP' = 1) ∧
      g (plg kv) ∈ GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical (kP (plg kv).1) D.R.r a} = ι '' GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical _ D.R.r a := by
    ext g
    constructor
    · rintro ⟨hg1, hg2⟩
      refine ⟨g (plg kv), hg2, ?_⟩
      funext PP'
      by_cases h : PP' = plg kv
      · subst h
        exact Pi.mulSingle_eq_same (M := fun PP : ↥R.Pg => GL (Fin D.R.r) (kP PP.1)) _ _
      · rw [hg1 PP' h]
        exact Pi.mulSingle_eq_of_ne (M := fun PP : ↥R.Pg => GL (Fin D.R.r) (kP PP.1)) h _
    · rintro ⟨u, hu, rfl⟩
      refine ⟨fun PP' h => Pi.mulSingle_eq_of_ne (M := fun PP : ↥R.Pg => GL (Fin D.R.r) (kP PP.1)) h _, ?_⟩
      rw [show ι u (plg kv) = u from Pi.mulSingle_eq_same (M := fun PP : ↥R.Pg => GL (Fin D.R.r) (kP PP.1)) _ _]
      exact hu
  rw [hset, GlobalTheory.GoodNoFixed.noFixed_iff_sum τ ι]

  have hbc : ∀ {k k' : Type} [CommRing k] [CommRing k'] (e : k ≃+* k') (y : GL (Fin D.R.r) k),
      Formalism.UG.bc (e.symm : k' →+* k) (Formalism.UG.bc (e : k →+* k') y) = y := by
    intro k k' _ _ e y
    apply Units.ext
    ext i j
    simp [Formalism.UG.bc]
  have hval : ∀ u : GL (Fin D.R.r) (kP (plg kv).1), τ.character (ι u) =
      LevelCuspCharacters.typeChar (s (sqEquiv D kv)) (Formalism.UG.bc ((iso kv).symm : kP (plg kv).1 →+* ZMod (D.host.g kv.1)) u) *
        ∏ PP ∈ Finset.univ.erase (plg kv), LevelCuspCharacters.typeChar (s (sqEquiv D (plg.symm PP))) 1 := by
    intro u
    obtain ⟨g', hg'⟩ := R.eG.surjective (ι u)
    have key : ∀ kv', φ g' (sqEquiv D kv') =
        Formalism.UG.bc ((iso kv').symm : kP (plg kv').1 →+* ZMod (D.host.g kv'.1)) (ι u (plg kv')) := by
      intro kv'
      rw [← hg', h2 g' kv', hbc]
      exact congrFun (hφ g') kv'
    rw [← hg', hchar, LevelCuspCharacters.tupleChar]
    letI := Fintype.ofFinite (LevelCuspCharacters.Sq D.host)
    rw [← Fintype.prod_equiv (plg.symm.trans (sqEquiv D))
      (fun PP => LevelCuspCharacters.typeChar (s (sqEquiv D (plg.symm PP))) (φ g' (sqEquiv D (plg.symm PP)))) _ (fun _ => rfl),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ (plg kv))]
    refine congrArg₂ (· * ·) ?_ (Finset.prod_congr rfl fun PP hPP => ?_)
    · rw [Equiv.symm_apply_apply, key, show ι u (plg kv) = u from Pi.mulSingle_eq_same (M := fun PP : ↥R.Pg => GL (Fin D.R.r) (kP PP.1)) _ _]
    · rw [key (plg.symm PP), show ι u (plg (plg.symm PP)) = 1 from
        Pi.mulSingle_eq_of_ne (M := fun PP : ↥R.Pg => GL (Fin D.R.r) (kP PP.1))
          (by rw [Equiv.apply_symm_apply]; exact Finset.ne_of_mem_erase hPP) _, map_one]
      rfl
  simp only [hval]
  rw [← Finset.sum_mul]
  refine mul_eq_zero_of_left ?_ _
  haveI : NeZero (D.host.g kv.1) := ⟨(Fact.out : (D.host.g kv.1).Prime).ne_zero⟩
  letI := Fintype.ofFinite (unipRadical (ZMod (D.host.g kv.1)) (blk2 (n := D.R.r) a))
  let E : unipRadical (ZMod (D.host.g kv.1)) (blk2 (n := D.R.r) a) ≃ unipRadical (kP (plg kv).1) (blk2 (n := D.R.r) a) :=
    { toFun := fun u => ⟨Formalism.UG.bc ((iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1)) u,
        GlobalTheory.GoodNoFixed.mem_radical_iff.1 (GlobalTheory.GoodNoFixed.map_mem_radical _ (GlobalTheory.GoodNoFixed.mem_radical_iff.2 u.2))⟩
      invFun := fun u => ⟨Formalism.UG.bc (((iso kv).symm : kP (plg kv).1 →+* ZMod (D.host.g kv.1))) u,
        GlobalTheory.GoodNoFixed.mem_radical_iff.1 (GlobalTheory.GoodNoFixed.map_mem_radical _ (GlobalTheory.GoodNoFixed.mem_radical_iff.2 u.2))⟩
      left_inv := fun u => Subtype.ext (hbc (iso kv) u)
      right_inv := fun u => Subtype.ext (by simpa using hbc (iso kv).symm u) }
  have hreg0 : LevelCuspCharacters.IsRegularParam (s (sqEquiv D kv)) := (hs (sqEquiv D kv).1).1 (sqEquiv D kv).2
  have hB := sum_typeChar_radical (p := D.host.g kv.1) (r := D.R.r) (s (sqEquiv D kv)) hreg0 h0 ha hw
  have hS : ∑ u : unipRadical (kP (plg kv).1) (blk2 (n := D.R.r) a), LevelCuspCharacters.typeChar (s (sqEquiv D kv))
      (Formalism.UG.bc ((iso kv).symm : kP (plg kv).1 →+* ZMod (D.host.g kv.1)) (u : GL (Fin D.R.r) (kP (plg kv).1))) =
      ∑ u : unipRadical (ZMod (D.host.g kv.1)) (blk2 (n := D.R.r) a),
        LevelCuspCharacters.typeChar (s (sqEquiv D kv)) (u : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
    refine (Fintype.sum_equiv E _ _ fun u => ?_).symm
    exact congrArg _ (hbc (iso kv) (u : GL (Fin D.R.r) (ZMod (D.host.g kv.1)))).symm
  exact hS.trans hB

end GlobalTheory.GoodProjHypH
