import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAveragingProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc
open scoped Matrix

section General

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ G V} {ρ : Representation ℂ G W} {K : Subgroup G} {h : G → ℂ} {x : V} {y : W}

/- English proof (translation)
Establish `hf` using `GlobalTheory.LGrp.mem_fixed.1 hx`. Establish `hg` using `GlobalTheory.LGrp.mem_fixed.1 hy`. Establish `bi : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β (σ (a * t * b) x) y = β (σ t x) y` using `fun a ha b hb t => by`. Take `⟨a, rfl⟩` from `θ.surjective a`. Rewrite using `[map_mul σ, map_mul σ, Module.End.mul_apply, Module.End.mul_apply, hf b hb]`.

Conclude with `(congrArg (β _) (hg a ((hθ a).2 ha)).symm).trans (hi a _ _)`. Establish `bi' : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β x (ρ (a * t * b) y) = β x (ρ t y)` using `fun a ha b hb t => by`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hg b hb]`. Conclude with `(congrArg (fun u => β u _) (hf _ ((hθ a).1 ha)).symm).trans (hi a _ _)`. Establish `inv : ∀ t, β (σ (θ t⁻¹) x) y = β x (ρ t y)` using `fun t => by`.

Rewrite using `[← hi t⁻¹ x (ρ t y)]`. Simplify using the standard rewrite rules. Establish `e1` using `(β.flip y).toAddMonoidHom.map_finsum (finite_heckeVec hK hh σ x)`. Establish `e2` using `(β x).toAddMonoidHom.map_finsum (finite_heckeVec hK hh ρ y)`. Use `e1.trans (Eq.trans (finsum_congr fun c => ?_) e2.symm)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `β (h c.out • σ c.out x) y = β x (h c.out • ρ c.out y)`. Rewrite using `[map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]`. Distinguish the cases in `h0 : h c.out = 0`. Simplify using `[h0]`. Take `⟨a, ha, b, hb, t, htt, e⟩` from `ht _ h0`.

Use `congr 1`. Rewrite using `[e, bi _ ha _ hb, bi' _ ha _ hb, ← inv, htt]`.
-/
private theorem pair_heckeVec (hK : IsCommensurated K) (hh : h ∈ Hecke ℂ K) (hx : x ∈ fixed σ K)
    (hy : y ∈ fixed ρ K) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (θ : G ≃* G) (hθ : ∀ k, k ∈ K ↔ θ k ∈ K)
    (hi : ∀ g v w, β (σ (θ g) v) (ρ g w) = β v w)
    (ht : ∀ g, h g ≠ 0 → ∃ a ∈ K, ∃ b ∈ K, ∃ t, θ t⁻¹ = t ∧ g = a * t * b) :
    β (heckeVec σ K h x) y = β x (heckeVec ρ K h y) := by
  have hf := GlobalTheory.LGrp.mem_fixed.1 hx
  have hg := GlobalTheory.LGrp.mem_fixed.1 hy
  have bi : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β (σ (a * t * b) x) y = β (σ t x) y := fun a ha b hb t => by
    obtain ⟨a, rfl⟩ := θ.surjective a
    rw [map_mul σ, map_mul σ, Module.End.mul_apply, Module.End.mul_apply, hf b hb]
    exact (congrArg (β _) (hg a ((hθ a).2 ha)).symm).trans (hi a _ _)
  have bi' : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β x (ρ (a * t * b) y) = β x (ρ t y) := fun a ha b hb t => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hg b hb]
    exact (congrArg (fun u => β u _) (hf _ ((hθ a).1 ha)).symm).trans (hi a _ _)
  have inv : ∀ t, β (σ (θ t⁻¹) x) y = β x (ρ t y) := fun t => by
    rw [← hi t⁻¹ x (ρ t y)]; simp
  have e1 := (β.flip y).toAddMonoidHom.map_finsum (finite_heckeVec hK hh σ x)
  have e2 := (β x).toAddMonoidHom.map_finsum (finite_heckeVec hK hh ρ y)
  refine e1.trans (Eq.trans (finsum_congr fun c => ?_) e2.symm)
  change β (h c.out • σ c.out x) y = β x (h c.out • ρ c.out y)
  rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  by_cases h0 : h c.out = 0
  · simp [h0]
  obtain ⟨a, ha, b, hb, t, htt, e⟩ := ht _ h0
  congr 1
  rw [e, bi _ ha _ hb, bi' _ ha _ hb, ← inv, htt]

/- English proof (translation)
Use `haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK`. Establish `hfi : (GlobalTheory.OrbitAvg.stab ρ K y).FiniteIndex`. Establish `ho : IsOpen (GlobalTheory.OrbitAvg.stab ρ K y : Set K)` using `(hρ y).preimage continuous_subtype_val`. Use `haveI := (GlobalTheory.OrbitAvg.stab ρ K y).quotient_finite_of_isOpen ho`. Conclude with `Subgroup.finiteIndex_of_finite_quotient`.

Use `⟨GlobalTheory.OrbitAvg.avg ρ K y, GlobalTheory.LGrp.mem_fixed.2 fun u hu => GlobalTheory.OrbitAvg.avg_invariant ρ K hfi ⟨u, hu⟩, ?_⟩` and prove the remaining obligations. Use `haveI := Fintype.ofFinite (K ⧸ GlobalTheory.OrbitAvg.stab ρ K y)`. Establish `hc : ((GlobalTheory.OrbitAvg.stab ρ K y).index : ℂ) ≠ 0` using `by exact_mod_cast hfi.index_ne_zero`. Establish `h1 : ∀ q : K ⧸ GlobalTheory.OrbitAvg.stab ρ K y, l (ρ (q.out : K) y) = l y` using `fun q => hl _ q.out.2 y`. Simplify using `only [GlobalTheory.OrbitAvg.avg, GlobalTheory.OrbitAvg.avgH, GlobalTheory.OrbitAvg.cv, finsum_eq_sum_of_fintype, map_smul, map_sum]`.

Rewrite using `[Finset.sum_congr rfl fun q _ => h1 q, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Subgroup.index, nsmul_eq_mul, smul_eq_mul, inv_mul_cancel_left₀ hc]`.
-/
private theorem exists_fixed_pair [TopologicalSpace G] [IsTopologicalGroup G] (hρ : IsSmooth ρ)
    (hK : IsCompact (K : Set G)) (l : W →ₗ[ℂ] ℂ) (hl : ∀ k ∈ K, ∀ v, l (ρ k v) = l v) (y : W) :
    ∃ y' ∈ fixed ρ K, l y' = l y := by
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hfi : (GlobalTheory.OrbitAvg.stab ρ K y).FiniteIndex := by
    have ho : IsOpen (GlobalTheory.OrbitAvg.stab ρ K y : Set K) := (hρ y).preimage continuous_subtype_val
    haveI := (GlobalTheory.OrbitAvg.stab ρ K y).quotient_finite_of_isOpen ho
    exact Subgroup.finiteIndex_of_finite_quotient
  refine ⟨GlobalTheory.OrbitAvg.avg ρ K y,
    GlobalTheory.LGrp.mem_fixed.2 fun u hu => GlobalTheory.OrbitAvg.avg_invariant ρ K hfi ⟨u, hu⟩, ?_⟩
  haveI := Fintype.ofFinite (K ⧸ GlobalTheory.OrbitAvg.stab ρ K y)
  have hc : ((GlobalTheory.OrbitAvg.stab ρ K y).index : ℂ) ≠ 0 := by exact_mod_cast hfi.index_ne_zero
  have h1 : ∀ q : K ⧸ GlobalTheory.OrbitAvg.stab ρ K y, l (ρ (q.out : K) y) = l y := fun q => hl _ q.out.2 y
  simp only [GlobalTheory.OrbitAvg.avg, GlobalTheory.OrbitAvg.avgH, GlobalTheory.OrbitAvg.cv, finsum_eq_sum_of_fintype, map_smul, map_sum]
  rw [Finset.sum_congr rfl fun q _ => h1 q, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Subgroup.index, nsmul_eq_mul, smul_eq_mul, inv_mul_cancel_left₀ hc]

end General

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.ConjPlace in
/- English proof (translation)
Establish `hKc : IsCompact (KGL w n : Set (GL (Fin n) (w.adicCompletion E)))` using `GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint _ (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers E w)`. Choose the witnesses or unpack the hypotheses as in `⟨y₀, hy₀⟩ : ∃ y, β x y ≠ 0 := by`. Assume the negation of the conclusion as `hn`. Conclude with `hx.1 (hβ x fun y => by_contra fun h => hn ⟨y, h⟩)`. Set `c` to `RingEquiv.refl (w.adicCompletion E)`.

Establish `hc : ∀ a, Valued.v (c a) = Valued.v a` using `fun _ => rfl`. Establish `hK` using `mem_iff_invT (n := n) c (map_mem_Ov_iff c hc)`. Take `⟨y, hyK, hy⟩` from `exists_fixed_pair hρ hKc (β x) (fun k hk v => by`. Use `hi k x v` as an intermediate fact. Rewrite using `[GlobalTheory.LGrp.mem_fixed.1 hx.2.1 _ ((hK k).1 hk)] at this) y₀` and apply the resulting hypothesis.

Establish `hne : β x y ≠ 0` using `hy ▸ hy₀`. Establish `hy'` using `hC.2 y hyK fun h0 => hne (by rw [h0, map_zero])`. Take `⟨p, hp⟩` from `exists_isUnifV w`. Take `⟨ϖ, rfl⟩ : ∃ ϖ : (w.adicCompletion E)ˣ, ϖ = p` from `⟨Units.mk0 p fun e => by simp [IsUnifV, e] at hp, rfl⟩`. Use `eq_of_satEig_eq (qV_ne_zero w) hx.2.2.1 hy'.2.2.1 fun j hj => ?_` and prove the remaining obligations.

Establish `key` using `pair_heckeVec (Final.GLintComm E w n) (Tj_mem_hecke hp j) hx.2.1 hyK β (GlobalTheory.LFun.ConjPlace.invT c n) hK hi (fun g hg => by`. Rewrite `hg` using `[Tj_apply]`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha, b, hb, e⟩ : ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w), g = a * dGL n ϖ j * b := by`. Assume the negation of the conclusion as `hn`. Conclude with `hg (if_neg hn)`.

Conclude with `⟨a, ha, b, hb, _, invT_dGL c ϖ j, e⟩)`. Rewrite `key` using `[hx.2.2.2 _ hp j hj, hy'.2.2.2 _ hp j hj, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]`. Conclude with `mul_right_cancel₀ hne key`.
-/
private theorem sat_eq_of_pair {E : Type} [Field E] [NumberField E] {n : ℕ} {w : HeightOneSpectrum (𝓞 E)} {V W : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    (hρ : IsSmooth ρ) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hβ : ∀ x, (∀ y, β x y = 0) → x = 0)
    (hi : ∀ g x y, β (σ (GlobalTheory.LFun.ConjPlace.invT (RingEquiv.refl _) n g) x) (ρ g y) = β x y)
    {x : V} {B C : Multiset ℂˣ} (hx : IsSatVecGL w σ x B) (hC : HasSatGL w ρ C) : B = C := by
  classical
  have hKc : IsCompact (KGL w n : Set (GL (Fin n) (w.adicCompletion E))) :=
    GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint _ (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers E w)
  obtain ⟨y₀, hy₀⟩ : ∃ y, β x y ≠ 0 := by
    by_contra hn
    exact hx.1 (hβ x fun y => by_contra fun h => hn ⟨y, h⟩)
  let c := RingEquiv.refl (w.adicCompletion E)
  have hc : ∀ a, Valued.v (c a) = Valued.v a := fun _ => rfl
  have hK := mem_iff_invT (n := n) c (map_mem_Ov_iff c hc)
  obtain ⟨y, hyK, hy⟩ := exists_fixed_pair hρ hKc (β x) (fun k hk v => by
    have := hi k x v
    rwa [GlobalTheory.LGrp.mem_fixed.1 hx.2.1 _ ((hK k).1 hk)] at this) y₀
  have hne : β x y ≠ 0 := hy ▸ hy₀
  have hy' := hC.2 y hyK fun h0 => hne (by rw [h0, map_zero])
  obtain ⟨p, hp⟩ := exists_isUnifV w
  obtain ⟨ϖ, rfl⟩ : ∃ ϖ : (w.adicCompletion E)ˣ, ϖ = p :=
    ⟨Units.mk0 p fun e => by simp [IsUnifV, e] at hp, rfl⟩
  refine eq_of_satEig_eq (qV_ne_zero w) hx.2.2.1 hy'.2.2.1 fun j hj => ?_
  have key := pair_heckeVec (Final.GLintComm E w n) (Tj_mem_hecke hp j) hx.2.1 hyK β
    (GlobalTheory.LFun.ConjPlace.invT c n) hK hi
    (fun g hg => by
      rw [Tj_apply] at hg
      obtain ⟨a, ha, b, hb, e⟩ : ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
          g = a * dGL n ϖ j * b := by
        by_contra hn
        exact hg (if_neg hn)
      exact ⟨a, ha, b, hb, _, invT_dGL c ϖ j, e⟩)
  rw [hx.2.2.2 _ hp j hj, hy'.2.2.2 _ hp j hj, map_smul, map_smul, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul] at key
  exact mul_right_cancel₀ hne key

open Neutral.B1 ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published

/- English proof (translation)
Establish `key : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) (Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g)) = Matrix.GeneralLinearGroup.map (conjLoc _ v) (Matrix.GeneralLinearGroup.map (pLoc E (cPl v)) (locGL E a (cPl w) g))` using `fun v => rfl`. Establish `key2 : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) (Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g)) = Matrix.GeneralLinearGroup.map (pLoc E v) (locGL E a w (Matrix.GeneralLinearGroup.map (conjLoc _ w) g))` using `fun v => by`. Rewrite using `[key]`. Distinguish the cases in `h : v = w`. Substitute `h` using the available equality.

Rewrite using `[pLoc_locGL, pLoc_locGL]`. Rewrite using `[pLoc_locGL_of_ne h, pLoc_locGL_of_ne (fun e => h (conjSrc_injective _ e)), map_one]`. Use `Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_)` and prove the remaining obligations. Conclude with `congrArg (fun u : GL (Fin a) (v.adicCompletion E) => u.val i j) (key2 v)`.
-/
private theorem conj_locGL {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (g : GL (Fin a) ((cPl w).adicCompletion E)) :
    Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g) =
      locGL E a w (Matrix.GeneralLinearGroup.map (conjLoc _ w) g) := by
  have key : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v)
      (Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g)) =
      Matrix.GeneralLinearGroup.map (conjLoc _ v)
        (Matrix.GeneralLinearGroup.map (pLoc E (cPl v)) (locGL E a (cPl w) g)) := fun v => rfl
  have key2 : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v)
      (Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g)) =
      Matrix.GeneralLinearGroup.map (pLoc E v) (locGL E a w (Matrix.GeneralLinearGroup.map (conjLoc _ w) g)) := fun v => by
    rw [key]
    by_cases h : v = w
    · subst h
      rw [pLoc_locGL, pLoc_locGL]
    · rw [pLoc_locGL_of_ne h, pLoc_locGL_of_ne (fun e => h (conjSrc_injective _ e)), map_one]
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_)
  exact congrArg (fun u : GL (Fin a) (v.adicCompletion E) => u.val i j) (key2 v)

/- English proof (translation)
Introduce `y` and use `by classical refine ⟨pLoc E _ (GlobalTheory.ThetaPull.cFin E (sLoc E w y)), ?_⟩ rw [← pLoc_conjFin] exact (congrArg (pLoc E w) (GlobalTheory.ThetaPull.cFin_cFin _)).trans (Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w y)`.
-/
private theorem conjLoc_surjective {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    Function.Surjective (conjLoc (IsCMField.complexConj E).toRingEquiv w) := fun y => by
  classical
  refine ⟨pLoc E _ (GlobalTheory.ThetaPull.cFin E (sLoc E w y)), ?_⟩
  rw [← pLoc_conjFin]
  exact (congrArg (pLoc E w) (GlobalTheory.ThetaPull.cFin_cFin _)).trans
    (Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w y)

/- English proof (translation)
Introduce `E _ _ _ n P ψ hd w hu B B' hB hB'`. Establish `hu' : (ψ⁻¹).UnrAt w` using `fun x hx => by`. Establish `h3 : ψ.loc w x = 1` using `hu x hx`. Conclude with `(congrArg Inv.inv h3).trans inv_one`. Establish `hC` using `GlobalTheory.SphGal.hasSatGL_twist E n P ψ⁻¹ w B hu' hB`.

Rewrite `hB'` using `[CG.hasSat_mk]`. Set `c : (cPl w).adicCompletion E ≃+* w.adicCompletion E` to `RingEquiv.ofBijective (conjLoc _ w) ⟨(conjLoc _ w).injective, conjLoc_surjective w⟩`. Establish `hq : Formalism.UG.qV E w = Formalism.UG.qV E (cPl w)`. Express the relevant statement in the definitionally equal form `Ideal.absNorm w.asIdeal = Ideal.absNorm (conjSrc (IsCMField.complexConj E).toRingEquiv w).asIdeal`. Rewrite using `[(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv w)]`.

Conclude with `(Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv _) (Ideal.map_comap_of_surjective _ (RingEquiv.surjective _) _).symm).toEquiv).symm`. Take `⟨x, hx⟩` from `GlobalTheory.LFun.HasSatGL.exists_vec hB'`. Establish `hx'` using `GlobalTheory.LFun.ConjPlace.isSatVecGL_invT c (conjLoc_spec _ w).2.2 hq hx`. Take `⟨β, -, hr, hf, -⟩` from `hd`. Use `sat_eq_of_pair ((P.twist ψ⁻¹).isSmooth_locRep w) β.flip hr (fun g u v => ?_) hx' hC` and prove the remaining obligations.

Take `⟨g, rfl⟩ : ∃ g', Matrix.GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv w) g' = g` from `⟨Matrix.GeneralLinearGroup.map c.symm.toRingHom g, Units.ext (Matrix.ext fun i j => c.apply_symm_apply _)⟩`. Establish `e1 : GlobalTheory.LFun.ConjPlace.invT (RingEquiv.refl _) n (Matrix.GeneralLinearGroup.map (conjLoc _ w) g) = GlobalTheory.LFun.ConjPlace.invT c n g` using `Units.ext (Matrix.ext fun i j => by`. Rewrite using `[GlobalTheory.LFun.ConjPlace.invT_val, GlobalTheory.LFun.ConjPlace.invT_val, ← map_inv]`. Use the proof step `rfl)`. Rewrite using `[e1]`.

Express the relevant statement in the definitionally equal form `β ((P.twist ψ⁻¹).locRep w _ v) (P.locRep (cPl w) ((GlobalTheory.LFun.ConjPlace.invT c n).symm (GlobalTheory.LFun.ConjPlace.invT c n g)) u) = β v u`. Rewrite using `[MulEquiv.symm_apply_apply, CuspSub.locRep_eq, CuspSub.locRep_eq, ← conj_locGL, ← hf (Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E n (cPl w) g)) v u]`. Establish `e2 : Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E n (cPl w) g)) = locGL E n (cPl w) g` using `Units.ext (Matrix.ext fun i j => GlobalTheory.ThetaPull.cFin_cFin _)`. Conclude with `congrArg (fun k => β _ (P.op (.fin k) u)) e2.symm`.
-/
theorem UpperTheory.V.Br.satOfPol :
    UpperTheory.V.Br.SatOfPol := by
  intro E _ _ _ n P ψ hd w hu B B' hB hB'
  have hu' : (ψ⁻¹).UnrAt w := fun x hx => by
    have h3 : ψ.loc w x = 1 := hu x hx
    exact (congrArg Inv.inv h3).trans inv_one
  have hC := GlobalTheory.SphGal.hasSatGL_twist E n P ψ⁻¹ w B hu' hB
  rw [CG.hasSat_mk] at hB'
  let c : (cPl w).adicCompletion E ≃+* w.adicCompletion E :=
    RingEquiv.ofBijective (conjLoc _ w) ⟨(conjLoc _ w).injective, conjLoc_surjective w⟩
  have hq : Formalism.UG.qV E w = Formalism.UG.qV E (cPl w) := by
    change Ideal.absNorm w.asIdeal = Ideal.absNorm (conjSrc (IsCMField.complexConj E).toRingEquiv w).asIdeal
    rw [(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv w)]
    exact (Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv _)
      (Ideal.map_comap_of_surjective _ (RingEquiv.surjective _) _).symm).toEquiv).symm
  obtain ⟨x, hx⟩ := GlobalTheory.LFun.HasSatGL.exists_vec hB'
  have hx' := GlobalTheory.LFun.ConjPlace.isSatVecGL_invT c (conjLoc_spec _ w).2.2 hq hx
  obtain ⟨β, -, hr, hf, -⟩ := hd
  refine sat_eq_of_pair ((P.twist ψ⁻¹).isSmooth_locRep w) β.flip hr (fun g u v => ?_) hx' hC
  obtain ⟨g, rfl⟩ : ∃ g', Matrix.GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv w) g' = g :=
    ⟨Matrix.GeneralLinearGroup.map c.symm.toRingHom g, Units.ext (Matrix.ext fun i j => c.apply_symm_apply _)⟩
  have e1 : GlobalTheory.LFun.ConjPlace.invT (RingEquiv.refl _) n (Matrix.GeneralLinearGroup.map (conjLoc _ w) g) =
      GlobalTheory.LFun.ConjPlace.invT c n g := Units.ext (Matrix.ext fun i j => by
    rw [GlobalTheory.LFun.ConjPlace.invT_val, GlobalTheory.LFun.ConjPlace.invT_val, ← map_inv]; rfl)
  rw [e1]
  change β ((P.twist ψ⁻¹).locRep w _ v) (P.locRep (cPl w) ((GlobalTheory.LFun.ConjPlace.invT c n).symm (GlobalTheory.LFun.ConjPlace.invT c n g)) u) = β v u
  rw [MulEquiv.symm_apply_apply, CuspSub.locRep_eq, CuspSub.locRep_eq, ← conj_locGL, ← hf (Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E n (cPl w) g)) v u]
  have e2 : Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E n (cPl w) g)) = locGL E n (cPl w) g :=
    Units.ext (Matrix.ext fun i j => GlobalTheory.ThetaPull.cFin_cFin _)
  exact congrArg (fun k => β _ (P.op (.fin k) u)) e2.symm
