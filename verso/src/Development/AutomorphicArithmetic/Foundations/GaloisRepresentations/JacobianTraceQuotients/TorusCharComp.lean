import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuot
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.IrreducibleAdmissibleGL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ImStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.CharDom
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceExp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ExistsCommonEigenvector
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ExpSub
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ExpLev
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.SubPerm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.SubQuot
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.NormDom
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.OfSupportHolds

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

namespace UpperTheory.Gal.Join

/- English proof (translation)
Establish `h' : ∀ y ∈ P, (T ∘ₗ (c • LinearMap.id)) y ∈ P` using `fun y hy => h _ (P.smul_mem c hy)`. Rewrite using `[trIn, trIn, dif_pos h, dif_pos h', ← smul_eq_mul, ← map_smul]`. Use `congr 1`. Use extensionality with `y`. Simplify using `[LinearMap.restrict_apply]`.
-/
private theorem trIn_smul {X : Type} [AddCommGroup X] [Module ℂ X] {P : Submodule ℂ X} {T : X →ₗ[ℂ] X}
    (h : ∀ y ∈ P, T y ∈ P) (c : ℂ) : trIn P (T ∘ₗ (c • LinearMap.id)) = c * trIn P T := by
  have h' : ∀ y ∈ P, (T ∘ₗ (c • LinearMap.id)) y ∈ P := fun y hy => h _ (P.smul_mem c hy)
  rw [trIn, trIn, dif_pos h, dif_pos h', ← smul_eq_mul, ← map_smul]
  congr 1
  ext y
  simp [LinearMap.restrict_apply]

/- English proof (translation)
The claim follows from `PositivityTheory.Exh.irreducibleAdmissibleGL _ n τ.V τ.ρ τ.smooth τ.irred`.
-/
private theorem adm {K : Type} [Field K] [NumberField K] {n : ℕ} {w : Pl K} (τ : SmIrr (Gw n w)) : IsAdmissible τ.ρ :=
  PositivityTheory.Exh.irreducibleAdmissibleGL _ n τ.V τ.ρ τ.smooth τ.irred

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ _ σ hσ hp n hn v w hns σw N hs hN π P hP hW τ τ' hτ hτ' μ ⟨y, hy0, hy⟩`. Take `⟨A, hA, hA0, hc⟩` from `h F E σ hσ hp n hn v w hns σw N hs hN π P hP hW τ τ' hτ hτ'`. Take `⟨U, hU, hy'⟩` from `expLev _ n _ τ.ρ τ.smooth y`. Take `⟨K', -, K, hK, l', l, hst, c, t₀, hc0, hid⟩` from `hc ⊤ U (by simp) hU`. Take `⟨f', st', sa'⟩` from `imStab _ n _ τ'.ρ (adm τ') K' l'`.

Take `⟨f, st, -⟩` from `imStab _ n _ τ.ρ (adm τ) K l`. Take `⟨E', e', m'⟩` from `traceExp _ _ (jacB τ'.ρ) (imK τ'.ρ K') st'`. Take `⟨E₀, e, m⟩` from `traceExp _ _ (jacB τ.ρ) (imK τ.ρ K) st`. Establish `hμ : μ.comp (nT n N) ∈ E₀.map fun μ => μ.comp (nT n N)` using `Multiset.mem_map_of_mem _ ((m μ).2 ⟨y, hy' K hK, hy0, hy⟩)`. Establish `hid' : ∀ t, Dom t → trIn (imK τ'.ρ K') (jacB τ'.ρ (t₀ * t) ∘ₗ jacA hA) = c * ((E₀.map fun μ => μ.comp (nT n N)).map fun μ => (μ (t₀ * t) : ℂ)).sum` using `fun t ht => by`.

Rewrite using `[hid t ht, e, Multiset.map_map]`. Both sides reduce to the same expression. Take `⟨t₁, ht₁, hne⟩` from `(charDom _ n t₀ (E₀.map fun μ => μ.comp (nT n N)) _ 1 1 one_ne_zero fun _ _ => rfl).2 (fun h0 => by rw [h0] at hμ; exact Multiset.notMem_zero _ hμ)`. Take `⟨μ', hinv, z, -, hz0, hz⟩` from `twExp _ _ (jacB τ'.ρ) (imK τ'.ρ K') (MulEquiv.piCongrRight fun _ => Units.mapEquiv σw.toMulEquiv) (jacA hA) st' (sa' σw A hA hst) (fun t y => jacSemi _ n σw hN.cyc.isom _ τ'.ρ A hA t y) (t₀ * t₁) (by rw [hid' t₁ ht₁]; exact mul_ne_zero hc0 hne)`. Take `⟨ω', rfl, s', q'⟩` from `expSub _ n _ τ'.ρ τ'.smooth τ'.irred μ' ⟨z, hz0, hz⟩`.

Establish `i' : ∀ i, Inv σw (ω' i)` using `fun i x => by`. Establish `h1` using `hinv (Pi.mulSingle i x)`. Establish `h2 : ∀ x, torusChar ω' (Pi.mulSingle i x) = ω' i x` using `fun x => by`. Rewrite using `[torusChar_apply, Finset.prod_eq_single i (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj, map_one]) (by simp), Pi.mulSingle_eq_same]`. Rewrite using `[← h2, ← h2, ← h1]`.

Use `congr 1`. Use function extensionality and compare the values at `j`. Express the relevant statement in the definitionally equal form `_ = Units.mapEquiv σw.toMulEquiv ((Pi.mulSingle i x : Fin n → _) j)`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality.

Rewrite using `[Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]`. Both sides reduce to the same expression. Rewrite using `[Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj, map_one]`. Take `⟨-, -, -, c', hc', hsc, -⟩` from `locDesc_holds _ n σw _ hN.cyc _ τ'.ρ τ'.irred ω' s' i' q' A hA hA0`. Establish `key` using `(charDom _ n t₀ (E₀.map fun μ => μ.comp (nT n N)) E' c c' hc0 fun t ht => by`.

Rewrite using `[← hid' t ht, hsc, trIn_smul (st' _), e']).1 _ hμ`. Take `⟨x, -, hx0, hx⟩` from `(m' _).1 key`. Conclude with `⟨x, hx0, hx⟩`.
-/
theorem liftExp (h : CoreId) : LiftExp := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn v w hns σw N hs hN π P hP hW τ τ' hτ hτ' μ ⟨y, hy0, hy⟩
  obtain ⟨A, hA, hA0, hc⟩ := h F E σ hσ hp n hn v w hns σw N hs hN π P hP hW τ τ' hτ hτ'
  obtain ⟨U, hU, hy'⟩ := expLev _ n _ τ.ρ τ.smooth y
  obtain ⟨K', -, K, hK, l', l, hst, c, t₀, hc0, hid⟩ := hc ⊤ U (by simp) hU
  obtain ⟨f', st', sa'⟩ := imStab _ n _ τ'.ρ (adm τ') K' l'
  obtain ⟨f, st, -⟩ := imStab _ n _ τ.ρ (adm τ) K l
  obtain ⟨E', e', m'⟩ := traceExp _ _ (jacB τ'.ρ) (imK τ'.ρ K') st'
  obtain ⟨E₀, e, m⟩ := traceExp _ _ (jacB τ.ρ) (imK τ.ρ K) st
  have hμ : μ.comp (nT n N) ∈ E₀.map fun μ => μ.comp (nT n N) :=
    Multiset.mem_map_of_mem _ ((m μ).2 ⟨y, hy' K hK, hy0, hy⟩)
  have hid' : ∀ t, Dom t → trIn (imK τ'.ρ K') (jacB τ'.ρ (t₀ * t) ∘ₗ jacA hA) =
      c * ((E₀.map fun μ => μ.comp (nT n N)).map fun μ => (μ (t₀ * t) : ℂ)).sum := fun t ht => by
    rw [hid t ht, e, Multiset.map_map]
    rfl
  obtain ⟨t₁, ht₁, hne⟩ := (charDom _ n t₀ (E₀.map fun μ => μ.comp (nT n N)) _ 1 1 one_ne_zero fun _ _ => rfl).2
    (fun h0 => by rw [h0] at hμ; exact Multiset.notMem_zero _ hμ)
  obtain ⟨μ', hinv, z, -, hz0, hz⟩ := twExp _ _ (jacB τ'.ρ) (imK τ'.ρ K')
    (MulEquiv.piCongrRight fun _ => Units.mapEquiv σw.toMulEquiv) (jacA hA) st' (sa' σw A hA hst)
    (fun t y => jacSemi _ n σw hN.cyc.isom _ τ'.ρ A hA t y) (t₀ * t₁) (by rw [hid' t₁ ht₁]; exact mul_ne_zero hc0 hne)
  obtain ⟨ω', rfl, s', q'⟩ := expSub _ n _ τ'.ρ τ'.smooth τ'.irred μ' ⟨z, hz0, hz⟩
  have i' : ∀ i, Inv σw (ω' i) := fun i x => by
    have h1 := hinv (Pi.mulSingle i x)
    have h2 : ∀ x, torusChar ω' (Pi.mulSingle i x) = ω' i x := fun x => by
      rw [torusChar_apply, Finset.prod_eq_single i (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj, map_one]) (by simp),
        Pi.mulSingle_eq_same]
    rw [← h2, ← h2, ← h1]
    congr 1
    funext j
    change _ = Units.mapEquiv σw.toMulEquiv ((Pi.mulSingle i x : Fin n → _) j)
    by_cases hj : j = i
    · subst hj
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
      rfl
    · rw [Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj, map_one]
  obtain ⟨-, -, -, c', hc', hsc, -⟩ := locDesc_holds _ n σw _ hN.cyc _ τ'.ρ τ'.irred ω' s' i' q' A hA hA0
  have key := (charDom _ n t₀ (E₀.map fun μ => μ.comp (nT n N)) E' c c' hc0 fun t ht => by
    rw [← hid' t ht, hsc, trIn_smul (st' _), e']).1 _ hμ
  obtain ⟨x, -, hx0, hx⟩ := (m' _).1 key
  exact ⟨x, hx0, hx⟩

/- English proof (translation)
Establish `hnt : Nontrivial τ.V` using `GroundTheory.Automorphic.RestrictedTensor.nontrivial_of_isIrreducible τ.irred`. Take `⟨h1, h2, h3, -⟩` from `locDesc_holds _ n (RingEquiv.refl _) 1 ⟨fun _ => rfl, one_pos, fun _ => rfl⟩ _ τ.ρ τ.irred ω s (fun _ _ => rfl) q LinearMap.id (fun _ _ => rfl) (fun h => by`. Take `⟨x, hx⟩` from `exists_ne (0 : τ.V)`. Conclude with `hx (LinearMap.congr_fun h x))`. Take `⟨E₀, e, m⟩` from `traceExp _ _ (jacB τ.ρ) ⊤ fun _ _ _ => trivial`.

Establish `hne : E₀ ≠ 0`. Introduce and unpack `rfl`. Establish `h4` using `e 1`. Rewrite `h4` using `[map_one, trIn, dif_pos fun _ _ => Submodule.mem_top]`. Establish `h5 : LinearMap.trace ℂ (⊤ : Submodule ℂ (Jacquet τ.ρ (unipB _ (Fin n)))) 1 = 0` using `h4`.

Rewrite `h5` using `[LinearMap.trace_one, finrank_top, Nat.cast_eq_zero]`. Conclude with `Module.finrank_pos.ne' h5`. Take `⟨μ, hμ⟩` from `Multiset.exists_mem_of_ne_zero hne`. Take `⟨y, -, hy⟩` from `(m μ).1 hμ`. Take `⟨p, rfl⟩` from `h3 μ ((subQuot _ _ (jacB τ.ρ) μ).1.1 ⟨y, hy⟩)`.

Conclude with `⟨p, y, hy⟩`.
-/
private theorem exp_of_sub {K : Type} [Field K] [NumberField K] {n : ℕ} {w : Pl K} (τ : SmIrr (Gw n w))
    {ω : Fin n → (w.adicCompletion K)ˣ →* ℂˣ} (s : ∀ i, IsSmoothChar (ω i)) (q : IsSubquotient τ.ρ (prinSeries ω)) :
    ∃ p : Equiv.Perm (Fin n), IsExp τ.ρ (torusChar (ω ∘ p)) := by
  have hnt : Nontrivial τ.V := GroundTheory.Automorphic.RestrictedTensor.nontrivial_of_isIrreducible τ.irred
  obtain ⟨h1, h2, h3, -⟩ := locDesc_holds _ n (RingEquiv.refl _) 1 ⟨fun _ => rfl, one_pos, fun _ => rfl⟩ _ τ.ρ τ.irred ω s
    (fun _ _ => rfl) q LinearMap.id (fun _ _ => rfl) (fun h => by
      obtain ⟨x, hx⟩ := exists_ne (0 : τ.V)
      exact hx (LinearMap.congr_fun h x))
  obtain ⟨E₀, e, m⟩ := traceExp _ _ (jacB τ.ρ) ⊤ fun _ _ _ => trivial
  have hne : E₀ ≠ 0 := by
    rintro rfl
    have h4 := e 1
    rw [map_one, trIn, dif_pos fun _ _ => Submodule.mem_top] at h4
    have h5 : LinearMap.trace ℂ (⊤ : Submodule ℂ (Jacquet τ.ρ (unipB _ (Fin n)))) 1 = 0 := h4
    rw [LinearMap.trace_one, finrank_top, Nat.cast_eq_zero] at h5
    exact Module.finrank_pos.ne' h5
  obtain ⟨μ, hμ⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨y, -, hy⟩ := (m μ).1 hμ
  obtain ⟨p, rfl⟩ := h3 μ ((subQuot _ _ (jacB τ.ρ) μ).1.1 ⟨y, hy⟩)
  exact ⟨p, y, hy⟩

/- English proof (translation)
Establish `h2 : ∀ (a : Fin n → Rˣ →* ℂˣ) i x, torusChar a (Pi.mulSingle i x) = a i x` using `fun a i x => by`. Rewrite using `[torusChar_apply, Finset.prod_eq_single i (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj, map_one]) (by simp), Pi.mulSingle_eq_same]`. Use function extensionality and compare the values at `i`. Use `ext1 x`. Rewrite using `[← h2, ← h2, h]`.
-/
private theorem torusChar_inj {R : Type} [CommRing R] {n : ℕ} {a b : Fin n → Rˣ →* ℂˣ} (h : torusChar a = torusChar b) : a = b := by
  have h2 : ∀ (a : Fin n → Rˣ →* ℂˣ) i x, torusChar a (Pi.mulSingle i x) = a i x := fun a i x => by
    rw [torusChar_apply, Finset.prod_eq_single i (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj, map_one]) (by simp),
      Pi.mulSingle_eq_same]
  funext i
  ext1 x
  rw [← h2, ← h2, h]

/- English proof (translation)
Use `MonoidHom.ext fun t => ?_` and prove the remaining obligations. Rewrite using `[MonoidHom.comp_apply, torusChar_apply, torusChar_apply]`. Both sides reduce to the same expression.
-/
private theorem torusChar_comp {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (a : Fin n → Rˣ →* ℂˣ) (N : Sˣ →* Rˣ) :
    (torusChar a).comp (nT n N) = torusChar fun i => (a i).comp N := by
  refine MonoidHom.ext fun t => ?_
  rw [MonoidHom.comp_apply, torusChar_apply, torusChar_apply]
  rfl

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ _ σ hσ hp n hn v w hns σw N hs hN π P hP hW τ τ' hτ hτ' ω s q`. Take `⟨p, hp'⟩` from `exp_of_sub τ s q`. Establish `h1` using `liftExp h F E σ hσ hp n hn v w hns σw N hs hN π P hP hW τ τ' hτ hτ' _ hp'`. Take `⟨ω', e, s', q'⟩` from `expSub _ n _ τ'.ρ τ'.smooth τ'.irred _ h1`. Rewrite `e` using `[torusChar_comp]`.

Take `rfl` from `torusChar_inj e`. Establish `h2` using `subPerm _ n _ τ'.ρ τ'.irred _ s' p.symm q'`. Establish `h3 : (fun i => ((ω ∘ p) i).comp N) ∘ p.symm = fun i => (ω i).comp N` using `funext fun i => by simp`. Rewrite `h2` using `[h3]`. Then use the resulting hypothesis.
-/
theorem liftGood (h : CoreId) : LiftGood := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn v w hns σw N hs hN π P hP hW τ τ' hτ hτ' ω s q
  obtain ⟨p, hp'⟩ := exp_of_sub τ s q
  have h1 := liftExp h F E σ hσ hp n hn v w hns σw N hs hN π P hP hW τ τ' hτ hτ' _ hp'
  obtain ⟨ω', e, s', q'⟩ := expSub _ n _ τ'.ρ τ'.smooth τ'.irred _ h1
  rw [torusChar_comp] at e
  obtain rfl := torusChar_inj e
  have h2 := subPerm _ n _ τ'.ρ τ'.irred _ s' p.symm q'
  have h3 : (fun i => ((ω ∘ p) i).comp N) ∘ p.symm = fun i => (ω i).comp N := funext fun i => by simp
  rwa [h3] at h2

end UpperTheory.Gal.Join
