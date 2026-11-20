import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LiftPfA
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd

noncomputable section

namespace Formalism.MainNotions.N.Ln34.CrystallineExponents

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Use `haveI : NeZero l := ⟨hl.ne_zero⟩`. Use `haveI : Algebra.IsAlgebraic ↥(K0 K) (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) _`. Use `haveI : IsAlgClosure ↥(K0 K) (Om l) := ⟨inferInstance, inferInstance⟩`. Establish `hint : IsIntegral ↥(K0 K) z` using `Algebra.IsIntegral.isIntegral z`.

Establish `hle : K0 K ≤ Ks K 1` using `le_sup_left`. Establish `hdeg` using `CyclotomicLifting.cyclotomic_degree_max_unramified K`. Rewrite `hdeg` using `[IntermediateField.relfinrank_eq_finrank_of_le hle]`. Establish `hsub : IntermediateField.extendScalars hle ≤ IntermediateField.adjoin ↥(K0 K) {z}`. Establish `h : Ks K 1 ≤ (IntermediateField.adjoin ↥(K0 K) {z}).restrictScalars ℚ_[l]`.

Use `sup_le (fun x hx => ?_) (IntermediateField.adjoin_le_iff.2 fun x hx => ?_)` and prove the remaining obligations. Conclude with `(IntermediateField.adjoin ↥(K0 K) {z}).algebraMap_mem ⟨x, hx⟩`. Establish `hx1 : x ^ l = 1` using `by simpa using hx`. Take `⟨b, -, rfl⟩` from `hz.eq_pow_of_pow_eq_one hx1`. Conclude with `pow_mem (IntermediateField.mem_adjoin_simple_self ↥(K0 K) z) b`.

Introduce `x hx`. Conclude with `h hx`. Use `haveI := IntermediateField.adjoin.finiteDimensional hint`. Establish `hd : l - 1 ≤ (minpoly ↥(K0 K) z).natDegree`. Rewrite using `[← IntermediateField.adjoin.finrank hint, ← hdeg]`.

Conclude with `IntermediateField.finrank_le_of_le_right hsub`. Establish `hroot : ∀ {w : Om l}, IsPrimitiveRoot w l → Polynomial.aeval w (Polynomial.cyclotomic l ↥(K0 K)) = 0` using `fun {w} hw => by`. Rewrite using `[Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]`. Conclude with `hw.isRoot_cyclotomic hl.pos`. Establish `hdvd : minpoly ↥(K0 K) z ∣ Polynomial.cyclotomic l ↥(K0 K)` using `minpoly.dvd _ _ (hroot hz)`.

Establish `heq : Polynomial.cyclotomic l ↥(K0 K) = minpoly ↥(K0 K) z` using `Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (Polynomial.cyclotomic.monic _ _) hdvd (by rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hl]; exact hd)`. Establish `h0 : Polynomial.aeval z' (minpoly ↥(K0 K) z) = 0` using `heq ▸ hroot hz'`. Conclude with `minpoly.exists_algEquiv_of_root' hint.isAlgebraic h0`.
-/
theorem exists_aut_prim (K : FinExt l) {z z' : Om l} (hz : IsPrimitiveRoot z l)
    (hz' : IsPrimitiveRoot z' l) : ∃ g : Om l ≃ₐ[↥(K0 K)] Om l, g z = z' := by
  have hl : l.Prime := Fact.out
  haveI : NeZero l := ⟨hl.ne_zero⟩
  haveI : Algebra.IsAlgebraic ↥(K0 K) (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) _
  haveI : IsAlgClosure ↥(K0 K) (Om l) := ⟨inferInstance, inferInstance⟩
  have hint : IsIntegral ↥(K0 K) z := Algebra.IsIntegral.isIntegral z
  have hle : K0 K ≤ Ks K 1 := le_sup_left
  have hdeg := CyclotomicLifting.cyclotomic_degree_max_unramified K
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle] at hdeg
  have hsub : IntermediateField.extendScalars hle ≤ IntermediateField.adjoin ↥(K0 K) {z} := by
    have h : Ks K 1 ≤ (IntermediateField.adjoin ↥(K0 K) {z}).restrictScalars ℚ_[l] := by
      refine sup_le (fun x hx => ?_) (IntermediateField.adjoin_le_iff.2 fun x hx => ?_)
      · exact (IntermediateField.adjoin ↥(K0 K) {z}).algebraMap_mem ⟨x, hx⟩
      · have hx1 : x ^ l = 1 := by simpa using hx
        obtain ⟨b, -, rfl⟩ := hz.eq_pow_of_pow_eq_one hx1
        exact pow_mem (IntermediateField.mem_adjoin_simple_self ↥(K0 K) z) b
    intro x hx
    exact h hx
  haveI := IntermediateField.adjoin.finiteDimensional hint
  have hd : l - 1 ≤ (minpoly ↥(K0 K) z).natDegree := by
    rw [← IntermediateField.adjoin.finrank hint, ← hdeg]
    exact IntermediateField.finrank_le_of_le_right hsub
  have hroot : ∀ {w : Om l}, IsPrimitiveRoot w l →
      Polynomial.aeval w (Polynomial.cyclotomic l ↥(K0 K)) = 0 := fun {w} hw => by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
    exact hw.isRoot_cyclotomic hl.pos
  have hdvd : minpoly ↥(K0 K) z ∣ Polynomial.cyclotomic l ↥(K0 K) := minpoly.dvd _ _ (hroot hz)
  have heq : Polynomial.cyclotomic l ↥(K0 K) = minpoly ↥(K0 K) z :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
      (Polynomial.cyclotomic.monic _ _) hdvd
      (by rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hl]; exact hd)
  have h0 : Polynomial.aeval z' (minpoly ↥(K0 K) z) = 0 := heq ▸ hroot hz'
  exact minpoly.exists_algEquiv_of_root' hint.isAlgebraic h0

/- English proof (translation)
Establish `: Algebra.IsAlgebraic ↥(K0 K) (Om l)` using `Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) _`. Take `⟨σ, hσ⟩` from `IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ_[l]) (L := ↥(K0 K)) (M := Om l) (E := Om l) ((LL.1.val).comp (((HW l).W K 1 LL hG).emb c))`. Establish `hσx : ∀ x : ↥(K0 K), σ (x : Om l) = ((((HW l).W K 1 LL hG).emb c x : ↥LL.1) : Om l)` using `fun x => by`. Use `congrArg (fun f => f x) hσ` as an intermediate fact. Simplify `this` using `[AlgHom.domRestrict]`.

Establish `hζ₁` using `Formalism.MainNotions.UnusedSlot80.LevR.root_of_unity_primitive D l`. Establish `hσinj : Function.Injective σ` using `σ.toRingHom.injective`. Establish `hζO : IsPrimitiveRoot ((ζ : ↥LL.1) : Om l) l` using `hζ.map_of_injective (f := LL.1.val) Subtype.val_injective`. Establish `hσζ₁ : IsPrimitiveRoot (σ ((D.loc l).ζQ 1)) l` using `hζ₁.map_of_injective hσinj`. Establish `: NeZero l` using `⟨(Fact.out : l.Prime).ne_zero⟩`.

Take `⟨b, -, hb⟩` from `hσζ₁.eq_pow_of_pow_eq_one hζO.pow_eq_one`. Establish `hβ : IsPrimitiveRoot ((D.loc l).ζQ 1 ^ b) l`. Apply `IsPrimitiveRoot.of_map_of_injective (f := σ) _ hσinj` to reduce the goal to its premises. Rewrite using `[map_pow, hb]`. Conclude with `hζO`.

Take `⟨g, hg⟩` from `exists_aut_prim K hζ₁ hβ`. Set `g' : Om l →ₐ[ℚ_[l]] Om l` to `(g.toAlgHom).restrictScalars ℚ_[l]`. Establish `hmem : ∀ y, ((σ.comp g').comp (Ks K 1).val) y ∈ LL.1` using `hG.2.2.2 _`. Set `τs : ↥(Ks K 1) →ₐ[ℚ_[l]] ↥LL.1` to `((σ.comp g').comp (Ks K 1).val).codRestrict LL.1.toSubalgebra hmem`. Use `⟨τs.comp (IntermediateField.inclusion hG.2.2.1), τs, ⟨fun x y hxy => ?_, fun y hy => ?_⟩, fun x y hxy => ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext show σ (g (y : Om l)) = _` to reduce the goal to its premises. Establish `hgx : g (x : Om l) = x` using `g.commutes x`. Rewrite using `[hxy, hgx, hσx]`. Apply `Subtype.ext show σ (g (y : Om l)) = _` to reduce the goal to its premises. Rewrite using `[hy, hg, map_pow, hb]`.

Use `show τs _ = τs y`. Use `congr 1`. Conclude with `Subtype.ext hxy.symm`.
-/
theorem exists_pt (D : D7) (HW : HWOf D.loc) {K LL : FinExt l} (hG : Good K 1 LL)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (hζ : IsPrimitiveRoot ζ l) :
    ∃ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ := by
  have : Algebra.IsAlgebraic ↥(K0 K) (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) _
  obtain ⟨σ, hσ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ_[l]) (L := ↥(K0 K))
    (M := Om l) (E := Om l) ((LL.1.val).comp (((HW l).W K 1 LL hG).emb c))
  have hσx : ∀ x : ↥(K0 K),
      σ (x : Om l) = ((((HW l).W K 1 LL hG).emb c x : ↥LL.1) : Om l) := fun x => by
    have := congrArg (fun f => f x) hσ
    simpa [AlgHom.domRestrict] using this
  have hζ₁ := Formalism.MainNotions.UnusedSlot80.LevR.root_of_unity_primitive D l
  have hσinj : Function.Injective σ := σ.toRingHom.injective
  have hζO : IsPrimitiveRoot ((ζ : ↥LL.1) : Om l) l :=
    hζ.map_of_injective (f := LL.1.val) Subtype.val_injective
  have hσζ₁ : IsPrimitiveRoot (σ ((D.loc l).ζQ 1)) l := hζ₁.map_of_injective hσinj
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨b, -, hb⟩ := hσζ₁.eq_pow_of_pow_eq_one hζO.pow_eq_one
  have hβ : IsPrimitiveRoot ((D.loc l).ζQ 1 ^ b) l := by
    apply IsPrimitiveRoot.of_map_of_injective (f := σ) _ hσinj
    rw [map_pow, hb]
    exact hζO
  obtain ⟨g, hg⟩ := exists_aut_prim K hζ₁ hβ
  let g' : Om l →ₐ[ℚ_[l]] Om l := (g.toAlgHom).restrictScalars ℚ_[l]
  have hmem : ∀ y, ((σ.comp g').comp (Ks K 1).val) y ∈ LL.1 := hG.2.2.2 _
  let τs : ↥(Ks K 1) →ₐ[ℚ_[l]] ↥LL.1 :=
    ((σ.comp g').comp (Ks K 1).val).codRestrict LL.1.toSubalgebra hmem
  refine ⟨τs.comp (IntermediateField.inclusion hG.2.2.1), τs,
    ⟨fun x y hxy => ?_, fun y hy => ?_⟩, fun x y hxy => ?_⟩
  · apply Subtype.ext
    show σ (g (y : Om l)) = _
    have hgx : g (x : Om l) = x := g.commutes x
    rw [hxy, hgx, hσx]
  · apply Subtype.ext
    show σ (g (y : Om l)) = _
    rw [hy, hg, map_pow, hb]
  · show τs _ = τs y
    congr 1
    exact Subtype.ext hxy.symm

end Formalism.MainNotions.N.Ln34.CrystallineExponents

end
