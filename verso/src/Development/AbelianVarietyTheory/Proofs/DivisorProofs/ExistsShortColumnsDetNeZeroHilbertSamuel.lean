import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMultiplicationFlatColumnsEvalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentOfFiltrationSymbolDetNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymbolsOfEvaluatedColumnsHermitianMultSystemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDeepestFiltrationStepEqRationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockWordOfTypeProdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExchangeIndependentCompletionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisChoiceDetNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockSymbolMatrixNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetColumnsNeZeroOfPointValuesIndependentStatement
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.HSShort.ChooseCols

/- English proof (translation)
Introduce `E _ _ N δ y hy`. Set `P : MvPolynomial (Fin N) E` to `∏ p, ∑ k, X k * C (y p k)`. Establish `hP : P ≠ 0`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `p _ h`.

Apply `hy p` to reduce the goal to its premises. Use function extensionality and compare the values at `k`. Establish `h1` using `congrArg (eval (Pi.single k 1)) h`. Simplify `h1` using `[Pi.single_apply]`. Establish `hx : ∃ x : Fin N → E, eval x P ≠ 0`.

Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Conclude with `hP (MvPolynomial.funext fun x => by rw [hne x, map_zero])`. Take `⟨x, hx⟩` from `hx`. Use `⟨x, fun p => ?_⟩` and prove the remaining obligations.

Establish `h2 : eval x P = ∏ p, ∑ k, x k * y p k` using `by simp [P]`. Rewrite `hx` using `[h2, Finset.prod_ne_zero_iff]`. Conclude with `hx p (Finset.mem_univ _)`.
-/
theorem avoid : ∀ (E : Type) [Field E] [Infinite E] (N δ : ℕ) (y : Fin δ → Fin N → E), (∀ p, y p ≠ 0) →
    ∃ l : Fin N → E, ∀ p, ∑ k, l k * y p k ≠ 0 := by
  intro E _ _ N δ y hy
  classical
  let P : MvPolynomial (Fin N) E := ∏ p, ∑ k, X k * C (y p k)
  have hP : P ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p _ h
    apply hy p
    funext k
    have h1 := congrArg (eval (Pi.single k 1)) h
    simpa [Pi.single_apply] using h1
  have hx : ∃ x : Fin N → E, eval x P ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hP (MvPolynomial.funext fun x => by rw [hne x, map_zero])
  obtain ⟨x, hx⟩ := hx
  refine ⟨x, fun p => ?_⟩
  have h2 : eval x P = ∏ p, ∑ k, x k * y p k := by simp [P]
  rw [h2, Finset.prod_ne_zero_iff] at hx
  exact hx p (Finset.mem_univ _)

/- English proof (translation)
Introduce `F E A A' _ _ _ _ _ _ _ ι V r bb`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `hx' : x = ∑ i, bb.repr ⟨x, hx⟩ i • (bb i : A)`.

Establish `h` using `congrArg Subtype.val (bb.sum_repr ⟨x, hx⟩)`. Rewrite `h` using `[Submodule.coe_sum]`. Simplify using `using h.symm`. Rewrite using `[hx', map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.map_smulₛₗ]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `Submodule.subset_span ⟨bb i, (bb i).2, rfl⟩`.
-/
theorem span_basis : ∀ (F E A A' : Type) [Field F] [Field E] [Algebra F E] [AddCommGroup A] [Module F A] [AddCommGroup A']
    [Module E A'] (ι : A →ₛₗ[algebraMap F E] A') (V : Submodule F A) (r : ℕ) (bb : Module.Basis (Fin r) F V),
    Submodule.span E (ι '' (V : Set A)) = Submodule.span E (Set.range fun i => ι (bb i)) := by
  intro F E A A' _ _ _ _ _ _ _ ι V r bb
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x = ∑ i, bb.repr ⟨x, hx⟩ i • (bb i : A) := by
      have h := congrArg Subtype.val (bb.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at h
      simpa using h.symm
    rw [hx', map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨bb i, (bb i).2, rfl⟩

/- English proof (translation)
Introduce `E M X _ _ _ g U hU hfin`. Take `⟨B, hBsub, hBspan, hBind⟩` from `exists_linearIndependent E (Set.range g)`. Rewrite `hBspan` using `[hU]`. Establish `hBU : ∀ x ∈ B, x ∈ U` using `fun x hx => hBspan ▸ Submodule.subset_span hx`. Establish `hind' : LinearIndependent E (fun x : B => (⟨x.1, hBU x.1 x.2⟩ : U))` using `LinearIndependent.of_comp U.subtype hBind`.

Use `haveI : Finite B := hind'.finite_of_isNoetherian`. Use `haveI : Fintype B := Fintype.ofFinite B`. Establish `hsrc : ∀ x : B, ∃ y, g y = x.1` using `fun x => hBsub x.2`. Use `choose τ hτ using hsrc`. Set `e : Fin (Fintype.card B) ≃ B` to `(Fintype.equivFin B).symm`.

Use `⟨Fintype.card B, fun k => τ (e k), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hBspan]`. Establish `h` using `finrank_span_eq_card hBind`. Rewrite `h` using `[Subtype.range_coe_subtype, Set.setOf_mem_eq]`. Conclude with `h.symm`.

Establish `h` using `hBind.comp e e.injective`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Conclude with `hτ (e k)`.
-/
theorem pick_indep : ∀ (E M X : Type) [Field E] [AddCommGroup M] [Module E M] (g : X → M) (U : Submodule E M),
    Submodule.span E (Set.range g) = U → FiniteDimensional E U →
    ∃ (n : ℕ) (σ : Fin n → X), n = Module.finrank E U ∧ LinearIndependent E fun k => g (σ k) := by
  intro E M X _ _ _ g U hU hfin
  classical
  obtain ⟨B, hBsub, hBspan, hBind⟩ := exists_linearIndependent E (Set.range g)
  rw [hU] at hBspan
  have hBU : ∀ x ∈ B, x ∈ U := fun x hx => hBspan ▸ Submodule.subset_span hx
  have hind' : LinearIndependent E (fun x : B => (⟨x.1, hBU x.1 x.2⟩ : U)) :=
    LinearIndependent.of_comp U.subtype hBind
  haveI : Finite B := hind'.finite_of_isNoetherian
  haveI : Fintype B := Fintype.ofFinite B
  have hsrc : ∀ x : B, ∃ y, g y = x.1 := fun x => hBsub x.2
  choose τ hτ using hsrc
  let e : Fin (Fintype.card B) ≃ B := (Fintype.equivFin B).symm
  refine ⟨Fintype.card B, fun k => τ (e k), ?_, ?_⟩
  · rw [← hBspan]
    have h := finrank_span_eq_card hBind
    rw [Subtype.range_coe_subtype, Set.setOf_mem_eq] at h
    exact h.symm
  · have h := hBind.comp e e.injective
    convert h using 1
    funext k
    exact hτ (e k)

/- English proof (translation)
Introduce `F A _ _ _ _ _ _ S E A' _ _ _ _ s δ Φ r bD`. Rewrite using `[Φ.div, span_basis F E A A' Φ.ι (S.V S.D) r bD]`. Repeatedly rewrite using `[Submodule.map_span]`. Rewrite using `[← Submodule.span_iUnion]`. Use `congr 1`.

Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem deep_span : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A]
    [IsScalarTower (𝓞 F) F A] (S : Sys F A) (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A']
    (s : Fin S.D → Fin S.N → E) (δ : ℕ) (Φ : S.Flat E A' s δ) (r : ℕ) (bD : Module.Basis (Fin r) F (S.V S.D)),
    Φ.U (S.T - S.D) = Submodule.span E
      (Set.range fun p : MonoDeg (Fin S.D) (S.T - S.D) × Fin r => pw Φ.mul s p.1.1 (Φ.ι (bD p.2))) := by
  intro F A _ _ _ _ _ _ S E A' _ _ _ _ s δ Φ r bD
  rw [Φ.div, span_basis F E A A' Φ.ι (S.V S.D) r bD]
  simp_rw [Submodule.map_span]
  rw [← Submodule.span_iUnion]
  congr 1
  ext x
  simp

/- English proof (translation)
Introduce `F A _ _ _ _ _ _ S hS E A' _ _ _ _ s δ Φ d b c hc`. Establish `hD1` using `hS.one_le`. Establish `hDT` using `hS.le_T`. Use `haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective`. Use `haveI : Infinite E := Infinite.of_injective (Nat.cast : ℕ → E) Nat.cast_injective`.

Take `⟨r0, b0, hb0⟩` from `hS.short0`. Take `⟨rD, bD, hbD⟩` from `hS.shortD`. Take `⟨rT, bT, hbT⟩` from `hS.shortT`. Take `⟨σ0, hσ0⟩` from `GlobalTheory.T.exists_basis_choice_det_ne_zero' F E A A' Φ.ι (S.V 0) r0 δ b0 Φ.res Φ.onto`. Take `⟨l, hl⟩` from `avoid E S.N δ Φ.y Φ.y_ne`.

Establish `hwX : ∀ q : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a), ∃ β : Fin S.T → Fin (S.D + 1), (∀ i : Fin S.D, (Finset.univ.filter fun r => β r = i.castSucc).card = q.2.1 i) ∧ (q.2.1.degree = S.T → ∀ r, β r ≠ Fin.last S.D) ∧ ∀ (M : Type) [Monoid M] (f : Fin (S.D + 1) → M), (List.ofFn f …` using `fun q => GlobalTheory.T.exists_block_word_of_type_prod S.D S.T q.2.1 (by have h1 := q.2.2; have h2 := q.1.2; omega)`. Use `choose βX hβX1 hβX2 hβX3 using hwX`. Establish `hwD : ∀ α : MonoDeg (Fin S.D) (S.T - S.D), ∃ β : Fin (S.T - S.D) → Fin (S.D + 1), (∀ i : Fin S.D, (Finset.univ.filter fun r => β r = i.castSucc).card = α.1 i) ∧ (α.1.degree = S.T - S.D → ∀ r, β r ≠ Fin.last S.D) ∧ ∀ (M : Type) [Monoid M] (f : Fin (S.D + 1) → M), (List.ofFn fun r …` using `fun α => GlobalTheory.T.exists_block_word_of_type_prod S.D (S.T - S.D) α.1 (le_of_eq α.2)`. Use `choose βD hβD1 hβD2 hβD3 using hwD`. Set `s' : Fin S.D → Fin S.N → E` to `fun i k => algebraMap F E (s i k)`.

Set `g : MonoDeg (Fin S.D) (S.T - S.D) × Fin rD → A'` to `fun p => pw Φ.mul s' p.1.1 (Φ.ι (bD p.2))`. Take `⟨hfin, hrank, -⟩` from `GlobalTheory.T.finrank_deepestFiltrationStep_eq_rational F A S hS E A' s δ Φ`. Take `⟨n, σD, hn, hindD⟩` from `pick_indep E A' _ g (Φ.U (S.T - S.D)) (deep_span F A S E A' s' δ Φ rD bD).symm hfin`. Set `X` to `(Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a) × Fin δ`. Set `m : Fin δ → S.V 0` to `fun p => b0 (σ0 p)`.

Set `colX : X → S.Col` to `fun q => ⟨0, S.T, Nat.zero_add _, βX q.1, m q.2⟩`. Set `colD : Fin n → S.Col` to `fun k => ⟨S.D, S.T - S.D, by omega, βD (σD k).1, bD (σD k).2⟩`. Set `d'` to `Fintype.card X + n`. Set `e1 : X ⊕ Fin n ≃ Fin d'` to `(Equiv.sumCongr (Fintype.equivFin X) (Equiv.refl _)).trans finSumFinEquiv`. Set `col' : Fin d' → S.Col` to `fun k => Sum.elim colX colD (e1.symm k)`.

Set `ix' : X ↪ Fin d'` to `⟨fun q => e1 (Sum.inl q), fun a a' h => Sum.inl_injective (e1.injective h)⟩`. Establish `hcolX : ∀ q, col' (ix' q) = colX q` using `fun q => by show Sum.elim colX colD (e1.symm (e1 (Sum.inl q))) = colX q`. Rewrite using `[Equiv.symm_apply_apply]`. Both sides reduce to the same expression. Establish `hcolD : ∀ k, col' (e1 (Sum.inr k)) = colD k` using `fun k => by show Sum.elim colX colD (e1.symm (e1 (Sum.inr k))) = colD k`.

Rewrite using `[Equiv.symm_apply_apply]`. Both sides reduce to the same expression. Establish `hrange : ∀ k, k ∉ Set.range ix' → ∃ k', e1 (Sum.inr k') = k`. Introduce `k hk`. Break down `h : e1.symm k with q | k'` into its components or cases.

Conclude with `absurd ⟨q, show e1 (Sum.inl q) = k by rw [← h, Equiv.apply_symm_apply]⟩ hk`. Conclude with `⟨k', by rw [← h, Equiv.apply_symm_apply]⟩`. Establish `hshape' : S.Shape δ col' m ix'`. Use `⟨fun q => by rw [hcolX], fun q => by rw [hcolX], fun q => ?_, fun k hk => ?_⟩` and prove the remaining obligations. Rewrite using `[hcolX]`.

Conclude with `hβX1 q.1`. Take `⟨k', rfl⟩` from `hrange k hk left`. Rewrite using `[hcolD]`. Conclude with `⟨rfl, hβD2 _ (σD k').1.2⟩`. Set `v : Fin d' → A'` to `fun k => word Φ.mul (fun q j => join s' l ((col' k).β q, j)) (Φ.ι (col' k).x)`.

Take `⟨hsym, hdeepU⟩` from `GlobalTheory.T.symbols_of_evaluated_columns_hermitianMultSystem F A S hS E A' s' δ Φ d' col' m ix' hshape' l`. Establish `hj : ∀ (i : Fin S.D) (j : Fin S.N), join s' l (Fin.castSucc i, j) = s' i j` using `fun i j => by simp [join]`. Establish `hvD : ∀ k', v (e1 (Sum.inr k')) = g (σD k')`. Introduce `k'`. Use `show word Φ.mul (fun q j => join s' l ((col' (e1 (Sum.inr k'))).β q, j)) (Φ.ι (col' (e1 (Sum.inr k'))).x) = _`.

Rewrite using `[hcolD]`. Use `show word Φ.mul (fun q j => join s' l (βD (σD k').1 q, j)) (Φ.ι (bD (σD k').2 : A)) = pw Φ.mul s' (σD k').1.1 (Φ.ι (bD (σD k').2 : A))`. Establish `h3` using `hβD3 (σD k').1 (Module.End E A') (fun x => Φ.mul (fun j => join s' l (x, j)))`. Unfold `word pw`. Rewrite using `[h3, (σD k').1.2, Nat.sub_self, pow_zero, mul_one]`.

Use `congr 3`. Use function extensionality and compare the values at `i`. Use `congr 2`. Use function extensionality and compare the values at `j`. Conclude with `hj i j`.

Set `ix'' : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a × Fin δ) ↪ Fin d'` to `(Equiv.sigmaProdDistrib (fun a : Fin (S.T - S.D) => MonoDeg (Fin S.D) a) (Fin δ)).symm.toEmbedding.trans ix'`. Establish `hv : ∀ q, v (ix'' q) ∈ Φ.U q.1` using `fun q => (hsym q.1 q.2.1 q.2.2).choose`. Set `J : Finset (Fin d')` to `Finset.univ.filter fun k => k ∉ Set.range ix'`. Establish `hJ : ∀ k ∈ J, k ∉ Set.range ix'' ∧ v k ∈ Φ.U (S.T - S.D)`. Introduce `k hk`.

Establish `hk'` using `(Finset.mem_filter.1 hk).2`. Use `⟨fun ⟨q, hq⟩ => hk' ⟨_, hq⟩, hdeepU k hk' ?_⟩` and prove the remaining obligations. Take `⟨k', rfl⟩` from `hrange k hk'`. Rewrite using `[hcolD]`. Establish `hdet : ∀ a : Fin (S.T - S.D), (Matrix.of fun i i' : MonoDeg (Fin S.D) a × Fin δ => Φ.sym a ⟨v (ix'' ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i).det ≠ 0`.

Introduce `a`. Establish `heq : (Matrix.of fun i i' : MonoDeg (Fin S.D) a × Fin δ => Φ.sym a ⟨v (ix'' ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i) = Matrix.of fun i i' : MonoDeg (Fin S.D) a × Fin δ => if i.1 = i'.1 then (∑ k, l k * Φ.y i.2 k) ^ (S.T - a) * (Matrix.of fun p' p => Φ.res (Φ.ι (b0 (σ0 p))) p') i.2 i'.2 else 0`. Use extensionality with `i i'`. Rewrite using `[Matrix.of_apply, Matrix.of_apply]`. Use `((hsym a i'.1 i'.2).choose_spec i.1 i.2).trans ?_` and prove the remaining obligations.

Distinguish the cases in `h : i.1 = i'.1`. Rewrite using `[if_pos (congrArg Subtype.val h), if_pos h]`. Both sides reduce to the same expression. Rewrite using `[if_neg (fun h' => h (Subtype.ext h')), if_neg h]`. Rewrite using `[heq]`.

Conclude with `GlobalTheory.T.det_blockSymbolMatrix_ne_zero' E _ δ _ _ _ hl hσ0`. Establish `hrspec : ∀ k : J, ∃ k', e1 (Sum.inr k') = k.1` using `fun k => hrange k.1 (Finset.mem_filter.1 k.2).2`. Use `choose f hf using hrspec`. Establish `hfinj : Function.Injective f` using `fun k1 k2 h => Subtype.ext (by rw [← hf k1, ← hf k2, h])`. Establish `hJind : LinearIndependent E (fun k : J => v k)`.

Establish `h1` using `hindD.comp f hfinj`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using `only [Function.comp]`. Rewrite using `[← hvD, hf k]`.

Establish `hall` using `GlobalTheory.T.linearIndependent_of_filtration_symbol_det_ne_zero E A' (S.T - S.D) d' (fun a => MonoDeg (Fin S.D) a × Fin δ) Φ.U (fun a => Φ.sym a) (fun a ha => Φ.le a ha) (fun a x => Φ.ker a a.2 x) ix'' J v hv hJ hdet hJind`. Establish `hcover : ∀ k, k ∈ Set.range ix'' ∨ k ∈ J`. Introduce `k`. Distinguish the cases in `hk : k ∈ Set.range ix'`. Take `⟨q, rfl⟩` from `hk left`.

Conclude with `⟨Equiv.sigmaProdDistrib _ _ q, by simp [ix'']⟩`. Use `right`. Conclude with `Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩`. Establish `hind' : LinearIndependent E v` using `hall.comp (fun k => ⟨k, hcover k⟩) (fun a a' h => congrArg Subtype.val h)`. Establish `hw : LinearIndependent E (fun k : Fin rT => Φ.ι (bT k : A))` using `Φ.indep rT (fun k => bT k) bT.linearIndependent`.

Establish `hmemT : ∀ k, v k ∈ Submodule.span E (Set.range fun k : Fin rT => Φ.ι (bT k : A))`. Take `⟨c', -, hc'⟩` from `GlobalTheory.T.hermitianMultiplicationFlat_columns_eval F A S hS E A' s' δ Φ d b c hc`. Introduce `k`. Rewrite using `[← span_basis F E A A' Φ.ι (S.V S.T) rT bT]`. Conclude with `(hc' (col' k) (join s' l)).1`.

Take `⟨K, hK, hindK⟩` from `GlobalTheory.T.exists_independent_completion E A' d' rT v _ hind' hw hmemT`. Establish `hrT : rT = d` using `by simpa using Fintype.card_congr (bT.indexEquiv b)`. Establish `hZ : Fintype.card (Fin d' ⊕ K) = d`. Rewrite using `[Fintype.card_sum, Fintype.card_fin, Fintype.card_coe, hK, hrT]`. Set `e2 : (Fin d' ⊕ K) ≃ Fin d` to `Fintype.equivFinOfCardEq hZ`.

Set `colT : K → S.Col` to `fun k => ⟨S.T, 0, Nat.add_zero _, Fin.elim0, bT k⟩`. Set `col : Fin d → S.Col` to `fun k => Sum.elim col' colT (e2.symm k)`. Set `ix : X ↪ Fin d` to `(ix'.trans (⟨Sum.inl, Sum.inl_injective⟩ : Fin d' ↪ (Fin d' ⊕ K))).trans e2.toEmbedding`. Establish `hcol1 : ∀ k', col (e2 (Sum.inl k')) = col' k'` using `fun k' => by show Sum.elim col' colT (e2.symm (e2 (Sum.inl k'))) = _`. Rewrite using `[Equiv.symm_apply_apply]`.

Both sides reduce to the same expression. Establish `hcol2 : ∀ k', col (e2 (Sum.inr k')) = colT k'` using `fun k' => by show Sum.elim col' colT (e2.symm (e2 (Sum.inr k'))) = _`. Rewrite using `[Equiv.symm_apply_apply]`. Both sides reduce to the same expression. Establish `hcolX' : ∀ q, col' (e1 (Sum.inl q)) = colX q` using `hcolX`.

Establish `hixe : ∀ q, ix q = e2 (Sum.inl (ix' q))` using `fun q => rfl`. Establish `hTD : S.T ≠ S.D` using `by omega`. Establish `hT0 : S.T ≠ 0` using `by omega`. Establish `hD0 : S.D ≠ 0` using `by omega`. Use `⟨col, m, ix, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `⟨fun q => by rw [hixe, hcol1]; exact hshape'.x_j q, fun q => by rw [hixe, hcol1]; exact hshape'.x_vec q, fun q => by rw [hixe, hcol1]; exact hshape'.x_type q, fun k hk => ?_⟩` and prove the remaining obligations. Take `⟨z, rfl⟩` from `e2.surjective k`. Break down `z with k' | k'` into its components or cases. Rewrite using `[hcol1]`. Conclude with `hshape'.rest k' (fun ⟨q, hq⟩ => hk ⟨q, by rw [hixe, hq]⟩)`.

Use `right`. Rewrite using `[hcol2]`. Introduce `k`. Take `⟨z, rfl⟩` from `e2.surjective k`. Break down `z with k' | k'` into its components or cases.

Rewrite using `[hcol1]`. Take `⟨z', rfl⟩` from `e1.surjective k'`. Break down `z' with q | k''` into its components or cases. Rewrite using `[hcolX']`. Use `⟨(hb0 _).1, fun σ => ?_⟩` and prove the remaining obligations.

Use `show _ ≤ if (0 : ℕ) = 0 then S.Lam0 else _`. Rewrite using `[if_pos rfl]`. Conclude with `(hb0 _).2 σ`. Rewrite using `[hcolD]`. Use `⟨(hbD _).1, fun σ => ?_⟩` and prove the remaining obligations.

Use `show _ ≤ if S.D = 0 then S.Lam0 else if S.D = S.D then S.LamD else S.LamT`. Rewrite using `[if_neg hD0, if_pos rfl]`. Conclude with `(hbD _).2 σ`. Rewrite using `[hcol2]`. Use `⟨(hbT _).1, fun σ => ?_⟩` and prove the remaining obligations.

Use `show _ ≤ if S.T = 0 then S.Lam0 else if S.T = S.D then S.LamD else S.LamT`. Rewrite using `[if_neg hT0, if_neg hTD]`. Conclude with `(hbT _).2 σ`. Rewrite using `[← hrank, ← hn, Finset.card_filter, ← e2.sum_comp, Fintype.sum_sum_type]`. Simplify using `only [hcol1, hcol2]`.

Rewrite using `[← e1.sum_comp, Fintype.sum_sum_type]`. Simplify using `only [hcolX', hcolD]`. Simplify using `[colX, colD, colT, hTD, hD0.symm]`. Apply `GlobalTheory.T.det_columns_ne_zero_of_pointValues_independent F A S hS E A' s' δ Φ d b c hc col (join s' l)` to reduce the goal to its premises. Establish `heq : (fun k => word Φ.mul (fun q j => join s' l ((col k).β q, j)) (Φ.ι (col k).x)) = (Sum.elim v fun k : K => Φ.ι (bT k : A)) ∘ e2.symm`.

Use function extensionality and compare the values at `k`. Take `⟨z, rfl⟩` from `e2.surjective k`. Break down `z with k' | k'` into its components or cases. Rewrite using `[Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, hcol1]`. Rewrite using `[Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr, hcol2] show word Φ.mul (fun q j => join s' l ((Fin.elim0 q : Fin (S.D + 1)), j)) (Φ.ι (bT k' : A)) = _`.

Simplify using `[word]`. Rewrite using `[heq]`. Conclude with `hindK.comp _ e2.symm.injective`.
-/
theorem exists_cols : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → F) (δ : ℕ) (Φ : S.Flat E A' (fun i k => algebraMap F E (s i k)) δ) (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∃ (col : Fin d → S.Col) (m : Fin δ → S.V 0) (ix : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a) × Fin δ ↪ Fin d), S.Shape δ col m ix ∧ S.ShortCols col ∧ (Finset.univ.filter fun k => (col k).j = S.D).card = S.deepRank s ∧ S.det c col ≠ 0 := by
  intro F A _ _ _ _ _ _ S hS E A' _ _ _ _ s δ Φ d b c hc
  classical
  have hD1 := hS.one_le
  have hDT := hS.le_T
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  haveI : Infinite E := Infinite.of_injective (Nat.cast : ℕ → E) Nat.cast_injective
  obtain ⟨r0, b0, hb0⟩ := hS.short0
  obtain ⟨rD, bD, hbD⟩ := hS.shortD
  obtain ⟨rT, bT, hbT⟩ := hS.shortT
  obtain ⟨σ0, hσ0⟩ := GlobalTheory.T.exists_basis_choice_det_ne_zero' F E A A' Φ.ι (S.V 0) r0 δ b0 Φ.res Φ.onto
  obtain ⟨l, hl⟩ := avoid E S.N δ Φ.y Φ.y_ne
  have hwX : ∀ q : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a), ∃ β : Fin S.T → Fin (S.D + 1),
      (∀ i : Fin S.D, (Finset.univ.filter fun r => β r = i.castSucc).card = q.2.1 i) ∧
      (q.2.1.degree = S.T → ∀ r, β r ≠ Fin.last S.D) ∧
      ∀ (M : Type) [Monoid M] (f : Fin (S.D + 1) → M), (List.ofFn fun r => f (β r)).prod =
        (List.ofFn fun i : Fin S.D => f i.castSucc ^ q.2.1 i).prod * f (Fin.last S.D) ^ (S.T - q.2.1.degree) :=
    fun q => GlobalTheory.T.exists_block_word_of_type_prod S.D S.T q.2.1 (by have h1 := q.2.2; have h2 := q.1.2; omega)
  choose βX hβX1 hβX2 hβX3 using hwX
  have hwD : ∀ α : MonoDeg (Fin S.D) (S.T - S.D), ∃ β : Fin (S.T - S.D) → Fin (S.D + 1),
      (∀ i : Fin S.D, (Finset.univ.filter fun r => β r = i.castSucc).card = α.1 i) ∧
      (α.1.degree = S.T - S.D → ∀ r, β r ≠ Fin.last S.D) ∧
      ∀ (M : Type) [Monoid M] (f : Fin (S.D + 1) → M), (List.ofFn fun r => f (β r)).prod =
        (List.ofFn fun i : Fin S.D => f i.castSucc ^ α.1 i).prod * f (Fin.last S.D) ^ (S.T - S.D - α.1.degree) :=
    fun α => GlobalTheory.T.exists_block_word_of_type_prod S.D (S.T - S.D) α.1 (le_of_eq α.2)
  choose βD hβD1 hβD2 hβD3 using hwD
  let s' : Fin S.D → Fin S.N → E := fun i k => algebraMap F E (s i k)
  let g : MonoDeg (Fin S.D) (S.T - S.D) × Fin rD → A' := fun p => pw Φ.mul s' p.1.1 (Φ.ι (bD p.2))
  obtain ⟨hfin, hrank, -⟩ := GlobalTheory.T.finrank_deepestFiltrationStep_eq_rational F A S hS E A' s δ Φ
  obtain ⟨n, σD, hn, hindD⟩ := pick_indep E A' _ g (Φ.U (S.T - S.D)) (deep_span F A S E A' s' δ Φ rD bD).symm hfin
  let X := (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a) × Fin δ
  let m : Fin δ → S.V 0 := fun p => b0 (σ0 p)
  let colX : X → S.Col := fun q => ⟨0, S.T, Nat.zero_add _, βX q.1, m q.2⟩
  let colD : Fin n → S.Col := fun k => ⟨S.D, S.T - S.D, by omega, βD (σD k).1, bD (σD k).2⟩
  let d' := Fintype.card X + n
  let e1 : X ⊕ Fin n ≃ Fin d' := (Equiv.sumCongr (Fintype.equivFin X) (Equiv.refl _)).trans finSumFinEquiv
  let col' : Fin d' → S.Col := fun k => Sum.elim colX colD (e1.symm k)
  let ix' : X ↪ Fin d' := ⟨fun q => e1 (Sum.inl q), fun a a' h => Sum.inl_injective (e1.injective h)⟩
  have hcolX : ∀ q, col' (ix' q) = colX q := fun q => by
    show Sum.elim colX colD (e1.symm (e1 (Sum.inl q))) = colX q
    rw [Equiv.symm_apply_apply]; rfl
  have hcolD : ∀ k, col' (e1 (Sum.inr k)) = colD k := fun k => by
    show Sum.elim colX colD (e1.symm (e1 (Sum.inr k))) = colD k
    rw [Equiv.symm_apply_apply]; rfl
  have hrange : ∀ k, k ∉ Set.range ix' → ∃ k', e1 (Sum.inr k') = k := by
    intro k hk
    rcases h : e1.symm k with q | k'
    · exact absurd ⟨q, show e1 (Sum.inl q) = k by rw [← h, Equiv.apply_symm_apply]⟩ hk
    · exact ⟨k', by rw [← h, Equiv.apply_symm_apply]⟩
  have hshape' : S.Shape δ col' m ix' := by
    refine ⟨fun q => by rw [hcolX], fun q => by rw [hcolX], fun q => ?_, fun k hk => ?_⟩
    · rw [hcolX]; exact hβX1 q.1
    · obtain ⟨k', rfl⟩ := hrange k hk
      left
      rw [hcolD]
      exact ⟨rfl, hβD2 _ (σD k').1.2⟩
  let v : Fin d' → A' := fun k => word Φ.mul (fun q j => join s' l ((col' k).β q, j)) (Φ.ι (col' k).x)
  obtain ⟨hsym, hdeepU⟩ := GlobalTheory.T.symbols_of_evaluated_columns_hermitianMultSystem F A S hS E A' s' δ Φ d' col' m ix' hshape' l
  have hj : ∀ (i : Fin S.D) (j : Fin S.N), join s' l (Fin.castSucc i, j) = s' i j := fun i j => by simp [join]
  have hvD : ∀ k', v (e1 (Sum.inr k')) = g (σD k') := by
    intro k'
    show word Φ.mul (fun q j => join s' l ((col' (e1 (Sum.inr k'))).β q, j)) (Φ.ι (col' (e1 (Sum.inr k'))).x) = _
    rw [hcolD]
    show word Φ.mul (fun q j => join s' l (βD (σD k').1 q, j)) (Φ.ι (bD (σD k').2 : A)) =
      pw Φ.mul s' (σD k').1.1 (Φ.ι (bD (σD k').2 : A))
    have h3 := hβD3 (σD k').1 (Module.End E A') (fun x => Φ.mul (fun j => join s' l (x, j)))
    unfold word pw
    rw [h3, (σD k').1.2, Nat.sub_self, pow_zero, mul_one]
    congr 3
    funext i
    congr 2
    funext j
    exact hj i j
  let ix'' : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a × Fin δ) ↪ Fin d' :=
    (Equiv.sigmaProdDistrib (fun a : Fin (S.T - S.D) => MonoDeg (Fin S.D) a) (Fin δ)).symm.toEmbedding.trans ix'
  have hv : ∀ q, v (ix'' q) ∈ Φ.U q.1 := fun q => (hsym q.1 q.2.1 q.2.2).choose
  let J : Finset (Fin d') := Finset.univ.filter fun k => k ∉ Set.range ix'
  have hJ : ∀ k ∈ J, k ∉ Set.range ix'' ∧ v k ∈ Φ.U (S.T - S.D) := by
    intro k hk
    have hk' := (Finset.mem_filter.1 hk).2
    refine ⟨fun ⟨q, hq⟩ => hk' ⟨_, hq⟩, hdeepU k hk' ?_⟩
    obtain ⟨k', rfl⟩ := hrange k hk'
    rw [hcolD]
  have hdet : ∀ a : Fin (S.T - S.D), (Matrix.of fun i i' : MonoDeg (Fin S.D) a × Fin δ =>
      Φ.sym a ⟨v (ix'' ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i).det ≠ 0 := by
    intro a
    have heq : (Matrix.of fun i i' : MonoDeg (Fin S.D) a × Fin δ => Φ.sym a ⟨v (ix'' ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i) =
        Matrix.of fun i i' : MonoDeg (Fin S.D) a × Fin δ => if i.1 = i'.1 then
          (∑ k, l k * Φ.y i.2 k) ^ (S.T - a) * (Matrix.of fun p' p => Φ.res (Φ.ι (b0 (σ0 p))) p') i.2 i'.2 else 0 := by
      ext i i'
      rw [Matrix.of_apply, Matrix.of_apply]
      refine ((hsym a i'.1 i'.2).choose_spec i.1 i.2).trans ?_
      by_cases h : i.1 = i'.1
      · rw [if_pos (congrArg Subtype.val h), if_pos h]; rfl
      · rw [if_neg (fun h' => h (Subtype.ext h')), if_neg h]
    rw [heq]
    exact GlobalTheory.T.det_blockSymbolMatrix_ne_zero' E _ δ _ _ _ hl hσ0
  have hrspec : ∀ k : J, ∃ k', e1 (Sum.inr k') = k.1 := fun k => hrange k.1 (Finset.mem_filter.1 k.2).2
  choose f hf using hrspec
  have hfinj : Function.Injective f := fun k1 k2 h => Subtype.ext (by rw [← hf k1, ← hf k2, h])
  have hJind : LinearIndependent E (fun k : J => v k) := by
    have h1 := hindD.comp f hfinj
    convert h1 using 1
    funext k
    simp only [Function.comp]
    rw [← hvD, hf k]
  have hall := GlobalTheory.T.linearIndependent_of_filtration_symbol_det_ne_zero E A' (S.T - S.D) d' (fun a => MonoDeg (Fin S.D) a × Fin δ) Φ.U (fun a => Φ.sym a)
    (fun a ha => Φ.le a ha) (fun a x => Φ.ker a a.2 x) ix'' J v hv hJ hdet hJind
  have hcover : ∀ k, k ∈ Set.range ix'' ∨ k ∈ J := by
    intro k
    by_cases hk : k ∈ Set.range ix'
    · obtain ⟨q, rfl⟩ := hk
      left
      exact ⟨Equiv.sigmaProdDistrib _ _ q, by simp [ix'']⟩
    · right
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩
  have hind' : LinearIndependent E v :=
    hall.comp (fun k => ⟨k, hcover k⟩) (fun a a' h => congrArg Subtype.val h)
  have hw : LinearIndependent E (fun k : Fin rT => Φ.ι (bT k : A)) := Φ.indep rT (fun k => bT k) bT.linearIndependent
  have hmemT : ∀ k, v k ∈ Submodule.span E (Set.range fun k : Fin rT => Φ.ι (bT k : A)) := by
    obtain ⟨c', -, hc'⟩ := GlobalTheory.T.hermitianMultiplicationFlat_columns_eval F A S hS E A' s' δ Φ d b c hc
    intro k
    rw [← span_basis F E A A' Φ.ι (S.V S.T) rT bT]
    exact (hc' (col' k) (join s' l)).1
  obtain ⟨K, hK, hindK⟩ := GlobalTheory.T.exists_independent_completion E A' d' rT v _ hind' hw hmemT
  have hrT : rT = d := by simpa using Fintype.card_congr (bT.indexEquiv b)
  have hZ : Fintype.card (Fin d' ⊕ K) = d := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe, hK, hrT]
  let e2 : (Fin d' ⊕ K) ≃ Fin d := Fintype.equivFinOfCardEq hZ
  let colT : K → S.Col := fun k => ⟨S.T, 0, Nat.add_zero _, Fin.elim0, bT k⟩
  let col : Fin d → S.Col := fun k => Sum.elim col' colT (e2.symm k)
  let ix : X ↪ Fin d := (ix'.trans (⟨Sum.inl, Sum.inl_injective⟩ : Fin d' ↪ (Fin d' ⊕ K))).trans e2.toEmbedding
  have hcol1 : ∀ k', col (e2 (Sum.inl k')) = col' k' := fun k' => by
    show Sum.elim col' colT (e2.symm (e2 (Sum.inl k'))) = _
    rw [Equiv.symm_apply_apply]; rfl
  have hcol2 : ∀ k', col (e2 (Sum.inr k')) = colT k' := fun k' => by
    show Sum.elim col' colT (e2.symm (e2 (Sum.inr k'))) = _
    rw [Equiv.symm_apply_apply]; rfl
  have hcolX' : ∀ q, col' (e1 (Sum.inl q)) = colX q := hcolX
  have hixe : ∀ q, ix q = e2 (Sum.inl (ix' q)) := fun q => rfl
  have hTD : S.T ≠ S.D := by omega
  have hT0 : S.T ≠ 0 := by omega
  have hD0 : S.D ≠ 0 := by omega
  refine ⟨col, m, ix, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun q => by rw [hixe, hcol1]; exact hshape'.x_j q, fun q => by rw [hixe, hcol1]; exact hshape'.x_vec q,
      fun q => by rw [hixe, hcol1]; exact hshape'.x_type q, fun k hk => ?_⟩
    obtain ⟨z, rfl⟩ := e2.surjective k
    rcases z with k' | k'
    · rw [hcol1]
      exact hshape'.rest k' (fun ⟨q, hq⟩ => hk ⟨q, by rw [hixe, hq]⟩)
    · right; rw [hcol2]
  · intro k
    obtain ⟨z, rfl⟩ := e2.surjective k
    rcases z with k' | k'
    · rw [hcol1]
      obtain ⟨z', rfl⟩ := e1.surjective k'
      rcases z' with q | k''
      · rw [hcolX']
        refine ⟨(hb0 _).1, fun σ => ?_⟩
        show _ ≤ if (0 : ℕ) = 0 then S.Lam0 else _
        rw [if_pos rfl]
        exact (hb0 _).2 σ
      · rw [hcolD]
        refine ⟨(hbD _).1, fun σ => ?_⟩
        show _ ≤ if S.D = 0 then S.Lam0 else if S.D = S.D then S.LamD else S.LamT
        rw [if_neg hD0, if_pos rfl]
        exact (hbD _).2 σ
    · rw [hcol2]
      refine ⟨(hbT _).1, fun σ => ?_⟩
      show _ ≤ if S.T = 0 then S.Lam0 else if S.T = S.D then S.LamD else S.LamT
      rw [if_neg hT0, if_neg hTD]
      exact (hbT _).2 σ
  · rw [← hrank, ← hn, Finset.card_filter, ← e2.sum_comp, Fintype.sum_sum_type]
    simp only [hcol1, hcol2]
    rw [← e1.sum_comp, Fintype.sum_sum_type]
    simp only [hcolX', hcolD]
    simp [colX, colD, colT, hTD, hD0.symm]
  · apply GlobalTheory.T.det_columns_ne_zero_of_pointValues_independent F A S hS E A' s' δ Φ d b c hc col (join s' l)
    have heq : (fun k => word Φ.mul (fun q j => join s' l ((col k).β q, j)) (Φ.ι (col k).x)) =
        (Sum.elim v fun k : K => Φ.ι (bT k : A)) ∘ e2.symm := by
      funext k
      obtain ⟨z, rfl⟩ := e2.surjective k
      rcases z with k' | k'
      · rw [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, hcol1]
      · rw [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr, hcol2]
        show word Φ.mul (fun q j => join s' l ((Fin.elim0 q : Fin (S.D + 1)), j)) (Φ.ι (bT k' : A)) = _
        simp [word]
    rw [heq]
    exact hindK.comp _ e2.symm.injective

end GlobalTheory.HSShort.ChooseCols
