import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientJacquetModuleRefineTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientRelativeJacquetBlockLevi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeJacquetPiExteriorTensorEquivNormalized
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PiExteriorTensorFlattenedIndexEquivNested
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetModuleInStagesRefinedBlocks
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinSigmaFinEquivSymmStrictMonoToLex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityJacquetEqBorelJacquetOfS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspProdCharTransport

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg GlobalTheory.JacStages GlobalTheory.JacStagesExact

namespace GlobalTheory.CompanionTheory.JmTrans

section Index

variable {s N : ℕ}

/- English proof (translation)
Rewrite using `[Finset.sum_range]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rw [dif_pos (lt_of_lt_of_le b.2 ha)] <;> rfl`.
-/
private theorem sum_castLE_lemma {s : ℕ} (d : Fin s → ℕ) (a : ℕ) (ha : a ≤ s) :
    ∑ b : Fin a, d (Fin.castLE ha b) = ∑ i ∈ Finset.range a, (if h : i < s then d ⟨i, h⟩ else 0) := by
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [dif_pos (lt_of_lt_of_le b.2 ha)] <;> rfl

/- English proof (translation)
Rewrite using `[sum_castLE_lemma d (a : ℕ) a.2.le, sum_castLE_lemma d (b : ℕ) b.2.le]`. Establish `e : (∑ i ∈ Finset.range a, (if h : i < s then d ⟨i, h⟩ else 0)) + d a = ∑ i ∈ Finset.range (a + 1), (if h : i < s then d ⟨i, h⟩ else 0)`. Rewrite using `[Finset.sum_range_succ, dif_pos a.2]`. Rewrite using `[e]`. Conclude with `Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_of_lt hab))`.
-/
private theorem sum_castLE_add_le_lemma_2 {s : ℕ} (d : Fin s → ℕ) {a b : Fin s} (hab : a < b) :
    ∑ c : Fin a, d (Fin.castLE a.2.le c) + d a ≤ ∑ c : Fin b, d (Fin.castLE b.2.le c) := by
  rw [sum_castLE_lemma d (a : ℕ) a.2.le, sum_castLE_lemma d (b : ℕ) b.2.le]
  have e : (∑ i ∈ Finset.range a, (if h : i < s then d ⟨i, h⟩ else 0)) + d a =
      ∑ i ∈ Finset.range (a + 1), (if h : i < s then d ⟨i, h⟩ else 0) := by
    rw [Finset.sum_range_succ, dif_pos a.2]
  rw [e]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_of_lt hab))

/- English proof (translation)
Establish `h' : Sigma.Lex (· < ·) (fun _ => (· < ·)) p q` using `hpq`. Take `⟨a, i⟩` from `p`. Take `⟨b, j⟩` from `q`. Rewrite using `[Fin.lt_def, stdBlocks_val, stdBlocks_val]`. Break down `Sigma.lex_iff.1 h' with hab | ⟨hab, hij⟩` into its components or cases.

Simplify using `only at hab`. Establish `key` using `sum_castLE_add_le_lemma_2 d hab`. Establish `hi` using `i.2`. Use linear arithmetic over natural numbers and integers. Simplify using `only at hab hij`.

Substitute `hab` using the available equality. Establish `hij' : (i : ℕ) < j` using `hij`. Use linear arithmetic over natural numbers and integers.
-/
theorem stdBlocks_lt (d : Fin s → ℕ) (h : ∑ a, d a = N) {p q : Σ a, Fin (d a)} (hpq : toLex p < toLex q) :
    stdBlocks d h p < stdBlocks d h q := by
  have h' : Sigma.Lex (· < ·) (fun _ => (· < ·)) p q := hpq
  obtain ⟨a, i⟩ := p
  obtain ⟨b, j⟩ := q
  rw [Fin.lt_def, stdBlocks_val, stdBlocks_val]
  rcases Sigma.lex_iff.1 h' with hab | ⟨hab, hij⟩
  · dsimp only at hab
    have key := sum_castLE_add_le_lemma_2 d hab
    have hi := i.2
    omega
  · dsimp only at hab hij
    subst hab
    have hij' : (i : ℕ) < j := hij
    omega

variable {y : Fin s → ℕ} {c : Fin s → ℕ} {x : ∀ a, Fin (c a) → ℕ}

/- English proof (translation)
Apply `stdBlocks_lt` to reduce the goal to its premises. Establish `h' : Sigma.Lex (· < ·) (fun _ => (· < ·)) p q` using `h`. Take `⟨a, u⟩` from `p`. Take `⟨b, v⟩` from `q`. Break down `Sigma.lex_iff.1 h' with hab | ⟨hab, huv⟩` into its components or cases.

Conclude with `Sigma.Lex.left _ _ hab`. Simplify using `only at hab huv`. Substitute `hab` using the available equality. Conclude with `Sigma.Lex.right _ _ (stdBlocks_lt _ _ (Sigma.Lex.left _ _ huv))`.
-/
theorem place_lt (hy : ∑ a, y a = N) (hx : ∀ a, ∑ i, x a i = y a) (p q : Σ a, Fin (c a))
    (i : Fin (x p.1 p.2)) (j : Fin (x q.1 q.2)) (h : toLex p < toLex q) :
    stdBlocks y hy ⟨p.1, stdBlocks (x p.1) (hx p.1) ⟨p.2, i⟩⟩ <
      stdBlocks y hy ⟨q.1, stdBlocks (x q.1) (hx q.1) ⟨q.2, j⟩⟩ := by
  apply stdBlocks_lt
  have h' : Sigma.Lex (· < ·) (fun _ => (· < ·)) p q := h
  obtain ⟨a, u⟩ := p
  obtain ⟨b, v⟩ := q
  rcases Sigma.lex_iff.1 h' with hab | ⟨hab, huv⟩
  · exact Sigma.Lex.left _ _ hab
  · dsimp only at hab huv
    subst hab
    exact Sigma.Lex.right _ _ (stdBlocks_lt _ _ (Sigma.Lex.left _ _ huv))

/- English proof (translation)
Break down `lt_trichotomy (toLex (finSigmaFinEquiv.symm l)) (toLex (finSigmaFinEquiv.symm l')) with h1 | h1 | h1` into its components or cases. Conclude with `h1`. Conclude with `absurd h (by rw [finSigmaFinEquiv.symm.injective (toLex.injective h1)]; exact lt_irrefl l')`. Establish `h2` using `stdBlocks_lt c rfl h1`. Simplify using `only [stdBlocks, Equiv.trans_apply, Equiv.apply_symm_apply, finCongr_apply, Fin.cast_eq_self] at h2`.

Conclude with `absurd h2 (lt_asymm h)`.
-/
private theorem finSigmaFinEquiv_symm_lt_lemma_3 {s : ℕ} {c : Fin s → ℕ} {l l' : Fin (∑ a, c a)} (h : l < l') :
    toLex (finSigmaFinEquiv.symm l) < toLex (finSigmaFinEquiv.symm l') := by
  rcases lt_trichotomy (toLex (finSigmaFinEquiv.symm l)) (toLex (finSigmaFinEquiv.symm l')) with h1 | h1 | h1
  · exact h1
  · exact absurd h (by rw [finSigmaFinEquiv.symm.injective (toLex.injective h1)]; exact lt_irrefl l')
  · have h2 := stdBlocks_lt c rfl h1
    simp only [stdBlocks, Equiv.trans_apply, Equiv.apply_symm_apply, finCongr_apply, Fin.cast_eq_self] at h2
    exact absurd h2 (lt_asymm h)

/- English proof (translation)
Establish `h' : Sigma.Lex (· < ·) (fun _ => (· < ·)) p q` using `h`. Take `⟨l, i⟩` from `p`. Take `⟨l', j⟩` from `q`. Rewrite using `[refinePlace_apply, refinePlace_apply]`. Break down `Sigma.lex_iff.1 h' with hl | ⟨hl, hij⟩` into its components or cases.

Conclude with `place_lt hy hx (finSigmaFinEquiv.symm l) (finSigmaFinEquiv.symm l') i j (finSigmaFinEquiv_symm_lt_lemma_3 hl)`. Simplify using `only at hl hij`. Substitute `hl` using the available equality. Conclude with `stdBlocks_lt _ _ (Sigma.Lex.right _ _ (stdBlocks_lt _ _ (Sigma.Lex.right _ _ hij)))`.
-/
theorem refinePlace_lt (hy : ∑ a, y a = N) (hx : ∀ a, ∑ i, x a i = y a)
    {p q : Σ l : Fin (∑ a, c a), Fin (x (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2)}
    (h : toLex p < toLex q) :
    refinePlace (stdBlocks y hy) (fun a => stdBlocks (x a) (hx a)) p <
      refinePlace (stdBlocks y hy) (fun a => stdBlocks (x a) (hx a)) q := by
  have h' : Sigma.Lex (· < ·) (fun _ => (· < ·)) p q := h
  obtain ⟨l, i⟩ := p
  obtain ⟨l', j⟩ := q
  rw [refinePlace_apply, refinePlace_apply]
  rcases Sigma.lex_iff.1 h' with hl | ⟨hl, hij⟩
  · exact place_lt hy hx (finSigmaFinEquiv.symm l) (finSigmaFinEquiv.symm l') i j
      (finSigmaFinEquiv_symm_lt_lemma_3 hl)
  · dsimp only at hl hij
    subst hl
    exact stdBlocks_lt _ _ (Sigma.Lex.right _ _ (stdBlocks_lt _ _ (Sigma.Lex.right _ _ hij)))

/- English proof (translation)
Establish `hmono : StrictMono (fun u => f (g.symm u))`. Introduce `u v huv`. Apply `hf` to reduce the goal to its premises. Break down `lt_trichotomy (toLex (g.symm u)) (toLex (g.symm v)) with h1 | h1 | h1` into its components or cases. Conclude with `h1`.

Conclude with `absurd huv (by rw [g.symm.injective (toLex.injective h1)]; exact lt_irrefl v)`. Establish `h2` using `hg _ _ h1`. Rewrite `h2` using `[Equiv.apply_symm_apply, Equiv.apply_symm_apply]`. Conclude with `absurd h2 (lt_asymm huv)`. Establish `heq : (fun u => f (g.symm u)) = id` using `(StrictMono.range_inj hmono strictMono_id).1 (by`.

Rewrite using `[Set.range_id]`. Conclude with `Set.range_eq_univ.2 fun u => ⟨g (f.symm u), by simp⟩)`. Use `Equiv.ext fun p => ?_` and prove the remaining obligations. Establish `h3` using `congrFun heq (g p)`. Simplify using `using h3`.
-/
private theorem eq_of_lexMono_lemma_4 {s : ℕ} {D : Fin s → ℕ} {N : ℕ} (f g : (Σ a, Fin (D a)) ≃ Fin N)
    (hf : ∀ p q, toLex p < toLex q → f p < f q) (hg : ∀ p q, toLex p < toLex q → g p < g q) : f = g := by
  have hmono : StrictMono (fun u => f (g.symm u)) := by
    intro u v huv
    apply hf
    rcases lt_trichotomy (toLex (g.symm u)) (toLex (g.symm v)) with h1 | h1 | h1
    · exact h1
    · exact absurd huv (by rw [g.symm.injective (toLex.injective h1)]; exact lt_irrefl v)
    · have h2 := hg _ _ h1
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h2
      exact absurd h2 (lt_asymm huv)
  have heq : (fun u => f (g.symm u)) = id :=
    (StrictMono.range_inj hmono strictMono_id).1 (by
      rw [Set.range_id]
      exact Set.range_eq_univ.2 fun u => ⟨g (f.symm u), by simp⟩)
  refine Equiv.ext fun p => ?_
  have h3 := congrFun heq (g p)
  simpa using h3

/- English proof (translation)
Conclude with `eq_of_lexMono_lemma_4 _ _ (fun _ _ h => refinePlace_lt hy hx h) (fun _ _ h => stdBlocks_lt _ hcat h)`.
-/
theorem refinePlace_stdBlocks (hy : ∑ a, y a = N) (hx : ∀ a, ∑ i, x a i = y a)
    (hcat : ∑ l : Fin (∑ a, c a), x (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2 = N) :
    refinePlace (stdBlocks y hy) (fun a => stdBlocks (x a) (hx a)) =
      stdBlocks (fun l => x (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2) hcat := by
  exact eq_of_lexMono_lemma_4 _ _ (fun _ _ h => refinePlace_lt hy hx h) (fun _ _ h => stdBlocks_lt _ hcat h)

end Index

section Exact

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {s : ℕ} {d : Fin s → ℕ} {t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}
  {U V W Y : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Y] [Module ℂ Y]

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨n, y, rfl⟩`. Take `⟨x, rfl⟩` from `hp y`. Use `⟨ρ (n : G) x - (((1 : N →* ℂˣ) n : ℂˣ) : ℂ) • x, Submodule.subset_span ⟨n, x, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hi : p.toLinearMap (ρ (n : G) x) = τ (n : G) (p x)` using `LinearMap.congr_fun (p.isIntertwining' (n : G)) x`.

Rewrite using `[map_sub, map_smul, hi]`. Both sides reduce to the same expression.
-/
private theorem twKer_le_map_lemma_5 {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {τ : Representation ℂ G W} (p : ρ.IntertwiningMap τ)
    (hp : Function.Surjective p) (N : Subgroup G) :
    GlobalTheory.PRep.twKer τ N 1 ≤ (GlobalTheory.PRep.twKer ρ N 1).map p.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨n, y, rfl⟩
  obtain ⟨x, rfl⟩ := hp y
  refine ⟨ρ (n : G) x - (((1 : N →* ℂˣ) n : ℂˣ) : ℂ) • x, Submodule.subset_span ⟨n, x, rfl⟩, ?_⟩
  have hi : p.toLinearMap (ρ (n : G) x) = τ (n : G) (p x) := LinearMap.congr_fun (p.isIntertwining' (n : G)) x
  rw [map_sub, map_smul, hi]
  rfl

/- English proof (translation)
Use `GlobalTheory.JHMult.jhMult_exact (GlobalTheory.JacStagesExact.relJacMap e' ι) (GlobalTheory.JacStagesExact.relJacMap e' p) hσ (GlobalTheory.JacStagesExact.relJacMap_injective e' hρ ι hι) (GlobalTheory.JacStagesExact.relJacMap_surjective e' p hp) ?_ ?_` and prove the remaining obligations. Introduce `u`. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ u`. Use `show (Submodule.Quotient.mk (p (ι v)) : Y ⧸ GlobalTheory.PRep.twKer ρ₂ (GlobalTheory.JacStages.relUnipD k e') 1) = 0`. Rewrite using `[he.apply_apply_eq_zero, Submodule.Quotient.mk_zero]`.

Introduce `u hu`. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ u`. Establish `h0 : (Submodule.Quotient.mk (p v) : Y ⧸ GlobalTheory.PRep.twKer ρ₂ (GlobalTheory.JacStages.relUnipD k e') 1) = 0` using `hu`. Establish `h1 : p v ∈ GlobalTheory.PRep.twKer ρ₂ (GlobalTheory.JacStages.relUnipD k e') 1` using `(Submodule.Quotient.mk_eq_zero _).1 h0`. Take `⟨w, hw, hpw⟩` from `twKer_le_map_lemma_5 p hp _ h1`.

Establish `h2 : p (v - w) = 0`. Establish `h3 : p.toLinearMap (v - w) = 0`. Rewrite using `[map_sub, hpw]`. Conclude with `sub_self _`. Conclude with `h3`.

Take `⟨u₁, hu₁⟩` from `(he (v - w)).1 h2`. Use `⟨Submodule.Quotient.mk u₁, ?_⟩` and prove the remaining obligations. Use `show (Submodule.Quotient.mk (ι u₁) : V ⧸ GlobalTheory.PRep.twKer ρ (GlobalTheory.JacStages.relUnipD k e') 1) = Submodule.Quotient.mk v`. Rewrite using `[hu₁, Submodule.Quotient.eq]`. Establish `h4 : v - w - v = -w` using `by abel`.

Rewrite using `[h4]`. Conclude with `Submodule.neg_mem _ hw`.
-/
theorem jhMult_relJacD_exact (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    {σ : Representation ℂ (∀ a, Levi k fun b => Fin (d' a b)) U} (hσ : σ.IsIrreducible)
    {ρ : Representation ℂ (Levi k fun a => Fin (d a)) V} {ρ₁ : Representation ℂ (Levi k fun a => Fin (d a)) W}
    {ρ₂ : Representation ℂ (Levi k fun a => Fin (d a)) Y} (ι : ρ₁.IntertwiningMap ρ) (p : ρ.IntertwiningMap ρ₂)
    (hρ : IsSmooth ρ) (hι : Function.Injective ι) (hp : Function.Surjective p) (he : Function.Exact ι p) :
    jhMult σ (relJacD e' ρ) = jhMult σ (relJacD e' ρ₁) + jhMult σ (relJacD e' ρ₂) := by
  classical
  refine GlobalTheory.JHMult.jhMult_exact (GlobalTheory.JacStagesExact.relJacMap e' ι) (GlobalTheory.JacStagesExact.relJacMap e' p) hσ
    (GlobalTheory.JacStagesExact.relJacMap_injective e' hρ ι hι) (GlobalTheory.JacStagesExact.relJacMap_surjective e' p hp) ?_ ?_
  · intro u
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    show (Submodule.Quotient.mk (p (ι v)) : Y ⧸ GlobalTheory.PRep.twKer ρ₂ (GlobalTheory.JacStages.relUnipD k e') 1) = 0
    rw [he.apply_apply_eq_zero, Submodule.Quotient.mk_zero]
  · intro u hu
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    have h0 : (Submodule.Quotient.mk (p v) : Y ⧸ GlobalTheory.PRep.twKer ρ₂ (GlobalTheory.JacStages.relUnipD k e') 1) = 0 := hu
    have h1 : p v ∈ GlobalTheory.PRep.twKer ρ₂ (GlobalTheory.JacStages.relUnipD k e') 1 := (Submodule.Quotient.mk_eq_zero _).1 h0
    obtain ⟨w, hw, hpw⟩ := twKer_le_map_lemma_5 p hp _ h1
    have h2 : p (v - w) = 0 := by
      have h3 : p.toLinearMap (v - w) = 0 := by
        rw [map_sub, hpw]
        exact sub_self _
      exact h3
    obtain ⟨u₁, hu₁⟩ := (he (v - w)).1 h2
    refine ⟨Submodule.Quotient.mk u₁, ?_⟩
    show (Submodule.Quotient.mk (ι u₁) : V ⧸ GlobalTheory.PRep.twKer ρ (GlobalTheory.JacStages.relUnipD k e') 1) =
      Submodule.Quotient.mk v
    rw [hu₁, Submodule.Quotient.eq]
    have h4 : v - w - v = -w := by abel
    rw [h4]
    exact Submodule.neg_mem _ hw

/- English proof (translation)
Introduce `v`. Establish `h : {g | S.toRepresentation g v = v} = {g | ρ g (v : V₀) = v}`. Use extensionality with `g`. Conclude with `Subtype.ext_iff`. Rewrite using `[h]`.

Conclude with `hρ v`.
-/
private theorem isSmooth_sub_lemma_6 {G V₀ : Type} [Group G] [TopologicalSpace G] [AddCommGroup V₀] [Module ℂ V₀]
    {ρ : Representation ℂ G V₀} (hρ : IsSmooth ρ) (S : Subrepresentation ρ) : IsSmooth S.toRepresentation := by
  intro v
  have h : {g | S.toRepresentation g v = v} = {g | ρ g (v : V₀) = v} := by
    ext g
    exact Subtype.ext_iff
  rw [h]
  exact hρ v

/- English proof (translation)
Introduce `x`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `g0 hg0`. Establish `hU : IsOpen {g | B.toRepresentation g y = y}` using `isSmooth_sub_lemma_6 hρ B y`.

Establish `hc : Continuous fun g : G => g0⁻¹ * g` using `continuous_const.mul continuous_id`. Establish `hmem : g0 ∈ (fun g : G => g0⁻¹ * g) ⁻¹' {g | B.toRepresentation g y = y}` using `by show B.toRepresentation (g0⁻¹ * g0) y = y`. Rewrite using `[inv_mul_cancel, map_one]`. Both sides reduce to the same expression. Use `Filter.mem_of_superset ((hU.preimage hc).mem_nhds hmem) ?_` and prove the remaining obligations.

Introduce `g hg`. Establish `hg' : B.toRepresentation (g0⁻¹ * g) y = y` using `hg`. Establish `e2 : subQuot B A (g0⁻¹ * g) (Submodule.Quotient.mk y) = Submodule.Quotient.mk y` using `by show Submodule.Quotient.mk (B.toRepresentation (g0⁻¹ * g) y) = _`. Rewrite using `[hg']`. Use `show subQuot B A g (Submodule.Quotient.mk y) = Submodule.Quotient.mk y`.

Rewrite using `[show g = g0 * (g0⁻¹ * g) by group, map_mul]`. Use `show subQuot B A g0 (subQuot B A (g0⁻¹ * g) (Submodule.Quotient.mk y)) = Submodule.Quotient.mk y`. Rewrite using `[e2]`. Conclude with `hg0`.
-/
private theorem isSmooth_subQuot_lemma_7 {G V₀ : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
    [AddCommGroup V₀] [Module ℂ V₀] {ρ : Representation ℂ G V₀} (hρ : IsSmooth ρ) (B A : Subrepresentation ρ) :
    IsSmooth (subQuot B A) := by
  intro x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [isOpen_iff_mem_nhds]
  intro g0 hg0
  have hU : IsOpen {g | B.toRepresentation g y = y} := isSmooth_sub_lemma_6 hρ B y
  have hc : Continuous fun g : G => g0⁻¹ * g := continuous_const.mul continuous_id
  have hmem : g0 ∈ (fun g : G => g0⁻¹ * g) ⁻¹' {g | B.toRepresentation g y = y} := by
    show B.toRepresentation (g0⁻¹ * g0) y = y
    rw [inv_mul_cancel, map_one]
    rfl
  refine Filter.mem_of_superset ((hU.preimage hc).mem_nhds hmem) ?_
  intro g hg
  have hg' : B.toRepresentation (g0⁻¹ * g) y = y := hg
  have e2 : subQuot B A (g0⁻¹ * g) (Submodule.Quotient.mk y) = Submodule.Quotient.mk y := by
    show Submodule.Quotient.mk (B.toRepresentation (g0⁻¹ * g) y) = _
    rw [hg']
  show subQuot B A g (Submodule.Quotient.mk y) = Submodule.Quotient.mk y
  rw [show g = g0 * (g0⁻¹ * g) by group, map_mul]
  show subQuot B A g0 (subQuot B A (g0⁻¹ * g) (Submodule.Quotient.mk y)) = Submodule.Quotient.mk y
  rw [e2]
  exact hg0

/- English proof (translation)
Use `jhMult_relJacD_exact e' hσ (⟨Submodule.inclusion h, fun g => LinearMap.ext fun x => rfl⟩ : A.toRepresentation.IntertwiningMap B.toRepresentation) (⟨(Submodule.comap B.toSubmodule.subtype A.toSubmodule).mkQ, fun g => LinearMap.ext fun x => rfl⟩ : B.toRepresentation.IntertwiningMap …` and prove the remaining obligations. Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Establish `hy' : (Submodule.Quotient.mk y : ↥B.toSubmodule ⧸ Submodule.comap B.toSubmodule.subtype A.toSubmodule) = 0` using `hy`.

Conclude with `⟨⟨(y : V), (Submodule.Quotient.mk_eq_zero (Submodule.comap B.toSubmodule.subtype A.toSubmodule)).1 hy'⟩, rfl⟩`. Introduce and unpack `⟨x, rfl⟩`. Conclude with `(Submodule.Quotient.mk_eq_zero (Submodule.comap B.toSubmodule.subtype A.toSubmodule)).2 x.2`.
-/
private theorem jhMult_relJacD_le_add_lemma_8 (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    {σ : Representation ℂ (∀ a, Levi k fun b => Fin (d' a b)) U} (hσ : σ.IsIrreducible)
    {ρ : Representation ℂ (Levi k fun a => Fin (d a)) V} (hρ : IsSmooth ρ) {A B : Subrepresentation ρ} (h : A ≤ B) :
    jhMult σ (relJacD e' B.toRepresentation) =
      jhMult σ (relJacD e' A.toRepresentation) + jhMult σ (relJacD e' (subQuot B A)) := by
  refine jhMult_relJacD_exact e' hσ
    (⟨Submodule.inclusion h, fun g => LinearMap.ext fun x => rfl⟩ :
      A.toRepresentation.IntertwiningMap B.toRepresentation)
    (⟨(Submodule.comap B.toSubmodule.subtype A.toSubmodule).mkQ, fun g => LinearMap.ext fun x => rfl⟩ :
      B.toRepresentation.IntertwiningMap (subQuot B A))
    (isSmooth_sub_lemma_6 hρ B) (Submodule.inclusion_injective h) (Submodule.mkQ_surjective _) ?_
  intro y
  constructor
  · intro hy
    have hy' : (Submodule.Quotient.mk y :
        ↥B.toSubmodule ⧸ Submodule.comap B.toSubmodule.subtype A.toSubmodule) = 0 := hy
    exact ⟨⟨(y : V), (Submodule.Quotient.mk_eq_zero (Submodule.comap B.toSubmodule.subtype A.toSubmodule)).1 hy'⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero (Submodule.comap B.toSubmodule.subtype A.toSubmodule)).2 x.2

/- English proof (translation)
Establish `htop : ∀ S : Subrepresentation ρ, jhMult σ (relJacD e' S.toRepresentation) ≤ jhMult σ (relJacD e' ρ)`. Introduce `S`. Conclude with `GlobalTheory.CompanionTheory.SocleJm.jhMult_le_of_injective hσ (GlobalTheory.JacStagesExact.relJacMap e' (⟨S.toSubmodule.subtype, fun g => LinearMap.ext fun x => rfl⟩ : S.toRepresentation.IntertwiningMap ρ)) (GlobalTheory.JacStagesExact.relJacMap_injective e' hρ _ Subtype.val_inj …`. Establish `hτ1 : 1 ≤ jhMult σ (relJacD e' τ)` using `Order.one_le_iff_ne_zero.2 (GlobalTheory.JHMult.jhMult_ne_zero_iff.2 hτ)`. Establish `hone : ∀ {S T : Subrepresentation ρ}, Nonempty ((subQuot S T).Equiv τ) → 1 ≤ jhMult σ (relJacD e' (subQuot S T))`.

Introduce `S T hφ`. Take `⟨φ⟩` from `hφ`. Establish `hinj : Function.Injective φ.symm.toIntertwiningMap`. Introduce `a b hab`. Establish `h' : φ (φ.symm a) = φ (φ.symm b)` using `congrArg φ hab`.

Rewrite `h'` using `[φ.apply_symm_apply, φ.apply_symm_apply]`. Then use the resulting hypothesis. Conclude with `hτ1.trans (GlobalTheory.CompanionTheory.SocleJm.jhMult_le_of_injective hσ (GlobalTheory.JacStagesExact.relJacMap e' φ.symm.toIntertwiningMap) (GlobalTheory.JacStagesExact.relJacMap_injective e' (isSmooth_subQuot_lemma_7 hρ S T) _ hinj))`. Use `show (⨆ r, ⨆ (_ : OccursTimes τ ρ r), (r : ℕ∞)) ≤ _`. Use `iSup₂_le fun r hr => ?_` and prove the remaining obligations. Take `⟨S, T, hTS, hST, hiso⟩` from `hr`.

Establish `key : ∀ n (hn : n < r), ((n + 1 : ℕ) : ℕ∞) ≤ jhMult σ (relJacD e' (S ⟨n, hn⟩).toRepresentation)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `hn`.

Rewrite using `[jhMult_relJacD_le_add_lemma_8 e' hσ hρ (hTS ⟨0, hn⟩)]`. Simplify using `using (hone (hiso ⟨0, hn⟩)).trans le_add_self`. Consider the case `succ n ih`. Introduce `hn`. Establish `h1` using `ih (Nat.lt_of_succ_lt hn)`.

Establish `hle : S ⟨n, Nat.lt_of_succ_lt hn⟩ ≤ T ⟨n + 1, hn⟩` using `hST _ _ (by simp [Fin.lt_def])`. Establish `hmono : jhMult σ (relJacD e' (S ⟨n, Nat.lt_of_succ_lt hn⟩).toRepresentation) ≤ jhMult σ (relJacD e' (T ⟨n + 1, hn⟩).toRepresentation)`. Rewrite using `[jhMult_relJacD_le_add_lemma_8 e' hσ hρ hle]`. Conclude with `le_self_add`. Rewrite using `[jhMult_relJacD_le_add_lemma_8 e' hσ hρ (hTS ⟨n + 1, hn⟩)]`.

Establish `h2` using `add_le_add (h1.trans hmono) (hone (hiso ⟨n + 1, hn⟩))`. Conclude with `le_trans (le_of_eq (Nat.cast_succ (n + 1))) h2`. Break down `Nat.eq_zero_or_pos r with hr0 | hr0` into its components or cases. Substitute `hr0` using the available equality. Simplify using the standard rewrite rules.

Take `⟨n, rfl⟩ : ∃ n, r = n + 1` from `⟨r - 1, by omega⟩`. Conclude with `(key n (Nat.lt_succ_self n)).trans (htop _)`.
-/
theorem jhMult_le_relJacD (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    {σ : Representation ℂ (∀ a, Levi k fun b => Fin (d' a b)) U} (hσ : σ.IsIrreducible)
    {τ : Representation ℂ (Levi k fun a => Fin (d a)) W} {ρ : Representation ℂ (Levi k fun a => Fin (d a)) V}
    (hρ : IsSmooth ρ) (hτ : IsSubquotient σ (relJacD e' τ)) :
    jhMult τ ρ ≤ jhMult σ (relJacD e' ρ) := by
  classical
  have htop : ∀ S : Subrepresentation ρ,
      jhMult σ (relJacD e' S.toRepresentation) ≤ jhMult σ (relJacD e' ρ) := by
    intro S
    exact GlobalTheory.CompanionTheory.SocleJm.jhMult_le_of_injective hσ
      (GlobalTheory.JacStagesExact.relJacMap e' (⟨S.toSubmodule.subtype, fun g => LinearMap.ext fun x => rfl⟩ :
        S.toRepresentation.IntertwiningMap ρ))
      (GlobalTheory.JacStagesExact.relJacMap_injective e' hρ _ Subtype.val_injective)
  have hτ1 : 1 ≤ jhMult σ (relJacD e' τ) :=
    Order.one_le_iff_ne_zero.2 (GlobalTheory.JHMult.jhMult_ne_zero_iff.2 hτ)
  have hone : ∀ {S T : Subrepresentation ρ}, Nonempty ((subQuot S T).Equiv τ) →
      1 ≤ jhMult σ (relJacD e' (subQuot S T)) := by
    intro S T hφ
    obtain ⟨φ⟩ := hφ
    have hinj : Function.Injective φ.symm.toIntertwiningMap := by
      intro a b hab
      have h' : φ (φ.symm a) = φ (φ.symm b) := congrArg φ hab
      rwa [φ.apply_symm_apply, φ.apply_symm_apply] at h'
    exact hτ1.trans (GlobalTheory.CompanionTheory.SocleJm.jhMult_le_of_injective hσ
      (GlobalTheory.JacStagesExact.relJacMap e' φ.symm.toIntertwiningMap)
      (GlobalTheory.JacStagesExact.relJacMap_injective e' (isSmooth_subQuot_lemma_7 hρ S T) _ hinj))
  show (⨆ r, ⨆ (_ : OccursTimes τ ρ r), (r : ℕ∞)) ≤ _
  refine iSup₂_le fun r hr => ?_
  obtain ⟨S, T, hTS, hST, hiso⟩ := hr
  have key : ∀ n (hn : n < r),
      ((n + 1 : ℕ) : ℕ∞) ≤ jhMult σ (relJacD e' (S ⟨n, hn⟩).toRepresentation) := by
    intro n
    induction n with
    | zero =>
      intro hn
      rw [jhMult_relJacD_le_add_lemma_8 e' hσ hρ (hTS ⟨0, hn⟩)]
      simpa using (hone (hiso ⟨0, hn⟩)).trans le_add_self
    | succ n ih =>
      intro hn
      have h1 := ih (Nat.lt_of_succ_lt hn)
      have hle : S ⟨n, Nat.lt_of_succ_lt hn⟩ ≤ T ⟨n + 1, hn⟩ := hST _ _ (by simp [Fin.lt_def])
      have hmono : jhMult σ (relJacD e' (S ⟨n, Nat.lt_of_succ_lt hn⟩).toRepresentation) ≤
          jhMult σ (relJacD e' (T ⟨n + 1, hn⟩).toRepresentation) := by
        rw [jhMult_relJacD_le_add_lemma_8 e' hσ hρ hle]
        exact le_self_add
      rw [jhMult_relJacD_le_add_lemma_8 e' hσ hρ (hTS ⟨n + 1, hn⟩)]
      have h2 := add_le_add (h1.trans hmono) (hone (hiso ⟨n + 1, hn⟩))
      exact le_trans (le_of_eq (Nat.cast_succ (n + 1))) h2
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · subst hr0
    simp
  · obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
    exact (key n (Nat.lt_succ_self n)).trans (htop _)

end Exact

/- English proof (translation)
Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]`. Introduce and unpack `_ ⟨z, rfl⟩`. Use `choose w hw using fun a => hf a (z a)`. Use `⟨PiTensorProduct.tprod ℂ w, ?_⟩` and prove the remaining obligations. Rewrite using `[PiTensorProduct.map_tprod]`.

Use `congr 1`. Use function extensionality and compare the values at `a`. Conclude with `hw a`.
-/
private theorem map_surjective_lemma_9 {ι : Type} {M₀ N₀ : ι → Type} [∀ a, AddCommGroup (M₀ a)]
    [∀ a, Module ℂ (M₀ a)] [∀ a, AddCommGroup (N₀ a)] [∀ a, Module ℂ (N₀ a)] (f : ∀ a, M₀ a →ₗ[ℂ] N₀ a)
    (hf : ∀ a, Function.Surjective (f a)) : Function.Surjective (PiTensorProduct.map f) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨z, rfl⟩
  choose w hw using fun a => hf a (z a)
  refine ⟨PiTensorProduct.tprod ℂ w, ?_⟩
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext a
  exact hw a

/- English proof (translation)
Use `choose S f hf using h`. Establish `hL : ∀ a, ∃ L : Y₀ a →ₗ[ℂ] ↥(S a).toSubmodule, L ∘ₗ (S a).toSubmodule.subtype = LinearMap.id` using `fun a => LinearMap.exists_leftInverse_of_injective _ (Submodule.ker_subtype _)`. Use `choose L hL using hL`. Establish `key : ∀ g : ∀ a, Γ a, piTensor ρ g ∘ₗ PiTensorProduct.map (fun a => (S a).toSubmodule.subtype) = PiTensorProduct.map (fun a => (S a).toSubmodule.subtype) ∘ₗ piTensor (fun a => (S a).toRepresentation) g`. Introduce `g`.

Use `show PiTensorProduct.map (fun a => ρ a (g a)) ∘ₗ PiTensorProduct.map (fun a => (S a).toSubmodule.subtype) = PiTensorProduct.map (fun a => (S a).toSubmodule.subtype) ∘ₗ PiTensorProduct.map (fun a => (S a).toRepresentation (g a))`. Rewrite using `[← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]`. Both sides reduce to the same expression. Establish `hΦ : PiTensorProduct.map (fun a => (f a).toLinearMap ∘ₗ L a) ∘ₗ PiTensorProduct.map (fun a => (S a).toSubmodule.subtype) = PiTensorProduct.map fun a => (f a).toLinearMap`. Rewrite using `[← PiTensorProduct.map_comp]`.

Use `congr 1`. Use function extensionality and compare the values at `a`. Rewrite using `[LinearMap.comp_assoc, hL a, LinearMap.comp_id]`. Establish `hf' : ∀ g : ∀ a, Γ a, PiTensorProduct.map (fun a => (f a).toLinearMap) ∘ₗ piTensor (fun a => (S a).toRepresentation) g = piTensor σ g ∘ₗ PiTensorProduct.map (fun a => (f a).toLinearMap)`. Introduce `g`.

Use `show PiTensorProduct.map (fun a => (f a).toLinearMap) ∘ₗ PiTensorProduct.map (fun a => (S a).toRepresentation (g a)) = PiTensorProduct.map (fun a => σ a (g a)) ∘ₗ PiTensorProduct.map (fun a => (f a).toLinearMap)`. Rewrite using `[← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Conclude with `(f a).isIntertwining' (g a)`.

Set `M : Subrepresentation (piTensor ρ)` to `⟨LinearMap.range (PiTensorProduct.map fun a => (S a).toSubmodule.subtype), by`. Introduce and unpack `g _ ⟨t, rfl⟩`. Conclude with `⟨piTensor (fun a => (S a).toRepresentation) g t, (LinearMap.congr_fun (key g) t).symm⟩⟩`. Use `⟨M, ⟨PiTensorProduct.map (fun a => (f a).toLinearMap ∘ₗ L a) ∘ₗ M.toSubmodule.subtype, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `g`.

Use `LinearMap.ext fun m => ?_` and prove the remaining obligations. Take `⟨v, t, rfl⟩` from `m`. Use `show PiTensorProduct.map (fun a => (f a).toLinearMap ∘ₗ L a) (piTensor ρ g (PiTensorProduct.map (fun a => (S a).toSubmodule.subtype) t)) = piTensor σ g (PiTensorProduct.map (fun a => (f a).toLinearMap ∘ₗ L a) (PiTensorProduct.map (fun a => (S a).toSubmodule.subtype) t))`. Establish `e1 : piTensor ρ g (PiTensorProduct.map (fun a => (S a).toSubmodule.subtype) t) = PiTensorProduct.map (fun a => (S a).toSubmodule.subtype) (piTensor (fun a => (S a).toRepresentation) g t)` using `LinearMap.congr_fun (key g) t`. Establish `e2 : ∀ u, PiTensorProduct.map (fun a => (f a).toLinearMap ∘ₗ L a) (PiTensorProduct.map (fun a => (S a).toSubmodule.subtype) u) = PiTensorProduct.map (fun a => (f a).toLinearMap) u` using `fun u => LinearMap.congr_fun hΦ u`.

Establish `e3 : PiTensorProduct.map (fun a => (f a).toLinearMap) (piTensor (fun a => (S a).toRepresentation) g t) = piTensor σ g (PiTensorProduct.map (fun a => (f a).toLinearMap) t)` using `LinearMap.congr_fun (hf' g) t`. Rewrite using `[e1, e2, e2]`. Conclude with `e3`. Introduce `z`. Take `⟨t, ht⟩` from `map_surjective_lemma_9 (fun a => (f a).toLinearMap) (fun a => hf a) z`.

Use `⟨⟨PiTensorProduct.map (fun a => (S a).toSubmodule.subtype) t, t, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show PiTensorProduct.map (fun a => (f a).toLinearMap ∘ₗ L a) (PiTensorProduct.map (fun a => (S a).toSubmodule.subtype) t) = z`. Establish `e2 : PiTensorProduct.map (fun a => (f a).toLinearMap ∘ₗ L a) (PiTensorProduct.map (fun a => (S a).toSubmodule.subtype) t) = PiTensorProduct.map (fun a => (f a).toLinearMap) t` using `LinearMap.congr_fun hΦ t`. Rewrite using `[e2]`. Conclude with `ht`.
-/
private theorem isSubquotient_piTensor_lemma_10 {ι : Type} {Γ Y₀ Z₀ : ι → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (Y₀ a)] [∀ a, Module ℂ (Y₀ a)] [∀ a, AddCommGroup (Z₀ a)] [∀ a, Module ℂ (Z₀ a)]
    {σ : ∀ a, Representation ℂ (Γ a) (Z₀ a)} {ρ : ∀ a, Representation ℂ (Γ a) (Y₀ a)}
    (h : ∀ a, IsSubquotient (σ a) (ρ a)) : IsSubquotient (piTensor σ) (piTensor ρ) := by
  classical
  choose S f hf using h
  have hL : ∀ a, ∃ L : Y₀ a →ₗ[ℂ] ↥(S a).toSubmodule, L ∘ₗ (S a).toSubmodule.subtype = LinearMap.id :=
    fun a => LinearMap.exists_leftInverse_of_injective _ (Submodule.ker_subtype _)
  choose L hL using hL
  have key : ∀ g : ∀ a, Γ a, piTensor ρ g ∘ₗ PiTensorProduct.map (fun a => (S a).toSubmodule.subtype) =
      PiTensorProduct.map (fun a => (S a).toSubmodule.subtype) ∘ₗ
        piTensor (fun a => (S a).toRepresentation) g := by
    intro g
    show PiTensorProduct.map (fun a => ρ a (g a)) ∘ₗ PiTensorProduct.map (fun a => (S a).toSubmodule.subtype) =
      PiTensorProduct.map (fun a => (S a).toSubmodule.subtype) ∘ₗ
        PiTensorProduct.map (fun a => (S a).toRepresentation (g a))
    rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
    rfl
  have hΦ : PiTensorProduct.map (fun a => (f a).toLinearMap ∘ₗ L a) ∘ₗ
      PiTensorProduct.map (fun a => (S a).toSubmodule.subtype) =
        PiTensorProduct.map fun a => (f a).toLinearMap := by
    rw [← PiTensorProduct.map_comp]
    congr 1
    funext a
    rw [LinearMap.comp_assoc, hL a, LinearMap.comp_id]
  have hf' : ∀ g : ∀ a, Γ a, PiTensorProduct.map (fun a => (f a).toLinearMap) ∘ₗ
      piTensor (fun a => (S a).toRepresentation) g =
        piTensor σ g ∘ₗ PiTensorProduct.map (fun a => (f a).toLinearMap) := by
    intro g
    show PiTensorProduct.map (fun a => (f a).toLinearMap) ∘ₗ
        PiTensorProduct.map (fun a => (S a).toRepresentation (g a)) =
      PiTensorProduct.map (fun a => σ a (g a)) ∘ₗ PiTensorProduct.map (fun a => (f a).toLinearMap)
    rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
    congr 1
    funext a
    exact (f a).isIntertwining' (g a)
  let M : Subrepresentation (piTensor ρ) :=
    ⟨LinearMap.range (PiTensorProduct.map fun a => (S a).toSubmodule.subtype), by
      rintro g _ ⟨t, rfl⟩
      exact ⟨piTensor (fun a => (S a).toRepresentation) g t, (LinearMap.congr_fun (key g) t).symm⟩⟩
  refine ⟨M, ⟨PiTensorProduct.map (fun a => (f a).toLinearMap ∘ₗ L a) ∘ₗ M.toSubmodule.subtype, ?_⟩, ?_⟩
  · intro g
    refine LinearMap.ext fun m => ?_
    obtain ⟨v, t, rfl⟩ := m
    show PiTensorProduct.map (fun a => (f a).toLinearMap ∘ₗ L a)
        (piTensor ρ g (PiTensorProduct.map (fun a => (S a).toSubmodule.subtype) t)) =
      piTensor σ g (PiTensorProduct.map (fun a => (f a).toLinearMap ∘ₗ L a)
        (PiTensorProduct.map (fun a => (S a).toSubmodule.subtype) t))
    have e1 : piTensor ρ g (PiTensorProduct.map (fun a => (S a).toSubmodule.subtype) t) =
        PiTensorProduct.map (fun a => (S a).toSubmodule.subtype)
          (piTensor (fun a => (S a).toRepresentation) g t) := LinearMap.congr_fun (key g) t
    have e2 : ∀ u, PiTensorProduct.map (fun a => (f a).toLinearMap ∘ₗ L a)
        (PiTensorProduct.map (fun a => (S a).toSubmodule.subtype) u) =
          PiTensorProduct.map (fun a => (f a).toLinearMap) u := fun u => LinearMap.congr_fun hΦ u
    have e3 : PiTensorProduct.map (fun a => (f a).toLinearMap) (piTensor (fun a => (S a).toRepresentation) g t) =
        piTensor σ g (PiTensorProduct.map (fun a => (f a).toLinearMap) t) := LinearMap.congr_fun (hf' g) t
    rw [e1, e2, e2]
    exact e3
  · intro z
    obtain ⟨t, ht⟩ := map_surjective_lemma_9 (fun a => (f a).toLinearMap) (fun a => hf a) z
    refine ⟨⟨PiTensorProduct.map (fun a => (S a).toSubmodule.subtype) t, t, rfl⟩, ?_⟩
    show PiTensorProduct.map (fun a => (f a).toLinearMap ∘ₗ L a)
        (PiTensorProduct.map (fun a => (S a).toSubmodule.subtype) t) = z
    have e2 : PiTensorProduct.map (fun a => (f a).toLinearMap ∘ₗ L a)
        (PiTensorProduct.map (fun a => (S a).toSubmodule.subtype) t) =
          PiTensorProduct.map (fun a => (f a).toLinearMap) t := LinearMap.congr_fun hΦ t
    rw [e2]
    exact ht

/- English proof (translation)
Introduce `k _ _ _ _ hA s N y hy c x hx hcat hpos V _ _ π hs _`. Set `e` to `stdBlocks (fun a => (y a).1) hy`. Set `e' : ∀ a, (Σ i, Fin ((x a i).1)) ≃ Fin ((y a).1)` to `fun a => stdBlocks (fun i => (x a i).1) (hx a)`. Establish `hcat' : ∑ l : Fin (∑ a, c a), (x (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2).1 = N` using `hcat`. Establish `hE : refinePlace e e' = stdBlocks (fun l => (x (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2).1) hcat'` using `refinePlace_stdBlocks (y := fun a => (y a).1) (x := fun a i => (x a i).1) hy hx hcat'`.

Establish `hσ : Representation.IsIrreducible ((piTensor fun l => (x (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2).rep).comp (GlobalTheory.JacStages.flatHom fun a b => GL (Fin (x a b).1) k))` using `GlobalTheory.FinGL.Transport.isIrreducible_comp (piTensor fun l => (x (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2).rep) (GlobalTheory.JacStages.flatHom fun a b => GL (Fin (x a b).1) k) (GlobalTheory.JacStages.flatHom_surjective (fun a b => GL (Fin (x a b).1) k)) (Glob …`. Establish `hρ : IsSmooth (jac e π)` using `GlobalTheory.SmGL.isSmooth_jac e hs`. Establish `hτ : IsSubquotient ((piTensor fun l => (x (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2).rep).comp (GlobalTheory.JacStages.flatHom fun a b => GL (Fin (x a b).1) k)) (relJacD e' (piTensor fun a => (y a).rep))`. Take `⟨φ1⟩` from `GlobalTheory.JacStages.piTensor_flatHom_equiv s c _ _ (fun a b => (x a b).rep)`. Take `⟨φ2⟩` from `GlobalTheory.JacStages.relJacD_piTensor_equiv k s (fun a => (y a).1) c (fun a b => (x a b).1) e' _ (fun a => (y a).rep)`.

Use `GlobalTheory.JHMult.jhMult_ne_zero_iff.1 ?_` and prove the remaining obligations. Use `((GlobalTheory.SmGL.jhMult_congr_left φ1 _).trans (GlobalTheory.SmGL.jhMult_congr_right _ φ2)).trans_ne ?_` and prove the remaining obligations. Use `GlobalTheory.JHMult.jhMult_ne_zero_iff.2 (isSubquotient_piTensor_lemma_10 fun a => ?_)` and prove the remaining obligations. Use `GlobalTheory.JHMult.jhMult_ne_zero_iff.1 ?_` and prove the remaining obligations. Conclude with `Order.one_le_iff_ne_zero.1 (hpos a)`.

Take `⟨φ3⟩` from `GlobalTheory.JacStagesProof.jac_refinePlace_equiv k s N (fun a => (y a).1) e c (fun a b => (x a b).1) e' V π`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hE]`. Both sides reduce to the same expression.
-/
theorem jm_le_jm_concat : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {s N : ℕ} (y : Fin s → IrrGL k) (hy : ∑ a, (y a).1 = N) (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL k) (hx : ∀ a, ∑ i, (x a i).1 = (y a).1) (hcat : ∑ i, (concat c x i).1 = N) (hpos : ∀ a, 1 ≤ jm (x a) (hx a) (y a).rep) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hfl : HasFiniteLength π), jm y hy π ≤ jm (concat c x) hcat π := by
  intro k _ _ _ _ hA s N y hy c x hx hcat hpos V _ _ π hs _
  classical
  let e := stdBlocks (fun a => (y a).1) hy
  let e' : ∀ a, (Σ i, Fin ((x a i).1)) ≃ Fin ((y a).1) := fun a => stdBlocks (fun i => (x a i).1) (hx a)
  have hcat' : ∑ l : Fin (∑ a, c a), (x (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2).1 = N := hcat
  have hE : refinePlace e e' =
      stdBlocks (fun l => (x (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2).1) hcat' :=
    refinePlace_stdBlocks (y := fun a => (y a).1) (x := fun a i => (x a i).1) hy hx hcat'
  have hσ : Representation.IsIrreducible
      ((piTensor fun l => (x (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2).rep).comp
        (GlobalTheory.JacStages.flatHom fun a b => GL (Fin (x a b).1) k)) :=
    GlobalTheory.FinGL.Transport.isIrreducible_comp
      (piTensor fun l => (x (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2).rep)
      (GlobalTheory.JacStages.flatHom fun a b => GL (Fin (x a b).1) k)
      (GlobalTheory.JacStages.flatHom_surjective (fun a b => GL (Fin (x a b).1) k))
      (GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA (concat c x))
  have hρ : IsSmooth (jac e π) := GlobalTheory.SmGL.isSmooth_jac e hs
  have hτ : IsSubquotient
      ((piTensor fun l => (x (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2).rep).comp
        (GlobalTheory.JacStages.flatHom fun a b => GL (Fin (x a b).1) k))
      (relJacD e' (piTensor fun a => (y a).rep)) := by
    obtain ⟨φ1⟩ := GlobalTheory.JacStages.piTensor_flatHom_equiv s c _ _ (fun a b => (x a b).rep)
    obtain ⟨φ2⟩ := GlobalTheory.JacStages.relJacD_piTensor_equiv k s (fun a => (y a).1) c (fun a b => (x a b).1) e' _
      (fun a => (y a).rep)
    refine GlobalTheory.JHMult.jhMult_ne_zero_iff.1 ?_
    refine ((GlobalTheory.SmGL.jhMult_congr_left φ1 _).trans (GlobalTheory.SmGL.jhMult_congr_right _ φ2)).trans_ne ?_
    refine GlobalTheory.JHMult.jhMult_ne_zero_iff.2 (isSubquotient_piTensor_lemma_10 fun a => ?_)
    refine GlobalTheory.JHMult.jhMult_ne_zero_iff.1 ?_
    exact Order.one_le_iff_ne_zero.1 (hpos a)
  obtain ⟨φ3⟩ := GlobalTheory.JacStagesProof.jac_refinePlace_equiv k s N (fun a => (y a).1) e c (fun a b => (x a b).1) e' V π
  calc Zc.jm y hy π = jhMult (piTensor fun a => (y a).rep) (jac e π) := rfl
    _ ≤ jhMult ((piTensor fun l => (x (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2).rep).comp
          (GlobalTheory.JacStages.flatHom fun a b => GL (Fin (x a b).1) k)) (relJacD e' (jac e π)) :=
        jhMult_le_relJacD e' hσ hρ hτ
    _ = jhMult ((piTensor fun l => (x (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2).rep).comp
          (GlobalTheory.JacStages.flatHom fun a b => GL (Fin (x a b).1) k))
          ((jac (refinePlace e e') π).comp (GlobalTheory.JacStages.flatHom fun a b => GL (Fin (x a b).1) k)) :=
        (GlobalTheory.SmGL.jhMult_congr_right _ φ3).symm
    _ = jhMult (piTensor fun l => (x (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2).rep)
          (jac (refinePlace e e') π) :=
        GlobalTheory.SmGL.EmptyBlocks.jhMult_comp_surjective _ (GlobalTheory.JacStages.flatHom_surjective _) _ _
    _ = Zc.jm (concat c x) hcat π := by
        rw [hE]
        rfl

end GlobalTheory.CompanionTheory.JmTrans

end
