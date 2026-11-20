import Formalism.SharpRestriction.GrowthBounds.ObjSeg
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
import Formalism.SharpRestriction.GrowthBounds.GLWeightTheory
import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition
import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeMapFractionField
import Formalism.SharpRestriction.GrowthBounds.FlipOneThree
import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.G.PolBridge

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory

variable {K : Type} [Field K] [CharZero K] {N r : ℕ} [NeZero r]

/- English proof (translation)
Simplify using `only [chWt, wtS]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases h : (i : ℕ) < j <;> simp [h]`.
-/
theorem chWt_eq (LL : ChainLetters N) (j : ℕ) (c : Fin r) (m : Fin N × Fin r →₀ ℕ) :
    chWt LL j c m = wtS (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} m c := by
  simp only [chWt, wtS]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (i : ℕ) < j <;> simp [h]

/- English proof (translation)
Establish `hpow : ∀ (c d : Fin r) (k : ℕ), ∀ x ∈ W, ((glAct K Lt S c d : Module.End K _) ^ k) x ∈ W`. Introduce `c d k`. Proceed by induction on `k with`. Consider the case `zero => intro x hx`. Simplify using `using hx`.

Consider the case `succ k ih => intro x hx`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Conclude with `hW c d _ (ih x hx)`. Introduce and unpack `g (⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩) x hx`. Rewrite using `[← dividedPower_formula_char_zero K (Fin N) Lt r S a b k hab]`.

Unfold `divPowE`. Rewrite using `[LinearMap.smul_apply]`. Conclude with `W.smul_mem _ (hpow a b k x hx)`. Rewrite using `[← binomial_formula_char_zero K (Fin N) Lt r S a k]`. Unfold `binomE`.

Rewrite using `[LinearMap.smul_apply]`. Use `W.smul_mem _ ?_` and prove the remaining obligations. Proceed by induction on `(List.range k) generalizing x with`. Consider the case `nil => simpa using hx`. Consider the case `cons i l ih`.

Rewrite using `[List.map_cons, List.prod_cons, Module.End.mul_apply]`. Use `ih x hx` as an intermediate fact. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]`. Conclude with `W.sub_mem (hW a a _ this) (W.smul_mem _ this)`.
-/
theorem uz_of_stable (Lt : Letters (Fin N)) (S : Set (Fin N)) (W : Submodule K (MvPolynomial (Fin N × Fin r) K))
    (hW : ∀ c d : Fin r, ∀ x ∈ W, glAct K Lt S c d x ∈ W) :
    ∀ g ∈ polUZgens K Lt S, ∀ x ∈ W, g x ∈ W := by
  have hpow : ∀ (c d : Fin r) (k : ℕ), ∀ x ∈ W, ((glAct K Lt S c d : Module.End K _) ^ k) x ∈ W := by
    intro c d k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih => intro x hx; rw [pow_succ', Module.End.mul_apply]; exact hW c d _ (ih x hx)
  rintro g (⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩) x hx
  · rw [← dividedPower_formula_char_zero K (Fin N) Lt r S a b k hab]
    unfold divPowE
    rw [LinearMap.smul_apply]
    exact W.smul_mem _ (hpow a b k x hx)
  · rw [← binomial_formula_char_zero K (Fin N) Lt r S a k]
    unfold binomE
    rw [LinearMap.smul_apply]
    refine W.smul_mem _ ?_
    induction (List.range k) generalizing x with
    | nil => simpa using hx
    | cons i l ih =>
      rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
      have := ih x hx
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact W.sub_mem (hW a a _ this) (W.smul_mem _ this)

/- English proof (translation)
Unfold `YCond`. Conclude with `sSup_le fun S hS => hS.1`.
-/
theorem ycond_le (LL : ChainLetters N) (j : ℕ) (M : WithTop ℤ) :
    YCond K (r := r) LL j M ≤ MvPolynomial.restrictSupport K {m | ((chWt LL j 0 m : ℤ) : WithTop ℤ) ≤ M} := by
  unfold YCond
  exact sSup_le fun S hS => hS.1

/- English proof (translation)
Unfold `chStable`. Introduce `c d x hx`. Establish `key : YCond K (r` using `r) LL j M ≤ (YCond K (r := r) LL j M).comap (glAct K (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} c d) := by`. Unfold `YCond`. Use `sSup_le fun T hT y hy => ?_` and prove the remaining obligations.

Conclude with `Submodule.mem_comap.2 (le_sSup hT (hT.2 c d y hy))`. Conclude with `key hx`.
-/
theorem ycond_stable (LL : ChainLetters N) (j : ℕ) (M : WithTop ℤ) :
    chStable K LL j (YCond K (r := r) LL j M) := by
  unfold chStable
  intro c d x hx
  have key : YCond K (r := r) LL j M ≤
      (YCond K (r := r) LL j M).comap
        (glAct K (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} c d) := by
    unfold YCond
    refine sSup_le fun T hT y hy => ?_
    exact Submodule.mem_comap.2 (le_sSup hT (hT.2 c d y hy))
  exact key hx

/- English proof (translation)
Distinguish the cases in `hcd : c = d`. Substitute `hcd right` using the available equality. Use `⟨c, 1, ?_⟩` and prove the remaining obligations. Rewrite using `[← binomial_formula_char_zero K (Fin N) Lt r S c 1]`. Unfold `binomE`.

Use extensionality with `x`. Simplify using `[glOps]`. Use `left`. Use `⟨c, d, 1, hcd, ?_⟩` and prove the remaining obligations. Use `glAct_pow_eq_factorial_divPow (R := K) (n := r) Lt S c d hcd 1` as an intermediate fact.

Simplify using `using this`.
-/
theorem glAct_mem_gens (Lt : Letters (Fin N)) (S : Set (Fin N)) (c d : Fin r) :
    glAct K Lt S c d ∈ polUZgens K Lt S := by
  by_cases hcd : c = d
  · subst hcd
    right
    refine ⟨c, 1, ?_⟩
    rw [← binomial_formula_char_zero K (Fin N) Lt r S c 1]
    unfold binomE
    ext x
    simp [glOps]
  · left
    refine ⟨c, d, 1, hcd, ?_⟩
    have := glAct_pow_eq_factorial_divPow (R := K) (n := r) Lt S c d hcd 1
    simpa using this

/- English proof (translation)
Establish `huz` using `uz_of_stable (K := K) (r := r) (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} _ (ycond_stable (K := K) (r := r) LL j M)`. Rewrite using `[polGenSub, Submodule.span_le]`. Introduce and unpack `x ⟨u, hu, rfl⟩`. It suffices to establish `h : ∀ y ∈ YCond K (r` using `r) LL j M, u y ∈ YCond K (r := r) LL j M from h G hG`. Proceed by induction on `hu using Submonoid.closure_induction with`.

Consider the case `mem g hg => exact huz g hg`. Consider the case `one => intro y hy`. Simplify using `using hy`. Consider the case `mul u v _ _ hu hv => intro y hy`. Conclude with `hu _ (hv y hy)`.
-/
theorem polGen_le_ycond (LL : ChainLetters N) (j : ℕ) (M : WithTop ℤ) (G : MvPolynomial (Fin N × Fin r) K)
    (hG : G ∈ YCond K (r := r) LL j M) :
    polGenSub K (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} G ≤ YCond K (r := r) LL j M := by
  have huz := uz_of_stable (K := K) (r := r) (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} _
    (ycond_stable (K := K) (r := r) LL j M)
  rw [polGenSub, Submodule.span_le]
  rintro x ⟨u, hu, rfl⟩
  suffices h : ∀ y ∈ YCond K (r := r) LL j M, u y ∈ YCond K (r := r) LL j M from h G hG
  induction hu using Submonoid.closure_induction with
  | mem g hg => exact huz g hg
  | one => intro y hy; simpa using hy
  | mul u v _ _ hu hv => intro y hy; exact hu _ (hv y hy)

/- English proof (translation)
Establish `hV` using `(valuationsAdditive_D7 D K (Fin N) (⟨LL.vec⟩ : Letters (Fin N)) r {i : Fin N | (i : ℕ) < j}).2.2.2.2.2 G M`. Rewrite using `[hV]`. Prove the components needed by the constructor for the conclusion. Introduce `hG mu hmu`. Take `⟨x, hx, hx0, hxw⟩` from `hmu`.

Establish `hxY` using `polGen_le_ycond LL j (M : WithTop ℤ) G hG hx`. Establish `hxR` using `ycond_le (K := K) (r := r) LL j (M : WithTop ℤ) hxY`. Rewrite `hxR` using `[MvPolynomial.mem_restrictSupport_iff]`. Establish `hne : x.support.Nonempty`. Rewrite using `[Finset.nonempty_iff_ne_empty]`.

Introduce `h`. Conclude with `hx0 (MvPolynomial.support_eq_empty.1 h)`. Take `⟨m, hm⟩` from `hne`. Establish `h1` using `hxR hm`. Simplify using `only [Set.mem_setOf_eq] at h1`.

Rewrite using `[← hxw m hm, ← chWt_eq]`. Conclude with `h1` after adjusting the coercions. Introduce `hw set W := polGenSub K (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} G with hWdef`. Establish `hgen : ∀ g ∈ polUZgens K (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j}, ∀ x ∈ W, g x ∈ W` using `fun g hg => generated_submodule_stable _ _ G g hg`. Establish `hR : W ≤ MvPolynomial.restrictSupport K {m | ((chWt LL j 0 m : ℤ) : WithTop ℤ) ≤ (M : WithTop ℤ)}`.

Introduce `x hx`. Rewrite using `[MvPolynomial.mem_restrictSupport_iff]`. Introduce `m hm`. Establish `hxL : x ∈ scalarExtension (RingHom.id K) W` using `Submodule.subset_span ⟨x, hx, MvPolynomial.map_id x⟩`. Establish `hmu` using `scalarExtension_monomial_weights (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} (RingHom.id K) W binomial_stable_contains_components (fun a k y hy => hgen _ (Or.inr ⟨a, k, rfl⟩) y hy) x hxL m hm`.

Use `hw _ hmu` as an intermediate fact. Simplify using `only [Set.mem_setOf_eq]`. Rewrite using `[chWt_eq]`. Conclude with `this` after adjusting the coercions. Establish `hS : chStable K LL j W` using `fun c d x hx => hgen _ (glAct_mem_gens _ _ c d) x hx`.

Conclude with `le_sSup (show W ∈ {S | S ≤ _ ∧ chStable K LL j S} from ⟨hR, hS⟩) (self_mem_generated_submodule _ _ G)`.
-/
theorem mem_ycond_iff (D : Formalism.BasicNotions.D7) (LL : ChainLetters N) (j : ℕ) (M : ℤ) (G : MvPolynomial (Fin N × Fin r) K) :
    G ∈ YCond K (r := r) LL j (M : WithTop ℤ) ↔
      lam1S (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} G ≤ (M : WithBot ℤ) := by
  classical
  have hV := (valuationsAdditive_D7 D K (Fin N) (⟨LL.vec⟩ : Letters (Fin N)) r {i : Fin N | (i : ℕ) < j}).2.2.2.2.2 G M
  rw [hV]
  constructor
  · intro hG mu hmu
    obtain ⟨x, hx, hx0, hxw⟩ := hmu
    have hxY := polGen_le_ycond LL j (M : WithTop ℤ) G hG hx
    have hxR := ycond_le (K := K) (r := r) LL j (M : WithTop ℤ) hxY
    rw [MvPolynomial.mem_restrictSupport_iff] at hxR
    have hne : x.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro h; exact hx0 (MvPolynomial.support_eq_empty.1 h)
    obtain ⟨m, hm⟩ := hne
    have h1 := hxR hm
    simp only [Set.mem_setOf_eq] at h1
    rw [← hxw m hm, ← chWt_eq]
    exact_mod_cast h1
  · intro hw
    set W := polGenSub K (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} G with hWdef
    have hgen : ∀ g ∈ polUZgens K (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j}, ∀ x ∈ W, g x ∈ W :=
      fun g hg => generated_submodule_stable _ _ G g hg
    have hR : W ≤ MvPolynomial.restrictSupport K {m | ((chWt LL j 0 m : ℤ) : WithTop ℤ) ≤ (M : WithTop ℤ)} := by
      intro x hx
      rw [MvPolynomial.mem_restrictSupport_iff]
      intro m hm
      have hxL : x ∈ scalarExtension (RingHom.id K) W :=
        Submodule.subset_span ⟨x, hx, MvPolynomial.map_id x⟩
      have hmu := scalarExtension_monomial_weights (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} (RingHom.id K) W binomial_stable_contains_components
        (fun a k y hy => hgen _ (Or.inr ⟨a, k, rfl⟩) y hy) x hxL m hm
      have := hw _ hmu
      simp only [Set.mem_setOf_eq]
      rw [chWt_eq]
      exact_mod_cast this
    have hS : chStable K LL j W := fun c d x hx => hgen _ (glAct_mem_gens _ _ c d) x hx
    exact le_sSup (show W ∈ {S | S ≤ _ ∧ chStable K LL j S} from ⟨hR, hS⟩) (self_mem_generated_submodule _ _ G)

/- English proof (translation)
Take `⟨T, hTfin, hvT, hTst⟩` from `polynomial_locally_finite K (Fin N) Lt r S v`. Establish `hst : ∀ a b, ∀ x ∈ T, glOps K r Lt S a b x ∈ T` using `hTst`. Establish `hres` using `subrep_restriction_of_reducibility (complete_reducibility_of_semisimple D h2) K _ r (glOps K r Lt S) (Formalism.MainNotions.G.Joints.isGLRep_glOps K (Fin N) Lt r S) T hst`. Establish `: FiniteDimensional K T` using `hTfin`. Use `highest_weight_dominant_holds K T r (restrictStableOperators _ T hst) hres.1 mu ⟨v, hvT⟩ ⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `h`. Conclude with `hv.1 (congrArg Subtype.val h)`. Conclude with `(hres.2.1 mu ⟨v, hvT⟩).2 hv.2.1`. Introduce `a b hab`. Conclude with `Subtype.ext (hv.2.2 a b hab)`.
-/
theorem hwv_dominant (D : Formalism.BasicNotions.D7) (h2 : Formalism.MainNotions.CovariantDegrees.adm2 D) (Lt : Letters (Fin N)) (S : Set (Fin N))
    (mu : Fin r → ℤ) (v : MvPolynomial (Fin N × Fin r) K) (hv : IsHWV (glOps K r Lt S) mu v) : Dominant mu := by
  obtain ⟨T, hTfin, hvT, hTst⟩ := polynomial_locally_finite K (Fin N) Lt r S v
  have hst : ∀ a b, ∀ x ∈ T, glOps K r Lt S a b x ∈ T := hTst
  have hres := subrep_restriction_of_reducibility (complete_reducibility_of_semisimple D h2) K _ r (glOps K r Lt S)
    (Formalism.MainNotions.G.Joints.isGLRep_glOps K (Fin N) Lt r S) T hst
  have : FiniteDimensional K T := hTfin
  refine highest_weight_dominant_holds K T r (restrictStableOperators _ T hst) hres.1 mu ⟨v, hvT⟩ ⟨?_, ?_, ?_⟩
  · intro h; exact hv.1 (congrArg Subtype.val h)
  · exact (hres.2.1 mu ⟨v, hvT⟩).2 hv.2.1
  · intro a b hab; exact Subtype.ext (hv.2.2 a b hab)

/- English proof (translation)
Rewrite using `[isoSub, Submodule.span_eq_bot]`. Introduce and unpack `x ⟨u, _, v, hv, rfl⟩`. Conclude with `absurd (hwv_dominant D h2 Lt S mu v hv) hmu`.
-/
theorem isoSub_eq_bot (D : Formalism.BasicNotions.D7) (h2 : Formalism.MainNotions.CovariantDegrees.adm2 D) (Lt : Letters (Fin N)) (S : Set (Fin N))
    (mu : Fin r → ℤ) (hmu : ¬ Dominant mu) : isoSub (glOps K r Lt S) mu = ⊥ := by
  rw [isoSub, Submodule.span_eq_bot]
  rintro x ⟨u, _, v, hv, rfl⟩
  exact absurd (hwv_dominant D h2 Lt S mu v hv) hmu

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hG mu hmu`. Assume the negation of the conclusion as `hpi`. Apply `hmu` to reduce the goal to its premises. Establish `hle : (⨆ lam ∈ pi, isoSub (glOps K r Lt S) lam) ≤ LinearMap.ker (e mu)`.

Use `iSup₂_le fun lam hlam => ?_` and prove the remaining obligations. Introduce `x hx`. Establish `hne : lam ≠ mu` using `fun h => hpi (h ▸ hlam)`. Establish `he'` using `he mu`. Unfold `IsIsoProj at he'`.

Conclude with `LinearMap.mem_ker.2 (he'.2 lam hne x hx)`. Conclude with `LinearMap.mem_ker.1 (hle hG)`. Introduce `h`. Take `⟨T, hT, hmem⟩` from `hdec G`. Rewrite using `[hT]`.

Use `Submodule.sum_mem _ fun mu _ => ?_` and prove the remaining obligations. Distinguish the cases in `h0 : e mu G = 0`. Rewrite using `[h0]`. Conclude with `Submodule.zero_mem _`. Conclude with `(le_iSup₂ (f := fun lam (_ : lam ∈ pi) => isoSub (glOps K r Lt S) lam) mu (h mu h0)) (hmem mu)`.
-/
theorem mem_iSup_iso_iff (Lt : Letters (Fin N)) (S : Set (Fin N))
    (e : (Fin r → ℤ) → Module.End K (MvPolynomial (Fin N × Fin r) K)) (he : ∀ mu, IsIsoProj (glOps K r Lt S) mu (e mu))
    (hdec : ∀ G : MvPolynomial (Fin N × Fin r) K, ∃ T : Finset (Fin r → ℤ),
      G = ∑ mu ∈ T, e mu G ∧ ∀ mu, e mu G ∈ isoSub (glOps K r Lt S) mu)
    (pi : Set (Fin r → ℤ)) (G : MvPolynomial (Fin N × Fin r) K) :
    G ∈ (⨆ lam ∈ pi, isoSub (glOps K r Lt S) lam) ↔ ∀ mu, e mu G ≠ 0 → mu ∈ pi := by
  constructor
  · intro hG mu hmu
    by_contra hpi
    apply hmu
    have hle : (⨆ lam ∈ pi, isoSub (glOps K r Lt S) lam) ≤ LinearMap.ker (e mu) := by
      refine iSup₂_le fun lam hlam => ?_
      intro x hx
      have hne : lam ≠ mu := fun h => hpi (h ▸ hlam)
      have he' := he mu
      unfold IsIsoProj at he'
      exact LinearMap.mem_ker.2 (he'.2 lam hne x hx)
    exact LinearMap.mem_ker.1 (hle hG)
  · intro h
    obtain ⟨T, hT, hmem⟩ := hdec G
    rw [hT]
    refine Submodule.sum_mem _ fun mu _ => ?_
    by_cases h0 : e mu G = 0
    · rw [h0]
      exact Submodule.zero_mem _
    · exact (le_iSup₂ (f := fun lam (_ : lam ∈ pi) => isoSub (glOps K r Lt S) lam) mu (h mu h0)) (hmem mu)

/- English proof (translation)
Unfold `YCond`. Apply `eq_top_iff.2` to reduce the goal to its premises. Apply `le_sSup` to reduce the goal to its premises. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `x _`.

Simplify using `[MvPolynomial.mem_restrictSupport_iff]`. Introduce `c d x _`. Conclude with `Submodule.mem_top`.
-/
theorem ycond_top (LL : ChainLetters N) (j : ℕ) : YCond K (r := r) LL j ⊤ = ⊤ := by
  unfold YCond
  apply eq_top_iff.2
  apply le_sSup
  refine ⟨?_, ?_⟩
  · intro x _
    simp [MvPolynomial.mem_restrictSupport_iff]
  · intro c d x _
    exact Submodule.mem_top

/- English proof (translation)
Simplify using `only [Pol, MvPolynomial.mem_restrictSupport_iff, MvPolynomial.support_map_of_injective G hf]`.
-/
theorem map_mem_Pol_iff {O : Type} [CommRing O] [IsDomain O] (f : O →+* K) (hf : Function.Injective f)
    (d : Fin N → ℕ) (G : MvPolynomial (Fin N × Fin r) O) :
    MvPolynomial.map f G ∈ Pol K r d ↔ G ∈ Pol O r d := by
  simp only [Pol, MvPolynomial.mem_restrictSupport_iff, MvPolynomial.support_map_of_injective G hf]

/- English proof (translation)
The claim follows from `(generated_weight_lemma_of_reducibility D h2 (valuationsAdditive_D7 D) K (Fin N) Lt r S e he).2 G M`.
-/
theorem lowest_degree_le_iff_types (D : Formalism.BasicNotions.D7) (h2 : Formalism.MainNotions.CovariantDegrees.adm2 D) (Lt : Letters (Fin N)) (S : Set (Fin N))
    (e : (Fin r → ℤ) → Module.End K (MvPolynomial (Fin N × Fin r) K)) (he : ∀ mu, IsIsoProj (glOps K r Lt S) mu (e mu))
    (G : MvPolynomial (Fin N × Fin r) K) (M : ℤ) :
    lam1S Lt S G ≤ (M : WithBot ℤ) ↔ ∀ mu, e mu G ≠ 0 → mu 0 ≤ M :=
  (generated_weight_lemma_of_reducibility D h2 (valuationsAdditive_D7 D) K (Fin N) Lt r S e he).2 G M

open Classical in

/- English proof (translation)
Introduce `N LL q J M hJ`. Establish `hp` using `X.std.1.prime`. Establish `hKz : CharZero (KK X.O)` using `dvr_fraction_field_charZero X.setting hp`. Establish `hOz : CharZero X.O` using `(algebraMap X.O (KK X.O)).charZero`. Establish `hinj : Function.Injective (algebraMap X.O (KK X.O))` using `IsFractionRing.injective X.O (KK X.O)`.

Establish `hr : NeZero X.r` using `⟨X.hm⟩`. Use `set Lt : Letters (Fin N) := ⟨LL.vec⟩ with hLt`. Set `Ix : Set (Fin (N + 1))` to `{i | ∃ k, J k = i.val}`. Set `pi : Fin (N + 1) → Set (Fin X.r → ℤ)` to `fun i => {lam | Dominant lam ∧ ∀ k, J k = i.val → ((lam ⟨0, Nat.pos_of_ne_zero X.hm⟩ : ℤ) : WithTop ℤ) ≤ M k}`. Establish `hpi : ∀ i, Formalism.MainNotions.CovariantDegrees.DomLowerSet (pi i)`.

Introduce `i`. Use `⟨fun mu h => h.1, fun mu hmu nu hnu hle => ⟨hnu, fun k hk => le_trans ?_ (hmu.2 k hk)⟩⟩` and prove the remaining obligations. Use `hle.1 ⟨0, Nat.pos_of_ne_zero X.hm⟩` as an intermediate fact. Establish `e1 : (Finset.univ.filter (· ≤ (⟨0, Nat.pos_of_ne_zero X.hm⟩ : Fin X.r))) = {⟨0, Nat.pos_of_ne_zero X.hm⟩}`. Use extensionality with `b`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Apply `Fin.ext` to reduce the goal to its premises. Use `Fin.le_def.1 h` as an intermediate fact.

Express the relevant statement in the definitionally equal form `b.val ≤ 0 at this`. Use `show b.val = 0`. Use linear arithmetic over natural numbers and integers. Introduce `h`. Rewrite using `[h]`.

Rewrite `this` using `[e1, Finset.sum_singleton, Finset.sum_singleton]`. Conclude with `this` after adjusting the coercions. Establish `hB` using `(h15 X.O N X.r Lt LL.deg pi hpi).1 Ix`. Establish `hdec` using `fun (i : Fin (N + 1)) => Formalism.MainNotions.G.Joints.polIsoDecompB_of D h2 (KK X.O) (Fin N) Lt X.r {l : Fin N | l.val < i.val}`. Establish `hcond : ∀ (i : Fin (N + 1)) (G : MvPolynomial (Fin N × Fin X.r) (KK X.O)), G ∈ (⨆ lam ∈ pi i, isoSub (glOps (KK X.O) X.r Lt {l : Fin N | l.val < i.val}) lam) ↔ ∀ k, J k = i.val → G ∈ YCond (KK X.O) (r` using `X.r) LL (J k) (M k) := by`.

Introduce `i G`. Take `⟨e, he, hd⟩` from `hdec i`. Rewrite using `[mem_iSup_iso_iff Lt _ e he hd]`. Prove the components needed by the constructor for the conclusion. Introduce `h k hk`.

Consider the cases of `hM : M k with`. Consider the case `top => rw [ycond_top]`. Conclude with `Submodule.mem_top`. Consider the case `coe Mk`. Rewrite using `[mem_ycond_iff D LL (J k) Mk G]`.

Establish `hS : {l : Fin N | (l : ℕ) < J k} = {l : Fin N | l.val < i.val}` using `by rw [hk]`. Rewrite using `[hS, lowest_degree_le_iff_types D h2 Lt _ e he G Mk]`. Introduce `mu hmu`. Use `(h mu hmu).2 k hk` as an intermediate fact. Rewrite `this` using `[hM]`.

Conclude with `this` after adjusting the coercions. Introduce `h mu hmu`. Use `⟨?_, fun k hk => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hdom`. Apply `hmu` to reduce the goal to its premises.

Take `⟨_, _, hmem⟩` from `hd G`. Establish `: e mu G ∈ isoSub (glOps (KK X.O) X.r Lt {l : Fin N | l.val < i.val}) mu` using `hmem mu`. Rewrite `this` using `[isoSub_eq_bot D h2 Lt _ mu hdom]`. Conclude with `(Submodule.mem_bot _).1 this`. Establish `hY` using `h k hk`.

Consider the cases of `hM : M k with`. Consider the case `top => exact le_top`. Consider the case `coe Mk`. Rewrite `hY` using `[hM, mem_ycond_iff D LL (J k) Mk G]`. Establish `hS : {l : Fin N | (l : ℕ) < J k} = {l : Fin N | l.val < i.val}` using `by rw [hk]`.

Rewrite `hY` using `[hS, lowest_degree_le_iff_types D h2 Lt _ e he G Mk]`. Conclude with `hY mu hmu` after adjusting the coercions. Establish `hmemL : ∀ G : MvPolynomial (Fin N × Fin X.r) X.O, G ∈ Formalism.MainNotions.CovariantDegrees.nestLat X.O N X.r Lt LL.deg pi Ix ↔ G ∈ Pol X.O X.r LL.deg ∧ ∀ k, MvPolynomial.map (algebraMap X.O (KK X.O)) G ∈ YCond (KK X.O) (r` using `X.r) LL (J k) (M k) := by`. Introduce `G`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hPol, hI⟩`. Use `⟨hPol, fun k => ?_⟩` and prove the remaining obligations. Conclude with `(hcond ⟨J k, Nat.lt_succ_of_le (hJ k)⟩ _).1 (hI _ ⟨k, rfl⟩) k rfl`. Introduce and unpack `⟨hPol, hY⟩`. Use `⟨hPol, fun i hi => ?_⟩` and prove the remaining obligations.

Rewrite using `[hcond]`. Introduce `k _`. Conclude with `hY k`. Establish `hY : ∀ F, F ∈ YjtZ X.O (r` using `X.r) LL J M ↔ ∃ G ∈ Formalism.MainNotions.CovariantDegrees.nestLat X.O N X.r Lt LL.deg pi Ix, MvPolynomial.map (algebraMap X.O (KK X.O)) G = F := by`. Introduce `F`.

Simplify using `only [hmemL]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hF1, G, rfl⟩`. Establish `hF1' : (MvPolynomial.map (algebraMap X.O (KK X.O)) G) ∈ Yjt (KK X.O) (r` using `X.r) LL J M := hF1`. Rewrite `hF1'` using `[Yjt, Submodule.mem_inf, Submodule.mem_iInf]`.

Conclude with `⟨G, ⟨(map_mem_Pol_iff _ hinj _ G).1 hF1'.1, hF1'.2⟩, rfl⟩`. Introduce and unpack `⟨G, ⟨hPol, hYk⟩, rfl⟩`. Use `⟨?_, G, rfl⟩` and prove the remaining obligations. Use `show MvPolynomial.map (algebraMap X.O (KK X.O)) G ∈ Yjt (KK X.O) (r := X.r) LL J M`. Rewrite using `[Yjt, Submodule.mem_inf, Submodule.mem_iInf]`.

Conclude with `⟨(map_mem_Pol_iff _ hinj _ G).2 hPol, hYk⟩`. Establish `hgen : (MvPolynomial.map (algebraMap X.O (KK X.O))) '' {G | ∃ P : PPath X.r N Lt LL.deg, ∃ I, IsSt P.mu I ∧ (∀ i ∈ Ix, P.mu i ∈ pi i) ∧ G = Psi X.O P.mu I} = {F | ∃ (P : PPath X.r N Lt LL.deg) (I : ℤ → Finset (Fin X.r)), (∀ k, ((P.mu ⟨J k, Nat.lt_succ_of_le (hJ k)⟩ ⟨0, Nat.pos_of …`. Use extensionality with `F`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨G, ⟨P, I, hSt, hpiP, rfl⟩, rfl⟩`.

Use `⟨P, I, fun k => (hpiP ⟨J k, Nat.lt_succ_of_le (hJ k)⟩ ⟨k, rfl⟩).2 k rfl, hSt, ?_⟩` and prove the remaining obligations. Conclude with `Formalism.MainNotions.G.Joints.StandardMonomialSpace.Psi_map _ P.mu I`. Introduce and unpack `⟨P, I, hk, hSt, rfl⟩`. Use `⟨Psi X.O P.mu I, ⟨P, I, hSt, fun i hi => ⟨P.dom i, fun k hki => ?_⟩, rfl⟩, Formalism.MainNotions.G.Joints.StandardMonomialSpace.Psi_map _ P.mu I⟩` and prove the remaining obligations. Establish `: i = ⟨J k, Nat.lt_succ_of_le (hJ k)⟩` using `Fin.ext hki.symm`.

Substitute `this` using the available equality. Conclude with `hk k`. Use extensionality with `F`. Rewrite using `[hY F]`. Establish `hB' : ∀ G, G ∈ Formalism.MainNotions.CovariantDegrees.nestLat X.O N X.r Lt LL.deg pi Ix ↔ G ∈ Formalism.MainNotions.CovariantDegrees.nestSpan X.O N X.r Lt LL.deg pi Ix` using `fun G => by rw [hB]; rfl`.

Simplify using `only [hB']`. Rewrite using `[← hgen]`. Set `φ : MvPolynomial (Fin N × Fin X.r) X.O →ₗ[X.O] MvPolynomial (Fin N × Fin X.r) (KK X.O)` to `(MvPolynomial.mapAlgHom (Algebra.ofId X.O (KK X.O))).toLinearMap`. Establish `hfun : (MvPolynomial.map (algebraMap X.O (KK X.O)) : MvPolynomial (Fin N × Fin X.r) X.O → _) = ⇑φ` using `rfl`. Rewrite using `[hfun, ← Submodule.map_span, Submodule.mem_map]`.

Both sides reduce to the same expression.
-/
theorem combined_weight_of_nested_sets (D : Formalism.BasicNotions.D7) (X : Formalism.MainNotions.flipOneThree.Inst) (h2 : Formalism.MainNotions.CovariantDegrees.adm2 D)
    (h15 : Formalism.MainNotions.CovariantDegrees.SaturatedLowerSetSpan D) : Formalism.MainNotions.flipOneThree.adm8 D X := by
  intro N LL q J M hJ
  have hp := X.std.1.prime
  have hKz : CharZero (KK X.O) := dvr_fraction_field_charZero X.setting hp
  have hOz : CharZero X.O := (algebraMap X.O (KK X.O)).charZero
  have hinj : Function.Injective (algebraMap X.O (KK X.O)) := IsFractionRing.injective X.O (KK X.O)
  have hr : NeZero X.r := ⟨X.hm⟩
  set Lt : Letters (Fin N) := ⟨LL.vec⟩ with hLt
  let Ix : Set (Fin (N + 1)) := {i | ∃ k, J k = i.val}
  let pi : Fin (N + 1) → Set (Fin X.r → ℤ) := fun i =>
    {lam | Dominant lam ∧ ∀ k, J k = i.val → ((lam ⟨0, Nat.pos_of_ne_zero X.hm⟩ : ℤ) : WithTop ℤ) ≤ M k}
  have hpi : ∀ i, Formalism.MainNotions.CovariantDegrees.DomLowerSet (pi i) := by
    intro i
    refine ⟨fun mu h => h.1, fun mu hmu nu hnu hle => ⟨hnu, fun k hk => le_trans ?_ (hmu.2 k hk)⟩⟩
    have := hle.1 ⟨0, Nat.pos_of_ne_zero X.hm⟩
    have e1 : (Finset.univ.filter (· ≤ (⟨0, Nat.pos_of_ne_zero X.hm⟩ : Fin X.r))) = {⟨0, Nat.pos_of_ne_zero X.hm⟩} := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; apply Fin.ext; have := Fin.le_def.1 h; change b.val ≤ 0 at this; show b.val = 0; omega
      · intro h; rw [h]
    rw [e1, Finset.sum_singleton, Finset.sum_singleton] at this
    exact_mod_cast this
  have hB := (h15 X.O N X.r Lt LL.deg pi hpi).1 Ix

  have hdec := fun (i : Fin (N + 1)) =>
    Formalism.MainNotions.G.Joints.polIsoDecompB_of D h2 (KK X.O) (Fin N) Lt X.r {l : Fin N | l.val < i.val}

  have hcond : ∀ (i : Fin (N + 1)) (G : MvPolynomial (Fin N × Fin X.r) (KK X.O)),
      G ∈ (⨆ lam ∈ pi i, isoSub (glOps (KK X.O) X.r Lt {l : Fin N | l.val < i.val}) lam) ↔
        ∀ k, J k = i.val → G ∈ YCond (KK X.O) (r := X.r) LL (J k) (M k) := by
    intro i G
    obtain ⟨e, he, hd⟩ := hdec i
    rw [mem_iSup_iso_iff Lt _ e he hd]
    constructor
    · intro h k hk
      cases hM : M k with
      | top => rw [ycond_top]; exact Submodule.mem_top
      | coe Mk =>
        rw [mem_ycond_iff D LL (J k) Mk G]
        have hS : {l : Fin N | (l : ℕ) < J k} = {l : Fin N | l.val < i.val} := by rw [hk]
        rw [hS, lowest_degree_le_iff_types D h2 Lt _ e he G Mk]
        intro mu hmu
        have := (h mu hmu).2 k hk
        rw [hM] at this
        exact_mod_cast this
    · intro h mu hmu
      refine ⟨?_, fun k hk => ?_⟩
      · by_contra hdom
        apply hmu
        obtain ⟨_, _, hmem⟩ := hd G
        have : e mu G ∈ isoSub (glOps (KK X.O) X.r Lt {l : Fin N | l.val < i.val}) mu := hmem mu
        rw [isoSub_eq_bot D h2 Lt _ mu hdom] at this
        exact (Submodule.mem_bot _).1 this
      · have hY := h k hk
        cases hM : M k with
        | top => exact le_top
        | coe Mk =>
          rw [hM, mem_ycond_iff D LL (J k) Mk G] at hY
          have hS : {l : Fin N | (l : ℕ) < J k} = {l : Fin N | l.val < i.val} := by rw [hk]
          rw [hS, lowest_degree_le_iff_types D h2 Lt _ e he G Mk] at hY
          exact_mod_cast hY mu hmu
  have hmemL : ∀ G : MvPolynomial (Fin N × Fin X.r) X.O,
      G ∈ Formalism.MainNotions.CovariantDegrees.nestLat X.O N X.r Lt LL.deg pi Ix ↔
        G ∈ Pol X.O X.r LL.deg ∧ ∀ k, MvPolynomial.map (algebraMap X.O (KK X.O)) G ∈ YCond (KK X.O) (r := X.r) LL (J k) (M k) := by
    intro G
    constructor
    · rintro ⟨hPol, hI⟩
      refine ⟨hPol, fun k => ?_⟩
      exact (hcond ⟨J k, Nat.lt_succ_of_le (hJ k)⟩ _).1 (hI _ ⟨k, rfl⟩) k rfl
    · rintro ⟨hPol, hY⟩
      refine ⟨hPol, fun i hi => ?_⟩
      rw [hcond]
      intro k _
      exact hY k
  have hY : ∀ F, F ∈ YjtZ X.O (r := X.r) LL J M ↔
      ∃ G ∈ Formalism.MainNotions.CovariantDegrees.nestLat X.O N X.r Lt LL.deg pi Ix, MvPolynomial.map (algebraMap X.O (KK X.O)) G = F := by
    intro F
    simp only [hmemL]
    constructor
    · rintro ⟨hF1, G, rfl⟩
      have hF1' : (MvPolynomial.map (algebraMap X.O (KK X.O)) G) ∈ Yjt (KK X.O) (r := X.r) LL J M := hF1
      rw [Yjt, Submodule.mem_inf, Submodule.mem_iInf] at hF1'
      exact ⟨G, ⟨(map_mem_Pol_iff _ hinj _ G).1 hF1'.1, hF1'.2⟩, rfl⟩
    · rintro ⟨G, ⟨hPol, hYk⟩, rfl⟩
      refine ⟨?_, G, rfl⟩
      show MvPolynomial.map (algebraMap X.O (KK X.O)) G ∈ Yjt (KK X.O) (r := X.r) LL J M
      rw [Yjt, Submodule.mem_inf, Submodule.mem_iInf]
      exact ⟨(map_mem_Pol_iff _ hinj _ G).2 hPol, hYk⟩

  have hgen : (MvPolynomial.map (algebraMap X.O (KK X.O))) ''
      {G | ∃ P : PPath X.r N Lt LL.deg, ∃ I, IsSt P.mu I ∧ (∀ i ∈ Ix, P.mu i ∈ pi i) ∧ G = Psi X.O P.mu I} =
      {F | ∃ (P : PPath X.r N Lt LL.deg) (I : ℤ → Finset (Fin X.r)),
        (∀ k, ((P.mu ⟨J k, Nat.lt_succ_of_le (hJ k)⟩ ⟨0, Nat.pos_of_ne_zero X.hm⟩ : ℤ) : WithTop ℤ) ≤ M k) ∧
          IsSt P.mu I ∧ F = Psi (KK X.O) P.mu I} := by
    ext F
    constructor
    · rintro ⟨G, ⟨P, I, hSt, hpiP, rfl⟩, rfl⟩
      refine ⟨P, I, fun k => (hpiP ⟨J k, Nat.lt_succ_of_le (hJ k)⟩ ⟨k, rfl⟩).2 k rfl, hSt, ?_⟩
      exact Formalism.MainNotions.G.Joints.StandardMonomialSpace.Psi_map _ P.mu I
    · rintro ⟨P, I, hk, hSt, rfl⟩
      refine ⟨Psi X.O P.mu I, ⟨P, I, hSt, fun i hi => ⟨P.dom i, fun k hki => ?_⟩, rfl⟩,
        Formalism.MainNotions.G.Joints.StandardMonomialSpace.Psi_map _ P.mu I⟩
      have : i = ⟨J k, Nat.lt_succ_of_le (hJ k)⟩ := Fin.ext hki.symm
      subst this
      exact hk k
  ext F
  rw [hY F]
  have hB' : ∀ G, G ∈ Formalism.MainNotions.CovariantDegrees.nestLat X.O N X.r Lt LL.deg pi Ix ↔
      G ∈ Formalism.MainNotions.CovariantDegrees.nestSpan X.O N X.r Lt LL.deg pi Ix := fun G => by rw [hB]; rfl
  simp only [hB']
  rw [← hgen]
  let φ : MvPolynomial (Fin N × Fin X.r) X.O →ₗ[X.O] MvPolynomial (Fin N × Fin X.r) (KK X.O) :=
    (MvPolynomial.mapAlgHom (Algebra.ofId X.O (KK X.O))).toLinearMap
  have hfun : (MvPolynomial.map (algebraMap X.O (KK X.O)) : MvPolynomial (Fin N × Fin X.r) X.O → _) = ⇑φ := rfl
  rw [hfun, ← Submodule.map_span, Submodule.mem_map]
  rfl

end Formalism.MainNotions.G.PolBridge
