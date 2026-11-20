import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.LocUApply
import Development.AutomorphicArithmetic.TwistedTraces.ListOfFnProdEqMulUpdateOneOfPairwiseCommute
import Development.AutomorphicArithmetic.TwistedTraces.FixedProjectionInvariantAndCommutingReps
import Development.AutomorphicArithmetic.TwistedTraces.FixedProjectionApplyEquivariantEq
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

/- English proof (translation)
Introduce `r G _ _ _ _ _ _ H _ _ _ S _ _ π τ Z hsm hc hZc hZi s I R hRZ hRs hI L K hL hKL hsK i f hf`. Set `a : Fin r → (H →L[ℂ] H)` to `fun j => prj (fixU (π j) (L j))`. Establish `hcomm : ∀ p q, p ≠ q → Commute (a p) (a q)` using `fun p q hpq => by`. Use `ContinuousLinearMap.ext fun v => ?_` and prove the remaining obligations. Conclude with `((UpperTheory.fixedProjection_invariant_and_commuting_reps (G p) (G q) H (π p) (π q) (L p) (L q)).2.2.2 (hc p q hpq)).2 v`.

Establish `hact : ∀ j, j ≠ i → ∀ g v, a j (π i g v) = π i g (a j v)` using `fun j hj g v => ((UpperTheory.fixedProjection_invariant_and_commuting_reps (G j) (G i) H (π j) (π i) (L j) (L i)).2.2.2 (hc j i hj)).1 g v`. Take `⟨hprod, hQc⟩` from `UpperTheory.list_ofFn_prod_eq_mul_update_one_of_pairwise_commute (H →L[ℂ] H) r a hcomm i`. Set `b : Fin r → (H →L[ℂ] H)` to `Function.update a i 1`. Set `Q : H →L[ℂ] H` to `(List.ofFn b).prod`. Establish `hQa : Commute (a i) Q` using `hQc (a i) fun j hj => hcomm i j hj.symm`.

Establish `hQπ : ∀ g v, Q (π i g v) = π i g (Q v)` using `fun g v => by`. Establish `h : Commute (π i g : H →L[ℂ] H) Q` using `hQc _ fun j hj => by`. Use `ContinuousLinearMap.ext fun v => ?_` and prove the remaining obligations. Conclude with `(hact j hj g v).symm`. Conclude with `(congrArg (fun T : H →L[ℂ] H => T v) h.eq).symm`.

Establish `hb : ∀ p q, p ≠ q → Commute (b p) (b q)` using `fun p q hpq => by`. Distinguish the cases in `hp : p = i`. Substitute `hp` using the available equality. Simplify using `only [b, Function.update_self]`. Conclude with `Commute.one_left _`.

Distinguish the cases in `hq : q = i`. Substitute `hq` using the available equality. Simplify using `only [b, Function.update_self]`. Conclude with `Commute.one_right _`. Simplify using `only [b, Function.update_of_ne hp, Function.update_of_ne hq]`.

Conclude with `hcomm p q hpq`. Establish `hQZ : ∀ v ∈ Z, Q v ∈ Z`. Set `M : Submonoid (H →L[ℂ] H)` to `{ carrier := {T | ∀ v ∈ Z, T v ∈ Z} mul_mem' := fun ha hb v hv => ha _ (hb v hv) one_mem' := fun v hv => hv }`. Establish `hM : Q ∈ M`. Use `Submonoid.list_prod_mem M fun x hx => ?_` and prove the remaining obligations.

Take `⟨j, rfl⟩` from `List.mem_ofFn.mp hx`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `only [b, Function.update_self]`. Conclude with `M.one_mem`.

Simplify using `only [b, Function.update_of_ne hj]`. Conclude with `fun v hv => (UpperTheory.fixedProjection_invariant_and_commuting_reps (G j) (G j) H (π j) (π j) (L j) (L j)).2.2.1 Z hZc (hZi j) v hv`. Conclude with `hM`. Establish `hQfix : ∀ j, j ≠ i → ∀ v, Q v ∈ fixU (π j) (L j)` using `fun j hj v => by`. Establish `h` using `(UpperTheory.list_ofFn_prod_eq_mul_update_one_of_pairwise_commute (H →L[ℂ] H) r b hb j).1`.

Establish `h2 : Q v = a j ((List.ofFn (Function.update b j 1)).prod v)`. Establish `h3 : b j = a j` using `Function.update_of_ne hj _ _`. Express the relevant statement in the definitionally equal form `(List.ofFn b).prod v = _`. Rewrite using `[h, h3]`. Both sides reduce to the same expression.

Rewrite using `[h2]`. Conclude with `(UpperTheory.fixedProjection_invariant_and_commuting_reps (G j) (G j) H (π j) (π j) (L j) (L j)).1 _`. Set `f' : S i →ₗ[ℂ] H` to `(R : H →ₗ[ℂ] H) ∘ₗ (Q : H →ₗ[ℂ] H) ∘ₗ f ∘ₗ ((I i).symm : S i →ₗ[ℂ] S i)`. Establish `hf' : ∀ y, f' y = R (Q (f ((I i).symm y)))` using `fun y => rfl`. Establish `hfZ : ∀ x, f x ∈ Z` using `fun x => (Submodule.mem_inf.1 (hf.mem x)).1`.

Use `⟨f', ⟨fun y => ?_, fun g y => ?_⟩, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[hf']`. Establish `hw` using `hQZ _ (hfZ ((I i).symm y))`. Use `Submodule.mem_inf.2 ⟨hRZ _ hw, ?_⟩` and prove the remaining obligations. Simplify using `only [Submodule.mem_iInf]`.

Introduce `j hj u hu`. Establish `h` using `hRs j ((s j).symm u) _ hw`. Rewrite `h` using `[(s j).apply_symm_apply]`. Rewrite using `[← h, hQfix j hj _ _ (hsK j u hu)]`. Establish `hIs : (I i).symm (τ i g y) = τ i ((s i).symm g) ((I i).symm y)`.

Apply `(I i).injective` to reduce the goal to its premises. Rewrite using `[hI, (I i).apply_symm_apply, (I i).apply_symm_apply, (s i).apply_symm_apply]`. Rewrite using `[hf', hf', hIs, hf.map, hQπ, hRs i _ _ (hQZ _ (hfZ _)), (s i).apply_symm_apply]`. Establish `hE : Eqv (τ i) (π i) ⊤ f` using `⟨fun _ => Submodule.mem_top, hf.map⟩`. Establish `h1` using `UpperTheory.fixedProjection_apply_equivariant_eq (G i) H (S i) (τ i) (hsm i) (π i) (L i) (hL i).1 (hL i).2 f hE x`.

Establish `h2 : (List.ofFn a).prod (f x) = Q (a i (f x))`. Rewrite using `[hprod]`. Conclude with `congrArg (fun T : H →L[ℂ] H => T (f x)) hQa.eq`. Rewrite using `[hf', (I i).symm_apply_apply]`. Express the relevant statement in the definitionally equal form `R ((List.ofFn a).prod (f x)) = _`.

Rewrite using `[h2]`. Express the relevant statement in the definitionally equal form `R (Q (prj (fixU (π i) (L i)) (f x))) = _`. Rewrite using `[h1]`.
-/
theorem UpperTheory.isotypic_projection_product_commute :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] (π : ∀ i, UnitaryRep (G i) H) (τ : ∀ i, Representation ℂ (G i) (S i)) (Z : Submodule ℂ H) (hsm : ∀ i, GroundTheory.Automorphic.IsSmooth (τ i)), (∀ i j, i ≠ j → ∀ g h v, π i g (π j h v) = π j h (π i g v)) → IsClosed (Z : Set H) → (∀ i, (π i).IsInvariant Z) → ∀ (s : ∀ i, G i ≃ₜ* G i) (I : ∀ i, S i ≃ₗ[ℂ] S i) (R : H →L[ℂ] H), (∀ v ∈ Z, R v ∈ Z) → (∀ i g, ∀ v ∈ Z, R (π i g v) = π i (s i g) (R v)) → (∀ i g x, I i (τ i g x) = τ i (s i g) (I i x)) → ∀ (L K : ∀ i, Subgroup (G i)) (hL : (∀ i, IsCompact (L i : Set (G i)) ∧ IsOpen (L i : Set (G i)))), (∀ i, K i ≤ L i) → (∀ i, ∀ k ∈ K i, (s i).symm k ∈ L i) → ∀ i f, Eqv (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (K j)) f → ∃ f', Eqv (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (K j)) f' ∧ ∀ x, R ((List.ofFn fun j => prj (fixU (π j) (L j))).prod (f x)) = f' (I i (fixedProj (τ i) (hsm i) (hL i).1 (hL i).2 x : S i)) := by
  intro r G _ _ _ _ _ _ H _ _ _ S _ _ π τ Z hsm hc hZc hZi s I R hRZ hRs hI L K hL hKL hsK i f hf
  let a : Fin r → (H →L[ℂ] H) := fun j => prj (fixU (π j) (L j))
  have hcomm : ∀ p q, p ≠ q → Commute (a p) (a q) := fun p q hpq => by
    refine ContinuousLinearMap.ext fun v => ?_
    exact ((UpperTheory.fixedProjection_invariant_and_commuting_reps (G p) (G q) H (π p) (π q) (L p) (L q)).2.2.2 (hc p q hpq)).2 v
  have hact : ∀ j, j ≠ i → ∀ g v, a j (π i g v) = π i g (a j v) := fun j hj g v =>
    ((UpperTheory.fixedProjection_invariant_and_commuting_reps (G j) (G i) H (π j) (π i) (L j) (L i)).2.2.2 (hc j i hj)).1 g v
  obtain ⟨hprod, hQc⟩ := UpperTheory.list_ofFn_prod_eq_mul_update_one_of_pairwise_commute (H →L[ℂ] H) r a hcomm i
  let b : Fin r → (H →L[ℂ] H) := Function.update a i 1
  let Q : H →L[ℂ] H := (List.ofFn b).prod
  have hQa : Commute (a i) Q := hQc (a i) fun j hj => hcomm i j hj.symm
  have hQπ : ∀ g v, Q (π i g v) = π i g (Q v) := fun g v => by
    have h : Commute (π i g : H →L[ℂ] H) Q := hQc _ fun j hj => by
      refine ContinuousLinearMap.ext fun v => ?_
      exact (hact j hj g v).symm
    exact (congrArg (fun T : H →L[ℂ] H => T v) h.eq).symm
  have hb : ∀ p q, p ≠ q → Commute (b p) (b q) := fun p q hpq => by
    by_cases hp : p = i
    · subst hp
      simp only [b, Function.update_self]
      exact Commute.one_left _
    · by_cases hq : q = i
      · subst hq
        simp only [b, Function.update_self]
        exact Commute.one_right _
      · simp only [b, Function.update_of_ne hp, Function.update_of_ne hq]
        exact hcomm p q hpq
  have hQZ : ∀ v ∈ Z, Q v ∈ Z := by
    let M : Submonoid (H →L[ℂ] H) :=
      { carrier := {T | ∀ v ∈ Z, T v ∈ Z}
        mul_mem' := fun ha hb v hv => ha _ (hb v hv)
        one_mem' := fun v hv => hv }
    have hM : Q ∈ M := by
      refine Submonoid.list_prod_mem M fun x hx => ?_
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      by_cases hj : j = i
      · subst hj
        simp only [b, Function.update_self]
        exact M.one_mem
      · simp only [b, Function.update_of_ne hj]
        exact fun v hv => (UpperTheory.fixedProjection_invariant_and_commuting_reps (G j) (G j) H (π j) (π j) (L j) (L j)).2.2.1 Z hZc (hZi j) v hv
    exact hM
  have hQfix : ∀ j, j ≠ i → ∀ v, Q v ∈ fixU (π j) (L j) := fun j hj v => by
    have h := (UpperTheory.list_ofFn_prod_eq_mul_update_one_of_pairwise_commute (H →L[ℂ] H) r b hb j).1
    have h2 : Q v = a j ((List.ofFn (Function.update b j 1)).prod v) := by
      have h3 : b j = a j := Function.update_of_ne hj _ _
      change (List.ofFn b).prod v = _
      rw [h, h3]
      rfl
    rw [h2]
    exact (UpperTheory.fixedProjection_invariant_and_commuting_reps (G j) (G j) H (π j) (π j) (L j) (L j)).1 _
  let f' : S i →ₗ[ℂ] H := (R : H →ₗ[ℂ] H) ∘ₗ (Q : H →ₗ[ℂ] H) ∘ₗ f ∘ₗ ((I i).symm : S i →ₗ[ℂ] S i)
  have hf' : ∀ y, f' y = R (Q (f ((I i).symm y))) := fun y => rfl
  have hfZ : ∀ x, f x ∈ Z := fun x => (Submodule.mem_inf.1 (hf.mem x)).1
  refine ⟨f', ⟨fun y => ?_, fun g y => ?_⟩, fun x => ?_⟩
  · rw [hf']
    have hw := hQZ _ (hfZ ((I i).symm y))
    refine Submodule.mem_inf.2 ⟨hRZ _ hw, ?_⟩
    simp only [Submodule.mem_iInf]
    intro j hj u hu
    have h := hRs j ((s j).symm u) _ hw
    rw [(s j).apply_symm_apply] at h
    rw [← h, hQfix j hj _ _ (hsK j u hu)]
  · have hIs : (I i).symm (τ i g y) = τ i ((s i).symm g) ((I i).symm y) := by
      apply (I i).injective
      rw [hI, (I i).apply_symm_apply, (I i).apply_symm_apply, (s i).apply_symm_apply]
    rw [hf', hf', hIs, hf.map, hQπ, hRs i _ _ (hQZ _ (hfZ _)), (s i).apply_symm_apply]
  · have hE : Eqv (τ i) (π i) ⊤ f := ⟨fun _ => Submodule.mem_top, hf.map⟩
    have h1 := UpperTheory.fixedProjection_apply_equivariant_eq (G i) H (S i) (τ i) (hsm i) (π i) (L i) (hL i).1 (hL i).2 f hE x
    have h2 : (List.ofFn a).prod (f x) = Q (a i (f x)) := by
      rw [hprod]
      exact congrArg (fun T : H →L[ℂ] H => T (f x)) hQa.eq
    rw [hf', (I i).symm_apply_apply]
    change R ((List.ofFn a).prod (f x)) = _
    rw [h2]
    change R (Q (prj (fixU (π i) (L i)) (f x))) = _
    rw [h1]
