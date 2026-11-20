import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.LocUApply
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

/- English proof (translation)
Introduce `r`. Proceed by induction on `r with`. Consider the case `zero => intro T t _ v`. Simplify using the standard rewrite rules. Consider the case `succ r ih`.

Introduce `T t h v`. Rewrite using `[List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply, h, ih (fun i => T i.succ) (fun i => t i.succ) (fun i => h _) v]`. Both sides reduce to the same expression.
-/
private theorem prod_res {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (X : Submodule ℂ H) :
    ∀ (r : ℕ) (T : Fin r → H →L[ℂ] H) (t : Fin r → Module.End ℂ X), (∀ i (v : X), ((t i v : X) : H) = T i v) →
      ∀ v : X, (((List.ofFn t).prod v : X) : H) = (List.ofFn T).prod v := by
  intro r
  induction r with
  | zero => intro T t _ v; simp
  | succ r ih =>
    intro T t h v
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply, h,
      ih (fun i => T i.succ) (fun i => t i.succ) (fun i => h _) v]
    rfl

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `r G _ _ _ _ _ _ H _ _ _ S _ _ π τ Z U c T B hc1 hle hB`. Set `X : Submodule ℂ H` to `Z ⊓ ⨅ i, fixU (π i) (U i)`. Establish `hX : X = Z ⊓ ⨅ i, fixU (π i) (U i)` using `rfl`. Set `D : Fin r → Submodule ℂ H` to `fun i => Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (U j)`. Establish `hD : ∀ i v, v ∈ D i ↔ v ∈ Z ∧ ∀ j, j ≠ i → v ∈ fixU (π j) (U j)` using `fun i v => by`.

Simplify using `only [D, Submodule.mem_inf, Submodule.mem_iInf]`. Establish `hXD : ∀ i, X = D i ⊓ fixU (π i) (U i)` using `fun i => by`. Use extensionality with `v`. Simplify using `only [hX, Submodule.mem_inf, Submodule.mem_iInf, hD]`. Use `⟨fun h => ⟨⟨h.1, fun j _ => h.2 j⟩, h.2 i⟩, fun h => ⟨h.1.1, fun j => ?_⟩⟩` and prove the remaining obligations.

Distinguish the cases in `e : j = i`. Conclude with `e ▸ h.2`. Conclude with `h.1.2 j e`. Establish `hm : ∀ i f, Eqv (τ i) (π i) (D i) f → ∀ x : fixedVectors (τ i) (U i), f x ∈ X` using `fun i f hf x => by`. Rewrite using `[hXD i]`.

Conclude with `⟨hf.mem _, fun u hu => by rw [← hf.map, mem_fixedVectors.1 x.2 u hu]⟩`. Use `prod_res X r T _ fun i v => ?_` and prove the remaining obligations. Establish `key : ∀ y ∈ spanFix (τ i) (π i) (D i) (U i), ∃ h : y ∈ X, ((c i (B i) ⟨y, h⟩ : X) : H) = T i y` using `fun y hy => by`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨f, hf, x, hx, rfl⟩` from `hy`. Conclude with `⟨hm i f hf ⟨x, hx⟩, (hc1 i (B i) f hf ⟨x, hx⟩ _ rfl).trans (hB i f ⟨fun _ => trivial, hf.map⟩ ⟨x, hx⟩).symm⟩`. Consider the case `zero => exact ⟨X.zero_mem, (congrArg Subtype.val (map_zero (c i (B i)))).trans (map_zero (T i)).symm⟩`. Consider the case `add u v _ _ h1 h2`. Take `⟨a, ha⟩` from `h1`.

Take `⟨b, hb⟩` from `h2`. Use `⟨X.add_mem a b, (congrArg Subtype.val (map_add (c i (B i)) ⟨u, a⟩ ⟨v, b⟩)).trans ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, ← ha, ← hb]`. Both sides reduce to the same expression. Consider the case `smul k u _ h1`.

Take `⟨a, ha⟩` from `h1`. Use `⟨X.smul_mem k a, (congrArg Subtype.val (map_smul (c i (B i)) k ⟨u, a⟩)).trans ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, ← ha]`. Both sides reduce to the same expression. Conclude with `(key v (hle i v.2)).2`.
-/
theorem UpperTheory.isotypic_subspace_product_closed :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] (π : ∀ i, UnitaryRep (G i) H) (τ : ∀ i, Representation ℂ (G i) (S i)) (Z : Submodule ℂ H) (U : ∀ i, Subgroup (G i)) (c : ∀ i, Module.End ℂ (fixedVectors (τ i) (U i)) →ₐ[ℂ] Module.End ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i))) (T : Fin r → H →L[ℂ] H) (B : ∀ i, Module.End ℂ (fixedVectors (τ i) (U i))), (∀ i t f, Eqv (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (U j)) f → ∀ (x : fixedVectors (τ i) (U i)) (y : ↥(Z ⊓ ⨅ i, fixU (π i) (U i))), (y : H) = f x → ((c i t y : ↥(Z ⊓ ⨅ i, fixU (π i) (U i))) : H) = f (t x)) → (∀ i, (Z ⊓ ⨅ i, fixU (π i) (U i)) ≤ spanFix (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (U j)) (U i)) → (∀ i f, Eqv (τ i) (π i) ⊤ f → ∀ x : fixedVectors (τ i) (U i), T i (f x) = f (B i x)) → ∀ v : ↥(Z ⊓ ⨅ i, fixU (π i) (U i)), (((List.ofFn fun i => c i (B i)).prod v : ↥(Z ⊓ ⨅ i, fixU (π i) (U i))) : H) = (List.ofFn T).prod v := by
  intro r G _ _ _ _ _ _ H _ _ _ S _ _ π τ Z U c T B hc1 hle hB
  let X : Submodule ℂ H := Z ⊓ ⨅ i, fixU (π i) (U i)
  have hX : X = Z ⊓ ⨅ i, fixU (π i) (U i) := rfl
  let D : Fin r → Submodule ℂ H := fun i => Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (U j)
  have hD : ∀ i v, v ∈ D i ↔ v ∈ Z ∧ ∀ j, j ≠ i → v ∈ fixU (π j) (U j) := fun i v => by
    simp only [D, Submodule.mem_inf, Submodule.mem_iInf]
  have hXD : ∀ i, X = D i ⊓ fixU (π i) (U i) := fun i => by
    ext v
    simp only [hX, Submodule.mem_inf, Submodule.mem_iInf, hD]
    refine ⟨fun h => ⟨⟨h.1, fun j _ => h.2 j⟩, h.2 i⟩, fun h => ⟨h.1.1, fun j => ?_⟩⟩
    by_cases e : j = i
    · exact e ▸ h.2
    · exact h.1.2 j e
  have hm : ∀ i f, Eqv (τ i) (π i) (D i) f → ∀ x : fixedVectors (τ i) (U i), f x ∈ X := fun i f hf x => by
    rw [hXD i]
    exact ⟨hf.mem _, fun u hu => by rw [← hf.map, mem_fixedVectors.1 x.2 u hu]⟩
  refine prod_res X r T _ fun i v => ?_
  have key : ∀ y ∈ spanFix (τ i) (π i) (D i) (U i), ∃ h : y ∈ X, ((c i (B i) ⟨y, h⟩ : X) : H) = T i y := fun y hy => by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, x, hx, rfl⟩ := hy
      exact ⟨hm i f hf ⟨x, hx⟩, (hc1 i (B i) f hf ⟨x, hx⟩ _ rfl).trans (hB i f ⟨fun _ => trivial, hf.map⟩ ⟨x, hx⟩).symm⟩
    | zero => exact ⟨X.zero_mem, (congrArg Subtype.val (map_zero (c i (B i)))).trans (map_zero (T i)).symm⟩
    | add u v _ _ h1 h2 =>
      obtain ⟨a, ha⟩ := h1
      obtain ⟨b, hb⟩ := h2
      refine ⟨X.add_mem a b, (congrArg Subtype.val (map_add (c i (B i)) ⟨u, a⟩ ⟨v, b⟩)).trans ?_⟩
      rw [map_add, ← ha, ← hb]; rfl
    | smul k u _ h1 =>
      obtain ⟨a, ha⟩ := h1
      refine ⟨X.smul_mem k a, (congrArg Subtype.val (map_smul (c i (B i)) k ⟨u, a⟩)).trans ?_⟩
      rw [map_smul, ← ha]; rfl
  exact (key v (hle i v.2)).2
