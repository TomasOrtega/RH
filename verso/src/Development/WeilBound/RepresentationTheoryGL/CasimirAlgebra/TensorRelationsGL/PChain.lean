import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PChainA

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace ChainP

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

def Good (E : Fin n → Fin n → Module.End ℂ M) (l : Fin n → ℂ) (ℓ : M →ₗ[ℂ] ℂ) (top : Fin n) (m : ℕ)
    (co : Fin m → Fin n) (g : Module.End ℂ (TV n M (Fin m))) : Prop :=
  g ∈ Algebra.adjoin ℂ (Set.range fun j : Fin m => xJ E j) ∧
    ℓ ∘ₗ LinearMap.proj (fun _ => top) ∘ₗ g ≠ 0 ∧
    (∀ j, (ℓ ∘ₗ LinearMap.proj (fun _ => top) ∘ₗ g) ∘ₗ xJ E j =
      (l (co j) + ((Finset.univ.filter fun i => i < j ∧ co i = co j).card : ℂ)) •
        (ℓ ∘ₗ LinearMap.proj (fun _ => top) ∘ₗ g)) ∧
    ∀ u : ℂ, (ℓ ∘ₗ LinearMap.proj (fun _ => top) ∘ₗ g) ∘ₗ qdet (tE (Finset.univ : Finset (Fin m)) E) u =
      (∏ k, (u + l k + ((Finset.univ.filter fun p => co p = k).card : ℂ))) • (ℓ ∘ₗ LinearMap.proj (fun _ => top) ∘ₗ g)

/- English proof (translation)
Use `symm`. Apply `Finset.card_bij (fun p _ => p.castSucc)` to reduce the goal to its premises. Introduce `p hp`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp] at hp ⊢`. Use `⟨?_, hp.2⟩` and prove the remaining obligations.

Rewrite `hp`, the goal using `[Fin.lt_def]`. Simplify using `using hp.1`. Introduce `a _ b _ h`. Conclude with `Fin.castSucc_injective _ h`. Introduce `b hb`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hb`. Establish `h1 : (b : ℕ) < i` using `by simpa [Fin.lt_def] using hb.1`. Establish `h2 : (b : ℕ) < m` using `lt_trans h1 i.isLt`. Use `⟨⟨b, h2⟩, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]`.

Use `⟨by simpa [Fin.lt_def] using h1, ?_⟩` and prove the remaining obligations. Establish `hb' : (⟨b, h2⟩ : Fin m).castSucc = b` using `Fin.ext rfl`. Rewrite using `[hb']`. Conclude with `hb.2`. Conclude with `Fin.ext rfl`.
-/
theorem card1 {m : ℕ} (co : Fin (m + 1) → Fin n) (i : Fin m) :
    (Finset.univ.filter fun p : Fin (m + 1) => p < i.castSucc ∧ co p = co i.castSucc).card =
      (Finset.univ.filter fun p : Fin m => p < i ∧ (co ∘ Fin.castSucc) p = (co ∘ Fin.castSucc) i).card := by
  symm
  apply Finset.card_bij (fun p _ => p.castSucc)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp] at hp ⊢
    refine ⟨?_, hp.2⟩
    rw [Fin.lt_def] at hp ⊢
    simpa using hp.1
  · intro a _ b _ h
    exact Fin.castSucc_injective _ h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have h1 : (b : ℕ) < i := by simpa [Fin.lt_def] using hb.1
    have h2 : (b : ℕ) < m := lt_trans h1 i.isLt
    refine ⟨⟨b, h2⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]
      refine ⟨by simpa [Fin.lt_def] using h1, ?_⟩
      have hb' : (⟨b, h2⟩ : Fin m).castSucc = b := Fin.ext rfl
      rw [hb']
      exact hb.2
    · exact Fin.ext rfl

/- English proof (translation)
Use `symm`. Apply `Finset.card_bij (fun p _ => p.castSucc)` to reduce the goal to its premises. Introduce `p hp`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp] at hp ⊢`. Conclude with `⟨Fin.castSucc_lt_last p, hp⟩`.

Introduce `a _ b _ h`. Conclude with `Fin.castSucc_injective _ h`. Introduce `b hb`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hb`. Establish `h2 : (b : ℕ) < m` using `by simpa [Fin.lt_def] using hb.1`.

Use `⟨⟨b, h2⟩, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]`. Establish `hb' : (⟨b, h2⟩ : Fin m).castSucc = b` using `Fin.ext rfl`. Rewrite using `[hb']`. Conclude with `hb.2`.

Conclude with `Fin.ext rfl`.
-/
theorem card2 {m : ℕ} (co : Fin (m + 1) → Fin n) :
    (Finset.univ.filter fun p : Fin (m + 1) => p < Fin.last m ∧ co p = co (Fin.last m)).card =
      (Finset.univ.filter fun p : Fin m => (co ∘ Fin.castSucc) p = co (Fin.last m)).card := by
  symm
  apply Finset.card_bij (fun p _ => p.castSucc)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp] at hp ⊢
    exact ⟨Fin.castSucc_lt_last p, hp⟩
  · intro a _ b _ h
    exact Fin.castSucc_injective _ h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have h2 : (b : ℕ) < m := by simpa [Fin.lt_def] using hb.1
    refine ⟨⟨b, h2⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]
      have hb' : (⟨b, h2⟩ : Fin m).castSucc = b := Fin.ext rfl
      rw [hb']
      exact hb.2
    · exact Fin.ext rfl

/- English proof (translation)
Rewrite using `[Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]`. Both sides reduce to the same expression.
-/
theorem card3 {m : ℕ} (co : Fin (m + 1) → Fin n) (k : Fin n) :
    (Finset.univ.filter fun p : Fin (m + 1) => co p = k).card =
      (Finset.univ.filter fun p : Fin m => (co ∘ Fin.castSucc) p = k).card + if co (Fin.last m) = k then 1 else 0 := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  rfl

/- English proof (translation)
Take `⟨-, h2, h3, -⟩` from `hT n M (Fin m) E hE Finset.univ`. Unfold `xJ`. Conclude with `(h2 j (Finset.mem_univ _) a b).add_left (Commute.sum_left _ _ _ fun i _ => h3 _ (fun p => by simp) a b)`.
-/
theorem xJ_comm (hT : TensorGl) (E : Fin n → Fin n → Module.End ℂ M) (hE : GlRel E) (m : ℕ) (j : Fin m)
    (a b : Fin n) : Commute (xJ E j) (tE (Finset.univ : Finset (Fin m)) E a b) := by
  obtain ⟨-, h2, h3, -⟩ := hT n M (Fin m) E hE Finset.univ
  unfold xJ
  exact (h2 j (Finset.mem_univ _) a b).add_left
    (Commute.sum_left _ _ _ fun i _ => h3 _ (fun p => by simp) a b)

/- English proof (translation)
Use `⟨Subalgebra.one_mem _, ?_, fun j => j.elim0, ?_⟩` and prove the remaining obligations. Introduce `h`. Apply `hℓ` to reduce the goal to its premises. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Use `LinearMap.congr_fun h (fun _ => v)` as an intermediate fact.

Simplify using `using this`. Introduce `u`. Establish `hc : ∀ a b : Fin n, (LinearMap.proj (fun _ : Fin 0 => top) : TV n M (Fin 0) →ₗ[ℂ] M) ∘ₗ tE (Finset.univ : Finset (Fin 0)) E a b = E a b ∘ₗ LinearMap.proj (fun _ : Fin 0 => top)`. Introduce `a b`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Simplify using `[tE, lift]`. Establish `hq` using `qdet_comp (LinearMap.proj (fun _ : Fin 0 => top) : TV n M (Fin 0) →ₗ[ℂ] M) _ E hc u`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Establish `hx` using `LinearMap.congr_fun hq x`. Simplify using `only [LinearMap.comp_apply, Module.End.one_apply, LinearMap.smul_apply] at hx ⊢`.

Rewrite using `[hx, hl u]`. Simplify using the standard rewrite rules.
-/
theorem base (E : Fin n → Fin n → Module.End ℂ M) (l : Fin n → ℂ) (hl : HasChar E l) (ℓ : M →ₗ[ℂ] ℂ)
    (hℓ : ℓ ≠ 0) (top : Fin n) (co : Fin 0 → Fin n) : Good E l ℓ top 0 co 1 := by
  refine ⟨Subalgebra.one_mem _, ?_, fun j => j.elim0, ?_⟩
  · intro h
    apply hℓ
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun h (fun _ => v)
    simpa using this
  · intro u
    have hc : ∀ a b : Fin n, (LinearMap.proj (fun _ : Fin 0 => top) : TV n M (Fin 0) →ₗ[ℂ] M) ∘ₗ
        tE (Finset.univ : Finset (Fin 0)) E a b = E a b ∘ₗ LinearMap.proj (fun _ : Fin 0 => top) := by
      intro a b
      refine LinearMap.ext fun x => ?_
      simp [tE, lift]
    have hq := qdet_comp (LinearMap.proj (fun _ : Fin 0 => top) : TV n M (Fin 0) →ₗ[ℂ] M) _ E hc u
    refine LinearMap.ext fun x => ?_
    have hx := LinearMap.congr_fun hq x
    simp only [LinearMap.comp_apply, Module.End.one_apply, LinearMap.smul_apply] at hx ⊢
    rw [hx, hl u]
    simp

/- English proof (translation)
Introduce `g hg`. Proceed by induction on `hg using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Conclude with `⟨xJ E (Fin.castAdd 1 i), Algebra.subset_adjoin ⟨_, rfl⟩, (hC n M E m 1).2.2.1 i⟩`.

Consider the case `algebraMap c`. Use `⟨algebraMap ℂ _ c, Subalgebra.algebraMap_mem _ c, ?_⟩` and prove the remaining obligations. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Use function extensionality and compare the values at `J I`. Simplify using `[lift, curF]`.

Consider the case `add x y _ _ hx hy`. Take `⟨x', hx', ex⟩` from `hx`. Take `⟨y', hy', ey⟩` from `hy`. Use `⟨x' + y', Subalgebra.add_mem _ hx' hy', ?_⟩` and prove the remaining obligations. Establish `hs : (lift (x + y) : Module.End ℂ (TV n (TV n M (Fin m)) (Fin 1))) = lift x + lift y`.

Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Use function extensionality and compare the values at `J`. Simplify using `[lift]`. Rewrite using `[hs, LinearMap.comp_add, LinearMap.add_comp, ex, ey]`. Consider the case `mul x y _ _ hx hy`.

Take `⟨x', hx', ex⟩` from `hx`. Take `⟨y', hy', ey⟩` from `hy`. Use `⟨x' * y', Subalgebra.mul_mem _ hx' hy', ?_⟩` and prove the remaining obligations. Establish `hs : (lift (x * y) : Module.End ℂ (TV n (TV n M (Fin m)) (Fin 1))) = lift x * lift y`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `J`. Simplify using `[lift]`. Rewrite using `[hs, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ex, LinearMap.comp_assoc, ey, LinearMap.comp_assoc]`.
-/
theorem liftAdj (hC : Curry) (E : Fin n → Fin n → Module.End ℂ M) (m : ℕ) :
    ∀ g ∈ Algebra.adjoin ℂ (Set.range fun j : Fin m => xJ E j), ∃ g' ∈ Algebra.adjoin ℂ
      (Set.range fun j : Fin (m + 1) => xJ E j), curF n M m 1 ∘ₗ g' =
        (lift g : Module.End ℂ (TV n (TV n M (Fin m)) (Fin 1))) ∘ₗ curF n M m 1 := by
  intro g hg
  induction hg using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨xJ E (Fin.castAdd 1 i), Algebra.subset_adjoin ⟨_, rfl⟩, (hC n M E m 1).2.2.1 i⟩
  | algebraMap c =>
    refine ⟨algebraMap ℂ _ c, Subalgebra.algebraMap_mem _ c, ?_⟩
    refine LinearMap.ext fun x => ?_
    funext J I
    simp [lift, curF]
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨y', hy', ey⟩ := hy
    refine ⟨x' + y', Subalgebra.add_mem _ hx' hy', ?_⟩
    have hs : (lift (x + y) : Module.End ℂ (TV n (TV n M (Fin m)) (Fin 1))) = lift x + lift y := by
      refine LinearMap.ext fun v => ?_
      funext J
      simp [lift]
    rw [hs, LinearMap.comp_add, LinearMap.add_comp, ex, ey]
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨y', hy', ey⟩ := hy
    refine ⟨x' * y', Subalgebra.mul_mem _ hx' hy', ?_⟩
    have hs : (lift (x * y) : Module.End ℂ (TV n (TV n M (Fin m)) (Fin 1))) = lift x * lift y := by
      refine LinearMap.ext fun v => ?_
      funext J
      simp [lift]
    rw [hs, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ex,
      LinearMap.comp_assoc, ey, LinearMap.comp_assoc]

/- English proof (translation)
Use `LinearMap.ext fun v => funext fun I => ?_` and prove the remaining obligations. Simplify `LinearMap.congr_fun h (v I)` using `[lift]`.
-/
private theorem pmap_lift_lemma {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {P : Type} (f : V →ₗ[ℂ] W) (X : Module.End ℂ V) (Y : Module.End ℂ W) (h : f ∘ₗ X = Y ∘ₗ f) :
    (LinearMap.pi fun I : P → Fin n => f ∘ₗ LinearMap.proj I) ∘ₗ lift X =
      lift Y ∘ₗ (LinearMap.pi fun I : P → Fin n => f ∘ₗ LinearMap.proj I) := by
  refine LinearMap.ext fun v => funext fun I => ?_
  simpa [lift] using LinearMap.congr_fun h (v I)

/- English proof (translation)
Use `LinearMap.ext fun v => funext fun I => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases h : I p = a <;> simp [eAt, h]`.
-/
private theorem pmap_eAt_lemma_2 {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {P : Type} [DecidableEq P] (f : V →ₗ[ℂ] W) (p : P) (a b : Fin n) :
    (LinearMap.pi fun I : P → Fin n => f ∘ₗ LinearMap.proj I) ∘ₗ eAt p a b =
      eAt p a b ∘ₗ (LinearMap.pi fun I : P → Fin n => f ∘ₗ LinearMap.proj I) := by
  refine LinearMap.ext fun v => funext fun I => ?_
  by_cases h : I p = a <;> simp [eAt, h]

/- English proof (translation)
Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `only [Om, LinearMap.comp_apply, LinearMap.sum_apply, map_sum, Module.End.mul_apply]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Establish `hA` using `LinearMap.congr_fun (pmap_lift_lemma (P := P) f _ _ (h a b)) (eAt p b a v)`. Establish `hB` using `LinearMap.congr_fun (pmap_eAt_lemma_2 f p b a) v`.

Simplify using `only [LinearMap.comp_apply] at hA hB`. Rewrite using `[hA, hB]`.
-/
private theorem pmap_Om_lemma_3 {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {P : Type} [DecidableEq P] (f : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b, f ∘ₗ E a b = F a b ∘ₗ f) (p : P) :
    (LinearMap.pi fun I : P → Fin n => f ∘ₗ LinearMap.proj I) ∘ₗ Om E p =
      Om F p ∘ₗ (LinearMap.pi fun I : P → Fin n => f ∘ₗ LinearMap.proj I) := by
  refine LinearMap.ext fun v => ?_
  simp only [Om, LinearMap.comp_apply, LinearMap.sum_apply, map_sum, Module.End.mul_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hA := LinearMap.congr_fun (pmap_lift_lemma (P := P) f _ _ (h a b)) (eAt p b a v)
  have hB := LinearMap.congr_fun (pmap_eAt_lemma_2 f p b a) v
  simp only [LinearMap.comp_apply] at hA hB
  rw [hA, hB]

/- English proof (translation)
Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `only [tE, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sum_apply, map_sum, map_add]`. Establish `hA` using `LinearMap.congr_fun (pmap_lift_lemma (P := P) f _ _ (h a b)) v`. Simplify using `only [LinearMap.comp_apply] at hA`. Rewrite using `[hA]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Establish `hB` using `LinearMap.congr_fun (pmap_eAt_lemma_2 f p a b) v`. Simplify `hB` using `only [LinearMap.comp_apply]`.
-/
private theorem pmap_tE_lemma_4 {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {P : Type} [DecidableEq P] (S : Finset P) (f : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b, f ∘ₗ E a b = F a b ∘ₗ f) (a b : Fin n) :
    (LinearMap.pi fun I : P → Fin n => f ∘ₗ LinearMap.proj I) ∘ₗ tE S E a b =
      tE S F a b ∘ₗ (LinearMap.pi fun I : P → Fin n => f ∘ₗ LinearMap.proj I) := by
  refine LinearMap.ext fun v => ?_
  simp only [tE, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sum_apply, map_sum, map_add]
  have hA := LinearMap.congr_fun (pmap_lift_lemma (P := P) f _ _ (h a b)) v
  simp only [LinearMap.comp_apply] at hA
  rw [hA]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  have hB := LinearMap.congr_fun (pmap_eAt_lemma_2 f p a b) v
  simpa only [LinearMap.comp_apply] using hB

/- English proof (translation)
Take `⟨g, hG⟩` from `ih`. Unfold `Good at hG ⊢`. Take `⟨hgA, hg0, hgj, hgq⟩` from `hG`. Take `⟨hE'gl, -, -, -⟩` from `hT n M (Fin m) E hE Finset.univ`. Use `set E' : Fin n → Fin n → Module.End ℂ (TV n M (Fin m)) := tE (Finset.univ : Finset (Fin m)) E with hEe`.

Establish `hgc : ∀ a b, Commute g (E' a b)` using `fun a b => adjoin_commute _ _ (by rintro x ⟨j, rfl⟩; exact xJ_comm hT E hE m j a b) g hgA`. Use `set ℓ' : TV n M (Fin m) →ₗ[ℂ] ℂ := ℓ ∘ₗ LinearMap.proj (fun _ : Fin m => top) ∘ₗ g with hℓe`. Use `set l' : Fin n → ℂ := fun k => l k + ((Finset.univ.filter fun p : Fin m => (co ∘ Fin.castSucc) p = k).card : ℂ) with hl'`. Establish `hq' : ∀ u, ℓ' ∘ₗ qdet E' u = (∏ k, (u + l' k)) • ℓ'`. Introduce `u`.

Rewrite using `[hgq u]`. Use `congr 1`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [hl']`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨N0, F0, hF0gl, -, hF0ch, hF0int, hN0⟩` from `hW n (TV n M (Fin m)) Unit (fun _ => E') (fun _ => hE'gl) (fun τ τ' h => absurd (Subsingleton.elim τ τ') h) (fun _ => l') ℓ' (fun _ u => hq' u)`. Establish `hFgl : GlRel (F0 ())` using `hF0gl ()`. Establish `hFch : HasChar (F0 ()) l'` using `hF0ch ()`. Establish `hFint : ∀ a b, N0.mkQ ∘ₗ E' a b = F0 () a b ∘ₗ N0.mkQ` using `hF0int ()`. Establish `hN0le : N0 ≤ LinearMap.ker ℓ'`.

Introduce `y hy`. Use `(hN0 y).1 hy 1 (Subalgebra.one_mem _)` as an intermediate fact. Simplify using `using this`. Use `set ψ := N0.liftQ ℓ' hN0le with hψe`. Establish `hψapp : ∀ z, ψ (N0.mkQ z) = ℓ' z` using `fun z => by`.

Rewrite using `[hψe]`. Conclude with `Submodule.liftQ_apply _ _ _`. Take `⟨-, -, hWhm⟩` from `hH n M E hE ℓ hWh top htop`. Take `⟨ψs, hψ1, hψ2, hψs⟩` from `hWhm m`. Establish `hψWh : IsWh (F0 ()) ψ`.

Use `⟨ψs, hψ1, hψ2, fun a b hab => ?_⟩` and prove the remaining obligations. Apply `Submodule.linearMap_qext N0` to reduce the goal to its premises. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Establish `hFy` using `LinearMap.congr_fun (hFint a b) y`. Simplify using `only [LinearMap.comp_apply, LinearMap.smul_apply] at hFy ⊢`.

Rewrite using `[← hFy, hψapp, hψapp]`. Establish `h1` using `LinearMap.congr_fun (hψs a b hab) (g y)`. Establish `h2` using `LinearMap.congr_fun (hgc a b).eq y`. Simplify using `only [LinearMap.comp_apply, LinearMap.smul_apply, Module.End.mul_apply] at h1 h2`. Simplify using `only [hℓe, LinearMap.comp_apply]`.

Rewrite using `[h2]`. Conclude with `h1`. Establish `hψ0 : ψ ≠ 0`. Introduce `h`. Apply `hg0` to reduce the goal to its premises.

Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Use `hψapp y` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `using this.symm`. Take `⟨-, hnv, -⟩` from `hH n (TV n M (Fin m) ⧸ N0) (F0 ()) hFgl ψ hψWh top htop`.

Take `⟨hkill, hSq⟩` from `hS n (TV n M (Fin m) ⧸ N0) (F0 ()) hFgl l' hFch`. Use `set L := (List.ofFn l').erase (l' (co (Fin.last m))) with hL`. Establish `hLlen : L.length = top`. Simplify using `only [hL]`. Rewrite using `[List.length_erase_of_mem (by simp), List.length_ofFn]`.

Use linear arithmetic over natural numbers and integers. Use `set Om' := Om E' (0 : Fin 1) with hOm'`. Use `set OmF := Om (F0 ()) (0 : Fin 1) with hOmF`. Use `set PE : Module.End ℂ (TV n (TV n M (Fin m)) (Fin 1)) := (L.map fun r => Om' - algebraMap ℂ _ r).prod with hPE`. Use `set PF : Module.End ℂ (TV n (TV n M (Fin m) ⧸ N0) (Fin 1)) := (L.map fun r => OmF - algebraMap ℂ _ r).prod with hPF`.

Use `set Q : TV n (TV n M (Fin m)) (Fin 1) →ₗ[ℂ] TV n (TV n M (Fin m) ⧸ N0) (Fin 1) := LinearMap.pi fun I : Fin 1 → Fin n => N0.mkQ ∘ₗ LinearMap.proj I with hQ`. Establish `hQOm : Q ∘ₗ Om' = OmF ∘ₗ Q` using `pmap_Om_lemma_3 N0.mkQ E' (F0 ()) hFint 0`. Establish `hQP : Q ∘ₗ PE = PF ∘ₗ Q` using `listSub_comp Q Om' OmF hQOm L`. Establish `hQsurj : Function.Surjective Q`. Introduce `y`.

Use `⟨fun I => (N0.mkQ_surjective (y I)).choose, funext fun I => ?_⟩` and prove the remaining obligations. Conclude with `(N0.mkQ_surjective (y I)).choose_spec`. Establish `hΦ : ∀ z, ℓ' (PE z (fun _ => top)) = ψ (PF (Q z) (fun _ => top))`. Introduce `z`. Establish `h` using `LinearMap.congr_fun hQP z`.

Simplify using `only [LinearMap.comp_apply] at h`. Rewrite using `[← h]`. Conclude with `(hψapp (PE z fun _ => top)).symm`. Take `⟨hcb, hctE, hccast, hcnat, -, -, -⟩` from `hC n M E m 1`. Establish `hnat : Fin.natAdd m (0 : Fin 1) = Fin.last m` using `Fin.ext (by simp)`.

Establish `hxJ0 : xJ E' (0 : Fin 1) = Om'`. Simplify using `[xJ, hOm']`. Establish `hcurX : curF n M m 1 ∘ₗ xJ E (Fin.last m) = Om' ∘ₗ curF n M m 1`. Use `hcnat 0` as an intermediate fact. Rewrite `this` using `[hnat, hxJ0]`.

Conclude with `this`. Take `⟨g1, hg1A, hg1⟩` from `liftAdj hC E m g hgA`. Establish `hcurP : curF n M m 1 ∘ₗ (L.map fun r => xJ E (Fin.last m) - algebraMap ℂ (Module.End ℂ (TV n M (Fin (m + 1)))) r).prod = PE ∘ₗ curF n M m 1` using `listSub_comp _ _ _ hcurX L`. Establish `hliftP : ∀ X : Module.End ℂ (TV n M (Fin m)), (∀ a b, Commute X (E' a b)) → ∀ w, PE (lift X w) = lift X (PE w)`. Introduce `X hX w`.

Establish `h1 : Commute (lift X : Module.End ℂ (TV n (TV n M (Fin m)) (Fin 1))) Om'` using `pmap_Om_lemma_3 (P := Fin 1) X E' E' (fun a b => (hX a b).eq) 0`. Establish `h2` using `LinearMap.congr_fun (listSub_commute Om' (lift X) h1.symm L).eq w`. Simplify `h2` using `only [Module.End.mul_apply]`. Establish `happend : ∀ y : TV n M (Fin (m + 1)), y (fun _ => top) = curF n M m 1 y (fun _ => top) (fun _ => top)`. Introduce `y`.

Simplify using `only [curF, LinearMap.pi_apply, LinearMap.proj_apply]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp`. Establish `hφ : ∀ x, ℓ (((L.map fun r => xJ E (Fin.last m) - algebraMap ℂ (Module.End ℂ (TV n M (Fin (m + 1)))) r).prod * g1) x (fun _ => top)) = ℓ' (PE (curF n M m 1 x) (fun _ => top))`.

Introduce `x`. Establish `h1` using `LinearMap.congr_fun hcurP (g1 x)`. Establish `h2` using `LinearMap.congr_fun hg1 x`. Simplify using `only [LinearMap.comp_apply] at h1 h2`. Use `(congrArg ℓ (happend _)).trans ?_` and prove the remaining obligations.

Rewrite using `[Module.End.mul_apply, h1, h2, hliftP g hgc]`. Both sides reduce to the same expression. Establish `hkill' : PF * (OmF - algebraMap ℂ _ (l' (co (Fin.last m)))) = 0` using `listSub_kill OmF l' (co (Fin.last m)) hkill`. Establish `hlastkey : ∀ w, ℓ' (PE (Om' w) (fun _ => top)) = l' (co (Fin.last m)) • ℓ' (PE w (fun _ => top))`. Introduce `w`.

Establish `e1 : PE (Om' w) - l' (co (Fin.last m)) • PE w = PE (Om' w - l' (co (Fin.last m)) • w)`. Rewrite using `[map_sub, map_smul]`. Establish `e2 : Q (Om' w - l' (co (Fin.last m)) • w) = (OmF - algebraMap ℂ _ (l' (co (Fin.last m)))) (Q w)`. Use `LinearMap.congr_fun hQOm w` as an intermediate fact. Simplify using `only [LinearMap.comp_apply] at this`.

Rewrite using `[map_sub, map_smul, this, LinearMap.sub_apply, Module.algebraMap_end_apply]`. Establish `e3 : PF ((OmF - algebraMap ℂ _ (l' (co (Fin.last m)))) (Q w)) = 0`. Use `LinearMap.congr_fun hkill' (Q w)` as an intermediate fact. Simplify `this` using `only [Module.End.mul_apply, LinearMap.zero_apply]`. Establish `e4 : ℓ' (PE (Om' w - l' (co (Fin.last m)) • w) (fun _ => top)) = 0`.

Rewrite using `[hΦ, e2, e3]`. Simplify using the standard rewrite rules. Rewrite `e4` using `[← e1]`. Establish `e5 : (PE (Om' w) - l' (co (Fin.last m)) • PE w) (fun _ => top) = PE (Om' w) (fun _ => top) - l' (co (Fin.last m)) • PE w (fun _ => top)` using `rfl`. Rewrite `e4` using `[e5, map_sub, map_smul, sub_eq_zero]`.

Conclude with `e4`. Take `⟨hTFgl, hOmFc, -, -⟩` from `hT n (TV n M (Fin m) ⧸ N0) (Fin 1) (F0 ()) hFgl Finset.univ`. Establish `hPFtE : ∀ a b, PF ∘ₗ tE Finset.univ (F0 ()) a b = tE Finset.univ (F0 ()) a b ∘ₗ PF` using `fun a b => (listSub_commute _ _ (hOmFc 0 (Finset.mem_univ _) a b) L).eq`. Establish `hWinv : ∀ a b, ∀ w ∈ LinearMap.range PF, tE Finset.univ (F0 ()) a b w ∈ LinearMap.range PF`. Introduce and unpack `a b _ ⟨y, rfl⟩`.

Use `⟨tE Finset.univ (F0 ()) a b y, ?_⟩` and prove the remaining obligations. Use `LinearMap.congr_fun (hPFtE a b) y` as an intermediate fact. Simplify `this` using `only [LinearMap.comp_apply]`. Establish `hOO` using `LinearMap.congr_fun (listSub_commute OmF OmF (Commute.refl _) L).eq`. Establish `hWO : ∀ w ∈ LinearMap.range PF, OmF w ∈ LinearMap.range PF`.

Introduce and unpack `_ ⟨y, rfl⟩`. Use `⟨OmF y, ?_⟩` and prove the remaining obligations. Simplify `hOO y` using `only [Module.End.mul_apply]`. Establish `hWsc : ∀ y, OmF (PF y) = l' (co (Fin.last m)) • PF y`. Introduce `y`.

Establish `h1` using `LinearMap.congr_fun hkill' y`. Establish `h2` using `hOO y`. Simplify using `only [Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply, map_sub, map_smul, LinearMap.zero_apply] at h1 h2`. Rewrite using `[← h2]`. Conclude with `sub_eq_zero.mp h1`.

Establish `hFW` using `hSq (LinearMap.range PF) (LinearMap.range PF) (fun a b => (tE Finset.univ (F0 ()) a b).restrict (hWinv a b)) LinearMap.id hWinv hWO (co (Fin.last m)) Function.surjective_id (fun a b w => rfl) (fun w => by`. Take `⟨_, y, rfl⟩` from `w`. Conclude with `Subtype.ext (hWsc y))`. Establish `hWchar : ∀ u y, qdet (tE Finset.univ (F0 ())) u (PF y) = (∏ k, (u + Function.update l' (co (Fin.last m)) (l' (co (Fin.last m)) + 1) k)) • PF y`. Introduce `u y`.

Establish `hsub` using `LinearMap.congr_fun (qdet_comp (LinearMap.range PF).subtype (fun a b => (tE Finset.univ (F0 ()) a b).restrict (hWinv a b)) (tE Finset.univ (F0 ())) (fun a b => LinearMap.ext fun w => rfl) u) ⟨PF y, y, rfl⟩`. Simplify using `only [LinearMap.comp_apply] at hsub`. Rewrite `hsub` using `[hFW u]`. Simplify using `using hsub.symm`. Use `⟨(L.map fun r => xJ E (Fin.last m) - algebraMap ℂ (Module.End ℂ (TV n M (Fin (m + 1)))) r).prod * g1, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `Subalgebra.mul_mem _ (list_prod_mem ?_) hg1A` and prove the remaining obligations. Introduce `x hx`. Take `⟨r, -, rfl⟩` from `List.mem_map.mp hx`. Conclude with `Subalgebra.sub_mem _ (Algebra.subset_adjoin ⟨Fin.last m, rfl⟩) (Subalgebra.algebraMap_mem _ r)`. Introduce `h0`.

Apply `hnv hψ0 L hLlen` to reduce the goal to its premises. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Take `⟨z, rfl⟩` from `hQsurj v`. Take `⟨x, rfl⟩` from `hcb.2 z`. Use `LinearMap.congr_fun h0 x` as an intermediate fact.

Simplify using `only [LinearMap.comp_apply, LinearMap.zero_apply, LinearMap.proj_apply] at this ⊢`. Rewrite using `[← hΦ, ← hφ]`. Conclude with `this`. Introduce `j`. Consider the cases of `j using Fin.lastCases with`.

Consider the case `last`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.proj_apply]`. Rewrite using `[hφ, hφ]`. Establish `hx` using `LinearMap.congr_fun hcurX x`.

Simplify using `only [LinearMap.comp_apply] at hx`. Rewrite using `[hx, hlastkey, card2]`. Consider the case `cast i`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.proj_apply]`.

Rewrite using `[hφ, hφ]`. Establish `hx` using `LinearMap.congr_fun (hccast i) x`. Simplify using `only [LinearMap.comp_apply] at hx`. Rewrite using `[card1, show Fin.castSucc i = Fin.castAdd 1 i from rfl, hx, hliftP (xJ E i) (fun a b => xJ_comm hT E hE m i a b)]`. Establish `hj` using `LinearMap.congr_fun (hgj i) (PE (curF n M m 1 x) (fun _ => top))`.

Simplify using `only [LinearMap.comp_apply, LinearMap.smul_apply] at hj`. Conclude with `hj`. Introduce `u`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.proj_apply]`.

Rewrite using `[hφ, hφ]`. Establish `hq1` using `LinearMap.congr_fun (qdet_comp (curF n M m 1) _ _ hctE u) x`. Simplify using `only [LinearMap.comp_apply] at hq1`. Rewrite using `[hq1, hΦ, hΦ]`. Establish `hq2` using `LinearMap.congr_fun (qdet_comp Q _ _ (pmap_tE_lemma_4 Finset.univ N0.mkQ E' (F0 ()) hFint) u) (curF n M m 1 x)`.

Simplify using `only [LinearMap.comp_apply] at hq2`. Rewrite using `[hq2]`. Establish `hq3` using `LinearMap.congr_fun (qdet_comp PF _ _ hPFtE u) (Q (curF n M m 1 x))`. Simplify using `only [LinearMap.comp_apply] at hq3`. Rewrite using `[hq3, hWchar, Pi.smul_apply, map_smul]`.

Use `congr 1`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[card3]`. Distinguish the cases in `hk : k = co (Fin.last m)`. Substitute `hk` using the available equality.

Simplify using `only [Function.update_self, if_true, hl']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Function.update_of_ne hk, if_neg (Ne.symm hk)]`. Simplify using `only [hl']`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem step (hT : TensorGl) (hC : Curry) (hS : StepChar) (hH : Height) (hW : WallQuot)
    (E : Fin n → Fin n → Module.End ℂ M) (hE : GlRel E) (l : Fin n → ℂ) (ℓ : M →ₗ[ℂ] ℂ)
    (hWh : IsWh E ℓ) (top : Fin n) (htop : (top : ℕ) + 1 = n) (m : ℕ) (co : Fin (m + 1) → Fin n)
    (ih : ∃ g, Good E l ℓ top m (co ∘ Fin.castSucc) g) : ∃ g, Good E l ℓ top (m + 1) co g := by
  obtain ⟨g, hG⟩ := ih
  unfold Good at hG ⊢
  obtain ⟨hgA, hg0, hgj, hgq⟩ := hG
  obtain ⟨hE'gl, -, -, -⟩ := hT n M (Fin m) E hE Finset.univ
  set E' : Fin n → Fin n → Module.End ℂ (TV n M (Fin m)) := tE (Finset.univ : Finset (Fin m)) E with hEe
  have hgc : ∀ a b, Commute g (E' a b) := fun a b =>
    adjoin_commute _ _ (by rintro x ⟨j, rfl⟩; exact xJ_comm hT E hE m j a b) g hgA
  set ℓ' : TV n M (Fin m) →ₗ[ℂ] ℂ := ℓ ∘ₗ LinearMap.proj (fun _ : Fin m => top) ∘ₗ g with hℓe
  set l' : Fin n → ℂ := fun k =>
    l k + ((Finset.univ.filter fun p : Fin m => (co ∘ Fin.castSucc) p = k).card : ℂ) with hl'
  have hq' : ∀ u, ℓ' ∘ₗ qdet E' u = (∏ k, (u + l' k)) • ℓ' := by
    intro u
    rw [hgq u]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [hl']
    ring
  obtain ⟨N0, F0, hF0gl, -, hF0ch, hF0int, hN0⟩ := hW n (TV n M (Fin m)) Unit (fun _ => E')
    (fun _ => hE'gl) (fun τ τ' h => absurd (Subsingleton.elim τ τ') h) (fun _ => l') ℓ' (fun _ u => hq' u)
  have hFgl : GlRel (F0 ()) := hF0gl ()
  have hFch : HasChar (F0 ()) l' := hF0ch ()
  have hFint : ∀ a b, N0.mkQ ∘ₗ E' a b = F0 () a b ∘ₗ N0.mkQ := hF0int ()
  have hN0le : N0 ≤ LinearMap.ker ℓ' := by
    intro y hy
    have := (hN0 y).1 hy 1 (Subalgebra.one_mem _)
    simpa using this
  set ψ := N0.liftQ ℓ' hN0le with hψe
  have hψapp : ∀ z, ψ (N0.mkQ z) = ℓ' z := fun z => by
    rw [hψe]
    exact Submodule.liftQ_apply _ _ _
  obtain ⟨-, -, hWhm⟩ := hH n M E hE ℓ hWh top htop
  obtain ⟨ψs, hψ1, hψ2, hψs⟩ := hWhm m
  have hψWh : IsWh (F0 ()) ψ := by
    refine ⟨ψs, hψ1, hψ2, fun a b hab => ?_⟩
    apply Submodule.linearMap_qext N0
    refine LinearMap.ext fun y => ?_
    have hFy := LinearMap.congr_fun (hFint a b) y
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hFy ⊢
    rw [← hFy, hψapp, hψapp]
    have h1 := LinearMap.congr_fun (hψs a b hab) (g y)
    have h2 := LinearMap.congr_fun (hgc a b).eq y
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Module.End.mul_apply] at h1 h2
    simp only [hℓe, LinearMap.comp_apply]
    rw [h2]
    exact h1
  have hψ0 : ψ ≠ 0 := by
    intro h
    apply hg0
    refine LinearMap.ext fun y => ?_
    have := hψapp y
    rw [h] at this
    simpa using this.symm
  obtain ⟨-, hnv, -⟩ := hH n (TV n M (Fin m) ⧸ N0) (F0 ()) hFgl ψ hψWh top htop
  obtain ⟨hkill, hSq⟩ := hS n (TV n M (Fin m) ⧸ N0) (F0 ()) hFgl l' hFch
  set L := (List.ofFn l').erase (l' (co (Fin.last m))) with hL
  have hLlen : L.length = top := by
    simp only [hL]
    rw [List.length_erase_of_mem (by simp), List.length_ofFn]
    omega
  set Om' := Om E' (0 : Fin 1) with hOm'
  set OmF := Om (F0 ()) (0 : Fin 1) with hOmF
  set PE : Module.End ℂ (TV n (TV n M (Fin m)) (Fin 1)) :=
    (L.map fun r => Om' - algebraMap ℂ _ r).prod with hPE
  set PF : Module.End ℂ (TV n (TV n M (Fin m) ⧸ N0) (Fin 1)) :=
    (L.map fun r => OmF - algebraMap ℂ _ r).prod with hPF
  set Q : TV n (TV n M (Fin m)) (Fin 1) →ₗ[ℂ] TV n (TV n M (Fin m) ⧸ N0) (Fin 1) :=
    LinearMap.pi fun I : Fin 1 → Fin n => N0.mkQ ∘ₗ LinearMap.proj I with hQ
  have hQOm : Q ∘ₗ Om' = OmF ∘ₗ Q := pmap_Om_lemma_3 N0.mkQ E' (F0 ()) hFint 0
  have hQP : Q ∘ₗ PE = PF ∘ₗ Q := listSub_comp Q Om' OmF hQOm L
  have hQsurj : Function.Surjective Q := by
    intro y
    refine ⟨fun I => (N0.mkQ_surjective (y I)).choose, funext fun I => ?_⟩
    exact (N0.mkQ_surjective (y I)).choose_spec
  have hΦ : ∀ z, ℓ' (PE z (fun _ => top)) = ψ (PF (Q z) (fun _ => top)) := by
    intro z
    have h := LinearMap.congr_fun hQP z
    simp only [LinearMap.comp_apply] at h
    rw [← h]
    exact (hψapp (PE z fun _ => top)).symm
  obtain ⟨hcb, hctE, hccast, hcnat, -, -, -⟩ := hC n M E m 1
  have hnat : Fin.natAdd m (0 : Fin 1) = Fin.last m := Fin.ext (by simp)
  have hxJ0 : xJ E' (0 : Fin 1) = Om' := by
    simp [xJ, hOm']
  have hcurX : curF n M m 1 ∘ₗ xJ E (Fin.last m) = Om' ∘ₗ curF n M m 1 := by
    have := hcnat 0
    rw [hnat, hxJ0] at this
    exact this
  obtain ⟨g1, hg1A, hg1⟩ := liftAdj hC E m g hgA
  have hcurP : curF n M m 1 ∘ₗ (L.map fun r => xJ E (Fin.last m) -
      algebraMap ℂ (Module.End ℂ (TV n M (Fin (m + 1)))) r).prod = PE ∘ₗ curF n M m 1 :=
    listSub_comp _ _ _ hcurX L
  have hliftP : ∀ X : Module.End ℂ (TV n M (Fin m)), (∀ a b, Commute X (E' a b)) →
      ∀ w, PE (lift X w) = lift X (PE w) := by
    intro X hX w
    have h1 : Commute (lift X : Module.End ℂ (TV n (TV n M (Fin m)) (Fin 1))) Om' :=
      pmap_Om_lemma_3 (P := Fin 1) X E' E' (fun a b => (hX a b).eq) 0
    have h2 := LinearMap.congr_fun (listSub_commute Om' (lift X) h1.symm L).eq w
    simpa only [Module.End.mul_apply] using h2
  have happend : ∀ y : TV n M (Fin (m + 1)),
      y (fun _ => top) = curF n M m 1 y (fun _ => top) (fun _ => top) := by
    intro y
    simp only [curF, LinearMap.pi_apply, LinearMap.proj_apply]
    congr 1
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp
  have hφ : ∀ x, ℓ (((L.map fun r => xJ E (Fin.last m) -
      algebraMap ℂ (Module.End ℂ (TV n M (Fin (m + 1)))) r).prod * g1) x (fun _ => top)) =
      ℓ' (PE (curF n M m 1 x) (fun _ => top)) := by
    intro x
    have h1 := LinearMap.congr_fun hcurP (g1 x)
    have h2 := LinearMap.congr_fun hg1 x
    simp only [LinearMap.comp_apply] at h1 h2
    refine (congrArg ℓ (happend _)).trans ?_
    rw [Module.End.mul_apply, h1, h2, hliftP g hgc]
    rfl
  have hkill' : PF * (OmF - algebraMap ℂ _ (l' (co (Fin.last m)))) = 0 :=
    listSub_kill OmF l' (co (Fin.last m)) hkill
  have hlastkey : ∀ w, ℓ' (PE (Om' w) (fun _ => top)) =
      l' (co (Fin.last m)) • ℓ' (PE w (fun _ => top)) := by
    intro w
    have e1 : PE (Om' w) - l' (co (Fin.last m)) • PE w = PE (Om' w - l' (co (Fin.last m)) • w) := by
      rw [map_sub, map_smul]
    have e2 : Q (Om' w - l' (co (Fin.last m)) • w) =
        (OmF - algebraMap ℂ _ (l' (co (Fin.last m)))) (Q w) := by
      have := LinearMap.congr_fun hQOm w
      simp only [LinearMap.comp_apply] at this
      rw [map_sub, map_smul, this, LinearMap.sub_apply, Module.algebraMap_end_apply]
    have e3 : PF ((OmF - algebraMap ℂ _ (l' (co (Fin.last m)))) (Q w)) = 0 := by
      have := LinearMap.congr_fun hkill' (Q w)
      simpa only [Module.End.mul_apply, LinearMap.zero_apply] using this
    have e4 : ℓ' (PE (Om' w - l' (co (Fin.last m)) • w) (fun _ => top)) = 0 := by
      rw [hΦ, e2, e3]
      simp
    rw [← e1] at e4
    have e5 : (PE (Om' w) - l' (co (Fin.last m)) • PE w) (fun _ => top) =
        PE (Om' w) (fun _ => top) - l' (co (Fin.last m)) • PE w (fun _ => top) := rfl
    rw [e5, map_sub, map_smul, sub_eq_zero] at e4
    exact e4
  obtain ⟨hTFgl, hOmFc, -, -⟩ := hT n (TV n M (Fin m) ⧸ N0) (Fin 1) (F0 ()) hFgl Finset.univ
  have hPFtE : ∀ a b, PF ∘ₗ tE Finset.univ (F0 ()) a b = tE Finset.univ (F0 ()) a b ∘ₗ PF :=
    fun a b => (listSub_commute _ _ (hOmFc 0 (Finset.mem_univ _) a b) L).eq
  have hWinv : ∀ a b, ∀ w ∈ LinearMap.range PF, tE Finset.univ (F0 ()) a b w ∈ LinearMap.range PF := by
    rintro a b _ ⟨y, rfl⟩
    refine ⟨tE Finset.univ (F0 ()) a b y, ?_⟩
    have := LinearMap.congr_fun (hPFtE a b) y
    simpa only [LinearMap.comp_apply] using this
  have hOO := LinearMap.congr_fun (listSub_commute OmF OmF (Commute.refl _) L).eq
  have hWO : ∀ w ∈ LinearMap.range PF, OmF w ∈ LinearMap.range PF := by
    rintro _ ⟨y, rfl⟩
    refine ⟨OmF y, ?_⟩
    simpa only [Module.End.mul_apply] using hOO y
  have hWsc : ∀ y, OmF (PF y) = l' (co (Fin.last m)) • PF y := by
    intro y
    have h1 := LinearMap.congr_fun hkill' y
    have h2 := hOO y
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply, map_sub, map_smul,
      LinearMap.zero_apply] at h1 h2
    rw [← h2]
    exact sub_eq_zero.mp h1
  have hFW := hSq (LinearMap.range PF) (LinearMap.range PF)
    (fun a b => (tE Finset.univ (F0 ()) a b).restrict (hWinv a b)) LinearMap.id hWinv hWO (co (Fin.last m))
    Function.surjective_id (fun a b w => rfl) (fun w => by
      obtain ⟨_, y, rfl⟩ := w
      exact Subtype.ext (hWsc y))
  have hWchar : ∀ u y, qdet (tE Finset.univ (F0 ())) u (PF y) =
      (∏ k, (u + Function.update l' (co (Fin.last m)) (l' (co (Fin.last m)) + 1) k)) • PF y := by
    intro u y
    have hsub := LinearMap.congr_fun (qdet_comp (LinearMap.range PF).subtype
      (fun a b => (tE Finset.univ (F0 ()) a b).restrict (hWinv a b)) (tE Finset.univ (F0 ()))
      (fun a b => LinearMap.ext fun w => rfl) u) ⟨PF y, y, rfl⟩
    simp only [LinearMap.comp_apply] at hsub
    rw [hFW u] at hsub
    simpa using hsub.symm
  refine ⟨(L.map fun r => xJ E (Fin.last m) -
      algebraMap ℂ (Module.End ℂ (TV n M (Fin (m + 1)))) r).prod * g1, ?_, ?_, ?_, ?_⟩
  · refine Subalgebra.mul_mem _ (list_prod_mem ?_) hg1A
    intro x hx
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
    exact Subalgebra.sub_mem _ (Algebra.subset_adjoin ⟨Fin.last m, rfl⟩) (Subalgebra.algebraMap_mem _ r)
  · intro h0
    apply hnv hψ0 L hLlen
    refine LinearMap.ext fun v => ?_
    obtain ⟨z, rfl⟩ := hQsurj v
    obtain ⟨x, rfl⟩ := hcb.2 z
    have := LinearMap.congr_fun h0 x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, LinearMap.proj_apply] at this ⊢
    rw [← hΦ, ← hφ]
    exact this
  · intro j
    cases j using Fin.lastCases with
    | last =>
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.proj_apply]
      rw [hφ, hφ]
      have hx := LinearMap.congr_fun hcurX x
      simp only [LinearMap.comp_apply] at hx
      rw [hx, hlastkey, card2]
    | cast i =>
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.proj_apply]
      rw [hφ, hφ]
      have hx := LinearMap.congr_fun (hccast i) x
      simp only [LinearMap.comp_apply] at hx
      rw [card1, show Fin.castSucc i = Fin.castAdd 1 i from rfl, hx,
        hliftP (xJ E i) (fun a b => xJ_comm hT E hE m i a b)]
      have hj := LinearMap.congr_fun (hgj i) (PE (curF n M m 1 x) (fun _ => top))
      simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hj
      exact hj
  · intro u
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.proj_apply]
    rw [hφ, hφ]
    have hq1 := LinearMap.congr_fun (qdet_comp (curF n M m 1) _ _ hctE u) x
    simp only [LinearMap.comp_apply] at hq1
    rw [hq1, hΦ, hΦ]
    have hq2 := LinearMap.congr_fun (qdet_comp Q _ _
      (pmap_tE_lemma_4 Finset.univ N0.mkQ E' (F0 ()) hFint) u) (curF n M m 1 x)
    simp only [LinearMap.comp_apply] at hq2
    rw [hq2]
    have hq3 := LinearMap.congr_fun (qdet_comp PF _ _ hPFtE u) (Q (curF n M m 1 x))
    simp only [LinearMap.comp_apply] at hq3
    rw [hq3, hWchar, Pi.smul_apply, map_smul]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [card3]
    by_cases hk : k = co (Fin.last m)
    · subst hk
      simp only [Function.update_self, if_true, hl']
      push_cast
      ring
    · rw [Function.update_of_ne hk, if_neg (Ne.symm hk)]
      simp only [hl']
      push_cast
      ring

end ChainP

/- English proof (translation)
Introduce `hT _ hC _ _ hS hH hW n M _ _ E hE l hl ℓ hℓ hWh top htop m`. Proceed by induction on `m with`. Consider the case `zero => intro co`. Conclude with `⟨1, ChainP.base E l hl ℓ hℓ top co⟩`. Consider the case `succ m ih`.

Introduce `co`. Conclude with `ChainP.step hT hC hS hH hW E hE l ℓ hWh top htop m co (ih (co ∘ Fin.castSucc))`.
-/
theorem chain_of : TensorGl → JMComm → Curry → StepFormula → QdetFacts → StepChar → Height → WallQuot →
    Chain := by
  intro hT _ hC _ _ hS hH hW n M _ _ E hE l hl ℓ hℓ hWh top htop m
  induction m with
  | zero => intro co; exact ⟨1, ChainP.base E l hl ℓ hℓ top co⟩
  | succ m ih =>
    intro co
    exact ChainP.step hT hC hS hH hW E hE l ℓ hWh top htop m co (ih (co ∘ Fin.castSucc))

end PositivityTheory.Rg.Cz

end
