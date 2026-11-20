import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

/- English proof (translation)
Establish `h : y ᵥ* inc e R = fun i => y (e i)`. Use extensionality with `i`. Simplify using `[inc, vecMul, dotProduct]`. Rewrite using `[coe_emb, vecMul_add, vecMul_one, ext0, ← vecMul_vecMul, ← vecMul_vecMul, h, vecMul_sub, vecMul_one]`.
-/
private theorem vecMul_emb {a n : ℕ} (e : Fin a ↪ Fin n) {R : Type} [CommRing R] (g : GL (Fin a) R) (y : Fin n → R) :
    y ᵥ* (emb e g).val = y + ((fun i => y (e i)) ᵥ* g.val - fun i => y (e i)) ᵥ* (inc e R)ᵀ := by
  have h : y ᵥ* inc e R = fun i => y (e i) := by
    ext i
    simp [inc, vecMul, dotProduct]
  rw [coe_emb, vecMul_add, vecMul_one, ext0, ← vecMul_vecMul, ← vecMul_vecMul, h, vecMul_sub, vecMul_one]

/- English proof (translation)
Establish `h` using `hg fun i => y (e i)`. Unfold `Reduction.euclidNorm at h ⊢`. Rewrite `h` using `[Real.sqrt_inj (by positivity) (by positivity)]`. Use `congr 1`. Rewrite using `[← Finset.sum_add_sum_compl (Finset.univ.map e), ← Finset.sum_add_sum_compl (Finset.univ.map e), Finset.sum_map, Finset.sum_map, ← h, vecMul_emb]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `: ∀ z : Fin a → R, (z ᵥ* (inc e R)ᵀ) (e j) = z j` using `fun z => by simp [inc, vecMul, dotProduct]`. Rewrite using `[Pi.add_apply, this, Pi.sub_apply, add_sub_cancel]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations.

Establish `hj' : ∀ k, j ≠ e k` using `fun k hk => by simp [hk] at hj`. Establish `: ∀ z : Fin a → R, (z ᵥ* (inc e R)ᵀ) j = 0` using `fun z => by simp [inc, vecMul, dotProduct, hj']`. Rewrite using `[Pi.add_apply, this, add_zero]`.
-/
private theorem norm_emb {a n : ℕ} (e : Fin a ↪ Fin n) {R : Type} [NormedField R] (g : GL (Fin a) R)
    (hg : ∀ y, Reduction.euclidNorm (y ᵥ* g.val) = Reduction.euclidNorm y) (y : Fin n → R) :
    Reduction.euclidNorm (y ᵥ* (emb e g).val) = Reduction.euclidNorm y := by
  have h := hg fun i => y (e i)
  unfold Reduction.euclidNorm at h ⊢
  rw [Real.sqrt_inj (by positivity) (by positivity)] at h
  congr 1
  rw [← Finset.sum_add_sum_compl (Finset.univ.map e), ← Finset.sum_add_sum_compl (Finset.univ.map e),
    Finset.sum_map, Finset.sum_map, ← h, vecMul_emb]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    have : ∀ z : Fin a → R, (z ᵥ* (inc e R)ᵀ) (e j) = z j := fun z => by simp [inc, vecMul, dotProduct]
    rw [Pi.add_apply, this, Pi.sub_apply, add_sub_cancel]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : ∀ k, j ≠ e k := fun k hk => by simp [hk] at hj
    have : ∀ z : Fin a → R, (z ᵥ* (inc e R)ᵀ) j = 0 := fun z => by simp [inc, vecMul, dotProduct, hj']
    rw [Pi.add_apply, this, add_zero]

/- English proof (translation)
Establish `h1 : g' = Matrix.GeneralLinearGroup.map f g` using `Units.ext (Matrix.ext hg)`. Establish `h2 : h' = Matrix.GeneralLinearGroup.map f (emb e g)` using `Units.ext (Matrix.ext hh)`. Rewrite using `[h1, h2, emb_map]`.
-/
private theorem emb_transfer {a n : ℕ} (e : Fin a ↪ Fin n) {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (g : GL (Fin a) R) (g' : GL (Fin a) S) (h' : GL (Fin n) S) (hg : ∀ i j, g'.val i j = f (g.val i j))
    (hh : ∀ i j, h'.val i j = f ((emb e g).val i j)) : h' = emb e g' := by
  have h1 : g' = Matrix.GeneralLinearGroup.map f g := Units.ext (Matrix.ext hg)
  have h2 : h' = Matrix.GeneralLinearGroup.map f (emb e g) := Units.ext (Matrix.ext hh)
  rw [h1, h2, emb_map]

/- English proof (translation)
Take `⟨u, rfl⟩` from `hg`. Conclude with `⟨emb e u, emb_transfer e (ValuativeRel.valuation F).integer.subtype u _ _ (fun _ _ => rfl) (fun _ _ => rfl)⟩`.
-/
private theorem int_emb {a n : ℕ} (e : Fin a ↪ Fin n) {F : Type} [Field F] [ValuativeRel F] (g : GL (Fin a) F)
    (hg : g ∈ GLnLocal.integralGL F a) : emb e g ∈ GLnLocal.integralGL F n := by
  obtain ⟨u, rfl⟩ := hg
  exact ⟨emb e u, emb_transfer e (ValuativeRel.valuation F).integer.subtype u _ _ (fun _ _ => rfl) (fun _ _ => rfl)⟩

/- English proof (translation)
Introduce `K _ _ a n e k hk`. Rewrite `hk`, the goal using `[Reduction.mem_maxCompact]`. Use `⟨fun w => ?_, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[emb_transfer e (Reduction.infEval w) k (Reduction.infAt w k) (Reduction.infAt w (emb e k)) (fun i j => Reduction.infAt_apply w k i j) (fun i j => Reduction.infAt_apply w _ i j), Reduction.mem_archCompact]`. Conclude with `norm_emb e _ (Reduction.mem_archCompact.1 (hk.1 w))`.

Rewrite using `[emb_transfer e (Reduction.finEval v) k (Reduction.finAt v k) (Reduction.finAt v (emb e k)) (fun i j => Reduction.finAt_apply v k i j) (fun i j => Reduction.finAt_apply v _ i j)]`. Conclude with `int_emb e _ (hk.2 v)`.
-/
theorem UpperTheory.blockEmbedding_adelic_norm_compat :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n), ∀ k ∈ Reduction.maxCompact (K := K) (n := a), emb e k ∈ Reduction.maxCompact (K := K) (n := n) := by
  intro K _ _ a n e k hk
  rw [Reduction.mem_maxCompact] at hk ⊢
  refine ⟨fun w => ?_, fun v => ?_⟩
  · rw [emb_transfer e (Reduction.infEval w) k (Reduction.infAt w k) (Reduction.infAt w (emb e k))
      (fun i j => Reduction.infAt_apply w k i j) (fun i j => Reduction.infAt_apply w _ i j), Reduction.mem_archCompact]
    exact norm_emb e _ (Reduction.mem_archCompact.1 (hk.1 w))
  · rw [emb_transfer e (Reduction.finEval v) k (Reduction.finAt v k) (Reduction.finAt v (emb e k))
      (fun i j => Reduction.finAt_apply v k i j) (fun i j => Reduction.finAt_apply v _ i j)]
    exact int_emb e _ (hk.2 v)
