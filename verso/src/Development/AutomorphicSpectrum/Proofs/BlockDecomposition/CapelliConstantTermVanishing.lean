import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapS

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Matrix Topology

namespace GlobalTheory.CompanionTheory.CTFin.CapStable

/- English proof (translation)
Use `S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)` and prove the remaining obligations. Take `⟨k, rfl⟩` from `List.mem_ofFn.1 hx`. Use `S.add_mem ?_ (h _ _)` and prove the remaining obligations. Use `split_ifs`. Conclude with `S.algebraMap_mem _`.

Conclude with `S.zero_mem`.
-/
theorem qdet_mem {a : ℕ} {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) (X : Fin a → Fin a → A)
    (h : ∀ i j, X i j ∈ S) (u : ℂ) : Formalism.REAL.qdet X u ∈ S := by
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (h _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

def blockM {R : Type} [CommRing R] {r s : ℕ} (A : Matrix (Fin r) (Fin r) R) (B : Matrix (Fin s) (Fin s) R) :
    Matrix (Fin (r + s)) (Fin (r + s)) R :=
  Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
    (fromBlocks A 0 0 B)

/- English proof (translation)
The claim follows from `GlobalTheory.SmGL.val_emb₂ R _ g`.
-/
theorem val_lev {R : Type} [CommRing R] {r s : ℕ} (g : GL (Fin r) R × GL (Fin s) R) :
    (lev R r s g).val = blockM g.1.val g.2.val :=
  GlobalTheory.SmGL.val_emb₂ R _ g

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [blockM, Matrix.map_apply, reindex_apply, submatrix_apply]`. Generalize the expression as in `(GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'`. Generalize the expression as in `(GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'`. Apply the tactic sequence `rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp`.
-/
theorem blockM_map {R S : Type} [CommRing R] [CommRing S] {r s : ℕ} (p : R →+* S)
    (A : Matrix (Fin r) (Fin r) R) (B : Matrix (Fin s) (Fin s) R) :
    (blockM A B).map p = blockM (A.map p) (B.map p) := by
  ext i j
  simp only [blockM, Matrix.map_apply, reindex_apply, submatrix_apply]
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(lev R r s g).val.map p = (lev S r s _).val`. Rewrite using `[val_lev, val_lev, blockM_map]`. Both sides reduce to the same expression.
-/
theorem map_lev {R S : Type} [CommRing R] [CommRing S] {r s : ℕ} (p : R →+* S)
    (g : GL (Fin r) R × GL (Fin s) R) :
    Matrix.GeneralLinearGroup.map p (lev R r s g) =
      lev S r s (Matrix.GeneralLinearGroup.map p g.1, Matrix.GeneralLinearGroup.map p g.2) := by
  apply Units.ext
  change (lev R r s g).val.map p = (lev S r s _).val
  rw [val_lev, val_lev, blockM_map]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

/- English proof (translation)
Use `ga_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[map_lev]`. Simplify using the standard rewrite rules. Rewrite using `[map_lev]`. Simplify using `only [pFin_infGL, pFin_infGL]`.

Conclude with `(map_one _).symm`.
-/
theorem infGL_lev (y : GL (Fin r) (Cinf E) × GL (Fin s) (Cinf E)) :
    infGL E (r + s) (lev (Cinf E) r s y) = lev (Ad E) r s (infGL E r y.1, infGL E s y.2) := by
  refine ga_ext ?_ ?_
  · rw [map_lev]; simp
  · rw [map_lev]; simp only [pFin_infGL, pFin_infGL]; exact (map_one _).symm

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [blockM, Matrix.add_apply, reindex_apply, submatrix_apply]`. Generalize the expression as in `(GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'`. Generalize the expression as in `(GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'`. Apply the tactic sequence `rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp`.
-/
theorem blockM_add {R : Type} [CommRing R] {r s : ℕ} (A A' : Matrix (Fin r) (Fin r) R)
    (B B' : Matrix (Fin s) (Fin s) R) : blockM A B + blockM A' B' = blockM (A + A') (B + B') := by
  ext i j
  simp only [blockM, Matrix.add_apply, reindex_apply, submatrix_apply]
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [blockM, Matrix.smul_apply, reindex_apply, submatrix_apply]`. Generalize the expression as in `(GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'`. Generalize the expression as in `(GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'`. Apply the tactic sequence `rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp`.
-/
theorem blockM_smul {R : Type} [CommRing R] {r s : ℕ} (t : ℝ) [Module ℝ R] (A : Matrix (Fin r) (Fin r) R)
    (B : Matrix (Fin s) (Fin s) R) : t • blockM A B = blockM (t • A) (t • B) := by
  ext i j
  simp only [blockM, Matrix.smul_apply, reindex_apply, submatrix_apply]
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp

/- English proof (translation)
Establish `h1 : (1 : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) = blockM 1 1`. Simplify using `[blockM, fromBlocks_one]`. Rewrite using `[h1, blockM_smul, blockM_add]`.
-/
theorem one_add_smul_blockM (t : ℝ) (X₁ : Matrix (Fin r) (Fin r) (Cinf E)) (X₂ : Matrix (Fin s) (Fin s) (Cinf E)) :
    1 + t • blockM X₁ X₂ = blockM (1 + t • X₁) (1 + t • X₂) := by
  have h1 : (1 : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) = blockM 1 1 := by
    simp [blockM, fromBlocks_one]
  rw [h1, blockM_smul, blockM_add]

/- English proof (translation)
Use `set g := lev (Ad E) r s m with hg`. Use `set X : Lie E (r + s) := toL (blockM X₁ X₂) with hX`. Set `c : ℝ → Lie E (r + s)` to `fun t => oneL E (r + s) + t • X`. Establish `hc : HasDerivAt c X 0` using `(((hasDerivAt_id' (0 : ℝ)).smul_const X).const_add (oneL E (r + s))).congr_deriv (one_smul ℝ X)`. Establish `h0 : c 0 = oneL E (r + s)` using `by simp [c]`.

Establish `hd : HasFDerivAt (chart F.1 g) (fderiv ℝ (chart F.1 g) (oneL E (r + s))) (c 0)`. Rewrite using `[h0]`. Conclude with `(differentiableAt_chart F.2 g).hasFDerivAt`. Establish `h2` using `hd.comp_hasDerivAt (0 : ℝ) hc`. Establish `ev : ∀ (n : ℕ) (Y : Lie E n), ∀ᶠ t : ℝ in 𝓝 0, oneL E n + t • Y ∈ invSet E n`.

Introduce `n Y`. Establish `hcont : Continuous fun t : ℝ => oneL E n + t • Y` using `by fun_prop`. Use `hcont.continuousAt.eventually_mem (isOpen_invSet.mem_nhds ?_)` and prove the remaining obligations. Simplify using `only [zero_smul, add_zero]`. Express the relevant statement in the definitionally equal form `IsUnit (Matrix.of (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) (Cinf E))))`.

Rewrite using `[Equiv.apply_symm_apply]`. Conclude with `isUnit_one`. Establish `hz : (chart F.1 g ∘ c) =ᶠ[𝓝 0] fun _ => 0` using `by filter_upwards [ev r (toL X₁), ev s (toL X₂)] with t h1 h2`. Take `⟨u₁, hu₁⟩` from `h1`. Take `⟨u₂, hu₂⟩` from `h2`.

Establish `e : c t = toL (lev (Cinf E) r s (u₁, u₂)).val`. Rewrite using `[val_lev]`. Express the relevant statement in the definitionally equal form `c t = toL (blockM u₁.val u₂.val)`. Rewrite using `[hu₁, hu₂]`. Conclude with `one_add_smul_blockM t X₁ X₂`.

Rewrite using `[Function.comp_apply, e, chart_val, infGL_lev, hg, ← map_mul]`. Conclude with `hF _`. Conclude with `h2.unique ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq hz)`.
-/
theorem lieD_block {F : Sm E (r + s)} (hF : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = 0)
    (X₁ : Matrix (Fin r) (Fin r) (Cinf E)) (X₂ : Matrix (Fin s) (Fin s) (Cinf E)) (m : GA E r × GA E s) :
    lieD (toL (blockM X₁ X₂)) F.1 (lev (Ad E) r s m) = 0 := by
  set g := lev (Ad E) r s m with hg
  set X : Lie E (r + s) := toL (blockM X₁ X₂) with hX
  let c : ℝ → Lie E (r + s) := fun t => oneL E (r + s) + t • X
  have hc : HasDerivAt c X 0 :=
    (((hasDerivAt_id' (0 : ℝ)).smul_const X).const_add (oneL E (r + s))).congr_deriv (one_smul ℝ X)
  have h0 : c 0 = oneL E (r + s) := by simp [c]
  have hd : HasFDerivAt (chart F.1 g) (fderiv ℝ (chart F.1 g) (oneL E (r + s))) (c 0) := by
    rw [h0]; exact (differentiableAt_chart F.2 g).hasFDerivAt
  have h2 := hd.comp_hasDerivAt (0 : ℝ) hc
  have ev : ∀ (n : ℕ) (Y : Lie E n), ∀ᶠ t : ℝ in 𝓝 0, oneL E n + t • Y ∈ invSet E n := by
    intro n Y
    have hcont : Continuous fun t : ℝ => oneL E n + t • Y := by fun_prop
    refine hcont.continuousAt.eventually_mem (isOpen_invSet.mem_nhds ?_)
    simp only [zero_smul, add_zero]
    change IsUnit (Matrix.of (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) (Cinf E))))
    rw [Equiv.apply_symm_apply]
    exact isUnit_one
  have hz : (chart F.1 g ∘ c) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [ev r (toL X₁), ev s (toL X₂)] with t h1 h2
    obtain ⟨u₁, hu₁⟩ := h1
    obtain ⟨u₂, hu₂⟩ := h2
    have e : c t = toL (lev (Cinf E) r s (u₁, u₂)).val := by
      rw [val_lev]
      change c t = toL (blockM u₁.val u₂.val)
      rw [hu₁, hu₂]
      exact one_add_smul_blockM t X₁ X₂
    rw [Function.comp_apply, e, chart_val, infGL_lev, hg, ← map_mul]
    exact hF _
  exact h2.unique ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq hz)

variable (E r s) in

def vanAlg : Subalgebra ℂ (Module.End ℂ (Sm E (r + s))) where
  carrier := {z | ∀ F : Sm E (r + s), (∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = 0) →
    ∀ m : GA E r × GA E s, (z F).1 (lev (Ad E) r s m) = 0}
  mul_mem' hx hy F hF := hx _ (hy F hF)
  add_mem' {x y} hx hy F hF m := by
    change (x F).1 _ + (y F).1 _ = 0
    rw [hx F hF m, hy F hF m, add_zero]
  algebraMap_mem' c F hF m := by
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply, hF m, smul_zero]

/- English proof (translation)
The claim follows from `S.smul_mem (S.sub_mem (h _) (S.smul_mem (h _) _)) _`.
-/
theorem Eop_mem_of {a : ℕ} (S : Subalgebra ℂ (Module.End ℂ (Sm E a))) (τ : E →+* ℂ) (p q : Fin a)
    (h : ∀ x, lieS E a p q x ∈ S) : Eop τ p q ∈ S :=
  S.smul_mem (S.sub_mem (h _) (S.smul_mem (h _) _)) _

/- English proof (translation)
Introduce `_ hF m` and use `lieD_block hF X₁ X₂ m`.
-/
theorem lie_block_mem (X₁ : Matrix (Fin r) (Fin r) (Cinf E)) (X₂ : Matrix (Fin s) (Fin s) (Cinf E)) :
    lie E (r + s) (toL (blockM X₁ X₂)) ∈ vanAlg E r s :=
  fun _ hF m => lieD_block hF X₁ X₂ m

/- English proof (translation)
Establish `hc : ∀ k : Fin r, Fin.castAdd s k = GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inl k)` using `fun k => Fin.ext (by simp)`. Establish `hn : ∀ k : Fin s, Fin.natAdd r k = GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inr k)` using `fun k => Fin.ext (by simp)`. Rewrite using `[hc, hc]`. Use extensionality with `a b`. Take `⟨a, rfl⟩` from `(GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective a`.

Take `⟨b, rfl⟩` from `(GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective b`. Simplify using `only [blockM, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.single_apply]`.
-/
theorem single_castAdd (i j : Fin r) (x : Cinf E) :
    Matrix.single (Fin.castAdd s i) (Fin.castAdd s j) x = blockM (Matrix.single i j x) (0 : Matrix (Fin s) (Fin s) (Cinf E)) := by
  have hc : ∀ k : Fin r, Fin.castAdd s k = GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inl k) := fun k => Fin.ext (by simp)
  have hn : ∀ k : Fin s, Fin.natAdd r k = GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inr k) := fun k => Fin.ext (by simp)
  rw [hc, hc]
  ext a b
  obtain ⟨a, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective a
  obtain ⟨b, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective b
  simp only [blockM, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.single_apply]

/- English proof (translation)
Establish `hc : ∀ k : Fin r, Fin.castAdd s k = GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inl k)` using `fun k => Fin.ext (by simp)`. Establish `hn : ∀ k : Fin s, Fin.natAdd r k = GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inr k)` using `fun k => Fin.ext (by simp)`. Rewrite using `[hn, hn]`. Use extensionality with `a b`. Take `⟨a, rfl⟩` from `(GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective a`.

Take `⟨b, rfl⟩` from `(GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective b`. Simplify using `only [blockM, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.single_apply]`.
-/
theorem single_natAdd (i j : Fin s) (x : Cinf E) :
    Matrix.single (Fin.natAdd r i) (Fin.natAdd r j) x = blockM (0 : Matrix (Fin r) (Fin r) (Cinf E)) (Matrix.single i j x) := by
  have hc : ∀ k : Fin r, Fin.castAdd s k = GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inl k) := fun k => Fin.ext (by simp)
  have hn : ∀ k : Fin s, Fin.natAdd r k = GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inr k) := fun k => Fin.ext (by simp)
  rw [hn, hn]
  ext a b
  obtain ⟨a, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective a
  obtain ⟨b, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective b
  simp only [blockM, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.single_apply]

/- English proof (translation)
The claim follows from `qdet_mem _ _ (fun i j => Eop_mem_of _ τ _ _ fun x => by rw [lieS_apply, single_castAdd]; exact lie_block_mem _ _) _`.
-/
theorem capR_mem (τ : E →+* ℂ) (u : ℂ) : capR r s τ u ∈ vanAlg E r s :=
  qdet_mem _ _ (fun i j => Eop_mem_of _ τ _ _ fun x => by
    rw [lieS_apply, single_castAdd]; exact lie_block_mem _ _) _

/- English proof (translation)
The claim follows from `qdet_mem _ _ (fun i j => Eop_mem_of _ τ _ _ fun x => by rw [lieS_apply, single_natAdd]; exact lie_block_mem _ _) _`.
-/
theorem capS_mem (τ : E →+* ℂ) (u : ℂ) : capS r s τ u ∈ vanAlg E r s :=
  qdet_mem _ _ (fun i j => Eop_mem_of _ τ _ _ fun x => by
    rw [lieS_apply, single_natAdd]; exact lie_block_mem _ _) _

variable (E) in

def nInvAlg (a r : ℕ) : Subalgebra ℂ (Module.End ℂ (Sm E a)) where
  carrier := {z | ∀ ψ : Sm E a, (∀ (x : BlockIx a r → Ad E) (g : GA E a), ψ.1 (unip x * g) = ψ.1 g) →
    ∀ (x : BlockIx a r → Ad E) (g : GA E a), (z ψ).1 (unip x * g) = (z ψ).1 g}
  mul_mem' hx hy ψ hψ := hx _ (hy ψ hψ)
  add_mem' {x y} hx hy ψ hψ v g := by
    change (x ψ).1 _ + (y ψ).1 _ = (x ψ).1 _ + (y ψ).1 _
    rw [hx ψ hψ v g, hy ψ hψ v g]
  algebraMap_mem' c ψ hψ v g := by
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply, hψ v g]

/- English proof (translation)
Introduce `ψ hψ v g`. Establish `e : chart ψ.1 (unip v * g) = chart ψ.1 g`. Use function extensionality and compare the values at `x`. Unfold `chart`. Use `split_ifs with hx`.

Rewrite using `[mul_assoc, hψ v]`. Both sides reduce to the same expression. Simplify using `only [GlobalTheory.CuspRep.lie_apply, lieD, e]`.
-/
theorem lie_mem_nInvAlg (a r : ℕ) (X : Lie E a) : lie E a X ∈ nInvAlg E a r := by
  intro ψ hψ v g
  have e : chart ψ.1 (unip v * g) = chart ψ.1 g := by
    funext x
    unfold chart
    split_ifs with hx
    · rw [mul_assoc, hψ v]
    · rfl
  simp only [GlobalTheory.CuspRep.lie_apply, lieD, e]

/- English proof (translation)
The claim follows from `qdet_mem _ _ (fun i j => Eop_mem_of _ τ _ _ fun x => lie_mem_nInvAlg a r _) _`.
-/
theorem cap_mem_nInvAlg (a r : ℕ) (τ : E →+* ℂ) (u : ℂ) : cap (a := a) τ u ∈ nInvAlg E a r :=
  qdet_mem _ _ (fun i j => Eop_mem_of _ τ _ _ fun x => lie_mem_nInvAlg a r _) _

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun hF => ⟨capR_mem τ u F hF, capS_mem τ u F hF⟩, fun hF => cap_mem_nInvAlg (r + s) r τ u F hF⟩`.
-/
theorem capStable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u : ℂ)
    (F : Sm E (r + s)) :
    ((∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = 0) →
      (∀ m : GA E r × GA E s, (capR r s τ u F).1 (lev (Ad E) r s m) = 0) ∧
        ∀ m : GA E r × GA E s, (capS r s τ u F).1 (lev (Ad E) r s m) = 0) ∧
    ((∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) →
      ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)),
        (cap (a := r + s) τ u F).1 (unip x * g) = (cap (a := r + s) τ u F).1 g) :=
  ⟨fun hF => ⟨capR_mem τ u F hF, capS_mem τ u F hF⟩, fun hF => cap_mem_nInvAlg (r + s) r τ u F hF⟩

end GlobalTheory.CompanionTheory.CTFin.CapStable

end
