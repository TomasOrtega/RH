import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[Matrix.mul_apply, map_sum, hp]`.
-/
private theorem mapL {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (j : A →+* B) (p : B →+ A)
    (hp : ∀ a y, p (j a * y) = a * p y) (M : Matrix (Fin n) (Fin n) A) (Z : Matrix (Fin n) (Fin n) B) :
    (M.map j * Z).map p = M * Z.map p := by
  ext a b
  simp [Matrix.mul_apply, map_sum, hp]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.mul_apply, map_sum, Matrix.map_apply]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm, hp, mul_comm]`.
-/
private theorem mapR {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (j : A →+* B) (p : B →+ A)
    (hp : ∀ a y, p (j a * y) = a * p y) (M : Matrix (Fin n) (Fin n) A) (Z : Matrix (Fin n) (Fin n) B) :
    (Z * M.map j).map p = Z.map p * M := by
  ext a b
  simp only [Matrix.mul_apply, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm, hp, mul_comm]

/- English proof (translation)
Introduce `l _ F n x x' j hE p hp hc`. Take `⟨⟨-, -, -, hρ, ha, -⟩, hw, -⟩` from `hE`. Establish `e1 : ∀ g, x'.ρX x'.A g = (x.ρX x.A g).map j`. Introduce `g`. Use extensionality with `a b`.

Simplify using `[NP.ρX, hρ, mat]`. Establish `e2 : ∀ v, x'.wX x'.A v = (x.wX x.A v).map j`. Introduce `v`. Use extensionality with `a b`. Simplify using `[NP.wX, hw]`.

Establish `e3 : ∀ v, x'.wiX x'.A v = (x.wiX x.A v).map j`. Introduce `v`. Use extensionality with `a b`. Simplify using `only [NP.wiX, hw, ← map_inv]`. Both sides reduce to the same expression.

Establish `hOd : ∀ Y ∈ Od x'.A x'.A n x'.a, Y.map p ∈ Od x.A x.A n x.a`. Introduce `Y hY a b`. Use `⟨fun h => ?_, fun _ => trivial⟩` and prove the remaining obligations. Use `(hY a b).1 (by rw [ha]; exact h)` as an intermediate fact. Rewrite `this`, the goal using `[Submodule.mem_bot]`.

Simplify using `[this]`. Establish `hsub : ∀ Y Z : Matrix (Fin n) (Fin n) x'.A, (Y - Z).map p = Y.map p - Z.map p`. Introduce `Y Z`. Use extensionality with `a b`. Simplify using the standard rewrite rules.

Establish `hadd : ∀ Y Z : Matrix (Fin n) (Fin n) x'.A, (Y + Z).map p = Y.map p + Z.map p`. Introduce `Y Z`. Use extensionality with `a b`. Simplify using the standard rewrite rules. Establish `hd : ∀ Y g, (dY F (x'.ρX x'.A) Y g).map p = dY F (x.ρX x.A) (Y.map p) g`.

Introduce `Y g`. Simplify using `only [dY]`. Rewrite using `[hsub, e1, e1, mapR j p hp, mapL j p hp]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `z ⟨h1, h2, h3, h4, h5, h6⟩`.

Use `⟨fun g => hOd _ (h1 g), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b N`. Take `⟨N', hN⟩` from `hc N`. Use `h2 a b N'` as an intermediate fact. Rewrite `this`, the goal using `[IsLocallyConstant.iff_eventually_eq]`.

Introduce `g`. Use `filter_upwards [this g] with h hh`. Rewrite `hh`, the goal using `[Ideal.Quotient.eq]`. Use `hN _ hh` as an intermediate fact. Rewrite `this` using `[map_sub]`.

Conclude with `this`. Introduce `g h`. Simplify using `only`. Rewrite using `[h3, hadd, e1, e1, mapR j p hp, mapL j p hp]`. Introduce `g`.

Simplify using `only`. Rewrite using `[h4]`. Use extensionality with `a b`. Simplify using the standard rewrite rules. Introduce `u g hg`.

Simplify using `only`. Rewrite using `[h5 u g hg]`. Use extensionality with `a b`. Simplify using the standard rewrite rules. Introduce `v`.

Take `⟨Y, hY, hL⟩` from `h6 v`. Use `⟨Y.map p, hOd _ hY, fun g => ?_⟩` and prove the remaining obligations. Establish `key : x.wiX x.A v * ((z (F.φ v g)).map p - dY F (x.ρX x.A) (Y.map p) (F.φ v g)) * x.wX x.A v = (x'.wiX x'.A v * (z (F.φ v g) - dY F (x'.ρX x'.A) Y (F.φ v g)) * x'.wX x'.A v).map p`. Rewrite using `[e2, e3, mapR j p hp, mapL j p hp, hsub, hd]`. Use `⟨fun a b hab => ?_, fun hg a => ?_⟩` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[key, Matrix.map_apply, (hL g).1 a b hab, map_zero]`. Simplify using `only`. Rewrite using `[key, Matrix.map_apply, (hL g).2 hg a, map_zero]`. Introduce and unpack `z ⟨Y, hY, hT, rfl⟩`.

Use `⟨Y.map p, hOd _ hY, ?_, funext fun g => hd Y g⟩` and prove the remaining obligations. Use extensionality with `a b`. Use `congrFun (congrFun hT a) b` as an intermediate fact. Simplify using `only [Matrix.transpose_apply, Matrix.neg_apply] at this`. Simplify using `[this]`.
-/
theorem UpperTheory.V.Pa.Det.compSel :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x x' : NP F n) (j : x.A →+* x'.A), x.Ext2 x' j → ∀ (p : x'.A →+ x.A), (∀ a y, p (j a * y) = a * p y) → (∀ N : ℕ, ∃ N' : ℕ, ∀ y ∈ Ideal.span {x'.t} ^ N', p y ∈ Ideal.span {x.t} ^ N) → (∀ z ∈ SelZ F x'.t (x'.ρX x'.A) (x'.wX x'.A) (x'.wiX x'.A) (Od x'.A x'.A n x'.a), (fun g => (z g).map p) ∈ SelZ F x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a)) ∧ ∀ z ∈ Bd F (x'.ρX x'.A) (Od x'.A x'.A n x'.a), (fun g => (z g).map p) ∈ Bd F (x.ρX x.A) (Od x.A x.A n x.a) := by
  intro l _ F n x x' j hE p hp hc
  obtain ⟨⟨-, -, -, hρ, ha, -⟩, hw, -⟩ := hE
  have e1 : ∀ g, x'.ρX x'.A g = (x.ρX x.A g).map j := by
    intro g
    ext a b
    simp [NP.ρX, hρ, mat]
  have e2 : ∀ v, x'.wX x'.A v = (x.wX x.A v).map j := by
    intro v
    ext a b
    simp [NP.wX, hw]
  have e3 : ∀ v, x'.wiX x'.A v = (x.wiX x.A v).map j := by
    intro v
    ext a b
    simp only [NP.wiX, hw, ← map_inv]
    rfl
  have hOd : ∀ Y ∈ Od x'.A x'.A n x'.a, Y.map p ∈ Od x.A x.A n x.a := by
    intro Y hY a b
    refine ⟨fun h => ?_, fun _ => trivial⟩
    have := (hY a b).1 (by rw [ha]; exact h)
    rw [Submodule.mem_bot] at this ⊢
    simp [this]
  have hsub : ∀ Y Z : Matrix (Fin n) (Fin n) x'.A, (Y - Z).map p = Y.map p - Z.map p := by
    intro Y Z; ext a b; simp
  have hadd : ∀ Y Z : Matrix (Fin n) (Fin n) x'.A, (Y + Z).map p = Y.map p + Z.map p := by
    intro Y Z; ext a b; simp
  have hd : ∀ Y g, (dY F (x'.ρX x'.A) Y g).map p = dY F (x.ρX x.A) (Y.map p) g := by
    intro Y g
    simp only [dY]
    rw [hsub, e1, e1, mapR j p hp, mapL j p hp]
  refine ⟨?_, ?_⟩
  · rintro z ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨fun g => hOd _ (h1 g), ?_, ?_, ?_, ?_, ?_⟩
    · intro a b N
      obtain ⟨N', hN⟩ := hc N
      have := h2 a b N'
      rw [IsLocallyConstant.iff_eventually_eq] at this ⊢
      intro g
      filter_upwards [this g] with h hh
      rw [Ideal.Quotient.eq] at hh ⊢
      have := hN _ hh
      rw [map_sub] at this
      exact this
    · intro g h
      simp only
      rw [h3, hadd, e1, e1, mapR j p hp, mapL j p hp]
    · intro g
      simp only
      rw [h4]
      ext a b
      simp
    · intro u g hg
      simp only
      rw [h5 u g hg]
      ext a b
      simp
    · intro v
      obtain ⟨Y, hY, hL⟩ := h6 v
      refine ⟨Y.map p, hOd _ hY, fun g => ?_⟩
      have key : x.wiX x.A v * ((z (F.φ v g)).map p - dY F (x.ρX x.A) (Y.map p) (F.φ v g)) * x.wX x.A v =
          (x'.wiX x'.A v * (z (F.φ v g) - dY F (x'.ρX x'.A) Y (F.φ v g)) * x'.wX x'.A v).map p := by
        rw [e2, e3, mapR j p hp, mapL j p hp, hsub, hd]
      refine ⟨fun a b hab => ?_, fun hg a => ?_⟩
      · simp only
        rw [key, Matrix.map_apply, (hL g).1 a b hab, map_zero]
      · simp only
        rw [key, Matrix.map_apply, (hL g).2 hg a, map_zero]
  · rintro z ⟨Y, hY, hT, rfl⟩
    refine ⟨Y.map p, hOd _ hY, ?_, funext fun g => hd Y g⟩
    ext a b
    have := congrFun (congrFun hT a) b
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    simp [this]
