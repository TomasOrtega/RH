import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.Fixg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.BilinearSmul.BSmulRight
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IsFixMapIff

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

open Matrix in
/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ τ hLoc c d m _ δ ι P hM`. Establish `hmv : ∀ (a b : U3 Δ) (v : Fin 3 → Lsq K Δ), ((a * b : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v = (a : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec ((b : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v)`. Introduce `a b v`. Rewrite using `[Submonoid.coe_mul, Matrix.mulVec_mulVec]`. Establish `hmv1 : ∀ v : Fin 3 → Lsq K Δ, ((1 : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v = v`.

Introduce `v`. Simplify using the standard rewrite rules. Establish `hinv : ∀ (a : U3 Δ) (v : Fin 3 → Lsq K Δ), ((a⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec ((a : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v) = v`. Introduce `a v`. Rewrite using `[← hmv, inv_mul_cancel, hmv1]`.

Establish `hinv' : ∀ (a : U3 Δ) (v : Fin 3 → Lsq K Δ), (a : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec (((a⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v) = v`. Introduce `a v`. Rewrite using `[← hmv, mul_inv_cancel, hmv1]`. Establish `hA : ∀ (A : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (v : Fin 3 → Lsq K Δ), (∀ i j, IsInt O (A i j)) → (∀ i, IsInt O (v i)) → ∀ i, IsInt O (A.mulVec v i)`. Introduce `A v hA hv i`.

Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `IsIntegral.sum _ (fun j _ => (hA i j).mul (hv j))`. Establish `hKUint : ∀ k ∈ KU O Δ, ∀ v : Fin 3 → Lsq K Δ, (∀ i, IsInt O (v i)) → ∀ i, IsInt O ((k : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v i)`. Introduce `k hk v hv`. Establish `hk' : ∀ i j, IsInt O ((k : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j) ∧ IsInt O (star ((k : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j))` using `hk`.

Conclude with `hA _ v (fun i j => (hk' i j).1) hv`. Establish `hKUof : ∀ h : U3 Δ, (∀ v : Fin 3 → Lsq K Δ, (∀ i, IsInt O (v i)) → ∀ i, IsInt O ((h : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v i)) → h ∈ KU O Δ`. Introduce `h H`. Establish `he : ∀ i j, IsInt O ((h : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j)`. Introduce `i j`.

Establish `hs : ∀ k, IsInt O ((Pi.single j (1 : Lsq K Δ) : Fin 3 → Lsq K Δ) k)`. Introduce `k`. Break down `eq_or_ne k j with rfl | hkj` into its components or cases. Simplify using `using (isIntegral_one : IsIntegral O (1 : Lsq K Δ))`. Simplify `(isIntegral_zero : IsIntegral O (0 : Lsq K Δ))` using `[Pi.single_apply, hkj]`.

Use `H _ hs i` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_single_one]`. Conclude with `fun i j => ⟨he i j, OE.int_star hLoc (he i j)⟩`. Take `⟨L, hLm⟩ : ∃ L : U3 Δ → Set (Sp Δ τ), ∀ g x, x ∈ L g ↔ ∀ i, IsInt O (((g⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec (P x) i)` from `⟨_, fun _ _ => Iff.rfl⟩`. Establish `LD : ∀ a b : U3 Δ, a⁻¹ * b ∈ KU O Δ → L b = L a`.

Introduce `a b hk`. Use extensionality with `x`. Rewrite using `[hLm, hLm]`. Establish `hb : b = a * (a⁻¹ * b)` using `(mul_inv_cancel_left a b).symm`. Use `set k := a⁻¹ * b`.

Rewrite using `[hb, _root_.mul_inv_rev, hmv]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `hKUint k hk _ h` as an intermediate fact. Rewrite `this` using `[hinv']`. Then use the resulting hypothesis.

Introduce `h`. Conclude with `hKUint _ (inv_mem hk) _ h`. Establish `Lsame : ∀ a b : U3 Δ, L a = L b → a⁻¹ * b ∈ KU O Δ`. Introduce `a b h`. Apply `hKUof` to reduce the goal to its premises.

Introduce `v hv`. Establish `hx : P.symm ((b : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v) ∈ L b`. Rewrite using `[hLm, LinearEquiv.apply_symm_apply, hinv]`. Conclude with `hv`. Rewrite `hx` using `[← h, hLm, LinearEquiv.apply_symm_apply]`.

Rewrite using `[hmv]` and apply the resulting hypothesis. Establish `hstar : ∀ (g : U3 Δ) (v : Fin 3 → Lsq K Δ), ((theta Δ g : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v = star ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec (star v))`. Introduce `g v`. Use `show ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map star).mulVec v = _`. Use function extensionality and compare the values at `i`.

Simplify using `[Matrix.mulVec, dotProduct, Matrix.map_apply, star_sum, star_mul']`. Establish `Gconv : ∀ g : U3 Δ, IsFix O c d m (L g) → g⁻¹ * δ * theta Δ g ∈ KU O Δ`. Introduce `g hF`. Apply `hKUof` to reduce the goal to its premises. Introduce `v hv`.

Establish `hx : P.symm ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec (star v)) ∈ L g`. Rewrite using `[hLm, LinearEquiv.apply_symm_apply, hinv]`. Introduce `i`. Conclude with `OE.int_star hLoc (hv i)`. Establish `hsx : semi d (P.symm ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec (star v))) ∈ L g`.

Rewrite using `[← hF.stab]`. Conclude with `⟨_, hx, rfl⟩`. Rewrite `hsx` using `[hLm, hM.semi, LinearEquiv.apply_symm_apply, ← hstar]`. Rewrite using `[hmv, hmv]` and apply the resulting hypothesis. Establish `hkrel : ∀ g : U3 Δ, g⁻¹ * δ * theta Δ g ∈ KU O Δ ↔ IsFix O c d m (L g)`.

Introduce `g`. Use `⟨fun h => ?_, Gconv g⟩` and prove the remaining obligations. Use `One.fixg O K Δ τ hLoc c d m δ ι P hM g h` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`.

Conclude with `hLm g x`. Establish `torinv : ∀ (t : (Etau K τ)ˣ) (x : Sp Δ τ), tor Δ t (tor Δ t⁻¹ x) = x`. Introduce `t x`. Apply `P.injective` to reduce the goal to its premises. Rewrite using `[hM.tor, hM.tor, map_inv, hinv']`.

Establish `Ltor : ∀ (t : (Etau K τ)ˣ) (g : U3 Δ), L (ι t * g) = tor Δ t '' L g`. Introduce `t g`. Use extensionality with `x`. Rewrite using `[hLm]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Use `⟨tor Δ t⁻¹ x, ?_, torinv t x⟩` and prove the remaining obligations. Rewrite using `[hLm, hM.tor, map_inv]`. Rewrite `hx` using `[_root_.mul_inv_rev, hmv]`. Then use the resulting hypothesis. Introduce and unpack `⟨y, hy, rfl⟩`.

Rewrite `hy` using `[hLm]`. Rewrite using `[_root_.mul_inv_rev, hmv, hM.tor, hinv]`. Conclude with `hy`. Establish `heq : ∀ (t : (Etau K τ)ˣ) (y : U3 Δ ⧸ KU O Δ), L (Quotient.out ((ι t) • y)) = tor Δ t '' L (Quotient.out y)`. Introduce `t y`.

Establish `hq : (QuotientGroup.mk (ι t * Quotient.out y) : U3 Δ ⧸ KU O Δ) = (ι t) • y` using `by conv_rhs => rw [← QuotientGroup.out_eq' y]`. Both sides reduce to the same expression. Establish `hq2 : (QuotientGroup.mk (ι t * Quotient.out y) : U3 Δ ⧸ KU O Δ) = QuotientGroup.mk (Quotient.out ((ι t) • y))`. Rewrite using `[QuotientGroup.out_eq', hq]`. Rewrite using `[LD _ _ (QuotientGroup.eq.mp hq2)]`.

Conclude with `Ltor t (Quotient.out y)`. Unfold `uOrb lcount orb`. Use `@wTrans _ _ _ inferInstance (MulAction.compHom (U3 Δ ⧸ KU O Δ) ι) (torAct Δ τ) (Cint O τ) _ _ (fun y S => S = L (Quotient.out y)) ?_ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `t y beta_reduce split_ifs with h1 h2 h3`. Both sides reduce to the same expression.

Conclude with `absurd ((hkrel _).mpr ((isFix_tor c d m t _).mp ((congrArg (IsFix O c d m) (heq t y)).to_iff.mp ((hkrel _).mp h1)))) h2`. Conclude with `absurd ((hkrel _).mpr ((congrArg (IsFix O c d m) (heq t y)).to_iff.mpr ((isFix_tor c d m t _).mpr ((hkrel _).mp h3)))) h1`. Both sides reduce to the same expression. Introduce `t S split_ifs with h1 h2 h3`. Both sides reduce to the same expression.

Conclude with `absurd ((isFix_tor c d m t S).mp h1) h2`. Conclude with `absurd ((isFix_tor c d m t S).mpr h3) h1`. Both sides reduce to the same expression. Introduce `t y S hR`. Substitute `hR` using the available equality.

Conclude with `(heq t y).symm`. Introduce `y S hR`. Substitute `hR` using the available equality. Use `beta_reduce`. Use `split_ifs with h1 h2 h3`.

Both sides reduce to the same expression. Conclude with `absurd ((hkrel _).mp h1) h2`. Conclude with `absurd ((hkrel _).mpr h3) h1`. Both sides reduce to the same expression. Introduce `y _`.

Conclude with `⟨_, rfl, fun S h => h⟩`. Introduce `S hS`. Establish `hF : IsFix O c d m S`. Assume the negation of the conclusion as `h`. Simplify using `[h] at hS`.

Take `⟨s, hs⟩` from `hF.fg`. Use `set M : Submodule O (Fin 3 → Lsq K Δ) := Submodule.map ((P : Sp Δ τ →ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)).restrictScalars O) (Submodule.span O (s : Set (Sp Δ τ))) with hMdef`. Establish `hmem : ∀ v, v ∈ M ↔ P.symm v ∈ S`. Introduce `v`. Rewrite using `[hs, hMdef, Submodule.mem_map, SetLike.mem_coe]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Simplify using `using hx`. Introduce `h`. Conclude with `⟨_, h, by simp⟩`.

Establish `hFG : M.FG` using `Submodule.FG.map _ (Submodule.fg_span (Finset.finite_toSet s))`. Take `⟨g, hg⟩` from `OE.ortho hLoc M hFG (by`. Introduce `w`. Rewrite using `[hmem, hF.dual]`. Prove the components needed by the constructor for the conclusion.

Introduce `h u hu`. Use `h _ ((hmem u).mp hu)` as an intermediate fact. Rewrite `this` using `[hM.form, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`. Conclude with `this`. Introduce `h x hx`.

Rewrite using `[hM.form, LinearEquiv.apply_symm_apply]`. Conclude with `h (P x) ((hmem _).mpr (by simpa using hx)))`. Establish `hSL : S = L g`. Use extensionality with `x`. Rewrite using `[hLm, ← hg, hmem, LinearEquiv.symm_apply_apply]`.

Use `⟨QuotientGroup.mk g, ?_, ?_⟩` and prove the remaining obligations. Use `show S = L (Quotient.out (QuotientGroup.mk g : U3 Δ ⧸ KU O Δ))`. Rewrite using `[hSL]`. Conclude with `(LD _ _ (QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk g : U3 Δ ⧸ KU O Δ)).symm)).symm`. Introduce `y hy`.

Rewrite using `[← QuotientGroup.out_eq' y]`. Apply `QuotientGroup.eq.mpr` to reduce the goal to its premises. Apply `Lsame` to reduce the goal to its premises. Rewrite using `[← hSL]`. Conclude with `hy.symm`.
-/
theorem UpperTheory.V.Z.Sym.Loc.orbEq : UpperTheory.V.Z.Sym.Loc.OrbEq := by
  intro O K _ _ _ _ _ Δ τ hLoc c d m _ δ ι P hM
  have hmv : ∀ (a b : U3 Δ) (v : Fin 3 → Lsq K Δ),
      ((a * b : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v
        = (a : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec ((b : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v) := by
    intro a b v
    rw [Submonoid.coe_mul, Matrix.mulVec_mulVec]
  have hmv1 : ∀ v : Fin 3 → Lsq K Δ, ((1 : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v = v := by
    intro v
    simp
  have hinv : ∀ (a : U3 Δ) (v : Fin 3 → Lsq K Δ),
      ((a⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec ((a : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v) = v := by
    intro a v
    rw [← hmv, inv_mul_cancel, hmv1]
  have hinv' : ∀ (a : U3 Δ) (v : Fin 3 → Lsq K Δ),
      (a : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec (((a⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v) = v := by
    intro a v
    rw [← hmv, mul_inv_cancel, hmv1]
  have hA : ∀ (A : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (v : Fin 3 → Lsq K Δ),
      (∀ i j, IsInt O (A i j)) → (∀ i, IsInt O (v i)) → ∀ i, IsInt O (A.mulVec v i) := by
    intro A v hA hv i
    simp only [Matrix.mulVec, dotProduct]
    exact IsIntegral.sum _ (fun j _ => (hA i j).mul (hv j))
  have hKUint : ∀ k ∈ KU O Δ, ∀ v : Fin 3 → Lsq K Δ, (∀ i, IsInt O (v i)) →
      ∀ i, IsInt O ((k : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v i) := by
    intro k hk v hv
    have hk' : ∀ i j, IsInt O ((k : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j)
        ∧ IsInt O (star ((k : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j)) := hk
    exact hA _ v (fun i j => (hk' i j).1) hv
  have hKUof : ∀ h : U3 Δ, (∀ v : Fin 3 → Lsq K Δ, (∀ i, IsInt O (v i)) →
      ∀ i, IsInt O ((h : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v i)) → h ∈ KU O Δ := by
    intro h H
    have he : ∀ i j, IsInt O ((h : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j) := by
      intro i j
      have hs : ∀ k, IsInt O ((Pi.single j (1 : Lsq K Δ) : Fin 3 → Lsq K Δ) k) := by
        intro k
        rcases eq_or_ne k j with rfl | hkj
        · simpa using (isIntegral_one : IsIntegral O (1 : Lsq K Δ))
        · simpa [Pi.single_apply, hkj] using (isIntegral_zero : IsIntegral O (0 : Lsq K Δ))
      have := H _ hs i
      simpa [Matrix.mulVec_single_one] using this
    exact fun i j => ⟨he i j, OE.int_star hLoc (he i j)⟩
  obtain ⟨L, hLm⟩ : ∃ L : U3 Δ → Set (Sp Δ τ), ∀ g x, x ∈ L g ↔
      ∀ i, IsInt O (((g⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec (P x) i) :=
    ⟨_, fun _ _ => Iff.rfl⟩
  have LD : ∀ a b : U3 Δ, a⁻¹ * b ∈ KU O Δ → L b = L a := by
    intro a b hk
    ext x
    rw [hLm, hLm]
    have hb : b = a * (a⁻¹ * b) := (mul_inv_cancel_left a b).symm
    set k := a⁻¹ * b
    rw [hb, _root_.mul_inv_rev, hmv]
    constructor
    · intro h
      have := hKUint k hk _ h
      rwa [hinv'] at this
    · intro h
      exact hKUint _ (inv_mem hk) _ h
  have Lsame : ∀ a b : U3 Δ, L a = L b → a⁻¹ * b ∈ KU O Δ := by
    intro a b h
    apply hKUof
    intro v hv
    have hx : P.symm ((b : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v) ∈ L b := by
      rw [hLm, LinearEquiv.apply_symm_apply, hinv]
      exact hv
    rw [← h, hLm, LinearEquiv.apply_symm_apply] at hx
    rwa [hmv]
  have hstar : ∀ (g : U3 Δ) (v : Fin 3 → Lsq K Δ),
      ((theta Δ g : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v
        = star ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec (star v)) := by
    intro g v
    show ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map star).mulVec v = _
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.map_apply, star_sum, star_mul']
  have Gconv : ∀ g : U3 Δ, IsFix O c d m (L g) → g⁻¹ * δ * theta Δ g ∈ KU O Δ := by
    intro g hF
    apply hKUof
    intro v hv
    have hx : P.symm ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec (star v)) ∈ L g := by
      rw [hLm, LinearEquiv.apply_symm_apply, hinv]
      intro i
      exact OE.int_star hLoc (hv i)
    have hsx : semi d (P.symm ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec (star v))) ∈ L g := by
      rw [← hF.stab]
      exact ⟨_, hx, rfl⟩
    rw [hLm, hM.semi, LinearEquiv.apply_symm_apply, ← hstar] at hsx
    rwa [hmv, hmv]
  have hkrel : ∀ g : U3 Δ, g⁻¹ * δ * theta Δ g ∈ KU O Δ ↔ IsFix O c d m (L g) := by
    intro g
    refine ⟨fun h => ?_, Gconv g⟩
    have := One.fixg O K Δ τ hLoc c d m δ ι P hM g h
    convert this using 1
    ext x
    exact hLm g x
  have torinv : ∀ (t : (Etau K τ)ˣ) (x : Sp Δ τ), tor Δ t (tor Δ t⁻¹ x) = x := by
    intro t x
    apply P.injective
    rw [hM.tor, hM.tor, map_inv, hinv']
  have Ltor : ∀ (t : (Etau K τ)ˣ) (g : U3 Δ), L (ι t * g) = tor Δ t '' L g := by
    intro t g
    ext x
    rw [hLm]
    constructor
    · intro hx
      refine ⟨tor Δ t⁻¹ x, ?_, torinv t x⟩
      rw [hLm, hM.tor, map_inv]
      rwa [_root_.mul_inv_rev, hmv] at hx
    · rintro ⟨y, hy, rfl⟩
      rw [hLm] at hy
      rw [_root_.mul_inv_rev, hmv, hM.tor, hinv]
      exact hy
  have heq : ∀ (t : (Etau K τ)ˣ) (y : U3 Δ ⧸ KU O Δ),
      L (Quotient.out ((ι t) • y)) = tor Δ t '' L (Quotient.out y) := by
    intro t y
    have hq : (QuotientGroup.mk (ι t * Quotient.out y) : U3 Δ ⧸ KU O Δ) = (ι t) • y := by
      conv_rhs => rw [← QuotientGroup.out_eq' y]
      rfl
    have hq2 : (QuotientGroup.mk (ι t * Quotient.out y) : U3 Δ ⧸ KU O Δ)
        = QuotientGroup.mk (Quotient.out ((ι t) • y)) := by
      rw [QuotientGroup.out_eq', hq]
    rw [LD _ _ (QuotientGroup.eq.mp hq2)]
    exact Ltor t (Quotient.out y)
  unfold uOrb lcount orb
  refine @wTrans _ _ _ inferInstance (MulAction.compHom (U3 Δ ⧸ KU O Δ) ι) (torAct Δ τ) (Cint O τ) _ _ (fun y S => S = L (Quotient.out y)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro t y
    beta_reduce
    split_ifs with h1 h2 h3
    · rfl
    · exact absurd ((hkrel _).mpr ((isFix_tor c d m t _).mp
        ((congrArg (IsFix O c d m) (heq t y)).to_iff.mp ((hkrel _).mp h1)))) h2
    · exact absurd ((hkrel _).mpr ((congrArg (IsFix O c d m) (heq t y)).to_iff.mpr
        ((isFix_tor c d m t _).mpr ((hkrel _).mp h3)))) h1
    · rfl
  · intro t S
    split_ifs with h1 h2 h3
    · rfl
    · exact absurd ((isFix_tor c d m t S).mp h1) h2
    · exact absurd ((isFix_tor c d m t S).mpr h3) h1
    · rfl
  · intro t y S hR
    subst hR
    exact (heq t y).symm
  · intro y S hR
    subst hR
    beta_reduce
    split_ifs with h1 h2 h3
    · rfl
    · exact absurd ((hkrel _).mp h1) h2
    · exact absurd ((hkrel _).mpr h3) h1
    · rfl
  · intro y _
    exact ⟨_, rfl, fun S h => h⟩
  · intro S hS
    have hF : IsFix O c d m S := by
      by_contra h
      simp [h] at hS
    obtain ⟨s, hs⟩ := hF.fg
    set M : Submodule O (Fin 3 → Lsq K Δ) :=
      Submodule.map ((P : Sp Δ τ →ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)).restrictScalars O)
        (Submodule.span O (s : Set (Sp Δ τ))) with hMdef
    have hmem : ∀ v, v ∈ M ↔ P.symm v ∈ S := by
      intro v
      rw [hs, hMdef, Submodule.mem_map, SetLike.mem_coe]
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
      · intro h
        exact ⟨_, h, by simp⟩
    have hFG : M.FG := Submodule.FG.map _ (Submodule.fg_span (Finset.finite_toSet s))
    obtain ⟨g, hg⟩ := OE.ortho hLoc M hFG (by
      intro w
      rw [hmem, hF.dual]
      constructor
      · intro h u hu
        have := h _ ((hmem u).mp hu)
        rw [hM.form, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
        exact this
      · intro h x hx
        rw [hM.form, LinearEquiv.apply_symm_apply]
        exact h (P x) ((hmem _).mpr (by simpa using hx)))
    have hSL : S = L g := by
      ext x
      rw [hLm, ← hg, hmem, LinearEquiv.symm_apply_apply]
    refine ⟨QuotientGroup.mk g, ?_, ?_⟩
    · show S = L (Quotient.out (QuotientGroup.mk g : U3 Δ ⧸ KU O Δ))
      rw [hSL]
      exact (LD _ _ (QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk g : U3 Δ ⧸ KU O Δ)).symm)).symm
    · intro y hy
      rw [← QuotientGroup.out_eq' y]
      apply QuotientGroup.eq.mpr
      apply Lsame
      rw [← hSL]
      exact hy.symm
