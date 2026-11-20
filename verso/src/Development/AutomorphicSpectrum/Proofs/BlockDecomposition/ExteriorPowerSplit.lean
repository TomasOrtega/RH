import Mathlib
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsDetEquivOfSubsingleton

open TensorProduct Module Function

namespace GlobalTheory.CompanionTheory.TopExtSplit

open GlobalTheory.TopExt

variable {R F H L : Type*} [CommRing R] [AddCommGroup F] [Module R F] [AddCommGroup H] [Module R H]
  [AddCommGroup L] [Module R L]

variable (R F) in

noncomputable def gradeProj (n : ℕ) : ExteriorAlgebra R F →ₗ[R] ⋀[R]^n F :=
  DirectSum.component R ℕ (fun k => ⋀[R]^k F) n ∘ₗ
    (DirectSum.decomposeLinearEquiv (fun k : ℕ => ⋀[R]^k F)).toLinearMap

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(DirectSum.decompose (fun k : ℕ => ⋀[R]^k F) (x : ExteriorAlgebra R F)) n = x`. Rewrite using `[DirectSum.decompose_coe, DirectSum.of_eq_same]`.
-/
theorem gradeProj_same {n : ℕ} (x : ⋀[R]^n F) :
    gradeProj R F n (x : ExteriorAlgebra R F) = x := by
  change (DirectSum.decompose (fun k : ℕ => ⋀[R]^k F) (x : ExteriorAlgebra R F)) n = x
  rw [DirectSum.decompose_coe, DirectSum.of_eq_same]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(DirectSum.decompose (fun k : ℕ => ⋀[R]^k F) (x : ExteriorAlgebra R F)) n = 0`. Conclude with `Subtype.ext (DirectSum.decompose_of_mem_ne _ x.2 h)`.
-/
theorem gradeProj_ne {m n : ℕ} (h : m ≠ n) (x : ⋀[R]^m F) :
    gradeProj R F n (x : ExteriorAlgebra R F) = 0 := by
  change (DirectSum.decompose (fun k : ℕ => ⋀[R]^k F) (x : ExteriorAlgebra R F)) n = 0
  exact Subtype.ext (DirectSum.decompose_of_mem_ne _ x.2 h)

/- English proof (translation)
Set `e : (0 : QuadraticForm R H) →qᵢ (QuadraticMap.prod (0 : QuadraticForm R F) (0 : QuadraticForm R L))` to `{ r.prod π with map_app' := fun x => by simp }`. Establish `he : ∀ x, e x = (r x, π x)` using `fun _ => rfl`. Set `Φ` to `(CliffordAlgebra.ofProd (0 : QuadraticForm R F) (0 : QuadraticForm R L)).comp (CliffordAlgebra.map e)`. Establish `h₁ : Φ.comp (ExteriorAlgebra.map i) = GradedTensorProduct.includeLeft _ _`. Use extensionality with `x`.

Simplify using `[Φ, he, hri, hπi]`. Establish `h₂ : Φ.comp (ExteriorAlgebra.map s) = GradedTensorProduct.includeRight _ _`. Use extensionality with `x`. Simplify using `[Φ, he, hrs, hπs]`. Use `⟨fun a b => TensorProduct.map (gradeProj R F a) (gradeProj R L b) ∘ₗ (GradedTensorProduct.of R (CliffordAlgebra.evenOdd (0 : QuadraticForm R F)) (CliffordAlgebra.evenOdd (0 : QuadraticForm R L))).symm.toLinearMap ∘ₗ Φ.toLinearMap, ?_⟩` and prove the remaining obligations.

Introduce `a b a' b' x y`. Establish `hx` using `AlgHom.congr_fun h₁ x`. Establish `hy` using `AlgHom.congr_fun h₂ y`. Rewrite `hx`, `hy` using `[AlgHom.comp_apply]`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply, coe_wedgeMap_tmul, map_mul, hx, hy, GradedTensorProduct.includeLeft_apply, GradedTensorProduct.includeRight_apply, GradedTensorProduct.tmul_one_mul_one_tmul]`.

Express the relevant statement in the definitionally equal form `TensorProduct.map (gradeProj R F a) (gradeProj R L b) ((x : ExteriorAlgebra R F) ⊗ₜ (y : ExteriorAlgebra R L)) = _`. Rewrite using `[TensorProduct.map_tmul]`.
-/
theorem exists_bigradedProj {i : F →ₗ[R] H} {s : L →ₗ[R] H} {r : H →ₗ[R] F} {π : H →ₗ[R] L}
    (hri : ∀ x, r (i x) = x) (hrs : ∀ y, r (s y) = 0) (hπi : ∀ x, π (i x) = 0)
    (hπs : ∀ y, π (s y) = y) :
    ∃ Ψ : ∀ a b : ℕ, ExteriorAlgebra R H →ₗ[R] (⋀[R]^a F) ⊗[R] (⋀[R]^b L),
      ∀ (a b a' b' : ℕ) (x : ⋀[R]^a' F) (y : ⋀[R]^b' L),
        Ψ a b (wedgeMap i s a' b' (x ⊗ₜ y) : ExteriorAlgebra R H) =
          gradeProj R F a (x : ExteriorAlgebra R F) ⊗ₜ
            gradeProj R L b (y : ExteriorAlgebra R L) := by
  let e : (0 : QuadraticForm R H) →qᵢ
      (QuadraticMap.prod (0 : QuadraticForm R F) (0 : QuadraticForm R L)) :=
    { r.prod π with map_app' := fun x => by simp }
  have he : ∀ x, e x = (r x, π x) := fun _ => rfl
  let Φ := (CliffordAlgebra.ofProd (0 : QuadraticForm R F) (0 : QuadraticForm R L)).comp
    (CliffordAlgebra.map e)
  have h₁ : Φ.comp (ExteriorAlgebra.map i) = GradedTensorProduct.includeLeft _ _ := by
    ext x
    simp [Φ, he, hri, hπi]
  have h₂ : Φ.comp (ExteriorAlgebra.map s) = GradedTensorProduct.includeRight _ _ := by
    ext x
    simp [Φ, he, hrs, hπs]
  refine ⟨fun a b => TensorProduct.map (gradeProj R F a) (gradeProj R L b) ∘ₗ
    (GradedTensorProduct.of R (CliffordAlgebra.evenOdd (0 : QuadraticForm R F))
      (CliffordAlgebra.evenOdd (0 : QuadraticForm R L))).symm.toLinearMap ∘ₗ Φ.toLinearMap, ?_⟩
  intro a b a' b' x y
  have hx := AlgHom.congr_fun h₁ x
  have hy := AlgHom.congr_fun h₂ y
  rw [AlgHom.comp_apply] at hx hy
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply,
    coe_wedgeMap_tmul, map_mul, hx, hy, GradedTensorProduct.includeLeft_apply,
    GradedTensorProduct.includeRight_apply, GradedTensorProduct.tmul_one_mul_one_tmul]
  change TensorProduct.map (gradeProj R F a) (gradeProj R L b)
    ((x : ExteriorAlgebra R F) ⊗ₜ (y : ExteriorAlgebra R L)) = _
  rw [TensorProduct.map_tmul]

noncomputable def wedgePiece (i : F →ₗ[R] H) (s : L →ₗ[R] H) (c : ℕ) (a : Fin (c + 1)) :
    (⋀[R]^(a : ℕ) F) ⊗[R] (⋀[R]^(c - a) L) →ₗ[R] ⋀[R]^c H :=
  (LinearEquiv.ofEq _ _ (by rw [Nat.add_sub_cancel' (Nat.lt_succ_iff.1 a.2)])).toLinearMap ∘ₗ
    wedgeMap i s a (c - a)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_wedgePiece (i : F →ₗ[R] H) (s : L →ₗ[R] H) (c : ℕ) (a : Fin (c + 1))
    (t : (⋀[R]^(a : ℕ) F) ⊗[R] (⋀[R]^(c - a) L)) :
    (wedgePiece i s c a t : ExteriorAlgebra R H) = wedgeMap i s a (c - a) t := rfl

noncomputable def wedgeSum (i : F →ₗ[R] H) (s : L →ₗ[R] H) (c : ℕ) :
    (∀ a : Fin (c + 1), (⋀[R]^(a : ℕ) F) ⊗[R] (⋀[R]^(c - a) L)) →ₗ[R] ⋀[R]^c H :=
  LinearMap.lsum R _ ℕ (wedgePiece i s c)

/- English proof (translation)
Simplify using `[wedgeSum, LinearMap.lsum_apply, coe_wedgePiece]`.
-/
theorem coe_wedgeSum (i : F →ₗ[R] H) (s : L →ₗ[R] H) (c : ℕ)
    (t : ∀ a : Fin (c + 1), (⋀[R]^(a : ℕ) F) ⊗[R] (⋀[R]^(c - a) L)) :
    (wedgeSum i s c t : ExteriorAlgebra R H) =
      ∑ a : Fin (c + 1), (wedgeMap i s a (c - a) (t a) : ExteriorAlgebra R H) := by
  simp [wedgeSum, LinearMap.lsum_apply, coe_wedgePiece]

/- English proof (translation)
Rewrite using `[wedgeSum, LinearMap.lsum_apply, LinearMap.sum_apply, Finset.sum_eq_single a]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb]`. Simplify using the standard rewrite rules.
-/
theorem wedgeSum_single (i : F →ₗ[R] H) (s : L →ₗ[R] H) (c : ℕ) (a : Fin (c + 1))
    (t : (⋀[R]^(a : ℕ) F) ⊗[R] (⋀[R]^(c - a) L)) :
    wedgeSum i s c (Pi.single a t) = wedgePiece i s c a t := by
  rw [wedgeSum, LinearMap.lsum_apply, LinearMap.sum_apply, Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

/- English proof (translation)
Take `⟨Ψ, hΨ⟩` from `exists_bigradedProj hri hrs hπi hπs`. Establish `key : ∀ (a b a' b' : ℕ) (t : (⋀[R]^a F) ⊗[R] (⋀[R]^b L)), Ψ a' b' (wedgeMap i s a b t : ExteriorAlgebra R H) = TensorProduct.map (gradeProj R F a' ∘ₗ (⋀[R]^a F).subtype) (gradeProj R L b' ∘ₗ (⋀[R]^b L).subtype) t`. Introduce `a b a' b' t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add x y hx hy`. Simplify using `only [map_add, Submodule.coe_add] at hx hy ⊢`. Rewrite using `[hx, hy]`. Consider the case `tmul x y`. Rewrite using `[hΨ, TensorProduct.map_tmul]`.

Both sides reduce to the same expression. Establish `hl : ∀ t (a' : Fin (c + 1)), Ψ a' (c - a') (wedgeSum i s c t : ExteriorAlgebra R H) = t a'`. Introduce `t a'`. Rewrite using `[coe_wedgeSum, map_sum, Finset.sum_eq_single a']`. Rewrite using `[key]`.

Establish `h₁ : gradeProj R F a' ∘ₗ (⋀[R]^(a' : ℕ) F).subtype = LinearMap.id` using `LinearMap.ext gradeProj_same`. Establish `h₂ : gradeProj R L (c - a') ∘ₗ (⋀[R]^(c - a') L).subtype = LinearMap.id` using `LinearMap.ext gradeProj_same`. Rewrite using `[h₁, h₂, TensorProduct.map_id, LinearMap.id_apply]`. Introduce `a _ hne`. Rewrite using `[key]`.

Establish `h₁ : gradeProj R F a' ∘ₗ (⋀[R]^(a : ℕ) F).subtype = 0` using `LinearMap.ext (gradeProj_ne (Fin.val_ne_of_ne hne))`. Rewrite using `[h₁, TensorProduct.map_zero_left, LinearMap.zero_apply]`. Simplify using the standard rewrite rules. Introduce `t t' h`. Use function extensionality and compare the values at `a'`.

Rewrite using `[← hl t a', ← hl t' a', h]`.
-/
theorem wedgeSum_injective {i : F →ₗ[R] H} {s : L →ₗ[R] H} {r : H →ₗ[R] F} {π : H →ₗ[R] L}
    (hri : ∀ x, r (i x) = x) (hrs : ∀ y, r (s y) = 0) (hπi : ∀ x, π (i x) = 0)
    (hπs : ∀ y, π (s y) = y) (c : ℕ) : Injective (wedgeSum i s c) := by
  obtain ⟨Ψ, hΨ⟩ := exists_bigradedProj hri hrs hπi hπs
  have key : ∀ (a b a' b' : ℕ) (t : (⋀[R]^a F) ⊗[R] (⋀[R]^b L)),
      Ψ a' b' (wedgeMap i s a b t : ExteriorAlgebra R H) =
        TensorProduct.map (gradeProj R F a' ∘ₗ (⋀[R]^a F).subtype)
          (gradeProj R L b' ∘ₗ (⋀[R]^b L).subtype) t := by
    intro a b a' b' t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [map_add, Submodule.coe_add] at hx hy ⊢
      rw [hx, hy]
    | tmul x y =>
      rw [hΨ, TensorProduct.map_tmul]
      rfl
  have hl : ∀ t (a' : Fin (c + 1)),
      Ψ a' (c - a') (wedgeSum i s c t : ExteriorAlgebra R H) = t a' := by
    intro t a'
    rw [coe_wedgeSum, map_sum, Finset.sum_eq_single a']
    · rw [key]
      have h₁ : gradeProj R F a' ∘ₗ (⋀[R]^(a' : ℕ) F).subtype = LinearMap.id :=
        LinearMap.ext gradeProj_same
      have h₂ : gradeProj R L (c - a') ∘ₗ (⋀[R]^(c - a') L).subtype = LinearMap.id :=
        LinearMap.ext gradeProj_same
      rw [h₁, h₂, TensorProduct.map_id, LinearMap.id_apply]
    · intro a _ hne
      rw [key]
      have h₁ : gradeProj R F a' ∘ₗ (⋀[R]^(a : ℕ) F).subtype = 0 :=
        LinearMap.ext (gradeProj_ne (Fin.val_ne_of_ne hne))
      rw [h₁, TensorProduct.map_zero_left, LinearMap.zero_apply]
    · simp
  intro t t' h
  funext a'
  rw [← hl t a', ← hl t' a', h]

/- English proof (translation)
Use `set A := LinearMap.range (ExteriorAlgebra.ι R ∘ₗ i) with hA`. Use `set B := LinearMap.range (ExteriorAlgebra.ι R ∘ₗ s) with hB`. Establish `hAB : LinearMap.range (ExteriorAlgebra.ι R : H →ₗ[R] _) = A + B`. Rewrite using `[hA, hB, LinearMap.range_comp, LinearMap.range_comp, Submodule.add_eq_sup, ← Submodule.map_sup, hsup, Submodule.map_top]`. Establish `key : ∀ C D : Submodule R (ExteriorAlgebra R H), C ≤ LinearMap.range (ExteriorAlgebra.ι R : H →ₗ[R] _) → D ≤ LinearMap.range (ExteriorAlgebra.ι R : H →ₗ[R] _) → C * D ≤ D * C`.

Introduce `C D hC hD`. Use `Submodule.mul_le.2 fun x hx y hy => ?_` and prove the remaining obligations. Take `⟨u, rfl⟩` from `hC hx`. Take `⟨v, rfl⟩` from `hD hy`. Rewrite using `[eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap u v)]`.

Conclude with `Submodule.neg_mem _ (Submodule.mul_mem_mul hy hx)`. Establish `hA' : A ≤ LinearMap.range (ExteriorAlgebra.ι R : H →ₗ[R] _)` using `hAB ▸ le_sup_left`. Establish `hB' : B ≤ LinearMap.range (ExteriorAlgebra.ι R : H →ₗ[R] _)` using `hAB ▸ le_sup_right`. Establish `hc : Commute A B` using `le_antisymm (key _ _ hA' hB') (key _ _ hB' hA')`. Take `⟨S, hS⟩ : ∃ S, S = (LinearMap.range (wedgeSum i s c)).map (⋀[R]^c H).subtype` from `⟨_, rfl⟩`.

Establish `hpiece : ∀ k l, k + l = c → A ^ k * B ^ l ≤ S`. Introduce `k l hkl`. Take `rfl : l = c - k` from `by omega`. Establish `hk : k < c + 1` using `by omega`. Use `Submodule.mul_le.2 fun x hx y hy => ?_` and prove the remaining obligations.

Rewrite `hx`, `hy` using `[range_pow_eq_map]`. Take `⟨x, hx, rfl⟩` from `hx`. Take `⟨y, hy, rfl⟩` from `hy`. Rewrite using `[hS]`. Use `⟨wedgeSum i s c (Pi.single (⟨k, hk⟩ : Fin (c + 1)) ((⟨x, hx⟩ : ⋀[R]^k F) ⊗ₜ (⟨y, hy⟩ : ⋀[R]^(c - k) L))), ⟨_, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[wedgeSum_single, Submodule.subtype_apply, coe_wedgePiece]`. Conclude with `coe_wedgeMap_tmul _ _ _ _`. Establish `hle : (⋀[R]^c H) ≤ S`. Rewrite using `[ExteriorAlgebra.exteriorPower, hAB, hc.add_pow']`. Use `Finset.sum_induction _ (· ≤ S) (fun x y hx hy => sup_le hx hy) bot_le ?_` and prove the remaining obligations.

Introduce and unpack `⟨k, l⟩ hkl`. Rewrite `hkl` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Use `hpiece k l hkl` as an intermediate fact. Generalize the expression as in `c.choose (k, l).1 = n`. Proceed by induction on `n with`.

Consider the case `zero => rw [zero_nsmul]`. Conclude with `bot_le`. Consider the case `succ n ih => rw [succ_nsmul]`. Conclude with `sup_le ih this`. Introduce `z`.

Establish `hz` using `hle z.2`. Rewrite `hz` using `[hS]`. Take `⟨_, ⟨t, rfl⟩, ht⟩` from `hz`. Conclude with `⟨t, Subtype.ext ht⟩`.
-/
theorem wedgeSum_surjective {i : F →ₗ[R] H} {s : L →ₗ[R] H}
    (hsup : LinearMap.range i ⊔ LinearMap.range s = ⊤) (c : ℕ) :
    Surjective (wedgeSum i s c) := by
  set A := LinearMap.range (ExteriorAlgebra.ι R ∘ₗ i) with hA
  set B := LinearMap.range (ExteriorAlgebra.ι R ∘ₗ s) with hB
  have hAB : LinearMap.range (ExteriorAlgebra.ι R : H →ₗ[R] _) = A + B := by
    rw [hA, hB, LinearMap.range_comp, LinearMap.range_comp, Submodule.add_eq_sup,
      ← Submodule.map_sup, hsup, Submodule.map_top]
  have key : ∀ C D : Submodule R (ExteriorAlgebra R H),
      C ≤ LinearMap.range (ExteriorAlgebra.ι R : H →ₗ[R] _) →
      D ≤ LinearMap.range (ExteriorAlgebra.ι R : H →ₗ[R] _) → C * D ≤ D * C := by
    intro C D hC hD
    refine Submodule.mul_le.2 fun x hx y hy => ?_
    obtain ⟨u, rfl⟩ := hC hx
    obtain ⟨v, rfl⟩ := hD hy
    rw [eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap u v)]
    exact Submodule.neg_mem _ (Submodule.mul_mem_mul hy hx)
  have hA' : A ≤ LinearMap.range (ExteriorAlgebra.ι R : H →ₗ[R] _) := hAB ▸ le_sup_left
  have hB' : B ≤ LinearMap.range (ExteriorAlgebra.ι R : H →ₗ[R] _) := hAB ▸ le_sup_right
  have hc : Commute A B := le_antisymm (key _ _ hA' hB') (key _ _ hB' hA')
  obtain ⟨S, hS⟩ : ∃ S, S = (LinearMap.range (wedgeSum i s c)).map (⋀[R]^c H).subtype := ⟨_, rfl⟩
  have hpiece : ∀ k l, k + l = c → A ^ k * B ^ l ≤ S := by
    intro k l hkl
    obtain rfl : l = c - k := by omega
    have hk : k < c + 1 := by omega
    refine Submodule.mul_le.2 fun x hx y hy => ?_
    rw [range_pow_eq_map] at hx hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    rw [hS]
    refine ⟨wedgeSum i s c (Pi.single (⟨k, hk⟩ : Fin (c + 1))
      ((⟨x, hx⟩ : ⋀[R]^k F) ⊗ₜ (⟨y, hy⟩ : ⋀[R]^(c - k) L))), ⟨_, rfl⟩, ?_⟩
    rw [wedgeSum_single, Submodule.subtype_apply, coe_wedgePiece]
    exact coe_wedgeMap_tmul _ _ _ _
  have hle : (⋀[R]^c H) ≤ S := by
    rw [ExteriorAlgebra.exteriorPower, hAB, hc.add_pow']
    refine Finset.sum_induction _ (· ≤ S) (fun x y hx hy => sup_le hx hy) bot_le ?_
    rintro ⟨k, l⟩ hkl
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
    have := hpiece k l hkl
    generalize c.choose (k, l).1 = n
    induction n with
    | zero => rw [zero_nsmul]; exact bot_le
    | succ n ih => rw [succ_nsmul]; exact sup_le ih this
  intro z
  have hz := hle z.2
  rw [hS] at hz
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := hz
  exact ⟨t, Subtype.ext ht⟩

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem ιMulti_cast {m n : ℕ} (h : n = m) (v : Fin m → H) :
    ExteriorAlgebra.ιMulti R m v = ExteriorAlgebra.ιMulti R n (v ∘ Fin.cast h) := by
  subst h
  rfl

/- English proof (translation)
Introduce `R F L H _ _ _ _ _ _ _ i s r π hri hrs hπi hπs hsup c`. Use `⟨LinearEquiv.ofBijective (wedgeSum i s c) ⟨wedgeSum_injective hri hrs hπi hπs c, wedgeSum_surjective hsup c⟩, fun a f h => Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(wedgeSum i s c _ : ExteriorAlgebra R H) = _`. Rewrite using `[wedgeSum_single, coe_wedgePiece, coe_wedgeMap_tmul]`. Simplify using `only [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.map_apply_ιMulti, ExteriorAlgebra.ιMulti_mul_ιMulti]`.

Conclude with `ιMulti_cast _ _`.
-/
theorem exteriorPower_split :
    ∀ (R F L H : Type) [CommRing R] [AddCommGroup F] [Module R F] [AddCommGroup L] [Module R L]
      [AddCommGroup H] [Module R H] (i : F →ₗ[R] H) (s : L →ₗ[R] H) (r : H →ₗ[R] F)
      (π : H →ₗ[R] L) (hri : ∀ x, r (i x) = x) (hrs : ∀ y, r (s y) = 0)
      (hπi : ∀ x, π (i x) = 0) (hπs : ∀ y, π (s y) = y)
      (hsup : LinearMap.range i ⊔ LinearMap.range s = ⊤) (c : ℕ),
      ∃ e : (∀ a : Fin (c + 1), (⋀[R]^(a : ℕ) F) ⊗[R] (⋀[R]^(c - a) L)) ≃ₗ[R] ⋀[R]^c H,
        ∀ (a : Fin (c + 1)) (f : Fin a → F) (h : Fin (c - a) → L),
          e (Pi.single a (exteriorPower.ιMulti R a f ⊗ₜ exteriorPower.ιMulti R (c - a) h)) =
            exteriorPower.ιMulti R c
              (Fin.append (fun k => i (f k)) (fun k => s (h k)) ∘
                Fin.cast (by have := a.2; omega)) := by
  intro R F L H _ _ _ _ _ _ _ i s r π hri hrs hπi hπs hsup c
  refine ⟨LinearEquiv.ofBijective (wedgeSum i s c)
    ⟨wedgeSum_injective hri hrs hπi hπs c, wedgeSum_surjective hsup c⟩, fun a f h =>
      Subtype.ext ?_⟩
  change (wedgeSum i s c _ : ExteriorAlgebra R H) = _
  rw [wedgeSum_single, coe_wedgePiece, coe_wedgeMap_tmul]
  simp only [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.map_apply_ιMulti,
    ExteriorAlgebra.ιMulti_mul_ιMulti]
  exact ιMulti_cast _ _

end GlobalTheory.CompanionTheory.TopExtSplit
