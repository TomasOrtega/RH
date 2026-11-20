import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteHopfPointsSeparate
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FourierInv

/- English proof (translation)
Proceed by induction on `t with`. Consider the case `zero => simp`. Consider the case `add s t hs ht => simp only [map_add, hs, ht]`. Consider the case `tmul a b => simp`.
-/
theorem pair_points {K : Type} [Field K] {H : Type} [CommRing H] [HopfAlgebra K H]
    [FiniteDimensional K H] (n n' : H →ₐ[K] K) (t : H ⊗[K] H) :
    CartierDual.pair K H H ((toConv n.toLinearMap : CartierDual K H) ⊗ₜ toConv n'.toLinearMap) t =
      (Algebra.TensorProduct.lift n n' (fun _ _ => Commute.all _ _) : H ⊗[K] H →ₐ[K] K) t := by
  induction t with
  | zero => simp
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul a b => simp

/- English proof (translation)
Use `CartierDual.ext_apply fun h => ?_` and prove the remaining obligations. Rewrite using `[CartierDual.mul_apply, pair_points]`. Conclude with `AlgHom.convMul_apply _ _ h`.
-/
theorem delta_mul {K : Type} [Field K] {H : Type} [CommRing H] [HopfAlgebra K H]
    [FiniteDimensional K H] (n n' : H →ₐ[K] K) :
    (toConv (toConv n * toConv n').ofConv.toLinearMap : CartierDual K H) =
      toConv n.toLinearMap * toConv n'.toLinearMap := by
  refine CartierDual.ext_apply fun h => ?_
  rw [CartierDual.mul_apply, pair_points]
  exact AlgHom.convMul_apply _ _ h

/- English proof (translation)
Use `CartierDual.ext_apply fun h => ?_` and prove the remaining obligations. Rewrite using `[CartierDual.one_apply]`. Conclude with `AlgHom.convOne_apply (R := K) (A := K) (C := H) h`.
-/
theorem delta_one {K : Type} [Field K] {H : Type} [CommRing H] [HopfAlgebra K H]
    [FiniteDimensional K H] :
    (toConv (1 : WithConv (H →ₐ[K] K)).ofConv.toLinearMap : CartierDual K H) = 1 := by
  refine CartierDual.ext_apply fun h => ?_
  rw [CartierDual.one_apply]
  exact AlgHom.convOne_apply (R := K) (A := K) (C := H) h

/- English proof (translation)
Use `sub_eq_zero.1 (hsep _ fun n => ?_)` and prove the remaining obligations. Simplify using `[he]`.
-/
theorem eq_sum_delta {K : Type} [Field K] {H : Type} [CommRing H] [Algebra K H]
    [Fintype (H →ₐ[K] K)] [DecidableEq (H →ₐ[K] K)] (e : (H →ₐ[K] K) → H)
    (he : ∀ m n : H →ₐ[K] K, n (e m) = if n = m then 1 else 0)
    (hsep : ∀ a : H, (∀ m : H →ₐ[K] K, m a = 0) → a = 0) (h : H) :
    h = ∑ m : H →ₐ[K] K, m h • e m := by
  refine sub_eq_zero.1 (hsep _ fun n => ?_)
  simp [he]

/- English proof (translation)
Introduce `K _ H _ _ _ _ _ _ e he hsep F hFs q`. Establish `hcounit : ∀ n : H →ₐ[K] K, Bialgebra.counitAlgHom K H (F (toConv n.toLinearMap)) = 1`. Introduce `n`. Rewrite using `[Bialgebra.counitAlgHom_apply, CoalgHomClass.counit_comp_apply]`. Simplify using the standard rewrite rules.

Distinguish the cases in `hq : q = Bialgebra.counitAlgHom K H`. Rewrite using `[if_pos hq, hq]`. Simplify using `[hcounit]`. Rewrite using `[if_neg hq]`. Use `letI : Fintype (WithConv (H →ₐ[K] K)) := Fintype.ofEquiv _ (WithConv.equiv _).symm`.

Set `χ : WithConv (H →ₐ[K] K) →* K` to `{ toFun := fun g => q (F (toConv g.ofConv.toLinearMap)) map_one' := by rw [delta_one, map_one, map_one] map_mul' := fun g g' => by`. Establish `h` using `delta_mul (K := K) (H := H) g.ofConv g'.ofConv`. Simplify using `only [WithConv.toConv_ofConv] at h`. Rewrite using `[h, map_mul, map_mul] }`. Establish `hsum : ∑ n : H →ₐ[K] K, q (F (toConv n.toLinearMap)) = ∑ g, χ g` using `Fintype.sum_equiv (WithConv.equiv _).symm _ _ fun n => rfl`.

Rewrite using `[hsum]`. Use `sum_hom_units_eq_zero χ fun hχ => hq (AlgHom.ext fun h => ?_)` and prove the remaining obligations. Take `⟨d, rfl⟩` from `hFs h`. Establish `hd : d = ∑ m : H →ₐ[K] K, d (e m) • (toConv m.toLinearMap : CartierDual K H)`. Use `CartierDual.ext_apply fun h' => ?_` and prove the remaining obligations.

Use `conv_lhs => rw [eq_sum_delta e he hsep h']`. Simplify using `[mul_comm]`. Establish `h1 : ∀ m : H →ₐ[K] K, q (F (toConv m.toLinearMap)) = 1` using `fun m => DFunLike.congr_fun hχ (toConv m)`. Rewrite using `[hd]`. Simplify using `[map_sum, map_smul, h1, hcounit]`.
-/
theorem sum_character : ∀ (K : Type) [Field K] (H : Type) [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [FiniteDimensional K H] [Fintype (H →ₐ[K] K)] [DecidableEq (H →ₐ[K] K)] (e : (H →ₐ[K] K) → H), (∀ m n : H →ₐ[K] K, n (e m) = if n = m then 1 else 0) → (∀ a : H, (∀ m : H →ₐ[K] K, m a = 0) → a = 0) → ∀ (F : CartierDual K H →ₐc[K] H), Function.Surjective F → ∀ q : H →ₐ[K] K, ∑ n : H →ₐ[K] K, q (F (toConv n.toLinearMap)) = if q = Bialgebra.counitAlgHom K H then (Fintype.card (H →ₐ[K] K) : K) else 0 := by
  intro K _ H _ _ _ _ _ _ e he hsep F hFs q
  have hcounit : ∀ n : H →ₐ[K] K, Bialgebra.counitAlgHom K H (F (toConv n.toLinearMap)) = 1 := by
    intro n
    rw [Bialgebra.counitAlgHom_apply, CoalgHomClass.counit_comp_apply]
    simp
  by_cases hq : q = Bialgebra.counitAlgHom K H
  · rw [if_pos hq, hq]
    simp [hcounit]
  rw [if_neg hq]
  letI : Fintype (WithConv (H →ₐ[K] K)) := Fintype.ofEquiv _ (WithConv.equiv _).symm
  let χ : WithConv (H →ₐ[K] K) →* K :=
    { toFun := fun g => q (F (toConv g.ofConv.toLinearMap))
      map_one' := by rw [delta_one, map_one, map_one]
      map_mul' := fun g g' => by
        have h := delta_mul (K := K) (H := H) g.ofConv g'.ofConv
        simp only [WithConv.toConv_ofConv] at h
        rw [h, map_mul, map_mul] }
  have hsum : ∑ n : H →ₐ[K] K, q (F (toConv n.toLinearMap)) = ∑ g, χ g :=
    Fintype.sum_equiv (WithConv.equiv _).symm _ _ fun n => rfl
  rw [hsum]
  refine sum_hom_units_eq_zero χ fun hχ => hq (AlgHom.ext fun h => ?_)
  obtain ⟨d, rfl⟩ := hFs h
  have hd : d = ∑ m : H →ₐ[K] K, d (e m) • (toConv m.toLinearMap : CartierDual K H) := by
    refine CartierDual.ext_apply fun h' => ?_
    conv_lhs => rw [eq_sum_delta e he hsep h']
    simp [mul_comm]
  have h1 : ∀ m : H →ₐ[K] K, q (F (toConv m.toLinearMap)) = 1 := fun m =>
    DFunLike.congr_fun hχ (toConv m)
  rw [hd]
  simp [map_sum, map_smul, h1, hcounit]

/- English proof (translation)
Introduce `K _ _ H _ _ _ _ _ _ e he hsep Λ y hΛ hy hy2`. Set `T : (H →ₐ[K] K) → H → H` to `fun m h => TensorProduct.lid K H (LinearMap.rTensor H m.toLinearMap (comul (R := K) h))`. Establish `hT : ∀ (m p : H →ₐ[K] K) (h : H), p (T m h) = (toConv m * toConv p).ofConv h`. Introduce `m p h`. Rewrite using `[AlgHom.convMul_apply]`.

Simplify using `only [T]`. Proceed by induction on `(comul (R := K) h) with`. Consider the case `zero => simp`. Consider the case `add s t hs ht => simp only [map_add, hs, ht]`. Consider the case `tmul a b => simp`.

Establish `hΛT : ∀ (m : H →ₐ[K] K) (h : H), Λ (T m h) = Λ h`. Introduce `m h`. Establish `h0 : (toConv m.toLinearMap : CartierDual K H) * Λ = Λ`. Rewrite using `[hΛ, CartierDual.counit_apply]`. Simplify using the standard rewrite rules.

Establish `h1` using `congrArg (fun d : CartierDual K H => d h) h0`. Establish `h2 : ∀ t : H ⊗[K] H, CartierDual.pair K H H ((toConv m.toLinearMap : CartierDual K H) ⊗ₜ Λ) t = Λ (TensorProduct.lid K H (LinearMap.rTensor H m.toLinearMap t))`. Introduce `t`. Proceed by induction on `t with`. Consider the case `zero => simp`.

Consider the case `add s t hs ht => simp only [map_add, hs, ht]`. Consider the case `tmul a b => simp`. Simplify using `only [CartierDual.mul_apply, h2] at h1`. Conclude with `h1`. Use `set u : H →ₐ[K] K := (1 : WithConv (H →ₐ[K] K)).ofConv with hu`.

Establish `hTe : ∀ n : H →ₐ[K] K, T n (e n) = e u`. Introduce `n`. Use `sub_eq_zero.1 (hsep _ fun p => ?_)` and prove the remaining obligations. Rewrite using `[map_sub, sub_eq_zero, hT, he, he]`. Establish `: ((toConv n * toConv p).ofConv = n) ↔ (p = u)`.

Rewrite using `[← WithConv.toConv_injective.eq_iff, WithConv.toConv_ofConv, mul_eq_left, hu]`. Conclude with `⟨fun h => by rw [← h, WithConv.ofConv_toConv], fun h => by rw [h, WithConv.toConv_ofConv]⟩`. Simplify using `only [this]`. Use `set c : K := Λ (e u) with hc`. Establish `hΛe : ∀ n : H →ₐ[K] K, Λ (e n) = c` using `fun n => by rw [hc, ← hTe n, hΛT]`.

Establish `hΛf : ∀ h : H, Λ h = c * ∑ m : H →ₐ[K] K, m h`. Introduce `h`. Use `conv_lhs => rw [eq_sum_delta e he hsep h]`. Simplify using `[map_sum, hΛe, Finset.mul_sum, mul_comm]`. Use `⟨c, ?_, hΛf⟩` and prove the remaining obligations.

Establish `hN : (Fintype.card (H →ₐ[K] K) : K) ≠ 0`. Establish `: 0 < Fintype.card (H →ₐ[K] K)` using `Fintype.card_pos_iff.2 ⟨Bialgebra.counitAlgHom K H⟩`. Conclude with `this.ne'` after adjusting the coercions. Establish `hy' : y = c * (Fintype.card (H →ₐ[K] K) : K)`. Rewrite using `[← hy, CartierDual.counit_apply, hΛf]`.

Simplify using the standard rewrite rules. Establish `h3 : (c ^ 2 * (Fintype.card (H →ₐ[K] K) : K) - 1) * (Fintype.card (H →ₐ[K] K) : K) = 0`. Rewrite `hy2` using `[hy']`. Take the linear combination `hy2`. Conclude with `sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hN)`.
-/
theorem integral_eq_sum : ∀ (K : Type) [Field K] [CharZero K] (H : Type) [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [FiniteDimensional K H] [Fintype (H →ₐ[K] K)] [DecidableEq (H →ₐ[K] K)] (e : (H →ₐ[K] K) → H), (∀ m n : H →ₐ[K] K, n (e m) = if n = m then 1 else 0) → (∀ a : H, (∀ m : H →ₐ[K] K, m a = 0) → a = 0) → ∀ (Λ : CartierDual K H) (y : K), (∀ d : CartierDual K H, d * Λ = algebraMap K _ (Coalgebra.counit (R := K) d) * Λ) → Coalgebra.counit (R := K) Λ = y → y ^ 2 = (Fintype.card (H →ₐ[K] K) : K) → ∃ c : K, c ^ 2 * (Fintype.card (H →ₐ[K] K) : K) = 1 ∧ ∀ h : H, Λ h = c * ∑ m : H →ₐ[K] K, m h := by
  intro K _ _ H _ _ _ _ _ _ e he hsep Λ y hΛ hy hy2
  let T : (H →ₐ[K] K) → H → H := fun m h =>
    TensorProduct.lid K H (LinearMap.rTensor H m.toLinearMap (comul (R := K) h))
  have hT : ∀ (m p : H →ₐ[K] K) (h : H), p (T m h) = (toConv m * toConv p).ofConv h := by
    intro m p h
    rw [AlgHom.convMul_apply]
    simp only [T]
    induction (comul (R := K) h) with
    | zero => simp
    | add s t hs ht => simp only [map_add, hs, ht]
    | tmul a b => simp
  have hΛT : ∀ (m : H →ₐ[K] K) (h : H), Λ (T m h) = Λ h := by
    intro m h
    have h0 : (toConv m.toLinearMap : CartierDual K H) * Λ = Λ := by
      rw [hΛ, CartierDual.counit_apply]
      simp
    have h1 := congrArg (fun d : CartierDual K H => d h) h0
    have h2 : ∀ t : H ⊗[K] H, CartierDual.pair K H H
        ((toConv m.toLinearMap : CartierDual K H) ⊗ₜ Λ) t =
        Λ (TensorProduct.lid K H (LinearMap.rTensor H m.toLinearMap t)) := by
      intro t
      induction t with
      | zero => simp
      | add s t hs ht => simp only [map_add, hs, ht]
      | tmul a b => simp
    simp only [CartierDual.mul_apply, h2] at h1
    exact h1
  set u : H →ₐ[K] K := (1 : WithConv (H →ₐ[K] K)).ofConv with hu
  have hTe : ∀ n : H →ₐ[K] K, T n (e n) = e u := by
    intro n
    refine sub_eq_zero.1 (hsep _ fun p => ?_)
    rw [map_sub, sub_eq_zero, hT, he, he]
    have : ((toConv n * toConv p).ofConv = n) ↔ (p = u) := by
      rw [← WithConv.toConv_injective.eq_iff, WithConv.toConv_ofConv, mul_eq_left, hu]
      exact ⟨fun h => by rw [← h, WithConv.ofConv_toConv], fun h => by rw [h, WithConv.toConv_ofConv]⟩
    simp only [this]
  set c : K := Λ (e u) with hc
  have hΛe : ∀ n : H →ₐ[K] K, Λ (e n) = c := fun n => by rw [hc, ← hTe n, hΛT]
  have hΛf : ∀ h : H, Λ h = c * ∑ m : H →ₐ[K] K, m h := by
    intro h
    conv_lhs => rw [eq_sum_delta e he hsep h]
    simp [map_sum, hΛe, Finset.mul_sum, mul_comm]
  refine ⟨c, ?_, hΛf⟩
  have hN : (Fintype.card (H →ₐ[K] K) : K) ≠ 0 := by
    have : 0 < Fintype.card (H →ₐ[K] K) := Fintype.card_pos_iff.2 ⟨Bialgebra.counitAlgHom K H⟩
    exact_mod_cast this.ne'
  have hy' : y = c * (Fintype.card (H →ₐ[K] K) : K) := by
    rw [← hy, CartierDual.counit_apply, hΛf]
    simp
  have h3 : (c ^ 2 * (Fintype.card (H →ₐ[K] K) : K) - 1) * (Fintype.card (H →ₐ[K] K) : K) = 0 := by
    rw [hy'] at hy2
    linear_combination hy2
  exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hN)
end GlobalTheory.FourierInv

namespace GlobalTheory.FourierInv

variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {H : Type} [CommRing H] [HopfAlgebra K H]
  [IsCocomm K H] [FiniteDimensional K H]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `HopfPoints.finite_points_separate_rank K K H`. Use `⟨h1, h2, ?_⟩` and prove the remaining obligations. Establish `h` using `h3 ⟨⊥, Ideal.isPrime_bot⟩`. Rewrite `h` using `[Module.rankAtStalk_eq_finrank_of_free]`. Conclude with `h` after adjusting the coercions.
-/
theorem points_facts : Finite (H →ₐ[K] K) ∧ (∀ a : H, (∀ m : H →ₐ[K] K, m a = 0) → a = 0) ∧
    Module.finrank K H = Nat.card (H →ₐ[K] K) := by
  obtain ⟨h1, h2, h3⟩ := HopfPoints.finite_points_separate_rank K K H
  refine ⟨h1, h2, ?_⟩
  have h := h3 ⟨⊥, Ideal.isPrime_bot⟩
  rw [Module.rankAtStalk_eq_finrank_of_free] at h
  exact_mod_cast h

/- English proof (translation)
Take `⟨hfin, hsep, hrk⟩` from `points_facts (K := K) (H := H)`. Use `Fintype.ofFinite (H →ₐ[K] K)` as an intermediate fact. Set `ev : H →ₗ[K] ((H →ₐ[K] K) → K)` to `LinearMap.pi fun m => m.toLinearMap`. Establish `hinj : Function.Injective ev`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `a ha`. Conclude with `hsep a fun m => congrFun ha m`. Establish `hsurj : Function.Surjective ev` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hrk, Nat.card_eq_fintype_card])).1 hinj`. Use `⟨fun m => (hsurj (Pi.single m 1)).choose, fun m n => ?_⟩` and prove the remaining obligations. Use `congrFun (hsurj (Pi.single m 1)).choose_spec n` as an intermediate fact.

Simplify `this` using `[ev, Pi.single_apply]`.
-/
theorem exists_delta [DecidableEq (H →ₐ[K] K)] :
    ∃ e : (H →ₐ[K] K) → H, ∀ m n : H →ₐ[K] K, n (e m) = if n = m then 1 else 0 := by
  obtain ⟨hfin, hsep, hrk⟩ := points_facts (K := K) (H := H)
  have := Fintype.ofFinite (H →ₐ[K] K)
  let ev : H →ₗ[K] ((H →ₐ[K] K) → K) := LinearMap.pi fun m => m.toLinearMap
  have hinj : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    exact hsep a fun m => congrFun ha m
  have hsurj : Function.Surjective ev :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simp [hrk, Nat.card_eq_fintype_card])).1 hinj
  refine ⟨fun m => (hsurj (Pi.single m 1)).choose, fun m n => ?_⟩
  have := congrFun (hsurj (Pi.single m 1)).choose_spec n
  simpa [ev, Pi.single_apply] using this

end GlobalTheory.FourierInv

namespace GlobalTheory.FourierInv

/- English proof (translation)
Establish `hd : comul (R` using `K) (toConv n.toLinearMap : CartierDual K H) = toConv n.toLinearMap ⊗ₜ toConv n.toLinearMap := by`. Rewrite using `[CartierDual.comul_eq_iff]`. Introduce `a b`. Simplify using the standard rewrite rules. Establish `hF : comul (R` using `K) (F (toConv n.toLinearMap)) = F (toConv n.toLinearMap) ⊗ₜ F (toConv n.toLinearMap) := by`.

Rewrite using `[← CoalgHomClass.map_comp_comul_apply, hd, TensorProduct.map_tmul]`. Both sides reduce to the same expression. Rewrite using `[AlgHom.convMul_apply, hF]`. Both sides reduce to the same expression.
-/
theorem convMul_apply_image {K : Type} [Field K] {H : Type} [CommRing H] [HopfAlgebra K H]
    [FiniteDimensional K H] (F : CartierDual K H →ₐc[K] H) (n p q : H →ₐ[K] K) :
    (toConv p * toConv q).ofConv (F (toConv n.toLinearMap)) =
      p (F (toConv n.toLinearMap)) * q (F (toConv n.toLinearMap)) := by
  have hd : comul (R := K) (toConv n.toLinearMap : CartierDual K H) =
      toConv n.toLinearMap ⊗ₜ toConv n.toLinearMap := by
    rw [CartierDual.comul_eq_iff]
    intro a b
    simp
  have hF : comul (R := K) (F (toConv n.toLinearMap)) =
      F (toConv n.toLinearMap) ⊗ₜ F (toConv n.toLinearMap) := by
    rw [← CoalgHomClass.map_comp_comul_apply, hd, TensorProduct.map_tmul]
    rfl
  rw [AlgHom.convMul_apply, hF]
  rfl

/- English proof (translation)
Introduce `K _ _ _ H _ _ _ _ F Λ y hΛ hy hy2 hF a`. Take `⟨hfin, hsep, hrk⟩` from `points_facts (K := K) (H := H)`. Use `Fintype.ofFinite (H →ₐ[K] K)` as an intermediate fact. Take `⟨e, he⟩` from `exists_delta (K := K) (H := H)`. Take `⟨c, hc, hΛf⟩` from `integral_eq_sum K H e he hsep Λ y hΛ hy (hy2.trans (by rw [Nat.card_eq_fintype_card]))`.

Establish `hFs : Function.Surjective F`. Establish `hrk' : Module.finrank K (CartierDual K H) = Module.finrank K H`. Rewrite using `[(CartierDual.toDual K H).finrank_eq, Subspace.dual_finrank_eq]`. Conclude with `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk' (f := (F : CartierDual K H →ₗ[K] H))).1 hF`. Establish `hchar` using `sum_character K H e he hsep F hFs`.

Establish `hψ : ∀ b : H, (toConv (Λ.ofConv ∘ₗ LinearMap.mulLeft K b) : CartierDual K H) = ∑ n : H →ₐ[K] K, (c * n b) • (toConv n.toLinearMap : CartierDual K H)`. Introduce `b`. Use `CartierDual.ext_apply fun h => ?_` and prove the remaining obligations. Simplify using `[hΛf, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`.

Establish `hFψ : ∀ (b : H) (p : H →ₐ[K] K), p (F (toConv (Λ.ofConv ∘ₗ LinearMap.mulLeft K b))) = ∑ n : H →ₐ[K] K, c * n b * p (F (toConv n.toLinearMap))`. Introduce `b p`. Rewrite using `[hψ b, map_sum, map_sum]`. Simplify using `[map_smul]`. Establish `hx : ∀ (φ : CartierDual K H) (n : H →ₐ[K] K), n ((CartierDual.bidual K H).symm (CartierDual.map F φ)) = φ (F (toConv n.toLinearMap))`.

Introduce `φ n`. Conclude with `CartierDual.apply_bidual_symm (CartierDual.map F φ) (toConv n.toLinearMap)`. Establish `hone : ∀ m p : H →ₐ[K] K, ((toConv m * toConv p).ofConv = Bialgebra.counitAlgHom K H) ↔ toConv m = (toConv p)⁻¹`. Introduce `m p`. Rewrite using `[eq_inv_iff_mul_eq_one, ← WithConv.ofConv_injective.eq_iff]`.

Apply the tactic sequence `constructor <;> intro h <;> rw [h] <;> ext <;> simp [AlgHom.convOne_apply]`. Use `sub_eq_zero.1 (hsep _ fun p => ?_)` and prove the remaining obligations. Rewrite using `[map_sub, sub_eq_zero, hFψ]`. Simplify using `only [hx]`. Establish `hφ : ∀ n : H →ₐ[K] K, (toConv (Λ.ofConv ∘ₗ LinearMap.mulLeft K (HopfAlgebra.antipode K a)) : CartierDual K H) (F (toConv n.toLinearMap)) = c * ∑ m : H →ₐ[K] K, m (HopfAlgebra.antipode K a) * m (F (toConv n.toLinearMap))`.

Introduce `n`. Simplify using `[hΛf]`. Simplify using `only [hφ]`. Use `set m₀ : H →ₐ[K] K := ((toConv p)⁻¹ : WithConv (H →ₐ[K] K)).ofConv with hm₀`. Establish `hm₀a : m₀ (HopfAlgebra.antipode K a) = p a`.

Establish `h1 : ((toConv m₀)⁻¹ : WithConv (H →ₐ[K] K)).ofConv a = m₀ (HopfAlgebra.antipode K a)`. Both sides reduce to the same expression. Rewrite using `[← h1, hm₀, WithConv.toConv_ofConv, inv_inv]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [convMul_apply_image, Finset.mul_sum, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Use `_ = c ^ 2 * ∑ m : H →ₐ[K] K, m (HopfAlgebra.antipode K a) * (if (toConv m * toConv p).ofConv = Bialgebra.counitAlgHom K H then (Fintype.card (H →ₐ[K] K) : K) else 0) := by`. Simplify using `only [hchar]`. Use `_ = c ^ 2 * (m₀ (HopfAlgebra.antipode K a) * (Fintype.card (H →ₐ[K] K) : K)) := by`.

Rewrite using `[Finset.sum_eq_single m₀]`. Rewrite using `[if_pos ((hone m₀ p).2 (by rw [hm₀, WithConv.toConv_ofConv]))]`. Introduce `m _ hm`. Rewrite using `[if_neg, mul_zero]`. Introduce `h`.

Conclude with `hm (by rw [hm₀, ← (hone m p).1 h])`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Use `_ = p a := by`. Rewrite using `[hm₀a]`.

Take the linear combination `(p a) * hc`.
-/
theorem inversion_field : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (H : Type) [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [FiniteDimensional K H] (F : CartierDual K H →ₐc[K] H) (Λ : CartierDual K H) (y : K), (∀ d : CartierDual K H, d * Λ = algebraMap K _ (Coalgebra.counit (R := K) d) * Λ) → Coalgebra.counit (R := K) Λ = y → y ^ 2 = (Nat.card (H →ₐ[K] K) : K) → Function.Injective F → ∀ a : H, F (toConv (Λ.ofConv ∘ₗ LinearMap.mulLeft K ((CartierDual.bidual K H).symm (CartierDual.map F (toConv (Λ.ofConv ∘ₗ LinearMap.mulLeft K (HopfAlgebra.antipode K a))))))) = a := by
  intro K _ _ _ H _ _ _ _ F Λ y hΛ hy hy2 hF a
  classical
  obtain ⟨hfin, hsep, hrk⟩ := points_facts (K := K) (H := H)
  have := Fintype.ofFinite (H →ₐ[K] K)
  obtain ⟨e, he⟩ := exists_delta (K := K) (H := H)
  obtain ⟨c, hc, hΛf⟩ := integral_eq_sum K H e he hsep Λ y hΛ hy
    (hy2.trans (by rw [Nat.card_eq_fintype_card]))
  have hFs : Function.Surjective F := by
    have hrk' : Module.finrank K (CartierDual K H) = Module.finrank K H := by
      rw [(CartierDual.toDual K H).finrank_eq, Subspace.dual_finrank_eq]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk'
      (f := (F : CartierDual K H →ₗ[K] H))).1 hF
  have hchar := sum_character K H e he hsep F hFs
  have hψ : ∀ b : H, (toConv (Λ.ofConv ∘ₗ LinearMap.mulLeft K b) : CartierDual K H) =
      ∑ n : H →ₐ[K] K, (c * n b) • (toConv n.toLinearMap : CartierDual K H) := by
    intro b
    refine CartierDual.ext_apply fun h => ?_
    simp [hΛf, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hFψ : ∀ (b : H) (p : H →ₐ[K] K), p (F (toConv (Λ.ofConv ∘ₗ LinearMap.mulLeft K b))) =
      ∑ n : H →ₐ[K] K, c * n b * p (F (toConv n.toLinearMap)) := by
    intro b p
    rw [hψ b, map_sum, map_sum]
    simp [map_smul]
  have hx : ∀ (φ : CartierDual K H) (n : H →ₐ[K] K),
      n ((CartierDual.bidual K H).symm (CartierDual.map F φ)) = φ (F (toConv n.toLinearMap)) := by
    intro φ n
    exact CartierDual.apply_bidual_symm (CartierDual.map F φ) (toConv n.toLinearMap)
  have hone : ∀ m p : H →ₐ[K] K, ((toConv m * toConv p).ofConv = Bialgebra.counitAlgHom K H) ↔
      toConv m = (toConv p)⁻¹ := by
    intro m p
    rw [eq_inv_iff_mul_eq_one, ← WithConv.ofConv_injective.eq_iff]
    constructor <;> intro h <;> rw [h] <;> ext <;> simp [AlgHom.convOne_apply]
  refine sub_eq_zero.1 (hsep _ fun p => ?_)
  rw [map_sub, sub_eq_zero, hFψ]
  simp only [hx]
  have hφ : ∀ n : H →ₐ[K] K,
      (toConv (Λ.ofConv ∘ₗ LinearMap.mulLeft K (HopfAlgebra.antipode K a)) : CartierDual K H)
        (F (toConv n.toLinearMap)) =
        c * ∑ m : H →ₐ[K] K, m (HopfAlgebra.antipode K a) * m (F (toConv n.toLinearMap)) := by
    intro n
    simp [hΛf]
  simp only [hφ]
  set m₀ : H →ₐ[K] K := ((toConv p)⁻¹ : WithConv (H →ₐ[K] K)).ofConv with hm₀
  have hm₀a : m₀ (HopfAlgebra.antipode K a) = p a := by
    have h1 : ((toConv m₀)⁻¹ : WithConv (H →ₐ[K] K)).ofConv a = m₀ (HopfAlgebra.antipode K a) :=
      rfl
    rw [← h1, hm₀, WithConv.toConv_ofConv, inv_inv]
  calc _ = c ^ 2 * ∑ m : H →ₐ[K] K, m (HopfAlgebra.antipode K a) *
        ∑ n : H →ₐ[K] K, (toConv m * toConv p).ofConv (F (toConv n.toLinearMap)) := by
        simp only [convMul_apply_image, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = c ^ 2 * ∑ m : H →ₐ[K] K, m (HopfAlgebra.antipode K a) *
        (if (toConv m * toConv p).ofConv = Bialgebra.counitAlgHom K H then
          (Fintype.card (H →ₐ[K] K) : K) else 0) := by
        simp only [hchar]
    _ = c ^ 2 * (m₀ (HopfAlgebra.antipode K a) * (Fintype.card (H →ₐ[K] K) : K)) := by
        rw [Finset.sum_eq_single m₀]
        · rw [if_pos ((hone m₀ p).2 (by rw [hm₀, WithConv.toConv_ofConv]))]
        · intro m _ hm
          rw [if_neg, mul_zero]
          intro h
          exact hm (by rw [hm₀, ← (hone m p).1 h])
        · intro h
          exact absurd (Finset.mem_univ _) h
    _ = p a := by
        rw [hm₀a]
        linear_combination (p a) * hc

end GlobalTheory.FourierInv
