import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatZeroFromResolutionAndGaga
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef.TermPair

/- English proof (translation)
Establish `memB : ∀ a, a ∈ A → u * a * u⁻¹ ∈ B` using `fun a ha => by`. Rewrite using `[hAB]; exact ⟨a, ha, by simp [MulAut.conj_apply]⟩`. Establish `memA : ∀ b, b ∈ B → u⁻¹ * b * u ∈ A` using `fun b hb => by`. Rewrite `hb` using `[hAB]`. Take `⟨a, ha, rfl⟩` from `hb`.

Simplify `ha` using `[MulAut.conj_apply, mul_assoc]`. Set `e : DoubleCoset.Quotient (A : Set H) (K : Set H) ≃ DoubleCoset.Quotient (B : Set H) (K : Set H)` to `{ toFun := Quotient.map' (u * ·) (fun x y hxy => by`. Take `⟨a, ha, k, hk, rfl⟩` from `DoubleCoset.rel_iff.1 hxy`. Conclude with `DoubleCoset.rel_iff.2 ⟨u * a * u⁻¹, memB a ha, k, hk, by group⟩)`. Use `invFun := Quotient.map' (u⁻¹ * ·) (fun x y hxy => by`.

Take `⟨b, hb, k, hk, rfl⟩` from `DoubleCoset.rel_iff.1 hxy`. Conclude with `DoubleCoset.rel_iff.2 ⟨u⁻¹ * b * u, memA b hb, k, hk, by group⟩)`. Use `left_inv := fun q => by`. Proceed by induction on `q using Quotient.inductionOn' with`. Consider the case `h x`.

Simplify using `only [Quotient.map'_mk'', inv_mul_cancel_left, mul_inv_cancel_left]`. Both sides reduce to the same expression. Use `right_inv := fun q => by`. Proceed by induction on `q using Quotient.inductionOn' with`. Consider the case `h x`.

Simplify using `only [Quotient.map'_mk'', inv_mul_cancel_left, mul_inv_cancel_left]`. Use `rfl }`. Establish `hF : ∀ x y : H, DoubleCoset.mk B K x = DoubleCoset.mk B K y → S₂ x = S₂ y` using `fun x y hxy => by`. Take `⟨b, hb, k, hk, rfl⟩` from `(DoubleCoset.eq B K x y).1 hxy`. Conclude with `(hS₂ b hb k hk x).symm`.

Rewrite using `[← finsum_comp_equiv e]`. Use `finsum_congr fun q => ?_` and prove the remaining obligations. Rewrite using `[h12]`. Apply `hF` to reduce the goal to its premises. Rewrite using `[DoubleCoset.out_eq']`.

Use `conv_rhs => rw [← DoubleCoset.out_eq' A K q]`. Both sides reduce to the same expression.
-/
theorem finsum_dc_translate {H : Type} [Group H] (A B K : Subgroup H) (u : H)
    (hAB : B = A.map (MulAut.conj u).toMonoidHom) (S₁ S₂ : H → ℂ)
    (hS₂ : ∀ b ∈ B, ∀ k ∈ K, ∀ h, S₂ (b * h * k) = S₂ h) (h12 : ∀ h, S₁ h = S₂ (u * h)) :
    ∑ᶠ q : DoubleCoset.Quotient (A : Set H) (K : Set H), S₁ (Quotient.out q) =
      ∑ᶠ q : DoubleCoset.Quotient (B : Set H) (K : Set H), S₂ (Quotient.out q) := by
  have memB : ∀ a, a ∈ A → u * a * u⁻¹ ∈ B := fun a ha => by
    rw [hAB]; exact ⟨a, ha, by simp [MulAut.conj_apply]⟩
  have memA : ∀ b, b ∈ B → u⁻¹ * b * u ∈ A := fun b hb => by
    rw [hAB] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    simpa [MulAut.conj_apply, mul_assoc] using ha
  let e : DoubleCoset.Quotient (A : Set H) (K : Set H) ≃ DoubleCoset.Quotient (B : Set H) (K : Set H) :=
    { toFun := Quotient.map' (u * ·) (fun x y hxy => by
        obtain ⟨a, ha, k, hk, rfl⟩ := DoubleCoset.rel_iff.1 hxy
        exact DoubleCoset.rel_iff.2 ⟨u * a * u⁻¹, memB a ha, k, hk, by group⟩)
      invFun := Quotient.map' (u⁻¹ * ·) (fun x y hxy => by
        obtain ⟨b, hb, k, hk, rfl⟩ := DoubleCoset.rel_iff.1 hxy
        exact DoubleCoset.rel_iff.2 ⟨u⁻¹ * b * u, memA b hb, k, hk, by group⟩)
      left_inv := fun q => by
        induction q using Quotient.inductionOn' with
        | h x =>
          simp only [Quotient.map'_mk'', inv_mul_cancel_left, mul_inv_cancel_left]
          rfl
      right_inv := fun q => by
        induction q using Quotient.inductionOn' with
        | h x =>
          simp only [Quotient.map'_mk'', inv_mul_cancel_left, mul_inv_cancel_left]
          rfl }
  have hF : ∀ x y : H, DoubleCoset.mk B K x = DoubleCoset.mk B K y → S₂ x = S₂ y := fun x y hxy => by
    obtain ⟨b, hb, k, hk, rfl⟩ := (DoubleCoset.eq B K x y).1 hxy
    exact (hS₂ b hb k hk x).symm
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun q => ?_
  rw [h12]
  apply hF
  rw [DoubleCoset.out_eq']
  conv_rhs => rw [← DoubleCoset.out_eq' A K q]
  rfl

/- English proof (translation)
The claim follows from `Nat.card_congr { toFun := fun w => ⟨v⁻¹ * w * v, (h w).1 w.2⟩ invFun := fun w => ⟨v * w * v⁻¹, (h _).2 (by simpa [mul_assoc] using w.2)⟩ left_inv := fun w => by ext; simp [mul_assoc] right_inv := fun w => by ext; simp [mul_assoc] }`.
-/
theorem card_eq_of_conj {Γ : Type} [Group Γ] (S T : Subgroup Γ) (v : Γ) (h : ∀ w, w ∈ T ↔ v⁻¹ * w * v ∈ S) :
    Nat.card T = Nat.card S :=
  Nat.card_congr
    { toFun := fun w => ⟨v⁻¹ * w * v, (h w).1 w.2⟩
      invFun := fun w => ⟨v * w * v⁻¹, (h _).2 (by simpa [mul_assoc] using w.2)⟩
      left_inv := fun w => by ext; simp [mul_assoc]
      right_inv := fun w => by ext; simp [mul_assoc] }

end GlobalTheory.LKDef.TermPair

namespace GlobalTheory.LKDef.TermPair

/- English proof (translation)
Rewrite using `[Subgroup.mem_map_equiv]`. Simplify using `[MulAut.conj_symm_apply]`.
-/
theorem mem_map_conj {H : Type} [Group H] (K : Subgroup H) (a x : H) :
    x ∈ K.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ K := by
  rw [Subgroup.mem_map_equiv]; simp [MulAut.conj_symm_apply]

/- English proof (translation)
Establish `e : (a * h * k)⁻¹ * y * (a * h * k) = k⁻¹ * (h⁻¹ * (a⁻¹ * y * a) * h) * k` using `by group`. Rewrite using `[e, K.mul_mem_cancel_right hk, K.mul_mem_cancel_left (K.inv_mem hk)]`.
-/
theorem conj_mem_iff {H : Type} [Group H] (K : Subgroup H) (a h k y : H) (hk : k ∈ K) :
    (a * h * k)⁻¹ * y * (a * h * k) ∈ K ↔ h⁻¹ * (a⁻¹ * y * a) * h ∈ K := by
  have e : (a * h * k)⁻¹ * y * (a * h * k) = k⁻¹ * (h⁻¹ * (a⁻¹ * y * a) * h) * k := by group
  rw [e, K.mul_mem_cancel_right hk, K.mul_mem_cancel_left (K.inv_mem hk)]

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

/- English proof (translation)
Introduce `y hy` and use `⟨hy.2, DFormPos.sim_pos p G (DForm.ofDPair P) y.1 y.2 hy.2⟩`.
-/
theorem cent_le_grp (P : DPair G) : P.cent ≤ GlobalTheory.LKCx.grp G P.β := fun y hy =>
  ⟨hy.2, DFormPos.sim_pos p G (DForm.ofDPair P) y.1 y.2 hy.2⟩

/- English proof (translation)
Use extensionality with `v`. Rewrite using `[Subgroup.mem_centralizer_singleton_iff, MonoidHom.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h'` using `congrArg (fun w : GlobalTheory.LKCx.grp G P.β => (w : G.Cˣ × ℚˣ).1) h`.

Simplify using `only [Subgroup.coe_mul, Prod.fst_mul] at h'`. Conclude with `⟨⟨v, h', v.2.1⟩, rfl⟩`. Introduce and unpack `⟨w, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `Prod.ext w.2.1 (mul_comm _ _)`.
-/
theorem centralizer_eq (P : DPair G) (hm : (P.γ, P.c) ∈ GlobalTheory.LKCx.grp G P.β) :
    Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} =
      (Subgroup.inclusion (cent_le_grp P)).range := by
  ext v
  rw [Subgroup.mem_centralizer_singleton_iff, MonoidHom.mem_range]
  constructor
  · intro h
    have h' := congrArg (fun w : GlobalTheory.LKCx.grp G P.β => (w : G.Cˣ × ℚˣ).1) h
    simp only [Subgroup.coe_mul, Prod.fst_mul] at h'
    exact ⟨⟨v, h', v.2.1⟩, rfl⟩
  · rintro ⟨w, rfl⟩
    apply Subtype.ext
    exact Prod.ext w.2.1 (mul_comm _ _)

end GlobalTheory.LKDef.TermPair

namespace GlobalTheory.LKDef.TermPair
variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

/- English proof (translation)
Establish `hδ' : δ = z⁻¹ * inclG G 1 P.atP * z` using `by simpa [IsNrm, nrmG] using hδ`. Establish `hle` using `cent_le_grp P`. Establish `e1 : ∀ w, GlobalTheory.LKCx.toAfF G P.β x t hx (Subgroup.inclusion hle w) = P.toAf x t hx w` using `fun w => rfl`. Establish `e2 : ∀ w, P.toQr 1 z w = z⁻¹ * GlobalTheory.LKCx.toP1 G P.β (Subgroup.inclusion hle w) * z` using `fun w => by`. Simplify using `[DPair.toQr, GlobalTheory.LKCx.toP1, carry, MulAut.conj_apply]`.

Establish `eg : Subgroup.inclusion hle P.self = ⟨(P.γ, P.c), hm⟩` using `rfl`. Establish `hj2g : GlobalTheory.LKCx.toP1 G P.β ⟨(P.γ, P.c), hm⟩ = inclG G 1 P.atP` using `rfl`. Establish `hC` using `centralizer_eq P hm`. Unfold `DPair.termAt pointSum centSum`. Use `finsum_dc_translate ((P.toAf x t hx).prod (P.toQr 1 z)).range ((Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)}).map ((GlobalTheory.LKCx.toAfF G P.β x t hx).prod (GlobalTheory.LKCx.toP1 G P.β))) (Kf.prod K') ((1 : G.GAf), z) ?_ (fun h => ((Nat.card (stab ( …` and prove the remaining obligations.

Rewrite using `[hC, MonoidHom.map_range, MonoidHom.map_range]`. Use `congrArg MonoidHom.range (MonoidHom.ext fun w => ?_)` and prove the remaining obligations. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Simplify using `[MulAut.conj_apply, e1]`. Simplify using `[MulAut.conj_apply, e2] group`.

Introduce and unpack `b hb k hk h`. Take `⟨v, hv, rfl⟩` from `Subgroup.mem_map.1 hb`. Take `⟨hk1, hk2⟩` from `Subgroup.mem_prod.1 hk`. Establish `hvc : v * (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) = (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) * v` using `Subgroup.mem_centralizer_singleton_iff.1 hv`. Establish `hvg : v⁻¹ * (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) * v = (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)`.

Rewrite using `[mul_assoc, ← hvc, inv_mul_cancel_left]`. Establish `hcard : Nat.card (stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' (((GlobalTheory.LKCx.toAfF G P.β x t hx).prod (GlobalTheory.LKCx.toP1 G P.β)) v * h * k) ⊓ Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} : Subgroup _) = Na …`. Use `card_eq_of_conj _ _ v fun w => ?_` and prove the remaining obligations. Simplify using `only [stab, Subgroup.mem_inf, Subgroup.mem_comap, mem_map_conj, MonoidHom.prod_apply, Prod.fst_mul, Prod.snd_mul]`. Rewrite using `[conj_mem_iff _ _ _ _ _ hk1, conj_mem_iff _ _ _ _ _ hk2, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv]`.

Establish `hCv : w ∈ Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} ↔ v⁻¹ * w * v ∈ Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)}`. Rewrite using `[Subgroup.mul_mem_cancel_right _ hv, Subgroup.mul_mem_cancel_left _ (Subgroup.inv_mem _ hv)]`. Rewrite using `[hCv]`. Establish `ef : ∀ a y : G.GAf, f ((a * h.1 * k.1)⁻¹ * y * (a * h.1 * k.1)) = f (h.1⁻¹ * (a⁻¹ * y * a) * h.1)` using `fun a y => by`. Rewrite using `[← hf k.1 hk1 (h.1⁻¹ * (a⁻¹ * y * a) * h.1)]`.

Use `congr 1`. Use `group`. Establish `ef' : ∀ a y : Gr G 1, f' ((a * h.2 * k.2)⁻¹ * y * (a * h.2 * k.2)) = f' (h.2⁻¹ * (a⁻¹ * y * a) * h.2)` using `fun a y => by`. Rewrite using `[← hf' k.2 hk2 (h.2⁻¹ * (a⁻¹ * y * a) * h.2)]`. Use `congr 1`.

Use `group`. Establish `g1 : ((GlobalTheory.LKCx.toAfF G P.β x t hx) v)⁻¹ * (GlobalTheory.LKCx.toAfF G P.β x t hx) (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) * (GlobalTheory.LKCx.toAfF G P.β x t hx) v = (GlobalTheory.LKCx.toAfF G P.β x t hx) (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)`. Rewrite using `[← map_inv, ← map_mul, ← map_mul, hvg]`. Establish `g2 : ((GlobalTheory.LKCx.toP1 G P.β) v)⁻¹ * ((GlobalTheory.LKCx.toP1 G P.β) (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) * 1) * (GlobalTheory.LKCx.toP1 G P.β) v = (GlobalTheory.LKCx.toP1 G P.β) (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) * 1`. Rewrite using `[mul_one, ← map_inv, ← map_mul, ← map_mul, hvg]`.

Use `beta_reduce`. Rewrite using `[hcard]`. Simplify using `only [term, MonoidHom.prod_apply, Prod.fst_mul, Prod.snd_mul, MonoidHom.id_apply]`. Rewrite using `[ef, ef', g1, g2]`. Introduce `h`.

Establish `hmem : ∀ w, Subgroup.inclusion hle w ∈ stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' (((1 : G.GAf), z) * h) ↔ w ∈ stab (P.toAf x t hx) (P.toQr 1 z) Kf K' h` using `fun w => by`. Simplify using `only [stab, Subgroup.mem_inf, Subgroup.mem_comap, mem_map_conj, Prod.fst_mul, Prod.snd_mul, one_mul, e1, e2]`. Establish `e3 : (z * h.2)⁻¹ * (GlobalTheory.LKCx.toP1 G P.β) (Subgroup.inclusion hle w) * (z * h.2) = h.2⁻¹ * (z⁻¹ * (GlobalTheory.LKCx.toP1 G P.β) (Subgroup.inclusion hle w) * z) * h.2` using `by group`. Rewrite using `[e3]`. Establish `hsub : stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' (((1 : G.GAf), z) * h) ⊓ Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} = (stab (P.toAf x t hx) (P.toQr 1 z) Kf K' h).map (Subgroup.inclusion hle)`.

Rewrite using `[hC]`. Use extensionality with `v`. Simplify using `only [Subgroup.mem_inf, MonoidHom.mem_range, Subgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hv, w, rfl⟩`.

Conclude with `⟨w, (hmem w).1 hv, rfl⟩`. Introduce and unpack `⟨w, hw, rfl⟩`. Conclude with `⟨(hmem w).2 hw, w, rfl⟩`. Establish `hcard : Nat.card (stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' (((1 : G.GAf), z) * h) ⊓ Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} : Subgroup _) = Nat.card (stab (P.toAf x t hx) (P.toQr 1 z) Kf K' h)`. Rewrite using `[hsub]`.

Conclude with `Subgroup.card_map_of_injective (Subgroup.inclusion_injective hle)`. Use `beta_reduce`. Rewrite using `[hcard]`. Simplify using `only [term, Prod.fst_mul, Prod.snd_mul, MonoidHom.id_apply, one_mul, mul_one, GlobalTheory.LKCx.sigG_one]`. Rewrite using `[← e1 P.self, eg, hδ', ← hj2g]`.

Use `congr 3`. Use `group`.
-/
theorem termAt_eq (P : DPair G) (hm : (P.γ, P.c) ∈ GlobalTheory.LKCx.grp G P.β) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ)
    (hf : ∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ)
    (hf' : ∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (δ z : Gr G 1)
    (hδ : IsNrm G 1 P.atP δ z) :
    P.termAt Kf f 1 K' f' x t hx δ z =
      centSum (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) (MonoidHom.id (Gr G 1)) Kf K' 1 f f'
        ⟨(P.γ, P.c), hm⟩ := by
  have hδ' : δ = z⁻¹ * inclG G 1 P.atP * z := by simpa [IsNrm, nrmG] using hδ
  have hle := cent_le_grp P
  have e1 : ∀ w, GlobalTheory.LKCx.toAfF G P.β x t hx (Subgroup.inclusion hle w) = P.toAf x t hx w := fun w => rfl
  have e2 : ∀ w, P.toQr 1 z w = z⁻¹ * GlobalTheory.LKCx.toP1 G P.β (Subgroup.inclusion hle w) * z := fun w => by
    simp [DPair.toQr, GlobalTheory.LKCx.toP1, carry, MulAut.conj_apply]
  have eg : Subgroup.inclusion hle P.self = ⟨(P.γ, P.c), hm⟩ := rfl
  have hj2g : GlobalTheory.LKCx.toP1 G P.β ⟨(P.γ, P.c), hm⟩ = inclG G 1 P.atP := rfl
  have hC := centralizer_eq P hm
  unfold DPair.termAt pointSum centSum
  refine finsum_dc_translate ((P.toAf x t hx).prod (P.toQr 1 z)).range
    ((Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)}).map
      ((GlobalTheory.LKCx.toAfF G P.β x t hx).prod (GlobalTheory.LKCx.toP1 G P.β))) (Kf.prod K') ((1 : G.GAf), z) ?_
    (fun h => ((Nat.card (stab (P.toAf x t hx) (P.toQr 1 z) Kf K' h) : ℕ) : ℂ)⁻¹ *
      (f (h.1⁻¹ * (P.toAf x t hx) P.self * h.1) * f' (h.2⁻¹ * δ * (sigG G 1) h.2)))
    (fun h => ((Nat.card (stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' h ⊓
      Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} : Subgroup _) : ℕ) : ℂ)⁻¹ *
      term (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) (MonoidHom.id (Gr G 1)) 1 f f' h
        ⟨(P.γ, P.c), hm⟩) ?_ ?_
  · rw [hC, MonoidHom.map_range, MonoidHom.map_range]
    refine congrArg MonoidHom.range (MonoidHom.ext fun w => ?_)
    refine Prod.ext ?_ ?_
    · simp [MulAut.conj_apply, e1]
    · simp [MulAut.conj_apply, e2]
      group
  · rintro b hb k hk h
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hb
    obtain ⟨hk1, hk2⟩ := Subgroup.mem_prod.1 hk
    have hvc : v * (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) = (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) * v := Subgroup.mem_centralizer_singleton_iff.1 hv
    have hvg : v⁻¹ * (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) * v = (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) := by
      rw [mul_assoc, ← hvc, inv_mul_cancel_left]
    have hcard : Nat.card (stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' (((GlobalTheory.LKCx.toAfF G P.β x t hx).prod (GlobalTheory.LKCx.toP1 G P.β)) v * h * k) ⊓
        Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} : Subgroup _) =
        Nat.card (stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' h ⊓ Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} : Subgroup _) := by
      refine card_eq_of_conj _ _ v fun w => ?_
      simp only [stab, Subgroup.mem_inf, Subgroup.mem_comap, mem_map_conj, MonoidHom.prod_apply, Prod.fst_mul,
        Prod.snd_mul]
      rw [conj_mem_iff _ _ _ _ _ hk1, conj_mem_iff _ _ _ _ _ hk2, map_mul, map_mul, map_mul, map_mul, map_inv,
        map_inv]
      have hCv : w ∈ Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} ↔ v⁻¹ * w * v ∈ Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} := by
        rw [Subgroup.mul_mem_cancel_right _ hv, Subgroup.mul_mem_cancel_left _ (Subgroup.inv_mem _ hv)]
      rw [hCv]
    have ef : ∀ a y : G.GAf, f ((a * h.1 * k.1)⁻¹ * y * (a * h.1 * k.1)) = f (h.1⁻¹ * (a⁻¹ * y * a) * h.1) :=
      fun a y => by
        rw [← hf k.1 hk1 (h.1⁻¹ * (a⁻¹ * y * a) * h.1)]; congr 1; group
    have ef' : ∀ a y : Gr G 1, f' ((a * h.2 * k.2)⁻¹ * y * (a * h.2 * k.2)) =
        f' (h.2⁻¹ * (a⁻¹ * y * a) * h.2) := fun a y => by
      rw [← hf' k.2 hk2 (h.2⁻¹ * (a⁻¹ * y * a) * h.2)]; congr 1; group
    have g1 : ((GlobalTheory.LKCx.toAfF G P.β x t hx) v)⁻¹ * (GlobalTheory.LKCx.toAfF G P.β x t hx) (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) * (GlobalTheory.LKCx.toAfF G P.β x t hx) v = (GlobalTheory.LKCx.toAfF G P.β x t hx) (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) := by
      rw [← map_inv, ← map_mul, ← map_mul, hvg]
    have g2 : ((GlobalTheory.LKCx.toP1 G P.β) v)⁻¹ * ((GlobalTheory.LKCx.toP1 G P.β) (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) * 1) * (GlobalTheory.LKCx.toP1 G P.β) v = (GlobalTheory.LKCx.toP1 G P.β) (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) * 1 := by
      rw [mul_one, ← map_inv, ← map_mul, ← map_mul, hvg]
    beta_reduce
    rw [hcard]
    simp only [term, MonoidHom.prod_apply, Prod.fst_mul, Prod.snd_mul, MonoidHom.id_apply]
    rw [ef, ef', g1, g2]
  · intro h
    have hmem : ∀ w, Subgroup.inclusion hle w ∈ stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' (((1 : G.GAf), z) * h) ↔
        w ∈ stab (P.toAf x t hx) (P.toQr 1 z) Kf K' h := fun w => by
      simp only [stab, Subgroup.mem_inf, Subgroup.mem_comap, mem_map_conj, Prod.fst_mul, Prod.snd_mul, one_mul, e1, e2]
      have e3 : (z * h.2)⁻¹ * (GlobalTheory.LKCx.toP1 G P.β) (Subgroup.inclusion hle w) * (z * h.2) =
          h.2⁻¹ * (z⁻¹ * (GlobalTheory.LKCx.toP1 G P.β) (Subgroup.inclusion hle w) * z) * h.2 := by group
      rw [e3]
    have hsub : stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' (((1 : G.GAf), z) * h) ⊓ Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} =
        (stab (P.toAf x t hx) (P.toQr 1 z) Kf K' h).map (Subgroup.inclusion hle) := by
      rw [hC]
      ext v
      simp only [Subgroup.mem_inf, MonoidHom.mem_range, Subgroup.mem_map]
      constructor
      · rintro ⟨hv, w, rfl⟩
        exact ⟨w, (hmem w).1 hv, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨(hmem w).2 hw, w, rfl⟩
    have hcard : Nat.card (stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' (((1 : G.GAf), z) * h) ⊓ Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} :
        Subgroup _) = Nat.card (stab (P.toAf x t hx) (P.toQr 1 z) Kf K' h) := by
      rw [hsub]; exact Subgroup.card_map_of_injective (Subgroup.inclusion_injective hle)
    beta_reduce
    rw [hcard]
    simp only [term, Prod.fst_mul, Prod.snd_mul, MonoidHom.id_apply, one_mul, mul_one, GlobalTheory.LKCx.sigG_one]
    rw [← e1 P.self, eg, hδ', ← hj2g]
    congr 3
    group

end GlobalTheory.LKDef.TermPair

namespace GlobalTheory.LKDef.TermPair

/- English proof (translation)
Introduce `p _ G P hm L f hf K' f' hf'`. Establish `hex : ∃ dz : Gr G 1 × Gr G 1, IsNrm G 1 P.atP dz.1 dz.2` using `⟨(inclG G 1 P.atP, 1), by simp [IsNrm, nrmG]⟩`. Unfold `DPair.term`. Rewrite using `[dif_pos hex]`. Conclude with `termAt_eq P hm _ f (fun k hk g => by simpa using hf.2.2.1 k hk g) K' f' (fun k hk g => by simpa [GlobalTheory.LKCx.sigG_one] using hf'.2.2.1 k hk g) _ _ _ _ _ hex.choose_spec`.
-/
theorem term_eq_centSum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : GlobalTheory.LKDef.DPair G) (hm : (P.γ, P.c) ∈ GlobalTheory.LKCx.grp G P.β)
    (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      P.term L.K.toSubgroup f 1 K' f' =
        centSum (GlobalTheory.LKCx.toAfF G P.β P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec)
          (GlobalTheory.LKCx.toP1 G P.β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' ⟨(P.γ, P.c), hm⟩ := by
  intro p _ G P hm L f hf K' f' hf'
  have hex : ∃ dz : Gr G 1 × Gr G 1, IsNrm G 1 P.atP dz.1 dz.2 :=
    ⟨(inclG G 1 P.atP, 1), by simp [IsNrm, nrmG]⟩
  unfold DPair.term
  rw [dif_pos hex]
  exact termAt_eq P hm _ f (fun k hk g => by simpa using hf.2.2.1 k hk g) K' f'
    (fun k hk g => by simpa [GlobalTheory.LKCx.sigG_one] using hf'.2.2.1 k hk g) _ _ _ _ _ hex.choose_spec

end GlobalTheory.LKDef.TermPair
