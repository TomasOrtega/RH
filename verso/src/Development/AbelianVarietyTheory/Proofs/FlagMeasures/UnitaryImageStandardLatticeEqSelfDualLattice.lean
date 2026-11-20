import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportInnerLattices
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

noncomputable section

namespace GlobalTheory.StdLatImg

open GlobalTheory.HL.CoordInnerSnd

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

def gen (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)) : Set V :=
  {v | (∀ a, H.h v (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h v (Fr.e a) ∈ M.L.O) ∧
    ∃ w : ↥(H.perp (H.X Fr.f)), (w : V) = Fr.prF v ∧ H.mkW Fr.f w ∈ L}

/- English proof (translation)
The claim follows from `GlobalTheory.UnramOrder.cj_mem M.L hx`.
-/
lemma cj_mem' {x : E} (hx : x ∈ M.L.O) : M.L.cj x ∈ M.L.O := GlobalTheory.UnramOrder.cj_mem M.L hx

/- English proof (translation)
The claim follows from `Λ.smul_mem (⟨c, hc⟩ : M.L.O) hw`.
-/
lemma smul_mem_lat (Λ : Submodule M.L.O V) {c : E} (hc : c ∈ M.L.O) {w : V} (hw : w ∈ Λ) :
    c • w ∈ Λ := Λ.smul_mem (⟨c, hc⟩ : M.L.O) hw

/- English proof (translation)
Rewrite using `[← hl_apply, ← hl_apply]`. Simplify using `only [FrameD.prF, map_sub, map_sum, map_smul, hl_apply, h_swap_zero (h1 _), h_swap_zero (h2 _)]`. Simplify using the standard rewrite rules.
-/
lemma h_prF_left (Fr : FrameD H r) (p s : V) (h1 : ∀ a, H.h p (Fr.e a) = 0)
    (h2 : ∀ a, H.h p (Fr.es a) = 0) : H.h (Fr.prF s) p = H.h s p := by
  rw [← hl_apply, ← hl_apply]
  simp only [FrameD.prF, map_sub, map_sum, map_smul, hl_apply, h_swap_zero (h1 _),
    h_swap_zero (h2 _)]
  simp

/- English proof (translation)
Rewrite using `[← hl_apply, ← hl_apply]`. Simplify using `only [FrameD.prF, map_sub, map_sum, map_smul, hl_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma decomp (Fr : FrameD H r) (v s : V) : H.h v s = H.h (Fr.prF v) s +
    ∑ a, H.h v (Fr.es a) * H.h (Fr.e a) s + ∑ a, H.h v (Fr.e a) * H.h (Fr.es a) s := by
  rw [← hl_apply, ← hl_apply]
  simp only [FrameD.prF, map_sub, map_sum, map_smul, hl_apply, smul_eq_mul]
  ring

end GlobalTheory.StdLatImg

namespace GlobalTheory.StdLatImg

open GlobalTheory.HL.CoordInnerSnd

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

/- English proof (translation)
Rewrite using `[← SetLike.mem_coe, hL]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, he⟩`. Conclude with `⟨x, hx, (mkW_eq Fr x w).1 he⟩`. Introduce and unpack `⟨x, hx, he⟩`.

Conclude with `⟨x, hx, (mkW_eq Fr x w).2 he⟩`.
-/
lemma memL_iff (Fr : FrameD H r) (Λ : Submodule M.L.O V) (L : Submodule M.L.O (H.Wb Fr.f))
    (hL : (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f) (w : ↥(H.perp (H.X Fr.f))) :
    H.mkW Fr.f w ∈ L ↔ ∃ x : ↥(H.perp (H.X Fr.f)), (x : V) ∈ Λ ∧ (x : V) - w ∈ H.X Fr.f := by
  rw [← SetLike.mem_coe, hL]
  constructor
  · rintro ⟨x, hx, he⟩; exact ⟨x, hx, (mkW_eq Fr x w).1 he⟩
  · rintro ⟨x, hx, he⟩; exact ⟨x, hx, (mkW_eq Fr x w).2 he⟩

/- English proof (translation)
Use `set v := n.symm u with hv`. Establish `hnv : n v = u` using `by simp [hv]`. Establish `hve : ∀ a, H.h v (Fr.e a) = H.h u (Fr.e a)` using `fun a => by`. Rewrite using `[← hn v (Fr.e a), hnv]`. Conclude with `congrArg _ (hfix a)`.

Establish `hveO : ∀ a, H.h v (Fr.e a) ∈ M.L.O` using `fun a => by`. Rewrite using `[hve]`. Conclude with `(hSD.2.2 u).1 hu _ (he a)`. Establish `hvesO : ∀ a, H.h v (Fr.es a) ∈ M.L.O` using `fun a => by`. Rewrite using `[← hn v (Fr.es a), hnv]`.

Conclude with `(hSD.2.2 u).1 hu _ (hes a)`. Use `⟨hvesO, hveO, ⟨Fr.prF v, prF_perp Fr v⟩, rfl, ?_⟩` and prove the remaining obligations. Use `set v' := v - ∑ a, H.h v (Fr.e a) • Fr.es a with hv'`. Establish `hv'p : v' ∈ H.perp (H.X Fr.f)`. Rewrite using `[mem_perpX]`.

Introduce `b`. Rewrite using `[← hl_apply]`. Simplify using `only [hv', map_sub, map_sum, map_smul, hl_apply, h_es_e, smul_eq_mul]`. Simplify using the standard rewrite rules. Establish `hx : n v' = u - ∑ a, H.h v (Fr.e a) • n (Fr.es a)`.

Simplify using `[hv', map_sub, map_sum, hnv]`. Establish `hxΛ : n v' ∈ Λ`. Rewrite using `[hx]`. Conclude with `Λ.sub_mem hu (Λ.sum_mem fun a _ => smul_mem_lat Λ (hveO a) (hes a))`. Establish `hxv'` using `hX v' hv'p`.

Establish `hxp : n v' ∈ H.perp (H.X Fr.f)`. Use `(H.perp (H.X Fr.f)).add_mem hv'p (X_le_perp Fr hxv')` as an intermediate fact. Simplify using `using this`. Rewrite using `[memL_iff Fr Λ L hL]`. Use `⟨⟨n v', hxp⟩, hxΛ, ?_⟩` and prove the remaining obligations.

Establish `hpr : Fr.prF v - v' = -∑ a, H.h v (Fr.es a) • Fr.e a`. Simplify using `only [FrameD.prF, hv']`. Normalize the expressions using the abelian group laws. Establish `: (n v' : V) - Fr.prF v = (n v' - v') - (Fr.prF v - v')` using `by abel`. Use `show n v' - Fr.prF v ∈ H.X Fr.f`.

Rewrite using `[this, hpr]`. Conclude with `(H.X Fr.f).sub_mem hxv' ((H.X Fr.f).neg_mem ((H.X Fr.f).sum_mem fun a _ => (H.X Fr.f).smul_mem _ (e_mem_X Fr a)))`.
-/
lemma symm_mem_gen (Fr : FrameD H r) (Λ : Submodule M.L.O V) (hSD : H.IsSelfDual Λ)
    (he : ∀ a : Fin r, Fr.f a.castSucc ∈ Λ) (L : Submodule M.L.O (H.Wb Fr.f))
    (hL : (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f) (n : V ≃ₗ[E] V) (hn : IsUnitary H n)
    (hfix : ∀ a : Fin r, n (Fr.f a.castSucc) = Fr.f a.castSucc) (hes : ∀ a, n (Fr.es a) ∈ Λ)
    (hX : ∀ v ∈ H.perp (H.X Fr.f), n v - v ∈ H.X Fr.f) {u : V} (hu : u ∈ Λ) :
    n.symm u ∈ gen Fr L := by
  set v := n.symm u with hv
  have hnv : n v = u := by simp [hv]
  have hve : ∀ a, H.h v (Fr.e a) = H.h u (Fr.e a) := fun a => by
    rw [← hn v (Fr.e a), hnv]; exact congrArg _ (hfix a)
  have hveO : ∀ a, H.h v (Fr.e a) ∈ M.L.O := fun a => by
    rw [hve]; exact (hSD.2.2 u).1 hu _ (he a)
  have hvesO : ∀ a, H.h v (Fr.es a) ∈ M.L.O := fun a => by
    rw [← hn v (Fr.es a), hnv]; exact (hSD.2.2 u).1 hu _ (hes a)
  refine ⟨hvesO, hveO, ⟨Fr.prF v, prF_perp Fr v⟩, rfl, ?_⟩
  set v' := v - ∑ a, H.h v (Fr.e a) • Fr.es a with hv'
  have hv'p : v' ∈ H.perp (H.X Fr.f) := by
    rw [mem_perpX]
    intro b
    rw [← hl_apply]
    simp only [hv', map_sub, map_sum, map_smul, hl_apply, h_es_e, smul_eq_mul]
    simp
  have hx : n v' = u - ∑ a, H.h v (Fr.e a) • n (Fr.es a) := by
    simp [hv', map_sub, map_sum, hnv]
  have hxΛ : n v' ∈ Λ := by
    rw [hx]
    exact Λ.sub_mem hu (Λ.sum_mem fun a _ => smul_mem_lat Λ (hveO a) (hes a))
  have hxv' := hX v' hv'p
  have hxp : n v' ∈ H.perp (H.X Fr.f) := by
    have := (H.perp (H.X Fr.f)).add_mem hv'p (X_le_perp Fr hxv')
    simpa using this
  rw [memL_iff Fr Λ L hL]
  refine ⟨⟨n v', hxp⟩, hxΛ, ?_⟩
  have hpr : Fr.prF v - v' = -∑ a, H.h v (Fr.es a) • Fr.e a := by
    simp only [FrameD.prF, hv']; abel
  have : (n v' : V) - Fr.prF v = (n v' - v') - (Fr.prF v - v') := by abel
  show n v' - Fr.prF v ∈ H.X Fr.f
  rw [this, hpr]
  exact (H.X Fr.f).sub_mem hxv' ((H.X Fr.f).neg_mem
    ((H.X Fr.f).sum_mem fun a _ => (H.X Fr.f).smul_mem _ (e_mem_X Fr a)))

end GlobalTheory.StdLatImg

namespace GlobalTheory.StdLatImg

open GlobalTheory.HL.CoordInnerSnd

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

/- English proof (translation)
Take `⟨hv1, hv2, wv, hwv, hwvL⟩` from `hv`. Take `⟨hs1, hs2, ws, hws, hwsL⟩` from `hs`. Take `⟨x, hxΛ, hxd⟩` from `(memL_iff Fr Λ L hL wv).1 hwvL`. Take `⟨x', hx'Λ, hx'd⟩` from `(memL_iff Fr Λ L hL ws).1 hwsL`. Rewrite `hxd` using `[hwv]`.

Rewrite `hx'd` using `[hws]`. Establish `hpp : H.h (Fr.prF v) (Fr.prF s) = H.h (x : V) (x' : V)`. Establish `e1 : Fr.prF v = x - ((x : V) - Fr.prF v)` using `by abel`. Establish `e2 : Fr.prF s = x' - ((x' : V) - Fr.prF s)` using `by abel`. Establish `k1 : H.h ((x : V) - Fr.prF v) (Fr.prF s) = 0` using `h_swap_zero (prF_perp Fr s _ hxd)`.

Establish `k2 : H.h (x : V) ((x' : V) - Fr.prF s) = 0` using `x.2 _ hx'd`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hl_apply, ← hl_apply, ← hl_apply, ← map_sub, ← e1]`. Use `_ = H.h (x : V) (Fr.prF s) := by rw [k1, sub_zero]`. Use `_ = H.h (x : V) (x' : V) := by`.

Rewrite using `[e2, ← neg_add_eq_sub, h_add_right, ← neg_one_smul E ((x' : V) - Fr.prF s), h_smul_right, k2, mul_zero, zero_add]`. Establish `hpO : H.h (Fr.prF v) s ∈ M.L.O`. Establish `e3 : H.h (Fr.prF v) s = M.L.cj (H.h s (Fr.prF v))` using `H.h_herm _ _`. Rewrite using `[e3, ← h_prF_left Fr (Fr.prF v) s (h_prF_e Fr v) (h_prF_es Fr v), H.h_herm, M.L.cj_cj, hpp]`. Conclude with `(hSD.2.2 x).1 hxΛ _ hx'Λ`.

Rewrite using `[decomp Fr v s]`. Use `M.L.O.add_mem (M.L.O.add_mem hpO ?_) ?_` and prove the remaining obligations. Use `M.L.O.sum_mem fun a _ => M.L.O.mul_mem (hv1 a) ?_` and prove the remaining obligations. Rewrite using `[H.h_herm]`. Conclude with `cj_mem' (hs2 a)`.

Use `M.L.O.sum_mem fun a _ => M.L.O.mul_mem (hv2 a) ?_` and prove the remaining obligations. Rewrite using `[H.h_herm]`. Conclude with `cj_mem' (hs1 a)`.
-/
lemma h_gen_mem (Fr : FrameD H r) (Λ : Submodule M.L.O V) (hSD : H.IsSelfDual Λ)
    (L : Submodule M.L.O (H.Wb Fr.f)) (hL : (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f)
    {v s : V} (hv : v ∈ gen Fr L) (hs : s ∈ gen Fr L) : H.h v s ∈ M.L.O := by
  obtain ⟨hv1, hv2, wv, hwv, hwvL⟩ := hv
  obtain ⟨hs1, hs2, ws, hws, hwsL⟩ := hs
  obtain ⟨x, hxΛ, hxd⟩ := (memL_iff Fr Λ L hL wv).1 hwvL
  obtain ⟨x', hx'Λ, hx'd⟩ := (memL_iff Fr Λ L hL ws).1 hwsL
  rw [hwv] at hxd
  rw [hws] at hx'd

  have hpp : H.h (Fr.prF v) (Fr.prF s) = H.h (x : V) (x' : V) := by
    have e1 : Fr.prF v = x - ((x : V) - Fr.prF v) := by abel
    have e2 : Fr.prF s = x' - ((x' : V) - Fr.prF s) := by abel
    have k1 : H.h ((x : V) - Fr.prF v) (Fr.prF s) = 0 :=
      h_swap_zero (prF_perp Fr s _ hxd)
    have k2 : H.h (x : V) ((x' : V) - Fr.prF s) = 0 := x.2 _ hx'd
    calc H.h (Fr.prF v) (Fr.prF s)
        = H.h (x : V) (Fr.prF s) - H.h ((x : V) - Fr.prF v) (Fr.prF s) := by
          rw [← hl_apply, ← hl_apply, ← hl_apply, ← map_sub, ← e1]
      _ = H.h (x : V) (Fr.prF s) := by rw [k1, sub_zero]
      _ = H.h (x : V) (x' : V) := by
          rw [e2, ← neg_add_eq_sub, h_add_right, ← neg_one_smul E ((x' : V) - Fr.prF s),
            h_smul_right, k2, mul_zero, zero_add]
  have hpO : H.h (Fr.prF v) s ∈ M.L.O := by
    have e3 : H.h (Fr.prF v) s = M.L.cj (H.h s (Fr.prF v)) := H.h_herm _ _
    rw [e3, ← h_prF_left Fr (Fr.prF v) s (h_prF_e Fr v) (h_prF_es Fr v), H.h_herm, M.L.cj_cj, hpp]
    exact (hSD.2.2 x).1 hxΛ _ hx'Λ
  rw [decomp Fr v s]
  refine M.L.O.add_mem (M.L.O.add_mem hpO ?_) ?_
  · refine M.L.O.sum_mem fun a _ => M.L.O.mul_mem (hv1 a) ?_
    rw [H.h_herm]; exact cj_mem' (hs2 a)
  · refine M.L.O.sum_mem fun a _ => M.L.O.mul_mem (hv2 a) ?_
    rw [H.h_herm]; exact cj_mem' (hs1 a)

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M V _ _ H r Fr Λ hSD he L hL n hn hfix hes hX`. Establish `hb` using `fun {u : V} (hu : u ∈ Λ) => symm_mem_gen Fr Λ hSD he L hL n hn hfix hes hX hu`. Establish `hgen : FrameD.LamStd Fr L = Submodule.span M.L.O (gen Fr L)` using `rfl`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `u hu`.

Rewrite using `[hgen]`. Conclude with `⟨n.symm u, Submodule.subset_span (hb hu), by simp⟩`. Rewrite using `[hgen, img, Submodule.map_le_iff_le_comap, Submodule.span_le]`. Introduce `s hs`. Use `show n s ∈ Λ`.

Use `(hSD.2.2 (n s)).2 fun t ht => ?_` and prove the remaining obligations. Establish `ht' : n (n.symm t) = t` using `by simp`. Rewrite using `[← ht', hn]`. Conclude with `h_gen_mem Fr Λ hSD L hL hs (hb ht)`.
-/
theorem eq_img_lamStd : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → (∀ a : Fin r, Fr.f a.castSucc ∈ Λ) → ∀ L : Submodule M.L.O (H.Wb Fr.f), (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f → ∀ n : V ≃ₗ[E] V, IsUnitary H n → (∀ a : Fin r, n (Fr.f a.castSucc) = Fr.f a.castSucc) → (∀ a, n (Fr.es a) ∈ Λ) → (∀ v ∈ H.perp (H.X Fr.f), n v - v ∈ H.X Fr.f) → Λ = img n (Fr.LamStd L) := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r Fr Λ hSD he L hL n hn hfix hes hX
  have hb := fun {u : V} (hu : u ∈ Λ) => symm_mem_gen Fr Λ hSD he L hL n hn hfix hes hX hu
  have hgen : FrameD.LamStd Fr L = Submodule.span M.L.O (gen Fr L) := rfl
  apply le_antisymm
  · intro u hu
    rw [hgen]
    exact ⟨n.symm u, Submodule.subset_span (hb hu), by simp⟩
  · rw [hgen, img, Submodule.map_le_iff_le_comap, Submodule.span_le]
    intro s hs
    show n s ∈ Λ
    refine (hSD.2.2 (n s)).2 fun t ht => ?_
    have ht' : n (n.symm t) = t := by simp
    rw [← ht', hn]
    exact h_gen_mem Fr Λ hSD L hL hs (hb ht)

end GlobalTheory.StdLatImg
