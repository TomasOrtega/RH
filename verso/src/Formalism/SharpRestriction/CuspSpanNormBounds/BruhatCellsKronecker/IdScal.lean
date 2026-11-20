import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.UnitriangularFrameLift

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.MainNotions.S Formalism.BasicNotions Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals Module

section Scal

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

/- English proof (translation)
Unfold `FlagG.Xa at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i, hi, rfl⟩` from `hx`. Establish `hi' : i.val < a.val + 1` using `hi`.

Distinguish the cases in `h : i = a`. Substitute `h; exact ⟨1, by simp⟩` using the available equality. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[zero_smul, sub_zero]`. Conclude with `geo_e_mem_Xa F i _ (by have : i.val ≠ a.val := fun h' => h (Fin.ext h'); omega)`.

Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨c, hc⟩` from `hx`. Take `⟨d, hd⟩` from `hy`. Use `⟨c + d, ?_⟩` and prove the remaining obligations.

Establish `: x + y - (c + d) • F.e a = (x - c • F.e a) + (y - d • F.e a)` using `by rw [add_smul]; abel`. Rewrite using `[this]`. Conclude with `Submodule.add_mem _ hc hd`. Consider the case `smul k x _ hx`. Take `⟨c, hc⟩` from `hx`.

Use `⟨k * c, ?_⟩` and prove the remaining obligations. Establish `: k • x - (k * c) • F.e a = k • (x - c • F.e a)` using `by rw [smul_sub, mul_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hc`.
-/
theorem scal_Xa_succ (F : FlagG S r T) (a : Fin r) (x : S.V) (hx : x ∈ F.Xa (a.val + 1)) :
    ∃ c : E, x - c • F.e a ∈ F.Xa a.val := by
  unfold FlagG.Xa at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    have hi' : i.val < a.val + 1 := hi
    by_cases h : i = a
    · subst h; exact ⟨1, by simp⟩
    · refine ⟨0, ?_⟩
      rw [zero_smul, sub_zero]
      exact geo_e_mem_Xa F i _ (by have : i.val ≠ a.val := fun h' => h (Fin.ext h'); omega)
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    refine ⟨c + d, ?_⟩
    have : x + y - (c + d) • F.e a = (x - c • F.e a) + (y - d • F.e a) := by rw [add_smul]; abel
    rw [this]
    exact Submodule.add_mem _ hc hd
  | smul k x _ hx =>
    obtain ⟨c, hc⟩ := hx
    refine ⟨k * c, ?_⟩
    have : k • x - (k * c) • F.e a = k • (x - c • F.e a) := by rw [smul_sub, mul_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hc

/- English proof (translation)
Introduce `h`. Establish `h1` using `geo_coefX F a 1 0 (Submodule.zero_mem _)`. Establish `h2` using `geo_coefX F a 0 (F.e a) h`. Rewrite `h1` using `[one_smul, add_zero]`. Rewrite `h2` using `[zero_smul, zero_add]`.

Rewrite `h2` using `[h1]`. Conclude with `one_ne_zero h2`.
-/
theorem scal_e_notMem (F : FlagG S r T) (a : Fin r) : F.e a ∉ F.Xa a.val := by
  intro h
  have h1 := geo_coefX F a 1 0 (Submodule.zero_mem _)
  have h2 := geo_coefX F a 0 (F.e a) h
  rw [one_smul, add_zero] at h1
  rw [zero_smul, zero_add] at h2
  rw [h1] at h2
  exact one_ne_zero h2

/- English proof (translation)
Introduce `a b`. Use `show S.hT (brS S a v • x - brS S a x • v) b + S.hT a (brS S b v • x - brS S b x • v) = 0`. Simplify using `only [brS, map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, S.herm.eq, RingHom.id_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem scal_xv_skew (x v : S.V) : xv S x v ∈ LieU S := by
  intro a b
  show S.hT (brS S a v • x - brS S a x • v) b + S.hT a (brS S b v • x - brS S b x • v) = 0
  simp only [brS, map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, S.herm.eq, RingHom.id_apply]
  ring

/- English proof (translation)
Use `show brS S y v • e - brS S y e • v = _`. Unfold `brS`. Rewrite using `[hy, zero_smul, sub_zero]`.
-/
theorem scal_xv_val (e v y : S.V) (hy : S.hT e y = 0) : xv S e v y = S.hT v y • e := by
  show brS S y v • e - brS S y e • v = _
  unfold brS
  rw [hy, zero_smul, sub_zero]

/- English proof (translation)
Establish `heX : F.e i ∈ F.X` using `Submodule.subset_span ⟨i, rfl⟩`. Use `⟨scal_xv_skew _ _, ?_, ?_⟩` and prove the remaining obligations. Introduce `a ha1 har x hx`. Rewrite using `[scal_xv_val _ _ x (geo_X_X F _ _ heX (geo_Xa_le_X F _ hx))]`. Distinguish the cases in `h : a ≤ i.val + 1`.

Rewrite using `[hv x (geo_Xa_mono F h hx), zero_smul]`. Conclude with `Submodule.zero_mem _`. Conclude with `Submodule.smul_mem _ _ (geo_e_mem_Xa F i _ (by omega))`. Introduce `x hx`. Rewrite using `[scal_xv_val _ _ x (hx _ heX)]`.

Conclude with `Submodule.smul_mem _ _ heX`.
-/
theorem scal_mem_LieN (F : FlagG S r T) (i : Fin r) (v : S.V) (hv : ∀ x ∈ F.Xa (i.val + 1), S.hT v x = 0) :
    xv S (F.e i) v ∈ F.LieN := by
  have heX : F.e i ∈ F.X := Submodule.subset_span ⟨i, rfl⟩
  refine ⟨scal_xv_skew _ _, ?_, ?_⟩
  · intro a ha1 har x hx
    rw [scal_xv_val _ _ x (geo_X_X F _ _ heX (geo_Xa_le_X F _ hx))]
    by_cases h : a ≤ i.val + 1
    · rw [hv x (geo_Xa_mono F h hx), zero_smul]; exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (geo_e_mem_Xa F i _ (by omega))
  · intro x hx
    rw [scal_xv_val _ _ x (hx _ heX)]
    exact Submodule.smul_mem _ _ heX

/- English proof (translation)
Unfold `FlagG.ell`. Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[hY, hu, smul_add, smul_smul]`. Conclude with `geo_coefX G i _ _ (Submodule.smul_mem _ _ hw)`. Introduce `k _ hk`.

Rewrite using `[hY]`. Break down `lt_or_gt_of_ne (fun h => hk (Fin.ext h) : k.val ≠ i.val) with h | h` into its components or cases. Rewrite using `[hγ k.succ (by rw [Fin.val_succ]; omega), zero_smul]`. Use `geo_coefX G k 0 0 (Submodule.zero_mem _)` as an intermediate fact. Simplify using `using this`.

Establish `hm : γ k.succ • u ∈ G.Xa k.val`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Rewrite using `[hu]`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ _ (geo_e_mem_Xa G i _ h)) (geo_Xa_mono G (le_of_lt h) hw)`. Use `geo_coefX G k 0 _ hm` as an intermediate fact.

Rewrite `this` using `[zero_smul, zero_add]`. Then use the resulting hypothesis. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem scal_ell (G : FlagG S r T) (Y : S.V →ₗ[E] S.V) (i : Fin r) (u : S.V) (d : E) (w : S.V)
    (hw : w ∈ G.Xa i.val) (hu : u = d • G.e i + w) (γ : Fin (r + 1) → E) (hY : ∀ p, Y (G.fvec p) = γ p • u)
    (hγ : ∀ p : Fin (r + 1), p.val ≤ i.val → γ p = 0) : G.ell Y = γ i.succ * d := by
  unfold FlagG.ell
  rw [Finset.sum_eq_single i]
  · rw [hY, hu, smul_add, smul_smul]
    exact geo_coefX G i _ _ (Submodule.smul_mem _ _ hw)
  · intro k _ hk
    rw [hY]
    rcases lt_or_gt_of_ne (fun h => hk (Fin.ext h) : k.val ≠ i.val) with h | h
    · rw [hγ k.succ (by rw [Fin.val_succ]; omega), zero_smul]
      have := geo_coefX G k 0 0 (Submodule.zero_mem _)
      simpa using this
    · have hm : γ k.succ • u ∈ G.Xa k.val := by
        refine Submodule.smul_mem _ _ ?_
        rw [hu]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (geo_e_mem_Xa G i _ h)) (geo_Xa_mono G (le_of_lt h) hw)
      have := geo_coefX G k 0 _ hm
      rwa [zero_smul, zero_add] at this
  · intro h; exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hle : orth S U ≤ orth S (U ⊔ Submodule.span E {f})`. Introduce `v hv`. Rewrite `hv`, the goal using `[p_mem_orth]`.

Establish `hvf` using `hcon v (fun x hx => p_symm_zero S (hv x hx))`. Introduce `x hx`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hx`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hb`. Rewrite using `[map_add, LinearMap.add_apply, hv a ha, map_smulₛₗ, LinearMap.smul_apply, p_symm_zero S hvf, smul_zero, add_zero]`.

Establish `h1` using `Submodule.finrank_mono hle`. Establish `h2` using `c_finrank_orth_ge U`. Establish `h3` using `c_finrank_orth_le (U ⊔ Submodule.span E {f})`. Establish `h4 : finrank E U < finrank E (U ⊔ Submodule.span E {f} : Submodule E S.V)`. Use `Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne le_sup_left ?_)` and prove the remaining obligations.

Introduce `h`. Apply `hf` to reduce the goal to its premises. Rewrite using `[h]`. Conclude with `Submodule.mem_sup_right (Submodule.mem_span_singleton_self f)`. Use linear arithmetic over natural numbers and integers.
-/
theorem scal_exists_v (U : Submodule E S.V) (f : S.V) (hf : f ∉ U) :
    ∃ v, (∀ x ∈ U, S.hT v x = 0) ∧ S.hT v f ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hle : orth S U ≤ orth S (U ⊔ Submodule.span E {f}) := by
    intro v hv
    rw [p_mem_orth] at hv ⊢
    have hvf := hcon v (fun x hx => p_symm_zero S (hv x hx))
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hb
    rw [map_add, LinearMap.add_apply, hv a ha, map_smulₛₗ, LinearMap.smul_apply, p_symm_zero S hvf, smul_zero,
      add_zero]
  have h1 := Submodule.finrank_mono hle
  have h2 := c_finrank_orth_ge U
  have h3 := c_finrank_orth_le (U ⊔ Submodule.span E {f})
  have h4 : finrank E U < finrank E (U ⊔ Submodule.span E {f} : Submodule E S.V) := by
    refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne le_sup_left ?_)
    intro h
    apply hf
    rw [h]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self f)
  omega

/- English proof (translation)
Establish `h1` using `h (star (1 - ρ))`. Establish `e1 : (1 - ρ) * star (1 - ρ) = star (1 - ρ) - ρ * star (1 - ρ)` using `by ring`. Establish `h2 : (1 - ρ) * star (1 - ρ) + star ((1 - ρ) * star (1 - ρ)) = 0`. Establish `e2 : star ((1 - ρ) * star (1 - ρ)) = star (star (1 - ρ)) - star (ρ * star (1 - ρ))`. Rewrite using `[e1]`.

Conclude with `star_sub _ _`. Rewrite using `[e2, e1]`. Take the linear combination `h1`. Establish `h3 : star ((1 - ρ) * star (1 - ρ)) = (1 - ρ) * star (1 - ρ)`. Rewrite using `[star_mul', star_star, mul_comm]`.

Rewrite `h2` using `[h3]`. Establish `h4 : (1 - ρ) * star (1 - ρ) = 0`. Establish `: (2 : E) * ((1 - ρ) * star (1 - ρ)) = 0` using `by linear_combination h2`. Conclude with `(mul_eq_zero.1 this).resolve_left two_ne_zero`. Establish `h5 : 1 - ρ = 0`.

Break down `mul_eq_zero.1 h4 with h | h` into its components or cases. Conclude with `h`. Conclude with `star_eq_zero.1 h`. Conclude with `(sub_eq_zero.1 h5).symm`.
-/
theorem scal_alg (ρ : E) (h : ∀ κ : E, κ + star κ = ρ * κ + star (ρ * κ)) : ρ = 1 := by
  have h1 := h (star (1 - ρ))
  have e1 : (1 - ρ) * star (1 - ρ) = star (1 - ρ) - ρ * star (1 - ρ) := by ring
  have h2 : (1 - ρ) * star (1 - ρ) + star ((1 - ρ) * star (1 - ρ)) = 0 := by
    have e2 : star ((1 - ρ) * star (1 - ρ)) = star (star (1 - ρ)) - star (ρ * star (1 - ρ)) := by
      rw [e1]
      exact star_sub _ _
    rw [e2, e1]
    linear_combination h1
  have h3 : star ((1 - ρ) * star (1 - ρ)) = (1 - ρ) * star (1 - ρ) := by
    rw [star_mul', star_star, mul_comm]
  rw [h3] at h2
  have h4 : (1 - ρ) * star (1 - ρ) = 0 := by
    have : (2 : E) * ((1 - ρ) * star (1 - ρ)) = 0 := by linear_combination h2
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero
  have h5 : 1 - ρ = 0 := by
    rcases mul_eq_zero.1 h4 with h | h
    · exact h
    · exact star_eq_zero.1 h
  exact (sub_eq_zero.1 h5).symm

/- English proof (translation)
Establish `hX : F'.X = F.X` using `by rw [tie_X_eq_Xa, tie_X_eq_Xa, hXa]`. Establish `heX : F.e i ∈ F.X` using `Submodule.subset_span ⟨i, rfl⟩`. Establish `hci0` using `hcs i.castSucc`. Rewrite `hci0` using `[geo_fvec_cast, geo_fvec_cast]`. Establish `hci0' : F'.e i - cs i.castSucc • F.e i ∈ F.Xa i.val` using `hci0`.

Establish `hci : cs i.castSucc ≠ 0`. Introduce `h0`. Rewrite `hci0'` using `[h0, zero_smul, sub_zero, ← hXa]`. Conclude with `scal_e_notMem F' i hci0'`. Establish `key : ∀ v : S.V, (∀ x ∈ F.Xa (i.val + 1), S.hT v x = 0) → S.hT v (F.fvec i.succ) + star (S.hT v (F.fvec i.succ)) = (cs i.succ * (cs i.castSucc)⁻¹) * S.hT v (F.fvec i.succ) + star ((cs i.succ * (cs i.castSucc)⁻¹) * S.hT v (F.fvec i.succ))`.

Introduce `v hv`. Establish `mF` using `scal_mem_LieN F i v hv`. Establish `mF' : xv S (F.e i) v ∈ F'.LieN` using `⟨mF.1, fun a ha1 har x hx => by rw [hXa] at hx ⊢; exact mF.2.1 a ha1 har x hx, fun x hx => by rw [hX] at hx ⊢; exact mF.2.2 x hx⟩`. Establish `eF : F.ell (xv S (F.e i) v) = S.hT v (F.fvec i.succ) * 1` using `scal_ell F _ i (F.e i) 1 0 (Submodule.zero_mem _) (by simp) (fun p => S.hT v (F.fvec p)) (fun p => scal_xv_val _ _ _ (geo_X_fvec F _ heX p)) (fun p hp => hv _ (by`. Establish `hpr : p.val < r` using `lt_of_le_of_lt hp i.isLt`.

Establish `e : p = Fin.castSucc ⟨p.val, hpr⟩` using `Fin.ext rfl`. Rewrite using `[e, geo_fvec_cast]`. Conclude with `geo_e_mem_Xa F _ _ (Nat.lt_succ_of_le hp)))`. Establish `eF' : F'.ell (xv S (F.e i) v) = S.hT v (F'.fvec i.succ) * (cs i.castSucc)⁻¹` using `scal_ell F' _ i (F.e i) (cs i.castSucc)⁻¹ (-((cs i.castSucc)⁻¹ • (F'.e i - cs i.castSucc • F.e i))) (by rw [hXa]; exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hci0')) (by rw [smul_sub, smul_smul, inv_mul_cancel₀ hci, one_smul]; abel) (fun p => S.hT v (F'.fvec p)) (fun p => s …`. Establish `hpr : p.val < r` using `lt_of_le_of_lt hp i.isLt`.

Establish `e : p = Fin.castSucc ⟨p.val, hpr⟩` using `Fin.ext rfl`. Rewrite using `[e, geo_fvec_cast, ← hXa]`. Conclude with `geo_e_mem_Xa F' _ _ (Nat.lt_succ_of_le hp)))`. Establish `hγ : S.hT v (F'.fvec i.succ) = cs i.succ * S.hT v (F.fvec i.succ)`. Establish `hd` using `hv _ (hcs i.succ)`.

Rewrite `hd` using `[map_sub, map_smul, smul_eq_mul, sub_eq_zero]`. Conclude with `hd`. Establish `hR : Algebra.trace K E (F.ell (xv S (F.e i) v)) = Algebra.trace K E (F'.ell (xv S (F.e i) v))` using `hrel _ ⟨mF, mF'⟩`. Establish `hR'` using `congrArg (algebraMap K E) hR`. Rewrite `hR'` using `[htr, htr, eF, eF', hγ, mul_one]`.

Establish `e2 : cs i.succ * S.hT v (F.fvec i.succ) * (cs i.castSucc)⁻¹ = (cs i.succ * (cs i.castSucc)⁻¹) * S.hT v (F.fvec i.succ)` using `by ring`. Rewrite `hR'` using `[e2]`. Conclude with `hR'`. Take `⟨v0, hv0, hk0⟩` from `scal_exists_v (F.Xa (i.val + 1)) (F.fvec i.succ) (hfn i)`. Establish `hρ : cs i.succ * (cs i.castSucc)⁻¹ = 1`.

Apply `scal_alg` to reduce the goal to its premises. Introduce `κ`. Establish `h` using `key (star (κ / S.hT v0 (F.fvec i.succ)) • v0) (fun x hx => by`. Rewrite using `[map_smulₛₗ, LinearMap.smul_apply, hv0 x hx, smul_zero])`. Establish `e : S.hT (star (κ / S.hT v0 (F.fvec i.succ)) • v0) (F.fvec i.succ) = κ`.

Rewrite using `[map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul, div_mul_cancel₀ _ hk0]`. Rewrite `h` using `[e]`. Conclude with `h`. Clear denominators, using `at hρ` for the nonvanishing conditions. Conclude with `hρ`.
-/
theorem scal_step (K : Type) [Field K] [Algebra K E] (F F' : FlagG S r T)
    (htr : ∀ x : E, algebraMap K E (Algebra.trace K E x) = x + star x)
    (hXa : ∀ j, F'.Xa j = F.Xa j) (hrel : Relevant K F F')
    (cs : Fin (r + 1) → E) (hcs : ∀ p, F'.fvec p - cs p • F.fvec p ∈ F.Xa p.val)
    (hfn : ∀ i : Fin r, F.fvec i.succ ∉ F.Xa (i.val + 1)) (i : Fin r) : cs i.succ = cs i.castSucc := by
  have hX : F'.X = F.X := by rw [tie_X_eq_Xa, tie_X_eq_Xa, hXa]
  have heX : F.e i ∈ F.X := Submodule.subset_span ⟨i, rfl⟩
  have hci0 := hcs i.castSucc
  rw [geo_fvec_cast, geo_fvec_cast] at hci0
  have hci0' : F'.e i - cs i.castSucc • F.e i ∈ F.Xa i.val := hci0
  have hci : cs i.castSucc ≠ 0 := by
    intro h0
    rw [h0, zero_smul, sub_zero, ← hXa] at hci0'
    exact scal_e_notMem F' i hci0'
  have key : ∀ v : S.V, (∀ x ∈ F.Xa (i.val + 1), S.hT v x = 0) →
      S.hT v (F.fvec i.succ) + star (S.hT v (F.fvec i.succ)) =
        (cs i.succ * (cs i.castSucc)⁻¹) * S.hT v (F.fvec i.succ) +
          star ((cs i.succ * (cs i.castSucc)⁻¹) * S.hT v (F.fvec i.succ)) := by
    intro v hv
    have mF := scal_mem_LieN F i v hv
    have mF' : xv S (F.e i) v ∈ F'.LieN :=
      ⟨mF.1, fun a ha1 har x hx => by rw [hXa] at hx ⊢; exact mF.2.1 a ha1 har x hx,
        fun x hx => by rw [hX] at hx ⊢; exact mF.2.2 x hx⟩
    have eF : F.ell (xv S (F.e i) v) = S.hT v (F.fvec i.succ) * 1 :=
      scal_ell F _ i (F.e i) 1 0 (Submodule.zero_mem _) (by simp) (fun p => S.hT v (F.fvec p))
        (fun p => scal_xv_val _ _ _ (geo_X_fvec F _ heX p))
        (fun p hp => hv _ (by
          have hpr : p.val < r := lt_of_le_of_lt hp i.isLt
          have e : p = Fin.castSucc ⟨p.val, hpr⟩ := Fin.ext rfl
          rw [e, geo_fvec_cast]
          exact geo_e_mem_Xa F _ _ (Nat.lt_succ_of_le hp)))
    have eF' : F'.ell (xv S (F.e i) v) = S.hT v (F'.fvec i.succ) * (cs i.castSucc)⁻¹ :=
      scal_ell F' _ i (F.e i) (cs i.castSucc)⁻¹ (-((cs i.castSucc)⁻¹ • (F'.e i - cs i.castSucc • F.e i)))
        (by rw [hXa]; exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hci0'))
        (by rw [smul_sub, smul_smul, inv_mul_cancel₀ hci, one_smul]; abel)
        (fun p => S.hT v (F'.fvec p))
        (fun p => scal_xv_val _ _ _ (geo_X_fvec F' _ (by rw [hX]; exact heX) p))
        (fun p hp => hv _ (by
          have hpr : p.val < r := lt_of_le_of_lt hp i.isLt
          have e : p = Fin.castSucc ⟨p.val, hpr⟩ := Fin.ext rfl
          rw [e, geo_fvec_cast, ← hXa]
          exact geo_e_mem_Xa F' _ _ (Nat.lt_succ_of_le hp)))
    have hγ : S.hT v (F'.fvec i.succ) = cs i.succ * S.hT v (F.fvec i.succ) := by
      have hd := hv _ (hcs i.succ)
      rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hd
      exact hd
    have hR : Algebra.trace K E (F.ell (xv S (F.e i) v)) = Algebra.trace K E (F'.ell (xv S (F.e i) v)) :=
      hrel _ ⟨mF, mF'⟩
    have hR' := congrArg (algebraMap K E) hR
    rw [htr, htr, eF, eF', hγ, mul_one] at hR'
    have e2 : cs i.succ * S.hT v (F.fvec i.succ) * (cs i.castSucc)⁻¹ =
        (cs i.succ * (cs i.castSucc)⁻¹) * S.hT v (F.fvec i.succ) := by ring
    rw [e2] at hR'
    exact hR'
  obtain ⟨v0, hv0, hk0⟩ := scal_exists_v (F.Xa (i.val + 1)) (F.fvec i.succ) (hfn i)
  have hρ : cs i.succ * (cs i.castSucc)⁻¹ = 1 := by
    apply scal_alg
    intro κ
    have h := key (star (κ / S.hT v0 (F.fvec i.succ)) • v0) (fun x hx => by
      rw [map_smulₛₗ, LinearMap.smul_apply, hv0 x hx, smul_zero])
    have e : S.hT (star (κ / S.hT v0 (F.fvec i.succ)) • v0) (F.fvec i.succ) = κ := by
      rw [map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul, div_mul_cancel₀ _ hk0]
    rw [e] at h
    exact h
  field_simp at hρ
  exact hρ

end Scal

/- English proof (translation)
Introduce `K E _ _ _ _ _ S r T F F' hT0 htr hXa hXp hrel`. Establish `hX : F'.X = F.X` using `by rw [tie_X_eq_Xa, tie_X_eq_Xa, hXa]`. Establish `h1 : ∀ p : Fin (r + 1), ∃ c : E, F'.fvec p - c • F.fvec p ∈ F.Xa p.val`. Introduce `p`. Use `Fin.lastCases ?_ (fun a => ?_) p` and prove the remaining obligations.

Rewrite using `[geo_fvec_last, geo_fvec_last]`. Establish `hz : F'.z ∈ F.Xplus`. Rewrite using `[← hXp]`. Conclude with `Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`. Take `⟨x, hx, y, hy, hxy⟩` from `Submodule.mem_sup.1 hz`.

Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hy`. Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite using `[← hxy, add_sub_cancel_right, Fin.val_last, ← tie_X_eq_Xa]`. Conclude with `hx`. Rewrite using `[geo_fvec_cast, geo_fvec_cast]`.

Conclude with `scal_Xa_succ F a _ (by rw [← hXa]; exact geo_e_mem_Xa F' a _ (Nat.lt_succ_self _))`. Use `choose cs hcs using h1`. Establish `hfn : ∀ i : Fin r, F.fvec i.succ ∉ F.Xa (i.val + 1)`. Introduce `i h`. Distinguish the cases in `hi : i.val + 1 < r`.

Establish `e : i.succ = Fin.castSucc ⟨i.val + 1, hi⟩` using `Fin.ext rfl`. Rewrite `h` using `[e, geo_fvec_cast]`. Conclude with `scal_e_notMem F ⟨i.val + 1, hi⟩ h`. Establish `e : i.succ = Fin.last r` using `Fin.ext (by rw [Fin.val_succ, Fin.val_last]; have := i.isLt; omega)`. Rewrite `h` using `[e, geo_fvec_last]`.

Establish `hzX` using `geo_Xa_le_X F _ h`. Establish `h0` using `geo_X_X F _ _ hzX hzX`. Rewrite `h0` using `[F.z_norm]`. Conclude with `hT0 (neg_eq_zero.1 h0)`. Establish `hstep` using `scal_step K F F' htr hXa hrel cs hcs hfn`.

Establish `hall : ∀ p : Fin (r + 1), cs p = cs 0`. Introduce `p`. Proceed by induction on `p using Fin.induction with`. Consider the case `zero => rfl`. Consider the case `succ i ih => exact (hstep i).trans ih`.

Establish `hc : ∀ p, cs p = cs (Fin.last r)` using `fun p => (hall p).trans (hall _).symm`. Establish `hzc : F'.z - cs (Fin.last r) • F.z ∈ F.X`. Use `hcs (Fin.last r)` as an intermediate fact. Rewrite `this` using `[geo_fvec_last, geo_fvec_last, Fin.val_last, ← tie_X_eq_Xa]`. Conclude with `this`.

Use `⟨cs (Fin.last r), ?_, fun a => ?_, hzc⟩` and prove the remaining obligations. Use `set c := cs (Fin.last r) with hcdef set x := F'.z - c • F.z with hx`. Establish `hz' : F'.z = c • F.z + x` using `by rw [hx]; abel`. Establish `hzx : S.hT F.z x = 0`. Use `geo_fvec_X F x hzc (Fin.last r)` as an intermediate fact.

Rewrite `this` using `[geo_fvec_last]`. Then use the resulting hypothesis. Establish `hxz : S.hT x F.z = 0` using `Formalism.MainNotions.LatticeGluingRadicals.p_symm_zero S hzx`. Establish `hxx : S.hT x x = 0` using `geo_X_X F _ _ hzc hzc`. Establish `hn` using `F'.z_norm`. Rewrite `hn` using `[hz']`.

Simplify using `only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hzx, hxz, hxx, F.z_norm, mul_zero, add_zero, starRingEnd_apply] at hn`. Establish `: (c * star c) * T = 1 * T` using `by linear_combination -hn`. Conclude with `mul_right_cancel₀ hT0 this`. Use `hcs a.castSucc` as an intermediate fact. Rewrite `this` using `[geo_fvec_cast, geo_fvec_cast, hc]`.

Conclude with `this`.
-/
theorem id_scal : EqualFlagsScalar := by
  intro K E _ _ _ _ _ S r T F F' hT0 htr hXa hXp hrel
  have hX : F'.X = F.X := by rw [tie_X_eq_Xa, tie_X_eq_Xa, hXa]
  have h1 : ∀ p : Fin (r + 1), ∃ c : E, F'.fvec p - c • F.fvec p ∈ F.Xa p.val := by
    intro p
    refine Fin.lastCases ?_ (fun a => ?_) p
    · rw [geo_fvec_last, geo_fvec_last]
      have hz : F'.z ∈ F.Xplus := by
        rw [← hXp]
        exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
      obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hz
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      refine ⟨c, ?_⟩
      rw [← hxy, add_sub_cancel_right, Fin.val_last, ← tie_X_eq_Xa]
      exact hx
    · rw [geo_fvec_cast, geo_fvec_cast]
      exact scal_Xa_succ F a _ (by rw [← hXa]; exact geo_e_mem_Xa F' a _ (Nat.lt_succ_self _))
  choose cs hcs using h1
  have hfn : ∀ i : Fin r, F.fvec i.succ ∉ F.Xa (i.val + 1) := by
    intro i h
    by_cases hi : i.val + 1 < r
    · have e : i.succ = Fin.castSucc ⟨i.val + 1, hi⟩ := Fin.ext rfl
      rw [e, geo_fvec_cast] at h
      exact scal_e_notMem F ⟨i.val + 1, hi⟩ h
    · have e : i.succ = Fin.last r := Fin.ext (by rw [Fin.val_succ, Fin.val_last]; have := i.isLt; omega)
      rw [e, geo_fvec_last] at h
      have hzX := geo_Xa_le_X F _ h
      have h0 := geo_X_X F _ _ hzX hzX
      rw [F.z_norm] at h0
      exact hT0 (neg_eq_zero.1 h0)
  have hstep := scal_step K F F' htr hXa hrel cs hcs hfn
  have hall : ∀ p : Fin (r + 1), cs p = cs 0 := by
    intro p
    induction p using Fin.induction with
    | zero => rfl
    | succ i ih => exact (hstep i).trans ih
  have hc : ∀ p, cs p = cs (Fin.last r) := fun p => (hall p).trans (hall _).symm
  have hzc : F'.z - cs (Fin.last r) • F.z ∈ F.X := by
    have := hcs (Fin.last r)
    rw [geo_fvec_last, geo_fvec_last, Fin.val_last, ← tie_X_eq_Xa] at this
    exact this
  refine ⟨cs (Fin.last r), ?_, fun a => ?_, hzc⟩
  · set c := cs (Fin.last r) with hcdef
    set x := F'.z - c • F.z with hx
    have hz' : F'.z = c • F.z + x := by rw [hx]; abel
    have hzx : S.hT F.z x = 0 := by
      have := geo_fvec_X F x hzc (Fin.last r)
      rwa [geo_fvec_last] at this
    have hxz : S.hT x F.z = 0 := Formalism.MainNotions.LatticeGluingRadicals.p_symm_zero S hzx
    have hxx : S.hT x x = 0 := geo_X_X F _ _ hzc hzc
    have hn := F'.z_norm
    rw [hz'] at hn
    simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hzx, hxz, hxx,
      F.z_norm, mul_zero, add_zero, starRingEnd_apply] at hn
    have : (c * star c) * T = 1 * T := by linear_combination -hn
    exact mul_right_cancel₀ hT0 this
  · have := hcs a.castSucc
    rw [geo_fvec_cast, geo_fvec_cast, hc] at this
    exact this

end Formalism.MainNotions.BridgeLemma

end
