import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyLinearEqui
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ParabolicInductionTrivialPreservesVirtualCharact
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct GlobalTheory.ParabVirt
open scoped Classical

noncomputable section
namespace GlobalTheory.ShinPsiRec

variable {F : Type} [Field F]

def low (a n : ℕ) : Submodule F (Fin n → F) where
  carrier := {v | ∀ i : Fin n, a ≤ (i : ℕ) → v i = 0}
  add_mem' := fun {u v} hu hv i hi => by simp [hu i hi, hv i hi]
  zero_mem' := fun i _ => rfl
  smul_mem' := fun c v hv i hi => by simp [hv i hi]

/- English proof (translation)
Rewrite using `[mem_stab]`. Prove the components needed by the constructor for the conclusion. Introduce `h i j hj hi`. Establish `hv : (Pi.single j 1 : Fin n → F) ∈ low a n`. Introduce `k hk`.

Establish `: k ≠ j` using `by intro e; subst e; omega`. Simplify using `[Pi.single_apply, this]`. Use `h _ hv i hi` as an intermediate fact. Simplify `this` using `[Matrix.toLin'_apply, Matrix.mulVec_single_one]`. Introduce `h v hv i hi`.

Rewrite using `[Matrix.toLin'_apply]`. Simplify using `only [Matrix.mulVec, dotProduct]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : (j : ℕ) < a`. Rewrite using `[h i j hj hi, zero_mul]`.

Rewrite using `[hv j (by omega), mul_zero]`.
-/
theorem mem_stab_low_iff (a n : ℕ) (x : GL (Fin n) F) : x ∈ stab (low (F := F) a n) ↔ InPar a x := by
  rw [mem_stab]
  constructor
  · intro h i j hj hi
    have hv : (Pi.single j 1 : Fin n → F) ∈ low a n := by
      intro k hk
      have : k ≠ j := by intro e; subst e; omega
      simp [Pi.single_apply, this]
    have := h _ hv i hi
    simpa [Matrix.toLin'_apply, Matrix.mulVec_single_one] using this
  · intro h v hv i hi
    rw [Matrix.toLin'_apply]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : (j : ℕ) < a
    · rw [h i j hj hi, zero_mul]
    · rw [hv j (by omega), mul_zero]

def lowEquiv {a n : ℕ} (ha : a ≤ n) : low (F := F) a n ≃ₗ[F] (Fin a → F) where
  toFun v := fun i => v.1 (Fin.castLE ha i)
  map_add' u v := rfl
  map_smul' c v := rfl
  invFun w := ⟨fun k => if h : (k : ℕ) < a then w ⟨k, h⟩ else 0, fun k hk => dif_neg (by omega)⟩
  left_inv v := by
    ext k
    dsimp only
    split_ifs with h
    · rfl
    · exact (v.2 k (by omega)).symm
  right_inv w := by
    funext i
    simp

/- English proof (translation)
Use extensionality with `i j`. Establish `hs : ((lowEquiv (F` using `F) ha).symm (Pi.single j 1)).1 = Pi.single (Fin.castLE ha j) 1 := by`. Use function extensionality and compare the values at `k`. Express the relevant statement in the definitionally equal form `(if h : (k : ℕ) < a then (Pi.single j 1 : Fin a → F) ⟨k, h⟩ else 0) = _`. Use `split_ifs with h`.

Simplify using `only [Pi.single_apply, Fin.ext_iff, Fin.val_castLE]`. Establish `: k ≠ Fin.castLE ha j`. Introduce `e`. Rewrite `h` using `[e, Fin.val_castLE]`. Conclude with `h j.2`.

Simplify using `[Pi.single_apply, this]`. Simplify using `only [resMat, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.toMatrix'_apply, LinearEquiv.conj_apply_apply]`. Express the relevant statement in the definitionally equal form `(Matrix.toLin' (p : Matrix (Fin n) (Fin n) F) ((lowEquiv (F := F) ha).symm (Pi.single j 1)).1) (Fin.castLE ha i) = _`. Rewrite using `[hs, Matrix.toLin'_apply, Matrix.mulVec_single_one]`. Establish `hi : (i : ℕ) < n` using `by omega`.

Establish `hj : (j : ℕ) < n` using `by omega`. Simplify using `only [tl, ent, dif_pos (And.intro hi hj), Matrix.transpose_apply]`. Both sides reduce to the same expression.
-/
theorem resMat_low {a n : ℕ} (ha : a ≤ n) (p : GL (Fin n) F) (hp : p ∈ stab (low (F := F) a n)) :
    resMat (low a n) (lowEquiv ha) ⟨p, hp⟩ = tl a (p : Matrix (Fin n) (Fin n) F) := by
  ext i j
  have hs : ((lowEquiv (F := F) ha).symm (Pi.single j 1)).1 = Pi.single (Fin.castLE ha j) 1 := by
    funext k
    change (if h : (k : ℕ) < a then (Pi.single j 1 : Fin a → F) ⟨k, h⟩ else 0) = _
    split_ifs with h
    · simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castLE]
    · have : k ≠ Fin.castLE ha j := by
        intro e; rw [e, Fin.val_castLE] at h; exact h j.2
      simp [Pi.single_apply, this]
  simp only [resMat, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.toMatrix'_apply, LinearEquiv.conj_apply_apply]
  change (Matrix.toLin' (p : Matrix (Fin n) (Fin n) F) ((lowEquiv (F := F) ha).symm (Pi.single j 1)).1)
    (Fin.castLE ha i) = _
  rw [hs, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  have hi : (i : ℕ) < n := by omega
  have hj : (j : ℕ) < n := by omega
  simp only [tl, ent, dif_pos (And.intro hi hj), Matrix.transpose_apply]
  rfl

/- English proof (translation)
Establish `hp'` using `(mem_stab_low_iff a n p).2 hp`. Rewrite using `[← resMat_low ha p hp']`. Conclude with `IsUnit.map (resMat (low a n) (lowEquiv ha)) (Group.isUnit _)`.
-/
theorem tl_isUnit {a n : ℕ} (ha : a ≤ n) (p : GL (Fin n) F) (hp : InPar a p) :
    IsUnit (tl a (p : Matrix (Fin n) (Fin n) F)) := by
  have hp' := (mem_stab_low_iff a n p).2 hp
  rw [← resMat_low ha p hp']
  exact IsUnit.map (resMat (low a n) (lowEquiv ha)) (Group.isUnit _)

/- English proof (translation)
Unfold `tlG toG`. Rewrite using `[dif_pos (tl_isUnit ha p hp)]`. Both sides reduce to the same expression.
-/
theorem coe_tlG {a n : ℕ} (ha : a ≤ n) (p : GL (Fin n) F) (hp : InPar a p) :
    ((tlG a p : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = tl a (p : Matrix (Fin n) (Fin n) F) := by
  unfold tlG toG
  rw [dif_pos (tl_isUnit ha p hp)]
  rfl

/- English proof (translation)
Rewrite using `[psiG, coe_tlG ha p ((mem_stab_low_iff a n p).1 hp), ← resMat_low ha p hp]`. Simplify using `only [resMat, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.toLin'_toMatrix']`. Rewrite using `[psi_conj]`.
-/
theorem psi_restrict_low (S : F[X] → ℂ) {a n : ℕ} (ha : a ≤ n) (p : GL (Fin n) F)
    (hp : p ∈ stab (low (F := F) a n)) :
    psi S (low (F := F) a n) ((Matrix.toLin' (p : Matrix (Fin n) (Fin n) F)).restrict hp) =
      psiG S a (tlG a p) := by
  rw [psiG, coe_tlG ha p ((mem_stab_low_iff a n p).1 hp), ← resMat_low ha p hp]
  simp only [resMat, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.toLin'_toMatrix']
  rw [psi_conj]

def resPsi (S : F[X] → ℂ) {n : ℕ} (x : GL (Fin n) F) (W : Submodule F (Fin n → F)) : ℂ :=
  if h : x ∈ stab W then psi S W ((Matrix.toLin' (x : Matrix (Fin n) (Fin n) F)).restrict h) else 0

/- English proof (translation)
Use `haveI : Finite (Submodule F (Fin n → F)) := Finite.of_injective (fun W : Submodule F (Fin n → F) => (W : Set (Fin n → F))) SetLike.coe_injective`. Use `letI := Fintype.ofFinite (GL (Fin n) F)`. Use `letI := Fintype.ofFinite (Submodule F (Fin n → F))`. Use `set W₀ := low (F := F) a n with hW₀def`. Establish `hW₀ : Module.finrank F W₀ = a` using `(lowEquiv ha).finrank_eq.trans (Module.finrank_fin_fun F)`.

Set `π : GL (Fin n) F → {W : Submodule F (Fin n → F) // Module.finrank F W = a}` to `fun t => ⟨W₀.map (lin t).toLinearMap, (LinearEquiv.finrank_map_eq _ _).trans hW₀⟩`. Establish `hs : Function.Surjective π`. Introduce `W`. Take `⟨f⟩ : Nonempty (W₀ ≃ₗ[F] W.1)` from `FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (hW₀.trans W.2.symm)`. Take `⟨g, hg⟩` from `Submodule.exists_linearEquiv_restrict_eq f`.

Take `⟨t, rfl⟩` from `lin_surjective g`. Use `⟨t, Subtype.ext ?_⟩` and prove the remaining obligations. Apply `Submodule.eq_of_le_of_finrank_eq` to reduce the goal to its premises. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Use `(f ⟨v, hv⟩).2` as an intermediate fact.

Rewrite `this` using `[hg]`. Conclude with `this`. Conclude with `(π t).2.trans W.2.symm`. Establish `hsum` using `sum_fibres (stab W₀) π hs (fun s t => Subtype.ext_iff.trans (map_eq_map_iff W₀ s t)) (fun W => resPsi S x W.1)`. Establish `hg : ∀ t : GL (Fin n) F, gal (RingHom.id F) n t = t`.

Introduce `t`. Use extensionality with `i j`. Simplify using `[gal]`. Establish `hterm : ∀ t : GL (Fin n) F, resPsi S x (π t).1 = (if InPar a (t⁻¹ * x * gal (RingHom.id F) n t) then psiG S a (tlG a (t⁻¹ * x * gal (RingHom.id F) n t)) * (fun _ => (1 : ℂ)) (brG a (n - a) (t⁻¹ * x * gal (RingHom.id F) n t)) else 0)`. Introduce `t`.

Rewrite using `[hg, mul_one]`. Simplify using `only [resPsi, π]`. Distinguish the cases in `h : t⁻¹ * x * t ∈ stab W₀`. Establish `h'` using `(conj_mem_stab_iff W₀ x t).1 h`. Rewrite using `[dif_pos h', if_pos ((mem_stab_low_iff a n _).1 h), ← psi_restrict_low S ha _ h, ← psi_conj F S _ _ ((lin t).submoduleMap W₀)]`.

Use `congr 1`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Take `⟨w, rfl⟩` from `((lin t).submoduleMap W₀).surjective v`. Rewrite using `[LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]`. Use `ext1`.

Express the relevant statement in the definitionally equal form `lin x (lin t w) = lin t (lin (t⁻¹ * x * t) w)`. Rewrite using `[← lin_mul, ← lin_mul, mul_assoc, mul_inv_cancel_left]`. Rewrite using `[dif_neg (fun h' => h ((conj_mem_stab_iff W₀ x t).2 h')), if_neg (fun h'' => h ((mem_stab_low_iff a n _).2 h''))]`. Establish `hcard : Nat.card {p : GL (Fin n) F // InPar a p} = Nat.card (stab W₀)` using `Nat.card_congr (Equiv.subtypeEquivRight fun p => (mem_stab_low_iff a n p).symm)`. Establish `hc0 : (Nat.card (stab W₀) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`.

Simplify using `only [hc, hcTw]`. Rewrite using `[hcard, ← finsum_congr hterm, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, hsum, inv_mul_cancel_left₀ hc0]`.
-/
theorem finsum_rank_eq_hc [Finite F] (S : F[X] → ℂ) {a n : ℕ} (ha : a ≤ n) (x : GL (Fin n) F) :
    ∑ᶠ W : {W : Submodule F (Fin n → F) // Module.finrank F W = a}, resPsi S x W.1 =
      hc a (n - a) (psiG S a) (fun _ => 1) n x := by
  classical
  haveI : Finite (Submodule F (Fin n → F)) :=
    Finite.of_injective (fun W : Submodule F (Fin n → F) => (W : Set (Fin n → F))) SetLike.coe_injective
  letI := Fintype.ofFinite (GL (Fin n) F)
  letI := Fintype.ofFinite (Submodule F (Fin n → F))
  set W₀ := low (F := F) a n with hW₀def
  have hW₀ : Module.finrank F W₀ = a := (lowEquiv ha).finrank_eq.trans (Module.finrank_fin_fun F)
  let π : GL (Fin n) F → {W : Submodule F (Fin n → F) // Module.finrank F W = a} := fun t =>
    ⟨W₀.map (lin t).toLinearMap, (LinearEquiv.finrank_map_eq _ _).trans hW₀⟩
  have hs : Function.Surjective π := by
    intro W
    obtain ⟨f⟩ : Nonempty (W₀ ≃ₗ[F] W.1) :=
      FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (hW₀.trans W.2.symm)
    obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
    obtain ⟨t, rfl⟩ := lin_surjective g
    refine ⟨t, Subtype.ext ?_⟩
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨v, hv, rfl⟩
      have := (f ⟨v, hv⟩).2
      rw [hg] at this
      exact this
    · exact (π t).2.trans W.2.symm
  have hsum := sum_fibres (stab W₀) π hs
    (fun s t => Subtype.ext_iff.trans (map_eq_map_iff W₀ s t)) (fun W => resPsi S x W.1)
  have hg : ∀ t : GL (Fin n) F, gal (RingHom.id F) n t = t := by
    intro t; ext i j; simp [gal]
  have hterm : ∀ t : GL (Fin n) F, resPsi S x (π t).1 =
      (if InPar a (t⁻¹ * x * gal (RingHom.id F) n t) then
        psiG S a (tlG a (t⁻¹ * x * gal (RingHom.id F) n t)) *
          (fun _ => (1 : ℂ)) (brG a (n - a) (t⁻¹ * x * gal (RingHom.id F) n t)) else 0) := by
    intro t
    rw [hg, mul_one]
    simp only [resPsi, π]
    by_cases h : t⁻¹ * x * t ∈ stab W₀
    · have h' := (conj_mem_stab_iff W₀ x t).1 h
      rw [dif_pos h', if_pos ((mem_stab_low_iff a n _).1 h), ← psi_restrict_low S ha _ h,
        ← psi_conj F S _ _ ((lin t).submoduleMap W₀)]
      congr 1
      refine LinearMap.ext fun v => ?_
      obtain ⟨w, rfl⟩ := ((lin t).submoduleMap W₀).surjective v
      rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
      ext1
      change lin x (lin t w) = lin t (lin (t⁻¹ * x * t) w)
      rw [← lin_mul, ← lin_mul, mul_assoc, mul_inv_cancel_left]
    · rw [dif_neg (fun h' => h ((conj_mem_stab_iff W₀ x t).2 h')),
        if_neg (fun h'' => h ((mem_stab_low_iff a n _).2 h''))]
  have hcard : Nat.card {p : GL (Fin n) F // InPar a p} = Nat.card (stab W₀) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun p => (mem_stab_low_iff a n p).symm)
  have hc0 : (Nat.card (stab W₀) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  simp only [hc, hcTw]
  rw [hcard, ← finsum_congr hterm, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, hsum,
    inv_mul_cancel_left₀ hc0]

end GlobalTheory.ShinPsiRec

namespace GlobalTheory.ShinPsiRec

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `Submodule.finrank_lt h` as an intermediate fact. Rewrite `this` using `[Module.finrank_fin_fun]`. Then use the resulting hypothesis. Introduce `h htop`.

Rewrite `h` using `[htop, finrank_top, Module.finrank_fin_fun]`. Conclude with `lt_irrefl _ h`.
-/
theorem ne_top_iff_finrank_lt {F : Type} [Field F] {n : ℕ} (W : Submodule F (Fin n → F)) :
    W ≠ ⊤ ↔ Module.finrank F W < n := by
  constructor
  · intro h
    have := Submodule.finrank_lt h
    rwa [Module.finrank_fin_fun] at this
  · intro h htop
    rw [htop, finrank_top, Module.finrank_fin_fun] at h
    exact lt_irrefl _ h

/- English proof (translation)
Use `haveI : Finite (Submodule F (Fin n → F)) := Finite.of_injective (fun W : Submodule F (Fin n → F) => (W : Set (Fin n → F))) SetLike.coe_injective`. Use `letI := Fintype.ofFinite (Submodule F (Fin n → F))`. Use `show psi S _ _ = S _ - _`. Rewrite using `[psi_eq, Matrix.charpoly_toLin']`. Use `congr 1`.

Rewrite using `[Finset.sum_congr rfl fun a ha => (finsum_rank_eq_hc S (le_of_lt (Finset.mem_range.1 ha)) x).symm]`. Establish `step : ∀ a : ℕ, ∑ᶠ W : {W : Submodule F (Fin n → F) // Module.finrank F W = a}, resPsi S x W.1 = ∑ W : Submodule F (Fin n → F), if Module.finrank F W = a then resPsi S x W else 0`. Introduce `a`. Rewrite using `[finsum_eq_sum_of_fintype, ← Finset.sum_filter]`. Conclude with `(Finset.sum_subtype _ (by simp) _).symm`.

Simplify using `only [step]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [Finset.sum_ite_eq]`. Rewrite using `[finsum_eq_sum_of_fintype]`. Rewrite using `[Finset.sum_congr rfl (g := fun W => resPsi S x W.1) fun W _ => by`.

Unfold `resPsi`. Rewrite using `[dif_pos (show x ∈ stab W.1 from W.2.2)]]`. Rewrite using `[← Finset.sum_subtype (Finset.univ.filter fun W : Submodule F (Fin n → F) => W ≠ ⊤ ∧ ∀ v ∈ W, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W) (fun W => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) (resPsi S x), Finset.sum_filter]`. Use `Finset.sum_congr rfl fun W _ => ?_` and prove the remaining obligations. Distinguish the cases in `hx : ∀ v ∈ W, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W`.

Simplify using `only [Finset.mem_range, ne_top_iff_finrank_lt, and_iff_left hx]`. Establish `hx' : x ∉ stab W` using `hx`. Simplify using `[resPsi, hx', hx]`.
-/
theorem psiG_eq_chG_sub_hc (F : Type) [Field F] [Finite F] (S : F[X] → ℂ) (n : ℕ) (x : GL (Fin n) F) :
    psiG S n x = chG S n x - ∑ a ∈ Finset.range n, hc a (n - a) (psiG S a) (fun _ => 1) n x := by
  classical
  haveI : Finite (Submodule F (Fin n → F)) :=
    Finite.of_injective (fun W : Submodule F (Fin n → F) => (W : Set (Fin n → F))) SetLike.coe_injective
  letI := Fintype.ofFinite (Submodule F (Fin n → F))
  show psi S _ _ = S _ - _
  rw [psi_eq, Matrix.charpoly_toLin']
  congr 1
  rw [Finset.sum_congr rfl fun a ha =>
    (finsum_rank_eq_hc S (le_of_lt (Finset.mem_range.1 ha)) x).symm]
  have step : ∀ a : ℕ, ∑ᶠ W : {W : Submodule F (Fin n → F) // Module.finrank F W = a}, resPsi S x W.1 =
      ∑ W : Submodule F (Fin n → F), if Module.finrank F W = a then resPsi S x W else 0 := by
    intro a
    rw [finsum_eq_sum_of_fintype, ← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) _).symm
  simp only [step]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq]
  rw [finsum_eq_sum_of_fintype]
  rw [Finset.sum_congr rfl (g := fun W => resPsi S x W.1) fun W _ => by
    unfold resPsi; rw [dif_pos (show x ∈ stab W.1 from W.2.2)]]
  rw [← Finset.sum_subtype (Finset.univ.filter fun W : Submodule F (Fin n → F) => W ≠ ⊤ ∧ ∀ v ∈ W, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W)
    (fun W => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) (resPsi S x), Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ => ?_
  by_cases hx : ∀ v ∈ W, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W
  · simp only [Finset.mem_range, ne_top_iff_finrank_lt, and_iff_left hx]
  · have hx' : x ∉ stab W := hx
    simp [resPsi, hx', hx]

end GlobalTheory.ShinPsiRec
