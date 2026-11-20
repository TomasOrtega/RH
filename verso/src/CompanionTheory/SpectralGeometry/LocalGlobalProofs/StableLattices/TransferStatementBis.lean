import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeOperatorsSpanAndFaithfulStatement

open CompanionTheory.Rg.Fl
open CompanionTheory.D.gk.admitted (stdPoly word word_nil word_cons)

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeTransfer

section Words

variable {R : Type*} [Ring R]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rw [word_nil, List.prod_nil]`. Consider the case `cons a l ih => rw [word_cons, ih, List.prod_cons, one_mul]`.
-/
theorem word_one (l : List R) : word (1 : R) l = l.prod := by
  induction l with
  | nil => rw [word_nil, List.prod_nil]
  | cons a l ih => rw [word_cons, ih, List.prod_cons, one_mul]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rw [word_nil, hE]`. Consider the case `cons a l ih => rw [word_cons, mul_assoc, ih]`.
-/
theorem word_mul_idem {E : R} (hE : E * E = E) (l : List R) : word E l * E = word E l := by
  induction l with
  | nil => rw [word_nil, hE]
  | cons a l ih => rw [word_cons, mul_assoc, ih]

/- English proof (translation)
Establish `h' : ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (π i)).prod = 0`. Rewrite using `[← h]`. Unfold `CompanionTheory.D.gk.admitted.stdPoly`. Use `Finset.sum_congr rfl fun π _ => ?_` and prove the remaining obligations. Rewrite using `[word_one, zsmul_eq_mul]`.

Establish `hrev : ∀ f : Fin M → R, (List.ofFn f).reverse = List.ofFn fun i => f i.rev`. Introduce `f`. Apply `List.ext_getElem` to reduce the goal to its premises. Simplify using the standard rewrite rules. Introduce `i h1 h2`.

Simplify using `only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn]`. Use `congr 1`. Use `ext`. Simplify using `only [Fin.val_rev]`. Simplify using `only [List.length_reverse, List.length_ofFn] at h1`.

Use linear arithmetic over natural numbers and integers. Establish `hsq : (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin M)) : ℤ) * (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin M)) : ℤ) = 1`. Rewrite using `[← Units.val_mul, Int.units_mul_self, Units.val_one]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun π _ => ?_` and prove the remaining obligations.

Rewrite using `[hrev, smul_smul, Equiv.Perm.sign_mul, Units.val_mul, mul_comm (Equiv.Perm.sign π : ℤ), ← mul_assoc, hsq, one_mul]`. Apply the tactic sequence `all_goals rfl`. Use `_ = (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin M)) : ℤ) • ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign (π * Fin.revPerm) : ℤ) • (List.ofFn fun i => b ((π * Fin.revPerm : Equiv.Perm (Fin M)) i)).prod := by`. Rewrite using `[Finset.smul_sum]`. Use `_ = (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin M)) : ℤ) • ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (π i)).prod := by`.

Use `congr 1`. Conclude with `Equiv.sum_comp (Equiv.mulRight Fin.revPerm) (fun π : Equiv.Perm (Fin M) => (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (π i)).prod)`. Use `_ = 0 := by rw [h', smul_zero]`.
-/
theorem sum_reverse_eq_zero {M : ℕ} (b : Fin M → R) (h : stdPoly (1 : R) b = 0) :
    ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (π i)).reverse.prod = 0 := by
  have h' : ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (π i)).prod = 0 := by
    rw [← h]
    unfold CompanionTheory.D.gk.admitted.stdPoly
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [word_one, zsmul_eq_mul]
  have hrev : ∀ f : Fin M → R, (List.ofFn f).reverse = List.ofFn fun i => f i.rev := by
    intro f
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn]
      congr 1
      ext
      simp only [Fin.val_rev]
      simp only [List.length_reverse, List.length_ofFn] at h1
      omega
  have hsq : (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin M)) : ℤ) *
      (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin M)) : ℤ) = 1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  calc ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (π i)).reverse.prod
      = ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin M)) : ℤ) •
          ((Equiv.Perm.sign (π * Fin.revPerm) : ℤ) •
            (List.ofFn fun i => b ((π * Fin.revPerm : Equiv.Perm (Fin M)) i)).prod) := by
        refine Finset.sum_congr rfl fun π _ => ?_
        rw [hrev, smul_smul, Equiv.Perm.sign_mul, Units.val_mul, mul_comm (Equiv.Perm.sign π : ℤ),
          ← mul_assoc, hsq, one_mul]
        all_goals rfl
    _ = (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin M)) : ℤ) •
          ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign (π * Fin.revPerm) : ℤ) •
            (List.ofFn fun i => b ((π * Fin.revPerm : Equiv.Perm (Fin M)) i)).prod := by
        rw [Finset.smul_sum]
    _ = (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin M)) : ℤ) •
          ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (π i)).prod := by
        congr 1
        exact Equiv.sum_comp (Equiv.mulRight Fin.revPerm)
          (fun π : Equiv.Perm (Fin M) => (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (π i)).prod)
    _ = 0 := by rw [h', smul_zero]

end Words

variable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def phi (K : Subgroup G) (σ : G →* (H →L[ℂ] H)) (v : H) : ((G ⧸ K) →₀ ℂ) →ₗ[ℂ] H :=
  Finsupp.linearCombination ℂ fun x : G ⧸ K => σ (Quotient.out x) v

abbrev dlt (K : Subgroup G) : (G ⧸ K) →₀ ℂ := Finsupp.single ((1 : G) : G ⧸ K) 1

variable {K : Subgroup G} {σ : G →* (H →L[ℂ] H)} {v : H}

/- English proof (translation)
Rewrite using `[phi, Finsupp.linearCombination_single]`. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul K x`. Rewrite using `[hk, map_mul, ContinuousLinearMap.mul_apply, hv k k.2]`.
-/
theorem phi_single (hv : ∀ k ∈ K, σ k v = v) (x : G) (c : ℂ) :
    phi K σ v (Finsupp.single (x : G ⧸ K) c) = c • σ x v := by
  rw [phi, Finsupp.linearCombination_single]
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K x
  rw [hk, map_mul, ContinuousLinearMap.mul_apply, hv k k.2]

/- English proof (translation)
Simplify using `only [CompanionTheory.Rg.Fl.lam, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, MulAction.Quotient.smul_mk, smul_eq_mul]`.
-/
theorem lam_single (g x : G) (c : ℂ) :
    lam K g (Finsupp.single (x : G ⧸ K) c) = Finsupp.single ((g * x : G) : G ⧸ K) c := by
  simp only [CompanionTheory.Rg.Fl.lam, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    MulAction.Quotient.smul_mk, smul_eq_mul]

/- English proof (translation)
Proceed by induction on `f using Finsupp.induction_linear with`. Consider the case `zero => simp only [map_zero]`. Consider the case `add f₁ f₂ h₁ h₂ => simp only [map_add, h₁, h₂]`. Consider the case `single y c`. Take `⟨x, rfl⟩` from `QuotientGroup.mk_surjective y`.

Rewrite using `[lam_single, phi_single hv, phi_single hv, map_mul, ContinuousLinearMap.mul_apply, ContinuousLinearMap.map_smul]`.
-/
theorem phi_lam (hv : ∀ k ∈ K, σ k v = v) (g : G) (f : (G ⧸ K) →₀ ℂ) :
    phi K σ v (lam K g f) = σ g (phi K σ v f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f₁ f₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single y c =>
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [lam_single, phi_single hv, phi_single hv, map_mul, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.map_smul]

/- English proof (translation)
Simplify using `only [dlt]`. Rewrite using `[lam_single, mul_one]`. Use `congr 1`. Conclude with `QuotientGroup.eq.2 (by simpa using K.inv_mem hk)`.
-/
theorem lam_dlt {k : G} (hk : k ∈ K) : lam K k (dlt K) = dlt K := by
  simp only [dlt]
  rw [lam_single, mul_one]
  congr 1
  exact QuotientGroup.eq.2 (by simpa using K.inv_mem hk)

/- English proof (translation)
Establish `hc` using `(Subalgebra.mem_centralizer_iff ℂ).1 h.2 (lam K g) ⟨g, rfl⟩`. Conclude with `congrArg (fun T : Module.End ℂ ((G ⧸ K) →₀ ℂ) => T f) hc`.
-/
theorem hk_comm (h : Hk K) (g : G) (f : (G ⧸ K) →₀ ℂ) :
    lam K g ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) f) = (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (lam K g f) := by
  have hc := (Subalgebra.mem_centralizer_iff ℂ).1 h.2 (lam K g) ⟨g, rfl⟩
  exact congrArg (fun T : Module.End ℂ ((G ⧸ K) →₀ ℂ) => T f) hc

/- English proof (translation)
Introduce `k hk`. Rewrite using `[← phi_lam hv, hk_comm, lam_dlt hk]`.
-/
theorem phi_fixed (hv : ∀ k ∈ K, σ k v = v) (h : Hk K) :
    ∀ k ∈ K, σ k (phi K σ v ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K))) =
      phi K σ v ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)) := by
  intro k hk
  rw [← phi_lam hv, hk_comm, lam_dlt hk]

/- English proof (translation)
Proceed by induction on `f using Finsupp.induction_linear with`. Consider the case `zero => simp only [map_zero]`. Consider the case `add f₁ f₂ h₁ h₂ => simp only [map_add, h₁, h₂]`. Consider the case `single y c`. Take `⟨x, rfl⟩` from `QuotientGroup.mk_surjective y`.

Establish `hd : lam K x (dlt K) = Finsupp.single (x : G ⧸ K) 1`. Simplify using `only [dlt]`. Rewrite using `[lam_single, mul_one]`. Rewrite using `[phi_single (phi_fixed hv h), ← phi_lam hv, hk_comm, hd, ← Finsupp.smul_single_one (x : G ⧸ K) c, LinearMap.map_smul, LinearMap.map_smul]`.
-/
theorem phi_phi (hv : ∀ k ∈ K, σ k v = v) (h : Hk K) (f : (G ⧸ K) →₀ ℂ) :
    phi K σ (phi K σ v ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K))) f =
      phi K σ v ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f₁ f₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single y c =>
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hd : lam K x (dlt K) = Finsupp.single (x : G ⧸ K) 1 := by
      simp only [dlt]
      rw [lam_single, mul_one]
    rw [phi_single (phi_fixed hv h), ← phi_lam hv, hk_comm, hd,
      ← Finsupp.smul_single_one (x : G ⧸ K) c, LinearMap.map_smul, LinearMap.map_smul]

/- English proof (translation)
Establish `hcard : (S.card : ℂ) ≠ 0`. Establish `hmem : (g : G ⧸ K) ∈ S`. Establish `: (g : G ⧸ K) ∈ (↑S : Set (G ⧸ K))`. Rewrite using `[hS]`. Conclude with `MulAction.mem_orbit_self _`.

Conclude with `Finset.mem_coe.1 this`. Conclude with `Nat.cast_ne_zero.2 (Finset.card_pos.2 ⟨_, hmem⟩).ne'`. Establish `hterm : ∀ y ∈ S, E (phi K σ v (Finsupp.single y 1)) = E (σ g v)`. Introduce `y hy`. Establish `hy' : y ∈ MulAction.orbit K (g : G ⧸ K)`.

Rewrite using `[← hS]`. Conclude with `hy`. Take `⟨k, rfl⟩` from `hy'`. Use `show E (phi K σ v (Finsupp.single (((k : G) * g : G) : G ⧸ K) 1)) = E (σ g v)`. Rewrite using `[phi_single hv, one_smul, map_mul, ContinuousLinearMap.mul_apply, hA.2.2 _ _ k.2]`.

Establish `hfix` using `phi_fixed hv (((S.card : ℂ)⁻¹ • T : Hk K))`. Rewrite using `[← hA.2.1 _ hfix, Subalgebra.coe_smul, LinearMap.smul_apply, hT]`. Simplify using `only [map_smul, map_sum]`. Rewrite using `[Finset.sum_congr rfl hterm, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]`.
-/
theorem avg_sigma {E : H →L[ℂ] H} (hA : IsAvg σ K E) (hv : ∀ k ∈ K, σ k v = v) (g : G) (T : Hk K)
    (S : Finset (G ⧸ K)) (hS : (↑S : Set (G ⧸ K)) = MulAction.orbit K (g : G ⧸ K))
    (hT : (T : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K) = ∑ y ∈ S, Finsupp.single y (1 : ℂ)) :
    E (σ g v) = phi K σ v ((((S.card : ℂ)⁻¹ • T : Hk K) : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)) := by
  have hcard : (S.card : ℂ) ≠ 0 := by
    have hmem : (g : G ⧸ K) ∈ S := by
      have : (g : G ⧸ K) ∈ (↑S : Set (G ⧸ K)) := by
        rw [hS]
        exact MulAction.mem_orbit_self _
      exact Finset.mem_coe.1 this
    exact Nat.cast_ne_zero.2 (Finset.card_pos.2 ⟨_, hmem⟩).ne'
  have hterm : ∀ y ∈ S, E (phi K σ v (Finsupp.single y 1)) = E (σ g v) := by
    intro y hy
    have hy' : y ∈ MulAction.orbit K (g : G ⧸ K) := by
      rw [← hS]
      exact hy
    obtain ⟨k, rfl⟩ := hy'
    show E (phi K σ v (Finsupp.single (((k : G) * g : G) : G ⧸ K) 1)) = E (σ g v)
    rw [phi_single hv, one_smul, map_mul,
      ContinuousLinearMap.mul_apply, hA.2.2 _ _ k.2]
  have hfix := phi_fixed hv (((S.card : ℂ)⁻¹ • T : Hk K))
  rw [← hA.2.1 _ hfix, Subalgebra.coe_smul, LinearMap.smul_apply, hT]
  simp only [map_smul, map_sum]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ hcard, one_smul]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil`. Simplify using `only [List.map_nil, word_nil, List.reverse_nil, List.prod_nil, OneMemClass.coe_one, Module.End.one_apply, dlt, phi_single hv, one_smul, map_one, ContinuousLinearMap.one_apply]`. Conclude with `hA.2.1 v hv`. Consider the case `cons g l ih`.

Simplify using `only [List.map_cons, word_cons, ContinuousLinearMap.mul_apply]`. Rewrite using `[ih, hb _ (phi_fixed hv _) g, phi_phi hv]`. Simplify using `only [List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil, mul_one, MulMemClass.coe_mul, Module.End.mul_apply]`.
-/
theorem word_apply {E : H →L[ℂ] H} (hA : IsAvg σ K E) (b : G → Hk K)
    (hb : ∀ (u : H), (∀ k ∈ K, σ k u = u) → ∀ g, E (σ g u) = phi K σ u ((b g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)))
    (hv : ∀ k ∈ K, σ k v = v) (l : List G) :
    word E (l.map fun g => σ g) v =
      phi K σ v ((((l.map b).reverse.prod : Hk K) : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)) := by
  induction l with
  | nil =>
    simp only [List.map_nil, word_nil, List.reverse_nil, List.prod_nil, OneMemClass.coe_one,
      Module.End.one_apply, dlt, phi_single hv, one_smul, map_one, ContinuousLinearMap.one_apply]
    exact hA.2.1 v hv
  | cons g l ih =>
    simp only [List.map_cons, word_cons, ContinuousLinearMap.mul_apply]
    rw [ih, hb _ (phi_fixed hv _) g, phi_phi hv]
    simp only [List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
      MulMemClass.coe_mul, Module.End.mul_apply]

/- English proof (translation)
Introduce `G _ K M hK hPI H _ _ _ σ _ E hA g`. Take `⟨T, hT, -, -⟩` from `GlobalTheory.T.hecke_operators_span_and_faithful G K hK`. Establish `hfin : ∀ x : G, (MulAction.orbit K (x : G ⧸ K)).Finite` using `hK`. Set `S : G → Finset (G ⧸ K)` to `fun x => (hfin x).toFinset`. Establish `hS : ∀ x, (↑(S x) : Set (G ⧸ K)) = MulAction.orbit K (x : G ⧸ K)` using `fun x => (hfin x).coe_toFinset`.

Set `b : G → Hk K` to `fun x => (((S x).card : ℂ)⁻¹ • T x : Hk K)`. Establish `hb : ∀ u : H, (∀ k ∈ K, σ k u = u) → ∀ x, E (σ x u) = phi K σ u ((b x : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K))` using `fun u hu x => avg_sigma hA hu x (T x) (S x) (hS x) (hT x (S x) (hS x))`. Establish `hEE : E * E = E`. Use extensionality with `v`. Conclude with `hA.2.1 (E v) (hA.1 v)`.

Establish `hpoly : stdPoly E (fun i => σ (g i)) * E = stdPoly E (fun i => σ (g i))`. Unfold `CompanionTheory.D.gk.admitted.stdPoly`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun π _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, word_mul_idem hEE]`.

Establish `key : ∀ u : H, (∀ k ∈ K, σ k u = u) → (stdPoly E fun i => σ (g i)) u = 0`. Introduce `u hu`. Set `A : (H →L[ℂ] H) →+ H` to `{ toFun := fun W => W u, map_zero' := rfl, map_add' := fun _ _ => rfl }`. Set `L : Hk K →+ H` to `{ toFun := fun h => phi K σ u ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)), map_zero' := by simp, map_add' := fun x y => by simp [map_add] }`. Establish `hw : ∀ π : Equiv.Perm (Fin M), A (word E (List.ofFn fun i => σ (g (π i)))) = L (List.ofFn fun i => b (g (π i))).reverse.prod`.

Introduce `π`. Use `word_apply hA b hb hu (List.ofFn fun i => g (π i))` as an intermediate fact. Rewrite `this` using `[List.map_ofFn, List.map_ofFn]`. Conclude with `this`. Establish `h0` using `sum_reverse_eq_zero (fun i => b (g i)) (hPI _)`.

Use `show A (stdPoly E fun i => σ (g i)) = 0`. Unfold `CompanionTheory.D.gk.admitted.stdPoly`. Rewrite using `[map_sum]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun π _ => ?_` and prove the remaining obligations.

Rewrite using `[← zsmul_eq_mul, map_zsmul, hw]`. Use `_ = L (∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (g (π i))).reverse.prod) := by`. Rewrite using `[map_sum]`. Simplify using `only [map_zsmul]`. Use `_ = 0 := by rw [h0, map_zero]`.

Use extensionality with `v`. Rewrite using `[ContinuousLinearMap.zero_apply, ← hpoly, ContinuousLinearMap.mul_apply]`. Conclude with `key _ (hA.1 v)`.
-/
theorem stTransfer : StTransfer := by
  intro G _ K M hK hPI H _ _ _ σ _ E hA g
  obtain ⟨T, hT, -, -⟩ := GlobalTheory.T.hecke_operators_span_and_faithful G K hK
  have hfin : ∀ x : G, (MulAction.orbit K (x : G ⧸ K)).Finite := hK
  let S : G → Finset (G ⧸ K) := fun x => (hfin x).toFinset
  have hS : ∀ x, (↑(S x) : Set (G ⧸ K)) = MulAction.orbit K (x : G ⧸ K) :=
    fun x => (hfin x).coe_toFinset
  let b : G → Hk K := fun x => (((S x).card : ℂ)⁻¹ • T x : Hk K)
  have hb : ∀ u : H, (∀ k ∈ K, σ k u = u) → ∀ x, E (σ x u) =
      phi K σ u ((b x : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)) :=
    fun u hu x => avg_sigma hA hu x (T x) (S x) (hS x) (hT x (S x) (hS x))
  have hEE : E * E = E := by
    ext v
    exact hA.2.1 (E v) (hA.1 v)
  have hpoly : stdPoly E (fun i => σ (g i)) * E = stdPoly E (fun i => σ (g i)) := by
    unfold CompanionTheory.D.gk.admitted.stdPoly
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [mul_assoc, word_mul_idem hEE]
  have key : ∀ u : H, (∀ k ∈ K, σ k u = u) → (stdPoly E fun i => σ (g i)) u = 0 := by
    intro u hu
    let A : (H →L[ℂ] H) →+ H :=
      { toFun := fun W => W u, map_zero' := rfl, map_add' := fun _ _ => rfl }
    let L : Hk K →+ H :=
      { toFun := fun h => phi K σ u ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)),
        map_zero' := by simp,
        map_add' := fun x y => by simp [map_add] }
    have hw : ∀ π : Equiv.Perm (Fin M), A (word E (List.ofFn fun i => σ (g (π i)))) =
        L (List.ofFn fun i => b (g (π i))).reverse.prod := by
      intro π
      have := word_apply hA b hb hu (List.ofFn fun i => g (π i))
      rw [List.map_ofFn, List.map_ofFn] at this
      exact this
    have h0 := sum_reverse_eq_zero (fun i => b (g i)) (hPI _)
    show A (stdPoly E fun i => σ (g i)) = 0
    unfold CompanionTheory.D.gk.admitted.stdPoly
    rw [map_sum]
    calc ∑ π : Equiv.Perm (Fin M), A (↑↑(Equiv.Perm.sign π) * word E (List.ofFn fun i => σ (g (π i))))
        = ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • L (List.ofFn fun i => b (g (π i))).reverse.prod := by
          refine Finset.sum_congr rfl fun π _ => ?_
          rw [← zsmul_eq_mul, map_zsmul, hw]
      _ = L (∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (g (π i))).reverse.prod) := by
          rw [map_sum]
          simp only [map_zsmul]
      _ = 0 := by rw [h0, map_zero]
  ext v
  rw [ContinuousLinearMap.zero_apply, ← hpoly, ContinuousLinearMap.mul_apply]
  exact key _ (hA.1 v)

end GlobalTheory.CompanionTheory.HeckeTransfer
