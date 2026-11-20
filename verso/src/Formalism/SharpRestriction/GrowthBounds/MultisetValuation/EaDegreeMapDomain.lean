import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.GainOfCapacityLoss

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Res

variable {ι κ R : Type} [CommRing R] (f : κ → ι)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ea_coeff_resV (a : MvPowerSeries ι R) (n : κ →₀ ℕ) :
    MvPowerSeries.coeff n (resV f a) = MvPowerSeries.coeff (n.mapDomain f) a := rfl

variable {f} (hf : Function.Injective f)

include hf

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[ea_coeff_resV, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]`. Repeatedly rewrite using `[ea_coeff_resV]`. Use `symm`. Use `Finset.sum_nbij' (fun q => (q.1.mapDomain f, q.2.mapDomain f)) (fun q => (q.1.comapDomain f hf.injOn, q.2.comapDomain f hf.injOn)) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations.

Introduce `q hq`. Rewrite `hq`, the goal using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Rewrite using `[← Finsupp.mapDomain_add, hq]`. Introduce `q hq`. Rewrite `hq`, the goal using `[Finset.HasAntidiagonal.mem_antidiagonal]`.

Rewrite using `[← Finsupp.comapDomain_add_of_injective hf, hq, Finsupp.comapDomain_mapDomain f hf]`. Introduce `q _`. Simplify using `only [Finsupp.comapDomain_mapDomain f hf]`. Introduce `q hq`. Rewrite `hq` using `[Finset.HasAntidiagonal.mem_antidiagonal]`.

Establish `hs : ∀ m : ι →₀ ℕ, m ≤ n.mapDomain f → (↑m.support : Set ι) ⊆ Set.range f`. Introduce `m hm x hx`. Establish `hx' : x ∈ (n.mapDomain f).support`. Rewrite `hx` using `[Finset.mem_coe, Finsupp.mem_support_iff]`. Rewrite using `[Finsupp.mem_support_iff]`.

Use `hm x` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨y, -, rfl⟩` from `Finset.mem_image.1 (Finsupp.mapDomain_support hx')`. Conclude with `⟨y, rfl⟩`. Establish `h1 : q.1 ≤ n.mapDomain f` using `hq ▸ le_self_add`.

Establish `h2 : q.2 ≤ n.mapDomain f` using `hq ▸ le_add_self`. Use `ext1`. Conclude with `Finsupp.mapDomain_comapDomain f hf _ (hs _ h1)`. Conclude with `Finsupp.mapDomain_comapDomain f hf _ (hs _ h2)`. Introduce `q _`.

Both sides reduce to the same expression.
-/
theorem ea_resV_mul (a b : MvPowerSeries ι R) : resV f (a * b) = resV f a * resV f b := by
  classical
  ext n
  rw [ea_coeff_resV, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  simp_rw [ea_coeff_resV]
  symm
  refine Finset.sum_nbij' (fun q => (q.1.mapDomain f, q.2.mapDomain f))
    (fun q => (q.1.comapDomain f hf.injOn, q.2.comapDomain f hf.injOn)) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq ⊢
    rw [← Finsupp.mapDomain_add, hq]
  · intro q hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq ⊢
    rw [← Finsupp.comapDomain_add_of_injective hf, hq, Finsupp.comapDomain_mapDomain f hf]
  · intro q _
    simp only [Finsupp.comapDomain_mapDomain f hf]
  · intro q hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have hs : ∀ m : ι →₀ ℕ, m ≤ n.mapDomain f → (↑m.support : Set ι) ⊆ Set.range f := by
      intro m hm x hx
      have hx' : x ∈ (n.mapDomain f).support := by
        rw [Finset.mem_coe, Finsupp.mem_support_iff] at hx
        rw [Finsupp.mem_support_iff]
        have := hm x
        omega
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx')
      exact ⟨y, rfl⟩
    have h1 : q.1 ≤ n.mapDomain f := hq ▸ le_self_add
    have h2 : q.2 ≤ n.mapDomain f := hq ▸ le_add_self
    ext1
    · exact Finsupp.mapDomain_comapDomain f hf _ (hs _ h1)
    · exact Finsupp.mapDomain_comapDomain f hf _ (hs _ h2)
  · intro q _
    rfl

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[ea_coeff_resV, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]`. Establish `h : n.mapDomain f = 0 ↔ n = 0`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `Finsupp.mapDomain_injective hf (by rw [h, Finsupp.mapDomain_zero])`. Introduce and unpack `rfl`. Conclude with `Finsupp.mapDomain_zero`. Distinguish the cases in `hn : n = 0`. Rewrite using `[if_pos (h.2 hn), if_pos hn]`.

Rewrite using `[if_neg (mt h.1 hn), if_neg hn]`.
-/
theorem ea_resV_C (c : R) : resV f (MvPowerSeries.C c : MvPowerSeries ι R) = MvPowerSeries.C c := by
  classical
  ext n
  rw [ea_coeff_resV, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]
  have h : n.mapDomain f = 0 ↔ n = 0 := by
    constructor
    · intro h
      exact Finsupp.mapDomain_injective hf (by rw [h, Finsupp.mapDomain_zero])
    · rintro rfl
      exact Finsupp.mapDomain_zero
  by_cases hn : n = 0
  · rw [if_pos (h.2 hn), if_pos hn]
  · rw [if_neg (mt h.1 hn), if_neg hn]

def ea_resHom : MvPowerSeries ι R →+* MvPowerSeries κ R where
  toFun := resV f
  map_one' := by
    have := ea_resV_C hf (1 : R)
    rwa [map_one, map_one] at this
  map_mul' := ea_resV_mul hf
  map_zero' := rfl
  map_add' _ _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ea_resHom_apply (a : MvPowerSeries ι R) : ea_resHom hf a = resV f a := rfl

omit hf in
/- English proof (translation)
Use extensionality with `n`. Rewrite using `[ea_coeff_resV]`. Simplify using `only [atPi, MvPowerSeries.coeff_apply, resV, Finsupp.degree_mapDomain]`.
-/
theorem ea_resV_atPi (vp : R) (a : MvPowerSeries ι R) : resV f (atPi vp a) = atPi vp (resV f a) := by
  ext n
  rw [ea_coeff_resV]
  simp only [atPi, MvPowerSeries.coeff_apply, resV, Finsupp.degree_mapDomain]

end Res

/- English proof (translation)
Establish `h : (fun x => MvPowerSeries.C vp * (MvPowerSeries.X x : MvPowerSeries σ R)) = (Function.const σ vp) • MvPowerSeries.X`. Use function extensionality and compare the values at `x`. Simplify using `[MvPowerSeries.smul_eq_C_mul]`. Rewrite using `[h, ← MvPowerSeries.rescale_eq_subst]`. Use extensionality with `n`.

Rewrite using `[MvPowerSeries.coeff_rescale]`. Simplify using `only [Finsupp.prod, Function.const_apply, Finset.prod_pow_eq_pow_sum, atPi, MvPowerSeries.coeff_apply, Finsupp.degree]`. Both sides reduce to the same expression.
-/
theorem ea_atPi_subst {σ R : Type} [CommRing R] (vp : R) (a : MvPowerSeries σ R) :
    MvPowerSeries.subst (fun x => MvPowerSeries.C vp * (MvPowerSeries.X x : MvPowerSeries σ R)) a = atPi vp a := by
  have h : (fun x => MvPowerSeries.C vp * (MvPowerSeries.X x : MvPowerSeries σ R)) =
      (Function.const σ vp) • MvPowerSeries.X := by
    funext x
    simp [MvPowerSeries.smul_eq_C_mul]
  rw [h, ← MvPowerSeries.rescale_eq_subst]
  ext n
  rw [MvPowerSeries.coeff_rescale]
  simp only [Finsupp.prod, Function.const_apply, Finset.prod_pow_eq_pow_sum, atPi,
    MvPowerSeries.coeff_apply, Finsupp.degree]
  rfl

/- English proof (translation)
Substitute `hn` using the available equality. Establish `hd : d ≤ (s : ℕ) + 2 * ν * d` using `le_add_left (Nat.le_mul_of_pos_left d (by have := NeZero.pos ν; omega))`. Use `show ((((s : ℕ) + 2 * ν * d - d) % (2 * ν) : ℕ) : ZMod (2 * ν)) = ((s : ℕ) : ZMod (2 * ν)) - (d : ZMod (2 * ν))`. Establish `h0 : ((2 * ν : ℕ) : ZMod (2 * ν)) = 0` using `ZMod.natCast_self _`. Rewrite using `[ZMod.natCast_mod, Nat.cast_sub hd]`.

Move the coercions through the operations in `at h0 ⊢`. Rewrite using `[h0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ea_eS_posSub {n' ν : ℕ} [NeZero ν] (hn : n' = 2 * ν) (s : Fin n') (d : ℕ) :
    ea_eS hn (posSub s d) = ea_eS hn s - (d : ZMod (2 * ν)) := by
  subst hn
  have hd : d ≤ (s : ℕ) + 2 * ν * d :=
    le_add_left (Nat.le_mul_of_pos_left d (by have := NeZero.pos ν; omega))
  show ((((s : ℕ) + 2 * ν * d - d) % (2 * ν) : ℕ) : ZMod (2 * ν)) = ((s : ℕ) : ZMod (2 * ν)) - (d : ZMod (2 * ν))
  have h0 : ((2 * ν : ℕ) : ZMod (2 * ν)) = 0 := ZMod.natCast_self _
  rw [ZMod.natCast_mod, Nat.cast_sub hd]
  push_cast at h0 ⊢
  rw [h0]
  ring

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

/- English proof (translation)
Introduce `y z h`. Simplify using `only [ea_eps, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at h`. Take `⟨h1, h2, h3⟩` from `h`. Conclude with `Prod.ext ((ea_e X v).symm.injective h1) (Prod.ext h2 h3)`.
-/
theorem ea_eps_inj (v : X.Pl) (j : ℕ) : Function.Injective (ea_eps X v j) := by
  intro y z h
  simp only [ea_eps, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact Prod.ext ((ea_e X v).symm.injective h1) (Prod.ext h2 h3)

/- English proof (translation)
Establish `key : ∀ l : ℕ, ea_eps X v j (ea_e X v s - 2 * (l : ZMod _), a, b) = (⟨v, (posSub s (2 * l), a, b)⟩ : X.ZA j)`. Introduce `l`. Simplify using `only [ea_eps, Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and, and_true]`. Rewrite using `[Equiv.symm_apply_eq]`. Simplify using `only [ea_e]`.

Rewrite using `[ea_eS_posSub]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use extensionality with `n`. Rewrite using `[ea_coeff_resV]`.

Simplify using `only [Sys.sSA, Formalism.InvariantFactorPaths.G7.sPos, MvPowerSeries.coeff_apply, Finsupp.degree_mapDomain]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Establish `hs : (Finsupp.single (⟨v, (posSub s (2 * l), a, b)⟩ : X.ZA j) (p ^ (2 * l))) = Finsupp.mapDomain (ea_eps X v j) (Finsupp.single (ea_e X v s - 2 * (l : ZMod _), (a, b)) ((p ^ 2) ^ l))`. Rewrite using `[Finsupp.mapDomain_single, key l, pow_mul]`. Establish `hiff : Finsupp.mapDomain (ea_eps X v j) n = Finsupp.single (⟨v, (posSub s (2 * l), a, b)⟩ : X.ZA j) (p ^ (2 * l)) ↔ n = Finsupp.single (ea_e X v s - 2 * (l : ZMod _), (a, b)) ((p ^ 2) ^ l)`.

Rewrite using `[hs]`. Conclude with `(Finsupp.mapDomain_injective (ea_eps_inj X v j)).eq_iff`. Distinguish the cases in `h : n = Finsupp.single (ea_e X v s - 2 * (l : ZMod _), (a, b)) ((p ^ 2) ^ l)`. Rewrite using `[if_pos (hiff.2 h), if_pos h]`. Rewrite using `[if_neg (mt hiff.1 h), if_neg h]`.
-/
theorem ea_res_sSA (K' : Type) [Field K'] (v : X.Pl) (j : ℕ) (s : Fin (X.G.P.n' v)) (a : Fin (NN X.G.P.m X.t j))
    (b : Fin (NN X.G.P.m X.t (j + 1))) :
    resV (ea_eps X v j) (X.sSA K' j v s a b) = Formalism.InvariantFactorPaths.G7.sPos p (ea_e X v s) (a, b) := by
  classical
  have key : ∀ l : ℕ, ea_eps X v j (ea_e X v s - 2 * (l : ZMod _), a, b) =
      (⟨v, (posSub s (2 * l), a, b)⟩ : X.ZA j) := by
    intro l
    simp only [ea_eps, Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and, and_true]
    rw [Equiv.symm_apply_eq]
    simp only [ea_e]
    rw [ea_eS_posSub]
    push_cast
    ring
  ext n
  rw [ea_coeff_resV]
  simp only [Sys.sSA, Formalism.InvariantFactorPaths.G7.sPos, MvPowerSeries.coeff_apply, Finsupp.degree_mapDomain]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hs : (Finsupp.single (⟨v, (posSub s (2 * l), a, b)⟩ : X.ZA j) (p ^ (2 * l))) =
      Finsupp.mapDomain (ea_eps X v j) (Finsupp.single (ea_e X v s - 2 * (l : ZMod _), (a, b)) ((p ^ 2) ^ l)) := by
    rw [Finsupp.mapDomain_single, key l, pow_mul]
  have hiff : Finsupp.mapDomain (ea_eps X v j) n = Finsupp.single (⟨v, (posSub s (2 * l), a, b)⟩ : X.ZA j) (p ^ (2 * l)) ↔
      n = Finsupp.single (ea_e X v s - 2 * (l : ZMod _), (a, b)) ((p ^ 2) ^ l) := by
    rw [hs]
    exact (Finsupp.mapDomain_injective (ea_eps_inj X v j)).eq_iff
  by_cases h : n = Finsupp.single (ea_e X v s - 2 * (l : ZMod _), (a, b)) ((p ^ 2) ^ l)
  · rw [if_pos (hiff.2 h), if_pos h]
  · rw [if_neg (mt hiff.1 h), if_neg h]

/- English proof (translation)
Rewrite using `[← ea_resHom_apply (ea_eps_inj X v j)]`. Simplify using `only [Sys.hhA, map_sum, map_mul, map_pow, ea_resHom_apply, ea_resV_C (ea_eps_inj X v j), ea_res_sSA]`. Simplify using `only [Formalism.InvariantFactorPaths.G7.hhS, Fintype.sum_prod_type]`. Use `Fintype.sum_equiv (ea_e X v) _ _ (fun s => ?_)` and prove the remaining obligations. Rewrite using `[Equiv.symm_apply_apply]`.

Simplify using `only [ea_e, ea_eS_posAdd, Nat.cast_one]`.
-/
theorem ea_res_hhA (K' : Type) [Field K'] (v : X.Pl) (j : ℕ) (u : Fin (X.G.P.n' v) → K') :
    resV (ea_eps X v j) (X.hhA K' j v u) = Formalism.InvariantFactorPaths.G7.hhS p fun s => u ((ea_e X v).symm s) := by
  rw [← ea_resHom_apply (ea_eps_inj X v j)]
  simp only [Sys.hhA, map_sum, map_mul, map_pow, ea_resHom_apply, ea_resV_C (ea_eps_inj X v j),
    ea_res_sSA]
  simp only [Formalism.InvariantFactorPaths.G7.hhS, Fintype.sum_prod_type]
  refine Fintype.sum_equiv (ea_e X v) _ _ (fun s => ?_)
  rw [Equiv.symm_apply_apply]
  simp only [ea_e, ea_eS_posAdd, Nat.cast_one]

/- English proof (translation)
Introduce `v j K' _ _ vp u F hF`. Take `⟨g, hg, hc⟩` from `hF`. Rewrite using `[ea_atPi_subst, ← ea_resV_atPi, ← ea_res_hhA]`. Use `⟨fun i => resV (ea_eps X v j) (g i), fun i n => ?_, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[ea_coeff_resV]`.

Conclude with `hg i _`. Rewrite using `[ea_coeff_resV, hc, Finsupp.degree_mapDomain]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [← ea_resHom_apply (ea_eps_inj X v j), ← map_pow, ← map_mul]`. Rewrite using `[ea_resHom_apply, ea_coeff_resV]`.
-/
theorem ea_brClass : ea_BrClass X := by
  intro v j K' _ _ vp u F hF
  obtain ⟨g, hg, hc⟩ := hF
  rw [ea_atPi_subst, ← ea_resV_atPi, ← ea_res_hhA]
  refine ⟨fun i => resV (ea_eps X v j) (g i), fun i n => ?_, fun n => ?_⟩
  · rw [ea_coeff_resV]
    exact hg i _
  · rw [ea_coeff_resV, hc, Finsupp.degree_mapDomain]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [← ea_resHom_apply (ea_eps_inj X v j), ← map_pow, ← map_mul]
    rw [ea_resHom_apply, ea_coeff_resV]

end Formalism.MainNotions.FormalGroupSystem.Pf
