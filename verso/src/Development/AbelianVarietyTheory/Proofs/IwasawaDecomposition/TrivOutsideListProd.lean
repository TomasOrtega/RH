import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompOfOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTrivOutsideLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitPlaceWPlGw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlacesInjective
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceProjectionEqZeroOfPlaceComponentEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgHomEqOrConj
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockLiftActionOnPrincipalCongruenceFixedVectors
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftStandardGroup

open ReciprocityTheory.Aut

def bz (r n p : ℕ) (γ : GL (Fin r) (ZMod p)) : Matrix (Fin n) (Fin n) ℤ := fun a b =>
  if hab : a.val < r ∧ b.val < r then
    ((((γ : Matrix (Fin r) (Fin r) (ZMod p)) ⟨a.val, hab.1⟩ ⟨b.val, hab.2⟩).val : ℕ) : ℤ)
  else if a = b then 1 else 0

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[GlobalTheory.SerSys.BlockLift.bm_apply]`. Simplify using `only [Matrix.map_apply, bz]`. Apply the tactic sequence `split_ifs <;> simp [ZMod.natCast_zmod_val]`.
-/
theorem bz_map_zmod (r t p : ℕ) [Fact p.Prime] (γ : GL (Fin r) (ZMod p)) :
    (bz r (r + t) p γ).map (Int.cast : ℤ → ZMod p) = GlobalTheory.SerSys.BlockLift.bm r t γ := by
  ext a b
  rw [GlobalTheory.SerSys.BlockLift.bm_apply]
  simp only [Matrix.map_apply, bz]
  split_ifs <;> simp [ZMod.natCast_zmod_val]

/- English proof (translation)
Establish `hu` using `(Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.SerSys.BlockLift.bm_isUnit r t γ)`. Introduce `h0`. Establish `e : (((bz r (r + t) p γ).det : ℤ) : ZMod p) = (GlobalTheory.SerSys.BlockLift.bm r t γ).det`. Rewrite using `[← bz_map_zmod]`. Conclude with `RingHom.map_det (Int.castRingHom (ZMod p)) _`.

Rewrite `h0` using `[e]`. Conclude with `hu.ne_zero h0`.
-/
theorem bz_det_ne (r t p : ℕ) [Fact p.Prime] (γ : GL (Fin r) (ZMod p)) :
    (((bz r (r + t) p γ).det : ℤ) : ZMod p) ≠ 0 := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.SerSys.BlockLift.bm_isUnit r t γ)
  intro h0
  have e : (((bz r (r + t) p γ).det : ℤ) : ZMod p) = (GlobalTheory.SerSys.BlockLift.bm r t γ).det := by
    rw [← bz_map_zmod]
    exact RingHom.map_det (Int.castRingHom (ZMod p)) _
  rw [e] at h0
  exact hu.ne_zero h0

section Local

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

/- English proof (translation)
Establish `h` using `s.split_le_one (m : 𝓞 L)`. Simplify using `using h`.
-/
theorem val_intCast_le_one (s : SplitPlace L) (m : ℤ) :
    Valued.v ((m : s.v.adicCompletion (maximalRealSubfield L))) ≤ 1 := by
  have h := s.split_le_one (m : 𝓞 L)
  simpa using h

/- English proof (translation)
Use `set u : ℤ := (((m : ZMod p)⁻¹).val : ℤ) with hu`. Establish `h1 : (((m * u - 1 : ℤ)) : ZMod p) = 0`. Rewrite using `[hu]`. Use `push_cast`. Rewrite using `[ZMod.natCast_zmod_val, mul_inv_cancel₀ hm, sub_self]`.

Take `⟨c, hc⟩` from `(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h1`. Establish `e : ((m : s.v.adicCompletion (maximalRealSubfield L)) * (u : s.v.adicCompletion (maximalRealSubfield L))) = 1 + (p : s.v.adicCompletion (maximalRealSubfield L)) * (c : s.v.adicCompletion (maximalRealSubfield L))`. Establish `: (m * u : ℤ) = 1 + (p : ℤ) * c` using `by linarith`. Conclude with `this` after adjusting the coercions. Establish `h2 : Valued.v ((p : s.v.adicCompletion (maximalRealSubfield L)) * (c : s.v.adicCompletion (maximalRealSubfield L))) < 1`.

Rewrite using `[map_mul]`. Conclude with `mul_lt_one_of_lt_of_le hp (val_intCast_le_one s c)`. Establish `h3 : Valued.v ((m : s.v.adicCompletion (maximalRealSubfield L)) * (u : s.v.adicCompletion (maximalRealSubfield L))) = 1`. Rewrite using `[e]`. Conclude with `Valuation.map_one_add_of_lt _ h2`.

Apply `le_antisymm (val_intCast_le_one s m)` to reduce the goal to its premises. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `h4` using `mul_lt_one_of_lt_of_le hlt (val_intCast_le_one s u)`. Rewrite `h4` using `[← map_mul, h3]`.

Conclude with `lt_irrefl _ h4`.
-/
theorem val_intCast_eq_one (s : SplitPlace L) {p : ℕ} [Fact p.Prime]
    (hp : Valued.v ((p : s.v.adicCompletion (maximalRealSubfield L))) < 1) (m : ℤ) (hm : (m : ZMod p) ≠ 0) :
    Valued.v ((m : s.v.adicCompletion (maximalRealSubfield L))) = 1 := by
  set u : ℤ := (((m : ZMod p)⁻¹).val : ℤ) with hu
  have h1 : (((m * u - 1 : ℤ)) : ZMod p) = 0 := by
    rw [hu]
    push_cast
    rw [ZMod.natCast_zmod_val, mul_inv_cancel₀ hm, sub_self]
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h1
  have e : ((m : s.v.adicCompletion (maximalRealSubfield L)) * (u : s.v.adicCompletion (maximalRealSubfield L))) =
      1 + (p : s.v.adicCompletion (maximalRealSubfield L)) * (c : s.v.adicCompletion (maximalRealSubfield L)) := by
    have : (m * u : ℤ) = 1 + (p : ℤ) * c := by linarith
    exact_mod_cast this
  have h2 : Valued.v ((p : s.v.adicCompletion (maximalRealSubfield L)) * (c : s.v.adicCompletion (maximalRealSubfield L))) < 1 := by
    rw [map_mul]
    exact mul_lt_one_of_lt_of_le hp (val_intCast_le_one s c)
  have h3 : Valued.v ((m : s.v.adicCompletion (maximalRealSubfield L)) * (u : s.v.adicCompletion (maximalRealSubfield L))) = 1 := by
    rw [e]
    exact Valuation.map_one_add_of_lt _ h2
  apply le_antisymm (val_intCast_le_one s m)
  by_contra hlt
  push_neg at hlt
  have h4 := mul_lt_one_of_lt_of_le hlt (val_intCast_le_one s u)
  rw [← map_mul, h3] at h4
  exact lt_irrefl _ h4

end Local

end GlobalTheory.LiftStandardGroup

end

namespace GlobalTheory.LiftStandardGroup

open ReciprocityTheory.Aut

section Local2

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Establish `hc : compAt L s'.v (((x : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) a b - (1 : Matrix (Fin n) (Fin n) (AL L)) a b) = 0`. Use `congrFun (congrFun (hx s'.v (by simpa using h)) a) b` as an intermediate fact. Rewrite `this` using `[Matrix.map_apply]`.

Rewrite using `[map_sub, this, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `h0` using `GlobalTheory.SplitProj.proj_eq_zero_of_compAt_eq_zero L s' _ hc`. Rewrite `h0` using `[map_sub, sub_eq_zero]`. Use `show s'.proj (((x : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) a b) = (1 : Matrix (Fin n) (Fin n) (s'.v.adicCompletion (maximalRealSubfield L))) a b`.

Rewrite using `[h0, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem loc_eq_one_of_ne {n : ℕ} (s' : SplitPlace L) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (h : s'.v ≠ v)
    {x : Formalism.AUTREP.GAf L n} (hx : TrivOutside {v} x) : s'.loc n x = 1 := by
  apply Units.ext
  refine Matrix.ext fun a b => ?_
  have hc : compAt L s'.v (((x : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) a b - (1 : Matrix (Fin n) (Fin n) (AL L)) a b) = 0 := by
    have := congrFun (congrFun (hx s'.v (by simpa using h)) a) b
    rw [Matrix.map_apply] at this
    rw [map_sub, this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h0 := GlobalTheory.SplitProj.proj_eq_zero_of_compAt_eq_zero L s' _ hc
  rw [map_sub, sub_eq_zero] at h0
  show s'.proj (((x : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) a b) =
    (1 : Matrix (Fin n) (Fin n) (s'.v.adicCompletion (maximalRealSubfield L))) a b
  rw [h0, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Use `set M : Matrix (Fin (r + t)) (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)) := (bz r (r + t) p γ).map (Int.cast : ℤ → s.v.adicCompletion (maximalRealSubfield L)) with hM`. Establish `hdetM : M.det = (((bz r (r + t) p γ).det : ℤ) : s.v.adicCompletion (maximalRealSubfield L))` using `(RingHom.map_det (Int.castRingHom (s.v.adicCompletion (maximalRealSubfield L))) _).symm`. Establish `hv : Valued.v M.det = 1`. Rewrite using `[hdetM]`. Conclude with `val_intCast_eq_one s hp _ (bz_det_ne r t p γ)`.

Establish `hne : M.det ≠ 0`. Introduce `h0`. Rewrite `hv` using `[h0, map_zero]`. Conclude with `zero_ne_one hv`. Use `set h : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)) := Matrix.GeneralLinearGroup.mkOfDetNeZero M hne with hh`.

Establish `hval : (h : Matrix (Fin (r + t)) (Fin (r + t)) _) = M` using `rfl`. Take `⟨x, hx1, hx2⟩` from `GlobalTheory.SplitSec.exists_trivOutside_loc L (r + t) s h`. Establish `hint : ∀ a b, Valued.v (M a b) ≤ 1` using `fun a b => by`. Rewrite using `[hM, Matrix.map_apply]`. Conclude with `val_intCast_le_one s _`.

Establish `hinvint : ∀ a b, Valued.v ((M⁻¹ : Matrix (Fin (r + t)) (Fin (r + t)) _) a b) ≤ 1`. Introduce `a b`. Establish `hadj : M.adjugate = ((bz r (r + t) p γ).adjugate).map (Int.cast : ℤ → s.v.adicCompletion (maximalRealSubfield L))` using `(RingHom.map_adjugate (Int.castRingHom (s.v.adicCompletion (maximalRealSubfield L))) _).symm`. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, hadj, Matrix.map_apply, smul_eq_mul, map_mul, map_inv₀, hv, inv_one, one_mul]`. Conclude with `val_intCast_le_one s _`.

Use `⟨x, hx1, ?_, ?_⟩` and prove the remaining obligations. Use `GlobalTheory.HeckeStdFacts.mem_Umax_of_loc s x hx1 ?_ ?_` and prove the remaining obligations. Introduce `a b`. Rewrite using `[hx2, hval]`. Conclude with `hint a b`.

Introduce `a b`. Rewrite using `[map_inv, hx2, Matrix.coe_units_inv, hval]`. Conclude with `hinvint a b`. Introduce `a b`. Rewrite using `[hx2, hval, hM]`.

Distinguish the cases in `hab : a.val < r ∧ b.val < r`. Rewrite using `[dif_pos hab, Matrix.map_apply]`. Simplify using `[bz, dif_pos hab]`. Rewrite using `[dif_neg hab, Matrix.map_apply]`. Simplify using `only [bz, dif_neg hab]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem exists_local (s : SplitPlace L) (r t p : ℕ) [Fact p.Prime]
    (hp : Valued.v ((p : s.v.adicCompletion (maximalRealSubfield L))) < 1) (γ : GL (Fin r) (ZMod p)) :
    ∃ x : Formalism.AUTREP.GAf L (r + t), TrivOutside {s.v} x ∧ x ∈ Umax L (r + t) ∧
      GlobalTheory.PendOf.IsLiftAt s r p γ (s.loc (r + t) x) := by
  set M : Matrix (Fin (r + t)) (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)) :=
    (bz r (r + t) p γ).map (Int.cast : ℤ → s.v.adicCompletion (maximalRealSubfield L)) with hM
  have hdetM : M.det = (((bz r (r + t) p γ).det : ℤ) : s.v.adicCompletion (maximalRealSubfield L)) :=
    (RingHom.map_det (Int.castRingHom (s.v.adicCompletion (maximalRealSubfield L))) _).symm
  have hv : Valued.v M.det = 1 := by
    rw [hdetM]; exact val_intCast_eq_one s hp _ (bz_det_ne r t p γ)
  have hne : M.det ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact zero_ne_one hv
  set h : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)) :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero M hne with hh
  have hval : (h : Matrix (Fin (r + t)) (Fin (r + t)) _) = M := rfl
  obtain ⟨x, hx1, hx2⟩ := GlobalTheory.SplitSec.exists_trivOutside_loc L (r + t) s h
  have hint : ∀ a b, Valued.v (M a b) ≤ 1 := fun a b => by
    rw [hM, Matrix.map_apply]; exact val_intCast_le_one s _
  have hinvint : ∀ a b, Valued.v ((M⁻¹ : Matrix (Fin (r + t)) (Fin (r + t)) _) a b) ≤ 1 := by
    intro a b
    have hadj : M.adjugate = ((bz r (r + t) p γ).adjugate).map (Int.cast : ℤ → s.v.adicCompletion (maximalRealSubfield L)) :=
      (RingHom.map_adjugate (Int.castRingHom (s.v.adicCompletion (maximalRealSubfield L))) _).symm
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, hadj, Matrix.map_apply, smul_eq_mul, map_mul, map_inv₀, hv,
      inv_one, one_mul]
    exact val_intCast_le_one s _
  refine ⟨x, hx1, ?_, ?_⟩
  · refine GlobalTheory.HeckeStdFacts.mem_Umax_of_loc s x hx1 ?_ ?_
    · intro a b; rw [hx2, hval]; exact hint a b
    · intro a b; rw [map_inv, hx2, Matrix.coe_units_inv, hval]; exact hinvint a b
  · intro a b
    rw [hx2, hval, hM]
    by_cases hab : a.val < r ∧ b.val < r
    · rw [dif_pos hab, Matrix.map_apply]
      simp [bz, dif_pos hab]
    · rw [dif_neg hab, Matrix.map_apply]
      simp only [bz, dif_neg hab]
      split_ifs <;> simp

end Local2

end GlobalTheory.LiftStandardGroup

namespace GlobalTheory.LiftStandardGroup

open ReciprocityTheory.Aut

/- English proof (translation)
The claim follows from `| [], _, hm, _ => absurd hm List.not_mem_nil | b :: l, hnd, hm, h1 => by rw [List.map_cons, List.prod_cons] by_cases hb : b = a · subst hb rw [List.prod_eq_one, mul_one] intro y hy obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy exact h1 c (List.mem_cons_of_mem _ hc) (fun e => (List.nod …`.
-/
theorem list_prod_map_eq {ι G : Type} [Monoid G] (f : ι → G) (a : ι) :
    ∀ l : List ι, l.Nodup → a ∈ l → (∀ b ∈ l, b ≠ a → f b = 1) → (l.map f).prod = f a
  | [], _, hm, _ => absurd hm List.not_mem_nil
  | b :: l, hnd, hm, h1 => by
    rw [List.map_cons, List.prod_cons]
    by_cases hb : b = a
    · subst hb
      rw [List.prod_eq_one, mul_one]
      intro y hy
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
      exact h1 c (List.mem_cons_of_mem _ hc) (fun e => (List.nodup_cons.1 hnd).1 (e ▸ hc))
    · rw [h1 b (by simp) hb, one_mul]
      exact list_prod_map_eq f a l (List.nodup_cons.1 hnd).2 ((List.mem_cons.1 hm).resolve_left (Ne.symm hb))
        (fun c hc => h1 c (List.mem_cons_of_mem _ hc))

/- English proof (translation)
The claim follows from `| [], _ => by rw [List.prod_nil]; exact GlobalTheory.HeckeStdFacts.triv_one | x :: l, h => by rw [List.prod_cons] exact GlobalTheory.HeckeStdFacts.triv_mul (h x (by simp)) (trivOutside_list_prod l fun y hy => h y (List.mem_cons_of_mem _ hy))`.
-/
theorem trivOutside_list_prod {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} :
    ∀ l : List (Formalism.AUTREP.GAf L n), (∀ x ∈ l, TrivOutside T x) → TrivOutside T l.prod
  | [], _ => by rw [List.prod_nil]; exact GlobalTheory.HeckeStdFacts.triv_one
  | x :: l, h => by
    rw [List.prod_cons]
    exact GlobalTheory.HeckeStdFacts.triv_mul (h x (by simp)) (trivOutside_list_prod l fun y hy => h y (List.mem_cons_of_mem _ hy))

/- English proof (translation)
Introduce `D n hn`. Take `⟨t, rfl⟩` from `Nat.exists_eq_add_of_le hn`. Use `choose s hs using fun kv : (Σ k : Fin 2, D.nd.PlG k) => GlobalTheory.FixedPlaceOverType.exists_splitPlace_w_plGw D kv.1 kv.2`. Establish `hp : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Valued.v (((D.host.g kv.1 : ℕ) : (s kv).v.adicCompletion (maximalRealSubfield D.host.E))) < 1`. Introduce `kv`.

Establish `h0 : ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal` using `D.naut.plGw_over kv.1 kv.2`. Rewrite `h0` using `[← hs kv]`. Establish `h1` using `((s kv).split_mem_ideal _).1 h0`. Simplify using `using h1`. Establish `hloc : ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (γ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))), ∃ x : Formalism.AUTREP.GAf D.host.E (D.R.r + t), TrivOutside {(s kv).v} x ∧ x ∈ Umax D.host.E (D.R.r + t) ∧ GlobalTheory.PendOf.IsLiftAt (s kv) D.R.r (D.host.g kv.1) γ ((s kv).loc (D.R.r + t) x)`.

Introduce `kv γ`. Use `haveI : Fact (D.host.g kv.1).Prime := ⟨D.host.g_prime kv.1⟩`. Conclude with `exists_local (s kv) D.R.r t (D.host.g kv.1) (hp kv) γ`. Use `choose x hx1 hx2 hx3 using hloc`. Establish `hinj : Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv).v)` using `GlobalTheory.PlaceInj.splitPlace_v_injective D (fun k v => s ⟨k, v⟩) (fun k v => hs ⟨k, v⟩)`.

Establish `hgPl : ∀ kv, (s kv).v ∈ GlobalTheory.PendOf.gPl D`. Introduce `kv`. Use `⟨kv, ?_⟩` and prove the remaining obligations. Use `show _ = _`. Rewrite using `[← hs kv]`.

Conclude with `(s kv).w_under`. Use `⟨fun g => ((Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList.map (fun kv => x kv (g kv))).prod, fun g => ⟨?_, ?_⟩, fun g => ?_⟩` and prove the remaining obligations. Apply `trivOutside_list_prod` to reduce the goal to its premises. Introduce `y hy`. Take `⟨kv, -, rfl⟩` from `List.mem_map.1 hy`.

Introduce `w hw`. Conclude with `hx1 kv (g kv) w (fun e => hw (by rw [Set.mem_singleton_iff.1 e]; exact hgPl kv))`. Introduce `kv s' hs'`. Establish `e : s' = s kv` using `GlobalTheory.SplitPlaceExt.eq_of_w_eq D.host.E (s kv) s' (hs'.trans (hs kv).symm)`. Substitute `e` using the available equality.

Rewrite using `[map_list_prod, List.map_map]`. Rewrite using `[list_prod_map_eq _ kv _ (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ _))]`. Conclude with `hx3 kv (g kv)`. Introduce `kv' _ hne`. Conclude with `loc_eq_one_of_ne (s kv) (fun e => hne (hinj e.symm)) (hx1 kv' (g kv'))`.

Apply `Subgroup.list_prod_mem` to reduce the goal to its premises. Introduce `y hy`. Take `⟨kv, -, rfl⟩` from `List.mem_map.1 hy`. Conclude with `hx2 kv (g kv)`.
-/
theorem main : ∀ (D : D7) (n : ℕ), D.R.r ≤ n → ∃ Lf : G0g D.nd → Formalism.AUTREP.GAf D.host.E n,
    GlobalTheory.PendOf.IsTypeGroupBlockLift D n Lf ∧ ∀ g, Lf g ∈ ReciprocityTheory.Aut.Umax D.host.E n := by
  intro D n hn
  classical
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  choose s hs using fun kv : (Σ k : Fin 2, D.nd.PlG k) => GlobalTheory.FixedPlaceOverType.exists_splitPlace_w_plGw D kv.1 kv.2
  have hp : ∀ kv : (Σ k : Fin 2, D.nd.PlG k),
      Valued.v (((D.host.g kv.1 : ℕ) : (s kv).v.adicCompletion (maximalRealSubfield D.host.E))) < 1 := by
    intro kv
    have h0 : ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal := D.naut.plGw_over kv.1 kv.2
    rw [← hs kv] at h0
    have h1 := ((s kv).split_mem_ideal _).1 h0
    simpa using h1
  have hloc : ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (γ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))),
      ∃ x : Formalism.AUTREP.GAf D.host.E (D.R.r + t), TrivOutside {(s kv).v} x ∧ x ∈ Umax D.host.E (D.R.r + t) ∧
        GlobalTheory.PendOf.IsLiftAt (s kv) D.R.r (D.host.g kv.1) γ ((s kv).loc (D.R.r + t) x) := by
    intro kv γ
    haveI : Fact (D.host.g kv.1).Prime := ⟨D.host.g_prime kv.1⟩
    exact exists_local (s kv) D.R.r t (D.host.g kv.1) (hp kv) γ
  choose x hx1 hx2 hx3 using hloc
  have hinj : Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv).v) :=
    GlobalTheory.PlaceInj.splitPlace_v_injective D (fun k v => s ⟨k, v⟩) (fun k v => hs ⟨k, v⟩)
  have hgPl : ∀ kv, (s kv).v ∈ GlobalTheory.PendOf.gPl D := by
    intro kv
    refine ⟨kv, ?_⟩
    show _ = _
    rw [← hs kv]
    exact (s kv).w_under
  refine ⟨fun g => ((Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList.map (fun kv => x kv (g kv))).prod,
    fun g => ⟨?_, ?_⟩, fun g => ?_⟩
  · apply trivOutside_list_prod
    intro y hy
    obtain ⟨kv, -, rfl⟩ := List.mem_map.1 hy
    intro w hw
    exact hx1 kv (g kv) w (fun e => hw (by rw [Set.mem_singleton_iff.1 e]; exact hgPl kv))
  · intro kv s' hs'
    have e : s' = s kv := GlobalTheory.SplitPlaceExt.eq_of_w_eq D.host.E (s kv) s' (hs'.trans (hs kv).symm)
    subst e
    rw [map_list_prod, List.map_map]
    rw [list_prod_map_eq _ kv _ (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ _))]
    · exact hx3 kv (g kv)
    · intro kv' _ hne
      exact loc_eq_one_of_ne (s kv) (fun e => hne (hinj e.symm)) (hx1 kv' (g kv'))
  · apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨kv, -, rfl⟩ := List.mem_map.1 hy
    exact hx2 kv (g kv)

end GlobalTheory.LiftStandardGroup
