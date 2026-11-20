import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints

noncomputable section
open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm
open Formalism.HermitianLatticeCounting.S6

section EmbGen
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}

def frPerp (F : FlagD H r) : Submodule K V where
  carrier := {v | ∀ a, H.B (F.e a) v = 0}
  add_mem' := by
    intro x y hx hy a
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_add, hx a, hy a, add_zero]
  zero_mem' := by
    intro a
    simp
  smul_mem' := by
    intro c x hx a
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [map_smulₛₗ, hx a, smul_zero]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_frPerp (F : FlagD H r) (v : V) : v ∈ frPerp F ↔ ∀ a, H.B (F.e a) v = 0 := Iff.rfl

/- English proof (translation)
The claim follows from `H.nondeg w (fun y => by rw [← H.herm y w, h y, star_zero])`.
-/
theorem B_right_nondeg (H : HermSpace K V) (w : V) (h : ∀ v, H.B v w = 0) : w = 0 :=
  H.nondeg w (fun y => by rw [← H.herm y w, h y, star_zero])

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc`. Establish `hz : c (Fin.last r) = 0`. Establish `h : H.B (∑ a, c a • F.e a) (F.e (Fin.last r)) = 0` using `by rw [hc, map_zero, LinearMap.zero_apply]`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply] at h`.

Rewrite `h` using `[Fin.sum_univ_castSucc]`. Simplify using `only [F.zperp, F.zz, smul_eq_mul, mul_zero, Finset.sum_const_zero, zero_add] at h`. Break down `mul_eq_zero.1 h with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (neg_eq_zero.1 h) F.hT`.

Establish `hc' : ∑ a : Fin r, c a.castSucc • F.e a.castSucc = 0`. Rewrite `hc` using `[Fin.sum_univ_castSucc, hz, zero_smul, add_zero]`. Conclude with `hc`. Establish `hcs` using `Fintype.linearIndependent_iff.1 F.indep (fun a => c a.castSucc) hc'`. Introduce `i`.

Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => exact hz`. Consider the case `cast a => exact hcs a`.
-/
theorem fr_indep (F : FlagD H r) : LinearIndependent K F.e := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hz : c (Fin.last r) = 0 := by
    have h : H.B (∑ a, c a • F.e a) (F.e (Fin.last r)) = 0 := by rw [hc, map_zero, LinearMap.zero_apply]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply] at h
    rw [Fin.sum_univ_castSucc] at h
    simp only [F.zperp, F.zz, smul_eq_mul, mul_zero, Finset.sum_const_zero, zero_add] at h
    rcases mul_eq_zero.1 h with h | h
    · exact h
    · exact absurd (neg_eq_zero.1 h) F.hT
  have hc' : ∑ a : Fin r, c a.castSucc • F.e a.castSucc = 0 := by
    rw [Fin.sum_univ_castSucc, hz, zero_smul, add_zero] at hc
    exact hc
  have hcs := Fintype.linearIndependent_iff.1 F.indep (fun a => c a.castSucc) hc'
  intro i
  induction i using Fin.lastCases with
  | last => exact hz
  | cast a => exact hcs a

def frMap (F : FlagD H r) : V →ₗ[K] (Fin (r + 1) → K) :=
  LinearMap.pi fun a => H.B.flip (F.e a)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem frMap_apply (F : FlagD H r) (v : V) (a : Fin (r + 1)) : frMap F v a = H.B v (F.e a) := rfl

/- English proof (translation)
Use extensionality with `v`. Rewrite using `[LinearMap.mem_ker, mem_frPerp, funext_iff]`. Use `forall_congr' fun a => ?_` and prove the remaining obligations. Rewrite using `[frMap_apply, Pi.zero_apply, ← H.herm (F.e a) v]`. Conclude with `⟨fun h => by rw [← star_star (H.B (F.e a) v), h, star_zero], fun h => by rw [h, star_zero]⟩`.
-/
theorem ker_frMap (F : FlagD H r) : LinearMap.ker (frMap F) = frPerp F := by
  ext v
  rw [LinearMap.mem_ker, mem_frPerp, funext_iff]
  refine forall_congr' fun a => ?_
  rw [frMap_apply, Pi.zero_apply, ← H.herm (F.e a) v]
  exact ⟨fun h => by rw [← star_star (H.B (F.e a) v), h, star_zero], fun h => by rw [h, star_zero]⟩

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨f, hf0, hf⟩` from `Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance`. Use `set c : Fin (r + 1) → K := fun a => f (fun j => if a = j then 1 else 0) with hcdef`. Establish `hfx : ∀ x, f x = ∑ a, x a * c a`. Introduce `x`.

Use `conv_lhs => rw [pi_eq_sum_univ x]`. Simplify using `only [map_sum, map_smul, smul_eq_mul, hcdef]`. Establish `hv : ∀ v, H.B v (∑ a, star (c a) • F.e a) = 0`. Introduce `v`. Establish `h1 : f (frMap F v) = 0`.

Establish `: f (frMap F v) ∈ Submodule.map f (LinearMap.range (frMap F))` using `Submodule.mem_map_of_mem (LinearMap.mem_range_self _ v)`. Rewrite `this` using `[hf]`. Conclude with `(Submodule.mem_bot K).1 this`. Rewrite `h1` using `[hfx]`. Rewrite using `[map_sum]`.

Simplify using `only [map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul]`. Rewrite using `[← h1]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[frMap_apply, mul_comm]`. Establish `hw` using `B_right_nondeg H _ hv`.

Establish `hc` using `Fintype.linearIndependent_iff.1 (fr_indep F) _ hw`. Apply `hf0` to reduce the goal to its premises. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[hfx]`. Simplify using `only [LinearMap.zero_apply]`.

Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Establish `: c a = 0` using `by simpa using hc a`. Rewrite using `[this, mul_zero]`.
-/
theorem range_frMap (F : FlagD H r) : LinearMap.range (frMap F) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
  set c : Fin (r + 1) → K := fun a => f (fun j => if a = j then 1 else 0) with hcdef
  have hfx : ∀ x, f x = ∑ a, x a * c a := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ x]
    simp only [map_sum, map_smul, smul_eq_mul, hcdef]
  have hv : ∀ v, H.B v (∑ a, star (c a) • F.e a) = 0 := by
    intro v
    have h1 : f (frMap F v) = 0 := by
      have : f (frMap F v) ∈ Submodule.map f (LinearMap.range (frMap F)) :=
        Submodule.mem_map_of_mem (LinearMap.mem_range_self _ v)
      rw [hf] at this
      exact (Submodule.mem_bot K).1 this
    rw [hfx] at h1
    rw [map_sum]
    simp only [map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul]
    rw [← h1]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [frMap_apply, mul_comm]
  have hw := B_right_nondeg H _ hv
  have hc := Fintype.linearIndependent_iff.1 (fr_indep F) _ hw
  apply hf0
  refine LinearMap.ext fun x => ?_
  rw [hfx]
  simp only [LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  have : c a = 0 := by simpa using hc a
  rw [this, mul_zero]

/- English proof (translation)
Establish `h` using `LinearMap.finrank_range_add_finrank_ker (frMap F)`. Rewrite `h` using `[range_frMap, ker_frMap, finrank_top, Module.finrank_fin_fun]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_frPerp [FiniteDimensional K V] (F : FlagD H r) :
    Module.finrank K (frPerp F) + (r + 1) = Module.finrank K V := by
  have h := LinearMap.finrank_range_add_finrank_ker (frMap F)
  rw [range_frMap, ker_frMap, finrank_top, Module.finrank_fin_fun] at h
  omega

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨b, -, rfl⟩ a`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last => rw [← H.herm (F.e b.castSucc) (F.e (Fin.last r)), F.zperp b, star_zero]`. Consider the case `cast a => exact F.iso a b`.
-/
theorem X_le_frPerp (F : FlagD H r) : F.X ≤ frPerp F := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, -, rfl⟩ a
  induction a using Fin.lastCases with
  | last => rw [← H.herm (F.e b.castSucc) (F.e (Fin.last r)), F.zperp b, star_zero]
  | cast a => exact F.iso a b

/- English proof (translation)
Establish `h : F.X = Submodule.span K (Set.range fun a : Fin r => F.e a.castSucc)` using `by show Submodule.span K _ = _`. Use `congr 1`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[h, finrank_span_eq_card F.indep, Fintype.card_fin]`.
-/
theorem finrank_X (F : FlagD H r) : Module.finrank K F.X = r := by
  have h : F.X = Submodule.span K (Set.range fun a : Fin r => F.e a.castSucc) := by
    show Submodule.span K _ = _
    congr 1
    ext x
    simp
  rw [h, finrank_span_eq_card F.indep, Fintype.card_fin]

def resH (H : HermSpace K V) (W : Submodule K V) (hnd : ∀ x : W, (∀ y : W, H.B x y = 0) → x = 0) :
    HermSpace K W where
  B := (H.B.comp W.subtype).compl₂ W.subtype
  herm x y := H.herm x y
  nondeg x h := hnd x h

/- English proof (translation)
Take `⟨Y, hY⟩` from `Submodule.exists_isCompl F.X`. Use `set W := Y ⊓ frPerp F with hW`. Establish `hsup : F.X ⊔ W = frPerp F`. Rewrite using `[hW, ← sup_inf_assoc_of_le Y (X_le_frPerp F), hY.sup_eq_top, top_inf_eq]`. Establish `hinf : F.X ⊓ W = ⊥`.

Use `eq_bot_iff.2 fun x hx => ?_` and prove the remaining obligations. Conclude with `hY.inf_eq_bot ▸ ⟨hx.1, hx.2.1⟩`. Establish `hpos : ∀ (σ : K →+* ℂ) (x : W), x ≠ 0 → 0 < (σ (H.B x x)).re`. Introduce `σ x hx`. Use `hP σ x ((mem_frPerp F _).1 x.2.2) fun hxX => hx ?_` and prove the remaining obligations.

Establish `: (x : V) ∈ F.X ⊓ W` using `⟨hxX, x.2⟩`. Rewrite `this` using `[hinf]`. Conclude with `Subtype.ext ((Submodule.mem_bot K).1 this)`. Establish `hnd : ∀ x : W, (∀ y : W, H.B x y = 0) → x = 0`. Introduce `x h`.

Assume the negation of the conclusion as `hx`. Use `hpos τ₀ x hx` as an intermediate fact. Rewrite `this` using `[h x, map_zero, Complex.zero_re]`. Conclude with `lt_irrefl _ this`. Use `⟨W, resH H W hnd, ⟨fun x y => rfl, fun v => ?_⟩, ?_, fun σ x hx => hpos σ x hx⟩` and prove the remaining obligations.

Rewrite using `[← mem_frPerp, Submodule.range_subtype, sup_comm, hsup]`. Establish `h1` using `Submodule.finrank_sup_add_finrank_inf_eq F.X W`. Rewrite `h1` using `[hsup, hinf, finrank_bot, finrank_X]`. Establish `h2` using `finrank_frPerp F`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_emb [FiniteDimensional K V] (F : FlagD H r) (τ₀ : K →+* ℂ) (hP : ∀ σ : K →+* ℂ, F.PosDefAt σ) :
    ∃ (W : Submodule K V) (HW : HermSpace K W), GlobalTheory.DegAsm.IsEmb F HW W.subtype ∧
      Module.finrank K W + (2 * r + 1) = Module.finrank K V ∧ GlobalTheory.Mass.PD HW.B.flip := by
  obtain ⟨Y, hY⟩ := Submodule.exists_isCompl F.X
  set W := Y ⊓ frPerp F with hW
  have hsup : F.X ⊔ W = frPerp F := by
    rw [hW, ← sup_inf_assoc_of_le Y (X_le_frPerp F), hY.sup_eq_top, top_inf_eq]
  have hinf : F.X ⊓ W = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    exact hY.inf_eq_bot ▸ ⟨hx.1, hx.2.1⟩
  have hpos : ∀ (σ : K →+* ℂ) (x : W), x ≠ 0 → 0 < (σ (H.B x x)).re := by
    intro σ x hx
    refine hP σ x ((mem_frPerp F _).1 x.2.2) fun hxX => hx ?_
    have : (x : V) ∈ F.X ⊓ W := ⟨hxX, x.2⟩
    rw [hinf] at this
    exact Subtype.ext ((Submodule.mem_bot K).1 this)
  have hnd : ∀ x : W, (∀ y : W, H.B x y = 0) → x = 0 := by
    intro x h
    by_contra hx
    have := hpos τ₀ x hx
    rw [h x, map_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  refine ⟨W, resH H W hnd, ⟨fun x y => rfl, fun v => ?_⟩, ?_, fun σ x hx => hpos σ x hx⟩
  · rw [← mem_frPerp, Submodule.range_subtype, sup_comm, hsup]
  · have h1 := Submodule.finrank_sup_add_finrank_inf_eq F.X W
    rw [hsup, hinf, finrank_bot, finrank_X] at h1
    have h2 := finrank_frPerp F
    omega

end EmbGen

/- English proof (translation)
Introduce `D large₂ X u _`. Establish `hpos : ∀ σ : D.host.E →+* ℂ, (F0 X u).PosDefAt σ` using `fun σ => Formalism.MainNotions.KappaEndpoints.nf_pos (lf D (X.Fu u)) (tu_ne D u) (p_posX D (Tu D u) (D.mem u).A.T_prime.pos _) σ`. Set `τ₀ : D.host.E →+* ℂ` to `(IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := D.host.E)).toRingHom`. Take `⟨W, HW, h1, h2, h3⟩` from `exists_emb (F0 X u) τ₀ hpos`. Use `⟨W, HW, h1, ?_, h3⟩` and prove the remaining obligations.

Establish `hV : Module.finrank D.host.E (VS D).V = D.R.rankY 0`. Rewrite using `[(VS D).rank_eq]`. Conclude with `D.sp.Y_rank 0 (Nat.zero_le _)`. Establish `hR : D.R.rankY 0 = 2 * D.R.rS + D.R.k + 1`. Take `⟨c, hc⟩` from `D.R.m_even`.

Use `D.R.two_le_m` as an intermediate fact. Simplify using `only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.rS, Formalism.BasicNotions.Ranks.r, zero_mul, add_zero]`. Use linear arithmetic over natural numbers and integers. Rewrite `h2` using `[hV, hR]`. Use linear arithmetic over natural numbers and integers.
-/
theorem embC : EmbC := by
  intro D large₂ X u _
  have hpos : ∀ σ : D.host.E →+* ℂ, (F0 X u).PosDefAt σ := fun σ =>
    Formalism.MainNotions.KappaEndpoints.nf_pos (lf D (X.Fu u)) (tu_ne D u)
      (p_posX D (Tu D u) (D.mem u).A.T_prime.pos _) σ
  let τ₀ : D.host.E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := D.host.E)).toRingHom
  obtain ⟨W, HW, h1, h2, h3⟩ := exists_emb (F0 X u) τ₀ hpos
  refine ⟨W, HW, h1, ?_, h3⟩
  have hV : Module.finrank D.host.E (VS D).V = D.R.rankY 0 := by
    rw [(VS D).rank_eq]
    exact D.sp.Y_rank 0 (Nat.zero_le _)
  have hR : D.R.rankY 0 = 2 * D.R.rS + D.R.k + 1 := by
    obtain ⟨c, hc⟩ := D.R.m_even
    have := D.R.two_le_m
    simp only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.rS, Formalism.BasicNotions.Ranks.r, zero_mul, add_zero]
    omega
  rw [hV, hR] at h2
  omega

end GlobalTheory.TypeAsm
