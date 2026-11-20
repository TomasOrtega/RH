import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarOmPart
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarNMove

noncomputable section

open scoped Classical
open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Matrix

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

open OmP

namespace OmR

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S`.
-/
theorem mem_orth' {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 :=
  PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S

/- English proof (translation)
The claim follows from `NMoveP.hsw S x y`.
-/
theorem hswap (x y : S.V) : S.hT y x = star (S.hT x y) := NMoveP.hsw S x y

/- English proof (translation)
The claim follows from `mem_orth'.2 fun x hx => NMoveP.spanL S F.e v h x hx`.
-/
theorem orthX_of {T : E} (F : FlagG S r T) {v : S.V} (h : ∀ i, S.hT (F.e i) v = 0) : v ∈ orth S F.X :=
  mem_orth'.2 fun x hx => NMoveP.spanL S F.e v h x hx

/- English proof (translation)
The claim follows from `orthX_of F fun i => by rw [← fvec_cs]; exact h _`.
-/
theorem orthX_of_f {T : E} (F : FlagG S r T) {v : S.V} (h : ∀ a, S.hT (F.fvec a) v = 0) : v ∈ orth S F.X :=
  orthX_of F fun i => by rw [← fvec_cs]; exact h _

/- English proof (translation)
The claim follows from `orthX_of F fun i => by rw [← fvec_cs, h.2]; simp [Fin.castSucc_ne_last]`.
-/
theorem om_orthX {T T' : E} {F : FlagG S r T} {F' : FlagG S r T'} {v : S.V} (h : OmV F F' v) :
    v ∈ orth S F.X :=
  orthX_of F fun i => by rw [← fvec_cs, h.2]; simp [Fin.castSucc_ne_last]

/- English proof (translation)
The claim follows from `orthX_of F F.z_orth`.
-/
theorem z_orthX {T : E} (F : FlagG S r T) : F.z ∈ orth S F.X := orthX_of F F.z_orth

/- English proof (translation)
Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨i.castSucc, fvec_cs F i⟩`.
-/
theorem X_le_sp {T : E} (F : FlagG S r T) : F.X ≤ Submodule.span E (Set.range F.fvec) := by
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨i.castSucc, fvec_cs F i⟩

section NL

variable {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V}

/- English proof (translation)
The claim follows from `hn.1.1 x y`.
-/
theorem nl_isom (hn : n ∈ NLam Λ F) (x y : S.V) : S.hT (n x) (n y) = S.hT x y := hn.1.1 x y

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨i, show i.1 < i.1 + 1 from Nat.lt_succ_self _, rfl⟩`.
-/
theorem e_mem_flag (F : LFlag S r T) (i : Fin r) : F.fl.e i ∈ Xflag F (i.1 + 1) :=
  Submodule.subset_span ⟨i, show i.1 < i.1 + 1 from Nat.lt_succ_self _, rfl⟩

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_subset_range _ _)`.
-/
theorem flag_le_X (F : LFlag S r T) (j : ℕ) : Xflag F j ≤ Xsp F :=
  Submodule.span_mono (Set.image_subset_range _ _)

/- English proof (translation)
The claim follows from `flag_le_X F i.1 (hn.2.1 i.1 _ (e_mem_flag F i))`.
-/
theorem nl_e (hn : n ∈ NLam Λ F) (i : Fin r) : n (F.fl.e i) - F.fl.e i ∈ Xsp F :=
  flag_le_X F i.1 (hn.2.1 i.1 _ (e_mem_flag F i))

/- English proof (translation)
Establish `: Xsp F ≤ (Xsp F).comap (n : S.V →ₗ[E] S.V)` using `by show Submodule.span E (Set.range F.fl.e) ≤ _`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Use `show n (F.fl.e i) ∈ Xsp F`. Establish `h` using `nl_e hn i`.

Establish `e : n (F.fl.e i) = (n (F.fl.e i) - F.fl.e i) + F.fl.e i` using `by abel`. Rewrite using `[e]`. Conclude with `Submodule.add_mem _ h (Submodule.subset_span ⟨i, rfl⟩)`. Conclude with `this hx`.
-/
theorem nl_X (hn : n ∈ NLam Λ F) {x : S.V} (hx : x ∈ Xsp F) : n x ∈ Xsp F := by
  have : Xsp F ≤ (Xsp F).comap (n : S.V →ₗ[E] S.V) := by
    show Submodule.span E (Set.range F.fl.e) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show n (F.fl.e i) ∈ Xsp F
    have h := nl_e hn i
    have e : n (F.fl.e i) = (n (F.fl.e i) - F.fl.e i) + F.fl.e i := by abel
    rw [e]
    exact Submodule.add_mem _ h (Submodule.subset_span ⟨i, rfl⟩)
  exact this hx

/- English proof (translation)
The claim follows from `hn.2.2 v hv`.
-/
theorem nl_orth (hn : n ∈ NLam Λ F) {v : S.V} (hv : v ∈ orth S (Xsp F)) : n v - v ∈ Xsp F := hn.2.2 v hv

/- English proof (translation)
Use `mem_orth'.2 fun x hx => ?_` and prove the remaining obligations. Rewrite using `[← nl_isom hn x, LinearEquiv.apply_symm_apply]`. Conclude with `mem_orth'.1 hv _ (nl_X hn hx)`.
-/
theorem nl_symm_orth (hn : n ∈ NLam Λ F) {v : S.V} (hv : v ∈ orth S (Xsp F)) : n.symm v ∈ orth S (Xsp F) := by
  refine mem_orth'.2 fun x hx => ?_
  rw [← nl_isom hn x, LinearEquiv.apply_symm_apply]
  exact mem_orth'.1 hv _ (nl_X hn hx)

/- English proof (translation)
Apply `Submodule.eq_of_le_of_finrank_eq _ (LinearEquiv.finrank_map_eq n _)` to reduce the goal to its premises. Rewrite using `[Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨b, rfl⟩, rfl⟩`. Establish `hX` using `X_le_sp F.fl`. Establish `e : (n : S.V →ₗ[E] S.V) (F.fl.fvec b) = F.fl.fvec b + (n (F.fl.fvec b) - F.fl.fvec b)`.

Simplify using the standard rewrite rules. Rewrite using `[e]`. Use `Submodule.add_mem _ (Submodule.subset_span ⟨b, rfl⟩) (hX ?_)` and prove the remaining obligations. Use `Fin.lastCases ?_ (fun i => ?_) b` and prove the remaining obligations. Rewrite using `[fvec_last]`.

Conclude with `nl_orth hn (z_orthX F.fl)`. Rewrite using `[fvec_cs]`. Conclude with `nl_e hn i`.
-/
theorem sp_map_eq (hn : n ∈ NLam Λ F) :
    (Submodule.span E (Set.range F.fl.fvec)).map (n : S.V →ₗ[E] S.V) = Submodule.span E (Set.range F.fl.fvec) := by
  apply Submodule.eq_of_le_of_finrank_eq _ (LinearEquiv.finrank_map_eq n _)
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
  have hX := X_le_sp F.fl
  have e : (n : S.V →ₗ[E] S.V) (F.fl.fvec b) = F.fl.fvec b + (n (F.fl.fvec b) - F.fl.fvec b) := by
    simp
  rw [e]
  refine Submodule.add_mem _ (Submodule.subset_span ⟨b, rfl⟩) (hX ?_)
  refine Fin.lastCases ?_ (fun i => ?_) b
  · rw [fvec_last]; exact nl_orth hn (z_orthX F.fl)
  · rw [fvec_cs]; exact nl_e hn i

end NL

section DC

variable {Λ : Submodule (𝓞 E) S.V} {T T' : E} (F : LFlag S r T)

def Inv (Ωγ : S.V) (F₁ : LFlag S r T') : Prop := ∃ v, OmV F.fl F₁.fl v ∧ v - Ωγ ∈ Xsp F

def QU (F₁ : LFlag S r T') : Prop :=
  ∀ d ∈ Submodule.span E (Set.range F₁.fl.fvec), (∀ a, S.hT (F.fl.fvec a) d = 0) → d = 0

/- English proof (translation)
Introduce `_ hd h0` and use `eq_zero_of_orth F.fl F₁.fl h hd h0`.
-/
theorem qu_of_det (F₁ : LFlag S r T') (h : (Zhat F.fl F₁.fl).det ≠ 0) : QU F F₁ :=
  fun _ hd h0 => eq_zero_of_orth F.fl F₁.fl h hd h0

variable {F}

/- English proof (translation)
Establish `e : F₂.fl.fvec = ((n : S.V →ₗ[E] S.V) ∘ₗ (m : S.V →ₗ[E] S.V)) ∘ F₁.fl.fvec` using `funext h`. Rewrite using `[e, Set.range_comp, ← Submodule.map_span, Submodule.map_comp, sp_map_eq hm]`.
-/
theorem sp_dc {F₁ F₂ : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V} (hm : m ∈ NLam Λ F₁)
    (h : ∀ a, frame F₂ a = n (m (frame F₁ a))) :
    Submodule.span E (Set.range F₂.fl.fvec) = (Submodule.span E (Set.range F₁.fl.fvec)).map (n : S.V →ₗ[E] S.V) := by
  have e : F₂.fl.fvec = ((n : S.V →ₗ[E] S.V) ∘ₗ (m : S.V →ₗ[E] S.V)) ∘ F₁.fl.fvec := funext h
  rw [e, Set.range_comp, ← Submodule.map_span, Submodule.map_comp, sp_map_eq hm]

/- English proof (translation)
Take `⟨n, hn, m, hm, hf, -⟩` from `h`. Establish `hsp` using `sp_dc hm hf`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, hvγ⟩`. Establish `hd` using `nl_orth hn (om_orthX hv)`.

Use `⟨n v, ⟨?_, fun a => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hsp, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]`. Conclude with `hv.1`. Establish `e : n v = v + (n v - v)` using `by abel`. Rewrite using `[e, map_add, NMoveP.hT_f_X F.fl a hd, add_zero, hv.2]`.

Establish `e : n v - Ωγ = (n v - v) + (v - Ωγ)` using `by abel`. Rewrite using `[e]`. Conclude with `Submodule.add_mem _ hd hvγ`. Introduce and unpack `⟨v, hv, hvγ⟩`. Establish `ho` using `nl_symm_orth hn (om_orthX hv)`.

Establish `hd` using `nl_orth hn ho`. Rewrite `hd` using `[LinearEquiv.apply_symm_apply]`. Use `⟨n.symm v, ⟨?_, fun a => ?_⟩, ?_⟩` and prove the remaining obligations. Establish `h1` using `hv.1`. Rewrite `h1` using `[hsp, Submodule.mem_map_equiv]`.

Conclude with `h1`. Establish `e : n.symm v = v - (v - n.symm v)` using `by abel`. Rewrite using `[e, map_sub, NMoveP.hT_f_X F.fl a hd, sub_zero, hv.2]`. Establish `e : n.symm v - Ωγ = (v - Ωγ) - (v - n.symm v)` using `by abel`. Rewrite using `[e]`.

Conclude with `Submodule.sub_mem _ hvγ hd`.
-/
theorem inv_dc {Ωγ : S.V} {F₁ F₂ : LFlag S r T'} (h : DCRel Λ F F₁ F₂) : Inv F Ωγ F₁ ↔ Inv F Ωγ F₂ := by
  obtain ⟨n, hn, m, hm, hf, -⟩ := h
  have hsp := sp_dc hm hf
  constructor
  · rintro ⟨v, hv, hvγ⟩
    have hd := nl_orth hn (om_orthX hv)
    refine ⟨n v, ⟨?_, fun a => ?_⟩, ?_⟩
    · rw [hsp, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]; exact hv.1
    · have e : n v = v + (n v - v) := by abel
      rw [e, map_add, NMoveP.hT_f_X F.fl a hd, add_zero, hv.2]
    · have e : n v - Ωγ = (n v - v) + (v - Ωγ) := by abel
      rw [e]; exact Submodule.add_mem _ hd hvγ
  · rintro ⟨v, hv, hvγ⟩
    have ho := nl_symm_orth hn (om_orthX hv)
    have hd := nl_orth hn ho
    rw [LinearEquiv.apply_symm_apply] at hd
    refine ⟨n.symm v, ⟨?_, fun a => ?_⟩, ?_⟩
    · have h1 := hv.1
      rw [hsp, Submodule.mem_map_equiv] at h1
      exact h1
    · have e : n.symm v = v - (v - n.symm v) := by abel
      rw [e, map_sub, NMoveP.hT_f_X F.fl a hd, sub_zero, hv.2]
    · have e : n.symm v - Ωγ = (v - Ωγ) - (v - n.symm v) := by abel
      rw [e]; exact Submodule.sub_mem _ hvγ hd

/- English proof (translation)
Take `⟨n, hn, m, hm, hf, -⟩` from `h`. Establish `hsp` using `sp_dc hm hf`. Prove the components needed by the constructor for the conclusion. Introduce `hq d hd h0`. Establish `ho : d ∈ orth S (Xsp F)` using `orthX_of_f F.fl h0`.

Establish `ho'` using `nl_symm_orth hn ho`. Establish `hdd` using `nl_orth hn ho'`. Rewrite `hdd` using `[LinearEquiv.apply_symm_apply]`. Rewrite `hd` using `[hsp, Submodule.mem_map_equiv]`. Establish `: n.symm d = 0` using `hq _ hd fun a => by`.

Establish `e : n.symm d = d - (d - n.symm d)` using `by abel`. Rewrite using `[e, map_sub, NMoveP.hT_f_X F.fl a hdd, sub_zero, h0]`. Simplify using `using congrArg n this`. Introduce `hq d hd h0`. Establish `ho : d ∈ orth S (Xsp F)` using `orthX_of_f F.fl h0`.

Establish `hdd` using `nl_orth hn ho`. Establish `hnd : n d ∈ Submodule.span E (Set.range F₂.fl.fvec)`. Rewrite using `[hsp, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]`. Conclude with `hd`. Establish `: n d = 0` using `hq _ hnd fun a => by`.

Establish `e : n d = d + (n d - d)` using `by abel`. Rewrite using `[e, map_add, NMoveP.hT_f_X F.fl a hdd, add_zero, h0]`. Simplify using `using this`.
-/
theorem qu_dc {F₁ F₂ : LFlag S r T'} (h : DCRel Λ F F₁ F₂) : QU F F₁ ↔ QU F F₂ := by
  obtain ⟨n, hn, m, hm, hf, -⟩ := h
  have hsp := sp_dc hm hf
  constructor
  · intro hq d hd h0
    have ho : d ∈ orth S (Xsp F) := orthX_of_f F.fl h0
    have ho' := nl_symm_orth hn ho
    have hdd := nl_orth hn ho'
    rw [LinearEquiv.apply_symm_apply] at hdd
    rw [hsp, Submodule.mem_map_equiv] at hd
    have : n.symm d = 0 := hq _ hd fun a => by
      have e : n.symm d = d - (d - n.symm d) := by abel
      rw [e, map_sub, NMoveP.hT_f_X F.fl a hdd, sub_zero, h0]
    simpa using congrArg n this
  · intro hq d hd h0
    have ho : d ∈ orth S (Xsp F) := orthX_of_f F.fl h0
    have hdd := nl_orth hn ho
    have hnd : n d ∈ Submodule.span E (Set.range F₂.fl.fvec) := by
      rw [hsp, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]; exact hd
    have : n d = 0 := hq _ hnd fun a => by
      have e : n d = d + (n d - d) := by abel
      rw [e, map_add, NMoveP.hT_f_X F.fl a hdd, add_zero, h0]
    simpa using this

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `rel a b hab => exact hI _ _ hab`. Consider the case `refl => exact Iff.rfl`. Consider the case `symm a b _ ih => exact ih.symm`. Consider the case `trans a b c _ _ ih1 ih2 => exact ih1.trans ih2`.
-/
theorem inv_eqv {P : LFlag S r T' → Prop} {x y : Carrier P} (h : Relation.EqvGen (Rel Λ F P) x y)
    (I : LFlag S r T' → Prop) (hI : ∀ F₁ F₂, DCRel Λ F F₁ F₂ → (I F₁ ↔ I F₂)) : I x.1 ↔ I y.1 := by
  induction h with
  | rel a b hab => exact hI _ _ hab
  | refl => exact Iff.rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

end DC

section Pair

variable {Λ : Submodule (𝓞 E) S.V} {T T' : E}

/- English proof (translation)
Use `symm`. Apply `Submodule.eq_of_le_of_finrank_eq` to reduce the goal to its premises. Introduce `u hu`. Use `mem_orth'.2 fun x hx => ?_` and prove the remaining obligations. Rewrite using `[hswap, mem_orth'.1 hx u hu, star_zero]`.

Establish `h1` using `PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S U`. Establish `h2` using `PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S (orth S U)`. Use linear arithmetic over natural numbers and integers.
-/
theorem orth_orth (U : Submodule E S.V) : orth S (orth S U) = U := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · intro u hu
    refine mem_orth'.2 fun x hx => ?_
    rw [hswap, mem_orth'.1 hx u hu, star_zero]
  · have h1 := PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S U
    have h2 := PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S (orth S U)
    omega

/- English proof (translation)
Use `Submodule.subset_span ?_` and prove the remaining obligations. Use `show F.fl.z ∈ (UU Λ F F' : Set S.V)`. Rewrite using `[← hF.2]`. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))`.
-/
theorem z_mem_UUE (F : LFlag S r T) (F' : LFlag S r T') (hF : IsLift Λ F) : F.fl.z ∈ UUE Λ F F' := by
  refine Submodule.subset_span ?_
  show F.fl.z ∈ (UU Λ F F' : Set S.V)
  rw [← hF.2]
  exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right
    (Submodule.mem_span_singleton_self _)))

/- English proof (translation)
Use `Submodule.subset_span ?_` and prove the remaining obligations. Use `show F'.fl.z ∈ (UU Λ F F' : Set S.V)`. Rewrite using `[← hF'.2]`. Conclude with `Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`.
-/
theorem z'_mem_UUE (F : LFlag S r T) (F' : LFlag S r T') (hF' : IsLift Λ F') : F'.fl.z ∈ UUE Λ F F' := by
  refine Submodule.subset_span ?_
  show F'.fl.z ∈ (UU Λ F F' : Set S.V)
  rw [← hF'.2]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

/- English proof (translation)
Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨b, rfl⟩`. Use `Fin.lastCases ?_ (fun i => ?_) b` and prove the remaining obligations. Rewrite using `[fvec_last]`. Conclude with `z'_mem_UUE F F' hF'`.

Rewrite using `[fvec_cs]`. Conclude with `PI.UnitaryGroupMassFormula.BetaLUniq.Xsp_le_UUE' S Λ hΛ F F' (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem sp_le_UUE (hΛ : Submodule.IsLattice E Λ) (F : LFlag S r T) (F' : LFlag S r T') (hF' : IsLift Λ F') :
    Submodule.span E (Set.range F'.fl.fvec) ≤ UUE Λ F F' := by
  rw [Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  refine Fin.lastCases ?_ (fun i => ?_) b
  · rw [fvec_last]; exact z'_mem_UUE F F' hF'
  · rw [fvec_cs]
    exact PI.UnitaryGroupMassFormula.BetaLUniq.Xsp_le_UUE' S Λ hΛ F F' (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Establish `n'` using `PI.UnitaryGroupMassFormula.BetaLUniq.gram_matrix_nondegenerate S Λ F F' hΛ hLF hL' hG'`. Establish `hHp : finrank E (Hp Λ F F') + (2 * r + 2) = finrank E S.V`. Use `PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S (UUE Λ F F')` as an intermediate fact. Rewrite `this` using `[n'.1]`. Conclude with `this`.

Establish `hle : Th Λ F F' F'' β ≤ Hp Λ F F'`. Introduce `y hy`. Take `⟨p, hp, rfl⟩` from `Submodule.mem_map.mp hy`. Simplify using `only [ThPairs, Submodule.mem_inf, Submodule.mem_prod] at hp`. Conclude with `hp.1.1.1`.

Establish `hTh : Th Λ F F' F'' β = Hp Λ F F'`. Apply `Submodule.eq_of_le_of_finrank_le hle` to reduce the goal to its premises. Simplify using `only [s0] at hs`. Use linear arithmetic over natural numbers and integers. Use `set ν : S.V := Ω'' + T⁻¹ • F.fl.z with hν`.

Establish `hzX : F.fl.z ∈ orth S (Xsp F)` using `z_orthX F.fl`. Use `clear_value ν`. Establish `hνX : ν ∈ orth S (Xsp F)`. Rewrite using `[hν]`. Conclude with `Submodule.add_mem _ (om_orthX hΩ) (Submodule.smul_mem _ _ hzX)`.

Establish `hνU'' : ν ∈ UUE Λ F F''`. Rewrite using `[hν]`. Conclude with `Submodule.add_mem _ (sp_le_UUE hΛ F F'' hL'' hΩ.1) (Submodule.smul_mem _ _ (z_mem_UUE F F'' hLF))`. Establish `hνH : ν ∈ orth S (Hp Λ F F')`. Use `mem_orth'.2 fun x hx => ?_` and prove the remaining obligations.

Rewrite `hx` using `[← hTh]`. Take `⟨p, hp, rfl⟩` from `Submodule.mem_map.mp hx`. Simplify using `only [ThPairs, Submodule.mem_inf, Submodule.mem_prod, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.fst_apply, LinearMap.snd_apply] at hp`. Establish `e : p.1 = p.2 + (p.1 - p.2)` using `by abel`. Simplify using `only [LinearMap.fst_apply]`.

Rewrite using `[e, LinearMap.map_add₂, mem_orth'.1 hνX _ hp.1.2]`. Establish `h2 : S.hT ν p.2 = 0` using `mem_orth'.1 hp.1.1.2 ν hνU''`. Rewrite using `[hswap, h2, star_zero, add_zero]`. Establish `hνU' : ν ∈ UUE Λ F F'`. Use `hνH` as an intermediate fact.

Rewrite `this` using `[show Hp Λ F F' = orth S (UUE Λ F F') from rfl, orth_orth]`. Conclude with `this`. Establish `hzz : S.hT F.fl.z ν = 0`. Establish `h1 : S.hT F.fl.z Ω'' = 1` using `by rw [← fvec_last, hΩ.2]; simp`. Rewrite using `[hν, map_add, map_smul, h1, F.fl.z_norm, smul_eq_mul]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hνXp : ν ∈ orth S (Xplus F)`. Use `mem_orth'.2 fun x hx => ?_` and prove the remaining obligations. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hx`.

Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hb`. Rewrite using `[LinearMap.map_add₂, mem_orth'.1 hνX a ha, NMoveP.hT_smulL, hzz, mul_zero, add_zero]`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun E).1 hΩ.1`. Establish `hSg'' : SgRel F F'' ν 0 T⁻¹ (c (Fin.last r))`. Use `⟨0, Submodule.zero_mem _, ∑ i : Fin r, c i.castSucc • F''.fl.e i, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩` and prove the remaining obligations.

Rewrite using `[hLF.2, hL''.2, hν, ← hc, Fin.sum_univ_castSucc, fvec_last]`. Simplify using `only [fvec_cs, sub_zero, add_zero]`. Normalize the expressions using the abelian group laws. Establish `hY : ∀ {F₁ : LFlag S r T'}, ν ∈ UUE Λ F F₁ → ν ∈ Ylift Λ F F₁` using `fun h => Submodule.mem_inf.2 ⟨h, hνXp⟩`. Take `⟨x, hx, x', hx', hE⟩` from `(hsc ν (hY hνU') ν (hY hνU'') 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) (by simp) (by simp) T⁻¹ (c (Fin.last r))).2 hSg''`.

Use `⟨Ω'' - x, ⟨?_, fun a => ?_⟩, by simpa using hx⟩` and prove the remaining obligations. Establish `e : Ω'' - x = c (Fin.last r) • F'.fl.z + x'`. Rewrite `hE` using `[hLF.2, hL'.2, sub_zero, hν]`. Use `congrArg (fun v => v - T⁻¹ • F.fl.z - x) hE` as an intermediate fact. Rewrite using `[show Ω'' - x = Ω'' + T⁻¹ • F.fl.z - T⁻¹ • F.fl.z - x by abel, this]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Use `Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.last r, fvec_last _⟩)) (X_le_sp F'.fl hx')` and prove the remaining obligations. Rewrite using `[map_sub, NMoveP.hT_f_X F.fl a hx, sub_zero, hΩ.2]`.
-/
theorem pair_core (hΛ : Submodule.IsLattice E Λ) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (k : ℕ) (hLF : IsLift Λ F) (hL' : IsLift Λ F') (hL'' : IsLift Λ F'') (hG' : Gval F F' ≠ 0)
    (hdim : finrank E S.V = k + 2 * r + 1) (hT : T ≠ 0) (hs : s0 Λ F F' F'' β k = 1)
    (hsc : IsScalar Λ F F' F'' β) {Ω'' : S.V} (hΩ : OmV F.fl F''.fl Ω'') :
    ∃ w, OmV F.fl F'.fl w ∧ Ω'' - w ∈ Xsp F := by
  have n' := PI.UnitaryGroupMassFormula.BetaLUniq.gram_matrix_nondegenerate S Λ F F' hΛ hLF hL' hG'
  have hHp : finrank E (Hp Λ F F') + (2 * r + 2) = finrank E S.V := by
    have := PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S (UUE Λ F F')
    rw [n'.1] at this
    exact this
  have hle : Th Λ F F' F'' β ≤ Hp Λ F F' := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hy
    simp only [ThPairs, Submodule.mem_inf, Submodule.mem_prod] at hp
    exact hp.1.1.1
  have hTh : Th Λ F F' F'' β = Hp Λ F F' := by
    apply Submodule.eq_of_le_of_finrank_le hle
    simp only [s0] at hs
    omega
  set ν : S.V := Ω'' + T⁻¹ • F.fl.z with hν
  have hzX : F.fl.z ∈ orth S (Xsp F) := z_orthX F.fl
  clear_value ν
  have hνX : ν ∈ orth S (Xsp F) := by
    rw [hν]; exact Submodule.add_mem _ (om_orthX hΩ) (Submodule.smul_mem _ _ hzX)
  have hνU'' : ν ∈ UUE Λ F F'' := by
    rw [hν]; exact Submodule.add_mem _ (sp_le_UUE hΛ F F'' hL'' hΩ.1) (Submodule.smul_mem _ _ (z_mem_UUE F F'' hLF))
  have hνH : ν ∈ orth S (Hp Λ F F') := by
    refine mem_orth'.2 fun x hx => ?_
    rw [← hTh] at hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    simp only [ThPairs, Submodule.mem_inf, Submodule.mem_prod, Submodule.mem_comap, LinearMap.sub_apply,
      LinearMap.fst_apply, LinearMap.snd_apply] at hp
    have e : p.1 = p.2 + (p.1 - p.2) := by abel
    simp only [LinearMap.fst_apply]
    rw [e, LinearMap.map_add₂, mem_orth'.1 hνX _ hp.1.2]
    have h2 : S.hT ν p.2 = 0 := mem_orth'.1 hp.1.1.2 ν hνU''
    rw [hswap, h2, star_zero, add_zero]
  have hνU' : ν ∈ UUE Λ F F' := by
    have := hνH
    rw [show Hp Λ F F' = orth S (UUE Λ F F') from rfl, orth_orth] at this
    exact this
  have hzz : S.hT F.fl.z ν = 0 := by
    have h1 : S.hT F.fl.z Ω'' = 1 := by rw [← fvec_last, hΩ.2]; simp
    rw [hν, map_add, map_smul, h1, F.fl.z_norm, smul_eq_mul]
    field_simp
    ring
  have hνXp : ν ∈ orth S (Xplus F) := by
    refine mem_orth'.2 fun x hx => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hb
    rw [LinearMap.map_add₂, mem_orth'.1 hνX a ha, NMoveP.hT_smulL, hzz, mul_zero, add_zero]
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hΩ.1
  have hSg'' : SgRel F F'' ν 0 T⁻¹ (c (Fin.last r)) := by
    refine ⟨0, Submodule.zero_mem _, ∑ i : Fin r, c i.castSucc • F''.fl.e i,
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
    rw [hLF.2, hL''.2, hν, ← hc, Fin.sum_univ_castSucc, fvec_last]
    simp only [fvec_cs, sub_zero, add_zero]
    abel
  have hY : ∀ {F₁ : LFlag S r T'}, ν ∈ UUE Λ F F₁ → ν ∈ Ylift Λ F F₁ := fun h => Submodule.mem_inf.2 ⟨h, hνXp⟩
  obtain ⟨x, hx, x', hx', hE⟩ := (hsc ν (hY hνU') ν (hY hνU'') 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _)
    (by simp) (by simp) T⁻¹ (c (Fin.last r))).2 hSg''
  refine ⟨Ω'' - x, ⟨?_, fun a => ?_⟩, by simpa using hx⟩
  · have e : Ω'' - x = c (Fin.last r) • F'.fl.z + x' := by
      rw [hLF.2, hL'.2, sub_zero, hν] at hE
      have := congrArg (fun v => v - T⁻¹ • F.fl.z - x) hE
      rw [show Ω'' - x = Ω'' + T⁻¹ • F.fl.z - T⁻¹ • F.fl.z - x by abel, this]
      abel
    rw [e]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.last r, fvec_last _⟩))
      (X_le_sp F'.fl hx')
  · rw [map_sub, NMoveP.hT_f_X F.fl a hx, sub_zero, hΩ.2]

end Pair

end OmR

open OmR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

/- English proof (translation)
Unfold `repF`. Use `split`. Name the introduced variables `x hx`. Unfold `nrep at hx`. Use `split_ifs at hx with h`.

Consider the cases of `hx`. Conclude with `h.choose_spec.1`. Conclude with `⟨(Quot.out γ.cls).2, Quot.out_eq _⟩`.
-/
theorem omRep_repF (γ : TermDef.Term D u u' F0 what₂) :
    Rep γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') γ.cls (repF γ) := by
  unfold repF
  split
  · rename_i x hx
    unfold nrep at hx
    split_ifs at hx with h
    cases hx
    exact h.choose_spec.1
  · exact ⟨(Quot.out γ.cls).2, Quot.out_eq _⟩

variable (u u' F0 what₂)

/- English proof (translation)
Introduce `hrows γ Z _ hdγ _ F' hP Ω' Ωγ h' hγ`. Take `⟨-, γ', ⟨p, hp1, hp2, hpS⟩, hrep⟩` from `hP`. Establish `hrepγ` using `omRep_repF γ`. Take `⟨lam, mem, cls⟩` from `γ`. Take `⟨lam', mem', cls'⟩` from `γ'`.

Simplify using `only [Corank.Pair.pfst] at hp1`. Simplify using `only [Corank.Pair.psnd] at hp2`. Consider the cases of `hp1`. Consider the cases of `hp2`. Take `⟨hPγ, eγ⟩` from `hrepγ`.

Take `⟨hP', e'⟩` from `hrep`. Establish `r1` using `Quot.eqvGen_exact eγ`. Establish `r2` using `Quot.eqvGen_exact e'`. Establish `hRL` using `hrows.1 p.lam p.mem`. Establish `hΛ : Submodule.IsLattice D.host.E p.lam` using `hRL.2.1.1`.

Establish `hLF : IsLift p.lam (lf D F0)` using `hRL.2.1.2.2.1`. Establish `i1` using `(inv_eqv r1 (Inv (lf D F0) Ωγ) fun _ _ h => inv_dc h).1 ⟨Ωγ, hγ, by simp⟩`. Establish `q1` using `(inv_eqv r1 (QU (lf D F0)) fun _ _ h => qu_dc h).1 (qu_of_det _ _ hdγ)`. Establish `i2` using `(inv_eqv r2 (Inv (lf D F0) Ω') fun _ _ h => inv_dc h).1 ⟨Ω', h', by simp⟩`. Take `⟨v', hv', hv'γ⟩` from `i1`.

Take `⟨v'', hv'', hv''Ω⟩` from `i2`. Take `⟨w, hw, hw''⟩` from `pair_core hΛ (lf D F0) p.fst.1 p.snd.1 p.beta D.R.k hLF p.fst.2.1 p.snd.2.1 p.G_fst (Corank.finrank_VS D) (Corank.tu_ne_zero u) hpS.1 hpS.2 hv''`. Establish `e : v' = w` using `sub_eq_zero.1 (q1 _ (Submodule.sub_mem _ hv'.1 hw.1) fun a => by`. Rewrite using `[map_sub, hv'.2, hw.2, sub_self])`. Substitute `e` using the available equality.

Establish `: Ω' - Ωγ = (v' - Ωγ) + (v'' - v') - (v'' - Ω')` using `by abel`. Rewrite using `[this]`. Conclude with `Submodule.sub_mem _ (Submodule.add_mem _ hv'γ hw'') hv''Ω`.
-/
theorem omega_representative_holds : OmRep u u' F0 what₂ := by
  intro hrows γ Z _ hdγ _ F' hP Ω' Ωγ h' hγ
  obtain ⟨-, γ', ⟨p, hp1, hp2, hpS⟩, hrep⟩ := hP
  have hrepγ := omRep_repF γ
  obtain ⟨lam, mem, cls⟩ := γ
  obtain ⟨lam', mem', cls'⟩ := γ'
  simp only [Corank.Pair.pfst] at hp1
  simp only [Corank.Pair.psnd] at hp2
  cases hp1
  cases hp2
  obtain ⟨hPγ, eγ⟩ := hrepγ
  obtain ⟨hP', e'⟩ := hrep
  have r1 := Quot.eqvGen_exact eγ
  have r2 := Quot.eqvGen_exact e'
  have hRL := hrows.1 p.lam p.mem
  have hΛ : Submodule.IsLattice D.host.E p.lam := hRL.2.1.1
  have hLF : IsLift p.lam (lf D F0) := hRL.2.1.2.2.1

  have i1 := (inv_eqv r1 (Inv (lf D F0) Ωγ) fun _ _ h => inv_dc h).1 ⟨Ωγ, hγ, by simp⟩
  have q1 := (inv_eqv r1 (QU (lf D F0)) fun _ _ h => qu_dc h).1 (qu_of_det _ _ hdγ)

  have i2 := (inv_eqv r2 (Inv (lf D F0) Ω') fun _ _ h => inv_dc h).1 ⟨Ω', h', by simp⟩
  obtain ⟨v', hv', hv'γ⟩ := i1
  obtain ⟨v'', hv'', hv''Ω⟩ := i2
  obtain ⟨w, hw, hw''⟩ := pair_core hΛ (lf D F0) p.fst.1 p.snd.1 p.beta D.R.k hLF p.fst.2.1 p.snd.2.1 p.G_fst
    (Corank.finrank_VS D) (Corank.tu_ne_zero u) hpS.1 hpS.2 hv''
  have e : v' = w := sub_eq_zero.1 (q1 _ (Submodule.sub_mem _ hv'.1 hw.1) fun a => by
    rw [map_sub, hv'.2, hw.2, sub_self])
  subst e
  have : Ω' - Ωγ = (v' - Ωγ) + (v'' - v') - (v'' - Ω') := by abel
  rw [this]
  exact Submodule.sub_mem _ (Submodule.add_mem _ hv'γ hw'') hv''Ω

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
