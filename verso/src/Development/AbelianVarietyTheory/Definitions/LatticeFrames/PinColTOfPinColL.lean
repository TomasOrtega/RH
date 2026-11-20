import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm.LiveModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => Function.injective_id, Function.surjective_id, Function.surjective_id, fun _ _ γ h => absurd ⟨γ, rfl⟩ h⟩`.
-/
theorem live_id {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀) : A.Live (fun _ => id) :=
  ⟨fun _ => Function.injective_id, Function.surjective_id, Function.surjective_id,
    fun _ _ γ h => absurd ⟨γ, rfl⟩ h⟩

def Reached {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀) : ∀ j, Ch₀ j → Prop
  | 0, _ => True
  | j + 1, β => j + 1 = B.R.m ∨ ∃ (hj : j + 1 ≤ B.R.m) (α : Ch₀ j), ∃ z, A.xi j hj α β z ≠ 0

/- English proof (translation)
Use `⟨fun _ => Subtype.val_injective, fun β => ⟨⟨β, trivial⟩, rfl⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `key : ∀ n, n = B.R.m → ∀ β : Ch₀ n, Reached A n β`. Introduce `n hn β`. Consider the cases of `n with`. Consider the case `zero => trivial`.

Consider the case `succ n => exact Or.inl hn`. Conclude with `fun β => ⟨⟨β, key _ rfl β⟩, rfl⟩`. Introduce `j hj γ hγ α z`. Assume the negation of the conclusion as `h`. Conclude with `hγ ⟨⟨γ, Or.inr ⟨hj, α, z, h⟩⟩, rfl⟩`.
-/
theorem live_reached {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀) :
    A.Live (Ch := fun j => {β // Reached A j β}) (fun _ => Subtype.val) := by
  refine ⟨fun _ => Subtype.val_injective, fun β => ⟨⟨β, trivial⟩, rfl⟩, ?_, ?_⟩
  · have key : ∀ n, n = B.R.m → ∀ β : Ch₀ n, Reached A n β := by
      intro n hn β
      cases n with
      | zero => trivial
      | succ n => exact Or.inl hn
    exact fun β => ⟨⟨β, key _ rfl β⟩, rfl⟩
  · intro j hj γ hγ α z
    by_contra h
    exact hγ ⟨⟨γ, Or.inr ⟨hj, α, z, h⟩⟩, rfl⟩

/- English proof (translation)
The claim follows from `| 0, β, _ => h.first β | j + 1, β, Or.inl e => by have key : ∀ n, B.R.m = n → Function.Surjective (ι n) := by rintro _ rfl; exact h.last exact key _ e.symm β | j + 1, β, Or.inr ⟨hj, α, z, hz⟩ => by by_contra hn exact hz (h.dead j hj β hn α z)`.
-/
theorem reached_mem {Ch₀ Ch : ℕ → Type} {A : TwDat I l Z u a Ch₀} {ι : ∀ j, Ch j → Ch₀ j} (h : A.Live ι) :
    ∀ j (β : Ch₀ j), Reached A j β → β ∈ Set.range (ι j)
  | 0, β, _ => h.first β
  | j + 1, β, Or.inl e => by
      have key : ∀ n, B.R.m = n → Function.Surjective (ι n) := by rintro _ rfl; exact h.last
      exact key _ e.symm β
  | j + 1, β, Or.inr ⟨hj, α, z, hz⟩ => by
      by_contra hn
      exact hz (h.dead j hj β hn α z)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => h.1, fun h' => ⟨h', fun _ hc => absurd (h.first _) hc⟩⟩`.
-/
theorem ramL_first {Ch₀ Ch : ℕ → Type} {A : TwDat I l Z u a Ch₀} {ι : ∀ j, Ch j → Ch₀ j} (h : A.Live ι) (φ) :
    A.RamL ι 0 φ ↔ RamT 0 φ := ⟨fun h => h.1, fun h' => ⟨h', fun _ hc => absurd (h.first _) hc⟩⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => h.1, fun h' => ⟨h', fun _ hc => absurd (h.last _) hc⟩⟩`.
-/
theorem ramL_last {Ch₀ Ch : ℕ → Type} {A : TwDat I l Z u a Ch₀} {ι : ∀ j, Ch j → Ch₀ j} (h : A.Live ι) (φ) :
    A.RamL ι B.R.m φ ↔ RamT B.R.m φ := ⟨fun h => h.1, fun h' => ⟨h', fun _ hc => absurd (h.last _) hc⟩⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.is, hι, h.om, fun j hj _ _ => h.dat j hj _ _, fun j hj _ _ _ => h.cst j hj _ _, fun _ _ _ => Iff.rfl, fun j hj _ φ y => h.rdq j hj _ φ y⟩`.
-/
theorem pinColL_of_pinColT {Ch₀ Ch : ℕ → Type} {A : TwDat I l Z u a Ch₀} {ι : ∀ j, Ch j → Ch₀ j} (hι : A.Live ι)
    {ψ θ x vac c₀ kom dd w Ram rd cK} (h : PinColT A ψ θ x vac c₀ kom dd w Ram rd cK) :
    PinColL A ι ψ θ x vac c₀ kom (fun j α γ => dd j (ι j α) (ι (j + 1) γ)) (fun j α γ => w j (ι j α) (ι (j + 1) γ))
      (fun j => {φ | A.RamL ι j φ}) (fun j β => rd j (ι j β)) cK :=
  ⟨h.is, hι, h.om, fun j hj _ _ => h.dat j hj _ _, fun j hj _ _ _ => h.cst j hj _ _, fun _ _ _ => Iff.rfl,
    fun j hj _ φ y => h.rdq j hj _ φ y⟩

/- English proof (translation)
Establish `hd : ∀ j, j < B.R.m → ∀ α γ, (volLev (x j).vol (A.U j α) : ℂ) * c₀ j * (A.chr (j + 1) (A.xr j α) : ℂ) * (A.chr (j + 1) (A.xr (j + 1) γ) : ℂ)⁻¹ ≠ 0` using `fun j hj α γ => mul_ne_zero (mul_ne_zero (mul_ne_zero (by exact_mod_cast hv j hj α) (hc j hj)) (Circle.coe_ne_zero _)) (inv_ne_zero (Circle.coe_ne_zero _))`. Use `⟨fun j α γ => cK j / ((volLev (x j).vol (A.U j α) : ℂ) * c₀ j * (A.chr (j + 1) (A.xr j α) : ℂ) * (A.chr (j + 1) (A.xr (j + 1) γ) : ℂ)⁻¹), h.is, h.om, fun j hj α γ => ⟨(h.dat j hj α γ).1, ?_⟩, fun j hj α γ => ?_, fun j hj φ => (h.ram j hj φ).trans ⟨fun h => h.1, fun h' => ⟨h', fun …` and prove the remaining obligations. Establish `h2` using `(h.dat j hj α γ).2`. Use `h2 using 2 with z` and compare the differences between its conclusion and the goal. Distinguish the cases in `hz : A.xi j hj α γ z = 0`.

Simplify using `only [id]`. Rewrite using `[hz, mul_zero, mul_zero]`. Establish `e` using `h.cst j hj α γ ⟨z, hz⟩`. Simplify using `only [id] at e ⊢`. Use `congr 1`.

Rewrite using `[div_eq_iff (hd j hj α γ), e]`. Expand and normalize the polynomial expressions, which then agree. Use `hd j hj α γ` as an intermediate fact. Rewrite using `[show ∀ p q r s t : ℂ, p * q * r * s * t = q * (p * r * s * t) from fun _ _ _ _ _ => by ring, div_mul_cancel₀ _ this]`.
-/
theorem pinColT_of_pinColL {Ch₀ : ℕ → Type} {A : TwDat I l Z u a Ch₀} {ψ θ x vac c₀ kom dd w Ram rd cK}
    (h : PinColL A (fun _ => id) ψ θ x vac c₀ kom dd w Ram rd cK) (hc : ∀ j, j < B.R.m → c₀ j ≠ 0)
    (hv : ∀ j, j < B.R.m → ∀ α, volLev (x j).vol (A.U j α) ≠ 0) :
    ∃ w', PinColT A ψ θ x vac c₀ kom dd w' Ram rd cK := by
  have hd : ∀ j, j < B.R.m → ∀ α γ, (volLev (x j).vol (A.U j α) : ℂ) * c₀ j * (A.chr (j + 1) (A.xr j α) : ℂ) *
      (A.chr (j + 1) (A.xr (j + 1) γ) : ℂ)⁻¹ ≠ 0 := fun j hj α γ =>
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by exact_mod_cast hv j hj α) (hc j hj)) (Circle.coe_ne_zero _))
      (inv_ne_zero (Circle.coe_ne_zero _))
  refine ⟨fun j α γ => cK j / ((volLev (x j).vol (A.U j α) : ℂ) * c₀ j * (A.chr (j + 1) (A.xr j α) : ℂ) *
      (A.chr (j + 1) (A.xr (j + 1) γ) : ℂ)⁻¹), h.is, h.om, fun j hj α γ => ⟨(h.dat j hj α γ).1, ?_⟩, fun j hj α γ => ?_,
    fun j hj φ => (h.ram j hj φ).trans ⟨fun h => h.1, fun h' => ⟨h', fun c hc => absurd ⟨_, rfl⟩ hc⟩⟩, h.rdq⟩
  · have h2 := (h.dat j hj α γ).2
    convert h2 using 2 with z
    by_cases hz : A.xi j hj α γ z = 0
    · simp only [id]; rw [hz, mul_zero, mul_zero]
    · have e := h.cst j hj α γ ⟨z, hz⟩
      simp only [id] at e ⊢
      congr 1
      rw [div_eq_iff (hd j hj α γ), e]; ring
  · have := hd j hj α γ
    rw [show ∀ p q r s t : ℂ, p * q * r * s * t = q * (p * r * s * t) from fun _ _ _ _ _ => by ring, div_mul_cancel₀ _ this]

/- English proof (translation)
Introduce `h0`. Apply `hK` to reduce the goal to its premises. Rewrite using `[h.cst j hj α γ hz, h0]`. Simplify using the standard rewrite rules.
-/
theorem w_ne_zero {Ch₀ Ch : ℕ → Type} {A : TwDat I l Z u a Ch₀} {ι : ∀ j, Ch j → Ch₀ j}
    {ψ θ x vac c₀ kom dd w Ram rd cK} (h : PinColL A ι ψ θ x vac c₀ kom dd w Ram rd cK) (j) (hj : j + 1 ≤ B.R.m)
    (hK : cK j ≠ 0) (α γ) (hz : ∃ z, A.xi j hj (ι j α) (ι (j + 1) γ) z ≠ 0) : w j α γ ≠ 0 := by
  intro h0
  apply hK
  rw [h.cst j hj α γ hz, h0]; simp

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z))
  (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (k : ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u a))

def movedLev : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X') :=
  (levG _ R.βX (datXP R P t)).comap (MulAut.conj g.bT⁻¹).toMonoidHom

def withTop (ε : ℂ) : ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u a) :=
  { k with eT := fun _ _ _ => Finsupp.single g.bT ε, cP := ε * (volLev g.volT (movedLev R g P t) : ℂ) }

/- English proof (translation)
Assemble the required witnesses or components as `⟨h, fun h => by show (MulAut.conj g.bT⁻¹) h ∈ levG _ R.βX (datXP R P t) ↔ _ rw [MulAut.conj_apply, inv_inv]; rfl, fun _ _ _ => rfl, rfl⟩`.
-/
theorem pinTopL_withTop (h : IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) ((g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _))) (ε : ℂ) :
    PinTopL R g P (t := t) (withTop R g P t k ε) (movedLev R g P t) ε :=
  ⟨h, fun h => by
    show (MulAut.conj g.bT⁻¹) h ∈ levG _ R.βX (datXP R P t) ↔ _
    rw [MulAut.conj_apply, inv_inv]; rfl, fun _ _ _ => rfl, rfl⟩

/- English proof (translation)
The claim follows from `h`.
-/
theorem pinChL_withTop (ε : ℂ) {c₀} {Ch₀ : ℕ → Type} {A : TwDat I l Z u a Ch₀} {ι w} (h : PinChL R g k c₀ A ι w) :
    PinChL R g (withTop R g P t k ε) c₀ A ι w := h

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[h.lev]`. Use `show _ ↔ (MulAut.conj g.bT⁻¹) x ∈ levG _ R.βX (datXP R P t)`. Rewrite using `[MulAut.conj_apply, inv_inv]`. Both sides reduce to the same expression.
-/
theorem pinTopL_lev {UT ε} (h : PinTopL R g P (t := t) k UT ε) : UT = movedLev R g P t := by
  ext x
  rw [h.lev]
  show _ ↔ (MulAut.conj g.bT⁻¹) x ∈ levG _ R.βX (datXP R P t)
  rw [MulAut.conj_apply, inv_inv]; rfl

/- English proof (translation)
Establish `hr` using `h.reads _ le_rfl`. Take `⟨c, rfl⟩` from `hr.onto β`. Take `⟨c', rfl⟩` from `hr.onto β'`. Use `(hr.key c c').2 ⟨(Idx.eq_top c.1 le_rfl).trans (Idx.eq_top c'.1 le_rfl).symm, ?_⟩` and prove the remaining obligations. Establish `e : ∀ q : PtAt B.R I.sel (I.tup a) (I.cst a) u B.R.m, cosetIn q = fun _ => ∅` using `fun q => by`.

Establish `h2` using `q.2`. Establish `h3 : q.1.2 = ∅`. Use `ysAt_ys_of_ne (R := B.R) I.sel (I.tup a) (I.cst a) (j := B.R.m) (Nat.succ_ne_self _) q.1.1.deco.1.N` as an intermediate fact. Conclude with `Set.mem_singleton_iff.1 (this ▸ h2)`. Use function extensionality and compare the values at `P`.

Simplify using `[cosetIn, h3]`. Conclude with `(e _).trans (e _).symm`.
-/
theorem top_subsingleton {Ch₀ : ℕ → Type} {A : TwDat I l Z u a Ch₀} (h : A.Is) (β β' : Ch₀ B.R.m) : β = β' := by
  have hr := h.reads _ le_rfl
  obtain ⟨c, rfl⟩ := hr.onto β
  obtain ⟨c', rfl⟩ := hr.onto β'
  refine (hr.key c c').2 ⟨(Idx.eq_top c.1 le_rfl).trans (Idx.eq_top c'.1 le_rfl).symm, ?_⟩
  have e : ∀ q : PtAt B.R I.sel (I.tup a) (I.cst a) u B.R.m, cosetIn q = fun _ => ∅ := fun q => by
    have h2 := q.2
    have h3 : q.1.2 = ∅ := by
      have := ysAt_ys_of_ne (R := B.R) I.sel (I.tup a) (I.cst a) (j := B.R.m) (Nat.succ_ne_self _) q.1.1.deco.1.N
      exact Set.mem_singleton_iff.1 (this ▸ h2)
    funext P
    simp [cosetIn, h3]
  exact (e _).trans (e _).symm

section Emb
open GlobalTheory.MixModel
variable {D : D7}

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Use `(Examples₂.stdSpace_gram_apply hs n (fun _ => false) n 0 i j).trans ?_` and prove the remaining obligations. Distinguish the cases in `h : i = j`. Substitute `h; rw [Matrix.one_apply_eq]; exact (if_pos rfl).trans (by simp [Examples₂.sgn])` using the available equality. Rewrite using `[Matrix.one_apply_ne h]`.

Conclude with `if_neg h`.
-/
theorem gram_pos {E : Type} [Field E] [NumberField E] [StarRing E] (hs : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (n : ℕ) :
    (Examples₂.posSpace hs n).gram = 1 := by
  funext i j
  refine (Examples₂.stdSpace_gram_apply hs n (fun _ => false) n 0 i j).trans ?_
  by_cases h : i = j
  · subst h; rw [Matrix.one_apply_eq]; exact (if_pos rfl).trans (by simp [Examples₂.sgn])
  · rw [Matrix.one_apply_ne h]; exact if_neg h

/- English proof (translation)
Establish `h1` using `rankP D`. Establish `h2` using `rankN D D.R.m le_rfl`. Establish `h3 : 0 < D.R.N D.R.m`. Use `D.R.two_le_m` as an intermediate fact. Establish `h4 : D.R.m * (D.R.t + 1) = D.R.m * D.R.t + D.R.m` using `by ring`.

Simplify using `only [Ranks.N]`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.
-/
theorem rk_top (D : D7) : D.sp.X'.rank + 1 = (D.sp.X D.R.m).rank := by
  have h1 := rankP D
  have h2 := rankN D D.R.m le_rfl
  have h3 : 0 < D.R.N D.R.m := by
    have := D.R.two_le_m
    have h4 : D.R.m * (D.R.t + 1) = D.R.m * D.R.t + D.R.m := by ring
    simp only [Ranks.N]; omega
  omega

def topDec (hG : (D.sp.X D.R.m).gram = 1) (hG' : D.sp.X'.gram = 1) :
    OrthDec (D.sp.X D.R.m) D.sp.X' (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1) where
  iA := Matrix.of fun b a => if (a : ℕ) = b then 1 else 0
  iB := Matrix.of fun b _ => if D.sp.X'.rank = b then 1 else 0
  isoA := by
    have := rk_top D
    rw [hG, hG', Matrix.mul_one]
    funext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single (⟨i, by omega⟩ : Fin (D.sp.X D.R.m).rank)]
    · simp [Matrix.one_apply, Fin.ext_iff, eq_comm]
    · intro b _ hb
      have : ¬ (i : ℕ) = b := fun e => hb (Fin.ext e.symm)
      simp [this]
    · simp
  isoB := by
    have := rk_top D
    rw [hG, Matrix.mul_one]
    funext i j
    have h : (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1).gram i j = 1 := by
      rw [gram_pos, Subsingleton.elim (α := Fin 1) i j, Matrix.one_apply_eq]
    rw [h, Matrix.mul_apply, Finset.sum_eq_single (⟨D.sp.X'.rank, by omega⟩ : Fin (D.sp.X D.R.m).rank)]
    · simp
    · intro b _ hb
      have : ¬ D.sp.X'.rank = b := fun e => hb (Fin.ext e.symm)
      simp [this]
    · simp
  orth := by
    rw [hG, Matrix.mul_one]
    funext i j
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    have := j.2
    by_cases hb : D.sp.X'.rank = b
    · have : ¬ (j : ℕ) = b := by omega
      simp [this]
    · simp [hb]
  rank_add := rk_top D

/- English proof (translation)
Establish `h0` using `rk_top D`. Establish `h1` using `rankP D`. Establish `ha` using `a.2`. Establish `e : ((D.sp.X'.frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)).symm (Pi.single a 1)) = D.sp.X'.frame (Fin.cast h1.symm a)`. Rewrite using `[LinearEquiv.symm_apply_eq]`.

Use function extensionality and compare the values at `k`. Simplify using `[Finsupp.single_apply, Pi.single_apply, Fin.ext_iff, eq_comm]`. Rewrite using `[iXm, LinearMap.toMatrix'_apply, iXc]`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[e, hi _ ⟨a, by omega⟩ rfl]`.

Simplify using `[Finsupp.single_apply, Fin.ext_iff]`.
-/
theorem iXm_eq (hi : ∀ (a : Fin D.sp.X'.rank) (b : Fin (D.sp.X D.R.m).rank), (a : ℕ) = b →
    D.sp.iX' (D.sp.X'.frame a) = (D.sp.X D.R.m).frame b) (b a) : iXm D b a = if (a : ℕ) = b then 1 else 0 := by
  have h0 := rk_top D
  have h1 := rankP D
  have ha := a.2
  have e : ((D.sp.X'.frame.equivFun.trans
      (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)).symm (Pi.single a 1)) =
      D.sp.X'.frame (Fin.cast h1.symm a) := by
    rw [LinearEquiv.symm_apply_eq]
    funext k
    simp [Finsupp.single_apply, Pi.single_apply, Fin.ext_iff, eq_comm]
  rw [iXm, LinearMap.toMatrix'_apply, iXc]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [e, hi _ ⟨a, by omega⟩ rfl]
  simp [Finsupp.single_apply, Fin.ext_iff]

/- English proof (translation)
Introduce `h`. Establish `h0` using `rk_top D`. Establish `h1` using `rankP D`. Establish `h2` using `rankN D D.R.m le_rfl`. Establish `eA : (iXm D).map (incA D) = ((topDec hG hG').jA).reindex (finCongr h2) (finCongr h1)`.

Use extensionality with `b a`. Simplify using `[iXm_eq hi, OrthDec.jA, rat, topDec]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[eA]`. Use `(topDec hG hG').emb_jA h 1` as an intermediate fact.

Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]`. Conclude with `congrArg (fun M => Matrix.submatrix M _ _) this`. Use `(topDec hG hG').emb_jB h 1` as an intermediate fact. Rewrite `this` using `[mt_one, Matrix.mul_one]`. Use function extensionality and compare the values at `b`.

Establish `e` using `congrFun (congrFun this (Fin.cast h2.symm b)) (0 : Fin 1)`. Establish `ez : (fun a : Fin (D.R.N D.R.m) => incA D (if a.1 + 1 = D.R.N D.R.m then c else 0)) = fun a => (topDec hG hG').jB (Fin.cast h2.symm a) (0 : Fin 1) * incA D c`. Use function extensionality and compare the values at `a`. Establish `: (a.1 + 1 = D.R.N D.R.m) ↔ D.sp.X'.rank = a` using `by omega`. Use `show _ = incA D (if D.sp.X'.rank = a then 1 else 0) * incA D c`.

Rewrite using `[← map_mul]`. Distinguish the cases in `ha : D.sp.X'.rank = a`. Rewrite using `[if_pos ha, if_pos (this.2 ha), one_mul]`. Rewrite using `[if_neg ha, if_neg (fun h => ha (this.1 h)), zero_mul]`. Establish `ez'` using `congrFun ez b`.

Rewrite using `[ez, ez', ← e]`. Use `Eq.trans ?_ (congrArg (· * incA D c) Matrix.mul_apply).symm` and prove the remaining obligations. Use `Eq.trans ?_ (Finset.sum_mul _ _ _).symm` and prove the remaining obligations. Use `Fintype.sum_equiv (finCongr h2.symm) _ _ fun x => ?_` and prove the remaining obligations. Conclude with `(mul_assoc _ _ _).symm`.
-/
theorem isEmbTop_topDec (hG : (D.sp.X D.R.m).gram = 1) (hG' : D.sp.X'.gram = 1)
    (hi : ∀ (a : Fin D.sp.X'.rank) (b : Fin (D.sp.X D.R.m).rank), (a : ℕ) = b →
      D.sp.iX' (D.sp.X'.frame a) = (D.sp.X D.R.m).frame b)
    (c : D.host.E) : IsEmbTop (D := D) (fun j => if j.1 + 1 = D.R.N D.R.m then c else 0)
      ((topDec hG hG').emb.comp (MonoidHom.inl _ _)) := by
  intro h
  have h0 := rk_top D
  have h1 := rankP D
  have h2 := rankN D D.R.m le_rfl
  have eA : (iXm D).map (incA D) = ((topDec hG hG').jA).reindex (finCongr h2) (finCongr h1) := by
    ext b a
    simp [iXm_eq hi, OrthDec.jA, rat, topDec]
  constructor
  · rw [eA]
    have := (topDec hG hG').emb_jA h 1
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    exact congrArg (fun M => Matrix.submatrix M _ _) this
  · have := (topDec hG hG').emb_jB h 1
    rw [mt_one, Matrix.mul_one] at this
    funext b
    have e := congrFun (congrFun this (Fin.cast h2.symm b)) (0 : Fin 1)
    have ez : (fun a : Fin (D.R.N D.R.m) => incA D (if a.1 + 1 = D.R.N D.R.m then c else 0)) =
        fun a => (topDec hG hG').jB (Fin.cast h2.symm a) (0 : Fin 1) * incA D c := by
      funext a
      have : (a.1 + 1 = D.R.N D.R.m) ↔ D.sp.X'.rank = a := by omega
      show _ = incA D (if D.sp.X'.rank = a then 1 else 0) * incA D c
      rw [← map_mul]
      by_cases ha : D.sp.X'.rank = a
      · rw [if_pos ha, if_pos (this.2 ha), one_mul]
      · rw [if_neg ha, if_neg (fun h => ha (this.1 h)), zero_mul]
    have ez' := congrFun ez b
    rw [ez, ez', ← e]
    refine Eq.trans ?_ (congrArg (· * incA D c) Matrix.mul_apply).symm
    refine Eq.trans ?_ (Finset.sum_mul _ _ _).symm
    refine Fintype.sum_equiv (finCongr h2.symm) _ _ fun x => ?_
    exact (mul_assoc _ _ _).symm
end Emb

/- English proof (translation)
Take `⟨hs, h1, h2, -⟩` from `hI.spaces`. Establish `key : ∀ S : HSp (I.rec7 l Z), ∀ n, S = Examples₂.posSpace hs n → S.gram = 1` using `by rintro _ n rfl; exact gram_pos hs n`. Establish `gen : ∀ (D : D7) (hG : (D.sp.X D.R.m).gram = 1) (hG' : D.sp.X'.gram = 1) (hi : ∀ (a : Fin D.sp.X'.rank) (b : Fin (D.sp.X D.R.m).rank), (a : ℕ) = b → D.sp.iX' (D.sp.X'.frame a) = (D.sp.X D.R.m).frame b) (c : D.host.E), ∃ (Lz : HSp D) (oT : ∀ n, n = D.R.m → GlobalTheory.MixModel.Or …` using `D) (fun j => if j.1 + 1 = D.R.N D.R.m then c else 0) ((oT D.R.m rfl).emb.comp (MonoidHom.inl _ _)) := fun D hG hG' hi c => ⟨_, fun n h => Eq.rec (motive := fun n _ => GlobalTheory.MixModel.OrthDec (D.sp.X n) _ _) (topDec hG hG') h.symm, isEmbTop_topDec hG hG' hi c⟩`. Conclude with `gen (I.rec7 l Z) (key _ _ (h1 _)) (key _ _ h2) hP.iX _`.
-/
theorem exists_emb (hI : I.Ok) (hP : TC.Pins B X) :
    ∃ (Lz : HSp (I.rec7 l Z)) (oT : ∀ n, n = (I.rec7 l Z).R.m → GlobalTheory.MixModel.OrthDec ((I.rec7 l Z).sp.X n) (I.rec7 l Z).sp.X' Lz),
      IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) ((oT B.R.m rfl).emb.comp (MonoidHom.inl _ _)) := by
  obtain ⟨hs, h1, h2, -⟩ := hI.spaces
  have key : ∀ S : HSp (I.rec7 l Z), ∀ n, S = Examples₂.posSpace hs n → S.gram = 1 := by rintro _ n rfl; exact gram_pos hs n
  have gen : ∀ (D : D7) (hG : (D.sp.X D.R.m).gram = 1) (hG' : D.sp.X'.gram = 1)
    (hi : ∀ (a : Fin D.sp.X'.rank) (b : Fin (D.sp.X D.R.m).rank), (a : ℕ) = b →
      D.sp.iX' (D.sp.X'.frame a) = (D.sp.X D.R.m).frame b) (c : D.host.E),
      ∃ (Lz : HSp D) (oT : ∀ n, n = D.R.m → GlobalTheory.MixModel.OrthDec (D.sp.X n) D.sp.X' Lz),
        IsEmbTop (D := D) (fun j => if j.1 + 1 = D.R.N D.R.m then c else 0) ((oT D.R.m rfl).emb.comp (MonoidHom.inl _ _)) :=
    fun D hG hG' hi c => ⟨_, fun n h => Eq.rec (motive := fun n _ => GlobalTheory.MixModel.OrthDec (D.sp.X n) _ _) (topDec hG hG') h.symm,
      isEmbTop_topDec hG hG' hi c⟩
  exact gen (I.rec7 l Z) (key _ _ (h1 _)) (key _ _ h2) hP.iX _

@[reducible] def reTop {D : D7} (g : GlobalTheory.Fam.Geo D) (Lz : HSp D) (oT : ∀ n, n = D.R.m → GlobalTheory.MixModel.OrthDec (D.sp.X n) D.sp.X' Lz) :
    GlobalTheory.Fam.Geo D := { g with Lz := Lz, oT := oT }

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨Lz, oT, h⟩` from `exists_emb (l := l) (Z := Z) (u := u) hI hP`. Conclude with `⟨Lz, oT, pinTopL_withTop R (reTop g Lz oT) P t k h ε⟩`.
-/
theorem exists_pinTopL (hI : I.Ok) (hP : TC.Pins B X) {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL]
    (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T)
    (k : ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u a)) (ε : ℂ) :
    ∃ Lz oT, PinTopL R (reTop g Lz oT) P (t := t) (withTop R (reTop g Lz oT) P t k ε) (movedLev R (reTop g Lz oT) P t) ε := by
  obtain ⟨Lz, oT, h⟩ := exists_emb (l := l) (Z := Z) (u := u) hI hP
  exact ⟨Lz, oT, pinTopL_withTop R (reTop g Lz oT) P t k h ε⟩

end GlobalTheory.AdForm.LiveModel
