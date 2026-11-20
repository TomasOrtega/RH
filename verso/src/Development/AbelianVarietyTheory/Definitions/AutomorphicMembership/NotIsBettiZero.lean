import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoordAtConstMulIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageConnectedComponentMem

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.Cartier
open GlobalTheory.TrueCx GlobalTheory.FlatLine

namespace GlobalTheory.ShFam.Pad

section Expo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

open Classical in

/- English proof (translation)
Take `⟨ρ, i⟩` from `z`. Establish `hne : conjEmb τ.1 ≠ τ.1` using `fun e => GlobalTheory.AllWt.conj_not_mem τ (e.symm ▸ τ.2)`. Establish `hp : Dw.mult τ.1 = Dw.p` using `if_pos τ.2`. Establish `hq : Dw.mult (conjEmb τ.1) = Dw.q` using `if_neg (GlobalTheory.AllWt.conj_not_mem τ)`. Establish `hl : ∀ (ρ' : E →+* ℂ) (k : ℕ), letterOf Dw (.inl (ρ', k)) = some ⟨ρ, i⟩ ↔ ρ' = ρ ∧ k = i` using `fun ρ' k => by`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Simplify using `only [letterOf] at h`. Use `split_ifs at h`. Take `⟨rfl, h2⟩` from `Sigma.mk.inj_iff.1 (Option.some.inj h)`.

Conclude with `⟨rfl, congrArg Fin.val (eq_of_heq h2)⟩`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `dif_pos i.2`. Apply the tactic sequence `have h1 : expo Dw (detSym Dw a R τ.1) ⟨ρ, i⟩ = ∑ k ∈ Finset.range (Dw.p + Dw.q), expo Dw (rootSym Dw a R τ.1 k) ⟨ρ, i⟩ := (Finsupp.sum_finsetSum_index (fun _ => by simp) fun _ _ _ => by split_ifs <;> simp).symm`. Establish `h2 : ∀ k, expo Dw (rootSym Dw a R τ.1 k) ⟨ρ, i⟩ = if k < Dw.p then (if τ.1 = ρ ∧ k = i then 1 else 0) else if conjEmb τ.1 = ρ ∧ Dw.p + Dw.q - 1 - k = i then -1 else 0` using `fun k => by`.

Unfold `expo rootSym`. Apply the tactic sequence `split_ifs <;> rw [Finsupp.sum_single_index (by simp)] <;> simp only [hl] <;> simp [*]`. Establish `hi` using `i.2`. Simplify using `only [h1, h2]`. Use `split_ifs with e1 e2`.

Substitute `e1` using the available equality. Rewrite using `[Finset.sum_eq_single (i : ℕ) (fun k _ hk => by simp [hk, hne]) fun h => absurd (Finset.mem_range.2 (by omega)) h, if_pos (by omega), if_pos ⟨rfl, rfl⟩]`. Substitute `e2` using the available equality. Rewrite using `[Finset.sum_eq_single (Dw.p + Dw.q - 1 - i) (fun k hk hk' => by`. Use `Finset.mem_range.1 hk` as an intermediate fact.

Use `split_ifs with b1 b2 b3`. Conclude with `absurd b2.1.symm hne`. Both sides reduce to the same expression. Use linear arithmetic over natural numbers and integers. Use the proof step `rfl) fun h => absurd (Finset.mem_range.2 (by omega)) h,`.

Use `if_neg (by omega), if_pos ⟨rfl, by omega⟩]`. Conclude with `Finset.sum_eq_zero fun k _ => by simp [Ne.symm e1, Ne.symm e2]`.
-/
theorem expo_detSym (τ : GlobalTheory.AllWt.Psi H) (a : ℕ → Bool) (R : Option ℝ) (z : Letter Dw) :
    expo Dw (detSym Dw a R τ.1) z = if z.1 = τ.1 then 1 else if z.1 = conjEmb τ.1 then -1 else 0 := by
  obtain ⟨ρ, i⟩ := z
  have hne : conjEmb τ.1 ≠ τ.1 := fun e => GlobalTheory.AllWt.conj_not_mem τ (e.symm ▸ τ.2)
  have hp : Dw.mult τ.1 = Dw.p := if_pos τ.2
  have hq : Dw.mult (conjEmb τ.1) = Dw.q := if_neg (GlobalTheory.AllWt.conj_not_mem τ)
  have hl : ∀ (ρ' : E →+* ℂ) (k : ℕ), letterOf Dw (.inl (ρ', k)) = some ⟨ρ, i⟩ ↔ ρ' = ρ ∧ k = i := fun ρ' k => by
    constructor
    · intro h
      simp only [letterOf] at h
      split_ifs at h
      obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 (Option.some.inj h)
      exact ⟨rfl, congrArg Fin.val (eq_of_heq h2)⟩
    · rintro ⟨rfl, rfl⟩
      exact dif_pos i.2
  have h1 : expo Dw (detSym Dw a R τ.1) ⟨ρ, i⟩ = ∑ k ∈ Finset.range (Dw.p + Dw.q), expo Dw (rootSym Dw a R τ.1 k) ⟨ρ, i⟩ :=
    (Finsupp.sum_finsetSum_index (fun _ => by simp) fun _ _ _ => by split_ifs <;> simp).symm
  have h2 : ∀ k, expo Dw (rootSym Dw a R τ.1 k) ⟨ρ, i⟩ = if k < Dw.p then (if τ.1 = ρ ∧ k = i then 1 else 0)
      else if conjEmb τ.1 = ρ ∧ Dw.p + Dw.q - 1 - k = i then -1 else 0 := fun k => by
    unfold expo rootSym
    split_ifs <;> rw [Finsupp.sum_single_index (by simp)] <;> simp only [hl] <;> simp [*]
  have hi := i.2
  simp only [h1, h2]
  split_ifs with e1 e2
  · subst e1
    rw [Finset.sum_eq_single (i : ℕ) (fun k _ hk => by simp [hk, hne]) fun h => absurd (Finset.mem_range.2 (by omega)) h,
      if_pos (by omega), if_pos ⟨rfl, rfl⟩]
  · subst e2
    rw [Finset.sum_eq_single (Dw.p + Dw.q - 1 - i) (fun k hk hk' => by
        have := Finset.mem_range.1 hk
        split_ifs with b1 b2 b3
        · exact absurd b2.1.symm hne
        · rfl
        · omega
        · rfl) fun h => absurd (Finset.mem_range.2 (by omega)) h,
      if_neg (by omega), if_pos ⟨rfl, by omega⟩]
  · exact Finset.sum_eq_zero fun k _ => by simp [Ne.symm e1, Ne.symm e2]

/- English proof (translation)
Use function extensionality and compare the values at `⟨ρ, i⟩`. Rewrite using `[expo_detSym]`. Use `show _ = -(GlobalTheory.AllWt.wtOf Dw (flatWt Dw τ) 0).1 (ρ, i)`. Distinguish the cases in `h : ρ (H.rt : E) = H.rt0`. Establish `h1 : ρ ≠ conjEmb τ.1` using `fun e => GlobalTheory.AllWt.conj_not_mem τ (e ▸ h)`.

Rewrite using `[GlobalTheory.AllWt.wtOf_big (flatWt Dw τ) 0 ⟨ρ, h⟩ i ((if_pos h : Dw.mult ρ = Dw.p) ▸ i.2)]`. Apply the tactic sequence `by_cases e : ρ = τ.1 <;> simp [flatWt, parWt, Subtype.ext_iff, e, h1]`. Establish `h1 : ρ ≠ τ.1` using `fun e => h (e ▸ τ.2)`. Use `GlobalTheory.AllWt.wtOf_small (flatWt Dw τ) 0 ⟨_, GlobalTheory.AllWt.conj_mem h⟩ i ((if_neg h : Dw.mult ρ = Dw.q) ▸ i.2)` as an intermediate fact. Simplify using `only [GlobalTheory.AllWt.conjEmb_conjEmb] at this`.

Rewrite using `[this]`. Establish `h2 : conjEmb ρ = τ.1 ↔ ρ = conjEmb τ.1` using `⟨fun e => by rw [← e, GlobalTheory.AllWt.conjEmb_conjEmb], fun e => by rw [e, GlobalTheory.AllWt.conjEmb_conjEmb]⟩`. Establish `h3 : (⟨_, GlobalTheory.AllWt.conj_mem h⟩ : GlobalTheory.AllWt.Psi H) = τ ↔ ρ = conjEmb τ.1` using `Subtype.ext_iff.trans h2`. Simplify using `only [flatWt, parWt, if_neg h1]`. Distinguish the cases in `e : ρ = conjEmb τ.1`.

Rewrite using `[if_pos e, if_pos (h3.2 e)]`. Both sides reduce to the same expression. Rewrite using `[if_neg e, if_neg (mt h3.1 e)]`. Both sides reduce to the same expression.
-/
theorem expo_detSym_eq (τ : GlobalTheory.AllWt.Psi H) (a : ℕ → Bool) (R : Option ℝ) :
    expo Dw (detSym Dw a R τ.1) = fun z => -GlobalTheory.AllWt.exOf Dw (flatWt Dw τ) 0 (some z) := by
  funext ⟨ρ, i⟩
  rw [expo_detSym]
  show _ = -(GlobalTheory.AllWt.wtOf Dw (flatWt Dw τ) 0).1 (ρ, i)
  by_cases h : ρ (H.rt : E) = H.rt0
  · have h1 : ρ ≠ conjEmb τ.1 := fun e => GlobalTheory.AllWt.conj_not_mem τ (e ▸ h)
    rw [GlobalTheory.AllWt.wtOf_big (flatWt Dw τ) 0 ⟨ρ, h⟩ i ((if_pos h : Dw.mult ρ = Dw.p) ▸ i.2)]
    by_cases e : ρ = τ.1 <;> simp [flatWt, parWt, Subtype.ext_iff, e, h1]
  · have h1 : ρ ≠ τ.1 := fun e => h (e ▸ τ.2)
    have := GlobalTheory.AllWt.wtOf_small (flatWt Dw τ) 0 ⟨_, GlobalTheory.AllWt.conj_mem h⟩ i ((if_neg h : Dw.mult ρ = Dw.q) ▸ i.2)
    simp only [GlobalTheory.AllWt.conjEmb_conjEmb] at this
    rw [this]
    have h2 : conjEmb ρ = τ.1 ↔ ρ = conjEmb τ.1 :=
      ⟨fun e => by rw [← e, GlobalTheory.AllWt.conjEmb_conjEmb], fun e => by rw [e, GlobalTheory.AllWt.conjEmb_conjEmb]⟩
    have h3 : (⟨_, GlobalTheory.AllWt.conj_mem h⟩ : GlobalTheory.AllWt.Psi H) = τ ↔ ρ = conjEmb τ.1 := Subtype.ext_iff.trans h2
    simp only [flatWt, parWt, if_neg h1]
    by_cases e : ρ = conjEmb τ.1
    · rw [if_pos e, if_pos (h3.2 e)]; rfl
    · rw [if_neg e, if_neg (mt h3.1 e)]; rfl

end Expo

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (Φ : s.Flag) (L : CmList A)

/- English proof (translation)
Use `letI := κ.σ₀.toAlgebra`. Set `P : FrPt s.Xo κ.c ℂ` to `(s.U κ.σ₀).un k x`. Establish `key : ∀ (x' : Sp ℂ ⟶ s.T.Z.X) (g : EigFrame s.T.Z (algebraMap κ.c.F ℂ) x'), x' = (GlobalTheory.AllWt.ptF P ≫ s.T.Z.jQ) ≫ genι s.T.Z → ∃ (i : s.Comp) (p : Sp ℂ ⟶ (Φ.C i).Y.X), p ≫ (Φ.C i).π = GlobalTheory.AllWt.ptF P ≫ s.T.Z.jQ ∧ (Φ.C i).Carries p g`. Introduce and unpack `_ g rfl`. Take `⟨⟨i, p⟩, h, -⟩` from `Φ.lifts ℂ _ _ (by rw [Category.assoc, s.T.Z.jQ_over, Descent.ptF_snd]) g`.

Conclude with `⟨i, p, h⟩`. Take `⟨i, p, hp, hc⟩` from `key _ (frameOf s.T.Z P) (Category.assoc _ _ _).symm`. Set `pt : Sp ℂ` to `IsLocalRing.closedPoint ℂ`. Establish `hs : ∀ a : Sp ℂ, a = pt` using `fun a => Subsingleton.elim (α := PrimeSpectrum ℂ) _ _`. Choose the witnesses or unpack the hypotheses as in `rfl : i = k := by`.

Use `(PtComp.existsUnique_onComp s ((GlobalTheory.AllWt.ptF P ≫ s.T.Z.jQ) pt)).unique ⟨⟨_, ReciprocityTheory.ChartRestriction.G.AR.Up.KU.orth_dom _ (isOrth_x0F _)⟩, fun a => ?_⟩ ⟨x, fun a => by rw [hs a]; exact mem_connectedComponent⟩` and prove the remaining obligations. Conclude with `(isPreconnected_range (Φ.C i).π.continuous).subset_connectedComponent ⟨p pt, by rw [← hp]; rfl⟩ (Φ.label i _ a)`. Conclude with `⟨p, hp, hc⟩`.
-/
theorem carriedC_un (k : s.Comp) (x : ((s.U κ.σ₀).X k).dom) : CarriedC (Φ.C k) ((s.U κ.σ₀).un k x) := by
  letI := κ.σ₀.toAlgebra
  let P : FrPt s.Xo κ.c ℂ := (s.U κ.σ₀).un k x
  have key : ∀ (x' : Sp ℂ ⟶ s.T.Z.X) (g : EigFrame s.T.Z (algebraMap κ.c.F ℂ) x'),
      x' = (GlobalTheory.AllWt.ptF P ≫ s.T.Z.jQ) ≫ genι s.T.Z → ∃ (i : s.Comp) (p : Sp ℂ ⟶ (Φ.C i).Y.X),
        p ≫ (Φ.C i).π = GlobalTheory.AllWt.ptF P ≫ s.T.Z.jQ ∧ (Φ.C i).Carries p g := by
    rintro _ g rfl
    obtain ⟨⟨i, p⟩, h, -⟩ := Φ.lifts ℂ _ _ (by rw [Category.assoc, s.T.Z.jQ_over, Descent.ptF_snd]) g
    exact ⟨i, p, h⟩
  obtain ⟨i, p, hp, hc⟩ := key _ (frameOf s.T.Z P) (Category.assoc _ _ _).symm
  let pt : Sp ℂ := IsLocalRing.closedPoint ℂ
  have hs : ∀ a : Sp ℂ, a = pt := fun a => Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  obtain rfl : i = k := by
    refine (PtComp.existsUnique_onComp s ((GlobalTheory.AllWt.ptF P ≫ s.T.Z.jQ) pt)).unique
      ⟨⟨_, ReciprocityTheory.ChartRestriction.G.AR.Up.KU.orth_dom _ (isOrth_x0F _)⟩, fun a => ?_⟩
      ⟨x, fun a => by rw [hs a]; exact mem_connectedComponent⟩
    exact (isPreconnected_range (Φ.C i).π.continuous).subset_connectedComponent ⟨p pt, by rw [← hp]; rfl⟩
      (Φ.label i _ a)
  exact ⟨p, hp, hc⟩

abbrev cmAt (k : s.Comp) : D.what₂.Tau ≃ ((s.U κ.σ₀).X k).Ψ := cmEquiv _ s.isUnf L.ψ k

def bettiCo (k : s.Comp) (τ : D.what₂.Tau) (x : Frame ((s.U κ.σ₀).X k).Ψ N) : ℂ :=
  (hodgeC ((s.U κ.σ₀).X k) (cmAt s L k) τ : ℂ) ^ S.Dw.q * horizGen (cmAt s L k τ) x

/- English proof (translation)
The claim follows from `mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.2 (hodgeC_pos _ _ _).ne')) (inv_ne_zero (x.2 _).1)`.
-/
theorem bettiCo_ne_zero (k : s.Comp) (τ : D.what₂.Tau) (x : ((s.U κ.σ₀).X k).dom) : bettiCo s L k τ x.1 ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.2 (hodgeC_pos _ _ _).ne')) (inv_ne_zero (x.2 _).1)

/- English proof (translation)
Simplify using `[bettiCo, hq, horizGen]`.
-/
example (hq : S.Dw.q = 0) (k : s.Comp) (τ : D.what₂.Tau) (x : Frame ((s.U κ.σ₀).X k).Ψ N) :
    bettiCo s L k τ x = (mat x (cmAt s L k τ)).det⁻¹ := by simp [bettiCo, hq, horizGen]

abbrev detEx (S : Sig A N j) (τ : D.what₂.Tau) : Letter S.Dw → ℤ :=
  expo S.Dw (detSym S.Dw (fun _ => false) none (DV.tauEmb D τ))

/- English proof (translation)
Rewrite using `[← expo_detSym_eq S.Dw (L.ψ τ) (fun _ => false) none, L.ψ_val]`.
-/
theorem detEx_eq (S : Sig A N j) (L : CmList A) (τ : D.what₂.Tau) :
    detEx S τ = fun z => -GlobalTheory.AllWt.exOf S.Dw (flatWt S.Dw (L.ψ τ)) 0 (some z) := by
  rw [← expo_detSym_eq S.Dw (L.ψ τ) (fun _ => false) none, L.ψ_val]

def IsBetti (k : s.Comp) (τ : D.what₂.Tau) (σ : (Φ.C k).Y.Fn) (b : ℂˣ) : Prop :=
  ∀ (x : ((s.U κ.σ₀).X k).dom) (a : ℂ),
    CoordAtC (Φ.C k) ((s.U κ.σ₀).un k x) (detEx S τ) σ a ↔ a = b * bettiCo s L k τ x.1

open Classical in

def flBetti (k : s.Comp) (τ : D.what₂.Tau) : ℂˣ :=
  if h : ∃ b, IsBetti s Φ L k τ (flatSec s Φ k τ) b then h.choose else 1

variable {s Φ L} {k : s.Comp} {τ : D.what₂.Tau} {σ : (Φ.C k).Y.Fn} {b b' : ℂˣ}

/- English proof (translation)
The claim follows from `(h x _).2 rfl`.
-/
theorem IsBetti.coordAtC (h : IsBetti s Φ L k τ σ b) (x : ((s.U κ.σ₀).X k).dom) :
    CoordAtC (Φ.C k) ((s.U κ.σ₀).un k x) (detEx S τ) σ (b * bettiCo s L k τ x.1) := (h x _).2 rfl

/- English proof (translation)
The claim follows from `have x : ((s.U κ.σ₀).X k).dom := ⟨_, ReciprocityTheory.ChartRestriction.G.AR.Up.KU.orth_dom _ (isOrth_x0F _)⟩ Units.ext (mul_right_cancel₀ (bettiCo_ne_zero s L k τ x) ((h' x _).1 (h.coordAtC x)))`.
-/
theorem IsBetti.unique (h : IsBetti s Φ L k τ σ b) (h' : IsBetti s Φ L k τ σ b') : b = b' :=
  have x : ((s.U κ.σ₀).X k).dom := ⟨_, ReciprocityTheory.ChartRestriction.G.AR.Up.KU.orth_dom _ (isOrth_x0F _)⟩
  Units.ext (mul_right_cancel₀ (bettiCo_ne_zero s L k τ x) ((h' x _).1 (h.coordAtC x)))

/- English proof (translation)
Introduce `x z` and use `by letI := κ.σ₀.toAlgebra refine (coordAt_const_mul_iff (k := ℂ) ha).trans ((h x _).trans ?_) show κ.σ₀ a⁻¹ * z = _ ↔ z = κ.σ₀ a * b * _ rw [map_inv₀, inv_mul_eq_iff_eq_mul₀ ((map_ne_zero _).2 ha), mul_assoc]`.
-/
theorem IsBetti.const_mul (h : IsBetti s Φ L k τ σ b) {a : κ.c.F} (ha : a ≠ 0) :
    IsBetti s Φ L k τ (constF κ.e (Φ.C k).Y a * σ) (Units.mk0 (κ.σ₀ a) ((map_ne_zero _).2 ha) * b) := fun x z => by
  letI := κ.σ₀.toAlgebra
  refine (coordAt_const_mul_iff (k := ℂ) ha).trans ((h x _).trans ?_)
  show κ.σ₀ a⁻¹ * z = _ ↔ z = κ.σ₀ a * b * _
  rw [map_inv₀, inv_mul_eq_iff_eq_mul₀ ((map_ne_zero _).2 ha), mul_assoc]

/- English proof (translation)
Rewrite using `[flBetti, dif_pos h]`. Conclude with `h.choose_spec`.
-/
theorem isBetti_flBetti (h : ∃ b, IsBetti s Φ L k τ (flatSec s Φ k τ) b) :
    IsBetti s Φ L k τ (flatSec s Φ k τ) (flBetti s Φ L k τ) := by
  rw [flBetti, dif_pos h]; exact h.choose_spec

end GlobalTheory.ShFam.Pad
