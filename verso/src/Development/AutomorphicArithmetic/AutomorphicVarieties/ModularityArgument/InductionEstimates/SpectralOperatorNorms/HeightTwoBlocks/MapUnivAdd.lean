import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.Blo
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.NearBlo
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.ResTyp

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Fx UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.BW

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {S : Set (BW.Pl E)}

private abbrev Pts (E : Type) [Field E] [NumberField E] : Type :=
  ((E →+* ℂ) → Multiset ℂ) → (BW.Pl E → Multiset ℂ) → Prop

private def key {n : ℕ} (d : Dat S n) : ℕ × Pts E := (d.len, d.On)

private def step (S : Set (BW.Pl E)) (r : ℕ) (p : ((E →+* ℂ) → Fin r → ℂ) × (BW.Pl E → Multiset ℂˣ))
    (q : ℕ × Pts E) : ℕ × Pts E :=
  (q.1 + 1, fun Λ t => ∃ (c : ℂ) (Λ' : (E →+* ℂ) → Multiset ℂ) (t' : BW.Pl E → Multiset ℂ), q.2 Λ' t' ∧
    (∀ τ, Λ τ = (Finset.univ.val.map fun i => p.1 τ i + c) + Λ' τ) ∧
    ∀ w ∉ S, t w = ((p.2 w).map fun x : ℂˣ => (x : ℂ) * ((Formalism.UG.qV E w : ℕ) : ℂ) ^ (-c)) + t' w)

open Classical in

private noncomputable def par {r : ℕ} (b : Blo S r) : ((E →+* ℂ) → Fin r → ℂ) × (BW.Pl E → Multiset ℂˣ) :=
  (b.Λ, fun w => if w ∈ S then 0 else b.sat w)

/- English proof (translation)
Establish `key : ∀ {m : ℕ} (g : Fin m → α), Finset.univ.val.map g = ∑ i, ({g i} : Multiset α)`. Introduce `m g`. Establish `e : (Finset.univ.val.map fun i => ({g i} : Multiset α)) = (Finset.univ.val.map g).map fun a => ({a} : Multiset α)`. Rewrite using `[Multiset.map_map]`. Both sides reduce to the same expression.

Rewrite using `[Finset.sum_eq_multiset_sum, e, Multiset.sum_map_singleton]`. Rewrite using `[key, key, key, Fin.sum_univ_add]`.
-/
private theorem map_univ_add {α : Type} {r s : ℕ} (f : Fin (r + s) → α) :
    (Finset.univ.val.map f) =
      (Finset.univ.val.map fun i => f (Fin.castAdd s i)) + Finset.univ.val.map fun i => f (Fin.natAdd r i) := by
  have key : ∀ {m : ℕ} (g : Fin m → α), Finset.univ.val.map g = ∑ i, ({g i} : Multiset α) := by
    intro m g
    have e : (Finset.univ.val.map fun i => ({g i} : Multiset α)) =
        (Finset.univ.val.map g).map fun a => ({a} : Multiset α) := by
      rw [Multiset.map_map]
      rfl
    rw [Finset.sum_eq_multiset_sum, e, Multiset.sum_map_singleton]
  rw [key, key, key, Fin.sum_univ_add]

/- English proof (translation)
Simplify using `only [msOf]`. Rewrite using `[map_univ_add]`. Use `congr 1`. Use `Multiset.map_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[Dat.ptL, Dat.lam, Dat.idx]`.

Conclude with `congrArg z (Fin.addCases_left (motive := fun _ => Fin (d.len + 1)) _)`. Use `Multiset.map_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[Dat.ptL, Dat.lam, Dat.idx]`. Conclude with `congrArg z (Fin.addCases_right (motive := fun _ => Fin (d.len + 1)) _)`.
-/
private theorem msOf_cons {r s : ℕ} (b : Blo S r) (d : Dat S s) (z : Fin (d.len + 1) → ℂ) (τ : E →+* ℂ) :
    msOf ((Dat.cons b d).ptL z) τ =
      (Finset.univ.val.map fun i => b.Λ τ i + z 0) + msOf (d.ptL fun j => z j.succ) τ := by
  simp only [msOf]
  rw [map_univ_add]
  congr 1
  · refine Multiset.map_congr rfl fun i _ => ?_
    simp [Dat.ptL, Dat.lam, Dat.idx]
    exact congrArg z (Fin.addCases_left (motive := fun _ => Fin (d.len + 1)) _)
  · refine Multiset.map_congr rfl fun i _ => ?_
    simp [Dat.ptL, Dat.lam, Dat.idx]
    exact congrArg z (Fin.addCases_right (motive := fun _ => Fin (d.len + 1)) _)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(∑ j : Fin (d.len + 1), _) = _`. Rewrite using `[Fin.sum_univ_succ]`. Both sides reduce to the same expression.
-/
private theorem ptS_cons {r s : ℕ} (b : Blo S r) (d : Dat S s) (z : Fin (d.len + 1) → ℂ) (w : BW.Pl E) :
    (Dat.cons b d).ptS z w =
      ((b.sat w).map fun x : ℂˣ => (x : ℂ) * ((Formalism.UG.qV E w : ℕ) : ℂ) ^ (-z 0)) + d.ptS (fun j => z j.succ) w := by
  change (∑ j : Fin (d.len + 1), _) = _
  rw [Fin.sum_univ_succ]
  rfl

/- English proof (translation)
Use `Prod.ext rfl (funext fun Λ => funext fun t => propext ⟨?_, ?_⟩)` and prove the remaining obligations. Introduce and unpack `⟨c, Λ', t', ⟨z, rfl, ht'⟩, hΛ, ht⟩`. Use `⟨(Fin.cons c z : Fin (d.len + 1) → ℂ), funext fun τ => ?_, fun w hw => ?_⟩` and prove the remaining obligations. Rewrite using `[msOf_cons]`. Simplify `hΛ τ` using `[par]`.

Rewrite using `[ptS_cons]`. Use `ht w hw` as an intermediate fact. Simplify using `only [par, key, if_neg hw] at this`. Rewrite using `[this, ht' w hw]`. Simplify using the standard rewrite rules.

Introduce and unpack `⟨(z : Fin (d.len + 1) → ℂ), rfl, ht⟩`. Use `⟨z 0, msOf (d.ptL fun j => z j.succ), d.ptS fun j => z j.succ, ⟨fun j => z j.succ, rfl, fun _ _ => rfl⟩, fun τ => ?_, fun w hw => ?_⟩` and prove the remaining obligations. Rewrite using `[msOf_cons]`. Both sides reduce to the same expression. Rewrite using `[ht w hw, ptS_cons]`.

Simplify using `[par, if_neg hw]`.
-/
private theorem step_key {r s : ℕ} (b : Blo S r) (d : Dat S s) :
    step S r (par b) (key d) = key (Dat.cons b d) := by
  refine Prod.ext rfl (funext fun Λ => funext fun t => propext ⟨?_, ?_⟩)
  · rintro ⟨c, Λ', t', ⟨z, rfl, ht'⟩, hΛ, ht⟩
    refine ⟨(Fin.cons c z : Fin (d.len + 1) → ℂ), funext fun τ => ?_, fun w hw => ?_⟩
    · rw [msOf_cons]
      simpa [par] using hΛ τ
    · rw [ptS_cons]
      have := ht w hw
      simp only [par, key, if_neg hw] at this
      rw [this, ht' w hw]
      simp
  · rintro ⟨(z : Fin (d.len + 1) → ℂ), rfl, ht⟩
    refine ⟨z 0, msOf (d.ptL fun j => z j.succ), d.ptS fun j => z j.succ,
      ⟨fun j => z j.succ, rfl, fun _ _ => rfl⟩, fun τ => ?_, fun w hw => ?_⟩
    · rw [msOf_cons]
      rfl
    · rw [ht w hw, ptS_cons]
      simp [par, if_neg hw]

private def Fin' (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (S : Set (BW.Pl E)) (n : ℕ) : Prop :=
  ∀ (ρ : Typ E n) (B : ℝ),
    {q : ℕ × Pts E | ∃ d : Dat S n, d.HasTyp ρ.ρ ∧ (∀ τ i, ‖d.lam τ i‖ ≤ B) ∧ q = key d}.Finite

/- English proof (translation)
Take `⟨⟨ρ₁, c₁, e₁⟩, ⟨ρ₂, c₂, e₂⟩, -⟩` from `UpperTheory.ConvolutionTheory.BW.resTyp E r s ρ`. Establish `f₁` using `UpperTheory.ConvolutionTheory.BW.nearBlo E S r ⟨ρ.d, ρ₁, c₁⟩ B`. Establish `f₂` using `hs ⟨ρ.d, ρ₂, c₂⟩ B`. Use `(f₁.image2 (step S r) f₂).subset ?_` and prove the remaining obligations. Introduce and unpack `q ⟨b, d, ⟨hK, hT⟩, hB, rfl⟩`.

Use `⟨par b, ⟨b, ?_, fun τ i => ?_, rfl, fun w => rfl⟩, key d, ⟨d, ?_, fun τ i => ?_, rfl⟩, step_key b d⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Killed (⇑ρ₁) b.f.1`. Rewrite using `[e₁]`. Conclude with `hK`. Simplify `hB τ (Fin.castAdd s i)` using `[Dat.lam]`.

Express the relevant statement in the definitionally equal form `d.HasTyp (⇑ρ₂)`. Rewrite using `[e₂]`. Conclude with `hT`. Simplify `hB τ (Fin.natAdd r i)` using `[Dat.lam]`.
-/
private theorem fin_cons (r s : ℕ) (hs : Fin' E S s) (ρ : Typ E (r + s)) (B : ℝ) :
    {q : ℕ × Pts E | ∃ (b : Blo S r) (d : Dat S s), (Dat.cons b d).HasTyp ρ.ρ ∧
      (∀ τ i, ‖(Dat.cons b d).lam τ i‖ ≤ B) ∧ q = key (Dat.cons b d)}.Finite := by
  obtain ⟨⟨ρ₁, c₁, e₁⟩, ⟨ρ₂, c₂, e₂⟩, -⟩ := UpperTheory.ConvolutionTheory.BW.resTyp E r s ρ
  have f₁ := UpperTheory.ConvolutionTheory.BW.nearBlo E S r ⟨ρ.d, ρ₁, c₁⟩ B
  have f₂ := hs ⟨ρ.d, ρ₂, c₂⟩ B
  refine (f₁.image2 (step S r) f₂).subset ?_
  rintro q ⟨b, d, ⟨hK, hT⟩, hB, rfl⟩
  refine ⟨par b, ⟨b, ?_, fun τ i => ?_, rfl, fun w => rfl⟩, key d, ⟨d, ?_, fun τ i => ?_, rfl⟩, step_key b d⟩
  · change Killed (⇑ρ₁) b.f.1
    rw [e₁]
    exact hK
  · simpa [Dat.lam] using hB τ (Fin.castAdd s i)
  · change d.HasTyp (⇑ρ₂)
    rw [e₂]
    exact hT
  · simpa [Dat.lam] using hB τ (Fin.natAdd r i)

/- English proof (translation)
Consider the cases of `d with`. Consider the case `nil => exact Or.inl ⟨rfl, HEq.rfl⟩`. Consider the case `cons b d' => exact Or.inr ⟨_, _, b, d', rfl, b.pos, HEq.rfl⟩`.
-/
private theorem dat_cases {n : ℕ} (d : Dat S n) :
    (n = 0 ∧ HEq d (Dat.nil : Dat S 0)) ∨
      ∃ (r s : ℕ) (b : Blo S r) (d' : Dat S s), r + s = n ∧ 0 < r ∧ HEq d (Dat.cons b d') := by
  cases d with
  | nil => exact Or.inl ⟨rfl, HEq.rfl⟩
  | cons b d' => exact Or.inr ⟨_, _, b, d', rfl, b.pos, HEq.rfl⟩

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `ρ B`. Establish `A : ∀ r s : ℕ, {q : ℕ × Pts E | r + s = n ∧ 0 < r ∧ ∃ (d : Dat S n) (b : Blo S r) (d' : Dat S s), HEq d (Dat.cons b d') ∧ d.HasTyp ρ.ρ ∧ (∀ τ i, ‖d.lam τ i‖ ≤ B) ∧ q = key d}.Finite`. Introduce `r s`.

Distinguish the cases in `h : r + s = n ∧ 0 < r`. Take `⟨h, hr⟩` from `h`. Substitute `h` using the available equality. Use `(fin_cons r s (ih s (by omega)) ρ B).subset ?_` and prove the remaining obligations. Introduce and unpack `q ⟨-, -, d, b, d', he, h₁, h₂, rfl⟩`.

Take `rfl` from `eq_of_heq he`. Conclude with `⟨b, d', h₁, h₂, rfl⟩`. Conclude with `Set.finite_empty.subset fun q hq => h ⟨hq.1, hq.2.1⟩`. Establish `A₀ : {q : ℕ × Pts E | n = 0 ∧ ∃ d : Dat S n, HEq d (Dat.nil : Dat S 0) ∧ q = key d}.Finite`. Distinguish the cases in `h : n = 0`.

Substitute `h` using the available equality. Use `(Set.finite_singleton (key (Dat.nil : Dat S 0))).subset ?_` and prove the remaining obligations. Introduce and unpack `q ⟨-, d, he, rfl⟩`. Take `rfl` from `eq_of_heq he`. Both sides reduce to the same expression.

Conclude with `Set.finite_empty.subset fun q hq => h hq.1`. Use `(A₀.union (Set.finite_iUnion fun p : Fin (n + 1) × Fin (n + 1) => A p.1 p.2)).subset ?_` and prove the remaining obligations. Introduce and unpack `q ⟨d, h₁, h₂, rfl⟩`. Break down `dat_cases d with ⟨h, he⟩ | ⟨r, s, b, d', h, hr, he⟩` into its components or cases. Conclude with `Or.inl ⟨h, d, he, rfl⟩`.

Use `Or.inr (Set.mem_iUnion.2 ⟨(⟨r, by omega⟩, ⟨s, by omega⟩), h, hr, d, b, d', he, h₁, h₂, rfl⟩)` and prove the remaining obligations.
-/
private theorem fin_all (n : ℕ) : Fin' E S n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ρ B
    have A : ∀ r s : ℕ, {q : ℕ × Pts E | r + s = n ∧ 0 < r ∧ ∃ (d : Dat S n) (b : Blo S r) (d' : Dat S s),
        HEq d (Dat.cons b d') ∧ d.HasTyp ρ.ρ ∧ (∀ τ i, ‖d.lam τ i‖ ≤ B) ∧ q = key d}.Finite := by
      intro r s
      by_cases h : r + s = n ∧ 0 < r
      · obtain ⟨h, hr⟩ := h
        subst h
        refine (fin_cons r s (ih s (by omega)) ρ B).subset ?_
        rintro q ⟨-, -, d, b, d', he, h₁, h₂, rfl⟩
        obtain rfl := eq_of_heq he
        exact ⟨b, d', h₁, h₂, rfl⟩
      · exact Set.finite_empty.subset fun q hq => h ⟨hq.1, hq.2.1⟩
    have A₀ : {q : ℕ × Pts E | n = 0 ∧ ∃ d : Dat S n, HEq d (Dat.nil : Dat S 0) ∧ q = key d}.Finite := by
      by_cases h : n = 0
      · subst h
        refine (Set.finite_singleton (key (Dat.nil : Dat S 0))).subset ?_
        rintro q ⟨-, d, he, rfl⟩
        obtain rfl := eq_of_heq he
        rfl
      · exact Set.finite_empty.subset fun q hq => h hq.1
    refine (A₀.union (Set.finite_iUnion fun p : Fin (n + 1) × Fin (n + 1) => A p.1 p.2)).subset ?_
    rintro q ⟨d, h₁, h₂, rfl⟩
    rcases dat_cases d with ⟨h, he⟩ | ⟨r, s, b, d', h, hr, he⟩
    · exact Or.inl ⟨h, d, he, rfl⟩
    · refine Or.inr (Set.mem_iUnion.2 ⟨(⟨r, by omega⟩, ⟨s, by omega⟩), h, hr, d, b, d', he, h₁, h₂, rfl⟩)

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX

/- English proof (translation)
Introduce `E _ _ _ S n ρ B`. Establish `f` using `fin_all (E := E) (S := S) n ρ B`. Use `f.to_subtype` as an intermediate fact. Use `choose g hg using fun q : {q : ℕ × Pts E | ∃ d : Dat S n, d.HasTyp ρ.ρ ∧ (∀ τ i, ‖d.lam τ i‖ ≤ B) ∧ q = key d} => q.2`. Use `⟨Set.range g, Set.finite_range g, fun d h₁ h₂ => ?_⟩` and prove the remaining obligations.

Establish `e : key d = key (g ⟨key d, d, h₁, h₂, rfl⟩)` using `(hg ⟨key d, d, h₁, h₂, rfl⟩).2.2`. Use `⟨_, ⟨_, rfl⟩, (congrArg Prod.fst e).symm, fun Λ t => ?_⟩` and prove the remaining obligations. Establish `e₂ : d.On = (g ⟨key d, d, h₁, h₂, rfl⟩).On` using `congrArg Prod.snd e`. Rewrite using `[← e₂]`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX.near2 :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (S : Set (BW.Pl E)) (n : ℕ) (ρ : Typ E n) (B : ℝ), ∃ D : Set (Dat S n), D.Finite ∧
      ∀ d : Dat S n, d.HasTyp ρ.ρ → (∀ τ i, ‖d.lam τ i‖ ≤ B) → ∃ d' ∈ D, d'.len = d.len ∧ ∀ Λ t, d'.On Λ t ↔ d.On Λ t := by
  intro E _ _ _ S n ρ B
  have f := fin_all (E := E) (S := S) n ρ B
  have := f.to_subtype
  choose g hg using fun q : {q : ℕ × Pts E | ∃ d : Dat S n, d.HasTyp ρ.ρ ∧ (∀ τ i, ‖d.lam τ i‖ ≤ B) ∧ q = key d} => q.2
  refine ⟨Set.range g, Set.finite_range g, fun d h₁ h₂ => ?_⟩
  have e : key d = key (g ⟨key d, d, h₁, h₂, rfl⟩) := (hg ⟨key d, d, h₁, h₂, rfl⟩).2.2
  refine ⟨_, ⟨_, rfl⟩, (congrArg Prod.fst e).symm, fun Λ t => ?_⟩
  have e₂ : d.On = (g ⟨key d, d, h₁, h₂, rfl⟩).On := congrArg Prod.snd e
  rw [← e₂]
