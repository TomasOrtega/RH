import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCompactificationInteriorPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptMultihomogFormStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptIsoCompareStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistedHodgeCptFlagStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.HodgeCompactPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFiniteExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeHostAutPermutationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistedHodgeCptCompareStatement
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.JNormal
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LGenflag
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TIdeal
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PairIsoK

/- English proof (translation)
Establish `e1 : Module.finrank A L = Module.finrank A.toSubfield L` using `rfl`. Establish `e2 : Module.finrank B L = Module.finrank B.toSubfield L` using `rfl`. Rewrite using `[e1, e2, h]`.
-/
theorem finrank_congr {F₁ F₂ L : Type} [Field F₁] [Field F₂] [Field L] [Algebra F₁ L] [Algebra F₂ L]
    (A : IntermediateField F₁ L) (B : IntermediateField F₂ L) (h : A.toSubfield = B.toSubfield) :
    Module.finrank A L = Module.finrank B L := by
  have e1 : Module.finrank A L = Module.finrank A.toSubfield L := rfl
  have e2 : Module.finrank B L = Module.finrank B.toSubfield L := rfl
  rw [e1, e2, h]

/- English proof (translation)
Take `rfl : r = fun s => r' (p s)` from `funext fun s => (hr s).symm`. Take `⟨c, u, hc, hj, hjc, hb, hu1, hu0, hst, hai, hd, hfr⟩` from `h`. Establish `hθ' : ∀ (a : Ωa) e, θ (a • e) = ψ.symm a • θ e` using `fun a e => by`. Use `hθ (ψ.symm a) e` as an intermediate fact. Rewrite `this` using `[ψ.apply_symm_apply]`. Then use the resulting hypothesis.

Establish `hθi : ∀ (a : Ωb) e, θ.symm (a • e) = ψ a • θ.symm e` using `fun a e => by`. Apply `θ.injective` to reduce the goal to its premises. Rewrite using `[hθ a, θ.apply_symm_apply, θ.apply_symm_apply]`. Establish `hsp : ∀ s, Submodule.span Ωa (Set.range fun k => θ.symm (c (p s) k)) = V s`. Introduce `s`.

Use extensionality with `e`. Rewrite using `[hV, ← (hc (p s)).2]`. Prove the components needed by the constructor for the conclusion. Introduce `he`. Proceed by induction on `he using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨k, rfl⟩` from `hx`. Rewrite using `[θ.apply_symm_apply]`. Conclude with `Submodule.subset_span ⟨k, rfl⟩`. Consider the case `zero => rw [map_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx => rw [hθ']`. Conclude with `Submodule.smul_mem _ _ hx`.

Introduce `he`. Establish `: ∀ x ∈ Submodule.span Ωb (Set.range (c (p s))), θ.symm x ∈ Submodule.span Ωa (Set.range fun k => θ.symm (c (p s) k))`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨k, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨k, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx => rw [hθi]`. Conclude with `Submodule.smul_mem _ _ hx`. Simplify using `using this _ he`. Use `⟨fun s k => θ.symm (c (p s) k), fun s => u (p s), fun s => ⟨?_, hsp s⟩, ?_, ?_, fun s => hb (p s), fun s => hu1 (p s), fun s => hu0 (p s), ?_, ?_, hd, ?_⟩` and prove the remaining obligations.

Use `(hc (p s)).1.map_of_injective_injective (⇑ψ.symm) θ.symm.toAddMonoidHom (fun a h => by simpa using h) (fun m h => by simpa using h) ?_` and prove the remaining obligations. Introduce `a m`. Use `show θ.symm (ψ.symm a • m) = a • θ.symm m`. Rewrite using `[hθi, ψ.apply_symm_apply]`. Introduce `a e show j (θ (a • e)) = _ • j (θ e)`.

Rewrite using `[hθ', hj, ← hψ, ψ.apply_symm_apply]`. Introduce `s`. Simplify using `using hjc (p s)`. Introduce `s i`. Simplify using `using hst (p s) i`.

Establish `h1` using `hai.comp (fun q : (Σ s, {lk : Fin (r' (p s)) × Fin (r' (p s)) // lk.2 < lk.1}) => (⟨p q.1, q.2⟩ : Σ s', {lk : Fin (r' s') × Fin (r' s') // lk.2 < lk.1})) (by`. Introduce and unpack `⟨s, a⟩ ⟨s', a'⟩ h`. Take `rfl : s = s'` from `p.injective (congrArg Sigma.fst h)`. Simplify using `using h)`. Conclude with `h1.ringHom_of_comp_eq (f := ψ.toRingHom) (g := RingHom.id Ω') ψ.surjective Function.injective_id (RingHom.ext hψ)`.

Establish `hrange : (Set.range fun q : Σ s, Fin (r' (p s)) × Fin (r' (p s)) => u (p q.1) q.2.1 q.2.2) = Set.range fun q : Σ s', Fin (r' s') × Fin (r' s') => u q.1 q.2.1 q.2.2`. Use extensionality with `t`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨s, a⟩, rfl⟩`. Conclude with `⟨⟨p s, a⟩, rfl⟩`.

Introduce and unpack `⟨⟨s', a⟩, rfl⟩`. Take `⟨s, rfl⟩` from `p.surjective s'`. Conclude with `⟨⟨s, a⟩, rfl⟩`. Rewrite using `[hrange, ← hfr]`. Use `finrank_congr _ _ ?_` and prove the remaining obligations.

Rewrite using `[IntermediateField.adjoin_toSubfield, IntermediateField.adjoin_toSubfield]`. Use `congr 2`. Use extensionality with `t`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`.

Conclude with `⟨ψ.symm a, by rw [← hψ, ψ.apply_symm_apply]⟩`. Introduce and unpack `⟨a, rfl⟩`. Conclude with `⟨ψ a, hψ a⟩`.
-/
theorem isGenericFlag_transport {Ωa Ωb Ω' E₁ E₂ E' : Type} [Field Ωa] [Field Ωb] [Field Ω'] [Algebra Ωa Ω'] [Algebra Ωb Ω']
    [AddCommGroup E₁] [Module Ωa E₁] [AddCommGroup E₂] [Module Ωb E₂] [AddCommGroup E'] [Module Ω' E']
    (ψ : Ωb ≃+* Ωa) (hψ : ∀ a, algebraMap Ωa Ω' (ψ a) = algebraMap Ωb Ω' a)
    (θ : E₁ ≃+ E₂) (hθ : ∀ (a : Ωb) e, θ (ψ a • e) = a • θ e) (j : E₂ →+ E') {S S' : Type} {r : S → ℕ} {r' : S' → ℕ}
    (p : S ≃ S') (hr : ∀ s, r' (p s) = r s) (V : S → Submodule Ωa E₁) (V' : S' → Submodule Ωb E₂)
    (hV : ∀ s e, e ∈ V s ↔ θ e ∈ V' (p s)) (b' : ∀ s', Fin (r' s') → E') (d : ℕ) (h : IsGenericFlag (Ω' := Ω') j V' b' d) :
    IsGenericFlag (Ω' := Ω') (j.comp θ.toAddMonoidHom) V (fun s k => b' (p s) (Fin.cast (hr s).symm k)) d := by
  obtain rfl : r = fun s => r' (p s) := funext fun s => (hr s).symm
  obtain ⟨c, u, hc, hj, hjc, hb, hu1, hu0, hst, hai, hd, hfr⟩ := h
  have hθ' : ∀ (a : Ωa) e, θ (a • e) = ψ.symm a • θ e := fun a e => by
    have := hθ (ψ.symm a) e
    rwa [ψ.apply_symm_apply] at this
  have hθi : ∀ (a : Ωb) e, θ.symm (a • e) = ψ a • θ.symm e := fun a e => by
    apply θ.injective
    rw [hθ a, θ.apply_symm_apply, θ.apply_symm_apply]
  have hsp : ∀ s, Submodule.span Ωa (Set.range fun k => θ.symm (c (p s) k)) = V s := by
    intro s
    ext e
    rw [hV, ← (hc (p s)).2]
    constructor
    · intro he
      induction he using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        rw [θ.apply_symm_apply]
        exact Submodule.subset_span ⟨k, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx => rw [hθ']; exact Submodule.smul_mem _ _ hx
    · intro he
      have : ∀ x ∈ Submodule.span Ωb (Set.range (c (p s))),
          θ.symm x ∈ Submodule.span Ωa (Set.range fun k => θ.symm (c (p s) k)) := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨k, rfl⟩ := hx
          exact Submodule.subset_span ⟨k, rfl⟩
        | zero => rw [map_zero]; exact zero_mem _
        | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
        | smul a x _ hx => rw [hθi]; exact Submodule.smul_mem _ _ hx
      simpa using this _ he
  refine ⟨fun s k => θ.symm (c (p s) k), fun s => u (p s), fun s => ⟨?_, hsp s⟩, ?_, ?_, fun s => hb (p s), fun s => hu1 (p s),
    fun s => hu0 (p s), ?_, ?_, hd, ?_⟩
  · refine (hc (p s)).1.map_of_injective_injective (⇑ψ.symm) θ.symm.toAddMonoidHom
      (fun a h => by simpa using h) (fun m h => by simpa using h) ?_
    intro a m
    show θ.symm (ψ.symm a • m) = a • θ.symm m
    rw [hθi, ψ.apply_symm_apply]
  · intro a e
    show j (θ (a • e)) = _ • j (θ e)
    rw [hθ', hj, ← hψ, ψ.apply_symm_apply]
  · intro s
    simpa using hjc (p s)
  · intro s i
    simpa using hst (p s) i
  · have h1 := hai.comp (fun q : (Σ s, {lk : Fin (r' (p s)) × Fin (r' (p s)) // lk.2 < lk.1}) =>
      (⟨p q.1, q.2⟩ : Σ s', {lk : Fin (r' s') × Fin (r' s') // lk.2 < lk.1})) (by
        rintro ⟨s, a⟩ ⟨s', a'⟩ h
        obtain rfl : s = s' := p.injective (congrArg Sigma.fst h)
        simpa using h)
    exact h1.ringHom_of_comp_eq (f := ψ.toRingHom) (g := RingHom.id Ω') ψ.surjective Function.injective_id
      (RingHom.ext hψ)
  · have hrange : (Set.range fun q : Σ s, Fin (r' (p s)) × Fin (r' (p s)) => u (p q.1) q.2.1 q.2.2) =
        Set.range fun q : Σ s', Fin (r' s') × Fin (r' s') => u q.1 q.2.1 q.2.2 := by
      ext t
      constructor
      · rintro ⟨⟨s, a⟩, rfl⟩
        exact ⟨⟨p s, a⟩, rfl⟩
      · rintro ⟨⟨s', a⟩, rfl⟩
        obtain ⟨s, rfl⟩ := p.surjective s'
        exact ⟨⟨s, a⟩, rfl⟩
    rw [hrange, ← hfr]
    refine finrank_congr _ _ ?_
    rw [IntermediateField.adjoin_toSubfield, IntermediateField.adjoin_toSubfield]
    congr 2
    ext t
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨ψ.symm a, by rw [← hψ, ψ.apply_symm_apply]⟩
    · rintro ⟨a, rfl⟩
      exact ⟨ψ a, hψ a⟩

/- English proof (translation)
Take `⟨_, _, _, _, _, _, _, _, _, _, hd, _⟩` from `h`. Conclude with `hd`.
-/
theorem IsGenericFlag_deg_pos {Ωa Ω' E₁ E' : Type} [Field Ωa] [Field Ω'] [Algebra Ωa Ω'] [AddCommGroup E₁] [Module Ωa E₁]
    [AddCommGroup E'] [Module Ω' E'] {j : E₁ →+ E'} {S : Type} {r : S → ℕ} {V : S → Submodule Ωa E₁}
    {b : ∀ s, Fin (r s) → E'} {d : ℕ} (h : IsGenericFlag (Ω' := Ω') j V b d) : 0 < d := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hd, _⟩ := h
  exact hd

/- English proof (translation)
Take `⟨c', u, hc', hj, -, -, -, -, hst, -⟩` from `h`. Establish `h1 : ∀ l, j (c' s l) ∈ Submodule.span Ω' (Set.range fun l => j (c l))`. Introduce `l`. Establish `hm : c' s l ∈ Submodule.span Ωa (Set.range c)`. Rewrite using `[hc, ← (hc' s).2]`.

Conclude with `Submodule.subset_span ⟨l, rfl⟩`. Establish `key : ∀ x ∈ Submodule.span Ωa (Set.range c), j x ∈ Submodule.span Ω' (Set.range fun l => j (c l))`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨q, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨q, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx => rw [hj]`. Conclude with `Submodule.smul_mem _ _ hx`. Conclude with `key _ hm`. Establish `h2 : ∀ k, b s k ∈ Submodule.span Ω' (Set.range fun l => j (c l))`.

Introduce `k`. Establish `hk : b s k ∈ flagStep Ω' (b s) (k + 1)` using `Submodule.subset_span ⟨k, by simp, rfl⟩`. Rewrite `hk` using `[hst]`. Use `(Submodule.span_le.2 ?_ : flagStep Ω' _ _ ≤ _) hk` and prove the remaining obligations. Introduce and unpack `_ ⟨a, -, rfl⟩`.

Conclude with `Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (h1 l)`. Establish `h3` using `fun k => (Submodule.mem_span_range_iff_exists_fun Ω').1 (h2 k)`. Use `choose m hm using h3`. Conclude with `⟨fun l k => m k l, fun k => (hm k).symm⟩`.
-/
theorem exists_coeff {Ωa Ω' E₁ E' : Type} [Field Ωa] [Field Ω'] [Algebra Ωa Ω'] [AddCommGroup E₁] [Module Ωa E₁]
    [AddCommGroup E'] [Module Ω' E'] {j : E₁ →+ E'} {S : Type} {r : S → ℕ} {V : S → Submodule Ωa E₁}
    {b : ∀ s, Fin (r s) → E'} {d : ℕ} (h : IsGenericFlag (Ω' := Ω') j V b d) (s : S) {n : ℕ} (c : Fin n → E₁)
    (hc : Submodule.span Ωa (Set.range c) = V s) :
    ∃ m : Matrix (Fin n) (Fin (r s)) Ω', ∀ k, b s k = ∑ l, m l k • j (c l) := by
  obtain ⟨c', u, hc', hj, -, -, -, -, hst, -⟩ := h
  have h1 : ∀ l, j (c' s l) ∈ Submodule.span Ω' (Set.range fun l => j (c l)) := by
    intro l
    have hm : c' s l ∈ Submodule.span Ωa (Set.range c) := by
      rw [hc, ← (hc' s).2]
      exact Submodule.subset_span ⟨l, rfl⟩
    have key : ∀ x ∈ Submodule.span Ωa (Set.range c), j x ∈ Submodule.span Ω' (Set.range fun l => j (c l)) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨q, rfl⟩ := hx
        exact Submodule.subset_span ⟨q, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx => rw [hj]; exact Submodule.smul_mem _ _ hx
    exact key _ hm
  have h2 : ∀ k, b s k ∈ Submodule.span Ω' (Set.range fun l => j (c l)) := by
    intro k
    have hk : b s k ∈ flagStep Ω' (b s) (k + 1) := Submodule.subset_span ⟨k, by simp, rfl⟩
    rw [hst] at hk
    refine (Submodule.span_le.2 ?_ : flagStep Ω' _ _ ≤ _) hk
    rintro _ ⟨a, -, rfl⟩
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (h1 l)
  have h3 := fun k => (Submodule.mem_span_range_iff_exists_fun Ω').1 (h2 k)
  choose m hm using h3
  exact ⟨fun l k => m k l, fun k => (hm k).symm⟩

/- English proof (translation)
Take `⟨c, _, hc, _⟩` from `h`. Conclude with `⟨c s, hc s⟩`.
-/
theorem exists_basis {Ωa Ω' E₁ E' : Type} [Field Ωa] [Field Ω'] [Algebra Ωa Ω'] [AddCommGroup E₁] [Module Ωa E₁]
    [AddCommGroup E'] [Module Ω' E'] {j : E₁ →+ E'} {S : Type} {r : S → ℕ} {V : S → Submodule Ωa E₁}
    {b : ∀ s, Fin (r s) → E'} {d : ℕ} (h : IsGenericFlag (Ω' := Ω') j V b d) (s : S) :
    ∃ c : Fin (r s) → E₁, LinearIndependent Ωa c ∧ Submodule.span Ωa (Set.range c) = V s := by
  obtain ⟨c, _, hc, _⟩ := h
  exact ⟨c s, hc s⟩

/- English proof (translation)
Use `GlobalTheory.CompanionTheory.Ar.FlagPull.flagStep_map_eq (i := RingHom.id Ω₃) (j := (Fintype.linearCombination Ω₃ f).toAddMonoidHom) (fun a e => by simp) h i` as an intermediate fact. Simplify `this` using `[Fintype.linearCombination_apply]`.
-/
theorem flagStep_rows {Ω₃ F : Type} [Field Ω₃] [AddCommGroup F] [Module Ω₃ F] {r : ℕ} (f : Fin r → F)
    (m m' : Fin r → Fin r → Ω₃) (h : ∀ i, flagStep Ω₃ (fun k l => m l k : Fin r → Fin r → Ω₃) i =
      flagStep Ω₃ (fun k l => m' l k : Fin r → Fin r → Ω₃) i) (i : ℕ) :
    flagStep Ω₃ (fun k => ∑ l, m l k • f l) i = flagStep Ω₃ (fun k => ∑ l, m' l k • f l) i := by
  have := GlobalTheory.CompanionTheory.Ar.FlagPull.flagStep_map_eq (i := RingHom.id Ω₃)
    (j := (Fintype.linearCombination Ω₃ f).toAddMonoidHom) (fun a e => by simp) h i
  simpa [Fintype.linearCombination_apply] using this

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem flagStep_cast {Ω₃ F : Type} [Field Ω₃] [AddCommGroup F] [Module Ω₃ F] {r r' : ℕ} (h : r = r') (b : Fin r' → F)
    (i : ℕ) : flagStep Ω₃ (fun a : Fin r => b (Fin.cast h a)) i = flagStep Ω₃ b i := by
  subst h
  rfl

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

/- English proof (translation)
Take `⟨A', e, j, m, h1, h2, h3, h4, h5, h6, h7, -, h9⟩` from `PositivityTheory.UnitarySelfGeneration.hodge_compact_pullback E H D l Xo c O β Y S Ω Ω' i K K' J J' y y' A x Z ξ' h hx hdisc hvb hall htie hnorm hd`. Establish `hdom : GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ A.ξ (e.hom ≫ h) i` using `by show A'.ξ ≫ e.hom ≫ h = _`. Rewrite using `[← Category.assoc, h1]`. Conclude with `hd`. Establish `hf : A'.f = (e.hom ≫ h) ≫ A.f` using `by rw [h2, Category.assoc]`.

Take `⟨Fl', hb', -, ⟨ψ', θ', q1, -, q3, q4⟩, q5⟩` from `GlobalTheory.CompanionTheory.Ar.FlagPull.flag_pull E H D l Xo c O β Y S Ω Ω' i K K' J J' y y' A A' (e.hom ≫ h) j m κ v Fl hb hy hdom hf h3 h4 h6 h7 h9 hfd`. Use `⟨A', e, Fl', ψ', θ', j, h1, h2, h4, h5, h6, hb', q1, q3, q4, q5, fun r e₀ L L' hL hP => ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.T.hodge_cpt_finite_extension E H D l Xo c O β Y S Ω Ω' i K K' J J' y y' A A' (e.hom ≫ h) j m κ v Fl hb hy hdom hf h3 h4 h6 h7 h9 Fl' hb' r e₀ L L' hL hP`.
-/
theorem pull_both {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω Ω' : Type} [Field Ω] [Field Ω'] (i : Ω →+* Ω') {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type}
    {J' : K' → Type} [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω'}
    (A : HodgeCpt Y S y) (Fl : A.Flag) (x : Sp Ω ⟶ Xo.XF c) (Z : Scheme.{0}) (ξ' : Sp Ω' ⟶ Z) (h : Z ⟶ A.X)
    (κ : K → K') (v : (Σ k, J k) → (Σ k, J' k))
    (hx : A.ξ ≫ A.f = x ≫ Y.j) (hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S)
    (hvb : ∀ p ∈ S, ∀ s, ((A.M.htOm A.t.PP.L (p ^ A.R p)).map (A.Vgen s).dualRestrict).IsVBOn
      {q | InFibre A.ξ p q} (labelRk D s) ⊤)
    (hall : ∀ q : Z, genPt ξ' ⤳ q) (htie : CoordTie ℤ ξ' (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩))
    (hnorm : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z) (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' A.ξ h i) (hb : IsBlockMap κ v)
    (hy : ∀ q, y' (v q) = i (y q)) (hfd : FiniteDimensional i.fieldRange Ω') :
    ∃ (A' : HodgeCpt Y S y') (e : A'.X ≅ Z) (Fl' : A'.Flag) (ψ' : A.Ω₀ ≃+* A'.Ω₀) (θ' : Fl.Li₀ ≃+ Fl'.Li₀)
      (j : A.Li →+ A'.Li),
      A'.ξ ≫ e.hom = ξ' ∧ A'.f = e.hom ≫ h ≫ A.f ∧ A'.cst = i.comp A.cst ∧ A'.R = A.R ∧ IsExtOver i j ∧
      (∀ s k, Fl'.b s k = j (Fl.b s k)) ∧ A'.fn.comp ψ'.toRingHom = i.comp A.fn ∧
      (∀ e, (Fl'.M₀.pt (θ' e)).left = spMap (dualMap ψ'.toRingHom) ≫ (Fl.M₀.pt e).left) ∧
      (∀ e, Fl'.j (θ' e) = j (Fl.j e)) ∧
      (∀ xdeg e, Fl.RootLines xdeg e → Fl'.RootLines (fun r => pullDeg κ (xdeg r)) (fun r => i (e r))) ∧
      ∀ r (e₀ : Ω) (L : HermLine J) (L' : HermLine J'), Fl.IsHodgeLine r e₀ L → IsPullHerm κ v L L' →
        Fl'.IsHodgeLine r (i e₀) L' := by
  obtain ⟨A', e, j, m, h1, h2, h3, h4, h5, h6, h7, -, h9⟩ :=
    PositivityTheory.UnitarySelfGeneration.hodge_compact_pullback E H D l Xo c O β Y S Ω Ω' i K K' J J' y y' A x Z ξ' h hx hdisc hvb hall htie hnorm hd
  have hdom : GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ A.ξ (e.hom ≫ h) i := by
    show A'.ξ ≫ e.hom ≫ h = _
    rw [← Category.assoc, h1]
    exact hd
  have hf : A'.f = (e.hom ≫ h) ≫ A.f := by rw [h2, Category.assoc]
  obtain ⟨Fl', hb', -, ⟨ψ', θ', q1, -, q3, q4⟩, q5⟩ :=
    GlobalTheory.CompanionTheory.Ar.FlagPull.flag_pull E H D l Xo c O β Y S Ω Ω' i K K' J J' y y' A A' (e.hom ≫ h) j m κ v Fl hb hy hdom hf h3
      h4 h6 h7 h9 hfd
  refine ⟨A', e, Fl', ψ', θ', j, h1, h2, h4, h5, h6, hb', q1, q3, q4, q5, fun r e₀ L L' hL hP => ?_⟩
  exact GlobalTheory.T.hodge_cpt_finite_extension E H D l Xo c O β Y S Ω Ω' i K K' J J' y y' A A' (e.hom ≫ h) j m κ v Fl hb hy hdom hf h3 h4 h6 h7 h9
    Fl' hb' r e₀ L L' hL hP

/- English proof (translation)
Simplify using `[spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`.
-/
theorem spMap_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/- English proof (translation)
Use `Spec.map_injective h` as an intermediate fact. Conclude with `congrArg CommRingCat.Hom.hom this`.
-/
theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

/- English proof (translation)
Take `⟨u, u', h1, h2, h3, h4⟩` from `h`. Use `⟨w ≫ u, w ≫ u', ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, h1]`. Rewrite using `[Category.assoc, h2]`. Rewrite using `[Category.assoc, h3, Category.assoc]`.

Simplify using `only [Category.assoc, h4]`.
-/
theorem twTan_pre {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}
    {g : HostAut H} {Φ : Xo.X ⟶ Xo.X} {n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ} {Y : Model Xo c β}
    {Y' : Model Xo c β'} {T T' : Scheme.{0}} {u₁ : T ⟶ Y.t.G.left} {u₂ : T ⟶ Y'.t.G.left} (w : T' ⟶ T)
    (h : TwTan n Y Y' u₁ u₂) : TwTan n Y Y' (w ≫ u₁) (w ≫ u₂) := by
  obtain ⟨u, u', h1, h2, h3, h4⟩ := h
  refine ⟨w ≫ u, w ≫ u', ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, h1]
  · rw [Category.assoc, h2]
  · rw [Category.assoc, h3, Category.assoc]
  · simp only [Category.assoc, h4]

/- English proof (translation)
Introduce `hCmp hTh E _ _ _ H D l Xo c O _ β Y g Φ n π S nn M M' T T' hβ hs hπ himg hR`. Take `⟨x₀, x₀', ψ, hξ, hξ', hfst, hsnd, hcst, hcst'⟩` from `himg`. Take `⟨π₀, hπ₀, hlab⟩` from `GlobalTheory.T.cm_type_host_aut_permutation E H l c g`. Establish `hππ : π₀ = π` using `Equiv.ext fun τ => Subtype.ext ((hπ₀ τ).trans (hπ τ).symm)`. Substitute `hππ` using the available equality.

Take `⟨θ, hθs, hθt, hθV⟩` from `GlobalTheory.T.twisted_hodge_cpt_compare E H D l Xo c O O β β Y Y g Φ n S M.Ω M'.Ω M.K M'.K M.ι M'.ι M.y M'.y T.A T'.A T.Fl T'.Fl ψ x₀ x₀' hβ hβ hξ hξ' hfst hsnd`. Use `letI a₁ : Algebra T.A.Ω₀ M.Ω := T.A.fn.toAlgebra`. Use `letI a₂ : Algebra T.A.Ω₀ M'.Ω := (T'.A.fn.comp ψ.symm.toRingHom).toAlgebra`. Use `letI a₃ : Algebra T'.A.Ω₀ M'.Ω := T'.A.fn.toAlgebra`. Apply the tactic sequence `have hrl : ∀ s, labelRk D (Sum.map π₀ π₀ s) = labelRk D s := by rintro (τ | τ) <;> rfl`.

Establish `g₁ : IsGenericFlag (Ω'` using `M.Ω) T.Fl.j T.Fl.V₀ T.Fl.b T.Fl.deg := T.Fl.generic`. Establish `g₂ : IsGenericFlag (Ω'` using `M'.Ω) (T'.Fl.j.comp θ.toAddMonoidHom) T.Fl.V₀ (fun s k => T'.Fl.b (Equiv.sumCongr π₀ π₀ s) (Fin.cast (hrl s).symm k)) T'.Fl.deg := isGenericFlag_transport ψ (fun a => by show T'.A.fn (ψ.symm (ψ a)) = T'.A.fn a`. Rewrite using `[ψ.symm_apply_apply]) θ (fun a e => hθs a e) T'.Fl.j (Equiv.sumCongr π₀ π₀) hrl T.Fl.V₀ T'.Fl.V₀`. Use the proof step `(fun s e => hθV s _ (by simpa [Equiv.sumCongr] using (hlab s)) e) T'.Fl.b T'.Fl.deg T'.Fl.generic`. Take `⟨Ω₃, fΩ, i₁, i₂, hi, ⟨n₁, n₂, hn₁, hn, hf₁, hf₂⟩, hflag⟩` from `PositivityTheory.UnitarySelfGeneration.l_genflag T.A.Ω₀ M.Ω M'.Ω T.Fl.Li₀ T.A.Li T'.A.Li T.Fl.j (T'.Fl.j.comp θ.toAddMonoidHom) (CMType H ⊕ CMType H) (labelRk D) T.Fl.V₀ T.Fl.b _ T.Fl.deg T'.Fl.deg g₁ g₂`.

Establish `hn₂ : 0 < n₂`. Use `Nat.mul_pos hn₁ (IsGenericFlag_deg_pos g₁)` as an intermediate fact. Rewrite `this` using `[hn]`. Conclude with `Nat.pos_of_mul_pos_right this`. Use `haveI : CharZero M.Ω := charZero_of_injective_ringHom T.A.cst.injective`.

Use `haveI : CharZero M'.Ω := charZero_of_injective_ringHom T'.A.cst.injective`. Use `haveI : CharZero Ω₃ := charZero_of_injective_ringHom i₁.injective`. Establish `hfd₁ : FiniteDimensional i₁.fieldRange Ω₃` using `FiniteDimensional.of_finrank_pos (by omega)`. Establish `hfd₂ : FiniteDimensional i₂.fieldRange Ω₃` using `FiniteDimensional.of_finrank_pos (by omega)`. Take `⟨K, hK, ι, hι, κ₁, v₁, κ₂, v₂, y, Z, ξ, h₁, h₂, hb₁, hb₂, hy₁, hy₂, harith, hbir, hall, htie, hnorm, hd₁, hd₂, hr₁, hr₂⟩` from `PositivityTheory.UnitarySelfGeneration.j_normal M.K M.ι M'.K M'.ι M.Ω M'.Ω Ω₃ i₁ i₂ M.y M'.y (Top.dimFl (CMType H) (D.p + D.q) + 1) T.A.X T'.A.X T.A.ξ T'.A.ξ M.arith M'.arith M.birational M'.birational hfd₁ hfd₂ T.A.all T'.A.all T.A.tie T'.A.tie`.

Establish `hx₁ : T.A.ξ ≫ T.A.f = (spMap T.A.fn ≫ x₀) ≫ Y.j`. Rewrite using `[Category.assoc, ← hξ]`. Conclude with `T.A.fn_over`. Establish `hx₂ : T'.A.ξ ≫ T'.A.f = (spMap T'.A.fn ≫ x₀') ≫ Y.j`. Rewrite using `[Category.assoc, ← hξ']`.

Conclude with `T'.A.fn_over`. Take `⟨A₁, e₁, Fl₁, ψ₁, θ₁, j₁, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩` from `pull_both i₁ T.A T.Fl (spMap T.A.fn ≫ x₀) Z ξ h₁ κ₁ v₁ hx₁ T.discr T.ht_vb hall htie hnorm hd₁ hb₁ (fun q => congrFun hy₁ q) hfd₁`. Take `⟨A₂, e₂, Fl₂, ψ₂, θ₂, j₂, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩` from `pull_both i₂ T'.A T'.Fl (spMap T'.A.fn ≫ x₀') Z ξ h₂ κ₂ v₂ hx₂ T'.discr T'.ht_vb hall htie hnorm hd₂ hb₂ (fun q => congrFun hy₂ q) hfd₂`. Establish `hi' : i₁.comp (T.A.fn.comp ψ.toRingHom) = i₂.comp T'.A.fn`. Use extensionality with `a`.

Use `congrArg (fun f => f (ψ a)) hi` as an intermediate fact. Simplify `this` using `[a₁, a₂, RingHom.algebraMap_toAlgebra]`. Establish `hkey : spMap i₁ ≫ spMap T.A.fn ≫ spMap ψ.toRingHom = spMap i₂ ≫ spMap T'.A.fn`. Rewrite using `[spMap_spMap, spMap_spMap, spMap_spMap, hi']`. Establish `hk3 : ∀ {W : Scheme.{0}} (t : Sp T'.A.Ω₀ ⟶ W), spMap i₂ ≫ spMap T'.A.fn ≫ t = spMap i₁ ≫ spMap T.A.fn ≫ spMap ψ.toRingHom ≫ t`.

Introduce `W t`. Rewrite using `[← Category.assoc, ← hkey]`. Simplify using `only [Category.assoc]`. Establish `hX₁ : A₁.ξ ≫ A₁.f = (spMap i₁ ≫ spMap T.A.fn ≫ x₀) ≫ Y.j`. Establish `hd : ξ ≫ h₁ = spMap i₁ ≫ T.A.ξ` using `hd₁`.

Combine the equalities or inequalities in the displayed calculation. Establish `hX₂ : A₂.ξ ≫ A₂.f = (spMap i₂ ≫ spMap T'.A.fn ≫ x₀') ≫ Y.j`. Establish `hd : ξ ≫ h₂ = spMap i₂ ≫ T'.A.ξ` using `hd₂`. Combine the equalities or inequalities in the displayed calculation. Establish `hfst₃ : (spMap i₂ ≫ spMap T'.A.fn ≫ x₀') ≫ Limits.pullback.fst _ _ = (spMap i₁ ≫ spMap T.A.fn ≫ x₀) ≫ Limits.pullback.fst _ _ ≫ Φ.hom`.

Simplify using `only [Category.assoc]`. Rewrite using `[hk3, hfst]`. Establish `hsnd₃ : (spMap i₂ ≫ spMap T'.A.fn ≫ x₀') ≫ Limits.pullback.snd _ _ = (spMap i₁ ≫ spMap T.A.fn ≫ x₀) ≫ Limits.pullback.snd _ _`. Simplify using `only [Category.assoc]`. Rewrite using `[hk3, hsnd]`.

Establish `hc₁ : (spMap i₁ ≫ spMap T.A.fn ≫ x₀) ≫ Limits.pullback.snd _ _ = spMap A₁.cst`. Rewrite using `[p3, ← spMap_spMap, ← hcst]`. Simplify using `only [Category.assoc]`. Establish `hc₂ : (spMap i₂ ≫ spMap T'.A.fn ≫ x₀') ≫ Limits.pullback.snd _ _ = spMap A₂.cst`. Rewrite using `[q3, ← spMap_spMap, ← hcst']`.

Simplify using `only [Category.assoc]`. Establish `hAc : A₁.cst = A₂.cst` using `spMap_inj (by rw [← hc₁, ← hc₂, hsnd₃])`. Establish `hξe : A₂.ξ ≫ (e₂ ≪≫ e₁.symm).hom = A₁.ξ`. Simplify using `only [Iso.trans_hom, Iso.symm_hom]`. Rewrite using `[← Category.assoc, q1, ← p1, Category.assoc, Iso.hom_inv_id, Category.comp_id]`.

Take `⟨φ, hφt, -, hφV, hφz⟩` from `hCmp E H D l Xo c O O β β Y Y g Φ n S Ω₃ K ι y A₁ A₂ (e₂ ≪≫ e₁.symm) _ _ hβ hβ hs hξe hX₁ hX₂ hfst₃ hsnd₃ hAc hc₁ (fun p hp => by rw [q4, p4]; exact hR p hp)`. Set `ψ₃ : A₂.Ω₀ ≃+* A₁.Ω₀` to `ψ₂.symm.trans (ψ.trans ψ₁)`. Set `θ₃ : Fl₁.Li₀ ≃+ Fl₂.Li₀` to `θ₁.symm.trans (θ.trans θ₂)`. Establish `hθ₃ : ∀ e, θ₃ (θ₁ e) = θ₂ (θ e)` using `fun e => by simp [θ₃]`. Establish `hfn : A₁.fn.comp ψ₃.toRingHom = A₂.fn`.

Use extensionality with `a`. Establish `h1` using `congrArg (fun f => f (ψ (ψ₂.symm a))) p7`. Establish `h2` using `congrArg (fun f => f (ψ₂.symm a)) hi'`. Establish `h3` using `congrArg (fun f => f (ψ₂.symm a)) q7`. Simplify using `only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply] at h1 h2 h3`.

Simplify using `only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ψ₃, RingEquiv.trans_apply]`. Rewrite using `[h1, h2, ← h3]`. Establish `hψc : (dualMap ψ₃.toRingHom).comp (dualMap ψ₂.toRingHom) = (dualMap ψ₁.toRingHom).comp (dualMap ψ.toRingHom)`. Rewrite using `[← GlobalTheory.CompanionTheory.Ar.FlagPull.dualMap_comp, ← GlobalTheory.CompanionTheory.Ar.FlagPull.dualMap_comp]`. Use `congr 1`.

Use extensionality with `a`. Simplify using `[ψ₃]`. Establish `htw : ∀ e, TwTan n Y Y (Fl₁.M₀.pt e).left (spMap (dualMap ψ₃.toRingHom) ≫ (Fl₂.M₀.pt (θ₃ e)).left)`. Introduce `e`. Take `⟨e₀, rfl⟩` from `θ₁.surjective e`.

Rewrite using `[hθ₃, q8, p8, ← Category.assoc, spMap_spMap, hψc, ← spMap_spMap, Category.assoc]`. Conclude with `twTan_pre _ (hθt e₀)`. Take `⟨-, hsteps⟩` from `GlobalTheory.T.twisted_hodge_cpt_flag E H D l Xo c O O β β Y Y g Φ n S Ω₃ K ι y A₁ A₂ Fl₁ Fl₂ ψ₃ θ₃ φ hβ hβ hfn hφt htw`. Establish `hst : ∀ s k, (flagStep Ω₃ (Fl₁.b s) k).map (φ : A₁.Li →ₗ[Ω₃] A₂.Li) = flagStep Ω₃ (Fl₂.b (Equiv.sumCongr π₀ π₀ s)) k`. Introduce `s`.

Take `⟨cc, hcl, hcs⟩` from `exists_basis g₁ s`. Take `⟨m₁, hm₁⟩` from `exists_coeff g₁ s cc hcs`. Take `⟨m₂, hm₂⟩` from `exists_coeff g₂ s cc hcs`. Establish `hrow` using `hflag s cc m₁ m₂ hcl hcs hm₁ hm₂`. Use `hsteps s (Equiv.sumCongr π₀ π₀ s) _ (fun q => θ₁ (cc q)) (fun q a => i₁ (m₁ q a)) ?_ ?_` and prove the remaining obligations.

Introduce `k`. Use `congr 1`. Use function extensionality and compare the values at `a`. Rewrite using `[p6, hm₁ a, map_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Rewrite using `[p5.1, p9]`. Introduce `k`. Use `(flagStep_cast (hrl s).symm (Fl₂.b (Equiv.sumCongr π₀ π₀ s)) k).symm.trans ?_` and prove the remaining obligations. Establish `e1 : (fun a => Fl₂.b (Equiv.sumCongr π₀ π₀ s) (Fin.cast (hrl s).symm a)) = fun a => ∑ q, i₂ (m₂ q a) • Fl₂.j (θ₃ (θ₁ (cc q)))`. Use function extensionality and compare the values at `a`.

Rewrite using `[q6, hm₂ a, map_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[q5.1, hθ₃, q9]`. Both sides reduce to the same expression. Conclude with `(congrArg (fun f => flagStep Ω₃ f k) e1).trans (flagStep_rows (fun q => Fl₂.j (θ₃ (θ₁ (cc q)))) (fun q a => i₂ (m₂ q a)) (fun q a => i₁ (m₁ q a)) (fun i => (hrow i).symm) k)`.

Establish `hemb : ∀ s, A₂.emb (Equiv.sumCongr π₀ π₀ s) = (A₁.emb s).comp g.s.toRingHom`. Introduce `s`. Use `show A₂.cst.comp (labelEmb c (Sum.map π₀ π₀ s)) = (A₁.cst.comp (labelEmb c s)).comp g.s.toRingHom`. Rewrite using `[hlab s, hAc]`. Both sides reduce to the same expression.

Establish `hgram` using `GlobalTheory.T.hodge_compactification_interior_point hTh E H D l Xo c O β Y S Ω₃ K ι y A₁ Fl₁ hβ`. Take `⟨b, d, hbm, hbn, hbz⟩` from `GlobalTheory.T.hodge_cpt_multihomog_form E H D l Xo c O β Y S Ω₃ K ι y A₁ _ hX₁ hβ`. Use `⟨K, hK, ι, hι, κ₁, v₁, κ₂, v₂, Ω₃, fΩ, inferInstance, y, b, d, hb₁, hb₂, ?_, ?_, harith, hbm, hbn, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hy₁]`. Conclude with `(PositivityTheory.UnitarySelfGeneration.t_ideal M.K M.ι M.Ω Ω₃ i₁ M.y).1`.

Rewrite using `[hy₂]`. Conclude with `(PositivityTheory.UnitarySelfGeneration.t_ideal M'.K M'.ι M'.Ω Ω₃ i₂ M'.y).1`. Rewrite using `[hr₁, hf₁]`. Conclude with `hn₁.ne'`. Rewrite using `[hr₁, hr₂, hf₁, hf₂]`.

Conclude with `hn`. Introduce `r L L' hL hL'`. Establish `hdeg : (Fl₁.rootLat (r.1, r.2)).IsDegOn Set.univ y L.a (i₁ (T.e r))`. Use `p10 _ _ T.roots r` as an intermediate fact. Rewrite using `[hL.1, T.sing_deg]`.

Conclude with `this`. Establish `hdeg' : (Fl₂.rootLat (π₀ r.1, r.2)).IsDegOn Set.univ y L'.a (i₂ (T'.e (π₀ r.1, r.2)))`. Use `q10 _ _ T'.roots (π₀ r.1, r.2)` as an intermediate fact. Rewrite using `[hL'.1, T'.sing_deg]`. Conclude with `this`.

Establish `hH` using `p11 r (T.e r) (T.sing r) L (T.hodge r) hL`. Establish `hH'` using `q11 (π₀ r.1, r.2) (T'.e (π₀ r.1, r.2)) (T'.sing (π₀ r.1, r.2)) L' (T'.hodge _) hL'`. Take `⟨f, f', hiso, hdef⟩` from `GlobalTheory.T.hodge_cpt_iso_compare E H D l Xo c O O β β Y Y S Ω₃ K ι y A₁ A₂ (e₂ ≪≫ e₁.symm) φ Fl₁ Fl₂ r.1 (π₀ r.1) r.2 (i₁ (T.e r)) (i₂ (T'.e (π₀ r.1, r.2))) L L' hbir hξe (fun q h v => ⟨hφV (.inl r.1) (.inl (π₀ r.1)) (hemb (.inl r.1)) q h v, hφV (.inr r.1) (.inr (π₀ r.1)) (he …`. Conclude with `⟨f, f', hiso, fun w hw => hdef w (hbz w hw.1 hw.2)⟩`.
-/
theorem pair_iso : HodgeComparisonCompatibility → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (_ : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (π : CMType H ≃ CMType H) (S : Finset ℕ) (n : ℕ) (M M' : Top.RootModel (CMType H) (D.p + D.q)) (T : HodgeTie Y S n M) (T' : HodgeTie Y S n M'), Mono (spMap β) → Φ.hom ≫ Xo.s = Xo.s → (∀ τ, (π τ).1 = τ.1.comp g.σ.toRingHom) → IsImageCpt Φ T.A T'.A → (∀ p ∈ S, T'.A.R p = T.A.R p) → ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (κ : M.K → K) (v : (Σ k, M.ι k) → Σ k, ι k) (κ' : M'.K → K) (v' : (Σ k, M'.ι k) → Σ k, ι k) (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (y : (Σ k, ι k) → Ω) (b : MRing ι) (d : K → ℕ), IsBlockMap κ v ∧ IsBlockMap κ' v' ∧ mCoordIdeal (y ∘ v) = M.P ∧ mCoordIdeal (y ∘ v') = M'.P ∧ IsArithVar (mCoordIdeal y) (Top.dimFl (CMType H) (D.p + D.q) + 1) ∧ IsMultiHomog b d ∧ b ∉ mCoordIdeal y ∧ IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) ≠ 0 ∧ IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) * T.Fl.deg = IntermediateField.relfinrank (blockFnField (y ∘ v')) (blockFnField y) * T'.Fl.deg ∧ ∀ (r : CMType H × Fin (D.p + D.q)) (L L' : HermLine ι), IsPullHerm κ v (T.sing r) L → IsPullHerm κ' v' (T'.sing (π r.1, r.2)) L' → IsoLineOn (mCoordIdeal y) {z | z ∈ mcPts (mCoordIdeal y) ∧ evC z b ≠ 0} L L' := by
  intro hCmp hTh E _ _ _ H D l Xo c O _ β Y g Φ n π S nn M M' T T' hβ hs hπ himg hR
  obtain ⟨x₀, x₀', ψ, hξ, hξ', hfst, hsnd, hcst, hcst'⟩ := himg
  obtain ⟨π₀, hπ₀, hlab⟩ := GlobalTheory.T.cm_type_host_aut_permutation E H l c g
  have hππ : π₀ = π := Equiv.ext fun τ => Subtype.ext ((hπ₀ τ).trans (hπ τ).symm)
  subst hππ
  obtain ⟨θ, hθs, hθt, hθV⟩ := GlobalTheory.T.twisted_hodge_cpt_compare E H D l Xo c O O β β Y Y g Φ n S M.Ω M'.Ω M.K M'.K M.ι M'.ι M.y M'.y T.A T'.A
    T.Fl T'.Fl ψ x₀ x₀' hβ hβ hξ hξ' hfst hsnd

  letI a₁ : Algebra T.A.Ω₀ M.Ω := T.A.fn.toAlgebra
  letI a₂ : Algebra T.A.Ω₀ M'.Ω := (T'.A.fn.comp ψ.symm.toRingHom).toAlgebra
  letI a₃ : Algebra T'.A.Ω₀ M'.Ω := T'.A.fn.toAlgebra
  have hrl : ∀ s, labelRk D (Sum.map π₀ π₀ s) = labelRk D s := by rintro (τ | τ) <;> rfl
  have g₁ : IsGenericFlag (Ω' := M.Ω) T.Fl.j T.Fl.V₀ T.Fl.b T.Fl.deg := T.Fl.generic
  have g₂ : IsGenericFlag (Ω' := M'.Ω) (T'.Fl.j.comp θ.toAddMonoidHom) T.Fl.V₀
      (fun s k => T'.Fl.b (Equiv.sumCongr π₀ π₀ s) (Fin.cast (hrl s).symm k)) T'.Fl.deg :=
    isGenericFlag_transport ψ (fun a => by
        show T'.A.fn (ψ.symm (ψ a)) = T'.A.fn a
        rw [ψ.symm_apply_apply]) θ (fun a e => hθs a e) T'.Fl.j (Equiv.sumCongr π₀ π₀) hrl T.Fl.V₀ T'.Fl.V₀
      (fun s e => hθV s _ (by simpa [Equiv.sumCongr] using (hlab s)) e) T'.Fl.b T'.Fl.deg T'.Fl.generic
  obtain ⟨Ω₃, fΩ, i₁, i₂, hi, ⟨n₁, n₂, hn₁, hn, hf₁, hf₂⟩, hflag⟩ := PositivityTheory.UnitarySelfGeneration.l_genflag T.A.Ω₀ M.Ω M'.Ω T.Fl.Li₀ T.A.Li T'.A.Li
    T.Fl.j (T'.Fl.j.comp θ.toAddMonoidHom) (CMType H ⊕ CMType H) (labelRk D) T.Fl.V₀ T.Fl.b _ T.Fl.deg T'.Fl.deg g₁ g₂
  have hn₂ : 0 < n₂ := by
    have := Nat.mul_pos hn₁ (IsGenericFlag_deg_pos g₁)
    rw [hn] at this
    exact Nat.pos_of_mul_pos_right this
  haveI : CharZero M.Ω := charZero_of_injective_ringHom T.A.cst.injective
  haveI : CharZero M'.Ω := charZero_of_injective_ringHom T'.A.cst.injective
  haveI : CharZero Ω₃ := charZero_of_injective_ringHom i₁.injective
  have hfd₁ : FiniteDimensional i₁.fieldRange Ω₃ := FiniteDimensional.of_finrank_pos (by omega)
  have hfd₂ : FiniteDimensional i₂.fieldRange Ω₃ := FiniteDimensional.of_finrank_pos (by omega)
  obtain ⟨K, hK, ι, hι, κ₁, v₁, κ₂, v₂, y, Z, ξ, h₁, h₂, hb₁, hb₂, hy₁, hy₂, harith, hbir, hall, htie, hnorm, hd₁, hd₂, hr₁, hr₂⟩ :=
    PositivityTheory.UnitarySelfGeneration.j_normal M.K M.ι M'.K M'.ι M.Ω M'.Ω Ω₃ i₁ i₂ M.y M'.y (Top.dimFl (CMType H) (D.p + D.q) + 1) T.A.X T'.A.X T.A.ξ T'.A.ξ
      M.arith M'.arith M.birational M'.birational hfd₁ hfd₂ T.A.all T'.A.all T.A.tie T'.A.tie
  have hx₁ : T.A.ξ ≫ T.A.f = (spMap T.A.fn ≫ x₀) ≫ Y.j := by
    rw [Category.assoc, ← hξ]; exact T.A.fn_over
  have hx₂ : T'.A.ξ ≫ T'.A.f = (spMap T'.A.fn ≫ x₀') ≫ Y.j := by
    rw [Category.assoc, ← hξ']; exact T'.A.fn_over
  obtain ⟨A₁, e₁, Fl₁, ψ₁, θ₁, j₁, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ :=
    pull_both i₁ T.A T.Fl (spMap T.A.fn ≫ x₀) Z ξ h₁ κ₁ v₁ hx₁ T.discr T.ht_vb hall htie hnorm hd₁ hb₁
      (fun q => congrFun hy₁ q) hfd₁
  obtain ⟨A₂, e₂, Fl₂, ψ₂, θ₂, j₂, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ :=
    pull_both i₂ T'.A T'.Fl (spMap T'.A.fn ≫ x₀') Z ξ h₂ κ₂ v₂ hx₂ T'.discr T'.ht_vb hall htie hnorm hd₂ hb₂
      (fun q => congrFun hy₂ q) hfd₂

  have hi' : i₁.comp (T.A.fn.comp ψ.toRingHom) = i₂.comp T'.A.fn := by
    ext a
    have := congrArg (fun f => f (ψ a)) hi
    simpa [a₁, a₂, RingHom.algebraMap_toAlgebra] using this
  have hkey : spMap i₁ ≫ spMap T.A.fn ≫ spMap ψ.toRingHom = spMap i₂ ≫ spMap T'.A.fn := by
    rw [spMap_spMap, spMap_spMap, spMap_spMap, hi']
  have hk3 : ∀ {W : Scheme.{0}} (t : Sp T'.A.Ω₀ ⟶ W), spMap i₂ ≫ spMap T'.A.fn ≫ t =
      spMap i₁ ≫ spMap T.A.fn ≫ spMap ψ.toRingHom ≫ t := by
    intro W t
    rw [← Category.assoc, ← hkey]
    simp only [Category.assoc]
  have hX₁ : A₁.ξ ≫ A₁.f = (spMap i₁ ≫ spMap T.A.fn ≫ x₀) ≫ Y.j := by
    have hd : ξ ≫ h₁ = spMap i₁ ≫ T.A.ξ := hd₁
    calc A₁.ξ ≫ A₁.f = (A₁.ξ ≫ e₁.hom) ≫ h₁ ≫ T.A.f := by rw [p2, Category.assoc]
      _ = (ξ ≫ h₁) ≫ T.A.f := by rw [p1, Category.assoc]
      _ = spMap i₁ ≫ T.A.ξ ≫ T.A.f := by rw [hd, Category.assoc]
      _ = _ := by rw [hx₁]; simp only [Category.assoc]
  have hX₂ : A₂.ξ ≫ A₂.f = (spMap i₂ ≫ spMap T'.A.fn ≫ x₀') ≫ Y.j := by
    have hd : ξ ≫ h₂ = spMap i₂ ≫ T'.A.ξ := hd₂
    calc A₂.ξ ≫ A₂.f = (A₂.ξ ≫ e₂.hom) ≫ h₂ ≫ T'.A.f := by rw [q2, Category.assoc]
      _ = (ξ ≫ h₂) ≫ T'.A.f := by rw [q1, Category.assoc]
      _ = spMap i₂ ≫ T'.A.ξ ≫ T'.A.f := by rw [hd, Category.assoc]
      _ = _ := by rw [hx₂]; simp only [Category.assoc]
  have hfst₃ : (spMap i₂ ≫ spMap T'.A.fn ≫ x₀') ≫ Limits.pullback.fst _ _ =
      (spMap i₁ ≫ spMap T.A.fn ≫ x₀) ≫ Limits.pullback.fst _ _ ≫ Φ.hom := by
    simp only [Category.assoc]
    rw [hk3, hfst]
  have hsnd₃ : (spMap i₂ ≫ spMap T'.A.fn ≫ x₀') ≫ Limits.pullback.snd _ _ =
      (spMap i₁ ≫ spMap T.A.fn ≫ x₀) ≫ Limits.pullback.snd _ _ := by
    simp only [Category.assoc]
    rw [hk3, hsnd]
  have hc₁ : (spMap i₁ ≫ spMap T.A.fn ≫ x₀) ≫ Limits.pullback.snd _ _ = spMap A₁.cst := by
    rw [p3, ← spMap_spMap, ← hcst]
    simp only [Category.assoc]
  have hc₂ : (spMap i₂ ≫ spMap T'.A.fn ≫ x₀') ≫ Limits.pullback.snd _ _ = spMap A₂.cst := by
    rw [q3, ← spMap_spMap, ← hcst']
    simp only [Category.assoc]
  have hAc : A₁.cst = A₂.cst := spMap_inj (by rw [← hc₁, ← hc₂, hsnd₃])
  have hξe : A₂.ξ ≫ (e₂ ≪≫ e₁.symm).hom = A₁.ξ := by
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, q1, ← p1, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨φ, hφt, -, hφV, hφz⟩ := hCmp E H D l Xo c O O β β Y Y g Φ n S Ω₃ K ι y A₁ A₂ (e₂ ≪≫ e₁.symm) _ _ hβ hβ hs hξe hX₁ hX₂
    hfst₃ hsnd₃ hAc hc₁ (fun p hp => by rw [q4, p4]; exact hR p hp)

  let ψ₃ : A₂.Ω₀ ≃+* A₁.Ω₀ := ψ₂.symm.trans (ψ.trans ψ₁)
  let θ₃ : Fl₁.Li₀ ≃+ Fl₂.Li₀ := θ₁.symm.trans (θ.trans θ₂)
  have hθ₃ : ∀ e, θ₃ (θ₁ e) = θ₂ (θ e) := fun e => by simp [θ₃]
  have hfn : A₁.fn.comp ψ₃.toRingHom = A₂.fn := by
    ext a
    have h1 := congrArg (fun f => f (ψ (ψ₂.symm a))) p7
    have h2 := congrArg (fun f => f (ψ₂.symm a)) hi'
    have h3 := congrArg (fun f => f (ψ₂.symm a)) q7
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply] at h1 h2 h3
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ψ₃, RingEquiv.trans_apply]
    rw [h1, h2, ← h3]
  have hψc : (dualMap ψ₃.toRingHom).comp (dualMap ψ₂.toRingHom) = (dualMap ψ₁.toRingHom).comp (dualMap ψ.toRingHom) := by
    rw [← GlobalTheory.CompanionTheory.Ar.FlagPull.dualMap_comp, ← GlobalTheory.CompanionTheory.Ar.FlagPull.dualMap_comp]
    congr 1
    ext a
    simp [ψ₃]
  have htw : ∀ e, TwTan n Y Y (Fl₁.M₀.pt e).left (spMap (dualMap ψ₃.toRingHom) ≫ (Fl₂.M₀.pt (θ₃ e)).left) := by
    intro e
    obtain ⟨e₀, rfl⟩ := θ₁.surjective e
    rw [hθ₃, q8, p8, ← Category.assoc, spMap_spMap, hψc, ← spMap_spMap, Category.assoc]
    exact twTan_pre _ (hθt e₀)
  obtain ⟨-, hsteps⟩ := GlobalTheory.T.twisted_hodge_cpt_flag E H D l Xo c O O β β Y Y g Φ n S Ω₃ K ι y A₁ A₂ Fl₁ Fl₂ ψ₃ θ₃ φ hβ hβ hfn hφt htw
  have hst : ∀ s k, (flagStep Ω₃ (Fl₁.b s) k).map (φ : A₁.Li →ₗ[Ω₃] A₂.Li) =
      flagStep Ω₃ (Fl₂.b (Equiv.sumCongr π₀ π₀ s)) k := by
    intro s
    obtain ⟨cc, hcl, hcs⟩ := exists_basis g₁ s
    obtain ⟨m₁, hm₁⟩ := exists_coeff g₁ s cc hcs
    obtain ⟨m₂, hm₂⟩ := exists_coeff g₂ s cc hcs
    have hrow := hflag s cc m₁ m₂ hcl hcs hm₁ hm₂
    refine hsteps s (Equiv.sumCongr π₀ π₀ s) _ (fun q => θ₁ (cc q)) (fun q a => i₁ (m₁ q a)) ?_ ?_
    · intro k
      congr 1
      funext a
      rw [p6, hm₁ a, map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [p5.1, p9]
    · intro k
      refine (flagStep_cast (hrl s).symm (Fl₂.b (Equiv.sumCongr π₀ π₀ s)) k).symm.trans ?_
      have e1 : (fun a => Fl₂.b (Equiv.sumCongr π₀ π₀ s) (Fin.cast (hrl s).symm a)) =
          fun a => ∑ q, i₂ (m₂ q a) • Fl₂.j (θ₃ (θ₁ (cc q))) := by
        funext a
        rw [q6, hm₂ a, map_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [q5.1, hθ₃, q9]
        rfl
      exact (congrArg (fun f => flagStep Ω₃ f k) e1).trans
        (flagStep_rows (fun q => Fl₂.j (θ₃ (θ₁ (cc q)))) (fun q a => i₂ (m₂ q a)) (fun q a => i₁ (m₁ q a))
          (fun i => (hrow i).symm) k)
  have hemb : ∀ s, A₂.emb (Equiv.sumCongr π₀ π₀ s) = (A₁.emb s).comp g.s.toRingHom := by
    intro s
    show A₂.cst.comp (labelEmb c (Sum.map π₀ π₀ s)) = (A₁.cst.comp (labelEmb c s)).comp g.s.toRingHom
    rw [hlab s, hAc]
    rfl
  have hgram := GlobalTheory.T.hodge_compactification_interior_point hTh E H D l Xo c O β Y S Ω₃ K ι y A₁ Fl₁ hβ
  obtain ⟨b, d, hbm, hbn, hbz⟩ := GlobalTheory.T.hodge_cpt_multihomog_form E H D l Xo c O β Y S Ω₃ K ι y A₁ _ hX₁ hβ
  refine ⟨K, hK, ι, hι, κ₁, v₁, κ₂, v₂, Ω₃, fΩ, inferInstance, y, b, d, hb₁, hb₂, ?_, ?_, harith, hbm, hbn, ?_, ?_, ?_⟩
  · rw [hy₁]
    exact (PositivityTheory.UnitarySelfGeneration.t_ideal M.K M.ι M.Ω Ω₃ i₁ M.y).1
  · rw [hy₂]
    exact (PositivityTheory.UnitarySelfGeneration.t_ideal M'.K M'.ι M'.Ω Ω₃ i₂ M'.y).1
  · rw [hr₁, hf₁]
    exact hn₁.ne'
  · rw [hr₁, hr₂, hf₁, hf₂]
    exact hn
  · intro r L L' hL hL'
    have hdeg : (Fl₁.rootLat (r.1, r.2)).IsDegOn Set.univ y L.a (i₁ (T.e r)) := by
      have := p10 _ _ T.roots r
      rw [hL.1, T.sing_deg]
      exact this
    have hdeg' : (Fl₂.rootLat (π₀ r.1, r.2)).IsDegOn Set.univ y L'.a (i₂ (T'.e (π₀ r.1, r.2))) := by
      have := q10 _ _ T'.roots (π₀ r.1, r.2)
      rw [hL'.1, T'.sing_deg]
      exact this
    have hH := p11 r (T.e r) (T.sing r) L (T.hodge r) hL
    have hH' := q11 (π₀ r.1, r.2) (T'.e (π₀ r.1, r.2)) (T'.sing (π₀ r.1, r.2)) L' (T'.hodge _) hL'
    obtain ⟨f, f', hiso, hdef⟩ := GlobalTheory.T.hodge_cpt_iso_compare E H D l Xo c O O β β Y Y S Ω₃ K ι y A₁ A₂ (e₂ ≪≫ e₁.symm) φ Fl₁ Fl₂ r.1 (π₀ r.1) r.2
      (i₁ (T.e r)) (i₂ (T'.e (π₀ r.1, r.2))) L L' hbir hξe
      (fun q h v => ⟨hφV (.inl r.1) (.inl (π₀ r.1)) (hemb (.inl r.1)) q h v, hφV (.inr r.1) (.inr (π₀ r.1)) (hemb (.inr r.1)) q h v⟩)
      (fun k => ⟨hst (.inl r.1) k, hst (.inr r.1) k⟩) hφz hdeg hdeg' hH hH' hgram
    exact ⟨f, f', hiso, fun w hw => hdef w (hbz w hw.1 hw.2)⟩

end GlobalTheory.CompanionTheory.Ar.PairIsoK

namespace PositivityTheory.UnitarySelfGeneration

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder

/- English proof (translation)
The claim follows from `@GlobalTheory.CompanionTheory.Ar.PairIsoK.pair_iso`.
-/
theorem pair_iso : HodgeComparisonCompatibility → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (_ : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (π : CMType H ≃ CMType H) (S : Finset ℕ) (n : ℕ) (M M' : Top.RootModel (CMType H) (D.p + D.q)) (T : HodgeTie Y S n M) (T' : HodgeTie Y S n M'), Mono (spMap β) → Φ.hom ≫ Xo.s = Xo.s → (∀ τ, (π τ).1 = τ.1.comp g.σ.toRingHom) → IsImageCpt Φ T.A T'.A → (∀ p ∈ S, T'.A.R p = T.A.R p) → ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (κ : M.K → K) (v : (Σ k, M.ι k) → Σ k, ι k) (κ' : M'.K → K) (v' : (Σ k, M'.ι k) → Σ k, ι k) (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (y : (Σ k, ι k) → Ω) (b : MRing ι) (d : K → ℕ), IsBlockMap κ v ∧ IsBlockMap κ' v' ∧ mCoordIdeal (y ∘ v) = M.P ∧ mCoordIdeal (y ∘ v') = M'.P ∧ IsArithVar (mCoordIdeal y) (Top.dimFl (CMType H) (D.p + D.q) + 1) ∧ IsMultiHomog b d ∧ b ∉ mCoordIdeal y ∧ IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) ≠ 0 ∧ IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) * T.Fl.deg = IntermediateField.relfinrank (blockFnField (y ∘ v')) (blockFnField y) * T'.Fl.deg ∧ ∀ (r : CMType H × Fin (D.p + D.q)) (L L' : HermLine ι), IsPullHerm κ v (T.sing r) L → IsPullHerm κ' v' (T'.sing (π r.1, r.2)) L' → IsoLineOn (mCoordIdeal y) {z | z ∈ mcPts (mCoordIdeal y) ∧ evC z b ≠ 0} L L' :=
  @GlobalTheory.CompanionTheory.Ar.PairIsoK.pair_iso

end PositivityTheory.UnitarySelfGeneration
