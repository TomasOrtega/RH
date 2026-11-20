import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.SConjSpaceC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentsThetaPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedFactorEqProductAbove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivOfIsSubquotient

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep

namespace UpperTheory.CBC.SatakeConjugationGLMap

section Local

variable {n : ℕ}

def glEquiv {L1 L2 : Type} [Field L1] [Field L2] (κ : L1 →+* L2) (hκ : Function.Bijective κ) :
    GL (Fin n) L1 ≃* GL (Fin n) L2 where
  toFun := Matrix.GeneralLinearGroup.map κ
  invFun := Matrix.GeneralLinearGroup.map (RingEquiv.ofBijective κ hκ).symm.toRingHom
  left_inv _ := Units.ext (Matrix.ext fun _ _ => (RingEquiv.ofBijective κ hκ).symm_apply_apply _)
  right_inv _ := Units.ext (Matrix.ext fun _ _ => (RingEquiv.ofBijective κ hκ).apply_symm_apply _)
  map_mul' := map_mul _

/- English proof (translation)
Take `⟨h, rfl⟩` from `MonoidHom.mem_range.1 hg`. Conclude with `MonoidHom.mem_range.2 ⟨Formalism.UG.bc (f.restrict O1 O2 hf) h, Units.ext (Matrix.ext fun _ _ => rfl)⟩`.
-/
theorem mem_GLint_map {L1 L2 : Type} [Field L1] [Field L2] (f : L1 →+* L2) {O1 : Subring L1} {O2 : Subring L2}
    (hf : ∀ x ∈ O1, f x ∈ O2) {g : GL (Fin n) L1} (hg : g ∈ Formalism.UG.GLint (Fin n) O1) :
    Matrix.GeneralLinearGroup.map f g ∈ Formalism.UG.GLint (Fin n) O2 := by
  obtain ⟨h, rfl⟩ := MonoidHom.mem_range.1 hg
  exact MonoidHom.mem_range.2 ⟨Formalism.UG.bc (f.restrict O1 O2 hf) h, Units.ext (Matrix.ext fun _ _ => rfl)⟩

def InS {L : Type} [Field L] (O : Subring L) (ϖ : L) (j : ℕ) (g : GL (Fin n) L) : Prop :=
  ∃ a ∈ Formalism.UG.GLint (Fin n) O, ∃ b ∈ Formalism.UG.GLint (Fin n) O,
    (g : Matrix (Fin n) (Fin n) L) = (a : Matrix (Fin n) (Fin n) L) * Formalism.UG.diagJ n ϖ j * (b : Matrix (Fin n) (Fin n) L)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Tj_eq {L : Type} [Field L] (O : Subring L) (ϖ : L) (j : ℕ) :
    Formalism.UG.Tj ℂ n O ϖ j = Set.indicator {g | InS O ϖ j g} 1 := rfl

/- English proof (translation)
Take `⟨a, ha, b, hb, e⟩` from `h`. Use `⟨_, mem_GLint_map f hf ha, _, mem_GLint_map f hf hb, ?_⟩` and prove the remaining obligations. Establish `hD : (Formalism.UG.diagJ n ϖ j).map f = Formalism.UG.diagJ n (f ϖ) j`. Use extensionality with `i k`. Simplify using `only [Formalism.UG.diagJ, Matrix.map_apply, Matrix.diagonal_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Express the relevant statement in the definitionally equal form `(g : Matrix (Fin n) (Fin n) L1).map f = (a : Matrix (Fin n) (Fin n) L1).map f * Formalism.UG.diagJ n (f ϖ) j * (b : Matrix (Fin n) (Fin n) L1).map f`. Rewrite using `[e, ← hD, Matrix.map_mul, Matrix.map_mul]`.
-/
theorem inS_map {L1 L2 : Type} [Field L1] [Field L2] (f : L1 →+* L2) {O1 : Subring L1} {O2 : Subring L2}
    (hf : ∀ x ∈ O1, f x ∈ O2) {ϖ : L1} {j : ℕ} {g : GL (Fin n) L1} (h : InS O1 ϖ j g) :
    InS O2 (f ϖ) j (Matrix.GeneralLinearGroup.map f g) := by
  obtain ⟨a, ha, b, hb, e⟩ := h
  refine ⟨_, mem_GLint_map f hf ha, _, mem_GLint_map f hf hb, ?_⟩
  have hD : (Formalism.UG.diagJ n ϖ j).map f = Formalism.UG.diagJ n (f ϖ) j := by
    ext i k
    simp only [Formalism.UG.diagJ, Matrix.map_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  change (g : Matrix (Fin n) (Fin n) L1).map f =
    (a : Matrix (Fin n) (Fin n) L1).map f * Formalism.UG.diagJ n (f ϖ) j * (b : Matrix (Fin n) (Fin n) L1).map f
  rw [e, ← hD, Matrix.map_mul, Matrix.map_mul]

/- English proof (translation)
Establish `hO' : ∀ x ∈ O2, (RingEquiv.ofBijective κ hκ).symm.toRingHom x ∈ O1` using `fun x hx => (hO _).2 (by`. Rewrite using `[show κ ((RingEquiv.ofBijective κ hκ).symm.toRingHom x) = x from (RingEquiv.ofBijective κ hκ).apply_symm_apply x])` and apply the resulting hypothesis. Use function extensionality and compare the values at `g`. Establish `key : InS O2 (κ ϖ) j (glEquiv (n` using `n) κ hκ g) ↔ InS O1 ϖ j g := by`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `inS_map (RingEquiv.ofBijective κ hκ).symm.toRingHom hO' h` as an intermediate fact. Establish `e1 : (RingEquiv.ofBijective κ hκ).symm.toRingHom (κ ϖ) = ϖ` using `(RingEquiv.ofBijective κ hκ).symm_apply_apply ϖ`. Establish `e2 : Matrix.GeneralLinearGroup.map (RingEquiv.ofBijective κ hκ).symm.toRingHom (glEquiv (n` using `n) κ hκ g) = g := (glEquiv (n := n) κ hκ).symm_apply_apply g`. Rewrite `this` using `[e1, e2]`. Then use the resulting hypothesis.

Introduce `h`. Conclude with `inS_map κ (fun x hx => (hO x).1 hx) h`. Rewrite using `[Function.comp_apply, Tj_eq, Tj_eq]`. Distinguish the cases in `hg : InS O1 ϖ j g`. Rewrite using `[Set.indicator_of_mem (show glEquiv (n := n) κ hκ g ∈ {g | InS O2 (κ ϖ) j g} from key.2 hg), Set.indicator_of_mem (show g ∈ {g | InS O1 ϖ j g} from hg)]`.

Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem (show glEquiv (n := n) κ hκ g ∉ {g | InS O2 (κ ϖ) j g} from mt key.1 hg), Set.indicator_of_notMem (show g ∉ {g | InS O1 ϖ j g} from hg)]`.
-/
theorem Tj_comp {L1 L2 : Type} [Field L1] [Field L2] (κ : L1 →+* L2) (hκ : Function.Bijective κ)
    {O1 : Subring L1} {O2 : Subring L2} (hO : ∀ x, x ∈ O1 ↔ κ x ∈ O2) (ϖ : L1) (j : ℕ) :
    Formalism.UG.Tj ℂ n O2 (κ ϖ) j ∘ (glEquiv (n := n) κ hκ) = Formalism.UG.Tj ℂ n O1 ϖ j := by
  have hO' : ∀ x ∈ O2, (RingEquiv.ofBijective κ hκ).symm.toRingHom x ∈ O1 := fun x hx => (hO _).2 (by
    rwa [show κ ((RingEquiv.ofBijective κ hκ).symm.toRingHom x) = x from
      (RingEquiv.ofBijective κ hκ).apply_symm_apply x])
  funext g
  have key : InS O2 (κ ϖ) j (glEquiv (n := n) κ hκ g) ↔ InS O1 ϖ j g := by
    constructor
    · intro h
      have := inS_map (RingEquiv.ofBijective κ hκ).symm.toRingHom hO' h
      have e1 : (RingEquiv.ofBijective κ hκ).symm.toRingHom (κ ϖ) = ϖ :=
        (RingEquiv.ofBijective κ hκ).symm_apply_apply ϖ
      have e2 : Matrix.GeneralLinearGroup.map (RingEquiv.ofBijective κ hκ).symm.toRingHom
          (glEquiv (n := n) κ hκ g) = g := (glEquiv (n := n) κ hκ).symm_apply_apply g
      rwa [e1, e2] at this
    · intro h
      exact inS_map κ (fun x hx => (hO x).1 hx) h
  rw [Function.comp_apply, Tj_eq, Tj_eq]
  by_cases hg : InS O1 ϖ j g
  · rw [Set.indicator_of_mem (show glEquiv (n := n) κ hκ g ∈ {g | InS O2 (κ ϖ) j g} from key.2 hg),
      Set.indicator_of_mem (show g ∈ {g | InS O1 ϖ j g} from hg)]
    rfl
  · rw [Set.indicator_of_notMem (show glEquiv (n := n) κ hκ g ∉ {g | InS O2 (κ ϖ) j g} from mt key.1 hg),
      Set.indicator_of_notMem (show g ∉ {g | InS O1 ϖ j g} from hg)]

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `hO : ∀ x, x ∈ Formalism.UG.Ov E w1 ↔ κ x ∈ Formalism.UG.Ov E w2` using `fun x => by`. Express the relevant statement in the definitionally equal form `x ∈ w1.adicCompletionIntegers E ↔ κ x ∈ w2.adicCompletionIntegers E`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers, hv]`. Establish `hK : ∀ g, g ∈ GlobalTheory.LFun.KGL w1 n ↔ glEquiv (n` using `n) κ hκ g ∈ GlobalTheory.LFun.KGL w2 n := fun g => ⟨fun hg => mem_GLint_map κ (fun x hx => (hO x).1 hx) hg, fun hg => by`. Use `mem_GLint_map (RingEquiv.ofBijective κ hκ).symm.toRingHom (fun x hx => (hO _).2 (by` as an intermediate fact.

Rewrite using `[show κ ((RingEquiv.ofBijective κ hκ).symm.toRingHom x) = x from (RingEquiv.ofBijective κ hκ).apply_symm_apply x])) hg` and apply the resulting hypothesis. Rewrite using `[show Matrix.GeneralLinearGroup.map (RingEquiv.ofBijective κ hκ).symm.toRingHom (glEquiv (n := n) κ hκ g) = g from (glEquiv (n := n) κ hκ).symm_apply_apply g] at this⟩` and apply the resulting hypothesis. Establish `hcomp : ρ.comp (Matrix.GeneralLinearGroup.map κ) = ρ.comp (glEquiv (n` using `n) κ hκ).toMonoidHom := MonoidHom.ext fun _ => rfl`. Establish `hρ : (ρ.comp (glEquiv (n` using `n) κ hκ).toMonoidHom).comp (glEquiv (n := n) κ hκ).symm.toMonoidHom = ρ := MonoidHom.ext fun g => show ρ (glEquiv (n := n) κ hκ ((glEquiv (n := n) κ hκ).symm g)) = ρ g by`. Rewrite using `[MulEquiv.apply_symm_apply]`.

Rewrite using `[hcomp]`. Establish `hfix : ∀ x, x ∈ GlobalTheory.PRep.fixed (ρ.comp (glEquiv (n` using `n) κ hκ).toMonoidHom) (GlobalTheory.LFun.KGL w1 n) ↔ x ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w2 n) := fun x => by`. Use `GlobalTheory.LFun.mem_fixed_comp_symm (ρ := ρ.comp (glEquiv (n := n) κ hκ).toMonoidHom) (x := x) (glEquiv (n := n) κ hκ) hK` as an intermediate fact. Rewrite `this` using `[hρ]`. Conclude with `this.symm`.

Use `⟨?_, fun x hx h0 => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `GlobalTheory.PRep.fixed _ _ ≠ ⊥`. Rewrite using `[Submodule.ext hfix]`. Conclude with `h.1`. Establish `hs` using `h.2 x ((hfix x).1 hx) h0`.

Use `⟨h0, hx, hs.2.2.1, fun ϖ hϖ j hj => ?_⟩` and prove the remaining obligations. Establish `hϖ2 : Formalism.UG.IsUnifV E w2 (κ ϖ)`. Unfold `Formalism.UG.IsUnifV at hϖ ⊢`. Rewrite using `[hv]`. Conclude with `hϖ`.

Establish `hh` using `GlobalTheory.LFun.heckeVec_comp_symm (ρ := ρ.comp (glEquiv (n := n) κ hκ).toMonoidHom) (x := x) (glEquiv (n := n) κ hκ) hK (h' := Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w2) (κ ϖ) j) (GlobalTheory.LFun.Tj_mem_hecke hϖ2 j).1 hx`. Rewrite `hh` using `[hρ, Tj_comp κ hκ hO ϖ j]`. Rewrite using `[← hh, hs.2.2.2 _ hϖ2 j hj, hq]`.
-/
theorem hasSatGL_comp {w1 w2 : HeightOneSpectrum (𝓞 E)} (κ : w1.adicCompletion E →+* w2.adicCompletion E)
    (hκ : Function.Bijective κ) (hv : ∀ x, Valued.v (κ x) = Valued.v x) (hq : Formalism.UG.qV E w1 = Formalism.UG.qV E w2)
    {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin n) (w2.adicCompletion E)) V}
    {B : Multiset ℂˣ} (h : GlobalTheory.LFun.HasSatGL w2 ρ B) :
    GlobalTheory.LFun.HasSatGL w1 (ρ.comp (Matrix.GeneralLinearGroup.map κ)) B := by
  have hO : ∀ x, x ∈ Formalism.UG.Ov E w1 ↔ κ x ∈ Formalism.UG.Ov E w2 := fun x => by
    change x ∈ w1.adicCompletionIntegers E ↔ κ x ∈ w2.adicCompletionIntegers E
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers, hv]
  have hK : ∀ g, g ∈ GlobalTheory.LFun.KGL w1 n ↔ glEquiv (n := n) κ hκ g ∈ GlobalTheory.LFun.KGL w2 n := fun g =>
    ⟨fun hg => mem_GLint_map κ (fun x hx => (hO x).1 hx) hg, fun hg => by
      have := mem_GLint_map (RingEquiv.ofBijective κ hκ).symm.toRingHom (fun x hx => (hO _).2 (by
        rwa [show κ ((RingEquiv.ofBijective κ hκ).symm.toRingHom x) = x from
          (RingEquiv.ofBijective κ hκ).apply_symm_apply x])) hg
      rwa [show Matrix.GeneralLinearGroup.map (RingEquiv.ofBijective κ hκ).symm.toRingHom
          (glEquiv (n := n) κ hκ g) = g from (glEquiv (n := n) κ hκ).symm_apply_apply g] at this⟩
  have hcomp : ρ.comp (Matrix.GeneralLinearGroup.map κ) = ρ.comp (glEquiv (n := n) κ hκ).toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  have hρ : (ρ.comp (glEquiv (n := n) κ hκ).toMonoidHom).comp (glEquiv (n := n) κ hκ).symm.toMonoidHom = ρ :=
    MonoidHom.ext fun g => show ρ (glEquiv (n := n) κ hκ ((glEquiv (n := n) κ hκ).symm g)) = ρ g by
      rw [MulEquiv.apply_symm_apply]
  rw [hcomp]
  have hfix : ∀ x, x ∈ GlobalTheory.PRep.fixed (ρ.comp (glEquiv (n := n) κ hκ).toMonoidHom) (GlobalTheory.LFun.KGL w1 n) ↔
      x ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w2 n) := fun x => by
    have := GlobalTheory.LFun.mem_fixed_comp_symm (ρ := ρ.comp (glEquiv (n := n) κ hκ).toMonoidHom) (x := x)
      (glEquiv (n := n) κ hκ) hK
    rw [hρ] at this
    exact this.symm
  refine ⟨?_, fun x hx h0 => ?_⟩
  · change GlobalTheory.PRep.fixed _ _ ≠ ⊥
    rw [Submodule.ext hfix]
    exact h.1
  · have hs := h.2 x ((hfix x).1 hx) h0
    refine ⟨h0, hx, hs.2.2.1, fun ϖ hϖ j hj => ?_⟩
    have hϖ2 : Formalism.UG.IsUnifV E w2 (κ ϖ) := by
      unfold Formalism.UG.IsUnifV at hϖ ⊢
      rw [hv]
      exact hϖ
    have hh := GlobalTheory.LFun.heckeVec_comp_symm (ρ := ρ.comp (glEquiv (n := n) κ hκ).toMonoidHom) (x := x)
      (glEquiv (n := n) κ hκ) hK (h' := Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w2) (κ ϖ) j) (GlobalTheory.LFun.Tj_mem_hecke hϖ2 j).1 hx
    rw [hρ, Tj_comp κ hκ hO ϖ j] at hh
    rw [← hh, hs.2.2.2 _ hϖ2 j hj, hq]

end Local

section Conj

variable {M : Type} [Field M] [NumberField M]

/- English proof (translation)
Use `(eq_conjSrc fun x => ?_).symm` and prove the remaining obligations. Use `conjPl_conjSrc c.symm w (c x)` as an intermediate fact. Rewrite `this` using `[c.symm_apply_apply]`. Conclude with `this.symm`.
-/
theorem conjSrc_conjSrc_symm (c : M ≃+* M) (w : HeightOneSpectrum (𝓞 M)) : conjSrc c (conjSrc c.symm w) = w := by
  refine (eq_conjSrc fun x => ?_).symm
  have := conjPl_conjSrc c.symm w (c x)
  rw [c.symm_apply_apply] at this
  exact this.symm

/- English proof (translation)
Introduce `x y h`. Use `FiniteAdeleRing.ext _ fun u => ?_` and prove the remaining obligations. Take `⟨v, rfl⟩ : ∃ v, conjSrc c v = u` from `⟨_, conjSrc_conjSrc_symm c u⟩`. Conclude with `(conjLoc c v).injective ((pLoc_conjFin c x v).symm.trans ((congrArg (pLoc M v) h).trans (pLoc_conjFin c y v)))`.
-/
theorem conjFin_injective (c : M ≃+* M) : Function.Injective (conjFin c) := by
  intro x y h
  refine FiniteAdeleRing.ext _ fun u => ?_
  obtain ⟨v, rfl⟩ : ∃ v, conjSrc c v = u := ⟨_, conjSrc_conjSrc_symm c u⟩
  exact (conjLoc c v).injective
    ((pLoc_conjFin c x v).symm.trans ((congrArg (pLoc M v) h).trans (pLoc_conjFin c y v)))

/- English proof (translation)
Establish `h1 : (s (sFin M 1)).1 = 0`. Set `y : Ad M` to `((1, 0) : InfiniteAdeleRing M × Af M)`. Establish `hx : (s.symm y).2 = 0`. Apply `conjFin_injective c` to reduce the goal to its premises. Rewrite using `[map_zero, ← hs, s.apply_symm_apply]`.

Establish `h0 : sFin M 1 * s.symm y = 0` using `Prod.ext (by change (0 : InfiniteAdeleRing M) * (s.symm y).1 = 0; exact zero_mul _) (by change (1 : Af M) * (s.symm y).2 = 0; rw [hx, mul_zero])`. Establish `h2 : s (sFin M 1) * y = 0`. Rewrite using `[← s.apply_symm_apply y, ← map_mul, h0, map_zero]`. Establish `h3` using `congrArg (fun z : Ad M => z.1) h2`. Express the relevant statement in the definitionally equal form `(s (sFin M 1)).1 * 1 = 0 at h3`.

Rewrite `h3` using `[mul_one]`. Then use the resulting hypothesis. Use `Prod.ext ?_ (hs _)` and prove the remaining obligations. Establish `e : sFin M z = sFin M 1 * sFin M z` using `by rw [← map_mul, one_mul]`. Rewrite using `[e, map_mul]`. Express the relevant statement in the definitionally equal form `(s (sFin M 1)).1 * (s (sFin M z)).1 = 0`.

Rewrite using `[h1, zero_mul]`.
-/
theorem s_sFin (c : M ≃+* M) (s : Ad M ≃+* Ad M) (hs : ∀ x, (s x).2 = conjFin c x.2) (z : Af M) :
    s (sFin M z) = sFin M (conjFin c z) := by
  have h1 : (s (sFin M 1)).1 = 0 := by
    let y : Ad M := ((1, 0) : InfiniteAdeleRing M × Af M)
    have hx : (s.symm y).2 = 0 := by
      apply conjFin_injective c
      rw [map_zero, ← hs, s.apply_symm_apply]
    have h0 : sFin M 1 * s.symm y = 0 := Prod.ext
      (by change (0 : InfiniteAdeleRing M) * (s.symm y).1 = 0; exact zero_mul _)
      (by change (1 : Af M) * (s.symm y).2 = 0; rw [hx, mul_zero])
    have h2 : s (sFin M 1) * y = 0 := by
      rw [← s.apply_symm_apply y, ← map_mul, h0, map_zero]
    have h3 := congrArg (fun z : Ad M => z.1) h2
    change (s (sFin M 1)).1 * 1 = 0 at h3
    rwa [mul_one] at h3
  refine Prod.ext ?_ (hs _)
  have e : sFin M z = sFin M 1 * sFin M z := by rw [← map_mul, one_mul]
  rw [e, map_mul]
  change (s (sFin M 1)).1 * (s (sFin M z)).1 = 0
  rw [h1, zero_mul]

/- English proof (translation)
Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `s ((1 : Matrix (Fin a) (Fin a) (Ad M)) i j - sFin M ((1 : Matrix (Fin a) (Fin a) (Af M)) i j) + sFin M ((k : Matrix (Fin a) (Fin a) (Af M)) i j)) = (1 : Matrix (Fin a) (Fin a) (Ad M)) i j - sFin M ((1 : Matrix (Fin a) (Fin a) (Af M)) i j) + sFin M (conjFin c ((k : Matrix (Fin a) …`. Rewrite using `[map_add, map_sub, s_sFin c s hs, s_sFin c s hs]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne h]`.
-/
theorem map_s_finGL (c : M ≃+* M) (s : Ad M ≃+* Ad M) (hs : ∀ x, (s x).2 = conjFin c x.2) {a : ℕ}
    (k : GL (Fin a) (Af M)) :
    Matrix.GeneralLinearGroup.map s.toRingHom (finGL M a k) = finGL M a (Matrix.GeneralLinearGroup.map (conjFin c) k) := by
  ext i j
  change s ((1 : Matrix (Fin a) (Fin a) (Ad M)) i j - sFin M ((1 : Matrix (Fin a) (Fin a) (Af M)) i j) +
      sFin M ((k : Matrix (Fin a) (Fin a) (Af M)) i j)) =
    (1 : Matrix (Fin a) (Fin a) (Ad M)) i j - sFin M ((1 : Matrix (Fin a) (Fin a) (Af M)) i j) +
      sFin M (conjFin c ((k : Matrix (Fin a) (Fin a) (Af M)) i j))
  rw [map_add, map_sub, s_sFin c s hs, s_sFin c s hs]
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.one_apply_ne h]

end Conj

section Glob

variable {M : Type} [Field M] [NumberField M] [IsTotallyReal M] {n : ℕ}

def pre (s : Ad M ≃+* Ad M) (f : GA M n → ℂ) : GA M n → ℂ := fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)

structure Rel (s : Ad M ≃+* Ad M) (P P' : UpperTheory.V.TR.CuspSub M n) : Prop where
  fwd : ∀ φ ∈ P.V, ∃ ψ ∈ P'.V, (ψ : GA M n → ℂ) = pre s φ
  bwd : ∀ ψ ∈ P'.V, ∃ φ ∈ P.V, (ψ : GA M n → ℂ) = pre s φ

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `φ hφ`. Establish `: pre s (φ : GA M n → ℂ) ∈ (Cusp.re P').space`. Rewrite using `[hsp]`. Conclude with `⟨_, ⟨φ, hφ, rfl⟩, rfl⟩`.

Take `⟨ψ, hψ, e⟩` from `this`. Conclude with `⟨ψ, hψ, e.symm⟩`. Introduce `ψ hψ`. Establish `: (ψ : GA M n → ℂ) ∈ (Cusp.re P').space` using `⟨ψ, hψ, rfl⟩`. Rewrite `this` using `[hsp]`.

Take `⟨f, ⟨φ, hφ, rfl⟩, e⟩` from `this`. Conclude with `⟨φ, hφ, e.symm⟩`.
-/
theorem rel_of (s : Ad M ≃+* Ad M) (P P' : UpperTheory.V.TR.CuspSub M n)
    (hsp : (Cusp.re P').space =
      (fun f : GA M n → ℂ => fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)) '' (Cusp.re P).space) :
    Rel s P P' := by
  constructor
  · intro φ hφ
    have : pre s (φ : GA M n → ℂ) ∈ (Cusp.re P').space := by
      rw [hsp]
      exact ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    obtain ⟨ψ, hψ, e⟩ := this
    exact ⟨ψ, hψ, e.symm⟩
  · intro ψ hψ
    have : (ψ : GA M n → ℂ) ∈ (Cusp.re P').space := ⟨ψ, hψ, rfl⟩
    rw [hsp] at this
    obtain ⟨f, ⟨φ, hφ, rfl⟩, e⟩ := this
    exact ⟨φ, hφ, e.symm⟩

omit [IsTotallyReal M] in
/- English proof (translation)
The claim follows from `Units.ext (Matrix.ext fun _ _ => s.apply_symm_apply _)`.
-/
theorem map_map_symm (s : Ad M ≃+* Ad M) (g : GA M n) :
    Matrix.GeneralLinearGroup.map s.toRingHom (Matrix.GeneralLinearGroup.map s.symm.toRingHom g) = g :=
  Units.ext (Matrix.ext fun _ _ => s.apply_symm_apply _)

/- English proof (translation)
Take `⟨ψ, -, e⟩` from `h.fwd φ.1 φ.2`. Rewrite using `[← e]`. Conclude with `ψ.2`.
-/
theorem pre_memSm {s : Ad M ≃+* Ad M} {P P' : UpperTheory.V.TR.CuspSub M n} (h : Rel s P P') (φ : P.V) :
    pre s φ.1.1 ∈ UpperTheory.V.TR.Sm M n := by
  obtain ⟨ψ, -, e⟩ := h.fwd φ.1 φ.2
  rw [← e]
  exact ψ.2

def tT {s : Ad M ≃+* Ad M} {P P' : UpperTheory.V.TR.CuspSub M n} (h : Rel s P P') : P.V →ₗ[ℂ] P'.V where
  toFun φ := ⟨⟨pre s φ.1.1, pre_memSm h φ⟩, by
    obtain ⟨ψ, hψ, e⟩ := h.fwd φ.1 φ.2
    have e' : ψ = ⟨pre s φ.1.1, pre_memSm h φ⟩ := Subtype.ext e
    exact e' ▸ hψ⟩
  map_add' _ _ := Subtype.ext (Subtype.ext (funext fun _ => rfl))
  map_smul' _ _ := Subtype.ext (Subtype.ext (funext fun _ => rfl))

/- English proof (translation)
Use `⟨fun φ φ' e => Subtype.ext (Subtype.ext (funext fun g => ?_)), fun ψ => ?_⟩` and prove the remaining obligations. Use `congrFun (congrArg (fun x : P'.V => (x.1 : GA M n → ℂ)) e) (Matrix.GeneralLinearGroup.map s.symm.toRingHom g)` as an intermediate fact. Express the relevant statement in the definitionally equal form `φ.1.1 (Matrix.GeneralLinearGroup.map s.toRingHom (Matrix.GeneralLinearGroup.map s.symm.toRingHom g)) = φ'.1.1 (Matrix.GeneralLinearGroup.map s.toRingHom (Matrix.GeneralLinearGroup.map s.symm.toRingHom g)) at this`. Rewrite `this` using `[map_map_symm]`. Then use the resulting hypothesis. Take `⟨φ, hφ, e⟩` from `h.bwd ψ.1 ψ.2`.

Use `⟨⟨φ, hφ⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `e.symm`.
-/
theorem tT_bij {s : Ad M ≃+* Ad M} {P P' : UpperTheory.V.TR.CuspSub M n} (h : Rel s P P') : Function.Bijective (tT h) := by
  refine ⟨fun φ φ' e => Subtype.ext (Subtype.ext (funext fun g => ?_)), fun ψ => ?_⟩
  · have := congrFun (congrArg (fun x : P'.V => (x.1 : GA M n → ℂ)) e) (Matrix.GeneralLinearGroup.map s.symm.toRingHom g)
    change φ.1.1 (Matrix.GeneralLinearGroup.map s.toRingHom (Matrix.GeneralLinearGroup.map s.symm.toRingHom g)) =
      φ'.1.1 (Matrix.GeneralLinearGroup.map s.toRingHom (Matrix.GeneralLinearGroup.map s.symm.toRingHom g)) at this
    rwa [map_map_symm] at this
  · obtain ⟨φ, hφ, e⟩ := h.bwd ψ.1 ψ.2
    refine ⟨⟨φ, hφ⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact e.symm

/- English proof (translation)
Establish `hq : Formalism.UG.qV M (conjSrc c v) = Formalism.UG.qV M v` using `GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc c v`. Establish `hloc` using `hasSatGL_comp (conjLoc c v) ⟨(conjLoc c v).injective, ParLaws.conjLoc_surjective c v⟩ (conjLoc_spec c v).2.2 hq hB`. Use `GlobalTheory.BaseChangeBridge.hasSatGL_of_equiv (LinearEquiv.ofBijective (tT h) (tT_bij h)) (fun g φ => ?_) hloc` and prove the remaining obligations. Use `Subtype.ext (Subtype.ext (funext fun x => ?_))` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ.1.1 (Matrix.GeneralLinearGroup.map s.toRingHom x * finGL M n (locGL M n v (Matrix.GeneralLinearGroup.map (conjLoc c v) g))) = φ.1.1 (Matrix.GeneralLinearGroup.map s.toRingHom (x * finGL M n (locGL M n (conjSrc c v) g)))`.

Rewrite using `[map_mul, map_s_finGL c s hs, GlobalTheory.ConjPairLoc.conjFin_locGL]`.
-/
theorem hasSat_conj (c : M ≃+* M) (s : Ad M ≃+* Ad M) (hs : ∀ x, (s x).2 = conjFin c x.2)
    {P P' : UpperTheory.V.TR.CuspSub M n} (h : Rel s P P') (v : HeightOneSpectrum (𝓞 M)) (B : Multiset ℂˣ)
    (hB : P.HasSat v B) : P'.HasSat (conjSrc c v) B := by
  have hq : Formalism.UG.qV M (conjSrc c v) = Formalism.UG.qV M v := GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc c v
  have hloc := hasSatGL_comp (conjLoc c v) ⟨(conjLoc c v).injective, ParLaws.conjLoc_surjective c v⟩
    (conjLoc_spec c v).2.2 hq hB
  refine GlobalTheory.BaseChangeBridge.hasSatGL_of_equiv (LinearEquiv.ofBijective (tT h) (tT_bij h)) (fun g φ => ?_) hloc
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  change φ.1.1 (Matrix.GeneralLinearGroup.map s.toRingHom x *
      finGL M n (locGL M n v (Matrix.GeneralLinearGroup.map (conjLoc c v) g))) =
    φ.1.1 (Matrix.GeneralLinearGroup.map s.toRingHom (x * finGL M n (locGL M n (conjSrc c v) g)))
  rw [map_mul, map_s_finGL c s hs, GlobalTheory.ConjPairLoc.conjFin_locGL]

end Glob

/- English proof (translation)
Use `GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc c w` as an intermediate fact. Rewrite `this` using `[Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]`. Conclude with `this`.
-/
theorem normV_conjSrc {M : Type} [Field M] [NumberField M] (c : M ≃+* M) (w : HeightOneSpectrum (𝓞 M)) :
    Formalism.ConjugateSelfDual.normV (conjSrc c w) = Formalism.ConjugateSelfDual.normV w := by
  have := GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc c w
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply] at this
  exact this

end UpperTheory.CBC.SatakeConjugationGLMap

open UpperTheory.CBC.SatakeConjugationGLMap in
/- English proof (translation)
Introduce `K M _ _ _ _ _ _ σ s hs n P P' hsp`. Use `⟨conjSrc σ.toRingEquiv.symm, conjSrc_injective _, fun w => GlobalTheory.DefU.ClassFin.under_conjSrc σ.toRingEquiv.symm (fun x => σ.symm.commutes x) w, fun w => normV_conjSrc _ w, Filter.Eventually.of_forall fun w B hB => ?_⟩` and prove the remaining obligations. Use `hasSat_conj σ.toRingEquiv s hs.2.2 (rel_of s P P' hsp) _ B hB` as an intermediate fact. Rewrite `this` using `[conjSrc_conjSrc_symm]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.CBC.SConjSatR_holds : UpperTheory.CBC.SConjSatR := by
  intro K M _ _ _ _ _ _ σ s hs n P P' hsp
  refine ⟨conjSrc σ.toRingEquiv.symm, conjSrc_injective _, fun w =>
    GlobalTheory.DefU.ClassFin.under_conjSrc σ.toRingEquiv.symm (fun x => σ.symm.commutes x) w, fun w => normV_conjSrc _ w,
    Filter.Eventually.of_forall fun w B hB => ?_⟩
  have := hasSat_conj σ.toRingEquiv s hs.2.2 (rel_of s P P' hsp) _ B hB
  rwa [conjSrc_conjSrc_symm] at this
