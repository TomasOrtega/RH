import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace GlobalTheory.St.G

/- English proof (translation)
Introduce `D X ιA hA w`. Take `⟨h1, h2⟩` from `hA`. Establish `hgen : ∀ x : X.B.I.E, ιA.symm (Formalism.UG.inclE (F` using `D.host.F) (Ad D.host.F) (X.ιE x)) = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) x := by`. Introduce `x`. Rewrite using `[RingEquiv.symm_apply_eq]`.

Conclude with `(h1 x).symm`. Establish `hgen' : ∀ x : X.B.I.E, ιA (Formalism.UG.inclE (F` using `X.B.I.F) (Af X.B.I.F) x) = Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) (X.ιE x) := h1`. Establish `hint : ∀ a, a ∈ IntAf X.B.I.F X.B.I.E ↔ ιA a ∈ OAd D.host.F D.host.E` using `h2`. Establish `hL' : ∀ c : Fin X.B.I.n → D.host.E, c ∈ (VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E)) ↔ (fun i => X.ιE.symm (c i)) ∈ X.B.I.L`. Introduce `c`.

Rewrite using `[X.L_eq, Submodule.mem_comap]`. Simplify using `[Fintype.linearCombination_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `hw`. Express the relevant statement in the definitionally equal form `w ∈ Submodule.span _ _ at hw`.

Express the relevant statement in the definitionally equal form `(fun i => ιA.symm (w i)) ∈ Submodule.span _ _`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨c, hc, rfl⟩` from `hx`. Use `Submodule.subset_span ⟨⟨fun i => X.ιE.symm (c i), (hL' c).1 hc⟩, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Simplify using `only`. Rewrite using `[← hgen, RingEquiv.apply_symm_apply]`. Consider the case `zero`. Use `Submodule.zero_mem _ using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy`. Establish `: (fun i => ιA.symm ((x + y) i)) = (fun i => ιA.symm (x i)) + (fun i => ιA.symm (y i))`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul r x _ hx`. Establish `hr : ιA.symm (r : D.host.E ⊗[D.host.F] Ad D.host.F) ∈ IntAf X.B.I.F X.B.I.E`.

Rewrite using `[hint, RingEquiv.apply_symm_apply]`. Conclude with `r.2`. Establish `: (fun i => ιA.symm ((r • x) i)) = (⟨_, hr⟩ : IntAf X.B.I.F X.B.I.E) • (fun i => ιA.symm (x i))`. Use function extensionality and compare the values at `i`. Simplify using `[Subring.smul_def, smul_eq_mul, map_mul]`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hx`. Introduce `hw`. Express the relevant statement in the definitionally equal form `_ ∈ Submodule.span _ _ at hw`. Express the relevant statement in the definitionally equal form `w ∈ Submodule.span _ _`.

Establish `key : ∀ v, v ∈ Submodule.span (IntAf X.B.I.F X.B.I.E) (Set.range fun x : X.B.I.L => fun i => Formalism.UG.inclE (F` using `X.B.I.F) (Af X.B.I.F) ((x : Fin X.B.I.n → X.B.I.E) i)) → (fun i => ιA (v i)) ∈ hat D.host.F ((VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E))) := by`. Introduce `v hv`. Express the relevant statement in the definitionally equal form `_ ∈ Submodule.span _ _`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨x, rfl⟩` from `hx`. Use `Submodule.subset_span ⟨fun i => X.ιE ((x : Fin X.B.I.n → X.B.I.E) i), (hL' _).2 ?_, ?_⟩` and prove the remaining obligations. Simplify using `using x.2`. Use function extensionality and compare the values at `i`. Simplify using `only`.

Rewrite using `[hgen']`. Consider the case `zero`. Use `Submodule.zero_mem _ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Consider the case `add x y _ _ hx hy`. Establish `: (fun i => ιA ((x + y) i)) = (fun i => ιA (x i)) + (fun i => ιA (y i))`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul r x _ hx`. Establish `hr : ιA (r : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ OAd D.host.F D.host.E` using `(hint _).1 r.2`. Establish `: (fun i => ιA ((r • x) i)) = (⟨_, hr⟩ : OAd D.host.F D.host.E) • (fun i => ιA (x i))`. Use function extensionality and compare the values at `i`.

Simplify using `[Subring.smul_def, smul_eq_mul, map_mul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hx`. Use `key _ hw` as an intermediate fact. Establish `e : (fun i => ιA (ιA.symm (w i))) = w` using `funext fun i => by simp`.

Rewrite `this` using `[e]`. Conclude with `this`.
-/
theorem latTransport : ∀ (D : D7) (X : HidaSetting D) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA → ∀ w : Fin X.B.I.n → D.host.E ⊗[D.host.F] Ad D.host.F, w ∈ hat D.host.F ((VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E))) ↔ (fun i => ιA.symm (w i)) ∈ X.B.I.Lf := by
  intro D X ιA hA w
  obtain ⟨h1, h2⟩ := hA
  have hgen : ∀ x : X.B.I.E, ιA.symm (Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) (X.ιE x)) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) x := by
    intro x; rw [RingEquiv.symm_apply_eq]; exact (h1 x).symm
  have hgen' : ∀ x : X.B.I.E, ιA (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) x) =
      Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) (X.ιE x) := h1
  have hint : ∀ a, a ∈ IntAf X.B.I.F X.B.I.E ↔ ιA a ∈ OAd D.host.F D.host.E := h2
  have hL' : ∀ c : Fin X.B.I.n → D.host.E,
      c ∈ (VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E)) ↔
        (fun i => X.ιE.symm (c i)) ∈ X.B.I.L := by
    intro c
    rw [X.L_eq, Submodule.mem_comap]
    simp [Fintype.linearCombination_apply]
  constructor
  · intro hw
    change w ∈ Submodule.span _ _ at hw
    change (fun i => ιA.symm (w i)) ∈ Submodule.span _ _
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      refine Submodule.subset_span ⟨⟨fun i => X.ιE.symm (c i), (hL' c).1 hc⟩, ?_⟩
      funext i
      simp only
      rw [← hgen, RingEquiv.apply_symm_apply]
    | zero =>
      convert Submodule.zero_mem _ using 1
      funext i; simp
    | add x y _ _ hx hy =>
      have : (fun i => ιA.symm ((x + y) i)) = (fun i => ιA.symm (x i)) + (fun i => ιA.symm (y i)) := by
        funext i; simp
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      have hr : ιA.symm (r : D.host.E ⊗[D.host.F] Ad D.host.F) ∈ IntAf X.B.I.F X.B.I.E := by
        rw [hint, RingEquiv.apply_symm_apply]; exact r.2
      have : (fun i => ιA.symm ((r • x) i)) = (⟨_, hr⟩ : IntAf X.B.I.F X.B.I.E) • (fun i => ιA.symm (x i)) := by
        funext i; simp [Subring.smul_def, smul_eq_mul, map_mul]
      rw [this]; exact Submodule.smul_mem _ _ hx
  · intro hw
    change _ ∈ Submodule.span _ _ at hw
    change w ∈ Submodule.span _ _
    have key : ∀ v, v ∈ Submodule.span (IntAf X.B.I.F X.B.I.E)
        (Set.range fun x : X.B.I.L => fun i => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((x : Fin X.B.I.n → X.B.I.E) i)) →
        (fun i => ιA (v i)) ∈ hat D.host.F ((VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E))) := by
      intro v hv
      change _ ∈ Submodule.span _ _
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨x, rfl⟩ := hx
        refine Submodule.subset_span ⟨fun i => X.ιE ((x : Fin X.B.I.n → X.B.I.E) i), (hL' _).2 ?_, ?_⟩
        · simpa using x.2
        · funext i; simp only; rw [hgen']
      | zero =>
      convert Submodule.zero_mem _ using 1
      funext i; simp
      | add x y _ _ hx hy =>
        have : (fun i => ιA ((x + y) i)) = (fun i => ιA (x i)) + (fun i => ιA (y i)) := by
          funext i; simp
        rw [this]; exact Submodule.add_mem _ hx hy
      | smul r x _ hx =>
        have hr : ιA (r : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ OAd D.host.F D.host.E := (hint _).1 r.2
        have : (fun i => ιA ((r • x) i)) = (⟨_, hr⟩ : OAd D.host.F D.host.E) • (fun i => ιA (x i)) := by
          funext i; simp [Subring.smul_def, smul_eq_mul, map_mul]
        rw [this]; exact Submodule.smul_mem _ _ hx
    have := key _ hw
    have e : (fun i => ιA (ιA.symm (w i))) = w := funext fun i => by simp
    rw [e] at this
    exact this

end GlobalTheory.St.G
