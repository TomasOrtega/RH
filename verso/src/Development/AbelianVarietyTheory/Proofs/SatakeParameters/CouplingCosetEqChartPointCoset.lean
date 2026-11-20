import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfMemZmu

noncomputable section

namespace GlobalTheory.TwV

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `h : s • (fr P).symm (a - b) ∈ stdAt E n P.1` using `GlobalTheory.TopStep.mem_stdAt.2 fun l => by`. Use `GlobalTheory.TopStep.intAt_sub (ha l) (hb l)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_sub, Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree.

Use `(hf P _).2 h` as an intermediate fact. Rewrite `this` using `[map_smul, LinearEquiv.apply_symm_apply]`. Then use the resulting hypothesis.
-/
theorem smul_sub_mem_of_frames {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))}
    {N : Submodule (𝓞 E) (Sp E n)} {fr : Frs E n SB} (hf : GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.IsFrames N fr) (P : SB) (s : E) (a b y₀ : Sp E n)
    (ha : ∀ l, IntAt P.1 (s * ((fr P).symm a - y₀) l)) (hb : ∀ l, IntAt P.1 (s * ((fr P).symm b - y₀) l)) :
    s • (a - b) ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal N := by
  have h : s • (fr P).symm (a - b) ∈ stdAt E n P.1 := GlobalTheory.TopStep.mem_stdAt.2 fun l => by
    have := GlobalTheory.TopStep.intAt_sub (ha l) (hb l)
    convert this using 1
    simp only [Pi.smul_apply, smul_eq_mul, map_sub, Pi.sub_apply]
    ring
  have := (hf P _).2 h
  rwa [map_smul, LinearEquiv.apply_symm_apply] at this

section

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}

/- English proof (translation)
Unfold `y0At`. Rewrite using `[dif_pos rfl]`.
-/
theorem chartBaseRepresentative_penultimate_step (A : AdData t u μ St) (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (P : SB t μ) :
    y0At A (t.m2 + 1) hi β P = A.y0 β P := by
  unfold y0At
  rw [dif_pos rfl]

end

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ H c`. Take `⟨w, -, hw⟩` from `H.chain.2.1 c`. Establish `hwm : w ∈ A.yb c`. Rewrite using `[hw, Set.mem_setOf_eq, sub_self]`. Conclude with `zero_mem _`.

Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Rewrite using `[hw, Set.mem_setOf_eq, locLat, Submodule.mem_iInf]`. Introduce `P`.

Rewrite using `[Submodule.mem_comap]`. Establish `h1` using `hy P`. Establish `h2` using `H.coset c w hwm P`. Rewrite `h1` using `[chartBaseRepresentative_penultimate_step]`. Unfold `SameCoset at h1 h2`.

Establish `key` using `smul_sub_mem_of_frames (GlobalTheory.ColPeriod.isFrames_frsF (A.pt _ (cpl_lt t μ).le c)) P _ y w _ h1 h2`. Distinguish the cases in `hP : P.1 ∈ t.Pr.vGs`. Simplify using `only [hP, if_true] at key ⊢`. Simplify using `using key`. Simplify using `only [hP, if_false] at key ⊢`.

Simplify `key` using `[zpow_natCast]`. Introduce `hy P`. Rewrite using `[chartBaseRepresentative_penultimate_step]`. Conclude with `H.coset c y hy P`.
-/
theorem cosetOf_eq_yb : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ c, cosetOf A (t.m2 + 1) (cpl_lt t μ).le ((St _ (cpl_lt t μ).le).chOf c) (A.pt _ (cpl_lt t μ).le c) = A.yb c) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ H c
  obtain ⟨w, -, hw⟩ := H.chain.2.1 c
  have hwm : w ∈ A.yb c := by
    rw [hw, Set.mem_setOf_eq, sub_self]
    exact zero_mem _
  ext y
  constructor
  · intro hy
    rw [hw, Set.mem_setOf_eq, locLat, Submodule.mem_iInf]
    intro P
    rw [Submodule.mem_comap]
    have h1 := hy P
    have h2 := H.coset c w hwm P
    rw [chartBaseRepresentative_penultimate_step] at h1
    unfold SameCoset at h1 h2
    have key := smul_sub_mem_of_frames (GlobalTheory.ColPeriod.isFrames_frsF (A.pt _ (cpl_lt t μ).le c)) P _ y w _ h1 h2
    by_cases hP : P.1 ∈ t.Pr.vGs
    · simp only [hP, if_true] at key ⊢
      simpa using key
    · simp only [hP, if_false] at key ⊢
      simpa [zpow_natCast] using key
  · intro hy P
    rw [chartBaseRepresentative_penultimate_step]
    exact H.coset c y hy P

end GlobalTheory.TwV

end
