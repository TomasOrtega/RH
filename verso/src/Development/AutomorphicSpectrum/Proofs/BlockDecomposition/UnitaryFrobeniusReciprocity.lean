import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BcParamEqOfSatUEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryBorelSplittingStatement

noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.FrobRec

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def coeffMap (ρ : Representation ℂ G V) (lam : Module.Dual ℂ V) : V →ₗ[ℂ] (G → ℂ) where
  toFun v g := lam (ρ g v)
  map_add' v w := by
    funext g
    simp
  map_smul' c v := by
    funext g
    simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeffMap_apply (ρ : Representation ℂ G V) (lam : Module.Dual ℂ V) (v : V) (g : G) :
    coeffMap ρ lam v g = lam (ρ g v) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Express the relevant statement in the definitionally equal form `lam (ρ x (ρ g v)) = lam (ρ (x * g) v)`. Rewrite using `[map_mul, Module.End.mul_apply]`.
-/
theorem coeffMap_equivariant (ρ : Representation ℂ G V) (lam : Module.Dual ℂ V) (g : G) (v : V) :
    coeffMap ρ lam (ρ g v) = rightReg ℂ G ℂ g (coeffMap ρ lam v) := by
  funext x
  change lam (ρ x (ρ g v)) = lam (ρ (x * g) v)
  rw [map_mul, Module.End.mul_apply]

/- English proof (translation)
Set `S : Subrepresentation ρ` to `{ toSubmodule := LinearMap.ker (coeffMap ρ lam) apply_mem_toSubmodule := by`. Introduce `g v hv`. Rewrite `hv`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[coeffMap_equivariant, hv, map_zero] }`. Break down `hρ.eq_bot_or_eq_top S with h | h` into its components or cases.

Establish `h1 : LinearMap.ker (coeffMap ρ lam) = ⊥` using `congrArg Subrepresentation.toSubmodule h`. Conclude with `LinearMap.ker_eq_bot.1 h1`. It suffices to derive a contradiction. Establish `h1 : LinearMap.ker (coeffMap ρ lam) = ⊤` using `congrArg Subrepresentation.toSubmodule h`. Use `hlam (LinearMap.ext fun v => ?_)` and prove the remaining obligations.

Establish `h2 : v ∈ LinearMap.ker (coeffMap ρ lam)` using `h1 ▸ Submodule.mem_top`. Establish `h3` using `congrFun (LinearMap.mem_ker.1 h2) 1`. Simplify `h3` using `[coeffMap_apply]`.
-/
theorem coeffMap_injective {ρ : Representation ℂ G V} (hρ : ρ.IsIrreducible) {lam : Module.Dual ℂ V}
    (hlam : lam ≠ 0) : Function.Injective (coeffMap ρ lam) := by
  let S : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker (coeffMap ρ lam)
      apply_mem_toSubmodule := by
        intro g v hv
        rw [LinearMap.mem_ker] at hv ⊢
        rw [coeffMap_equivariant, hv, map_zero] }
  rcases hρ.eq_bot_or_eq_top S with h | h
  · have h1 : LinearMap.ker (coeffMap ρ lam) = ⊥ := congrArg Subrepresentation.toSubmodule h
    exact LinearMap.ker_eq_bot.1 h1
  · exfalso
    have h1 : LinearMap.ker (coeffMap ρ lam) = ⊤ := congrArg Subrepresentation.toSubmodule h
    refine hlam (LinearMap.ext fun v => ?_)
    have h2 : v ∈ LinearMap.ker (coeffMap ρ lam) := h1 ▸ Submodule.mem_top
    have h3 := congrFun (LinearMap.mem_ker.1 h2) 1
    simpa [coeffMap_apply] using h3

end Abstract

section U

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

/- English proof (translation)
Establish `h : ∀ i : Fin n, (((t * u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i`. Introduce `i`. Simplify using `only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]`. Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[hu.2 i, mul_one]`.

Introduce `j _ hj`. Rewrite using `[ht i j (Ne.symm hj), zero_mul]`. Simplify using the standard rewrite rules. Unfold `chiDeltaU`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use `split_ifs with hi`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem chiDeltaU_mul_uni {m : ℕ} (q : ℕ) (α : Fin m → ℂ) {t u : GU σ n}
    (ht : IsDiagM (t : GL (Fin n) L)) (hu : IsUniM (u : GL (Fin n) L)) :
    chiDeltaU q α (t * u) = chiDeltaU q α t := by
  have h : ∀ i : Fin n, (((t * u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by
    intro i
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
    rw [Finset.sum_eq_single i]
    · rw [hu.2 i, mul_one]
    · intro j _ hj
      rw [ht i j (Ne.symm hj), zero_mul]
    · simp
  unfold chiDeltaU
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [h]
  · rfl

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Establish `h : ρ u w - w ∈ jacU ρ` using `Submodule.subset_span ⟨u, hu, w, rfl⟩`. Establish `h0` using `hJ _ h`. Rewrite `h0` using `[map_sub, sub_eq_zero]`. Then use the resulting hypothesis.
-/
theorem form_uni {ρ : Representation ℂ (GU σ n) V} {lam : Module.Dual ℂ V}
    (hJ : ∀ x ∈ jacU ρ, lam x = 0) {u : GU σ n} (hu : IsUniM (u : GL (Fin n) L)) (w : V) :
    lam (ρ u w) = lam w := by
  have h : ρ u w - w ∈ jacU ρ := Submodule.subset_span ⟨u, hu, w, rfl⟩
  have h0 := hJ _ h
  rwa [map_sub, sub_eq_zero] at h0

/- English proof (translation)
Introduce `b g hb`. Take `⟨t, u, ht, hu, rfl⟩` from `hsplit L σ n hσ b hb`. Rewrite using `[chiDeltaU_mul_uni q _ ht hu, coeffMap_apply, coeffMap_apply, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hT t ht, form_uni hJ hu]`.
-/
theorem coeffMap_mem (hsplit : BorelSplitU) (hσ : ∀ x, σ (σ x) = x) {q : ℕ} {β : Fin (n / 2) → ℂˣ}
    {ρ : Representation ℂ (GU σ n) V} {lam : Module.Dual ℂ V} (hJ : ∀ x ∈ jacU ρ, lam x = 0)
    (hT : ∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → ∀ v,
      lam (ρ t v) = chiDeltaU q (fun i => (β i : ℂ)) t * lam v) (v : V) :
    coeffMap ρ lam v ∈ psSpaceU σ q β := by
  intro b g hb
  obtain ⟨t, u, ht, hu, rfl⟩ := hsplit L σ n hσ b hb
  rw [chiDeltaU_mul_uni q _ ht hu, coeffMap_apply, coeffMap_apply, map_mul, map_mul,
    Module.End.mul_apply, Module.End.mul_apply, hT t ht, form_uni hJ hu]

end U

/- English proof (translation)
Introduce `L _ _ _ ϖ σ q n V _ _ ρ α hU _ hIrr hSat β lam hJ hlam hT`. Establish `hmem` using `coeffMap_mem hsplit hU.1 hJ hT`. Establish `hinj` using `coeffMap_injective hIrr hlam`. Establish `heq` using `coeffMap_equivariant ρ lam`. Use `⟨?_, (coeffMap ρ lam).codRestrict (psSpaceU σ q β) hmem, ?_, fun g v => ?_⟩` and prove the remaining obligations.

Take `⟨v₀, hv₀⟩` from `hSat.exists_vec`. Establish `h0 : coeffMap ρ lam v₀ ≠ 0` using `fun h => hv₀.1 (hinj (h.trans (map_zero _).symm))`. Establish `hα : IsSatVecU ϖ q (rightReg ℂ _ ℂ) (coeffMap ρ lam v₀) α` using `hv₀.map hU _ heq h0`. Establish `hsph : IsSphericalU q (fun i => (β i : ℂ)) (coeffMap ρ lam v₀)`. Introduce `b g k hb hk`.

Establish `h1 : coeffMap ρ lam v₀ (b * g * k) = coeffMap ρ lam v₀ (b * g)`. Rewrite using `[coeffMap_apply, coeffMap_apply, map_mul (ρ) (b * g) k, Module.End.mul_apply, GlobalTheory.LGrp.mem_fixed.1 hv₀.2.1 k hk]`. Rewrite using `[h1]`. Conclude with `hmem v₀ b g hb`. Conclude with `hα.unique hU (isSatVecU_of_isSphericalU hU hsph h0)`.

Introduce `a b hab`. Conclude with `hinj (congrArg Subtype.val hab)`. Conclude with `Subtype.ext (heq g v)`.
-/
theorem frobU_of_split (hsplit : BorelSplitU) : FrobU := by
  intro L _ _ _ ϖ σ q n V _ _ ρ α hU _ hIrr hSat β lam hJ hlam hT
  have hmem := coeffMap_mem hsplit hU.1 hJ hT
  have hinj := coeffMap_injective hIrr hlam
  have heq := coeffMap_equivariant ρ lam
  refine ⟨?_, (coeffMap ρ lam).codRestrict (psSpaceU σ q β) hmem, ?_, fun g v => ?_⟩
  · obtain ⟨v₀, hv₀⟩ := hSat.exists_vec
    have h0 : coeffMap ρ lam v₀ ≠ 0 := fun h => hv₀.1 (hinj (h.trans (map_zero _).symm))
    have hα : IsSatVecU ϖ q (rightReg ℂ _ ℂ) (coeffMap ρ lam v₀) α := hv₀.map hU _ heq h0
    have hsph : IsSphericalU q (fun i => (β i : ℂ)) (coeffMap ρ lam v₀) := by
      intro b g k hb hk
      have h1 : coeffMap ρ lam v₀ (b * g * k) = coeffMap ρ lam v₀ (b * g) := by
        rw [coeffMap_apply, coeffMap_apply, map_mul (ρ) (b * g) k, Module.End.mul_apply,
          GlobalTheory.LGrp.mem_fixed.1 hv₀.2.1 k hk]
      rw [h1]
      exact hmem v₀ b g hb
    exact hα.unique hU (isSatVecU_of_isSphericalU hU hsph h0)
  · intro a b hab
    exact hinj (congrArg Subtype.val hab)
  · exact Subtype.ext (heq g v)

/- English proof (translation)
The claim follows from `frobU_of_split GlobalTheory.T.unitary_borel_splitting`.
-/
theorem frobU : FrobU := frobU_of_split GlobalTheory.T.unitary_borel_splitting

end GlobalTheory.CompanionTheory.FrobRec

end
