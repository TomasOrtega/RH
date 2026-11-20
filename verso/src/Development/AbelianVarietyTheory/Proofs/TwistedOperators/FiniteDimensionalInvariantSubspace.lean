import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactUnitaryFiniteInvariantSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactIrreducibleHasHighestWeightAndIsoStatement
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

noncomputable section

namespace GlobalTheory.KFinStable

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def restr (ε : Fin n → Bool) (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (T : Module.End ℂ (kFinVec ε ρ))
    (S : Submodule ℂ H) (hle : S ≤ kFinVec ε ρ) : S →ₗ[ℂ] H :=
  (kFinVec ε ρ).subtype ∘ₗ T ∘ₗ Submodule.inclusion hle

/- English proof (translation)
Take `⟨hfd, hK, hirr, ⟨v0, hv0S, hv0, hv0w⟩, hdom⟩` from `hS`. Use `set φ := restr ε ρ T S hle with hφ`. Establish `hcomm : ∀ g (hg : g ∈ Kset ε) (x : S), φ ⟨ρ g x, hK g hg x x.2⟩ = ρ g (φ x)`. Introduce `g hg x`. Conclude with `hT g hg ⟨x, hle x.2⟩ ⟨ρ g x, hle (hK g hg x x.2)⟩ rfl`.

Use `set Kr : Submodule ℂ H := (LinearMap.ker φ).map S.subtype with hKr`. Establish `hKrS : Kr ≤ S` using `Submodule.map_subtype_le _ _`. Establish `hKrK : IsKStableOn ε ρ Kr`. Introduce `g hg x hx`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.1 hx`.

Use `Submodule.mem_map.2 ⟨⟨ρ g y, hK g hg y y.2⟩, ?_, rfl⟩` and prove the remaining obligations. Rewrite `hy`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[hcomm g hg y, hy, map_zero]`. Break down `hirr Kr hKrS hKrK with h0 | h1` into its components or cases. Use `right`.

Establish `hinj : Function.Injective φ`. Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`. Introduce `y hy`. Establish `: (y : H) ∈ Kr` using `Submodule.mem_map.2 ⟨y, hy, rfl⟩`. Rewrite `this` using `[h0, Submodule.mem_bot]`.

Conclude with `(Submodule.mem_bot ℂ).2 (Subtype.ext this)`. Use `⟨LinearMap.finiteDimensional_range φ, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `g hg _ ⟨x, rfl⟩`. Conclude with `⟨⟨ρ g x, hK g hg x x.2⟩, hcomm g hg x⟩`. Introduce `S'' hS''le hS''K set P : Submodule ℂ H := (S''.comap φ).map S.subtype with hP`.

Establish `hPS : P ≤ S` using `Submodule.map_subtype_le _ _`. Establish `hPK : IsKStableOn ε ρ P`. Introduce `g hg x hx`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.1 hx`. Use `Submodule.mem_map.2 ⟨⟨ρ g y, hK g hg y y.2⟩, ?_, rfl⟩` and prove the remaining obligations.

Rewrite `hy`, the goal using `[Submodule.mem_comap]`. Rewrite using `[hcomm g hg y]`. Conclude with `hS''K g hg _ hy`. Break down `hirr P hPS hPK with hP0 | hP1` into its components or cases. Use `left`.

Rewrite using `[eq_bot_iff]`. Introduce `y hy`. Take `⟨z, rfl⟩` from `hS''le hy`. Establish `: (z : H) ∈ P` using `Submodule.mem_map.2 ⟨z, hy, rfl⟩`. Rewrite `this` using `[hP0, Submodule.mem_bot]`.

Establish `hz : z = 0` using `Subtype.ext this`. Rewrite using `[hz, map_zero]`. Conclude with `Submodule.zero_mem _`. Use `right`. Use `le_antisymm hS''le ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨z, rfl⟩`. Establish `: (z : H) ∈ P` using `by rw [hP1]; exact z.2`. Take `⟨z', hz', hzz⟩` from `Submodule.mem_map.1 this`. Establish `: z' = z` using `Subtype.ext hzz`. Rewrite using `[← this]`.

Conclude with `hz'`. Use `⟨φ ⟨v0, hv0S⟩, ⟨_, rfl⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Use `hinj (h.trans (map_zero φ).symm)` as an intermediate fact. Conclude with `hv0 (congrArg Subtype.val this)`.

Introduce `θ hθ`. Rewrite using `[← hcomm _ hθ, ← map_smul]`. Use `congr 1`. Conclude with `Subtype.ext (hv0w θ hθ)`. Introduce and unpack `μ _ ⟨x, rfl⟩ hy hw`.

Establish `hx : (x : H) ≠ 0`. Introduce `h`. Apply `hy` to reduce the goal to its premises. Rewrite using `[show x = 0 from Subtype.ext h, map_zero]`. Use `hdom μ x x.2 hx ?_` and prove the remaining obligations.

Introduce `θ hθ`. Use `hw θ hθ` as an intermediate fact. Rewrite `this` using `[← hcomm _ hθ, ← map_smul]`. Conclude with `congrArg Subtype.val (hinj this)`. Use `left`.

Rewrite using `[LinearMap.range_eq_bot]`. Use extensionality with `y`. Establish `: (y : H) ∈ Kr` using `by rw [h1]; exact y.2`. Take `⟨z, hz, hzy⟩` from `Submodule.mem_map.1 this`. Establish `: z = y` using `Subtype.ext hzy`.

Rewrite using `[← this]`. Simplify using `using hz`.
-/
theorem range_restr (ε : Fin n → Bool) (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (T : Module.End ℂ (kFinVec ε ρ))
    (hT : ∀ κ ∈ Kset ε, ∀ (v w : kFinVec ε ρ), (w : H) = ρ κ v → ((T w : kFinVec ε ρ) : H) = ρ κ (T v : H))
    (Λ : Fin n → ℝ) (S : Submodule ℂ H) (hS : IsKTypeOf ε ρ Λ S) (hle : S ≤ kFinVec ε ρ) :
    LinearMap.range (restr ε ρ T S hle) = ⊥ ∨ IsKTypeOf ε ρ Λ (LinearMap.range (restr ε ρ T S hle)) := by
  obtain ⟨hfd, hK, hirr, ⟨v0, hv0S, hv0, hv0w⟩, hdom⟩ := hS
  set φ := restr ε ρ T S hle with hφ
  have hcomm : ∀ g (hg : g ∈ Kset ε) (x : S), φ ⟨ρ g x, hK g hg x x.2⟩ = ρ g (φ x) := by
    intro g hg x
    exact hT g hg ⟨x, hle x.2⟩ ⟨ρ g x, hle (hK g hg x x.2)⟩ rfl

  set Kr : Submodule ℂ H := (LinearMap.ker φ).map S.subtype with hKr
  have hKrS : Kr ≤ S := Submodule.map_subtype_le _ _
  have hKrK : IsKStableOn ε ρ Kr := by
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
    refine Submodule.mem_map.2 ⟨⟨ρ g y, hK g hg y y.2⟩, ?_, rfl⟩
    rw [LinearMap.mem_ker] at hy ⊢
    rw [hcomm g hg y, hy, map_zero]
  rcases hirr Kr hKrS hKrK with h0 | h1
  · right
    have hinj : Function.Injective φ := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro y hy
      have : (y : H) ∈ Kr := Submodule.mem_map.2 ⟨y, hy, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext this)
    refine ⟨LinearMap.finiteDimensional_range φ, ?_, ?_, ?_, ?_⟩
    · rintro g hg _ ⟨x, rfl⟩
      exact ⟨⟨ρ g x, hK g hg x x.2⟩, hcomm g hg x⟩
    · intro S'' hS''le hS''K
      set P : Submodule ℂ H := (S''.comap φ).map S.subtype with hP
      have hPS : P ≤ S := Submodule.map_subtype_le _ _
      have hPK : IsKStableOn ε ρ P := by
        intro g hg x hx
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
        refine Submodule.mem_map.2 ⟨⟨ρ g y, hK g hg y y.2⟩, ?_, rfl⟩
        rw [Submodule.mem_comap] at hy ⊢
        rw [hcomm g hg y]
        exact hS''K g hg _ hy
      rcases hirr P hPS hPK with hP0 | hP1
      · left
        rw [eq_bot_iff]
        intro y hy
        obtain ⟨z, rfl⟩ := hS''le hy
        have : (z : H) ∈ P := Submodule.mem_map.2 ⟨z, hy, rfl⟩
        rw [hP0, Submodule.mem_bot] at this
        have hz : z = 0 := Subtype.ext this
        rw [hz, map_zero]; exact Submodule.zero_mem _
      · right
        refine le_antisymm hS''le ?_
        rintro _ ⟨z, rfl⟩
        have : (z : H) ∈ P := by rw [hP1]; exact z.2
        obtain ⟨z', hz', hzz⟩ := Submodule.mem_map.1 this
        have : z' = z := Subtype.ext hzz
        rw [← this]; exact hz'
    · refine ⟨φ ⟨v0, hv0S⟩, ⟨_, rfl⟩, ?_, ?_⟩
      · intro h
        have := hinj (h.trans (map_zero φ).symm)
        exact hv0 (congrArg Subtype.val this)
      · intro θ hθ
        rw [← hcomm _ hθ, ← map_smul]
        congr 1
        exact Subtype.ext (hv0w θ hθ)
    · rintro μ _ ⟨x, rfl⟩ hy hw
      have hx : (x : H) ≠ 0 := by
        intro h
        apply hy
        rw [show x = 0 from Subtype.ext h, map_zero]
      refine hdom μ x x.2 hx ?_
      intro θ hθ
      have := hw θ hθ
      rw [← hcomm _ hθ, ← map_smul] at this
      exact congrArg Subtype.val (hinj this)
  · left
    rw [LinearMap.range_eq_bot]
    ext y
    have : (y : H) ∈ Kr := by rw [h1]; exact y.2
    obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.1 this
    have : z = y := Subtype.ext hzy
    rw [← this]
    simpa using hz

end GlobalTheory.KFinStable

noncomputable section

namespace GlobalTheory.KFinStable

variable {n : ℕ}

def kSub (ε : Fin n → Bool) : Subgroup (Matrix.unitaryGroup (Fin n) ℂ) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) ℂ) * Jm ε = Jm ε * g}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    show (a : Matrix (Fin n) (Fin n) ℂ) * b * Jm ε = Jm ε * (a * b)
    rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]
  one_mem' := by
    show ((1 : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * Jm ε = Jm ε * _
    simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    show star (a : Matrix (Fin n) (Fin n) ℂ) * Jm ε = Jm ε * star (a : Matrix (Fin n) (Fin n) ℂ)
    have h := congrArg star ha
    simp only [star_mul, Matrix.star_eq_conjTranspose, Jm_conjTranspose] at h
    simpa [Matrix.star_eq_conjTranspose] using h.symm

/- English proof (translation)
Assemble the required witnesses or components as `⟨(g : Matrix.unitaryGroup (Fin n) ℂ).2, g.2⟩`.
-/
theorem mem_Kset (ε : Fin n → Bool) (g : kSub ε) : ((g : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε :=
  ⟨(g : Matrix.unitaryGroup (Fin n) ℂ).2, g.2⟩

/- English proof (translation)
Use `show inUJ ε _`. Establish `hu : star ((g : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * ((g : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1` using `Unitary.star_mul_self_of_mem (g : Matrix.unitaryGroup (Fin n) ℂ).2`. Unfold `inUJ`. Rewrite using `[Matrix.mul_assoc, ← g.2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, hu, Matrix.one_mul]`.
-/
theorem mem_UJset (ε : Fin n → Bool) (g : kSub ε) :
    ((g : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
  show inUJ ε _
  have hu : star ((g : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *
      ((g : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Unitary.star_mul_self_of_mem (g : Matrix.unitaryGroup (Fin n) ℂ).2
  unfold inUJ
  rw [Matrix.mul_assoc, ← g.2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, hu, Matrix.one_mul]

instance unitaryGroup_compactSpace' (m : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin m) ℂ) := by
  apply isCompact_iff_compactSpace.mp
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin m => Set.pi Set.univ fun _ : Fin m =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine IsCompact.of_isClosed_subset (t := ((Matrix.unitaryGroup (Fin m) ℂ : Submonoid _) :
      Set (Matrix (Fin m) (Fin m) ℂ))) hK isClosed_unitary ?_
  intro U hU
  exact Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j =>
    mem_closedBall_zero_iff.2 (entry_norm_bound_of_unitary hU i j)

instance matrix_secondCountable' (m : ℕ) : SecondCountableTopology (Matrix (Fin m) (Fin m) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin m → ℂ))

instance unitaryGroup_secondCountable' (m : ℕ) :
    SecondCountableTopology (Matrix.unitaryGroup (Fin m) ℂ) :=
  TopologicalSpace.Subtype.secondCountableTopology _

instance kSub_secondCountable (ε : Fin n → Bool) : SecondCountableTopology (kSub ε) :=
  TopologicalSpace.Subtype.secondCountableTopology _

instance kSub_compactSpace (ε : Fin n → Bool) : CompactSpace (kSub ε) := by
  apply isCompact_iff_compactSpace.mp
  apply IsClosed.isCompact
  have : IsClosed {g : Matrix.unitaryGroup (Fin n) ℂ |
      (g : Matrix (Fin n) (Fin n) ℂ) * Jm ε = Jm ε * g} :=
    isClosed_eq ((continuous_subtype_val).mul continuous_const)
      (continuous_const.mul continuous_subtype_val)
  exact this

end GlobalTheory.KFinStable

noncomputable section

namespace GlobalTheory.KFinStable

def kRep {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) :
    kSub ε →* (H →L[ℂ] H) where
  toFun g := ρ ((g : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
  map_one' := h.1
  map_mul' a b := h.2 _ (mem_UJset ε a) _ (mem_UJset ε b)

/- English proof (translation)
Introduce `n ε H _ _ _ _ ρ hA T hT`. Take `⟨hrep, hcont, hnorm, hadm⟩` from `hA`. Take `⟨S₀, hS₀, hS₀fd, hS₀K⟩` from `GlobalTheory.T.compact_unitary_finite_invariant_subspace (kSub ε) H (kRep ε ρ hrep) (fun k x => hnorm _ (mem_Kset ε k) x) (fun x => (hcont x).comp_continuous (continuous_subtype_val.comp continuous_subtype_val) (fun k => mem_UJset ε k))`. Establish `hS₀K' : IsKStableOn ε ρ S₀` using `fun g hg v hv => hS₀K ⟨⟨g, hg.1⟩, hg.2⟩ v hv`. Establish `hex : ∃ d, ∃ S : Submodule ℂ H, S ≠ ⊥ ∧ FiniteDimensional ℂ S ∧ IsKStableOn ε ρ S ∧ Module.finrank ℂ S = d` using `⟨_, S₀, hS₀, hS₀fd, hS₀K', rfl⟩`.

Take `⟨S₁, hS₁, hS₁fd, hS₁K, hS₁d⟩` from `Nat.find_spec hex`. Establish `hirr : ∀ S' : Submodule ℂ H, S' ≤ S₁ → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = S₁`. Introduce `S' hle hK'`. Distinguish the cases in `h0 : S' = ⊥`. Conclude with `Or.inl h0`.

Use `right`. Assume the negation of the conclusion as `hne`. Establish `hlt : S' < S₁` using `lt_of_le_of_ne hle hne`. Use `haveI := Submodule.finiteDimensional_of_le hle`. Use `Submodule.finrank_lt_finrank_of_lt hlt` as an intermediate fact.

Conclude with `Nat.find_min hex (hS₁d ▸ this) ⟨S', h0, inferInstance, hK', rfl⟩`. Take `⟨Λ, hΛ⟩` from `(GlobalTheory.T.maxCompact_irreducible_has_highest_weight_and_iso n ε H ρ hrep hcont hnorm).1 S₁ hS₁fd hS₁ hS₁K hirr`. Use `set Sg : Submodule ℂ H := sSup {S' | S' ≤ ⊤ ∧ IsKTypeOf ε ρ Λ S'} with hSg`. Use `haveI hSgfd : FiniteDimensional ℂ Sg := hadm Λ`. Establish `hkt_le : ∀ S', IsKTypeOf ε ρ Λ S' → S' ≤ kFinVec ε ρ` using `fun S' h v hv => ⟨S', h.1, hv, h.2.1⟩`.

Establish `hSgle : Sg ≤ kFinVec ε ρ` using `sSup_le fun S' h => hkt_le S' h.2`. Establish `hle_Sg : ∀ S', IsKTypeOf ε ρ Λ S' → S' ≤ Sg` using `fun S' h => le_sSup ⟨le_top, h⟩`. Use `⟨Sg.comap (kFinVec ε ρ).subtype, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe hSgle).symm`. Take `⟨v0, hv0, hv0ne, -⟩` from `hΛ.2.2.2.1`.

Introduce `hbot`. Establish `hmem : (⟨v0, hkt_le S₁ hΛ hv0⟩ : kFinVec ε ρ) ∈ Sg.comap (kFinVec ε ρ).subtype` using `hle_Sg S₁ hΛ hv0`. Rewrite `hmem` using `[hbot, Submodule.mem_bot]`. Conclude with `hv0ne (congrArg Subtype.val hmem)`. Introduce `k set N : Submodule ℂ H := (Sg.comap ((kFinVec ε ρ).subtype ∘ₗ T k)).map (kFinVec ε ρ).subtype with hN`.

Establish `hSgN : Sg ≤ N`. Use `sSup_le fun S' hS' => ?_` and prove the remaining obligations. Introduce `x hx`. Establish `hxk` using `hkt_le S' hS'.2 hx`. Use `Submodule.mem_map.2 ⟨⟨x, hxk⟩, ?_, rfl⟩` and prove the remaining obligations.

Rewrite using `[Submodule.mem_comap]`. Establish `hr : restr ε ρ (T k) S' (hkt_le S' hS'.2) ⟨x, hx⟩ ∈ Sg`. Break down `range_restr ε ρ (T k) (fun κ hκ v w h => hT κ hκ k v w h) Λ S' hS'.2 (hkt_le S' hS'.2) with h0 | h1` into its components or cases. Establish `: restr ε ρ (T k) S' (hkt_le S' hS'.2) ⟨x, hx⟩ ∈ LinearMap.range (restr ε ρ (T k) S' (hkt_le S' hS'.2))` using `⟨_, rfl⟩`. Rewrite `this` using `[h0, Submodule.mem_bot]`.

Rewrite using `[this]`. Conclude with `Sg.zero_mem`. Conclude with `hle_Sg _ h1 ⟨_, rfl⟩`. Conclude with `hr`. Introduce `w hw`.

Rewrite `hw`, the goal using `[Submodule.mem_comap]`. Take `⟨y, hy, hyw⟩` from `Submodule.mem_map.1 (hSgN hw)`. Establish `: y = w` using `Subtype.ext hyw`. Rewrite using `[← this]`. Conclude with `hy`.
-/
theorem exists_finDim_stable : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε ρ → ∀ T : ℕ → Module.End ℂ (kFinVec ε ρ), (∀ κ ∈ Kset ε, ∀ (k : ℕ) (v w : kFinVec ε ρ), (w : H) = ρ κ v → ((T k w : kFinVec ε ρ) : H) = ρ κ (T k v : H)) → ∃ S : Submodule ℂ (kFinVec ε ρ), FiniteDimensional ℂ S ∧ S ≠ ⊥ ∧ ∀ k, ∀ w ∈ S, T k w ∈ S := by
  intro n ε H _ _ _ _ ρ hA T hT
  obtain ⟨hrep, hcont, hnorm, hadm⟩ := hA

  obtain ⟨S₀, hS₀, hS₀fd, hS₀K⟩ := GlobalTheory.T.compact_unitary_finite_invariant_subspace (kSub ε) H (kRep ε ρ hrep)
    (fun k x => hnorm _ (mem_Kset ε k) x)
    (fun x => (hcont x).comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
      (fun k => mem_UJset ε k))
  have hS₀K' : IsKStableOn ε ρ S₀ := fun g hg v hv => hS₀K ⟨⟨g, hg.1⟩, hg.2⟩ v hv

  have hex : ∃ d, ∃ S : Submodule ℂ H, S ≠ ⊥ ∧ FiniteDimensional ℂ S ∧ IsKStableOn ε ρ S ∧
      Module.finrank ℂ S = d := ⟨_, S₀, hS₀, hS₀fd, hS₀K', rfl⟩
  classical
  obtain ⟨S₁, hS₁, hS₁fd, hS₁K, hS₁d⟩ := Nat.find_spec hex
  have hirr : ∀ S' : Submodule ℂ H, S' ≤ S₁ → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = S₁ := by
    intro S' hle hK'
    by_cases h0 : S' = ⊥
    · exact Or.inl h0
    right
    by_contra hne
    have hlt : S' < S₁ := lt_of_le_of_ne hle hne
    haveI := Submodule.finiteDimensional_of_le hle
    have := Submodule.finrank_lt_finrank_of_lt hlt
    exact Nat.find_min hex (hS₁d ▸ this) ⟨S', h0, inferInstance, hK', rfl⟩
  obtain ⟨Λ, hΛ⟩ := (GlobalTheory.T.maxCompact_irreducible_has_highest_weight_and_iso n ε H ρ hrep hcont hnorm).1 S₁ hS₁fd hS₁ hS₁K hirr

  set Sg : Submodule ℂ H := sSup {S' | S' ≤ ⊤ ∧ IsKTypeOf ε ρ Λ S'} with hSg
  haveI hSgfd : FiniteDimensional ℂ Sg := hadm Λ
  have hkt_le : ∀ S', IsKTypeOf ε ρ Λ S' → S' ≤ kFinVec ε ρ := fun S' h v hv => ⟨S', h.1, hv, h.2.1⟩
  have hSgle : Sg ≤ kFinVec ε ρ := sSup_le fun S' h => hkt_le S' h.2
  have hle_Sg : ∀ S', IsKTypeOf ε ρ Λ S' → S' ≤ Sg := fun S' h => le_sSup ⟨le_top, h⟩
  refine ⟨Sg.comap (kFinVec ε ρ).subtype, ?_, ?_, ?_⟩
  · exact LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe hSgle).symm
  · obtain ⟨v0, hv0, hv0ne, -⟩ := hΛ.2.2.2.1
    intro hbot
    have hmem : (⟨v0, hkt_le S₁ hΛ hv0⟩ : kFinVec ε ρ) ∈ Sg.comap (kFinVec ε ρ).subtype :=
      hle_Sg S₁ hΛ hv0
    rw [hbot, Submodule.mem_bot] at hmem
    exact hv0ne (congrArg Subtype.val hmem)
  · intro k
    set N : Submodule ℂ H :=
      (Sg.comap ((kFinVec ε ρ).subtype ∘ₗ T k)).map (kFinVec ε ρ).subtype with hN
    have hSgN : Sg ≤ N := by
      refine sSup_le fun S' hS' => ?_
      intro x hx
      have hxk := hkt_le S' hS'.2 hx
      refine Submodule.mem_map.2 ⟨⟨x, hxk⟩, ?_, rfl⟩
      rw [Submodule.mem_comap]
      have hr : restr ε ρ (T k) S' (hkt_le S' hS'.2) ⟨x, hx⟩ ∈ Sg := by
        rcases range_restr ε ρ (T k) (fun κ hκ v w h => hT κ hκ k v w h) Λ S' hS'.2 (hkt_le S' hS'.2) with h0 | h1
        · have : restr ε ρ (T k) S' (hkt_le S' hS'.2) ⟨x, hx⟩ ∈
              LinearMap.range (restr ε ρ (T k) S' (hkt_le S' hS'.2)) := ⟨_, rfl⟩
          rw [h0, Submodule.mem_bot] at this
          rw [this]; exact Sg.zero_mem
        · exact hle_Sg _ h1 ⟨_, rfl⟩
      exact hr
    intro w hw
    rw [Submodule.mem_comap] at hw ⊢
    obtain ⟨y, hy, hyw⟩ := Submodule.mem_map.1 (hSgN hw)
    have : y = w := Subtype.ext hyw
    rw [← this]
    exact hy

end GlobalTheory.KFinStable
